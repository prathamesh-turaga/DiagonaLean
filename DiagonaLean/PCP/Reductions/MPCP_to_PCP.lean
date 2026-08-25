/-
Copyright (c) 2026 Aalok Thakkar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aalok Thakkar
-/

import DiagonaLean.MPCP.Basic
import DiagonaLean.PCP.Basic

/-! # MPCP ⪯ₘ PCP

Many-one reduction from the Modified Post Correspondence Problem to PCP,
following the Hopcroft–Ullman construction and the Coq formalisation of
Forster, Heiter, and Smolka [ForsterHeiterSmolka2018].

The alphabet `α` is extended with two fresh markers `⋕` and `₹`.
The interleaving functions `hashL` (hash before) and `hashR` (hash after)
satisfy the key duality `hashL x ++ [⋕] = ⋕ :: hashR x`, which is what
allows the end tile to close a solution. The three tile roles are:
`tileStart` (forces every solution to begin with it), `tileReg` (encodes
an MPCP card), and `tileEnd` (closes the match).

## References

* [J. E. Hopcroft, R. Motwani, J. D. Ullman,
  *Introduction to Automata Theory, Languages, and Computation*][HopcroftMotwaniUllman2006]
* [Y. Forster, E. Heiter, G. Smolka,
  *Verification of PCP-Related Computational Reductions in Coq*][ForsterHeiterSmolka2018]
-/

@[expose] public section

namespace DiagonaLean.PCP.Reduction

open DiagonaLean.PCP
open DiagonaLean.MPCP

/-- Extend alphabet `α` with two distinguished markers `⋕` (hash) and `₹` (rupee).
Disjointness from the original alphabet is a type fact. -/
inductive Ext (α : Type) : Type
  /-- A map that lifts a symbol in `α` to a symbol in the extended alphabet `Ext α`. -/
  | sym   : α → Ext α
  /-- A distinguishing marker in `Ext α` used to interleave. -/
  | hash  : Ext α
  /-- A distinguishing marker in `Ext α` used for the beginning/terminating symbol. -/
  | rupee : Ext α
  deriving DecidableEq

@[inherit_doc] notation   "⋕" => Ext.hash
@[inherit_doc] notation   "₹" => Ext.rupee
@[inherit_doc] prefix:max "↟" => Ext.sym

variable {α : Type}

/-- Interleave with `⋕` before each symbol: `a₀ a₁ … aₙ ↦ ⋕ ↟a₀ ⋕ ↟a₁ … ⋕ ↟aₙ`. -/
def hashL : List α → List (Ext α)
  | []      => []
  | a :: x  => ⋕ :: ↟a :: hashL x

/-- Interleave with `⋕` after each symbol: `a₀ a₁ … aₙ ↦ ↟a₀ ⋕ ↟a₁ ⋕ … ↟aₙ ⋕`. -/
def hashR : List α → List (Ext α)
  | []      => []
  | a :: x  => ↟a :: ⋕ :: hashR x

/-- `hashL` of the empty List is empty. -/
@[simp]
theorem hashL_nil : hashL ([] : List α) = [] := rfl

/-- `hashR` of the empty List is empty. -/
@[simp]
theorem hashR_nil : hashR ([] : List α) = [] := rfl

/-- `hashL` of a cons List prepends `⋕` then the lifted head symbol. -/
@[simp]
theorem hashL_cons (a : α) (x : List α) :
    hashL (a :: x) = ⋕ :: ↟a :: hashL x := rfl

/-- `hashR` of a cons List appends the lifted head symbol then `⋕`. -/
@[simp]
theorem hashR_cons (a : α) (x : List α) :
    hashR (a :: x) = ↟a :: ⋕ :: hashR x := rfl

/-- `hashL` distributes over List concatenation. -/
@[simp]
theorem hashL_append (x y : List α) :
    hashL (x ++ y) = hashL x ++ hashL y := by
  induction x with
  | nil => simp
  | cons a x ih => simp [ih]

/-- `hashR` distributes over List concatenation. -/
@[simp]
theorem hashR_append (x y : List α) :
    hashR (x ++ y) = hashR x ++ hashR y := by
  induction x with
  | nil => simp
  | cons a x ih => simp [ih]

/-- Key duality: `hashL x ++ [⋕] = ⋕ :: hashR x`.
This allows the end tile to close a solution by converting a `hashL` suffix
into a `hashR` prefix. -/
theorem hashL_snoc_eq (x : List α) :
    hashL x ++ [⋕] = ⋕ :: hashR x := by
  induction x with
  | nil => rfl
  | cons a x ih => simp [ih]

/-- `hashL x` never equals `⋕ :: hashR y` for any `x` and `y`.
Used in `match_start` to rule out regular tiles as the first tile of a solution. -/
theorem hashL_ne_hash_hashR (x y : List α) :
    hashL x ≠ ⋕ :: hashR y := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
    simp
    intro h
    cases y with
    | nil => simp at h
    | cons b y =>
      simp at h
      grind

/-- The start tile for an MPCP instance with distinguished card `c`.
Its top begins with `₹`, forcing every PCP solution to start with this tile. -/
def tileStart (c : Tile α) : Tile (Ext α) where
  top := ₹ :: hashL c.top
  bot := ₹ :: ⋕ :: hashR c.bot

/-- The regular tile encoding an MPCP card `t` via interleaving. -/
def tileReg (t : Tile α) : Tile (Ext α) where
  top := hashL t.top
  bot := hashR t.bot

/-- The end tile: the unique tile that can close a solution by converting
a trailing `hashL` suffix into the `hashR` form needed on the bottom. -/
def tileEnd : Tile (Ext α) where
  top := [⋕, ₹]
  bot := [₹]

/-- The reduced PCP instance for MPCP input `(c, R)`.
The start tile comes first; non-empty cards from `c :: R` are interleaved
as regular tiles; the end tile closes. Empty cards are filtered out to prevent
spurious PCP solutions. -/
def mpcpToPcp (c : Tile α) (R : Stack α) : Stack (Ext α) :=
  tileStart c ::
  ((c :: R).filterMap (fun t =>
    if t.top ≠ [] ∨ t.bot ≠ [] then some (tileReg t) else none)) ++
  [tileEnd]

/-- Every tile in `mpcpToPcp c R` is either the start tile, the end tile,
or the `tileReg` encoding of some non-empty card from `c :: R`. -/
theorem mem_mpcpToPcp_iff (c : Tile α) (R : Stack α) (t : Tile (Ext α)) :
    t ∈ mpcpToPcp c R ↔
    t = tileStart c ∨
    t = tileEnd ∨
    ∃ s, s ∈ c :: R ∧ (s.top ≠ [] ∨ s.bot ≠ []) ∧ t = tileReg s := by
  unfold mpcpToPcp
  simp only [List.cons_append, List.mem_cons, List.mem_append,
             List.mem_filterMap, List.not_mem_nil,
             Option.ite_none_right_eq_some, Option.some.injEq, or_false]
  constructor
  · rintro (rfl | ⟨s, hmem, hne, hrfl⟩ | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr ⟨s, hmem, hne, hrfl.symm⟩)
    · exact Or.inr (Or.inl rfl)
  · rintro (rfl | rfl | ⟨s, hmem, hne, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl ⟨s, hmem, hne, rfl⟩)

/-- No tile in `mpcpToPcp c R` has a top List beginning with a lifted symbol `↟a`.
All tops begin with `₹` (start tile) or `⋕` (regular or end tile). -/
theorem not_sym_head_top (c : Tile α) (R : Stack α) (a : α) (w u : List (Ext α)) :
    Tile.mk (↟a :: w) u ∉ mpcpToPcp c R := by
  rw [mem_mpcpToPcp_iff]
  rintro (h | h | ⟨s, _, _, hk⟩)
  · simp [tileStart, Tile.mk.injEq] at h
  · simp [tileEnd, Tile.mk.injEq] at h
  · simp only [tileReg, Tile.mk.injEq] at hk
    obtain ⟨hk1, _⟩ := hk
    cases hxs : s.top with
    | nil =>
      rw [hxs, hashL_nil] at hk1
      exact List.cons_ne_nil _ _ hk1
    | cons b bs =>
      rw [hxs, hashL_cons] at hk1
      simp at hk1

/-- No tile in `mpcpToPcp c R` has a bottom List beginning with `⋕`.
All bottoms begin with `₹` (start or end tile) or `↟a` (regular tile). -/
theorem not_hash_head_bot (c : Tile α) (R : Stack α) (v w : List (Ext α)) :
    Tile.mk v (⋕ :: w) ∉ mpcpToPcp c R := by
  rw [mem_mpcpToPcp_iff]
  rintro (h | h | ⟨s, _, _, hk⟩)
  · simp [tileStart, Tile.mk.injEq] at h
  · simp [tileEnd, Tile.mk.injEq] at h
  · simp only [tileReg, Tile.mk.injEq] at hk
    obtain ⟨_, hk2⟩ := hk
    cases hys : s.bot with
    | nil =>
      rw [hys, hashR_nil] at hk2
      exact List.cons_ne_nil _ _ hk2
    | cons b bs =>
      rw [hys, hashR_cons] at hk2
      simp at hk2

/-- `τ1` of any sub-stack drawn from `mpcpToPcp c R` never begins with `↟a`.
This is the stack-level version of `not_sym_head_top`. -/
theorem τ1_ne_sym_head (c : Tile α) (R : Stack α) (B : Stack (Ext α))
    (a : α) (w : List (Ext α))
    (hmem : ∀ t ∈ B, t ∈ mpcpToPcp c R) :
    τ1 B ≠ ↟a :: w := by
  induction B generalizing w with
  | nil => simp
  | cons d B ih =>
    intro h
    have hd : d ∈ mpcpToPcp c R := hmem d (List.mem_cons_self)
    have hB : ∀ t ∈ B, t ∈ mpcpToPcp c R :=
      fun t ht => hmem t (List.mem_cons_of_mem _ ht)
    simp only [τ1_cons] at h
    cases hd_top : d.top with
    | nil =>
      rw [hd_top] at h
      simp only [List.nil_append] at h
      exact ih w hB h
    | cons e es =>
      rw [hd_top] at h
      simp only [List.cons_append] at h
      have he : e = ↟a := by injection h
      subst he
      exact not_sym_head_top c R a es d.bot
        (by cases d; simp_all)

/-- `τ2` of any sub-stack drawn from `mpcpToPcp c R` never begins with `⋕`.
This is the stack-level version of `not_hash_head_bot`. -/
theorem τ2_ne_hash_head (c : Tile α) (R : Stack α) (B : Stack (Ext α))
    (w : List (Ext α))
    (hmem : ∀ t ∈ B, t ∈ mpcpToPcp c R) :
    τ2 B ≠ ⋕ :: w := by
  induction B generalizing w with
  | nil => simp
  | cons d B ih =>
    intro h
    have hd : d ∈ mpcpToPcp c R := hmem d (List.mem_cons_self)
    have hB : ∀ t ∈ B, t ∈ mpcpToPcp c R :=
      fun t ht => hmem t (List.mem_cons_of_mem _ ht)
    simp only [τ2_cons] at h
    cases hd_bot : d.bot with
    | nil =>
      rw [hd_bot] at h
      simp only [List.nil_append] at h
      exact ih w hB h
    | cons e es =>
      rw [hd_bot] at h
      simp only [List.cons_append] at h
      have he : e = ⋕ := by injection h
      subst he
      exact not_hash_head_bot c R d.top es
        (by cases d; simp_all)

/-- Any non-empty matching PCP solution drawn from `mpcpToPcp c R` must begin
with the start tile. This is the key invariant for the backward direction. -/
theorem match_start (c : Tile α) (R : Stack α)
    (d : Tile (Ext α)) (B : Stack (Ext α))
    (hmem : ∀ t ∈ d :: B, t ∈ mpcpToPcp c R)
    (heq  : τ1 (d :: B) = τ2 (d :: B)) :
    d = tileStart c := by
  have hd : d ∈ mpcpToPcp c R := hmem d (List.mem_cons_self)
  have hB : ∀ t ∈ B, t ∈ mpcpToPcp c R :=
    fun t ht => hmem t (List.mem_cons_of_mem _ ht)
  rw [mem_mpcpToPcp_iff] at hd
  rcases hd with rfl | rfl | ⟨s, _, hne, rfl⟩
  · rfl
  · simp only [tileEnd, τ1_cons, τ2_cons] at heq
    grind
  · simp only [tileReg, τ1_cons, τ2_cons] at heq
    cases hx : s.top with
    | nil =>
      cases hy : s.bot with
      | nil =>
        rcases hne with h | h
        · exact absurd hx h
        · exact absurd hy h
      | cons b ys =>
        rw [hx, hy] at heq
        simp only [hashL_nil, hashR_cons, List.nil_append, List.cons_append] at heq
        exact absurd heq (τ1_ne_sym_head c R B b (⋕ :: hashR ys ++ τ2 B) hB)
    | cons a xs =>
      cases hy : s.bot with
      | nil =>
        rw [hx, hy] at heq
        simp only [hashL_cons, hashR_nil, List.cons_append, List.nil_append] at heq
        exact absurd heq.symm
          (τ2_ne_hash_head c R B (↟a :: hashL xs ++ τ1 B) hB)
      | cons b ys =>
        rw [hx, hy] at heq
        simp only [hashL_cons, hashR_cons, List.cons_append] at heq
        grind

/-- The regular tiles obtained by interleaving every non-empty card of `A`. -/
private def regsOf (A : Stack α) : Stack (Ext α) :=
  A.filterMap fun t =>
    if t.top ≠ [] ∨ t.bot ≠ [] then some (tileReg t) else none

/-- `τ1` of the regular tiles of `A` equals `hashL (τ1 A)`. -/
private theorem τ1_regsOf (A : Stack α) :
    τ1 (regsOf A) = hashL (τ1 A) := by
  induction A with
  | nil => rfl
  | cons s A ih =>
    show τ1 (List.filterMap _ (s :: A)) = hashL (τ1 (s :: A))
    rw [List.filterMap_cons, τ1_cons, hashL_append]
    by_cases h : s.top ≠ [] ∨ s.bot ≠ []
    · rw [ite_eq_left h]
      change (tileReg s).top ++ τ1 (regsOf A) = _
      rw [ih]; simp [tileReg]
    · rw [ite_eq_right h]
      change τ1 (regsOf A) = _
      push Not at h
      rw [h.1, hashL_nil, List.nil_append, ih]

/-- `τ2` of the regular tiles of `A` equals `hashR (τ2 A)`. -/
private theorem τ2_regsOf (A : Stack α) :
    τ2 (regsOf A) = hashR (τ2 A) := by
  induction A with
  | nil => rfl
  | cons s A ih =>
    show τ2 (List.filterMap _ (s :: A)) = hashR (τ2 (s :: A))
    rw [List.filterMap_cons, τ2_cons, hashR_append]
    by_cases h : s.top ≠ [] ∨ s.bot ≠ []
    · rw [ite_eq_left h]
      change (tileReg s).bot ++ τ2 (regsOf A) = _
      rw [ih]; simp [tileReg]
    · rw [ite_eq_right h]
      change τ2 (regsOf A) = _
      push Not at h
      rw [h.2, hashR_nil, List.nil_append, ih]

/-- Every tile in `regsOf A` is the `tileReg` encoding of some non-empty card from `A`. -/
private theorem mem_regsOf (A : Stack α) (t : Tile (Ext α))
    (ht : t ∈ regsOf A) :
    ∃ s ∈ A, (s.top ≠ [] ∨ s.bot ≠ []) ∧ t = tileReg s := by
  simp only [regsOf, List.mem_filterMap, Option.ite_none_right_eq_some,
             Option.some.injEq] at ht
  obtain ⟨s, hsmem, hne, hrfl⟩ := ht
  exact ⟨s, hsmem, hne, hrfl.symm⟩

/-- If `(c, R)` admits an MPCP solution `A`, then `mpcpToPcp c R` admits a PCP solution. -/
theorem mpcp_to_pcp_solution (c : Tile α) (R : Stack α)
    (A : Stack α)
    (hA  : ∀ t ∈ A, t ∈ c :: R)
    (heq : c.top ++ τ1 A = c.bot ++ τ2 A) :
    ∃ B : Stack (Ext α),
      B ≠ [] ∧
      (∀ t ∈ B, t ∈ mpcpToPcp c R) ∧
      τ1 B = τ2 B := by
  refine ⟨tileStart c :: regsOf A ++ [tileEnd], ?_, ?_, ?_⟩
  · simp
  · intro t ht
    simp only [List.cons_append, List.mem_cons, List.mem_append,
               List.not_mem_nil, or_false] at ht
    rw [mem_mpcpToPcp_iff]
    rcases ht with rfl | hreg | rfl
    · exact Or.inl rfl
    · obtain ⟨s, hsmem, hne, rfl⟩ := mem_regsOf A t hreg
      exact Or.inr (Or.inr ⟨s, hA s hsmem, hne, rfl⟩)
    · exact Or.inr (Or.inl rfl)
  · have h1 := τ1_regsOf A
    have h2 := τ2_regsOf A
    have h1_eval :
        τ1 (tileStart c :: regsOf A ++ [tileEnd]) =
          ₹ :: hashL (c.top ++ τ1 A) ++ [⋕, ₹] := by
      simp only [τ1_cons, τ1_append, tileStart, tileEnd, τ1_nil,
                 List.append_nil, h1]
      simp only [List.cons_append, ← hashL_append]
    have h2_eval :
        τ2 (tileStart c :: regsOf A ++ [tileEnd]) =
          ₹ :: ⋕ :: hashR (c.bot ++ τ2 A) ++ [₹] := by
      simp only [τ2_cons, τ2_append, tileStart, tileEnd, τ2_nil,
                 List.append_nil, h2]
      simp only [List.cons_append, ← hashR_append]
    rw [h1_eval, h2_eval, heq]
    have hclose : ∀ w : List α, hashL w ++ [⋕, ₹] = ⋕ :: hashR w ++ [₹] := by
      intro w
      have : hashL w ++ [⋕, ₹] = (hashL w ++ [⋕]) ++ [₹] := by simp
      rw [this, hashL_snoc_eq]
    grind

/-- `hashL x ++ ₹ :: w₁` never equals `⋕ :: hashR y ++ ₹ :: w₂`.
Used in the backward direction to rule out start tiles appearing mid-solution. -/
theorem hashL_append_rupee_ne (x y : List α) (w₁ w₂ : List (Ext α)) :
    hashL x ++ ₹ :: w₁ ≠ ⋕ :: hashR y ++ ₹ :: w₂ := by
  induction x generalizing y with
  | nil =>
    cases y <;> intro h <;> simp at h
  | cons a x ih =>
    cases y with
    | nil => intro h; simp at h
    | cons b y =>
      intro h
      simp at h
      exact ih y h.2

/-- `hashR x ++ ₹ :: w₁ = hashR y ++ ₹ :: w₂` implies `x = y`.
Used in the backward direction when the end tile closes the match. -/
theorem hashR_append_rupee_inj (x y : List α) (w₁ w₂ : List (Ext α))
    (h : hashR x ++ ₹ :: w₁ = hashR y ++ ₹ :: w₂) : x = y := by
  induction x generalizing y with
  | nil =>
    cases y with
    | nil => rfl
    | cons b y => simp at h
  | cons a x ih =>
    cases y with
    | nil => simp at h
    | cons b y =>
      simp at h
      obtain ⟨h1, h2⟩ := h
      rw [h1, ih y h2]

/-- Generalised backward direction: given a sub-stack `B` whose tiles are from the
reduced instance, and a matching state `(u, v)` capturing accumulated tops and bottoms,
reconstruct an MPCP-style match. This drives the inductive step of the backward direction. -/
theorem pcp_to_mpcp_solution_gen (c : Tile α) (R : Stack α)
    (B : Stack (Ext α)) (u v : List α)
    (hB  : ∀ t ∈ B, t ∈ mpcpToPcp c R)
    (hmatch : hashL u ++ τ1 B = ⋕ :: hashR v ++ τ2 B) :
    ∃ A : Stack α, (∀ t ∈ A, t ∈ c :: R) ∧
      u ++ τ1 A = v ++ τ2 A := by
  induction B generalizing u v with
  | nil =>
    simp only [τ1_nil, τ2_nil, List.append_nil] at hmatch
    exact absurd hmatch (hashL_ne_hash_hashR _ _)
  | cons d B ih =>
    have hd : d ∈ mpcpToPcp c R := hB d (List.mem_cons_self)
    have hB' : ∀ t ∈ B, t ∈ mpcpToPcp c R :=
      fun t ht => hB t (List.mem_cons_of_mem _ ht)
    rw [mem_mpcpToPcp_iff] at hd
    rcases hd with rfl | rfl | ⟨s, hsmem, _, rfl⟩
    · simp only [tileStart, τ1_cons, τ2_cons] at hmatch
      exact absurd hmatch (hashL_append_rupee_ne u v _ _)
    · simp only [tileEnd, τ1_cons, τ2_cons] at hmatch
      have h_lhs : hashL u ++ ([⋕, ₹] ++ τ1 B) = ⋕ :: hashR u ++ ₹ :: τ1 B := by
        have h1 : hashL u ++ ([⋕, ₹] ++ τ1 B) = (hashL u ++ [⋕]) ++ (₹ :: τ1 B) :=
          by grind
        rw [h1, hashL_snoc_eq]
      rw [h_lhs] at hmatch
      have hmatch_tail : hashR u ++ ₹ :: τ1 B = hashR v ++ ₹ :: τ2 B := by
        injection hmatch
      have huv := hashR_append_rupee_inj u v _ _ hmatch_tail
      subst huv
      exact ⟨[], by simp, by simp⟩
    · simp only [tileReg, τ1_cons, τ2_cons] at hmatch
      have h_lhs : hashL u ++ (hashL s.top ++ τ1 B) =
          hashL (u ++ s.top) ++ τ1 B := by
        rw [← List.append_assoc, ← hashL_append]
      have h_rhs : ⋕ :: hashR v ++ (hashR s.bot ++ τ2 B) =
          ⋕ :: hashR (v ++ s.bot) ++ τ2 B := by
        simp [← List.append_assoc, ← hashR_append]
      rw [h_lhs, h_rhs] at hmatch
      obtain ⟨A, hA, heq⟩ := ih (u ++ s.top) (v ++ s.bot) hB' hmatch
      refine ⟨s :: A, ?_, ?_⟩
      · intro t ht
        simp only [List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact hsmem
        · exact hA t ht
      · simp only [τ1_cons, τ2_cons]
        rw [← List.append_assoc u s.top, ← List.append_assoc v s.bot]
        exact heq

/-- If the reduced PCP instance has a solution, the original MPCP instance has a solution. -/
theorem pcp_to_mpcp_solution (c : Tile α) (R : Stack α)
    (B : Stack (Ext α))
    (hne  : B ≠ [])
    (hB   : ∀ t ∈ B, t ∈ mpcpToPcp c R)
    (heq  : τ1 B = τ2 B) :
    ∃ A : Stack α, (∀ t ∈ A, t ∈ c :: R) ∧
      c.top ++ τ1 A = c.bot ++ τ2 A := by
  cases B with
  | nil => contradiction
  | cons d B' =>
    have hfirst : d = tileStart c := match_start c R d B' hB heq
    subst hfirst
    have hB' : ∀ t ∈ B', t ∈ mpcpToPcp c R :=
      fun t ht => hB t (List.mem_cons_of_mem _ ht)
    have htail : hashL c.top ++ τ1 B' = ⋕ :: hashR c.bot ++ τ2 B' := by
      have := heq
      simp only [tileStart, τ1_cons, τ2_cons] at this
      grind
    exact pcp_to_mpcp_solution_gen c R B' c.top c.bot hB' htail

/-- MPCP reduces many-one to PCP via `mpcpToPcp`: `(c, R)` has an MPCP solution
iff `mpcpToPcp c R` has a PCP solution. -/
theorem mpcp_iff_pcp (c : Tile α) (R : Stack α) :
    MPCP.DecisionProblem c R ↔ PCP.DecisionProblem (mpcpToPcp c R) := by
  constructor
  · rintro ⟨A, hA, heq⟩
    obtain ⟨B, hne, hB, heqB⟩ := mpcp_to_pcp_solution c R A hA heq
    exact ⟨B, hne, hB, heqB⟩
  · rintro ⟨B, hne, hB, heq⟩
    obtain ⟨A, hA, heqA⟩ := pcp_to_mpcp_solution c R B hne hB heq
    exact ⟨A, hA, heqA⟩

end DiagonaLean.PCP.Reduction
