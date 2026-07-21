# ⊢ DiagonaLean

A foundational software research project to develop the first tactic-driven toolkit for mechanising computability-theoretic reasoning in Lean 4.

A continuation of https://github.com/aalok-thakkar/undecidability/.

## Phased work plan

- **Phase 1 — Core Framework (Months 1–6).** Formal definitions of Problem, ManyOneReduction, TuringReduction. Composition laws, undecidability transfer theorems, public notation layer.
- **Phase 2 — Canonical Base Problems (Months 4–10).** Self-contained undecidability proofs for the Halting Problem, TM acceptance (ATM), the Post Correspondence Problem, and selected language-theoretic problems (CFG universality, CFG intersection-emptiness). Each is registered in the reduction graph via `@[reduction_graph]`.
- **Phase 3 — Standard Reduction Library (Months 8–18).** Mechanisation of the undecidability results in Hopcroft–Motwani–Ullman, plus selected results from Rogers and Soare. The target is a comprehensive, textbook-aligned reduction graph in which every node is a certified formal object and every edge is a machine-checked reduction.

