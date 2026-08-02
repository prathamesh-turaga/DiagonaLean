# ⊢ DiagonaLean

A foundational software research project to develop the first tactic-driven toolkit for mechanising computability-theoretic reasoning in Lean 4.

A continuation of https://github.com/aalok-thakkar/undecidability/.

## Phased work plan

- **Phase 1 : Core Framework (Months 1–3).** Formalization of several basic undecidability problems. Specifically: Ambiguity of CFGs, Empty Intersection of CFGs, Halting, PCP/MPCP, Matrix Mortality, String Rewriting, and possibly Rice's Theorem. We also come up with a rudimentary tactic extracted from these formal proofs to reduce an instance of one problem into an instance of another, with some holes that need to be filled. This requires formalizing the notion of a problem, and the definition of the predicate `Undecidable`. Some work on this has already happened in `Synthetic/`.
- **Phase 2 : Base Theorems (Months 4–7).** We formalize the acceptance problem and several more undecidability problems. Further, we formalize more theorems: after Rice, Rice-Shapiro and Greibach. Each undecidable problem is registered in the reduction graph via `@[reduction_graph]`. We also introduce a tactic to traverse the reduction graph. The reduction tactic also matures more at this stage.
- **Phase 3 : Standard Reduction Library (Months 8–).** We now move on to formalizing more models of computation and show their equivalence to Turing Machines (if they are not already in Cslib, such as λ-calculus): RAM Machines, register machines, and μ-recursive functions.

