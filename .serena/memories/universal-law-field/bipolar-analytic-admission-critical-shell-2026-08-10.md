# ULF-LSM-7 analytic admission mechanism (2026-08-10)

Higher mechanism: algebraic equivalence saturation and analytic Hausdorff admission are distinct laws. Analytic admission is the maximal Hausdorff quotient after EqvGen saturation, and on compact Hausdorff sources its kernel is exactly equality under all continuous real-valued unitizing reporters.

Paper:
- Stage2: docs/drafts/pipeline/2-fully-proven/universal-law-field/law-saturation-mechanics/bipolar-admission-hull-critical-shell-and-infinite-alternation-law.md
- Stage1 programme: .../law-saturation-mechanics/bipolar-admission-hull-critical-shell-and-infinite-alternation-program.md
- Parent programme: .../bipolar-law-formation-and-constitutive-interference-program.md

Lean:
- formal/GaloisForLFunctions/HTGeometry/ConstitutiveAnalyticAdmissionHull.lean
- formal/GaloisForLFunctions/HTGeometry/ConstitutiveOneEndedAdmissionCriticalShell.lean
- imported by HTGeometry/UniversalLawField.lean
- Stage3 certification card added.

Certified generic laws:
1. EqvGen observer invariance.
2. Universal factorization of every continuous T2 unitizing observer through algebraic saturation then T2Quotient.
3. Exact scalar bipolar characterization by continuous real reporters on compact Hausdorff sources.

Certified unconditional cofinal capstone:
X=OnePoint Nat. Continuous retractions pair {0,1},{2,3},... and {0},{1,2},{3,4},...
- algebraic join makes all finite points one class but leaves infinity;
- set reporter 0 on Nat, 1 at infinity unitizes both but is discontinuous;
- every continuous T2 jointly unitizing observer is constant, hence analytic admission total;
- finite reporters 1_{n>N}, value 1 at infinity, have exact margin 1 and stabilize pointwise to the set reporter;
- best constant replacement gap is exactly 1/2.
Capstone: oneEndedAdmissionCriticalShell.

Verification:
- direct lake env lean passed for both modules;
- scripts/formal_tools.py lint passed;
- final lake build GaloisForLFunctions.HTGeometry.UniversalLawField passed, 11,525 jobs;
- axiom audit: only propext, Classical.choice, Quot.sound;
- no task-owned stale Lean process.

Exact boundary: general least-closed-equivalence restatement, Dirac measure-TV, two-ended integer model, non-equicontinuity theorem, and bounded-alternation closure remain paper-only. Do not cite as Lean-certified.

Field status: Bipolar Target 3 mechanism core closed. Next lane must be doctrine-relative admission (positive/holomorphic/smooth/domain-restricted reporters) and must produce nonisomorphic critical shells from one source. Do not regress to routes.