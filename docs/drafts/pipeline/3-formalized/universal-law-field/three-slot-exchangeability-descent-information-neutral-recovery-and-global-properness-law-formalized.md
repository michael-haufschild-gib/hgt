# Three-slot exchangeability descent and global properness — formalized

- **Paper card:** `docs/drafts/pipeline/2-fully-proven/universal-law-field/species-relative-formation-mechanics/three-slot-exchangeability-descent-information-neutral-recovery-and-global-properness-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveExchangeableFormationSelection`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`

Lean certifies:

1. two-slot functional-equation orbit symmetrization is transposition-blind;
2. the orbit-symmetrized three-slot cylinder defect is exactly `(p - q)^2 / 2`;
3. the adjacent-versus-skipped coincidence defect under one slot deletion is the same square, so
   formation-thinning consistency already forces neutrality;
4. the coordinate-free skipped-minus-adjacent tensor packet factors exactly as
   `(p - q) ⊗ₜ (p - q)`;
5. every real linear reporter evaluates that factorization as a nonnegative square, with exact
   reporter-level zero locus;
6. three-slot exchangeability for a reporter family reconstructs equality of reflected reporter
   laws;
7. a finite separating reporter family has nonnegative complete defect, zero exactly at equality;
8. functional-equation reflection preserves defect and work;
9. independent formation depth adds work exactly;
10. uniformly bounded complete work at every depth is equivalent to reflected-law equality.

Verification used `/tmp` scratch elaboration, direct leaf elaboration, one targeted leaf build, and
a scratch `#print axioms` audit.  No umbrella, area, or full-project build was run.  Audited
capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.  Module is wired into the
universal-law-field umbrella without building it.

This certifies the algebraic formation/descent/properness mechanism.  It does not prove the open
source landing: that literal pre-zero functional-equation slots form one indistinguishable species
and carry a bounded complete formation work law.
