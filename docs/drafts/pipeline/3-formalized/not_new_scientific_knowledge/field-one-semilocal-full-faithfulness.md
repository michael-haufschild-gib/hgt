# Full faithfulness of the semilocal Weyl tensor

- **ID:** `field-one-semilocal-full-faithfulness`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-finite-adele-self-duality`
- **Statement:** the full \(\mathbb R\times\mathbb A_f\) Weyl action on the algebraic
  Schwartz--Bruhat tensor is faithful.

## Proof

Finite-zero contraction against the integral Bruhat test recovers the real multiplier and
separates real coordinates. Archimedean-zero contraction against the standard Gaussian recovers
the finite multiplier because both the Gaussian and every real phase equal one at zero.
Finite-character primitivity then separates finite coordinates. The two coordinate equalities
give equality in \(\mathbb R\times\mathbb A_f\).

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneSemilocalFullFaithfulness`
- **Core theorems:** `fieldOneSemilocalContractArchimedeanZero_tmul`,
  `fieldOneSemilocalArchimedeanWeylMultiplier_gaussian_zero`,
  `fieldOneSemilocalBruhatWeylMultiplier_eq_imp_snd_eq`,
  `fieldOneSemilocalBruhatWeylMultiplier_injective`
- **Audit:** direct `lake env lean` passed. Scratch `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound`. Final targeted `lake build` remains reserved for final
  audit.

## Gates

- [x] 0 → 1: dual contraction typed
- [x] 1 → 2: dependency-closed coordinate-separation proof
- [x] 2 → 3: unconditional direct Lean check and axiom audit
- [ ] 3 → 4: publication-ready integration
