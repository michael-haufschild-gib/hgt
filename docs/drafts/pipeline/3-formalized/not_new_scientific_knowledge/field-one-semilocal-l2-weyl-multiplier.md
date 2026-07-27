# Semilocal product-Haar L² Weyl multiplier

- **ID:** `field-one-semilocal-l2-weyl-multiplier`
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION / THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-finite-adele-l2-weyl-multiplier`
- **Statement:** the normalized real and standard finite-adele phases combine into a unitary
  additive Weyl action on product-Haar \(L^2(\mathbb R\times\mathbb A_f)\).

## Theorem

For \(a=(a_\infty,a_f)\) and \(x=(x_\infty,x_f)\), let
\[
  \chi_a(x)=
  \exp(-2\pi i a_\infty x_\infty)\,\psi_f(a_fx_f).
\]
This phase is continuous, has norm one, and satisfies
\(\chi_{a+b}=\chi_a\chi_b\). It therefore defines onto linear isometries
\[
  W_a:L^2(\mathbb R\times\mathbb A_f,\,dx\otimes d x_f)
  \simeq L^2(\mathbb R\times\mathbb A_f,\,dx\otimes d x_f)
\]
with \(W_aW_b=W_{a+b}\). The rational diagonal specialization has the same additive law.

The product measure is formed on \(\mathbb A_f\times\mathbb R\), with sigma-finite Lebesgue
measure on `Measure.prod`'s right side, and transported by coordinate swap. This also proves
positivity on nonempty open sets without a finite-adele sigma-finiteness premise.

No Hilbert-tensor identification, spectral assertion, trace, positivity, or RH premise occurs.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneSemilocalL2WeylMultiplier`
- **Core theorems:** `norm_fieldOneSemilocalL2WeylPhase`,
  `fieldOneSemilocalL2WeylPhase_add`,
  `fieldOneSemilocalL2WeylUnitary_add_apply`,
  `fieldOneRationalDiagonalL2WeylUnitary_add_apply`
- **Audit:** direct `lake env lean` passed. Scratch `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound`. Final targeted `lake build` remains reserved for final
  audit.

## Gates

- [x] 0 → 1: normalized product phase and product measure typed
- [x] 1 → 2: dependency-closed unitary/additive proof
- [x] 2 → 3: unconditional direct Lean check and axiom audit
- [ ] 3 → 4: publication-ready integration
