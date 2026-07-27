# Faithful semilocal Bruhat embedding in product-Haar L²

- **ID:** `field-one-semilocal-bruhat-l2-embedding`
- **Stage:** 3-formalized
- **Type:** CONSTRUCTION / THEOREM (Lean)
- **Labels:** `[PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `field-one-semilocal-bruhat-to-l2`
- **Statement:** the canonical algebraic Schwartz--Bruhat map into semilocal product-Haar
  \(L^2\) is injective.

## Proof

Form product measure first on \(\mathbb A_f\times\mathbb R\), placing known sigma-finite Lebesgue
measure on `Measure.prod`'s right side, then transport it to
\(\mathbb R\times\mathbb A_f\) by coordinate swap. The resulting measure is positive on every
nonempty open set without any sigma-finiteness premise for finite-adele Haar.

The algebraic Schwartz--Bruhat tensor embeds in the full product function space by the general
function-tensor injectivity theorem. Its image is continuous. The \(L^2\) map has this continuous
function as representative; equality in \(L^2\) gives almost-everywhere equality, open positivity
upgrades it to pointwise equality, and function-tensor injectivity recovers tensor equality.

No density or completed-Hilbert-tensor claim occurs.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.FieldOneSemilocalBruhatL2Embedding`
- **Core theorems:** `fieldOneSemilocalBruhatToFunction_injective`,
  `fieldOneSemilocalBruhatToFunction_continuous`,
  `fieldOneSemilocalBruhatToL2_ae`,
  `fieldOneSemilocalBruhatToL2_injective`
- **Supporting instance:** `fieldOneSemilocalAddHaarIsOpenPosMeasure`
- **Audit:** direct cached `lake env lean` passed. Scratch `#print axioms` reports only `propext`,
  `Classical.choice`, and `Quot.sound`. Final targeted `lake build` remains reserved for final
  audit.

## Gates

- [x] 0 → 1: faithful pointwise tensor and open-positive measure typed
- [x] 1 → 2: continuous representative and injectivity proof
- [x] 2 → 3: unconditional direct Lean check and axiom audit
- [ ] 3 → 4: publication-ready integration
