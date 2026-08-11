# Attempt 8: the loop fused with xiWeilPolarization (2026-08-11)

Module `RHTower/GaussHodgeWeilPolarizationFusion.lean` (wired, built, axiom-clean, 8 theorems).
Card hodge-sign-wall-constructed-pairing, attempt 8 = Gate-II milestone (a).

Hostile check first: "H-mass = odd-sector restriction of xiWeilPolarization" is FALSE naively —
the polarization is irreducibly the holomorphic channel (its prime-test summand ≡ 1). The true
fusion, all unconditional/pointwise:
- xiWeilPrimeTest p z := exp(z·I·log p); on the divisor = burnolPrimeCharacter (spectral
  coordinates: xiSpectralPoint q · I = s − 1/2); sharp = character at FE-reflected argument.
- Blindness INSIDE the interface: xiWeilPairTerm (prime test) ≡ 1.
- Pair-square law (any test F): xiWeilPairTerm F q + xiWeilPairTerm F (lineConj q) =
  ‖F(α)‖² + ‖F(ᾱ)‖² − ‖F(α) − F(ᾱ)‖².
- At the prime test ‖F(α) − F(ᾱ)‖² = cosh defect ⟹ massDensity_eq_hermitianPair_sub_weilPair:
  H-mass density = Hermitian pair energy − 2·Re(Weil pair value), and
  riemannHypothesis_iff_hermitianPair_eq_weilPair: RH ⟺ the gap closes at prime 2.
- Unconditional eigen-Gram: xiWeilPolarization couples eigen(α) only to eigen(conj α), value
  m(α)·XiC′(α)·conj XiC′(conj α) — the RH-conditional orthogonality in XiWeilPolarization.lean
  is the diagonal collapse of this law.

Consequence for the entry-point hunt: any Gate-II mechanism producing
Re(xiWeilPolarization-pair values) = Hermitian pair energy (e.g. compressed-trace identity à la
Connes–Consani, extended multi-place) lands DIRECTLY on H-mass vanishing, hence RH, through the
loop. The Weil-positivity interface and the Gauss/Hodge/seam loop are now one formal object.
