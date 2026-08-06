# Ramified top-conormal ambidexterity

- **ID:** `deninger-ramified-top-conormal-ambidexterity`
- **Stage:** 3-formalized
- **Paper proof:**
  `new_scientific_knowledge/deninger/deninger-ramified-top-conormal-ambidexterity.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.DeningerRamifiedTopConormalAmbidexterity`

## Formalized capstones

Algebraic power sectors:

- `powerMapResidueComponent_deningerShiftedPowerPullback`:
  extraction of residue class `r` is a left inverse to
  `g(X) ↦ X^r g(X^n)`;
- `deningerShiftedPowerPullback_comp`:
  shifted sectors compose by the exact affine radix law
  `r_(mn)=m*r_n+r_m`;
- `deningerTopConormalPowerPullback_comp`:
  `g(X) ↦ X^(n-1)g(X^n)` composes strictly for all positive powers;
- `powerMapResidueComponent_deningerTopConormalPowerPullback`:
  final-residue extraction recovers the source polynomial;
- `deningerCoherentPowerShift_eq_raw_or_topConormal`:
  every strict coherent monomial sector for the commutative positive-power
  semigroup is either raw (`r_n=0`) or top conormal (`r_n=n-1`).

Finite ramified Hilbert blocks:

- `deningerFiniteBlockResiduePair_rawPowerEmbedding`:
  Grothendieck anti-diagonal residue transpose of raw power embedding is
  final-residue extraction;
- `deningerTopConormalResidue_rawPowerEmbedding_eq_zero`:
  raw and top-conormal sectors are disjoint at every genuinely ramified
  degree;
- `deningerTopConormalResidue_differentAction`:
  coordinate form of `trace = different * residue`;
- `inner_deningerTopConormalEmbedding_left` and
  `inner_deningerTopConormalEmbedding`:
  final-coordinate embedding has final-residue extraction as literal
  Hilbert adjoint and is isometric;
- `deningerTopConormalTransfer_adjoint` and
  `deningerTopConormalCotransfer_transfer`:
  rank-half-density normalization preserves adjunction and gives the exact
  degree law `(n+1) • id`.

All statements are unconditional. No RH, Xi zero, zero simplicity,
spectral synthesis, or source-annihilation premise occurs.

## Verification

- direct foreground check:
  `lake env lean GaloisForLFunctions/RHTower/DeningerRamifiedTopConormalAmbidexterity.lean`
  passed;
- umbrella import added to `GaloisForLFunctions/RHTower.lean`;
- targeted final audit:
  `lake build GaloisForLFunctions.RHTower.DeningerRamifiedTopConormalAmbidexterity`
  passed;
- `#print axioms` on nine capstones reports only `propext`,
  `Classical.choice`, and `Quot.sound` (classification needs no
  `Classical.choice`);
- module contains no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`;
- global `scripts/formal_tools.py lint` reached this umbrella import but is
  currently blocked by six unrelated pre-existing unreachable modules; none
  is in this theorem's dependency or write scope.

## Scientific consequence

Finite ramified local-block ambidexterity is no longer an unspecified
duality assertion. Raw power pullback is wrong positive local sector:
its residue transpose lives in a disjoint congruence class. Multiplication
by the top-conormal monomial before Hilbertization gives the unique nonraw
strict coherent correction and restores literal dagger plus degree.

Actual rational-Witt stages are unit-group quotients and do not contain this
ramified fibre. Their minimal top-conormal thickening is handled by separate
finite-stage cocone module. Remaining Route-L theorem must prove conormal
grade intrinsic to framed coefficient and transport it coefficient-faithfully
and nonannihilatingly into actual completed Xi Gamma/co-Poisson Green
boundary before reflection-diagonal sewing. Current formalization does not
claim that landing or RH.
