# Shifted Reciprocal Moments Determine the Divisor

- **ID:** shifted-reciprocal-moments-determine-divisor
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / zero-feeding guardrail
- **Source:** RH landscape gate; reciprocal seam moment route
- **Statement:** In the reciprocal seam chart, the all-order shifted tower
  `T_k = sum_y M_y y^k` for `k>=1` determines the weighted reciprocal divisor.
  Therefore importing the whole shifted moment tower is already importing a
  zero-complete object unless the tower is independently constructed from source data.

## Setup

A reciprocal divisor datum is a countable multiset

`D={(y,M_y)}`

with `y in C*`, positive multiplicities `M_y`, conjugation symmetry, and

`sum_y M_y |y| < infinity`.

Assume `Y={y : M_y != 0}` has no accumulation point except possibly `0`; this is the
reciprocal-zero situation for

`y_rho = -(rho-1/2)^(-2)`.

Define the shifted moments

`T_k(D)=sum_y M_y y^k`, `k>=1`.

Equivalently, let

`nu_D = sum_y M_y y delta_y`.

Then `nu_D` is a finite complex measure and

`T_{n+1}(D)=int z^n dnu_D(z)`.

## Theorem

Let `D` and `D'` be two reciprocal divisor data satisfying the setup hypotheses. If

`T_k(D)=T_k(D')` for every `k>=1`,

then `D=D'` as weighted multisets.

Thus the all-order shifted reciprocal moment tower is faithful to the reciprocal
divisor.

## Proof

Let

`mu = nu_D - nu_D'`.

This is a finite complex measure. Its support is contained in

`K = Y union Y' union {0}`.

The set `K` is compact, countable, and has empty interior. The complement `C \\ K` is
connected for countable compact `K`. Hence, by Mergelyan's theorem, polynomials are
uniformly dense in `C(K)`.

The moment equality says

`int z^n dmu(z)=0`

for every `n>=0`. Therefore `int p(z) dmu(z)=0` for every polynomial `p`. By uniform
density and finiteness of `mu`, this extends to every continuous function on `K`.
The Riesz representation theorem then gives `mu=0`.

So `nu_D=nu_D'`. Since both measures have no atom at `0` and every support point
`y` is nonzero, the atom of `nu_D` at `y` has mass `M_y y`. Dividing by `y` recovers
`M_y`. Therefore the weighted multisets agree.

## Consequence for the RH Route

This theorem sharpens the source-aware `Q_0` warning.

The shifted tower `[T_{i+j+1}]` is the right finite-measure chart, but the full
all-order tower is not source-neutral. It is faithful to the reciprocal zero divisor.
Consequently:

1. A proof that assumes the full shifted tower has the source-built values has already
   assumed a zero-complete object unless those values are produced from Euler/Gamma/FE
   source data.
2. All-order `Q_0` positivity is a faithful RH chart, not a source proof by itself.
3. The missing theorem remains the source construction of the tower or of an equivalent
   polarized object without first reading the zeros.

In short: finite towers are blind; the infinite tower is faithful. The proof has to
explain why the source-built infinite tower lands in the positive cone.

## Source Boundary

The proof imports only compact polynomial approximation on countable compact sets
(Mergelyan) and elementary measure determinacy. It is not a new RH theorem. Its role is
to prevent an all-order moment tower from being treated as if it were independent
source data.

## Gates

- [x] 0 -> 1 in-progress: all-order shifted-tower zero-feeding risk isolated.
- [x] 1 -> 2 fully-proven: compact moment determinacy proof written.
- [x] 2 -> 3 formalized: `formal/GaloisForLFunctions/HTGeometry/AtomicMomentDeterminacy.lean`
  proves the determinacy **without** any polynomial-density import; see the certificate below.

## Log

- 2026-06-24 -- Professor: created under the RH-only goal after checking the finite
  spectral Torelli certificate. The finite Lean theorem covers finite multisets; this
  card records the compact countable reciprocal-divisor analogue for the shifted
  all-order tower.

## 2026-06-24 seam-log extraction companion

`seam-log-hankel-rh-equivalence.md` records the companion fact: the same all-order shifted tower is extracted from the canonical seam log jet by `T_k=-2k(-1)^k [z^k] log(Phi(z)/Phi(0))`, with `Phi(z)=Xi(sqrt(z))`. Thus the tower is simultaneously source-built from the canonical completed function and faithful to the reciprocal divisor. The remaining open content is the positivity of this source-built, divisor-faithful tower.

## 2026-06-24 source extraction needs canonical gauge

`reciprocal-seam-canonical-gauge-extraction.md` complements divisor determinacy with the source-side normalization. The shifted tower determines the reciprocal divisor, but a raw seam-log extraction from a zero-free gauged representative shifts the tower by an explicit local Hankel counterterm. The divisor-faithful source tower is the canonical completed `xi` extraction, or the corrected tower after subtracting that counterterm.

## 2026-06-24 protector tail companion

`tail-e-zero-support-nonselector.md` applies the same compact moment-determinacy principle to the protector Hankel tail. The shifted reciprocal tower determines the divisor; likewise, a full Hankel tail supported on the shifted reciprocal zero support determines its signed representing measure.

So the tail is zero-faithful in its own coordinate. It can record source finite-part anatomy, but it does not by itself provide the source theorem forcing the Stieltjes or boundary-index sign.

## 2026-07-15 disk-Schur contrast

`xi-radial-jensen-schur-capacity-rigidity.md` uses the same shifted reciprocal moments but changes
the approximation geometry.  Mergelyan approximation on the divisor-dependent countable compact
support can align arbitrary atom phases and is therefore zero-faithful.  Requiring one polynomial
to be contractive on the fixed unit disk prevents that free phase interpolation.  The stronger
source radius and sector bounds make the constant `1` the unconditional Schwarz--Pick extremizer:
the Schur norm is exactly the zeroth source moment.  Its deficit from the radial Jensen mass is
exactly half the global reflection energy.  Thus disk-Schur approximation compresses the complete
moment tower to the holomorphic source curvature; the complementary adjoint/polar channel carries
the orientation information.


## Lean certificate — 2026-08-16 (2→3 gate closed)

`formal/GaloisForLFunctions/HTGeometry/AtomicMomentDeterminacy.lean`, wired into the `HTGeometry`
umbrella; every declaration audits to `[propext, Classical.choice, Quot.sound]`.

The Lean proof does **not** use Mergelyan, and needs no polynomial-density theorem at all — mathlib
has neither.  The hypotheses of this card are stronger than "countable compact": the reciprocal
atoms accumulate only at the origin.  That is enough for an elementary argument:

1. normalize by an atom `z_{j₀}` of **maximal modulus** among those carrying nonzero weight — such an
   atom exists because only finitely many atoms exceed any positive modulus;
2. every normalized atom then lies in the closed unit disc, and `z_{j₀}` is the unique one equal
   to `1` (injectivity of the atom map);
3. average the vanishing moments over `n < N`.  Tannery's theorem exchanges the limit with the sum:
   a geometric progression in the closed unit disc with ratio `≠ 1` has vanishing Cesàro mean, so
   every other atom drops out and the surviving term is exactly the weight at `z_{j₀}`;
4. hence that weight is zero — contradicting its choice.

| Paper step | Lean |
|---|---|
| Cesàro means of a non-unit progression in the closed unit disc vanish | `norm_geomSum_le_of_norm_le_one`, `tendsto_geomSum_cesaro_of_norm_le_one`, `tendsto_shiftedGeomSum_cesaro` |
| every power moment of summable atomic data converges | `summable_atomicMoment` |
| **all moments vanish ⇒ all weights vanish** | `coeff_eq_zero_of_atomicMoments_vanish` |
| **`T_k(D) = T_k(D')` for `k ≥ 1` ⇒ `D = D'`** | `atomicData_eq_of_moments_eq` |
| the same with one extra atom at the accumulation point | `atomicData_withCenter_eq_of_moments_eq` |

Instantiation for this card: take `c_y = M_y · y` (absolutely summable exactly by the card's
hypothesis `Σ_y M_y |y| < ∞`) and `z_y = y`.  Then `Σ_y c_y y^{n} = T_{n+1}(D)`, so equality of the
shifted tower for `k ≥ 1` is equality of all moments of `c`, and the theorem gives `M_y y = M'_y y`,
hence `M_y = M'_y` since the atoms are nonzero.  Only moments of order `≥ 1` are consumed, which is
exactly the tower the card supplies.
