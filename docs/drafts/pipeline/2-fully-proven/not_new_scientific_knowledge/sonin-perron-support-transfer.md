# Sonin--Perron support transfer and coherence obstruction

- **ID:** sonin-perron-support-transfer
- **Stage:** 2-fully-proven
- **Type:** THEOREM / OBSTRUCTION, `[PROVED HERE]`
- **Date:** 2026-07-10
- **Parents:** `perron-carrier-flank-mass.md`, `sonin-euler-metric-corner-noncompact.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/SoninPerronSupportTransfer.lean`

## Medalist question

The Perron support theorem consumes geometric `L2` control on all negative integer lines.  An even
Sonin source supplies a physical gap, and that gap supplies every negative exponential moment.  The
field-level question is not whether Mellin--Plancherel transports those moments.  It does.  The
question is whether the transported `L2` classes can be the negative-line traces of one analytic
Dirichlet carrier, and what that compatibility would force.

The answer is rigid.  Exact cross-line coherence transfers physical support to arithmetic support:

`physical cutoff q  ==>  Dirichlet support n <= q^(-1)`.

Consequently, at every positive cutoff, coherence plus finite Perron horizontal mass permits only
finite coefficient support.  It is incompatible with every entire Dirichlet carrier whose
coefficient support is infinite.  Above unit cutoff it forces the entire carrier to be zero.

## Native objects

Let `f` belong to the even central Sonin carrier at cutoff `q>0`, and put

`g(t) = logEvenUnitary(f)(t)`.

Define lower support at `tau` by

`g(t)=0` for almost every `t<tau`.

For `M` a natural number, define the negative source weight and normalized trace

`g_M(t) = exp(-M t) g(t)`,

`T_M(g) = U_Mellin(g_M)`,

where `U_Mellin` is the normalized Fourier--Mellin linear isometry on `L2(R)`.

**Cross-line Mellin coherence** for an analytic carrier `F` is the constraint

`F(-M+it) = T_M(g)(t)` almost everywhere in `t`, for every natural `M`.       (C)

This is a compatibility among all lines of one analytic function.  It is strictly stronger than
constructing the lines separately as `L2` classes.

## Theorem A `[PROVED]`: the Sonin gap becomes lower logarithmic support

If `f` belongs to the even central Sonin carrier at cutoff `q>0`, then

`g(t)=0` almost everywhere on `t<log q`.                                      (1)

### Proof

The physical half of Sonin membership says that the cutoff projection of `f` on `[-q,q]` is zero.
The projection is the indicator of that interval, so `f(x)=0` almost everywhere there.  The map
`t |-> exp(t)` is quasi-measure-preserving.  Hence the vanishing statement can be pulled back along
it.  Since `exp(t)<q` whenever `t<log q`, the exact logarithmic unitary formula gives (1).

## Theorem B `[PROVED]`: lower support gives geometric negative moments

Let `g` be in `L2(R)` and vanish almost everywhere below `tau`.  Then for every natural `M`,

`g_M` belongs to `L2(R)` and

`||g_M||_2 <= exp(-M tau) ||g||_2`.                                           (2)

### Proof

Where `g` is nonzero, `t>=tau`.  Since `M>=0`,

`exp(-M t) <= exp(-M tau)`.

Thus `|g_M(t)|` is almost everywhere dominated by `exp(-M tau)|g(t)|`.  The `L2` domination theorem
gives membership and (2).  Applying the linear isometry `U_Mellin` gives

`||T_M(g)||_2 <= exp(-M tau) ||g||_2`.                                       (3)

At `tau=log q`, the factor is exactly

`exp(-M log q) = q^(-M)`.                                                     (4)

## Theorem C `[PROVED]`: coherence discharges negative-flank energy

Assume (C).  Equality almost everywhere identifies the vertical trace

`t |-> F(-M+it)`

with `T_M(g)`.  Equations (3)--(4) therefore prove

`(integral_R |F(-M+it)|^2 dt)^(1/2) <= q^(-M)||g||_2`.                       (5)

In the formal interface,

`HasCoherentNegativeMellinTraces`

constructs

`HasPerronCarrierFlankL2Energy`.

This discharges the quantitative negative-line Prop from source support plus one explicit seam
constraint.

## Theorem D `[PROVED]`: exact cross-support transfer

Let `F` be entire and agree on `Re(s)>=c>0` with an absolutely convergent Dirichlet series

`L(s) = sum_(n>=1) a_n n^(-s)`.

Assume:

1. `f` belongs to the even central Sonin carrier at cutoff `q>0`;
2. `F` and `logEvenUnitary(f)` satisfy cross-line coherence (C);
3. `F` has finite coefficient-independent Perron horizontal mass.

Then, for every `n>=1`,

`a_n != 0  ==>  n <= q^(-1)`.                                                (6)

### Proof

Theorems A--C give Perron flank `L2` energy bounded by

`B(M)=q^(-M)||g||_2`.

This is an exact geometric envelope of radius `q^(-1)`.  The coefficient-independent Perron carrier
theorem combines that energy with finite horizontal mass, manufactures the required contour escape,
and gives the exact arithmetic support inequality (6).

## Corollary E `[PROVED]`: finite-support rigidity at every positive cutoff

Under the hypotheses of Theorem D, the full coefficient support is finite.  Choose a natural `N`
with `q^(-1)<N`.  Equation (6) places every positive support index in `{1,...,N-1}`; index zero is a
single irrelevant exceptional index in the `LSeries` convention.  Hence

`support(a)` is finite.                                                       (7)

Equivalently, if `support(a)` is infinite and the other analytic and horizontal-mass hypotheses
hold, then cross-line coherence (C) is false for every `q>0`.

## Corollary F `[PROVED]`: above unit cutoff the carrier vanishes

If additionally `q>1`, then `q^(-1)<1`.  Every positive index satisfies `n>=1`, so (6) forces

`a_n=0` for every `n>=1`.

The `LSeries` is therefore zero on the right half-plane.  Since `F` is entire and agrees with it
there, the analytic identity theorem gives

`F=0` identically.                                                            (8)

Thus a nonzero entire Dirichlet carrier with finite horizontal mass cannot satisfy (C) with a Sonin
source at any cutoff `q>1`.

## Attack and falsification

- `[FAILED]` A critical-line Hardy--Titchmarsh `L2` class determines an entire carrier.  An `L2`
  class has no pointwise analytic representative and no upper exponential moments.  It supplies one
  spectral line, not a coherent analytic family of lines.
- `[BRIDGE]` The lower-support multiplier estimate and Mellin--Plancherel isometry are standard
  analysis.
- `[PROVED HERE]` The new content is the exact support transfer through the project-native Perron
  carrier interface and its finite-support/no-coherence consequences.
- `[FALSIFIED]` Exact equality of all weighted source transforms with the negative lines of a
  nonzero infinite-support Dirichlet carrier can serve as the missing seam while retaining finite
  horizontal mass.  Corollary E rules this out at every positive cutoff.

## What the theorem changes

The missing seam cannot be filled by declaring that every negative line is exactly the normalized
transform of the same lower-supported source.  That proposal is too rigid: together with the Perron
horizontal condition it collapses infinite arithmetic support to finite support.

The first viable infinite-support replacement has now been constructed in
`perron-mellin-seam-residue.md`.  The alternatives are:

1. `[PROVED]` an additive cross-line defect whose coefficient-indexed Perron residues recover the
   infinite arithmetic tail, without a finite geometric defect-norm bound;
2. a renormalized or cocyclic coherence law rather than equality (C);
3. failure of the finite horizontal carrier mass, followed by a different contour mechanism.

The obstruction is useful independently of which alternative survives: it specifies exactly what a
future weld is not allowed to identify.

## Novelty and significance gates

- **NOVEL:** the reciprocal support law (6), its finite-support consequence (7), and the resulting
  no-coherence theorem are not statements imported from the prior corpus.  They arise only after
  composing the new logarithmic-source trace object with the coefficient-independent Perron carrier
  theorem.
- **SIGNIFICANT:** the result rejects the most direct proposed weld between Sonin source geometry and
  an analytic Dirichlet carrier.  It also discharges the negative-flank energy Prop conditionally and
  replaces an amorphous “analytic continuation gap” by a precise cross-line defect problem.

## Scope

- The theorem does not assert cross-line coherence for the project target; it proves what coherence
  would force and then rules it out for infinite-support carriers under horizontal mass.
- The theorem does not prove finite horizontal carrier mass for the target.
- The theorem does not prove RH.  It removes one false source-to-carrier route and identifies the
  exact replacement object that must be constructed.

## Gates

- [x] 0 -> 1: lower-support source mechanism and coherence constraint isolated.
- [x] 1 -> 2: support transfer, finite-support rigidity, and no-go corollaries proved on paper.
- [x] 2 -> 3: all statements formalized in Lean.
- [ ] 3 -> 4: the additive seam law and its arithmetic coordinates are now proved; promotion
  requires constructing it for the target carrier and constraining those coordinates by divisor or
  cocycle data.
