# Time-one Gamma prime seams have finite factorial jet energy exactly on the critical line

- **ID:** `time-one-gamma-jet-fock-rh-criterion`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / EXACT RH CONSUMER / HT CLOCK BRIDGE
- **Scientific status:** `[PROVED HERE] [FORMALIZED]
  [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** `prime-laplace-gamma-jet-incidence-phase-transition.md`,
  `archimedean-meixner-root-seam-scale.md`, and
  `gamma-factorial-fock-polarization-boundary-charge.md`
- **Statement:** At the actual time-one Gamma--Meixner shape, the weighted prime--Laplace
  transform of a reflected rational-Hurwitz seam has finite factorial raw-jet energy at one safe
  base point if and only if the strip point lies on the critical line.  Hence RH is equivalent to
  one uniform cofinal Gamma-clock bound; no convolution-root deconvolution is needed for this
  criterion.

## The time-one source transform

Put

```text
w_1(p)=cosh(2log p)^(-1/2)
      =sqrt(2)p^(-1)(1+p^(-4))^(-1/2),                   (1)

M_1(s)=sum_p w_1(p)(log p)p^(-s),        Re s>0.         (2)
```

Let

```text
rho=1/2+a+i*t,       |a|<1/2,                            (3)
```

and define, initially for `Re z>1`,

```text
V_rho(z)=M_1(z+rho)-M_1(z+1-conjugate(rho)).             (4)
```

The prime coefficient of `(4)` is the conjugate reflected seam multiplied by the safe time-one
weight:

```text
V_rho(z)
 =sum_p w_1(p)(log p)
   [p^(-rho)-p^(-(1-conjugate(rho)))]p^(-z).             (5)
```

Every open-strip seam belongs to the time-one Meixner Hilbert domain because
`1>|2Re(rho)-1|`.  Thus `(4)` is the source-value transform of an honest time-one Hilbert vector,
not a formal divergent coefficient pairing.

## The source pole at zero

The exact weight `(1)` gives

```text
M_1(s)=sqrt(2) sum_p (log p)p^(-(1+s))+H(s),             (6)
```

where `H` is holomorphic on `Re s>-4`: the coefficient difference in `(6)` is
`O((log p)p^(-5-Re s))`.

For the prime zeta function `P`,

```text
sum_p (log p)p^(-(1+s))=-P'(1+s)=1/s+holomorphic        (7)
```

near `s=0`.  Consequently

```text
M_1(s)=sqrt(2)/s+holomorphic                             (8)
```

near zero.

## Cancellation exactly on the critical line

If `a=0`, then

```text
rho=1-conjugate(rho),
```

so the two terms in `(4)` are identical and

```text
V_rho=0.                                                 (9)
```

If `a>0`, the second term of `(4)` has an uncancelled simple pole at

```text
z_*=conjugate(rho)-1=-1/2+a-i*t,                         (10)
```

while the first argument there equals `2a>0`, where `(2)` is holomorphic.  If `a<0`, the first
term has an uncancelled simple pole at

```text
z_*=-rho=-1/2-a-i*t,                                     (11)
```

while the second argument there equals `-2a>0`.  In both cases

```text
Re z_*=-1/2+|a|<0.                                      (12)
```

Thus the time-one shape moves every off-line obstruction to a finite left-half-plane pole of the
prime--Laplace seam transform; only the critical-line pair cancels it.

## The pole is the reflected Mertens corona

Locally at the source boundary, equations `(4)` and `(8)` split as

```text
V_rho(z)
 =sqrt(2)[1/(z+rho)-1/(z+1-conjugate(rho))]
   + regular translated terms.                           (12a)
```

The polar doublet is

```text
sqrt(2)(1-rho-conjugate(rho))
 /[(z+rho)(z+1-conjugate(rho))].                         (12b)
```

Its coefficient is `sqrt(2)(1-2Re(rho))`.  The residue in `(8)` is the analytic form of the
actual unit-field Mertens corona: the prime degree-one source has a pole at its critical Abel
boundary, while the complete vanishing-tail layer contributes only regular germs there.

Thus the time-one criterion is not using an arbitrary new singularity.  It is the
anti-reflection translate of the sole continuous source quotient `[one]` left by the weighted
Euler joint-graph theorem.  The two translated corona supports are

```text
{-rho},       {conjugate(rho)-1};                         (12c)
```

they coincide in the global Laplace coordinate exactly on the critical line.

## Factorial raw-jet criterion

Fix one real base point `x_0>1`.  For `N>=1`, put

```text
E_N(rho)=sum_(j=0)^(N-1)|V_rho^(j)(x_0)|^2/j!.           (13)
```

Then

```text
sup_N E_N(rho)<infinity  iff Re(rho)=1/2.                (14)
```

The forward implication follows from `(9)`.  Conversely, suppose the supremum is finite and set

```text
c_j=V_rho^(j)(x_0)/j!.                                   (15)
```

Boundedness of `(13)` implies `j!|c_j|^2 ->0`, hence

```text
limsup_(j->infinity)|c_j|^(1/j)=0.                       (16)
```

The Taylor series at `x_0` therefore has infinite radius of convergence and extends `V_rho` to an
entire function.  This contradicts the uncancelled finite pole `(10)` or `(11)` whenever `a!=0`.
Thus `(14)` holds.

Equation `(13)` is exactly the factorial Fock norm of the first `N` raw derivative observations,
the positive metric selected by Gamma's opposite-variance jet clocks.

## Lean certificate

The dependency-closed module

```text
formal/GaloisForLFunctions/RHTower/TimeOneGammaJetFockRHCriterion.lean
```

formalizes every proved theorem on this card.  It identifies the complex prime transform with the
actual real time-one Mertens source, realizes the reflected seam as the value transform of an honest
time-one Meixner Hilbert vector, proves analyticity on the exact common convergence half-plane, and
proves critical-line cancellation.  For off-line points it derives the two normalized inward-ray
residues `-sqrt 2` and `+sqrt 2` at `(10)` and `(11)`.  Those nonzero residues give concrete
`NoExtensionAt` witnesses without assuming meromorphic continuation.

The general factorial-Fock entire-extension theorem then yields the exact iff `(14)`, explicit
cofinal divergence for every proposed off-line bound, and the Xi-divisor/RH equivalence `(17)`.
Principal declarations are:

```text
primeSeamTransform_one_ofReal_eq_timeOnePrimeLaplace
meixnerPrimeSeamValue_eq_reflected_transform_complex
analyticOnNhd_timeOneGammaPrimeSeam
tendsto_timeOneGammaPrimeSeam_right_residue
tendsto_timeOneGammaPrimeSeam_left_residue
timeOneGammaPrimeSeam_noExtensionAt_of_re_gt_half
timeOneGammaPrimeSeam_noExtensionAt_of_re_lt_half
timeOneGammaJetFockBounded_iff_re_eq_half
exists_timeOneGammaJetFockEnergy_gt_of_re_ne_half
summable_timeOneMeixnerSeamEnergy_of_openStrip
inner_timeOneMeixnerSeam_eq_timeOneGammaPrimeSeam
riemannHypothesis_iff_forall_xiDivisor_timeOneGammaJetFockBounded
```

The conjectural source producer `(18)` remains open and is not assumed by any declaration.

## Exact RH criterion

Every nontrivial Xi divisor point lies in the open strip.  Applying `(14)` fibrewise gives

```text
RH
 iff for every Xi divisor fibre rho,
       sup_N sum_(j<N)|V_rho^(j)(x_0)|^2/j!<infinity.    (17)
```

The base point `x_0>1` is arbitrary and one fixed choice suffices.  Under RH every energy in
`(17)` is zero.  If any off-line zero exists, its single positive summand diverges with the clock
resolution.

## Application conjecture for the HT anomaly field

`[CONJECTURE -- TIME-ONE POLARIZED CLOCK BOUND]` Construct `(4)` before divisor insertion as the
time-one Gamma--Meixner evaluation of the completed Euler anti-reflection anomaly.  For every
finite clock, identify its jet `(V,V',...,V^(N-1))` with the polarized source-anomaly colligation
and prove

```text
sup_N E_N(rho)<=C_rho<infinity                            (18)
```

whenever the completed Xi source constraint vanishes at `rho`.  The constant may depend on the
fibre; no uniformity in zero height is required for `(17)`.

If `(18)` is proved without using a zero-defined norm or assuming line location, `(14)` gives RH.
This is a smaller proof obligation than deconvolving the time-one Gamma carrier into every
positive Meixner root: it uses one actual archimedean measure and all HT observation resolutions.

An equivalent geometric formulation is:

```text
[CONJECTURE -- AFFINE-PINNED MERTENS BOUNDARY DESCENT]
```

On a completed Xi zero orbit, the FE--Schwarz source comparison identifies the two translated
time-one Mertens boundary germs in one Gamma-normalized global Laplace chart, preserving the
affine origin rather than allowing a recentering transport.  Equality of their singular supports
then turns `(12c)` into

```text
-rho=conjugate(rho)-1,
```

which is the critical-line equation.

This formulation names the exact datum which the full anomaly colligation must preserve: source
support plus affine origin.  Curvature or an abstract comparison torsor without that pinning can
transport one one-dimensional residue line to the other and proves nothing.

## Attacks and positive residues

1. **RH-equivalence attack.**  Equation `(17)` is a consumer, not a producer.  Its positive
   residue is the exact producer target `(18)`, with a fixed source measure and a fixed base point.
2. **Universal-jet attack.**  Taylor clocks exist for every analytic germ.  The positive residue
   is that `(4)` fixes the actual Euler anti-reflection vector and time-one Gamma weight; the
   completed source anomaly, not Taylor kinematics, must prove `(18)`.
3. **Finite-clock attack.**  Every `E_N` is finite even off the line.  The positive residue is the
   sharp cofinal dichotomy `(14)`: only a bound independent of clock resolution has content.
4. **Bare-curvature attack.**  Summability of Gamma's factorial boundary vector does not identify
   it with the raw jet of `V_rho`.  The positive residue is an explicit incidence equality to be
   proved, rather than an unspecified norm comparison.
5. **Naive-Fock attack.**  The full prime-to-factorial-Fock map is unbounded on arbitrary source
   vectors.  The positive residue is that the special on-shell vector `(4)` is the only required
   input; `(18)` is a relative-graph statement on the completed constraint, not global boundedness
   of the incidence operator.
6. **Corona-redressing attack.**  The scalar coefficient in `(12b)` already records
   `Re(rho)-1/2`; merely naming it as a corona charge is an RH restatement.  The positive residue
   is the affine-pinned descent conjecture: a proof must construct the common source chart and
   forbid translation gauge before reading the support equality.
7. **Unpinned-groupoid attack.**  Two simple-pole germs are abstractly isomorphic after translating
   their support.  The positive residue is the exact support law `(12c)`, which becomes selective
   only in the Gamma-normalized global Laplace coordinate retained by the full colligation.

## Parent-theory boundary

The prime-zeta pole, Taylor-radius criterion, and factorial Fock norm are classical.  The card is
an exact bridge and is not claimed as new scientific knowledge.  Candidate new content begins
only with a source proof of `(18)` through the HT anomaly colligation.

## Gates

- [x] identify the safe time-one weighted seam transform
- [x] compute the uncancelled off-line source pole
- [x] prove the finite-factorial-jet iff criterion
- [x] derive the exact RH equivalence
- [x] isolate the source-facing uniform clock bound
- [x] identify the off-line pole as the reflected Mertens corona doublet
- [x] state the affine-pinned boundary descent alternative and its transport falsifier
- [x] formalize the exact time-one transform and honest Hilbert-vector realization
- [x] formalize both off-line residues and no-extension obstructions
- [x] formalize the factorial raw-jet iff criterion and exact RH equivalence
- [ ] construct the completed Euler anti-reflection anomaly in the Gamma clock field
- [ ] prove the incidence identity and bound `(18)`
- [ ] deduce RH

## Lean completion log — 2026-08-24

`RHTower/TimeOneGammaJetFockRHCriterion.lean` is imported explicitly by `RHTower.lean`. Direct
source checking and targeted leaf build pass. `#print axioms` audits of every new declaration report
only `propext`, `Classical.choice`, and `Quot.sound`. Repository lint finds no forbidden declaration
in this module; its current nonzero exit is an unrelated pre-existing umbrella reachability failure
for `GaloisForLFunctions.HTGeometry.SecondOrderConstraintDescent`.
