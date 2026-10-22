# Theta-cusp dominant first-atom ratio certificate

- **ID:** `theta-cusp-dominant-first-atom-ratio-certificate`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Scientific status:** `[CONJECTURE]`
- **2026-07-20 target correction:** `[SUPERSEDED AS THE NATIVE GATE]`.  Conditions `(5)`--`(6)`
  remain a correct sufficient certificate, but the exact consumer is the single completed-source
  balance in `theta-cusp-gaussian-aperture-composite-balance.md`.  The positive first-atom endpoint
  slope is cancelled at first order by completed-source evenness and is not a boundary sign for
  the full aperture.
- **Statement:** The `n=1` theta-cusp atom has enough explicit ratio margin, and the `n>=2`
  atom tail is small enough, to prove the two quadratic source inequalities forcing the first
  nonconstant prime--Gamma Hankel block.

## Goal

Prove the first genuinely nonconstant slice of the countable prime--Gamma source Hankel cone from
the explicit theta source, without Xi zero locations, real-rootedness, a limiting positive measure,
or an RH-equivalent sign assumption.

## Source decomposition

For

\[
m_j=2\int_0^\infty x^{2j}\thetaCuspFullSource(x)\,dx,
\]

write

\[
m_j=a_j+r_j,
\]

where `a_j` is the contribution of `thetaCuspSourceTerm x 1` and `r_j` is the sum of all terms
with `n>=2`.  Every atom is positive on `x>0`, hence `a_j,r_j>=0`.

Under the substitution `t=n^2e^{2x}`, the contribution of the `n`th atom is

\[
a_{j,n}=
2\pi\,4^{-j}n^{-1/2}
\int_{n^2}^{\infty}
  \left(\log\frac{t}{n^2}\right)^{2j}
  \left(2\pi t^{5/4}-3t^{1/4}\right)e^{-\pi t}\,dt.       \tag{1}
\]

The integrand is positive for `n>=1`.  For `n=1`, `(1)` is a finite combination of even
parameter derivatives of

\[
I(s)=\pi^{-s-1}\Gamma(s+1,\pi).
\]

For `n>=2`, the lower endpoint `t>=n^2` exposes the factor `e^{-\pi n^2}` and gives a rapidly
summable explicit tail majorant.

## Uniform source-atom domination

`[PROVED IN LEAN]` For every `x>=0` and `n>=1`, the exact source atoms satisfy

\[
\Phi_n(x)\le q_n\Phi_1(x),\qquad
q_n=2n^4e^{-\pi(n^2-1)}.                                 \tag{2}
\]

The polynomial part gives the factor `2n^4`; the Gaussian exponent separates by

\[
n^2e^{2x}\ge (n^2-1)+e^{2x}.
\]

Moreover the full higher-atom weight has the unconditional rational bound

\[
Q:=\sum_{n\ge2}q_n\le\frac8{2997}.                       \tag{3}
\]

The Lean proof uses `pi>3.14`, a finite lower Taylor bound for `exp`, and the geometric
majorant

\[
q_{k+2}\le \frac1{375}\left(\frac1{1000}\right)^k.
\]

Consequently the same relative enclosure holds at every moment order:

\[
0\le r_j\le Q a_j,\qquad
a_j\le m_j\le\frac{3005}{2997}a_j.                       \tag{4}
\]

This replaces the former order-dependent tail bounds by one all-order value relation.

## Remaining finite certificate

It is now enough to prove only the two first-atom inequalities

\[
14\left(\frac{3005}{2997}a_2\right)^2\le9a_1a_3,         \tag{5}
\]

and

\[
16\left(\frac{3005}{2997}a_0\right)
  \left(\frac{3005}{2997}a_2\right)\le45a_1^2.           \tag{6}
\]

The enclosure `(4)` then gives

\[
14m_2^2\le9m_1m_3,
\qquad
16m_0m_2\le45m_1^2.
\]

The formal two-ratio gate therefore yields every linear-polynomial source Hankel inequality.

## Ward/Gibbs reduction `[PROVED IN LEAN]`

The first source atom is the Schwinger--Dyson/Ward image of the positive Liouville Gibbs atom

\[
b(x)=e^{x/2}e^{2x}e^{-\pi e^{2x}},\qquad
\Phi_1(x)=-2\pi\left(b'(x)+\tfrac12b(x)\right).
\]

For `B_k = integral_0^infinity x^k b(x) dx`, define

\[
U_0=2e^{-\pi}-B_0,\qquad
U_{j+1}=4(j+1)B_{2j+1}-B_{2j+2}.
\]

`PrimeArchThetaLiouvilleWard.lean` proves `a_j=2 pi U_j`, `U_j>=0`, and transports the all-order
enclosure `(4)` to

\[
2\pi U_j\le m_j\le\frac{3005}{2997}(2\pi U_j).
\]

It also proves directly that the two conditions

\[
14\left(\frac{3005}{2997}U_2\right)^2\le9U_1U_3,
\qquad
16\left(\frac{3005}{2997}U_0\right)
  \left(\frac{3005}{2997}U_2\right)\le45U_1^2
\]

imply every linear-polynomial prime--Gamma source Hankel inequality.  Thus the remaining finite
certificate can be proved in the positive truncated-Gamma Gibbs variables, with the zeroth-order
boundary charge isolated explicitly.

## Supersymmetric Morse/Born reduction `[PROVED IN LEAN]`

The Gibbs atom is itself the Born density of an exact supersymmetric Morse zero mode.  With

\[
t_n(x)=\pi(n e^x)^2,\qquad
\psi_{A,n}(x)=n e^{Ax}e^{-t_n(x)/2},\qquad
W_{A,n}(x)=t_n(x)-A,
\]

Lean proves

\[
(\partial_x+W_{A,n})\psi_{A,n}=0,
\qquad
(-\partial_x^2+W_{A,n}^2-2t_n)\psi_{A,n}=0,
\]

and the partner-potential shape invariance

\[
V_+(A,n)=V_-(A-2,n)+4(A-1).
\]

At `A=5/4`, `b_n=psi_(5/4,n)^2` and the source atom is the positive Born observable

\[
\Phi_n(x)=4\pi\bigl(W_{5/4,n}(x)-1/4\bigr)\psi_{5/4,n}(x)^2.
\]

Therefore the Ward variables are exactly the Born-observable moments `M_j(1)`, not merely
comparable to them.  The all-order enclosure and the final Hankel consumer have both been
transported to `M_j(1)`.  On `n>=1`, `x>=0`, Lean also proves the pointwise partner floor

\[
\pi^2-\pi/2+25/16\le V_+(5/4,n)(x).
\]

This exposes mixed position--momentum Gram matrices, the exact supercharge, and half-line
Witten-Laplacian coercivity as usable physics inputs.  The floor is not yet promoted to a spectral
gap, and ordinary position-moment positivity alone remains too weak for `(5)`.

## Anomalous Darboux/Doob reduction `[PROVED IN LEAN]`

For every polynomial `P`, `PrimeArchThetaMorseAnomalousDarboux.lean` proves the exact
ground-state transform and half-line boundary defect

\[
H_-(P\psi)=(-P''+2WP')\psi,
\qquad
(P\psi)'(0)+W(0)(P\psi)(0)=P'(0)\psi(0).
\]

For positive atom number, the dressed state belongs to the same Robin domain exactly when
`P'(0)=0`.  Applied to the normalized odd monomial whose derivative is `x^(2j)`, this isolates
`j=0` as the unique contact-anomalous Born moment and gives every atom moment the exact value
representation

\[
a_{j,n}=4\pi\int_0^\infty D_{j,n}(x)\,dx,
\]

where `D_{j,n}` is the formalized Morse Hamiltonian Ward density.  The corresponding Born moment
is `2 integral D_(j,n)`.  The two open inequalities `(5)`--`(6)` and their existing linear Hankel
consumer have been rewritten directly in these Hamiltonian Ward values.  This removes the
self-adjoint half-line momentum ambiguity and leaves a precise quantum-mechanical target: prove
the two displayed inequalities from mixed position--Hamiltonian positivity or coercivity.

## Born/Witten pure-state reduction `[PROVED IN LEAN]`

The positive Born observable can be absorbed completely into a new source-defined amplitude

\[
\chi_n(x)=2\sqrt{t_n(x)-3/2}\,\psi_n(x).
\]

Lean proves the exact static value identities

\[
\Phi_n(x)=\pi\chi_n(x)^2,
\qquad
(\partial_x+B_n)\chi_n=0,
\qquad
B_n'=2t_n+\frac{3t_n}{(t_n-3/2)^2},
\]

where `B_n=W_(5/4),n-t_n/(t_n-3/2)`.  Thus the formerly observable-weighted Born moments are
literal position moments of one supersymmetric ground state.  The full theta source is a sum of
these pure-state squares, the negative-log-density curvature has the pointwise floor
`4 pi n^2`, and polynomial test states have an exact Robin-domain classification.

The two open inequalities `(5)`--`(6)` and the linear Hankel conclusion are now stated directly in
the pure-state moments of `chi_1`.  This removes both the positive insertion and the half-line
momentum-domain ambiguity.  The curvature floor alone is not asserted to be a Brascamp--Lieb
spectral-gap theorem and does not by itself discharge either inequality.

## Numerical pre-certification

High-precision quadrature gives

```text
                         a_0                    a_1
n=1      4.969490382416646e-1     2.297141874217970e-2
n=2      1.717398877415948e-4     5.255729295068555e-7

                         a_2                    a_3
n=1      2.962841018448894e-3     5.992957351379432e-4
n=2      7.415238622609523e-9     2.114596358483180e-10
```

The `n>=3` contributions are already below `6e-11` at level zero and decay faster at the higher
levels.  The full-source ratios are

\[
\frac{m_1m_3}{m_2^2}\approx1.56826779548>\frac{14}{9},
\qquad
\frac{m_0m_2}{m_1^2}\approx2.79110285817<\frac{45}{16}.
\]

These computations select the constants and certify feasibility; they are not the proof.

## Positive chain

```text
explicit incomplete-Gamma bounds for the n=1 atom
  + explicit e^(-pi*n^2) bounds for the n>=2 tail
  -> two theta-cusp quadratic ratio inequalities
  -> first nonconstant theta-cumulant Hankel determinant
  -> all real linear-polynomial prime--Gamma source tests are nonnegative.
```

## Formal progress

`PrimeArchThetaAtomMoments.lean` proves unconditionally

\[
m_j=\sum_{n\ge0}a_{j,n},
\qquad a_{j,n}\ge0,
\]

by an `L¹`-justified sum--integral interchange.  It also defines the exact remainder

\[
r_j=m_j-a_{j,1}\ge0
\]

and proves `m_j=a_{j,1}+r_j`.

`PrimeArchThetaSourceAtomDomination.lean` now proves unconditionally and without numerical
approximation the pointwise domination `(2)`, the summable tail bound `(3)`, the all-order moment
enclosure `(4)`, and the transfer from `(5)`--`(6)` to every linear-polynomial prime--Gamma
source Hankel test.  The higher-atom tail is therefore closed.  Only the two explicit first-atom
incomplete-Gamma inequalities remain open for this block.

`PrimeArchThetaMorseGroundState.lean` strengthens the same open core by replacing the first-atom
variables with moments of one positive observable in an explicit zero-energy Morse state.  This
does not discharge `(5)`--`(6)` by itself; it provides new exact operator relations with which to
attack them without changing their value content.

`PrimeArchThetaMorseAnomalousDarboux.lean` applies those relations to the whole moment family.  It
classifies the Robin-domain anomaly, identifies every existing first-atom/Born moment with an
integrated Hamiltonian Ward density, and connects the resulting two Hamiltonian inequalities to
the already-formalized linear Hankel conclusion.  The values required by `(5)`--`(6)` remain open.

`PrimeArchThetaBornWittenGroundState.lean` and `PrimeArchThetaBornWittenBootstrap.lean` absorb the
Born observable into an exact source amplitude, identify all existing moments with its ordinary
position moments, prove the source-defined logarithmic curvature and polynomial Robin anomaly, and
connect the resulting pure-state inequalities to the same Hankel conclusion.  The two numerical
value inequalities remain the open core.

Principal declarations:

- `thetaCuspAtomRawEvenMoment`
- `thetaCuspAtomRawEvenMoment_nonneg`
- `thetaCuspRawEvenMoment_eq_tsum_atomRawEvenMoment`
- `thetaCuspHigherAtomRawEvenMoment`
- `thetaCuspHigherAtomRawEvenMoment_nonneg`
- `thetaCuspRawEvenMoment_eq_one_add_higher`
- `thetaCuspSourceTerm_le_first`
- `thetaCuspHigherAtomDominationWeight_le_geometric_rational`
- `thetaCuspHigherAtomRawEvenMoment_le_first`
- `thetaCuspRawEvenMoment_le_first_atom_factor`
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_first_atom`
- `thetaCuspSourceTerm_eq_liouvilleWard`
- `thetaCuspAtomRawEvenMoment_succ_eq_liouvilleGibbs`
- `thetaCuspRawEvenMoment_between_firstAtomWardMoment`
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_liouvilleWard`
- `thetaCuspMorseZeroMode_schrodinger_zero`
- `thetaCuspMorse_shapeInvariant`
- `thetaCuspMorsePotentialPlus_floor`
- `thetaCuspSourceTerm_eq_morseBornObservable`
- `thetaCuspAtomRawEvenMoment_eq_morseBornMoment`
- `thetaCuspRawEvenMoment_between_morseBornMoment`
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_morseBorn`
- `thetaCuspMorse_robinDefect_eq_zero_iff`
- `thetaCuspMorseHamiltonianMinus_dressedPolynomial`
- `pow_mul_thetaCuspSourceTerm_eq_morseHamiltonianWard`
- `thetaCuspAtomRawEvenMoment_eq_morseHamiltonianWard`
- `thetaCuspRawEvenMoment_eq_tsum_morseHamiltonianWard`
- `thetaCuspMorseBornMoment_eq_morseHamiltonianWard`
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_morseHamiltonianWard`
- `thetaCuspSourceTerm_eq_pi_mul_bornWittenAmplitude_sq`
- `thetaCuspFullSource_eq_pi_mul_tsum_bornWittenAmplitude_sq`
- `thetaCuspBornWitten_supercharge_zero`
- `thetaCuspBornWittenCurvature_floor`
- `thetaCuspBornWittenLogCurvature_floor`
- `thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq`
- `thetaCuspRawEvenMoment_eq_tsum_integral_bornWittenAmplitude_sq`
- `iteratedDeriv_XiC_zero_eq_tsum_bornWittenAmplitude_sq`
- `thetaCuspBornWittenRawMoment_eq_thetaCuspRawEvenMoment`
- `normalizedPrimeArchMoment_one_eq_bornWittenQuadraticSource`
- `thetaCuspBornWitten_robinDefect_eq_zero_iff`
- `forall_primeArchSourceTraceHankel_linear_nonneg_of_bornWittenAmplitude`

## Gates

- [x] source-pure atom decomposition identified
- [x] exact incomplete-Gamma integral representation derived
- [x] viable rational ratio window identified numerically
- [x] prove the sum-integral atom decomposition in Lean
- [x] prove nonnegativity of every atom and the higher-atom remainder
- [x] prove one pointwise domination valid for every source atom
- [x] prove the all-order relative tail bound `Q <= 8/2997` in Lean
- [x] reduce the full-source ratios to two buffered first-atom inequalities
- [ ] prove explicit rational enclosures for `a_0,a_1,a_2,a_3`
- [ ] prove inequalities `(5)` and `(6)`
- [ ] formalize the remaining incomplete-Gamma certificate in Lean
- [ ] extend the dominant-atom mechanism beyond the first Hankel block

## Quadratic Stein--Robertson reduction `[PROVED IN LEAN]`

For the `k=1,n=1` radial pure state `eta=x*chi_1`, let `J_r=integral x^r eta^2` and use the quadratic quantum vector field

```text
P(x)=x-x^2/2,
S_P=P(B_1-1/x)-P'/2=(x-x^2/2)B_1+x-3/2.
```

`PrimeArchThetaQuadraticSteinRobertson.lean` proves the exact half-line Stein covariance and Robertson inequality

```text
C = integral (x^2-x^3/2) eta^2,
E = integral S_P^2 eta^2,
(J_0*C)^2 <= (J_0^2*J_4-J_0*J_2^2)*E.
```

It also proves unconditionally that `E` is finite and strictly positive, using an explicit polynomial--Gaussian energy majorant, and that the single scalar certificate

```text
(14*(3005/2997)^2-9)*J_2^2*E <= 9*J_0*C^2
```

implies the open upper first-atom inequality `(5)`.  The resulting theorem feeds directly into the existing linear prime--Gamma source Hankel consumer.  Ordinary dilation `P=x` was numerically falsified at the required constant; the quadratic field clears the buffered variance threshold by about `0.749%`.  The scalar energy estimate is now the open upper-ratio core; the relaxed condition `(6)` remains independent.

## Likelihood-ordered transfer sharpening `[PROVED ON PAPER]`

The later exact likelihood-ratio order between the first atom and the complete higher tail shows
that the coordinatewise enclosure in `(5)`--`(6)` pays one factor too many. If

```text
c=3005/2997,
```

then it is enough to prove

```text
14*c*a_2^2<=9*a_1*a_3,
16*c*a_0*a_2<=45*a_1^2.                                  (19)
```

Indeed the cross-moment law

```text
r_(k+n)*a_k<=a_(k+n)*r_k
```

makes `r_j/a_j` nonincreasing. It bounds `m_2` by `a_2*m_1/a_1`; combining this once with
`m_j<=c*a_j` proves both full-source inequalities. The paper proof is
`../2-fully-proven/not_new_scientific_knowledge/theta-cusp-likelihood-ordered-tail-single-loss-transfer.md`.

The existing Lean consumers still encode the older `c^2` sufficient conditions. A successor
formalization should replace them by `(19)` and lower the quadratic Stein/Rayleigh coefficient
from `14*c^2-9` to `14*c-9`. The analytic first-atom and degree-two-tail problems remain open.

## Reflected half-density budget transfer `[PROVED ON PAPER]`

The exact Ward--Laplace shift of the Liouville--Gibbs atom closes both source transforms at the
reflected half-density points.  For the first atom and its higher tail this gives

```text
sum_(j>=0) a_j/(4^j*(2*j)!)=(4*pi-1)*exp(-pi),
H:=sum_(j>=0) r_j/(4^j*(2*j)!)=1/2-(4*pi-1)*exp(-pi).
```

Combining this value relation with the formal monotonicity of `r_j/a_j`, and retaining the Gaussian
cusp damping in the atom comparison, proves

```text
W=a_0+a_1/8,
H<(8/2997)*a_0<(8/2997)*W.
```

It is enough to prove

```text
14*(W+H)*a_2^2 <= 9*W*a_1*a_3,
16*(a_0+H)*a_2 <= 45*a_1^2.                              (20)
```

These conditions are strictly weaker than `(19)` because `H/W<8/2997` and
`H<(8/2997)*a_0`.
The paper proof, including the all-order Ward--Laplace Taylor constraints, is
`../../../3-formalized/not_new_scientific_knowledge/theta-cusp-half-density-ward-laplace-budget-transfer.md`.
The branch-activation proof is
`../../../3-formalized/not_new_scientific_knowledge/theta-cusp-half-density-damped-tail-domination.md`.
The truth of the two weakened inequalities in `(20)` has not been assessed numerically under the
active no-computation restriction.

## Antisymmetric reflection and Turan-curvature reduction `[PROVED ON PAPER]`

The difference, rather than the sum, of the two Ward--Laplace half-density values gives the exact
odd-moment budget

```text
sum_(j>=0) M_(2*j+1)/(4^j*(2*j+1)!)=exp(-pi),
```

where `M_k=integral x^k*f_1(x) dx`.  The higher-atom constant also cancels identically:

```text
T_1=sum_(j>=1) a_j/(4^j*(2*j)!),
T_2=sum_(j>=2) a_j/(4^j*(2*j)!),
a_0+H=1/2-T_1,
W+H=1/2-T_2.
```

Consequently the second inequality in `(20)` follows already from the finite first-atom condition

```text
8*a_2 <= 45*a_1^2+2*a_1*a_2+a_2^2/24.                 (21)
```

More structurally, set

```text
D_m=M_(2*m)^2-(2*m-1)/(2*m+1)*M_(2*m-2)*M_(2*m+2).
```

The two conditions in `(20)` are exactly a lower bound on `D_1` and an upper bound on `D_2`.
Both are generated by the one slope-curvature function

```text
E(x)=d/dx (V'(x)/x),
V=-log(f_1).
```

The singular boundary part is favorable and explicit:

```text
D_m=s_0/(2*m+1)
      *(M_(2*m-1)*M_(2*m+2)-M_(2*m)*M_(2*m+1))+G_m,
```

where `s_0=(log f_1)'(0)>0`, the determinant is nonnegative, and `G_m` is the regular-curvature
double integral.  The exact first-atom potential additionally satisfies `V''>=19`.

The regular curvature changes sign exactly once.  Each `G_m` is its pairing with a positive
strictly unimodal crossing window `K_m`, whose unique peak is
`sqrt(M_(2*m+2)/M_(2*m))`.  Thus the open core is no longer two unrelated incomplete-Gamma
enclosures.  It is the paired one-seam window estimate `(G_1 lower, G_2 upper)` recorded in
`../2-fully-proven/not_new_scientific_knowledge/12-prime-theta-fock-incidence/theta-cusp-antisymmetric-half-density-turan-curvature-transfer.md`.
The exact remaining research interface is
`theta-cusp-one-seam-turan-window-balance.md`.  No generic log-concavity argument supplies both
directions.  Its continuous value-chart input is
`../2-fully-proven/not_new_scientific_knowledge/12-prime-theta-fock-incidence/theta-cusp-continuous-half-density-residual-tail-chart.md`:
both tilted residual transforms are elementary at every cutoff, and the unique regular-curvature
seam occurs before `log 2`.
