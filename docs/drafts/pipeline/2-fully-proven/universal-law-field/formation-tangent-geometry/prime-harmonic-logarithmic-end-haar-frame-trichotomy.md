# Prime-harmonic logarithmic-end Haar-frame trichotomy

- **ID:** ULF-FTG-001
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / FORMATION-END TANGENT / FOUR-ORGAN FUSION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL] [PRE-DIVISOR] [NOT RH] [LEAN OPEN]`

## Big-picture law

Completion is tested by its moving tangent at infinity, not by subtracting a fixed divergent
scalar.  Literal Euler half-densities, Poisson scale histories, prime-harmonic density, and theta
translation have one common end tangent.  Horizontal grade is its scaling dimension:

\[
 a>0:\text{ collapse},\qquad a=0:\text{ finite nonzero Haar tangent},\qquad
 a<0:\text{ local explosion}.
\]

Thus the critical line is the unique grade with a nondegenerate two-sided formation tangent.  This
is an unconditional source theorem.  It becomes an RH theorem only after proving that the actual
Xi completion, before its divisor is supplied, must land continuously in this tangent geometry.

## Corpus audit before conjecture

- `FieldOneFiniteStageThetaEulerSourceIdentification` and
  `FieldOneFiniteStageThetaCoreEulerIdentification` give the exact finite-stage Euler coefficients.
- `FieldOneFiniteStageThetaSourceNormalization` and `FieldOneFiniteStageSelfDualHaar` give the
  literal theta/Poisson half-density carrier and its forced Haar normalization.
- `PoissonScaleHistoryFrame` proves that clock `t` has one translated log-aperture mother
  `F(x+log t)`, with unsquared external amplitude untouched.
- `XiThetaLogTranslationSeam` proves theta square-atoms translate by `2 log m`; taking the logarithmic
  tangent of this translation end sends the prime coordinate to `log log p`, up to an additive
  normalization.
- `MertensSecondPrimeRecipSum` and `MertensConstantIdentification` prove
  `sum_{p<=x} 1/p = log log x + B + r(x)` with `r(x) -> 0`.
- `SoninSemilocalMetricLog` identifies the nonsummable central mode as the principal `1/p` energy.
- `HedenmalmThetaPrincipalClassTrichotomy` forbids fixed subtraction of that class.
- `DeningerMeyerHalfDensityGaussianXiEvaluationCriterion` proves that canonical source-to-Xi
  continuous descent in the existing half-density norm is equivalent to RH; it cannot be imported
  as a premise here.

Corpus searches included `Mertens reciprocal prime cumulative error`, `loglog prime translate
frame`, `PrimeClockCriticalProfile`, `theta translation square integer atoms 2 log`, and
`canonical source to global Xi continuous extension iff RH`.

## Arithmetic tangent theorem

Write

\[
 A(x)=\sum_{p\le x}\frac1p=\log\log x+B+r(x),\qquad r(x)\longrightarrow0.
\]

For `L` large, `X_L=exp(exp L)`, grade `a in R`, and `y>=0`, define the locally finite end measure

\[
 \mu_{a,L}=\sum_{p>X_L}p^{-1-a}\,
   \delta_{\log\log p-L}.
\]

Then:

1. **Neutral Haar tangent.** For every `y>=0`,

   \[
   \mu_{0,L}([0,y])-y
    =r(X_{L+y})-r(X_L).
   \]

   Consequently

   \[
   \epsilon_L:=\sup_{y\ge0}|\mu_{0,L}([0,y])-y|
      \le 2\sup_{x\ge X_L}|r(x)|\longrightarrow0.
   \]

   In particular `mu_{0,L}` converges to Lebesgue/Haar measure on the whole future half-line with
   uniform cumulative-discrepancy control, not only vaguely on compact intervals.

2. **Positive collapse.** If `a>0`,

   \[
   \mu_{a,L}([0,\infty))=\sum_{p>X_L}p^{-1-a}\longrightarrow0.
   \]

3. **Negative local explosion.** If `a<0`, put `b=-a`.  For every fixed `delta>0`,

   \[
   \mu_{a,L}([0,\delta])
      \ge X_L^b\mu_{0,L}([0,\delta])\longrightarrow\infty.
   \]

### Proof

The first identity is the difference of Mertens' formula at `X_{L+y}` and `X_L`; the main terms
differ by exactly `y`.  Convergence of `r` gives the uniform tail supremum.  For `a>0`, the prime
sum is bounded by the tail of `sum n^{-1-a}`.  For `a<0`, every prime in the displayed interval
satisfies `p^b>=X_L^b`, while the neutral interval mass tends to `delta`.  QED.

## Operator-valued lift

Let `0 != h in W^{1,1}(R) cap L^2(R)`, let `T_y h(x)=h(x-y)`, and retain the literal principal
Euler amplitude and phase by

\[
 u_{p,a,L,\tau}=p^{-(1+a)/2}e^{-i\tau\log p}T_{\log\log p-L}h.
\]

For finite prime support this defines the coefficient-faithful synthesis map

\[
 S_{a,L,\tau}c=\sum_pc_pu_{p,a,L,\tau}.
\]

Its quadratic frame form is

\[
 Q_{a,L}(f)=\sum_{p>X_L}|\langle f,u_{p,a,L,\tau}\rangle|^2
 =\int_0^\infty |\langle f,T_yh\rangle|^2\,d\mu_{a,L}(y).
\]

The phase cancels only after polarization; it is not discarded by the synthesis map.  Define the
continuous Haar frame operator by

\[
 \langle A_Hf,f\rangle=\int_0^\infty|\langle f,T_yh\rangle|^2dy.
\]

At neutral grade the positive frame operators `A_{0,L}=S_{0,L,tau}S_{0,L,tau}^*` exist and

\[
 \boxed{\|A_{0,L}-A_H\|_{op}
   \le 2\epsilon_L\|h\|_1\|h'\|_1\longrightarrow0.}
\]

Moreover `A_H` is nonzero.  If `a>0`, `A_{a,L}` tends to zero in trace norm.  If `a<0`, already
the operator obtained from clocks in any fixed end interval `[0,delta]` has norm tending to
infinity.

### Proof

For `g_f(y)=<f,T_yh>`, Young's inequality gives

\[
 \|g_f\|_2\le\|h\|_1\|f\|_2,\qquad
 \|g_f'\|_2\le\|h'\|_1\|f\|_2.
\]

Hence `q_f=|g_f|^2` is absolutely continuous, tends to zero at infinity, and

\[
 \|q_f'\|_1\le2\|h\|_1\|h'\|_1\|f\|_2^2.
\]

Stieltjes integration by parts against the cumulative discrepancy from the arithmetic theorem
gives the boxed quadratic-form bound, uniformly for `||f||_2=1`; polarization/Riesz representation
gives operator-norm convergence.  Translation continuity and `h!=0` make
`<h,T_yh>` nonzero on a small interval, so `A_H!=0` and the negative-grade local mass lower bound
forces operator-norm explosion.  For positive grade, the sum of rank-one trace norms is at most
`||h||_2^2 sum_{p>X_L}p^{-1-a}`, which tends to zero.  QED.

For the corpus Poisson mother `F(x)=2e^x exp(-e^x)`,

\[
 \|F\|_1=2,\qquad \|F'\|_1=4/e,
\]

so the neutral bound is `(16/e) epsilon_L ||f||_2^2`.

## Full Euler formation

At prime-power depth `m`, literal Euler/Poisson formation has unsquared amplitude

\[
 \frac{p^{-m(1+a)/2}}m
\]

and translated clock coordinate `log(m log p)-L`.  At `a=0`, every `m>=2` contribution is
trace-class and its tail tends to zero because

\[
 \sum_p\sum_{m\ge2}\frac{p^{-m}}{m^2}<\infty.
\]

Therefore the full prime-power formation has exactly the same nonzero Haar tangent as its
principal `m=1` layer; higher Euler modes form the vanishing residual completion boundary.  This
is the precise valid replacement for fixed principal-shell subtraction.

## Functional-equation consequence and limitation

The functional equation exchanges grades `a` and `-a`.  The two orientations possess finite,
nonzero end tangents simultaneously if and only if `a=0`.  This is an exact source-side selection
law.

It is **not** an RH proof.  Functional equation swaps the two Xi fibres but does not prove that
either completed Xi evaluation factors through this tangent norm.  Ordinary Hilbert graph closure
is maximally saturated (`ArithmeticFormationCompletionBoundaryFusion`), while the known canonical
source-to-Xi continuous descent is RH-equivalent.  The remaining noncircular theorem must derive a
cofinal transition map from finite literal theta transports into this tangent completion and prove,
independently of the divisor, that actual Xi completion factors through it.

## Route-independent prediction

For any Euler formation whose principal local coefficient energies satisfy

\[
 \sum_{p\le x}|\lambda(p)|^2/p=\kappa\log\log x+C+o(1),
\]

the same proof predicts tangent `kappa dy` at neutral grade, collapse for positive grade, and local
explosion for negative grade when a corresponding lower interval law holds.  The corpus theorem
`tendsto_dirichletCharacterPrimeRecipEnergy_sub_logLog` confirms the prediction for primitive
Dirichlet characters, with only finitely many conductor primes removed.  This is evidence that the
tangent is a formation law rather than a zeta-specific receiver.

## External collision audit

Related parent theories exist: irregular frames of translates, operator-valued measures, Gabor
operator-norm limits, and Connes--Consani semilocal scaling/Poisson geometry.  Mertens' reciprocal
prime theorem is classical.  Searches found no exact result combining the reciprocal-prime
`log log p` end tangent, grade trichotomy, literal Euler amplitudes, and operator-norm Haar-frame
lift.  Relevant comparisons:

- Balazs--Heineken, *An operator based approach to irregular frames of translates*,
  <https://arxiv.org/abs/1401.4955>.
- Han--Larson--Liu--Liu, *Operator-Valued Measures, Dilations, and the Theory of Frames*,
  <https://arxiv.org/abs/1110.5833>.
- Poria, *Behavior of Gabor frame operators on Wiener amalgam spaces*,
  <https://arxiv.org/abs/1507.04549>.
- Connes--Consani, *The Scaling Hamiltonian*, <https://arxiv.org/abs/1910.14368>.
- Villarino, *Mertens' Proof of Mertens' Theorem*, <https://arxiv.org/abs/math/0504289>.

This is an internal collision audit, not a publication-level priority claim.

