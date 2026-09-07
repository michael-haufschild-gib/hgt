# Center-mixed theta positivity: current Fourier formulation

Status: Fourier incidence and the complete signed-jet criterion are formalized. The required
unconditional Fourier sign remains open. This card records the current mathematical statement;
the [direct source-energy attempt](clg-ttf-all-polynomial-source-energy.md) contains the unresolved
source estimates.

## Literal source and density

Use the corpus definitions `thetaCuspFullSource` and `thetaCuspCenterMixedDensity`:

```
Φ(x) = Σ_(n≥1) (4π²n⁴exp(9x/2) - 6πn²exp(5x/2)) exp(-πn²exp(2x)),
D_a(t) = ∫_(r>0) r sinh(ar) Φ(r/2+t) Φ(r/2-t) dr,
0<a<1/2.
```

The complete source is even and strictly positive. The density is even, nonnegative,
integrable, smooth, and strictly decreasing on positive displacements. In particular, a negative
numerical value for this literal density contradicts the proved source sign and cannot be used
as evidence. Pointwise positivity of `D_a` does not imply positivity of its Fourier transform.

Current Lean sources:

- `ThetaWignerCenterMix`: `thetaCuspCenterMixedDensity_even`,
  `thetaCuspCenterMixedDensity_nonneg`, `integrable_thetaCuspCenterMixedDensity`.
- `ThetaCuspKernelLogConcavity`: complete-source logarithmic concavity and positivity.
- `ThetaCuspCenterMixedFirstJetStrict`: `thetaCuspCenterMixedDensityFirstJet_lt_zero`
  and `strictAntiOn_thetaCuspCenterMixedDensity`.
- `ThetaCuspCenterMixedSignedJetCompleteness`:
  `contDiff_infty_thetaCuspCenterMixedDensity`.

## Exact Fourier normalization

Define the unnormalized Fourier transform by
`Dhat_a(s)=∫_ℝ D_a(t)exp(-ist)dt`. The corpus's autocorrelation tangent satisfies
`F_a(2t)=D_a(t)`, and its current is

```
J_a(b) = ∫_ℝ F_a(u)exp(-ibu)du = 2 Dhat_a(2b),
J_a(b) = 2 Im[XiC'(b-ia) conjugate(XiC(b-ia))]
       = ∂_a |XiC(b-ia)|².
```

These identities hold at zeros as well as away from them. They are formal theorems, including
the Fourier–Laplace integrability and source incidence. The relevant declarations are
`ofReal_thetaCuspCenterMixedFourierCurrent` in
`ThetaCuspCenterMixedSignedJetCompleteness`, and
`thetaCuspCenterMixedFourierCurrent_eq_xiTransverseEnergyCurrent` with
`hasDerivAt_normSq_XiC_transverse` in `ThetaCuspCenterMixedDivisorTomography`.

When changing variables to separate the two source factors, retain those factors until absolute
integrability has been justified. The isolated transform of `r sinh(ar)` is not an ordinary
convergent Fourier integral. The existing proof handles the complete source integrand; no
unproved contour shift or extra zero hypothesis remains in this Fourier identity.

## Complete sign criterion and its quantifiers

For a fixed aperture, positivity of all translation-invariant matrices
`[D_a(t_i-t_j)]` is the positive-definiteness/Fourier-sign condition for `D_a`.
The formal signed-jet formulation is

```
s_(2k)(a)=(-1)^k D_a^(2k)(0),    s_(2k+1)(a)=0,
m_n(a)=2π · 2^(-n) · s_n(a),

(∀ N,v, Σ_(i,j<N) v_i v_j s_(i+j)(a) ≥ 0)
  ↔ (∀ b, J_a(b)≥0).
```

Source-derived exponential decay supplies the determinacy needed for this equivalence.
`thetaCuspCenterMixedSignedJetCone_at_iff_pointwise` proves the fixed-aperture statement;
`thetaCuspCenterMixedSignedJetCone_iff_riemannHypothesis` proves

```
RH ↔ ∀ a∈(0,1/2), ∀ b∈ℝ, J_a(b)≥0.
```

A sign at one fixed aperture is not this quantified RH criterion. Likewise, a nonnegative
derivative at one aperture does not by itself give monotonicity on an interval of apertures.
At each fixed real frequency, proving the derivative sign throughout that interval would give
the required monotonicity of the squared modulus.

The full signed rank-six mixed section is strictly positive. Larger sections remain obligations;
the complete criterion supplies no induction from a finite section. A proof of a propagation
law covering every order would be legitimate progress; recording more finite sections alone
does not establish the universal statement.

## Source obligation

The missing result is an unconditional comparison for the complete source, valid for every
frequency and every critical aperture. Equivalently it must prove every finite signed Hankel
form nonnegative. The complex Fourier pair, differentiation under the integral, all-order jet
incidence, and determinacy are already available and should not be rebuilt as substitutes for
that sign.

Generic source positivity, evenness, and logarithmic concavity are insufficient; the corpus's
`HTGeometry.LaguerreKernelCounterexample` proves this. A convexity test of `D_a` on the whole
positive ray is also inappropriate: smooth evenness forces `D_a'(0)=0`, while its derivative is
strictly negative at positive displacements. A differentiable convex function on that ray would
have a nondecreasing derivative. No numerical convexity scan is needed to resolve that conflict.

The current direct work retains complete source pairings, all cross terms, and any correction's
boundary values. Neither a numerical Fourier sample nor a reformulation of the same sign is
an unconditional proof of RH.

## Audit of a claimed theta approximation closure

[Shi, arXiv:1706.08868v1](https://arxiv.org/html/1706.08868v1) asserts uniform convergence
`H_n=H(14,n,·)→Xi` near zero (Theorem 3.6), uses the scaling
`W_n(z)=H_n(2z/log n)` (3.46), and splits `W_n=U_n−V_n` into positive-kernel
cosine transforms. Its claimed first positive roots satisfy
`π/2<x_1(n)<y_1(n)<π` for all sufficiently large odd `n` (Theorem 4.4, (4.14)).
The coefficients in (4.5) are half those in (3.48); this changes the normalization
of `W_n` by a positive factor of two, and does not change the following contradiction.

**Analytic audit, not a Lean theorem:** these assertions are incompatible. Since `Xi(0)>0`,
convergence gives `W_n(0)>0` eventually. Positivity of `V_n(0)` and the absence of its
zeros before `y_1(n)` give `V_n(x_1(n))>0`. Therefore

```
W_n(x_1(n)) = -V_n(x_1(n)) < 0.
```

The intermediate value theorem supplies a zero `w_n∈(0,π)` of `W_n`. Consequently
`H_n(z_n)=0` with `z_n=2w_n/log n→0`. Uniform convergence near zero and continuity of
`Xi` imply `H_n(z_n)→Xi(0)>0`, a contradiction. No numerical zero, global zero theorem,
or use of Hurwitz is needed.

An explicit frequency pinpoints an incompatible sign claim without locating roots.
Equation (4.20) and its `V_n` counterpart give

```
W_n(x) = 2(u_2(n,x)−u_1(n,x)) cos x
       + 2x(v_2(n,x)−v_1(n,x)) sin x.
```

At `x=π`, this is `W_n(π)=−2(u_2(n,π)−u_1(n,π))`. Convergence forces its left side
eventually positive. Proposition 4.2, (4.4), claims `u_2(n,x)>u_1(n,x)` for every
real `x` and sufficiently large odd `n`, which forces the right side negative.
Thus, if the approximation convergence is retained, that uniform sign claim is false.
More precisely, under the normalization of (4.5), convergence and the exact formula force
`u_2(n,kπ)−u_1(n,kπ)→(−1)^k Xi(0)/4` for each fixed nonnegative integer `k`.
This locates the incompatible claimed inequality; it does not independently validate
every preceding approximation estimate or locate the erroneous intermediate step of its proof.

The positive constraint exposed by the audit is stronger than excluding this ordering:
for every fixed `R`, the stated convergence forces the rescaled `W_n` to converge uniformly
on `[-R,R]` to a positive constant (`Xi(0)` or `Xi(0)/2`, according to normalization).
Thus its real zeros must escape every fixed compact interval. Proof: split the uniform error
into `|H_n(2z/log n)−Xi(2z/log n)|` and `|Xi(2z/log n)−Xi(0)|`; both tend uniformly to zero.
This is a paper-level consequence of the asserted approximation convergence, not an
unconditional formal result for those unformalized approximants. It supplies no missing
CLG/TTF source sign.

There is also a direct scaling error in Lemma 3.11: a strip `|Im z|≤1/2` for `W_n`
corresponds to `|Im z|≤1/log n` for `H_n`, rather than `|Im z|≤(log n)/4`.
