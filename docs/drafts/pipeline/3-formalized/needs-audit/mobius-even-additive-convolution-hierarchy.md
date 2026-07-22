# Even additive Möbius hierarchy and the missing higher-convolution factor

- **ID:** `mobius-even-additive-convolution-hierarchy`
- **Status:** `[FORMALIZED] [BRIDGE] [NEEDS NOVELTY AUDIT]`
- **Source:** Möbius--Laplace frontier after the Gamma--Hankel localization wall
- **Claim grade:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED]`

## Exact hierarchy

Put

\[
  M(N)=\sum_{n\le N}\mu(n),\qquad
  \Phi(x)=\sum_{n\ge1}\mu(n)e^{-nx}.
\]

For an integer `d >= 1`, define the fixed-simplex additive convolution

\[
  V_d(N)=\sum_{a_1+\cdots+a_d=N}M(a_1)\cdots M(a_d).
\]

Since

\[
  \sum_{N\ge0}M(N)z^N=\frac{\sum_{n\ge1}\mu(n)z^n}{1-z},
\]

absolute convergence for `0 < z < 1` gives the exact `d`-fold identity

\[
  \Phi(x)^d=(1-e^{-x})^d\sum_{N\ge0}V_d(N)e^{-Nx}.       \tag{1}
\]

This is the correctly indexed higher-additive object. It retains all `d` Mertens factors.

## Even-order one-sided RH criterion

Let `d >= 2` be even. Then, after supplying the classical Littlewood implication

\[
  \mathrm{RH}\Longrightarrow
  M(N)=O_\delta((N+1)^{1/2+\delta})\quad(\delta>0),       \tag{2}
\]

the following are equivalent:

1. RH;
2. for every `epsilon > 0`, there is `C_epsilon >= 0` such that
   \[
     V_d(N)\le C_\varepsilon (N+1)^{3d/2-1+\varepsilon}
     \qquad(N\ge0).                                      \tag{3}
   \]

Only the upper sign in (3) is needed.

### Forward direction: (3) implies RH

Because `d` is even and `Phi(x)` is real, the left side of (1) is nonnegative. Apply (3)
termwise in (1). The standard exponential-moment estimate gives

\[
  \sum_{N\ge0}(N+1)^{3d/2-1+\varepsilon}e^{-Nx}
  \ll_{d,\varepsilon}x^{-3d/2-\varepsilon}
  \qquad(0<x\le1).
\]

Using `1-e^{-x} <= x`,

\[
  |\Phi(x)|^d\ll_{d,\varepsilon}x^{-d/2-\varepsilon},
  \qquad
  |\Phi(x)|\ll_{d,\varepsilon}x^{-1/2-\varepsilon/d}.    \tag{4}
\]

The all-`epsilon` family supplies every strict half-power bound. The formalized
decay-to-Mellin-continuation bridge then excludes zeta zeros in `Re(s) > 1/2`; functional-equation
symmetry gives RH.

### Reverse direction: RH implies (3)

Fix `epsilon > 0` and use (2) with `delta=epsilon/d`. Every composition
`a_1+...+a_d=N` has `a_j+1 <= N+1`, so each summand has norm at most

\[
  C_\delta^d(N+1)^{d/2+\varepsilon}.
\]

There are at most `(N+1)^(d-1)` such compositions. Therefore

\[
  |V_d(N)|\le C_\delta^d(N+1)^{3d/2-1+\varepsilon},
\]

which implies the one-sided estimate (3).

The critical exponent is thus `3d/2-1`, not a dimension-dependent relaxation of the half-power
wall. Increasing additive order does not make RH easier: every even rung is another exact copy of
the Mertens half-power source.

## First nonlinear rung (`d=4`)

Let

\[
  U(N)=\sum_{a+b=N}M(a)M(b).
\]

The already formalized quadratic identity is

\[
  \Phi(x)^2=(1-e^{-x})^2\sum_{N\ge0}U(N)e^{-Nx}.
\]

Define

\[
  W(N)=\sum_{a+b=N}U(a)U(b)=V_4(N).
\]

Then

\[
  \Phi(x)^4=(1-e^{-x})^4\sum_{N\ge0}W(N)e^{-Nx}.          \tag{5}
\]

Consequently the one-sided family

\[
  W(N)\le C_\varepsilon(N+1)^{5+\varepsilon}             \tag{6}
\]

implies RH, and RH implies (6) through Littlewood. This is the Lean target: it reuses the existing
second-Cesaro/Mertens object and needs only one additional Cauchy product.

## Hostile attack against the recent ternary route

Banks--Shparlinski, *Multiple sums with the Mobius function* (QJM 77 (2026), 109--127), prove
bounds for

\[
  \sum_{f(n_1)+g(n_2)+P(n_3)=M}u_{n_1}v_{n_2}\mu(n_1n_2n_3).
\]

This does not supply the coefficient of `Phi^3`:

- `mu(n_1 n_2 n_3)` equals `mu(n_1)mu(n_2)mu(n_3)` only on the pairwise-coprime squarefree
  stratum;
- the omitted gcd strata have positive density and cannot be discarded as lower order;
- even granting a complete coprimality decomposition, their unconditional long-interval estimate
  saves arbitrary logarithms from the natural `N^2` fixed-sum scale, while the even hierarchy
  requires a power-scale square-root threshold. For `d=4`, (6) saves two full powers from the
  trivial cumulative `N^7` Mertens-convolution majorant (or from `N^4` at the first-cumulative
  Mobius-simplex level).

Thus current ternary technology misses both the arithmetic object and the required exponent.

Primary source: <https://arxiv.org/abs/2506.08787>.

## Correction to a March 2026 arbitrary-summand preprint

Cantarini--Gambini--Zaccagnini, *On the discrete convolution of the Liouville and Mobius
functions*, correctly begins with the `d`-fold Laplace convolution

\[
  (G_1*\cdots*G_d)(x)=\frac1{(d-1)!}
  \sum_{n\le x}\mathcal G_d(n)(x-n)^{d-1}.               \tag{7}
\]

Its next displayed recursion replaces the right side by repeated integrals involving
`mathcal G_(d-1), mathcal G_(d-2), ...`, thereby dropping arithmetic factors. That recursion is
false for `d >= 3`.

A symbolic counterexample uses `g_1=g_2=g_3=delta_1`. Then `mathcal G_3=delta_3`, and the `d=3`
left side of (7) is

\[
  \frac12(x-3)^2\mathbf 1_{x\ge3}.
\]

The claimed first reduction uses `mathcal G_2=delta_2` and equals

\[
  \int_0^x\sum_{n\le y}\mathcal G_2(n)(y-n)\,dy
  =\frac12(x-2)^2\mathbf 1_{x\ge2},
\]

so the two sides have different support before any asymptotic issue arises.

Correct recursion retains the removed arithmetic function:

\[
  C_d(x)=\sum_{m\le x}g_d(m)\int_0^{x-m}C_{d-1}(y)\,dy,
  \quad
  C_j(x)=\frac1{(j-1)!}\sum_{n\le x}\mathcal G_j(n)(x-n)^{j-1}. \tag{8}
\]

Equivalently, keep the genuine Laplace convolution `G_1*...*G_d`. Expanding `d` Mertens or
Liouville summatory explicit formulas therefore produces zero sums of orders through `d`, not only
the double-zero terms displayed later in that preprint. The main scale also exposes the loss:
convolving `d` square-root-scale summatory terms has degree `3d/2-1`, whereas integrating the binary
formula `d-2` times produces degree `d`.

Primary sources:

- preprint: <https://arxiv.org/abs/2603.10241>;
- correct general Laplace-convolution identity cited there: Cantarini--Gambini--Zaccagnini,
  *Laplace convolutions of weighted averages of arithmetical functions*, Forum Math. 37 (2025),
  515--533, <https://arxiv.org/abs/2401.07531>.

This correction is mathematically exact but should be treated as an author-review candidate before
publication claims are made.

## No-go conclusion and survivor

- **Failed route:** use current ternary/multiple-Mobius estimates to prove a higher-even simplex
  source. Object and exponent both miss.
- **Positive survivor:** exact even-order one-sided criterion (1)--(4), with first nonlinear rung
  (5)--(6), plus correction (8) to the dropped-factor recursion.
- **RH status:** not proved. Unconditional estimate (3), at any even order, remains exactly the
  half-power cancellation wall.

## Lean targets

- `mobiusMertensFourthConvolution` (`W=U*U`);
- exact identity (5);
- one-sided `N^(5+o(1))` upper source implies every strict half-power decay and RH;
- Mertens all-strict-half-power source implies the quartic upper source;
- conditional iff interface using the existing Littlewood argument parameter.

## Formalization milestone -- 2026-07-22

Implemented in
`formal/GaloisForLFunctions/RHTower/MobiusMertensFourthConvolutionCriterion.lean`:

- `mobiusMertensFourthConvolution`;
- `mobiusDiscreteLaplaceTransform_pow_four_eq_one_sub_exp_pow_four_mul_tsum`, exact identity (5);
- `norm_pow_four_mobiusDiscreteLaplaceTransform_le_of_fourthConvolutionSubpowerUpperBound`;
- `mobiusMertensFourthConvolutionSubpowerUpperBound_implies_allStrictHalfPowerDecay`;
- `mobiusMertensFourthConvolutionSubpowerUpperBound_implies_riemannHypothesis`;
- `mobiusMertensAllStrictHalfPowerBound_implies_fourthConvolutionSubpowerUpperBound`;
- `mobiusMertensFourthConvolutionSubpowerUpperBound_iff_riemannHypothesis_of_mertens`.

Direct `lake env lean` verification and targeted final
`lake build GaloisForLFunctions.RHTower.MobiusMertensFourthConvolutionCriterion` both pass.
`#print axioms` on the exact identity and all endpoint implications reports only `propext`,
`Classical.choice`, and `Quot.sound`.

The paper theorem covers every fixed even `d`; Lean formalizes the first genuinely nonlinear rung
`d=4`, reusing the already checked quadratic source. The remaining general-`d` induction is
structural repetition and is not needed by any stronger connector: `d=4` already returns exactly
the same RH frontier.
