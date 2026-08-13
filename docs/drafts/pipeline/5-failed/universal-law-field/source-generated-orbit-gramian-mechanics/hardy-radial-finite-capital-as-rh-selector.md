# Hardy radial finite capital as an RH selector

- **ID:** ULF-SGOGM-FAIL-2
- **Stage:** 5 — failed/retired
- **Type:** CIRCULAR SELECTION CLAIM
- **Claim:** Prove RH by postulating that every zero's radial multiplier packet has finite
  Euler-shell orbit capital.
- **Verdict:** `[RH-EQUIVALENT PREMISE] [CIRCULAR AS SELECTOR] [RETIRED]`
- **Positive survivor:**
  `../../../2-fully-proven/universal-law-field/source-generated-orbit-gramian-mechanics/spectral-hardy-trace-formation-admission-and-radial-capital-wall-law.md`

## 1. Exact killing theorem

Fix `m>=1` and `sigma>3`. For `rho` in the critical strip put

\[
 a_\rho=\Re\rho-\frac12,
 \qquad
 x_\rho(n)
 ={n^{-\sigma/2}\over\sqrt{S_m(\sigma)}}(n^{2a_\rho}-1).
 \tag{HF.1}
\]

The Stage-2 Hardy-admission theorem proves unconditionally

\[
 q_{G_{m,\sigma}}(x_\rho)<\infty
 \iff \Re\rho=\frac12.
 \tag{HF.2}
\]

Therefore the global statement

\[
 \forall\rho,quad
 \Xi(\rho)=0\Longrightarrow q_{G_{m,\sigma}}(x_\rho)<\infty
 \tag{HF.3}
\]

is equivalent to RH for nontrivial zeros. RH implies `(HF.3)` because `x_rho=0` on the line;
`(HF.3)` implies RH by `(HF.2)`.

## 2. Why this is not a source theorem yet

Calling `(HF.3)` “source admission,” “finite work,” or “physical realizability” does not weaken its
logical content. Unless a pre-zero operation constructs an explicit `L^2` source-time history for
`x_rho` without using `Xi(rho)=0` as its load-bearing step, the claim merely renames the desired
conclusion.

Functional-equation transport and common recovery cannot help: the split-recovery theorem proves
that both preserve least capital exactly.

## 3. Positive survivor

The failure leaves three unconditional laws.

1. Source reachability is exactly Hardy trace interpolation on the spectral set.
2. Euler-shell exact-time packets have infinite capital, whereas width-`T` averages have exact
   capital `1/T`.
3. The radial multiplier has finite capital exactly on the neutral line.

These are useful diagnostics and prohibit false source-admission arguments. They do not themselves
advance RH selection.

## 4. Required noncircular successor

A valid successor must be parameter-free and formed before divisor specialization. For example, it
could construct a global source operator `B` with finite intrinsic work and prove an identity

\[
 WB=\mathfrak D
 \tag{HF.4}
\]

for a source defect `D` defined independently of a chosen zero. Only afterward may evaluation at
`rho` identify a radial component of `D`. If the factorization is introduced separately for each
zero, it is circular by `(HF.2)`.

## 5. Status

- [x] circularity proved by exact iff;
- [x] recovery/functional-equation escapes ruled out;
- [x] positive analytic survivor retained;
- [ ] parameter-free global source factorization;
- [ ] selection consequence.

No Lean was written or built during this research pass.
