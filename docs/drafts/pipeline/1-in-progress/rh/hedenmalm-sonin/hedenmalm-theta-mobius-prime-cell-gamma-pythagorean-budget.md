# Hedenmalm--theta Möbius prime-cell Euler--Gamma Pythagorean budget

- **ID:** P-G49
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) + LEAN FORMALIZATION IN PROGRESS
- **Source:** P-G48 co-Poisson complement; corpus Gamma-Jordan characteristic identity
- **Statement:** Running prime charge splits exactly into squared Julia Cayley defect and fourth-power Gamma cyclic complement; together with primitive co-Poisson current this gives an exact three-channel Ward identity.

## Goal

Identify P-G48's positive trace-class complement with actual corpus structure rather than name a
new remainder.  Separate coefficient identity from physical source-clock provenance.

## Gates

- [x] 0 → 1 in-progress: exact Pythagorean budget and three-channel Ward identity
- [ ] 1 → 2 fully-proven: finalize after Lean source check
- [ ] 2 → 3 formalized: module, umbrella, build, lint, axiom audit green
- [ ] 3 → 4 publication-ready: standalone exposition and external novelty audit

## P-G49 exact budget `[PROVED HERE]`

Let `a=qe^{-k}` be P-G47 running odds and define Julia Cayley coordinate

\[
 C(a,T)=\frac{T-1}{T+a}.
\tag{1}
\]

For `a>0`, `T>1`, one has `0<C<1`.  The P-G47/P-G48 formulas become

\[
 W=aC^2,
 \qquad
 H=a(1-C^2).
\tag{2}
\]

Corpus Gamma cyclic characteristic is

\[
 \varphi_\infty(u)=\cosh(u)^{-1/2},
\tag{3}
\]

and satisfies

\[
 \varphi_\infty(u)^4+\tanh(u)^2=1.
\tag{4}
\]

The unique real rapidity with `tanh u=C` is `u=artanh C`, so

\[
 \boxed{
 H=a\varphi_\infty(\operatorname{artanh}C)^4,
 \qquad
 a=W+a\varphi_\infty(\operatorname{artanh}C)^4.
 }
\tag{P-G49}
\]

Combining P-G48's literal `\mathcal C_p(1+x\epsilon)=-a_p` gives exact local Ward identity

\[
 \boxed{
 \mathcal C_p(1+x\epsilon)+W_p+
 a_p\varphi_\infty(\operatorname{artanh}C_p)^4=0.
 }
\tag{5}
\]

## Big-picture reinterpretation

P-G41--P-G49 are shadows of one conservative three-channel scattering law:

1. primitive Gamma/co-Poisson source injects signed charge `-a`;
2. Julia channel carries reflected/projective defect `aC^2`;
3. Gamma cyclic channel carries complementary charge `a(1-C^2)`;
4. thermal cascade transfers charge from Gamma channel into Julia channel;
5. wall freezing is complete transfer `C→1`; interior cold vacuum is simultaneous running-charge
   escape `a→0`.

This explains why earlier attempts repeatedly found positivity but not annihilation: they isolated
one positive leg of a conservative budget.

## No-theatre audit

Equation `(5)` is exact, nontrivial, coefficient-faithful, and uses two pre-existing source
objects.  However physical provenance is not closed.  We evaluate `\varphi_\infty` at the
Julia-forced nonlinear clock

\[
 u_p=\operatorname{artanh}\frac{T_p-1}{T_p+a_p}.
\tag{6}
\]

Corpus Gamma source usually arrives with clocks linear in `log p`.  P-G49 does not prove that the
actual completed Euler--Gamma source carries `(6)`.  Treating the value identity as source
construction would be theatre.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  HedenmalmThetaMobiusPoleUnitPrimeCellGammaPythagoreanBudget.lean
```

Key declarations:

- `thermalBernoulliCoPoissonCayley_mem_Ioo_zero_one`;
- `thermalBernoulliBoundaryLayerDefectOdds_eq_runningOdds_mul_cayley_sq`;
- `thermalBernoulliCoPoissonComplement_eq_runningOdds_mul_one_sub_cayley_sq`;
- `semilocalArchimedeanCharacteristic_artanh_cayley_pow_four`;
- `thermalBernoulliCoPoissonComplement_eq_gammaCharacteristic`;
- `thermalBernoulliEulerGammaPythagoreanBudget`;
- `eulerGammaCoPoissonPrimitiveTerm_add_julia_add_gamma_eq_zero`.

## Next hard gate

Compare forced clock `(6)` with literal Gamma/co-Poisson/Mellin source clocks.  Either construct a
source transform producing `(6)` before divisor evaluation, or prove a clock-mismatch no-go and
retain `(P-G49)` as exact receiver classification.

## Log

- 2026-08-12 — identified P-G48 complement as fourth-power Gamma characteristic at forced Julia
  rapidity; proved exact Euler--Gamma Pythagorean budget and literal three-channel Ward identity;
  physical clock provenance left explicit.
