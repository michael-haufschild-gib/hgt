# Unit-Riesz outgoing charge as Suzuki Green curvature

- **ID:** `ccm-unit-riesz-suzuki-green-producer-classification`
- **Stage:** 3-formalized
- **Type:** CROSS-ROUTE EXACT SOURCE WELD / RH-EQUIVALENT PRODUCER CLASSIFICATION
- **Scientific status:** `[PAPER PROOF CLOSED] [LEAN FORMALIZED, UNCONDITIONAL]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [EXTERNAL PRIORITY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** `ccm-unit-riesz-coherent-outgoing-charge-hankel`,
  `ccm-unit-riesz-log-lattice-rh-criterion`, Suzuki explicit screw criterion,
  CCM Guinand--Weil Xi-screw Green connection

## Claim

Let `R_1(t)` be the unit-rate causal resolvent of the critical normalized Chebyshev error. Then

```text
RH
iff exists B, for every t>=0, |R_1(t)|<=B
iff exists B_0, for every integer N>=2, |R_1(log N)|<=B_0.
```

Equivalently, RH holds exactly when the total HG energy of literal completed outgoing blocks is
uniformly bounded over integer apertures. Subsequent sharp classification now also proves under RH
`|R_1(log N)|<4`, so uniform pole-packet domination is itself RH-equivalent; see formalized sharp
card and `CCMUnitRieszSharpPoleClassification.lean`.

## Exact Green decomposition

Fix any base `0<b<log 2` and put

```text
F_H(h)=exp(-(H-h)/2)-exp(-(H-h)),
F_H(H)=0,
F_H'(H)=-1/2,
F_H''(h)=1/4 exp(-(H-h)/2)-exp(-(H-h)).
```

At `H=log N`, each prime atom satisfies

```text
(Lambda(k)/sqrt(k)) F_H(log k)
 = (Lambda(k)/sqrt(N)) (1-exp(-(log N-log k)/2)).
```

Thus the prime part of the unit-Riesz outgoing charge is the literal completed CCM source tested
by `F_H`, after restoring its polar and Gamma pieces. The existing Xi-screw Green law gives

```text
q_N = G_H(Psi) + P_H - A_H,

G_H(Psi)
 = F_H'(H) C_b(H) - integral_b^H C_b(h) F_H''(h) dh,

C_b(h)=Psi(h)-Psi(b)-(h-b) Psi'_+(b),

P_H=integral_b^H F_H(h) 2 cosh(h/2) dh-exp(H/2)/3,
A_H=integral_b^H F_H(h) a_Gamma(h) dh.
```

Here `Psi` is Suzuki's literal multiplicity-exact Xi screw and `a_Gamma` is the published CCM
archimedean density.

## Uniform-bound proof

Assume RH. Suzuki's theorem, already formalized in corpus, supplies `|Psi(h)|<=C` on the positive
ray. Expanding the affine codiagonal and integrating its constant and linear pieces exactly gives

```text
G_H(Psi)
 = F_H'(H) Psi(H)
   - integral_b^H Psi(h) F_H''(h) dh
   - Psi(b) F_H'(b)
   + Psi'_+(b) F_H(b).
```

The reporter has uniform bounds

```text
|F_H'(H)|=1/2,
integral_b^H |F_H''(h)| dh <= 3/2,
|F_H'(b)|<=3/2,
|F_H(b)|<=2.
```

Hence `G_H(Psi)` is uniformly bounded. Polar contribution has exact cancellation

```text
integral_b^H F_H(h) 2 cosh(h/2) dh
 = exp(H/2)/3
   +(H-b-2-exp(b))exp(-H/2)
   +((2/3)exp(3b/2)+2exp(b/2))exp(-H),
```

so `P_H` is bounded. Finally

```text
a_Gamma(h)=exp(-h/2)/(1-exp(-2h)),
0<=F_H(h)<=exp(-(H-h)/2)
```

on `[b,H]`. Since denominator is bounded below by `1-exp(-2b)>0`,

```text
|A_H| <= (H-b)exp(-H/2)/(1-exp(-2b)),
```

which is uniformly bounded. Therefore `q_N`, and hence `R_1(log N)=2q_N`, is uniformly bounded.
Integer-log interpolation yields a global bound. The reverse implication is the already-closed
bounded-resolvent analytic endpoint.

## Novelty and theatre audit

Suzuki boundedness criterion and Green integration by parts are individually known/formalized.
New content is exact identification of the literal unit-Riesz CCM outgoing charge with Suzuki
Green curvature at the forced two-exponential reporter, followed by cancellation strong enough to
prove the reverse implication absent from the current CCM corpus. This fuses CCM-HG/UR/FU with the
multiplicity-exact Suzuki divisor source and turns a one-way criterion into an equivalence.

This is not an RH proof: RH is used for forward boundedness, and boundedness implies RH in reverse.
It does prove that generic attempts to derive any uniform outgoing bound are not auxiliary
estimates; they are full RH producers. Remaining genuinely sharper question is whether literal
CCM restricted-Weil/ground geometry forces the canonical numerical pole constant `4`, or instead
forces boundedness with a source-determined noncanonical constant.

## Gates

- [x] exact reporter and atom matching
- [x] Xi-screw Green decomposition
- [x] affine-codiagonal cancellation
- [x] uniform screw-functional bound under RH
- [x] exact polar cancellation
- [x] uniform Gamma remainder bound
- [x] paper proof of RH-equivalent boundedness
- [x] unconditional Lean formalization
- [x] exact leaf build and umbrella wiring
- [ ] independent mathematical audit
- [ ] external priority audit

## Log

- 2026-08-16 -- Identified forced reporter `exp(-u/2)-exp(-u)` as Green kernel for outgoing charge.
- 2026-08-16 -- Derived exact Suzuki codiagonal decomposition and cancellation of affine base data.
- 2026-08-16 -- Proved RH implies uniform outgoing bound; combined with analytic endpoint to obtain equivalence.

## Index of the formalization

Module: `RHTower/CCMUnitRieszSuzukiGreenProducerClassification.lean` (namespace `RHTower`).
All declarations are unconditional; `#print axioms` returns only
`propext, Classical.choice, Quot.sound`.

| Card item | Lean declaration |
|---|---|
| forced reporter `F_H` and its jets | `unitRieszSuzukiReporter`, `unitRieszSuzukiReporter_H`, `unitRieszSuzukiReporterDeriv_H`, `hasDerivAt_unitRieszSuzukiReporter`, `hasDerivAt_unitRieszSuzukiReporterDeriv` |
| prime-atom matching | `unitRieszSuzuki_prime_term`, `unitRieszSuzuki_prime_sum` |
| completed source at integer aperture | `unitRieszSuzuki_completedSource_log_nat` |
| Xi-screw Green decomposition | `unitRieszSuzukiGreen`, `unitRieszSuzuki_completedSource_eq_green`, `unitRieszSuzukiGreen_eq_raw` |
| affine-codiagonal cancellation | `integral_unitRieszSuzukiReporterSecond`, `integral_sub_base_mul_unitRieszSuzukiReporterSecond` |
| uniform screw-functional bound | `abs_integral_suzukiPsi_mul_unitRieszSuzukiReporterSecond_le`, `abs_unitRieszSuzukiGreen_le_of_suzuki_bound` |
| exact polar cancellation | `unitRieszSuzukiPolarCorrection_eq`, `abs_unitRieszSuzukiPolarCorrection_le` |
| uniform Gamma remainder bound | `ccmPublishedArchimedeanDensity_le_unitRieszSuzukiBase`, `abs_unitRieszSuzukiArchCorrection_le` |
| outgoing charge as Green curvature | `unitRieszSuzuki_outgoing_eq_green` |
| RH implies the uniform bound | `exists_log_nat_bound_criticalMellinChebyshevResolventSource_of_riemannHypothesis` |
| the RH equivalences | `riemannHypothesis_iff_unitRieszCriticalResolventLogNatBounded`, `riemannHypothesis_iff_unitRieszCriticalResolventBounded`, `riemannHypothesis_iff_unitRieszCompletedOutgoingEnergyBounded` |
