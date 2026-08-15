# Route U polar polyphase valuation two

- **ID:** `route-u-polar-polyphase-valuation-two`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Status:** `[LEAN-PROVED]` `[NOVELTY UNVERIFIED]`
- **Parent:** `route-u-kelvin-gamma-two-chart-renormalization-no-go`
- **Exact claim:** after the actual common source-matched filter, the polarized pole term of the
  explicit cofinal Route-U packet has hard-edge valuation two; its leading coefficient is one half
  of the squared pole Fourier sample, while its antipodal polyphase sample vanishes.

## Public sentence

The explicit-formula pole sees the direct polyphase channel but loses its antipodal half-alias;
after exact degree cancellation its cross capital is quadratic, not logarithmic, in hard-edge mass.

## Goal

Determine whether the literal pole term supplies the unit boundary charge required by the
Kelvin--Gamma two-chart no-go.  A positive answer would construct part of the missing chart-local
source correction.  A negative answer must close with the sharp surviving valuation law and
localize the missing charge to the von-Mangoldt cross source.

## Gates

- [x] 0 → 1 in-progress: literal source isolated, exact attack, Door passport below
- [x] 1 → 2 fully-proven: dependency-closed paper proof and hostile audit
- [x] 2 → 3 formalized: closed Lean theorem, scratch verification, leaf `.olean`, axiom audit
- [ ] 3 → 4 publication-ready: standalone theorem, literature audit, expert novelty audit

## Exact frontier

### Internal corpus

`[CORPUS]` `XiShiftedHardEdgePrimeGammaSourceDisintegration.lean` identifies the literal pole
summand of a shifted-reversal packet `Q` as

```text
2*pi*Q(-1/4)^2*exp(t/4).
```

`[CORPUS]` `XiShiftedHardEdgePrimeGammaAntipodalPolarization.lean` polarizes the completed source
at a common reciprocal degree.  `XiShiftedHardEdgePrimeGammaKelvinCrossCurrent.lean` proves exact
common-degree reversal and Kelvin covariance.  `XiShiftedHardEdgeFiniteHankelWitness.lean` realizes
the compact lattice packet as a finite Chebyshev polynomial.  The complex Paley--Wiener,
periodization, and Nyquist modules already prove phase convergence, uniform strip decay, and
alias-tail decay.

None states the pole-source valuation or identifies the antipodal pole evaluation as a half-alias
selector.

### External primary audit

- Weil, *Sur les « formules explicites » de la théorie des nombres premiers* (1972), gives the
  completed explicit-formula decomposition.
- Burnol, *The Explicit Formula and the conductor operator*, arXiv:math/9902080, interprets the
  local explicit formula through conductor/inversion operators.
- Connes--Consani, *The Scaling Hamiltonian*, arXiv:1910.14368, studies the scaling action behind
  the archimedean explicit formula.
- Connes et al., *Heat Expansion and Zeta*, arXiv:2402.13082, records the zeta pole heat summand as
  `2 exp(t/4)`.

No located source gives the cofinal source-matched Chebyshev/polyphase valuation below.  Classical
ingredients are not claimed new; source-specific synthesis and sharp classification remain
provisional pending expert audit.

## Conjecture loop

### U-POLAR-CHARGE-ONE

`[CONJECTURE]` The literal pole cross term carries the missing unit logarithmic boundary charge.

**Verdict:** `[FALSIFIED]`.  The source-matched Laplace integral and common reversal degree cancel
exactly.  The remaining denominator is only `a^2-1/4`, so the normalized pole cross capital has
valuation two, not logarithmic valuation one.

### U-POLAR-ANTIPODAL-SURVIVAL

`[CONJECTURE]` Both antipodal pole samples survive and their interference may hide a logarithm.

**Verdict:** `[FALSIFIED]`.  Evaluation at `-z_a` is exactly the lattice periodization shifted by
half an alias period.  Uniform Paley--Wiener decay kills this Nyquist sample, while evaluation at
`z_a` converges to the direct pole Fourier sample.

### U-POLAR-VALUATION-TWO

`[CANDIDATE]` Fix cutoff `n` and real Schwartz amplitude `g`.  Put

```text
a_k = k+1,
P_k = routeUExplicitFiniteChebyshevPacket n k g,
z_k = (a_k^2+1/4)/(a_k^2-1/4),
F_n = routeUComplexPositiveFourierExtension n (routeURealEvenAmplitude g) (i/2),
N_k = (P_k(z_k)^2-P_k(-z_k)^2)/(2*(a_k^2-1/4)).
```

Then

```text
P_k(z_k)  -> Re(F_n),
P_k(-z_k) -> 0,
a_k^2*N_k -> Re(F_n)^2/2,
N_k       -> 0.                                      (PV.1)
```

Moreover `pi*(2d_k)!*N_k` is exactly the pole summand of the actual common-filter completed-source
cross capital of the even/odd antipodal channels of `P_k`, where `d_k` is their common reciprocal
degree.

## Exact algebraic reduction

Let `E=(P+P∘(-id))/2`, `O=(P-P∘(-id))/2`, and let `Q_E,Q_O` be their shifted reversals padded to
common degree `d` at mass `a>1/2`.  Polarization of the two pole squares gives the pointwise cross
source

```text
2*pi*Q_E(-1/4)*Q_O(-1/4)*exp(t/4).                    (PV.2)
```

After multiplication by the actual source filter `t^(2d) exp(-a^2 t)`, the Gamma integral is

```text
2*pi*(2d)!*Q_E(-1/4)*Q_O(-1/4)
  /(a^2-1/4)^(2d+1).                                  (PV.3)
```

Common-degree shifted reversal gives, with
`z_a=(a^2+1/4)/(a^2-1/4)`,

```text
Q_E(-1/4)Q_O(-1/4)
 = (a^2-1/4)^(2d) E(z_a)O(z_a)
 = (a^2-1/4)^(2d) [P(z_a)^2-P(-z_a)^2]/4.            (PV.4)
```

Substitution in `(PV.3)` and division by the native common capital factor `pi*(2d)!` yields

```text
N_a(P) = [P(z_a)^2-P(-z_a)^2]/[2(a^2-1/4)].          (PV.5)
```

Every degree-dependent power cancels.  This identity is exact, not asymptotic.

## Paper-proof obligations for `(PV.1)`

Let `A_n` be the real-even compact approximation of `g`, `h_k=2/a_k`,
`L_k=2*pi/h_k=pi*a_k`, and `phi_k=routeUComplexHardEdgePhase k (i/2)`.

1. The Cayley character identity at `i/2` and the finite Chebyshev construction give

   ```text
   P_k(z_k) = Periodization(A_n,h_k,phi_k).            (PV.6)
   ```

2. Chebyshev parity `T_m(-z)=(-1)^m T_m(z)` and `h_k L_k=2*pi` give

   ```text
   P_k(-z_k) = Periodization(A_n,h_k,phi_k+L_k/2).     (PV.7)
   ```

3. `phi_k -> i/2`; its real part is zero and its imaginary part lies in the closed unit strip.
   Continuity of the entire Fourier extension plus the uniform alias-tail estimate proves from
   `(PV.6)` that `P_k(z_k)->F_n`.

4. The shifted phase in `(PV.7)` lies exactly on the Nyquist boundary:
   `Re(phi_k+L_k/2)=L_k/2 -> +infinity`, with bounded imaginary part.  Uniform Fourier decay and
   uniform alias-tail decay prove `P_k(-z_k)->0`.

5. `a_k^2/(a_k^2-1/4)->1`.  Square, subtract, and multiply the preceding limits in `(PV.5)` to
   obtain the valuation-two limit.  The unscaled limit follows either from `(PV.5)` or by dividing
   the finite valuation-two limit by `a_k^2->+infinity`.

The proof uses no Xi zero, RH assumption, numerical computation, or asymptotic degree estimate.
All five steps, including `(PV.6)` and `(PV.7)` at the literal pole point, are closed in Lean.

## Lean certificate

- Generic complex finite-Chebyshev sampling:
  `GaloisForLFunctions.RHTower.XiShiftedHardEdgeComplexFiniteChebyshevSample`.
- Exact source theorem:
  `GaloisForLFunctions.RHTower.XiShiftedHardEdgePrimeGammaPolarPolyphaseValuation`.
- Capstones:
  `tendsto_routeUPolarNormalizedCrossCapital_valuation_two`,
  `tendsto_routeUPolarNormalizedCrossCapital_zero`,
  `routeUHardEdgeFilteredPolarCrossCapital_eq`, and
  `routeUExplicitFilteredPolarCrossCapital_eq_normalized`.
- Verification: both exact leaf files pass `lake env lean`; both exact leaf `.olean`s were emitted
  directly; the two imports are wired into `GaloisForLFunctions.RHTower`; no umbrella build was run.
- `#print axioms` on all four capstones reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden-token audit is empty for both new modules.

## Hostile audit

- This does **not** prove RH, sign the full source capital, or control the von-Mangoldt term.
- The pole term cannot cancel the Kelvin--Gamma logarithmic boundary divergence after native
  source normalization: its normalized contribution is `O(a^-2)`.
- Vanishing can be faster when `F_n=0`; `(PV.1)` gives exact leading coefficient, not universal
  nonvanishing.
- The half-alias mechanism itself is a known sampling phenomenon.  The research delta is its exact
  identification inside the literal pole source together with source-matched degree cancellation.
- Novelty remains `[NOVELTY UNVERIFIED]`; Lean closure does not establish priority.

## No-go closure

- **Exact killing mechanism:** `(PV.3)`--`(PV.5)` force valuation two and eliminate any hidden
  degree/logarithmic reserve.
- **Strongest positive survivor:** exact valuation law `(PV.1)` with leading pole-sample coefficient.
- **New insight:** the pole is a polyphase selector, not chart-charge reservoir.
- **Remaining open core:** the von-Mangoldt cross source alone must supply any non-scalar unit
  boundary charge required to glue the Kelvin--Gamma charts.

## Universal-shadow map

| Corpus phenomenon | Higher organizing principle |
|---|---|
| shifted reversal has large degree powers | source-matched filtering is a valuation functor that removes gauge degree |
| pole evaluation occurs at `W=-1/4` | completed-formula pole is a fixed imaginary Fourier sample `i/2` |
| antipodal polynomial sends `z` to `-z` | antipody is half-alias translation in the physical lattice |
| direct sample survives, antipodal sample dies | completed pole selects one polyphase channel |
| Gamma needs logarithmic boundary charge | pole and Gamma live in different hard-edge valuations |
| scalar renormalization fails | remaining arithmetic correction must retain prime/orbit locality |

## Log

- 2026-08-15 — created in Stage 1 after exact filter/reversal calculation falsified pole charge one
  and exposed the valuation-two survivor.
- 2026-08-15 — dependency-closed paper proof and exact Lean theorem verified; promoted to Stage 3.
