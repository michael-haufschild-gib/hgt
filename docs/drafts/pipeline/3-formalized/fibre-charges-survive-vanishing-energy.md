# Fibre charges survive vanishing energy

- **ID:** F0311-Q3-4.5a-test
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-0311/fable.md` §4.5(a), first classification test; loop card `1-in-progress/fable-0311-q3-breakthrough-questions.md`
- **Statement:** For every conductor `m ≥ 1`, charge `t` and `ε > 0` there is `Q ≥ R` such that for
  every horizon `N ≥ mQ` a harmonic-pole-neutral input supported on `{1} ∪ {m p : p ≤ Q prime, p ∤ m}`
  has adjunction mass, residual mean square `M((G − t e_m)²)`, physical input and physical residual
  output all `< ε`, while the `e_m`-component of its output `M(G·e_m)` is exactly `t`.

## Answer to the test

Yes. Inputs on `m p` retain the nonconstant output `e_m` with every energy vanishing, at every fixed
conductor, uniformly over horizons `N ≥ mQ`. Every mode's receiving charge hides in vanishing-energy
inputs; energy and physical-input norms do not detect charges in any conductor.

## Paper proof

1. **Fibre transport.** With `b` on the fibre primes, the packet of `Σ_p b_p δ_{mp}` is
   `Σ b_p e_{mp} = e_m P_b` (`e_{mp} = e_m e_p` for `p ∤ m`), and the derivation law
   `G e_{mp} = e_p G e_m + e_m G e_p` gives `G = e_m G(b) + S_m P_b`, `S_m = G e_m`.
2. **Coherent coefficients.** `b_p = (t/B_m) √φ(p)/p`, `B_m = Σ_{p ≤ Q, p∤m} log p/p`. The prime
   decomposition `G(b) = Σ b_p log p/√φ(p) − X`, `X = Σ τ(p) b_p e_p`, has response exactly `t`.
   Hence `G − t e_m = −e_m X + S_m P_b`.
3. **Sizes.** `w_p² = (p−1)/p² ≤ 2 log p/p`, so `Σ b_p² ≤ 2t²/B_m`; `τ(p) ≤ 1`, so
   `Σ τ(p)² b_p² ≤ Σ b_p²`. Adjunction weights add over `m·p`, and `(log p + τ(p)) w_p² = log p/p`,
   so the adjunction mass is `(log m + τ(m)) Σ b_p² + t²/B_m ≤ (2(log m + τ(m)) + 1) t²/B_m`.
4. **Bounds.** `e_m`, `S_m` are `m`-periodic, bounded by `C_m`, `C'_m`. Pointwise
   `(G − t e_m)² ≤ 2C_m² X² + 2C'_m² P_b²`. Complete means of packet squares are coefficient masses;
   harmonic sums obey `(Σ_{n≤N} F²/n)/log N ≤ 52·mass` for `Q ≤ N`. Harmonic pole centering adds only
   the constant conductor, which the generator and the adjunction weight ignore, and contracts the
   physical input. Every energy is `≤ K_m t²/B_m`, `K_m = 2(log m + τ(m)) + 1 + 208(C_m² + C'_m²)`.
5. **Exact retention.** `G·e_m = t e_m² − e_m² X + (S_m e_m) P_b`. `M(e_m²) = 1`. `X`, `P_b` have
   period `L = Π_{fibre} p`, prime to `m`, and zero sum over a period (prime-supported packets have
   zero complete mean). `mL ∣ (mQ)!`, and the period sum of a product of an `m`-periodic and an
   `L`-periodic function factors (CRT). So the last two means vanish: `M(G e_m) = t`.
6. **Choice of `Q`.** `B_m(Q) ≥ B(Q) − Σ_{p∣m} log p/p → ∞`; take `B_m(Q) ≥ K_m t²/ε + 1`.

## Lean

`formal/GaloisForLFunctions/CriticalScaleArithmeticRigidity/FibreChargesSurviveVanishingEnergy.lean`:
`fibrePrimes`, `fibreRestrict`, `fibreCoefficients`, `sum_fibreCoefficients`,
`normalizedConductorPacket_fibre`, `arithmeticPrimeGenerator_fibre`,
`packetMean_mul_eq_zero_of_coprime`, `fibreScale`, `fibreCharge`, `fibreScale_tendsto_atTop`,
`primePoleResponse_fibreCharge`, `primeAdjunctionMass_fibreCharge`, `fibre_residual`,
`packetMean_fibre_retains`, `fibreCharge_bounds`, **`exists_fibre_charge_vanishing_energy`**.

Checked with `lake --old env lean`; transitive axioms of `exists_fibre_charge_vanishing_energy`,
`packetMean_fibre_retains`, `arithmeticPrimeGenerator_fibre`, `primeAdjunctionMass_fibreCharge`:
`propext`, `Classical.choice`, `Quot.sound`. Wired into `CriticalScaleArithmeticRigidity.lean`.

## Consequence for §4.5(a)

The classification test answers *yes* for every conductor: the conductor-Gram receiver cannot be
reached by energy or physical-norm limits at any fixed mode; only exact signed identities of the
complete form (the raw dilation energy, which on the scalar family is `t²(1/θ − ½)` at `Q = N^θ`;
see the Q6 card) can see the charge.

## Log
- 2026-11-04 — paper proof and Lean formalization completed
