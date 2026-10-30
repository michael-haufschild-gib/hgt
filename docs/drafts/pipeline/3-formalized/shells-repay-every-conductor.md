# The successor shells repay every conductor

- **ID:** shells-repay-every-conductor
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** AGT README §9 ("repayment of the nonpolar `−log c` losses by successor shells");
  RAPT `OverlapForcesNewRamanujanTerms` (every nonpolar reference energy becomes negative);
  Q1 of `docs/reports/review-2910/obstacles-summary.md`.
- **Statement:** For a `C²` profile on `[0,1]` with `M = ∫φ² > 0`, every `m ≥ 1` and `c > 0`, the
  completed conductor energy `E_m(c) = φ(m)⁻¹ Σ_{d∣m} μ(m/d) d E(c/d)` satisfies
  `E_m(c) = E_m^ref(c) − (2/(Mφ(m))) Σ_{1≤h<c} c_m(h) ∫_{h/c}^1 G(u)/u du`
  `= (2/(Mφ(m))) Σ_{a≥1,(a,m)=1} (m/a) ∫_{ac/m}^∞ |φ̂(2πt)|² dt ≥ 0`, and `E_m(c) → 0`.
  `E_m^ref(c) = completeWeilAdjunctionEnergy φ c m` is the reference energy; for `c ≤ 1` the
  two coincide.

## Paper proof

`E` is the completed conductor-one energy of
`completed-shell-energy-positive-fourier-integral.md`, with
`E(c) = (2/M) Σ_{k≥1} k⁻¹ T(kc)`, `T(a) = ∫_a^∞ |φ̂(2πt)|² dt`.

**Shell form.** Write `E(c/d) = log(1/(2πc)) + log d + β/M + (c/d) q − 2S(c/d)/M`. Then
`Σ_{d∣m} μ(m/d) d = φ(m)`, `Σ_{d∣m} μ(m/d) d log d = φ(m)(log m + τ(m))`,
`Σ_{d∣m} μ(m/d) = 1_{m=1}`. For the shells, `S(c/d) = Σ_{1≤h'<c/d} ∫_{h'd/c}^1 G/u`, and
`h' ↦ h = h'd` is a bijection onto `{1 ≤ h < c : d ∣ h}`. Hence
`Σ_d μ(m/d) d S(c/d) = Σ_{1≤h<c} (Σ_{d∣(m,h)} μ(m/d) d) ∫_{h/c}^1 G/u = Σ_h c_m(h) ∫_{h/c}^1 G/u`.

**Repayment.** Insert the series for `E(c/d)` and put `e = m/d`. The injective map
`k ↦ (k+1)e − 1` carries the `k`-th term `μ(e) d (k+1)⁻¹ T((k+1)c/d)` to the index `a = (k+1)e`,
where it reads `μ(e)(m/a) T(ac/m)`. Summing over `d`, the coefficient of `(m/a) T(ac/m)` is
`Σ_{e∣m, e∣a} μ(e) = Σ_{e∣(m,a)} μ(e) = 1_{(m,a)=1}`. All terms are nonnegative.

**Marginality** follows from `E(c/d) → 0` for each of the finitely many `d`.

## Meaning

Past touching, the nonpolar reference energies `E_m^ref(c) = E_m^ref(1) − log c` become negative.
The successor shells, weighted by the Ramanujan sums `c_m(h)` that the affine prime windows produce,
repay this loss exactly: after Möbius inversion the signs collapse to the coprimality indicator and
every completed conductor energy is a positive Fourier integral at every overlap. Identification of
`E_m(c)`, `c > 1`, with the actual Ramanujan-mode energies of the complete Weil matrix is a separate
theorem.

## Lean

`formal/GaloisForLFunctions/RenormalizedArithmeticPotentialTheory/TheShellsRepayEveryConductor.lean`,
namespace `GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.CompletedShell`:
`completedConductorEnergy_eq_reference_sub_shells`, `hasSum_completedConductorEnergy`,
`completedConductorEnergy_nonneg`, `tendsto_completedConductorEnergy_atTop`,
`completedConductorEnergy_eq_adjunction`; helpers `sum_shellSum_div`,
`sum_divisors_moebius_filter_dvd`. Checked with `lake --old env lean`; transitive axioms
`propext`, `Classical.choice`, `Quot.sound`; wired into `RenormalizedArithmeticPotentialTheory.lean`.

## Log
- 2026-10-30 — proved and formalized.
