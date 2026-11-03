import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheEnergyOfAFrequencyTwist

/-!
# Every frequency acts as a Frobenius angle

Over a pure curve the Frobenius angle `u` enters the rescaled limit of the family through the
Hurwitz form `ζ(β+1, u) + ζ(β+1, 1 − u)` (`tendsto_rpow_mul_curveBulk`), and over `ℤ` a cosine
twist of rational frequency `a/M` has the second-order term `½(ζ(β+1, u) + ζ(β+1, 1 − u))`
(`cosTwist_layer_criticalCurve`). Here the frequency is arbitrary:

* **The second-order term of a frequency** (`freqTwist_layer_criticalCurve`): for every real `α`
  with `2α ∉ ℤ` and `u = {α}`, along `c^{β+1}/log N → K` the window `h(log(n/N)) cos(2πnα)/√n` has

  `c⁻¹⟨Wx, x⟩/∫g² → (βA_φ/(K∫φ²)) · ½(ζ(β+1, u) + ζ(β+1, 1 − u)) ∫ e^{−(β+1)y} H²`.

The proof replaces periodicity by its two consequences: bounded partial sums (geometric sums) for
the pole terms and the twisted Riemann sums, and Kuzmin–Landau with a rotation for the quiet region
(`exists_freqLow_energy_le`); the energy law equidistributes the oscillation `cos(2π(2n + δ)α)` by
summation by parts (`freqEnergy_le`). The coefficient is a continuous function of `u ∈ (0, 1)`, the
same for rational and irrational frequencies, and it is the Hurwitz form that a Frobenius angle `u`
carries over `𝔽_q`: the second-order term of the degeneration does not distinguish a twist frequency
over `ℤ` from an angle of Frobenius over a curve.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-- `sin 2πα ≠ 0` forces `sin πα ≠ 0`. -/
theorem sin_pi_ne_zero_of_two {α : ℝ} (hα2 : Real.sin (Real.pi * (2 * α)) ≠ 0) :
    Real.sin (Real.pi * α) ≠ 0 := by
  intro h0
  apply hα2
  rw [show Real.pi * (2 * α) = 2 * (Real.pi * α) by ring, Real.sin_two_mul, h0]
  ring

/-- A frequency off `½ℤ` has a fractional part in `(0, 1)`. -/
theorem fract_pos_of_sin {α : ℝ} (hα : Real.sin (Real.pi * α) ≠ 0) : 0 < Int.fract α := by
  rcases (Int.fract_nonneg α).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hα
    have e := Int.floor_add_fract α
    rw [← h, add_zero] at e
    rw [← e, mul_comm]
    exact Real.sin_int_mul_pi _

/-- **The second-order term of a frequency.** For `2α ∉ ℤ`, `u = {α}`: along `c^{β+1}/log N → K`,
`c⁻¹⟨Wx, x⟩/∫g² → (βA_φ/(K∫φ²)) · ½(ζ(β+1, u) + ζ(β+1, 1 − u)) ∫ e^{−(β+1)y} H²` for the window
twisted by `cos(2πnα)`. -/
theorem freqTwist_layer_criticalCurve (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ q : ℝ} (hq : 4 < q)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-q))
    {β Aφ : ℝ} (hβ : 0 < β)
    (hT : Tendsto (fun x => x ^ β * ArithmeticDegenerationTheory.spectralTail φ x) atTop (𝓝 Aφ))
    (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K))
    {α : ℝ} (hα2 : Real.sin (Real.pi * (2 * α)) ≠ 0) :
    Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (twistedWeights h (freqTwist α) N)
        (atomDilate φ (c N / N))) / ∫ u, atomDilate φ (c N / N) u ^ 2)) atTop
      (𝓝 (β * Aφ / (K * ∫ u, φ u ^ 2) *
        ((hurwitzSum (β + 1) (Int.fract α) + hurwitzSum (β + 1) (1 - Int.fract α)) / 2) *
        ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2)) := by
  obtain ⟨hcinf, hclog, -⟩ := criticalCurve_facts_rpow hc1 (q := β + 1) (by linarith) hK hcrit
  have hsin := sin_pi_ne_zero_of_two hα2
  have hu0 := fract_pos_of_sin hsin
  have hu1 := Int.fract_lt_one α
  set u := Int.fract α with hu
  have hm0 : 0 < min u (1 - u) := lt_min hu0 (by linarith)
  have hm1 : min u (1 - u) ≤ 1 := (min_le_left _ _).trans hu1.le
  have hAA' : A ≤ A - Real.log (min u (1 - u)) := by
    have := Real.log_nonpos hm0.le hm1
    linarith
  have hsharp := twisted_layer_sharp_of_energy_of_bounded hφ hφsupp hφ2 hq hCφ hdecay hh hA hsupp
    hc1 hcinf hclog (abs_freqTwist_le α) (abs_sum_range_freqTwist_le hsin) hAA'
    (freqAlias φ h α) (abs_freqEnergy_sub_le hφ hφsupp hh hA hsupp hα2)
    (exists_freqLow_energy_le (by linarith : 0 ≤ q) hCφ hdecay hh hA hsupp hu0)
  set I := ∫ y, Real.exp (-(β * y)) * h y ^ 2 with hI
  set M₀ := ∫ u, φ u ^ 2 with hM₀
  have hlim : ∀ v, 0 < v → v ≤ 1 → Tendsto (fun N : ℕ =>
      Real.log N * densityAlias (twistDensity φ v) h (c N) N) atTop
      (𝓝 (K⁻¹ * (Aφ * hurwitzSum (β + 1) v * (β * I)))) := fun v hv0 hv1 =>
    tendsto_log_mul_twistDensityAlias hφ hφsupp hq hCφ hdecay hβ hT hh hA hsupp hc1 hK hcrit hv0 hv1
  have hterm : Tendsto (fun N : ℕ => Real.log N / M₀ * freqAlias φ h α (c N) N) atTop
      (𝓝 (M₀⁻¹ * ((K⁻¹ * (Aφ * hurwitzSum (β + 1) u * (β * I)) +
        K⁻¹ * (Aφ * hurwitzSum (β + 1) (1 - u) * (β * I))) / 2))) := by
    have := (((hlim u hu0 hu1.le).add (hlim (1 - u) (by linarith) (by linarith))).div_const
      2).const_mul M₀⁻¹
    refine this.congr fun N => ?_
    unfold freqAlias
    rw [← hu]
    ring
  have := hsharp.add hterm
  rw [zero_add] at this
  have hH : ∫ y, Real.exp (-((β + 1) * y)) * halfWeight h y ^ 2 = I := by
    rw [hI]; congr 1; funext y
    rw [halfWeight, mul_pow, ← Real.exp_nat_mul,
      show Real.exp (-((β + 1) * y)) * (Real.exp ((2 : ℕ) * (y / 2)) * h y ^ 2) =
        (Real.exp (-((β + 1) * y)) * Real.exp ((2 : ℕ) * (y / 2))) * h y ^ 2 by ring,
      ← Real.exp_add]
    congr 2; push_cast; ring
  rw [hH]
  have hval : M₀⁻¹ * ((K⁻¹ * (Aφ * hurwitzSum (β + 1) u * (β * I)) +
      K⁻¹ * (Aφ * hurwitzSum (β + 1) (1 - u) * (β * I))) / 2) =
      β * Aφ / (K * M₀) * ((hurwitzSum (β + 1) u + hurwitzSum (β + 1) (1 - u)) / 2) * I := by
    field_simp
  rw [hval] at this
  refine this.congr fun N => ?_
  ring

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
