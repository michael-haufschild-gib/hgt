import Mathlib

/-!
# The universal archimedean logarithmic mass of the leading endpoint layer

Three exact mechanisms of the card are formalized.

*The sawtooth logarithmic mass.*  The sawtooth `S(θ) = ∑_{k≥1} sin(kθ)/k` has Fourier coefficients
of modulus `1/(2k)`, so counting both signs of the frequency its total energy is
`2 ∑_{k≥1} 1/(4k²) = π²/12` — equation `(11)`.

*The uniform logarithmic rescaling.*  A multiplier with `M(ξ) = log|ξ| + O(1)` satisfies
`M(Lη)/log L → 1` for every fixed `η > 0` — equation `(9)`, the step that converts the semiclassical
measure into a logarithmic scale.

*The endpoint constant.*  The sawtooth mass `π²/12`, the constrained response constant `16/(11π)`
and the doubling `log L_λ ∼ 2 log λ` multiply to exactly `8π/33` — equations `(12)`–`(15)`; a prime
response one logarithmic order lower contributes nothing to that limit — equation `(17)`.

The digamma multiplier `(1)`, its expansion `(2)`, the semiclassical measure `(8)` and the
logarithmic energy estimate `(10)` are cited parents and stay outside the Lean statement.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## The sawtooth logarithmic mass -/

/-- The squared modulus `|p_k|² = 1/(4k²)` of the `k`-th sawtooth Fourier coefficient. -/
def sawtoothCoeffSq (k : ℕ) : ℝ := 1 / (4 * (k : ℝ) ^ (2 : ℕ))

/-- **Equation (11).**  Counting both signs of the frequency, the sawtooth energy is `π²/12`. -/
theorem hasSum_sawtoothEnergy :
    HasSum (fun k : ℕ => 2 * sawtoothCoeffSq k) (Real.pi ^ (2 : ℕ) / 12) := by
  have heq : (fun k : ℕ => 2 * sawtoothCoeffSq k)
      = fun k : ℕ => (1 / 2 : ℝ) * (1 / (k : ℝ) ^ (2 : ℕ)) := by
    funext k
    unfold sawtoothCoeffSq
    ring
  have hval : (1 / 2 : ℝ) * (Real.pi ^ (2 : ℕ) / 6) = Real.pi ^ (2 : ℕ) / 12 := by ring
  rw [heq, ← hval]
  exact hasSum_zeta_two.mul_left (1 / 2 : ℝ)

/-- **Equation (11), summed form.** -/
theorem tsum_sawtoothEnergy :
    ∑' k : ℕ, 2 * sawtoothCoeffSq k = Real.pi ^ (2 : ℕ) / 12 :=
  hasSum_sawtoothEnergy.tsum_eq

/-! ## The uniform logarithmic rescaling -/

/-- **Equation (9).**  A multiplier equal to `log|ξ|` up to a bounded error rescales to the constant
`1`: on the support of the semiclassical measure the frequency is bounded away from zero, so the
whole logarithmic weight comes from the chirp scale. -/
theorem tendsto_logMultiplier_ratio {M : ℝ → ℝ} {C R : ℝ}
    (hM : ∀ ξ : ℝ, R ≤ abs ξ → abs (M ξ - Real.log (abs ξ)) ≤ C) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun L : ℝ => M (L * η) / Real.log L) atTop (nhds 1) := by
  have hlogtop : Tendsto (fun L : ℝ => Real.log L) atTop atTop := Real.tendsto_log_atTop
  have hbound : Tendsto (fun L : ℝ => (C + abs (Real.log η)) / Real.log L) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hlogtop
  have hmain : Tendsto (fun L : ℝ => M (L * η) / Real.log L - 1) atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop (R / η), eventually_gt_atTop (1 : ℝ)] with L hL1 hL2
    have hLpos : 0 < L := lt_trans zero_lt_one hL2
    have hLη : 0 < L * η := by positivity
    have hR : R ≤ abs (L * η) := by
      rw [abs_of_pos hLη]
      calc R = R / η * η := by field_simp
        _ ≤ L * η := mul_le_mul_of_nonneg_right hL1 (le_of_lt hη)
    have hlogpos : 0 < Real.log L := Real.log_pos hL2
    have hsplit : Real.log (abs (L * η)) = Real.log L + Real.log η := by
      rw [abs_of_pos hLη, Real.log_mul (ne_of_gt hLpos) (ne_of_gt hη)]
    have hdiff : M (L * η) / Real.log L - 1
        = (M (L * η) - Real.log (abs (L * η)) + Real.log η) / Real.log L := by
      rw [hsplit]
      field_simp
      ring
    have habs : abs (M (L * η) - Real.log (abs (L * η)) + Real.log η)
        ≤ abs (M (L * η) - Real.log (abs (L * η))) + abs (Real.log η) := by
      simpa [Real.norm_eq_abs] using
        norm_add_le (M (L * η) - Real.log (abs (L * η))) (Real.log η)
    have hnum : abs (M (L * η) - Real.log (abs (L * η)) + Real.log η)
        ≤ C + abs (Real.log η) :=
      le_trans habs (by have h := hM (L * η) hR; linarith)
    rw [hdiff, Real.norm_eq_abs, abs_div, abs_of_pos hlogpos, div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hnum (le_of_lt (inv_pos.mpr hlogpos))
  have h := hmain.add_const 1
  simpa using h

/-! ## The endpoint constant -/

/-- The exact endpoint constant of `(15)`: the sawtooth mass, the constrained response constant and
the doubling of the chirp scale multiply to `8π/33`. -/
theorem endpoint_constant_eq :
    (16 / (11 * Real.pi)) * (Real.pi ^ (2 : ℕ) / 12) * 2 = 8 * Real.pi / 33 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  norm_num

/-- The algebraic factorization behind `(15)`. -/
theorem endpoint_scale_factorization {aSq d1 A logL logl : ℝ}
    (hd : d1 ≠ 0) (hL : logL ≠ 0) (hl : logl ≠ 0) :
    (aSq * A) / (d1 * logl) = (aSq / d1) * (A / logL) * (logL / logl) := by
  field_simp

/-- **Equations (12)–(15).**  The archimedean endpoint scale is exactly `8π/33`. -/
theorem tendsto_endpoint_archimedean_scale {A d1 aSq logL : ℝ → ℝ}
    (hA : Tendsto (fun l => A l / logL l) atTop (nhds (Real.pi ^ (2 : ℕ) / 12)))
    (ha : Tendsto (fun l => aSq l / d1 l) atTop (nhds (16 / (11 * Real.pi))))
    (hLl : Tendsto (fun l => logL l / Real.log l) atTop (nhds 2))
    (hdne : ∀ᶠ l in atTop, d1 l ≠ 0) (hLne : ∀ᶠ l in atTop, logL l ≠ 0) :
    Tendsto (fun l => (aSq l * A l) / (d1 l * Real.log l)) atTop
      (nhds (8 * Real.pi / 33)) := by
  have hprod : Tendsto (fun l => (aSq l / d1 l) * (A l / logL l) * (logL l / Real.log l))
      atTop (nhds ((16 / (11 * Real.pi)) * (Real.pi ^ (2 : ℕ) / 12) * 2)) :=
    (ha.mul hA).mul hLl
  rw [endpoint_constant_eq] at hprod
  refine hprod.congr' ?_
  have hlne : ∀ᶠ l : ℝ in atTop, Real.log l ≠ 0 := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with l hl
    exact ne_of_gt (Real.log_pos hl)
  filter_upwards [hdne, hLne, hlne] with l hd hL hl
  exact (endpoint_scale_factorization hd hL hl).symm

/-- **Equation (17).**  A response one logarithmic order lower does not disturb the leading
archimedean scale. -/
theorem tendsto_lowerOrder_response {Qp d1 : ℝ → ℝ} {c : ℝ}
    (hQ : Tendsto (fun l => Qp l / d1 l) atTop (nhds c)) :
    Tendsto (fun l => (Qp l / d1 l) / Real.log l) atTop (nhds 0) :=
  Tendsto.div_atTop hQ Real.tendsto_log_atTop

end GaloisForLFunctions.RHTower

end
