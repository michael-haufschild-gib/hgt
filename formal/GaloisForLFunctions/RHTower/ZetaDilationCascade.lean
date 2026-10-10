import GaloisForLFunctions.RHTower.SquarefreeDiscrepancyZeroCascade

/-!
# The dilation cascade `z ↦ 1 - z/k`

Receivers whose Dirichlet series carry `ζ(ks)` in the denominator (`k`-free counts, `k > 1`) turn a
power bound `O(x^α)` into a dilation law: every zero `ρ` with `kα < Re ρ < 1` must have
`ζ(ρ/k) = 0`. Together with the reflection `s ↦ 1 - s` this sends a zero `z` to the zero `1 - z/k`.
The orbit `z_j = k/(k+1) + (-1/k)^j (ρ - k/(k+1))` converges to the real point `k/(k+1)`, where
`ζ ≠ 0`.

**Theorem** (`riemannZeta_ne_zero_of_dilation`). Let `k > 1`, `α ≥ 0`, and suppose every zero `ρ`
with `kα < Re ρ < 1` has `ζ(ρ/k) = 0`. Then `ζ(s) ≠ 0` whenever `kα < Re s` and
`kα < 1 - Re s/k`. The orbit's real parts stay between `Re s` and `1 - Re s/k`.

Consequently the exponent law of such a receiver can certify zero-freeness at the frontier `Θ`
only while `Θ ≤ k/(k+1)`, the cascade fixed point. The case `k = 2` is
`SquarefreeDiscrepancy.riemannZeta_ne_zero_of_halving`.
-/

open Filter Topology Complex

namespace RHTower.DilationCascade

noncomputable section

/-- The orbit `z_j = k/(k+1) + (-1/k)^j (ρ - k/(k+1))` of `z ↦ 1 - z/k`. -/
def orbit (k : ℝ) (ρ : ℂ) (j : ℕ) : ℂ :=
  (k / (k + 1) : ℝ) + ((-1 / k : ℝ) : ℂ) ^ j * (ρ - (k / (k + 1) : ℝ))

theorem orbit_succ {k : ℝ} (hk : 0 < k) (ρ : ℂ) (j : ℕ) :
    orbit k ρ (j + 1) = 1 - orbit k ρ j / k := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast (by linarith : k + 1 ≠ 0)
  unfold orbit
  rw [pow_succ]
  have e1 : ((k / (k + 1) : ℝ) : ℂ) = (k : ℂ) / ((k : ℂ) + 1) := by push_cast; ring
  have e2 : ((-1 / k : ℝ) : ℂ) = -1 / (k : ℂ) := by push_cast; ring
  rw [e1, e2]
  generalize (-1 / (k : ℂ)) ^ j = w
  field_simp
  ring

theorem orbit_re (k : ℝ) (ρ : ℂ) (j : ℕ) :
    (orbit k ρ j).re = k / (k + 1) + (-1 / k) ^ j * (ρ.re - k / (k + 1)) := by
  unfold orbit
  rw [Complex.add_re, Complex.ofReal_re, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Complex.sub_re, Complex.ofReal_re]

/-- The real parts of the orbit lie between `Re ρ` and `1 - Re ρ/k`. -/
theorem orbit_re_bounds {k : ℝ} (hk : 1 < k) (ρ : ℂ) (j : ℕ) :
    min ρ.re (1 - ρ.re / k) ≤ (orbit k ρ j).re ∧
      (orbit k ρ j).re ≤ max ρ.re (1 - ρ.re / k) := by
  have hk0 : 0 < k := by linarith
  rw [orbit_re]
  set q : ℝ := (-1 / k) ^ j with hq
  have hbounds : -(1 / k) ≤ q ∧ q ≤ 1 := by
    rcases Nat.eq_zero_or_pos j with hj | hj
    · rw [hq, hj, pow_zero]
      constructor
      · have : 0 < 1 / k := by positivity
        linarith
      · exact le_rfl
    · have habs : |q| ≤ 1 / k := by
        rw [hq, abs_pow, show |(-1 / k : ℝ)| = 1 / k by
          rw [abs_div, abs_neg, abs_one, abs_of_pos hk0]]
        calc (1 / k) ^ j ≤ (1 / k) ^ 1 :=
              pow_le_pow_of_le_one (by positivity) (by rw [div_le_one hk0]; linarith) hj
          _ = 1 / k := pow_one _
      have h1k : 1 / k ≤ 1 := by rw [div_le_one hk0]; linarith
      constructor <;> linarith [abs_le.mp habs]
  obtain ⟨hlo, hhi⟩ := hbounds
  have e2 : k / (k + 1) + (-(1 / k)) * (ρ.re - k / (k + 1)) = 1 - ρ.re / k := by
    field_simp
    ring
  have hlin : ∀ q' : ℝ, k / (k + 1) + q' * (ρ.re - k / (k + 1)) =
      (1 - (q' + 1 / k) / (1 + 1 / k)) * (1 - ρ.re / k) +
        ((q' + 1 / k) / (1 + 1 / k)) * ρ.re := by
    intro q'
    field_simp
    ring
  have hw0 : 0 ≤ (q + 1 / k) / (1 + 1 / k) := by
    apply div_nonneg <;> [linarith; positivity]
  have hw1 : (q + 1 / k) / (1 + 1 / k) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  rw [hlin q]
  set w : ℝ := (q + 1 / k) / (1 + 1 / k)
  constructor
  · rcases le_total ρ.re (1 - ρ.re / k) with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  · rcases le_total ρ.re (1 - ρ.re / k) with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith

theorem tendsto_orbit {k : ℝ} (hk : 1 < k) (ρ : ℂ) :
    Tendsto (orbit k ρ) atTop (𝓝 ((k / (k + 1) : ℝ) : ℂ)) := by
  have hk0 : 0 < k := by linarith
  have hnorm : ‖((-1 / k : ℝ) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_one, abs_of_pos hk0,
      div_lt_one hk0]
    exact hk
  have hpow : Tendsto (fun j : ℕ => ((-1 / k : ℝ) : ℂ) ^ j) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
  have h := (hpow.mul_const (ρ - (k / (k + 1) : ℝ))).const_add ((k / (k + 1) : ℝ) : ℂ)
  rw [zero_mul, add_zero] at h
  exact h

/-- `ζ(σ) ≠ 0` for `0 < σ < 1`. -/
theorem riemannZeta_ofReal_ne_zero {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    riemannZeta (σ : ℂ) ≠ 0 := by
  obtain ⟨r, hr, hZ⟩ := exists_zetaResidueUnit_ofReal_eq_pos hσ0
  intro h
  have h1 : (σ : ℂ) ≠ 1 := by exact_mod_cast hσ1.ne
  rw [zetaResidueUnit, Function.update_of_ne h1, h, mul_zero] at hZ
  exact (by exact_mod_cast hr.ne' : (r : ℂ) ≠ 0) hZ.symm

/-- **Dilation cascade.** -/
theorem riemannZeta_ne_zero_of_dilation {k α : ℝ} (hk : 1 < k) (hα : 0 ≤ α)
    (hdil : ∀ ρ : ℂ, riemannZeta ρ = 0 → k * α < ρ.re → ρ.re < 1 → riemannZeta (ρ / k) = 0)
    {s : ℂ} (h1 : k * α < s.re) (h2 : k * α < 1 - s.re / k) :
    riemannZeta s ≠ 0 := by
  intro hz
  have hk0 : 0 < k := by linarith
  have hs1 : s.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  have hs0 : 0 < s.re := lt_of_le_of_lt (mul_nonneg hk0.le hα) h1
  have hmin : k * α < min s.re (1 - s.re / k) := lt_min h1 h2
  have hmax : max s.re (1 - s.re / k) < 1 :=
    max_lt hs1 (by have : 0 < s.re / k := by positivity
                   linarith)
  have hzeros : ∀ j : ℕ, riemannZeta (orbit k s j) = 0 := by
    intro j
    induction j with
    | zero => simpa [orbit] using hz
    | succ j ih =>
      obtain ⟨hlo, hhi⟩ := orbit_re_bounds hk s j
      have hre1 : k * α < (orbit k s j).re := lt_of_lt_of_le hmin hlo
      have hre2 : (orbit k s j).re < 1 := lt_of_le_of_lt hhi hmax
      have hdiv := hdil _ ih hre1 hre2
      have hdre : (orbit k s j / k).re = (orbit k s j).re / k := by
        rw [show (k : ℂ) = ((k : ℝ) : ℂ) from rfl, Complex.div_ofReal_re]
      have hre0 : 0 < (orbit k s j / k).re := by
        rw [hdre]
        exact div_pos (lt_of_le_of_lt (mul_nonneg hk0.le hα) hre1) hk0
      have hre1' : (orbit k s j / k).re < 1 := by
        rw [hdre, div_lt_one hk0]; linarith
      rw [orbit_succ hk0]
      exact (riemannZeta_one_sub_eq_zero_iff hre0 hre1').mpr hdiv
  have hfix0 : 0 < k / (k + 1) := by positivity
  have hfix1 : k / (k + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hcont : ContinuousAt riemannZeta ((k / (k + 1) : ℝ) : ℂ) :=
    (differentiableAt_riemannZeta (by exact_mod_cast hfix1.ne)).continuousAt
  have hlim := hcont.tendsto.comp (tendsto_orbit hk s)
  have h0 : Tendsto (fun j => riemannZeta (orbit k s j)) atTop (𝓝 0) := by
    simp only [hzeros]; exact tendsto_const_nhds
  exact riemannZeta_ofReal_ne_zero hfix0 hfix1 (tendsto_nhds_unique hlim h0)

/-- **The cascade reaches the frontier only below `k/(k+1)`.** For `kα < σ` the band condition
`kα < 1 - σ/k` at `σ = Θ`, with `α` just below `Θ/k`, holds exactly when `Θ < k/(k+1)`. -/
theorem band_contains_iff {k Θ : ℝ} (hk : 1 < k) :
    Θ < 1 - Θ / k ↔ Θ < k / (k + 1) := by
  have hk0 : 0 < k := by linarith
  have e : Θ + Θ / k = Θ * (k + 1) / k := by field_simp
  rw [lt_div_iff₀ (by linarith), lt_sub_iff_add_lt, e, div_lt_one hk0]

end

end RHTower.DilationCascade
