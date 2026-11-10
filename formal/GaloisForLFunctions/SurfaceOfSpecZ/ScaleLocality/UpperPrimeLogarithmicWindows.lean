import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.UpperLogarithmicWindows
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PrimeLogarithmicWindows

/-!
# Upper prime traces on logarithmic windows

Prime gaps transfer an upper prime bound to continuous observations.
The upper logarithmic receiver lowers the width by one third unless
already bounded by the observed exponent. Applying it at the abscissa
removes this loss and gives the exact width criterion, including RH.
-/

open Complex Filter Topology
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- An upper prime power bound transfers whenever the target exponent dominates both costs. -/
theorem upper_prime_power_windows_transfer {Z : ZeroConfig} (hZ : TemperedConfig Z) {a α σ K : ℝ}
    (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hσα : σ ≤ α) (haα : a - 1 / 3 ≤ α)
    (R : ℝ → ℝ) (hR : ∀ᶠ T in atTop, 2 ≤ R T ∧ R T ≤ T)
    (hwidth : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
      |Real.log p - T| ≤ R T →
      2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re ≤ K * (p : ℝ) ^ σ) :
    ∃ M : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u : ℝ,
      |u - T| ≤ R T / 2 →
      2 * (lagStructure Z (boxSpline 1 3) u).re ≤ M * Real.exp (α * u) := by
  obtain ⟨G, U₀, hG, _, hnear⟩ := exists_log_degree_near (θ := (2 : ℝ) / 3)
    (by norm_num) (powGaps_primes (by norm_num) (by norm_num))
  let L : ℝ := ∑' z : ℂ, ‖lagCoeff Z (boxSpline 1 3) z‖ * ‖z‖
  have hL : 0 ≤ L := tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hgaplim : Tendsto (fun u : ℝ => 2 * G * Real.exp (((2 : ℝ) / 3 - 1) * u)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (2 : ℝ) / 3 - 1 < 0))
    simpa only [Function.comp_def, id_eq, mul_zero] using he.const_mul (2 * G)
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.mp
    (hgaplim.eventually_le_const (by norm_num : (0 : ℝ) < 1))
  let V : ℝ := max U₀ (max U₁ 0)
  have hV : 0 ≤ V := (le_max_right U₁ 0).trans (le_max_right U₀ _)
  have hlate : ∀ᶠ T in atTop, 2 * V ≤ T ∧ 2 ≤ R T ∧ R T ≤ T := by
    filter_upwards [eventually_ge_atTop (2 * V), hR] with T hT hshape
    exact ⟨hT, hshape⟩
  obtain ⟨W, hW⟩ := eventually_atTop.mp hlate
  refine ⟨|K| + 4 * L * G, fun U => ?_⟩
  obtain ⟨T, hTmax, hbound⟩ := hprime (max U W)
  have hTU : U ≤ T := (le_max_left _ _).trans hTmax
  obtain ⟨hT₂, hR₂, hRT⟩ := hW T ((le_max_right _ _).trans hTmax)
  refine ⟨T, hTU, fun u hu => ?_⟩
  have huV : V ≤ u := by
    have hlu := (abs_le.mp hu).1
    linarith only [hlu, hRT, hT₂]
  have hu₀ : U₀ ≤ u := (le_max_left _ _).trans huV
  have hu₁ : U₁ ≤ u := (le_max_left U₁ 0).trans ((le_max_right U₀ _).trans huV)
  have hu0 : 0 ≤ u := hV.trans huV
  obtain ⟨p, hp, _, hlog0, hlogu, hgap⟩ := hnear u hu₀
  have hgap₁ : u - Real.log p ≤ 1 := hgap.trans (hU₁ u hu₁)
  have hlogT : |Real.log p - T| ≤ R T := by
    have htri : |Real.log p - T| ≤ |u - T| + |u - Real.log p| := by
      calc |Real.log p - T| = |(u - T) - (u - Real.log p)| := by congr 1; ring
        _ ≤ _ := by simpa only [Real.norm_eq_abs] using norm_sub_le (u - T) (u - Real.log p)
    rw [abs_of_nonneg (sub_nonneg.mpr hlogu)] at htri
    linarith only [htri, hu, hgap₁, hR₂]
  have hbase := hbound p hp hlogT
  have hlip := abs_two_re_lagStructure_sub_le_of_width hZ ha hwidth hlog0 hlogu
  have hvar : |2 * (lagStructure Z (boxSpline 1 3) u).re -
      2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re| ≤
      4 * L * G * Real.exp (α * u) := by
    have h₁ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * L by positivity)) (Real.exp_pos (a * u)).le
    have he : Real.exp (((2 : ℝ) / 3 - 1) * u) * Real.exp (a * u) =
        Real.exp ((a - 1 / 3) * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h₂ : 2 * L * (2 * G * Real.exp (((2 : ℝ) / 3 - 1) * u)) * Real.exp (a * u) =
        4 * L * G * Real.exp ((a - 1 / 3) * u) := by
      calc _ = 4 * L * G *
          (Real.exp (((2 : ℝ) / 3 - 1) * u) * Real.exp (a * u)) := by ring
        _ = _ := by rw [he]
    have h₃ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right haα hu0))
      (show 0 ≤ 4 * L * G by positivity)
    exact hlip.trans (h₁.trans (h₂.le.trans h₃))
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpower : (p : ℝ) ^ σ ≤ Real.exp (α * u) := by
    rw [Real.rpow_def_of_pos hp0]
    apply Real.exp_le_exp.mpr
    calc Real.log p * σ = σ * Real.log p := mul_comm _ _
      _ ≤ σ * u := mul_le_mul_of_nonneg_left hlogu hσ
      _ ≤ α * u := mul_le_mul_of_nonneg_right hσα hu0
  have hK : K * (p : ℝ) ^ σ ≤ |K| * Real.exp (α * u) :=
    (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hp0.le _)).trans
      (mul_le_mul_of_nonneg_left hpower (abs_nonneg K))
  have hhigh := (abs_le.mp hvar).2
  nlinarith only [hbase, hK, hhigh]

/-- The upper observation criterion measures the exact zero width. -/
theorem zeta_re_le_iff_upper_prime_logarithmic_power_windows {σ : ℝ} (hσ : 0 ≤ σ) :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ) ↔
      ∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
        |Real.log p - T| ≤ primeLogarithmicRadius T →
          2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re ≤
            K * (p : ℝ) ^ σ := by
  constructor
  · intro hwidth
    obtain ⟨K, hK⟩ := (zeta_re_le_iff_abs_prime_logarithmic_power_windows hσ).mp hwidth
    refine ⟨K, fun U => ?_⟩
    obtain ⟨T, hT, hbound⟩ := hK U
    exact ⟨T, hT, fun p hp hwin => (le_abs_self _).trans (hbound p hp hwin)⟩
  · rintro ⟨K, hprime⟩
    let a : ℝ := _root_.RHTower.zetaZeroAbscissa - 1 / 2
    have ha : 0 ≤ a := sub_nonneg.mpr _root_.RHTower.half_le_zetaZeroAbscissa
    have hwidth : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + a :=
      (zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le ha).mp (by dsimp [a]; linarith only)
    obtain ⟨M, hM⟩ := upper_prime_power_windows_transfer temperedConfig_zetaZeroConfig
      ha hσ (le_max_left σ (a - 1 / 3)) (le_max_right σ (a - 1 / 3))
      primeLogarithmicRadius primeLogarithmicRadius_shape hwidth hprime
    have hstep : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + max σ (a - 1 / 3) := by
      apply zeta_re_le_of_upper_logarithmic_windows (hσ.trans (le_max_left _ _))
      intro U
      obtain ⟨T, hT, hbound⟩ := hM U
      refine ⟨T, hT, fun u hu => hbound u ?_⟩
      change |u - T| ≤ (32 * Real.log (T + 2)) / 2
      linarith only [hu]
    have hnew := (zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le
      (hσ.trans (le_max_left σ (a - 1 / 3)))).mpr hstep
    have haσ : a ≤ σ := by
      by_contra h
      have hless : max σ (a - 1 / 3) < a :=
        max_lt (lt_of_not_ge h) (by linarith only)
      dsimp [a] at hnew hless
      linarith only [hnew, hless]
    intro ρ hρ
    exact (hwidth ρ hρ).trans (by linarith only [haσ])

/-- RH is an upper bound on the primes of arbitrarily late logarithmic windows. -/
theorem riemannHypothesis_iff_upper_prime_logarithmic_windows :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
      ∀ p : ℕ, p.Prime → |Real.log p - T| ≤ primeLogarithmicRadius T →
        2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re ≤ K := by
  constructor
  · intro hRH
    obtain ⟨K, hK⟩ := riemannHypothesis_iff_abs_prime_logarithmic_windows.mp hRH
    refine ⟨K, fun U => ?_⟩
    obtain ⟨T, hT, hbound⟩ := hK U
    exact ⟨T, hT, fun p hp hwin => (le_abs_self _).trans (hbound p hp hwin)⟩
  · intro h
    have hw := (zeta_re_le_iff_upper_prime_logarithmic_power_windows
      (σ := 0) le_rfl).mpr (by simpa only [Real.rpow_zero, mul_one] using h)
    apply riemannHypothesis_of_forall_re_le
    simpa only [add_zero] using hw

#print axioms upper_prime_power_windows_transfer
#print axioms zeta_re_le_iff_upper_prime_logarithmic_power_windows
#print axioms riemannHypothesis_iff_upper_prime_logarithmic_windows
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

