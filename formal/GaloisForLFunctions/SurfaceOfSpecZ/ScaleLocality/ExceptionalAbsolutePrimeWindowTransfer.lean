import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.FinitePrimeAvoidance
import GaloisForLFunctions.SurfaceOfSpecZ.TheGapMethodIterates

/-! Absolute prime observations transfer to the interior of a window even
when a power-saving number of primes is omitted. The proof uses only the
Lipschitz bound for the trace and uniform prime avoidance. -/

open Complex Filter Topology
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
set_option autoImplicit false
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Absolute transfer with a separately chosen exceptional set in each window. -/
theorem abs_prime_power_windows_transfer_off_finset {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {a α σ δ γ β K C : ℝ} (ha : 0 ≤ a) (hσ : 0 ≤ σ) (hσα : σ ≤ α)
    (haα : a + β - 1 ≤ α) (hγ : 0 ≤ γ) (hγβ : γ < β)
    (hβ : 7 / 12 < β) (hβ1 : β < 1) (hC : 0 ≤ C)
    (R : ℝ → ℝ)
    (hR : ∀ᶠ T in atTop, 2 ≤ R T ∧ R T ≤ T ∧ δ * T ≤ γ * (T - R T / 2))
    (hwidth : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ (T : ℝ) (E : Finset ℕ), U ≤ T ∧
      (E.card : ℝ) ≤ C * Real.exp (δ * T) ∧
      ∀ p : ℕ, p.Prime → p ∉ E → |Real.log p - T| ≤ R T →
        |2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re| ≤ K * (p : ℝ) ^ σ) :
    ∃ M : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u : ℝ,
      |u - T| ≤ R T / 2 →
      |2 * (lagStructure Z (boxSpline 1 3) u).re| ≤ M * Real.exp (α * u) := by
  obtain ⟨U₀, _, hnear⟩ := exists_log_prime_avoiding_small_finset hγ hγβ hβ hβ1 hC
  let L : ℝ := ∑' z : ℂ, ‖lagCoeff Z (boxSpline 1 3) z‖ * ‖z‖
  have hL : 0 ≤ L := tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hgaplim : Tendsto (fun u : ℝ => 2 * Real.exp ((β - 1) * u)) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (show β - 1 < 0 by linarith only [hβ1]))
    simpa only [Function.comp_def, id_eq, mul_zero] using he.const_mul 2
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.mp (hgaplim.eventually_le_const zero_lt_one)
  let V : ℝ := max U₀ (max U₁ 0)
  have hV : 0 ≤ V := (le_max_right U₁ 0).trans (le_max_right U₀ _)
  obtain ⟨W, hW⟩ := eventually_atTop.mp ((eventually_ge_atTop (2 * V)).and hR)
  refine ⟨|K| + 4 * L, fun U => ?_⟩
  obtain ⟨T, E, hTmax, hcard, hbound⟩ := hprime (max U W)
  have hTU : U ≤ T := (le_max_left _ _).trans hTmax
  obtain ⟨hT₂, hR₂, hRT, hmargin⟩ := hW T ((le_max_right _ _).trans hTmax)
  refine ⟨T, hTU, fun u hu => ?_⟩
  have huV : V ≤ u := by
    have hlu := (abs_le.mp hu).1
    linarith only [hlu, hRT, hT₂]
  have hu₀ : U₀ ≤ u := (le_max_left _ _).trans huV
  have hu₁ : U₁ ≤ u := (le_max_left U₁ 0).trans ((le_max_right U₀ _).trans huV)
  have hu0 : 0 ≤ u := hV.trans huV
  have hcardu : (E.card : ℝ) ≤ C * Real.exp (γ * u) := by
    apply hcard.trans
    apply mul_le_mul_of_nonneg_left _ hC
    apply Real.exp_le_exp.mpr
    exact hmargin.trans (mul_le_mul_of_nonneg_left
      (by linarith only [(abs_le.mp hu).1]) hγ)
  obtain ⟨p, hp, hpE, hlog0, hlogu, hgap⟩ := hnear u hu₀ E hcardu
  have hgap₁ : u - Real.log p ≤ 1 := hgap.trans (hU₁ u hu₁)
  have hlogT : |Real.log p - T| ≤ R T := by
    have htri : |Real.log p - T| ≤ |u - T| + |u - Real.log p| := by
      calc _ = |(u - T) - (u - Real.log p)| := by congr 1; ring
        _ ≤ _ := by simpa only [Real.norm_eq_abs] using norm_sub_le (u - T) (u - Real.log p)
    rw [abs_of_nonneg (sub_nonneg.mpr hlogu)] at htri
    linarith only [htri, hu, hgap₁, hR₂]
  have hbase := hbound p hp hpE hlogT
  have hlip := abs_two_re_lagStructure_sub_le_of_width hZ ha hwidth hlog0 hlogu
  have hvar : |2 * (lagStructure Z (boxSpline 1 3) u).re -
      2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re| ≤
      4 * L * Real.exp (α * u) := by
    have h₁ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgap (show 0 ≤ 2 * L by positivity)) (Real.exp_pos (a * u)).le
    have h₂ : 2 * L * (2 * Real.exp ((β - 1) * u)) * Real.exp (a * u) =
        4 * L * Real.exp ((a + β - 1) * u) := by
      rw [show (a + β - 1) * u = (β - 1) * u + a * u by ring, Real.exp_add]
      ring
    have h₃ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right haα hu0))
      (show 0 ≤ 4 * L by positivity)
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
  calc
    |2 * (lagStructure Z (boxSpline 1 3) u).re| ≤
        |2 * (lagStructure Z (boxSpline 1 3) u).re -
          2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re| +
        |2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re| := by
      have he : 2 * (lagStructure Z (boxSpline 1 3) u).re =
          (2 * (lagStructure Z (boxSpline 1 3) u).re -
            2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) +
          2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re := by ring
      conv_lhs => rw [he]
      exact abs_add_le _ _
    _ ≤ 4 * L * Real.exp (α * u) + |K| * Real.exp (α * u) :=
      add_le_add hvar (hbase.trans hK)
    _ = _ := by ring

#print axioms abs_prime_power_windows_transfer_off_finset
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
