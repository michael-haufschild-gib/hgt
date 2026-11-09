import GaloisForLFunctions.SurfaceOfSpecZ.TheGapMethodIterates

/-!
# Prime-gap transfer inside growing observation windows

Once a logarithmic window radius lies between two and its center, the
nearest prime to every point of its interior half-window remains in the
full window. A trace of width `a` loses only exponent `a-1/3`.
-/

open Complex Filter Topology
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Prime lower bounds transfer to half-windows whose radii lie between two and their centers. -/
theorem prime_windows_transfer {Z : ZeroConfig} (hZ : TemperedConfig Z) {a α K : ℝ}
    (ha : 0 ≤ a) (hα : 0 ≤ α) (haα : a - 1 / 3 ≤ α)
    (R : ℝ → ℝ) (hR : ∀ᶠ T in atTop, 2 ≤ R T ∧ R T ≤ T)
    (hwidth : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
      |Real.log p - T| ≤ R T →
      -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) :
    ∃ M : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u : ℝ,
      |u - T| ≤ R T / 2 →
      -(M * Real.exp (α * u)) ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
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
  have hK : K ≤ |K| * Real.exp (α * u) :=
    (le_abs_self K).trans (by
      have hh := mul_le_mul_of_nonneg_left (Real.one_le_exp (mul_nonneg hα hu0)) (abs_nonneg K)
      simpa only [mul_one] using hh)
  have hlow := (abs_le.mp hvar).1
  nlinarith only [hbase, hK, hlow]

#print axioms prime_windows_transfer

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
