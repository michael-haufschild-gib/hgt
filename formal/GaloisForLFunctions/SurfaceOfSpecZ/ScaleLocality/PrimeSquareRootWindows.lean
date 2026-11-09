import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.SquareRootWindowsDetectEveryDepth
import GaloisForLFunctions.SurfaceOfSpecZ.TheGapMethodIterates

/-!
# Prime windows of square-root logarithmic radius decide RH

The prime-gap bound `x^(2/3)` propagates a local prime lower bound to an
interior half-window. At zero width `a` the loss has exponent `a-1/3`.
Starting from width `1/2`, two applications of the continuous window
criterion reduce the width through `1/6` to zero.
-/

open Complex Filter Topology
open GaloisForLFunctions.SquareRootThreshold Zeta23
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Prime gaps transfer a local lower bound to interior half-windows at the improved width. -/
theorem prime_squareRoot_windows_transfer {Z : ZeroConfig} (hZ : TemperedConfig Z) {a α r K : ℝ}
    (ha : 0 ≤ a) (hα : 0 ≤ α) (haα : a - 1 / 3 ≤ α) (hr : 0 < r)
    (hwidth : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + a)
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
      |Real.log p - T| ≤ r * Real.sqrt T →
      -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) :
    ∃ M : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u : ℝ,
      |u - T| ≤ (r / 2) * Real.sqrt T →
      -(M * Real.exp (α * u)) ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re := by
  obtain ⟨G, U₀, hG, hU₀, hnear⟩ := exists_log_degree_near (θ := (2 : ℝ) / 3)
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
  refine ⟨|K| + 4 * L * G, fun U => ?_⟩
  let W : ℝ := max U (max (2 * V) (max (r ^ 2) ((2 / r) ^ 2)))
  obtain ⟨T, hTW, hbound⟩ := hprime W
  have hTU : U ≤ T := (le_max_left _ _).trans hTW
  have hT₂ : 2 * V ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hTW)
  have hTr : r ^ 2 ≤ T := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hTW))
  have hTspan : (2 / r) ^ 2 ≤ T := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hTW))
  have hT : 0 ≤ T := (sq_nonneg r).trans hTr
  have hrS : r ≤ Real.sqrt T := (Real.le_sqrt hr.le hT).mpr hTr
  have hsmall : r * Real.sqrt T ≤ T := by
    have hh := mul_le_mul_of_nonneg_right hrS (Real.sqrt_nonneg T)
    simpa only [← sq, Real.sq_sqrt hT] using hh
  have hspan : 1 ≤ r / 2 * Real.sqrt T := by
    have hh := (Real.le_sqrt (show 0 ≤ 2 / r by positivity) hT).mpr hTspan
    have hmul := (div_le_iff₀ hr).mp hh
    nlinarith only [hmul]
  refine ⟨T, hTU, fun u hu => ?_⟩
  have huV : V ≤ u := by
    have hlu := (abs_le.mp hu).1
    nlinarith only [hlu, hsmall, hT₂]
  have hu₀ : U₀ ≤ u := (le_max_left _ _).trans huV
  have hu₁ : U₁ ≤ u := (le_max_left U₁ 0).trans ((le_max_right U₀ _).trans huV)
  have hu0 : 0 ≤ u := hV.trans huV
  obtain ⟨p, hp, hpExp, hlog0, hlogu, hgap⟩ := hnear u hu₀
  have hgap₁ : u - Real.log p ≤ 1 := hgap.trans (hU₁ u hu₁)
  have hlogT : |Real.log p - T| ≤ r * Real.sqrt T := by
    have htri : |Real.log p - T| ≤ |u - T| + |u - Real.log p| := by
      calc |Real.log p - T| = |(u - T) - (u - Real.log p)| := by congr 1; ring
        _ ≤ _ := by simpa only [Real.norm_eq_abs] using norm_sub_le (u - T) (u - Real.log p)
    rw [abs_of_nonneg (sub_nonneg.mpr hlogu)] at htri
    nlinarith only [htri, hu, hgap₁, hspan]
  have hbase := hbound p hp hlogT
  have hlip := abs_two_re_lagStructure_sub_le_of_width hZ
    ha hwidth hlog0 hlogu
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

/-- Square-root prime windows detect impurity even when no greatest depth is attained. -/
theorem onLine_of_prime_squareRoot_windows {Z : ZeroConfig} (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {r K : ℝ} (hr : 0 < r)
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
      |Real.log p - T| ≤ r * Real.sqrt T →
      -K ≤ 2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  have hhalf : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 + (1 / 2 : ℝ) := by
    intro ρ hρ
    have hh := (Z.strip ρ hρ).2
    linarith only [hh]
  obtain ⟨M, hM⟩ := prime_squareRoot_windows_transfer hZ
    (a := (1 : ℝ) / 2) (α := 1 / 6)
    (by norm_num) (by norm_num) (by norm_num) hr hhalf hprime
  have hwidth := configuration_re_le_of_squareRoot_windows hZ hnoreal
    (by norm_num : (0 : ℝ) ≤ 1 / 6)
    (half_pos hr) hM
  obtain ⟨N, hN⟩ := prime_squareRoot_windows_transfer hZ
    (a := (1 : ℝ) / 6) (α := 0)
    (by norm_num) le_rfl (by norm_num) hr hwidth hprime
  have hzero := configuration_re_le_of_squareRoot_windows hZ hnoreal
    (α := 0) le_rfl (half_pos hr) hN
  intro ρ hρ
  have h₁ := hzero ρ hρ
  have h₂ := hzero (reflect ρ) (Z.reflect_mem ρ hρ)
  have he : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
  rw [he] at h₂
  linarith only [h₁, h₂]

/-- Every sufficiently late square-root window contains an arbitrarily negative prime sample. -/
theorem eventually_prime_squareRoot_window_negative {Z : ZeroConfig} (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0)
    (himpure : ∃ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2) {r : ℝ} (hr : 0 < r) (K : ℝ) :
    ∃ U : ℝ, ∀ T : ℝ, U ≤ T → ∃ p : ℕ, p.Prime ∧
      |Real.log p - T| ≤ r * Real.sqrt T ∧
      2 * (lagStructure Z (boxSpline 1 3) (Real.log p)).re < -K := by
  classical
  by_contra h
  push_neg at h
  have hpure := onLine_of_prime_squareRoot_windows hZ hnoreal hr h
  obtain ⟨ρ, hρ, hne⟩ := himpure
  exact hne (hpure ρ hρ)

/-- Bounded prime traces on arbitrarily late square-root windows force RH. -/
theorem riemannHypothesis_of_prime_squareRoot_windows {r K : ℝ} (hr : 0 < r)
    (hprime : ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ p : ℕ, p.Prime →
      |Real.log p - T| ≤ r * Real.sqrt T →
      -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_zetaZeroConfig_onLine]
  exact onLine_of_prime_squareRoot_windows temperedConfig_zetaZeroConfig
    (fun _ hρ hzero => not_mem_carrier_of_im_eq_zero hρ hzero) hr hprime

/-- Every positive square-root radius gives an RH criterion on arbitrary sparse prime windows. -/
theorem riemannHypothesis_iff_prime_squareRoot_windows (r : ℝ) (hr : 0 < r) :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧
      ∀ p : ℕ, p.Prime → |Real.log p - T| ≤ r * Real.sqrt T →
        -K ≤ 2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re := by
  constructor
  · intro hRH
    obtain ⟨K, hK⟩ := riemannHypothesis_iff_bddBelow_primeDegrees.mp hRH
    exact ⟨K, fun U => ⟨U, le_rfl, fun p hp _ => hK p hp⟩⟩
  · rintro ⟨K, hK⟩
    exact riemannHypothesis_of_prime_squareRoot_windows hr hK

#print axioms prime_squareRoot_windows_transfer
#print axioms onLine_of_prime_squareRoot_windows
#print axioms eventually_prime_squareRoot_window_negative
#print axioms riemannHypothesis_of_prime_squareRoot_windows
#print axioms riemannHypothesis_iff_prime_squareRoot_windows

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
