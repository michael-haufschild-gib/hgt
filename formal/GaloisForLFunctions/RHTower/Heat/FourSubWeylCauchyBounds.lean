import GaloisForLFunctions.RHTower.Heat.FourSubWeylSliceProfiles

/-! # Cauchy bounds from the four sub-Weyl slice profiles

The Cauchy radius `N/(log t+2E)` controls all four slopes simultaneously.
Euler growth supplies the portion of the circle outside the inner strip.
-/

noncomputable section
open Complex MeasureTheory Filter Topology Metric
open scoped ComplexOrder
open GaloisForLFunctions.HTGeometry

namespace RHTower

private theorem subWeyl_profile_shift {u E r c δ x z : ℝ} (β : ℝ)
    (hu : 0 ≤ u) (hE : 0 ≤ E) (hr : 0 ≤ r) (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hδ : 0 ≤ δ) (hz : |z| ≤ |x| + r) :
    u * -(β + c * (1 / 2 + δ - |z|)) ≤
      (u + 2 * E) * r - β * u - c * u * (1 / 2 - |x|) := by
  have hdisp : |z| - |x| - δ ≤ r := by linarith only [hz, hδ]
  have h1 := mul_le_mul_of_nonneg_left hdisp (mul_nonneg hc hu)
  have h2 := mul_le_mul_of_nonneg_right hc1 (mul_nonneg hu hr)
  have h3 := mul_nonneg hE hr
  nlinarith only [h1, h2, h3]

/-- Every low-order derivative satisfies the four actual sub-Weyl profiles. -/
theorem exists_norm_iteratedDeriv_xiSliceProduct_le_inner_four_subWeyl_profiles {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1 / 20) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 80 ≤ t → ∀ x : ℝ, |x| < 1 / 2 → ∀ N : ℕ, 1 ≤ N →
      (N : ℝ) ≤ Real.log t →
      ‖iteratedDeriv N (xiSliceProduct t) (x : ℂ)‖ / N.factorial ≤
        C * xiSliceReal t (1 / 2 + 2 * η)
          * ((Real.exp (N - 31 / 200 * Real.log t - 3 / 100 * Real.log t * (1 / 2 - |x|))
            + Real.exp (N - Real.log t / 13 - 3 / 13 * Real.log t * (1 / 2 - |x|))
            + Real.exp (N - Real.log t / 53 - 23 / 53 * Real.log t * (1 / 2 - |x|))
            + Real.exp (N - η * Real.log t - subWeylGain η * Real.log t * (1 / 2 - |x|)))
          * ((Real.log t + 2 * xiEulerConstant η) / N) ^ N) := by
  obtain ⟨C₁, hC₁, hS₁⟩ := exists_norm_xiSliceProduct_le_four_subWeyl_profiles (R₁ := 2) hη hη1
    (by norm_num)
  obtain ⟨C₂, hC₂, hS₂⟩ := exists_norm_xiSliceProduct_le_strip (R₁ := 2) hη (by linarith only [hη1])
    (by norm_num)
  have hc0 := subWeylGain_nonneg hη hη1
  have hc1 := subWeylGain_le_one hη
  refine ⟨C₁ + C₂, add_pos hC₁ hC₂, fun t ht x hx N hN1 hNu => ?_⟩
  have ht0 : 0 < t := by linarith only [ht]
  obtain ⟨u, hudef⟩ : ∃ u, u = Real.log t := ⟨_, rfl⟩
  obtain ⟨E, hEdef⟩ : ∃ E, E = xiEulerConstant η := ⟨_, rfl⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = subWeylGain η := ⟨_, rfl⟩
  rw [← hudef] at hNu ⊢
  rw [← hEdef, ← hcdef]
  rw [← hcdef] at hc0 hc1
  have hE0 : 0 < E := hEdef ▸ xiEulerConstant_pos hη
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hu0 : 0 < u := hN0.trans_le hNu
  have hu2E : 0 < u + 2 * E := by linarith only [hu0, hE0]
  obtain ⟨S₀, hS₀⟩ : ∃ S₀, S₀ = xiSliceReal t (1 / 2 + 2 * η) := ⟨_, rfl⟩
  have hS₀0 : 0 ≤ S₀ := hS₀ ▸ xiSliceReal_nonneg t _
  obtain ⟨r, hrdef⟩ : ∃ r, r = N / (u + 2 * E) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; positivity
  have hr1 : r ≤ 1 := by rw [hrdef, div_le_one hu2E]; linarith only [hNu, hE0]
  have hrN : (u + 2 * E) * r = N := by rw [hrdef]; field_simp
  have hxa : 0 < 1 / 2 - |x| := sub_pos.mpr hx
  obtain ⟨A₁, hA₁⟩ : ∃ A₁, A₁ = (u + 2 * E) * r - 31 / 200 * u - 3 / 100 * u * (1 / 2 - |x|) := ⟨_, rfl⟩
  obtain ⟨A₂, hA₂⟩ : ∃ A₂, A₂ = (u + 2 * E) * r - u / 13 - 3 / 13 * u * (1 / 2 - |x|) := ⟨_, rfl⟩
  obtain ⟨A₃, hA₃⟩ : ∃ A₃, A₃ = (u + 2 * E) * r - u / 53 - 23 / 53 * u * (1 / 2 - |x|) := ⟨_, rfl⟩
  obtain ⟨A₄, hA₄⟩ : ∃ A₄, A₄ = (u + 2 * E) * r - η * u - c * u * (1 / 2 - |x|) := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = (C₁ + C₂) * S₀ * (Real.exp A₁ + Real.exp A₂ + Real.exp A₃ + Real.exp A₄) :=
    ⟨_, rfl⟩
  have hMb : ∀ z ∈ sphere (x : ℂ) r, ‖xiSliceProduct t z‖ ≤ M := by
    intro z hz
    have hzr : ‖z - x‖ = r := mem_sphere_iff_norm.mp hz
    have hza : |z.re - x| ≤ r := by
      have := Complex.abs_re_le_norm (z - x)
      rw [Complex.sub_re, Complex.ofReal_re] at this
      linarith only [this, hzr]
    have hzc : |z.im| ≤ r := by
      have := Complex.abs_im_le_norm (z - x)
      rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at this
      linarith only [this, hzr]
    have hz' : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm
    have habs : |z.re| ≤ |x| + r := by
      have := abs_add_le (z.re - x) x
      rw [sub_add_cancel] at this
      linarith only [this, hza]
    have hE1 : 0 ≤ Real.exp A₁ := (Real.exp_pos _).le
    have hE2 : 0 ≤ Real.exp A₂ := (Real.exp_pos _).le
    have hE3 : 0 ≤ Real.exp A₃ := (Real.exp_pos _).le
    have hE4 : 0 ≤ Real.exp A₄ := (Real.exp_pos _).le
    rw [hz']
    by_cases ha : |z.re| < 1 / 2 + η
    · have h := hS₁ t z.re z.im (by linarith only [ht]) (by linarith only [hzc, hr1]) ha
      rw [← hS₀, ← hcdef] at h
      refine h.trans ?_
      rw [Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos ht0, Real.rpow_def_of_pos ht0,
        Real.rpow_def_of_pos ht0, ← hudef, hM]
      have hexp1 : u * -(31 / 200 + 3 / 100 * (1 / 2 - |z.re|)) ≤ A₁ := by
        rw [hA₁]
        simpa only [add_zero] using subWeyl_profile_shift (β := 31 / 200) (c := 3 / 100)
          (δ := 0) hu0.le hE0.le hr0.le (by norm_num) (by norm_num) (by norm_num) habs
      have hexp2 : u * -(1 / 13 + 3 / 13 * (1 / 2 - |z.re|)) ≤ A₂ := by
        rw [hA₂]
        have h := subWeyl_profile_shift (β := 1 / 13) (c := 3 / 13)
          (δ := 0) hu0.le hE0.le hr0.le (by norm_num) (by norm_num) (by norm_num) habs
        rw [add_zero, show (1 / 13 : ℝ) * u = u / 13 by ring] at h
        exact h
      have hexp3 : u * -(1 / 53 + 23 / 53 * (1 / 2 - |z.re|)) ≤ A₃ := by
        rw [hA₃]
        have h := subWeyl_profile_shift (β := 1 / 53) (c := 23 / 53)
          (δ := 0) hu0.le hE0.le hr0.le (by norm_num) (by norm_num) (by norm_num) habs
        rw [add_zero, show (1 / 53 : ℝ) * u = u / 53 by ring] at h
        exact h
      have hexp4 : u * -(η + c * (1 / 2 + η - |z.re|)) ≤ A₄ := by
        rw [hA₄]
        exact subWeyl_profile_shift (β := η) (c := c) (δ := η)
          hu0.le hE0.le hr0.le hc0 hc1 hη.le habs
      have hCC : C₁ * S₀ ≤ (C₁ + C₂) * S₀ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂.le) hS₀0
      exact mul_le_mul hCC (add_le_add (add_le_add (add_le_add (Real.exp_le_exp.mpr hexp1)
          (Real.exp_le_exp.mpr hexp2)) (Real.exp_le_exp.mpr hexp3)) (Real.exp_le_exp.mpr hexp4))
        (by positivity) (mul_nonneg (add_nonneg hC₁.le hC₂.le) hS₀0)
    · push Not at ha
      obtain ⟨-, hout⟩ := hS₂ t z.re z.im (by linarith only [ht]) (by linarith only [hzc, hr1])
      refine le_trans (hout ha (by linarith only [habs, hx, hr1, ht])) ?_
      set y := max |z.re| (1 / 2 + 2 * η) with hy
      have hy1 : 1 / 2 + 2 * η ≤ y := le_max_right _ _
      have hy2 : y ≤ t / 2 := max_le
        (by linarith only [habs, hx, hr1, ht]) (by linarith only [hη1, ht])
      have hgrow := (xiSliceReal_growth_euler (t := t) hη (by linarith only [ht])
        (y₁ := 1 / 2 + 2 * η) (y₂ := y) (by linarith only [hη]) hy1 hy2).2
      rw [← hudef, ← hEdef, ← hS₀] at hgrow
      have hexp : (u + 2 * E) * (y - (1 / 2 + 2 * η)) ≤ A₄ := by
        rw [hA₄]
        have hcu : c * u * (1 / 2 - |x|) ≤ u * (1 / 2 - |x|) := by
          have := mul_le_mul_of_nonneg_right hc1 (by positivity : (0 : ℝ) ≤ u * (1 / 2 - |x|))
          linarith only [this]
        have e0 : u * (1 / 2 - |x|) - c * u * (1 / 2 - |x|) = (1 - c) * (u * (1 / 2 - |x|)) := by
          ring
        have hcu' : 0 ≤ (1 - c) * (u * (1 / 2 - |x|)) :=
          mul_nonneg (by linarith only [hc1]) (by positivity)
        rcases le_total |z.re| (1 / 2 + 2 * η) with h | h
        · rw [hy, max_eq_right h, sub_self, mul_zero]
          have h1 : 1 / 2 + η - |x| ≤ r := by linarith only [ha, habs]
          have h2 : u * (1 / 2 + η - |x|) ≤ u * r := mul_le_mul_of_nonneg_left h1 hu0.le
          have h3 : 0 ≤ E * r := mul_nonneg hE0.le hr0.le
          have e1 : (u + 2 * E) * r - η * u - c * u * (1 / 2 - |x|)
              = (u * r - u * (1 / 2 + η - |x|)) + 2 * (E * r)
                + (u * (1 / 2 - |x|) - c * u * (1 / 2 - |x|)) := by ring
          linarith only [h2, h3, e0, e1, hcu']
        · rw [hy, max_eq_left h]
          have h1 : |z.re| - (1 / 2 + 2 * η) ≤ r + |x| - 1 / 2 - 2 * η := by linarith only [habs]
          have h2 := mul_le_mul_of_nonneg_left h1 hu2E.le
          have hneg : |x| - 1 / 2 - 2 * η ≤ 0 := by linarith only [hx, hη]
          have h3 : 2 * E * (|x| - 1 / 2 - 2 * η) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
          have e1 : (u + 2 * E) * (r + |x| - 1 / 2 - 2 * η)
              = (u + 2 * E) * r + u * (|x| - 1 / 2 - 2 * η) + 2 * E * (|x| - 1 / 2 - 2 * η) := by
            ring
          have e2 : u * (|x| - 1 / 2 - 2 * η) = -(u * (1 / 2 - |x|)) - 2 * (η * u) := by ring
          have hηu : 0 ≤ η * u := by positivity
          linarith only [h2, h3, e0, e1, e2, hcu', hηu]
      calc C₂ * xiSliceReal t y
          ≤ C₂ * (S₀ * Real.exp ((u + 2 * E) * (y - (1 / 2 + 2 * η)))) :=
            mul_le_mul_of_nonneg_left hgrow hC₂.le
        _ ≤ (C₁ + C₂) * (S₀ * Real.exp A₄) :=
            mul_le_mul (le_add_of_nonneg_left hC₁.le)
              (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hS₀0)
              (by positivity) (add_nonneg hC₁.le hC₂.le)
        _ ≤ (C₁ + C₂) * (S₀ * (Real.exp A₁ + Real.exp A₂ + Real.exp A₃ + Real.exp A₄)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (by linarith only [hE1, hE2, hE3]) hS₀0) (add_nonneg hC₁.le hC₂.le)
        _ = M := by rw [hM]; ring
  have hcauchy := norm_iteratedDeriv_xiSliceProduct_le t N hr0 hMb
  have hfact : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  rw [div_le_iff₀ hfact, ← hS₀]
  have hA₁' : A₁ = N - 31 / 200 * u - 3 / 100 * u * (1 / 2 - |x|) := by rw [hA₁, hrN]
  have hA₂' : A₂ = N - u / 13 - 3 / 13 * u * (1 / 2 - |x|) := by rw [hA₂, hrN]
  have hA₃' : A₃ = N - u / 53 - 23 / 53 * u * (1 / 2 - |x|) := by rw [hA₃, hrN]
  have hA₄' : A₄ = N - η * u - c * u * (1 / 2 - |x|) := by rw [hA₄, hrN]
  calc ‖iteratedDeriv N (xiSliceProduct t) (x : ℂ)‖ ≤ N.factorial * M / r ^ N := hcauchy
    _ = (C₁ + C₂) * S₀ * ((Real.exp (N - 31 / 200 * u - 3 / 100 * u * (1 / 2 - |x|))
          + Real.exp (N - u / 13 - 3 / 13 * u * (1 / 2 - |x|))
          + Real.exp (N - u / 53 - 23 / 53 * u * (1 / 2 - |x|))
          + Real.exp (N - η * u - c * u * (1 / 2 - |x|))) * ((u + 2 * E) / N) ^ N)
          * N.factorial := by
        rw [hM, ← hA₁', ← hA₂', ← hA₃', ← hA₄', hrdef, div_pow, div_pow]
        field_simp

end RHTower

#print axioms RHTower.exists_norm_iteratedDeriv_xiSliceProduct_le_inner_four_subWeyl_profiles
