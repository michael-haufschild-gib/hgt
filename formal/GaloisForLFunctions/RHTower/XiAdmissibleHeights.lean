import GaloisForLFunctions.RHTower.XiSymmetricMassBounds
import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# Heights carrying no `ξ`-zero are dense

All `ξ`-zeros lie in the open critical strip, so those with ordinate in a bounded interval lie in a
compact box and are finite in number.  Their ordinates form a finite set, and any nonempty open
interval of heights therefore contains a height at which the whole horizontal line misses the
divisor.  Such heights are exactly the ones the rectangle argument principle admits.
-/

open Complex Set Metric

noncomputable section

namespace RHTower

/-- **Admissible heights are dense.** -/
theorem exists_admissible_height {a b : ℝ} (hab : a < b) :
    ∃ T ∈ Set.Ioo a b, ∀ x : ℝ, xi ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
  classical
  set R : ℝ := |a| + |b| + 2 with hR
  have hfin : {z ∈ Metric.closedBall (0 : ℂ) R | xi z = 0}.Finite :=
    xi_zeros_closedBall_finite 0 R
  set ords : Finset ℝ := hfin.toFinset.image Complex.im with hords
  have hinf : (Set.Ioo a b).Infinite := Set.Ioo_infinite hab
  obtain ⟨T, hTmem, hTnot⟩ := (hinf.exists_notMem_finset ords)
  refine ⟨T, hTmem, fun x hzero => ?_⟩
  have hstrip := xi_zero_re_mem_open_unit hzero
  have hre : ((x : ℂ) + (T : ℂ) * I).re = x := by simp
  have him : ((x : ℂ) + (T : ℂ) * I).im = T := by simp
  rw [hre] at hstrip
  have hTa : a < T := hTmem.1
  have hTb : T < b := hTmem.2
  have hTabs : |T| ≤ |a| + |b| := by
    rw [abs_le]
    constructor
    · have h1 : -|a| ≤ a := neg_abs_le a
      have h2 : (0 : ℝ) ≤ |b| := abs_nonneg b
      linarith
    · have h1 : b ≤ |b| := le_abs_self b
      have h2 : (0 : ℝ) ≤ |a| := abs_nonneg a
      linarith
  have hball : ((x : ℂ) + (T : ℂ) * I) ∈ Metric.closedBall (0 : ℂ) R := by
    rw [mem_closedBall, dist_zero_right]
    refine le_trans (Complex.norm_le_abs_re_add_abs_im _) ?_
    rw [hre, him, hR]
    have hx : |x| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hstrip.1, hstrip.2]
    linarith
  refine hTnot ?_
  rw [hords, Finset.mem_image]
  exact ⟨(x : ℂ) + (T : ℂ) * I, by rw [Set.Finite.mem_toFinset]; exact ⟨hball, hzero⟩, him⟩

/-! ## The annular count -/

/-- **Every fixed multiplicative annulus eventually carries any prescribed divisor mass.**  Two
admissible heights straddling the annulus have mass difference at least `C`, and that difference is
the divisor mass carried by ordinates between them. -/
theorem exists_annular_mass_lower (C : ℝ) :
    ∃ Γ₀ : ℝ, ∀ Γ : ℝ, Γ₀ ≤ Γ →
      ∃ T₁ T₂ : ℝ, Γ < T₁ ∧ T₁ < T₂ ∧ T₂ < 10 * Γ ∧
        (∀ x : ℝ, xi ((x : ℂ) + (T₁ : ℂ) * I) ≠ 0) ∧
        (∀ x : ℝ, xi ((x : ℂ) + (T₂ : ℂ) * I) ≠ 0) ∧
        C ≤ (xiSymmetricMass T₂ : ℝ) - (xiSymmetricMass T₁ : ℝ) := by
  obtain ⟨T₀, hT₀4, hbounds⟩ := exists_xiSymmetricMass_two_sided
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hlogtop : Filter.Tendsto
      (fun Γ : ℝ => (1 / (2 * Real.pi)) * (Γ * Real.log Γ) - (4 * Real.log 2 / Real.pi) * Γ)
      Filter.atTop Filter.atTop := by
    have hsub : Filter.Tendsto
        (fun Γ : ℝ => Γ * ((1 / (2 * Real.pi)) * Real.log Γ - 4 * Real.log 2 / Real.pi))
        Filter.atTop Filter.atTop := by
      refine Filter.Tendsto.atTop_mul_atTop₀ Filter.tendsto_id ?_
      have h1 : Filter.Tendsto (fun Γ : ℝ => (1 / (2 * Real.pi)) * Real.log Γ)
          Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (by positivity) Real.tendsto_log_atTop
      exact h1.atTop_add tendsto_const_nhds
    refine hsub.congr fun Γ => ?_
    ring
  obtain ⟨Γ₁, hΓ₁⟩ := Filter.eventually_atTop.mp ((Filter.tendsto_atTop.mp hlogtop) C)
  refine ⟨max (max Γ₁ T₀) 4, fun Γ hΓ => ?_⟩
  have hΓ4 : (4 : ℝ) ≤ Γ := le_trans (le_max_right _ _) hΓ
  have hΓT₀ : T₀ ≤ Γ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΓ
  have hΓΓ₁ : Γ₁ ≤ Γ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΓ
  have hΓ0 : (0 : ℝ) < Γ := by linarith
  have hlogΓ : (1 : ℝ) ≤ Real.log Γ := by
    rw [Real.le_log_iff_exp_le hΓ0]
    have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    linarith
  obtain ⟨T₁, hT₁mem, hT₁ne⟩ := exists_admissible_height (a := Γ) (b := 2 * Γ) (by linarith)
  obtain ⟨T₂, hT₂mem, hT₂ne⟩ := exists_admissible_height (a := 9 * Γ) (b := 10 * Γ) (by linarith)
  refine ⟨T₁, T₂, hT₁mem.1, by linarith [hT₁mem.2, hT₂mem.1], hT₂mem.2, hT₁ne, hT₂ne, ?_⟩
  have hT₁0 : (0 : ℝ) < T₁ := by linarith [hT₁mem.1]
  have hT₂0 : (0 : ℝ) < T₂ := by linarith [hT₂mem.1]
  obtain ⟨hlow₁, hhigh₁⟩ := hbounds T₁ (by linarith [hT₁mem.1]) hT₁ne
  obtain ⟨hlow₂, hhigh₂⟩ := hbounds T₂ (by linarith [hT₂mem.1]) hT₂ne
  -- lower bound for the big height
  have hlogT₂ : Real.log Γ ≤ Real.log T₂ :=
    Real.log_le_log hΓ0 (by linarith [hT₂mem.1])
  have hbig : (9 / (2 * Real.pi)) * (Γ * Real.log Γ) ≤ (xiSymmetricMass T₂ : ℝ) := by
    have h1 : 9 * Γ ≤ T₂ := by linarith [hT₂mem.1]
    have hlogpos : (0 : ℝ) < Real.log Γ := by linarith
    have hkey : 9 * (Γ * Real.log Γ) ≤ T₂ * Real.log T₂ := by
      have hprod : (9 * Γ) * Real.log Γ ≤ T₂ * Real.log T₂ :=
        mul_le_mul h1 hlogT₂ hlogpos.le (by linarith)
      linarith [hprod]
    calc (9 / (2 * Real.pi)) * (Γ * Real.log Γ)
        = (1 / (2 * Real.pi)) * (9 * (Γ * Real.log Γ)) := by ring
      _ ≤ (1 / (2 * Real.pi)) * (T₂ * Real.log T₂) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ ≤ (xiSymmetricMass T₂ : ℝ) := hlow₂
  -- upper bound for the small height
  have hlogT₁ : Real.log T₁ ≤ Real.log 2 + Real.log Γ := by
    have h1 : T₁ ≤ 2 * Γ := le_of_lt hT₁mem.2
    have h2 : Real.log T₁ ≤ Real.log (2 * Γ) := Real.log_le_log hT₁0 h1
    rwa [Real.log_mul (by norm_num) hΓ0.ne'] at h2
  have hsmall : (xiSymmetricMass T₁ : ℝ)
      ≤ (4 / Real.pi) * (Γ * Real.log Γ) + (4 * Real.log 2 / Real.pi) * Γ := by
    refine le_trans hhigh₁ ?_
    have h1 : T₁ ≤ 2 * Γ := le_of_lt hT₁mem.2
    have hlogT₁0 : 0 ≤ Real.log T₁ := Real.log_nonneg (by linarith [hT₁mem.1])
    have hprod : T₁ * Real.log T₁ ≤ (2 * Γ) * (Real.log 2 + Real.log Γ) :=
      mul_le_mul h1 hlogT₁ hlogT₁0 (by linarith)
    have hkey : 2 * (T₁ * Real.log T₁) ≤ 4 * (Γ * Real.log Γ) + 4 * Real.log 2 * Γ := by
      nlinarith [hprod]
    calc (2 / Real.pi) * (T₁ * Real.log T₁)
        = (1 / Real.pi) * (2 * (T₁ * Real.log T₁)) := by ring
      _ ≤ (1 / Real.pi) * (4 * (Γ * Real.log Γ) + 4 * Real.log 2 * Γ) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (4 / Real.pi) * (Γ * Real.log Γ) + (4 * Real.log 2 / Real.pi) * Γ := by ring
  have hgap := hΓ₁ Γ hΓΓ₁
  have harith : (9 / (2 * Real.pi)) * (Γ * Real.log Γ)
      - ((4 / Real.pi) * (Γ * Real.log Γ) + (4 * Real.log 2 / Real.pi) * Γ)
      = (1 / (2 * Real.pi)) * (Γ * Real.log Γ) - (4 * Real.log 2 / Real.pi) * Γ := by
    field_simp
    ring
  linarith [hbig, hsmall, hgap, harith]

end RHTower
