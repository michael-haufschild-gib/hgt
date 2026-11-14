import GaloisForLFunctions.CompactHyperbolicSurfaces.BergmanProjection

/-!
# The area of a compact surface is an integer multiple of `2π`

For the weight-`2(j + 2)` Bergman kernel `K_j` of `X = Γ\ℍ`, `d_j = ∫_F K_j(y, y) dμ(y)` is a
natural number (`exists_nat_integral_bergAut_diag`).  The term `γ = 1` of `K_j(y, y)` is
`c_j = (2j + 3)/4π`.  For `γ ≠ 1` and `y ∈ F` the displacement is bounded below,
`u(y, γy) ≥ u₀ > 0` (`exists_pairU_ge`), so `|K_j(y, y) − c_j| ≤ c_j M q^j` with
`q = 1/(1 + u₀) < 1` and `M` the bound of `Σ_γ (1 + u(y, γy))^{−2}`
(`norm_bergAut_diag_sub_le`).  Hence `|d_j − c_j |F|| ≤ c_j |F| M q^j`; as `c_{j+1} − c_j = 1/2π`,
the integers `d_{j+1} − d_j` converge to `|F|/2π`, which is therefore a natural number
(`exists_nat_volume_F_eq`): **`|F| = 2πN`**, Gauss–Bonnet integrality without polygons.
-/

open MeasureTheory Set Filter UpperHalfPlane
open scoped ENNReal MatrixGroups Real Topology

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- A real number approximable by integers to any precision is an integer. -/
theorem exists_int_eq_of_forall_approx {x : ℝ} (h : ∀ ε > 0, ∃ k : ℤ, |x - k| < ε) :
    ∃ k : ℤ, x = k := by
  obtain ⟨k₀, hk₀⟩ := h (1 / 2) (by norm_num)
  refine ⟨k₀, ?_⟩
  by_contra hne
  have hδ : 0 < |x - k₀| := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨k, hk⟩ := h (min |x - k₀| (1 / 2)) (lt_min hδ (by norm_num))
  have hk1 : |x - k| < 1 / 2 := hk.trans_le (min_le_right _ _)
  have hkk : k = k₀ := by
    have h1 : |((k - k₀ : ℤ) : ℝ)| < 1 := by
      push_cast
      calc |(k : ℝ) - k₀| = |(x - k₀) - (x - k)| := by ring_nf
        _ ≤ |x - k₀| + |x - k| := abs_sub _ _
        _ < 1 := by linarith
    have h2 : |k - k₀| < 1 := by exact_mod_cast h1
    exact sub_eq_zero.mp (Int.abs_lt_one_iff.mp h2)
  subst hkk
  exact lt_irrefl _ (hk.trans_le (min_le_left _ _))

theorem bergTerm_one (j : ℕ) (y : ℍ) : bergTerm j 1 y y = 1 := by
  rw [bergTerm, one_smul, bergK_self, autF_one, one_pow, mul_one]

namespace CompactQuotient

variable (X : CompactQuotient)

/-- **Displacement bound.**  `u(y, γy) ≥ u₀ > 0` for `y ∈ F`, `γ ≠ 1`. -/
theorem exists_pairU_ge : ∃ u₀ > 0, ∀ y ∈ X.F, ∀ γ : X.Γ, γ ≠ 1 →
    u₀ ≤ pairU y ((γ : SL(2, ℝ)) • y) := by
  obtain ⟨ε, hε, -, hεK⟩ := X.cocompactFree.exists_dist_smul_ge X.isCompact_K
  refine ⟨(Real.cosh ε - 1) / 2, by have := Real.one_lt_cosh.mpr hε.ne'; linarith,
    fun y hy γ hγ => ?_⟩
  rw [pairU_eq_cosh]
  have hd := hεK y (X.F_subset hy) γ hγ
  have : Real.cosh ε ≤ Real.cosh (dist y ((γ : SL(2, ℝ)) • y)) :=
    Real.cosh_le_cosh.mpr (by rw [abs_of_pos hε, abs_of_nonneg dist_nonneg]; exact hd)
  linarith

variable {X} {u₀ : ℝ} (hu₀ : 0 < u₀)
  (hu : ∀ y ∈ X.F, ∀ γ : X.Γ, γ ≠ 1 → u₀ ≤ pairU y ((γ : SL(2, ℝ)) • y))
include hu₀ hu

/-- `|K_j(y, y) − c_j| ≤ c_j M q^j` on `F`, `q = 1/(1 + u₀)`. -/
theorem norm_bergAut_diag_sub_le (j : ℕ) {y : ℍ} (hy : y ∈ X.F) :
    ‖X.bergAut j y y - bergC j‖ ≤ bergC j * (X.bergBound 0 * (1 + u₀)⁻¹ ^ j) := by
  classical
  have hs := X.summable_bergTerm j y y
  rw [bergAut, hs.tsum_eq_add_tsum_ite 1, OneMemClass.coe_one, bergTerm_one, mul_add, mul_one,
    add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg (bergC_pos j).le]
  refine mul_le_mul_of_nonneg_left ?_ (bergC_pos j).le
  have hle : ∀ γ : X.Γ, ‖(if γ = 1 then 0 else bergTerm j γ y y)‖ ≤
      (1 + u₀)⁻¹ ^ j * ‖bergTerm 0 γ y y‖ := by
    intro γ
    split_ifs with h
    · rw [norm_zero]; positivity
    · rw [norm_bergTerm, norm_bergTerm]
      have h1 := pairU_nonneg y ((γ : SL(2, ℝ)) • y)
      have h2 := hu y hy γ h
      have hq : (1 + pairU y ((γ : SL(2, ℝ)) • y))⁻¹ ≤ (1 + u₀)⁻¹ :=
        inv_anti₀ (by linarith) (by linarith)
      rw [← inv_pow, ← inv_pow, show j + 2 = j + (0 + 2) by ring, pow_add]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hq j) (by positivity)
  have hsn : Summable fun γ : X.Γ => ‖(if γ = 1 then 0 else bergTerm j γ y y)‖ :=
    Summable.of_nonneg_of_le (fun γ => norm_nonneg _) hle
      ((X.summable_norm_bergTerm 0 y y).mul_left _)
  calc ‖∑' γ : X.Γ, (if γ = 1 then 0 else bergTerm j γ y y)‖
      ≤ ∑' γ : X.Γ, ‖(if γ = 1 then 0 else bergTerm j γ y y)‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' γ : X.Γ, (1 + u₀)⁻¹ ^ j * ‖bergTerm 0 γ y y‖ :=
        hsn.tsum_le_tsum hle ((X.summable_norm_bergTerm 0 y y).mul_left _)
    _ = (1 + u₀)⁻¹ ^ j * ∑' γ : X.Γ, ‖bergTerm 0 γ y y‖ := tsum_mul_left
    _ ≤ (1 + u₀)⁻¹ ^ j * X.bergBound 0 :=
        mul_le_mul_of_nonneg_left (X.tsum_norm_bergTerm_le 0 y y) (by positivity)
    _ = X.bergBound 0 * (1 + u₀)⁻¹ ^ j := mul_comm _ _

/-- `|d_j − c_j |F|| ≤ c_j |F| M q^j`. -/
theorem norm_integral_bergAut_diag_sub_le (j : ℕ) :
    ‖(∫ y in X.F, X.bergAut j y y) - ((bergC j * (volume X.F).toReal : ℝ) : ℂ)‖ ≤
      bergC j * (X.bergBound 0 * (1 + u₀)⁻¹ ^ j) * (volume X.F).toReal := by
  have hc : Continuous fun y : ℍ => X.bergAut j y y :=
    (X.continuous_bergAut j).comp₂ continuous_id continuous_id
  have hint : IntegrableOn (fun y : ℍ => X.bergAut j y y) X.F :=
    Measure.integrableOn_of_bounded X.volume_F_lt_top.ne hc.aestronglyMeasurable
      (Eventually.of_forall fun y => X.norm_bergAut_le j y y)
  have h1 : (∫ y in X.F, X.bergAut j y y) - ((bergC j * (volume X.F).toReal : ℝ) : ℂ) =
      ∫ y in X.F, (X.bergAut j y y - bergC j) := by
    rw [integral_sub hint (integrable_const _), setIntegral_const, Complex.real_smul]
    simp only [Measure.real]
    push_cast
    ring
  rw [h1]
  refine (norm_setIntegral_le_of_norm_le_const X.volume_F_lt_top
    fun y hy => norm_bergAut_diag_sub_le hu₀ hu j hy).trans (le_of_eq ?_)
  simp only [Measure.real]

omit hu₀ hu in
/-- **Integrality of the area.**  `|F| = 2πN` for a natural number `N`. -/
theorem exists_nat_volume_F_eq : ∃ N : ℕ, (volume X.F).toReal = 2 * π * N := by
  obtain ⟨u₀, hu₀, hu⟩ := X.exists_pairU_ge
  set A := (volume X.F).toReal with hA
  set M := X.bergBound 0
  set q := (1 + u₀)⁻¹ with hqdef
  have hA0 : 0 ≤ A := ENNReal.toReal_nonneg
  have hM0 : 0 ≤ M := X.bergBound_nonneg 0
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hπ := Real.pi_pos
  choose d hd using fun j => X.exists_nat_integral_bergAut_diag j
  have he : ∀ j, |(d j : ℝ) - bergC j * A| ≤ bergC j * (M * q ^ j) * A := by
    intro j
    have h := norm_integral_bergAut_diag_sub_le hu₀ hu j
    rw [hd j, ← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at h
    exact h
  have hc : ∀ j : ℕ, bergC j = (2 * j + 3) / (4 * π) := fun j => rfl
  set x := A / (2 * π)
  have hlim : ∀ ε > 0, ∃ k : ℤ, |x - k| < ε := by
    intro ε hε
    have ht : Tendsto (fun j : ℕ => M * A / π * (((j : ℝ) + 3) * q ^ j)) atTop (𝓝 0) := by
      have h1 := tendsto_pow_const_mul_const_pow_of_abs_lt_one 1
        (by rw [abs_of_nonneg hq0]; exact hq1)
      have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
      have h3 := (h1.add (h2.const_mul 3)).const_mul (M * A / π)
      simp only [pow_one, mul_zero, add_zero] at h3
      exact h3.congr fun j => by ring
    obtain ⟨j, hj⟩ := (ht.eventually (gt_mem_nhds hε)).exists
    refine ⟨(d (j + 1) : ℤ) - d j, ?_⟩
    have hx : x = bergC (j + 1) * A - bergC j * A := by
      simp only [x]; rw [hc, hc]; push_cast; field_simp; ring
    have e1 := he (j + 1)
    have e2 := he j
    have hqj : q ^ (j + 1) ≤ q ^ j := pow_le_pow_of_le_one hq0 hq1.le (Nat.le_succ j)
    have hb : bergC (j + 1) * (M * q ^ (j + 1)) * A + bergC j * (M * q ^ j) * A ≤
        M * A / π * (((j : ℝ) + 3) * q ^ j) := by
      rw [hc, hc]
      have hqj' : 0 ≤ q ^ j := pow_nonneg hq0 j
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have key : ((2 * ((j + 1 : ℕ) : ℝ) + 3) * q ^ (j + 1) + (2 * j + 3) * q ^ j) ≤
          4 * ((j + 3) * q ^ j) := by
        push_cast
        nlinarith [mul_le_mul_of_nonneg_left hqj (by linarith : (0 : ℝ) ≤ 2 * (j + 1) + 3)]
      have hMA : 0 ≤ M * A := mul_nonneg hM0 hA0
      calc (2 * ((j + 1 : ℕ) : ℝ) + 3) / (4 * π) * (M * q ^ (j + 1)) * A +
            (2 * j + 3) / (4 * π) * (M * q ^ j) * A
          = M * A / (4 * π) * ((2 * ((j + 1 : ℕ) : ℝ) + 3) * q ^ (j + 1) + (2 * j + 3) * q ^ j) := by
            field_simp
        _ ≤ M * A / (4 * π) * (4 * ((j + 3) * q ^ j)) :=
            mul_le_mul_of_nonneg_left key (by positivity)
        _ = M * A / π * (((j : ℝ) + 3) * q ^ j) := by field_simp
    calc |x - (((d (j + 1) : ℤ) - d j : ℤ) : ℝ)| =
        |((d j : ℝ) - bergC j * A) - ((d (j + 1) : ℝ) - bergC (j + 1) * A)| := by
          rw [hx]; push_cast; ring_nf
      _ ≤ |(d j : ℝ) - bergC j * A| + |(d (j + 1) : ℝ) - bergC (j + 1) * A| := abs_sub _ _
      _ ≤ bergC j * (M * q ^ j) * A + bergC (j + 1) * (M * q ^ (j + 1)) * A := add_le_add e2 e1
      _ ≤ M * A / π * (((j : ℝ) + 3) * q ^ j) := by linarith
      _ < ε := hj
  obtain ⟨k, hk⟩ := exists_int_eq_of_forall_approx hlim
  have hk0 : 0 ≤ k := by
    have : (0 : ℝ) ≤ k := by rw [← hk]; positivity
    exact_mod_cast this
  refine ⟨k.toNat, ?_⟩
  rw [show ((k.toNat : ℕ) : ℝ) = k by exact_mod_cast Int.toNat_of_nonneg hk0, ← hk]
  simp only [x]
  field_simp

end CompactQuotient

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
