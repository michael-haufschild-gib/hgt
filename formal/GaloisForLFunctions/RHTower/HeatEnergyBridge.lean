import GaloisForLFunctions.RHTower.TrigPolyOrthogonality
import GaloisForLFunctions.RHTower.DirichletAbel
import GaloisForLFunctions.RHTower.BoundaryGermL2
import GaloisForLFunctions.RHTower.HeatEnergyAsymptotic

/-!
# The truncated Dirichlet germ

The truncations of the boundary Dirichlet series are trigonometric polynomials, so both the
orthogonality identity and the additive-heat quadratic-form identity apply to them verbatim, and
they converge pointwise to the boundary germ off the phase origin.
-/

open Complex HurwitzZeta MeasureTheory Set Filter Topology

namespace RHTower

/-- The index set of the first `N` positive modes. -/
noncomputable def modeSet (N : ℕ) : Finset ℤ :=
  (Finset.range N).map ⟨fun i : ℕ => (i : ℤ) + 1, fun i j h => by
    simp only [add_left_inj, Nat.cast_inj] at h
    exact h⟩

theorem sum_modeSet {M : Type*} [AddCommMonoid M] (N : ℕ) (F : ℤ → M) :
    ∑ n ∈ modeSet N, F n = ∑ i ∈ Finset.range N, F ((i : ℤ) + 1) := by
  rw [modeSet, Finset.sum_map]
  rfl

/-- The truncated boundary Dirichlet germ. -/
noncomputable def dirichletTrunc (s : ℂ) (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ n ∈ modeSet N, (((n : ℝ)) : ℂ) ^ (-s) * Complex.exp (I * (n : ℂ) * (θ : ℂ))

/-- **The window `L²` norm of a truncation.** -/
theorem integral_dirichletTrunc_normSq (s : ℂ) (N : ℕ) :
    (∫ θ in Ioc (-Real.pi) Real.pi,
        dirichletTrunc s N θ * (starRingEnd ℂ) (dirichletTrunc s N θ))
      = 2 * Real.pi * ∑ i ∈ Finset.range N, ((((i : ℝ) + 1) ^ (-2 * s.re) : ℝ) : ℂ) := by
  simp only [dirichletTrunc]
  rw [integral_trigPoly_normSq (modeSet N) (fun n => (((n : ℝ)) : ℂ) ^ (-s))]
  congr 1
  rw [sum_modeSet]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hpos : (0 : ℝ) < ((i : ℝ) + 1) := by positivity
  have hcast : ((((i : ℤ) + 1 : ℤ) : ℝ)) = ((i : ℝ) + 1) := by push_cast; ring
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hre : (-s).re = -s.re := by simp
  rw [hre, ← Real.rpow_natCast (((i : ℝ) + 1) ^ (-s.re)) 2, ← Real.rpow_mul hpos.le]
  congr 1
  push_cast
  ring

/-- **The truncations converge pointwise to the boundary germ off the phase origin.** -/
theorem tendsto_dirichletTrunc {s : ℂ} (hs : 0 < s.re) {θ : ℝ}
    (hθ0 : -Real.pi < θ) (hθ1 : θ ≤ Real.pi) (hne : θ ≠ 0) :
    Tendsto (fun N : ℕ => dirichletTrunc s N θ) atTop (𝓝 (phaseGerm s θ)) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set a : ℝ := θ / (2 * Real.pi) with ha
  have hane : a ≠ 0 := by
    rw [ha]
    exact div_ne_zero hne (by positivity)
  have habs : |a| < 1 / 2 ∨ a = 1 / 2 := by
    rcases eq_or_lt_of_le hθ1 with h | h
    · right
      rw [ha, h]
      field_simp
    · left
      rw [ha, abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi),
        div_lt_div_iff₀ (by positivity) (by norm_num)]
      rcases abs_cases θ with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> linarith
  have hnotint : ∀ n : ℤ, a ≠ (n : ℝ) := by
    intro n hcon
    rcases habs with h | h
    · rw [hcon] at h hane
      have hn0 : n = 0 := by
        by_contra hne'
        have : (1 : ℝ) ≤ |(n : ℝ)| := by
          have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs hne'
          calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
            _ ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h1
            _ = |(n : ℝ)| := by push_cast [Int.cast_abs]; ring
        linarith
      rw [hn0] at hane
      simp at hane
    · rw [hcon] at h
      have h2 : (2 : ℝ) * (n : ℝ) = 1 := by linarith
      have : (2 * n : ℤ) = 1 := by exact_mod_cast h2
      omega
  have hexpne : Complex.exp (2 * ↑Real.pi * I * a) ≠ 1 := by
    intro hcon0
    rw [Complex.exp_eq_one_iff] at hcon0
    obtain ⟨n, hcon⟩ := hcon0
    refine hnotint n ?_
    have hpine : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
    have hIne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hc : ((a : ℝ) : ℂ) = ((n : ℤ) : ℂ) := by
      field_simp at hcon
      exact hcon
    exact_mod_cast hc
  have hzero : ((a : ℝ) : UnitAddCircle) ≠ 0 := by
    intro hcon0
    rw [AddCircle.coe_eq_zero_iff] at hcon0
    obtain ⟨n, hcon⟩ := hcon0
    exact hnotint n (by simpa using hcon.symm)
  have hlim := tendsto_abelDirichlet (norm_coeffPartial_expCoeff_le hexpne) hs
  rw [abelDirichlet_eq_expZeta hzero hexpne hs] at hlim
  have hgerm : expZeta ((a : ℝ) : UnitAddCircle) s = phaseGerm s θ := by
    rw [phaseGerm, ha]
  rw [hgerm] at hlim
  refine hlim.congr fun N => ?_
  rw [dirichletTrunc, sum_modeSet]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcast : ((((i : ℤ) + 1 : ℤ) : ℝ)) = ((i : ℝ) + 1) := by push_cast; ring
  rw [hcast]
  congr 1
  rw [expCoeff, ← Complex.exp_nat_mul]
  congr 1
  have h2a : (2 * (↑Real.pi : ℂ) * I * ((a : ℝ) : ℂ)) = I * ((θ : ℝ) : ℂ) := by
    rw [ha]
    push_cast
    field_simp
  push_cast
  rw [show ((i : ℕ) + 1 : ℂ) * (2 * (↑Real.pi : ℂ) * I * ((a : ℝ) : ℂ))
      = ((i : ℂ) + 1) * (2 * (↑Real.pi : ℂ) * I * ((a : ℝ) : ℂ)) by ring, h2a]
  ring

/-- The mode sets are nested. -/
theorem modeSet_subset {N M : ℕ} (h : N ≤ M) : modeSet N ⊆ modeSet M := by
  intro n hn
  rw [modeSet, Finset.mem_map] at hn ⊢
  obtain ⟨i, hi, rfl⟩ := hn
  exact ⟨i, Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) h), rfl⟩

theorem modeSet_sdiff {N M : ℕ} (_h : N ≤ M) :
    modeSet M \ modeSet N
      = (Finset.Ico N M).map ⟨fun i : ℕ => (i : ℤ) + 1, fun i j hij => by
          simp only [add_left_inj, Nat.cast_inj] at hij
          exact hij⟩ := by
  ext n
  simp only [Finset.mem_sdiff, modeSet, Finset.mem_map, Finset.mem_range, Finset.mem_Ico,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hnot⟩
    refine ⟨i, ⟨?_, hi⟩, rfl⟩
    by_contra hlt
    exact hnot ⟨i, by omega, rfl⟩
  · rintro ⟨i, ⟨hNi, hiM⟩, rfl⟩
    refine ⟨⟨i, hiM, rfl⟩, ?_⟩
    rintro ⟨j, hj, hji⟩
    have : j = i := by
      simp only [add_left_inj, Nat.cast_inj] at hji
      exact hji
    omega

/-- **The `L²` distance between two truncations.** -/
theorem integral_trunc_sub_normSq (s : ℂ) {N M : ℕ} (h : N ≤ M) :
    (∫ θ in Ioc (-Real.pi) Real.pi,
        (dirichletTrunc s M θ - dirichletTrunc s N θ)
          * (starRingEnd ℂ) (dirichletTrunc s M θ - dirichletTrunc s N θ))
      = 2 * Real.pi * ∑ i ∈ Finset.Ico N M, ((((i : ℝ) + 1) ^ (-2 * s.re) : ℝ) : ℂ) := by
  have hsplit : ∀ θ : ℝ, dirichletTrunc s M θ - dirichletTrunc s N θ
      = ∑ n ∈ modeSet M \ modeSet N,
          (((n : ℝ)) : ℂ) ^ (-s) * Complex.exp (I * (n : ℂ) * (θ : ℂ)) := by
    intro θ
    simp only [dirichletTrunc]
    rw [sub_eq_iff_eq_add, ← Finset.sum_sdiff (modeSet_subset h)]
  simp only [hsplit]
  rw [integral_trigPoly_normSq (modeSet M \ modeSet N) (fun n => (((n : ℝ)) : ℂ) ^ (-s)),
    modeSet_sdiff h, Finset.sum_map]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have hpos : (0 : ℝ) < ((i : ℝ) + 1) := by positivity
  have hcast : ((((i : ℤ) + 1 : ℤ) : ℝ)) = ((i : ℝ) + 1) := by push_cast; ring
  simp only [Function.Embedding.coeFn_mk]
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hre : (-s).re = -s.re := by simp
  rw [hre, ← Real.rpow_natCast (((i : ℝ) + 1) ^ (-s.re)) 2, ← Real.rpow_mul hpos.le]
  congr 1
  push_cast
  ring

/-! ## The `L²` limit of the truncations -/

theorem summable_truncMajorant {s : ℂ} (h0 : 1 / 2 < s.re) :
    Summable (fun i : ℕ => ((i : ℝ) + 1) ^ (-2 * s.re)) := by
  have hw : (0 : ℝ) < ((((2 * s.re - 1 : ℝ)) : ℂ)).re := by simp; linarith
  have h := summable_shiftMajorant (w := (((2 * s.re - 1 : ℝ)) : ℂ)) hw
  refine h.congr fun i => ?_
  congr 1
  simp

/-- The `L²` tail of the truncations. -/
noncomputable def truncTail (s : ℂ) (N : ℕ) : ℝ :=
  ∑' i : ℕ, (((i + N : ℕ) : ℝ) + 1) ^ (-2 * s.re)

theorem truncTail_nonneg (s : ℂ) (N : ℕ) : 0 ≤ truncTail s N :=
  tsum_nonneg fun i => Real.rpow_nonneg (by positivity) _

theorem tendsto_truncTail (s : ℂ) :
    Tendsto (fun N : ℕ => truncTail s N) atTop (𝓝 0) := by
  have h := tendsto_sum_nat_add (fun i : ℕ => ((i : ℝ) + 1) ^ (-2 * s.re))
  refine h.congr fun N => ?_
  rw [truncTail]

theorem sum_Ico_le_truncTail {s : ℂ} (h0 : 1 / 2 < s.re) {N M : ℕ} (_h : N ≤ M) :
    (∑ i ∈ Finset.Ico N M, ((i : ℝ) + 1) ^ (-2 * s.re)) ≤ truncTail s N := by
  have hsum : Summable (fun i : ℕ => (((i + N : ℕ) : ℝ) + 1) ^ (-2 * s.re)) := by
    have := (summable_nat_add_iff (f := fun i : ℕ => ((i : ℝ) + 1) ^ (-2 * s.re)) N).mpr
      (summable_truncMajorant h0)
    exact this
  have hmap : (∑ i ∈ Finset.Ico N M, ((i : ℝ) + 1) ^ (-2 * s.re))
      = ∑ i ∈ Finset.range (M - N), (((i + N : ℕ) : ℝ) + 1) ^ (-2 * s.re) := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.add_comm N i]
  rw [hmap, truncTail]
  refine hsum.sum_le_tsum _ (fun i _ => Real.rpow_nonneg (by positivity) _)

/-- The real form of the Cauchy estimate. -/
theorem integral_trunc_sub_normSq_real (s : ℂ) {N M : ℕ} (h : N ≤ M) :
    (∫ θ in Ioc (-Real.pi) Real.pi, ‖dirichletTrunc s M θ - dirichletTrunc s N θ‖ ^ 2)
      = 2 * Real.pi * ∑ i ∈ Finset.Ico N M, ((i : ℝ) + 1) ^ (-2 * s.re) := by
  have hcx := integral_trunc_sub_normSq s h
  have hint : (∫ θ in Ioc (-Real.pi) Real.pi,
      (dirichletTrunc s M θ - dirichletTrunc s N θ)
        * (starRingEnd ℂ) (dirichletTrunc s M θ - dirichletTrunc s N θ))
      = (((∫ θ in Ioc (-Real.pi) Real.pi,
          ‖dirichletTrunc s M θ - dirichletTrunc s N θ‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hint] at hcx
  have hrhs : (2 : ℂ) * ↑Real.pi * ∑ i ∈ Finset.Ico N M,
      ((((i : ℝ) + 1) ^ (-2 * s.re) : ℝ) : ℂ)
      = (((2 * Real.pi * ∑ i ∈ Finset.Ico N M, ((i : ℝ) + 1) ^ (-2 * s.re) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hrhs] at hcx
  exact_mod_cast hcx

/-- Each truncation is continuous. -/
theorem continuous_dirichletTrunc (s : ℂ) (N : ℕ) : Continuous (dirichletTrunc s N) := by
  have hfun : (dirichletTrunc s N) = fun θ : ℝ => ∑ n ∈ modeSet N,
      (((n : ℝ)) : ℂ) ^ (-s) * Complex.exp (I * (n : ℂ) * (θ : ℂ)) := rfl
  rw [hfun]
  exact continuous_finsetSum _ fun n _ => by fun_prop

/-- **Fatou: the germ is the `L²` limit of its truncations.** -/
theorem lintegral_germ_sub_trunc_le {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) (N : ℕ) :
    (∫⁻ θ in Ioc (-Real.pi) Real.pi,
        ENNReal.ofReal (‖phaseGerm s θ - dirichletTrunc s N θ‖ ^ 2))
      ≤ ENNReal.ofReal (2 * Real.pi * truncTail s N) := by
  have h0' : (0 : ℝ) < s.re := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hcont : ∀ M : ℕ, Continuous
      (fun θ : ℝ => ‖dirichletTrunc s (M + N) θ - dirichletTrunc s N θ‖ ^ 2) :=
    fun M => (((continuous_dirichletTrunc s (M + N)).sub
      (continuous_dirichletTrunc s N)).norm.pow 2)
  have hmeas : ∀ M : ℕ, Measurable
      (fun θ : ℝ => ENNReal.ofReal (‖dirichletTrunc s (M + N) θ - dirichletTrunc s N θ‖ ^ 2)) :=
    fun M => ENNReal.measurable_ofReal.comp (hcont M).measurable
  have hne0 : ∀ᵐ θ ∂(volume : Measure ℝ), θ ≠ 0 :=
    MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))
  have hptwise : ∀ᵐ θ ∂(volume.restrict (Ioc (-Real.pi) Real.pi)),
      liminf (fun M : ℕ =>
        ENNReal.ofReal (‖dirichletTrunc s (M + N) θ - dirichletTrunc s N θ‖ ^ 2)) atTop
        = ENNReal.ofReal (‖phaseGerm s θ - dirichletTrunc s N θ‖ ^ 2) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc,
      MeasureTheory.ae_restrict_of_ae hne0] with θ hθ hne
    have hlim : Tendsto (fun M : ℕ => dirichletTrunc s (M + N) θ) atTop
        (𝓝 (phaseGerm s θ)) :=
      (tendsto_dirichletTrunc h0' hθ.1 hθ.2 hne).comp (tendsto_add_atTop_nat N)
    have hlim2 : Tendsto (fun M : ℕ =>
        ENNReal.ofReal (‖dirichletTrunc s (M + N) θ - dirichletTrunc s N θ‖ ^ 2)) atTop
        (𝓝 (ENNReal.ofReal (‖phaseGerm s θ - dirichletTrunc s N θ‖ ^ 2))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp
        (((hlim.sub tendsto_const_nhds).norm).pow 2)
    exact hlim2.liminf_eq
  have hfatou := MeasureTheory.lintegral_liminf_le
    (μ := volume.restrict (Ioc (-Real.pi) Real.pi)) (u := (atTop : Filter ℕ))
    (f := fun M : ℕ => fun θ : ℝ =>
      ENNReal.ofReal (‖dirichletTrunc s (M + N) θ - dirichletTrunc s N θ‖ ^ 2))
    hmeas
  rw [lintegral_congr_ae hptwise] at hfatou
  refine hfatou.trans ?_
  refine liminf_le_of_frequently_le'
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun M => ?_))
  have hle : N ≤ M + N := Nat.le_add_left N M
  have hint : IntegrableOn
      (fun θ : ℝ => ‖dirichletTrunc s (M + N) θ - dirichletTrunc s N θ‖ ^ 2)
      (Ioc (-Real.pi) Real.pi) := (hcont M).integrableOn_Ioc
  have hval : (∫⁻ θ in Ioc (-Real.pi) Real.pi,
      ENNReal.ofReal (‖dirichletTrunc s (M + N) θ - dirichletTrunc s N θ‖ ^ 2))
      = ENNReal.ofReal (∫ θ in Ioc (-Real.pi) Real.pi,
          ‖dirichletTrunc s (M + N) θ - dirichletTrunc s N θ‖ ^ 2) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun θ => by positivity)).symm
  rw [hval, integral_trunc_sub_normSq_real s hle]
  refine ENNReal.ofReal_le_ofReal ?_
  refine mul_le_mul_of_nonneg_left (sum_Ico_le_truncTail h0 hle) (by positivity)

/-- The squared error is measurable. -/
theorem aestronglyMeasurable_germ_sub_trunc_sq {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (N : ℕ) :
    AEStronglyMeasurable (fun θ : ℝ => ‖phaseGerm s θ - dirichletTrunc s N θ‖ ^ 2)
      (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
  (((aestronglyMeasurable_phaseGerm h0 h1).sub
    (continuous_dirichletTrunc s N).aestronglyMeasurable).norm.pow 2)

/-- The squared error is integrable. -/
theorem integrableOn_germ_sub_trunc_sq {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) (N : ℕ) :
    IntegrableOn (fun θ : ℝ => ‖phaseGerm s θ - dirichletTrunc s N θ‖ ^ 2)
      (Ioc (-Real.pi) Real.pi) := by
  have h0' : (0 : ℝ) < s.re := by linarith
  refine ⟨aestronglyMeasurable_germ_sub_trunc_sq h0' h1 N, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  have hcongr : (∫⁻ θ in Ioc (-Real.pi) Real.pi,
      ‖‖phaseGerm s θ - dirichletTrunc s N θ‖ ^ 2‖ₑ)
      = ∫⁻ θ in Ioc (-Real.pi) Real.pi,
        ENNReal.ofReal (‖phaseGerm s θ - dirichletTrunc s N θ‖ ^ 2) := by
    refine lintegral_congr fun θ => ?_
    rw [← ofReal_norm, Real.norm_of_nonneg (by positivity)]
  rw [hcongr]
  exact lt_of_le_of_lt (lintegral_germ_sub_trunc_le h0 h1 N) ENNReal.ofReal_lt_top

/-- **The `L²` error bound.** -/
theorem integral_germ_sub_trunc_le {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) (N : ℕ) :
    (∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ - dirichletTrunc s N θ‖ ^ 2)
      ≤ 2 * Real.pi * truncTail s N := by
  have h0' : (0 : ℝ) < s.re := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc (-Real.pi) Real.pi)]
      fun θ : ℝ => ‖phaseGerm s θ - dirichletTrunc s N θ‖ ^ 2 :=
    Filter.Eventually.of_forall fun θ => by positivity
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnn
    (aestronglyMeasurable_germ_sub_trunc_sq h0' h1 N)]
  have hbound := lintegral_germ_sub_trunc_le h0 h1 N
  have hle : (∫⁻ θ in Ioc (-Real.pi) Real.pi,
      ENNReal.ofReal (‖phaseGerm s θ - dirichletTrunc s N θ‖ ^ 2)).toReal
      ≤ (ENNReal.ofReal (2 * Real.pi * truncTail s N)).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  refine hle.trans (le_of_eq ?_)
  refine ENNReal.toReal_ofReal ?_
  have := truncTail_nonneg s N
  positivity

/-- **The truncations converge to the germ in `L²`.** -/
theorem tendsto_integral_germ_sub_trunc {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) :
    Tendsto (fun N : ℕ =>
      ∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ - dirichletTrunc s N θ‖ ^ 2)
      atTop (𝓝 0) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmaj : Tendsto (fun N : ℕ => 2 * Real.pi * truncTail s N) atTop (𝓝 0) := by
    have := (tendsto_truncTail s).const_mul (2 * Real.pi)
    rw [mul_zero] at this
    exact this
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => ?_) ?_ hmaj
  · exact integral_nonneg fun θ => by positivity
  · exact Filter.Eventually.of_forall fun N => integral_germ_sub_trunc_le h0 h1 N

/-- Truncations are square integrable on the window. -/
theorem memLp_dirichletTrunc (s : ℂ) (N : ℕ) :
    MemLp (dirichletTrunc s N) 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
  refine (memLp_two_iff_integrable_sq_norm
    (continuous_dirichletTrunc s N).aestronglyMeasurable).mpr ?_
  exact ((continuous_dirichletTrunc s N).norm.pow 2).integrableOn_Ioc

theorem memLp_germ_sub_trunc {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) (N : ℕ) :
    MemLp (fun θ : ℝ => phaseGerm s θ - dirichletTrunc s N θ) 2
      (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
  have h0' : (0 : ℝ) < s.re := by linarith
  refine (memLp_two_iff_integrable_sq_norm
    ((aestronglyMeasurable_phaseGerm h0' h1).sub
      (continuous_dirichletTrunc s N).aestronglyMeasurable)).mpr ?_
  exact integrableOn_germ_sub_trunc_sq h0 h1 N

/-- Cauchy--Schwarz against a square-integrable factor. -/
theorem integral_norm_mul_le {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hg : MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) :
    (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖ * ‖g θ‖)
      ≤ (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))
        * (∫ θ in Ioc (-Real.pi) Real.pi, ‖g θ‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    constructor <;> norm_num
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    simpa using hf
  have hg' : MemLp g (ENNReal.ofReal (2 : ℝ)) (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
    simpa using hg
  exact MeasureTheory.integral_mul_norm_le_Lp_mul_Lq hpq hf' hg'

/-- Cauchy--Schwarz in square-root form. -/
theorem integral_norm_mul_le_sqrt {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hg : MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) :
    (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖ * ‖g θ‖)
      ≤ Real.sqrt (∫ θ in Ioc (-Real.pi) Real.pi, ‖f θ‖ ^ 2)
        * Real.sqrt (∫ θ in Ioc (-Real.pi) Real.pi, ‖g θ‖ ^ 2) := by
  have h := integral_norm_mul_le hf hg
  have hrw : ∀ u : ℝ → ℂ, (∫ θ in Ioc (-Real.pi) Real.pi, ‖u θ‖ ^ (2 : ℝ))
      = ∫ θ in Ioc (-Real.pi) Real.pi, ‖u θ‖ ^ 2 := by
    intro u
    refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only []
    rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hrw f, hrw g] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact h

/-- The real form of the truncation norm. -/
theorem integral_dirichletTrunc_normSq_real (s : ℂ) (N : ℕ) :
    (∫ θ in Ioc (-Real.pi) Real.pi, ‖dirichletTrunc s N θ‖ ^ 2)
      = 2 * Real.pi * ∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ (-2 * s.re) := by
  have hcx := integral_dirichletTrunc_normSq s N
  have hint : (∫ θ in Ioc (-Real.pi) Real.pi,
      dirichletTrunc s N θ * (starRingEnd ℂ) (dirichletTrunc s N θ))
      = (((∫ θ in Ioc (-Real.pi) Real.pi, ‖dirichletTrunc s N θ‖ ^ 2 : ℝ)) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hint] at hcx
  have hrhs : (2 : ℂ) * ↑Real.pi * ∑ i ∈ Finset.range N,
      ((((i : ℝ) + 1) ^ (-2 * s.re) : ℝ) : ℂ)
      = (((2 * Real.pi * ∑ i ∈ Finset.range N, ((i : ℝ) + 1) ^ (-2 * s.re) : ℝ)) : ℂ) := by
    push_cast
    ring
  rw [hrhs] at hcx
  exact_mod_cast hcx

theorem integral_dirichletTrunc_normSq_le {s : ℂ} (h0 : 1 / 2 < s.re) (N : ℕ) :
    (∫ θ in Ioc (-Real.pi) Real.pi, ‖dirichletTrunc s N θ‖ ^ 2)
      ≤ 2 * Real.pi * ∑' i : ℕ, ((i : ℝ) + 1) ^ (-2 * s.re) := by
  rw [integral_dirichletTrunc_normSq_real]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact (summable_truncMajorant h0).sum_le_tsum _
    (fun i _ => Real.rpow_nonneg (by positivity) _)

/-- Products of square-integrable functions are integrable on the window. -/
theorem integrable_norm_mul {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc (-Real.pi) Real.pi)))
    (hg : MemLp g 2 (volume.restrict (Ioc (-Real.pi) Real.pi))) :
    IntegrableOn (fun θ : ℝ => ‖f θ‖ * ‖g θ‖) (Ioc (-Real.pi) Real.pi) := by
  have h := MeasureTheory.MemLp.integrable_mul hf.norm hg.norm
  exact h

/-- **The heat quadratic form passes to the `L²` limit.** -/
theorem tendsto_heatIntegral_trunc {s : ℂ} (h0 : 1 / 2 < s.re) (h1 : s.re < 1) {x : ℝ}
    (hx : 0 < x) :
    Tendsto (fun N : ℕ => ∫ θ in Ioc (-Real.pi) Real.pi,
        heatMultiplier x θ * (dirichletTrunc s N θ * (starRingEnd ℂ) (dirichletTrunc s N θ)))
      atTop (𝓝 (∫ θ in Ioc (-Real.pi) Real.pi,
        heatMultiplier x θ * (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ)))) := by
  have h0' : (0 : ℝ) < s.re := by linarith
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-Real.pi)) (b := Real.pi)).exists_bound_of_continuousOn
    ((continuous_heatMultiplier hx).continuousOn)
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨by linarith, hpi.le⟩)
  set Ag : ℝ := Real.sqrt (∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ‖ ^ 2) with hAg
  set Bt : ℝ := Real.sqrt (2 * Real.pi * ∑' i : ℕ, ((i : ℝ) + 1) ^ (-2 * s.re)) with hBt
  set eps : ℕ → ℝ := fun N =>
    Real.sqrt (∫ θ in Ioc (-Real.pi) Real.pi, ‖phaseGerm s θ - dirichletTrunc s N θ‖ ^ 2)
    with heps
  have hAg0 : 0 ≤ Ag := Real.sqrt_nonneg _
  have hBt0 : 0 ≤ Bt := Real.sqrt_nonneg _
  have hepslim : Tendsto eps atTop (𝓝 0) := by
    have h2 := (Real.continuous_sqrt.tendsto 0).comp (tendsto_integral_germ_sub_trunc h0 h1)
    rw [Real.sqrt_zero] at h2
    exact h2
  have hkey : ∀ N : ℕ, ‖(∫ θ in Ioc (-Real.pi) Real.pi,
      heatMultiplier x θ * (dirichletTrunc s N θ * (starRingEnd ℂ) (dirichletTrunc s N θ)))
      - (∫ θ in Ioc (-Real.pi) Real.pi,
        heatMultiplier x θ * (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ)))‖
      ≤ M * (eps N * (Bt + Ag)) := by
    intro N
    set u : ℝ → ℂ := fun θ => phaseGerm s θ - dirichletTrunc s N θ with hu
    have hmemu : MemLp u 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
      memLp_germ_sub_trunc h0 h1 N
    have hmemt : MemLp (dirichletTrunc s N) 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
      memLp_dirichletTrunc s N
    have hmemg : MemLp (phaseGerm s) 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
      memLp_phaseGerm h0 h1
    have hint1 : IntegrableOn (fun θ : ℝ =>
        heatMultiplier x θ * (dirichletTrunc s N θ * (starRingEnd ℂ) (dirichletTrunc s N θ)))
        (Ioc (-Real.pi) Real.pi) := by
      refine ((continuous_heatMultiplier hx).mul
        ((continuous_dirichletTrunc s N).mul
          (Complex.continuous_conj.comp (continuous_dirichletTrunc s N)))).integrableOn_Ioc
    have hint2 : IntegrableOn (fun θ : ℝ =>
        heatMultiplier x θ * (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ)))
        (Ioc (-Real.pi) Real.pi) := by
      refine ((integrableOn_germSq_mul_heatMultiplier h0 h1 hx).congr ?_)
      filter_upwards with θ
      ring
    rw [← MeasureTheory.integral_sub hint1 hint2]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hptw : ∀ θ ∈ Ioc (-Real.pi) Real.pi,
        ‖heatMultiplier x θ * (dirichletTrunc s N θ * (starRingEnd ℂ) (dirichletTrunc s N θ))
          - heatMultiplier x θ * (phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ))‖
        ≤ M * (‖u θ‖ * ‖dirichletTrunc s N θ‖) + M * (‖u θ‖ * ‖phaseGerm s θ‖) := by
      intro θ hθ
      have hmem : θ ∈ Icc (-Real.pi) Real.pi := ⟨hθ.1.le, hθ.2⟩
      have hid : dirichletTrunc s N θ * (starRingEnd ℂ) (dirichletTrunc s N θ)
          - phaseGerm s θ * (starRingEnd ℂ) (phaseGerm s θ)
          = (-u θ) * (starRingEnd ℂ) (dirichletTrunc s N θ)
            + phaseGerm s θ * (starRingEnd ℂ) (-u θ) := by
        rw [hu]
        simp only [map_sub, map_neg]
        ring
      rw [← mul_sub, hid, norm_mul]
      have hb := hM θ hmem
      have hstep : ‖(-u θ) * (starRingEnd ℂ) (dirichletTrunc s N θ)
          + phaseGerm s θ * (starRingEnd ℂ) (-u θ)‖
          ≤ ‖u θ‖ * ‖dirichletTrunc s N θ‖ + ‖u θ‖ * ‖phaseGerm s θ‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj, norm_neg]
        exact le_of_eq (by ring)
      have hnn : (0 : ℝ) ≤ ‖u θ‖ * ‖dirichletTrunc s N θ‖ + ‖u θ‖ * ‖phaseGerm s θ‖ := by
        positivity
      calc ‖heatMultiplier x θ‖ * ‖(-u θ) * (starRingEnd ℂ) (dirichletTrunc s N θ)
            + phaseGerm s θ * (starRingEnd ℂ) (-u θ)‖
          ≤ M * (‖u θ‖ * ‖dirichletTrunc s N θ‖ + ‖u θ‖ * ‖phaseGerm s θ‖) := by
            exact mul_le_mul hb hstep (norm_nonneg _) hM0
        _ = M * (‖u θ‖ * ‖dirichletTrunc s N θ‖) + M * (‖u θ‖ * ‖phaseGerm s θ‖) := by ring
    have hmajint : IntegrableOn (fun θ : ℝ =>
        M * (‖u θ‖ * ‖dirichletTrunc s N θ‖) + M * (‖u θ‖ * ‖phaseGerm s θ‖))
        (Ioc (-Real.pi) Real.pi) :=
      ((integrable_norm_mul hmemu hmemt).const_mul M).add
        ((integrable_norm_mul hmemu hmemg).const_mul M)
    have hmono := MeasureTheory.setIntegral_mono_on (hint1.sub hint2).norm hmajint
      measurableSet_Ioc hptw
    refine hmono.trans ?_
    rw [MeasureTheory.integral_add ((integrable_norm_mul hmemu hmemt).const_mul M)
      ((integrable_norm_mul hmemu hmemg).const_mul M),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    have hcs1 := integral_norm_mul_le_sqrt hmemu hmemt
    have hcs2 := integral_norm_mul_le_sqrt hmemu hmemg
    have hbt : Real.sqrt (∫ θ in Ioc (-Real.pi) Real.pi, ‖dirichletTrunc s N θ‖ ^ 2) ≤ Bt := by
      rw [hBt]
      exact Real.sqrt_le_sqrt (integral_dirichletTrunc_normSq_le h0 N)
    have hepsN : eps N = Real.sqrt (∫ θ in Ioc (-Real.pi) Real.pi, ‖u θ‖ ^ 2) := by
      rw [heps, hu]
    have h1' : (∫ θ in Ioc (-Real.pi) Real.pi, ‖u θ‖ * ‖dirichletTrunc s N θ‖)
        ≤ eps N * Bt := by
      rw [hepsN]
      refine hcs1.trans ?_
      exact mul_le_mul_of_nonneg_left hbt (Real.sqrt_nonneg _)
    have h2' : (∫ θ in Ioc (-Real.pi) Real.pi, ‖u θ‖ * ‖phaseGerm s θ‖) ≤ eps N * Ag := by
      rw [hepsN, hAg]
      exact hcs2
    nlinarith [h1', h2', hM0]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hmaj : Tendsto (fun N : ℕ => M * (eps N * (Bt + Ag))) atTop (𝓝 0) := by
    have := (hepslim.mul_const (Bt + Ag)).const_mul M
    simpa using this
  exact squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _)
    (Filter.Eventually.of_forall hkey) hmaj

end RHTower
