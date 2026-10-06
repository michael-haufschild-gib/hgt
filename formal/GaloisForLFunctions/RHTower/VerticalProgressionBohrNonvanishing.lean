import GaloisForLFunctions.RHTower.VerticalProgressionBohrMoment

/-!
# Non-vanishing of `ζ` on vertical progressions restricted to Bohr sets

**Theorem** (`eventually_nonvanishingCount_ge`, `le_liminf_nonvanishingCount`). Let `α > 0`,
`β ∈ ℝ`, `θ ∈ ℝ^K`, `H` the closure of `ℤθ̄` in `𝕋^K` with Haar probability `μ_H`, and `U ⊆ 𝕋^K`
open. Then

`liminf_{T→∞} T^{−1} #{T ≤ ℓ ≤ 2T : ℓθ̄ ∈ U, ζ(½ + i(αℓ + β)) ≠ 0} ≥ μ_H(U)²/3`.

**Proof.** For a smooth `0 ≤ φ ≤ 1` supported in `[1, 2]`, a continuous `0 ≤ W ≤ 1` supported in
`U` and `0 < ϑ < ½`, Cauchy–Schwarz gives `|S₁(W)|² ≤ #{…} · S₂` (`normSq_bohrMoment_le_count`), with
`S₁(W)/T → (∫W dμ_H)(∫φ)` and `S₂/T → (∫φ)(1 + 1/ϑ)`. Hence the density is at least
`(∫W dμ_H)²(∫φ) ϑ/(1 + ϑ)`, and letting `W ↑ 1_U`, `φ ↑ 1_{[1,2]}`, `ϑ ↑ ½` gives `μ_H(U)²/3`.
-/

open Complex MeasureTheory Set Filter Topology UnitAddTorus
open scoped BigOperators

namespace RHTower.VerticalAP

noncomputable section

open BohrOrbit

variable {K : ℕ}

open Classical in
/-- `#{T ≤ ℓ ≤ 2T : ℓθ̄ ∈ U, ζ(½ + i(αℓ + β)) ≠ 0}`. -/
def nonvanishingCount (α β : ℝ) (θ : Fin K → ℝ) (U : Set (UnitAddTorus (Fin K))) (T : ℝ) : ℕ :=
  ((Finset.Icc ⌈T⌉ ⌊2 * T⌋).filter fun ℓ : ℤ =>
    orbitPt θ ℓ ∈ U ∧ riemannZeta (critPt (α * ℓ + β)) ≠ 0).card

/-- The complexification of a real continuous function. -/
def complexify (W : C(UnitAddTorus (Fin K), ℝ)) : C(UnitAddTorus (Fin K), ℂ) :=
  ⟨fun x => (W x : ℂ), Complex.continuous_ofReal.comp W.continuous⟩

/-- **Cauchy–Schwarz on the non-vanishing set** `|S₁(W)|² ≤ #{…} · S₂`. -/
theorem normSq_bohrMoment_le_count {φ : ℝ → ℝ} (hsupp : Function.support φ ⊆ Icc 1 2)
    (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∀ y, φ y ≤ 1) {W : C(UnitAddTorus (Fin K), ℝ)}
    (hW0 : ∀ x, 0 ≤ W x) (hW1 : ∀ x, W x ≤ 1) {U : Set (UnitAddTorus (Fin K))}
    (hWU : ∀ x, W x ≠ 0 → x ∈ U) (θ : Fin K → ℝ) (α β : ℝ) (N : ℕ) {T : ℝ} (hT : 0 < T) :
    ‖bohrMoment φ (complexify W) θ α β N T‖ ^ 2 ≤
      (nonvanishingCount α β θ U T : ℝ) * secondMoment φ α β N T := by
  classical
  set S := Finset.Icc ⌈T⌉ ⌊2 * T⌋
  set A := S.filter fun ℓ : ℤ => orbitPt θ ℓ ∈ U ∧ riemannZeta (critPt (α * ℓ + β)) ≠ 0
  set a : ℤ → ℂ := fun ℓ => (φ ((ℓ : ℝ) / T) : ℂ) * ((complexify W) (orbitPt θ ℓ) *
    apMollZeta N α β ℓ)
  have hsumA : bohrMoment φ (complexify W) θ α β N T = ∑ ℓ ∈ A, a ℓ := by
    rw [bohrMoment_eq_sum hsupp _ _ _ _ _ hT, Finset.sum_filter]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    split_ifs with h
    · rfl
    · rcases not_and_or.mp h with h | h
      · have : W (orbitPt θ ℓ) = 0 := by by_contra hne; exact h (hWU _ hne)
        simp [complexify, this]
      · push Not at h
        simp [apMollZeta, h]
  have hnorm : ∀ ℓ, ‖a ℓ‖ ^ 2 ≤ φ ((ℓ : ℝ) / T) * ‖apMollZeta N α β ℓ‖ ^ 2 := by
    intro ℓ
    simp only [a, complexify, ContinuousMap.coe_mk, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (hφ0 _), abs_of_nonneg (hW0 _)]
    have h0 := hφ0 ((ℓ : ℝ) / T)
    have h1 := hφ1 ((ℓ : ℝ) / T)
    have h2 := hW0 (orbitPt θ ℓ)
    have h3 := hW1 (orbitPt θ ℓ)
    have h4 := norm_nonneg (apMollZeta N α β ℓ)
    have : φ ((ℓ : ℝ) / T) * (W (orbitPt θ ℓ) * ‖apMollZeta N α β ℓ‖) ≤
        φ ((ℓ : ℝ) / T) * ‖apMollZeta N α β ℓ‖ := by
      have := mul_le_mul_of_nonneg_right h3 h4
      nlinarith
    calc (φ ((ℓ : ℝ) / T) * (W (orbitPt θ ℓ) * ‖apMollZeta N α β ℓ‖)) ^ 2
        ≤ (φ ((ℓ : ℝ) / T) * ‖apMollZeta N α β ℓ‖) ^ 2 := by
          gcongr
      _ = φ ((ℓ : ℝ) / T) * (φ ((ℓ : ℝ) / T) * ‖apMollZeta N α β ℓ‖ ^ 2) := by ring
      _ ≤ 1 * (φ ((ℓ : ℝ) / T) * ‖apMollZeta N α β ℓ‖ ^ 2) := by gcongr
      _ = _ := one_mul _
  rw [hsumA, secondMoment_eq_sum hsupp α β N hT]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq A (fun _ => (1 : ℝ)) (fun ℓ => ‖a ℓ‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hCS
  calc ‖∑ ℓ ∈ A, a ℓ‖ ^ 2 ≤ (∑ ℓ ∈ A, ‖a ℓ‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (A.card : ℝ) * ∑ ℓ ∈ A, ‖a ℓ‖ ^ 2 := hCS
    _ ≤ (A.card : ℝ) * ∑ ℓ ∈ S, φ ((ℓ : ℝ) / T) * ‖apMollZeta N α β ℓ‖ ^ 2 := by
        gcongr
        calc ∑ ℓ ∈ A, ‖a ℓ‖ ^ 2 ≤ ∑ ℓ ∈ A, φ ((ℓ : ℝ) / T) * ‖apMollZeta N α β ℓ‖ ^ 2 :=
              Finset.sum_le_sum fun ℓ _ => hnorm ℓ
          _ ≤ ∑ ℓ ∈ S, φ ((ℓ : ℝ) / T) * ‖apMollZeta N α β ℓ‖ ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                fun ℓ _ _ => mul_nonneg (hφ0 _) (by positivity)

/-- **The density from fixed test data.** -/
theorem eventually_count_ge_of_test {φ : ℝ → ℝ} (hφ : ∀ k : ℕ, ContDiff ℝ k φ)
    (hsupp : Function.support φ ⊆ Icc 1 2) (hφ0 : ∀ y, 0 ≤ φ y) (hφ1 : ∀ y, φ y ≤ 1)
    (hφpos : 0 < ∫ x, φ x) {W : C(UnitAddTorus (Fin K), ℝ)} (hW0 : ∀ x, 0 ≤ W x)
    (hW1 : ∀ x, W x ≤ 1) {U : Set (UnitAddTorus (Fin K))} (hWU : ∀ x, W x ≠ 0 → x ∈ U)
    (θ : Fin K → ℝ) {α β ϑ : ℝ} (hα : 0 < α) (hϑ0 : 0 < ϑ) (hϑ : ϑ < 1 / 2) {c : ℝ}
    (hc : c < (∫ x, W x ∂(orbitHaar θ)) ^ 2 * (∫ x, φ x) / (1 + 1 / ϑ)) :
    ∀ᶠ T : ℝ in atTop, c ≤ (nonvanishingCount α β θ U T : ℝ) / T := by
  set B : ℝ := ∫ x, φ x
  set I : ℝ := ∫ x, W x ∂(orbitHaar θ)
  have hS₁ := tendsto_bohrMoment_div hφ hsupp hφ0 θ (β := β) hα hϑ0 hϑ (complexify W)
  have hIC : ∫ x, (complexify W) x ∂(orbitHaar θ) = ((I : ℝ) : ℂ) := by
    simp only [complexify, ContinuousMap.coe_mk]
    exact integral_complex_ofReal
  rw [hIC] at hS₁
  have hS₂ := tendsto_secondMoment_div hφ hsupp (β := β) hα hϑ0 hϑ
  have hnum : Tendsto (fun T => ‖bohrMoment φ (complexify W) θ α β (molLen ϑ T) T / T‖ ^ 2)
      atTop (𝓝 ((I * B) ^ 2)) := by
    have h2 := ((continuous_norm.tendsto _).comp hS₁).pow 2
    have hv : ‖(I : ℂ) * ((∫ x, φ x : ℝ) : ℂ)‖ ^ 2 = (I * B) ^ 2 := by
      rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hv] at h2
    exact h2
  have hden : B * (1 + 1 / ϑ) ≠ 0 := by positivity
  have hratio := hnum.div hS₂ hden
  have hL : (I * B) ^ 2 / (B * (1 + 1 / ϑ)) = I ^ 2 * B / (1 + 1 / ϑ) := by
    field_simp
  rw [hL] at hratio
  filter_upwards [hratio.eventually (lt_mem_nhds hc), eventually_gt_atTop 0] with T hT hT0
  refine le_trans hT.le ?_
  simp only [Pi.div_apply]
  set S₁ := bohrMoment φ (complexify W) θ α β (molLen ϑ T) T
  set S₂ := secondMoment φ α β (molLen ϑ T) T
  have hCS := normSq_bohrMoment_le_count hsupp hφ0 hφ1 hW0 hW1 hWU θ α β (molLen ϑ T) hT0
  have hS₂0 : 0 ≤ S₂ := tsum_nonneg fun ℓ => mul_nonneg (hφ0 _) (by positivity)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  rcases hS₂0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_div, div_zero]; positivity
  · rw [div_pow, div_div_eq_mul_div, div_le_div_iff₀ hpos hT0]
    calc ‖S₁‖ ^ 2 / T ^ 2 * T * T = ‖S₁‖ ^ 2 := by field_simp
      _ ≤ (nonvanishingCount α β θ U T : ℝ) * S₂ := hCS
      _ = (nonvanishingCount α β θ U T : ℝ) * S₂ := rfl

/-! ## Approximation of the test data -/

/-- `W_n(x) = min(1, n · d(x, Uᶜ))`. -/
def openApprox (U : Set (UnitAddTorus (Fin K))) (n : ℕ) : C(UnitAddTorus (Fin K), ℝ) :=
  ⟨fun x => min 1 ((n : ℝ) * Metric.infDist x Uᶜ),
    continuous_const.min (continuous_const.mul (Metric.continuous_infDist_pt _))⟩

theorem openApprox_apply (U : Set (UnitAddTorus (Fin K))) (n : ℕ) (x : UnitAddTorus (Fin K)) :
    openApprox U n x = min 1 ((n : ℝ) * Metric.infDist x Uᶜ) := rfl

theorem openApprox_nonneg (U : Set (UnitAddTorus (Fin K))) (n : ℕ) (x : UnitAddTorus (Fin K)) :
    0 ≤ openApprox U n x := by
  rw [openApprox_apply]
  exact le_min zero_le_one (mul_nonneg (Nat.cast_nonneg n) Metric.infDist_nonneg)

theorem openApprox_eq_zero {U : Set (UnitAddTorus (Fin K))} (n : ℕ) {x : UnitAddTorus (Fin K)}
    (hx : x ∉ U) : openApprox U n x = 0 := by
  rw [openApprox_apply, Metric.infDist_zero_of_mem (Set.mem_compl hx), mul_zero]
  exact min_eq_right zero_le_one

/-- On an open set with nonempty complement, `W_n → 1_U` pointwise. -/
theorem tendsto_openApprox {U : Set (UnitAddTorus (Fin K))} (hU : IsOpen U) (hc : Uᶜ.Nonempty)
    (x : UnitAddTorus (Fin K)) :
    Tendsto (fun n => openApprox U n x) atTop (𝓝 (U.indicator 1 x)) := by
  by_cases hx : x ∈ U
  · rw [Set.indicator_of_mem hx, Pi.one_apply]
    have hd : 0 < Metric.infDist x Uᶜ := by
      rw [← Metric.infDist_pos_iff_notMem_closure hc, hU.isClosed_compl.closure_eq]
      exact fun h => h hx
    have hgrow : Tendsto (fun n : ℕ => (n : ℝ) * Metric.infDist x Uᶜ) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hd
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hgrow.eventually_ge_atTop 1] with n hn
    rw [openApprox_apply, min_eq_left hn]
  · rw [Set.indicator_of_notMem hx]
    exact tendsto_const_nhds.congr fun n => (openApprox_eq_zero n hx).symm

/-- **Inner approximation of an open set** by continuous `0 ≤ W ≤ 1` supported in it. -/
theorem exists_openApprox {U : Set (UnitAddTorus (Fin K))} (hU : IsOpen U)
    (μ : Measure (UnitAddTorus (Fin K))) [IsFiniteMeasure μ] :
    ∃ W : ℕ → C(UnitAddTorus (Fin K), ℝ), (∀ n x, 0 ≤ W n x) ∧ (∀ n x, W n x ≤ 1) ∧
      (∀ n x, W n x ≠ 0 → x ∈ U) ∧
      Tendsto (fun n => ∫ x, W n x ∂μ) atTop (𝓝 (μ U).toReal) := by
  by_cases hc : Uᶜ.Nonempty
  · refine ⟨openApprox U, openApprox_nonneg U, fun n x => min_le_left _ _,
      fun n x h => by_contra fun hx => h (openApprox_eq_zero n hx), ?_⟩
    have hlim := tendsto_integral_of_dominated_convergence (μ := μ) (F := fun n x => openApprox U n x)
      (f := U.indicator 1) (fun _ => 1)
      (fun n => (openApprox U n).continuous.aestronglyMeasurable) (integrable_const 1)
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (openApprox_nonneg U n x)]
        exact min_le_left _ _)
      (Eventually.of_forall (tendsto_openApprox hU hc))
    rwa [integral_indicator_one hU.measurableSet, measureReal_def] at hlim
  · have hU' : U = Set.univ := by
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hc
      exact hc
    refine ⟨fun _ => ContinuousMap.const _ 1, fun _ _ => zero_le_one, fun _ _ => le_rfl,
      fun _ x _ => hU' ▸ Set.mem_univ x, ?_⟩
    refine tendsto_const_nhds.congr fun n => ?_
    rw [hU']
    simp only [ContinuousMap.const_apply, integral_const, smul_eq_mul, mul_one, measureReal_def]

/-- A smooth bump `0 ≤ φ ≤ 1` supported in `(1, 2)` and equal to `1` on `[3/2 − r, 3/2 + r]`. -/
def plateau {r : ℝ} (h0 : 0 < r) (h1 : r < 1 / 2) : ContDiffBump (3 / 2 : ℝ) :=
  ⟨r, 1 / 2, h0, h1⟩

theorem plateau_support {r : ℝ} (h0 : 0 < r) (h1 : r < 1 / 2) :
    Function.support (plateau h0 h1 : ℝ → ℝ) ⊆ Icc 1 2 := by
  rw [ContDiffBump.support_eq, Real.ball_eq_Ioo]
  show Ioo (3 / 2 - 1 / 2) (3 / 2 + 1 / 2) ⊆ Icc 1 2
  norm_num
  exact Ioo_subset_Icc_self

theorem plateau_contDiff {r : ℝ} (h0 : 0 < r) (h1 : r < 1 / 2) (k : ℕ) :
    ContDiff ℝ k (plateau h0 h1 : ℝ → ℝ) :=
  (plateau h0 h1).contDiff (n := k)

theorem two_mul_le_integral_plateau {r : ℝ} (h0 : 0 < r) (h1 : r < 1 / 2) :
    2 * r ≤ ∫ x, (plateau h0 h1 : ℝ → ℝ) x := by
  set f := plateau h0 h1
  have hset : ∫ x in Metric.closedBall (3 / 2 : ℝ) f.rIn, f x = 2 * r := by
    rw [setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet
      (fun x hx => f.one_of_mem_closedBall hx), setIntegral_const,
      show f.rIn = r from rfl, Real.volume_real_closedBall h0.le, smul_eq_mul, mul_one]
  rw [← hset]
  exact setIntegral_le_integral f.integrable (Eventually.of_forall fun _ => f.nonneg)

/-- The parameter `r_n = 1/2 − 1/(n + 3) ∈ [1/6, 1/2)`. -/
def plateauRadius (n : ℕ) : ℝ := 1 / 2 - ((n : ℝ) + 3)⁻¹

theorem plateauRadius_pos (n : ℕ) : 0 < plateauRadius n := by
  unfold plateauRadius
  have : ((n : ℝ) + 3)⁻¹ ≤ 3⁻¹ :=
    inv_anti₀ (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  linarith

theorem plateauRadius_lt (n : ℕ) : plateauRadius n < 1 / 2 := by
  unfold plateauRadius
  have : 0 < ((n : ℝ) + 3)⁻¹ := by positivity
  linarith

theorem tendsto_plateauRadius : Tendsto plateauRadius atTop (𝓝 (1 / 2)) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 3)⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).inv_tendsto_atTop
  have := (tendsto_const_nhds (x := (1 / 2 : ℝ))).sub hinv
  rw [sub_zero] at this
  exact this

/-! ## The theorem -/

/-- **Non-vanishing on vertical progressions in Bohr sets**: for every `c < μ_H(U)²/3`, eventually
`c T ≤ #{T ≤ ℓ ≤ 2T : ℓθ̄ ∈ U, ζ(½ + i(αℓ + β)) ≠ 0}`. -/
theorem eventually_nonvanishingCount_ge {U : Set (UnitAddTorus (Fin K))} (hU : IsOpen U)
    (θ : Fin K → ℝ) {α : ℝ} (β : ℝ) (hα : 0 < α) {c : ℝ}
    (hc : c < (orbitHaar θ U).toReal ^ 2 / 3) :
    ∀ᶠ T : ℝ in atTop, c ≤ (nonvanishingCount α β θ U T : ℝ) / T := by
  obtain ⟨W, hW0, hW1, hWU, hlim⟩ := exists_openApprox hU (orbitHaar θ)
  set m := (orbitHaar θ U).toReal
  have hL : Tendsto (fun n => (∫ x, W n x ∂(orbitHaar θ)) ^ 2 * (2 * plateauRadius n) /
      (1 + 1 / plateauRadius n)) atTop (𝓝 (m ^ 2 * (2 * (1 / 2)) / (1 + 1 / (1 / 2)))) :=
    ((hlim.pow 2).mul (tendsto_plateauRadius.const_mul 2)).div
      (tendsto_const_nhds.add (tendsto_const_nhds.div tendsto_plateauRadius (by norm_num)))
      (by norm_num)
  have hval : m ^ 2 * (2 * (1 / 2)) / (1 + 1 / (1 / 2)) = m ^ 2 / 3 := by norm_num
  rw [hval] at hL
  obtain ⟨n, hn⟩ := (hL.eventually (lt_mem_nhds hc)).exists
  have h0 := plateauRadius_pos n
  have h1 := plateauRadius_lt n
  have hB := two_mul_le_integral_plateau h0 h1
  refine eventually_count_ge_of_test (plateau_contDiff h0 h1) (plateau_support h0 h1)
    (fun _ => ContDiffBump.nonneg _) (fun _ => ContDiffBump.le_one _) (by linarith) (hW0 n)
    (hW1 n) (hWU n) θ hα h0 h1 (lt_of_lt_of_le hn ?_)
  gcongr

theorem card_Icc_ceil_floor_le {T : ℝ} (hT : 0 ≤ T) :
    ((Finset.Icc ⌈T⌉ ⌊2 * T⌋).card : ℝ) ≤ T + 1 := by
  rw [Int.card_Icc]
  have h1 := Int.floor_le (2 * T)
  have h2 := Int.le_ceil T
  rcases le_or_gt 0 (⌊2 * T⌋ + 1 - ⌈T⌉) with h | h
  · have : (((⌊2 * T⌋ + 1 - ⌈T⌉).toNat : ℕ) : ℝ) = ((⌊2 * T⌋ + 1 - ⌈T⌉ : ℤ) : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h]
    rw [this]
    push_cast
    linarith
  · rw [Int.toNat_of_nonpos h.le, Nat.cast_zero]
    linarith

theorem nonvanishingCount_div_le (α β : ℝ) (θ : Fin K → ℝ) (U : Set (UnitAddTorus (Fin K)))
    {T : ℝ} (hT : 1 ≤ T) : (nonvanishingCount α β θ U T : ℝ) / T ≤ 2 := by
  classical
  have hcard : (nonvanishingCount α β θ U T : ℝ) ≤ ((Finset.Icc ⌈T⌉ ⌊2 * T⌋).card : ℝ) := by
    unfold nonvanishingCount
    exact_mod_cast Finset.card_filter_le _ _
  rw [div_le_iff₀ (by linarith)]
  linarith [card_Icc_ceil_floor_le (by linarith : (0 : ℝ) ≤ T)]

/-- **Theorem.** `liminf_{T→∞} T⁻¹ #{T ≤ ℓ ≤ 2T : ℓθ̄ ∈ U, ζ(½ + i(αℓ + β)) ≠ 0} ≥ μ_H(U)²/3`
for every open `U ⊆ 𝕋^K`, where `μ_H` is the Haar probability of `H = cl ℤθ̄`. -/
theorem le_liminf_nonvanishingCount {U : Set (UnitAddTorus (Fin K))} (hU : IsOpen U)
    (θ : Fin K → ℝ) {α : ℝ} (β : ℝ) (hα : 0 < α) :
    (orbitHaar θ U).toReal ^ 2 / 3 ≤
      liminf (fun T : ℝ => (nonvanishingCount α β θ U T : ℝ) / T) atTop := by
  have hcob : IsCoboundedUnder (· ≥ ·) atTop
      (fun T : ℝ => (nonvanishingCount α β θ U T : ℝ) / T) :=
    isCoboundedUnder_ge_of_eventually_le atTop (x := 2)
      (by filter_upwards [eventually_ge_atTop 1] with T hT
          exact nonvanishingCount_div_le α β θ U hT)
  exact le_of_forall_lt_imp_le_of_dense fun c hc =>
    le_liminf_of_le hcob (eventually_nonvanishingCount_ge hU θ β hα hc)

/-- **Positive density** whenever the open set `U` meets the orbit closure `H`. -/
theorem liminf_nonvanishingCount_pos {U : Set (UnitAddTorus (Fin K))} (hU : IsOpen U)
    (θ : Fin K → ℝ) (hUH : ∃ x ∈ U, x ∈ orbitSubgroup θ) {α : ℝ} (β : ℝ) (hα : 0 < α) :
    0 < liminf (fun T : ℝ => (nonvanishingCount α β θ U T : ℝ) / T) atTop := by
  have hpos : 0 < (orbitHaar θ U).toReal :=
    ENNReal.toReal_pos (orbitHaar_pos_of_isOpen θ hU hUH).ne' (measure_ne_top _ _)
  exact lt_of_lt_of_le (by positivity) (le_liminf_nonvanishingCount hU θ β hα)

open Classical in
theorem nonvanishingCount_univ (α β : ℝ) (θ : Fin K → ℝ) (T : ℝ) :
    nonvanishingCount α β θ Set.univ T = ((Finset.Icc ⌈T⌉ ⌊2 * T⌋).filter fun ℓ : ℤ =>
      riemannZeta (critPt (α * ℓ + β)) ≠ 0).card := by
  unfold nonvanishingCount
  congr 1
  ext ℓ
  simp

open Classical in
/-- **The case `U = 𝕋^K`** (Li–Radziwiłł): for every `α > 0` and `β`,
`liminf_{T→∞} T^{−1} #{T ≤ ℓ ≤ 2T : ζ(½ + i(αℓ + β)) ≠ 0} ≥ 1/3`. -/
theorem le_liminf_card_riemannZeta_ne_zero {α : ℝ} (β : ℝ) (hα : 0 < α) :
    1 / 3 ≤ liminf (fun T : ℝ => (((Finset.Icc ⌈T⌉ ⌊2 * T⌋).filter fun ℓ : ℤ =>
      riemannZeta (critPt (α * ℓ + β)) ≠ 0).card : ℝ) / T) atTop := by
  have h := le_liminf_nonvanishingCount (K := 0) isOpen_univ (fun i => i.elim0) β hα
  rw [measure_univ, ENNReal.toReal_one] at h
  simp only [nonvanishingCount_univ] at h
  norm_num at h ⊢
  exact h

end

end RHTower.VerticalAP
