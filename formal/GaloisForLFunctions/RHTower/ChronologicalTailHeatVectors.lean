import GaloisForLFunctions.RHTower.ChronologicalTailSampleSpace
import GaloisForLFunctions.RHTower.ChronologicalTailKernelLipschitz
import GaloisForLFunctions.RHTower.ChronologicalTailRiemann
import GaloisForLFunctions.RHTower.ChronologicalTailInjectivity
import GaloisForLFunctions.RHTower.ChronologicalHeatL2

/-!
# The tail heat vectors in `L²([1, 2])`

For `0 < θ < 1`, a profile `g` on `[θ, 1]` and `N ≥ 1` put

* `F_g(u) = ∫_θ¹ g(x) h(xu) dx` (the tail heat transform, `tailVec`),
* `F_{g,N}(u) = N⁻¹ Σ_{θN < k ≤ N} g(k/N) h(ku/N)` (its discrete tail, `tailSampleVec`),
* `K_ρ(u) = ∫_0^θ x^{ρ-1} h(xu) dx` (the critical vector, `critVec`),

as vectors of `L²([1, 2])`.

* For Lipschitz `g`, `‖F_{g,N} - F_g‖ = O(1/N)` (first-order Riemann sums).
* If the restrictions of `g₁, …, g_l` to `[θ, 1]` are linearly independent, so are the vectors
  `F_{g_i}` over `ℂ` (injectivity of the heat transform on continuous profiles).
* For `Re ρ = 1/2`, the critical vector lies outside the complex span of any finite family of
  tail vectors of continuous profiles (heat-transform separation).
-/

open MeasureTheory Set Filter Complex
open scoped Topology
open GaloisForLFunctions.HTGeometry.ChronologicalTensor

noncomputable section

namespace RHTower

/-! ### The tail heat transform on the positive axis -/

/-- The tail heat transform `F_G(u) = ∫_θ¹ G(x) h(xu) dx`. -/
def tailHeat (θ : ℝ) (G : ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ x in θ..1, G x * ((fusionBoseDefect (x * u) : ℝ) : ℂ)

theorem boseTransform_tailProfile_ofReal {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (G : ℝ → ℂ)
    {u : ℝ} (hu : 0 < u) : boseTransform (tailProfile θ G) (u : ℂ) = tailHeat θ G u := by
  rw [boseTransform_ofReal _ hu]
  have hfun : (fun x : ℝ => tailProfile θ G x * ((fusionBoseDefect (x * u) : ℝ) : ℂ)) =
      (Ici θ).indicator (fun x => G x * ((fusionBoseDefect (x * u) : ℝ) : ℂ)) := by
    funext x
    by_cases hx : θ ≤ x
    · rw [tailProfile, if_pos hx, Set.indicator_of_mem (show x ∈ Ici θ from hx)]
    · rw [tailProfile, if_neg hx, zero_mul, Set.indicator_of_notMem (show x ∉ Ici θ from hx)]
  have hset : Ioo (0 : ℝ) 1 ∩ Ici θ = Ico θ 1 := by
    ext x
    simp only [mem_inter_iff, mem_Ioo, mem_Ici, mem_Ico]
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨⟨by linarith, h1⟩, h2⟩
  rw [hfun, setIntegral_indicator measurableSet_Ici, hset, integral_Ico_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, tailHeat, intervalIntegral.integral_of_le hθ1.le]

/-- The extension of `G` by zero off `[θ, 1]`. -/
def tailCut (θ : ℝ) (G : ℝ → ℂ) : ℝ → ℂ := (Icc θ 1).indicator G

theorem measurable_tailCut {θ : ℝ} {G : ℝ → ℂ} (hG : ContinuousOn G (Icc θ 1)) :
    Measurable (tailCut θ G) := by
  classical
  rw [tailCut, ← Set.piecewise_eq_indicator]
  exact hG.measurable_piecewise continuousOn_const measurableSet_Icc

theorem exists_bound_tailCut {θ : ℝ} {G : ℝ → ℂ} (hG : ContinuousOn G (Icc θ 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖tailCut θ G x‖ ≤ C := by
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hG
  refine ⟨max C₀ 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc θ 1
  · rw [tailCut, Set.indicator_of_mem hx]; exact (hC₀ x hx).trans (le_max_left _ _)
  · rw [tailCut, Set.indicator_of_notMem hx, norm_zero]; exact le_max_right _ _

theorem tailHeat_tailCut {θ : ℝ} (hθ1 : θ ≤ 1) (G : ℝ → ℂ) (u : ℝ) :
    tailHeat θ (tailCut θ G) u = tailHeat θ G u := by
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le hθ1] at hx
  simp only [tailCut, Set.indicator_of_mem hx]

theorem integrableOn_tailProfile_tailCut {θ : ℝ} {G : ℝ → ℂ} (hG : ContinuousOn G (Icc θ 1)) :
    IntegrableOn (tailProfile θ (tailCut θ G)) (Ioo (0 : ℝ) 1) := by
  obtain ⟨C, hC0, hCb⟩ := exists_bound_tailCut hG
  exact Measure.integrableOn_of_bounded (M := C) (by rw [Real.volume_Ioo]; simp)
    (measurable_tailProfile θ (measurable_tailCut hG)).aestronglyMeasurable
    (Eventually.of_forall (norm_tailProfile_le hC0 hCb))

theorem continuousOn_boseTransform_ofReal {g : ℝ → ℂ} (hg : IntegrableOn g (Ioo (0 : ℝ) 1)) :
    ContinuousOn (fun u : ℝ => boseTransform g (u : ℂ)) (Ioi 0) :=
  (analyticOnNhd_boseTransform hg).continuousOn.comp Complex.continuous_ofReal.continuousOn
    fun _u hu => ofReal_mem_boseDomain hu

theorem continuousOn_tailHeat {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {G : ℝ → ℂ}
    (hG : ContinuousOn G (Icc θ 1)) : ContinuousOn (tailHeat θ G) (Ioi 0) :=
  (continuousOn_boseTransform_ofReal (integrableOn_tailProfile_tailCut hG)).congr fun u hu => by
    beta_reduce
    rw [boseTransform_tailProfile_ofReal hθ0 hθ1 _ hu, tailHeat_tailCut hθ1.le]

theorem continuousOn_bose_comp_mul {s : Set ℝ} {u : ℝ} (hu : 0 < u) (hs : s ⊆ Ioi 0) :
    ContinuousOn (fun x : ℝ => ((fusionBoseDefect (x * u) : ℝ) : ℂ)) s :=
  Complex.continuous_ofReal.comp_continuousOn
    (chronologicalBose_continuousOn.comp (continuousOn_id.mul continuousOn_const)
      fun _ hx => mul_pos (hs hx) hu)

theorem intervalIntegrable_tailHeat_integrand {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {G : ℝ → ℂ}
    (hG : ContinuousOn G (Icc θ 1)) {u : ℝ} (hu : 0 < u) :
    IntervalIntegrable (fun x => G x * ((fusionBoseDefect (x * u) : ℝ) : ℂ)) volume θ 1 := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [uIcc_of_le hθ1]
  exact hG.mul (continuousOn_bose_comp_mul hu fun x hx => hθ0.trans_le hx.1)

theorem tailHeat_sum {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {l : ℕ} (c : Fin l → ℂ)
    {G : Fin l → ℝ → ℂ} (hG : ∀ i, ContinuousOn (G i) (Icc θ 1)) {u : ℝ} (hu : 0 < u) :
    ∑ i, c i * tailHeat θ (G i) u = tailHeat θ (fun x => ∑ i, c i * G i x) u := by
  simp only [tailHeat]
  calc ∑ i, c i * ∫ x in θ..1, G i x * ((fusionBoseDefect (x * u) : ℝ) : ℂ)
      = ∑ i, ∫ x in θ..1, c i * (G i x * ((fusionBoseDefect (x * u) : ℝ) : ℂ)) := by
        simp only [intervalIntegral.integral_const_mul]
    _ = ∫ x in θ..1, ∑ i, c i * (G i x * ((fusionBoseDefect (x * u) : ℝ) : ℂ)) :=
        (intervalIntegral.integral_finsetSum fun i _ =>
          (intervalIntegrable_tailHeat_integrand hθ0 hθ1 (hG i) hu).const_mul (c i)).symm
    _ = _ := intervalIntegral.integral_congr fun x _ => by
        simp only [Finset.sum_mul, mul_assoc]

/-! ### The vectors -/

/-- The tail heat vector `F_g ∈ L²([1, 2])`. -/
def tailVec (θ : ℝ) (g : ℝ → ℝ) : SampleSpace := toSample (tailHeat θ fun x => (g x : ℂ))

/-- The critical vector `K_ρ ∈ L²([1, 2])`. -/
def critVec (θ : ℝ) (ρ : ℂ) : SampleSpace :=
  toSample fun u : ℝ => boseTransform (criticalProfile θ ρ) (u : ℂ)

/-- The discrete tail `F_{g,N}(u) = N⁻¹ Σ_{θN < k ≤ N} g(k/N) h(ku/N)`. -/
def tailSampleFun (θ : ℝ) (N : ℕ) (g : ℝ → ℝ) (u : ℝ) : ℂ :=
  (1 / (N : ℂ)) * tailSampleSum θ N fun x => (g x : ℂ) * ((fusionBoseDefect (x * u) : ℝ) : ℂ)

/-- The discrete tail vector `F_{g,N} ∈ L²([1, 2])`. -/
def tailSampleVec (θ : ℝ) (N : ℕ) (g : ℝ → ℝ) : SampleSpace := toSample (tailSampleFun θ N g)

theorem Icc_one_two_subset_Ioi : Icc (1 : ℝ) 2 ⊆ Ioi 0 := fun _ hu => lt_of_lt_of_le one_pos hu.1

theorem integrableOn_criticalProfile {θ : ℝ} {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    IntegrableOn (criticalProfile θ ρ) (Ioo (0 : ℝ) 1) :=
  integrableOn_of_weight (measurable_criticalProfile θ ρ) le_rfl
    (integrableOn_criticalProfile_weight (s := 0) (by rw [hρ]; norm_num))

theorem continuousOn_critFun {θ : ℝ} {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ContinuousOn (fun u : ℝ => boseTransform (criticalProfile θ ρ) (u : ℂ)) (Icc 1 2) :=
  (continuousOn_boseTransform_ofReal (integrableOn_criticalProfile hρ)).mono
    Icc_one_two_subset_Ioi

theorem memLp_tailHeat {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {G : ℝ → ℂ}
    (hG : ContinuousOn G (Icc θ 1)) : MemLp (tailHeat θ G) 2 sampleMeasure :=
  memLp_sample_of_continuousOn ((continuousOn_tailHeat hθ0 hθ1 hG).mono Icc_one_two_subset_Ioi)

/-- The embedded Bose dilate `u ↦ h(cu)`; bounded by one. -/
theorem memLp_sample_bose (c : ℝ) :
    MemLp (fun u : ℝ => ((fusionBoseDefect (c * u) : ℝ) : ℂ)) 2 sampleMeasure :=
  memLp_sample_of_bound
    (Complex.measurable_ofReal.comp
      (measurable_fusionBoseDefect.comp (measurable_const.mul measurable_id))).aestronglyMeasurable
    fun u _ => by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (fusionBoseDefect_bounds _).1]
      exact (fusionBoseDefect_bounds _).2.1

theorem memLp_tailSampleFun (θ : ℝ) (N : ℕ) (g : ℝ → ℝ) :
    MemLp (tailSampleFun θ N g) 2 sampleMeasure := by
  have hterm : ∀ k : ℕ, MemLp (fun u : ℝ => if θ * N < k then (g (k / N) : ℂ) *
      ((fusionBoseDefect (k / N * u) : ℝ) : ℂ) else 0) 2 sampleMeasure := by
    intro k
    by_cases hk : θ * N < k
    · simp only [hk, if_true]
      exact (memLp_sample_bose _).const_mul _
    · simp only [hk, if_false]
      exact MemLp.zero'
  exact (memLp_finsetSum (Finset.Ioc 0 N) fun k _ => hterm k).const_mul (1 / (N : ℂ))

/-! ### The Riemann estimate -/

/-- **The discrete tail vectors converge at rate `1/N`.** -/
theorem exists_norm_tailSampleVec_sub_tailVec_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {g : ℝ → ℝ} {K : NNReal} (hg : LipschitzOnWith K g (Icc θ 1)) :
    ∃ C : ℝ, ∀ N : ℕ, 0 < N → ‖tailSampleVec θ N g - tailVec θ g‖ ≤ C / N := by
  obtain ⟨Lh, hLh0, hLh⟩ := exists_fusionBoseDefect_lipschitz
  obtain ⟨B₀, hB₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  set B := max B₀ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ x ∈ Icc θ 1, |g x| ≤ B := fun x hx =>
    (Real.norm_eq_abs _ ▸ hB₀ x hx).trans (le_max_left _ _)
  have hgc : ContinuousOn (fun x => (g x : ℂ)) (Icc θ 1) :=
    Complex.continuous_ofReal.comp_continuousOn hg.continuousOn
  refine ⟨B + (K + 2 * B * Lh), fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [tailSampleVec, tailVec, ← toSample_sub (memLp_tailSampleFun θ N g)
    (memLp_tailHeat hθ0 hθ1 hgc)]
  refine norm_toSample_le (by positivity) fun u hu => ?_
  have hu0 : 0 < u := lt_of_lt_of_le one_pos hu.1
  have hmem : ∀ x ∈ Icc θ 1, x * u ∈ Ioc (0 : ℝ) 2 := fun x hx =>
    ⟨mul_pos (hθ0.trans_le hx.1) hu0, by nlinarith [hx.2, hu.2, hθ0.trans_le hx.1]⟩
  set φ : ℝ → ℂ := fun x => (g x : ℂ) * ((fusionBoseDefect (x * u) : ℝ) : ℂ) with hφ
  have hφM : ∀ x ∈ Icc θ 1, ‖φ x‖ ≤ B := by
    intro x hx
    rw [hφ, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (fusionBoseDefect_bounds _).1]
    exact (mul_le_mul (hB x hx) (fusionBoseDefect_bounds _).2.1 (fusionBoseDefect_bounds _).1
      hB0).trans_eq (mul_one B)
  have hφL : ∀ x ∈ Icc θ 1, ∀ y ∈ Icc θ 1, ‖φ x - φ y‖ ≤ (K + 2 * B * Lh) * |x - y| := by
    intro x hx y hy
    have hsplit : φ x - φ y = (((g x - g y) * fusionBoseDefect (x * u) +
        g y * (fusionBoseDefect (x * u) - fusionBoseDefect (y * u)) : ℝ) : ℂ) := by
      rw [hφ]; push_cast; ring
    have hgxy : |g x - g y| ≤ K * |x - y| := by
      have := hg.dist_le_mul x hx y hy
      rwa [Real.dist_eq, Real.dist_eq] at this
    have hhxy : |fusionBoseDefect (x * u) - fusionBoseDefect (y * u)| ≤ Lh * (2 * |x - y|) := by
      refine (hLh _ (hmem x hx) _ (hmem y hy)).trans (mul_le_mul_of_nonneg_left ?_ hLh0)
      rw [← sub_mul, abs_mul, abs_of_pos hu0, mul_comm]
      exact mul_le_mul_of_nonneg_right hu.2 (abs_nonneg _)
    have hb := fusionBoseDefect_bounds (x * u)
    rw [hsplit, Complex.norm_real, Real.norm_eq_abs]
    calc |(g x - g y) * fusionBoseDefect (x * u) +
          g y * (fusionBoseDefect (x * u) - fusionBoseDefect (y * u))|
        ≤ |g x - g y| * |fusionBoseDefect (x * u)| +
          |g y| * |fusionBoseDefect (x * u) - fusionBoseDefect (y * u)| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ (K * |x - y|) * 1 + B * (Lh * (2 * |x - y|)) := by
          rw [abs_of_nonneg hb.1]
          exact add_le_add (mul_le_mul hgxy hb.2.1 hb.1 (by positivity))
            (mul_le_mul (hB y hy) hhxy (abs_nonneg _) hB0)
      _ = (K + 2 * B * Lh) * |x - y| := by ring
  have hint : IntervalIntegrable φ volume θ 1 :=
    intervalIntegrable_tailHeat_integrand hθ0 hθ1.le hgc hu0
  exact norm_tailSampleSum_sub_integral_le hθ0 hθ1 hφM hφL hint hN

/-! ### Linear independence and separation -/

theorem sum_smul_tailVec {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {l : ℕ} {g : Fin l → ℝ → ℝ}
    (hcont : ∀ i, ContinuousOn (g i) (Icc θ 1)) (c : Fin l → ℂ) :
    ∑ i, c i • tailVec θ (g i) = toSample (tailHeat θ fun x => ∑ i, c i * (g i x : ℂ)) := by
  have hgc : ∀ i, ContinuousOn (fun x => (g i x : ℂ)) (Icc θ 1) := fun i =>
    Complex.continuous_ofReal.comp_continuousOn (hcont i)
  have hm : ∀ i, MemLp (tailHeat θ fun x => (g i x : ℂ)) 2 sampleMeasure := fun i =>
    memLp_tailHeat hθ0 hθ1 (hgc i)
  calc ∑ i, c i • tailVec θ (g i)
      = ∑ i, toSample (c i • tailHeat θ fun x => (g i x : ℂ)) :=
        Finset.sum_congr rfl fun i _ => (toSample_smul (c i) (hm i)).symm
    _ = toSample (∑ i, c i • tailHeat θ fun x => (g i x : ℂ)) :=
        (toSample_sum _ fun i _ => (hm i).const_smul (c i)).symm
    _ = toSample (tailHeat θ fun x => ∑ i, c i * (g i x : ℂ)) := by
        refine toSample_congr fun u hu => ?_
        rw [Finset.sum_apply]
        simp only [Pi.smul_apply, smul_eq_mul]
        exact tailHeat_sum hθ0 hθ1.le c hgc (lt_of_lt_of_le one_pos hu.1)

/-- **Linear independence of the tail heat vectors.** -/
theorem linearIndependent_tailVec {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {l : ℕ}
    {g : Fin l → ℝ → ℝ} (hcont : ∀ i, ContinuousOn (g i) (Icc θ 1))
    (hind : ∀ c : Fin l → ℝ, (∀ x ∈ Icc θ 1, ∑ i, c i * g i x = 0) → c = 0) :
    LinearIndependent ℂ fun i => tailVec θ (g i) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set G : ℝ → ℂ := fun x => ∑ i, c i * (g i x : ℂ) with hGdef
  have hGc : ContinuousOn G (Icc θ 1) :=
    continuousOn_finsetSum _ fun i _ =>
      continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (hcont i))
  have hzero : EqOn (tailHeat θ G) 0 (Icc 1 2) :=
    eqOn_of_toSample_eq ((continuousOn_tailHeat hθ0 hθ1 hGc).mono Icc_one_two_subset_Ioi)
      continuousOn_const (by rw [← sum_smul_tailVec hθ0 hθ1 hcont, hc, toSample_zero])
  have hG0 : EqOn G 0 (Icc θ 1) :=
    eqOn_zero_of_boseTransform_tailProfile_eq_zero hθ0 hθ1 hGc fun t ht => by
      rw [boseTransform_tailProfile_ofReal hθ0 hθ1 _ (lt_of_lt_of_le one_pos ht.1)]
      exact hzero ht
  have hre := hind (fun i => (c i).re) fun x hx => by
    have := congrArg Complex.re (hG0 hx)
    simpa [hGdef, Complex.re_sum, Complex.mul_re] using this
  have him := hind (fun i => (c i).im) fun x hx => by
    have := congrArg Complex.im (hG0 hx)
    simpa [hGdef, Complex.im_sum, Complex.mul_im] using this
  intro i
  exact Complex.ext (by simpa using congrFun hre i) (by simpa using congrFun him i)

/-- **Separation.**  The critical vector is not in the span of finitely many tail vectors. -/
theorem critVec_not_mem_span {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {ρ : ℂ} (hρ : ρ.re = 1 / 2)
    {l : ℕ} {g : Fin l → ℝ → ℝ} (hcont : ∀ i, ContinuousOn (g i) (Icc θ 1)) :
    critVec θ ρ ∉ Submodule.span ℂ (Set.range fun i => tailVec θ (g i)) := by
  intro hmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  set G : ℝ → ℂ := fun x => ∑ i, c i * (g i x : ℂ) with hGdef
  have hGc : ContinuousOn G (Icc θ 1) :=
    continuousOn_finsetSum _ fun i _ =>
      continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn (hcont i))
  rw [sum_smul_tailVec hθ0 hθ1 hcont] at hc
  have heq := eqOn_of_toSample_eq ((continuousOn_tailHeat hθ0 hθ1 hGc).mono Icc_one_two_subset_Ioi)
    (continuousOn_critFun hρ) hc
  obtain ⟨C, hC0, hCb⟩ := exists_bound_tailCut hGc
  refine heatTransform_separation hθ0 hθ1 hρ hC0 (measurable_tailCut hGc) hCb fun t ht => ?_
  rw [boseTransform_tailProfile_ofReal hθ0 hθ1 _ (lt_of_lt_of_le one_pos ht.1),
    tailHeat_tailCut hθ1.le]
  exact (heq ht).symm

end RHTower
