import GaloisForLFunctions.EulerFETransportTheory.TheFullGaussianCurrentAtEscapingHeights
import GaloisForLFunctions.RHTower.DirichletLStripBounds

/-!
# Only exceptional Gaussian modes remain

A finite exceptional layer suffices for joint height/damping renormalization.
The complete complementary Gamma field is bounded by a positive power of
damping times logarithmic height. Its removal therefore retains uniform
control throughout a high strip in the actual finite-layer world.
-/

open Complex Filter Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- Gamma recursion bounds every undamped mode by the squared translated
resolvent, with one constant throughout the positive strip. -/
theorem exists_gaussianMode_unit_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ s : ℂ, 0 < s.re → s.re ≤ 1 → xi s ≠ 0 →
      ∀ q : XiZeroCopy, ‖gaussianMBKernel 1 (xiZero q - s)‖ ≤
        K * ‖(xiZero q - s)⁻¹‖ ^ 2 := by
  obtain ⟨B, hB, hb⟩ := exists_bound_norm_Gamma_strip (a := 1) (b := 3) zero_lt_one
  refine ⟨6 * B, by positivity, fun s hs0 hs1 hxi q => ?_⟩
  let a : ℂ := xiZero q - s
  have hq0 : 0 < (xiZero q).re := xiZeroCopy_re_pos q
  have hq1 : (xiZero q).re < 1 := xiZeroCopy_re_lt_one q
  have ha0 : a ≠ 0 := by
    intro hz
    exact hxi (by rw [← sub_eq_zero.mp hz]; exact xi_xiZero q)
  have ha2 : a + 2 ≠ 0 := by
    intro hz
    have hh := congrArg Complex.re hz
    dsimp [a] at hh
    simp at hh
    linarith
  have hh : a / 2 + 1 ≠ 0 := by
    intro hz
    have hh := congrArg Complex.re hz
    dsimp [a] at hh
    simp at hh
    linarith
  have hrec : Complex.Gamma (a / 2 + 2) =
      (a / 2 + 1) * (a / 2) * Complex.Gamma (a / 2) := by
    rw [show a / 2 + 2 = (a / 2 + 1) + 1 by ring,
      Complex.Gamma_add_one _ hh, Complex.Gamma_add_one _ (div_ne_zero ha0 two_ne_zero)]
  have hid : (1 / 2 : ℂ) * Complex.Gamma (a / 2) =
      2 * Complex.Gamma (a / 2 + 2) / (a * (a + 2)) := by
    rw [hrec]
    field_simp
    ring
  have hΓ : ‖Complex.Gamma (a / 2 + 2)‖ ≤ B := by
    apply hb
    · dsimp [a]; simp; linarith
    · dsimp [a]; simp; linarith
  simp only [gaussianMBKernel, Complex.ofReal_one, Complex.one_cpow, mul_one]
  change ‖(1 / 2 : ℂ) * Complex.Gamma (a / 2)‖ ≤ _
  rw [hid, norm_div, norm_mul, norm_mul, Complex.norm_two]
  calc
    _ ≤ 2 * B / (‖a‖ * ‖a + 2‖) := by gcongr
    _ = (2 * B) * (‖a⁻¹‖ * ‖(a + 2)⁻¹‖) := by
      simp only [norm_inv, div_eq_mul_inv, mul_inv, mul_assoc]
    _ ≤ (2 * B) * (3 * ‖a⁻¹‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (reciprocal_shift_product_le hs1 hxi q) (by positivity)
    _ = _ := by ring

/-- The raw prime current with only finitely many exceptional Gamma modes
removed, retaining the normalized continued finite part. -/
def finiteGaussianFinitePartError (F : Finset XiZeroCopy) (s : ℂ) (y : ℝ) : ℂ :=
  gaussianPrimeContinuumGap s y + (∑ q ∈ F, gaussianMBKernel y (xiZero q - s)) -
    (Real.exp (-y) : ℂ) * (gaussianArchimedeanCurrent s - logDeriv xi s)

private theorem finiteGaussianFinitePartError_eq (F : Finset XiZeroCopy)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re ≤ 1) (hxi : xi s ≠ 0) {y : ℝ} (hy : 0 < y) :
    finiteGaussianFinitePartError F s y = complexGaussianFinitePartError s y -
      ∑' q : {q : XiZeroCopy // q ∉ F}, gaussianMBKernel y (xiZero q - s) := by
  have h := ((summable_norm_complexGaussianModes hs0 hs1 hxi hy).of_norm).sum_add_tsum_subtype_compl F
  change (∑ q ∈ F, gaussianMBKernel y (xiZero q - s)) +
    (∑' q : {q : XiZeroCopy // q ∉ F}, gaussianMBKernel y (xiZero q - s)) =
      complexGaussianModes s y at h
  rw [finiteGaussianFinitePartError, complexGaussianFinitePartError, ← h]
  ring

/-- The infinite nonexceptional Gamma field has a damping-power gain. -/
private theorem norm_complementaryGaussianModes_le {K σ θ : ℝ}
    (hK : ∀ s : ℂ, 0 < s.re → s.re ≤ 1 → xi s ≠ 0 → ∀ q : XiZeroCopy,
      ‖gaussianMBKernel 1 (xiZero q - s)‖ ≤ K * ‖(xiZero q - s)⁻¹‖ ^ 2)
    (hK0 : 0 < K) (F : Finset XiZeroCopy)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re ≤ 1) (hsσ : σ ≤ s.re) (hxi : xi s ≠ 0)
    {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ‖∑' q : {q : XiZeroCopy // q ∉ F}, gaussianMBKernel y (xiZero q - s)‖ ≤
      K * y ^ ((σ - θ) / 2) * ∑' q : XiZeroCopy, ‖(xiZero q - s)⁻¹‖ ^ 2 := by
  have hmode : ∀ q : {q : XiZeroCopy // q ∉ F},
      ‖gaussianMBKernel y (xiZero q - s)‖ ≤
        K * y ^ ((σ - θ) / 2) * ‖(xiZero q - s)⁻¹‖ ^ 2 := by
    intro q
    have hp : y ^ (-((xiZero q - s) / 2)).re ≤ y ^ ((σ - θ) / 2) := by
      apply Real.rpow_le_rpow_of_exponent_ge hy hy1
      simp only [Complex.neg_re, Complex.div_ofNat_re, Complex.sub_re]
      linarith [hrest q q.property]
    have he : ‖gaussianMBKernel y (xiZero q - s)‖ =
        ‖gaussianMBKernel 1 (xiZero q - s)‖ * y ^ (-((xiZero q - s) / 2)).re := by
      simp only [gaussianMBKernel, Complex.ofReal_one, Complex.one_cpow, mul_one]
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
    rw [he]
    calc
      _ ≤ (K * ‖(xiZero q - s)⁻¹‖ ^ 2) * y ^ ((σ - θ) / 2) :=
        mul_le_mul (hK s hs0 hs1 hxi q) hp (by positivity) (by positivity)
      _ = _ := by ring
  have hv := summable_norm_inv_xiZero_sub_sq s
  have hvle : (∑' q : {q : XiZeroCopy // q ∉ F}, ‖(xiZero q - s)⁻¹‖ ^ 2) ≤
      ∑' q : XiZeroCopy, ‖(xiZero q - s)⁻¹‖ ^ 2 := by
    have hsplit := hv.sum_add_tsum_subtype_compl F
    have hpos : 0 ≤ ∑ q ∈ F, ‖(xiZero q - s)⁻¹‖ ^ 2 :=
      Finset.sum_nonneg fun q _ => sq_nonneg _
    linarith
  have hm := (summable_norm_complexGaussianModes hs0 hs1 hxi hy).subtype (fun q => q ∉ F)
  calc
    _ ≤ ∑' q : {q : XiZeroCopy // q ∉ F}, ‖gaussianMBKernel y (xiZero q - s)‖ :=
      norm_tsum_le_tsum_norm hm
    _ ≤ ∑' q : {q : XiZeroCopy // q ∉ F},
        K * y ^ ((σ - θ) / 2) * ‖(xiZero q - s)⁻¹‖ ^ 2 :=
      hm.tsum_le_tsum hmode ((hv.subtype _).mul_left (K * y ^ ((σ - θ) / 2)))
    _ = K * y ^ ((σ - θ) / 2) *
        ∑' q : {q : XiZeroCopy // q ∉ F}, ‖(xiZero q - s)⁻¹‖ ^ 2 := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left hvle (by positivity)

/-- Finitely many exceptional modes suffice uniformly in height: the complete
complement contributes the damping power set by its horizontal gap. -/
theorem exists_finiteGaussianFinitePartError_bound {σ θ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (F : Finset XiZeroCopy)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 0 < y → y ≤ 1 →
      ∀ s ∈ gaussianRegularHighStrip σ δ,
        ‖finiteGaussianFinitePartError F s y‖ ≤
          C * (y + y ^ ((σ - θ) / 2)) * (1 + Real.log s.im) := by
  obtain ⟨K, hK, hk⟩ := exists_gaussianMode_unit_bound
  obtain ⟨D, hD, hd⟩ := exists_zeroResolvent_logHeight_bound hδ
  obtain ⟨C, hC, hc⟩ := exists_gaussianFinitePartError_logHeight_bound hσ hδ
  refine ⟨2 * C + K * D, by positivity, fun y hy hy1 s hs => ?_⟩
  have hs0 : 0 < s.re := hσ.trans_le hs.1
  have hxi := xi_ne_zero_of_separated hδ hs.2.2.2
  have hL : 0 ≤ 1 + Real.log s.im := by
    have := Real.log_nonneg (show 1 ≤ s.im by linarith [hs.2.2.1])
    linarith
  have hpow : 0 ≤ y ^ ((σ - θ) / 2) := by positivity
  have htail := norm_complementaryGaussianModes_le hk hK F hrest hs0 hs.2.1 hs.1 hxi hy hy1
  have htail' : ‖∑' q : {q : XiZeroCopy // q ∉ F}, gaussianMBKernel y (xiZero q - s)‖ ≤
      K * D * y ^ ((σ - θ) / 2) * (1 + Real.log s.im) := by
    refine htail.trans ?_
    calc
      _ ≤ K * y ^ ((σ - θ) / 2) * (D * (1 + Real.log s.im)) :=
        mul_le_mul_of_nonneg_left (hd s hs.2.2.1 hs.2.2.2) (by positivity)
      _ = _ := by ring
  have hfull : ‖complexGaussianFinitePartError s y‖ ≤ 2 * C * y * (1 + Real.log s.im) := by
    refine (hc y hy s hs).trans ?_
    have hcoef : C * y * (1 + y) ≤ 2 * C * y := by
      nlinarith [mul_nonneg (mul_nonneg hC.le hy.le) (sub_nonneg.mpr hy1)]
    exact mul_le_mul_of_nonneg_right hcoef hL
  rw [finiteGaussianFinitePartError_eq F hs0 hs.2.1 hxi hy]
  calc
    _ ≤ ‖complexGaussianFinitePartError s y‖ +
        ‖∑' q : {q : XiZeroCopy // q ∉ F}, gaussianMBKernel y (xiZero q - s)‖ := norm_sub_le _ _
    _ ≤ 2 * C * y * (1 + Real.log s.im) +
        K * D * y ^ ((σ - θ) / 2) * (1 + Real.log s.im) := add_le_add hfull htail'
    _ = (2 * C * y + K * D * y ^ ((σ - θ) / 2)) * (1 + Real.log s.im) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hL
      nlinarith [mul_nonneg (show 0 ≤ 2 * C by positivity) hpow,
        mul_nonneg (show 0 ≤ K * D by positivity) hy.le]

/-- A strict horizontal gap makes finite exceptional subtraction uniformly
sufficient after division by logarithmic height. -/
theorem tendstoUniformlyOn_finiteGaussianFinitePartError {σ θ δ : ℝ}
    (hσ : 0 < σ) (hδ : 0 < δ) (hgap : θ < σ) (F : Finset XiZeroCopy)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ) :
    TendstoUniformlyOn (fun y : ℝ => fun s : ℂ =>
      finiteGaussianFinitePartError F s y / ((1 + Real.log s.im : ℝ) : ℂ))
      (fun _ => 0) (𝓝[>] 0) (gaussianRegularHighStrip σ δ) := by
  obtain ⟨C, hC, hb⟩ := exists_finiteGaussianFinitePartError_bound hσ hδ F hrest
  have hη : 0 < (σ - θ) / 2 := by linarith
  have hp : Tendsto (fun y : ℝ => y ^ ((σ - θ) / 2)) (𝓝[>] 0) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const 0 ((σ - θ) / 2) (Or.inr hη.le)).tendsto
      |>.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simpa only [Real.zero_rpow hη.ne'] using h
  have hy0 : Tendsto (fun y : ℝ => y) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun y : ℝ => C * (y + y ^ ((σ - θ) / 2))) (𝓝[>] 0) (𝓝 0) := by
    simpa only [add_zero, mul_zero] using (hy0.add hp).const_mul C
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds zero_lt_one).filter_mono nhdsWithin_le_nhds,
    hlim.eventually (eventually_lt_nhds hε)] with y hy hy1 hyε
  change 0 < y at hy
  intro s hs
  have hL : 0 < 1 + Real.log s.im := by
    have := Real.log_nonneg (show 1 ≤ s.im by linarith [hs.2.2.1])
    linarith
  rw [dist_zero_left, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  exact ((div_le_iff₀ hL).mpr (hb y hy hy1.le s hs)).trans_lt hyε

/-- In the actual failure-of-AAL world, only finitely many exceptional modes
are needed at every high ordinate. The infinite complementary field vanishes
uniformly at its horizontal-gap power of damping. -/
theorem not_asymptoticAbscissaLaw_has_finiteGaussianControl
    (hnot : ¬ AsymptoticAbscissaLaw) :
    ∃ (F : Finset XiZeroCopy) (θ σ H C : ℝ),
      1 / 2 ≤ θ ∧ θ < σ ∧ σ < 1 ∧ 0 < H ∧ 0 < C ∧
      (∃ q ∈ F, σ < (q.1 : ℂ).re) ∧
      (∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ) ∧
      (∀ y : ℝ, 0 < y → y ≤ 1 → ∀ s : ℂ, σ ≤ s.re → s.re ≤ 1 → H ≤ s.im →
        ‖finiteGaussianFinitePartError F s y‖ ≤
          C * (y + y ^ ((σ - θ) / 2)) * (1 + Real.log s.im)) ∧
      TendstoUniformlyOn (fun y : ℝ => fun s : ℂ =>
        finiteGaussianFinitePartError F s y / ((1 + Real.log s.im : ℝ) : ℂ))
        (fun _ => 0) (𝓝[>] 0) {s : ℂ | σ ≤ s.re ∧ s.re ≤ 1 ∧ H ≤ s.im} := by
  classical
  unfold AsymptoticAbscissaLaw at hnot
  push Not at hnot
  obtain ⟨h, hh, hfin, q, hq⟩ := hnot
  obtain ⟨M, hM⟩ := (hfin.image fun p : XiZeroCopy => |(p.1 : ℂ).im|).bddAbove
  let F : Finset XiZeroCopy := hfin.toFinset
  let θ : ℝ := 1 / 2 + h
  let σ : ℝ := (θ + (q.1 : ℂ).re) / 2
  let δ : ℝ := ((q.1 : ℂ).re - θ) / 4
  let H : ℝ := max M 0 + δ + 4
  have hθ : 1 / 2 ≤ θ := by dsimp [θ]; linarith
  have hqθ : θ < (q.1 : ℂ).re := hq
  have hq1 := (xi_divisor_support_re_mem_open_unit q.1).2
  have hgap : θ < σ := by dsimp [σ]; linarith
  have hσ : 0 < σ := by linarith
  have hσ1 : σ < 1 := by dsimp [σ]; linarith
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hH : 0 < H := by dsimp [H]; positivity
  have hqF : q ∈ F := by simpa only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hq
  have hrest : ∀ p : XiZeroCopy, p ∉ F → (xiZero p).re ≤ θ := by
    intro p hp
    by_contra hn
    apply hp
    change p ∈ hfin.toFinset
    exact Set.Finite.mem_toFinset.mpr (lt_of_not_ge hn)
  have hdomain : ∀ s : ℂ, σ ≤ s.re → s.re ≤ 1 → H ≤ s.im →
      s ∈ gaussianRegularHighStrip σ δ := by
    intro s hsσ hs1 hsH
    have ht : 4 ≤ s.im := by dsimp [H] at hsH; linarith [le_max_right M 0]
    refine ⟨hsσ, hs1, ht, fun p => ?_⟩
    by_cases hp : (p.1 : ℂ).re ≤ θ
    · have hre : δ ≤ s.re - (p.1 : ℂ).re := by dsimp [σ] at hsσ; dsimp [δ]; linarith
      have hnorm := Complex.re_le_norm (s - (p.1 : ℂ))
      rw [Complex.sub_re, norm_sub_rev] at hnorm
      exact hre.trans hnorm
    · have hp' : p ∈ {p : XiZeroCopy | 1 / 2 + h < (p.1 : ℂ).re} := lt_of_not_ge hp
      have hpM : |(p.1 : ℂ).im| ≤ M := hM ⟨p, hp', rfl⟩
      have him : δ ≤ s.im - (p.1 : ℂ).im := by
        dsimp [H] at hsH
        linarith [le_max_left M 0, le_abs_self (p.1 : ℂ).im]
      have hnorm := Complex.im_le_norm (s - (p.1 : ℂ))
      rw [Complex.sub_im, norm_sub_rev] at hnorm
      exact him.trans hnorm
  obtain ⟨C, hC, hbound⟩ := exists_finiteGaussianFinitePartError_bound hσ hδ F hrest
  refine ⟨F, θ, σ, H, C, hθ, hgap, hσ1, hH, hC, ⟨q, hqF, by dsimp [σ]; linarith⟩,
    hrest, fun y hy hy1 s hsσ hs1 hsH => hbound y hy hy1 s (hdomain s hsσ hs1 hsH), ?_⟩
  have hu := tendstoUniformlyOn_finiteGaussianFinitePartError hσ hδ hgap F hrest
  rw [Metric.tendstoUniformlyOn_iff] at hu ⊢
  intro ε hε
  filter_upwards [hu ε hε] with y hy s hs
  exact hy s (hdomain s hs.1 hs.2.1 hs.2.2)

#print axioms exists_gaussianMode_unit_bound
#print axioms exists_finiteGaussianFinitePartError_bound
#print axioms tendstoUniformlyOn_finiteGaussianFinitePartError
#print axioms not_asymptoticAbscissaLaw_has_finiteGaussianControl

end GaloisForLFunctions.EulerFETransportTheory
