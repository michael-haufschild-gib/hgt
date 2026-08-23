import GaloisForLFunctions.RHTower.SuzukiCauchyGram

/-!
# The energy-weighted Cauchy series as an `L²` isometry

The functions `x ↦ (A/E)(x)/(x - γ_ρ)`, one for each distinct Xi zero, are pairwise orthogonal
in `L²(ℝ)` with `‖·‖² = π/m_ρ`.  A coefficient family square-summable against those weights
therefore gives an `L²`-convergent series, and the inner product of two such series is the
weighted `ℓ²` inner product.

The one delicate point is that the series is never absolutely convergent — `∑ √(m_ρ)/|γ_ρ|`
diverges — so the pointwise sum has to be identified with the `L²` sum.  That is done by
extracting an almost-everywhere convergent subsequence from the `L²` limit and comparing it with
the pointwise limit, which is why the divisor support is enumerated by `ℕ` here.
-/

open Complex Filter Topology MeasureTheory

namespace RHTower
noncomputable section

/-! ## An enumeration of the Xi divisor support -/

theorem countable_XiDivisorSupport : Countable XiDivisorSupport :=
  Set.countable_univ_iff.mp xiDivisorSupport_univ_countable

theorem infinite_XiDivisorSupport : Infinite XiDivisorSupport :=
  Set.infinite_coe_iff.mpr xiDivisorSupport_infinite

/-- An enumeration of the distinct Xi zeros. -/
def xiSupportEnum : ℕ ≃ XiDivisorSupport := by
  haveI := countable_XiDivisorSupport
  haveI := infinite_XiDivisorSupport
  haveI : Encodable XiDivisorSupport := Encodable.ofCountable _
  exact (Denumerable.ofEncodableOfInfinite XiDivisorSupport).eqv.symm

/-! ## The energy-weighted Cauchy kernels as `L²` vectors -/

/-- The `L²(ℝ)` function `x ↦ (A/E)(x) / (x - γ_ρ)`. -/
def suzukiEnergyKernelFun (ρ : XiDivisorSupport) (x : ℝ) : ℂ :=
  suzukiHalfInner ((x : ℝ) : ℂ) * suzukiCauchyKernel ρ x

theorem norm_sq_suzukiEnergyKernelFun (ρ : XiDivisorSupport) (x : ℝ) :
    ‖suzukiEnergyKernelFun ρ x‖ ^ 2
      = ‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ 2 / (x - xiRealSpectralPointSupport ρ) ^ 2 := by
  rw [suzukiEnergyKernelFun, norm_mul, mul_pow, suzukiCauchyKernel, norm_inv]
  rw [show ((x : ℂ) - ((xiRealSpectralPointSupport ρ : ℝ) : ℂ))
      = (((x - xiRealSpectralPointSupport ρ : ℝ)) : ℂ) by push_cast; ring]
  rw [Complex.norm_real, Real.norm_eq_abs, inv_pow, sq_abs, div_eq_mul_inv]

theorem continuous_suzukiHalfInner_ofReal (hRH : RiemannHypothesis) :
    Continuous fun x : ℝ => suzukiHalfInner ((x : ℝ) : ℂ) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  exact (differentiableAt_suzukiHalfInner_of_rh hRH (z := ((x : ℝ) : ℂ))
    (by simp)).continuousAt.comp Complex.continuous_ofReal.continuousAt

theorem aestronglyMeasurable_suzukiEnergyKernelFun (hRH : RiemannHypothesis)
    (ρ : XiDivisorSupport) :
    AEStronglyMeasurable (suzukiEnergyKernelFun ρ) volume := by
  refine ((continuous_suzukiHalfInner_ofReal hRH).aestronglyMeasurable).mul ?_
  exact (Measurable.inv (Complex.measurable_ofReal.sub measurable_const)).aestronglyMeasurable

theorem memLp_suzukiEnergyKernelFun (hRH : RiemannHypothesis) (ρ : XiDivisorSupport) :
    MemLp (suzukiEnergyKernelFun ρ) 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm
    (aestronglyMeasurable_suzukiEnergyKernelFun hRH ρ)).mpr ?_
  refine (integrable_normSq_suzukiHalfInner_div_sq hRH (xiSupportMult_pos ρ)
    (analyticOrderAt_xiRealSpectralPointSupport hRH ρ)
    (XiC_xiRealSpectralPointSupport hRH ρ)).congr ?_
  filter_upwards with x
  exact (norm_sq_suzukiEnergyKernelFun ρ x).symm

/-- The `L²(ℝ)` vector of the energy-weighted Cauchy kernel at a Xi zero. -/
def suzukiEnergyKernel (hRH : RiemannHypothesis) (ρ : XiDivisorSupport) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (memLp_suzukiEnergyKernelFun hRH ρ).toLp _

/-- **The Gram identity in `L²`.** -/
theorem inner_suzukiEnergyKernel (hRH : RiemannHypothesis) (ρ σ : XiDivisorSupport) :
    inner ℂ (suzukiEnergyKernel hRH ρ) (suzukiEnergyKernel hRH σ)
      = if ρ = σ then ((Real.pi / (xiSupportMult ρ : ℝ) : ℝ) : ℂ) else 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hae : (fun x : ℝ => inner ℂ ((suzukiEnergyKernel hRH ρ : Lp ℂ 2 _) x)
        ((suzukiEnergyKernel hRH σ : Lp ℂ 2 _) x))
      =ᵐ[volume] fun x : ℝ => ((‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) *
        ((starRingEnd ℂ) (suzukiCauchyKernel ρ x)) * (suzukiCauchyKernel σ x) := by
    simp only [suzukiEnergyKernel]
    filter_upwards [(memLp_suzukiEnergyKernelFun hRH ρ).coeFn_toLp,
      (memLp_suzukiEnergyKernelFun hRH σ).coeFn_toLp] with x h1 h2
    rw [h1, h2, RCLike.inner_apply, suzukiEnergyKernelFun, suzukiEnergyKernelFun]
    rw [map_mul]
    have hconj : (starRingEnd ℂ) (suzukiHalfInner ((x : ℝ) : ℂ)) *
        suzukiHalfInner ((x : ℝ) : ℂ)
        = ((‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj, Complex.sq_norm]
    rw [← hconj]
    ring
  rw [MeasureTheory.integral_congr_ae hae]
  exact integral_halfInnerEnergy_kernel_pair hRH ρ σ

/-! ## Finite orthogonal sums -/

theorem inner_finsetSum_smul_of_orthogonal {ι : Type*} [DecidableEq ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v : ι → E) (w : ι → ℝ)
    (hv : ∀ i j, inner ℂ (v i) (v j) = if i = j then ((w i : ℝ) : ℂ) else 0)
    (s : Finset ι) (a b : ι → ℂ) :
    inner ℂ (∑ i ∈ s, a i • v i) (∑ j ∈ s, b j • v j)
      = ∑ i ∈ s, (starRingEnd ℂ) (a i) * b i * ((w i : ℝ) : ℂ) := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · rw [inner_smul_left, inner_smul_right, hv i i, if_pos rfl]
    ring
  · intro j _ hji
    rw [inner_smul_left, inner_smul_right, hv i j, if_neg (Ne.symm hji)]
    ring
  · intro h
    exact absurd hi h

/-! ## The Cauchy series in `L²` -/

/-- Partial sums of the energy-weighted Cauchy series along the enumeration. -/
def suzukiCauchyPartial (hRH : RiemannHypothesis) (a : XiDivisorSupport → ℂ) (N : ℕ) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  ∑ n ∈ Finset.range N, a (xiSupportEnum n) • suzukiEnergyKernel hRH (xiSupportEnum n)

/-- The weight attached to each Xi zero by the Gram identity. -/
def suzukiCauchyWeight (ρ : XiDivisorSupport) : ℝ := Real.pi / (xiSupportMult ρ : ℝ)

theorem suzukiCauchyWeight_pos (ρ : XiDivisorSupport) : 0 < suzukiCauchyWeight ρ := by
  have h : (0 : ℝ) < (xiSupportMult ρ : ℝ) := by
    exact_mod_cast xiSupportMult_pos ρ
  exact div_pos Real.pi_pos h

theorem inner_suzukiCauchyPartial (hRH : RiemannHypothesis) (a b : XiDivisorSupport → ℂ)
    (N : ℕ) :
    inner ℂ (suzukiCauchyPartial hRH a N) (suzukiCauchyPartial hRH b N)
      = ∑ n ∈ Finset.range N, (starRingEnd ℂ) (a (xiSupportEnum n)) * b (xiSupportEnum n)
          * ((suzukiCauchyWeight (xiSupportEnum n) : ℝ) : ℂ) := by
  classical
  have hv : ∀ n l : ℕ,
      inner ℂ (suzukiEnergyKernel hRH (xiSupportEnum n))
          (suzukiEnergyKernel hRH (xiSupportEnum l))
        = if n = l then ((suzukiCauchyWeight (xiSupportEnum n) : ℝ) : ℂ) else 0 := by
    intro n l
    rw [inner_suzukiEnergyKernel hRH]
    by_cases h : n = l
    · subst h
      rw [if_pos rfl, if_pos rfl, suzukiCauchyWeight]
    · rw [if_neg h, if_neg (fun hc => h (xiSupportEnum.injective hc))]
  exact inner_finsetSum_smul_of_orthogonal _ _ hv (Finset.range N)
    (fun n => a (xiSupportEnum n)) (fun n => b (xiSupportEnum n))

theorem suzukiCauchyPartial_sub (hRH : RiemannHypothesis) (a : XiDivisorSupport → ℂ)
    {M N : ℕ} (hMN : M ≤ N) :
    suzukiCauchyPartial hRH a N - suzukiCauchyPartial hRH a M
      = ∑ n ∈ Finset.Ico M N, a (xiSupportEnum n) • suzukiEnergyKernel hRH (xiSupportEnum n) := by
  rw [suzukiCauchyPartial, suzukiCauchyPartial]
  exact (Finset.sum_Ico_eq_sub _ hMN).symm

theorem norm_sq_suzukiCauchyPartial_sub (hRH : RiemannHypothesis) (a : XiDivisorSupport → ℂ)
    {M N : ℕ} (hMN : M ≤ N) :
    ‖suzukiCauchyPartial hRH a N - suzukiCauchyPartial hRH a M‖ ^ 2
      = ∑ n ∈ Finset.Ico M N,
          ‖a (xiSupportEnum n)‖ ^ 2 * suzukiCauchyWeight (xiSupportEnum n) := by
  classical
  have hv : ∀ n l : ℕ,
      inner ℂ (suzukiEnergyKernel hRH (xiSupportEnum n))
          (suzukiEnergyKernel hRH (xiSupportEnum l))
        = if n = l then ((suzukiCauchyWeight (xiSupportEnum n) : ℝ) : ℂ) else 0 := by
    intro n l
    rw [inner_suzukiEnergyKernel hRH]
    by_cases h : n = l
    · subst h
      rw [if_pos rfl, if_pos rfl, suzukiCauchyWeight]
    · rw [if_neg h, if_neg (fun hc => h (xiSupportEnum.injective hc))]
  have hinner := inner_finsetSum_smul_of_orthogonal _ _ hv (Finset.Ico M N)
    (fun n => a (xiSupportEnum n)) (fun n => a (xiSupportEnum n))
  rw [suzukiCauchyPartial_sub hRH a hMN]
  have hsq := @inner_self_eq_norm_sq ℂ _ _ _ _
    (∑ n ∈ Finset.Ico M N, a (xiSupportEnum n) • suzukiEnergyKernel hRH (xiSupportEnum n))
  rw [hinner] at hsq
  rw [← hsq]
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mul_comm ((starRingEnd ℂ) (a (xiSupportEnum n))) (a (xiSupportEnum n)),
    Complex.mul_conj, Complex.sq_norm]
  simp


/-! ## Convergence of the Cauchy series -/

theorem cauchySeq_suzukiCauchyPartial (hRH : RiemannHypothesis) (a : XiDivisorSupport → ℂ)
    (hsum : Summable fun ρ : XiDivisorSupport => ‖a ρ‖ ^ 2 * suzukiCauchyWeight ρ) :
    CauchySeq (suzukiCauchyPartial hRH a) := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  have hsumN : Summable fun n : ℕ =>
      ‖a (xiSupportEnum n)‖ ^ 2 * suzukiCauchyWeight (xiSupportEnum n) :=
    (xiSupportEnum.summable_iff
      (f := fun ρ : XiDivisorSupport => ‖a ρ‖ ^ 2 * suzukiCauchyWeight ρ)).mpr hsum
  have hc : CauchySeq fun N : ℕ => ∑ n ∈ Finset.range N,
      ‖a (xiSupportEnum n)‖ ^ 2 * suzukiCauchyWeight (xiSupportEnum n) :=
    hsumN.hasSum.tendsto_sum_nat.cauchySeq
  rw [Metric.cauchySeq_iff'] at hc
  obtain ⟨M, hM⟩ := hc (ε ^ 2) (by positivity)
  refine ⟨M, fun N hN => ?_⟩
  have h1 := hM N hN
  rw [Real.dist_eq, ← Finset.sum_Ico_eq_sub _ hN] at h1
  have hnonneg : (0 : ℝ) ≤ ∑ n ∈ Finset.Ico M N,
      ‖a (xiSupportEnum n)‖ ^ 2 * suzukiCauchyWeight (xiSupportEnum n) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (sq_nonneg _) (suzukiCauchyWeight_pos _).le
  have h2 : ‖suzukiCauchyPartial hRH a N - suzukiCauchyPartial hRH a M‖ ^ 2 < ε ^ 2 := by
    rw [norm_sq_suzukiCauchyPartial_sub hRH a hN]
    rw [abs_of_nonneg hnonneg] at h1
    exact h1
  rw [dist_eq_norm]
  nlinarith [norm_nonneg (suzukiCauchyPartial hRH a N - suzukiCauchyPartial hRH a M), h2, hε]

theorem coeFn_eq_of_tendsto_ae {S : Lp ℂ 2 (volume : Measure ℝ)}
    {F : ℕ → Lp ℂ 2 (volume : Measure ℝ)} {g : ℝ → ℂ}
    (hconv : Tendsto F atTop (𝓝 S))
    (hpt : ∀ᵐ x ∂(volume : Measure ℝ), Tendsto (fun n => (F n : ℝ → ℂ) x) atTop (𝓝 (g x))) :
    (S : ℝ → ℂ) =ᵐ[volume] g := by
  obtain ⟨ns, hmono, hae⟩ :=
    (MeasureTheory.tendstoInMeasure_of_tendsto_Lp hconv).exists_seq_tendsto_ae
  filter_upwards [hae, hpt] with x h1 h2
  exact tendsto_nhds_unique h1 (h2.comp hmono.tendsto_atTop)

theorem coeFn_suzukiCauchyPartial (hRH : RiemannHypothesis) (a : XiDivisorSupport → ℂ) (N : ℕ) :
    (suzukiCauchyPartial hRH a N : ℝ → ℂ)
      =ᵐ[volume] fun x : ℝ => ∑ n ∈ Finset.range N,
        a (xiSupportEnum n) * suzukiEnergyKernelFun (xiSupportEnum n) x := by
  induction N with
  | zero =>
    have h0 : suzukiCauchyPartial hRH a 0 = 0 := by simp [suzukiCauchyPartial]
    rw [h0]
    filter_upwards [MeasureTheory.Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx
    rw [hx]
    simp
  | succ N ih =>
    have hstep : suzukiCauchyPartial hRH a (N + 1)
        = suzukiCauchyPartial hRH a N
          + a (xiSupportEnum N) • suzukiEnergyKernel hRH (xiSupportEnum N) := by
      rw [suzukiCauchyPartial, suzukiCauchyPartial, Finset.sum_range_succ]
    rw [hstep]
    filter_upwards [MeasureTheory.Lp.coeFn_add (suzukiCauchyPartial hRH a N)
        (a (xiSupportEnum N) • suzukiEnergyKernel hRH (xiSupportEnum N)),
      MeasureTheory.Lp.coeFn_smul (a (xiSupportEnum N))
        (suzukiEnergyKernel hRH (xiSupportEnum N)),
      (memLp_suzukiEnergyKernelFun hRH (xiSupportEnum N)).coeFn_toLp, ih] with x h1 h2 h3 h4
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, h4, Finset.sum_range_succ]
    simp only [suzukiEnergyKernel]
    rw [h3, smul_eq_mul]


/-! ## The pointwise sum is the `L²` sum -/

theorem exists_lp_of_hasSum (hRH : RiemannHypothesis) (a : XiDivisorSupport → ℂ)
    (hsa : Summable fun ρ : XiDivisorSupport => ‖a ρ‖ ^ 2 * suzukiCauchyWeight ρ)
    (g : ℝ → ℂ)
    (hg : ∀ᵐ x ∂(volume : Measure ℝ),
      HasSum (fun ρ : XiDivisorSupport => a ρ * suzukiEnergyKernelFun ρ x) (g x)) :
    ∃ S : Lp ℂ 2 (volume : Measure ℝ),
      Tendsto (suzukiCauchyPartial hRH a) atTop (𝓝 S) ∧ (S : ℝ → ℂ) =ᵐ[volume] g := by
  obtain ⟨S, hS⟩ := cauchySeq_tendsto_of_complete (cauchySeq_suzukiCauchyPartial hRH a hsa)
  refine ⟨S, hS, coeFn_eq_of_tendsto_ae hS ?_⟩
  have hall : ∀ᵐ x ∂(volume : Measure ℝ), ∀ N : ℕ,
      (suzukiCauchyPartial hRH a N : ℝ → ℂ) x
        = ∑ n ∈ Finset.range N,
          a (xiSupportEnum n) * suzukiEnergyKernelFun (xiSupportEnum n) x :=
    (MeasureTheory.ae_all_iff).mpr fun N => coeFn_suzukiCauchyPartial hRH a N
  filter_upwards [hall, hg] with x hx hgx
  have hnat : HasSum
      (fun n : ℕ => a (xiSupportEnum n) * suzukiEnergyKernelFun (xiSupportEnum n) x) (g x) :=
    (xiSupportEnum.hasSum_iff
      (f := fun ρ : XiDivisorSupport => a ρ * suzukiEnergyKernelFun ρ x)).mpr hgx
  refine (hnat.tendsto_sum_nat).congr fun N => ?_
  exact (hx N).symm

theorem summable_cross (a b : XiDivisorSupport → ℂ)
    (hsa : Summable fun ρ : XiDivisorSupport => ‖a ρ‖ ^ 2 * suzukiCauchyWeight ρ)
    (hsb : Summable fun ρ : XiDivisorSupport => ‖b ρ‖ ^ 2 * suzukiCauchyWeight ρ) :
    Summable fun ρ : XiDivisorSupport =>
      (starRingEnd ℂ) (a ρ) * b ρ * ((suzukiCauchyWeight ρ : ℝ) : ℂ) := by
  refine Summable.of_norm_bounded ((hsa.add hsb).mul_left (1 / 2)) fun ρ => ?_
  rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (suzukiCauchyWeight_pos ρ).le]
  nlinarith [sq_nonneg (‖a ρ‖ - ‖b ρ‖), (suzukiCauchyWeight_pos ρ).le, norm_nonneg (a ρ),
    norm_nonneg (b ρ), mul_nonneg (norm_nonneg (a ρ)) (norm_nonneg (b ρ))]

theorem inner_of_tendsto (hRH : RiemannHypothesis) (a b : XiDivisorSupport → ℂ)
    (hsa : Summable fun ρ : XiDivisorSupport => ‖a ρ‖ ^ 2 * suzukiCauchyWeight ρ)
    (hsb : Summable fun ρ : XiDivisorSupport => ‖b ρ‖ ^ 2 * suzukiCauchyWeight ρ)
    {S T : Lp ℂ 2 (volume : Measure ℝ)}
    (hS : Tendsto (suzukiCauchyPartial hRH a) atTop (𝓝 S))
    (hT : Tendsto (suzukiCauchyPartial hRH b) atTop (𝓝 T)) :
    inner ℂ S T = ∑' ρ : XiDivisorSupport,
      (starRingEnd ℂ) (a ρ) * b ρ * ((suzukiCauchyWeight ρ : ℝ) : ℂ) := by
  have hsc := summable_cross a b hsa hsb
  have hscN : Summable fun n : ℕ => (starRingEnd ℂ) (a (xiSupportEnum n)) * b (xiSupportEnum n)
      * ((suzukiCauchyWeight (xiSupportEnum n) : ℝ) : ℂ) :=
    (xiSupportEnum.summable_iff
      (f := fun ρ : XiDivisorSupport =>
        (starRingEnd ℂ) (a ρ) * b ρ * ((suzukiCauchyWeight ρ : ℝ) : ℂ))).mpr hsc
  have hlim : Tendsto (fun N : ℕ => inner ℂ (suzukiCauchyPartial hRH a N)
      (suzukiCauchyPartial hRH b N)) atTop (𝓝 (inner ℂ S T)) := by
    exact (continuous_inner (𝕜 := ℂ)).continuousAt.tendsto.comp (hS.prodMk_nhds hT)
  have hpartial : ∀ N : ℕ, inner ℂ (suzukiCauchyPartial hRH a N) (suzukiCauchyPartial hRH b N)
      = ∑ n ∈ Finset.range N, (starRingEnd ℂ) (a (xiSupportEnum n)) * b (xiSupportEnum n)
          * ((suzukiCauchyWeight (xiSupportEnum n) : ℝ) : ℂ) :=
    fun N => inner_suzukiCauchyPartial hRH a b N
  have hlim2 := hlim.congr hpartial
  have hsumN := (hscN.hasSum_iff_tendsto_nat).mpr hlim2
  rw [← hsumN.tsum_eq]
  exact xiSupportEnum.tsum_eq
    (fun ρ : XiDivisorSupport =>
      (starRingEnd ℂ) (a ρ) * b ρ * ((suzukiCauchyWeight ρ : ℝ) : ℂ))


/-- **The Cauchy-series isometry.**  For coefficient families square-summable against the Gram
weights, the `L²(ℝ)` inner product of the pointwise energy-weighted Cauchy series is the weighted
`ℓ²` inner product of the coefficients. -/
theorem integral_conj_of_hasSum (hRH : RiemannHypothesis) (a b : XiDivisorSupport → ℂ)
    (hsa : Summable fun ρ : XiDivisorSupport => ‖a ρ‖ ^ 2 * suzukiCauchyWeight ρ)
    (hsb : Summable fun ρ : XiDivisorSupport => ‖b ρ‖ ^ 2 * suzukiCauchyWeight ρ)
    (ga gb : ℝ → ℂ)
    (hga : ∀ᵐ x ∂(volume : Measure ℝ),
      HasSum (fun ρ : XiDivisorSupport => a ρ * suzukiEnergyKernelFun ρ x) (ga x))
    (hgb : ∀ᵐ x ∂(volume : Measure ℝ),
      HasSum (fun ρ : XiDivisorSupport => b ρ * suzukiEnergyKernelFun ρ x) (gb x)) :
    (∫ x : ℝ, (starRingEnd ℂ) (ga x) * gb x)
      = ∑' ρ : XiDivisorSupport,
        (starRingEnd ℂ) (a ρ) * b ρ * ((suzukiCauchyWeight ρ : ℝ) : ℂ) := by
  obtain ⟨Sa, hSa, haea⟩ := exists_lp_of_hasSum hRH a hsa ga hga
  obtain ⟨Sb, hSb, haeb⟩ := exists_lp_of_hasSum hRH b hsb gb hgb
  have hinner := inner_of_tendsto hRH a b hsa hsb hSa hSb
  rw [← hinner, MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [haea, haeb] with x h1 h2
  rw [RCLike.inner_apply, h1, h2]
  ring

/-- The pointwise sum of the energy-weighted Cauchy series lies in `L²(ℝ)`. -/
theorem memLp_of_hasSum (hRH : RiemannHypothesis) (a : XiDivisorSupport → ℂ)
    (hsa : Summable fun ρ : XiDivisorSupport => ‖a ρ‖ ^ 2 * suzukiCauchyWeight ρ)
    (g : ℝ → ℂ)
    (hg : ∀ᵐ x ∂(volume : Measure ℝ),
      HasSum (fun ρ : XiDivisorSupport => a ρ * suzukiEnergyKernelFun ρ x) (g x)) :
    MemLp g 2 (volume : Measure ℝ) := by
  obtain ⟨S, _, hae⟩ := exists_lp_of_hasSum hRH a hsa g hg
  exact (Lp.memLp S).ae_eq hae

end
end RHTower
