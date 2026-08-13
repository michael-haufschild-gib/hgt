import GaloisForLFunctions.HTGeometry.BoundaryCarrierTranslationFreeness
import GaloisForLFunctions.HTGeometry.CauchyKernelWeakConvergence
import GaloisForLFunctions.HTGeometry.CauchyJetFrame

/-!
# The maximal-translation full-rank phase is a Gδ set

The simultaneous full-rank witness phase quantifies one open finite certificate — a lower
packet with injective expanded-evaluation `mulVec` — over every canonical pattern and every
injective shift configuration.  Patterns are countable.  The shift space is exhausted by the
compact sets of configurations with bounded nodes and quantified minimal separation, and on each
compact piece the universal section of the jointly open certificate set is open by the tube
lemma.  Joint openness comes from the weak-topology continuity of every Cauchy power transform,
uniformly controlled through the elementary kernel difference identity
`(x−z)⁻¹ − (x−w)⁻¹ = (z−w)(x−z)⁻¹(x−w)⁻¹`.

Consequently the full-rank phase is a countable intersection of open sets.  Since the full-rank
witness implies maximal translation-differential-freeness pointwise, residuality of the free
phase follows from residuality of the full-rank phase by monotonicity, with no separate Gδ
hypothesis on the free phase.
-/

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.HTGeometry

open ClassicalAnalyticNevanlinnaCarrierFamily

noncomputable section

/-! ## Kernel difference estimates -/

theorem cauchyKernel_base_ne_zero {z : ℂ} (hz : z.im ≠ 0) (x : ℝ) :
    ((x : ℂ) - z) ≠ 0 := by
  intro hcon
  apply hz
  have him := congrArg Complex.im hcon
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im] at him
  linarith

/-- Norm bound for a difference of powers with a common bound on both bases. -/
theorem norm_pow_sub_pow_le_of_norm_le {A B : ℂ} {M : ℝ}
    (hA : ‖A‖ ≤ M) (hB : ‖B‖ ≤ M) (m : ℕ) :
    ‖A ^ m - B ^ m‖ ≤ m * M ^ (m - 1) * ‖A - B‖ := by
  have hM : 0 ≤ M := le_trans (norm_nonneg A) hA
  rw [← geom_sum₂_mul A B m, norm_mul]
  have hsum : ‖∑ i ∈ Finset.range m, A ^ i * B ^ (m - 1 - i)‖ ≤ m * M ^ (m - 1) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hterm : ∀ i ∈ Finset.range m, ‖A ^ i * B ^ (m - 1 - i)‖ ≤ M ^ (m - 1) := by
      intro i hi
      simp only [Finset.mem_range] at hi
      rw [norm_mul, norm_pow, norm_pow]
      calc ‖A‖ ^ i * ‖B‖ ^ (m - 1 - i)
          ≤ M ^ i * M ^ (m - 1 - i) := by
            exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hA i)
              (pow_le_pow_left₀ (norm_nonneg _) hB _)
              (pow_nonneg (norm_nonneg _) _) (pow_nonneg hM i)
        _ = M ^ (m - 1) := by
            rw [← pow_add]
            congr 1
            omega
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

/-- The Cauchy kernel difference identity. -/
theorem cauchyKernel_sub_eq (x : ℝ) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    ((x : ℂ) - z)⁻¹ - ((x : ℂ) - w)⁻¹ =
      (z - w) * (((x : ℂ) - z)⁻¹ * ((x : ℂ) - w)⁻¹) := by
  have h1 := cauchyKernel_base_ne_zero hz x
  have h2 := cauchyKernel_base_ne_zero hw x
  field_simp
  ring

/-- Uniform-in-`x` difference bound for Cauchy kernel powers. -/
theorem norm_cauchyPow_sub_le (m : ℕ) {z w : ℂ} {M : ℝ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hzM : |z.im|⁻¹ ≤ M) (hwM : |w.im|⁻¹ ≤ M) (x : ℝ) :
    ‖(((x : ℂ) - z)⁻¹) ^ m - (((x : ℂ) - w)⁻¹) ^ m‖ ≤
      m * M ^ (m + 1) * ‖z - w‖ := by
  have hM : 0 ≤ M := le_trans (by positivity) hzM
  have hA : ‖((x : ℂ) - z)⁻¹‖ ≤ M := le_trans (_root_.HTGeometry.norm_cauchy_kernel_le x hz) hzM
  have hB : ‖((x : ℂ) - w)⁻¹‖ ≤ M := le_trans (_root_.HTGeometry.norm_cauchy_kernel_le x hw) hwM
  have hstep := norm_pow_sub_pow_le_of_norm_le hA hB m
  have hdiff : ‖((x : ℂ) - z)⁻¹ - ((x : ℂ) - w)⁻¹‖ ≤ ‖z - w‖ * (M * M) := by
    rw [cauchyKernel_sub_eq x hz hw, norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul hA hB (norm_nonneg _) hM) (norm_nonneg _)
  calc ‖(((x : ℂ) - z)⁻¹) ^ m - (((x : ℂ) - w)⁻¹) ^ m‖
      ≤ m * M ^ (m - 1) * ‖((x : ℂ) - z)⁻¹ - ((x : ℂ) - w)⁻¹‖ := hstep
    _ ≤ m * M ^ (m - 1) * (‖z - w‖ * (M * M)) := by
        exact mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ ≤ m * M ^ (m + 1) * ‖z - w‖ := by
        rcases Nat.eq_zero_or_pos m with hm | hm
        · subst hm
          simp
        · have hpow : M ^ (m - 1) * (M * M) = M ^ (m + 1) := by
            rw [show M * M = M ^ 2 by ring, ← pow_add]
            congr 1
            omega
          have hrw : (m : ℝ) * M ^ (m - 1) * (‖z - w‖ * (M * M))
              = m * M ^ (m + 1) * ‖z - w‖ := by
            rw [← hpow]
            ring
          rw [hrw]

/-! ## Weak continuity of the power transforms -/

theorem integrable_cauchyPow (μ : Measure ℝ) [IsFiniteMeasure μ] {z : ℂ}
    (hz : z.im ≠ 0) (m : ℕ) :
    Integrable (fun x : ℝ => (((x : ℂ) - z)⁻¹) ^ m) μ := by
  refine Integrable.of_bound
    ((_root_.HTGeometry.continuous_cauchyKernel hz).pow m).aestronglyMeasurable
    (|z.im|⁻¹ ^ m) ?_
  filter_upwards with x
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (_root_.HTGeometry.norm_cauchy_kernel_le x hz) m

/-- The real part of a Cauchy power kernel as a bounded continuous test function. -/
def cauchyPowKernelRe (m : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ => ((((x : ℂ) - z)⁻¹) ^ m).re)
    (Complex.continuous_re.comp ((_root_.HTGeometry.continuous_cauchyKernel hz).pow m))
    (|z.im|⁻¹ ^ m)
    fun x => le_trans (Complex.abs_re_le_norm _) (by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (_root_.HTGeometry.norm_cauchy_kernel_le x hz) m)

/-- The imaginary part of a Cauchy power kernel as a bounded continuous test function. -/
def cauchyPowKernelIm (m : ℕ) (z : ℂ) (hz : z.im ≠ 0) :
    BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ => ((((x : ℂ) - z)⁻¹) ^ m).im)
    (Complex.continuous_im.comp ((_root_.HTGeometry.continuous_cauchyKernel hz).pow m))
    (|z.im|⁻¹ ^ m)
    fun x => le_trans (Complex.abs_im_le_norm _) (by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) (_root_.HTGeometry.norm_cauchy_kernel_le x hz) m)

theorem cauchyPowerTransform_eq_re_add_im (μ : Measure ℝ) [IsFiniteMeasure μ] {z : ℂ}
    (hz : z.im ≠ 0) (m : ℕ) :
    ∫ x, (((x : ℂ) - z)⁻¹) ^ m ∂μ
      = (((∫ x, ((((x : ℂ) - z)⁻¹) ^ m).re ∂μ : ℝ)) : ℂ)
        + (((∫ x, ((((x : ℂ) - z)⁻¹) ^ m).im ∂μ : ℝ)) : ℂ) * Complex.I := by
  have hint := integrable_cauchyPow μ hz m
  have hre : ∫ x, ((((x : ℂ) - z)⁻¹) ^ m).re ∂μ
      = (∫ x, (((x : ℂ) - z)⁻¹) ^ m ∂μ).re := by
    simpa using Complex.reCLM.integral_comp_comm hint
  have him : ∫ x, ((((x : ℂ) - z)⁻¹) ^ m).im ∂μ
      = (∫ x, (((x : ℂ) - z)⁻¹) ^ m ∂μ).im := by
    simpa using Complex.imCLM.integral_comp_comm hint
  rw [hre, him, Complex.re_add_im]

/-- **Weak convergence carries every Cauchy power transform.** -/
theorem tendsto_cauchyPowerTransform_of_tendsto {ι : Type*} {F : Filter ι}
    {μs : ι → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (hlim : Tendsto μs F (𝓝 μ)) {z : ℂ} (hz : z.im ≠ 0) (m : ℕ) :
    Tendsto (fun i => ∫ x, (((x : ℂ) - z)⁻¹) ^ m ∂(μs i : Measure ℝ)) F
      (𝓝 (∫ x, (((x : ℂ) - z)⁻¹) ^ m ∂(μ : Measure ℝ))) := by
  have hall := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim
  have hre := hall (cauchyPowKernelRe m z hz)
  have him := hall (cauchyPowKernelIm m z hz)
  have hcomb : Tendsto (fun i =>
      (((∫ x, ((((x : ℂ) - z)⁻¹) ^ m).re ∂(μs i : Measure ℝ) : ℝ)) : ℂ)
        + (((∫ x, ((((x : ℂ) - z)⁻¹) ^ m).im ∂(μs i : Measure ℝ) : ℝ)) : ℂ)
            * Complex.I) F
      (𝓝 ((((∫ x, ((((x : ℂ) - z)⁻¹) ^ m).re ∂(μ : Measure ℝ) : ℝ)) : ℂ)
        + (((∫ x, ((((x : ℂ) - z)⁻¹) ^ m).im ∂(μ : Measure ℝ) : ℝ)) : ℂ)
            * Complex.I)) := by
    refine (((Complex.continuous_ofReal.tendsto _).comp hre).add ?_)
    exact (((Complex.continuous_ofReal.tendsto _).comp him).mul_const Complex.I)
  rw [cauchyPowerTransform_eq_re_add_im _ hz]
  refine hcomb.congr fun i => ?_
  exact (cauchyPowerTransform_eq_re_add_im (μs i : Measure ℝ) hz m).symm

/-- **Joint continuity of the Cauchy power transform** in the probability measure (weak topology)
and the off-axis node. -/
theorem continuousOn_cauchyPowerTransform (m : ℕ) :
    ContinuousOn
      (fun q : ProbabilityMeasure ℝ × ℂ =>
        ∫ x, (((x : ℂ) - q.2)⁻¹) ^ m ∂(q.1 : Measure ℝ))
      {q : ProbabilityMeasure ℝ × ℂ | q.2.im ≠ 0} := by
  intro q₀ hq₀
  have hz₀ : q₀.2.im ≠ 0 := hq₀
  set S : Set (ProbabilityMeasure ℝ × ℂ) := {q | q.2.im ≠ 0}
  set G : ProbabilityMeasure ℝ × ℂ → ℂ := fun q =>
    ∫ x, (((x : ℂ) - q₀.2)⁻¹) ^ m ∂(q.1 : Measure ℝ) with hGdef
  set Fn : ProbabilityMeasure ℝ × ℂ → ℂ := fun q =>
    ∫ x, (((x : ℂ) - q.2)⁻¹) ^ m ∂(q.1 : Measure ℝ) with hFdef
  have hfst : Tendsto (fun q : ProbabilityMeasure ℝ × ℂ => q.1) (𝓝[S] q₀) (𝓝 q₀.1) :=
    (continuous_fst.tendsto q₀).mono_left nhdsWithin_le_nhds
  have hG : Tendsto G (𝓝[S] q₀) (𝓝 (Fn q₀)) :=
    tendsto_cauchyPowerTransform_of_tendsto hfst hz₀ m
  have hsnd : Tendsto (fun q : ProbabilityMeasure ℝ × ℂ => ‖q.2 - q₀.2‖)
      (𝓝[S] q₀) (𝓝 0) := by
    have : Tendsto (fun q : ProbabilityMeasure ℝ × ℂ => q.2 - q₀.2) (𝓝[S] q₀)
        (𝓝 (q₀.2 - q₀.2)) :=
      ((continuous_snd.tendsto q₀).mono_left nhdsWithin_le_nhds).sub tendsto_const_nhds
    rw [sub_self] at this
    simpa using this.norm
  set M : ℝ := 2 * |q₀.2.im|⁻¹ with hMdef
  have hdiff : Tendsto (fun q => Fn q - G q) (𝓝[S] q₀) (𝓝 0) := by
    apply squeeze_zero_norm'
      (a := fun q : ProbabilityMeasure ℝ × ℂ => m * M ^ (m + 1) * ‖q.2 - q₀.2‖)
    · have hnear : ∀ᶠ q : ProbabilityMeasure ℝ × ℂ in 𝓝[S] q₀,
          ‖q.2 - q₀.2‖ < |q₀.2.im| / 2 :=
        hsnd.eventually_lt_const (by positivity)
      filter_upwards [hnear, self_mem_nhdsWithin] with q hqnear hqS
      have hzq : q.2.im ≠ 0 := hqS
      have hqim : |q₀.2.im| / 2 ≤ |q.2.im| := by
        have h1 : |q₀.2.im - q.2.im| ≤ ‖q₀.2 - q.2‖ := by
          have := Complex.abs_im_le_norm (q₀.2 - q.2)
          simpa [Complex.sub_im] using this
        have h2 : ‖q₀.2 - q.2‖ < |q₀.2.im| / 2 := by
          rw [norm_sub_rev]
          exact hqnear
        have h3 := abs_sub_abs_le_abs_sub q₀.2.im q.2.im
        linarith [le_trans h3 (le_of_lt (lt_of_le_of_lt h1 h2))]
      have hq₀pos : 0 < |q₀.2.im| := abs_pos.mpr hz₀
      have hqM : |q.2.im|⁻¹ ≤ M := by
        rw [hMdef]
        have h2pos : 0 < |q₀.2.im| / 2 := by positivity
        calc |q.2.im|⁻¹ ≤ (|q₀.2.im| / 2)⁻¹ := by
              exact inv_anti₀ h2pos hqim
          _ = 2 * |q₀.2.im|⁻¹ := by
              rw [div_eq_mul_inv, mul_inv, inv_inv]
              ring
      have hq₀M : |q₀.2.im|⁻¹ ≤ M := by
        rw [hMdef]
        nlinarith [inv_pos.mpr hq₀pos]
      have hbound : ∀ x : ℝ,
          ‖(((x : ℂ) - q.2)⁻¹) ^ m - (((x : ℂ) - q₀.2)⁻¹) ^ m‖ ≤
            m * M ^ (m + 1) * ‖q.2 - q₀.2‖ :=
        fun x => norm_cauchyPow_sub_le m hzq hz₀ hqM hq₀M x
      have hint1 := integrable_cauchyPow (q.1 : Measure ℝ) hzq m
      have hint2 := integrable_cauchyPow (q.1 : Measure ℝ) hz₀ m
      have hFG : Fn q - G q =
          ∫ x, ((((x : ℂ) - q.2)⁻¹) ^ m - (((x : ℂ) - q₀.2)⁻¹) ^ m)
            ∂(q.1 : Measure ℝ) := by
        rw [hFdef, hGdef]
        exact (integral_sub hint1 hint2).symm
      rw [hFG]
      have hle := norm_integral_le_of_norm_le_const
        (μ := (q.1 : Measure ℝ)) (C := (m : ℝ) * M ^ (m + 1) * ‖q.2 - q₀.2‖)
        (f := fun x : ℝ => (((x : ℂ) - q.2)⁻¹) ^ m - (((x : ℂ) - q₀.2)⁻¹) ^ m)
        (Filter.Eventually.of_forall hbound)
      simpa using hle
    · have : Tendsto (fun q : ProbabilityMeasure ℝ × ℂ =>
          (m : ℝ) * M ^ (m + 1) * ‖q.2 - q₀.2‖) (𝓝[S] q₀)
          (𝓝 ((m : ℝ) * M ^ (m + 1) * 0)) :=
        hsnd.const_mul _
      simpa using this
  have hsum := hdiff.add hG
  rw [zero_add] at hsum
  refine hsum.congr fun q => ?_
  ring

/-! ## The packet value as a power transform -/

/-- On off-axis nodes, the expanded packet value is a factorial multiple of a Cauchy power
transform. -/
theorem probabilityCarrierExpandedPacketValue_eq_powerTransform
    {row ι : Type} [Fintype ι]
    (nu : ProbabilityMeasure ℝ) (orders : ι → ℕ)
    (packet : InjectiveProjectiveRowPacket row)
    (shift : InjectiveShiftConfiguration ι)
    (p : row × Fin (Fintype.card (Σ i, Fin (orders i))))
    (hnode : (packet.1 p.1 +
      shift.1 ((Fintype.equivFin (Σ i, Fin (orders i))).symm p.2).1).im ≠ 0) :
    probabilityCarrierExpandedPacketValue nu orders packet shift p =
      ((((Fintype.equivFin (Σ i, Fin (orders i))).symm p.2).2.1.factorial : ℂ)) *
        ∫ x, (((x : ℂ) - (packet.1 p.1 +
            shift.1 ((Fintype.equivFin (Σ i, Fin (orders i))).symm p.2).1))⁻¹) ^
          ((((Fintype.equivFin (Σ i, Fin (orders i))).symm p.2).2.1) + 1)
          ∂(nu : Measure ℝ) := by
  set j := (Fintype.equivFin (Σ i, Fin (orders i))).symm p.2 with hj
  set node := packet.1 p.1 + shift.1 j.1 with hnodedef
  have hzsupport : node ∉ algebraMap ℝ ℂ '' (nu : Measure ℝ).support := by
    rintro ⟨x, _hx, hzx⟩
    have him := congrArg Complex.im hzx
    change ((x : ℂ)).im = node.im at him
    simp only [Complex.ofReal_im] at him
    exact hnode him.symm
  have hactual := iteratedDeriv_resolventTransform (μ := (nu : Measure ℝ)) j.2 node hzsupport
  rw [resolventTransform_def] at hactual
  have hactual' : iteratedDeriv j.2
      (fun u => ∫ x, ((x : ℂ) - u)⁻¹ ∂(nu : Measure ℝ)) node =
      cauchyJetFunction (nu : Measure ℝ) j.2 node := by
    simpa [resolvent] using hactual
  show iteratedDeriv j.2
      (fun z => ∫ x, ((x : ℂ) - z)⁻¹ ∂(nu : Measure ℝ)) node = _
  rw [hactual']
  simp only [cauchyJetFunction, resolventPowerTransform, resolvent, Ring.inverse_eq_inv,
    Complex.coe_algebraMap]

/-- Joint continuity of the expanded packet value on the lower-admissible region. -/
theorem continuousOn_probabilityCarrierExpandedPacketValue
    {row ι : Type} [Fintype ι] [Fintype row] (orders : ι → ℕ)
    (packet : InjectiveProjectiveRowPacket row) :
    ContinuousOn
      (fun q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι =>
        probabilityCarrierExpandedPacketValue q.1 orders packet q.2)
      {q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι |
        ∀ x, (combinedProjectiveRowShiftPacket packet q.2 x).im < 0} := by
  rw [continuousOn_pi]
  intro p
  set j := (Fintype.equivFin (Σ i, Fin (orders i))).symm p.2 with hj
  set A : Set (ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι) :=
    {q | ∀ x, (combinedProjectiveRowShiftPacket packet q.2 x).im < 0} with hA
  have hnodeA : ∀ q ∈ A, (packet.1 p.1 + q.2.1 j.1).im < 0 := by
    intro q hq
    exact hq (p.1, j.1)
  have hnodeMap : Continuous (fun q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι =>
      (q.1, packet.1 p.1 + q.2.1 j.1)) := by
    refine continuous_fst.prodMk ?_
    exact continuous_const.add ((continuous_apply j.1).comp
      (continuous_subtype_val.comp continuous_snd))
  have hmaps : Set.MapsTo (fun q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι =>
      (q.1, packet.1 p.1 + q.2.1 j.1)) A {q : ProbabilityMeasure ℝ × ℂ | q.2.im ≠ 0} := by
    intro q hq
    exact (hnodeA q hq).ne
  have hbase : ContinuousOn
      (fun q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι =>
        ((j.2.1.factorial : ℂ)) *
          ∫ x, (((x : ℂ) - (packet.1 p.1 + q.2.1 j.1))⁻¹) ^ (j.2.1 + 1)
            ∂(q.1 : Measure ℝ)) A := by
    refine continuousOn_const.mul ?_
    exact (continuousOn_cauchyPowerTransform (j.2.1 + 1)).comp
      hnodeMap.continuousOn hmaps
  refine ContinuousOn.congr hbase ?_
  intro q hq
  exact probabilityCarrierExpandedPacketValue_eq_powerTransform q.1 orders packet q.2 p
    (hnodeA q hq).ne

/-! ## Openness of the finite certificate -/

/-- For one fixed packet, the lower-admissible full-rank pairs form an open set. -/
theorem isOpen_lowerAdmissible_fullRank_pairs
    {row ι κ : Type} [Fintype row] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (qdeg : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (packet : InjectiveProjectiveRowPacket row) :
    IsOpen {q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι |
      (∀ x, (combinedProjectiveRowShiftPacket packet q.2 x).im < 0) ∧
      Function.Injective ((expandedDifferentialEvaluationMatrix qdeg
        (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
        (probabilityCarrierExpandedPacketValue q.1 orders packet q.2)).mulVec)} := by
  set A : Set (ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι) :=
    {q | ∀ x, (combinedProjectiveRowShiftPacket packet q.2 x).im < 0} with hA
  have hAopen : IsOpen A := by
    rw [hA, show {q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι |
        ∀ x, (combinedProjectiveRowShiftPacket packet q.2 x).im < 0} =
        ⋂ x, {q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι |
          (combinedProjectiveRowShiftPacket packet q.2 x).im < 0} by
      ext q
      simp]
    apply isOpen_iInter_of_finite
    intro x
    have hcont : Continuous (fun q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι =>
        (combinedProjectiveRowShiftPacket packet q.2 x).im) := by
      apply Complex.continuous_im.comp
      exact continuous_const.add ((continuous_apply x.2).comp
        (continuous_subtype_val.comp continuous_snd))
    exact isOpen_lt hcont continuous_const
  have hset : {q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι |
      (∀ x, (combinedProjectiveRowShiftPacket packet q.2 x).im < 0) ∧
      Function.Injective ((expandedDifferentialEvaluationMatrix qdeg
        (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
        (probabilityCarrierExpandedPacketValue q.1 orders packet q.2)).mulVec)} =
      A ∩ (fun q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι =>
        probabilityCarrierExpandedPacketValue q.1 orders packet q.2) ⁻¹'
          (expandedDifferentialEvaluationRankDefect qdeg
            (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent)ᶜ := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      mem_expandedDifferentialEvaluationRankDefect_iff, not_not, hA]
  rw [hset]
  exact (continuousOn_probabilityCarrierExpandedPacketValue orders packet).isOpen_inter_preimage
    hAopen
    (expandedDifferentialEvaluationFullRank_isOpen qdeg
      (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent)

/-! ## Compact exhaustion of the shift space and the tube lemma -/

/-- Shift configurations with bounded nodes and quantified separation. -/
def shiftExhaustion (ι : Type) [Fintype ι] (m : ℕ) :
    Set (InjectiveShiftConfiguration ι) :=
  {s | (∀ i, ‖s.1 i‖ ≤ m) ∧ ∀ i j, i ≠ j → (1 : ℝ) / (m + 1) ≤ ‖s.1 i - s.1 j‖}

theorem isCompact_shiftExhaustion (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) :
    IsCompact (shiftExhaustion ι m) := by
  rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
  have himage : Subtype.val '' shiftExhaustion ι m =
      {f : ι → ℂ | (∀ i, ‖f i‖ ≤ m) ∧
        ∀ i j, i ≠ j → (1 : ℝ) / (m + 1) ≤ ‖f i - f j‖} := by
    ext f
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hf
      have hinj : Function.Injective f := by
        intro i j hij
        by_contra hne
        have hsep := hf.2 i j hne
        rw [hij, sub_self, norm_zero] at hsep
        have : (0 : ℝ) < 1 / (m + 1) := by positivity
        linarith
      exact ⟨⟨f, hinj⟩, hf, rfl⟩
  rw [himage]
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · have h1 : IsClosed {f : ι → ℂ | ∀ i, ‖f i‖ ≤ (m : ℝ)} := by
      rw [Set.setOf_forall]
      exact isClosed_iInter fun i =>
        isClosed_le ((continuous_apply i).norm) continuous_const
    have h2 : IsClosed {f : ι → ℂ |
        ∀ i j, i ≠ j → (1 : ℝ) / (m + 1) ≤ ‖f i - f j‖} := by
      rw [Set.setOf_forall]
      refine isClosed_iInter fun i => ?_
      rw [Set.setOf_forall]
      refine isClosed_iInter fun j => ?_
      by_cases hij : i = j
      · subst hij
        convert isClosed_univ using 1
        ext f
        simp
      · have hset : {f : ι → ℂ | i ≠ j → (1 : ℝ) / (m + 1) ≤ ‖f i - f j‖} =
            {f : ι → ℂ | (1 : ℝ) / (m + 1) ≤ ‖f i - f j‖} := by
          ext f
          simp [hij]
        rw [hset]
        exact isClosed_le continuous_const
          (((continuous_apply i).sub (continuous_apply j)).norm)
    exact h1.inter h2
  · apply Bornology.IsBounded.subset (Metric.isBounded_closedBall (x := (0 : ι → ℂ))
      (r := m))
    intro f hf
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg (by positivity)]
    exact fun i => by simpa using hf.1 i

/-- Every injective configuration lies in some exhaustion level. -/
theorem exists_mem_shiftExhaustion {ι : Type} [Fintype ι]
    (s : InjectiveShiftConfiguration ι) :
    ∃ m : ℕ, s ∈ shiftExhaustion ι m := by
  classical
  by_cases hempty : IsEmpty ι
  · exact ⟨0, fun i => (hempty.false i).elim, fun i => (hempty.false i).elim⟩
  rw [not_isEmpty_iff] at hempty
  haveI : Nonempty ι := hempty
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ i, ‖s.1 i‖ ≤ B := by
    refine ⟨(Finset.univ : Finset ι).sup' Finset.univ_nonempty
      (fun i : ι => ‖s.1 i‖), ?_⟩
    intro i
    exact Finset.le_sup' (fun i : ι => ‖s.1 i‖) (Finset.mem_univ i)
  by_cases hsub : Nontrivial ι
  · obtain ⟨δ, hδpos, hδ⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ i j, i ≠ j → δ ≤ ‖s.1 i - s.1 j‖ := by
      classical
      set pairs : Finset (ι × ι) := Finset.univ.filter (fun p => p.1 ≠ p.2) with hpairs
      have hne : pairs.Nonempty := by
        obtain ⟨i, j, hij⟩ := hsub
        exact ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
      refine ⟨pairs.inf' hne (fun p => ‖s.1 p.1 - s.1 p.2‖), ?_, ?_⟩
      · rw [Finset.lt_inf'_iff]
        intro p hp
        simp only [hpairs, Finset.mem_filter] at hp
        rw [norm_pos_iff, sub_ne_zero]
        exact fun h => hp.2 (s.2 h)
      · intro i j hij
        have hmem : (i, j) ∈ pairs :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
        exact Finset.inf'_le _ hmem
    obtain ⟨m₁, hm₁⟩ := exists_nat_ge B
    obtain ⟨m₂, hm₂⟩ := exists_nat_ge (1 / δ)
    refine ⟨m₁ + m₂, fun i => le_trans (hB i) (by push_cast; linarith), ?_⟩
    intro i j hij
    refine le_trans ?_ (hδ i j hij)
    rw [div_le_iff₀ (by positivity)]
    have h1δ : 1 / δ ≤ m₂ := hm₂
    rw [div_le_iff₀ hδpos] at h1δ
    push_cast
    nlinarith [norm_nonneg (s.1 i - s.1 j), hδpos.le]
  · obtain ⟨m₁, hm₁⟩ := exists_nat_ge B
    refine ⟨m₁, fun i => le_trans (hB i) hm₁, ?_⟩
    intro i j hij
    exfalso
    rw [not_nontrivial_iff_subsingleton] at hsub
    exact hij (Subsingleton.elim i j)

/-- The universal section of an open set over a compact fibre set is open. -/
theorem isOpen_forall_compact_section {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {G : Set (X × Y)} (hG : IsOpen G) {K : Set Y} (hK : IsCompact K) :
    IsOpen {x : X | ∀ y ∈ K, (x, y) ∈ G} := by
  rw [isOpen_iff_forall_mem_open]
  intro x₀ hx₀
  obtain ⟨u, v, hu, _hv, hxu, hKv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hK hG (by
      rintro ⟨a, b⟩ ⟨ha, hb⟩
      rw [Set.mem_singleton_iff] at ha
      subst ha
      exact hx₀ b hb)
  refine ⟨u, ?_, hu, hxu rfl⟩
  intro x hx y hy
  exact huv ⟨hx, hKv hy⟩

/-! ## The Gδ theorem and the residual free phase -/

/-- **The maximal-translation full-rank phase is a Gδ set** in the weak topology. -/
theorem isGδ_maximalTranslationFullRankWitness :
    IsGδ {nu : ProbabilityMeasure ℝ | MaximalTranslationFullRankWitness nu} := by
  classical
  have hset : {nu : ProbabilityMeasure ℝ | MaximalTranslationFullRankWitness nu} =
      ⋂ (p : FiniteDifferentialPattern Unit), ⋂ (m : ℕ),
        {nu : ProbabilityMeasure ℝ |
          ∀ s ∈ shiftExhaustion (CarrierPatternShift p) m,
            probabilityCarrierExpandedFullRankWitness
              (row := CarrierPatternRow p) nu
              p.coefficientDegree p.orders (carrierPatternExponent p) s} := by
    ext nu
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h p m s _
      exact h p s
    · intro h p s
      obtain ⟨m, hm⟩ := exists_mem_shiftExhaustion s
      exact h p m s hm
  rw [hset]
  refine IsGδ.iInter fun p => IsGδ.iInter fun m => IsOpen.isGδ ?_
  have hG : IsOpen {q : ProbabilityMeasure ℝ ×
      InjectiveShiftConfiguration (CarrierPatternShift p) |
      probabilityCarrierExpandedFullRankWitness
        (row := CarrierPatternRow p) q.1
        p.coefficientDegree p.orders (carrierPatternExponent p) q.2} := by
    have hunion : {q : ProbabilityMeasure ℝ ×
        InjectiveShiftConfiguration (CarrierPatternShift p) |
        probabilityCarrierExpandedFullRankWitness
          (row := CarrierPatternRow p) q.1
          p.coefficientDegree p.orders (carrierPatternExponent p) q.2} =
        ⋃ packet : InjectiveProjectiveRowPacket (CarrierPatternRow p),
          {q : ProbabilityMeasure ℝ ×
            InjectiveShiftConfiguration (CarrierPatternShift p) |
            (∀ x, (combinedProjectiveRowShiftPacket packet q.2 x).im < 0) ∧
            Function.Injective ((expandedDifferentialEvaluationMatrix p.coefficientDegree
              (Fintype.card (Σ i, Fin (p.orders i))) packet.1 (carrierPatternExponent p)
              (probabilityCarrierExpandedPacketValue q.1 p.orders packet q.2)).mulVec)} := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      rfl
    rw [hunion]
    exact isOpen_iUnion fun packet =>
      isOpen_lowerAdmissible_fullRank_pairs p.coefficientDegree p.orders
        (carrierPatternExponent p) packet
  exact isOpen_forall_compact_section hG
    (isCompact_shiftExhaustion (CarrierPatternShift p) m)

/-! ## Finite kernel extraction and the free phase -/

/-- In a finite-dimensional space, a family of submodules with trivial infimum admits a finite
subfamily with trivial infimum, by Artinian descent on finite partial infima. -/
theorem exists_finset_inf_eq_bot_of_iInf_eq_bot {ι : Type*} {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V]
    (W : ι → Submodule ℂ V) (h : ⨅ i, W i = ⊥) :
    ∃ t : Finset ι, t.inf W = ⊥ := by
  classical
  have hS : {U : Submodule ℂ V | ∃ t : Finset ι, U = t.inf W}.Nonempty :=
    ⟨⊤, ∅, by simp⟩
  obtain ⟨U₀, ⟨t₀, hU₀⟩, hmin⟩ :=
    (wellFounded_lt (α := Submodule ℂ V)).has_min _ hS
  refine ⟨t₀, ?_⟩
  have hle : ∀ i, U₀ ≤ W i := by
    intro i
    by_contra hnot
    have hlt : U₀ ⊓ W i < U₀ := by
      rw [lt_iff_le_and_ne]
      refine ⟨inf_le_left, ?_⟩
      intro heq
      apply hnot
      rw [← heq]
      exact inf_le_right
    exact hmin (U₀ ⊓ W i)
      ⟨insert i t₀, by rw [Finset.inf_insert, hU₀, inf_comm]⟩ hlt
  have hbot : U₀ ≤ ⊥ := by
    rw [← h]
    exact le_iInf hle
  rw [← hU₀]
  exact le_antisymm hbot bot_le

/-- The stacked evaluation matrix of a packet tuple. -/
def stackedEvaluationMatrix {row κ ι : Type} [Fintype ι]
    (qdeg : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    {k : ℕ} (tuple : Fin k → InjectiveProjectiveRowPacket row)
    (nu : ProbabilityMeasure ℝ) (shift : InjectiveShiftConfiguration ι) :
    Matrix (Fin k × row) (κ × Fin (qdeg + 1)) ℂ :=
  fun x c => expandedDifferentialEvaluationMatrix qdeg
    (Fintype.card (Σ i, Fin (orders i))) (tuple x.1).1 exponent
    (probabilityCarrierExpandedPacketValue nu orders (tuple x.1) shift) x.2 c

/-- For one fixed packet tuple, the simultaneously admissible stacked full-rank pairs form an
open set. -/
theorem isOpen_lowerAdmissible_stacked_fullRank_pairs
    {row ι κ : Type} [Fintype row] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (qdeg : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    {k : ℕ} (tuple : Fin k → InjectiveProjectiveRowPacket row) :
    IsOpen {q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι |
      (∀ i x, (combinedProjectiveRowShiftPacket (tuple i) q.2 x).im < 0) ∧
      Function.Injective
        ((stackedEvaluationMatrix qdeg orders exponent tuple q.1 q.2).mulVec)} := by
  set A : Set (ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι) :=
    {q | ∀ i x, (combinedProjectiveRowShiftPacket (tuple i) q.2 x).im < 0} with hA
  have hAsub : ∀ i, A ⊆ {q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι |
      ∀ x, (combinedProjectiveRowShiftPacket (tuple i) q.2 x).im < 0} := by
    intro i q hq
    exact hq i
  have hAopen : IsOpen A := by
    rw [hA, show {q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι |
        ∀ i x, (combinedProjectiveRowShiftPacket (tuple i) q.2 x).im < 0} =
        ⋂ (i) (x), {q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι |
          (combinedProjectiveRowShiftPacket (tuple i) q.2 x).im < 0} by
      ext q
      simp]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun x => ?_
    have hcont : Continuous (fun q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι =>
        (combinedProjectiveRowShiftPacket (tuple i) q.2 x).im) := by
      apply Complex.continuous_im.comp
      exact continuous_const.add ((continuous_apply x.2).comp
        (continuous_subtype_val.comp continuous_snd))
    exact isOpen_lt hcont continuous_const
  have hcontStacked : ContinuousOn
      (fun q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι =>
        stackedEvaluationMatrix qdeg orders exponent tuple q.1 q.2) A := by
    rw [continuousOn_iff_continuous_restrict]
    apply continuous_matrix
    intro x c
    have hmat : ContinuousOn
        (fun q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι =>
          expandedDifferentialEvaluationMatrix qdeg
            (Fintype.card (Σ i, Fin (orders i))) (tuple x.1).1 exponent
            (probabilityCarrierExpandedPacketValue q.1 orders (tuple x.1) q.2)) A := by
      exact (continuous_expandedDifferentialEvaluationMatrix qdeg
        (Fintype.card (Σ i, Fin (orders i))) (tuple x.1).1 exponent).comp_continuousOn
        ((continuousOn_probabilityCarrierExpandedPacketValue orders (tuple x.1)).mono
          (hAsub x.1))
    have happly : Continuous (fun M : Matrix row (κ × Fin (qdeg + 1)) ℂ => M x.2 c) :=
      (continuous_apply c).comp (continuous_apply x.2)
    have hcomp := happly.comp_continuousOn hmat
    have hentry : ContinuousOn
        (fun q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι =>
          stackedEvaluationMatrix qdeg orders exponent tuple q.1 q.2 x c) A :=
      ContinuousOn.congr hcomp fun q _ => rfl
    exact continuousOn_iff_continuous_restrict.mp hentry
  have hset : {q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι |
      (∀ i x, (combinedProjectiveRowShiftPacket (tuple i) q.2 x).im < 0) ∧
      Function.Injective
        ((stackedEvaluationMatrix qdeg orders exponent tuple q.1 q.2).mulVec)} =
      A ∩ (fun q : ProbabilityMeasure ℝ × InjectiveShiftConfiguration ι =>
        stackedEvaluationMatrix qdeg orders exponent tuple q.1 q.2) ⁻¹'
          (rectangularRankDefect)ᶜ := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
      mem_rectangularRankDefect_iff_not_injective, not_not, hA]
  rw [hset]
  exact hcontStacked.isOpen_inter_preimage hAopen rectangularRankDefect_isClosed.isOpen_compl

/-- **The tuple-witness form of pointwise relation-freeness.**  All coefficient relations at one
shift die exactly when finitely many simultaneously admissible packets stack to an injective
evaluation matrix. -/
theorem forall_relation_coeff_zero_iff_exists_stacked_witness
    {row ι κ : Type} [Fintype row] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (qdeg : ℕ) (orders : ι → ℕ)
    (exponent : κ → (Fin (Fintype.card (Σ i, Fin (orders i))) →₀ ℕ))
    (nu : ProbabilityMeasure ℝ) (shift : InjectiveShiftConfiguration ι) :
    (∀ coeff : κ × Fin (qdeg + 1) → ℂ,
      probabilityCarrierExpandedPatternRelationHolds (row := row)
        nu qdeg orders exponent shift coeff → ∀ col, coeff col = 0) ↔
    ∃ (k : ℕ) (tuple : Fin k → InjectiveProjectiveRowPacket row),
      (∀ i x, (combinedProjectiveRowShiftPacket (tuple i) shift x).im < 0) ∧
      Function.Injective
        ((stackedEvaluationMatrix qdeg orders exponent tuple nu shift).mulVec) := by
  classical
  constructor
  · intro hfree
    set Adm : Type := {packet : InjectiveProjectiveRowPacket row //
      ∀ x, (combinedProjectiveRowShiftPacket packet shift x).im < 0} with hAdm
    set W : Adm → Submodule ℂ (κ × Fin (qdeg + 1) → ℂ) := fun pk =>
      LinearMap.ker (Matrix.mulVecLin
        (expandedDifferentialEvaluationMatrix qdeg
          (Fintype.card (Σ i, Fin (orders i))) pk.1.1 exponent
          (probabilityCarrierExpandedPacketValue nu orders pk.1 shift))) with hW
    have hbot : ⨅ pk, W pk = ⊥ := by
      rw [eq_bot_iff]
      intro coeff hcoeff
      rw [Submodule.mem_bot]
      have hrel : probabilityCarrierExpandedPatternRelationHolds (row := row)
          nu qdeg orders exponent shift coeff := by
        intro packet hadm r
        have hmem := Submodule.mem_iInf W |>.mp hcoeff ⟨packet, hadm⟩
        rw [hW] at hmem
        have hz := congrFun (LinearMap.mem_ker.mp hmem) r
        rw [Matrix.mulVecLin_apply] at hz
        have hsum : ∑ c, (expandedDifferentialEvaluationMatrix qdeg
            (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
            (probabilityCarrierExpandedPacketValue nu orders packet shift)) r c *
              coeff c = 0 := by
          simpa [Matrix.mulVec, dotProduct] using hz
        calc ∑ col, coeff col * (expandedDifferentialEvaluationMatrix qdeg
            (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
            (probabilityCarrierExpandedPacketValue nu orders packet shift)) r col
            = ∑ col, (expandedDifferentialEvaluationMatrix qdeg
              (Fintype.card (Σ i, Fin (orders i))) packet.1 exponent
              (probabilityCarrierExpandedPacketValue nu orders packet shift)) r col *
                coeff col :=
              Finset.sum_congr rfl fun col _ => mul_comm _ _
          _ = 0 := hsum
      exact funext fun col => hfree coeff hrel col
    obtain ⟨t, ht⟩ := exists_finset_inf_eq_bot_of_iInf_eq_bot W hbot
    refine ⟨t.card, fun i => (t.equivFin.symm i).1.1, ?_, ?_⟩
    · intro i x
      exact (t.equivFin.symm i).1.2 x
    · have hker : LinearMap.ker (Matrix.mulVecLin
          (stackedEvaluationMatrix qdeg orders exponent
            (fun i => (t.equivFin.symm i).1.1) nu shift)) = ⊥ := by
        rw [eq_bot_iff]
        intro coeff hcoeff
        rw [Submodule.mem_bot]
        have hzero := LinearMap.mem_ker.mp hcoeff
        have hall : ∀ pk ∈ t, coeff ∈ W pk := by
          intro pk hpk
          rw [hW, LinearMap.mem_ker]
          funext r
          have hi := congrFun hzero (t.equivFin ⟨pk, hpk⟩, r)
          rw [Matrix.mulVecLin_apply] at hi
          rw [Matrix.mulVecLin_apply]
          rw [show (stackedEvaluationMatrix qdeg orders exponent
              (fun i => (t.equivFin.symm i).1.1) nu shift).mulVec coeff
                (t.equivFin ⟨pk, hpk⟩, r) =
              (expandedDifferentialEvaluationMatrix qdeg
                (Fintype.card (Σ i, Fin (orders i)))
                ((t.equivFin.symm (t.equivFin ⟨pk, hpk⟩)).1.1).1 exponent
                (probabilityCarrierExpandedPacketValue nu orders
                  (t.equivFin.symm (t.equivFin ⟨pk, hpk⟩)).1.1 shift)).mulVec
                coeff r from rfl] at hi
          rw [Equiv.symm_apply_apply] at hi
          exact hi
        have hinf : coeff ∈ t.inf W := Submodule.mem_finsetInf.mpr hall
        rw [ht] at hinf
        exact Submodule.mem_bot ℂ |>.mp hinf
      exact LinearMap.ker_eq_bot.mp hker
  · rintro ⟨k, tuple, hadm, hinj⟩ coeff hrel col
    have hzero : (stackedEvaluationMatrix qdeg orders exponent tuple nu shift).mulVec
        coeff = 0 := by
      funext x
      have hr := hrel (tuple x.1) (hadm x.1) x.2
      have hval : (stackedEvaluationMatrix qdeg orders exponent tuple nu shift).mulVec
          coeff x = ∑ c, (stackedEvaluationMatrix qdeg orders exponent tuple
            nu shift) x c * coeff c := by
        simp [Matrix.mulVec, dotProduct]
      rw [Pi.zero_apply, hval]
      calc ∑ c, (stackedEvaluationMatrix qdeg orders exponent tuple nu shift) x c *
            coeff c
          = ∑ c, coeff c * (stackedEvaluationMatrix qdeg orders exponent tuple
              nu shift) x c :=
            Finset.sum_congr rfl fun c _ => mul_comm _ _
        _ = 0 := hr
    have hcoeff : coeff = 0 := by
      apply hinj
      rw [hzero, Matrix.mulVec_zero]
    rw [hcoeff]
    rfl

/-- **The maximal-translation differential-free phase is a Gδ set** in the weak topology. -/
theorem isGδ_maximalTranslationDifferentialFree :
    IsGδ {nu : ProbabilityMeasure ℝ | MaximalTranslationDifferentialFree nu} := by
  classical
  have hset : {nu : ProbabilityMeasure ℝ | MaximalTranslationDifferentialFree nu} =
      ⋂ (p : FiniteDifferentialPattern Unit), ⋂ (m : ℕ),
        {nu : ProbabilityMeasure ℝ |
          ∀ s ∈ shiftExhaustion (CarrierPatternShift p) m,
            ∀ coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ,
              probabilityCarrierExpandedPatternRelationHolds
                (row := CarrierPatternRow p) nu p.coefficientDegree p.orders
                (carrierPatternExponent p) s coeff → ∀ col, coeff col = 0} := by
    ext nu
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h p m s _ coeff hrel
      exact h p s coeff hrel
    · intro h p s coeff hrel
      obtain ⟨m, hm⟩ := exists_mem_shiftExhaustion s
      exact h p m s hm coeff hrel
  rw [hset]
  refine IsGδ.iInter fun p => IsGδ.iInter fun m => IsOpen.isGδ ?_
  have hG : IsOpen {q : ProbabilityMeasure ℝ ×
      InjectiveShiftConfiguration (CarrierPatternShift p) |
      ∀ coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ,
        probabilityCarrierExpandedPatternRelationHolds
          (row := CarrierPatternRow p) q.1 p.coefficientDegree p.orders
          (carrierPatternExponent p) q.2 coeff → ∀ col, coeff col = 0} := by
    have hunion : {q : ProbabilityMeasure ℝ ×
        InjectiveShiftConfiguration (CarrierPatternShift p) |
        ∀ coeff : CarrierPatternMonomial p × Fin (p.coefficientDegree + 1) → ℂ,
          probabilityCarrierExpandedPatternRelationHolds
            (row := CarrierPatternRow p) q.1 p.coefficientDegree p.orders
            (carrierPatternExponent p) q.2 coeff → ∀ col, coeff col = 0} =
        ⋃ (k : ℕ), ⋃ (tuple : Fin k →
            InjectiveProjectiveRowPacket (CarrierPatternRow p)),
          {q : ProbabilityMeasure ℝ ×
            InjectiveShiftConfiguration (CarrierPatternShift p) |
            (∀ i x, (combinedProjectiveRowShiftPacket (tuple i) q.2 x).im < 0) ∧
            Function.Injective
              ((stackedEvaluationMatrix p.coefficientDegree p.orders
                (carrierPatternExponent p) tuple q.1 q.2).mulVec)} := by
      ext q
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      exact forall_relation_coeff_zero_iff_exists_stacked_witness
        p.coefficientDegree p.orders (carrierPatternExponent p) q.1 q.2
    rw [hunion]
    exact isOpen_iUnion fun k => isOpen_iUnion fun tuple =>
      isOpen_lowerAdmissible_stacked_fullRank_pairs p.coefficientDegree p.orders
        (carrierPatternExponent p) tuple
  exact isOpen_forall_compact_section hG
    (isCompact_shiftExhaustion (CarrierPatternShift p) m)

end

end GaloisForLFunctions.HTGeometry
