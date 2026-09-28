import GaloisForLFunctions.RHTower.SourceInverseTraceIdealNoGo
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantAlgebraicMultiplicity
import GaloisForLFunctions.HTGeometry.EntireDet2HilbertSchmidtContinuity
import GaloisForLFunctions.HTGeometry.VitaliConvergence

/-!
# The relative Fredholm determinant of the Mertens-clock defect

For a Hilbert–Schmidt operator `T` on a Hilbert space with Hilbert basis `b`, the regularized
determinant `det₂(I + T)` is the entire Carleman determinant of the coordinate matrix of `T`
evaluated at `-1`, and for trace-class `T` the Fredholm determinant is
`det(I + T) = det₂(I + T) e^{Tr T}`.  Both vanish exactly when `-1` is an eigenvalue of `T`.

With `A = W + E` (`E` the trace-class Mertens-clock defect), the relative determinant

`D_rel(λ) = det(I + E (W - λ)⁻¹)`

is defined for `λ` off the band `[0, 4] ⊇ σ(W)`.  It is holomorphic there — the finite-section
determinants are holomorphic, locally uniformly bounded by the Carleman bound, and converge
pointwise, so Vitali's theorem applies — and its zeros are exactly the eigenvalues of `A` off the
band, all of which are real and larger than `4`.  The resolvent difference
`(A - λ)⁻¹ - (W - λ)⁻¹ = -(A - λ)⁻¹ E (W - λ)⁻¹` is trace class.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal ComplexConjugate

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section
set_option autoImplicit false

local notation "L²₊" => Lp ℂ 2 halfLineMeasure

/-! ### Regularized and Fredholm determinants in coordinates -/

section Coordinates

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type*} [DecidableEq ι] (b : HilbertBasis ι ℂ H)

/-- The coordinate operator `b.repr ∘ T ∘ b.repr⁻¹` on `ℓ²(ι)`. -/
def coordOp (T : H →L[ℂ] H) : lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  (b.repr.toContinuousLinearEquiv : H →L[ℂ] lp (fun _ : ι => ℂ) 2) ∘L T ∘L
    (b.repr.symm.toContinuousLinearEquiv : lp (fun _ : ι => ℂ) 2 →L[ℂ] H)

omit [CompleteSpace H] [DecidableEq ι] in
theorem coordOp_apply (T : H →L[ℂ] H) (w : lp (fun _ : ι => ℂ) 2) :
    coordOp b T w = b.repr (T (b.repr.symm w)) := rfl

omit [DecidableEq ι] in
theorem isHilbertSchmidt_coordOp {T : H →L[ℂ] H} (hT : ContinuousLinearMap.IsHilbertSchmidt T) :
    ContinuousLinearMap.IsHilbertSchmidt (coordOp b T) :=
  (hT.comp_right _).comp_left _

/-- The coordinate matrix `(i, j) ↦ ⟪b i, T (b j)⟫`. -/
def coordMatrix (T : H →L[ℂ] H) : ι × ι → ℂ := HilbertSchmidt.matrixOf (coordOp b T)

omit [CompleteSpace H] in
theorem coordMatrix_apply (T : H →L[ℂ] H) (p : ι × ι) :
    coordMatrix b T p = inner ℂ (b p.1) (T (b p.2)) := by
  rw [coordMatrix, HilbertSchmidt.matrixOf, coordOp_apply, HilbertBasis.repr_symm_single,
    HilbertBasis.repr_apply_apply]

theorem isHS_coordMatrix {T : H →L[ℂ] H} (hT : ContinuousLinearMap.IsHilbertSchmidt T) :
    HilbertSchmidt.IsHS (coordMatrix b T) :=
  HilbertSchmidt.isHS_matrixOf (isHilbertSchmidt_coordOp b hT)

theorem hsNormSq_coordMatrix_le {T : H →L[ℂ] H} (hT : ContinuousLinearMap.IsHilbertSchmidt T) :
    HilbertSchmidt.hsNormSq (coordMatrix b T) ≤ ContinuousLinearMap.hsNormSq T := by
  have e : HilbertSchmidt.toOperator (isHS_coordMatrix b hT) = coordOp b T :=
    HilbertSchmidt.toOperator_matrixOf (isHilbertSchmidt_coordOp b hT)
  rw [← HilbertSchmidt.hsNormSq_toOperator (isHS_coordMatrix b hT), e]
  have h1 := ContinuousLinearMap.hsNormSq_comp_left_le (hT.comp_right
    (b.repr.symm.toContinuousLinearEquiv : lp (fun _ : ι => ℂ) 2 →L[ℂ] H))
    (b.repr.toContinuousLinearEquiv : H →L[ℂ] lp (fun _ : ι => ℂ) 2)
  have h2 := ContinuousLinearMap.hsNormSq_comp_right_le hT
    (b.repr.symm.toContinuousLinearEquiv : lp (fun _ : ι => ℂ) 2 →L[ℂ] H)
  have hn1 : ‖(b.repr.toContinuousLinearEquiv : H →L[ℂ] lp (fun _ : ι => ℂ) 2)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp
  have hn2 : ‖(b.repr.symm.toContinuousLinearEquiv : lp (fun _ : ι => ℂ) 2 →L[ℂ] H)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by simp
  have hs0 := ContinuousLinearMap.hsNormSq_nonneg (T ∘L
    (b.repr.symm.toContinuousLinearEquiv : lp (fun _ : ι => ℂ) 2 →L[ℂ] H))
  have hT0 := ContinuousLinearMap.hsNormSq_nonneg T
  calc ContinuousLinearMap.hsNormSq (coordOp b T)
      ≤ ‖(b.repr.toContinuousLinearEquiv : H →L[ℂ] lp (fun _ : ι => ℂ) 2)‖ ^ 2 *
          ContinuousLinearMap.hsNormSq (T ∘L
            (b.repr.symm.toContinuousLinearEquiv : lp (fun _ : ι => ℂ) 2 →L[ℂ] H)) := h1
    _ ≤ 1 * ContinuousLinearMap.hsNormSq (T ∘L
            (b.repr.symm.toContinuousLinearEquiv : lp (fun _ : ι => ℂ) 2 →L[ℂ] H)) := by
        gcongr
        nlinarith [norm_nonneg (b.repr.toContinuousLinearEquiv : H →L[ℂ] lp (fun _ : ι => ℂ) 2)]
    _ ≤ 1 * (‖(b.repr.symm.toContinuousLinearEquiv : lp (fun _ : ι => ℂ) 2 →L[ℂ] H)‖ ^ 2 *
          ContinuousLinearMap.hsNormSq T) := by gcongr
    _ ≤ ContinuousLinearMap.hsNormSq T := by
        rw [one_mul]
        have : ‖(b.repr.symm.toContinuousLinearEquiv : lp (fun _ : ι => ℂ) 2 →L[ℂ] H)‖ ^ 2 ≤ 1 := by
          nlinarith [norm_nonneg (b.repr.symm.toContinuousLinearEquiv :
            lp (fun _ : ι => ℂ) 2 →L[ℂ] H)]
        nlinarith

/-- The regularized determinant `det₂(I + T) = det₂(I - (-1) K_T)`. -/
def det2Op (T : H →L[ℂ] H) : ℂ := entireDet2 (coordMatrix b T) (-1)

/-- The Fredholm determinant `det(I + T) = det₂(I + T) e^{Tr T}`. -/
def fredholmDetOp (T : H →L[ℂ] H) : ℂ := det2Op b T * Complex.exp (ContinuousLinearMap.opTrace T)

/-- `det₂(I + T) = 0` exactly when `-1` is an eigenvalue of `T`. -/
theorem det2Op_eq_zero_iff {T : H →L[ℂ] H} (hT : ContinuousLinearMap.IsHilbertSchmidt T) :
    det2Op b T = 0 ↔ ∃ v : H, v ≠ 0 ∧ T v = -v := by
  have e : HilbertSchmidt.toOperator (isHS_coordMatrix b hT) = coordOp b T :=
    HilbertSchmidt.toOperator_matrixOf (isHilbertSchmidt_coordOp b hT)
  rw [det2Op, entireDet2_eq_zero_iff_exists_eigenvector (isHS_coordMatrix b hT)
    (show (-1 : ℂ) ≠ 0 by norm_num), e]
  constructor
  · rintro ⟨w, hw0, hw⟩
    refine ⟨b.repr.symm w, fun h => hw0 (by simpa using congrArg b.repr h), ?_⟩
    have h := congrArg b.repr.symm hw
    rw [coordOp_apply, LinearIsometryEquiv.symm_apply_apply] at h
    rw [h]; simp
  · rintro ⟨v, hv0, hv⟩
    refine ⟨b.repr v, fun h => hv0 (by simpa using congrArg b.repr.symm h), ?_⟩
    rw [coordOp_apply, LinearIsometryEquiv.symm_apply_apply, hv]
    simp

theorem fredholmDetOp_eq_zero_iff {T : H →L[ℂ] H} (hT : ContinuousLinearMap.IsHilbertSchmidt T) :
    fredholmDetOp b T = 0 ↔ ∃ v : H, v ≠ 0 ∧ T v = -v := by
  rw [fredholmDetOp, mul_eq_zero, or_iff_left (Complex.exp_ne_zero _), det2Op_eq_zero_iff b hT]

/-! #### Holomorphic dependence -/

/-- The finite regularized determinant is holomorphic in a holomorphic matrix entry family. -/
theorem differentiableAt_finiteDet2_of_entries {m : Type*} [Fintype m] [DecidableEq m]
    {M : ℂ → Matrix m m ℂ} {z₀ : ℂ} (hM : ∀ i j, DifferentiableAt ℂ (fun z => M z i j) z₀)
    (w : ℂ) : DifferentiableAt ℂ (fun z => finiteDet2 (M z) w) z₀ := by
  unfold finiteDet2
  have hdet : DifferentiableAt ℂ (fun z => (1 + w • M z).det) z₀ := by
    have hrw : (fun z => (1 + w • M z).det) = fun z => ∑ σ : Equiv.Perm m,
        (Equiv.Perm.sign σ : ℂ) * ∏ i, ((if σ i = i then (1 : ℂ) else 0) + w * M z (σ i) i) := by
      funext z
      rw [Matrix.det_apply']
      refine Finset.sum_congr rfl fun σ _ => congrArg _ (Finset.prod_congr rfl fun i _ => ?_)
      simp [Matrix.one_apply]
    rw [hrw]
    refine DifferentiableAt.fun_sum fun σ _ => (differentiableAt_const _).mul ?_
    exact DifferentiableAt.fun_finsetProd fun i _ =>
      (differentiableAt_const _).add ((differentiableAt_const _).mul (hM (σ i) i))
  have htr : DifferentiableAt ℂ (fun z => (M z).trace) z₀ :=
    DifferentiableAt.fun_sum fun i _ => hM i i
  exact hdet.mul ((htr.const_mul w).neg.cexp)

variable [Countable ι] [Nonempty ι]

/-- An exhausting sequence of finite coordinate sets. -/
theorem exists_finset_exhaustion :
    ∃ s : ℕ → Finset ι, Tendsto s atTop atTop := by
  obtain ⟨f, hf⟩ := exists_surjective_nat ι
  classical
  refine ⟨fun N => (Finset.range N).image f, tendsto_atTop_finset_of_monotone ?_ ?_⟩
  · intro a c hac
    exact Finset.image_subset_image (Finset.range_subset_range.mpr hac)
  · intro x
    obtain ⟨n, rfl⟩ := hf x
    exact ⟨n + 1, Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), rfl⟩⟩

/-- **Holomorphy of `det₂(I + E X(z))`** for a Hilbert–Schmidt `E` and a holomorphic operator
family `X`: finite sections, the Carleman bound and Vitali's theorem. -/
theorem differentiableOn_det2Op_comp {E : H →L[ℂ] H} (hE : ContinuousLinearMap.IsHilbertSchmidt E)
    {X : ℂ → H →L[ℂ] H} {U : Set ℂ} (hU : IsOpen U) (hX : DifferentiableOn ℂ X U) :
    DifferentiableOn ℂ (fun z => det2Op b (E ∘L X z)) U := by
  obtain ⟨s, hs⟩ := exists_finset_exhaustion (ι := ι)
  set K : ℂ → ι × ι → ℂ := fun z => coordMatrix b (E ∘L X z) with hKdef
  have hHS : ∀ z, ContinuousLinearMap.IsHilbertSchmidt (E ∘L X z) := fun z => hE.comp_right _
  have hentry : ∀ p : ι × ι, DifferentiableOn ℂ (fun z => K z p) U := by
    intro p
    have hΦ : ∀ z, K z p = ((innerSL ℂ (b p.1)) ∘L E ∘L
        (ContinuousLinearMap.apply ℂ H (b p.2))) (X z) := by
      intro z
      show coordMatrix b (E ∘L X z) p = _
      rw [coordMatrix_apply]
      rfl
    simp_rw [hΦ]
    exact ((innerSL ℂ (b p.1)) ∘L E ∘L (ContinuousLinearMap.apply ℂ H (b p.2))).differentiable
      |>.comp_differentiableOn hX
  set F : ℕ → ℂ → ℂ := fun N z => finiteDet2 (-(HilbertSchmidt.blockMatrix (K z) (s N))) (-1)
    with hFdef
  have hFdiff : ∀ N, DifferentiableOn ℂ (F N) U := by
    intro N z hz
    refine (differentiableAt_finiteDet2_of_entries (M := fun z =>
      -(HilbertSchmidt.blockMatrix (K z) (s N))) (fun i j => ?_) (-1)).differentiableWithinAt
    exact ((hentry ((i : ι), (j : ι))).differentiableAt (hU.mem_nhds hz)).neg
  have hFlim : ∀ z, Tendsto (fun N => F N z) atTop (𝓝 (det2Op b (E ∘L X z))) := fun z =>
    (tendsto_finiteDet2_entireDet2 (isHS_coordMatrix b (hHS z)) (-1)).comp hs
  intro z₀ hz₀
  obtain ⟨R, hR0, hRU⟩ := Metric.isOpen_iff.mp hU z₀ hz₀
  set ρ : ℝ := R / 2 with hρ
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hcb : closedBall z₀ ρ ⊆ U := (closedBall_subset_ball (by rw [hρ]; linarith)).trans hRU
  have hXcont : ContinuousOn X (closedBall z₀ ρ) := hX.continuousOn.mono hcb
  obtain ⟨C, hC⟩ := (isCompact_closedBall z₀ ρ).exists_bound_of_continuousOn hXcont
  have hbd : ∀ N, ∀ z ∈ ball z₀ ρ, ‖F N z‖ ≤
      Real.exp (C ^ 2 * ContinuousLinearMap.hsNormSq E / 2) := by
    intro N z hz
    have hz' : z ∈ closedBall z₀ ρ := ball_subset_closedBall hz
    refine (norm_finiteDet2_le _ _).trans (Real.exp_le_exp.mpr ?_)
    have hneg : matHSNormSq (-(HilbertSchmidt.blockMatrix (K z) (s N))) =
        matHSNormSq (HilbertSchmidt.blockMatrix (K z) (s N)) := by
      simp [matHSNormSq, norm_neg]
    rw [hneg, norm_neg, norm_one, one_pow, one_mul]
    have h1 := HilbertSchmidt.matHSNormSq_blockMatrix_le (isHS_coordMatrix b (hHS z)) (s N)
    have h2 := hsNormSq_coordMatrix_le b (hHS z)
    have h3 := ContinuousLinearMap.hsNormSq_comp_right_le hE (X z)
    have h4 : ‖X z‖ ^ 2 ≤ C ^ 2 := by
      have := hC z hz'
      exact pow_le_pow_left₀ (norm_nonneg _) this 2
    have hE0 := ContinuousLinearMap.hsNormSq_nonneg E
    have h5 : ‖X z‖ ^ 2 * ContinuousLinearMap.hsNormSq E ≤ C ^ 2 * ContinuousLinearMap.hsNormSq E :=
      mul_le_mul_of_nonneg_right h4 hE0
    have : matHSNormSq (HilbertSchmidt.blockMatrix (K z) (s N)) ≤
        C ^ 2 * ContinuousLinearMap.hsNormSq E := by
      calc _ ≤ HilbertSchmidt.hsNormSq (K z) := h1
        _ ≤ ContinuousLinearMap.hsNormSq (E ∘L X z) := h2
        _ ≤ ‖X z‖ ^ 2 * ContinuousLinearMap.hsNormSq E := h3
        _ ≤ _ := h5
    linarith
  obtain ⟨G, hGdiff, hGconv⟩ := vitali_tendstoLocallyUniformlyOn (F := F) (c := z₀) (R := ρ)
    (r := ρ / 4) (z₀ := z₀) (Y := ball z₀ (ρ / 4)) (by positivity) (by linarith)
    (fun N => (hFdiff N).mono ((ball_subset_closedBall).trans hcb)) hbd le_rfl
    (mem_ball_self (by positivity))
    (eventually_nhdsWithin_of_eventually_nhds
      (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))).frequently
    (fun z _ => ⟨_, hFlim z⟩)
  have hGeq : ∀ z ∈ ball z₀ (ρ / 4), G z = det2Op b (E ∘L X z) := fun z hz =>
    tendsto_nhds_unique (hGconv.tendsto_at hz) (hFlim z)
  have hd : DifferentiableOn ℂ (fun z => det2Op b (E ∘L X z)) (ball z₀ (ρ / 4)) :=
    hGdiff.congr fun z hz => (hGeq z hz).symm
  exact (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))).differentiableWithinAt

/-! #### The trace against a trace-class operator -/

/-- `X ↦ Tr(E X)` as a bounded linear functional, `|Tr(E X)| ≤ ‖E‖₁ ‖X‖`. -/
def traceAgainst {E : H →L[ℂ] H} (hE : MemSchattenClass 1 E) : (H →L[ℂ] H) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun X => ContinuousLinearMap.opTrace (E ∘L X)
      map_add' := fun X Y => by
        rw [ContinuousLinearMap.comp_add, opTrace_add_of_memSchattenClass_one
          (memSchattenClass_one_comp_right hE X) (memSchattenClass_one_comp_right hE Y)]
      map_smul' := fun c X => by
        rw [ContinuousLinearMap.comp_smul, opTrace_smul]
        rfl }
    (traceNorm H E) fun X =>
      (norm_opTrace_le_traceNorm (memSchattenClass_one_comp_right hE X)).trans
        (traceNorm_comp_right_le hE.one_summable_approxNumber X)

theorem traceAgainst_apply {E : H →L[ℂ] H} (hE : MemSchattenClass 1 E) (X : H →L[ℂ] H) :
    traceAgainst hE X = ContinuousLinearMap.opTrace (E ∘L X) := rfl

/-- **Holomorphy of the Fredholm determinant `det(I + E X(z))`.** -/
theorem differentiableOn_fredholmDetOp_comp {E : H →L[ℂ] H} (hE : MemSchattenClass 1 E)
    (hEhs : ContinuousLinearMap.IsHilbertSchmidt E) {X : ℂ → H →L[ℂ] H} {U : Set ℂ}
    (hU : IsOpen U) (hX : DifferentiableOn ℂ X U) :
    DifferentiableOn ℂ (fun z => fredholmDetOp b (E ∘L X z)) U := by
  have h1 := differentiableOn_det2Op_comp b hEhs hU hX
  have h2 : DifferentiableOn ℂ (fun z => ContinuousLinearMap.opTrace (E ∘L X z)) U :=
    (traceAgainst hE).differentiable.comp_differentiableOn hX
  exact h1.mul h2.cexp

end Coordinates

/-! ### The band and the resolvent of `W` -/

local instance fact_two_ne_top_relDet : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

instance nontrivial_halfLineL2 : Nontrivial L²₊ :=
  ⟨⟨primeCellVec ⟨2, Nat.prime_two⟩, 0, orthonormal_primeCellVec.ne_zero _⟩⟩

theorem nonneg_wienerHopfSechOp : 0 ≤ wienerHopfSechOp :=
  (ContinuousLinearMap.nonneg_iff_isPositive _).mpr isPositive_wienerHopfSechOp

/-- `σ(W) ⊆ [0, 4]`. -/
theorem spectrum_wienerHopfSechOp_subset : spectrum ℂ wienerHopfSechOp ⊆ weylIntervalZeroFour := by
  intro z hz
  have hre := isSelfAdjoint_wienerHopfSechOp.mem_spectrum_eq_re hz
  have hreal : z.re ∈ spectrum ℝ wienerHopfSechOp := by
    rw [← spectrum.algebraMap_mem_iff ℂ]
    simpa [← hre] using hz
  have h0 : 0 ≤ z.re := spectrum_nonneg_of_nonneg nonneg_wienerHopfSechOp hreal
  have hnorm := (spectrum.norm_le_norm_of_mem hz).trans norm_wienerHopfSechOp_le
  have h4 : z.re ≤ 4 := (Complex.re_le_norm z).trans hnorm
  exact ⟨z.re, ⟨h0, h4⟩, hre.symm⟩

theorem isClosed_weylIntervalZeroFour : IsClosed weylIntervalZeroFour :=
  (isCompact_Icc.image Complex.continuous_ofReal).isClosed

theorem mem_resolventSet_wienerHopfSechOp {z : ℂ} (hz : z ∉ weylIntervalZeroFour) :
    z ∈ resolventSet ℂ wienerHopfSechOp := by
  by_contra h
  exact hz (spectrum_wienerHopfSechOp_subset h)

theorem resolvent_wienerHopfSechOp_mul {z : ℂ} (hz : z ∉ weylIntervalZeroFour) :
    (algebraMap ℂ (L²₊ →L[ℂ] L²₊) z - wienerHopfSechOp) * resolvent wienerHopfSechOp z = 1 := by
  have h := mem_resolventSet_wienerHopfSechOp hz
  rw [spectrum.resolvent_eq h]
  exact h.mul_val_inv

theorem mul_resolvent_wienerHopfSechOp {z : ℂ} (hz : z ∉ weylIntervalZeroFour) :
    resolvent wienerHopfSechOp z * (algebraMap ℂ (L²₊ →L[ℂ] L²₊) z - wienerHopfSechOp) = 1 := by
  have h := mem_resolventSet_wienerHopfSechOp hz
  rw [spectrum.resolvent_eq h]
  exact h.val_inv_mul

/-- `T(λ) = E (W - λ)⁻¹ = -E (λ - W)⁻¹`. -/
def relativeResolventTerm (z : ℂ) : L²₊ →L[ℂ] L²₊ :=
  -(mertensClockDefectOp ∘L resolvent wienerHopfSechOp z)

theorem isHilbertSchmidt_mertensClockDefectOp :
    ContinuousLinearMap.IsHilbertSchmidt mertensClockDefectOp := by
  obtain ⟨S, U, hS, hU, hE⟩ := isTraceClass_mertensStepSechOp_sub
  rw [show mertensClockDefectOp = mertensStepSechOp - wienerHopfSechOp from rfl, hE]
  exact hU.comp_left S

theorem isTraceClass_relativeResolventTerm (z : ℂ) :
    ContinuousLinearMap.IsTraceClass (relativeResolventTerm z) := by
  obtain ⟨S, U, hS, hU, hE⟩ := isTraceClass_mertensStepSechOp_sub
  refine ⟨-S, U ∘L resolvent wienerHopfSechOp z, hS.neg, hU.comp_right _, ?_⟩
  rw [relativeResolventTerm, show mertensClockDefectOp = mertensStepSechOp - wienerHopfSechOp
    from rfl, hE]
  ext v
  simp

theorem memSchattenClass_one_relativeResolventTerm (z : ℂ) :
    MemSchattenClass 1 (relativeResolventTerm z) :=
  IsTraceClass.memSchattenClass_one (isTraceClass_relativeResolventTerm z)

theorem isHilbertSchmidt_relativeResolventTerm (z : ℂ) :
    ContinuousLinearMap.IsHilbertSchmidt (relativeResolventTerm z) :=
  (isHilbertSchmidt_mertensClockDefectOp.comp_right _).neg

/-- The coordinate Hilbert basis of `L²(0, ∞)`. -/
def halfLineBasis : HilbertBasis (exists_hilbertBasis ℂ L²₊).choose ℂ L²₊ :=
  ContinuousLinearMap.hsBasis ℂ L²₊

open scoped Classical in
/-- **The relative Fredholm determinant** `D_rel(λ) = det(I + E (W - λ)⁻¹)`. -/
def relativeDet (z : ℂ) : ℂ := fredholmDetOp halfLineBasis (relativeResolventTerm z)

/-- **Zeros of the relative determinant are the eigenvalues of `A` off the band.** -/
theorem relativeDet_eq_zero_iff {z : ℂ} (hz : z ∉ weylIntervalZeroFour) :
    relativeDet z = 0 ↔ ∃ u : L²₊, u ≠ 0 ∧ mertensStepSechOp u = z • u := by
  classical
  rw [relativeDet, fredholmDetOp_eq_zero_iff _ (isHilbertSchmidt_relativeResolventTerm z)]
  have hR := resolvent_wienerHopfSechOp_mul hz
  have hR' := mul_resolvent_wienerHopfSechOp hz
  have hA : ∀ u, mertensStepSechOp u = mertensClockDefectOp u + wienerHopfSechOp u := by
    intro u; simp [mertensClockDefectOp]
  have hid : ∀ v, z • resolvent wienerHopfSechOp z v - wienerHopfSechOp (resolvent wienerHopfSechOp z v)
      = v := by
    intro v
    have := congrArg (fun X : L²₊ →L[ℂ] L²₊ => X v) hR
    change z • resolvent wienerHopfSechOp z v - wienerHopfSechOp (resolvent wienerHopfSechOp z v)
      = v at this
    exact this
  have hid' : ∀ u, resolvent wienerHopfSechOp z (z • u - wienerHopfSechOp u) = u := by
    intro u
    have := congrArg (fun X : L²₊ →L[ℂ] L²₊ => X u) hR'
    change resolvent wienerHopfSechOp z (z • u - wienerHopfSechOp u) = u at this
    exact this
  constructor
  · rintro ⟨v, hv0, hv⟩
    refine ⟨resolvent wienerHopfSechOp z v, fun h0 => hv0 ?_, ?_⟩
    · rw [← hid v, h0, smul_zero, map_zero, sub_zero]
    · have hv' : mertensClockDefectOp (resolvent wienerHopfSechOp z v) = v := by
        have := congrArg Neg.neg hv
        simpa [relativeResolventTerm] using this
      rw [hA, hv']
      nth_rewrite 1 [← hid v]
      abel
  · rintro ⟨u, hu0, hu⟩
    refine ⟨z • u - wienerHopfSechOp u, fun h0 => hu0 ?_, ?_⟩
    · rw [← hid' u, h0, map_zero]
    · have h1 := hA u
      rw [hu] at h1
      change -(mertensClockDefectOp (resolvent wienerHopfSechOp z (z • u - wienerHopfSechOp u))) =
        -(z • u - wienerHopfSechOp u)
      rw [hid' u, h1]
      abel

/-- The zeros of `D_rel` are real and larger than `4`. -/
theorem relativeDet_zero_real_gt_four {z : ℂ} (hz : z ∉ weylIntervalZeroFour)
    (h0 : relativeDet z = 0) : z.im = 0 ∧ 4 < z.re := by
  obtain ⟨u, hu0, hu⟩ := (relativeDet_eq_zero_iff hz).mp h0
  have hsym := isSelfAdjoint_mertensStepSechOp.isSymmetric
  have hreal := hsym.conj_eigenvalue_eq_self (Module.End.hasEigenvalue_of_hasEigenvector ⟨by
    rw [Module.End.mem_eigenspace_iff]; exact hu, hu0⟩)
  have him : z.im = 0 := by
    have := congrArg Complex.im hreal
    simp at this; linarith
  have hre0 : 0 ≤ z.re := by
    have hpos := re_inner_mertensStepSechOp_nonneg u
    have hkey : (inner ℂ u (mertensStepSechOp u)).re = z.re * ‖u‖ ^ 2 := by
      rw [hu, inner_smul_right, inner_self_eq_norm_sq_to_K]
      simp [Complex.mul_re, him, ← Complex.ofReal_pow]
    rw [hkey] at hpos
    have hn : 0 < ‖u‖ ^ 2 := by
      have := norm_pos_iff.mpr hu0
      positivity
    nlinarith
  refine ⟨him, ?_⟩
  by_contra hle
  push Not at hle
  exact hz ⟨z.re, ⟨hre0, hle⟩, by apply Complex.ext <;> simp [him]⟩

/-! ### Holomorphy of the relative determinant -/

instance countable_halfLineBasisIndex : Countable (exists_hilbertBasis ℂ L²₊).choose :=
  halfLineBasis.orthonormal.countable_index

instance nonempty_halfLineBasisIndex : Nonempty (exists_hilbertBasis ℂ L²₊).choose := by
  by_contra hne
  rw [not_nonempty_iff] at hne
  obtain ⟨v, hv⟩ := exists_ne (0 : L²₊)
  apply hv
  have h0 : halfLineBasis.repr v = 0 := by
    ext i
    exact isEmptyElim i
  simpa using congrArg halfLineBasis.repr.symm h0

theorem differentiableOn_resolvent_wienerHopfSechOp :
    DifferentiableOn ℂ (resolvent wienerHopfSechOp) weylIntervalZeroFourᶜ := fun _ hz =>
  (spectrum.hasDerivAt_resolvent_const_left
    (mem_resolventSet_wienerHopfSechOp hz)).differentiableAt.differentiableWithinAt

theorem relativeResolventTerm_eq (z : ℂ) :
    relativeResolventTerm z = mertensClockDefectOp ∘L (-resolvent wienerHopfSechOp z) := by
  rw [relativeResolventTerm, ContinuousLinearMap.comp_neg]

/-- **The relative determinant is holomorphic off the band.** -/
theorem differentiableOn_relativeDet :
    DifferentiableOn ℂ relativeDet weylIntervalZeroFourᶜ := by
  classical
  have h := differentiableOn_fredholmDetOp_comp halfLineBasis
    memSchattenClass_one_mertensClockDefectOp isHilbertSchmidt_mertensClockDefectOp
    isClosed_weylIntervalZeroFour.isOpen_compl differentiableOn_resolvent_wienerHopfSechOp.neg
  refine h.congr fun z _ => ?_
  rw [relativeDet, relativeResolventTerm_eq]
  congr

theorem analyticOnNhd_relativeDet : AnalyticOnNhd ℂ relativeDet weylIntervalZeroFourᶜ :=
  differentiableOn_relativeDet.analyticOnNhd isClosed_weylIntervalZeroFour.isOpen_compl

/-! ### The resolvent difference is trace class -/

theorem resolvent_sub_resolvent_eq {z : ℂ} (hA : z ∈ resolventSet ℂ mertensStepSechOp)
    (hW : z ∈ resolventSet ℂ wienerHopfSechOp) :
    resolvent mertensStepSechOp z - resolvent wienerHopfSechOp z =
      resolvent mertensStepSechOp z * mertensClockDefectOp * resolvent wienerHopfSechOp z := by
  have hA1 : resolvent mertensStepSechOp z *
      (algebraMap ℂ (L²₊ →L[ℂ] L²₊) z - mertensStepSechOp) = 1 := by
    rw [spectrum.resolvent_eq hA]; exact hA.val_inv_mul
  have hW1 : (algebraMap ℂ (L²₊ →L[ℂ] L²₊) z - wienerHopfSechOp) *
      resolvent wienerHopfSechOp z = 1 := by
    rw [spectrum.resolvent_eq hW]; exact hW.mul_val_inv
  have hE : mertensClockDefectOp = (algebraMap ℂ (L²₊ →L[ℂ] L²₊) z - wienerHopfSechOp) -
      (algebraMap ℂ (L²₊ →L[ℂ] L²₊) z - mertensStepSechOp) := by
    rw [mertensClockDefectOp]; abel
  rw [hE, mul_sub, sub_mul, mul_assoc, hW1, hA1, mul_one, one_mul]

/-- **`(λ - A)⁻¹ - (λ - W)⁻¹` is trace class** wherever both resolvents exist. -/
theorem isTraceClass_resolvent_sub_resolvent {z : ℂ} (hA : z ∈ resolventSet ℂ mertensStepSechOp)
    (hW : z ∈ resolventSet ℂ wienerHopfSechOp) :
    ContinuousLinearMap.IsTraceClass
      (resolvent mertensStepSechOp z - resolvent wienerHopfSechOp z) := by
  obtain ⟨S, U, hS, hU, hE⟩ := isTraceClass_mertensStepSechOp_sub
  refine ⟨resolvent mertensStepSechOp z ∘L S, U ∘L resolvent wienerHopfSechOp z,
    hS.comp_left _, hU.comp_right _, ?_⟩
  rw [resolvent_sub_resolvent_eq hA hW, show mertensClockDefectOp =
    mertensStepSechOp - wienerHopfSechOp from rfl, hE]
  rfl

/-! ### Consequences -/

/-- The factorization `λ - A = (I + T(λ)) (λ - W)` with `T(λ) = -E (λ - W)⁻¹ = E (W - λ)⁻¹`. -/
theorem algebraMap_sub_mertensStepSechOp_eq {z : ℂ} (hz : z ∉ weylIntervalZeroFour) :
    algebraMap ℂ (L²₊ →L[ℂ] L²₊) z - mertensStepSechOp =
      (1 + relativeResolventTerm z) * (algebraMap ℂ (L²₊ →L[ℂ] L²₊) z - wienerHopfSechOp) := by
  have hR := mul_resolvent_wienerHopfSechOp hz
  have hT : relativeResolventTerm z = -(mertensClockDefectOp * resolvent wienerHopfSechOp z) := rfl
  rw [hT, add_mul, one_mul, neg_mul, mul_assoc, hR, mul_one, mertensClockDefectOp]
  abel

open scoped Classical in
/-- Since `Tr E = 0`, the Fredholm determinant of every multiple of `E` equals its second
regularization. -/
theorem fredholmDetOp_smul_mertensClockDefectOp (c : ℂ) :
    fredholmDetOp halfLineBasis (c • mertensClockDefectOp) =
      det2Op halfLineBasis (c • mertensClockDefectOp) := by
  classical
  rw [fredholmDetOp, opTrace_smul, show mertensClockDefectOp = mertensStepSechOp - wienerHopfSechOp
    from rfl, opTrace_mertensStepSechOp_sub, mul_zero, Complex.exp_zero, mul_one]

/-- The relative determinant does not vanish off the real axis. -/
theorem relativeDet_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : relativeDet z ≠ 0 := by
  have hband : z ∉ weylIntervalZeroFour := by
    rintro ⟨x, _, hx⟩
    apply hz
    rw [← hx, Complex.ofReal_im]
  intro h0
  exact hz (relativeDet_zero_real_gt_four hband h0).1

/-- **The zeros of `D_rel` are isolated**: each point off the band has a punctured neighbourhood
free of zeros. -/
theorem eventually_relativeDet_ne_zero {z₀ : ℂ} (hz₀ : z₀ ∉ weylIntervalZeroFour) :
    ∀ᶠ z in 𝓝[≠] z₀, relativeDet z ≠ 0 := by
  rcases (analyticOnNhd_relativeDet z₀ hz₀).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    by_cases him : z₀.im = 0
    swap
    · exact relativeDet_ne_zero_of_im_ne_zero him h.self_of_nhds
    have hseq : Tendsto (fun n : ℕ => z₀ + Complex.I * ((1 : ℂ) / ((n : ℂ) + 1))) atTop (𝓝 z₀) := by
      have h1 : Tendsto (fun n : ℕ => (1 : ℂ) / ((n : ℂ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using (h1.const_mul Complex.I).const_add z₀
    obtain ⟨n, hn⟩ := (hseq.eventually h).exists
    refine relativeDet_ne_zero_of_im_ne_zero ?_ hn
    have : (z₀ + Complex.I * ((1 : ℂ) / ((n : ℂ) + 1))).im = 1 / ((n : ℝ) + 1) := by
      simp [him]
      field_simp
      norm_cast
      simp [Complex.normSq]
      ring_nf
    rw [this]
    positivity
  · exact h

end

end RHTower
