import GaloisForLFunctions.RHTower.Deninger.DeningerTateGraphGreenPrimeSector
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Horizontal residue is invisible to transverse-only graph control

At a pro-log Stein residue chart, evaluating a horizontal character coordinate is an actual
component of the arithmetic Poincare residue.  Normalized one-sided Dirichlet packets have unit
horizontal `L²` mass and aligned evaluation `sqrt N`.  Tensoring them with one fixed transverse
Tate mode leaves every transverse graph-power mass constant.  Therefore no finite family of
transverse graph-power seminorms can bound horizontal residue evaluation.

The theorem is a topology obstruction, not an objection to the existing holomorphic pro-Stein
topology: compact-open/Cauchy seminorms do control evaluation.  It proves that such horizontal
control cannot be discarded when the Tate graph scale is introduced.
-/

namespace RHTower

open Filter

/-- Common coefficient of the normalized one-sided horizontal Dirichlet packet. -/
noncomputable def deningerHorizontalDirichletCoefficient (N : ℕ) : ℝ :=
  (Real.sqrt N)⁻¹

/-- Squared `L²` mass of the normalized horizontal Dirichlet packet. -/
noncomputable def deningerHorizontalDirichletMass (N : ℕ) : ℝ :=
  ∑ _k ∈ Finset.range N, deningerHorizontalDirichletCoefficient N ^ 2

/-- Value of the normalized horizontal Dirichlet packet at its aligned character. -/
noncomputable def deningerHorizontalDirichletEvaluation (N : ℕ) : ℝ :=
  ∑ _k ∈ Finset.range N, deningerHorizontalDirichletCoefficient N

/-- Applying a fixed transverse generator power only rescales horizontal `L²` mass. -/
noncomputable def deningerHorizontalTransversePowerMass
    (lam : ℝ) (m N : ℕ) : ℝ :=
  |lam| ^ (2 * m) * deningerHorizontalDirichletMass N

/-- Nonempty normalized horizontal Dirichlet packets have unit `L²` mass. -/
theorem deningerHorizontalDirichletMass_eq_one {N : ℕ} (hN : 0 < N) :
    deningerHorizontalDirichletMass N = 1 := by
  rw [deningerHorizontalDirichletMass]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [deningerHorizontalDirichletCoefficient, inv_pow]
  nth_rewrite 1 [← Real.sq_sqrt (Nat.cast_nonneg N)]
  exact mul_inv_cancel₀
    (pow_ne_zero 2 (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hN)))

/-- Evaluation at the aligned character has exact size `sqrt N`. -/
theorem deningerHorizontalDirichletEvaluation_eq_sqrt (N : ℕ) :
    deningerHorizontalDirichletEvaluation N = Real.sqrt N := by
  rcases N.eq_zero_or_pos with rfl | hN
  · simp [deningerHorizontalDirichletEvaluation]
  · rw [deningerHorizontalDirichletEvaluation]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [deningerHorizontalDirichletCoefficient]
    nth_rewrite 1 [← Real.sq_sqrt (Nat.cast_nonneg N)]
    rw [pow_two, mul_assoc,
      mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hN)),
      mul_one]

/-- Every fixed transverse graph-power mass is independent of horizontal aperture. -/
theorem deningerHorizontalTransversePowerMass_eq
    (lam : ℝ) (m : ℕ) {N : ℕ} (hN : 0 < N) :
    deningerHorizontalTransversePowerMass lam m N = |lam| ^ (2 * m) := by
  rw [deningerHorizontalTransversePowerMass,
    deningerHorizontalDirichletMass_eq_one hN, mul_one]

/-- Aligned horizontal character evaluation is unbounded. -/
theorem deningerHorizontalDirichletEvaluation_tendsto_atTop :
    Tendsto deningerHorizontalDirichletEvaluation atTop atTop := by
  refine (Real.tendsto_sqrt_atTop.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).congr' ?_
  exact Filter.Eventually.of_forall fun N =>
    (deningerHorizontalDirichletEvaluation_eq_sqrt N).symm

/-- No constant bounds aligned evaluation by normalized horizontal `L²` mass. -/
theorem deningerHorizontalDirichletEvaluation_unbounded
    (C : ℝ) :
    ∃ N : ℕ, 0 < N ∧
      C < deningerHorizontalDirichletEvaluation N ∧
      deningerHorizontalDirichletMass N = 1 := by
  have hlarge :
      ∀ᶠ N : ℕ in atTop, C < deningerHorizontalDirichletEvaluation N :=
    deningerHorizontalDirichletEvaluation_tendsto_atTop.eventually
      (eventually_gt_atTop C)
  have hpositive : ∀ᶠ N : ℕ in atTop, 0 < N :=
    Filter.eventually_atTop.2 ⟨1, fun N hN => hN⟩
  obtain ⟨N, hlargeN, hN⟩ := (hlarge.and hpositive).exists
  exact ⟨N, hN, hlargeN, deningerHorizontalDirichletMass_eq_one hN⟩

/-- Even one fixed transverse graph-power seminorm cannot bound horizontal evaluation. -/
theorem deningerHorizontalEvaluation_not_bounded_by_transversePower
    (lam : ℝ) (m : ℕ) (C : ℝ) :
    ∃ N : ℕ, 0 < N ∧
      C * deningerHorizontalTransversePowerMass lam m N <
        deningerHorizontalDirichletEvaluation N := by
  obtain ⟨N, hN, hlarge, _⟩ :=
    deningerHorizontalDirichletEvaluation_unbounded
      (C * |lam| ^ (2 * m))
  refine ⟨N, hN, ?_⟩
  rw [deningerHorizontalTransversePowerMass_eq lam m hN]
  exact hlarge

/-- No finite family of transverse graph-power masses controls horizontal evaluation. -/
theorem deningerHorizontalEvaluation_not_bounded_by_finiteTransverseProfile
    (lam C : ℝ) (orders : Finset ℕ) :
    ∃ N : ℕ, 0 < N ∧
      C * (∑ m ∈ orders,
        deningerHorizontalTransversePowerMass lam m N) <
          deningerHorizontalDirichletEvaluation N ∧
      ∀ m ∈ orders,
        deningerHorizontalTransversePowerMass lam m N =
          |lam| ^ (2 * m) := by
  obtain ⟨N, hN, hlarge, _⟩ :=
    deningerHorizontalDirichletEvaluation_unbounded
      (C * ∑ m ∈ orders, |lam| ^ (2 * m))
  refine ⟨N, hN, ?_, ?_⟩
  · rw [Finset.sum_congr rfl fun m hm =>
      deningerHorizontalTransversePowerMass_eq lam m hN]
    exact hlarge
  · intro m hm
    exact deningerHorizontalTransversePowerMass_eq lam m hN

/-- Squared evaluation-to-Sobolev ratio of the rank-`d` two-mode tensor cube. -/
noncomputable def deningerRankCubeSobolevEvaluationRatioSq
    (s d : ℕ) : ℝ :=
  (2 : ℝ) ^ d / (d + 1 : ℝ) ^ s

/-- In unbounded horizontal rank, every fixed Sobolev order loses point evaluation. -/
theorem deningerRankCubeSobolevEvaluationRatioSq_tendsto_atTop
    (s : ℕ) :
    Tendsto (deningerRankCubeSobolevEvaluationRatioSq s) atTop atTop := by
  let small : ℕ → ℝ := fun d => (d + 1 : ℝ) ^ s / (2 : ℝ) ^ d
  have hbase :
      Tendsto (fun n : ℕ => (n : ℝ) ^ s / (2 : ℝ) ^ n)
        atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt s one_lt_two
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  have hsmall : Tendsto small atTop (nhds 0) := by
    have hmul :
        Tendsto
          (fun d : ℕ => (2 : ℝ) * ((d + 1 : ℝ) ^ s / (2 : ℝ) ^ (d + 1)))
          atTop (nhds 0) := by
      simpa only [Function.comp_apply, Nat.cast_add, Nat.cast_one, mul_zero] using
        hshift.const_mul (2 : ℝ)
    refine hmul.congr' (Filter.Eventually.of_forall fun d => ?_)
    dsimp [small]
    rw [pow_succ']
    field_simp
  have hpositive : ∀ᶠ d : ℕ in atTop, 0 < small d :=
    Filter.Eventually.of_forall fun d => div_pos (pow_pos (by positivity) _)
      (pow_pos (by positivity) _)
  have hsmallGT : Tendsto small atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsmall, hpositive⟩
  refine hsmallGT.inv_tendsto_nhdsGT_zero.congr' ?_
  exact Filter.Eventually.of_forall fun d => by
    rw [deningerRankCubeSobolevEvaluationRatioSq]
    dsimp [small]
    rw [inv_div]

section HorizontalCirclePacket

open MeasureTheory AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- Alignment coefficient of the horizontal Dirichlet packet at a character point. -/
noncomputable def deningerDirichletCoeff (zeta : AddCircle T) (k : ℕ) : ℂ :=
  (starRingEnd ℂ) (fourier (k : ℤ) zeta)

omit hT in
/-- Every alignment coefficient is unimodular. -/
theorem deningerDirichletCoeff_norm (zeta : AddCircle T) (k : ℕ) :
    ‖deningerDirichletCoeff zeta k‖ = 1 := by
  rw [deningerDirichletCoeff, RCLike.norm_conj, fourier_apply]
  exact Circle.norm_coe _

omit hT in
/-- The alignment coefficient cancels its own character value. -/
theorem deningerDirichletCoeff_mul_fourier (zeta : AddCircle T) (k : ℕ) :
    deningerDirichletCoeff zeta k * fourier (k : ℤ) zeta = 1 := by
  have h : ‖fourier (k : ℤ) zeta‖ = 1 := by
    rw [fourier_apply]; exact Circle.norm_coe _
  rw [deningerDirichletCoeff, RCLike.conj_mul, h]
  norm_num

/-- The aligned horizontal Dirichlet kernel, as a finite character sum in `L²`. -/
noncomputable def deningerDirichletKernelLp (zeta : AddCircle T) (N : ℕ) :
    Lp ℂ 2 (haarAddCircle (T := T)) :=
  ∑ k ∈ Finset.range N, deningerDirichletCoeff zeta k • fourierLp 2 (k : ℤ)

/-- Orthonormality of the characters gives the kernel the exact `L²` norm `√N`. -/
theorem deningerDirichletKernelLp_norm (zeta : AddCircle T) (N : ℕ) :
    ‖deningerDirichletKernelLp zeta N‖ = Real.sqrt N := by
  have horth : Orthonormal ℂ fun k : ℕ => fourierLp (T := T) 2 (k : ℤ) :=
    (orthonormal_fourier (T := T)).comp (fun k : ℕ => (k : ℤ)) Nat.cast_injective
  have hinner :
      (inner ℂ (deningerDirichletKernelLp zeta N) (deningerDirichletKernelLp zeta N)) =
        ((N : ℝ) : ℂ) := by
    rw [deningerDirichletKernelLp,
      horth.inner_sum (deningerDirichletCoeff zeta) (deningerDirichletCoeff zeta)]
    have : ∀ k ∈ Finset.range N,
        (starRingEnd ℂ) (deningerDirichletCoeff zeta k) * deningerDirichletCoeff zeta k =
          (1 : ℂ) := by
      intro k _
      rw [RCLike.conj_mul, deningerDirichletCoeff_norm]
      norm_num
    rw [Finset.sum_congr rfl this]
    simp
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), hinner]
  simp

/-- The normalized aligned horizontal Dirichlet packet, as a continuous function on the circle. -/
noncomputable def deningerDirichletPacket (zeta : AddCircle T) (N : ℕ) : C(AddCircle T, ℂ) :=
  ((Real.sqrt N : ℝ) : ℂ)⁻¹ •
    ∑ k ∈ Finset.range N, deningerDirichletCoeff zeta k • fourier (k : ℤ)

omit hT in
/-- **Aligned evaluation.**  The packet takes the value `√N` at its alignment point. -/
theorem deningerDirichletPacket_eval_self (zeta : AddCircle T) (N : ℕ) :
    deningerDirichletPacket zeta N zeta = ((Real.sqrt N : ℝ) : ℂ) := by
  have hsum : (∑ k ∈ Finset.range N,
      deningerDirichletCoeff zeta k • fourier (k : ℤ) : C(AddCircle T, ℂ)) zeta =
      ((N : ℝ) : ℂ) := by
    simp only [ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
      smul_eq_mul]
    rw [Finset.sum_congr rfl fun k _ => deningerDirichletCoeff_mul_fourier zeta k]
    simp
  rw [deningerDirichletPacket, ContinuousMap.smul_apply, hsum, smul_eq_mul]
  rcases N.eq_zero_or_pos with rfl | hN
  · simp
  · have hpos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
    have hne : ((Real.sqrt N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have hsq : ((Real.sqrt N : ℝ) : ℂ) * ((Real.sqrt N : ℝ) : ℂ) = ((N : ℝ) : ℂ) := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ))
        (Real.mul_self_sqrt (Nat.cast_nonneg N))
    rw [← hsq, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- The packet's `L²` class is the normalized Dirichlet kernel. -/
theorem deningerDirichletPacket_toLp (zeta : AddCircle T) (N : ℕ) :
    ContinuousMap.toLp 2 (haarAddCircle (T := T)) ℂ (deningerDirichletPacket zeta N) =
      ((Real.sqrt N : ℝ) : ℂ)⁻¹ • deningerDirichletKernelLp zeta N := by
  rw [deningerDirichletPacket, deningerDirichletKernelLp, map_smul, map_sum]
  exact congrArg _ (Finset.sum_congr rfl fun k _ => map_smul _ _ _)

/-- **Unit mass.**  Nonempty normalized horizontal Dirichlet packets are `L²`-unit vectors. -/
theorem deningerDirichletPacket_norm_toLp {N : ℕ} (hN : 0 < N) (zeta : AddCircle T) :
    ‖ContinuousMap.toLp 2 (haarAddCircle (T := T)) ℂ (deningerDirichletPacket zeta N)‖ = 1 := by
  have hpos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  rw [deningerDirichletPacket_toLp, norm_smul, deningerDirichletKernelLp_norm,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
    inv_mul_cancel₀ hpos.ne']

end HorizontalCirclePacket

section TransverseTensorGraph

open MeasureTheory AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The elementary tensor of a horizontal function with one fixed transverse mode. -/
noncomputable def deningerTransverseTensor (f : C(AddCircle T, ℂ)) (eta : E) :
    C(AddCircle T, E) :=
  ⟨fun z => f z • eta, f.continuous.smul continuous_const⟩

omit hT in
@[simp]
theorem deningerTransverseTensor_apply (f : C(AddCircle T, ℂ)) (eta : E) (z : AddCircle T) :
    deningerTransverseTensor f eta z = f z • eta :=
  rfl

/-- The `L²` norm of a continuous field is the `L²` norm of its class. -/
theorem deningerToLp_norm (g : C(AddCircle T, E)) :
    ‖ContinuousMap.toLp 2 (haarAddCircle (T := T)) ℂ g‖ =
      (eLpNorm g 2 (haarAddCircle (T := T))).toReal := by
  rw [Lp.norm_def]
  exact congrArg ENNReal.toReal
    (eLpNorm_congr_ae (ContinuousMap.coeFn_toLp (haarAddCircle (T := T)) g))

/-- An elementary tensor factorizes its `L²` norm. -/
theorem deningerTransverseTensor_norm_toLp (f : C(AddCircle T, ℂ)) (eta : E) :
    ‖ContinuousMap.toLp 2 (haarAddCircle (T := T)) ℂ (deningerTransverseTensor f eta)‖ =
      ‖eta‖ * ‖ContinuousMap.toLp 2 (haarAddCircle (T := T)) ℂ f‖ := by
  have hnorm : eLpNorm (fun z => f z • eta) 2 (haarAddCircle (T := T)) =
      eLpNorm ((‖eta‖ : ℝ) • fun z => f z) 2 (haarAddCircle (T := T)) := by
    refine eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun z => ?_)
    rw [norm_smul, Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg eta),
      mul_comm]
  rw [deningerToLp_norm, deningerToLp_norm]
  show (eLpNorm (fun z => f z • eta) 2 (haarAddCircle (T := T))).toReal = _
  rw [hnorm, eLpNorm_const_smul, ENNReal.toReal_mul]
  simp

/-- The transverse graph monomial acting on a continuous field. -/
noncomputable def deningerTransverseFieldPower (A : E →L[ℂ] E) (m : ℕ)
    (u : C(AddCircle T, E)) : C(AddCircle T, E) :=
  ⟨fun z => (A ^ m) (u z), (A ^ m).continuous.comp u.continuous⟩

/-- A transverse eigenvector stays an eigenvector of every graph monomial. -/
theorem deningerTransverseEigen_pow {A : E →L[ℂ] E} {lam : ℂ} {eta : E}
    (heta : A eta = lam • eta) (m : ℕ) : (A ^ m) eta = lam ^ m • eta := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hstep : (A ^ (m + 1)) eta = (A ^ m) (A eta) := by
      rw [pow_succ]; rfl
    rw [hstep, heta, map_smul, ih, smul_smul, pow_succ, mul_comm]

omit hT in
/-- The transverse generator acts on an elementary tensor through its transverse factor only. -/
theorem deningerTransverseFieldPower_tensor {A : E →L[ℂ] E} {lam : ℂ} {eta : E}
    (heta : A eta = lam • eta) (m : ℕ) (f : C(AddCircle T, ℂ)) :
    deningerTransverseFieldPower A m (deningerTransverseTensor f eta) =
      deningerTransverseTensor (lam ^ m • f) eta := by
  refine ContinuousMap.ext fun z => ?_
  show (A ^ m) (f z • eta) = (lam ^ m * f z) • eta
  rw [map_smul, deningerTransverseEigen_pow heta, smul_smul, mul_comm]

/-- **Transverse graph blindness.**  Every transverse graph-power mass of the aligned packet
tensor is independent of the horizontal aperture `N`. -/
theorem deningerTransverseGraphPower_norm_dirichletPacket
    {A : E →L[ℂ] E} {lam : ℂ} {eta : E} (heta : A eta = lam • eta) (hetaNorm : ‖eta‖ = 1)
    (m : ℕ) {N : ℕ} (hN : 0 < N) (zeta : AddCircle T) :
    ‖ContinuousMap.toLp 2 (haarAddCircle (T := T)) ℂ
        (deningerTransverseFieldPower A m
          (deningerTransverseTensor (deningerDirichletPacket zeta N) eta))‖ =
      ‖lam‖ ^ m := by
  rw [deningerTransverseFieldPower_tensor heta, deningerTransverseTensor_norm_toLp,
    hetaNorm, one_mul, map_smul, norm_smul, deningerDirichletPacket_norm_toLp hN,
    mul_one, norm_pow]

omit hT in
/-- **Aligned residue evaluation.**  The same tensor has evaluation norm `√N`. -/
theorem deningerTransverseTensor_eval_norm_dirichletPacket
    {eta : E} (hetaNorm : ‖eta‖ = 1) (N : ℕ) (zeta : AddCircle T) :
    ‖deningerTransverseTensor (deningerDirichletPacket zeta N) eta zeta‖ = Real.sqrt N := by
  rw [deningerTransverseTensor_apply, norm_smul, hetaNorm, mul_one,
    deningerDirichletPacket_eval_self, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]

/-- **The no-go.**  No constant multiple of any finite family of transverse graph-power
seminorms dominates aligned horizontal residue evaluation. -/
theorem deningerHorizontalResidue_not_bounded_by_transverseGraph
    {A : E →L[ℂ] E} {lam : ℂ} {eta : E} (heta : A eta = lam • eta) (hetaNorm : ‖eta‖ = 1)
    (C : ℝ) (orders : Finset ℕ) (zeta : AddCircle T) :
    ∃ N : ℕ, 0 < N ∧
      C * ∑ m ∈ orders,
          ‖ContinuousMap.toLp 2 (haarAddCircle (T := T)) ℂ
            (deningerTransverseFieldPower A m
              (deningerTransverseTensor (deningerDirichletPacket zeta N) eta))‖ <
        ‖deningerTransverseTensor (deningerDirichletPacket zeta N) eta zeta‖ := by
  obtain ⟨N, hN, hlarge, -⟩ :=
    deningerHorizontalDirichletEvaluation_unbounded (C * ∑ m ∈ orders, ‖lam‖ ^ m)
  refine ⟨N, hN, ?_⟩
  rw [deningerTransverseTensor_eval_norm_dirichletPacket hetaNorm,
    Finset.sum_congr rfl fun m _ =>
      deningerTransverseGraphPower_norm_dirichletPacket heta hetaNorm m hN zeta]
  rwa [deningerHorizontalDirichletEvaluation_eq_sqrt] at hlarge

end TransverseTensorGraph

end RHTower
