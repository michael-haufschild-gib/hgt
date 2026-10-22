import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerGeneralizedZeroJetDescent
import GaloisForLFunctions.HTGeometry.FourierIntegralDilation

/-!
# Exact dilation flow on Meyer cohomology

Right translation in logarithmic radius is multiplicative dilation.  This
file proves that the all-weight target is translation invariant, constructs
the matching Schwartz-source scaling, and proves exact intertwining with the
literal Poisson boundary.  The flow therefore descends to actual Meyer
cohomology.

Paugam's weighted reciprocal involution reverses time with weight `exp(c)`,
and the faithful entire Mellin transform diagonalizes the flow by the
character `exp(s c)`.  These identities supply the flow infrastructure needed
to distinguish a genuine weight-one generalized-jet pairing from a
non-equivariant pointwise determinant.

No topology on the algebraic quotient, RH premise, spectral decomposition, or
numerical computation is used.
-/

open Complex Filter Function Set Topology
open scoped ContDiff FourierTransform SchwartzMap
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

theorem DeningerMeyerStrongLogDecay.translate
    {g : ℝ → ℂ} (hg : DeningerMeyerStrongLogDecay g)
    (c : ℝ) :
    DeningerMeyerStrongLogDecay (fun t => g (t - c)) where
  smooth :=
    hg.smooth.comp
      (contDiff_id.sub contDiff_const)
  decayTop := by
    intro n a
    rw [iteratedDeriv_comp_sub_const]
    have hcomp :=
      (hg.decayTop n a).comp_tendsto
        (tendsto_atTop_add_const_right
          atTop (-c) tendsto_id)
    apply hcomp.trans
    have heq :
        (fun t : ℝ =>
            Real.exp (t - c) ^ (-a)) =
          fun t : ℝ =>
            Real.exp (-c) ^ (-a) *
              Real.exp t ^ (-a) := by
      funext t
      rw [show t - c = (-c) + t by ring,
        Real.exp_add,
        Real.mul_rpow
          (Real.exp_pos (-c)).le
          (Real.exp_pos t).le]
    change
      (fun t : ℝ => Real.exp (t - c) ^ (-a)) =O[atTop]
        fun t : ℝ => Real.exp t ^ (-a)
    rw [heq]
    exact
      Asymptotics.isBigO_const_mul_self
        (Real.exp (-c) ^ (-a))
        (fun t : ℝ => Real.exp t ^ (-a)) atTop
  decayBot := by
    intro n b
    rw [iteratedDeriv_comp_sub_const]
    have hcomp :=
      (hg.decayBot n b).comp_tendsto
        (tendsto_atBot_add_const_right
          atBot (-c) tendsto_id)
    apply hcomp.trans
    have heq :
        (fun t : ℝ =>
            Real.exp (t - c) ^ b) =
          fun t : ℝ =>
            Real.exp (-c) ^ b *
              Real.exp t ^ b := by
      funext t
      rw [show t - c = (-c) + t by ring,
        Real.exp_add,
        Real.mul_rpow
          (Real.exp_pos (-c)).le
          (Real.exp_pos t).le]
    change
      (fun t : ℝ => Real.exp (t - c) ^ b) =O[atBot]
        fun t : ℝ => Real.exp t ^ b
    rw [heq]
    exact
      Asymptotics.isBigO_const_mul_self
        (Real.exp (-c) ^ b)
        (fun t : ℝ => Real.exp t ^ b) atBot

/-- Right translation by flow time `c` on the all-weight logarithmic target. -/
def deningerMeyerStrongLogFlow (c : ℝ) :
    DeningerMeyerStrongLogTarget →ₗ[ℂ]
      DeningerMeyerStrongLogTarget where
  toFun g :=
    ⟨fun t => (g : ℝ → ℂ) (t - c),
      g.property.translate c⟩
  map_add' g h := by
    apply Subtype.ext
    funext t
    rfl
  map_smul' z g := by
    apply Subtype.ext
    funext t
    rfl

@[simp]
theorem deningerMeyerStrongLogFlow_apply
    (c : ℝ) (g : DeningerMeyerStrongLogTarget) (t : ℝ) :
    ((deningerMeyerStrongLogFlow c g :
      DeningerMeyerStrongLogTarget) : ℝ → ℂ) t =
      (g : ℝ → ℂ) (t - c) :=
  rfl

@[simp]
theorem deningerMeyerStrongLogFlow_zero
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogFlow 0 g = g := by
  apply Subtype.ext
  funext t
  simp

theorem deningerMeyerStrongLogFlow_add
    (a b : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogFlow a
        (deningerMeyerStrongLogFlow b g) =
      deningerMeyerStrongLogFlow (a + b) g := by
  apply Subtype.ext
  funext t
  simp only [deningerMeyerStrongLogFlow_apply]
  ring

private def deningerMeyerRealScaleCLE (c : ℝ) : ℝ ≃L[ℝ] ℝ :=
  ContinuousLinearEquiv.smulLeft
    (Units.mk0 (Real.exp (-c))
      (Real.exp_ne_zero (-c)))

private def deningerMeyerSchwartzScale (c : ℝ) :
    SchwartzMap ℝ ℂ →L[ℂ] SchwartzMap ℝ ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (deningerMeyerRealScaleCLE c)

private theorem deningerMeyerSchwartzScale_apply
    (c : ℝ) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    deningerMeyerSchwartzScale c f x =
      f (Real.exp (-c) * x) := by
  rfl

/-- Multiplicative scaling on Meyer's endpoint-zero source. -/
def deningerMeyerCapFlow (c : ℝ) :
    DeningerMeyerCap →ₗ[ℂ] DeningerMeyerCap where
  toFun f := by
    let scaled : SchwartzMap ℝ ℂ :=
      deningerMeyerSchwartzScale c f.val
    refine ⟨scaled, ?_⟩
    rw [deningerMeyerCap_mem_iff]
    have hf :=
      (deningerMeyerCap_mem_iff f.val).mp f.property
    refine ⟨?_, ?_, ?_⟩
    · intro x
      dsimp [scaled]
      rw [deningerMeyerSchwartzScale_apply,
        deningerMeyerSchwartzScale_apply]
      have harg :
          Real.exp (-c) * (-x) =
            -(Real.exp (-c) * x) := by ring
      rw [harg, hf.1]
    · dsimp [scaled]
      rw [deningerMeyerSchwartzScale_apply,
        mul_zero, hf.2.1]
    · dsimp [scaled]
      change
        FourierTransform.fourier
          (fun x : ℝ =>
            f.val (Real.exp (-c) * x)) 0 = 0
      have hfun :
          (fun x : ℝ =>
            f.val (Real.exp (-c) * x)) =
          fun x : ℝ => f.val (x / Real.exp c) := by
        funext x
        congr 1
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero c]
      have hf0 :
          FourierTransform.fourier
            (f.val : ℝ → ℂ) 0 = 0 := by
        rw [← SchwartzMap.fourier_coe]
        exact hf.2.2
      rw [hfun,
        GaloisForLFunctions.HTGeometry.fourierIntegral_comp_div
          f.val (Real.exp c) (Real.exp_pos c) 0,
        mul_zero, hf0]
      simp
  map_add' f g := by
    apply Subtype.ext
    exact (deningerMeyerSchwartzScale c).map_add f.val g.val
  map_smul' z f := by
    apply Subtype.ext
    exact (deningerMeyerSchwartzScale c).map_smul z f.val

@[simp]
theorem deningerMeyerCapFlow_apply
    (c : ℝ) (f : DeningerMeyerCap) (x : ℝ) :
    ((deningerMeyerCapFlow c f :
      DeningerMeyerCap) : SchwartzMap ℝ ℂ) x =
      (f.val : ℝ → ℂ) (Real.exp (-c) * x) :=
  rfl

/-- Logarithmic flow intertwines the literal Poisson boundary with source scaling. -/
@[simp]
theorem deningerMeyerStrongLogFlow_boundary
    (c : ℝ) (f : DeningerMeyerCap) :
    deningerMeyerStrongLogFlow c
        (deningerMeyerStrongLogSumLM f) =
      deningerMeyerStrongLogSumLM
        (deningerMeyerCapFlow c f) := by
  apply Subtype.ext
  funext t
  rw [deningerMeyerStrongLogFlow_apply,
    deningerMeyerStrongLogSumLM_apply,
    deningerMeyerStrongLogSumLM_apply]
  unfold deningerMeyerSum
  apply tsum_congr
  intro n
  rw [deningerMeyerCapFlow_apply]
  congr 1
  rw [Real.exp_sub, Real.exp_neg]
  field_simp [Real.exp_ne_zero c]

theorem deningerMeyerStrongLogFlow_range_le
    (c : ℝ) :
    LinearMap.range deningerMeyerStrongLogSumLM ≤
      (LinearMap.range
        deningerMeyerStrongLogSumLM).comap
          (deningerMeyerStrongLogFlow c) := by
  rintro _ ⟨f, rfl⟩
  exact
    ⟨deningerMeyerCapFlow c f,
      (deningerMeyerStrongLogFlow_boundary c f).symm⟩

/-- Dilation flow descended to the actual all-weight Meyer quotient. -/
def deningerMeyerStrongLogCohomologyFlow (c : ℝ) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ]
      DeningerMeyerStrongLogCohomology :=
  (LinearMap.range
    deningerMeyerStrongLogSumLM).mapQ
      (LinearMap.range
        deningerMeyerStrongLogSumLM)
      (deningerMeyerStrongLogFlow c)
      (deningerMeyerStrongLogFlow_range_le c)

@[simp]
theorem deningerMeyerStrongLogCohomologyFlow_mk
    (c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogCohomologyFlow c
        (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk
        (deningerMeyerStrongLogFlow c g) :=
  rfl

@[simp]
theorem deningerMeyerStrongLogCohomologyFlow_zero
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerStrongLogCohomologyFlow 0 u = u := by
  induction u using Submodule.Quotient.induction_on with
  | _ g =>
      simp

theorem deningerMeyerStrongLogCohomologyFlow_add
    (a b : ℝ) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerStrongLogCohomologyFlow a
        (deningerMeyerStrongLogCohomologyFlow b u) =
      deningerMeyerStrongLogCohomologyFlow (a + b) u := by
  induction u using Submodule.Quotient.induction_on with
  | _ g =>
      simp only [
        deningerMeyerStrongLogCohomologyFlow_mk,
        deningerMeyerStrongLogFlow_add]

/-- Weighted reciprocal inversion reverses flow time with weight `exp(c)`. -/
theorem deningerMeyerStrongLogJ_flow
    (c : ℝ) (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogJ
        (deningerMeyerStrongLogFlow c g) =
      (Real.exp c : ℂ) •
        deningerMeyerStrongLogFlow (-c)
          (deningerMeyerStrongLogJ g) := by
  apply Subtype.ext
  funext t
  simp only [
    deningerMeyerStrongLogJ_apply,
    deningerMeyerStrongLogFlow_apply,
    Submodule.coe_smul,
    Pi.smul_apply,
    smul_eq_mul]
  rw [show -(t - -c) = -t - c by ring]
  rw [← mul_assoc, ← Complex.ofReal_mul,
    ← Real.exp_add]
  congr 2
  ring

theorem deningerMeyerStrongLogCohomologyJ_flow
    (c : ℝ) (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerStrongLogCohomologyJ
        (deningerMeyerStrongLogCohomologyFlow c u) =
      (Real.exp c : ℂ) •
        deningerMeyerStrongLogCohomologyFlow (-c)
          (deningerMeyerStrongLogCohomologyJ u) := by
  induction u using Submodule.Quotient.induction_on with
  | _ g =>
      simp only [
        deningerMeyerStrongLogCohomologyFlow_mk,
        deningerMeyerStrongLogCohomologyJ_mk,
        deningerMeyerStrongLogJ_flow,
        Submodule.Quotient.mk_smul]

/-- The entire logarithmic Mellin transform diagonalizes right translation. -/
theorem deningerMeyerStrongLogMellin_flow
    (c : ℝ) (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogFlow c g) s =
      Complex.exp (s * (c : ℂ)) *
        deningerMeyerStrongLogMellin g s := by
  rw [deningerMeyerStrongLogMellin,
    deningerMeyerStrongLogMellin]
  simp only [
    deningerMeyerStrongLogMellinJet,
    pow_zero, one_mul,
    deningerMeyerStrongLogFlow_apply]
  let F : ℝ → ℂ := fun u =>
    Complex.exp (s * ((u + c : ℝ) : ℂ)) *
      (g : ℝ → ℂ) u
  have hleft :
      (fun t : ℝ =>
        Complex.exp (s * (t : ℂ)) *
          (g : ℝ → ℂ) (t - c)) =
        fun t : ℝ => F (t - c) := by
    funext t
    dsimp [F]
    congr 2
    push_cast
    ring
  rw [hleft, MeasureTheory.integral_sub_right_eq_self F c,
    ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with t
  dsimp [F]
  have hexp :
      Complex.exp (s * ((t + c : ℝ) : ℂ)) =
        Complex.exp (s * (c : ℂ)) *
          Complex.exp (s * (t : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

end

end RHTower
