import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMNativeAngularGreen
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCuspMetricSource
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! Horizontal reflection of the literal theta source and its actual causal response.
The resulting cross-current cancellation does not assert complete radiative extinction. -/
namespace RHTower.D4BMSpatialReflectionCurrent
open MeasureTheory Set
open D4BMNativeCircle D4BMNativeResponse
open scoped ContDiff
noncomputable section
set_option autoImplicit false

theorem fourierPhase_reflection (b : Bool) (N : ℕ) (X : ℝ) :
    d4BMCompletedEisensteinFourierPhase b N (-X) =
      d4BMCompletedEisensteinFourierPhase (!b) N X := by
  cases b <;>
    simp [d4BMCompletedEisensteinFourierPhase, d4BMFourierSign]

theorem signedTail_reflection (u nu : ℂ) (b : Bool) (X Y : ℝ) (j m : ℕ) :
    d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu b (-X) j m Y =
      d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu (!b) X j m Y := by
  simp only [d4BMCompletedEisensteinSignedSqrtWhittakerTail, fourierPhase_reflection]

/-- Both Weyl powers and every signed Fourier mode are retained. -/
theorem literal_scalar_reflection (u : ℂ) (X Y : ℝ) :
    D4BMLiteralCusp.scalar u ![-X,Y] = D4BMLiteralCusp.scalar u ![X,Y] := by
  simp only [D4BMLiteralCusp.scalar, Matrix.cons_val_zero, Matrix.cons_val_one,
    d4BMCompletedEisensteinCuspLeg,
    d4BMCompletedEisensteinCuspTailPart, d4BMCompletedEisensteinFullSignedZeroWord,
    signedTail_reflection, Bool.not_false, Bool.not_true]
  rw [add_comm (d4BMCompletedEisensteinSignedSqrtWhittakerTail u u true X 0 0 Y)]

theorem circle_source_reflection (q : XiZeroCopy) (d theta X k : ℝ) :
    source q d (2*Real.pi-theta) (-X) k = source q d theta X k := by
  have he : logCircle d (2*Real.pi-theta) (-X) k =
      ![-(logCircle d theta X k 0), logCircle d theta X k 1] := by
    ext i
    fin_cases i <;>
      simp [logCircle, circle, offset, height, denominator,
        Real.sin_two_pi_sub, Real.cos_two_pi_sub]
    ring
  change (1/2:ℂ)*(D4BMLiteralCusp.scalar _ (logCircle _ _ _ _) *
    D4BMLiteralCusp.scalar _ (logCircle _ _ _ _)) = _
  rw [he, literal_scalar_reflection]
  rfl

theorem circle_integral_reflection (q : XiZeroCopy) (d X k : ℝ) :
    (∫ theta in (0:ℝ)..2*Real.pi, source q d theta (-X) k) =
      ∫ theta in (0:ℝ)..2*Real.pi, source q d theta X k := by
  calc
    _ = ∫ theta in (0:ℝ)..2*Real.pi,
        source q d (2*Real.pi-theta) (-X) k := by
      simpa using (intervalIntegral.integral_comp_sub_left
        (fun theta => source q d theta (-X) k) (a := 0) (b := 2*Real.pi) (2*Real.pi)).symm
    _ = _ := intervalIntegral.integral_congr (fun theta _ => circle_source_reflection q d theta X k)

theorem circle_mean_reflection (q : XiZeroCopy) (d X k : ℝ) :
    mean q d (-X) k = mean q d X k := by
  unfold mean D4BMNativeCircle.average
  rw [← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi),
    ← intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ 2*Real.pi),
    circle_integral_reflection]

theorem riemann_kernel_reflection (q : XiZeroCopy) (h x y X k : ℝ) :
    nativeRiemannKernel q h x y (-X) k = nativeRiemannKernel q h x y X k :=
  circle_mean_reflection q _ X k

/-- The original causal support, characteristic edges and reflected image remain intact. -/
theorem dirichlet_kernel_reflection (q : XiZeroCopy) (h x y X k : ℝ) :
    nativeDirichletCausalKernel q h x y (-X) k = nativeDirichletCausalKernel q h x y X k := by
  simp only [nativeDirichletCausalKernel, riemann_kernel_reflection]

/-- Reflection is derived from the original full source integral, with its fixed clock. -/
theorem full_response_reflection (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) :
    fullNullResponse q s amplitude p r (-X) k = fullNullResponse q s amplitude p r X k := by
  change (1/4:ℂ)*(∫ a in (0:ℝ)..p, ∫ b in (0:ℝ)..r,
    ((1/(2*Real.pi:ℂ))*(∫ theta in (0:ℝ)..2*Real.pi,
      source q (Real.arcosh (max 1 (D4BMCausalKernel.invariant
        ((p+r-a-b)/2) ((p-r)/2) ((a-b)/2)))) theta (-X) k))*
      oddSource s amplitude ((a+b)/2) ((a-b)/2)) = _
  simp_rw [circle_integral_reflection]
  rfl

theorem residual_reflection (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) :
    fullNullResidual q s amplitude p r (-X) k = fullNullResidual q s amplitude p r X k := by
  simp only [fullNullResidual, full_response_reflection, D4BMJointSource.cutoffPower,
    D4BMGlobalAngularResponse.cutoff, Matrix.cons_val_one]

theorem time_primitive_reflection (q : XiZeroCopy) (s amplitude : ℂ) (t x X k : ℝ) :
    nativeResidualTimePrimitive q s amplitude t x (-X) k =
      nativeResidualTimePrimitive q s amplitude t x X k := by
  simp only [nativeResidualTimePrimitive, residual_reflection]

def scalarLog (u : ℂ) (z : ℝ × ℝ) : ℂ :=
  D4BMLiteralCusp.scalar u ![z.1, Real.exp z.2]

theorem scalar_log_reflection (u : ℂ) (X k : ℝ) :
    scalarLog u (-X,k) = scalarLog u (X,k) := literal_scalar_reflection u X _

theorem scalar_log_smooth (u : ℂ) : ContDiff ℝ ∞ (scalarLog u) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  have hs : ContDiffAt ℝ ∞ (D4BMLiteralCusp.scalar u) ![z.1,Real.exp z.2] :=
    (D4BMAngularSeries.cuspLeg_contDiffOn .scalar u).contDiffAt
      ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds (Real.exp_pos z.2))
  have hc : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ =>
      (![z.1, Real.exp z.2] : Fin 2 → ℝ)) z := by
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i
    · change ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => z.1) z
      exact contDiffAt_fst
    · change ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => Real.exp z.2) z
      exact contDiffAt_snd.exp
  exact hs.comp z hc

private def dx (F : ℝ × ℝ → ℂ) (X k : ℝ) : ℂ := deriv (fun x => F (x,k)) X
private def dk (F : ℝ × ℝ → ℂ) (X k : ℝ) : ℂ := deriv (fun y => F (X,y)) k

private theorem dx_reflection (F : ℝ × ℝ → ℂ)
    (h : ∀ X k, F (-X,k) = F (X,k)) (X k : ℝ) : dx F (-X) k = -dx F X k := by
  have he := deriv_comp_neg (fun x => F (x,k)) X
  simp only [h] at he
  exact neg_eq_iff_eq_neg.mp he.symm

private theorem dk_reflection (F : ℝ × ℝ → ℂ)
    (h : ∀ X k, F (-X,k) = F (X,k)) (X k : ℝ) : dk F (-X) k = dk F X k := by
  simp only [dk, h]

private theorem dx_smooth (F : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => dx F z.1 z.2) := by
  have he (z : ℝ × ℝ) : dx F z.1 z.2 = fderiv ℝ F z (1,0) :=
    ((hf.differentiable (by simp) z).hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv
  simp only [he]
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (hf.contDiffAt.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

private theorem dk_smooth (F : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => dk F z.1 z.2) := by
  have he (z : ℝ × ℝ) : dk F z.1 z.2 = fderiv ℝ F z (0,1) :=
    ((hf.differentiable (by simp) z).hasFDerivAt.comp_hasDerivAt z.2
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv
  simp only [he]
  apply contDiff_iff_contDiffAt.mpr
  intro z
  exact (hf.contDiffAt.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const

private theorem dx_mul (F G : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ F) (hg : ContDiff ℝ ∞ G)
    (X k : ℝ) : dx (fun z => F z*G z) X k = dx F X k*G (X,k)+F (X,k)*dx G X k := by
  have hF := hf.comp (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => k)))
  have hG := hg.comp (contDiff_id.prodMk (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => k)))
  exact deriv_mul (hF.differentiable (by simp) X) (hG.differentiable (by simp) X)

private theorem dk_mul (F G : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ F) (hg : ContDiff ℝ ∞ G)
    (X k : ℝ) : dk (fun z => F z*G z) X k = dk F X k*G (X,k)+F (X,k)*dk G X k := by
  have hF := hf.comp ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => X)).prodMk contDiff_id)
  have hG := hg.comp ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => X)).prodMk contDiff_id)
  exact deriv_mul (hF.differentiable (by simp) k) (hG.differentiable (by simp) k)

private theorem mixed_commute (F : ℝ × ℝ → ℂ) (hf : ContDiff ℝ ∞ F) (X k : ℝ) :
    dx (fun z => dk F z.1 z.2) X k = dk (fun z => dx F z.1 z.2) X k := by
  have hx : (fun z : ℝ × ℝ => dx F z.1 z.2) = fun z => fderiv ℝ F z (1,0) := by
    funext z
    exact ((hf.differentiable (by simp) z).hasFDerivAt.comp_hasDerivAt z.1
      ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))).deriv
  have hk : (fun z : ℝ × ℝ => dk F z.1 z.2) = fun z => fderiv ℝ F z (0,1) := by
    funext z
    exact ((hf.differentiable (by simp) z).hasFDerivAt.comp_hasDerivAt z.2
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))).deriv
  rw [hx,hk]
  have hdf : ContDiffAt ℝ ∞ (fderiv ℝ F) (X,k) :=
    hf.contDiffAt.fderiv_right (m := ∞) (by simp)
  have hd := (hdf.differentiableAt (by simp)).hasFDerivAt
  have hxk := (hd.clm_apply (hasFDerivAt_const ((0,1) : ℝ × ℝ) (X,k))).comp_hasDerivAt X
    ((hasDerivAt_id X).prodMk (hasDerivAt_const X k))
  have hkx := (hd.clm_apply (hasFDerivAt_const ((1,0) : ℝ × ℝ) (X,k))).comp_hasDerivAt k
    ((hasDerivAt_const k X).prodMk (hasDerivAt_id k))
  change deriv (fun x => fderiv ℝ F (x,k) (0,1)) X = deriv (fun y => fderiv ℝ F (X,y) (1,0)) k
  have hxv : deriv (fun x => fderiv ℝ F (x,k) (0,1)) X =
      fderiv ℝ (fderiv ℝ F) (X,k) (1,0) (0,1) := by simpa [Function.comp_def] using hxk.deriv
  have hkv : deriv (fun y => fderiv ℝ F (X,y) (1,0)) k =
      fderiv ℝ (fderiv ℝ F) (X,k) (0,1) (1,0) := by simpa [Function.comp_def] using hkx.deriv
  rw [hxv,hkv]
  exact hf.contDiffAt.isSymmSndFDerivAt
    (by norm_num; exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) (1,0) (0,1)

/-- The cross-eigenvalue current paired with the coexact actual causal response,
in logarithmic height coordinates. Source and reader parameters are independent. -/
def causalCrossWork (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r X k : ℝ) : ℂ :=
  let C : ℝ × ℝ → ℂ := fun z => fullNullResponse q s amplitude p r z.1 z.2
  (scalarLog u (X,k)*dx (scalarLog v) X k-scalarLog v (X,k)*dx (scalarLog u) X k)*dk C X k-
    (scalarLog u (X,k)*dk (scalarLog v) X k-scalarLog v (X,k)*dk (scalarLog u) X k)*dx C X k

theorem causal_cross_work_reflection (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r X k : ℝ) :
    causalCrossWork u v q s amplitude p r (-X) k = -causalCrossWork u v q s amplitude p r X k := by
  dsimp only [causalCrossWork]
  simp only [scalar_log_reflection, dx_reflection _ (scalar_log_reflection u),
    dx_reflection _ (scalar_log_reflection v), dk_reflection _ (scalar_log_reflection u),
    dk_reflection _ (scalar_log_reflection v),
    dx_reflection (fun z => fullNullResponse q s amplitude p r z.1 z.2)
      (full_response_reflection q s amplitude p r),
    dk_reflection (fun z => fullNullResponse q s amplitude p r z.1 z.2)
      (full_response_reflection q s amplitude p r)]
  ring

theorem causal_cross_work_smooth (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r : ℝ) : ContDiff ℝ ∞ (fun z : ℝ × ℝ => causalCrossWork u v q s amplitude p r z.1 z.2) := by
  have hu := scalar_log_smooth u
  have hv := scalar_log_smooth v
  have hc := fullNullResponse_angular_smooth q s amplitude p r
  exact ((hu.mul (dx_smooth _ hv)).sub (hv.mul (dx_smooth _ hu))).mul (dk_smooth _ hc) |>.sub
    (((hu.mul (dk_smooth _ hv)).sub (hv.mul (dk_smooth _ hu))).mul (dx_smooth _ hc))

/-- Admission is proved from the actual source and response, before using parity. -/
theorem causal_cross_work_integrable (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r k l h : ℝ) : IntervalIntegrable (fun X => causalCrossWork u v q s amplitude p r X k)
      volume l h :=
  ((causal_cross_work_smooth u v q s amplitude p r).continuous.comp
    (continuous_id.prodMk continuous_const)).intervalIntegrable l h

/-- Exact cancellation of the admitted cross-eigenvalue work, at every finite slice. -/
theorem causal_cross_work_integral_zero (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r k L : ℝ) : (∫ X in -L..L, causalCrossWork u v q s amplitude p r X k) = 0 := by
  have he := intervalIntegral.integral_comp_neg
    (fun X => causalCrossWork u v q s amplitude p r X k) (a := -L) (b := L)
  simp only [causal_cross_work_reflection, intervalIntegral.integral_neg, neg_neg] at he
  linear_combination -he/2

/-- Every radial, time and height weight factors through this cancellation. -/
theorem weighted_causal_cross_work_integral_zero (u v : ℂ) (q : XiZeroCopy) (s amplitude w : ℂ)
    (p r k L : ℝ) : (∫ X in -L..L, w*causalCrossWork u v q s amplitude p r X k) = 0 := by
  rw [intervalIntegral.integral_const_mul, causal_cross_work_integral_zero, mul_zero]

/-- The distinct coexact/coexact channel is even, so the odd-current argument does
not remove it. This expression includes the original hyperbolic inverse weights. -/
def causalCoexactWork (v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r X k : ℝ) : ℂ :=
  let C : ℝ × ℝ → ℂ := fun z => fullNullResponse q s amplitude p r z.1 z.2
  (Real.exp k:ℂ)^(2 : ℕ)*dx (scalarLog v) X k*dx C X k+dk (scalarLog v) X k*dk C X k

theorem causal_coexact_work_reflection (v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r X k : ℝ) :
    causalCoexactWork v q s amplitude p r (-X) k = causalCoexactWork v q s amplitude p r X k := by
  dsimp only [causalCoexactWork]
  simp only [dx_reflection _ (scalar_log_reflection v), dk_reflection _ (scalar_log_reflection v),
    dx_reflection (fun z => fullNullResponse q s amplitude p r z.1 z.2)
      (full_response_reflection q s amplitude p r),
    dk_reflection (fun z => fullNullResponse q s amplitude p r z.1 z.2)
      (full_response_reflection q s amplitude p r)]
  ring


open GaloisForLFunctions.HTGeometry.ScalarTwoJet

/-- The actual native response in the original upper-half-plane coordinates. -/
def causalField (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) (z : Fin 2 → ℝ) : ℂ :=
  fullNullResponse q s amplitude p r (z 0) (Real.log (z 1))

private theorem causal_field_smooth (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) :
    ContDiffAt ℝ ∞ (causalField q s amplitude p r) ![X,Real.exp k] := by
  have hc : ContDiffAt ℝ ∞ (fun z : Fin 2 → ℝ => (z 0, Real.log (z 1))) ![X,Real.exp k] := by
    apply ContDiffAt.prodMk
    · fun_prop
    · have hY : ContDiffAt ℝ ∞ (fun z : Fin 2 → ℝ => z 1) ![X,Real.exp k] := by fun_prop
      have hl : ContDiffAt ℝ ∞ Real.log (Real.exp k) := Real.contDiffAt_log.mpr (Real.exp_ne_zero k)
      exact hl.comp ![X,Real.exp k] hY
  change ContDiffAt ℝ ∞ ((fun w : ℝ × ℝ => fullNullResponse q s amplitude p r w.1 w.2) ∘
    (fun z : Fin 2 → ℝ => (z 0,Real.log (z 1)))) ![X,Real.exp k]
  exact (fullNullResponse_angular_smooth q s amplitude p r).contDiffAt.comp ![X,Real.exp k] hc

private theorem log_dx (F : (Fin 2 → ℝ) → ℂ) (X k : ℝ)
    (hf : DifferentiableAt ℝ F ![X,Real.exp k]) :
    dx (fun z : ℝ × ℝ => F ![z.1,Real.exp z.2]) X k = coordDeriv 0 F ![X,Real.exp k] := by
  have hp : HasDerivAt (fun x : ℝ => (![x,Real.exp k] : Fin 2 → ℝ)) (Pi.single 0 1) X := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i <;> simp <;> first | exact hasDerivAt_id _ | exact hasDerivAt_const _ _
  exact (hf.hasFDerivAt.comp_hasDerivAt X hp).deriv

private theorem log_dk (F : (Fin 2 → ℝ) → ℂ) (X k : ℝ)
    (hf : DifferentiableAt ℝ F ![X,Real.exp k]) :
    dk (fun z : ℝ × ℝ => F ![z.1,Real.exp z.2]) X k =
      (Real.exp k:ℂ)*coordDeriv 1 F ![X,Real.exp k] := by
  have hp : HasDerivAt (fun y : ℝ => (![X,Real.exp y] : Fin 2 → ℝ))
      (Real.exp k • Pi.single 1 1) k := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i <;> simp <;> first | exact Real.hasDerivAt_exp _ | exact hasDerivAt_const _ _
  have he : fderiv ℝ F ![X,Real.exp k] (Real.exp k • Pi.single 1 1) =
      (Real.exp k:ℂ)*coordDeriv 1 F ![X,Real.exp k] := by
    rw [map_smul, Complex.real_smul]
  exact ((hf.hasFDerivAt.comp_hasDerivAt k hp).congr_deriv he).deriv

/-- Original inverse-metric contraction of the source/reader current with the
coexact native response. All derivatives are actual coordinate derivatives. -/
def physicalCrossWork (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r : ℝ) (z : Fin 2 → ℝ) : ℂ :=
  ∑ i : Fin 2, ∑ j : Fin 2, (D4BMHorizon.metric z)⁻¹ i j*
    (D4BMLiteralCusp.scalar u z*coordDeriv i (D4BMLiteralCusp.scalar v) z-
      D4BMLiteralCusp.scalar v z*coordDeriv i (D4BMLiteralCusp.scalar u) z)*
      D4BMHorizon.coexact (causalField q s amplitude p r) j z

theorem physical_cross_work_log (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r X k : ℝ) : physicalCrossWork u v q s amplitude p r ![X,Real.exp k] =
      (Real.exp k:ℂ)*causalCrossWork u v q s amplitude p r X k := by
  have hu := (D4BMLiteralCusp.scalar_contDiffAt u 1 ![X,Real.exp k]
    (Real.exp_pos k)).differentiableAt (by simp)
  have hv := (D4BMLiteralCusp.scalar_contDiffAt v 1 ![X,Real.exp k]
    (Real.exp_pos k)).differentiableAt (by simp)
  have hc := (causal_field_smooth q s amplitude p r X k).differentiableAt (by simp)
  have hux : dx (scalarLog u) X k = coordDeriv 0 (D4BMLiteralCusp.scalar u) ![X,Real.exp k] :=
    log_dx _ X k hu
  have hvx : dx (scalarLog v) X k = coordDeriv 0 (D4BMLiteralCusp.scalar v) ![X,Real.exp k] :=
    log_dx _ X k hv
  have huk : dk (scalarLog u) X k =
      (Real.exp k:ℂ)*coordDeriv 1 (D4BMLiteralCusp.scalar u) ![X,Real.exp k] := log_dk _ X k hu
  have hvk : dk (scalarLog v) X k =
      (Real.exp k:ℂ)*coordDeriv 1 (D4BMLiteralCusp.scalar v) ![X,Real.exp k] := log_dk _ X k hv
  have hcx : dx (fun z => fullNullResponse q s amplitude p r z.1 z.2) X k =
      coordDeriv 0 (causalField q s amplitude p r) ![X,Real.exp k] := by
    simpa only [causalField, Matrix.cons_val_zero, Matrix.cons_val_one, Real.log_exp] using
      log_dx (causalField q s amplitude p r) X k hc
  have hck : dk (fun z => fullNullResponse q s amplitude p r z.1 z.2) X k =
      (Real.exp k:ℂ)*coordDeriv 1 (causalField q s amplitude p r) ![X,Real.exp k] := by
    simpa only [causalField, Matrix.cons_val_zero, Matrix.cons_val_one, Real.log_exp] using
      log_dk (causalField q s amplitude p r) X k hc
  unfold physicalCrossWork
  rw [D4BMHorizon.metric_inverse _ (Real.exp_pos k)]
  simp only [Fin.sum_univ_two, Matrix.diagonal_apply, Fin.isValue, ↓reduceIte,
    Fin.zero_ne_one, Ne.symm Fin.zero_ne_one,
    D4BMHorizon.coexact, Matrix.cons_val_zero, Matrix.cons_val_one,
    zero_mul, zero_add, add_zero, causalCrossWork, hux, hvx, huk, hvk, hcx, hck]
  dsimp only [scalarLog]
  ring

/-- The original physical contraction is admitted on each finite angular slice. -/
theorem physical_cross_work_integrable (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r k l h : ℝ) : IntervalIntegrable
      (fun X => physicalCrossWork u v q s amplitude p r ![X,Real.exp k]) volume l h := by
  simp_rw [physical_cross_work_log]
  exact (causal_cross_work_integrable u v q s amplitude p r k l h).const_mul _

/-- Extinction of this original physical current, with its changing height weight;
this is not extinction of the complete nonlinear left-QNM action. -/
theorem physical_cross_work_integral_zero (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r k L : ℝ) :
    (∫ X in -L..L, physicalCrossWork u v q s amplitude p r ![X,Real.exp k]) = 0 := by
  simp_rw [physical_cross_work_log]
  exact weighted_causal_cross_work_integral_zero u v q s amplitude _ p r k L

/-- Removing a symmetric inner gap preserves cancellation; this includes the two
horizontal arms of a truncated modular cell below height one. -/
theorem physical_cross_work_paired_slice_zero (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r k l L : ℝ) :
    (∫ X in -L..-l, physicalCrossWork u v q s amplitude p r ![X,Real.exp k])+
      (∫ X in l..L, physicalCrossWork u v q s amplitude p r ![X,Real.exp k]) = 0 := by
  simp_rw [physical_cross_work_log]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, ← mul_add]
  have he := intervalIntegral.integral_comp_neg
    (fun X => causalCrossWork u v q s amplitude p r X k) (a := l) (b := L)
  simp only [causal_cross_work_reflection, intervalIntegral.integral_neg] at he
  rw [← he, neg_add_cancel, mul_zero]

/-- Densitized Stokes flux in logarithmic height, retaining its two components. -/
def boundaryFluxX (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) : ℂ :=
  scalarLog u (X,k)*scalarLog v (X,k)*
    dk (fun z => fullNullResponse q s amplitude p r z.1 z.2) X k

def boundaryFluxK (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ) (p r X k : ℝ) : ℂ :=
  -(scalarLog u (X,k)*scalarLog v (X,k)*
    dx (fun z => fullNullResponse q s amplitude p r z.1 z.2) X k)

/-- Actual source regularity admits every finite boundary segment. -/
theorem boundary_flux_smooth (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ) (p r : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => boundaryFluxX u v q s amplitude p r z.1 z.2) ∧
    ContDiff ℝ ∞ (fun z : ℝ × ℝ => boundaryFluxK u v q s amplitude p r z.1 z.2) := by
  have hST := (scalar_log_smooth u).mul (scalar_log_smooth v)
  have hC := fullNullResponse_angular_smooth q s amplitude p r
  exact ⟨hST.mul (dk_smooth _ hC), (hST.mul (dx_smooth _ hC)).neg⟩

/-- The complete derivative-transfer identity, with the actual Stokes flux. -/
theorem causal_cross_work_stokes (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r X k : ℝ) :
    causalCrossWork u v q s amplitude p r X k =
      -(dx (fun z => boundaryFluxX u v q s amplitude p r z.1 z.2) X k+
        dk (fun z => boundaryFluxK u v q s amplitude p r z.1 z.2) X k)+
      2*scalarLog u (X,k)*
        (dx (scalarLog v) X k*dk (fun z => fullNullResponse q s amplitude p r z.1 z.2) X k-
          dk (scalarLog v) X k*dx (fun z => fullNullResponse q s amplitude p r z.1 z.2) X k) := by
  let C : ℝ × ℝ → ℂ := fun z => fullNullResponse q s amplitude p r z.1 z.2
  have hS := scalar_log_smooth u
  have hT := scalar_log_smooth v
  have hC : ContDiff ℝ ∞ C := fullNullResponse_angular_smooth q s amplitude p r
  have hn (F : ℝ × ℝ → ℂ) : dk (fun z => -F z) X k = -dk F X k := by
    exact deriv.neg
  change causalCrossWork u v q s amplitude p r X k =
    -(dx (fun z => scalarLog u z*scalarLog v z*dk C z.1 z.2) X k+
      dk (fun z => -(scalarLog u z*scalarLog v z*dx C z.1 z.2)) X k)+_
  rw [dx_mul _ _ (hS.mul hT) (dk_smooth _ hC), dx_mul _ _ hS hT, hn,
    dk_mul _ _ (hS.mul hT) (dx_smooth _ hC), dk_mul _ _ hS hT, mixed_commute C hC]
  dsimp only [causalCrossWork, C]
  ring

theorem boundary_flux_x_reflection (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r X k : ℝ) :
    boundaryFluxX u v q s amplitude p r (-X) k = boundaryFluxX u v q s amplitude p r X k := by
  simp only [boundaryFluxX, scalar_log_reflection,
    dk_reflection (fun z => fullNullResponse q s amplitude p r z.1 z.2)
      (full_response_reflection q s amplitude p r)]

theorem boundary_flux_k_reflection (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r X k : ℝ) :
    boundaryFluxK u v q s amplitude p r (-X) k = -boundaryFluxK u v q s amplitude p r X k := by
  simp only [boundaryFluxK, scalar_log_reflection,
    dx_reflection (fun z => fullNullResponse q s amplitude p r z.1 z.2)
      (full_response_reflection q s amplitude p r)]
  ring

theorem boundary_flux_k_integral_zero (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r k L : ℝ) : (∫ X in -L..L, boundaryFluxK u v q s amplitude p r X k) = 0 := by
  have he := intervalIntegral.integral_comp_neg
    (fun X => boundaryFluxK u v q s amplitude p r X k) (a := -L) (b := L)
  simp only [boundary_flux_k_reflection, intervalIntegral.integral_neg, neg_neg] at he
  linear_combination -he/2

/-- All four original oriented edge terms cancel on a symmetric finite rectangle. -/
theorem rectangle_boundary_flux_zero (u v : ℂ) (q : XiZeroCopy) (s amplitude : ℂ)
    (p r L k0 k1 : ℝ) :
    (∫ k in k0..k1, boundaryFluxX u v q s amplitude p r L k-
      boundaryFluxX u v q s amplitude p r (-L) k)+
    (∫ X in -L..L, boundaryFluxK u v q s amplitude p r X k1)-
    (∫ X in -L..L, boundaryFluxK u v q s amplitude p r X k0) = 0 := by
  simp only [boundary_flux_x_reflection, sub_self, intervalIntegral.integral_zero,
    boundary_flux_k_integral_zero, add_zero]

end
end RHTower.D4BMSpatialReflectionCurrent
