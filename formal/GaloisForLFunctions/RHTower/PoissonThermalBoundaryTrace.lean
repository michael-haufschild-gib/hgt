import GaloisForLFunctions.RHTower.PoissonThermalTraceClassLift
import GaloisForLFunctions.RHTower.TraceClassCyclicity

/-!
# The half-line boundary trace anomaly

The full-line multipliers `m` and `m'` commute, but their half-line compressions
`W = P₊ W_full P₊` and `J = P₊ J_full P₊` do not.  Writing `h(u) = sech²(u/2)`, `j(u) = u h(u)`,
the commutator kernel is

`[W, W_j](y, z) = ∫_{b > 0} ((y + b) h(y + b) h(z + b) + h(y + b) (z + b) h(z + b)) db`,

i.e. `[W, W_j] = P Q* + Q P*` with the Hilbert–Schmidt Hankel operators `P(y,b) = j(y + b)`,
`Q(y,b) = h(y + b)`.  Hence `[W, J] = i [W, W_j]` is trace class with

`tr [W, J] = 2i ∫₀^∞ u² h(u)² du = i/(2π) ∫_ℝ |m'(ξ)|² dξ ≠ 0`.

The prime pair `A = U K U*`, `C = U C_P U*` differs from `(W, J)` by trace-class operators, and
`tr [A, C] = tr [W, J]` by cyclicity of the trace against bounded factors.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Filter Set Topology Real
open scoped ENNReal NNReal

namespace RHTower

open GaloisForLFunctions.HTGeometry

local notation "L²₊" => Lp ℂ 2 halfLineMeasure

/-! ### The real kernel identity -/

theorem integrable_sechSqHalfTilt : Integrable sechSqHalfTilt := by
  refine integrable_abs_mul_sechSqHalf.mono' continuous_sechSqHalfTilt.aestronglyMeasurable
    (Eventually.of_forall fun s => ?_)
  rw [Real.norm_eq_abs, sechSqHalfTilt, abs_mul, abs_of_pos (sechSqHalf_pos s)]

theorem norm_sechSqHalf_le_one (s : ℝ) : ‖sechSqHalf s‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (sechSqHalf_pos s)]; exact sechSqHalf_le_one s

/-- **The commutator kernel of the Wiener–Hopf compressions.**  For all `y, z`,
`∫_{a ≥ 0} h(y-a) j(a-z) - ∫_{a ≥ 0} j(y-a) h(a-z)
  = ∫_{b ≥ 0} j(y+b) h(z+b) + ∫_{b ≥ 0} h(y+b) j(z+b)`. -/
theorem wienerHopf_commutator_kernel (y z : ℝ) :
    (∫ a in Ici 0, sechSqHalf (y - a) * sechSqHalfTilt (a - z)) -
        ∫ a in Ici 0, sechSqHalfTilt (y - a) * sechSqHalf (a - z) =
      (∫ b in Ici 0, sechSqHalfTilt (y + b) * sechSqHalf (z + b)) +
        ∫ b in Ici 0, sechSqHalf (y + b) * sechSqHalfTilt (z + b) := by
  set F : ℝ → ℝ := fun a => sechSqHalf (y - a) * sechSqHalfTilt (a - z) with hFdef
  set G : ℝ → ℝ := fun a => sechSqHalfTilt (y - a) * sechSqHalf (a - z) with hGdef
  have hF : Integrable F :=
    (integrable_sechSqHalfTilt.comp_sub_right z).bdd_mul
      (continuous_sechSqHalf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun a => norm_sechSqHalf_le_one _)
  have hG' : Integrable fun a => sechSqHalf (a - z) * sechSqHalfTilt (y - a) :=
    (integrable_sechSqHalfTilt.comp_sub_left y).bdd_mul
      (continuous_sechSqHalf.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun a => norm_sechSqHalf_le_one _)
  have hG : Integrable G := hG'.congr (Eventually.of_forall fun a => by simp only [G]; ring)
  have hFG : ∫ a, F a = ∫ a, G a := by
    rw [← integral_sub_left_eq_self F (μ := volume) (y + z)]
    congr 1
    funext a
    simp only [F, G]
    rw [show y - (y + z - a) = a - z by ring, show y + z - a - z = y - a by ring, mul_comm]
  have hsF := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hF
  have hsG := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hG
  rw [compl_Ioi] at hsF hsG
  have hnF : ∫ a in Iic 0, F a = ∫ b in Ioi 0, F (-b) := by
    rw [integral_comp_neg_Ioi 0 F, neg_zero]
  have hnG : ∫ a in Iic 0, G a = ∫ b in Ioi 0, G (-b) := by
    rw [integral_comp_neg_Ioi 0 G, neg_zero]
  have hGn : IntegrableOn (fun b => G (-b)) (Ioi 0) := hG.comp_neg.integrableOn
  have hFn : IntegrableOn (fun b => F (-b)) (Ioi 0) := hF.comp_neg.integrableOn
  have hR1 : IntegrableOn (fun b => sechSqHalfTilt (y + b) * sechSqHalf (z + b)) (Ioi 0) := by
    refine Integrable.integrableOn ?_
    have := (integrable_sechSqHalfTilt.comp_add_left y).bdd_mul (c := 1)
      (continuous_sechSqHalf.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun b => norm_sechSqHalf_le_one (z + b))
    exact this.congr (Eventually.of_forall fun b => by
      simp only [Function.comp_apply, Pi.add_apply, id_eq]; ring)
  have hR2 : IntegrableOn (fun b => sechSqHalf (y + b) * sechSqHalfTilt (z + b)) (Ioi 0) := by
    refine Integrable.integrableOn ?_
    exact (integrable_sechSqHalfTilt.comp_add_left z).bdd_mul (c := 1)
      (continuous_sechSqHalf.comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (Eventually.of_forall fun b => norm_sechSqHalf_le_one (y + b))
  rw [integral_Ici_eq_integral_Ioi, integral_Ici_eq_integral_Ioi, integral_Ici_eq_integral_Ioi,
    integral_Ici_eq_integral_Ioi]
  have e1 : (∫ a in Ioi 0, F a) - ∫ a in Ioi 0, G a =
      (∫ b in Ioi 0, G (-b)) - ∫ b in Ioi 0, F (-b) := by
    linarith [hsF, hsG, hFG, hnF, hnG]
  change (∫ a in Ioi 0, F a) - ∫ a in Ioi 0, G a = _
  rw [e1, ← integral_sub hGn hFn, ← integral_add hR1 hR2]
  refine integral_congr_ae (Eventually.of_forall fun b => ?_)
  simp only [F, G]
  rw [show y - -b = y + b by ring, show -b - z = -(z + b) by ring, sechSqHalf_neg,
    sechSqHalfTilt_neg]
  ring

/-! ### Hankel kernels -/

/-- The Hankel kernel `g(y + b)` on the half-line of an integrable measurable profile. -/
def hankelKernel (g : ℝ → ℝ) (hgm : Measurable g) (hg : Integrable g) :
    SchurKernel halfLineMeasure where
  toFun y b := (g (y + b) : ℂ)
  measurable := Complex.measurable_ofReal.comp (hgm.comp (measurable_fst.add measurable_snd))
  bound := (∫⁻ u, ‖(g u : ℂ)‖ₑ).toNNReal
  row y := by
    have hfin : ∫⁻ u, ‖(g u : ℂ)‖ₑ ≠ ⊤ := hg.ofReal.2.ne
    refine (setLIntegral_le_lintegral _ _).trans ?_
    rw [lintegral_add_left_eq_self (fun u => ‖(g u : ℂ)‖ₑ) y, ENNReal.coe_toNNReal hfin]
  col b := by
    have hfin : ∫⁻ u, ‖(g u : ℂ)‖ₑ ≠ ⊤ := hg.ofReal.2.ne
    refine (setLIntegral_le_lintegral _ _).trans ?_
    rw [lintegral_add_right_eq_self (fun u => ‖(g u : ℂ)‖ₑ) b, ENNReal.coe_toNNReal hfin]

theorem hankelKernel_toFun (g : ℝ → ℝ) (hgm : Measurable g) (hg : Integrable g) (y b : ℝ) :
    (hankelKernel g hgm hg).toFun y b = (g (y + b) : ℂ) := rfl

/-- A Hankel kernel with exponential decay on `[0, ∞)` is square integrable. -/
theorem hankelKernel_sq_lt_top (g : ℝ → ℝ) (hgm : Measurable g) (hg : Integrable g) {M α : ℝ}
    (hα : 0 < α) (hb : ∀ u, 0 ≤ u → |g u| ≤ M * Real.exp (-(α * u))) :
    ∫⁻ y, ∫⁻ b, ‖(hankelKernel g hgm hg).toFun y b‖ₑ ^ 2 ∂halfLineMeasure ∂halfLineMeasure < ∞ := by
  set E : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-((2 * α) * t)))
  have hpt : ∀ y ∈ Ici (0 : ℝ), ∀ b ∈ Ici (0 : ℝ),
      ‖(hankelKernel g hgm hg).toFun y b‖ₑ ^ 2 ≤ ENNReal.ofReal (M ^ 2) * E y * E b := by
    intro y hy b hb'
    have hu : 0 ≤ y + b := add_nonneg hy hb'
    rw [hankelKernel_toFun, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := hb (y + b) hu
    have hM : 0 ≤ M := by
      have := (abs_nonneg _).trans h1
      exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
    calc |g (y + b)| ^ 2 ≤ (M * Real.exp (-(α * (y + b)))) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = M ^ 2 * Real.exp (-((2 * α) * y)) * Real.exp (-((2 * α) * b)) := by
          rw [mul_pow, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
          congr 2
          push_cast
          ring
  have hE : ∫⁻ t in Ici 0, E t < ∞ := lintegral_Ici_ofReal_exp_neg_lt_top (by positivity)
  calc ∫⁻ y, ∫⁻ b, ‖(hankelKernel g hgm hg).toFun y b‖ₑ ^ 2 ∂halfLineMeasure ∂halfLineMeasure
      ≤ ∫⁻ y in Ici 0, ∫⁻ b in Ici 0, ENNReal.ofReal (M ^ 2) * E y * E b := by
        refine setLIntegral_mono' measurableSet_Ici fun y hy => ?_
        exact setLIntegral_mono' measurableSet_Ici fun b hb' => hpt y hy b hb'
    _ = ∫⁻ y in Ici 0, (ENNReal.ofReal (M ^ 2) * E y) * ∫⁻ b in Ici 0, E b := by
        refine lintegral_congr fun y => ?_
        exact lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
    _ = ENNReal.ofReal (M ^ 2) * (∫⁻ y in Ici 0, E y) * ∫⁻ b in Ici 0, E b := by
        rw [lintegral_mul_const' _ _ hE.ne, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ∞ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE) hE

/-- `P(y, b) = j(y + b)`. -/
def boundaryTiltKernel : SchurKernel halfLineMeasure :=
  hankelKernel sechSqHalfTilt continuous_sechSqHalfTilt.measurable integrable_sechSqHalfTilt

/-- `Q(y, b) = h(y + b)`. -/
def boundarySechKernel : SchurKernel halfLineMeasure :=
  hankelKernel sechSqHalf measurable_sechSqHalf integrable_sechSqHalf

theorem boundaryTiltKernel_sq_lt_top :
    ∫⁻ y, ∫⁻ b, ‖boundaryTiltKernel.toFun y b‖ₑ ^ 2 ∂halfLineMeasure ∂halfLineMeasure < ∞ :=
  hankelKernel_sq_lt_top _ _ _ (M := 8) (α := 1 / 2) (by norm_num) fun u hu => by
    have := abs_sechSqHalfTilt_le u
    rwa [abs_of_nonneg hu] at this

theorem boundarySechKernel_sq_lt_top :
    ∫⁻ y, ∫⁻ b, ‖boundarySechKernel.toFun y b‖ₑ ^ 2 ∂halfLineMeasure ∂halfLineMeasure < ∞ :=
  hankelKernel_sq_lt_top _ _ _ (M := 4) (α := 1) one_pos fun u hu => by
    have := abs_sechSqHalf_le u
    rwa [abs_of_nonneg hu] at this

/-! ### `[W, W_j] = P Q* + Q P*` -/

/-- **The half-line commutator.**  `W W_j - W_j W = P Q* + Q P*`. -/
theorem wienerHopf_commutator_eq :
    wienerHopfSechOp ∘L wienerHopfTiltOp - wienerHopfTiltOp ∘L wienerHopfSechOp =
      boundaryTiltKernel.op ∘L ContinuousLinearMap.adjoint boundarySechKernel.op +
        boundarySechKernel.op ∘L ContinuousLinearMap.adjoint boundaryTiltKernel.op := by
  rw [SchurKernel.adjoint_op, SchurKernel.adjoint_op, wienerHopfSechOp, wienerHopfTiltOp,
    ← SchurKernel.comp_op, ← SchurKernel.comp_op, ← SchurKernel.comp_op, ← SchurKernel.comp_op,
    ← SchurKernel.sub_op, ← SchurKernel.add_op]
  refine SchurKernel.op_eq_of_ae (Eventually.of_forall fun y => Eventually.of_forall fun z => ?_)
  change (∫ a in Ici 0, ((sechSqHalf (y - a) : ℝ) : ℂ) * ((sechSqHalfTilt (a - z) : ℝ) : ℂ)) -
      (∫ a in Ici 0, ((sechSqHalfTilt (y - a) : ℝ) : ℂ) * ((sechSqHalf (a - z) : ℝ) : ℂ)) =
    (∫ b in Ici 0, ((sechSqHalfTilt (y + b) : ℝ) : ℂ) *
        (starRingEnd ℂ) ((sechSqHalf (z + b) : ℝ) : ℂ)) +
      ∫ b in Ici 0, ((sechSqHalf (y + b) : ℝ) : ℂ) *
        (starRingEnd ℂ) ((sechSqHalfTilt (z + b) : ℝ) : ℂ)
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, integral_complex_ofReal]
  exact_mod_cast wienerHopf_commutator_kernel y z

/-! ### Trace class and trace -/

local instance fact_two_ne_top_boundaryTrace : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

private theorem memSchattenClass_one_add' {S T : L²₊ →L[ℂ] L²₊} (hS : MemSchattenClass 1 S)
    (hT : MemSchattenClass 1 T) : MemSchattenClass 1 (S + T) :=
  memSchattenClass_one_add (hS.isCompactOperator one_pos) (hT.isCompactOperator one_pos) hS hT

private theorem memSchattenClass_one_sub' {S T : L²₊ →L[ℂ] L²₊} (hS : MemSchattenClass 1 S)
    (hT : MemSchattenClass 1 T) : MemSchattenClass 1 (S - T) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ T]
  exact memSchattenClass_one_add' hS (memSchattenClass_one_smul hT _)

theorem isHilbertSchmidt_boundaryTilt : ContinuousLinearMap.IsHilbertSchmidt boundaryTiltKernel.op :=
  boundaryTiltKernel.isHilbertSchmidt_op boundaryTiltKernel_sq_lt_top

theorem isHilbertSchmidt_boundarySech : ContinuousLinearMap.IsHilbertSchmidt boundarySechKernel.op :=
  boundarySechKernel.isHilbertSchmidt_op boundarySechKernel_sq_lt_top

theorem memSchattenClass_one_boundaryTilt_comp :
    MemSchattenClass 1 (boundaryTiltKernel.op ∘L ContinuousLinearMap.adjoint boundarySechKernel.op) :=
  memSchattenClass_one_comp isHilbertSchmidt_boundaryTilt isHilbertSchmidt_boundarySech.adjoint

theorem memSchattenClass_one_boundarySech_comp :
    MemSchattenClass 1 (boundarySechKernel.op ∘L ContinuousLinearMap.adjoint boundaryTiltKernel.op) :=
  memSchattenClass_one_comp isHilbertSchmidt_boundarySech isHilbertSchmidt_boundaryTilt.adjoint

/-- `[W, W_j]` is trace class. -/
theorem memSchattenClass_one_wienerHopf_commutator :
    MemSchattenClass 1
      (wienerHopfSechOp ∘L wienerHopfTiltOp - wienerHopfTiltOp ∘L wienerHopfSechOp) := by
  rw [wienerHopf_commutator_eq]
  exact memSchattenClass_one_add' memSchattenClass_one_boundaryTilt_comp
    memSchattenClass_one_boundarySech_comp

theorem opTrace_boundaryTilt_comp :
    ContinuousLinearMap.opTrace
        (boundaryTiltKernel.op ∘L ContinuousLinearMap.adjoint boundarySechKernel.op) =
      ((∫ y in Ici 0, ∫ z in Ici 0, sechSqHalfTilt (z + y) * sechSqHalf (z + y) : ℝ) : ℂ) := by
  rw [SchurKernel.adjoint_op, SchurKernel.opTrace_comp_op _ _ boundaryTiltKernel_sq_lt_top
    ((SchurKernel.lintegral_adjoint_sq _).trans_lt boundarySechKernel_sq_lt_top)]
  change (∫ y in Ici 0, ∫ z in Ici 0, ((sechSqHalfTilt (z + y) : ℝ) : ℂ) *
    (starRingEnd ℂ) ((sechSqHalf (z + y) : ℝ) : ℂ)) = _
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, integral_complex_ofReal]

theorem opTrace_boundarySech_comp :
    ContinuousLinearMap.opTrace
        (boundarySechKernel.op ∘L ContinuousLinearMap.adjoint boundaryTiltKernel.op) =
      ((∫ y in Ici 0, ∫ z in Ici 0, sechSqHalfTilt (z + y) * sechSqHalf (z + y) : ℝ) : ℂ) := by
  rw [SchurKernel.adjoint_op, SchurKernel.opTrace_comp_op _ _ boundarySechKernel_sq_lt_top
    ((SchurKernel.lintegral_adjoint_sq _).trans_lt boundaryTiltKernel_sq_lt_top)]
  change (∫ y in Ici 0, ∫ z in Ici 0, ((sechSqHalf (z + y) : ℝ) : ℂ) *
    (starRingEnd ℂ) ((sechSqHalfTilt (z + y) : ℝ) : ℂ)) = _
  simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, integral_complex_ofReal, mul_comm]

/-- `tr [W, W_j] = 2 ∫_{y,z ≥ 0} j(y+z) h(y+z)`. -/
theorem opTrace_wienerHopf_commutator :
    ContinuousLinearMap.opTrace
        (wienerHopfSechOp ∘L wienerHopfTiltOp - wienerHopfTiltOp ∘L wienerHopfSechOp) =
      2 * ((∫ y in Ici 0, ∫ z in Ici 0, sechSqHalfTilt (z + y) * sechSqHalf (z + y) : ℝ) : ℂ) := by
  rw [wienerHopf_commutator_eq, opTrace_add_of_memSchattenClass_one
    memSchattenClass_one_boundaryTilt_comp memSchattenClass_one_boundarySech_comp,
    opTrace_boundaryTilt_comp, opTrace_boundarySech_comp]
  ring

/-! ### The double integral over the quadrant -/

/-- **Tonelli on the quadrant:** `∫_{y ≥ 0} ∫_{z ≥ 0} F(z + y) = ∫_{u ≥ 0} u F(u)`. -/
theorem lintegral_Ici_lintegral_Ici_add {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ y in Ici 0, ∫⁻ z in Ici 0, F (z + y) = ∫⁻ u in Ici 0, ENNReal.ofReal u * F u := by
  have hin : ∀ y : ℝ, ∫⁻ z in Ici 0, F (z + y) = ∫⁻ u, (Ici y).indicator F u := by
    intro y
    rw [← lintegral_indicator measurableSet_Ici,
      ← lintegral_add_right_eq_self ((Ici y).indicator F) y]
    refine lintegral_congr fun z => ?_
    by_cases hz : 0 ≤ z
    · rw [Set.indicator_of_mem (show z ∈ Ici (0 : ℝ) from hz),
        Set.indicator_of_mem (show z + y ∈ Ici y by simp [mem_Ici, hz])]
    · rw [Set.indicator_of_notMem (show z ∉ Ici (0 : ℝ) from hz),
        Set.indicator_of_notMem (show z + y ∉ Ici y by simp [mem_Ici]; linarith)]
  set S : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ p.2} with hSdef
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_fst).inter (measurableSet_le measurable_fst measurable_snd)
  have hK : Measurable (S.indicator fun p : ℝ × ℝ => F p.2) := (hF.comp measurable_snd).indicator hS
  have hout : ∫⁻ y in Ici 0, ∫⁻ z in Ici 0, F (z + y) =
      ∫⁻ y, ∫⁻ u, S.indicator (fun p : ℝ × ℝ => F p.2) (y, u) := by
    simp_rw [hin]
    rw [← lintegral_indicator measurableSet_Ici]
    refine lintegral_congr fun y => ?_
    by_cases hy : 0 ≤ y
    · rw [Set.indicator_of_mem (show y ∈ Ici (0 : ℝ) from hy)]
      refine lintegral_congr fun u => ?_
      by_cases hu : y ≤ u
      · rw [Set.indicator_of_mem (show u ∈ Ici y from hu),
          Set.indicator_of_mem (show (y, u) ∈ S from ⟨hy, hu⟩)]
      · rw [Set.indicator_of_notMem (show u ∉ Ici y from hu),
          Set.indicator_of_notMem (show (y, u) ∉ S from fun h => hu h.2)]
    · rw [Set.indicator_of_notMem (show y ∉ Ici (0 : ℝ) from hy)]
      symm
      refine lintegral_eq_zero_iff' (by fun_prop) |>.mpr (Eventually.of_forall fun u => ?_)
      show S.indicator (fun p : ℝ × ℝ => F p.2) (y, u) = 0
      rw [Set.indicator_of_notMem (show (y, u) ∉ S from fun h => hy h.1)]
  rw [hout, lintegral_lintegral_swap (show AEMeasurable (Function.uncurry fun y u =>
    S.indicator (fun p : ℝ × ℝ => F p.2) (y, u)) (volume.prod volume) from hK.aemeasurable)]
  have hslice : ∀ u : ℝ, ∫⁻ y, S.indicator (fun p : ℝ × ℝ => F p.2) (y, u) =
      ENNReal.ofReal u * F u := by
    intro u
    have e : (fun y => S.indicator (fun p : ℝ × ℝ => F p.2) (y, u)) =
        (Icc 0 u).indicator fun _ => F u := by
      funext y
      by_cases h : 0 ≤ y ∧ y ≤ u
      · rw [Set.indicator_of_mem (show (y, u) ∈ S from h),
          Set.indicator_of_mem (show y ∈ Icc 0 u from h)]
      · rw [Set.indicator_of_notMem (show (y, u) ∉ S from h),
          Set.indicator_of_notMem (show y ∉ Icc 0 u from h)]
    rw [e, lintegral_indicator_const measurableSet_Icc, Real.volume_Icc, sub_zero, mul_comm]
  simp_rw [hslice]
  rw [← lintegral_indicator measurableSet_Ici]
  refine lintegral_congr fun u => ?_
  by_cases hu : 0 ≤ u
  · rw [Set.indicator_of_mem (show u ∈ Ici (0 : ℝ) from hu)]
  · rw [Set.indicator_of_notMem (show u ∉ Ici (0 : ℝ) from hu),
      ENNReal.ofReal_of_nonpos (le_of_not_ge hu), zero_mul]

/-- The real form: `∫_{y ≥ 0} ∫_{z ≥ 0} G(z + y) = ∫_{u ≥ 0} u G(u)` for continuous `G ≥ 0` on
`[0, ∞)` with integrable first moment. -/
theorem integral_Ici_integral_Ici_add {G : ℝ → ℝ} (hGc : Continuous G)
    (hG0 : ∀ u, 0 ≤ u → 0 ≤ G u) (hint : IntegrableOn (fun u => u * G u) (Ici 0))
    (hinner : ∀ y, 0 ≤ y → IntegrableOn (fun z => G (z + y)) (Ici 0)) :
    ∫ y in Ici 0, ∫ z in Ici 0, G (z + y) = ∫ u in Ici 0, u * G u := by
  have hmeas : Measurable fun u => ENNReal.ofReal (G u) := ENNReal.measurable_ofReal.comp hGc.measurable
  have hinnerEq : ∀ y ∈ Ici (0 : ℝ), ENNReal.ofReal (∫ z in Ici 0, G (z + y)) =
      ∫⁻ z in Ici 0, ENNReal.ofReal (G (z + y)) := by
    intro y hy
    refine ofReal_integral_eq_lintegral_ofReal (hinner y hy) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ici] with z hz
    exact hG0 _ (add_nonneg hz hy)
  have hsm : AEStronglyMeasurable (fun y => ∫ z in Ici 0, G (z + y)) (volume.restrict (Ici 0)) := by
    have h := (hGc.comp (continuous_snd.add continuous_fst)).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ici (0 : ℝ)))
    exact h.aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae _ hsm, integral_eq_lintegral_of_nonneg_ae]
  · congr 1
    rw [setLIntegral_congr_fun measurableSet_Ici hinnerEq,
      lintegral_Ici_lintegral_Ici_add hmeas]
    refine setLIntegral_congr_fun measurableSet_Ici fun u hu => ?_
    rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ u from hu)]
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with u hu
    exact mul_nonneg hu (hG0 u hu)
  · exact hint.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
    refine setIntegral_nonneg measurableSet_Ici fun z hz => hG0 _ (add_nonneg hz hy)

/-! ### The anomaly constant -/

/-- The boundary anomaly `∫₀^∞ u² h(u)² du`. -/
def boundaryAnomaly : ℝ := ∫ u in Ici 0, u ^ 2 * sechSqHalf u ^ 2

theorem abs_sechSqHalfTilt_le_eight (u : ℝ) : |sechSqHalfTilt u| ≤ 8 := by
  refine (abs_sechSqHalfTilt_le u).trans ?_
  have : Real.exp (-((1 / 2) * |u|)) ≤ 1 := Real.exp_le_one_iff.mpr (by
    have := abs_nonneg u; linarith)
  linarith

theorem sq_mul_sechSqHalf_sq_le (u : ℝ) : |u ^ 2 * sechSqHalf u ^ 2| ≤ 8 * (|u| * sechSqHalf u) := by
  have hj := abs_sechSqHalfTilt_le_eight u
  rw [sechSqHalfTilt, abs_mul, abs_of_pos (sechSqHalf_pos u)] at hj
  have hh := (sechSqHalf_pos u).le
  rw [abs_of_nonneg (by positivity)]
  calc u ^ 2 * sechSqHalf u ^ 2 = (|u| * sechSqHalf u) * (|u| * sechSqHalf u) := by
        rw [← sq_abs u]; ring
    _ ≤ 8 * (|u| * sechSqHalf u) := by
        gcongr

theorem integrable_sq_mul_sechSqHalf_sq : Integrable fun u : ℝ => u ^ 2 * sechSqHalf u ^ 2 :=
  (integrable_abs_mul_sechSqHalf.const_mul 8).mono'
    ((continuous_pow 2).mul (continuous_sechSqHalf.pow 2)).aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact sq_mul_sechSqHalf_sq_le u)

/-- **`tr [W, W_j] = 2 ∫₀^∞ u² h(u)² du`.** -/
theorem opTrace_wienerHopf_commutator_eq_anomaly :
    ContinuousLinearMap.opTrace
        (wienerHopfSechOp ∘L wienerHopfTiltOp - wienerHopfTiltOp ∘L wienerHopfSechOp) =
      2 * (boundaryAnomaly : ℂ) := by
  rw [opTrace_wienerHopf_commutator]
  congr 2
  have hGc : Continuous fun u => sechSqHalfTilt u * sechSqHalf u :=
    continuous_sechSqHalfTilt.mul continuous_sechSqHalf
  have hG0 : ∀ u, 0 ≤ u → 0 ≤ sechSqHalfTilt u * sechSqHalf u := fun u hu => by
    rw [sechSqHalfTilt]; have := (sechSqHalf_pos u).le; positivity
  have hint : IntegrableOn (fun u => u * (sechSqHalfTilt u * sechSqHalf u)) (Ici 0) := by
    refine Integrable.integrableOn (integrable_sq_mul_sechSqHalf_sq.congr
      (Eventually.of_forall fun u => ?_))
    simp only [sechSqHalfTilt]; ring
  have hinner : ∀ y, 0 ≤ y → IntegrableOn (fun z => sechSqHalfTilt (z + y) * sechSqHalf (z + y))
      (Ici 0) := fun y _ =>
    ((integrable_sechSqHalfTilt.comp_add_right y).mul_bdd (c := 1)
      (continuous_sechSqHalf.comp (continuous_id.add continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun z => norm_sechSqHalf_le_one (z + y))).integrableOn
  rw [integral_Ici_integral_Ici_add hGc hG0 hint hinner, boundaryAnomaly]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [sechSqHalfTilt]; ring

/-- The anomaly is strictly positive. -/
theorem boundaryAnomaly_pos : 0 < boundaryAnomaly := by
  rw [boundaryAnomaly, integral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall fun u => by positivity) integrable_sq_mul_sechSqHalf_sq.integrableOn]
  have hsupp : Ioi (0 : ℝ) ⊆ Function.support fun u : ℝ => u ^ 2 * sechSqHalf u ^ 2 := by
    intro u hu
    have := sechSqHalf_pos u
    simp only [Function.mem_support]
    exact mul_ne_zero (pow_ne_zero 2 (ne_of_gt hu)) (pow_ne_zero 2 this.ne')
  calc (0 : ℝ≥0∞) < volume.restrict (Ici 0) (Ioi 0) := by
        rw [Measure.restrict_apply measurableSet_Ioi,
          show Ioi (0 : ℝ) ∩ Ici 0 = Ioi 0 from inter_eq_left.mpr Ioi_subset_Ici_self,
          Real.volume_Ioi]
        simp
    _ ≤ _ := measure_mono hsupp

/-! ### Plancherel -/

theorem l2_norm_sq_eq_integral (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ 2 := by
  have h2 := MeasureTheory.L2.inner_def (𝕜 := ℂ) f f
  rw [inner_self_eq_norm_sq_to_K] at h2
  have h3 : ∀ a : ℝ, inner ℂ ((f : ℝ → ℂ) a) ((f : ℝ → ℂ) a) = ((‖(f : ℝ → ℂ) a‖ ^ 2 : ℝ) : ℂ) := by
    intro a
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp_rw [h3] at h2
  rw [integral_complex_ofReal] at h2
  have h4 : ((‖f‖ ^ 2 : ℝ) : ℂ) = ((∫ x : ℝ, ‖(f : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    exact h2
  exact_mod_cast h4

theorem memLp_thermalTiltKernel : MemLp thermalTiltKernel 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm
    measurable_thermalTiltKernel.aestronglyMeasurable).mpr ?_
  refine integrable_sq_mul_sechSqHalf_sq.congr (Eventually.of_forall fun u => ?_)
  simp only
  rw [norm_thermalTiltKernel, mul_pow, sq_abs]

/-- **Plancherel for the commutator symbol:** `∫_ℝ |m'(ξ)|² dξ = 2π ∫_ℝ u² h(u)² du`. -/
theorem integral_thermalSymbolDeriv_sq :
    ∫ ξ, thermalSymbolDeriv ξ ^ 2 = 2 * π * ∫ u, u ^ 2 * sechSqHalf u ^ 2 := by
  set v := memLp_thermalTiltKernel.toLp thermalTiltKernel
  have hvint : Integrable (v : ℝ → ℂ) :=
    integrable_thermalTiltKernel.congr (MemLp.coeFn_toLp memLp_thermalTiltKernel).symm
  have hF : (fourierL2 ℝ v : ℝ → ℂ) =ᵐ[volume]
      fun w => ((thermalSymbolDeriv (-(2 * π * w)) : ℝ) : ℂ) := by
    filter_upwards [fourierL2_coeFn_ae_eq_fourier v hvint] with w hw
    rw [hw, ← fourier_thermalTiltKernel, Real.fourier_real_eq, Real.fourier_real_eq]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp memLp_thermalTiltKernel] with x hx
    rw [hx]
  have hnorm := norm_fourierL2_apply (E := ℝ) v
  have h1 : ‖fourierL2 ℝ v‖ ^ 2 = ∫ w, thermalSymbolDeriv (-(2 * π) * w) ^ 2 := by
    rw [l2_norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hF] with w hw
    rw [hw, Complex.norm_real, Real.norm_eq_abs, sq_abs, neg_mul]
  have h2 : ‖v‖ ^ 2 = ∫ u, u ^ 2 * sechSqHalf u ^ 2 := by
    rw [l2_norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp memLp_thermalTiltKernel] with u hu
    rw [hu, norm_thermalTiltKernel, mul_pow, sq_abs]
  have h3 := Measure.integral_comp_mul_left (fun ξ => thermalSymbolDeriv ξ ^ 2) (-(2 * π))
  have hmain : ∫ u, u ^ 2 * sechSqHalf u ^ 2 = (2 * π)⁻¹ * ∫ ξ, thermalSymbolDeriv ξ ^ 2 := by
    rw [← h2, ← hnorm, h1, h3, abs_inv, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * π),
      smul_eq_mul]
  rw [hmain]
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  field_simp

/-- `∫_ℝ u² h² = 2 ∫₀^∞ u² h²` (evenness). -/
theorem integral_sq_mul_sechSqHalf_sq : ∫ u, u ^ 2 * sechSqHalf u ^ 2 = 2 * boundaryAnomaly := by
  have hs := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi integrable_sq_mul_sechSqHalf_sq
  rw [compl_Ioi] at hs
  have hneg : ∫ u in Iic 0, u ^ 2 * sechSqHalf u ^ 2 = ∫ u in Ioi 0, u ^ 2 * sechSqHalf u ^ 2 := by
    have h := integral_comp_neg_Ioi (0 : ℝ) (fun u : ℝ => u ^ 2 * sechSqHalf u ^ 2)
    rw [neg_zero] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [sechSqHalf_neg, neg_sq]
  rw [boundaryAnomaly, integral_Ici_eq_integral_Ioi, ← hs, hneg]
  ring

/-! ### The prime pair -/

/-- A commutator with a trace-class factor is trace class with trace zero. -/
theorem memSchattenClass_one_commutator {T : L²₊ →L[ℂ] L²₊} (hT : MemSchattenClass 1 T)
    (B : L²₊ →L[ℂ] L²₊) : MemSchattenClass 1 (T ∘L B - B ∘L T) :=
  memSchattenClass_one_sub' (memSchattenClass_one_comp_right hT B) (memSchattenClass_one_comp_left hT B)

theorem opTrace_commutator_eq_zero {T : L²₊ →L[ℂ] L²₊} (hT : MemSchattenClass 1 T)
    (B : L²₊ →L[ℂ] L²₊) : ContinuousLinearMap.opTrace (T ∘L B - B ∘L T) = 0 := by
  rw [opTrace_sub_of_memSchattenClass_one (memSchattenClass_one_comp_right hT B)
    (memSchattenClass_one_comp_left hT B), hT.one_opTrace_comp_comm B, sub_self]

/-- Commutators with trace-class perturbations: `[W + E, J + F] - [W, J]` is trace class with
trace zero when `E, F ∈ S₁`. -/
theorem commutator_add_traceClass {W J E F : L²₊ →L[ℂ] L²₊} (hE : MemSchattenClass 1 E)
    (hF : MemSchattenClass 1 F) :
    MemSchattenClass 1 ((W + E) ∘L (J + F) - (J + F) ∘L (W + E) - (W ∘L J - J ∘L W)) ∧
      ContinuousLinearMap.opTrace
        ((W + E) ∘L (J + F) - (J + F) ∘L (W + E) - (W ∘L J - J ∘L W)) = 0 := by
  have e : (W + E) ∘L (J + F) - (J + F) ∘L (W + E) - (W ∘L J - J ∘L W) =
      (E ∘L J - J ∘L E) + (-(F ∘L W - W ∘L F)) + (E ∘L F - F ∘L E) := by
    simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
    abel
  have h1 := memSchattenClass_one_commutator hE J
  have h2 : MemSchattenClass 1 (-(F ∘L W - W ∘L F)) := by
    rw [← neg_one_smul ℂ]; exact memSchattenClass_one_smul (memSchattenClass_one_commutator hF W) _
  have h3 := memSchattenClass_one_commutator hE F
  rw [e]
  refine ⟨memSchattenClass_one_add' (memSchattenClass_one_add' h1 h2) h3, ?_⟩
  rw [opTrace_add_of_memSchattenClass_one (memSchattenClass_one_add' h1 h2) h3,
    opTrace_add_of_memSchattenClass_one h1 h2, opTrace_commutator_eq_zero hE J,
    opTrace_commutator_eq_zero hE F, ← neg_one_smul ℂ (F ∘L W - W ∘L F), opTrace_smul,
    opTrace_commutator_eq_zero hF W]
  ring

/-! ### (6) The boundary trace anomaly -/

/-- `[W, J] = i [W, W_j]`. -/
theorem wienerHopf_commutator_smul :
    wienerHopfSechOp ∘L (Complex.I • wienerHopfTiltOp) - (Complex.I • wienerHopfTiltOp) ∘L wienerHopfSechOp =
      Complex.I • (wienerHopfSechOp ∘L wienerHopfTiltOp - wienerHopfTiltOp ∘L wienerHopfSechOp) := by
  rw [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, smul_sub]

/-- **(6)** For `W = P₊ W_full P₊`, `J = P₊ J_full P₊`, `A = U K U*` and `C = U C_P U*`:
`[W, J]` and `[A, C]` are trace class, `tr [A, C] = tr [W, J] = 2i ∫₀^∞ u² h(u)² du
= i/(2π) ∫_ℝ |m'(ξ)|² dξ`, and this trace is nonzero. -/
theorem boundary_trace_anomaly :
    let W := halfLineRestrict ∘L thermalConvOp ∘L halfLineExtend
    let J := halfLineRestrict ∘L thermalCommOp ∘L halfLineExtend
    let A := primeCellOp ∘L poissonPrimeOp ∘L primeCellOp.adjoint
    let C := primeCellOp ∘L poissonPrimeClockCommOp ∘L primeCellOp.adjoint
    MemSchattenClass 1 (W ∘L J - J ∘L W) ∧ MemSchattenClass 1 (A ∘L C - C ∘L A) ∧
      ContinuousLinearMap.opTrace (A ∘L C - C ∘L A) = ContinuousLinearMap.opTrace (W ∘L J - J ∘L W) ∧
      ContinuousLinearMap.opTrace (W ∘L J - J ∘L W) = 2 * Complex.I * boundaryAnomaly ∧
      ContinuousLinearMap.opTrace (W ∘L J - J ∘L W) =
        Complex.I / (2 * π) * ((∫ ξ, thermalSymbolDeriv ξ ^ 2 : ℝ) : ℂ) ∧
      ContinuousLinearMap.opTrace (W ∘L J - J ∘L W) ≠ 0 := by
  intro W J A C
  have hW : W = wienerHopfSechOp := halfLine_compression_thermalConvOp
  have hJ : J = Complex.I • wienerHopfTiltOp := halfLine_compression_thermalCommOp
  have hA : A = mertensStepSechOp := primeCellOp_conj_poissonPrimeOp
  have hC : C = Complex.I • mertensStepTiltOp := primeCellOp_conj_poissonPrimeClockCommOp
  have hWJ : W ∘L J - J ∘L W =
      Complex.I • (wienerHopfSechOp ∘L wienerHopfTiltOp - wienerHopfTiltOp ∘L wienerHopfSechOp) := by
    rw [hW, hJ, wienerHopf_commutator_smul]
  have hWJ1 : MemSchattenClass 1 (W ∘L J - J ∘L W) := by
    rw [hWJ]; exact memSchattenClass_one_smul memSchattenClass_one_wienerHopf_commutator _
  have htr : ContinuousLinearMap.opTrace (W ∘L J - J ∘L W) = 2 * Complex.I * boundaryAnomaly := by
    rw [hWJ, opTrace_smul, opTrace_wienerHopf_commutator_eq_anomaly]; ring
  have hE : MemSchattenClass 1 (A - W) := by rw [hA, hW]; exact memSchattenClass_one_mertensStepSechOp_sub
  have hF : MemSchattenClass 1 (C - J) := by
    rw [hC, hJ, ← smul_sub]; exact memSchattenClass_one_smul memSchattenClass_one_mertensStepTiltOp_sub _
  obtain ⟨hdiff, htr0⟩ := commutator_add_traceClass (W := W) (J := J) hE hF
  simp only [add_sub_cancel] at hdiff htr0
  have hAC : A ∘L C - C ∘L A = (W ∘L J - J ∘L W) + (A ∘L C - C ∘L A - (W ∘L J - J ∘L W)) := by abel
  have hAC1 : MemSchattenClass 1 (A ∘L C - C ∘L A) := by
    rw [hAC]; exact memSchattenClass_one_add' hWJ1 hdiff
  refine ⟨hWJ1, hAC1, ?_, htr, ?_, ?_⟩
  · rw [hAC, opTrace_add_of_memSchattenClass_one hWJ1 hdiff, htr0, add_zero]
  · rw [htr, integral_thermalSymbolDeriv_sq, integral_sq_mul_sechSqHalf_sq]
    have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  · rw [htr]
    have := boundaryAnomaly_pos
    have h2 : (2 * Complex.I * (boundaryAnomaly : ℂ)) = ((2 * boundaryAnomaly : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h2]
    exact mul_ne_zero (by exact_mod_cast (by positivity : (2 * boundaryAnomaly) ≠ 0)) Complex.I_ne_zero

end RHTower
