import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCutoffMismatchMellin
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalAngularSourceValue
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCompactModularPeriodization
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalAngularCutoffCalibration

/-!
Literal height restoration of the original scalar source and explicit causal field.

The complete physical reader is integrated over the actual invariant modular
measure, with the finite core retained. Its exact horizontal mean evaluates the
three original cutoff-power integrals. Subtracting the derived terminal powers
identifies the raw half-square finite part with the existing physical source
coefficient. Restoring the continued explicit field then cancels all three
projected principal responses and retains the complete original onset lift.

These are height limits at fixed frequency and radius. They do not exchange
height, temporal, horizon or QNM limits, or identify the full Einstein current.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMOriginalScalarRestoration
open D4BMGlobalAngularResponse D4BMJointSource D4BMModularCore D4BMLaplaceRadial
open D4BMCuspProjection (mean integral_cusp_field_from)
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal
attribute [-instance] RCLike.innerProductSpace


/-- The original modular integral with its literal height cutoff. -/
def truncatedIntegral (F : UpperHalfPlane → ℂ) (Y : ℝ) : ℂ :=
  ∫ z in {z : UpperHalfPlane | z.im ≤ Y}, F z ∂measure

private theorem heightSet_measurable (Y : ℝ) :
    MeasurableSet {z : UpperHalfPlane | z.im ≤ Y} :=
  measurableSet_le UpperHalfPlane.continuous_im.measurable measurable_const

/-- Continuous original fields are integrable on each finite truncated modular cell. -/
theorem truncated_integrable (F : UpperHalfPlane → ℂ) (hF : Continuous F) (Y : ℝ) :
    IntegrableOn F {z : UpperHalfPlane | z.im ≤ Y} measure := by
  obtain ⟨C,hC⟩ := (truncated_cell_compact Y).exists_bound_of_continuousOn hF.continuousOn
  have h : MemLp ({z : UpperHalfPlane | z.im ≤ Y}.indicator F) 2 measure := by
    apply MemLp.of_bound (hF.aestronglyMeasurable.indicator (heightSet_measurable Y)) (max C 0)
    filter_upwards [ae_restrict_mem ModularGroup.isClosed_fd.measurableSet] with z hz
    by_cases hy : z.im ≤ Y
    · rw [indicator_of_mem (show z ∈ {z : UpperHalfPlane | z.im ≤ Y} from hy)]
      exact (hC z ⟨hz,hy⟩).trans (le_max_left _ _)
    · rw [indicator_of_notMem (show z ∉ {z : UpperHalfPlane | z.im ≤ Y} from hy),norm_zero]
      exact le_max_right _ _
  exact (integrable_indicator_iff (heightSet_measurable Y)).mp (h.integrable (by norm_num))

/-- Increasing actual height cutoffs exhaust every absolutely integrable angular field. -/
theorem truncatedIntegral_tendsto (F : UpperHalfPlane → ℂ) (hF : Integrable F measure) :
    Tendsto (truncatedIntegral F) atTop (𝓝 (∫ z, F z ∂measure)) := by
  have hu : (⋃ Y : ℝ, {z : UpperHalfPlane | z.im ≤ Y}) = univ := by
    ext z
    simp only [mem_iUnion,mem_setOf_eq,mem_univ,iff_true]
    exact ⟨z.im,le_rfl⟩
  have hm : Monotone (fun Y : ℝ => {z : UpperHalfPlane | z.im ≤ Y}) := by
    intro a b hab z hz
    exact hz.trans hab
  have h := tendsto_setIntegral_of_monotone (μ := measure) (f := F) heightSet_measurable hm
    (by simpa only [hu,integrableOn_univ] using hF)
  change Tendsto (fun Y : ℝ => ∫ z in {z : UpperHalfPlane | z.im ≤ Y}, F z ∂measure) atTop (𝓝 (∫ z, F z ∂measure))
  simpa only [hu,setIntegral_univ] using h


private theorem coordinates_continuous : Continuous coordinates := by
  apply continuous_pi
  intro i
  fin_cases i
  · exact UpperHalfPlane.continuous_re
  · exact UpperHalfPlane.continuous_im

private theorem scalar_continuous (u : ℂ) :
    Continuous (fun z : UpperHalfPlane => scalar u (coordinates z)) :=
  (D4BMAngularSeries.cuspLeg_contDiffOn .scalar u).continuousOn.comp_continuous
    coordinates_continuous (fun z => z.im_pos)

private theorem cutoffPower_continuous (k : ℂ) :
    Continuous (fun z : UpperHalfPlane => cutoffPower k (coordinates z)) := by
  have hp : Continuous (fun z : UpperHalfPlane => (z.im:ℂ)^k) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr z.im_pos.ne')).comp
      UpperHalfPlane.continuous_im.continuousAt
  exact (sourceCutoff_smooth.continuous.comp coordinates_continuous).mul hp

/-- Horizontal integration includes the entire reader, not only its Weyl term. -/
theorem truncated_scalarCutoff_eq_strip (u k : ℂ) (Y : ℝ) (hY : 1 ≤ Y) :
    truncatedIntegral (fun z => scalar u (coordinates z)*cutoffPower k (coordinates z)) Y =
      ∫ y in (1:ℝ)..Y, principal u ![0,y]*cutoffPower k ![0,y]/(y:ℂ)^(2 : ℕ) := by
  let F (z : ℂ) := if z.im ≤ Y then scalar u ![z.re,z.im]*cutoffPower k ![z.re,z.im] else 0
  have hi : Integrable (fun z : UpperHalfPlane => F z) measure := by
    have hh := (truncated_integrable _ ((scalar_continuous u).mul (cutoffPower_continuous k)) Y).integrable_indicator
      (heightSet_measurable Y)
    change Integrable (fun z : UpperHalfPlane => if z.im ≤ Y then scalar u (coordinates z)*cutoffPower k (coordinates z) else 0) measure at hh
    convert! hh using 1
  have hz (z : ℂ) (hz : z.im ≤ 1) : F z=0 := by
    dsimp only [F]
    split_ifs
    · unfold cutoffPower cutoff
      rw [Real.smoothTransition.zero_of_nonpos (by change z.im-2≤0; linarith)]
      simp
    · rfl
  have h := integral_cusp_field_from 1 (by norm_num) F hi hz
  have hl : (∫ z : UpperHalfPlane, F z ∂measure) =
      truncatedIntegral (fun z => scalar u (coordinates z)*cutoffPower k (coordinates z)) Y := by
    change (∫ z, ({z : UpperHalfPlane | z.im ≤ Y}.indicator
      (fun z => scalar u (coordinates z)*cutoffPower k (coordinates z))) z ∂measure) = _
    exact integral_indicator (heightSet_measurable Y)
  rw [hl] at h
  rw [h,intervalIntegral.integral_of_le hY]
  have hm (y : ℝ) (hy : 1 < y) :
      mean (fun x => F (Complex.measurableEquivRealProd.symm (x,y)))/(y:ℂ)^(2 : ℕ) =
        if y ≤ Y then principal u ![0,y]*cutoffPower k ![0,y]/(y:ℂ)^(2 : ℕ) else 0 := by
    change mean (fun x => if y ≤ Y then scalar u ![x,y]*cutoffPower k ![x,y] else 0)/(y:ℂ)^(2 : ℕ) = _
    by_cases hyY : y ≤ Y
    · simp only [hyY,ite_true]
      have hc (x : ℝ) : cutoffPower k ![x,y] = cutoffPower k ![0,y] := rfl
      simp_rw [hc]
      change (∫ x in Ioc (-1/2:ℝ) (1/2), scalar u ![x,y]*cutoffPower k ![0,y])/(y:ℂ)^(2 : ℕ) = _
      rw [integral_mul_const]
      change (mean (fun x => scalar u ![x,y])*cutoffPower k ![0,y])/(y:ℂ)^(2 : ℕ) = _
      rw [mean_scalar u (by linarith)]
    · simp [hyY,D4BMCuspProjection.mean]
  calc
    _ = ∫ y in Ioi (1:ℝ), if y ≤ Y then principal u ![0,y]*cutoffPower k ![0,y]/(y:ℂ)^(2 : ℕ) else 0 :=
      setIntegral_congr_fun measurableSet_Ioi (fun y hy => hm y hy)
    _ = ∫ y in Ioc (1:ℝ) Y, if y ≤ Y then principal u ![0,y]*cutoffPower k ![0,y]/(y:ℂ)^(2 : ℕ) else 0 := by
      apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
        (show Ioc (1:ℝ) Y ⊆ Ioi 1 from fun y hy => hy.1)
      intro y hy
      have hn : ¬y ≤ Y := fun h => hy.2 ⟨hy.1,h⟩
      simp only [hn,ite_false]
    _ = _ := setIntegral_congr_fun measurableSet_Ioc (fun y hy => if_pos hy.2)

private theorem weighted_cutoff_integrable (v : ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun y : ℝ => cutoff ![0,y]*(y:ℂ)^(v-1)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  have hy0 : 0 < y := lt_of_lt_of_le ha (by simpa only [min_eq_left hab] using hy.1)
  exact (nativeCutoff_height_continuous.continuousAt.mul
    (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hy0.ne'))).continuousWithinAt

/-- The terminal power is subtracted from the actual cutoff integral; its finite part has a fixed sign. -/
theorem cutoff_integral_terminal (e : ℂ) (he : e ≠ 0) (Y : ℝ) (hY : 4 ≤ Y) :
    (∫ y in (1:ℝ)..Y, cutoff ![0,y]*(y:ℂ)^(e-1)) =
      (Y:ℂ)^e/e-nativeCutoffMellinContinuation e := by
  have h14 := weighted_cutoff_integrable e 1 4 (by norm_num) (by norm_num)
  have h4Y := weighted_cutoff_integrable e 4 Y (by norm_num) hY
  have hbase : (∫ y in (1:ℝ)..4, cutoff ![0,y]*(y:ℂ)^(e-1)) = cutoffBulkMoment 1 e := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hp : 0 < y := by
      have hy' : y ∈ Icc (1:ℝ) 4 := by simpa using hy
      linarith [hy'.1]
    dsimp [powerCutoffHeight,cutoffPower]
    rw [mul_left_comm,← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hp.ne')]
    congr 2
    ring
  have htail : (∫ y in (4:ℝ)..Y, cutoff ![0,y]*(y:ℂ)^(e-1)) =
      ((Y:ℂ)^e-(4:ℂ)^e)/e := by
    calc
      _ = ∫ y in (4:ℝ)..Y, (y:ℂ)^(e-1) := by
        apply intervalIntegral.integral_congr
        intro y hy
        have hy4 : 4 ≤ y := (show y ∈ Icc (4:ℝ) Y by simpa only [uIcc_of_le hY] using hy).1
        change (Real.smoothTransition (y-2):ℂ)*(y:ℂ)^(e-1)=(y:ℂ)^(e-1)
        rw [Real.smoothTransition.one_of_one_le (by linarith)]
        simp
      _ = _ := by
        rw [integral_cpow (Or.inr ⟨by intro h; apply he; linear_combination h,
          by simpa only [uIcc_of_le hY,mem_Icc,not_and] using
            (show (4:ℝ) ≤ 0 → ¬0 ≤ Y by norm_num)⟩)]
        simp only [sub_add_cancel,Complex.ofReal_ofNat]
  rw [← intervalIntegral.integral_add_adjacent_intervals h14 h4Y,hbase,htail,
    cutoffBulkMoment_eq_nativeMellin 1 e (by simpa using he)]
  simp only [show (1:ℂ)+e-1=e by ring]
  ring

/-- Exact physical principal restoration in the literal truncated modular integral. -/
theorem physical_cutoff_restoration (q : XiZeroCopy) (i : Fin 3) (Y : ℝ) (hY : 4 ≤ Y) :
    truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        cutoffPower (principalExponent q i) (coordinates z)) Y -
      reflectedCompletedLambda ((q.1:ℂ)-1)*(Y:ℂ)^(principalExponent q i-(q.1:ℂ)/2)/
        (principalExponent q i-(q.1:ℂ)/2) =
      -scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/physicalAngularGap q q i := by
  let e := principalExponent q i-(q.1:ℂ)/2
  let C := reflectedCompletedLambda ((q.1:ℂ)-1)
  rw [truncated_scalarCutoff_eq_strip _ _ Y (by linarith),neg_div,physicalScalar_principalCutoff_div_gap]
  have hi : (∫ y in (1:ℝ)..Y, principal (physicalAngularParameter q) ![0,y]*
      cutoffPower (principalExponent q i) ![0,y]/(y:ℂ)^(2 : ℕ)) =
      C*(∫ y in (1:ℝ)..Y, cutoff ![0,y]*(y:ℂ)^(e-1)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro y hy
    have hp : 0 < y := by
      have hy' : y ∈ Icc (1:ℝ) Y := by simpa only [uIcc_of_le (show (1:ℝ)≤Y by linarith)] using hy
      linarith [hy'.1]
    have hn : (y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp.ne'
    dsimp only
    rw [physicalScalar_principal]
    change C*(y:ℂ)^(1-(q.1:ℂ)/2)*(cutoff ![0,y]*(y:ℂ)^principalExponent q i)/(y:ℂ)^(2 : ℕ) = _
    rw [show (y:ℂ)^(2 : ℕ)=(y:ℂ)^(2:ℂ) by norm_cast]
    rw [show C*(y:ℂ)^(1-(q.1:ℂ)/2)*(cutoff ![0,y]*(y:ℂ)^principalExponent q i)=
      C*cutoff ![0,y]*((y:ℂ)^(1-(q.1:ℂ)/2)*(y:ℂ)^principalExponent q i) by ring,
      ← Complex.cpow_add _ _ hn,mul_div_assoc,← Complex.cpow_sub _ _ hn]
    rw [show (1-(q.1:ℂ)/2)+principalExponent q i-2=e-1 by dsimp [e]; ring]
    ring
  rw [hi,cutoff_integral_terminal e (physicalPrincipal_mellinExponent_ne_zero q i) Y hY]
  dsimp only [e,C]
  ring


/-- Counterterm read from the original three principal powers, with no free constant. -/
def principalCounterterm (q : XiZeroCopy) (b : Fin 3 → ℂ) (Y : ℝ) : ℂ :=
  ∑ i : Fin 3, b i*reflectedCompletedLambda ((q.1:ℂ)-1)*
    (Y:ℂ)^(principalExponent q i-(q.1:ℂ)/2)/(principalExponent q i-(q.1:ℂ)/2)

private theorem source_decomposition (q : XiZeroCopy) (z : UpperHalfPlane) :
    fullSquarePotential q (coordinates z) = squareResidual q (coordinates z)+
      ∑ i : Fin 3, principalAmplitude q i*cutoffPower (principalExponent q i) (coordinates z) := by
  rw [squareResidual,principalSquare_expansion q _ z.im_pos,Finset.mul_sum]
  have h : (∑ i : Fin 3, cutoff (coordinates z)*(principalAmplitude q i*(z.im:ℂ)^principalExponent q i)) =
      ∑ i : Fin 3, principalAmplitude q i*cutoffPower (principalExponent q i) (coordinates z) := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [cutoffPower,coordinates,Matrix.cons_val]
    ring
  change fullSquarePotential q (coordinates z) = fullSquarePotential q (coordinates z)-
    (∑ i : Fin 3, cutoff (coordinates z)*(principalAmplitude q i*(z.im:ℂ)^principalExponent q i))+_
  rw [h]
  ring

private theorem square_scalar_decomposition (q : XiZeroCopy) (Y : ℝ) :
    truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
      fullSquarePotential q (coordinates z)) Y =
    truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
      squareResidual q (coordinates z)) Y +
    ∑ i : Fin 3, principalAmplitude q i*truncatedIntegral
      (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        cutoffPower (principalExponent q i) (coordinates z)) Y := by
  have hp (i : Fin 3) : IntegrableOn (fun z : UpperHalfPlane => scalar (physicalAngularParameter q) (coordinates z)*
      cutoffPower (principalExponent q i) (coordinates z)) {z : UpperHalfPlane | z.im ≤ Y} measure := by
    exact truncated_integrable _ ((scalar_continuous (physicalAngularParameter q)).mul
      (cutoffPower_continuous (principalExponent q i))) Y
  have he (z : UpperHalfPlane) : scalar (physicalAngularParameter q) (coordinates z)*fullSquarePotential q (coordinates z) =
      scalar (physicalAngularParameter q) (coordinates z)*squareResidual q (coordinates z)+
        ∑ i : Fin 3, principalAmplitude q i*(scalar (physicalAngularParameter q) (coordinates z)*
          cutoffPower (principalExponent q i) (coordinates z)) := by
    rw [source_decomposition q z,mul_add,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold truncatedIntegral
  simp_rw [he]
  rw [integral_add (scalar_squareResidual_integrable q (physicalAngularParameter q)).integrableOn
    (integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => (hp i).const_mul (principalAmplitude q i))),
    integral_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => (hp i).const_mul (principalAmplitude q i))]
  simp_rw [integral_const_mul]

/-- Literal raw half-square truncation has exactly the source coefficient used by the physical resolvent. -/
theorem original_square_finitePart (q : XiZeroCopy) :
    Tendsto (fun Y => truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        fullSquarePotential q (coordinates z)) Y-principalCounterterm q (principalAmplitude q) Y)
      atTop (𝓝 (physicalSelfSourceCoefficient q)) := by
  have he : (fun Y => truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        fullSquarePotential q (coordinates z)) Y-principalCounterterm q (principalAmplitude q) Y) =ᶠ[atTop]
      (fun Y => truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        squareResidual q (coordinates z)) Y-
        ∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)*
          principalAmplitude q i/physicalAngularGap q q i) := by
    filter_upwards [eventually_ge_atTop (4:ℝ)] with Y hY
    rw [square_scalar_decomposition]
    have hs : (∑ i : Fin 3, principalAmplitude q i*truncatedIntegral
        (fun z => scalar (physicalAngularParameter q) (coordinates z)*
          cutoffPower (principalExponent q i) (coordinates z)) Y)-principalCounterterm q (principalAmplitude q) Y =
        -(∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)*
          principalAmplitude q i/physicalAngularGap q q i) := by
      unfold principalCounterterm
      rw [← Finset.sum_sub_distrib,← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have h := physical_cutoff_restoration q i Y hY
      linear_combination principalAmplitude q i*h
    linear_combination hs
  apply Tendsto.congr' he.symm
  exact (truncatedIntegral_tendsto _ (scalar_squareResidual_integrable q (physicalAngularParameter q))).sub_const _

/-- The actual source, with its derived height subtraction, has the corpus's four-Lambda value. -/
theorem original_square_finitePart_fourLambda (q : XiZeroCopy) (hq : 1/2 < (q.1:ℂ).re) :
    Tendsto (fun Y => truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        fullSquarePotential q (coordinates z)) Y-principalCounterterm q (principalAmplitude q) Y)
      atTop (𝓝 (reflectedCompletedLambda (5*(q.1:ℂ)/2-1)*reflectedCompletedLambda ((q.1:ℂ)/2)^(2 : ℕ)*
        reflectedCompletedLambda (1-3*(q.1:ℂ)/2)/2)) := by
  rw [← physicalSelfSourceCoefficient_fourLambda q hq]
  exact original_square_finitePart q


/-- Exact restoration for all three original principal coefficients at once. -/
theorem principal_sum_restoration (q : XiZeroCopy) (b : Fin 3 → ℂ) (Y : ℝ) (hY : 4 ≤ Y) :
    (∑ i : Fin 3, b i*truncatedIntegral
      (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        cutoffPower (principalExponent q i) (coordinates z)) Y)-principalCounterterm q b Y =
      -(∑ i : Fin 3, scalarCutoffPeriod (physicalAngularParameter q) (principalExponent q i)/
        physicalAngularGap q q i*b i) := by
  unfold principalCounterterm
  rw [← Finset.sum_sub_distrib,← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have h := physical_cutoff_restoration q i Y hY
  linear_combination b i*h

private theorem fullSquare_continuous (q : XiZeroCopy) :
    Continuous (fun z : UpperHalfPlane => fullSquarePotential q (coordinates z)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact ((fullSquarePotential_smooth q (coordinates z) z.im_pos 0).continuousAt).comp
    coordinates_continuous.continuousAt

/-- Actual principal coefficients of the original continued explicit field, including its full lift. -/
def explicitPrincipalCoefficient (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (t : ℝ) (i : Fin 3) : ℂ :=
  continuedPrincipalDifference q branch w a i t+
    radialLift (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*principalAmplitude q i

private theorem explicit_truncated_decomposition (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (t Y : ℝ) :
    truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
      continuedExplicitField q branch w a t (coordinates z)) Y =
    radialLift (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*
      truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        fullSquarePotential q (coordinates z)) Y +
    ∑ i : Fin 3, continuedPrincipalDifference q branch w a i t*truncatedIntegral
      (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        cutoffPower (principalExponent q i) (coordinates z)) Y := by
  have hp (i : Fin 3) : IntegrableOn (fun z : UpperHalfPlane => scalar (physicalAngularParameter q) (coordinates z)*
      cutoffPower (principalExponent q i) (coordinates z)) {z : UpperHalfPlane | z.im ≤ Y} measure := by
    exact truncated_integrable _ ((scalar_continuous (physicalAngularParameter q)).mul
      (cutoffPower_continuous (principalExponent q i))) Y
  have hQ : IntegrableOn (fun z : UpperHalfPlane => scalar (physicalAngularParameter q) (coordinates z)*
      fullSquarePotential q (coordinates z)) {z : UpperHalfPlane | z.im ≤ Y} measure := by
    exact truncated_integrable _ ((scalar_continuous (physicalAngularParameter q)).mul (fullSquare_continuous q)) Y
  have he (z : UpperHalfPlane) : scalar (physicalAngularParameter q) (coordinates z)*
      continuedExplicitField q branch w a t (coordinates z) =
    radialLift (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*
      (scalar (physicalAngularParameter q) (coordinates z)*fullSquarePotential q (coordinates z)) +
    ∑ i : Fin 3, continuedPrincipalDifference q branch w a i t*
      (scalar (physicalAngularParameter q) (coordinates z)*cutoffPower (principalExponent q i) (coordinates z)) := by
    unfold continuedExplicitField
    rw [mul_add,Finset.mul_sum]
    congr 1
    · ring
    · apply Finset.sum_congr rfl
      intro i _
      ring
  unfold truncatedIntegral
  simp_rw [he]
  rw [integral_add (hQ.const_mul _) (integrable_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => (hp i).const_mul _)),
    integral_finsetSum (Finset.univ : Finset (Fin 3)) (fun i _ => (hp i).const_mul _)]
  simp_rw [integral_const_mul]

/-- Restoring the literal principal field cancels the projected principal response;
the complete original onset lift remains. -/
theorem original_explicit_finitePart (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (t : ℝ) :
    Tendsto (fun Y => truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        continuedExplicitField q branch w a t (coordinates z)) Y-
        principalCounterterm q (explicitPrincipalCoefficient q branch w a t) Y)
      atTop (𝓝 (radialLift (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t*
        physicalSelfSourceCoefficient q-physicalSelfPrincipalResponse q branch w a t)) := by
  let L := radialLift (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t
  have he : (fun Y => truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        continuedExplicitField q branch w a t (coordinates z)) Y-
        principalCounterterm q (explicitPrincipalCoefficient q branch w a t) Y) =ᶠ[atTop]
      (fun Y => L*(truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        fullSquarePotential q (coordinates z)) Y-principalCounterterm q (principalAmplitude q) Y)-
        physicalSelfPrincipalResponse q branch w a t) := by
    filter_upwards [eventually_ge_atTop (4:ℝ)] with Y hY
    rw [explicit_truncated_decomposition]
    have hs := principal_sum_restoration q (fun i => continuedPrincipalDifference q branch w a i t) Y hY
    have hc : principalCounterterm q (explicitPrincipalCoefficient q branch w a t) Y =
        principalCounterterm q (fun i => continuedPrincipalDifference q branch w a i t) Y+
          L*principalCounterterm q (principalAmplitude q) Y := by
      unfold principalCounterterm explicitPrincipalCoefficient
      rw [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [L]
      ring
    rw [hc]
    change _ = L*(_-_)-physicalSelfPrincipalResponse q branch w a t
    dsimp only [physicalSelfPrincipalResponse] at ⊢
    linear_combination hs
  apply Tendsto.congr' he.symm
  exact ((original_square_finitePart q).const_mul L).sub_const _

/-- Exact height-restored scalar profile: the three principal corrections cancel
against their literal integrals, retaining the original reduced Green function and onset lift.
Temporal/horizon finite-part interchange and the complete metric current are separate obligations. -/
theorem restored_scalar_profile (q : XiZeroCopy) (branch : Bool) (w a : ℂ) (t : ℝ) :
    Tendsto (fun Y => continuedPhysicalSelfResponse q branch w a t+
      (truncatedIntegral (fun z => scalar (physicalAngularParameter q) (coordinates z)*
        continuedExplicitField q branch w a t (coordinates z)) Y-
        principalCounterterm q (explicitPrincipalCoefficient q branch w a t) Y))
      atTop (𝓝 (physicalSelfSourceCoefficient q*
        (continuedReducedGreen w (physicalRadialFrequency q) (physicalRate q branch) a 1 t+
          radialLift (physicalRate q branch) w a (continuedOnset (physicalRate q branch) w) t))) := by
  have h := (original_explicit_finitePart q branch w a t).const_add
    (continuedPhysicalSelfResponse q branch w a t)
  convert! h using 1
  congr 1
  rw [continuedPhysicalSelfResponse_decomposition]
  ring

end
end RHTower.D4BMOriginalScalarRestoration
