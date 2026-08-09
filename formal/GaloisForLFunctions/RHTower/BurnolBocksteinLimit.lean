import GaloisForLFunctions.RHTower.BurnolReflectedPotential
import GaloisForLFunctions.RHTower.BurnolDyadicCommutatorStaircase

/-!
# The Bockstein limit of the crossing correlation

For negative lag the aperture-crossing correlation collapses the other way: the head now sits at
the shifted argument, giving `W_G(s) = conj(c) e^{s/2} ∫_{1/2}^{e^{-s}/2} g`.  Together with the
positive-lag collapse this bounds the whole correlation by `‖c‖ M e^{-s/2}`, hence

`‖q^{-n} W_G(nL + r)‖ ≤ ‖c‖ M e^{-r/2}` uniformly in `n`,

which is an integrable majorant against `|κ̇|`.  Dominated convergence therefore turns the pointwise
depth profile into the Bockstein limit `𝔅_n(G) → Res_{1/2}(G)`.
-/

open Complex Real MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-! ## The negative-lag collapse -/

theorem burnolCrossingWeight_eq_indicator_neg {s : ℝ} (hs : s < 0) (v : ℝ) :
    burnolCrossingWeight s v =
      Set.indicator (Ioc burnolApertureLog (burnolApertureLog - s)) (fun _ => (1 : ℝ)) v := by
  rw [burnolCrossingWeight]
  by_cases h1 : v ≤ burnolApertureLog
  · have h3 : v + s ≤ burnolApertureLog := by linarith
    have hmem : v ∉ Ioc burnolApertureLog (burnolApertureLog - s) := fun hc => absurd hc.1
      (not_lt.mpr h1)
    rw [if_pos h3, if_pos h1, Set.indicator_of_notMem hmem]
    norm_num
  · by_cases h3 : v + s ≤ burnolApertureLog
    · have hmem : v ∈ Ioc burnolApertureLog (burnolApertureLog - s) :=
        ⟨not_le.mp h1, by linarith⟩
      rw [if_pos h3, if_neg h1, Set.indicator_of_mem hmem]
      norm_num
    · have hmem : v ∉ Ioc burnolApertureLog (burnolApertureLog - s) := by
        intro hc
        exact h3 (by linarith [hc.2])
      rw [if_neg h3, if_neg h1, Set.indicator_of_notMem hmem]
      norm_num

theorem burnolCrossingCorrelationW_eq_window_neg {g : ℝ → ℂ} {s : ℝ} (hs : s < 0) :
    burnolCrossingCorrelationW g s =
      ∫ v in Ioc burnolApertureLog (burnolApertureLog - s),
        (starRingEnd ℂ) (burnolLogLift g (v + s)) * burnolLogLift g v := by
  rw [burnolCrossingCorrelationW]
  have hpt : ∀ v : ℝ,
      (starRingEnd ℂ) (burnolLogLift g (v + s)) * ((burnolCrossingWeight s v : ℝ) : ℂ) *
          burnolLogLift g v =
        Set.indicator (Ioc burnolApertureLog (burnolApertureLog - s))
          (fun w : ℝ => (starRingEnd ℂ) (burnolLogLift g (w + s)) * burnolLogLift g w) v := by
    intro v
    rw [burnolCrossingWeight_eq_indicator_neg hs v]
    by_cases hv : v ∈ Ioc burnolApertureLog (burnolApertureLog - s)
    · rw [Set.indicator_of_mem hv, Set.indicator_of_mem hv]
      push_cast
      ring
    · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem hv]
      push_cast
      ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_indicator measurableSet_Ioc]

theorem burnolCrossingCorrelationW_eq_of_head_neg {g : ℝ → ℂ} {c : ℂ}
    (hhead : BurnolApertureHead g c) {s : ℝ} (hs : s < 0) :
    burnolCrossingCorrelationW g s =
      (starRingEnd ℂ) c * ((Real.exp (s / 2) : ℝ) : ℂ) *
        ∫ t in Ioc (1 / 2 : ℝ) (Real.exp (-s) / 2), g t := by
  rw [burnolCrossingCorrelationW_eq_window_neg hs]
  have hint : ∀ v ∈ Ioc burnolApertureLog (burnolApertureLog - s),
      (starRingEnd ℂ) (burnolLogLift g (v + s)) * burnolLogLift g v =
        ((starRingEnd ℂ) c * ((Real.exp (s / 2) : ℝ) : ℂ)) *
          (Real.exp (v + 0) • g (Real.exp (v + 0))) := by
    intro v hv
    have hle : v + s ≤ burnolApertureLog := by linarith [hv.2]
    rw [burnolLogLift_of_apertureHead hhead hle, burnolLogLift, map_mul, Complex.conj_ofReal,
      Complex.real_smul]
    have hexp : ((Real.exp ((v + s) / 2) : ℝ) : ℂ) * ((Real.exp (v / 2) : ℝ) : ℂ) =
        ((Real.exp (s / 2) : ℝ) : ℂ) * ((Real.exp (v + 0) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    calc ((Real.exp ((v + s) / 2) : ℝ) : ℂ) * (starRingEnd ℂ) c *
            (((Real.exp (v / 2) : ℝ) : ℂ) * g (Real.exp v))
        = (((Real.exp ((v + s) / 2) : ℝ) : ℂ) * ((Real.exp (v / 2) : ℝ) : ℂ)) *
            ((starRingEnd ℂ) c * g (Real.exp v)) := by ring
      _ = _ := by
            rw [hexp]
            simp only [add_zero]
            ring
  rw [setIntegral_congr_fun measurableSet_Ioc hint, MeasureTheory.integral_const_mul,
    ← integral_burnolExpShiftSubstitution g burnolApertureLog (burnolApertureLog - s) 0]
  have h1 : Real.exp (burnolApertureLog + 0) = 1 / 2 := by
    rw [add_zero, exp_burnolApertureLog]
  have h2 : Real.exp (burnolApertureLog - s + 0) = Real.exp (-s) / 2 := by
    rw [add_zero, show burnolApertureLog - s = burnolApertureLog + (-s) by ring, Real.exp_add,
      exp_burnolApertureLog]
    ring
  rw [h1, h2]

/-! ## The uniform bound -/

theorem burnolCrossingCorrelationW_zero (g : ℝ → ℂ) : burnolCrossingCorrelationW g 0 = 0 := by
  rw [burnolCrossingCorrelationW]
  have hpt : ∀ v : ℝ,
      (starRingEnd ℂ) (burnolLogLift g (v + 0)) * ((burnolCrossingWeight 0 v : ℝ) : ℂ) *
        burnolLogLift g v = 0 := by
    intro v
    have hw : burnolCrossingWeight 0 v = 0 := by
      rw [burnolCrossingWeight, add_zero]
      ring
    rw [hw]
    push_cast
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_zero]

theorem norm_setIntegral_le_burnolTotal {g : ℝ → ℂ} (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ)))
    {X : ℝ} : ‖∫ t in Ioc (1 / 2 : ℝ) X, g t‖ ≤ ∫ t in Ioi (1 / 2 : ℝ), ‖g t‖ := by
  have hsub : Ioc (1 / 2 : ℝ) X ⊆ Ioi (1 / 2 : ℝ) := fun t ht => mem_Ioi.mpr ht.1
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm _) ?_
  refine MeasureTheory.setIntegral_mono_set hIoi.norm
    (Filter.Eventually.of_forall fun t => norm_nonneg _)
    (Filter.Eventually.of_forall hsub)

/-- **A uniform bound on the crossing correlation.** -/
theorem norm_burnolCrossingCorrelationW_le {g : ℝ → ℂ} {c : ℂ} (hhead : BurnolApertureHead g c)
    (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ))) (s : ℝ) :
    ‖burnolCrossingCorrelationW g s‖ ≤
      ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) * Real.exp (-s / 2) := by
  set M : ℝ := ∫ t in Ioi (1 / 2 : ℝ), ‖g t‖ with hM
  have hM0 : 0 ≤ M := MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    (fun t _ => norm_nonneg _)
  rcases lt_trichotomy s 0 with hs | hs | hs
  · rw [burnolCrossingCorrelationW_eq_of_head_neg hhead hs, norm_mul, norm_mul,
      Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    have hb := norm_setIntegral_le_burnolTotal (g := g) hIoi (X := Real.exp (-s) / 2)
    have hexp : Real.exp (s / 2) ≤ Real.exp (-s / 2) := by
      refine Real.exp_le_exp.mpr ?_
      linarith
    have hstep1 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ ‖c‖ * Real.exp (s / 2))
    have hstep2 : ‖c‖ * Real.exp (s / 2) * M ≤ ‖c‖ * M * Real.exp (-s / 2) := by
      nlinarith [hexp, mul_nonneg (norm_nonneg c) hM0, norm_nonneg c, hM0]
    linarith
  · rw [hs, burnolCrossingCorrelationW_zero, norm_zero]
    positivity
  · rw [burnolCrossingCorrelationW_eq_of_head hhead hs, norm_mul, norm_mul, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hb : ‖∫ t in Ioc (1 / 2 : ℝ) (Real.exp s / 2), (starRingEnd ℂ) (g t)‖ ≤ M := by
      rw [integral_conj, Complex.norm_conj]
      exact norm_setIntegral_le_burnolTotal hIoi
    have hstep1 := mul_le_mul_of_nonneg_left hb
      (by positivity : (0 : ℝ) ≤ ‖c‖ * Real.exp (-s / 2))
    have hval : ‖c‖ * Real.exp (-s / 2) * M = ‖c‖ * M * Real.exp (-s / 2) := by ring
    linarith


/-! ## An integrable majorant for the Bockstein kernel -/

theorem burnolZExpBound {z : ℝ} (hz : 0 ≤ z) {k : ℝ} (hk : 0 < k) :
    z * Real.exp (-(z / k)) ≤ k := by
  have h := Real.add_one_le_exp (z / k)
  have hpos : (0 : ℝ) < Real.exp (z / k) := Real.exp_pos _
  rw [Real.exp_neg, mul_inv_le_iff₀ hpos]
  have hmul := mul_le_mul_of_nonneg_left h hk.le
  field_simp at hmul
  nlinarith [hmul, hk, hpos]

theorem burnolPow3ExpBound {z : ℝ} (hz : 0 ≤ z) : z ^ 3 * Real.exp (-z) ≤ 27 := by
  have h := burnolZExpBound hz (k := (3 : ℝ)) (by norm_num)
  have hid : z ^ 3 * Real.exp (-z) = (z * Real.exp (-(z / 3))) ^ 3 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  rw [hid]
  have hnn : 0 ≤ z * Real.exp (-(z / 3)) := by positivity
  refine le_trans (pow_le_pow_left₀ hnn h 3) ?_
  norm_num

theorem burnolPow4ExpBound {z : ℝ} (hz : 0 ≤ z) : z ^ 4 * Real.exp (-z) ≤ 256 := by
  have h := burnolZExpBound hz (k := (4 : ℝ)) (by norm_num)
  have hid : z ^ 4 * Real.exp (-z) = (z * Real.exp (-(z / 4))) ^ 4 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  rw [hid]
  have hnn : 0 ≤ z * Real.exp (-(z / 4)) := by positivity
  refine le_trans (pow_le_pow_left₀ hnn h 4) ?_
  norm_num

theorem burnolBocksteinKernel_mul_mode_eq (u : ℝ) :
    burnolBocksteinKernel u * Real.exp (-u / 2) =
      4 * Real.exp (-u) * (burnolCollarZ 0 u * (3 * burnolCollarZ 0 u - 4) *
        Real.exp (-burnolCollarZ 0 u)) := by
  rw [burnolBocksteinKernel, burnolCollarGamma, burnolCollarH]
  have hexp : Real.exp (-u / 2) * Real.exp (-u / 2) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  linear_combination (4 * burnolCollarZ 0 u * (3 * burnolCollarZ 0 u - 4) *
    Real.exp (-burnolCollarZ 0 u)) * hexp

theorem abs_burnolBocksteinKernel_mul_mode_le (u : ℝ) :
    |burnolBocksteinKernel u * Real.exp (-u / 2)| ≤ 400 * Real.exp (-|u|) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπ4 : (3 : ℝ) < π := by linarith [Real.pi_gt_three]
  have hπ32 : π ≤ 4 := Real.pi_le_four
  set z : ℝ := burnolCollarZ 0 u with hz
  have hzpos : 0 < z := burnolCollarZ_pos 0 u
  have hzval : z = π * Real.exp (-2 * u) := by
    rw [hz, burnolCollarZ]
    norm_num
  have hzexp : Real.exp (-burnolCollarZ 0 u) = Real.exp (-z) := by rw [hz]
  have hep0 : (0 : ℝ) < Real.exp (-z) := Real.exp_pos _
  rw [burnolBocksteinKernel_mul_mode_eq u, ← hz, hzexp, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_pos (Real.exp_pos (-u)),
    abs_of_pos hep0]
  have hsplit : |z * (3 * z - 4)| ≤ 3 * z ^ 2 + 4 * z := by
    rw [abs_le]
    constructor <;> nlinarith [hzpos, sq_nonneg z]
  have hep : (0 : ℝ) < Real.exp (-z) := Real.exp_pos _
  rcases le_or_gt 0 u with hu | hu
  · have hzle : z ≤ π := by
      rw [hzval]
      have h1 : Real.exp (-2 * u) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        linarith
      nlinarith [h1, hπ]
    have hexp1 : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hbnd : |z * (3 * z - 4)| * Real.exp (-z) ≤ 100 := by
      nlinarith [hsplit, hexp1, hzpos, hzle, hπ32, hep, abs_nonneg (z * (3 * z - 4))]
    have habs : |u| = u := abs_of_nonneg hu
    rw [habs]
    have hmul := mul_le_mul_of_nonneg_left hbnd
      (by positivity : (0 : ℝ) ≤ 4 * Real.exp (-u))
    nlinarith [hmul, Real.exp_pos (-u)]
  · have hzge : π ≤ z := by
      rw [hzval]
      have h1 : (1 : ℝ) ≤ Real.exp (-2 * u) := Real.one_le_exp (by linarith)
      nlinarith [h1, hπ]
    have hcomp : Real.exp (-u) ≤ z / π := by
      rw [hzval, mul_div_cancel_left₀ _ (ne_of_gt hπ)]
      exact Real.exp_le_exp.mpr (by linarith)
    have hquart : (3 * z ^ 4 + 4 * z ^ 3) * Real.exp (-z) ≤ 876 := by
      nlinarith [burnolPow4ExpBound hzpos.le, burnolPow3ExpBound hzpos.le, hep]
    have hkey : Real.exp (-u) * (|z * (3 * z - 4)| * Real.exp (-z)) ≤ 876 / (π * z) := by
      have h1 : Real.exp (-u) * (|z * (3 * z - 4)| * Real.exp (-z)) ≤
          (z / π) * ((3 * z ^ 2 + 4 * z) * Real.exp (-z)) := by
        refine mul_le_mul hcomp ?_ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hsplit hep.le
      have h3 : (z / π) * ((3 * z ^ 2 + 4 * z) * Real.exp (-z)) ≤ 876 / (π * z) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < π * z)]
        have hval : (z / π) * ((3 * z ^ 2 + 4 * z) * Real.exp (-z)) * (π * z) =
            (3 * z ^ 4 + 4 * z ^ 3) * Real.exp (-z) := by
          field_simp
        rw [hval]
        exact hquart
      linarith
    have hpiz : (876 : ℝ) / (π * z) ≤ 100 * Real.exp (2 * u) := by
      rw [hzval, div_le_iff₀ (by positivity)]
      have hexp2 : Real.exp (2 * u) * Real.exp (-2 * u) = 1 := by
        rw [← Real.exp_add]
        norm_num
      have hval : 100 * Real.exp (2 * u) * (π * (π * Real.exp (-2 * u))) =
          100 * π ^ 2 * (Real.exp (2 * u) * Real.exp (-2 * u)) := by ring
      rw [hval, hexp2]
      nlinarith [hπ4]
    have hmono : Real.exp (2 * u) ≤ Real.exp (-|u|) := by
      refine Real.exp_le_exp.mpr ?_
      rw [abs_of_neg hu]
      linarith
    nlinarith [hkey, hpiz, hmono, Real.exp_pos (2 * u)]

theorem burnolIntegrable_exp_neg_abs : Integrable (fun u : ℝ => Real.exp (-|u|)) := by
  rw [← integrableOn_univ, ← Set.Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine IntegrableOn.congr_fun (integrableOn_exp_Iic 0) (fun u hu => ?_) measurableSet_Iic
    rw [abs_of_nonpos hu, neg_neg]
  · refine IntegrableOn.congr_fun (exp_neg_integrableOn_Ioi 0 (by norm_num : (0:ℝ) < 1))
      (fun u hu => ?_) measurableSet_Ioi
    rw [abs_of_pos (mem_Ioi.mp hu)]
    norm_num

theorem burnolIntegrable_bocksteinKernel_mul_mode :
    Integrable (fun u : ℝ => burnolBocksteinKernel u * Real.exp (-u / 2)) := by
  have hcont : Continuous fun u : ℝ => burnolBocksteinKernel u * Real.exp (-u / 2) := by
    unfold burnolBocksteinKernel burnolCollarGamma burnolCollarH burnolCollarZ
    fun_prop
  refine MeasureTheory.Integrable.mono' (g := fun u : ℝ => 400 * Real.exp (-|u|))
    (burnolIntegrable_exp_neg_abs.const_mul 400) hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  rw [Real.norm_eq_abs]
  exact abs_burnolBocksteinKernel_mul_mode_le u


/-! ## Continuity of the crossing correlation -/

/-- The tail primitive of an integrable positive-ray function. -/
def burnolTailPrimitive (g : ℝ → ℂ) (X : ℝ) : ℂ := ∫ t in Ioc (1 / 2 : ℝ) X, g t

theorem burnolTailPrimitive_eq_intervalIntegral {g : ℝ → ℂ}
    (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ))) (X : ℝ) :
    burnolTailPrimitive g X = ∫ t in (1 / 2 : ℝ)..X, Set.indicator (Ioi (1 / 2 : ℝ)) g t := by
  rcases le_or_gt (1 / 2 : ℝ) X with hX | hX
  · rw [burnolTailPrimitive, intervalIntegral.integral_of_le hX]
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [Set.indicator_of_mem (mem_Ioi.mpr ht.1)]
  · rw [burnolTailPrimitive, intervalIntegral.integral_of_ge hX.le]
    have hempty : Ioc (1 / 2 : ℝ) X = ∅ := Ioc_eq_empty (by linarith)
    rw [hempty, MeasureTheory.setIntegral_empty]
    have hzero : ∀ t ∈ Ioc X (1 / 2 : ℝ), Set.indicator (Ioi (1 / 2 : ℝ)) g t = (0 : ℂ) := by
      intro t ht
      refine Set.indicator_of_notMem ?_ g
      intro hc
      exact absurd (mem_Ioi.mp hc) (not_lt.mpr ht.2)
    rw [setIntegral_congr_fun measurableSet_Ioc hzero]
    simp

theorem continuous_burnolTailPrimitive {g : ℝ → ℂ} (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ))) :
    Continuous (burnolTailPrimitive g) := by
  have hglob : Integrable (Set.indicator (Ioi (1 / 2 : ℝ)) g) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hIoi
  have hcont := intervalIntegral.continuous_primitive
    (f := Set.indicator (Ioi (1 / 2 : ℝ)) g) (fun a b => hglob.intervalIntegrable)
    (1 / 2 : ℝ)
  exact hcont.congr fun X => (burnolTailPrimitive_eq_intervalIntegral hIoi X).symm

theorem burnolTailPrimitive_half (g : ℝ → ℂ) : burnolTailPrimitive g (1 / 2) = 0 := by
  rw [burnolTailPrimitive, Ioc_self, MeasureTheory.setIntegral_empty]

theorem burnolCrossingCorrelationW_eq_ite {g : ℝ → ℂ} {c : ℂ} (hhead : BurnolApertureHead g c)
    (s : ℝ) :
    burnolCrossingCorrelationW g s =
      if s ≤ 0 then
        (starRingEnd ℂ) c * ((Real.exp (s / 2) : ℝ) : ℂ) *
          burnolTailPrimitive g (Real.exp (-s) / 2)
      else
        -c * ((Real.exp (-s / 2) : ℝ) : ℂ) *
          burnolTailPrimitive (fun t : ℝ => (starRingEnd ℂ) (g t)) (Real.exp s / 2) := by
  rcases lt_trichotomy s 0 with hs | hs | hs
  · rw [if_pos hs.le, burnolCrossingCorrelationW_eq_of_head_neg hhead hs, burnolTailPrimitive]
  · rw [hs, if_pos le_rfl, burnolCrossingCorrelationW_zero]
    have hz : Real.exp (-(0 : ℝ)) / 2 = 1 / 2 := by norm_num
    rw [hz, burnolTailPrimitive_half]
    ring
  · rw [if_neg (not_le.mpr hs), burnolCrossingCorrelationW_eq_of_head hhead hs,
      burnolTailPrimitive]

theorem continuous_burnolCrossingCorrelationW {g : ℝ → ℂ} {c : ℂ}
    (hhead : BurnolApertureHead g c) (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ))) :
    Continuous (burnolCrossingCorrelationW g) := by
  have hconj : IntegrableOn (fun t : ℝ => (starRingEnd ℂ) (g t)) (Ioi (1 / 2 : ℝ)) := by
    have := hIoi.norm
    refine ⟨(Complex.continuous_conj.comp_aestronglyMeasurable hIoi.1), ?_⟩
    refine hIoi.2.congr' ?_
    filter_upwards with t
    simp
  have h1 : Continuous fun s : ℝ =>
      (starRingEnd ℂ) c * ((Real.exp (s / 2) : ℝ) : ℂ) *
        burnolTailPrimitive g (Real.exp (-s) / 2) := by
    refine Continuous.mul (Continuous.mul continuous_const ?_) ?_
    · exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))
    · exact (continuous_burnolTailPrimitive hIoi).comp
        ((Real.continuous_exp.comp continuous_neg).div_const 2)
  have h2 : Continuous fun s : ℝ =>
      -c * ((Real.exp (-s / 2) : ℝ) : ℂ) *
        burnolTailPrimitive (fun t : ℝ => (starRingEnd ℂ) (g t)) (Real.exp s / 2) := by
    refine Continuous.mul (Continuous.mul continuous_const ?_) ?_
    · exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))
    · exact (continuous_burnolTailPrimitive hconj).comp
        (Real.continuous_exp.div_const 2)
  have hglue : ∀ s : ℝ, s = 0 →
      (starRingEnd ℂ) c * ((Real.exp (s / 2) : ℝ) : ℂ) *
          burnolTailPrimitive g (Real.exp (-s) / 2) =
        -c * ((Real.exp (-s / 2) : ℝ) : ℂ) *
          burnolTailPrimitive (fun t : ℝ => (starRingEnd ℂ) (g t)) (Real.exp s / 2) := by
    intro s hs
    subst hs
    have hz : Real.exp (-(0 : ℝ)) / 2 = 1 / 2 := by norm_num
    have hz' : Real.exp (0 : ℝ) / 2 = 1 / 2 := by norm_num
    rw [hz, hz', burnolTailPrimitive_half, burnolTailPrimitive_half]
    ring
  have hif : Continuous fun s : ℝ =>
      if s ≤ 0 then
        (starRingEnd ℂ) c * ((Real.exp (s / 2) : ℝ) : ℂ) *
          burnolTailPrimitive g (Real.exp (-s) / 2)
      else
        -c * ((Real.exp (-s / 2) : ℝ) : ℂ) *
          burnolTailPrimitive (fun t : ℝ => (starRingEnd ℂ) (g t)) (Real.exp s / 2) :=
    Continuous.if_le h1 h2 continuous_id continuous_const (fun s hs => hglue s hs)
  exact hif.congr fun s => (burnolCrossingCorrelationW_eq_ite hhead s).symm


/-! ## The Bockstein limit -/

theorem tendsto_burnolCrossingDepthProfile {g : ℝ → ℂ} {c : ℂ} (hhead : BurnolApertureHead g c)
    (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ))) (r : ℝ) :
    Tendsto (fun n : ℕ => ((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
        burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r)) atTop
      (𝓝 ((-c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t)) *
        ((Real.exp (-r / 2) : ℝ) : ℂ))) := by
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) * Real.log 2 + r) atTop atTop := by
    refine Filter.Tendsto.atTop_add ?_ tendsto_const_nhds
    exact Filter.Tendsto.atTop_mul_const (Real.log_pos (by norm_num))
      tendsto_natCast_atTop_atTop
  have hcomp := ((tendsto_burnolCrossingResidue hhead hIoi).comp hshift).mul_const
    ((Real.exp (-r / 2) : ℝ) : ℂ)
  refine hcomp.congr fun n => ?_
  rw [Function.comp_apply]
  have hsplit : ((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) =
      ((Real.exp (((n : ℝ) * Real.log 2 + r) / 2) : ℝ) : ℂ) *
        ((Real.exp (-r / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    ring
  rw [hsplit]
  ring

/-- The transverse Bockstein reading at depth `n`. -/
def burnolBocksteinReading (g : ℝ → ℂ) (n : ℕ) : ℂ :=
  2 * ∫ r : ℝ, ((burnolBocksteinKernel r : ℝ) : ℂ) *
    (((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
      burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r))

theorem norm_burnolDepthProfile_le {g : ℝ → ℂ} {c : ℂ} (hhead : BurnolApertureHead g c)
    (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ))) (n : ℕ) (r : ℝ) :
    ‖((burnolBocksteinKernel r : ℝ) : ℂ) *
        (((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
          burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r))‖ ≤
      ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) *
        |burnolBocksteinKernel r * Real.exp (-r / 2)| := by
  set s : ℝ := (n : ℝ) * Real.log 2 + r with hs
  set M : ℝ := ∫ t in Ioi (1 / 2 : ℝ), ‖g t‖ with hM
  have hM0 : 0 ≤ M := MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    (fun t _ => norm_nonneg _)
  have hW := norm_burnolCrossingCorrelationW_le hhead hIoi s
  have hfac : Real.exp ((n : ℝ) * Real.log 2 / 2) * Real.exp (-s / 2) = Real.exp (-r / 2) := by
    rw [← Real.exp_add, hs]
    congr 1
    ring
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_mul,
    abs_of_pos (Real.exp_pos (-r / 2))]
  have hstep := mul_le_mul_of_nonneg_left hW
    (le_of_lt (Real.exp_pos ((n : ℝ) * Real.log 2 / 2)))
  have hval : Real.exp ((n : ℝ) * Real.log 2 / 2) * (‖c‖ * M * Real.exp (-s / 2)) =
      ‖c‖ * M * Real.exp (-r / 2) := by
    rw [show Real.exp ((n : ℝ) * Real.log 2 / 2) * (‖c‖ * M * Real.exp (-s / 2)) =
        ‖c‖ * M * (Real.exp ((n : ℝ) * Real.log 2 / 2) * Real.exp (-s / 2)) by ring, hfac]
  nlinarith [hstep, hval, abs_nonneg (burnolBocksteinKernel r), Real.exp_pos (-r / 2),
    norm_nonneg (burnolCrossingCorrelationW g s), Real.exp_pos ((n : ℝ) * Real.log 2 / 2)]

/-- **The Bockstein reading converges to the singular first-wall residue.** -/
theorem tendsto_burnolBocksteinReading {g : ℝ → ℂ} {c : ℂ} (hhead : BurnolApertureHead g c)
    (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ))) :
    Tendsto (burnolBocksteinReading g) atTop
      (𝓝 (-c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t))) := by
  set R : ℂ := -c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) with hR
  set M : ℝ := ∫ t in Ioi (1 / 2 : ℝ), ‖g t‖ with hM
  have hWcont := continuous_burnolCrossingCorrelationW hhead hIoi
  have hkcont : Continuous fun r : ℝ => ((burnolBocksteinKernel r : ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp ?_
    unfold burnolBocksteinKernel burnolCollarGamma burnolCollarH burnolCollarZ
    fun_prop
  have hbound : Integrable
      (fun r : ℝ => ‖c‖ * M * |burnolBocksteinKernel r * Real.exp (-r / 2)|) := by
    have h := burnolIntegrable_bocksteinKernel_mul_mode.norm
    simpa only [Real.norm_eq_abs] using h.const_mul (‖c‖ * M)
  have hlim := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun (n : ℕ) (r : ℝ) => ((burnolBocksteinKernel r : ℝ) : ℂ) *
      (((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
        burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r)))
    (f := fun r : ℝ => ((burnolBocksteinKernel r : ℝ) : ℂ) *
      (R * ((Real.exp (-r / 2) : ℝ) : ℂ)))
    (bound := fun r : ℝ => ‖c‖ * M * |burnolBocksteinKernel r * Real.exp (-r / 2)|)
    (fun n => (hkcont.mul (continuous_const.mul
      (hWcont.comp (continuous_const.add continuous_id)))).aestronglyMeasurable)
    hbound
    (fun n => Filter.Eventually.of_forall fun r => norm_burnolDepthProfile_le hhead hIoi n r)
    (Filter.Eventually.of_forall fun r =>
      (tendsto_burnolCrossingDepthProfile hhead hIoi r).const_mul _)
  have hval : (∫ r : ℝ, ((burnolBocksteinKernel r : ℝ) : ℂ) *
      (R * ((Real.exp (-r / 2) : ℝ) : ℂ))) = R * ((1 : ℂ) / 2) := by
    have hcongr : (fun r : ℝ => ((burnolBocksteinKernel r : ℝ) : ℂ) *
        (R * ((Real.exp (-r / 2) : ℝ) : ℂ))) =
        fun r : ℝ => R * (((burnolBocksteinKernel r * Real.exp (-r / 2) : ℝ)) : ℂ) := by
      funext r
      push_cast
      ring
    rw [hcongr, MeasureTheory.integral_const_mul, integral_complex_ofReal]
    congr 1
    have h := integral_burnolBocksteinKernel_mul_mode
    have : (∫ u : ℝ, burnolBocksteinKernel u * Real.exp (-u / 2)) = 1 / 2 := by linarith
    rw [this]
    norm_num
  rw [hval] at hlim
  have hfinal := hlim.const_mul (2 : ℂ)
  refine hfinal.congr' ?_ |>.congr' (Filter.Eventually.of_forall fun n => rfl) |>.mono_right ?_
  · exact Filter.Eventually.of_forall fun n => rfl
  · refine le_of_eq ?_
    congr 1
    rw [hR]
    ring


/-! ## The two physical orientations -/

theorem xiDivisor_tendsto_burnolBocksteinReading_forward {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (hxi : xi ρ = 0) :
    Tendsto (burnolBocksteinReading (burnolZeroDividedSource ρ)) atTop
      (𝓝 (burnolFirstWallResidue ρ)) := by
  have hIoi : IntegrableOn (burnolZeroDividedSource ρ) (Ioi (1 / 2 : ℝ)) :=
    (integrableOn_burnolZeroDividedSource hρ0 hρ1 hxi).mono_set
      (fun x hx => mem_Ioi.mpr (lt_trans (by norm_num) (mem_Ioi.mp hx)))
  have h := tendsto_burnolBocksteinReading
    (xiDivisor_burnolZeroDividedSource_apertureHead hρ0 hρ1 hxi) hIoi
  rwa [xiDivisor_integral_burnolZeroDividedSource_exterior hρ0 hρ1 hxi] at h

theorem xiDivisor_tendsto_burnolBocksteinReading_reflected {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (hxi : xi ρ = 0) :
    Tendsto (burnolBocksteinReading (burnolReflectedDividedSource ρ)) atTop
      (𝓝 (burnolFirstWallCosineResidue ρ)) := by
  have hIoi : IntegrableOn (burnolReflectedDividedSource ρ) (Ioi (1 / 2 : ℝ)) :=
    (integrableOn_burnolReflectedDividedSource hρ0 hρ1 hxi).mono_set
      (fun x hx => mem_Ioi.mpr (lt_trans (by norm_num) (mem_Ioi.mp hx)))
  have h := tendsto_burnolBocksteinReading
    (burnolReflectedDividedSource_apertureHead hρ0) hIoi
  rw [xiDivisor_integral_burnolReflectedDividedSource_exterior hρ0 hρ1 hxi] at h
  have hval : -(burnolFirstWallCosineHead ρ) *
      (starRingEnd ℂ) (-burnolFirstWallExteriorMass ρ) = burnolFirstWallCosineResidue ρ := by
    rw [burnolFirstWallCosineResidue, map_neg]
    ring
  rwa [hval] at h

/-- **The Gamma--Bockstein landing on the Route-R current.** -/
theorem xiDivisor_tendsto_burnolBocksteinHeadFlux {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) :
    Tendsto (fun n : ℕ => 2 * (burnolBocksteinReading (burnolZeroDividedSource ρ) n -
        burnolBocksteinReading (burnolReflectedDividedSource ρ) n).re) atTop
      (𝓝 (burnolCartierDividedShiftHeadFlux ρ)) := by
  have hdiff := (xiDivisor_tendsto_burnolBocksteinReading_forward hρ0 hρ1 hxi).sub
    (xiDivisor_tendsto_burnolBocksteinReading_reflected hρ0 hρ1 hxi)
  have hre := (Complex.continuous_re.tendsto _).comp hdiff
  have hfin := hre.const_mul (2 : ℝ)
  rw [Function.comp_def] at hfin
  rwa [burnolFirstWallResidue_sub_cosineResidue_re_eq_headFlux ρ] at hfin

/-- **No nonzero constant collar plateau.**  The depth profile is a nonzero multiple of the
nonconstant `A`-null mode, so a constant limit at two distinct depths forces it to vanish. -/
theorem xiDivisor_burnolNoConstantPlateau {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) {L : ℂ} {r₁ r₂ : ℝ} (hne : r₁ ≠ r₂)
    (h1 : Tendsto (fun n : ℕ => ((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
        burnolCrossingCorrelationW (burnolZeroDividedSource ρ)
          ((n : ℝ) * Real.log 2 + r₁)) atTop (𝓝 L))
    (h2 : Tendsto (fun n : ℕ => ((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
        burnolCrossingCorrelationW (burnolZeroDividedSource ρ)
          ((n : ℝ) * Real.log 2 + r₂)) atTop (𝓝 L)) : L = 0 := by
  have hIoi : IntegrableOn (burnolZeroDividedSource ρ) (Ioi (1 / 2 : ℝ)) :=
    (integrableOn_burnolZeroDividedSource hρ0 hρ1 hxi).mono_set
      (fun x hx => mem_Ioi.mpr (lt_trans (by norm_num) (mem_Ioi.mp hx)))
  have hhead := xiDivisor_burnolZeroDividedSource_apertureHead hρ0 hρ1 hxi
  have hp1 := tendsto_burnolCrossingDepthProfile hhead hIoi r₁
  have hp2 := tendsto_burnolCrossingDepthProfile hhead hIoi r₂
  rw [xiDivisor_integral_burnolZeroDividedSource_exterior hρ0 hρ1 hxi] at hp1 hp2
  have he1 := tendsto_nhds_unique h1 hp1
  have he2 := tendsto_nhds_unique h2 hp2
  set R : ℂ := -burnolFirstWallHead ρ * (starRingEnd ℂ) (burnolFirstWallExteriorMass ρ) with hR
  by_cases hRzero : R = 0
  · rw [he1, hRzero, zero_mul]
  · exfalso
    have hEq : ((Real.exp (-r₁ / 2) : ℝ) : ℂ) = ((Real.exp (-r₂ / 2) : ℝ) : ℂ) := by
      have := he1.symm.trans he2
      exact mul_left_cancel₀ hRzero this
    have hreal : Real.exp (-r₁ / 2) = Real.exp (-r₂ / 2) := by
      exact_mod_cast hEq
    have := Real.exp_eq_exp.mp hreal
    exact hne (by linarith)


/-- **The exact same-fibre Stokes transgression.** -/
theorem xiDivisor_tendsto_burnolBocksteinStokes {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) :
    Tendsto (fun n : ℕ => 2 * (burnolBocksteinReading (burnolZeroDividedSource ρ) n -
        burnolBocksteinReading (burnolReflectedDividedSource ρ) n).re) atTop
      (𝓝 ((∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
            (‖burnolApertureCommutator (1 / 2) (burnolZeroDividedSource ρ) t‖ ^ 2)).toReal -
        (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
            (‖burnolApertureCommutator (1 / 2) (burnolReflectedDividedSource ρ) t‖ ^ 2)).toReal)) := by
  have hf : ∀ s, s ∈ Ioo (0 : ℝ) (1 / 2) → burnolZeroDividedSource ρ s =
      burnolFirstWallHead ρ := fun s hs =>
    xiDivisor_burnolZeroDividedSource_head_eq hρ0 hρ1 hxi hs.1 hs.2.le
  have hg : ∀ s, s ∈ Ioo (0 : ℝ) (1 / 2) → burnolReflectedDividedSource ρ s =
      burnolFirstWallCosineHead ρ := fun s hs =>
    burnolReflectedDividedSource_head hρ0 hs.1 hs.2.le
  rw [burnolApertureCommutator_normSq_difference ρ hf hg]
  exact xiDivisor_tendsto_burnolBocksteinHeadFlux hρ0 hρ1 hxi

/-! ## The completed collar pairing vanishes -/

theorem burnolPow5ExpBound {z : ℝ} (hz : 0 ≤ z) : z ^ 5 * Real.exp (-z) ≤ 3125 := by
  have h := burnolZExpBound hz (k := (5 : ℝ)) (by norm_num)
  have hid : z ^ 5 * Real.exp (-z) = (z * Real.exp (-(z / 5))) ^ 5 := by
    rw [mul_pow, ← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  rw [hid]
  have hnn : 0 ≤ z * Real.exp (-(z / 5)) := by positivity
  refine le_trans (pow_le_pow_left₀ hnn h 5) ?_
  norm_num

theorem burnolCollarKernel_mul_mode_eq (u : ℝ) :
    burnolCollarKernel 0 u * Real.exp (-u / 2) =
      4 * Real.exp (-u) * (Real.exp (-burnolCollarZ 0 u) *
        (burnolCollarZ 0 u * (2 * burnolCollarZ 0 u ^ 2 - 7 * burnolCollarZ 0 u + 3))) := by
  rw [burnolCollarKernel]
  have hexp : Real.exp (-u / 2) * Real.exp (-u / 2) = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  linear_combination (4 * Real.exp (-burnolCollarZ 0 u) *
    (burnolCollarZ 0 u * (2 * burnolCollarZ 0 u ^ 2 - 7 * burnolCollarZ 0 u + 3))) * hexp

theorem abs_burnolCollarKernel_mul_mode_le (u : ℝ) :
    |burnolCollarKernel 0 u * Real.exp (-u / 2)| ≤ 4000 * Real.exp (-|u|) := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hπ4 : (3 : ℝ) < π := by linarith [Real.pi_gt_three]
  have hπ32 : π ≤ 4 := Real.pi_le_four
  set z : ℝ := burnolCollarZ 0 u with hz
  have hzpos : 0 < z := burnolCollarZ_pos 0 u
  have hzval : z = π * Real.exp (-2 * u) := by
    rw [hz, burnolCollarZ]
    norm_num
  have hep : (0 : ℝ) < Real.exp (-z) := Real.exp_pos _
  have hzexp : Real.exp (-burnolCollarZ 0 u) = Real.exp (-z) := by rw [hz]
  rw [burnolCollarKernel_mul_mode_eq u, ← hz, hzexp, abs_mul, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4), abs_of_pos (Real.exp_pos (-u)),
    abs_of_pos hep]
  have hsplit : |z * (2 * z ^ 2 - 7 * z + 3)| ≤ 2 * z ^ 3 + 7 * z ^ 2 + 3 * z := by
    rw [abs_le]
    constructor <;> nlinarith [hzpos, sq_nonneg z, pow_pos hzpos 3]
  rcases le_or_gt 0 u with hu | hu
  · have hzle : z ≤ π := by
      rw [hzval]
      have h1 : Real.exp (-2 * u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      nlinarith [h1, hπ]
    have hexp1 : Real.exp (-z) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hbnd : Real.exp (-z) * |z * (2 * z ^ 2 - 7 * z + 3)| ≤ 1000 := by
      nlinarith [hsplit, hexp1, hzpos, hzle, hπ32, hep,
        abs_nonneg (z * (2 * z ^ 2 - 7 * z + 3))]
    have habs : |u| = u := abs_of_nonneg hu
    rw [habs]
    have hmul := mul_le_mul_of_nonneg_left hbnd
      (by positivity : (0 : ℝ) ≤ 4 * Real.exp (-u))
    nlinarith [hmul, Real.exp_pos (-u)]
  · have hzge : π ≤ z := by
      rw [hzval]
      have h1 : (1 : ℝ) ≤ Real.exp (-2 * u) := Real.one_le_exp (by linarith)
      nlinarith [h1, hπ]
    have hcomp : Real.exp (-u) ≤ z / π := by
      rw [hzval, mul_div_cancel_left₀ _ (ne_of_gt hπ)]
      exact Real.exp_le_exp.mpr (by linarith)
    have hquint : (2 * z ^ 5 + 7 * z ^ 4 + 3 * z ^ 3) * Real.exp (-z) ≤ 8123 := by
      nlinarith [burnolPow5ExpBound hzpos.le, burnolPow4ExpBound hzpos.le,
        burnolPow3ExpBound hzpos.le, hep]
    have hkey : Real.exp (-u) * (Real.exp (-z) * |z * (2 * z ^ 2 - 7 * z + 3)|) ≤
        8123 / (π * z) := by
      have h1 : Real.exp (-u) * (Real.exp (-z) * |z * (2 * z ^ 2 - 7 * z + 3)|) ≤
          (z / π) * ((2 * z ^ 3 + 7 * z ^ 2 + 3 * z) * Real.exp (-z)) := by
        refine mul_le_mul hcomp ?_ (by positivity) (by positivity)
        nlinarith [hsplit, hep, abs_nonneg (z * (2 * z ^ 2 - 7 * z + 3))]
      have h3 : (z / π) * ((2 * z ^ 3 + 7 * z ^ 2 + 3 * z) * Real.exp (-z)) ≤
          8123 / (π * z) := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < π * z)]
        have hval : (z / π) * ((2 * z ^ 3 + 7 * z ^ 2 + 3 * z) * Real.exp (-z)) * (π * z) =
            (2 * z ^ 5 + 7 * z ^ 4 + 3 * z ^ 3) * Real.exp (-z) := by
          field_simp
        rw [hval]
        exact hquint
      linarith
    have hpiz : (8123 : ℝ) / (π * z) ≤ 1000 * Real.exp (2 * u) := by
      rw [hzval, div_le_iff₀ (by positivity)]
      have hexp2 : Real.exp (2 * u) * Real.exp (-2 * u) = 1 := by
        rw [← Real.exp_add]
        norm_num
      have hval : 1000 * Real.exp (2 * u) * (π * (π * Real.exp (-2 * u))) =
          1000 * π ^ 2 * (Real.exp (2 * u) * Real.exp (-2 * u)) := by ring
      rw [hval, hexp2]
      nlinarith [hπ4]
    have hmono : Real.exp (2 * u) ≤ Real.exp (-|u|) := by
      refine Real.exp_le_exp.mpr ?_
      rw [abs_of_neg hu]
      linarith
    nlinarith [hkey, hpiz, hmono, Real.exp_pos (2 * u)]

theorem burnolIntegrable_collarKernel_mul_mode :
    Integrable (fun u : ℝ => burnolCollarKernel 0 u * Real.exp (-u / 2)) := by
  have hcont : Continuous fun u : ℝ => burnolCollarKernel 0 u * Real.exp (-u / 2) := by
    unfold burnolCollarKernel burnolCollarZ
    fun_prop
  refine MeasureTheory.Integrable.mono' (g := fun u : ℝ => 4000 * Real.exp (-|u|))
    (burnolIntegrable_exp_neg_abs.const_mul 4000) hcont.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun u => ?_
  rw [Real.norm_eq_abs]
  exact abs_burnolCollarKernel_mul_mode_le u


/-- The completed collar depth pairing, normalised by the depth weight. -/
def burnolCollarDepthReading (g : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ r : ℝ, ((burnolCollarKernel 0 r : ℝ) : ℂ) *
    (((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
      burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r))

theorem norm_burnolCollarDepthProfile_le {g : ℝ → ℂ} {c : ℂ} (hhead : BurnolApertureHead g c)
    (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ))) (n : ℕ) (r : ℝ) :
    ‖((burnolCollarKernel 0 r : ℝ) : ℂ) *
        (((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
          burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r))‖ ≤
      ‖c‖ * (∫ t in Ioi (1 / 2 : ℝ), ‖g t‖) *
        |burnolCollarKernel 0 r * Real.exp (-r / 2)| := by
  set s : ℝ := (n : ℝ) * Real.log 2 + r with hs
  set M : ℝ := ∫ t in Ioi (1 / 2 : ℝ), ‖g t‖ with hM
  have hM0 : 0 ≤ M := MeasureTheory.setIntegral_nonneg measurableSet_Ioi
    (fun t _ => norm_nonneg _)
  have hW := norm_burnolCrossingCorrelationW_le hhead hIoi s
  have hfac : Real.exp ((n : ℝ) * Real.log 2 / 2) * Real.exp (-s / 2) = Real.exp (-r / 2) := by
    rw [← Real.exp_add, hs]
    congr 1
    ring
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), abs_mul,
    abs_of_pos (Real.exp_pos (-r / 2))]
  have hstep := mul_le_mul_of_nonneg_left hW
    (le_of_lt (Real.exp_pos ((n : ℝ) * Real.log 2 / 2)))
  have hval : Real.exp ((n : ℝ) * Real.log 2 / 2) * (‖c‖ * M * Real.exp (-s / 2)) =
      ‖c‖ * M * Real.exp (-r / 2) := by
    rw [show Real.exp ((n : ℝ) * Real.log 2 / 2) * (‖c‖ * M * Real.exp (-s / 2)) =
        ‖c‖ * M * (Real.exp ((n : ℝ) * Real.log 2 / 2) * Real.exp (-s / 2)) by ring, hfac]
  nlinarith [hstep, hval, abs_nonneg (burnolCollarKernel 0 r), Real.exp_pos (-r / 2),
    norm_nonneg (burnolCrossingCorrelationW g s), Real.exp_pos ((n : ℝ) * Real.log 2 / 2)]

/-- **The completed collar annihilates the first-wall residue.**  The normalised depth pairing
tends to zero because the limit profile lies in the kernel of the Gamma moment. -/
theorem tendsto_burnolCollarDepthReading {g : ℝ → ℂ} {c : ℂ} (hhead : BurnolApertureHead g c)
    (hIoi : IntegrableOn g (Ioi (1 / 2 : ℝ))) :
    Tendsto (burnolCollarDepthReading g) atTop (𝓝 0) := by
  set R : ℂ := -c * (starRingEnd ℂ) (∫ t in Ioi (1 / 2 : ℝ), g t) with hR
  set M : ℝ := ∫ t in Ioi (1 / 2 : ℝ), ‖g t‖ with hM
  have hWcont := continuous_burnolCrossingCorrelationW hhead hIoi
  have hkcont : Continuous fun r : ℝ => ((burnolCollarKernel 0 r : ℝ) : ℂ) := by
    refine Complex.continuous_ofReal.comp ?_
    unfold burnolCollarKernel burnolCollarZ
    fun_prop
  have hbound : Integrable
      (fun r : ℝ => ‖c‖ * M * |burnolCollarKernel 0 r * Real.exp (-r / 2)|) := by
    have h := burnolIntegrable_collarKernel_mul_mode.norm
    simpa only [Real.norm_eq_abs] using h.const_mul (‖c‖ * M)
  have hlim := MeasureTheory.tendsto_integral_of_dominated_convergence
    (F := fun (n : ℕ) (r : ℝ) => ((burnolCollarKernel 0 r : ℝ) : ℂ) *
      (((Real.exp ((n : ℝ) * Real.log 2 / 2) : ℝ) : ℂ) *
        burnolCrossingCorrelationW g ((n : ℝ) * Real.log 2 + r)))
    (f := fun r : ℝ => ((burnolCollarKernel 0 r : ℝ) : ℂ) *
      (R * ((Real.exp (-r / 2) : ℝ) : ℂ)))
    (bound := fun r : ℝ => ‖c‖ * M * |burnolCollarKernel 0 r * Real.exp (-r / 2)|)
    (fun n => (hkcont.mul (continuous_const.mul
      (hWcont.comp (continuous_const.add continuous_id)))).aestronglyMeasurable)
    hbound
    (fun n => Filter.Eventually.of_forall fun r =>
      norm_burnolCollarDepthProfile_le hhead hIoi n r)
    (Filter.Eventually.of_forall fun r =>
      (tendsto_burnolCrossingDepthProfile hhead hIoi r).const_mul _)
  have hval : (∫ r : ℝ, ((burnolCollarKernel 0 r : ℝ) : ℂ) *
      (R * ((Real.exp (-r / 2) : ℝ) : ℂ))) = 0 := by
    have hcongr : (fun r : ℝ => ((burnolCollarKernel 0 r : ℝ) : ℂ) *
        (R * ((Real.exp (-r / 2) : ℝ) : ℂ))) =
        fun r : ℝ => R * (((burnolCollarKernel 0 r * Real.exp (-r / 2) : ℝ)) : ℂ) := by
      funext r
      push_cast
      ring
    rw [hcongr, MeasureTheory.integral_const_mul, integral_complex_ofReal,
      integral_burnolCollarKernel_mul_mode]
    norm_num
  rw [hval] at hlim
  exact hlim

theorem xiDivisor_tendsto_burnolCollarDepthReading {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1)
    (hxi : xi ρ = 0) :
    Tendsto (burnolCollarDepthReading (burnolZeroDividedSource ρ)) atTop (𝓝 0) := by
  have hIoi : IntegrableOn (burnolZeroDividedSource ρ) (Ioi (1 / 2 : ℝ)) :=
    (integrableOn_burnolZeroDividedSource hρ0 hρ1 hxi).mono_set
      (fun x hx => mem_Ioi.mpr (lt_trans (by norm_num) (mem_Ioi.mp hx)))
  exact tendsto_burnolCollarDepthReading
    (xiDivisor_burnolZeroDividedSource_apertureHead hρ0 hρ1 hxi) hIoi

theorem xiDivisor_tendsto_burnolCollarDepthReading_reflected {ρ : ℂ} (hρ0 : 0 < ρ.re)
    (hρ1 : ρ.re < 1) (hxi : xi ρ = 0) :
    Tendsto (burnolCollarDepthReading (burnolReflectedDividedSource ρ)) atTop (𝓝 0) := by
  have hIoi : IntegrableOn (burnolReflectedDividedSource ρ) (Ioi (1 / 2 : ℝ)) :=
    (integrableOn_burnolReflectedDividedSource hρ0 hρ1 hxi).mono_set
      (fun x hx => mem_Ioi.mpr (lt_trans (by norm_num) (mem_Ioi.mp hx)))
  exact tendsto_burnolCollarDepthReading (burnolReflectedDividedSource_apertureHead hρ0) hIoi

end RHTower
