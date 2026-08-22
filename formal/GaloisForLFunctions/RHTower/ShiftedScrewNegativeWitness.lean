import GaloisForLFunctions.RHTower.ScrewShiftXiValueIdentity
import GaloisForLFunctions.RHTower.PacketAutocorrelationLaplace

/-!
# The damped-sine witness for the even-shift filtered screw form
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

/-! ## The one-node damped-sine packet -/

/-- The single node `w = a(1 - i)` of the damped-sine packet `y_a(x) = e^{-ax} sin(ax)`. -/
def dampedNode (a : ℝ) : Fin 1 → ℂ := fun _ => (a : ℂ) * (1 - Complex.I)

/-- Its unit real coefficient. -/
def dampedWeight : Fin 1 → ℝ := fun _ => 1

theorem dampedNode_re (a : ℝ) (j : Fin 1) : ((dampedNode a) j).re = a := by
  simp [dampedNode, Complex.mul_re]

theorem dampedNode_re_pos {a : ℝ} (ha : 0 < a) (j : Fin 1) : 0 < ((dampedNode a) j).re := by
  rw [dampedNode_re]
  exact ha

theorem packetProfile_dampedNode (a x : ℝ) :
    packetProfile (dampedNode a) dampedWeight x
      = Real.exp (-(a * x)) * Real.sin (a * x) := by
  rw [packetProfile, nodePacket, halfLineExpPacket]
  rw [Fin.sum_univ_one]
  simp only [dampedWeight, dampedNode, Complex.ofReal_one, one_mul]
  have hzre : (-((a : ℂ) * (1 - Complex.I)) * (x : ℂ)).re = -(a * x) := by
    simp [Complex.mul_re, Complex.mul_im]
  have hzim : (-((a : ℂ) * (1 - Complex.I)) * (x : ℂ)).im = a * x := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [Complex.exp_im, hzre, hzim]

theorem autocorrCoeff_dampedNode {a : ℝ} (ha : 0 < a) (k : Fin 1) :
    autocorrCoeff (dampedNode a) dampedWeight k = (1 - Complex.I) / (4 * (a : ℂ)) := by
  have ha0 : (a : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt ha
  rw [autocorrCoeff, Fin.sum_univ_one]
  simp only [dampedWeight, dampedNode, Complex.ofReal_one, one_mul]
  have hconj : (starRingEnd ℂ) ((a : ℂ) * (1 - Complex.I)) = (a : ℂ) * (1 + Complex.I) := by
    rw [map_mul, map_sub, map_one, Complex.conj_I, Complex.conj_ofReal]
    ring
  rw [hconj]
  have hd1 : (a : ℂ) * (1 + Complex.I) + (a : ℂ) * (1 - Complex.I) = 2 * (a : ℂ) := by ring
  have hd2 : (a : ℂ) * (1 - Complex.I) + (a : ℂ) * (1 - Complex.I)
      = 2 * (a : ℂ) * (1 - Complex.I) := by ring
  rw [hd1, hd2]
  have hIne : (1 : ℂ) - Complex.I ≠ 0 := by
    intro hc
    have him := congrArg Complex.im hc
    simp at him
  field_simp
  linear_combination (-2 : ℂ) * Complex.I_sq

theorem re_quarter_one_sub_I_mul {x : ℝ} (hx : x ≠ 0) (E C S : ℝ) :
    ((1 - Complex.I) / (4 * (x : ℂ)) * ((E : ℂ) * ((C : ℂ) + (S : ℂ) * Complex.I))).re
      = E * (C + S) / (4 * x) := by
  have hx0 : (x : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hx
  have key : (1 - Complex.I) / (4 * (x : ℂ)) * ((E : ℂ) * ((C : ℂ) + (S : ℂ) * Complex.I))
      = ((E * (C + S) / (4 * x) : ℝ) : ℂ)
        + ((E * (S - C) / (4 * x) : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
    linear_combination (-((E : ℂ) * (S : ℂ))) * Complex.I_sq
  rw [key]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

theorem packetAutocorrelation_dampedNode {a : ℝ} (ha : 0 < a) (h : ℝ) :
    packetAutocorrelation (dampedNode a) dampedWeight h
      = Real.exp (-(a * h)) * (Real.cos (a * h) + Real.sin (a * h)) / (8 * a) := by
  have hw := dampedNode_re_pos ha
  have hbase := packetAutocorrelation_eq hw dampedWeight h
  rw [halfLineExpPacket, Fin.sum_univ_one, autocorrCoeff_dampedNode ha] at hbase
  have hexp : (-((dampedNode a) 0) * (h : ℂ))
      = ((-(a * h) : ℝ) : ℂ) + ((a * h : ℝ) : ℂ) * Complex.I := by
    simp only [dampedNode]
    push_cast
    ring
  rw [hexp] at hbase
  have hz : Complex.exp (((-(a * h) : ℝ) : ℂ) + ((a * h : ℝ) : ℂ) * Complex.I)
      = ((Real.exp (-(a * h)) : ℝ) : ℂ) *
        (((Real.cos (a * h) : ℝ) : ℂ) + ((Real.sin (a * h) : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.exp_add, Complex.exp_mul_I, Complex.ofReal_exp, Complex.ofReal_cos,
      Complex.ofReal_sin]
  rw [hz, re_quarter_one_sub_I_mul (ne_of_gt ha)] at hbase
  have ha0 : (0:ℝ) < 4 * a := by linarith
  have ha1 : (0:ℝ) < 8 * a := by linarith
  field_simp at hbase ⊢
  linarith [hbase]

/-! ## The Laplace transform of the damped-sine autocorrelation -/

/-- The closed-form Laplace transform of the damped-sine autocorrelation. -/
def dampedLaplaceValue (a c : ℝ) : ℝ := (2 * a + c) / (8 * a * ((a + c) ^ 2 + a ^ 2))

theorem dampedNorm_pos {a c : ℝ} (ha : 0 < a) : 0 < (a + c) ^ 2 + a ^ 2 := by positivity

theorem re_dampedLaplace {a c : ℝ} (ha : 0 < a) :
    (((1 - Complex.I) / (4 * (a : ℂ))) / ((a : ℂ) * (1 - Complex.I) + (c : ℂ))).re
      = (2 * a + c) / (4 * a * ((a + c) ^ 2 + a ^ 2)) := by
  have hN : (0 : ℝ) < (a + c) ^ 2 + a ^ 2 := dampedNorm_pos ha
  have ha' : a ≠ 0 := ne_of_gt ha
  have ha0 : (a : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ha'
  have hMne : (4 * a * ((a + c) ^ 2 + a ^ 2) : ℝ) ≠ 0 := by positivity
  have hMc : ((4 * a * ((a + c) ^ 2 + a ^ 2) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hMne
  have hden : (a : ℂ) * (1 - Complex.I) + (c : ℂ) ≠ 0 := by
    intro hc
    have him := congrArg Complex.im hc
    simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_im] at him
    nlinarith [him, ha]
  have key : ((1 - Complex.I) / (4 * (a : ℂ))) / ((a : ℂ) * (1 - Complex.I) + (c : ℂ))
      = (((2 * a + c : ℝ) : ℂ) - ((c : ℝ) : ℂ) * Complex.I)
          / ((4 * a * ((a + c) ^ 2 + a ^ 2) : ℝ) : ℂ) := by
    rw [div_div, div_eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) ha0) hden) hMc]
    push_cast
    linear_combination (-4 * (a : ℂ) ^ 2 * (c : ℂ)) * Complex.I_sq
  rw [key, Complex.div_ofReal_re]
  simp

theorem autocorrLaplace_dampedNode {a c : ℝ} (ha : 0 < a) (hac : 0 < a + c) :
    autocorrLaplace (dampedNode a) dampedWeight c = dampedLaplaceValue a c := by
  have hw := dampedNode_re_pos ha
  have hwc : ∀ j, 0 < ((dampedNode a) j + (c : ℂ)).re := by
    intro j
    simp only [Complex.add_re, Complex.ofReal_re, dampedNode_re]
    linarith
  have h := autocorrLaplace_eq hw dampedWeight hwc
  rw [Fin.sum_univ_one, autocorrCoeff_dampedNode ha] at h
  have hnode : (dampedNode a) 0 + (c : ℂ) = (a : ℂ) * (1 - Complex.I) + (c : ℂ) := rfl
  rw [hnode, re_dampedLaplace ha] at h
  rw [dampedLaplaceValue]
  have hN : (0 : ℝ) < (a + c) ^ 2 + a ^ 2 := dampedNorm_pos ha
  have h4 : (0 : ℝ) < 4 * a * ((a + c) ^ 2 + a ^ 2) := by positivity
  have h8 : (0 : ℝ) < 8 * a * ((a + c) ^ 2 + a ^ 2) := by positivity
  field_simp at h ⊢
  linarith [h]

/-! ## The even-shift filtered quadratic on a damped core -/

variable {n : ℕ}

/-- The regular half of the even-shift filtered quadratic. -/
def shiftedScrewRegularCurrent (w : Fin n → ℂ) (r : Fin n → ℝ) : ℝ :=
  ∫ h in Ioi (0 : ℝ), shiftedScrewDensity h * packetAutocorrelation w r h

/-- The even-shift filtered convolution quadratic of a damped core, in autocorrelation form. -/
def shiftedScrewQuadratic (w : Fin n → ℂ) (r : Fin n → ℝ) : ℝ :=
  2 * shiftedScrewRegularCurrent w r
    - 2 * ∑' m : ℕ, shiftedScrewAtomCoeff m * packetAutocorrelation w r (Real.log m)

theorem shiftedScrewRegularCurrent_eq {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (hhalf : ∀ j, 1 / 2 < (w j).re) (r : Fin n → ℝ) :
    shiftedScrewRegularCurrent w r
      = autocorrLaplace w r (-(1 / 2)) - autocorrLaplace w r (3 / 2)
        - autocorrLaplace w r (5 / 2) := by
  have hc1 : ∀ j, 0 < (w j + ((-(1 / 2) : ℝ) : ℂ)).re := by
    intro j
    have := hhalf j
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hc2 : ∀ j, 0 < (w j + ((3 / 2 : ℝ) : ℂ)).re := by
    intro j
    have := hw j
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hc3 : ∀ j, 0 < (w j + ((5 / 2 : ℝ) : ℂ)).re := by
    intro j
    have := hw j
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hi1 := integrableOn_exp_neg_mul_packetAutocorrelation hw r hc1
  have hi2 := integrableOn_exp_neg_mul_packetAutocorrelation hw r hc2
  have hi3 := integrableOn_exp_neg_mul_packetAutocorrelation hw r hc3
  have hcongr : (fun h : ℝ => shiftedScrewDensity h * packetAutocorrelation w r h)
      = fun h : ℝ =>
        (Real.exp (-((-(1 / 2) : ℝ) * h)) * packetAutocorrelation w r h
          - Real.exp (-((3 / 2 : ℝ) * h)) * packetAutocorrelation w r h)
        - Real.exp (-((5 / 2 : ℝ) * h)) * packetAutocorrelation w r h := by
    funext h
    rw [shiftedScrewDensity]
    have e1 : Real.exp (-((-(1 / 2) : ℝ) * h)) = Real.exp (h / 2) := by
      congr 1
      ring
    have e2 : Real.exp (-((3 / 2 : ℝ) * h)) = Real.exp (-(3 * h / 2)) := by
      congr 1
      ring
    have e3 : Real.exp (-((5 / 2 : ℝ) * h)) = Real.exp (-(5 * h / 2)) := by
      congr 1
      ring
    rw [e1, e2, e3]
    ring
  have h12 : IntegrableOn (fun h : ℝ =>
      Real.exp (-((-(1 / 2) : ℝ) * h)) * packetAutocorrelation w r h
        - Real.exp (-((3 / 2 : ℝ) * h)) * packetAutocorrelation w r h) (Ioi 0) := hi1.sub hi2
  rw [shiftedScrewRegularCurrent, hcongr,
    MeasureTheory.integral_sub h12 hi3, MeasureTheory.integral_sub hi1 hi2]
  rfl

theorem shiftedScrewRegularCurrent_dampedNode {a : ℝ} (ha : 1 / 2 < a) :
    shiftedScrewRegularCurrent (dampedNode a) dampedWeight
      = dampedLaplaceValue a (-(1 / 2)) - dampedLaplaceValue a (3 / 2)
        - dampedLaplaceValue a (5 / 2) := by
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have hw := dampedNode_re_pos ha0
  have hhalf : ∀ j, 1 / 2 < ((dampedNode a) j).re := by
    intro j
    rw [dampedNode_re]
    exact ha
  rw [shiftedScrewRegularCurrent_eq hw hhalf dampedWeight,
    autocorrLaplace_dampedNode ha0 (by linarith),
    autocorrLaplace_dampedNode ha0 (by linarith),
    autocorrLaplace_dampedNode ha0 (by linarith)]

/-! ## The scaling limit of the regular half -/

theorem tendsto_dampedLaplaceValue (c : ℝ) :
    Tendsto (fun a : ℝ => a ^ 2 * (2 * dampedLaplaceValue a c)) atTop (𝓝 (1 / 4)) := by
  have hinv : Tendsto (fun a : ℝ => c * a⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.const_mul c
  have hg : Tendsto (fun t : ℝ => (2 + t) / (4 * ((1 + t) ^ 2 + 1))) (𝓝 0) (𝓝 (1 / 4)) := by
    have hcont : ContinuousAt (fun t : ℝ => (2 + t) / (4 * ((1 + t) ^ 2 + 1))) 0 := by
      refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
      norm_num
    have := hcont.tendsto
    norm_num at this
    exact this
  have hcomp := hg.comp hinv
  refine hcomp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  have hN : (0 : ℝ) < (a + c) ^ 2 + a ^ 2 := dampedNorm_pos ha
  have ha' : a ≠ 0 := ne_of_gt ha
  have hd : (0 : ℝ) < 4 * ((1 + c * a⁻¹) ^ 2 + 1) := by positivity
  show (2 + c * a⁻¹) / (4 * ((1 + c * a⁻¹) ^ 2 + 1)) = a ^ 2 * (2 * dampedLaplaceValue a c)
  have hd2 : (1 + c * a⁻¹) ^ 2 + 1 ≠ 0 := by positivity
  have hNne : (a + c) ^ 2 + a ^ 2 ≠ 0 := ne_of_gt hN
  rw [dampedLaplaceValue]
  field_simp
  ring

theorem tendsto_shiftedScrewRegular :
    Tendsto (fun a : ℝ => a ^ 2 * (2 * shiftedScrewRegularCurrent (dampedNode a) dampedWeight))
      atTop (𝓝 (-(1 / 4))) := by
  have h1 := tendsto_dampedLaplaceValue (-(1 / 2))
  have h2 := tendsto_dampedLaplaceValue (3 / 2)
  have h3 := tendsto_dampedLaplaceValue (5 / 2)
  have hlim := (h1.sub h2).sub h3
  have hval : (1 : ℝ) / 4 - 1 / 4 - 1 / 4 = -(1 / 4) := by norm_num
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (1 / 2 : ℝ)] with a ha
  rw [shiftedScrewRegularCurrent_dampedNode ha]
  ring

/-! ## The atomic half is negligible at large scaling -/

theorem shiftedScrewAtomCoeff_nonneg (m : ℕ) : 0 ≤ shiftedScrewAtomCoeff m := by
  rcases Nat.lt_or_ge m 1 with hm | hm
  · have : m = 0 := by omega
    subst this
    simp [shiftedScrewAtomCoeff]
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hpow : ((m : ℝ)) ^ (-(2 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg (by linarith)]
      rw [inv_le_one_iff₀]
      right
      exact Real.one_le_rpow hm1 (by norm_num)
    have h1 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt m :=
      ArithmeticFunction.vonMangoldt_nonneg
    have h2 : (0 : ℝ) ≤ ((m : ℝ)) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by linarith) _
    rw [shiftedScrewAtomCoeff]
    have h3 : (0 : ℝ) ≤ 1 - ((m : ℝ)) ^ (-(2 : ℝ)) := by linarith
    positivity

theorem exp_neg_mul_log_eq_rpow {m : ℕ} (hm : 1 ≤ m) (a : ℝ) :
    Real.exp (-(a * Real.log m)) = ((m : ℝ)) ^ (-a) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Real.rpow_def_of_pos hm0]
  congr 1
  ring

theorem abs_atomTerm_le {a : ℝ} (ha : 2 ≤ a) (m : ℕ) :
    |shiftedScrewAtomCoeff m *
        packetAutocorrelation (dampedNode a) dampedWeight (Real.log m)|
      ≤ ((2 : ℝ) ^ ((2 : ℝ) - a) / (4 * a)) *
        (ArithmeticFunction.vonMangoldt m * ((m : ℝ)) ^ (-(5 / 2) : ℝ)) := by
  have ha0 : (0 : ℝ) < a := by linarith
  rcases Nat.lt_or_ge m 2 with hm | hm
  · have hz : ArithmeticFunction.vonMangoldt m = 0 := by
      interval_cases m
      · simp
      · simp
    rw [shiftedScrewAtomCoeff, hz]
    simp
  · have hm0 : (0 : ℝ) < (m : ℝ) := by
      have : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hLam : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt m :=
      ArithmeticFunction.vonMangoldt_nonneg
    have hr : (0 : ℝ) < ((m : ℝ)) ^ (-a) := Real.rpow_pos_of_pos hm0 _
    have hp2 : (0 : ℝ) ≤ ((m : ℝ)) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by linarith) _
    have hC : |packetAutocorrelation (dampedNode a) dampedWeight (Real.log m)|
        ≤ ((m : ℝ)) ^ (-a) / (4 * a) := by
      rw [packetAutocorrelation_dampedNode ha0]
      have hcs : |Real.cos (a * Real.log m) + Real.sin (a * Real.log m)| ≤ 2 := by
        have h1 := Real.neg_one_le_cos (a * Real.log m)
        have h2 := Real.cos_le_one (a * Real.log m)
        have h3 := Real.neg_one_le_sin (a * Real.log m)
        have h4 := Real.sin_le_one (a * Real.log m)
        rw [abs_le]
        constructor <;> linarith
      rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos _),
        abs_of_pos (by positivity : (0 : ℝ) < 8 * a),
        exp_neg_mul_log_eq_rpow (by omega) a]
      have hstep : ((m : ℝ)) ^ (-a) *
          |Real.cos (a * Real.log m) + Real.sin (a * Real.log m)| ≤ ((m : ℝ)) ^ (-a) * 2 :=
        mul_le_mul_of_nonneg_left hcs (le_of_lt hr)
      have hfin : ((m : ℝ)) ^ (-a) * 2 / (8 * a) = ((m : ℝ)) ^ (-a) / (4 * a) := by
        field_simp
        ring
      calc ((m : ℝ)) ^ (-a) *
          |Real.cos (a * Real.log m) + Real.sin (a * Real.log m)| / (8 * a)
          ≤ ((m : ℝ)) ^ (-a) * 2 / (8 * a) := by gcongr
        _ = ((m : ℝ)) ^ (-a) / (4 * a) := hfin
    have hcoef : shiftedScrewAtomCoeff m
        ≤ ArithmeticFunction.vonMangoldt m * ((m : ℝ)) ^ (-(1 / 2) : ℝ) := by
      rw [shiftedScrewAtomCoeff]
      have hpow : (0 : ℝ) ≤ ((m : ℝ)) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by linarith) _
      exact mul_le_of_le_one_right (mul_nonneg hLam hp2) (by linarith)
    have hrpow : ((m : ℝ)) ^ (-(1 / 2) : ℝ) * ((m : ℝ)) ^ (-a)
        ≤ (2 : ℝ) ^ ((2 : ℝ) - a) * ((m : ℝ)) ^ (-(5 / 2) : ℝ) := by
      rw [← Real.rpow_add hm0]
      have hsplit : ((m : ℝ)) ^ (-(1 / 2) + -a : ℝ)
          = ((m : ℝ)) ^ ((2 : ℝ) - a) * ((m : ℝ)) ^ (-(5 / 2) : ℝ) := by
        rw [← Real.rpow_add hm0]
        congr 1
        ring
      rw [hsplit]
      have hbase : ((m : ℝ)) ^ ((2 : ℝ) - a) ≤ (2 : ℝ) ^ ((2 : ℝ) - a) := by
        rw [show ((2 : ℝ) - a) = -(a - 2) by ring, Real.rpow_neg (by linarith),
          Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
        have hb : (2 : ℝ) ^ (a - 2) ≤ ((m : ℝ)) ^ (a - 2) :=
          Real.rpow_le_rpow (by norm_num) hm2 (by linarith)
        have hpos : (0 : ℝ) < (2 : ℝ) ^ (a - 2) := Real.rpow_pos_of_pos (by norm_num) _
        exact inv_anti₀ hpos hb
      have hpos : (0 : ℝ) ≤ ((m : ℝ)) ^ (-(5 / 2) : ℝ) := Real.rpow_nonneg (by linarith) _
      exact mul_le_mul_of_nonneg_right hbase hpos
    have hnn1 : (0 : ℝ) ≤ shiftedScrewAtomCoeff m := shiftedScrewAtomCoeff_nonneg m
    rw [abs_mul, abs_of_nonneg hnn1]
    have hkey : (ArithmeticFunction.vonMangoldt m * ((m : ℝ)) ^ (-(1 / 2) : ℝ)) *
          (((m : ℝ)) ^ (-a) / (4 * a))
        = (ArithmeticFunction.vonMangoldt m *
            (((m : ℝ)) ^ (-(1 / 2) : ℝ) * ((m : ℝ)) ^ (-a))) / (4 * a) := by ring
    have hkey2 : ((2 : ℝ) ^ ((2 : ℝ) - a) / (4 * a)) *
          (ArithmeticFunction.vonMangoldt m * ((m : ℝ)) ^ (-(5 / 2) : ℝ))
        = (ArithmeticFunction.vonMangoldt m *
            ((2 : ℝ) ^ ((2 : ℝ) - a) * ((m : ℝ)) ^ (-(5 / 2) : ℝ))) / (4 * a) := by ring
    calc shiftedScrewAtomCoeff m *
        |packetAutocorrelation (dampedNode a) dampedWeight (Real.log m)|
        ≤ (ArithmeticFunction.vonMangoldt m * ((m : ℝ)) ^ (-(1 / 2) : ℝ)) *
            (((m : ℝ)) ^ (-a) / (4 * a)) :=
          mul_le_mul hcoef hC (abs_nonneg _) (mul_nonneg hLam hp2)
      _ = (ArithmeticFunction.vonMangoldt m *
            (((m : ℝ)) ^ (-(1 / 2) : ℝ) * ((m : ℝ)) ^ (-a))) / (4 * a) := hkey
      _ ≤ (ArithmeticFunction.vonMangoldt m *
            ((2 : ℝ) ^ ((2 : ℝ) - a) * ((m : ℝ)) ^ (-(5 / 2) : ℝ))) / (4 * a) := by gcongr
      _ = ((2 : ℝ) ^ ((2 : ℝ) - a) / (4 * a)) *
            (ArithmeticFunction.vonMangoldt m * ((m : ℝ)) ^ (-(5 / 2) : ℝ)) := hkey2.symm

theorem summable_atomMajorant :
    Summable (fun m : ℕ => ArithmeticFunction.vonMangoldt m * ((m : ℝ)) ^ (-(5 / 2) : ℝ)) :=
  GaloisForLFunctions.HTGeometry.summable_vonMangoldt_rpow (σ := 5 / 2) (by norm_num)

theorem summable_atomTerm {a : ℝ} (ha : 2 ≤ a) :
    Summable (fun m : ℕ => shiftedScrewAtomCoeff m *
      packetAutocorrelation (dampedNode a) dampedWeight (Real.log m)) := by
  refine Summable.of_norm_bounded
    (summable_atomMajorant.mul_left ((2 : ℝ) ^ ((2 : ℝ) - a) / (4 * a))) fun m => ?_
  rw [Real.norm_eq_abs]
  exact abs_atomTerm_le ha m

theorem abs_atomSum_le {a : ℝ} (ha : 2 ≤ a) :
    |∑' m : ℕ, shiftedScrewAtomCoeff m *
        packetAutocorrelation (dampedNode a) dampedWeight (Real.log m)|
      ≤ ((2 : ℝ) ^ ((2 : ℝ) - a) / (4 * a)) *
        ∑' m : ℕ, ArithmeticFunction.vonMangoldt m * ((m : ℝ)) ^ (-(5 / 2) : ℝ) := by
  have hnorm : Summable (fun m : ℕ => ‖shiftedScrewAtomCoeff m *
      packetAutocorrelation (dampedNode a) dampedWeight (Real.log m)‖) := by
    refine Summable.of_nonneg_of_le (fun m => norm_nonneg _) (fun m => ?_)
      (summable_atomMajorant.mul_left ((2 : ℝ) ^ ((2 : ℝ) - a) / (4 * a)))
    rw [Real.norm_eq_abs]
    exact abs_atomTerm_le ha m
  have h1 : ‖∑' m : ℕ, shiftedScrewAtomCoeff m *
      packetAutocorrelation (dampedNode a) dampedWeight (Real.log m)‖
      ≤ ∑' m : ℕ, ‖shiftedScrewAtomCoeff m *
        packetAutocorrelation (dampedNode a) dampedWeight (Real.log m)‖ :=
    norm_tsum_le_tsum_norm hnorm
  have h2 : (∑' m : ℕ, ‖shiftedScrewAtomCoeff m *
      packetAutocorrelation (dampedNode a) dampedWeight (Real.log m)‖)
      ≤ ∑' m : ℕ, ((2 : ℝ) ^ ((2 : ℝ) - a) / (4 * a)) *
        (ArithmeticFunction.vonMangoldt m * ((m : ℝ)) ^ (-(5 / 2) : ℝ)) := by
    refine Summable.tsum_mono hnorm
      (summable_atomMajorant.mul_left ((2 : ℝ) ^ ((2 : ℝ) - a) / (4 * a))) fun m => ?_
    rw [Real.norm_eq_abs]
    exact abs_atomTerm_le ha m
  rw [tsum_mul_left] at h2
  rw [← Real.norm_eq_abs]
  linarith

theorem rpow_two_sub_eq {a : ℝ} : (2 : ℝ) ^ ((2 : ℝ) - a) = 4 * Real.exp (-(Real.log 2 * a)) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [show Real.log 2 * (2 - a) = 2 * Real.log 2 + -(Real.log 2 * a) by ring, Real.exp_add]
  congr 1
  rw [show (2 : ℝ) * Real.log 2 = Real.log (2 ^ (2 : ℕ)) by rw [Real.log_pow]; push_cast; ring]
  rw [Real.exp_log (by norm_num)]
  norm_num

theorem tendsto_linear_exp_neg_log_two :
    Tendsto (fun a : ℝ => a * Real.exp (-(Real.log 2 * a))) atTop (𝓝 0) := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have hscale : Tendsto (fun a : ℝ => Real.log 2 * a) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hlog Filter.tendsto_id
  have hcomp : Tendsto (fun a : ℝ => (Real.log 2 * a) * Real.exp (-(Real.log 2 * a)))
      atTop (𝓝 0) := hpow.comp hscale
  have := hcomp.const_mul (Real.log 2)⁻¹
  rw [mul_zero] at this
  refine this.congr fun a => ?_
  field_simp

theorem tendsto_atomPart :
    Tendsto (fun a : ℝ => a ^ 2 * (2 * ∑' m : ℕ, shiftedScrewAtomCoeff m *
      packetAutocorrelation (dampedNode a) dampedWeight (Real.log m))) atTop (𝓝 0) := by
  set S : ℝ := ∑' m : ℕ, ArithmeticFunction.vonMangoldt m * ((m : ℝ)) ^ (-(5 / 2) : ℝ) with hS
  have hSnn : 0 ≤ S := by
    rw [hS]
    refine tsum_nonneg fun m => ?_
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (by positivity) _)
  have hg : Tendsto (fun a : ℝ => 2 * S * (a * Real.exp (-(Real.log 2 * a)))) atTop (𝓝 0) := by
    simpa using tendsto_linear_exp_neg_log_two.const_mul (2 * S)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with a ha
  have ha0 : (0 : ℝ) < a := by linarith
  have hbound := abs_atomSum_le ha
  rw [← hS] at hbound
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ a ^ 2),
    abs_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ))]
  have hkey : a ^ 2 * (2 * ((2 : ℝ) ^ ((2 : ℝ) - a) / (4 * a) * S))
      = 2 * S * (a * Real.exp (-(Real.log 2 * a))) := by
    rw [rpow_two_sub_eq]
    field_simp
  calc a ^ 2 * (2 * |∑' m : ℕ, shiftedScrewAtomCoeff m *
        packetAutocorrelation (dampedNode a) dampedWeight (Real.log m)|)
      ≤ a ^ 2 * (2 * ((2 : ℝ) ^ ((2 : ℝ) - a) / (4 * a) * S)) := by
        have h2 : (0:ℝ) ≤ a ^ 2 * 2 := by positivity
        nlinarith [hbound, sq_nonneg a]
    _ = 2 * S * (a * Real.exp (-(Real.log 2 * a))) := hkey

/-- **Equation `(28)`.**  The scaled even-shift filtered quadratic of the damped-sine packet
converges to `-1/4`. -/
theorem tendsto_shiftedScrewQuadratic :
    Tendsto (fun a : ℝ => a ^ 2 * shiftedScrewQuadratic (dampedNode a) dampedWeight)
      atTop (𝓝 (-(1 / 4))) := by
  have h1 := tendsto_shiftedScrewRegular
  have h2 := tendsto_atomPart
  have hlim := h1.sub h2
  rw [sub_zero] at hlim
  refine hlim.congr fun a => ?_
  rw [shiftedScrewQuadratic]
  ring

/-- **The negative witness.**  For all sufficiently large `a` the even-shift filtered quadratic of
the damped-sine packet is strictly negative. -/
theorem eventually_shiftedScrewQuadratic_neg :
    ∀ᶠ a : ℝ in atTop, shiftedScrewQuadratic (dampedNode a) dampedWeight < 0 := by
  have hlim := tendsto_shiftedScrewQuadratic
  have hneg : ∀ᶠ a : ℝ in atTop, a ^ 2 * shiftedScrewQuadratic (dampedNode a) dampedWeight < 0 := by
    have := hlim.eventually (eventually_lt_nhds (by norm_num : -(1 / 4 : ℝ) < 0))
    exact this
  filter_upwards [hneg, eventually_gt_atTop (0 : ℝ)] with a hlt ha0
  have hsq : (0 : ℝ) < a ^ 2 := by positivity
  nlinarith [hlt, hsq]

end

end RHTower
