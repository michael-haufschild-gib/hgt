import GaloisForLFunctions.RHTower.PairedCompletedEulerCurrent
import GaloisForLFunctions.RHTower.PairedInfiniteApertureCurrent
import GaloisForLFunctions.RHTower.ScrewTailHalfMoment

/-!
# The compensated Gauss form as one screw-tail current
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

variable {n : ℕ}

/-! ## Elementary exponential integrals -/

theorem hasDerivAt_neg_exp_neg_mul {c : ℝ} (hc : c ≠ 0) (h : ℝ) :
    HasDerivAt (fun t : ℝ => -Real.exp (-(c * t)) / c) (Real.exp (-(c * h))) h := by
  have hin : HasDerivAt (fun t : ℝ => -(c * t)) (-c) h := by
    simpa [Pi.neg_def] using ((hasDerivAt_id h).const_mul c).neg
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(c * t)))
      (Real.exp (-(c * h)) * (-c)) h := hin.exp
  have := (hexp.neg).div_const c
  refine this.congr_deriv ?_
  field_simp

theorem integral_Ioi_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    ∫ h in Ioi (0 : ℝ), Real.exp (-(c * h)) = 1 / c := by
  have hlim : Tendsto (fun t : ℝ => -Real.exp (-(c * t)) / c) atTop (𝓝 0) := by
    have := tendsto_expNegLinear hc (-(1 / c))
    simpa [neg_div, div_eq_mul_inv, mul_comm] using this
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    (g := fun t : ℝ => -Real.exp (-(c * t)) / c) (a := (0 : ℝ))
    ((hasDerivAt_neg_exp_neg_mul (ne_of_gt hc) 0).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_neg_exp_neg_mul (ne_of_gt hc) x)
    (fun x _ => le_of_lt (Real.exp_pos _)) hlim
  rw [h]
  simp
  field_simp

theorem hasDerivAt_neg_linear_exp_neg_mul {c : ℝ} (hc : c ≠ 0) (h : ℝ) :
    HasDerivAt (fun t : ℝ => -(t / c + 1 / c ^ 2) * Real.exp (-(c * t)))
      (h * Real.exp (-(c * h))) h := by
  have hin : HasDerivAt (fun t : ℝ => -(t / c + 1 / c ^ 2)) (-(1 / c)) h := by
    have h1 : HasDerivAt (fun t : ℝ => t / c + 1 / c ^ 2) (1 / c) h := by
      simpa using ((hasDerivAt_id h).div_const c).add_const (1 / c ^ 2)
    simpa [Pi.neg_def] using h1.neg
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(c * t)))
      (Real.exp (-(c * h)) * (-c)) h := by
    have hlin : HasDerivAt (fun t : ℝ => -(c * t)) (-c) h := by
      simpa [Pi.neg_def] using ((hasDerivAt_id h).const_mul c).neg
    exact hlin.exp
  refine (hin.mul hexp).congr_deriv ?_
  field_simp
  ring

theorem integral_Ioi_mul_exp_neg_mul {c : ℝ} (hc : 0 < c) :
    ∫ h in Ioi (0 : ℝ), h * Real.exp (-(c * h)) = 1 / c ^ 2 := by
  have hlim : Tendsto (fun t : ℝ => -(t / c + 1 / c ^ 2) * Real.exp (-(c * t))) atTop (𝓝 0) := by
    have hpow : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have hscale : Tendsto (fun t : ℝ => c * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id
    have h1 : Tendsto (fun t : ℝ => (c * t) * Real.exp (-(c * t))) atTop (𝓝 0) :=
      hpow.comp hscale
    have h2 : Tendsto (fun t : ℝ => Real.exp (-(c * t))) atTop (𝓝 0) := by
      simpa using tendsto_expNegLinear hc 1
    have hcomb := (h1.const_mul (-(1 / c ^ 2))).add (h2.const_mul (-(1 / c ^ 2)))
    rw [show (-(1 / c ^ 2) * (0 : ℝ) + -(1 / c ^ 2) * (0 : ℝ)) = 0 by ring] at hcomb
    refine hcomb.congr fun t => ?_
    field_simp
    ring
  have h := integral_Ioi_of_hasDerivAt_of_nonneg
    (g := fun t : ℝ => -(t / c + 1 / c ^ 2) * Real.exp (-(c * t))) (a := (0 : ℝ))
    ((hasDerivAt_neg_linear_exp_neg_mul (ne_of_gt hc) 0).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_neg_linear_exp_neg_mul (ne_of_gt hc) x)
    (fun x hx => mul_nonneg (le_of_lt hx) (le_of_lt (Real.exp_pos _))) hlim
  rw [h]
  simp

theorem integrableOn_exp_neg_mul_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun h : ℝ => Real.exp (-(c * h))) (Ioi 0) := by
  have hlim : Tendsto (fun t : ℝ => -Real.exp (-(c * t)) / c) atTop (𝓝 0) := by
    have := tendsto_expNegLinear hc (-(1 / c))
    simpa [neg_div, div_eq_mul_inv, mul_comm] using this
  exact integrableOn_Ioi_deriv_of_nonneg
    (g := fun t : ℝ => -Real.exp (-(c * t)) / c) (l := 0)
    ((hasDerivAt_neg_exp_neg_mul (ne_of_gt hc) 0).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_neg_exp_neg_mul (ne_of_gt hc) x)
    (fun x _ => le_of_lt (Real.exp_pos _)) hlim

theorem integrableOn_mul_exp_neg_mul_Ioi {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun h : ℝ => h * Real.exp (-(c * h))) (Ioi 0) := by
  have hlim : Tendsto (fun t : ℝ => -(t / c + 1 / c ^ 2) * Real.exp (-(c * t))) atTop (𝓝 0) := by
    have hpow : Tendsto (fun x : ℝ => x * Real.exp (-x)) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have hscale : Tendsto (fun t : ℝ => c * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id
    have h1 : Tendsto (fun t : ℝ => (c * t) * Real.exp (-(c * t))) atTop (𝓝 0) :=
      hpow.comp hscale
    have h2 : Tendsto (fun t : ℝ => Real.exp (-(c * t))) atTop (𝓝 0) := by
      simpa using tendsto_expNegLinear hc 1
    have hcomb := (h1.const_mul (-(1 / c ^ 2))).add (h2.const_mul (-(1 / c ^ 2)))
    rw [show (-(1 / c ^ 2) * (0 : ℝ) + -(1 / c ^ 2) * (0 : ℝ)) = 0 by ring] at hcomb
    refine hcomb.congr fun t => ?_
    field_simp
    ring
  exact integrableOn_Ioi_deriv_of_nonneg
    (g := fun t : ℝ => -(t / c + 1 / c ^ 2) * Real.exp (-(c * t))) (l := 0)
    ((hasDerivAt_neg_linear_exp_neg_mul (ne_of_gt hc) 0).continuousAt.continuousWithinAt)
    (fun x _ => hasDerivAt_neg_linear_exp_neg_mul (ne_of_gt hc) x)
    (fun x hx => mul_nonneg (le_of_lt hx) (le_of_lt (Real.exp_pos _))) hlim

/-! ## The compensated bracket -/

theorem packetAutocorrelation_zero_eq (w : Fin n → ℂ) (r : Fin n → ℝ) :
    packetAutocorrelation w r 0 = packetEnergy w r := by
  rw [packetAutocorrelation, packetEnergy]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (nodePacket w r x).im * (halfLineExpPacket w (lagCoeff w r 0) x).im
    = (nodePacket w r x).im ^ 2
  rw [expPacket_lagCoeff w r 0 x, add_zero]
  ring

/-- The compensated bracket `C_y(h) - e^{-3h/2} C_0` of equation `(11)`, with the sign that makes
each Gauss term one integral. -/
def gaussCompensatedBracket (w : Fin n → ℂ) (r : Fin n → ℝ) (h : ℝ) : ℝ :=
  Real.exp (-(3 * h / 2)) * packetEnergy w r - packetAutocorrelation w r h

theorem gaussCompensatedBracket_zero (w : Fin n → ℂ) (r : Fin n → ℝ) :
    gaussCompensatedBracket w r 0 = 0 := by
  rw [gaussCompensatedBracket, packetAutocorrelation_zero_eq]
  simp

/-- Each compensated Gauss term is a single half-line integral against the bracket. -/
theorem gaussTerm_eq_integral {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    (m : ℕ) :
    (1 / (2 * ((m : ℝ) + 1))) * packetEnergy w r
        - packetResolventPairing w r (2 * (m : ℝ) + 1 / 2)
      = ∫ h in Ioi (0 : ℝ),
          Real.exp (-((2 * (m : ℝ) + 1 / 2) * h)) * gaussCompensatedBracket w r h := by
  set c : ℝ := 2 * (m : ℝ) + 1 / 2 with hc
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hcpos : 0 < c := by rw [hc]; linarith
  have hwc : ∀ j, 0 < (w j + (c : ℂ)).re := by
    intro j
    have := hw j
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hshift : 0 < c + 3 / 2 := by linarith
  have hexpmul : ∀ h : ℝ, Real.exp (-(c * h)) * (Real.exp (-(3 * h / 2)) * packetEnergy w r)
      = packetEnergy w r * Real.exp (-((c + 3 / 2) * h)) := by
    intro h
    rw [show -((c + 3 / 2) * h) = -(c * h) + -(3 * h / 2) by ring, Real.exp_add]
    ring
  have hfirst : (1 / (2 * ((m : ℝ) + 1))) * packetEnergy w r
      = ∫ h in Ioi (0 : ℝ), Real.exp (-(c * h)) *
          (Real.exp (-(3 * h / 2)) * packetEnergy w r) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexpmul),
      MeasureTheory.integral_const_mul, integral_Ioi_exp_neg_mul hshift]
    rw [hc]
    field_simp
    ring
  have hsecond : packetResolventPairing w r c
      = ∫ h in Ioi (0 : ℝ), Real.exp (-(c * h)) * packetAutocorrelation w r h := by
    rw [packetResolventPairing_eq_autocorrLaplace hw r hwc, autocorrLaplace]
  have hbase : IntegrableOn
      (fun h : ℝ => packetEnergy w r * Real.exp (-((c + 3 / 2) * h))) (Ioi 0) :=
    (integrableOn_exp_neg_mul_Ioi hshift).const_mul (packetEnergy w r)
  have hint1 : IntegrableOn (fun h : ℝ => Real.exp (-(c * h)) *
      (Real.exp (-(3 * h / 2)) * packetEnergy w r)) (Ioi 0) :=
    hbase.congr_fun (fun h _ => (hexpmul h).symm) measurableSet_Ioi
  have hint2 : IntegrableOn (fun h : ℝ => Real.exp (-(c * h)) *
      packetAutocorrelation w r h) (Ioi 0) :=
    integrableOn_exp_neg_mul_packetAutocorrelation hw r hwc
  rw [hfirst, hsecond, ← MeasureTheory.integral_sub hint1 hint2]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [gaussCompensatedBracket]
  ring

/-! ## Bounds on the compensated bracket -/

/-- A uniform bound for the derivative of the compensated bracket on the closed half-line. -/
def bracketDerivBound (w : Fin n → ℂ) (r : Fin n → ℝ) : ℝ :=
  (3 / 2) * |packetEnergy w r| + (1 / 2) * (∑ k, ‖-(w k) * autocorrCoeff w r k‖)

/-- A uniform bound for the compensated bracket itself. -/
def bracketBound (w : Fin n → ℂ) (r : Fin n → ℝ) : ℝ :=
  |packetEnergy w r| + (1 / 2) * (∑ k, ‖autocorrCoeff w r k‖)

theorem bracketDerivBound_nonneg (w : Fin n → ℂ) (r : Fin n → ℝ) :
    0 ≤ bracketDerivBound w r := by
  rw [bracketDerivBound]
  have h1 : (0 : ℝ) ≤ |packetEnergy w r| := abs_nonneg _
  have h2 : (0 : ℝ) ≤ ∑ k, ‖-(w k) * autocorrCoeff w r k‖ :=
    Finset.sum_nonneg fun k _ => norm_nonneg _
  linarith

theorem bracketBound_nonneg (w : Fin n → ℂ) (r : Fin n → ℝ) : 0 ≤ bracketBound w r := by
  rw [bracketBound]
  have h1 : (0 : ℝ) ≤ |packetEnergy w r| := abs_nonneg _
  have h2 : (0 : ℝ) ≤ ∑ k, ‖autocorrCoeff w r k‖ :=
    Finset.sum_nonneg fun k _ => norm_nonneg _
  linarith

theorem hasDerivAt_gaussCompensatedBracket {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) (h : ℝ) :
    HasDerivAt (gaussCompensatedBracket w r)
      (-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r
        - packetAutocorrelationDeriv w r h) h := by
  have hlin : HasDerivAt (fun t : ℝ => -(3 * t / 2)) (-(3 / 2 : ℝ)) h := by
    have := ((hasDerivAt_id h).const_mul (3 : ℝ)).div_const 2
    simpa [Pi.neg_def] using this.neg
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(3 * t / 2)))
      (-(3 / 2) * Real.exp (-(3 * h / 2))) h := by
    refine hlin.exp.congr_deriv ?_
    ring
  exact (hexp.mul_const (packetEnergy w r)).sub (hasDerivAt_packetAutocorrelation hw r h)

theorem abs_gaussCompensatedBracket_deriv_le {w : Fin n → ℂ} (r : Fin n → ℝ) {α : ℝ}
    (hα : ∀ k, α ≤ (w k).re) (hα2 : 0 < α) {h : ℝ} (hh : 0 ≤ h) :
    |(-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r
        - packetAutocorrelationDeriv w r h)| ≤ bracketDerivBound w r := by
  have hd := abs_packetAutocorrelationDeriv_le (w := w) r hα hh
  have hexp1 : Real.exp (-(3 * h / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hexp0 : 0 < Real.exp (-(3 * h / 2)) := Real.exp_pos _
  have hexp2 : Real.exp (-(α * h)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hsum : (0 : ℝ) ≤ ∑ k, ‖-(w k) * autocorrCoeff w r k‖ :=
    Finset.sum_nonneg fun k _ => norm_nonneg _
  have hterm1 : |(-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r)|
      ≤ (3 / 2) * |packetEnergy w r| := by
    rw [abs_mul, abs_mul]
    have : |(-(3 / 2) : ℝ)| = 3 / 2 := by norm_num
    rw [this, abs_of_pos hexp0]
    nlinarith [abs_nonneg (packetEnergy w r)]
  have hterm2 : |packetAutocorrelationDeriv w r h|
      ≤ (1 / 2) * (∑ k, ‖-(w k) * autocorrCoeff w r k‖) := by
    refine le_trans hd ?_
    nlinarith
  calc |(-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r
        - packetAutocorrelationDeriv w r h)|
      ≤ |(-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r)|
        + |packetAutocorrelationDeriv w r h| := abs_sub _ _
    _ ≤ bracketDerivBound w r := by rw [bracketDerivBound]; linarith

theorem abs_gaussCompensatedBracket_le_mul {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 0 < α) {h : ℝ} (hh : 0 ≤ h) :
    |gaussCompensatedBracket w r h| ≤ bracketDerivBound w r * h := by
  have hconv : Convex ℝ (Ici (0 : ℝ)) := convex_Ici 0
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivWithinAt (gaussCompensatedBracket w r)
      (-(3 / 2) * Real.exp (-(3 * x / 2)) * packetEnergy w r
        - packetAutocorrelationDeriv w r x) (Ici (0 : ℝ)) x :=
    fun x _ => (hasDerivAt_gaussCompensatedBracket hw r x).hasDerivWithinAt
  have hbound : ∀ x ∈ Ici (0 : ℝ),
      ‖(-(3 / 2) * Real.exp (-(3 * x / 2)) * packetEnergy w r
        - packetAutocorrelationDeriv w r x)‖ ≤ bracketDerivBound w r :=
    fun x hx => abs_gaussCompensatedBracket_deriv_le r hα hα2 hx
  have h0 : (0 : ℝ) ∈ Ici (0 : ℝ) := Set.mem_Ici.mpr (le_refl 0)
  have hmem : h ∈ Ici (0 : ℝ) := Set.mem_Ici.mpr hh
  have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound h0 hmem
  rw [gaussCompensatedBracket_zero] at this
  simpa [Real.norm_eq_abs, abs_of_nonneg hh] using this

theorem abs_gaussCompensatedBracket_le {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 0 < α) {h : ℝ} (hh : 0 ≤ h) :
    |gaussCompensatedBracket w r h| ≤ bracketBound w r := by
  have hc := abs_packetAutocorrelation_le hw r hα hh
  have hexp0 : 0 < Real.exp (-(3 * h / 2)) := Real.exp_pos _
  have hexp1 : Real.exp (-(3 * h / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hexp2 : Real.exp (-(α * h)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hsum : (0 : ℝ) ≤ ∑ k, ‖autocorrCoeff w r k‖ :=
    Finset.sum_nonneg fun k _ => norm_nonneg _
  have h1 : |Real.exp (-(3 * h / 2)) * packetEnergy w r| ≤ |packetEnergy w r| := by
    rw [abs_mul, abs_of_pos hexp0]
    nlinarith [abs_nonneg (packetEnergy w r)]
  have h2 : |packetAutocorrelation w r h| ≤ (1 / 2) * (∑ k, ‖autocorrCoeff w r k‖) := by
    refine le_trans hc ?_
    nlinarith
  calc |gaussCompensatedBracket w r h|
      ≤ |Real.exp (-(3 * h / 2)) * packetEnergy w r| + |packetAutocorrelation w r h| :=
        abs_sub _ _
    _ ≤ bracketBound w r := by rw [bracketBound]; linarith

/-! ## The series–integral interchange -/

theorem continuous_gaussCompensatedBracket {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) : Continuous (gaussCompensatedBracket w r) := by
  have hc := continuous_packetAutocorrelation hw r
  have hexp : Continuous fun h : ℝ => Real.exp (-(3 * h / 2)) := by fun_prop
  exact (hexp.mul continuous_const).sub hc

theorem integrableOn_gaussTermIntegrand {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 0 < α) {c : ℝ} (hc : 0 < c) :
    IntegrableOn
      (fun h : ℝ => Real.exp (-(c * h)) * gaussCompensatedBracket w r h) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun h : ℝ => Real.exp (-(c * h)) * gaussCompensatedBracket w r h)
      (volume.restrict (Ioi 0)) :=
    (((by fun_prop : Continuous fun h : ℝ => Real.exp (-(c * h))).mul
      (continuous_gaussCompensatedBracket hw r)).aestronglyMeasurable)
  refine MeasureTheory.Integrable.mono'
    ((integrableOn_exp_neg_mul_Ioi hc).const_mul (bracketBound w r)) hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with h hh
  have hh0 : (0 : ℝ) ≤ h := le_of_lt hh
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have := abs_gaussCompensatedBracket_le hw r hα hα2 hh0
  nlinarith [Real.exp_pos (-(c * h)), bracketBound_nonneg w r]

theorem integral_norm_gaussTermIntegrand_le {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 0 < α) {c : ℝ} (hc : 0 < c) :
    (∫ h in Ioi (0 : ℝ), ‖Real.exp (-(c * h)) * gaussCompensatedBracket w r h‖)
      ≤ bracketDerivBound w r / c ^ 2 := by
  have hmajint : IntegrableOn
      (fun h : ℝ => bracketDerivBound w r * (h * Real.exp (-(c * h)))) (Ioi 0) :=
    (integrableOn_mul_exp_neg_mul_Ioi hc).const_mul (bracketDerivBound w r)
  have hnormint : IntegrableOn
      (fun h : ℝ => ‖Real.exp (-(c * h)) * gaussCompensatedBracket w r h‖) (Ioi 0) :=
    (integrableOn_gaussTermIntegrand hw r hα hα2 hc).norm
  have hle : ∀ h ∈ Ioi (0 : ℝ),
      ‖Real.exp (-(c * h)) * gaussCompensatedBracket w r h‖
        ≤ bracketDerivBound w r * (h * Real.exp (-(c * h))) := by
    intro h hh
    have hh0 : (0 : ℝ) ≤ h := le_of_lt hh
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hb := abs_gaussCompensatedBracket_le_mul hw r hα hα2 hh0
    nlinarith [Real.exp_pos (-(c * h))]
  have hmono := MeasureTheory.setIntegral_mono_on hnormint hmajint measurableSet_Ioi hle
  refine le_trans hmono ?_
  rw [MeasureTheory.integral_const_mul, integral_Ioi_mul_exp_neg_mul hc]
  rw [div_eq_mul_inv]
  ring_nf
  exact le_refl _

theorem summable_gaussTermBound (w : Fin n → ℂ) (r : Fin n → ℝ) :
    Summable (fun m : ℕ => bracketDerivBound w r / (2 * (m : ℝ) + 1 / 2) ^ 2) := by
  have hbase : Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 2) := by
    have h := Real.summable_one_div_nat_pow.mpr one_lt_two
    have := (summable_nat_add_iff 1).mpr h
    simpa using this
  refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    ((hbase.mul_left (4 * bracketDerivBound w r)))
  · have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have : (0 : ℝ) < (2 * (m : ℝ) + 1 / 2) ^ 2 := by positivity
    exact div_nonneg (bracketDerivBound_nonneg w r) (le_of_lt this)
  · have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hpos : (0 : ℝ) < (2 * (m : ℝ) + 1 / 2) := by linarith
    have hpos2 : (0 : ℝ) < ((m : ℝ) + 1) := by linarith
    have hcomp : ((m : ℝ) + 1) / 2 ≤ 2 * (m : ℝ) + 1 / 2 := by linarith
    have hsq : (((m : ℝ) + 1) / 2) ^ 2 ≤ (2 * (m : ℝ) + 1 / 2) ^ 2 := by nlinarith
    have hM := bracketDerivBound_nonneg w r
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (2 * (m : ℝ) + 1 / 2) ^ 2)]
    have hkey : 4 * bracketDerivBound w r * (1 / ((m : ℝ) + 1) ^ 2)
        * (((m : ℝ) + 1) / 2) ^ 2 = bracketDerivBound w r := by
      field_simp
      ring
    nlinarith [mul_le_mul_of_nonneg_left hsq
      (by positivity : (0 : ℝ) ≤ 4 * bracketDerivBound w r * (1 / ((m : ℝ) + 1) ^ 2))]

theorem tsum_exp_neg_gauss {h : ℝ} (hh : 0 < h) :
    ∑' m : ℕ, Real.exp (-((2 * (m : ℝ) + 1 / 2) * h)) = screwTailKernel h := by
  have hterm : ∀ m : ℕ, Real.exp (-((2 * (m : ℝ) + 1 / 2) * h))
      = Real.exp (-(h / 2)) * (Real.exp (-(2 * h))) ^ m := by
    intro m
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [tsum_congr hterm, tsum_mul_left]
  have hlt : Real.exp (-(2 * h)) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  rw [tsum_geometric_of_lt_one (le_of_lt (Real.exp_pos _)) hlt, screwTailKernel]
  rw [div_eq_mul_inv]
  ring_nf

/-- The compensated Gauss series is one half-line integral against the tail kernel. -/
theorem tsum_gaussTerm_eq_integral {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 0 < α) :
    (∑' m : ℕ, ((1 / (2 * ((m : ℝ) + 1))) * packetEnergy w r
        - packetResolventPairing w r (2 * (m : ℝ) + 1 / 2)))
      = ∫ h in Ioi (0 : ℝ), screwTailKernel h * gaussCompensatedBracket w r h := by
  have hcpos : ∀ m : ℕ, (0 : ℝ) < 2 * (m : ℝ) + 1 / 2 := by
    intro m
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hint : ∀ m : ℕ, IntegrableOn
      (fun h : ℝ => Real.exp (-((2 * (m : ℝ) + 1 / 2) * h)) * gaussCompensatedBracket w r h)
      (Ioi 0) := fun m => integrableOn_gaussTermIntegrand hw r hα hα2 (hcpos m)
  have hsum : Summable (fun m : ℕ => ∫ h in Ioi (0 : ℝ),
      ‖Real.exp (-((2 * (m : ℝ) + 1 / 2) * h)) * gaussCompensatedBracket w r h‖) := by
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) (summable_gaussTermBound w r)
    · exact MeasureTheory.integral_nonneg fun h => norm_nonneg _
    · exact integral_norm_gaussTermIntegrand_le hw r hα hα2 (hcpos m)
  rw [tsum_congr (fun m => gaussTerm_eq_integral hw r m)]
  rw [MeasureTheory.integral_tsum_of_summable_integral_norm hint hsum]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun h hh => ?_
  rw [tsum_mul_right, tsum_exp_neg_gauss hh]

/-- **Equation `(11)`.**  The compensated Gauss-resolvent quadratic is the archimedean contact
mass plus one tail-kernel current against the compensated bracket. -/
theorem gaussResolventQuadratic_eq {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 0 < α) :
    gaussResolventQuadratic w r
      = -((Real.log Real.pi + Real.eulerMascheroniConstant) / 2) * packetEnergy w r
        - ∫ h in Ioi (0 : ℝ), screwTailKernel h *
            (packetAutocorrelation w r h - Real.exp (-(3 * h / 2)) * packetEnergy w r) := by
  rw [gaussResolventQuadratic, tsum_gaussTerm_eq_integral hw r hα hα2]
  have hflip : (∫ h in Ioi (0 : ℝ), screwTailKernel h * gaussCompensatedBracket w r h)
      = -∫ h in Ioi (0 : ℝ), screwTailKernel h *
          (packetAutocorrelation w r h - Real.exp (-(3 * h / 2)) * packetEnergy w r) := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
    simp only [gaussCompensatedBracket]
    ring
  rw [hflip]
  ring

/-! ## The sharp exponential bounds -/

theorem abs_bracketDeriv_le_exp {w : Fin n → ℂ} (r : Fin n → ℝ) {α : ℝ}
    (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 ≤ α) {h : ℝ} (hh : 0 ≤ h) :
    |(-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r
        - packetAutocorrelationDeriv w r h)|
      ≤ bracketDerivBound w r * Real.exp (-(h / 2)) := by
  have hd := abs_packetAutocorrelationDeriv_le (w := w) r hα hh
  have hexp0 : 0 < Real.exp (-(h / 2)) := Real.exp_pos _
  have hcmp1 : Real.exp (-(3 * h / 2)) ≤ Real.exp (-(h / 2)) := by
    rw [Real.exp_le_exp]
    linarith
  have hcmp2 : Real.exp (-(α * h)) ≤ Real.exp (-(h / 2)) := by
    rw [Real.exp_le_exp]
    nlinarith
  have hsum : (0 : ℝ) ≤ ∑ k, ‖-(w k) * autocorrCoeff w r k‖ :=
    Finset.sum_nonneg fun k _ => norm_nonneg _
  have hterm1 : |(-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r)|
      ≤ (3 / 2) * |packetEnergy w r| * Real.exp (-(h / 2)) := by
    rw [abs_mul, abs_mul, show |(-(3 / 2) : ℝ)| = 3 / 2 by norm_num,
      abs_of_pos (Real.exp_pos _)]
    nlinarith [abs_nonneg (packetEnergy w r)]
  have hterm2 : |packetAutocorrelationDeriv w r h|
      ≤ (1 / 2) * (∑ k, ‖-(w k) * autocorrCoeff w r k‖) * Real.exp (-(h / 2)) := by
    refine le_trans hd ?_
    nlinarith
  calc |(-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r
        - packetAutocorrelationDeriv w r h)|
      ≤ |(-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r)|
        + |packetAutocorrelationDeriv w r h| := abs_sub _ _
    _ ≤ bracketDerivBound w r * Real.exp (-(h / 2)) := by
        rw [bracketDerivBound]
        nlinarith

theorem hasDerivAt_bracketBoundary (M : ℝ) (x : ℝ) :
    HasDerivAt (fun t : ℝ => 2 * M * (1 - Real.exp (-(t / 2))))
      (M * Real.exp (-(x / 2))) x := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(t / 2)))
      (-(Real.exp (-(x / 2)) / 2)) x := hasDerivAt_expNegHalf x
  have := ((hexp.const_sub 1).const_mul (2 * M))
  refine this.congr_deriv ?_
  ring

/-- **The sharp contact bound.**  The compensated bracket is dominated by the primitive of its
own derivative majorant. -/
theorem abs_gaussCompensatedBracket_le_exp {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 ≤ α) {h : ℝ} (hh : 0 ≤ h) :
    |gaussCompensatedBracket w r h|
      ≤ 2 * bracketDerivBound w r * (1 - Real.exp (-(h / 2))) := by
  have hcont : ContinuousOn (gaussCompensatedBracket w r) (Icc 0 h) :=
    (continuous_gaussCompensatedBracket hw r).continuousOn
  have hderiv : ∀ x ∈ Ico (0 : ℝ) h, HasDerivWithinAt (gaussCompensatedBracket w r)
      (-(3 / 2) * Real.exp (-(3 * x / 2)) * packetEnergy w r
        - packetAutocorrelationDeriv w r x) (Ici x) x :=
    fun x _ => (hasDerivAt_gaussCompensatedBracket hw r x).hasDerivWithinAt
  have hstart : ‖gaussCompensatedBracket w r 0‖ ≤ 2 * bracketDerivBound w r * (1 - Real.exp (-((0:ℝ) / 2))) := by
    rw [gaussCompensatedBracket_zero]
    simp
  have hB : ∀ x : ℝ, HasDerivAt (fun t : ℝ => 2 * bracketDerivBound w r * (1 - Real.exp (-(t / 2))))
      (bracketDerivBound w r * Real.exp (-(x / 2))) x :=
    fun x => hasDerivAt_bracketBoundary (bracketDerivBound w r) x
  have hbound : ∀ x ∈ Ico (0 : ℝ) h,
      ‖(-(3 / 2) * Real.exp (-(3 * x / 2)) * packetEnergy w r
        - packetAutocorrelationDeriv w r x)‖
        ≤ bracketDerivBound w r * Real.exp (-(x / 2)) := by
    intro x hx
    simpa [Real.norm_eq_abs] using abs_bracketDeriv_le_exp r hα hα2 hx.1
  have := image_norm_le_of_norm_deriv_right_le_deriv_boundary hcont hderiv hstart hB hbound
    (Set.mem_Icc.mpr ⟨hh, le_refl h⟩)
  simpa using this

/-! ## Continuity and integrability of the tail objects -/

theorem continuousOn_screwTailKernel : ContinuousOn screwTailKernel (Ioi 0) := by
  intro h hh
  have hpos : 0 < 1 - Real.exp (-(2 * h)) := by
    have : Real.exp (-(2 * h)) < 1 := by
      rw [Real.exp_lt_one_iff]
      have := Set.mem_Ioi.mp hh
      linarith
    linarith
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.div (by fun_prop) (by fun_prop) (ne_of_gt hpos)

theorem continuousOn_screwTailPrimitive : ContinuousOn screwTailPrimitive (Ioi 0) := by
  intro h hh
  have hh0 : 0 < h := Set.mem_Ioi.mp hh
  have h0 := exp_neg_half_pos h
  have h1 := exp_neg_half_lt_one hh0
  refine ContinuousAt.continuousWithinAt ?_
  refine ContinuousAt.add (ContinuousAt.div_const (ContinuousAt.sub ?_ ?_) 2) ?_
  · exact (Real.continuousAt_log (by linarith)).comp (by fun_prop)
  · exact (Real.continuousAt_log (by linarith)).comp (by fun_prop)
  · exact Real.continuous_arctan.continuousAt.comp (by fun_prop)

theorem screwTailKernel_mul_oneSub_le {h : ℝ} (hh : 0 < h) :
    screwTailKernel h * (1 - Real.exp (-(h / 2))) ≤ Real.exp (-(h / 2)) := by
  have h0 := exp_neg_half_pos h
  have h1 := exp_neg_half_lt_one hh
  rw [screwTailKernel, ← exp_neg_half_pow_four h]
  set u : ℝ := Real.exp (-(h / 2)) with hu
  have hfac : 1 - u ^ 4 = (1 - u) * ((1 + u) * (1 + u ^ 2)) := by ring
  have hne : (1 : ℝ) - u ≠ 0 := by linarith
  have hkey : u / (1 - u ^ 4) * (1 - u) = u / ((1 + u) * (1 + u ^ 2)) := by
    rw [hfac]
    field_simp
  rw [hkey, div_le_iff₀ (by positivity)]
  nlinarith

theorem integrableOn_screwTailPrimitive_mul_exp :
    IntegrableOn (fun h : ℝ => screwTailPrimitive h * Real.exp (-(3 * h / 2))) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg (g := screwMomentPrimitive) (l := 0)
    (continuous_screwMomentPrimitive.continuousWithinAt)
    (fun x hx => hasDerivAt_screwMomentPrimitive hx)
    (fun x hx => screwTailPrimitive_mul_exp_nonneg hx)
    screwMomentPrimitive_tendsto_zero

theorem integrableOn_screwTailKernel_mul_bracket {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 ≤ α) :
    IntegrableOn
      (fun h : ℝ => screwTailKernel h * gaussCompensatedBracket w r h) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun h : ℝ => screwTailKernel h * gaussCompensatedBracket w r h)
      (volume.restrict (Ioi 0)) :=
    (continuousOn_screwTailKernel.mul
      (continuous_gaussCompensatedBracket hw r).continuousOn).aestronglyMeasurable
        measurableSet_Ioi
  have hα0 : 0 < α := lt_of_lt_of_le (by norm_num) hα2
  refine MeasureTheory.Integrable.mono'
    ((integrableOn_exp_neg_mul_Ioi (by norm_num : (0:ℝ) < 1 / 2)).const_mul
      (2 * bracketDerivBound w r)) hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with h hh
  have hh0 : (0 : ℝ) < h := Set.mem_Ioi.mp hh
  have hk : 0 ≤ screwTailKernel h := screwTailKernel_nonneg hh0
  have hb := abs_gaussCompensatedBracket_le_exp hw r hα hα2 (le_of_lt hh0)
  have hprod := screwTailKernel_mul_oneSub_le hh0
  have hM : 0 ≤ bracketDerivBound w r := bracketDerivBound_nonneg w r
  have hhalf : Real.exp (-((1 / 2 : ℝ) * h)) = Real.exp (-(h / 2)) := by
    congr 1
    ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk, hhalf]
  calc screwTailKernel h * |gaussCompensatedBracket w r h|
      ≤ screwTailKernel h * (2 * bracketDerivBound w r * (1 - Real.exp (-(h / 2)))) :=
        mul_le_mul_of_nonneg_left hb hk
    _ = 2 * bracketDerivBound w r * (screwTailKernel h * (1 - Real.exp (-(h / 2)))) := by ring
    _ ≤ 2 * bracketDerivBound w r * Real.exp (-(h / 2)) := by
        exact mul_le_mul_of_nonneg_left hprod (by linarith)

theorem integrableOn_screwTailPrimitive_mul_bracketDeriv {w : Fin n → ℂ}
    (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) {α : ℝ} (hα : ∀ k, α ≤ (w k).re)
    (hα2 : 1 / 2 ≤ α) :
    IntegrableOn (fun h : ℝ => screwTailPrimitive h *
      (-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r
        - packetAutocorrelationDeriv w r h)) (Ioi 0) := by
  have hcontderiv : Continuous (fun h : ℝ =>
      -(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r
        - packetAutocorrelationDeriv w r h) := by
    have h1 : Continuous fun h : ℝ => -(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r := by
      fun_prop
    have h2 : Continuous (packetAutocorrelationDeriv w r) := by
      unfold packetAutocorrelationDeriv
      exact (Complex.continuous_re.comp
        (continuous_halfLineExpPacket w (fun k => -(w k) * autocorrCoeff w r k))).const_mul _
    exact h1.sub h2
  have hmeas : AEStronglyMeasurable
      (fun h : ℝ => screwTailPrimitive h *
        (-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r
          - packetAutocorrelationDeriv w r h)) (volume.restrict (Ioi 0)) :=
    (continuousOn_screwTailPrimitive.mul hcontderiv.continuousOn).aestronglyMeasurable
      measurableSet_Ioi
  refine MeasureTheory.Integrable.mono'
    (integrableOn_screwTailPrimitive_mul_exp_half.const_mul (bracketDerivBound w r)) hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with h hh
  have hh0 : (0 : ℝ) < h := Set.mem_Ioi.mp hh
  have hA : 0 ≤ screwTailPrimitive h := by
    have h0 := exp_neg_half_pos h
    have h1 := exp_neg_half_lt_one hh0
    have hlogm : Real.log (1 - Real.exp (-(h / 2))) ≤ 0 :=
      Real.log_nonpos (by linarith) (by linarith)
    have hlogp : 0 ≤ Real.log (1 + Real.exp (-(h / 2))) := Real.log_nonneg (by linarith)
    have harc : 0 ≤ Real.arctan (Real.exp (-(h / 2))) := Real.arctan_nonneg.mpr (le_of_lt h0)
    rw [screwTailPrimitive]
    linarith
  have hd := abs_bracketDeriv_le_exp r hα hα2 (le_of_lt hh0)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hA]
  calc screwTailPrimitive h * |(-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r
        - packetAutocorrelationDeriv w r h)|
      ≤ screwTailPrimitive h * (bracketDerivBound w r * Real.exp (-(h / 2))) :=
        mul_le_mul_of_nonneg_left hd hA
    _ = bracketDerivBound w r * (screwTailPrimitive h * Real.exp (-(h / 2))) := by ring

/-! ## The half-line integration by parts -/

theorem continuous_screwTailPrimitive_mul_oneSub :
    Continuous (fun h : ℝ => screwTailPrimitive h * (1 - Real.exp (-(h / 2)))) := by
  have hexp : Continuous fun h : ℝ => Real.exp (-(h / 2)) := by fun_prop
  have hrw : (fun h : ℝ => screwTailPrimitive h * (1 - Real.exp (-(h / 2))))
      = fun h : ℝ => (1 / 2) * ((1 - Real.exp (-(h / 2))) * Real.log (1 + Real.exp (-(h / 2))))
        - (1 / 2) * ((1 - Real.exp (-(h / 2))) * Real.log (1 - Real.exp (-(h / 2))))
        + (1 - Real.exp (-(h / 2))) * Real.arctan (Real.exp (-(h / 2))) := by
    funext h
    rw [screwTailPrimitive]
    ring
  rw [hrw]
  have h1 : Continuous fun h : ℝ =>
      (1 - Real.exp (-(h / 2))) * Real.log (1 + Real.exp (-(h / 2))) := by
    refine (continuous_const.sub hexp).mul ?_
    refine Real.continuousOn_log.comp_continuous (continuous_const.add hexp) fun h => ?_
    have := Real.exp_pos (-(h / 2))
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hcon
    linarith
  have h2 : Continuous fun h : ℝ =>
      (1 - Real.exp (-(h / 2))) * Real.log (1 - Real.exp (-(h / 2))) :=
    Real.continuous_mul_log.comp (continuous_const.sub hexp)
  have h3 : Continuous fun h : ℝ =>
      (1 - Real.exp (-(h / 2))) * Real.arctan (Real.exp (-(h / 2))) :=
    (continuous_const.sub hexp).mul (Real.continuous_arctan.comp hexp)
  exact ((h1.const_mul _).sub (h2.const_mul _)).add h3

theorem screwTailPrimitive_mul_oneSub_zero :
    screwTailPrimitive 0 * (1 - Real.exp (-((0 : ℝ) / 2))) = 0 := by
  simp

theorem tendsto_screwTailBoundary_zero {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 ≤ α) :
    Tendsto (fun h : ℝ => -(screwTailPrimitive h * gaussCompensatedBracket w r h))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  have hg : Tendsto (fun h : ℝ =>
      2 * bracketDerivBound w r * (screwTailPrimitive h * (1 - Real.exp (-(h / 2)))))
      (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
    have hc := continuous_screwTailPrimitive_mul_oneSub.continuousAt (x := (0 : ℝ))
    have := (hc.tendsto.const_mul (2 * bracketDerivBound w r)).mono_left
      (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    rw [screwTailPrimitive_mul_oneSub_zero] at this
    simpa using this
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh0 : (0 : ℝ) < h := Set.mem_Ioi.mp hh
  have hA : 0 ≤ screwTailPrimitive h := by
    have h0 := exp_neg_half_pos h
    have h1 := exp_neg_half_lt_one hh0
    have hlogm : Real.log (1 - Real.exp (-(h / 2))) ≤ 0 :=
      Real.log_nonpos (by linarith) (by linarith)
    have hlogp : 0 ≤ Real.log (1 + Real.exp (-(h / 2))) := Real.log_nonneg (by linarith)
    have harc : 0 ≤ Real.arctan (Real.exp (-(h / 2))) := Real.arctan_nonneg.mpr (le_of_lt h0)
    rw [screwTailPrimitive]
    linarith
  have hb := abs_gaussCompensatedBracket_le_exp hw r hα hα2 (le_of_lt hh0)
  rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg hA]
  calc screwTailPrimitive h * |gaussCompensatedBracket w r h|
      ≤ screwTailPrimitive h * (2 * bracketDerivBound w r * (1 - Real.exp (-(h / 2)))) :=
        mul_le_mul_of_nonneg_left hb hA
    _ = 2 * bracketDerivBound w r * (screwTailPrimitive h * (1 - Real.exp (-(h / 2)))) := by
        ring

theorem continuousWithinAt_screwTailBoundary {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 ≤ α) :
    ContinuousWithinAt (fun h : ℝ => -(screwTailPrimitive h * gaussCompensatedBracket w r h))
      (Ici 0) 0 := by
  have h0 : -(screwTailPrimitive 0 * gaussCompensatedBracket w r 0) = 0 := by
    rw [gaussCompensatedBracket_zero]
    ring
  have hset : Ici (0 : ℝ) = Ioi 0 ∪ {0} := by
    ext x
    simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ioi, Set.mem_singleton_iff]
    constructor
    · intro hx
      rcases lt_or_eq_of_le hx with h' | h'
      · exact Or.inl h'
      · exact Or.inr h'.symm
    · rintro (h' | rfl)
      · exact le_of_lt h'
      · exact le_refl 0
  rw [ContinuousWithinAt, hset, nhdsWithin_union, h0]
  refine Filter.Tendsto.sup (tendsto_screwTailBoundary_zero hw r hα hα2) ?_
  rw [nhdsWithin_singleton]
  simpa [h0] using
    tendsto_pure_nhds (fun h : ℝ => -(screwTailPrimitive h * gaussCompensatedBracket w r h)) 0

theorem tendsto_screwTailBoundary_atTop {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 0 < α) :
    Tendsto (fun h : ℝ => -(screwTailPrimitive h * gaussCompensatedBracket w r h))
      atTop (𝓝 0) := by
  have hg : Tendsto (fun h : ℝ => bracketBound w r * screwTailPrimitive h) atTop (𝓝 0) := by
    simpa using screwTailPrimitive_tendsto_zero.const_mul (bracketBound w r)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with h hh0
  have hA : 0 ≤ screwTailPrimitive h := by
    have h0 := exp_neg_half_pos h
    have h1 := exp_neg_half_lt_one hh0
    have hlogm : Real.log (1 - Real.exp (-(h / 2))) ≤ 0 :=
      Real.log_nonpos (by linarith) (by linarith)
    have hlogp : 0 ≤ Real.log (1 + Real.exp (-(h / 2))) := Real.log_nonneg (by linarith)
    have harc : 0 ≤ Real.arctan (Real.exp (-(h / 2))) := Real.arctan_nonneg.mpr (le_of_lt h0)
    rw [screwTailPrimitive]
    linarith
  have hb := abs_gaussCompensatedBracket_le hw r hα hα2 (le_of_lt hh0)
  rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_nonneg hA]
  calc screwTailPrimitive h * |gaussCompensatedBracket w r h|
      ≤ screwTailPrimitive h * bracketBound w r := mul_le_mul_of_nonneg_left hb hA
    _ = bracketBound w r * screwTailPrimitive h := by ring

theorem hasDerivAt_screwTailBoundary {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) {h : ℝ} (hh : 0 < h) :
    HasDerivAt (fun t : ℝ => -(screwTailPrimitive t * gaussCompensatedBracket w r t))
      (screwTailKernel h * gaussCompensatedBracket w r h
        - screwTailPrimitive h * (-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r
          - packetAutocorrelationDeriv w r h)) h := by
  have hA := hasDerivAt_screwTailPrimitive hh
  have hG := hasDerivAt_gaussCompensatedBracket hw r h
  have := (hA.mul hG).neg
  refine (this.congr_deriv ?_)
  ring

/-- **The half-line integration by parts.**  The tail-kernel current equals the tail-primitive
current against the derivative of the bracket. -/
theorem integral_screwTail_byParts {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 ≤ α) :
    (∫ h in Ioi (0 : ℝ), screwTailKernel h * gaussCompensatedBracket w r h)
      = ∫ h in Ioi (0 : ℝ), screwTailPrimitive h *
          (-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r
            - packetAutocorrelationDeriv w r h) := by
  have hα0 : 0 < α := lt_of_lt_of_le (by norm_num) hα2
  have hint1 := integrableOn_screwTailKernel_mul_bracket hw r hα hα2
  have hint2 := integrableOn_screwTailPrimitive_mul_bracketDeriv hw r hα hα2
  have hFTC := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := fun t : ℝ => -(screwTailPrimitive t * gaussCompensatedBracket w r t))
    (f' := fun h : ℝ => screwTailKernel h * gaussCompensatedBracket w r h
      - screwTailPrimitive h * (-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r
        - packetAutocorrelationDeriv w r h))
    (a := (0 : ℝ)) (m := 0)
    (continuousWithinAt_screwTailBoundary hw r hα hα2)
    (fun x hx => hasDerivAt_screwTailBoundary hw r (Set.mem_Ioi.mp hx))
    (hint1.sub hint2)
    (tendsto_screwTailBoundary_atTop hw r hα hα0)
  rw [MeasureTheory.integral_sub hint1 hint2] at hFTC
  have hzero : -(screwTailPrimitive 0 * gaussCompensatedBracket w r 0) = 0 := by
    rw [gaussCompensatedBracket_zero]
    ring
  simp only [hzero] at hFTC
  linarith

/-! ## Equation `(12)`: the canonical contact normalization -/

theorem integrableOn_screwTailPrimitive_mul_autocorrDeriv {w : Fin n → ℂ}
    (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) {α : ℝ} (hα : ∀ k, α ≤ (w k).re)
    (hα2 : 1 / 2 ≤ α) :
    IntegrableOn
      (fun h : ℝ => screwTailPrimitive h * packetAutocorrelationDeriv w r h) (Ioi 0) := by
  have hcont : Continuous (packetAutocorrelationDeriv w r) := by
    unfold packetAutocorrelationDeriv
    exact (Complex.continuous_re.comp
      (continuous_halfLineExpPacket w (fun k => -(w k) * autocorrCoeff w r k))).const_mul _
  have hmeas : AEStronglyMeasurable
      (fun h : ℝ => screwTailPrimitive h * packetAutocorrelationDeriv w r h)
      (volume.restrict (Ioi 0)) :=
    (continuousOn_screwTailPrimitive.mul hcont.continuousOn).aestronglyMeasurable
      measurableSet_Ioi
  set B : ℝ := (1 / 2) * (∑ k, ‖-(w k) * autocorrCoeff w r k‖) with hB
  have hBnn : 0 ≤ B := by
    rw [hB]
    have : (0 : ℝ) ≤ ∑ k, ‖-(w k) * autocorrCoeff w r k‖ :=
      Finset.sum_nonneg fun k _ => norm_nonneg _
    linarith
  refine MeasureTheory.Integrable.mono'
    (integrableOn_screwTailPrimitive_mul_exp_half.const_mul B) hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with h hh
  have hh0 : (0 : ℝ) < h := Set.mem_Ioi.mp hh
  have hA : 0 ≤ screwTailPrimitive h := by
    have h0 := exp_neg_half_pos h
    have h1 := exp_neg_half_lt_one hh0
    have hlogm : Real.log (1 - Real.exp (-(h / 2))) ≤ 0 :=
      Real.log_nonpos (by linarith) (by linarith)
    have hlogp : 0 ≤ Real.log (1 + Real.exp (-(h / 2))) := Real.log_nonneg (by linarith)
    have harc : 0 ≤ Real.arctan (Real.exp (-(h / 2))) := Real.arctan_nonneg.mpr (le_of_lt h0)
    rw [screwTailPrimitive]
    linarith
  have hd := abs_packetAutocorrelationDeriv_le (w := w) r hα (le_of_lt hh0)
  have hcmp : Real.exp (-(α * h)) ≤ Real.exp (-(h / 2)) := by
    rw [Real.exp_le_exp]
    nlinarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hA]
  calc screwTailPrimitive h * |packetAutocorrelationDeriv w r h|
      ≤ screwTailPrimitive h * (B * Real.exp (-(h / 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        refine le_trans hd ?_
        rw [hB]
        nlinarith [Real.exp_pos (-(α * h))]
    _ = B * (screwTailPrimitive h * Real.exp (-(h / 2))) := by ring

theorem screwContactConst_eq :
    screwContactConst
      = (Real.log Real.pi + Real.eulerMascheroniConstant) / 2
        + (3 / 2) * Real.log 2 + Real.pi / 4 := by
  rw [screwContactConst]
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  rw [Real.log_mul (by norm_num) Real.pi_ne_zero, h8]
  ring

/-- **Equation `(12)`.**  The compensated Gauss quadratic is one tail-primitive current plus the
canonical contact normalization. -/
theorem gaussResolventQuadratic_eq_tailCurrent {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 ≤ α) :
    gaussResolventQuadratic w r
      = -(∫ h in Ioi (0 : ℝ), screwTailPrimitive h * packetAutocorrelationDeriv w r h)
        - screwContactConst * packetEnergy w r := by
  have hα0 : 0 < α := lt_of_lt_of_le (by norm_num) hα2
  have hsplit : (∫ h in Ioi (0 : ℝ), screwTailPrimitive h *
      (-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r
        - packetAutocorrelationDeriv w r h))
      = (-(3 / 2) * packetEnergy w r) * (Real.log 2 + Real.pi / 6)
        - ∫ h in Ioi (0 : ℝ), screwTailPrimitive h * packetAutocorrelationDeriv w r h := by
    have hA : IntegrableOn (fun h : ℝ => (-(3 / 2) * packetEnergy w r) *
        (screwTailPrimitive h * Real.exp (-(3 * h / 2)))) (Ioi 0) :=
      integrableOn_screwTailPrimitive_mul_exp.const_mul _
    have hB := integrableOn_screwTailPrimitive_mul_autocorrDeriv hw r hα hα2
    have hcongr : (fun h : ℝ => screwTailPrimitive h *
        (-(3 / 2) * Real.exp (-(3 * h / 2)) * packetEnergy w r
          - packetAutocorrelationDeriv w r h))
        = fun h : ℝ => (-(3 / 2) * packetEnergy w r) *
            (screwTailPrimitive h * Real.exp (-(3 * h / 2)))
          - screwTailPrimitive h * packetAutocorrelationDeriv w r h := by
      funext h
      ring
    rw [hcongr, MeasureTheory.integral_sub hA hB, MeasureTheory.integral_const_mul,
      integral_Ioi_screwTailPrimitive_mul_exp]
  have hgauss : gaussResolventQuadratic w r
      = -((Real.log Real.pi + Real.eulerMascheroniConstant) / 2) * packetEnergy w r
        + ∫ h in Ioi (0 : ℝ), screwTailKernel h * gaussCompensatedBracket w r h := by
    rw [gaussResolventQuadratic, tsum_gaussTerm_eq_integral hw r hα hα0]
  rw [hgauss, integral_screwTail_byParts hw r hα hα2, hsplit, screwContactConst_eq]
  ring

/-! ## Equations `(16)` and `(18)`: the normalized screw current -/

theorem integrableOn_packetAutocorrelationDeriv {w : Fin n → ℂ} (r : Fin n → ℝ) {α : ℝ}
    (hα : ∀ k, α ≤ (w k).re) (hα2 : 0 < α) :
    IntegrableOn (packetAutocorrelationDeriv w r) (Ioi 0) := by
  have hcont : Continuous (packetAutocorrelationDeriv w r) := by
    unfold packetAutocorrelationDeriv
    exact (Complex.continuous_re.comp
      (continuous_halfLineExpPacket w (fun k => -(w k) * autocorrCoeff w r k))).const_mul _
  refine MeasureTheory.Integrable.mono'
    (integrableOn_expMajorant hα2 ((1 / 2) * (∑ k, ‖-(w k) * autocorrCoeff w r k‖)))
    hcont.aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with h hh
  have hh0 : (0 : ℝ) < h := Set.mem_Ioi.mp hh
  rw [Real.norm_eq_abs]
  exact abs_packetAutocorrelationDeriv_le (w := w) r hα (le_of_lt hh0)

theorem tendsto_packetAutocorrelation_atTop {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 0 < α) :
    Tendsto (packetAutocorrelation w r) atTop (𝓝 0) := by
  have hg : Tendsto (fun h : ℝ =>
      ((1 / 2) * (∑ k, ‖autocorrCoeff w r k‖)) * Real.exp (-(α * h))) atTop (𝓝 0) :=
    tendsto_expNegLinear hα2 _
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with h hh
  rw [Real.norm_eq_abs]
  have := abs_packetAutocorrelation_le hw r hα hh
  linarith

/-- The total transverse current of the autocorrelation is minus its contact mass. -/
theorem integral_Ioi_packetAutocorrelationDeriv {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 0 < α) :
    (∫ h in Ioi (0 : ℝ), packetAutocorrelationDeriv w r h) = -packetEnergy w r := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto
    (f := packetAutocorrelation w r) (f' := packetAutocorrelationDeriv w r)
    (a := (0 : ℝ)) (m := 0)
    ((continuous_packetAutocorrelation hw r).continuousWithinAt)
    (fun x _ => hasDerivAt_packetAutocorrelation hw r x)
    (integrableOn_packetAutocorrelationDeriv r hα hα2)
    (tendsto_packetAutocorrelation_atTop hw r hα hα2)
  rw [h, packetAutocorrelation_zero_eq]
  ring

theorem integrableOn_criticalCurrentReal {w : Fin n → ℂ} (r : Fin n → ℝ) {α : ℝ}
    (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 < α) :
    IntegrableOn (fun h : ℝ =>
      criticalMellinCompletedError h * packetAutocorrelationDeriv w r h) (Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ => (criticalCurrent w r x).re) (Ioi 0) :=
    (integrableOn_criticalCurrent_Ioi (w := w) r hα hα2 (le_refl (0 : ℝ))).re
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  show (criticalCurrent w r x).re
    = criticalMellinCompletedError x * packetAutocorrelationDeriv w r x
  rw [criticalCurrent, autocorrTestDeriv]
  simp

/-- **Equation `(16)`.**  The normalized one-sided screw current. -/
def screwCurrent (h : ℝ) : ℝ :=
  criticalMellinCompletedError h + screwTailPrimitive h - screwContactConst

/-- **Equation `(18)`.**  The complete absolute-Euler paired Xi value is one classical current
integral against the normalized screw current. -/
theorem paired_screwCurrent {w : Fin n → ℂ} (r : Fin n → ℝ) {α : ℝ}
    (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 < α) :
    pairedQuadratic w r completedCriticalValue
      = -8 * ∫ h in Ioi (0 : ℝ), screwCurrent h * packetAutocorrelationDeriv w r h := by
  have hhalf : ∀ j, 1 / 2 < (w j).re := fun j => lt_of_lt_of_le hα2 (hα j)
  have hw : ∀ j, 0 < (w j).re := fun j => lt_trans (by norm_num) (hhalf j)
  have hα0 : 0 < α := lt_trans (by norm_num) hα2
  have hint1 := integrableOn_criticalCurrentReal (w := w) r hα hα2
  have hint2 := integrableOn_screwTailPrimitive_mul_autocorrDeriv hw r hα (le_of_lt hα2)
  have hint3 : IntegrableOn (fun h : ℝ =>
      screwContactConst * packetAutocorrelationDeriv w r h) (Ioi 0) :=
    (integrableOn_packetAutocorrelationDeriv r hα hα0).const_mul _
  have hsplit : (∫ h in Ioi (0 : ℝ), screwCurrent h * packetAutocorrelationDeriv w r h)
      = (∫ h in Ioi (0 : ℝ),
          criticalMellinCompletedError h * packetAutocorrelationDeriv w r h)
        + (∫ h in Ioi (0 : ℝ), screwTailPrimitive h * packetAutocorrelationDeriv w r h)
        - screwContactConst * (∫ h in Ioi (0 : ℝ), packetAutocorrelationDeriv w r h) := by
    have hcongr : (fun h : ℝ => screwCurrent h * packetAutocorrelationDeriv w r h)
        = fun h : ℝ => (criticalMellinCompletedError h * packetAutocorrelationDeriv w r h
            + screwTailPrimitive h * packetAutocorrelationDeriv w r h)
          - screwContactConst * packetAutocorrelationDeriv w r h := by
      funext h
      rw [screwCurrent]
      ring
    have hsum12 : IntegrableOn (fun h : ℝ =>
        criticalMellinCompletedError h * packetAutocorrelationDeriv w r h
          + screwTailPrimitive h * packetAutocorrelationDeriv w r h) (Ioi 0) := hint1.add hint2
    rw [hcongr, MeasureTheory.integral_sub hsum12 hint3,
      MeasureTheory.integral_add hint1 hint2, MeasureTheory.integral_const_mul]
  rw [paired_completedCriticalValue r hα hα2,
    gaussResolventQuadratic_eq_tailCurrent hw r hα (le_of_lt hα2), hsplit,
    integral_Ioi_packetAutocorrelationDeriv hw r hα hα0, criticalCurrentIntegralReal]
  ring

end

end RHTower
