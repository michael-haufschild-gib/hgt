import GaloisForLFunctions.HTGeometry.GaussianL2Tail
import GaloisForLFunctions.HTGeometry.MassGaugeDampedSymbol
import GaloisForLFunctions.RHTower.MassGaugeSuperluminalCompression

/-!
# The Gaussian causal packet

The wave packet used to read the exponential type of a damped propagator on a superluminal causal
window is the self-dual Gaussian, modulated to a prescribed frequency and translated to a
prescribed centre.  Both operations are unitary, so the packet has the mass of the Gaussian, and
the modulus of the packet is the modulus of the translated Gaussian.

Consequently the window defect of the packet is a pure Gaussian tail: if the centre sits a distance
`m` from both endpoints of the window, the squared defect is at most `e^{-πm²}`.  On a window
`(0, κu)` with the centre at `cu`, `1 < c < κ`, this is `e^{-π(mu)²}` — far below every
`e^{-σu^q}`, `q < 1`, which is exactly the accounting a damped propagator needs.
-/

open MeasureTheory Filter Topology Complex GaloisForLFunctions.HTGeometry

open scoped FourierTransform

namespace RHTower

open RHTower.MellinL2

noncomputable section

/-! ## The window defect of an `L²` datum -/

theorem norm_sub_windowCutoff_sq {S : Set ℝ} (hS : MeasurableSet S)
    (f : Lp (α := ℝ) (μ := (volume : Measure ℝ)) ℂ 2) :
    ‖f - windowCutoff hS f‖ ^ (2 : ℕ) = ∫ x in Sᶜ, ‖(f : ℝ → ℂ) x‖ ^ (2 : ℕ) := by
  classical
  have hfun : (fun x => ‖((f - windowCutoff hS f : Lp (α := ℝ) ℂ 2) : ℝ → ℂ) x‖ ^ (2 : ℕ))
      =ᵐ[(volume : Measure ℝ)] Sᶜ.indicator (fun x => ‖(f : ℝ → ℂ) x‖ ^ (2 : ℕ)) := by
    filter_upwards [Lp.coeFn_sub f (windowCutoff hS f), windowCutoff_coeFn hS f] with x h1 h2
    rw [h1, Pi.sub_apply, h2]
    by_cases hmem : x ∈ S
    · rw [windowSymbol_eq_one hmem, one_mul, sub_self, norm_zero,
        Set.indicator_of_notMem (by simpa using hmem)]
      norm_num
    · rw [windowSymbol, Set.indicator_of_notMem hmem, zero_mul, sub_zero,
        Set.indicator_of_mem (by simpa using hmem)]
  rw [norm_lpTwo_sq (μ := (volume : Measure ℝ)), integral_congr_ae hfun,
    integral_indicator hS.compl]

/-! ## The packet -/

/-- The Gaussian causal packet: the self-dual Gaussian modulated to frequency `-R` and translated
so that its centre sits at `T`. -/
def gaussPacket (R T : ℝ) : Lp (α := ℝ) ℂ 2 :=
  additiveTranslationUnitary (-T) (fourierPhaseMulUnitary (-R) gaussLp)

@[simp] theorem norm_gaussPacket (R T : ℝ) : ‖gaussPacket R T‖ = ‖gaussLp‖ := by
  rw [gaussPacket, LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]

theorem norm_gaussLp_pos : 0 < ‖gaussLp‖ := by
  have hsq : ‖gaussLp‖ ^ (2 : ℕ) = Real.sqrt 2⁻¹ := norm_gaussLp_sq
  have hpos : (0 : ℝ) < Real.sqrt 2⁻¹ := Real.sqrt_pos.2 (by norm_num)
  rcases eq_or_lt_of_le (norm_nonneg gaussLp) with h | h
  · exfalso
    have hzero : (0 : ℝ) ^ (2 : ℕ) = Real.sqrt 2⁻¹ := by
      rw [h]
      exact hsq
    rw [pow_two, mul_zero] at hzero
    linarith [hpos, hzero]
  · exact h

theorem coeFn_gaussPacket_norm (R T : ℝ) :
    (fun x => ‖(gaussPacket R T : ℝ → ℂ) x‖)
      =ᵐ[(volume : Measure ℝ)] fun x => ‖(gaussLp : ℝ → ℂ) (x - T)‖ := by
  have htrans := translation_coeFn_massGaugeSuperluminalCompression (-T) (fourierPhaseMulUnitary (-R) gaussLp)
  have hphase := phaseMul_coeFn (-R) gaussLp
  have hphase' : ∀ᵐ x : ℝ,
      (fourierPhaseMulUnitary (-R) gaussLp : ℝ → ℂ) (x + -T)
        = fourierPhase (-R) (x + -T) * (gaussLp : ℝ → ℂ) (x + -T) := by
    have hshift := (MeasureTheory.measurePreserving_add_right (volume : Measure ℝ) (-T)).quasiMeasurePreserving
    exact hshift.ae hphase
  filter_upwards [htrans, hphase'] with x h1 h2
  rw [gaussPacket, h1, h2, norm_mul, norm_fourierPhase, one_mul]
  congr 2

/-! ## The window defect of the packet -/

theorem gaussPacket_window_defect_le {R T H : ℝ} (hT : 0 < T) (hTH : T < H) :
    ‖gaussPacket R T - windowCutoff (measurableSet_Ioo (a := (0 : ℝ)) (b := H))
        (gaussPacket R T)‖ ^ (2 : ℕ)
      ≤ Real.exp (-(Real.pi * (min T (H - T)) ^ (2 : ℕ))) := by
  classical
  set m : ℝ := min T (H - T) with hm
  have hm0 : 0 < m := lt_min hT (by linarith)
  rw [norm_sub_windowCutoff_sq]
  have hindic : ∫ x in (Set.Ioo (0 : ℝ) H)ᶜ, ‖(gaussPacket R T : ℝ → ℂ) x‖ ^ (2 : ℕ)
      = ∫ x : ℝ, (Set.Ioo (0 : ℝ) H)ᶜ.indicator
        (fun x => ‖(gaussPacket R T : ℝ → ℂ) x‖ ^ (2 : ℕ)) x :=
    (integral_indicator (measurableSet_Ioo.compl)).symm
  have hshift : ∫ x : ℝ, (Set.Ioo (0 : ℝ) H)ᶜ.indicator
        (fun x => ‖(gaussPacket R T : ℝ → ℂ) x‖ ^ (2 : ℕ)) x
      = ∫ x : ℝ, (Set.Ioo (0 : ℝ) H)ᶜ.indicator
        (fun x => ‖(gaussLp : ℝ → ℂ) (x - T)‖ ^ (2 : ℕ)) x := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_gaussPacket_norm R T] with x hx
    by_cases hmem : x ∈ (Set.Ioo (0 : ℝ) H)ᶜ
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hx]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
  have htranslate : ∫ x : ℝ, (Set.Ioo (0 : ℝ) H)ᶜ.indicator
        (fun x => ‖(gaussLp : ℝ → ℂ) (x - T)‖ ^ (2 : ℕ)) x
      = ∫ y : ℝ, (Set.Ioo (0 : ℝ) H)ᶜ.indicator
        (fun x => ‖(gaussLp : ℝ → ℂ) (x - T)‖ ^ (2 : ℕ)) (y + T) := by
    exact (integral_add_right_eq_self
      (fun x : ℝ => (Set.Ioo (0 : ℝ) H)ᶜ.indicator
        (fun x => ‖(gaussLp : ℝ → ℂ) (x - T)‖ ^ (2 : ℕ)) x) T).symm
  have hdom : ∀ y : ℝ, (Set.Ioo (0 : ℝ) H)ᶜ.indicator
      (fun x => ‖(gaussLp : ℝ → ℂ) (x - T)‖ ^ (2 : ℕ)) (y + T)
      ≤ {y : ℝ | m ≤ |y|}.indicator (fun y => ‖(gaussLp : ℝ → ℂ) y‖ ^ (2 : ℕ)) y := by
    intro y
    by_cases hmem : (y + T) ∈ (Set.Ioo (0 : ℝ) H)ᶜ
    · rw [Set.indicator_of_mem hmem]
      have hy : m ≤ |y| := by
        rw [Set.mem_compl_iff, Set.mem_Ioo] at hmem
        push Not at hmem
        rcases le_or_gt (y + T) 0 with h | h
        · have : y ≤ -T := by linarith
          have : T ≤ |y| := by
            rw [le_abs]
            right
            linarith
          exact le_trans (min_le_left _ _) this
        · have hH : H ≤ y + T := hmem (by linarith)
          have : H - T ≤ |y| := by
            rw [le_abs]
            left
            linarith
          exact le_trans (min_le_right _ _) this
      rw [Set.indicator_of_mem (by exact hy)]
      have hsimp : y + T - T = y := by ring
      rw [hsimp]
    · rw [Set.indicator_of_notMem hmem]
      exact Set.indicator_nonneg (fun _ _ => by positivity) y
  have hmeas : MeasurableSet {y : ℝ | m ≤ |y|} :=
    measurableSet_le measurable_const measurable_norm
  have hintdom : Integrable ({y : ℝ | m ≤ |y|}.indicator
      (fun y => ‖(gaussLp : ℝ → ℂ) y‖ ^ (2 : ℕ))) := by
    have hbase : Integrable (fun y : ℝ => ‖(gaussLp : ℝ → ℂ) y‖ ^ (2 : ℕ)) :=
      (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable gaussLp)).1 (Lp.memLp gaussLp)
    exact (hbase.indicator hmeas)
  have hbase : Integrable (fun y : ℝ => ‖(gaussLp : ℝ → ℂ) y‖ ^ (2 : ℕ)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable gaussLp)).1 (Lp.memLp gaussLp)
  have hFint : Integrable (fun x : ℝ => (Set.Ioo (0 : ℝ) H)ᶜ.indicator
      (fun x => ‖(gaussLp : ℝ → ℂ) (x - T)‖ ^ (2 : ℕ)) x) :=
    (hbase.comp_sub_right T).indicator measurableSet_Ioo.compl
  have hintsrc : Integrable (fun y : ℝ => (Set.Ioo (0 : ℝ) H)ᶜ.indicator
      (fun x => ‖(gaussLp : ℝ → ℂ) (x - T)‖ ^ (2 : ℕ)) (y + T)) := hFint.comp_add_right T
  rw [hindic, hshift, htranslate]
  refine le_trans (integral_mono hintsrc hintdom hdom) ?_
  rw [integral_indicator hmeas]
  exact gaussLp_tail_le hm0.le

/-! ## The frequency profile of the packet -/

theorem fourier_gaussLp : 𝓕 gaussLp = gaussLp :=
  GaloisForLFunctions.fourier_gaussianSchwartz_toLp

/-- The frequency profile of the Gaussian causal packet. -/
def fourierGaussPacket (R T : ℝ) : Lp (α := ℝ) (μ := (volume : Measure ℝ)) ℂ 2 :=
  𝓕 (gaussPacket R T)

theorem fourierGaussPacket_eq (R T : ℝ) :
    fourierGaussPacket R T
      = fourierPhaseMulUnitary (-T) (additiveTranslationUnitary R gaussLp) := by
  rw [fourierGaussPacket, gaussPacket, fourier_additiveTranslation,
    fourier_fourierPhaseMulUnitary, neg_neg, fourier_gaussLp]

theorem coeFn_fourierGaussPacket_norm (R T : ℝ) :
    (fun w => ‖(fourierGaussPacket R T : ℝ → ℂ) w‖)
      =ᵐ[(volume : Measure ℝ)] fun w => ‖(gaussLp : ℝ → ℂ) (w + R)‖ := by
  have hphase := phaseMul_coeFn (-T) (additiveTranslationUnitary R gaussLp)
  have htrans := translation_coeFn_massGaugeSuperluminalCompression R gaussLp
  filter_upwards [hphase, htrans] with w h1 h2
  rw [fourierGaussPacket_eq, h1, norm_mul, norm_fourierPhase, one_mul, h2]

/-- **The band defect of the packet.**  Outside a frequency band of radius `ρ` about `-R` the
squared mass of the packet is at most `e^{-πρ²}`. -/
theorem fourierGaussPacket_band_defect_le {R T rho : ℝ} (hrho : 0 ≤ rho) :
    ∫ w in {w : ℝ | rho ≤ |w + R|}, ‖(fourierGaussPacket R T : ℝ → ℂ) w‖ ^ (2 : ℕ)
      ≤ Real.exp (-(Real.pi * rho ^ (2 : ℕ))) := by
  classical
  have hmeasS : MeasurableSet {w : ℝ | rho ≤ |w + R|} :=
    measurableSet_le measurable_const ((measurable_id.add_const R).norm)
  have hmeasT : MeasurableSet {y : ℝ | rho ≤ |y|} :=
    measurableSet_le measurable_const measurable_norm
  have hcongr : ∫ w in {w : ℝ | rho ≤ |w + R|}, ‖(fourierGaussPacket R T : ℝ → ℂ) w‖ ^ (2 : ℕ)
      = ∫ w in {w : ℝ | rho ≤ |w + R|}, ‖(gaussLp : ℝ → ℂ) (w + R)‖ ^ (2 : ℕ) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae (coeFn_fourierGaussPacket_norm R T)] with w hw
    rw [hw]
  rw [hcongr]
  have hind : ∫ w in {w : ℝ | rho ≤ |w + R|}, ‖(gaussLp : ℝ → ℂ) (w + R)‖ ^ (2 : ℕ)
      = ∫ w : ℝ, {w : ℝ | rho ≤ |w + R|}.indicator
        (fun w => ‖(gaussLp : ℝ → ℂ) (w + R)‖ ^ (2 : ℕ)) w :=
    (integral_indicator hmeasS).symm
  have hfun : ∀ w : ℝ, {w : ℝ | rho ≤ |w + R|}.indicator
      (fun w => ‖(gaussLp : ℝ → ℂ) (w + R)‖ ^ (2 : ℕ)) w
      = ({y : ℝ | rho ≤ |y|}.indicator (fun y => ‖(gaussLp : ℝ → ℂ) y‖ ^ (2 : ℕ))) (w + R) := by
    intro w
    by_cases hmem : rho ≤ |w + R|
    · rw [Set.indicator_of_mem (by exact hmem), Set.indicator_of_mem (by exact hmem)]
    · rw [Set.indicator_of_notMem (by exact hmem), Set.indicator_of_notMem (by exact hmem)]
  have hshift : ∫ w : ℝ, {w : ℝ | rho ≤ |w + R|}.indicator
        (fun w => ‖(gaussLp : ℝ → ℂ) (w + R)‖ ^ (2 : ℕ)) w
      = ∫ y : ℝ, {y : ℝ | rho ≤ |y|}.indicator (fun y => ‖(gaussLp : ℝ → ℂ) y‖ ^ (2 : ℕ)) y := by
    rw [funext hfun]
    exact integral_add_right_eq_self
      ({y : ℝ | rho ≤ |y|}.indicator (fun y => ‖(gaussLp : ℝ → ℂ) y‖ ^ (2 : ℕ))) R
  rw [hind, hshift, integral_indicator hmeasT]
  exact gaussLp_tail_le hrho

/-! ## The Gaussian absorbs an exponential weight as a shift -/

theorem exp_weight_gauss (sigma y : ℝ) :
    Complex.exp (((2 * Real.pi * sigma * y : ℝ)) : ℂ) * Complex.exp (-(Real.pi * (y : ℂ) ^ (2 : ℕ)))
      = Complex.exp (((Real.pi * sigma ^ (2 : ℕ) : ℝ)) : ℂ)
        * Complex.exp (-(Real.pi * (((y - sigma : ℝ)) : ℂ) ^ (2 : ℕ))) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem coeFn_gaussLp_shift (R : ℝ) :
    (fun w : ℝ => (gaussLp : ℝ → ℂ) (w + R))
      =ᵐ[(volume : Measure ℝ)] fun w : ℝ => Complex.exp (-(Real.pi * (((w + R : ℝ)) : ℂ) ^ (2 : ℕ))) := by
  have hshift := (MeasureTheory.measurePreserving_add_right
    (volume : Measure ℝ) R).quasiMeasurePreserving
  exact hshift.ae coeFn_gaussLp

/-- **The exponentially weighted packet is the packet at a shifted frequency.** -/
theorem coeFn_expWeight_fourierGaussPacket (sigma R T : ℝ) :
    (fun w : ℝ => Complex.exp (((2 * Real.pi * sigma * (w + R) : ℝ)) : ℂ)
        * (fourierGaussPacket R T : ℝ → ℂ) w)
      =ᵐ[(volume : Measure ℝ)] fun w : ℝ => Complex.exp (((Real.pi * sigma ^ (2 : ℕ) : ℝ)) : ℂ)
        * (fourierGaussPacket (R - sigma) T : ℝ → ℂ) w := by
  have h1 := phaseMul_coeFn (-T) (additiveTranslationUnitary R gaussLp)
  have h2 := translation_coeFn_massGaugeSuperluminalCompression R gaussLp
  have h3 := phaseMul_coeFn (-T) (additiveTranslationUnitary (R - sigma) gaussLp)
  have h4 := translation_coeFn_massGaugeSuperluminalCompression (R - sigma) gaussLp
  have h5 := coeFn_gaussLp_shift R
  have h6 := coeFn_gaussLp_shift (R - sigma)
  filter_upwards [h1, h2, h3, h4, h5, h6] with w e1 e2 e3 e4 e5 e6
  rw [fourierGaussPacket_eq, fourierGaussPacket_eq, e1, e3, e2, e4, e5, e6]
  have hcast : ((w + R - sigma : ℝ) : ℂ) = ((w + (R - sigma) : ℝ) : ℂ) := by
    push_cast
    ring
  have hkey := exp_weight_gauss sigma (w + R)
  rw [hcast] at hkey
  calc Complex.exp (((2 * Real.pi * sigma * (w + R) : ℝ)) : ℂ)
        * (fourierPhase (-T) w * Complex.exp (-(Real.pi * (((w + R : ℝ)) : ℂ) ^ (2 : ℕ))))
      = fourierPhase (-T) w * (Complex.exp (((2 * Real.pi * sigma * (w + R) : ℝ)) : ℂ)
          * Complex.exp (-(Real.pi * (((w + R : ℝ)) : ℂ) ^ (2 : ℕ)))) := by ring
    _ = fourierPhase (-T) w * (Complex.exp (((Real.pi * sigma ^ (2 : ℕ) : ℝ)) : ℂ)
          * Complex.exp (-(Real.pi * (((w + (R - sigma) : ℝ)) : ℂ) ^ (2 : ℕ)))) := by
        rw [hkey]
    _ = Complex.exp (((Real.pi * sigma ^ (2 : ℕ) : ℝ)) : ℂ)
          * (fourierPhase (-T) w * Complex.exp (-(Real.pi * (((w + (R - sigma) : ℝ)) : ℂ) ^ (2 : ℕ)))) := by
        ring


/-! ## The comparison model on the band -/

theorem fourierPhase_eq_exp (a x : ℝ) :
    fourierPhase a x = Complex.exp (2 * Real.pi * (a * x) * Complex.I) := by
  rw [fourierPhase, Real.fourierChar_apply]
  push_cast
  ring_nf

theorem fourierPhase_add (a b x : ℝ) :
    fourierPhase a x * fourierPhase b x = fourierPhase (a + b) x := by
  rw [fourierPhase_eq_exp, fourierPhase_eq_exp, fourierPhase_eq_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The band comparison model: the band-centre symbol value times the plane wave `e^{(σ+iu)η}`,
`η = 2π(w + r/2π)`. -/
def dampedModelSymbol (a lambda sigma u r w : ℝ) : ℂ :=
  massGaugeDampedSymbol a lambda sigma u (-r)
    * Complex.exp (((sigma : ℂ) + (u : ℝ) * Complex.I)
      * (((2 * Real.pi * (w + r / (2 * Real.pi)) : ℝ)) : ℂ))

/-- The scalar the model produces on a Gaussian packet. -/
def dampedModelConst (a lambda sigma u r : ℝ) : ℂ :=
  massGaugeDampedSymbol a lambda sigma u (-r)
    * Complex.exp (((r * u : ℝ)) * Complex.I)
    * Complex.exp (((Real.pi * sigma ^ (2 : ℕ) : ℝ)) : ℂ)

theorem norm_dampedModelConst (a lambda sigma u r : ℝ) :
    ‖dampedModelConst a lambda sigma u r‖
      = ‖massGaugeDampedSymbol a lambda sigma u (-r)‖ * Real.exp (Real.pi * sigma ^ (2 : ℕ)) := by
  rw [dampedModelConst, norm_mul, norm_mul]
  have h1 : ‖Complex.exp (((r * u : ℝ)) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have h2 : ‖Complex.exp (((Real.pi * sigma ^ (2 : ℕ) : ℝ)) : ℂ)‖
      = Real.exp (Real.pi * sigma ^ (2 : ℕ)) := by
    rw [Complex.norm_exp, Complex.ofReal_re]
  rw [h1, h2, mul_one]

/-- **The model turns the packet into a shifted packet.**  The exponential band weight becomes a
frequency shift by `σ`, and the plane-wave phase becomes a translation by `u`. -/
theorem coeFn_dampedModel_mul_packet (a lambda sigma u r T : ℝ) (hr : r ≠ 0) :
    (fun w : ℝ => dampedModelSymbol a lambda sigma u r w
        * (fourierGaussPacket (r / (2 * Real.pi)) T : ℝ → ℂ) w)
      =ᵐ[(volume : Measure ℝ)] fun w : ℝ => dampedModelConst a lambda sigma u r
        * (fourierGaussPacket (r / (2 * Real.pi) - sigma) (T - u) : ℝ → ℂ) w := by
  set R : ℝ := r / (2 * Real.pi) with hR
  have hRr : 2 * Real.pi * R = r := by
    rw [hR]
    field_simp
  have hweight := coeFn_expWeight_fourierGaussPacket sigma R T
  have h1 := phaseMul_coeFn (-T) (additiveTranslationUnitary (R - sigma) gaussLp)
  have h2 := translation_coeFn_massGaugeSuperluminalCompression (R - sigma) gaussLp
  have h3 := phaseMul_coeFn (-(T - u)) (additiveTranslationUnitary (R - sigma) gaussLp)
  filter_upwards [hweight, h1, h2, h3] with w ew e1 e2 e3
  have hsplit : Complex.exp (((sigma : ℂ) + (u : ℝ) * Complex.I)
        * (((2 * Real.pi * (w + R) : ℝ)) : ℂ))
      = Complex.exp (((2 * Real.pi * sigma * (w + R) : ℝ)) : ℂ)
        * (fourierPhase u w * Complex.exp (((r * u : ℝ)) * Complex.I)) := by
    rw [fourierPhase_eq_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have hRc : ((2 : ℂ) * (Real.pi : ℂ) * (R : ℂ)) = (r : ℂ) := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hRr
    push_cast
    linear_combination ((u : ℂ) * Complex.I) * hRc
  calc dampedModelSymbol a lambda sigma u r w
        * (fourierGaussPacket R T : ℝ → ℂ) w
      = massGaugeDampedSymbol a lambda sigma u (-r)
          * (fourierPhase u w * Complex.exp (((r * u : ℝ)) * Complex.I))
          * (Complex.exp (((2 * Real.pi * sigma * (w + R) : ℝ)) : ℂ)
            * (fourierGaussPacket R T : ℝ → ℂ) w) := by
        rw [dampedModelSymbol, hsplit]
        ring
    _ = massGaugeDampedSymbol a lambda sigma u (-r)
          * (fourierPhase u w * Complex.exp (((r * u : ℝ)) * Complex.I))
          * (Complex.exp (((Real.pi * sigma ^ (2 : ℕ) : ℝ)) : ℂ)
            * (fourierGaussPacket (R - sigma) T : ℝ → ℂ) w) := by
        rw [ew]
    _ = dampedModelConst a lambda sigma u r
          * (fourierGaussPacket (R - sigma) (T - u) : ℝ → ℂ) w := by
        rw [dampedModelConst, fourierGaussPacket_eq, fourierGaussPacket_eq, e1, e3, e2]
        have hph : fourierPhase u w * fourierPhase (-T) w = fourierPhase (-(T - u)) w := by
          rw [fourierPhase_add]
          congr 1
          ring
        calc massGaugeDampedSymbol a lambda sigma u (-r)
              * (fourierPhase u w * Complex.exp (((r * u : ℝ)) * Complex.I))
              * (Complex.exp (((Real.pi * sigma ^ (2 : ℕ) : ℝ)) : ℂ)
                * (fourierPhase (-T) w * (gaussLp : ℝ → ℂ) (w + (R - sigma))))
            = massGaugeDampedSymbol a lambda sigma u (-r)
                * Complex.exp (((r * u : ℝ)) * Complex.I)
                * Complex.exp (((Real.pi * sigma ^ (2 : ℕ) : ℝ)) : ℂ)
                * ((fourierPhase u w * fourierPhase (-T) w)
                  * (gaussLp : ℝ → ℂ) (w + (R - sigma))) := by ring
          _ = massGaugeDampedSymbol a lambda sigma u (-r)
                * Complex.exp (((r * u : ℝ)) * Complex.I)
                * Complex.exp (((Real.pi * sigma ^ (2 : ℕ) : ℝ)) : ℂ)
                * (fourierPhase (-(T - u)) w * (gaussLp : ℝ → ℂ) (w + (R - sigma))) := by
              rw [hph]


end

end RHTower
