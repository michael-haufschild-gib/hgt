import GaloisForLFunctions.RHTower.CriticalMellinBoundaryStieltjes
import GaloisForLFunctions.RHTower.PacketAutocorrelationExplicit
import GaloisForLFunctions.RHTower.XiMassCriticalPrimeCone
import GaloisForLFunctions.HTGeometry.RealDirichletSeries

/-!
# The infinite-aperture critical-Mellin current of a damped exponential packet

For a finite real damped-exponential core with all real parts at least `α > 1/2`, the
autocorrelation `C_y` decays like `e^{-α h}` while the completed critical error grows at most like
`e^{h/2}`.  The boundary term of the Stieltjes pairing therefore dies and the truncated current
converges, so the finite-aperture law passes to the aperture limit:

```text
lim_{a → ∞} ⟨C_y⟩_a = -∫_0^∞ E_crit(h) C_y'(h) dh.
```

Every prime and prime power has been absorbed into the single cumulative source `E_crit`.  No
prime number theorem remainder is used: the elementary square-root bound
`|E_crit(h)| ≤ 23 e^{h/2}` suffices because the packet damping is strictly stronger.
-/

namespace RHTower

open GaloisForLFunctions.HTGeometry MeasureTheory Set Complex Filter
open scoped BigOperators Topology

noncomputable section

variable {n : ℕ}

/-! ## The autocorrelation as a complex test function -/

theorem continuous_halfLineExpPacket (w q : Fin n → ℂ) :
    Continuous (halfLineExpPacket w q) := by
  unfold halfLineExpPacket
  fun_prop

theorem continuous_packetAutocorrelation {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re)
    (r : Fin n → ℝ) : Continuous (packetAutocorrelation w r) := by
  have hfun : packetAutocorrelation w r
      = fun t : ℝ => (1 / 2 : ℝ) * (halfLineExpPacket w (autocorrCoeff w r) t).re := by
    funext t
    have := packetAutocorrelation_eq hw r t
    linarith
  rw [hfun]
  exact continuous_const.mul
    (Complex.continuous_re.comp (continuous_halfLineExpPacket w (autocorrCoeff w r)))

/-- The autocorrelation of the core, as a test function for the Stieltjes pairing. -/
def autocorrTest (w : Fin n → ℂ) (r : Fin n → ℝ) (h : ℝ) : ℂ :=
  ((packetAutocorrelation w r h : ℝ) : ℂ)

/-- Its derivative. -/
def autocorrTestDeriv (w : Fin n → ℂ) (r : Fin n → ℝ) (h : ℝ) : ℂ :=
  ((packetAutocorrelationDeriv w r h : ℝ) : ℂ)

theorem hasDerivAt_autocorrTest {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    (h : ℝ) : HasDerivAt (autocorrTest w r) (autocorrTestDeriv w r h) h :=
  Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt h (hasDerivAt_packetAutocorrelation hw r h)

theorem continuous_autocorrTestDeriv (w : Fin n → ℂ) (r : Fin n → ℝ) :
    Continuous (autocorrTestDeriv w r) := by
  unfold autocorrTestDeriv packetAutocorrelationDeriv
  exact Complex.continuous_ofReal.comp
    (continuous_const.mul (Complex.continuous_re.comp (continuous_halfLineExpPacket _ _)))

/-! ## The exponential majorant -/

/-- The coefficient mass of the autocorrelation derivative packet. -/
def autocorrDerivBound (w : Fin n → ℂ) (r : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ k, ‖-(w k) * autocorrCoeff w r k‖

/-- The coefficient mass of the autocorrelation packet. -/
def autocorrBound (w : Fin n → ℂ) (r : Fin n → ℝ) : ℝ :=
  (1 / 2) * ∑ k, ‖autocorrCoeff w r k‖

theorem autocorrDerivBound_nonneg (w : Fin n → ℂ) (r : Fin n → ℝ) :
    0 ≤ autocorrDerivBound w r := by
  unfold autocorrDerivBound
  positivity

theorem autocorrBound_nonneg (w : Fin n → ℂ) (r : Fin n → ℝ) : 0 ≤ autocorrBound w r := by
  unfold autocorrBound
  positivity

theorem norm_autocorrTestDeriv_le {w : Fin n → ℂ} (r : Fin n → ℝ) {α : ℝ}
    (hα : ∀ k, α ≤ (w k).re) {h : ℝ} (hh : 0 ≤ h) :
    ‖autocorrTestDeriv w r h‖ ≤ autocorrDerivBound w r * Real.exp (-(α * h)) := by
  rw [autocorrTestDeriv, Complex.norm_real, Real.norm_eq_abs]
  simpa [autocorrDerivBound, mul_assoc] using abs_packetAutocorrelationDeriv_le r hα hh

theorem norm_autocorrTest_le {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) {α : ℝ}
    (hα : ∀ k, α ≤ (w k).re) {h : ℝ} (hh : 0 ≤ h) :
    ‖autocorrTest w r h‖ ≤ autocorrBound w r * Real.exp (-(α * h)) := by
  rw [autocorrTest, Complex.norm_real, Real.norm_eq_abs]
  simpa [autocorrBound, mul_assoc] using abs_packetAutocorrelation_le hw r hα hh

/-- The critical current is dominated by a strictly decaying exponential. -/
theorem norm_criticalCurrent_le {w : Fin n → ℂ} (r : Fin n → ℝ) {α : ℝ}
    (hα : ∀ k, α ≤ (w k).re) {h : ℝ} (hh : 0 ≤ h) :
    ‖(criticalMellinCompletedError h : ℂ) * autocorrTestDeriv w r h‖
      ≤ (23 * autocorrDerivBound w r) * Real.exp (-((α - 1 / 2) * h)) := by
  have hE : ‖(criticalMellinCompletedError h : ℂ)‖ ≤ 23 * Real.exp (h / 2) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact abs_criticalMellinCompletedError_le_sqrt hh
  have hD := norm_autocorrTestDeriv_le r hα hh
  have hEnn : (0 : ℝ) ≤ ‖(criticalMellinCompletedError h : ℂ)‖ := norm_nonneg _
  calc ‖(criticalMellinCompletedError h : ℂ) * autocorrTestDeriv w r h‖
      = ‖(criticalMellinCompletedError h : ℂ)‖ * ‖autocorrTestDeriv w r h‖ := norm_mul _ _
    _ ≤ (23 * Real.exp (h / 2)) * (autocorrDerivBound w r * Real.exp (-(α * h))) := by
        exact mul_le_mul hE hD (norm_nonneg _) (by positivity)
    _ = (23 * autocorrDerivBound w r) * Real.exp (-((α - 1 / 2) * h)) := by
        rw [show (-((α - 1 / 2) * h)) = h / 2 + -(α * h) from by ring, Real.exp_add]
        ring

/-! ## Integrability and the aperture limit -/

theorem measurable_criticalError : Measurable criticalMellinCompletedError := by
  have h : criticalMellinCompletedError
      = fun h : ℝ => 4 * Real.sinh (h / 2) - criticalMellinPrimeMass h :=
    funext criticalMellinCompletedError_eq_polar_sub_primeMass
  rw [h]
  exact (by fun_prop : Measurable fun h : ℝ => 4 * Real.sinh (h / 2)).sub
    criticalMellinPrimeMass_mono.measurable

/-- The critical current of the core. -/
def criticalCurrent (w : Fin n → ℂ) (r : Fin n → ℝ) (h : ℝ) : ℂ :=
  (criticalMellinCompletedError h : ℂ) * autocorrTestDeriv w r h

theorem measurable_criticalCurrent (w : Fin n → ℂ) (r : Fin n → ℝ) :
    Measurable (criticalCurrent w r) :=
  (Complex.measurable_ofReal.comp measurable_criticalError).mul
    (continuous_autocorrTestDeriv w r).measurable

theorem integrableOn_expMajorant {c T : ℝ} (hc : 0 < c) (A : ℝ) :
    IntegrableOn (fun h : ℝ => A * Real.exp (-(c * h))) (Ioi T) := by
  have hbase : IntegrableOn (fun h : ℝ => Real.exp ((-c) * h)) (Ioi T) :=
    integrableOn_exp_mul_Ioi (by linarith) T
  have : IntegrableOn (fun h : ℝ => A * Real.exp ((-c) * h)) (Ioi T) := hbase.const_mul A
  refine this.congr_fun (fun h _ => ?_) measurableSet_Ioi
  show A * Real.exp ((-c) * h) = A * Real.exp (-(c * h))
  rw [show (-c) * h = -(c * h) from by ring]

theorem integral_expMajorant {c T : ℝ} (hc : 0 < c) :
    (∫ h in Ioi T, Real.exp (-(c * h))) = Real.exp (-(c * T)) / c := by
  have h := integral_exp_mul_Ioi (a := -c) (by linarith) T
  have hfun : (fun h : ℝ => Real.exp (-(c * h))) = fun h : ℝ => Real.exp ((-c) * h) := by
    funext h
    rw [show (-c) * h = -(c * h) from by ring]
  rw [hfun, h, show (-c) * T = -(c * T) from by ring]
  field_simp

theorem integrableOn_criticalCurrent_Ioi {w : Fin n → ℂ} (r : Fin n → ℝ) {α : ℝ}
    (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (criticalCurrent w r) (Ioi T) := by
  have hc : 0 < α - 1 / 2 := by linarith
  refine (integrableOn_expMajorant hc (23 * autocorrDerivBound w r)).mono'
    ((measurable_criticalCurrent w r).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact norm_criticalCurrent_le r hα (le_trans hT (le_of_lt hh))

theorem norm_criticalCurrent_tail_le {w : Fin n → ℂ} (r : Fin n → ℝ) {α : ℝ}
    (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T) :
    ‖∫ h in Ioi T, criticalCurrent w r h‖
      ≤ (23 * autocorrDerivBound w r) * Real.exp (-((α - 1 / 2) * T)) / (α - 1 / 2) := by
  have hc : 0 < α - 1 / 2 := by linarith
  have hbound : ‖∫ h in Ioi T, criticalCurrent w r h‖
      ≤ ∫ h in Ioi T, (23 * autocorrDerivBound w r) * Real.exp (-((α - 1 / 2) * h)) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine MeasureTheory.setIntegral_mono_on
      (integrableOn_criticalCurrent_Ioi r hα hα2 hT).norm
      (integrableOn_expMajorant hc (23 * autocorrDerivBound w r)) measurableSet_Ioi ?_
    intro h hh
    exact norm_criticalCurrent_le r hα (le_trans hT (le_of_lt hh))
  have hval : (∫ h in Ioi T, (23 * autocorrDerivBound w r) * Real.exp (-((α - 1 / 2) * h)))
      = (23 * autocorrDerivBound w r) * (Real.exp (-((α - 1 / 2) * T)) / (α - 1 / 2)) := by
    rw [MeasureTheory.integral_const_mul, integral_expMajorant hc]
  rw [hval] at hbound
  calc ‖∫ h in Ioi T, criticalCurrent w r h‖
      ≤ (23 * autocorrDerivBound w r) * (Real.exp (-((α - 1 / 2) * T)) / (α - 1 / 2)) := hbound
    _ = (23 * autocorrDerivBound w r) * Real.exp (-((α - 1 / 2) * T)) / (α - 1 / 2) := by ring

theorem integral_Ioc_add_tail {w : Fin n → ℂ} (r : Fin n → ℝ) {α : ℝ}
    (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T) :
    (∫ h in Ioc (0 : ℝ) T, criticalCurrent w r h) + ∫ h in Ioi T, criticalCurrent w r h
      = ∫ h in Ioi (0 : ℝ), criticalCurrent w r h := by
  have hunion : Ioc (0 : ℝ) T ∪ Ioi T = Ioi (0 : ℝ) := Set.Ioc_union_Ioi_eq_Ioi hT
  have hdisj : Disjoint (Ioc (0 : ℝ) T) (Ioi T) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.mpr hx')
  have hint0 : IntegrableOn (criticalCurrent w r) (Ioi 0) :=
    integrableOn_criticalCurrent_Ioi r hα hα2 le_rfl
  have hintOc : IntegrableOn (criticalCurrent w r) (Ioc (0 : ℝ) T) :=
    hint0.mono_set (by rw [← hunion]; exact Set.subset_union_left)
  have hintIoi : IntegrableOn (criticalCurrent w r) (Ioi T) :=
    integrableOn_criticalCurrent_Ioi r hα hα2 hT
  rw [← hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hintOc hintIoi]


/-! ## The aperture limit -/

theorem criticalMellinStieltjesPairing_autocorrTest_eq {w : Fin n → ℂ}
    (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    criticalMellinStieltjesPairing a (autocorrTest w r)
      = (criticalMellinCompletedError (2 * a) : ℂ) * autocorrTest w r (2 * a)
        - ∫ h in Ioc (0 : ℝ) (2 * a), criticalCurrent w r h :=
  criticalMellinStieltjesPairing_boundary ha
    (fun x _ => hasDerivAt_autocorrTest hw r x)
    ((continuous_autocorrTestDeriv w r).intervalIntegrable 0 (2 * a))

theorem tendsto_expNegLinear {c : ℝ} (hc : 0 < c) (A : ℝ) :
    Tendsto (fun a : ℝ => A * Real.exp (-(c * a))) atTop (𝓝 0) := by
  have hlin : Tendsto (fun a : ℝ => -(c * a)) atTop atBot :=
    Filter.tendsto_neg_atTop_atBot.comp (Filter.Tendsto.const_mul_atTop hc Filter.tendsto_id)
  have hexp : Tendsto (fun a : ℝ => Real.exp (-(c * a))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hlin
  simpa using hexp.const_mul A

/-- **Equation `(7)`: the infinite-aperture Stieltjes boundary law.**  Every prime and prime power
is absorbed into the single cumulative critical source. -/
theorem tendsto_criticalMellinStieltjesPairing_autocorrTest {w : Fin n → ℂ}
    (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) {α : ℝ}
    (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 < α) :
    Tendsto (fun a : ℝ => criticalMellinStieltjesPairing a (autocorrTest w r)) atTop
      (𝓝 (-∫ h in Ioi (0 : ℝ), criticalCurrent w r h)) := by
  have hc : 0 < α - 1 / 2 := by linarith
  set c : ℝ := α - 1 / 2 with hcdef
  set K : ℝ := autocorrBound w r with hK
  set M : ℝ := autocorrDerivBound w r with hM
  set L : ℂ := -∫ h in Ioi (0 : ℝ), criticalCurrent w r h with hL
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_
    (tendsto_expNegLinear (c := 2 * c) (by linarith) (23 * K + 23 * M / c))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
  have h2a : (0 : ℝ) ≤ 2 * a := by linarith
  have hsplit := integral_Ioc_add_tail r hα hα2 h2a
  have hpair := criticalMellinStieltjesPairing_autocorrTest_eq hw r ha
  have hdiff : criticalMellinStieltjesPairing a (autocorrTest w r) - L
      = (criticalMellinCompletedError (2 * a) : ℂ) * autocorrTest w r (2 * a)
        + ∫ h in Ioi (2 * a), criticalCurrent w r h := by
    rw [hpair, hL, ← hsplit]
    ring
  rw [hdiff]
  have hE : ‖(criticalMellinCompletedError (2 * a) : ℂ)‖ ≤ 23 * Real.exp (a) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have := abs_criticalMellinCompletedError_le_sqrt h2a
    rw [show 2 * a / 2 = a from by ring] at this
    exact this
  have hC : ‖autocorrTest w r (2 * a)‖ ≤ K * Real.exp (-(α * (2 * a))) :=
    norm_autocorrTest_le hw r hα h2a
  have hbdry : ‖(criticalMellinCompletedError (2 * a) : ℂ) * autocorrTest w r (2 * a)‖
      ≤ (23 * K) * Real.exp (-((2 * c) * a)) := by
    calc ‖(criticalMellinCompletedError (2 * a) : ℂ) * autocorrTest w r (2 * a)‖
        = ‖(criticalMellinCompletedError (2 * a) : ℂ)‖ * ‖autocorrTest w r (2 * a)‖ :=
          norm_mul _ _
      _ ≤ (23 * Real.exp a) * (K * Real.exp (-(α * (2 * a)))) :=
          mul_le_mul hE hC (norm_nonneg _) (by positivity)
      _ = (23 * K) * Real.exp (-((2 * c) * a)) := by
          rw [show (-((2 * c) * a)) = a + -(α * (2 * a)) from by rw [hcdef]; ring, Real.exp_add]
          ring
  have htail : ‖∫ h in Ioi (2 * a), criticalCurrent w r h‖
      ≤ (23 * M / c) * Real.exp (-((2 * c) * a)) := by
    have h := norm_criticalCurrent_tail_le r hα hα2 h2a
    rw [show (-((α - 1 / 2) * (2 * a))) = -((2 * c) * a) from by rw [hcdef]; ring] at h
    calc ‖∫ h in Ioi (2 * a), criticalCurrent w r h‖
        ≤ (23 * M) * Real.exp (-((2 * c) * a)) / c := h
      _ = (23 * M / c) * Real.exp (-((2 * c) * a)) := by ring
  calc ‖(criticalMellinCompletedError (2 * a) : ℂ) * autocorrTest w r (2 * a)
        + ∫ h in Ioi (2 * a), criticalCurrent w r h‖
      ≤ ‖(criticalMellinCompletedError (2 * a) : ℂ) * autocorrTest w r (2 * a)‖
        + ‖∫ h in Ioi (2 * a), criticalCurrent w r h‖ := norm_add_le _ _
    _ ≤ (23 * K) * Real.exp (-((2 * c) * a)) + (23 * M / c) * Real.exp (-((2 * c) * a)) := by
        exact add_le_add hbdry htail
    _ = (23 * K + 23 * M / c) * Real.exp (-((2 * c) * a)) := by ring


/-! ## The literal infinite-aperture law -/

/-- The polar half of the infinite-aperture pairing. -/
def polarAutocorrCurrent (w : Fin n → ℂ) (r : Fin n → ℝ) : ℂ :=
  ∫ h in Ioi (0 : ℝ), autocorrTest w r h * (2 * Real.cosh (h / 2) : ℂ)

/-- The prime half of the infinite-aperture pairing. -/
def primeAutocorrCurrent (w : Fin n → ℂ) (r : Fin n → ℝ) : ℂ :=
  ∑' k : ℕ, (criticalMellinAtomWeight k : ℂ) * autocorrTest w r (Real.log k)

theorem two_cosh_nonneg (h : ℝ) : (0 : ℝ) ≤ 2 * Real.cosh (h / 2) := by
  rw [Real.cosh_eq]
  have h1 := Real.exp_pos (h / 2)
  have h2 := Real.exp_pos (-(h / 2))
  linarith

theorem two_cosh_le {h : ℝ} (hh : 0 ≤ h) :
    2 * Real.cosh (h / 2) ≤ 2 * Real.exp (h / 2) := by
  rw [Real.cosh_eq]
  have hle : Real.exp (-(h / 2)) ≤ Real.exp (h / 2) := by
    rw [Real.exp_le_exp]; linarith
  linarith

theorem norm_polarIntegrand_le {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) {α : ℝ}
    (hα : ∀ k, α ≤ (w k).re) {h : ℝ} (hh : 0 ≤ h) :
    ‖autocorrTest w r h * (2 * Real.cosh (h / 2) : ℂ)‖
      ≤ (2 * autocorrBound w r) * Real.exp (-((α - 1 / 2) * h)) := by
  have hcosh : ‖(2 * Real.cosh (h / 2) : ℂ)‖ ≤ 2 * Real.exp (h / 2) := by
    rw [show ((2 : ℂ) * (Real.cosh (h / 2) : ℂ)) = ((2 * Real.cosh (h / 2) : ℝ) : ℂ) from by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (two_cosh_nonneg h)]
    exact two_cosh_le hh
  calc ‖autocorrTest w r h * (2 * Real.cosh (h / 2) : ℂ)‖
      = ‖autocorrTest w r h‖ * ‖(2 * Real.cosh (h / 2) : ℂ)‖ := norm_mul _ _
    _ ≤ (autocorrBound w r * Real.exp (-(α * h))) * (2 * Real.exp (h / 2)) :=
        mul_le_mul (norm_autocorrTest_le hw r hα hh) hcosh (norm_nonneg _)
          (mul_nonneg (autocorrBound_nonneg w r) (Real.exp_pos _).le)
    _ = (2 * autocorrBound w r) * Real.exp (-((α - 1 / 2) * h)) := by
        rw [show (-((α - 1 / 2) * h)) = -(α * h) + h / 2 from by ring, Real.exp_add]
        ring

theorem integrableOn_polarIntegrand {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 < α) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun h : ℝ => autocorrTest w r h * (2 * Real.cosh (h / 2) : ℂ)) (Ioi T) := by
  have hc : 0 < α - 1 / 2 := by linarith
  have hmeas : Measurable (fun h : ℝ => autocorrTest w r h * (2 * Real.cosh (h / 2) : ℂ)) := by
    refine Measurable.mul ?_ (by fun_prop)
    exact Complex.measurable_ofReal.comp (continuous_packetAutocorrelation hw r).measurable
  refine (integrableOn_expMajorant hc (2 * autocorrBound w r)).mono'
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact norm_polarIntegrand_le hw r hα (le_trans hT (le_of_lt hh))

theorem tendsto_polarTruncation {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 < α) :
    Tendsto (fun a : ℝ =>
        ∫ h in Ioc (0 : ℝ) (2 * a), autocorrTest w r h * (2 * Real.cosh (h / 2) : ℂ))
      atTop (𝓝 (polarAutocorrCurrent w r)) := by
  have hc : 0 < α - 1 / 2 := by linarith
  set G : ℝ → ℂ := fun h => autocorrTest w r h * (2 * Real.cosh (h / 2) : ℂ) with hG
  rw [← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' ?_
    (tendsto_expNegLinear (c := 2 * (α - 1 / 2)) (by linarith)
      ((2 * autocorrBound w r) / (α - 1 / 2)))
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
  have h2a : (0 : ℝ) ≤ 2 * a := by linarith
  have hint0 : IntegrableOn G (Ioi 0) := integrableOn_polarIntegrand hw r hα hα2 le_rfl
  have hintIoi : IntegrableOn G (Ioi (2 * a)) := integrableOn_polarIntegrand hw r hα hα2 h2a
  have hunion : Ioc (0 : ℝ) (2 * a) ∪ Ioi (2 * a) = Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi h2a
  have hdisj : Disjoint (Ioc (0 : ℝ) (2 * a)) (Ioi (2 * a)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.mpr hx')
  have hintOc : IntegrableOn G (Ioc (0 : ℝ) (2 * a)) :=
    hint0.mono_set (by rw [← hunion]; exact Set.subset_union_left)
  have hsplit : (∫ h in Ioc (0 : ℝ) (2 * a), G h) + ∫ h in Ioi (2 * a), G h
      = ∫ h in Ioi (0 : ℝ), G h := by
    rw [← hunion, MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hintOc hintIoi]
  have hdiff : (∫ h in Ioc (0 : ℝ) (2 * a), G h) - polarAutocorrCurrent w r
      = -∫ h in Ioi (2 * a), G h := by
    rw [polarAutocorrCurrent, ← hsplit]
    ring
  rw [hdiff, norm_neg]
  have hbound : ‖∫ h in Ioi (2 * a), G h‖
      ≤ ∫ h in Ioi (2 * a), (2 * autocorrBound w r) * Real.exp (-((α - 1 / 2) * h)) := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    refine MeasureTheory.setIntegral_mono_on hintIoi.norm
      (integrableOn_expMajorant hc (2 * autocorrBound w r)) measurableSet_Ioi ?_
    intro h hh
    exact norm_polarIntegrand_le hw r hα (le_trans h2a (le_of_lt hh))
  rw [MeasureTheory.integral_const_mul, integral_expMajorant hc,
    show (-((α - 1 / 2) * (2 * a))) = -((2 * (α - 1 / 2)) * a) from by ring] at hbound
  calc ‖∫ h in Ioi (2 * a), G h‖
      ≤ (2 * autocorrBound w r) * (Real.exp (-((2 * (α - 1 / 2)) * a)) / (α - 1 / 2)) := hbound
    _ = ((2 * autocorrBound w r) / (α - 1 / 2)) * Real.exp (-((2 * (α - 1 / 2)) * a)) := by ring


theorem criticalMellinAtomWeight_zero : criticalMellinAtomWeight 0 = 0 := by
  simp [criticalMellinAtomWeight]

theorem criticalMellinAtomWeight_one : criticalMellinAtomWeight 1 = 0 := by
  simp [criticalMellinAtomWeight]

theorem norm_primeTerm_le {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ) {α : ℝ}
    (hα : ∀ k, α ≤ (w k).re) (k : ℕ) :
    ‖(criticalMellinAtomWeight k : ℂ) * autocorrTest w r (Real.log k)‖
      ≤ autocorrBound w r *
        (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1 / 2 + α))) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp [criticalMellinAtomWeight_zero]
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hkpos
  have hlog : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hkpos)
  have hwt : |criticalMellinAtomWeight k| = criticalMellinAtomWeight k :=
    abs_of_nonneg (by
      refine mul_nonneg (Real.rpow_nonneg hkR.le _) ?_
      exact ArithmeticFunction.vonMangoldt_nonneg)
  have hexp : Real.exp (-(α * Real.log k)) = (k : ℝ) ^ (-α) := by
    rw [Real.rpow_def_of_pos hkR]
    congr 1
    ring
  have hsplit : (k : ℝ) ^ (-1 / 2 : ℝ) * (k : ℝ) ^ (-α) = (k : ℝ) ^ (-(1 / 2 + α)) := by
    rw [← Real.rpow_add hkR]
    congr 1
    ring
  calc ‖(criticalMellinAtomWeight k : ℂ) * autocorrTest w r (Real.log k)‖
      = criticalMellinAtomWeight k * ‖autocorrTest w r (Real.log k)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hwt]
    _ ≤ criticalMellinAtomWeight k * (autocorrBound w r * Real.exp (-(α * Real.log k))) := by
        refine mul_le_mul_of_nonneg_left (norm_autocorrTest_le hw r hα hlog) ?_
        rw [← hwt]
        exact abs_nonneg _
    _ = autocorrBound w r *
          (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1 / 2 + α))) := by
        rw [hexp, criticalMellinAtomWeight, ← hsplit]
        ring

theorem summable_primeAutocorr {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 < α) :
    Summable (fun k : ℕ =>
      (criticalMellinAtomWeight k : ℂ) * autocorrTest w r (Real.log k)) := by
  have hmaj : Summable (fun k : ℕ => autocorrBound w r *
      (ArithmeticFunction.vonMangoldt k * (k : ℝ) ^ (-(1 / 2 + α)))) :=
    (GaloisForLFunctions.HTGeometry.summable_vonMangoldt_rpow
      (σ := 1 / 2 + α) (by linarith)).mul_left _
  exact Summable.of_norm_bounded hmaj (fun k => norm_primeTerm_le hw r hα k)

theorem sum_Icc_eq_sum_range {w : Fin n → ℂ} (r : Fin n → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.Icc 2 N, (criticalMellinAtomWeight k : ℂ) * autocorrTest w r (Real.log k))
      = ∑ k ∈ Finset.range (N + 1),
          (criticalMellinAtomWeight k : ℂ) * autocorrTest w r (Real.log k) := by
  refine Finset.sum_subset ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro k hk hnot
    simp only [Finset.mem_range] at hk
    simp only [Finset.mem_Icc, not_and, not_le] at hnot
    have hk2 : k < 2 := by
      by_contra hc
      exact absurd (hnot (by omega)) (by omega)
    interval_cases k
    · simp [criticalMellinAtomWeight_zero]
    · simp [criticalMellinAtomWeight_one]

theorem tendsto_floorExp_atTop :
    Tendsto (fun a : ℝ => ⌊Real.exp (2 * a)⌋₊ + 1) atTop atTop := by
  have h2 : Tendsto (fun a : ℝ => 2 * a) atTop atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num) Filter.tendsto_id
  have hexp : Tendsto (fun a : ℝ => Real.exp (2 * a)) atTop atTop :=
    Real.tendsto_exp_atTop.comp h2
  have hfloor : Tendsto (fun a : ℝ => ⌊Real.exp (2 * a)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hexp
  exact tendsto_atTop_mono (fun a => Nat.le_succ _) hfloor

theorem tendsto_primeTruncation {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 < α) :
    Tendsto (fun a : ℝ => ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
        (criticalMellinAtomWeight k : ℂ) * autocorrTest w r (Real.log k))
      atTop (𝓝 (primeAutocorrCurrent w r)) := by
  have hsum := summable_primeAutocorr hw r hα hα2
  have hnat := hsum.hasSum.tendsto_sum_nat
  have hcomp := hnat.comp tendsto_floorExp_atTop
  refine hcomp.congr fun a => ?_
  exact (sum_Icc_eq_sum_range r _).symm

/-- **Equation `(7)`, literal form.**  The complete infinite-aperture polar minus prime pairing of
the packet autocorrelation is the single cumulative critical current. -/
theorem polar_sub_prime_autocorrCurrent {w : Fin n → ℂ} (hw : ∀ j, 0 < (w j).re) (r : Fin n → ℝ)
    {α : ℝ} (hα : ∀ k, α ≤ (w k).re) (hα2 : 1 / 2 < α) :
    polarAutocorrCurrent w r - primeAutocorrCurrent w r
      = -∫ h in Ioi (0 : ℝ), criticalCurrent w r h := by
  have hlim := tendsto_criticalMellinStieltjesPairing_autocorrTest hw r hα hα2
  have hsplit : (fun a : ℝ => criticalMellinStieltjesPairing a (autocorrTest w r))
      = fun a : ℝ =>
        (∫ h in Ioc (0 : ℝ) (2 * a), autocorrTest w r h * (2 * Real.cosh (h / 2) : ℂ))
          - ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
              (criticalMellinAtomWeight k : ℂ) * autocorrTest w r (Real.log k) := rfl
  rw [hsplit] at hlim
  have hlim2 := (tendsto_polarTruncation hw r hα hα2).sub (tendsto_primeTruncation hw r hα hα2)
  exact tendsto_nhds_unique hlim2 hlim


end

end RHTower
