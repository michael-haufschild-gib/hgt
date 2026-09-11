import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekGammaMobiusCoordinateEndpoint
import GaloisForLFunctions.HTGeometry.FrullaniIntegral

/-!
# Actual weighted-translation representation of the arithmetic current

The complete half-density translation difference has a convergent Frullani
integral equal to the actual coefficient derivative. Every arithmetic atom is
retained, including its vanishing zero-index coefficient. Norm integrals justify
the full series exchange at each positive source coordinate. The original
atomwise global boundary remains explicit; signed joint admission is separate.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set Filter Topology
noncomputable section

/-- The original half-density transport, retaining its source-coordinate weight. -/
def pwGammaWeightedTranslation (h : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((Real.sqrt x / Real.sqrt (x+h) : ℝ) : ℂ)*f (x+h)

theorem pwGammaWeightedTranslation_zero (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    pwGammaWeightedTranslation 0 f x = f x := by
  simp [pwGammaWeightedTranslation, (Real.sqrt_pos.mpr hx).ne']

theorem pwGammaWeightedTranslation_add (f : ℝ → ℂ) {h k x : ℝ}
    (hh : 0 ≤ h) (_hk : 0 ≤ k) (hx : 0 < x) :
    pwGammaWeightedTranslation h (pwGammaWeightedTranslation k f) x =
      pwGammaWeightedTranslation (h+k) f x := by
  have hxh : Real.sqrt (x+h) ≠ 0 := (Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg hx hh)).ne'
  have hc : (Real.sqrt (x+h) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxh
  simp only [pwGammaWeightedTranslation, add_assoc, Complex.ofReal_div]
  field_simp [hc]

theorem pwGammaWeightedTranslation_ray_atom {n : ℕ} (hn : 0 < n) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) :
    pwGammaWeightedTranslation h (fun y => pwGammaRaySource ((n : ℝ)*y)) x =
      (Real.exp (-((n : ℝ)*h)) : ℂ)*pwGammaRaySource ((n : ℝ)*x) := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hxh : 0 < x+h := add_pos_of_pos_of_nonneg hx hh
  rw [pwGammaWeightedTranslation, pwGammaRaySource_eq (mul_pos hnr hxh),
    pwGammaRaySource_eq (mul_pos hnr hx)]
  have hs := (Real.sqrt_pos.mpr hxh).ne'
  rw [Real.sqrt_mul hnr.le, Real.sqrt_mul hnr.le,
    show -((n : ℝ)*(x+h)) = -((n : ℝ)*x) + -((n : ℝ)*h) by ring, Real.exp_add]
  push_cast
  have hc : (Real.sqrt (x+h) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  field_simp [hc]

private theorem pwGammaFrullani_global_atom_zero (z : ℂ) : pwGammaMobiusGlobalAtom z 0 = 0 := by
  funext x
  simp [pwGammaMobiusGlobalAtom]

theorem pwGammaWeightedTranslation_global_atom (z : ℂ) (n : ℕ) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) :
    pwGammaWeightedTranslation h (pwGammaMobiusGlobalAtom z n) x =
      (Real.exp (-((n : ℝ)*h)) : ℂ)*pwGammaMobiusGlobalAtom z n x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaFrullani_global_atom_zero, pwGammaWeightedTranslation]
  have hq := pwGammaWeightedTranslation_ray_atom hn hh hx
  change (((Real.sqrt x / Real.sqrt (x+h) : ℝ) : ℂ)*pwGammaRaySource ((n : ℝ)*(x+h))) = _ at hq
  simp only [pwGammaWeightedTranslation, pwGammaMobiusGlobalAtom]
  calc
    _ = (((moebius n : ℤ) : ℂ)*Complex.exp (-z*(Real.log (n : ℝ) : ℂ))) *
        (((Real.sqrt x / Real.sqrt (x+h) : ℝ) : ℂ)*pwGammaRaySource ((n : ℝ)*(x+h))) := by ring
    _ = _ := by rw [hq]; ring

/-- Original complete difference kernel; zero index is excluded from its separate admission. -/
def pwGammaFrullaniKernel (n : ℕ) (h : ℝ) : ℂ :=
  (Complex.exp (-((n : ℂ)*(h : ℂ)))-Complex.exp (-(h : ℂ)))/(h : ℂ)

theorem pwGammaFrullaniKernel_eq_real (n : ℕ) (h : ℝ) :
    pwGammaFrullaniKernel n h =
      (((Real.exp (-((n : ℝ)*h))-Real.exp (-h))/h : ℝ) : ℂ) := by
  simp only [pwGammaFrullaniKernel, Complex.ofReal_div, Complex.ofReal_sub,
    Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_natCast]

theorem pwGammaFrullaniKernel_integrable {n : ℕ} (hn : 0 < n) :
    IntegrableOn (pwGammaFrullaniKernel n) (Ioi 0) := by
  have hnC : (0 : ℝ) < (n : ℂ).re := by simpa using (show (0 : ℝ) < n by exact_mod_cast hn)
  have hh := GaloisForLFunctions.HTGeometry.integrableOn_frullani
    (a := (n : ℂ)) (b := 1) hnC (by simp)
  change IntegrableOn (fun h : ℝ => (Complex.exp (-((n : ℂ)*(h : ℂ)))-Complex.exp (-(h : ℂ)))/(h : ℂ)) (Ioi 0)
  simpa only [one_mul] using hh

theorem pwGammaFrullaniKernel_integral {n : ℕ} (hn : 0 < n) :
    (∫ h in Ioi (0 : ℝ), pwGammaFrullaniKernel n h) = -(Real.log (n : ℝ) : ℂ) := by
  have hnC : (0 : ℝ) < (n : ℂ).re := by simpa using (show (0 : ℝ) < n by exact_mod_cast hn)
  have hh := GaloisForLFunctions.HTGeometry.integral_frullani
    (a := (n : ℂ)) (b := 1) hnC (by simp)
  simpa only [one_mul, Complex.log_one, zero_sub, ← Complex.natCast_log, pwGammaFrullaniKernel] using hh

theorem pwGammaFrullaniKernel_norm_eq {n : ℕ} (hn : 0 < n) {h : ℝ} (hh : 0 < h) :
    ‖pwGammaFrullaniKernel n h‖ = -(pwGammaFrullaniKernel n h).re := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have he : Real.exp (-((n : ℝ)*h)) ≤ Real.exp (-h) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [pwGammaFrullaniKernel_eq_real, Complex.norm_real, Complex.ofReal_re,
    Real.norm_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr he) hh.le)]

theorem pwGammaFrullaniKernel_norm_integral {n : ℕ} (hn : 0 < n) :
    (∫ h in Ioi (0 : ℝ), ‖pwGammaFrullaniKernel n h‖) = Real.log (n : ℝ) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun h hh => pwGammaFrullaniKernel_norm_eq hn hh), integral_neg]
  have hre := integral_re (pwGammaFrullaniKernel_integrable hn)
  change (∫ h in Ioi (0 : ℝ), (pwGammaFrullaniKernel n h).re) =
    (∫ h in Ioi (0 : ℝ), pwGammaFrullaniKernel n h).re at hre
  rw [hre, pwGammaFrullaniKernel_integral hn, Complex.neg_re, Complex.ofReal_re, neg_neg]

/-- Actual Möbius atom in the nonlocal coordinate response. -/
def pwGammaMobiusFrullaniAtom (z : ℂ) (x : ℝ) (n : ℕ) (h : ℝ) : ℂ :=
  pwGammaFrullaniKernel n h*pwGammaMobiusGlobalAtom z n x

private theorem pwGammaMobiusFrullaniAtom_zero (z : ℂ) (x : ℝ) : pwGammaMobiusFrullaniAtom z x 0 = 0 := by
  funext h
  simp [pwGammaMobiusFrullaniAtom, pwGammaFrullani_global_atom_zero]

theorem pwGammaMobiusFrullaniAtom_integrable (z : ℂ) (x : ℝ) (n : ℕ) :
    IntegrableOn (pwGammaMobiusFrullaniAtom z x n) (Ioi 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pwGammaMobiusFrullaniAtom_zero]; exact integrable_zero ℝ ℂ _
  exact (pwGammaFrullaniKernel_integrable hn).mul_const _

theorem pwGammaMobiusFrullaniAtom_integral (z : ℂ) (x : ℝ) (n : ℕ) :
    (∫ h in Ioi (0 : ℝ), pwGammaMobiusFrullaniAtom z x n h) =
      pwGammaMobiusGlobalCurrentAtom z n x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusFrullaniAtom_zero, pwGammaMobiusGlobalCurrentAtom, pwGammaFrullani_global_atom_zero]
  simp only [pwGammaMobiusFrullaniAtom, integral_mul_const, pwGammaFrullaniKernel_integral hn,
    pwGammaMobiusGlobalCurrentAtom]

theorem pwGammaMobiusFrullaniAtom_norm_integral (z : ℂ) (x : ℝ) (n : ℕ) :
    (∫ h in Ioi (0 : ℝ), ‖pwGammaMobiusFrullaniAtom z x n h‖) =
      ‖pwGammaMobiusGlobalCurrentAtom z n x‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusFrullaniAtom_zero, pwGammaMobiusGlobalCurrentAtom, pwGammaFrullani_global_atom_zero]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simp only [pwGammaMobiusFrullaniAtom, norm_mul, integral_mul_const, pwGammaFrullaniKernel_norm_integral hn,
    pwGammaMobiusGlobalCurrentAtom, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg (Real.log_nonneg hn1)]

theorem pwGammaMobiusFrullaniAtom_norm_integrals_summable (z : ℂ) {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ∫ h in Ioi (0 : ℝ), ‖pwGammaMobiusFrullaniAtom z x n h‖) := by
  simp only [pwGammaMobiusFrullaniAtom_norm_integral]
  exact (pwGammaMobiusTiltCurrent_summable z hx).norm

theorem pwGammaMobiusFrullaniAtom_eq (z : ℂ) (n : ℕ) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) :
    pwGammaMobiusFrullaniAtom z x n h =
      (pwGammaWeightedTranslation h (pwGammaMobiusGlobalAtom z n) x-
        (Real.exp (-h) : ℂ)*pwGammaMobiusGlobalAtom z n x)/(h : ℂ) := by
  rw [pwGammaWeightedTranslation_global_atom z n hh hx, pwGammaMobiusFrullaniAtom,
    pwGammaFrullaniKernel_eq_real]
  push_cast
  ring

/-- The complete original-family response, before any series/integral exchange. -/
def pwGammaMobiusFrullaniResponse (z : ℂ) (x h : ℝ) : ℂ :=
  (pwGammaWeightedTranslation h (pwGammaMobiusTilt z) x-
    (Real.exp (-h) : ℂ)*pwGammaMobiusTilt z x)/(h : ℂ)

private theorem pwGammaMobiusTranslatedAtoms_summable (z : ℂ) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) :
    Summable (fun n => pwGammaWeightedTranslation h (pwGammaMobiusGlobalAtom z n) x) :=
  (pwGammaMobiusTilt_summable z (add_pos_of_pos_of_nonneg hx hh)).mul_left _

theorem pwGammaMobiusFrullaniAtom_summable (z : ℂ) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) :
    Summable (fun n => pwGammaMobiusFrullaniAtom z x n h) := by
  have h0 : Summable (fun n => (Real.exp (-h) : ℂ)*pwGammaMobiusGlobalAtom z n x) :=
    (pwGammaMobiusTilt_summable z hx).mul_left _
  have hs := ((pwGammaMobiusTranslatedAtoms_summable z hh hx).sub h0).mul_right (h : ℂ)⁻¹
  exact hs.congr (fun n => by rw [pwGammaMobiusFrullaniAtom_eq z n hh hx, div_eq_mul_inv])

theorem pwGammaMobiusFrullaniResponse_eq_tsum (z : ℂ) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) :
    pwGammaMobiusFrullaniResponse z x h = ∑' n, pwGammaMobiusFrullaniAtom z x n h := by
  have h1 := pwGammaMobiusTranslatedAtoms_summable z hh hx
  have h0 : Summable (fun n => (Real.exp (-h) : ℂ)*pwGammaMobiusGlobalAtom z n x) :=
    (pwGammaMobiusTilt_summable z hx).mul_left _
  calc
    _ = ((∑' n, pwGammaWeightedTranslation h (pwGammaMobiusGlobalAtom z n) x)-
        (∑' n, (Real.exp (-h) : ℂ)*pwGammaMobiusGlobalAtom z n x))/(h : ℂ) := by
      simp only [pwGammaMobiusFrullaniResponse, pwGammaWeightedTranslation,
        pwGammaMobiusTilt_eq_global_atoms, tsum_mul_left]
    _ = ∑' n, (pwGammaWeightedTranslation h (pwGammaMobiusGlobalAtom z n) x-
        (Real.exp (-h) : ℂ)*pwGammaMobiusGlobalAtom z n x)/(h : ℂ) := by
      rw [← h1.tsum_sub h0]
      simp only [div_eq_mul_inv, tsum_mul_right]
    _ = _ := tsum_congr (fun n => (pwGammaMobiusFrullaniAtom_eq z n hh hx).symm)

theorem pwGammaMobiusFrullaniResponse_integrable (z : ℂ) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (pwGammaMobiusFrullaniResponse z x) (Ioi 0) := by
  have hs := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (pwGammaMobiusFrullaniAtom_integrable z x) (pwGammaMobiusFrullaniAtom_norm_integrals_summable z hx)
  exact IntegrableOn.congr_fun hs (fun h hh => (pwGammaMobiusFrullaniResponse_eq_tsum z hh.le hx).symm)
    measurableSet_Ioi

/-- Actual nonlocal source identity, with all coefficients and the full integral retained. -/
theorem pwGammaMobiusFrullaniResponse_integral (z : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ h in Ioi (0 : ℝ), pwGammaMobiusFrullaniResponse z x h) = pwGammaMobiusTiltCurrent z x := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun h hh => pwGammaMobiusFrullaniResponse_eq_tsum z hh.le hx),
    ← integral_tsum_of_summable_integral_norm (pwGammaMobiusFrullaniAtom_integrable z x)
      (pwGammaMobiusFrullaniAtom_norm_integrals_summable z hx)]
  simp only [pwGammaMobiusFrullaniAtom_integral, pwGammaMobiusTiltCurrent_eq_global_atoms]

theorem pwGammaMobiusFrullaniResponse_integral_eq_deriv (z : ℂ) {x : ℝ} (hx : 0 < x) :
    (∫ h in Ioi (0 : ℝ), pwGammaMobiusFrullaniResponse z x h) =
      deriv (fun b : ℂ => pwGammaMobiusTilt b x) z := by
  rw [pwGammaMobiusFrullaniResponse_integral z hx, pwGammaMobiusTilt_deriv z hx]

theorem pwGammaMobiusFrullaniResponse_integral_zero {x : ℝ} (hx : 0 < x) :
    (∫ h in Ioi (0 : ℝ), pwGammaMobiusFrullaniResponse 0 x h) = pwGammaMobiusLogCurrent x := by
  rw [pwGammaMobiusFrullaniResponse_integral 0 hx, pwGammaMobiusTiltCurrent_zero]

/-- Exact atomwise global boundary; this is not a signed joint-admission assertion. -/
theorem pwGammaMobiusFrullaniAtom_iterated_absolute_admission (z : ℂ) :
    Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ∫ h in Ioi (0 : ℝ),
      ‖pwGammaMobiusFrullaniAtom z x n h‖) ↔ 0 < z.re := by
  simp only [pwGammaMobiusFrullaniAtom_norm_integral]
  exact pwGammaMobiusGlobalCurrentAtom_absolute_admission z

theorem pwGammaMobiusFrullaniResponse_iterated_integrable :
    IntegrableOn (fun x : ℝ => ∫ h in Ioi (0 : ℝ), pwGammaMobiusFrullaniResponse 0 x h) (Ioi 0) :=
  IntegrableOn.congr_fun pwGammaMobiusLogCurrent_integrable
    (fun _x hx => (pwGammaMobiusFrullaniResponse_integral_zero hx).symm) measurableSet_Ioi

theorem pwGammaMobiusFrullaniResponse_iterated_integral :
    (∫ x in Ioi (0 : ℝ), ∫ h in Ioi (0 : ℝ), pwGammaMobiusFrullaniResponse 0 x h) =
      (Real.Gamma (3/2) : ℂ) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => pwGammaMobiusFrullaniResponse_integral_zero hx),
    pwGammaMobiusLogCurrent_integral]

/-- Closed actual-family representation, retaining its exact absolute boundary and original mass. -/
theorem pwGammaMobiusFrullaniCurrent_closed :
    (∀ z : ℂ, ∀ x : ℝ, 0 < x →
      IntegrableOn (pwGammaMobiusFrullaniResponse z x) (Ioi 0) ∧
      (∫ h in Ioi (0 : ℝ), pwGammaMobiusFrullaniResponse z x h) = pwGammaMobiusTiltCurrent z x) ∧
    (∀ z : ℂ, Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ∫ h in Ioi (0 : ℝ),
      ‖pwGammaMobiusFrullaniAtom z x n h‖) ↔ 0 < z.re) ∧
    IntegrableOn (fun x : ℝ => ∫ h in Ioi (0 : ℝ), pwGammaMobiusFrullaniResponse 0 x h) (Ioi 0) ∧
    (∫ x in Ioi (0 : ℝ), ∫ h in Ioi (0 : ℝ), pwGammaMobiusFrullaniResponse 0 x h) =
      (Real.Gamma (3/2) : ℂ) :=
  ⟨fun z _x hx => ⟨pwGammaMobiusFrullaniResponse_integrable z hx, pwGammaMobiusFrullaniResponse_integral z hx⟩,
    pwGammaMobiusFrullaniAtom_iterated_absolute_admission,
    pwGammaMobiusFrullaniResponse_iterated_integrable, pwGammaMobiusFrullaniResponse_iterated_integral⟩

end
end RHTower
