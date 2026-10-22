import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekGammaForcingMeasureClassification

/-!
# Actual Möbius coordinate generator and weighted global admission

The complete coefficient family has coordinate derivative `M_z/(2*x) - M_(z-1)`.
A common summable majorant on each positive interval justifies differentiation
of the full series. The compensating ray weight preserves the exact absolute
atom-integral admission region `0 < z.re`, and its complete mass law is retained.
The signed endpoint coordinate identity is pointwise; this module does not
assert global admission of its shifted family or a spectral Ward balance.
-/

set_option backward.isDefEq.respectTransparency false
namespace RHTower
open ArithmeticFunction MeasureTheory Set Filter Topology
noncomputable section

private theorem pwGammaCoordinate_atom_zero (z : ℂ) : pwGammaMobiusGlobalAtom z 0 = 0 := by
  funext x
  simp [pwGammaMobiusGlobalAtom]

theorem pwGammaMobiusGlobalAtom_shift (z : ℂ) (n : ℕ) (x : ℝ) :
    pwGammaMobiusGlobalAtom (z-1) n x = (n : ℂ)*pwGammaMobiusGlobalAtom z n x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaMobiusGlobalAtom]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  unfold pwGammaMobiusGlobalAtom
  rw [show -(z-1)*(Real.log (n : ℝ) : ℂ) = -z*(Real.log (n : ℝ) : ℂ) + (Real.log (n : ℝ) : ℂ) by ring,
    Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hnr]
  push_cast
  ring

private theorem pwGammaRaySource_dilation_hasDerivAt {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) :
    HasDerivAt (fun y : ℝ => pwGammaRaySource ((n : ℝ)*y))
      (((1/(2*x) : ℝ) : ℂ)*pwGammaRaySource ((n : ℝ)*x) -
        (n : ℂ)*pwGammaRaySource ((n : ℝ)*x)) x := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hnx := mul_pos hnr hx
  have hq := (pwGammaConnectionForcing_hasDerivAt 0 (Real.log ((n : ℝ)*x))).differentiableAt.hasDerivAt
  rw [pwGammaSource_log_derivative_ray_eq hnx] at hq
  have hl : HasDerivAt (fun y : ℝ => Real.log ((n : ℝ)*y)) (1/x) x := by
    have h := (Real.hasDerivAt_log hnx.ne').comp x ((hasDerivAt_id x).const_mul (n : ℝ))
    exact h.congr_deriv (by field_simp)
  have hh := hq.scomp x hl
  change HasDerivAt (fun y : ℝ => pwGammaRaySource ((n : ℝ)*y)) _ x at hh
  refine hh.congr_deriv ?_
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_ofNat, Complex.ofReal_natCast]
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  field_simp

theorem pwGammaMobiusGlobalAtom_coordinate_hasDerivAt (z : ℂ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (pwGammaMobiusGlobalAtom z n)
      (((1/(2*x) : ℝ) : ℂ)*pwGammaMobiusGlobalAtom z n x - pwGammaMobiusGlobalAtom (z-1) n x) x := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pwGammaCoordinate_atom_zero, pwGammaCoordinate_atom_zero]
    simp
  have hh := (pwGammaRaySource_dilation_hasDerivAt hx hn).const_mul
    (((moebius n : ℤ) : ℂ)*Complex.exp (-z*(Real.log (n : ℝ) : ℂ)))
  change HasDerivAt (pwGammaMobiusGlobalAtom z n) _ x at hh
  refine hh.congr_deriv ?_
  rw [pwGammaMobiusGlobalAtom_shift]
  unfold pwGammaMobiusGlobalAtom
  ring

private theorem pwGammaCoordinate_coefficient_bound {z : ℂ} {N n : ℕ}
    (hz : ‖z‖ ≤ (N : ℝ)) (hn : 0 < n) :
    ‖((moebius n : ℤ) : ℂ)*Complex.exp (-z*(Real.log (n : ℝ) : ℂ))‖ ≤ (n : ℝ)^N := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hmu : ‖((moebius n : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast (show |moebius n| ≤ 1 from abs_moebius_le_one)
  have hre : -z.re ≤ (N : ℝ) :=
    (neg_le_abs z.re).trans ((Complex.abs_re_le_norm z).trans hz)
  have he : ‖Complex.exp (-z*(Real.log (n : ℝ) : ℂ))‖ ≤ (n : ℝ)^N := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero]
    calc
      _ ≤ Real.exp ((N : ℝ)*Real.log (n : ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hre (Real.log_nonneg hn1))
      _ = _ := by rw [Real.exp_nat_mul, Real.exp_log hnr]
  rw [norm_mul]
  simpa only [one_mul] using mul_le_mul hmu he (norm_nonneg _) zero_le_one

theorem pwGammaRaySource_interval_bound {a b y : ℝ} (ha : 0 < a)
    (hay : a ≤ y) (hyb : y ≤ b) {n : ℕ} (hn : 0 < n) :
    ‖pwGammaRaySource ((n : ℝ)*y)‖ ≤
      (Real.sqrt b / Real.sqrt a)*‖pwGammaRaySource ((n : ℝ)*a)‖ := by
  have hy : 0 < y := ha.trans_le hay
  have hb : 0 < b := hy.trans_le hyb
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [pwGammaRaySource_eq (mul_pos hnr hy), pwGammaRaySource_eq (mul_pos hnr ha),
    Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity), Real.sqrt_mul hnr.le, Real.sqrt_mul hnr.le]
  have he : Real.exp (-((n : ℝ)*y)) ≤ Real.exp (-((n : ℝ)*a)) := by gcongr
  calc
    _ ≤ Real.sqrt (n : ℝ)*Real.sqrt b * Real.exp (-((n : ℝ)*a)) := by gcongr
    _ = _ := by field_simp

theorem pwGammaMobiusGlobalAtom_interval_bound {z : ℂ} {N : ℕ}
    (hz : ‖z‖ ≤ (N : ℝ)) {a b y : ℝ} (ha : 0 < a) (hay : a ≤ y) (hyb : y ≤ b) (n : ℕ) :
    ‖pwGammaMobiusGlobalAtom z n y‖ ≤
      (Real.sqrt b / Real.sqrt a)*((n : ℝ)^N*‖pwGammaRaySource ((n : ℝ)*a)‖) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pwGammaCoordinate_atom_zero]
    simp only [Pi.zero_apply, norm_zero]
    positivity
  rw [pwGammaMobiusGlobalAtom, norm_mul]
  calc
    _ ≤ (n : ℝ)^N*((Real.sqrt b/Real.sqrt a)*‖pwGammaRaySource ((n : ℝ)*a)‖) :=
      mul_le_mul (pwGammaCoordinate_coefficient_bound hz hn)
        (pwGammaRaySource_interval_bound ha hay hyb hn) (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem pwGammaCoordinate_derivative_interval_bound {z : ℂ} {N : ℕ}
    (hz : ‖z‖ ≤ (N : ℝ)) (hz1 : ‖z-1‖ ≤ (N : ℝ)) {a b y : ℝ}
    (ha : 0 < a) (hay : a ≤ y) (hyb : y ≤ b) (n : ℕ) :
    ‖((1/(2*y) : ℝ) : ℂ)*pwGammaMobiusGlobalAtom z n y - pwGammaMobiusGlobalAtom (z-1) n y‖ ≤
      ((1/(2*a)+1)*(Real.sqrt b/Real.sqrt a))*
        ((n : ℝ)^N*‖pwGammaRaySource ((n : ℝ)*a)‖) := by
  have hy : 0 < y := ha.trans_le hay
  have hb : 0 < b := hy.trans_le hyb
  have hb0 := pwGammaMobiusGlobalAtom_interval_bound hz ha hay hyb n
  have hb1 := pwGammaMobiusGlobalAtom_interval_bound hz1 ha hay hyb n
  calc
    _ ≤ ‖((1/(2*y) : ℝ) : ℂ)*pwGammaMobiusGlobalAtom z n y‖ +
        ‖pwGammaMobiusGlobalAtom (z-1) n y‖ := norm_sub_le _ _
    _ = (1/(2*y))*‖pwGammaMobiusGlobalAtom z n y‖ + ‖pwGammaMobiusGlobalAtom (z-1) n y‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ ≤ (1/(2*a))*((Real.sqrt b/Real.sqrt a)*((n : ℝ)^N*‖pwGammaRaySource ((n : ℝ)*a)‖)) +
        ((Real.sqrt b/Real.sqrt a)*((n : ℝ)^N*‖pwGammaRaySource ((n : ℝ)*a)‖)) := by gcongr
    _ = _ := by ring

/-- The full source derivative retains the actual minus-one coefficient shift. -/
theorem pwGammaMobiusTilt_coordinate_hasDerivAt (z : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (pwGammaMobiusTilt z)
      (((1/(2*x) : ℝ) : ℂ)*pwGammaMobiusTilt z x - pwGammaMobiusTilt (z-1) x) x := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max ‖z‖ ‖z-1‖)
  have hz : ‖z‖ ≤ (N : ℝ) := (le_max_left _ _).trans hN.le
  have hz1 : ‖z-1‖ ≤ (N : ℝ) := (le_max_right _ _).trans hN.le
  let a : ℝ := x/2
  let b : ℝ := x+x/2
  have ha : 0 < a := by dsimp [a]; positivity
  have hxI : x ∈ Ioo a b := by dsimp [a,b]; constructor <;> linarith
  have hsum := (pwGammaRaySource_polynomial_moment_summable ha N).mul_left
    ((1/(2*a)+1)*(Real.sqrt b/Real.sqrt a))
  have hh := hasDerivAt_tsum_of_isPreconnected hsum isOpen_Ioo (convex_Ioo a b).isPreconnected
    (fun n y hy => pwGammaMobiusGlobalAtom_coordinate_hasDerivAt z n (ha.trans hy.1))
    (fun n y hy => pwGammaCoordinate_derivative_interval_bound hz hz1 ha hy.1.le hy.2.le n)
    hxI (pwGammaMobiusTilt_summable z hx) hxI
  change HasDerivAt (pwGammaMobiusTilt z) _ x at hh
  refine hh.congr_deriv ?_
  have h0 : Summable (fun n => pwGammaMobiusGlobalAtom z n x) := pwGammaMobiusTilt_summable z hx
  have h1 : Summable (fun n => pwGammaMobiusGlobalAtom (z-1) n x) := pwGammaMobiusTilt_summable (z-1) hx
  rw [((h0.mul_left ((1/(2*x) : ℝ) : ℂ)).tsum_sub h1), tsum_mul_left]
  rfl

theorem pwGammaMobiusTilt_coordinate_deriv (z : ℂ) {x : ℝ} (hx : 0 < x) :
    deriv (pwGammaMobiusTilt z) x =
      (((1/(2*x) : ℝ) : ℂ)*pwGammaMobiusTilt z x - pwGammaMobiusTilt (z-1) x) :=
  (pwGammaMobiusTilt_coordinate_hasDerivAt z hx).deriv

/-- Actual log-coordinate evolution; the forcing comes from the original coefficient family. -/
theorem pwGammaMobiusTilt_log_coordinate_hasDerivAt (z : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => pwGammaMobiusTilt z (Real.exp u))
      ((1/2 : ℂ)*pwGammaMobiusTilt z (Real.exp t) -
        (Real.exp t : ℂ)*pwGammaMobiusTilt (z-1) (Real.exp t)) t := by
  have hh := (pwGammaMobiusTilt_coordinate_hasDerivAt z (Real.exp_pos t)).scomp t (Real.hasDerivAt_exp t)
  change HasDerivAt (fun u : ℝ => pwGammaMobiusTilt z (Real.exp u)) _ t at hh
  refine hh.congr_deriv ?_
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  have he : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)
  field_simp

theorem pwGammaMobiusTilt_log_coordinate_deriv (z : ℂ) (t : ℝ) :
    deriv (fun u : ℝ => pwGammaMobiusTilt z (Real.exp u)) t =
      (1/2 : ℂ)*pwGammaMobiusTilt z (Real.exp t) -
        (Real.exp t : ℂ)*pwGammaMobiusTilt (z-1) (Real.exp t) :=
  (pwGammaMobiusTilt_log_coordinate_hasDerivAt z t).deriv

/-- The actual coordinate forcing keeps the compensating ray weight. -/
def pwGammaMobiusCoordinateShiftAtom (z : ℂ) (n : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ)*pwGammaMobiusGlobalAtom (z-1) n x

theorem pwGammaMobiusCoordinateShiftAtom_eq (z : ℂ) (n : ℕ) (x : ℝ) :
    pwGammaMobiusCoordinateShiftAtom z n x =
      (((moebius n : ℤ) : ℂ)*Complex.exp (-z*(Real.log (n : ℝ) : ℂ))) *
        ((((n : ℝ)*x : ℝ) : ℂ)*pwGammaRaySource ((n : ℝ)*x)) := by
  rw [pwGammaMobiusCoordinateShiftAtom, pwGammaMobiusGlobalAtom_shift, pwGammaMobiusGlobalAtom]
  push_cast
  ring

private theorem pwGammaCoordinate_shift_zero (z : ℂ) : pwGammaMobiusCoordinateShiftAtom z 0 = 0 := by
  funext x
  rw [pwGammaMobiusCoordinateShiftAtom_eq]
  simp

theorem pwGammaMobiusCoordinateShiftAtom_integrable (z : ℂ) (n : ℕ) :
    IntegrableOn (pwGammaMobiusCoordinateShiftAtom z n) (Ioi 0) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [pwGammaCoordinate_shift_zero]; exact integrable_zero ℝ ℂ _
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hh : IntegrableOn (fun x : ℝ => ((((n : ℝ)*x : ℝ) : ℂ)*pwGammaRaySource ((n : ℝ)*x))) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff (fun y : ℝ => (y : ℂ)*pwGammaRaySource y) 0 hnr).mpr
    simpa only [mul_zero] using pwGammaRaySource_mul_moment_integrable
  exact IntegrableOn.congr_fun (hh.const_mul _) (fun x _ => (pwGammaMobiusCoordinateShiftAtom_eq z n x).symm)
    measurableSet_Ioi

private theorem pwGammaCoordinate_first_norm_integral :
    (∫ x in Ioi (0 : ℝ), ‖(x : ℂ)*pwGammaRaySource x‖) = Real.Gamma (5/2) := by
  rw [← pwGammaRaySource_first_moment_integral]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.le]

private theorem pwGammaCoordinate_Gamma_step :
    Real.Gamma (5/2) = (3/2 : ℝ)*Real.Gamma (3/2) := by
  have h := Real.Gamma_add_one (s := 3/2) (by positivity)
  rwa [show (3/2 : ℝ)+1=5/2 by ring] at h

theorem pwGammaMobiusCoordinateShiftAtom_norm_integral (z : ℂ) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusCoordinateShiftAtom z n x‖) =
      (3/2 : ℝ)*(∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusGlobalAtom z n x‖) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaCoordinate_shift_zero, pwGammaCoordinate_atom_zero]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  simp_rw [pwGammaMobiusCoordinateShiftAtom_eq, pwGammaMobiusGlobalAtom, norm_mul, integral_const_mul]
  have hm : (∫ y in Ioi (0 : ℝ), ‖(y : ℂ)‖*‖pwGammaRaySource y‖) = Real.Gamma (5/2) := by
    simpa only [norm_mul] using pwGammaCoordinate_first_norm_integral
  rw [integral_comp_mul_left_Ioi (fun y : ℝ => ‖(y : ℂ)‖*‖pwGammaRaySource y‖) 0 hnr,
    integral_comp_mul_left_Ioi (fun y : ℝ => ‖pwGammaRaySource y‖) 0 hnr]
  simp only [mul_zero, smul_eq_mul, hm,
    pwGammaRaySource_norm_integral, pwGammaCoordinate_Gamma_step]
  ring

theorem pwGammaMobiusCoordinateShiftAtom_integral (z : ℂ) (n : ℕ) :
    (∫ x in Ioi (0 : ℝ), pwGammaMobiusCoordinateShiftAtom z n x) =
      (3/2 : ℂ)*(∫ x in Ioi (0 : ℝ), pwGammaMobiusGlobalAtom z n x) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [pwGammaCoordinate_shift_zero, pwGammaCoordinate_atom_zero]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  simp_rw [pwGammaMobiusCoordinateShiftAtom_eq, pwGammaMobiusGlobalAtom, integral_const_mul]
  rw [integral_comp_mul_left_Ioi (fun y : ℝ => (y : ℂ)*pwGammaRaySource y) 0 hnr,
    integral_comp_mul_left_Ioi pwGammaRaySource 0 hnr]
  simp only [mul_zero, pwGammaRaySource_mul_moment_integral, pwGammaRaySource_integral,
    pwGammaCoordinate_Gamma_step, Complex.real_smul]
  push_cast
  ring

/-- The ray weight exactly compensates the coefficient shift in the absolute admission boundary. -/
theorem pwGammaMobiusCoordinateShiftAtom_absolute_admission (z : ℂ) :
    Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusCoordinateShiftAtom z n x‖) ↔ 0 < z.re := by
  simp_rw [pwGammaMobiusCoordinateShiftAtom_norm_integral]
  rw [summable_mul_left_iff (show (3/2 : ℝ) ≠ 0 by positivity)]
  exact pwGammaMobiusGlobalAtom_absolute_admission z

theorem pwGammaMobiusTilt_weighted_shift_eq_tsum (z : ℂ) (x : ℝ) :
    (x : ℂ)*pwGammaMobiusTilt (z-1) x = ∑' n, pwGammaMobiusCoordinateShiftAtom z n x := by
  rw [pwGammaMobiusTilt_eq_global_atoms, ← tsum_mul_left]
  rfl

theorem pwGammaMobiusTilt_weighted_shift_integrable {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ)*pwGammaMobiusTilt (z-1) x) (Ioi 0) := by
  have hh := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (pwGammaMobiusCoordinateShiftAtom_integrable z) ((pwGammaMobiusCoordinateShiftAtom_absolute_admission z).mpr hz)
  exact IntegrableOn.congr_fun hh (fun x _ => (pwGammaMobiusTilt_weighted_shift_eq_tsum z x).symm) measurableSet_Ioi

theorem pwGammaMobiusTilt_weighted_shift_integral {z : ℂ} (hz : 0 < z.re) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)*pwGammaMobiusTilt (z-1) x) =
      (3/2 : ℂ)*(∫ x in Ioi (0 : ℝ), pwGammaMobiusTilt z x) := by
  simp_rw [pwGammaMobiusTilt_weighted_shift_eq_tsum]
  rw [← integral_tsum_of_summable_integral_norm (pwGammaMobiusCoordinateShiftAtom_integrable z)
    ((pwGammaMobiusCoordinateShiftAtom_absolute_admission z).mpr hz)]
  simp_rw [pwGammaMobiusCoordinateShiftAtom_integral]
  rw [tsum_mul_left, pwGammaMobiusTilt_integral_eq_tsum hz]

/-- The weighted coordinate generator is the complete shifted-source response. -/
theorem pwGammaMobiusTilt_weighted_coordinate_deriv (z : ℂ) {x : ℝ} (hx : 0 < x) :
    (x : ℂ)*deriv (pwGammaMobiusTilt z) x =
      (1/2 : ℂ)*pwGammaMobiusTilt z x - (x : ℂ)*pwGammaMobiusTilt (z-1) x := by
  rw [pwGammaMobiusTilt_coordinate_deriv z hx]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_ofNat]
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  field_simp

theorem pwGammaMobiusTilt_weighted_coordinate_integrable {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ)*deriv (pwGammaMobiusTilt z) x) (Ioi 0) := by
  have hh := ((pwGammaMobiusTilt_integrable hz).const_mul (1/2 : ℂ)).sub
    (pwGammaMobiusTilt_weighted_shift_integrable hz)
  exact IntegrableOn.congr_fun hh (fun x hx => (pwGammaMobiusTilt_weighted_coordinate_deriv z hx).symm)
    measurableSet_Ioi

theorem pwGammaMobiusTilt_weighted_coordinate_integral {z : ℂ} (hz : 0 < z.re) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ)*deriv (pwGammaMobiusTilt z) x) =
      -(∫ x in Ioi (0 : ℝ), pwGammaMobiusTilt z x) := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => pwGammaMobiusTilt_weighted_coordinate_deriv z hx)]
  rw [integral_sub ((pwGammaMobiusTilt_integrable hz).const_mul (1/2 : ℂ))
    (pwGammaMobiusTilt_weighted_shift_integrable hz), integral_const_mul,
    pwGammaMobiusTilt_weighted_shift_integral hz]
  ring

/-- At the signed endpoint the coordinate identity is pointwise; no global shifted admission is assumed. -/
theorem pwGammaMobiusPreimage_log_coordinate_hasDerivAt (t : ℝ) :
    HasDerivAt (fun u : ℝ => pwGammaMobiusPreimage (Real.exp u))
      ((1/2 : ℂ)*pwGammaMobiusPreimage (Real.exp t) -
        (Real.exp t : ℂ)*pwGammaMobiusTilt (-1) (Real.exp t)) t := by
  simpa only [pwGammaMobiusTilt_zero, zero_sub] using pwGammaMobiusTilt_log_coordinate_hasDerivAt 0 t

/-- Closed actual-family law: both distinct generators, exact weighted admission and its full mass law. -/
theorem pwGammaMobiusCoordinateGenerator_closed :
    (∀ z : ℂ, ∀ x : ℝ, 0 < x →
      HasDerivAt (fun b : ℂ => pwGammaMobiusTilt b x) (pwGammaMobiusTiltCurrent z x) z ∧
      HasDerivAt (pwGammaMobiusTilt z)
        (((1/(2*x) : ℝ) : ℂ)*pwGammaMobiusTilt z x-pwGammaMobiusTilt (z-1) x) x) ∧
    (∀ z : ℂ, ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => pwGammaMobiusTilt z (Real.exp u))
        ((1/2 : ℂ)*pwGammaMobiusTilt z (Real.exp t)-
          (Real.exp t : ℂ)*pwGammaMobiusTilt (z-1) (Real.exp t)) t) ∧
    (∀ z : ℂ, Summable (fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖pwGammaMobiusCoordinateShiftAtom z n x‖) ↔
      0 < z.re) ∧
    (∀ z : ℂ, 0 < z.re →
      IntegrableOn (fun x : ℝ => (x : ℂ)*pwGammaMobiusTilt (z-1) x) (Ioi 0) ∧
      IntegrableOn (fun x : ℝ => (x : ℂ)*deriv (pwGammaMobiusTilt z) x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), (x : ℂ)*pwGammaMobiusTilt (z-1) x) =
        (3/2 : ℂ)*(∫ x in Ioi (0 : ℝ), pwGammaMobiusTilt z x) ∧
      (∫ x in Ioi (0 : ℝ), (x : ℂ)*deriv (pwGammaMobiusTilt z) x) =
        -(∫ x in Ioi (0 : ℝ), pwGammaMobiusTilt z x)) :=
  ⟨fun z _x hx => ⟨pwGammaMobiusTilt_hasDerivAt z hx, pwGammaMobiusTilt_coordinate_hasDerivAt z hx⟩,
    pwGammaMobiusTilt_log_coordinate_hasDerivAt, pwGammaMobiusCoordinateShiftAtom_absolute_admission,
    fun _z hz => ⟨pwGammaMobiusTilt_weighted_shift_integrable hz,
      pwGammaMobiusTilt_weighted_coordinate_integrable hz, pwGammaMobiusTilt_weighted_shift_integral hz,
      pwGammaMobiusTilt_weighted_coordinate_integral hz⟩⟩

end
end RHTower
