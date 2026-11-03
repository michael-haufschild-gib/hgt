import GaloisForLFunctions.RHTower.SelbergCuspSpectrumRadius

/-!
# The ordinary exponential series of Selberg coefficients

Polynomial coefficient growth gives a holomorphic series on the right
half-plane. Its frequencies are integers, hence its period is `2πi`.
-/

noncomputable section
open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.SelbergClass

def ordinaryExponentialTerm (F : ExtendedSelbergClass) (z : ℂ) (n : ℕ) : ℂ :=
  F.coeff n * Complex.exp (-(n : ℂ) * z)

def ordinaryExponentialSeries (F : ExtendedSelbergClass) (z : ℂ) : ℂ :=
  ∑' n : ℕ, ordinaryExponentialTerm F z n

private def ordinaryThetaCoordinate (z : ℂ) : ℂ :=
  I * z / ((2 * Real.pi : ℝ) : ℂ)

private theorem ordinaryThetaCoordinate_im (z : ℂ) :
    (ordinaryThetaCoordinate z).im = z.re / (2 * Real.pi) := by
  simp [ordinaryThetaCoordinate, Complex.div_ofReal_im]

private theorem ordinaryExponentialTerm_eq_theta (F : ExtendedSelbergClass) (z : ℂ) (n : ℕ) :
    ordinaryExponentialTerm F z n = thetaTerm F.coeff 1 0 (ordinaryThetaCoordinate z) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [ordinaryExponentialTerm]
  · rw [thetaTerm, if_neg hn.ne']
    simp only [neg_zero, Complex.cpow_zero, mul_one, one_div_one, Real.rpow_one]
    change F.coeff n * Complex.exp (-(n : ℂ) * z) = _
    congr 1
    congr 1
    unfold ordinaryThetaCoordinate
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring

private theorem ordinaryExponentialSeries_eq_theta (F : ExtendedSelbergClass) (z : ℂ) :
    ordinaryExponentialSeries F z = thetaSeries F.coeff 1 0 (ordinaryThetaCoordinate z) :=
  tsum_congr (ordinaryExponentialTerm_eq_theta F z)

theorem summable_ordinaryExponentialTerm (F : ExtendedSelbergClass) {z : ℂ} (hz : 0 < z.re) :
    Summable (ordinaryExponentialTerm F z) := by
  obtain ⟨C, hC⟩ := F.exists_coeff_bound
  have hz' : 0 < (ordinaryThetaCoordinate z).im := by
    rw [ordinaryThetaCoordinate_im]
    exact div_pos hz (by positivity)
  exact (summable_thetaTerm_of_im_pos hC (by norm_num : (0 : ℝ) < 1) 0
    (ordinaryThetaCoordinate z) hz').congr fun n => (ordinaryExponentialTerm_eq_theta F z n).symm

/-- The ordinary exponential series is holomorphic throughout the right half-plane. -/
theorem analyticOnNhd_ordinaryExponentialSeries (F : ExtendedSelbergClass) :
    AnalyticOnNhd ℂ (ordinaryExponentialSeries F) {z : ℂ | 0 < z.re} := by
  obtain ⟨C, hC⟩ := F.exists_coeff_bound
  have heq : ordinaryExponentialSeries F =
      fun z => thetaSeries F.coeff 1 0 (ordinaryThetaCoordinate z) :=
    funext (ordinaryExponentialSeries_eq_theta F)
  rw [heq]
  intro z hz
  have hz' : 0 < (ordinaryThetaCoordinate z).im := by
    rw [ordinaryThetaCoordinate_im]
    exact div_pos hz (by positivity)
  exact AnalyticAt.comp (g := fun w => thetaSeries F.coeff 1 0 w)
    (f := ordinaryThetaCoordinate) (x := z)
    (analyticAt_thetaSeries hC (by norm_num : (0 : ℝ) < 1) 0 (ordinaryThetaCoordinate z) hz')
    (by unfold ordinaryThetaCoordinate; fun_prop)

/-- Integer frequencies give the exact imaginary period, including for the
totalized sum outside its initial convergence half-plane. -/
theorem ordinaryExponentialSeries_periodic (F : ExtendedSelbergClass) :
    Function.Periodic (ordinaryExponentialSeries F) (2 * (Real.pi : ℂ) * I) := by
  intro z
  apply tsum_congr
  intro n
  rw [ordinaryExponentialTerm, ordinaryExponentialTerm,
    show -(n : ℂ) * (z + 2 * (Real.pi : ℂ) * I) =
      -(n : ℂ) * z + (n : ℂ) * (-(2 * (Real.pi : ℂ) * I)) by ring,
    Complex.exp_add, Complex.exp_nat_mul, Complex.exp_neg, Complex.exp_two_pi_mul_I,
    inv_one, one_pow, mul_one]

end GaloisForLFunctions.SelbergClass
