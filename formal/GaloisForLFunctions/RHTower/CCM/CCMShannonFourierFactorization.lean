import GaloisForLFunctions.RHTower.CCM.CCMCompactFourierMeanSquareZeroTransfer

/-!
# Shannon factorization of a band-limited Fourier transform

A trigonometric polynomial with integer modes `-N, …, N`, restricted to one period `[0, 2π]` and
extended by zero, has the entire Fourier transform

`F(z) = ((e^{2πiz} − 1)/i) · ∑_j ξ_j /(z + j)`.

The prefactor vanishes exactly on the integers, hence only at real points.  Off the real axis the
zeros of `F` are therefore exactly the zeros of the first-order Fourier resolvent
`∑_j ξ_j/(z + j)`, which for an odd coefficient vector is the negative of `∑_j ξ_j/(z − j)`.

This is the bridge from the finite-matrix resolvent to the actual Fourier transform.
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-! ## The band-limited trigonometric polynomial -/

/-- The symmetric window of integer modes `{-N, …, N}`. -/
def ccmModeWindow (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)

theorem neg_mem_ccmModeWindow {N : ℕ} {j : ℤ} (hj : j ∈ ccmModeWindow N) :
    -j ∈ ccmModeWindow N := by
  rw [ccmModeWindow, Finset.mem_Icc] at hj ⊢
  omega

/-- The trigonometric polynomial with coefficient vector `ξ`. -/
def ccmTrigPoly (N : ℕ) (xi : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ j ∈ ccmModeWindow N, xi j * Complex.exp (Complex.I * ((j : ℂ) * (x : ℂ)))

theorem continuous_ccmTrigPoly (N : ℕ) (xi : ℤ → ℂ) : Continuous (ccmTrigPoly N xi) := by
  refine continuous_finsetSum _ fun j _ => ?_
  fun_prop

/-! ## Splitting the symmetric mode window -/

theorem ccmModeWindow_succ (N : ℕ) :
    ccmModeWindow (N + 1)
      = insert ((N : ℤ) + 1) (insert (-((N : ℤ) + 1)) (ccmModeWindow N)) := by
  ext j
  simp only [ccmModeWindow, Finset.mem_Icc, Finset.mem_insert, Nat.cast_add, Nat.cast_one]
  omega

theorem sum_ccmModeWindow_eq {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℤ → M) :
    ∑ j ∈ ccmModeWindow N, f j
      = f 0 + ∑ k ∈ Finset.range N, (f ((k : ℤ) + 1) + f (-((k : ℤ) + 1))) := by
  induction N with
  | zero => simp [ccmModeWindow]
  | succ N ih =>
    have hmemNeg : -((N : ℤ) + 1) ∉ ccmModeWindow N := by
      simp only [ccmModeWindow, Finset.mem_Icc]
      omega
    have hmemPos : ((N : ℤ) + 1) ∉ insert (-((N : ℤ) + 1)) (ccmModeWindow N) := by
      simp only [ccmModeWindow, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [ccmModeWindow_succ, Finset.sum_insert hmemPos, Finset.sum_insert hmemNeg, ih,
      Finset.sum_range_succ]
    abel

/-! ## The period factor -/

/-- The Shannon period factor `(e^{2πiz} − 1)/i`. -/
def ccmPeriodFactor (z : ℂ) : ℂ :=
  (Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z) - 1) / Complex.I

theorem re_two_pi_I_mul (z : ℂ) :
    (2 * (Real.pi : ℂ) * Complex.I * z).re = -(2 * Real.pi * z.im) := by
  simp [Complex.mul_re, Complex.mul_im]

/-- The period factor vanishes only at real frequencies. -/
theorem ccmPeriodFactor_ne_zero {z : ℂ} (hz : z.im ≠ 0) : ccmPeriodFactor z ≠ 0 := by
  rw [ccmPeriodFactor, div_ne_zero_iff]
  refine ⟨fun hcon => ?_, Complex.I_ne_zero⟩
  have hone : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z) = 1 := by
    rwa [sub_eq_zero] at hcon
  have hnorm : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z)‖ = 1 := by
    rw [hone, norm_one]
  rw [Complex.norm_exp, re_two_pi_I_mul, Real.exp_eq_one_iff] at hnorm
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  exact hz (by nlinarith)

/-! ## The Shannon factorization -/

theorem compactFourier_ccmTrigPoly (N : ℕ) (xi : ℤ → ℂ) {z : ℂ}
    (hz : ∀ j ∈ ccmModeWindow N, z + (j : ℂ) ≠ 0) :
    compactFourier (ccmTrigPoly N xi) 0 (2 * Real.pi) z
      = ccmPeriodFactor z * ∑ j ∈ ccmModeWindow N, xi j / (z + (j : ℂ)) := by
  have hstep : ∀ j ∈ ccmModeWindow N,
      (∫ x in (0 : ℝ)..(2 * Real.pi),
          xi j * Complex.exp (Complex.I * (z + (j : ℂ)) * (x : ℂ)))
        = ccmPeriodFactor z * (xi j / (z + (j : ℂ))) := by
    intro j hj
    have hjne : z + (j : ℂ) ≠ 0 := hz j hj
    have hne : Complex.I * (z + (j : ℂ)) ≠ 0 := mul_ne_zero Complex.I_ne_zero hjne
    have htop : Complex.exp (Complex.I * (z + (j : ℂ)) * ((2 * Real.pi : ℝ) : ℂ))
        = Complex.exp (2 * (Real.pi : ℂ) * Complex.I * z) := by
      have hsplit : Complex.I * (z + (j : ℂ)) * ((2 * Real.pi : ℝ) : ℂ)
          = 2 * (Real.pi : ℂ) * Complex.I * z + (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        push_cast
        ring
      rw [hsplit, Complex.exp_add, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow,
        mul_one]
    have hbot : Complex.exp (Complex.I * (z + (j : ℂ)) * ((0 : ℝ) : ℂ)) = 1 := by
      simp
    rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hne, htop, hbot,
      ccmPeriodFactor]
    field_simp
  rw [compactFourier]
  have hint : (fun x : ℝ => ccmTrigPoly N xi x * Complex.exp (Complex.I * (z * (x : ℂ))))
      = fun x : ℝ => ∑ j ∈ ccmModeWindow N,
          xi j * Complex.exp (Complex.I * (z + (j : ℂ)) * (x : ℂ)) := by
    funext x
    rw [ccmTrigPoly, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_assoc, ← Complex.exp_add]
    have harg : Complex.I * ((j : ℂ) * (x : ℂ)) + Complex.I * (z * (x : ℂ))
        = Complex.I * (z + (j : ℂ)) * (x : ℂ) := by ring
    rw [harg]
  rw [hint, intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hstep
  · intro j _
    apply Continuous.intervalIntegrable
    fun_prop

/-! ## Odd coefficient vectors -/

/-- For an odd coefficient vector the two first-order resolvents differ by a sign. -/
theorem sum_ccmModeWindow_odd_neg (N : ℕ) {xi : ℤ → ℂ} (hodd : ∀ j : ℤ, xi (-j) = -xi j)
    (z : ℂ) :
    ∑ j ∈ ccmModeWindow N, xi j / (z + (j : ℂ))
      = -∑ j ∈ ccmModeWindow N, xi j / (z - (j : ℂ)) := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_nbij' (fun j => -j) (fun j => -j) (fun a ha => neg_mem_ccmModeWindow ha)
    (fun a ha => neg_mem_ccmModeWindow ha) (fun a _ => neg_neg a) (fun a _ => neg_neg a)
    fun a _ => ?_
  rw [hodd a]
  push_cast
  rw [neg_div, sub_neg_eq_add, neg_neg]

/-! ## The zero transfer -/

/-- Off the real axis, a zero of the band-limited Fourier transform is a zero of the first-order
Fourier resolvent of the odd coefficient vector. -/
theorem sum_eq_zero_of_compactFourier_ccmTrigPoly_eq_zero {N : ℕ} {xi : ℤ → ℂ} {z : ℂ}
    (hodd : ∀ j : ℤ, xi (-j) = -xi j) (him : z.im ≠ 0)
    (hzero : compactFourier (ccmTrigPoly N xi) 0 (2 * Real.pi) z = 0) :
    ∑ j ∈ ccmModeWindow N, xi j / (z - (j : ℂ)) = 0 := by
  have hz : ∀ j ∈ ccmModeWindow N, z + (j : ℂ) ≠ 0 := by
    intro j _ hcon
    apply him
    have := congrArg Complex.im hcon
    simpa using this
  rw [compactFourier_ccmTrigPoly N xi hz, sum_ccmModeWindow_odd_neg N hodd z] at hzero
  have hfac := ccmPeriodFactor_ne_zero him
  rcases mul_eq_zero.1 hzero with h | h
  · exact absurd h hfac
  · exact neg_eq_zero.1 h

/-- **Real zeros of the band-limited Fourier transform.**  If the first-order Fourier resolvent of
an odd coefficient vector has no nonreal zero, then neither does the Fourier transform of the
associated trigonometric polynomial on one period. -/
theorem compactFourier_ccmTrigPoly_zero_im_eq_zero {N : ℕ} {xi : ℤ → ℂ} {z : ℂ}
    (hodd : ∀ j : ℤ, xi (-j) = -xi j)
    (hres : ∀ w : ℂ, w.im ≠ 0 → (∑ j ∈ ccmModeWindow N, xi j / (w - (j : ℂ))) ≠ 0)
    (hzero : compactFourier (ccmTrigPoly N xi) 0 (2 * Real.pi) z = 0) :
    z.im = 0 := by
  by_contra him
  exact hres z him (sum_eq_zero_of_compactFourier_ccmTrigPoly_eq_zero hodd him hzero)

end

end RHTower
