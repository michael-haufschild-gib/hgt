import GaloisForLFunctions.RHTower.CompletedPrimeGammaMovingHankelReflection
import GaloisForLFunctions.RHTower.CompletedFluxGradedReality
import GaloisForLFunctions.RHTower.ReflectionParity

/-!
# Complex moving completed prime--Gamma Hankel determinants

The established moving determinant takes the real part of every Taylor coefficient before forming
its matrix.  That is the right target at the functional-equation center, but it destroys the
holomorphic function whose zero orders could transport the positive far-right orientation.

This file retains the full complex coefficients.  The resulting matrix and determinant satisfy the
same exact base reflection, and at `sigma = 1/2` they are precisely the scalar extension of the
existing real prime--Gamma Hankel matrix and determinant.  Thus analytic parity may be studied on a
complex function without changing the central RH consumer.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The full complex even Taylor coefficient, before applying `Complex.re`. -/
def complexAnalyticTraceMoment (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv (2 * n) f 0 / ((2 * n).factorial : ℂ)

/-- Taking the real part recovers the established real trace moment exactly. -/
@[simp] theorem complexAnalyticTraceMoment_re (f : ℂ → ℂ) (n : ℕ) :
    (complexAnalyticTraceMoment f n).re = analyticTraceMoments f n := rfl

/-- Full complex moving moment of the completed prime--Gamma source. -/
def completedMovingComplexMoment (sigma : ℂ) (k : ℕ) : ℂ :=
  complexAnalyticTraceMoment (completedMovingMomentGerm sigma) k

/-- Complex moving Hankel matrix, retaining all Taylor-coefficient phases. -/
def completedMovingComplexHankelMatrix (n : ℕ) (sigma : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => completedMovingComplexMoment sigma ((i : ℕ) + (j : ℕ))

/-- Complex determinant whose real central specialization is the RH Hankel determinant. -/
def completedMovingComplexHankelDet (n : ℕ) (sigma : ℂ) : ℂ :=
  (completedMovingComplexHankelMatrix n sigma).det

/-- Functional-equation reflection fixes every full complex moving moment. -/
@[simp] theorem completedMovingComplexMoment_one_sub (sigma : ℂ) (k : ℕ) :
    completedMovingComplexMoment (1 - sigma) k =
      completedMovingComplexMoment sigma k := by
  rw [completedMovingComplexMoment, completedMovingComplexMoment,
    complexAnalyticTraceMoment, complexAnalyticTraceMoment,
    iteratedDeriv_completedMovingMomentGerm_one_sub]
  have heven : (-1 : ℂ) ^ (2 * k) = 1 := by
    rw [pow_mul]
    norm_num
  rw [heven, one_mul]

/-- The complete complex moving Hankel matrix is reflection invariant. -/
@[simp] theorem completedMovingComplexHankelMatrix_one_sub (n : ℕ) (sigma : ℂ) :
    completedMovingComplexHankelMatrix n (1 - sigma) =
      completedMovingComplexHankelMatrix n sigma := by
  ext i j
  exact completedMovingComplexMoment_one_sub sigma ((i : ℕ) + (j : ℕ))

/-- **Complex determinant reflection.**  The full determinant is even about `1/2`. -/
@[simp] theorem completedMovingComplexHankelDet_one_sub (n : ℕ) (sigma : ℂ) :
    completedMovingComplexHankelDet n (1 - sigma) =
      completedMovingComplexHankelDet n sigma := by
  rw [completedMovingComplexHankelDet, completedMovingComplexHankelDet,
    completedMovingComplexHankelMatrix_one_sub]

/-- At the center, every full complex moment is the scalar extension of the established real
prime--Gamma moment. -/
@[simp] theorem completedMovingComplexMoment_one_half (k : ℕ) :
    completedMovingComplexMoment (1 / 2) k =
      (normalizedPrimeArchMoment k : ℂ) := by
  rw [completedMovingComplexMoment, complexAnalyticTraceMoment,
    completedMovingMomentGerm_one_half_eventuallyEq.iteratedDeriv_eq,
    iteratedDeriv_normalizedPrimeArchMomentGerm_two_mul]
  rw [normalizedPrimeArchMoment]
  have hfac : (((2 * k).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k)
  field_simp

/-- The center complex matrix is exactly base change of the real RH-consumer matrix. -/
@[simp] theorem completedMovingComplexHankelMatrix_one_half (n : ℕ) :
    completedMovingComplexHankelMatrix n (1 / 2) =
      (primeArchSourceMomentHankelMatrix n).map (algebraMap ℝ ℂ) := by
  ext i j
  rw [completedMovingComplexHankelMatrix, completedMovingComplexMoment_one_half,
    Matrix.map_apply, primeArchSourceMomentHankelMatrix_apply]
  rfl

/-- **No-loss central specialization.**  The center complex determinant is exactly the complex
cast of the established real prime--Gamma determinant. -/
@[simp] theorem completedMovingComplexHankelDet_one_half (n : ℕ) :
    completedMovingComplexHankelDet n (1 / 2) =
      ((primeArchSourceMomentHankelMatrix n).det : ℂ) := by
  rw [completedMovingComplexHankelDet,
    completedMovingComplexHankelMatrix_one_half]
  exact (RingHom.map_det (algebraMap ℝ ℂ)
    (primeArchSourceMomentHankelMatrix n)).symm

/-! ## Explicit holomorphic completed-source jet family -/

/-- The paper-defined odd logarithmic-derivative moment
`(-1)^k (xi'/xi)^(2k+1)(sigma)/(2k+1)!`. -/
def completedOddLogDerivMoment (sigma : ℂ) (k : ℕ) : ℂ :=
  (-1 : ℂ) ^ k * iteratedDeriv (2 * k + 1) (logDeriv xi) sigma /
    ((2 * k + 1).factorial : ℂ)

/-- Hankel matrix of the explicit odd logarithmic-derivative moments. -/
def completedOddLogDerivHankelMatrix (n : ℕ) (sigma : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => completedOddLogDerivMoment sigma ((i : ℕ) + (j : ℕ))

/-- Determinant of the explicit completed-source jet matrix. -/
def completedOddLogDerivHankelDet (n : ℕ) (sigma : ℂ) : ℂ :=
  (completedOddLogDerivHankelMatrix n sigma).det

/-- Every logarithmic-derivative jet has the parity dictated by the completed functional
equation. -/
private theorem iteratedDeriv_logDeriv_xi_one_sub (m : ℕ) (sigma : ℂ) :
    iteratedDeriv m (logDeriv xi) (1 - sigma) =
      (-1 : ℂ) ^ (m + 1) * iteratedDeriv m (logDeriv xi) sigma := by
  have hfun : (fun s : ℂ => logDeriv xi (1 - s)) = -(logDeriv xi) := by
    funext s
    exact logDeriv_xi_reciprocity s
  have hd := congrArg (fun f : ℂ → ℂ => iteratedDeriv m f sigma) hfun
  change iteratedDeriv m (fun s : ℂ => logDeriv xi (1 - s)) sigma =
    iteratedDeriv m (-(logDeriv xi)) sigma at hd
  rw [congrFun (iteratedDeriv_comp_const_sub m (logDeriv xi) 1) sigma,
    iteratedDeriv_neg] at hd
  have hd' : (-1 : ℂ) ^ m * iteratedDeriv m (logDeriv xi) (1 - sigma) =
      -iteratedDeriv m (logDeriv xi) sigma := by
    simpa only [smul_eq_mul] using hd
  have hsq : (-1 : ℂ) ^ m * (-1 : ℂ) ^ m = 1 := by
    rw [← pow_add, show m + m = 2 * m by omega, pow_mul]
    norm_num
  calc
    iteratedDeriv m (logDeriv xi) (1 - sigma) =
        (-1 : ℂ) ^ m *
          ((-1 : ℂ) ^ m * iteratedDeriv m (logDeriv xi) (1 - sigma)) := by
            rw [← mul_assoc, hsq, one_mul]
    _ = (-1 : ℂ) ^ m * (-iteratedDeriv m (logDeriv xi) sigma) := by rw [hd']
    _ = (-1 : ℂ) ^ (m + 1) * iteratedDeriv m (logDeriv xi) sigma := by
      rw [pow_succ]
      ring

/-- Odd completed-source moments are fixed by `sigma ↦ 1 - sigma`. -/
@[simp] theorem completedOddLogDerivMoment_one_sub (sigma : ℂ) (k : ℕ) :
    completedOddLogDerivMoment (1 - sigma) k = completedOddLogDerivMoment sigma k := by
  rw [completedOddLogDerivMoment, completedOddLogDerivMoment,
    iteratedDeriv_logDeriv_xi_one_sub]
  have heven : (-1 : ℂ) ^ (2 * k + 1 + 1) = 1 := by
    rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, pow_mul]
    norm_num
  rw [heven, one_mul]

/-- Exact reflection of the explicit completed-source jet matrix. -/
@[simp] theorem completedOddLogDerivHankelMatrix_one_sub (n : ℕ) (sigma : ℂ) :
    completedOddLogDerivHankelMatrix n (1 - sigma) =
      completedOddLogDerivHankelMatrix n sigma := by
  ext i j
  exact completedOddLogDerivMoment_one_sub sigma ((i : ℕ) + (j : ℕ))

/-- Exact reflection of the explicit holomorphic determinant family. -/
@[simp] theorem completedOddLogDerivHankelDet_one_sub (n : ℕ) (sigma : ℂ) :
    completedOddLogDerivHankelDet n (1 - sigma) =
      completedOddLogDerivHankelDet n sigma := by
  rw [completedOddLogDerivHankelDet, completedOddLogDerivHankelDet,
    completedOddLogDerivHankelMatrix_one_sub]

private theorem analyticAt_logDeriv_xi {sigma : ℂ} (hxi : xi sigma ≠ 0) :
    AnalyticAt ℂ (logDeriv xi) sigma := by
  change AnalyticAt ℂ (fun z => deriv xi z / xi z) sigma
  exact (xi_analyticOnNhd_univ sigma (Set.mem_univ sigma)).deriv.div
    (xi_analyticOnNhd_univ sigma (Set.mem_univ sigma)) hxi

private theorem analyticAt_iteratedDeriv_logDeriv_xi (m : ℕ) {sigma : ℂ}
    (hxi : xi sigma ≠ 0) : AnalyticAt ℂ (iteratedDeriv m (logDeriv xi)) sigma := by
  induction m with
  | zero => simpa using analyticAt_logDeriv_xi hxi
  | succ m ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- Every explicit odd completed-source moment is holomorphic away from the Xi divisor. -/
theorem analyticAt_completedOddLogDerivMoment (k : ℕ) {sigma : ℂ}
    (hxi : xi sigma ≠ 0) : AnalyticAt ℂ (fun s => completedOddLogDerivMoment s k) sigma := by
  change AnalyticAt ℂ (fun s =>
    (-1 : ℂ) ^ k * iteratedDeriv (2 * k + 1) (logDeriv xi) s /
      ((2 * k + 1).factorial : ℂ)) sigma
  exact (analyticAt_const.mul
    (analyticAt_iteratedDeriv_logDeriv_xi (2 * k + 1) hxi)).div_const

private theorem analyticAt_matrix_det_local {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : ℂ → Matrix ι ι ℂ} {z0 : ℂ}
    (hM : ∀ i j, AnalyticAt ℂ (fun z => M z i j) z0) :
    AnalyticAt ℂ (fun z => (M z).det) z0 := by
  have heq : (fun z => (M z).det) =
      fun z => ∑ sigma : Equiv.Perm ι,
        ((Equiv.Perm.sign sigma : ℤ) : ℂ) * ∏ i, M z (sigma i) i := by
    funext z
    rw [Matrix.det_apply]
    exact Finset.sum_congr rfl (fun sigma _ => by rw [Units.smul_def, zsmul_eq_mul])
  rw [heq]
  exact Finset.analyticAt_fun_sum _
    (fun sigma _ => analyticAt_const.mul
      (Finset.analyticAt_fun_prod _ (fun i _ => hM (sigma i) i)))

/-- **Holomorphic parity surface.**  The explicit completed-source Hankel determinant is analytic
at every point off the Xi divisor. -/
theorem analyticAt_completedOddLogDerivHankelDet (n : ℕ) {sigma : ℂ}
    (hxi : xi sigma ≠ 0) : AnalyticAt ℂ (completedOddLogDerivHankelDet n) sigma := by
  change AnalyticAt ℂ (fun s => (completedOddLogDerivHankelMatrix n s).det) sigma
  apply analyticAt_matrix_det_local
  intro i j
  exact analyticAt_completedOddLogDerivMoment ((i : ℕ) + (j : ℕ)) hxi

/-! ## Exact center bridge between the two complex families -/

private theorem iteratedDeriv_logDeriv_xi_centered_mul_I (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => logDeriv xi (1 / 2 + z * Complex.I)) 0 =
      Complex.I ^ m * iteratedDeriv m (logDeriv xi) (1 / 2) := by
  have hxi0 : xi (1 / 2 : ℂ) ≠ 0 := by
    simpa only [XiC, zero_mul, add_zero] using XiC_zero_ne
  have hev : ∀ᶠ s : ℂ in nhds (1 / 2), xi s ≠ 0 :=
    (xi_analyticOnNhd_univ (1 / 2) (Set.mem_univ _)).continuousAt.eventually_ne hxi0
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  let U : Set ℂ := Metric.ball 0 r
  let f : ℂ → ℂ := fun w => logDeriv xi (w + 1 / 2)
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUdiff : UniqueDiffOn ℂ U := hUopen.uniqueDiffOn
  have hzero : (0 : ℂ) ∈ U := by
    change dist (0 : ℂ) 0 < r
    simpa using hr
  have hf : AnalyticOnNhd ℂ f U := by
    intro w hw
    have hne : xi (w + 1 / 2) ≠ 0 := by
      apply hball
      rw [dist_eq_norm]
      have hwr : ‖w‖ < r := by
        change dist w 0 < r at hw
        simpa only [dist_zero_right] using hw
      simpa only [add_sub_cancel_right] using hwr
    have haff : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) w := by fun_prop
    exact (analyticAt_logDeriv_xi (sigma := w + 1 / 2) hne).comp
      (f := fun z : ℂ => z + 1 / 2) haff
  have hmap : Set.MapsTo (fun z : ℂ => Complex.I * z) U U := by
    intro z hz
    change dist z 0 < r at hz
    change dist (Complex.I * z) 0 < r
    rw [dist_zero_right] at hz ⊢
    rw [norm_mul, Complex.norm_I, one_mul]
    exact hz
  have hchain := iteratedDerivWithin_comp_const_smul
    (n := m) hzero hUdiff (hf.contDiffOn hUdiff) Complex.I hmap
  have hopenComp := iteratedDerivWithin_of_isOpen (n := m)
    (f := fun z : ℂ => f (Complex.I * z)) hUopen hzero
  have hopenF := iteratedDerivWithin_of_isOpen (n := m) (f := f) hUopen hzero
  simp only [mul_zero] at hchain
  rw [hopenComp, hopenF] at hchain
  dsimp only [f] at hchain
  norm_num at hchain
  rw [congrFun (iteratedDeriv_comp_add_const m (logDeriv xi) (1 / 2)) 0] at hchain
  simpa only [zero_add, mul_comm, add_comm, smul_eq_mul] using hchain

/-- **Exact affine center bridge.**  The full coefficient extracted from the moving normalized
germ is exactly the paper-defined odd logarithmic-derivative moment at `1/2`. -/
@[simp] theorem completedMovingComplexMoment_eq_completedOddLogDerivMoment_one_half
    (k : ℕ) :
    completedMovingComplexMoment (1 / 2) k =
      completedOddLogDerivMoment (1 / 2) k := by
  have hxi0 : xi (1 / 2 : ℂ) ≠ 0 := by
    simpa only [XiC, zero_mul, add_zero] using XiC_zero_ne
  have hXiCLog : AnalyticAt ℂ (logDeriv XiC) 0 := by
    change AnalyticAt ℂ (fun z => deriv XiC z / XiC z) 0
    exact (XiC_analytic 0 (Set.mem_univ 0)).deriv.div
      (XiC_analytic 0 (Set.mem_univ 0)) XiC_zero_ne
  have hT : AnalyticAt ℂ (completedMovingRelativeTrace (1 / 2)) 0 := by
    have hfun : completedMovingRelativeTrace (1 / 2) = logDeriv XiC := by
      funext z
      exact completedMovingRelativeTrace_one_half z
    rw [hfun]
    exact hXiCLog
  have hG : AnalyticAt ℂ (completedMovingMomentGerm (1 / 2)) 0 := by
    rw [completedMovingMomentGerm]
    exact analyticAt_normalizedTraceMomentGerm hT
  have hT0 : completedMovingRelativeTrace (1 / 2) 0 = 0 := by
    simp [completedMovingRelativeTrace]
  have hrel : oddTracePreimage (completedMovingMomentGerm (1 / 2)) =
      completedMovingRelativeTrace (1 / 2) := by
    simpa only [completedMovingMomentGerm] using
      oddTracePreimage_normalizedTraceMomentGerm_eq
        (completedMovingRelativeTrace (1 / 2)) hT0
  have hd := congrArg (fun f : ℂ → ℂ => iteratedDeriv (2 * k + 1) f 0) hrel
  have hodd : oddTracePreimage (completedMovingMomentGerm (1 / 2)) =
      -(fun z : ℂ => z * completedMovingMomentGerm (1 / 2) z) := by
    funext z
    simp only [oddTracePreimage, Pi.neg_apply]
    ring
  change iteratedDeriv (2 * k + 1)
      (oddTracePreimage (completedMovingMomentGerm (1 / 2))) 0 =
    iteratedDeriv (2 * k + 1) (completedMovingRelativeTrace (1 / 2)) 0 at hd
  rw [hodd, iteratedDeriv_neg,
    iteratedDeriv_id_mul_zero_succ (completedMovingMomentGerm (1 / 2))
      (2 * k) hG.contDiffAt] at hd
  have haff : AnalyticAt ℂ (fun z : ℂ => 1 / 2 + z * Complex.I) 0 := by fun_prop
  have hcomp : AnalyticAt ℂ
      (fun z : ℂ => logDeriv xi (1 / 2 + z * Complex.I)) 0 := by
    exact (analyticAt_logDeriv_xi (sigma := (1 / 2 : ℂ)) hxi0).comp_of_eq
      haff (by norm_num)
  change -(↑(2 * k + 1) *
      iteratedDeriv (2 * k) (completedMovingMomentGerm (1 / 2)) 0) =
    iteratedDeriv (2 * k + 1)
      (fun z : ℂ => Complex.I *
        (logDeriv xi (1 / 2 + z * Complex.I) - logDeriv xi (1 / 2))) 0 at hd
  have hsub : iteratedDeriv (2 * k + 1)
      (fun z : ℂ => logDeriv xi (1 / 2 + z * Complex.I) - logDeriv xi (1 / 2)) 0 =
      iteratedDeriv (2 * k + 1)
        (fun z : ℂ => logDeriv xi (1 / 2 + z * Complex.I)) 0 -
      iteratedDeriv (2 * k + 1) (fun _ : ℂ => logDeriv xi (1 / 2)) 0 := by
    change iteratedDeriv (2 * k + 1)
      ((fun z : ℂ => logDeriv xi (1 / 2 + z * Complex.I)) -
        (fun _ : ℂ => logDeriv xi (1 / 2))) 0 = _
    exact iteratedDeriv_sub hcomp.contDiffAt analyticAt_const.contDiffAt
  rw [iteratedDeriv_const_mul_field,
    hsub,
    iteratedDeriv_const,
    if_neg (by omega : 2 * k + 1 ≠ 0), sub_zero,
    iteratedDeriv_logDeriv_xi_centered_mul_I] at hd
  have hIpow : Complex.I * Complex.I ^ (2 * k + 1) = (-1 : ℂ) ^ (k + 1) := by
    rw [← pow_succ', show 2 * k + 1 + 1 = 2 * (k + 1) by omega,
      pow_mul, Complex.I_sq]
  rw [← mul_assoc, hIpow] at hd
  rw [completedMovingComplexMoment, complexAnalyticTraceMoment,
    completedOddLogDerivMoment]
  have hfac0 : (((2 * k).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k)
  have hfac1 : (((2 * k + 1).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k + 1)
  have hsign : -((-1 : ℂ) ^ (k + 1)) = (-1 : ℂ) ^ k := by
    rw [pow_succ]
    ring
  have hmain : ((2 * k + 1 : ℕ) : ℂ) *
      iteratedDeriv (2 * k) (completedMovingMomentGerm (1 / 2)) 0 =
      (-1 : ℂ) ^ k * iteratedDeriv (2 * k + 1) (logDeriv xi) (1 / 2) := by
    calc
      ((2 * k + 1 : ℕ) : ℂ) *
          iteratedDeriv (2 * k) (completedMovingMomentGerm (1 / 2)) 0 =
        -((-1 : ℂ) ^ (k + 1) *
          iteratedDeriv (2 * k + 1) (logDeriv xi) (1 / 2)) := by
            linear_combination -hd
      _ = (-1 : ℂ) ^ k *
          iteratedDeriv (2 * k + 1) (logDeriv xi) (1 / 2) := by
            calc
              -((-1 : ℂ) ^ (k + 1) *
                  iteratedDeriv (2 * k + 1) (logDeriv xi) (1 / 2)) =
                (-((-1 : ℂ) ^ (k + 1))) *
                  iteratedDeriv (2 * k + 1) (logDeriv xi) (1 / 2) := by ring
              _ = _ := by rw [hsign]
  apply (div_eq_div_iff hfac0 hfac1).2
  rw [show (2 * k + 1).factorial = (2 * k + 1) * (2 * k).factorial by
    rw [show 2 * k + 1 = (2 * k) + 1 by omega, Nat.factorial_succ]]
  rw [Nat.cast_mul]
  calc
    iteratedDeriv (2 * k) (completedMovingMomentGerm (1 / 2)) 0 *
        (((2 * k + 1 : ℕ) : ℂ) * (((2 * k).factorial : ℕ) : ℂ)) =
      (((2 * k + 1 : ℕ) : ℂ) *
        iteratedDeriv (2 * k) (completedMovingMomentGerm (1 / 2)) 0) *
          (((2 * k).factorial : ℕ) : ℂ) := by ring
    _ = ((-1 : ℂ) ^ k *
        iteratedDeriv (2 * k + 1) (logDeriv xi) (1 / 2)) *
          (((2 * k).factorial : ℕ) : ℂ) := by rw [hmain]

/-- The two complex moving Hankel matrices agree entrywise at the functional-equation center. -/
@[simp] theorem completedMovingComplexHankelMatrix_eq_completedOddLogDerivHankelMatrix_one_half
    (n : ℕ) :
    completedMovingComplexHankelMatrix n (1 / 2) =
      completedOddLogDerivHankelMatrix n (1 / 2) := by
  ext i j
  exact completedMovingComplexMoment_eq_completedOddLogDerivMoment_one_half
    ((i : ℕ) + (j : ℕ))

/-- **Explicit determinant center bridge.**  The holomorphic logarithmic-derivative determinant
specializes exactly to the complex lift of the established central RH determinant. -/
@[simp] theorem completedMovingComplexHankelDet_eq_completedOddLogDerivHankelDet_one_half
    (n : ℕ) :
    completedMovingComplexHankelDet n (1 / 2) =
      completedOddLogDerivHankelDet n (1 / 2) := by
  rw [completedMovingComplexHankelDet, completedOddLogDerivHankelDet,
    completedMovingComplexHankelMatrix_eq_completedOddLogDerivHankelMatrix_one_half]

/-! ## Schwarz reality of the explicit determinant -/

private theorem logDeriv_xi_conj_local (s : ℂ) :
    logDeriv xi ((starRingEnd ℂ) s) = (starRingEnd ℂ) (logDeriv xi s) := by
  have h := congrArg Neg.neg (seamFluxCochain_conj s)
  simpa only [seamFluxCochain, neg_neg, map_neg] using h

private theorem iteratedDeriv_logDeriv_xi_conj_local (m : ℕ) (s : ℂ) :
    iteratedDeriv m (logDeriv xi) ((starRingEnd ℂ) s) =
      (starRingEnd ℂ) (iteratedDeriv m (logDeriv xi) s) := by
  have hfun : (starRingEnd ℂ) ∘ (logDeriv xi) ∘ (starRingEnd ℂ) = logDeriv xi := by
    funext z
    simp only [Function.comp_apply]
    rw [logDeriv_xi_conj_local, Complex.conj_conj]
  have hd := iteratedDeriv_conj_conj (logDeriv xi) m
  rw [hfun] at hd
  have hval := congrFun hd ((starRingEnd ℂ) s)
  simpa only [Function.comp_apply, Complex.conj_conj] using hval

/-- Every explicit completed-source moment is Schwarz-equivariant in its base point. -/
@[simp] theorem completedOddLogDerivMoment_conj (sigma : ℂ) (k : ℕ) :
    completedOddLogDerivMoment ((starRingEnd ℂ) sigma) k =
      (starRingEnd ℂ) (completedOddLogDerivMoment sigma k) := by
  rw [completedOddLogDerivMoment, completedOddLogDerivMoment,
    iteratedDeriv_logDeriv_xi_conj_local]
  simp only [map_div₀, map_mul, map_pow, map_neg, map_one, map_natCast]

/-- The explicit completed-source jet matrix is Schwarz-equivariant. -/
@[simp] theorem completedOddLogDerivHankelMatrix_conj (n : ℕ) (sigma : ℂ) :
    completedOddLogDerivHankelMatrix n ((starRingEnd ℂ) sigma) =
      (completedOddLogDerivHankelMatrix n sigma).map (starRingEnd ℂ) := by
  ext i j
  rw [completedOddLogDerivHankelMatrix, Matrix.map_apply,
    completedOddLogDerivMoment_conj]
  rfl

/-- The explicit holomorphic determinant is Schwarz-equivariant. -/
@[simp] theorem completedOddLogDerivHankelDet_conj (n : ℕ) (sigma : ℂ) :
    completedOddLogDerivHankelDet n ((starRingEnd ℂ) sigma) =
      (starRingEnd ℂ) (completedOddLogDerivHankelDet n sigma) := by
  rw [completedOddLogDerivHankelDet, completedOddLogDerivHankelMatrix_conj,
    completedOddLogDerivHankelDet]
  exact (RingHom.map_det (starRingEnd ℂ)
    (completedOddLogDerivHankelMatrix n sigma)).symm

/-- Every explicit moment is real on the real base axis. -/
@[simp] theorem completedOddLogDerivMoment_ofReal_im (x : ℝ) (k : ℕ) :
    (completedOddLogDerivMoment (x : ℂ) k).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa using (completedOddLogDerivMoment_conj (x : ℂ) k).symm

/-- **Real-axis orientation surface.**  The explicit completed-source determinant is real on the
entire real axis, including points where the logarithmic derivative is filled by Lean's derivative
convention. -/
@[simp] theorem completedOddLogDerivHankelDet_ofReal_im (n : ℕ) (x : ℝ) :
    (completedOddLogDerivHankelDet n (x : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  simpa using (completedOddLogDerivHankelDet_conj n (x : ℂ)).symm

/-- Reflection forces even analytic order at the center whenever the determinant germ is not
locally identically zero.  This discharges the fixed-point member of the parity target; only
noncentral real determinant zeros can reverse the far-right orientation. -/
theorem completedOddLogDerivHankelDet_central_order_even (n : ℕ)
    (hne : analyticOrderAt (completedOddLogDerivHankelDet n) (1 / 2) ≠ ⊤) :
    Even (analyticOrderAt (completedOddLogDerivHankelDet n) (1 / 2)).toNat := by
  have hxi0 : xi (1 / 2 : ℂ) ≠ 0 := by
    simpa only [XiC, zero_mul, add_zero] using XiC_zero_ne
  apply analyticOrderAt_even_of_reflection_eventually
    (analyticAt_completedOddLogDerivHankelDet n hxi0) _ hne
  filter_upwards with sigma
  have harg : 2 * (1 / 2 : ℂ) - sigma = 1 - sigma := by ring
  rw [harg, completedOddLogDerivHankelDet_one_sub]

end

end RHTower
