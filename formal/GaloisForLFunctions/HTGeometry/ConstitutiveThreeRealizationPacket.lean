import Mathlib
import GaloisForLFunctions.HTGeometry.ConstitutiveCyclicProcessFourShadow

/-!
# One spectral packet, three unlike realizations

A finite spectral packet `(λⱼ, wⱼ)` produces one response sequence `mₙ = ∑ⱼ wⱼ λⱼⁿ`, which is
simultaneously the moment sequence of an atomic measure, the jet at the origin of an exponential
polynomial annihilated by a constant-coefficient differential operator, and the state-space response
of a diagonal operator triple.  One polynomial supplies the recurrence, the differential equation,
the poles of the transfer function and the withheld response.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset Polynomial
open scoped Matrix

section SpectralPacket

variable {r : ℕ}

/-- The constitutive response sequence of a spectral packet, equation (1), with complex weights. -/
noncomputable def packetMoment (lam w : Fin r → ℂ) (n : ℕ) : ℂ := ∑ j, w j * lam j ^ n

/-- Real weights recover the response sequence of the cyclic process. -/
theorem packetMoment_ofReal (lam : Fin r → ℂ) (w : Fin r → ℝ) (n : ℕ) :
    packetMoment lam (fun j => (w j : ℂ)) n = processMoment lam w n := rfl

/-! ### §3 — the shared recurrence and transfer law -/

/-- **Equation (8).**  The response obeys the order-`r` recurrence of the packet polynomial. -/
theorem packetMoment_recurrence (lam w : Fin r → ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (r + 1), (spectrumPoly lam).coeff k * packetMoment lam w (n + k) = 0 := by
  have hswap : ∑ k ∈ Finset.range (r + 1), (spectrumPoly lam).coeff k * packetMoment lam w (n + k)
      = ∑ j, w j * lam j ^ n
        * ∑ k ∈ Finset.range (r + 1), (spectrumPoly lam).coeff k * lam j ^ k := by
    have hexp : ∀ k, (spectrumPoly lam).coeff k * packetMoment lam w (n + k)
        = ∑ j, (spectrumPoly lam).coeff k * (w j * lam j ^ (n + k)) := by
      intro k
      rw [packetMoment, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun k _ => hexp k, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add]
    ring
  rw [hswap]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hev : ∑ k ∈ Finset.range (r + 1), (spectrumPoly lam).coeff k * lam j ^ k
      = (spectrumPoly lam).eval (lam j) :=
    (eval_eq_sum_range' (n := r + 1) (by rw [natDegree_spectrumPoly]; omega) _).symm
  rw [hev, eval_spectrumPoly, mul_zero]

/-- **Equation (12).**  The withheld response is predicted by the packet polynomial. -/
theorem packet_withheld_prediction (lam w : Fin r → ℂ) :
    packetMoment lam w (2 * r)
      = -∑ k ∈ Finset.range r, (spectrumPoly lam).coeff k * packetMoment lam w (r + k) := by
  have h := packetMoment_recurrence lam w r
  rw [Finset.sum_range_succ, coeff_spectrumPoly_top, one_mul] at h
  have hidx : r + r = 2 * r := by ring
  rw [hidx] at h
  linear_combination h

/-- **Equation (9).**  The generating function of the response is rational. -/
theorem tsum_packetMoment_mul_pow (lam w : Fin r → ℂ) {z : ℂ}
    (hz : ∀ j, ‖lam j * z‖ < 1) :
    ∑' n : ℕ, packetMoment lam w n * z ^ n = ∑ j, w j / (1 - lam j * z) := by
  have hfun : ∀ n : ℕ, packetMoment lam w n * z ^ n = ∑ j, w j * (lam j * z) ^ n := by
    intro n
    rw [packetMoment, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow]
    ring
  rw [tsum_congr hfun,
    Summable.tsum_finsetSum fun j _ => (summable_geometric_of_norm_lt_one (hz j)).mul_left _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (hz j), div_eq_mul_inv]

/-! ### §2.3 — the linear operator chart -/

/-- **Equation (6).**  The response is the state-space response of the diagonal triple
`(A, b, c) = (diag λ, 1, w)`. -/
theorem packetMoment_eq_operator (lam w : Fin r → ℂ) (n : ℕ) :
    packetMoment lam w n
      = w ⬝ᵥ ((Matrix.diagonal lam ^ n).mulVec (fun _ => 1)) := by
  rw [packetMoment, dotProduct]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diagonal_pow, Matrix.mulVec_diagonal, mul_one, Pi.pow_apply]

/-- **Equation (7).**  In the positive chamber the response is the unitary orbit overlap. -/
theorem packetMoment_eq_orbit (lam : Fin r → ℂ) (w : Fin r → ℝ) (hw : ∀ j, 0 ≤ w j) (n : ℕ) :
    packetMoment lam (fun j => (w j : ℂ)) n
      = ∑ j, (starRingEnd ℂ) ((Real.sqrt (w j) : ℝ) : ℂ)
        * (lam j ^ n * ((Real.sqrt (w j) : ℝ) : ℂ)) := by
  rw [packetMoment]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.conj_ofReal]
  have hsq : ((Real.sqrt (w j) : ℝ) : ℂ) * ((Real.sqrt (w j) : ℝ) : ℂ) = ((w j : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw j)]
  calc ((w j : ℝ) : ℂ) * lam j ^ n
      = (((Real.sqrt (w j) : ℝ) : ℂ) * ((Real.sqrt (w j) : ℝ) : ℂ)) * lam j ^ n := by rw [hsq]
    _ = _ := by ring

/-! ### §2.2 — the analytic differential chart -/

/-- The exponential polynomial of the packet. -/
noncomputable def packetFun (lam w : Fin r → ℂ) (t : ℂ) : ℂ :=
  ∑ j, w j * Complex.exp (lam j * t)

theorem hasDerivAt_exp_mul (lam t : ℂ) :
    HasDerivAt (fun s : ℂ => Complex.exp (lam * s)) (lam * Complex.exp (lam * t)) t := by
  have h : HasDerivAt (fun s : ℂ => lam * s) lam t := by
    simpa using (hasDerivAt_id t).const_mul lam
  simpa [mul_comm] using h.cexp

/-- The jets of the exponential polynomial. -/
theorem iteratedDeriv_packetFun (lam w : Fin r → ℂ) (n : ℕ) :
    iteratedDeriv n (packetFun lam w)
      = fun t => ∑ j, w j * lam j ^ n * Complex.exp (lam j * t) := by
  induction n with
  | zero =>
    funext t
    rw [iteratedDeriv_zero, packetFun]
    exact Finset.sum_congr rfl fun j _ => by ring
  | succ m ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    have hdiff : ∀ j : Fin r, DifferentiableAt ℂ
        (fun s => w j * lam j ^ m * Complex.exp (lam j * s)) t :=
      fun j => ((hasDerivAt_exp_mul (lam j) t).differentiableAt).const_mul _
    rw [deriv_fun_sum fun j _ => hdiff j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [deriv_const_mul _ (hasDerivAt_exp_mul (lam j) t).differentiableAt,
      (hasDerivAt_exp_mul (lam j) t).deriv]
    ring

/-- **Equation (4).**  The jets at the origin are the response sequence. -/
theorem iteratedDeriv_packetFun_zero (lam w : Fin r → ℂ) (n : ℕ) :
    iteratedDeriv n (packetFun lam w) 0 = packetMoment lam w n := by
  rw [iteratedDeriv_packetFun, packetMoment]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_zero, Complex.exp_zero, mul_one]

/-- **Equation (5).**  The exponential polynomial is annihilated by the packet operator `p(D)`. -/
theorem packet_ODE (lam w : Fin r → ℂ) (t : ℂ) :
    ∑ k ∈ Finset.range (r + 1),
        (spectrumPoly lam).coeff k * iteratedDeriv k (packetFun lam w) t = 0 := by
  have hswap : ∑ k ∈ Finset.range (r + 1),
        (spectrumPoly lam).coeff k * iteratedDeriv k (packetFun lam w) t
      = ∑ j, w j * Complex.exp (lam j * t)
        * ∑ k ∈ Finset.range (r + 1), (spectrumPoly lam).coeff k * lam j ^ k := by
    have hexp : ∀ k, (spectrumPoly lam).coeff k * iteratedDeriv k (packetFun lam w) t
        = ∑ j, (spectrumPoly lam).coeff k * (w j * lam j ^ k * Complex.exp (lam j * t)) := by
      intro k
      rw [iteratedDeriv_packetFun, Finset.mul_sum]
    rw [Finset.sum_congr rfl fun k _ => hexp k, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hswap]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hev : ∑ k ∈ Finset.range (r + 1), (spectrumPoly lam).coeff k * lam j ^ k
      = (spectrumPoly lam).eval (lam j) :=
    (eval_eq_sum_range' (n := r + 1) (by rw [natDegree_spectrumPoly]; omega) _).symm
  rw [hev, eval_spectrumPoly, mul_zero]

/-! ### §2.1 — the atomic moment chart -/

/-- The atomic spectral measure of a positive packet. -/
noncomputable def packetMeasure (lam : Fin r → ℂ) (w : Fin r → ℝ) : MeasureTheory.Measure ℂ :=
  ∑ j, (ENNReal.ofReal (w j)) • MeasureTheory.Measure.dirac (lam j)

/-- **Equation (3).**  The response is the moment sequence of the atomic measure. -/
theorem integral_packetMeasure (lam : Fin r → ℂ) (w : Fin r → ℝ) (hw : ∀ j, 0 ≤ w j) (n : ℕ) :
    ∫ x, x ^ n ∂(packetMeasure lam w) = packetMoment lam (fun j => (w j : ℂ)) n := by
  have hint : ∀ j : Fin r, MeasureTheory.Integrable (fun x : ℂ => x ^ n)
      (MeasureTheory.Measure.dirac (lam j)) := by
    intro j
    constructor
    · exact (by fun_prop : Continuous fun x : ℂ => x ^ n).aestronglyMeasurable
    · rw [MeasureTheory.hasFiniteIntegral_iff_enorm,
        MeasureTheory.lintegral_dirac' _ (by fun_prop)]
      exact enorm_lt_top
  rw [packetMeasure, MeasureTheory.integral_finsetSum_measure, packetMoment]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [MeasureTheory.integral_smul_measure, MeasureTheory.integral_dirac,
      ENNReal.toReal_ofReal (hw j), Complex.real_smul]
  · exact fun j _ => (hint j).smul_measure (by simp)

/-! ### §4 — the Hankel window and its rank -/

/-- The rectangular Vandermonde matrix of the packet frequencies. -/
noncomputable def rectVandermonde (lam : Fin r → ℂ) (N : ℕ) : Matrix (Fin r) (Fin (N + 1)) ℂ :=
  Matrix.of fun k i => lam k ^ (i : ℕ)

@[simp] theorem rectVandermonde_apply (lam : Fin r → ℂ) (N : ℕ) (k : Fin r) (i : Fin (N + 1)) :
    rectVandermonde lam N k i = lam k ^ (i : ℕ) := rfl

/-- The Hankel window of the response through time `N`. -/
noncomputable def packetHankel (lam w : Fin r → ℂ) (N : ℕ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  Matrix.of fun i j => packetMoment lam w ((i : ℕ) + (j : ℕ))

@[simp] theorem packetHankel_apply (lam w : Fin r → ℂ) (N : ℕ) (i j : Fin (N + 1)) :
    packetHankel lam w N i j = packetMoment lam w ((i : ℕ) + (j : ℕ)) := rfl

/-- **Equation (10).**  The Hankel window factors through the rectangular Vandermonde matrix. -/
theorem packetHankel_eq (lam w : Fin r → ℂ) (N : ℕ) :
    packetHankel lam w N
      = (rectVandermonde lam N)ᵀ * Matrix.diagonal w * rectVandermonde lam N := by
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply, packetHankel_apply, packetMoment]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.transpose_apply, rectVandermonde_apply, Matrix.mul_apply, Finset.sum_eq_single k]
  · rw [Matrix.diagonal_apply_eq, rectVandermonde_apply, pow_add]
    ring
  · intro l _ hl
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hl), zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- **Equation (11), the valid half.**  The Hankel window can never see more than `r` modes,
nor more than the `N + 1` samples it is built from. -/
theorem rank_packetHankel_le (lam w : Fin r → ℂ) (N : ℕ) :
    (packetHankel lam w N).rank ≤ min (N + 1) r := by
  rw [packetHankel_eq]
  refine (Matrix.rank_mul_le_right _ _).trans (le_min ?_ ?_)
  · exact Matrix.rank_le_width _
  · exact Matrix.rank_le_height _

/-- The square Hankel matrix of the first `2r − 1` responses of a complex packet. -/
noncomputable def packetHankelSq (lam w : Fin r → ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => packetMoment lam w ((i : ℕ) + (j : ℕ))

theorem packetHankelSq_eq (lam w : Fin r → ℂ) :
    packetHankelSq lam w
      = (Matrix.vandermonde lam)ᵀ * Matrix.diagonal w * Matrix.vandermonde lam := by
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  show packetMoment lam w ((i : ℕ) + (j : ℕ)) = _
  rw [packetMoment]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.transpose_apply, Matrix.vandermonde_apply, Matrix.mul_apply, Finset.sum_eq_single k]
  · rw [Matrix.diagonal_apply_eq, Matrix.vandermonde_apply, pow_add]
    ring
  · intro l _ hl
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hl), zero_mul]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem det_packetHankelSq (lam w : Fin r → ℂ) :
    (packetHankelSq lam w).det = (Matrix.vandermonde lam).det ^ 2 * ∏ j, w j := by
  rw [packetHankelSq_eq, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    Matrix.det_diagonal]
  ring

theorem det_packetHankelSq_ne_zero (lam w : Fin r → ℂ) (hinj : Function.Injective lam)
    (hw : ∀ j, w j ≠ 0) : (packetHankelSq lam w).det ≠ 0 := by
  rw [det_packetHankelSq]
  exact mul_ne_zero (pow_ne_zero _ (Matrix.det_vandermonde_ne_zero_iff.mpr hinj))
    (Finset.prod_ne_zero_iff.mpr fun j _ => hw j)

/-- **Equation (11), the saturated regime.**  Once the window is at least as long as the
number of modes, the Hankel rank is exactly the number of modes. -/
theorem rank_packetHankel_of_le (lam w : Fin r → ℂ) (hinj : Function.Injective lam)
    (hw : ∀ j, w j ≠ 0) {N : ℕ} (hN : r ≤ N + 1) :
    (packetHankel lam w N).rank = r := by
  refine le_antisymm ((rank_packetHankel_le lam w N).trans (min_le_right _ _)) ?_
  set e : Fin r → Fin (N + 1) := fun i => ⟨(i : ℕ), by omega⟩ with he
  have hsub : (packetHankel lam w N).submatrix e e = packetHankelSq lam w := rfl
  have hrk : ((packetHankel lam w N).submatrix e e).rank = r := by
    rw [hsub, Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr (det_packetHankelSq_ne_zero lam w hinj hw))), Fintype.card_fin]
  calc r = ((packetHankel lam w N).submatrix e e).rank := hrk.symm
    _ ≤ (packetHankel lam w N).rank := Matrix.rank_submatrix_le _ _ _

/-! ### §4, the short-window rank law fails -/

/-- A square matrix of full rank has nonzero determinant. -/
theorem det_ne_zero_of_rank_eq_card {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (h : A.rank = Fintype.card n) : A.det ≠ 0 := by
  have htop : LinearMap.range A.mulVecLin = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [show Module.finrank ℂ (LinearMap.range A.mulVecLin) = A.rank from rfl, h,
      Module.finrank_pi ℂ]
  have hsurj : Function.Surjective A.mulVecLin := LinearMap.range_eq_top.mp htop
  have hinj : Function.Injective A.mulVecLin :=
    (LinearMap.injective_iff_surjective (K := ℂ) (V := n → ℂ)).mpr hsurj
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hv (hinj (by simpa [Matrix.mulVecLin_apply] using hAv))

/-- A primitive cube root of unity. -/
noncomputable def cubeRoot : ℂ := ⟨-(1 / 2), Real.sqrt 3 / 2⟩

private theorem sqrt_three_mul_self : Real.sqrt 3 * Real.sqrt 3 = 3 :=
  Real.mul_self_sqrt (by norm_num)

theorem cubeRoot_sq : cubeRoot ^ 2 = ⟨-(1 / 2), -(Real.sqrt 3 / 2)⟩ := by
  have hs := sqrt_three_mul_self
  rw [pow_two]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, cubeRoot] <;> nlinarith [hs]

theorem cubeRoot_sum : 1 + cubeRoot + cubeRoot ^ 2 = 0 := by
  rw [cubeRoot_sq]
  apply Complex.ext <;> norm_num [cubeRoot]

theorem cubeRoot_pow_three : cubeRoot ^ 3 = 1 := by
  have hs := sqrt_three_mul_self
  have h : cubeRoot ^ 3 = cubeRoot * cubeRoot ^ 2 := by ring
  rw [h, cubeRoot_sq]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, cubeRoot] <;> nlinarith [hs]

theorem cubeRoot_im_pos : 0 < cubeRoot.im := by
  have : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  show (0 : ℝ) < Real.sqrt 3 / 2
  linarith

/-- The three cube roots of unity. -/
noncomputable def cubeLam : Fin 3 → ℂ := ![1, cubeRoot, cubeRoot ^ 2]

/-- The uniform positive weight on the three cube roots. -/
noncomputable def cubeW : Fin 3 → ℂ := ![1 / 3, 1 / 3, 1 / 3]

theorem cubeLam_injective : Function.Injective cubeLam := by
  have hs : (0 : ℝ) < Real.sqrt 3 / 2 := by
    have h3 := Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num)
    linarith
  have him : ∀ j : Fin 3,
      (cubeLam j).im = ![0, Real.sqrt 3 / 2, -(Real.sqrt 3 / 2)] j := by
    intro j
    fin_cases j
    · show (1 : ℂ).im = _
      simp
    · show cubeRoot.im = _
      simp [cubeRoot]
    · show (cubeRoot ^ 2).im = _
      rw [cubeRoot_sq]
      simp
  intro a b hab
  have h := congrArg Complex.im hab
  rw [him a, him b] at h
  fin_cases a <;> fin_cases b <;> simp at h ⊢ <;> first | rfl | (exfalso; linarith)

theorem cubeW_pos : ∀ j, 0 < (cubeW j).re := by
  intro j
  fin_cases j <;> norm_num [cubeW]

theorem cubeW_real : ∀ j, (cubeW j).im = 0 := by
  intro j
  fin_cases j <;> norm_num [cubeW]

theorem packetMoment_cube_zero : packetMoment cubeLam cubeW 0 = 1 := by
  rw [packetMoment, Fin.sum_univ_three]
  show (1 : ℂ) / 3 * (1 : ℂ) ^ 0 + 1 / 3 * cubeRoot ^ 0 + 1 / 3 * (cubeRoot ^ 2) ^ 0 = 1
  norm_num

theorem packetMoment_cube_one : packetMoment cubeLam cubeW 1 = 0 := by
  have hsum := cubeRoot_sum
  rw [packetMoment, Fin.sum_univ_three]
  show (1 : ℂ) / 3 * (1 : ℂ) ^ 1 + 1 / 3 * cubeRoot ^ 1 + 1 / 3 * (cubeRoot ^ 2) ^ 1 = 0
  linear_combination hsum / 3

theorem packetMoment_cube_two : packetMoment cubeLam cubeW 2 = 0 := by
  have hsum := cubeRoot_sum
  have hcube := cubeRoot_pow_three
  rw [packetMoment, Fin.sum_univ_three]
  show (1 : ℂ) / 3 * (1 : ℂ) ^ 2 + 1 / 3 * cubeRoot ^ 2 + 1 / 3 * (cubeRoot ^ 2) ^ 2 = 0
  linear_combination hsum / 3 + (cubeRoot / 3) * hcube

/-- **The short-window rank law is false.**  For three unit-modulus modes with uniform positive
weights the Hankel window of length two has rank one, not `min (N + 1) r = 2`: the naive
identity `rank H_N = min (N + 1) r` fails in exactly the unsaturated regime `N + 1 < r`,
even inside the positive chamber. -/
theorem rank_packetHankel_cube :
    (packetHankel cubeLam cubeW 1).rank = 1 ∧ (1 : ℕ) < min (1 + 1) 3 := by
  have hm0 := packetMoment_cube_zero
  have hm1 := packetMoment_cube_one
  have hm2 := packetMoment_cube_two
  have hdet : (packetHankel cubeLam cubeW 1).det = 0 := by
    rw [Matrix.det_fin_two]
    show packetMoment cubeLam cubeW (0 + 0) * packetMoment cubeLam cubeW (1 + 1)
      - packetMoment cubeLam cubeW (0 + 1) * packetMoment cubeLam cubeW (1 + 0) = 0
    norm_num [hm0, hm1, hm2]
  have hne2 : (packetHankel cubeLam cubeW 1).rank ≠ 2 := by
    intro h
    exact det_ne_zero_of_rank_eq_card _ (by rw [h]; simp) hdet
  have hle : (packetHankel cubeLam cubeW 1).rank ≤ 2 := by
    simpa using rank_packetHankel_le cubeLam cubeW 1
  have hge : 1 ≤ (packetHankel cubeLam cubeW 1).rank := by
    set e : Fin 1 → Fin 2 := fun _ => 0 with he
    have hsub : ((packetHankel cubeLam cubeW 1).submatrix e e).det ≠ 0 := by
      rw [Matrix.det_unique]
      show packetMoment cubeLam cubeW (0 + 0) ≠ 0
      rw [show (0 : ℕ) + 0 = 0 from rfl, hm0]
      exact one_ne_zero
    have hrk : ((packetHankel cubeLam cubeW 1).submatrix e e).rank = 1 := by
      rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr
        (isUnit_iff_ne_zero.mpr hsub)), Fintype.card_fin]
    calc (1 : ℕ) = ((packetHankel cubeLam cubeW 1).submatrix e e).rank := hrk.symm
      _ ≤ (packetHankel cubeLam cubeW 1).rank := Matrix.rank_submatrix_le _ _ _
  exact ⟨by omega, by norm_num⟩

/-! ### §4 — exact Prony reconstruction from the first `2r` responses -/

private theorem mulVec_injective_of_det_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (h : A.det ≠ 0) : Function.Injective A.mulVec := by
  intro a b hab
  have hstep : A⁻¹ *ᵥ (A *ᵥ a) = A⁻¹ *ᵥ (A *ᵥ b) := by rw [hab]
  simpa only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h),
    Matrix.one_mulVec] using hstep

/-- The recurrence in the form used by the Hankel system. -/
theorem packetMoment_recurrence_fin (lam w : Fin r → ℂ) (n : ℕ) :
    ∑ k : Fin r, (spectrumPoly lam).coeff (k : ℕ) * packetMoment lam w (n + (k : ℕ))
      = -packetMoment lam w (n + r) := by
  have h := packetMoment_recurrence lam w n
  rw [Finset.sum_range_succ, coeff_spectrumPoly_top, one_mul] at h
  rw [Fin.sum_univ_eq_sum_range
    (fun k => (spectrumPoly lam).coeff k * packetMoment lam w (n + k))]
  linear_combination h

/-- The recurrence coefficients solve the leading Hankel system. -/
theorem packetHankelSq_mulVec_coeff (lam w : Fin r → ℂ) (i : Fin r) :
    (packetHankelSq lam w).mulVec (fun k : Fin r => (spectrumPoly lam).coeff (k : ℕ)) i
      = -packetMoment lam w ((i : ℕ) + r) := by
  rw [← packetMoment_recurrence_fin lam w (i : ℕ), Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun k _ => ?_
  show packetMoment lam w ((i : ℕ) + (k : ℕ)) * (spectrumPoly lam).coeff (k : ℕ) = _
  ring

/-- The first `2r` responses determine the recurrence coefficients. -/
theorem packet_coeff_eq_of_responses_eq (lam lam' w w' : Fin r → ℂ)
    (hinj : Function.Injective lam) (hw : ∀ j, w j ≠ 0)
    (h : ∀ n, n < 2 * r → packetMoment lam w n = packetMoment lam' w' n) (k : Fin r) :
    (spectrumPoly lam).coeff (k : ℕ) = (spectrumPoly lam').coeff (k : ℕ) := by
  have hH : packetHankelSq lam w = packetHankelSq lam' w' := by
    ext i j
    exact h _ (by omega)
  have hsys : (packetHankelSq lam w).mulVec (fun k : Fin r => (spectrumPoly lam).coeff (k : ℕ))
      = (packetHankelSq lam w).mulVec (fun k : Fin r => (spectrumPoly lam').coeff (k : ℕ)) := by
    funext i
    rw [packetHankelSq_mulVec_coeff, hH, packetHankelSq_mulVec_coeff]
    congr 1
    exact h _ (by omega)
  exact congrFun (mulVec_injective_of_det_ne_zero _
    (det_packetHankelSq_ne_zero lam w hinj hw) hsys) k

/-- The first `2r` responses determine every later response. -/
theorem packetMoment_eq_of_eq_below (lam lam' w w' : Fin r → ℂ)
    (hinj : Function.Injective lam) (hw : ∀ j, w j ≠ 0)
    (h : ∀ n, n < 2 * r → packetMoment lam w n = packetMoment lam' w' n) (n : ℕ) :
    packetMoment lam w n = packetMoment lam' w' n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < 2 * r
    · exact h n hn
    · have hnr : n - r + r = n := by omega
      have hL := packetMoment_recurrence_fin lam w (n - r)
      have hR := packetMoment_recurrence_fin lam' w' (n - r)
      rw [hnr] at hL hR
      have hterms : ∑ k : Fin r, (spectrumPoly lam).coeff (k : ℕ)
            * packetMoment lam w (n - r + (k : ℕ))
          = ∑ k : Fin r, (spectrumPoly lam').coeff (k : ℕ)
            * packetMoment lam' w' (n - r + (k : ℕ)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [packet_coeff_eq_of_responses_eq lam lam' w w' hinj hw h k,
          ih (n - r + (k : ℕ)) (by omega)]
      have hneg : -packetMoment lam w n = -packetMoment lam' w' n := by
        rw [← hL, ← hR, hterms]
      linear_combination -hneg

/-- The first `2r` responses determine the spectrum polynomial, hence the unordered packet of
frequencies. -/
theorem packet_spectrumPoly_eq_of_responses_eq (lam lam' w w' : Fin r → ℂ)
    (hinj : Function.Injective lam) (hw : ∀ j, w j ≠ 0)
    (h : ∀ n, n < 2 * r → packetMoment lam w n = packetMoment lam' w' n) :
    spectrumPoly lam = spectrumPoly lam' := by
  refine Polynomial.ext fun k => ?_
  rcases lt_trichotomy k r with hk | hk | hk
  · exact packet_coeff_eq_of_responses_eq lam lam' w w' hinj hw h ⟨k, hk⟩
  · subst hk
    rw [coeff_spectrumPoly_top, coeff_spectrumPoly_top]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_spectrumPoly]; omega),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [natDegree_spectrumPoly]; omega)]

/-- Given the frequencies, the first `r` responses determine the weights. -/
theorem packet_weights_eq_of_responses_eq (lam w w' : Fin r → ℂ)
    (hinj : Function.Injective lam)
    (h : ∀ n, n < r → packetMoment lam w n = packetMoment lam w' n) : w = w' := by
  have hV : (Matrix.vandermonde lam)ᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hd : (Matrix.vandermonde lam)ᵀ *ᵥ (fun j => w j - w' j)
      = (Matrix.vandermonde lam)ᵀ *ᵥ (fun _ => (0 : ℂ)) := by
    funext i
    rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
    have hzero : ∑ j, (Matrix.vandermonde lam)ᵀ i j * (0 : ℂ) = 0 := by simp
    rw [hzero]
    have hexp : ∑ j, (Matrix.vandermonde lam)ᵀ i j * (w j - w' j)
        = packetMoment lam w (i : ℕ) - packetMoment lam w' (i : ℕ) := by
      rw [packetMoment, packetMoment, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.transpose_apply, Matrix.vandermonde_apply]
      ring
    rw [hexp, h (i : ℕ) i.isLt, sub_self]
  have hzero := mulVec_injective_of_det_ne_zero _ hV hd
  funext j
  have hj := congrFun hzero j
  linear_combination hj

/-! ### §5 — the positive unitary chamber -/

/-- The Toeplitz response matrix of a positive packet on the unit circle is the Gram matrix of
the unitary orbit, and its entries are the responses. -/
theorem momentGram_apply_packet (lam : Fin r → ℂ) (w : Fin r → ℝ)
    (hlam : ∀ j, ‖lam j‖ = 1) (hw : ∀ j, 0 ≤ w j) (N : ℕ) {i j : Fin (N + 1)}
    (hij : (i : ℕ) ≤ (j : ℕ)) :
    momentGram lam w N i j = packetMoment lam (fun j => (w j : ℂ)) ((j : ℕ) - (i : ℕ)) := by
  rw [packetMoment_ofReal]
  exact momentGram_apply_of_le lam w hlam hw N hij

/-- **The three-realization process law.**  One spectral packet carries an atomic-measure chart,
an analytic chart annihilated by `p(D)`, a state-space chart, and a rational transfer chart; the
same polynomial `p` governs the Hankel rank, the positive Gram profile and the withheld
response. -/
theorem three_realizations (lam : Fin r → ℂ) (w : Fin r → ℝ) (hlam : ∀ j, ‖lam j‖ = 1)
    (hinj : Function.Injective lam) (hw : ∀ j, 0 < w j) {N : ℕ} (hN : r ≤ N + 1) (n : ℕ) :
    (∫ x, x ^ n ∂(packetMeasure lam w) = packetMoment lam (fun j => (w j : ℂ)) n)
      ∧ iteratedDeriv n (packetFun lam fun j => (w j : ℂ)) 0
          = packetMoment lam (fun j => (w j : ℂ)) n
      ∧ (∀ t : ℂ, ∑ k ∈ Finset.range (r + 1), (spectrumPoly lam).coeff k
          * iteratedDeriv k (packetFun lam fun j => (w j : ℂ)) t = 0)
      ∧ packetMoment lam (fun j => (w j : ℂ)) n
          = (fun j => (w j : ℂ)) ⬝ᵥ ((Matrix.diagonal lam ^ n).mulVec fun _ => 1)
      ∧ (∀ z : ℂ, ‖z‖ < 1 →
          ∑' k : ℕ, packetMoment lam (fun j => (w j : ℂ)) k * z ^ k
            = ∑ j, (w j : ℂ) / (1 - lam j * z))
      ∧ (packetHankel lam (fun j => (w j : ℂ)) N).rank = r
      ∧ (momentGram lam w N).rank = min (N + 1) r
      ∧ packetMoment lam (fun j => (w j : ℂ)) (2 * r)
          = -∑ k ∈ Finset.range r, (spectrumPoly lam).coeff k
              * packetMoment lam (fun j => (w j : ℂ)) (r + k) := by
  refine ⟨integral_packetMeasure lam w (fun j => (hw j).le) n,
    iteratedDeriv_packetFun_zero lam _ n, fun t => packet_ODE lam _ t,
    packetMoment_eq_operator lam _ n, fun z hz => ?_,
    rank_packetHankel_of_le lam _ hinj (fun j => ?_) hN,
    rank_momentGram lam w hinj hw N, packet_withheld_prediction lam _⟩
  · refine tsum_packetMoment_mul_pow lam _ fun j => ?_
    rw [norm_mul, hlam j, one_mul]
    exact hz
  · simpa using ne_of_gt (hw j)

end SpectralPacket

end GaloisForLFunctions.HTGeometry
