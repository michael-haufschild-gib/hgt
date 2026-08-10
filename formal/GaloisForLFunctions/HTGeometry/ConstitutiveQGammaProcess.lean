import Mathlib
import GaloisForLFunctions.HTGeometry.QBinomialTheorem
import GaloisForLFunctions.HTGeometry.QGammaAnalytic
import GaloisForLFunctions.HTGeometry.QDigamma
import GaloisForLFunctions.HTGeometry.QGammaBellSubstitution
import GaloisForLFunctions.HTGeometry.ShiftEliminationEngine
import GaloisForLFunctions.HTGeometry.QShiftField
import GaloisForLFunctions.HTGeometry.QIncrement
import GaloisForLFunctions.HTGeometry.QIncrementAnalytic
import GaloisForLFunctions.HTGeometry.QTranscendence
import GaloisForLFunctions.HTGeometry.QShiftInverse
import GaloisForLFunctions.HTGeometry.ShiftEigenrelationEngine
import GaloisForLFunctions.HTGeometry.QDigammaHypertranscendental
import GaloisForLFunctions.HTGeometry.QGammaHypertranscendental
import GaloisForLFunctions.HTGeometry.ConstitutiveCyclicProcessFourShadow

/-!
# The q-Gamma process: positive atomic law and exponential response

Jackson's q-Gamma function is the moment-generating function of an explicit discrete probability
law.  With `w_n = (q;q)_∞ qⁿ/(q;q)_n` and `x_n = n log q − log(1−q)`,

`Γ_q(1+s) = ∑_n w_n e^{s x_n}`  for `Re s > −1`,

which is the q-binomial theorem after the normalisation `Γ_q(z) = (1−q)^{1−z}(q;q)_∞/(qᶻ;q)_∞`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- **Equation (2).**  The atomic support points `x_n = n log q − log(1−q)`. -/
def qGammaAtom (q : RealEulerNome) (n : ℕ) : ℝ :=
  n * Real.log q.val - Real.log (1 - q.val)

/-- The half-plane point `1 + s` carrying the q-Gamma response. -/
def qGammaShiftPoint (q : RealEulerNome) (s : ℂ) (hs : -1 < s.re) : EulerQGammaPoint where
  q := q
  z := 1 + s
  re_pos := by
    have : (1 + s).re = 1 + s.re := by simp
    rw [this]
    linarith

/-- **The q-Gamma response** `F_q(s) = Γ_q(1+s)`. -/
def qGammaResponse (q : RealEulerNome) (s : ℂ) (hs : -1 < s.re) : ℂ :=
  qGamma (qGammaShiftPoint q s hs)

theorem cpow_ofReal_pos {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ z = Complex.exp (z * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.ofReal_log hx.le]
  ring_nf

/-- The complex infinite q-Pochhammer symbol at the nome is the real q-factorial. -/
theorem qPochhammerInf_eq_realQFactorialInf (q : RealEulerNome) :
    qPochhammerInf (q.val : ℂ) q.toEulerNome = ((realQFactorialInf q : ℝ) : ℂ) := by
  have hreal : HasProd (fun j : ℕ => (1 - q.val ^ (j + 1))) (realQFactorialInf q) :=
    (realQFactorial_multipliable q).hasProd
  have hmap : HasProd (fun j : ℕ => ((1 - q.val ^ (j + 1) : ℝ) : ℂ))
      ((realQFactorialInf q : ℝ) : ℂ) := by
    have hcomp := hreal.map (Complex.ofRealHom : ℝ →+* ℂ) Complex.continuous_ofReal
    refine hcomp.congr_fun fun j => ?_
    simp
  have hfun : (fun j : ℕ => ((1 - q.val ^ (j + 1) : ℝ) : ℂ))
      = fun j : ℕ => (1 - (q.val : ℂ) * (q.val : ℂ) ^ j) := by
    funext j
    push_cast
    ring
  rw [hfun] at hmap
  rw [qPochhammerInf, RealEulerNome.toEulerNome_coe]
  exact hmap.tprod_eq

/-- **Theorem 1.1, equation (3).**  The q-Gamma response is the exponential moment transform of the
positive atomic law `μ_q`. -/
theorem qGammaResponse_hasSum (q : RealEulerNome) {s : ℂ} (hs : -1 < s.re) :
    HasSum (fun n : ℕ => ((qGammaWeight q n : ℝ) : ℂ)
        * Complex.exp (s * ((qGammaAtom q n : ℝ) : ℂ)))
      (qGammaResponse q s hs) := by
  set x := qGammaShiftPoint q s hs with hx
  have hz : x.z = 1 + s := rfl
  have hq : x.q = q := rfl
  set a : ℂ := (q.val : ℂ) ^ (1 + s) with hadef
  have ha : ‖a‖ < 1 := by
    have := x.denominatorDatum.a_norm_lt_one
    rw [EulerQGammaPoint.denominatorDatum] at this
    simpa [hz, hq, hadef] using this
  have hbin := qBinomial_hasSum q ha
  set K : ℂ := ((1 - q.val : ℝ) : ℂ) ^ (1 - (1 + s)) * ((realQFactorialInf q : ℝ) : ℂ) with hK
  have hval : K * (qPochhammerInf a q.toEulerNome)⁻¹ = qGammaResponse q s hs := by
    rw [qGammaResponse, qGamma, qGammaCore, hK, hz, hq,
      qPochhammerInf_eq_realQFactorialInf q]
    rw [div_eq_mul_inv]
    ring
  rw [← hval]
  refine (hbin.mul_left K).congr_fun fun n => ?_
  -- termwise identification
  have hqpos : (0 : ℝ) < q.val := q.pos
  have h1q : (0 : ℝ) < 1 - q.val := sub_pos.mpr q.lt_one
  have hfac : ((realQFactorial q n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (realQFactorial_pos q n).ne'
  have hapow : a ^ n = ((q.val ^ n : ℝ) : ℂ) * Complex.exp (s * (n : ℂ) * (Real.log q.val : ℂ)) := by
    rw [hadef, cpow_ofReal_pos hqpos, ← Complex.exp_nat_mul]
    rw [show ((q.val ^ n : ℝ) : ℂ) = Complex.exp ((n : ℂ) * (Real.log q.val : ℂ)) by
      rw [← cpow_ofReal_pos hqpos, Complex.cpow_natCast]
      push_cast
      ring]
    rw [← Complex.exp_add]
    congr 1
    ring
  have hnorm : ((1 - q.val : ℝ) : ℂ) ^ (1 - (1 + s))
      = Complex.exp (-(s * (Real.log (1 - q.val) : ℂ))) := by
    rw [cpow_ofReal_pos h1q]
    congr 1
    ring
  have hexp : Complex.exp (s * ((qGammaAtom q n : ℝ) : ℂ))
      = Complex.exp (s * (n : ℂ) * (Real.log q.val : ℂ))
        * Complex.exp (-(s * (Real.log (1 - q.val) : ℂ))) := by
    rw [← Complex.exp_add, qGammaAtom]
    congr 1
    push_cast
    ring
  rw [qBinomialTerm, hK, hapow, hnorm, hexp, qGammaWeight, qGeometricCoefficient]
  push_cast
  field_simp

/-! ## §2 — the positive kernel and the GNS realization -/

theorem qGammaWeight_pos (q : RealEulerNome) (n : ℕ) : 0 < qGammaWeight q n := by
  rw [qGammaWeight, qGeometricCoefficient]
  exact mul_pos (realQFactorialInf_pos q) (div_pos (pow_pos q.pos n) (realQFactorial_pos q n))

/-- **The geometric weight bound** `0 < w_n ≤ qⁿ`. -/
theorem qGammaWeight_le_pow (q : RealEulerNome) (n : ℕ) : qGammaWeight q n ≤ q.val ^ n := by
  rw [qGammaWeight, qGeometricCoefficient, mul_div_assoc']
  rw [div_le_iff₀ (realQFactorial_pos q n)]
  have hle : realQFactorialInf q ≤ realQFactorial q n := realQFactorialInf_le q n
  nlinarith [pow_pos q.pos n, realQFactorial_pos q n]

theorem qGammaWeight_summable (q : RealEulerNome) : Summable (qGammaWeight q) :=
  (qGammaWeight_hasSum_one q).summable

/-- The GNS Hilbert space of the q-Gamma law. -/
abbrev QGammaSpace : Type := lp (fun _ : ℕ => ℂ) 2

theorem qGammaSqrt_memℓp (q : RealEulerNome) (φ : ℕ → ℂ) (hφ : ∀ n, ‖φ n‖ = 1) :
    Memℓp (fun n => φ n * ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ)) 2 := by
  refine memℓp_gen ?_
  have hfun : (fun n : ℕ => ‖φ n * ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ)‖ ^ (2 : ENNReal).toReal)
      = qGammaWeight q := by
    funext n
    rw [norm_mul, hφ n, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sq_sqrt (qGammaWeight_pos q n).le]
  rw [hfun]
  exact qGammaWeight_summable q

theorem qGammaSqrt_memℓp' (q : RealEulerNome) :
    Memℓp (fun n : ℕ => ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ)) 2 := by
  have h := qGammaSqrt_memℓp q (fun _ => 1) (fun _ => by simp)
  simpa using h

/-- **The GNS cyclic vector** `Ω = (√w_n)`. -/
def qOmega (q : RealEulerNome) : QGammaSpace :=
  ⟨fun n => ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ), qGammaSqrt_memℓp' q⟩

/-- **The unitary orbit vector** `U_t Ω`. -/
def qOrbit (q : RealEulerNome) (t : ℝ) : QGammaSpace :=
  ⟨fun n => Complex.exp (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ))
      * ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ),
    qGammaSqrt_memℓp q _ (fun n => by
      rw [Complex.norm_exp]
      have : (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.mul_im]
      rw [this, Real.exp_zero])⟩

@[simp] theorem qOrbit_apply (q : RealEulerNome) (t : ℝ) (n : ℕ) :
    (qOrbit q t : ℕ → ℂ) n
      = Complex.exp (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ))
        * ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ) := rfl

@[simp] theorem qOmega_apply (q : RealEulerNome) (n : ℕ) :
    (qOmega q : ℕ → ℂ) n = ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ) := rfl

/-- **Equation (7).**  The characteristic response `C_q(t) = F_q(it)`. -/
def qChar (q : RealEulerNome) (t : ℝ) : ℂ :=
  qGammaResponse q (Complex.I * (t : ℂ)) (by simp)

theorem qChar_hasSum (q : RealEulerNome) (t : ℝ) :
    HasSum (fun n : ℕ => ((qGammaWeight q n : ℝ) : ℂ)
        * Complex.exp (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ))) (qChar q t) := by
  have := qGammaResponse_hasSum q (s := Complex.I * (t : ℂ)) (by simp)
  exact this

/-- **Equation (10), orbit form.**  The GNS inner product of two orbit vectors is the
characteristic response at the time difference. -/
theorem inner_qOrbit (q : RealEulerNome) (s t : ℝ) :
    (inner ℂ (qOrbit q s) (qOrbit q t) : ℂ) = qChar q (t - s) := by
  rw [lp.inner_eq_tsum, ← (qChar_hasSum q (t - s)).tsum_eq]
  refine tsum_congr fun n => ?_
  rw [RCLike.inner_apply, qOrbit_apply, qOrbit_apply]
  have hphase : (starRingEnd ℂ) (Complex.exp (Complex.I * (s : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)))
      = Complex.exp (-(Complex.I * (s : ℂ) * ((qGammaAtom q n : ℝ) : ℂ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp
  have hsqrt : ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ)
      * ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ) = ((qGammaWeight q n : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (qGammaWeight_pos q n).le]
  rw [map_mul, hphase, Complex.conj_ofReal]
  have hexp : Complex.exp (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ))
      * Complex.exp (-(Complex.I * (s : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)))
      = Complex.exp (Complex.I * ((t - s : ℝ) : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [← hsqrt, ← hexp]
  ring

/-- **Equation (10).**  The characteristic response is the GNS matrix element of the unitary
group in the cyclic vector. -/
theorem qChar_eq_inner (q : RealEulerNome) (t : ℝ) :
    qChar q t = (inner ℂ (qOmega q) (qOrbit q t) : ℂ) := by
  have h := inner_qOrbit q 0 t
  rw [sub_zero] at h
  rw [← h]
  congr 1
  refine lp.ext ?_
  funext n
  rw [qOrbit_apply, qOmega_apply]
  simp

/-- **Equation (11).**  The translation kernel is positive definite: the quadratic form is the
squared norm of the corresponding orbit combination. -/
theorem qChar_kernel_eq_normSq (q : RealEulerNome) {m : ℕ} (c : Fin m → ℂ) (t : Fin m → ℝ) :
    ∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * qChar q (t j - t i)
      = ((‖∑ j, c j • qOrbit q (t j)‖ : ℝ) : ℂ) ^ 2 := by
  have hnorm : ((‖∑ j, c j • qOrbit q (t j)‖ : ℝ) : ℂ) ^ 2
      = (inner ℂ (∑ i, c i • qOrbit q (t i)) (∑ j, c j • qOrbit q (t j)) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    rfl
  rw [hnorm, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_smul_right, inner_qOrbit]
  ring

theorem qChar_kernel_nonneg (q : RealEulerNome) {m : ℕ} (c : Fin m → ℂ) (t : Fin m → ℝ) :
    0 ≤ (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * qChar q (t j - t i)).re := by
  rw [qChar_kernel_eq_normSq]
  have : (((‖∑ j, c j • qOrbit q (t j)‖ : ℝ) : ℂ) ^ 2).re
      = ‖∑ j, c j • qOrbit q (t j)‖ ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  rw [this]
  positivity

/-! ### Moments of the atomic law -/

theorem summable_succ_pow_mul_geometric_real {r : ℝ} (hr0 : 0 < r) (hr : r < 1) (k : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * r ^ n) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k (r := r)
    (by rw [Real.norm_eq_abs, abs_of_pos hr0]; exact hr)
  have hshift : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * r ^ (n + 1)) := by
    have hh := (summable_nat_add_iff 1).mpr h
    refine hh.congr fun n => ?_
    push_cast
    ring
  have hmul := hshift.mul_left r⁻¹
  refine hmul.congr fun n => ?_
  rw [pow_succ]
  field_simp

theorem abs_qGammaAtom_le (q : RealEulerNome) (n : ℕ) :
    |qGammaAtom q n| ≤ ((n : ℝ) + 1) * (|Real.log q.val| + |Real.log (1 - q.val)|) := by
  rw [qGammaAtom]
  refine le_trans (abs_sub _ _) ?_
  rw [abs_mul, Nat.abs_cast]
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 := abs_nonneg (Real.log q.val)
  have h2 := abs_nonneg (Real.log (1 - q.val))
  nlinarith

/-- Every polynomial moment of the atomic law converges. -/
theorem qMomentTerm_summable (q : RealEulerNome) (k : ℕ) :
    Summable (fun n : ℕ => qGammaWeight q n * qGammaAtom q n ^ k) := by
  set C : ℝ := |Real.log q.val| + |Real.log (1 - q.val)| with hC
  have hC0 : 0 ≤ C := by positivity
  refine Summable.of_norm_bounded (g := fun n : ℕ => C ^ k * (((n : ℝ) + 1) ^ k * q.val ^ n)) ?_ ?_
  · exact (summable_succ_pow_mul_geometric_real q.pos q.lt_one k).mul_left (C ^ k)
  · intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (qGammaWeight_pos q n), abs_pow]
    have hx : |qGammaAtom q n| ^ k ≤ (((n : ℝ) + 1) * C) ^ k :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_qGammaAtom_le q n) k
    have hw : qGammaWeight q n ≤ q.val ^ n := qGammaWeight_le_pow q n
    calc qGammaWeight q n * |qGammaAtom q n| ^ k
        ≤ q.val ^ n * (((n : ℝ) + 1) * C) ^ k := by
          refine mul_le_mul hw hx (by positivity) (pow_nonneg q.pos.le n)
      _ = C ^ k * (((n : ℝ) + 1) ^ k * q.val ^ n) := by
          rw [mul_pow]
          ring

/-- The `k`-th moment of the atomic law. -/
def qMoment (q : RealEulerNome) (k : ℕ) : ℝ :=
  ∑' n : ℕ, qGammaWeight q n * qGammaAtom q n ^ k

theorem qMoment_hasSum (q : RealEulerNome) (k : ℕ) :
    HasSum (fun n : ℕ => qGammaWeight q n * qGammaAtom q n ^ k) (qMoment q k) :=
  (qMomentTerm_summable q k).hasSum

theorem qGammaAtom_injective (q : RealEulerNome) : Function.Injective (qGammaAtom q) := by
  intro a b hab
  rw [qGammaAtom, qGammaAtom] at hab
  have hlog : Real.log q.val ≠ 0 := ne_of_lt (Real.log_neg q.pos q.lt_one)
  have hmul : (a : ℝ) * Real.log q.val = (b : ℝ) * Real.log q.val := by linarith
  exact_mod_cast mul_right_cancel₀ hlog hmul

/-- **Equation (12).**  The moment matrix `M_N = (m_{i+j})`. -/
def qMomentMatrix (q : RealEulerNome) (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ :=
  Matrix.of fun i j => qMoment q ((i : ℕ) + (j : ℕ))

/-- **Equation (13).**  The moment quadratic form is the mean square of the evaluated
polynomial. -/
theorem qMomentMatrix_hasSum (q : RealEulerNome) (N : ℕ) (c : Fin (N + 1) → ℝ) :
    HasSum (fun n : ℕ => qGammaWeight q n * (∑ j, c j * qGammaAtom q n ^ (j : ℕ)) ^ 2)
      (∑ i, ∑ j, c i * (qMomentMatrix q N i j * c j)) := by
  have hbase : HasSum (fun n : ℕ =>
      ∑ i, ∑ j, c i * c j * (qGammaWeight q n * qGammaAtom q n ^ ((i : ℕ) + (j : ℕ))))
      (∑ i, ∑ j, c i * c j * qMoment q ((i : ℕ) + (j : ℕ))) :=
    hasSum_sum fun i _ => hasSum_sum fun j _ =>
      (qMoment_hasSum q ((i : ℕ) + (j : ℕ))).mul_left _
  have hval : (∑ i, ∑ j, c i * c j * qMoment q ((i : ℕ) + (j : ℕ)))
      = ∑ i, ∑ j, c i * (qMomentMatrix q N i j * c j) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    show _ = c i * (qMoment q ((i : ℕ) + (j : ℕ)) * c j)
    ring
  rw [hval] at hbase
  refine hbase.congr_fun fun n => ?_
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add]
  ring

theorem qMomentMatrix_quadratic (q : RealEulerNome) (N : ℕ) (c : Fin (N + 1) → ℝ) :
    ∑ i, ∑ j, c i * (qMomentMatrix q N i j * c j)
      = ∑' n : ℕ, qGammaWeight q n * (∑ j, c j * qGammaAtom q n ^ (j : ℕ)) ^ 2 :=
  (qMomentMatrix_hasSum q N c).tsum_eq.symm

theorem qMomentMatrix_isHermitian (q : RealEulerNome) (N : ℕ) :
    (qMomentMatrix q N).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  show qMoment q ((j : ℕ) + (i : ℕ)) = qMoment q ((i : ℕ) + (j : ℕ))
  rw [Nat.add_comm]

/-- The evaluation polynomial of a coefficient vector. -/
noncomputable def qEvalPoly {N : ℕ} (c : Fin (N + 1) → ℝ) : Polynomial ℝ :=
  ∑ j : Fin (N + 1), Polynomial.C (c j) * Polynomial.X ^ (j : ℕ)

theorem qEvalPoly_eval {N : ℕ} (c : Fin (N + 1) → ℝ) (x : ℝ) :
    (qEvalPoly c).eval x = ∑ j, c j * x ^ (j : ℕ) := by
  rw [qEvalPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem coeff_qEvalPoly {N : ℕ} (c : Fin (N + 1) → ℝ) (j : Fin (N + 1)) :
    (qEvalPoly c).coeff (j : ℕ) = c j := by
  rw [qEvalPoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro k _ hk
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h => hk (Fin.ext h.symm)), mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

theorem qEvalPoly_ne_zero {N : ℕ} {c : Fin (N + 1) → ℝ} (hc : c ≠ 0) : qEvalPoly c ≠ 0 := by
  intro h0
  apply hc
  funext j
  have := coeff_qEvalPoly c j
  rw [h0] at this
  simpa using this.symm

/-- **Equation (13).**  The moment matrices of the q-Gamma law are positive definite. -/
theorem qMomentMatrix_posDef (q : RealEulerNome) (N : ℕ) : (qMomentMatrix q N).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨qMomentMatrix_isHermitian q N, fun c hc => ?_⟩
  have hquad : (star c) ⬝ᵥ (qMomentMatrix q N).mulVec c
      = ∑ i, ∑ j, c i * (qMomentMatrix q N i j * c j) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    show star (c i) * ((qMomentMatrix q N).mulVec c i) = _
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [star_trivial]
  have hsum := qMomentMatrix_hasSum q N c
  rw [hquad, ← hsum.tsum_eq]
  have hpoly : qEvalPoly c ≠ 0 := qEvalPoly_ne_zero hc
  have hex : ∃ n : ℕ, (qEvalPoly c).eval (qGammaAtom q n) ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hpoly (Polynomial.eq_zero_of_infinite_isRoot _
      (Set.infinite_of_injective_forall_mem (qGammaAtom_injective q) fun n => hall n))
  obtain ⟨n₀, hn₀⟩ := hex
  have hnonneg : ∀ n : ℕ, 0 ≤ qGammaWeight q n * (∑ j, c j * qGammaAtom q n ^ (j : ℕ)) ^ 2 :=
    fun n => mul_nonneg (qGammaWeight_pos q n).le (sq_nonneg _)
  have hterm : 0 < qGammaWeight q n₀ * (∑ j, c j * qGammaAtom q n₀ ^ (j : ℕ)) ^ 2 := by
    refine mul_pos (qGammaWeight_pos q n₀) ?_
    have hne : (∑ j, c j * qGammaAtom q n₀ ^ (j : ℕ)) ≠ 0 := by
      rw [← qEvalPoly_eval c]
      exact hn₀
    positivity
  calc (0 : ℝ) < qGammaWeight q n₀ * (∑ j, c j * qGammaAtom q n₀ ^ (j : ℕ)) ^ 2 := hterm
    _ ≤ ∑' n : ℕ, qGammaWeight q n * (∑ j, c j * qGammaAtom q n ^ (j : ℕ)) ^ 2 :=
        Summable.le_tsum hsum.summable n₀ fun m _ => hnonneg m

/-! ## §5 — the exponential tilt -/

theorem EulerQGammaPoint.eq_of {x y : EulerQGammaPoint} (hq : x.q = y.q) (hz : x.z = y.z) :
    x = y := by
  cases x
  cases y
  simp_all

/-- **Equation (21).**  The exponentially tilted weights `w̃_n = e^{x_n} w_n`. -/
def qTiltWeight (q : RealEulerNome) (n : ℕ) : ℝ :=
  Real.exp (qGammaAtom q n) * qGammaWeight q n

theorem qTiltWeight_pos (q : RealEulerNome) (n : ℕ) : 0 < qTiltWeight q n :=
  mul_pos (Real.exp_pos _) (qGammaWeight_pos q n)

/-- **Equation (24).**  The atom is the log-likelihood ratio of the tilt. -/
theorem log_qTiltWeight_div (q : RealEulerNome) (n : ℕ) :
    Real.log (qTiltWeight q n / qGammaWeight q n) = qGammaAtom q n := by
  rw [qTiltWeight, mul_div_assoc, div_self (qGammaWeight_pos q n).ne', mul_one, Real.log_exp]

theorem qGammaResponse_one (q : RealEulerNome) :
    qGammaResponse q 1 (by norm_num) = 1 := by
  have h : qGammaShiftPoint q 1 (by norm_num) = (EulerQGammaPoint.one q).shift :=
    EulerQGammaPoint.eq_of rfl rfl
  rw [qGammaResponse, h, qGamma_two]

/-- **Equation (21).**  The tilted weights again form a probability law, because `Γ_q(2) = 1`. -/
theorem qTiltWeight_hasSum_one (q : RealEulerNome) : HasSum (qTiltWeight q) 1 := by
  have h := qGammaResponse_hasSum q (s := (1 : ℂ)) (by norm_num)
  rw [qGammaResponse_one q] at h
  have hreal : HasSum (fun n : ℕ => ((qTiltWeight q n : ℝ) : ℂ)) ((1 : ℝ) : ℂ) := by
    rw [Complex.ofReal_one]
    refine h.congr_fun fun n => ?_
    rw [qTiltWeight]
    push_cast
    rw [one_mul, ← Complex.ofReal_exp]
    ring
  exact Complex.hasSum_ofReal.mp hreal

/-- **Equation (22).**  The tilted characteristic response is the shifted q-Gamma response. -/
theorem qTilt_hasSum (q : RealEulerNome) (t : ℝ) :
    HasSum (fun n : ℕ => ((qTiltWeight q n : ℝ) : ℂ)
        * Complex.exp (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)))
      (qGammaResponse q (1 + Complex.I * (t : ℂ)) (by simp)) := by
  have h := qGammaResponse_hasSum q (s := 1 + Complex.I * (t : ℂ)) (by simp)
  refine h.congr_fun fun n => ?_
  rw [qTiltWeight]
  push_cast
  rw [← Complex.ofReal_exp]
  rw [show ((1 : ℂ) + Complex.I * (t : ℂ)) * ((qGammaAtom q n : ℝ) : ℂ)
      = ((qGammaAtom q n : ℝ) : ℂ) + Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ) by ring]
  rw [Complex.exp_add]
  push_cast
  ring

/-- **Equation (23).**  Jackson's functional equation forces the tilted response. -/
theorem qTilt_response_eq (q : RealEulerNome) (t : ℝ) :
    qGammaResponse q (1 + Complex.I * (t : ℂ)) (by simp)
      = ((1 - (q.val : ℂ) ^ (1 + Complex.I * (t : ℂ))) / ((1 - q.val : ℝ) : ℂ)) * qChar q t := by
  have hpt : qGammaShiftPoint q (1 + Complex.I * (t : ℂ)) (by simp)
      = (qGammaShiftPoint q (Complex.I * (t : ℂ)) (by simp)).shift :=
    EulerQGammaPoint.eq_of rfl (by
      show (1 : ℂ) + (1 + Complex.I * (t : ℂ)) = (1 + Complex.I * (t : ℂ)) + 1
      ring)
  rw [qGammaResponse, hpt, qGamma_shift]
  rfl

/-! ## §3 — recurrent observation and the open marked lift -/

theorem norm_sq_lp (v : QGammaSpace) : ‖v‖ ^ 2 = ∑' n : ℕ, ‖(v : ℕ → ℂ) n‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (f := v) (by norm_num)
  rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
  rw [h]
  refine tsum_congr fun n => ?_
  rw [Real.rpow_natCast]

theorem qOrbit_sub_qOmega_apply (q : RealEulerNome) (t : ℝ) (n : ℕ) :
    ((qOrbit q t - qOmega q : QGammaSpace) : ℕ → ℂ) n
      = (Complex.exp (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)) - 1)
        * ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ) := by
  rw [lp.coeFn_sub]
  show (qOrbit q t : ℕ → ℂ) n - (qOmega q : ℕ → ℂ) n = _
  rw [qOrbit_apply, qOmega_apply]
  ring

theorem norm_qOrbit_sub_qOmega_sq (q : RealEulerNome) (t : ℝ) :
    ‖qOrbit q t - qOmega q‖ ^ 2
      = ∑' n : ℕ, qGammaWeight q n
        * ‖Complex.exp (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)) - 1‖ ^ 2 := by
  rw [norm_sq_lp]
  refine tsum_congr fun n => ?_
  rw [qOrbit_sub_qOmega_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (qGammaWeight_pos q n).le]
  ring

theorem norm_qPhase (q : RealEulerNome) (t : ℝ) (n : ℕ) :
    ‖Complex.exp (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero]

theorem qOrbitDiff_le_four (q : RealEulerNome) (t : ℝ) (n : ℕ) :
    ‖Complex.exp (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)) - 1‖ ^ 2 ≤ 4 := by
  have hb : ‖Complex.exp (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)) - 1‖ ≤ 2 := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [norm_qPhase, norm_one]
    norm_num
  nlinarith [norm_nonneg (Complex.exp (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)) - 1)]

theorem qOrbitDiff_summable (q : RealEulerNome) (t : ℝ) :
    Summable (fun n : ℕ => qGammaWeight q n
      * ‖Complex.exp (Complex.I * (t : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)) - 1‖ ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun n => mul_nonneg (qGammaWeight_pos q n).le (sq_nonneg _)) (fun n => ?_)
    ((qGammaWeight_summable q).mul_left 4)
  have h4 := qOrbitDiff_le_four q t n
  have hw := (qGammaWeight_pos q n).le
  nlinarith

/-- **Equation (15).**  The observer recurs: at arbitrarily late integer times the orbit vector
returns to the cyclic vector. -/
theorem exists_qOrbit_near_qOmega (q : RealEulerNome) {ε : ℝ} (hε : 0 < ε) (M : ℕ) :
    ∃ m : ℕ, M ≤ m ∧ ‖qOrbit q (m : ℝ) - qOmega q‖ < ε := by
  classical
  have hsum := qGammaWeight_hasSum_one q
  have hsummable := qGammaWeight_summable q
  have htail : Filter.Tendsto (fun N : ℕ => ∑' n : ℕ, qGammaWeight q (n + N)) Filter.atTop
      (𝓝 0) := tendsto_sum_nat_add (qGammaWeight q)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∑' n : ℕ, qGammaWeight q (n + (N + 1)) < ε ^ 2 / 8 := by
    have hpos : (0 : ℝ) < ε ^ 2 / 8 := by positivity
    obtain ⟨i₀, hi₀⟩ := Filter.eventually_atTop.mp (htail.eventually (gt_mem_nhds hpos))
    exact ⟨i₀, hi₀ (i₀ + 1) (by omega)⟩
  set g : Fin (N + 1) → Circle := fun i => Circle.exp (qGammaAtom q (i : ℕ)) with hg
  set s : Set Circle := {c : Circle | ‖(c : ℂ) - 1‖ < ε / 2} with hs
  have hsopen : IsOpen s := by
    have hcont : Continuous fun c : Circle => ‖(c : ℂ) - 1‖ := by fun_prop
    exact isOpen_lt hcont continuous_const
  have hsmem : s ∈ 𝓝 (1 : Circle) := by
    refine hsopen.mem_nhds ?_
    show ‖((1 : Circle) : ℂ) - 1‖ < ε / 2
    simp
    linarith
  have hU : Set.pi Set.univ (fun _ : Fin (N + 1) => s) ∈ 𝓝 (1 : Fin (N + 1) → Circle) :=
    set_pi_mem_nhds Set.finite_univ fun i _ => hsmem
  obtain ⟨m, hm, hmem⟩ := exists_pow_mem_of_compactSpace g hU M
  refine ⟨m, hm, ?_⟩
  have hhead : ∀ n : ℕ, ∀ hn : n < N + 1,
      ‖Complex.exp (Complex.I * ((m : ℝ) : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)) - 1‖ < ε / 2 := by
    intro n hn
    have hj : (g ^ m) ⟨n, hn⟩ ∈ s := hmem ⟨n, hn⟩ (Set.mem_univ _)
    rw [hs, Set.mem_setOf_eq] at hj
    have hval : (((g ^ m) ⟨n, hn⟩ : Circle) : ℂ)
        = Complex.exp (Complex.I * ((m : ℝ) : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)) := by
      show (((g ⟨n, hn⟩) ^ m : Circle) : ℂ) = _
      rw [Circle.coe_pow, hg]
      simp only [Circle.coe_exp]
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rwa [hval] at hj
  have hnormsq : ‖qOrbit q (m : ℝ) - qOmega q‖ ^ 2 < ε ^ 2 := by
    rw [norm_qOrbit_sub_qOmega_sq]
    have hsplit := (qOrbitDiff_summable q (m : ℝ)).sum_add_tsum_nat_add (N + 1)
    rw [← hsplit]
    have hhead_bound : ∑ i ∈ Finset.range (N + 1), qGammaWeight q i
        * ‖Complex.exp (Complex.I * ((m : ℝ) : ℂ) * ((qGammaAtom q i : ℝ) : ℂ)) - 1‖ ^ 2
        ≤ (ε / 2) ^ 2 := by
      have hle : ∀ i ∈ Finset.range (N + 1), qGammaWeight q i
          * ‖Complex.exp (Complex.I * ((m : ℝ) : ℂ) * ((qGammaAtom q i : ℝ) : ℂ)) - 1‖ ^ 2
          ≤ qGammaWeight q i * (ε / 2) ^ 2 := by
        intro i hi
        have hilt : i < N + 1 := Finset.mem_range.mp hi
        have hb := hhead i hilt
        have hnn := norm_nonneg
          (Complex.exp (Complex.I * ((m : ℝ) : ℂ) * ((qGammaAtom q i : ℝ) : ℂ)) - 1)
        have hw := (qGammaWeight_pos q i).le
        have hsq : ‖Complex.exp (Complex.I * ((m : ℝ) : ℂ) * ((qGammaAtom q i : ℝ) : ℂ)) - 1‖ ^ 2
            ≤ (ε / 2) ^ 2 := by nlinarith
        exact mul_le_mul_of_nonneg_left hsq hw
      refine le_trans (Finset.sum_le_sum hle) ?_
      rw [← Finset.sum_mul]
      have hmass : ∑ i ∈ Finset.range (N + 1), qGammaWeight q i ≤ 1 :=
        sum_le_hasSum _ (fun i _ => (qGammaWeight_pos q i).le) hsum
      nlinarith [sq_nonneg (ε / 2)]
    have htail_bound : ∑' i : ℕ, qGammaWeight q (i + (N + 1))
        * ‖Complex.exp (Complex.I * ((m : ℝ) : ℂ)
          * ((qGammaAtom q (i + (N + 1)) : ℝ) : ℂ)) - 1‖ ^ 2
        ≤ 4 * ∑' i : ℕ, qGammaWeight q (i + (N + 1)) := by
      rw [← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun i => ?_) ?_ ?_
      · have h4 := qOrbitDiff_le_four q (m : ℝ) (i + (N + 1))
        have hw := (qGammaWeight_pos q (i + (N + 1))).le
        nlinarith
      · exact ((qOrbitDiff_summable q (m : ℝ)).comp_injective
          (add_left_injective (N + 1)))
      · exact (hsummable.comp_injective (add_left_injective (N + 1))).mul_left 4
    rw [show (ε / 2) ^ 2 = ε ^ 2 / 4 by ring] at hhead_bound
    have hεsq : 0 < ε ^ 2 := by positivity
    linarith [hhead_bound, htail_bound, hN, hεsq]
  have hnn : 0 ≤ ‖qOrbit q (m : ℝ) - qOmega q‖ := norm_nonneg _
  nlinarith [hnormsq, hnn, hε]

/-- **Equation (16).**  The marked logarithmic lift `h(t) = t·XΩ`. -/
def qLift (q : RealEulerNome) (t : ℝ) : QGammaSpace :=
  ⟨fun n => ((t * qGammaAtom q n : ℝ) : ℂ) * ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ), by
    refine memℓp_gen ?_
    have hfun : (fun n : ℕ => ‖((t * qGammaAtom q n : ℝ) : ℂ)
        * ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ)‖ ^ (2 : ENNReal).toReal)
        = fun n : ℕ => t ^ 2 * (qGammaWeight q n * qGammaAtom q n ^ 2) := by
      funext n
      rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rw [mul_pow, sq_abs, Real.sq_sqrt (qGammaWeight_pos q n).le]
      ring
    rw [hfun]
    exact (qMomentTerm_summable q 2).mul_left _⟩

theorem norm_qLift_sq (q : RealEulerNome) (t : ℝ) :
    ‖qLift q t‖ ^ 2 = t ^ 2 * qMoment q 2 := by
  rw [norm_sq_lp, qMoment, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  show ‖((t * qGammaAtom q n : ℝ) : ℂ) * ((Real.sqrt (qGammaWeight q n) : ℝ) : ℂ)‖ ^ 2 = _
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, sq_abs,
    Real.sq_sqrt (qGammaWeight_pos q n).le]
  ring

theorem qMoment_two_pos (q : RealEulerNome) : 0 < qMoment q 2 := by
  have hne : ∃ n : ℕ, qGammaAtom q n ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    have h01 : (0 : ℕ) = 1 := qGammaAtom_injective q (by rw [hall 0, hall 1])
    exact absurd h01 (by norm_num)
  obtain ⟨n₀, hn₀⟩ := hne
  have hterm : 0 < qGammaWeight q n₀ * qGammaAtom q n₀ ^ 2 :=
    mul_pos (qGammaWeight_pos q n₀) (by positivity)
  calc (0 : ℝ) < qGammaWeight q n₀ * qGammaAtom q n₀ ^ 2 := hterm
    _ ≤ qMoment q 2 :=
        Summable.le_tsum (qMomentTerm_summable q 2) n₀ fun m _ =>
          mul_nonneg (qGammaWeight_pos q m).le (sq_nonneg _)

/-- **Equation (17).**  The marked lift escapes: its norm grows linearly in the time. -/
theorem norm_qLift_tendsto_atTop (q : RealEulerNome) :
    Filter.Tendsto (fun t : ℝ => ‖qLift q t‖) Filter.atTop Filter.atTop := by
  have hval : ∀ t : ℝ, 0 ≤ t → ‖qLift q t‖ = t * Real.sqrt (qMoment q 2) := by
    intro t ht
    have hsq := norm_qLift_sq q t
    have hnn : 0 ≤ ‖qLift q t‖ := norm_nonneg _
    have hrhs : 0 ≤ t * Real.sqrt (qMoment q 2) :=
      mul_nonneg ht (Real.sqrt_nonneg _)
    have hsq2 : ‖qLift q t‖ ^ 2 = (t * Real.sqrt (qMoment q 2)) ^ 2 := by
      rw [hsq, mul_pow, Real.sq_sqrt (qMoment_two_pos q).le]
    nlinarith [hsq2, hnn, hrhs]
  have hlin : Filter.Tendsto (fun t : ℝ => t * Real.sqrt (qMoment q 2)) Filter.atTop
      Filter.atTop :=
    Filter.Tendsto.atTop_mul_const (Real.sqrt_pos.mpr (qMoment_two_pos q)) Filter.tendsto_id
  refine hlin.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
  exact (hval t ht).symm

/-! ## §5, equation (25) — the response derivative and the entropy costs -/

theorem exp_smul_qGammaAtom (q : RealEulerNome) (σ : ℝ) (n : ℕ) :
    Real.exp (σ * qGammaAtom q n) = (q.val ^ σ) ^ n * (1 - q.val) ^ (-σ) := by
  have hq : (0 : ℝ) < q.val := q.pos
  have h1q : (0 : ℝ) < 1 - q.val := sub_pos.mpr q.lt_one
  have hA : Real.exp (σ * Real.log q.val) = q.val ^ σ := by
    rw [Real.rpow_def_of_pos hq, mul_comm]
  have hB : Real.exp (σ * Real.log (1 - q.val)) = (1 - q.val) ^ σ := by
    rw [Real.rpow_def_of_pos h1q, mul_comm]
  rw [qGammaAtom, mul_sub, Real.exp_sub]
  rw [show σ * ((n : ℝ) * Real.log q.val) = (n : ℝ) * (σ * Real.log q.val) by ring]
  rw [Real.exp_nat_mul, hA, hB, Real.rpow_neg h1q.le, div_eq_mul_inv]

/-- Every weighted exponential-tilt moment of the atomic law converges. -/
theorem qWeightExp_summable (q : RealEulerNome) {σ : ℝ} (hσ : -1 < σ) (k : ℕ) :
    Summable (fun n : ℕ =>
      qGammaWeight q n * |qGammaAtom q n| ^ k * Real.exp (σ * qGammaAtom q n)) := by
  have hq : (0 : ℝ) < q.val := q.pos
  have h1q : (0 : ℝ) < 1 - q.val := sub_pos.mpr q.lt_one
  set C₁ : ℝ := |Real.log q.val| + |Real.log (1 - q.val)| with hC₁
  set r : ℝ := q.val ^ (1 + σ) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hq _
  have hr1 : r < 1 := by
    rw [hr]
    exact Real.rpow_lt_one hq.le q.lt_one (by linarith)
  have hstep : ∀ n : ℕ, q.val ^ n * (q.val ^ σ) ^ n = r ^ n := by
    intro n
    rw [← mul_pow, hr]
    congr 1
    rw [Real.rpow_add hq, Real.rpow_one]
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (((summable_succ_pow_mul_geometric_real hr0 hr1 k).mul_left
      (C₁ ^ k * (1 - q.val) ^ (-σ))))
  · exact mul_nonneg (mul_nonneg (qGammaWeight_pos q n).le (by positivity)) (Real.exp_pos _).le
  · rw [exp_smul_qGammaAtom]
    have hw : qGammaWeight q n ≤ q.val ^ n := qGammaWeight_le_pow q n
    have hx : |qGammaAtom q n| ^ k ≤ (((n : ℝ) + 1) * C₁) ^ k :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_qGammaAtom_le q n) k
    have hpow : (0 : ℝ) < (q.val ^ σ) ^ n * (1 - q.val) ^ (-σ) := by
      have := Real.rpow_pos_of_pos hq σ
      have h2 := Real.rpow_pos_of_pos h1q (-σ)
      positivity
    calc qGammaWeight q n * |qGammaAtom q n| ^ k * ((q.val ^ σ) ^ n * (1 - q.val) ^ (-σ))
        ≤ q.val ^ n * (((n : ℝ) + 1) * C₁) ^ k * ((q.val ^ σ) ^ n * (1 - q.val) ^ (-σ)) := by
          refine mul_le_mul_of_nonneg_right ?_ hpow.le
          exact mul_le_mul hw hx (by positivity) (pow_nonneg hq.le n)
      _ = C₁ ^ k * (1 - q.val) ^ (-σ) * (((n : ℝ) + 1) ^ k * r ^ n) := by
          rw [mul_pow, ← hstep n]
          ring

/-- The response series as a function of the intervention parameter. -/
def qResponseFun (q : RealEulerNome) (s : ℂ) : ℂ :=
  ∑' n : ℕ, ((qGammaWeight q n : ℝ) : ℂ) * Complex.exp (s * ((qGammaAtom q n : ℝ) : ℂ))

theorem qResponseFun_eq (q : RealEulerNome) {s : ℂ} (hs : -1 < s.re) :
    qResponseFun q s = qGammaResponse q s hs :=
  (qGammaResponse_hasSum q hs).tsum_eq

/-- The open strip carrying both intervention points `0` and `1`. -/
def qStrip : Set ℂ := {s : ℂ | -(1 / 2 : ℝ) < s.re ∧ s.re < 2}

theorem isOpen_qStrip : IsOpen qStrip := by
  have h1 : IsOpen {s : ℂ | -(1 / 2 : ℝ) < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have h2 : IsOpen {s : ℂ | s.re < 2} := isOpen_lt Complex.continuous_re continuous_const
  exact h1.inter h2

theorem convex_qStrip : Convex ℝ qStrip := by
  have h1 : Convex ℝ {s : ℂ | -(1 / 2 : ℝ) < s.re} :=
    convex_halfSpace_re_gt _
  have h2 : Convex ℝ {s : ℂ | s.re < 2} := convex_halfSpace_re_lt _
  exact h1.inter h2

theorem norm_qResponseTerm_deriv_le (q : RealEulerNome) (n : ℕ) {s : ℂ} (hs : s ∈ qStrip) :
    ‖((qGammaWeight q n : ℝ) : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)
        * Complex.exp (s * ((qGammaAtom q n : ℝ) : ℂ))‖
      ≤ qGammaWeight q n * |qGammaAtom q n| ^ 1 * Real.exp (-(1 / 2 : ℝ) * qGammaAtom q n)
        + qGammaWeight q n * |qGammaAtom q n| ^ 1 * Real.exp (2 * qGammaAtom q n) := by
  have hnorm : ‖Complex.exp (s * ((qGammaAtom q n : ℝ) : ℂ))‖
      = Real.exp (s.re * qGammaAtom q n) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  rw [norm_mul, norm_mul, hnorm, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (qGammaWeight_pos q n), pow_one]
  rcases le_or_gt 0 (qGammaAtom q n) with hx | hx
  · have hle : Real.exp (s.re * qGammaAtom q n) ≤ Real.exp (2 * qGammaAtom q n) := by
      refine Real.exp_le_exp.mpr ?_
      exact mul_le_mul_of_nonneg_right (le_of_lt hs.2) hx
    have hpos : 0 ≤ qGammaWeight q n * |qGammaAtom q n| :=
      mul_nonneg (qGammaWeight_pos q n).le (abs_nonneg _)
    nlinarith [Real.exp_pos (-(1 / 2 : ℝ) * qGammaAtom q n),
      mul_nonneg hpos (Real.exp_pos (-(1 / 2 : ℝ) * qGammaAtom q n)).le]
  · have hle : Real.exp (s.re * qGammaAtom q n) ≤ Real.exp (-(1 / 2 : ℝ) * qGammaAtom q n) := by
      refine Real.exp_le_exp.mpr ?_
      have hneg : qGammaAtom q n < 0 := hx
      nlinarith [hs.1]
    have hpos : 0 ≤ qGammaWeight q n * |qGammaAtom q n| :=
      mul_nonneg (qGammaWeight_pos q n).le (abs_nonneg _)
    nlinarith [Real.exp_pos (2 * qGammaAtom q n),
      mul_nonneg hpos (Real.exp_pos (2 * qGammaAtom q n)).le]

/-- **The response series is differentiable, with the term-by-term derivative.** -/
theorem hasDerivAt_qResponseFun (q : RealEulerNome) {s : ℂ} (hs : s ∈ qStrip) :
    HasDerivAt (qResponseFun q)
      (∑' n : ℕ, ((qGammaWeight q n : ℝ) : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)
        * Complex.exp (s * ((qGammaAtom q n : ℝ) : ℂ))) s := by
  set u : ℕ → ℝ := fun n =>
    qGammaWeight q n * |qGammaAtom q n| ^ 1 * Real.exp (-(1 / 2 : ℝ) * qGammaAtom q n)
      + qGammaWeight q n * |qGammaAtom q n| ^ 1 * Real.exp (2 * qGammaAtom q n) with hu
  have hsummable : Summable u :=
    (qWeightExp_summable q (by norm_num : -1 < -(1 / 2 : ℝ)) 1).add
      (qWeightExp_summable q (by norm_num : -1 < (2 : ℝ)) 1)
  have hderiv : ∀ (n : ℕ) (y : ℂ), y ∈ qStrip →
      HasDerivAt (fun z : ℂ => ((qGammaWeight q n : ℝ) : ℂ)
          * Complex.exp (z * ((qGammaAtom q n : ℝ) : ℂ)))
        (((qGammaWeight q n : ℝ) : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)
          * Complex.exp (y * ((qGammaAtom q n : ℝ) : ℂ))) y := by
    intro n y _
    have hbase : HasDerivAt (fun z : ℂ => z * ((qGammaAtom q n : ℝ) : ℂ))
        ((qGammaAtom q n : ℝ) : ℂ) y := by
      simpa using (hasDerivAt_id y).mul_const ((qGammaAtom q n : ℝ) : ℂ)
    have hexp := hbase.cexp
    simpa [mul_comm, mul_assoc, mul_left_comm]
      using hexp.const_mul ((qGammaWeight q n : ℝ) : ℂ)
  have hzero : Summable fun n : ℕ => ((qGammaWeight q n : ℝ) : ℂ)
      * Complex.exp ((0 : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)) := by
    have := (qGammaResponse_hasSum q (s := (0 : ℂ)) (by norm_num)).summable
    exact this
  have h0 : (0 : ℂ) ∈ qStrip :=
    ⟨by simp only [Complex.zero_re]; norm_num, by simp only [Complex.zero_re]; norm_num⟩
  exact hasDerivAt_tsum_of_isPreconnected hsummable isOpen_qStrip
    (convex_qStrip.isPreconnected) hderiv
    (fun n y hy => norm_qResponseTerm_deriv_le q n hy) h0 hzero hs

theorem qWeightAtomExp_summable (q : RealEulerNome) {σ : ℝ} (hσ : -1 < σ) :
    Summable (fun n : ℕ =>
      qGammaWeight q n * qGammaAtom q n * Real.exp (σ * qGammaAtom q n)) := by
  refine Summable.of_abs ?_
  refine (qWeightExp_summable q hσ 1).congr fun n => ?_
  rw [abs_mul, abs_mul, abs_of_pos (qGammaWeight_pos q n), abs_of_pos (Real.exp_pos _), pow_one]

theorem qResponseDeriv_ofReal (q : RealEulerNome) {σ : ℝ} (hσ : -1 < σ) :
    ∑' n : ℕ, ((qGammaWeight q n : ℝ) : ℂ) * ((qGammaAtom q n : ℝ) : ℂ)
        * Complex.exp (((σ : ℝ) : ℂ) * ((qGammaAtom q n : ℝ) : ℂ))
      = ((∑' n : ℕ, qGammaWeight q n * qGammaAtom q n * Real.exp (σ * qGammaAtom q n) : ℝ) : ℂ) := by
  have hreal := (qWeightAtomExp_summable q hσ).hasSum
  have hmap : HasSum (fun n : ℕ =>
      ((qGammaWeight q n * qGammaAtom q n * Real.exp (σ * qGammaAtom q n) : ℝ) : ℂ))
      ((∑' n : ℕ, qGammaWeight q n * qGammaAtom q n * Real.exp (σ * qGammaAtom q n) : ℝ) : ℂ) :=
    Complex.hasSum_ofReal.mpr hreal
  refine (hmap.congr_fun fun n => ?_).tsum_eq
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_mul]

/-- **Equation (25), left.**  The relative entropy of the tilt against the base law. -/
def qKLTiltBase (q : RealEulerNome) : ℝ :=
  ∑' n : ℕ, qTiltWeight q n * Real.log (qTiltWeight q n / qGammaWeight q n)

/-- **Equation (25), right.**  The relative entropy of the base law against the tilt. -/
def qKLBaseTilt (q : RealEulerNome) : ℝ :=
  ∑' n : ℕ, qGammaWeight q n * Real.log (qGammaWeight q n / qTiltWeight q n)

theorem qKLTiltBase_eq (q : RealEulerNome) :
    qKLTiltBase q
      = ∑' n : ℕ, qGammaWeight q n * qGammaAtom q n * Real.exp (1 * qGammaAtom q n) := by
  rw [qKLTiltBase]
  refine tsum_congr fun n => ?_
  rw [log_qTiltWeight_div, qTiltWeight]
  ring

theorem qKLBaseTilt_eq (q : RealEulerNome) :
    qKLBaseTilt q
      = -∑' n : ℕ, qGammaWeight q n * qGammaAtom q n * Real.exp (0 * qGammaAtom q n) := by
  rw [qKLBaseTilt, ← tsum_neg]
  refine tsum_congr fun n => ?_
  have hlog : Real.log (qGammaWeight q n / qTiltWeight q n) = -qGammaAtom q n := by
    rw [← log_qTiltWeight_div q n, ← Real.log_inv]
    congr 1
    rw [inv_div]
  rw [hlog, zero_mul, Real.exp_zero]
  ring

/-- **Equation (25).**  The two directed entropy costs are the response derivatives at the two
intervention points. -/
theorem deriv_qResponseFun_one (q : RealEulerNome) :
    deriv (qResponseFun q) 1 = ((qKLTiltBase q : ℝ) : ℂ) := by
  have hmem : (1 : ℂ) ∈ qStrip :=
    ⟨by simp only [Complex.one_re]; norm_num, by simp only [Complex.one_re]; norm_num⟩
  have h := hasDerivAt_qResponseFun q hmem
  rw [h.deriv, qKLTiltBase_eq]
  have hcast : ((1 : ℂ)) = (((1 : ℝ) : ℝ) : ℂ) := by norm_num
  rw [hcast]
  exact qResponseDeriv_ofReal q (by norm_num : -1 < (1 : ℝ))

theorem deriv_qResponseFun_zero (q : RealEulerNome) :
    deriv (qResponseFun q) 0 = ((-qKLBaseTilt q : ℝ) : ℂ) := by
  have hmem : (0 : ℂ) ∈ qStrip :=
    ⟨by simp only [Complex.zero_re]; norm_num, by simp only [Complex.zero_re]; norm_num⟩
  have h := hasDerivAt_qResponseFun q hmem
  rw [h.deriv, qKLBaseTilt_eq, neg_neg]
  have hcast : ((0 : ℂ)) = (((0 : ℝ) : ℝ) : ℂ) := by norm_num
  rw [hcast]
  exact qResponseDeriv_ofReal q (by norm_num : -1 < (0 : ℝ))

/-! ## §2, the resolvent — the diagonal operator layer -/

theorem summable_norm_sq_of_memℓp {f : ℕ → ℂ} (hf : Memℓp f 2) :
    Summable (fun n : ℕ => ‖f n‖ ^ 2) := by
  have h := (memℓp_gen_iff (E := fun _ : ℕ => ℂ) (f := f) (p := 2) (by norm_num)).mp hf
  refine h.congr fun n => ?_
  rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- Diagonal multiplication of an `ℓ²` sequence. -/
def lpDiagFun (d : ℕ → ℂ) (f : QGammaSpace) : ℕ → ℂ := fun n => d n * (f : ℕ → ℂ) n

theorem memℓp_lpDiagFun {d : ℕ → ℂ} {C : ℝ} (hd : ∀ n, ‖d n‖ ≤ C) (f : QGammaSpace) :
    Memℓp (lpDiagFun d f) 2 := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hd 0)
  refine memℓp_gen ?_
  have hfun : (fun n : ℕ => ‖lpDiagFun d f n‖ ^ (2 : ENNReal).toReal)
      = fun n : ℕ => ‖d n‖ ^ 2 * ‖(f : ℕ → ℂ) n‖ ^ 2 := by
    funext n
    rw [show ((2 : ENNReal).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      lpDiagFun, norm_mul, mul_pow]
  rw [hfun]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_norm_sq_of_memℓp (lp.memℓp f)).mul_left (C ^ 2))
  have hdn : ‖d n‖ ^ 2 ≤ C ^ 2 := by
    have := hd n
    nlinarith [norm_nonneg (d n)]
  exact mul_le_mul_of_nonneg_right hdn (by positivity)

/-- The diagonal operator of a bounded sequence, as a linear map. -/
def lpDiagLM (d : ℕ → ℂ) {C : ℝ} (hd : ∀ n, ‖d n‖ ≤ C) : QGammaSpace →ₗ[ℂ] QGammaSpace where
  toFun f := ⟨lpDiagFun d f, memℓp_lpDiagFun hd f⟩
  map_add' f g := by
    refine lp.ext ?_
    funext n
    show d n * ((f + g : QGammaSpace) : ℕ → ℂ) n
      = (⟨lpDiagFun d f, _⟩ : QGammaSpace) n + (⟨lpDiagFun d g, _⟩ : QGammaSpace) n
    rw [lp.coeFn_add]
    show d n * ((f : ℕ → ℂ) n + (g : ℕ → ℂ) n) = d n * (f : ℕ → ℂ) n + d n * (g : ℕ → ℂ) n
    ring
  map_smul' c f := by
    refine lp.ext ?_
    funext n
    show d n * ((c • f : QGammaSpace) : ℕ → ℂ) n
      = (c • (⟨lpDiagFun d f, _⟩ : QGammaSpace)) n
    rw [lp.coeFn_smul, lp.coeFn_smul]
    show d n * (c * (f : ℕ → ℂ) n) = c * (d n * (f : ℕ → ℂ) n)
    ring

@[simp] theorem lpDiagLM_apply (d : ℕ → ℂ) {C : ℝ} (hd : ∀ n, ‖d n‖ ≤ C) (f : QGammaSpace)
    (n : ℕ) : ((lpDiagLM d hd f : QGammaSpace) : ℕ → ℂ) n = d n * (f : ℕ → ℂ) n := rfl

theorem lpDiagLM_norm_le (d : ℕ → ℂ) {C : ℝ} (hd : ∀ n, ‖d n‖ ≤ C) (f : QGammaSpace) :
    ‖lpDiagLM d hd f‖ ≤ C * ‖f‖ := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hd 0)
  have hsq : ‖lpDiagLM d hd f‖ ^ 2 ≤ (C * ‖f‖) ^ 2 := by
    rw [norm_sq_lp, mul_pow, norm_sq_lp f, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_) ?_ ?_
    · rw [lpDiagLM_apply, norm_mul, mul_pow]
      have hdn : ‖d n‖ ^ 2 ≤ C ^ 2 := by
        have := hd n
        nlinarith [norm_nonneg (d n)]
      exact mul_le_mul_of_nonneg_right hdn (by positivity)
    · exact summable_norm_sq_of_memℓp (lp.memℓp (lpDiagLM d hd f))
    · exact (summable_norm_sq_of_memℓp (lp.memℓp f)).mul_left (C ^ 2)
  have h1 : 0 ≤ ‖lpDiagLM d hd f‖ := norm_nonneg _
  have h2 : 0 ≤ C * ‖f‖ := mul_nonneg hC0 (norm_nonneg _)
  nlinarith

/-- The diagonal operator of a bounded sequence, as a bounded operator. -/
def lpDiagCLM (d : ℕ → ℂ) {C : ℝ} (hd : ∀ n, ‖d n‖ ≤ C) : QGammaSpace →L[ℂ] QGammaSpace :=
  LinearMap.mkContinuous (lpDiagLM d hd) C (lpDiagLM_norm_le d hd)

@[simp] theorem lpDiagCLM_apply (d : ℕ → ℂ) {C : ℝ} (hd : ∀ n, ‖d n‖ ≤ C) (f : QGammaSpace)
    (n : ℕ) : ((lpDiagCLM d hd f : QGammaSpace) : ℕ → ℂ) n = d n * (f : ℕ → ℂ) n := rfl

theorem lpDiagCLM_opNorm_le (d : ℕ → ℂ) {C : ℝ} (hd : ∀ n, ‖d n‖ ≤ C) :
    ‖lpDiagCLM d hd‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ (le_trans (norm_nonneg _) (hd 0)) _

theorem IsCompactOperator.congr_fun' {f g : QGammaSpace → QGammaSpace}
    (hf : IsCompactOperator f) (h : ∀ x, f x = g x) : IsCompactOperator g := by
  have hfg : f = g := funext h
  rwa [hfg] at hf

/-- The `n`-th coordinate injection `ℂ → ℓ²`, as a bounded operator. -/
def lpSingleCLM (n : ℕ) : ℂ →L[ℂ] QGammaSpace :=
  LinearMap.mkContinuous (lp.lsingle (E := fun _ : ℕ => ℂ) (𝕜 := ℂ) 2 n) 1 (fun a => by
    rw [one_mul]
    show ‖lp.single (E := fun _ : ℕ => ℂ) 2 n a‖ ≤ ‖a‖
    rw [lp.norm_single (by norm_num)])

@[simp] theorem lpSingleCLM_apply (n : ℕ) (a : ℂ) : lpSingleCLM n a = lp.single (E := fun _ : ℕ => ℂ) 2 n a := rfl

theorem isCompactOperator_lpSingleCLM (n : ℕ) : IsCompactOperator (lpSingleCLM n) :=
  isCompactOperator_of_locallyCompactSpace_rng _

/-- Every rank-one coordinate operator on `ℓ²` is compact: it factors through `ℂ`. -/
theorem isCompactOperator_rankOne (n : ℕ) (c : ℂ) :
    IsCompactOperator (fun f : QGammaSpace => lp.single (E := fun _ : ℕ => ℂ) 2 n (c * (f : ℕ → ℂ) n)) := by
  have hc : IsCompactOperator ((lpSingleCLM n) ∘
      (c • (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n))) :=
    (isCompactOperator_lpSingleCLM n).comp_clm _
  refine IsCompactOperator.congr_fun' hc fun f => ?_
  rfl

theorem isCompactOperator_finset_rankOne (d : ℕ → ℂ) (N : ℕ) :
    IsCompactOperator (fun f : QGammaSpace =>
      ∑ k ∈ Finset.range N, lp.single (E := fun _ : ℕ => ℂ) 2 k (d k * (f : ℕ → ℂ) k)) := by
  induction N with
  | zero =>
    have h0 : IsCompactOperator (fun _ : QGammaSpace => (0 : QGammaSpace)) :=
      isCompactOperator_zero
    refine IsCompactOperator.congr_fun' h0 fun f => ?_
    simp
  | succ N ih =>
    have hstep := ih.add (isCompactOperator_rankOne N (d N))
    refine IsCompactOperator.congr_fun' hstep fun f => ?_
    rw [Finset.sum_range_succ]
    rfl

theorem lpDiagCLM_trunc_eq_sum (d : ℕ → ℂ) {C : ℝ} (_hd : ∀ n, ‖d n‖ ≤ C) (N : ℕ)
    (hdN : ∀ n, ‖(if n < N then d n else 0 : ℂ)‖ ≤ C) (f : QGammaSpace) :
    (lpDiagCLM (fun n => if n < N then d n else 0) hdN f : QGammaSpace)
      = ∑ k ∈ Finset.range N, lp.single (E := fun _ : ℕ => ℂ) 2 k (d k * (f : ℕ → ℂ) k) := by
  refine lp.ext ?_
  funext n
  rw [lpDiagCLM_apply]
  have hrhs : ((∑ k ∈ Finset.range N, lp.single (E := fun _ : ℕ => ℂ) 2 k (d k * (f : ℕ → ℂ) k) :
      QGammaSpace) : ℕ → ℂ) n
      = ∑ k ∈ Finset.range N, (if n = k then d k * (f : ℕ → ℂ) k else 0) := by
    rw [lp.coeFn_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [lp.single_apply, Pi.single_apply]
  rw [hrhs]
  by_cases hn : n < N
  · rw [if_pos hn, Finset.sum_eq_single n]
    · rw [if_pos rfl]
    · intro k _ hk
      rw [if_neg (fun h => hk h.symm)]
    · intro hmem
      exact absurd (Finset.mem_range.mpr hn) hmem
  · rw [if_neg hn, zero_mul]
    refine (Finset.sum_eq_zero fun k hk => ?_).symm
    have hklt : k < N := Finset.mem_range.mp hk
    rw [if_neg (by omega)]

/-- **A diagonal operator whose entries tend to zero is compact.** -/
theorem isCompactOperator_lpDiagCLM {d : ℕ → ℂ} {C : ℝ} (hd : ∀ n, ‖d n‖ ≤ C)
    (hlim : Filter.Tendsto (fun n => ‖d n‖) Filter.atTop (𝓝 0)) :
    IsCompactOperator (lpDiagCLM d hd) := by
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hd 0)
  have hdN : ∀ N : ℕ, ∀ n, ‖(if n < N then d n else 0 : ℂ)‖ ≤ C := by
    intro N n
    by_cases hn : n < N
    · rw [if_pos hn]
      exact hd n
    · rw [if_neg hn, norm_zero]
      exact hC0
  set T : ℕ → QGammaSpace →L[ℂ] QGammaSpace :=
    fun N => lpDiagCLM (fun n => if n < N then d n else 0) (hdN N) with hT
  have hcompact : ∀ N, IsCompactOperator (T N) := by
    intro N
    refine IsCompactOperator.congr_fun' (isCompactOperator_finset_rankOne d N) fun f => ?_
    exact (lpDiagCLM_trunc_eq_sum d hd N (hdN N) f).symm
  have htend : Filter.Tendsto T Filter.atTop (𝓝 (lpDiagCLM d hd)) := by
    refine Metric.tendsto_atTop.mpr fun ε hε => ?_
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp
      (hlim.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity)))
    refine ⟨N₀, fun N hN => ?_⟩
    have hbound : ∀ n, ‖(d n - if n < N then d n else 0 : ℂ)‖ ≤ ε / 2 := by
      intro n
      by_cases hn : n < N
      · rw [if_pos hn, sub_self, norm_zero]
        positivity
      · rw [if_neg hn, sub_zero]
        exact le_of_lt (hN₀ n (by omega))
    have hdiff : ∀ f : QGammaSpace, ‖lpDiagCLM d hd f - T N f‖ ≤ (ε / 2) * ‖f‖ := by
      intro f
      have hrep : lpDiagCLM d hd f - T N f
          = lpDiagCLM (fun n => d n - if n < N then d n else 0) hbound f := by
        refine lp.ext ?_
        funext n
        rw [lp.coeFn_sub]
        show (lpDiagCLM d hd f : ℕ → ℂ) n - (T N f : ℕ → ℂ) n = _
        rw [lpDiagCLM_apply, hT]
        show d n * (f : ℕ → ℂ) n - (if n < N then d n else 0) * (f : ℕ → ℂ) n = _
        rw [lpDiagCLM_apply]
        ring
      rw [hrep]
      exact lpDiagLM_norm_le _ hbound f
    have hop : ‖T N - lpDiagCLM d hd‖ ≤ ε / 2 := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
      rw [sub_apply, ← norm_neg]
      have hneg : -(T N f - lpDiagCLM d hd f) = lpDiagCLM d hd f - T N f := neg_sub _ _
      rw [hneg]
      exact hdiff f
    rw [dist_eq_norm]
    calc ‖T N - lpDiagCLM d hd‖ ≤ ε / 2 := hop
      _ < ε := by linarith
  exact isCompactOperator_of_tendsto htend (Filter.Eventually.of_forall hcompact)

/-! ### The q-Gamma resolvent -/

/-- **The resolvent entries** `(x_n − i)⁻¹` of the multiplication operator. -/
def qResolventEntry (q : RealEulerNome) (n : ℕ) : ℂ :=
  (((qGammaAtom q n : ℝ) : ℂ) - Complex.I)⁻¹

theorem norm_qGammaAtom_sub_I (q : RealEulerNome) (n : ℕ) :
    1 ≤ ‖((qGammaAtom q n : ℝ) : ℂ) - Complex.I‖ := by
  have him : (((qGammaAtom q n : ℝ) : ℂ) - Complex.I).im = -1 := by
    simp
  have := Complex.abs_im_le_norm (((qGammaAtom q n : ℝ) : ℂ) - Complex.I)
  rw [him] at this
  simpa using this

theorem qResolventEntry_bound (q : RealEulerNome) (n : ℕ) : ‖qResolventEntry q n‖ ≤ 1 := by
  rw [qResolventEntry, norm_inv]
  have h := norm_qGammaAtom_sub_I q n
  rw [inv_le_one_iff₀]
  right
  exact h

/-- **The resolvent inverts** `X − i` coordinatewise. -/
theorem qResolventEntry_mul (q : RealEulerNome) (n : ℕ) :
    (((qGammaAtom q n : ℝ) : ℂ) - Complex.I) * qResolventEntry q n = 1 := by
  rw [qResolventEntry, mul_inv_cancel₀]
  intro h0
  have := norm_qGammaAtom_sub_I q n
  rw [h0, norm_zero] at this
  linarith

theorem tendsto_qGammaAtom_atBot (q : RealEulerNome) :
    Filter.Tendsto (qGammaAtom q) Filter.atTop Filter.atBot := by
  have hlog : Real.log q.val < 0 := Real.log_neg q.pos q.lt_one
  have hnat : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hlin : Filter.Tendsto (fun n : ℕ => (n : ℝ) * Real.log q.val) Filter.atTop
      Filter.atBot := hnat.atTop_mul_const_of_neg hlog
  have hshift := tendsto_atBot_add_const_right Filter.atTop (-Real.log (1 - q.val)) hlin
  refine hshift.congr fun n => ?_
  rw [qGammaAtom]
  ring

theorem tendsto_norm_qResolventEntry (q : RealEulerNome) :
    Filter.Tendsto (fun n => ‖qResolventEntry q n‖) Filter.atTop (𝓝 0) := by
  have habs : Filter.Tendsto (fun n : ℕ => |qGammaAtom q n|) Filter.atTop Filter.atTop :=
    Filter.tendsto_abs_atBot_atTop.comp (tendsto_qGammaAtom_atBot q)
  have hnorm : Filter.Tendsto (fun n : ℕ => ‖((qGammaAtom q n : ℝ) : ℂ) - Complex.I‖)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun n => ?_) habs
    have := Complex.abs_re_le_norm (((qGammaAtom q n : ℝ) : ℂ) - Complex.I)
    have hre : (((qGammaAtom q n : ℝ) : ℂ) - Complex.I).re = qGammaAtom q n := by simp
    rwa [hre] at this
  have hinv := hnorm.inv_tendsto_atTop
  refine hinv.congr fun n => ?_
  show (‖((qGammaAtom q n : ℝ) : ℂ) - Complex.I‖)⁻¹ = _
  rw [qResolventEntry, norm_inv]

/-- **The resolvent of the q-Gamma multiplication operator.** -/
def qResolvent (q : RealEulerNome) : QGammaSpace →L[ℂ] QGammaSpace :=
  lpDiagCLM (qResolventEntry q) (qResolventEntry_bound q)

/-- **Theorem 2.1, the compact-resolvent clause.**  The resolvent is a compact operator. -/
theorem isCompactOperator_qResolvent (q : RealEulerNome) :
    IsCompactOperator (qResolvent q) :=
  isCompactOperator_lpDiagCLM _ (tendsto_norm_qResolventEntry q)

end

end GaloisForLFunctions.HTGeometry
