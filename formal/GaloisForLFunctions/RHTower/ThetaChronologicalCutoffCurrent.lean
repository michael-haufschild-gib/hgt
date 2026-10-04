import GaloisForLFunctions.RHTower.ThetaMovingCuspSpectralShear
import GaloisForLFunctions.RHTower.ThetaCutoffCommutatorMellin

/-!
# Gaussian polynomial atoms and the cofinal cutoff current as a log-shift series

The atoms `ψ_Q(y) = e^{3y} Q(e^{2y}) e^{−π e^{2y}}` are closed under differentiation:
`ψ_Q' = ψ_{3Q + 2XQ' − 2πXQ}`.  Each is bounded with a right Gaussian tail, and the weighted
lattice sums `Σ_d d^{−1} |ψ_Q(y + log d)|` are bounded uniformly in `y ∈ ℝ`.  The cofinal cutoff
current is `C(y) = Σ_d μ(d)/d · φ(y + log d)` with `φ = ψ_{−2π}`; hence every derivative of `C`
is a bounded continuous log-shift series.  A log-shift series has Mellin transform
`(Σ_d a_d d^{−z}) ℒf(z)` wherever this converges absolutely.
-/

open MeasureTheory Set Filter Topology Polynomial
open scoped ContDiff

namespace RHTower

noncomputable section

/-! ## Gaussian polynomial atoms -/

/-- `ψ_Q(y) = e^{3y} Q(e^{2y}) e^{−π e^{2y}}`. -/
def gaussPolyAtom (Q : ℝ[X]) (y : ℝ) : ℝ :=
  Real.exp (3 * y) * Q.eval (Real.exp (2 * y)) * Real.exp (-(Real.pi * Real.exp (2 * y)))

/-- The derivative polynomial `3Q + 2XQ' − 2πXQ`. -/
def gaussPolyAtomStep (Q : ℝ[X]) : ℝ[X] :=
  C 3 * Q + C 2 * X * derivative Q - C (2 * Real.pi) * X * Q

theorem hasDerivAt_gaussPolyAtom (Q : ℝ[X]) (y : ℝ) :
    HasDerivAt (gaussPolyAtom Q) (gaussPolyAtom (gaussPolyAtomStep Q) y) y := by
  have h1 : HasDerivAt (fun y : ℝ => Real.exp (3 * y)) (Real.exp (3 * y) * 3) y :=
    ((hasDerivAt_id y).const_mul 3 |>.congr_deriv (by simp)).exp
  have h2 : HasDerivAt (fun y : ℝ => Real.exp (2 * y)) (Real.exp (2 * y) * 2) y :=
    ((hasDerivAt_id y).const_mul 2 |>.congr_deriv (by simp)).exp
  have hQ := (Q.hasDerivAt (Real.exp (2 * y))).comp y h2
  have h3 : HasDerivAt (fun y : ℝ => Real.exp (-(Real.pi * Real.exp (2 * y))))
      (Real.exp (-(Real.pi * Real.exp (2 * y))) * (-(Real.pi * (Real.exp (2 * y) * 2)))) y :=
    ((h2.const_mul Real.pi).neg).exp
  have h := (h1.fun_mul hQ).fun_mul h3
  simp only [Function.comp_def] at h
  refine h.congr_deriv ?_
  simp only [gaussPolyAtom, gaussPolyAtomStep, eval_sub, eval_add, eval_mul, eval_C, eval_X]
  ring

/-- The iterated derivative polynomials. -/
def gaussPolyAtomIter (Q : ℝ[X]) (n : ℕ) : ℝ[X] := gaussPolyAtomStep^[n] Q

theorem iteratedDeriv_gaussPolyAtom (Q : ℝ[X]) (n : ℕ) :
    iteratedDeriv n (gaussPolyAtom Q) = gaussPolyAtom (gaussPolyAtomIter Q n) := by
  induction n with
  | zero => simp [gaussPolyAtomIter]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    rw [(hasDerivAt_gaussPolyAtom _ y).deriv, gaussPolyAtomIter, gaussPolyAtomIter,
      Function.iterate_succ_apply']

theorem continuous_gaussPolyAtom (Q : ℝ[X]) : Continuous (gaussPolyAtom Q) :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_gaussPolyAtom Q y).continuousAt

/-- A polynomial bound `|Q(s)| ≤ A (1+s)^m` on `s ≥ 0`. -/
theorem exists_abs_eval_le (Q : ℝ[X]) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ s : ℝ, 0 ≤ s → |Q.eval s| ≤ A * (1 + s) ^ Q.natDegree := by
  refine ⟨∑ i ∈ Finset.range (Q.natDegree + 1), |Q.coeff i|, Finset.sum_nonneg fun _ _ => abs_nonneg _,
    fun s hs => ?_⟩
  rw [eval_eq_sum_range, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_pow, abs_of_nonneg hs]
  have hi' : i ≤ Q.natDegree := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc s ^ i ≤ (1 + s) ^ i := pow_le_pow_left₀ hs (by linarith) i
    _ ≤ (1 + s) ^ Q.natDegree := pow_le_pow_right₀ (by linarith) hi'

/-- `(1+x)^k e^{−cx} ≤ e^c k!/c^k` for `x ≥ 0`, `c > 0`. -/
theorem one_add_pow_mul_exp_neg_le {c : ℝ} (hc : 0 < c) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ k * Real.exp (-(c * x)) ≤ Real.exp c * (k.factorial / c ^ k) := by
  have h := Real.pow_div_factorial_le_exp (c * (1 + x)) (by positivity) k
  rw [div_le_iff₀ (by positivity), mul_pow] at h
  have hexp : Real.exp (-(c * x)) = Real.exp c * Real.exp (-(c * (1 + x))) := by
    rw [← Real.exp_add]; ring_nf
  rw [hexp]
  have hpos : 0 < c ^ k := by positivity
  have he := Real.exp_pos (-(c * (1 + x)))
  have h2 : (1 + x) ^ k * Real.exp (-(c * (1 + x))) ≤ k.factorial / c ^ k := by
    rw [le_div_iff₀ hpos]
    have : Real.exp (c * (1 + x)) * Real.exp (-(c * (1 + x))) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [mul_le_mul_of_nonneg_right h he.le]
  nlinarith [Real.exp_pos c]

theorem gaussianLogTail_gaussPolyAtom (Q : ℝ[X]) : GaussianLogTail (gaussPolyAtom Q) := by
  obtain ⟨A, hA, hQ⟩ := exists_abs_eval_le Q
  set m := Q.natDegree
  have hpos : ∀ y, 0 ≤ y → |gaussPolyAtom Q y| ≤ A * 2 ^ m * Real.exp (((3 + 2 * m : ℕ) : ℝ) * y) *
      Real.exp (-Real.pi * Real.exp (2 * y)) := by
    intro y hy
    have hs : 1 ≤ Real.exp (2 * y) := Real.one_le_exp (by linarith)
    rw [gaussPolyAtom, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have h1 := hQ _ (Real.exp_pos (2 * y)).le
    have h2 : (1 + Real.exp (2 * y)) ^ m ≤ 2 ^ m * Real.exp (2 * y) ^ m := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by linarith) m
    have h3 : Real.exp (3 * y) * Real.exp (2 * y) ^ m = Real.exp (((3 + 2 * m : ℕ) : ℝ) * y) := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]; push_cast; ring_nf
    calc Real.exp (3 * y) * |Q.eval (Real.exp (2 * y))| * Real.exp (-(Real.pi * Real.exp (2 * y)))
        ≤ Real.exp (3 * y) * (A * (2 ^ m * Real.exp (2 * y) ^ m)) *
            Real.exp (-(Real.pi * Real.exp (2 * y))) := by
          gcongr
          exact h1.trans (mul_le_mul_of_nonneg_left h2 hA)
      _ = A * 2 ^ m * (Real.exp (3 * y) * Real.exp (2 * y) ^ m) *
            Real.exp (-Real.pi * Real.exp (2 * y)) := by ring_nf
      _ = _ := by rw [h3]
  refine ⟨⟨A * 2 ^ m * Real.exp ((((3 + 2 * m : ℕ) : ℝ)) ^ 2 / (8 * Real.pi)) + A * 2 ^ m, by positivity,
    fun y => ?_⟩, ⟨A * 2 ^ m, 3 + 2 * m, by positivity, hpos⟩⟩
  rcases le_total 0 y with hy | hy
  · refine (hpos y hy).trans ?_
    have := exp_mul_exp_neg_le (((3 + 2 * m : ℕ) : ℝ)) y hy
    have hc : 0 ≤ A * 2 ^ m := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this hc, Real.exp_pos ((((3 + 2 * m : ℕ) : ℝ)) ^ 2 / (8 * Real.pi))]
  · have hs : Real.exp (2 * y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hs0 := Real.exp_pos (2 * y)
    rw [gaussPolyAtom, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
    have h1 := hQ _ hs0.le
    have e1 : Real.exp (3 * y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have e3 : Real.exp (-(Real.pi * Real.exp (2 * y))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    have h2 : (1 + Real.exp (2 * y)) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by positivity) (by linarith) m
    have hQb : |Q.eval (Real.exp (2 * y))| ≤ A * 2 ^ m := h1.trans (mul_le_mul_of_nonneg_left h2 hA)
    have := Real.exp_pos ((((3 + 2 * m : ℕ) : ℝ)) ^ 2 / (8 * Real.pi))
    calc Real.exp (3 * y) * |Q.eval (Real.exp (2 * y))| * Real.exp (-(Real.pi * Real.exp (2 * y)))
        ≤ 1 * (A * 2 ^ m) * 1 := by gcongr
      _ ≤ _ := by nlinarith [mul_nonneg (show (0:ℝ) ≤ A * 2 ^ m by positivity) this.le]

/-! ## Uniform lattice bounds -/

/-- `Σ_{d ≥ 1} e^{−b d²} ≤ (1/2)√(π/b)`, through partial sums. -/
theorem sum_range_exp_neg_mul_sq_le {b : ℝ} (hb : 0 < b) (N : ℕ) :
    ∑ i ∈ Finset.range N, Real.exp (-b * ((i + 1 : ℕ) : ℝ) ^ 2) ≤ Real.sqrt (Real.pi / b) / 2 := by
  have hanti : AntitoneOn (fun x : ℝ => Real.exp (-b * x ^ 2)) (Icc 0 (0 + N)) := by
    intro x hx y hy hxy
    refine Real.exp_le_exp.2 ?_
    have : x ^ 2 ≤ y ^ 2 := pow_le_pow_left₀ hx.1 hxy 2
    nlinarith
  have h1 := hanti.sum_le_integral
  simp only [zero_add] at h1
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-b * x ^ 2)) (Ioi 0) :=
    (integrable_exp_neg_mul_sq hb).integrableOn
  have h2 : ∫ x in (0 : ℝ)..N, Real.exp (-b * x ^ 2) ≤ ∫ x in Ioi (0 : ℝ), Real.exp (-b * x ^ 2) := by
    rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N)]
    exact setIntegral_mono_set hint (Eventually.of_forall fun x => (Real.exp_pos _).le)
      (Ioc_subset_Ioi_self.eventuallyLE)
  rw [integral_gaussian_Ioi] at h2
  refine le_trans (le_of_eq ?_) (h1.trans h2)
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring_nf

/-- **Uniform lattice bound.**  `Σ_d d^{−1} |ψ_Q(y + log d)|` converges and is bounded uniformly in
`y ∈ ℝ`. -/
theorem exists_tsum_inv_mul_abs_gaussPolyAtom_le (Q : ℝ[X]) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, Summable (fun d : ℕ => (d : ℝ)⁻¹ * |gaussPolyAtom Q (y + Real.log d)|) ∧
      ∑' d : ℕ, (d : ℝ)⁻¹ * |gaussPolyAtom Q (y + Real.log d)| ≤ M := by
  obtain ⟨A, hA, hQ⟩ := exists_abs_eval_le Q
  set m := Q.natDegree
  set K : ℝ := A * (Real.exp (Real.pi / 2) * ((m + 1).factorial / (Real.pi / 2) ^ (m + 1)))
  have hK : 0 ≤ K := by positivity
  set M : ℝ := K * (Real.sqrt (Real.pi / (Real.pi / 2)) / 2)
  have hterm : ∀ y : ℝ, ∀ d : ℕ, 1 ≤ d → (d : ℝ)⁻¹ * |gaussPolyAtom Q (y + Real.log d)| ≤
      K * Real.exp y * Real.exp (-(Real.pi / 2 * Real.exp (2 * y)) * (d : ℝ) ^ 2) := by
    intro y d hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    set x : ℝ := (d : ℝ) ^ 2 * Real.exp (2 * y)
    have hx : 0 ≤ x := by positivity
    have e2 : Real.exp (2 * (y + Real.log d)) = x := by
      have hl : Real.exp (2 * Real.log d) = (d : ℝ) ^ 2 := by
        rw [← Real.exp_log (pow_pos hdR 2), Real.log_pow]; norm_num
      rw [mul_add, Real.exp_add, hl, mul_comm]
    have e3 : Real.exp (3 * (y + Real.log d)) = (d : ℝ) ^ 3 * Real.exp (3 * y) := by
      have hl : Real.exp (3 * Real.log d) = (d : ℝ) ^ 3 := by
        rw [← Real.exp_log (pow_pos hdR 3), Real.log_pow]; norm_num
      rw [mul_add, Real.exp_add, hl, mul_comm]
    rw [gaussPolyAtom, e2, e3, abs_mul, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (d : ℝ) ^ 3 * Real.exp (3 * y)),
      abs_of_pos (Real.exp_pos _)]
    have h1 := hQ x hx
    have hb := one_add_pow_mul_exp_neg_le (show 0 < Real.pi / 2 by positivity) (m + 1) hx
    have hsplit : Real.exp (-(Real.pi * x)) = Real.exp (-(Real.pi / 2 * x)) * Real.exp (-(Real.pi / 2 * x)) := by
      rw [← Real.exp_add]; ring_nf
    have hxe : x * Real.exp y = (d : ℝ) ^ 2 * Real.exp (3 * y) := by
      simp only [x]; rw [mul_assoc, ← Real.exp_add]; ring_nf
    have hlast : Real.exp (-(Real.pi / 2 * x)) = Real.exp (-(Real.pi / 2 * Real.exp (2 * y)) * (d : ℝ) ^ 2) := by
      simp only [x]; ring_nf
    have key : x * |Q.eval x| ≤ A * (1 + x) ^ (m + 1) := by
      calc x * |Q.eval x| ≤ (1 + x) * (A * (1 + x) ^ m) :=
            mul_le_mul (by linarith) h1 (abs_nonneg _) (by positivity)
        _ = A * (1 + x) ^ (m + 1) := by ring
    have hb' : A * (1 + x) ^ (m + 1) * Real.exp (-(Real.pi / 2 * x)) ≤ K := by
      simp only [K]; rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hb hA
    calc (d : ℝ)⁻¹ * ((d : ℝ) ^ 3 * Real.exp (3 * y) * |Q.eval x| * Real.exp (-(Real.pi * x)))
        = Real.exp y * (x * |Q.eval x|) * (Real.exp (-(Real.pi / 2 * x)) *
            Real.exp (-(Real.pi / 2 * x))) := by
          rw [← hsplit, show Real.exp y * (x * |Q.eval x|) = (x * Real.exp y) * |Q.eval x| by ring, hxe]
          field_simp
      _ ≤ Real.exp y * (A * (1 + x) ^ (m + 1)) * (Real.exp (-(Real.pi / 2 * x)) *
            Real.exp (-(Real.pi / 2 * x))) := by gcongr
      _ = Real.exp y * (A * (1 + x) ^ (m + 1) * Real.exp (-(Real.pi / 2 * x))) *
            Real.exp (-(Real.pi / 2 * x)) := by ring
      _ ≤ Real.exp y * K * Real.exp (-(Real.pi / 2 * x)) := by gcongr
      _ = _ := by rw [hlast]; ring
  have hpartial : ∀ y : ℝ, ∀ N : ℕ, ∑ d ∈ Finset.range N,
      (d : ℝ)⁻¹ * |gaussPolyAtom Q (y + Real.log d)| ≤ M := by
    intro y N
    cases N with
    | zero => simp; positivity
    | succ N =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, inv_zero, zero_mul, add_zero]
      have hb : 0 < Real.pi / 2 * Real.exp (2 * y) := by positivity
      calc ∑ i ∈ Finset.range N, ((i + 1 : ℕ) : ℝ)⁻¹ * |gaussPolyAtom Q (y + Real.log ((i + 1 : ℕ) : ℝ))|
          ≤ ∑ i ∈ Finset.range N, K * Real.exp y *
              Real.exp (-(Real.pi / 2 * Real.exp (2 * y)) * ((i + 1 : ℕ) : ℝ) ^ 2) :=
            Finset.sum_le_sum fun i _ => hterm y (i + 1) (by omega)
        _ = K * Real.exp y * ∑ i ∈ Finset.range N,
              Real.exp (-(Real.pi / 2 * Real.exp (2 * y)) * ((i + 1 : ℕ) : ℝ) ^ 2) := by
            rw [Finset.mul_sum]
        _ ≤ K * Real.exp y * (Real.sqrt (Real.pi / (Real.pi / 2 * Real.exp (2 * y))) / 2) :=
            mul_le_mul_of_nonneg_left (sum_range_exp_neg_mul_sq_le hb N) (by positivity)
        _ = M := by
            simp only [M]
            have : Real.sqrt (Real.pi / (Real.pi / 2 * Real.exp (2 * y))) =
                Real.sqrt (Real.pi / (Real.pi / 2)) * (Real.exp y)⁻¹ := by
              rw [div_mul_eq_div_div, Real.sqrt_div' _ (Real.exp_pos _).le,
                show Real.exp (2 * y) = Real.exp y ^ 2 by rw [← Real.exp_nat_mul]; ring_nf,
                Real.sqrt_sq (Real.exp_pos _).le, div_eq_mul_inv]
            rw [this]
            field_simp
  refine ⟨M, by positivity, fun y => ?_⟩
  have hnn : ∀ d : ℕ, 0 ≤ (d : ℝ)⁻¹ * |gaussPolyAtom Q (y + Real.log d)| := fun d => by positivity
  exact ⟨summable_of_sum_range_le hnn (hpartial y), Real.tsum_le_of_sum_range_le hnn (hpartial y)⟩

/-! ## The cofinal cutoff current -/

/-- The one-atom current `φ(y) = −2π e^{3y} e^{−π e^{2y}}`. -/
def cutoffAtomPoly : ℝ[X] := C (-(2 * Real.pi))

theorem gaussPolyAtom_cutoffAtomPoly (y : ℝ) :
    gaussPolyAtom cutoffAtomPoly y = -(2 * Real.pi) * Real.exp (3 * y) *
      Real.exp (-(Real.pi * Real.exp (2 * y))) := by
  simp [gaussPolyAtom, cutoffAtomPoly]; ring

/-- The weights `μ(d)/d`. -/
def moebiusInvWeight (d : ℕ) : ℝ := (ArithmeticFunction.moebius d : ℝ) * (d : ℝ)⁻¹

theorem polyBoundedWeight_moebiusInvWeight : PolyBoundedWeight 0 moebiusInvWeight := by
  intro d
  rw [moebiusInvWeight, pow_zero, abs_mul]
  have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  · have : |(d : ℝ)⁻¹| ≤ 1 := by
      rw [abs_of_pos (by positivity)]; exact inv_le_one_of_one_le₀ (by exact_mod_cast hd)
    nlinarith [abs_nonneg ((ArithmeticFunction.moebius d : ℝ)), abs_nonneg ((d : ℝ)⁻¹)]

theorem thetaFluxTerm_eq_neg_atom {d : ℕ} (hd : 0 < d) (y : ℝ) :
    (ArithmeticFunction.moebius d : ℝ) * thetaFluxTerm y d =
      -(moebiusInvWeight d * gaussPolyAtom cutoffAtomPoly (y + Real.log d)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have e2 : Real.exp (2 * (y + Real.log d)) = (d : ℝ) ^ 2 * Real.exp (2 * y) := by
    have hl : Real.exp (2 * Real.log d) = (d : ℝ) ^ 2 := by
      rw [← Real.exp_log (pow_pos hdR 2), Real.log_pow]; norm_num
    rw [mul_add, Real.exp_add, hl, mul_comm]
  have e3 : Real.exp (3 * (y + Real.log d)) = (d : ℝ) ^ 3 * Real.exp (3 * y) := by
    have hl : Real.exp (3 * Real.log d) = (d : ℝ) ^ 3 := by
      rw [← Real.exp_log (pow_pos hdR 3), Real.log_pow]; norm_num
    rw [mul_add, Real.exp_add, hl, mul_comm]
  rw [thetaFluxTerm_eq, moebiusInvWeight, gaussPolyAtom_cutoffAtomPoly, e2, e3]
  field_simp

/-- **(14)** `C(y) = Σ_d μ(d)/d · φ(y + log d)`. -/
theorem cofinalBoundaryProfile_eq_logShiftSeries :
    cofinalBoundaryProfile = logShiftSeries moebiusInvWeight (gaussPolyAtom cutoffAtomPoly) := by
  funext y
  rw [cofinalBoundaryProfile, logShiftSeries, ← tsum_neg]
  refine tsum_congr fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [moebiusInvWeight]
  · rw [thetaFluxTerm_eq_neg_atom hd, neg_neg]

/-- The derivative polynomials of the cutoff current. -/
def cutoffDerivPoly (j : ℕ) : ℝ[X] := gaussPolyAtomIter cutoffAtomPoly j

/-- **Every derivative of `C` is the log-shift series of the derived atom.** -/
theorem iteratedDeriv_cofinalBoundaryProfile (j : ℕ) :
    iteratedDeriv j cofinalBoundaryProfile =
      logShiftSeries moebiusInvWeight (gaussPolyAtom (cutoffDerivPoly j)) := by
  induction j with
  | zero => simp [cofinalBoundaryProfile_eq_logShiftSeries, cutoffDerivPoly, gaussPolyAtomIter]
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext y
    refine (GaussianLogTail.hasDerivAt_logShiftSeries (gaussianLogTail_gaussPolyAtom _)
      (gaussianLogTail_gaussPolyAtom _) (fun x => hasDerivAt_gaussPolyAtom _ x)
      polyBoundedWeight_moebiusInvWeight y).deriv.trans ?_
    rw [cutoffDerivPoly, cutoffDerivPoly, gaussPolyAtomIter, gaussPolyAtomIter,
      Function.iterate_succ_apply']

theorem cutoffDerivPoly_succ (j : ℕ) :
    cutoffDerivPoly (j + 1) = gaussPolyAtomStep (cutoffDerivPoly j) := by
  rw [cutoffDerivPoly, cutoffDerivPoly, gaussPolyAtomIter, gaussPolyAtomIter,
    Function.iterate_succ_apply']

theorem hasDerivAt_iteratedDeriv_cofinalBoundaryProfile (j : ℕ) (y : ℝ) :
    HasDerivAt (iteratedDeriv j cofinalBoundaryProfile)
      (iteratedDeriv (j + 1) cofinalBoundaryProfile y) y := by
  rw [iteratedDeriv_cofinalBoundaryProfile j, iteratedDeriv_cofinalBoundaryProfile (j + 1),
    cutoffDerivPoly_succ]
  exact GaussianLogTail.hasDerivAt_logShiftSeries (gaussianLogTail_gaussPolyAtom _)
    (gaussianLogTail_gaussPolyAtom _) (fun x => hasDerivAt_gaussPolyAtom _ x)
    polyBoundedWeight_moebiusInvWeight y

theorem continuous_iteratedDeriv_cofinalBoundaryProfile (j : ℕ) :
    Continuous (iteratedDeriv j cofinalBoundaryProfile) :=
  continuous_iff_continuousAt.2 fun y => (hasDerivAt_iteratedDeriv_cofinalBoundaryProfile j y).continuousAt

theorem contDiff_cofinalBoundaryProfile : ContDiff ℝ ∞ cofinalBoundaryProfile := by
  rw [contDiff_infty]
  intro n
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  exact fun y => (hasDerivAt_iteratedDeriv_cofinalBoundaryProfile m y).differentiableAt

/-- **Every derivative of `C` is bounded on the whole line.** -/
theorem exists_abs_iteratedDeriv_cofinalBoundaryProfile_le (j : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, |iteratedDeriv j cofinalBoundaryProfile y| ≤ M := by
  obtain ⟨M, hM, hsum⟩ := exists_tsum_inv_mul_abs_gaussPolyAtom_le (cutoffDerivPoly j)
  refine ⟨M, hM, fun y => ?_⟩
  rw [iteratedDeriv_cofinalBoundaryProfile, logShiftSeries]
  obtain ⟨hs, hle⟩ := hsum y
  have hbound : ∀ d : ℕ, |moebiusInvWeight d * gaussPolyAtom (cutoffDerivPoly j) (y + Real.log d)| ≤
      (d : ℝ)⁻¹ * |gaussPolyAtom (cutoffDerivPoly j) (y + Real.log d)| := by
    intro d
    have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hw : |moebiusInvWeight d| ≤ (d : ℝ)⁻¹ := by
      rw [moebiusInvWeight, abs_mul, abs_inv, Nat.abs_cast]
      calc |(ArithmeticFunction.moebius d : ℝ)| * (d : ℝ)⁻¹ ≤ 1 * (d : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_right hμ (inv_nonneg.2 (Nat.cast_nonneg d))
        _ = _ := one_mul _
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hw (abs_nonneg _)
  have hs' : Summable fun d : ℕ => |moebiusInvWeight d * gaussPolyAtom (cutoffDerivPoly j) (y + Real.log d)| :=
    Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hbound hs
  rw [← Real.norm_eq_abs]
  calc ‖∑' d : ℕ, moebiusInvWeight d * gaussPolyAtom (cutoffDerivPoly j) (y + Real.log d)‖
      ≤ ∑' d : ℕ, ‖moebiusInvWeight d * gaussPolyAtom (cutoffDerivPoly j) (y + Real.log d)‖ :=
        norm_tsum_le_tsum_norm (by simpa only [Real.norm_eq_abs] using hs')
    _ = ∑' d : ℕ, |moebiusInvWeight d * gaussPolyAtom (cutoffDerivPoly j) (y + Real.log d)| :=
        tsum_congr fun d => Real.norm_eq_abs _
    _ ≤ ∑' d : ℕ, (d : ℝ)⁻¹ * |gaussPolyAtom (cutoffDerivPoly j) (y + Real.log d)| :=
        Summable.tsum_le_tsum hbound hs' hs
    _ ≤ M := hle

/-! ## Laplace transforms -/

/-- A two-sided envelope `|ψ_Q(y)| ≤ K e^{3y} e^{−(π/2) e^{2y}}`. -/
theorem exists_abs_gaussPolyAtom_le_envelope (Q : ℝ[X]) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y, |gaussPolyAtom Q y| ≤
      K * (Real.exp (3 * y) * Real.exp (-(Real.pi / 2 * Real.exp (2 * y)))) := by
  obtain ⟨A, hA, hQ⟩ := exists_abs_eval_le Q
  set m := Q.natDegree
  set K : ℝ := A * (Real.exp (Real.pi / 2) * (m.factorial / (Real.pi / 2) ^ m))
  refine ⟨K, by positivity, fun y => ?_⟩
  set s := Real.exp (2 * y)
  have hs : 0 ≤ s := (Real.exp_pos _).le
  have hb := one_add_pow_mul_exp_neg_le (show 0 < Real.pi / 2 by positivity) m hs
  rw [gaussPolyAtom, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  have hsplit : Real.exp (-(Real.pi * s)) = Real.exp (-(Real.pi / 2 * s)) * Real.exp (-(Real.pi / 2 * s)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  calc Real.exp (3 * y) * |Q.eval s| * (Real.exp (-(Real.pi / 2 * s)) * Real.exp (-(Real.pi / 2 * s)))
      ≤ Real.exp (3 * y) * (A * (1 + s) ^ m) * (Real.exp (-(Real.pi / 2 * s)) *
          Real.exp (-(Real.pi / 2 * s))) := by gcongr; exact hQ s hs
    _ = Real.exp (3 * y) * (A * ((1 + s) ^ m * Real.exp (-(Real.pi / 2 * s)))) *
          Real.exp (-(Real.pi / 2 * s)) := by ring
    _ ≤ Real.exp (3 * y) * K * Real.exp (-(Real.pi / 2 * s)) := by
        gcongr; simp only [K]; exact mul_le_mul_of_nonneg_left hb hA
    _ = _ := by ring

theorem integrable_cexp_mul_gaussPolyAtom (Q : ℝ[X]) {z : ℂ} (hz : -3 < z.re) :
    Integrable fun y : ℝ => Complex.exp (z * y) * (gaussPolyAtom Q y : ℂ) := by
  obtain ⟨K, hK, hb⟩ := exists_abs_gaussPolyAtom_le_envelope Q
  have hmaj : Integrable fun y : ℝ => K * (Real.exp ((z.re + 3) * y) *
      Real.exp (-(Real.pi / 2 * Real.exp (2 * y)))) :=
    (integrable_exp_mul_exp_neg_mul_exp_two_mul (by linarith) (by positivity)).const_mul K
  refine hmaj.mono' ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
    (Complex.continuous_ofReal.comp (continuous_gaussPolyAtom Q))).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  calc Real.exp (z.re * y) * |gaussPolyAtom Q y|
      ≤ Real.exp (z.re * y) * (K * (Real.exp (3 * y) * Real.exp (-(Real.pi / 2 * Real.exp (2 * y))))) :=
        mul_le_mul_of_nonneg_left (hb y) (Real.exp_pos _).le
    _ = _ := by rw [add_mul, Real.exp_add]; ring

theorem tendsto_exp_mul_exp_neg_exp_atTop {b c : ℝ} (hc : 0 < c) :
    Tendsto (fun y : ℝ => Real.exp (b * y) * Real.exp (-(c * Real.exp (2 * y)))) atTop (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => b * y - c * Real.exp (2 * y)) atTop atBot := by
    refine tendsto_atBot_mono' atTop ?_ tendsto_neg_atTop_atBot
    filter_upwards [eventually_ge_atTop (max 0 ((|b| + 1) / (2 * c)))] with y hy
    have hy0 : 0 ≤ y := le_trans (le_max_left _ _) hy
    have hy1 : (|b| + 1) / (2 * c) ≤ y := le_trans (le_max_right _ _) hy
    rw [div_le_iff₀ (by positivity)] at hy1
    have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * y by linarith)
    nlinarith [abs_nonneg b, le_abs_self b, mul_le_mul_of_nonneg_left hq hc.le]
  refine (Real.tendsto_exp_atBot.comp h).congr fun y => ?_
  simp only [Function.comp, ← Real.exp_add]
  ring_nf

theorem tendsto_cexp_mul_gaussPolyAtom (Q : ℝ[X]) {z : ℂ} (hz : -3 < z.re) :
    Tendsto (fun y : ℝ => Complex.exp (z * y) * (gaussPolyAtom Q y : ℂ)) atBot (𝓝 0) ∧
      Tendsto (fun y : ℝ => Complex.exp (z * y) * (gaussPolyAtom Q y : ℂ)) atTop (𝓝 0) := by
  obtain ⟨K, hK, hb⟩ := exists_abs_gaussPolyAtom_le_envelope Q
  have hnorm : ∀ y : ℝ, ‖Complex.exp (z * y) * (gaussPolyAtom Q y : ℂ)‖ ≤
      K * (Real.exp ((z.re + 3) * y) * Real.exp (-(Real.pi / 2 * Real.exp (2 * y)))) := fun y => by
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    calc Real.exp (z.re * y) * |gaussPolyAtom Q y|
        ≤ Real.exp (z.re * y) * (K * (Real.exp (3 * y) * Real.exp (-(Real.pi / 2 * Real.exp (2 * y))))) :=
          mul_le_mul_of_nonneg_left (hb y) (Real.exp_pos _).le
      _ = _ := by rw [add_mul, Real.exp_add]; ring
  constructor
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmaj : Tendsto (fun y : ℝ => K * Real.exp ((z.re + 3) * y)) atBot (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atBot (show 0 < z.re + 3 by linarith))).const_mul K
      simpa using this
    refine squeeze_zero (fun _ => norm_nonneg _) (fun y => (hnorm y).trans ?_) hmaj
    have : Real.exp (-(Real.pi / 2 * Real.exp (2 * y))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos, Real.exp_pos (2 * y)])
    nlinarith [Real.exp_pos ((z.re + 3) * y), mul_le_mul_of_nonneg_left this (Real.exp_pos ((z.re + 3) * y)).le]
  · rw [tendsto_zero_iff_norm_tendsto_zero]
    have hmaj := (tendsto_exp_mul_exp_neg_exp_atTop (b := z.re + 3) (show 0 < Real.pi / 2 by positivity)).const_mul K
    rw [mul_zero] at hmaj
    exact squeeze_zero (fun _ => norm_nonneg _) hnorm hmaj

/-- **Integration by parts for atoms.**  `ℒψ_{Q'} = −z ℒψ_Q` on `Re z > −3`. -/
theorem integral_cexp_mul_gaussPolyAtom_step (Q : ℝ[X]) {z : ℂ} (hz : -3 < z.re) :
    (∫ y : ℝ, Complex.exp (z * y) * (gaussPolyAtom (gaussPolyAtomStep Q) y : ℂ)) =
      -z * ∫ y : ℝ, Complex.exp (z * y) * (gaussPolyAtom Q y : ℂ) := by
  have hderiv : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (z * y) * (gaussPolyAtom Q y : ℂ))
      (z * (Complex.exp (z * y) * (gaussPolyAtom Q y : ℂ)) +
        Complex.exp (z * y) * (gaussPolyAtom (gaussPolyAtomStep Q) y : ℂ)) y := by
    intro y
    have h1 : HasDerivAt (fun y : ℝ => Complex.exp (z * y)) (Complex.exp (z * y) * z) y := by
      have := ((hasDerivAt_id (y : ℂ)).const_mul z).cexp.comp_ofReal
      simpa using this
    have h2 : HasDerivAt (fun y : ℝ => (gaussPolyAtom Q y : ℂ))
        ((gaussPolyAtom (gaussPolyAtomStep Q) y : ℝ) : ℂ) y := (hasDerivAt_gaussPolyAtom Q y).ofReal_comp
    exact (h1.fun_mul h2).congr_deriv (by ring)
  have hint1 := integrable_cexp_mul_gaussPolyAtom Q hz
  have hint2 := integrable_cexp_mul_gaussPolyAtom (gaussPolyAtomStep Q) hz
  have h := integral_of_hasDerivAt_of_tendsto hderiv ((hint1.const_mul z).add hint2)
    (tendsto_cexp_mul_gaussPolyAtom Q hz).1 (tendsto_cexp_mul_gaussPolyAtom Q hz).2
  rw [integral_add (hint1.const_mul z) hint2, integral_const_mul, sub_zero] at h
  linear_combination h

theorem integral_cexp_mul_gaussPolyAtom_iter (Q : ℝ[X]) {z : ℂ} (hz : -3 < z.re) (j : ℕ) :
    (∫ y : ℝ, Complex.exp (z * y) * (gaussPolyAtom (gaussPolyAtomIter Q j) y : ℂ)) =
      (-z) ^ j * ∫ y : ℝ, Complex.exp (z * y) * (gaussPolyAtom Q y : ℂ) := by
  induction j with
  | zero => simp [gaussPolyAtomIter]
  | succ j ih =>
    rw [gaussPolyAtomIter, Function.iterate_succ_apply', ← gaussPolyAtomIter,
      integral_cexp_mul_gaussPolyAtom_step _ hz, ih, pow_succ]
    ring

/-- `ℒφ(z) = −G(z)` on `Re z > −3`. -/
theorem integral_cexp_mul_cutoffAtom {z : ℂ} (hz : -3 < z.re) :
    (∫ y : ℝ, Complex.exp (z * y) * (gaussPolyAtom cutoffAtomPoly y : ℂ)) = -commutatorGammaFactor z := by
  have h := integral_cexp_mul_thetaFluxTerm (d := 1) one_pos hz
  have hfun : (fun y : ℝ => Complex.exp (z * y) * (gaussPolyAtom cutoffAtomPoly y : ℂ)) =
      fun y : ℝ => -(Complex.exp (z * y) * (thetaFluxTerm y 1 : ℂ)) := by
    funext y
    have := thetaFluxTerm_eq_neg_atom (d := 1) one_pos y
    simp only [ArithmeticFunction.moebius_apply_one, Int.cast_one, one_mul, moebiusInvWeight,
      Nat.cast_one, inv_one, Real.log_one, add_zero] at this
    rw [this]; push_cast; ring
  rw [hfun, integral_neg, h]
  simp

/-- **Mellin law of a log-shift series.**  If `Σ_d |a_d| d^{−Re z} < ∞` and `e^{zy}f` is integrable,
then `∫ e^{zy} Σ_d a_d f(y + log d) dy = (Σ_d a_d d^{−z}) ∫ e^{zy} f`. -/
theorem integral_cexp_mul_logShiftSeries {a : ℕ → ℝ} (ha0 : a 0 = 0) {f : ℝ → ℝ}
    {z : ℂ} (hfint : Integrable fun y : ℝ => Complex.exp (z * y) * (f y : ℂ))
    (ha : Summable fun d : ℕ => |a d| * (d : ℝ) ^ (-z.re)) :
    Integrable (fun y : ℝ => Complex.exp (z * y) * (logShiftSeries a f y : ℂ)) ∧
      (∫ y : ℝ, Complex.exp (z * y) * (logShiftSeries a f y : ℂ)) =
        (∑' d : ℕ, (a d : ℂ) * (d : ℂ) ^ (-z)) * ∫ y : ℝ, Complex.exp (z * y) * (f y : ℂ) := by
  set F : ℕ → ℝ → ℂ := fun d y => Complex.exp (z * y) * ((a d * f (y + Real.log d) : ℝ) : ℂ)
  have hFint : ∀ d, Integrable (F d) := fun d => by
    have := (integrable_cexp_mul_comp_add (Real.log d) (G := fun y => (f y : ℂ)) hfint).const_mul (a d : ℂ)
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [F]; push_cast; ring
  set I : ℝ := ∫ y : ℝ, ‖Complex.exp (z * y) * (f y : ℂ)‖
  have hFnorm : ∀ d, 0 < d → (∫ y : ℝ, ‖F d y‖) = |a d| * (d : ℝ) ^ (-z.re) * I := by
    intro d hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hshift := integral_add_right_eq_self (μ := volume)
      (fun y : ℝ => ‖Complex.exp (z * y) * (f y : ℂ)‖) (Real.log d)
    have hpt : ∀ u : ℝ, ‖F d u‖ = |a d| * (d : ℝ) ^ (-z.re) *
        ‖Complex.exp (z * (((u + Real.log d : ℝ)) : ℂ)) * (f (u + Real.log d) : ℂ)‖ := by
      intro u
      simp only [F]
      rw [norm_cexp_mul_real_weight, norm_cexp_mul_real_weight, abs_mul, Real.rpow_def_of_pos hdR]
      have : Real.exp (z.re * u) = Real.exp (Real.log d * -z.re) * Real.exp (z.re * (u + Real.log d)) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]; ring
    simp_rw [hpt]
    rw [integral_const_mul, hshift]
  have hsum : Summable fun d => ∫ y : ℝ, ‖F d y‖ := by
    refine (ha.mul_right I).congr fun d => ?_
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [F, ha0]
    · rw [hFnorm d hd]
  have hfun : (fun y : ℝ => Complex.exp (z * y) * (logShiftSeries a f y : ℂ)) =
      fun y => ∑' d, F d y := by
    funext y
    simp only [F, logShiftSeries]
    rw [Complex.ofReal_tsum, tsum_mul_left]
  have hInt : ∀ d, 0 < d → (∫ y, F d y) = (a d : ℂ) * (d : ℂ) ^ (-z) *
      ∫ y : ℝ, Complex.exp (z * y) * (f y : ℂ) := by
    intro d hd
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have h1 : (fun y => F d y) = fun y : ℝ => (a d : ℂ) *
        (Complex.exp (z * y) * (f (y + Real.log d) : ℂ)) := by
      funext y; simp only [F]; push_cast; ring
    rw [h1, integral_const_mul, integral_cexp_mul_comp_add z (Real.log d) (fun y => (f y : ℂ)),
      natCast_cpow_eq_cexp_mul_log hd]
    ring_nf
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm hFint hsum
  · rw [hfun, ← (hasSum_integral_of_summable_integral_norm hFint hsum).tsum_eq, ← tsum_mul_right]
    refine tsum_congr fun d => ?_
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [F, ha0]
    · exact hInt d hd

theorem summable_abs_moebiusInvWeight_mul_rpow {σ : ℝ} (hσ : 0 < σ) :
    Summable fun d : ℕ => |moebiusInvWeight d| * (d : ℝ) ^ (-σ) := by
  refine Summable.of_nonneg_of_le (fun d => by positivity) (fun d => ?_)
    (Real.summable_nat_rpow.2 (show -(1 + σ) < -1 by linarith))
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [moebiusInvWeight]; exact Real.rpow_nonneg le_rfl _
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hμ : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [moebiusInvWeight, abs_mul, abs_inv, Nat.abs_cast]
  calc |(ArithmeticFunction.moebius d : ℝ)| * (d : ℝ)⁻¹ * (d : ℝ) ^ (-σ)
      ≤ 1 * (d : ℝ)⁻¹ * (d : ℝ) ^ (-σ) := by gcongr
    _ = (d : ℝ) ^ (-(1 + σ)) := by
        rw [one_mul, ← Real.rpow_neg_one, ← Real.rpow_add hdR]; ring_nf

theorem tsum_moebiusInvWeight_mul_cpow {z : ℂ} (hz : 0 < z.re) :
    (∑' d : ℕ, (moebiusInvWeight d : ℂ) * (d : ℂ) ^ (-z)) = (riemannZeta (1 + z))⁻¹ := by
  rw [← tsum_moebius_mul_natCast_cpow (s := 1 + z) (by simp; linarith)]
  refine tsum_congr fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [moebiusInvWeight]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [moebiusInvWeight, neg_add, Complex.cpow_add _ _ hdC, Complex.cpow_neg_one]
  push_cast
  ring

/-- **Mellin law of every derivative of `C`.**  `ℒ(C^{(j)})(z) = −(−z)^j G(z)/ζ(1+z)`, `Re z > 0`. -/
theorem integral_cexp_mul_iteratedDeriv_cofinalBoundaryProfile (j : ℕ) {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun y : ℝ => Complex.exp (z * y) * ((iteratedDeriv j cofinalBoundaryProfile y : ℝ) : ℂ)) ∧
      (∫ y : ℝ, Complex.exp (z * y) * ((iteratedDeriv j cofinalBoundaryProfile y : ℝ) : ℂ)) =
        -((-z) ^ j * commutatorGammaFactor z * (riemannZeta (1 + z))⁻¹) := by
  rw [iteratedDeriv_cofinalBoundaryProfile]
  obtain ⟨hint, hval⟩ := integral_cexp_mul_logShiftSeries (by simp [moebiusInvWeight])
    (integrable_cexp_mul_gaussPolyAtom (cutoffDerivPoly j) (by linarith))
    (summable_abs_moebiusInvWeight_mul_rpow hz)
  refine ⟨hint, ?_⟩
  rw [hval, tsum_moebiusInvWeight_mul_cpow hz, cutoffDerivPoly,
    integral_cexp_mul_gaussPolyAtom_iter _ (by linarith), integral_cexp_mul_cutoffAtom (by linarith)]
  ring

end

end RHTower
