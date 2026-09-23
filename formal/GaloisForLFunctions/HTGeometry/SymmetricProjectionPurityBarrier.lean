import GaloisForLFunctions.HTGeometry.PauliEdgeBlockNorms

/-!
# The purity barrier of a moment supported on a projection

A positive trace-one moment supported on the range of an orthogonal projection sits at
Hilbert--Schmidt distance exactly `Tr(M²) - 1/h` from the normalized projection, where `h` is the
rank: the cross term and the reference purity both equal `1/h`.

Cauchy--Schwarz for the Hilbert--Schmidt pairing against a projection carrying the support bounds
the purity from below by the reciprocal of that projection's rank.  Together these give the
square-root barrier: a moment supported on at most `q` states is at Hilbert--Schmidt distance at
least `sqrt(1/q - 1/h)` from the universal normalized projection.
-/

open scoped Matrix

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Purity

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The squared Hilbert--Schmidt norm is the trace of `Aᴴ A`. -/
theorem hsNormSq_eq_trace (A : Matrix n n ℂ) :
    ((hsNormSq A : ℝ) : ℂ) = (Aᴴ * A).trace := by
  classical
  rw [hsNormSq, Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_mul']

/-- **Cauchy--Schwarz for the Hilbert--Schmidt pairing.** -/
theorem abs_re_trace_le (A B : Matrix n n ℂ) :
    |(Aᴴ * B).trace.re| ≤ Real.sqrt (hsNormSq A) * Real.sqrt (hsNormSq B) := by
  classical
  have hentry : (Aᴴ * B).trace = ∑ i, ∑ j, (starRingEnd ℂ) (A j i) * B j i := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.conjTranspose_apply]
    rfl
  have hre : (Aᴴ * B).trace.re = ∑ i, ∑ j, ((starRingEnd ℂ) (A j i) * B j i).re := by
    rw [hentry, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => Complex.re_sum _ _
  have hbound : |(Aᴴ * B).trace.re| ≤ ∑ i, ∑ j, ‖A j i‖ * ‖B j i‖ := by
    rw [hre]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun i _ => ?_)
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun j _ => ?_)
    calc |((starRingEnd ℂ) (A j i) * B j i).re| ≤ ‖(starRingEnd ℂ) (A j i) * B j i‖ :=
          Complex.abs_re_le_norm _
      _ = ‖A j i‖ * ‖B j i‖ := by rw [norm_mul, RCLike.norm_conj]
  refine le_trans hbound ?_
  have hcs : (∑ i, ∑ j, ‖A j i‖ * ‖B j i‖) ^ (2 : ℕ) ≤ hsNormSq A * hsNormSq B := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (n × n))
      (fun p : n × n => ‖A p.2 p.1‖) (fun p : n × n => ‖B p.2 p.1‖)
    have hsum : (∑ i, ∑ j, ‖A j i‖ * ‖B j i‖)
        = ∑ p : n × n, ‖A p.2 p.1‖ * ‖B p.2 p.1‖ := by
      rw [Fintype.sum_prod_type]
    have hA : (∑ p : n × n, ‖A p.2 p.1‖ ^ (2 : ℕ)) = hsNormSq A := by
      rw [Fintype.sum_prod_type, hsNormSq]
    have hB : (∑ p : n × n, ‖B p.2 p.1‖ ^ (2 : ℕ)) = hsNormSq B := by
      rw [Fintype.sum_prod_type, hsNormSq]
    rw [hsum, ← hA, ← hB]
    exact h
  have hnn : 0 ≤ ∑ i, ∑ j, ‖A j i‖ * ‖B j i‖ :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  have hsq : Real.sqrt (hsNormSq A) * Real.sqrt (hsNormSq B)
      = Real.sqrt (hsNormSq A * hsNormSq B) :=
    (Real.sqrt_mul (hsNormSq_nonneg A) _).symm
  rw [hsq, show (∑ i, ∑ j, ‖A j i‖ * ‖B j i‖)
      = Real.sqrt ((∑ i, ∑ j, ‖A j i‖ * ‖B j i‖) ^ (2 : ℕ)) from (Real.sqrt_sq hnn).symm]
  exact Real.sqrt_le_sqrt hcs

/-- **The purity bound.**  A Hermitian trace-one matrix supported on a projection of rank `q` has
purity at least `1/q`. -/
theorem inv_le_hsNormSq_of_support (M P : Matrix n n ℂ) (hP : Pᴴ = P) (hPP : P * P = P)
    (hPM : P * M = M) (hM : M.trace = 1) {q : ℝ} (hq : 0 < q) (hPtrace : P.trace = (q : ℂ)) :
    q⁻¹ ≤ hsNormSq M := by
  classical
  have hPnorm : hsNormSq P = q := by
    have h : ((hsNormSq P : ℝ) : ℂ) = (q : ℂ) := by
      rw [hsNormSq_eq_trace, hP, hPP, hPtrace]
    exact_mod_cast h
  have hcross : (Pᴴ * M).trace.re = 1 := by
    rw [hP, hPM, hM]
    simp
  have hcs := abs_re_trace_le P M
  rw [hcross, hPnorm] at hcs
  have habs : (1 : ℝ) ≤ Real.sqrt q * Real.sqrt (hsNormSq M) := by
    calc (1 : ℝ) = |(1 : ℝ)| := (abs_one).symm
      _ ≤ Real.sqrt q * Real.sqrt (hsNormSq M) := hcs
  have hsq : Real.sqrt q * Real.sqrt (hsNormSq M) = Real.sqrt (q * hsNormSq M) :=
    (Real.sqrt_mul (le_of_lt hq) _).symm
  rw [hsq] at habs
  have hnnprod : (0 : ℝ) ≤ q * hsNormSq M :=
    mul_nonneg (le_of_lt hq) (hsNormSq_nonneg M)
  have hle : (1 : ℝ) ≤ q * hsNormSq M := by
    nlinarith [Real.sq_sqrt hnnprod, Real.sqrt_nonneg (q * hsNormSq M), habs]
  rw [inv_le_iff_one_le_mul₀ hq]
  linarith

/-- **The exact expansion `(22)`.**  The Hilbert--Schmidt distance of a supported trace-one moment
from the normalized projection is the purity minus the reference purity. -/
theorem hsNormSq_sub_normalized_projection (M P : Matrix n n ℂ) (hM : Mᴴ = M) (hP : Pᴴ = P)
    (hPP : P * P = P) (hPM : P * M = M) (hMtrace : M.trace = 1) {h : ℝ} (hh : 0 < h)
    (hPtrace : P.trace = (h : ℂ)) :
    hsNormSq (M - ((h : ℂ))⁻¹ • P) = hsNormSq M - h⁻¹ := by
  classical
  have hhC : ((h : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hh
  have hcross : (M * P).trace = 1 := by
    rw [Matrix.trace_mul_comm, hPM, hMtrace]
  have hkey : ((hsNormSq (M - ((h : ℂ))⁻¹ • P) : ℝ) : ℂ)
      = ((hsNormSq M : ℝ) : ℂ) - ((h : ℂ))⁻¹ := by
    rw [hsNormSq_eq_trace, hsNormSq_eq_trace]
    have hconj : (M - ((h : ℂ))⁻¹ • P)ᴴ = M - ((h : ℂ))⁻¹ • P := by
      rw [Matrix.conjTranspose_sub, hM, Matrix.conjTranspose_smul, hP]
      congr 1
      rw [star_inv₀, Complex.star_def, Complex.conj_ofReal]
    rw [hconj, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.trace_sub,
      Matrix.trace_sub, Matrix.trace_sub]
    have h1 : (((h : ℂ))⁻¹ • P * M).trace = ((h : ℂ))⁻¹ := by
      rw [Matrix.smul_mul, Matrix.trace_smul, hPM, hMtrace, smul_eq_mul, mul_one]
    have h2 : (M * ((h : ℂ))⁻¹ • P).trace = ((h : ℂ))⁻¹ := by
      rw [Matrix.mul_smul, Matrix.trace_smul, hcross, smul_eq_mul, mul_one]
    have h3 : ((((h : ℂ))⁻¹ • P) * (((h : ℂ))⁻¹ • P)).trace = ((h : ℂ))⁻¹ := by
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, hPP, hPtrace,
        smul_eq_mul, smul_eq_mul]
      field_simp
    have hMM : (M * M).trace = (Mᴴ * M).trace := by rw [hM]
    rw [h1, h2, h3, hMM]
    ring
  have hreal : ((hsNormSq M - h⁻¹ : ℝ) : ℂ) = ((hsNormSq M : ℝ) : ℂ) - ((h : ℂ))⁻¹ := by
    push_cast
    ring
  rw [← hreal] at hkey
  exact_mod_cast hkey

/-- **`(22)` and `(23)`.**  A trace-one moment supported on a rank-`q` projection inside a rank-`h`
one is at squared Hilbert--Schmidt distance at least `1/q - 1/h` from the normalized projection. -/
theorem hsNormSq_sub_normalized_projection_ge (M P Q : Matrix n n ℂ) (hM : Mᴴ = M) (hP : Pᴴ = P)
    (hPP : P * P = P) (hPM : P * M = M) (hMtrace : M.trace = 1) {h : ℝ} (hh : 0 < h)
    (hPtrace : P.trace = (h : ℂ)) (hQ : Qᴴ = Q) (hQQ : Q * Q = Q) (hQM : Q * M = M)
    {q : ℝ} (hq : 0 < q) (hQtrace : Q.trace = (q : ℂ)) :
    q⁻¹ - h⁻¹ ≤ hsNormSq (M - ((h : ℂ))⁻¹ • P) := by
  rw [hsNormSq_sub_normalized_projection M P hM hP hPP hPM hMtrace hh hPtrace]
  have := inv_le_hsNormSq_of_support M Q hQ hQQ hQM hMtrace hq hQtrace
  linarith


/-- **`(28)`.**  The symmetric dimension dominates `D^r / r!`. -/
theorem pow_le_factorial_mul_choose (D r : ℕ) (hD : 0 < D) :
    D ^ r ≤ r.factorial * (D + r - 1).choose r := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  have hasc : (d + 1).ascFactorial r = r.factorial * (d + r).choose r :=
    Nat.ascFactorial_eq_factorial_mul_choose d r
  have hpow : (d + 1) ^ r ≤ (d + 1).ascFactorial r := Nat.pow_succ_le_ascFactorial (d + 1) r
  have hidx : d + 1 + r - 1 = d + r := by omega
  rw [hidx, ← hasc]
  exact hpow

/-- **`(26)`.**  If the raw target bound of the capacity regime is nontrivial, the number of
supported states is below the symmetric dimension. -/
theorem lt_choose_of_capacity_bound (N D r : ℕ) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hD : 0 < D)
    (h : (N : ℝ) * (a ^ r)⁻¹ * ((r.factorial : ℝ) / (D : ℝ) ^ r) < 1) :
    (N : ℝ) < (((D + r - 1).choose r : ℕ) : ℝ) := by
  have hDR : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hfac : (0 : ℝ) < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
  have harp : (0 : ℝ) < a ^ r := by positivity
  have hDrp : (0 : ℝ) < (D : ℝ) ^ r := by positivity
  have hstep : (N : ℝ) < a ^ r * ((D : ℝ) ^ r / (r.factorial : ℝ)) := by
    rw [mul_assoc, ← lt_div_iff₀ (by positivity)] at h
    refine lt_of_lt_of_le h (le_of_eq ?_)
    field_simp
  have har1 : a ^ r ≤ 1 := pow_le_one₀ (le_of_lt ha) ha1
  have hchain : (N : ℝ) < (D : ℝ) ^ r / (r.factorial : ℝ) := by
    have hnn : 0 ≤ (D : ℝ) ^ r / (r.factorial : ℝ) := by positivity
    calc (N : ℝ) < a ^ r * ((D : ℝ) ^ r / (r.factorial : ℝ)) := hstep
      _ ≤ 1 * ((D : ℝ) ^ r / (r.factorial : ℝ)) := by
          exact mul_le_mul_of_nonneg_right har1 hnn
      _ = (D : ℝ) ^ r / (r.factorial : ℝ) := one_mul _
  have hnat : ((D ^ r : ℕ) : ℝ) ≤ ((r.factorial * (D + r - 1).choose r : ℕ) : ℝ) := by
    exact_mod_cast pow_le_factorial_mul_choose D r hD
  push_cast at hnat
  calc (N : ℝ) < (D : ℝ) ^ r / (r.factorial : ℝ) := hchain
    _ ≤ (((D + r - 1).choose r : ℕ) : ℝ) := by
        rw [div_le_iff₀ hfac]
        calc (D : ℝ) ^ r ≤ (r.factorial : ℝ) * (((D + r - 1).choose r : ℕ) : ℝ) := hnat
          _ = (((D + r - 1).choose r : ℕ) : ℝ) * (r.factorial : ℝ) := by ring

end Purity

end

end GaloisForLFunctions.HTGeometry
