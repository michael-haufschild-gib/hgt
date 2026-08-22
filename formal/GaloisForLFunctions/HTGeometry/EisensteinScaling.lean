import GaloisForLFunctions.HTGeometry.EisensteinUniform

/-!
# Eisenstein's theorem without an integrality hypothesis

The last hypothesis of the uniform statement — that the first `2r+1` coefficients of the root lie
in the base ring — is removed here.  Those coefficients are finitely many elements of the fraction
field, so a single `D ∈ A` clears all of them; and multiplying the *polynomial* by `(C D) ^ deg F`
puts the reduced polynomial's coefficients back into `A` without touching the root.

That is the point of scaling the polynomial rather than the root: multiplying by a nonzero constant
changes neither the roots nor the order of vanishing of the derivative, so no degree bookkeeping and
no characteristic hypothesis is needed — whereas scaling the root would require
`deg (derivative F) = deg F − 1`.

The conclusion carries the expected fixed extra factor `D`, which is the standard form of
Eisenstein's theorem: the denominators are `D · q ^ (2N)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

variable {K : Type*} [Field K]

/-! ## Closure properties of `A`-integral power series -/

theorem coeffMem_mul {A : Subring K} {f g : PowerSeries K}
    (hf : ∀ N, PowerSeries.coeff N f ∈ A) (hg : ∀ N, PowerSeries.coeff N g ∈ A) :
    ∀ N, PowerSeries.coeff N (f * g) ∈ A :=
  coeffBnd_zero_zero_iff.1
    (((coeffBnd_zero_zero_iff (A := A) (q := (1 : K))).2 hf).mul
      ((coeffBnd_zero_zero_iff (A := A) (q := (1 : K))).2 hg))

theorem coeffMem_pow {A : Subring K} {f : PowerSeries K}
    (hf : ∀ N, PowerSeries.coeff N f ∈ A) (i : ℕ) :
    ∀ N, PowerSeries.coeff N (f ^ i) ∈ A := by
  have h := ((coeffBnd_zero_zero_iff (A := A) (q := (1 : K))).2 hf).pow i
  rw [Nat.mul_zero] at h
  exact coeffBnd_zero_zero_iff.1 h

theorem coeffMem_C_pow {A : Subring K} {D : K} (hD : D ∈ A) (k : ℕ) :
    ∀ N, PowerSeries.coeff N ((PowerSeries.C D : PowerSeries K) ^ k) ∈ A := by
  intro N
  rw [← map_pow, PowerSeries.coeff_C]
  by_cases hN : N = 0
  · rw [if_pos hN]
    exact A.pow_mem hD _
  · rw [if_neg hN]
    exact A.zero_mem

/-- **Scaling an evaluation into the base ring.**  If the polynomial has `A`-coefficients and the
argument becomes `A`-integral after multiplication by `D`, then `(C D) ^ m` times the value is
`A`-integral, for any `m` at least the degree. -/
theorem coeffMem_C_pow_mul_eval {A : Subring K} {P : Polynomial (PowerSeries K)}
    (hP : ∀ i N, PowerSeries.coeff N (P.coeff i) ∈ A) {D : K} (hD : D ∈ A) {w : PowerSeries K}
    (hDw : ∀ N, PowerSeries.coeff N (PowerSeries.C D * w) ∈ A) {m : ℕ} (hm : P.natDegree ≤ m) :
    ∀ N, PowerSeries.coeff N ((PowerSeries.C D : PowerSeries K) ^ m * P.eval w) ∈ A := by
  intro N
  rw [Polynomial.eval_eq_sum_range, Finset.mul_sum, map_sum]
  refine A.sum_mem fun j hj => ?_
  have hjm : j ≤ m := by
    have hj' := Finset.mem_range.1 hj
    omega
  have hrw : (PowerSeries.C D : PowerSeries K) ^ m * (P.coeff j * w ^ j)
      = (PowerSeries.C D : PowerSeries K) ^ (m - j) * P.coeff j
        * ((PowerSeries.C D : PowerSeries K) * w) ^ j := by
    have hsp : (PowerSeries.C D : PowerSeries K) ^ m
        = (PowerSeries.C D : PowerSeries K) ^ (m - j) * (PowerSeries.C D : PowerSeries K) ^ j := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsp, mul_pow]
    ring
  rw [hrw]
  exact coeffMem_mul (coeffMem_mul (coeffMem_C_pow hD _) (hP j)) (coeffMem_pow hDw j) N

theorem coeffMem_C_pow_mul_taylor {A : Subring K} {F : Polynomial (PowerSeries K)}
    (hF : ∀ i N, PowerSeries.coeff N (F.coeff i) ∈ A) {D : K} (hD : D ∈ A) {a : PowerSeries K}
    (hDa : ∀ N, PowerSeries.coeff N (PowerSeries.C D * a) ∈ A) {m : ℕ} (hm : F.natDegree ≤ m) :
    ∀ i N, PowerSeries.coeff N
      ((PowerSeries.C D : PowerSeries K) ^ m * (Polynomial.taylor a F).coeff i) ∈ A := by
  intro i N
  rw [Polynomial.taylor_coeff]
  exact coeffMem_C_pow_mul_eval (coeffMem_hasseDeriv hF i) hD hDa
    (le_trans (Polynomial.natDegree_hasseDeriv_le F i) (le_trans (Nat.sub_le _ _) hm)) N

theorem coeffMem_C_pow_mul_defectPoly {A : Subring K} (r : ℕ) {F : Polynomial (PowerSeries K)}
    (hF : ∀ i N, PowerSeries.coeff N (F.coeff i) ∈ A) {D : K} (hD : D ∈ A) {y : PowerSeries K}
    (hDy : ∀ N, N < 2 * r + 1 → D * PowerSeries.coeff N y ∈ A) {m : ℕ} (hm : F.natDegree ≤ m) :
    ∀ i N, PowerSeries.coeff N
      ((PowerSeries.C D : PowerSeries K) ^ m * (defectPoly r F y).coeff i) ∈ A := by
  have hDy₀ : ∀ N, PowerSeries.coeff N
      (PowerSeries.C D * truncPS (2 * r + 1) y) ∈ A := by
    intro N
    rw [PowerSeries.coeff_C_mul, coeff_truncPS]
    by_cases hN : N < 2 * r + 1
    · rw [if_pos hN]
      exact hDy N hN
    · rw [if_neg hN, mul_zero]
      exact A.zero_mem
  have hkey : ∀ i M, PowerSeries.coeff M ((PowerSeries.C D : PowerSeries K) ^ m *
      ((Polynomial.taylor (truncPS (2 * r + 1) y) F).coeff i *
        ((PowerSeries.X : PowerSeries K) ^ (r + 1)) ^ i)) ∈ A := by
    intro i M
    have hcomm : (PowerSeries.C D : PowerSeries K) ^ m *
        ((Polynomial.taylor (truncPS (2 * r + 1) y) F).coeff i *
          ((PowerSeries.X : PowerSeries K) ^ (r + 1)) ^ i)
        = ((PowerSeries.X : PowerSeries K) ^ ((r + 1) * i)) *
          ((PowerSeries.C D : PowerSeries K) ^ m *
            (Polynomial.taylor (truncPS (2 * r + 1) y) F).coeff i) := by
      rw [← pow_mul]
      ring
    rw [hcomm]
    exact coeffMem_X_pow_mul (coeffMem_C_pow_mul_taylor hF hD hDy₀ hm i) _ M
  intro i N
  rw [defectPoly, coeff_polyShiftPow, coeff_shiftScale, ← map_pow, PowerSeries.coeff_C_mul,
    coeff_shiftPow]
  have hk := hkey i (N + (2 * r + 1))
  rw [← map_pow, PowerSeries.coeff_C_mul] at hk
  exact hk

/-! ## Clearing the first coefficients -/

/-- A single element of `A` clears the denominators of any finite set of coefficients. -/
private theorem exists_common_denominator {A : Subring K}
    (hfrac : ∀ x : K, ∃ d ∈ A, d ≠ 0 ∧ d * x ∈ A) (y : PowerSeries K) (n : ℕ) :
    ∃ D ∈ A, D ≠ 0 ∧ ∀ N, N < n → D * PowerSeries.coeff N y ∈ A := by
  classical
  choose d hdA hd0 hdy using fun N => hfrac (PowerSeries.coeff N y)
  refine ⟨∏ N ∈ Finset.range n, d N, A.prod_mem fun N _ => hdA N,
    Finset.prod_ne_zero_iff.2 fun N _ => hd0 N, ?_⟩
  intro N hN
  have hmem : N ∈ Finset.range n := Finset.mem_range.2 hN
  have hsplit : (∏ M ∈ Finset.range n, d M)
      = (∏ M ∈ (Finset.range n).erase N, d M) * d N :=
    (Finset.prod_erase_mul _ _ hmem).symm
  rw [hsplit, mul_assoc]
  exact A.mul_mem (A.prod_mem fun M _ => hdA M) (hdy N)

/-! ## Eisenstein's theorem, no integrality hypothesis -/

/-- **Eisenstein's theorem on algebraic power series, ramified case, unconditional form.** -/
theorem exists_coeff_mem_of_isRoot_of_pos_defect_of_frac {A : Subring K}
    (hfrac : ∀ x : K, ∃ d ∈ A, d ≠ 0 ∧ d * x ∈ A)
    {F : Polynomial (PowerSeries K)} (hF : ∀ i N, PowerSeries.coeff N (F.coeff i) ∈ A)
    {y : PowerSeries K} (hroot : F.eval y = 0) {r : ℕ} (hr0 : 0 < r)
    (hlow : ∀ j < r, PowerSeries.coeff j ((Polynomial.derivative F).eval y) = 0)
    (hr : PowerSeries.coeff r ((Polynomial.derivative F).eval y) ≠ 0) :
    ∃ q ∈ A, q ≠ 0 ∧ ∃ D ∈ A, D ≠ 0 ∧
      ∀ N, D * (q ^ (2 * N) * PowerSeries.coeff N y) ∈ A := by
  classical
  obtain ⟨D, hDA, hD0, hDy⟩ := exists_common_denominator hfrac y (2 * r + 1)
  obtain ⟨hz, hzd⟩ := isRoot_defectPoly_and_constantCoeff_deriv_ne_zero hroot hlow hr
  -- the scaled reduced polynomial has coefficients in `A`
  have hHmem : ∀ i N, PowerSeries.coeff N
      ((Polynomial.C ((PowerSeries.C D : PowerSeries K) ^ F.natDegree)
        * defectPoly r F y).coeff i) ∈ A := by
    intro i N
    rw [Polynomial.coeff_C_mul]
    exact coeffMem_C_pow_mul_defectPoly r hF hDA hDy le_rfl i N
  have hHroot : (Polynomial.C ((PowerSeries.C D : PowerSeries K) ^ F.natDegree)
      * defectPoly r F y).eval (defectRoot r y) = 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_C, hz, mul_zero]
  have hHderiv : PowerSeries.coeff 0
      ((Polynomial.derivative (Polynomial.C ((PowerSeries.C D : PowerSeries K) ^ F.natDegree)
        * defectPoly r F y)).eval (defectRoot r y)) ≠ 0 := by
    rw [Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C, ← map_pow,
      PowerSeries.coeff_C_mul]
    exact mul_ne_zero (pow_ne_zero _ hD0) hzd
  obtain ⟨q, hq, hq0, hbnd⟩ := exists_coeffBnd_of_isRoot hfrac hHmem hHroot hHderiv
    (by rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact constantCoeff_defectRoot hr0 y)
  refine ⟨q, hq, hq0, D, hDA, hD0, fun N => ?_⟩
  have hy_eq : y = truncPS (2 * r + 1) y
      + (PowerSeries.X : PowerSeries K) ^ (r + 1) * defectRoot r y := by
    rw [X_pow_mul_defectRoot]
    ring
  rw [hy_eq, map_add, mul_add, mul_add]
  refine A.add_mem ?_ ?_
  · by_cases hN : N < 2 * r + 1
    · rw [coeff_truncPS, if_pos hN]
      have hrw : D * (q ^ (2 * N) * PowerSeries.coeff N y)
          = q ^ (2 * N) * (D * PowerSeries.coeff N y) := by ring
      rw [hrw]
      exact A.mul_mem (A.pow_mem hq _) (hDy N hN)
    · rw [coeff_truncPS, if_neg hN, mul_zero, mul_zero]
      exact A.zero_mem
  · by_cases hN : N < r + 1
    · have hdvd : (PowerSeries.X : PowerSeries K) ^ (r + 1) ∣
          (PowerSeries.X : PowerSeries K) ^ (r + 1) * defectRoot r y := ⟨_, rfl⟩
      rw [PowerSeries.X_pow_dvd_iff] at hdvd
      rw [hdvd N hN, mul_zero, mul_zero]
      exact A.zero_mem
    · obtain ⟨M, hM⟩ : ∃ M, N = M + (r + 1) := ⟨N - (r + 1), by omega⟩
      subst hM
      rw [PowerSeries.coeff_X_pow_mul]
      obtain ⟨c, hc, hce⟩ := hbnd M
      have hexp : q ^ (2 * (M + (r + 1))) = q ^ (2 * (r + 1)) * q ^ (2 * M) := by
        rw [← pow_add]
        congr 1
        omega
      have hrw : D * (q ^ (2 * (M + (r + 1))) * PowerSeries.coeff M (defectRoot r y))
          = D * (q ^ (2 * (r + 1)) * (q ^ (2 * M) * PowerSeries.coeff M (defectRoot r y))) := by
        rw [hexp]
        ring
      rw [hrw, hce]
      exact A.mul_mem hDA (A.mul_mem (A.pow_mem hq _) (A.mul_mem (A.pow_mem hq 1) hc))

/-- **Eisenstein's theorem, unramified case, unconditional form.** -/
theorem exists_coeff_mem_of_isRoot_of_zero_defect_of_frac {A : Subring K}
    (hfrac : ∀ x : K, ∃ d ∈ A, d ≠ 0 ∧ d * x ∈ A)
    {F : Polynomial (PowerSeries K)} (hF : ∀ i N, PowerSeries.coeff N (F.coeff i) ∈ A)
    {y : PowerSeries K} (hroot : F.eval y = 0)
    (hr : PowerSeries.coeff 0 ((Polynomial.derivative F).eval y) ≠ 0) :
    ∃ q ∈ A, q ≠ 0 ∧ ∃ D ∈ A, D ≠ 0 ∧
      ∀ N, D * (q ^ (2 * N) * PowerSeries.coeff N y) ∈ A := by
  classical
  obtain ⟨D, hDA, hD0, hDy⟩ := exists_common_denominator hfrac y 1
  set a : PowerSeries K := PowerSeries.C (PowerSeries.coeff 0 y) with hadef
  have hDa : ∀ N, PowerSeries.coeff N (PowerSeries.C D * a) ∈ A := by
    intro N
    rw [PowerSeries.coeff_C_mul, hadef, PowerSeries.coeff_C]
    by_cases hN : N = 0
    · rw [if_pos hN]
      exact hDy 0 (by omega)
    · rw [if_neg hN, mul_zero]
      exact A.zero_mem
  have hshift : y - a + a = y := by ring
  have hHmem : ∀ i N, PowerSeries.coeff N
      ((Polynomial.C ((PowerSeries.C D : PowerSeries K) ^ F.natDegree)
        * Polynomial.taylor a F).coeff i) ∈ A := by
    intro i N
    rw [Polynomial.coeff_C_mul]
    exact coeffMem_C_pow_mul_taylor hF hDA hDa le_rfl i N
  have hHroot : (Polynomial.C ((PowerSeries.C D : PowerSeries K) ^ F.natDegree)
      * Polynomial.taylor a F).eval (y - a) = 0 := by
    rw [Polynomial.eval_mul, Polynomial.eval_C, eval_taylor, hshift, hroot, mul_zero]
  have hHderiv : PowerSeries.coeff 0
      ((Polynomial.derivative (Polynomial.C ((PowerSeries.C D : PowerSeries K) ^ F.natDegree)
        * Polynomial.taylor a F)).eval (y - a)) ≠ 0 := by
    rw [Polynomial.derivative_C_mul, Polynomial.eval_mul, Polynomial.eval_C, derivative_taylor,
      eval_taylor, hshift, ← map_pow, PowerSeries.coeff_C_mul]
    exact mul_ne_zero (pow_ne_zero _ hD0) hr
  have hy0' : PowerSeries.coeff 0 (y - a) = 0 := by
    rw [map_sub, hadef, PowerSeries.coeff_C, if_pos rfl, sub_self]
  obtain ⟨q, hq, hq0, hbnd⟩ := exists_coeffBnd_of_isRoot hfrac hHmem hHroot hHderiv hy0'
  refine ⟨q, hq, hq0, D, hDA, hD0, fun N => ?_⟩
  by_cases hN : N = 0
  · subst hN
    rw [Nat.mul_zero, pow_zero, one_mul]
    exact hDy 0 (by omega)
  · have hyN : PowerSeries.coeff N y = PowerSeries.coeff N (y - a) := by
      rw [map_sub, hadef, PowerSeries.coeff_C, if_neg hN, sub_zero]
    rw [hyN]
    obtain ⟨c, hc, hce⟩ := hbnd N
    rw [hce, pow_one]
    exact A.mul_mem hDA (A.mul_mem hq hc)

/-- **Eisenstein's theorem on algebraic power series.**  Let `A` be a subring of a field `K` whose
fraction field is `K`, let `F` be a polynomial whose coefficients are power series with coefficients
in `A`, and let `y` be a root of `F` at which the derivative does not vanish identically.  Then the
coefficients of `y` have geometrically bounded denominators:

`D · q ^ (2N) · y_N ∈ A`  for every `N`,

for some nonzero `q, D ∈ A`.  No hypothesis on `y` beyond being a root. -/
theorem exists_coeff_mem_of_isRoot_of_frac {A : Subring K}
    (hfrac : ∀ x : K, ∃ d ∈ A, d ≠ 0 ∧ d * x ∈ A)
    {F : Polynomial (PowerSeries K)} (hF : ∀ i N, PowerSeries.coeff N (F.coeff i) ∈ A)
    {y : PowerSeries K} (hroot : F.eval y = 0) {r : ℕ}
    (hlow : ∀ j < r, PowerSeries.coeff j ((Polynomial.derivative F).eval y) = 0)
    (hr : PowerSeries.coeff r ((Polynomial.derivative F).eval y) ≠ 0) :
    ∃ q ∈ A, q ≠ 0 ∧ ∃ D ∈ A, D ≠ 0 ∧
      ∀ N, D * (q ^ (2 * N) * PowerSeries.coeff N y) ∈ A := by
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    exact exists_coeff_mem_of_isRoot_of_zero_defect_of_frac hfrac hF hroot hr
  · exact exists_coeff_mem_of_isRoot_of_pos_defect_of_frac hfrac hF hroot hr0 hlow hr

end GaloisForLFunctions.HTGeometry
