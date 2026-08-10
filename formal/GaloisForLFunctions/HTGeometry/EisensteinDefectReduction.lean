import GaloisForLFunctions.HTGeometry.EisensteinSimpleRoot
import GaloisForLFunctions.HTGeometry.HenselDefectRoot

/-!
# Removing the defect from an algebraic power series

A root `y` whose derivative `F′(y)` vanishes to order `r` is turned into a root with a *simple*
derivative — nonzero constant term — by the same substitution that removes the defect in Newton's
lemma: write

`y = y₀ + t^{r+1} · z`,   `y₀` the truncation of `y` below degree `2r+1`,

and divide `F(y₀ + t^{r+1} Z)` by `t^{2r+1}`.  The quotient `H` has `H₁ = u`, where
`F′(y₀) = t^r · u` and `u` has nonzero constant term, and every higher coefficient of `H` has zero
constant term; so its reduction at `t = 0` is the linear polynomial `α + ū Z`, and `H′(z)` has
constant term `ū ≠ 0`.

This is the reduction of Eisenstein's theorem to its unramified case: `z` is a root of `H` with a
simple derivative, so `EisensteinSimpleRoot` applies to it, and `y = y₀ + t^{r+1} z` recovers `y`
from `z` with only a shift of indices.

Everything here happens over a field; no subring, no integrality.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

variable {K : Type*} [Field K]

/-- The reduced root: `z` with `y = y₀ + t^{r+1} z`. -/
noncomputable def defectRoot (r : ℕ) (y : PowerSeries K) : PowerSeries K :=
  shiftPow (r + 1) (y - truncPS (2 * r + 1) y)

/-- The polynomial `z` is a root of: `F(y₀ + t^{r+1} Z)` divided by `t^{2r+1}`. -/
noncomputable def defectPoly (r : ℕ) (F : Polynomial (PowerSeries K)) (y : PowerSeries K) :
    Polynomial (PowerSeries K) :=
  polyShiftPow (2 * r + 1)
    (shiftScale F (truncPS (2 * r + 1) y) ((PowerSeries.X : PowerSeries K) ^ (r + 1)))

theorem X_pow_mul_defectRoot (r : ℕ) (y : PowerSeries K) :
    (PowerSeries.X : PowerSeries K) ^ (r + 1) * defectRoot r y
      = y - truncPS (2 * r + 1) y := by
  refine X_pow_mul_shiftPow ?_
  refine dvd_trans (pow_dvd_pow _ (by omega)) (X_pow_dvd_sub_truncPS (2 * r + 1) y)

/-- **The defect substitution produces a simple root.** -/
theorem isRoot_defectPoly_and_constantCoeff_deriv_ne_zero {F : Polynomial (PowerSeries K)}
    {y : PowerSeries K} (hroot : F.eval y = 0) {r : ℕ}
    (hlow : ∀ j < r, PowerSeries.coeff j ((Polynomial.derivative F).eval y) = 0)
    (hr : PowerSeries.coeff r ((Polynomial.derivative F).eval y) ≠ 0) :
    (defectPoly r F y).eval (defectRoot r y) = 0 ∧
      PowerSeries.coeff 0
        ((Polynomial.derivative (defectPoly r F y)).eval (defectRoot r y)) ≠ 0 := by
  classical
  set y₀ : PowerSeries K := truncPS (2 * r + 1) y with hy₀
  have hbig : (PowerSeries.X : PowerSeries K) ^ (2 * r + 1) ∣ (y₀ - y) := by
    have hrw : y₀ - y = -(y - y₀) := by ring
    rw [hrw]
    exact dvd_neg.2 (X_pow_dvd_sub_truncPS (2 * r + 1) y)
  -- the derivative at the truncation agrees with the derivative at the root to high order
  have hagree : ∀ i < 2 * r + 1,
      PowerSeries.coeff i ((Polynomial.derivative F).eval y₀)
        = PowerSeries.coeff i ((Polynomial.derivative F).eval y) := by
    intro i hi
    have hdvd : (PowerSeries.X : PowerSeries K) ^ (2 * r + 1) ∣
        ((Polynomial.derivative F).eval y₀ - (Polynomial.derivative F).eval y) :=
      dvd_trans hbig (Polynomial.sub_dvd_eval_sub _ _ (Polynomial.derivative F))
    rw [PowerSeries.X_pow_dvd_iff] at hdvd
    have hz := hdvd i hi
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  -- so it is `X ^ r` times a series with nonzero constant term
  have hdvdr : (PowerSeries.X : PowerSeries K) ^ r ∣ (Polynomial.derivative F).eval y₀ := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [hagree m (by omega)]
    exact hlow m hm
  set u : PowerSeries K := shiftPow r ((Polynomial.derivative F).eval y₀) with hu
  have hufact : (Polynomial.derivative F).eval y₀ = (PowerSeries.X : PowerSeries K) ^ r * u :=
    (X_pow_mul_shiftPow hdvdr).symm
  have hucc : PowerSeries.constantCoeff (R := K) u
      = PowerSeries.coeff r ((Polynomial.derivative F).eval y) := by
    rw [hu, constantCoeff_shiftPow, hagree r (by omega)]
  have hune : PowerSeries.constantCoeff (R := K) u ≠ 0 := by rw [hucc]; exact hr
  -- the value at the truncation vanishes to order `2r+1`
  have hval : (PowerSeries.X : PowerSeries K) ^ (2 * r + 1) ∣ F.eval y₀ := by
    have hdvd : (PowerSeries.X : PowerSeries K) ^ (2 * r + 1) ∣ (F.eval y₀ - F.eval y) :=
      dvd_trans hbig (Polynomial.sub_dvd_eval_sub _ _ F)
    rwa [hroot, sub_zero] at hdvd
  -- every coefficient of the substituted polynomial is divisible by `X ^ (2r+1)`
  have hXsum : (PowerSeries.X : PowerSeries K) ^ r * (PowerSeries.X : PowerSeries K) ^ (r + 1)
      = (PowerSeries.X : PowerSeries K) ^ (2 * r + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hdvd : ∀ k, (PowerSeries.X : PowerSeries K) ^ (2 * r + 1) ∣
      (shiftScale F y₀ ((PowerSeries.X : PowerSeries K) ^ (r + 1))).coeff k := by
    intro k
    rw [coeff_shiftScale]
    match k with
    | 0 =>
        rw [pow_zero, mul_one, Polynomial.taylor_coeff_zero]
        exact hval
    | 1 =>
        rw [pow_one, Polynomial.taylor_coeff_one, hufact]
        exact ⟨u, by rw [← hXsum]; ring⟩
    | (k + 2) =>
        rw [← pow_mul]
        refine Dvd.dvd.mul_left (pow_dvd_pow _ ?_) _
        have h1 : (r + 1) * 2 ≤ (r + 1) * (k + 2) := Nat.mul_le_mul_left _ (by omega)
        omega
  have hGH : Polynomial.C ((PowerSeries.X : PowerSeries K) ^ (2 * r + 1)) * defectPoly r F y
      = shiftScale F y₀ ((PowerSeries.X : PowerSeries K) ^ (r + 1)) :=
    C_X_pow_mul_polyShiftPow hdvd
  -- the reduced root is a root of the quotient
  have hzero : (defectPoly r F y).eval (defectRoot r y) = 0 := by
    have hev : (shiftScale F y₀ ((PowerSeries.X : PowerSeries K) ^ (r + 1))).eval
        (defectRoot r y) = 0 := by
      rw [eval_shiftScale, X_pow_mul_defectRoot]
      have hy : y₀ + (y - y₀) = y := by ring
      rw [hy, hroot]
    rw [← hGH, Polynomial.eval_mul, Polynomial.eval_C] at hev
    exact (mul_eq_zero.mp hev).resolve_left (pow_ne_zero _ PowerSeries.X_ne_zero)
  refine ⟨hzero, ?_⟩
  -- the reduction of the quotient is linear with nonzero slope
  have hH1 : (defectPoly r F y).coeff 1 = u := by
    rw [defectPoly, coeff_polyShiftPow, coeff_shiftScale, pow_one, Polynomial.taylor_coeff_one,
      hufact]
    have hrw : (PowerSeries.X : PowerSeries K) ^ r * u * (PowerSeries.X : PowerSeries K) ^ (r + 1)
        = (PowerSeries.X : PowerSeries K) ^ (2 * r + 1) * u := by
      rw [← hXsum]; ring
    rw [hrw, shiftPow_X_pow_mul]
  have hHk : ∀ k, PowerSeries.constantCoeff (R := K) ((defectPoly r F y).coeff (k + 2)) = 0 := by
    intro k
    rw [defectPoly, coeff_polyShiftPow, constantCoeff_shiftPow, coeff_shiftScale, ← pow_mul]
    have hbig2 : (PowerSeries.X : PowerSeries K) ^ (2 * r + 2) ∣
        (Polynomial.taylor y₀ F).coeff (k + 2) *
          (PowerSeries.X : PowerSeries K) ^ ((r + 1) * (k + 2)) := by
      refine Dvd.dvd.mul_left (pow_dvd_pow _ ?_) _
      have h1 : (r + 1) * 2 ≤ (r + 1) * (k + 2) := Nat.mul_le_mul_left _ (by omega)
      omega
    rw [PowerSeries.X_pow_dvd_iff] at hbig2
    exact hbig2 (2 * r + 1) (by omega)
  have hHbar : (defectPoly r F y).map (PowerSeries.constantCoeff (R := K))
      = Polynomial.C (PowerSeries.constantCoeff (R := K) ((defectPoly r F y).coeff 0))
        + Polynomial.C (PowerSeries.constantCoeff (R := K) u) * Polynomial.X := by
    ext n
    rw [Polynomial.coeff_map]
    match n with
    | 0 => simp
    | 1 => rw [hH1]; simp
    | (n + 2) => rw [hHk n]; simp
  rw [PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_eval, ← Polynomial.derivative_map,
    hHbar, Polynomial.derivative_add,
    Polynomial.derivative_C, zero_add, Polynomial.derivative_C_mul, Polynomial.derivative_X,
    mul_one, Polynomial.eval_C]
  exact hune

/-- For a positive defect the reduced root has vanishing constant term, which is exactly the
normalisation the simple-root theorem asks for. -/
theorem constantCoeff_defectRoot {r : ℕ} (hr : 0 < r) (y : PowerSeries K) :
    PowerSeries.constantCoeff (R := K) (defectRoot r y) = 0 := by
  rw [defectRoot, constantCoeff_shiftPow]
  have hdvd := X_pow_dvd_sub_truncPS (2 * r + 1) y
  rw [PowerSeries.X_pow_dvd_iff] at hdvd
  exact hdvd (r + 1) (by omega)

/-- **The reduced polynomial keeps its coefficients in the base ring.**  Only the first `2r+1`
coefficients of `y` are involved, so a single common denominator clears them. -/
theorem coeffMem_defectPoly {A : Subring K} {q : K} (hq : q ∈ A) (r : ℕ)
    {F : Polynomial (PowerSeries K)} (hF : ∀ i N, PowerSeries.coeff N (F.coeff i) ∈ A)
    {y : PowerSeries K} (hy : ∀ N, N < 2 * r + 1 → PowerSeries.coeff N y ∈ A) :
    ∀ i N, PowerSeries.coeff N ((defectPoly r F y).coeff i) ∈ A := by
  have hy₀ : ∀ M, PowerSeries.coeff M (truncPS (2 * r + 1) y) ∈ A := by
    intro M
    rw [coeff_truncPS]
    by_cases hM : M < 2 * r + 1
    · rw [if_pos hM]
      exact hy M hM
    · rw [if_neg hM]
      exact A.zero_mem
  have htay : ∀ j M,
      PowerSeries.coeff M ((Polynomial.taylor (truncPS (2 * r + 1) y) F).coeff j) ∈ A := by
    intro j M
    rw [Polynomial.taylor_coeff]
    have hev := CoeffBnd.eval (A := A) (q := q) hq (κ := 0) (β := 0)
      (P := Polynomial.hasseDeriv j F)
      (fun i => coeffBnd_zero_zero_iff.2 (coeffMem_hasseDeriv hF j i))
      (coeffBnd_zero_zero_iff.2 hy₀)
    exact (coeffBnd_zero_zero_iff.1 hev) M
  intro i N
  rw [defectPoly, coeff_polyShiftPow, coeff_shiftScale]
  refine coeffMem_shiftPow (fun M => ?_) (2 * r + 1) N
  rw [← pow_mul, mul_comm]
  exact coeffMem_X_pow_mul (htay i) _ M

/-- **Eisenstein's theorem, ramified case.**  A root whose derivative vanishes to positive order
`r` still has geometrically bounded denominators, provided its first `2r+1` coefficients lie in the
base ring.  The reduction is the defect substitution; the bound is inherited from the reduced root
with a shift of `r+1` in the index. -/
theorem exists_coeff_mem_of_isRoot_of_pos_defect {A : Subring K}
    (hfrac : ∀ x : K, ∃ d ∈ A, d ≠ 0 ∧ d * x ∈ A)
    {F : Polynomial (PowerSeries K)} (hF : ∀ i N, PowerSeries.coeff N (F.coeff i) ∈ A)
    {y : PowerSeries K} (hroot : F.eval y = 0) {r : ℕ} (hr0 : 0 < r)
    (hlow : ∀ j < r, PowerSeries.coeff j ((Polynomial.derivative F).eval y) = 0)
    (hr : PowerSeries.coeff r ((Polynomial.derivative F).eval y) ≠ 0)
    (hy : ∀ N, N < 2 * r + 1 → PowerSeries.coeff N y ∈ A) :
    ∃ q ∈ A, q ≠ 0 ∧ ∀ N, q ^ (2 * N) * PowerSeries.coeff N y ∈ A := by
  obtain ⟨hz, hzd⟩ := isRoot_defectPoly_and_constantCoeff_deriv_ne_zero hroot hlow hr
  obtain ⟨q, hq, hq0, hbnd⟩ := exists_coeffBnd_of_isRoot hfrac
    (coeffMem_defectPoly (q := (1 : K)) A.one_mem r hF hy) hz hzd
    (by rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact constantCoeff_defectRoot hr0 y)
  refine ⟨q, hq, hq0, fun N => ?_⟩
  have hy_eq : y = truncPS (2 * r + 1) y
      + (PowerSeries.X : PowerSeries K) ^ (r + 1) * defectRoot r y := by
    rw [X_pow_mul_defectRoot]
    ring
  rw [hy_eq, map_add, mul_add]
  refine A.add_mem ?_ ?_
  · by_cases hN : N < 2 * r + 1
    · rw [coeff_truncPS, if_pos hN]
      exact A.mul_mem (A.pow_mem hq _) (hy N hN)
    · rw [coeff_truncPS, if_neg hN, mul_zero]
      exact A.zero_mem
  · by_cases hN : N < r + 1
    · have hdvd : (PowerSeries.X : PowerSeries K) ^ (r + 1) ∣
          (PowerSeries.X : PowerSeries K) ^ (r + 1) * defectRoot r y := ⟨_, rfl⟩
      rw [PowerSeries.X_pow_dvd_iff] at hdvd
      rw [hdvd N hN, mul_zero]
      exact A.zero_mem
    · obtain ⟨M, hM⟩ : ∃ M, N = M + (r + 1) := ⟨N - (r + 1), by omega⟩
      subst hM
      rw [PowerSeries.coeff_X_pow_mul]
      obtain ⟨c, hc, hce⟩ := hbnd M
      have hexp : q ^ (2 * (M + (r + 1))) = q ^ (2 * (r + 1)) * q ^ (2 * M) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hexp, mul_assoc, hce]
      exact A.mul_mem (A.pow_mem hq _) (A.mul_mem (A.pow_mem hq 1) hc)

end GaloisForLFunctions.HTGeometry
