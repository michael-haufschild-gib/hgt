import GaloisForLFunctions.HTGeometry.NewtonSlopeTransform
import Mathlib.Algebra.Polynomial.Taylor

/-!
# Newton's lemma with a defect

Hensel's lemma lifts a root whose derivative is a unit.  When the derivative vanishes to order `r`
the root still lifts, provided the value vanishes to order strictly more than `2r`: this is Newton's
lemma with defect `r`, the exact power-series analogue of `|F(y₀)| < |F′(y₀)|²`.

The proof removes the defect rather than repeating the iteration.  Substituting
`y = y₀ + X^{r+1} Z` and dividing the resulting polynomial by `X^{2r+1}` produces a polynomial in
`Z` whose reduction at `X = 0` is *linear with unit slope* — the defect has been absorbed into the
substitution — so the ordinary Hensel statement applies to it.  Concretely the reduced polynomial is
`α + ū Z`, where `α` is the constant term of `F(y₀)/X^{2r+1}` and `ū` the constant term of the unit
in `F′(y₀) = X^r · u`; the division is `polyShiftPow`, the substitution is `shiftScale`, and the
lifting is the divisor form of Hensel's lemma applied to the linear divisor `Z - z₀`.

Nothing here is monic: the polynomial obtained after dividing by `X^{2r+1}` never is, which is why
the divisor form — which does not assume `f` monic — is the right tool.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

variable {R : Type*} [CommRing R]

/-! ## Dividing the coefficients of a polynomial by a power of the variable -/

@[simp]
theorem shiftPow_zero' (k : ℕ) : shiftPow k (0 : PowerSeries R) = 0 := by
  ext n
  rw [coeff_shiftPow, map_zero, map_zero]

theorem shiftPow_X_pow_mul (k : ℕ) (ψ : PowerSeries R) :
    shiftPow k ((PowerSeries.X : PowerSeries R) ^ k * ψ) = ψ := by
  ext n
  rw [coeff_shiftPow, PowerSeries.coeff_X_pow_mul]

/-- Divide every coefficient of a polynomial over a power-series ring by `X ^ k`. -/
noncomputable def polyShiftPow (k : ℕ) (G : (PowerSeries R)[X]) : (PowerSeries R)[X] :=
  ∑ i ∈ Finset.range (G.natDegree + 1), Polynomial.C (shiftPow k (G.coeff i)) * Polynomial.X ^ i

@[simp]
theorem coeff_polyShiftPow (k : ℕ) (G : (PowerSeries R)[X]) (i : ℕ) :
    (polyShiftPow k G).coeff i = shiftPow k (G.coeff i) := by
  classical
  rw [polyShiftPow, Polynomial.finsetSum_coeff]
  by_cases hi : i ≤ G.natDegree
  · rw [Finset.sum_eq_single i]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hb), mul_zero]
    · intro hcon
      exact absurd (Finset.mem_range.2 (by omega)) hcon
  · have hzero : G.coeff i = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hzero, shiftPow_zero']
    refine Finset.sum_eq_zero fun b hb => ?_
    have hbd : b < G.natDegree + 1 := Finset.mem_range.1 hb
    have hne : i ≠ b := by omega
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]

theorem C_X_pow_mul_polyShiftPow {k : ℕ} {G : (PowerSeries R)[X]}
    (hdvd : ∀ i, (PowerSeries.X : PowerSeries R) ^ k ∣ G.coeff i) :
    Polynomial.C ((PowerSeries.X : PowerSeries R) ^ k) * polyShiftPow k G = G := by
  ext i
  rw [Polynomial.coeff_C_mul, coeff_polyShiftPow, X_pow_mul_shiftPow (hdvd i)]

/-! ## Substituting `y₀ + h · Z` -/

/-- The polynomial `Z ↦ F (y₀ + h · Z)`. -/
noncomputable def shiftScale (F : (PowerSeries R)[X]) (y₀ h : PowerSeries R) : (PowerSeries R)[X] :=
  ∑ k ∈ Finset.range ((Polynomial.taylor y₀ F).natDegree + 1),
    Polynomial.C ((Polynomial.taylor y₀ F).coeff k * h ^ k) * Polynomial.X ^ k

theorem coeff_shiftScale (F : (PowerSeries R)[X]) (y₀ h : PowerSeries R) (k : ℕ) :
    (shiftScale F y₀ h).coeff k = (Polynomial.taylor y₀ F).coeff k * h ^ k := by
  classical
  rw [shiftScale, Polynomial.finsetSum_coeff]
  by_cases hk : k ≤ (Polynomial.taylor y₀ F).natDegree
  · rw [Finset.sum_eq_single k]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hb), mul_zero]
    · intro hcon
      exact absurd (Finset.mem_range.2 (by omega)) hcon
  · have hzero : (Polynomial.taylor y₀ F).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hzero, zero_mul]
    refine Finset.sum_eq_zero fun b hb => ?_
    have hbd : b < (Polynomial.taylor y₀ F).natDegree + 1 := Finset.mem_range.1 hb
    have hne : k ≠ b := by omega
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]

theorem eval_shiftScale (F : (PowerSeries R)[X]) (y₀ h z : PowerSeries R) :
    (shiftScale F y₀ h).eval z = F.eval (y₀ + h * z) := by
  have hT : (Polynomial.taylor y₀ F).eval (h * z) = F.eval (h * z + y₀) := by
    rw [Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_C]
  have hsum : ∀ k ∈ Finset.range ((Polynomial.taylor y₀ F).natDegree + 1),
      (Polynomial.C ((Polynomial.taylor y₀ F).coeff k * h ^ k) * Polynomial.X ^ k).eval z
        = (Polynomial.taylor y₀ F).coeff k * (h * z) ^ k := by
    intro k _
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_pow]
    ring
  rw [shiftScale, Polynomial.eval_finsetSum, Finset.sum_congr rfl hsum,
    ← Polynomial.eval_eq_sum_range, hT, add_comm]

/-! ## The derivative at a linear divisor -/

/-- The quotient by `X - a`, evaluated at `a`, is the derivative at `a`. -/
theorem eval_divByMonic_X_sub_C {S : Type*} [CommRing S] (p : S[X]) (a : S) :
    (p /ₘ ((X : S[X]) - Polynomial.C a)).eval a = (Polynomial.derivative p).eval a := by
  have hdecomp : p = ((X : S[X]) - Polynomial.C a) * (p /ₘ ((X : S[X]) - Polynomial.C a))
      + Polynomial.C (p.eval a) := by
    conv_lhs => rw [← Polynomial.modByMonic_add_div p ((X : S[X]) - Polynomial.C a)]
    rw [Polynomial.modByMonic_X_sub_C_eq_C_eval]
    ring
  have hderiv := congrArg Polynomial.derivative hdecomp
  rw [Polynomial.derivative_add, Polynomial.derivative_C, add_zero, Polynomial.derivative_mul,
    Polynomial.derivative_sub, Polynomial.derivative_X, Polynomial.derivative_C, sub_zero,
    one_mul] at hderiv
  have heval := congrArg (Polynomial.eval a) hderiv
  simpa using heval

/-! ## Newton's lemma with defect -/

/-- **Newton's lemma with defect `r`.**  If `F'(y₀) = X ^ r · unit` and `F(y₀)` vanishes to order at
least `2r + 1`, then `F` has a root congruent to `y₀` modulo `X ^ (r+1)`. -/
theorem exists_isRoot_of_defect [Nontrivial R] {F : (PowerSeries R)[X]} {y₀ u : PowerSeries R}
    {r : ℕ} (hu : IsUnit u)
    (hderiv : (Polynomial.derivative F).eval y₀ = (PowerSeries.X : PowerSeries R) ^ r * u)
    (hval : (PowerSeries.X : PowerSeries R) ^ (2 * r + 1) ∣ F.eval y₀) :
    ∃ y : PowerSeries R, F.IsRoot y ∧
      (PowerSeries.X : PowerSeries R) ^ (r + 1) ∣ (y - y₀) := by
  classical
  -- the substituted polynomial and its division by `X ^ (2r+1)`
  have hXsum : (PowerSeries.X : PowerSeries R) ^ r * (PowerSeries.X : PowerSeries R) ^ (r + 1)
      = (PowerSeries.X : PowerSeries R) ^ (2 * r + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hdvd : ∀ k, (PowerSeries.X : PowerSeries R) ^ (2 * r + 1) ∣
      (shiftScale F y₀ ((PowerSeries.X : PowerSeries R) ^ (r + 1))).coeff k := by
    intro k
    rw [coeff_shiftScale]
    match k with
    | 0 =>
        rw [pow_zero, mul_one, Polynomial.taylor_coeff_zero]
        exact hval
    | 1 =>
        rw [pow_one, Polynomial.taylor_coeff_one, hderiv]
        exact ⟨u, by rw [← hXsum]; ring⟩
    | (k + 2) =>
        rw [← pow_mul]
        refine Dvd.dvd.mul_left (pow_dvd_pow _ ?_) _
        have h1 : (r + 1) * 2 ≤ (r + 1) * (k + 2) := Nat.mul_le_mul_left _ (by omega)
        omega
  have hGH := C_X_pow_mul_polyShiftPow hdvd
  -- the reduction of the quotient is linear with unit slope
  have hH1 : (polyShiftPow (2 * r + 1)
      (shiftScale F y₀ ((PowerSeries.X : PowerSeries R) ^ (r + 1)))).coeff 1 = u := by
    rw [coeff_polyShiftPow, coeff_shiftScale, pow_one, Polynomial.taylor_coeff_one, hderiv]
    have hrw : (PowerSeries.X : PowerSeries R) ^ r * u * (PowerSeries.X : PowerSeries R) ^ (r + 1)
        = (PowerSeries.X : PowerSeries R) ^ (2 * r + 1) * u := by
      rw [← hXsum]; ring
    rw [hrw, shiftPow_X_pow_mul]
  have hHk : ∀ k, PowerSeries.constantCoeff (R := R) ((polyShiftPow (2 * r + 1)
      (shiftScale F y₀ ((PowerSeries.X : PowerSeries R) ^ (r + 1)))).coeff (k + 2)) = 0 := by
    intro k
    rw [coeff_polyShiftPow, constantCoeff_shiftPow, coeff_shiftScale, ← pow_mul]
    have hbig : (PowerSeries.X : PowerSeries R) ^ (2 * r + 2) ∣
        (Polynomial.taylor y₀ F).coeff (k + 2) *
          (PowerSeries.X : PowerSeries R) ^ ((r + 1) * (k + 2)) := by
      refine Dvd.dvd.mul_left (pow_dvd_pow _ ?_) _
      have h1 : (r + 1) * 2 ≤ (r + 1) * (k + 2) := Nat.mul_le_mul_left _ (by omega)
      omega
    rw [PowerSeries.X_pow_dvd_iff] at hbig
    exact hbig (2 * r + 1) (by omega)
  set H : (PowerSeries R)[X] :=
    polyShiftPow (2 * r + 1) (shiftScale F y₀ ((PowerSeries.X : PowerSeries R) ^ (r + 1))) with hHdef
  set α : R := PowerSeries.constantCoeff (R := R) (H.coeff 0) with hα
  obtain ⟨w, hw⟩ : ∃ w : R, w * PowerSeries.constantCoeff (R := R) u = 1 := by
    obtain ⟨v, hv⟩ := (hu.map (PowerSeries.constantCoeff (R := R)))
    exact ⟨↑v⁻¹, by rw [← hv]; simp⟩
  have hHbar : H.map (PowerSeries.constantCoeff (R := R))
      = Polynomial.C α + Polynomial.C (PowerSeries.constantCoeff (R := R) u) * Polynomial.X := by
    ext n
    rw [Polynomial.coeff_map]
    match n with
    | 0 => simp [hα]
    | 1 => rw [hH1]; simp
    | (n + 2) => rw [hHk n]; simp
  -- the linear divisor
  set z₀ : PowerSeries R := PowerSeries.C (-(w * α)) with hz₀
  have hz₀c : PowerSeries.constantCoeff (R := R) z₀ = -(w * α) := by
    rw [hz₀, PowerSeries.constantCoeff_C]
  have hroot0 : PowerSeries.constantCoeff (R := R) (H.eval z₀) = 0 := by
    rw [constantCoeff_eval, hHbar, hz₀c]
    rw [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    calc α + PowerSeries.constantCoeff (R := R) u * -(w * α)
        = α - (w * PowerSeries.constantCoeff (R := R) u) * α := by ring
      _ = 0 := by rw [hw, one_mul, sub_self]
  have hmod : CoeffMem (Ideal.span {(PowerSeries.X : PowerSeries R)}) (H %ₘ ((X :
      (PowerSeries R)[X]) - Polynomial.C z₀)) := by
    rw [Polynomial.modByMonic_X_sub_C_eq_C_eval]
    intro i
    rw [Polynomial.coeff_C]
    split
    · rw [mem_span_X_iff]
      exact hroot0
    · exact Submodule.zero_mem _
  -- the complementary quotient is invertible
  have hQ : (H /ₘ ((X : (PowerSeries R)[X]) - Polynomial.C z₀)).eval z₀
      = (Polynomial.derivative H).eval z₀ := eval_divByMonic_X_sub_C H z₀
  have hQunit : IsUnit ((H /ₘ ((X : (PowerSeries R)[X]) - Polynomial.C z₀)).eval z₀) := by
    rw [hQ, PowerSeries.isUnit_iff_constantCoeff, constantCoeff_eval, ← Polynomial.derivative_map,
      hHbar]
    rw [Polynomial.derivative_add, Polynomial.derivative_C, zero_add, Polynomial.derivative_C_mul,
      Polynomial.derivative_X, mul_one, Polynomial.eval_C]
    exact hu.map _
  obtain ⟨V, hV⟩ := hQunit
  obtain ⟨s, hs⟩ : ((X : (PowerSeries R)[X]) - Polynomial.C z₀) ∣
      (Polynomial.C ((↑V⁻¹ : PowerSeries R)) *
        (H /ₘ ((X : (PowerSeries R)[X]) - Polynomial.C z₀)) - 1) := by
    refine (Polynomial.dvd_iff_isRoot (a := z₀)).2 ?_
    rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_one, ← hV]
    simp
  have hbez : CoeffMem (Ideal.span {(PowerSeries.X : PowerSeries R)})
      (Polynomial.C ((↑V⁻¹ : PowerSeries R)) *
        (H /ₘ ((X : (PowerSeries R)[X]) - Polynomial.C z₀)) +
        (-s) * ((X : (PowerSeries R)[X]) - Polynomial.C z₀) - 1) := by
    have hz : Polynomial.C ((↑V⁻¹ : PowerSeries R)) *
        (H /ₘ ((X : (PowerSeries R)[X]) - Polynomial.C z₀)) +
        (-s) * ((X : (PowerSeries R)[X]) - Polynomial.C z₀) - 1 = 0 := by
      linear_combination hs
    rw [hz]
    exact coeffMem_zero
  obtain ⟨g, hgm, hgdeg, hgdvd, -⟩ :=
    exists_monic_dvd_of_coeffMem_modByMonic (Ideal.span {(PowerSeries.X : PowerSeries R)})
      (monic_X_sub_C z₀) hmod hbez
  -- a monic divisor of degree one is `X - C z`
  have hgnat : g.natDegree = 1 := by
    rw [Polynomial.natDegree_eq_of_degree_eq hgdeg, Polynomial.natDegree_X_sub_C]
  have hgz : g = (X : (PowerSeries R)[X]) - Polynomial.C (-(g.coeff 0)) := by
    rw [map_neg, sub_neg_eq_add]
    exact hgm.eq_X_add_C hgnat
  have hHz : Polynomial.eval (-(g.coeff 0)) H = 0 := by
    have hroot : H.IsRoot (-(g.coeff 0)) := by
      rw [← Polynomial.dvd_iff_isRoot, ← hgz]
      exact hgdvd
    exact hroot
  refine ⟨y₀ + (PowerSeries.X : PowerSeries R) ^ (r + 1) * (-(g.coeff 0)), ?_, ?_⟩
  · rw [Polynomial.IsRoot, ← eval_shiftScale F y₀ ((PowerSeries.X : PowerSeries R) ^ (r + 1)),
      ← hGH, Polynomial.eval_mul, Polynomial.eval_C, hHz, mul_zero]
  · exact ⟨-(g.coeff 0), by ring⟩

end GaloisForLFunctions.HTGeometry
