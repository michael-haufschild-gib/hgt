import GaloisForLFunctions.HTGeometry.EisensteinDefectReduction
import GaloisForLFunctions.HTGeometry.TschirnhausShift

/-!
# Eisenstein's theorem, uniform statement

The simple-root case and the ramified case are joined here into one statement: a root of a
polynomial with power-series coefficients in a subring `A`, whose derivative does not vanish
identically, has coefficients with geometrically bounded denominators.

The simple case is reduced to the normalised one (`y₀ = 0`) by translating the root, which is
`Polynomial.taylor`; the translation is legitimate because the constant term of `y` lies in `A`,
so the translated polynomial still has `A`-coefficients.  The ramified case is the previous
module's reduction.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

variable {K : Type*} [Field K]

/-- Evaluating a translated polynomial. -/
theorem eval_taylor {S : Type*} [CommRing S] (F : Polynomial S) (a z : S) :
    (Polynomial.taylor a F).eval z = F.eval (z + a) := by
  rw [Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_C]

/-- Translation commutes with differentiation. -/
theorem derivative_taylor {S : Type*} [CommRing S] (a : S) (F : Polynomial S) :
    Polynomial.derivative (Polynomial.taylor a F)
      = Polynomial.taylor a (Polynomial.derivative F) := by
  rw [Polynomial.taylor_apply, Polynomial.taylor_apply, Polynomial.derivative_comp,
    Polynomial.derivative_add, Polynomial.derivative_X, Polynomial.derivative_C, add_zero,
    one_mul]

/-- Translating by an element of the base ring keeps the coefficients in the base ring. -/
theorem coeffMem_taylor {A : Subring K} {F : Polynomial (PowerSeries K)}
    (hF : ∀ i N, PowerSeries.coeff N (F.coeff i) ∈ A) {a : PowerSeries K}
    (ha : ∀ N, PowerSeries.coeff N a ∈ A) :
    ∀ i N, PowerSeries.coeff N ((Polynomial.taylor a F).coeff i) ∈ A := by
  intro i N
  rw [Polynomial.taylor_coeff]
  have hev := CoeffBnd.eval (A := A) (q := (1 : K)) A.one_mem (κ := 0) (β := 0)
    (P := Polynomial.hasseDeriv i F)
    (fun j => coeffBnd_zero_zero_iff.2 (coeffMem_hasseDeriv hF i j))
    (coeffBnd_zero_zero_iff.2 ha)
  exact (coeffBnd_zero_zero_iff.1 hev) N

/-- **Eisenstein's theorem, unramified case with an arbitrary constant term.** -/
theorem exists_coeff_mem_of_isRoot_of_zero_defect {A : Subring K}
    (hfrac : ∀ x : K, ∃ d ∈ A, d ≠ 0 ∧ d * x ∈ A)
    {F : Polynomial (PowerSeries K)} (hF : ∀ i N, PowerSeries.coeff N (F.coeff i) ∈ A)
    {y : PowerSeries K} (hroot : F.eval y = 0)
    (hr : PowerSeries.coeff 0 ((Polynomial.derivative F).eval y) ≠ 0)
    (hy0 : PowerSeries.coeff 0 y ∈ A) :
    ∃ q ∈ A, q ≠ 0 ∧ ∀ N, q ^ (2 * N) * PowerSeries.coeff N y ∈ A := by
  classical
  set a : PowerSeries K := PowerSeries.C (PowerSeries.coeff 0 y) with hadef
  have hamem : ∀ N, PowerSeries.coeff N a ∈ A := by
    intro N
    rw [hadef, PowerSeries.coeff_C]
    by_cases hN : N = 0
    · rw [if_pos hN]
      exact hy0
    · rw [if_neg hN]
      exact A.zero_mem
  have hshift : y - a + a = y := by ring
  have hroot' : (Polynomial.taylor a F).eval (y - a) = 0 := by
    rw [eval_taylor, hshift, hroot]
  have hderiv' : (Polynomial.derivative (Polynomial.taylor a F)).eval (y - a)
      = (Polynomial.derivative F).eval y := by
    rw [derivative_taylor, eval_taylor, hshift]
  have hy0' : PowerSeries.coeff 0 (y - a) = 0 := by
    rw [map_sub, hadef, PowerSeries.coeff_C, if_pos rfl, sub_self]
  obtain ⟨q, hq, hq0, hbnd⟩ := exists_coeffBnd_of_isRoot hfrac (coeffMem_taylor hF hamem) hroot'
    (by rw [hderiv']; exact hr) hy0'
  refine ⟨q, hq, hq0, fun N => ?_⟩
  by_cases hN : N = 0
  · subst hN
    rw [Nat.mul_zero, pow_zero, one_mul]
    exact hy0
  · have hyN : PowerSeries.coeff N y = PowerSeries.coeff N (y - a) := by
      rw [map_sub, hadef, PowerSeries.coeff_C, if_neg hN, sub_zero]
    rw [hyN]
    obtain ⟨c, hc, hce⟩ := hbnd N
    rw [hce, pow_one]
    exact A.mul_mem hq hc

/-- **Eisenstein's theorem on algebraic power series.**  A root of a polynomial with power-series
coefficients in `A`, whose derivative vanishes to finite order `r` at the root and whose first
`2r+1` coefficients lie in `A`, has geometrically bounded denominators. -/
theorem exists_coeff_mem_of_isRoot {A : Subring K}
    (hfrac : ∀ x : K, ∃ d ∈ A, d ≠ 0 ∧ d * x ∈ A)
    {F : Polynomial (PowerSeries K)} (hF : ∀ i N, PowerSeries.coeff N (F.coeff i) ∈ A)
    {y : PowerSeries K} (hroot : F.eval y = 0) {r : ℕ}
    (hlow : ∀ j < r, PowerSeries.coeff j ((Polynomial.derivative F).eval y) = 0)
    (hr : PowerSeries.coeff r ((Polynomial.derivative F).eval y) ≠ 0)
    (hy : ∀ N, N < 2 * r + 1 → PowerSeries.coeff N y ∈ A) :
    ∃ q ∈ A, q ≠ 0 ∧ ∀ N, q ^ (2 * N) * PowerSeries.coeff N y ∈ A := by
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    exact exists_coeff_mem_of_isRoot_of_zero_defect hfrac hF hroot hr (hy 0 (by omega))
  · exact exists_coeff_mem_of_isRoot_of_pos_defect hfrac hF hroot hr0 hlow hr hy

end GaloisForLFunctions.HTGeometry
