import GaloisForLFunctions.HTGeometry.NewtonSlopeTransform
import Mathlib.Algebra.Polynomial.Taylor

/-!
# The Tschirnhaus shift

Translating the variable of a monic polynomial changes its second coefficient by `deg f` times the
translation, so in characteristic zero the second coefficient can always be removed.  This is what
makes the Newton–Puiseux iteration terminate: with a vanishing second coefficient, an edge
polynomial can never be a single linear factor raised to the full degree, so its distinct roots
genuinely split the polynomial.

The translation is `Polynomial.taylor`, and the second coefficient is computed from
`Polynomial.taylor_coeff` together with the two surviving terms of the Hasse derivative of order
`deg f − 1`.

Everything about the translation itself — monicity, degree, roots, and reduction — holds over any
commutative ring; only the removal of the second coefficient needs the degree to be invertible.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

/-! ## The Hasse derivative just below the degree -/

/-- **The Hasse derivative of order `deg f − 1` of a monic polynomial is linear**, with constant
term the second coefficient and slope the degree. -/
theorem hasseDeriv_natDegree_sub_one {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic) {e : ℕ}
    (he : f.natDegree = e + 1) :
    Polynomial.hasseDeriv e f
      = Polynomial.C (f.coeff e) + Polynomial.C ((e + 1 : ℕ) : R) * Polynomial.X := by
  ext n
  rw [Polynomial.hasseDeriv_coeff]
  match n with
  | 0 => simp
  | 1 =>
      have hch : (1 + e).choose e = e + 1 := by
        rw [Nat.add_comm]
        exact Nat.choose_succ_self_right e
      have hc : f.coeff (1 + e) = 1 := by
        rw [Nat.add_comm, ← he]
        exact hf.coeff_natDegree
      rw [hch, hc, mul_one]
      simp
  | (n + 2) =>
      have hz : f.coeff (n + 2 + e) = 0 := by
        refine Polynomial.coeff_eq_zero_of_natDegree_lt ?_
        omega
      rw [hz, mul_zero]
      simp [Polynomial.coeff_one]

/-- **Translation shifts the second coefficient by the degree times the translation.** -/
theorem taylor_coeff_natDegree_sub_one {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic) {e : ℕ}
    (he : f.natDegree = e + 1) (a : R) :
    (Polynomial.taylor a f).coeff e = f.coeff e + ((e + 1 : ℕ) : R) * a := by
  rw [Polynomial.taylor_coeff, hasseDeriv_natDegree_sub_one hf he, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]

/-- **The next-to-leading coefficient after translation, indexed by the degree.** -/
theorem taylor_coeff_pred {R : Type*} [CommRing R] {f : R[X]} {d : ℕ} (hd : 1 ≤ d)
    (hdeg : f.natDegree = d) (hf : f.Monic) {a : R} :
    (Polynomial.taylor a f).coeff (d - 1) = f.coeff (d - 1) + (d : R) * a := by
  have he : f.natDegree = (d - 1) + 1 := by rw [hdeg]; omega
  have hdd : (d - 1) + 1 = d := by omega
  rw [taylor_coeff_natDegree_sub_one hf he a, hdd]

/-- **Translation changes every coefficient by a multiple of the translation.**  The `k`-th
coefficient of the translate is the `k`-th Hasse derivative evaluated at `a`, and evaluation at `a`
differs from evaluation at `0` by a multiple of `a`. -/
theorem taylor_coeff_eq_add {R : Type*} [CommRing R] (f : R[X]) (a : R) (k : ℕ) :
    ∃ s : R, (Polynomial.taylor a f).coeff k = f.coeff k + a * s := by
  obtain ⟨s, hs⟩ := Polynomial.sub_dvd_eval_sub a 0 ((Polynomial.hasseDeriv k) f)
  refine ⟨s, ?_⟩
  have h0 : ((Polynomial.hasseDeriv k) f).eval 0 = f.coeff k := by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.hasseDeriv_coeff]
    simp
  rw [sub_zero, h0] at hs
  rw [Polynomial.taylor_coeff, ← hs]
  ring

/-! ## Translation preserves everything else -/

theorem monic_taylor {R : Type*} [CommRing R] {f : R[X]} (hf : f.Monic) (a : R) :
    (Polynomial.taylor a f).Monic := by
  rw [Polynomial.taylor_apply]
  exact hf.comp_X_add_C a

theorem isRoot_taylor_iff {R : Type*} [CommRing R] (f : R[X]) (a y : R) :
    (Polynomial.taylor a f).IsRoot y ↔ f.IsRoot (y + a) := by
  rw [Polynomial.taylor_apply, Polynomial.IsRoot, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C]
  rfl

theorem map_taylor {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (f : R[X]) (a : R) :
    (Polynomial.taylor a f).map φ = Polynomial.taylor (φ a) (f.map φ) := by
  rw [Polynomial.taylor_apply, Polynomial.taylor_apply, Polynomial.map_comp, Polynomial.map_add,
    Polynomial.map_X, Polynomial.map_C]

/-! ## Removing the second coefficient -/

variable {K : Type} [Field K]

/-- **The Tschirnhaus shift.**  When the degree is invertible, a translation removes the second
coefficient, and the translation is as small as the second coefficient itself — so a special fibre
equal to `X ^ d` survives the shift. -/
theorem exists_taylor_coeff_eq_zero {f : (PowerSeries K)[X]} (hf : f.Monic) {e : ℕ}
    (he : f.natDegree = e + 1) (hchar : ((e + 1 : ℕ) : K) ≠ 0) :
    ∃ a : PowerSeries K,
      PowerSeries.constantCoeff a
          = - PowerSeries.constantCoeff (f.coeff e) * (((e + 1 : ℕ) : K))⁻¹ ∧
        (Polynomial.taylor a f).coeff e = 0 := by
  classical
  refine ⟨- f.coeff e * PowerSeries.C (((e + 1 : ℕ) : K))⁻¹, ?_, ?_⟩
  · rw [map_mul, map_neg, PowerSeries.constantCoeff_C]
  · rw [taylor_coeff_natDegree_sub_one hf he]
    have hcast : (((e + 1 : ℕ) : PowerSeries K)) = PowerSeries.C (((e + 1 : ℕ) : K)) := by
      simp
    rw [hcast]
    have hinv : PowerSeries.C (((e + 1 : ℕ) : K)) * PowerSeries.C (((e + 1 : ℕ) : K))⁻¹
        = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hchar, map_one]
    calc f.coeff e + PowerSeries.C (((e + 1 : ℕ) : K)) *
            (- f.coeff e * PowerSeries.C (((e + 1 : ℕ) : K))⁻¹)
        = f.coeff e - (PowerSeries.C (((e + 1 : ℕ) : K)) *
            PowerSeries.C (((e + 1 : ℕ) : K))⁻¹) * f.coeff e := by ring
      _ = 0 := by rw [hinv, one_mul, sub_self]

end GaloisForLFunctions.HTGeometry
