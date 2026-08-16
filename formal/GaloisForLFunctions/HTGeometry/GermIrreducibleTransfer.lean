import GaloisForLFunctions.HTGeometry.GermDistinguishedFactorization

/-!
# Irreducibility of a distinguished polynomial is irreducibility of its germ

A monic factor of `X^D` in `ℂ[X]` is a power of `X`: all its roots are roots of `X^D`, hence zero.
Applying the coefficientwise value map, a monic factor of a distinguished polynomial is therefore
distinguished.

Combined with the factorization transfer this makes irreducibility interchangeable: a distinguished
polynomial is irreducible in `ℂ{z'}[X]` exactly when its germ is irreducible in `ℂ{z}`.  This is the
step that lets the factorization theory of the germ ring be imported from the polynomial ring, where
Gauss applies to the inductive hypothesis on the dimension.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {n : ℕ}

/-- **A monic factor of a power of `X` is a power of `X`.** -/
theorem eq_X_pow_of_monic_of_mul_eq_X_pow {p q : Polynomial ℂ} (hp : p.Monic) {D : ℕ}
    (h : p * q = Polynomial.X ^ D) : p = Polynomial.X ^ p.natDegree := by
  classical
  have hroots : ∀ ρ ∈ p.roots, ρ = 0 := by
    intro ρ hρ
    have hev : p.eval ρ = 0 := (mem_roots hp.ne_zero).mp hρ
    have hXD : (Polynomial.X ^ D : Polynomial ℂ).eval ρ = 0 := by
      rw [← h, eval_mul, hev, zero_mul]
    rw [eval_pow, eval_X] at hXD
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · rw [pow_zero] at hXD
      exact absurd hXD one_ne_zero
    · exact (pow_eq_zero_iff (by omega)).mp hXD
  have hcard : Multiset.card p.roots = p.natDegree :=
    splits_iff_card_roots.mp (IsAlgClosed.splits _)
  have hrep : p.roots = Multiset.replicate (Multiset.card p.roots) 0 :=
    (Multiset.eq_replicate_card).mpr hroots
  have hprod : (p.roots.map fun r => Polynomial.X - Polynomial.C r).prod = p :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp hcard
  rw [← hprod, hrep, hcard]
  simp [Multiset.map_replicate]

/-- **A monic factor of a distinguished polynomial is distinguished.** -/
theorem coeff_eq_zero_of_monic_mul_eq_distPoly {P Q : Polynomial (AnalyticGerm (0 : Fin n → ℂ))}
    (hP : P.Monic) (_hQ : Q.Monic) {d : ℕ} {α : ℕ → AnalyticGerm (0 : Fin n → ℂ)}
    (hzero : ∀ j, j < d → germValueMap n (α j) = 0) (h : P * Q = distPoly d α) :
    ∀ j, j < P.natDegree → germValueMap n (P.coeff j) = 0 := by
  refine coeff_eq_zero_of_map_eq_X_pow ?_
  have hmapmul : P.map (germValueMap n) * Q.map (germValueMap n) = Polynomial.X ^ d := by
    rw [← Polynomial.map_mul, h, map_distPoly_eq_X_pow hzero]
  have hPmap : (P.map (germValueMap n)).Monic := hP.map _
  have hnat : (P.map (germValueMap n)).natDegree = P.natDegree := hP.natDegree_map _
  rw [← hnat]
  exact eq_X_pow_of_monic_of_mul_eq_X_pow hPmap hmapmul

/-- **A factor of a monic polynomial can be normalized to be monic.** -/
theorem exists_monic_factorization {P Q W : Polynomial (AnalyticGerm (0 : Fin n → ℂ))}
    (hW : W.Monic) (h : P * Q = W) :
    ∃ P' Q' : Polynomial (AnalyticGerm (0 : Fin n → ℂ)),
      P'.Monic ∧ Q'.Monic ∧ P' * Q' = W ∧ Associated P P' ∧ Associated Q Q' := by
  have hlead : P.leadingCoeff * Q.leadingCoeff = 1 := by
    rw [← leadingCoeff_mul, h]
    exact hW
  have hPu : IsUnit (Polynomial.C Q.leadingCoeff : Polynomial (AnalyticGerm (0 : Fin n → ℂ))) :=
    isUnit_C.mpr ⟨⟨Q.leadingCoeff, P.leadingCoeff, by rw [mul_comm]; exact hlead, hlead⟩, rfl⟩
  have hQu : IsUnit (Polynomial.C P.leadingCoeff : Polynomial (AnalyticGerm (0 : Fin n → ℂ))) :=
    isUnit_C.mpr ⟨⟨P.leadingCoeff, Q.leadingCoeff, hlead, by rw [mul_comm]; exact hlead⟩, rfl⟩
  refine ⟨Polynomial.C Q.leadingCoeff * P, Polynomial.C P.leadingCoeff * Q, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C, mul_comm]
    exact hlead
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C]
    exact hlead
  · rw [show Polynomial.C Q.leadingCoeff * P * (Polynomial.C P.leadingCoeff * Q)
        = Polynomial.C (P.leadingCoeff * Q.leadingCoeff) * (P * Q) from by
      rw [map_mul]; ring, hlead, map_one, one_mul, h]
  · exact ⟨hPu.unit, by rw [IsUnit.unit_spec]; ring⟩
  · exact ⟨hQu.unit, by rw [IsUnit.unit_spec]; ring⟩

/-- **Irreducibility of a distinguished polynomial transfers to its germ.** -/
theorem irreducible_germEval_of_irreducible {d : ℕ} (hd : 0 < d)
    {α : ℕ → AnalyticGerm (0 : Fin n → ℂ)}
    (hzero : ∀ j, j < d → germValueMap n (α j) = 0)
    (hirr : Irreducible (distPoly d α)) : Irreducible (germEval n (distPoly d α)) := by
  refine ⟨not_isUnit_germEval_distPoly hd hzero, ?_⟩
  intro g h hgh
  obtain ⟨dG, dH, αG, αH, u, v, hzG, hzH, hu, hv, hgP, hhQ, hW⟩ :=
    exists_distPoly_factorization hzero hgh
  rcases hirr.isUnit_or_isUnit hW with hUG | hUH
  · left
    have h1 : distPoly dG αG = 1 :=
      (distPoly_monic dG αG).natDegree_eq_zero.mp (natDegree_eq_zero_of_isUnit hUG)
    rw [hgP, h1, map_one, one_mul]
    exact hu
  · right
    have h1 : distPoly dH αH = 1 :=
      (distPoly_monic dH αH).natDegree_eq_zero.mp (natDegree_eq_zero_of_isUnit hUH)
    rw [hhQ, h1, map_one, one_mul]
    exact hv

end GaloisForLFunctions.HTGeometry
