import GaloisForLFunctions.HTGeometry.Quantum.LinearResponse.AbelBohrPolynomials
import GaloisForLFunctions.HTGeometry.LinearPartialFractions

/-!
# Minimality of the Bohr denominator

A supported gap contributes a real pole in the inverse-shift
variable. Some numerator entry stays nonzero there, so every
polynomial representation of the response must retain that pole.
-/

open Matrix Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : Matrix ι ι ℂ}

private theorem abelGapFactor_eval_inv_ne_zero {a g : ℝ} (hg : g ≠ 0) (ha : a ≠ g) :
    (abelGapFactor a).eval (g : ℂ)⁻¹ ≠ 0 := by
  rw [eval_abelGapFactor]
  intro he
  have h := congrArg (fun z : ℂ => (g : ℂ) * z) (sub_eq_zero.mp he)
  rw [mul_one, ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hg), one_mul] at h
  apply ha
  simpa only [Complex.ofReal_re] using congrArg Complex.re h.symm

theorem eval_abelBohrDenominator_inv_eq_zero (hH : H.IsHermitian) (X : Matrix ι ι ℂ)
    {g : ℝ} (hg : g ∈ abelProbeBohrGaps hH X) :
    (abelBohrDenominator hH X).eval (g : ℂ)⁻¹ = 0 := by
  have h0 := ((mem_abelProbeBohrGaps hH X g).mp hg).1
  rw [abelBohrDenominator, Polynomial.eval_prod]
  apply Finset.prod_eq_zero hg
  rw [eval_abelGapFactor, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr h0), sub_self]

/-- At each candidate pole at least one numerator entry is nonzero. -/
theorem exists_eval_abelBohrNumerator_inv_ne_zero (hH : H.IsHermitian) (X : Matrix ι ι ℂ)
    {g : ℝ} (hg : g ∈ abelProbeBohrGaps hH X) :
    ∃ i j, hamiltonianGap hH i j = g ∧ (abelBohrNumerator hH X i j).eval (g : ℂ)⁻¹ ≠ 0 := by
  classical
  obtain ⟨h0, i, j, he, hx⟩ := (mem_abelProbeBohrGaps hH X g).mp hg
  refine ⟨i, j, he, ?_⟩
  rw [abelBohrNumerator, Matrix.of_apply, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, he]
  exact mul_ne_zero hx (Finset.prod_ne_zero_iff.mpr fun a ha =>
    abelGapFactor_eval_inv_ne_zero h0 (Finset.mem_erase.mp ha).1)

/-- Any common polynomial denominator has a zero at every supported gap reciprocal. -/
theorem eval_abelBohrCommonDenominator_inv_eq_zero (hH : H.IsHermitian) (X : Matrix ι ι ℂ)
    (Q : Polynomial ℂ) (N : Matrix ι ι (Polynomial ℂ))
    (hN : ∀ i j, Q * abelBohrNumerator hH X i j = abelBohrDenominator hH X * N i j)
    {g : ℝ} (hg : g ∈ abelProbeBohrGaps hH X) : Q.eval (g : ℂ)⁻¹ = 0 := by
  obtain ⟨i, j, _, he⟩ := exists_eval_abelBohrNumerator_inv_ne_zero hH X hg
  have hv := congrArg (Polynomial.eval (g : ℂ)⁻¹) (hN i j)
  rw [Polynomial.eval_mul, Polynomial.eval_mul, eval_abelBohrDenominator_inv_eq_zero hH X hg,
    zero_mul] at hv
  exact (mul_eq_zero.mp hv).resolve_right he

/-- The supported gap count is a lower bound on every common denominator degree. -/
theorem card_abelProbeBohrGaps_le_natDegree_of_commonDenominator (hH : H.IsHermitian)
    (X : Matrix ι ι ℂ) {Q : Polynomial ℂ} (hQ : Q ≠ 0) (N : Matrix ι ι (Polynomial ℂ))
    (hN : ∀ i j, Q * abelBohrNumerator hH X i j = abelBohrDenominator hH X * N i j) :
    (abelProbeBohrGaps hH X).card ≤ Q.natDegree := by
  by_contra! hd
  apply hQ
  let s := abelProbeBohrGaps hH X
  let f : s → ℂ := fun a => ((a.1 : ℝ) : ℂ)⁻¹
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg Complex.re (inv_injective h)
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q hf ?_ ?_
  · intro a
    exact eval_abelBohrCommonDenominator_inv_eq_zero hH X Q N hN a.2
  · rw [Fintype.card_coe]
    exact hd

private theorem abelBohrDenominator_ne_zero (hH : H.IsHermitian) (X : Matrix ι ι ℂ) :
    abelBohrDenominator hH X ≠ 0 := by
  intro h
  have he := eval_abelBohrDenominator_zero hH X
  rw [h, Polynomial.eval_zero] at he
  exact zero_ne_one he

theorem natDegree_abelBohrDenominator (hH : H.IsHermitian) (X : Matrix ι ι ℂ) :
    (abelBohrDenominator hH X).natDegree = (abelProbeBohrGaps hH X).card := by
  apply le_antisymm (natDegree_abelBohrDenominator_le hH X)
  exact card_abelProbeBohrGaps_le_natDegree_of_commonDenominator hH X
    (abelBohrDenominator_ne_zero hH X)
    (abelBohrNumerator hH X) (fun _ _ => rfl)

/-- Cross multiplication can represent the probe with denominator
`Q` exactly when the Bohr denominator divides `Q`. -/
theorem abelBohrCommonDenominator_iff_dvd (hH : H.IsHermitian) (X : Matrix ι ι ℂ)
    (Q : Polynomial ℂ) :
    (∃ N : Matrix ι ι (Polynomial ℂ), ∀ i j,
      Q * abelBohrNumerator hH X i j = abelBohrDenominator hH X * N i j) ↔
      abelBohrDenominator hH X ∣ Q := by
  constructor
  · rintro ⟨N, hN⟩
    let σ := fun g : ℝ => (g : ℂ)⁻¹
    let s := abelProbeBohrGaps hH X
    let P := ∏ g ∈ s, (Polynomial.X - Polynomial.C (σ g))
    have hσ : Function.Injective σ := by
      intro a b h
      exact congrArg Complex.re (inv_injective h)
    obtain ⟨c, hc⟩ : ∃ c : ℂ, abelBohrDenominator hH X = Polynomial.C c * P :=
      eq_C_mul_prod_X_sub_C hσ (fun _ hg => eval_abelBohrDenominator_inv_eq_zero hH X hg)
        (natDegree_abelBohrDenominator_le hH X)
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero, zero_mul] at hc
      exact abelBohrDenominator_ne_zero hH X hc
    obtain ⟨R, hR⟩ : P ∣ Q :=
      prod_X_sub_C_dvd_of_isRoot hσ
        (fun _ hg => eval_abelBohrCommonDenominator_inv_eq_zero hH X Q N hN hg)
    refine ⟨Polynomial.C c⁻¹ * R, ?_⟩
    rw [hR, hc]
    symm
    calc
      _ = (Polynomial.C c * Polynomial.C c⁻¹) * (P * R) := by ac_rfl
      _ = P * R := by
        rw [← map_mul, mul_inv_cancel₀ hc0, map_one, one_mul]
  · rintro ⟨R, rfl⟩
    exact ⟨fun i j => R * abelBohrNumerator hH X i j, fun i j => mul_assoc _ _ _⟩

#print axioms exists_eval_abelBohrNumerator_inv_ne_zero
#print axioms card_abelProbeBohrGaps_le_natDegree_of_commonDenominator
#print axioms natDegree_abelBohrDenominator
#print axioms abelBohrCommonDenominator_iff_dvd

end

end GaloisForLFunctions.HTGeometry
