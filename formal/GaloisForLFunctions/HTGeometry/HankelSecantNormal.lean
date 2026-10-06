import GaloisForLFunctions.HTGeometry.HankelSecantUnmixed
import GaloisForLFunctions.HTGeometry.HankelSingularHeight
import GaloisForLFunctions.HTGeometry.SerreIntersectionNormality
import GaloisForLFunctions.HTGeometry.HankelDegenerateRange

/-!
# The Hankel secant varieties are normal

Over a field of characteristic zero, the coordinate ring `K[x_0, …, x_{N−1}]/I_r` of the affine
cone over the `r`-th secant variety of the rational normal curve (the Hankel determinantal variety
of the `(r+1)`-minors) is integrally closed, for every `N` and `r`.

For `N ≤ 2r` the ideal is zero.  Otherwise the Serre-type criterion applies:

* **S2**: every associated prime of a principal ideal has height one
  (`height_eq_one_of_mem_associatedPrimes_hankel`, from freeness over a polynomial subring);
* **R1**: a height-one prime does not contain the `r`-minors, since every prime that does has
  height at least two (`two_le_height_of_singular`); so it avoids some moved chart `δ_t`
  (`exists_hankelChartElemAt_notMem`), whose localization is a localized polynomial ring
  (`isIntegrallyClosed_hankelChartAt`).
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

variable (K : Type) [Field K] [CharZero K]

/-- **The Hankel secant varieties are normal.** -/
theorem isIntegrallyClosed_hankelSecantRing (N r : ℕ) :
    IsIntegrallyClosed (HankelSecantRing K N r) := by
  classical
  by_cases hN : N ≤ 2 * r
  · have hbot := finiteHankelSecantIdeal_eq_bot K hN
    have e : MvPolynomial (Fin N) K ≃+* HankelSecantRing K N r :=
      ((Ideal.quotEquivOfEq hbot).trans (RingEquiv.quotientBot _)).symm
    exact IsIntegrallyClosed.of_equiv e
  push Not at hN
  refine isIntegrallyClosed_of_height_one_away (fun a ha Q hQ =>
    height_eq_one_of_mem_associatedPrimes_hankel K hN.le ha hQ) ?_
  intro P hP hP1
  rcases Nat.eq_zero_or_pos r with hr | hr
  · exfalso
    subst hr
    have h1 := Ideal.height_le_ringKrullDim_of_isPrime (I := P)
    have h2 := ringKrullDim_hankelSecantQuotient_le K (N := N) (r := 0) (by omega)
    rw [hP1] at h1
    have := h1.trans h2
    norm_num at this
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hJ : ¬ (RHTower.finiteHankelSecantIdeal K N s).map (Ideal.Quotient.mk _) ≤ P := by
    intro hle
    have := two_le_height_of_singular K hN P hle
    rw [hP1] at this
    norm_num at this
  obtain ⟨t, -, ht⟩ := exists_hankelChartElemAt_notMem K hN P hJ
  exact ⟨_, ht, isIntegrallyClosed_hankelChartAt K hN.le (t : K)⟩

end

end GaloisForLFunctions.HTGeometry
