import GaloisForLFunctions.HTGeometry.PaperNativeReesHomogeneousSums
import GaloisForLFunctions.HTGeometry.PaperWeightOrderIdeals

/-!
# Polynomial normal lines from homogeneous ideal generators

Combine the paper's nonnegative weights and exact Rees coefficient kernel.
A nonzero homogeneous ideal element at the ideal's lowest positive degree
has algebraically independent powers in the associated graded ring. The
data below retain every algebraic obligation; concrete applications supply
all fields from existing Lean proofs. The variable type may be infinite.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

noncomputable section

/-- Fully specified algebraic data for a lowest-degree homogeneous normal direction. -/
structure PaperHomogeneousNormalData (K σ : Type*) [Field K] (I : Ideal (MvPolynomial σ K)) where
  generator : MvPolynomial σ K
  degree : ℕ
  degree_pos : 0 < degree
  generator_mem : generator ∈ I
  generator_ne_zero : generator ≠ 0
  homogeneous : generator.IsWeightedHomogeneous (fun _ => (1 : ℤ)) (degree : ℤ)
  order_bound : I ≤ paperWeightOrderIdeal (fun _ : σ => (1 : ℤ)) (by intro _; exact zero_le_one) degree

variable {K σ : Type*} [Field K] {I : Ideal (MvPolynomial σ K)}

/-- The selected generator has its usual membership in each ideal power. -/
theorem PaperHomogeneousNormalData.pow_mem (D : PaperHomogeneousNormalData K σ I) (n : ℕ) :
    D.generator ^ n ∈ I ^ n := Ideal.pow_mem_pow D.generator_mem n

/-- Native degree-one Rees representative of the homogeneous generator. -/
def PaperHomogeneousNormalData.nativeRees (D : PaperHomogeneousNormalData K σ I) : reesAlgebra I :=
  ReesGrading.mono I 1 D.generator (by simpa only [pow_one] using D.generator_mem)

/-- The corresponding element of the actual associated graded ring. -/
def PaperHomogeneousNormalData.direction (D : PaperHomogeneousNormalData K σ I) :
    PaperIdealAssociatedGraded I := paperNativeReesSpecialization I D.nativeRees

/-- The powers of the direction are represented by homogeneous generator powers. -/
theorem PaperHomogeneousNormalData.direction_pow (D : PaperHomogeneousNormalData K σ I) (n : ℕ) :
    D.direction ^ n = paperNativeReesSpecialization I
      (ReesGrading.mono I n (D.generator ^ n) (D.pow_mem n)) := by
  rw [PaperHomogeneousNormalData.direction, ← map_pow]
  congr 1
  apply Subtype.ext
  change Polynomial.monomial 1 D.generator ^ n = Polynomial.monomial n (D.generator ^ n)
  rw [Polynomial.monomial_pow, one_mul]

/-- Scalar generator powers gain an ideal order exactly when the scalar vanishes. -/
theorem PaperHomogeneousNormalData.scalar_pow_mem_succ_iff
    (D : PaperHomogeneousNormalData K σ I) (n : ℕ) (c : K) :
    C c * D.generator ^ n ∈ I ^ (n + 1) ↔ c = 0 := by
  constructor
  · intro h
    by_contra hc
    have hc0 : (C c : MvPolynomial σ K) ≠ 0 := by
      intro he
      exact hc (MvPolynomial.C_injective σ K (by simpa only [map_zero] using he))
    have hh : (C c * D.generator ^ n).IsWeightedHomogeneous
        (fun _ => (1 : ℤ)) ((n : ℤ) * D.degree) := by
      simpa only [nsmul_eq_mul] using (D.homogeneous.pow n).C_mul c
    have hd : (0 : ℤ) < D.degree := by exact_mod_cast D.degree_pos
    have hlt : (n : ℤ) * D.degree < ((n + 1 : ℕ) : ℤ) * D.degree := by
      push_cast
      nlinarith
    exact paperWeightOrderIdeal_not_mem_of_homogeneous _ _ hh
      (mul_ne_zero hc0 (pow_ne_zero n D.generator_ne_zero)) hlt
      (paperWeightOrderIdeal_pow_le _ _ I _ D.order_bound (n + 1) h)
  · rintro rfl
    simp

/-- Generator powers cannot gain one additional ideal order. -/
theorem PaperHomogeneousNormalData.pow_not_mem_succ
    (D : PaperHomogeneousNormalData K σ I) (n : ℕ) : D.generator ^ n ∉ I ^ (n + 1) := by
  intro h
  exact one_ne_zero ((D.scalar_pow_mem_succ_iff n 1).mp (by simpa using h))

/-- Every power of the actual normal direction remains nonzero. -/
theorem PaperHomogeneousNormalData.direction_pow_ne_zero
    (D : PaperHomogeneousNormalData K σ I) (n : ℕ) : D.direction ^ n ≠ 0 := by
  rw [D.direction_pow]
  intro h
  exact D.pow_not_mem_succ n
    ((paperNativeReesSpecialization_mono_eq_zero_iff I n ⟨_, D.pow_mem n⟩).mp h)

/-- The normal direction is never nilpotent. -/
theorem PaperHomogeneousNormalData.direction_not_isNilpotent
    (D : PaperHomogeneousNormalData K σ I) : ¬ IsNilpotent D.direction := by
  rintro ⟨n, hn⟩
  exact D.direction_pow_ne_zero n hn

/-- No finite scalar relation between the normal-direction powers can vanish. -/
theorem PaperHomogeneousNormalData.sum_eq_zero_iff
    (D : PaperHomogeneousNormalData K σ I) (s : Finset ℕ) (a : ℕ → K) :
    (∑ n ∈ s, algebraMap (MvPolynomial σ K) (PaperIdealAssociatedGraded I) (C (a n)) *
      D.direction ^ n) = 0 ↔ ∀ n ∈ s, a n = 0 := by
  let b : (n : ℕ) → (I ^ n : Ideal (MvPolynomial σ K)) := fun n =>
    ⟨C (a n) * D.generator ^ n, (I ^ n).mul_mem_left _ (D.pow_mem n)⟩
  have hterm (n : ℕ) :
      algebraMap (MvPolynomial σ K) (PaperIdealAssociatedGraded I) (C (a n)) * D.direction ^ n =
        paperNativeReesSpecialization I (ReesGrading.mono I n (b n) (b n).property) := by
    rw [D.direction_pow, ← (paperNativeReesSpecialization I).commutes (C (a n)), ← map_mul]
    congr 1
    apply Subtype.ext
    change Polynomial.C (C (a n)) * Polynomial.monomial n (D.generator ^ n) =
      Polynomial.monomial n (C (a n) * D.generator ^ n)
    exact Polynomial.C_mul_monomial
  have hsum := Finset.sum_congr (s₁ := s) rfl (fun n _ => hterm n)
  rw [hsum, paperNativeRees_sum_mono_eq_zero_iff]
  exact forall_congr' fun n => forall_congr' fun _ => D.scalar_pow_mem_succ_iff n (a n)

/-- Polynomial substitution into the associated graded ring. -/
def PaperHomogeneousNormalData.polynomialMap (D : PaperHomogeneousNormalData K σ I) :
    Polynomial K →+* PaperIdealAssociatedGraded I :=
  paperNativeReesPolynomialMap I MvPolynomial.C D.direction

/-- The explicit polynomial substitution has zero kernel. -/
theorem PaperHomogeneousNormalData.polynomialMap_eq_zero_iff
    (D : PaperHomogeneousNormalData K σ I) (p : Polynomial K) : D.polynomialMap p = 0 ↔ p = 0 := by
  change Polynomial.eval₂ _ _ p = 0 ↔ p = 0
  rw [Polynomial.eval₂_eq_sum]
  change (∑ n ∈ p.support, algebraMap (MvPolynomial σ K) (PaperIdealAssociatedGraded I)
    (C (p.coeff n)) * D.direction ^ n) = 0 ↔ p = 0
  rw [D.sum_eq_zero_iff]
  constructor
  · intro h
    apply Polynomial.ext
    intro n
    by_cases hn : n ∈ p.support
    · simpa only [Polynomial.coeff_zero] using h n hn
    · have hz : p.coeff n = 0 := by
        by_contra he
        exact hn (Polynomial.mem_support_iff.mpr he)
      simpa only [Polynomial.coeff_zero] using hz
  · rintro rfl
    simp

/-- The normal-direction substitution embeds a polynomial ring over the coefficient field. -/
theorem PaperHomogeneousNormalData.polynomialMap_injective
    (D : PaperHomogeneousNormalData K σ I) : Function.Injective D.polynomialMap :=
  (injective_iff_map_eq_zero _).mpr fun p hp => (D.polynomialMap_eq_zero_iff p).mp hp

end

end GaloisForLFunctions.HTGeometry
