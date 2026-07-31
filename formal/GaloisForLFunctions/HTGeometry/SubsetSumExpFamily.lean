import GaloisForLFunctions.HTGeometry.InvariantRootFamily

/-!
# The subset-sum family of a conjugate set

For the roots `ρ₁, …, ρₙ` of a monic integer polynomial and an integer `N`, the numbers
`N · ∑_{i ∈ S} ρᵢ`, taken over the subsets `S` of a fixed size, are the complex roots of a monic
integer polynomial: the family of formal subset sums is invariant under renaming the variables, so
`InvariantRootFamily` applies.

Splitting off the largest power of `X` from that polynomial isolates the vanishing subset sums,
leaving a monic factor with nonzero constant term whose roots are exactly the nonvanishing ones.

* `scaledSubsetSum`, `subsetSumFamily` — the formal subset sums and their multiset.
* `subsetSumFamily_invariant` — the multiset is invariant under renaming.
* `exists_monic_subsetSum_poly` — the monic integer polynomial with those roots.
* `exists_monic_nonzero_const_factor` — splitting off `Xᶻ`.
* `sum_exp_aroots_of_eq_X_pow_mul` — the effect of that splitting on `∑ exp`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Finset

/-- The integer polynomial `N · ∑_{i ∈ S} Xᵢ`. -/
noncomputable def scaledSubsetSum (N : ℤ) {n : ℕ} (S : Finset (Fin n)) :
    MvPolynomial (Fin n) ℤ :=
  ∑ i ∈ S, MvPolynomial.C N * MvPolynomial.X i

theorem rename_scaledSubsetSum (N : ℤ) {n : ℕ} (e : Equiv.Perm (Fin n)) (S : Finset (Fin n)) :
    MvPolynomial.rename e (scaledSubsetSum N S) = scaledSubsetSum N (S.image e) := by
  classical
  rw [scaledSubsetSum, scaledSubsetSum, map_sum,
    Finset.sum_image (fun a _ b _ h => e.injective h)]
  exact Finset.sum_congr rfl fun i _ => by simp

theorem aeval_scaledSubsetSum (N : ℤ) {n : ℕ} (ρ : Fin n → ℂ) (S : Finset (Fin n)) :
    MvPolynomial.aeval ρ (scaledSubsetSum N S) = (N : ℂ) * ∑ i ∈ S, ρ i := by
  rw [scaledSubsetSum, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- The multiset of scaled subset sums over the subsets of a fixed size. -/
noncomputable def subsetSumFamily (N : ℤ) (n s : ℕ) : Multiset (MvPolynomial (Fin n) ℤ) :=
  ((Finset.powersetCard s (Finset.univ : Finset (Fin n))).val).map (scaledSubsetSum N)

theorem card_subsetSumFamily (N : ℤ) (n s : ℕ) :
    Multiset.card (subsetSumFamily N n s) = n.choose s := by
  rw [subsetSumFamily, Multiset.card_map]
  have : Multiset.card (Finset.powersetCard s (Finset.univ : Finset (Fin n))).val
      = (Finset.powersetCard s (Finset.univ : Finset (Fin n))).card := rfl
  rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- Renaming the variables permutes the subsets of a fixed size, so the family is invariant. -/
theorem subsetSumFamily_invariant (N : ℤ) (n s : ℕ) (e : Equiv.Perm (Fin n)) :
    (subsetSumFamily N n s).map (MvPolynomial.rename e) = subsetSumFamily N n s := by
  classical
  have hinj : Function.Injective (fun S : Finset (Fin n) => S.image e) :=
    Finset.image_injective e.injective
  have himg : (Finset.powersetCard s (Finset.univ : Finset (Fin n))).image
      (fun S : Finset (Fin n) => S.image e)
      = Finset.powersetCard s (Finset.univ : Finset (Fin n)) := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro A hA
      rw [Finset.mem_image] at hA
      obtain ⟨B, hB, rfl⟩ := hA
      rw [Finset.mem_powersetCard] at hB ⊢
      exact ⟨Finset.subset_univ _, by
        rw [Finset.card_image_of_injective _ e.injective, hB.2]⟩
    · rw [Finset.card_image_of_injective _ hinj]
  rw [subsetSumFamily, Multiset.map_map]
  have hcomp : ((MvPolynomial.rename e :
        MvPolynomial (Fin n) ℤ →ₐ[ℤ] MvPolynomial (Fin n) ℤ) ∘ (scaledSubsetSum N))
      = (scaledSubsetSum N) ∘ (fun S : Finset (Fin n) => S.image e) := by
    funext S
    exact rename_scaledSubsetSum N e S
  rw [hcomp, ← Multiset.map_map, subsetSumFamily]
  congr 1
  rw [← Finset.image_val_of_injOn (fun a _ b _ h => hinj h), himg]

/-- **The scaled subset sums of a conjugate set are the roots of a monic integer polynomial.** -/
theorem exists_monic_subsetSum_poly {m : ℤ[X]} (hm : m.Monic) {n : ℕ} (hn : m.natDegree = n)
    {ρ : Fin n → ℂ} (hρ : m.aroots ℂ = Multiset.map ρ (Finset.univ : Finset (Fin n)).val)
    (N : ℤ) (s : ℕ) :
    ∃ F : ℤ[X], F.Monic ∧ F.natDegree = n.choose s ∧
      F.aroots ℂ = ((Finset.powersetCard s (Finset.univ : Finset (Fin n))).val).map
        (fun S => (N : ℂ) * ∑ i ∈ S, ρ i) := by
  classical
  obtain ⟨F, hFmonic, hFdeg, hFmap⟩ :=
    exists_monic_int_map_eq_prod hm hn hρ (subsetSumFamily N n s)
      (subsetSumFamily_invariant N n s)
  refine ⟨F, hFmonic, by rw [hFdeg, card_subsetSumFamily], ?_⟩
  rw [Polynomial.aroots, hFmap]
  have hsplit : (subsetSumFamily N n s).map
      (fun q => Polynomial.X - Polynomial.C (MvPolynomial.aeval ρ q))
      = (((Finset.powersetCard s (Finset.univ : Finset (Fin n))).val).map
        (fun S => (N : ℂ) * ∑ i ∈ S, ρ i)).map (fun a => Polynomial.X - Polynomial.C a) := by
    rw [subsetSumFamily, Multiset.map_map, Multiset.map_map]
    refine Multiset.map_congr rfl fun S _ => ?_
    simp only [Function.comp_apply]
    rw [aeval_scaledSubsetSum]
  rw [hsplit, Polynomial.roots_multiset_prod_X_sub_C]

/-- Splitting off the largest power of `X` from a monic integer polynomial. -/
theorem exists_monic_nonzero_const_factor {F : ℤ[X]} (hF : F.Monic) :
    ∃ (z : ℕ) (H : ℤ[X]), H.Monic ∧ H.eval 0 ≠ 0 ∧ F = X ^ z * H ∧ z ≤ F.natDegree := by
  classical
  have hXC : (Polynomial.X - Polynomial.C (0 : ℤ)) = Polynomial.X := by simp
  refine ⟨Polynomial.rootMultiplicity 0 F,
    F /ₘ (Polynomial.X - Polynomial.C (0 : ℤ)) ^ Polynomial.rootMultiplicity 0 F, ?_, ?_, ?_, ?_⟩
  · refine Polynomial.Monic.of_mul_monic_left (p := Polynomial.X ^ Polynomial.rootMultiplicity 0 F)
      (Polynomial.monic_X_pow _) ?_
    rw [← hXC, Polynomial.pow_mul_divByMonic_rootMultiplicity_eq]
    exact hF
  · exact Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hF.ne_zero
  · rw [← hXC, Polynomial.pow_mul_divByMonic_rootMultiplicity_eq]
  · have hdvd : (Polynomial.X : ℤ[X]) ^ Polynomial.rootMultiplicity 0 F ∣ F := by
      rw [← hXC]
      exact Polynomial.pow_rootMultiplicity_dvd F 0
    have := Polynomial.natDegree_le_of_dvd hdvd hF.ne_zero
    rwa [Polynomial.natDegree_X_pow] at this

/-- Splitting off `Xᶻ` contributes exactly `z` to the sum of `exp` over the complex roots. -/
theorem sum_exp_aroots_of_eq_X_pow_mul {F H : ℤ[X]} (hF : F.Monic) {z : ℕ}
    (hFH : F = X ^ z * H) :
    ((F.aroots ℂ).map Complex.exp).sum = (z : ℂ) + ((H.aroots ℂ).map Complex.exp).sum := by
  have hFmap : (F.map (algebraMap ℤ ℂ)).Monic := hF.map _
  have hne : (Polynomial.X : ℂ[X]) ^ z * (H.map (algebraMap ℤ ℂ)) ≠ 0 := by
    have := hFmap.ne_zero
    rw [hFH, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X] at this
    exact this
  rw [Polynomial.aroots, hFH, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.roots_mul hne, Polynomial.roots_pow, Polynomial.roots_X,
    Multiset.nsmul_singleton, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
    Multiset.sum_replicate]
  simp [Polynomial.aroots]

end GaloisForLFunctions.HTGeometry
