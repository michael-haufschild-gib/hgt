import GaloisForLFunctions.HTGeometry.PrimeWalshStoneReconstruction

/-!
# Cofinite Hasse reconstruction for prime-Walsh observables

The compact prime-tail cluster space is treated as the family of local places.  A global cylinder
observable modulo eventual tail-vanishing is determined exactly by its values at all cluster
places, every local observable has one unique global quotient class, and representatives are
unique modulo disagreement at finitely many prime indices.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Set Topology

noncomputable section

/-- Two cylinder observables define the same global tail class exactly when they disagree at only
finitely many prime indices. -/
theorem primeTailQuotient_mk_congr_hasse_iff
    {J : Type*} (θ : ℕ → (J → Bool))
    (f g : LocallyConstant (J → Bool) ℂ) :
    Ideal.Quotient.mk (primeTailVanishingIdeal θ) f =
        Ideal.Quotient.mk (primeTailVanishingIdeal θ) g ↔
      {n | f (θ n) ≠ g (θ n)}.Finite := by
  rw [Ideal.Quotient.eq, mem_primeTailVanishingIdeal_iff_eventuallyZero]
  have hset : {n | (f - g) (θ n) ≠ 0} = {n | f (θ n) ≠ g (θ n)} := by
    ext n
    change (f (θ n) - g (θ n) ≠ 0) ↔ f (θ n) ≠ g (θ n)
    exact sub_ne_zero
  rw [hset]

/-- Tail quotient classes agree exactly when every compact cluster-place observation agrees. -/
theorem primeTailQuotient_congr_hasse_iff
    {J : Type*} [DecidableEq J] (θ : ℕ → (J → Bool))
    (q r : LocallyConstant (J → Bool) ℂ ⧸ primeTailVanishingIdeal θ) :
    q = r ↔ ∀ x : primeOrientationTailClusterSet θ,
      primeTailLocallyConstantQuotientEquiv θ q x =
        primeTailLocallyConstantQuotientEquiv θ r x := by
  constructor
  · rintro rfl x
    rfl
  · intro hlocal
    apply (primeTailLocallyConstantQuotientEquiv θ).injective
    ext x
    exact hlocal x

/-- A global tail class is zero exactly when every cluster-place value is zero. -/
theorem primeTailQuotient_eq_zero_hasse_iff
    {J : Type*} [DecidableEq J] (θ : ℕ → (J → Bool))
    (q : LocallyConstant (J → Bool) ℂ ⧸ primeTailVanishingIdeal θ) :
    q = 0 ↔ ∀ x : primeOrientationTailClusterSet θ,
      primeTailLocallyConstantQuotientEquiv θ q x = 0 := by
  rw [primeTailQuotient_congr_hasse_iff θ q 0]
  simp

/-- Distinct global tail classes differ at a concrete compact cluster place. -/
theorem primeTailQuotient_ne_iff_exists_localWitness
    {J : Type*} [DecidableEq J] (θ : ℕ → (J → Bool))
    (q r : LocallyConstant (J → Bool) ℂ ⧸ primeTailVanishingIdeal θ) :
    q ≠ r ↔ ∃ x : primeOrientationTailClusterSet θ,
      primeTailLocallyConstantQuotientEquiv θ q x ≠
        primeTailLocallyConstantQuotientEquiv θ r x := by
  classical
  constructor
  · intro hqr
    by_contra hno
    apply hqr
    apply (primeTailQuotient_congr_hasse_iff θ q r).mpr
    intro x
    by_contra hx
    exact hno ⟨x, hx⟩
  · rintro ⟨x, hx⟩ hqr
    exact hx (by rw [hqr])

/-- Every locally constant observable on the compact tail constraint has one unique global tail
quotient class. -/
theorem primeTailQuotient_existsUnique_globalClass
    {J : Type*} [DecidableEq J] (θ : ℕ → (J → Bool))
    (localObservable : LocallyConstant (primeOrientationTailClusterSet θ) ℂ) :
    ∃! q : LocallyConstant (J → Bool) ℂ ⧸ primeTailVanishingIdeal θ,
      primeTailLocallyConstantQuotientEquiv θ q = localObservable := by
  refine ⟨(primeTailLocallyConstantQuotientEquiv θ).symm localObservable, ?_, ?_⟩
  · exact (primeTailLocallyConstantQuotientEquiv θ).apply_symm_apply localObservable
  · intro q hq
    apply (primeTailLocallyConstantQuotientEquiv θ).injective
    rw [hq]
    exact ((primeTailLocallyConstantQuotientEquiv θ).apply_symm_apply localObservable).symm

/-- Every tail-local observable has a global cylinder representative, unique modulo finite
prime-index disagreement. -/
theorem primeTail_exists_globalRepresentative_unique_eventually
    {J : Type*} [DecidableEq J] (θ : ℕ → (J → Bool))
    (localObservable : LocallyConstant (primeOrientationTailClusterSet θ) ℂ) :
    ∃ f : LocallyConstant (J → Bool) ℂ,
      primeTailLocallyConstantQuotientEquiv θ
          (Ideal.Quotient.mk (primeTailVanishingIdeal θ) f) = localObservable ∧
      ∀ g : LocallyConstant (J → Bool) ℂ,
        primeTailLocallyConstantQuotientEquiv θ
            (Ideal.Quotient.mk (primeTailVanishingIdeal θ) g) = localObservable ↔
          {n | g (θ n) ≠ f (θ n)}.Finite := by
  let q := (primeTailLocallyConstantQuotientEquiv θ).symm localObservable
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨f, ?_, fun g => ?_⟩
  · rw [hf]
    exact (primeTailLocallyConstantQuotientEquiv θ).apply_symm_apply localObservable
  · constructor
    · intro hg
      apply (primeTailQuotient_mk_congr_hasse_iff θ g f).mp
      apply (primeTailLocallyConstantQuotientEquiv θ).injective
      rw [hg, hf]
      exact ((primeTailLocallyConstantQuotientEquiv θ).apply_symm_apply localObservable).symm
    · intro hfinite
      have hgf := (primeTailQuotient_mk_congr_hasse_iff θ g f).mpr hfinite
      rw [hgf, hf]
      exact (primeTailLocallyConstantQuotientEquiv θ).apply_symm_apply localObservable

end


end GaloisForLFunctions.HTGeometry
