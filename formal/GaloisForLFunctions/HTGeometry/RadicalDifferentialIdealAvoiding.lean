import GaloisForLFunctions.HTGeometry.DifferentialFieldSolution

/-!
# Radical differential ideals avoiding an element

For a radical ideal, missing an element is the same as missing all its powers, so Zorn applies to
the radical differential ideals that avoid a fixed element exactly as it does to the proper ones: a
maximal such ideal exists, and Ritt's product law makes it prime — otherwise the element would land
in it squared.

The consequence is the form of the weak differential Nullstellensatz that separation needs: an
element outside a radical differential ideal stays nonzero under some differential map to a
differential field killing the ideal.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {R : Type*} [CommRing R] [Differential R]

/-- **A maximal radical differential ideal avoiding a given element exists.** -/
theorem exists_maximal_avoiding_radicalDifferential {I₀ : Ideal R} (hrad : I₀.IsRadical)
    (hδ : ∀ x ∈ I₀, Differential.deriv x ∈ I₀) {e : R} (he : e ∉ I₀) :
    ∃ M : Ideal R, M.IsRadical ∧ (∀ x ∈ M, Differential.deriv x ∈ M) ∧ I₀ ≤ M ∧ e ∉ M ∧
      ∀ J : Ideal R, J.IsRadical → (∀ x ∈ J, Differential.deriv x ∈ J) → M ≤ J → e ∉ J →
        J = M := by
  classical
  set S : Set (Ideal R) :=
    {I : Ideal R | I.IsRadical ∧ (∀ x ∈ I, Differential.deriv x ∈ I) ∧ I₀ ≤ I ∧ e ∉ I} with hS
  have hbound : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc
    rcases Set.eq_empty_or_nonempty c with rfl | hnec
    · exact ⟨I₀, ⟨hrad, hδ, le_rfl, he⟩, by simp⟩
    refine ⟨sSup c, ⟨?_, ?_, ?_, ?_⟩, fun z hz => le_sSup hz⟩
    · intro y hy
      obtain ⟨n, hn⟩ := hy
      rw [Submodule.mem_sSup_of_directed hnec hc.directedOn] at hn ⊢
      obtain ⟨J, hJc, hJ⟩ := hn
      exact ⟨J, hJc, (hcS hJc).1 ⟨n, hJ⟩⟩
    · intro x hx
      rw [Submodule.mem_sSup_of_directed hnec hc.directedOn] at hx ⊢
      obtain ⟨J, hJc, hJ⟩ := hx
      exact ⟨J, hJc, (hcS hJc).2.1 x hJ⟩
    · obtain ⟨J, hJc⟩ := hnec
      exact le_trans (hcS hJc).2.2.1 (le_sSup hJc)
    · intro hmem
      rw [Submodule.mem_sSup_of_directed hnec hc.directedOn] at hmem
      obtain ⟨J, hJc, hJ⟩ := hmem
      exact (hcS hJc).2.2.2 hJ
  obtain ⟨M, hM⟩ := zorn_le₀ S hbound
  refine ⟨M, hM.1.1, hM.1.2.1, hM.1.2.2.1, hM.1.2.2.2, ?_⟩
  intro J hJrad hJδ hle hJe
  have hJS : J ∈ S := ⟨hJrad, hJδ, le_trans hM.1.2.2.1 hle, hJe⟩
  exact le_antisymm (hM.2 hJS hle) hle

/-- **A maximal radical differential ideal avoiding an element is prime.** -/
theorem isPrime_of_maximal_avoiding_radicalDifferential {M : Ideal R} (hrad : M.IsRadical)
    (hδ : ∀ x ∈ M, Differential.deriv x ∈ M) {e : R} (he : e ∉ M)
    (hmax : ∀ J : Ideal R, J.IsRadical → (∀ x ∈ J, Differential.deriv x ∈ J) → M ≤ J → e ∉ J →
      J = M) : M.IsPrime := by
  classical
  refine ⟨fun htop => he (by rw [htop]; trivial), ?_⟩
  intro a b hab
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨ha, hb⟩ := hcon
  have hgen : ∀ x : R, x ∉ M → e ∈ radicalDifferentialIdeal ((M : Set R) ∪ {x}) := by
    intro x hx
    have hle : M ≤ radicalDifferentialIdeal ((M : Set R) ∪ {x}) := by
      intro y hy
      exact subset_radicalDifferentialIdeal _ (Or.inl hy)
    have hxmem : x ∈ radicalDifferentialIdeal ((M : Set R) ∪ {x}) :=
      subset_radicalDifferentialIdeal _ (Or.inr rfl)
    by_contra hene
    have heq := hmax (radicalDifferentialIdeal ((M : Set R) ∪ {x}))
      (isRadical_radicalDifferentialIdeal _) (deriv_mem_radicalDifferentialIdeal _) hle hene
    rw [heq] at hxmem
    exact hx hxmem
  have hesq : e * e ∈ M := by
    have hprod : ∀ s ∈ ((M : Set R) ∪ {a}), ∀ t ∈ ((M : Set R) ∪ {b}), s * t ∈ M := by
      rintro s (hs | rfl) t (ht | rfl)
      · exact Ideal.mul_mem_right _ _ hs
      · exact Ideal.mul_mem_right _ _ hs
      · exact Ideal.mul_mem_left _ _ ht
      · exact hab
    exact mul_mem_of_forall_mul_mem hrad hδ hprod (hgen a ha) (hgen b hb)
  exact he (hrad ⟨2, by rw [pow_two]; exact hesq⟩)

/-- **Every element outside a radical differential ideal survives a prime differential ideal above
it.** -/
theorem exists_isPrime_avoiding_radicalDifferential {I₀ : Ideal R} (hrad : I₀.IsRadical)
    (hδ : ∀ x ∈ I₀, Differential.deriv x ∈ I₀) {e : R} (he : e ∉ I₀) :
    ∃ P : Ideal R, P.IsPrime ∧ (∀ x ∈ P, Differential.deriv x ∈ P) ∧ I₀ ≤ P ∧ e ∉ P := by
  obtain ⟨M, hMrad, hMδ, hIM, hMe, hMmax⟩ :=
    exists_maximal_avoiding_radicalDifferential hrad hδ he
  exact ⟨M, isPrime_of_maximal_avoiding_radicalDifferential hMrad hMδ hMe hMmax, hMδ, hIM, hMe⟩

/-- **The weak differential Nullstellensatz with a nonvanishing element.**  A radical differential
ideal missing an element is killed by a differential ring map to a differential field which does not
kill that element. -/
theorem exists_differentialField_hom_of_notMem {R : Type u} [CommRing R] [Algebra ℚ R]
    [Differential R] {I : Ideal R} (hrad : I.IsRadical)
    (hδ : ∀ x ∈ I, Differential.deriv x ∈ I) {e : R} (he : e ∉ I) :
    ∃ (L : Type u) (_ : Field L) (_ : Differential L) (f : R →+* L),
      (∀ x : R, f (Differential.deriv x) = Differential.deriv (f x)) ∧ (∀ x ∈ I, f x = 0) ∧
        f e ≠ 0 := by
  classical
  obtain ⟨P, hPprime, hPδ, hIP, hPe⟩ := exists_isPrime_avoiding_radicalDifferential hrad hδ he
  letI : Differential (R ⧸ P) := quotientDifferential P hPδ
  haveI : IsDomain (R ⧸ P) := Ideal.Quotient.isDomain P
  letI : Algebra ℚ (R ⧸ P) := (Ideal.Quotient.mk P).comp (algebraMap ℚ R) |>.toAlgebra
  letI : Differential (FractionRing (R ⧸ P)) := fractionRingDifferential (R ⧸ P)
  refine ⟨FractionRing (R ⧸ P), inferInstance, inferInstance,
    (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P), ?_, ?_, ?_⟩
  · intro x
    show algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P (Differential.deriv x))
      = Differential.deriv (algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P x))
    rw [← quotientDifferential_deriv_mk P hPδ x, fractionRingDifferential_algebraMap]
  · intro x hx
    show algebraMap (R ⧸ P) (FractionRing (R ⧸ P)) (Ideal.Quotient.mk P x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hIP hx), map_zero]
  · intro hzero
    have hmk : (Ideal.Quotient.mk P) e = 0 := by
      have hinj : Function.Injective (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))) :=
        IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P))
      refine hinj ?_
      rw [map_zero]
      exact hzero
    exact hPe (Ideal.Quotient.eq_zero_iff_mem.mp hmk)

end

end GaloisForLFunctions.HTGeometry
