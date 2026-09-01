import GaloisForLFunctions.HTGeometry.RadicalDifferentialIdealAvoiding

/-!
# Radical differential ideals avoiding a multiplicative set

The differential prime-avoidance argument extends from one element to an arbitrary submonoid.
This form constructs differential generic points whose selected coordinate remains transcendental.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {R : Type*} [CommRing R] [Differential R]

/-- A maximal radical differential ideal disjoint from a prescribed submonoid exists. -/
theorem exists_maximal_disjoint_radicalDifferential
    {I₀ : Ideal R} (hrad : I₀.IsRadical)
    (hδ : ∀ x ∈ I₀, Differential.deriv x ∈ I₀)
    (M : Submonoid R) (hdisj : Disjoint (I₀ : Set R) (M : Set R)) :
    ∃ P : Ideal R, P.IsRadical ∧ (∀ x ∈ P, Differential.deriv x ∈ P) ∧ I₀ ≤ P ∧
      Disjoint (P : Set R) (M : Set R) ∧
      ∀ J : Ideal R, J.IsRadical → (∀ x ∈ J, Differential.deriv x ∈ J) → P ≤ J →
        Disjoint (J : Set R) (M : Set R) → J = P := by
  classical
  let S : Set (Ideal R) :=
    {I | I.IsRadical ∧ (∀ x ∈ I, Differential.deriv x ∈ I) ∧ I₀ ≤ I ∧
      Disjoint (I : Set R) (M : Set R)}
  have hbound : ∀ c ⊆ S, IsChain (· ≤ ·) c → ∃ ub ∈ S, ∀ z ∈ c, z ≤ ub := by
    intro c hcS hc
    rcases Set.eq_empty_or_nonempty c with rfl | hnec
    · exact ⟨I₀, ⟨hrad, hδ, le_rfl, hdisj⟩, by simp⟩
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
    · rw [Set.disjoint_left]
      intro x hx hxM
      have hx' : x ∈ sSup c := hx
      rw [Submodule.mem_sSup_of_directed hnec hc.directedOn] at hx'
      obtain ⟨J, hJc, hxJ⟩ := hx'
      exact Set.disjoint_left.mp (hcS hJc).2.2.2 hxJ hxM
  obtain ⟨P, hP⟩ := zorn_le₀ S hbound
  refine ⟨P, hP.1.1, hP.1.2.1, hP.1.2.2.1, hP.1.2.2.2, ?_⟩
  intro J hJrad hJδ hle hJdisj
  exact le_antisymm (hP.2 ⟨hJrad, hJδ, le_trans hP.1.2.2.1 hle, hJdisj⟩ hle) hle

/-- A maximal radical differential ideal disjoint from a submonoid is prime. -/
theorem isPrime_of_maximal_disjoint_radicalDifferential
    {P : Ideal R} (hrad : P.IsRadical)
    (hδ : ∀ x ∈ P, Differential.deriv x ∈ P)
    (M : Submonoid R) (hdisj : Disjoint (P : Set R) (M : Set R))
    (hmax : ∀ J : Ideal R, J.IsRadical → (∀ x ∈ J, Differential.deriv x ∈ J) → P ≤ J →
      Disjoint (J : Set R) (M : Set R) → J = P) : P.IsPrime := by
  classical
  have hproper : P ≠ ⊤ := by
    intro htop
    have honeP : (1 : R) ∈ P := by rw [htop]; trivial
    exact Set.disjoint_left.mp hdisj honeP M.one_mem
  refine ⟨hproper, ?_⟩
  intro a b hab
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨ha, hb⟩ := hcon
  have hgen : ∀ x : R, x ∉ P →
      ∃ s : R, s ∈ M ∧ s ∈ radicalDifferentialIdeal ((P : Set R) ∪ {x}) := by
    intro x hx
    let J := radicalDifferentialIdeal ((P : Set R) ∪ {x})
    have hle : P ≤ J := fun y hy => subset_radicalDifferentialIdeal _ (Or.inl hy)
    have hxJ : x ∈ J := subset_radicalDifferentialIdeal _ (Or.inr rfl)
    by_contra hnone
    push Not at hnone
    have hJdisj : Disjoint (J : Set R) (M : Set R) := by
      rw [Set.disjoint_left]
      intro s hsJ hsM
      exact hnone s hsM hsJ
    have heq := hmax J (isRadical_radicalDifferentialIdeal _)
      (deriv_mem_radicalDifferentialIdeal _) hle hJdisj
    rw [heq] at hxJ
    exact hx hxJ
  obtain ⟨s, hsM, hs⟩ := hgen a ha
  obtain ⟨t, htM, ht⟩ := hgen b hb
  have hprod : ∀ x ∈ ((P : Set R) ∪ {a}), ∀ y ∈ ((P : Set R) ∪ {b}), x * y ∈ P := by
    rintro x (hx | rfl) y (hy | rfl)
    · exact Ideal.mul_mem_right _ _ hx
    · exact Ideal.mul_mem_right _ _ hx
    · exact Ideal.mul_mem_left _ _ hy
    · exact hab
  have hst : s * t ∈ P := mul_mem_of_forall_mul_mem hrad hδ hprod hs ht
  exact Set.disjoint_left.mp hdisj hst (M.mul_mem hsM htM)

/-- Every radical differential ideal disjoint from a submonoid lies below a prime differential
ideal still disjoint from that submonoid. -/
theorem exists_isPrime_disjoint_radicalDifferential
    {I₀ : Ideal R} (hrad : I₀.IsRadical)
    (hδ : ∀ x ∈ I₀, Differential.deriv x ∈ I₀)
    (M : Submonoid R) (hdisj : Disjoint (I₀ : Set R) (M : Set R)) :
    ∃ P : Ideal R, P.IsPrime ∧ (∀ x ∈ P, Differential.deriv x ∈ P) ∧ I₀ ≤ P ∧
      Disjoint (P : Set R) (M : Set R) := by
  obtain ⟨P, hPrad, hPδ, hIP, hPdisj, hPmax⟩ :=
    exists_maximal_disjoint_radicalDifferential hrad hδ M hdisj
  exact ⟨P, isPrime_of_maximal_disjoint_radicalDifferential hPrad hPδ M hPdisj hPmax,
    hPδ, hIP, hPdisj⟩

end

end GaloisForLFunctions.HTGeometry
