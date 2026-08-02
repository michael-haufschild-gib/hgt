import GaloisForLFunctions.HTGeometry.AnchoredProjectiveRecurrenceConservationLaw
import GaloisForLFunctions.HTGeometry.ComponentReplicaCollisionLaw
import GaloisForLFunctions.HTGeometry.RealFiniteAnalyticEscape

/-!
# Exact projective gap module of a disconnected tensor sum

For a finite family of finite component spectra, every total energy gap is
the sum of its component gaps, and every component gap is realized by a
total gap that changes only that component.  Thus the rational projective
gap module of the tensor-sum spectrum is exactly the supremum of the
component projective gap modules.  This is the unconditional algebraic
identity used by disconnected graph-local spectral factorization.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Tensor-sum energy of a finite family of component spectra. -/
def finiteComponentSumEnergy
    {C : Type*} [Fintype C]
    {I : C → Type*} [∀ c, Fintype (I c)]
    (energy : ∀ c, I c → ℝ)
    (x : ∀ c, I c) : ℝ :=
  ∑ c, energy c (x c)

/-- Changing one component of a product label changes the tensor-sum
energy by exactly that component gap. -/
theorem finiteComponentSumEnergy_update_sub
    {C : Type*} [Fintype C] [DecidableEq C]
    {I : C → Type*} [∀ c, Fintype (I c)]
    (energy : ∀ c, I c → ℝ)
    (reference : ∀ c, I c)
    (c : C) (i : I c) :
    finiteComponentSumEnergy energy
          (Function.update reference c i) -
        finiteComponentSumEnergy energy reference =
      energy c i - energy c (reference c) := by
  classical
  unfold finiteComponentSumEnergy
  rw [← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single c]
  · simp
  · intro d _ hdc
    simp [hdc]
  · simp

/-- **Disconnected projective gap-module equality.**  The projective gap
space of a finite tensor-sum spectrum is exactly the supremum of the
component projective gap spaces.  No genericity, transversality, or
maximal-rank hypothesis is used. -/
theorem anchoredGapSubspace_finiteComponentSumEnergy_eq_iSup
    {C : Type*} [Fintype C] [DecidableEq C]
    {I : C → Type*} [∀ c, Fintype (I c)]
    (energy : ∀ c, I c → ℝ)
    (reference : ∀ c, I c) :
    anchoredGapSubspace
        (finiteComponentSumEnergy energy) reference =
      ⨆ c,
        anchoredGapSubspace (energy c) (reference c) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro _ ⟨x, rfl⟩
    change
      finiteComponentSumEnergy energy x -
          finiteComponentSumEnergy energy reference ∈
        ⨆ c, anchoredGapSubspace (energy c) (reference c)
    unfold finiteComponentSumEnergy
    rw [← Finset.sum_sub_distrib]
    apply Submodule.sum_mem
    intro c _
    exact
      (le_iSup
        (fun d => anchoredGapSubspace (energy d) (reference d)) c)
        (Submodule.subset_span ⟨x c, rfl⟩)
  · apply iSup_le
    intro c
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    have htotal :
        finiteComponentSumEnergy energy
              (Function.update reference c i) -
            finiteComponentSumEnergy energy reference ∈
          anchoredGapSubspace
            (finiteComponentSumEnergy energy) reference :=
      Submodule.subset_span
        ⟨Function.update reference c i, rfl⟩
    rwa [finiteComponentSumEnergy_update_sub] at htotal

/-- Every component projective gap space embeds in the total projective
gap space by changing only that component. -/
theorem anchoredGapSubspace_component_le_total
    {C : Type*} [Fintype C] [DecidableEq C]
    {I : C → Type*} [∀ c, Fintype (I c)]
    (energy : ∀ c, I c → ℝ)
    (reference : ∀ c, I c) (c : C) :
    anchoredGapSubspace (energy c) (reference c) ≤
      anchoredGapSubspace
        (finiteComponentSumEnergy energy) reference := by
  rw [anchoredGapSubspace_finiteComponentSumEnergy_eq_iSup]
  exact le_iSup
    (fun d => anchoredGapSubspace (energy d) (reference d)) c

/-- Evaluation of one componentwise balanced relation after independently
scaling the component spectra. -/
def componentScaleRelation
    {C : Type*} [Fintype C]
    {I : C → Type*} [∀ c, Fintype (I c)]
    (energy : ∀ c, I c → ℝ)
    (k : ∀ c, I c → ℤ)
    (scale : C → ℝ) : ℝ :=
  ∑ c, scale c * ∑ i, (k c i : ℝ) * energy c i

/-- Linear polynomial in component scales representing one balanced
relation. -/
def componentScaleRelationPolynomial
    {C : Type*} [Fintype C]
    {I : C → Type*} [∀ c, Fintype (I c)]
    (energy : ∀ c, I c → ℝ)
    (k : ∀ c, I c → ℤ) :
    MvPolynomial C ℝ :=
  ∑ c,
    MvPolynomial.X c *
      MvPolynomial.C (∑ i, (k c i : ℝ) * energy c i)

theorem eval_componentScaleRelationPolynomial
    {C : Type*} [Fintype C]
    {I : C → Type*} [∀ c, Fintype (I c)]
    (energy : ∀ c, I c → ℝ)
    (k : ∀ c, I c → ℤ)
    (scale : C → ℝ) :
    MvPolynomial.eval scale
        (componentScaleRelationPolynomial energy k) =
      componentScaleRelation energy k scale := by
  simp [componentScaleRelationPolynomial,
    componentScaleRelation, mul_comm]

/-- A nonzero componentwise character has a nonzero component. -/
private theorem exists_component_character_ne_zero
    {C : Type*} {I : C → Type*}
    (k : ∀ c, I c → ℤ) (hk : k ≠ 0) :
    ∃ c, k c ≠ 0 := by
  by_contra h
  push Not at h
  exact hk (funext h)

/-- Every nonzero componentwise balanced relation polynomial is nonzero
when each component spectrum is maximally projective. -/
theorem componentScaleRelationPolynomial_ne_zero
    {C : Type*} [Fintype C] [DecidableEq C]
    {I : C → Type*} [∀ c, Fintype (I c)]
    (energy : ∀ c, I c → ℝ)
    (hmax : ∀ c, MaximallyProjectiveEnergy (energy c))
    (k : ∀ c, I c → ℤ)
    (hbalanced : ∀ c, SpectralCharacterBalanced (k c))
    (hk : k ≠ 0) :
    componentScaleRelationPolynomial energy k ≠ 0 := by
  classical
  obtain ⟨c, hkc⟩ := exists_component_character_ne_zero k hk
  have hvalue :
      (∑ i, (k c i : ℝ) * energy c i) ≠ 0 := by
    intro hzero
    exact hkc (hmax c (k c) (hbalanced c) hzero)
  intro hpoly
  have heval :
      MvPolynomial.eval (Pi.single c 1)
          (componentScaleRelationPolynomial energy k) = 0 := by
    rw [hpoly]
    simp
  rw [eval_componentScaleRelationPolynomial] at heval
  unfold componentScaleRelation at heval
  have hcollapse :
      (∑ d, (Pi.single c (1 : ℝ) : C → ℝ) d *
          ∑ i, (k d i : ℝ) * energy d i) =
        ∑ i, (k c i : ℝ) * energy c i := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hdc
      simp [hdc]
    · simp
  rw [hcollapse] at heval
  exact hvalue heval

/-- **Rational-transverse component scaling.**  Independently scaling any
finite family of maximally projective component spectra can make all
component gap modules mutually projectively independent.  The scales are
obtained by countable real-analytic avoidance; no arithmetic independence
is assumed. -/
theorem exists_scales_componentProjectivelyIndependent
    {C : Type*} [Fintype C] [DecidableEq C]
    {I : C → Type*} [∀ c, Fintype (I c)]
    (energy : ∀ c, I c → ℝ)
    (hmax : ∀ c, MaximallyProjectiveEnergy (energy c)) :
    ∃ scale : C → ℝ,
      ComponentProjectivelyIndependent
        (fun c i => scale c * energy c i) := by
  classical
  let J :=
    {k : ∀ c, I c → ℤ //
      (∀ c, SpectralCharacterBalanced (k c)) ∧ k ≠ 0}
  let f : J → (C → ℝ) → ℝ :=
    fun j scale => componentScaleRelation energy j.1 scale
  have hf :
      ∀ j : J, AnalyticOnNhd ℝ (f j) Set.univ := by
    intro j
    have hfun :
        f j = fun scale =>
          MvPolynomial.eval scale
            (componentScaleRelationPolynomial energy j.1) := by
      funext scale
      exact (eval_componentScaleRelationPolynomial
        energy j.1 scale).symm
    rw [hfun]
    intro scale hscale
    exact
      (AnalyticOnNhd.eval_mvPolynomial
        (componentScaleRelationPolynomial energy j.1))
        scale hscale
  have hne : ∀ j : J, ∃ scale ∈ (Set.univ : Set (C → ℝ)),
      f j scale ≠ 0 := by
    intro j
    have hpoly := componentScaleRelationPolynomial_ne_zero
      energy hmax j.1 j.2.1 j.2.2
    by_contra h
    push Not at h
    apply hpoly
    apply MvPolynomial.funext
    intro scale
    have := h scale (Set.mem_univ scale)
    simpa [f, eval_componentScaleRelationPolynomial] using this
  obtain ⟨scale, _, hscale⟩ :=
    exists_forall_neZero_of_countable_analyticOnNhd_real_local
      f Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty hf hne
  refine ⟨scale, ?_⟩
  intro k hbalanced hrelation c
  by_cases hk : k = 0
  · simp [hk]
  · let j : J := ⟨k, hbalanced, hk⟩
    exfalso
    apply hscale j
    unfold f componentScaleRelation
    calc
      ∑ d, scale d * ∑ i, (k d i : ℝ) * energy d i =
          ∑ d, ∑ i,
            (k d i : ℝ) * (scale d * energy d i) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := hrelation

/-- Labels for all nonreference component gaps. -/
abbrev ComponentAnchoredGapIndex
    {C : Type*} {I : C → Type*}
    (reference : ∀ c, I c) :=
  (c : C) × {i : I c // i ≠ reference c}

/-- One anchored component gap, indexed in the disjoint union of all
component gap packets. -/
def componentAnchoredGap
    {C : Type*} {I : C → Type*}
    (energy : ∀ c, I c → ℝ)
    (reference : ∀ c, I c)
    (ci : ComponentAnchoredGapIndex reference) : ℝ :=
  energy ci.1 ci.2.1 - energy ci.1 (reference ci.1)

/-- Mutual component projective independence makes the disjoint union of
all anchored component gaps rationally linearly independent. -/
theorem componentAnchoredGap_linearIndependent
    {C : Type*} [Fintype C] [DecidableEq C]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (reference : ∀ c, I c)
    (hindependent : ComponentProjectivelyIndependent energy) :
    LinearIndependent ℚ
      (componentAnchoredGap energy reference) := by
  rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let k : ∀ c, I c → ℤ :=
    fun c i =>
      ∑ j : {j : I c // j ≠ reference c},
        g ⟨c, j⟩ *
          ((if i = j.1 then 1 else 0) -
            if i = reference c then 1 else 0)
  have hbalanced :
      ∀ c, SpectralCharacterBalanced (k c) := by
    intro c
    unfold SpectralCharacterBalanced k
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [← Finset.mul_sum]
    simp [Finset.sum_sub_distrib]
  have hrelation :
      (∑ c, ∑ i, (k c i : ℝ) * energy c i) = 0 := by
    calc
      ∑ c, ∑ i, (k c i : ℝ) * energy c i =
          ∑ c, ∑ j : {j : I c // j ≠ reference c},
            (g ⟨c, j⟩ : ℝ) *
              (energy c j.1 - energy c (reference c)) := by
        apply Finset.sum_congr rfl
        intro c _
        unfold k
        push_cast
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        simp_rw [mul_assoc]
        rw [← Finset.mul_sum]
        congr 1
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
        simp
      _ = ∑ ci : ComponentAnchoredGapIndex reference,
          (g ci : ℝ) * componentAnchoredGap energy reference ci := by
        rw [Fintype.sum_sigma]
        rfl
      _ = 0 := by
        simpa [componentAnchoredGap, zsmul_eq_mul] using hg
  have hk : ∀ c, k c = 0 :=
    hindependent k hbalanced hrelation
  intro ci
  have hci := congrFun (hk ci.1) ci.2.1
  unfold k at hci
  rw [Finset.sum_eq_single ci.2] at hci
  · simpa [ci.2.2] using hci
  · intro j _ hj
    have hjval : ci.2.1 ≠ j.1 := by
      intro h
      exact hj (Subtype.ext h.symm)
    simp [hjval, ci.2.2]
  · simp

/-- Supremum of component gap spaces is the span of the disjoint union of
the component anchored-gap packets. -/
theorem iSup_anchoredGapSubspace_eq_span_componentAnchoredGap
    {C : Type*} [Fintype C] [DecidableEq C]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (reference : ∀ c, I c) :
    (⨆ c, anchoredGapSubspace (energy c) (reference c)) =
      Submodule.span ℚ
        (Set.range (componentAnchoredGap energy reference)) := by
  apply le_antisymm
  · apply iSup_le
    intro c
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = reference c
    · simp [hi]
    · exact Submodule.subset_span
        ⟨⟨c, ⟨i, hi⟩⟩, rfl⟩
  · apply Submodule.span_le.2
    rintro _ ⟨ci, rfl⟩
    exact
      (le_iSup
        (fun c => anchoredGapSubspace (energy c) (reference c)) ci.1)
        (Submodule.subset_span ⟨ci.2.1, rfl⟩)

/-- Under mutual projective independence, total disconnected temporal
rank is the sum of the maximal component ranks. -/
theorem anchoredTemporalRank_finiteComponentSumEnergy_eq_sum
    {C : Type*} [Fintype C] [DecidableEq C]
    {I : C → Type*} [∀ c, Fintype (I c)]
    [∀ c, DecidableEq (I c)]
    (energy : ∀ c, I c → ℝ)
    (reference : ∀ c, I c)
    (hindependent : ComponentProjectivelyIndependent energy) :
    anchoredTemporalRank
        (finiteComponentSumEnergy energy) reference =
      ∑ c, (Fintype.card (I c) - 1) := by
  unfold anchoredTemporalRank
  rw [anchoredGapSubspace_finiteComponentSumEnergy_eq_iSup,
    iSup_anchoredGapSubspace_eq_span_componentAnchoredGap]
  rw [finrank_span_eq_card
    (componentAnchoredGap_linearIndependent
      energy reference hindependent)]
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro c _
  exact Set.card_ne_eq (reference c)

end

end GaloisForLFunctions.HTGeometry
