import GaloisForLFunctions.HTGeometry.TripticKernelNormalForm
import GaloisForLFunctions.HTGeometry.MeromorphicFieldRealization
import GaloisForLFunctions.HTGeometry.TripticGermConstraint

/-!
# The kernel of the orbital divisor

A source with vanishing orbital divisor differs from an explicit finite combination of theta-source
jets by a constant, off a countable set; and its mixed constant is forced to vanish.

The difference has no principal part anywhere, so its canonical normal form is entire.  That normal
form is `1`-periodic exactly, because both the source and the atom sum are, and has constant mixed
second difference off the countable union of the atoms' pole lattices and the source's own
non-analytic points.  Pole-free rigidity then makes it constant.

* `exists_const_sub_totalAtomSum_of_vanishing_divisor`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

variable {F : ℂ → ℂ} {τ σ : ℂ}

set_option maxHeartbeats 1000000 in
/-- **The kernel identification.**  A `1`-periodic meromorphic function with constant mixed
difference whose orbital divisor vanishes is, off a countable set, an explicit finite combination of
theta-source jets plus a constant — and its mixed constant is zero. -/
theorem exists_const_sub_totalAtomSum_of_vanishing_divisor
    (hF : MeromorphicOn F Set.univ)
    (hper : PeriodicOneGerm F)
    {Cst : ℂ} (hmixed : MixedConstGerm F τ σ Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])
    (hvanish : ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
      ∑ᶠ m : ℤ, laurentCoeff (fun z => F (z + σ) - F z) (p + (m : ℂ) * σ) ℓ = 0) :
    Cst = 0 ∧ ∃ (n : ℕ) (Rτ Rσ : ℕ → Finset ℂ) (c : ℂ) (S : Set ℂ), S.Countable ∧
      ∀ z ∉ S, F z = totalAtomSum F τ σ n Rτ Rσ z + c := by
  classical
  obtain ⟨n, Rτ, Rσ, hnf⟩ := exists_totalAtomSum_no_principal_part hF hper hmixed hτ hσ hindep
    hindepτ hindepσ hvanish
  set A : ℂ → ℂ := totalAtomSum F τ σ n Rτ Rσ with hAdef
  set G : ℂ → ℂ := fun z => F z - A z with hGdef
  have hAmero : ∀ z : ℂ, MeromorphicAt A z := fun z =>
    meromorphicAt_totalAtomSum hτ hσ F n Rτ Rσ z
  have hGmero : MeromorphicOn G Set.univ := fun z _ =>
    (hF z (Set.mem_univ z)).sub (hAmero z)
  -- the difference has no principal part
  have hpp : ∀ (w : ℂ) (ℓ : ℤ), ℓ < 0 → laurentCoeff G w ℓ = 0 := by
    intro w ℓ hℓ
    rw [hGdef, laurentCoeff_sub (hF w (Set.mem_univ w)) (hAmero w) ℓ, ← hnf w ℓ hℓ, sub_self]
  -- so its normal form is entire
  set H : ℂ → ℂ := toMeromorphicNFOn G Set.univ with hHdef
  have hHdiff : Differentiable ℂ H := differentiable_toMeromorphicNFOn_of_no_principal_part
    hGmero hpp
  -- `G` is germ `1`-periodic, so its normal form is exactly `1`-periodic
  have hGper : ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, G (w + 1) = G w := by
    intro z
    filter_upwards [hper z] with w hw
    rw [hGdef]
    simp only
    rw [hw, hAdef, totalAtomSum_periodic F τ σ n Rτ Rσ w]
  have hHper : ∀ z : ℂ, H (z + 1) = H z :=
    periodic_toMeromorphicNFOn_of_eventually_punctured_meromorphic hGmero 1 hGper
  -- the countable exceptional set
  set N : Set ℂ := {z : ℂ | AnalyticAt ℂ G z}ᶜ with hNdef
  have hNcount : N.Countable := Meromorphic.countable_compl_analyticAt
    (fun z => hGmero z (Set.mem_univ z))
  set NF : Set ℂ := {z : ℂ | AnalyticAt ℂ F z}ᶜ with hNFdef
  have hNFcount : NF.Countable := Meromorphic.countable_compl_analyticAt
    (fun z => hF z (Set.mem_univ z))
  have hshiftCount : ∀ T : Set ℂ, T.Countable → ∀ h : ℂ, {z : ℂ | z + h ∈ T}.Countable := by
    intro T hT h
    have hsub : {z : ℂ | z + h ∈ T} ⊆ (fun u : ℂ => u - h) '' T := by
      intro z hz
      exact ⟨z + h, hz, by ring⟩
    exact Set.Countable.mono hsub (hT.image _)
  have hshiftCount' : ∀ T : Set ℂ, T.Countable → {z : ℂ | z + τ + σ ∈ T}.Countable := by
    intro T hT
    exact hshiftCount T hT (τ + σ) |>.mono (by
      intro z hz
      simpa [add_assoc] using hz)
  set S : Set ℂ := totalAtomSumBad τ σ n Rτ Rσ ∪ N ∪ {z : ℂ | z + τ ∈ N} ∪
    {z : ℂ | z + σ ∈ N} ∪ {z : ℂ | z + τ + σ ∈ N} ∪ NF ∪ {z : ℂ | z + τ ∈ NF} ∪
    {z : ℂ | z + σ ∈ NF} ∪ {z : ℂ | z + τ + σ ∈ NF} with hSdef
  have hScount : S.Countable :=
    ((((((((countable_totalAtomSumBad τ σ n Rτ Rσ).union hNcount).union
      (hshiftCount N hNcount τ)).union (hshiftCount N hNcount σ)).union
      (hshiftCount' N hNcount)).union hNFcount).union
      (hshiftCount NF hNFcount τ)).union (hshiftCount NF hNFcount σ)).union
      (hshiftCount' NF hNFcount)
  -- off `N` the normal form is the difference itself
  have hHG : ∀ a : ℂ, a ∉ N → H a = G a := by
    intro a ha
    have hGa : AnalyticAt ℂ G a := by
      rw [hNdef] at ha
      simpa using ha
    have hpunct : H =ᶠ[𝓝[≠] a] G :=
      hGmero.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ a)
    exact (eventuallyEq_nhds_of_nhdsNE_of_continuousAt hpunct
      (hHdiff a).continuousAt hGa.continuousAt).eq_of_nhds
  -- the mixed relation for the normal form
  have hanF : ∀ a : ℂ, a ∉ NF → AnalyticAt ℂ F a := by
    intro a ha
    rw [hNFdef] at ha
    simpa using ha
  have hHmix : ∀ z ∉ S, H (z + τ + σ) - H (z + τ) - (H (z + σ) - H z) = Cst := by
    intro z hz
    rw [hSdef] at hz
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq] at hz
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz1, hz2⟩, hz3⟩, hz4⟩, hz5⟩, hz6⟩, hz7⟩, hz8⟩, hz9⟩ := hz
    rw [hHG _ hz2, hHG _ hz3, hHG _ hz4, hHG _ hz5]
    have hatom := totalAtomSum_mixed_eq_zero hτ hσ F n Rτ Rσ hz1
    have hFmix := mixedConst_eq_of_analyticAt hmixed (hanF z hz6) (hanF (z + τ) hz7)
      (hanF (z + σ) hz8) (hanF (z + τ + σ) hz9)
    rw [hGdef]
    simp only
    rw [← hAdef] at hatom
    linear_combination hFmix - hatom
  obtain ⟨hHconst, hCst⟩ := const_of_entire_of_class_off_countable hindepτ hindepσ hHdiff hScount
    (fun z _ => hHper z) hHmix
  refine ⟨hCst, n, Rτ, Rσ, H 0, S, hScount, fun z hz => ?_⟩
  rw [hSdef] at hz
  simp only [Set.mem_union, not_or, Set.mem_setOf_eq] at hz
  have hz2 : z ∉ N := hz.1.1.1.1.1.1.1.2
  have hval : G z = H 0 := by
    rw [← hHG z hz2]
    exact hHconst z 0
  rw [hGdef] at hval
  simp only at hval
  linear_combination hval

end

end GaloisForLFunctions.HTGeometry
