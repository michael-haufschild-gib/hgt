import GaloisForLFunctions.HTGeometry.TripticKernelNormalForm
import GaloisForLFunctions.HTGeometry.MeromorphicFieldRealization

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
    (hper : ∀ z : ℂ, F (z + 1) = F z)
    {Cst : ℂ} (hmixed : ∀ z : ℂ, F (z + τ + σ) - F (z + τ) - F (z + σ) + F z = Cst)
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
  -- `G` is exactly `1`-periodic, hence so is `H`
  have hGper : ∀ z : ℂ, G (z + 1) = G z := by
    intro z
    rw [hGdef]
    simp only
    rw [hper z, hAdef, totalAtomSum_periodic F τ σ n Rτ Rσ z]
  have hHper : ∀ z : ℂ, H (z + 1) = H z :=
    periodic_toMeromorphicNFOn_of_eventually_punctured_meromorphic hGmero 1
      (fun z => Filter.Eventually.of_forall fun w => hGper w)
  -- the countable exceptional set
  set N : Set ℂ := {z : ℂ | AnalyticAt ℂ G z}ᶜ with hNdef
  have hNcount : N.Countable := Meromorphic.countable_compl_analyticAt
    (fun z => hGmero z (Set.mem_univ z))
  have hshiftCount : ∀ h : ℂ, {z : ℂ | z + h ∈ N}.Countable := by
    intro h
    have hsub : {z : ℂ | z + h ∈ N} ⊆ (fun u : ℂ => u - h) '' N := by
      intro z hz
      exact ⟨z + h, hz, by ring⟩
    exact Set.Countable.mono hsub (hNcount.image _)
  set S : Set ℂ := totalAtomSumBad τ σ n Rτ Rσ ∪ N ∪ {z : ℂ | z + τ ∈ N} ∪
    {z : ℂ | z + σ ∈ N} ∪ {z : ℂ | z + τ + σ ∈ N} with hSdef
  have hScount : S.Countable := by
    refine ((((countable_totalAtomSumBad τ σ n Rτ Rσ).union hNcount).union
      (hshiftCount τ)).union (hshiftCount σ)).union ?_
    exact hshiftCount (τ + σ) |>.mono (by
      intro z hz
      simpa [add_assoc] using hz)
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
  have hHmix : ∀ z ∉ S, H (z + τ + σ) - H (z + τ) - (H (z + σ) - H z) = Cst := by
    intro z hz
    have hz1 : z ∉ totalAtomSumBad τ σ n Rτ Rσ := fun h =>
      hz (Or.inl (Or.inl (Or.inl (Or.inl h))))
    have hz2 : z ∉ N := fun h => hz (Or.inl (Or.inl (Or.inl (Or.inr h))))
    have hz3 : z + τ ∉ N := fun h => hz (Or.inl (Or.inl (Or.inr h)))
    have hz4 : z + σ ∉ N := fun h => hz (Or.inl (Or.inr h))
    have hz5 : z + τ + σ ∉ N := fun h => hz (Or.inr h)
    rw [hHG _ hz2, hHG _ hz3, hHG _ hz4, hHG _ hz5]
    have hatom := totalAtomSum_mixed_eq_zero hτ hσ F n Rτ Rσ hz1
    have hFmix := hmixed z
    rw [hGdef]
    simp only
    rw [← hAdef] at hatom
    linear_combination hFmix - hatom
  obtain ⟨hHconst, hCst⟩ := const_of_entire_of_class_off_countable hindepτ hindepσ hHdiff hScount
    (fun z _ => hHper z) hHmix
  refine ⟨hCst, n, Rτ, Rσ, H 0, S, hScount, fun z hz => ?_⟩
  have hz2 : z ∉ N := fun h => hz (Or.inl (Or.inl (Or.inl (Or.inr h))))
  have hval : G z = H 0 := by
    rw [← hHG z hz2]
    exact hHconst z 0
  rw [hGdef] at hval
  simp only at hval
  linear_combination hval

end

end GaloisForLFunctions.HTGeometry
