import GaloisForLFunctions.HTGeometry.QuasiAbelianEnlargedPacket

/-!
# Finite complement-translate vanishing from lower jet ampleness

At one subgroup-rank extension, a lower-factor section must retain prescribed mixed jets on the
original packet and vanish through the same orders at finitely many nonzero complement translates.
This is not a new analytic interpolation problem: those points form one larger packet for the lower
lattice.  Consequently lower all-order jet ampleness constructs all columns needed by the finite
damping argument.

This theorem deliberately supplies no global normalized-growth bound.  That quantitative bound is
the remaining analytic core of the all-order Abe extension, and cannot follow from surjectivity of
a finite jet-evaluation map alone.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- **Finite complement-translate vanishing.**  A jet-ample lower factor supplies, for every
finite set of complement indices, lower-automorphic columns with prescribed original packet jets
and zero jets at every selected nonzero complement translate. -/
theorem AutomorphicFactor.exists_jetColumns_with_finite_complement_vanishing
    {d c : ℕ} {ΓH Γ : AddSubgroup (Fin d → ℂ)}
    (lower : AutomorphicFactor d ΓH)
    (hlower : AutomorphicFactor.JetAmpleEveryFiniteOrder.{u} lower)
    (hle : ΓH ≤ Γ)
    {I T : Type u} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
    (w : I → Fin d → ℂ) (m : I → ℕ) (hm : ∀ i, 0 < m i)
    (comp : (Fin c → ℤ) →+ (Fin d → ℂ))
    (comp_mem : ∀ z, comp z ∈ Γ)
    (comp_not_mem_lower : ∀ z, comp z ∈ ΓH → z = 0)
    (t : T → Fin c → ℤ) (ht : Function.Injective t)
    (s₀ : T) (hs₀ : t s₀ = 0)
    (hdistinct : PairwiseDistinctModulo Γ w)
    (lowerColumn : FiniteJetPacketIndex d I m → lower.forms) :
    ∃ seed : FiniteJetPacketIndex d I m → lower.forms,
      (∀ j (i : FiniteJetPacketIndex d I m),
        multiIndexJetEvalCLM (w i.1) i.2.1 (seed j).1 =
          multiIndexJetEvalCLM (w i.1) i.2.1 (lowerColumn j).1) ∧
      (∀ j (i : I) s (a : FiniteJetMultiIndex d (m i)), s ≠ s₀ →
        multiIndexJetEvalCLM (w i + comp (t s)) a.1 (seed j).1 = 0) := by
  classical
  let w' : I × T → Fin d → ℂ := enlargedPacketPoints w comp t
  let m' : I × T → ℕ := fun p => m p.1
  have hm' : ∀ p, 0 < m' p := fun p => hm p.1
  have hdistinct' : PairwiseDistinctModulo ΓH w' := by
    simpa only [w'] using pairwiseDistinctModulo_enlargedPacketPoints hle comp_mem
      comp_not_mem_lower ht hdistinct
  have hsurj : Function.Surjective (lower.jetPacketLinearMap w' m') :=
    hlower (I × T) w' m' hdistinct' hm'
  let seed : FiniteJetPacketIndex d I m → lower.forms := fun j =>
    Classical.choose (hsurj fun q =>
      if q.1.2 = s₀ then
        multiIndexJetEvalCLM (w q.1.1) q.2.1 (lowerColumn j).1
      else 0)
  have hseed (j : FiniteJetPacketIndex d I m) :
      lower.jetPacketLinearMap w' m' (seed j) = fun q =>
        if q.1.2 = s₀ then
          multiIndexJetEvalCLM (w q.1.1) q.2.1 (lowerColumn j).1
        else 0 :=
    Classical.choose_spec (hsurj fun q =>
      if q.1.2 = s₀ then
        multiIndexJetEvalCLM (w q.1.1) q.2.1 (lowerColumn j).1
      else 0)
  refine ⟨seed, ?_, ?_⟩
  · intro j i
    let q : FiniteJetPacketIndex d (I × T) m' := ⟨(i.1, s₀), i.2⟩
    have h := congrFun (hseed j) q
    simpa [AutomorphicFactor.jetPacketLinearMap_apply, w', m', q, hs₀] using h
  · intro j i s a hs
    let q : FiniteJetPacketIndex d (I × T) m' := ⟨(i, s), a⟩
    have h := congrFun (hseed j) q
    simpa [AutomorphicFactor.jetPacketLinearMap_apply, w', m', q, hs] using h

end

end GaloisForLFunctions.HTGeometry
