import GaloisForLFunctions.HTGeometry.LocalTwoLayerSpectralResponse

/-!
# Selected-layer spectral response

The two-layer endpoint response extends pairwise to an arbitrary finite local
alphabet.  A perturbation supported on any chosen pair of local labels
produces the same oriented-gap residue packet while every unselected layer
drops out exactly.
-/

open Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Product spectrum with an arbitrary finite local shift packet. -/
def layeredEnergy
    {α ρ : Type*} (energy : α → ℂ) (shift : ρ → ℂ) :
    α × ρ → ℂ :=
  fun p => energy p.1 + shift p.2

/-- Endpoint coupling supported on one selected pair of distinct local
labels. -/
def selectedLayerCoupling
    {α ρ : Type*} [DecidableEq ρ]
    (transition : Matrix α α ℂ) (r s : ρ) :
    Matrix (α × ρ) (α × ρ) ℂ :=
  fun x y =>
    if (x.2 = r ∧ y.2 = s) ∨ (x.2 = s ∧ y.2 = r)
    then transition x.1 y.1
    else 0

/-- A selected pair coupling is zero on the full product diagonal. -/
theorem selectedLayerCoupling_diagonal_zero
    {α ρ : Type*} [DecidableEq ρ]
    (transition : Matrix α α ℂ) {r s : ρ} (hrs : r ≠ s) :
    ∀ i, selectedLayerCoupling transition r s i i = 0 := by
  rintro ⟨a, u⟩
  simp only [selectedLayerCoupling]
  split_ifs with h
  · rcases h with h | h
    · exact (hrs (h.1.symm.trans h.2)).elim
    · exact (hrs (h.2.symm.trans h.1)).elim
  · rfl

/-- For fixed old labels, the selected-layer sum has exactly the two
opposite orientations and no other local contribution. -/
theorem selectedLayer_localResponse_eq
    {α ρ : Type*} [Fintype ρ] [DecidableEq ρ]
    (energy : α → ℂ) (shift : ρ → ℂ)
    (transition : Matrix α α ℂ)
    (coefficient : α × ρ → ℂ)
    {r s : ρ} (hrs : r ≠ s) (a b : α) :
    (∑ u, ∑ v,
      coefficient (a, u) *
        (selectedLayerCoupling transition r s (a, u) (b, v) *
            selectedLayerCoupling transition r s (b, v) (a, u) /
          (layeredEnergy energy shift (a, u) -
            layeredEnergy energy shift (b, v)))) =
      coefficient (a, r) *
          (transition a b * transition b a /
            ((energy a + shift r) - (energy b + shift s))) +
        coefficient (a, s) *
          (transition a b * transition b a /
            ((energy a + shift s) - (energy b + shift r))) := by
  classical
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun u => ∑ v,
      coefficient (a, u) *
        (selectedLayerCoupling transition r s (a, u) (b, v) *
            selectedLayerCoupling transition r s (b, v) (a, u) /
          (layeredEnergy energy shift (a, u) -
            layeredEnergy energy shift (b, v)))) r]
  have hs_ne_r : s ≠ r := Ne.symm hrs
  rw [Finset.sum_eq_single s]
  · rw [Finset.sum_eq_single ⟨s, hs_ne_r⟩]
    · rw [Finset.sum_eq_single r]
      · simp [selectedLayerCoupling, layeredEnergy, hrs, hs_ne_r]
      · intro v hv hvr
        simp [selectedLayerCoupling, layeredEnergy, hs_ne_r, hvr]
      · intro hr
        exact absurd (Finset.mem_univ r) hr
    · intro u hu hus
      apply Finset.sum_eq_zero
      intro v hv
      have hur : (u : ρ) ≠ r := u.2
      have hus' : (u : ρ) ≠ s := by
        exact fun h => hus (Subtype.ext h)
      simp [selectedLayerCoupling, layeredEnergy, hur, hus']
    · intro hs
      exact absurd
        (Finset.mem_univ
          (⟨s, hs_ne_r⟩ : {u : ρ // u ≠ r})) hs
  · intro v hv hvs
    simp [selectedLayerCoupling, layeredEnergy, hrs, hvs]
  · intro hs
    exact absurd (Finset.mem_univ s) hs

/-- **Arbitrary-alphabet selected-pair residue law.** For every chosen
distinct local pair `r,s`, the complete second-order response is the same
simple-pole packet as in the Boolean extension. -/
theorem selectedLayerSecondOrderResponse_eq_residuePacket
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ]
    (energy : α → ℂ) (shift : ρ → ℂ)
    (transition : Matrix α α ℂ)
    (coefficient : α × ρ → ℂ)
    {r s : ρ} (hrs : r ≠ s) :
    (∑ i, coefficient i *
        ∑ j ∈ Finset.univ.erase i,
          selectedLayerCoupling transition r s i j *
              selectedLayerCoupling transition r s j i /
            (layeredEnergy energy shift i -
              layeredEnergy energy shift j)) =
      ∑ a, ∑ b,
        ((coefficient (a, r) - coefficient (b, s)) *
            (transition a b * transition b a)) /
          ((shift r - shift s) + energy a - energy b) := by
  classical
  rw [secondOrderResponse_erase_eq_full
    (layeredEnergy energy shift)
    (selectedLayerCoupling transition r s)
    (selectedLayerCoupling_diagonal_zero transition hrs)
    coefficient]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type, Finset.mul_sum]
  conv_lhs =>
    enter [2, a]
    rw [Finset.sum_comm]
  simp_rw [selectedLayer_localResponse_eq
    energy shift transition coefficient hrs]
  simp_rw [Finset.sum_add_distrib]
  conv_lhs =>
    rhs
    rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [show
      (energy b + shift s) - (energy a + shift r) =
        -((shift r - shift s) + energy a - energy b) by ring,
      div_neg]
  rw [show
      (energy a + shift r) - (energy b + shift s) =
        (shift r - shift s) + energy a - energy b by ring]
  ring

/-- **Every finite local alphabet obeys the selected-pair relation-erasure
law.** An analytic spectral relation for every collision-free value of one
selected layer difference forces coefficient equality across every
nonzero transition product for that pair of local labels. -/
theorem crossLayer_eq_of_selectedLayerAnalyticBranchRelation
    {α ρ : Type*} [Fintype α] [Fintype ρ]
    [DecidableEq α] [DecidableEq ρ] [Nonempty α]
    (energy : α → ℝ) (hmax : MaximallyProjectiveEnergy energy)
    (transition : Matrix α α ℂ)
    (coefficient : α × ρ → ℂ)
    {r s : ρ} (hrs : r ≠ s)
    (S : Set ℂ) (hS : S.Infinite)
    (shift : ℂ → ρ → ℂ)
    (hpairShift :
      ∀ z ∈ S, shift z r - shift z s = z)
    (hsimple :
      ∀ z ∈ S,
        Function.Injective
          (layeredEnergy
            (fun a => (energy a : ℂ)) (shift z)))
    (branch : ℂ → (α × ρ) → ℂ → ℂ)
    (hbranch :
      ∀ z ∈ S, ∀ i, AnalyticAt ℂ (branch z i) 0)
    (hbase :
      ∀ z ∈ S, ∀ i,
        branch z i 0 =
          layeredEnergy
            (fun a => (energy a : ℂ)) (shift z) i)
    (hroot :
      ∀ z ∈ S, ∀ i,
        ∀ᶠ g in 𝓝 0,
          matrixCharpolyRelation
            (Matrix.diagonal
                (layeredEnergy
                  (fun a => (energy a : ℂ)) (shift z)) +
              g • selectedLayerCoupling transition r s,
              branch z i g) = 0)
    (hrelation :
      ∀ z ∈ S,
        ∀ᶠ g in 𝓝 0,
          ∑ i, coefficient i * branch z i g = 0) :
    ∀ a b, a ≠ b →
      transition a b * transition b a ≠ 0 →
      coefficient (a, r) = coefficient (b, s) := by
  have hadmissible :
      ∀ z ∈ S,
        z ∉ twoLayerForbiddenShift
          (fun a => (energy a : ℂ)) := by
    intro z hz hforbidden
    rcases hforbidden with ⟨⟨a, b⟩, hzab⟩
    have hcollision :
        layeredEnergy
            (fun a => (energy a : ℂ)) (shift z) (a, r) =
          layeredEnergy
            (fun a => (energy a : ℂ)) (shift z) (b, s) := by
      unfold layeredEnergy
      have hpair := hpairShift z hz
      change (energy b : ℂ) - energy a = z at hzab
      linear_combination hpair - hzab
    have hpairs := hsimple z hz hcollision
    exact hrs (congrArg Prod.snd hpairs)
  apply crossCoefficient_eq_of_residueIdentity
    energy hmax transition
    (fun a => coefficient (a, r))
    (fun b => coefficient (b, s))
    S hS hadmissible
  intro z hz
  have hresponse :=
    affineEigenbranch_linear_relation_secondOrder
      (layeredEnergy
        (fun a => (energy a : ℂ)) (shift z))
      (hsimple z hz)
      (selectedLayerCoupling transition r s)
      (selectedLayerCoupling_diagonal_zero transition hrs)
      coefficient (branch z)
      (hbranch z hz) (hbase z hz) (hroot z hz)
      (hrelation z hz)
  rw [selectedLayerSecondOrderResponse_eq_residuePacket
    (hrs := hrs)] at hresponse
  rw [hpairShift z hz] at hresponse
  exact hresponse

end

end GaloisForLFunctions.HTGeometry
