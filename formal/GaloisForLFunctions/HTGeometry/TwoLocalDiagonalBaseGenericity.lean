import GaloisForLFunctions.HTGeometry.EdgeBlockReindex
import GaloisForLFunctions.HTGeometry.FiniteHyperplaneAvoidance
import GaloisForLFunctions.HTGeometry.TwoLocalUniversalHypercubeFamily

/-!
# A two-local diagonal base with simple spectrum and simple edge gaps

The diagonal part of the all-qubit two-local family is affine in its coefficients, with an explicit
slope along each coefficient direction: moving one onsite coefficient moves one energy difference,
and moving one interaction coefficient moves one edge gap.  Each unwanted coincidence -- two equal
energies, or two equal edge gaps of the same qubit -- is therefore a hyperplane in coefficient
space, while the positivity of all edge gaps holds on a nonempty open set.

Hyperplanes cannot cover an open set, so there is a two-local diagonal Hamiltonian whose `2^n`
energies are pairwise distinct and whose edge gaps are, for every qubit, positive and pairwise
distinct.  That is exactly the base point required by the block splitting escape.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-- Real diagonal energy of the all-qubit two-local family. -/
def hypercubeTwoLocalEnergy (p : HypercubeTwoLocalParameter n → ℝ) (x : Fin n → Bool) : ℝ :=
  p .constant + ∑ i, p (.onsite i) * (boolOccupation (x i) : ℝ)
    + ∑ i, ∑ j, p (.interaction i j) * (boolOccupation (x i) : ℝ) *
        (boolOccupation (x j) : ℝ)

theorem continuous_hypercubeTwoLocalEnergy (x : Fin n → Bool) :
    Continuous fun p : HypercubeTwoLocalParameter n → ℝ => hypercubeTwoLocalEnergy p x := by
  unfold hypercubeTwoLocalEnergy
  refine ((continuous_apply _).add ?_).add ?_
  · exact continuous_finsetSum _ fun i _ => (continuous_apply _).mul continuous_const
  · exact continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => ((continuous_apply _).mul continuous_const).mul
        continuous_const

/-- Moving one onsite coefficient moves every energy by that occupation number. -/
theorem hypercubeTwoLocalEnergy_shift_onsite (p : HypercubeTwoLocalParameter n → ℝ)
    (x : Fin n → Bool) (i₀ : Fin n) (δ : ℝ) :
    hypercubeTwoLocalEnergy
        (p + δ • (Pi.single (HypercubeTwoLocalParameter.onsite i₀) (1 : ℝ))) x
      = hypercubeTwoLocalEnergy p x + δ * (boolOccupation (x i₀) : ℝ) := by
  classical
  set Δ : HypercubeTwoLocalParameter n → ℝ :=
    δ • (Pi.single (HypercubeTwoLocalParameter.onsite i₀) (1 : ℝ)) with hΔ
  have h0 : (p + Δ) HypercubeTwoLocalParameter.constant
      = p HypercubeTwoLocalParameter.constant := by
    simp [hΔ]
  have h1 : (∑ i, (p + Δ) (.onsite i) * (boolOccupation (x i) : ℝ))
      = (∑ i, p (.onsite i) * (boolOccupation (x i) : ℝ)) + δ * (boolOccupation (x i₀) : ℝ) := by
    have hterm : ∀ i : Fin n, (p + Δ) (.onsite i) * (boolOccupation (x i) : ℝ)
        = p (.onsite i) * (boolOccupation (x i) : ℝ)
          + (if i = i₀ then δ * (boolOccupation (x i₀) : ℝ) else 0) := by
      intro i
      by_cases hi : i = i₀
      · subst hi
        simp [hΔ]
        ring
      · simp [hΔ, hi]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i₀ fun _ => δ * (boolOccupation (x i₀) : ℝ)]
    simp
  have h2 : (∑ i, ∑ j, (p + Δ) (.interaction i j) * (boolOccupation (x i) : ℝ) *
        (boolOccupation (x j) : ℝ))
      = ∑ i, ∑ j, p (.interaction i j) * (boolOccupation (x i) : ℝ) *
          (boolOccupation (x j) : ℝ) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have : (p + Δ) (.interaction i j) = p (.interaction i j) := by
      simp [hΔ]
    rw [this]
  rw [hypercubeTwoLocalEnergy, hypercubeTwoLocalEnergy, h0, h1, h2]
  ring

/-- Moving one interaction coefficient moves every energy by that pair occupation number. -/
theorem hypercubeTwoLocalEnergy_shift_interaction (p : HypercubeTwoLocalParameter n → ℝ)
    (x : Fin n → Bool) (i₀ j₀ : Fin n) (δ : ℝ) :
    hypercubeTwoLocalEnergy
        (p + δ • (Pi.single (HypercubeTwoLocalParameter.interaction i₀ j₀) (1 : ℝ))) x
      = hypercubeTwoLocalEnergy p x
          + δ * ((boolOccupation (x i₀) : ℝ) * (boolOccupation (x j₀) : ℝ)) := by
  classical
  set Δ : HypercubeTwoLocalParameter n → ℝ :=
    δ • (Pi.single (HypercubeTwoLocalParameter.interaction i₀ j₀) (1 : ℝ)) with hΔ
  have h0 : (p + Δ) HypercubeTwoLocalParameter.constant
      = p HypercubeTwoLocalParameter.constant := by
    simp [hΔ]
  have h1 : (∑ i, (p + Δ) (.onsite i) * (boolOccupation (x i) : ℝ))
      = ∑ i, p (.onsite i) * (boolOccupation (x i) : ℝ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (p + Δ) (.onsite i) = p (.onsite i) := by simp [hΔ]
    rw [this]
  have h2 : (∑ i, ∑ j, (p + Δ) (.interaction i j) * (boolOccupation (x i) : ℝ) *
        (boolOccupation (x j) : ℝ))
      = (∑ i, ∑ j, p (.interaction i j) * (boolOccupation (x i) : ℝ) *
          (boolOccupation (x j) : ℝ))
        + δ * ((boolOccupation (x i₀) : ℝ) * (boolOccupation (x j₀) : ℝ)) := by
    have hrow : ∀ i : Fin n,
        (∑ j, (p + Δ) (.interaction i j) * (boolOccupation (x i) : ℝ) *
            (boolOccupation (x j) : ℝ))
          = (∑ j, p (.interaction i j) * (boolOccupation (x i) : ℝ) *
              (boolOccupation (x j) : ℝ))
            + (if i = i₀ then
                δ * ((boolOccupation (x i₀) : ℝ) * (boolOccupation (x j₀) : ℝ)) else 0) := by
      intro i
      have hterm : ∀ j : Fin n, (p + Δ) (.interaction i j) * (boolOccupation (x i) : ℝ) *
            (boolOccupation (x j) : ℝ)
          = p (.interaction i j) * (boolOccupation (x i) : ℝ) * (boolOccupation (x j) : ℝ)
            + (if j = j₀ then (if i = i₀ then
                δ * ((boolOccupation (x i₀) : ℝ) * (boolOccupation (x j₀) : ℝ))
                else 0) else 0) := by
        intro j
        by_cases hj : j = j₀
        · subst hj
          by_cases hi : i = i₀
          · subst hi
            simp [hΔ]
            ring
          · simp [hΔ, hi]
        · simp [hΔ, hj]
      rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ j₀ fun _ => (if i = i₀ then
          δ * ((boolOccupation (x i₀) : ℝ) * (boolOccupation (x j₀) : ℝ)) else 0)]
      simp
    rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i₀ fun _ =>
        δ * ((boolOccupation (x i₀) : ℝ) * (boolOccupation (x j₀) : ℝ))]
    simp
  rw [hypercubeTwoLocalEnergy, hypercubeTwoLocalEnergy, h0, h1, h2]
  ring


/-- The edge gaps of the two-local diagonal family, as functions of the coefficients. -/
noncomputable def twoLocalEdgeGap (i : Fin n) (z : qubitEnvironment n i)
    (p : HypercubeTwoLocalParameter n → ℝ) : ℝ :=
  edgeGap i (hypercubeTwoLocalEnergy p) z

theorem continuous_twoLocalEdgeGap (i : Fin n) (z : qubitEnvironment n i) :
    Continuous (twoLocalEdgeGap i z) := by
  unfold twoLocalEdgeGap edgeGap
  exact ((continuous_hypercubeTwoLocalEnergy _).sub
    (continuous_hypercubeTwoLocalEnergy _)).div_const 2

/-- Moving the interaction coefficient of the distinguished qubit with one of its neighbours moves
that qubit's edge gaps by the neighbour's occupation number. -/
theorem twoLocalEdgeGap_shift_interaction (i : Fin n) (z : qubitEnvironment n i) {j : Fin n}
    (hj : j ≠ i) (p : HypercubeTwoLocalParameter n → ℝ) (δ : ℝ) :
    twoLocalEdgeGap i z
        (p + δ • (Pi.single (HypercubeTwoLocalParameter.interaction i j) (1 : ℝ)))
      = twoLocalEdgeGap i z p + δ * (-(boolOccupation (z ⟨j, hj⟩) : ℝ) / 2) := by
  simp only [twoLocalEdgeGap, edgeGap, hypercubeTwoLocalEnergy_shift_interaction,
    edgeState_self, edgeState_of_ne i z _ hj]
  simp only [boolOccupation, if_true]
  push_cast
  ring

/-- Moving one onsite coefficient moves the difference of two energies. -/
theorem energyDifference_shift_onsite (x y : Fin n → Bool) (i₀ : Fin n)
    (p : HypercubeTwoLocalParameter n → ℝ) (δ : ℝ) :
    (hypercubeTwoLocalEnergy (p + δ • (Pi.single (HypercubeTwoLocalParameter.onsite i₀) (1 : ℝ))) x
        - hypercubeTwoLocalEnergy
            (p + δ • (Pi.single (HypercubeTwoLocalParameter.onsite i₀) (1 : ℝ))) y)
      = (hypercubeTwoLocalEnergy p x - hypercubeTwoLocalEnergy p y)
        + δ * ((boolOccupation (x i₀) : ℝ) - (boolOccupation (y i₀) : ℝ)) := by
  rw [hypercubeTwoLocalEnergy_shift_onsite, hypercubeTwoLocalEnergy_shift_onsite]
  ring

/-- Occupation numbers of the two ends of an edge differ by one. -/
theorem sum_occupation_edgeState_diff (i : Fin n) (z : qubitEnvironment n i) :
    (∑ j, (boolOccupation (edgeState i z true j) : ℝ))
      = (∑ j, (boolOccupation (edgeState i z false j) : ℝ)) + 1 := by
  classical
  have herase : (∑ j ∈ Finset.univ.erase i, (boolOccupation (edgeState i z true j) : ℝ))
      = ∑ j ∈ Finset.univ.erase i, (boolOccupation (edgeState i z false j) : ℝ) := by
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [edgeState_of_ne i z true hji, edgeState_of_ne i z false hji]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), ← Finset.sum_erase_add _ _ (Finset.mem_univ i),
    herase, edgeState_self, edgeState_self]
  simp [boolOccupation]

/-- Coefficients with all onsite terms equal to minus one. -/
def negativeOnsiteParameters (n : ℕ) : HypercubeTwoLocalParameter n → ℝ
  | .constant => 0
  | .onsite _ => -1
  | .interaction _ _ => 0
  | .transverse _ => 0

theorem hypercubeTwoLocalEnergy_negativeOnsite (x : Fin n → Bool) :
    hypercubeTwoLocalEnergy (negativeOnsiteParameters n) x
      = -(∑ i, (boolOccupation (x i) : ℝ)) := by
  simp only [hypercubeTwoLocalEnergy, negativeOnsiteParameters]
  rw [show (∑ i, ∑ j, (0 : ℝ) * (boolOccupation (x i) : ℝ) * (boolOccupation (x j) : ℝ)) = 0 by
    simp]
  rw [show (∑ i, (-1 : ℝ) * (boolOccupation (x i) : ℝ))
      = -(∑ i, (boolOccupation (x i) : ℝ)) by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring]
  ring

theorem twoLocalEdgeGap_negativeOnsite (i : Fin n) (z : qubitEnvironment n i) :
    twoLocalEdgeGap i z (negativeOnsiteParameters n) = 1 / 2 := by
  rw [twoLocalEdgeGap, edgeGap, hypercubeTwoLocalEnergy_negativeOnsite,
    hypercubeTwoLocalEnergy_negativeOnsite, sum_occupation_edgeState_diff]
  ring


/-- Coincidences that a two-local diagonal base must avoid: two equal energies, or two equal edge
gaps of the same qubit. -/
abbrev TwoLocalBaseCondition (n : ℕ) : Type :=
  {q : (Fin n → Bool) × (Fin n → Bool) // q.1 ≠ q.2} ⊕
    ((i : Fin n) × {q : qubitEnvironment n i × qubitEnvironment n i // q.1 ≠ q.2})

/-- The functional whose vanishing is the corresponding coincidence. -/
noncomputable def twoLocalBaseFunctional :
    TwoLocalBaseCondition n → (HypercubeTwoLocalParameter n → ℝ) → ℝ
  | .inl q => fun p => hypercubeTwoLocalEnergy p q.1.1 - hypercubeTwoLocalEnergy p q.1.2
  | .inr q => fun p => twoLocalEdgeGap q.1 q.2.1.1 p - twoLocalEdgeGap q.1 q.2.1.2 p

/-- **A two-local diagonal base with simple spectrum and simple positive edge gaps.**  The `2^n`
energies are pairwise distinct, and for every qubit the edge gaps are positive and pairwise
distinct. -/
theorem exists_twoLocalDiagonalBase (n : ℕ) :
    ∃ p : HypercubeTwoLocalParameter n → ℝ,
      Function.Injective (hypercubeTwoLocalEnergy p) ∧
      (∀ (i : Fin n) (z : qubitEnvironment n i), 0 < edgeGap i (hypercubeTwoLocalEnergy p) z) ∧
      (∀ i : Fin n, Function.Injective (edgeGap i (hypercubeTwoLocalEnergy p))) := by
  classical
  set Ω : Set (HypercubeTwoLocalParameter n → ℝ) :=
    {p | ∀ (i : Fin n) (z : qubitEnvironment n i), 0 < twoLocalEdgeGap i z p} with hΩ
  have hΩeq : Ω = ⋂ i : Fin n, ⋂ z : qubitEnvironment n i,
      {p : HypercubeTwoLocalParameter n → ℝ | 0 < twoLocalEdgeGap i z p} := by
    ext p
    simp [hΩ]
  have hΩopen : IsOpen Ω := by
    rw [hΩeq]
    refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun z => ?_
    exact isOpen_lt continuous_const (continuous_twoLocalEdgeGap i z)
  have hΩne : Ω.Nonempty := by
    refine ⟨negativeOnsiteParameters n, ?_⟩
    intro i z
    rw [twoLocalEdgeGap_negativeOnsite]
    norm_num
  obtain ⟨p, hpΩ, hpne⟩ :=
    exists_mem_open_forall_ne_zero hΩopen hΩne (twoLocalBaseFunctional (n := n))
      (Finset.univ : Finset (TwoLocalBaseCondition n))
      (fun r _ => by
        cases r with
        | inl q =>
            exact (continuous_hypercubeTwoLocalEnergy _).sub (continuous_hypercubeTwoLocalEnergy _)
        | inr q =>
            exact (continuous_twoLocalEdgeGap _ _).sub (continuous_twoLocalEdgeGap _ _))
      (fun r _ => by
        cases r with
        | inl q =>
            obtain ⟨⟨x, y⟩, hxy⟩ := q
            obtain ⟨i₀, hi₀⟩ : ∃ i, x i ≠ y i := by
              by_contra hcon
              push Not at hcon
              exact hxy (funext fun i => hcon i)
            refine ⟨HypercubeTwoLocalParameter.onsite i₀,
              (boolOccupation (x i₀) : ℝ) - (boolOccupation (y i₀) : ℝ), ?_, ?_⟩
            · cases hx : x i₀ <;> cases hy : y i₀ <;>
                simp [hx, hy, boolOccupation] at hi₀ ⊢
            · intro p δ
              exact energyDifference_shift_onsite x y i₀ p δ
        | inr q =>
            obtain ⟨i, ⟨⟨z, z'⟩, hzz'⟩⟩ := q
            obtain ⟨j, hj⟩ : ∃ j : {j : Fin n // j ≠ i}, z j ≠ z' j := by
              by_contra hcon
              push Not at hcon
              exact hzz' (funext fun j => hcon j)
            obtain ⟨j₀, hj₀⟩ := j
            refine ⟨HypercubeTwoLocalParameter.interaction i j₀,
              (-(boolOccupation (z ⟨j₀, hj₀⟩) : ℝ) / 2) - (-(boolOccupation (z' ⟨j₀, hj₀⟩) : ℝ) / 2),
              ?_, ?_⟩
            · cases hz : z ⟨j₀, hj₀⟩ <;> cases hz' : z' ⟨j₀, hj₀⟩ <;>
                simp [hz, hz', boolOccupation] at hj ⊢
            · intro p δ
              show twoLocalEdgeGap i z _ - twoLocalEdgeGap i z' _ = _
              rw [twoLocalEdgeGap_shift_interaction i z hj₀,
                twoLocalEdgeGap_shift_interaction i z' hj₀]
              show _ = (twoLocalEdgeGap i z p - twoLocalEdgeGap i z' p) + _
              ring)
  refine ⟨p, ?_, ?_, ?_⟩
  · intro x y hxy
    by_contra hne
    exact hpne (.inl ⟨(x, y), hne⟩) (Finset.mem_univ _) (by
      show hypercubeTwoLocalEnergy p x - hypercubeTwoLocalEnergy p y = 0
      rw [hxy, sub_self])
  · intro i z
    exact hpΩ i z
  · intro i z z' hzz'
    by_contra hne
    exact hpne (.inr ⟨i, ⟨(z, z'), hne⟩⟩) (Finset.mem_univ _) (by
      show twoLocalEdgeGap i z p - twoLocalEdgeGap i z' p = 0
      rw [twoLocalEdgeGap, twoLocalEdgeGap, hzz', sub_self])


/-- Moving the constant coefficient moves every energy equally. -/
theorem hypercubeTwoLocalEnergy_shift_constant (p : HypercubeTwoLocalParameter n → ℝ)
    (x : Fin n → Bool) (t : ℝ) :
    hypercubeTwoLocalEnergy
        (p + t • (Pi.single HypercubeTwoLocalParameter.constant (1 : ℝ))) x
      = hypercubeTwoLocalEnergy p x + t := by
  classical
  set Δ : HypercubeTwoLocalParameter n → ℝ :=
    t • (Pi.single HypercubeTwoLocalParameter.constant (1 : ℝ)) with hΔ
  have h0 : (p + Δ) HypercubeTwoLocalParameter.constant
      = p HypercubeTwoLocalParameter.constant + t := by
    simp [hΔ]
  have h1 : (∑ i, (p + Δ) (.onsite i) * (boolOccupation (x i) : ℝ))
      = ∑ i, p (.onsite i) * (boolOccupation (x i) : ℝ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : (p + Δ) (.onsite i) = p (.onsite i) := by simp [hΔ]
    rw [hi]
  have h2 : (∑ i, ∑ j, (p + Δ) (.interaction i j) * (boolOccupation (x i) : ℝ) *
        (boolOccupation (x j) : ℝ))
      = ∑ i, ∑ j, p (.interaction i j) * (boolOccupation (x i) : ℝ) *
          (boolOccupation (x j) : ℝ) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hij : (p + Δ) (.interaction i j) = p (.interaction i j) := by simp [hΔ]
    rw [hij]
  rw [hypercubeTwoLocalEnergy, hypercubeTwoLocalEnergy, h0, h1, h2]
  ring

/-- The coefficient direction shifting every edge gap of one qubit while fixing every edge mean. -/
def edgeShiftDirection (i : Fin n) : HypercubeTwoLocalParameter n → ℝ :=
  fun θ =>
    (Pi.single HypercubeTwoLocalParameter.constant (1 : ℝ) :
        HypercubeTwoLocalParameter n → ℝ) θ
      - 2 * (Pi.single (HypercubeTwoLocalParameter.onsite i) (1 : ℝ) :
          HypercubeTwoLocalParameter n → ℝ) θ

theorem hypercubeTwoLocalEnergy_shift_edgeDirection (p : HypercubeTwoLocalParameter n → ℝ)
    (x : Fin n → Bool) (i : Fin n) (t : ℝ) :
    hypercubeTwoLocalEnergy (p + t • edgeShiftDirection i) x
      = hypercubeTwoLocalEnergy p x + t * (1 - 2 * (boolOccupation (x i) : ℝ)) := by
  have hsplit : p + t • edgeShiftDirection i
      = (p + t • (Pi.single HypercubeTwoLocalParameter.constant (1 : ℝ)))
        + (-(2 * t)) • (Pi.single (HypercubeTwoLocalParameter.onsite i) (1 : ℝ)) := by
    funext θ
    simp only [edgeShiftDirection, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsplit, hypercubeTwoLocalEnergy_shift_onsite, hypercubeTwoLocalEnergy_shift_constant]
  ring

theorem edgeGap_shift_edgeDirection (p : HypercubeTwoLocalParameter n → ℝ) (i : Fin n)
    (z : qubitEnvironment n i) (t : ℝ) :
    edgeGap i (hypercubeTwoLocalEnergy (p + t • edgeShiftDirection i)) z
      = edgeGap i (hypercubeTwoLocalEnergy p) z + t := by
  simp only [edgeGap, hypercubeTwoLocalEnergy_shift_edgeDirection, edgeState_self]
  simp only [boolOccupation, if_true]
  push_cast
  ring

theorem edgeMean_shift_edgeDirection (p : HypercubeTwoLocalParameter n → ℝ) (i : Fin n)
    (z : qubitEnvironment n i) (t : ℝ) :
    edgeMean i (hypercubeTwoLocalEnergy (p + t • edgeShiftDirection i)) z
      = edgeMean i (hypercubeTwoLocalEnergy p) z := by
  simp only [edgeMean, hypercubeTwoLocalEnergy_shift_edgeDirection, edgeState_self]
  simp only [boolOccupation, if_true]
  push_cast
  ring

theorem edgeShiftDirection_transverse (i i' : Fin n) :
    edgeShiftDirection i (HypercubeTwoLocalParameter.transverse i') = 0 := by
  simp [edgeShiftDirection]


/-- Switching off every transverse coefficient. -/
def zeroTransverse (p : HypercubeTwoLocalParameter n → ℝ) : HypercubeTwoLocalParameter n → ℝ
  | .constant => p .constant
  | .onsite i => p (.onsite i)
  | .interaction i j => p (.interaction i j)
  | .transverse _ => 0

theorem zeroTransverse_transverse (p : HypercubeTwoLocalParameter n → ℝ) (i : Fin n) :
    zeroTransverse p (.transverse i) = 0 := rfl

theorem hypercubeTwoLocalEnergy_zeroTransverse (p : HypercubeTwoLocalParameter n → ℝ) :
    hypercubeTwoLocalEnergy (zeroTransverse p) = hypercubeTwoLocalEnergy p := by
  funext x
  simp only [hypercubeTwoLocalEnergy, zeroTransverse]

/-- **A two-local diagonal base.**  Switching off the transverse couplings leaves a purely diagonal
two-local Hamiltonian with pairwise distinct energies and, for every qubit, positive and pairwise
distinct edge gaps. -/
theorem exists_twoLocalDiagonalBase_zeroTransverse (n : ℕ) :
    ∃ p : HypercubeTwoLocalParameter n → ℝ,
      (∀ i : Fin n, p (.transverse i) = 0) ∧
      Function.Injective (hypercubeTwoLocalEnergy p) ∧
      (∀ (i : Fin n) (z : qubitEnvironment n i), 0 < edgeGap i (hypercubeTwoLocalEnergy p) z) ∧
      (∀ i : Fin n, Function.Injective (edgeGap i (hypercubeTwoLocalEnergy p))) := by
  obtain ⟨p, hinj, hpos, hgap⟩ := exists_twoLocalDiagonalBase n
  refine ⟨zeroTransverse p, zeroTransverse_transverse p, ?_, ?_, ?_⟩ <;>
    rw [hypercubeTwoLocalEnergy_zeroTransverse]
  · exact hinj
  · exact hpos
  · exact hgap

end GaloisForLFunctions.HTGeometry
