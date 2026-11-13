import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBoundStatesOfAWindowAreTheSlowModesOfItsDoobChain
import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBindingEnergyOfAWindowIsCarriedByItsFloorTrees

/-!
# The floor trees alone do not connect a window of ratio four

On the window `(6r, 24r]` of ratio four, at block size `6r`, only the floor maps of `2` and `3`
join two blocks: a contact `⌊b/k⌋ = a` needs `k ≤ b/a < 4`. For `8r ≤ c < 9r` the three blocks
`c, 2c, 2c + 1` — a parent and its two children under the tree of `2` — form a **component** of
the floor trees (`floorContact_eq_zero_of_component`): the parent of `c` under `2` and `3` lies
below the window, its children under `3` lie above it, and the children `2c, 2c + 1` have no
children in the window and their parent under `3` lies below it.

So the floor trees alone have at least `r` components of three blocks (`floorTreeComponent`), and
the **dilation process** of the window — its Doob chain without the jets — has no spectral gap:
on the indicator of a component its Dirichlet form vanishes. With the jets the Doob energy of
such an indicator is the energy of the jets alone (`doobEnergy_component_eq_prime_free`), for
every positive weight vector. Hence any proof that a window of ratio four holds one bound state
must bind these `r` components, a number proportional to the block size, through the jets alone
(`poincare_component_of_le_one`).
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-- The blocks `c, 2c, 2c + 1`, as positions in the window `(6r, 24r]`. -/
def floorTreeComponent (r c : ℕ) (j : ℕ) : Prop :=
  6 * r + j = c ∨ 6 * r + j = 2 * c ∨ 6 * r + j = 2 * c + 1

instance (r c j : ℕ) : Decidable (floorTreeComponent r c j) := by
  unfold floorTreeComponent
  infer_instance

/-- A floor map between two blocks of `(6r, 24r]` is that of `2` or `3`. -/
theorem le_three_of_floor {r k x y : ℕ} (hx : 6 * r ≤ x) (hy : y < 24 * r) (hxy : y / k = x) :
    k ≤ 3 := by
  have h1 : y / k * k ≤ y := Nat.div_mul_le_self y k
  rw [hxy] at h1
  by_contra h
  push Not at h
  have : 6 * r * 4 ≤ x * k := Nat.mul_le_mul hx h
  omega

/-- **The blocks `c, 2c, 2c + 1` are a component of the floor trees of `(6r, 24r]`.** No floor
map joins a block of the component to a block of the window outside it. -/
theorem floorContact_eq_zero_of_component {Q r c a b : ℕ} (hc₁ : 8 * r ≤ c) (hc₂ : c < 9 * r)
    (ha : 6 * r ≤ a) (hb : 6 * r ≤ b) (ha' : a < 24 * r) (hb' : b < 24 * r)
    (hone : ((a = c ∨ a = 2 * c ∨ a = 2 * c + 1) ∧ ¬ (b = c ∨ b = 2 * c ∨ b = 2 * c + 1)) ∨
      (¬ (a = c ∨ a = 2 * c ∨ a = 2 * c + 1) ∧ (b = c ∨ b = 2 * c ∨ b = 2 * c + 1))) :
    floorContact Q (min a b) (max a b) = 0 := by
  refine Finset.sum_eq_zero fun k hk => if_neg fun h => ?_
  have hk2 := (Finset.mem_Icc.mp hk).1
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab] at h
    have hk3 := le_three_of_floor ha hb' h
    interval_cases k <;> omega
  · rw [min_eq_right hab, max_eq_left hab] at h
    have hk3 := le_three_of_floor hb ha' h
    interval_cases k <;> omega

/-- The neutral part of the window `(6r, 24r]` at two blocks. -/
theorem neutralWindow_ratio_four_apply (Q r : ℕ) (i j : Fin (18 * r)) :
    neutralWindow Q (6 * r) (18 * r) i j = neutralBlock Q (6 * r + i) (6 * r + j) := rfl

/-- The indicator of a component of the floor trees. -/
def componentIndicator (r c : ℕ) (j : Fin (18 * r)) : ℝ :=
  if floorTreeComponent r c j then 1 else 0

/-- **On the indicator of a component the Doob energy is that of the jets alone**, for every
weight vector. -/
theorem doobEnergy_component_eq_prime_free {Q r c : ℕ} (hc₁ : 8 * r ≤ c) (hc₂ : c < 9 * r)
    (φ : Fin (18 * r) → ℝ) (t : ℝ) :
    doobEnergy (neutralWindow Q (6 * r) (18 * r)) φ (fun j => componentIndicator r c j - t) =
      doobEnergy (neutralWindow 1 (6 * r) (18 * r)) φ (fun j => componentIndicator r c j - t) := by
  unfold doobEnergy
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold doobConductance
  rw [neutralWindow_ratio_four_apply, neutralWindow_ratio_four_apply]
  have hi' := i.isLt
  have hj' := j.isLt
  have key : floorContact Q (min (6 * r + (i : ℕ)) (6 * r + j)) (max (6 * r + (i : ℕ)) (6 * r + j)) *
      ((componentIndicator r c i - t) - (componentIndicator r c j - t)) ^ 2 = 0 := by
    unfold componentIndicator
    by_cases hi : floorTreeComponent r c i <;> by_cases hj : floorTreeComponent r c j
    · simp [hi, hj]
    · rw [floorContact_eq_zero_of_component hc₁ hc₂ (by omega) (by omega) (by omega) (by omega)
        (Or.inl ⟨hi, hj⟩), zero_mul]
    · rw [floorContact_eq_zero_of_component hc₁ hc₂ (by omega) (by omega) (by omega) (by omega)
        (Or.inr ⟨hi, hj⟩), zero_mul]
    · simp [hi, hj]
  calc -neutralBlock Q (6 * r + (i : ℕ)) (6 * r + j) * φ i * φ j *
        ((componentIndicator r c i - t) - (componentIndicator r c j - t)) ^ 2 =
      -(neutralBlock 1 (6 * r + (i : ℕ)) (6 * r + j) -
          floorContact Q (min (6 * r + (i : ℕ)) (6 * r + j)) (max (6 * r + (i : ℕ)) (6 * r + j))) *
        φ i * φ j * ((componentIndicator r c i - t) - (componentIndicator r c j - t)) ^ 2 := by
        rw [neutralBlock_eq_one_sub]
    _ = -neutralBlock 1 (6 * r + (i : ℕ)) (6 * r + j) * φ i * φ j *
          ((componentIndicator r c i - t) - (componentIndicator r c j - t)) ^ 2 +
        φ i * φ j * (floorContact Q (min (6 * r + (i : ℕ)) (6 * r + j))
          (max (6 * r + (i : ℕ)) (6 * r + j)) *
          ((componentIndicator r c i - t) - (componentIndicator r c j - t)) ^ 2) := by ring
    _ = -neutralBlock 1 (6 * r + (i : ℕ)) (6 * r + j) * φ i * φ j *
          ((componentIndicator r c i - t) - (componentIndicator r c j - t)) ^ 2 := by
        rw [key, mul_zero, add_zero]

/-- **One bound state at ratio four forces the jets to bind every component.** If the window
`(6r, 24r]` holds at most one bound state, then for its positive ground vector `φ` with
eigenvalue `λ`, every centred indicator of a component satisfies the Poincaré inequality with
constant `−λ` for the Doob chain of the jets alone. -/
theorem poincare_component_of_le_one {Q r c : ℕ} (hc₁ : 8 * r ≤ c) (hc₂ : c < 9 * r)
    {φ : Fin (18 * r) → ℝ} (hφ : ∀ i, 0 < φ i) {lam : ℝ}
    (heig : neutralWindow Q (6 * r) (18 * r) *ᵥ φ = lam • φ)
    (hone : hermNegIndex ((neutralWindow Q (6 * r) (18 * r)).map (↑) :
      Matrix (Fin (18 * r)) (Fin (18 * r)) ℂ) ≤ 1) (t : ℝ)
    (ht : doobMean φ (fun j => componentIndicator r c j - t) = 0) :
    -lam * doobMass φ (fun j => componentIndicator r c j - t) ≤
      doobEnergy (neutralWindow 1 (6 * r) (18 * r)) φ (fun j => componentIndicator r c j - t) := by
  rw [← doobEnergy_component_eq_prime_free (Q := Q) hc₁ hc₂ φ t]
  exact (hermNegIndex_le_one_iff_poincare (neutralWindow_symm Q (6 * r) (18 * r))
    (fun _ _ hij => (neutralWindow_neg_of_ne Q (6 * r) hij).le) hφ heig).mp hone _ ht

/-- The components are disjoint for different parents, so there are at least `r` of them. -/
theorem floorTreeComponent_disjoint {r c c' j : ℕ} (hc₁ : 8 * r ≤ c) (hc₂ : c < 9 * r)
    (hc₁' : 8 * r ≤ c') (hc₂' : c' < 9 * r) (hcc : c ≠ c')
    (h : floorTreeComponent r c j) : ¬ floorTreeComponent r c' j := by
  unfold floorTreeComponent at *
  omega

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
