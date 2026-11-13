import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBoundStatesOfAWindowAreTheSlowModesOfItsDoobChain
import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBindingEnergyOfAWindowIsCarriedByItsFloorTrees

/-!
# The floor trees alone do not connect a window of ratio below nine halves

On the window `(R, R + J]` at block size `R` a contact `⌊b/k⌋ = a` joins a parent `a` to a child
`b ∈ [ka, ka + k)`. Take a block `c` with `R ≤ c`, `R + J ≤ 3c` and `2c + 1 < 3R`. Then the three
blocks `c, 2c, 2c + 1` form a **component** of the floor trees
(`floorContact_eq_zero_of_component`):

* `c < 2R` has no parent in the window, and its children under `k ≥ 3` lie at `3c ≥ R + J`;
* `2c, 2c + 1` have the parent `c` under `2`, their parents under `k ≥ 3` lie below `R` because
  `2c + 1 < 3R`, and their children lie at `4c > R + J`.

Such `c` exist iff `(R + J)/3 < 3R/2`, i.e. for every ratio `ρ < 9/2`, and then there are about
`(7R − 2J)/6` of them, a number proportional to the block size (`floorTreeComponent_disjoint`). At
ratio four, `(6r, 24r]`, they are the `r` blocks `8r ≤ c < 9r`. From ratio `9/2` on every
`c < 3R/2` has a child `3c` in the window and these components disappear.

So for every ratio below `9/2` the **dilation process** — the Doob chain without the jets — has
no spectral gap: on the indicator of a component its Dirichlet form vanishes, and with the jets
the Doob energy of such an indicator is the energy of the jets alone
(`doobEnergy_component_eq_prime_free`), for every positive weight vector. Hence a window of ratio
below `9/2` with one bound state binds each of these components through the jets alone
(`poincare_component_of_le_one`).
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-- The blocks `c, 2c, 2c + 1`, as positions in the window `(R, R + J]`. -/
def floorTreeComponent (R c : ℕ) (j : ℕ) : Prop :=
  R + j = c ∨ R + j = 2 * c ∨ R + j = 2 * c + 1

instance (R c j : ℕ) : Decidable (floorTreeComponent R c j) := by
  unfold floorTreeComponent
  infer_instance

/-- **The blocks `c, 2c, 2c + 1` are a component of the floor trees of `(R, R + J]`** when
`R ≤ c`, `R + J ≤ 3c` and `2c + 1 < 3R`: no floor map joins a block of the component to a block of
the window outside it. -/
theorem floorContact_eq_zero_of_component {Q R J c a b : ℕ} (hc₀ : R ≤ c) (hc₁ : R + J ≤ 3 * c)
    (hc₂ : 2 * c + 1 < 3 * R) (ha : R ≤ a) (hb : R ≤ b) (ha' : a < R + J) (hb' : b < R + J)
    (hone : ((a = c ∨ a = 2 * c ∨ a = 2 * c + 1) ∧ ¬ (b = c ∨ b = 2 * c ∨ b = 2 * c + 1)) ∨
      (¬ (a = c ∨ a = 2 * c ∨ a = 2 * c + 1) ∧ (b = c ∨ b = 2 * c ∨ b = 2 * c + 1))) :
    floorContact Q (min a b) (max a b) = 0 := by
  refine Finset.sum_eq_zero fun k hk => if_neg fun h => ?_
  have hk2 := (Finset.mem_Icc.mp hk).1
  -- a contact `⌊y/k⌋ = x` gives `kx ≤ y < kx + k`
  have hdiv : ∀ x y : ℕ, y / k = x → k * x ≤ y ∧ y < k * x + k := fun x y hxy => by
    have h1 : y / k * k ≤ y := Nat.div_mul_le_self y k
    have h2 : y < (y / k + 1) * k := by
      have := Nat.lt_div_mul_add (show 0 < k by omega) (a := y)
      linarith
    rw [hxy] at h1 h2
    constructor <;> nlinarith
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right hab] at h
    obtain ⟨h1, h2⟩ := hdiv a b h
    rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
    · omega
    · have : 3 * a ≤ k * a := Nat.mul_le_mul_right a hk3
      omega
  · rw [min_eq_right hab, max_eq_left hab] at h
    obtain ⟨h1, h2⟩ := hdiv b a h
    rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | hk3
    · omega
    · have : 3 * b ≤ k * b := Nat.mul_le_mul_right b hk3
      omega

/-- The indicator of a component of the floor trees. -/
def componentIndicator (R J c : ℕ) (j : Fin J) : ℝ :=
  if floorTreeComponent R c j then 1 else 0

/-- **On the indicator of a component the Doob energy is that of the jets alone**, for every
weight vector. -/
theorem doobEnergy_component_eq_prime_free {Q R J c : ℕ} (hc₀ : R ≤ c) (hc₁ : R + J ≤ 3 * c)
    (hc₂ : 2 * c + 1 < 3 * R) (φ : Fin J → ℝ) (t : ℝ) :
    doobEnergy (neutralWindow Q R J) φ (fun j => componentIndicator R J c j - t) =
      doobEnergy (neutralWindow 1 R J) φ (fun j => componentIndicator R J c j - t) := by
  unfold doobEnergy
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  unfold doobConductance
  show -neutralBlock Q (R + (i : ℕ)) (R + j) * φ i * φ j *
      ((componentIndicator R J c i - t) - (componentIndicator R J c j - t)) ^ 2 =
    -neutralBlock 1 (R + (i : ℕ)) (R + j) * φ i * φ j *
      ((componentIndicator R J c i - t) - (componentIndicator R J c j - t)) ^ 2
  have hi' := i.isLt
  have hj' := j.isLt
  have key : floorContact Q (min (R + (i : ℕ)) (R + j)) (max (R + (i : ℕ)) (R + j)) *
      ((componentIndicator R J c i - t) - (componentIndicator R J c j - t)) ^ 2 = 0 := by
    unfold componentIndicator
    by_cases hi : floorTreeComponent R c i <;> by_cases hj : floorTreeComponent R c j
    · simp [hi, hj]
    · rw [floorContact_eq_zero_of_component hc₀ hc₁ hc₂ (by omega) (by omega) (by omega)
        (by omega) (Or.inl ⟨hi, hj⟩), zero_mul]
    · rw [floorContact_eq_zero_of_component hc₀ hc₁ hc₂ (by omega) (by omega) (by omega)
        (by omega) (Or.inr ⟨hi, hj⟩), zero_mul]
    · simp [hi, hj]
  rw [neutralBlock_eq_one_sub Q (R + (i : ℕ)) (R + j)]
  linear_combination φ i * φ j * key

/-- **One bound state below ratio `9/2` forces the jets to bind every component.** If the window
holds at most one bound state, then for its positive ground vector `φ` with eigenvalue `λ`, every
centred indicator of a component satisfies the Poincaré inequality with constant `−λ` for the
Doob chain of the jets alone. -/
theorem poincare_component_of_le_one {Q R J c : ℕ} (hc₀ : R ≤ c) (hc₁ : R + J ≤ 3 * c)
    (hc₂ : 2 * c + 1 < 3 * R) {φ : Fin J → ℝ} (hφ : ∀ i, 0 < φ i) {lam : ℝ}
    (heig : neutralWindow Q R J *ᵥ φ = lam • φ)
    (hone : hermNegIndex ((neutralWindow Q R J).map (↑) : Matrix (Fin J) (Fin J) ℂ) ≤ 1) (t : ℝ)
    (ht : doobMean φ (fun j => componentIndicator R J c j - t) = 0) :
    -lam * doobMass φ (fun j => componentIndicator R J c j - t) ≤
      doobEnergy (neutralWindow 1 R J) φ (fun j => componentIndicator R J c j - t) := by
  rw [← doobEnergy_component_eq_prime_free (Q := Q) hc₀ hc₁ hc₂ φ t]
  exact (hermNegIndex_le_one_iff_poincare (neutralWindow_symm Q R J)
    (fun _ _ hij => (neutralWindow_neg_of_ne Q R hij).le) hφ heig).mp hone _ ht

/-- Components with different parents are disjoint. -/
theorem floorTreeComponent_disjoint {R c c' j : ℕ} (hc₀ : R ≤ c) (hc₂ : 2 * c + 1 < 3 * R)
    (hc₀' : R ≤ c') (hc₂' : 2 * c' + 1 < 3 * R) (hcc : c ≠ c')
    (h : floorTreeComponent R c j) : ¬ floorTreeComponent R c' j := by
  unfold floorTreeComponent at *
  omega

/-- At ratio four the components are those of the parents `8r ≤ c < 9r` of `(6r, 24r]`. -/
theorem component_ratio_four {r c : ℕ} (hc₁ : 8 * r ≤ c) (hc₂ : c < 9 * r) :
    6 * r ≤ c ∧ 6 * r + 18 * r ≤ 3 * c ∧ 2 * c + 1 < 3 * (6 * r) := by
  omega

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
