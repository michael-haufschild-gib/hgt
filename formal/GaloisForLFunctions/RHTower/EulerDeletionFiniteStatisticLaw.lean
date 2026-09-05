import GaloisForLFunctions.RHTower.EulerDeletionDirichletGram
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleCylinderClosure

/-!
# Full finite divisibility statistics of the literal Dirichlet source

For positive pairwise-coprime moduli and exponent alpha > 1, every real function
of their divisibility bits has exactly the expectation of independent Bernoulli
bits with parameters p^(-alpha), multiplied by the actual Dirichlet mass.
The theorem includes arbitrary nonlinear finite observables, all Boolean atoms,
and every nonempty product of the actual centered deletion coefficients.

The proof expands affine indicator products into finitely many multiples streams.
All exchanges have proved summability. This is the classical zeta-distribution
independence mechanism, not a new arithmetic obstruction or an RH proof.
Chronological dependence between different integer indices is outside this law.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.DeletionFiniteStatistics

/-- An arbitrary affine function of each of finitely many divisibility indicators. -/
def affineCoefficient (F : Finset ℕ) (u v : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ p ∈ F, ((if p ∣ n then v p else 0) + u p)

def subsetCoefficient (F S : Finset ℕ) (u v : ℕ → ℝ) : ℝ :=
  (∏ p ∈ S, v p) * ∏ p ∈ F \ S, u p

/-- All products expand into literal multiples streams, including the empty subset. -/
theorem affine_weight_expansion (F : Finset ℕ)
    (hpair : (F : Set ℕ).Pairwise Nat.Coprime) (u v : ℕ → ℝ) (α : ℝ) (n : ℕ) :
    affineCoefficient F u v n * deletionDirichletWeight α n =
      ∑ S ∈ F.powerset, subsetCoefficient F S u v *
        deletionDivisibilityWeight α (∏ p ∈ S, p) n := by
  classical
  rw [affineCoefficient, Finset.prod_add, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro S hS
  have hSF := Finset.mem_powerset.mp hS
  have hpairS : (S : Set ℕ).Pairwise Nat.Coprime :=
    fun p hp q hq hpq => hpair (hSF hp) (hSF hq) hpq
  have hd := finset_prod_dvd_iff_of_pairwise_coprime S hpairS n
  rw [Finset.prod_ite_zero]
  by_cases hn : (∏ p ∈ S, p) ∣ n
  · rw [if_pos (hd.mp hn), deletionDivisibilityWeight, if_pos hn]
    rfl
  · rw [if_neg (fun h => hn (hd.mpr h)), deletionDivisibilityWeight, if_neg hn]
    simp

theorem summable_affine_weight {α : ℝ} (hα : 1 < α)
    (F : Finset ℕ) (hpair : (F : Set ℕ).Pairwise Nat.Coprime) (u v : ℕ → ℝ) :
    Summable (fun n => affineCoefficient F u v n * deletionDirichletWeight α n) := by
  simp_rw [affine_weight_expansion F hpair]
  exact summable_sum (fun S _ =>
    (summable_deletionDivisibilityWeight hα _).mul_left (subsetCoefficient F S u v))

/-- Entire finite affine algebra factors with the actual Dirichlet probabilities. -/
theorem tsum_affine_weight {α : ℝ} (hα : 1 < α)
    (F : Finset ℕ) (hpos : ∀ p ∈ F, 0 < p)
    (hpair : (F : Set ℕ).Pairwise Nat.Coprime) (u v : ℕ → ℝ) :
    ∑' n, affineCoefficient F u v n * deletionDirichletWeight α n =
      deletionDirichletMass α * ∏ p ∈ F, (v p * (p : ℝ)^(-α) + u p) := by
  classical
  have hsum := fun S (_ : S ∈ F.powerset) =>
    (summable_deletionDivisibilityWeight hα (∏ p ∈ S, p)).mul_left
      (subsetCoefficient F S u v)
  simp_rw [affine_weight_expansion F hpair]
  rw [Summable.tsum_finsetSum hsum]
  simp only [tsum_mul_left]
  have he (S : Finset ℕ) (hS : S ∈ F.powerset) :
      subsetCoefficient F S u v * (∑' n, deletionDivisibilityWeight α (∏ p ∈ S, p) n) =
        deletionDirichletMass α *
          ((∏ p ∈ S, v p * (p : ℝ)^(-α)) * ∏ p ∈ F \ S, u p) := by
    have hSF := Finset.mem_powerset.mp hS
    have hpS : 0 < ∏ p ∈ S, p := Finset.prod_pos (fun p hp => hpos p (hSF hp))
    rw [tsum_deletionDivisibilityWeight α hpS]
    have hpow : ((∏ p ∈ S, p : ℕ) : ℝ)^(-α) = ∏ p ∈ S, (p : ℝ)^(-α) := by
      rw [Nat.cast_prod]
      exact (Real.finsetProd_rpow S (fun p : ℕ => (p : ℝ))
        (fun p _ => Nat.cast_nonneg p) (-α)).symm
    rw [hpow, Finset.prod_mul_distrib]
    dsimp [subsetCoefficient]
    ring
  rw [Finset.sum_congr rfl he, ← Finset.mul_sum, ← Finset.prod_add]

/-- The full finite Boolean record of literal divisibility at one integer. -/
abbrev State (F : Finset ℕ) := ↥F → Bool

def pattern (F : Finset ℕ) (n : ℕ) : State F :=
  fun p => if p.val ∣ n then true else false

def atom (F : Finset ℕ) (b : State F) (n : ℕ) : ℝ :=
  if pattern F n = b then 1 else 0

def atomConstant (F : Finset ℕ) (b : State F) (p : ℕ) : ℝ :=
  if hp : p ∈ F then (if b ⟨p,hp⟩ then 0 else 1) else 0

def atomSlope (F : Finset ℕ) (b : State F) (p : ℕ) : ℝ :=
  if hp : p ∈ F then (if b ⟨p,hp⟩ then 1 else -1) else 0

/-- Every Boolean atom belongs to the finite affine indicator algebra. -/
theorem atom_eq_affine (F : Finset ℕ) (b : State F) (n : ℕ) :
    atom F b n = affineCoefficient F (atomConstant F b) (atomSlope F b) n := by
  classical
  have hp : affineCoefficient F (atomConstant F b) (atomSlope F b) n =
      ∏ p : ↥F, (if pattern F n p = b p then (1 : ℝ) else 0) := by
    rw [affineCoefficient, ← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro p _
    by_cases hd : p.val ∣ n <;> cases hb : b p <;>
      simp [atomConstant, atomSlope, pattern, p.property, hd, hb]
  rw [hp, Fintype.prod_ite_zero]
  simp only [Finset.prod_const_one, ← funext_iff, atom]

/-- The exact mass assigned to one Boolean configuration by the product law. -/
def atomProbability (α : ℝ) (F : Finset ℕ) (b : State F) : ℝ :=
  ∏ p : ↥F, if b p then (p.val : ℝ)^(-α) else 1 - (p.val : ℝ)^(-α)

theorem summable_atom_weight {α : ℝ} (hα : 1 < α)
    (F : Finset ℕ) (b : State F) :
    Summable (fun n => atom F b n * deletionDirichletWeight α n) := by
  apply ((summable_deletionDirichletWeight hα).indicator {n | pattern F n = b}).congr
  intro n
  simp [atom, Set.indicator_apply, ite_mul]

/-- Full finite atom law, not just pairwise independence. -/
theorem tsum_atom_weight {α : ℝ} (hα : 1 < α)
    (F : Finset ℕ) (hpos : ∀ p ∈ F, 0 < p)
    (hpair : (F : Set ℕ).Pairwise Nat.Coprime) (b : State F) :
    ∑' n, atom F b n * deletionDirichletWeight α n =
      deletionDirichletMass α * atomProbability α F b := by
  simp_rw [atom_eq_affine]
  rw [tsum_affine_weight hα F hpos hpair, ← Finset.prod_coe_sort]
  congr 1
  dsimp only [atomProbability]
  apply Finset.prod_congr rfl
  intro p _
  cases hb : b p <;> simp [atomConstant, atomSlope, p.property, hb]
  all_goals ring

theorem finite_observable_partition (F : Finset ℕ) (Φ : State F → ℝ) (n : ℕ) :
    Φ (pattern F n) = ∑ b : State F, Φ b * atom F b n := by
  classical
  simp [atom, mul_ite]

theorem summable_finite_observable {α : ℝ} (hα : 1 < α)
    (F : Finset ℕ) (Φ : State F → ℝ) :
    Summable (fun n => Φ (pattern F n) * deletionDirichletWeight α n) := by
  have he (n : ℕ) : Φ (pattern F n) * deletionDirichletWeight α n =
      ∑ b : State F, Φ b * (atom F b n * deletionDirichletWeight α n) := by
    rw [finite_observable_partition F Φ n, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [he]
  exact summable_sum (fun b _ => (summable_atom_weight hα F b).mul_left (Φ b))

/-- Every real observable of finitely many divisibility bits has an explicit product-law value. -/
theorem tsum_finite_observable {α : ℝ} (hα : 1 < α)
    (F : Finset ℕ) (hpos : ∀ p ∈ F, 0 < p)
    (hpair : (F : Set ℕ).Pairwise Nat.Coprime) (Φ : State F → ℝ) :
    ∑' n, Φ (pattern F n) * deletionDirichletWeight α n =
      deletionDirichletMass α * ∑ b : State F, Φ b * atomProbability α F b := by
  have he (n : ℕ) : Φ (pattern F n) * deletionDirichletWeight α n =
      ∑ b : State F, Φ b * (atom F b n * deletionDirichletWeight α n) := by
    rw [finite_observable_partition F Φ n, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [he]
  rw [Summable.tsum_finsetSum (fun b _ => (summable_atom_weight hα F b).mul_left (Φ b))]
  simp only [tsum_mul_left, tsum_atom_weight hα F hpos hpair]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring


/-- All nonempty products of distinct coprime centered channels already vanish in every chamber. -/
theorem tsum_centered_product_zero {α : ℝ} (hα : 1 < α)
    (F : Finset ℕ) (hF : F.Nonempty) (hpos : ∀ p ∈ F, 0 < p)
    (hpair : (F : Set ℕ).Pairwise Nat.Coprime) :
    ∑' n, (∏ p ∈ F, deletionCenteredCoefficient α p n) * deletionDirichletWeight α n = 0 := by
  let u (p : ℕ) : ℝ := p * (p : ℝ)^(-α)
  let v (p : ℕ) : ℝ := -(p : ℝ)
  have he (n : ℕ) : (∏ p ∈ F, deletionCenteredCoefficient α p n) =
      affineCoefficient F u v n := by
    apply Finset.prod_congr rfl
    intro p _
    by_cases hp : p ∣ n
    all_goals simp [deletionCenteredCoefficient, blockDeletionCoefficient, hp, u, v]
    all_goals ring
  simp_rw [he]
  rw [tsum_affine_weight hα F hpos hpair]
  obtain ⟨p, hp⟩ := hF
  rw [Finset.prod_eq_zero hp (by dsimp [u,v]; ring), mul_zero]


end RHTower.DeletionFiniteStatistics
