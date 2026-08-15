import GaloisForLFunctions.HTGeometry.TorusPhaseTrigCalculus

/-!
# Exact replica moment of a spectral phase orbit

A spectral phase orbit with occupation weights `p` pairs with a replica tensor through the
occupation basis of the symmetric power: each multi-index contributes its multinomial normalization,
the product of the weights along the multi-index, and the torus character of that multi-index.

Distinct multi-indices are distinct torus characters, so Haar orthogonality makes the replica mean
square exactly the weighted sum of the squared coefficients.  Capping every occupation weight by a
single scale therefore bounds the replica moment by the replica factorial times that scale to the
replica order, uniformly over all replica tensors.
-/

open MeasureTheory Complex UnitAddTorus Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

set_option linter.unusedSectionVars false

variable {d : Type*} [Fintype d] [DecidableEq d]

section MultiIndexDegree

/-- The occupation multi-indices of a prescribed replica order. -/
def occupationSet (d : Type*) [Fintype d] [DecidableEq d] (r : ℕ) : Finset (d → ℕ) :=
  (Fintype.piFinset fun _ : d => Finset.range (r + 1)).filter fun α => ∑ j, α j = r

theorem sum_eq_of_mem_occupationSet {r : ℕ} {α : d → ℕ} (hα : α ∈ occupationSet d r) :
    ∑ j, α j = r := (Finset.mem_filter.mp hα).2

/-- The multinomial normalization of an occupation multi-index. -/
def occupationWeight (r : ℕ) (α : d → ℕ) : ℝ :=
  (r.factorial : ℝ) / (∏ j, ((α j).factorial : ℝ))

theorem occupationWeight_pos (r : ℕ) (α : d → ℕ) : 0 < occupationWeight r α := by
  rw [occupationWeight]
  refine div_pos (by positivity) (Finset.prod_pos fun j _ => ?_)
  exact_mod_cast (α j).factorial_pos

theorem occupationWeight_le_factorial (r : ℕ) (α : d → ℕ) :
    occupationWeight r α ≤ (r.factorial : ℝ) := by
  have hprodpos : (0 : ℝ) < ∏ j, ((α j).factorial : ℝ) :=
    Finset.prod_pos fun j _ => by exact_mod_cast (α j).factorial_pos
  have hone : (1 : ℝ) ≤ ∏ j, ((α j).factorial : ℝ) := by
    have hstep := Finset.prod_le_prod (s := (Finset.univ : Finset d)) (f := fun _ : d => (1 : ℝ))
      (g := fun j => ((α j).factorial : ℝ)) (fun j _ => zero_le_one)
      (fun j _ => by exact_mod_cast (α j).factorial_pos)
    simpa using hstep
  have hrpos : (0 : ℝ) ≤ (r.factorial : ℝ) := by positivity
  rw [occupationWeight, div_le_iff₀ hprodpos]
  nlinarith

/-- The product of the occupation weights along a multi-index is at most the cap to the replica
order. -/
theorem prod_pow_le_of_le {p : d → ℝ} (hp : ∀ j, 0 ≤ p j) {τ : ℝ}
    (hτ : ∀ j, p j ≤ τ) {r : ℕ} {α : d → ℕ} (hα : α ∈ occupationSet d r) :
    (∏ j, p j ^ α j) ≤ τ ^ r := by
  calc (∏ j, p j ^ α j) ≤ ∏ j, τ ^ α j :=
        Finset.prod_le_prod (fun j _ => pow_nonneg (hp j) _)
          (fun j _ => pow_le_pow_left₀ (hp j) (hτ j) _)
    _ = τ ^ (∑ j, α j) := by rw [Finset.prod_pow_eq_pow_sum]
    _ = τ ^ r := by rw [sum_eq_of_mem_occupationSet hα]

end MultiIndexDegree

section ReplicaPairing

/-- The occupation character of a multi-index. -/
def occupationFreq (α : d → ℕ) : d → ℤ := fun j => (α j : ℤ)

theorem occupationFreq_injective : Function.Injective (occupationFreq (d := d)) := by
  intro α β h
  funext j
  have h2 : ((α j : ℤ)) = ((β j : ℤ)) := congrFun h j
  exact_mod_cast h2

/-- The coefficient of a replica tensor in the occupation basis, weighted by the orbit. -/
def replicaCoeff (p : d → ℝ) (r : ℕ) (w : (d → ℕ) → ℂ) (α : d → ℕ) : ℂ :=
  ((Real.sqrt (occupationWeight r α) : ℝ) : ℂ) *
    ((∏ j, Real.sqrt (p j) ^ α j : ℝ) : ℂ) * (starRingEnd ℂ) (w α)

/-- The pairing of the replica power of a spectral phase orbit with a replica tensor. -/
def replicaPairing (p : d → ℝ) (r : ℕ) (w : (d → ℕ) → ℂ) (x : d → ℝ) : ℂ :=
  trigLift (occupationSet d r) occupationFreq (replicaCoeff p r w) x

theorem normSq_replicaCoeff {p : d → ℝ} (hp : ∀ j, 0 ≤ p j) (r : ℕ) (w : (d → ℕ) → ℂ)
    (α : d → ℕ) :
    ‖replicaCoeff p r w α‖ ^ 2 = occupationWeight r α * (∏ j, p j ^ α j) * ‖w α‖ ^ 2 := by
  have hprod : (∏ j, Real.sqrt (p j) ^ α j) ^ 2 = ∏ j, p j ^ α j := by
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← pow_mul, mul_comm (α j) 2, pow_mul, Real.sq_sqrt (hp j)]
  rw [replicaCoeff, norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (Finset.prod_nonneg fun j _ => pow_nonneg (Real.sqrt_nonneg _) _)]
  rw [mul_pow, mul_pow, Real.sq_sqrt (occupationWeight_pos r α).le, hprod]

/-- **Exact replica moment.**  Haar orthogonality of distinct occupation characters makes the
replica mean square the weighted sum of the squared coefficients. -/
theorem integral_box_normSq_replicaPairing {p : d → ℝ} (hp : ∀ j, 0 ≤ p j) (r : ℕ)
    (w : (d → ℕ) → ℂ) :
    (∫ x in torusBox d, ‖replicaPairing p r w x‖ ^ 2) =
      ∑ α ∈ occupationSet d r, occupationWeight r α * (∏ j, p j ^ α j) * ‖w α‖ ^ 2 := by
  have hkey : (∫ x in torusBox d, ‖replicaPairing p r w x‖ ^ 2) =
      ∑ α ∈ occupationSet d r, ‖replicaCoeff p r w α‖ ^ 2 :=
    integral_box_normSq_trigLift_of_injOn (occupationSet d r) occupationFreq
      (replicaCoeff p r w) (fun α _ β _ h => occupationFreq_injective h)
  rw [hkey]
  exact Finset.sum_congr rfl fun α _ => normSq_replicaCoeff hp r w α

/-- **Replica moment bound.**  Capping every occupation weight bounds the replica mean square by
the replica factorial times the cap to the replica order. -/
theorem integral_box_normSq_replicaPairing_le {p : d → ℝ} (hp : ∀ j, 0 ≤ p j) {τ : ℝ}
    (hτ : ∀ j, p j ≤ τ) (r : ℕ) (w : (d → ℕ) → ℂ) :
    (∫ x in torusBox d, ‖replicaPairing p r w x‖ ^ 2) ≤
      (r.factorial : ℝ) * τ ^ r * ∑ α ∈ occupationSet d r, ‖w α‖ ^ 2 := by
  rw [integral_box_normSq_replicaPairing hp r w, Finset.mul_sum]
  refine Finset.sum_le_sum fun α hα => ?_
  have hprod : (0 : ℝ) ≤ ∏ j, p j ^ α j :=
    Finset.prod_nonneg fun j _ => pow_nonneg (hp j) _
  calc occupationWeight r α * (∏ j, p j ^ α j) * ‖w α‖ ^ 2
      ≤ (r.factorial : ℝ) * (∏ j, p j ^ α j) * ‖w α‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hprod) (sq_nonneg _)
        exact occupationWeight_le_factorial r α
    _ ≤ (r.factorial : ℝ) * τ ^ r * ‖w α‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left (prod_pow_le_of_le hp hτ hα) (by positivity)

end ReplicaPairing

section HeavySector

variable {p : d → ℝ}

/-- The occupation collision of a spectral orbit. -/
def occupationCollision (p : d → ℝ) : ℝ := ∑ j, p j ^ 2

/-- The heavy spectral sector above a cap. -/
def heavySector (p : d → ℝ) (τ : ℝ) : Finset d := Finset.univ.filter fun j => τ < p j

/-- The light truncation of the occupation weights. -/
def lightWeights (p : d → ℝ) (τ : ℝ) : d → ℝ := fun j => if τ < p j then 0 else p j

theorem lightWeights_nonneg (hp : ∀ j, 0 ≤ p j) (τ : ℝ) (j : d) : 0 ≤ lightWeights p τ j := by
  rw [lightWeights]
  split <;> [exact le_rfl; exact hp j]

theorem lightWeights_le (τ : ℝ) (hτ : 0 ≤ τ) (j : d) : lightWeights p τ j ≤ τ := by
  rw [lightWeights]
  split
  · exact hτ
  · exact not_lt.mp ‹¬ τ < p j›

/-- **Heavy sector mass.**  Above a cap the total occupation mass is at most the collision over the
cap. -/
theorem sum_heavySector_le (hp : ∀ j, 0 ≤ p j) {τ : ℝ} (hτ : 0 < τ) :
    ∑ j ∈ heavySector p τ, p j ≤ occupationCollision p / τ := by
  rw [le_div_iff₀ hτ, occupationCollision]
  calc (∑ j ∈ heavySector p τ, p j) * τ = ∑ j ∈ heavySector p τ, p j * τ := by
        rw [Finset.sum_mul]
    _ ≤ ∑ j ∈ heavySector p τ, p j ^ 2 := by
        refine Finset.sum_le_sum fun j hj => ?_
        simp only [heavySector, Finset.mem_filter] at hj
        have h1 : 0 ≤ p j := hp j
        have h2 : τ < p j := hj.2
        nlinarith
    _ ≤ ∑ j, p j ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j _ _ => sq_nonneg _)

end HeavySector

end GaloisForLFunctions.HTGeometry
