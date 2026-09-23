import GaloisForLFunctions.HTGeometry.TorusPhaseTrigCalculus
import GaloisForLFunctions.HTGeometry.ReplicaHilbertCoareaIncidenceLaw

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

local instance torusReplicaMomentBoundMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance torusReplicaMomentBoundIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance torusReplicaMomentBoundIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
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
    ‖replicaCoeff p r w α‖ ^ (2 : ℕ) = occupationWeight r α * (∏ j, p j ^ α j) * ‖w α‖ ^ (2 : ℕ) := by
  have hprod : (∏ j, Real.sqrt (p j) ^ α j) ^ (2 : ℕ) = ∏ j, p j ^ α j := by
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
    (∫ x in torusBox d, ‖replicaPairing p r w x‖ ^ (2 : ℕ)) =
      ∑ α ∈ occupationSet d r, occupationWeight r α * (∏ j, p j ^ α j) * ‖w α‖ ^ (2 : ℕ) := by
  have hkey : (∫ x in torusBox d, ‖replicaPairing p r w x‖ ^ (2 : ℕ)) =
      ∑ α ∈ occupationSet d r, ‖replicaCoeff p r w α‖ ^ (2 : ℕ) :=
    integral_box_normSq_trigLift_of_injOn (occupationSet d r) occupationFreq
      (replicaCoeff p r w) (fun α _ β _ h => occupationFreq_injective h)
  rw [hkey]
  exact Finset.sum_congr rfl fun α _ => normSq_replicaCoeff hp r w α

/-- **Replica moment bound.**  Capping every occupation weight bounds the replica mean square by
the replica factorial times the cap to the replica order. -/
theorem integral_box_normSq_replicaPairing_le {p : d → ℝ} (hp : ∀ j, 0 ≤ p j) {τ : ℝ}
    (hτ : ∀ j, p j ≤ τ) (r : ℕ) (w : (d → ℕ) → ℂ) :
    (∫ x in torusBox d, ‖replicaPairing p r w x‖ ^ (2 : ℕ)) ≤
      (r.factorial : ℝ) * τ ^ r * ∑ α ∈ occupationSet d r, ‖w α‖ ^ (2 : ℕ) := by
  rw [integral_box_normSq_replicaPairing hp r w, Finset.mul_sum]
  refine Finset.sum_le_sum fun α hα => ?_
  have hprod : (0 : ℝ) ≤ ∏ j, p j ^ α j :=
    Finset.prod_nonneg fun j _ => pow_nonneg (hp j) _
  calc occupationWeight r α * (∏ j, p j ^ α j) * ‖w α‖ ^ (2 : ℕ)
      ≤ (r.factorial : ℝ) * (∏ j, p j ^ α j) * ‖w α‖ ^ (2 : ℕ) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hprod) (sq_nonneg _)
        exact occupationWeight_le_factorial r α
    _ ≤ (r.factorial : ℝ) * τ ^ r * ‖w α‖ ^ (2 : ℕ) := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact mul_le_mul_of_nonneg_left (prod_pow_le_of_le hp hτ hα) (by positivity)

end ReplicaPairing

section HeavySector

variable {p : d → ℝ}

/-- The occupation collision of a spectral orbit. -/
def occupationCollision (p : d → ℝ) : ℝ := ∑ j, p j ^ (2 : ℕ)

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
    _ ≤ ∑ j ∈ heavySector p τ, p j ^ (2 : ℕ) := by
        refine Finset.sum_le_sum fun j hj => ?_
        simp only [heavySector, Finset.mem_filter] at hj
        have h1 : 0 ≤ p j := hp j
        have h2 : τ < p j := hj.2
        nlinarith
    _ ≤ ∑ j, p j ^ (2 : ℕ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun j _ _ => sq_nonneg _)

end HeavySector

section FidelityMoment

/-- The spectral phase orbit of an occupation profile. -/
def torusReplicaPhaseOrbit (p : d → ℝ) (x : d → ℝ) : d → ℂ :=
  fun j => (Real.sqrt (p j) : ℂ) * charLift (Pi.single j 1) x

theorem occupationSet_eq_piAntidiag (r : ℕ) :
    occupationSet d r = Finset.piAntidiag Finset.univ r := by
  ext α
  simp only [occupationSet, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range,
    Finset.mem_piAntidiag]
  constructor
  · rintro ⟨-, hsum⟩
    exact ⟨hsum, fun i _ => Finset.mem_univ i⟩
  · rintro ⟨hsum, -⟩
    refine ⟨fun j => ?_, hsum⟩
    have hsum' : ∑ i, α i = r := hsum
    have hle : α j ≤ ∑ i, α i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (α i)) (Finset.mem_univ j)
    omega

theorem multinomial_le_factorial_of_mem {r : ℕ} {α : d → ℕ} (hα : α ∈ occupationSet d r) :
    Nat.multinomial Finset.univ α ≤ r.factorial := by
  have hspec := Nat.multinomial_spec (Finset.univ : Finset d) α
  rw [sum_eq_of_mem_occupationSet hα] at hspec
  have hone : 1 ≤ ∏ i : d, (α i).factorial :=
    Finset.one_le_prod' fun i _ => (α i).factorial_pos
  nlinarith [Nat.multinomial_pos (Finset.univ : Finset d) α]

/-- The inner product of a spectral phase orbit with a target is a character combination. -/
theorem finiteComplexInner_torusReplicaPhaseOrbit (p : d → ℝ) (x : d → ℝ) (z : d → ℂ) :
    finiteComplexInner (torusReplicaPhaseOrbit p x) z =
      ∑ j, ((Real.sqrt (p j) : ℂ) * z j) * charLift (-(Pi.single j 1)) x := by
  rw [finiteComplexInner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [torusReplicaPhaseOrbit, map_mul, Complex.conj_ofReal, ← charLift_neg_index]
  ring

/-- The replica power of that inner product is a character combination over occupation
multi-indices. -/
theorem inner_torusReplicaPhaseOrbit_pow (p : d → ℝ) (x : d → ℝ) (z : d → ℂ) (r : ℕ) :
    (finiteComplexInner (torusReplicaPhaseOrbit p x) z) ^ r =
      trigLift (occupationSet d r) (fun α => -(occupationFreq α))
        (fun α => (Nat.multinomial Finset.univ α : ℂ) *
          ∏ j, ((Real.sqrt (p j) : ℂ) * z j) ^ α j) x := by
  classical
  rw [finiteComplexInner_torusReplicaPhaseOrbit p x z,
    Finset.sum_pow_eq_sum_piAntidiag Finset.univ
      (fun j => ((Real.sqrt (p j) : ℂ) * z j) * charLift (-(Pi.single j 1)) x) r,
    ← occupationSet_eq_piAntidiag, trigLift]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hsplit : (∏ j, (((Real.sqrt (p j) : ℂ) * z j) * charLift (-(Pi.single j 1)) x) ^ α j) =
      (∏ j, ((Real.sqrt (p j) : ℂ) * z j) ^ α j) *
        ∏ j, (charLift (-(Pi.single j 1)) x) ^ α j := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => by rw [mul_pow]
  have hchar : (∏ j, (charLift (-(Pi.single j 1)) x) ^ α j) =
      charLift (-(occupationFreq α)) x := by
    have hstep : ∀ j : d, (charLift (-(Pi.single j 1)) x) ^ α j =
        charLift (((α j : ℤ)) • (-(Pi.single j (1 : ℤ)))) x := fun j =>
      charLift_pow _ x (α j)
    rw [Finset.prod_congr rfl fun j _ => hstep j, charLift_prod_index]
    congr 1
    funext k
    simp only [occupationFreq, Finset.sum_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    rw [Finset.sum_eq_single k]
    · rw [Pi.single_eq_same]
      ring
    · intro j _ hjk
      rw [Pi.single_eq_of_ne (Ne.symm hjk)]
      ring
    · intro hcon
      exact absurd (Finset.mem_univ k) hcon
  rw [hsplit, hchar]
  ring

/-- **Replica fidelity moment.**  Capping every occupation weight bounds the replica fidelity
moment of the spectral phase orbit by the replica factorial times the cap to the replica order. -/
theorem integral_box_fidelity_pow_le {p : d → ℝ} (hp : ∀ j, 0 ≤ p j) {τ : ℝ}
    (hτ : ∀ j, p j ≤ τ) (hτ0 : 0 ≤ τ) {z : d → ℂ} (hz : ∑ j, ‖z j‖ ^ (2 : ℕ) ≤ 1) (r : ℕ) :
    (∫ x in torusBox d, finitePureStateFidelity (torusReplicaPhaseOrbit p x) z ^ r) ≤
      (r.factorial : ℝ) * τ ^ r := by
  classical
  have hpt : ∀ x : d → ℝ, finitePureStateFidelity (torusReplicaPhaseOrbit p x) z ^ r =
      ‖(finiteComplexInner (torusReplicaPhaseOrbit p x) z) ^ r‖ ^ (2 : ℕ) := by
    intro x
    rw [finitePureStateFidelity, norm_pow, ← pow_mul, ← pow_mul, mul_comm 2 r]
  simp_rw [hpt, inner_torusReplicaPhaseOrbit_pow p _ z r]
  rw [integral_box_normSq_trigLift_of_injOn _ _ _ (fun α _ β _ h => by
    have : occupationFreq α = occupationFreq β := by
      have := congrArg (fun n : d → ℤ => -n) h
      simpa using this
    exact occupationFreq_injective this)]
  have hcoeff : ∀ α ∈ occupationSet d r,
      ‖(Nat.multinomial Finset.univ α : ℂ) * ∏ j, ((Real.sqrt (p j) : ℂ) * z j) ^ α j‖ ^ (2 : ℕ) ≤
        (r.factorial : ℝ) * τ ^ r *
          ((Nat.multinomial Finset.univ α : ℝ) * ∏ j, ‖z j‖ ^ (2 * α j)) := by
    intro α hα
    have hnorm : ‖(Nat.multinomial Finset.univ α : ℂ) *
        ∏ j, ((Real.sqrt (p j) : ℂ) * z j) ^ α j‖ ^ (2 : ℕ) =
        (Nat.multinomial Finset.univ α : ℝ) ^ (2 : ℕ) * ∏ j, (p j * ‖z j‖ ^ (2 : ℕ)) ^ α j := by
      rw [norm_mul, mul_pow, Complex.norm_natCast, norm_prod, ← Finset.prod_pow]
      congr 1
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
        ← pow_mul, mul_comm (α j) 2, pow_mul, mul_pow, Real.sq_sqrt (hp j)]
    rw [hnorm]
    have hzprod : (∏ j, (p j * ‖z j‖ ^ (2 : ℕ)) ^ α j) ≤ τ ^ r * ∏ j, ‖z j‖ ^ (2 * α j) := by
      have hsplit : (∏ j, (p j * ‖z j‖ ^ (2 : ℕ)) ^ α j) =
          (∏ j, p j ^ α j) * ∏ j, ‖z j‖ ^ (2 * α j) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        rw [mul_pow, ← pow_mul, mul_comm 2 (α j)]
      rw [hsplit]
      refine mul_le_mul_of_nonneg_right (prod_pow_le_of_le hp hτ hα)
        (Finset.prod_nonneg fun j _ => by positivity)
    have hmult : (Nat.multinomial Finset.univ α : ℝ) ≤ (r.factorial : ℝ) := by
      exact_mod_cast multinomial_le_factorial_of_mem hα
    have hm0 : (0 : ℝ) ≤ (Nat.multinomial Finset.univ α : ℝ) := Nat.cast_nonneg _
    have hzp : (0 : ℝ) ≤ ∏ j, ‖z j‖ ^ (2 * α j) := Finset.prod_nonneg fun j _ => by positivity
    calc (Nat.multinomial Finset.univ α : ℝ) ^ (2 : ℕ) * ∏ j, (p j * ‖z j‖ ^ (2 : ℕ)) ^ α j
        ≤ (Nat.multinomial Finset.univ α : ℝ) ^ (2 : ℕ) * (τ ^ r * ∏ j, ‖z j‖ ^ (2 * α j)) :=
          mul_le_mul_of_nonneg_left hzprod (by positivity)
      _ ≤ (r.factorial : ℝ) * τ ^ r *
            ((Nat.multinomial Finset.univ α : ℝ) * ∏ j, ‖z j‖ ^ (2 * α j)) := by
          have hτr : (0 : ℝ) ≤ τ ^ r := pow_nonneg hτ0 r
          have hfac : (Nat.multinomial Finset.univ α : ℝ) ^ (2 : ℕ) *
              (τ ^ r * ∏ j, ‖z j‖ ^ (2 * α j)) =
              (Nat.multinomial Finset.univ α : ℝ) *
                ((Nat.multinomial Finset.univ α : ℝ) *
                  (τ ^ r * ∏ j, ‖z j‖ ^ (2 * α j))) := by ring
          have hrhs : (r.factorial : ℝ) * τ ^ r *
              ((Nat.multinomial Finset.univ α : ℝ) * ∏ j, ‖z j‖ ^ (2 * α j)) =
              (r.factorial : ℝ) *
                ((Nat.multinomial Finset.univ α : ℝ) *
                  (τ ^ r * ∏ j, ‖z j‖ ^ (2 * α j))) := by ring
          rw [hfac, hrhs]
          exact mul_le_mul_of_nonneg_right hmult
            (mul_nonneg hm0 (mul_nonneg hτr hzp))
  refine le_trans (Finset.sum_le_sum hcoeff) ?_
  rw [← Finset.mul_sum]
  have hmulti : (∑ α ∈ occupationSet d r,
      (Nat.multinomial Finset.univ α : ℝ) * ∏ j, ‖z j‖ ^ (2 * α j)) =
      (∑ j, ‖z j‖ ^ (2 : ℕ)) ^ r := by
    rw [occupationSet_eq_piAntidiag,
      Finset.sum_pow_eq_sum_piAntidiag Finset.univ (fun j => ‖z j‖ ^ (2 : ℕ)) r]
    refine Finset.sum_congr rfl fun α _ => ?_
    congr 1
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← pow_mul, mul_comm 2 (α j)]
  rw [hmulti]
  have hle1 : (∑ j, ‖z j‖ ^ (2 : ℕ)) ^ r ≤ 1 :=
    pow_le_one₀ (Finset.sum_nonneg fun j _ => by positivity) hz
  have hnn : (0 : ℝ) ≤ (r.factorial : ℝ) * τ ^ r :=
    mul_nonneg (by positivity) (pow_nonneg hτ0 r)
  calc (r.factorial : ℝ) * τ ^ r * (∑ j, ‖z j‖ ^ (2 : ℕ)) ^ r
      ≤ (r.factorial : ℝ) * τ ^ r * 1 := mul_le_mul_of_nonneg_left hle1 hnn
    _ = (r.factorial : ℝ) * τ ^ r := by ring

end FidelityMoment

section HeavyTransfer

/-- The heavy truncation of the occupation weights. -/
def heavyWeights (p : d → ℝ) (τ : ℝ) : d → ℝ := fun j => if τ < p j then p j else 0

theorem heavyWeights_nonneg {p : d → ℝ} (hp : ∀ j, 0 ≤ p j) (τ : ℝ) (j : d) :
    0 ≤ heavyWeights p τ j := by
  rw [heavyWeights]
  split <;> [exact hp j; exact le_rfl]

theorem sum_heavyWeights (p : d → ℝ) (τ : ℝ) :
    ∑ j, heavyWeights p τ j = ∑ j ∈ heavySector p τ, p j := by
  classical
  rw [heavySector, Finset.sum_filter]
  exact Finset.sum_congr rfl fun j _ => rfl

theorem torusReplicaPhaseOrbit_add_split (p : d → ℝ) (τ : ℝ) (x : d → ℝ) (j : d) :
    torusReplicaPhaseOrbit p x j =
      torusReplicaPhaseOrbit (heavyWeights p τ) x j + torusReplicaPhaseOrbit (lightWeights p τ) x j := by
  rw [torusReplicaPhaseOrbit, torusReplicaPhaseOrbit, torusReplicaPhaseOrbit, heavyWeights, lightWeights]
  by_cases h : τ < p j
  · rw [if_pos h, if_pos h]
    simp
  · rw [if_neg h, if_neg h]
    simp

theorem sum_normSq_torusReplicaPhaseOrbit {q : d → ℝ} (hq : ∀ j, 0 ≤ q j) (x : d → ℝ) :
    ∑ j, ‖torusReplicaPhaseOrbit q x j‖ ^ (2 : ℕ) = ∑ j, q j := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [torusReplicaPhaseOrbit, norm_mul, norm_charLift, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hq j)]

theorem norm_finiteComplexInner_le (u v : d → ℂ) :
    ‖finiteComplexInner u v‖ ≤
      Real.sqrt (∑ j, ‖u j‖ ^ (2 : ℕ)) * Real.sqrt (∑ j, ‖v j‖ ^ (2 : ℕ)) := by
  have hnorm : ∀ w : d → ℂ,
      ‖(WithLp.toLp 2 w : EuclideanSpace ℂ d)‖ = Real.sqrt (∑ j, ‖w j‖ ^ (2 : ℕ)) := by
    intro w
    rw [EuclideanSpace.norm_eq]
  rw [← inner_toLp_eq_finiteComplexInner u v, ← hnorm u, ← hnorm v]
  exact norm_inner_le_norm _ _

/-- **Heavy sector mass at the calibrated cap.**  With the cap set to four collisions over the
threshold, the heavy occupation mass is at most a quarter of the threshold. -/
theorem sum_heavyWeights_le {p : d → ℝ} (hp : ∀ j, 0 ≤ p j) {a : ℝ} (ha : 0 < a) :
    ∑ j, heavyWeights p (4 * occupationCollision p / a) j ≤ a / 4 := by
  classical
  rcases eq_or_lt_of_le (show (0 : ℝ) ≤ occupationCollision p from
      Finset.sum_nonneg fun j _ => sq_nonneg _) with hC | hC
  · have hCz : ∑ i, p i ^ (2 : ℕ) = 0 := hC.symm
    have hzero : ∀ j, p j = 0 := by
      intro j
      have hstep : p j ^ (2 : ℕ) ≤ ∑ i, p i ^ (2 : ℕ) :=
        Finset.single_le_sum (f := fun i => p i ^ (2 : ℕ)) (fun i _ => sq_nonneg (p i))
          (Finset.mem_univ j)
      rw [hCz] at hstep
      nlinarith [sq_nonneg (p j), hp j]
    have : ∑ j, heavyWeights p (4 * occupationCollision p / a) j = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [heavyWeights, hzero j]
      split <;> rfl
    rw [this]
    linarith
  · have hτ : 0 < 4 * occupationCollision p / a := by positivity
    have hstep := sum_heavySector_le hp hτ
    rw [sum_heavyWeights]
    refine le_trans hstep (le_of_eq ?_)
    have hCne : occupationCollision p ≠ 0 := ne_of_gt hC
    have hane : a ≠ 0 := ne_of_gt ha
    field_simp

/-- **Equation `(10)`.**  Removing the heavy spectral sector costs at most a factor four in the
capture threshold. -/
theorem fidelity_lightWeights_ge {p : d → ℝ} (hp : ∀ j, 0 ≤ p j) {τ a : ℝ} (ha : 0 < a)
    (hheavy : ∑ j, heavyWeights p τ j ≤ a / 4)
    {z : d → ℂ} (hz : ∑ j, ‖z j‖ ^ (2 : ℕ) ≤ 1) {x : d → ℝ}
    (hcap : a ≤ finitePureStateFidelity (torusReplicaPhaseOrbit p x) z) :
    a / 4 ≤ finitePureStateFidelity (torusReplicaPhaseOrbit (lightWeights p τ) x) z := by
  have hsplit : finiteComplexInner (torusReplicaPhaseOrbit p x) z =
      finiteComplexInner (torusReplicaPhaseOrbit (heavyWeights p τ) x) z +
        finiteComplexInner (torusReplicaPhaseOrbit (lightWeights p τ) x) z := by
    rw [finiteComplexInner, finiteComplexInner, finiteComplexInner, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [torusReplicaPhaseOrbit_add_split p τ x j, map_add]
    ring
  have hheavyNorm : ‖finiteComplexInner (torusReplicaPhaseOrbit (heavyWeights p τ) x) z‖ ≤
      Real.sqrt a / 2 := by
    refine le_trans (norm_finiteComplexInner_le _ _) ?_
    rw [sum_normSq_torusReplicaPhaseOrbit (heavyWeights_nonneg hp τ) x]
    have h1 : Real.sqrt (∑ j, heavyWeights p τ j) ≤ Real.sqrt (a / 4) :=
      Real.sqrt_le_sqrt hheavy
    have h2 : Real.sqrt (∑ j, ‖z j‖ ^ (2 : ℕ)) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hz
    have h3 : Real.sqrt (a / 4) = Real.sqrt a / 2 := by
      have h4 : Real.sqrt a / 2 = Real.sqrt a * Real.sqrt (1 / 4) := by
        rw [show Real.sqrt (1 / 4 : ℝ) = 1 / 2 by
          rw [show (1 / 4 : ℝ) = (1 / 2) ^ (2 : ℕ) by norm_num,
            Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 1 / 2)]]
        ring
      rw [h4, ← Real.sqrt_mul ha.le]
      congr 1
      ring
    calc Real.sqrt (∑ j, heavyWeights p τ j) * Real.sqrt (∑ j, ‖z j‖ ^ (2 : ℕ))
        ≤ Real.sqrt (a / 4) * 1 :=
          mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt a / 2 := by rw [mul_one, h3]
  have hfull : Real.sqrt a ≤ ‖finiteComplexInner (torusReplicaPhaseOrbit p x) z‖ := by
    rw [show ‖finiteComplexInner (torusReplicaPhaseOrbit p x) z‖ =
        Real.sqrt (‖finiteComplexInner (torusReplicaPhaseOrbit p x) z‖ ^ (2 : ℕ)) from
      (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hcap
  have hlight : Real.sqrt a / 2 ≤
      ‖finiteComplexInner (torusReplicaPhaseOrbit (lightWeights p τ) x) z‖ := by
    have htri : ‖finiteComplexInner (torusReplicaPhaseOrbit p x) z‖ ≤
        ‖finiteComplexInner (torusReplicaPhaseOrbit (heavyWeights p τ) x) z‖ +
          ‖finiteComplexInner (torusReplicaPhaseOrbit (lightWeights p τ) x) z‖ := by
      rw [hsplit]
      exact norm_add_le _ _
    linarith
  rw [finitePureStateFidelity]
  have hsq : (Real.sqrt a / 2) ^ (2 : ℕ) ≤
      ‖finiteComplexInner (torusReplicaPhaseOrbit (lightWeights p τ) x) z‖ ^ (2 : ℕ) :=
    pow_le_pow_left₀ (by positivity) hlight 2
  have hval : (Real.sqrt a / 2) ^ (2 : ℕ) = a / 4 := by
    rw [div_pow, Real.sq_sqrt ha.le]
    norm_num
  linarith [hval ▸ hsq]

end HeavyTransfer



end GaloisForLFunctions.HTGeometry
