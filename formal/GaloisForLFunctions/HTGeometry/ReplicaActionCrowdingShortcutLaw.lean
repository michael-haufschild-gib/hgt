import GaloisForLFunctions.HTGeometry.SubprobabilityPhaseTwistedReplicaShortcutActionLaw

/-!
# Replica-action crowding shortcut law

Finite-window and Gaussian shortcut bounds need not pay for the globally
smallest nonzero replica action.  At resolution `δ`, unresolved nonzero
actions form a graph on replica multiplicity vectors.  Its maximum local
degree controls their total mass by a weighted Schur estimate.  Thus an
isolated near-collision costs only one permutation-floor unit instead of
destroying the decay estimate for every replica pair.
-/

open scoped BigOperators Interval ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

theorem symmetricRelation_weighted_sum_le_degree_mul_sq
    {α : Type*} [Fintype α]
    (R : α → α → Prop) [DecidableRel R]
    (hR : ∀ x y, R x y → R y x) (v : α → ℝ) (K : ℝ)
    (hdegree : ∀ x, (∑ y, if R x y then (1 : ℝ) else 0) ≤ K) :
    (∑ x, ∑ y, if R x y then v x * v y else 0) ≤
      K * ∑ x, v x ^ 2 := by
  classical
  let S : ℝ := ∑ x, ∑ y, if R x y then v x * v y else 0
  let A : ℝ := ∑ x, ∑ y, if R x y then v x ^ 2 else 0
  have htranspose :
      (∑ x, ∑ y, if R x y then v y ^ 2 else 0) = A := by
    unfold A
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    by_cases hxy : R x y
    · have hyx : R y x := hR x y hxy
      simp [hxy, hyx]
    · have hyx : ¬ R y x := fun hyx => hxy (hR y x hyx)
      simp [hxy, hyx]
  have htwo : 2 * S ≤ 2 * A := by
    calc
      2 * S = ∑ x, ∑ y, if R x y then 2 * (v x * v y) else 0 := by
        simp only [S, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hxy : R x y <;> simp [hxy]
      _ ≤ ∑ x, ∑ y, if R x y then v x ^ 2 + v y ^ 2 else 0 := by
        apply Finset.sum_le_sum
        intro x hx
        apply Finset.sum_le_sum
        intro y hy
        split_ifs
        · nlinarith [sq_nonneg (v x - v y)]
        · exact le_rfl
      _ = ∑ x, ∑ y,
            ((if R x y then v x ^ 2 else 0) +
              (if R x y then v y ^ 2 else 0)) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hxy : R x y <;> simp [hxy]
      _ = (∑ x, ∑ y, if R x y then v x ^ 2 else 0) +
            (∑ x, ∑ y, if R x y then v y ^ 2 else 0) := by
        simp only [Finset.sum_add_distrib]
      _ = A + A := by
        rw [htranspose]
      _ = 2 * A := by ring
  have hA : A ≤ K * ∑ x, v x ^ 2 := by
    calc
      A = ∑ x, (∑ y, if R x y then (1 : ℝ) else 0) * v x ^ 2 := by
        simp only [A]
        apply Finset.sum_congr rfl
        intro x hx
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro y hy
        split_ifs <;> ring
      _ ≤ ∑ x, K * v x ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        exact mul_le_mul_of_nonneg_right (hdegree x) (sq_nonneg (v x))
      _ = K * ∑ x, v x ^ 2 := by rw [Finset.mul_sum]
  nlinarith

abbrev ReplicaMultiplicityIndex
    (I : Type*) [Fintype I] [DecidableEq I] (n : ℕ) :=
  {p : I → ℕ // p ∈ Finset.univ.piAntidiag n}

def fidelityReplicaMultiplicityAmplitude
    {I : Type*} [Fintype I]
    (weight : I → ℝ) (p : I → ℕ) : ℝ :=
  (Nat.multinomial Finset.univ p : ℝ) * ∏ i, weight i ^ p i

theorem fidelityReplicaMultiplicityWeight_eq_amplitude_mul
    {I : Type*} [Fintype I]
    (weight : I → ℝ) (p q : I → ℕ) :
    fidelityReplicaMultiplicityWeight weight p q =
      fidelityReplicaMultiplicityAmplitude weight p *
        fidelityReplicaMultiplicityAmplitude weight q := by
  simp only [fidelityReplicaMultiplicityWeight,
    fidelityReplicaMultiplicityAmplitude]
  ring

def replicaNearAction
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ)
    (p q : ReplicaMultiplicityIndex I n) : Prop :=
  0 < |replicaMultiplicityEnergy energy p.1 -
      replicaMultiplicityEnergy energy q.1| ∧
    |replicaMultiplicityEnergy energy p.1 -
      replicaMultiplicityEnergy energy q.1| < δ

noncomputable instance replicaNearActionDecidable
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ) :
    DecidableRel (replicaNearAction energy n δ) :=
  Classical.decRel _

noncomputable def replicaActionCrowdingDegree
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ) : ℕ := by
  classical
  exact Finset.univ.sup fun p : ReplicaMultiplicityIndex I n =>
    (Finset.univ.filter (replicaNearAction energy n δ p)).card

theorem card_filter_replicaNearAction_le_crowdingDegree
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) (δ : ℝ)
    (p : ReplicaMultiplicityIndex I n) :
    (Finset.univ.filter (replicaNearAction energy n δ p)).card ≤
      replicaActionCrowdingDegree energy n δ := by
  classical
  unfold replicaActionCrowdingDegree
  exact Finset.le_sup (s := (Finset.univ : Finset (ReplicaMultiplicityIndex I n)))
    (f := fun p => (Finset.univ.filter (replicaNearAction energy n δ p)).card)
    (Finset.mem_univ p)

noncomputable def fidelityReplicaNearActionMass
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ) (δ : ℝ) : ℝ := by
  classical
  exact ∑ p : ReplicaMultiplicityIndex I n,
    ∑ q : ReplicaMultiplicityIndex I n,
      if replicaNearAction energy n δ p q then
        fidelityReplicaMultiplicityWeight weight p.1 q.1
      else 0

theorem fidelityReplicaNearActionMass_eq_finset
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ) (δ : ℝ) :
    fidelityReplicaNearActionMass weight energy n δ =
      ∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          if 0 < |replicaMultiplicityEnergy energy p -
              replicaMultiplicityEnergy energy q| ∧
            |replicaMultiplicityEnergy energy p -
              replicaMultiplicityEnergy energy q| < δ
          then fidelityReplicaMultiplicityWeight weight p q
          else 0 := by
  classical
  unfold fidelityReplicaNearActionMass
  symm
  calc
    (∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          if 0 < |replicaMultiplicityEnergy energy p -
              replicaMultiplicityEnergy energy q| ∧
            |replicaMultiplicityEnergy energy p -
              replicaMultiplicityEnergy energy q| < δ
          then fidelityReplicaMultiplicityWeight weight p q
          else 0) =
        ∑ p : ReplicaMultiplicityIndex I n,
          ∑ q ∈ Finset.univ.piAntidiag n,
            if 0 < |replicaMultiplicityEnergy energy p.1 -
                replicaMultiplicityEnergy energy q| ∧
              |replicaMultiplicityEnergy energy p.1 -
                replicaMultiplicityEnergy energy q| < δ
            then fidelityReplicaMultiplicityWeight weight p.1 q
            else 0 :=
      Finset.sum_subtype (Finset.univ.piAntidiag n) (by simp) _
    _ = ∑ p : ReplicaMultiplicityIndex I n,
          ∑ q : ReplicaMultiplicityIndex I n,
            if 0 < |replicaMultiplicityEnergy energy p.1 -
                replicaMultiplicityEnergy energy q.1| ∧
              |replicaMultiplicityEnergy energy p.1 -
                replicaMultiplicityEnergy energy q.1| < δ
            then fidelityReplicaMultiplicityWeight weight p.1 q.1
            else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      exact Finset.sum_subtype (Finset.univ.piAntidiag n) (by simp) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      by_cases h :
          0 < |replicaMultiplicityEnergy energy p.1 -
            replicaMultiplicityEnergy energy q.1| ∧
          |replicaMultiplicityEnergy energy p.1 -
            replicaMultiplicityEnergy energy q.1| < δ
      · simp [replicaNearAction, h]
      · simp [replicaNearAction]

def fidelityReplicaSubtypePermutationFloor
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (n : ℕ) : ℝ :=
  ∑ p : ReplicaMultiplicityIndex I n,
    fidelityReplicaMultiplicityWeight weight p.1 p.1

theorem fidelityReplicaSubtypePermutationFloor_eq
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (n : ℕ) :
    fidelityReplicaSubtypePermutationFloor weight n =
      fidelityReplicaPermutationFloor weight n := by
  classical
  unfold fidelityReplicaSubtypePermutationFloor fidelityReplicaPermutationFloor
  exact (Finset.sum_subtype (Finset.univ.piAntidiag n) (by simp)
    (fun p => fidelityReplicaMultiplicityWeight weight p p)).symm

theorem fidelityReplicaNearActionMass_le_crowdingDegree_mul_floor
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ) (δ : ℝ) :
    fidelityReplicaNearActionMass weight energy n δ ≤
      (replicaActionCrowdingDegree energy n δ : ℝ) *
        fidelityReplicaSubtypePermutationFloor weight n := by
  classical
  have hsymm : ∀ p q : ReplicaMultiplicityIndex I n,
      replicaNearAction energy n δ p q →
        replicaNearAction energy n δ q p := by
    intro p q hpq
    rcases hpq with ⟨hpos, hlt⟩
    constructor
    · simpa only [abs_sub_comm] using hpos
    · simpa only [abs_sub_comm] using hlt
  have hdegree : ∀ p : ReplicaMultiplicityIndex I n,
      (∑ q, if replicaNearAction energy n δ p q then (1 : ℝ) else 0) ≤
        (replicaActionCrowdingDegree energy n δ : ℝ) := by
    intro p
    have hcard := card_filter_replicaNearAction_le_crowdingDegree energy n δ p
    calc
      (∑ q, if replicaNearAction energy n δ p q then (1 : ℝ) else 0) =
          ((Finset.univ.filter (replicaNearAction energy n δ p)).card : ℝ) := by
            simp
      _ ≤ (replicaActionCrowdingDegree energy n δ : ℝ) := by
        exact_mod_cast hcard
  have hgraph := symmetricRelation_weighted_sum_le_degree_mul_sq
    (replicaNearAction energy n δ) hsymm
    (fun p : ReplicaMultiplicityIndex I n =>
      fidelityReplicaMultiplicityAmplitude weight p.1)
    (replicaActionCrowdingDegree energy n δ : ℝ) hdegree
  simpa only [fidelityReplicaNearActionMass,
      fidelityReplicaSubtypePermutationFloor,
      fidelityReplicaMultiplicityWeight_eq_amplitude_mul,
      pow_two] using hgraph

theorem norm_twistedGaussianSpectralFidelityMean_le_collision_add_crowding
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    ‖twistedGaussianSpectralFidelityMean weight energy twist n T‖ ≤
      fidelityReplicaCollisionMass weight energy n +
        fidelityReplicaNearActionMass weight energy n δ +
          Real.exp (-((T * δ) ^ 2) / 2) := by
  classical
  let B : ℝ := Real.exp (-((T * δ) ^ 2) / 2)
  have hBnonneg : 0 ≤ B := (Real.exp_pos _).le
  have hsumNonneg : 0 ≤ ∑ i, weight i :=
    Finset.sum_nonneg fun i hi => hweight i
  have htotal :
      (∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          fidelityReplicaMultiplicityWeight weight p q) =
        (∑ i, weight i) ^ (2 * n) :=
    sum_fidelityReplicaMultiplicityWeight_eq_sum_pow weight n
  have htotalLe : (∑ i, weight i) ^ (2 * n) ≤ 1 :=
    pow_le_one₀ hsumNonneg hweightSum
  have hkernelOne (x : ℝ) :
      ‖gaussianObserverActionKernel x‖ ≤ 1 := by
    rw [norm_gaussianObserverActionKernel]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg x])
  rw [twistedGaussianSpectralFidelityMean_eq_actionKernel]
  calc
    ‖∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
            replicaMultiplicityTwist twist p q *
            gaussianObserverActionKernel
              (T * (replicaMultiplicityEnergy energy p -
                replicaMultiplicityEnergy energy q))‖
        ≤ ∑ p ∈ Finset.univ.piAntidiag n,
            ∑ q ∈ Finset.univ.piAntidiag n,
              ‖(fidelityReplicaMultiplicityWeight weight p q : ℂ) *
                replicaMultiplicityTwist twist p q *
                gaussianObserverActionKernel
                  (T * (replicaMultiplicityEnergy energy p -
                    replicaMultiplicityEnergy energy q))‖ := by
          exact (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun p _ => norm_sum_le _ _)
    _ ≤ ∑ p ∈ Finset.univ.piAntidiag n,
          ∑ q ∈ Finset.univ.piAntidiag n,
            ((if replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
              then fidelityReplicaMultiplicityWeight weight p q
              else 0) +
            (if 0 < |replicaMultiplicityEnergy energy p -
                  replicaMultiplicityEnergy energy q| ∧
                |replicaMultiplicityEnergy energy p -
                  replicaMultiplicityEnergy energy q| < δ
              then fidelityReplicaMultiplicityWeight weight p q
              else 0) +
            fidelityReplicaMultiplicityWeight weight p q * B) := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.sum_le_sum
          intro q hq
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (fidelityReplicaMultiplicityWeight_nonneg hweight p q),
            norm_replicaMultiplicityTwist htwist]
          simp only [mul_one]
          let a := |replicaMultiplicityEnergy energy p -
            replicaMultiplicityEnergy energy q|
          by_cases heq : replicaMultiplicityEnergy energy p =
              replicaMultiplicityEnergy energy q
          · rw [heq, sub_self, mul_zero, gaussianObserverActionKernel_zero]
            simp only [norm_one, mul_one, abs_zero, lt_self_iff_false,
              false_and, if_false, if_true]
            have hw := fidelityReplicaMultiplicityWeight_nonneg hweight p q
            nlinarith
          · have hapos : 0 < a := by
              unfold a
              exact abs_pos.mpr (sub_ne_zero.mpr heq)
            by_cases hnear : a < δ
            · rw [if_neg heq, if_pos ⟨hapos, hnear⟩, zero_add]
              have hk := hkernelOne
                (T * (replicaMultiplicityEnergy energy p -
                  replicaMultiplicityEnergy energy q))
              have hw := fidelityReplicaMultiplicityWeight_nonneg hweight p q
              nlinarith
            · rw [if_neg heq, if_neg (not_and_of_not_right _ hnear),
                zero_add, zero_add]
              have hfar : δ ≤ a := le_of_not_gt hnear
              exact mul_le_mul_of_nonneg_left
                (norm_gaussianObserverActionKernel_mul_le hT hδ hfar)
                (fidelityReplicaMultiplicityWeight_nonneg hweight p q)
    _ = fidelityReplicaCollisionMass weight energy n +
          fidelityReplicaNearActionMass weight energy n δ +
          (∑ i, weight i) ^ (2 * n) * B := by
          simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          rw [htotal, ← fidelityReplicaResonantMass_eq_collisionMass,
            fidelityReplicaNearActionMass_eq_finset]
          rfl
    _ ≤ fidelityReplicaCollisionMass weight energy n +
          fidelityReplicaNearActionMass weight energy n δ + B := by
          exact add_le_add (le_refl _)
            (mul_le_of_le_one_left hBnonneg htotalLe)
    _ = fidelityReplicaCollisionMass weight energy n +
          fidelityReplicaNearActionMass weight energy n δ +
          Real.exp (-((T * δ) ^ 2) / 2) := rfl

theorem norm_twistedGaussianSpectralFidelityMean_le_collision_add_degree_floor
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    ‖twistedGaussianSpectralFidelityMean weight energy twist n T‖ ≤
      fidelityReplicaCollisionMass weight energy n +
        (replicaActionCrowdingDegree energy n δ : ℝ) *
          fidelityReplicaPermutationFloor weight n +
        Real.exp (-((T * δ) ^ 2) / 2) := by
  have hnear := fidelityReplicaNearActionMass_le_crowdingDegree_mul_floor
    weight energy n δ
  rw [fidelityReplicaSubtypePermutationFloor_eq] at hnear
  exact (norm_twistedGaussianSpectralFidelityMean_le_collision_add_crowding
      hweight hweightSum htwist n hT hδ).trans (by linarith)

theorem norm_twistedFiniteSpectralFidelityMean_le_collision_add_crowding
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    ‖twistedFiniteSpectralFidelityMean weight energy twist n T‖ ≤
      fidelityReplicaCollisionMass weight energy n +
        fidelityReplicaNearActionMass weight energy n δ +
          min 1 (T * δ)⁻¹ := by
  classical
  let B : ℝ := min 1 (T * δ)⁻¹
  have hBnonneg : 0 ≤ B := by
    unfold B
    positivity
  have hsumNonneg : 0 ≤ ∑ i, weight i :=
    Finset.sum_nonneg fun i hi => hweight i
  have htotal :
      (∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          fidelityReplicaMultiplicityWeight weight p q) =
        (∑ i, weight i) ^ (2 * n) :=
    sum_fidelityReplicaMultiplicityWeight_eq_sum_pow weight n
  have htotalLe : (∑ i, weight i) ^ (2 * n) ≤ 1 :=
    pow_le_one₀ hsumNonneg hweightSum
  have hkernelOne (x : ℝ) : ‖symmetricPhaseAverage T x‖ ≤ 1 := by
    rw [symmetricPhaseAverage_eq_sinc T x hT.ne', Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_real_sinc_le_one _
  rw [twistedFiniteSpectralFidelityMean_eq_replicaPhaseAverage]
  calc
    ‖∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
            replicaMultiplicityTwist twist p q *
            symmetricPhaseAverage T
              (replicaMultiplicityEnergy energy p -
                replicaMultiplicityEnergy energy q)‖
        ≤ ∑ p ∈ Finset.univ.piAntidiag n,
            ∑ q ∈ Finset.univ.piAntidiag n,
              ‖(fidelityReplicaMultiplicityWeight weight p q : ℂ) *
                replicaMultiplicityTwist twist p q *
                symmetricPhaseAverage T
                  (replicaMultiplicityEnergy energy p -
                    replicaMultiplicityEnergy energy q)‖ := by
          exact (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun p _ => norm_sum_le _ _)
    _ ≤ ∑ p ∈ Finset.univ.piAntidiag n,
          ∑ q ∈ Finset.univ.piAntidiag n,
            ((if replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
              then fidelityReplicaMultiplicityWeight weight p q
              else 0) +
            (if 0 < |replicaMultiplicityEnergy energy p -
                  replicaMultiplicityEnergy energy q| ∧
                |replicaMultiplicityEnergy energy p -
                  replicaMultiplicityEnergy energy q| < δ
              then fidelityReplicaMultiplicityWeight weight p q
              else 0) +
            fidelityReplicaMultiplicityWeight weight p q * B) := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.sum_le_sum
          intro q hq
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (fidelityReplicaMultiplicityWeight_nonneg hweight p q),
            norm_replicaMultiplicityTwist htwist]
          simp only [mul_one]
          let a := |replicaMultiplicityEnergy energy p -
            replicaMultiplicityEnergy energy q|
          by_cases heq : replicaMultiplicityEnergy energy p =
              replicaMultiplicityEnergy energy q
          · rw [heq, sub_self,
              symmetricPhaseAverage_eq_sinc T 0 hT.ne']
            simp only [mul_zero, Real.sinc_zero, Complex.norm_real,
              Real.norm_eq_abs, abs_one, mul_one, abs_zero,
              lt_self_iff_false, false_and, if_false, if_true]
            have hw := fidelityReplicaMultiplicityWeight_nonneg hweight p q
            nlinarith
          · have hapos : 0 < a := by
              unfold a
              exact abs_pos.mpr (sub_ne_zero.mpr heq)
            by_cases hnear : a < δ
            · rw [if_neg heq, if_pos ⟨hapos, hnear⟩, zero_add]
              have hk := hkernelOne
                (replicaMultiplicityEnergy energy p -
                  replicaMultiplicityEnergy energy q)
              have hw := fidelityReplicaMultiplicityWeight_nonneg hweight p q
              nlinarith
            · rw [if_neg heq, if_neg (not_and_of_not_right _ hnear),
                zero_add, zero_add]
              have hfar : δ ≤ a := le_of_not_gt hnear
              exact mul_le_mul_of_nonneg_left
                (norm_symmetricPhaseAverage_le_min_inv hT hδ hfar)
                (fidelityReplicaMultiplicityWeight_nonneg hweight p q)
    _ = fidelityReplicaCollisionMass weight energy n +
          fidelityReplicaNearActionMass weight energy n δ +
          (∑ i, weight i) ^ (2 * n) * B := by
          simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          rw [htotal, ← fidelityReplicaResonantMass_eq_collisionMass,
            fidelityReplicaNearActionMass_eq_finset]
          rfl
    _ ≤ fidelityReplicaCollisionMass weight energy n +
          fidelityReplicaNearActionMass weight energy n δ + B := by
          exact add_le_add (le_refl _)
            (mul_le_of_le_one_left hBnonneg htotalLe)
    _ = fidelityReplicaCollisionMass weight energy n +
          fidelityReplicaNearActionMass weight energy n δ +
          min 1 (T * δ)⁻¹ := rfl

theorem norm_twistedFiniteSpectralFidelityMean_le_collision_add_degree_floor
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ) :
    ‖twistedFiniteSpectralFidelityMean weight energy twist n T‖ ≤
      fidelityReplicaCollisionMass weight energy n +
        (replicaActionCrowdingDegree energy n δ : ℝ) *
          fidelityReplicaPermutationFloor weight n +
        min 1 (T * δ)⁻¹ := by
  have hnear := fidelityReplicaNearActionMass_le_crowdingDegree_mul_floor
    weight energy n δ
  rw [fidelityReplicaSubtypePermutationFloor_eq] at hnear
  exact (norm_twistedFiniteSpectralFidelityMean_le_collision_add_crowding
      hweight hweightSum htwist n hT hδ).trans (by linarith)

theorem threshold_pow_mul_gaussianTwistedCoherenceCaptureSet_measureReal_le_norm
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) (hn : 0 < n) {T threshold : ℝ}
    (hthreshold : 0 ≤ threshold) :
    threshold ^ (2 * n) *
        (gaussianReal 0 1).real
          (gaussianTwistedCoherenceCaptureSet
            weight energy twist T threshold) ≤
      ‖twistedGaussianSpectralFidelityMean
        weight energy twist n T‖ := by
  let f : ℝ → ℝ := fun x =>
    ‖twistedFiniteSpectralAmplitude weight energy twist (T * x)‖ ^ (2 * n)
  have hfcont : Continuous f := by
    unfold f twistedFiniteSpectralAmplitude
    fun_prop
  have hfint : Integrable f (gaussianReal 0 1) := by
    have hbound : ∀ x, f x ≤ 1 := by
      intro x
      have hamp :
          ‖twistedFiniteSpectralAmplitude weight energy twist (T * x)‖ ≤ 1 := by
        unfold twistedFiniteSpectralAmplitude
        calc
          ‖∑ i, (weight i : ℂ) * twist i *
              Complex.exp (((energy i * (T * x) : ℝ) : ℂ) * Complex.I)‖
              ≤ ∑ i, ‖(weight i : ℂ) * twist i *
                Complex.exp (((energy i * (T * x) : ℝ) : ℂ) * Complex.I)‖ :=
                norm_sum_le _ _
          _ = ∑ i, weight i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (hweight i), htwist, Complex.norm_exp]
            simp
          _ ≤ 1 := hweightSum
      exact pow_le_one₀ (norm_nonneg _) hamp
    refine (integrable_const (1 : ℝ)).mono' hfcont.aestronglyMeasurable ?_
    filter_upwards with x
    exact Real.norm_of_nonneg (by positivity) |>.trans_le (hbound x)
  have hnn : 0 ≤ᵐ[gaussianReal 0 1] f :=
    Filter.Eventually.of_forall fun x => by positivity
  have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    hnn hfint (threshold ^ (2 * n))
  have hset :
      {x : ℝ | threshold ^ (2 * n) ≤ f x} =
        gaussianTwistedCoherenceCaptureSet
          weight energy twist T threshold := by
    ext x
    unfold f gaussianTwistedCoherenceCaptureSet
    simp only [Set.mem_setOf_eq]
    have hexp : 2 * n ≠ 0 := by omega
    exact pow_le_pow_iff_left₀ hthreshold (norm_nonneg _) hexp
  rw [hset] at hmark
  refine hmark.trans ?_
  have hmeanReal :
      ∫ x : ℝ, f x ∂gaussianReal 0 1 =
        (twistedGaussianSpectralFidelityMean
          weight energy twist n T).re := by
    have hfc : Integrable (fun x => (f x : ℂ)) (gaussianReal 0 1) :=
      hfint.ofReal
    calc
      (∫ x : ℝ, f x ∂gaussianReal 0 1) =
          ∫ x : ℝ, ((f x : ℂ)).re ∂gaussianReal 0 1 := by simp
      _ = (∫ x : ℝ, (f x : ℂ) ∂gaussianReal 0 1).re :=
        integral_re hfc
      _ = (twistedGaussianSpectralFidelityMean
          weight energy twist n T).re := by
        congr 1
        unfold twistedGaussianSpectralFidelityMean
        apply integral_congr_ae
        filter_upwards with x
        unfold f twistedFiniteSpectralFidelity
        rw [Complex.normSq_eq_norm_sq]
        norm_cast
        rw [pow_mul]
  rw [hmeanReal]
  exact Complex.re_le_norm _

theorem threshold_pow_mul_gaussianTwistedCoherenceCaptureSet_measureReal_le_degree_floor
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ threshold : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hthreshold : 0 ≤ threshold) :
    threshold ^ (2 * n) *
        (gaussianReal 0 1).real
          (gaussianTwistedCoherenceCaptureSet
            weight energy twist T threshold) ≤
      fidelityReplicaCollisionMass weight energy n +
        (replicaActionCrowdingDegree energy n δ : ℝ) *
          fidelityReplicaPermutationFloor weight n +
        Real.exp (-((T * δ) ^ 2) / 2) := by
  exact (threshold_pow_mul_gaussianTwistedCoherenceCaptureSet_measureReal_le_norm
      hweight hweightSum htwist n hn hthreshold).trans
    (norm_twistedGaussianSpectralFidelityMean_le_collision_add_degree_floor
      hweight hweightSum htwist n hT hδ)

theorem threshold_pow_mul_uniformTwistedCoherenceCaptureSet_measureReal_le_norm
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (n : ℕ) (hn : 0 < n) {T threshold : ℝ}
    (hT : 0 < T) (hthreshold : 0 ≤ threshold) :
    threshold ^ (2 * n) *
        volume.real
          (uniformTwistedCoherenceCaptureSet
            weight energy twist T threshold) ≤
      2 * T * ‖twistedFiniteSpectralFidelityMean
        weight energy twist n T‖ := by
  let f : ℝ → ℝ := fun t =>
    ‖twistedFiniteSpectralAmplitude weight energy twist t‖ ^ (2 * n)
  have hfcont : Continuous f := by
    unfold f twistedFiniteSpectralAmplitude
    fun_prop
  have hfint : IntegrableOn f (Set.Ioc (-T) T) :=
    hfcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (-T) T)] f :=
    Filter.Eventually.of_forall fun t => by positivity
  have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    hnn hfint (threshold ^ (2 * n))
  have hlevelMeas : MeasurableSet {t : ℝ | threshold ^ (2 * n) ≤ f t} :=
    measurableSet_le measurable_const hfcont.measurable
  have hset :
      {t : ℝ | threshold ^ (2 * n) ≤ f t} ∩ Set.Ioc (-T) T =
        uniformTwistedCoherenceCaptureSet
          weight energy twist T threshold := by
    ext t
    unfold f uniformTwistedCoherenceCaptureSet
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
    have hexp : 2 * n ≠ 0 := by omega
    rw [pow_le_pow_iff_left₀ hthreshold (norm_nonneg _) hexp]
    tauto
  have hmark' :
      threshold ^ (2 * n) *
          volume.real
            (uniformTwistedCoherenceCaptureSet
              weight energy twist T threshold) ≤
        ∫ t in Set.Ioc (-T) T, f t := by
    rw [measureReal_restrict_apply hlevelMeas] at hmark
    rwa [hset] at hmark
  refine hmark'.trans ?_
  have hfc : IntegrableOn (fun t => (f t : ℂ)) (Set.Ioc (-T) T) :=
    hfint.ofReal
  have hrealIntegral :
      ∫ t in Set.Ioc (-T) T, f t =
        (∫ t : ℝ in -T..T, (f t : ℂ)).re := by
    calc
      (∫ t in Set.Ioc (-T) T, f t) =
          ∫ t in Set.Ioc (-T) T, ((f t : ℂ)).re := by simp
      _ = (∫ t in Set.Ioc (-T) T, (f t : ℂ)).re :=
        integral_re hfc
      _ = (∫ t : ℝ in -T..T, (f t : ℂ)).re := by
        rw [intervalIntegral.integral_of_le (by linarith)]
  rw [hrealIntegral]
  have hintegralMean :
      (∫ t : ℝ in -T..T, (f t : ℂ)) =
        (2 * T : ℂ) *
          twistedFiniteSpectralFidelityMean weight energy twist n T := by
    unfold twistedFiniteSpectralFidelityMean
    have h2T : (2 * T : ℂ) ≠ 0 := by
      exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr hT.ne')
    symm
    calc
      (2 * T : ℂ) * ((2 * T : ℂ)⁻¹ *
          ∫ t : ℝ in -T..T,
            twistedFiniteSpectralFidelity weight energy twist t ^ n) =
          ((2 * T : ℂ) * (2 * T : ℂ)⁻¹) *
            ∫ t : ℝ in -T..T,
              twistedFiniteSpectralFidelity weight energy twist t ^ n := by ring
      _ = ∫ t : ℝ in -T..T,
              twistedFiniteSpectralFidelity weight energy twist t ^ n := by
            rw [mul_inv_cancel₀ h2T, one_mul]
      _ = ∫ t : ℝ in -T..T, (f t : ℂ) := by
            apply intervalIntegral.integral_congr
            intro t ht
            unfold f twistedFiniteSpectralFidelity
            change
              ((Complex.normSq
                  (twistedFiniteSpectralAmplitude weight energy twist t) : ℂ) ^ n) =
                (↑(‖twistedFiniteSpectralAmplitude weight energy twist t‖ ^
                  (2 * n)) : ℂ)
            rw [Complex.normSq_eq_norm_sq]
            norm_cast
            rw [pow_mul]
  have hreMul :
      ((2 * T : ℂ) *
        twistedFiniteSpectralFidelityMean weight energy twist n T).re =
      2 * T *
        (twistedFiniteSpectralFidelityMean weight energy twist n T).re := by
    rw [Complex.mul_re]
    norm_num
  rw [hintegralMean, hreMul]
  exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _)
    (mul_nonneg (by norm_num) hT.le)

theorem threshold_pow_mul_uniformTwistedCoherenceCaptureSet_measureReal_le_degree_floor
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ threshold : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hthreshold : 0 ≤ threshold) :
    threshold ^ (2 * n) *
        volume.real
          (uniformTwistedCoherenceCaptureSet
            weight energy twist T threshold) ≤
      2 * T *
        (fidelityReplicaCollisionMass weight energy n +
          (replicaActionCrowdingDegree energy n δ : ℝ) *
            fidelityReplicaPermutationFloor weight n +
          min 1 (T * δ)⁻¹) := by
  exact (threshold_pow_mul_uniformTwistedCoherenceCaptureSet_measureReal_le_norm
      n hn hT hthreshold).trans
    (mul_le_mul_of_nonneg_left
      (norm_twistedFiniteSpectralFidelityMean_le_collision_add_degree_floor
        hweight hweightSum htwist n hT hδ)
      (mul_nonneg (by norm_num) hT.le))

end GaloisForLFunctions.HTGeometry
