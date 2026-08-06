import GaloisForLFunctions.HTGeometry.SubprobabilityPhaseTwistedReplicaShortcutActionLaw
import GaloisForLFunctions.RHTower.AdaptiveStaticChoiCircuitShortcutActionLaw

/-!
# Direct-net adaptive static-Choi shortcut action law

Direct overlap with each arbitrary full Choi target removes the orbit-anchor
triangle loss.  Every capture radius below one is therefore available.  Under
maximal projective spectral rank, the target-specific replica collision mass
is at most `r! d⁻ʳ`, uniformly over the full `d²`-dimensional target space.

Finite target dictionaries may be selected after observing time.  An arbitrary
possibly infinite target class is handled through any supplied finite metric
net; the selector itself needs no measurable structure.
-/

open scoped BigOperators ComplexConjugate Interval ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

def directStaticChoiTargetWeight
    (d : ℕ) (target : EuclideanSpace ℂ (Fin d × Fin d))
    (i : Fin d) : ℝ :=
  (Real.sqrt (d : ℝ))⁻¹ * ‖target (i, i)‖

def directStaticChoiTargetTwist
    {d : ℕ} (target : EuclideanSpace ℂ (Fin d × Fin d))
    (i : Fin d) : ℂ :=
  if target (i, i) = 0 then 1
  else target (i, i) / (‖target (i, i)‖ : ℂ)

theorem norm_directStaticChoiTargetTwist
    {d : ℕ} (target : EuclideanSpace ℂ (Fin d × Fin d))
    (i : Fin d) :
    ‖directStaticChoiTargetTwist target i‖ = 1 := by
  unfold directStaticChoiTargetTwist
  split_ifs with h
  · simp
  · rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr h)

theorem directStaticChoiTargetWeight_mul_twist
    {d : ℕ} (target : EuclideanSpace ℂ (Fin d × Fin d))
    (i : Fin d) :
    (directStaticChoiTargetWeight d target i : ℂ) *
        directStaticChoiTargetTwist target i =
      ((Real.sqrt (d : ℝ))⁻¹ : ℂ) * target (i, i) := by
  unfold directStaticChoiTargetWeight directStaticChoiTargetTwist
  split_ifs with h
  · simp [h]
  · have hnorm : ‖target (i, i)‖ ≠ 0 := norm_ne_zero_iff.mpr h
    push_cast
    field_simp [hnorm]

theorem inner_staticSpectralChoiVector_target_eq_directTwistedAmplitude
    {d : ℕ} (t : ℝ) (energy : Fin d → ℝ)
    (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    inner ℂ (staticSpectralChoiVector d t energy) target =
      twistedFiniteSpectralAmplitude
        (directStaticChoiTargetWeight d target) (fun i => -energy i)
        (directStaticChoiTargetTwist target) t := by
  rw [EuclideanSpace.inner_toLp_toLp]
  change
    (∑ ij : Fin d × Fin d,
      target ij * starRingEnd ℂ
        (if ij.1 = ij.2 then
          ((Real.sqrt (d : ℝ))⁻¹ : ℂ) *
            fourier 1 (finiteHamiltonianAddCirclePhase t energy ij.1)
        else 0)) = _
  rw [Fintype.sum_prod_type]
  simp_rw [apply_ite (starRingEnd ℂ)]
  simp only [map_zero, mul_ite, mul_zero, Fintype.sum_ite_eq]
  simp_rw [fourier_finiteHamiltonianAddCirclePhase]
  unfold twistedFiniteSpectralAmplitude
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul, starRingEnd_apply, Complex.star_def, map_inv₀,
    Complex.conj_ofReal]
  rw [show
      starRingEnd ℂ (finiteObserverHamiltonianVertexPhase t energy i) =
        Complex.exp ((((-energy i) * t : ℝ) : ℂ) * Complex.I) by
    unfold finiteObserverHamiltonianVertexPhase
    rw [starRingEnd_apply, Complex.star_def, ← Complex.exp_conj]
    congr 1
    push_cast
    simp
    ring]
  rw [directStaticChoiTargetWeight_mul_twist]
  ring

theorem sum_norm_sq_staticChoiTarget_diagonal_le_one
    {d : ℕ} {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) :
    ∑ i : Fin d, ‖target (i, i)‖ ^ 2 ≤ 1 := by
  let diag : Fin d → Fin d × Fin d := fun i => (i, i)
  have hdiag : Function.Injective diag := by
    intro i j h
    exact congrArg Prod.fst h
  calc
    ∑ i : Fin d, ‖target (i, i)‖ ^ 2 =
        ∑ i : Fin d, ‖target (diag i)‖ ^ 2 := rfl
    _ = ∑ ij ∈ Finset.univ.image diag, ‖target ij‖ ^ 2 := by
      rw [Finset.sum_image]
      exact hdiag.injOn
    _ ≤ ∑ ij : Fin d × Fin d, ‖target ij‖ ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
    _ = ‖target‖ ^ 2 := (EuclideanSpace.norm_sq_eq target).symm
    _ = 1 := by rw [htarget]; norm_num

theorem sum_directStaticChoiTargetWeight_le_one
    {d : ℕ} (hd : 0 < d)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) :
    ∑ i, directStaticChoiTargetWeight d target i ≤ 1 := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrtPos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  have hmass := sum_norm_sq_staticChoiTarget_diagonal_le_one htarget
  have hmassNonneg : 0 ≤ ∑ i : Fin d, ‖target (i, i)‖ ^ 2 :=
    Finset.sum_nonneg fun i hi => sq_nonneg _
  have hrootMass : Real.sqrt (∑ i : Fin d, ‖target (i, i)‖ ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_iff]
    exact ⟨by norm_num, by simpa using hmass⟩
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt
    (Finset.univ : Finset (Fin d)) (fun _ => (1 : ℝ))
      (fun i => ‖target (i, i)‖)
  simp only [one_mul, one_pow, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hcs
  have hsumNorm : ∑ i : Fin d, ‖target (i, i)‖ ≤ Real.sqrt (d : ℝ) := by
    calc
      ∑ i : Fin d, ‖target (i, i)‖ ≤
          Real.sqrt (d : ℝ) *
            Real.sqrt (∑ i : Fin d, ‖target (i, i)‖ ^ 2) := hcs
      _ ≤ Real.sqrt (d : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hrootMass hsqrtPos.le
      _ = Real.sqrt (d : ℝ) := mul_one _
  calc
    ∑ i, directStaticChoiTargetWeight d target i =
        (Real.sqrt (d : ℝ))⁻¹ * ∑ i, ‖target (i, i)‖ := by
      unfold directStaticChoiTargetWeight
      rw [Finset.mul_sum]
    _ ≤ (Real.sqrt (d : ℝ))⁻¹ * Real.sqrt (d : ℝ) :=
      mul_le_mul_of_nonneg_left hsumNorm (inv_nonneg.mpr hsqrtPos.le)
    _ = 1 := inv_mul_cancel₀ hsqrtPos.ne'

theorem sum_sq_directStaticChoiTargetWeight_le_inv
    {d : ℕ} (hd : 0 < d)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) :
    ∑ i, directStaticChoiTargetWeight d target i ^ 2 ≤ (d : ℝ)⁻¹ := by
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hsqrtPos : 0 < Real.sqrt (d : ℝ) := Real.sqrt_pos.2 hdR
  have hmass := sum_norm_sq_staticChoiTarget_diagonal_le_one htarget
  calc
    ∑ i, directStaticChoiTargetWeight d target i ^ 2 =
        (Real.sqrt (d : ℝ))⁻¹ ^ 2 *
          ∑ i, ‖target (i, i)‖ ^ 2 := by
      unfold directStaticChoiTargetWeight
      simp_rw [mul_pow, ← Finset.mul_sum]
    _ ≤ (Real.sqrt (d : ℝ))⁻¹ ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hmass (sq_nonneg _)
    _ = (d : ℝ)⁻¹ := by
      rw [mul_one, inv_pow, Real.sq_sqrt hdR.le]

theorem directStaticChoiTargetWeight_nonneg
    {d : ℕ} (target : EuclideanSpace ℂ (Fin d × Fin d)) (i : Fin d) :
    0 ≤ directStaticChoiTargetWeight d target i := by
  unfold directStaticChoiTargetWeight
  positivity

theorem maximallyProjectiveEnergy_neg
    {I : Type*} [Fintype I]
    {energy : I → ℝ} (hmax : MaximallyProjectiveEnergy energy) :
    MaximallyProjectiveEnergy (fun i => -energy i) := by
  intro k hbalanced henergy
  apply hmax k hbalanced
  have hneg : -(∑ i, (k i : ℝ) * energy i) = 0 := by
    calc
      -(∑ i, (k i : ℝ) * energy i) =
          ∑ i, (k i : ℝ) * (-energy i) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            ring
      _ = 0 := henergy
  linarith

theorem fidelityReplicaCollisionMass_eq_floor_of_maximallyProjective
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (n : ℕ)
    (hmax : MaximallyProjectiveEnergy energy) :
    fidelityReplicaCollisionMass weight energy n =
      fidelityReplicaPermutationFloor weight n := by
  have hrigid : ReplicaRigidAt energy n :=
    (forall_replicaRigidAt_iff_maximallyProjectiveEnergy energy).2 hmax n
  unfold fidelityReplicaCollisionMass
  suffices fidelityReplicaResonanceExcess weight energy n = 0 by rw [this, add_zero]
  unfold fidelityReplicaResonanceExcess
  apply Finset.sum_eq_zero
  intro p hp
  apply Finset.sum_eq_zero
  intro q hq
  by_cases hres : replicaMultiplicityEnergy energy p =
      replicaMultiplicityEnergy energy q
  · have hpq := hrigid p hp q hq hres
    simp [hpq]
  · simp [hres]

theorem multinomial_le_factorial_of_mem_piAntidiag
    {I : Type*} [Fintype I] [DecidableEq I]
    {p : I → ℕ} {n : ℕ}
    (hp : p ∈ Finset.univ.piAntidiag n) :
    Nat.multinomial Finset.univ p ≤ n.factorial := by
  rw [Finset.mem_piAntidiag] at hp
  unfold Nat.multinomial
  rw [hp.1]
  exact Nat.div_le_self _ _

theorem fidelityReplicaPermutationFloor_le_factorial_mul_sum_sq_pow
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight : I → ℝ} (hweight : ∀ i, 0 ≤ weight i) (n : ℕ) :
    fidelityReplicaPermutationFloor weight n ≤
      (n.factorial : ℝ) * (∑ i, weight i ^ 2) ^ n := by
  unfold fidelityReplicaPermutationFloor
  calc
    (∑ p ∈ Finset.univ.piAntidiag n,
        fidelityReplicaMultiplicityWeight weight p p) ≤
      ∑ p ∈ Finset.univ.piAntidiag n,
        (n.factorial : ℝ) * (Nat.multinomial Finset.univ p : ℝ) *
          ∏ i, (weight i ^ 2) ^ p i := by
      apply Finset.sum_le_sum
      intro p hp
      have hmultiNat := multinomial_le_factorial_of_mem_piAntidiag hp
      have hmulti : (Nat.multinomial Finset.univ p : ℝ) ≤ n.factorial := by
        exact_mod_cast hmultiNat
      have hMnonneg : 0 ≤ (Nat.multinomial Finset.univ p : ℝ) := by positivity
      have hPnonneg : 0 ≤ ∏ i, weight i ^ p i :=
        Finset.prod_nonneg fun i hi => pow_nonneg (hweight i) _
      unfold fidelityReplicaMultiplicityWeight
      have hMM :
          (Nat.multinomial Finset.univ p : ℝ) *
              (Nat.multinomial Finset.univ p : ℝ) ≤
            (n.factorial : ℝ) *
              (Nat.multinomial Finset.univ p : ℝ) :=
        mul_le_mul_of_nonneg_right hmulti hMnonneg
      calc
        (Nat.multinomial Finset.univ p : ℝ) *
              (∏ i, weight i ^ p i) *
              (Nat.multinomial Finset.univ p : ℝ) *
                (∏ i, weight i ^ p i) =
            ((Nat.multinomial Finset.univ p : ℝ) *
              (Nat.multinomial Finset.univ p : ℝ)) *
              ((∏ i, weight i ^ p i) * (∏ i, weight i ^ p i)) := by ring
        _ ≤ ((n.factorial : ℝ) *
              (Nat.multinomial Finset.univ p : ℝ)) *
              ((∏ i, weight i ^ p i) * (∏ i, weight i ^ p i)) :=
            mul_le_mul_of_nonneg_right hMM (mul_nonneg hPnonneg hPnonneg)
        _ = (n.factorial : ℝ) *
              (Nat.multinomial Finset.univ p : ℝ) *
                ∏ i, (weight i ^ 2) ^ p i := by
            simp only [pow_two, mul_pow, Finset.prod_mul_distrib]
    _ = (n.factorial : ℝ) *
        ∑ p ∈ Finset.univ.piAntidiag n,
          (Nat.multinomial Finset.univ p : ℝ) *
            ∏ i, (weight i ^ 2) ^ p i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = (n.factorial : ℝ) * (∑ i, weight i ^ 2) ^ n := by
      rw [Finset.sum_pow_eq_sum_piAntidiag]

theorem directStaticChoiTarget_collision_le_factorial_inv_pow
    {d : ℕ} (hd : 0 < d)
    {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1) (n : ℕ) :
    fidelityReplicaCollisionMass
        (directStaticChoiTargetWeight d target) (fun i => -energy i) n ≤
      (n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n := by
  rw [fidelityReplicaCollisionMass_eq_floor_of_maximallyProjective
    (directStaticChoiTargetWeight d target) (fun i => -energy i) n
    (maximallyProjectiveEnergy_neg hmax)]
  exact (fidelityReplicaPermutationFloor_le_factorial_mul_sum_sq_pow
    (directStaticChoiTargetWeight_nonneg target) n).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity)
          (sum_sq_directStaticChoiTargetWeight_le_inv hd htarget) n)
        (by positivity))

theorem replicaMultiplicityEnergy_neg
    {I : Type*} [Fintype I]
    (energy : I → ℝ) (p : I → ℕ) :
    replicaMultiplicityEnergy (fun i => -energy i) p =
      -replicaMultiplicityEnergy energy p := by
  unfold replicaMultiplicityEnergy
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem nonzeroReplicaActionMagnitudes_neg
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) :
    nonzeroReplicaActionMagnitudes (fun i => -energy i) n =
      nonzeroReplicaActionMagnitudes energy n := by
  classical
  unfold nonzeroReplicaActionMagnitudes
  congr 1
  apply Finset.image_congr
  intro pq hpq
  change
    |replicaMultiplicityEnergy (fun i => -energy i) pq.1 -
        replicaMultiplicityEnergy (fun i => -energy i) pq.2| =
      |replicaMultiplicityEnergy energy pq.1 -
        replicaMultiplicityEnergy energy pq.2|
  rw [replicaMultiplicityEnergy_neg, replicaMultiplicityEnergy_neg]
  rw [show -replicaMultiplicityEnergy energy pq.1 -
      -replicaMultiplicityEnergy energy pq.2 =
        -(replicaMultiplicityEnergy energy pq.1 -
          replicaMultiplicityEnergy energy pq.2) by ring,
    abs_neg]

theorem intrinsicReplicaActionResolution_neg
    {I : Type*} [Fintype I] [DecidableEq I]
    (energy : I → ℝ) (n : ℕ) :
    intrinsicReplicaActionResolution (fun i => -energy i) n =
      intrinsicReplicaActionResolution energy n := by
  unfold intrinsicReplicaActionResolution
  simp only [nonzeroReplicaActionMagnitudes_neg]

theorem norm_inner_ge_sqrt_one_sub_sq_of_traceDistance_le
    {I : Type*} [Fintype I]
    (x z : EuclideanSpace ℂ I)
    (hx : ‖x‖ = 1) (hz : ‖z‖ = 1)
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1)
    (hdist : pureStateTraceDistance x z ≤ epsilon) :
    Real.sqrt (1 - epsilon ^ 2) ≤ ‖inner ℂ x z‖ := by
  have hinner : ‖inner ℂ x z‖ ≤ 1 := by
    calc
      ‖inner ℂ x z‖ ≤ ‖x‖ * ‖z‖ := norm_inner_le_norm _ _
      _ = 1 := by rw [hx, hz, one_mul]
  have hdeficit : 0 ≤ 1 - ‖inner ℂ x z‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hinner)
      (by positivity : 0 ≤ 1 + ‖inner ℂ x z‖)]
  have hrootSq :
      (pureStateTraceDistance x z) ^ 2 =
        1 - ‖inner ℂ x z‖ ^ 2 := by
    unfold pureStateTraceDistance
    rw [Real.sq_sqrt hdeficit]
  have hdistNonneg := pureStateTraceDistance_nonneg x z
  have hdistSq :
      (pureStateTraceDistance x z) ^ 2 ≤ epsilon ^ 2 := by
    nlinarith
  have hrad : 0 ≤ 1 - epsilon ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hepsilonOne)
      (by positivity : 0 ≤ 1 + epsilon)]
  have hsq : 1 - epsilon ^ 2 ≤ ‖inner ℂ x z‖ ^ 2 := by
    rw [hrootSq] at hdistSq
    nlinarith
  have hsqrtSq := Real.sq_sqrt hrad
  nlinarith [Real.sqrt_nonneg (1 - epsilon ^ 2),
    norm_nonneg (inner ℂ x z)]

theorem staticChoiTargetCapture_implies_directCoherence
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1)
    {epsilon t : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1)
    (ht : t ∈ staticChoiTargetCaptureSet energy target epsilon) :
    Real.sqrt (1 - epsilon ^ 2) ≤
      ‖twistedFiniteSpectralAmplitude
        (directStaticChoiTargetWeight d target) (fun i => -energy i)
        (directStaticChoiTargetTwist target) t‖ := by
  have hcoherence := norm_inner_ge_sqrt_one_sub_sq_of_traceDistance_le
    (staticSpectralChoiVector d t energy) target
    (staticSpectralChoiVector_norm hd t energy) htarget
    hepsilon hepsilonOne ht
  rw [inner_staticSpectralChoiVector_target_eq_directTwistedAmplitude] at hcoherence
  exact hcoherence

theorem gaussianStaticChoiTargetCapture_subset_directCoherence
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1)
    {epsilon T : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    gaussianStaticChoiTargetCaptureSet energy target T epsilon ⊆
      gaussianTwistedCoherenceCaptureSet
        (directStaticChoiTargetWeight d target) (fun i => -energy i)
        (directStaticChoiTargetTwist target) T
        (Real.sqrt (1 - epsilon ^ 2)) := by
  intro x hx
  exact staticChoiTargetCapture_implies_directCoherence hd htarget
    hepsilon hepsilonOne hx

theorem uniformStaticChoiTargetCapture_subset_directCoherence
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1)
    {epsilon T : ℝ} (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    uniformStaticChoiTargetCaptureSet energy target T epsilon ⊆
      uniformTwistedCoherenceCaptureSet
        (directStaticChoiTargetWeight d target) (fun i => -energy i)
        (directStaticChoiTargetTwist target) T
        (Real.sqrt (1 - epsilon ^ 2)) := by
  intro t ht
  exact ⟨ht.2, staticChoiTargetCapture_implies_directCoherence hd htarget
    hepsilon hepsilonOne ht.1⟩

theorem gaussian_directStaticChoiTargetShortcut_actionLaw
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real
          (gaussianStaticChoiTargetCaptureSet energy target T epsilon) ≤
      (n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
        Real.exp (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2) := by
  let weight := directStaticChoiTargetWeight d target
  let negEnergy : Fin d → ℝ := fun i => -energy i
  let twist := directStaticChoiTargetTwist target
  let threshold := Real.sqrt (1 - epsilon ^ 2)
  have hsubset :
      gaussianStaticChoiTargetCaptureSet energy target T epsilon ⊆
        gaussianTwistedCoherenceCaptureSet weight negEnergy twist T threshold :=
    gaussianStaticChoiTargetCapture_subset_directCoherence hd htarget
      hepsilon hepsilonOne
  have hpow : 0 ≤ threshold ^ (2 * n) := pow_nonneg (Real.sqrt_nonneg _) _
  calc
    threshold ^ (2 * n) *
        (gaussianReal 0 1).real
          (gaussianStaticChoiTargetCaptureSet energy target T epsilon) ≤
      threshold ^ (2 * n) *
        (gaussianReal 0 1).real
          (gaussianTwistedCoherenceCaptureSet weight negEnergy twist T threshold) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsubset) hpow
    _ ≤ fidelityReplicaCollisionMass weight negEnergy n +
        Real.exp (-((T * intrinsicReplicaActionResolution negEnergy n) ^ 2) / 2) := by
      apply threshold_pow_mul_gaussianTwistedCoherenceCaptureSet_measureReal_le_of_sum_le_one
        (directStaticChoiTargetWeight_nonneg target)
        (sum_directStaticChoiTargetWeight_le_one hd htarget)
        (norm_directStaticChoiTargetTwist target) n hn hT
        (intrinsicReplicaActionResolution_pos negEnergy n)
        (Real.sqrt_nonneg _)
      intro p hp q hq hne
      exact intrinsicReplicaActionResolution_le negEnergy n hp hq hne
    _ ≤ (n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
        Real.exp (-((T * intrinsicReplicaActionResolution negEnergy n) ^ 2) / 2) := by
      exact add_le_add
        (directStaticChoiTarget_collision_le_factorial_inv_pow
          hd hmax htarget n) (le_refl _)
    _ = (n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
        Real.exp (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2) := by
      rw [intrinsicReplicaActionResolution_neg]

theorem uniform_directStaticChoiTargetShortcut_actionLaw
    {d : ℕ} (hd : 0 < d) {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    {target : EuclideanSpace ℂ (Fin d × Fin d)}
    (htarget : ‖target‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        volume.real
          (uniformStaticChoiTargetCaptureSet energy target T epsilon) ≤
      2 * T * ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
        min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  let weight := directStaticChoiTargetWeight d target
  let negEnergy : Fin d → ℝ := fun i => -energy i
  let twist := directStaticChoiTargetTwist target
  let threshold := Real.sqrt (1 - epsilon ^ 2)
  have hsubset :
      uniformStaticChoiTargetCaptureSet energy target T epsilon ⊆
        uniformTwistedCoherenceCaptureSet weight negEnergy twist T threshold :=
    uniformStaticChoiTargetCapture_subset_directCoherence hd htarget
      hepsilon hepsilonOne
  have hwindow :
      uniformTwistedCoherenceCaptureSet weight negEnergy twist T threshold ⊆
        Set.Ioc (-T) T := fun t ht => ht.1
  have hfinite :
      volume (uniformTwistedCoherenceCaptureSet weight negEnergy twist T threshold) ≠ ∞ :=
    ne_of_lt ((measure_mono hwindow).trans_lt measure_Ioc_lt_top)
  have hpow : 0 ≤ threshold ^ (2 * n) := pow_nonneg (Real.sqrt_nonneg _) _
  calc
    threshold ^ (2 * n) *
        volume.real
          (uniformStaticChoiTargetCaptureSet energy target T epsilon) ≤
      threshold ^ (2 * n) *
        volume.real
          (uniformTwistedCoherenceCaptureSet weight negEnergy twist T threshold) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsubset hfinite) hpow
    _ ≤ 2 * T * (fidelityReplicaCollisionMass weight negEnergy n +
        min 1 (T * intrinsicReplicaActionResolution negEnergy n)⁻¹) := by
      apply threshold_pow_mul_uniformTwistedCoherenceCaptureSet_measureReal_le_of_sum_le_one
        (directStaticChoiTargetWeight_nonneg target)
        (sum_directStaticChoiTargetWeight_le_one hd htarget)
        (norm_directStaticChoiTargetTwist target) n hn hT
        (intrinsicReplicaActionResolution_pos negEnergy n)
        (Real.sqrt_nonneg _)
      intro p hp q hq hne
      exact intrinsicReplicaActionResolution_le negEnergy n hp hq hne
    _ ≤ 2 * T * ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
        min 1 (T * intrinsicReplicaActionResolution negEnergy n)⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hT.le)
      exact add_le_add
        (directStaticChoiTarget_collision_le_factorial_inv_pow
          hd hmax htarget n) (le_refl _)
    _ = 2 * T * ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
        min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
      rw [intrinsicReplicaActionResolution_neg]

/-- Finite target dictionary chosen after observing Gaussian time. -/
theorem gaussian_directAdaptiveStaticChoiTargetShortcut_actionLaw
    {d : ℕ} (hd : 0 < d)
    {W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real
          (⋃ w : W, gaussianStaticChoiTargetCaptureSet
            energy (target w) T epsilon) ≤
      (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          Real.exp (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  have hpow : 0 ≤ Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) :=
    pow_nonneg (Real.sqrt_nonneg _) _
  calc
    Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real
          (⋃ w : W, gaussianStaticChoiTargetCaptureSet
            energy (target w) T epsilon) ≤
      Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        ∑ w : W, (gaussianReal 0 1).real
          (gaussianStaticChoiTargetCaptureSet energy (target w) T epsilon) :=
      mul_le_mul_of_nonneg_left (measureReal_iUnion_fintype_le _) hpow
    _ = ∑ w : W, Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real
          (gaussianStaticChoiTargetCaptureSet energy (target w) T epsilon) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _w : W, ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          Real.exp (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
      apply Finset.sum_le_sum
      intro w hw
      exact gaussian_directStaticChoiTargetShortcut_actionLaw
        hd hmax (htarget w) n hn hT hepsilon hepsilonOne
    _ = (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          Real.exp (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
      simp
      ring

/-- Finite target dictionary chosen after observing uniform-window time. -/
theorem uniform_directAdaptiveStaticChoiTargetShortcut_actionLaw
    {d : ℕ} (hd : 0 < d)
    {W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        volume.real
          (⋃ w : W, uniformStaticChoiTargetCaptureSet
            energy (target w) T epsilon) ≤
      2 * T * (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  have hpow : 0 ≤ Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) :=
    pow_nonneg (Real.sqrt_nonneg _) _
  calc
    Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        volume.real
          (⋃ w : W, uniformStaticChoiTargetCaptureSet
            energy (target w) T epsilon) ≤
      Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        ∑ w : W, volume.real
          (uniformStaticChoiTargetCaptureSet energy (target w) T epsilon) :=
      mul_le_mul_of_nonneg_left (measureReal_iUnion_fintype_le _) hpow
    _ = ∑ w : W, Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) *
        volume.real
          (uniformStaticChoiTargetCaptureSet energy (target w) T epsilon) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ _w : W, 2 * T *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
      apply Finset.sum_le_sum
      intro w hw
      exact uniform_directStaticChoiTargetShortcut_actionLaw
        hd hmax (htarget w) n hn hT hepsilon hepsilonOne
    _ = 2 * T * (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
      simp
      ring

theorem sqrt_one_sub_sq_pow_two_mul
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (hepsilonOne : epsilon ≤ 1)
    (n : ℕ) :
    Real.sqrt (1 - epsilon ^ 2) ^ (2 * n) =
      (1 - epsilon ^ 2) ^ n := by
  have hrad : 0 ≤ 1 - epsilon ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hepsilonOne)
      (by positivity : 0 ≤ 1 + epsilon)]
  rw [two_mul, pow_add, ← mul_pow, Real.mul_self_sqrt hrad]

/-- Arbitrary adaptive target selector resolved by one finite metric net.
The selector and target class need no measurable structure. -/
theorem gaussian_directAdaptiveNetStaticChoiShortcut_actionLaw
    {d : ℕ} (hd : 0 < d)
    {C W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (selectedTarget : C → EuclideanSpace ℂ (Fin d × Fin d))
    (hselectedTarget : ∀ c, ‖selectedTarget c‖ = 1)
    (netTarget : W → EuclideanSpace ℂ (Fin d × Fin d))
    (hnetTarget : ∀ w, ‖netTarget w‖ = 1)
    (netIndex : C → W) (selector : ℝ → C) (A : Set ℝ)
    (n : ℕ) (hn : 0 < n) {T epsilon eta : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon) (heta : 0 ≤ eta)
    (hradius : epsilon + eta ≤ 1)
    (hnet : ∀ c, pureStateTraceDistance
      (selectedTarget c) (netTarget (netIndex c)) ≤ eta)
    (hsuccess : ∀ x ∈ A, pureStateTraceDistance
      (staticSpectralChoiVector d (T * x) energy)
      (selectedTarget (selector x)) ≤ epsilon) :
    Real.sqrt (1 - (epsilon + eta) ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real A ≤
      (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          Real.exp (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  have hsubset : A ⊆
      ⋃ w : W, gaussianStaticChoiTargetCaptureSet
        energy (netTarget w) T (epsilon + eta) := by
    intro x hx
    simp only [Set.mem_iUnion]
    refine ⟨netIndex (selector x), ?_⟩
    apply pureStateTraceDistance_triangle
      (staticSpectralChoiVector d (T * x) energy)
      (selectedTarget (selector x))
      (netTarget (netIndex (selector x)))
      (staticSpectralChoiVector_norm hd _ energy)
      (hselectedTarget _)
      (hnetTarget _)
      |>.trans
    exact add_le_add (hsuccess x hx) (hnet _)
  have hpow : 0 ≤ Real.sqrt (1 - (epsilon + eta) ^ 2) ^ (2 * n) :=
    pow_nonneg (Real.sqrt_nonneg _) _
  calc
    Real.sqrt (1 - (epsilon + eta) ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real A ≤
      Real.sqrt (1 - (epsilon + eta) ^ 2) ^ (2 * n) *
        (gaussianReal 0 1).real
          (⋃ w : W, gaussianStaticChoiTargetCaptureSet
            energy (netTarget w) T (epsilon + eta)) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsubset) hpow
    _ ≤ _ := gaussian_directAdaptiveStaticChoiTargetShortcut_actionLaw
      hd hmax netTarget hnetTarget n hn hT (add_nonneg hepsilon heta) hradius

/-- Uniform-window arbitrary-selector counterpart of the adaptive-net law. -/
theorem uniform_directAdaptiveNetStaticChoiShortcut_actionLaw
    {d : ℕ} (hd : 0 < d)
    {C W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (selectedTarget : C → EuclideanSpace ℂ (Fin d × Fin d))
    (hselectedTarget : ∀ c, ‖selectedTarget c‖ = 1)
    (netTarget : W → EuclideanSpace ℂ (Fin d × Fin d))
    (hnetTarget : ∀ w, ‖netTarget w‖ = 1)
    (netIndex : C → W) (selector : ℝ → C) (A : Set ℝ)
    (n : ℕ) (hn : 0 < n) {T epsilon eta : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon) (heta : 0 ≤ eta)
    (hradius : epsilon + eta ≤ 1)
    (hwindow : A ⊆ Set.Ioc (-T) T)
    (hnet : ∀ c, pureStateTraceDistance
      (selectedTarget c) (netTarget (netIndex c)) ≤ eta)
    (hsuccess : ∀ t ∈ A, pureStateTraceDistance
      (staticSpectralChoiVector d t energy)
      (selectedTarget (selector t)) ≤ epsilon) :
    Real.sqrt (1 - (epsilon + eta) ^ 2) ^ (2 * n) *
        volume.real A ≤
      2 * T * (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  have hsubset : A ⊆
      ⋃ w : W, uniformStaticChoiTargetCaptureSet
        energy (netTarget w) T (epsilon + eta) := by
    intro t ht
    simp only [Set.mem_iUnion]
    refine ⟨netIndex (selector t), ?_⟩
    refine ⟨?_, hwindow ht⟩
    apply pureStateTraceDistance_triangle
      (staticSpectralChoiVector d t energy)
      (selectedTarget (selector t))
      (netTarget (netIndex (selector t)))
      (staticSpectralChoiVector_norm hd _ energy)
      (hselectedTarget _)
      (hnetTarget _)
      |>.trans
    exact add_le_add (hsuccess t ht) (hnet _)
  have hUnionWindow :
      (⋃ w : W, uniformStaticChoiTargetCaptureSet
        energy (netTarget w) T (epsilon + eta)) ⊆ Set.Ioc (-T) T := by
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨w, hw⟩ := ht
    exact hw.2
  have hfinite :
      volume
        (⋃ w : W, uniformStaticChoiTargetCaptureSet
          energy (netTarget w) T (epsilon + eta)) ≠ ∞ :=
    ne_of_lt ((measure_mono hUnionWindow).trans_lt measure_Ioc_lt_top)
  have hpow : 0 ≤ Real.sqrt (1 - (epsilon + eta) ^ 2) ^ (2 * n) :=
    pow_nonneg (Real.sqrt_nonneg _) _
  calc
    Real.sqrt (1 - (epsilon + eta) ^ 2) ^ (2 * n) *
        volume.real A ≤
      Real.sqrt (1 - (epsilon + eta) ^ 2) ^ (2 * n) *
        volume.real
          (⋃ w : W, uniformStaticChoiTargetCaptureSet
            energy (netTarget w) T (epsilon + eta)) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hsubset hfinite) hpow
    _ ≤ _ := uniform_directAdaptiveStaticChoiTargetShortcut_actionLaw
      hd hmax netTarget hnetTarget n hn hT (add_nonneg hepsilon heta) hradius

theorem gaussian_directAdaptiveStaticChoiTargetShortcut_probability_le
    {d : ℕ} (hd : 0 < d)
    {W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    (1 - epsilon ^ 2) ^ n *
        (gaussianReal 0 1).real
          (⋃ w : W, gaussianStaticChoiTargetCaptureSet
            energy (target w) T epsilon) ≤
      (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          Real.exp (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  rw [← sqrt_one_sub_sq_pow_two_mul hepsilon hepsilonOne n]
  exact gaussian_directAdaptiveStaticChoiTargetShortcut_actionLaw
    hd hmax target htarget n hn hT hepsilon hepsilonOne

theorem uniform_directAdaptiveStaticChoiTargetShortcut_probability_le
    {d : ℕ} (hd : 0 < d)
    {W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (target : W → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    (1 - epsilon ^ 2) ^ n *
        (volume.real
          (⋃ w : W, uniformStaticChoiTargetCaptureSet
            energy (target w) T epsilon) / (2 * T)) ≤
      (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  have hmain := uniform_directAdaptiveStaticChoiTargetShortcut_actionLaw
    hd hmax target htarget n hn hT hepsilon hepsilonOne
  rw [sqrt_one_sub_sq_pow_two_mul hepsilon hepsilonOne n] at hmain
  have h2T : 0 < 2 * T := mul_pos (by norm_num) hT
  rw [← mul_div_assoc]
  apply (div_le_iff₀ h2T).2
  calc
    (1 - epsilon ^ 2) ^ n *
        volume.real
          (⋃ w : W, uniformStaticChoiTargetCaptureSet
            energy (target w) T epsilon) ≤
      2 * T * (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) := hmain
    _ = (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) *
            (2 * T) := by ring

theorem gaussian_directAdaptiveNetStaticChoiShortcut_probability_le
    {d : ℕ} (hd : 0 < d)
    {C W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (selectedTarget : C → EuclideanSpace ℂ (Fin d × Fin d))
    (hselectedTarget : ∀ c, ‖selectedTarget c‖ = 1)
    (netTarget : W → EuclideanSpace ℂ (Fin d × Fin d))
    (hnetTarget : ∀ w, ‖netTarget w‖ = 1)
    (netIndex : C → W) (selector : ℝ → C) (A : Set ℝ)
    (n : ℕ) (hn : 0 < n) {T epsilon eta : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon) (heta : 0 ≤ eta)
    (hradius : epsilon + eta ≤ 1)
    (hnet : ∀ c, pureStateTraceDistance
      (selectedTarget c) (netTarget (netIndex c)) ≤ eta)
    (hsuccess : ∀ x ∈ A, pureStateTraceDistance
      (staticSpectralChoiVector d (T * x) energy)
      (selectedTarget (selector x)) ≤ epsilon) :
    (1 - (epsilon + eta) ^ 2) ^ n * (gaussianReal 0 1).real A ≤
      (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          Real.exp (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  rw [← sqrt_one_sub_sq_pow_two_mul (add_nonneg hepsilon heta) hradius n]
  exact gaussian_directAdaptiveNetStaticChoiShortcut_actionLaw
    hd hmax selectedTarget hselectedTarget netTarget hnetTarget
    netIndex selector A n hn hT hepsilon heta hradius hnet hsuccess

theorem uniform_directAdaptiveNetStaticChoiShortcut_probability_le
    {d : ℕ} (hd : 0 < d)
    {C W : Type*} [Fintype W] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (selectedTarget : C → EuclideanSpace ℂ (Fin d × Fin d))
    (hselectedTarget : ∀ c, ‖selectedTarget c‖ = 1)
    (netTarget : W → EuclideanSpace ℂ (Fin d × Fin d))
    (hnetTarget : ∀ w, ‖netTarget w‖ = 1)
    (netIndex : C → W) (selector : ℝ → C) (A : Set ℝ)
    (n : ℕ) (hn : 0 < n) {T epsilon eta : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon) (heta : 0 ≤ eta)
    (hradius : epsilon + eta ≤ 1)
    (hwindow : A ⊆ Set.Ioc (-T) T)
    (hnet : ∀ c, pureStateTraceDistance
      (selectedTarget c) (netTarget (netIndex c)) ≤ eta)
    (hsuccess : ∀ t ∈ A, pureStateTraceDistance
      (staticSpectralChoiVector d t energy)
      (selectedTarget (selector t)) ≤ epsilon) :
    (1 - (epsilon + eta) ^ 2) ^ n * (volume.real A / (2 * T)) ≤
      (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  have hmain := uniform_directAdaptiveNetStaticChoiShortcut_actionLaw
    hd hmax selectedTarget hselectedTarget netTarget hnetTarget
    netIndex selector A n hn hT hepsilon heta hradius hwindow hnet hsuccess
  rw [sqrt_one_sub_sq_pow_two_mul (add_nonneg hepsilon heta) hradius n] at hmain
  have h2T : 0 < 2 * T := mul_pos (by norm_num) hT
  rw [← mul_div_assoc]
  apply (div_le_iff₀ h2T).2
  calc
    (1 - (epsilon + eta) ^ 2) ^ n * volume.real A ≤
      2 * T * (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) := hmain
    _ = (Fintype.card W : ℝ) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) *
            (2 * T) := by ring

/-- Gaussian direct-target shortcut law for all padded circuit words. -/
theorem gaussian_directAdaptivePaddedCircuitShortcut_probability_le
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    (1 - epsilon ^ 2) ^ n *
        (gaussianReal 0 1).real
          (⋃ w : PaddedCircuitWord gate s,
            gaussianStaticChoiTargetCaptureSet
              energy (target w) T epsilon) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          Real.exp (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  simpa only [card_paddedCircuitWord, Nat.cast_pow] using
    gaussian_directAdaptiveStaticChoiTargetShortcut_probability_le
      hd hmax target htarget n hn hT hepsilon hepsilonOne

/-- Uniform-window direct-target shortcut law for all padded circuit words. -/
theorem uniform_directAdaptivePaddedCircuitShortcut_probability_le
    {d : ℕ} (hd : 0 < d)
    {gate : Type*} [Fintype gate] {energy : Fin d → ℝ}
    (hmax : MaximallyProjectiveEnergy energy)
    (s : ℕ)
    (target : PaddedCircuitWord gate s →
      EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ w, ‖target w‖ = 1)
    (n : ℕ) (hn : 0 < n) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 ≤ epsilon)
    (hepsilonOne : epsilon ≤ 1) :
    (1 - epsilon ^ 2) ^ n *
        (volume.real
          (⋃ w : PaddedCircuitWord gate s,
            uniformStaticChoiTargetCaptureSet
              energy (target w) T epsilon) / (2 * T)) ≤
      (Fintype.card gate : ℝ) ^ (s + 1) *
        ((n.factorial : ℝ) * (d : ℝ)⁻¹ ^ n +
          min 1 (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  simpa only [card_paddedCircuitWord, Nat.cast_pow] using
    uniform_directAdaptiveStaticChoiTargetShortcut_probability_le
      hd hmax target htarget n hn hT hepsilon hepsilonOne

end RHTower
