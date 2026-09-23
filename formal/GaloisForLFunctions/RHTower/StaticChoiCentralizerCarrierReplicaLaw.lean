import GaloisForLFunctions.RHTower.StaticChoiOptimalDesignWeightedCrowdingFirstReturnLaw
import GaloisForLFunctions.HTGeometry.FiniteSpectralPhaseActionLaw
import GaloisForLFunctions.RHTower.AutonomousReturnReflection
import GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

open scoped BigOperators Matrix ComplexConjugate
open Set Matrix

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open RHTower
open GaloisForLFunctions.RHTower

noncomputable section

/-- Strict near-action mass cannot exceed the full mass of the replica subprobability law. -/
theorem fidelityReplicaNearActionMass_le_totalMass
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} (hweight : ∀ i, 0 ≤ weight i)
    (r : ℕ) (δ : ℝ) :
    fidelityReplicaNearActionMass weight energy r δ ≤
      (∑ i, weight i) ^ (2 * r) := by
  classical
  rw [fidelityReplicaNearActionMass_eq_finset]
  calc
    (∑ p ∈ Finset.univ.piAntidiag r,
        ∑ q ∈ Finset.univ.piAntidiag r,
          if 0 < |replicaMultiplicityEnergy energy p -
              replicaMultiplicityEnergy energy q| ∧
            |replicaMultiplicityEnergy energy p -
              replicaMultiplicityEnergy energy q| < δ
          then fidelityReplicaMultiplicityWeight weight p q
          else 0) ≤
        ∑ p ∈ Finset.univ.piAntidiag r,
          ∑ q ∈ Finset.univ.piAntidiag r,
            fidelityReplicaMultiplicityWeight weight p q := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      split_ifs
      · exact le_rfl
      · exact fidelityReplicaMultiplicityWeight_nonneg hweight p q
    _ = (∑ i, weight i) ^ (2 * r) :=
      sum_fidelityReplicaMultiplicityWeight_eq_sum_pow weight r

/-- Exact one-copy mass of a Choi target in the static spectral centralizer. -/
def directStaticChoiCentralizerMass
    {d : ℕ} (target : EuclideanSpace ℂ (Fin d × Fin d)) : ℝ :=
  ∑ i, directStaticChoiTargetWeight d target i

theorem directStaticChoiCentralizerMass_nonneg
    {d : ℕ} (target : EuclideanSpace ℂ (Fin d × Fin d)) :
    0 ≤ directStaticChoiCentralizerMass target := by
  unfold directStaticChoiCentralizerMass
  exact Finset.sum_nonneg fun i _ => directStaticChoiTargetWeight_nonneg target i

theorem directStaticChoiCentralizerMass_le_one
    {d : ℕ} (hd : 0 < d)
    {target : EuclideanSpace ℂ (Fin d × Fin d)} (htarget : ‖target‖ = 1) :
    directStaticChoiCentralizerMass target ≤ 1 :=
  sum_directStaticChoiTargetWeight_le_one hd htarget

/-- Growing replicas exponentially suppress every target outside the high-centralizer carrier. -/
theorem directStaticChoiTargetNearActionMass_le_centralizerMass_pow
    {d : ℕ} (target : EuclideanSpace ℂ (Fin d × Fin d))
    (energy : Fin d → ℝ) (r : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass target energy r δ ≤
      directStaticChoiCentralizerMass target ^ (2 * r) := by
  exact fidelityReplicaNearActionMass_le_totalMass
    (directStaticChoiTargetWeight_nonneg target) r δ

/-- Design-weighted near-action mass splits into an exponentially small transverse term and the
literal design mass of the high-centralizer carrier. -/
theorem weighted_directStaticChoiNearActionMass_le_transverse_add_carrier
    {d : ℕ} (hd : 0 < d)
    {C : Type*} [Fintype C]
    (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ = 1)
    (energy : Fin d → ℝ) (r : ℕ) (δ β : ℝ)
    (hβ0 : 0 ≤ β)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C) :
    (∑ c, w c * directStaticChoiTargetNearActionMass (target c) energy r δ) ≤
      β ^ (2 * r) +
        ∑ c, if β < directStaticChoiCentralizerMass (target c) then w c else 0 := by
  have hterm : ∀ c : C,
      w c * directStaticChoiTargetNearActionMass (target c) energy r δ ≤
        w c * β ^ (2 * r) +
          (if β < directStaticChoiCentralizerMass (target c) then w c else 0) := by
    intro c
    have hwc : 0 ≤ w c := hw.1 c
    have hS0 := directStaticChoiCentralizerMass_nonneg (target c)
    have hS1 := directStaticChoiCentralizerMass_le_one hd (htarget c)
    have hnear := directStaticChoiTargetNearActionMass_le_centralizerMass_pow
      (target c) energy r δ
    by_cases hc : β < directStaticChoiCentralizerMass (target c)
    · rw [if_pos hc]
      have hpow : directStaticChoiCentralizerMass (target c) ^ (2 * r) ≤ 1 :=
        pow_le_one₀ hS0 hS1
      have hnearOne := hnear.trans hpow
      have hβpow : 0 ≤ β ^ (2 * r) := pow_nonneg hβ0 _
      nlinarith [mul_le_mul_of_nonneg_left hnearOne hwc]
    · rw [if_neg hc, add_zero]
      have hSβ : directStaticChoiCentralizerMass (target c) ≤ β := le_of_not_gt hc
      have hpow := pow_le_pow_left₀ hS0 hSβ (2 * r)
      exact mul_le_mul_of_nonneg_left (hnear.trans hpow) hwc
  calc
    (∑ c, w c * directStaticChoiTargetNearActionMass (target c) energy r δ) ≤
        ∑ c, (w c * β ^ (2 * r) +
          if β < directStaticChoiCentralizerMass (target c) then w c else 0) :=
      Finset.sum_le_sum fun c _ => hterm c
    _ = β ^ (2 * r) +
        ∑ c, if β < directStaticChoiCentralizerMass (target c) then w c else 0 := by
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hw.2, one_mul]

/-- Failure of the transverse replica bound quantitatively forces optimal-design weight into the
high-centralizer carrier. -/
theorem carrierWeight_gt_of_weightedNearActionMass_gt
    {d : ℕ} (hd : 0 < d)
    {C : Type*} [Fintype C]
    (target : C → EuclideanSpace ℂ (Fin d × Fin d))
    (htarget : ∀ c, ‖target c‖ = 1)
    (energy : Fin d → ℝ) (r : ℕ) (δ β κ : ℝ)
    (hβ0 : 0 ≤ β)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C)
    (hbad : β ^ (2 * r) + κ <
      ∑ c, w c * directStaticChoiTargetNearActionMass (target c) energy r δ) :
    κ < ∑ c, if β < directStaticChoiCentralizerMass (target c) then w c else 0 := by
  have hsplit := weighted_directStaticChoiNearActionMass_le_transverse_add_carrier
    hd target htarget energy r δ β hβ0 w hw
  linarith

/-! Exact geometric meaning of the high-centralizer carrier for unitary Choi targets. -/

noncomputable def unitaryRadialDiagonalMatrix
    {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => phaseNormalize 1 (W i i)

theorem unitaryRadialDiagonalMatrix_mem_unitary
    {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) :
    unitaryRadialDiagonalMatrix W ∈ Matrix.unitaryGroup (Fin d) ℂ := by
  apply mem_unitaryGroup_diagonal_general
  intro i
  exact norm_phaseNormalize_finiteSpectralPhaseActionLaw (by norm_num)

def unitaryDiagonalCentralizerMass
    {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (d : ℝ)⁻¹ * ∑ i, ‖W i i‖

/-- The target-vector centralizer mass specializes exactly to normalized diagonal mass for a
unitary Choi vector. -/
theorem directStaticChoiCentralizerMass_choiVector_eq
    {d : ℕ} (hd : 0 < d) (W : Matrix (Fin d) (Fin d) ℂ) :
    directStaticChoiCentralizerMass (choiVector W) =
      unitaryDiagonalCentralizerMass W := by
  classical
  unfold directStaticChoiCentralizerMass directStaticChoiTargetWeight
  unfold unitaryDiagonalCentralizerMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change (Real.sqrt (d : ℝ))⁻¹ *
      ‖W i i / (Real.sqrt (Fintype.card (Fin d)) : ℂ)‖ =
    (d : ℝ)⁻¹ * ‖W i i‖
  simp only [Fintype.card_fin]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hsqrt : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = d :=
    Real.mul_self_sqrt hdR.le
  field_simp [Real.sqrt_ne_zero'.mpr hdR]
  ring_nf at hsqrt ⊢
  calc
    ‖W i i‖ * (d : ℝ) = ‖W i i‖ * Real.sqrt (d : ℝ) ^ (2 : ℕ) :=
      congrArg (fun x : ℝ => ‖W i i‖ * x) hsqrt.symm
    _ = Real.sqrt (d : ℝ) ^ (2 : ℕ) * ‖W i i‖ := mul_comm _ _

theorem trace_radialDiagonal_conjTranspose_mul
    {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) :
    Matrix.trace ((unitaryRadialDiagonalMatrix W)ᴴ * W) =
      ((∑ i, ‖W i i‖ : ℝ) : ℂ) := by
  classical
  rw [Matrix.trace]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  change ((unitaryRadialDiagonalMatrix W)ᴴ * W) i i = (‖W i i‖ : ℂ)
  rw [unitaryRadialDiagonalMatrix, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul]
  simpa [Pi.star_apply] using star_phaseNormalize_one_mul (W i i)

/-- A unitary target's centralizer mass is exactly its Choi fidelity with the radial diagonal
centralizer phase. -/
theorem choiDist_radialDiagonal_exact
    {d : ℕ} (hd : 0 < d) (W : Matrix (Fin d) (Fin d) ℂ) :
    choiDist (unitaryRadialDiagonalMatrix W) W =
      Real.sqrt (1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ)) := by
  rw [choiDist_eq (by simpa using hd)]
  rw [trace_radialDiagonal_conjTranspose_mul]
  have hsum : 0 ≤ ∑ i : Fin d, ‖W i i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hsum]
  simp only [Fintype.card_fin]
  congr 2
  unfold unitaryDiagonalCentralizerMass
  field_simp [Nat.cast_ne_zero.mpr hd.ne']

theorem unitaryDiagonalCentralizerMass_nonneg
    {d : ℕ} (W : Matrix (Fin d) (Fin d) ℂ) :
    0 ≤ unitaryDiagonalCentralizerMass W := by
  unfold unitaryDiagonalCentralizerMass
  positivity

theorem unitaryDiagonalCentralizerMass_le_one
    {d : ℕ} (hd : 0 < d) {W : Matrix (Fin d) (Fin d) ℂ}
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    unitaryDiagonalCentralizerMass W ≤ 1 := by
  have hsum : (∑ i : Fin d, ‖W i i‖) ≤ (d : ℝ) := by
    calc
      (∑ i : Fin d, ‖W i i‖) ≤ ∑ _i : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => entry_norm_bound_of_unitary hW i i
      _ = (d : ℝ) := by simp
  unfold unitaryDiagonalCentralizerMass
  rw [inv_mul_le_one₀ (by exact_mod_cast hd)]
  exact hsum

/-- High centralizer mass places a circuit target inside an explicit projective Choi tube around
an exact spectral-centralizer phase. -/
theorem choiDist_radialDiagonal_lt_of_mass_gt
    {d : ℕ} (hd : 0 < d) (W : Matrix (Fin d) (Fin d) ℂ)
    (hW : W ∈ Matrix.unitaryGroup (Fin d) ℂ)
    {β : ℝ} (hβ0 : 0 ≤ β)
    (hmass : β < unitaryDiagonalCentralizerMass W) :
    choiDist (unitaryRadialDiagonalMatrix W) W <
      Real.sqrt (1 - β ^ (2 : ℕ)) := by
  rw [choiDist_radialDiagonal_exact hd]
  have hmass0 := unitaryDiagonalCentralizerMass_nonneg W
  have hmass1 := unitaryDiagonalCentralizerMass_le_one hd hW
  have hsquare : β ^ (2 : ℕ) < unitaryDiagonalCentralizerMass W ^ (2 : ℕ) := by
    simpa [pow_two] using
      (mul_self_lt_mul_self_iff hβ0 hmass0).mp hmass
  have hrad : 0 ≤ 1 - unitaryDiagonalCentralizerMass W ^ (2 : ℕ) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmass1)
      (add_nonneg (by norm_num : (0 : ℝ) ≤ 1) hmass0)]
  exact Real.sqrt_lt_sqrt hrad (by linarith)

/-- For a matrix Choi target, the replica near-action mass is controlled by the normalized
diagonal mass of that matrix in the Hamiltonian eigenbasis. -/
theorem directStaticChoiTargetNearActionMass_choiVector_le
    {d : ℕ} (hd : 0 < d) (W : Matrix (Fin d) (Fin d) ℂ)
    (energy : Fin d → ℝ) (r : ℕ) (δ : ℝ) :
    directStaticChoiTargetNearActionMass (choiVector W) energy r δ ≤
      unitaryDiagonalCentralizerMass W ^ (2 * r) := by
  rw [← directStaticChoiCentralizerMass_choiVector_eq hd W]
  exact directStaticChoiTargetNearActionMass_le_centralizerMass_pow
    (choiVector W) energy r δ

/-- **Geometric replica-carrier decomposition.** For a finite unitary circuit dictionary, every
weighted direct-target near-action mass splits into an exponentially suppressed transverse term
and literal design weight inside a Choi tube around exact diagonal spectral-centralizer phases. -/
theorem weighted_unitaryChoiNearActionMass_le_transverse_add_centralizerTube
    {d : ℕ} (hd : 0 < d)
    {C : Type*} [Fintype C]
    (W : C → Matrix (Fin d) (Fin d) ℂ)
    (hW : ∀ c, W c ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (energy : Fin d → ℝ) (r : ℕ) (δ β : ℝ)
    (hβ0 : 0 ≤ β)
    (w : C → ℝ) (hw : w ∈ stdSimplex ℝ C) :
    (∑ c, w c * directStaticChoiTargetNearActionMass
        (choiVector (W c)) energy r δ) ≤
      β ^ (2 * r) +
        ∑ c, if choiDist (unitaryRadialDiagonalMatrix (W c)) (W c) <
            Real.sqrt (1 - β ^ (2 : ℕ)) then w c else 0 := by
  have htarget : ∀ c, ‖choiVector (W c)‖ = 1 := by
    intro c
    apply norm_choiVector_eq_one (by simpa using hd)
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp (hW c))
  have hsplit := weighted_directStaticChoiNearActionMass_le_transverse_add_carrier
    hd (fun c => choiVector (W c)) htarget energy r δ β hβ0 w hw
  calc
    _ ≤ β ^ (2 * r) +
        ∑ c, if β < directStaticChoiCentralizerMass (choiVector (W c))
          then w c else 0 := hsplit
    _ ≤ β ^ (2 * r) +
        ∑ c, if choiDist (unitaryRadialDiagonalMatrix (W c)) (W c) <
            Real.sqrt (1 - β ^ (2 : ℕ)) then w c else 0 := by
      gcongr
      rw [directStaticChoiCentralizerMass_choiVector_eq hd (W c)]
      by_cases hc : β < unitaryDiagonalCentralizerMass (W c)
      · rw [if_pos hc, if_pos]
        exact choiDist_radialDiagonal_lt_of_mass_gt hd (W c) (hW c) hβ0 hc
      · rw [if_neg hc]
        split_ifs
        · exact hw.1 c
        · exact le_rfl

/-- **Centralizer-tube canonical first-return law.** The opaque weighted near-action term in the
canonical determinant-design theorem is replaced by an exponentially small replica term plus the
literal optimal-design weight of circuits lying near exact spectral-centralizer phases. -/
theorem no_forward_unitaryChoiCircuitReturn_of_canonicalCentralizerTubeBudget
    {d : ℕ} (hd : 0 < d)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    {energy : Fin d → ℝ} (hmax : MaximallyProjectiveEnergy energy)
    (W : C → Matrix (Fin d) (Fin d) ℂ)
    (hW : ∀ c, W c ∈ Matrix.unitaryGroup (Fin d) ℂ)
    {r : ℕ} {T δ epsn epsw β : ℝ}
    (hTpos : 0 < T) (hδ : 0 < δ)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hepswOne : epsw < 1)
    (hT : epsw / staticChoiSpeed energy ≤ T)
    (hβ0 : 0 ≤ β)
    (hbudget :
      (Module.finrank ℂ
          (replicaTargetSpan r (fun c => (choiVector (W c)).ofLp)) : ℝ) *
        ((r.factorial : ℝ) * (d : ℝ)⁻¹ ^ r +
          β ^ (2 * r) +
          (∑ c, if choiDist (unitaryRadialDiagonalMatrix (W c)) (W c) <
              Real.sqrt (1 - β ^ (2 : ℕ)) then
            staticChoiTargetOptimalDesignWeight r (fun c => choiVector (W c))
              (fun c => norm_choiVector_eq_one (by simpa using hd)
                (by simpa [Matrix.star_eq_conjTranspose] using
                  (Matrix.mem_unitaryGroup_iff'.mp (hW c)))) c
          else 0) +
          Real.exp (-((T * δ) ^ (2 : ℕ)) / 2)) <
        gaussianFloorTwo *
          ((epsw - epsn) / staticChoiSpeed energy / (2 * T)) *
          (1 - epsw ^ (2 : ℕ)) ^ r) :
    ¬ ∃ t ∈ Icc
        (epsw / staticChoiSpeed energy +
          (epsw - epsn) / staticChoiSpeed energy) T,
      ∃ c, pureStateTraceDistance
        (staticSpectralChoiVector d t energy) (choiVector (W c)) ≤ epsn := by
  let target : C → EuclideanSpace ℂ (Fin d × Fin d) := fun c => choiVector (W c)
  have htarget : ∀ c, ‖target c‖ = 1 := by
    intro c
    apply norm_choiVector_eq_one (by simpa using hd)
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp (hW c))
  let w := staticChoiTargetOptimalDesignWeight r target htarget
  have hw := staticChoiTargetOptimalDesignWeight_mem_stdSimplex r target htarget
  have hsplit := weighted_unitaryChoiNearActionMass_le_transverse_add_centralizerTube
    hd W hW energy r δ β hβ0 w hw
  apply no_forward_pureChoiCircuitReturn_of_canonicalOptimalDesignWeightedCrowding
    hd hmax target htarget hTpos hδ hepsn hgap hepswOne hT
  apply lt_of_le_of_lt _ hbudget
  have hsplit' :
      (∑ c, staticChoiTargetOptimalDesignWeight r target htarget c *
        directStaticChoiTargetNearActionMass (target c) energy r δ) ≤
        β ^ (2 * r) +
          ∑ c, if choiDist (unitaryRadialDiagonalMatrix (W c)) (W c) <
              Real.sqrt (1 - β ^ (2 : ℕ)) then
            staticChoiTargetOptimalDesignWeight r target htarget c else 0 := by
    simpa only [target, w] using hsplit
  nlinarith

end

end RHTower
