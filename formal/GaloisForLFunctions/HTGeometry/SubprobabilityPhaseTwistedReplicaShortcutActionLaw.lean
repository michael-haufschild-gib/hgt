import GaloisForLFunctions.HTGeometry.PhaseTwistedReplicaShortcutActionLaw

/-!
# Subprobability phase-twisted replica shortcut action

Direct target overlaps have nonnegative absolute spectral coefficients whose
sum can be strictly below one.  This module extends finite-window and Gaussian
replica action bounds from probability weights to arbitrary nonnegative
subprobability weights.  Exact collision mass is retained; unresolved action
leakage still has unit constant because total absolute replica mass is at most
one.
-/

open scoped BigOperators Interval ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

theorem sum_fidelityReplicaMultiplicityWeight_eq_sum_pow
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight : I → ℝ) (n : ℕ) :
    (∑ p ∈ Finset.univ.piAntidiag n,
      ∑ q ∈ Finset.univ.piAntidiag n,
        fidelityReplicaMultiplicityWeight weight p q) =
      (∑ i, weight i) ^ (2 * n) := by
  classical
  have h :=
    complexFidelityReplicaMultiplicityExpansion
      weight (fun _ => 1) (fun _ => 1) n
  simp only [mul_one, one_pow, Finset.prod_const_one] at h
  have hc :
      (((∑ i, weight i) : ℝ) : ℂ) ^ (2 * n) =
        ((∑ p ∈ Finset.univ.piAntidiag n,
          ∑ q ∈ Finset.univ.piAntidiag n,
            fidelityReplicaMultiplicityWeight weight p q : ℝ) : ℂ) := by
    calc
      (((∑ i, weight i) : ℝ) : ℂ) ^ (2 * n) =
          ((∑ i, (weight i : ℂ)) ^ n) *
            ((∑ i, (weight i : ℂ)) ^ n) := by
              push_cast
              rw [two_mul, pow_add]
      _ = _ := by
        rw [h]
        push_cast
        rfl
  exact_mod_cast hc.symm

theorem norm_twistedGaussianSpectralFidelityMean_le_collision_add_of_sum_le_one
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) {T δ : ℝ}
    (hT : 0 < T) (hδ : 0 < δ)
    (hgap :
      ∀ p ∈ Finset.univ.piAntidiag n,
        ∀ q ∈ Finset.univ.piAntidiag n,
          replicaMultiplicityEnergy energy p ≠
              replicaMultiplicityEnergy energy q →
            δ ≤
              |replicaMultiplicityEnergy energy p -
                replicaMultiplicityEnergy energy q|) :
    ‖twistedGaussianSpectralFidelityMean weight energy twist n T‖ ≤
      fidelityReplicaCollisionMass weight energy n +
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
            if replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
            then fidelityReplicaMultiplicityWeight weight p q
            else fidelityReplicaMultiplicityWeight weight p q * B := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.sum_le_sum
          intro q hq
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (fidelityReplicaMultiplicityWeight_nonneg hweight p q),
            norm_replicaMultiplicityTwist htwist]
          simp only [mul_one]
          by_cases heq :
              replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
          · rw [if_pos heq, heq, sub_self, mul_zero,
              gaussianObserverActionKernel_zero]
            simp
          · rw [if_neg heq]
            exact mul_le_mul_of_nonneg_left
              (norm_gaussianObserverActionKernel_mul_le hT hδ
                (hgap p hp q hq heq))
              (fidelityReplicaMultiplicityWeight_nonneg hweight p q)
    _ ≤ ∑ p ∈ Finset.univ.piAntidiag n,
          ∑ q ∈ Finset.univ.piAntidiag n,
            ((if replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
              then fidelityReplicaMultiplicityWeight weight p q
              else 0) +
              fidelityReplicaMultiplicityWeight weight p q * B) := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.sum_le_sum
          intro q hq
          by_cases heq :
              replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
          · simp only [heq, if_pos]
            exact le_add_of_nonneg_right
              (mul_nonneg
                (fidelityReplicaMultiplicityWeight_nonneg hweight p q)
                hBnonneg)
          · simp [heq]
    _ = fidelityReplicaCollisionMass weight energy n +
          (∑ i, weight i) ^ (2 * n) * B := by
          simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          rw [htotal, ← fidelityReplicaResonantMass_eq_collisionMass]
          rfl
    _ ≤ fidelityReplicaCollisionMass weight energy n + B := by
          exact add_le_add (le_refl _)
            (mul_le_of_le_one_left hBnonneg htotalLe)
    _ = fidelityReplicaCollisionMass weight energy n +
          Real.exp (-((T * δ) ^ 2) / 2) := rfl

theorem norm_twistedFiniteSpectralFidelityMean_le_collision_add_of_sum_le_one
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) {T δ : ℝ}
    (hT : 0 < T) (hδ : 0 < δ)
    (hgap :
      ∀ p ∈ Finset.univ.piAntidiag n,
        ∀ q ∈ Finset.univ.piAntidiag n,
          replicaMultiplicityEnergy energy p ≠
              replicaMultiplicityEnergy energy q →
            δ ≤
              |replicaMultiplicityEnergy energy p -
                replicaMultiplicityEnergy energy q|) :
    ‖twistedFiniteSpectralFidelityMean weight energy twist n T‖ ≤
      fidelityReplicaCollisionMass weight energy n +
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
            if replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
            then fidelityReplicaMultiplicityWeight weight p q
            else fidelityReplicaMultiplicityWeight weight p q * B := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.sum_le_sum
          intro q hq
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (fidelityReplicaMultiplicityWeight_nonneg hweight p q),
            norm_replicaMultiplicityTwist htwist]
          simp only [mul_one]
          by_cases heq :
              replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
          · rw [if_pos heq, heq, sub_self,
              symmetricPhaseAverage_eq_sinc T 0 hT.ne']
            simp
          · rw [if_neg heq]
            exact mul_le_mul_of_nonneg_left
              (norm_symmetricPhaseAverage_le_min_inv
                hT hδ (hgap p hp q hq heq))
              (fidelityReplicaMultiplicityWeight_nonneg hweight p q)
    _ ≤ ∑ p ∈ Finset.univ.piAntidiag n,
          ∑ q ∈ Finset.univ.piAntidiag n,
            ((if replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
              then fidelityReplicaMultiplicityWeight weight p q
              else 0) +
              fidelityReplicaMultiplicityWeight weight p q * B) := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.sum_le_sum
          intro q hq
          by_cases heq :
              replicaMultiplicityEnergy energy p =
                replicaMultiplicityEnergy energy q
          · simp only [heq, if_pos]
            exact le_add_of_nonneg_right
              (mul_nonneg
                (fidelityReplicaMultiplicityWeight_nonneg hweight p q)
                hBnonneg)
          · simp [heq]
    _ = fidelityReplicaCollisionMass weight energy n +
          (∑ i, weight i) ^ (2 * n) * B := by
          simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          rw [htotal, ← fidelityReplicaResonantMass_eq_collisionMass]
          rfl
    _ ≤ fidelityReplicaCollisionMass weight energy n + B := by
          exact add_le_add (le_refl _)
            (mul_le_of_le_one_left hBnonneg htotalLe)
    _ = fidelityReplicaCollisionMass weight energy n +
          min 1 (T * δ)⁻¹ := rfl

theorem threshold_pow_mul_gaussianTwistedCoherenceCaptureSet_measureReal_le_of_sum_le_one
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ threshold : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hthreshold : 0 ≤ threshold)
    (hgap :
      ∀ p ∈ Finset.univ.piAntidiag n,
        ∀ q ∈ Finset.univ.piAntidiag n,
          replicaMultiplicityEnergy energy p ≠
              replicaMultiplicityEnergy energy q →
            δ ≤
              |replicaMultiplicityEnergy energy p -
                replicaMultiplicityEnergy energy q|) :
    threshold ^ (2 * n) *
        (gaussianReal 0 1).real
          (gaussianTwistedCoherenceCaptureSet
            weight energy twist T threshold) ≤
      fidelityReplicaCollisionMass weight energy n +
        Real.exp (-((T * δ) ^ 2) / 2) := by
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
  calc
    (twistedGaussianSpectralFidelityMean weight energy twist n T).re
        ≤ ‖twistedGaussianSpectralFidelityMean weight energy twist n T‖ :=
          Complex.re_le_norm _
    _ ≤ fidelityReplicaCollisionMass weight energy n +
          Real.exp (-((T * δ) ^ 2) / 2) :=
      norm_twistedGaussianSpectralFidelityMean_le_collision_add_of_sum_le_one
        hweight hweightSum htwist n hT hδ hgap

theorem threshold_pow_mul_uniformTwistedCoherenceCaptureSet_measureReal_le_of_sum_le_one
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i ≤ 1)
    (htwist : ∀ i, ‖twist i‖ = 1)
    (n : ℕ) (hn : 0 < n) {T δ threshold : ℝ}
    (hT : 0 < T) (hδ : 0 < δ) (hthreshold : 0 ≤ threshold)
    (hgap :
      ∀ p ∈ Finset.univ.piAntidiag n,
        ∀ q ∈ Finset.univ.piAntidiag n,
          replicaMultiplicityEnergy energy p ≠
              replicaMultiplicityEnergy energy q →
            δ ≤
              |replicaMultiplicityEnergy energy p -
                replicaMultiplicityEnergy energy q|) :
    threshold ^ (2 * n) *
        volume.real
          (uniformTwistedCoherenceCaptureSet
            weight energy twist T threshold) ≤
      2 * T *
        (fidelityReplicaCollisionMass weight energy n +
          min 1 (T * δ)⁻¹) := by
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
  calc
    2 * T *
        (twistedFiniteSpectralFidelityMean weight energy twist n T).re
        ≤ 2 * T *
          ‖twistedFiniteSpectralFidelityMean weight energy twist n T‖ := by
            exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _)
              (mul_nonneg (by norm_num) hT.le)
    _ ≤ 2 * T *
        (fidelityReplicaCollisionMass weight energy n +
          min 1 (T * δ)⁻¹) := by
            exact mul_le_mul_of_nonneg_left
              (norm_twistedFiniteSpectralFidelityMean_le_collision_add_of_sum_le_one
                hweight hweightSum htwist n hT hδ hgap)
              (mul_nonneg (by norm_num) hT.le)

end GaloisForLFunctions.HTGeometry
