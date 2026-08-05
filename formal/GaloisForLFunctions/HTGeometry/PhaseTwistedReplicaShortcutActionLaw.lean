import GaloisForLFunctions.HTGeometry.IntrinsicReplicaObserverSpectralActionLaw
import GaloisForLFunctions.HTGeometry.GaussianSpectralPacketActionLaw

/-!
# Adaptive circuit-shortcut action law

For every finite spectrum, arbitrary normalized spectral weights, every
finite dictionary of targets, and every positive replica order, this module
bounds all target choices made after observing time.  Exact replica-action
collisions and the smallest nonzero replica action are the only spectral
costs.  Uniform finite windows have inverse-action leakage; Gaussian windows
have exponential leakage.  Maximal projective spectral rank reduces the
collision term to the exact permutation floor.

The target dictionary is represented by phase twists.  A separate geometric
capstone reduces proximity to arbitrary pure target rays to one such twist per
target and instantiates finite padded circuit dictionaries.
-/

open scoped BigOperators Interval ENNReal NNReal
open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section



def twistedFiniteSpectralAmplitude
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (twist : I → ℂ) (t : ℝ) : ℂ :=
  ∑ i, (weight i : ℂ) * twist i *
    Complex.exp (((energy i * t : ℝ) : ℂ) * Complex.I)

def twistedFiniteSpectralFidelity
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (twist : I → ℂ) (t : ℝ) : ℂ :=
  (Complex.normSq (twistedFiniteSpectralAmplitude weight energy twist t) : ℂ)

def replicaMultiplicityTwist
    {I : Type*} [Fintype I]
    (twist : I → ℂ) (p q : I → ℕ) : ℂ :=
  (∏ i, twist i ^ p i) * ∏ i, (starRingEnd ℂ) (twist i) ^ q i

theorem norm_replicaMultiplicityTwist
    {I : Type*} [Fintype I]
    {twist : I → ℂ} (htwist : ∀ i, ‖twist i‖ = 1)
    (p q : I → ℕ) :
    ‖replicaMultiplicityTwist twist p q‖ = 1 := by
  classical
  unfold replicaMultiplicityTwist
  rw [norm_mul, norm_prod, norm_prod]
  simp [norm_pow, htwist]

theorem twistedFiniteSpectralFidelity_eq_phaseProduct
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (twist : I → ℂ) (t : ℝ) :
    twistedFiniteSpectralFidelity weight energy twist t =
      (∑ i, (weight i : ℂ) *
          (twist i * Complex.exp (((energy i * t : ℝ) : ℂ) * Complex.I))) *
      (∑ i, (weight i : ℂ) *
          ((starRingEnd ℂ) (twist i) *
            Complex.exp (((-energy i * t : ℝ) : ℂ) * Complex.I))) := by
  classical
  rw [twistedFiniteSpectralFidelity, Complex.normSq_eq_conj_mul_self]
  unfold twistedFiniteSpectralAmplitude
  rw [map_sum]
  simp_rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have hconj :
      (∑ i, (weight i : ℂ) * (starRingEnd ℂ) (twist i) *
          Complex.exp
            ((starRingEnd ℂ)
              (((energy i * t : ℝ) : ℂ) * Complex.I))) =
        ∑ i, (weight i : ℂ) *
          ((starRingEnd ℂ) (twist i) *
            Complex.exp (((-energy i * t : ℝ) : ℂ) * Complex.I)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hexponent :
        (starRingEnd ℂ) (((energy i * t : ℝ) : ℂ) * Complex.I) =
          (((-energy i * t : ℝ) : ℂ) * Complex.I) := by
      push_cast
      simp
    rw [hexponent]
    ring
  rw [hconj, mul_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    ring

theorem twistedFiniteSpectralFidelity_pow_expansion
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (twist : I → ℂ) (n : ℕ) (t : ℝ) :
    twistedFiniteSpectralFidelity weight energy twist t ^ n =
      ∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
            replicaMultiplicityTwist twist p q *
            Complex.exp
              (((t * (replicaMultiplicityEnergy energy p -
                replicaMultiplicityEnergy energy q) : ℝ) : ℂ) *
                Complex.I) := by
  classical
  rw [twistedFiniteSpectralFidelity_eq_phaseProduct, mul_pow,
    complexFidelityReplicaMultiplicityExpansion]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  have hpositive :
      (∏ i, (twist i * Complex.exp
        (((energy i * t : ℝ) : ℂ) * Complex.I)) ^ p i) =
        (∏ i, twist i ^ p i) *
          Complex.exp
            (((t * replicaMultiplicityEnergy energy p : ℝ) : ℂ) *
              Complex.I) := by
    simp_rw [mul_pow, Finset.prod_mul_distrib, ← Complex.exp_nat_mul]
    congr 1
    rw [← Complex.exp_sum]
    congr 1
    unfold replicaMultiplicityEnergy
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hnegative :
      (∏ i, ((starRingEnd ℂ) (twist i) * Complex.exp
        (((-energy i * t : ℝ) : ℂ) * Complex.I)) ^ q i) =
        (∏ i, (starRingEnd ℂ) (twist i) ^ q i) *
          Complex.exp
            (((-t * replicaMultiplicityEnergy energy q : ℝ) : ℂ) *
              Complex.I) := by
    simp_rw [mul_pow, Finset.prod_mul_distrib, ← Complex.exp_nat_mul]
    congr 1
    rw [← Complex.exp_sum]
    congr 1
    unfold replicaMultiplicityEnergy
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hpositive, hnegative]
  unfold replicaMultiplicityTwist
  calc
    _ = (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
          ((∏ i, twist i ^ p i) *
            ∏ i, (starRingEnd ℂ) (twist i) ^ q i) *
          Complex.exp
            ((t * replicaMultiplicityEnergy energy p : ℝ) * Complex.I +
              (-t * replicaMultiplicityEnergy energy q : ℝ) * Complex.I) := by
        rw [Complex.exp_add]
        ring
    _ = _ := by
      congr 2
      push_cast
      ring

def twistedFiniteSpectralFidelityMean
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (twist : I → ℂ)
    (n : ℕ) (T : ℝ) : ℂ :=
  (2 * T : ℂ)⁻¹ *
    ∫ t : ℝ in -T..T,
      twistedFiniteSpectralFidelity weight energy twist t ^ n

theorem twistedFiniteSpectralFidelityMean_eq_replicaPhaseAverage
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (twist : I → ℂ)
    (n : ℕ) (T : ℝ) :
    twistedFiniteSpectralFidelityMean weight energy twist n T =
      ∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
            replicaMultiplicityTwist twist p q *
            symmetricPhaseAverage T
              (replicaMultiplicityEnergy energy p -
                replicaMultiplicityEnergy energy q) := by
  classical
  unfold twistedFiniteSpectralFidelityMean
  simp_rw [twistedFiniteSpectralFidelity_pow_expansion]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [intervalIntegral.integral_finsetSum]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      rw [intervalIntegral.integral_const_mul]
      unfold symmetricPhaseAverage
      ring
    · intro q hq
      exact
        (by fun_prop :
          Continuous (fun x : ℝ =>
            ((fidelityReplicaMultiplicityWeight weight p q : ℂ) *
              replicaMultiplicityTwist twist p q) *
              Complex.exp
                (((x * (replicaMultiplicityEnergy energy p -
                  replicaMultiplicityEnergy energy q) : ℝ) : ℂ) *
                  Complex.I))).intervalIntegrable
          (μ := MeasureTheory.volume) (-T) T
  · intro p hp
    exact
      (by fun_prop :
        Continuous (fun t : ℝ =>
          ∑ q ∈ Finset.univ.piAntidiag n,
            (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
              replicaMultiplicityTwist twist p q *
              Complex.exp
                (((t * (replicaMultiplicityEnergy energy p -
                  replicaMultiplicityEnergy energy q) : ℝ) : ℂ) *
                  Complex.I))).intervalIntegrable
        (μ := MeasureTheory.volume) (-T) T

theorem norm_twistedFiniteSpectralFidelityMean_le_collision_add
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
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
  have htotal :
      (∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          fidelityReplicaMultiplicityWeight weight p q) = 1 :=
    sum_fidelityReplicaMultiplicityWeight_eq_one weight n hweightSum
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
    _ = fidelityReplicaCollisionMass weight energy n + B := by
          simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          rw [htotal, one_mul,
            ← fidelityReplicaResonantMass_eq_collisionMass]
          rfl
    _ = fidelityReplicaCollisionMass weight energy n +
          min 1 (T * δ)⁻¹ := rfl

def twistedGaussianSpectralFidelityMean
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (twist : I → ℂ)
    (n : ℕ) (T : ℝ) : ℂ :=
  ∫ x : ℝ,
    twistedFiniteSpectralFidelity weight energy twist (T * x) ^ n
      ∂gaussianReal 0 1

theorem twistedGaussianSpectralFidelityMean_eq_actionKernel
    {I : Type*} [Fintype I] [DecidableEq I]
    (weight energy : I → ℝ) (twist : I → ℂ)
    (n : ℕ) (T : ℝ) :
    twistedGaussianSpectralFidelityMean weight energy twist n T =
      ∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          (fidelityReplicaMultiplicityWeight weight p q : ℂ) *
            replicaMultiplicityTwist twist p q *
            gaussianObserverActionKernel
              (T * (replicaMultiplicityEnergy energy p -
                replicaMultiplicityEnergy energy q)) := by
  classical
  have hintegrable (action : ℝ) :
      Integrable
        (fun x : ℝ =>
          Complex.exp (((action * x : ℝ) : ℂ) * Complex.I))
        (gaussianReal 0 1) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards with x
    rw [Complex.norm_exp]
    simp
  unfold twistedGaussianSpectralFidelityMean
  simp_rw [twistedFiniteSpectralFidelity_pow_expansion]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro q hq
      rw [integral_const_mul]
      rw [show
        (fun x : ℝ =>
          Complex.exp
            (((T * x * (replicaMultiplicityEnergy energy p -
              replicaMultiplicityEnergy energy q) : ℝ) : ℂ) * Complex.I)) =
        fun x : ℝ =>
          Complex.exp
            ((((T * (replicaMultiplicityEnergy energy p -
              replicaMultiplicityEnergy energy q)) * x : ℝ) : ℂ) * Complex.I) by
        funext x
        congr 1
        push_cast
        ring]
      rw [integral_gaussian_observer_character]
    · intro q hq
      have hphase : Integrable
          (fun x : ℝ => Complex.exp
            (((T * x * (replicaMultiplicityEnergy energy p -
              replicaMultiplicityEnergy energy q) : ℝ) : ℂ) * Complex.I))
          (gaussianReal 0 1) := by
        convert hintegrable
          (T * (replicaMultiplicityEnergy energy p -
            replicaMultiplicityEnergy energy q)) using 1
        funext x
        congr 1
        push_cast
        ring
      exact hphase.const_mul
        ((fidelityReplicaMultiplicityWeight weight p q : ℂ) *
          replicaMultiplicityTwist twist p q)
  · intro p hp
    apply integrable_finsetSum
    intro q hq
    have hphase : Integrable
        (fun x : ℝ => Complex.exp
          (((T * x * (replicaMultiplicityEnergy energy p -
            replicaMultiplicityEnergy energy q) : ℝ) : ℂ) * Complex.I))
        (gaussianReal 0 1) := by
      convert hintegrable
        (T * (replicaMultiplicityEnergy energy p -
          replicaMultiplicityEnergy energy q)) using 1
      funext x
      congr 1
      push_cast
      ring
    exact hphase.const_mul
      ((fidelityReplicaMultiplicityWeight weight p q : ℂ) *
        replicaMultiplicityTwist twist p q)

theorem norm_gaussianObserverActionKernel (action : ℝ) :
    ‖gaussianObserverActionKernel action‖ =
      Real.exp (-(action ^ 2) / 2) := by
  unfold gaussianObserverActionKernel
  rw [Complex.norm_exp]
  congr 1
  change (-((action : ℂ) ^ 2) / 2).re = -(action ^ 2) / 2
  have hre : ((action : ℂ) ^ 2).re = action ^ 2 := by
    rw [pow_two, Complex.mul_re]
    norm_num
    ring
  rw [Complex.div_re, Complex.neg_re, hre]
  norm_num [Complex.normSq]
  ring

theorem norm_gaussianObserverActionKernel_mul_le
    {T δ detuning : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hdetuning : δ ≤ |detuning|) :
    ‖gaussianObserverActionKernel (T * detuning)‖ ≤
      Real.exp (-((T * δ) ^ 2) / 2) := by
  rw [norm_gaussianObserverActionKernel]
  apply Real.exp_le_exp.mpr
  have hmul : T * δ ≤ |T * detuning| := by
    rw [abs_mul, abs_of_pos hT]
    exact mul_le_mul_of_nonneg_left hdetuning hT.le
  have hsq : (T * δ) ^ 2 ≤ |T * detuning| ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hT.le hδ.le) hmul 2
  rw [sq_abs] at hsq
  linarith

theorem norm_twistedGaussianSpectralFidelityMean_le_collision_add
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
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
  have htotal :
      (∑ p ∈ Finset.univ.piAntidiag n,
        ∑ q ∈ Finset.univ.piAntidiag n,
          fidelityReplicaMultiplicityWeight weight p q) = 1 :=
    sum_fidelityReplicaMultiplicityWeight_eq_one weight n hweightSum
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
    _ = fidelityReplicaCollisionMass weight energy n + B := by
          simp_rw [Finset.sum_add_distrib, ← Finset.sum_mul]
          rw [htotal, one_mul,
            ← fidelityReplicaResonantMass_eq_collisionMass]
          rfl
    _ = fidelityReplicaCollisionMass weight energy n +
          Real.exp (-((T * δ) ^ 2) / 2) := rfl

def gaussianTwistedCoherenceCaptureSet
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (twist : I → ℂ)
    (T threshold : ℝ) : Set ℝ :=
  {x | threshold ≤
    ‖twistedFiniteSpectralAmplitude weight energy twist (T * x)‖}

theorem gaussianTwistedCoherenceCaptureSet_measurable
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (twist : I → ℂ)
    (T threshold : ℝ) :
    MeasurableSet
      (gaussianTwistedCoherenceCaptureSet
        weight energy twist T threshold) := by
  unfold gaussianTwistedCoherenceCaptureSet
  exact (isClosed_le continuous_const (by
    apply Continuous.norm
    unfold twistedFiniteSpectralAmplitude
    fun_prop)).measurableSet

theorem threshold_pow_mul_gaussianTwistedCoherenceCaptureSet_measureReal_le
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
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
          _ = 1 := hweightSum
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
      norm_twistedGaussianSpectralFidelityMean_le_collision_add
        hweight hweightSum htwist n hT hδ hgap

theorem threshold_pow_mul_gaussianAdaptiveCoherenceShortcut_measureReal_le
    {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W]
    {weight energy : I → ℝ} {twist : W → I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (htwist : ∀ w i, ‖twist w i‖ = 1)
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
          (⋃ w : W, gaussianTwistedCoherenceCaptureSet
            weight energy (twist w) T threshold) ≤
      (Fintype.card W : ℝ) *
        (fidelityReplicaCollisionMass weight energy n +
          Real.exp (-((T * δ) ^ 2) / 2)) := by
  have hpow : 0 ≤ threshold ^ (2 * n) := pow_nonneg hthreshold _
  calc
    threshold ^ (2 * n) *
        (gaussianReal 0 1).real
          (⋃ w : W, gaussianTwistedCoherenceCaptureSet
            weight energy (twist w) T threshold)
        ≤ threshold ^ (2 * n) *
            ∑ w : W, (gaussianReal 0 1).real
              (gaussianTwistedCoherenceCaptureSet
                weight energy (twist w) T threshold) :=
          mul_le_mul_of_nonneg_left
            (measureReal_iUnion_fintype_le _) hpow
    _ = ∑ w : W, threshold ^ (2 * n) *
            (gaussianReal 0 1).real
              (gaussianTwistedCoherenceCaptureSet
                weight energy (twist w) T threshold) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ _w : W,
          (fidelityReplicaCollisionMass weight energy n +
            Real.exp (-((T * δ) ^ 2) / 2)) := by
          apply Finset.sum_le_sum
          intro w hw
          exact
            threshold_pow_mul_gaussianTwistedCoherenceCaptureSet_measureReal_le
              hweight hweightSum (htwist w) n hn hT hδ hthreshold hgap
    _ = (Fintype.card W : ℝ) *
        (fidelityReplicaCollisionMass weight energy n +
          Real.exp (-((T * δ) ^ 2) / 2)) := by
            simp
            ring

def uniformTwistedCoherenceCaptureSet
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (twist : I → ℂ)
    (T threshold : ℝ) : Set ℝ :=
  {t ∈ Set.Ioc (-T) T |
    threshold ≤ ‖twistedFiniteSpectralAmplitude weight energy twist t‖}

theorem uniformTwistedCoherenceCaptureSet_measurable
    {I : Type*} [Fintype I]
    (weight energy : I → ℝ) (twist : I → ℂ)
    (T threshold : ℝ) :
    MeasurableSet
      (uniformTwistedCoherenceCaptureSet
        weight energy twist T threshold) := by
  unfold uniformTwistedCoherenceCaptureSet
  exact measurableSet_Ioc.inter
    (isClosed_le continuous_const (by
      show Continuous (fun t : ℝ =>
        ‖twistedFiniteSpectralAmplitude weight energy twist t‖)
      apply Continuous.norm
      unfold twistedFiniteSpectralAmplitude
      fun_prop)).measurableSet

theorem threshold_pow_mul_uniformTwistedCoherenceCaptureSet_measureReal_le
    {I : Type*} [Fintype I] [DecidableEq I]
    {weight energy : I → ℝ} {twist : I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
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
              (norm_twistedFiniteSpectralFidelityMean_le_collision_add
                hweight hweightSum htwist n hT hδ hgap)
              (mul_nonneg (by norm_num) hT.le)

theorem threshold_pow_mul_uniformAdaptiveCoherenceShortcut_measureReal_le
    {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W]
    {weight energy : I → ℝ} {twist : W → I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (htwist : ∀ w i, ‖twist w i‖ = 1)
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
          (⋃ w : W, uniformTwistedCoherenceCaptureSet
            weight energy (twist w) T threshold) ≤
      2 * T * (Fintype.card W : ℝ) *
        (fidelityReplicaCollisionMass weight energy n +
          min 1 (T * δ)⁻¹) := by
  have hpow : 0 ≤ threshold ^ (2 * n) := pow_nonneg hthreshold _
  calc
    threshold ^ (2 * n) *
        volume.real
          (⋃ w : W, uniformTwistedCoherenceCaptureSet
            weight energy (twist w) T threshold)
        ≤ threshold ^ (2 * n) *
            ∑ w : W, volume.real
              (uniformTwistedCoherenceCaptureSet
                weight energy (twist w) T threshold) :=
          mul_le_mul_of_nonneg_left
            (measureReal_iUnion_fintype_le _) hpow
    _ = ∑ w : W, threshold ^ (2 * n) *
            volume.real
              (uniformTwistedCoherenceCaptureSet
                weight energy (twist w) T threshold) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ _w : W,
          2 * T *
            (fidelityReplicaCollisionMass weight energy n +
              min 1 (T * δ)⁻¹) := by
          apply Finset.sum_le_sum
          intro w hw
          exact
            threshold_pow_mul_uniformTwistedCoherenceCaptureSet_measureReal_le
              hweight hweightSum (htwist w) n hn hT hδ hthreshold hgap
    _ = 2 * T * (Fintype.card W : ℝ) *
        (fidelityReplicaCollisionMass weight energy n +
          min 1 (T * δ)⁻¹) := by
            simp
            ring

/-- Every finite spectrum has a canonical positive action resolution, so
the adaptive uniform-window shortcut law needs no externally supplied gap. -/
theorem threshold_pow_mul_uniformAdaptiveCoherenceShortcut_measureReal_le_intrinsic
    {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W]
    {weight energy : I → ℝ} {twist : W → I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (htwist : ∀ w i, ‖twist w i‖ = 1)
    (n : ℕ) (hn : 0 < n) {T threshold : ℝ}
    (hT : 0 < T) (hthreshold : 0 ≤ threshold) :
    threshold ^ (2 * n) *
        volume.real
          (⋃ w : W, uniformTwistedCoherenceCaptureSet
            weight energy (twist w) T threshold) ≤
      2 * T * (Fintype.card W : ℝ) *
        (fidelityReplicaCollisionMass weight energy n +
          min 1
            (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  apply threshold_pow_mul_uniformAdaptiveCoherenceShortcut_measureReal_le
    hweight hweightSum htwist n hn hT
    (intrinsicReplicaActionResolution_pos energy n) hthreshold
  intro p hp q hq hne
  exact intrinsicReplicaActionResolution_le energy n hp hq hne

/-- Gaussian-time counterpart of the intrinsic adaptive shortcut law. -/
theorem threshold_pow_mul_gaussianAdaptiveCoherenceShortcut_measureReal_le_intrinsic
    {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W]
    {weight energy : I → ℝ} {twist : W → I → ℂ}
    (hweight : ∀ i, 0 ≤ weight i)
    (hweightSum : ∑ i, weight i = 1)
    (htwist : ∀ w i, ‖twist w i‖ = 1)
    (n : ℕ) (hn : 0 < n) {T threshold : ℝ}
    (hT : 0 < T) (hthreshold : 0 ≤ threshold) :
    threshold ^ (2 * n) *
        (gaussianReal 0 1).real
          (⋃ w : W, gaussianTwistedCoherenceCaptureSet
            weight energy (twist w) T threshold) ≤
      (Fintype.card W : ℝ) *
        (fidelityReplicaCollisionMass weight energy n +
          Real.exp
            (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  apply threshold_pow_mul_gaussianAdaptiveCoherenceShortcut_measureReal_le
    hweight hweightSum htwist n hn hT
    (intrinsicReplicaActionResolution_pos energy n) hthreshold
  intro p hp q hq hne
  exact intrinsicReplicaActionResolution_le energy n hp hq hne

/-- Maximal projective rank replaces collision mass by its exact permutation
floor in the intrinsic uniform adaptive shortcut law. -/
theorem threshold_pow_mul_uniformAdaptiveCoherenceShortcut_measureReal_le_floor
    {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W]
    {weight energy : I → ℝ} {twist : W → I → ℂ}
    (hweight : ∀ i, 0 < weight i)
    (hweightSum : ∑ i, weight i = 1)
    (htwist : ∀ w i, ‖twist w i‖ = 1)
    (hmax : MaximallyProjectiveEnergy energy)
    (n : ℕ) (hn : 0 < n) {T threshold : ℝ}
    (hT : 0 < T) (hthreshold : 0 ≤ threshold) :
    threshold ^ (2 * n) *
        volume.real
          (⋃ w : W, uniformTwistedCoherenceCaptureSet
            weight energy (twist w) T threshold) ≤
      2 * T * (Fintype.card W : ℝ) *
        (fidelityReplicaPermutationFloor weight n +
          min 1
            (T * intrinsicReplicaActionResolution energy n)⁻¹) := by
  rw [← (all_fidelityReplicaCollisionMass_eq_floor_iff
    hweight energy).2 hmax n]
  exact
    threshold_pow_mul_uniformAdaptiveCoherenceShortcut_measureReal_le_intrinsic
      (fun i => (hweight i).le) hweightSum htwist n hn hT hthreshold

/-- Maximal-projective Gaussian counterpart. -/
theorem threshold_pow_mul_gaussianAdaptiveCoherenceShortcut_measureReal_le_floor
    {I W : Type*} [Fintype I] [DecidableEq I] [Fintype W]
    {weight energy : I → ℝ} {twist : W → I → ℂ}
    (hweight : ∀ i, 0 < weight i)
    (hweightSum : ∑ i, weight i = 1)
    (htwist : ∀ w i, ‖twist w i‖ = 1)
    (hmax : MaximallyProjectiveEnergy energy)
    (n : ℕ) (hn : 0 < n) {T threshold : ℝ}
    (hT : 0 < T) (hthreshold : 0 ≤ threshold) :
    threshold ^ (2 * n) *
        (gaussianReal 0 1).real
          (⋃ w : W, gaussianTwistedCoherenceCaptureSet
            weight energy (twist w) T threshold) ≤
      (Fintype.card W : ℝ) *
        (fidelityReplicaPermutationFloor weight n +
          Real.exp
            (-((T * intrinsicReplicaActionResolution energy n) ^ 2) / 2)) := by
  rw [← (all_fidelityReplicaCollisionMass_eq_floor_iff
    hweight energy).2 hmax n]
  exact
    threshold_pow_mul_gaussianAdaptiveCoherenceShortcut_measureReal_le_intrinsic
      (fun i => (hweight i).le) hweightSum htwist n hn hT hthreshold

end
end GaloisForLFunctions.HTGeometry

