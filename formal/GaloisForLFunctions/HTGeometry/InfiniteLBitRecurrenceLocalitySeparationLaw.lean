import GaloisForLFunctions.HTGeometry.QuasiLocalInfiniteLBitEvolutionLaw
import GaloisForLFunctions.HTGeometry.FiniteHorizonCStarPerturbationLaw
import GaloisForLFunctions.HTGeometry.LBitLocalObserverTemporalDimensionLaw

/-!
# Infinite l-bit recurrence--locality separation

The same absolutely summable countable l-bit field has two properties:

* its Heisenberg flip commutators obey a volume-independent exponential
  distance bound;
* every finite environment of one local flip carries the maximal possible
  rational temporal rank.

This is an exact infinite-volume separation between propagation of influence
and observer-visible recurrence dimension.
-/

open Set Filter
open scoped BigOperators Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Flip one site in an infinite Boolean configuration. -/
def infiniteLBitFlip
    (i : ℕ) (σ : InfiniteLBitConfiguration) :
    InfiniteLBitConfiguration :=
  fun j => if j = i then !σ j else σ j

@[simp]
theorem infiniteLBitFlip_apply_self
    (i : ℕ) (σ : InfiniteLBitConfiguration) :
    infiniteLBitFlip i σ i = !σ i := by
  simp [infiniteLBitFlip]

theorem infiniteLBitFlip_apply_of_ne
    {i j : ℕ} (hji : j ≠ i)
    (σ : InfiniteLBitConfiguration) :
    infiniteLBitFlip i σ j = σ j := by
  simp [infiniteLBitFlip, hji]

@[simp]
theorem infiniteLBitFlip_involutive
    (i : ℕ) (σ : InfiniteLBitConfiguration) :
    infiniteLBitFlip i (infiniteLBitFlip i σ) = σ := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [infiniteLBitFlip]
  · simp [infiniteLBitFlip, hji]

theorem infiniteLBitFlip_commute
    (i j : ℕ) (σ : InfiniteLBitConfiguration) :
    infiniteLBitFlip i (infiniteLBitFlip j σ) =
      infiniteLBitFlip j (infiniteLBitFlip i σ) := by
  funext k
  by_cases hki : k = i
  · subst k
    by_cases hij : i = j
    · subst j
      simp
    · simp [infiniteLBitFlip, hij]
  · by_cases hkj : k = j
    · subst k
      simp [infiniteLBitFlip, hki]
    · simp [infiniteLBitFlip, hki, hkj]

theorem infiniteLBitCharacter_flip_of_not_mem
    (S : Finset ℕ) {i : ℕ} (hi : i ∉ S)
    (σ : InfiniteLBitConfiguration) :
    infiniteLBitCharacter S (infiniteLBitFlip i σ) =
      infiniteLBitCharacter S σ := by
  classical
  unfold infiniteLBitCharacter
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := by
    intro h
    subst j
    exact hi hj
  rw [infiniteLBitFlip_apply_of_ne hji]

/-- Double configuration difference of the infinite l-bit energy. -/
def infiniteLBitEnergyDoubleFlip
    (i j : ℕ) (σ : InfiniteLBitConfiguration) : ℝ :=
  quasiLocalInfiniteLBitEnergy
      (infiniteLBitFlip i (infiniteLBitFlip j σ)) -
    quasiLocalInfiniteLBitEnergy (infiniteLBitFlip i σ) -
    quasiLocalInfiniteLBitEnergy (infiniteLBitFlip j σ) +
    quasiLocalInfiniteLBitEnergy σ

/-- Double configuration difference of one interaction term. -/
def infiniteLBitEnergyTermDoubleFlip
    (S : Finset ℕ) (i j : ℕ)
    (σ : InfiniteLBitConfiguration) : ℝ :=
  quasiLocalInfiniteLBitEnergyTerm S
      (infiniteLBitFlip i (infiniteLBitFlip j σ)) -
    quasiLocalInfiniteLBitEnergyTerm S (infiniteLBitFlip i σ) -
    quasiLocalInfiniteLBitEnergyTerm S (infiniteLBitFlip j σ) +
    quasiLocalInfiniteLBitEnergyTerm S σ

/-- A double flip kills every interaction not incident on both sites. -/
theorem abs_infiniteLBitEnergyTermDoubleFlip_le
    (S : Finset ℕ) (i j : ℕ)
    (σ : InfiniteLBitConfiguration) :
    |infiniteLBitEnergyTermDoubleFlip S i j σ| ≤
      if i ∈ S ∧ j ∈ S then
        4 * |quasiLocalInfiniteLBitCoefficient S|
      else 0 := by
  classical
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · rw [if_pos ⟨hi, hj⟩]
      unfold infiniteLBitEnergyTermDoubleFlip
      calc
        |quasiLocalInfiniteLBitEnergyTerm S
              (infiniteLBitFlip i (infiniteLBitFlip j σ)) -
            quasiLocalInfiniteLBitEnergyTerm S (infiniteLBitFlip i σ) -
            quasiLocalInfiniteLBitEnergyTerm S (infiniteLBitFlip j σ) +
            quasiLocalInfiniteLBitEnergyTerm S σ|
            ≤
          |quasiLocalInfiniteLBitEnergyTerm S
              (infiniteLBitFlip i (infiniteLBitFlip j σ)) -
            quasiLocalInfiniteLBitEnergyTerm S (infiniteLBitFlip i σ) -
            quasiLocalInfiniteLBitEnergyTerm S (infiniteLBitFlip j σ)| +
            |quasiLocalInfiniteLBitEnergyTerm S σ| := by
              exact abs_add_le _ _
        _ ≤
          (|quasiLocalInfiniteLBitEnergyTerm S
              (infiniteLBitFlip i (infiniteLBitFlip j σ)) -
            quasiLocalInfiniteLBitEnergyTerm S (infiniteLBitFlip i σ)| +
            |quasiLocalInfiniteLBitEnergyTerm S (infiniteLBitFlip j σ)|) +
            |quasiLocalInfiniteLBitEnergyTerm S σ| := by
              gcongr
              simpa using
                (abs_sub_le
                  (quasiLocalInfiniteLBitEnergyTerm S
                    (infiniteLBitFlip i
                      (infiniteLBitFlip j σ)) -
                    quasiLocalInfiniteLBitEnergyTerm S
                      (infiniteLBitFlip i σ))
                  0
                  (quasiLocalInfiniteLBitEnergyTerm S
                    (infiniteLBitFlip j σ)))
        _ ≤
          |quasiLocalInfiniteLBitEnergyTerm S
              (infiniteLBitFlip i (infiniteLBitFlip j σ))| +
            |quasiLocalInfiniteLBitEnergyTerm S (infiniteLBitFlip i σ)| +
            |quasiLocalInfiniteLBitEnergyTerm S (infiniteLBitFlip j σ)| +
            |quasiLocalInfiniteLBitEnergyTerm S σ| := by
              gcongr
              simpa using
                (abs_sub_le
                  (quasiLocalInfiniteLBitEnergyTerm S
                    (infiniteLBitFlip i
                      (infiniteLBitFlip j σ)))
                  0
                  (quasiLocalInfiniteLBitEnergyTerm S
                    (infiniteLBitFlip i σ)))
        _ = 4 * |quasiLocalInfiniteLBitCoefficient S| := by
          simp only [abs_quasiLocalInfiniteLBitEnergyTerm]
          ring
    · rw [if_neg (by simp [hj])]
      unfold infiniteLBitEnergyTermDoubleFlip
      unfold quasiLocalInfiniteLBitEnergyTerm
      have hdouble :
        infiniteLBitCharacter S
            (infiniteLBitFlip i (infiniteLBitFlip j σ)) =
          infiniteLBitCharacter S (infiniteLBitFlip i σ) := by
            calc
              infiniteLBitCharacter S
                  (infiniteLBitFlip i (infiniteLBitFlip j σ)) =
                infiniteLBitCharacter S
                  (infiniteLBitFlip j (infiniteLBitFlip i σ)) := by
                    rw [infiniteLBitFlip_commute]
              _ = infiniteLBitCharacter S
                  (infiniteLBitFlip i σ) :=
                infiniteLBitCharacter_flip_of_not_mem S hj
                  (infiniteLBitFlip i σ)
      have hsingle :
          infiniteLBitCharacter S (infiniteLBitFlip j σ) =
            infiniteLBitCharacter S σ :=
        infiniteLBitCharacter_flip_of_not_mem S hj σ
      rw [hdouble, hsingle]
      ring_nf
      simp
  · rw [if_neg (by simp [hi])]
    unfold infiniteLBitEnergyTermDoubleFlip
    unfold quasiLocalInfiniteLBitEnergyTerm
    have hdouble :
      infiniteLBitCharacter S
          (infiniteLBitFlip i (infiniteLBitFlip j σ)) =
        infiniteLBitCharacter S (infiniteLBitFlip j σ) := by
          exact infiniteLBitCharacter_flip_of_not_mem S hi
            (infiniteLBitFlip j σ)
    have hsingle :
        infiniteLBitCharacter S (infiniteLBitFlip i σ) =
          infiniteLBitCharacter S σ :=
      infiniteLBitCharacter_flip_of_not_mem S hi σ
    rw [hdouble, hsingle]
    ring_nf
    simp

theorem summable_infiniteLBitEnergyTermDoubleFlip
    (i j : ℕ) (σ : InfiniteLBitConfiguration) :
    Summable
      (fun S : Finset ℕ =>
        infiniteLBitEnergyTermDoubleFlip S i j σ) := by
  unfold infiniteLBitEnergyTermDoubleFlip
  exact
    (((summable_quasiLocalInfiniteLBitEnergyTerm
      (infiniteLBitFlip i (infiniteLBitFlip j σ))).sub
        (summable_quasiLocalInfiniteLBitEnergyTerm
          (infiniteLBitFlip i σ))).sub
      (summable_quasiLocalInfiniteLBitEnergyTerm
        (infiniteLBitFlip j σ))).add
      (summable_quasiLocalInfiniteLBitEnergyTerm σ)

theorem infiniteLBitEnergyDoubleFlip_eq_tsum
    (i j : ℕ) (σ : InfiniteLBitConfiguration) :
    infiniteLBitEnergyDoubleFlip i j σ =
      ∑' S : Finset ℕ,
        infiniteLBitEnergyTermDoubleFlip S i j σ := by
  unfold infiniteLBitEnergyDoubleFlip
  unfold quasiLocalInfiniteLBitEnergy
  have hsum :=
    (((summable_quasiLocalInfiniteLBitEnergyTerm
      (infiniteLBitFlip i (infiniteLBitFlip j σ))).hasSum.sub
        (summable_quasiLocalInfiniteLBitEnergyTerm
          (infiniteLBitFlip i σ)).hasSum).sub
      (summable_quasiLocalInfiniteLBitEnergyTerm
        (infiniteLBitFlip j σ)).hasSum).add
      (summable_quasiLocalInfiniteLBitEnergyTerm σ).hasSum
  exact hsum.tsum_eq.symm

theorem pairwiseDistance_le_finiteLBitSupportDiameter
    {S : Finset ℕ} {i j : ℕ} (hi : i ∈ S) (hj : j ∈ S) :
    Nat.dist i j ≤ finiteLBitSupportDiameter S := by
  have hinner :
      Nat.dist i j ≤ S.sup (fun k => Nat.dist i k) :=
    Finset.le_sup (f := fun k => Nat.dist i k) hj
  have houter :
      S.sup (fun k => Nat.dist i k) ≤
        S.sup (fun k => S.sup (fun l => Nat.dist k l)) :=
    Finset.le_sup
      (f := fun k => S.sup (fun l => Nat.dist k l)) hi
  exact hinner.trans houter

theorem one_le_half_pow_mul_two_pow_of_le
    {a b : ℕ} (hab : a ≤ b) :
    (1 : ℝ) ≤
      ((1 : ℝ) / 2) ^ a * (2 : ℝ) ^ b := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  calc
    (1 : ℝ) =
        ((1 : ℝ) / 2) ^ a * (2 : ℝ) ^ a := by
          rw [← mul_pow]
          norm_num
    _ ≤
        (((1 : ℝ) / 2) ^ a * (2 : ℝ) ^ a) *
          (2 : ℝ) ^ k := by
            exact le_mul_of_one_le_right
              (by positivity)
              (one_le_pow₀ (by norm_num))
    _ =
        ((1 : ℝ) / 2) ^ a *
          ((2 : ℝ) ^ a * (2 : ℝ) ^ k) := by ring

theorem abs_infiniteLBitEnergyTermDoubleFlip_le_weighted
    (S : Finset ℕ) (i j : ℕ)
    (σ : InfiniteLBitConfiguration) :
    |infiniteLBitEnergyTermDoubleFlip S i j σ| ≤
      4 * ((1 : ℝ) / 2) ^ Nat.dist i j *
        ((2 : ℝ) ^ finiteLBitSupportDiameter S *
          |quasiLocalInfiniteLBitCoefficient S|) := by
  classical
  by_cases hboth : i ∈ S ∧ j ∈ S
  · have hbase :
        |infiniteLBitEnergyTermDoubleFlip S i j σ| ≤
          4 * |quasiLocalInfiniteLBitCoefficient S| := by
      simpa [hboth] using
        abs_infiniteLBitEnergyTermDoubleFlip_le S i j σ
    refine hbase.trans ?_
    have hdiam :
        Nat.dist i j ≤ finiteLBitSupportDiameter S :=
      pairwiseDistance_le_finiteLBitSupportDiameter
        hboth.1 hboth.2
    have hfactor :
        (1 : ℝ) ≤
          ((1 : ℝ) / 2) ^ Nat.dist i j *
            (2 : ℝ) ^ finiteLBitSupportDiameter S :=
      one_le_half_pow_mul_two_pow_of_le hdiam
    calc
      4 * |quasiLocalInfiniteLBitCoefficient S| =
          (4 * |quasiLocalInfiniteLBitCoefficient S|) * 1 := by ring
      _ ≤
          (4 * |quasiLocalInfiniteLBitCoefficient S|) *
            (((1 : ℝ) / 2) ^ Nat.dist i j *
              (2 : ℝ) ^ finiteLBitSupportDiameter S) := by
                exact mul_le_mul_of_nonneg_left hfactor
                  (by positivity)
      _ =
          4 * ((1 : ℝ) / 2) ^ Nat.dist i j *
            ((2 : ℝ) ^ finiteLBitSupportDiameter S *
              |quasiLocalInfiniteLBitCoefficient S|) := by ring
  · have hzero :
        |infiniteLBitEnergyTermDoubleFlip S i j σ| ≤ 0 := by
      simpa [hboth] using
        abs_infiniteLBitEnergyTermDoubleFlip_le S i j σ
    exact hzero.trans (by positivity)

/-- Diameter-weighted absolute interaction mass. -/
def quasiLocalInfiniteLBitWeightedMass : ℝ :=
  ∑' S : Finset ℕ,
    (2 : ℝ) ^ finiteLBitSupportDiameter S *
      |quasiLocalInfiniteLBitCoefficient S|

/-- The diameter-weighted interaction mass is finite. -/
theorem summable_quasiLocalInfiniteLBitWeightedCoefficient :
    Summable
      (fun S : Finset ℕ =>
        (2 : ℝ) ^ finiteLBitSupportDiameter S *
          |quasiLocalInfiniteLBitCoefficient S|) := by
  apply Summable.of_nonneg_of_le
    (fun S => mul_nonneg (by positivity) (abs_nonneg _))
    (fun S => ?_)
    (summable_geometric_two_encode :
      Summable
        (fun S : Finset ℕ =>
          ((1 : ℝ) / 2) ^ Encodable.encode S))
  calc
    (2 : ℝ) ^ finiteLBitSupportDiameter S *
          |quasiLocalInfiniteLBitCoefficient S|
        ≤
      (2 : ℝ) ^ finiteLBitSupportDiameter S *
        ((1 : ℝ) / 2) ^ quasiLocalLBitSupportComplexity S := by
          exact mul_le_mul_of_nonneg_left
            (abs_quasiLocalInfiniteLBitCoefficient_le S)
            (by positivity)
    _ =
      ((1 : ℝ) / 2) ^
        (Encodable.encode S + S.card +
          finiteLBitSupportExtent S) := by
          rw [quasiLocalLBitSupportComplexity]
          have hsum :
            Encodable.encode S + S.card +
                finiteLBitSupportExtent S +
                finiteLBitSupportDiameter S =
              (Encodable.encode S + S.card +
                finiteLBitSupportExtent S) +
                finiteLBitSupportDiameter S := by omega
          rw [hsum, pow_add]
          calc
            (2 : ℝ) ^ finiteLBitSupportDiameter S *
                (((1 : ℝ) / 2) ^
                  (Encodable.encode S + S.card +
                    finiteLBitSupportExtent S) *
                  ((1 : ℝ) / 2) ^
                    finiteLBitSupportDiameter S) =
              ((1 : ℝ) / 2) ^
                  (Encodable.encode S + S.card +
                    finiteLBitSupportExtent S) *
                (((2 : ℝ) * ((1 : ℝ) / 2)) ^
                  finiteLBitSupportDiameter S) := by
                    rw [mul_pow]
                    ring
            _ =
              ((1 : ℝ) / 2) ^
                (Encodable.encode S + S.card +
                  finiteLBitSupportExtent S) := by norm_num
    _ ≤ ((1 : ℝ) / 2) ^ Encodable.encode S := by
      apply pow_le_pow_of_le_one
      · norm_num
      · norm_num
      · omega

/-- Double energy differences decay exponentially with site distance. -/
theorem abs_infiniteLBitEnergyDoubleFlip_le
    (i j : ℕ) (σ : InfiniteLBitConfiguration) :
    |infiniteLBitEnergyDoubleFlip i j σ| ≤
      4 * ((1 : ℝ) / 2) ^ Nat.dist i j *
        quasiLocalInfiniteLBitWeightedMass := by
  rw [infiniteLBitEnergyDoubleFlip_eq_tsum]
  rw [← Real.norm_eq_abs]
  calc
    ‖∑' S : Finset ℕ,
        infiniteLBitEnergyTermDoubleFlip S i j σ‖ ≤
      ∑' S : Finset ℕ,
        ‖infiniteLBitEnergyTermDoubleFlip S i j σ‖ :=
      norm_tsum_le_tsum_norm
        (summable_infiniteLBitEnergyTermDoubleFlip i j σ).norm
    _ ≤
      ∑' S : Finset ℕ,
        4 * ((1 : ℝ) / 2) ^ Nat.dist i j *
          ((2 : ℝ) ^ finiteLBitSupportDiameter S *
            |quasiLocalInfiniteLBitCoefficient S|) := by
              apply Summable.tsum_le_tsum
              · intro S
                simpa [Real.norm_eq_abs] using
                  abs_infiniteLBitEnergyTermDoubleFlip_le_weighted
                    S i j σ
              · exact
                  (summable_infiniteLBitEnergyTermDoubleFlip
                    i j σ).norm
              · exact
                  summable_quasiLocalInfiniteLBitWeightedCoefficient.mul_left
                    (4 * ((1 : ℝ) / 2) ^ Nat.dist i j)
    _ =
      4 * ((1 : ℝ) / 2) ^ Nat.dist i j *
        quasiLocalInfiniteLBitWeightedMass := by
          rw [quasiLocalInfiniteLBitWeightedMass, tsum_mul_left]

/-- Phase multiplying one Heisenberg-evolved local flip. -/
noncomputable def quasiLocalInfiniteLBitHeisenbergFlipPhase
    (t : ℝ) (i : ℕ) (σ : InfiniteLBitConfiguration) : ℂ :=
  Complex.exp
    (t •
      (Complex.I *
        ((quasiLocalInfiniteLBitEnergy (infiniteLBitFlip i σ) -
          quasiLocalInfiniteLBitEnergy σ : ℝ) : ℂ)))

@[simp]
theorem norm_quasiLocalInfiniteLBitHeisenbergFlipPhase
    (t : ℝ) (i : ℕ) (σ : InfiniteLBitConfiguration) :
    ‖quasiLocalInfiniteLBitHeisenbergFlipPhase t i σ‖ = 1 := by
  rw [quasiLocalInfiniteLBitHeisenbergFlipPhase,
    Complex.norm_exp]
  simp

theorem norm_quasiLocalInfiniteLBitHeisenbergFlipPhase_sub_le
    (t : ℝ) (i j : ℕ) (σ : InfiniteLBitConfiguration) :
    ‖quasiLocalInfiniteLBitHeisenbergFlipPhase t i
          (infiniteLBitFlip j σ) -
        quasiLocalInfiniteLBitHeisenbergFlipPhase t i σ‖ ≤
      |t| * (4 * ((1 : ℝ) / 2) ^ Nat.dist i j *
        quasiLocalInfiniteLBitWeightedMass) := by
  let a : ℝ :=
    quasiLocalInfiniteLBitEnergy
        (infiniteLBitFlip i (infiniteLBitFlip j σ)) -
      quasiLocalInfiniteLBitEnergy (infiniteLBitFlip j σ)
  let b : ℝ :=
    quasiLocalInfiniteLBitEnergy (infiniteLBitFlip i σ) -
      quasiLocalInfiniteLBitEnergy σ
  let x : ℂ := Complex.I * (a : ℂ)
  let y : ℂ := Complex.I * (b : ℂ)
  have hx : x ∈ skewAdjoint ℂ := by
    rw [skewAdjoint.mem_iff]
    simp [x]
  have hy : y ∈ skewAdjoint ℂ := by
    rw [skewAdjoint.mem_iff]
    simp [y]
  have hduhamel :=
    exp_skewAdjoint_sub_exp_skewAdjoint_norm_le
      x y hx hy t
  have hxy :
      ‖x - y‖ =
        |infiniteLBitEnergyDoubleFlip i j σ| := by
    rw [show x - y =
        (Complex.I : ℂ) *
          (infiniteLBitEnergyDoubleFlip i j σ : ℂ) by
      simp only [x, y, a, b, infiniteLBitEnergyDoubleFlip]
      push_cast
      ring]
    rw [norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
  change ‖Complex.exp (t • x) - Complex.exp (t • y)‖ ≤ _
  calc
    ‖Complex.exp (t • x) - Complex.exp (t • y)‖
        ≤ |t| * ‖x - y‖ := by
          simpa only [Complex.exp_eq_exp_ℂ] using hduhamel
    _ = |t| * |infiniteLBitEnergyDoubleFlip i j σ| := by
      rw [hxy]
    _ ≤ |t| * (4 * ((1 : ℝ) / 2) ^ Nat.dist i j *
        quasiLocalInfiniteLBitWeightedMass) := by
      exact mul_le_mul_of_nonneg_left
        (abs_infiniteLBitEnergyDoubleFlip_le i j σ) (abs_nonneg t)

theorem continuous_infiniteLBitFlip (i : ℕ) :
    Continuous (infiniteLBitFlip i) := by
  apply continuous_pi
  intro j
  by_cases hji : j = i
  · subst j
    have hnot : Continuous (fun b : Bool => !b) :=
      continuous_of_discreteTopology
    have happly :
        Continuous (fun σ : InfiniteLBitConfiguration => σ i) :=
      continuous_apply i
    have hc := hnot.comp happly
    convert hc using 1
    funext σ
    simp [infiniteLBitFlip]
  · simpa [infiniteLBitFlip, hji] using
      (continuous_apply j :
        Continuous (fun σ : InfiniteLBitConfiguration => σ j))

/-- Configuration flip acting on continuous amplitudes. -/
noncomputable def infiniteLBitFlipOperator
    (i : ℕ) (ψ : ContinuousInfiniteLBitAmplitude) :
    ContinuousInfiniteLBitAmplitude :=
  ψ.comp
    ⟨infiniteLBitFlip i, continuous_infiniteLBitFlip i⟩

@[simp]
theorem infiniteLBitFlipOperator_apply
    (i : ℕ) (ψ : ContinuousInfiniteLBitAmplitude)
    (σ : InfiniteLBitConfiguration) :
    infiniteLBitFlipOperator i ψ σ =
      ψ (infiniteLBitFlip i σ) :=
  rfl

/-- Heisenberg evolution of one local flip. -/
noncomputable def quasiLocalInfiniteLBitHeisenbergFlip
    (t : ℝ) (i : ℕ) (ψ : ContinuousInfiniteLBitAmplitude) :
    ContinuousInfiniteLBitAmplitude :=
  quasiLocalInfiniteLBitEvolution t
    (infiniteLBitFlipOperator i
      (quasiLocalInfiniteLBitEvolution (-t) ψ))

theorem quasiLocalInfiniteLBitHeisenbergFlip_apply
    (t : ℝ) (i : ℕ) (ψ : ContinuousInfiniteLBitAmplitude)
    (σ : InfiniteLBitConfiguration) :
    quasiLocalInfiniteLBitHeisenbergFlip t i ψ σ =
      quasiLocalInfiniteLBitHeisenbergFlipPhase t i σ *
        ψ (infiniteLBitFlip i σ) := by
  rw [quasiLocalInfiniteLBitHeisenbergFlip,
    quasiLocalInfiniteLBitEvolution_apply,
    infiniteLBitFlipOperator_apply,
    quasiLocalInfiniteLBitEvolution_apply]
  rw [quasiLocalInfiniteLBitPhase,
    quasiLocalInfiniteLBitPhase,
    quasiLocalInfiniteLBitHeisenbergFlipPhase]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  apply Complex.ext
  all_goals
    simp [RCLike.real_smul_eq_coe_mul] <;> ring

/-- Commutator of one Heisenberg-evolved flip with a second local flip. -/
noncomputable def quasiLocalInfiniteLBitFlipCommutator
    (t : ℝ) (i j : ℕ) (ψ : ContinuousInfiniteLBitAmplitude) :
    ContinuousInfiniteLBitAmplitude :=
  quasiLocalInfiniteLBitHeisenbergFlip t i
      (infiniteLBitFlipOperator j ψ) -
    infiniteLBitFlipOperator j
      (quasiLocalInfiniteLBitHeisenbergFlip t i ψ)

theorem quasiLocalInfiniteLBitFlipCommutator_apply
    (t : ℝ) (i j : ℕ) (ψ : ContinuousInfiniteLBitAmplitude)
    (σ : InfiniteLBitConfiguration) :
    quasiLocalInfiniteLBitFlipCommutator t i j ψ σ =
      (quasiLocalInfiniteLBitHeisenbergFlipPhase t i σ -
        quasiLocalInfiniteLBitHeisenbergFlipPhase t i
          (infiniteLBitFlip j σ)) *
        ψ (infiniteLBitFlip j (infiniteLBitFlip i σ)) := by
  rw [quasiLocalInfiniteLBitFlipCommutator,
    ContinuousMap.sub_apply,
    quasiLocalInfiniteLBitHeisenbergFlip_apply,
    infiniteLBitFlipOperator_apply,
    infiniteLBitFlipOperator_apply,
    quasiLocalInfiniteLBitHeisenbergFlip_apply]
  rw [infiniteLBitFlip_commute i j σ]
  ring

/-- Volume-independent exponential influence bound. -/
theorem norm_quasiLocalInfiniteLBitFlipCommutator_le
    (t : ℝ) (i j : ℕ) (ψ : ContinuousInfiniteLBitAmplitude) :
    ‖quasiLocalInfiniteLBitFlipCommutator t i j ψ‖ ≤
      |t| * (4 * ((1 : ℝ) / 2) ^ Nat.dist i j *
        quasiLocalInfiniteLBitWeightedMass) * ‖ψ‖ := by
  have hmass : 0 ≤ quasiLocalInfiniteLBitWeightedMass := by
    unfold quasiLocalInfiniteLBitWeightedMass
    exact tsum_nonneg fun S =>
      mul_nonneg (by positivity) (abs_nonneg _)
  have hcoefficient :
      0 ≤ |t| * (4 * ((1 : ℝ) / 2) ^ Nat.dist i j *
        quasiLocalInfiniteLBitWeightedMass) := by
    positivity
  rw [ContinuousMap.norm_le _
    (mul_nonneg hcoefficient (norm_nonneg ψ))]
  intro σ
  rw [quasiLocalInfiniteLBitFlipCommutator_apply, norm_mul]
  calc
    ‖quasiLocalInfiniteLBitHeisenbergFlipPhase t i σ -
          quasiLocalInfiniteLBitHeisenbergFlipPhase t i
            (infiniteLBitFlip j σ)‖ *
        ‖ψ (infiniteLBitFlip j (infiniteLBitFlip i σ))‖
        ≤
      (|t| * (4 * ((1 : ℝ) / 2) ^ Nat.dist i j *
        quasiLocalInfiniteLBitWeightedMass)) *
        ‖ψ (infiniteLBitFlip j (infiniteLBitFlip i σ))‖ := by
          gcongr
          rw [norm_sub_rev]
          exact
            norm_quasiLocalInfiniteLBitHeisenbergFlipPhase_sub_le
              t i j σ
    _ ≤
      |t| * (4 * ((1 : ℝ) / 2) ^ Nat.dist i j *
        quasiLocalInfiniteLBitWeightedMass) * ‖ψ‖ := by
          exact mul_le_mul_of_nonneg_left
            (ContinuousMap.norm_coe_le_norm ψ _)
            hcoefficient

theorem norm_quasiLocalInfiniteLBitFlipCommutator_le_two
    (t : ℝ) (i j : ℕ) (ψ : ContinuousInfiniteLBitAmplitude) :
    ‖quasiLocalInfiniteLBitFlipCommutator t i j ψ‖ ≤
      2 * ‖ψ‖ := by
  rw [ContinuousMap.norm_le _
    (mul_nonneg (by norm_num) (norm_nonneg ψ))]
  intro σ
  rw [quasiLocalInfiniteLBitFlipCommutator_apply, norm_mul]
  calc
    ‖quasiLocalInfiniteLBitHeisenbergFlipPhase t i σ -
          quasiLocalInfiniteLBitHeisenbergFlipPhase t i
            (infiniteLBitFlip j σ)‖ *
        ‖ψ (infiniteLBitFlip j (infiniteLBitFlip i σ))‖
        ≤
      (‖quasiLocalInfiniteLBitHeisenbergFlipPhase t i σ‖ +
        ‖quasiLocalInfiniteLBitHeisenbergFlipPhase t i
          (infiniteLBitFlip j σ)‖) *
        ‖ψ (infiniteLBitFlip j (infiniteLBitFlip i σ))‖ := by
          gcongr
          exact norm_sub_le _ _
    _ ≤ 2 * ‖ψ‖ := by
      rw [norm_quasiLocalInfiniteLBitHeisenbergFlipPhase,
        norm_quasiLocalInfiniteLBitHeisenbergFlipPhase,
        one_add_one_eq_two]
      exact mul_le_mul_of_nonneg_left
        (ContinuousMap.norm_coe_le_norm ψ _) (by norm_num)

/-- Exponential influence cone, clipped by the universal commutator bound. -/
theorem norm_quasiLocalInfiniteLBitFlipCommutator_le_min
    (t : ℝ) (i j : ℕ) (ψ : ContinuousInfiniteLBitAmplitude) :
    ‖quasiLocalInfiniteLBitFlipCommutator t i j ψ‖ ≤
      min
        (2 * ‖ψ‖)
        (|t| * (4 * ((1 : ℝ) / 2) ^ Nat.dist i j *
          quasiLocalInfiniteLBitWeightedMass) * ‖ψ‖) :=
  le_min
    (norm_quasiLocalInfiniteLBitFlipCommutator_le_two
      t i j ψ)
    (norm_quasiLocalInfiniteLBitFlipCommutator_le
      t i j ψ)

/-- Insert one distinguished site into an embedded finite environment
support. -/
def quasiLocalInfiniteLBitIncidentSupport
    (x : ℕ) (F : Finset ℕ) (S : Finset F) :
    {A : Finset ℕ // A.Nonempty} :=
  ⟨insert x
      (S.map (Function.Embedding.subtype fun y : ℕ => y ∈ F)),
    ⟨x, Finset.mem_insert_self _ _⟩⟩

theorem quasiLocalInfiniteLBitIncidentSupport_injective
    (x : ℕ) (F : Finset ℕ) (hxF : x ∉ F) :
    Function.Injective
      (quasiLocalInfiniteLBitIncidentSupport x F) := by
  intro S T hST
  apply Finset.map_injective
    (Function.Embedding.subtype fun y : ℕ => y ∈ F)
  have hval :
      insert x
          (S.map (Function.Embedding.subtype fun y : ℕ => y ∈ F)) =
        insert x
          (T.map (Function.Embedding.subtype fun y : ℕ => y ∈ F)) :=
    congrArg Subtype.val hST
  have hxS :
      x ∉ S.map
        (Function.Embedding.subtype fun y : ℕ => y ∈ F) := by
    simp only [Finset.mem_map, Function.Embedding.coe_subtype,
      Subtype.exists, exists_and_right, exists_eq_right]
    intro hx
    exact hxF hx.1
  have hxT :
      x ∉ T.map
        (Function.Embedding.subtype fun y : ℕ => y ∈ F) := by
    simp only [Finset.mem_map, Function.Embedding.coe_subtype,
      Subtype.exists, exists_and_right, exists_eq_right]
    intro hx
    exact hxF hx.1
  have herase := congrArg (fun A : Finset ℕ => A.erase x) hval
  simpa [hxS, hxT] using herase

/-- Coefficients incident on one site, restricted to a finite environment. -/
noncomputable def quasiLocalInfiniteLBitIncidentRestriction
    (x : ℕ) (F : Finset ℕ) (S : Finset F) : ℝ :=
  quasiLocalInfiniteLBitCoefficient
    (quasiLocalInfiniteLBitIncidentSupport x F S).1

theorem quasiLocalInfiniteLBitIncidentRestriction_linearIndependent
    (x : ℕ) (F : Finset ℕ) (hxF : x ∉ F) :
    LinearIndependent ℚ
      (quasiLocalInfiniteLBitIncidentRestriction x F) := by
  have hcomp :=
    quasiLocalInfiniteLBitCoefficient_linearIndependent.comp
      (quasiLocalInfiniteLBitIncidentSupport x F)
      (quasiLocalInfiniteLBitIncidentSupport_injective x F hxF)
  exact hcomp

/-- Every finite environment of one local flip has maximal temporal rank. -/
theorem quasiLocalInfiniteLBitIncidentRestriction_localFlip_fullRank
    (x : ℕ) (F : Finset ℕ) (hxF : x ∉ F) :
    lbitLocalFlipTemporalRank
      (quasiLocalInfiniteLBitIncidentRestriction x F) =
        2 ^ F.card := by
  simpa using
    lbitLocalFlipTemporalRank_eq_maximal
      (quasiLocalInfiniteLBitIncidentRestriction x F)
      (quasiLocalInfiniteLBitIncidentRestriction_linearIndependent
        x F hxF)

/-- **Infinite recurrence--locality separation law.**
The same infinite coefficient field has maximal local-flip temporal rank in
every finite environment and a volume-independent exponential influence
cone. -/
theorem quasiLocalInfiniteLBit_fullRank_and_commutatorBound
    (x y : ℕ) (F : Finset ℕ) (hxF : x ∉ F)
    (t : ℝ) (ψ : ContinuousInfiniteLBitAmplitude) :
    lbitLocalFlipTemporalRank
        (quasiLocalInfiniteLBitIncidentRestriction x F) =
          2 ^ F.card ∧
      ‖quasiLocalInfiniteLBitFlipCommutator t x y ψ‖ ≤
        min
          (2 * ‖ψ‖)
          (|t| * (4 * ((1 : ℝ) / 2) ^ Nat.dist x y *
            quasiLocalInfiniteLBitWeightedMass) * ‖ψ‖) :=
  ⟨quasiLocalInfiniteLBitIncidentRestriction_localFlip_fullRank
      x F hxF,
    norm_quasiLocalInfiniteLBitFlipCommutator_le_min
      t x y ψ⟩

end

end GaloisForLFunctions.HTGeometry
