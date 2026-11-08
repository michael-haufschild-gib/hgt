import GaloisForLFunctions.HeightHomotopyArithmeticCounts.KernelHilbertCompletion

/-!
# Operator-norm convergence of the actual torsion forms

The original spacing kernels define continuous symmetric bilinear forms on
all positively conductor-weighted Hilbert probe spaces. Their pair series are
absolutely convergent, and the raw forms remain positive. The exact scalar
counterterm is the ordinary coefficient pairing. After this normalization,
the operators converge to the arithmetic limit with a uniform power rate.
-/

noncomputable section
open Finset Filter Topology
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticEffectivityTheory ArithmeticIntersectionTheory

/-- Every positive regulator gives a bounded absolute scalar-renormalized pairing. -/
theorem spacingRenormalizedKernel_weighted_absolute_bound (δ : ℝ) (hδ : 0 < δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (x : ℕ → ℝ), (∀ n ∈ S, 0 < n) →
      (∑ m ∈ S, ∑ n ∈ S, |x m*x n*spacingRenormalizedKernel ε m n|) ≤
        C*∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
  obtain ⟨A, hA, hL⟩ := spacingLimitKernel_weighted_absolute_bound δ hδ
  obtain ⟨D, hD, hE⟩ := spacingKernelError_weighted_absolute_bound δ hδ
  refine ⟨A+D*ε^(min (δ/8) 1), by positivity, ?_⟩
  intro S x hS
  have hpoint (m n : ℕ) : |x m*x n*spacingRenormalizedKernel ε m n| ≤
      |x m*x n*spacingLimitKernel m n|+|x m*x n*spacingKernelError ε m n| := by
    rw [spacingRenormalizedKernel_eq, mul_add]
    exact abs_add_le _ _
  calc _ ≤ ∑ m ∈ S, ∑ n ∈ S,
        (|x m*x n*spacingLimitKernel m n|+|x m*x n*spacingKernelError ε m n|) :=
        sum_le_sum fun m _ => sum_le_sum fun n _ => hpoint m n
       _ = (∑ m ∈ S, ∑ n ∈ S, |x m*x n*spacingLimitKernel m n|)+
        (∑ m ∈ S, ∑ n ∈ S, |x m*x n*spacingKernelError ε m n|) := by
        simp only [sum_add_distrib]
       _ ≤ A*(∑ n ∈ S, (n:ℝ)^δ*(x n)^2)+
        D*ε^(min (δ/8) 1)*(∑ n ∈ S, (n:ℝ)^δ*(x n)^2) :=
        add_le_add (hL S x hS) (hE ε S x hε hS)
       _ = _ := by ring

/-- The original spacing-regulated torsion kernel before scalar renormalization. -/
def spacingRawKernel (ε : ℝ) (m n : ℕ) : ℝ :=
  twistedEnergy (spacingRadius ε m n) m n

/-- The scalar counterterm is exactly the conductor diagonal. -/
theorem spacingRawKernel_eq (ε : ℝ) (m n : ℕ) :
    spacingRawKernel ε m n=spacingRenormalizedKernel ε m n-
      if m=n then Real.log (2*ε) else 0 := by
  unfold spacingRawKernel spacingRenormalizedKernel
  ring

/-- Positive conductor weight dominates the ordinary finite square norm. -/
theorem sum_sq_le_weighted_mass (δ : ℝ) (hδ : 0 < δ)
    (S : Finset ℕ) (x : ℕ → ℝ) (hS : ∀ n ∈ S, 0 < n) :
    (∑ n ∈ S, (x n)^2) ≤ ∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
  apply sum_le_sum
  intro n hn
  have hw : (1:ℝ) ≤ (n:ℝ)^δ :=
    Real.one_le_rpow (by exact_mod_cast hS n hn) hδ.le
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (sq_nonneg (x n))

/-- The original positive torsion form is bounded on every positively weighted probe space. -/
theorem spacingRawKernel_weighted_absolute_bound (δ : ℝ) (hδ : 0 < δ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ℕ) (x : ℕ → ℝ), (∀ n ∈ S, 0 < n) →
      (∑ m ∈ S, ∑ n ∈ S, |x m*x n*spacingRawKernel ε m n|) ≤
        C*∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
  classical
  obtain ⟨A, hA, hR⟩ := spacingRenormalizedKernel_weighted_absolute_bound δ hδ ε hε
  refine ⟨A+|Real.log (2*ε)|, add_pos_of_pos_of_nonneg hA (abs_nonneg _), ?_⟩
  intro S x hS
  have hd : (∑ m ∈ S, ∑ n ∈ S, |x m*x n*(if m=n then Real.log (2*ε) else 0)|)=
      |Real.log (2*ε)| *∑ n ∈ S, (x n)^2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro m hm
    rw [sum_eq_single m]
    · rw [if_pos rfl, abs_mul, ← pow_two, abs_of_nonneg (sq_nonneg (x m)), mul_comm]
    · intro n _hn hnm
      rw [if_neg hnm.symm, mul_zero, abs_zero]
    · exact fun h => (h hm).elim
  have hpoint (m n : ℕ) : |x m*x n*spacingRawKernel ε m n| ≤
      |x m*x n*spacingRenormalizedKernel ε m n|+
        |x m*x n*(if m=n then Real.log (2*ε) else 0)| := by
    rw [spacingRawKernel_eq, mul_sub]
    exact abs_sub _ _
  calc _ ≤ ∑ m ∈ S, ∑ n ∈ S,
        (|x m*x n*spacingRenormalizedKernel ε m n|+
          |x m*x n*(if m=n then Real.log (2*ε) else 0)|) :=
        sum_le_sum fun m _ => sum_le_sum fun n _ => hpoint m n
       _ = (∑ m ∈ S, ∑ n ∈ S, |x m*x n*spacingRenormalizedKernel ε m n|)+
        |Real.log (2*ε)| *∑ n ∈ S, (x n)^2 := by
        simp only [sum_add_distrib]
        rw [hd]
       _ ≤ A*(∑ n ∈ S, (n:ℝ)^δ*(x n)^2)+
        |Real.log (2*ε)| *(∑ n ∈ S, (n:ℝ)^δ*(x n)^2) :=
        add_le_add (hR S x hS)
          (mul_le_mul_of_nonneg_left (sum_sq_le_weighted_mass δ hδ S x hS) (abs_nonneg _))
       _ = _ := by ring

/-- All three original arithmetic pair series converge absolutely on every pair of probes. -/
theorem spacingOperators_absolute (δ : ℝ) (hδ : 0 < δ)
    (ε : ℝ) (hε : 0 < ε) (u v : WeightedProbe δ) :
    Summable (fun p : ℕ×ℕ =>
      |probeCoefficients δ u p.1*probeCoefficients δ v p.2*spacingLimitKernel p.1 p.2|) ∧
    Summable (fun p : ℕ×ℕ =>
      |probeCoefficients δ u p.1*probeCoefficients δ v p.2*spacingRenormalizedKernel ε p.1 p.2|) ∧
    Summable (fun p : ℕ×ℕ =>
      |probeCoefficients δ u p.1*probeCoefficients δ v p.2*spacingRawKernel ε p.1 p.2|) := by
  obtain ⟨A, hA, hL⟩ := spacingLimitKernel_weighted_absolute_bound δ hδ
  obtain ⟨B, hB, hR⟩ := spacingRenormalizedKernel_weighted_absolute_bound δ hδ ε hε
  obtain ⟨C, hC, hT⟩ := spacingRawKernel_weighted_absolute_bound δ hδ ε hε
  exact ⟨(weightedKernelPairing_absolute δ A hA.le spacingLimitKernel hL u v).1,
    (weightedKernelPairing_absolute δ B hB.le (spacingRenormalizedKernel ε) hR u v).1,
    (weightedKernelPairing_absolute δ C hC.le (spacingRawKernel ε) hT u v).1⟩

/-- Positive conductor weight makes the ordinary coefficient scalar product absolutely summable. -/
theorem summable_probeCoefficients_pair (δ : ℝ) (hδ : 0 < δ) (u v : WeightedProbe δ) :
    Summable (fun n : ℕ => |probeCoefficients δ u n*probeCoefficients δ v n|) := by
  have hmajor := ((probeCoefficients_summable δ u).add (probeCoefficients_summable δ v)).div_const 2
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) ?_ hmajor
  intro n
  by_cases hn : n=0
  · subst n
    simp only [probeCoefficients_zero, zero_pow (by decide : 2≠0), mul_zero,
      abs_zero, zero_add, zero_div, le_refl]
  have hw : (1:ℝ) ≤ (n:ℝ)^δ := Real.one_le_rpow
    (by exact_mod_cast Nat.pos_of_ne_zero hn) hδ.le
  have hu : (probeCoefficients δ u n)^2 ≤ (n:ℝ)^δ*(probeCoefficients δ u n)^2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (sq_nonneg (probeCoefficients δ u n))
  have hv : (probeCoefficients δ v n)^2 ≤ (n:ℝ)^δ*(probeCoefficients δ v n)^2 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hw (sq_nonneg (probeCoefficients δ v n))
  rw [abs_mul]
  calc _ ≤ ((probeCoefficients δ u n)^2+(probeCoefficients δ v n)^2)/2 := by
        nlinarith only [sq_nonneg (|probeCoefficients δ u n|-|probeCoefficients δ v n|),
          sq_abs (probeCoefficients δ u n), sq_abs (probeCoefficients δ v n)]
       _ ≤ _ := div_le_div_of_nonneg_right (add_le_add hu hv) (by norm_num)

/-- Continuous arithmetic limit on the complete weighted probe carrier. -/
def spacingLimitOperator (δ : ℝ) (hδ : 0 < δ) :
    WeightedProbe δ →L[ℝ] WeightedProbe δ →L[ℝ] ℝ :=
  let H := spacingLimitKernel_weighted_absolute_bound δ hδ
  weightedKernelContinuous δ (Classical.choose H) (Classical.choose_spec H).1.le
    spacingLimitKernel (Classical.choose_spec H).2

/-- The scalar-renormalized operator is constructed from its original torsion kernel. -/
def spacingRenormalizedOperator (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) :
    WeightedProbe δ →L[ℝ] WeightedProbe δ →L[ℝ] ℝ :=
  if hε : 0 < ε then
    let H := spacingRenormalizedKernel_weighted_absolute_bound δ hδ ε hε
    weightedKernelContinuous δ (Classical.choose H) (Classical.choose_spec H).1.le
      (spacingRenormalizedKernel ε) (Classical.choose_spec H).2
  else 0

/-- The original torsion operator before scalar renormalization. -/
def spacingRawOperator (δ : ℝ) (hδ : 0 < δ) (ε : ℝ) :
    WeightedProbe δ →L[ℝ] WeightedProbe δ →L[ℝ] ℝ :=
  if hε : 0 < ε then
    let H := spacingRawKernel_weighted_absolute_bound δ hδ ε hε
    weightedKernelContinuous δ (Classical.choose H) (Classical.choose_spec H).1.le
      (spacingRawKernel ε) (Classical.choose_spec H).2
  else 0

@[simp] theorem spacingLimitOperator_apply (δ : ℝ) (hδ : 0 < δ) (u v : WeightedProbe δ) :
    spacingLimitOperator δ hδ u v=weightedKernelPairing δ spacingLimitKernel u v := rfl

/-- The continuous regulated operator is the original absolutely convergent series. -/
theorem spacingRenormalizedOperator_apply (δ : ℝ) (hδ : 0 < δ)
    (ε : ℝ) (hε : 0 < ε) (u v : WeightedProbe δ) :
    spacingRenormalizedOperator δ hδ ε u v=
      weightedKernelPairing δ (spacingRenormalizedKernel ε) u v := by
  rw [spacingRenormalizedOperator, dif_pos hε]
  rfl

/-- The raw operator retains the original torsion-energy series. -/
theorem spacingRawOperator_apply (δ : ℝ) (hδ : 0 < δ)
    (ε : ℝ) (hε : 0 < ε) (u v : WeightedProbe δ) :
    spacingRawOperator δ hδ ε u v=weightedKernelPairing δ (spacingRawKernel ε) u v := by
  rw [spacingRawOperator, dif_pos hε]
  rfl

/-- The limiting continuous form is symmetric. -/
theorem spacingLimitOperator_comm (δ : ℝ) (hδ : 0 < δ) (u v : WeightedProbe δ) :
    spacingLimitOperator δ hδ u v=spacingLimitOperator δ hδ v u :=
  weightedKernelPairing_comm δ spacingLimitKernel spacingLimitKernel_comm u v

/-- The actual regulated continuous form is symmetric. -/
theorem spacingRenormalizedOperator_comm (δ : ℝ) (hδ : 0 < δ)
    (ε : ℝ) (hε : 0 < ε) (u v : WeightedProbe δ) :
    spacingRenormalizedOperator δ hδ ε u v=spacingRenormalizedOperator δ hδ ε v u := by
  rw [spacingRenormalizedOperator_apply δ hδ ε hε,
    spacingRenormalizedOperator_apply δ hδ ε hε]
  exact weightedKernelPairing_comm δ (spacingRenormalizedKernel ε)
    (spacingRenormalizedKernel_comm ε) u v

/-- Subtracting the full continuous forms gives the original mixed spacing-error series. -/
theorem spacingOperator_difference_apply (δ : ℝ) (hδ : 0 < δ)
    (ε : ℝ) (hε : 0 < ε) (u v : WeightedProbe δ) :
    (spacingRenormalizedOperator δ hδ ε-spacingLimitOperator δ hδ) u v=
      weightedKernelPairing δ (spacingKernelError ε) u v := by
  obtain ⟨A, hA, hL⟩ := spacingLimitKernel_weighted_absolute_bound δ hδ
  obtain ⟨D, hD, hE⟩ := spacingKernelError_weighted_absolute_bound δ hδ
  have hLs := (weightedKernelPairing_absolute δ A hA.le spacingLimitKernel hL u v).1.of_abs
  have hEs := (weightedKernelPairing_absolute δ (D*ε^(min (δ/8) 1)) (by positivity)
    (spacingKernelError ε) (fun S x hS => hE ε S x hε hS) u v).1.of_abs
  simp only [sub_apply, spacingLimitOperator_apply]
  rw [spacingRenormalizedOperator_apply δ hδ ε hε]
  unfold weightedKernelPairing
  simp_rw [spacingRenormalizedKernel_eq, mul_add]
  rw [hLs.tsum_add hEs]
  ring

/-- The original renormalized torsion operators converge with every admissible weighted rate. -/
theorem spacingOperator_norm_error_rate (δ α : ℝ) (hδ : 0 < δ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hgap : 2*α < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      ‖spacingRenormalizedOperator δ hδ ε-spacingLimitOperator δ hδ‖ ≤ C*ε^α := by
  obtain ⟨C, hC, hfinite⟩ := spacingKernelError_weighted_absolute_rate δ α hα hα1 hgap
  refine ⟨4*C, by positivity, ?_⟩
  intro ε hε
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro u v
  rw [spacingOperator_difference_apply δ hδ ε hε]
  have h := weightedKernelBilinear_bound δ (C*ε^α) (by positivity)
    (spacingKernelError ε) (fun S x hS => hfinite ε S x hε hS) u v
  change ‖weightedKernelPairing δ (spacingKernelError ε) u v‖ ≤
    4*(C*ε^α)*‖u‖*‖v‖ at h
  calc _ ≤ 4*(C*ε^α)*‖u‖*‖v‖ := h
       _ = _ := by ring

/-- Operator-norm convergence holds on every positively conductor-weighted Hilbert space. -/
theorem tendsto_spacingRenormalizedOperator (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (spacingRenormalizedOperator δ hδ) (𝓝[>] (0:ℝ))
      (𝓝 (spacingLimitOperator δ hδ)) := by
  let α := min (δ/8) 1
  have hα : 0 < α := lt_min (by positivity) zero_lt_one
  have hgap : 2*α < δ := by
    have hm := min_le_left (δ/8) (1:ℝ)
    dsimp only [α]
    linarith only [hm, hδ]
  obtain ⟨C, _hC, hbound⟩ := spacingOperator_norm_error_rate δ α hδ hα (min_le_right _ _) hgap
  have hc : ContinuousAt (fun ε : ℝ => ε^α) 0 :=
    Real.continuousAt_rpow_const 0 α (Or.inr hα.le)
  have hp := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  rw [Real.zero_rpow hα.ne'] at hp
  have hmajor := hp.const_mul C
  simp only [mul_zero] at hmajor
  have hnorm : Tendsto (fun ε : ℝ =>
      ‖spacingRenormalizedOperator δ hδ ε-spacingLimitOperator δ hδ‖)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun ε : ℝ =>
      norm_nonneg (spacingRenormalizedOperator δ hδ ε-spacingLimitOperator δ hδ)) _ hmajor
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hbound ε hε
  rw [Metric.tendsto_nhds (u := spacingRenormalizedOperator δ hδ)]
  intro η hη
  filter_upwards [hnorm.eventually (Iio_mem_nhds hη)] with ε hε
  rw [dist_eq_norm (spacingRenormalizedOperator δ hδ ε) (spacingLimitOperator δ hδ)]
  exact hε

#print axioms spacingLimitOperator
#print axioms spacingRenormalizedOperator
#print axioms spacingRawOperator
#print axioms spacingOperator_difference_apply
#print axioms spacingOperator_norm_error_rate
#print axioms tendsto_spacingRenormalizedOperator

/-- The ordinary coefficient pairing is the conductor diagonal. -/
def probeDiagonalKernel (m n : ℕ) : ℝ := if m=n then 1 else 0

/-- Positive conductor weight bounds the scalar diagonal. -/
theorem probeDiagonalKernel_weighted_bound (δ : ℝ) (hδ : 0 < δ)
    (S : Finset ℕ) (x : ℕ → ℝ) (hS : ∀ n ∈ S, 0 < n) :
    (∑ m ∈ S, ∑ n ∈ S, |x m*x n*probeDiagonalKernel m n|) ≤
      ∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
  classical
  have hd : (∑ m ∈ S, ∑ n ∈ S, |x m*x n*probeDiagonalKernel m n|)=∑ n ∈ S, (x n)^2 := by
    apply sum_congr rfl
    intro m hm
    rw [sum_eq_single m]
    · simp only [probeDiagonalKernel, if_true, mul_one, ← pow_two, abs_of_nonneg (sq_nonneg (x m))]
    · intro n _hn hnm
      simp only [probeDiagonalKernel, if_neg hnm.symm, mul_zero, abs_zero]
    · exact fun h => (h hm).elim
  rw [hd]
  exact sum_sq_le_weighted_mass δ hδ S x hS

/-- The diagonal pair series equals the ordinary coefficient scalar product. -/
theorem weightedKernelPairing_diagonal (δ : ℝ) (hδ : 0 < δ) (u v : WeightedProbe δ) :
    weightedKernelPairing δ probeDiagonalKernel u v=
      ∑' n : ℕ, probeCoefficients δ u n*probeCoefficients δ v n := by
  have hb (S : Finset ℕ) (x : ℕ → ℝ) (hS : ∀ n ∈ S, 0 < n) :
      (∑ m ∈ S, ∑ n ∈ S, |x m*x n*probeDiagonalKernel m n|) ≤
        1*∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
    simpa only [one_mul] using probeDiagonalKernel_weighted_bound δ hδ S x hS
  have hs := (weightedKernelPairing_absolute δ 1 zero_le_one probeDiagonalKernel hb u v).1.of_abs
  unfold weightedKernelPairing
  rw [hs.tsum_prod]
  apply tsum_congr
  intro m
  rw [tsum_eq_single m]
  · simp only [probeDiagonalKernel, if_true, mul_one]
  · intro n hnm
    simp only [probeDiagonalKernel, if_neg hnm.symm, mul_zero]

private theorem spacingRenormalizedKernel_eq_raw_diagonal (ε : ℝ) (m n : ℕ) :
    spacingRenormalizedKernel ε m n=spacingRawKernel ε m n+Real.log (2*ε)*probeDiagonalKernel m n := by
  unfold spacingRenormalizedKernel spacingRawKernel probeDiagonalKernel
  by_cases h : m=n <;> simp only [h, if_true, if_false, mul_one, mul_zero]

/-- The infinite operator counterterm is exactly the original unweighted coefficient pairing. -/
theorem spacingOperator_scalar_counterterm (δ : ℝ) (hδ : 0 < δ)
    (ε : ℝ) (hε : 0 < ε) (u v : WeightedProbe δ) :
    spacingRenormalizedOperator δ hδ ε u v=spacingRawOperator δ hδ ε u v+
      Real.log (2*ε)*(∑' n : ℕ, probeCoefficients δ u n*probeCoefficients δ v n) := by
  obtain ⟨A, hA, hraw⟩ := spacingRawKernel_weighted_absolute_bound δ hδ ε hε
  have hraws := (weightedKernelPairing_absolute δ A hA.le (spacingRawKernel ε) hraw u v).1.of_abs
  have hd (S : Finset ℕ) (x : ℕ → ℝ) (hS : ∀ n ∈ S, 0 < n) :
      (∑ m ∈ S, ∑ n ∈ S, |x m*x n*probeDiagonalKernel m n|) ≤
        1*∑ n ∈ S, (n:ℝ)^δ*(x n)^2 := by
    simpa only [one_mul] using probeDiagonalKernel_weighted_bound δ hδ S x hS
  have hds := (weightedKernelPairing_absolute δ 1 zero_le_one probeDiagonalKernel hd u v).1.of_abs
  rw [spacingRenormalizedOperator_apply δ hδ ε hε, spacingRawOperator_apply δ hδ ε hε]
  have hsplit (p : ℕ×ℕ) :
      probeCoefficients δ u p.1*probeCoefficients δ v p.2*spacingRenormalizedKernel ε p.1 p.2=
        probeCoefficients δ u p.1*probeCoefficients δ v p.2*spacingRawKernel ε p.1 p.2+
        Real.log (2*ε)*(probeCoefficients δ u p.1*probeCoefficients δ v p.2*probeDiagonalKernel p.1 p.2) := by
    rw [spacingRenormalizedKernel_eq_raw_diagonal]
    ring
  unfold weightedKernelPairing
  simp_rw [hsplit]
  rw [hraws.tsum_add (hds.mul_left (Real.log (2*ε))), tsum_mul_left]
  exact congrArg (fun z : ℝ =>
    (∑' p : ℕ×ℕ, probeCoefficients δ u p.1*probeCoefficients δ v p.2*spacingRawKernel ε p.1 p.2)+
      Real.log (2*ε)*z) (weightedKernelPairing_diagonal δ hδ u v)

/-- The original positive continuous torsion pairing is symmetric. -/
theorem spacingRawOperator_comm (δ : ℝ) (hδ : 0 < δ)
    (ε : ℝ) (hε : 0 < ε) (u v : WeightedProbe δ) :
    spacingRawOperator δ hδ ε u v=spacingRawOperator δ hδ ε v u := by
  have hu := spacingOperator_scalar_counterterm δ hδ ε hε u v
  have hv := spacingOperator_scalar_counterterm δ hδ ε hε v u
  have hc := spacingRenormalizedOperator_comm δ hδ ε hε u v
  have hd : (∑' n : ℕ, probeCoefficients δ u n*probeCoefficients δ v n)=
      ∑' n : ℕ, probeCoefficients δ v n*probeCoefficients δ u n :=
    tsum_congr fun n => mul_comm _ _
  rw [hd] at hu
  linarith only [hu, hv, hc]

/-- The original regulated torsion operator remains positive on the full infinite carrier. -/
theorem spacingRawOperator_nonneg (δ : ℝ) (hδ : 0 < δ)
    (ε : ℝ) (hε : 0 < ε) (u : WeightedProbe δ) :
    0 ≤ spacingRawOperator δ hδ ε u u := by
  classical
  obtain ⟨A, hA, hraw⟩ := spacingRawKernel_weighted_absolute_bound δ hδ ε hε
  have hs := (weightedKernelPairing_absolute δ A hA.le (spacingRawKernel ε) hraw u u).1.of_abs
  let x := probeCoefficients δ u
  have hx0 : x 0=0 := rfl
  have ht : Tendsto (fun N : ℕ => ∑ p ∈ range N ×ˢ range N,
      x p.1*x p.2*spacingRawKernel ε p.1 p.2) atTop
      (𝓝 (weightedKernelPairing δ (spacingRawKernel ε) u u)) := by
    apply hs.hasSum.comp
    apply tendsto_atTop_finset_of_monotone
    · intro a b hab
      exact product_subset_product (range_subset_range.mpr hab) (range_subset_range.mpr hab)
    · intro p
      refine ⟨max p.1 p.2+1, ?_⟩
      simp only [mem_product, mem_range]
      exact ⟨by omega, by omega⟩
  rw [spacingRawOperator_apply δ hδ ε hε]
  apply ge_of_tendsto' ht
  intro N
  let S := (range N).filter (fun n => 0 < n)
  have hnzero (n : ℕ) (hn : n∈range N) (hnot : n∉S) : n=0 := by
    by_contra h0
    exact hnot (mem_filter.mpr ⟨hn, Nat.pos_of_ne_zero h0⟩)
  have hinner (m : ℕ) : (∑ n ∈ S, x m*x n*spacingRawKernel ε m n)=
      ∑ n ∈ range N, x m*x n*spacingRawKernel ε m n := by
    apply sum_subset (filter_subset _ _)
    intro n hn hnot
    rw [hnzero n hn hnot, hx0, mul_zero, zero_mul]
  have heq : spacingForm ε S x=∑ p ∈ range N ×ˢ range N,
      x p.1*x p.2*spacingRawKernel ε p.1 p.2 := by
    rw [sum_product]
    change (∑ m ∈ S, ∑ n ∈ S, x m*x n*spacingRawKernel ε m n)=_
    simp_rw [hinner]
    apply sum_subset (filter_subset _ _)
    intro m hm hnot
    simp only [hnzero m hm hnot, hx0, zero_mul, sum_const_zero]
  rw [← heq]
  exact spacingForm_nonneg hε (fun n hn => (mem_filter.mp hn).2) x

#print axioms spacingOperators_absolute
#print axioms summable_probeCoefficients_pair
#print axioms spacingLimitOperator_comm
#print axioms spacingRawOperator_comm
#print axioms spacingOperator_scalar_counterterm
#print axioms spacingRawOperator_nonneg

end GaloisForLFunctions.HeightHomotopyArithmeticCounts
