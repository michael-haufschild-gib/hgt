import GaloisForLFunctions.HTGeometry.SelfConvolutionSubgroupBoundary
import GaloisForLFunctions.HTGeometry.SelfConsistentRefreshSchedules

/-!
# Exact nonlinear relaxation under uniform refresh

For the finite-group self-consistent model inspired by arXiv:2609.10119, the
uniform law is absorbing under convolution. This gives an exact decomposition
into pure self-convolution and uniform mass: the surviving coefficient squares
at every step. Consequently every positive refresh strength gives a global
doubly exponential bound, even when refresh stops after one step. Arbitrary
later coupling schedules retain the same conclusion. Subgroup-uniform laws
supply exact invariant affine families and their subgroup-index amplitudes.

These are statements about the concrete finite convolution model, not the
paper's interval maps with singularities.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
open Matrix
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Uniform admixture squares its surviving coefficient under self-convolution. -/
theorem probabilityUniform_convolution_affine (q : FiniteProbabilityLaw G) (α : ℝ) (i : G) :
    (∑ j, (α*q.prob (i*j⁻¹)+(1-α)*(uniformNoiseLaw (ι := G)).prob (i*j⁻¹))*
      (α*q.prob j+(1-α)*(uniformNoiseLaw (ι := G)).prob j)) =
      α^(2 : ℕ)*(q.mix (relativeGroupNoise q)).prob i+(1-α^(2 : ℕ))*(uniformNoiseLaw (ι := G)).prob i := by
  let h := q
  let c : ℝ := (Fintype.card G : ℝ)⁻¹
  have hmass : (∑ j, h.prob j) = 1 := h.sum_prob
  have hshift : (∑ j, h.prob (i*j⁻¹)) = 1 :=
    sum_row_of_mem_doublyStochastic (relativeGroupNoise h).property i
  have hconv : (∑ j, h.prob (i*j⁻¹)*h.prob j) = (h.mix (relativeGroupNoise h)).prob i := by
    exact (relativeGroupNoise_prob h h i).symm
  have hcard : (Fintype.card G : ℝ)*c = 1 :=
    mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := G))
  change (∑ j, (α*h.prob (i*j⁻¹)+(1-α)*c)*(α*h.prob j+(1-α)*c)) =
    α^(2 : ℕ)*(h.mix (relativeGroupNoise h)).prob i+(1-α^(2 : ℕ))*c
  have hterm (j : G) : (α*h.prob (i*j⁻¹)+(1-α)*c)*(α*h.prob j+(1-α)*c) =
      α^(2 : ℕ)*(h.prob (i*j⁻¹)*h.prob j)+α*(1-α)*c*h.prob (i*j⁻¹)+
        α*(1-α)*c*h.prob j+(1-α)^(2 : ℕ)*c*c := by ring
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hconv, hshift, hmass,
    mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc
    _ = α^(2 : ℕ)*(h.mix (relativeGroupNoise h)).prob i+2*α*(1-α)*c+(1-α)^(2 : ℕ)*c*((Fintype.card G : ℝ)*c) := by ring
    _ = _ := by rw [hcard]; ring

/-- Subgroup laws give an invariant affine line, with coefficient squared. -/
theorem subgroupUniform_convolution_affine (H : Subgroup G) (α : ℝ) (i : G) :
    (∑ j, (α*(subgroupUniformLaw H).prob (i*j⁻¹)+(1-α)*(uniformNoiseLaw (ι := G)).prob (i*j⁻¹))*
      (α*(subgroupUniformLaw H).prob j+(1-α)*(uniformNoiseLaw (ι := G)).prob j)) =
      α^(2 : ℕ)*(subgroupUniformLaw H).prob i+(1-α^(2 : ℕ))*(uniformNoiseLaw (ι := G)).prob i := by
  have h := probabilityUniform_convolution_affine (subgroupUniformLaw H) α i
  rwa [subgroupUniformLaw_self_convolution] at h

/-- Pure self-convolution without the uniform refresh term. -/
def selfConvolutionOrbit (p : FiniteProbabilityLaw G) : ℕ → FiniteProbabilityLaw G
  | 0 => p
  | n+1 => (selfConvolutionOrbit p n).mix (relativeGroupNoise (selfConvolutionOrbit p n))

/-- Every initial law has an exact refreshed/unrefreshed decomposition. -/
theorem selfConsistentRefreshAtOrbit_exact (r : ℝ) (p : FiniteProbabilityLaw G) (n : ℕ) (i : G) :
    (selfConsistentRefreshAtOrbit r p n).prob i =
      refreshRate r^(2^n-1)*(selfConvolutionOrbit p n).prob i+
        (1-refreshRate r^(2^n-1))*(uniformNoiseLaw (ι := G)).prob i := by
  induction n generalizing i with
  | zero => simp [selfConsistentRefreshAtOrbit, selfConvolutionOrbit]
  | succ n ih =>
    change refreshRate r*((selfConsistentRefreshAtOrbit r p n).mix
      (relativeGroupNoise (selfConsistentRefreshAtOrbit r p n))).prob i+
        (1-refreshRate r)*(uniformNoiseLaw (ι := G)).prob i = _
    rw [relativeGroupNoise_prob]
    simp_rw [ih]
    rw [probabilityUniform_convolution_affine]
    have hexp : 2^(n+1)-1 = (2^n-1)*2+1 := by
      have hp : 0 < 2^n := pow_pos (by omega) n
      rw [pow_succ]
      omega
    have hr : refreshRate r^(2^(n+1)-1) = refreshRate r*(refreshRate r^(2^n-1))^(2 : ℕ) := by
      rw [hexp, pow_succ, pow_mul]
      ring
    rw [hr]
    change _ = refreshRate r*(refreshRate r^(2^n-1))^(2 : ℕ)*
      ((selfConvolutionOrbit p n).mix (relativeGroupNoise (selfConvolutionOrbit p n))).prob i+_
    ring

/-- The residual distance factors exactly into refresh survival and pure-convolution distance. -/
theorem selfConsistentRefreshAtOrbit_distance_exact (r : ℝ) (p : FiniteProbabilityLaw G) (n : ℕ) :
    refreshDistance (selfConsistentRefreshAtOrbit r p n) (uniformNoiseLaw (ι := G)) =
      refreshRate r^(2^n-1)*refreshDistance (selfConvolutionOrbit p n) (uniformNoiseLaw (ι := G)) := by
  unfold refreshDistance
  simp_rw [selfConsistentRefreshAtOrbit_exact]
  have he (a b t : ℝ) : t*a+(1-t)*b-b = t*(a-b) := by ring
  simp_rw [he, abs_mul, abs_of_nonneg (pow_nonneg (refreshRate_pos r).le _), Finset.mul_sum]

/-- Every positive refresh strength yields a global doubly exponential bound, for every initial law. -/
theorem selfConsistentRefreshAtOrbit_global_double_rate (r : ℝ) (p : FiniteProbabilityLaw G) (n : ℕ) :
    refreshDistance (selfConsistentRefreshAtOrbit r p n) (uniformNoiseLaw (ι := G)) ≤
      2*refreshRate r^(2^n-1) := by
  rw [selfConsistentRefreshAtOrbit_distance_exact, mul_comm 2]
  exact mul_le_mul_of_nonneg_left (refreshDistance_le_two _ _) (pow_nonneg (refreshRate_pos r).le _)

/-- Starting from any subgroup law, the full nonlinear orbit has an exact closed formula. -/
theorem selfConsistentRefreshAtOrbit_subgroup (r : ℝ) (H : Subgroup G) (n : ℕ) (i : G) :
    (selfConsistentRefreshAtOrbit r (subgroupUniformLaw H) n).prob i =
      refreshRate r^(2^n-1)*(subgroupUniformLaw H).prob i+
        (1-refreshRate r^(2^n-1))*(uniformNoiseLaw (ι := G)).prob i := by
  induction n generalizing i with
  | zero => simp [selfConsistentRefreshAtOrbit]
  | succ n ih =>
    change refreshRate r*((selfConsistentRefreshAtOrbit r (subgroupUniformLaw H) n).mix
      (relativeGroupNoise (selfConsistentRefreshAtOrbit r (subgroupUniformLaw H) n))).prob i+
        (1-refreshRate r)*(uniformNoiseLaw (ι := G)).prob i = _
    rw [relativeGroupNoise_prob]
    simp_rw [ih]
    rw [subgroupUniform_convolution_affine]
    have hexp : 2^(n+1)-1 = (2^n-1)*2+1 := by
      have hp : 0 < 2^n := pow_pos (by omega) n
      rw [pow_succ]
      omega
    have hr : refreshRate r^(2^(n+1)-1) = refreshRate r*(refreshRate r^(2^n-1))^(2 : ℕ) := by
      rw [hexp, pow_succ, pow_mul]
      ring
    rw [hr]
    ring

/-- The exact distance decays doubly exponentially for every strictly positive refresh strength. -/
theorem selfConsistentRefreshAtOrbit_subgroup_distance (r : ℝ) (H : Subgroup G) (n : ℕ) :
    refreshDistance (selfConsistentRefreshAtOrbit r (subgroupUniformLaw H) n) (uniformNoiseLaw (ι := G)) =
      refreshRate r^(2^n-1)*refreshDistance (subgroupUniformLaw H) (uniformNoiseLaw (ι := G)) := by
  unfold refreshDistance
  simp_rw [selfConsistentRefreshAtOrbit_subgroup]
  have he (a b t : ℝ) : t*a+(1-t)*b-b = t*(a-b) := by ring
  simp_rw [he, abs_mul, abs_of_nonneg (pow_nonneg (refreshRate_pos r).le _), Finset.mul_sum]

omit [DecidableEq G] in
/-- The subgroup index fixes the entire amplitude of the relaxation curve. -/
theorem subgroupUniformLaw_distance (H : Subgroup G) :
    refreshDistance (subgroupUniformLaw H) (uniformNoiseLaw (ι := G)) =
      2*(1-(Nat.card H : ℝ)/(Fintype.card G : ℝ)) := by
  classical
  rw [Nat.card_eq_fintype_card]
  have hh : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos (α := H)
  have hg : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  have hle : (Fintype.card H : ℝ) ≤ Fintype.card G := by
    exact_mod_cast Fintype.card_le_of_injective (fun x : H => (x : G)) Subtype.val_injective
  have hinv : (Fintype.card G : ℝ)⁻¹ ≤ (Fintype.card H : ℝ)⁻¹ := by
    exact (inv_le_inv₀ hg hh).mpr hle
  have hpoint (i : G) : |(subgroupUniformLaw H).prob i-(uniformNoiseLaw (ι := G)).prob i| =
      (subgroupUniformLaw H).prob i+(uniformNoiseLaw (ι := G)).prob i-
        2*(if i ∈ H then (Fintype.card G : ℝ)⁻¹ else 0) := by
    by_cases hi : i ∈ H
    · simp only [subgroupUniformLaw, uniformNoiseLaw, hi, if_true]
      rw [abs_of_nonneg (sub_nonneg.mpr hinv)]
      ring
    · simp [subgroupUniformLaw, uniformNoiseLaw, hi, abs_of_nonneg (inv_pos.mpr hg).le]
  unfold refreshDistance
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, (subgroupUniformLaw H).sum_prob,
    uniformNoiseLaw.sum_prob, ← Finset.mul_sum, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Fintype.card_subtype]
  ring

/-- Exact surviving coefficient for an arbitrary sequence of refreshed transfers. -/
def scheduledRefreshSurvival (r : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n+1 => refreshRate (r n)*scheduledRefreshSurvival r n ^ (2 : ℕ)

omit [Group G] [Fintype G] [DecidableEq G] in
theorem scheduledRefreshSurvival_nonneg (r : ℕ → ℝ) (n : ℕ) :
    0 ≤ scheduledRefreshSurvival r n := by
  cases n with
  | zero => exact zero_le_one
  | succ n => exact mul_nonneg (refreshRate_pos _).le (sq_nonneg _)

/-- Time variation preserves the exact uniform/pure-convolution decomposition. -/
theorem selfConsistentScheduledOrbit_exact (r : ℕ → ℝ) (p : FiniteProbabilityLaw G) (n : ℕ) (i : G) :
    (selfConsistentScheduledOrbit r p n).prob i =
      scheduledRefreshSurvival r n*(selfConvolutionOrbit p n).prob i+
        (1-scheduledRefreshSurvival r n)*(uniformNoiseLaw (ι := G)).prob i := by
  induction n generalizing i with
  | zero => simp [selfConsistentScheduledOrbit, scheduledRefreshSurvival, selfConvolutionOrbit]
  | succ n ih =>
    change refreshRate (r n)*((selfConsistentScheduledOrbit r p n).mix
      (relativeGroupNoise (selfConsistentScheduledOrbit r p n))).prob i+
        (1-refreshRate (r n))*(uniformNoiseLaw (ι := G)).prob i = _
    rw [relativeGroupNoise_prob]
    simp_rw [ih]
    rw [probabilityUniform_convolution_affine]
    simp only [scheduledRefreshSurvival, selfConvolutionOrbit]
    ring

omit [Group G] [Fintype G] [DecidableEq G] in
/-- The first refreshed step controls all later survival, irrespective of later strengths. -/
theorem scheduledRefreshSurvival_first_bound (r : ℕ → ℝ) (n : ℕ) :
    scheduledRefreshSurvival r (n+1) ≤ refreshRate (r 0)^(2^n) := by
  induction n with
  | zero => simp [scheduledRefreshSurvival]
  | succ n ih =>
    change refreshRate (r (n+1))*scheduledRefreshSurvival r (n+1)^(2 : ℕ) ≤ _
    calc
      _ ≤ scheduledRefreshSurvival r (n+1)^(2 : ℕ) :=
        mul_le_of_le_one_left (sq_nonneg _) (refreshRate_lt_one _).le
      _ ≤ (refreshRate (r 0)^(2^n))^(2 : ℕ) :=
        (sq_le_sq₀ (scheduledRefreshSurvival_nonneg _ _)
          (pow_nonneg (refreshRate_pos _).le _)).mpr ih
      _ = _ := by rw [← pow_mul, pow_succ]

/-- Any positive first refresh gives doubly exponential forgetting under every later schedule. -/
theorem selfConsistentScheduledOrbit_double_rate (r : ℕ → ℝ) (p : FiniteProbabilityLaw G) (n : ℕ) :
    refreshDistance (selfConsistentScheduledOrbit r p (n+1)) (uniformNoiseLaw (ι := G)) ≤
      2*refreshRate (r 0)^(2^n) := by
  have he : refreshDistance (selfConsistentScheduledOrbit r p (n+1)) (uniformNoiseLaw (ι := G)) =
      scheduledRefreshSurvival r (n+1)*refreshDistance (selfConvolutionOrbit p (n+1)) (uniformNoiseLaw (ι := G)) := by
    unfold refreshDistance
    simp_rw [selfConsistentScheduledOrbit_exact]
    have hid (a b t : ℝ) : t*a+(1-t)*b-b = t*(a-b) := by ring
    simp_rw [hid, abs_mul, abs_of_nonneg (scheduledRefreshSurvival_nonneg _ _), Finset.mul_sum]
  rw [he]
  calc
    _ ≤ scheduledRefreshSurvival r (n+1)*2 :=
      mul_le_mul_of_nonneg_left (refreshDistance_le_two _ _) (scheduledRefreshSurvival_nonneg _ _)
    _ ≤ _ := by nlinarith [scheduledRefreshSurvival_first_bound r n]

/-- Every real-valued coupling schedule converges: later refresh need not be nonsummable. -/
theorem selfConsistentScheduledOrbit_tendsto (r : ℕ → ℝ) (p : FiniteProbabilityLaw G) :
    Filter.Tendsto (fun n => refreshDistance (selfConsistentScheduledOrbit r p n)
      (uniformNoiseLaw (ι := G))) Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun n : ℕ => 2^n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  have hr := tendsto_pow_atTop_nhds_zero_of_lt_one (refreshRate_pos (r 0)).le
    (refreshRate_lt_one (r 0))
  have hlim : Filter.Tendsto (fun n : ℕ => 2*refreshRate (r 0)^(2^n)) Filter.atTop (nhds 0) := by
    simpa using (hr.comp hp).const_mul 2
  apply (Filter.tendsto_add_atTop_iff_nat 1).mp
  exact squeeze_zero (fun n => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (selfConsistentScheduledOrbit_double_rate r p) hlim

/-- A single refresh followed by pure self-convolution retains an exact surviving coefficient. -/
theorem selfConvolutionOrbit_single_refresh_exact (r : ℝ) (p : FiniteProbabilityLaw G)
    (n : ℕ) (i : G) :
    (selfConvolutionOrbit (selfConsistentRefreshAt r p) n).prob i =
      refreshRate r^(2^n)*(selfConvolutionOrbit p (n+1)).prob i+
        (1-refreshRate r^(2^n))*(uniformNoiseLaw (ι := G)).prob i := by
  induction n generalizing i with
  | zero => simp [selfConvolutionOrbit, selfConsistentRefreshAt]
  | succ n ih =>
    change ((selfConvolutionOrbit (selfConsistentRefreshAt r p) n).mix
      (relativeGroupNoise (selfConvolutionOrbit (selfConsistentRefreshAt r p) n))).prob i = _
    rw [relativeGroupNoise_prob]
    simp_rw [ih]
    rw [probabilityUniform_convolution_affine]
    have hr : refreshRate r^(2^(n+1)) = (refreshRate r^(2^n))^(2 : ℕ) := by
      rw [pow_succ, pow_mul]
    rw [hr]
    rfl

/-- Even with refresh switched off after the first step, error decays doubly exponentially. -/
theorem selfConvolutionOrbit_single_refresh_bound (r : ℝ) (p : FiniteProbabilityLaw G) (n : ℕ) :
    refreshDistance (selfConvolutionOrbit (selfConsistentRefreshAt r p) n) (uniformNoiseLaw (ι := G)) ≤
      2*refreshRate r^(2^n) := by
  have he : refreshDistance (selfConvolutionOrbit (selfConsistentRefreshAt r p) n) (uniformNoiseLaw (ι := G)) =
      refreshRate r^(2^n)*refreshDistance (selfConvolutionOrbit p (n+1)) (uniformNoiseLaw (ι := G)) := by
    unfold refreshDistance
    simp_rw [selfConvolutionOrbit_single_refresh_exact]
    have hid (a b t : ℝ) : t*a+(1-t)*b-b = t*(a-b) := by ring
    simp_rw [hid, abs_mul, abs_of_nonneg (pow_nonneg (refreshRate_pos _).le _), Finset.mul_sum]
  rw [he, mul_comm 2]
  exact mul_le_mul_of_nonneg_left (refreshDistance_le_two _ _) (pow_nonneg (refreshRate_pos _).le _)

/-- One positive uniform pulse suffices for convergence under all later pure self-convolutions. -/
theorem selfConvolutionOrbit_single_refresh_tendsto (r : ℝ) (p : FiniteProbabilityLaw G) :
    Filter.Tendsto (fun n => refreshDistance (selfConvolutionOrbit (selfConsistentRefreshAt r p) n)
      (uniformNoiseLaw (ι := G))) Filter.atTop (nhds 0) := by
  have hp : Filter.Tendsto (fun n : ℕ => 2^n) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by omega)
  have hr := tendsto_pow_atTop_nhds_zero_of_lt_one (refreshRate_pos r).le (refreshRate_lt_one r)
  have hlim : Filter.Tendsto (fun n : ℕ => 2*refreshRate r^(2^n)) Filter.atTop (nhds 0) := by
    simpa using (hr.comp hp).const_mul 2
  exact squeeze_zero (fun n => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (selfConvolutionOrbit_single_refresh_bound r p) hlim

end GaloisForLFunctions.HTGeometry
