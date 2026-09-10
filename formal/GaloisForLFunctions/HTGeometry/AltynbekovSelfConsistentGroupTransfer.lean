import GaloisForLFunctions.HTGeometry.FiniteNoiseInformationBoundary

/-!
# Closed nonlinear transfer dynamics on finite group probability laws

Altynbekov--Olimov--Ruziboev, arXiv:2609.10119, Theorem 2.1 and Lemma 3.12
use weak coupling and an asymmetric contraction estimate to construct an
attracting density. On the corpus's finite group convolution kernels, uniform
refresh supplies an explicit nonlinear instance with no unresolved analytic inputs.

For every finite group and every real coupling parameter, the current law
chooses its own convolution kernel. Any strictly positive uniform refresh gives
an explicit unique fixed probability law and global exponential convergence.
The estimate toward this core is stronger than the available pairwise estimate.
At quarter coupling, the exact quadratic residual gives a uniform doubly
exponential error bound. The interval-map and Sobolev assertions of the paper
are not claimed here; these are closed results for the specified native kernels.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
open Matrix
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Full L1 distance between two finite probability laws. -/
def refreshDistance (p q : FiniteProbabilityLaw G) : ℝ :=
  ∑ i, |p.prob i-q.prob i|

/-- Varying the noise law is nonexpansive when the signal law is fixed. -/
theorem relativeGroupNoise_noise_distance (p q r : FiniteProbabilityLaw G) :
    refreshDistance (r.mix (relativeGroupNoise p)) (r.mix (relativeGroupNoise q)) ≤
      refreshDistance p q := by
  unfold refreshDistance
  simp_rw [relativeGroupNoise_prob, ← Finset.sum_sub_distrib, ← sub_mul]
  calc
    (∑ i, |∑ j, (p.prob (i*j⁻¹)-q.prob (i*j⁻¹))*r.prob j|) ≤
        ∑ i, ∑ j, |(p.prob (i*j⁻¹)-q.prob (i*j⁻¹))*r.prob j| :=
      Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, (∑ i, |p.prob i-q.prob i|) * r.prob j := by
      simp_rw [abs_mul, abs_of_nonneg (r.nonneg _)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul]
      congr 1
      exact Equiv.sum_comp (Equiv.mulRight j⁻¹) (fun i => |p.prob i-q.prob i|)
    _ = _ := by rw [← Finset.mul_sum, r.sum_prob, mul_one]

/-- Self-convolution is two-Lipschitz on the complete finite probability simplex. -/
theorem relativeGroupNoise_self_distance (p q : FiniteProbabilityLaw G) :
    refreshDistance (p.mix (relativeGroupNoise p)) (q.mix (relativeGroupNoise q)) ≤
      2 * refreshDistance p q := by
  have hnoise := relativeGroupNoise_noise_distance p q p
  have hsignal := relativeGroupNoise_totalVariation_le q p q
  have htriangle :
      refreshDistance (p.mix (relativeGroupNoise p)) (q.mix (relativeGroupNoise q)) ≤
        refreshDistance (p.mix (relativeGroupNoise p)) (p.mix (relativeGroupNoise q)) +
        refreshDistance (p.mix (relativeGroupNoise q)) (q.mix (relativeGroupNoise q)) := by
    unfold refreshDistance
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ => abs_sub_le _ _ _
  change refreshDistance (p.mix (relativeGroupNoise q)) (q.mix (relativeGroupNoise q)) ≤
    refreshDistance p q at hsignal
  linarith

/-- A nonlinear transfer: one quarter self-convolution, three quarters uniform refresh. -/
def selfConsistentRefresh (p : FiniteProbabilityLaw G) : FiniteProbabilityLaw G where
  prob i := (p.mix (relativeGroupNoise p)).prob i / 4 + 3/4 * (uniformNoiseLaw (ι := G)).prob i
  nonneg i := add_nonneg (div_nonneg ((p.mix (relativeGroupNoise p)).nonneg i) (by positivity))
    (mul_nonneg (by positivity) (uniformNoiseLaw.nonneg i))
  sum_prob := by
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum,
      (p.mix (relativeGroupNoise p)).sum_prob, uniformNoiseLaw.sum_prob]
    ring

theorem selfConsistentRefresh_distance (p q : FiniteProbabilityLaw G) :
    refreshDistance (selfConsistentRefresh p) (selfConsistentRefresh q) =
      (1/4 : ℝ) * refreshDistance (p.mix (relativeGroupNoise p)) (q.mix (relativeGroupNoise q)) := by
  unfold refreshDistance
  simp only [selfConsistentRefresh]
  have he (a b c : ℝ) : a/4 + 3/4*c - (b/4 + 3/4*c) = (a-b)/4 := by ring
  simp_rw [he, abs_div]
  simp only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4), ← Finset.sum_div]
  ring

theorem selfConsistentRefresh_contraction (p q : FiniteProbabilityLaw G) :
    refreshDistance (selfConsistentRefresh p) (selfConsistentRefresh q) ≤
      (1/2 : ℝ) * refreshDistance p q := by
  rw [selfConsistentRefresh_distance]
  have h := relativeGroupNoise_self_distance p q
  linarith

/-- Uniform density is fixed under every group-noise kernel. -/
theorem relativeGroupNoise_uniform (p : FiniteProbabilityLaw G) :
    ((uniformNoiseLaw (ι := G)).mix (relativeGroupNoise p)).prob =
      (uniformNoiseLaw (ι := G)).prob := by
  funext i
  change (∑ j, (relativeGroupNoise p).val i j * (Fintype.card G : ℝ)⁻¹) = _
  rw [← Finset.sum_mul, sum_row_of_mem_doublyStochastic (relativeGroupNoise p).property, one_mul]
  rfl

theorem selfConsistentRefresh_uniform :
    (selfConsistentRefresh (uniformNoiseLaw (ι := G))).prob =
      (uniformNoiseLaw (ι := G)).prob := by
  funext i
  change ((uniformNoiseLaw (ι := G)).mix (relativeGroupNoise uniformNoiseLaw)).prob i / 4 +
    3/4 * (uniformNoiseLaw (ι := G)).prob i = _
  rw [relativeGroupNoise_uniform]
  ring

/-- All iterates are actual probability laws, including arbitrary initial laws. -/
def selfConsistentRefreshOrbit (p : FiniteProbabilityLaw G) : ℕ → FiniteProbabilityLaw G
  | 0 => p
  | n+1 => selfConsistentRefresh (selfConsistentRefreshOrbit p n)

/-- Global exponential attraction, with no regularity or contraction premise. -/
theorem selfConsistentRefreshOrbit_distance (p q : FiniteProbabilityLaw G) (n : ℕ) :
    refreshDistance (selfConsistentRefreshOrbit p n) (selfConsistentRefreshOrbit q n) ≤
      (1/2 : ℝ)^n * refreshDistance p q := by
  induction n with
  | zero => simp [selfConsistentRefreshOrbit]
  | succ n ih =>
    exact (selfConsistentRefresh_contraction _ _).trans
      (by simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left ih (by positivity : (0:ℝ) ≤ 1/2))

theorem selfConsistentRefreshOrbit_uniform (n : ℕ) :
    (selfConsistentRefreshOrbit (uniformNoiseLaw (ι := G)) n).prob =
      (uniformNoiseLaw (ι := G)).prob := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (fun i => _ / 4 + 3/4 * _) = _
    simp only [FiniteProbabilityLaw.mix, relativeGroupNoise, Matrix.mulVec, dotProduct, ih]
    exact selfConsistentRefresh_uniform

/-- The fixed-point equation has exactly one probability solution. -/
theorem selfConsistentRefresh_fixed_iff (p : FiniteProbabilityLaw G) :
    (selfConsistentRefresh p).prob = p.prob ↔ p.prob = (uniformNoiseLaw (ι := G)).prob := by
  constructor
  · intro hp
    have h := selfConsistentRefresh_contraction p (uniformNoiseLaw (ι := G))
    unfold refreshDistance at h
    rw [hp, selfConsistentRefresh_uniform] at h
    have hnonneg : 0 ≤ ∑ i, |p.prob i-(uniformNoiseLaw (ι := G)).prob i| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    have hz : (∑ i, |p.prob i-(uniformNoiseLaw (ι := G)).prob i|) = 0 := by linarith
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg
      (p.prob i-(uniformNoiseLaw (ι := G)).prob i))).mp hz
    funext i
    exact sub_eq_zero.mp (abs_eq_zero.mp (he i (Finset.mem_univ i)))
  · intro hp
    have h := selfConsistentRefresh_uniform (G := G)
    simpa [selfConsistentRefresh, FiniteProbabilityLaw.mix, relativeGroupNoise,
      Matrix.mulVec, dotProduct, hp] using h

/-- Self-convolution has a quadratic residual around the uniform density. -/
theorem relativeGroupNoise_self_quadratic (p : FiniteProbabilityLaw G) (i : G) :
    (p.mix (relativeGroupNoise p)).prob i - (uniformNoiseLaw (ι := G)).prob i =
      ∑ j, (p.prob (i*j⁻¹)-(uniformNoiseLaw (ι := G)).prob (i*j⁻¹)) *
        (p.prob j-(uniformNoiseLaw (ι := G)).prob j) := by
  have hrow : (∑ j, p.prob (i*j⁻¹)) = 1 :=
    sum_row_of_mem_doublyStochastic (relativeGroupNoise p).property i
  have hu : (∑ _j : G, (Fintype.card G : ℝ)⁻¹) = 1 := uniformNoiseLaw.sum_prob
  rw [relativeGroupNoise_prob]
  simp only [uniformNoiseLaw]
  have he (a b c : ℝ) : (a-c)*(b-c) = a*b-a*c-c*b+c*c := by ring
  simp_rw [he, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hrow, p.sum_prob, hu]
  ring

/-- The nonlinear error is bounded quadratically, stronger than uniform Lipschitz control. -/
theorem relativeGroupNoise_self_quadratic_distance (p : FiniteProbabilityLaw G) :
    refreshDistance (p.mix (relativeGroupNoise p)) (uniformNoiseLaw (ι := G)) ≤
      refreshDistance p (uniformNoiseLaw (ι := G)) ^ 2 := by
  unfold refreshDistance
  simp_rw [relativeGroupNoise_self_quadratic]
  calc
    _ ≤ ∑ i, ∑ j, |(p.prob (i*j⁻¹)-(uniformNoiseLaw (ι := G)).prob (i*j⁻¹)) *
        (p.prob j-(uniformNoiseLaw (ι := G)).prob j)| :=
      Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
    _ = (∑ i, |p.prob i-(uniformNoiseLaw (ι := G)).prob i|)^2 := by
      simp_rw [abs_mul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      have he (j : G) :
          (∑ i, |p.prob (i*j⁻¹)-(uniformNoiseLaw (ι := G)).prob (i*j⁻¹)|) =
            ∑ i, |p.prob i-(uniformNoiseLaw (ι := G)).prob i| :=
        Equiv.sum_comp (Equiv.mulRight j⁻¹)
          (fun i => |p.prob i-(uniformNoiseLaw (ι := G)).prob i|)
      simp_rw [he, ← Finset.mul_sum, pow_two]

/-- Uniform refresh retains the full quadratic convergence improvement. -/
theorem selfConsistentRefresh_quadratic (p : FiniteProbabilityLaw G) :
    refreshDistance (selfConsistentRefresh p) (uniformNoiseLaw (ι := G)) ≤
      (1/4 : ℝ) * refreshDistance p (uniformNoiseLaw (ι := G)) ^ 2 := by
  have h := selfConsistentRefresh_distance p (uniformNoiseLaw (ι := G))
  have hq := relativeGroupNoise_self_quadratic_distance p
  unfold refreshDistance at h hq ⊢
  rw [selfConsistentRefresh_uniform, relativeGroupNoise_uniform] at h
  linarith

/-- The actual orbit obeys a doubly exponential error bound around its explicit fixed law. -/
theorem selfConsistentRefreshOrbit_quadratic_bound (p : FiniteProbabilityLaw G) (n : ℕ) :
    refreshDistance (selfConsistentRefreshOrbit p n) (uniformNoiseLaw (ι := G)) ≤
      4 * (refreshDistance p (uniformNoiseLaw (ι := G)) / 4) ^ (2^n) := by
  have hd (q : FiniteProbabilityLaw G) : 0 ≤ refreshDistance q (uniformNoiseLaw (ι := G)) :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  induction n with
  | zero =>
    simp only [selfConsistentRefreshOrbit, pow_zero, pow_one]
    linarith
  | succ n ih =>
    have hs := selfConsistentRefresh_quadratic (selfConsistentRefreshOrbit p n)
    have hb : 0 ≤ 4 * (refreshDistance p (uniformNoiseLaw (ι := G)) / 4)^(2^n) := by
      exact mul_nonneg (by positivity) (pow_nonneg
        (div_nonneg (hd p) (by positivity)) _)
    have hsq := (sq_le_sq₀ (hd _) hb).mpr ih
    have he :
        (1/4 : ℝ) * (4 * (refreshDistance p (uniformNoiseLaw (ι := G))/4)^(2^n))^2 =
          4 * (refreshDistance p (uniformNoiseLaw (ι := G))/4)^(2^(n+1)) := by
      rw [show 2^(n+1) = 2^n*2 by rw [pow_succ], pow_mul]
      ring
    change refreshDistance (selfConsistentRefresh (selfConsistentRefreshOrbit p n)) _ ≤ _
    rw [← he]
    linarith

/-- Attraction to the explicit uniform density in the full L1 distance. -/
theorem selfConsistentRefreshOrbit_uniform_bound (p : FiniteProbabilityLaw G) (n : ℕ) :
    refreshDistance (selfConsistentRefreshOrbit p n) (uniformNoiseLaw (ι := G)) ≤
      (1/2 : ℝ)^n * refreshDistance p (uniformNoiseLaw (ι := G)) := by
  have h := selfConsistentRefreshOrbit_distance p (uniformNoiseLaw (ι := G)) n
  simpa only [refreshDistance, selfConsistentRefreshOrbit_uniform] using h

/-- The certified exponential estimate gives actual convergence, without compactness assumptions. -/
theorem selfConsistentRefreshOrbit_distance_tendsto (p : FiniteProbabilityLaw G) :
    Filter.Tendsto (fun n => refreshDistance (selfConsistentRefreshOrbit p n)
      (uniformNoiseLaw (ι := G))) Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun n : ℕ => (1/2 : ℝ)^n *
      refreshDistance p (uniformNoiseLaw (ι := G))) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by positivity : (0 : ℝ) ≤ 1/2) (by linarith : (1/2 : ℝ) < 1)).mul_const
        (refreshDistance p (uniformNoiseLaw (ι := G)))
  exact squeeze_zero (fun n => Finset.sum_nonneg fun i _ => abs_nonneg _)
    (selfConsistentRefreshOrbit_uniform_bound p) hpow

/-- Every individual group population converges to its uniform value. -/
theorem selfConsistentRefreshOrbit_coordinate_tendsto (p : FiniteProbabilityLaw G) (i : G) :
    Filter.Tendsto (fun n => (selfConsistentRefreshOrbit p n).prob i) Filter.atTop
      (nhds ((uniformNoiseLaw (ι := G)).prob i)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun n => abs_nonneg _)
    (fun n => Finset.single_le_sum (fun j _ => abs_nonneg
      ((selfConsistentRefreshOrbit p n).prob j-(uniformNoiseLaw (ι := G)).prob j))
      (Finset.mem_univ i)) (selfConsistentRefreshOrbit_distance_tendsto p)

/-- A refresh coupling strictly between zero and one for every real parameter. -/
def refreshRate (r : ℝ) : ℝ := 1/(1+Real.exp r)

theorem refreshRate_pos (r : ℝ) : 0 < refreshRate r := by
  unfold refreshRate
  positivity

theorem refreshRate_lt_one (r : ℝ) : refreshRate r < 1 := by
  unfold refreshRate
  apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 1+Real.exp r)).mpr
  linarith [Real.exp_pos r]

/-- Self-consistent convolution with every strictly positive uniform refresh strength. -/
def selfConsistentRefreshAt (r : ℝ) (p : FiniteProbabilityLaw G) : FiniteProbabilityLaw G where
  prob i := refreshRate r * (p.mix (relativeGroupNoise p)).prob i +
    (1-refreshRate r) * (uniformNoiseLaw (ι := G)).prob i
  nonneg i := add_nonneg
    (mul_nonneg (refreshRate_pos r).le ((p.mix (relativeGroupNoise p)).nonneg i))
    (mul_nonneg (sub_nonneg.mpr (refreshRate_lt_one r).le) (uniformNoiseLaw.nonneg i))
  sum_prob := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      (p.mix (relativeGroupNoise p)).sum_prob, uniformNoiseLaw.sum_prob]
    ring

/-- The uniform core is fixed at every admitted coupling. -/
theorem selfConsistentRefreshAt_uniform (r : ℝ) :
    (selfConsistentRefreshAt r (uniformNoiseLaw (ι := G))).prob =
      (uniformNoiseLaw (ι := G)).prob := by
  funext i
  change refreshRate r * ((uniformNoiseLaw (ι := G)).mix
    (relativeGroupNoise uniformNoiseLaw)).prob i + (1-refreshRate r)*_ = _
  rw [relativeGroupNoise_uniform]
  ring

/-- Arbitrary pairs obey the expected two-times-coupling estimate. -/
theorem selfConsistentRefreshAt_pair_bound (r : ℝ) (p q : FiniteProbabilityLaw G) :
    refreshDistance (selfConsistentRefreshAt r p) (selfConsistentRefreshAt r q) ≤
      (2*refreshRate r) * refreshDistance p q := by
  have he : refreshDistance (selfConsistentRefreshAt r p) (selfConsistentRefreshAt r q) =
      refreshRate r * refreshDistance (p.mix (relativeGroupNoise p)) (q.mix (relativeGroupNoise q)) := by
    unfold refreshDistance
    simp only [selfConsistentRefreshAt]
    have hid (a b c t : ℝ) : t*a+(1-t)*c-(t*b+(1-t)*c) = t*(a-b) := by ring
    simp_rw [hid, abs_mul, abs_of_nonneg (refreshRate_pos r).le, Finset.mul_sum]
  rw [he]
  have h := mul_le_mul_of_nonneg_left (relativeGroupNoise_self_distance p q) (refreshRate_pos r).le
  nlinarith

/-- Relative to the uniform core, the rate is the coupling itself, even above one half. -/
theorem selfConsistentRefreshAt_core_bound (r : ℝ) (p : FiniteProbabilityLaw G) :
    refreshDistance (selfConsistentRefreshAt r p) (uniformNoiseLaw (ι := G)) ≤
      refreshRate r * refreshDistance p (uniformNoiseLaw (ι := G)) := by
  have h := relativeGroupNoise_totalVariation_le p p (uniformNoiseLaw (ι := G))
  rw [relativeGroupNoise_uniform] at h
  have he : refreshDistance (selfConsistentRefreshAt r p) (uniformNoiseLaw (ι := G)) =
      refreshRate r * refreshDistance (p.mix (relativeGroupNoise p)) (uniformNoiseLaw (ι := G)) := by
    unfold refreshDistance
    simp only [selfConsistentRefreshAt]
    have hid (a b t : ℝ) : t*a+(1-t)*b-b = t*(a-b) := by ring
    simp_rw [hid, abs_mul, abs_of_nonneg (refreshRate_pos r).le, Finset.mul_sum]
  rw [he]
  exact mul_le_mul_of_nonneg_left h (refreshRate_pos r).le

def selfConsistentRefreshAtOrbit (r : ℝ) (p : FiniteProbabilityLaw G) : ℕ → FiniteProbabilityLaw G
  | 0 => p
  | n+1 => selfConsistentRefreshAt r (selfConsistentRefreshAtOrbit r p n)

/-- Every positive refresh strength gives global exponential attraction. -/
theorem selfConsistentRefreshAtOrbit_bound (r : ℝ) (p : FiniteProbabilityLaw G) (n : ℕ) :
    refreshDistance (selfConsistentRefreshAtOrbit r p n) (uniformNoiseLaw (ι := G)) ≤
      refreshRate r^n * refreshDistance p (uniformNoiseLaw (ι := G)) := by
  induction n with
  | zero => simp [selfConsistentRefreshAtOrbit]
  | succ n ih =>
    exact (selfConsistentRefreshAt_core_bound r _).trans
      (by simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left ih (refreshRate_pos r).le)

/-- Actual convergence follows for every real coupling parameter. -/
theorem selfConsistentRefreshAtOrbit_tendsto (r : ℝ) (p : FiniteProbabilityLaw G) :
    Filter.Tendsto (fun n => refreshDistance (selfConsistentRefreshAtOrbit r p n)
      (uniformNoiseLaw (ι := G))) Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun n : ℕ => refreshRate r^n *
      refreshDistance p (uniformNoiseLaw (ι := G))) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one
      (refreshRate_pos r).le (refreshRate_lt_one r)).mul_const
        (refreshDistance p (uniformNoiseLaw (ι := G)))
  exact squeeze_zero (fun n => Finset.sum_nonneg fun i _ => abs_nonneg _)
    (selfConsistentRefreshAtOrbit_bound r p) hpow

/-- Asymmetric contraction alone excludes every competing probability fixed point. -/
theorem selfConsistentRefreshAt_fixed_iff (r : ℝ) (p : FiniteProbabilityLaw G) :
    (selfConsistentRefreshAt r p).prob = p.prob ↔ p.prob = (uniformNoiseLaw (ι := G)).prob := by
  constructor
  · intro hp
    have h := selfConsistentRefreshAt_core_bound r p
    unfold refreshDistance at h
    rw [hp] at h
    have hnonneg : 0 ≤ ∑ i, |p.prob i-(uniformNoiseLaw (ι := G)).prob i| :=
      Finset.sum_nonneg fun i _ => abs_nonneg _
    have hz : (∑ i, |p.prob i-(uniformNoiseLaw (ι := G)).prob i|) = 0 := by
      nlinarith [refreshRate_lt_one r]
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg
      (p.prob i-(uniformNoiseLaw (ι := G)).prob i))).mp hz
    funext i
    exact sub_eq_zero.mp (abs_eq_zero.mp (he i (Finset.mem_univ i)))
  · intro hp
    have h := selfConsistentRefreshAt_uniform (G := G) r
    simpa [selfConsistentRefreshAt, FiniteProbabilityLaw.mix, relativeGroupNoise,
      Matrix.mulVec, dotProduct, hp] using h

/-- The explicit quarter-coupling model is a member of the full parameter family. -/
theorem selfConsistentRefreshAt_log_three (p : FiniteProbabilityLaw G) :
    (selfConsistentRefreshAt (Real.log 3) p).prob = (selfConsistentRefresh p).prob := by
  funext i
  simp only [selfConsistentRefreshAt, selfConsistentRefresh, refreshRate,
    Real.exp_log (by positivity : (0 : ℝ) < 3)]
  ring

omit [Group G] [DecidableEq G] in
/-- Two probability laws are at L1 distance at most two. -/
theorem refreshDistance_le_two (p q : FiniteProbabilityLaw G) : refreshDistance p q ≤ 2 := by
  unfold refreshDistance
  calc
    _ ≤ ∑ i, (p.prob i+q.prob i) := Finset.sum_le_sum fun i _ => by
      simpa only [abs_of_nonneg (p.nonneg i), abs_of_nonneg (q.nonneg i)] using
        abs_sub (p.prob i) (q.prob i)
    _ = 2 := by rw [Finset.sum_add_distrib, p.sum_prob, q.sum_prob]; ring

/-- The quadratic improvement is uniformly doubly exponential over all initial laws. -/
theorem selfConsistentRefreshOrbit_uniform_quadratic_bound (p : FiniteProbabilityLaw G) (n : ℕ) :
    refreshDistance (selfConsistentRefreshOrbit p n) (uniformNoiseLaw (ι := G)) ≤
      4 * (1/2 : ℝ)^(2^n) := by
  have hdist := refreshDistance_le_two p (uniformNoiseLaw (ι := G))
  have hnonneg : 0 ≤ refreshDistance p (uniformNoiseLaw (ι := G))/4 :=
    div_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _) (by positivity)
  exact (selfConsistentRefreshOrbit_quadratic_bound p n).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnonneg (by linarith) _) (by positivity))

end GaloisForLFunctions.HTGeometry
