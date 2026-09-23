import GaloisForLFunctions.RHTower.PrimeIsingTreeFixedModalClosureNoGo
import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance

/-!
# Arbitrary-graph GKS obstruction for prime-mass Lee--Yang approximants

A finite zero-field ferromagnetic Ising model on any graph satisfies the first Griffiths/GKS
pair-correlation inequality. This file isolates that literature theorem as a finite weight-table
interface and proves a topology-independent consequence for the completed Xi approximation route.

The normalized characteristic partition has central curvature equal to the magnetization variance.
GKS makes every off-diagonal covariance nonnegative, while each diagonal spin square is one.
Therefore curvature is at least one quarter of the sum of squared site masses. Prime-log masses give
one fixed positive unit per vertex.

Two consequences are closed in Lean:

* no unscaled sequence of GKS-certified finite prime-mass spin systems, with arbitrary changing
  graph topology, interactions, and size, converges locally uniformly to pointed completed Xi;
* if a growing sequence converges after common site-mass scaling `aₙ`, then necessarily `aₙ → 0`;
* a fixed quartic Landau/Curie--Weiss critical universality class cannot supply the limit, because
  its third-order ODE is closed under local-uniform convergence and contradicts Xi
  hypertranscendence.

Thus adding graph cycles cannot repair the finite-tree route. The sole surviving Lee--Yang regime is
a genuinely critical dense limit in which individual site masses collapse while collective
correlations retain non-Gaussian higher cumulants and escape every fixed finite Landau ODE.
-/

open Complex Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Boolean spin encoded as `+1` or `-1`. -/
def boolSpin (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem boolSpin_sq (b : Bool) : boolSpin b ^ (2 : ℕ) = 1 := by
  cases b <;> simp [boolSpin]

/-- Finite prime-mass spin weight table carrying the first Griffiths/GKS inequality. Ordinary
zero-field ferromagnetic Ising models on arbitrary finite graphs supply this certificate. -/
structure FiniteGKSPrimeSpinModel (n : ℕ) where
  mass : Fin n → ℝ
  weight : (Fin n → Bool) → ℝ
  mass_floor : ∀ i, Real.log 2 ≤ mass i
  weight_nonneg : ∀ σ, 0 ≤ weight σ
  totalWeight_pos : 0 < ∑ σ, weight σ
  pairNumerator_nonneg : ∀ i j,
    0 ≤ ∑ σ, weight σ * boolSpin (σ i) * boolSpin (σ j)

/-- Zero-field partition weight. -/
def FiniteGKSPrimeSpinModel.totalWeight {n : ℕ}
    (M : FiniteGKSPrimeSpinModel n) : ℝ :=
  ∑ σ, M.weight σ

/-- Half-scaled prime-log magnetization. -/
def FiniteGKSPrimeSpinModel.magnetization {n : ℕ}
    (M : FiniteGKSPrimeSpinModel n) (σ : Fin n → Bool) : ℝ :=
  (∑ i, M.mass i * boolSpin (σ i)) / 2

/-- Normalized characteristic partition in the centered Xi coordinate. -/
def FiniteGKSPrimeSpinModel.partition {n : ℕ}
    (M : FiniteGKSPrimeSpinModel n) (z : ℂ) : ℂ :=
  ∑ σ, ((M.weight σ / M.totalWeight : ℝ) : ℂ) *
    Complex.exp (((Complex.I * M.magnetization σ : ℂ)) * z)

/-- Unnormalized two-site spin correlation. -/
def FiniteGKSPrimeSpinModel.pairNumerator {n : ℕ}
    (M : FiniteGKSPrimeSpinModel n) (i j : Fin n) : ℝ :=
  ∑ σ, M.weight σ * boolSpin (σ i) * boolSpin (σ j)

theorem FiniteGKSPrimeSpinModel.magnetization_sq {n : ℕ}
    (M : FiniteGKSPrimeSpinModel n) (σ : Fin n → Bool) :
    M.magnetization σ ^ (2 : ℕ) =
      ∑ i, ∑ j,
        (M.mass i * M.mass j / 4) *
          (boolSpin (σ i) * boolSpin (σ j)) := by
  unfold FiniteGKSPrimeSpinModel.magnetization
  rw [div_pow]
  norm_num
  rw [sq, Finset.sum_mul]
  rw [div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem FiniteGKSPrimeSpinModel.pairNumerator_diag {n : ℕ}
    (M : FiniteGKSPrimeSpinModel n) (i : Fin n) :
    M.pairNumerator i i = M.totalWeight := by
  unfold FiniteGKSPrimeSpinModel.pairNumerator
    FiniteGKSPrimeSpinModel.totalWeight
  apply Finset.sum_congr rfl
  intro σ hσ
  calc
    M.weight σ * boolSpin (σ i) * boolSpin (σ i) =
        M.weight σ * boolSpin (σ i) ^ (2 : ℕ) := by ring
    _ = M.weight σ := by rw [boolSpin_sq]; ring

theorem FiniteGKSPrimeSpinModel.weighted_magnetization_sq_eq_pair_sum {n : ℕ}
    (M : FiniteGKSPrimeSpinModel n) :
    ∑ σ, M.weight σ * M.magnetization σ ^ (2 : ℕ) =
      ∑ i, ∑ j, (M.mass i * M.mass j / 4) * M.pairNumerator i j := by
  simp_rw [M.magnetization_sq]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  unfold FiniteGKSPrimeSpinModel.pairNumerator
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  ring

theorem FiniteGKSPrimeSpinModel.sum_mass_sq_div_four_mul_totalWeight_le_weighted_magnetization_sq
    {n : ℕ} (M : FiniteGKSPrimeSpinModel n) :
    ((∑ i, M.mass i ^ (2 : ℕ)) / 4) * M.totalWeight ≤
      ∑ σ, M.weight σ * M.magnetization σ ^ (2 : ℕ) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hmass : ∀ i, 0 ≤ M.mass i := fun i =>
    le_trans hlog.le (M.mass_floor i)
  have hpair : ∀ i j, 0 ≤ M.pairNumerator i j := by
    intro i j
    exact M.pairNumerator_nonneg i j
  have hterm : ∀ i j,
      0 ≤ (M.mass i * M.mass j / 4) * M.pairNumerator i j := by
    intro i j
    exact mul_nonneg (div_nonneg (mul_nonneg (hmass i) (hmass j)) (by norm_num))
      (hpair i j)
  rw [M.weighted_magnetization_sq_eq_pair_sum]
  calc
    ((∑ i, M.mass i ^ (2 : ℕ)) / 4) * M.totalWeight =
        ∑ i, (M.mass i * M.mass i / 4) * M.totalWeight := by
      rw [div_eq_mul_inv, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i, (M.mass i * M.mass i / 4) * M.pairNumerator i i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [M.pairNumerator_diag]
    _ ≤ ∑ i, ∑ j, (M.mass i * M.mass j / 4) * M.pairNumerator i j := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.single_le_sum (fun j _ => hterm i j) (Finset.mem_univ i)

theorem FiniteGKSPrimeSpinModel.vertex_floor_le_normalized_second_moment
    {n : ℕ} (M : FiniteGKSPrimeSpinModel n) :
    (n : ℝ) * Real.log 2 ^ (2 : ℕ) / 4 ≤
      (∑ σ, M.weight σ * M.magnetization σ ^ (2 : ℕ)) / M.totalWeight := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsquare : ∀ i, Real.log 2 ^ (2 : ℕ) ≤ M.mass i ^ (2 : ℕ) := by
    intro i
    nlinarith [M.mass_floor i]
  have hsum : (n : ℝ) * Real.log 2 ^ (2 : ℕ) ≤ ∑ i, M.mass i ^ (2 : ℕ) := by
    calc
      (n : ℝ) * Real.log 2 ^ (2 : ℕ) = ∑ _i : Fin n, Real.log 2 ^ (2 : ℕ) := by simp
      _ ≤ ∑ i, M.mass i ^ (2 : ℕ) := Finset.sum_le_sum fun i _ => hsquare i
  have hweighted :=
    M.sum_mass_sq_div_four_mul_totalWeight_le_weighted_magnetization_sq
  apply (le_div_iff₀ M.totalWeight_pos).2
  have htotal : 0 ≤ M.totalWeight := M.totalWeight_pos.le
  have hscaled := mul_le_mul_of_nonneg_right hsum
    (div_nonneg htotal (by norm_num : (0 : ℝ) ≤ 4))
  calc
    (n : ℝ) * Real.log 2 ^ (2 : ℕ) / 4 * M.totalWeight =
        ((n : ℝ) * Real.log 2 ^ (2 : ℕ)) * (M.totalWeight / 4) := by ring
    _ ≤ (∑ i, M.mass i ^ (2 : ℕ)) * (M.totalWeight / 4) := hscaled
    _ = ((∑ i, M.mass i ^ (2 : ℕ)) / 4) * M.totalWeight := by ring
    _ ≤ ∑ σ, M.weight σ * M.magnetization σ ^ (2 : ℕ) := hweighted

theorem FiniteGKSPrimeSpinModel.iteratedDeriv_partition {n : ℕ}
    (M : FiniteGKSPrimeSpinModel n) (k : ℕ) (z : ℂ) :
    iteratedDeriv k M.partition z =
      ∑ σ, ((M.weight σ / M.totalWeight : ℝ) : ℂ) *
        (Complex.I * M.magnetization σ) ^ k *
        Complex.exp ((Complex.I * M.magnetization σ) * z) := by
  exact GaloisForLFunctions.iteratedDeriv_finset_expSum Finset.univ
    (fun σ => ((M.weight σ / M.totalWeight : ℝ) : ℂ))
    (fun σ => Complex.I * M.magnetization σ) k z

theorem FiniteGKSPrimeSpinModel.neg_re_iteratedDeriv_two_partition_zero {n : ℕ}
    (M : FiniteGKSPrimeSpinModel n) :
    -(iteratedDeriv 2 M.partition 0).re =
      (∑ σ, M.weight σ * (M.magnetization σ) ^ (2 : ℕ)) / M.totalWeight := by
  rw [M.iteratedDeriv_partition]
  simp only [mul_zero, Complex.exp_zero, mul_one]
  change -Complex.reCLM (∑ σ, ((M.weight σ / M.totalWeight : ℝ) : ℂ) *
    (Complex.I * M.magnetization σ) ^ (2 : ℕ)) = _
  rw [map_sum Complex.reCLM]
  simp only [Complex.ofReal_div, Complex.reCLM_apply,
    Complex.mul_re, Complex.div_ofReal_re, Complex.ofReal_re,
    Complex.div_ofReal_im, Complex.ofReal_im, zero_div, zero_mul, sub_zero]
  have hterm (x : Fin n → Bool) :
      ((Complex.I * (M.magnetization x : ℂ)) ^ (2 : ℕ)).re =
        -(M.magnetization x) ^ (2 : ℕ) := by
    rw [mul_pow]
    have hI : (Complex.I : ℂ) ^ (2 : ℕ) = -1 := by norm_num
    rw [hI]
    norm_cast
    norm_num
  simp_rw [hterm]
  simp [FiniteGKSPrimeSpinModel.totalWeight]
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun x _ => by ring)

theorem FiniteGKSPrimeSpinModel.vertex_curvature_floor {n : ℕ}
    (M : FiniteGKSPrimeSpinModel n) :
    (n : ℝ) * Real.log 2 ^ (2 : ℕ) / 4 ≤
      -(iteratedDeriv 2 M.partition 0).re := by
  rw [M.neg_re_iteratedDeriv_two_partition_zero]
  exact M.vertex_floor_le_normalized_second_moment

theorem FiniteGKSPrimeSpinModel.differentiable_partition {n : ℕ}
    (M : FiniteGKSPrimeSpinModel n) : Differentiable ℂ M.partition := by
  unfold FiniteGKSPrimeSpinModel.partition
  fun_prop

theorem card_primeSpinConfigurations (n : ℕ) :
    Fintype.card (Fin n → Bool) = 2 ^ n := by
  rw [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

theorem FiniteGKSPrimeSpinModel.finiteModalWidthAtMost_iteratedDeriv_partition
    {n : ℕ} (M : FiniteGKSPrimeSpinModel n) (z : ℂ) :
    HTGeometry.FiniteModalWidthAtMost (2 ^ n)
      (fun k => iteratedDeriv k M.partition z) := by
  let e : (Fin n → Bool) ≃ Fin (Fintype.card (Fin n → Bool)) :=
    Fintype.equivFin (Fin n → Bool)
  have hcard : Fintype.card (Fin n → Bool) = 2 ^ n := card_primeSpinConfigurations n
  rw [← hcard]
  refine ⟨fun i =>
      (((M.weight (e.symm i) / M.totalWeight : ℝ) : ℂ) *
        Complex.exp ((Complex.I * M.magnetization (e.symm i)) * z)),
    fun i => Complex.I * M.magnetization (e.symm i), ?_⟩
  funext k
  rw [M.iteratedDeriv_partition]
  unfold HTGeometry.finiteModalSequence
  have hreindex := Equiv.sum_comp e (fun i =>
    (((M.weight (e.symm i) / M.totalWeight : ℝ) : ℂ) *
      Complex.exp ((Complex.I * M.magnetization (e.symm i)) * z)) *
      (Complex.I * M.magnetization (e.symm i)) ^ k)
  simp only [Equiv.symm_apply_apply] at hreindex
  calc
    (∑ σ, ((M.weight σ / M.totalWeight : ℝ) : ℂ) *
        (Complex.I * M.magnetization σ) ^ k *
        Complex.exp ((Complex.I * M.magnetization σ) * z)) =
        ∑ σ, ((M.weight σ / M.totalWeight : ℝ) : ℂ) *
          Complex.exp ((Complex.I * M.magnetization σ) * z) *
          (Complex.I * M.magnetization σ) ^ k := by
      apply Finset.sum_congr rfl
      intro σ hσ
      ring
    _ = _ := hreindex

theorem eventually_vertexCount_real_bounded_of_gksPrimeSpin_tendstoLocallyUniformly
    (vertexCount : ℕ → ℕ)
    (M : ∀ k, FiniteGKSPrimeSpinModel (vertexCount k))
    (hconv : TendstoLocallyUniformly
      (fun k => (M k).partition) unitCentralXiC atTop) :
    ∃ C : ℝ, ∀ᶠ k in atTop, (vertexCount k : ℝ) ≤ C := by
  have hjet := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform
    isOpen_univ (tendstoLocallyUniformlyOn_univ.mpr hconv)
    (Filter.Eventually.of_forall fun k =>
      (M k).differentiable_partition.differentiableOn)
    2 (Set.mem_univ 0)
  have hcurv : Tendsto
      (fun k => -(iteratedDeriv 2 (M k).partition 0).re) atTop
      (nhds (-(iteratedDeriv 2 unitCentralXiC 0).re)) := by
    simpa only [Function.comp_apply] using!
      ((continuous_neg.comp Complex.continuous_re).continuousAt.tendsto.comp hjet)
  let K : ℝ := -(iteratedDeriv 2 unitCentralXiC 0).re + 1
  have hevent : ∀ᶠ k in atTop,
      -(iteratedDeriv 2 (M k).partition 0).re < K :=
    hcurv.eventually (Iio_mem_nhds (by dsimp [K]; linarith))
  have hlogSq : 0 < Real.log 2 ^ (2 : ℕ) :=
    sq_pos_of_pos (Real.log_pos (by norm_num))
  refine ⟨4 * K / Real.log 2 ^ (2 : ℕ), ?_⟩
  filter_upwards [hevent] with k hk
  apply (le_div_iff₀ hlogSq).2
  have hfloor := (M k).vertex_curvature_floor
  nlinarith

theorem eventually_vertexCount_nat_bounded_of_gksPrimeSpin_tendstoLocallyUniformly
    (vertexCount : ℕ → ℕ)
    (M : ∀ k, FiniteGKSPrimeSpinModel (vertexCount k))
    (hconv : TendstoLocallyUniformly
      (fun k => (M k).partition) unitCentralXiC atTop) :
    ∃ V : ℕ, ∀ᶠ k in atTop, vertexCount k ≤ V := by
  obtain ⟨C, hC⟩ :=
    eventually_vertexCount_real_bounded_of_gksPrimeSpin_tendstoLocallyUniformly
      vertexCount M hconv
  obtain ⟨V, hV⟩ := exists_nat_gt C
  refine ⟨V, ?_⟩
  filter_upwards [hC] with k hk
  have hlt : (vertexCount k : ℝ) < (V : ℝ) := hk.trans_lt hV
  exact_mod_cast (show vertexCount k < V by exact_mod_cast hlt).le

/-- No unscaled sequence of finite prime-mass spin systems satisfying the GKS pair-correlation
inequalities can converge locally uniformly to completed Xi. Graph topology and couplings may vary
arbitrarily. -/
theorem not_tendstoLocallyUniformly_finiteGKSPrimeSpinPartition_unitCentralXiC
    (vertexCount : ℕ → ℕ)
    (M : ∀ k, FiniteGKSPrimeSpinModel (vertexCount k)) :
    ¬ TendstoLocallyUniformly
      (fun k => (M k).partition) unitCentralXiC atTop := by
  intro hconv
  obtain ⟨V, hV⟩ :=
    eventually_vertexCount_nat_bounded_of_gksPrimeSpin_tendstoLocallyUniformly
      vertexCount M hconv
  have hwidth : ∀ᶠ k in atTop, ∀ z,
      HTGeometry.FiniteModalWidthAtMost (2 ^ V)
        (fun j => iteratedDeriv j (M k).partition z) := by
    filter_upwards [hV] with k hk
    intro z
    exact ((M k).finiteModalWidthAtMost_iteratedDeriv_partition z).mono
      (Nat.pow_le_pow_right (by omega) hk)
  exact (HTGeometry.not_tendstoLocallyUniformly_of_hypertranscendental_of_fixedModalJetWidth
    (fun k => (M k).differentiable_partition)
    unitCentralXiC_hypertranscendental hwidth) hconv

/-- Critical argument scaling of a finite GKS spin partition. -/
def FiniteGKSPrimeSpinModel.rescaledPartition {n : ℕ}
    (M : FiniteGKSPrimeSpinModel n) (a : ℝ) (z : ℂ) : ℂ :=
  M.partition ((a : ℂ) * z)

theorem FiniteGKSPrimeSpinModel.iteratedDeriv_rescaledPartition {n : ℕ}
    (M : FiniteGKSPrimeSpinModel n) (a : ℝ) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (M.rescaledPartition a) z =
      (a : ℂ) ^ k * iteratedDeriv k M.partition ((a : ℂ) * z) := by
  exact GaloisForLFunctions.iteratedDeriv_comp_mul_left_uncond
    M.partition (a : ℂ) k z

theorem FiniteGKSPrimeSpinModel.rescaled_vertex_curvature_floor {n : ℕ}
    (M : FiniteGKSPrimeSpinModel n) (a : ℝ) :
    a ^ (2 : ℕ) * ((n : ℝ) * Real.log 2 ^ (2 : ℕ) / 4) ≤
      -(iteratedDeriv 2 (M.rescaledPartition a) 0).re := by
  rw [M.iteratedDeriv_rescaledPartition, mul_zero]
  have hbase := M.vertex_curvature_floor
  have hscaled := mul_le_mul_of_nonneg_left hbase (sq_nonneg a)
  have hreal (D : ℂ) : -(((a : ℂ) ^ (2 : ℕ) * D).re) = a ^ (2 : ℕ) * (-D.re) := by
    have ha2 : (a : ℂ) ^ (2 : ℕ) = ((a ^ (2 : ℕ) : ℝ) : ℂ) := by norm_num
    have hmul : (a : ℂ) ^ (2 : ℕ) * D = ((a ^ (2 : ℕ) : ℝ) : ℂ) * D :=
      congrArg (fun z : ℂ => z * D) ha2
    calc
      -(((a : ℂ) ^ (2 : ℕ) * D).re) = -(((((a ^ (2 : ℕ) : ℝ) : ℂ) * D)).re) :=
        congrArg (fun z : ℂ => -z.re) hmul
      _ = a ^ (2 : ℕ) * (-D.re) := by
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
        ring
  rw [hreal]
  exact hscaled

/-- Any Xi-convergent critically rescaled GKS sequence has bounded variance scale
`a_k^(2 : ℕ) * vertexCount_k`. -/
theorem eventually_scale_sq_mul_vertexCount_bounded_of_rescaled_gksPrimeSpin_tendstoLocallyUniformly
    (vertexCount : ℕ → ℕ)
    (M : ∀ k, FiniteGKSPrimeSpinModel (vertexCount k))
    (a : ℕ → ℝ)
    (hconv : TendstoLocallyUniformly
      (fun k => (M k).rescaledPartition (a k)) unitCentralXiC atTop) :
    ∃ C : ℝ, ∀ᶠ k in atTop, a k ^ (2 : ℕ) * (vertexCount k : ℝ) ≤ C := by
  have hdiff : ∀ k, Differentiable ℂ ((M k).rescaledPartition (a k)) := by
    intro k
    unfold FiniteGKSPrimeSpinModel.rescaledPartition
    exact (M k).differentiable_partition.comp
      ((differentiable_const (a k : ℂ)).mul differentiable_id)
  have hjet := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform
    isOpen_univ (tendstoLocallyUniformlyOn_univ.mpr hconv)
    (Filter.Eventually.of_forall fun k => (hdiff k).differentiableOn)
    2 (Set.mem_univ 0)
  have hcurv : Tendsto
      (fun k => -(iteratedDeriv 2 ((M k).rescaledPartition (a k)) 0).re) atTop
      (nhds (-(iteratedDeriv 2 unitCentralXiC 0).re)) := by
    simpa only [Function.comp_apply] using!
      ((continuous_neg.comp Complex.continuous_re).continuousAt.tendsto.comp hjet)
  let K : ℝ := -(iteratedDeriv 2 unitCentralXiC 0).re + 1
  have hevent : ∀ᶠ k in atTop,
      -(iteratedDeriv 2 ((M k).rescaledPartition (a k)) 0).re < K :=
    hcurv.eventually (Iio_mem_nhds (by dsimp [K]; linarith))
  have hlogSq : 0 < Real.log 2 ^ (2 : ℕ) :=
    sq_pos_of_pos (Real.log_pos (by norm_num))
  refine ⟨4 * K / Real.log 2 ^ (2 : ℕ), ?_⟩
  filter_upwards [hevent] with k hk
  apply (le_div_iff₀ hlogSq).2
  have hfloor := (M k).rescaled_vertex_curvature_floor (a k)
  nlinarith

/-- If graph size diverges along an Xi-convergent rescaled GKS sequence, its only possible escape
is critical collapse of the site-mass scale. -/
theorem tendsto_scale_zero_of_vertexCount_tendsto_atTop_of_rescaled_gksPrimeSpin_tendstoLocallyUniformly
    (vertexCount : ℕ → ℕ)
    (M : ∀ k, FiniteGKSPrimeSpinModel (vertexCount k))
    (a : ℕ → ℝ)
    (hvertices : Tendsto (fun k => (vertexCount k : ℝ)) atTop atTop)
    (hconv : TendstoLocallyUniformly
      (fun k => (M k).rescaledPartition (a k)) unitCentralXiC atTop) :
    Tendsto a atTop (nhds 0) := by
  obtain ⟨C, hC⟩ :=
    eventually_scale_sq_mul_vertexCount_bounded_of_rescaled_gksPrimeSpin_tendstoLocallyUniformly
      vertexCount M a hconv
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hεsq : 0 < ε ^ (2 : ℕ) := sq_pos_of_pos hε
  let B : ℝ := max C 0 + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith [le_max_right C 0]
  have hlarge : ∀ᶠ k in atTop,
      B / ε ^ (2 : ℕ) < (vertexCount k : ℝ) :=
    hvertices (Filter.eventually_gt_atTop (B / ε ^ (2 : ℕ)))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hC.and hlarge)
  refine ⟨N, fun k hk => ?_⟩
  obtain ⟨hbound, hklarge⟩ := hN k hk
  rw [Real.dist_eq, sub_zero]
  by_contra hnot
  have habs : ε ≤ |a k| := le_of_not_gt hnot
  have hsquare : ε ^ (2 : ℕ) ≤ a k ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (|a k| - ε), sq_abs (a k)]
  have hvertexPos : 0 < (vertexCount k : ℝ) :=
    lt_trans (div_pos hB hεsq) hklarge
  have hmul : B < ε ^ (2 : ℕ) * (vertexCount k : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hεsq).mp hklarge
  have hprod : ε ^ (2 : ℕ) * (vertexCount k : ℝ) ≤
      a k ^ (2 : ℕ) * (vertexCount k : ℝ) :=
    mul_le_mul_of_nonneg_right hsquare hvertexPos.le
  have hCle : C ≤ max C 0 := le_max_left C 0
  dsimp [B] at hmul
  linarith

/-- A function satisfying the quartic Landau fixed-point equation `F''' = c z F` is
differentially algebraic. The equation is the integration-by-parts ODE for the Fourier transform
of a density proportional to `exp (-a x^(4 : ℕ))`. -/
theorem differentiallyAlgebraic_of_iteratedDeriv_three_eq_landau
    {f : ℂ → ℂ} {c : ℂ}
    (hode : ∀ z, iteratedDeriv 3 f z = c * z * f z) :
    GaloisForLFunctions.DifferentiallyAlgebraic f := by
  refine ⟨3, MvPolynomial.X 4 -
    MvPolynomial.C c * MvPolynomial.X 0 * MvPolynomial.X 1, ?_, ?_⟩
  · intro hzero
    have heval := congrArg
      (MvPolynomial.eval (fun i : Fin 5 => if i = 4 then 1 else 0)) hzero
    have h14 : (1 : Fin 5) ≠ 4 := by decide
    simp [h14] at heval
  · intro z
    simp only [map_sub, MvPolynomial.eval_X, map_mul, MvPolynomial.eval_C,
      Fin.cons_zero]
    have hvalue :
        (Fin.cons z (fun j : Fin 4 => iteratedDeriv (j : ℕ) f z) : Fin 5 → ℂ) 1 = f z := by
      rw [show (1 : Fin 5) = Fin.succ 0 from rfl, Fin.cons_succ]
      simp
    have hthree :
        (Fin.cons z (fun j : Fin 4 => iteratedDeriv (j : ℕ) f z) : Fin 5 → ℂ) 4 =
          iteratedDeriv 3 f z := by
      rw [show (4 : Fin 5) = Fin.succ (3 : Fin 4) from rfl, Fin.cons_succ]
      norm_num
    rw [hvalue, hthree, hode]
    ring

/-- **Quartic critical-universality no-go.** A locally-uniform limit of entire functions in one
fixed quartic Landau universality class still satisfies its third-order ODE, hence cannot be the
hypertranscendental completed Xi function. -/
theorem not_tendstoLocallyUniformly_unitCentralXiC_of_fixed_quarticLandauODE
    (F : ℕ → ℂ → ℂ) (c : ℂ)
    (hF : ∀ k, Differentiable ℂ (F k))
    (hode : ∀ k z, iteratedDeriv 3 (F k) z = c * z * F k z) :
    ¬ TendstoLocallyUniformly F unitCentralXiC atTop := by
  intro hconv
  have hUniv := tendstoLocallyUniformlyOn_univ.mpr hconv
  have hdiff : ∀ᶠ k in atTop, DifferentiableOn ℂ (F k) Set.univ :=
    Filter.Eventually.of_forall fun k => (hF k).differentiableOn
  have hlimitOde : ∀ z,
      iteratedDeriv 3 unitCentralXiC z = c * z * unitCentralXiC z := by
    intro z
    have hthree := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform
      isOpen_univ hUniv hdiff 3 (Set.mem_univ z)
    have hzero := GaloisForLFunctions.iteratedDeriv_tendsto_of_locallyUniform
      isOpen_univ hUniv hdiff 0 (Set.mem_univ z)
    have hvalue : Tendsto (fun k => F k z) atTop (nhds (unitCentralXiC z)) := by
      simpa only [iteratedDeriv_zero] using hzero
    have hrhs : Tendsto (fun k => c * z * F k z) atTop
        (nhds (c * z * unitCentralXiC z)) :=
      tendsto_const_nhds.mul hvalue
    have hthree' : Tendsto (fun k => iteratedDeriv 3 (F k) z) atTop
        (nhds (c * z * unitCentralXiC z)) :=
      hrhs.congr' (Filter.Eventually.of_forall fun k => (hode k z).symm)
    exact tendsto_nhds_unique hthree hthree'
  exact unitCentralXiC_hypertranscendental
    (differentiallyAlgebraic_of_iteratedDeriv_three_eq_landau hlimitOde)

end

end GaloisForLFunctions.RHTower
