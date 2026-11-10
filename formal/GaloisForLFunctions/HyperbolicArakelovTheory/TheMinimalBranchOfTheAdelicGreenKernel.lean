import GaloisForLFunctions.HyperbolicArakelovTheory.ThePrimeWalkSelectsTheGreenKernel
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The minimal branch of the adelic Green kernel

Weighted occupation sums select the upper spectral branch, including its
tempered endpoint. The reflected lower branch solves the same point-source
equation but is not minimal among nonnegative supersolutions.
-/

set_option autoImplicit false
noncomputable section
open Filter
open scoped Classical BigOperators Topology

namespace GaloisForLFunctions.HyperbolicArakelovTheory.MinimalGreen
open FullAdelic AdelicAdjacency AdelicRadial AdelicGreen PrimeWalk

variable (p : {p : ℕ // p.Prime})

private theorem prime_pos : (0 : ℝ) < p.1 := by exact_mod_cast p.2.pos
private theorem prime_one_lt : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt
private theorem degree_pos : 0 < (p.1 : ℝ) + 1 := by positivity
private theorem eigen_pos (s : ℝ) : 0 < treeEigen p.1 s :=
  add_pos (Real.rpow_pos_of_pos (prime_pos p) s)
    (Real.rpow_pos_of_pos (prime_pos p) (1 - s))

private theorem eigen_reflection (s : ℝ) : treeEigen p.1 (1 - s) = treeEigen p.1 s := by
  unfold treeEigen
  rw [sub_sub_cancel]
  exact add_comm _ _

private theorem edge_eq : treeEigen p.1 (1 / 2) = 2 * Real.sqrt p.1 :=
  (treeEigen_eq_iff (prime_one_lt p) (1 / 2)).mpr rfl

private theorem edge_le (s : ℝ) : treeEigen p.1 (1 / 2) ≤ treeEigen p.1 s := by
  rw [edge_eq]
  exact two_sqrt_le_treeEigen (prime_pos p) s

private theorem edge_lt {s : ℝ} (hs : 1 / 2 < s) :
    treeEigen p.1 (1 / 2) < treeEigen p.1 s := by
  rcases lt_or_eq_of_le (edge_le p s) with h | h
  · exact h
  · have he : treeEigen p.1 s = 2 * Real.sqrt p.1 := h.symm.trans (edge_eq p)
    have hse := (treeEigen_eq_iff (prime_one_lt p) s).mp he
    exact (hs.ne' hse).elim

/-- The scalar converting the uniform walk to spectral parameter `ell`. -/
def walkWeight (ell : ℝ) : ℝ := ((p.1 : ℝ) + 1) / ell

/-- One weighted occupation term, constructed from actual finite walk probabilities. -/
def weightedTerm (ell : ℝ) (N : ℕ) (x y : LocalVertex p) : ℝ :=
  walkWeight p ell ^ N * walkMass p N x y / ell

def weightedPartial (ell : ℝ) (x : LocalVertex p) (N : ℕ) (y : LocalVertex p) : ℝ :=
  ∑ k ∈ Finset.range N, weightedTerm p ell k x y

/-- Nonnegative supersolutions for a fixed point source and spectral parameter. -/
def supersolutions (ell : ℝ) (x : LocalVertex p) : Set (LocalVertex p → ℝ) :=
  {u | (∀ y, 0 ≤ u y) ∧ ∀ y, pointMass p x y ≤ ell * u y - ∑ w ∈ neighbors p y, u w}

private theorem weight_nonneg {ell : ℝ} (hell : 0 < ell) : 0 ≤ walkWeight p ell :=
  (div_pos (degree_pos p) hell).le

theorem weightedTerm_nonneg {ell : ℝ} (hell : 0 < ell) (N : ℕ) (x y : LocalVertex p) :
    0 ≤ weightedTerm p ell N x y :=
  div_nonneg (mul_nonneg (pow_nonneg (weight_nonneg p hell) N)
    (walkMass_nonneg p N x y)) hell.le

private theorem weight_step {ell : ℝ} (hell : 0 < ell) (f : LocalVertex p → ℝ)
    (y : LocalVertex p) :
    walkWeight p ell * walkStep p f y = (∑ w ∈ neighbors p y, f w) / ell := by
  change (((p.1 : ℝ) + 1) / ell) * ((∑ w ∈ neighbors p y, f w) /
    ((p.1 : ℝ) + 1)) = _
  field_simp [(degree_pos p).ne', hell.ne']

private def weightedSource (ell : ℝ) (x : LocalVertex p) : LocalVertex p → ℝ :=
  ell⁻¹ • pointMass p x

private theorem iter_source (ell : ℝ) (x y : LocalVertex p) (N : ℕ) :
    ((walkStep p) ^ N) (weightedSource p ell x) y = walkMass p N x y / ell := by
  rw [weightedSource, map_smul, Pi.smul_apply, smul_eq_mul]
  unfold walkMass
  ring

private theorem weighted_telescope (ell : ℝ) (f : LocalVertex p → ℝ)
    (N : ℕ) (y : LocalVertex p) :
    (∑ k ∈ Finset.range N, walkWeight p ell ^ k *
      ((walkStep p) ^ k) (f - walkWeight p ell • walkStep p f) y) =
      f y - walkWeight p ell ^ N * ((walkStep p) ^ N) f y := by
  have hterm (k : ℕ) : walkWeight p ell ^ k *
      ((walkStep p) ^ k) (f - walkWeight p ell • walkStep p f) y =
      walkWeight p ell ^ k * ((walkStep p) ^ k) f y -
        walkWeight p ell ^ (k + 1) * ((walkStep p) ^ (k + 1)) f y := by
    rw [map_sub, Pi.sub_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    simp only [pow_succ, Module.End.mul_apply]
    ring
  simp_rw [hterm]
  rw [Finset.sum_range_sub']
  simp only [pow_zero, Module.End.one_apply, one_mul]

private theorem kernel_source {s : ℝ} (hs : 0 < s) (x : LocalVertex p) :
    localGreen p s x - walkWeight p (treeEigen p.1 s) • walkStep p (localGreen p s x) =
      weightedSource p (treeEigen p.1 s) x := by
  funext y
  change localGreen p s x y - walkWeight p (treeEigen p.1 s) *
    walkStep p (localGreen p s x) y = (treeEigen p.1 s)⁻¹ * pointMass p x y
  rw [weight_step p (eigen_pos p s)]
  have h := congrArg (fun t : ℝ => t / treeEigen p.1 s) (localGreen_resolvent p hs x y)
  rw [sub_div, mul_div_cancel_left₀ _ (eigen_pos p s).ne'] at h
  rw [h]
  unfold pointMass
  ring

theorem weightedPartial_eq {s : ℝ} (hs : 0 < s) (x y : LocalVertex p) (N : ℕ) :
    weightedPartial p (treeEigen p.1 s) x N y = localGreen p s x y -
      walkWeight p (treeEigen p.1 s) ^ N * ((walkStep p) ^ N) (localGreen p s x) y := by
  have h := weighted_telescope p (treeEigen p.1 s) (localGreen p s x) N y
  rw [kernel_source p hs] at h
  simpa only [iter_source, weightedPartial, weightedTerm, mul_div_assoc] using h

private theorem kernel_mem {s : ℝ} (hs : 0 < s) (x : LocalVertex p) :
    localGreen p s x ∈ supersolutions p (treeEigen p.1 s) x :=
  ⟨fun y => (localGreen_pos p hs x y).le,
    fun y => (localGreen_resolvent p hs x y).symm.le⟩

/-- Every finite weighted occupation kernel lies below every nonnegative supersolution. -/
theorem weightedPartial_le {ell : ℝ} (hell : 0 < ell) (x : LocalVertex p)
    {u : LocalVertex p → ℝ} (hu : u ∈ supersolutions p ell x) (N : ℕ) (y : LocalVertex p) :
    weightedPartial p ell x N y ≤ u y := by
  have hdiff : weightedSource p ell x ≤ u - walkWeight p ell • walkStep p u := by
    intro z
    have h := div_le_div_of_nonneg_right (hu.2 z) hell.le
    rw [sub_div, mul_div_cancel_left₀ _ hell.ne'] at h
    change ell⁻¹ * pointMass p x z ≤ u z - walkWeight p ell * walkStep p u z
    rw [weight_step p hell]
    simpa only [div_eq_mul_inv, mul_comm] using h
  calc
    _ = ∑ k ∈ Finset.range N, walkWeight p ell ^ k *
        ((walkStep p) ^ k) (weightedSource p ell x) y := by
      simp only [weightedPartial, weightedTerm, iter_source, mul_div_assoc]
    _ ≤ ∑ k ∈ Finset.range N, walkWeight p ell ^ k *
        ((walkStep p) ^ k) (u - walkWeight p ell • walkStep p u) y := by
      exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left
        (walkIter_mono p k hdiff y) (pow_nonneg (weight_nonneg p hell) k)
    _ = u y - walkWeight p ell ^ N * ((walkStep p) ^ N) u y := weighted_telescope p ell u N y
    _ ≤ u y := sub_le_self _ (mul_nonneg (pow_nonneg (weight_nonneg p hell) N)
      (walkIter_nonneg p N hu.1 y))

private theorem kernel_le_tempered {s : ℝ} (hs : 1 / 2 ≤ s) (x y : LocalVertex p) :
    localGreen p s x y ≤
      (localGreen p s x x / localGreen p (1 / 2) x x) * localGreen p (1 / 2) x y := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hA := localGreen_pos p hs0 x x
  have hB := localGreen_pos p (by norm_num : (0 : ℝ) < 1 / 2) x x
  rw [localGreen_self] at hA hB
  rw [localGreen, localGreen_self, localGreen_self, localGreen,
    ← mul_assoc, div_mul_cancel₀ _ hB.ne']
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge (localRatio_pos p x y) (localRatio_le_one p x y) hs)
    hA.le

private theorem kernel_iter_bound {s : ℝ} (hs : 1 / 2 ≤ s) (x y : LocalVertex p) (N : ℕ) :
    ((walkStep p) ^ N) (localGreen p s x) y ≤ spectralRatio p ^ N *
      ((localGreen p s x x / localGreen p (1 / 2) x x) * localGreen p (1 / 2) x y) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hc : 0 ≤ localGreen p s x x / localGreen p (1 / 2) x x :=
    div_nonneg (localGreen_pos p hs0 x x).le (localGreen_pos p (by norm_num) x x).le
  calc
    _ ≤ ((walkStep p) ^ N)
        ((localGreen p s x x / localGreen p (1 / 2) x x) • localGreen p (1 / 2) x) y :=
      walkIter_mono p N (fun z => kernel_le_tempered p hs x z) y
    _ = (localGreen p s x x / localGreen p (1 / 2) x x) *
        ((walkStep p) ^ N) (localGreen p (1 / 2) x) y := by
      rw [map_smul, Pi.smul_apply, smul_eq_mul]
    _ ≤ (localGreen p s x x / localGreen p (1 / 2) x x) *
        (spectralRatio p ^ N * localGreen p (1 / 2) x y) :=
      mul_le_mul_of_nonneg_left (tempered_iter_bound p x y N) hc
    _ = _ := by ring

private theorem weight_mul_ratio (s : ℝ) :
    walkWeight p (treeEigen p.1 s) * spectralRatio p =
      treeEigen p.1 (1 / 2) / treeEigen p.1 s := by
  rw [edge_eq]
  unfold walkWeight spectralRatio
  field_simp [(degree_pos p).ne', (eigen_pos p s).ne']

/-- Above the tempered edge, the exact walk remainder has a geometric bound. -/
theorem weighted_remainder_bound {s : ℝ} (hs : 1 / 2 ≤ s)
    (x y : LocalVertex p) (N : ℕ) :
    walkWeight p (treeEigen p.1 s) ^ N * ((walkStep p) ^ N) (localGreen p s x) y ≤
      (treeEigen p.1 (1 / 2) / treeEigen p.1 s) ^ N *
        ((localGreen p s x x / localGreen p (1 / 2) x x) * localGreen p (1 / 2) x y) := by
  calc
    _ ≤ walkWeight p (treeEigen p.1 s) ^ N * (spectralRatio p ^ N *
        ((localGreen p s x x / localGreen p (1 / 2) x x) * localGreen p (1 / 2) x y)) :=
      mul_le_mul_of_nonneg_left (kernel_iter_bound p hs x y N)
        (pow_nonneg (weight_nonneg p (eigen_pos p s)) N)
    _ = _ := by rw [← mul_assoc, ← mul_pow, weight_mul_ratio]

theorem tendsto_weightedPartial {s : ℝ} (hs : 1 / 2 < s) (x y : LocalVertex p) :
    Tendsto (fun N => weightedPartial p (treeEigen p.1 s) x N y) atTop
      (𝓝 (localGreen p s x y)) := by
  have hs0 : 0 < s := lt_trans (by norm_num) hs
  have hr0 : 0 ≤ treeEigen p.1 (1 / 2) / treeEigen p.1 s :=
    (div_pos (eigen_pos p _) (eigen_pos p _)).le
  have hr1 : treeEigen p.1 (1 / 2) / treeEigen p.1 s < 1 :=
    (div_lt_one (eigen_pos p s)).mpr (edge_lt p hs)
  have hr : |treeEigen p.1 (1 / 2) / treeEigen p.1 s| < 1 := by
    rw [abs_of_nonneg hr0]
    exact hr1
  have hpow := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hr
  have hz : Tendsto (fun N => walkWeight p (treeEigen p.1 s) ^ N *
      ((walkStep p) ^ N) (localGreen p s x) y) atTop (𝓝 0) := by
    apply squeeze_zero
      (fun N => mul_nonneg (pow_nonneg (weight_nonneg p (eigen_pos p s)) N)
        (walkIter_nonneg p N (fun z => (localGreen_pos p hs0 x z).le) y))
      (fun N => weighted_remainder_bound p hs.le x y N)
    simpa only [zero_mul] using hpow.mul_const
      ((localGreen p s x x / localGreen p (1 / 2) x x) * localGreen p (1 / 2) x y)
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => localGreen p s x y)
    atTop (𝓝 (localGreen p s x y))).sub hz
  simpa only [weightedPartial_eq p hs0, sub_zero] using ht

/-- The upper branch is the convergent weighted occupation kernel. -/
theorem hasSum_above {s : ℝ} (hs : 1 / 2 < s) (x y : LocalVertex p) :
    HasSum (fun N => weightedTerm p (treeEigen p.1 s) N x y) (localGreen p s x y) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun N => weightedTerm_nonneg p (eigen_pos p s) N x y) _).mpr
  exact tendsto_weightedPartial p hs x y

private theorem weightedTerm_antitone {ell mu : ℝ} (hell : 0 < ell) (hellmu : ell ≤ mu)
    (N : ℕ) (x y : LocalVertex p) : weightedTerm p mu N x y ≤ weightedTerm p ell N x y := by
  have hmu : 0 < mu := hell.trans_le hellmu
  have hb : walkWeight p mu ≤ walkWeight p ell :=
    div_le_div_of_nonneg_left (degree_pos p).le hell hellmu
  have hpow := pow_le_pow_left₀ (weight_nonneg p hmu) hb N
  calc
    _ ≤ walkWeight p ell ^ N * walkMass p N x y / mu :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpow (walkMass_nonneg p N x y)) hmu.le
    _ ≤ _ := div_le_div_of_nonneg_left
      (mul_nonneg (pow_nonneg (weight_nonneg p hell) N) (walkMass_nonneg p N x y)) hell hellmu

private theorem continuousAt_kernel {s : ℝ} (hs : 0 < s) (x y : LocalVertex p) :
    ContinuousAt (fun t => localGreen p t x y) s := by
  have hc : Continuous (fun t : ℝ => (p.1 : ℝ) ^ t) :=
    continuous_const.rpow continuous_id (fun _ => Or.inl (prime_pos p).ne')
  have hd : Continuous (fun t : ℝ => (p.1 : ℝ) ^ (2*t) - 1) :=
    (continuous_const.rpow (continuous_const.mul continuous_id)
      (fun _ => Or.inl (prime_pos p).ne')).sub continuous_const
  have hn : (p.1 : ℝ) ^ (2*s) - 1 ≠ 0 :=
    (sub_pos.mpr (Real.one_lt_rpow (prime_one_lt p) (by linarith only [hs]))).ne'
  have hR : Continuous (fun t : ℝ => localRatio p x y ^ t) :=
    continuous_const.rpow continuous_id (fun _ => Or.inl (localRatio_pos p x y).ne')
  simpa only [localGreen, treeGreen, pow_zero, mul_one, Pi.mul_apply, Pi.div_apply] using!
    (hc.continuousAt.div hd.continuousAt hn).mul hR.continuousAt

/-- The critical occupation sum converges pointwise and equals the tempered source kernel. -/
theorem hasSum_critical (x y : LocalVertex p) :
    HasSum (fun N => weightedTerm p (treeEigen p.1 (1 / 2)) N x y)
      (localGreen p (1 / 2) x y) := by
  have hbound (N : ℕ) : weightedPartial p (treeEigen p.1 (1 / 2)) x N y ≤
      localGreen p (1 / 2) x y :=
    weightedPartial_le p (eigen_pos p _) x (kernel_mem p (by norm_num) x) N y
  have hsum := summable_of_sum_range_le
    (fun N => weightedTerm_nonneg p (eigen_pos p (1 / 2)) N x y) hbound
  have hupper : (∑' N, weightedTerm p (treeEigen p.1 (1 / 2)) N x y) ≤
      localGreen p (1 / 2) x y :=
    le_of_tendsto hsum.hasSum.tendsto_sum_nat (Eventually.of_forall hbound)
  have hbelow (s : ℝ) (hs : 1 / 2 < s) : localGreen p s x y ≤
      ∑' N, weightedTerm p (treeEigen p.1 (1 / 2)) N x y := by
    have ha := hasSum_above p hs x y
    have h := Summable.tsum_le_tsum
      (fun N => weightedTerm_antitone p (eigen_pos p (1 / 2)) (edge_le p s) N x y)
      ha.summable hsum
    rwa [ha.tsum_eq] at h
  have hlim : Tendsto (fun s => localGreen p s x y) (𝓝[>] (1 / 2 : ℝ))
      (𝓝 (localGreen p (1 / 2) x y)) :=
    (continuousAt_kernel p (by norm_num : (0 : ℝ) < 1 / 2) x y).tendsto.mono_left
      nhdsWithin_le_nhds
  have hevent : ∀ᶠ s : ℝ in 𝓝[>] (1 / 2 : ℝ), 1 / 2 < s := self_mem_nhdsWithin
  have hlower : localGreen p (1 / 2) x y ≤
      ∑' N, weightedTerm p (treeEigen p.1 (1 / 2)) N x y :=
    le_of_tendsto hlim (hevent.mono fun s hs => hbelow s hs)
  have he := le_antisymm hupper hlower
  simpa only [he] using! hsum.hasSum

theorem hasSum_kernel {s : ℝ} (hs : 1 / 2 ≤ s) (x y : LocalVertex p) :
    HasSum (fun N => weightedTerm p (treeEigen p.1 s) N x y) (localGreen p s x y) := by
  rcases lt_or_eq_of_le hs with h | h
  · exact hasSum_above p h x y
  · rw [← h]
    exact hasSum_critical p x y

/-- The whole upper branch, including the spectral edge, is minimal without a growth hypothesis. -/
theorem localGreen_isLeast_of_half_le {s : ℝ} (hs : 1 / 2 ≤ s) (x : LocalVertex p) :
    IsLeast (supersolutions p (treeEigen p.1 s) x) (localGreen p s x) := by
  refine ⟨kernel_mem p (lt_of_lt_of_le (by norm_num) hs) x, ?_⟩
  intro u hu y
  exact le_of_tendsto (hasSum_kernel p hs x y).tendsto_sum_nat
    (Eventually.of_forall fun N => weightedPartial_le p (eigen_pos p s) x hu N y)

private theorem denominator_pos {s : ℝ} (hs : 0 < s) :
    0 < (p.1 : ℝ) ^ s - (p.1 : ℝ) ^ (-s) := by
  have ha := Real.one_lt_rpow (prime_one_lt p) hs
  have ha0 := Real.rpow_pos_of_pos (prime_pos p) s
  rw [Real.rpow_neg (prime_pos p).le]
  have hi : ((p.1 : ℝ) ^ s)⁻¹ < 1 := by
    rw [inv_eq_one_div]
    exact (div_lt_one ha0).mpr ha
  exact sub_pos.mpr (hi.trans ha)

private theorem diagonal_eq_inv {s : ℝ} (hs : 0 < s) (x : LocalVertex p) :
    localGreen p s x x = 1 / ((p.1 : ℝ) ^ s - (p.1 : ℝ) ^ (-s)) := by
  have ha := Real.one_lt_rpow (prime_one_lt p) hs
  have ha0 := Real.rpow_pos_of_pos (prime_pos p) s
  have hd := (denominator_pos p hs).ne'
  rw [Real.rpow_neg (prime_pos p).le] at hd
  have hsq : ((p.1 : ℝ) ^ s) ^ 2 - 1 ≠ 0 := by nlinarith only [ha]
  have he : (p.1 : ℝ) ^ (2*s) = ((p.1 : ℝ) ^ s) ^ 2 := by
    rw [show 2*s = s*2 by ring, Real.rpow_mul (prime_pos p).le, Real.rpow_two]
  rw [localGreen_self]
  simp only [treeGreen, pow_zero, mul_one]
  rw [he, Real.rpow_neg (prime_pos p).le]
  field_simp [ha0.ne', hd, hsq]

private theorem diagonal_strictAnti {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (x : LocalVertex p) : localGreen p t x x < localGreen p s x x := by
  have ht := hs.trans hst
  have h1 := Real.rpow_lt_rpow_of_exponent_lt (prime_one_lt p) hst
  have h2 := Real.rpow_lt_rpow_of_exponent_lt (prime_one_lt p) (neg_lt_neg hst)
  have hd : (p.1 : ℝ) ^ s - (p.1 : ℝ) ^ (-s) <
      (p.1 : ℝ) ^ t - (p.1 : ℝ) ^ (-t) := by linarith only [h1, h2]
  rw [diagonal_eq_inv p ht, diagonal_eq_inv p hs]
  apply (div_lt_div_iff₀ (denominator_pos p ht) (denominator_pos p hs)).mpr
  simpa only [one_mul] using hd

/-- Among positive source profiles, the walk selects exactly `s≥1/2`. -/
theorem minimal_branch_iff {s : ℝ} (hs : 0 < s) (x : LocalVertex p) :
    IsLeast (supersolutions p (treeEigen p.1 s) x) (localGreen p s x) ↔ 1 / 2 ≤ s := by
  constructor
  · intro h
    by_contra hn
    have hlt : s < 1 / 2 := lt_of_not_ge hn
    have ht : 0 < 1 - s := by linarith only [hlt]
    have hm := kernel_mem p ht x
    rw [eigen_reflection] at hm
    have hle := h.2 hm x
    have hdiag := diagonal_strictAnti p hs (by linarith only [hlt] : s < 1 - s) x
    exact (not_lt_of_ge hle) hdiag
  · exact fun h => localGreen_isLeast_of_half_le p h x

/-- The lower branch retains exactly the positive harmonic excess over its reflected walk kernel. -/
theorem lower_branch_harmonic_defect {s : ℝ} (hs : 0 < s) (hlt : s < 1 / 2)
    (x : LocalVertex p) :
    (∀ y, 0 ≤ localGreen p s x y - localGreen p (1 - s) x y) ∧
    (∀ y, treeEigen p.1 s * (localGreen p s x y - localGreen p (1 - s) x y) -
      (∑ w ∈ neighbors p y, (localGreen p s x w - localGreen p (1 - s) x w)) = 0) ∧
    0 < localGreen p s x x - localGreen p (1 - s) x x := by
  have ht : 1 / 2 ≤ 1 - s := by linarith only [hlt]
  have ht0 : 0 < 1 - s := by linarith only [hlt]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    have hm := kernel_mem p hs x
    rw [← eigen_reflection p s] at hm
    exact sub_nonneg.mpr ((localGreen_isLeast_of_half_le p ht x).2 hm y)
  · intro y
    have h1 := localGreen_resolvent p hs x y
    have h2 := localGreen_resolvent p ht0 x y
    rw [eigen_reflection] at h2
    rw [Finset.sum_sub_distrib]
    linear_combination h1 - h2
  · exact sub_pos.mpr (diagonal_strictAnti p hs (by linarith only [hlt]) x)

/-- Weighted iteration leaves a nonzero boundary term precisely on the lower branch. -/
theorem lower_branch_remainder_tendsto {s : ℝ} (hs : 0 < s) (hlt : s < 1 / 2)
    (x y : LocalVertex p) :
    Tendsto (fun N => walkWeight p (treeEigen p.1 s) ^ N *
      ((walkStep p) ^ N) (localGreen p s x) y) atTop
      (𝓝 (localGreen p s x y - localGreen p (1 - s) x y)) := by
  have ht : 1 / 2 < 1 - s := by linarith only [hlt]
  have hlim := tendsto_weightedPartial p ht x y
  rw [eigen_reflection] at hlim
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => localGreen p s x y)
    atTop (𝓝 (localGreen p s x y))).sub hlim
  simpa only [weightedPartial_eq p hs, sub_sub_cancel] using h

/-- Weil's prime-power coefficient is a normalized critical occupation sum on actual vertices. -/
theorem hasSum_weilPrimeKernel {m k : ℕ} (hm : 0 < m) (hk : 1 ≤ k) :
    HasSum (fun N => (Real.log p.1 * (((p.1 : ℝ) - 1) / Real.sqrt p.1)) *
      weightedTerm p (treeEigen p.1 (1 / 2)) N (baseVertex p) (apartmentVertex p k))
      (ArithmeticEffectivityTheory.weilPrimeKernel m (m * p.1 ^ k)) := by
  have h := (hasSum_critical p (baseVertex p) (apartmentVertex p k)).mul_left
    (Real.log p.1 * (((p.1 : ℝ) - 1) / Real.sqrt p.1))
  rw [← weilPrimeKernel_eq_localGreen p hm hk] at h
  simpa only using! h

#print axioms hasSum_above
#print axioms hasSum_critical
#print axioms localGreen_isLeast_of_half_le
#print axioms minimal_branch_iff
#print axioms lower_branch_harmonic_defect
#print axioms lower_branch_remainder_tendsto
#print axioms hasSum_weilPrimeKernel

end GaloisForLFunctions.HyperbolicArakelovTheory.MinimalGreen
