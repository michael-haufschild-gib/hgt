import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.PositiveCloudExtension
import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.PositiveConeCutoffs
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Positive atomic nullseries on a two-generator cone

For any positive clocks `a,b` and `0 < d < D`, there is a positive atomic
measure of mass two on `d ≤ Re z < D` whose exponential moments vanish at every
nonzero natural cone time `ma + nb`. Its real-part supremum is `D`, unattained;
at most `T` atoms have imaginary part of absolute value at most `T`.
Each weight is at least `1 / (1 + |Im z|)`.

Nested finite corrections use increasing real levels and geometrically decaying
block masses. Exact prefix cancellation survives the absolutely convergent sum.
Atoms are numbered below their heights; merging repeated points preserves every
moment, the weight lower bound, and the counting estimate.
-/

open Finset Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- Compatible positive prefixes retain every earlier atom and add a nonempty block. -/
structure StageChain (S : ℕ → Finset ℝ) (δ : ℕ → ℝ) where
  stage : (k : ℕ) → CloudStage S δ k
  first_nonempty : 0 < (stage 0).cloud.size
  extension : (k : ℕ) → StageExtension (stage k)
  next_eq : ∀ k, (extension k).next = stage (k + 1)

lemma exists_stage_chain (S : ℕ → Finset ℝ) (δ : ℕ → ℝ)
    (hS : ∀ k u, u ∈ S k → 0 < u) (hδ : Monotone δ)
    (htail : ∀ k, 2 * ∑ u ∈ S (k + 1) \ S k,
      Real.exp (-(δ (k + 1) - δ k) * u) ≤ (1 / 2 : ℝ) ^ (k + 1) / 4) :
    Nonempty (StageChain S δ) := by
  obtain ⟨first, hfirst⟩ := exists_initial_stage S δ (hS 0)
  let next : (k : ℕ) → (c : CloudStage S δ k) → StageExtension c := fun k c =>
    Classical.choice (exists_stage_extension c (hS (k + 1))
      (hδ (Nat.le_succ k)) (hδ (Nat.zero_le _)) (htail k))
  let stages : (k : ℕ) → CloudStage S δ k :=
    Nat.rec first (fun k c => (next k c).next)
  exact ⟨{
    stage := stages
    first_nonempty := hfirst
    extension := fun k => next k (stages k)
    next_eq := fun k => rfl
  }⟩

def StageChain.block {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ) : ℕ → Cloud
  | 0 => (c.stage 0).cloud
  | k + 1 => levelCloud (δ (k + 1)) (c.extension k).height (c.extension k).weight

lemma StageChain.cloud_succ {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ) (k : ℕ) :
    (c.stage (k + 1)).cloud = (c.stage k).cloud.append (c.block (k + 1)) := by
  rw [← c.next_eq k]
  exact (c.extension k).cloud_eq

lemma StageChain.block_size_pos {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ) (k : ℕ) :
    0 < (c.block k).size := by
  cases k with
  | zero => exact c.first_nonempty
  | succ k => exact (c.extension k).size_pos

lemma StageChain.block_mass {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ) (k : ℕ) :
    (c.block k).mass = (1 / 2 : ℝ) ^ k := by
  cases k with
  | zero =>
    have h := (c.stage 0).mass_eq
    change (c.stage 0).cloud.mass = _
    norm_num at h ⊢
    exact h
  | succ k =>
    have h := (c.stage (k + 1)).mass_eq
    rw [c.cloud_succ, Cloud.mass_append, (c.stage k).mass_eq, pow_succ] at h
    rw [pow_succ]
    linarith

lemma StageChain.block_positive {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ) (k : ℕ) :
    ∀ j, 0 < (c.block k).weight j := by
  cases k with
  | zero => exact (c.stage 0).positive
  | succ k =>
    have h := (c.stage (k + 1)).positive
    rw [c.cloud_succ] at h
    intro j
    simpa only [Cloud.append, Fin.append_right] using h (Fin.natAdd (c.stage k).cloud.size j)

lemma StageChain.block_real {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ) (k : ℕ)
    (j : Fin (c.block k).size) : ((c.block k).point j).re = δ k := by
  cases k with
  | zero => exact le_antisymm ((c.stage 0).real_bound j) ((c.stage 0).real_lower j)
  | succ k => exact levelCloud_real _ _ _ j

lemma StageChain.block_reciprocal {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ) (k : ℕ) :
    ∀ j, 1 / (1 + |((c.block k).point j).im|) ≤ (c.block k).weight j := by
  cases k with
  | zero => exact (c.stage 0).reciprocal_weight
  | succ k =>
    have h := (c.stage (k + 1)).reciprocal_weight
    rw [c.cloud_succ] at h
    intro j
    simpa only [Cloud.append, Fin.append_right] using h (Fin.natAdd (c.stage k).cloud.size j)

lemma StageChain.block_moment_succ {S : ℕ → Finset ℝ} {δ : ℕ → ℝ}
    (c : StageChain S δ) (k : ℕ) (u : ℝ) :
    (c.block (k + 1)).moment u = (c.stage (k + 1)).cloud.moment u - (c.stage k).cloud.moment u := by
  rw [c.cloud_succ, Cloud.moment_append]
  ring

lemma StageChain.sum_block_moment {S : ℕ → Finset ℝ} {δ : ℕ → ℝ}
    (c : StageChain S δ) (k : ℕ) (u : ℝ) :
    ∑ j ∈ range (k + 1), (c.block j).moment u = (c.stage k).cloud.moment u := by
  induction k with
  | zero => simp only [Nat.zero_add, sum_range_one, StageChain.block]
  | succ k ih => rw [sum_range_succ, ih, c.block_moment_succ]; ring

abbrev StageChain.AtomIndex {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ) :=
  (k : ℕ) × Fin (c.block k).size

def StageChain.atom {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ)
    (i : c.AtomIndex) : ℂ := (c.block i.1).point i.2

def StageChain.atomWeight {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ)
    (i : c.AtomIndex) : ℝ := (c.block i.1).weight i.2

lemma StageChain.atomWeight_pos {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ)
    (i : c.AtomIndex) : 0 < c.atomWeight i := c.block_positive i.1 i.2

lemma StageChain.atom_re {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ)
    (i : c.AtomIndex) : (c.atom i).re = δ i.1 := c.block_real i.1 i.2

lemma StageChain.summable_atomWeight {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ) :
    Summable c.atomWeight := by
  rw [summable_sigma_of_nonneg (f := c.atomWeight) (fun i => (c.atomWeight_pos i).le)]
  refine ⟨fun k => Summable.of_finite, ?_⟩
  have he : (fun k => ∑' j : Fin (c.block k).size, c.atomWeight ⟨k, j⟩) =
      fun k => (1 / 2 : ℝ) ^ k := by
    funext k
    rw [tsum_fintype]
    exact c.block_mass k
  rw [he]
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

lemma StageChain.tsum_atomWeight {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ) :
    ∑' i, c.atomWeight i = 2 := by
  have hσ := c.summable_atomWeight.hasSum.sigma
    (fun k => hasSum_fintype (fun j : Fin (c.block k).size => c.atomWeight ⟨k, j⟩))
  change HasSum (fun k => (c.block k).mass) (∑' i, c.atomWeight i) at hσ
  simp_rw [c.block_mass] at hσ
  have hg : HasSum (fun k : ℕ => (1 / 2 : ℝ) ^ k) 2 := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1) using 1; norm_num
  exact hσ.unique hg

lemma StageChain.summable_atom_moment {S : ℕ → Finset ℝ} {δ : ℕ → ℝ}
    (c : StageChain S δ) {D : ℝ} (hδ0 : ∀ k, 0 ≤ δ k) (hδD : ∀ k, δ k ≤ D) (u : ℝ) :
    Summable fun i : c.AtomIndex => (c.atomWeight i : ℂ) * Complex.exp ((u : ℂ) * c.atom i) := by
  refine Summable.of_norm_bounded (c.summable_atomWeight.mul_right (Real.exp (|u| * D))) fun i => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (c.atomWeight_pos i), Complex.norm_exp]
  have he : ((u : ℂ) * c.atom i).re = u * δ i.1 := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, c.atom_re]
  rw [he]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (c.atomWeight_pos i).le
  exact (mul_le_mul_of_nonneg_right (le_abs_self u) (hδ0 i.1)).trans
    (mul_le_mul_of_nonneg_left (hδD i.1) (abs_nonneg u))

lemma StageChain.hasSum_block_moment {S : ℕ → Finset ℝ} {δ : ℕ → ℝ}
    (c : StageChain S δ) (hS : Monotone S) {u : ℝ} {N : ℕ} (hu : u ∈ S N) :
    HasSum (fun k => (c.block k).moment u) 0 := by
  have hz : ∀ k, N ≤ k → (c.stage k).cloud.moment u = 0 :=
    fun k hk => (c.stage k).zero u (hS hk hu)
  have hzero : ∀ k ∉ range (N + 1), (c.block k).moment u = 0 := by
    intro k hk
    rw [mem_range, not_lt] at hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [c.block_moment_succ, hz (j + 1) (by omega), hz j (by omega), sub_self]
  have h : HasSum (fun k => (c.block k).moment u)
      (∑ k ∈ range (N + 1), (c.block k).moment u) := hasSum_sum_of_ne_finset_zero hzero
  rwa [c.sum_block_moment, hz N le_rfl] at h

/-- Every exhausted frequency has an absolutely convergent zero moment. -/
theorem StageChain.hasSum_atom_moment {S : ℕ → Finset ℝ} {δ : ℕ → ℝ}
    (c : StageChain S δ) (hS : Monotone S) {D : ℝ}
    (hδ0 : ∀ k, 0 ≤ δ k) (hδD : ∀ k, δ k ≤ D) {u : ℝ} {N : ℕ} (hu : u ∈ S N) :
    HasSum (fun i : c.AtomIndex => (c.atomWeight i : ℂ) * Complex.exp ((u : ℂ) * c.atom i)) 0 := by
  have hs := c.summable_atom_moment hδ0 hδD u
  have hσ := hs.hasSum.sigma (fun k => hasSum_fintype
    (fun j : Fin (c.block k).size => (c.atomWeight ⟨k, j⟩ : ℂ) *
      Complex.exp ((u : ℂ) * c.atom ⟨k, j⟩)))
  change HasSum (fun k => (c.block k).moment u)
    (∑' i : c.AtomIndex, (c.atomWeight i : ℂ) * Complex.exp ((u : ℂ) * c.atom i)) at hσ
  rw [← hσ.unique (c.hasSum_block_moment hS hu)]
  exact hs.hasSum

def StageChain.atomOffset {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ) (k : ℕ) : ℕ :=
  ∑ j ∈ range k, (c.block j).size

lemma StageChain.atomOffset_succ {S : ℕ → Finset ℝ} {δ : ℕ → ℝ}
    (c : StageChain S δ) (k : ℕ) :
    c.atomOffset (k + 1) = c.atomOffset k + (c.block k).size := sum_range_succ _ _

lemma StageChain.atomOffset_succ_eq_size {S : ℕ → Finset ℝ} {δ : ℕ → ℝ}
    (c : StageChain S δ) (k : ℕ) : c.atomOffset (k + 1) = (c.stage k).cloud.size := by
  induction k with
  | zero => simp only [Nat.zero_add, atomOffset, sum_range_one, StageChain.block]
  | succ k ih =>
    rw [c.atomOffset_succ, ih, c.cloud_succ]
    rfl

lemma StageChain.atomOffset_mono {S : ℕ → Finset ℝ} {δ : ℕ → ℝ}
    (c : StageChain S δ) : Monotone c.atomOffset := by
  apply monotone_nat_of_le_succ
  intro k
  rw [c.atomOffset_succ]
  omega

def StageChain.atomRank {S : ℕ → Finset ℝ} {δ : ℕ → ℝ} (c : StageChain S δ)
    (i : c.AtomIndex) : ℕ := c.atomOffset i.1 + i.2.val

lemma StageChain.atomRank_injective {S : ℕ → Finset ℝ} {δ : ℕ → ℝ}
    (c : StageChain S δ) : Function.Injective c.atomRank := by
  rintro ⟨k, j⟩ ⟨l, t⟩ h
  change c.atomOffset k + j.val = c.atomOffset l + t.val at h
  rcases lt_trichotomy k l with hkl | hkl | hkl
  · have hmono : c.atomOffset (k + 1) ≤ c.atomOffset l :=
      c.atomOffset_mono (by omega)
    have hj : c.atomOffset k + j.val < c.atomOffset (k + 1) := by
      rw [c.atomOffset_succ]
      omega
    omega
  · subst l
    have hjt : j = t := Fin.ext (Nat.add_left_cancel h)
    subst t
    rfl
  · have hmono : c.atomOffset (l + 1) ≤ c.atomOffset k :=
      c.atomOffset_mono (by omega)
    have ht : c.atomOffset l + t.val < c.atomOffset (l + 1) := by
      rw [c.atomOffset_succ]
      omega
    omega

lemma StageChain.atomRank_height {S : ℕ → Finset ℝ} {δ : ℕ → ℝ}
    (c : StageChain S δ) (i : c.AtomIndex) :
    ((c.atomRank i + 1 : ℕ) : ℝ) ≤ (c.atom i).im := by
  rcases i with ⟨k, j⟩
  cases k with
  | zero => simpa only [atomRank, atomOffset, sum_range_zero, zero_add, atom, StageChain.block]
      using (c.stage 0).rank_height j
  | succ k =>
    have h := (c.stage (k + 1)).rank_height
    rw [c.cloud_succ] at h
    have hj := h (Fin.natAdd (c.stage k).cloud.size j)
    simp only [Cloud.append, Fin.append_right, Fin.val_natAdd] at hj
    change ((c.atomOffset (k + 1) + j.val + 1 : ℕ) : ℝ) ≤ ((c.block (k + 1)).point j).im
    rw [c.atomOffset_succ_eq_size]
    exact hj

/-- At height `T`, the atom indices inject into `Fin floor(T)`. -/
theorem StageChain.exists_heightEmbedding {S : ℕ → Finset ℝ} {δ : ℕ → ℝ}
    (c : StageChain S δ) (T : ℝ) :
    Nonempty ({i : c.AtomIndex // |(c.atom i).im| ≤ T} ↪ Fin ⌊T⌋₊) := by
  refine ⟨{
  toFun := fun i => ⟨c.atomRank i.val, Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
    (Nat.le_floor ((c.atomRank_height i.val).trans ((le_abs_self _).trans i.property)))⟩
  inj' := by
    intro i j hij
    apply Subtype.ext
    apply c.atomRank_injective
    exact congrArg Fin.val hij
  }⟩

/-- Increasing real parts approach the upper boundary without reaching it. -/
def approachLevel (d D : ℝ) (k : ℕ) : ℝ := D - (D - d) * (1 / 2 : ℝ) ^ k

lemma approachLevel_zero (d D : ℝ) : approachLevel d D 0 = d := by
  simp only [approachLevel, pow_zero, mul_one]
  ring

lemma strictMono_approachLevel {d D : ℝ} (hdD : d < D) : StrictMono (approachLevel d D) := by
  apply strictMono_nat_of_lt_succ
  intro k
  have hp : 0 < (D - d) * (1 / 2 : ℝ) ^ k :=
    mul_pos (sub_pos.mpr hdD) (pow_pos (by norm_num) k)
  simp only [approachLevel, pow_succ]
  nlinarith [hp]

lemma approachLevel_lower {d D : ℝ} (hdD : d < D) (k : ℕ) : d ≤ approachLevel d D k := by
  have h := mul_le_mul_of_nonneg_left
    (pow_le_one₀ (n := k) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1))
    (sub_nonneg.mpr hdD.le)
  simp only [approachLevel]
  linarith

lemma approachLevel_lt {d D : ℝ} (hdD : d < D) (k : ℕ) : approachLevel d D k < D := by
  have hp : 0 < (D - d) * (1 / 2 : ℝ) ^ k :=
    mul_pos (sub_pos.mpr hdD) (pow_pos (by norm_num) k)
  simp only [approachLevel]
  linarith

lemma tendsto_approachLevel (d D : ℝ) : Tendsto (approachLevel d D) atTop (𝓝 D) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)
  have h : Tendsto (fun k : ℕ => D - (D - d) * (1 / 2 : ℝ) ^ k) atTop
      (𝓝 (D - (D - d) * 0)) := tendsto_const_nhds.sub (tendsto_const_nhds.mul hp)
  change Tendsto (fun k : ℕ => D - (D - d) * (1 / 2 : ℝ) ^ k) atTop (𝓝 D)
  simpa only [mul_zero, sub_zero] using h

/-- A positive locally finite nullseries on an actual two-clock cone, of mass two and unattained width. -/
theorem exists_two_clock_positive_nullseries {a b d D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hdD : d < D) :
    ∃ (ι : Type) (_ : Countable ι) (z : ι → ℂ) (w : ι → ℝ),
      (∀ i, 0 < w i) ∧ HasSum w 2 ∧
      (∀ i, d ≤ (z i).re ∧ (z i).re < D) ∧
      (∀ r : ℝ, r < D → ∃ i, r < (z i).re) ∧
      (∀ i, 1 / (1 + |(z i).im|) ≤ w i) ∧
      (∀ T : ℝ, Nonempty ({i : ι // |(z i).im| ≤ T} ↪ Fin ⌊T⌋₊)) ∧
      (∀ t : PositiveCone a b,
        HasSum (fun i => (w i : ℂ) * Complex.exp ((t.val : ℂ) * z i)) 0) := by
  let δ := approachLevel d D
  have hδ : StrictMono δ := strictMono_approachLevel hdD
  obtain ⟨S, hSmono, hSpos, hcover, htail⟩ := exists_nested_cone_cutoffs ha hb
    (fun k => δ (k + 1) - δ k) (fun k => (1 / 2 : ℝ) ^ (k + 1) / 8)
    (fun k => sub_pos.mpr (hδ (Nat.lt_succ_self k)))
    (fun k => div_pos (pow_pos (by norm_num) _) (by norm_num))
  have htail' : ∀ k, 2 * ∑ u ∈ S (k + 1) \ S k,
      Real.exp (-(δ (k + 1) - δ k) * u) ≤ (1 / 2 : ℝ) ^ (k + 1) / 4 := by
    intro k
    linarith [htail k]
  obtain ⟨c⟩ := exists_stage_chain S δ hSpos hδ.monotone htail'
  refine ⟨c.AtomIndex, inferInstance, c.atom, c.atomWeight, c.atomWeight_pos, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := c.summable_atomWeight.hasSum
    rwa [c.tsum_atomWeight] at h
  · intro i
    rw [c.atom_re]
    exact ⟨approachLevel_lower hdD i.1, approachLevel_lt hdD i.1⟩
  · intro r hr
    have he : ∀ᶠ k : ℕ in atTop, r < δ k :=
      (tendsto_approachLevel d D).eventually (eventually_gt_nhds hr)
    obtain ⟨k, hk⟩ := he.exists
    refine ⟨⟨k, ⟨0, c.block_size_pos k⟩⟩, ?_⟩
    rw [c.atom_re]
    exact hk
  · intro i
    exact c.block_reciprocal i.1 i.2
  · intro T
    exact c.exists_heightEmbedding T
  · intro t
    obtain ⟨N, hN⟩ := hcover t
    exact c.hasSum_atom_moment hSmono
      (fun k => hd.le.trans (approachLevel_lower hdD k))
      (fun k => (approachLevel_lt hdD k).le) hN

/-- Merging repeated nodes preserves positivity, cone moments, height counts, and the unattained width. -/
theorem exists_two_clock_positive_atomic_nullseries {a b d D : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hdD : d < D) :
    ∃ (ι : Type) (_ : Countable ι) (z : ι → ℂ) (w : ι → ℝ),
      Function.Injective z ∧ (∀ i, 0 < w i) ∧ HasSum w 2 ∧
      (∀ i, d ≤ (z i).re ∧ (z i).re < D) ∧
      (∀ r : ℝ, r < D → ∃ i, r < (z i).re) ∧
      (∀ i, 1 / (1 + |(z i).im|) ≤ w i) ∧
      (∀ T : ℝ, Nonempty ({i : ι // |(z i).im| ≤ T} ↪ Fin ⌊T⌋₊)) ∧
      (∀ t : PositiveCone a b,
        HasSum (fun i => (w i : ℂ) * Complex.exp ((t.val : ℂ) * z i)) 0) := by
  classical
  obtain ⟨ι, hι, z, w, hw, hs, hstrip, hwidth, hbound, hcount, hmoment⟩ :=
    exists_two_clock_positive_nullseries ha hb hd hdD
  letI : Countable ι := hι
  let J : Type := Set.range z
  let π : ι → J := fun i => ⟨z i, ⟨i, rfl⟩⟩
  let rep : J → ι := fun v => v.property.choose
  have hrep : ∀ v : J, z (rep v) = v.val := fun v => v.property.choose_spec
  have hinj : Function.Injective rep := by
    intro u v huv
    apply Subtype.ext
    exact (hrep u).symm.trans ((congrArg z huv).trans (hrep v))
  letI : Countable J := hinj.countable
  let W : J → ℝ := fun v => ∑' i : π ⁻¹' {v}, w i.val
  have hsW : HasSum W 2 := hs.tsum_fiberwise π
  have hle : ∀ v, w (rep v) ≤ W v := by
    intro v
    let i : π ⁻¹' {v} := ⟨rep v, show π (rep v) = v from Subtype.ext (hrep v)⟩
    exact (hs.summable.subtype (fun i => π i = v)).le_tsum i (fun j _ => (hw j.val).le)
  refine ⟨J, inferInstance, (fun v => v.val), W, Subtype.coe_injective,
    (fun v => (hw (rep v)).trans_le (hle v)), hsW, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    have h := hstrip (rep v)
    rwa [hrep v] at h
  · intro r hr
    obtain ⟨i, hi⟩ := hwidth r hr
    exact ⟨π i, hi⟩
  · intro v
    have h := hbound (rep v)
    rw [hrep v] at h
    exact h.trans (hle v)
  · intro T
    let e : {v : J // |v.val.im| ≤ T} ↪ {i : ι // |(z i).im| ≤ T} := {
      toFun := fun v => ⟨rep v.val, by rw [hrep v.val]; exact v.property⟩
      inj' := by
        intro u v huv
        apply Subtype.ext
        apply hinj
        exact congrArg Subtype.val huv
    }
    exact ⟨e.trans (Classical.choice (hcount T))⟩
  · intro t
    have h := (hmoment t).tsum_fiberwise π
    have he : (fun v : J => ∑' i : π ⁻¹' {v},
        (w i.val : ℂ) * Complex.exp ((t.val : ℂ) * z i.val)) =
        fun v : J => (W v : ℂ) * Complex.exp ((t.val : ℂ) * v.val) := by
      funext v
      calc (∑' i : π ⁻¹' {v}, (w i.val : ℂ) * Complex.exp ((t.val : ℂ) * z i.val))
          = ∑' i : π ⁻¹' {v}, (w i.val : ℂ) * Complex.exp ((t.val : ℂ) * v.val) := by
              apply tsum_congr
              intro i
              have hi : z i.val = v.val := congrArg Subtype.val i.property
              rw [hi]
        _ = (∑' i : π ⁻¹' {v}, (w i.val : ℂ)) * Complex.exp ((t.val : ℂ) * v.val) :=
              tsum_mul_right
        _ = (W v : ℂ) * Complex.exp ((t.val : ℂ) * v.val) := by
              rw [← Complex.ofReal_tsum]
    rw [he] at h
    exact h

#print axioms exists_two_clock_positive_atomic_nullseries



end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
