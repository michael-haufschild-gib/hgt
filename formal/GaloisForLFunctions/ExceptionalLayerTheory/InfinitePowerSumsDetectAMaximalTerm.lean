import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic

/-!
# Detecting a maximal term in an infinite power sum

For an absolutely summable nonzero complex family, let `R` be its maximal
modulus and `M = ∑ ‖zᵢ‖ / R`. Some `1 ≤ k ≤ 64 M` satisfies
`Re ∑ zᵢ^k > R^k / 8`.

A Fejér polynomial supplies a lower bound proportional to `‖zᵢ‖`, so its
weighted sum converges over the full family. A unit-modulus term gives a
quadratic positive contribution; nonnegative moment weights then force a
positive real power sum. No finite-support or modulus-gap premise is used.
-/

open Complex Finset Filter Topology

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private def geometricPrefix (N : ℕ) (z : ℂ) : ℂ := ∑ k ∈ range N, z ^ k

private def triangularPower (N : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ range N, ∑ k ∈ range j, z ^ (k + 1)

private theorem geometricPrefix_succ (N : ℕ) (z : ℂ) :
    geometricPrefix (N + 1) z = 1 + z * geometricPrefix N z := by
  rw [geometricPrefix, sum_range_succ']
  simp only [pow_zero]
  rw [geometricPrefix, mul_sum]
  simp_rw [pow_succ, mul_comm z]
  exact add_comm _ _

private theorem triangularPower_succ (N : ℕ) (z : ℂ) :
    triangularPower (N + 1) z = triangularPower N z + z * geometricPrefix N z := by
  rw [triangularPower, sum_range_succ]
  congr 1
  rw [geometricPrefix, mul_sum]
  exact sum_congr rfl fun k _ => by rw [pow_succ, mul_comm]

private theorem geometricPrefix_normSq_step (N : ℕ) (z : ℂ) :
    normSq (geometricPrefix (N + 1) z) - normSq z * normSq (geometricPrefix N z) =
      1 + 2 * (z * geometricPrefix N z).re := by
  rw [geometricPrefix_succ]
  simp only [normSq_apply, add_re, add_im, one_re, one_im, mul_re, mul_im]
  ring

/-- The Fejér polynomial on the disc is a sum of squares. -/
private theorem triangularPower_square_identity (N : ℕ) (z : ℂ) :
    (N : ℝ) + 2 * (triangularPower N z).re =
      normSq (geometricPrefix N z) +
        (1 - normSq z) * ∑ j ∈ range N, normSq (geometricPrefix j z) := by
  induction N with
  | zero => simp [geometricPrefix, triangularPower]
  | succ N ih =>
    rw [triangularPower_succ, add_re, sum_range_succ, Nat.cast_add, Nat.cast_one]
    have hs := geometricPrefix_normSq_step N z
    linarith only [ih, hs]

private theorem triangularPower_re_ge (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    -(N : ℝ) / 2 ≤ (triangularPower N z).re := by
  have hzsq : normSq z ≤ 1 := by
    rw [normSq_eq_norm_sq]
    nlinarith only [hz, norm_nonneg z]
  have hs := triangularPower_square_identity N z
  have hn : 0 ≤ normSq (geometricPrefix N z) := normSq_nonneg _
  have hsum : 0 ≤ ∑ j ∈ range N, normSq (geometricPrefix j z) :=
    sum_nonneg fun j _ => normSq_nonneg _
  have hp := mul_nonneg (sub_nonneg.mpr hzsq) hsum
  linarith only [hs, hn, hp]

private theorem geometricPrefix_norm_le_two {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) (N : ℕ) :
    ‖geometricPrefix N z‖ ≤ 2 := by
  induction N with
  | zero => simp [geometricPrefix]
  | succ N ih =>
    rw [geometricPrefix_succ]
    have ht := norm_add_le (1 : ℂ) (z * geometricPrefix N z)
    rw [norm_one, norm_mul] at ht
    have hm := mul_le_mul_of_nonneg_left ih (norm_nonneg z)
    linarith only [ht, hm, hz]

/-- The lower bound is summable even when infinitely many modes occur. -/
private theorem triangularPower_re_ge_norm (N : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    -2 * N * ‖z‖ ≤ (triangularPower N z).re := by
  by_cases hsmall : ‖z‖ ≤ 1 / 2
  · have hb : ‖triangularPower N z‖ ≤ 2 * N * ‖z‖ := by
      induction N with
      | zero => simp [triangularPower]
      | succ N ih =>
        rw [triangularPower_succ]
        have ht := norm_add_le (triangularPower N z) (z * geometricPrefix N z)
        rw [norm_mul] at ht
        have hm := mul_le_mul_of_nonneg_left (geometricPrefix_norm_le_two hsmall N)
          (norm_nonneg z)
        push_cast
        nlinarith only [ht, ih, hm]
    have hr := neg_abs_le (triangularPower N z).re
    have ha := abs_re_le_norm (triangularPower N z)
    linarith only [hb, hr, ha]
  · have hb := triangularPower_re_ge N hz
    have hp := mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
      (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hsmall)))
    nlinarith only [hb, hp, (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

private theorem triangularPower_one (N : ℕ) :
    (triangularPower N 1).re = (N : ℝ) * (N - 1) / 2 := by
  have hg : ∀ N : ℕ, geometricPrefix N 1 = (N : ℂ) := by
    intro N
    simp [geometricPrefix]
  induction N with
  | zero => simp [triangularPower]
  | succ N ih =>
    rw [triangularPower_succ, one_mul, hg, add_re, natCast_re]
    push_cast
    rw [ih]
    ring

private def weightedTriangularPower (N : ℕ) (w z : ℂ) : ℝ :=
  (triangularPower N z).re +
    ((triangularPower N (z * w)).re + (triangularPower N (z * (starRingEnd ℂ) w)).re) / 2

private theorem weightedTriangularPower_eq (N : ℕ) (w z : ℂ) :
    weightedTriangularPower N w z =
      ∑ j ∈ range N, ∑ k ∈ range j, (1 + (w ^ (k + 1)).re) * (z ^ (k + 1)).re := by
  have hp (k : ℕ) :
      (1 + (w ^ k).re) * (z ^ k).re =
        (z ^ k).re + (((z * w) ^ k).re + ((z * (starRingEnd ℂ) w) ^ k).re) / 2 := by
    simp only [mul_pow, ← map_pow, mul_re, conj_re, conj_im]
    ring
  simp_rw [hp]
  simp only [weightedTriangularPower, triangularPower, re_sum, add_div,
    sum_add_distrib, ← sum_div]

private theorem weightedTriangularPower_ge (N : ℕ) {w z : ℂ}
    (hw : ‖w‖ = 1) (hz : ‖z‖ ≤ 1) :
    -4 * N * ‖z‖ ≤ weightedTriangularPower N w z := by
  have hzw : ‖z * w‖ = ‖z‖ := by rw [norm_mul, hw, mul_one]
  have hzwc : ‖z * (starRingEnd ℂ) w‖ = ‖z‖ := by rw [norm_mul, norm_conj, hw, mul_one]
  have h₁ := triangularPower_re_ge_norm N hz
  have h₂ := triangularPower_re_ge_norm N (z := z * w) (hzw.trans_le hz)
  have h₃ := triangularPower_re_ge_norm N (z := z * (starRingEnd ℂ) w) (hzwc.trans_le hz)
  rw [hzw] at h₂
  rw [hzwc] at h₃
  unfold weightedTriangularPower
  linarith only [h₁, h₂, h₃]

private theorem weightedTriangularPower_self (N : ℕ) {w : ℂ} (hw : ‖w‖ = 1) :
    (N : ℝ) * (N - 4) / 4 ≤ weightedTriangularPower N w w := by
  have hwc : w * (starRingEnd ℂ) w = 1 := by rw [mul_conj, normSq_eq_norm_sq, hw]; norm_num
  have h₁ := triangularPower_re_ge N (le_of_eq hw)
  have h₂ := triangularPower_re_ge N (z := w * w) (by rw [norm_mul, hw]; norm_num)
  rw [weightedTriangularPower, hwc, triangularPower_one]
  linarith only [h₁, h₂]

private theorem norm_pow_succ_le {z : ℂ} (hz : ‖z‖ ≤ 1) (k : ℕ) :
    ‖z ^ (k + 1)‖ ≤ ‖z‖ := by
  rw [norm_pow]
  simpa using pow_le_pow_of_le_one (norm_nonneg z) hz (Nat.succ_le_succ (Nat.zero_le k))

/-- An absolutely summable family in the closed unit disc with a unit-modulus
term has a positive real power sum before a constant times its total mass.
The Fejér weights retain the entire infinite family. -/
theorem infinite_real_power_sum_detects_unit_term {ι : Type*} {z : ι → ℂ}
    (hz : Summable (fun i => ‖z i‖)) (hdisc : ∀ i, ‖z i‖ ≤ 1)
    (i₀ : ι) (hi₀ : ‖z i₀‖ = 1) :
    ∃ k : ℕ, 1 ≤ k ∧ (k : ℝ) ≤ 64 * ∑' i, ‖z i‖ ∧
      1 / 8 < (∑' i, z i ^ k).re := by
  classical
  let M : ℝ := ∑' i, ‖z i‖
  have hM : 1 ≤ M := by
    simpa only [hi₀] using hz.le_tsum i₀ (fun i _ => norm_nonneg (z i))
  let N : ℕ := ⌈32 * M⌉₊ + 9
  have hNlo : 32 * M + 9 ≤ (N : ℝ) := by
    have hc := Nat.le_ceil (32 * M)
    dsimp [N]
    push_cast
    linarith only [hc]
  have hNhi : (N : ℝ) < 32 * M + 10 := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ 32 * M by linarith only [hM])
    dsimp [N]
    push_cast
    linarith only [hc]
  have hNpos : (0 : ℝ) < N := by linarith only [hNlo, hM]
  have hNbound : (N : ℝ) - 1 ≤ 64 * M := by linarith only [hNhi, hM]
  have hsp (k : ℕ) : Summable (fun i => z i ^ (k + 1)) :=
    hz.of_norm_bounded fun i => norm_pow_succ_le (hdisc i) k
  have hsr (k : ℕ) : Summable (fun i => (z i ^ (k + 1)).re) :=
    reCLM.summable (hsp k)
  have hsw (k : ℕ) :
      Summable (fun i => (1 + (z i₀ ^ (k + 1)).re) * (z i ^ (k + 1)).re) :=
    (hsr k).mul_left _
  have hsj (j : ℕ) := summable_sum (s := range j) (fun k _ => hsw k)
  have hsU : Summable (fun i => weightedTriangularPower N (z i₀) (z i)) := by
    simpa only [weightedTriangularPower_eq] using
      summable_sum (s := range N) (fun j _ => hsj j)
  have hts : (∑' i, weightedTriangularPower N (z i₀) (z i)) =
      ∑ j ∈ range N, ∑ k ∈ range j,
        (1 + (z i₀ ^ (k + 1)).re) * (∑' i, z i ^ (k + 1)).re := by
    simp_rw [weightedTriangularPower_eq]
    rw [Summable.tsum_finsetSum (fun j _ => hsj j)]
    apply sum_congr rfl
    intro j _
    rw [Summable.tsum_finsetSum (fun k _ => hsw k)]
    apply sum_congr rfl
    intro k _
    rw [tsum_mul_left, re_tsum (hsp k)]
  have hlower : (N : ℝ) * (N - 4) / 4 - 4 * N * M ≤
      ∑' i, weightedTriangularPower N (z i₀) (z i) := by
    have hmass : Summable (fun i => (4 : ℝ) * N * ‖z i‖) := hz.mul_left _
    have haug := hsU.add hmass
    have hle := haug.le_tsum i₀ (fun i _ => by
      have hg := weightedTriangularPower_ge N hi₀ (hdisc i)
      linarith only [hg])
    rw [hsU.tsum_add hmass, tsum_mul_left] at hle
    have hself := weightedTriangularPower_self N hi₀
    have hnonneg : (0 : ℝ) ≤ 4 * N * ‖z i₀‖ := by positivity
    change _ ≤ _ + 4 * N * M at hle
    linarith only [hle, hself, hnonneg]
  by_contra hbad
  have hsmall : ∀ k : ℕ, 1 ≤ k → (k : ℝ) ≤ 64 * M →
      (∑' i, z i ^ k).re ≤ 1 / 8 := by
    intro k hk hkM
    exact le_of_not_gt (fun h => hbad ⟨k, hk, hkM, h⟩)
  have hupper : (∑' i, weightedTriangularPower N (z i₀) (z i)) ≤
      (N : ℝ) * (N - 1) / 8 := by
    rw [hts]
    calc
      _ ≤ ∑ j ∈ range N, ∑ k ∈ range j, (1 / 4 : ℝ) := by
        apply sum_le_sum
        intro j hj
        apply sum_le_sum
        intro k hk
        have hkN : k + 2 ≤ N := by
          have := mem_range.mp hk
          have := mem_range.mp hj
          omega
        have hkR : (k + 1 : ℝ) ≤ (N : ℝ) - 1 := by
          have hh : (k + 2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
          linarith only [hh]
        have hm := hsmall (k + 1) (Nat.succ_pos k) (by push_cast; linarith only [hkR, hNbound])
        have habs := abs_re_le_norm (z i₀ ^ (k + 1))
        rw [norm_pow, hi₀, one_pow] at habs
        have hwlo : 0 ≤ 1 + (z i₀ ^ (k + 1)).re := by
          have hneg := neg_abs_le (z i₀ ^ (k + 1)).re
          linarith only [habs, hneg]
        have hwhi : 1 + (z i₀ ^ (k + 1)).re ≤ 2 := by
          have hpos := le_abs_self (z i₀ ^ (k + 1)).re
          linarith only [habs, hpos]
        have hmul := mul_le_mul_of_nonneg_left hm hwlo
        linarith only [hmul, hwhi]
      _ = (N : ℝ) * (N - 1) / 8 := by
        have hcount : (∑ j ∈ range N, ∑ _k ∈ range j, (1 : ℝ)) =
            (N : ℝ) * (N - 1) / 2 := by
          simpa only [triangularPower, re_sum, one_pow, one_re] using triangularPower_one N
        calc
          _ = (∑ j ∈ range N, ∑ _k ∈ range j, (1 : ℝ)) / 4 := by
            simp only [sum_div]
          _ = (N : ℝ) * (N - 1) / 8 := by rw [hcount]; ring
  have hcontra : 0 < (N : ℝ) * (N - 7 - 32 * M) := by
    exact mul_pos hNpos (by linarith only [hNlo])
  nlinarith only [hlower, hupper, hcontra]

/-- Absolute summability makes every positive superlevel finite, hence a
nonzero family attains a positive maximal modulus. -/
theorem exists_maximal_norm_of_summable {ι : Type*} {z : ι → ℂ}
    (hz : Summable (fun i => ‖z i‖)) (i₀ : ι) (hi₀ : z i₀ ≠ 0) :
    ∃ j : ι, 0 < ‖z j‖ ∧ ∀ i, ‖z i‖ ≤ ‖z j‖ := by
  classical
  have hpos := norm_pos_iff.mpr hi₀
  have hf : {i | ‖z i₀‖ ≤ ‖z i‖}.Finite := by
    have he := hz.tendsto_cofinite_zero.eventually_lt_const hpos
    simpa only [not_lt] using Filter.eventually_cofinite.mp he
  have hi : i₀ ∈ hf.toFinset := by simp
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image hf.toFinset (fun i => ‖z i‖) ⟨i₀, hi⟩
  have hjlo : ‖z i₀‖ ≤ ‖z j‖ := hmax i₀ hi
  refine ⟨j, hpos.trans_le hjlo, fun i => ?_⟩
  by_cases h : ‖z i₀‖ ≤ ‖z i‖
  · exact hmax i (hf.mem_toFinset.mpr h)
  · exact (le_of_lt (lt_of_not_ge h)).trans hjlo

/-- A real power sum detects the maximal modulus of any nonzero absolutely
summable complex family. The allowed order depends on its total mass divided
by that modulus, not on support size or a gap between successive moduli. -/
theorem infinite_real_power_sum_detects_maximal_term {ι : Type*} {z : ι → ℂ}
    (hz : Summable (fun i => ‖z i‖)) (i₀ : ι) (hi₀ : z i₀ ≠ 0) :
    ∃ j : ι, ∃ k : ℕ, 0 < ‖z j‖ ∧ (∀ i, ‖z i‖ ≤ ‖z j‖) ∧
      1 ≤ k ∧ (k : ℝ) ≤ 64 * (∑' i, ‖z i‖) / ‖z j‖ ∧
      ‖z j‖ ^ k / 8 < (∑' i, z i ^ k).re := by
  obtain ⟨j, hj, hmax⟩ := exists_maximal_norm_of_summable hz i₀ hi₀
  let R : ℝ := ‖z j‖
  have hR : 0 < R := hj
  have hnorm (i : ι) : ‖z i / (R : ℂ)‖ = ‖z i‖ / R := by
    rw [norm_div, norm_real, Real.norm_of_nonneg hR.le]
  have hsum : Summable (fun i => ‖z i / (R : ℂ)‖) := by
    simp_rw [hnorm]
    exact hz.div_const R
  have hdisc (i : ι) : ‖z i / (R : ℂ)‖ ≤ 1 := by
    rw [hnorm, div_le_one hR]
    exact hmax i
  have hunit : ‖z j / (R : ℂ)‖ = 1 := by rw [hnorm]; exact div_self hR.ne'
  obtain ⟨k, hk, hkM, hkpos⟩ := infinite_real_power_sum_detects_unit_term hsum hdisc j hunit
  have hmass : (∑' i, ‖z i / (R : ℂ)‖) = (∑' i, ‖z i‖) / R := by
    simp_rw [hnorm]
    exact tsum_div_const
  have hmoment : (∑' i, (z i / (R : ℂ)) ^ k).re =
      (∑' i, z i ^ k).re / R ^ k := by
    simp_rw [div_pow]
    rw [tsum_div_const, ← ofReal_pow, div_ofReal_re]
  refine ⟨j, k, hj, hmax, hk, ?_, ?_⟩
  · rw [hmass] at hkM
    simpa only [mul_div_assoc] using hkM
  · rw [hmoment] at hkpos
    have hh := (lt_div_iff₀ (pow_pos hR k)).mp hkpos
    change R ^ k / 8 < _
    linarith only [hh]

end GaloisForLFunctions.ExceptionalLayerTheory

#print axioms GaloisForLFunctions.ExceptionalLayerTheory.infinite_real_power_sum_detects_maximal_term
