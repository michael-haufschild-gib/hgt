import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Leading order of a vector-valued power series

A power series with values in a normed space and a positive radius of convergence factors as
`g(c) = c^r · (u_r + O(c))`, where `r` is its first index with a nonzero coefficient.  Hence the
squared norm of `g` has exact leading order `‖u_r‖² c^{2r}`.

This is the vector form of the elementary fact that a Taylor expansion sees its first nonvanishing
coefficient: applied to a bounded projection of `cosh(cX)` or `sinh(cX)` it converts the first
visible even or odd polynomial degree into the exact rate of the corresponding parity energy.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Majorant for the tail of a vector power series beyond its leading index. -/
def seriesTailBound (u : ℕ → E) (R : ℝ) (r : ℕ) : ℝ :=
  (∑' k : ℕ, ‖u k‖ * R ^ k) / R ^ (r + 1)

omit [NormedSpace ℝ E] in
theorem seriesTailBound_nonneg (u : ℕ → E) {R : ℝ} (hR : 0 < R) (r : ℕ) :
    0 ≤ seriesTailBound u R r := by
  rw [seriesTailBound]
  have hnum : (0 : ℝ) ≤ ∑' k : ℕ, ‖u k‖ * R ^ k := by
    refine tsum_nonneg fun k => ?_
    have h1 : (0 : ℝ) ≤ ‖u k‖ := norm_nonneg _
    have h2 : (0 : ℝ) ≤ R ^ k := pow_nonneg hR.le k
    exact mul_nonneg h1 h2
  have hden : (0 : ℝ) < R ^ (r + 1) := pow_pos hR _
  exact div_nonneg hnum hden.le

set_option maxHeartbeats 1000000 in
/-- **The tail beyond the leading coefficient is linear in the parameter.** -/
theorem norm_sub_leading_le {u : ℕ → E} {R : ℝ} (hR : 0 < R)
    (hsum : Summable fun k => ‖u k‖ * R ^ k) (r : ℕ) {c : ℝ} (hcR : |c| ≤ R)
    {G : E} (hG : HasSum (fun k => c ^ k • u (r + k)) G) :
    ‖G - u r‖ ≤ |c| * seriesTailBound u R r := by
  have hf0 : (fun k : ℕ => c ^ k • u (r + k)) 0 = u r := by simp
  have hshift : HasSum (fun n : ℕ => c ^ (n + 1) • u (r + (n + 1))) (G - u r) := by
    refine (hasSum_nat_add_iff (f := fun k : ℕ => c ^ k • u (r + k)) 1).mpr ?_
    simpa [hf0] using hG
  have hmaj : ∀ n : ℕ, ‖c ^ (n + 1) • u (r + (n + 1))‖ ≤ |c| * (R ^ n * ‖u (r + 1 + n)‖) := by
    intro n
    have hpowle : |c| ^ n ≤ R ^ n := pow_le_pow_left₀ (abs_nonneg c) hcR n
    have hnorm : ‖c ^ (n + 1) • u (r + (n + 1))‖ = |c| ^ (n + 1) * ‖u (r + (n + 1))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_pow]
    rw [hnorm, show r + (n + 1) = r + 1 + n by omega, pow_succ]
    have hnn : (0 : ℝ) ≤ ‖u (r + 1 + n)‖ := norm_nonneg _
    calc |c| ^ n * |c| * ‖u (r + 1 + n)‖ ≤ R ^ n * |c| * ‖u (r + 1 + n)‖ := by
          have := mul_le_mul_of_nonneg_right hpowle (abs_nonneg c)
          exact mul_le_mul_of_nonneg_right this hnn
      _ = |c| * (R ^ n * ‖u (r + 1 + n)‖) := by ring
  have hshiftsum : Summable fun n : ℕ => ‖u (r + 1 + n)‖ * R ^ (r + 1 + n) := by
    have h := (summable_nat_add_iff (f := fun k : ℕ => ‖u k‖ * R ^ k) (r + 1)).mpr hsum
    refine h.congr fun n => ?_
    rw [Nat.add_comm n (r + 1)]
  have htail : Summable fun n : ℕ => R ^ n * ‖u (r + 1 + n)‖ := by
    refine (hshiftsum.mul_left ((R ^ (r + 1))⁻¹)).congr fun n => ?_
    have hsplit : R ^ (r + 1 + n) = R ^ (r + 1) * R ^ n := by rw [pow_add]
    rw [hsplit, show (R ^ (r + 1))⁻¹ * (‖u (r + 1 + n)‖ * (R ^ (r + 1) * R ^ n))
        = (R ^ (r + 1))⁻¹ * R ^ (r + 1) * (R ^ n * ‖u (r + 1 + n)‖) by ring,
      inv_mul_cancel₀ (pow_pos hR (r + 1)).ne', one_mul]
  have htailsum : (∑' n : ℕ, R ^ n * ‖u (r + 1 + n)‖) ≤ seriesTailBound u R r := by
    rw [seriesTailBound, le_div_iff₀ (pow_pos hR _), ← tsum_mul_right]
    have hcongr : ∀ n : ℕ, (R ^ n * ‖u (r + 1 + n)‖) * R ^ (r + 1)
        = ‖u (r + 1 + n)‖ * R ^ (r + 1 + n) := by
      intro n
      rw [pow_add]
      ring
    rw [tsum_congr hcongr]
    exact hshiftsum.tsum_le_tsum_of_inj (fun n => r + 1 + n)
      (fun a b hab => by dsimp only at hab; omega)
      (fun k _ => mul_nonneg (norm_nonneg _) (pow_nonneg hR.le _)) (fun n => le_of_eq rfl) hsum
  have hnormsum : Summable fun n : ℕ => ‖c ^ (n + 1) • u (r + (n + 1))‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hmaj (htail.mul_left |c|)
  have hle : ‖G - u r‖ ≤ ∑' n : ℕ, ‖c ^ (n + 1) • u (r + (n + 1))‖ := by
    rw [← hshift.tsum_eq]
    exact norm_tsum_le_tsum_norm hnormsum
  refine hle.trans ?_
  calc ∑' n : ℕ, ‖c ^ (n + 1) • u (r + (n + 1))‖
      ≤ ∑' n : ℕ, |c| * (R ^ n * ‖u (r + 1 + n)‖) :=
        hnormsum.tsum_le_tsum hmaj (htail.mul_left |c|)
    _ = |c| * ∑' n : ℕ, R ^ n * ‖u (r + 1 + n)‖ := tsum_mul_left
    _ ≤ |c| * seriesTailBound u R r := mul_le_mul_of_nonneg_left htailsum (abs_nonneg c)

set_option maxHeartbeats 1000000 in
/-- **The rescaled sum converges to the leading coefficient.**  Dividing a vector power series by
the power of its first nonzero index leaves that coefficient in the limit. -/
theorem tendsto_smul_inv_pow_of_hasSum {u : ℕ → E} {R : ℝ} (hR : 0 < R)
    (hsum : Summable fun k => ‖u k‖ * R ^ k) {r : ℕ} (hzero : ∀ k, k < r → u k = 0)
    {g : ℝ → E} (hg : ∀ c : ℝ, 0 < c → c ≤ R → HasSum (fun k => c ^ k • u k) (g c)) :
    Tendsto (fun c : ℝ => (c ^ r)⁻¹ • g c) (𝓝[>] (0 : ℝ)) (𝓝 (u r)) := by
  have hshift : ∀ c : ℝ, 0 < c → c ≤ R →
      HasSum (fun k => c ^ k • u (r + k)) ((c ^ r)⁻¹ • g c) := by
    intro c hc hcR
    have hzeros : ∑ i ∈ Finset.range r, c ^ i • u i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hzero i (Finset.mem_range.mp hi), smul_zero]
    have hadd : HasSum (fun n : ℕ => c ^ (n + r) • u (n + r)) (g c) := by
      refine (hasSum_nat_add_iff (f := fun k : ℕ => c ^ k • u k) r).mpr ?_
      simpa [hzeros] using hg c hc hcR
    have hscaled : HasSum (fun n : ℕ => (c ^ r)⁻¹ • (c ^ (n + r) • u (n + r)))
        ((c ^ r)⁻¹ • g c) := HasSum.const_smul ((c ^ r)⁻¹) hadd
    have hfun : (fun n : ℕ => (c ^ r)⁻¹ • (c ^ (n + r) • u (n + r)))
        = fun k : ℕ => c ^ k • u (r + k) := by
      funext n
      have hcoef : (c ^ r)⁻¹ * c ^ (n + r) = c ^ n := by
        rw [pow_add]
        field_simp
      rw [smul_smul, hcoef, add_comm n r]
    rwa [hfun] at hscaled
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hRmem : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ), c ≤ R :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds hR)
  have hbound : ∀ᶠ c : ℝ in 𝓝[>] (0 : ℝ),
      ‖(c ^ r)⁻¹ • g c - u r‖ ≤ |c| * seriesTailBound u R r := by
    filter_upwards [self_mem_nhdsWithin, hRmem] with c hc hcR
    exact norm_sub_leading_le hR hsum r
      (by rw [abs_of_pos (Set.mem_Ioi.mp hc)]; exact hcR)
      (hshift c (Set.mem_Ioi.mp hc) hcR)
  have hzeroLim : Tendsto (fun c : ℝ => |c| * seriesTailBound u R r)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun c : ℝ => |c| * seriesTailBound u R r) (𝓝 (0 : ℝ))
        (𝓝 (0 * seriesTailBound u R r)) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).mul tendsto_const_nhds
    rw [zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  exact squeeze_zero' (Filter.Eventually.of_forall fun c => norm_nonneg _) hbound hzeroLim

set_option maxHeartbeats 1000000 in
/-- **The two-sided rescaled limit.**  The same statement on a punctured neighbourhood of the
origin, for a series whose sum is available at both signs of the parameter. -/
theorem tendsto_smul_inv_pow_of_hasSum_punctured {u : ℕ → E} {R : ℝ} (hR : 0 < R)
    (hsum : Summable fun k => ‖u k‖ * R ^ k) {r : ℕ} (hzero : ∀ k, k < r → u k = 0)
    {g : ℝ → E} (hg : ∀ c : ℝ, c ≠ 0 → |c| ≤ R → HasSum (fun k => c ^ k • u k) (g c)) :
    Tendsto (fun c : ℝ => (c ^ r)⁻¹ • g c) (𝓝[≠] (0 : ℝ)) (𝓝 (u r)) := by
  have hshift : ∀ c : ℝ, c ≠ 0 → |c| ≤ R →
      HasSum (fun k => c ^ k • u (r + k)) ((c ^ r)⁻¹ • g c) := by
    intro c hc hcR
    have hzeros : ∑ i ∈ Finset.range r, c ^ i • u i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hzero i (Finset.mem_range.mp hi), smul_zero]
    have hadd : HasSum (fun n : ℕ => c ^ (n + r) • u (n + r)) (g c) := by
      refine (hasSum_nat_add_iff (f := fun k : ℕ => c ^ k • u k) r).mpr ?_
      simpa [hzeros] using hg c hc hcR
    have hscaled : HasSum (fun n : ℕ => (c ^ r)⁻¹ • (c ^ (n + r) • u (n + r)))
        ((c ^ r)⁻¹ • g c) := HasSum.const_smul ((c ^ r)⁻¹) hadd
    have hfun : (fun n : ℕ => (c ^ r)⁻¹ • (c ^ (n + r) • u (n + r)))
        = fun k : ℕ => c ^ k • u (r + k) := by
      funext n
      have hcoef : (c ^ r)⁻¹ * c ^ (n + r) = c ^ n := by
        rw [pow_add]
        field_simp
      rw [smul_smul, hcoef, add_comm n r]
    rwa [hfun] at hscaled
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hRmem : ∀ᶠ c : ℝ in 𝓝[≠] (0 : ℝ), |c| ≤ R := by
    refine eventually_nhdsWithin_of_eventually_nhds ?_
    have habs : Tendsto (fun c : ℝ => |c|) (𝓝 (0 : ℝ)) (𝓝 0) := by
      simpa using continuous_abs.tendsto (0 : ℝ)
    exact habs.eventually (eventually_le_nhds hR)
  have hbound : ∀ᶠ c : ℝ in 𝓝[≠] (0 : ℝ),
      ‖(c ^ r)⁻¹ • g c - u r‖ ≤ |c| * seriesTailBound u R r := by
    filter_upwards [self_mem_nhdsWithin, hRmem] with c hc hcR
    exact norm_sub_leading_le hR hsum r hcR (hshift c hc hcR)
  have hzeroLim : Tendsto (fun c : ℝ => |c| * seriesTailBound u R r)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun c : ℝ => |c| * seriesTailBound u R r) (𝓝 (0 : ℝ))
        (𝓝 (0 * seriesTailBound u R r)) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).mul tendsto_const_nhds
    rw [zero_mul] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  exact squeeze_zero' (Filter.Eventually.of_forall fun c => norm_nonneg _) hbound hzeroLim

set_option maxHeartbeats 1000000 in
/-- **The exact leading order of a vector power series.**  The squared norm of the sum divided by
the `2r`-th power of the parameter converges to the squared norm of the first nonzero
coefficient. -/
theorem tendsto_normSq_div_pow_of_hasSum {u : ℕ → E} {R : ℝ} (hR : 0 < R)
    (hsum : Summable fun k => ‖u k‖ * R ^ k) {r : ℕ} (hzero : ∀ k, k < r → u k = 0)
    {g : ℝ → E} (hg : ∀ c : ℝ, 0 < c → c ≤ R → HasSum (fun k => c ^ k • u k) (g c)) :
    Tendsto (fun c : ℝ => ‖g c‖ ^ (2 : ℕ) / c ^ (2 * r)) (𝓝[>] (0 : ℝ)) (𝓝 (‖u r‖ ^ (2 : ℕ))) := by
  have hlim := tendsto_smul_inv_pow_of_hasSum hR hsum hzero hg
  have hnorm : Tendsto (fun c : ℝ => ‖(c ^ r)⁻¹ • g c‖ ^ (2 : ℕ))
      (𝓝[>] (0 : ℝ)) (𝓝 (‖u r‖ ^ (2 : ℕ))) := (hlim.norm).pow 2
  refine hnorm.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c hc
  have hcpos : (0 : ℝ) < c := Set.mem_Ioi.mp hc
  have hpow : (0 : ℝ) < c ^ r := pow_pos hcpos r
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpow), mul_pow, inv_pow, ← pow_mul,
    mul_comm r 2]
  field_simp

/-- **The even substitution.**  A power series in `c²` with first nonzero coefficient at index `j`
has squared norm of exact order `c^{4j}`. -/
theorem tendsto_normSq_div_pow_even {u : ℕ → E} {R : ℝ} (hR : 0 < R)
    (hsum : Summable fun k => ‖u k‖ * R ^ k) {j : ℕ} (hzero : ∀ k, k < j → u k = 0)
    {g : ℝ → E} (hg : ∀ t : ℝ, 0 < t → t ≤ R → HasSum (fun k => t ^ k • u k) (g t)) :
    Tendsto (fun c : ℝ => ‖g (c ^ (2 : ℕ))‖ ^ (2 : ℕ) / c ^ (4 * j)) (𝓝[>] (0 : ℝ)) (𝓝 (‖u j‖ ^ (2 : ℕ))) := by
  have hbase := tendsto_normSq_div_pow_of_hasSum hR hsum hzero hg
  have hsq : Tendsto (fun c : ℝ => c ^ (2 : ℕ)) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have h0 : Tendsto (fun c : ℝ => c ^ (2 : ℕ)) (𝓝 (0 : ℝ)) (𝓝 0) := by
        simpa using (continuous_pow 2).tendsto (0 : ℝ)
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact pow_pos (Set.mem_Ioi.mp hc) 2
  refine (hbase.comp hsq).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with c _
  simp only [Function.comp_apply]
  rw [← pow_mul]
  congr 2
  ring

end GaloisForLFunctions.HTGeometry
