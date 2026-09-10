import GaloisForLFunctions.HTGeometry.AltynbekovSelfConsistentGroupTransfer
import Mathlib.GroupTheory.OrderOfElement

/-!
# The zero-refresh boundary: idempotent laws on finite groups

The self-consistent convolution model inspired by arXiv:2609.10119 has a unique
uniform fixed law under any positive uniform refresh. At zero refresh, the exact
survivor is the classical finite-group idempotent-probability classification:
every fixed law is uniform on a subgroup. Positive support forms a subgroup;
equality at a maximal coordinate forces uniform weights on that support.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The canonical uniform law on any subgroup, extended by zero to the ambient group. -/
def subgroupUniformLaw (H : Subgroup G) : FiniteProbabilityLaw G := by
  classical
  refine ⟨fun i => if i ∈ H then (Fintype.card H : ℝ)⁻¹ else 0, ?_, ?_⟩
  · intro i
    split_ifs <;> positivity
  · rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← Fintype.card_subtype]
    exact mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero (α := H))

omit [DecidableEq G] in
/-- Every subgroup law has exactly that subgroup as its positive support. -/
theorem subgroupUniformLaw_pos_iff (H : Subgroup G) (i : G) :
    0 < (subgroupUniformLaw H).prob i ↔ i ∈ H := by
  classical
  have hn : (0 : ℝ) < Fintype.card H := by exact_mod_cast Fintype.card_pos (α := H)
  by_cases hi : i ∈ H <;> simp [subgroupUniformLaw, hi, inv_pos.mpr hn]

/-- Uniform convolution within a subgroup reproduces the same law. -/
theorem subgroupUniformLaw_self_convolution (H : Subgroup G) :
    ((subgroupUniformLaw H).mix (relativeGroupNoise (subgroupUniformLaw H))).prob =
      (subgroupUniformLaw H).prob := by
  classical
  funext i
  rw [relativeGroupNoise_prob]
  by_cases hi : i ∈ H
  · have hterm (j : G) :
        (subgroupUniformLaw H).prob (i*j⁻¹)*(subgroupUniformLaw H).prob j =
          (Fintype.card H : ℝ)⁻¹*(subgroupUniformLaw H).prob j := by
      by_cases hj : j ∈ H
      · simp [subgroupUniformLaw, hj, H.mul_mem hi (H.inv_mem hj)]
      · simp [subgroupUniformLaw, hj]
    simp_rw [hterm]
    rw [← Finset.mul_sum, (subgroupUniformLaw H).sum_prob, mul_one]
    simp [subgroupUniformLaw, hi]
  · have hterm (j : G) :
        (subgroupUniformLaw H).prob (i*j⁻¹)*(subgroupUniformLaw H).prob j = 0 := by
      by_cases hj : j ∈ H
      · have hx : i*j⁻¹ ∉ H := by
          intro hx
          apply hi
          simpa using H.mul_mem hx hj
        simp [subgroupUniformLaw, hx]
      · simp [subgroupUniformLaw, hj]
    simp only [hterm, Finset.sum_const_zero]
    simp [subgroupUniformLaw, hi]

/-- A single positive product supplies a lower bound on the self-convolution population. -/
theorem selfConvolution_product_lower (p : FiniteProbabilityLaw G) (a b : G) :
    p.prob a*p.prob b ≤ (p.mix (relativeGroupNoise p)).prob (a*b) := by
  rw [relativeGroupNoise_prob]
  have h := Finset.single_le_sum (fun j _ => mul_nonneg (p.nonneg ((a*b)*j⁻¹)) (p.nonneg j))
    (Finset.mem_univ b)
  simpa using h

omit [Group G] [DecidableEq G] in
/-- A finite probability law has a positive source coordinate. -/
private theorem finiteProbabilityLaw_exists_positive (p : FiniteProbabilityLaw G) :
    ∃ i, 0 < p.prob i := by
  by_contra h
  push Not at h
  have hz : ∑ i, p.prob i = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact le_antisymm (h i) (p.nonneg i)
  rw [p.sum_prob] at hz
  exact one_ne_zero hz

/-- At zero refresh, all stationary probability laws are exactly subgroup-uniform laws. -/
theorem selfConvolution_fixed_iff_subgroupUniform (p : FiniteProbabilityLaw G) :
    (p.mix (relativeGroupNoise p)).prob = p.prob ↔
      ∃ H : Subgroup G, p.prob = (subgroupUniformLaw H).prob := by
  classical
  constructor
  · intro hfix
    have hmul {a b : G} (ha : 0 < p.prob a) (hb : 0 < p.prob b) : 0 < p.prob (a*b) := by
      have h := selfConvolution_product_lower p a b
      rw [hfix] at h
      exact (mul_pos ha hb).trans_le h
    have hpowpos (a : G) (ha : 0 < p.prob a) (n : ℕ) : 0 < p.prob (a^(n+1)) := by
      induction n with
      | zero => simpa using ha
      | succ n ih => simpa only [pow_succ] using hmul ih ha
    have hcard : 1 ≤ Fintype.card G := Nat.succ_le_of_lt Fintype.card_pos
    obtain ⟨a, ha⟩ := finiteProbabilityLaw_exists_positive p
    have hone : 0 < p.prob 1 := by
      have h := hpowpos a ha (Fintype.card G-1)
      rw [Nat.sub_add_cancel hcard] at h
      simpa using h
    have hpow (a : G) (ha : 0 < p.prob a) (n : ℕ) : 0 < p.prob (a^n) := by
      induction n with
      | zero => simpa using hone
      | succ n ih => simpa only [pow_succ] using hmul ih ha
    have hinv {a : G} (ha : 0 < p.prob a) : 0 < p.prob a⁻¹ := by
      have he : a^(Fintype.card G-1)*a = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel hcard]
        simp
      have hei : a^(Fintype.card G-1) = a⁻¹ := (eq_inv_iff_mul_eq_one).mpr he
      rw [← hei]
      exact hpow a ha _
    let H : Subgroup G :=
      { carrier := {a | 0 < p.prob a}
        one_mem' := hone
        mul_mem' := fun ha hb => hmul ha hb
        inv_mem' := fun ha => hinv ha }
    obtain ⟨g, _, hgmax⟩ := Finset.exists_max_image Finset.univ p.prob Finset.univ_nonempty
    have hgpos : 0 < p.prob g := ha.trans_le (hgmax a (Finset.mem_univ a))
    have hgap : (∑ j, (p.prob g-p.prob (g*j⁻¹))*p.prob j) = 0 := by
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, p.sum_prob, mul_one]
      rw [← relativeGroupNoise_prob, hfix, sub_self]
    have heach (j : G) : (p.prob g-p.prob (g*j⁻¹))*p.prob j = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg
        (sub_nonneg.mpr (hgmax _ (Finset.mem_univ _))) (p.nonneg j))).mp hgap j (Finset.mem_univ j)
    have hfull (y : G) (hy : y ∈ H) : p.prob y = p.prob g := by
      have hj : y⁻¹*g ∈ H := H.mul_mem (H.inv_mem hy) hgpos
      have h := (mul_eq_zero.mp (heach (y⁻¹*g))).resolve_right (ne_of_gt hj)
      have he := (sub_eq_zero.mp h).symm
      simpa [mul_assoc] using he
    have hprofile (i : G) : p.prob i = if i ∈ H then p.prob g else 0 := by
      by_cases hi : i ∈ H
      · simpa [hi] using hfull i hi
      · have hnot : ¬ 0 < p.prob i := hi
        simp only [hi, if_false]
        exact le_antisymm (le_of_not_gt hnot) (p.nonneg i)
    have hsum : (∑ i, if i ∈ H then p.prob g else 0) = 1 :=
      (Finset.sum_congr rfl (fun i _ => hprofile i)).symm.trans p.sum_prob
    rw [← Finset.sum_filter] at hsum
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    rw [← Fintype.card_subtype] at hsum
    have hc : (Fintype.card H : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := H)
    have hg : p.prob g = (Fintype.card H : ℝ)⁻¹ := by
      apply mul_left_cancel₀ hc
      rw [mul_inv_cancel₀ hc]
      exact hsum
    refine ⟨H, ?_⟩
    funext i
    rw [hprofile]
    simp only [subgroupUniformLaw, hg]
  · rintro ⟨H, hp⟩
    have h := subgroupUniformLaw_self_convolution H
    simpa only [FiniteProbabilityLaw.mix, relativeGroupNoise, Matrix.mulVec, dotProduct, hp] using h

end GaloisForLFunctions.HTGeometry
