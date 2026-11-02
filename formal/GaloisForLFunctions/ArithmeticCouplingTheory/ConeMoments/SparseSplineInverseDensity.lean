import GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.SparseSplineSchedule

/-!
# Zero exponent of convergence for sparse spline schedules

Matched heights grow supergeometrically. Geometric block sizes therefore
make every positive inverse-power ordinate sum converge.
-/

open Finset Complex Filter Topology
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments

/-- Matched heights have a supergeometric lower bound independently of the number of nodes. -/
lemma PrescribedSplineSchedule.log_height_lower {a b d D : ℝ}
    (s : PrescribedSplineSchedule a b d D) (k : ℕ) :
    (4:ℝ)^(s.start+k)/8 ≤ Real.log (s.height k) := by
  have hn : (0:ℝ) < s.size k := by exact_mod_cast s.size_pos k
  have hn1 : (1:ℝ) ≤ s.size k := by exact_mod_cast Nat.succ_le_iff.mpr (s.size_pos k)
  have hp : (s.height k)^8=(s.size k:ℝ)/correctionMass (s.start+k) := by
    rw [s.height_eq]
    exact matched_spline_height_pow (correctionMass_pos _) (s.size_pos k)
  have hl := congrArg Real.log hp
  rw [Real.log_pow,Real.log_div hn.ne' (correctionMass_pos _).ne',
    correctionMass,Real.log_exp] at hl
  have hnlog := Real.log_nonneg hn1
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl,hnlog]

/-- Every positive multiple of the supergeometric exponent dominates geometric block counts. -/
lemma summable_exp_neg_four_pow_mul_geometric {c R : ℝ}
    (hc : 0 < c) (hR : 0 < R) (s : ℕ) :
    Summable (fun k : ℕ => Real.exp (-c*(4:ℝ)^(s+k))*R^k) := by
  have hfour : Tendsto (fun k : ℕ => (4:ℝ)^k/k) atTop atTop :=
    tendsto_atTop_mono (fun k =>
      div_le_div_of_nonneg_right (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2)
        (by norm_num : (2:ℝ) ≤ 4) k) (Nat.cast_nonneg k))
      GaloisForLFunctions.tendsto_two_pow_div_natCast_atTop
  have hlim := Filter.Tendsto.const_mul_atTop
    (mul_pos hc (pow_pos (by norm_num : (0:ℝ) < 4) s)) hfour
  have hf : Tendsto (fun k : ℕ => (c*(4:ℝ)^(s+k))/k) atTop atTop := by
    apply hlim.congr
    intro k
    rw [pow_add]
    ring
  simpa only [neg_mul] using GaloisForLFunctions.summable_exp_neg_mul_pow hf hR

/-- Geometric block sizes and matched heights give zero exponent of convergence. -/
theorem summable_sparse_spline_inverse_power {a b d D : ℝ}
    (s : PrescribedSplineSchedule a b d D) {U R : ℝ}
    (hR : 0 < R) (hsize : ∀ k : ℕ, (s.size k:ℝ) ≤ U*R^k)
    {γ : (k : ℕ) → Fin (s.size k) → ℝ}
    (hγ : ∀ k j, s.height k ≤ γ k j) {ε : ℝ} (hε : 0 < ε) :
    Summable (fun i : (k : ℕ) × Fin (s.size k) => (1+γ i.1 i.2)^(-ε)) := by
  have hpoint (k : ℕ) (j : Fin (s.size k)) :
      (1+γ k j)^(-ε) ≤ Real.exp (-(ε/8)*(4:ℝ)^(s.start+k)) := by
    have hH : 0 < s.height k := zero_lt_one.trans_le (s.height_one k)
    have hγ1 : 1 ≤ γ k j := (s.height_one k).trans (hγ k j)
    have hlog : (4:ℝ)^(s.start+k)/8 ≤ Real.log (1+γ k j) :=
      (s.log_height_lower k).trans (Real.log_le_log hH (by linarith only [hγ k j]))
    have hbase : 0 < 1+γ k j := by linarith only [hγ1]
    rw [Real.rpow_def_of_pos hbase]
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left hlog hε.le
    nlinarith only [hh]
  have hs := (summable_exp_neg_four_pow_mul_geometric (c := ε/8)
    (div_pos hε (by norm_num)) hR s.start).mul_left U
  rw [summable_sigma_of_nonneg
    (f := fun i : (k : ℕ) × Fin (s.size k) => (1+γ i.1 i.2)^(-ε))
    (fun i => Real.rpow_nonneg (by
      linarith only [(s.height_one i.1).trans (hγ i.1 i.2)]) _)]
  refine ⟨fun _ => Summable.of_finite,?_⟩
  apply Summable.of_nonneg_of_le (fun k => tsum_nonneg fun j => Real.rpow_nonneg (by
    linarith only [(s.height_one k).trans (hγ k j)]) _)
    (fun k => ?_) hs
  rw [tsum_fintype]
  calc
    _ ≤ ∑ _j : Fin (s.size k), Real.exp (-(ε/8)*(4:ℝ)^(s.start+k)) :=
      sum_le_sum fun j _ => hpoint k j
    _ = (s.size k:ℝ)*Real.exp (-(ε/8)*(4:ℝ)^(s.start+k)) := by
      rw [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    _ ≤ (U*R^k)*Real.exp (-(ε/8)*(4:ℝ)^(s.start+k)) :=
      mul_le_mul_of_nonneg_right (hsize k) (Real.exp_pos _).le
    _ = U*(Real.exp (-(ε/8)*(4:ℝ)^(s.start+k))*R^k) := by ring

#print axioms PrescribedSplineSchedule.log_height_lower
#print axioms summable_exp_neg_four_pow_mul_geometric
#print axioms summable_sparse_spline_inverse_power
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments
