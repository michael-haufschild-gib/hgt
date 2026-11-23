import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Selecting enough cosine factors at a short physical time -/
open Real Filter Set
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
noncomputable section

/-- Selecting about M/t² spins keeps the perturbation bounded while
their cosine factors suppress the reference trace. -/
theorem select_spin_count {κ : ℝ} (hκ : 0 < κ) :
    ∃ L δ : ℝ, 0 < L ∧ 0 < δ ∧ ∀ t : ℝ, 0 < |t| → |t| ≤ 1 →
      ∀ k : ℕ, L ≤ (k:ℝ)*t^2 → ∃ m ≤ k, |cos t|^m+|t|*δ*sqrt (21*m) < κ := by
  let c := 2/π^2
  have hc : 0 < c := by dsimp only [c]; positivity
  obtain ⟨x,hx,hdec⟩ := ((eventually_gt_atTop (0:ℝ)).and
    (tendsto_exp_neg_atTop_nhds_zero.eventually_lt_const (half_pos hκ))).exists
  let L := x/c
  have hL : 0 < L := div_pos hx hc
  let R := sqrt (21*(L+1))
  have hR : 0 < R := sqrt_pos.mpr (by positivity)
  let δ := κ/(4*R)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  refine ⟨L,δ,hL,hδ,?_⟩
  intro t ht hs k hk
  have ht' : 0<t^2 := sq_pos_of_ne_zero (abs_pos.mp ht)
  let m := ⌈L/t^2⌉₊
  have hlow := (div_le_iff₀ ht').mp (Nat.le_ceil (L/t^2))
  have hhigh : (m:ℝ)*t^2 ≤ L+1 := by
    have hm := mul_le_mul_of_nonneg_right (Nat.ceil_lt_add_one (div_nonneg hL.le ht'.le)).le ht'.le
    rw [add_mul,div_mul_cancel₀ _ ht'.ne',one_mul] at hm
    exact hm.trans (add_le_add le_rfl (by simpa only [one_pow,sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) hs 2))
  refine ⟨m,Nat.ceil_le.mpr ((div_le_iff₀ ht').mpr hk),?_⟩
  have hcos : |cos t| ≤ exp (-(c*t^2)) := by
    have hb := abs_le.mp hs
    rw [abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨by linarith only [hb.1,pi_gt_three],
      by linarith only [hb.2,pi_gt_three]⟩)]
    exact (cos_le_one_sub_mul_cos_sq (hs.trans (by linarith only [pi_gt_three]))).trans
      (by simpa only [sub_eq_add_neg,add_comm] using add_one_le_exp (-(c*t^2)))
  have hpow := pow_le_pow_left₀ (abs_nonneg _) hcos m
  rw [←exp_nat_mul] at hpow
  have hbound : |cos t|^m < κ/2 := by
    apply (hpow.trans (exp_le_exp.mpr ?_)).trans_lt hdec
    have he : c*L=x := by dsimp only [L]; field_simp
    nlinarith only [he,mul_le_mul_of_nonneg_left hlow hc.le]
  have herr : |t|*sqrt (21*m) ≤ R := by
    apply (sq_le_sq₀ (by positivity) hR.le).mp
    rw [mul_pow,sq_abs,sq_sqrt (by positivity)]
    change _ ≤ (sqrt (21*(L+1)))^2
    rw [sq_sqrt (by positivity)]
    nlinarith only [hhigh]
  have hδR : δ*R = κ/4 := by dsimp only [δ]; field_simp [hR.ne']
  nlinarith only [hbound,mul_le_mul_of_nonneg_left herr hδ.le,hδR,hκ]

#print axioms select_spin_count
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
