import GaloisForLFunctions.RHTower.XiGaussianHeatNormalBlockResolution
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelJacobiSignChanges
import GaloisForLFunctions.HTGeometry.ABHN.HasseMatrixRanks

/-!
# Exact inertia through every singular heat Hankel block

Scalar extension preserves the real kernel dimensions of a normal block.
Interlacing therefore determines both inertia indices throughout the block;
the signs of its two regular endpoint determinants decide the sole possible
odd-dimensional remainder. No intermediate pivot is inverted.
-/

open Matrix HTGeometry
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

theorem hermNullIndex_heatMomentSection_eq (a : ℝ) (N : ℕ) :
    hermNullIndex (heatMomentSection a N) =
      Module.finrank ℝ (LinearMap.ker (momentHankelMatrix (heatRealMoments a) N).mulVecLin) := by
  have hr := ABHN.matrix_rank_eq_rank_map (L := ℂ)
    (momentHankelMatrix (heatRealMoments a) N)
  have hR := LinearMap.finrank_range_add_finrank_ker
    (momentHankelMatrix (heatRealMoments a) N).mulVecLin
  have hC := LinearMap.finrank_range_add_finrank_ker (heatMomentSection a N).mulVecLin
  change Matrix.rank (momentHankelMatrix (heatRealMoments a) N) =
    Matrix.rank (heatMomentSection a N) at hr
  change Matrix.rank (momentHankelMatrix (heatRealMoments a) N) + _ = _ at hR
  change Matrix.rank (heatMomentSection a N) + _ = _ at hC
  simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hR hC
  unfold hermNullIndex
  omega

theorem hermPosIndex_heatMomentSection_le_succ {a : ℝ} (ha : 0 < a) (N : ℕ) :
    hermPosIndex (heatMomentSection a N) ≤ hermPosIndex (heatMomentSection a (N + 1)) := by
  obtain ⟨W, hW, hpos⟩ := exists_isPosDefOn_finrank_eq_posIndex (heatMomentSection a N)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h := Submodule.finrank_le W
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  rw [← hW, ← LinearMap.finrank_range_of_inj
    (f := (heatCoeffExt N).comp W.subtype)
    ((heatCoeffExt_injective N).comp Subtype.val_injective)]
  refine finrank_le_posIndex fun y hy hy0 => ?_
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
  have hx0 : (x : Fin N → ℂ) ≠ 0 := by
    intro h
    apply hy0
    simp [h]
  simpa only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    hermQuad_heatMomentSection_heatCoeffExt ha hN] using hpos x x.property hx0

theorem hermPosIndex_heatMomentSection_succ_le {a : ℝ} (ha : 0 < a) (N : ℕ) :
    hermPosIndex (heatMomentSection a (N + 1)) ≤ hermPosIndex (heatMomentSection a N) + 1 := by
  obtain ⟨W, hW, hpos⟩ := exists_isPosDefOn_finrank_eq_posIndex (heatMomentSection a (N + 1))
  rw [← hW]
  let f : W →ₗ[ℂ] ℂ := (LinearMap.proj (Fin.last N)).comp W.subtype
  have hrank := LinearMap.finrank_range_add_finrank_ker f
  have hr1 : Module.finrank ℂ (LinearMap.range f) ≤ 1 := by
    simpa only [Module.finrank_self] using Submodule.finrank_le (LinearMap.range f)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have h := Submodule.finrank_le W
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  let Φ : LinearMap.ker f →ₗ[ℂ] (Fin N → ℂ) :=
    (LinearMap.funLeft ℂ ℂ Fin.castSucc).comp (W.subtype.comp (LinearMap.ker f).subtype)
  have hlast (y : LinearMap.ker f) : ((y : W) : Fin (N + 1) → ℂ) (Fin.last N) = 0 :=
    LinearMap.mem_ker.mp y.property
  have hΦext (y : LinearMap.ker f) : heatCoeffExt N (Φ y) =
      ((y : W) : Fin (N + 1) → ℂ) := heatCoeffExt_truncate (hlast y)
  have hinj : Function.Injective Φ := by
    intro y z h
    have hh := congrArg (heatCoeffExt N) h
    rw [hΦext, hΦext] at hh
    exact Subtype.ext (Subtype.ext hh)
  have hpositive : IsPosDefOn (heatMomentSection a N) (LinearMap.range Φ) := by
    intro z hz hz0
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hz
    have hy0 : ((y : W) : Fin (N + 1) → ℂ) ≠ 0 := by
      intro h
      apply hz0
      rw [← hΦext y] at h
      exact (heatCoeffExt_injective N) (h.trans (map_zero _).symm)
    rw [← hermQuad_heatMomentSection_heatCoeffExt ha hN, hΦext]
    exact hpos (y : W) (y : W).property hy0
  have hle := finrank_le_posIndex hpositive
  rw [LinearMap.finrank_range_of_inj hinj] at hle
  omega

private theorem stepwise_le_add {f : ℕ → ℕ} (hf : ∀ n, f (n + 1) ≤ f n + 1)
    {i j : ℕ} (hij : i ≤ j) : f j ≤ f i + (j - i) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  simp only [Nat.add_sub_cancel_left]
  induction k with
  | zero => simp
  | succ k ih =>
    simpa only [Nat.add_assoc] using (hf (i + k)).trans (Nat.add_le_add_right ih 1)

private theorem heat_inertia_sum (a : ℝ) (N : ℕ) :
    hermPosIndex (heatMomentSection a N) + hermNegIndex (heatMomentSection a N) +
      hermNullIndex (heatMomentSection a N) = N := by
  simpa using posIndex_add_negIndex_add_nullIndex (isHermitian_heatMomentSection a N)

/-- Below the midpoint the new directions are entirely radical. Above it,
each remaining extension resolves one positive and one negative direction. -/
theorem heat_normal_block_inertia_halves {a : ℝ} (ha : 0 < a) {n d : ℕ}
    (h : MomentNormalBlock (heatRealMoments a) n d) {k : ℕ} (hk : k ≤ d) :
    (2 * k ≤ d →
      hermPosIndex (heatMomentSection a (n + k)) = hermPosIndex (heatMomentSection a n) ∧
      hermNegIndex (heatMomentSection a (n + k)) = hermNegIndex (heatMomentSection a n)) ∧
    (d ≤ 2 * k →
      hermPosIndex (heatMomentSection a (n + d)) =
        hermPosIndex (heatMomentSection a (n + k)) + (d - k) ∧
      hermNegIndex (heatMomentSection a (n + d)) =
        hermNegIndex (heatMomentSection a (n + k)) + (d - k)) := by
  have hnul (i : ℕ) (hi : i ≤ d) :
      hermNullIndex (heatMomentSection a (n + i)) = min i (d - i) := by
    rw [hermNullIndex_heatMomentSection_eq, h.nullity hi]
  have hs0 := heat_inertia_sum a n
  have hsk := heat_inertia_sum a (n + k)
  have hsd := heat_inertia_sum a (n + d)
  have hz := hnul 0 (Nat.zero_le d)
  simp only [Nat.add_zero, Nat.zero_min] at hz
  rw [hz] at hs0
  rw [hnul k hk] at hsk
  rw [hnul d le_rfl] at hsd
  simp only [Nat.sub_self, Nat.min_zero, Nat.add_zero] at hsd
  constructor
  · intro hm
    have hp := monotone_nat_of_le_succ (hermPosIndex_heatMomentSection_le_succ ha)
      (show n ≤ n + k by omega)
    have hn := monotone_nat_of_le_succ (hermNegIndex_heatMomentSection_le_succ ha)
      (show n ≤ n + k by omega)
    rw [min_eq_left (by omega : k ≤ d - k)] at hsk
    omega
  · intro hm
    have hp := stepwise_le_add (f := fun N => hermPosIndex (heatMomentSection a N))
      (hermPosIndex_heatMomentSection_succ_le ha)
      (show n + k ≤ n + d by omega)
    have hn := stepwise_le_add (f := fun N => hermNegIndex (heatMomentSection a N))
      (hermNegIndex_heatMomentSection_succ_le ha)
      (show n + k ≤ n + d by omega)
    rw [min_eq_right (by omega : d - k ≤ k)] at hsk
    omega

/-- Source-only charge of one regular-to-regular block. The correction by
`(-1)^(d/2)` retains the hyperbolic pairs hidden by zero scalar pivots. -/
def heatNormalBlockCharge (a : ℝ) (n d : ℕ) : ℕ :=
  d / 2 + if (-1 : ℝ) ^ (d / 2) *
    (momentHankelMatrix (heatRealMoments a) n).det *
    (momentHankelMatrix (heatRealMoments a) (n + d)).det < 0 then 1 else 0

/-- The complete negative inertia contribution of a normal block is read
from its length and its two nonzero endpoint determinants. -/
theorem heat_normal_block_charge {a : ℝ} (ha : 0 < a) {n d : ℕ}
    (h : MomentNormalBlock (heatRealMoments a) n d) :
    hermNegIndex (heatMomentSection a (n + d)) =
      hermNegIndex (heatMomentSection a n) + heatNormalBlockCharge a n d := by
  have hm := (heat_normal_block_inertia_halves ha h (k := d / 2) (by omega)).1 (by omega)
  have hstep := stepwise_le_add (f := fun N => hermNegIndex (heatMomentSection a N))
    (hermNegIndex_heatMomentSection_succ_le ha)
    (show n + d / 2 ≤ n + d by omega)
  have hpstep := stepwise_le_add (f := fun N => hermPosIndex (heatMomentSection a N))
    (hermPosIndex_heatMomentSection_succ_le ha)
    (show n + d / 2 ≤ n + d by omega)
  have hs0 := heat_inertia_sum a n
  have hsd := heat_inertia_sum a (n + d)
  have hn0 := h.nullity (k := 0) (Nat.zero_le d)
  have hnd := h.nullity (k := d) le_rfl
  simp only [Nat.add_zero, Nat.zero_min] at hn0
  simp only [Nat.sub_self, Nat.min_zero] at hnd
  rw [hermNullIndex_heatMomentSection_eq, hn0] at hs0
  rw [hermNullIndex_heatMomentSection_eq, hnd] at hsd
  rw [hm.1] at hpstep
  rw [hm.2] at hstep
  have he : hermNegIndex (heatMomentSection a (n + d)) =
      hermNegIndex (heatMomentSection a n) + d / 2 ∨
      hermNegIndex (heatMomentSection a (n + d)) =
      hermNegIndex (heatMomentSection a n) + d / 2 + 1 := by omega
  have s0 := neg_one_pow_negIndex_mul_heatMomentDet_pos
    (show (leadingMatrix (heatMomentArray a) n).det ≠ 0 from h.head_regular)
  have sd := neg_one_pow_negIndex_mul_heatMomentDet_pos
    (show (leadingMatrix (heatMomentArray a) (n + d)).det ≠ 0 from h.next_regular)
  have hsq : ((-1 : ℝ) ^ hermNegIndex (heatMomentSection a n)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    simp
  have hprod (t D E : ℝ) :
      ((-1 : ℝ) ^ hermNegIndex (heatMomentSection a n) * D) *
      ((-1 : ℝ) ^ hermNegIndex (heatMomentSection a n) * t * E) = t * D * E := by
    calc
      _ = ((-1 : ℝ) ^ hermNegIndex (heatMomentSection a n)) ^ 2 * (t * D * E) := by ring
      _ = _ := by rw [hsq, one_mul]
  have hs := mul_pos s0 sd
  rcases he with he | he
  · rw [he, pow_add] at hs
    have hsign : 0 < (-1 : ℝ) ^ (d / 2) *
        (momentHankelMatrix (heatRealMoments a) n).det *
        (momentHankelMatrix (heatRealMoments a) (n + d)).det := by
      change 0 < (-1 : ℝ) ^ (d / 2) *
        (leadingMatrix (heatMomentArray a) n).det *
        (leadingMatrix (heatMomentArray a) (n + d)).det
      rwa [hprod] at hs
    simp only [heatNormalBlockCharge, if_neg (not_lt.mpr hsign.le), Nat.add_zero]
    exact he
  · rw [he, pow_succ, pow_add] at hs
    have hsign : (-1 : ℝ) ^ (d / 2) *
        (momentHankelMatrix (heatRealMoments a) n).det *
        (momentHankelMatrix (heatRealMoments a) (n + d)).det < 0 := by
      change (-1 : ℝ) ^ (d / 2) *
        (leadingMatrix (heatMomentArray a) n).det *
        (leadingMatrix (heatMomentArray a) (n + d)).det < 0
      have heq :
          ((-1 : ℝ) ^ hermNegIndex (heatMomentSection a n) *
            (leadingMatrix (heatMomentArray a) n).det) *
          ((-1 : ℝ) ^ hermNegIndex (heatMomentSection a n) * (-1 : ℝ) ^ (d / 2) * -1 *
            (leadingMatrix (heatMomentArray a) (n + d)).det) =
          -((-1 : ℝ) ^ (d / 2) * (leadingMatrix (heatMomentArray a) n).det *
            (leadingMatrix (heatMomentArray a) (n + d)).det) := by
        calc
          _ = -(((-1 : ℝ) ^ hermNegIndex (heatMomentSection a n) *
              (leadingMatrix (heatMomentArray a) n).det) *
            ((-1 : ℝ) ^ hermNegIndex (heatMomentSection a n) * (-1 : ℝ) ^ (d / 2) *
              (leadingMatrix (heatMomentArray a) (n + d)).det)) := by ring
          _ = _ := by rw [hprod]
      rw [heq] at hs
      exact neg_pos.mp hs
    simp only [heatNormalBlockCharge, if_pos hsign]
    omega

/-- Full signature inside a normal block. Natural subtraction records the
initial radical plateau and its subsequent resolution into signed directions. -/
theorem heat_normal_block_inertia {a : ℝ} (ha : 0 < a) {n d : ℕ}
    (h : MomentNormalBlock (heatRealMoments a) n d) {k : ℕ} (hk : k ≤ d) :
    hermPosIndex (heatMomentSection a (n + k)) =
      hermPosIndex (heatMomentSection a n) + (k - heatNormalBlockCharge a n d) ∧
    hermNegIndex (heatMomentSection a (n + k)) =
      hermNegIndex (heatMomentSection a n) + (k + heatNormalBlockCharge a n d - d) ∧
    hermNullIndex (heatMomentSection a (n + k)) = min k (d - k) := by
  have hc := heat_normal_block_charge ha h
  have hm := heat_normal_block_inertia_halves ha h (k := d / 2) (by omega)
  have hqlo : d / 2 ≤ heatNormalBlockCharge a n d := by
    unfold heatNormalBlockCharge
    split_ifs <;> omega
  have hqhi : heatNormalBlockCharge a n d ≤ d - d / 2 := by
    by_cases he : 2 * (d / 2) = d
    · have hm0 := (hm.1 (by omega)).2
      have hm1 := (hm.2 (by omega)).2
      omega
    · unfold heatNormalBlockCharge
      split_ifs <;> omega
  have hs0 := heat_inertia_sum a n
  have hsd := heat_inertia_sum a (n + d)
  have hn0 := h.nullity (k := 0) (Nat.zero_le d)
  have hnd := h.nullity (k := d) le_rfl
  simp only [Nat.add_zero, Nat.zero_min] at hn0
  simp only [Nat.sub_self, Nat.min_zero] at hnd
  rw [hermNullIndex_heatMomentSection_eq, hn0] at hs0
  rw [hermNullIndex_heatMomentSection_eq, hnd] at hsd
  have hnul : hermNullIndex (heatMomentSection a (n + k)) = min k (d - k) := by
    rw [hermNullIndex_heatMomentSection_eq, h.nullity hk]
  have hh := heat_normal_block_inertia_halves ha h hk
  by_cases he : 2 * k ≤ d
  · have hp := hh.1 he
    refine ⟨?_, ?_, hnul⟩ <;> omega
  · have hp := hh.2 (by omega)
    refine ⟨?_, ?_, hnul⟩ <;> omega

end
end RHTower
