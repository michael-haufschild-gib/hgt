import GaloisForLFunctions.RHTower.PaperWoldNearEnvelope
import GaloisForLFunctions.HTGeometry.HilbertSchmidtMatrix

/-! # The full directed Wold kernel below the half power

The actual prime increments admit a square-summable product majorant. No window
restriction, sign assumption, or arithmetic cancellation hypothesis is needed.
-/

namespace RHTower
noncomputable section
open Filter Topology

structure PaperWoldStrictHalf where
  t : ℝ
  nonneg : 0 ≤ t
  lt_half : t < 1 / 2

def PaperWoldStrictHalf.nearParameters (p : PaperWoldStrictHalf) : PaperWoldNearParameters where
  t := p.t
  eta := 1
  t_nonneg := p.nonneg
  eta_nonneg := zero_le_one
  budget := by linarith [p.lt_half]

def paperWoldFullEnvelope (p : PaperWoldStrictHalf) (n : ℕ) : ℝ :=
  paperWoldEnvelopeConstant p.nearParameters *
    ((n : ℝ) + 1) ^ (p.t + paperWoldSlack p.nearParameters - 1)

theorem paperWoldFullEnvelope_nonneg (p : PaperWoldStrictHalf) (n : ℕ) :
    0 ≤ paperWoldFullEnvelope p n := by
  unfold paperWoldFullEnvelope
  positivity [paperWoldEnvelopeConstant_pos p.nearParameters]

theorem paperWoldFullEnvelope_sq (p : PaperWoldStrictHalf) (n : ℕ) :
    paperWoldFullEnvelope p n ^ 2 = paperWoldEnvelopeConstant p.nearParameters ^ 2 *
      ((n : ℝ) + 1) ^ ((p.t + paperWoldSlack p.nearParameters - 1) * 2) := by
  rw [paperWoldFullEnvelope, mul_pow, Real.rpow_mul (by positivity), Real.rpow_two]

theorem paperWoldFullEnvelope_sq_summable (p : PaperWoldStrictHalf) :
    Summable (fun n => paperWoldFullEnvelope p n ^ 2) := by
  have he : (p.t + paperWoldSlack p.nearParameters - 1) * 2 < -1 := by
    dsimp [paperWoldSlack, PaperWoldStrictHalf.nearParameters]
    linarith [p.lt_half]
  have h := ((Real.summable_nat_rpow).mpr he).comp_injective Nat.succ_injective
  simpa only [paperWoldFullEnvelope_sq, Function.comp_def, Nat.cast_succ] using
    h.mul_left (paperWoldEnvelopeConstant p.nearParameters ^ 2)

theorem paperWoldInteraction_product_bound (p : PaperWoldStrictHalf) {n j : ℕ} (hnj : n ≤ j) :
    |paperWoldInteraction p.nearParameters n j| ≤
      paperWoldFullEnvelope p n * paperWoldFullEnvelope p j := by
  have hx : 0 < (n : ℝ) + 1 := by positivity
  have hy : 0 < (j : ℝ) + 1 := by positivity
  have hw : ((n : ℝ) + 1) ^ (2 * p.t) ≤
      ((n : ℝ) + 1) ^ p.t * ((j : ℝ) + 1) ^ p.t := by
    rw [show 2 * p.t = p.t + p.t by ring, Real.rpow_add hx]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hx.le (by exact_mod_cast Nat.add_le_add_right hnj 1) p.nonneg)
      (Real.rpow_nonneg hx.le _)
  have hi := mul_le_mul (paperWold_increment_power_bound p.nearParameters n)
    (paperWold_increment_power_bound p.nearParameters j) (abs_nonneg _)
    (by positivity [paperWoldEnvelopeConstant_pos p.nearParameters])
  have h := mul_le_mul hw hi (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (mul_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hy.le _))
  calc
    |paperWoldInteraction p.nearParameters n j| = ((n : ℝ) + 1) ^ (2 * p.t) *
        (|xiHeatCassiniWoldNatIncrement n| * |xiHeatCassiniWoldNatIncrement j|) := by
      simp only [paperWoldInteraction, PaperWoldStrictHalf.nearParameters, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg hx.le _)]
      ring
    _ ≤ _ := h
    _ = _ := by
      unfold paperWoldFullEnvelope
      rw [show ((n : ℝ) + 1) ^ (p.t + paperWoldSlack p.nearParameters - 1) =
          ((n : ℝ) + 1) ^ p.t * ((n : ℝ) + 1) ^ (paperWoldSlack p.nearParameters - 1) by
            rw [← Real.rpow_add hx]; congr 1; ring,
        show ((j : ℝ) + 1) ^ (p.t + paperWoldSlack p.nearParameters - 1) =
          ((j : ℝ) + 1) ^ p.t * ((j : ℝ) + 1) ^ (paperWoldSlack p.nearParameters - 1) by
            rw [← Real.rpow_add hy]; congr 1; ring]
      ring

def paperWoldFullKernel (p : PaperWoldStrictHalf) (q : ℕ × ℕ) : ℂ :=
  if q.1 < q.2 then (paperWoldInteraction p.nearParameters q.1 q.2 : ℂ) else 0

theorem paperWoldFullKernel_bound (p : PaperWoldStrictHalf) (q : ℕ × ℕ) :
    ‖paperWoldFullKernel p q‖ ≤ paperWoldFullEnvelope p q.1 * paperWoldFullEnvelope p q.2 := by
  unfold paperWoldFullKernel
  split_ifs with h
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using paperWoldInteraction_product_bound p h.le
  · simpa only [norm_zero] using mul_nonneg (paperWoldFullEnvelope_nonneg p q.1)
      (paperWoldFullEnvelope_nonneg p q.2)

theorem paperWoldFullKernel_isHS (p : PaperWoldStrictHalf) :
    HilbertSchmidt.IsHS (paperWoldFullKernel p) := by
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_)
    ((paperWoldFullEnvelope_sq_summable p).mul_of_nonneg (paperWoldFullEnvelope_sq_summable p)
      (fun n => sq_nonneg _) (fun n => sq_nonneg _))
  have h := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (paperWoldFullEnvelope_nonneg p q.1)
    (paperWoldFullEnvelope_nonneg p q.2))).mpr (paperWoldFullKernel_bound p q)
  simpa only [mul_pow] using h

/-- Bounded entrywise selection, including arbitrary windows and complex phases. -/
abbrev PaperWoldMask := ℕ × ℕ → {z : ℂ // ‖z‖ ≤ 1}

def paperWoldFullMask : PaperWoldMask := fun _ => ⟨1, by simp⟩

def paperWoldWindowMask (w : ℕ → ℕ) : PaperWoldMask :=
  fun q => ⟨if q.2 ≤ q.1 + w q.1 then 1 else 0, by split_ifs <;> simp⟩

def paperWoldMaskedKernel (p : PaperWoldStrictHalf) (m : PaperWoldMask) (q : ℕ × ℕ) : ℂ :=
  (m q : ℂ) * paperWoldFullKernel p q

@[simp] theorem paperWoldMaskedKernel_full (p : PaperWoldStrictHalf) :
    paperWoldMaskedKernel p paperWoldFullMask = paperWoldFullKernel p := by
  funext q
  simp [paperWoldMaskedKernel, paperWoldFullMask]

theorem paperWoldMaskedKernel_norm_le (p : PaperWoldStrictHalf) (m : PaperWoldMask) (q : ℕ × ℕ) :
    ‖paperWoldMaskedKernel p m q‖ ≤ ‖paperWoldFullKernel p q‖ := by
  rw [paperWoldMaskedKernel, norm_mul]
  exact (mul_le_mul_of_nonneg_right (m q).property (norm_nonneg _)).trans_eq (one_mul _)

theorem paperWoldMaskedKernel_isHS (p : PaperWoldStrictHalf) (m : PaperWoldMask) :
    HilbertSchmidt.IsHS (paperWoldMaskedKernel p m) :=
  Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun q => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (paperWoldMaskedKernel_norm_le p m q))
    (paperWoldFullKernel_isHS p)

theorem paperWoldMaskedKernel_hsNormSq_le (p : PaperWoldStrictHalf) (m : PaperWoldMask) :
    HilbertSchmidt.hsNormSq (paperWoldMaskedKernel p m) ≤ HilbertSchmidt.hsNormSq (paperWoldFullKernel p) :=
  Summable.tsum_le_tsum
    (fun q => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (paperWoldMaskedKernel_norm_le p m q))
    (paperWoldMaskedKernel_isHS p m) (paperWoldFullKernel_isHS p)

theorem paperWoldMaskedKernel_lower (p : PaperWoldStrictHalf) (m : PaperWoldMask)
    {n j : ℕ} (h : j ≤ n) : paperWoldMaskedKernel p m (n,j) = 0 := by
  simp [paperWoldMaskedKernel, paperWoldFullKernel, not_lt_of_ge h]

end
end RHTower
