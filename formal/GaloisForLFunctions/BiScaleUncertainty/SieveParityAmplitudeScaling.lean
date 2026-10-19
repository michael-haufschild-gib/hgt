import GaloisForLFunctions.BiScaleUncertainty.SieveParityNeighborhoodStability
import GaloisForLFunctions.TransHorizonIncidenceMechanics.RadicalCheckpointSignRigidityAndGaugeLaw

/-! Exact amplitude transport of the actual local recovery exponent. -/

open scoped BigOperators
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.TransHorizonIncidenceMechanics (sieveSeq_scale_weight)
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
set_option autoImplicit false

theorem translatedMoment_scale (N : ℕ) (c : ℕ → ℝ) (scl : ℝ) {m : ℕ} (v : Fin m → ℕ) :
    translatedMoment N (fun d => scl*c d) v = scl^m*translatedMoment N c v := by
  simp only [translatedMoment, sieveSeq_scale_weight, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum]
  ring

/-- The local exponent is unchanged by any nonzero physical amplitude rescaling. -/
theorem local_holder_scale (N : ℕ) (b : ℕ → ℝ) (α scl : ℝ) (hscl : scl ≠ 0)
    (h : LocalPairwiseHolder N b α) : LocalPairwiseHolder N (fun d => scl*b d) α := by
  obtain ⟨R, hR, C, hC, hlocal⟩ := h
  let s : ℝ := scl⁻¹
  let K : ℝ := |s|^5+|s|^6
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hsclabs : 0 < |scl| := abs_pos.mpr hscl
  have hinv : |s| * |scl| = 1 := by rw [← abs_mul]; simp [s, hscl]
  have hback : scl*s = 1 := by simp [s, hscl]
  refine ⟨|scl| * R, mul_pos hsclabs hR, |scl| * C*K^α, by positivity, ?_⟩
  intro c e ε hε hc he h5 h6
  let c' : ℕ → ℝ := fun d => s*c d
  let e' : ℕ → ℝ := fun d => s*e d
  have hball (f : ℕ → ℝ)
      (hf : ∀ n, |sieveSeq N f n-sieveSeq N (fun d => scl*b d) n| ≤ |scl| * R) :
      ∀ n, |sieveSeq N (fun d => s*f d) n-sieveSeq N b n| ≤ R := by
    intro n
    have hh := mul_le_mul_of_nonneg_left (hf n) (abs_nonneg s)
    have heq : sieveSeq N (fun d => s*f d) n-sieveSeq N b n =
        s*(sieveSeq N f n-sieveSeq N (fun d => scl*b d) n) := by
      simp only [sieveSeq_scale_weight]
      dsimp [s]
      field_simp [hscl]
    rw [heq, abs_mul]
    simpa only [← mul_assoc, hinv, one_mul] using hh
  have hraw (m : ℕ) (hm : m = 5 ∨ m = 6)
      (hv : ∀ v : Fin m → ℕ, |translatedMoment N c v-translatedMoment N e v| ≤ ε)
      (v : Fin m → ℕ) :
      |translatedMoment N c' v-translatedMoment N e' v| ≤ K*ε := by
    change |translatedMoment N (fun d => s*c d) v-
      translatedMoment N (fun d => s*e d) v| ≤ K*ε
    rw [translatedMoment_scale, translatedMoment_scale, ← mul_sub, abs_mul, abs_pow]
    have hp : |s|^m ≤ K := by
      rcases hm with rfl | rfl <;> dsimp [K] <;>
        nlinarith only [pow_nonneg (abs_nonneg s) 5, pow_nonneg (abs_nonneg s) 6]
    exact mul_le_mul hp (hv v) (abs_nonneg _) hK
  obtain ⟨h, hh⟩ := hlocal c' e' (K*ε) (mul_nonneg hK hε)
    (hball c hc) (hball e he)
    (hraw 5 (Or.inl rfl) h5) (hraw 6 (Or.inr rfl) h6)
  refine ⟨h, fun n => ?_⟩
  have hb := mul_le_mul_of_nonneg_left (hh n) hsclabs.le
  have heq : sieveSeq N e n-sieveSeq N c (n+h) =
      scl*(sieveSeq N e' n-sieveSeq N c' (n+h)) := by
    dsimp [c', e']
    simp only [sieveSeq_scale_weight]
    calc
      _ = (scl*s)*(sieveSeq N e n-sieveSeq N c (n+h)) := by rw [hback, one_mul]
      _ = _ := by ring
  rw [heq, abs_mul]
  rw [Real.mul_rpow hK hε] at hb
  nlinarith only [hb]

theorem local_holder_scale_iff (N : ℕ) (b : ℕ → ℝ) (α scl : ℝ) (hscl : scl ≠ 0) :
    LocalPairwiseHolder N (fun d => scl*b d) α ↔ LocalPairwiseHolder N b α := by
  constructor
  · intro h
    have hh := local_holder_scale N (fun d => scl*b d) α scl⁻¹ (inv_ne_zero hscl) h
    simpa only [← mul_assoc, inv_mul_cancel₀ hscl, one_mul] using hh
  · exact local_holder_scale N b α scl hscl

/-- Actual sieve weights for a parity source of prescribed amplitude. -/
def paritySource (N : ℕ) (a : ℝ) : ℕ → ℝ := fun d => (a/2)*parityWeights N d

theorem coordinate_paritySource (N : ℕ) (hN : 2 ≤ N) (a : ℝ) (q : ℕ) :
    selbergMultiplesCoord N (paritySource N a) q = if q = 2 then a else 0 := by
  have hs : selbergMultiplesCoord N (paritySource N a) q =
      (a/2)*selbergMultiplesCoord N (parityWeights N) q := by
    simp [selbergMultiplesCoord, paritySource, Finset.mul_sum, mul_div_assoc]
  rw [hs, coordinate_parityWeights N hN]
  split_ifs <;> ring

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
