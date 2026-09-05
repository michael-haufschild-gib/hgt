import GaloisForLFunctions.HTGeometry.ChronologicalTensor.SegmentExtrapolation
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.SealingExamples

/-!
# A universal enclosure bound depending only on degree

Jordan decomposition converts a signed probe into an extrapolated segment of
monotone unit probes. For degree d >= 2, d*(d-1) enclosures suffice for exact
monotone capacity, independently of coefficients and the number of gaps.
Enclosure capacity decreases with depth, so equality persists thereafter.
The six-endpoint reversal example therefore stabilizes by depth six.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Finset

def upwardProbe {n : ℕ} (g : Fin n → ℝ) : Fin n → ℝ := fun i => |g i|+g i

def downwardProbe {n : ℕ} (g : Fin n → ℝ) : Fin n → ℝ := fun i => |g i|-g i

theorem upwardProbe_variation {n : ℕ} (g : Fin n → ℝ) :
    variation (upwardProbe g) = variation g+displacement g := by
  have hp (i : Fin n) : 0 ≤ upwardProbe g i := by
    dsimp [upwardProbe]; linarith [neg_abs_le (g i)]
  simp only [variation]
  simp_rw [abs_of_nonneg (hp _)]
  simp only [upwardProbe,displacement,sum_add_distrib]

theorem downwardProbe_variation {n : ℕ} (g : Fin n → ℝ) :
    variation (downwardProbe g) = variation g-displacement g := by
  have hp (i : Fin n) : 0 ≤ downwardProbe g i := by
    exact sub_nonneg.mpr (le_abs_self _)
  simp only [variation]
  simp_rw [abs_of_nonneg (hp _)]
  simp only [downwardProbe,displacement,sum_sub_distrib]

theorem jordan_segment_identity {n : ℕ} (g : Fin (n+1) → ℝ) (t : ℝ) (i : Fin (n+1)) :
    displacement g * segmentProbe (upwardProbe g) (downwardProbe g) t i = g i+
      (displacement g*t-variation g)/2*
        (radialProbe (upwardProbe g) i-radialProbe (downwardProbe g) i) := by
  have hu := congrFun (radialProbe_data (upwardProbe g)).2.2 i
  have hd := congrFun (radialProbe_data (downwardProbe g)).2.2 i
  have hp : 0 ≤ upwardProbe g i := by dsimp [upwardProbe]; linarith [neg_abs_le (g i)]
  have hn : 0 ≤ downwardProbe g i := sub_nonneg.mpr (le_abs_self _)
  rw [abs_of_nonneg hp,upwardProbe_variation] at hu
  rw [abs_of_nonneg hn,downwardProbe_variation] at hd
  dsimp [upwardProbe] at hu
  dsimp [downwardProbe] at hd
  unfold segmentProbe
  nlinarith


theorem quadratic_sealing_probe_bound {n r m : ℕ}
    (D : Fin m → Fin (r+2) → Finset (Fin (n+1))) (c : Fin m → ℝ) (g : Fin (n+1) → ℝ) :
    |displacement (normalizeProbe g)^((r+2)*(r+1))*familyValue D c (normalizeProbe g)| ≤
      monotoneCapacity D c := by
  have hpos (g : Fin (n+1) → ℝ) (hsg : 0 ≤ displacement (normalizeProbe g)) :
      |displacement (normalizeProbe g)^((r+2)*(r+1))*familyValue D c (normalizeProbe g)| ≤
        monotoneCapacity D c := by
    let z := normalizeProbe g
    let S := displacement z
    let V := variation z
    have hv : V ≤ 1 := normalizeProbe_budget g
    have hv0 : 0 ≤ V := variation_nonneg z
    have hsv : S ≤ V := (le_abs_self S).trans (abs_sum_le_sum_abs _ _)
    change |S^((r+2)*(r+1))*familyValue D c z| ≤ monotoneCapacity D c
    by_cases hs0 : S = 0
    · rw [hs0,zero_pow (ne_of_gt (show 0 < (r+2)*(r+1) by positivity)),zero_mul,abs_zero]
      exact monotoneCapacity_nonneg D c
    · have hs : 0 < S := lt_of_le_of_ne hsg (Ne.symm hs0)
      have hratio : 0 ≤ V/S-1 := by
        have hh : (1 : ℝ) ≤ V/S := (le_div_iff₀ hs).mpr (by simpa using hsv)
        linarith
      have ht : 1+|V/S-1| = V/S := by rw [abs_of_nonneg hratio]; ring
      have hb := segment_extrapolation D c (upwardProbe z) (downwardProbe z) (V/S-1)
      rw [ht] at hb
      have hz : z = fun i => S*segmentProbe (upwardProbe z) (downwardProbe z) (V/S) i := by
        funext i
        have hh := jordan_segment_identity z (V/S) i
        have he : S*(V/S)-V = 0 := by field_simp; ring
        change S*segmentProbe (upwardProbe z) (downwardProbe z) (V/S) i =
          z i+(S*(V/S)-V)/2*(radialProbe (upwardProbe z) i-radialProbe (downwardProbe z) i) at hh
        rw [he,zero_div,zero_mul,add_zero] at hh
        exact hh.symm
      have heval := congrArg (familyValue D c) hz
      rw [familyValue_scale] at heval
      have hdegree : (r+2)*(r+1)+(r+2) = (r+2)*(r+2) := by ring
      have hpower := pow_le_pow_left₀ hv0 hv ((r+2)*(r+2))
      rw [one_pow] at hpower
      calc
        _ = S^((r+2)*(r+2))*|familyValue D c
            (segmentProbe (upwardProbe z) (downwardProbe z) (V/S))| := by
          rw [heval,abs_mul,abs_mul,abs_pow,abs_pow,abs_of_pos hs,← mul_assoc,← pow_add,hdegree]
        _ ≤ S^((r+2)*(r+2))*(monotoneCapacity D c*(V/S)^((r+2)*(r+2))) :=
          mul_le_mul_of_nonneg_left hb (pow_nonneg hs.le _)
        _ = monotoneCapacity D c*V^((r+2)*(r+2)) := by
          rw [div_pow]
          field_simp
        _ ≤ monotoneCapacity D c*1 := mul_le_mul_of_nonneg_left hpower (monotoneCapacity_nonneg D c)
        _ = monotoneCapacity D c := mul_one _
  by_cases hs : 0 ≤ displacement (normalizeProbe g)
  · exact hpos g hs
  · have hn : 0 ≤ displacement (normalizeProbe (-g)) := by
      simp only [normalizeProbe_neg,displacement,Pi.neg_apply,sum_neg_distrib]
      change 0 ≤ -displacement (normalizeProbe g)
      linarith
    have hb := hpos (-g) hn
    simpa only [normalizeProbe_neg,displacement,Pi.neg_apply,sum_neg_distrib,
      abs_mul,abs_pow,abs_neg,familyValue_neg_abs] using hb

theorem quadratic_sealing_capacity {n r m : ℕ}
    (D : Fin m → Fin (r+2) → Finset (Fin (n+1))) (c : Fin m → ℝ) :
    sealedCapacity D c ((r+2)*(r+1)) = monotoneCapacity D c := by
  apply le_antisymm _ (monotoneCapacity_le_sealed D c _)
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨g,rfl⟩
  exact quadratic_sealing_probe_bound D c g


theorem sealedCapacity_add_depth {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (k l : ℕ) : sealedCapacity D c (k+l) ≤ sealedCapacity D c k := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨g,rfl⟩
  dsimp only
  rw [abs_mul,abs_pow,pow_add]
  have hp := pow_le_pow_left₀ (abs_nonneg _) (normalized_displacement_bound g) l
  rw [one_pow] at hp
  have hb := sealedCapacity_probe_bound D c k g
  rw [abs_mul,abs_pow] at hb
  calc
    _ = (|displacement (normalizeProbe g)|^k*|familyValue D c (normalizeProbe g)|)*
        |displacement (normalizeProbe g)|^l := by ring
    _ ≤ (|displacement (normalizeProbe g)|^k*|familyValue D c (normalizeProbe g)|)*1 :=
      mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ sealedCapacity D c k := by simpa only [mul_one] using hb

theorem quadratic_sealing_allDepths {n r m : ℕ}
    (D : Fin m → Fin (r+2) → Finset (Fin (n+1))) (c : Fin m → ℝ) (k : ℕ) :
    sealedCapacity D c ((r+2)*(r+1)+k) = monotoneCapacity D c := by
  apply le_antisymm _ (monotoneCapacity_le_sealed D c _)
  exact (sealedCapacity_add_depth D c _ k).trans_eq (quadratic_sealing_capacity D c)

theorem sixWindows_reversal_sealed_six (k : ℕ) :
    sealedCapacity sixWindows ![27,-1] (6+k) = 1 := by
  have h := quadratic_sealing_allDepths (r := 1) sixWindows (![27,-1] : Fin 2 → ℝ) k
  rw [sixWindows_reversal_monotoneCapacity] at h
  exact h

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
