import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.HarmonicClocks.Readings
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.RapidZeros.Overlap

/-! # Gram matrix of equally spaced quantum compositions -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open scoped ComplexConjugate

private theorem shift_clock_coordinate (t c : ℝ) (f : Gas) (x : ℕ+ × ℕ+) :
    clockSplit (t+c) f x = splitPhase (c/2) (x.1*x.2)*clockSplit t f x := by
  have h : criticalTime (t+c) = criticalTime t+(2*criticalTime (c/2)-1) := by
    unfold criticalTime
    push_cast
    ring
  change channel (criticalTime (t+c)) (x.1*x.2) x.1*f (x.1*x.2) =
    splitPhase (c/2) _*(channel (criticalTime t) _ _*f _)
  rw [h,channel,channel,heat_add,splitPhase]
  ring

/-- Translating both observation times is invisible to their Hilbert-space overlap. -/
theorem clock_overlap_shift (w t c : ℝ) (f g : Gas) :
    inner ℂ (clockSplit (w+c) f) (clockSplit (t+c) g) = inner ℂ (clockSplit w f) (clockSplit t g) := by
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro x
  simp only [RCLike.inner_apply,shift_clock_coordinate,map_mul]
  have h : splitPhase (c/2) (x.1*x.2)*conj (splitPhase (c/2) (x.1*x.2)) = 1 := by
    rw [Complex.mul_conj,← Complex.sq_norm,splitPhase_norm]
    norm_num
  linear_combination (clockSplit t g x * conj (clockSplit w f x)) * h

theorem clock_overlap_difference (v : MissingWave) (w t : ℝ) :
    inner ℂ (clockSplit w v.val) (clockSplit t v.val) =
      (‖v.val‖^2:ℝ)*compositionResponse v (criticalTime ((t-w)/2)) := by
  let d := (t-w)/2
  have h := clock_overlap_shift (-d) d ((t+w)/2) v.val v.val
  rw [show -d+(t+w)/2 = w by dsimp only [d]; ring,
      show d+(t+w)/2 = t by dsimp only [d]; ring,split_pair_overlap] at h
  exact h

/-- The complete Gram matrix above the diagonal is indexed by positive clock differences. -/
theorem harmonic_clock_overlap (v : MissingWave) (t : ℝ) (i j : ℕ) (h : i ≤ j) :
    inner ℂ (clockSplit (2*(i:ℝ)*t) v.val) (clockSplit (2*(j:ℝ)*t) v.val) =
      (‖v.val‖^2:ℝ)*harmonicReading v t (j-i) := by
  rw [clock_overlap_difference,harmonicReading,Nat.cast_sub h]
  rw [show (2*(j:ℝ)*t-2*(i:ℝ)*t)/2 = ((j:ℝ)-(i:ℝ))*t by ring]

/-- All tested harmonics vanish precisely when the r outgoing split states are mutually orthogonal. -/
theorem orthogonal_clock_family_iff (r : ℕ+) (v : MissingWave) (t : ℝ) :
    (∀ i j : Fin r.val, i < j → inner ℂ (clockSplit (2*(i.val:ℝ)*t) v.val)
      (clockSplit (2*(j.val:ℝ)*t) v.val) = 0) ↔ harmonicTest r 0 v t := by
  have hM : ((‖v.val‖^2:ℝ):ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr (missingWave_ne_zero v)))
  constructor
  · intro hf h hp hl
    have he := hf ⟨0,r.pos⟩ ⟨h,hl⟩ (show (0:ℕ) < h from hp)
    rw [harmonic_clock_overlap v t 0 h (Nat.zero_le _),Nat.sub_zero] at he
    rw [(mul_eq_zero.mp he).resolve_left hM,norm_zero]
  · intro hh i j hij
    have hlt : i.val < j.val := hij
    rw [harmonic_clock_overlap _ _ _ _ hlt.le]
    have he := hh (j.val-i.val) (Nat.sub_pos_of_lt hlt) ((Nat.sub_le _ _).trans_lt j.isLt)
    rw [norm_le_zero_iff.mp he,mul_zero]

#print axioms clock_overlap_shift
#print axioms clock_overlap_difference
#print axioms harmonic_clock_overlap
#print axioms orthogonal_clock_family_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
