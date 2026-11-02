import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# A polynomial scale for the boundary gap

A quadratic height cutoff and an explicit polynomial radius make both
the polynomial bulk term and the sixth-power tail smaller than the
own-atom eighth-power height lower bound.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary

/-- An eighth-power atom dominates a polynomial bulk and a sixth-power
tail after a quadratic height cutoff and a polynomial radial choice. -/
lemma exists_polynomial_gap_scale {A B s₀ : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hs₀ : 0 < s₀) (N : ℕ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ s₀ ∧ ∀ H : ℝ, 1 ≤ H →
      ∃ T : ℝ, H ≤ T ∧
        B*((c/H^(2*N+8))*T^N+1/T^6) < A/H^8 := by
  let L := 1+8*B/A
  have hL : 1 ≤ L := le_add_of_nonneg_right (div_nonneg (mul_nonneg (by norm_num) hB.le) hA.le)
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hL6 : 8*B ≤ A*L^6 := by
    have hfirst : 8*B/A ≤ L := by dsimp only [L]; linarith
    have hpow : L ≤ L^6 := by
      calc
        L = L*1 := (mul_one L).symm
        _ ≤ L*L^5 := mul_le_mul_of_nonneg_left (one_le_pow₀ hL) hLp.le
        _ = _ := by ring
    exact (div_le_iff₀ hA).mp (hfirst.trans hpow) |>.trans_eq (by ring)
  let c := min s₀ (A/(8*B*L^N))
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcB : 8*B*L^N*c ≤ A := by
    have hh := (le_div_iff₀ (show 0 < 8*B*L^N by positivity)).mp (min_le_right s₀ (A/(8*B*L^N)))
    dsimp only [c]
    nlinarith only [hh]
  refine ⟨c,hc,min_le_left _ _,?_⟩
  intro H hH
  have hHp : 0 < H := zero_lt_one.trans_le hH
  let T := L*H^2
  have hTp : 0 < T := by dsimp only [T]; positivity
  have hHT : H ≤ T := by
    have hHH : H ≤ H^2 := by nlinarith only [hH,mul_nonneg (sub_nonneg.mpr hH) hHp.le]
    exact hHH.trans (le_mul_of_one_le_left (sq_nonneg H) hL)
  have hHpow : H^8 ≤ H^12 := by
    calc
      H^8 = H^8*1 := (mul_one _).symm
      _ ≤ H^8*H^4 := mul_le_mul_of_nonneg_left (one_le_pow₀ hH) (pow_nonneg hHp.le 8)
      _ = _ := by ring
  have htail : B/T^6 ≤ A/(8*H^8) := by
    apply (div_le_div_iff₀ (pow_pos hTp 6) (by positivity)).2
    have hh := mul_le_mul_of_nonneg_right hL6 (pow_nonneg hHp.le 8)
    have hh' := mul_le_mul_of_nonneg_left hHpow (mul_nonneg hA.le (pow_nonneg hLp.le 6))
    dsimp only [T]
    nlinarith only [hh,hh']
  have hscale : B*((c/H^(2*N+8))*T^N)=B*c*L^N/H^8 := by
    dsimp only [T]
    rw [mul_pow,pow_add,← pow_mul]
    field_simp [hHp.ne']
  have hbulk : B*((c/H^(2*N+8))*T^N) ≤ A/(8*H^8) := by
    rw [hscale]
    apply (div_le_div_iff₀ (pow_pos hHp 8) (by positivity)).2
    have hh := mul_le_mul_of_nonneg_right hcB (pow_nonneg hHp.le 8)
    nlinarith only [hh]
  have hpos : 0 < A/H^8 := div_pos hA (pow_pos hHp 8)
  refine ⟨T,hHT,?_⟩
  have he : A/(8*H^8)=(A/H^8)/8 := by ring
  rw [he] at htail hbulk
  rw [mul_add,mul_one_div]
  linarith only [htail,hbulk,hpos]

#print axioms exists_polynomial_gap_scale
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
