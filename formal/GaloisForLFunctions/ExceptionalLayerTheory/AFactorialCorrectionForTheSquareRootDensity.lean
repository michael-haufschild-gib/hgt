import GaloisForLFunctions.ExceptionalLayerTheory.LogFactorialWeightsForTheMiddlePrimeInterval
import GaloisForLFunctions.RHTower.Sieve.LogLogTelescope

/-!
# A factorial correction orthogonal to the square-root density

Two dilated parity functions have the same leading factorial pairing after
rescaling. Their difference has a square-root moment of definite sign.
It can therefore remove this moment from the complementary factorial weight.
-/

noncomputable section

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

def edge (j : ℕ) : ℝ := (Real.sqrt j)⁻¹

/-- Weight of a quotient cell under the square-root density at unit horizon. -/
def cellSize (j : ℕ) : ℝ := edge j - edge (j+1)

theorem cellSize_nonneg {j : ℕ} (hj : 1 ≤ j) : 0 ≤ cellSize j := by
  unfold cellSize edge
  apply sub_nonneg.mpr
  apply inv_anti₀ (Real.sqrt_pos.mpr (by exact_mod_cast hj : (0 : ℝ) < j))
  exact Real.sqrt_le_sqrt (by push_cast; linarith)

private theorem sum_cellSize {a b : ℕ} (h : a ≤ b) :
    ∑ j ∈ Ico a b, cellSize j = edge a - edge b := by
  have h' := RHTower.Sieve.sum_Ico_telescope (fun j => -edge j) h
  simpa only [cellSize,neg_sub_neg] using h'

/-- Finite square-root moment of the first J quotient cells. -/
def squareMoment (J : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Ico 1 (J+1), w j * cellSize j

/-- The total cell mass above R is at most the reciprocal square root of R. -/
private theorem moment_bound {R J : ℕ} (hR : 1 ≤ R) (hJ : R ≤ J+1)
    {w : ℕ → ℝ} {M : ℝ} (hM : 0 ≤ M) (hw : ∀ j, |w j| ≤ M)
    (hz : ∀ j, 1 ≤ j → j < R → w j = 0) :
    |squareMoment J w| ≤ M * edge R := by
  have hsub : Ico R (J+1) ⊆ Ico 1 (J+1) := fun j hj =>
    mem_Ico.mpr ⟨hR.trans (mem_Ico.mp hj).1,(mem_Ico.mp hj).2⟩
  unfold squareMoment
  rw [← sum_subset (f := fun j => w j * cellSize j) hsub (by
    intro j hj hnot
    have hlt : j < R := by
      by_contra! h
      exact hnot (mem_Ico.mpr ⟨h,(mem_Ico.mp hj).2⟩)
    rw [hz j (mem_Ico.mp hj).1 hlt,zero_mul])]
  calc
    _ ≤ ∑ j ∈ Ico R (J+1), M * cellSize j := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro j hj
      have h := cellSize_nonneg (hR.trans (mem_Ico.mp hj).1)
      rw [abs_mul,abs_of_nonneg h]
      exact mul_le_mul_of_nonneg_right (hw j) h
    _ ≤ _ := by
      rw [← mul_sum, sum_cellSize hJ]
      exact mul_le_mul_of_nonneg_left (sub_le_self _ (by unfold edge; positivity)) hM

private def parity (R j : ℕ) : ℝ := ((j/R%2 : ℕ) : ℝ)

private theorem parity_bounds (R j : ℕ) : 0 ≤ parity R j ∧ parity R j ≤ 1 := by
  unfold parity
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast (show j/R%2 ≤ 1 by omega)⟩

private theorem parity_one {a j : ℕ} (ha : 0 < a) (hl : a ≤ j) (hu : j < 2*a) :
    parity a j = 1 := by
  have h₁ := (Nat.one_le_div_iff ha).mpr hl
  have h₂ := (Nat.div_lt_iff_lt_mul ha).mpr hu
  simp [parity, show j/a = 1 by omega]

/-- The factor 64 preserves the linear factorial density and reverses the
sign of the square-root moment. -/
def parityCorrection (R j : ℕ) : ℝ := parity R j - 64*parity (64*R) j

/-- Both parity terms take values in the unit interval. -/
theorem parityCorrection_bound (a j : ℕ) : |parityCorrection a j| ≤ 65 := by
  obtain ⟨h₁,h₂⟩ := parity_bounds a j
  obtain ⟨h₃,h₄⟩ := parity_bounds (64*a) j
  rw [parityCorrection,abs_le]
  constructor <;> linarith only [h₁,h₂,h₃,h₄]

private theorem squareMoment_sub_mul (J : ℕ) (u v : ℕ → ℝ) (c : ℝ) :
    squareMoment J (fun j => u j - c*v j) = squareMoment J u - c*squareMoment J v := by
  simp only [squareMoment, sub_mul, mul_assoc, sum_sub_distrib, ← mul_sum]

private theorem edge_mul (a R : ℕ) : edge (a*R) = edge a * edge R := by
  simp [edge, Real.sqrt_mul (Nat.cast_nonneg a), mul_comm]

private theorem edge_gap (R : ℕ) :
    2*edge R ≤ 64*(edge (64*R) - edge (128*R)) := by
  have hroot : (32/3 : ℝ) ≤ Real.sqrt 128 := Real.le_sqrt_of_sq_le (by norm_num)
  have hinv := inv_anti₀ (by norm_num : (0 : ℝ) < 32/3) hroot
  have hnum : (2 : ℝ) ≤ 64*(edge 64-edge 128) := by
    unfold edge
    norm_num only [Nat.cast_ofNat, show Real.sqrt 64 = 8 by norm_num]
    norm_num at hinv
    linarith only [hinv]
  rw [edge_mul 64,edge_mul 128, ← sub_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hnum (by unfold edge; positivity)

private def resolution (R : ℕ) := 128*R^2

private theorem resolution_large {R : ℕ} (hR : 1 ≤ R) : 128*R ≤ resolution R := by
  exact Nat.mul_le_mul_left _ (by simpa [sq] using Nat.mul_le_mul_left R hR)

private theorem correction_moment {R : ℕ} (hR : 1 ≤ R) :
    squareMoment (resolution R) (parityCorrection R) ≤ -edge R := by
  let J := resolution R
  have hJ : 128*R ≤ J := resolution_large hR
  have hpar := moment_bound (J := J) hR (by omega) (w := parity R) (show (0 : ℝ) ≤ 1 by norm_num)
    (fun j => by rw [abs_of_nonneg (parity_bounds R j).1]; exact (parity_bounds R j).2)
    (fun j _ hj => by simp [parity,Nat.div_eq_of_lt hj])
  have hlo : edge (64*R) - edge (128*R) ≤ squareMoment J (parity (64*R)) := by
    rw [← sum_cellSize (show 64*R ≤ 128*R by omega)]
    calc
      _ = ∑ j ∈ Ico (64*R) (128*R), parity (64*R) j * cellSize j := by
        apply sum_congr rfl
        intro j hj
        obtain ⟨hl,hu⟩ := mem_Ico.mp hj
        rw [parity_one (by omega) hl (by omega : j < 2*(64*R)),one_mul]
      _ ≤ _ := by
        apply sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨hl,hu⟩ := mem_Ico.mp hj
          exact mem_Ico.mpr ⟨by omega,by omega⟩
        · intro j hj _
          exact mul_nonneg (parity_bounds ..).1 (cellSize_nonneg (mem_Ico.mp hj).1)
  have hup := (le_abs_self _).trans hpar
  change squareMoment J (fun j => parity R j - 64*parity (64*R) j) ≤ _
  rw [squareMoment_sub_mul]
  linarith only [hup,hlo,edge_gap R]

/-- Coefficient removing the finite square-root moment of the complementary prefix. -/
def momentRatio (R : ℕ) : ℝ :=
  squareMoment (resolution R) (fun j => 1-factorialPrefix R j) /
    squareMoment (resolution R) (parityCorrection R)

/-- The square-root correction costs at most the original coefficient mass plus one. -/
theorem ratio_bound {R : ℕ} (hR : 1 ≤ R) : |momentRatio R| ≤ 1+mass R := by
  have he : 0 < edge R := by unfold edge; positivity
  have hg := correction_moment hR
  have hM : 0 ≤ 1+mass R := by
    have := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
    linarith
  have hJ := resolution_large hR
  have hw := moment_bound (J := resolution R) hR (by omega) hM
    (fun j => (abs_sub 1 (factorialPrefix R j)).trans
      (add_le_add (le_of_eq abs_one) (abs_prefix_le_mass hR j)))
    (fun j hj hjR => by rw [prefix_one hj hjR, sub_self])
  have hneg : squareMoment (resolution R) (parityCorrection R) < 0 := by linarith only [he,hg]
  rw [momentRatio,abs_div,abs_of_neg hneg]
  apply (div_le_iff₀ (by linarith only [he,hg])).mpr
  exact hw.trans (mul_le_mul_of_nonneg_left (by linarith only [hg]) hM)

/-- Complementary factorial weight with its finite square-root moment removed. -/
def primeWeight (R j : ℕ) : ℝ := (1-factorialPrefix R j) - momentRatio R * parityCorrection R j

theorem primeWeight_moment {R : ℕ} (hR : 1 ≤ R) :
    squareMoment (128*R^2) (primeWeight R) = 0 := by
  have he : 0 < edge R := by unfold edge; positivity
  have hg := correction_moment hR
  have hne : squareMoment (resolution R) (parityCorrection R) ≠ 0 := by linarith only [he,hg]
  change squareMoment (resolution R) (primeWeight R) = 0
  unfold primeWeight
  rw [squareMoment_sub_mul, momentRatio, div_mul_cancel₀ _ hne, sub_self]

theorem primeWeight_small {R j : ℕ} (hj : 1 ≤ j) (hlt : j < R) : primeWeight R j = 0 := by
  simp [primeWeight, prefix_one hj hlt,parityCorrection,parity,Nat.div_eq_of_lt hlt,
    Nat.div_eq_of_lt (show j < 64*R by omega)]

theorem primeWeight_bound {R : ℕ} (hR : 1 ≤ R) (j : ℕ) :
    |primeWeight R j| ≤ 66*(1+mass R) := by
  have hw := (abs_sub 1 (factorialPrefix R j)).trans
    (add_le_add (le_of_eq abs_one) (abs_prefix_le_mass hR j))
  have hg := parityCorrection_bound R j
  have hM := (abs_nonneg _).trans hw
  apply (abs_sub _ _).trans
  rw [abs_mul]
  have h := mul_le_mul (ratio_bound hR) hg (abs_nonneg _) hM
  linarith only [hw,h]

private theorem parity_floor (a j : ℕ) :
    parity a j = ((j/a : ℕ) : ℝ) - 2*((j/(2*a) : ℕ) : ℝ) := by
  have h := Nat.mod_add_div (j/a) 2
  have hr : (↑((j/a)%2) : ℝ) + 2*↑((j/a)/2) = ↑(j/a) := by exact_mod_cast h
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm a 2] at hr
  unfold parity
  linarith only [hr]

/-- The parity correction is a signed sum of four divisor floors. -/
theorem parityCorrection_floors (a j : ℕ) : parityCorrection a j =
    (((j/a : ℕ) : ℝ)-2*((j/(2*a) : ℕ) : ℝ))-
    64*((((j/(64*a) : ℕ) : ℝ))-2*((j/(2*(64*a)) : ℕ) : ℝ)) := by
  simp only [parityCorrection,parity_floor]

/-- The first nonzero quotient cell of the correction has index at least a. -/
theorem parityCorrection_small {a j : ℕ} (h : j < a) : parityCorrection a j = 0 := by
  simp [parityCorrection,parity,Nat.div_eq_of_lt h,Nat.div_eq_of_lt (show j < 64*a by omega)]

private def parityPair (a X : ℕ) : ℝ := ∑ m ∈ Icc 1 X, vonMangoldt m * parity a (X/m)

/-- The leading factorial pairing of a single parity is X log(2)/a. -/
private theorem parity_pair_bound {a X : ℕ} (ha : 1 ≤ a) (hX : 1 ≤ X) :
    |parityPair a X - ((X : ℝ)/a)*Real.log 2| ≤
      3*(3+Real.log (2*a : ℕ)+2*Real.log X) := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hlog := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) ha0.ne'
  have h₁ := abs_le.mp (ArithmeticKreinLangerTheory.abs_log_div_factorial_sub_le hX ha)
  have h₂ := abs_le.mp (ArithmeticKreinLangerTheory.abs_log_div_factorial_sub_le hX
    (show 1 ≤ 2*a by omega))
  have hle : Real.log a ≤ Real.log (2*a : ℕ) := Real.log_le_log ha0 (by exact_mod_cast (by omega : a ≤ 2*a))
  have hid : parityPair a X = Real.log ((X/a).factorial : ℕ) - 2*Real.log ((X/(2*a)).factorial : ℕ) := by
    simp only [parityPair,parity_floor,mul_sub, sum_sub_distrib,mul_left_comm (vonMangoldt _) (2 : ℝ),
      ← mul_sum,mangoldt_floor]
  rw [hid,abs_le]
  push_cast at h₂ hle ⊢
  rw [hlog] at h₂ hle ⊢
  have hm : 2 * (((X : ℝ)/(2*a))*(Real.log X-(Real.log 2+Real.log a)-1)) =
      ((X : ℝ)/a)*(Real.log X-Real.log a-1) - ((X : ℝ)/a)*Real.log 2 := by ring
  constructor <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2,hm,hle]

/-- The correction has logarithmic pairing with all von Mangoldt weights. -/
theorem correction_pair {R X : ℕ} (hR : 1 ≤ R) (hX : 1 ≤ X) :
    |∑ m ∈ Icc 1 X, vonMangoldt m * parityCorrection R (X/m)| ≤
        195*(3+Real.log (128*R : ℕ)+2*Real.log X) := by
  have h₁ := abs_le.mp (parity_pair_bound hR hX)
  have h₂ := abs_le.mp (parity_pair_bound (show 1 ≤ 64*R by omega) hX)
  have hid : (∑ m ∈ Icc 1 X, vonMangoldt m * parityCorrection R (X/m)) =
      parityPair R X - 64*parityPair (64*R) X := by
    simp only [parityCorrection,parityPair,mul_sub,mul_left_comm (vonMangoldt _) (64 : ℝ),
      sum_sub_distrib,mul_sum]
  have hle : Real.log (2*R : ℕ) ≤ Real.log (128*R : ℕ) := Real.log_le_log
    (by exact_mod_cast (show 0 < 2*R by omega)) (by exact_mod_cast (show 2*R ≤ 128*R by omega))
  rw [show 2*(64*R) = 128*R by omega] at h₂
  have hm : 64*(((X : ℝ)/(64*R))*Real.log 2) = ((X : ℝ)/R)*Real.log 2 := by ring
  push_cast only [Nat.cast_mul,Nat.cast_ofNat] at h₂
  push_cast only [Nat.cast_mul,Nat.cast_ofNat] at h₁ hle ⊢
  rw [hid,abs_le]
  constructor <;> linarith only [h₁.1,h₁.2,h₂.1,h₂.2,hm,hle]

/-- Complementary pairing with the full prime powers reproduces the
density-subtracted Chebyshev function at logarithmic cost per unit mass. -/
theorem primeWeight_factorial {R X : ℕ} (hR : 1 ≤ R) (hX : 1 ≤ X) :
    |(Chebyshev.psi X - X) - ∑ m ∈ Icc 1 X, vonMangoldt m * primeWeight R (X/m)| ≤
      196*(1+mass R)*(3+Real.log (128*R : ℕ)+2*Real.log X) := by
  have hΨ : ∑ m ∈ Icc 1 X, vonMangoldt m = Chebyshev.psi X := by
    unfold Chebyshev.psi; rw [Nat.floor_natCast]; rfl
  have hid : (Chebyshev.psi X-X) - ∑ m ∈ Icc 1 X, vonMangoldt m * primeWeight R (X/m) =
      ((∑ m ∈ Icc 1 X, vonMangoldt m * factorialPrefix R (X/m))-X) +
        momentRatio R * ∑ m ∈ Icc 1 X, vonMangoldt m * parityCorrection R (X/m) := by
    simp only [primeWeight,mul_sub,mul_one,mul_left_comm (vonMangoldt _) (momentRatio R),
      sum_sub_distrib, ← mul_sum,hΨ]
    ring
  have hle : Real.log (2*R : ℕ) ≤ Real.log (128*R : ℕ) := Real.log_le_log
    (by exact_mod_cast (show 0 < 2*R by omega)) (by exact_mod_cast (show 2*R ≤ 128*R by omega))
  have hm : 0 ≤ mass R := (abs_nonneg _).trans (abs_prefix_le_mass hR 0)
  have hL := Real.log_natCast_nonneg (128*R)
  have hXlog := Real.log_natCast_nonneg X
  have hL0 : 0 ≤ 3+Real.log (128*R : ℕ)+2*Real.log X := by positivity
  rw [hid]
  apply (abs_add_le _ _).trans
  rw [abs_mul]
  have hf := (abs_mangoldt_prefix_sub_count_le hR hX).trans
    (mul_le_mul_of_nonneg_left (show 3+Real.log (2*R : ℕ)+2*Real.log X ≤
      3+Real.log (128*R : ℕ)+2*Real.log X by linarith only [hle]) hm)
  have hg := mul_le_mul (ratio_bound hR) (correction_pair hR hX) (abs_nonneg _) (by linarith only [hm])
  linarith only [hf,hg,hL0]

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
