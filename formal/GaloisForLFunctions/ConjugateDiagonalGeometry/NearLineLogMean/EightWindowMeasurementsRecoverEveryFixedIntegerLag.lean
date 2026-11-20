import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheSuccessiveIntegerLagsOfTheLogWindow

/-!
# Eight window measurements recover every fixed integer lag

Take a rectangle in length and bandwidth large enough to activate
the first k lags of each new endpoint and small enough to exclude
lag k+1. Its mixed difference measures the sum of the first k Gram
correlations with constant weight. Subtract the rectangle for k−1:
only the prescribed lag survives, with conditioning independent of
the block's location.
-/

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
open Finset
noncomputable section

/-- Signed Gram sum at fixed additive lag r, indexed by its upper endpoint. -/
def integerLagBlock (a : ℕ → ℂ) (P Q r : ℕ) :=
  ∑ j ∈ Ico P Q, gram (a (j+1)) (a (j+1-r))

/-- Sum of the signed blocks at lags 1 through K. -/
def initialLagBlock (a : ℕ → ℂ) (P Q K : ℕ) :=
  ∑ j ∈ Ico P Q, ∑ r ∈ Icc 1 K, gram (a (j+1)) (a (j+1-r))

private theorem excess_step (a : ℕ → ℂ) (j : ℕ) (d : ℝ) :
    excessEnergy a (j+1) d-excessEnergy a j d = row a j d - ‖a (j+1)‖^2*d := by
  rw [excessEnergy,excessEnergy,row,sum_range_succ]
  ring

private theorem rectangular_row (a : ℕ → ℂ) {j K : ℕ} (hK : K≤j) {d e : ℝ}
    (hd : 0≤d) (hde : d≤e) (hlo : (K:ℝ) ≤ d*((j+1-K:ℕ):ℝ)) (hhi : e*((j+1:ℕ):ℝ) ≤ (K:ℝ)+1) :
    (excessEnergy a (j+1) e-excessEnergy a j e)-(excessEnergy a (j+1) d-excessEnergy a j d) =
      2*(e-d)*∑ r ∈ Icc 1 K, gram (a (j+1)) (a (j+1-r)) := by
  have hh := (mul_le_mul_of_nonneg_right hde (Nat.cast_nonneg (j+1) : 0≤((j+1:ℕ):ℝ))).trans hhi
  rw [excess_step,excess_step,row_by_initial_lags a hK (hd.trans hde) hhi,row_by_initial_lags a hK hd hh]
  rw [add_sub_cancel_left,add_sub_cancel_left,←mul_sub,←sum_sub_distrib,mul_assoc]
  congr 1
  rw [mul_sum]
  apply sum_congr rfl
  intro r hr
  have hrK := (mem_Icc.mp hr).2
  have hpos : 0<j+1-r := by omega
  have hn : ((j+1-K:ℕ):ℝ) ≤ (j+1-r:ℕ) := Nat.cast_le.mpr (by omega)
  have hl : logLag r (j+1-r) ≤ d := (log_lag_bounds r hpos).2.trans
    ((div_le_iff₀ (Nat.cast_pos.mpr hpos)).mpr
      ((Nat.cast_le.mpr hrK).trans (hlo.trans (mul_le_mul_of_nonneg_left hn hd))))
  simp only [lagPair,max_eq_left (sub_nonneg.mpr hl),max_eq_left (sub_nonneg.mpr (hl.trans hde)),
    show j+1-r+r=j+1 by omega]
  ring

/-- A length-bandwidth rectangle measures the sum of all the first K
lag correlations on its newly included endpoints. -/
theorem rectangle_reads_initial_lags (a : ℕ → ℂ) {P Q K : ℕ} (hpq : P≤Q) (hk : K≤P)
    {d e : ℝ} (hd : 0 ≤ d) (hde : d ≤ e) (hlo : (K:ℝ) ≤ d*((P+1-K:ℕ):ℝ))
    (hhi : e*(Q:ℝ) ≤ (K:ℝ)+1) :
    (excessEnergy a Q e-excessEnergy a P e)-(excessEnergy a Q d-excessEnergy a P d) =
      2*(e-d)*initialLagBlock a P Q K := by
  let F (j : ℕ) := excessEnergy a j e-excessEnergy a j d
  have htel : ∑ j ∈ Ico P Q, (F (j+1)-F j) = F Q-F P := by
    rw [sum_Ico_eq_sub _ hpq,sum_range_sub,sum_range_sub]
    ring
  rw [initialLagBlock,mul_sum]
  calc
    _ = F Q-F P := by dsimp only [F]; ring
    _ = _ := htel.symm.trans (sum_congr rfl fun j hj => by
      have hs := mem_Ico.mp hj
      have hlow := hlo.trans (mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (show P+1-K≤j+1-K by omega)) hd)
      have hhigh := (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.succ_le_of_lt hs.2)) (hd.trans hde)).trans hhi
      have h := rectangular_row a (hk.trans hs.1) hd hde hlow hhigh
      dsimp only [F]
      linarith only [h])

/-- Four energy measurements calibrated to the first K lags. -/
def initialLagReading (a : ℕ → ℂ) (P Q K : ℕ) (L : ℝ) :=
  ((K:ℝ)+1/2)*(normalizedExcess a Q (((K:ℝ)+1/2)/L)-normalizedExcess a P (((K:ℝ)+1/2)/L)) -
    (K:ℝ)*(normalizedExcess a Q ((K:ℝ)/L)-normalizedExcess a P ((K:ℝ)/L))

private theorem excess_mul_normalized (a : ℕ → ℂ) (M : ℕ) (v : ℝ) :
    excessEnergy a M v = v*normalizedExcess a M v := by
  rcases eq_or_ne v 0 with rfl|hv
  · rw [zero_mul,excess_energy_by_integer_lag a M 0 le_rfl (by simp)]
    simp
  · unfold normalizedExcess
    field_simp [hv]

private theorem reading_initial (a : ℕ → ℂ) {P Q K : ℕ} (hpq : P ≤ Q) (hk : K ≤ P)
    {L : ℝ} (hL : 0<L) (hleft : L ≤ ((P+1-K:ℕ):ℝ))
    (hright : ((K:ℝ)+1/2)*(Q:ℝ) ≤ ((K:ℝ)+1)*L) :
    initialLagBlock a P Q K = initialLagReading a P Q K L := by
  let d := (K:ℝ)/L
  let e := ((K:ℝ)+1/2)/L
  have hd : 0≤d := div_nonneg (Nat.cast_nonneg _) hL.le
  have hde : d≤e := div_le_div_of_nonneg_right (le_add_of_nonneg_right (by norm_num)) hL.le
  have hlo : (K:ℝ) ≤ d*((P+1-K:ℕ):ℝ) := by
    have h := mul_le_mul_of_nonneg_left hleft hd
    dsimp only [d] at h ⊢
    rwa [div_mul_cancel₀ _ hL.ne'] at h
  have hhi : e*(Q:ℝ) ≤ (K:ℝ)+1 := by
    dsimp only [e]
    rw [div_mul_eq_mul_div,div_le_iff₀ hL]
    exact hright
  have h := rectangle_reads_initial_lags a hpq hk hd hde hlo hhi
  rw [excess_mul_normalized a Q e,excess_mul_normalized a P e,
    excess_mul_normalized a Q d,excess_mul_normalized a P d] at h
  apply (mul_left_cancel₀ (show L⁻¹≠0 from inv_ne_zero hL.ne'))
  dsimp only [d,e] at h
  unfold initialLagReading
  linear_combination -h

/-- Subtraction of two consecutive calibrated rectangles isolates one
fixed lag. The eight coefficients depend only on that lag. -/
theorem eight_readings_recover_integer_lag (a : ℕ → ℂ) {P Q K : ℕ} (hpq : P ≤ Q) (hk : K+1 ≤ P)
    {L : ℝ} (hL : 0<L) (hleft : L ≤ ((P+1-(K+1):ℕ):ℝ))
    (hright : (((K+1:ℕ):ℝ)+1/2)*(Q:ℝ) ≤ (((K+1:ℕ):ℝ)+1)*L) :
    integerLagBlock a P Q (K+1) = initialLagReading a P Q (K+1) L - initialLagReading a P Q K L := by
  have hK := reading_initial a hpq hk hL hleft hright
  have hleft' := hleft.trans (Nat.cast_le.mpr (show P+1-(K+1) ≤ P+1-K by omega))
  have hLQ := hleft.trans (Nat.cast_le.mpr (show P+1-(K+1) ≤ Q by omega))
  have hright' : ((K:ℝ)+1/2)*(Q:ℝ) ≤ ((K:ℝ)+1)*L := by
    rw [Nat.cast_succ] at hright
    linarith only [hright,hLQ]
  rw [←hK,←reading_initial a hpq (by omega : K≤P) hL hleft' hright',integerLagBlock,initialLagBlock,initialLagBlock,
    ←sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  rw [sum_Icc_succ_top (by omega : 1≤K+1),add_sub_cancel_left]

/-- An explicit family of blocks of unbounded length for every fixed
positive lag. The two rectangles always fit, including their endpoints. -/
theorem fixed_lag_readings_on_expanding_blocks (a : ℕ → ℂ) (K : ℕ) {A : ℕ} (hA : 0 < A) (hKA : K≤A) :
    let P := (2*K+3)*A+K
    let Q := (2*K+4)*A
    let L : ℝ := (2*(K:ℝ)+3)*A
    integerLagBlock a P Q (K+1) = initialLagReading a P Q (K+1) L - initialLagReading a P Q K L := by
  dsimp only
  have hQ : (2*K+4)*A = (2*K+3)*A+A := by ring
  have hpos : 0<(2*K+3)*A := Nat.mul_pos (by omega) hA
  apply eight_readings_recover_integer_lag a (by omega) (by omega) (by positivity)
  · have h : (2*K+3)*A+K+1-(K+1)=(2*K+3)*A := by omega
    rw [h]
    push_cast
    rfl
  · push_cast
    apply le_of_eq
    ring

#print axioms fixed_lag_readings_on_expanding_blocks

#print axioms rectangle_reads_initial_lags
#print axioms eight_readings_recover_integer_lag
end
end GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval
