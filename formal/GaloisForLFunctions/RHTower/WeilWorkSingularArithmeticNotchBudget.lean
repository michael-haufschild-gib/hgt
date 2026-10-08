import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticNotchGoodScales
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticNotchTail
import GaloisForLFunctions.RHTower.WeilAbsoluteConvergenceRigidity

/-!
# Simultaneous control of the notch mass terms

The harmonic head, full square-root mass, and shifted tail are controlled
on every large scale. Only the local square-root mass requires selection.
-/

noncomputable section
open Finset

namespace RHTower.WeilSingularArithmetic
open WeilAbscissa

/-- The four nonnegative masses in the localized notch estimate. -/
def notchMassBudget (d : ℕ → ℝ) (c L : ℝ) : ℝ :=
  let N := ⌈(1 + L) ^ 2⌉₊
  (∑ n ∈ range (N + 1), |d n| / n) +
    Real.log L / Real.sqrt L *
      (∑ n ∈ range (N + 1), |d n| / Real.sqrt n *
        (if (n : ℝ) ≤ c * L then 1 else 0)) +
    (∑ n ∈ range (N + 1), |d n| / Real.sqrt n) / (1 + L) +
    (1 + L) * ∑' i : ℕ,
      (|d (i + (N + 1))| / (i + (N + 1) : ℕ)) / Real.sqrt (i + (N + 1) : ℕ)

/-- All four masses share one bound after a single local scale is selected. -/
theorem notchMassBudget_le {d : ℕ → ℝ} {A η c L : ℝ}
    (hA : 0 ≤ A) (hη : 0 ≤ η) (hL : 32 ≤ L)
    (hb : ∀ N : ℕ, 1 ≤ N → (∑ n ∈ range (N + 1), |d n| / n) ≤ A + η * Real.log N)
    (hlocal : ∀ F : Finset ℕ,
      (∑ n ∈ F, |d n| / Real.sqrt n * (if (n : ℝ) ≤ c * L then 1 else 0)) ≤
        η * Real.sqrt L) :
    notchMassBudget d c L ≤ 4 * A + 4 * η + 18 * η * Real.log (L - 1) := by
  let N := ⌈(1 + L) ^ 2⌉₊
  let H := ∑ n ∈ range (N + 1), |d n| / n
  let T := ∑ n ∈ range (N + 1), |d n| / Real.sqrt n
  let S := A + 4 * η * Real.log (L - 1)
  have hL0 : 0 < L := by linarith
  have hLp : 0 < 1 + L := by linarith
  have hNlo : (1 + L) ^ 2 ≤ (N : ℝ) := Nat.le_ceil _
  have hNhi : (N : ℝ) ≤ 2 * (1 + L) ^ 2 := by
    have := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ (1 + L) ^ 2 by positivity)
    dsimp [N]
    nlinarith
  have hN : 1 ≤ N := by
    have h : (1 : ℝ) ≤ N := by nlinarith
    exact_mod_cast h
  have hslo : 1 + L ≤ Real.sqrt N := by
    rw [Real.le_sqrt hLp.le (by positivity)]
    exact hNlo
  have hshi : Real.sqrt N ≤ 2 * (1 + L) := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hlogN : Real.log N ≤ 4 * Real.log (L - 1) := by
    have := one_add_log_ceil_le hL
    change 1 + Real.log N ≤ 4 * Real.log (L - 1) at this
    linarith
  have hH0 : 0 ≤ H := Finset.sum_nonneg fun n _ => by positivity
  have hH : H ≤ S := by
    have h := mul_le_mul_of_nonneg_left hlogN hη
    have hbN := hb N hN
    dsimp [H, S]
    nlinarith
  have hT : T / (1 + L) ≤ 2 * S := by
    have ht := sum_abs_div_sqrt_le_sqrt_mul_harmonic d N
    change T ≤ Real.sqrt N * H at ht
    have ht' := ht.trans (mul_le_mul_of_nonneg_right hshi hH0)
    apply (div_le_iff₀ hLp).mpr
    have hh := mul_le_mul_of_nonneg_left hH (show 0 ≤ 2 * (1 + L) by positivity)
    nlinarith
  have hsL := Real.sqrt_pos.mpr hL0
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hlogL : Real.log L ≤ 2 * Real.log (L - 1) := by
    have hlm : 0 < L - 1 := by linarith
    have h := Real.log_le_log hL0 (show L ≤ (L - 1) * (L - 1) by nlinarith)
    rwa [Real.log_mul hlm.ne' hlm.ne', ← two_mul] at h
  have hloc : Real.log L / Real.sqrt L *
      (∑ n ∈ range (N + 1), |d n| / Real.sqrt n *
        (if (n : ℝ) ≤ c * L then 1 else 0)) ≤ 2 * η * Real.log (L - 1) := by
    calc
      _ ≤ Real.log L / Real.sqrt L * (η * Real.sqrt L) :=
        mul_le_mul_of_nonneg_left (hlocal _) (by positivity)
      _ = η * Real.log L := by field_simp
      _ ≤ η * (2 * Real.log (L - 1)) := mul_le_mul_of_nonneg_left hlogL hη
      _ = _ := by ring
  have htail := tsum_shift_div_sqrt_le_of_log_envelope
    (fun n => div_nonneg (abs_nonneg (d n)) (Nat.cast_nonneg n)) hA hη hb hN
  have htail' : (1 + L) * (∑' i : ℕ,
      (|d (i + (N + 1))| / (i + (N + 1) : ℕ)) / Real.sqrt (i + (N + 1) : ℕ)) ≤
        S + 4 * η := by
    have hcoef : 0 ≤ A + η * (Real.log N + 4) := by
      have : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
      positivity
    have hsN : 0 < Real.sqrt (N : ℝ) := lt_of_lt_of_le hLp hslo
    calc
      _ ≤ (1 + L) * ((A + η * (Real.log N + 4)) * (Real.sqrt N)⁻¹) :=
        mul_le_mul_of_nonneg_left htail hLp.le
      _ = (A + η * (Real.log N + 4)) * ((1 + L) / Real.sqrt N) := by ring
      _ ≤ (A + η * (Real.log N + 4)) * 1 :=
        mul_le_mul_of_nonneg_left ((div_le_one hsN).mpr hslo) hcoef
      _ ≤ S + 4 * η := by
        have := mul_le_mul_of_nonneg_left hlogN hη
        dsimp [S]
        nlinarith
  change H + _ + T / (1 + L) + _ ≤ _
  dsimp [S] at hH hT htail'
  linarith

/-- Harmonic smallness makes the complete notch budget smaller than every
positive logarithmic floor on arbitrarily late scales. -/
theorem exists_notchMassBudget_lt_log_floor (d : ℕ → ℝ)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ range (N + 1), |d n| / n) ≤ A + η * Real.log N)
    {c κ K : ℝ} (hc : 0 < c) (hκ : 0 < κ) (hK : 0 ≤ K) (C L₀ : ℝ) :
    ∃ L : ℝ, max 32 L₀ ≤ L ∧ C + K * notchMassBudget d c L < κ * Real.log (L - 1) := by
  have hshift : ∀ η : ℝ, 0 < η → ∃ A : ℝ, 0 ≤ A ∧ ∀ N : ℕ,
      (∑ n ∈ range (N + 1), |d n| / n) ≤ A + η * Real.log (N + 1) := by
    intro η hη
    obtain ⟨A, hA, hb⟩ := hsmall η hη
    refine ⟨A, hA, fun N => ?_⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simpa using hA
    · have hlog := Real.log_le_log (show 0 < (N : ℝ) by exact_mod_cast hN)
        (show (N : ℝ) ≤ (N : ℝ) + 1 by linarith)
      exact (hb N hN).trans (add_le_add (le_refl A) (mul_le_mul_of_nonneg_left hlog hη.le))
  let η := κ / (1 + 36 * K)
  have hden : 0 < 1 + 36 * K := by positivity
  have hη : 0 < η := div_pos hκ hden
  have hηeq : η * (1 + 36 * K) = κ := by dsimp [η]; field_simp
  obtain ⟨A, hA, hb⟩ := hsmall η hη
  let B := |C| + K * (4 * A + 4 * η) + 1
  have hB : 0 < B := by dsimp [B]; positivity
  obtain ⟨L, hL, hlocal⟩ := exists_large_local_mass_scale_of_harmonic_envelope d hshift hc hη
    (max (max 32 L₀) (1 + Real.exp (2 * B / κ)))
  have hLbase : max 32 L₀ ≤ L :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hL)
  have hLexp : 1 + Real.exp (2 * B / κ) ≤ L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hL)
  have hL32 : 32 ≤ L := (le_max_left _ _).trans hLbase
  have hlog := Real.log_le_log (Real.exp_pos (2 * B / κ))
    (show Real.exp (2 * B / κ) ≤ L - 1 by linarith)
  rw [Real.log_exp] at hlog
  have hlg0 : 0 ≤ Real.log (L - 1) := Real.log_nonneg (by linarith)
  have hm := (div_le_iff₀ hκ).mp hlog
  have hcoef : 18 * K * η ≤ κ / 2 := by nlinarith
  have hcprod := mul_le_mul_of_nonneg_right hcoef hlg0
  have hbudget := mul_le_mul_of_nonneg_left (notchMassBudget_le hA hη.le hL32 hb hlocal) hK
  refine ⟨L, hLbase, ?_⟩
  have hC := le_abs_self C
  dsimp [B] at hm
  nlinarith

end RHTower.WeilSingularArithmetic
