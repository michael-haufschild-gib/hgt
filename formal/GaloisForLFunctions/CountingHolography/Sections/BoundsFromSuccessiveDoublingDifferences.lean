import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # One-sided bounds from successive doubling differences

Normalizing by the linear scale kills the boundary term at infinity.
Each inversion preserves every power strictly below one.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections
open Filter Topology
namespace SquareDoubling

def scale (n : ℕ) : ℝ := (n : ℝ)+1

theorem scale_ge_one (n : ℕ) : 1 ≤ scale n := by
  unfold scale
  linarith only [Nat.cast_nonneg (α := ℝ) n]

theorem scale_step (n : ℕ) : scale (2*n+1) = 2*scale n := by
  unfold scale
  push_cast
  ring

theorem sublinear_power {r : ℝ} (hr : r < 1) :
    Tendsto (fun n : ℕ => (scale n)^r / scale n) atTop (𝓝 0) := by
  have hS : Tendsto scale atTop atTop := tendsto_atTop_mono
    (f := fun n : ℕ => (n : ℝ)) (fun n => le_add_of_nonneg_right zero_le_one) tendsto_natCast_atTop_atTop
  have h := (tendsto_rpow_neg_atTop (show 0 < 1-r by linarith)).comp hS
  apply h.congr fun n => ?_
  change (scale n)^(-(1-r)) = _
  rw [show -(1-r) = r-1 by ring,Real.rpow_sub (zero_lt_one.trans_le (scale_ge_one n)),Real.rpow_one]

/-- After normalizing by n+1, a negative value propagating to a larger
integer would persist arbitrarily far out, contradicting convergence to zero. -/
private theorem nonneg_of_doubling {g : ℕ → ℝ} (hlim : Tendsto g atTop (𝓝 0))
    (hd : ∀ n : ℕ, 0 < n → g (2*n+1) ≤ g n) {n : ℕ} (hn : 0 < n) : 0 ≤ g n := by
  by_contra! hneg
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hlim.eventually_const_lt hneg)
  have hex (k : ℕ) : ∃ d : ℕ, n+k ≤ d ∧ g d ≤ g n := by
    induction k with
    | zero => exact ⟨n,by omega,le_rfl⟩
    | succ k ih =>
      obtain ⟨d,hk,hd'⟩ := ih
      exact ⟨2*d+1,by omega,(hd d (by omega)).trans hd'⟩
  obtain ⟨d,hk,hd'⟩ := hex N
  exact (hN d (by omega)).not_ge hd'

theorem lower_of_doubling_difference {F : ℕ → ℝ} {r C : ℝ} (hr : r < 1)
    (hlim : Tendsto (fun n => F n/scale n) atTop (𝓝 0))
    (hd : ∀ n : ℕ, 0 < n → F (2*n+1) ≤ 2*F n+C*(scale n)^r) :
    ∃ A : ℝ, ∀ n : ℕ, 0 < n → -(A*(scale n)^r) ≤ F n := by
  have ht : (2:ℝ)^r < 2 := by
    simpa only [Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hr
  let A := C/(2-(2:ℝ)^r)
  have hA : A*(2-(2:ℝ)^r) = C := div_mul_cancel₀ _ (sub_pos.mpr ht).ne'
  let g (n : ℕ) := (F n+A*(scale n)^r)/scale n
  have hg : Tendsto g atTop (𝓝 0) := by
    simpa only [g,add_div,mul_div_assoc,mul_zero,add_zero] using hlim.add ((sublinear_power hr).const_mul A)
  have hstep (n : ℕ) (hn : 0 < n) : g (2*n+1) ≤ g n := by
    have hpos := zero_lt_one.trans_le (scale_ge_one n)
    have hh := congrArg (fun b : ℝ => b*(scale n)^r) hA
    have he : F (2*n+1) + A*((2:ℝ)^r*(scale n)^r) ≤ 2*(F n+A*(scale n)^r) := by
      linarith only [hd n hn,hh]
    unfold g
    rw [scale_step,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hpos.le]
    exact (div_le_div_of_nonneg_right he (mul_nonneg two_pos.le hpos.le)).trans_eq
      (mul_div_mul_left _ _ two_ne_zero)
  refine ⟨A,fun n hn => ?_⟩
  have h := (le_div_iff₀ (zero_lt_one.trans_le (scale_ge_one n))).mp (nonneg_of_doubling hg hstep hn)
  linarith only [h]

end SquareDoubling

open SquareDoubling

/-- A lower bound for the second forward doubling difference descends to
the sequence at the same sublinear power of the square-root conductor. -/
theorem lower_of_second_doubling_difference {F : ℕ → ℝ} {r C : ℝ} (hr : r < 1)
    (hlim : Tendsto (fun n : ℕ => F n/((n:ℝ)+1)) atTop (𝓝 0))
    (hd : ∀ n : ℕ, 0 < n → -(C*((n:ℝ)+1)^r) ≤
      4*F n-4*F (2*n+1)+F (2*(2*n+1)+1)) :
    ∃ A : ℝ, ∀ n : ℕ, 0 < n → -(A*((n:ℝ)+1)^r) ≤ F n := by
  let g := fun n : ℕ => 2*F n-F (2*n+1)
  have hu : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (f := id) (fun n => by dsimp; omega) tendsto_id
  change Tendsto (fun n => F n/scale n) atTop (𝓝 0) at hlim
  have hg : Tendsto (fun n => g n/scale n) atTop (𝓝 0) := by
    have ht := (hlim.const_mul 2).sub ((hlim.comp hu).const_mul 2)
    simp only [mul_zero,sub_zero] at ht
    apply ht.congr fun n => ?_
    change 2*(F n/scale n)-2*(F (2*n+1)/scale (2*n+1)) = (2*F n-F (2*n+1))/scale n
    rw [scale_step]
    field_simp [(zero_lt_one.trans_le (scale_ge_one n)).ne'] <;> ring
  obtain ⟨K,hK⟩ := lower_of_doubling_difference hr hg (C := C) (fun n hn => by
    dsimp only [g,scale]
    linarith only [hd n hn])
  exact lower_of_doubling_difference hr hlim (C := K) (fun n hn => by
    have h := hK n hn
    dsimp only [g] at h
    linarith only [h])

end GaloisForLFunctions.CountingHolography.Sections
