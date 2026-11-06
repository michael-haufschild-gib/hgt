import GaloisForLFunctions.RHTower.PositiveRealResolventChart
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Finite pole jets decay away from their height

For `P(s) = Σ cρ/(s−ρ)` with `|Im ρ| ≤ H`, the actual derivatives satisfy
`‖P⁽ᵏ⁾(s)‖/k! ≤ Σ‖cρ‖/(|Im s|−H)^(k+1)` above height `H`.
Radius-normalized jets decay uniformly in derivative order once the vertical gap exceeds
the radius, including when the order varies with height.

At a fixed centre with a unique nearest pole `ρ₀`, the normalization by `(s−ρ₀)^(k+1)`
recovers its coefficient. Thus both suppression at distant centres and residue recovery at
a fixed centre follow from the same exact derivative formula.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.ZeroConfigurationGeometry

noncomputable section

/-- The signed factorial-normalized derivative of a finite simple-pole sum. -/
def finitePoleJet (F : Finset ℂ) (c : ℂ → ℂ) (k : ℕ) (s : ℂ) : ℂ :=
  ∑ ρ ∈ F, c ρ / (s - ρ) ^ (k + 1)


/-- Vertical separation bounds the distance to every pole, independently of real parts. -/
theorem height_gap_le_norm_sub {s ρ : ℂ} {H : ℝ} (hρ : |ρ.im| ≤ H) :
    |s.im| - H ≤ ‖s - ρ‖ := by
  have htri := abs_sub_abs_le_abs_sub s.im ρ.im
  have him := Complex.abs_im_le_norm (s - ρ)
  rw [Complex.sub_im] at him
  linarith

/-- All derivative orders of a finite low-height pole family obey the same height gap. -/
theorem norm_finitePoleJet_le (F : Finset ℂ) (c : ℂ → ℂ) (k : ℕ)
    {s : ℂ} {H : ℝ} (hF : ∀ ρ ∈ F, |ρ.im| ≤ H) (hs : H < |s.im|) :
    ‖finitePoleJet F c k s‖ ≤ (∑ ρ ∈ F, ‖c ρ‖) / (|s.im| - H) ^ (k + 1) := by
  have hd : 0 < |s.im| - H := sub_pos.mpr hs
  calc
    ‖finitePoleJet F c k s‖ ≤ ∑ ρ ∈ F, ‖c ρ / (s - ρ) ^ (k + 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ρ ∈ F, ‖c ρ‖ / (|s.im| - H) ^ (k + 1) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      rw [norm_div, norm_pow]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (pow_pos hd _)
        (pow_le_pow_left₀ hd.le (height_gap_le_norm_sub (hF ρ hρ)) _)
    _ = _ := (Finset.sum_div _ _ _).symm

/-- Multiplication by a detection radius gives geometric suppression with ratio `r / gap`. -/
theorem scaled_norm_finitePoleJet_le (F : Finset ℂ) (c : ℂ → ℂ) (k : ℕ)
    {s : ℂ} {H r : ℝ} (hF : ∀ ρ ∈ F, |ρ.im| ≤ H)
    (hs : H < |s.im|) (hr : 0 ≤ r) :
    r ^ (k + 1) * ‖finitePoleJet F c k s‖ ≤
      (∑ ρ ∈ F, ‖c ρ‖) * (r / (|s.im| - H)) ^ (k + 1) := by
  calc
    r ^ (k + 1) * ‖finitePoleJet F c k s‖ ≤
        r ^ (k + 1) * ((∑ ρ ∈ F, ‖c ρ‖) / (|s.im| - H) ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left (norm_finitePoleJet_le F c k hF hs) (pow_nonneg hr _)
    _ = _ := by rw [div_pow]; ring


/-- Above one detection radius, the decay bound is uniform in derivative order.
In particular, choosing the order as a function of height cannot remove this decay. -/
theorem scaled_norm_finitePoleJet_le_uniform_in_order
    (F : Finset ℂ) (c : ℂ → ℂ) (k : ℕ) {s : ℂ} {H r : ℝ}
    (hF : ∀ ρ ∈ F, |ρ.im| ≤ H) (hs : H < |s.im|)
    (hr : 0 ≤ r) (hgap : H + r ≤ |s.im|) :
    r ^ (k + 1) * ‖finitePoleJet F c k s‖ ≤
      (∑ ρ ∈ F, ‖c ρ‖) * r / (|s.im| - H) := by
  have hd : 0 < |s.im| - H := sub_pos.mpr hs
  have hq0 : 0 ≤ r / (|s.im| - H) := div_nonneg hr hd.le
  have hq1 : r / (|s.im| - H) ≤ 1 := (div_le_one hd).mpr (by linarith)
  have hp : ∀ j : ℕ, (r / (|s.im| - H)) ^ (j + 1) ≤ r / (|s.im| - H) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ]
      exact (mul_le_mul_of_nonneg_right ih hq0).trans (mul_le_of_le_one_right hq0 hq1)
  calc
    _ ≤ (∑ ρ ∈ F, ‖c ρ‖) * (r / (|s.im| - H)) ^ (k + 1) :=
      scaled_norm_finitePoleJet_le F c k hF hs hr
    _ ≤ (∑ ρ ∈ F, ‖c ρ‖) * (r / (|s.im| - H)) :=
      mul_le_mul_of_nonneg_left (hp k) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    _ = _ := by ring

/-- Radius-normalized jets vanish when the radius is smaller than the vertical pole gap. -/
theorem tendsto_scaled_finitePoleJet (F : Finset ℂ) (c : ℂ → ℂ)
    {s : ℂ} {H r : ℝ} (hF : ∀ ρ ∈ F, |ρ.im| ≤ H)
    (hr : 0 ≤ r) (hs : H + r < |s.im|) :
    Tendsto (fun k : ℕ => r ^ (k + 1) * ‖finitePoleJet F c k s‖) atTop (𝓝 0) := by
  have hd : 0 < |s.im| - H := by linarith
  have hq0 : 0 ≤ r / (|s.im| - H) := div_nonneg hr hd.le
  have hq1 : r / (|s.im| - H) < 1 := (div_lt_one hd).mpr (by linarith)
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have hbound : Tendsto
      (fun k : ℕ => (∑ ρ ∈ F, ‖c ρ‖) * (r / (|s.im| - H)) ^ (k + 1))
      atTop (𝓝 0) := by
    simpa only [pow_succ, mul_zero, zero_mul] using
      (tendsto_const_nhds.mul (hpow.mul_const (r / (|s.im| - H))))
  exact squeeze_zero (fun k => mul_nonneg (pow_nonneg hr _) (norm_nonneg _))
    (fun k => scaled_norm_finitePoleJet_le F c k hF (by linarith) hr) hbound

/-- These finite power sums are the actual normalized derivatives, not only formal jets. -/
theorem iteratedDeriv_finitePoleJet_zero (F : Finset ℂ) (c : ℂ → ℂ) (k : ℕ)
    {s : ℂ} (hs : ∀ ρ ∈ F, s ≠ ρ) :
    iteratedDeriv k (finitePoleJet F c 0) s =
      (-1 : ℂ) ^ k * (k.factorial : ℂ) * finitePoleJet F c k s := by
  have hterm : ∀ ρ ∈ F, ContDiffAt ℂ k (fun z : ℂ => c ρ * (z - ρ)⁻¹) s := by
    intro ρ hρ
    have hne : s - ρ ≠ 0 := sub_ne_zero.mpr (hs ρ hρ)
    fun_prop
  have hfun : finitePoleJet F c 0 = fun z => ∑ ρ ∈ F, c ρ * (z - ρ)⁻¹ := by
    funext z
    simp only [finitePoleJet, zero_add, pow_one, div_eq_mul_inv]
  rw [hfun, iteratedDeriv_fun_sum hterm]
  simp only [finitePoleJet, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [_root_.iteratedDeriv_const_mul_field]
  rw [RHTower.iteratedDeriv_inv_sub ρ k s (sub_ne_zero.mpr (hs ρ hρ))]
  ring


/-- The factorial-normalized actual derivative decays with the vertical pole gap. -/
theorem norm_iteratedDeriv_finitePoleJet_zero_div_factorial_le
    (F : Finset ℂ) (c : ℂ → ℂ) (k : ℕ) {s : ℂ} {H : ℝ}
    (hF : ∀ ρ ∈ F, |ρ.im| ≤ H) (hs : H < |s.im|) :
    ‖iteratedDeriv k (finitePoleJet F c 0) s‖ / (k.factorial : ℝ) ≤
      (∑ ρ ∈ F, ‖c ρ‖) / (|s.im| - H) ^ (k + 1) := by
  have hsne : ∀ ρ ∈ F, s ≠ ρ := by
    intro ρ hρ heq
    have h := hF ρ hρ
    rw [← heq] at h
    linarith
  have hfact : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hcoeff : ‖(-1 : ℂ) ^ k * (k.factorial : ℂ)‖ = (k.factorial : ℝ) := by simp
  rw [iteratedDeriv_finitePoleJet_zero F c k hsne, norm_mul, hcoeff,
    mul_comm, mul_div_cancel_right₀ _ hfact]
  exact norm_finitePoleJet_le F c k hF hs


/-- High derivatives at a fixed centre recover the coefficient of its unique nearest pole. -/
theorem tendsto_finitePoleJet_at_unique_nearest (F : Finset ℂ) (c : ℂ → ℂ)
    {s ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ F) (hs : s ≠ ρ₀)
    (hnearest : ∀ ρ ∈ F, ρ ≠ ρ₀ → ‖s - ρ₀‖ < ‖s - ρ‖) :
    Tendsto (fun k : ℕ => (s - ρ₀) ^ (k + 1) * finitePoleJet F c k s)
      atTop (𝓝 (c ρ₀)) := by
  classical
  have hterm : ∀ ρ ∈ F, Tendsto
      (fun k : ℕ => c ρ * ((s - ρ₀) / (s - ρ)) ^ (k + 1))
      atTop (𝓝 (if ρ = ρ₀ then c ρ₀ else 0)) := by
    intro ρ hρ
    by_cases heq : ρ = ρ₀
    · subst ρ
      simpa only [div_self (sub_ne_zero.mpr hs), one_pow, mul_one, if_true] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => c ρ₀) atTop (𝓝 (c ρ₀)))
    · have hgap := hnearest ρ hρ heq
      have hd : 0 < ‖s - ρ‖ := lt_of_le_of_lt (norm_nonneg _) hgap
      have hq : ‖(s - ρ₀) / (s - ρ)‖ < 1 := by
        rw [norm_div]
        exact (div_lt_one hd).mpr hgap
      have hp := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq
      simpa only [heq, if_false, pow_succ, mul_zero, zero_mul] using
        ((hp.mul_const ((s - ρ₀) / (s - ρ))).const_mul (c ρ))
  have hsum := tendsto_finsetSum F hterm
  have hlim : (∑ ρ ∈ F, if ρ = ρ₀ then c ρ₀ else 0) = c ρ₀ := by simp [hρ₀]
  rw [hlim] at hsum
  convert hsum using 1
  funext k
  rw [finitePoleJet, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [div_pow]
  ring


#print axioms norm_iteratedDeriv_finitePoleJet_zero_div_factorial_le
#print axioms scaled_norm_finitePoleJet_le_uniform_in_order
#print axioms tendsto_scaled_finitePoleJet
#print axioms tendsto_finitePoleJet_at_unique_nearest

end
end GaloisForLFunctions.ZeroConfigurationGeometry
