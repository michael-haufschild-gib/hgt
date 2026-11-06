import GaloisForLFunctions.RHTower.PositiveRealResolventChart
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Finite pole jets decay away from their height

For `P(s) = Σ cρ/(s−ρ)` with `|Im ρ| ≤ H`, the actual derivatives satisfy
`‖P⁽ᵏ⁾(s)‖/k! ≤ Σ‖cρ‖/(|Im s|−H)^(k+1)` above height `H`.
After multiplication by a local detection radius to power `k+1`, this finite pole contribution
tends to zero whenever the radius is smaller than the vertical gap.
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
  rw [iteratedDeriv_const_mul_field, RHTower.iteratedDeriv_inv_sub ρ k s
    (sub_ne_zero.mpr (hs ρ hρ))]
  ring


end
end GaloisForLFunctions.ZeroConfigurationGeometry
