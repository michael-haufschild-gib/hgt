import GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit.AZeroFreeRegionBoundsTheHeavyReturns
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.SignedPrimeLogSquareWindows
import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth

/-!
# Homogeneous return transfer would collapse every zero-free strip

A strip of depth `h < 1/2` excludes heavy prime returns up to `exp(ηT)`
when the prime cutoff is `floor(T^(2/(1/2-h)))`. Consequently a transfer
from those return-free intervals to uniformly bounded prime traces on
log-square windows would imply that quasi-RH is RH.
-/

open Filter Topology Complex
open Zeta23
noncomputable section
namespace GaloisForLFunctions.SignFreePurityMechanisms

open TranscendenceTheoryOfThePrimeOrbit SquareRootThreshold SurfaceOfSpecZ.ScaleLocality

/-- No heavy subset of the small primes returns to the identity in the prescribed height range. -/
def NoHeavyIdentityReturn (A η δ T₁ T : ℝ) : Prop :=
  ∀ H : Finset ℕ, IsHeavy ⌊T ^ A⌋₊ (1 / 1000) H →
    ∀ t : ℝ, T₁ ≤ t → t ≤ Real.exp (η * T) →
      ¬ IsDeltaReturn H (fun p : ℕ => Real.log p) δ t

/-- The proposed uniform transfer from homogeneous returns to one prime window. -/
def HomogeneousReturnWindowTransfer : Prop :=
  ∀ A η δ T₁ : ℝ, 0 < A → 0 < η → 0 < δ → δ ≤ 1 / 20 →
    ∃ K U : ℝ, ∀ T : ℝ, U ≤ T → NoHeavyIdentityReturn A η δ T₁ T →
      ∀ p : ℕ, p.Prime → |Real.log p - T| ≤ primeLogSquareRadius T →
        |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) (Real.log p)).re| ≤ K

/-- Every strict strip excludes heavy returns throughout the power-height range of a late window. -/
theorem eventually_noHeavyIdentityReturn_of_strip {h T₀ η : ℝ}
    (hh : 0 ≤ h) (hh1 : h < 1 / 2)
    (hstrip : ∀ ρ ∈ zetaZeroConfig.carrier, T₀ ≤ |ρ.im| → |ρ.re - 1 / 2| ≤ h) :
    ∃ T₁ : ℝ, ∀ᶠ T : ℝ in atTop,
      NoHeavyIdentityReturn (2 / (1 / 2 - h)) η (1 / 20) T₁ T := by
  obtain ⟨c, hc, T₁, hreturn⟩ := log_ge_of_heavy_return_of_strip hh hstrip
  obtain ⟨N, hN⟩ := eventually_atTop.mp hreturn
  let d : ℝ := 1 / 2 - h
  let A : ℝ := 2 / d
  have hd : 0 < d := by dsimp [d]; linarith only [hh1]
  have hA : 1 ≤ A := by
    dsimp [A]
    rw [le_div_iff₀ hd]
    dsimp [d]
    linarith only [hh]
  let b : ℝ := c * (1 / 2 : ℝ) ^ d
  have hb : 0 < b := mul_pos hc (Real.rpow_pos_of_pos (by norm_num) d)
  refine ⟨max T₁ 1, ?_⟩
  filter_upwards [eventually_ge_atTop (max 2 (2 * (N : ℝ))),
    eventually_gt_atTop (η / b)] with T hT hlarge
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hT1 : 1 ≤ T := by linarith only [hT2]
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hNT : 2 * (N : ℝ) ≤ T := (le_max_right _ _).trans hT
  have hTp : T ≤ T ^ A := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hT1 hA
  have hfloor : (1 / 2 : ℝ) * T ^ A ≤ (⌊T ^ A⌋₊ : ℝ) := by
    have hf := Nat.lt_floor_add_one (T ^ A)
    linarith only [hf, hTp, hT2]
  have hyN : N ≤ ⌊T ^ A⌋₊ := by
    have hy : (N : ℝ) ≤ (⌊T ^ A⌋₊ : ℝ) := by
      linarith only [hNT, hTp, hfloor]
    exact_mod_cast hy
  have hyPow : (1 / 2 : ℝ) ^ d * T ^ 2 ≤ (⌊T ^ A⌋₊ : ℝ) ^ d := by
    have hm := Real.rpow_le_rpow
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hT0.le A)) hfloor hd.le
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hT0.le A),
      ← Real.rpow_mul hT0.le, show A * d = 2 by dsimp [A]; field_simp,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hm
    exact hm
  intro H hH t ht hupper hret
  have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
  have hlower := hN _ hyN H hH (1 / 20) t (by norm_num) le_rfl
    ((le_max_left _ _).trans ht) hret
  have hlog : Real.log t ≤ η * T := by
    have hh := Real.log_le_log (lt_of_lt_of_le zero_lt_one ht1) hupper
    rwa [Real.log_exp] at hh
  have hquad : b * T ^ 2 ≤ Real.log t := by
    simpa only [b, mul_assoc] using
      (mul_le_mul_of_nonneg_left hyPow hc.le).trans hlower
  have hlin : η < b * T := by
    have hh := (div_lt_iff₀ hb).mp hlarge
    linarith only [hh]
  have hstrict := mul_lt_mul_of_pos_right hlin hT0
  nlinarith only [hquad, hlog, hstrict]

/-- The return-window transfer implies quasi-RH collapses to RH. -/
theorem homogeneousReturnWindowTransfer_implies_quasiRH_collapse :
    HomogeneousReturnWindowTransfer →
      (_root_.RHTower.zetaZeroAbscissa < 1 → RiemannHypothesis) := by
  intro htransfer hΘ
  have hw : zetaZeroWidth < 1 / 2 := by
    rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
    linarith only [hΘ]
  obtain ⟨T₁, hfree⟩ := eventually_noHeavyIdentityReturn_of_strip
    (η := 1) (T₀ := 0) zetaZeroWidth_nonneg hw
    (fun ρ hρ _ => abs_re_sub_half_le_zetaZeroWidth hρ)
  obtain ⟨K, U, hK⟩ := htransfer (2 / (1 / 2 - zetaZeroWidth)) 1 (1 / 20) T₁
    (div_pos (by norm_num) (by linarith only [hw])) zero_lt_one (by norm_num) le_rfl
  obtain ⟨V, hV⟩ := eventually_atTop.mp hfree
  apply riemannHypothesis_iff_abs_prime_logSquare_windows_signed.mpr
  refine ⟨K, fun W => ?_⟩
  let T := max W (max U V)
  refine ⟨T, le_max_left _ _, hK T ?_ (hV T ?_)⟩
  · exact (le_max_left U V).trans (le_max_right W _)
  · exact (le_max_right U V).trans (le_max_right W _)

/-- In abscissa notation, the same implication is `Theta < 1` implies `Theta = 1/2`. -/
theorem homogeneousReturnWindowTransfer_implies_abscissa_collapse :
    HomogeneousReturnWindowTransfer →
      (_root_.RHTower.zetaZeroAbscissa < 1 → _root_.RHTower.zetaZeroAbscissa = 1 / 2) := by
  intro htransfer hΘ
  have hRH := homogeneousReturnWindowTransfer_implies_quasiRH_collapse htransfer hΘ
  have hw := riemannHypothesis_iff_zetaZeroWidth_eq_zero.mp hRH
  rw [zetaZeroWidth_eq_zetaZeroAbscissa_sub_half] at hw
  linarith only [hw]

#print axioms eventually_noHeavyIdentityReturn_of_strip
#print axioms homogeneousReturnWindowTransfer_implies_quasiRH_collapse
#print axioms homogeneousReturnWindowTransfer_implies_abscissa_collapse

end GaloisForLFunctions.SignFreePurityMechanisms
