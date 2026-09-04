import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicReciprocalAbel
import GaloisForLFunctions.RHTower.Sieve.RelMoebiusSharp
import GaloisForLFunctions.RHTower.Sieve.ContourParamMono
import GaloisForLFunctions.RHTower.Sieve.PolylogLimits
import GaloisForLFunctions.RHTower.Sieve.Section4DiscCofactor

/-!
# Low-frequency bound for Menon's harmonic Möbius polynomial

The zero-free-region estimate for twisted Möbius sums is transferred through reciprocal Abel
summation to the exact harmonic coefficient `μ(n)/n`.  Its relative majorant beats every fixed
power of the logarithm, uniformly throughout every admissible low-frequency disc.
-/

namespace RHTower.Sieve

open Finset Filter Topology

noncomputable section

theorem ramareCofactorCoeff_empty (n : ℕ) :
    ramareCofactorCoeff ∅ n = moebiusCoeff n := by
  simp [ramareCofactorCoeff, moebiusCoeff, primeFactorsIn]

theorem harmonicRamareCofactorCoeff_empty (n : ℕ) :
    harmonicRamareCofactorCoeff ∅ n = harmonicMoebiusC n := by
  simp [harmonicRamareCofactorCoeff, harmonicMoebiusC, primeFactorsIn]

/-- Uniform low-frequency estimate on an arbitrary positive harmonic Möbius block. -/
theorem exists_norm_logPoly_harmonicMoebiusC_Icc_le :
    ∃ (K₀ : ℕ) (N₁ : ℝ), ∀ (a b : ℕ) (w : ℝ), 1 ≤ a → a ≤ b →
      N₁ ≤ ((a - 1 : ℕ) : ℝ) →
      K₀ ≤ contourParam (a : ℝ) →
      5 + 4 * |(-(2 * Real.pi * w))|
        ≤ ((contourParam (a : ℝ) : ℕ) : ℝ) →
      ‖logPoly harmonicMoebiusC (Finset.Icc a b) w‖
        ≤ ((((a - 1 : ℕ) : ℝ) + (b : ℝ)) * relMoebiusSharp ((a - 1 : ℕ) : ℝ)) /
            (a : ℝ) := by
  obtain ⟨K₀, N₁, hsharp⟩ := exists_norm_logPoly_moebiusCoeff_Icc_le
  refine ⟨K₀, max N₁ (Real.exp 1), ?_⟩
  intro a b w ha hab hN hK hτ
  have haExp : Real.exp 1 ≤ ((a - 1 : ℕ) : ℝ) := le_trans (le_max_right _ _) hN
  have ha1 : (1 : ℝ) ≤ ((a - 1 : ℕ) : ℝ) :=
    le_trans (by nlinarith [Real.exp_one_gt_d9]) haExp
  have ha0 : (0 : ℝ) < ((a - 1 : ℕ) : ℝ) := zero_lt_one.trans_le ha1
  have habR : ((a - 1 : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast (by omega : a - 1 ≤ b)
  have hrel0 := relMoebiusSharp_nonneg ha0
  have hmain := norm_logPoly_harmonicRamareCofactor_Icc_le_of_prefix
    (∅ : Finset ℕ) ha hab w (E :=
      (((a - 1 : ℕ) : ℝ) + (b : ℝ)) * relMoebiusSharp ((a - 1 : ℕ) : ℝ)) ?_
  · have hempty : harmonicRamareCofactorCoeff ∅ = harmonicMoebiusC :=
      funext harmonicRamareCofactorCoeff_empty
    rw [hempty] at hmain
    exact hmain
  · intro c hac hcb
    have hNlo : N₁ ≤ ((a - 1 : ℕ) : ℝ) := le_trans (le_max_left _ _) hN
    have hcN : N₁ ≤ (c : ℝ) := le_trans hNlo (by exact_mod_cast (by omega : a - 1 ≤ c))
    have hacR : ((a - 1 : ℕ) : ℝ) ≤ (c : ℝ) := by exact_mod_cast (by omega : a - 1 ≤ c)
    have hlog : (1 : ℝ) ≤ Real.log ((a - 1 : ℕ) : ℝ) :=
      (Real.le_log_iff_exp_le ha0).2 haExp
    have hwidth : (1 : ℝ) ≤ smoothWidth ((a - 1 : ℕ) : ℝ) :=
      one_le_smoothWidth ha0 hlog
    have haCast : (a : ℝ) = ((a - 1 : ℕ) : ℝ) + 1 := by
      norm_cast
      omega
    have hargLo : (a : ℝ) ≤
        ((a - 1 : ℕ) : ℝ) + smoothWidth ((a - 1 : ℕ) : ℝ) := by
      rw [haCast]
      linarith
    have hcWidth0 : 0 ≤ smoothWidth (c : ℝ) := by
      rw [smoothWidth]
      exact div_nonneg (Nat.cast_nonneg c) (smoothRatio_pos _).le
    have hargHi : (a : ℝ) ≤ (c : ℝ) + smoothWidth (c : ℝ) := by
      have hacCast : (a : ℝ) ≤ (c : ℝ) := by exact_mod_cast hac
      linarith
    have hcontLo : contourParam (a : ℝ) ≤
        contourParam (((a - 1 : ℕ) : ℝ) + smoothWidth ((a - 1 : ℕ) : ℝ)) :=
      contourParam_mono (by exact_mod_cast ha) hargLo
    have hcontHi : contourParam (a : ℝ) ≤
        contourParam ((c : ℝ) + smoothWidth (c : ℝ)) :=
      contourParam_mono (by exact_mod_cast ha) hargHi
    have hbase := hsharp a c w ha hNlo hcN (le_trans hK hcontLo) (le_trans hK hcontHi)
      (le_trans hτ (by exact_mod_cast hcontLo)) (le_trans hτ (by exact_mod_cast hcontHi))
    rw [moebiusSharpBound_eq_mul ha0,
      moebiusSharpBound_eq_mul (lt_of_lt_of_le ha0 hacR)] at hbase
    have hrel : relMoebiusSharp (c : ℝ) ≤ relMoebiusSharp ((a - 1 : ℕ) : ℝ) :=
      relMoebiusSharp_antitone ha1 hacR
    have hcbR : (c : ℝ) ≤ (b : ℝ) := by exact_mod_cast hcb
    have hempty : ramareCofactorCoeff ∅ = moebiusCoeff := funext ramareCofactorCoeff_empty
    rw [hempty]
    refine hbase.trans ?_
    nlinarith [relMoebiusSharp_nonneg (lt_of_lt_of_le ha0 hacR)]

/-- Every fixed log power is absorbed by the relative sharp twisted-Möbius majorant. -/
theorem tendsto_log_rpow_mul_relMoebiusSharp_zero (p : ℝ) :
    Tendsto (fun x : ℝ => (Real.log x) ^ p * relMoebiusSharp x) atTop (𝓝 0) := by
  let κ : ℝ := zeroFreeConst / 8192 / 2
  have hκ : 0 < κ := by
    dsimp [κ]
    exact div_pos (div_pos zeroFreeConst_pos (by norm_num)) (by norm_num)
  have hu : Tendsto (fun x : ℝ => (Real.log x) ^ ((1 : ℝ) / 20)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp Real.tendsto_log_atTop
  have hbase : Tendsto (fun x : ℝ =>
      (Real.log x) ^ p * Real.exp (-((Real.log x) ^ ((1 : ℝ) / 20)))) atTop (𝓝 0) :=
    tendsto_rpow_log_mul_exp_neg (c := p) (a := (1 / 20 : ℝ)) (by norm_num)
  have hfirst : Tendsto (fun x : ℝ =>
      (Real.log x) ^ p *
        (3 * Real.exp (-(zeroFreeConst / 8192 *
          ((Real.log x) ^ ((1 : ℝ) / 20)) ^ 2 / 2)) / Real.pi)) atTop (𝓝 0) := by
    have hmajor : Tendsto (fun x : ℝ =>
        (3 / Real.pi) * ((Real.log x) ^ p *
          Real.exp (-((Real.log x) ^ ((1 : ℝ) / 20))))) atTop (𝓝 0) := by
      simpa using hbase.const_mul (3 / Real.pi)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _) ?_ hmajor
    filter_upwards [hu.eventually_ge_atTop (1 / κ),
      eventually_gt_atTop (1 : ℝ)] with x hx hxl
    have hlog : 0 < Real.log x := Real.log_pos hxl
    have hu0 : 0 ≤ (Real.log x) ^ ((1 : ℝ) / 20) :=
      Real.rpow_nonneg hlog.le _
    have hκu : 1 ≤ κ * (Real.log x) ^ ((1 : ℝ) / 20) := by
      calc
        (1 : ℝ) = κ * (1 / κ) := by field_simp
        _ ≤ κ * (Real.log x) ^ ((1 : ℝ) / 20) :=
          mul_le_mul_of_nonneg_left hx hκ.le
    have hquad : (Real.log x) ^ ((1 : ℝ) / 20) ≤
        κ * ((Real.log x) ^ ((1 : ℝ) / 20)) ^ 2 := by
      nlinarith
    have hexp : Real.exp (-(zeroFreeConst / 8192 *
          ((Real.log x) ^ ((1 : ℝ) / 20)) ^ 2 / 2)) ≤
        Real.exp (-((Real.log x) ^ ((1 : ℝ) / 20))) := by
      rw [Real.exp_le_exp]
      dsimp [κ] at hquad
      nlinarith
    have hp0 : 0 ≤ (Real.log x) ^ p := Real.rpow_nonneg hlog.le _
    have hc0 : 0 ≤ 3 / Real.pi := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc
      (Real.log x) ^ p *
          (3 * Real.exp (-(zeroFreeConst / 8192 *
            ((Real.log x) ^ ((1 : ℝ) / 20)) ^ 2 / 2)) / Real.pi)
        = (3 / Real.pi) * (Real.log x) ^ p *
            Real.exp (-(zeroFreeConst / 8192 *
              ((Real.log x) ^ ((1 : ℝ) / 20)) ^ 2 / 2)) := by ring
      _ ≤ (3 / Real.pi) * (Real.log x) ^ p *
            Real.exp (-((Real.log x) ^ ((1 : ℝ) / 20))) :=
          mul_le_mul_of_nonneg_left hexp (mul_nonneg hc0 hp0)
      _ = (3 / Real.pi) * ((Real.log x) ^ p *
            Real.exp (-((Real.log x) ^ ((1 : ℝ) / 20)))) := by ring
      _ = _ := rfl
  have hsecond : Tendsto (fun x : ℝ =>
      (Real.log x) ^ p * (1 / smoothRatio x)) atTop (𝓝 0) := by
    simpa [smoothRatio, one_div, Real.exp_neg] using hbase
  have hthird : Tendsto (fun x : ℝ =>
      (Real.log x) ^ p * (1 / x)) atTop (𝓝 0) := by
    have h := (_root_.isLittleO_log_rpow_rpow_atTop p
      (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
    simpa [Real.rpow_one, div_eq_mul_inv] using h
  have hsum := (hfirst.add hsecond).add hthird
  simpa only [relMoebiusSharp, mul_add, zero_add] using hsum

/-- Pure inverse-log envelope, with no hidden parameter dependence. -/
theorem eventually_relMoebiusSharp_le_log_rpow_neg (p : ℝ) :
    ∀ᶠ x : ℝ in atTop, relMoebiusSharp x ≤ (Real.log x) ^ (-p) := by
  have hlim := tendsto_log_rpow_mul_relMoebiusSharp_zero p
  have hone := hlim.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hone, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hp0 : 0 < (Real.log x) ^ p := Real.rpow_pos_of_pos hlog _
  rw [Real.rpow_neg hlog.le, ← one_div, le_div_iff₀ hp0]
  simpa only [mul_comm] using hx.le

/-- The exact harmonic Möbius polynomial over a low-frequency disc. -/
theorem exists_setIntegral_disc_normSq_logPoly_harmonicMoebiusC_Icc_le :
    ∃ (K₀ : ℕ) (N₁ : ℝ), ∀ (a b : ℕ) (w₀ : ℝ), 1 ≤ a → a ≤ b → 0 ≤ w₀ →
      N₁ ≤ ((a - 1 : ℕ) : ℝ) → K₀ ≤ contourParam (a : ℝ) →
      5 + 4 * (2 * Real.pi * w₀) ≤ ((contourParam (a : ℝ) : ℕ) : ℝ) →
      (∫ w in Set.Icc (-w₀) w₀,
          ‖logPoly harmonicMoebiusC (Finset.Icc a b) w‖ ^ 2) ≤
        (((((a - 1 : ℕ) : ℝ) + (b : ℝ)) * relMoebiusSharp ((a - 1 : ℕ) : ℝ)) /
            (a : ℝ)) ^ 2 * (2 * w₀) := by
  obtain ⟨K₀, N₁, hpoint⟩ := exists_norm_logPoly_harmonicMoebiusC_Icc_le
  refine ⟨K₀, N₁, ?_⟩
  intro a b w₀ ha hab hw₀ hN hK hτ
  refine setIntegral_disc_normSq_logPoly_le harmonicMoebiusC (Finset.Icc a b) hw₀ ?_
  intro w hw
  rw [Set.mem_Icc] at hw
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have habs : |(-(2 * Real.pi * w))| ≤ 2 * Real.pi * w₀ := by
    rw [abs_neg, abs_mul, abs_of_pos hπ]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨hw.1, hw.2⟩) hπ.le
  exact hpoint a b w ha hab hN hK (by linarith [hτ, habs])

end

end RHTower.Sieve
