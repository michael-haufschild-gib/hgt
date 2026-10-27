import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheMertensEnergyPaysItsCriticalResidues
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.TheAbelCofactorGramsSelectTheDominantZeros

/-!
# The boundary receiver pays the critical shadows

At the damping `ε = Re ρ − ½` of an off-line zero `ρ` the translated zero `ρ − ε` lands on the
critical line, at its *shadow* `½ + i Im ρ`. The damped Möbius receiver's symbol
`(ζ(s)/ζ(s+ε) − m_ε ζ(s))/s` then has, on the line `Re s = ½`, a simple pole with residue
`r_ρ = ζ(½ + i Im ρ)/(ζ′(ρ)(½ + i Im ρ))`, the critical value at the shadow over `ζ′(ρ)`.

* **Rows** (`abs_receiver_le_sq`). `|A_ε(n)| ≤ (1 + |m_ε|) n²`.
* **The shadow law** (`shadow_mass_le_slope`). For `0 < ε < ½` and a finite set `Z` of simple
  zeros on `Re ρ = ½ + ε`, a receiver energy `E_ε(T) ≤ S log(T+1) + B` forces
  `Σ_{ρ ∈ Z} ‖r_ρ‖² ≤ S`: the logarithmic slope of the boundary receiver pays the critical values at
  the shadows (`sum_residue_le_slope` with the window poles of `exists_cofactor_pole_bound`).
* **The shadow growth rate** (`not_forall_receiver_energy_le_log`). `limsup E_ε(T)/log T` is at
  least the shadow mass `Σ_ρ ‖ζ(½ + i Im ρ)/(ζ′(ρ)(½ + i Im ρ))‖²`.

`ArithmeticContinuationAndCriticalEnergy` proves that admission at `ε` forces `ζ(½ + i Im ρ) = 0`
with multiplicity (`riemannZeta_criticalLine_eq_zero_of_mem_receiverDampings`). Here a nonzero
critical value at the shadow is converted into an explicit logarithmic energy rate: the boundary
receiver's energy slope is priced by the critical values of `ζ` at the shadows.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open GaloisForLFunctions.TransHorizonIncidenceMechanics (complexMellinCell complexMellinPairing
  weightCenteredPrefix weightCenteredPrefix_zero dampedDensity)
open GaloisForLFunctions.BezoutValuationIncidence (pmPowerDampedRealWeight)
open GaloisForLFunctions.ArithmeticDefectRigidity (logProfile)
open GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy (dampedMobiusEnergy)

/-- **The receiver grows at most quadratically**: `|A_ε(n)| ≤ (1 + |m_ε|) n²`. -/
theorem abs_receiver_le_sq {ε : ℝ} (hε : 0 ≤ ε) (n : ℕ) :
    |receiver ε n| ≤ (1 + |dampedDensity ε|) * (n : ℝ) ^ 2 := by
  have hc : ∀ d : ℕ, |pmPowerDampedRealWeight ε d| ≤ 1 := by
    intro d
    rw [pmPowerDampedRealWeight, abs_mul]
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp [BezoutValuationIncidence.moebiusReal]
    · have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
      exact mul_le_one₀ (BezoutValuationIncidence.abs_moebiusReal_le_one' d) (by positivity)
        (Real.rpow_le_one_of_one_le_of_nonpos hd1 (by linarith))
  have hsum : |∑ j ∈ Finset.Icc 1 n, ∑ d ∈ j.divisors, pmPowerDampedRealWeight ε d| ≤
      (n : ℝ) * n := by
    calc |∑ j ∈ Finset.Icc 1 n, ∑ d ∈ j.divisors, pmPowerDampedRealWeight ε d|
        ≤ ∑ j ∈ Finset.Icc 1 n, ∑ d ∈ j.divisors, |pmPowerDampedRealWeight ε d| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
            Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ j ∈ Finset.Icc 1 n, (j.divisors.card : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          calc ∑ d ∈ j.divisors, |pmPowerDampedRealWeight ε d| ≤ ∑ _d ∈ j.divisors, (1 : ℝ) :=
                Finset.sum_le_sum fun d _ => hc d
            _ = j.divisors.card := by simp
      _ ≤ ∑ _j ∈ Finset.Icc 1 n, (n : ℝ) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have := Nat.card_divisors_le_self j
          have hjn := (Finset.mem_Icc.mp hj).2
          exact_mod_cast this.trans hjn
      _ = (n : ℝ) * n := by simp
  rw [receiver, weightCenteredPrefix]
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h
      nlinarith
  calc |∑ j ∈ Finset.Icc 1 n, ∑ d ∈ j.divisors, pmPowerDampedRealWeight ε d - dampedDensity ε * n|
      ≤ |∑ j ∈ Finset.Icc 1 n, ∑ d ∈ j.divisors, pmPowerDampedRealWeight ε d| +
          |dampedDensity ε * n| := abs_sub _ _
    _ ≤ (n : ℝ) * n + |dampedDensity ε| * (n : ℝ) ^ 2 := by
        rw [abs_mul, Nat.abs_cast]
        gcongr
    _ = (1 + |dampedDensity ε|) * (n : ℝ) ^ 2 := by ring

/-- **The shadow law.** For `0 < ε < ½` and a finite set `Z` of simple zeros of `ζ` on
`Re ρ = ½ + ε`, a receiver energy `E_ε(T) ≤ S log(T+1) + B` forces
`Σ_{ρ ∈ Z} ‖ζ(ρ − ε)/(ζ′(ρ)(ρ − ε))‖² ≤ S`; here `ρ − ε = ½ + i Im ρ` is the shadow of `ρ`. -/
theorem shadow_mass_le_slope {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ deriv riemannZeta ρ ≠ 0 ∧ ρ.re = 1 / 2 + ε) {S B : ℝ}
    (hS0 : 0 ≤ S) (hB0 : 0 ≤ B)
    (hE : ∀ T : ℕ, dampedMobiusEnergy ε T ≤ S * Real.log ((T : ℝ) + 1) + B) :
    ∑ ρ ∈ Z, ‖riemannZeta (ρ - ε) / (deriv riemannZeta ρ * (ρ - ε))‖ ^ 2 ≤ S := by
  set v := receiver ε with hv
  have hv0 : v 0 = 0 := weightCenteredPrefix_zero _ _
  have hK : 0 ≤ 1 + |dampedDensity ε| := by positivity
  have hvb := abs_receiver_le_sq hε.le
  -- the log-scale energy is linear
  have hB' : 0 ≤ S * Real.log 2 + B := by have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2); positivity
  have hlin : ∀ L : ℝ, 0 ≤ L → ∫ u in (0 : ℝ)..L, logProfile v u ^ 2 ≤ S * L + (S * Real.log 2 + B) := by
    intro L hL
    set T := ⌊Real.exp L⌋₊ with hT
    have hLT : L ≤ Real.log ((T : ℝ) + 1) :=
      ((Real.lt_log_iff_exp_lt (by positivity)).mpr (Nat.lt_floor_add_one _)).le
    have hT2 : Real.log ((T : ℝ) + 1) ≤ L + Real.log 2 := by
      rw [← Real.log_exp L, ← Real.log_mul (Real.exp_pos L).ne' two_ne_zero]
      refine Real.log_le_log (by positivity) ?_
      have hfl : (T : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos L).le
      have h1 : 1 ≤ Real.exp L := Real.one_le_exp hL
      linarith
    calc ∫ u in (0 : ℝ)..L, logProfile v u ^ 2
        ≤ ∫ u in (0 : ℝ)..Real.log ((T : ℝ) + 1), logProfile v u ^ 2 := by
          refine intervalIntegral.integral_mono_interval le_rfl hL hLT
            (Eventually.of_forall fun u => sq_nonneg _) ?_
          exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (Real.log_nonneg (by
            linarith [T.cast_nonneg (α := ℝ)]))).mpr (integrableOn_logProfile_sq hK hvb _)
      _ = dampedMobiusEnergy ε T := by
          rw [← pronic_energy_eq_log_integral, receiver_energy_eq]
      _ ≤ S * Real.log ((T : ℝ) + 1) + B := hE T
      _ ≤ S * (L + Real.log 2) + B := by gcongr
      _ = S * L + (S * Real.log 2 + B) := by ring
  -- energy below every power, in receiver form
  have hEκ : ∀ κ : ℝ, 0 < κ → ∀ T : ℕ,
      dampedMobiusEnergy ε T ≤ (S / κ + (S * Real.log 2 + B)) * ((T : ℝ) + 1) ^ κ := by
    intro κ hκ T
    rw [← receiver_energy_eq]
    exact pronic_energy_le_of_linear hS0 hB' hlin hκ T
  have hCκ : ∀ κ : ℝ, 0 < κ → 0 ≤ S / κ + (S * Real.log 2 + B) := fun κ hκ =>
    add_nonneg (div_nonneg hS0 hκ.le) hB'
  -- the window poles at the shadows
  have hpole : ∀ ρ ∈ Z, ∃ δ₀ > 0, ∃ M : ℝ, ∀ e ∈ Ioo (0 : ℝ) δ₀,
      ∀ y ∈ Icc (ρ.im - δ₀) (ρ.im + δ₀),
        ‖lineSymbol (logProfile v) e y -
          riemannZeta (ρ - ε) / (deriv riemannZeta ρ * (ρ - ε)) /
            ((e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I)‖ ≤ M := by
    intro ρ hρ
    obtain ⟨hz, hd, hre⟩ := hZ ρ hρ
    have hρ1 : ρ ≠ 1 := fun h => by rw [h, Complex.one_re] at hre; linarith
    have hs0 : ρ - (ε : ℂ) ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    have hs1 : ρ - (ε : ℂ) ≠ 1 := fun h => by
      have := congrArg Complex.re h; simp at this; linarith
    obtain ⟨η, hη, M, hp⟩ := exists_cofactor_pole_bound (ε := (ε : ℂ)) (dampedDensity ε : ℂ)
      hz hd hρ1 hs0 hs1
    refine ⟨min (η / 2) (1 / 4), lt_min (by linarith) (by norm_num), M, fun e he y hy => ?_⟩
    have he1 : e < η / 2 := he.2.trans_le (min_le_left _ _)
    have he2 : e < 1 / 4 := he.2.trans_le (min_le_right _ _)
    have hy' : |y - ρ.im| ≤ η / 2 := abs_sub_le_iff.mpr
      ⟨by linarith [hy.2, min_le_left (η / 2) (1 / 4)],
        by linarith [hy.1, min_le_left (η / 2) (1 / 4)]⟩
    set s : ℂ := ((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I with hsdef
    have hss : s - (ρ - ε) = (e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hsdef, hre]
    have hnorm : ‖s - (ρ - ε)‖ < η := by
      rw [hss]
      calc ‖(e : ℂ) + ((y - ρ.im : ℝ) : ℂ) * I‖ ≤ ‖(e : ℂ)‖ + ‖((y - ρ.im : ℝ) : ℂ) * I‖ :=
            norm_add_le _ _
        _ = |e| + |y - ρ.im| := by
            simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
        _ < η := by rw [abs_of_pos he.1]; linarith
    have hne : s ≠ ρ - ε := fun h => by
      have := congrArg Complex.re (show s - (ρ - ε) = 0 by rw [h, sub_self])
      rw [hss] at this; simp at this; linarith [he.1]
    obtain ⟨hζ, hsε, -, -, hb⟩ := hp s hnorm hne
    have hsre : s.re = e + 1 / 2 := by simp [hsdef]
    have hΦ := complexMellinPairing_receiver_eq hε (by linarith) (hCκ e he.1) he.1.le (hEκ e he.1)
      (s := s) (by rw [hsre]; linarith [he.1]) (by rw [hsre]; linarith) hζ hsε
    have hline := lineSymbol_receiver_eq (hCκ e he.1) he.1.le (hEκ e he.1)
      (show e / 2 < e by linarith [he.1]) y
    rw [show logProfile v = receiverLogProfile ε from rfl, hline,
      show ((e + 1 / 2 : ℝ) : ℂ) + (y : ℂ) * I = s from rfl, hΦ, ← hss]
    exact hb
  have hsep : ∀ ρ ∈ Z, ∀ ρ' ∈ Z, ρ ≠ ρ' → ρ.im ≠ ρ'.im := fun ρ hρ ρ' hρ' hne h =>
    hne (Complex.ext (by rw [(hZ ρ hρ).2.2, (hZ ρ' hρ').2.2]) h)
  exact sum_residue_le_slope hv0 hK hvb hS0 hB' hlin Z hsep _ hpole

/-- **The boundary receiver energy grows at least at the shadow rate.** For `0 < ε < ½`, a finite
set `Z` of simple zeros on `Re ρ = ½ + ε` and any `S < Σ_{ρ ∈ Z} ‖ζ(ρ − ε)/(ζ′(ρ)(ρ − ε))‖²`, the
receiver energy is not bounded by `S log(T+1) + B`: `limsup E_ε(T)/log T` is at least the shadow
mass. -/
theorem not_forall_receiver_energy_le_log {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / 2) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, riemannZeta ρ = 0 ∧ deriv riemannZeta ρ ≠ 0 ∧ ρ.re = 1 / 2 + ε) {S B : ℝ}
    (hS : S < ∑ ρ ∈ Z, ‖riemannZeta (ρ - ε) / (deriv riemannZeta ρ * (ρ - ε))‖ ^ 2) :
    ¬ ∀ T : ℕ, dampedMobiusEnergy ε T ≤ S * Real.log ((T : ℝ) + 1) + B := by
  intro hE
  have hB0 : 0 ≤ B := by
    have h0 := hE 0
    rw [← receiver_energy_eq] at h0
    simpa using h0
  rcases lt_or_ge S 0 with hS0 | hS0
  · -- a negative slope contradicts `E_ε ≥ 0`
    set T := ⌈Real.exp (B / (-S) + 1)⌉₊
    have hT : B / (-S) + 1 ≤ Real.log ((T : ℝ) + 1) := by
      have hc : Real.exp (B / (-S) + 1) ≤ T := Nat.le_ceil _
      rw [Real.le_log_iff_exp_le (by positivity)]
      linarith
    have hnn : 0 ≤ dampedMobiusEnergy ε T := by
      rw [← receiver_energy_eq]; exact Finset.sum_nonneg fun n _ => by positivity
    have h1 := hE T
    have h2 : -S * (B / (-S) + 1) ≤ -S * Real.log ((T : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hT (by linarith)
    rw [mul_add, mul_div_cancel₀ _ (by linarith : -S ≠ 0)] at h2
    linarith
  · linarith [shadow_mass_le_slope hε hε1 Z hZ hS0 hB0 hE]

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
