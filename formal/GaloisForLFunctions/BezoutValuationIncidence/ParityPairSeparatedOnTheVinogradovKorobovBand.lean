import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheVinogradovKorobovBand
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ParityPairAtHalfDamping
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusCovarianceCancellation

/-!
# The parity pair is separated on the Vinogradov–Korobov band

The damped Möbius weight `c_ε(d) = μ(d) d^{-ε}` and its parity twin `c'_ε` (nonnegative, supported on
squarefree moduli) have Ramanujan coefficients of equal absolute value, `|W_{c'}(e)| = |W_c(e)|`, so
every sign-blind datum of the two rows coincides: below half damping no such datum decides the
receiver.

On the Vinogradov–Korobov band `1/2 - κσ(T)/(480 log T) ≤ ε ≤ 1/2` (`ε ≥ 1/4`) the pair is separated
uniformly in the damping:

* `E_T(c_ε) ≤ E` (`exists_receiver_le_on_vinogradovKorobovBand`);
* `E_T(c'_ε) ≥ c (log(T+1) - log 100)` with one `c > 0`.

The second bound is the drift of the squarefree moduli beyond the prefix; its constant is made uniform
in `ε ∈ [1/4, 1/2]` through monotonicity of the Euler product `ρ_ε = ∏_p (1 - p^{-1-ε})` and of the
twin's local factors `1/(p^{1+ε} - 2)`. Since no sign-blind datum separates the pair, the bound on the
band reads the signs of `μ`: it is paid by the zero-free region of `1/ζ`.
-/

open Finset Filter Topology RHTower.Sieve
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Constants uniform in the damping -/

/-- The Euler product `ρ_ε = ∏_p (1 - p^{-1-ε})` increases with `ε`. -/
theorem dampedDensity_le_dampedDensity {ε ε' : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε') :
    dampedDensity ε ≤ dampedDensity ε' := by
  have h1 := RHTower.pmPowerDampedDivisorDensity_hasProd_real hε
  have h2 := RHTower.pmPowerDampedDivisorDensity_hasProd_real (lt_of_lt_of_le hε hεε')
  refine le_of_tendsto_of_tendsto' h1 h2 fun s => prod_le_prod (fun p _ => ?_) fun p _ => ?_
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_le
    have hp0 : (0 : ℝ) < p := by linarith
    have ht : (p : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
    exact sub_nonneg.mpr ((div_le_one hp0).mpr (by linarith))
  · have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_le
    have hp0 : (0 : ℝ) < p := by linarith
    have hle : (p : ℝ) ^ (-ε') ≤ (p : ℝ) ^ (-ε) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have := div_le_div_of_nonneg_right hle hp0.le
    linarith

/-- The twin's local factor `1/(p^{1+ε} - 2)` decreases with `ε`. -/
theorem parityTwinLocal_le_parityTwinLocal {ε ε' : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε') {p : ℕ}
    (hp : p.Prime) : parityTwinLocal ε' p ≤ parityTwinLocal ε p := by
  have h2 := two_lt_prime_rpow hε hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hle : (p : ℝ) ^ (1 + ε) ≤ (p : ℝ) ^ (1 + ε') :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  unfold parityTwinLocal
  exact one_div_le_one_div_of_le (by linarith) (by linarith)

theorem parityTwinShape_le_parityTwinShape {ε ε' : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε') (d : ℕ) :
    parityTwinShape ε' d ≤ parityTwinShape ε d := by
  unfold parityTwinShape
  split_ifs
  · exact prod_le_prod
      (fun p hp => (parityTwinLocal_pos (lt_of_lt_of_le hε hεε')
        (Nat.prime_of_mem_primeFactors hp)).le)
      fun p hp => parityTwinLocal_le_parityTwinLocal hε hεε' (Nat.prime_of_mem_primeFactors hp)
  · exact le_rfl

theorem parityTwinCoprimeMass_one_le {ε ε' : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε') :
    parityTwinCoprimeMass ε' 1 ≤ parityTwinCoprimeMass ε 1 := by
  rw [parityTwinCoprimeMass_one_eq_tsum, parityTwinCoprimeMass_one_eq_tsum]
  exact (summable_parityTwinShape (lt_of_lt_of_le hε hεε')).tsum_le_tsum
    (parityTwinShape_le_parityTwinShape hε hεε') (summable_parityTwinShape hε)

/-- The twin's drift constant at damping `1/4`, `K⋆ = ρ_{1/4}/U_{1/4}`. -/
def twinDriftConstant : ℝ := dampedDensity (1 / 4) / parityTwinCoprimeMass (1 / 4) 1

theorem twinDriftConstant_pos : 0 < twinDriftConstant :=
  div_pos (RHTower.pmPowerDampedDivisorDensity_re_pos (by norm_num))
    (parityTwinCoprimeMass_one_pos (by norm_num))

theorem twinDriftConstant_le {ε : ℝ} (hε : 1 / 4 ≤ ε) :
    twinDriftConstant ≤ dampedDensity ε / parityTwinCoprimeMass ε 1 := by
  have h4 : (0 : ℝ) < 1 / 4 := by norm_num
  unfold twinDriftConstant
  exact div_le_div₀ (RHTower.pmPowerDampedDivisorDensity_re_pos (by linarith)).le
    (dampedDensity_le_dampedDensity h4 hε) (parityTwinCoprimeMass_one_pos (by linarith))
    (parityTwinCoprimeMass_one_le h4 hε)

/-! ## §2. The twin's receiver grows logarithmically, uniformly in the damping -/

theorem log_add_one_sub_log_le_inv {n : ℕ} (hn : 1 ≤ n) :
    Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.log_div (by positivity) hn0.ne', add_div, div_self hn0.ne']
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + 1 / n by positivity)
  linarith

/-- `log(T+1) - log a ≤ Σ_{a ≤ n ≤ T} 1/n` for `1 ≤ a ≤ T + 1`. -/
theorem log_sub_log_le_sum_Icc_inv {a : ℕ} (ha : 1 ≤ a) {T : ℕ} (haT : a ≤ T + 1) :
    Real.log ((T : ℝ) + 1) - Real.log a ≤ ∑ n ∈ Icc a T, (1 : ℝ) / n := by
  induction T, (show a - 1 ≤ T by omega) using Nat.le_induction with
  | base =>
    have : ((a - 1 : ℕ) : ℝ) + 1 = a := by rw [Nat.cast_sub ha]; push_cast; ring
    rw [this, sub_self, Icc_eq_empty (by omega), sum_empty]
  | succ T hT ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have h1 := ih (by omega)
    have h2 := log_add_one_sub_log_le_inv (n := T + 1) (by omega)
    push_cast at h2 ⊢
    linarith

/-- **The twin's receiver on `[1/4, 1/2]`.** With `K⋆ = ρ_{1/4}/U_{1/4}`,
`(K⋆/16)²/4 · (log(T+1) - log 100) ≤ E_T(c'_ε)` for every `T` and every `ε ∈ [1/4, 1/2]`. -/
theorem parityTwin_receiver_ge {ε : ℝ} (hε4 : 1 / 4 ≤ ε) (hε2 : ε ≤ 1 / 2) (T : ℕ) :
    (twinDriftConstant / 16) ^ 2 / 4 * (Real.log ((T : ℝ) + 1) - Real.log 100) ≤
      weightPronicEnergy (parityTwinWeight ε) (dampedDensity ε) T := by
  have hε : 0 < ε := by linarith
  set c := (twinDriftConstant / 16) ^ 2 / 4 with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hK0 := twinDriftConstant_pos
  have hcell : ∀ n : ℕ, 100 ≤ n → c * (1 / (n : ℝ)) ≤
      weightCenteredPrefix (parityTwinWeight ε) (dampedDensity ε) n ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro n hn
    have hdrift : twinDriftConstant / 16 * n * (2 * (n : ℝ)) ^ (-ε) ≤
        (n : ℝ) * ∑ d ∈ Ioc n (2 * n), parityTwinWeight ε d / d := by
      refine le_trans ?_ (parityTwin_drift_ge hε hn)
      have hK := twinDriftConstant_le hε4
      have hP : 0 ≤ (n : ℝ) * (2 * (n : ℝ)) ^ (-ε) :=
        mul_nonneg (Nat.cast_nonneg n) (Real.rpow_nonneg (by positivity) _)
      nlinarith
    have h := weightCell_ge_of_drift (parityTwinWeight_nonneg hε) (hasSum_parityTwinWeight_div hε)
      (by positivity) hε2 (by omega) hdrift
    rw [hcdef]
    calc (twinDriftConstant / 16) ^ 2 / 4 * (1 / (n : ℝ)) =
        (twinDriftConstant / 16) ^ 2 / 4 / n := by ring
      _ ≤ _ := h
  rw [weightPronicEnergy]
  rcases lt_or_ge T 99 with hT | hT
  · have hlog : Real.log ((T : ℝ) + 1) ≤ Real.log 100 :=
      Real.log_le_log (by positivity) (by have : (T : ℝ) ≤ 98 := by exact_mod_cast (by omega : T ≤ 98)
                                          linarith)
    have hnn : 0 ≤ ∑ n ∈ Icc 1 T, weightCenteredPrefix (parityTwinWeight ε) (dampedDensity ε) n ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) := sum_nonneg fun n _ => by positivity
    nlinarith
  · have hsub : Icc 100 T ⊆ Icc 1 T := Icc_subset_Icc (by norm_num) le_rfl
    have hlog := log_sub_log_le_sum_Icc_inv (a := 100) (by norm_num) (T := T) (by omega)
    push_cast at hlog
    calc c * (Real.log ((T : ℝ) + 1) - Real.log 100) ≤ c * ∑ n ∈ Icc 100 T, (1 : ℝ) / n :=
          mul_le_mul_of_nonneg_left hlog hc0
      _ = ∑ n ∈ Icc 100 T, c * (1 / (n : ℝ)) := by rw [mul_sum]
      _ ≤ ∑ n ∈ Icc 100 T, weightCenteredPrefix (parityTwinWeight ε) (dampedDensity ε) n ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1)) :=
          sum_le_sum fun n hn => hcell n (mem_Icc.mp hn).1
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity

/-! ## §3. The pair -/

/-- **The parity pair is separated on the Vinogradov–Korobov band.** The damped Möbius weight and its
parity twin have Ramanujan coefficients of equal absolute value at every damping, and there are
`E` and `c > 0` such that for every horizon `T` and every damping on the band
`1/4 ≤ ε ≤ 1/2`, `ε ≥ 1/2 - κσ(T)/(480 log T)`:
`E_T(c_ε) ≤ E` while `E_T(c'_ε) ≥ c (log(T+1) - log 100)`. -/
theorem parityPair_separated_on_vinogradovKorobovBand :
    (∀ ε : ℝ, 0 < ε → ∀ e : ℕ, 0 < e →
      |weightRamanujanCoeff (parityTwinWeight ε) e| =
        |weightRamanujanCoeff (pmPowerDampedRealWeight ε) e|) ∧
    ∃ E c : ℝ, 0 < c ∧ ∀ (T : ℕ) (ε : ℝ), 1 / 4 ≤ ε → ε ≤ 1 / 2 →
      1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ ε →
        weightPronicEnergy (pmPowerDampedRealWeight ε) (dampedDensity ε) T ≤ E ∧
        c * (Real.log ((T : ℝ) + 1) - Real.log 100) ≤
          weightPronicEnergy (parityTwinWeight ε) (dampedDensity ε) T := by
  refine ⟨fun ε hε e he => abs_weightRamanujanCoeff_parityTwin hε he, ?_⟩
  obtain ⟨E, hE⟩ := exists_receiver_le_on_vinogradovKorobovBand
  refine ⟨E, (twinDriftConstant / 16) ^ 2 / 4, by have := twinDriftConstant_pos; positivity,
    fun T ε h4 h2 hb => ⟨?_, parityTwin_receiver_ge h4 h2 T⟩⟩
  rw [weightPronicEnergy_pmPowerDamped]
  exact hE T ε h4 h2 hb

end

end GaloisForLFunctions.BezoutValuationIncidence
