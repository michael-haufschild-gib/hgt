import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeTailLimits
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeTailNorms
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeWindowScales
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargeComplementReceiver

/-!
# Physical receiving tails in exact conductor complements

The coprime product tail splits into the transported prime tail and a
vanishing base-mode term. Its norm stays bounded. Consequently projection
of the terminal test off a common growing conductor space preserves every
fixed-mode signed receiving limit.
-/

noncomputable section

open Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  CompletedArithmeticForms SelectiveMultiscaleArithmeticPositivity

/-- Physical coordinates of the prime tail transported by a fixed receiving mode. -/
def fibrePrimeTailVector (m Q N : ℕ) (t : ℝ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (Real.sqrt (Real.log N))⁻¹ • packetVector
    (fun n => normalizedRamanujanMode m n *
      completedPrimeDilationTail Q (fibreRestrict m (fibreCharge m Q t)) (N / n) n) N

/-- Physical coordinates of the complete arithmetic tail of the neutral fibre charge. -/
def fibreChargeTailVector (m Q N : ℕ) (t : ℝ) : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
  (Real.sqrt (Real.log N))⁻¹ • packetVector
    (fun n => completedPrimeDilationTail (m * Q)
      (harmonicFibreChargeCoefficients m Q N t) (N / n) n) N

/-- Harmonic centering preserves the exact product decomposition of the tail vector. -/
theorem fibreChargeTailVector_eq {m Q : ℕ} (hm : 0 < m) (hQ : 1 ≤ Q) (N : ℕ) (t : ℝ) :
    fibreChargeTailVector m Q N t = fibrePrimeTailVector m Q N t + fibreBaseTailVector m Q N t := by
  simp only [fibreChargeTailVector, completedPrimeDilationTail_harmonicFibreCharge hm hQ,
    packetVector_add, smul_add, fibrePrimeTailVector, fibreBaseTailVector, fibreBaseTailProfile]

private theorem physical_packet_norm_le {N : ℕ} (hL : 1 ≤ Real.log N)
    (F : ℕ → ℝ) {D : ℝ} (hD : 0 ≤ D) (hF : ∀ n, |F n| ≤ D) :
    ‖(Real.sqrt (Real.log N))⁻¹ • packetVector F N‖ ≤ 2 * D := by
  have hL0 : 0 < Real.log N := zero_lt_one.trans_le hL
  have hH : harmonicMass N ≤ 2 * Real.log N := by
    have h := harmonic_le_one_add_log N
    have he : (harmonic N : ℝ) = harmonicMass N := by
      simpa only [harmonicMass, one_div] using
        _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum N
    rw [he] at h
    linarith only [h, hL]
  have hmass : ‖packetVector F N‖ ^ 2 ≤ D ^ 2 * harmonicMass N := by
    rw [packetVector_norm_sq, harmonicMass, mul_sum]
    apply sum_le_sum
    intro n _
    have h := pow_le_pow_left₀ (abs_nonneg _) (hF n) 2
    rw [sq_abs] at h
    exact (div_le_div_of_nonneg_right h (Nat.cast_nonneg n)).trans_eq (by ring)
  have hsq : ‖(Real.sqrt (Real.log N))⁻¹ • packetVector F N‖ ^ 2 ≤ 2 * D ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow,
      Real.sq_sqrt (Real.log_natCast_nonneg N)]
    calc
      _ ≤ (Real.log N)⁻¹ * (D ^ 2 * harmonicMass N) :=
        mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr hL0.le)
      _ ≤ (Real.log N)⁻¹ * (D ^ 2 * (2 * Real.log N)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH (sq_nonneg D))
          (inv_nonneg.mpr hL0.le)
      _ = _ := by field_simp [hL0.ne']
  nlinarith only [hsq, hD, norm_nonneg ((Real.sqrt (Real.log N))⁻¹ • packetVector F N)]

/-- The physical transported prime tail stays bounded in each fixed receiving mode. -/
theorem eventually_fibrePrimeTailVector_norm_le {m : ℕ} (hm : 0 < m) (t : ℝ) :
    ∀ᶠ X : ℕ in atTop,
      ‖fibrePrimeTailVector m (X ^ 2) (X ^ 40) t‖ ≤ 2 * modeBound m * (|t| + 1) := by
  have hQ : Tendsto (fun X : ℕ => X ^ 2) atTop atTop := tendsto_pow_atTop (by omega)
  have hN : Tendsto (fun X : ℕ => X ^ 40) atTop atTop := tendsto_pow_atTop (by omega)
  have hB := (fibreScale_tendsto_atTop hm).comp hQ
  have hL := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hN
  have hlim := (((tendsto_primePoleScale_div_fibreScale hm).comp hQ).add
    (hB.const_div_atTop (8 + m : ℝ))).const_mul |t|
  simp only [Function.comp_apply, add_zero, mul_one] at hlim
  filter_upwards [eventually_ge_atTop 1, hB.eventually (eventually_ge_atTop 1),
    hL.eventually (eventually_ge_atTop 1),
    hlim.eventually (ge_mem_nhds (by linarith : |t| < |t| + 1))] with X hX hb hl hh
  change 1 ≤ fibreScale m (X ^ 2) at hb
  change 1 ≤ Real.log (X ^ 40 : ℕ) at hl
  have hB0 : 0 < fibreScale m (X ^ 2) := zero_lt_one.trans_le hb
  have htail (n : ℕ) :
      |completedPrimeDilationTail (X ^ 2) (fibreRestrict m (fibreCharge m (X ^ 2) t))
        (X ^ 40 / n) n| ≤ |t| + 1 := by
    have h := abs_fibreTail_le_activity hm (X ^ 2) (X ^ 40 / n) n t
    have ha := primeActivityMass_le_primePoleScale_add_eight (X ^ 2)
    refine h.trans ((mul_le_mul_of_nonneg_left
      (add_le_add_right ha (m : ℝ)) (abs_nonneg _)).trans ?_)
    rw [abs_div, abs_of_pos hB0]
    exact le_trans (le_of_eq (by ring)) hh
  have hm0 := (modeBound_pos hm).le
  have h := physical_packet_norm_le hl
    (fun n => normalizedRamanujanMode m n *
      completedPrimeDilationTail (X ^ 2) (fibreRestrict m (fibreCharge m (X ^ 2) t))
        (X ^ 40 / n) n)
    (mul_nonneg hm0 (by positivity : 0 ≤ |t| + 1)) (fun n => by
      rw [abs_mul]
      exact mul_le_mul (abs_le_periodSum hm (normalizedRamanujanMode_periodic hm) n)
        (htail n) (abs_nonneg _) hm0)
  exact h.trans_eq (by ring)

/-- The complete arithmetic tail also stays bounded after harmonic pole subtraction. -/
theorem eventually_fibreChargeTailVector_norm_le {m : ℕ} (hm : 0 < m) (t : ℝ) :
    ∀ᶠ X : ℕ in atTop,
      ‖fibreChargeTailVector m (X ^ 2) (X ^ 40) t‖ ≤ 2 * modeBound m * (|t| + 1) + 1 := by
  filter_upwards [eventually_ge_atTop 1, eventually_fibrePrimeTailVector_norm_le hm t,
    (tendsto_fibreBaseTailVector_norm hm (a := 2) (d := 40) (by omega) (by omega) t).eventually
      (ge_mem_nhds (by norm_num : (0 : ℝ) < 1))] with X hX hp hb
  rw [fibreChargeTailVector_eq hm (Nat.one_le_pow 2 X hX)]
  exact (norm_add_le _ _).trans (add_le_add hp hb)

/-- The transported vector's terminal pairing is the literal signed harmonic tail sum. -/
theorem fibrePrimeTailVector_inner_terminal (m l X : ℕ) (t : ℝ) :
    ⟪fibrePrimeTailVector m (X ^ 2) (X ^ 40) t,
      fibreChargeWindowVector l (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)⟫ =
        fibreTerminalPrimeTailPairing m l X t := by
  rw [fibrePrimeTailVector, fibreChargeWindowVector,
    real_inner_smul_left, real_inner_smul_right, packetVector_inner]
  have hs : (Real.sqrt (Real.log (X ^ 40 : ℕ)))⁻¹ *
      (Real.sqrt (Real.log (X ^ 40 : ℕ)))⁻¹ = (Real.log (X ^ 40 : ℕ))⁻¹ := by
    rw [← mul_inv, ← sq, Real.sq_sqrt (Real.log_natCast_nonneg _)]
  rw [← mul_assoc, hs]
  unfold fibreTerminalPrimeTailPairing
  rw [div_eq_mul_inv, mul_comm _ (Real.log (X ^ 40 : ℕ))⁻¹]
  congr 1
  exact sum_congr rfl fun n _ => by ring

/-- The base-mode tail contributes zero to every fixed terminal receiving mode. -/
theorem tendsto_fibreBaseTail_window_pairing {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      ⟪fibreBaseTailVector m (X ^ 2) (X ^ 40) t,
        fibreChargeWindowVector l (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)⟫) atTop (𝓝 0) := by
  have hn : Tendsto (fun X : ℕ =>
      ‖fibreChargeWindowVector l (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)‖)
      atTop (𝓝 (Real.sqrt (1 / 20 : ℝ))) := by
    simpa only [Real.sqrt_sq (norm_nonneg _)] using
      (tendsto_fibreChargeTerminal_window_norm_sq hl).sqrt
  have hlim := (tendsto_fibreBaseTailVector_norm hm
    (a := 2) (d := 40) (by omega) (by omega) t).mul hn
  simp only [zero_mul] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [] with X
  simpa only [Real.norm_eq_abs] using abs_real_inner_le_norm
    (fibreBaseTailVector m (X ^ 2) (X ^ 40) t)
    (fibreChargeWindowVector l (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40))

/-- Every fixed receiving fibre reads its own signed tail coefficient before projection. -/
theorem tendsto_fibreChargeTail_window_pairing {m l : ℕ}
    (hm : 0 < m) (hl : 0 < l) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      ⟪fibreChargeTailVector m (X ^ 2) (X ^ 40) t,
        fibreChargeWindowVector l (X ^ 38) (X ^ 39) (X ^ 40) (X ^ 40)⟫)
      atTop (𝓝 ((if m = l then 1 else 0) * (t / 80))) := by
  have h := (tendsto_fibreTerminalPrimeTailPairing hm hl t).add
    (tendsto_fibreBaseTail_window_pairing hm hl t)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [fibreChargeTailVector_eq hm (Nat.one_le_pow 2 X hX), inner_add_left,
    fibrePrimeTailVector_inner_terminal]

/-- Projection off any fixed multiple of the prime cutoff changes no limiting signed tail pairing. -/
theorem tendsto_fibreChargeTail_projection_pairing {m l R : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hR : 0 < R) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      ⟪fibreChargeTailVector m (X ^ 2) (X ^ 40) t,
        fibreChargeTerminalProjection l R X⟫)
      atTop (𝓝 0) := by
  have hlim := (tendsto_fibreChargeTerminal_projection_norm hl hR).const_mul
    (2 * modeBound m * (|t| + 1) + 1)
  simp only [mul_zero] at hlim
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_fibreChargeTailVector_norm_le hm t] with X hX
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right hX (norm_nonneg _))

/-- The exact growing conductor complement preserves the diagonal receiving law in every fixed fibre. -/
theorem tendsto_fibreChargeTail_terminalReceiver_pairing {m l R : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hR : 0 < R) (t : ℝ) :
    Tendsto (fun X : ℕ =>
      ⟪fibreChargeTailVector m (X ^ 2) (X ^ 40) t, fibreChargeTerminalReceiver l R X⟫)
      atTop (𝓝 ((if m = l then 1 else 0) * (t / 80))) := by
  simpa only [fibreChargeTerminalReceiver, fibreChargeWindowComplement,
    fibreChargeTerminalProjection, inner_sub_right, sub_zero] using
    (tendsto_fibreChargeTail_window_pairing hm hl t).sub
      (tendsto_fibreChargeTail_projection_pairing hm hl hR t)

#print axioms fibreChargeTailVector_eq
#print axioms tendsto_fibreChargeTail_terminalReceiver_pairing

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
