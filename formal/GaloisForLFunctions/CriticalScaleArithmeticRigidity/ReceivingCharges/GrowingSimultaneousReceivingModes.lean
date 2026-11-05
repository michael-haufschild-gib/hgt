import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.SimultaneousCompleteReceivingLaw

/-!
# Uniform simultaneous receiving on growing mode sets

Finite basis and polarized energy bounds control every bounded charge vector.
A monotone diagonal cutoff makes the mode set grow while retaining exact
harmonic neutrality and the complete signed receiving law.
-/

noncomputable section
open Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity

open ArithmeticCouplingTheory RenormalizedArithmeticPotentialTheory
  SelectiveMultiscaleArithmeticPositivity SpacingScaleHarmonicAnalysis CompletedArithmeticForms
  ArithmeticIntersectionTheory

private def receivingUnit (m n : ℕ) : ℝ := if n = m then 1 else 0

private def receivingBasis (R X m : ℕ) : EuclideanSpace ℝ (PrimeHorizonIndex (X ^ 40)) :=
  commonPrimeFibreChargeVector m R.factorial (X ^ 2) (X ^ 40) 1

private def receivingSynthesis (R X : ℕ) (t : ℕ → ℝ) :
    EuclideanSpace ℝ (PrimeHorizonIndex (X ^ 40)) :=
  ∑ m ∈ Icc 1 R, t m • receivingBasis R X m

private theorem receiving_modes (R : ℕ) {m : ℕ} (hm : m ∈ Icc 1 R) :
    0 < m ∧ m ∣ R.factorial :=
  ⟨(mem_Icc.mp hm).1, Nat.dvd_factorial (mem_Icc.mp hm).1 (mem_Icc.mp hm).2⟩

/-- The common-exclusion fibre depends linearly on its prescribed charge. -/
theorem commonPrimeFibreChargeVector_smul (m M Q N : ℕ) (t : ℝ) :
    commonPrimeFibreChargeVector m M Q N t =
      t • commonPrimeFibreChargeVector m M Q N 1 := by
  have hpoint (n : ℕ) : normalizedRamanujanMode m n *
      incidencePacket (fibrePrimes M Q) (fun _ => t / fibreScale M Q) n =
      t * (normalizedRamanujanMode m n *
        incidencePacket (fibrePrimes M Q) (fun _ => 1 / fibreScale M Q) n) := by
    simp only [incidencePacket, mul_sum]
    apply sum_congr rfl
    intro p _
    ring
  simp only [commonPrimeFibreChargeVector, hpoint, harmonicCenteredPacketVector_smul]

private theorem packet_eq_receivingSynthesis (R : ℕ) {X : ℕ} (hX : 1 ≤ X) (t : ℕ → ℝ) :
    simultaneousReceivingPacket R X t = receivingSynthesis R X t := by
  rw [simultaneousReceivingPacket, commonPrimeFibreVector_eq_sum (Nat.factorial_pos R)
    (Nat.one_le_pow 2 X hX) (Icc 1 R) (fun m hm => receiving_modes R hm)]
  exact sum_congr rfl fun m _ => commonPrimeFibreChargeVector_smul m _ _ _ (t m)

private theorem receivingSynthesis_unit (R X : ℕ) {m : ℕ} (hm : m ∈ Icc 1 R) :
    receivingSynthesis R X (receivingUnit m) = receivingBasis R X m := by
  simp only [receivingSynthesis, receivingUnit, ite_smul, one_smul, zero_smul,
    sum_ite_eq', if_pos hm]

private theorem receivingSynthesis_add (R X : ℕ) (s t : ℕ → ℝ) :
    receivingSynthesis R X (fun m => s m + t m) =
      receivingSynthesis R X s + receivingSynthesis R X t := by
  simp only [receivingSynthesis, add_smul, sum_add_distrib]

private def receivingOperator (K : ℝ) (X : ℕ) :=
  Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline
    (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40))

private def receivingGram (K : ℝ) (R X m n : ℕ) : ℝ :=
  ⟪receivingOperator K X (receivingBasis R X m), receivingBasis R X n⟫

private theorem tendsto_receivingSynthesis_energy {K : ℝ} (hK : 0 < K)
    (R : ℕ) (t : ℕ → ℝ) :
    Tendsto (fun X : ℕ => ⟪receivingOperator K X (receivingSynthesis R X t),
      receivingSynthesis R X t⟫) atTop (𝓝 0) := by
  apply (tendsto_simultaneousReceiving_complete_energy hK R t).congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [packet_eq_receivingSynthesis R hX]
  rfl

private theorem tendsto_receivingBasis_norm (R : ℕ) {m : ℕ} (hm : m ∈ Icc 1 R) :
    Tendsto (fun X : ℕ => ‖receivingBasis R X m‖) atTop (𝓝 0) := by
  have hs : Tendsto (fun X : ℕ => ‖receivingBasis R X m‖ ^ 2) atTop (𝓝 0) := by
    apply (tendsto_simultaneousReceiving_input_sq R (receivingUnit m)).congr'
    filter_upwards [eventually_ge_atTop 1] with X hX
    rw [packet_eq_receivingSynthesis R hX, receivingSynthesis_unit R X hm]
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

private theorem tendsto_receivingGram {K : ℝ} (hK : 0 < K) (R : ℕ)
    {m n : ℕ} (hm : m ∈ Icc 1 R) (hn : n ∈ Icc 1 R) :
    Tendsto (fun X : ℕ => receivingGram K R X m n) atTop (𝓝 0) := by
  have hp := tendsto_receivingSynthesis_energy hK R
    (fun j => receivingUnit m j + receivingUnit n j)
  have hm' := tendsto_receivingSynthesis_energy hK R (receivingUnit m)
  have hn' := tendsto_receivingSynthesis_energy hK R (receivingUnit n)
  have hlim := ((hp.sub hm').sub hn').div_const 2
  simp only [sub_zero, zero_div] at hlim
  apply hlim.congr
  intro X
  rw [receivingSynthesis_add, receivingSynthesis_unit R X hm,
    receivingSynthesis_unit R X hn]
  have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (completeWeilMatrix_isHermitian tiltedUnitSpline
      (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ)) (X ^ 40)))
      (receivingBasis R X n) (receivingBasis R X m)
  change ⟪receivingOperator K X (receivingBasis R X n), receivingBasis R X m⟫ =
    ⟪receivingBasis R X n, receivingOperator K X (receivingBasis R X m)⟫ at hsym
  rw [← real_inner_comm (receivingBasis R X n)
    (receivingOperator K X (receivingBasis R X m))] at hsym
  simp only [map_add, inner_add_left, inner_add_right]
  rw [hsym]
  unfold receivingGram
  ring

private def receivingPairingError (K : ℝ) (R X m l : ℕ) : ℝ :=
  ⟪receivingOperator K X (receivingBasis R X m),
    fibreChargeTerminalReceiver l R.factorial X⟫ - if m = l then 1 / 80 else 0

private theorem tendsto_receivingPairingError {K : ℝ} (hK : 0 < K) (R : ℕ)
    {m l : ℕ} (hm : m ∈ Icc 1 R) (hl : l ∈ Icc 1 R) :
    Tendsto (fun X : ℕ => receivingPairingError K R X m l) atTop (𝓝 0) := by
  let l' : ℕ+ := ⟨l, (mem_Icc.mp hl).1⟩
  have h := (tendsto_simultaneousReceiving_signed_pairing hK R (receivingUnit m) l').sub_const
    (if m = l then (1 / 80 : ℝ) else 0)
  have he : (if (l' : ℕ) ≤ R then receivingUnit m l' / 80 else 0) =
      if m = l then (1 / 80 : ℝ) else 0 := by
    change (if l ≤ R then (if l = m then (1 : ℝ) else 0) / 80 else 0) = _
    rw [if_pos (mem_Icc.mp hl).2]
    by_cases hml : m = l
    · subst m
      simp only [ite_true]
    · rw [if_neg hml, if_neg (Ne.symm hml), zero_div]
  rw [he, sub_self] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  rw [packet_eq_receivingSynthesis R hX, receivingSynthesis_unit R X hm]
  rfl

private def receivingAdjunctionBound (R X : ℕ) : ℝ :=
  ((Icc 1 R).card : ℝ) *
    (∑ m ∈ Icc 1 R, (2 * (Real.log m + tameDifferent m) + 1)) /
      fibreScale R.factorial (X ^ 2)

/-- A charge-independent bound formed from finite basis and receiver errors. -/
def simultaneousReceivingError (K : ℝ) (R X : ℕ) : ℝ :=
  |receivingAdjunctionBound R X| + (∑ m ∈ Icc 1 R, ‖receivingBasis R X m‖) ^ 2 +
    (∑ m ∈ Icc 1 R, ∑ n ∈ Icc 1 R, |receivingGram K R X m n|) +
    (∑ l ∈ Icc 1 R, ∑ m ∈ Icc 1 R, |receivingPairingError K R X m l|) +
    ∑ l ∈ Icc 1 R, |‖fibreChargeTerminalReceiver l R.factorial X‖ ^ 2 - 1 / 20|

/-- Every finite mode set admits one error bound tending to zero for all bounded charges. -/
theorem tendsto_simultaneousReceivingError {K : ℝ} (hK : 0 < K) (R : ℕ) :
    Tendsto (simultaneousReceivingError K R) atTop (𝓝 0) := by
  have hX : Tendsto (fun X : ℕ => X ^ 2) atTop atTop := tendsto_pow_atTop (by omega)
  have ha := (((fibreScale_tendsto_atTop (Nat.factorial_pos R)).comp hX).const_div_atTop
    (((Icc 1 R).card : ℝ) * ∑ m ∈ Icc 1 R, (2 * (Real.log m + tameDifferent m) + 1))).abs
  have hi := (tendsto_finsetSum (Icc 1 R) (fun m hm => tendsto_receivingBasis_norm R hm)).pow 2
  have he := tendsto_finsetSum (Icc 1 R) fun m hm =>
    tendsto_finsetSum (Icc 1 R) fun n hn => (tendsto_receivingGram hK R hm hn).abs
  have hp := tendsto_finsetSum (Icc 1 R) fun l hl =>
    tendsto_finsetSum (Icc 1 R) fun m hm => (tendsto_receivingPairingError hK R hm hl).abs
  have hr := tendsto_finsetSum (Icc 1 R) fun l hl =>
    ((tendsto_fibreChargeTerminalReceiver_norm_sq (mem_Icc.mp hl).1
      (Nat.factorial_pos R)).sub_const (1 / 20 : ℝ)).abs
  change Tendsto (fun X => simultaneousReceivingError K R X) atTop (𝓝 0)
  simpa only [simultaneousReceivingError, receivingAdjunctionBound, sum_const_zero,
    Function.comp_apply, abs_zero, zero_pow two_ne_zero, add_zero, sub_self] using
      (((ha.add hi).add he).add hp).add hr

private theorem abs_sum_mul_le {ι : Type*} (S : Finset ι) (c f : ι → ℝ)
    (hc : ∀ i ∈ S, |c i| ≤ 1) : |∑ i ∈ S, c i * f i| ≤ ∑ i ∈ S, |f i| := by
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (hc i hi) (abs_nonneg _)).trans_eq (one_mul _)

private theorem receivingSynthesis_norm_sq_le (R X : ℕ) (t : ℕ → ℝ)
    (ht : ∀ m ∈ Icc 1 R, |t m| ≤ 1) :
    ‖receivingSynthesis R X t‖ ^ 2 ≤ (∑ m ∈ Icc 1 R, ‖receivingBasis R X m‖) ^ 2 := by
  have hh : ‖receivingSynthesis R X t‖ ≤ ∑ m ∈ Icc 1 R, ‖receivingBasis R X m‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun m hm => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (ht m hm) (norm_nonneg _)).trans_eq (one_mul _)
  exact pow_le_pow_left₀ (norm_nonneg _) hh 2

private theorem receivingSynthesis_energy_le (K : ℝ) (R X : ℕ) (t : ℕ → ℝ)
    (ht : ∀ m ∈ Icc 1 R, |t m| ≤ 1) :
    |⟪receivingOperator K X (receivingSynthesis R X t), receivingSynthesis R X t⟫| ≤
      ∑ m ∈ Icc 1 R, ∑ n ∈ Icc 1 R, |receivingGram K R X m n| := by
  have he : ⟪receivingOperator K X (receivingSynthesis R X t), receivingSynthesis R X t⟫ =
      ∑ m ∈ Icc 1 R, t m * ∑ n ∈ Icc 1 R, t n * receivingGram K R X m n := by
    simp only [receivingSynthesis, map_sum, sum_inner, inner_sum, map_smul,
      real_inner_smul_left, real_inner_smul_right, mul_sum, receivingGram]
    conv_lhs => rw [sum_comm]
    exact sum_congr rfl fun m _ => sum_congr rfl fun n _ => by ring
  rw [he]
  exact (abs_sum_mul_le _ _ _ ht).trans
    (sum_le_sum fun m _ => abs_sum_mul_le _ _ _ ht)

private theorem receivingSynthesis_pairing_error_le (K : ℝ) (R X : ℕ) (t : ℕ → ℝ)
    (ht : ∀ m ∈ Icc 1 R, |t m| ≤ 1) {l : ℕ} (hl : l ∈ Icc 1 R) :
    |⟪receivingOperator K X (receivingSynthesis R X t),
      fibreChargeTerminalReceiver l R.factorial X⟫ - t l / 80| ≤
        ∑ j ∈ Icc 1 R, ∑ m ∈ Icc 1 R, |receivingPairingError K R X m j| := by
  have he : ⟪receivingOperator K X (receivingSynthesis R X t),
      fibreChargeTerminalReceiver l R.factorial X⟫ - t l / 80 =
      ∑ m ∈ Icc 1 R, t m * receivingPairingError K R X m l := by
    simp only [receivingSynthesis, map_sum, sum_inner, map_smul,
      real_inner_smul_left, receivingPairingError, mul_sub, sum_sub_distrib,
      mul_ite, mul_zero, sum_ite_eq', if_pos hl]
    ring
  rw [he]
  exact (abs_sum_mul_le _ _ _ ht).trans
    (single_le_sum (fun j _ => sum_nonneg fun m _ =>
      abs_nonneg (receivingPairingError K R X m j)) hl)

private theorem simultaneousReceiving_adjunction_le (R X : ℕ) (t : ℕ → ℝ)
    (ht : ∀ m ∈ Icc 1 R, |t m| ≤ 1) (hb : 0 < fibreScale R.factorial (X ^ 2)) :
    primeAdjunctionMass (R.factorial * X ^ 2) (simultaneousReceivingCoefficients R X t) ≤
      |receivingAdjunctionBound R X| := by
  have hh := commonPrimeFibre_adjunction_le (Nat.factorial_pos R) (Icc 1 R)
    (fun m hm => receiving_modes R hm) (X ^ 40) t hb
  have hsum : (∑ m ∈ Icc 1 R, (2 * (Real.log m + tameDifferent m) + 1) * t m ^ 2) ≤
      ∑ m ∈ Icc 1 R, (2 * (Real.log m + tameDifferent m) + 1) := by
    apply sum_le_sum
    intro m hm
    have ht2 : t m ^ 2 ≤ 1 := by
      nlinarith only [ht m hm, abs_nonneg (t m), sq_abs (t m)]
    have hw : 0 ≤ 2 * (Real.log m + tameDifferent m) + 1 := by
      have hl := Real.log_natCast_nonneg m
      have hd := tameDifferent_nonneg m
      linarith only [hl, hd]
    exact (mul_le_mul_of_nonneg_left ht2 hw).trans_eq (mul_one _)
  exact hh.trans ((div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)) hb.le).trans (le_abs_self _))

private theorem receivingError_parts (K : ℝ) (R X : ℕ) :
    |receivingAdjunctionBound R X| ≤ simultaneousReceivingError K R X ∧
    (∑ m ∈ Icc 1 R, ‖receivingBasis R X m‖) ^ 2 ≤ simultaneousReceivingError K R X ∧
    (∑ m ∈ Icc 1 R, ∑ n ∈ Icc 1 R, |receivingGram K R X m n|) ≤
      simultaneousReceivingError K R X ∧
    (∑ l ∈ Icc 1 R, ∑ m ∈ Icc 1 R, |receivingPairingError K R X m l|) ≤
      simultaneousReceivingError K R X ∧
    (∑ l ∈ Icc 1 R, |‖fibreChargeTerminalReceiver l R.factorial X‖ ^ 2 - 1 / 20|) ≤
      simultaneousReceivingError K R X := by
  have hA := abs_nonneg (receivingAdjunctionBound R X)
  have hI := sq_nonneg (∑ m ∈ Icc 1 R, ‖receivingBasis R X m‖)
  have hE : 0 ≤ ∑ m ∈ Icc 1 R, ∑ n ∈ Icc 1 R, |receivingGram K R X m n| :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  have hP : 0 ≤ ∑ l ∈ Icc 1 R, ∑ m ∈ Icc 1 R, |receivingPairingError K R X m l| :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  have hR : 0 ≤ ∑ l ∈ Icc 1 R,
      |‖fibreChargeTerminalReceiver l R.factorial X‖ ^ 2 - 1 / 20| :=
    sum_nonneg fun _ _ => abs_nonneg _
  dsimp only [simultaneousReceivingError]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> linarith only [hA, hI, hE, hP, hR]

/-- Exact arithmetic coordinates and quantitative errors for a prescribed charge vector. -/
def ReceivingChargeControl (K : ℝ) (R X : ℕ) (t : ℕ → ℝ) (ε : ℝ) : Prop :=
    harmonicSum (X ^ 40) (conductorHorizonProfile (R.factorial * X ^ 2)
      (simultaneousReceivingCoefficients R X t)) = 0 ∧
    (∀ m ∈ Icc 1 R, packetMean (R.factorial * X ^ 2) (fun n =>
      arithmeticPrimeGenerator (R.factorial * X ^ 2)
        (simultaneousReceivingCoefficients R X t) n * normalizedRamanujanMode m n) = t m) ∧
    primeAdjunctionMass (R.factorial * X ^ 2) (simultaneousReceivingCoefficients R X t) ≤ ε ∧
    ‖simultaneousReceivingPacket R X t‖ ^ 2 ≤ ε ∧
    |completeWeilEnergy tiltedUnitSpline (2 * K * Real.log (X ^ 40 : ℕ) ^ (1 / 8 : ℝ))
      (X ^ 40) (simultaneousReceivingPacket R X t)| ≤ ε ∧
    ∀ l ∈ Icc 1 R, |⟪receivingOperator K X (simultaneousReceivingPacket R X t),
      fibreChargeTerminalReceiver l R.factorial X⟫ - t l / 80| ≤ ε

/-- Uniform receiving on the unit charge cube. The conductor cutoff stays below `X³`,
whereas the physical horizon is `X⁴⁰`. -/
def SimultaneousReceivingControl (K : ℝ) (R X : ℕ) (ε : ℝ) : Prop :=
  R.factorial ≤ X ∧
  (∀ t : ℕ → ℝ, (∀ m ∈ Icc 1 R, |t m| ≤ 1) → ReceivingChargeControl K R X t ε) ∧
  ∀ l ∈ Icc 1 R,
    fibreChargeTerminalReceiver l R.factorial X ∈
      (conductorSubspace (R.factorial * X ^ 2) (X ^ 40))ᗮ ∧
    |‖fibreChargeTerminalReceiver l R.factorial X‖ ^ 2 - 1 / 20| ≤ ε

/-- Receiving control for an arbitrary prescribed profile, without a bound on its charges. -/
def PrescribedReceivingControl (K : ℝ) (R X : ℕ) (t : ℕ → ℝ) (ε : ℝ) : Prop :=
  R.factorial ≤ X ∧ ReceivingChargeControl K R X t ε ∧
  ∀ l ∈ Icc 1 R,
    fibreChargeTerminalReceiver l R.factorial X ∈
      (conductorSubspace (R.factorial * X ^ 2) (X ^ 40))ᗮ ∧
    |‖fibreChargeTerminalReceiver l R.factorial X‖ ^ 2 - 1 / 20| ≤ ε

/-- Finite-mode convergence is uniform over every charge vector in the unit cube. -/
theorem eventually_simultaneousReceivingControl {K : ℝ} (hK : 0 < K)
    (R : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, SimultaneousReceivingControl K R X ε := by
  have hX2 : Tendsto (fun X : ℕ => X ^ 2) atTop atTop := tendsto_pow_atTop (by omega)
  have hb := ((fibreScale_tendsto_atTop (Nat.factorial_pos R)).comp hX2).eventually_gt_atTop 0
  have he := (tendsto_simultaneousReceivingError hK R).eventually (ge_mem_nhds hε)
  filter_upwards [eventually_ge_atTop R.factorial, hb, he] with X hX hB hE
  have hX1 : 1 ≤ X := (Nat.factorial_pos R).trans_le hX
  obtain ⟨hA, hI, hG, hP, hR⟩ := receivingError_parts K R X
  refine ⟨hX, ?_, ?_⟩
  · intro t ht
    refine ⟨commonPrimeFibre_neutral (Nat.factorial_pos R) (Nat.one_le_pow 2 X hX1)
      (Nat.one_le_pow 40 X hX1) (Icc 1 R) t, ?_,
      (simultaneousReceiving_adjunction_le R X t ht hB).trans (hA.trans hE), ?_, ?_, ?_⟩
    · intro m hm
      simpa only [simultaneousReceivingCoefficients, if_pos hm] using
        commonPrimeFibre_receiving_coordinates (Nat.factorial_pos R)
          (receiving_modes R hm).1 (receiving_modes R hm).2 (Icc 1 R)
          (fun n hn => receiving_modes R hn) (X ^ 40) t hB
    · rw [packet_eq_receivingSynthesis R hX1]
      exact (receivingSynthesis_norm_sq_le R X t ht).trans (hI.trans hE)
    · rw [packet_eq_receivingSynthesis R hX1]
      exact (receivingSynthesis_energy_le K R X t ht).trans (hG.trans hE)
    · intro l hl
      rw [packet_eq_receivingSynthesis R hX1]
      exact (receivingSynthesis_pairing_error_le K R X t ht hl).trans (hP.trans hE)
  · intro l hl
    exact ⟨fibreChargeTerminalReceiver_mem l R.factorial X,
      (single_le_sum (fun j _ => abs_nonneg _) hl).trans (hR.trans hE)⟩

-- Taking the largest admissible finite cutoff produces a monotone, cofinal schedule.
private theorem exists_growing_receiving_diagonal {P : ℕ → ℕ → Prop}
    (hP : ∀ R, ∀ᶠ X : ℕ in atTop, P R X) :
    ∃ r : ℕ → ℕ, Monotone r ∧ Tendsto r atTop atTop ∧ ∀ᶠ X : ℕ in atTop, P (r X) X := by
  have hthreshold : ∀ R : ℕ, ∃ T : ℕ, ∀ X, T ≤ X →
      P R X := fun R => eventually_atTop.mp (hP R)
  choose T hT using hthreshold
  let Q (X R : ℕ) : Prop := R = 0 ∨ T R + R ≤ X
  let r (X : ℕ) := Nat.findGreatest (Q X) X
  have hspec (X : ℕ) : Q X (r X) :=
    Nat.findGreatest_spec (P := Q X) (Nat.zero_le X) (Or.inl rfl)
  have hmono : Monotone r := by
    intro X Y hXY
    apply Nat.le_findGreatest ((Nat.findGreatest_le (P := Q X) X).trans hXY)
    rcases hspec X with hz | hh
    · exact Or.inl hz
    · exact Or.inr (hh.trans hXY)
  have htop : Tendsto r atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun R => ⟨T R + R, fun X hX => ?_⟩
    exact Nat.le_findGreatest (by omega) (Or.inr hX)
  refine ⟨r, hmono, htop, ?_⟩
  filter_upwards [eventually_ge_atTop (T 0)] with X hX
  rcases hspec X with hz | hh
  · rw [hz]
    exact hT 0 X hX
  · exact hT (r X) X (by omega)

/-- One monotone growing mode cutoff works uniformly for every bounded charge vector.
The error is at most `1/(R(X)+1)` and the exact conductor complement is retained. -/
theorem exists_growing_simultaneousReceivingControl {K : ℝ} (hK : 0 < K) :
    ∃ R : ℕ → ℕ, Monotone R ∧ Tendsto R atTop atTop ∧
      ∀ᶠ X : ℕ in atTop,
        SimultaneousReceivingControl K (R X) X (1 / ((R X : ℝ) + 1)) :=
  exists_growing_receiving_diagonal fun R =>
    eventually_simultaneousReceivingControl hK R
      (by positivity : 0 < 1 / ((R : ℝ) + 1))

/-- The growing cutoff yields uniform errors below every positive tolerance. -/
theorem exists_growing_simultaneousReceiving_vanishing {K : ℝ} (hK : 0 < K) :
    ∃ R : ℕ → ℕ, Monotone R ∧ Tendsto R atTop atTop ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop, SimultaneousReceivingControl K (R X) X ε := by
  obtain ⟨R, hmono, htop, hcontrol⟩ := exists_growing_simultaneousReceivingControl hK
  refine ⟨R, hmono, htop, fun ε hε => ?_⟩
  have hsmall := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp htop
  filter_upwards [hcontrol, hsmall.eventually (ge_mem_nhds hε)] with X hc he
  refine ⟨hc.1, ?_, ?_⟩
  · intro t ht
    obtain ⟨hn, hcoord, ha, hi, hw, hp⟩ := hc.2.1 t ht
    exact ⟨hn, hcoord, ha.trans he, hi.trans he, hw.trans he,
      fun l hl => (hp l hl).trans he⟩
  · intro l hl
    exact ⟨(hc.2.2 l hl).1, (hc.2.2 l hl).2.trans he⟩

/-- Every fixed finite part of an arbitrary charge profile has simultaneous receiving control. -/
theorem eventually_prescribedReceivingControl {K : ℝ} (hK : 0 < K)
    (R : ℕ) (t : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ X : ℕ in atTop, PrescribedReceivingControl K R X t ε := by
  have ha := (tendsto_simultaneousReceiving_adjunction R t).eventually (ge_mem_nhds hε)
  have hi := (tendsto_simultaneousReceiving_input_sq R t).eventually (ge_mem_nhds hε)
  have hw := (tendsto_simultaneousReceiving_complete_energy hK R t).abs.eventually
    (by simpa only [abs_zero] using ge_mem_nhds hε)
  have hp : ∀ᶠ X : ℕ in atTop, ∀ l : {l : ℕ // l ∈ Icc 1 R},
      |⟪receivingOperator K X (simultaneousReceivingPacket R X t),
        fibreChargeTerminalReceiver l.val R.factorial X⟫ - t l.val / 80| ≤ ε := by
    rw [Filter.eventually_all]
    intro l
    let l' : ℕ+ := ⟨l.val, (mem_Icc.mp l.property).1⟩
    have hl : (l' : ℕ) ≤ R := (mem_Icc.mp l.property).2
    have hlval : (l' : ℕ) = l.val := rfl
    have h := (tendsto_simultaneousReceiving_signed_pairing hK R t l').sub_const (t l.val / 80)
    rw [if_pos hl, hlval, sub_self] at h
    exact h.abs.eventually (by simpa only [abs_zero] using ge_mem_nhds hε)
  have hr : ∀ᶠ X : ℕ in atTop, ∀ l : {l : ℕ // l ∈ Icc 1 R},
      |‖fibreChargeTerminalReceiver l.val R.factorial X‖ ^ 2 - 1 / 20| ≤ ε := by
    rw [Filter.eventually_all]
    intro l
    have h := (tendsto_fibreChargeTerminalReceiver_norm_sq
      (mem_Icc.mp l.property).1 (Nat.factorial_pos R)).sub_const (1 / 20 : ℝ)
    rw [sub_self] at h
    exact h.abs.eventually (by simpa only [abs_zero] using ge_mem_nhds hε)
  filter_upwards [eventually_ge_atTop R.factorial,
    eventually_simultaneousReceiving_coordinates R t, ha, hi, hw, hp, hr]
    with X hX hc hA hI hW hP hR
  exact ⟨hX, ⟨hc.1, hc.2, hA, hI, hW, fun l hl => hP ⟨l, hl⟩⟩,
    fun l hl => ⟨fibreChargeTerminalReceiver_mem l R.factorial X, hR ⟨l, hl⟩⟩⟩

/-- Every infinite real charge profile is received on a growing mode set.
The cutoff can depend on the profile; no boundedness assumption is needed. -/
theorem exists_growing_prescribedReceiving {K : ℝ} (hK : 0 < K) (t : ℕ → ℝ) :
    ∃ R : ℕ → ℕ, Monotone R ∧ Tendsto R atTop atTop ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop, PrescribedReceivingControl K (R X) X t ε := by
  obtain ⟨R, hmono, htop, hcontrol⟩ := exists_growing_receiving_diagonal
    (fun R => eventually_prescribedReceivingControl hK R t
      (by positivity : 0 < 1 / ((R : ℝ) + 1)))
  refine ⟨R, hmono, htop, fun ε hε => ?_⟩
  have hsmall := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp htop
  filter_upwards [hcontrol, hsmall.eventually (ge_mem_nhds hε)] with X hc he
  obtain ⟨hn, hcoord, ha, hi, hw, hp⟩ := hc.2.1
  exact ⟨hc.1, ⟨hn, hcoord, ha.trans he, hi.trans he, hw.trans he,
    fun l hl => (hp l hl).trans he⟩,
    fun l hl => ⟨(hc.2.2 l hl).1, (hc.2.2 l hl).2.trans he⟩⟩

/-- Both the mode cutoff and the full conductor cutoff grow monotonically and without bound,
while the conductor cutoff stays below `X³` and receiving errors vanish uniformly. -/
theorem exists_growing_simultaneousReceiving_conductors {K : ℝ} (hK : 0 < K) :
    ∃ R M : ℕ → ℕ, Monotone R ∧ Tendsto R atTop atTop ∧
      Monotone M ∧ Tendsto M atTop atTop ∧
      (∀ X, M X = (R X).factorial * X ^ 2) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ X : ℕ in atTop,
        SimultaneousReceivingControl K (R X) X ε ∧ M X ≤ X ^ 3 := by
  obtain ⟨R, hmono, htop, hcontrol⟩ := exists_growing_simultaneousReceiving_vanishing hK
  let M (X : ℕ) := (R X).factorial * X ^ 2
  have hMmono : Monotone M := fun X Y hXY =>
    Nat.mul_le_mul (Nat.factorial_le (hmono hXY))
      (pow_le_pow_left₀ (Nat.zero_le X) hXY 2)
  have hMtop : Tendsto M atTop atTop := by
    refine tendsto_atTop_atTop.mpr fun n => ⟨n + 1, fun X hX => ?_⟩
    have hX1 : 1 ≤ X := by omega
    have hpow : X ≤ X ^ 2 := by nlinarith only [hX1]
    have hfactor : X ^ 2 ≤ M X := by
      change X ^ 2 ≤ (R X).factorial * X ^ 2
      calc X ^ 2 = 1 * X ^ 2 := (one_mul _).symm
        _ ≤ (R X).factorial * X ^ 2 :=
          Nat.mul_le_mul_right _ (show 1 ≤ (R X).factorial from Nat.factorial_pos _)
    exact (by omega : n ≤ X).trans (hpow.trans hfactor)
  refine ⟨R, M, hmono, htop, hMmono, hMtop, fun _ => rfl, fun ε hε => ?_⟩
  filter_upwards [hcontrol ε hε] with X hc
  refine ⟨hc, ?_⟩
  calc M X ≤ X * X ^ 2 := Nat.mul_le_mul_right _ hc.1
    _ = X ^ 3 := by ring

#print axioms tendsto_simultaneousReceivingError
#print axioms eventually_simultaneousReceivingControl
#print axioms exists_growing_simultaneousReceivingControl
#print axioms exists_growing_simultaneousReceiving_vanishing
#print axioms exists_growing_prescribedReceiving
#print axioms exists_growing_simultaneousReceiving_conductors

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
