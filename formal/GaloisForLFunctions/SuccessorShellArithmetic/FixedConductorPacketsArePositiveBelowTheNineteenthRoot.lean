import GaloisForLFunctions.CompletedArithmeticForms.WeilGrowingPackets
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompleteConductorResidualsRetainTheirHorizonDecay

/-!
# Fixed conductor packets are positive below the nineteenth root

Along `c_N = (log N)^α` the conductor floor is `E_m(c) ≥ κ c⁻⁷`, the complete residual keeps its
horizon decay `‖(W − E_m)u_m‖² ≤ K_m(c⁵/log N + c¹⁰(log N/N)²)`, and the Gram error of conductor
modes is `O(ml/log N)` with `E_m ≤ C_m c²`. After scaling by `c⁷`:

* the residual contributes `c^{19/2}(log N)^{−1/2}` (`tendsto_scaled_residual_norm_of_lt_one_nineteenth`);
* the Gram error contributes `c⁹/log N`.

Both vanish exactly when `19α < 1`. So every fixed finite family of distinct conductors is positive
simultaneously for all coefficients along `c_N = (log N)^α`, `0 < α < 1/19`
(`eventually_tiltedWeil_packet_pos_of_lt_one_nineteenth`). The exponent `19 = 2·7 + 5` is the
floor exponent twice plus the residual exponent: with the floor `(m/c)⁷` sharp at fixed `m`, the
residual rate `c⁵/log N` is the only input that can move it.
-/

noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.SuccessorShellArithmetic

open CompletedArithmeticForms CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

private theorem packetOverlap_nonneg (α : ℝ) (N : ℕ) : 0 ≤ logarithmicPacketOverlap α N :=
  Real.rpow_nonneg (Real.log_natCast_nonneg N) α

/-- `(log N)^a / N → 0` along the integers. -/
private theorem tendsto_log_rpow_div_nat (a : ℝ) :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ a / (N : ℝ)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop a (zero_lt_one' ℝ)).tendsto_div_nhds_zero
  have h' := h.comp tendsto_natCast_atTop_atTop
  refine h'.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  simp only [Function.comp, Real.rpow_one]

/-- The horizon tail `c¹⁴ · c¹⁰ (log N/N)²` vanishes along every logarithmic schedule. -/
private theorem tendsto_horizon_tail (α : ℝ) :
    Tendsto (fun N : ℕ => logarithmicPacketOverlap α N ^ 24 * (Real.log (N : ℝ) / N) ^ 2)
      atTop (𝓝 0) := by
  have h1 := tendsto_log_rpow_div_nat (24 * α + 1)
  have h2 := tendsto_log_rpow_div_nat 1
  have h := h1.mul h2
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpow : logarithmicPacketOverlap α N ^ 24 = Real.log (N : ℝ) ^ (24 * α) := by
    unfold logarithmicPacketOverlap
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    push_cast
    ring_nf
  rw [hpow, Real.rpow_add hL, Real.rpow_one, Real.rpow_one]
  ring

/-- **The scaled residual vanishes below the nineteenth root**: `c⁷‖(W − E_m)u_m‖ → 0` along
`c = (log N)^α` for `0 < α < 1/19`. -/
theorem tendsto_scaled_residual_norm_of_lt_one_nineteenth {α : ℝ} (hα0 : 0 < α)
    (hα : α < 1 / 19) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ => logarithmicPacketOverlap α N ^ 7 *
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (logarithmicPacketOverlap α N) N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline (logarithmicPacketOverlap α N) m •
          normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0) := by
  obtain ⟨K, hK, hbound⟩ := exists_tiltedUnitSpline_completedConductor_residual_horizon_bound hm
  let c := logarithmicPacketOverlap α
  have hfirst := tendsto_packetOverlap_pow_div_log (α := α) 19 (by push_cast; linarith only [hα])
  have hlim := (hfirst.add (tendsto_horizon_tail α)).const_mul K
  rw [add_zero, mul_zero] at hlim
  -- eventually the horizon condition `4(e + 3)²c² ≤ N` holds
  have hdom : ∀ᶠ N : ℕ in atTop, 1 ≤ c N ∧ 4 * (Real.exp 1 + 3) ^ 2 * c N ^ 2 ≤ (N : ℝ) := by
    have h2 := (tendsto_packetOverlap_pow_div_log (α := α) 2
      (by push_cast; linarith only [hα])).eventually
      (gt_mem_nhds (show (0 : ℝ) < 1 / (4 * (Real.exp 1 + 3) ^ 2) by positivity))
    filter_upwards [eventually_logarithmicPacketOverlap_source_domain hα0, h2,
      eventually_ge_atTop 3] with N hd hN h3
    refine ⟨hd.1, ?_⟩
    have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hLN : Real.log (N : ℝ) ≤ N := (Real.log_le_sub_one_of_pos (by positivity)).trans
      (by linarith only)
    have hA : (0 : ℝ) < 4 * (Real.exp 1 + 3) ^ 2 := by positivity
    rw [div_lt_div_iff₀ hL hA, one_mul] at hN
    change logarithmicPacketOverlap α N ^ 2 * (4 * (Real.exp 1 + 3) ^ 2) < Real.log N at hN
    nlinarith only [hN, hLN]
  have hsq : Tendsto (fun N : ℕ => (c N ^ 7 *
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline (c N) m •
          normalizedRamanujanHorizonVector m N‖) ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) _ hlim
    filter_upwards [hbound, hdom] with N hN hd
    have h := mul_le_mul_of_nonneg_left (hN (c N) hd.1 hd.2)
      (pow_nonneg (packetOverlap_nonneg α N) 14)
    rw [mul_pow, ← pow_mul]
    refine h.trans_eq ?_
    dsimp only [c]
    ring
  have h := hsq.sqrt
  rw [Real.sqrt_zero] at h
  refine h.congr fun N => Real.sqrt_sq (mul_nonneg (pow_nonneg (packetOverlap_nonneg α N) 7)
    (norm_nonneg _))

/-- The scaled packet entries differ from their energy diagonal by `o(1)` for `α < 1/19`. -/
theorem tendsto_scaled_packet_entry_error_of_lt_one_nineteenth {α : ℝ}
    (hα0 : 0 < α) (hα : α < 1 / 19) (m l : ℕ+) :
    Tendsto (fun N : ℕ => logarithmicPacketOverlap α N ^ 7 *
      (⟪Matrix.toEuclideanLin
          (completeWeilMatrix tiltedUnitSpline (logarithmicPacketOverlap α N) N)
          (normalizedRamanujanHorizonVector m N), normalizedRamanujanHorizonVector l N⟫ -
        (if m = l then completedConductorEnergy tiltedUnitSpline (logarithmicPacketOverlap α N) m
          else 0))) atTop (𝓝 0) := by
  let c := logarithmicPacketOverlap α
  let E (N : ℕ) := completedConductorEnergy tiltedUnitSpline (c N) m
  let r (N : ℕ) := Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
      (normalizedRamanujanHorizonVector m N) - E N • normalizedRamanujanHorizonVector m N
  have hres : Tendsto (fun N : ℕ => ‖c N ^ 7 • r N‖) atTop (𝓝 0) := by
    apply (tendsto_scaled_residual_norm_of_lt_one_nineteenth hα0 hα m.property).congr
    intro N
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (packetOverlap_nonneg α N) 7)]
  have hi := tendsto_horizon_inner_zero_of_norm (fun N => c N ^ 7 • r N)
    (fun N => normalizedRamanujanHorizonVector l N) hres
    (tendsto_normalizedRamanujanHorizonVector_norm l.property)
  obtain ⟨C, hC, hE⟩ := exists_completedConductorEnergy_polynomial_bound
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos m.property
  have hlim := (tendsto_packetOverlap_pow_div_log (α := α) 9
    (by push_cast; linarith only [hα])).const_mul (C * (2 * (m : ℝ) * (l : ℝ) + 1))
  simp only [mul_zero] at hlim
  have hgram : Tendsto (fun N : ℕ => c N ^ 7 * E N *
      (⟪normalizedRamanujanHorizonVector m N, normalizedRamanujanHorizonVector l N⟫ -
        (if m = l then 1 else 0))) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_logarithmicPacketOverlap_source_domain hα0,
      eventually_ge_atTop 2] with N hd hN
    have hc : 0 ≤ c N := (zero_lt_one.trans_le hd.1).le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hc 7)]
    calc
      _ ≤ c N ^ 7 * (C * c N ^ 2) * ((2 * (m : ℝ) * (l : ℝ) + 1) / Real.log N) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hE _ hd.1) (pow_nonneg hc 7))
          (normalizedRamanujan_gram_error_le m l hN) (abs_nonneg _) (by positivity)
      _ = _ := by dsimp only [c]; ring
  have h := hi.add hgram
  simp only [zero_add] at h
  apply h.congr
  intro N
  simp only [r, real_inner_smul_left, inner_sub_left, E, c]
  split_ifs <;> ring

/-- **Fixed conductor packets are positive below the nineteenth root.** Every fixed family of
distinct positive conductors is positive for all coefficients along `c_N = (log N)^α`,
`0 < α < 1/19`. -/
theorem eventually_tiltedWeil_packet_pos_of_lt_one_nineteenth {α : ℝ}
    (hα0 : 0 < α) (hα : α < 1 / 19) {d : ℕ}
    (m : Fin d → ℕ+) (hm : Function.Injective m) :
    ∀ᶠ N : ℕ in atTop, ∀ b : Fin d → ℝ, b ≠ 0 →
      0 < completeWeilEnergy tiltedUnitSpline (logarithmicPacketOverlap α N) N
        (∑ i, b i • normalizedRamanujanHorizonVector (m i) N) := by
  let c := logarithmicPacketOverlap α
  let κ := tiltedConductorFloorCoefficient
  let H (N : ℕ) : Matrix (Fin d) (Fin d) ℝ := fun i j => c N ^ 7 *
    ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline (c N) N)
      (normalizedRamanujanHorizonVector (m i) N), normalizedRamanujanHorizonVector (m j) N⟫
  let D (N : ℕ) : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal fun i =>
    c N ^ 7 * completedConductorEnergy tiltedUnitSpline (c N) (m i)
  let ε := κ / (2 * ((d : ℝ) + 1))
  have hκ : 0 < κ := tiltedConductorFloorCoefficient_pos
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hgap : (d : ℝ) * ε < κ := by
    dsimp only [ε]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith only [hκ, mul_nonneg (Nat.cast_nonneg d) hκ.le]
  have hclose : ∀ᶠ N : ℕ in atTop, ∀ i j, |(H N - D N) i j| ≤ ε := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have ht := tendsto_scaled_packet_entry_error_of_lt_one_nineteenth hα0 hα (m i) (m j)
    filter_upwards [Metric.tendsto_nhds.mp ht ε hε] with N hN
    rw [Real.dist_eq, sub_zero] at hN
    have he : (m i = m j) ↔ i = j := hm.eq_iff
    simpa only [H, D, Matrix.sub_apply, Matrix.diagonal_apply, he, mul_ite, mul_zero,
      mul_sub] using hN.le
  filter_upwards [hclose, eventually_logarithmicPacketOverlap_source_domain hα0] with N hN hd
  intro b hb
  have hc : 0 < c N := zero_lt_one.trans_le hd.1
  have hmass : 0 < b ⬝ᵥ b := by
    have hnon : 0 ≤ b ⬝ᵥ b := Finset.sum_nonneg fun _ _ => mul_self_nonneg _
    exact lt_of_le_of_ne hnon (Ne.symm fun he => hb (dotProduct_self_eq_zero.mp he))
  have hfloor : κ * (b ⬝ᵥ b) ≤ b ⬝ᵥ D N *ᵥ b := by
    simp only [D, dotProduct, Matrix.mulVec_diagonal, mul_sum]
    apply sum_le_sum
    intro i _
    have hf := tiltedUnitSpline_completedConductorEnergy_ge_polynomial_floor hd.1 (m i).property
    change κ / c N ^ 7 ≤ completedConductorEnergy tiltedUnitSpline (c N) (m i) at hf
    rw [div_le_iff₀ (pow_pos hc 7)] at hf
    have h := mul_le_mul_of_nonneg_right hf (sq_nonneg (b i))
    calc
      _ = κ * b i ^ 2 := by ring
      _ ≤ completedConductorEnergy tiltedUnitSpline (c N) (m i) * c N ^ 7 * b i ^ 2 := h
      _ = _ := by ring
  have herr := HTGeometry.abs_dotProduct_mulVec_le (H N - D N) hε.le hN b
  have heq : b ⬝ᵥ H N *ᵥ b = b ⬝ᵥ D N *ᵥ b + b ⬝ᵥ (H N - D N) *ᵥ b := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
    ring
  have hpos : 0 < b ⬝ᵥ H N *ᵥ b := by
    have hneg := (abs_le.mp herr).1
    have hp := mul_pos (sub_pos.mpr hgap) hmass
    nlinarith only [hfloor, hneg, heq, hp]
  have hform : b ⬝ᵥ H N *ᵥ b = c N ^ 7 *
      completeWeilEnergy tiltedUnitSpline (c N) N
        (∑ i, b i • normalizedRamanujanHorizonVector (m i) N) := by
    simp only [H, completeWeilEnergy, dotProduct, Matrix.mulVec, map_sum, map_smul,
      sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  rw [hform] at hpos
  exact (mul_pos_iff_of_pos_left (pow_pos hc 7)).mp hpos

end GaloisForLFunctions.SuccessorShellArithmetic

#print axioms GaloisForLFunctions.SuccessorShellArithmetic.tendsto_scaled_residual_norm_of_lt_one_nineteenth
#print axioms GaloisForLFunctions.SuccessorShellArithmetic.eventually_tiltedWeil_packet_pos_of_lt_one_nineteenth
