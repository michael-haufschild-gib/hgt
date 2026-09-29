import GaloisForLFunctions.HTGeometry.SingularGaugeToeplitzHorizon

/-!
# The prime–Hodge singular-gauge Riesz charge

With `Q = diag(√m_n)`, the survival shift `C`, the metric defect `D = I - C*C` and the pure shift
`U` on `ℓ²(ℕ)`:

* **(A)** `Φ = Q D Q = Q² - U* Q² U = diag(w_n)`, while `D = diag(6/(2n+9))` is not trace class
  and `tr Q² = 7/4`; tensoring with the prime Stokes operator `A_d` gives `T_d = G_d - 𝒰* G_d 𝒰`,
  and the literal signed defect `T(t)` on `ℓ²(ℕ × Primes)` is `sign(t)` times this displacement.
* **(B)** joint reconstruction: the history blocks of `T_d` are `δ_{nm} w_n A_d`, summing to `A_d`;
  their prime traces are `w_n`; the blocks of `G_d` have prime traces `m_n`; the Riesz potential
  `∑_j 𝒰*ʲ T_d 𝒰ʲ` converges to `G_d` in trace norm.
* **(C)** `tr T_d = ‖T_d‖₁ = 1`, and `T(t)` is a two-chamber wall: `‖T(t) - T(0)‖₁ = 1` for every
  `t ≠ 0`, so `t ↦ T(t)` is not trace-norm continuous at `0`.
-/

open Filter Topology ContinuousLinearMap
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

/-! ## The singular-gauge sandwich -/

theorem steinIncidence_eq_diagonal : steinIncidence
    = _root_.HTGeometry.ellTwoDiagonal (fun n => ((PrimeHodgeHistory.w n : ℝ) : ℂ))
      historyFlux_norm_le :=
  eq_diagonal_of_basis _ _ steinIncidence_basis

/-- **(SGRC.3).**  `Φ = Q(I - C*C)Q = diag(w_n)`. -/
theorem singularGauge_sandwich_defect :
    singularGauge ∘L elapsedHistoryDefect 1 ∘L singularGauge = steinIncidence := by
  rw [steinIncidence_eq_diagonal]
  ext f n
  simp only [comp_apply, singularGauge_coord, elapsedHistoryDefect_coord,
    _root_.HTGeometry.ellTwoDiagonal_apply]
  have hm := PrimeHodgeHistory.m_pos n
  have key : ((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ) * (((elapsedDefect 1 n : ℝ) : ℂ) *
      (((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ) * (f : ℕ → ℂ) n))
      = ((Real.sqrt (PrimeHodgeHistory.m n) * Real.sqrt (PrimeHodgeHistory.m n) *
        elapsedDefect 1 n : ℝ) : ℂ) * (f : ℕ → ℂ) n := by
    push_cast
    ring
  rw [key, Real.mul_self_sqrt hm.le]
  congr 2
  rw [elapsedDefect, PrimeHodgeHistory.w]
  field_simp

/-- **(SGRC.3).**  `Φ = Q² - U* Q² U`. -/
theorem steinGramian_displacement :
    steinGramian - adjoint vecForward ∘L steinGramian ∘L vecForward = steinIncidence := by
  rw [adjoint_vecForward, steinIncidence_eq_diagonal]
  ext f n
  simp only [sub_apply, comp_apply, lp.coeFn_sub, Pi.sub_apply, steinGramian_coord,
    vecBack_apply, vecForward_apply_succ, _root_.HTGeometry.ellTwoDiagonal_apply]
  rw [← sub_mul, PrimeHodgeHistory.w, Complex.ofReal_sub]

/-- The metric defect `D = I - C*C` has diagonal `6/(2n+9)`. -/
theorem elapsedDefect_one_eq (n : ℕ) : elapsedDefect 1 n = 6 / (2 * (n : ℝ) + 9) := by
  rw [elapsedDefect_partialFraction]
  simp only [residueCoeffA, residueCoeffB, residueCoeffC]
  push_cast
  ring

/-- **(SGRC.4).**  The literal signed defect on `ℓ²(ℕ × Primes)` is `sign(t)` times the shift
displacement of `G_{|t|} = Q² ⊗ A_{|t|}`. -/
theorem homotopyDefect_eq_displacement {t : ℝ} (ht : t ≠ 0) :
    primeHistoryUnitary ∘L primeHodgeHistoryIntegralNuclearHomotopyDefect t ∘L
        adjoint primeHistoryUnitary
      = ((Real.sign t : ℝ) : ℂ) • (gaugeCompletion (primeFormation (abs_pos.mpr ht)) -
        adjoint vecForward ∘L gaugeCompletion (primeFormation (abs_pos.mpr ht)) ∘L vecForward) := by
  rw [primeHistoryUnitary_conj, historyDefect_eq_displacement ht]

/-! ## Joint reconstruction -/

section Blocks

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem inner_single_historyMap (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ ≤ 1) (A : E →L[ℂ] E) (n m : ℕ)
    (x y : E) :
    ⟪lp.single 2 n x, historyMap a ha A (lp.single 2 m y)⟫_ℂ
      = if n = m then a n * ⟪x, A y⟫_ℂ else 0 := by
  have h : ⟪lp.single 2 n x, historyMap a ha A (lp.single 2 m y)⟫_ℂ
      = ⟪x, (historyMap a ha A (lp.single 2 m y) : ℕ → E) n⟫_ℂ := lp.inner_single_left _ _ _
  rw [h, historyMap_apply]
  split_ifs with hnm
  · subst hnm
    rw [lp.single_apply_self, inner_smul_right]
  · rw [lp.single_apply_ne _ _ _ hnm, map_zero, smul_zero, inner_zero_right]

end Blocks

theorem opTrace_smul_of_traceClass {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {A : H →L[ℂ] H} (hA : MemSchattenClass 1 A) (c : ℂ) :
    opTrace (c • A) = c * opTrace A := by
  have hcA : MemSchattenClass 1 (c • A) := by
    unfold MemSchattenClass at hA ⊢
    simp_rw [approxNumber_smul, Real.rpow_one] at hA ⊢
    exact hA.mul_left _
  obtain ⟨w, b, -⟩ := exists_hilbertBasis ℂ H
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one hcA b,
    opTrace_eq_tsum_basis_of_memSchattenClass_one hA b, ← tsum_mul_left]
  exact tsum_congr fun i => by rw [smul_apply, inner_smul_right]

/-- **(SGRC.6)–(SGRC.9).**  The history blocks of `T_d` are `δ_{nm} w_n A_d` with prime traces
`w_n`; those of `G_d` are `δ_{nm} m_n A_d` with prime traces `m_n`; the diagonal blocks of `T_d`
sum to `A_d`. -/
theorem prime_joint_reconstruction {d : ℝ} (hd : 0 < d) :
    (∀ n m (x y : PrimeHilbert), ⟪lp.single 2 n x,
        fluxTensor (primeFormation hd) (lp.single 2 m y)⟫_ℂ
      = if n = m then (PrimeHodgeHistory.w n : ℂ) * ⟪x, primeFormation hd y⟫_ℂ else 0) ∧
    (∀ n m (x y : PrimeHilbert), ⟪lp.single 2 n x,
        gaugeCompletion (primeFormation hd) (lp.single 2 m y)⟫_ℂ
      = if n = m then (PrimeHodgeHistory.m n : ℂ) * ⟪x, primeFormation hd y⟫_ℂ else 0) ∧
    HasSum (fun n => (PrimeHodgeHistory.w n : ℂ) • primeFormation hd) (primeFormation hd) ∧
    (∀ n, opTrace ((PrimeHodgeHistory.w n : ℂ) • primeFormation hd) = PrimeHodgeHistory.w n) ∧
    (∀ n, opTrace ((PrimeHodgeHistory.m n : ℂ) • primeFormation hd) = PrimeHodgeHistory.m n) ∧
    Tendsto (fun N => traceNorm (HistoryL2 PrimeHilbert) (gaugeCompletion (primeFormation hd) -
      ∑ j ∈ Finset.range N, (vecBack ^ j) ∘L fluxTensor (primeFormation hd) ∘L (vecForward ^ j)))
      atTop (𝓝 0) := by
  obtain ⟨h1, h2, h3⟩ := primeFormation_traceClass hd
  refine ⟨fun n m x y => inner_single_historyMap _ _ _ n m x y,
    fun n m x y => inner_single_historyMap _ _ _ n m x y, hasSum_fluxTensor_blocks _,
    fun n => ?_, fun n => ?_, tendsto_traceNorm_gaugeCompletion_sub h1 h2⟩
  · rw [opTrace_smul_of_traceClass h2, h3, mul_one]
  · rw [opTrace_smul_of_traceClass h2, h3, mul_one]

/-! ## Conservation and the two-chamber wall -/

/-- **(SGRC.10).**  `tr T_d = ‖T_d‖₁ = 1`. -/
theorem prime_charge_unit {d : ℝ} (hd : 0 < d) :
    opTrace (fluxTensor (primeFormation hd)) = 1 ∧
      traceNorm (HistoryL2 PrimeHilbert) (fluxTensor (primeFormation hd)) = 1 := by
  obtain ⟨h1, h2, h3⟩ := primeFormation_traceClass hd
  exact ⟨by rw [(fluxTensor_traceClass h1 h2).2.2, h3], (prime_completion_masses hd).1⟩

/-- **§8.**  `‖T(t) - T(0)‖₁ = 1` for every `t ≠ 0`. -/
theorem traceNorm_homotopyDefect_sub_zero {t : ℝ} (ht : t ≠ 0) :
    traceNorm PrimeHodgeHistoryHilbert (primeHodgeHistoryIntegralNuclearHomotopyDefect t -
      primeHodgeHistoryIntegralNuclearHomotopyDefect 0) = 1 := by
  rw [primeHodgeHistoryIntegralNuclearHomotopyDefect_zero, sub_zero,
    (primeHodgeHistoryIntegralNuclearHomotopyDefect_closed t).2.2.1]
  rcases lt_or_gt_of_ne ht with h | h
  · rw [Real.sign_of_neg h, abs_neg, abs_one]
  · rw [Real.sign_of_pos h, abs_one]

/-- **§8.**  `t ↦ T(t)` is not trace-norm continuous at the neutral wall. -/
theorem not_tendsto_traceNorm_homotopyDefect :
    ¬Tendsto (fun t => traceNorm PrimeHodgeHistoryHilbert
      (primeHodgeHistoryIntegralNuclearHomotopyDefect t -
        primeHodgeHistoryIntegralNuclearHomotopyDefect 0)) (𝓝[≠] 0) (𝓝 0) := by
  intro h
  have h1 : Tendsto (fun t => traceNorm PrimeHodgeHistoryHilbert
      (primeHodgeHistoryIntegralNuclearHomotopyDefect t -
        primeHodgeHistoryIntegralNuclearHomotopyDefect 0)) (𝓝[≠] 0) (𝓝 1) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht =>
      (traceNorm_homotopyDefect_sub_zero ht).symm)
  exact one_ne_zero (tendsto_nhds_unique h1 h)

/-- **ULF-PHSGRC-001.**  The singular gauge turns the non-nuclear metric defect `D = I - C*C`
(`diag(6/(2n+9))`, not trace class) into the unit charge `Φ = Q D Q = Q² - U*Q²U = diag(w_n)`;
the literal prime-mixed defect is `sign(t)` times the displacement `G_d - 𝒰* G_d 𝒰`; its history
blocks, prime traces and Riesz potential reconstruct `A_d`, `w_n`, `m_n` and `G_d`; its trace and
trace norm are `1`, matching `-ind C` and the total exit flux; and `T(t)` is a two-chamber wall,
trace-norm discontinuous at `t = 0`. -/
theorem prime_hodge_singular_gauge_riesz_charge :
    primeHodgeHistorySurvivalShift ∘L singularGauge = singularGauge ∘L vecForward ∧
    singularGauge ∘L elapsedHistoryDefect 1 ∘L singularGauge = steinIncidence ∧
    steinGramian - adjoint vecForward ∘L steinGramian ∘L vecForward = steinIncidence ∧
    (∀ n, elapsedDefect 1 n = 6 / (2 * (n : ℝ) + 9)) ∧
    ¬MemSchattenClass 1 (elapsedHistoryDefect 1) ∧
    opTrace steinGramian = ((7 / 4 : ℝ) : ℂ) ∧
    (∀ {t : ℝ} (ht : t ≠ 0), primeHistoryUnitary ∘L
        primeHodgeHistoryIntegralNuclearHomotopyDefect t ∘L adjoint primeHistoryUnitary
      = ((Real.sign t : ℝ) : ℂ) • (gaugeCompletion (primeFormation (abs_pos.mpr ht)) -
        adjoint vecForward ∘L gaugeCompletion (primeFormation (abs_pos.mpr ht)) ∘L vecForward)) ∧
    (∀ {d : ℝ} (hd : 0 < d), opTrace (fluxTensor (primeFormation hd)) = 1 ∧
      traceNorm (HistoryL2 PrimeHilbert) (fluxTensor (primeFormation hd)) = 1 ∧
      traceNorm (HistoryL2 PrimeHilbert) (gaugeCompletion (primeFormation hd)) = 7 / 4) ∧
    ((-primeHodgeHistorySurvivalShiftIndex : ℤ) : ℂ) =
      opTrace primeHodgeHistoryIntegralNuclearDefectT ∧
    ((∑' n, primeHodgeHistoryExitEnergy n : ℝ) : ℂ) =
      opTrace primeHodgeHistoryIntegralNuclearDefectT ∧
    ¬Tendsto (fun t => traceNorm PrimeHodgeHistoryHilbert
      (primeHodgeHistoryIntegralNuclearHomotopyDefect t -
        primeHodgeHistoryIntegralNuclearHomotopyDefect 0)) (𝓝[≠] 0) (𝓝 0) := by
  obtain ⟨c1, c2, -⟩ := primeHodgeHistory_index_exitFlux_integralNuclear_conservation
  exact ⟨survivalShift_comp_singularGauge, singularGauge_sandwich_defect,
    steinGramian_displacement, elapsedDefect_one_eq, (elapsedHistoryDefect_schatten le_rfl).1,
    steinGramian_traceClass.2.2.1, fun ht => homotopyDefect_eq_displacement ht,
    fun hd => ⟨(prime_charge_unit hd).1, (prime_charge_unit hd).2,
      (prime_completion_masses hd).2⟩, c1, c2, not_tendsto_traceNorm_homotopyDefect⟩

end GaloisForLFunctions.HTGeometry
