import GaloisForLFunctions.HTGeometry.PrimePairWallLanding
import GaloisForLFunctions.HTGeometry.HodgeSurvivalShiftDynamics

/-!
# The prime–Hodge Stein–Gramian reconstruction

For the forced survival shift `C e_n = √r_n e_{n+1}` on `ℓ²(ℕ)`, `r_n = m_{n+1}/m_n`:

* the survival masses have total `∑ m_n = 7/4 = ∑ (n+1) w_n`;
* **(A)** the controllability Gramian `G = ∑_j Cʲ P₀ C*ʲ` converges in trace norm to `diag(m_n)`,
  `tr G = ‖G‖₁ = 7/4`, and `G - C G C* = P₀`; every bounded solution of this Stein equation is
  `G`, because `C*ⁿ` annihilates `e_k` for `n > k`;
* **(B)** the incidence `Φ = Δ^{1/2} G Δ^{1/2}` with the adjoint defect `Δ = I - C*C` is
  `diag(w_n)`: positive, nuclear, `tr Φ = ‖Φ‖₁ = tr P₀ = 1`, `‖Φ‖ = 2/3`; abstractly
  `tr(R K K* R*) = tr(K K*) - tr(C K K* C*)` whenever `R*R = I - C*C`;
* the prime–Hodge defects are reconstructed from `Φ`: the separable defect is `Φ ⊗ A_form`, and
  the Cayley-collision record is `V Φ V*` for the isometric formation embedding
  `V e_n = f_n/‖f_n‖`, `f_n = E₀ Sⁿ Ω_H`.
-/

open MeasureTheory Filter Topology Set ContinuousLinearMap ProbabilityTheory
open scoped ENNReal NNReal ComplexConjugate InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local instance isProbabilityMeasure_expMeasure_one_stein : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure one_pos

/-! ## The total survival mass -/

theorem sum_range_m (N : ℕ) :
    ∑ n ∈ Finset.range N, PrimeHodgeHistory.m n
      = 105 / 8 * (1 / 3 - 1 / 5 - 1 / (2 * (N : ℝ) + 3) + 1 / (2 * (N : ℝ) + 5)) := by
  induction N with
  | zero => norm_num
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, PrimeHodgeHistory.m]
    push_cast
    field_simp
    ring

theorem tendsto_one_div_two_mul_add (c : ℝ) :
    Tendsto (fun N : ℕ => 1 / (2 * (N : ℝ) + c)) atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => 2 * (N : ℝ) + c) atTop atTop :=
    tendsto_atTop_add_const_right _ c (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
  simp only [one_div]
  exact h.inv_tendsto_atTop

/-- **(PHRD.2).**  `∑ₙ m_n = 7/4`. -/
theorem hasSum_m : HasSum PrimeHodgeHistory.m (7 / 4) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n => (PrimeHodgeHistory.m_pos n).le)]
  simp_rw [sum_range_m]
  have h := ((tendsto_const_nhds (x := (1 / 3 - 1 / 5 : ℝ))).sub
    (tendsto_one_div_two_mul_add 3)).add (tendsto_one_div_two_mul_add 5)
  have h2 := h.const_mul (105 / 8 : ℝ)
  convert h2 using 1
  norm_num

theorem summable_hodgeSurvivalMass : Summable PrimeHodgeHistory.m := hasSum_m.summable

theorem sum_range_succ_mul_w (N : ℕ) :
    ∑ n ∈ Finset.range N, ((n : ℝ) + 1) * PrimeHodgeHistory.w n
      = ∑ n ∈ Finset.range N, PrimeHodgeHistory.m n - N * PrimeHodgeHistory.m N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, PrimeHodgeHistory.w]
    push_cast
    ring

theorem tendsto_mul_m : Tendsto (fun N : ℕ => (N : ℝ) * PrimeHodgeHistory.m N) atTop (𝓝 0) := by
  have hup : Tendsto (fun N : ℕ => 105 * (1 / (2 * (N : ℝ) + 5))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_two_mul_add 5).const_mul (105 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun N => mul_nonneg (Nat.cast_nonneg N) (PrimeHodgeHistory.m_pos N).le) fun N => ?_
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  simp only [PrimeHodgeHistory.m]
  push_cast
  rw [mul_div_assoc', div_le_iff₀ (by positivity)]
  have h1 : (N : ℝ) ≤ 2 * N + 3 := by linarith
  have h2 : (1 : ℝ) ≤ 2 * N + 7 := by linarith
  field_simp
  nlinarith [mul_le_mul h1 h2 (by norm_num) (by positivity)]

/-- **Theorem PHRD-A.**  The exit law has mean `∑ (n+1) w_n = ∑ m_n = 7/4`. -/
theorem hasSum_succ_mul_w :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * PrimeHodgeHistory.w n) (7 / 4) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg
    (fun n => mul_nonneg (by positivity) (PrimeHodgeHistory.w_pos n).le)]
  simp_rw [sum_range_succ_mul_w]
  have h := (hasSum_m.tendsto_sum_nat).sub tendsto_mul_m
  rw [sub_zero] at h
  exact h

/-! ## The coordinates of the survival shift -/

theorem survivalShift_coord_zero (f : lp (fun _ : ℕ => ℂ) 2) :
    (primeHodgeHistorySurvivalShift f : ℕ → ℂ) 0 = 0 :=
  primeHodgeHistorySurvivalShift_zero f

theorem survivalShift_coord_succ (f : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    (primeHodgeHistorySurvivalShift f : ℕ → ℂ) (n + 1)
      = primeHodgeHistorySurvivalWeight n * (f : ℕ → ℂ) n :=
  primeHodgeHistorySurvivalShift_apply f n

/-- `(C* f)_n = √r_n f_{n+1}`. -/
theorem adjoint_survivalShift_coord (f : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    (adjoint primeHodgeHistorySurvivalShift f : ℕ → ℂ) n
      = primeHodgeHistorySurvivalWeight n * (f : ℕ → ℂ) (n + 1) := by
  rw [primeHodgeHistorySurvivalShift, adjoint_comp, adjoint_primeHodgeHistorySurvivalDiagonal,
    GaloisForLFunctions.HTGeometry.adjoint_shiftOp, comp_apply, primeHodgeHistorySurvivalDiagonal,
    _root_.HTGeometry.ellTwoDiagonal_apply, GaloisForLFunctions.HTGeometry.backOp_apply]

theorem survivalWeight_mul_self (n : ℕ) :
    primeHodgeHistorySurvivalWeight n * primeHodgeHistorySurvivalWeight n
      = (PrimeHodgeHistory.survivalRatio n : ℂ) := by
  rw [primeHodgeHistorySurvivalWeight, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (PrimeHodgeHistory.survivalRatio_pos n).le]

/-- `Cᴺ` vanishes on the first `N` coordinates. -/
theorem survivalShift_pow_coord_of_lt {N n : ℕ} (h : n < N) (f : lp (fun _ : ℕ => ℂ) 2) :
    ((primeHodgeHistorySurvivalShift ^ N) f : ℕ → ℂ) n = 0 := by
  induction N generalizing n with
  | zero => omega
  | succ N ih =>
    rw [pow_succ', mul_def, comp_apply]
    rcases n with _ | k
    · exact survivalShift_coord_zero _
    · rw [survivalShift_coord_succ, ih (by omega), mul_zero]

/-! ## Theorem A: the Stein Gramian -/

theorem norm_sqrt_ofReal_sq (x : ℝ) (hx : 0 ≤ x) : ‖((Real.sqrt x : ℝ) : ℂ)‖ ^ 2 = x := by
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hx]

theorem summable_sqrt_m_sq :
    Summable fun n => ‖((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ)‖ ^ 2 :=
  summable_hodgeSurvivalMass.congr fun n =>
    (norm_sqrt_ofReal_sq _ (PrimeHodgeHistory.m_pos n).le).symm

/-- **(PHSG.4)–(PHSG.5).**  The source Gramian `G = diag(m_n)`. -/
def steinGramian : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  recordOp (E := ℂ) (fun n => ((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ)) summable_sqrt_m_sq

theorem inner_sqrt_self_mul (x : ℝ) (hx : 0 ≤ x) (z : ℂ) :
    ⟪((Real.sqrt x : ℝ) : ℂ), z⟫_ℂ • ((Real.sqrt x : ℝ) : ℂ) = (x : ℂ) * z := by
  rw [RCLike.inner_apply, smul_eq_mul, Complex.conj_ofReal]
  rw [show z * ((Real.sqrt x : ℝ) : ℂ) * ((Real.sqrt x : ℝ) : ℂ)
      = z * (((Real.sqrt x * Real.sqrt x : ℝ)) : ℂ) by push_cast; ring,
    Real.mul_self_sqrt hx]
  ring

theorem steinGramian_coord (f : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    (steinGramian f : ℕ → ℂ) n = (PrimeHodgeHistory.m n : ℂ) * (f : ℕ → ℂ) n := by
  rw [steinGramian, recordOp_apply]
  exact inner_sqrt_self_mul _ (PrimeHodgeHistory.m_pos n).le _

/-- The source port `P₀ = |e₀⟩⟨e₀|`. -/
abbrev sourcePort : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 := historyGrade (E := ℂ) 0

theorem sourcePort_coord (f : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    (sourcePort f : ℕ → ℂ) n = if n = 0 then (f : ℕ → ℂ) 0 else 0 := by
  rw [sourcePort, historyGrade_apply, lp.single_apply]
  by_cases h : n = 0
  · subst h
    simp
  · simp [h]

/-- **(PHSG.5).**  The Stein equation `G - C G C* = P₀`. -/
theorem steinGramian_stein :
    steinGramian - primeHodgeHistorySurvivalShift ∘L steinGramian ∘L
        adjoint primeHodgeHistorySurvivalShift = sourcePort := by
  ext f n
  rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, sourcePort_coord, steinGramian_coord]
  rcases n with _ | k
  · rw [comp_apply, comp_apply, survivalShift_coord_zero, sub_zero, if_pos rfl,
      PrimeHodgeHistory.m_zero, Complex.ofReal_one, one_mul]
  · rw [comp_apply, comp_apply, survivalShift_coord_succ, steinGramian_coord,
      adjoint_survivalShift_coord, if_neg (Nat.succ_ne_zero k)]
    have hm : (PrimeHodgeHistory.m (k + 1) : ℂ)
        = (PrimeHodgeHistory.survivalRatio k : ℂ) * (PrimeHodgeHistory.m k : ℂ) := by
      rw [PrimeHodgeHistory.survivalRatio, ← Complex.ofReal_mul,
        div_mul_cancel₀ _ (PrimeHodgeHistory.m_pos k).ne']
    rw [hm, ← survivalWeight_mul_self]
    ring

/-- **Theorem PHSG-A, uniqueness.**  Every bounded solution of `X - C X C* = P₀` is `G`. -/
theorem eq_steinGramian_of_stein {X : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2}
    (hX : X - primeHodgeHistorySurvivalShift ∘L X ∘L adjoint primeHodgeHistorySurvivalShift
      = sourcePort) : X = steinGramian := by
  have hD1 : ∀ f, (X - steinGramian) f = primeHodgeHistorySurvivalShift
      ((X - steinGramian) (adjoint primeHodgeHistorySurvivalShift f)) := by
    intro f
    have h1 := congrArg (fun A : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 => A f)
      (hX.trans steinGramian_stein.symm)
    simp only [sub_apply, comp_apply] at h1
    simp only [sub_apply, map_sub]
    exact sub_eq_sub_iff_sub_eq_sub.mp h1
  have hDN : ∀ N f, (X - steinGramian) f = (primeHodgeHistorySurvivalShift ^ N)
      ((X - steinGramian) ((adjoint primeHodgeHistorySurvivalShift ^ N) f)) := by
    intro N
    induction N with
    | zero => intro f; simp
    | succ N ih =>
      intro f
      rw [ih f, hD1 ((adjoint primeHodgeHistorySurvivalShift ^ N) f),
        pow_succ primeHodgeHistorySurvivalShift N,
        pow_succ' (adjoint primeHodgeHistorySurvivalShift) N,
        mul_def, mul_def, comp_apply, comp_apply]
  have hzero : X - steinGramian = 0 := by
    ext f n
    rw [hDN (n + 1) f, survivalShift_pow_coord_of_lt (Nat.lt_succ_self n)]
    rfl
  exact sub_eq_zero.mp hzero

theorem steinGramian_traceClass :
    steinGramian.IsPositive ∧ MemSchattenClass 1 steinGramian ∧
      opTrace steinGramian = ((7 / 4 : ℝ) : ℂ) ∧
      traceNorm (lp (fun _ : ℕ => ℂ) 2) steinGramian = 7 / 4 := by
  obtain ⟨h1, h2, h3⟩ := recordOp_traceClass (E := ℂ)
    (fun n => ((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ)) summable_sqrt_m_sq
  have ht : ∑' n, ‖((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ)‖ ^ 2 = 7 / 4 := by
    rw [← hasSum_m.tsum_eq]
    exact tsum_congr fun n => norm_sqrt_ofReal_sq _ (PrimeHodgeHistory.m_pos n).le
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [steinGramian, h3, ht]
  · rw [steinGramian, traceNorm_recordOp, ht]

/-- The `j`-th Gramian summand `Cʲ P₀ C*ʲ = m_j |e_j⟩⟨e_j|`. -/
theorem survivalShift_pow_sourcePort_coord (j : ℕ) (f : lp (fun _ : ℕ => ℂ) 2) (n : ℕ) :
    (((primeHodgeHistorySurvivalShift ^ j) ∘L sourcePort ∘L
        adjoint (primeHodgeHistorySurvivalShift ^ j)) f : ℕ → ℂ) n
      = if n = j then (PrimeHodgeHistory.m j : ℂ) * (f : ℕ → ℂ) j else 0 := by
  have h0 : ((adjoint (primeHodgeHistorySurvivalShift ^ j) f : lp (fun _ : ℕ => ℂ) 2) : ℕ → ℂ) 0
      = ((Real.sqrt (PrimeHodgeHistory.m j) : ℝ) : ℂ) * (f : ℕ → ℂ) j := by
    have h := adjoint_inner_right (primeHodgeHistorySurvivalShift ^ j) (historyCoord 0) f
    rw [survivalShift_pow_basis, zero_add, PrimeHodgeHistory.m_zero, div_one, inner_smul_left,
      Complex.conj_ofReal, historyCoord_eq, historyCoord_eq, lp.inner_single_left,
      lp.inner_single_left] at h
    simpa using h
  have hsp : sourcePort (adjoint (primeHodgeHistorySurvivalShift ^ j) f)
      = (((Real.sqrt (PrimeHodgeHistory.m j) : ℝ) : ℂ) * (f : ℕ → ℂ) j) • historyCoord 0 := by
    rw [sourcePort, historyGrade_apply, h0, historyCoord_eq, ← lp.single_smul, smul_eq_mul,
      mul_one]
  rw [comp_apply, comp_apply, hsp, map_smul, survivalShift_pow_basis, zero_add,
    PrimeHodgeHistory.m_zero, div_one, smul_smul, historyCoord_eq, lp.coeFn_smul, Pi.smul_apply,
    lp.single_apply, smul_eq_mul]
  by_cases h : n = j
  · subst h
    simp only [Pi.single_eq_same, mul_one, if_true]
    rw [show ((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ) * (f : ℕ → ℂ) n *
        ((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ)
        = ((Real.sqrt (PrimeHodgeHistory.m n) * Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ) *
          (f : ℕ → ℂ) n by push_cast; ring,
      Real.mul_self_sqrt (PrimeHodgeHistory.m_pos n).le]
  · simp [h]

/-- **Theorem PHSG-A, convergence.**  `∑_{j<N} Cʲ P₀ C*ʲ → G` in trace norm. -/
theorem tendsto_traceNorm_steinGramian_sub :
    Tendsto (fun N => traceNorm (lp (fun _ : ℕ => ℂ) 2) (steinGramian -
      ∑ j ∈ Finset.range N, (primeHodgeHistorySurvivalShift ^ j) ∘L sourcePort ∘L
        adjoint (primeHodgeHistorySurvivalShift ^ j))) atTop (𝓝 0) := by
  have hdiff : ∀ N, steinGramian - ∑ j ∈ Finset.range N, (primeHodgeHistorySurvivalShift ^ j) ∘L
      sourcePort ∘L adjoint (primeHodgeHistorySurvivalShift ^ j)
        = recordOp (E := ℂ)
            (fun n => historyTail N n • ((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ))
            (summable_historyTail_record _ summable_sqrt_m_sq N) := by
    intro N
    ext f n
    rw [sub_apply, lp.coeFn_sub, Pi.sub_apply, steinGramian_coord, sum_apply, lp.coeFn_sum,
      Finset.sum_apply]
    simp_rw [survivalShift_pow_sourcePort_coord]
    rw [recordOp_apply, Finset.sum_ite_eq, historyTail]
    by_cases h : N ≤ n
    · rw [if_neg (by simp; omega), if_pos h, one_smul, sub_zero]
      exact (inner_sqrt_self_mul _ (PrimeHodgeHistory.m_pos n).le _).symm
    · rw [if_pos (by simp; omega), if_neg h, sub_self, zero_smul, inner_zero_left, zero_smul]
  simp_rw [hdiff, traceNorm_recordOp, tsum_historyTail_record _ summable_sqrt_m_sq]
  simp_rw [norm_sqrt_ofReal_sq _ (PrimeHodgeHistory.m_pos _).le]
  exact tendsto_sum_nat_add PrimeHodgeHistory.m

/-! ## Theorem B: the Stein–defect incidence -/

theorem summable_sqrt_w_sq :
    Summable fun n => ‖((Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ)‖ ^ 2 :=
  PrimeHodgeHistory.summable_w.congr fun n =>
    (norm_sqrt_ofReal_sq _ (PrimeHodgeHistory.w_pos n).le).symm

/-- **(PHSG.10).**  The incidence `Φ = Δ^{1/2} G Δ^{1/2}`. -/
def steinIncidence : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  sqrtExitDefect ∘L steinGramian ∘L sqrtExitDefect

/-- **(PHSG.11).**  `Φ = diag(w_n)`. -/
theorem steinIncidence_eq :
    steinIncidence = recordOp (E := ℂ) (fun n => ((Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ))
      summable_sqrt_w_sq := by
  ext f n
  rw [recordOp_apply, inner_sqrt_self_mul _ (PrimeHodgeHistory.w_pos n).le, steinIncidence,
    comp_apply, comp_apply, sqrtExitDefect, _root_.HTGeometry.ellTwoDiagonal_apply,
    steinGramian_coord, _root_.HTGeometry.ellTwoDiagonal_apply,
    PrimeHodgeHistory.w_eq_m_mul_exitHazard]
  rw [show ((Real.sqrt (PrimeHodgeHistory.exitHazard n) : ℝ) : ℂ) *
      ((PrimeHodgeHistory.m n : ℂ) * (((Real.sqrt (PrimeHodgeHistory.exitHazard n) : ℝ) : ℂ) *
        (f : ℕ → ℂ) n))
      = (((Real.sqrt (PrimeHodgeHistory.exitHazard n) *
          Real.sqrt (PrimeHodgeHistory.exitHazard n) : ℝ) : ℂ)) * (PrimeHodgeHistory.m n : ℂ) *
          (f : ℕ → ℂ) n by push_cast; ring,
    Real.mul_self_sqrt (PrimeHodgeHistory.exitHazard_pos n).le]
  push_cast
  ring

/-- **Theorem PHSG-B.**  `Φ ≥ 0`, `Φ ∈ S₁`, `tr Φ = ‖Φ‖₁ = 1`, `‖Φ‖ = w₀ = 2/3`. -/
theorem steinIncidence_nuclear :
    steinIncidence.IsPositive ∧ MemSchattenClass 1 steinIncidence ∧
      opTrace steinIncidence = 1 ∧
      traceNorm (lp (fun _ : ℕ => ℂ) 2) steinIncidence = 1 ∧ ‖steinIncidence‖ = 2 / 3 := by
  obtain ⟨h1, h2, h3⟩ := recordOp_traceClass (E := ℂ)
    (fun n => ((Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ)) summable_sqrt_w_sq
  have ht : ∑' n, ‖((Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ)‖ ^ 2 = 1 := by
    rw [← PrimeHodgeHistory.tsum_w]
    exact tsum_congr fun n => norm_sqrt_ofReal_sq _ (PrimeHodgeHistory.w_pos n).le
  rw [steinIncidence_eq]
  refine ⟨h1, h2, by rw [h3, ht, Complex.ofReal_one], by rw [traceNorm_recordOp, ht], ?_⟩
  rw [norm_recordOp _ _ (k := 0) fun n => by
    rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (PrimeHodgeHistory.w_antitone (Nat.zero_le n)),
    norm_sqrt_ofReal_sq _ (PrimeHodgeHistory.w_pos 0).le, PrimeHodgeHistory.w_zero]

theorem steinIncidence_basis (n : ℕ) :
    steinIncidence (historyCoord n) = (PrimeHodgeHistory.w n : ℂ) • historyCoord n := by
  ext k
  rw [steinIncidence_eq, recordOp_apply, inner_sqrt_self_mul _ (PrimeHodgeHistory.w_pos k).le,
    lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, historyCoord_eq, lp.single_apply]
  by_cases h : k = n
  · subst h
    simp
  · simp [h]

/-! ## The abstract Stein–defect trace law -/

section SteinTrace

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem opTrace_comp_adjoint_self {A : K →L[ℂ] H} (hA : IsHilbertSchmidt A) :
    opTrace (A ∘L adjoint A) = (ContinuousLinearMap.hsNormSq A : ℂ) := by
  have h := opTrace_adjoint_comp_self (adjoint A)
  rw [adjoint_adjoint] at h
  rw [h, hsInner_self_eq_ofReal_hsNormSq', hA.hsNormSq_adjoint]

theorem opTrace_sub_of_hs {A B : H →L[ℂ] K} {A' B' : K →L[ℂ] H} (hA : IsHilbertSchmidt A)
    (hA' : IsHilbertSchmidt A') (hB : IsHilbertSchmidt B) (hB' : IsHilbertSchmidt B') :
    opTrace (A' ∘L A - B' ∘L B) = opTrace (A' ∘L A) - opTrace (B' ∘L B) := by
  rw [opTrace, opTrace, opTrace, ← Summable.tsum_sub (summable_inner_diag_comp hA' hA _)
    (summable_inner_diag_comp hB' hB _)]
  exact tsum_congr fun i => by rw [sub_apply, inner_sub_right]

/-- `‖R B‖²_HS = ‖B‖²_HS - ‖C B‖²_HS` whenever `R*R = I - C*C`. -/
theorem hsNormSq_defect_comp {C R : H →L[ℂ] H}
    (hR : adjoint R ∘L R = ContinuousLinearMap.id ℂ H - adjoint C ∘L C) {B : K →L[ℂ] H}
    (hB : IsHilbertSchmidt B) :
    ContinuousLinearMap.hsNormSq (R ∘L B)
      = ContinuousLinearMap.hsNormSq B - ContinuousLinearMap.hsNormSq (C ∘L B) := by
  have hnorm : ∀ y : H, ‖R y‖ ^ 2 = ‖y‖ ^ 2 - ‖C y‖ ^ 2 := by
    intro y
    have h := congrArg (fun A : H →L[ℂ] H => RCLike.re ⟪y, A y⟫_ℂ) hR
    simp only [comp_apply, sub_apply, id_apply, adjoint_inner_right, inner_sub_right,
      map_sub] at h
    rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq, inner_self_eq_norm_sq] at h
    exact h
  rw [ContinuousLinearMap.hsNormSq, ContinuousLinearMap.hsNormSq, ContinuousLinearMap.hsNormSq,
    ← Summable.tsum_sub hB (hB.comp_left C)]
  exact tsum_congr fun i => by rw [comp_apply, comp_apply, hnorm]

/-- **(PHSG.12), abstract form.**  If `B B* - C B B* C* = P` and `R*R = I - C*C`, then the
incidence `R B B* R*` has trace `tr P`. -/
theorem opTrace_steinIncidence_eq {C R : H →L[ℂ] H}
    (hR : adjoint R ∘L R = ContinuousLinearMap.id ℂ H - adjoint C ∘L C) {B : K →L[ℂ] H}
    (hB : IsHilbertSchmidt B) {P : H →L[ℂ] H}
    (hP : B ∘L adjoint B - (C ∘L B) ∘L adjoint (C ∘L B) = P) :
    opTrace ((R ∘L B) ∘L adjoint (R ∘L B)) = opTrace P := by
  rw [← hP, opTrace_sub_of_hs hB.adjoint hB (hB.comp_left C).adjoint (hB.comp_left C),
    opTrace_comp_adjoint_self hB, opTrace_comp_adjoint_self (hB.comp_left C),
    opTrace_comp_adjoint_self (hB.comp_left R), hsNormSq_defect_comp hR hB]
  push_cast
  ring

end SteinTrace

theorem adjoint_sqrtExitDefect : adjoint sqrtExitDefect = sqrtExitDefect := by
  rw [sqrtExitDefect, _root_.HTGeometry.adjoint_ellTwoDiagonal]
  congr 1
  funext n
  rw [Complex.conj_ofReal]

theorem adjoint_sqrtExitDefect_comp_eq_fracture :
    adjoint sqrtExitDefect ∘L sqrtExitDefect
      = ContinuousLinearMap.id ℂ _ - adjoint primeHodgeHistorySurvivalShift ∘L
          primeHodgeHistorySurvivalShift := by
  rw [adjoint_sqrtExitDefect_comp, primeHodgeHistoryExitDefect_eq_adjoint_fracture]

/-- The reachability synthesis `K c = ∑ c_n √m_n e_n`, with `G = K K*`. -/
abbrev reachabilitySynthesis : HistoryScalar →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  recordSynthesis (E := ℂ) (fun n => ((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ))
    summable_sqrt_m_sq

theorem steinGramian_eq_synthesis :
    steinGramian = reachabilitySynthesis ∘L adjoint reachabilitySynthesis := rfl

/-- **(PHSG.12).**  `tr Φ = tr G - tr(C G C*) = tr P₀ = 1`, by trace cyclicity. -/
theorem opTrace_steinIncidence_eq_sourcePort :
    opTrace steinIncidence = opTrace sourcePort ∧ opTrace sourcePort = 1 := by
  have hB := isHilbertSchmidt_recordSynthesis (E := ℂ)
    (fun n => ((Real.sqrt (PrimeHodgeHistory.m n) : ℝ) : ℂ)) summable_sqrt_m_sq
  have hP : reachabilitySynthesis ∘L adjoint reachabilitySynthesis
      - (primeHodgeHistorySurvivalShift ∘L reachabilitySynthesis) ∘L
          adjoint (primeHodgeHistorySurvivalShift ∘L reachabilitySynthesis) = sourcePort := by
    rw [← steinGramian_stein, steinGramian_eq_synthesis, adjoint_comp]
    rfl
  have h := opTrace_steinIncidence_eq adjoint_sqrtExitDefect_comp_eq_fracture hB hP
  have hΦ : (sqrtExitDefect ∘L reachabilitySynthesis) ∘L
      adjoint (sqrtExitDefect ∘L reachabilitySynthesis) = steinIncidence := by
    rw [adjoint_comp, adjoint_sqrtExitDefect, steinIncidence, steinGramian_eq_synthesis]
    rfl
  rw [hΦ] at h
  refine ⟨h, ?_⟩
  rw [← h]
  exact steinIncidence_nuclear.2.2.1

/-! ## Reconstruction of the prime–Hodge defects -/

theorem inner_historyCoord_steinIncidence (n : ℕ) :
    ⟪historyCoord n, steinIncidence (historyCoord n)⟫_ℂ = (PrimeHodgeHistory.w n : ℂ) := by
  rw [steinIncidence_basis, inner_smul_right, inner_historyCoord, if_pos rfl, mul_one]

/-- **(PHSG.13).**  The separable prime–history defect is `Φ ⊗ A_form`: its history weights are
the diagonal of the Stein incidence. -/
theorem historyDefect_eq_steinIncidence_tensor (t : ℝ) :
    historyDefect t = historyMap
      (fun n => ⟪historyCoord n, steinIncidence (historyCoord n)⟫_ℂ)
      (fun n => by
        rw [inner_historyCoord_steinIncidence]
        exact historyFlux_norm_le n)
      (stokesCubicUnit t) := by
  rw [historyDefect, fluxTensor]
  exact historyMap_congr _ _ (funext fun n => (inner_historyCoord_steinIncidence n).symm) _

section GradeEmbedding

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (u : ℕ → E) (hu : ∀ n, ‖u n‖ = 1)

omit [CompleteSpace E] in
include hu in
theorem memℓp_gradeEmbedding (c : HistoryScalar) : Memℓp (fun n => c n • u n) 2 := by
  refine (memℓp_gen_iff two_toReal_pos).mpr ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have hs := (lp.memℓp c).summable two_toReal_pos
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
  exact hs.congr fun n => by rw [norm_smul, hu, mul_one]

/-- The grade embedding `c ↦ (c_n u_n)_n` as a linear map. -/
def gradeEmbeddingLinear : HistoryScalar →ₗ[ℂ] HistoryL2 E where
  toFun c := ⟨fun n => c n • u n, memℓp_gradeEmbedding u hu c⟩
  map_add' c d := by
    ext n
    simp [add_smul]
  map_smul' a c := by
    ext n
    simp [smul_smul]

omit [CompleteSpace E] in
theorem norm_gradeEmbeddingLinear (c : HistoryScalar) : ‖gradeEmbeddingLinear u hu c‖ = ‖c‖ := by
  have h1 := norm_sq_historyL2 (gradeEmbeddingLinear u hu c)
  have h2 := norm_sq_lp_eq_tsum c
  have h3 : ∑' n, ‖(gradeEmbeddingLinear u hu c) n‖ ^ 2 = ∑' n, ‖c n‖ ^ 2 :=
    tsum_congr fun n => by
      change ‖c n • u n‖ ^ 2 = _
      rw [norm_smul, hu, mul_one]
  rw [h3, ← h2] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

/-- **(PHSG.14).**  The isometric grade embedding `V δ_n = u_n` in grade `n`. -/
def gradeEmbedding : HistoryScalar →L[ℂ] HistoryL2 E :=
  (gradeEmbeddingLinear u hu).mkContinuous 1 fun c => by
    rw [norm_gradeEmbeddingLinear, one_mul]

omit [CompleteSpace E] in
theorem gradeEmbedding_apply (c : HistoryScalar) (n : ℕ) :
    gradeEmbedding u hu c n = c n • u n := rfl

omit [CompleteSpace E] in
theorem norm_gradeEmbedding_apply (c : HistoryScalar) : ‖gradeEmbedding u hu c‖ = ‖c‖ :=
  norm_gradeEmbeddingLinear u hu c

theorem adjoint_gradeEmbedding_apply (f : HistoryL2 E) (n : ℕ) :
    adjoint (gradeEmbedding u hu) f n = ⟪u n, f n⟫_ℂ := by
  have hsingle : gradeEmbedding u hu (lp.single 2 n (1 : ℂ)) = lp.single 2 n (u n) := by
    ext k
    rw [gradeEmbedding_apply, lp.single_apply, lp.single_apply]
    by_cases h : k = n
    · subst h
      simp
    · simp [h]
  have h := adjoint_inner_right (gradeEmbedding u hu) (lp.single 2 n (1 : ℂ)) f
  rw [lp.inner_single_left, hsingle, lp.inner_single_left] at h
  rw [← h]
  simp

/-- `V diag(|s_n|²) V* = ⊕ₙ |s_n u_n⟩⟨s_n u_n|`. -/
theorem gradeEmbedding_conj_recordOp {s : ℕ → ℂ} (hs : Summable fun n => ‖s n‖ ^ 2)
    (hsu : Summable fun n => ‖s n • u n‖ ^ 2) :
    gradeEmbedding u hu ∘L recordOp (E := ℂ) s hs ∘L adjoint (gradeEmbedding u hu)
      = recordOp (fun n => s n • u n) hsu := by
  ext f n
  rw [comp_apply, comp_apply, gradeEmbedding_apply, recordOp_apply, recordOp_apply,
    adjoint_gradeEmbedding_apply, inner_smul_left, smul_smul]
  congr 1
  rw [smul_eq_mul, RCLike.inner_apply]
  ring

end GradeEmbedding

theorem norm_hodgeExitVector (n : ℕ) :
    ‖collisionExitVector expPairLaw n‖ = Real.sqrt (PrimeHodgeHistory.w n) := by
  rw [← norm_hodgeExitVector_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The normalized exit directions `u_n = e_n/‖e_n‖`. -/
def hodgeExitDirection (n : ℕ) : Lp ℂ 2 expPairLaw :=
  (((Real.sqrt (PrimeHodgeHistory.w n))⁻¹ : ℝ) : ℂ) • collisionExitVector expPairLaw n

theorem norm_hodgeExitDirection (n : ℕ) : ‖hodgeExitDirection n‖ = 1 := by
  have hw := Real.sqrt_pos.mpr (PrimeHodgeHistory.w_pos n)
  rw [hodgeExitDirection, norm_smul, norm_hodgeExitVector, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hw), inv_mul_cancel₀ hw.ne']

/-- The formation embedding `V e_n = f_n/√w_n`. -/
abbrev formationEmbedding : HistoryScalar →L[ℂ] HistoryL2 (Lp ℂ 2 expPairLaw) :=
  gradeEmbedding hodgeExitDirection norm_hodgeExitDirection

/-- **(PHSG.15).**  The Cayley-collision record is `𝖳 = V Φ V*`. -/
theorem hodgeCollisionRecord_eq_formation_conj :
    formationEmbedding ∘L steinIncidence ∘L adjoint formationEmbedding = hodgeCollisionRecord := by
  have hsu : Summable fun n =>
      ‖((Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ) • hodgeExitDirection n‖ ^ 2 :=
    summable_sqrt_w_sq.congr fun n => by rw [norm_smul, norm_hodgeExitDirection, mul_one]
  rw [steinIncidence_eq, gradeEmbedding_conj_recordOp _ _ summable_sqrt_w_sq hsu]
  refine recordOp_congr _ _ _ (funext fun n => ?_)
  have hw := (Real.sqrt_pos.mpr (PrimeHodgeHistory.w_pos n)).ne'
  rw [hodgeExitDirection, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hw,
    Complex.ofReal_one, one_smul]

/-- **ULF-PHSG-001.**  The source Gramian `G = ∑ Cʲ P₀ C*ʲ = diag(m_n)` is the unique bounded
solution of `G - C G C* = P₀`, with `tr G = ‖G‖₁ = 7/4`; the Stein incidence `Φ = Δ^{1/2} G Δ^{1/2}`
is `diag(w_n)`, positive nuclear with `tr Φ = ‖Φ‖₁ = tr P₀ = 1` and `‖Φ‖ = 2/3`; it reconstructs
the separable defect as `Φ ⊗ A_form` and the Cayley-collision record as `V Φ V*`; and
`tr G = 7/4`, `tr Φ = tr 𝖳 = 1 = -ind C`. -/
theorem prime_hodge_stein_gramian_reconstruction :
    steinGramian - primeHodgeHistorySurvivalShift ∘L steinGramian ∘L
        adjoint primeHodgeHistorySurvivalShift = sourcePort ∧
      (∀ X, X - primeHodgeHistorySurvivalShift ∘L X ∘L adjoint primeHodgeHistorySurvivalShift
        = sourcePort → X = steinGramian) ∧
      Tendsto (fun N => traceNorm (lp (fun _ : ℕ => ℂ) 2) (steinGramian -
        ∑ j ∈ Finset.range N, (primeHodgeHistorySurvivalShift ^ j) ∘L sourcePort ∘L
          adjoint (primeHodgeHistorySurvivalShift ^ j))) atTop (𝓝 0) ∧
      opTrace steinGramian = ((7 / 4 : ℝ) : ℂ) ∧
      traceNorm (lp (fun _ : ℕ => ℂ) 2) steinGramian = 7 / 4 ∧
      steinIncidence.IsPositive ∧ MemSchattenClass 1 steinIncidence ∧
      opTrace steinIncidence = opTrace sourcePort ∧ opTrace sourcePort = 1 ∧
      traceNorm (lp (fun _ : ℕ => ℂ) 2) steinIncidence = 1 ∧ ‖steinIncidence‖ = 2 / 3 ∧
      (∀ n, steinIncidence (historyCoord n) = (PrimeHodgeHistory.w n : ℂ) • historyCoord n) ∧
      formationEmbedding ∘L steinIncidence ∘L adjoint formationEmbedding = hodgeCollisionRecord ∧
      opTrace hodgeCollisionRecord = 1 ∧
      primeHodgeHistorySurvivalShiftIndex = -1 := by
  obtain ⟨-, -, hG3, hG4⟩ := steinGramian_traceClass
  obtain ⟨hΦ1, hΦ2, -, hΦ4, hΦ5⟩ := steinIncidence_nuclear
  obtain ⟨hP1, hP2⟩ := opTrace_steinIncidence_eq_sourcePort
  exact ⟨steinGramian_stein, fun X hX => eq_steinGramian_of_stein hX,
    tendsto_traceNorm_steinGramian_sub, hG3, hG4, hΦ1, hΦ2, hP1, hP2, hΦ4, hΦ5,
    steinIncidence_basis, hodgeCollisionRecord_eq_formation_conj,
    hodgeCollisionRecord_nuclear.2.2.2.1, primeHodgeHistorySurvivalShiftIndex_eq_neg_one⟩

end GaloisForLFunctions.HTGeometry
