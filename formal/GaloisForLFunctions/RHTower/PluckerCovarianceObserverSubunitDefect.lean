import GaloisForLFunctions.RHTower.PluckerCovarianceSquareRootPurification
import GaloisForLFunctions.RHTower.PhysicalPluckerThetaLift
import GaloisForLFunctions.HTGeometry.HistoryRecordOperator

/-!
# Closed-observer subunit defect of the purified Plücker covariance history

With the theta first-exit weights `w_n = 630/((2n+3)(2n+5)(2n+7)(2n+9))` (`w_0 = 2/3`,
`w_1 = 2/11`) and the canonical purifications `u_n = √A_n` of the full physical covariances:

* **`(PCPOS.8)`–`(PCPOS.10)`** the open history `Ω = ∑ √w_n δ_n ⊗ u_n` is a unit vector and closing
  the history observer gives `T = Tr_history |Ω⟩⟨Ω| = ∑ w_n |u_n⟩⟨u_n|`.
* **Theorem PCPOS, `(PCPOS.11)`–`(PCPOS.16)`** `T ≥ 0`, `T ∈ S₁`, `Tr T = ‖T‖₁ = 1` and
  `‖T‖² ≤ Tr T² ≤ 1 - (8/33)(1 - F₀₁²) < 1`, `F₀₁ = |⟨u_0, u_1⟩|`; the signed wall `sign(t) T` is
  odd with trace `sign t` and trace norm `|sign t|`.
* **`(PCPOS.16a)`–`(PCPOS.16b)`** `Δ_{n,k} = 1 - |⟨u_n, u_k⟩|²` is the `2 × 2` Gram determinant and
  `1 - Tr T² = ∑_{n,k} w_n w_k Δ_{n,k}`, which vanishes exactly when all the rays coincide.
* **§5, `(PCPOS.17)`–`(PCPOS.20)`** on the marked rays `ε_n = δ_n ⊗ u_n` the shift
  `C = J C_θ J*` satisfies `C ε_n = √r_n ε_{n+1}` and `C J = J C_θ` with `ind C_θ = -1`;
  `C*C - CC* = ∑ k_n |ε_n⟩⟨ε_n|` is positive trace class of trace `1 = -ind C_θ`; the first-exit
  law reconstructs `r_n`, `m_n`, `w_n`; the exit defect `T̂ = ∑ w_n |ε_n⟩⟨ε_n|` closes to `T`.
* **§6** a positive unital map on an operator system is contractive on positive elements, so it
  never sends `T` to an operator of norm one (for instance a rank-one projection).
-/

open Filter Topology
open scoped InnerProductSpace ENNReal
open ContinuousLinearMap InnerProductSpace

noncomputable section

namespace RHTower.HedenmalmThetaSource

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower

/-! ### Dephased records are frame operators of graded rays -/

section Record

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

omit [InnerProductSpace ℂ K] [CompleteSpace K] in
theorem summable_norm_sq_gradedRay {v : ℕ → K} (hv : Summable fun n => ‖v n‖ ^ 2) :
    Summable fun n => ‖(lp.single 2 n (v n) : HistoryL2 K)‖ ^ 2 := by
  refine hv.congr fun n => ?_
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2)]

/-- The dephased record `⊕_n |v_n⟩⟨v_n|` is the frame operator of the graded rays `δ_n ⊗ v_n`. -/
theorem recordOp_eq_frameOperator {v : ℕ → K} (hv : Summable fun n => ‖v n‖ ^ 2) :
    recordOp v hv = frameOperator fun n => (lp.single 2 n (v n) : HistoryL2 K) := by
  have hs := summable_norm_sq_gradedRay hv
  ext1 f
  refine lp.ext (funext fun n => ?_)
  rw [recordOp_apply, frameOperator_apply hs]
  have hsum : Summable fun m => ⟪(lp.single 2 m (v m) : HistoryL2 K), f⟫_ℂ •
      (lp.single 2 m (v m) : HistoryL2 K) :=
    (Summable.of_norm (summable_norm_rankOne_frame hs)).mapL (ContinuousLinearMap.apply ℂ _ f)
  have hev : ∀ g : HistoryL2 K, lp.evalCLM ℂ (fun _ : ℕ => K) 2 n g = g n := fun _ => rfl
  have h := (lp.evalCLM ℂ (fun _ : ℕ => K) 2 n).map_tsum hsum
  rw [hev] at h
  rw [h, tsum_eq_single n]
  · rw [hev, lp.coeFn_smul, Pi.smul_apply, lp.single_apply_self, lp.inner_single_left]
  · intro m hm
    rw [hev, lp.coeFn_smul, Pi.smul_apply, lp.single_apply_ne _ _ _ (Ne.symm hm), smul_zero]

/-- **Closing the history of a record.**  The partial trace over `ℓ²(ℕ)` of `⊕_n |v_n⟩⟨v_n|` is
the frame operator `∑ |v_n⟩⟨v_n|`. -/
theorem recordOp_isPartialTrace {v : ℕ → K} (hv : Summable fun n => ‖v n‖ ^ 2) :
    IsPartialTrace (recordOp v hv) (frameOperator v) := by
  have hs := summable_norm_sq_gradedRay hv
  refine ⟨frameOperator_memSchattenClass_one hv, fun B => ?_⟩
  rw [recordOp_eq_frameOperator hv, opTrace_frameOperator_comp hv, opTrace_frameOperator_comp hs]
  refine tsum_congr fun n => ?_
  have hamp : ampliation ℕ B (lp.single 2 n (v n)) = lp.single 2 n (B (v n)) := by
    refine lp.ext (funext fun m => ?_)
    rw [ampliation_apply, lp.single_apply, lp.single_apply]
    by_cases h : m = n
    · subst h; simp
    · simp [h]
  rw [hamp, lp.inner_single_left, lp.single_apply_self]

end Record

/-! ### `(PCPOS.8)`–`(PCPOS.10)`: one open history and one closed observer -/

theorem thetaWeight_one : PrimeHodgeHistory.w 1 = 2 / 11 := by
  norm_num [PrimeHodgeHistory.w, PrimeHodgeHistory.m]

/-- The observer ray `√w_n u_n`. -/
def observerRay (n : ℕ) : PacketHilbertSchmidt :=
  ((Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ) • purifiedCovariance n

theorem norm_sq_observerRay (n : ℕ) : ‖observerRay n‖ ^ 2 = PrimeHodgeHistory.w n := by
  rw [observerRay, norm_smul, norm_purifiedCovariance, mul_one, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (PrimeHodgeHistory.w_pos n).le]

theorem summable_norm_sq_observerRay : Summable fun n => ‖observerRay n‖ ^ 2 := by
  simp_rw [norm_sq_observerRay]
  exact PrimeHodgeHistory.summable_w

theorem tsum_norm_sq_observerRay : ∑' n, ‖observerRay n‖ ^ 2 = 1 := by
  simp_rw [norm_sq_observerRay]
  exact PrimeHodgeHistory.tsum_w

/-- **`(PCPOS.9)`** the coherent open history `Ω = ∑ √w_n δ_n ⊗ u_n`. -/
def openHistory : HistoryL2 PacketHilbertSchmidt :=
  framePurification observerRay summable_norm_sq_observerRay

theorem norm_openHistory : ‖openHistory‖ = 1 := by
  have h := norm_sq_framePurification summable_norm_sq_observerRay
  rw [tsum_norm_sq_observerRay] at h
  change ‖openHistory‖ ^ 2 = 1 at h
  have h0 := norm_nonneg openHistory
  nlinarith [sq_nonneg (‖openHistory‖ - 1)]

/-- **`(PCPOS.10)`** the closed-observer defect `T = ∑ w_n |u_n⟩⟨u_n|`. -/
def closedObserverDefect : PacketHilbertSchmidt →L[ℂ] PacketHilbertSchmidt :=
  frameOperator observerRay

theorem closedObserverDefect_eq_tsum :
    closedObserverDefect = ∑' n, (PrimeHodgeHistory.w n : ℂ) •
      rankOne ℂ (purifiedCovariance n) (purifiedCovariance n) := by
  rw [closedObserverDefect, frameOperator]
  refine tsum_congr fun n => ?_
  ext1 x
  rw [observerRay, rankOne_apply, smul_apply, rankOne_apply, inner_smul_left, smul_smul,
    smul_smul, Complex.conj_ofReal]
  congr 1
  have hc : ((Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ) *
      ((Real.sqrt (PrimeHodgeHistory.w n) : ℝ) : ℂ) = (PrimeHodgeHistory.w n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (PrimeHodgeHistory.w_pos n).le]
  linear_combination ⟪purifiedCovariance n, x⟫_ℂ * hc

/-- **`(PCPOS.10)`** closing the history observer of `|Ω⟩⟨Ω|` gives `T`. -/
theorem closedObserverDefect_isPartialTrace :
    IsPartialTrace (rankOne ℂ openHistory openHistory) closedObserverDefect :=
  frameOperator_isPartialTrace summable_norm_sq_observerRay

/-! ### Theorem PCPOS -/

/-- `F₀₁ = |Tr(√A_0 √A_1)| = |⟨u_0, u_1⟩|`. -/
def pluckerFidelity : ℝ := ‖⟪purifiedCovariance 0, purifiedCovariance 1⟫_ℂ‖

/-- **Theorem PCPOS, `(PCPOS.11)`**: `T ≥ 0`, `T ∈ S₁`, `Tr T = ‖T‖₁ = 1`. -/
theorem closedObserverDefect_density :
    closedObserverDefect.IsPositive ∧ MemSchattenClass 1 closedObserverDefect ∧
      opTrace closedObserverDefect = 1 ∧ traceNorm _ closedObserverDefect = 1 := by
  have hs := summable_norm_sq_observerRay
  refine ⟨frameOperator_isPositive hs, frameOperator_memSchattenClass_one hs, ?_, ?_⟩
  · rw [closedObserverDefect, opTrace_frameOperator hs, tsum_norm_sq_observerRay,
      Complex.ofReal_one]
  · rw [closedObserverDefect, traceNorm_frameOperator hs, tsum_norm_sq_observerRay]

theorem inner_observerRay (n k : ℕ) :
    ⟪observerRay n, observerRay k⟫_ℂ =
      ((Real.sqrt (PrimeHodgeHistory.w n) * Real.sqrt (PrimeHodgeHistory.w k) : ℝ) : ℂ) *
        ⟪purifiedCovariance n, purifiedCovariance k⟫_ℂ := by
  rw [observerRay, observerRay, inner_smul_left, inner_smul_right, Complex.conj_ofReal,
    ← mul_assoc, Complex.ofReal_mul]

theorem norm_inner_observerRay_sq (n k : ℕ) :
    ‖⟪observerRay n, observerRay k⟫_ℂ‖ ^ 2 =
      PrimeHodgeHistory.w n * PrimeHodgeHistory.w k *
        ‖⟪purifiedCovariance n, purifiedCovariance k⟫_ℂ‖ ^ 2 := by
  rw [inner_observerRay, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    mul_pow, Real.sq_sqrt (PrimeHodgeHistory.w_pos n).le,
    Real.sq_sqrt (PrimeHodgeHistory.w_pos k).le]

/-- The purity `Tr T² = ∑_{n,k} w_n w_k |⟨u_n, u_k⟩|²`. -/
def observerPurity : ℝ :=
  ∑' k, ∑' n, PrimeHodgeHistory.w n * PrimeHodgeHistory.w k *
    ‖⟪purifiedCovariance n, purifiedCovariance k⟫_ℂ‖ ^ 2

/-- **`(PCPOS.15)`** `Tr T² = ∑_{n,k} w_n w_k |⟨u_n, u_k⟩|²`. -/
theorem opTrace_closedObserverDefect_sq :
    opTrace (closedObserverDefect ∘L closedObserverDefect) = (observerPurity : ℂ) := by
  rw [closedObserverDefect, opTrace_frameOperator_sq summable_norm_sq_observerRay, observerPurity]
  simp_rw [norm_inner_observerRay_sq]

/-- The two-history dispersion `Δ_{n,k} = 1 - |⟨u_n, u_k⟩|²`. -/
def historyDispersion (n k : ℕ) : ℝ := 1 - ‖⟪purifiedCovariance n, purifiedCovariance k⟫_ℂ‖ ^ 2

/-- **`(PCPOS.16a)`** `Δ_{n,k}` is the Gram determinant `det [[⟨u_n,u_n⟩, ⟨u_n,u_k⟩],
[⟨u_k,u_n⟩, ⟨u_k,u_k⟩]]`. -/
theorem historyDispersion_eq_gram (n k : ℕ) :
    historyDispersion n k = frameGramDeterminant (purifiedCovariance n) (purifiedCovariance k) ∧
      ((historyDispersion n k : ℝ) : ℂ) =
        Matrix.det !![⟪purifiedCovariance n, purifiedCovariance n⟫_ℂ,
          ⟪purifiedCovariance n, purifiedCovariance k⟫_ℂ;
          ⟪purifiedCovariance k, purifiedCovariance n⟫_ℂ,
          ⟪purifiedCovariance k, purifiedCovariance k⟫_ℂ] := by
  have h : historyDispersion n k =
      frameGramDeterminant (purifiedCovariance n) (purifiedCovariance k) := by
    rw [historyDispersion, frameGramDeterminant, norm_purifiedCovariance,
      norm_purifiedCovariance]
    ring
  exact ⟨h, by rw [h]; exact frameGramDeterminant_eq_det _ _⟩

theorem historyDispersion_nonneg (n k : ℕ) : 0 ≤ historyDispersion n k := by
  rw [(historyDispersion_eq_gram n k).1]
  exact frameGramDeterminant_nonneg _ _

theorem frameGramDeterminant_observerRay (n k : ℕ) :
    frameGramDeterminant (observerRay n) (observerRay k) =
      PrimeHodgeHistory.w n * PrimeHodgeHistory.w k * historyDispersion n k := by
  rw [frameGramDeterminant, norm_sq_observerRay, norm_sq_observerRay, norm_inner_observerRay_sq,
    historyDispersion]
  ring

/-- **`(PCPOS.16b)`** `1 - Tr T² = ∑_{n,k} w_n w_k Δ_{n,k}`. -/
theorem one_sub_observerPurity :
    1 - observerPurity =
      ∑' k, ∑' n, PrimeHodgeHistory.w n * PrimeHodgeHistory.w k * historyDispersion n k := by
  have h := one_sub_framePurity summable_norm_sq_observerRay tsum_norm_sq_observerRay
  simp_rw [norm_inner_observerRay_sq, frameGramDeterminant_observerRay] at h
  rw [observerPurity, h]

theorem summable_inner_dispersion (k : ℕ) :
    Summable fun n => PrimeHodgeHistory.w n * PrimeHodgeHistory.w k * historyDispersion n k := by
  have h := summable_frameGramDeterminant summable_norm_sq_observerRay k
  simpa only [frameGramDeterminant_observerRay] using h

theorem summable_outer_dispersion :
    Summable fun k => ∑' n, PrimeHodgeHistory.w n * PrimeHodgeHistory.w k *
      historyDispersion n k := by
  have h := summable_tsum_frameGramDeterminant summable_norm_sq_observerRay
    tsum_norm_sq_observerRay
  simpa only [frameGramDeterminant_observerRay] using h

theorem dispersion_term_nonneg (n k : ℕ) :
    0 ≤ PrimeHodgeHistory.w n * PrimeHodgeHistory.w k * historyDispersion n k :=
  mul_nonneg (mul_nonneg (PrimeHodgeHistory.w_pos n).le (PrimeHodgeHistory.w_pos k).le)
    (historyDispersion_nonneg n k)

/-- **`(PCPOS.16)`** keeping only the ordered pairs `(0, 1)` and `(1, 0)`:
`Tr T² ≤ 1 - (8/33)(1 - F₀₁²)`. -/
theorem observerPurity_le : observerPurity ≤ 1 - 8 / 33 * (1 - pluckerFidelity ^ 2) := by
  have hpair := sum_le_hasSum ({0, 1} : Finset ℕ)
    (fun k _ => tsum_nonneg fun n => dispersion_term_nonneg n k) summable_outer_dispersion.hasSum
  rw [Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)] at hpair
  have h0 : PrimeHodgeHistory.w 1 * PrimeHodgeHistory.w 0 * historyDispersion 1 0 ≤
      ∑' n, PrimeHodgeHistory.w n * PrimeHodgeHistory.w 0 * historyDispersion n 0 :=
    (summable_inner_dispersion 0).le_tsum 1 fun n _ => dispersion_term_nonneg n 0
  have h1 : PrimeHodgeHistory.w 0 * PrimeHodgeHistory.w 1 * historyDispersion 0 1 ≤
      ∑' n, PrimeHodgeHistory.w n * PrimeHodgeHistory.w 1 * historyDispersion n 1 :=
    (summable_inner_dispersion 1).le_tsum 0 fun n _ => dispersion_term_nonneg n 1
  have hsymm : historyDispersion 1 0 = historyDispersion 0 1 := by
    rw [historyDispersion, historyDispersion, ← norm_inner_symm]
  have hΔ : historyDispersion 0 1 = 1 - pluckerFidelity ^ 2 := rfl
  have hone := one_sub_observerPurity
  have hval : PrimeHodgeHistory.w 1 * PrimeHodgeHistory.w 0 * historyDispersion 1 0 +
      PrimeHodgeHistory.w 0 * PrimeHodgeHistory.w 1 * historyDispersion 0 1 =
      8 / 33 * (1 - pluckerFidelity ^ 2) := by
    rw [PrimeHodgeHistory.w_zero, thetaWeight_one, hsymm, hΔ]
    ring
  linarith

/-- **Theorem PCPOS, `(PCPOS.12)`**: `‖T‖ ≤ √(1 - (8/33)(1 - F₀₁²)) < 1`. -/
theorem norm_closedObserverDefect_le :
    ‖closedObserverDefect‖ ≤ Real.sqrt (1 - 8 / 33 * (1 - pluckerFidelity ^ 2)) ∧
      Real.sqrt (1 - 8 / 33 * (1 - pluckerFidelity ^ 2)) < 1 := by
  have hsq := norm_frameOperator_sq_le summable_norm_sq_observerRay
  simp_rw [norm_inner_observerRay_sq] at hsq
  change ‖closedObserverDefect‖ ^ 2 ≤ observerPurity at hsq
  have hF := fidelity_lt_one
  change pluckerFidelity < 1 at hF
  have hF0 : 0 ≤ pluckerFidelity := norm_nonneg _
  refine ⟨Real.le_sqrt_of_sq_le (hsq.trans observerPurity_le), ?_⟩
  rw [Real.sqrt_lt' one_pos]
  nlinarith

/-- **Theorem PCPOS, `(PCPOS.11)`**: `‖T‖ < 1`. -/
theorem norm_closedObserverDefect_lt_one : ‖closedObserverDefect‖ < 1 :=
  norm_closedObserverDefect_le.1.trans_lt norm_closedObserverDefect_le.2

/-- **`(PCPOS.16b)`, rigidity**: `1 - Tr T² = 0` exactly when every `Δ_{n,k}` vanishes, i.e. when
all the rays `u_n` coincide; here `1 - Tr T² > 0`. -/
theorem one_sub_observerPurity_eq_zero_iff :
    (1 - observerPurity = 0 ↔ ∀ n k, historyDispersion n k = 0) ∧ 0 < 1 - observerPurity := by
  have hpos : 0 < 1 - observerPurity := by
    have h := observerPurity_le
    have hF := fidelity_lt_one
    change pluckerFidelity < 1 at hF
    have hF0 : 0 ≤ pluckerFidelity := norm_nonneg _
    nlinarith
  refine ⟨⟨fun h => absurd h hpos.ne', fun hall => ?_⟩, hpos⟩
  rw [one_sub_observerPurity]
  simp [hall]

theorem historyDispersion_eq_zero_iff (n k : ℕ) :
    historyDispersion n k = 0 ↔ ∃ c : ℂ, purifiedCovariance k = c • purifiedCovariance n := by
  have hn : purifiedCovariance n ≠ 0 := fun h => by
    have := norm_purifiedCovariance n; rw [h, norm_zero] at this; exact zero_ne_one this
  have hk : purifiedCovariance k ≠ 0 := fun h => by
    have := norm_purifiedCovariance k; rw [h, norm_zero] at this; exact zero_ne_one this
  rw [historyDispersion, sub_eq_zero]
  constructor
  · intro h
    have h1 : ‖⟪purifiedCovariance n, purifiedCovariance k⟫_ℂ‖ =
        ‖purifiedCovariance n‖ * ‖purifiedCovariance k‖ := by
      rw [norm_purifiedCovariance, norm_purifiedCovariance, one_mul]
      have h0 := norm_nonneg ⟪purifiedCovariance n, purifiedCovariance k⟫_ℂ
      nlinarith [sq_nonneg (‖⟪purifiedCovariance n, purifiedCovariance k⟫_ℂ‖ - 1)]
    obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff hn hk).1 h1
    exact ⟨r, hr⟩
  · rintro ⟨c, hc⟩
    have hc1 : ‖c‖ = 1 := by
      have := norm_purifiedCovariance k
      rwa [hc, norm_smul, norm_purifiedCovariance, mul_one] at this
    rw [hc, inner_smul_right, norm_mul, hc1, one_mul, inner_self_eq_norm_sq_to_K,
      norm_purifiedCovariance]
    simp

/-! ### `(PCPOS.13)`–`(PCPOS.14)`: the signed wall -/

/-- **`(PCPOS.13)`** `T(t) = sign(t) T`. -/
def signedObserverWall (t : ℝ) : PacketHilbertSchmidt →L[ℂ] PacketHilbertSchmidt :=
  (Real.sign t : ℂ) • closedObserverDefect

/-- **`(PCPOS.14)`** `T(-t) = -T(t)`, `T(0) = 0`, `T(t) ∈ S₁`, `Tr T(t) = sign t`,
`‖T(t)‖₁ = |sign t|`. -/
theorem signedObserverWall_laws (t : ℝ) :
    signedObserverWall (-t) = -signedObserverWall t ∧ signedObserverWall 0 = 0 ∧
      MemSchattenClass 1 (signedObserverWall t) ∧
      opTrace (signedObserverWall t) = Real.sign t ∧
      traceNorm _ (signedObserverWall t) = |Real.sign t| := by
  obtain ⟨-, hS1, htr, hnorm⟩ := closedObserverDefect_density
  refine ⟨?_, ?_, memSchattenClass_one_smul hS1 _, ?_, ?_⟩
  · rw [signedObserverWall, signedObserverWall, Real.sign_neg, Complex.ofReal_neg, neg_smul]
  · rw [signedObserverWall, Real.sign_zero, Complex.ofReal_zero, zero_smul]
  · rw [signedObserverWall, opTrace_smul, htr, mul_one]
  · rw [signedObserverWall, traceNorm_smul, hnorm, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-! ### §5: the homotopy defect on the marked rays -/

/-- The marked embedding `J e_n = ε_n = δ_n ⊗ u_n`. -/
def markedEmbedding : HistoryScalar →L[ℂ] HistoryL2 PacketHilbertSchmidt :=
  gradeEmbedding purifiedCovariance norm_purifiedCovariance

/-- The marked ray `ε_n = δ_n ⊗ u_n`. -/
def markedRay (n : ℕ) : HistoryL2 PacketHilbertSchmidt := lp.single 2 n (purifiedCovariance n)

theorem markedEmbedding_single (n : ℕ) :
    markedEmbedding (lp.single 2 n 1) = markedRay n := by
  refine lp.ext (funext fun k => ?_)
  rw [markedEmbedding, gradeEmbedding_apply, markedRay, lp.single_apply, lp.single_apply]
  by_cases h : k = n
  · subst h; simp
  · simp [h]

/-- The marked rays are orthonormal. -/
theorem markedRay_orthonormal : Orthonormal ℂ markedRay := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [markedRay, markedRay, lp.inner_single_left, lp.single_apply]
  by_cases h : i = j
  · subst h
    simp [inner_self_eq_norm_sq_to_K, norm_purifiedCovariance]
  · simp [h]

theorem adjoint_markedEmbedding_comp :
    adjoint markedEmbedding ∘L markedEmbedding = ContinuousLinearMap.id ℂ _ := by
  refine ext_of_inner_single fun i j => ?_
  rw [comp_apply, adjoint_inner_right, markedEmbedding_single, markedEmbedding_single,
    id_apply, lp.inner_single_left, lp.single_apply]
  have h := markedRay_orthonormal
  rw [orthonormal_iff_ite] at h
  rw [h i j]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- **`(PCPOS.17)`** the marked shift `C = J C_θ J*`. -/
def markedShift : HistoryL2 PacketHilbertSchmidt →L[ℂ] HistoryL2 PacketHilbertSchmidt :=
  markedEmbedding ∘L primeHodgeHistorySurvivalShift ∘L adjoint markedEmbedding

/-- **`(PCPOS.17)`** `C J = J C_θ`: on the marked span `C` is unitarily equivalent to the theta
survival shift. -/
theorem markedShift_comp_embedding :
    markedShift ∘L markedEmbedding = markedEmbedding ∘L primeHodgeHistorySurvivalShift := by
  rw [markedShift, comp_assoc, comp_assoc, adjoint_markedEmbedding_comp, comp_id]

/-- **`(PCPOS.17)`** `C ε_n = √r_n ε_{n+1}`, `r_n = (2n+3)/(2n+9)`. -/
theorem markedShift_ray (n : ℕ) :
    markedShift (markedRay n) = primeHodgeHistorySurvivalWeight n • markedRay (n + 1) ∧
      PrimeHodgeHistory.survivalRatio n = ((2 * n + 3 : ℕ) : ℝ) / ((2 * n + 9 : ℕ) : ℝ) := by
  refine ⟨?_, PrimeHodgeHistory.survivalRatio_formula n⟩
  have h := congrArg (fun A => A (lp.single 2 n (1 : ℂ))) markedShift_comp_embedding
  simp only [comp_apply, markedEmbedding_single] at h
  rw [h]
  have hb := primeHodgeHistorySurvivalShift_basis n
  rw [HTGeometry.ellTwoCoordinateBasis_apply] at hb
  rw [hb, map_smul, HTGeometry.ellTwoCoordinateBasis_apply, markedEmbedding_single]

/-- The square roots `√k_n` of the relative curvature weights. -/
def relativeCurvatureRoot (n : ℕ) : ℂ :=
  ((Real.sqrt (PrimeHodgeHistory.relativeCurvatureWeight n) : ℝ) : ℂ)

theorem relativeCurvatureRoot_mul_self (n : ℕ) :
    relativeCurvatureRoot n * relativeCurvatureRoot n =
      (PrimeHodgeHistory.relativeCurvatureWeight n : ℂ) := by
  rw [relativeCurvatureRoot, ← Complex.ofReal_mul,
    Real.mul_self_sqrt (PrimeHodgeHistory.relativeCurvatureWeight_pos n).le]

theorem norm_sq_relativeCurvatureRoot (n : ℕ) :
    ‖relativeCurvatureRoot n‖ ^ 2 = PrimeHodgeHistory.relativeCurvatureWeight n := by
  rw [relativeCurvatureRoot, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (PrimeHodgeHistory.relativeCurvatureWeight_pos n).le]

theorem summable_norm_sq_relativeCurvatureRoot :
    Summable fun n => ‖relativeCurvatureRoot n‖ ^ 2 := by
  simp_rw [norm_sq_relativeCurvatureRoot]
  exact PrimeHodgeHistory.summable_relativeCurvatureWeight

/-- The relative curvature operator is the diagonal `(K y)_n = k_n y_n`. -/
theorem relativeCurvatureOperator_apply (y : ArithmeticDilationHilbert) (n : ℕ) :
    primeHodgeHistoryRelativeCurvatureOperator y n =
      (PrimeHodgeHistory.relativeCurvatureWeight n : ℂ) * y n := by
  have h := ((HilbertSchmidt.lpBasis ℕ).hasSum_repr y).mapL
    primeHodgeHistoryRelativeCurvatureOperator
  have hn := h.mapL (lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n)
  have hev : ∀ f : ArithmeticDilationHilbert, lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n f = f n :=
    fun _ => rfl
  simp only [hev, map_smul, primeHodgeHistoryRelativeCurvatureOperator_apply_basis] at hn
  rw [← hn.tsum_eq, tsum_eq_single n]
  · rw [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_smul, Pi.smul_apply, HilbertSchmidt.lpBasis_apply,
      lp.single_apply_self, HilbertBasis.repr_apply_apply, HilbertSchmidt.lpBasis_apply,
      lp.inner_single_left]
    simp only [RCLike.inner_apply, map_one, mul_one, smul_eq_mul]
    ring
  · intro m hm
    rw [lp.coeFn_smul, Pi.smul_apply, lp.coeFn_smul, Pi.smul_apply, HilbertSchmidt.lpBasis_apply,
      lp.single_apply_ne _ _ _ (Ne.symm hm), smul_zero, smul_zero]

theorem summable_norm_sq_relativeCurvatureRay :
    Summable fun n => ‖relativeCurvatureRoot n • purifiedCovariance n‖ ^ 2 := by
  refine summable_norm_sq_relativeCurvatureRoot.congr fun n => ?_
  rw [norm_smul, norm_purifiedCovariance, mul_one]

/-- The self-commutator record `∑ k_n |ε_n⟩⟨ε_n|`. -/
def markedSelfCommutatorRecord : HistoryL2 PacketHilbertSchmidt →L[ℂ]
    HistoryL2 PacketHilbertSchmidt :=
  recordOp (fun n => relativeCurvatureRoot n • purifiedCovariance n)
    summable_norm_sq_relativeCurvatureRay

/-- **`(PCPOS.18)`** `C*C - CC* = J (C_θ*C_θ - C_θC_θ*) J* = ∑ k_n |ε_n⟩⟨ε_n|`. -/
theorem markedShift_selfCommutator :
    adjoint markedShift ∘L markedShift - markedShift ∘L adjoint markedShift =
      markedSelfCommutatorRecord := by
  have hJ : ∀ z : HistoryScalar, adjoint markedEmbedding (markedEmbedding z) = z := fun z => by
    have h := congrArg (fun A => A z) adjoint_markedEmbedding_comp
    simpa using h
  have hK : ∀ y : ArithmeticDilationHilbert,
      adjoint primeHodgeHistorySurvivalShift (primeHodgeHistorySurvivalShift y) -
        primeHodgeHistorySurvivalShift (adjoint primeHodgeHistorySurvivalShift y) =
      primeHodgeHistoryRelativeCurvatureOperator y := fun y => by
    have h := congrArg (fun A => A y) survivalShift_selfCommutator_eq
    simpa using h
  have hadj : adjoint markedShift = markedEmbedding ∘L
      adjoint primeHodgeHistorySurvivalShift ∘L adjoint markedEmbedding := by
    rw [markedShift, adjoint_comp, adjoint_comp, adjoint_adjoint, comp_assoc]
  ext1 x
  have hL : (adjoint markedShift ∘L markedShift - markedShift ∘L adjoint markedShift) x =
      markedEmbedding (primeHodgeHistoryRelativeCurvatureOperator (adjoint markedEmbedding x)) := by
    rw [sub_apply, comp_apply, comp_apply, hadj, markedShift]
    simp only [comp_apply, hJ]
    rw [← map_sub, hK]
  rw [hL]
  refine lp.ext (funext fun n => ?_)
  rw [markedEmbedding, gradeEmbedding_apply, relativeCurvatureOperator_apply,
    adjoint_gradeEmbedding_apply, markedSelfCommutatorRecord, recordOp_apply, inner_smul_left,
    smul_smul, relativeCurvatureRoot, Complex.conj_ofReal, ← relativeCurvatureRoot,
    ← relativeCurvatureRoot_mul_self]
  ring_nf

/-- **`(PCPOS.18)`** `C*C - CC* ≥ 0`, `∈ S₁`, `Tr(C*C - CC*) = 1 = -ind C_θ`, and
`(C*C - CC*) ε_n = k_n ε_n`. -/
theorem markedSelfCommutator_traceClass :
    (adjoint markedShift ∘L markedShift - markedShift ∘L adjoint markedShift).IsPositive ∧
      MemSchattenClass 1 (adjoint markedShift ∘L markedShift - markedShift ∘L adjoint markedShift) ∧
      opTrace (adjoint markedShift ∘L markedShift - markedShift ∘L adjoint markedShift) = 1 ∧
      ((-primeHodgeHistorySurvivalShiftIndex : ℤ) : ℂ) = 1 ∧
      ∀ n, (adjoint markedShift ∘L markedShift - markedShift ∘L adjoint markedShift)
        (markedRay n) = (PrimeHodgeHistory.relativeCurvatureWeight n : ℂ) • markedRay n := by
  rw [markedShift_selfCommutator]
  obtain ⟨hpos, hS1, htr⟩ := recordOp_traceClass _ summable_norm_sq_relativeCurvatureRay
  refine ⟨hpos, hS1, ?_, ?_, fun n => ?_⟩
  · rw [markedSelfCommutatorRecord, htr]
    have : ∀ n, ‖relativeCurvatureRoot n • purifiedCovariance n‖ ^ 2 =
        PrimeHodgeHistory.relativeCurvatureWeight n := fun n => by
      rw [norm_smul, norm_purifiedCovariance, mul_one, norm_sq_relativeCurvatureRoot]
    simp_rw [this]
    rw [PrimeHodgeHistory.tsum_relativeCurvatureWeight, Complex.ofReal_one]
  · rw [primeHodgeHistorySurvivalShiftIndex_eq_neg_one]
    norm_num
  · refine lp.ext (funext fun m => ?_)
    rw [markedSelfCommutatorRecord, recordOp_apply, markedRay, lp.coeFn_smul, Pi.smul_apply]
    by_cases h : m = n
    · subst h
      rw [lp.single_apply_self, inner_smul_left, inner_self_eq_norm_sq_to_K,
        norm_purifiedCovariance, smul_smul]
      congr 1
      have hc := relativeCurvatureRoot_mul_self m
      rw [relativeCurvatureRoot, Complex.conj_ofReal, ← relativeCurvatureRoot]
      norm_num
      linear_combination hc
    · rw [lp.single_apply_ne _ _ _ h, inner_zero_right, zero_smul, smul_zero]

/-- **`(PCPOS.19)`** the first-exit law reconstructs the survival ratios, the survival masses and
the exit weights: `r_n = ∑_{j ≤ n} k_j`, `m_n = ∏_{j < n} r_j`, `w_n = m_n (1 - r_n)`. -/
theorem firstExit_reconstruction (n : ℕ) :
    PrimeHodgeHistory.survivalRatio n =
        ∑ j ∈ Finset.range (n + 1), PrimeHodgeHistory.relativeCurvatureWeight j ∧
      PrimeHodgeHistory.m n = ∏ j ∈ Finset.range n, PrimeHodgeHistory.survivalRatio j ∧
      PrimeHodgeHistory.w n =
        PrimeHodgeHistory.m n * (1 - PrimeHodgeHistory.survivalRatio n) :=
  ⟨PrimeHodgeHistory.survivalRatio_eq_sum_range_relativeCurvatureWeight n,
    PrimeHodgeHistory.m_eq_prod_survivalRatio n,
    PrimeHodgeHistory.w_eq_m_mul_one_sub_survivalRatio n⟩

/-- **`(PCPOS.20)`** the marked exit defect `T̂ = ∑ w_n |ε_n⟩⟨ε_n|`. -/
def markedExitDefect : HistoryL2 PacketHilbertSchmidt →L[ℂ] HistoryL2 PacketHilbertSchmidt :=
  recordOp observerRay summable_norm_sq_observerRay

/-- **`(PCPOS.20)`** `T̂ ≥ 0`, `T̂ ∈ S₁`, `Tr T̂ = 1`, `T̂ ε_n = w_n ε_n`, and closing the history
sends `T̂` to `T`. -/
theorem markedExitDefect_laws :
    markedExitDefect.IsPositive ∧ MemSchattenClass 1 markedExitDefect ∧
      opTrace markedExitDefect = 1 ∧
      (∀ n, markedExitDefect (markedRay n) = (PrimeHodgeHistory.w n : ℂ) • markedRay n) ∧
      IsPartialTrace markedExitDefect closedObserverDefect := by
  obtain ⟨hpos, hS1, htr⟩ := recordOp_traceClass observerRay summable_norm_sq_observerRay
  refine ⟨hpos, hS1, ?_, fun n => ?_, recordOp_isPartialTrace summable_norm_sq_observerRay⟩
  · rw [markedExitDefect, htr, tsum_norm_sq_observerRay, Complex.ofReal_one]
  · refine lp.ext (funext fun m => ?_)
    rw [markedExitDefect, recordOp_apply, markedRay, lp.coeFn_smul, Pi.smul_apply]
    by_cases h : m = n
    · subst h
      rw [lp.single_apply_self, observerRay, inner_smul_left, inner_self_eq_norm_sq_to_K,
        norm_purifiedCovariance, smul_smul, Complex.conj_ofReal]
      congr 1
      have hc : ((Real.sqrt (PrimeHodgeHistory.w m) : ℝ) : ℂ) *
          ((Real.sqrt (PrimeHodgeHistory.w m) : ℝ) : ℂ) = (PrimeHodgeHistory.w m : ℂ) := by
        rw [← Complex.ofReal_mul, Real.mul_self_sqrt (PrimeHodgeHistory.w_pos m).le]
      norm_num
      linear_combination hc
    · rw [lp.single_apply_ne _ _ _ h, inner_zero_right, zero_smul, smul_zero]

/-! ### §6: positive unital maps cannot reach the escape horizon -/

section PositiveUnital

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A positive unital map on an operator system is contractive on positive elements:
`0 ≤ Φ(X) ≤ ‖X‖ Φ(1) = ‖X‖`. -/
theorem norm_le_of_positive_unital (S : Submodule ℂ (E →L[ℂ] E)) (h1 : (1 : E →L[ℂ] E) ∈ S)
    (Φ : S →ₗ[ℂ] (F →L[ℂ] F))
    (hΦ : ∀ s : S, (s : E →L[ℂ] E).IsPositive → (Φ s).IsPositive) (hunit : Φ ⟨1, h1⟩ = 1)
    {X : E →L[ℂ] E} (hX : X ∈ S) (hXpos : X.IsPositive) : ‖Φ ⟨X, hX⟩‖ ≤ ‖X‖ := by
  have hY : (‖X‖ : ℂ) • (1 : E →L[ℂ] E) - X ∈ S := S.sub_mem (S.smul_mem _ h1) hX
  have hX0 : (0 : E →L[ℂ] E) ≤ X := (ContinuousLinearMap.nonneg_iff_isPositive X).2 hXpos
  have hXle : X ≤ (‖X‖ : ℂ) • (1 : E →L[ℂ] E) := by
    have h := IsSelfAdjoint.le_algebraMap_norm_self (a := X) hXpos.isSelfAdjoint
    rwa [Algebra.algebraMap_eq_smul_one, RCLike.real_smul_eq_coe_smul (K := ℂ)] at h
  have hYpos : ((‖X‖ : ℂ) • (1 : E →L[ℂ] E) - X).IsPositive :=
    (ContinuousLinearMap.le_def _ _).1 hXle
  have hΦY := hΦ ⟨_, hY⟩ hYpos
  have hsplit : (⟨(‖X‖ : ℂ) • (1 : E →L[ℂ] E) - X, hY⟩ : S) =
      (‖X‖ : ℂ) • ⟨1, h1⟩ - ⟨X, hX⟩ := rfl
  rw [hsplit, map_sub, map_smul, hunit] at hΦY
  have hle : Φ ⟨X, hX⟩ ≤ (‖X‖ : ℂ) • (1 : F →L[ℂ] F) := (ContinuousLinearMap.le_def _ _).2 hΦY
  have h0 : 0 ≤ Φ ⟨X, hX⟩ := (ContinuousLinearMap.nonneg_iff_isPositive _).2 (hΦ _ hXpos)
  calc ‖Φ ⟨X, hX⟩‖ ≤ ‖(‖X‖ : ℂ) • (1 : F →L[ℂ] F)‖ :=
        CStarAlgebra.norm_le_norm_of_nonneg_of_le h0 hle
    _ ≤ ‖X‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
        exact mul_le_of_le_one_right (norm_nonneg _) (norm_id_le)

end PositiveUnital

/-- **§6, selection lemma**: no positive unital map on an operator system containing `T` sends
`T` to an operator of norm one (in particular to a rank-one projection). -/
theorem positive_unital_ne_of_norm_eq_one {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (S : Submodule ℂ (PacketHilbertSchmidt →L[ℂ]
      PacketHilbertSchmidt)) (h1 : 1 ∈ S) (Φ : S →ₗ[ℂ] (F →L[ℂ] F))
    (hΦ : ∀ s : S, (s : PacketHilbertSchmidt →L[ℂ] PacketHilbertSchmidt).IsPositive →
      (Φ s).IsPositive) (hunit : Φ ⟨1, h1⟩ = 1) (hT : closedObserverDefect ∈ S)
    {P : F →L[ℂ] F} (hP : ‖P‖ = 1) : Φ ⟨closedObserverDefect, hT⟩ ≠ P := by
  intro h
  have hle := norm_le_of_positive_unital S h1 Φ hΦ hunit hT closedObserverDefect_density.1
  rw [h, hP] at hle
  exact absurd norm_closedObserverDefect_lt_one (not_lt.2 hle)

end RHTower.HedenmalmThetaSource
