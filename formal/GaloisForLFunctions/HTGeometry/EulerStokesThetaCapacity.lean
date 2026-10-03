import GaloisForLFunctions.HTGeometry.EulerStokesApertureCapacity

/-!
# The bi-six integral–nuclear object `T_cap = Φ ⊗ C`

Fusing the theta Mellin-six history flux `Φ = diag(w_n)` with the aperture capacity `C` gives
`T_cap = Φ ⊗ C` on `ℓ²(ℕ × I)` (**(ESAC.16)**), realized as the right Gram of the frame
`√(w_n s_i) e_n ⊗ ψ^{(6)}_{λ_i}`.  It is positive and trace class with
`Tr T_cap = ‖T_cap‖₁ = ` the primitive collision budget `< 115/108`, its sixth Sylvester power in the
prime clock is the form `(230/27) Φ ⊗ |c⟩⟨c|` (**(ESAC.17)**), and its history-tail trace is
`Tr((P_{[m,∞)} ⊗ I) T_cap) = m_m · budget` (**(ESAC.18)**).
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

local notation "ℓ²HE" => lp (fun _ : ℕ × EulerLabel => ℂ) 2

/-- The joint frame `√(w_n s_i) e_n ⊗ ψ^{(6)}_{λ_i}`. -/
def thetaCapacityFrame (a : ℕ × EulerLabel) : lp (fun _ : ℕ => HalfLineL2) 2 :=
  ((Real.sqrt (PrimeHodgeHistory.w a.1 * xiGammaEulerPrimitiveCubicLogMomentWeight a.2) : ℝ) : ℂ) •
    lp.single 2 a.1 (gammaCoherentVector 6 (xiGammaEulerPrimitiveLogFrequency_pos a.2))

theorem norm_sq_thetaCapacityFrame (a : ℕ × EulerLabel) :
    ‖thetaCapacityFrame a‖ ^ 2 =
      PrimeHodgeHistory.w a.1 * xiGammaEulerPrimitiveCubicLogMomentWeight a.2 := by
  rw [thetaCapacityFrame, norm_smul, lp.norm_single (by norm_num), norm_gammaCoherentVector, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (mul_nonneg (PrimeHodgeHistory.w_pos _).le
      (xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg _))]

theorem summable_thetaCapacityWeight :
    Summable fun a : ℕ × EulerLabel =>
      PrimeHodgeHistory.w a.1 * xiGammaEulerPrimitiveCubicLogMomentWeight a.2 := by
  have hw : Summable fun n => ‖PrimeHodgeHistory.w n‖ := by
    simpa [Real.norm_of_nonneg (PrimeHodgeHistory.w_pos _).le] using PrimeHodgeHistory.summable_w
  have hs : Summable fun i => ‖xiGammaEulerPrimitiveCubicLogMomentWeight i‖ := by
    simpa [Real.norm_of_nonneg (xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg _)] using
      summable_xiGammaEulerPrimitiveCubicLogMomentWeight
  exact summable_mul_of_summable_norm hw hs

theorem tsum_thetaCapacityWeight :
    ∑' a : ℕ × EulerLabel, PrimeHodgeHistory.w a.1 * xiGammaEulerPrimitiveCubicLogMomentWeight a.2 =
      routePPrimitiveCollisionCubicTraceBudget := by
  rw [tsum_mul_tsum_of_summable_norm (f := PrimeHodgeHistory.w)
      (g := xiGammaEulerPrimitiveCubicLogMomentWeight) ?_ ?_ |>.symm, PrimeHodgeHistory.tsum_w, one_mul]
  · rfl
  · simpa [Real.norm_of_nonneg (PrimeHodgeHistory.w_pos _).le] using PrimeHodgeHistory.summable_w
  · simpa [Real.norm_of_nonneg (xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg _)] using
      summable_xiGammaEulerPrimitiveCubicLogMomentWeight

theorem summable_norm_sq_thetaCapacityFrame : Summable fun a => ‖thetaCapacityFrame a‖ ^ 2 := by
  simp_rw [norm_sq_thetaCapacityFrame]
  exact summable_thetaCapacityWeight

/-- The joint synthesis. -/
def thetaCapacitySynthesis : ℓ²HE →L[ℂ] lp (fun _ : ℕ => HalfLineL2) 2 :=
  squareSummableSynthesis thetaCapacityFrame summable_norm_sq_thetaCapacityFrame

/-- **(ESAC.16)** `T_cap = Φ ⊗ C`. -/
def thetaCapacity : ℓ²HE →L[ℂ] ℓ²HE :=
  ContinuousLinearMap.adjoint thetaCapacitySynthesis ∘L thetaCapacitySynthesis

/-- **(ESAC.16)** `T_cap((n,i),(m,j)) = δ_{nm} w_n C(i,j)`. -/
theorem inner_single_thetaCapacity (a b : ℕ × EulerLabel) :
    ⟪(lp.single 2 a (1 : ℂ) : ℓ²HE), thetaCapacity (lp.single 2 b 1)⟫_ℂ =
      if a.1 = b.1 then (PrimeHodgeHistory.w a.1 : ℂ) * (capacityEntry a.2 b.2 : ℂ) else 0 := by
  obtain ⟨n, i⟩ := a
  obtain ⟨m, j⟩ := b
  rw [thetaCapacity, thetaCapacitySynthesis, inner_single_rightGram_single, thetaCapacityFrame,
    thetaCapacityFrame, inner_smul_left, inner_smul_right, Complex.conj_ofReal, lp.inner_single_left]
  simp only
  by_cases h : n = m
  · subst h
    rw [lp.single_apply_self, if_pos rfl, inner_gammaCoherentVector, ← (inner_single_capacityGram i j).2,
      Real.sqrt_mul (PrimeHodgeHistory.w_pos n).le, Real.sqrt_mul (PrimeHodgeHistory.w_pos n).le,
      Real.sqrt_mul (xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg i)]
    have hw := Real.mul_self_sqrt (PrimeHodgeHistory.w_pos n).le
    simp only [← Complex.ofReal_mul]
    congr 1
    linear_combination (Real.sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight i) *
      Real.sqrt (xiGammaEulerPrimitiveCubicLogMomentWeight j) *
        (2 * Real.sqrt (xiGammaEulerPrimitiveLogFrequency i * xiGammaEulerPrimitiveLogFrequency j) /
          (xiGammaEulerPrimitiveLogFrequency i + xiGammaEulerPrimitiveLogFrequency j)) ^ 6) * hw
  · rw [lp.single_apply_ne _ _ _ h, if_neg h, inner_zero_right, mul_zero, mul_zero]

/-- **(ESAC.17)** `T_cap ≥ 0`, `T_cap ∈ 𝒮₁`, `Tr T_cap = ‖T_cap‖₁ = ` budget `< 115/108`. -/
theorem thetaCapacity_traceClass :
    thetaCapacity.IsPositive ∧ MemSchattenClass 1 thetaCapacity ∧
      thetaCapacity.opTrace = (routePPrimitiveCollisionCubicTraceBudget : ℂ) ∧
      traceNorm ℓ²HE thetaCapacity = routePPrimitiveCollisionCubicTraceBudget ∧
      routePPrimitiveCollisionCubicTraceBudget < 115 / 108 := by
  obtain ⟨hpos, hS, htr⟩ := rightGram_traceClass summable_norm_sq_thetaCapacityFrame
  simp_rw [norm_sq_thetaCapacityFrame] at htr
  rw [tsum_thetaCapacityWeight] at htr
  refine ⟨hpos, hS, htr, ?_, routePPrimitiveCollisionCubicTraceBudget_lt_quantum⟩
  exact (traceNorm_eq_re_opTrace_of_isPositive hS hpos).trans (by rw [htr, Complex.ofReal_re])

/-- **(ESAC.17)** The sixth Sylvester power of `T_cap` in `I ⊗ L` is `(230/27) Φ ⊗ |c⟩⟨c|`. -/
theorem thetaCapacity_sixthBoundary_law (a b : ℕ × EulerLabel) :
    ((xiGammaEulerPrimitiveLogFrequency a.2 + xiGammaEulerPrimitiveLogFrequency b.2 : ℝ) : ℂ) ^ 6 *
        ⟪(lp.single 2 a (1 : ℂ) : ℓ²HE), thetaCapacity (lp.single 2 b 1)⟫_ℂ =
      if a.1 = b.1 then
        (((230 / 27 : ℝ) * PrimeHodgeHistory.w a.1 * sixthBoundaryVector a.2 *
          sixthBoundaryVector b.2 : ℝ) : ℂ) else 0 := by
  rw [inner_single_thetaCapacity]
  split_ifs
  · have h := sixthBoundary_law a.2 b.2
    rw [show (((230 / 27 : ℝ) * PrimeHodgeHistory.w a.1 * sixthBoundaryVector a.2 *
        sixthBoundaryVector b.2 : ℝ) : ℂ) = (PrimeHodgeHistory.w a.1 : ℂ) *
        (((230 / 27 : ℝ) * sixthBoundaryVector a.2 * sixthBoundaryVector b.2 : ℝ) : ℂ) by push_cast; ring,
      ← h]
    push_cast
    ring
  · rw [mul_zero]

/-- The history-tail projection `P_{[m,∞)} ⊗ I`. -/
def eulerHistoryTailProjection (m : ℕ) : ℓ²HE →L[ℂ] ℓ²HE :=
  lpDiagonalCLM (fun a : ℕ × EulerLabel => if m ≤ a.1 then (1 : ℂ) else 0) zero_le_one
    fun a => by split_ifs <;> simp

theorem adjoint_eulerHistoryTailProjection (m : ℕ) :
    ContinuousLinearMap.adjoint (eulerHistoryTailProjection m) = eulerHistoryTailProjection m := by
  symm
  refine (ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => ?_
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun a => ?_
  rw [show ((eulerHistoryTailProjection m x : ℓ²HE) : ℕ × EulerLabel → ℂ) a =
      (if m ≤ a.1 then (1 : ℂ) else 0) * x a from rfl,
    show ((eulerHistoryTailProjection m y : ℓ²HE) : ℕ × EulerLabel → ℂ) a =
      (if m ≤ a.1 then (1 : ℂ) else 0) * y a from rfl, RCLike.inner_apply, RCLike.inner_apply]
  split_ifs <;> simp

/-- **(ESAC.18)** `(P_{[m,∞)} ⊗ I) T_cap` is trace class with trace `m_m · ` budget. -/
theorem historyTail_trace_thetaCapacity (m : ℕ) :
    MemSchattenClass 1 (eulerHistoryTailProjection m ∘L thetaCapacity) ∧
      (eulerHistoryTailProjection m ∘L thetaCapacity).opTrace =
        ((PrimeHodgeHistory.m m * routePPrimitiveCollisionCubicTraceBudget : ℝ) : ℂ) := by
  have hV := squareSummableSynthesis_isHilbertSchmidt summable_norm_sq_thetaCapacityFrame
  have hfac : eulerHistoryTailProjection m ∘L thetaCapacity =
      ContinuousLinearMap.adjoint (thetaCapacitySynthesis ∘L eulerHistoryTailProjection m) ∘L
        thetaCapacitySynthesis := by
    rw [ContinuousLinearMap.adjoint_comp, adjoint_eulerHistoryTailProjection, thetaCapacity]
    rfl
  have hVP : (thetaCapacitySynthesis ∘L eulerHistoryTailProjection m).IsHilbertSchmidt :=
    hV.comp_right _
  have hS : MemSchattenClass 1 (eulerHistoryTailProjection m ∘L thetaCapacity) := by
    rw [hfac]
    exact memSchattenClass_one_comp hVP.adjoint hV
  refine ⟨hS, ?_⟩
  rw [opTrace_eq_tsum_basis_of_memSchattenClass_one hS (HilbertSchmidt.lpBasis _)]
  have hdiag : ∀ a : ℕ × EulerLabel, ⟪HilbertSchmidt.lpBasis _ a,
      (eulerHistoryTailProjection m ∘L thetaCapacity) (HilbertSchmidt.lpBasis _ a)⟫_ℂ =
      ((if m ≤ a.1 then PrimeHodgeHistory.w a.1 * xiGammaEulerPrimitiveCubicLogMomentWeight a.2
        else 0 : ℝ) : ℂ) := fun a => by
    rw [HilbertSchmidt.lpBasis_apply, ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.adjoint_inner_left, adjoint_eulerHistoryTailProjection, eulerHistoryTailProjection,
      lpDiagonalCLM_single]
    split_ifs with h
    · rw [inner_single_thetaCapacity, if_pos rfl, ← (inner_single_capacityGram a.2 a.2).2,
        Real.sqrt_mul_self (xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg _)]
      have hlam := xiGammaEulerPrimitiveLogFrequency_pos a.2
      rw [Real.sqrt_mul_self hlam.le, show 2 * xiGammaEulerPrimitiveLogFrequency a.2 /
        (xiGammaEulerPrimitiveLogFrequency a.2 + xiGammaEulerPrimitiveLogFrequency a.2) = 1 by
          field_simp; ring]
      push_cast
      ring
    · rw [show (lp.single 2 a (0 : ℂ) : ℓ²HE) = 0 by ext; simp, inner_zero_left]
      simp
  simp_rw [hdiag]
  rw [← Complex.ofReal_tsum]
  congr 1
  have hsplit : ∀ a : ℕ × EulerLabel, (if m ≤ a.1 then PrimeHodgeHistory.w a.1 *
      xiGammaEulerPrimitiveCubicLogMomentWeight a.2 else 0) =
      (if m ≤ a.1 then PrimeHodgeHistory.w a.1 else 0) * xiGammaEulerPrimitiveCubicLogMomentWeight a.2 :=
    fun a => by split_ifs <;> simp
  simp_rw [hsplit]
  have hwt : Summable fun n : ℕ => ‖(if m ≤ n then PrimeHodgeHistory.w n else 0)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (PrimeHodgeHistory.summable_w)
    split_ifs
    · rw [Real.norm_of_nonneg (PrimeHodgeHistory.w_pos _).le]
    · rw [norm_zero]
      exact (PrimeHodgeHistory.w_pos _).le
  have hs : Summable fun i => ‖xiGammaEulerPrimitiveCubicLogMomentWeight i‖ := by
    simpa [Real.norm_of_nonneg (xiGammaEulerPrimitiveCubicLogMomentWeight_nonneg _)] using
      summable_xiGammaEulerPrimitiveCubicLogMomentWeight
  rw [show (∑' a : ℕ × EulerLabel, (if m ≤ a.1 then PrimeHodgeHistory.w a.1 else 0) *
      xiGammaEulerPrimitiveCubicLogMomentWeight a.2) =
      ∑' z : ℕ × EulerLabel, (fun n : ℕ => if m ≤ n then PrimeHodgeHistory.w n else 0) z.1 *
        xiGammaEulerPrimitiveCubicLogMomentWeight z.2 from rfl,
    ← tsum_mul_tsum_of_summable_norm hwt hs]
  have htail : ∑' n : ℕ, (if m ≤ n then PrimeHodgeHistory.w n else 0) = PrimeHodgeHistory.m m := by
    have hsum : Summable fun n : ℕ => (if m ≤ n then PrimeHodgeHistory.w n else 0) := hwt.of_norm
    rw [← hsum.sum_add_tsum_nat_add m, Finset.sum_eq_zero fun n hn => by
      rw [if_neg (by simpa using hn)], zero_add, ← PrimeHodgeHistory.tail_tsum_w m]
    exact tsum_congr fun k => by rw [if_pos (by omega)]
  rw [htail]
  rfl

end GaloisForLFunctions.HTGeometry
