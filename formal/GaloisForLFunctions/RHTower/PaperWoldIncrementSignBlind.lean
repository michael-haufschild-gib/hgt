import GaloisForLFunctions.RHTower.PaperWoldFullOperator
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.HTGeometry.LpTwoMatrixOperators

/-!
# Masked Wold operators cannot see the arithmetic sign of the increments

Every masked directed Wold kernel factors as
`(n+1)^(2t) d_n d_j m(n,j) = s_n · (n+1)^(2t) |d_n| |d_j| m(n,j) · s_j`
with `s_n = ±1` the sign of the literal increment `d_n`.  Hence every masked Wold operator is
conjugate, by one diagonal sign involution, to the operator built from the magnitudes `|d_n|`.
All unitary invariants (norm, compactness) of the two operators agree.

The magnitudes are the increments of a fake residual with all jumps nonnegative.  Its partial sums
diverge: the logarithmic cells over even composite cutoffs already sum to infinity.  The literal
residual tends to zero.  So no property of masked Wold operators that is invariant under diagonal
sign conjugation distinguishes the prime number theorem from its maximal failure.
-/

namespace RHTower
noncomputable section
open Filter Topology GaloisForLFunctions GaloisForLFunctions.HTGeometry

/-- Sign of the literal natural Wold increment, as a unimodular multiplier. -/
def woldIncrementSign (n : ℕ) : ℂ :=
  if 0 ≤ xiHeatCassiniWoldNatIncrement n then 1 else -1

theorem norm_woldIncrementSign (n : ℕ) : ‖woldIncrementSign n‖ = 1 := by
  unfold woldIncrementSign; split_ifs <;> simp

theorem woldIncrementSign_mul_self (n : ℕ) : woldIncrementSign n * woldIncrementSign n = 1 := by
  unfold woldIncrementSign; split_ifs <;> norm_num

theorem woldIncrement_eq_sign_mul_abs (n : ℕ) :
    (xiHeatCassiniWoldNatIncrement n : ℂ) =
      woldIncrementSign n * (|xiHeatCassiniWoldNatIncrement n| : ℝ) := by
  unfold woldIncrementSign
  split_ifs with h
  · rw [abs_of_nonneg h, one_mul]
  · rw [abs_of_neg (lt_of_not_ge h)]; push_cast; ring

/-- The masked directed Wold kernel with every increment replaced by its magnitude. -/
def paperWoldMagnitudeKernel (p : PaperWoldStrictHalf) (m : PaperWoldMask) (q : ℕ × ℕ) : ℂ :=
  (m q : ℂ) * if q.1 < q.2 then
    ((((q.1 : ℝ) + 1) ^ (2 * p.t) * |xiHeatCassiniWoldNatIncrement q.1| *
      |xiHeatCassiniWoldNatIncrement q.2| : ℝ) : ℂ) else 0

/-- The literal masked kernel is the magnitude kernel conjugated by the increment signs. -/
theorem paperWoldMaskedKernel_eq_sign_conj (p : PaperWoldStrictHalf) (m : PaperWoldMask)
    (n j : ℕ) :
    paperWoldMaskedKernel p m (n, j) =
      woldIncrementSign n * paperWoldMagnitudeKernel p m (n, j) * woldIncrementSign j := by
  unfold paperWoldMaskedKernel paperWoldFullKernel paperWoldMagnitudeKernel paperWoldInteraction
  simp only [PaperWoldStrictHalf.nearParameters]
  split_ifs
  · push_cast
    rw [woldIncrement_eq_sign_mul_abs n, woldIncrement_eq_sign_mul_abs j]
    ring
  · simp

theorem norm_paperWoldMagnitudeKernel (p : PaperWoldStrictHalf) (m : PaperWoldMask)
    (q : ℕ × ℕ) : ‖paperWoldMagnitudeKernel p m q‖ = ‖paperWoldMaskedKernel p m q‖ := by
  obtain ⟨n, j⟩ := q
  rw [paperWoldMaskedKernel_eq_sign_conj, norm_mul, norm_mul, norm_woldIncrementSign,
    norm_woldIncrementSign, one_mul, mul_one]

theorem paperWoldMagnitudeKernel_isHS (p : PaperWoldStrictHalf) (m : PaperWoldMask) :
    HilbertSchmidt.IsHS (paperWoldMagnitudeKernel p m) :=
  (paperWoldMaskedKernel_isHS p m).congr fun q => by rw [norm_paperWoldMagnitudeKernel]

/-- The magnitude operator: the masked Wold operator of the all-nonnegative fake increments. -/
def paperWoldMagnitudeOperator (p : PaperWoldStrictHalf) (m : PaperWoldMask) :
    PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  HilbertSchmidt.toOperator (paperWoldMagnitudeKernel_isHS p m)

/-- Diagonal multiplication by the increment signs. -/
def woldSignOperator : PaperWoldHistory →L[ℂ] PaperWoldHistory :=
  lpDiagonalCLM woldIncrementSign zero_le_one (fun n => (norm_woldIncrementSign n).le)

@[simp] theorem woldSignOperator_apply (x : PaperWoldHistory) (n : ℕ) :
    woldSignOperator x n = woldIncrementSign n * x n := rfl

theorem woldSignOperator_apply_apply (x : PaperWoldHistory) :
    woldSignOperator (woldSignOperator x) = x := by
  ext n
  simp only [woldSignOperator_apply, ← mul_assoc, woldIncrementSign_mul_self, one_mul]

theorem norm_woldSignOperator_apply (x : PaperWoldHistory) : ‖woldSignOperator x‖ = ‖x‖ := by
  have hle : ∀ y : PaperWoldHistory, ‖woldSignOperator y‖ ≤ ‖y‖ := fun y =>
    (woldSignOperator.le_opNorm y).trans
      (mul_le_of_le_one_left (norm_nonneg _) (norm_lpDiagonalCLM_le _ _ _))
  refine le_antisymm (hle x) ?_
  calc ‖x‖ = ‖woldSignOperator (woldSignOperator x)‖ := by rw [woldSignOperator_apply_apply]
    _ ≤ ‖woldSignOperator x‖ := hle _

/-- **Sign conjugation.**  Each literal masked Wold operator is the magnitude operator conjugated
by the diagonal sign involution. -/
theorem paperWoldMaskedOperator_eq_sign_conj (p : PaperWoldStrictHalf) (m : PaperWoldMask) :
    paperWoldMaskedOperator p m =
      woldSignOperator ∘L paperWoldMagnitudeOperator p m ∘L woldSignOperator := by
  apply HasLpMatrix.ext (K := fun n j => paperWoldMaskedKernel p m (n, j))
  · intro n j
    exact paperWoldMaskedOperator_single p m n j
  · intro n j
    change ((woldSignOperator ∘L paperWoldMagnitudeOperator p m ∘L woldSignOperator)
      (lp.single 2 j (1 : ℂ)) : ℕ → ℂ) n = _
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, woldSignOperator]
    rw [lpDiagonalCLM_single, lpDiagonalCLM_apply]
    have hs : (lp.single 2 j (woldIncrementSign j) : PaperWoldHistory) =
        woldIncrementSign j • (lp.single 2 j (1 : ℂ) : PaperWoldHistory) := by
      rw [← lp.single_smul, smul_eq_mul, mul_one]
    rw [hs, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, paperWoldMagnitudeOperator,
      HilbertSchmidt.toOperator_single, paperWoldMaskedKernel_eq_sign_conj]
    ring

/-- The literal and magnitude masked Wold operators have the same norm. -/
theorem norm_paperWoldMaskedOperator_eq_magnitude (p : PaperWoldStrictHalf) (m : PaperWoldMask) :
    ‖paperWoldMaskedOperator p m‖ = ‖paperWoldMagnitudeOperator p m‖ := by
  have hle : ∀ T : PaperWoldHistory →L[ℂ] PaperWoldHistory,
      ‖woldSignOperator ∘L T ∘L woldSignOperator‖ ≤ ‖T‖ := by
    intro T
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, norm_woldSignOperator_apply]
    exact (T.le_opNorm _).trans_eq (by rw [norm_woldSignOperator_apply])
  have hback : paperWoldMagnitudeOperator p m =
      woldSignOperator ∘L paperWoldMaskedOperator p m ∘L woldSignOperator := by
    rw [paperWoldMaskedOperator_eq_sign_conj]
    ext1 x
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, woldSignOperator_apply_apply]
  apply le_antisymm
  · rw [paperWoldMaskedOperator_eq_sign_conj]; exact hle _
  · rw [hback]; exact hle _

/-- The literal and magnitude masked Wold operators are compact together. -/
theorem isCompactOperator_paperWoldMagnitudeOperator (p : PaperWoldStrictHalf)
    (m : PaperWoldMask) : IsCompactOperator (paperWoldMagnitudeOperator p m) :=
  (HilbertSchmidt.isHilbertSchmidt_toOperator _).isCompactOperator

/-- The logarithmic cell of every even composite cutoff is a lower bound for the magnitude. -/
private theorem log_cell_le_abs_increment {k : ℕ} (hk : 1 ≤ k) :
    Real.log (2 * k + 2) - Real.log (2 * k + 1) ≤ |xiHeatCassiniWoldNatIncrement (2 * k)| := by
  have hnp : ¬ (2 * k + 2).Prime := by
    rw [show 2 * k + 2 = 2 * (k + 1) by ring]
    exact Nat.not_prime_mul (by norm_num) (by omega)
  rw [xiHeatCassiniWoldNatIncrement_eq]
  simp only [xiHeatCassiniWoldNatWeight, dif_neg hnp, zero_sub, abs_neg]
  push_cast
  exact le_abs_self _

/-- **The fake residual diverges.**  The magnitudes of the literal increments are not summable. -/
theorem not_summable_abs_woldIncrement :
    ¬ Summable (fun n => |xiHeatCassiniWoldNatIncrement n|) := by
  intro hs
  have heven : Summable (fun k : ℕ => |xiHeatCassiniWoldNatIncrement (2 * (k + 1))|) :=
    hs.comp_injective (fun a b h => by omega)
  have hcell : Summable (fun k : ℕ => 1 / (2 * ((k : ℝ) + 1) + 2)) := by
    refine heven.of_nonneg_of_le (fun k => by positivity) fun k => ?_
    have hk := log_cell_le_abs_increment (k := k + 1) (by omega)
    have hpos : (0 : ℝ) < 2 * ((k : ℝ) + 1) + 1 := by positivity
    have hcellLow : 1 / (2 * ((k : ℝ) + 1) + 2) ≤
        Real.log (2 * ((k : ℝ) + 1) + 2) - Real.log (2 * ((k : ℝ) + 1) + 1) := by
      rw [← Real.log_div (by positivity) hpos.ne']
      refine le_trans (le_of_eq ?_) (Real.one_sub_inv_le_log_of_pos (by positivity))
      field_simp
      ring
    push_cast at hk
    exact hcellLow.trans hk
  have hharm : Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) :=
    (hcell.mul_left 2).congr fun k => by push_cast; field_simp; ring
  exact Real.not_summable_one_div_natCast ((summable_nat_add_iff 2).mp hharm)

/-- The literal centered Wold residual tends to zero. -/
theorem tendsto_xiHeatCassiniWoldNatResidualLogDiscrepancy_zero :
    Tendsto xiHeatCassiniWoldNatResidualLogDiscrepancy atTop (𝓝 0) := by
  obtain ⟨B, c, hc, -, hrate⟩ := exists_xiHeatCassiniWoldNatResidualLogDiscrepancy_exp_rate
  have hsqrt : Tendsto (fun N : ℕ => c * Real.sqrt (Real.log N)) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp
      tendsto_natCast_atTop_atTop)).const_mul_atTop hc
  have hexp : Tendsto (fun N : ℕ => B * Real.exp (-c * Real.sqrt (Real.log N))) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hsqrt)).const_mul B
    simp only [mul_zero] at h
    refine h.congr fun N => ?_
    simp only [Function.comp_apply, neg_mul]
  exact squeeze_zero_norm' (hrate.mono fun N hN => by simpa only [Real.norm_eq_abs] using hN) hexp

/-- **Sign-blindness of the masked Wold operators.**  For every strict-half exponent and mask,
the literal operator and the magnitude operator have equal norms and are both compact, while the
literal residual tends to zero and the magnitude partial sums diverge. -/
theorem paperWoldMaskedOperator_signBlind (p : PaperWoldStrictHalf) (m : PaperWoldMask) :
    ‖paperWoldMaskedOperator p m‖ = ‖paperWoldMagnitudeOperator p m‖ ∧
      IsCompactOperator (paperWoldMaskedOperator p m) ∧
      IsCompactOperator (paperWoldMagnitudeOperator p m) ∧
      Tendsto xiHeatCassiniWoldNatResidualLogDiscrepancy atTop (𝓝 0) ∧
      ¬ Summable (fun n => |xiHeatCassiniWoldNatIncrement n|) :=
  ⟨norm_paperWoldMaskedOperator_eq_magnitude p m, paperWoldMaskedOperator_compact p m,
    isCompactOperator_paperWoldMagnitudeOperator p m,
    tendsto_xiHeatCassiniWoldNatResidualLogDiscrepancy_zero, not_summable_abs_woldIncrement⟩

end
end RHTower
