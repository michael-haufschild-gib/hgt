import GaloisForLFunctions.RHTower.JointAncestryChainZeroFreeHalfPlane
import GaloisForLFunctions.RHTower.WeilLagFunctionGrowth

/-!
# A chain-free converse: the dressing level bounds the zeros

Positivity of the `σ`-dressed aggregate bounds every off-diagonal coefficient by the diagonal.  On
the integer characters this reads `n^{−σ} Φ(log n) ≤ Φ(0)`, and between consecutive integers the
lag function moves by at most `30`, so `Φ(L) ≤ M e^{σL}` for all `L ≥ 0`.  The growth criterion for
the lag function (Landau's theorem for the nonnegative density `M e^{σu} − Φ(u)`) then puts every
zero in `Re ρ ≤ ½ + σ` whenever `σ < ½`.

* `re_le_half_add_of_jasDressedPSD`: `JasDressedPSD σ`, `0 ≤ σ < ½` ⟹ `Re ρ ≤ ½ + σ`;
* `abs_re_sub_half_le_of_jasDressedPSD`: the same two-sided, by the functional equation;
* `re_le_half_add_jasAbscissa`: unconditionally, every zero satisfies `Re ρ ≤ ½ + σ*`.

No chain hypothesis enters: the argument uses only the size of `Φ`, never the isolation of a
single zero.  Together with `σ* ≥ 1 + |Re ρ₀ − ½|` for a farthest zero, the JAS abscissa satisfies
`σ* ≥ Θ − ½` always and `σ* ≥ Θ + ½` off a chain (`Θ = sup Re ρ`): the chain gap is exactly `1`.
-/

open Complex

namespace RHTower

noncomputable section

/-- Positivity bounds the integer lags: `Φ(log n) ≤ Φ(0) n^σ`. -/
theorem integerLag_le_of_jasDressedPSD {σ : ℝ} (h : JasDressedPSD σ) {n : ℕ} (hn : 2 ≤ n) :
    integerLag n ≤ poleSharpConstant * Real.exp (σ * Real.log n) := by
  have hle := re_jasDressedLagAggregate_le_of_psd h (jasNatChar_ne_zero hn)
  rw [jasDressedLagAggregate_jasNatChar σ (show n ≠ 0 by omega), weilLagFunction_eq_ofReal,
    ← Complex.ofReal_mul, Complex.ofReal_re] at hle
  have hpos : 0 < Real.exp (-σ * Real.log n) := Real.exp_pos _
  have hinv : Real.exp (σ * Real.log n) * Real.exp (-σ * Real.log n) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  unfold integerLag
  have h2 : weilLagFunctionReal (Real.log n) =
      Real.exp (σ * Real.log n) * (Real.exp (-σ * Real.log n) * weilLagFunctionReal (Real.log n)) := by
    rw [← mul_assoc, hinv, one_mul]
  rw [h2, mul_comm poleSharpConstant]
  exact mul_le_mul_of_nonneg_left hle (Real.exp_pos _).le

/-- **Positivity at `σ ≥ 0` gives one-sided exponential growth `Φ(L) ≤ M e^{σL}`.** -/
theorem exists_weilLagFunctionReal_le_exp_of_jasDressedPSD {σ : ℝ} (hσ : 0 ≤ σ)
    (h : JasDressedPSD σ) :
    ∃ M : ℝ, ∀ L, 0 ≤ L → weilLagFunctionReal L ≤ M * Real.exp (σ * L) := by
  have hA := poleSharpConstant_pos
  have hmass : 0 ≤ jasLagAbsMass := tsum_nonneg fun _ => norm_nonneg _
  refine ⟨poleSharpConstant + 30 + 2 * jasLagAbsMass, fun L hL => ?_⟩
  have hexp1 : 1 ≤ Real.exp (σ * L) := Real.one_le_exp (mul_nonneg hσ hL)
  rcases lt_or_ge L (Real.log 2) with hsmall | hbig
  · have h1 : weilLagFunctionReal L ≤ ‖weilLagFunction L‖ := Complex.re_le_norm _
    have h2 := norm_weilLagFunction_le L
    have h3 : Real.exp (|L| / 2) ≤ 2 := by
      rw [abs_of_nonneg hL]
      calc Real.exp (L / 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr (by linarith)
        _ = 2 := Real.exp_log (by norm_num)
    have h4 : weilLagFunctionReal L ≤ 2 * jasLagAbsMass :=
      h1.trans (h2.trans (mul_le_mul_of_nonneg_right h3 hmass))
    nlinarith
  · have hfloor := weilLagFunctionReal_le_integerLag_add hbig
    have hX2 : (2 : ℝ) ≤ Real.exp L := by
      calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ Real.exp L := Real.exp_le_exp.mpr hbig
    have hn2 : 2 ≤ ⌊Real.exp L⌋₊ := by
      have := Nat.floor_le_floor hX2
      simpa using this
    have hint := integerLag_le_of_jasDressedPSD h hn2
    have hfl : ((⌊Real.exp L⌋₊ : ℕ) : ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos L).le
    have hflpos : (0 : ℝ) < ((⌊Real.exp L⌋₊ : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < ⌊Real.exp L⌋₊ by omega)
    have hlog : Real.log (⌊Real.exp L⌋₊ : ℝ) ≤ L := by
      calc Real.log (⌊Real.exp L⌋₊ : ℝ) ≤ Real.log (Real.exp L) := Real.log_le_log hflpos hfl
        _ = L := Real.log_exp L
    have hexp : Real.exp (σ * Real.log (⌊Real.exp L⌋₊ : ℝ)) ≤ Real.exp (σ * L) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog hσ)
    have h5 : weilLagFunctionReal L ≤ poleSharpConstant * Real.exp (σ * L) + 30 :=
      hfloor.trans (by nlinarith [mul_le_mul_of_nonneg_left hexp hA.le])
    nlinarith

/-- **Chain-free converse.**  Positivity at a dressing level `0 ≤ σ < ½` puts every zero in
`Re ρ ≤ ½ + σ`. -/
theorem re_le_half_add_of_jasDressedPSD {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2)
    (h : JasDressedPSD σ) (q : XiZeroCopy) : (q.1 : ℂ).re ≤ 1 / 2 + σ := by
  obtain ⟨M, hM⟩ := exists_weilLagFunctionReal_le_exp_of_jasDressedPSD hσ0 h
  exact re_le_half_add_of_weilLagFunctionReal_le_exp hσ0 hσ hM q

/-- The two-sided form, by the functional equation. -/
theorem abs_re_sub_half_le_of_jasDressedPSD {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2)
    (h : JasDressedPSD σ) (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ σ := by
  have h1 := re_le_half_add_of_jasDressedPSD hσ0 hσ h q
  have h2 := re_le_half_add_of_jasDressedPSD hσ0 hσ h (xiZeroCopyReflectEquiv q)
  rw [xiZeroCopy_reflect_val, Complex.sub_re, Complex.one_re] at h2
  rw [abs_le]
  constructor <;> linarith

/-- In half-plane form. -/
theorem xiZeroHalfPlaneBound_of_jasDressedPSD {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2)
    (h : JasDressedPSD σ) : XiZeroHalfPlaneBound σ := by
  intro ρ hρ
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  exact re_le_half_add_of_jasDressedPSD hσ0 hσ h q

/-- **Unconditionally, every zero lies left of `½ + σ*`.** -/
theorem re_le_half_add_jasAbscissa (q : XiZeroCopy) : (q.1 : ℂ).re ≤ 1 / 2 + jasAbscissa := by
  rcases lt_or_ge jasAbscissa (1 / 2) with hlt | hge
  · exact re_le_half_add_of_jasDressedPSD zero_le_jasAbscissa hlt jasDressedPSD_jasAbscissa q
  · have := (xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support q.1)).2
    linarith

end

end RHTower
