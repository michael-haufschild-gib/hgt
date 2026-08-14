import GaloisForLFunctions.RHTower.SuzukiValuationEvaluationAlgebra
import GaloisForLFunctions.RHTower.SuzukiExteriorHardyAmplitudes
import GaloisForLFunctions.RHTower.SuzukiWienerNuclearBoundaryCarrier

/-!
# The exact high-frequency rigged carrier of Suzuki's exterior symbol

At a fixed aperture Suzuki's exterior symbol is the valuation Wiener element

`h_ξ = L(ξ) δ₀ + q_a(ξ) δ₀ + t_a`,

with `L(ξ) = log ⟨ξ⟩`, a uniformly bounded archimedean remainder `q_a`, and the finite prime atom
family `t_a` of mass `M_a`.  Above an explicit frequency threshold the widened margin
`C_a + M_a < L₀ ≤ L(ξ)` makes the Neumann series an actual `ℓ¹` inverse, and unit-phase evaluation
— which is multiplicative here because `h_ξ` is finitely supported — turns that inverse into the
reciprocal of the symbol.  Hence the two-root carrier reconstructs the completed mode by absolute
evaluation, with no `ℓ²`-to-scalar map anywhere.
-/

open Set Filter Topology
open scoped ENNReal
open RHTower
  (suzukiExteriorLogWeight suzukiSymbolRemainder exists_bound_suzukiSymbolRemainder)

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The visible prime-power alphabet of an aperture: the steps with `p^j ≤ e^{2a}`. -/
def suzukiApertureSteps (a : ℝ) : Finset (Nat.Primes × ℕ) :=
  ((((Finset.range (⌊Real.exp (2 * a)⌋₊ + 1)).subtype fun n => Nat.Prime n) : Finset Nat.Primes)
      ×ˢ Finset.Icc 1 ⌊Real.exp (2 * a)⌋₊).filter
    fun pj => (pj.1 : ℕ) ^ pj.2 ≤ ⌊Real.exp (2 * a)⌋₊

theorem one_le_of_mem_suzukiApertureSteps {a : ℝ} {pj : Nat.Primes × ℕ}
    (h : pj ∈ suzukiApertureSteps a) : 1 ≤ pj.2 := by
  have h1 := (Finset.mem_filter.mp h).1
  have h2 := (Finset.mem_product.mp h1).2
  exact (Finset.mem_Icc.mp h2).1

/-- Suzuki's finite prime coefficient family at aperture `a`. -/
def suzukiExteriorAtoms (a : ℝ) : SuzukiSeamValuation → ℂ :=
  suzukiWienerAtoms (suzukiApertureSteps a)

/-- **`(18)`: the exact Wiener mass `M_a = 2 ∑ (log p) p^{-j/2}`.** -/
def suzukiWienerMass (a : ℝ) : ℝ :=
  2 * ∑ s ∈ suzukiApertureSteps a, suzukiPrimePowerWeight s

theorem suzukiWienerMass_nonneg (a : ℝ) : 0 ≤ suzukiWienerMass a := by
  rw [suzukiWienerMass]
  have : 0 ≤ ∑ s ∈ suzukiApertureSteps a, suzukiPrimePowerWeight s :=
    Finset.sum_nonneg fun s _ => suzukiPrimePowerWeight_nonneg' s
  linarith

theorem discreteMass_suzukiExteriorAtoms (a : ℝ) :
    discreteMass (fun ν => ‖suzukiExteriorAtoms a ν‖ₑ)
      = ENNReal.ofReal (suzukiWienerMass a) :=
  discreteMass_enorm_suzukiWienerAtoms fun _ h => one_le_of_mem_suzukiApertureSteps h

theorem suzukiExteriorAtoms_eq_zero_outside (a : ℝ) {ν : SuzukiSeamValuation}
    (hν : ν ∉ suzukiAtomSupport (suzukiApertureSteps a)) : suzukiExteriorAtoms a ν = 0 := by
  apply suzukiWienerAtoms_eq_zero
  intro x hx heq
  exact hν (by rw [suzukiAtomSupport, Finset.mem_image]; exact ⟨x, hx, heq.symm⟩)

/-- The high-pass valuation element `h_ξ` of Suzuki's exterior symbol. -/
def suzukiHighPassElement (a ξ : ℝ) : SuzukiSeamValuation → ℂ :=
  wienerHighPassSymbol ((suzukiExteriorLogWeight ξ : ℝ) : ℂ) (suzukiSymbolRemainder a ξ)
    (suzukiExteriorAtoms a)

/-- **`(15)`--`(16)`: the exact source normalization, with `κ = 1`.** -/
def suzukiExteriorSymbol (a ξ : ℝ) : ℂ :=
  ((suzukiExteriorLogWeight ξ : ℝ) : ℂ) + suzukiSymbolRemainder a ξ
    + suzukiWienerEval ξ (suzukiExteriorAtoms a)

/-- The high-pass element is supported on the unit atom and the visible prime atoms. -/
theorem suzukiHighPassElement_eq_zero_outside (a ξ : ℝ) {ν : SuzukiSeamValuation}
    (hν : ν ∉ insert (0 : SuzukiSeamValuation) (suzukiAtomSupport (suzukiApertureSteps a))) :
    suzukiHighPassElement a ξ ν = 0 := by
  have h0 : ν ≠ 0 := fun h => hν (by rw [h]; exact Finset.mem_insert_self _ _)
  have hatom : suzukiExteriorAtoms a ν = 0 :=
    suzukiExteriorAtoms_eq_zero_outside a fun h => hν (Finset.mem_insert_of_mem h)
  rw [suzukiHighPassElement, wienerHighPassSymbol, discreteDelta, if_neg h0, mul_zero,
    hatom, add_zero]

theorem summable_norm_suzukiHighPassElement (a ξ : ℝ) :
    Summable fun ν => ‖suzukiHighPassElement a ξ ν‖ := by
  apply summable_of_ne_finset_zero
    (s := insert (0 : SuzukiSeamValuation) (suzukiAtomSupport (suzukiApertureSteps a)))
  intro ν hν
  rw [suzukiHighPassElement_eq_zero_outside a ξ hν, norm_zero]

theorem summable_norm_suzukiExteriorAtoms (a : ℝ) :
    Summable fun ν => ‖suzukiExteriorAtoms a ν‖ := by
  apply summable_of_ne_finset_zero (s := suzukiAtomSupport (suzukiApertureSteps a))
  intro ν hν
  rw [suzukiExteriorAtoms_eq_zero_outside a hν, norm_zero]

/-- **The evaluation of the high-pass element is the symbol.** -/
theorem suzukiWienerEval_highPassElement (a ξ : ℝ) :
    suzukiWienerEval ξ (suzukiHighPassElement a ξ) = suzukiExteriorSymbol a ξ := by
  have hsplit : suzukiHighPassElement a ξ
      = fun ν => (((suzukiExteriorLogWeight ξ : ℝ) : ℂ) + suzukiSymbolRemainder a ξ) * discreteDelta ν
          + suzukiExteriorAtoms a ν := rfl
  have hdelta : Summable fun ν : SuzukiSeamValuation =>
      ‖(((suzukiExteriorLogWeight ξ : ℝ) : ℂ) + suzukiSymbolRemainder a ξ) * discreteDelta ν‖ := by
    apply summable_of_ne_finset_zero (s := ({0} : Finset SuzukiSeamValuation))
    intro ν hν
    have h0 : ν ≠ 0 := by simpa using hν
    rw [discreteDelta, if_neg h0, mul_zero, norm_zero]
  rw [hsplit, suzukiWienerEval_add hdelta (summable_norm_suzukiExteriorAtoms a),
    suzukiWienerEval_const_mul_delta, suzukiExteriorSymbol]

/-- **`(19)`: the explicit high-frequency threshold.**  There is a uniform bound on the
archimedean remainder, a margin strictly above `C_a + M_a`, and a frequency past which the
logarithmic weight exceeds that margin. -/
theorem exists_suzukiExteriorThreshold (a : ℝ) :
    ∃ C L0 Ξ : ℝ, 0 ≤ C ∧ 0 < L0 ∧ (∀ ξ : ℝ, ‖suzukiSymbolRemainder a ξ‖ ≤ C)
      ∧ C + suzukiWienerMass a < L0
      ∧ ∀ ξ : ℝ, Ξ ≤ |ξ| → L0 ≤ suzukiExteriorLogWeight ξ := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_suzukiSymbolRemainder a
  refine ⟨C, C + suzukiWienerMass a + 1, Real.sqrt (Real.exp (2 * (C + suzukiWienerMass a + 1))),
    hC0, by linarith [suzukiWienerMass_nonneg a], hC, by linarith, ?_⟩
  intro ξ hξ
  have hpos : 0 < Real.exp (2 * (C + suzukiWienerMass a + 1)) := Real.exp_pos _
  have hsq : Real.exp (2 * (C + suzukiWienerMass a + 1)) ≤ ξ ^ 2 := by
    have h1 : Real.sqrt (Real.exp (2 * (C + suzukiWienerMass a + 1))) ^ 2
        = Real.exp (2 * (C + suzukiWienerMass a + 1)) := Real.sq_sqrt hpos.le
    have h2 : Real.sqrt (Real.exp (2 * (C + suzukiWienerMass a + 1))) ^ 2 ≤ |ξ| ^ 2 := by
      nlinarith [Real.sqrt_nonneg (Real.exp (2 * (C + suzukiWienerMass a + 1))), hξ,
        abs_nonneg ξ]
    rw [h1] at h2
    rwa [sq_abs] at h2
  have hlog : 2 * (C + suzukiWienerMass a + 1) ≤ Real.log (1 + ξ ^ 2) := by
    have hle : Real.exp (2 * (C + suzukiWienerMass a + 1)) ≤ 1 + ξ ^ 2 := by linarith
    have := Real.log_le_log hpos hle
    rwa [Real.log_exp] at this
  rw [suzukiExteriorLogWeight]
  linarith

/-- The Neumann inverse of the high-pass element at a frequency above the threshold. -/
def suzukiExteriorInverse (a ξ : ℝ) : SuzukiSeamValuation → ℂ :=
  wienerNeumannInverse ((suzukiExteriorLogWeight ξ : ℝ) : ℂ) (suzukiSymbolRemainder a ξ)
    (suzukiExteriorAtoms a)

/-- **`(22)`: above the threshold the inverse is `ℓ¹` with the exact margin bound.** -/
theorem tsum_enorm_suzukiExteriorInverse_le {a ξ C L0 : ℝ} (hC0 : 0 ≤ C)
    (hq : ‖suzukiSymbolRemainder a ξ‖ ≤ C) (hL : L0 ≤ suzukiExteriorLogWeight ξ)
    (hsub : C + suzukiWienerMass a < L0) :
    (∑' ν, ‖suzukiExteriorInverse a ξ ν‖ₑ)
      ≤ (ENNReal.ofReal L0 - ENNReal.ofReal (C + suzukiWienerMass a))⁻¹ := by
  have hqe : ‖suzukiSymbolRemainder a ξ‖ₑ ≤ ENNReal.ofReal C := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hq
  have hLe : ENNReal.ofReal L0 ≤ ‖((suzukiExteriorLogWeight ξ : ℝ) : ℂ)‖ₑ := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (le_trans hL (le_abs_self _))
  have hbound := fun ν => enorm_wienerNeumannInverse_le (G := SuzukiSeamValuation)
    (t := suzukiExteriorAtoms a) (C := C) (L0 := L0) hqe hLe ν
  have hmass : (∑' ν, ‖suzukiExteriorInverse a ξ ν‖ₑ)
      ≤ discreteMass (fun ν => (ENNReal.ofReal L0)⁻¹
          * discreteNeumannKernel (wienerStarKernel C L0 (suzukiExteriorAtoms a)) ν) := by
    rw [discreteMass]
    exact ENNReal.tsum_le_tsum hbound
  refine hmass.trans ?_
  rw [discreteMass_wienerInverseKernel, discreteMass_suzukiExteriorAtoms]
  have hlt : ENNReal.ofReal C + ENNReal.ofReal (suzukiWienerMass a) < ENNReal.ofReal L0 := by
    rw [← ENNReal.ofReal_add hC0 (suzukiWienerMass_nonneg a)]
    exact ENNReal.ofReal_lt_ofReal_iff (by linarith [suzukiWienerMass_nonneg a]) |>.mpr hsub
  have hsum : ENNReal.ofReal C + ENNReal.ofReal (suzukiWienerMass a)
      = ENNReal.ofReal (C + suzukiWienerMass a) :=
    (ENNReal.ofReal_add hC0 (suzukiWienerMass_nonneg a)).symm
  rw [hsum] at hlt ⊢
  exact le_of_eq (wienerInverseMass_eq hlt ENNReal.ofReal_ne_top)

private theorem summable_norm_of_tsum_enorm_ne_top {f : SuzukiSeamValuation → ℂ}
    (h : (∑' ν, ‖f ν‖ₑ) ≠ ⊤) : Summable fun ν => ‖f ν‖ := by
  have hnn : Summable fun ν => ‖f ν‖₊ := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simpa [enorm_eq_nnnorm] using h
  simpa using NNReal.summable_coe.mpr hnn

theorem summable_norm_suzukiExteriorInverse {a ξ C L0 : ℝ} (hC0 : 0 ≤ C)
    (hq : ‖suzukiSymbolRemainder a ξ‖ ≤ C) (hL : L0 ≤ suzukiExteriorLogWeight ξ)
    (hsub : C + suzukiWienerMass a < L0) :
    Summable fun ν => ‖suzukiExteriorInverse a ξ ν‖ := by
  apply summable_norm_of_tsum_enorm_ne_top
  have hle := tsum_enorm_suzukiExteriorInverse_le hC0 hq hL hsub
  have hne : (ENNReal.ofReal L0 - ENNReal.ofReal (C + suzukiWienerMass a))⁻¹ ≠ ⊤ := by
    apply ENNReal.inv_ne_top.mpr
    have hlt : ENNReal.ofReal (C + suzukiWienerMass a) < ENNReal.ofReal L0 :=
      ENNReal.ofReal_lt_ofReal_iff (by linarith [suzukiWienerMass_nonneg a]) |>.mpr hsub
    exact (tsub_pos_of_lt hlt).ne'
  exact ne_top_of_le_ne_top hne hle

/-- **`(21)`: the Neumann series really inverts the symbol.** -/
theorem discreteConv_suzukiHighPass_inverse {a ξ C L0 : ℝ} (hC0 : 0 ≤ C)
    (hq : ‖suzukiSymbolRemainder a ξ‖ ≤ C) (hL : L0 ≤ suzukiExteriorLogWeight ξ)
    (hsub : C + suzukiWienerMass a < L0) :
    discreteConv (suzukiHighPassElement a ξ) (suzukiExteriorInverse a ξ) = discreteDelta := by
  have hL0pos : 0 < L0 := by linarith [suzukiWienerMass_nonneg a]
  have hLpos : 0 < suzukiExteriorLogWeight ξ := lt_of_lt_of_le hL0pos hL
  have hne : ((suzukiExteriorLogWeight ξ : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact ne_of_gt hLpos
  have hqe : ‖suzukiSymbolRemainder a ξ‖ₑ ≤ ENNReal.ofReal C := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal hq
  have hLe : ENNReal.ofReal L0 ≤ ‖((suzukiExteriorLogWeight ξ : ℝ) : ℂ)‖ₑ := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (le_trans hL (le_abs_self _))
  have hmass : discreteMass (fun ν => ‖wienerRelativeKernel ((suzukiExteriorLogWeight ξ : ℝ) : ℂ)
      (suzukiSymbolRemainder a ξ) (suzukiExteriorAtoms a) ν‖ₑ) < 1 := by
    have hle : discreteMass (fun ν => ‖wienerRelativeKernel ((suzukiExteriorLogWeight ξ : ℝ) : ℂ)
        (suzukiSymbolRemainder a ξ) (suzukiExteriorAtoms a) ν‖ₑ)
        ≤ discreteMass (wienerStarKernel C L0 (suzukiExteriorAtoms a)) := by
      rw [discreteMass, discreteMass]
      exact ENNReal.tsum_le_tsum fun ν => enorm_wienerRelativeKernel_le hqe hLe ν
    refine lt_of_le_of_lt hle ?_
    rw [discreteMass_wienerStarKernel, discreteMass_suzukiExteriorAtoms]
    rw [ENNReal.div_lt_iff (Or.inl (by simpa using hL0pos)) (Or.inl ENNReal.ofReal_ne_top),
      one_mul, ← ENNReal.ofReal_add hC0 (suzukiWienerMass_nonneg a)]
    exact ENNReal.ofReal_lt_ofReal_iff hL0pos |>.mpr hsub
  exact discreteConv_wienerHighPassSymbol_neumannInverse hne hmass

/-- **`(25)`: absolute evaluation inverts the symbol.**  Above the threshold the unit-phase
evaluation of the Neumann inverse is the reciprocal of Suzuki's symbol. -/
theorem suzukiWienerEval_inverse_mul {a ξ C L0 : ℝ} (hC0 : 0 ≤ C)
    (hq : ‖suzukiSymbolRemainder a ξ‖ ≤ C) (hL : L0 ≤ suzukiExteriorLogWeight ξ)
    (hsub : C + suzukiWienerMass a < L0) :
    suzukiWienerEval ξ (suzukiExteriorInverse a ξ) * suzukiExteriorSymbol a ξ = 1 := by
  have hconv := discreteConv_suzukiHighPass_inverse hC0 hq hL hsub
  have hcomm : discreteConv (suzukiExteriorInverse a ξ) (suzukiHighPassElement a ξ)
      = discreteDelta := by
    rw [discreteConv_comm]
    exact hconv
  have hEval := congrArg (suzukiWienerEval ξ) hcomm
  rw [suzukiWienerEval_discreteConv (T := insert (0 : SuzukiSeamValuation)
      (suzukiAtomSupport (suzukiApertureSteps a)))
      (summable_norm_suzukiExteriorInverse hC0 hq hL hsub)
      (fun σ hσ => suzukiHighPassElement_eq_zero_outside a ξ hσ),
    suzukiWienerEval_discreteDelta, suzukiWienerEval_highPassElement] at hEval
  exact hEval

/-- **`(23)`--`(25)`: the two-root carrier reconstructs the completed mode.**  For any source
family the carrier `c = h⁻¹ ⋆ s` evaluates to the source evaluation divided by the symbol. -/
theorem suzukiWienerEval_carrier {a ξ C L0 : ℝ} (hC0 : 0 ≤ C)
    (hq : ‖suzukiSymbolRemainder a ξ‖ ≤ C) (hL : L0 ≤ suzukiExteriorLogWeight ξ)
    (hsub : C + suzukiWienerMass a < L0) {s : SuzukiSeamValuation → ℂ}
    {T : Finset SuzukiSeamValuation} (hs : ∀ σ ∉ T, s σ = 0) :
    suzukiWienerEval ξ (discreteConv (suzukiExteriorInverse a ξ) s) * suzukiExteriorSymbol a ξ
      = suzukiWienerEval ξ s := by
  rw [suzukiWienerEval_discreteConv (summable_norm_suzukiExteriorInverse hC0 hq hL hsub) hs]
  have hkey := suzukiWienerEval_inverse_mul hC0 hq hL hsub
  calc suzukiWienerEval ξ (suzukiExteriorInverse a ξ) * suzukiWienerEval ξ s
        * suzukiExteriorSymbol a ξ
      = (suzukiWienerEval ξ (suzukiExteriorInverse a ξ) * suzukiExteriorSymbol a ξ)
          * suzukiWienerEval ξ s := by ring
    _ = suzukiWienerEval ξ s := by rw [hkey, one_mul]

end

end GaloisForLFunctions.RHTower
