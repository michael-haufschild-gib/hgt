import GaloisForLFunctions.RHTower.DumitrescuWolfPhaseWrap
import GaloisForLFunctions.RHTower.XiZeroSumDivergence

/-!
# The endpoint obstruction for the actual zeta ordinates

The Xi zero copies form a countable type whose spectral norms escape every bound off finite sets,
and whose reciprocal sum diverges.  Enumerating them therefore produces an ordinate sequence
`xiOrdinate : ℕ → ℝ` that is positive, tends to infinity, and has divergent reciprocal partial
sums — exactly the three hypotheses of the paired vertical Riccati obstruction.

Consequently neither channel of the Dumitrescu--Wolf quantisation reaches its asserted endpoint, and
this statement carries no hypotheses beyond the setup constants and the requirement that the
recurrences stay defined.
-/

open Complex Filter Topology GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The Xi divisor has infinitely many multiplicity copies: over a finite index type every family
is summable, contradicting the divergence of the reciprocal spectral norms. -/
instance instInfiniteXiZeroCopy : Infinite XiZeroCopy := by
  refine not_finite_iff_infinite.mp fun hfin => ?_
  haveI := hfin
  exact not_summable_inv_norm_xiSpectralPoint Summable.of_finite

/-- Square-summability makes the spectral norms escape every bound off finite sets. -/
theorem tendsto_norm_xiSpectralPoint_cofinite :
    Tendsto (fun q : XiZeroCopy => ‖xiSpectralPoint q‖) cofinite atTop := by
  have hsq := xiSpectralPoint_inv_sq_summable
  rw [tendsto_atTop]
  intro B
  set M : ℝ := max B 1 with hM
  have hMpos : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hev := Filter.Tendsto.eventually_lt_const
    (show (0 : ℝ) < 1 / M ^ 2 by positivity) hsq.tendsto_cofinite_zero
  filter_upwards [hev] with q hq
  have hpos : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  rw [div_lt_div_iff₀ (by positivity) (by positivity)] at hq
  have hlt : M < ‖xiSpectralPoint q‖ := by nlinarith [hMpos, hpos, hq]
  exact le_trans (le_max_left B 1) hlt.le

/-- A choice of enumeration of the Xi zero copies. -/
def xiOrdinateEquiv : ℕ ≃ XiZeroCopy := Classical.choice nonempty_equiv_of_countable

/-- The ordinate sequence of the Xi divisor: spectral norms along a fixed enumeration. -/
def xiOrdinate (k : ℕ) : ℝ := ‖xiSpectralPoint (xiOrdinateEquiv k)‖

theorem xiOrdinate_pos (k : ℕ) : 0 < xiOrdinate k :=
  norm_pos_iff.mpr (xiSpectralPoint_ne_zero _)

theorem tendsto_xiOrdinate_atTop : Tendsto xiOrdinate atTop atTop := by
  have hinj : Tendsto (xiOrdinateEquiv : ℕ → XiZeroCopy) cofinite cofinite :=
    xiOrdinateEquiv.injective.tendsto_cofinite
  rw [Nat.cofinite_eq_atTop] at hinj
  exact tendsto_norm_xiSpectralPoint_cofinite.comp hinj

theorem not_summable_inv_xiOrdinate : ¬ Summable (fun k => (xiOrdinate k)⁻¹) := by
  intro hsum
  refine not_summable_inv_norm_xiSpectralPoint ?_
  rw [← Equiv.summable_iff xiOrdinateEquiv]
  exact hsum.congr fun k => by simp [xiOrdinate, one_div]

/-- **The harmonic hypothesis, discharged.**  The reciprocal ordinate partial sums diverge. -/
theorem tendsto_sum_inv_xiOrdinate_atTop :
    Tendsto (fun N => ∑ k ∈ Finset.range N, (xiOrdinate k)⁻¹) atTop atTop :=
  (not_summable_iff_tendsto_nat_atTop_of_nonneg
    (fun k => inv_nonneg.mpr (xiOrdinate_pos k).le)).mp not_summable_inv_xiOrdinate

/-! ## The unconditional endpoint obstruction -/

variable {α β T : ℝ}

/-- **Incoming channel.**  For the actual zeta ordinates the lower Riccati sequence cannot tend to
`+∞`.  No arithmetic hypothesis remains. -/
theorem not_tendsto_atTop_verticalLowerRiccati_xiOrdinate
    (hα : 1 / 2 < α) (hαβ : α < β) (hT : 0 < T)
    (hden : ∀ k, 1 - tangentIterate (verticalLowerIncrement α β T xiOrdinate) k
      * verticalLowerIncrement α β T xiOrdinate k ≠ 0) :
    ¬ Tendsto (tangentIterate (verticalLowerIncrement α β T xiOrdinate)) atTop atTop :=
  not_tendsto_atTop_verticalLowerRiccati hα hαβ hT xiOrdinate_pos
    tendsto_xiOrdinate_atTop tendsto_sum_inv_xiOrdinate_atTop hden

/-- **Outgoing channel.**  Likewise the upper Riccati sequence cannot tend to `-∞`. -/
theorem not_tendsto_atBot_verticalUpperRiccati_xiOrdinate
    (hα : 1 / 2 < α) (hαβ : α < β) (hT : 0 < T)
    (hden : ∀ k, 1 - tangentIterate (verticalUpperIncrement α β T xiOrdinate) k
      * verticalUpperIncrement α β T xiOrdinate k ≠ 0) :
    ¬ Tendsto (tangentIterate (verticalUpperIncrement α β T xiOrdinate)) atTop atBot :=
  not_tendsto_atBot_verticalUpperRiccati hα hαβ hT xiOrdinate_pos
    tendsto_xiOrdinate_atTop tendsto_sum_inv_xiOrdinate_atTop hden

/-- **Recurrent return.**  The incoming channel returns to zero along a subsequence. -/
theorem exists_subseq_verticalLowerRiccati_xiOrdinate_tendsto_zero
    (hα : 1 / 2 < α) (hαβ : α < β) (hT : 0 < T)
    (hden : ∀ k, 1 - tangentIterate (verticalLowerIncrement α β T xiOrdinate) k
      * verticalLowerIncrement α β T xiOrdinate k ≠ 0) :
    ∃ n : ℕ → ℕ, Tendsto n atTop atTop ∧
      Tendsto (fun m => tangentIterate (verticalLowerIncrement α β T xiOrdinate) (n m))
        atTop (𝓝 0) :=
  exists_subseq_verticalLowerRiccati_tendsto_zero hα hαβ hT xiOrdinate_pos
    tendsto_xiOrdinate_atTop tendsto_sum_inv_xiOrdinate_atTop hden

end

end RHTower
