import GaloisForLFunctions.RHTower.PaperThetaParameterTraces
import GaloisForLFunctions.RHTower.PaperThetaCutMeyerCurrent

/-! # Admitted confluent theta parametrices

These are derivatives of the literal modes. Every order is admitted after
one finite cut. Below each full Xi multiplicity the cut disappears, so the
same construction gives native whole-line BV jets without a simplicity premise.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

def parameterEndpointTrace (n : ℕ) : ℂ := if n = 0 then -1 else 0

def leftParameterJet (n : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  (-1 : ℂ)^n * flatParameterJet n (-z) (-x)

def cutParameterJet (n : ℕ) (z : ℂ) (a x : ℝ) : ℂ :=
  iteratedDeriv n (fun w => cutQuotient w a x) z

theorem leftParameterJet_eq (n : ℕ) (z : ℂ) (x : ℝ) :
    leftParameterJet n z x = iteratedDeriv n (fun w => leftQuotient w x) z := by
  exact (iteratedDeriv_comp_neg n (fun w => flatQuotient w (-x)) z).symm

theorem cutParameterJet_left (n : ℕ) (z : ℂ) {a x : ℝ} (hx : x < a) :
    cutParameterJet n z a x = leftParameterJet n z x := by
  simp only [cutParameterJet, cutQuotient, if_pos hx, leftParameterJet_eq]

theorem cutParameterJet_right (n : ℕ) (z : ℂ) {a x : ℝ} (hx : a ≤ x) :
    cutParameterJet n z a x = flatParameterJet n z x := by
  simp only [cutParameterJet, cutQuotient, if_neg (not_lt.mpr hx), flatParameterJet]

theorem continuous_leftParameterJet (n : ℕ) (z : ℂ) : Continuous (leftParameterJet n z) :=
  ((continuous_flatParameterJet n (-z)).comp continuous_neg).const_mul _

theorem tendsto_flatParameterJet_atTop (n : ℕ) (z : ℂ) :
    Tendsto (flatParameterJet n z) atTop (𝓝 (parameterEndpointTrace n)) := by
  cases n with
  | zero => exact tendsto_flatQuotient_atTop z
  | succ n => simpa only [parameterEndpointTrace, Nat.succ_ne_zero, if_false]
      using tendsto_flatParameterJet_succ_atTop n z

theorem tendsto_leftParameterJet_atBot (n : ℕ) (z : ℂ) :
    Tendsto (leftParameterJet n z) atBot (𝓝 (parameterEndpointTrace n)) := by
  have h := ((tendsto_flatParameterJet_atTop n (-z)).comp tendsto_neg_atBot_atTop).const_mul
    ((-1 : ℂ)^n)
  have he : (-1 : ℂ)^n * parameterEndpointTrace n = parameterEndpointTrace n := by
    cases n <;> simp [parameterEndpointTrace]
  rw [he] at h
  exact h

theorem boundedVariationOn_leftParameterJet_Iic (n : ℕ) (z : ℂ) (a : ℝ) :
    BoundedVariationOn (leftParameterJet n z) (Iic a) := by
  have h : BoundedVariationOn (fun x : ℝ => flatParameterJet n (-z) (-x)) (Iic a) := by
    apply ne_top_of_le_ne_top (boundedVariationOn_flatParameterJet_Ici n (-z) (-a))
    apply eVariationOn.comp_le_of_antitoneOn (flatParameterJet n (-z))
      (s := Ici (-a)) (fun x : ℝ => -x) (fun _ _ _ _ h => neg_le_neg h)
    intro x hx
    exact neg_le_neg (show x ≤ a from hx)
  exact (lipschitzWith_smul ((-1 : ℂ)^n)).comp_boundedVariationOn h

theorem tendsto_cutParameterJet_left (n : ℕ) (z : ℂ) (a : ℝ) :
    Tendsto (cutParameterJet n z a) (𝓝[<] a) (𝓝 (leftParameterJet n z a)) := by
  apply ((continuous_leftParameterJet n z).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (cutParameterJet_left n z hx).symm

theorem tendsto_cutParameterJet_right (n : ℕ) (z : ℂ) (a : ℝ) :
    Tendsto (cutParameterJet n z a) (𝓝[>] a) (𝓝 (flatParameterJet n z a)) := by
  apply ((continuous_flatParameterJet n z).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact (cutParameterJet_right n z (show a ≤ x from hx.le)).symm

/-- A single finite cut admits every differentiated source mode, at every parameter. -/
theorem boundedVariationOn_cutParameterJet (n : ℕ) (z : ℂ) (a : ℝ) :
    BoundedVariationOn (cutParameterJet n z a) univ := by
  have hl : eVariationOn (cutParameterJet n z a) (Iio a) ≠ ⊤ := by
    rw [eVariationOn.congr (s := Iio a) (fun x hx => cutParameterJet_left n z hx)]
    exact (boundedVariationOn_leftParameterJet_Iic n z a).mono Iio_subset_Iic_self
  have hlc : eVariationOn (cutParameterJet n z a) (Iic a) ≠ ⊤ := by
    have he := eVariationOn.eVariationOn_on_inter_Iic_eq_Iio_add_edist
      (f := cutParameterJet n z a) (s := univ) (a := a)
      (l := leftParameterJet n z a) (by simpa using (inferInstance : (𝓝[<] a).NeBot))
      (mem_univ a) (by simpa using tendsto_cutParameterJet_left n z a)
    simp only [univ_inter] at he
    rw [he]
    exact ENNReal.add_ne_top.mpr ⟨hl, edist_ne_top _ _⟩
  have hr : eVariationOn (cutParameterJet n z a) (Ici a) ≠ ⊤ := by
    rw [eVariationOn.congr (s := Ici a) (fun x hx => cutParameterJet_right n z hx)]
    exact boundedVariationOn_flatParameterJet_Ici n z a
  have hu : Iic a ∪ Ici a = (univ : Set ℝ) := by
    ext x
    simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
    exact le_total x a
  change eVariationOn (cutParameterJet n z a) univ ≠ ⊤
  have he := eVariationOn.union (cutParameterJet n z a) (s := Iic a) (t := Ici a) (x := a)
    ⟨by simp, fun _ h => h⟩ ⟨by simp, fun _ h => h⟩
  rw [hu] at he
  rw [he]
  exact ENNReal.add_ne_top.mpr ⟨hlc, hr⟩

theorem tendsto_cutParameterJet_atTop (n : ℕ) (z : ℂ) (a : ℝ) :
    Tendsto (cutParameterJet n z a) atTop (𝓝 (parameterEndpointTrace n)) := by
  apply (tendsto_flatParameterJet_atTop n z).congr'
  filter_upwards [eventually_ge_atTop a] with x hx
  exact (cutParameterJet_right n z hx).symm

theorem tendsto_cutParameterJet_atBot (n : ℕ) (z : ℂ) (a : ℝ) :
    Tendsto (cutParameterJet n z a) atBot (𝓝 (parameterEndpointTrace n)) := by
  apply (tendsto_leftParameterJet_atBot n z).congr'
  filter_upwards [eventually_lt_atBot a] with x hx
  exact (cutParameterJet_left n z hx).symm

/-- The scalar charge jet is the actual jump between admitted branch traces. -/
theorem flatParameterJet_sub_left (n : ℕ) (z : ℂ) (a : ℝ) :
    flatParameterJet n z a-leftParameterJet n z a =
      iteratedDeriv n (fun w => cutCharge w a) z := by
  have hl : Differentiable ℂ (fun w => leftQuotient w a) :=
    (differentiable_flatQuotient_parameter (-a)).comp differentiable_neg
  rw [leftParameterJet_eq]
  change _ = iteratedDeriv n (fun w => flatQuotient w a-leftQuotient w a) z
  rw [iteratedDeriv_fun_sub
    ((differentiable_flatQuotient_parameter a).analyticAt z).contDiffAt
    (hl.analyticAt z).contDiffAt]
  rfl

theorem cutParameterJet_eq_native (rho : XiDivisorSupport)
    (j : Fin (xiSupportMultiplicity rho)) (a x : ℝ) :
    cutParameterJet j.val (xiSpectralPointSupport rho) a x =
      flatParameterJet j.val (xiSpectralPointSupport rho) x := by
  by_cases hx : x < a
  · rw [cutParameterJet_left _ _ hx]
    have hj := (cutCharge_full_multiplicity_jets rho x).1 j.val j.isLt
    rw [← flatParameterJet_sub_left] at hj
    exact (sub_eq_zero.mp hj).symm
  · exact cutParameterJet_right _ _ (le_of_not_gt hx)

/-- All confluent slots below the full multiplicity are genuine native BV modes. -/
theorem boundedVariationOn_divisor_flatParameterJet (rho : XiDivisorSupport)
    (j : Fin (xiSupportMultiplicity rho)) :
    BoundedVariationOn (flatParameterJet j.val (xiSpectralPointSupport rho)) univ := by
  have he := funext (cutParameterJet_eq_native rho j 0)
  rw [← he]
  exact boundedVariationOn_cutParameterJet _ _ _

/-- The first terminal cut carries a nonzero jump in the actual admitted family. -/
theorem terminalParameterJet_jump_ne_zero (rho : XiDivisorSupport) (a : ℝ) :
    flatParameterJet (xiSupportMultiplicity rho) (xiSpectralPointSupport rho) a -
      leftParameterJet (xiSupportMultiplicity rho) (xiSpectralPointSupport rho) a ≠ 0 := by
  rw [flatParameterJet_sub_left]
  exact (cutCharge_full_multiplicity_jets rho a).2

end RHTower.PaperThetaEndpoint
