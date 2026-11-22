import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.SingleCut.Survival

/-! # Infinite ninth moment of the distinguished first excursion -/
open MeasureTheory ProbabilityTheory Filter Set
namespace GaloisForLFunctions.HTGeometry.WeakBonds.SingleCut
noncomputable section
open PrescribedTimes

/-- A Gaussian prefix and the same prefix normalized to any positive
coupling norm both have infinite ninth absolute moment of the smaller
of onset and elapsed first-return time. -/
theorem gaussian_one_bond_ninth_moment :
    ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let P := nearHilbertContinuousCircuitBudget (n+2)
      let μ := Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)
      ∀ s ≤ P/2, let J := fun x => min (crossingOrigin n P (9/80) x) (crossingWait n P s x)
      (¬ Integrable (fun x => |J x|^9) μ) ∧ ∀ r > (0:ℝ),
        ¬ Integrable (fun x => |J (atRadius r x)|^9) μ := by
  filter_upwards [gaussian_one_bond_survival] with k hk
  intro n P μ s hs J
  obtain ⟨c,hc,h⟩ := hk
  have hm : Measurable J := (measurable_crossingOrigin ..).min (measurable_crossingWait ..)
  let E (T : ℝ) := {x | 1 ≤ coefficientNorm x ∧ T < crossingOrigin n P (9/80) x ∧ ∀ s ≤ P/2, T < crossingWait n P s x}
  have hE {T : ℝ} {x : PrefixIndex n→ℝ} (hx : x∈E T) : T < J x := lt_min hx.2.1 (hx.2.2 s hs)
  constructor
  · apply not_integrable_boundary_moment μ J hm 9 (B:=1) zero_lt_one (half_pos hc)
    intro T hT
    rw [mul_one]
    exact ((half_lt_self hc).trans_le (h T hT)).trans_le (mul_le_mul_of_nonneg_left
      (measureReal_mono (fun _ hx => hE hx : E T ⊆ {x | T < J x})) (pow_nonneg (zero_le_one.trans hT) _))
  · intro r hr
    have hnorm : Measurable (coefficientNorm (n:=n)) :=
      (continuous_norm.comp (PiLp.continuous_toLp 2 _)).measurable
    have hrad : Measurable (atRadius (n:=n) r) := (measurable_const.div hnorm).smul measurable_id
    apply not_integrable_boundary_moment μ _ (hm.comp hrad) 9 (B:=1/r) (one_div_pos.mpr hr) (half_pos hc)
    intro T hT
    have hsub : E T ⊆ {x | T*(1/r) < J (atRadius r x)} := by
      intro x hx
      have hp := zero_lt_one.trans_le hx.1
      let q := r/coefficientNorm x
      have hq : 0 < q := div_pos hr hp
      have hj : q*J (atRadius r x)=J x := by
        change q*min (crossingOrigin n P (9/80) (q • x)) (crossingWait n P s (q • x))=_
        rw [mul_min_of_nonneg _ _ hq.le,smul_crossingOrigin _ _ _ hq,smul_crossingWait _ _ _ hq]
      have hq' : q ≤ r := div_le_self hr.le hx.1
      have hTq : q*(T*(1/r)) ≤ T := by
        calc _ ≤ r*(T*(1/r)) := mul_le_mul_of_nonneg_right hq' (by positivity)
             _ = T := by field_simp
      exact (mul_lt_mul_iff_right₀ hq).mp (hTq.trans_lt ((hE hx).trans_eq hj.symm))
    exact ((half_lt_self hc).trans_le (h T hT)).trans_le (mul_le_mul_of_nonneg_left
      (measureReal_mono hsub) (pow_nonneg (zero_le_one.trans hT) _))

#print axioms gaussian_one_bond_ninth_moment
end
end GaloisForLFunctions.HTGeometry.WeakBonds.SingleCut
