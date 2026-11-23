import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.SmallTimeLaw.ContinuousRate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.PhysicalSpeed.EarlyTail

/-! # Gaussian large deviations for the first physical excursion -/
open MeasureTheory ProbabilityTheory Filter Real Set Topology
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.SmallTimeLaw
open ShortWindows LocalPatches.PhysicalSpeed
noncomputable section

private theorem early_rate_bound {p : ℝ → ℝ} {A M L : ℝ} (hM : 0 < M)
    (hp : ∀ t > 0, 0 < p t) (hbound : ∀ t > 0, p t ≤ M*exp (-(A/t)^2/2))
    (hr : Tendsto (fun t : ℝ => t^2*log (p t)) (𝓝[>] 0) (𝓝 L)) : L ≤ -A^2/2 := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hlim : Tendsto (fun t : ℝ => t^2*log M-A^2/2) (𝓝[>] 0) (𝓝 (-A^2/2)) := by
    simpa only [zero_pow two_ne_zero,zero_mul,zero_sub,neg_div] using
      ((ht.pow 2).mul_const (log M)).sub_const (A^2/2)
  apply le_of_tendsto_of_tendsto hr hlim
  filter_upwards [self_mem_nhdsWithin] with t ht'
  have ht₀ : 0 < t := ht'
  have h := log_le_log (hp t ht₀) (hbound t ht₀)
  rw [log_mul hM.ne' (exp_pos _).ne',log_exp] at h
  apply (mul_le_mul_of_nonneg_left h (sq_nonneg t)).trans_eq
  field_simp [ht₀.ne']
  <;> ring

/-- Either an early onset or an early first half-budget return has a sharp
finite inverse-square-time exponent. The same speed bound applies to the
joint early event with the first empty return. All probabilities concern
the two stopping times of one physical prefix. -/
theorem gaussian_first_excursion_small_deadlines :
    ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let P := nearHilbertContinuousCircuitBudget N
      let σ := crossingOrigin (k+1) P (9/80)
      let Δ := crossingWait (k+1) P
      ∀ F ∈ ({fun x => min (σ x) (Δ (P/2) x), fun x => max (σ x) (Δ 0 x)} :
        Set ((PrefixIndex (k+1) → ℝ) → ℝ)),
        let μ := Measure.pi fun _ : PrefixIndex (k+1) => gaussianReal 0 1
        let L := log (essSup (unitWeight F) μ)
        L ≤ -(travelProduct N)^2/2 ∧
          Tendsto (fun t : ℝ => t^2*log (pathPauliDisorderLaw.real {ω | F (prefixPoint k ω) ≤ t}))
            (𝓝[>] 0) (𝓝 L) := by
  filter_upwards [gaussian_early_first_passage_tail] with k hk
  intro N P σ Δ F hF μ L
  have hcases : F=(fun x => min (σ x) (Δ (P/2) x)) ∨ F=(fun x => max (σ x) (Δ 0 x)) := hF
  have hf : Measurable F := by
    rcases hcases with rfl|rfl
    · exact (measurable_crossingOrigin ..).min (measurable_crossingWait ..)
    · exact (measurable_crossingOrigin ..).max (measurable_crossingWait ..)
  have hom (a : ℝ) (ha : 0<a) (x : PrefixIndex (k+1) → ℝ) : a*F (a • x)=F x := by
    have hσ := smul_crossingOrigin (k+1) P (9/80) ha x
    have hΔ := fun s => smul_crossingWait (k+1) P s ha x
    rcases hcases with rfl|rfl
    · change a*min _ _=min _ _
      rw [mul_min_of_nonneg _ _ ha.le,hσ,hΔ]
    · change a*max _ _=max _ _
      rw [mul_max_of_nonneg _ _ ha.le,hσ,hΔ]
  let p (t : ℝ) := pathPauliDisorderLaw.real {ω | F (prefixPoint k ω) ≤ t}
  have he (t) : p t=μ.real {x | F x ≤ t} := (gaussian_pauli_prefix_coordinates_law (k+1)).measureReal_preimage
    (measurableSet_le hf measurable_const).nullMeasurableSet
  have hh := gaussian_continuous_passage_rate F hf hom
  have hr : Tendsto (fun t : ℝ => t^2*log (p t)) (𝓝[>] 0) (𝓝 L) := by simpa only [he] using hh
  refine ⟨?_,hr⟩
  let m := Fintype.card (ChainLabel N)
  have hm : 0 < m := Fintype.card_pos_iff.mpr (instNonemptyChainLabel (k+2))
  apply early_rate_bound (M:=2*(m:ℝ)) (by positivity) _ _ hr
  · intro t ht
    rw [he]
    exact ENNReal.toReal_pos (deadline_pos F hf hom ht).ne' (measure_ne_top _ _)
  · intro t ht
    apply le_trans _ (hk t ht)
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro ω hx
    rcases hcases with rfl|rfl
    · rcases min_le_iff.mp hx with h|h
      · exact Or.inl h
      · exact Or.inr ⟨P/2,le_rfl,h⟩
    · exact Or.inl ((le_max_left ..).trans hx)

#print axioms gaussian_first_excursion_small_deadlines
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.SmallTimeLaw
