import GaloisForLFunctions.HTGeometry.GammaFieldAbstractCollapse
import GaloisForLFunctions.HTGeometry.FinitePhaseLawFromRatios

/-!
# The finite phase law from a relation valid only far up the line

The collapse argument samples the relation along a Bohr return sequence, which tends to `+∞`, so the
relation is only ever used far up the vertical line.  Weakening the hypothesis from "the relation
holds at every point of `ℂ`" to "the relation holds eventually on the line" therefore costs nothing —
and it is the form in which a relation between germs at the upper end arrives.
-/

open Filter Topology Complex

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **Collapse from a relation sampled along the return sequence.** -/
theorem recurrence_collapse_to_autonomous_of_eventual {ι : Type*} (E : Finset ι)
    (F M : ι → ℂ → ℂ) (β : ι) (hβ : β ∈ E) (s₀ : ℂ) (T : ℕ → ℝ) (d : ι → ℂ)
    (hrel : ∀ᶠ l in atTop, ∑ α ∈ E, F α (s₀ + (T l : ℂ) * Complex.I)
      * M α (s₀ + (T l : ℂ) * Complex.I) = 0)
    (hFβ : ∀ᶠ l in atTop, F β (s₀ + (T l : ℂ) * Complex.I) ≠ 0)
    (hcoeff : ∀ α ∈ E, Tendsto
      (fun l => F α (s₀ + (T l : ℂ) * Complex.I) / F β (s₀ + (T l : ℂ) * Complex.I))
      atTop (nhds (d α)))
    (hmon : ∀ α ∈ E, Tendsto
      (fun l => M α (s₀ + (T l : ℂ) * Complex.I)) atTop (nhds (M α s₀))) :
    (∑ α ∈ E, d α * M α s₀ = 0) ∧ d β = 1 := by
  refine ⟨?_, ?_⟩
  · have hlim : Tendsto (fun l =>
        ∑ α ∈ E, (F α (s₀ + (T l : ℂ) * Complex.I) /
          F β (s₀ + (T l : ℂ) * Complex.I)) *
          M α (s₀ + (T l : ℂ) * Complex.I))
        atTop (nhds (∑ α ∈ E, d α * M α s₀)) := by
      apply tendsto_finsetSum
      intro α hα
      exact (hcoeff α hα).mul (hmon α hα)
    have hzeroLim : Tendsto (fun l =>
        ∑ α ∈ E, (F α (s₀ + (T l : ℂ) * Complex.I) /
          F β (s₀ + (T l : ℂ) * Complex.I)) *
          M α (s₀ + (T l : ℂ) * Complex.I)) atTop (nhds 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hFβ, hrel] with l hFβl hrell
      symm
      rw [show (∑ α ∈ E, (F α (s₀ + (T l : ℂ) * Complex.I) /
          F β (s₀ + (T l : ℂ) * Complex.I)) *
          M α (s₀ + (T l : ℂ) * Complex.I)) =
        (∑ α ∈ E, F α (s₀ + (T l : ℂ) * Complex.I) *
          M α (s₀ + (T l : ℂ) * Complex.I)) /
          F β (s₀ + (T l : ℂ) * Complex.I) by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl (fun α _ => by ring)]
      rw [hrell, zero_div]
    exact tendsto_nhds_unique hlim hzeroLim
  · have hlim := hcoeff β hβ
    have hOne : Tendsto
        (fun l => F β (s₀ + (T l : ℂ) * Complex.I) /
          F β (s₀ + (T l : ℂ) * Complex.I)) atTop (nhds 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hFβ] with l hFβl
      exact (div_self hFβl).symm
    exact tendsto_nhds_unique hlim hOne

/-- **Collapse from a relation valid far up the line.** -/
theorem recurrence_collapse_of_bohr_return_eventual {n : ℕ} (F M : Fin n → ℂ → ℂ) (β : Fin n)
    (s₀ : ℂ) (d : Fin n → ℂ)
    (hrel : ∀ᶠ t : ℝ in atTop, ∑ α, F α (s₀ + (t : ℂ) * Complex.I)
      * M α (s₀ + (t : ℂ) * Complex.I) = 0)
    (hMcont : ∀ α, Continuous fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I))
    (hMap : ∀ α, IsBohrAlmostPeriodic fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I))
    (hFβ : ∀ᶠ t : ℝ in atTop, F β (s₀ + (t : ℂ) * Complex.I) ≠ 0)
    (hcoeff : ∀ α, Tendsto
      (fun t : ℝ => F α (s₀ + (t : ℂ) * Complex.I) / F β (s₀ + (t : ℂ) * Complex.I))
      atTop (nhds (d α))) :
    (∑ α, d α * M α s₀ = 0) ∧ d β = 1 := by
  classical
  obtain ⟨T, hT, hret⟩ := exists_bohr_return_sequence_tendsto
    (g := fun α => fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I)) hMcont hMap
  have hmon : ∀ α ∈ (Finset.univ : Finset (Fin n)), Tendsto
      (fun l => M α (s₀ + (T l : ℂ) * Complex.I)) atTop (nhds (M α s₀)) := by
    intro α _
    have h := hret α 0
    have hzero : M α (s₀ + ((0 : ℝ) : ℂ) * Complex.I) = M α s₀ := by
      norm_num
    rw [hzero] at h
    refine h.congr fun l => ?_
    norm_num
  exact recurrence_collapse_to_autonomous_of_eventual Finset.univ F M β (Finset.mem_univ β) s₀ T d
    (hT.eventually hrel) (hT.eventually hFβ)
    (fun α _ => (hcoeff α).comp hT) hmon

/-- **Eq. (8) on the line, from a relation valid far up it.** -/
theorem line_relation_of_coeff_limits_eventual {n N : ℕ} {σ : ℝ} {Φ : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ) (d : Fin N → ℂ) (β : Fin N)
    (hcoeff : ∀ α, Tendsto (fun t : ℝ =>
      F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        / F β ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds (d α)))
    (hFβ : ∀ᶠ t : ℝ in atTop, F β ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hrel : ∀ᶠ t : ℝ in atTop, ∑ α, F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (e α i) = 0)
    (t₀ : ℝ) :
    jetPoly d e
      (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ
        ((σ : ℂ) + (t₀ : ℂ) * Complex.I)) = 0 := by
  classical
  set s₀ : ℂ := (σ : ℂ) + ((t₀ : ℝ) : ℂ) * Complex.I with hs₀
  set M : Fin N → ℂ → ℂ := fun α s => ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i)
    with hM
  have hjet : ∀ α : Fin N,
      Continuous (fun t : ℝ => M α ((σ : ℂ) + (t : ℂ) * Complex.I)) ∧
      IsBohrAlmostPeriodic (fun t : ℝ => M α ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    fun α => isBohrAlmostPeriodic_jetMonomial hR hΦ hap (e α)
  have hshift : Tendsto (fun t : ℝ => t + t₀) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_id
  have hfun : ∀ (g : ℂ → ℂ) (t : ℝ), g (s₀ + (t : ℂ) * Complex.I)
      = g ((σ : ℂ) + ((t + t₀ : ℝ) : ℂ) * Complex.I) := by
    intro g t
    rw [hs₀]
    push_cast
    ring_nf
  have hMcont : ∀ α : Fin N, Continuous fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I) := by
    intro α
    have hc := (hjet α).1
    have hcomp : (fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I))
        = fun t : ℝ => (fun u : ℝ => M α ((σ : ℂ) + (u : ℂ) * Complex.I)) (t + t₀) := by
      funext t
      exact hfun _ t
    rw [hcomp]
    exact hc.comp (continuous_id.add continuous_const)
  have hMap : ∀ α : Fin N,
      IsBohrAlmostPeriodic fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I) := by
    intro α
    have ha := (hjet α).2
    have hcomp : (fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I))
        = fun t : ℝ => (fun u : ℝ => M α ((σ : ℂ) + (u : ℂ) * Complex.I)) (t + t₀) := by
      funext t
      exact hfun _ t
    rw [hcomp]
    exact isBohrAlmostPeriodic_comp_add_const ha t₀
  have hcoeff' : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      F α (s₀ + (t : ℂ) * Complex.I) / F β (s₀ + (t : ℂ) * Complex.I)) atTop (nhds (d α)) := by
    intro α
    have h := (hcoeff α).comp hshift
    refine h.congr fun t => ?_
    simp only [Function.comp_apply]
    rw [hfun (F α) t, hfun (F β) t]
  have hFβ' : ∀ᶠ t : ℝ in atTop, F β (s₀ + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [hshift.eventually hFβ] with t ht
    rw [hfun (F β) t]
    exact ht
  have hrel' : ∀ᶠ t : ℝ in atTop, ∑ α, F α (s₀ + (t : ℂ) * Complex.I)
      * M α (s₀ + (t : ℂ) * Complex.I) = 0 := by
    filter_upwards [hshift.eventually hrel] with t ht
    have hchange : ∑ α, F α (s₀ + (t : ℂ) * Complex.I) * M α (s₀ + (t : ℂ) * Complex.I)
        = ∑ α, F α ((σ : ℂ) + ((t + t₀ : ℝ) : ℂ) * Complex.I)
          * M α ((σ : ℂ) + ((t + t₀ : ℝ) : ℂ) * Complex.I) :=
      Finset.sum_congr rfl fun α _ => by rw [hfun (F α) t, hfun (M α) t]
    rw [hchange]
    exact ht
  have hcollapse := recurrence_collapse_of_bohr_return_eventual F M β s₀ d hrel' hMcont hMap
    hFβ' hcoeff'
  have hval := hcollapse.1
  simpa [jetPoly, hM, hs₀] using hval

/-- **Eq. (8) on the strip, from a relation valid far up the line.** -/
theorem strip_relation_of_coeff_limits_eventual {n N : ℕ} {σ : ℝ} {Φ : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ) (d : Fin N → ℂ) (β : Fin N)
    (hcoeff : ∀ α, Tendsto (fun t : ℝ =>
      F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        / F β ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds (d α)))
    (hFβ : ∀ᶠ t : ℝ in atTop, F β ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hrel : ∀ᶠ t : ℝ in atTop, ∑ α, F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (e α i) = 0)
    {z : ℂ} (hz : z ∈ verticalStrip σ R) :
    jetPoly d e (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) = 0 :=
  jetPoly_eqOn_zero_of_line hR hΦ d e
    (fun t => line_relation_of_coeff_limits_eventual hR hΦ hap e F d β hcoeff hFβ hrel t) hz

/-- **Finite rank from a relation valid far up the line.** -/
theorem rank_finite_of_coeff_limits_eventual {n N : ℕ} {σ : ℝ} {Φ : ℂ → ℂ} {R r ρ : ℝ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R) (hR : 0 < R)
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ) (d : Fin N → ℂ) (β : Fin N)
    (hcoeff : ∀ α, Tendsto (fun t : ℝ =>
      F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        / F β ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop (nhds (d α)))
    (hFβ : ∀ᶠ t : ℝ in atTop, F β ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hrel : ∀ᶠ t : ℝ in atTop, ∑ α, F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (e α i) = 0)
    (he : Function.Injective e) (hdβ : d β ≠ 0)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  refine rank_finite_of_polynomial_relation hr hρ hrρ hΦ hap hf hfu hftb n _
    (monomialSum_ne_zero d e he β hdβ) ?_
  intro z hz
  rw [← jetPoly_eq_mvEval]
  exact strip_relation_of_coeff_limits_eventual hR hΦ hap e F d β hcoeff hFβ hrel hz

/-- **The law over the coefficient ratios, from a relation valid far up the line.** -/
theorem finite_phase_law_of_coeff_ratios_eventual {n N : ℕ} {σ R rr ρ : ℝ}
    (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ) (d : Fin N → ℂ) (β : Fin N)
    (hcoeff : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      F α ((σ : ℂ) + (t : ℂ) * Complex.I) / F β ((σ : ℂ) + (t : ℂ) * Complex.I))
      atTop (nhds (d α)))
    (hFβ : ∀ᶠ t : ℝ in atTop, F β ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) (hdβ : d β ≠ 0)
    (hrel : ∀ᶠ t : ℝ in atTop, ∑ α, F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (e α i) = 0)
    (he : Function.Injective e)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    (∀ z ∈ verticalStrip σ R,
        jetPoly d e (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) = 0)
      ∧ (∑ α : Fin N, MvPolynomial.C (d α)
          * ∏ i : Fin (n + 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) ℂ) ^ (e α i)) ≠ 0
      ∧ ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) :=
  ⟨fun _z hz => strip_relation_of_coeff_limits_eventual hR hΦ hap e F d β hcoeff hFβ hrel hz,
    monomialSum_ne_zero d e he β hdβ,
    rank_finite_of_coeff_limits_eventual hr hρ hrρ hR hΦ hap e F d β hcoeff hFβ hrel he hdβ
      hf hfu hftb⟩

/-- **The law from Gamma-jet data, with the relation only far up the line.** -/
theorem finite_phase_law_of_gammaJet_data_eventual {n N : ℕ} {σ R rr ρ : ℝ} (hσ : 0 < σ)
    (hN : 0 < N) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
    (u a dP b : Fin N → ℕ) (c : Fin N → ℂ) (hc : ∀ α, c α ≠ 0)
    (hF : ∀ α : Fin N, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaJetShape σ (u α) (a α) (dP α) (b α) t) atTop (nhds (c α)))
    (hrel : ∀ᶠ t : ℝ in atTop, ∑ α, F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (e α i) = 0)
    (he : Function.Injective e)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    ∃ (β : Fin N) (d : Fin N → ℂ), d β = 1
      ∧ (∀ z ∈ verticalStrip σ R,
        jetPoly d e (fun i : Fin (n + 1) => iteratedDeriv (i : ℕ) Φ z) = 0)
      ∧ (∑ α : Fin N, MvPolynomial.C (d α)
          * ∏ i : Fin (n + 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) ℂ) ^ (e α i)) ≠ 0
      ∧ ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  obtain ⟨β, r, hrlim, hrβ⟩ := exists_dominant_with_shape_ratios hσ hN u a dP b
  obtain ⟨hFβ, -, hcoeff⟩ := tendsto_family_ratio_of_normalized
    (F := fun α t => F α ((σ : ℂ) + (t : ℂ) * Complex.I))
    (shape := fun α => gammaJetShape σ (u α) (a α) (dP α) (b α)) (c := c) (r := r)
    β (hc β) (fun α => eventually_gammaJetShape_ne_zero hσ (u α) (a α) (dP α) (b α)) hF hrlim
  have hdβ : c β * r β / c β = 1 := self_ratio_eq_one β (hc β) hrβ
  refine ⟨β, fun α => c α * r α / c β, hdβ, ?_⟩
  exact finite_phase_law_of_coeff_ratios_eventual hr hρ hrρ hR hΦ hap e F _ β hcoeff hFβ
    (by rw [hdβ]; exact one_ne_zero) hrel he hf hfu hftb

end GaloisForLFunctions
