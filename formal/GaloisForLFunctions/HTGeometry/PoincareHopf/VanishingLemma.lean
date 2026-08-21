import GaloisForLFunctions.HTGeometry.PoincareHopf.DivergenceForm

/-!
# The fundamental vanishing lemma of degree theory

A `C¹` field on `ℝⁿ` that vanishes on a neighbourhood of the boundary of a bounded open set `Ω` has
vanishing total divergence over `Ω`: its zero extension is a globally `C¹` compactly supported
field, so the divergence theorem applies with no boundary term.

Specialising to the Piola field `V j = ∑ i, cof (Du)_{i j} · (W ∘ u) i`, whose divergence is
`(div W) ∘ u · det (Du)`, gives

  `∫_Ω (div W) (u x) · det (Du x) dx = 0`

whenever `W` vanishes outside the ball of radius `ρ` and `‖u‖ > ρ` on `∂Ω`.  Every invariance
property of the Brouwer degree is a corollary of this statement.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {u W V : (Fin n → ℝ) → (Fin n → ℝ)} {Ω : Set (Fin n → ℝ)} {ρ : ℝ}

theorem fieldDivergence_eq_zero_of_eventuallyEq_zero {x : Fin n → ℝ}
    (h : V =ᶠ[nhds x] 0) : fieldDivergence V x = 0 := by
  have hz : fderiv ℝ V x = 0 := by rw [h.fderiv_eq]; simp
  simp [fieldDivergence, hz]

theorem fieldDivergence_congr_of_eventuallyEq {V' : (Fin n → ℝ) → (Fin n → ℝ)}
    {x : Fin n → ℝ} (h : V =ᶠ[nhds x] V') : fieldDivergence V x = fieldDivergence V' x := by
  simp [fieldDivergence, h.fderiv_eq]

section Core

/-- Off `Ω` the zero extension of a field vanishing near `∂Ω` vanishes on a neighbourhood. -/
theorem indicator_eventuallyEq_zero (hΩ : IsOpen Ω)
    (hfront : ∀ x ∈ frontier Ω, V =ᶠ[nhds x] 0) {x : Fin n → ℝ} (hx : x ∉ Ω) :
    Ω.indicator V =ᶠ[nhds x] 0 := by
  by_cases hcl : x ∈ closure Ω
  · have hxf : x ∈ frontier Ω := by rw [hΩ.frontier_eq]; exact ⟨hcl, hx⟩
    filter_upwards [hfront x hxf] with z hz
    by_cases hzΩ : z ∈ Ω
    · rw [Set.indicator_of_mem hzΩ, hz]
    · rw [Set.indicator_of_notMem hzΩ]
      rfl
  · have hopen : IsOpen (closure Ω)ᶜ := isClosed_closure.isOpen_compl
    filter_upwards [hopen.mem_nhds hcl] with z hz
    exact Set.indicator_of_notMem (fun h => hz (subset_closure h)) _

theorem contDiff_indicator (hV : ContDiff ℝ 1 V) (hΩ : IsOpen Ω)
    (hfront : ∀ x ∈ frontier Ω, V =ᶠ[nhds x] 0) : ContDiff ℝ 1 (Ω.indicator V) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ω
  · have hev : Ω.indicator V =ᶠ[nhds x] V := by
      filter_upwards [hΩ.mem_nhds hx] with z hz
      exact Set.indicator_of_mem hz _
    exact hV.contDiffAt.congr_of_eventuallyEq hev
  · exact (contDiffAt_const (c := (0 : Fin n → ℝ))).congr_of_eventuallyEq
      (indicator_eventuallyEq_zero hΩ hfront hx)

theorem hasCompactSupport_indicator (hΩb : Bornology.IsBounded Ω) :
    HasCompactSupport (Ω.indicator V) := by
  refine HasCompactSupport.intro
    (K := closure Ω) (Metric.isCompact_of_isClosed_isBounded isClosed_closure hΩb.closure) ?_
  intro x hx
  exact Set.indicator_of_notMem (fun h => hx (subset_closure h)) _

/-- **The fundamental vanishing lemma.**  A `C¹` field vanishing near the boundary of a bounded
open set has zero total divergence over that set. -/
theorem integral_fieldDivergence_of_vanishing_near_frontier
    (hV : ContDiff ℝ 1 V) (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hfront : ∀ x ∈ frontier Ω, V =ᶠ[nhds x] 0) :
    ∫ x in Ω, fieldDivergence V x = 0 := by
  have h0 : ∫ x, fieldDivergence (Ω.indicator V) x = 0 :=
    integral_fieldDivergence_eq_zero (contDiff_indicator hV hΩ hfront)
      (hasCompactSupport_indicator hΩb)
  have hout : ∀ x ∉ Ω, fieldDivergence (Ω.indicator V) x = 0 := fun x hx =>
    fieldDivergence_eq_zero_of_eventuallyEq_zero (indicator_eventuallyEq_zero hΩ hfront hx)
  have hin : ∀ x ∈ Ω, fieldDivergence (Ω.indicator V) x = fieldDivergence V x := by
    intro x hx
    refine fieldDivergence_congr_of_eventuallyEq ?_
    filter_upwards [hΩ.mem_nhds hx] with z hz
    exact Set.indicator_of_mem hz _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout] at h0
  rw [← h0]
  exact (setIntegral_congr_fun hΩ.measurableSet hin).symm

end Core

theorem piolaField_eq_zero_of_le (hWball : ∀ w, ρ ≤ ‖w‖ → W w = 0) {x : Fin n → ℝ}
    (hx : ρ ≤ ‖u x‖) : piolaField u W x = 0 := by
  funext j
  simp [piolaField, hWball _ hx]

/-- Where `‖u‖` exceeds the radius of the support of `W`, the Piola field vanishes identically on a
neighbourhood. -/
theorem piolaField_eventuallyEq_zero (hu : ContDiff ℝ 2 u)
    (hWball : ∀ w, ρ ≤ ‖w‖ → W w = 0) {x : Fin n → ℝ} (hx : ρ < ‖u x‖) :
    piolaField u W =ᶠ[nhds x] 0 := by
  have hcont : Continuous fun z => ‖u z‖ := hu.continuous.norm
  have hopen : IsOpen {z : Fin n → ℝ | ρ < ‖u z‖} := isOpen_lt continuous_const hcont
  filter_upwards [hopen.mem_nhds hx] with z hz
  exact piolaField_eq_zero_of_le hWball hz.le

/-- **The vanishing lemma in divergence form.** -/
theorem integral_divergence_comp_det_eq_zero
    (hu : ContDiff ℝ 2 u) (hW : ContDiff ℝ 1 W)
    (hWball : ∀ w, ρ ≤ ‖w‖ → W w = 0)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    (hfront : ∀ x ∈ frontier Ω, ρ < ‖u x‖) :
    ∫ x in Ω, fieldDivergence W (u x) * (jac u x).det = 0 := by
  have hzero := integral_fieldDivergence_of_vanishing_near_frontier
    (contDiff_piolaField hu hW) hΩ hΩb
    (fun x hx => piolaField_eventuallyEq_zero hu hWball (hfront x hx))
  rw [← hzero]
  exact (setIntegral_congr_fun hΩ.measurableSet
    (fun x _ => fieldDivergence_piolaField hu hW x)).symm

end GaloisForLFunctions.HTGeometry.PoincareHopf
