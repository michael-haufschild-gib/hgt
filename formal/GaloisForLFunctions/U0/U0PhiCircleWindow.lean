/-
# u₀ ⟂ φ — the circle-window reduction (relation needed only on a sub-window)

`U0PhiCard.u0_phi_no_relation_3var_open_crossing` fires the natural-boundary engine against a
relation assumed on ALL of `Ext`.  The genuine Böttcher-side supplier cannot deliver that: the
formalized `bottcherCoord` lives on the far field, and its eventual continuation `φ` will live on
some open basin window `Ω` reaching the unit circle (the Green-crossing).  A relation between `φ`
and `u₀` transported from a far-field carrier holds, a priori, only on an open piece `V` of
`Ω ∩ Ext`.

This file closes that gap: the relation on ANY nonempty open `V ⊆ Ω ∩ Ext` propagates to all of
`Ω ∩ Ext` by the identity theorem (the coefficient functions are analytic on `Ω`, `u₀` on `Ext`,
and `Ω ∩ Ext` is preconnected by hypothesis), and the generic engine
`NaturalBoundaryTranscendence.no_poly_relation_of_natural_boundary_arc` then fires at
`D = Ω ∩ Ext`: near a circle point `z₀ ∈ Ω` the window is invisible (`D ∩ ball = Ext ∩ ball` for
small balls), so `u0_natural_boundary` and `lens_preconnected` localize.

Why this interface and not the image-winding one: the deep-data certificate
`PhibImageWindingDeepData` demands a closed loop `γ` with `f^[k]∘γ` of ODD winding about `0`,
`γ` avoiding the bad set `B_k = (f^[k])⁻¹(escapeOpen b)ᶜ`.  Every component of `B_k` carries an
EVEN count of zeros of `f^[k]` (the target disk `{‖w‖ ≤ max 2 ‖b‖}` always contains the critical
value `b`, so `B₁` is one component of full degree `2`; preimage components multiply that degree),
hence by the argument principle every avoidable winding is even and that interface is
unsatisfiable.  The circle-window interface below is the corrected reduction; its one remaining
input is the analytic continuation `φ` of the Böttcher coordinate to a connected window touching
the unit circle — the same object the q62 continuation program is building.
-/
import GaloisForLFunctions.U0.NaturalBoundaryTranscendence

open Polynomial Filter Topology Complex Metric Set
open U0 U0NaturalBoundary U0Transcendence U0PhiCard NaturalBoundaryTranscendence

namespace U0PhiCircleWindow

/-- **Window localization of continuation.** Continuing `f` across `z₀` with respect to the
windowed domain `Ω ∩ D` is continuing it with respect to `D`, once `Ω` is a neighbourhood of
`z₀` — the two within-filters agree. -/
theorem continuesAcross_of_inter {f : ℂ → ℂ} {Ω D : Set ℂ} {z₀ : ℂ}
    (hΩ : Ω ∈ 𝓝 z₀) (h : ContinuesAcross f (Ω ∩ D) z₀) : ContinuesAcross f D z₀ := by
  obtain ⟨g, hg, hev⟩ := h
  refine ⟨g, hg, ?_⟩
  rwa [nhdsWithin_inter, nhdsWithin_eq_nhds.mpr hΩ,
    inf_eq_right.mpr nhdsWithin_le_nhds] at hev

/-- **The windowed relation contradiction (coefficient form).** Coefficients `a i` analytic on an
open preconnected window `Ω` containing a unit-circle point `z₁`, with `Ω ∩ Ext` preconnected;
the polynomial relation `∑ aᵢ(z)·u₀(z)ⁱ = 0` is assumed only on a nonempty open `V ⊆ Ω ∩ Ext`,
plus the separable-specialization data at some `w ∈ Ω`.  Then `False`.  This is
`u0_phi_card_step3` with the relation hypothesis weakened from all of `Ext` to the window piece
`V` — the form a far-field carrier transport can actually supply. -/
theorem u0_windowed_relation_false {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hDc : IsPreconnected (Ω ∩ Ext))
    {d : ℕ} (hd : 1 ≤ d)
    (a : Fin (d + 1) → ℂ → ℂ) (ha : ∀ i, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a (Fin.last d) w ≠ 0)
    (hsepw : (∑ i : Fin (d + 1), C (a i w) * X ^ (i : ℕ) : ℂ[X]).Separable)
    {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) (hz₁norm : ‖z₁‖ = 1)
    {V : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty) (hVD : V ⊆ Ω ∩ Ext)
    (hrelV : ∀ z ∈ V, ∑ i : Fin (d + 1), a i z * (u0 z) ^ (i : ℕ) = 0) : False := by
  -- the relation function is analytic on the window piece `Ω ∩ Ext`
  have hG : AnalyticOnNhd ℂ (fun z => ∑ i : Fin (d + 1), a i z * (u0 z) ^ (i : ℕ))
      (Ω ∩ Ext) := by
    intro z hz
    have h1 : AnalyticAt ℂ (∑ i : Fin (d + 1), fun z => a i z * (u0 z) ^ (i : ℕ)) z :=
      Finset.analyticAt_sum _
        (fun i _ => (ha i z hz.1).mul ((u0_analyticOnNhd_Ext z hz.2).pow _))
    have h2 : (∑ i : Fin (d + 1), fun z => a i z * (u0 z) ^ (i : ℕ))
        = fun z => ∑ i : Fin (d + 1), a i z * (u0 z) ^ (i : ℕ) := by
      funext y; simp
    rwa [h2] at h1
  -- identity theorem: the relation propagates from `V` to all of `Ω ∩ Ext`
  obtain ⟨v₀, hv₀⟩ := hVne
  have hev : (fun z => ∑ i : Fin (d + 1), a i z * (u0 z) ^ (i : ℕ)) =ᶠ[𝓝 v₀] 0 :=
    Filter.eventuallyEq_of_mem (hVo.mem_nhds hv₀) (fun z hz => hrelV z hz)
  have hrelD : Set.EqOn (fun z => ∑ i : Fin (d + 1), a i z * (u0 z) ^ (i : ℕ)) 0 (Ω ∩ Ext) :=
    hG.eqOn_zero_of_preconnected_of_eventuallyEq_zero hDc (hVD hv₀) hev
  -- fire the generic natural-boundary engine at `D = Ω ∩ Ext`
  refine no_poly_relation_of_natural_boundary_arc hd (D := Ω ∩ Ext) (f := u0)
    ((u0_analyticOnNhd_Ext.mono (fun z hz => hz.2)).continuousOn) hΩc a ha hw hleadw hsepw
    hz₁ (S := Ω ∩ {z : ℂ | ‖z‖ = 1}) (fun z hz => hz.1)
    (frequently_mem_open_unitCircle_of_mem hΩo hz₁ hz₁norm) ?_ ?_ ?_
  · -- every circle point of the window is a natural-boundary point for the windowed domain
    intro z₀ hz₀ hcont
    exact u0_natural_boundary z₀ hz₀.2
      (continuesAcross_of_inter (hΩo.mem_nhds hz₀.1) hcont)
  · -- the lens: inside the window, small balls do not see the window
    intro z₀ hz₀
    obtain ⟨r₀, hr₀pos, hball⟩ := Metric.isOpen_iff.mp hΩo z₀ hz₀.1
    refine ⟨min (1 / 2) (r₀ / 2), by positivity, ?_⟩
    intro ρ hρpos hρle
    have hsub : ball z₀ ρ ⊆ Ω := fun x hx =>
      hball (lt_of_lt_of_le (lt_of_lt_of_le hx.out
        (le_trans hρle (min_le_right _ _))) (by linarith))
    have hEq : (Ω ∩ Ext) ∩ ball z₀ ρ = Ext ∩ ball z₀ ρ := by
      ext x
      constructor
      · rintro ⟨⟨_, hxE⟩, hxb⟩; exact ⟨hxE, hxb⟩
      · rintro ⟨hxE, hxb⟩; exact ⟨⟨hsub hxb, hxE⟩, hxb⟩
    constructor
    · rw [hEq]
      exact lens_preconnected z₀ hz₀.2 hρpos (le_trans hρle (min_le_left _ _))
    · rw [hEq]
      refine ⟨((1 : ℝ) + ρ / 2) • z₀, ?_, ?_⟩
      · show (1 : ℝ) < ‖((1 : ℝ) + ρ / 2) • z₀‖
        rw [norm_smul, Real.norm_eq_abs, hz₀.2, mul_one, abs_of_pos (by linarith)]
        linarith
      · rw [mem_ball, dist_eq_norm,
          show ((1 : ℝ) + ρ / 2) • z₀ - z₀ = (ρ / 2) • z₀ by module,
          norm_smul, Real.norm_eq_abs, hz₀.2, mul_one, abs_of_pos (by linarith)]
        linarith
  · -- the propagated relation on `D`
    intro z hz
    simpa using hrelD hz

end U0PhiCircleWindow

namespace U0PhiCircleWindow

/-- **u₀ ⟂ φ, circle-window form (the corrected reduction).** No nonzero polynomial relation
`P(z, φ(z), u₀(z)) = 0` of positive `u₀`-degree can hold on a nonempty open piece `V` of the
window `Ω ∩ Ext`, given: `φ` analytic on the open preconnected window `Ω`, `Ω` touching the unit
circle at `z₁`, `Ω ∩ Ext` preconnected, and the separable-specialization data at some `w ∈ Ω`
(the minimal polynomial of `u₀` over `ℂ(z, φ)`, separable in characteristic 0).  Compared with
`u0_phi_no_relation_3var_open_crossing`, the relation is required only on `V` — exactly what a
far-field carrier transport supplies once `φ` continues the Böttcher coordinate into the window.
The lone remaining analytic input for the `u₀ ⟂ φ_b` cards is therefore the window continuation
`(Ω, φ)` itself with a Green-crossing circle point. -/
theorem u0_phi_windowed_no_relation_3var {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hDc : IsPreconnected (Ω ∩ Ext))
    {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ Ω)
    (P : (Polynomial (Polynomial ℂ))[X]) (hd : 1 ≤ P.natDegree)
    {w : ℂ} (hw : w ∈ Ω)
    (hleadw : (∑ i : Fin (P.natDegree + 1),
      C ((P.coeff i).eval₂ (evalRingHom w) (φ w)) * X ^ (i : ℕ) : ℂ[X]).coeff P.natDegree ≠ 0)
    (hsepw : (∑ i : Fin (P.natDegree + 1),
      C ((P.coeff i).eval₂ (evalRingHom w) (φ w)) * X ^ (i : ℕ) : ℂ[X]).Separable)
    {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) (hz₁norm : ‖z₁‖ = 1)
    {V : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty) (hVD : V ⊆ Ω ∩ Ext)
    (hrel : ∀ z ∈ V, P.eval₂ (eval₂RingHom (evalRingHom z) (φ z)) (u0 z) = 0) : False := by
  set d := P.natDegree with hd'
  set a : Fin (d + 1) → ℂ → ℂ := fun i z => (P.coeff i).eval₂ (evalRingHom z) (φ z) with ha'
  have ha : ∀ i, AnalyticOnNhd ℂ (a i) Ω := fun i => eval_phi_analytic hφ (P.coeff i)
  have hlead : a (Fin.last d) w ≠ 0 := by
    have hc : (∑ i : Fin (d + 1), C (a i w) * X ^ (i : ℕ) : ℂ[X]).coeff d = a (Fin.last d) w := by
      rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (Fin.last d)]
      · rw [coeff_C_mul, coeff_X_pow, Fin.val_last]; simp
      · intro i _ hi
        rw [coeff_C_mul, coeff_X_pow,
          if_neg (fun h => hi (Fin.ext (h.symm.trans (Fin.val_last d).symm))), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [← hc]; exact hleadw
  have hrelV : ∀ z ∈ V, ∑ i : Fin (d + 1), a i z * (u0 z) ^ (i : ℕ) = 0 := by
    intro z hz
    have hz0 := hrel z hz
    rw [eval₂_eq_sum_range] at hz0
    rw [show (∑ i : Fin (d + 1), a i z * (u0 z) ^ (i : ℕ))
          = ∑ k ∈ Finset.range (d + 1), (P.coeff k).eval₂ (evalRingHom z) (φ z) * (u0 z) ^ k from
        Fin.sum_univ_eq_sum_range
          (fun k => (P.coeff k).eval₂ (evalRingHom z) (φ z) * (u0 z) ^ k) (d + 1)]
    exact hz0
  exact u0_windowed_relation_false hΩo hΩc hDc hd a ha hw hlead hsepw hz₁ hz₁norm
    hVo hVne hVD hrelV

end U0PhiCircleWindow
