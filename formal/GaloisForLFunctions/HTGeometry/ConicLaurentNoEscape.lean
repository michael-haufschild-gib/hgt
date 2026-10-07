import GaloisForLFunctions.HTGeometry.ConicInteriorLimit
import GaloisForLFunctions.HTGeometry.ToricConicCorner
import GaloisForLFunctions.Bottcher.DiskAlgebraicContinuation
import Mathlib.Topology.Order.IntermediateValue

/-!
# No finite Laurent asymptotic values on the logarithmic conic

The exponential pair compactifies in `(ℂ ∪ {∞})²`. Interior cluster points are
excluded by the mixed product identity, and a single boundary coordinate is
excluded by the Laurent equation. Connected tails select one of four remaining
corners; the covering-limit argument excludes that corner.
-/

namespace GaloisForLFunctions.HTGeometry.ConicLaurentNoEscape

open Filter Topology Set Complex ToricConicCorner ConicInteriorLimit
open scoped OnePoint

theorem laurent_comm (x y : ℂ) : laurent x y = laurent y x := by
  dsimp [laurent]
  ring

@[simp] theorem laurent_inv_left (x y : ℂ) : laurent x⁻¹ y = laurent x y := by
  simp only [laurent, inv_inv]
  ring

@[simp] theorem laurent_inv_right (x y : ℂ) : laurent x y⁻¹ = laurent x y := by
  simp only [laurent, inv_inv]
  ring

theorem no_single_zero {A : Type*} {l : Filter A} [l.NeBot] {x y : A → ℂ} {y₀ d : ℂ}
    (hx : Tendsto x l (𝓝 0)) (hy : Tendsto y l (𝓝 y₀)) (hy₀ : y₀ ≠ 0)
    (hxne : ∀ t, x t ≠ 0) (hyne : ∀ t, y t ≠ 0)
    (hd : Tendsto (fun t ↦ laurent (x t) (y t)) l (𝓝 d)) : False := by
  have h₀ : Tendsto (fun t ↦ (laurent (x t) (y t) - y t - (y t)⁻¹) * x t)
      l (𝓝 0) := by
    simpa using ((hd.sub hy).sub (hy.inv₀ hy₀)).mul hx
  have h₁ : Tendsto (fun t ↦ (laurent (x t) (y t) - y t - (y t)⁻¹) * x t)
      l (𝓝 1) := by
    have hlim : Tendsto (fun t ↦ x t ^ 2 + 1) l (𝓝 1) := by
      simpa using (hx.pow 2).add_const 1
    apply hlim.congr'
    exact Eventually.of_forall fun t ↦ by
      dsimp [laurent]
      field_simp [hxne t, hyne t]
      ring
  exact zero_ne_one (tendsto_nhds_unique h₀ h₁)

theorem inv_limit_of_onePoint {A : Type*} {l : Filter A} {f : A → ℂ}
    (h : Tendsto (fun t ↦ (f t : OnePoint ℂ)) l (𝓝 ∞)) :
    Tendsto (fun t ↦ (f t)⁻¹) l (𝓝 0) := by
  apply tendsto_inv₀_cobounded.comp
  simpa only [Metric.cobounded_eq_cocompact] using escape_of_onePoint h

theorem no_interior_on_escape {A : Type*} (U : Ultrafilter A) {a b : A → ℂ}
    {C x d : ℂ} {y : OnePoint ℂ} (hconic : ∀ t, a t ^ 2 + b t ^ 2 = C)
    (he : Tendsto (fun t ↦ (a t, b t)) U (cocompact (ℂ × ℂ)))
    (hx : x ≠ 0) (hxa : Tendsto (fun t ↦ exp (a t)) U (𝓝 x))
    (hyb : Tendsto (fun t ↦ (exp (b t) : OnePoint ℂ)) U (𝓝 y))
    (hd : Tendsto (fun t ↦ laurent (exp (a t)) (exp (b t))) U (𝓝 d)) : False := by
  cases y using OnePoint.rec with
  | infty =>
    have hy := inv_limit_of_onePoint hyb
    have hdn : Tendsto (fun t ↦ laurent (exp (b t))⁻¹ (exp (a t))) U (𝓝 d) := by
      simpa only [laurent_inv_left, laurent_comm (exp (b _))] using hd
    exact no_single_zero hy hxa hx (fun t ↦ inv_ne_zero (exp_ne_zero (b t)))
      (fun t ↦ exp_ne_zero (a t)) hdn
  | coe y =>
    have hy := finite_limit_of_onePoint hyb
    by_cases hy₀ : y = 0
    · subst y
      have hdn : Tendsto (fun t ↦ laurent (exp (b t)) (exp (a t))) U (𝓝 d) := by
        simpa only [laurent_comm (exp (b _))] using hd
      exact no_single_zero hy hxa hx (fun t ↦ exp_ne_zero (b t))
        (fun t ↦ exp_ne_zero (a t)) hdn
    · obtain ⟨a₀, b₀, ha, hb⟩ := conic_interior_limits U hconic hx hy₀ hxa hy
      exact not_finite_and_escape (ha.prodMk_nhds hb) he

def boundary : Set (OnePoint ℂ) := {((0 : ℂ) : OnePoint ℂ), ∞}

theorem boundary_finite : boundary.Finite := by
  exact (finite_singleton _).insert _

theorem pair_cluster_boundary {a b : ℝ → ℂ} {C d : ℂ}
    (hconic : ∀ t, a t ^ 2 + b t ^ 2 = C)
    (he : Tendsto (fun t ↦ (a t, b t)) atTop (cocompact (ℂ × ℂ)))
    (hd : Tendsto (fun t ↦ laurent (exp (a t)) (exp (b t))) atTop (𝓝 d))
    {p : OnePoint ℂ × OnePoint ℂ}
    (hp : MapClusterPt p atTop (fun t ↦ ((exp (a t) : OnePoint ℂ), (exp (b t) : OnePoint ℂ)))) :
    p ∈ boundary ×ˢ boundary := by
  obtain ⟨U, hU, hUp⟩ := mapClusterPt_iff_ultrafilter.mp hp
  have h₁ := continuous_fst.continuousAt.tendsto.comp hUp
  have h₂ := continuous_snd.continuousAt.tendsto.comp hUp
  have hdU := hd.mono_left hU
  have heU := he.mono_left hU
  have hdn : Tendsto (fun t ↦ laurent (exp (b t)) (exp (a t))) U (𝓝 d) := by
    simpa only [laurent_comm (exp (b _))] using hdU
  have heSwap : Tendsto (fun t ↦ (b t, a t)) U (cocompact (ℂ × ℂ)) := by
    exact (Homeomorph.prodComm ℂ ℂ).isClosedEmbedding.tendsto_cocompact.comp heU
  constructor
  · cases h₁p : p.1 using OnePoint.rec with
    | infty => simp [boundary]
    | coe x =>
      by_cases hx : x = 0
      · simp [boundary, hx]
      · exact (no_interior_on_escape U hconic heU hx
          (finite_limit_of_onePoint (h₁p ▸ h₁)) h₂ hdU).elim
  · cases h₂p : p.2 using OnePoint.rec with
    | infty => simp [boundary]
    | coe y =>
      by_cases hy : y = 0
      · simp [boundary, hy]
      · exact (no_interior_on_escape U (fun t ↦ (add_comm _ _).trans (hconic t)) heSwap hy
          (finite_limit_of_onePoint (h₂p ▸ h₂)) h₁ hdn).elim

theorem exp_signed_zero {a : ℝ → ℂ} {p : OnePoint ℂ} (hp : p ∈ boundary)
    (h : Tendsto (fun t ↦ (exp (a t) : OnePoint ℂ)) atTop (𝓝 p)) :
    ∃ s : Bool, Tendsto (fun t ↦ exp (if s then -a t else a t)) atTop (𝓝 0) := by
  rcases hp with hp | hp
  · refine ⟨false, ?_⟩
    simpa using finite_limit_of_onePoint (hp ▸ h)
  · refine ⟨true, ?_⟩
    simpa only [Bool.true_eq, ↓reduceIte, exp_neg] using inv_limit_of_onePoint (hp ▸ h)

theorem no_finite_asymptotic_value {a b : ℝ → ℂ} (ha : Continuous a) (hb : Continuous b)
    {C d : ℂ} (hconic : ∀ t, a t ^ 2 + b t ^ 2 = C)
    (he : Tendsto (fun t ↦ (a t, b t)) atTop (cocompact (ℂ × ℂ)))
    (hd : Tendsto (fun t ↦ laurent (exp (a t)) (exp (b t))) atTop (𝓝 d)) : False := by
  let e : ℝ → OnePoint ℂ × OnePoint ℂ := fun t ↦ (↑(exp (a t)), ↑(exp (b t)))
  have hcont : Continuous e :=
    (OnePoint.continuous_coe.comp (Complex.continuous_exp.comp ha)).prodMk
      (OnePoint.continuous_coe.comp (Complex.continuous_exp.comp hb))
  have hcl (p) (hp : MapClusterPt p atTop e) : p ∈ boundary ×ˢ boundary :=
    pair_cluster_boundary hconic he hd hp
  obtain ⟨p, hp⟩ := Bottcher.tendsto_of_mapClusterPt_finite atTop_basis isCompact_univ
    (fun _ ↦ subset_univ _) (fun _ _ hij ↦ closure_mono (image_mono (Ici_subset_Ici.mpr hij)))
    (fun _ ↦ isPreconnected_Ici.image e hcont.continuousOn) (boundary_finite.prod boundary_finite) hcl
  have hbp := hcl p hp.mapClusterPt
  obtain ⟨s, hs⟩ := exp_signed_zero hbp.1 (continuous_fst.continuousAt.tendsto.comp hp)
  obtain ⟨t, ht⟩ := exp_signed_zero hbp.2 (continuous_snd.continuousAt.tendsto.comp hp)
  let a' : ℝ → ℂ := fun r ↦ if s then -a r else a r
  let b' : ℝ → ℂ := fun r ↦ if t then -b r else b r
  have ha' : Continuous a' := by cases s <;> simp only [a', Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hb' : Continuous b' := by cases t <;> simp only [b', Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hc' (r) : a' r ^ 2 + b' r ^ 2 = C := by
    cases s <;> cases t <;> simpa [a', b'] using hconic r
  have hd' : Tendsto (fun r ↦ laurent (exp (a' r)) (exp (b' r))) atTop (𝓝 d) := by
    cases s <;> cases t <;> simpa only [a', b', Bool.false_eq_true, ↓reduceIte, exp_neg,
      laurent_inv_left, laurent_inv_right] using hd
  exact no_conic_corner ha' hb' hc' hs ht hd'

end GaloisForLFunctions.HTGeometry.ConicLaurentNoEscape
