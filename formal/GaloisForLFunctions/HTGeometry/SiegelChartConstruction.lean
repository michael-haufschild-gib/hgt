import GaloisForLFunctions.HTGeometry.GermReducedPresentation
import GaloisForLFunctions.HTGeometry.PolydiscWeierstrass
import GaloisForLFunctions.HTGeometry.SiegelUniformTransition

/-!
# Local reduced charts of a globally presented meromorphic function

A meromorphic function given globally as a quotient `A / B` of two holomorphic functions has, near
every point, a *reduced* presentation: numerator and denominator with relatively prime germs.  The
reduced presentation is valid on a whole ball, not just at the centre, because coprimality is an
open condition; and its denominator is nowhere locally trivial, because a nonzero holomorphic
function does not vanish identically near any point of a connected domain.

Cancelling a nonzero holomorphic factor is the tool used throughout: on a connected open set, if a
product vanishes identically and one factor is somewhere nonzero, the other factor vanishes
identically.  This is what turns the cross identities of two presentations into the identity of
their fractions.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Metric

variable {n : ℕ}

/-- **Cancelling a nonzero holomorphic factor on a connected domain.** -/
theorem eqOn_zero_of_mul_eq_zero {U : Set (Fin n → ℂ)} (hUopen : IsOpen U)
    (hUconn : IsPreconnected U) {F G : (Fin n → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F U) (hG : AnalyticOnNhd ℂ G U)
    (hG0 : ∃ z₀ ∈ U, G z₀ ≠ 0) (h : ∀ z ∈ U, F z * G z = 0) : ∀ z ∈ U, F z = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨w, hwU, hFw⟩ := hcon
  have hFne : ∀ᶠ z in 𝓝 w, F z ≠ 0 := (hF w hwU).continuousAt.eventually_ne hFw
  have hGzero : G =ᶠ[𝓝 w] 0 := by
    filter_upwards [hFne, hUopen.mem_nhds hwU] with z hz1 hz2
    exact (mul_eq_zero.mp (h z hz2)).resolve_left hz1
  have hEq := hG.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconn hwU hGzero
  obtain ⟨z₀, hz₀U, hz₀⟩ := hG0
  exact hz₀ (hEq hz₀U)

/-- **A reduced chart of a globally presented meromorphic function.**  On a small ball the
presentation is holomorphic, relatively prime at *every* point, has a nowhere locally trivial
denominator, and presents the same fraction as the global one. -/
theorem exists_reduced_chart {A B : (Fin (n + 1) → ℂ) → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (hB0 : ∃ z, B z ≠ 0) (c : Fin (n + 1) → ℂ) :
    ∃ (δ : ℝ) (A' B' : (Fin (n + 1) → ℂ) → ℂ), 0 < δ ∧
      (∀ z ∈ ball c δ, AnalyticAt ℂ A' z) ∧ (∀ z ∈ ball c δ, AnalyticAt ℂ B' z) ∧
      (∀ z ∈ ball c δ, ∀ (h1 : AnalyticAt ℂ A' z) (h2 : AnalyticAt ℂ B' z),
        IsRelPrime (analyticGermOf h1) (analyticGermOf h2)) ∧
      (∀ z ∈ ball c δ, ¬ B' =ᶠ[𝓝 z] 0) ∧
      (∀ z ∈ ball c δ, A z * B' z = A' z * B z) := by
  classical
  have hAuniv : AnalyticOnNhd ℂ A Set.univ := fun z _ =>
    analyticAt_of_differentiableOn isOpen_univ hA.differentiableOn (Set.mem_univ z)
  have hBuniv : AnalyticOnNhd ℂ B Set.univ := fun z _ =>
    analyticAt_of_differentiableOn isOpen_univ hB.differentiableOn (Set.mem_univ z)
  have hAan : AnalyticAt ℂ A c := hAuniv c (Set.mem_univ c)
  have hBan : AnalyticAt ℂ B c := hBuniv c (Set.mem_univ c)
  have hBglobal : ¬ B =ᶠ[𝓝 c] 0 := by
    intro hcon
    obtain ⟨z, hz⟩ := hB0
    exact hz (hBuniv.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ c) hcon (Set.mem_univ z))
  obtain ⟨A', B', hA'an, hB'an, hB'0, hrel, hcross⟩ :=
    exists_reduced_presentation_at hAan hBan hBglobal
  -- radii for analyticity, for the cross identity and for the propagation of coprimality
  obtain ⟨r₁, hr₁, hA'ball⟩ := exists_ball_analyticOnNhd hA'an
  obtain ⟨r₂, hr₂, hB'ball⟩ := exists_ball_analyticOnNhd hB'an
  obtain ⟨r₃, hr₃, hcrossball⟩ := Metric.eventually_nhds_iff.mp hcross
  obtain ⟨r₄, hr₄, hrelball⟩ :=
    Metric.eventually_nhds_iff.mp (eventually_isRelPrime_germ hA'an hB'an hrel)
  set δ : ℝ := min (min r₁ r₂) (min r₃ r₄) with hδ
  have hδpos : 0 < δ := lt_min (lt_min hr₁ hr₂) (lt_min hr₃ hr₄)
  have hsub₁ : ball c δ ⊆ ball c r₁ :=
    ball_subset_ball (le_trans (min_le_left _ _) (min_le_left _ _))
  have hsub₂ : ball c δ ⊆ ball c r₂ :=
    ball_subset_ball (le_trans (min_le_left _ _) (min_le_right _ _))
  refine ⟨δ, A', B', hδpos, fun z hz => hA'ball z (hsub₁ hz), fun z hz => hB'ball z (hsub₂ hz),
    ?_, ?_, ?_⟩
  · intro z hz h1 h2
    exact hrelball (lt_of_lt_of_le (mem_ball.mp hz)
      (le_trans (min_le_right _ _) (min_le_right _ _))) h1 h2
  · intro z hz hcon
    have hEq := (hB'ball.mono hsub₂).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      ((convex_ball c δ).isPreconnected) hz hcon
    refine hB'0 ?_
    filter_upwards [Metric.ball_mem_nhds c hδpos] with w hw
    exact hEq hw
  · intro z hz
    exact hcrossball (lt_of_lt_of_le (mem_ball.mp hz)
      (le_trans (min_le_right _ _) (min_le_left _ _)))

/-! ## Chart packages -/

variable {N : ℕ}

/-- The package of properties a reduced local chart of a family of fractions must have on a set. -/
def ChartPackage (A B A' B' : Fin (N + 1) → (Fin (n + 1) → ℂ) → ℂ)
    (U : Set (Fin (n + 1) → ℂ)) : Prop :=
  (∀ k, ∀ z ∈ U, AnalyticAt ℂ (A' k) z) ∧ (∀ k, ∀ z ∈ U, AnalyticAt ℂ (B' k) z) ∧
    (∀ k, ∀ z ∈ U, ∀ (h1 : AnalyticAt ℂ (A' k) z) (h2 : AnalyticAt ℂ (B' k) z),
      IsRelPrime (analyticGermOf h1) (analyticGermOf h2)) ∧
    (∀ k, ∀ z ∈ U, ¬ (B' k) =ᶠ[𝓝 z] 0) ∧
    (∀ k, ∀ z ∈ U, A k z * B' k z = A' k z * B k z)

theorem ChartPackage.mono {A B A' B' : Fin (N + 1) → (Fin (n + 1) → ℂ) → ℂ}
    {U V : Set (Fin (n + 1) → ℂ)} (h : ChartPackage A B A' B' U) (hVU : V ⊆ U) :
    ChartPackage A B A' B' V :=
  ⟨fun k z hz => h.1 k z (hVU hz), fun k z hz => h.2.1 k z (hVU hz),
    fun k z hz => h.2.2.1 k z (hVU hz), fun k z hz => h.2.2.2.1 k z (hVU hz),
    fun k z hz => h.2.2.2.2 k z (hVU hz)⟩

/-- **A reduced chart of a whole family, on one ball.** -/
theorem exists_chartPackage_at {A B : Fin (N + 1) → (Fin (n + 1) → ℂ) → ℂ}
    (hA : ∀ k, Differentiable ℂ (A k)) (hB : ∀ k, Differentiable ℂ (B k))
    (hB0 : ∀ k, ∃ z, B k z ≠ 0) (c : Fin (n + 1) → ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ A' B' : Fin (N + 1) → (Fin (n + 1) → ℂ) → ℂ,
      ChartPackage A B A' B' (ball c δ) := by
  classical
  choose δ A' B' hδ hA'an hB'an hrel hB'ne hcross using
    fun k => exists_reduced_chart (hA k) (hB k) (hB0 k) c
  refine ⟨Finset.univ.inf' Finset.univ_nonempty δ, ?_, A', B', ?_, ?_, ?_, ?_, ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr fun k _ => hδ k
  all_goals
    intro k z hz
    have hzk : z ∈ ball c (δ k) :=
      ball_subset_ball (Finset.inf'_le δ (Finset.mem_univ k)) hz
  · exact hA'an k z hzk
  · exact hB'an k z hzk
  · exact hrel k z hzk
  · exact hB'ne k z hzk
  · exact hcross k z hzk

/-- **One radius serves every centre of a compact set.** -/
theorem exists_uniform_chartPackage {A B : Fin (N + 1) → (Fin (n + 1) → ℂ) → ℂ}
    (hA : ∀ k, Differentiable ℂ (A k)) (hB : ∀ k, Differentiable ℂ (B k))
    (hB0 : ∀ k, ∃ z, B k z ≠ 0) {K : Set (Fin (n + 1) → ℂ)} (hK : IsCompact K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c ∈ K, ∃ A' B' : Fin (N + 1) → (Fin (n + 1) → ℂ) → ℂ,
      ChartPackage A B A' B' (ball c ρ) := by
  classical
  choose δ hδ A' B' hpack using fun c : Fin (n + 1) → ℂ => exists_chartPackage_at hA hB hB0 c
  have hcover : K ⊆ ⋃ c ∈ K, ball c (δ c / 2) :=
    fun z hz => Set.mem_biUnion hz (mem_ball_self (by linarith [hδ z]))
  obtain ⟨b, hbsub, hbfin, hbcov⟩ :=
    hK.elim_finite_subcover_image (b := K) (c := fun c => ball c (δ c / 2))
      (fun c _ => isOpen_ball) hcover
  set s : Finset (Fin (n + 1) → ℂ) := hbfin.toFinset with hs
  rcases Finset.eq_empty_or_nonempty s with hse | hsne
  · refine ⟨1, one_pos, ?_⟩
    intro c hc
    exfalso
    obtain ⟨x, hx, -⟩ : ∃ x ∈ b, c ∈ ball x (δ x / 2) := by
      have := hbcov hc
      simpa using this
    have : x ∈ s := by rwa [hs, Set.Finite.mem_toFinset]
    rw [hse] at this
    exact absurd this (Finset.notMem_empty x)
  refine ⟨s.inf' hsne (fun c => δ c / 2), ?_, ?_⟩
  · exact (Finset.lt_inf'_iff _).mpr fun c _ => by linarith [hδ c]
  · intro c hc
    obtain ⟨x, hx, hcx⟩ : ∃ x ∈ b, c ∈ ball x (δ x / 2) := by
      have := hbcov hc
      simpa using this
    have hxs : x ∈ s := by rwa [hs, Set.Finite.mem_toFinset]
    refine ⟨A' x, B' x, (hpack x).mono ?_⟩
    intro z hz
    refine mem_ball.mpr ?_
    calc dist z x ≤ dist z c + dist c x := dist_triangle z c x
      _ < s.inf' hsne (fun c => δ c / 2) + δ x / 2 := by
          exact add_lt_add (mem_ball.mp hz) (mem_ball.mp hcx)
      _ ≤ δ x / 2 + δ x / 2 := by
          have := Finset.inf'_le (fun c => δ c / 2) hxs
          linarith
      _ = δ x := by ring

/-! ## Translating a chart by a period, and comparing two charts -/

theorem exists_ne_zero_on_open {F : (Fin n → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F Set.univ)
    (hF0 : ∃ z, F z ≠ 0) {U : Set (Fin n → ℂ)} (hUopen : IsOpen U) (hUne : U.Nonempty) :
    ∃ z ∈ U, F z ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨z₁, hz₁⟩ := hUne
  obtain ⟨z, hz⟩ := hF0
  refine hz ?_
  refine hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
    (Set.mem_univ z₁) ?_ (Set.mem_univ z)
  filter_upwards [hUopen.mem_nhds hz₁] with w hw
  exact hcon w hw

theorem mem_ball_sub_iff {c z p : Fin n → ℂ} {ρ : ℝ} :
    z - p ∈ ball (c - p) ρ ↔ z ∈ ball c ρ := by
  simp only [mem_ball, dist_eq_norm]
  constructor
  · intro h; simpa [sub_sub_sub_cancel_right] using h
  · intro h; simpa [sub_sub_sub_cancel_right] using h

/-- **Translating a chart by a period.** -/
theorem chartPackage_translate {A B A' B' : Fin (N + 1) → (Fin (n + 1) → ℂ) → ℂ}
    (hA : ∀ k, Differentiable ℂ (A k)) (hB : ∀ k, Differentiable ℂ (B k))
    (hB0 : ∀ k, ∃ z, B k z ≠ 0) {P : AddSubgroup (Fin (n + 1) → ℂ)}
    (hper : ∀ k, ∀ p ∈ P, ∀ z, A k (z + p) * B k z = A k z * B k (z + p))
    {p : Fin (n + 1) → ℂ} (hp : p ∈ P) {c : Fin (n + 1) → ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : ChartPackage A B A' B' (ball (c - p) ρ)) :
    ChartPackage A B (fun k z => A' k (z - p)) (fun k z => B' k (z - p)) (ball c ρ) := by
  have hAuniv : ∀ k, AnalyticOnNhd ℂ (A k) Set.univ := fun k z _ =>
    analyticAt_of_differentiableOn isOpen_univ (hA k).differentiableOn (Set.mem_univ z)
  have hBuniv : ∀ k, AnalyticOnNhd ℂ (B k) Set.univ := fun k z _ =>
    analyticAt_of_differentiableOn isOpen_univ (hB k).differentiableOn (Set.mem_univ z)
  have hmem : ∀ z ∈ ball c ρ, z - p ∈ ball (c - p) ρ := fun z hz => mem_ball_sub_iff.mpr hz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k z hz
    exact AnalyticAt.comp (g := A' k) (f := fun v : Fin (n + 1) → ℂ => v - p)
      (h.1 k (z - p) (hmem z hz)) (analyticAt_sub_const p z)
  · intro k z hz
    exact AnalyticAt.comp (g := B' k) (f := fun v : Fin (n + 1) → ℂ => v - p)
      (h.2.1 k (z - p) (hmem z hz)) (analyticAt_sub_const p z)
  · intro k z hz h1 h2
    exact isRelPrime_germ_translate (h.1 k (z - p) (hmem z hz)) (h.2.1 k (z - p) (hmem z hz))
      h1 h2 (h.2.2.1 k (z - p) (hmem z hz) _ _)
  · intro k z hz hcon
    refine h.2.2.2.1 k (z - p) (hmem z hz) ?_
    have htend : Filter.Tendsto (fun v : Fin (n + 1) → ℂ => v + p) (𝓝 (z - p)) (𝓝 z) := by
      have h1 : Filter.Tendsto (fun v : Fin (n + 1) → ℂ => v + p) (𝓝 (z - p)) (𝓝 (z - p + p)) :=
        (analyticAt_add_const p (z - p)).continuousAt
      rwa [sub_add_cancel] at h1
    filter_upwards [htend.eventually hcon] with v hv
    have hv' : B' k (v + p - p) = 0 := hv
    rwa [add_sub_cancel_right] at hv'
  · -- the cross identity, after cancelling `B k (· - p)`
    intro k z hz
    have hU : IsOpen (ball c ρ) := isOpen_ball
    have hUconn : IsPreconnected (ball c ρ) := (convex_ball c ρ).isPreconnected
    set X : (Fin (n + 1) → ℂ) → ℂ :=
      fun w => A k w * B' k (w - p) - A' k (w - p) * B k w with hX
    have hXan : AnalyticOnNhd ℂ X (ball c ρ) := by
      intro w hw
      refine AnalyticAt.sub ?_ ?_
      · exact (hAuniv k w (Set.mem_univ w)).mul
          (AnalyticAt.comp (g := B' k) (f := fun v : Fin (n + 1) → ℂ => v - p)
            (h.2.1 k (w - p) (hmem w hw)) (analyticAt_sub_const p w))
      · exact (AnalyticAt.comp (g := A' k) (f := fun v : Fin (n + 1) → ℂ => v - p)
          (h.1 k (w - p) (hmem w hw)) (analyticAt_sub_const p w)).mul
          (hBuniv k w (Set.mem_univ w))
    have hGan : AnalyticOnNhd ℂ (fun w => B k (w - p)) (ball c ρ) := by
      intro w _
      exact AnalyticAt.comp (g := B k) (f := fun v : Fin (n + 1) → ℂ => v - p)
        (hBuniv k (w - p) (Set.mem_univ _)) (analyticAt_sub_const p w)
    have hG0 : ∃ z₀ ∈ ball c ρ, B k (z₀ - p) ≠ 0 := by
      obtain ⟨w, hw, hwne⟩ := exists_ne_zero_on_open (hBuniv k) (hB0 k) (U := ball (c - p) ρ)
        isOpen_ball ⟨c - p, mem_ball_self hρ⟩
      exact ⟨w + p, by rwa [← mem_ball_sub_iff, add_sub_cancel_right], by
        rwa [add_sub_cancel_right]⟩
    have hmul : ∀ w ∈ ball c ρ, X w * B k (w - p) = 0 := by
      intro w hw
      have h1 := h.2.2.2.2 k (w - p) (hmem w hw)
      have h2 := hper k p hp (w - p)
      rw [sub_add_cancel] at h2
      rw [hX]
      simp only
      linear_combination (B' k (w - p)) * h2 + (B k w) * h1
    have := eqOn_zero_of_mul_eq_zero hU hUconn hXan hGan hG0 hmul z hz
    rw [hX] at this
    simp only at this
    linear_combination this

/-- **A reduced chart at every point, with one radius.** -/
theorem exists_uniform_chartPackage_everywhere {A B : Fin (N + 1) → (Fin (n + 1) → ℂ) → ℂ}
    (hA : ∀ k, Differentiable ℂ (A k)) (hB : ∀ k, Differentiable ℂ (B k))
    (hB0 : ∀ k, ∃ z, B k z ≠ 0) {P : AddSubgroup (Fin (n + 1) → ℂ)}
    (hper : ∀ k, ∀ p ∈ P, ∀ z, A k (z + p) * B k z = A k z * B k (z + p))
    {K : Set (Fin (n + 1) → ℂ)} (hK : IsCompact K) (hfund : ∀ z, ∃ p ∈ P, z - p ∈ K) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ c : Fin (n + 1) → ℂ, ∃ A' B' : Fin (N + 1) → (Fin (n + 1) → ℂ) → ℂ,
      ChartPackage A B A' B' (ball c ρ) := by
  obtain ⟨ρ, hρ, hspec⟩ := exists_uniform_chartPackage hA hB hB0 hK
  refine ⟨ρ, hρ, ?_⟩
  intro c
  obtain ⟨p, hp, hcp⟩ := hfund c
  obtain ⟨A', B', hpack⟩ := hspec _ hcp
  exact ⟨fun k z => A' k (z - p), fun k z => B' k (z - p),
    chartPackage_translate hA hB hB0 hper hp hρ hpack⟩

/-- **Two charts of the same family present the same fraction across a period.** -/
theorem chartPackage_cross {A B A₁ B₁ A₂ B₂ : Fin (N + 1) → (Fin (n + 1) → ℂ) → ℂ}
    (hA : ∀ k, Differentiable ℂ (A k)) (hB : ∀ k, Differentiable ℂ (B k))
    (hB0 : ∀ k, ∃ z, B k z ≠ 0) {P : AddSubgroup (Fin (n + 1) → ℂ)}
    (hper : ∀ k, ∀ p ∈ P, ∀ z, A k (z + p) * B k z = A k z * B k (z + p))
    {c₁ c₂ : Fin (n + 1) → ℂ} {ρ : ℝ}
    (h₁ : ChartPackage A B A₁ B₁ (ball c₁ ρ)) (h₂ : ChartPackage A B A₂ B₂ (ball c₂ ρ))
    {p : Fin (n + 1) → ℂ} (hp : p ∈ P) (k : Fin (N + 1)) {z : Fin (n + 1) → ℂ}
    (hz₁ : z ∈ ball c₁ ρ) (hz₂ : z - p ∈ ball c₂ ρ) :
    A₁ k z * B₂ k (z - p) = A₂ k (z - p) * B₁ k z := by
  have hAuniv : ∀ k, AnalyticOnNhd ℂ (A k) Set.univ := fun k z _ =>
    analyticAt_of_differentiableOn isOpen_univ (hA k).differentiableOn (Set.mem_univ z)
  have hBuniv : ∀ k, AnalyticOnNhd ℂ (B k) Set.univ := fun k z _ =>
    analyticAt_of_differentiableOn isOpen_univ (hB k).differentiableOn (Set.mem_univ z)
  have hshift : ∀ w : Fin (n + 1) → ℂ, w - p ∈ ball c₂ ρ ↔ w ∈ ball (c₂ + p) ρ := by
    intro w
    have : c₂ + p - p = c₂ := by abel
    rw [← mem_ball_sub_iff (c := c₂ + p) (z := w) (p := p) (ρ := ρ), this]
  set U : Set (Fin (n + 1) → ℂ) := ball c₁ ρ ∩ ball (c₂ + p) ρ with hU
  have hUopen : IsOpen U := isOpen_ball.inter isOpen_ball
  have hUconn : IsPreconnected U :=
    ((convex_ball c₁ ρ).inter (convex_ball (c₂ + p) ρ)).isPreconnected
  have hzU : z ∈ U := ⟨hz₁, (hshift z).mp hz₂⟩
  have hmem₁ : ∀ w ∈ U, w ∈ ball c₁ ρ := fun w hw => hw.1
  have hmem₂ : ∀ w ∈ U, w - p ∈ ball c₂ ρ := fun w hw => (hshift w).mpr hw.2
  set X : (Fin (n + 1) → ℂ) → ℂ :=
    fun w => A₁ k w * B₂ k (w - p) - A₂ k (w - p) * B₁ k w with hX
  have hXan : AnalyticOnNhd ℂ X U := by
    intro w hw
    refine AnalyticAt.sub ((h₁.1 k w (hmem₁ w hw)).mul ?_)
      (AnalyticAt.mul ?_ (h₁.2.1 k w (hmem₁ w hw)))
    · exact AnalyticAt.comp (g := B₂ k) (f := fun v : Fin (n + 1) → ℂ => v - p)
        (h₂.2.1 k (w - p) (hmem₂ w hw)) (analyticAt_sub_const p w)
    · exact AnalyticAt.comp (g := A₂ k) (f := fun v : Fin (n + 1) → ℂ => v - p)
        (h₂.1 k (w - p) (hmem₂ w hw)) (analyticAt_sub_const p w)
  have hBan : AnalyticOnNhd ℂ (B k) U := fun w _ => hBuniv k w (Set.mem_univ w)
  have hBpan : AnalyticOnNhd ℂ (fun w => B k (w - p)) U := by
    intro w _
    exact AnalyticAt.comp (g := B k) (f := fun v : Fin (n + 1) → ℂ => v - p)
      (hBuniv k (w - p) (Set.mem_univ _)) (analyticAt_sub_const p w)
  have hBne : ∃ w ∈ U, B k w ≠ 0 :=
    exists_ne_zero_on_open (hBuniv k) (hB0 k) hUopen ⟨z, hzU⟩
  have hBpne : ∃ w ∈ U, B k (w - p) ≠ 0 := by
    obtain ⟨w₀, hw₀⟩ := hB0 k
    exact exists_ne_zero_on_open (F := fun w => B k (w - p))
      (fun w _ => AnalyticAt.comp (g := B k) (f := fun v : Fin (n + 1) → ℂ => v - p)
        (hBuniv k (w - p) (Set.mem_univ _)) (analyticAt_sub_const p w))
      ⟨w₀ + p, by rwa [add_sub_cancel_right]⟩ hUopen ⟨z, hzU⟩
  have hmul : ∀ w ∈ U, (X w * B k (w - p)) * B k w = 0 := by
    intro w hw
    have e₁ := h₁.2.2.2.2 k w (hmem₁ w hw)
    have e₂ := h₂.2.2.2.2 k (w - p) (hmem₂ w hw)
    have e₃ := hper k p hp (w - p)
    rw [sub_add_cancel] at e₃
    rw [hX]
    simp only
    linear_combination (-(B₂ k (w - p)) * (B k (w - p))) * e₁ + (B₁ k w * B k w) * e₂
      + (B₁ k w * B₂ k (w - p)) * e₃
  have hstep₁ : ∀ w ∈ U, X w * B k (w - p) = 0 :=
    eqOn_zero_of_mul_eq_zero hUopen hUconn (fun w hw => (hXan w hw).mul (hBpan w hw)) hBan
      hBne hmul
  have hstep₂ : ∀ w ∈ U, X w = 0 :=
    eqOn_zero_of_mul_eq_zero hUopen hUconn hXan hBpan hBpne hstep₁
  have := hstep₂ z hzU
  rw [hX] at this
  simp only at this
  linear_combination this

end GaloisForLFunctions.HTGeometry
