import GaloisForLFunctions.HTGeometry.TorusOrbitPolyannulusUniqueness

/-!
# The algebra of holomorphic functions on a polyannulus is a domain

A polyannulus is a product of annuli, hence connected.  On a connected open
set the holomorphic functions have no zero divisors: if a product vanishes and
one factor is nonzero somewhere, the other vanishes near that point, hence
everywhere by the identity theorem.

The restrictions to an open set of the functions holomorphic on a neighbourhood
of it therefore form an integral domain over `ℂ`.  This is the ambient algebra
in which the phase jets live, and in which their transcendence degree is
measured.
-/

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The polyannulus is connected -/

variable {d : Type} [Fintype d] [DecidableEq d]

omit [Fintype d] [DecidableEq d] in
theorem isPreconnected_polyannulus {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j) :
    IsPreconnected (polyannulus ρ) := by
  have hset : polyannulus ρ = Set.univ.pi (fun j => logAnnulus (ρ j)) := by
    ext z
    rw [Set.mem_univ_pi]
    rfl
  rw [hset]
  exact isPreconnected_univ_pi fun j => isPreconnected_logAnnulus (hρ j)

omit [Fintype d] [DecidableEq d] in
theorem nonempty_polyannulus {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j) :
    (polyannulus ρ).Nonempty :=
  ⟨fun _ => 1, unitTorus_subset_polyannulus hρ fun _ => by simp⟩

/-! ### No zero divisors among holomorphic functions -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **A vanishing product with a nonvanishing factor forces the other factor to
vanish.** -/
theorem eqOn_zero_of_mul_eqOn_zero {U : Set E} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {F G : E → ℂ} (hG : AnalyticOnNhd ℂ G U)
    (hF : AnalyticOnNhd ℂ F U) (h : ∀ z ∈ U, F z * G z = 0) {z₀ : E}
    (hz₀ : z₀ ∈ U) (hFz₀ : F z₀ ≠ 0) : ∀ z ∈ U, G z = 0 := by
  have hne : ∀ᶠ z in 𝓝 z₀, F z ≠ 0 := (hF z₀ hz₀).continuousAt.eventually_ne hFz₀
  have hev : G =ᶠ[𝓝 z₀] 0 := by
    filter_upwards [hne, hUo.mem_nhds hz₀] with z hz1 hz2
    exact (mul_eq_zero.1 (h z hz2)).resolve_left hz1
  intro z hz
  exact hG.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc hz₀ hev hz

/-- **The holomorphic functions on a connected open set have no zero
divisors.** -/
theorem eqOn_zero_or_eqOn_zero_of_mul_eqOn_zero {U : Set E} (hUo : IsOpen U)
    (hUc : IsPreconnected U) {F G : E → ℂ} (hF : AnalyticOnNhd ℂ F U)
    (hG : AnalyticOnNhd ℂ G U) (h : ∀ z ∈ U, F z * G z = 0) :
    (∀ z ∈ U, F z = 0) ∨ ∀ z ∈ U, G z = 0 := by
  by_cases hF0 : ∀ z ∈ U, F z = 0
  · exact Or.inl hF0
  · refine Or.inr ?_
    obtain ⟨z₀, hz₀, hne⟩ : ∃ z ∈ U, F z ≠ 0 := by
      by_contra hcon
      refine hF0 fun z hz => ?_
      by_contra hz'
      exact hcon ⟨z, hz, hz'⟩
    exact eqOn_zero_of_mul_eqOn_zero hUo hUc hG hF h hz₀ hne

/-! ### The algebra of holomorphic functions on an open set -/

/-- Restrictions to `U` of the functions holomorphic on a neighbourhood of
`U`. -/
def analyticSubalgebra (U : Set E) : Subalgebra ℂ (↥U → ℂ) where
  carrier := {f | ∃ F : E → ℂ, AnalyticOnNhd ℂ F U ∧ ∀ z : ↥U, f z = F z.1}
  mul_mem' := by
    rintro f g ⟨F, hF, hfF⟩ ⟨G, hG, hgG⟩
    refine ⟨fun z => F z * G z, hF.mul hG, fun z => ?_⟩
    rw [Pi.mul_apply, hfF z, hgG z]
  add_mem' := by
    rintro f g ⟨F, hF, hfF⟩ ⟨G, hG, hgG⟩
    refine ⟨fun z => F z + G z, hF.add hG, fun z => ?_⟩
    rw [Pi.add_apply, hfF z, hgG z]
  algebraMap_mem' := by
    intro c
    refine ⟨fun _ => c, analyticOnNhd_const, fun z => rfl⟩

theorem mem_analyticSubalgebra {U : Set E} {f : ↥U → ℂ} :
    f ∈ analyticSubalgebra U ↔
      ∃ F : E → ℂ, AnalyticOnNhd ℂ F U ∧ ∀ z : ↥U, f z = F z.1 := Iff.rfl

/-- The restriction of a holomorphic function, as an element of the algebra. -/
def analyticRestrict {U : Set E} (F : E → ℂ) (hF : AnalyticOnNhd ℂ F U) :
    ↥(analyticSubalgebra U) :=
  ⟨fun z => F z.1, F, hF, fun _ => rfl⟩

@[simp] theorem analyticRestrict_apply {U : Set E} (F : E → ℂ)
    (hF : AnalyticOnNhd ℂ F U) (z : ↥U) :
    (analyticRestrict F hF : ↥U → ℂ) z = F z.1 := rfl

/-- **The algebra of holomorphic functions on a connected open set is an
integral domain.** -/
theorem isDomain_analyticSubalgebra {U : Set E} (hUo : IsOpen U)
    (hUc : IsPreconnected U) (hUne : U.Nonempty) :
    IsDomain ↥(analyticSubalgebra U) := by
  obtain ⟨w, hw⟩ := hUne
  haveI hnt : Nontrivial ↥(analyticSubalgebra U) := by
    refine ⟨0, 1, ?_⟩
    intro hcon
    have := congrFun (congrArg (fun x : ↥(analyticSubalgebra U) => (x : ↥U → ℂ)) hcon)
      ⟨w, hw⟩
    simp at this
  haveI hnzd : NoZeroDivisors ↥(analyticSubalgebra U) := by
    refine ⟨?_⟩
    rintro ⟨f, F, hF, hfF⟩ ⟨g, G, hG, hgG⟩ hmul
    have hzero : ∀ z ∈ U, F z * G z = 0 := by
      intro z hz
      have := congrFun (congrArg
        (fun x : ↥(analyticSubalgebra U) => (x : ↥U → ℂ)) hmul) ⟨z, hz⟩
      rw [← hfF ⟨z, hz⟩, ← hgG ⟨z, hz⟩]
      simpa using this
    rcases eqOn_zero_or_eqOn_zero_of_mul_eqOn_zero hUo hUc hF hG hzero with h | h
    · left
      refine Subtype.ext (funext fun z => ?_)
      show f z = 0
      rw [hfF z]
      exact h z.1 z.2
    · right
      refine Subtype.ext (funext fun z => ?_)
      show g z = 0
      rw [hgG z]
      exact h z.1 z.2
  exact NoZeroDivisors.to_isDomain _

omit [DecidableEq d] in
/-- The polyannulus instance of the previous theorem. -/
theorem isDomain_analyticSubalgebra_polyannulus {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j) :
    IsDomain ↥(analyticSubalgebra (polyannulus ρ)) :=
  isDomain_analyticSubalgebra (isOpen_polyannulus ρ) (isPreconnected_polyannulus hρ)
    (nonempty_polyannulus hρ)

end

end GaloisForLFunctions.HTGeometry
