import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation
import GaloisForLFunctions.HTGeometry.EllipticPrincipalJet

/-!
# The mixed constraint as an identity of meromorphic germs

A meromorphic function is an element of `Mer(ℂ)`, not a total function: its values at its own poles
are an artefact of the representative.  Constraints such as `Δ₁F = 0` and `Δ_τΔ_σF ∈ ℂ` are
identities in `Mer(ℂ)`, so they say that the difference vanishes on a punctured neighbourhood of
every point, not at every point — no representative of a function with poles can satisfy them
pointwise, because at a pole one side has a finite artefact value where the identity demands the
cancellation of an infinity.

Laurent coefficients depend only on the punctured germ, so every coefficient-level consequence of
the constraints survives this weakening; and at a point where all four translates are analytic the
identity does hold pointwise, by continuity.

* `PeriodicOneGerm`, `MixedConstGerm`;
* `tendsto_nhdsNE_add_const`, the translation transport of a germ identity;
* `eventuallyEq_boundary_shift_one`, `..._tau`, `..._sigma`;
* `periodicOne_eq_of_analyticAt`, `mixedConst_eq_of_analyticAt`;
* `mixedConstGerm_deriv`, `mixedConstGerm_iteratedDeriv_succ`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Translation carries punctured neighbourhoods to punctured neighbourhoods. -/
theorem tendsto_nhdsNE_add_const (z h : ℂ) :
    Tendsto (fun w : ℂ ↦ w + h) (𝓝[≠] z) (𝓝[≠] (z + h)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hc : Tendsto (fun w : ℂ ↦ w + h) (𝓝 z) (𝓝 (z + h)) :=
      (continuous_id.add continuous_const).continuousAt
    exact hc.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with w hw
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hw ⊢
    intro hc
    exact hw (by linear_combination hc)

/-- `Δ₁F = 0` as an identity of meromorphic germs. -/
def PeriodicOneGerm (F : ℂ → ℂ) : Prop := ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, F (w + 1) = F w

/-- `Δ_τΔ_σF = Cst` as an identity of meromorphic germs. -/
def MixedConstGerm (F : ℂ → ℂ) (τ σ Cst : ℂ) : Prop :=
  ∀ z : ℂ, ∀ᶠ w in 𝓝[≠] z, F (w + τ + σ) - F (w + τ) - F (w + σ) + F w = Cst

theorem periodicOneGerm_of_forall {F : ℂ → ℂ} (h : ∀ z : ℂ, F (z + 1) = F z) :
    PeriodicOneGerm F := fun _ ↦ Filter.Eventually.of_forall fun w ↦ h w

theorem mixedConstGerm_of_forall {F : ℂ → ℂ} {τ σ Cst : ℂ}
    (h : ∀ z : ℂ, F (z + τ + σ) - F (z + τ) - F (z + σ) + F z = Cst) :
    MixedConstGerm F τ σ Cst := fun _ ↦ Filter.Eventually.of_forall fun w ↦ h w

/-- A germ identity holds on the punctured neighbourhood of every translate. -/
theorem PeriodicOneGerm.shift {F : ℂ → ℂ} (h : PeriodicOneGerm F) (c z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, F (w + c + 1) = F (w + c) :=
  (tendsto_nhdsNE_add_const z c).eventually (h (z + c))

/-- The boundary function of a germ-periodic source is germ-periodic. -/
theorem eventuallyEq_boundary_shift_one {F : ℂ → ℂ} (hper : PeriodicOneGerm F) (σ z : ℂ) :
    (fun w ↦ F (w + 1 + σ) - F (w + 1)) =ᶠ[𝓝[≠] z] fun w ↦ F (w + σ) - F w := by
  filter_upwards [hper.shift σ z, hper z] with w h1 h2
  rw [show w + 1 + σ = w + σ + 1 by ring, h1, h2]

/-- A `τ`-step changes the `σ`-boundary function by the mixed constant. -/
theorem eventuallyEq_boundary_shift_tau {F : ℂ → ℂ} {τ σ Cst : ℂ}
    (hmixed : MixedConstGerm F τ σ Cst) (z : ℂ) :
    (fun w ↦ F (w + τ + σ) - F (w + τ)) =ᶠ[𝓝[≠] z] fun w ↦ (F (w + σ) - F w) + Cst := by
  filter_upwards [hmixed z] with w h
  linear_combination h

/-- A `σ`-step changes the `τ`-boundary function by the same constant. -/
theorem eventuallyEq_boundary_shift_sigma {F : ℂ → ℂ} {τ σ Cst : ℂ}
    (hmixed : MixedConstGerm F τ σ Cst) (z : ℂ) :
    (fun w ↦ F (w + σ + τ) - F (w + σ)) =ᶠ[𝓝[≠] z] fun w ↦ (F (w + τ) - F w) + Cst := by
  filter_upwards [hmixed z] with w h
  have hcomm : ∀ y : ℂ, F (y + σ + τ) = F (y + τ + σ) := by
    intro y
    rw [show y + σ + τ = y + τ + σ by ring]
  rw [hcomm w]
  linear_combination h

/-- Translating a function preserves analyticity of the composite at the shifted point. -/
theorem analyticAt_comp_add_const {F : ℂ → ℂ} {z c : ℂ} (h : AnalyticAt ℂ F (z + c)) :
    AnalyticAt ℂ (fun w ↦ F (w + c)) z := by
  have hadd : AnalyticAt ℂ (fun w : ℂ ↦ w + c) z := by fun_prop
  exact AnalyticAt.comp (g := F) (f := fun w : ℂ ↦ w + c) (by simpa using h) hadd

/-- Where both translates are analytic, germ periodicity holds pointwise. -/
theorem periodicOne_eq_of_analyticAt {F : ℂ → ℂ} (hper : PeriodicOneGerm F) {z : ℂ}
    (h0 : AnalyticAt ℂ F z) (h1 : AnalyticAt ℂ F (z + 1)) : F (z + 1) = F z := by
  have hc1 : ContinuousAt (fun w ↦ F (w + 1)) z := (analyticAt_comp_add_const h1).continuousAt
  have hc0 : ContinuousAt F z := h0.continuousAt
  exact (eventuallyEq_nhds_of_nhdsNE_of_continuousAt (hper z) hc1 hc0).eq_of_nhds

/-- Where all four translates are analytic, the germ mixed constraint holds pointwise. -/
theorem mixedConst_eq_of_analyticAt {F : ℂ → ℂ} {τ σ Cst : ℂ}
    (hmixed : MixedConstGerm F τ σ Cst) {z : ℂ} (h0 : AnalyticAt ℂ F z)
    (h1 : AnalyticAt ℂ F (z + τ)) (h2 : AnalyticAt ℂ F (z + σ))
    (h3 : AnalyticAt ℂ F (z + τ + σ)) :
    F (z + τ + σ) - F (z + τ) - F (z + σ) + F z = Cst := by
  have hc : ContinuousAt (fun w ↦ F (w + τ + σ) - F (w + τ) - F (w + σ) + F w) z := by
    have e3 : ContinuousAt (fun w ↦ F (w + τ + σ)) z := by
      have h3' : AnalyticAt ℂ F (z + (τ + σ)) := by
        rw [show z + (τ + σ) = z + τ + σ by ring]
        exact h3
      have := (analyticAt_comp_add_const h3').continuousAt
      simpa [add_assoc] using this
    have e1 : ContinuousAt (fun w ↦ F (w + τ)) z := (analyticAt_comp_add_const h1).continuousAt
    have e2 : ContinuousAt (fun w ↦ F (w + σ)) z := (analyticAt_comp_add_const h2).continuousAt
    exact ((e3.sub e1).sub e2).add h0.continuousAt
  exact (eventuallyEq_nhds_of_nhdsNE_of_continuousAt (hmixed z) hc continuousAt_const).eq_of_nhds

/-! ### Differentiating a germ constraint -/

/-- A punctured-neighbourhood property holds on an open punctured set. -/
theorem exists_isOpen_of_eventually_nhdsNE {z₀ : ℂ} {P : ℂ → Prop}
    (h : ∀ᶠ w in 𝓝[≠] z₀, P w) :
    ∃ W : Set ℂ, IsOpen W ∧ W ∈ 𝓝[≠] z₀ ∧ ∀ w ∈ W, P w := by
  rw [eventually_nhdsWithin_iff, eventually_nhds_iff] at h
  obtain ⟨U, hU, hUopen, hz₀⟩ := h
  refine ⟨U ∩ {z₀}ᶜ, hUopen.inter isOpen_compl_singleton, ?_, fun w hw ↦ hU w hw.1 hw.2⟩
  exact Filter.inter_mem (nhdsWithin_le_nhds (hUopen.mem_nhds hz₀)) self_mem_nhdsWithin

/-- Every translate of a meromorphic function is analytic on a punctured neighbourhood of every
point. -/
theorem eventually_nhdsNE_analyticAt_comp_add {f : ℂ → ℂ}
    (hf : MeromorphicOn f (Set.univ : Set ℂ)) (c z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ f (w + c) := by
  have hbase : ∀ y : ℂ, ∀ᶠ w in 𝓝[≠] y, AnalyticAt ℂ f w := by
    intro y
    have hdisj := mem_codiscreteWithin.mp hf.analyticAt_mem_codiscreteWithin y (Set.mem_univ y)
    filter_upwards [Filter.disjoint_principal_right.mp hdisj] with w hw
    simpa using hw
  exact (tendsto_nhdsNE_add_const z c).eventually (hbase (z + c))

theorem meromorphicOn_iteratedDeriv {f : ℂ → ℂ} (hf : MeromorphicOn f (Set.univ : Set ℂ)) (j : ℕ) :
    MeromorphicOn (iteratedDeriv j f) (Set.univ : Set ℂ) := by
  induction j with
  | zero =>
      simpa [iteratedDeriv_zero] using hf
  | succ n ih =>
      intro z _
      rw [iteratedDeriv_succ]
      exact (ih z (Set.mem_univ z)).deriv

/-- **Differentiating a germ mixed constraint kills its constant.**  On an open punctured set the
mixed combination is constant, so its derivative vanishes there, and the derivative splits along the
four translates because each of them is analytic. -/
theorem mixedConstGerm_deriv {f : ℂ → ℂ} {τ σ Cst : ℂ}
    (hf : MeromorphicOn f (Set.univ : Set ℂ)) (h : MixedConstGerm f τ σ Cst) :
    MixedConstGerm (deriv f) τ σ 0 := by
  intro z
  have hτσ : ∀ᶠ w in 𝓝[≠] z, AnalyticAt ℂ f (w + τ + σ) := by
    filter_upwards [eventually_nhdsNE_analyticAt_comp_add hf (τ + σ) z] with w hw
    rwa [show w + τ + σ = w + (τ + σ) by ring]
  obtain ⟨W, hWopen, hWmem, hW⟩ := exists_isOpen_of_eventually_nhdsNE
    ((h z).and ((eventually_nhdsNE_analyticAt_comp_add hf 0 z).and
      ((eventually_nhdsNE_analyticAt_comp_add hf τ z).and
        ((eventually_nhdsNE_analyticAt_comp_add hf σ z).and hτσ))))
  filter_upwards [hWmem] with w hw
  obtain ⟨_, han0, hanτ, hanσ, hanτσ⟩ := hW w hw
  have han0' : AnalyticAt ℂ f w := by simpa using han0
  have hd3 : DifferentiableAt ℂ (fun u ↦ f (u + τ + σ)) w := by
    have : DifferentiableAt ℂ (fun u ↦ f (u + (τ + σ))) w :=
      (analyticAt_comp_add_const (by rwa [show w + (τ + σ) = w + τ + σ by ring])).differentiableAt
    simpa [add_assoc] using this
  have hd1 : DifferentiableAt ℂ (fun u ↦ f (u + τ)) w :=
    (analyticAt_comp_add_const hanτ).differentiableAt
  have hd2 : DifferentiableAt ℂ (fun u ↦ f (u + σ)) w :=
    (analyticAt_comp_add_const hanσ).differentiableAt
  have hMev : (fun u ↦ f (u + τ + σ) - f (u + τ) - f (u + σ) + f u) =ᶠ[𝓝 w] fun _ ↦ Cst := by
    filter_upwards [hWopen.mem_nhds hw] with u hu using (hW u hu).1
  have h0 : deriv (fun u ↦ f (u + τ + σ) - f (u + τ) - f (u + σ) + f u) w = 0 := by
    rw [hMev.deriv_eq, deriv_const]
  have hdA : DifferentiableAt ℂ (fun u ↦ f (u + τ + σ) - f (u + τ)) w := hd3.fun_sub hd1
  have hdB : DifferentiableAt ℂ (fun u ↦ f (u + τ + σ) - f (u + τ) - f (u + σ)) w := hdA.fun_sub hd2
  rw [deriv_fun_add hdB han0'.differentiableAt, deriv_fun_sub hdA hd2,
    deriv_fun_sub hd3 hd1] at h0
  have e3 : deriv (fun u ↦ f (u + τ + σ)) w = deriv f (w + τ + σ) := by
    have := deriv_comp_add_const (f := f) (a := τ + σ) w
    rw [show w + (τ + σ) = w + τ + σ by ring] at this
    simpa [add_assoc] using this
  rw [e3, deriv_comp_add_const f τ w, deriv_comp_add_const f σ w] at h0
  linear_combination h0

/-- Every jet of a germ mixed-constraint source has vanishing mixed constant. -/
theorem mixedConstGerm_iteratedDeriv_succ {f : ℂ → ℂ} {τ σ Cst : ℂ}
    (hf : MeromorphicOn f (Set.univ : Set ℂ)) (h : MixedConstGerm f τ σ Cst) (j : ℕ) :
    MixedConstGerm (iteratedDeriv (j + 1) f) τ σ 0 := by
  induction j with
  | zero =>
      have hfun : iteratedDeriv 1 f = deriv f := iteratedDeriv_one
      rw [hfun]
      exact mixedConstGerm_deriv hf h
  | succ n ih =>
      have hfun : iteratedDeriv (n + 2) f = deriv (iteratedDeriv (n + 1) f) := iteratedDeriv_succ
      rw [hfun]
      exact mixedConstGerm_deriv (meromorphicOn_iteratedDeriv hf (n + 1)) ih

end

end GaloisForLFunctions.HTGeometry
