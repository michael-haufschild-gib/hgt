import GaloisForLFunctions.HTGeometry.StripHullHolomorphic

/-!
# The differential relation propagates to the whole carrier

Locally uniform convergence of holomorphic functions carries over to every iterated derivative, so a
continuous relation among the derivatives — a polynomial differential relation, say — passes to
locally uniform limits.  Vertical translates of a solution of an *autonomous* relation are again
solutions, so every uniform limit of translates satisfies the same relation, and in particular every
point of the phase carrier does.

Together with the jet separation theorem for explicit equations this is what makes the finite jet
sample injective on the carrier: all carrier points solve one and the same equation, so agreeing
jets force agreement.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {F : ℂ → ℂ} {σ R r : ℝ}

/-- Locally uniform convergence of holomorphic functions passes to every iterated derivative. -/
theorem tendstoLocallyUniformlyOn_iteratedDeriv {U : Set ℂ} (hU : IsOpen U)
    {ι : Type*} {φ : Filter ι} {Fs : ι → ℂ → ℂ} {g : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn Fs g φ U)
    (hdiff : ∀ᶠ m in φ, DifferentiableOn ℂ (Fs m) U) : ∀ k : ℕ,
      TendstoLocallyUniformlyOn (fun m => iteratedDeriv k (Fs m)) (iteratedDeriv k g) φ U ∧
        (∀ᶠ m in φ, DifferentiableOn ℂ (iteratedDeriv k (Fs m)) U) := by
  intro k
  induction k with
  | zero =>
      constructor
      · simpa [iteratedDeriv_zero] using hconv
      · simpa [iteratedDeriv_zero] using hdiff
  | succ j ih =>
      obtain ⟨hc, hd⟩ := ih
      constructor
      · have hderiv := hc.deriv hd hU
        have hrw : (deriv ∘ fun m => iteratedDeriv j (Fs m))
            = fun m => iteratedDeriv (j + 1) (Fs m) := by
          funext m
          rw [iteratedDeriv_succ]
          rfl
        rw [hrw] at hderiv
        rw [iteratedDeriv_succ]
        exact hderiv
      · filter_upwards [hd] with m hm
        rw [iteratedDeriv_succ]
        exact ((hm.analyticOnNhd hU).deriv).differentiableOn

/-- **A polynomial differential relation passes to locally uniform limits.** -/
theorem relation_of_tendstoLocallyUniformlyOn {U : Set ℂ} (hU : IsOpen U)
    {ι : Type*} {φ : Filter ι} [φ.NeBot] {Fs : ι → ℂ → ℂ} {g : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn Fs g φ U)
    (hdiff : ∀ᶠ m in φ, DifferentiableOn ℂ (Fs m) U)
    {n : ℕ} {P : (Fin n → ℂ) → ℂ} (hP : Continuous P)
    (hrel : ∀ᶠ m in φ, ∀ z ∈ U, P (fun k => iteratedDeriv (k : ℕ) (Fs m) z) = 0) :
    ∀ z ∈ U, P (fun k => iteratedDeriv (k : ℕ) g z) = 0 := by
  intro z hz
  have hjet : Tendsto (fun m => (fun k : Fin n => iteratedDeriv (k : ℕ) (Fs m) z)) φ
      (nhds (fun k : Fin n => iteratedDeriv (k : ℕ) g z)) := by
    rw [tendsto_pi_nhds]
    intro k
    exact ((tendstoLocallyUniformlyOn_iteratedDeriv hU hconv hdiff (k : ℕ)).1).tendsto_at hz
  have hlim : Tendsto (fun m => P (fun k : Fin n => iteratedDeriv (k : ℕ) (Fs m) z)) φ
      (nhds (P (fun k : Fin n => iteratedDeriv (k : ℕ) g z))) := (hP.tendsto _).comp hjet
  have hzero : Tendsto (fun m => P (fun k : Fin n => iteratedDeriv (k : ℕ) (Fs m) z)) φ
      (nhds 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hrel] with m hm
    exact (hm z hz).symm
  exact tendsto_nhds_unique hlim hzero

/-- **Uniform limits of translates satisfy the same autonomous differential relation.** -/
theorem relation_of_translate_limit (hr : r < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    {n : ℕ} {P : (Fin n → ℂ) → ℂ} (hP : Continuous P)
    (hrel : ∀ z ∈ verticalStrip σ R, P (fun k => iteratedDeriv (k : ℕ) F z) = 0)
    {g : ℂ → ℂ} {τ : ℕ → ℝ}
    (hconv : TendstoUniformlyOn (fun m z => F (z + (τ m : ℂ) * Complex.I)) g atTop
      (closedStrip σ r)) :
    ∀ z ∈ verticalStrip σ r, P (fun k => iteratedDeriv (k : ℕ) g z) = 0 := by
  have hsub : verticalStrip σ r ⊆ closedStrip σ r := by
    intro z hz
    show |z.re - σ| ≤ r
    exact le_of_lt hz
  have hdiff : ∀ m : ℕ, DifferentiableOn ℂ (fun z => F (z + (τ m : ℂ) * Complex.I))
      (verticalStrip σ r) := by
    intro m z hz
    have hzs : z + (τ m : ℂ) * Complex.I ∈ verticalStrip σ R := by
      have hmem : z + (τ m : ℂ) * Complex.I ∈ closedStrip σ r :=
        mem_closedStrip_add_I σ r z (hsub hz) (τ m)
      exact closedStrip_subset_verticalStrip hr hmem
    exact ((hF.differentiableAt ((isOpen_verticalStrip σ R).mem_nhds hzs)).comp z
      ((differentiable_id.add_const _) z)).differentiableWithinAt
  have hrelm : ∀ m : ℕ, ∀ z ∈ verticalStrip σ r,
      P (fun k => iteratedDeriv (k : ℕ) (fun w => F (w + (τ m : ℂ) * Complex.I)) z) = 0 := by
    intro m z hz
    have hshift : ∀ k : ℕ, iteratedDeriv k (fun w => F (w + (τ m : ℂ) * Complex.I)) z
        = iteratedDeriv k F (z + (τ m : ℂ) * Complex.I) := by
      intro k
      rw [iteratedDeriv_comp_add_const]
    have hzs : z + (τ m : ℂ) * Complex.I ∈ verticalStrip σ R := by
      have hmem : z + (τ m : ℂ) * Complex.I ∈ closedStrip σ r :=
        mem_closedStrip_add_I σ r z (hsub hz) (τ m)
      exact closedStrip_subset_verticalStrip hr hmem
    have := hrel _ hzs
    rw [← this]
    congr 1
    funext k
    exact hshift (k : ℕ)
  refine relation_of_tendstoLocallyUniformlyOn (φ := (atTop : Filter ℕ))
    (Fs := fun m z => F (z + (τ m : ℂ) * Complex.I)) (g := g)
    (isOpen_verticalStrip σ r) ?_ ?_ hP ?_
  · exact (hconv.mono hsub).tendstoLocallyUniformlyOn
  · exact Filter.Eventually.of_forall hdiff
  · exact Filter.Eventually.of_forall hrelm

/-- **The phase carrier is a family of solutions of the same autonomous relation.** -/
theorem exists_solution_of_hull (hr : r < R) (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    {n : ℕ} {P : (Fin n → ℂ) → ℂ} (hP : Continuous P)
    (hrel : ∀ z ∈ verticalStrip σ R, P (fun k => iteratedDeriv (k : ℕ) F z) = 0)
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ ℂ)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I))
    (x : BohrHull Gb) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (verticalStrip σ r) ∧
      (∀ z : closedStrip σ r, g (z : ℂ) = bohrEval Gb x z) ∧
        ∀ z ∈ verticalStrip σ r, P (fun k => iteratedDeriv (k : ℕ) g z) = 0 := by
  obtain ⟨g, τ, huniform, hgval⟩ := exists_translate_seq_of_hull hGb x
  exact ⟨g, differentiableOn_of_tendstoUniformlyOn hr hF huniform, hgval,
    relation_of_translate_limit hr hF hP hrel huniform⟩

end GaloisForLFunctions
