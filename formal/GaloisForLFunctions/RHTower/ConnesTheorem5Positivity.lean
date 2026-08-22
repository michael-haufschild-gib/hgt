import GaloisForLFunctions.RHTower.ConnesPositiveTypeCutoff

/-!
# §VIII Theorem 5: the Weil distribution is of positive type

§VIII (22)–(25) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Connes derives the Riemann Hypothesis for all Grössencharakters from the trace formula in three
steps:

* (23) the periodization carries the cut-off subspace into the module window, so the difference
  `r_Λ = S_Λ − Q'_{Λ,0}` of the two projections is a positive operator
  (`connes_starProjection_norm_mono`);
* (24)(25) hence the cut-off functional `Δ_Λ(f) = τ_Λ(V(f)^* r_Λ V(f))` is nonnegative on the
  positive cone (`connes_positiveType_conjugate`);
* letting `Λ → ∞`, the trace formula identifies the limit as Weil's distribution, and positivity
  passes to the limit.

The last step is what this file supplies, together with the assembled statement.  The trace
formula that provides the convergence hypothesis is `ConnesTraceFormulaWeil.connes_trace4_weil`;
the final passage from positivity of the Weil distribution to RH is Weil's explicit-formula
criterion, which Connes *quotes* rather than proves.
-/

open Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- **Positivity passes to the limit.** -/
theorem connes_theorem5_positive_of_tendsto {A : Type*} {Δ : A → ℝ} {ΔΛ : ℝ → A → ℝ}
    {S : Set A}
    (hpos : ∀ᶠ Λ : ℝ in atTop, ∀ a ∈ S, 0 ≤ ΔΛ Λ a)
    (hlim : ∀ a ∈ S, Tendsto (fun Λ : ℝ => ΔΛ Λ a) atTop (𝓝 (Δ a))) :
    ∀ a ∈ S, 0 ≤ Δ a := by
  intro a ha
  refine ge_of_tendsto (hlim a ha) ?_
  filter_upwards [hpos] with Λ hΛ
  exact hΛ a ha

/-- **§VIII Theorem 5, assembled.**  If the cut-off functionals are the conjugation traces
`Δ_Λ(f^* f) = τ_Λ(V(f)^* r_Λ V(f))` with `r_Λ ≥ 0` and positive traces `τ_Λ`, and if they converge
pointwise, then the limit — Connes' Weil distribution — is of positive type. -/
theorem connes_theorem5_weil_positiveType {A B : Type*} [NonUnitalRing A] [StarRing A]
    [NonUnitalRing B] [PartialOrder B] [StarRing B] [StarOrderedRing B]
    (V : A → B) (τ : ℝ → (B →+ ℝ)) (r : ℝ → B) (Δ : A → ℝ) (ΔΛ : ℝ → A → ℝ)
    (hτ : ∀ Λ : ℝ, ∀ b : B, 0 ≤ b → 0 ≤ τ Λ b)
    (hr : ∀ Λ : ℝ, 0 ≤ r Λ)
    (hcut : ∀ (Λ : ℝ) (f : A), ΔΛ Λ (star f * f) = τ Λ (star (V f) * r Λ * V f))
    (hlim : ∀ a : A, Tendsto (fun Λ : ℝ => ΔΛ Λ a) atTop (𝓝 (Δ a))) :
    ∀ f : A, 0 ≤ Δ (star f * f) := by
  intro f
  refine ge_of_tendsto (hlim (star f * f)) ?_
  filter_upwards with Λ
  rw [hcut Λ f]
  exact connes_positiveType_conjugate (hτ Λ) (hr Λ) (V f)

/-- The hypotheses of `connes_theorem5_weil_positiveType` have a model, so the theorem is not
vacuous. -/
theorem connes_theorem5_hypotheses_model :
    ∃ (V : ℝ → ℝ) (τ : ℝ → (ℝ →+ ℝ)) (r : ℝ → ℝ) (Δ : ℝ → ℝ) (ΔΛ : ℝ → ℝ → ℝ),
      (∀ Λ : ℝ, ∀ b : ℝ, 0 ≤ b → 0 ≤ τ Λ b) ∧
      (∀ Λ : ℝ, 0 ≤ r Λ) ∧
      (∀ (Λ : ℝ) (f : ℝ), ΔΛ Λ (star f * f) = τ Λ (star (V f) * r Λ * V f)) ∧
      (∀ a : ℝ, Tendsto (fun Λ : ℝ => ΔΛ Λ a) atTop (𝓝 (Δ a))) := by
  refine ⟨id, fun _ => AddMonoidHom.id ℝ, fun _ => 1, id, fun _ => id, ?_, ?_, ?_, ?_⟩
  · intro _ b hb
    exact hb
  · intro _
    exact zero_le_one
  · intro Λ f
    simp [star_trivial]
  · intro a
    exact tendsto_const_nhds

end

end GaloisForLFunctions.RHTower
