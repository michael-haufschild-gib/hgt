import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleHypertranscendence
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleDivisor
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# Divisor and hypertranscendence of the socle response on the whole chamber

For every `σ > 0` and real `τ` with `σ + τ > 1` the socle response
`C_{σ,τ}(z) = ∏_{j≥1} ζ(jσ + τ + z)/ζ(jσ + τ)` satisfies no algebraic differential equation on the
half-plane `Re z > 1 - σ - τ` where the ladder converges.  On that half-plane `C` is holomorphic and
zero-free and satisfies `C(z) = ζ(σ + τ + z) C(z + σ)`.  Differential algebraicity on a domain is
closed under translation and quotients, so a relation for `C` would give one for `z ↦ ζ(σ + τ + z)`;
propagating it across the single pole and undoing the translation contradicts Hilbert's theorem.

The response is the ladder translated by `τ` and divided by a nonzero constant, so its divisor at
every `z₀` is the finite sum of zeta orders at `jσ + τ + z₀` over the depths below the tail
threshold.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry.AbelianZetaGas

/-- The convergence half-plane `Re z > 1 - σ - τ` of the socle response. -/
def responseHalfPlane (σ τ : ℝ) : Set ℂ := {z : ℂ | 1 - σ - τ < z.re}

theorem mem_responseHalfPlane_iff {σ τ : ℝ} {z : ℂ} :
    z ∈ responseHalfPlane σ τ ↔ (τ : ℂ) + z ∈ socleChamber σ := by
  simp only [responseHalfPlane, socleChamber, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re]
  constructor <;> intro h <;> linarith

theorem isOpen_responseHalfPlane (σ τ : ℝ) : IsOpen (responseHalfPlane σ τ) :=
  isOpen_lt continuous_const Complex.continuous_re

theorem isPreconnected_responseHalfPlane (σ τ : ℝ) : IsPreconnected (responseHalfPlane σ τ) :=
  (convex_halfSpace_re_gt (1 - σ - τ)).isPreconnected

theorem responseHalfPlane_infinite (σ τ : ℝ) : (responseHalfPlane σ τ).Infinite := by
  refine Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => (((n : ℝ) + (|1 - σ - τ| + 1) : ℝ) : ℂ))
    (fun a b hab => by
      have := congrArg Complex.re hab
      simp only [Complex.ofReal_re] at this
      exact_mod_cast add_right_cancel this) fun n => ?_
  simp only [responseHalfPlane, Set.mem_setOf_eq, Complex.ofReal_re]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith [le_abs_self (1 - σ - τ)]

theorem responseHalfPlane_nonempty (σ τ : ℝ) : (responseHalfPlane σ τ).Nonempty :=
  (responseHalfPlane_infinite σ τ).nonempty

theorem add_mem_responseHalfPlane {σ τ : ℝ} (hσ : 0 < σ) {z : ℂ}
    (hz : z ∈ responseHalfPlane σ τ) : z + (σ : ℂ) ∈ responseHalfPlane σ τ := by
  simp only [responseHalfPlane, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re] at hz ⊢
  linarith

theorem analyticAt_socleResponse {σ τ : ℝ} (hσ : 0 < σ) {z : ℂ}
    (hz : z ∈ responseHalfPlane σ τ) : AnalyticAt ℂ (socleResponse σ τ) z := by
  have hmem : (τ : ℂ) + z ∈ socleChamber σ := mem_responseHalfPlane_iff.mp hz
  have hL : AnalyticAt ℂ (socleLadder σ) ((τ : ℂ) + z) :=
    ((differentiableOn_socleLadder hσ).analyticOnNhd (isOpen_socleChamber σ)) _ hmem
  have hshift : AnalyticAt ℂ (fun w : ℂ => (τ : ℂ) + w) z := analyticAt_const.add analyticAt_id
  have hcomp := AnalyticAt.comp (g := socleLadder σ) (f := fun w : ℂ => (τ : ℂ) + w) hL hshift
  exact hcomp.div_const

theorem socleResponse_ne_zero {σ τ : ℝ} (hσ : 0 < σ) (hτ : 1 < σ + τ) {z : ℂ}
    (hz : z ∈ responseHalfPlane σ τ) : socleResponse σ τ z ≠ 0 := by
  rw [socleResponse]
  refine div_ne_zero (socleLadder_ne_zero_of_mem hσ (mem_responseHalfPlane_iff.mp hz))
    (socleLadder_ne_zero_of_mem hσ ?_)
  simp only [socleChamber, Set.mem_setOf_eq, Complex.ofReal_re]
  linarith

/-- Dividing by a nonzero constant does not change the meromorphic order. -/
theorem meromorphicOrderAt_div_const {g : ℂ → ℂ} {c : ℂ} (hc : c ≠ 0) (x : ℂ) :
    meromorphicOrderAt (fun z => g z / c) x = meromorphicOrderAt g x := by
  classical
  by_cases hg : MeromorphicAt g x
  · have h := meromorphicOrderAt_div (f := g) (g := fun _ => c) hg (MeromorphicAt.const c x)
    rw [meromorphicOrderAt_const, if_neg hc, sub_zero] at h
    exact h
  · rw [meromorphicOrderAt_of_not_meromorphicAt hg, meromorphicOrderAt_of_not_meromorphicAt]
    intro h
    refine hg ((h.mul (MeromorphicAt.const c x)).congr ?_)
    filter_upwards with z
    exact div_mul_cancel₀ (g z) hc

/-- `(AZC.18)`  **Divisor of the response.**  At every `z₀`, the order of `C_{σ,τ}` is the finite
sum `∑_{j<J} ord_{(j+1)σ + τ + z₀} ζ` for every depth `J` above the tail threshold at level `b`. -/
theorem meromorphicOrderAt_socleResponse {σ τ b : ℝ} (hσ : 0 < σ) (hτ : 1 < σ + τ) {J : ℕ}
    (hJ : SocleTail.socleTailThreshold σ b ≤ J) {z₀ : ℂ} (hz₀ : b < τ + z₀.re) :
    meromorphicOrderAt (socleResponse σ τ) z₀
      = ∑ j ∈ Finset.range J,
        meromorphicOrderAt riemannZeta (((j + 1 : ℕ) : ℂ) * (σ : ℂ) + ((τ : ℂ) + z₀)) := by
  have hne : socleLadder σ (τ : ℂ) ≠ 0 := socleLadder_ne_zero_of_mem hσ (by
    simp only [socleChamber, Set.mem_setOf_eq, Complex.ofReal_re]
    linarith)
  have hfun : socleResponse σ τ = fun z => (fun w => socleLadder σ (w + (τ : ℂ))) z /
      socleLadder σ (τ : ℂ) := by
    funext z
    rw [socleResponse, add_comm]
  rw [hfun, meromorphicOrderAt_div_const hne,
    meromorphicOrderAt_comp_add (socleLadder σ) z₀ (τ : ℂ), add_comm z₀]
  exact meromorphicOrderAt_socleLadder hσ hJ (by simpa [Complex.add_re] using hz₀)

/-- **Theorem 7.1 on the whole chamber.**  For every `σ > 0` and `τ` with `σ + τ > 1`, the socle
response `C_{σ,τ}` satisfies no algebraic differential equation on its convergence half-plane. -/
theorem not_differentiallyAlgebraicOn_socleResponse_chamber {σ τ : ℝ} (hσ : 0 < σ)
    (hτ : 1 < σ + τ) :
    ¬ DifferentiallyAlgebraicOn (socleResponse σ τ) (responseHalfPlane σ τ) := by
  intro hDA
  have hWo := isOpen_responseHalfPlane σ τ
  have hWc := isPreconnected_responseHalfPlane σ τ
  have hWne := responseHalfPlane_nonempty σ τ
  have hWinf := responseHalfPlane_infinite σ τ
  have hCan : AnalyticOnNhd ℂ (socleResponse σ τ) (responseHalfPlane σ τ) := fun z hz =>
    analyticAt_socleResponse hσ hz
  have hBan : AnalyticOnNhd ℂ (fun z => socleResponse σ τ (z + (σ : ℂ)))
      (responseHalfPlane σ τ) := by
    intro z hz
    have h := analyticAt_socleResponse hσ (add_mem_responseHalfPlane hσ hz)
    have hshift : AnalyticAt ℂ (fun w : ℂ => w + (σ : ℂ)) z := analyticAt_id.add analyticAt_const
    simpa [Function.comp_def] using
      AnalyticAt.comp (g := socleResponse σ τ) (f := fun w : ℂ => w + (σ : ℂ)) h hshift
  have hBne : ∀ z ∈ responseHalfPlane σ τ, socleResponse σ τ (z + (σ : ℂ)) ≠ 0 := fun z hz =>
    socleResponse_ne_zero hσ hτ (add_mem_responseHalfPlane hσ hz)
  have hBDA : DifferentiallyAlgebraicOn (fun z => socleResponse σ τ (z + (σ : ℂ)))
      (responseHalfPlane σ τ) :=
    DifferentiallyAlgebraicOn.mono (fun z hz => add_mem_responseHalfPlane hσ hz)
      (DifferentiallyAlgebraicOn.comp_add_const hDA (σ : ℂ))
  have hquot := differentiallyAlgebraicOn_div hWo hWc hWne hWinf hCan hBan hBne hDA hBDA
  set a : ℂ := ((σ + τ : ℝ) : ℂ) with hadef
  have hzeta : DifferentiallyAlgebraicOn (fun z => riemannZeta (z + a))
      (responseHalfPlane σ τ) := by
    refine DifferentiallyAlgebraicOn.congr hWo ?_ hquot
    intro z hz
    have h := socleResponse_translation hσ τ z
    rw [div_eq_iff (hBne z hz), ← h, hadef]
    push_cast
    ring_nf
  have hpole : AnalyticOnNhd ℂ (fun z => riemannZeta (z + a)) ({1 - a}ᶜ : Set ℂ) := by
    intro z hz
    have hne : z + a ≠ 1 := fun h => hz (by rw [Set.mem_singleton_iff]; linear_combination h)
    have h := AnalyticAt.comp (g := riemannZeta) (f := fun w : ℂ => w + a) (x := z)
      (analyticOn_riemannZeta _ hne) (analyticAt_id.add analyticAt_const)
    simpa [Function.comp_def] using h
  have hsub : responseHalfPlane σ τ ⊆ ({1 - a}ᶜ : Set ℂ) := by
    intro z hz h1
    rw [Set.mem_singleton_iff] at h1
    have hre := congrArg Complex.re h1
    simp only [responseHalfPlane, Set.mem_setOf_eq] at hz
    rw [hadef] at hre
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re] at hre
    linarith
  have hglobal := differentiallyAlgebraic_of_on_compl_singleton hpole hWo hWne hsub hzeta
  exact hypertranscendental_riemannZeta
    ((differentiallyAlgebraic_comp_add_const_iff (f := riemannZeta) a).mp hglobal)

end GaloisForLFunctions.HTGeometry.AbelianZetaGas
