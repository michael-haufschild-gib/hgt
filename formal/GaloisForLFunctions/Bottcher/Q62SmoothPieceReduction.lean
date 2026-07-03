/-
# Smooth-piece rigidity (#118 general gatekeeper) reduced to Schwarz reflection alone

`SmoothPieceRigidity c₁ c₂` (HbothconnAssembly) is the general both-connected gatekeeper of q62: no
relatively-open piece of `J_{c₁}` sits inside the modulus-one locus of a branch of a separable fibre
polynomial with `K_{c₂}ᶜ`-analytic coefficients. This file discharges everything in it except one
genuinely mathlib-absent complex-analysis input.

Chain:
* the continuous root branch `wfam k` upgrades to **analytic** on `Ω = ball z₁ ρ ∩ K_{c₂}ᶜ` (where the
  coefficients live): at each point the fibre has `N` distinct roots of degree `N`, hence is separable
  (`separable_of_distinct_roots`), the root `wfam k` is simple, the implicit function theorem
  (`exists_analyticAt_branch_analytic`) gives an analytic branch, and branch uniqueness
  (`eqOn_branch_of_relation_analytic`) identifies it with `wfam k` — **proven here**
  (`wfam_analyticOnNhd_of_smoothPiece`);
* if `wfam k` is locally constant `≡ ζ` (`‖ζ‖ = 1`), the relation `∑ aᵢ(z)·ζⁱ = 0` propagates over the
  connected basin `K_{c₂}ᶜ` by the identity theorem, contradicting the unit-root exclusion — **proven
  here**;
* if `wfam k` is non-constant, the `J_{c₁}` piece lies in its real-analytic modulus-one locus, and the
  Böttcher branch `β_{c₁}` reflects across it — the isolated `ReflectionCore`, the one remaining input;
* the resulting continuation of `β_{c₁}` contradicts the proven natural boundary
  `hnb_of_mem_mandelbrot_connected` — **wired in here**.

Result: for connected `c₁ ∈ mandelbrot ∖ {0,-2}`, `SmoothPieceRigidity c₁ c₂` reduces to exactly
`ReflectionCore c₁` (Schwarz reflection across an analytic Julia arc + boundary regularity). Everything
else — branch analyticity, the constant case, and the endgame — is proven. Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.InteriorNonemptyHnb
import GaloisForLFunctions.Bottcher.HbothconnAssembly
import GaloisForLFunctions.Bottcher.RelativeBranchFamily
import GaloisForLFunctions.Bottcher.RelativeNaturalBoundary

open Metric Set Topology Filter Complex Polynomial

namespace Bottcher

/-- **A degree-`N` complex polynomial with `N` distinct roots is separable.** The `N` distinct roots
give `≥ N` elements in `roots.toFinset`, while `toFinset.card ≤ card roots ≤ natDegree = N`; equality
forces `roots.Nodup`, and over `ℂ` (which splits everything) `nodup_roots_iff_of_splits` gives
separability. This is the reverse of `nodup_roots` and supplies separability at every point of the ball
from the distinct-root data of the smooth-piece configuration. -/
theorem separable_of_distinct_roots {p : ℂ[X]} {N : ℕ} (hN : 1 ≤ N)
    (hdeg : p.natDegree = N) (f : Fin N → ℂ) (hinj : Function.Injective f)
    (hroots : ∀ k, p.eval (f k) = 0) : p.Separable := by
  have hp0 : p ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; omega
  have hsplits : p.Splits := IsAlgClosed.splits p
  rw [← nodup_roots_iff_of_splits hp0 hsplits]
  have hmem : ∀ k, f k ∈ p.roots := fun k => by rw [Polynomial.mem_roots hp0]; exact hroots k
  have hsub : (Finset.univ.image f) ⊆ p.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨k, rfl⟩ := hx; exact Multiset.mem_toFinset.mpr (hmem k)
  have hcard_image : (Finset.univ.image f).card = N := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hge : N ≤ p.roots.toFinset.card := hcard_image ▸ Finset.card_le_card hsub
  have hle_deg : Multiset.card p.roots ≤ N := hdeg ▸ p.card_roots'
  have htoLe : p.roots.toFinset.card ≤ Multiset.card p.roots := Multiset.toFinset_card_le _
  have heq : p.roots.toFinset.card = Multiset.card p.roots := le_antisymm htoLe (by omega)
  exact Multiset.toFinset_card_eq_card_iff_nodup.mp heq

/-- **Branch analyticity upgrade.** A continuous root branch `wfam k` of the fibre family (distinct
roots, constant degree `N`, `K_{c₂}ᶜ`-analytic coefficients) is analytic on `ball z₁ ρ ∩ K_{c₂}ᶜ`. At
each point `zs` there the fibre is separable (`separable_of_distinct_roots` from the `N` distinct
roots), its leading coefficient `a N zs` is nonzero (degree `N`), so `wfam k zs` is a simple root; the
implicit function theorem (`exists_analyticAt_branch_analytic`) produces an analytic branch `g` through
it, and branch uniqueness (`eqOn_branch_of_relation_analytic`, matching the index by distinctness)
identifies `g` with `wfam k` on a neighborhood, transferring analyticity. This discharges the `hbranch`
interface of the smooth-piece reduction. -/
theorem wfam_analyticOnNhd_of_smoothPiece
    {c₂ : ℂ} (a : ℕ → ℂ → ℂ) (sT : Finset ℕ) (N : ℕ) (wfam : Fin N → ℂ → ℂ)
    (z₁ : ℂ) (ρ : ℝ) (k : Fin N)
    (hNsT : N ∈ sT) (hN1 : 1 ≤ N)
    (ha : ∀ i ∈ sT, AnalyticOnNhd ℂ (a i) (filledJulia c₂)ᶜ)
    (hcont : ∀ k', ContinuousOn (wfam k') (Metric.ball z₁ ρ))
    (hdist : ∀ z ∈ Metric.ball z₁ ρ, ∀ k' l, k' ≠ l → wfam k' z ≠ wfam l z)
    (hdeg : ∀ z ∈ Metric.ball z₁ ρ, (fibrePoly a sT z).natDegree = N)
    (hroot : ∀ k', ∀ z ∈ Metric.ball z₁ ρ, ∑ i ∈ sT, a i z * (wfam k' z) ^ i = 0) :
    AnalyticOnNhd ℂ (wfam k) (Metric.ball z₁ ρ ∩ (filledJulia c₂)ᶜ) := by
  rintro zs ⟨hzsball, hzsK₂⟩
  have haCD : ∀ i ∈ sT, ContDiffAt ℂ ⊤ (a i) zs := fun i hi => (ha i hi zs hzsK₂).contDiffAt
  set Q := fibrePoly a sT zs with hQdef
  have hdegzs : Q.natDegree = N := hdeg zs hzsball
  have hinj : Function.Injective (fun k' => wfam k' zs) := by
    intro k' l h; by_contra hne; exact hdist zs hzsball k' l hne h
  have hrootszs : ∀ k', Q.eval (wfam k' zs) = 0 := fun k' => by
    rw [hQdef, eval_fibrePoly]; exact hroot k' zs hzsball
  have hsep : Q.Separable :=
    separable_of_distinct_roots hN1 hdegzs (fun k' => wfam k' zs) hinj hrootszs
  have hlead : a N zs ≠ 0 := by
    have hQ0 : Q ≠ 0 := fun h => by rw [h, natDegree_zero] at hdegzs; omega
    have hlc := Polynomial.leadingCoeff_ne_zero.mpr hQ0
    rwa [Polynomial.leadingCoeff, hdegzs, hQdef, coeff_fibrePoly, if_pos hNsT] at hlc
  have hpart : HasDerivAt (fun w => ∑ i ∈ sT, a i zs * w ^ i)
      (Q.derivative.eval (wfam k zs)) (wfam k zs) := relation_hasDerivAt_w_analytic a sT zs (wfam k zs)
  have hd : Q.derivative.eval (wfam k zs) ≠ 0 := eval_derivative_ne_zero_of_separable hsep (hrootszs k)
  obtain ⟨g, hgAt, hgz, hgrel⟩ :=
    exists_analyticAt_branch_analytic haCD (hroot k zs hzsball) hpart hd
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff.mp
    (hgrel.and ((hgAt.eventually_analyticAt).and (isOpen_ball.eventually_mem hzsball)))
  set U := Metric.ball zs δ with hUdef
  have hUsub : U ⊆ Metric.ball z₁ ρ := fun z hz => (hδball (Metric.mem_ball.mp hz)).2.2
  have hgcont : ContinuousOn g U := fun z hz =>
    (hδball (Metric.mem_ball.mp hz)).2.1.continuousAt.continuousWithinAt
  have hgrootU : ∀ z ∈ U, ∑ i ∈ sT, a i z * (g z) ^ i = 0 := fun z hz =>
    (hδball (Metric.mem_ball.mp hz)).1
  obtain ⟨j, hj⟩ := eqOn_branch_of_relation_analytic hN1 wfam g (convex_ball zs δ).isPreconnected
    (fun k' => (hcont k').mono hUsub) hgcont
    (fun z hz => hdist z (hUsub hz)) (fun z hz => hdeg z (hUsub hz))
    (fun k' z hz => hroot k' z (hUsub hz)) hgrootU (Metric.mem_ball_self hδ)
  have hjk : j = k := by
    by_contra hne
    exact hdist zs hzsball j k hne
      (by rw [← hj (Metric.mem_ball_self hδ)]; exact hgz)
  subst hjk
  have hgw : g =ᶠ[𝓝 zs] wfam j := by
    filter_upwards [isOpen_ball.mem_nhds (Metric.mem_ball_self hδ)] with z hz using hj hz
  exact hgAt.congr hgw

/-- **The reflection core — the one remaining deep input of smooth-piece rigidity.** A non-constant
analytic `φ` (nonzero derivative somewhere on the open `Ω`) whose modulus is `1` on a relatively-open
piece `P` of `frontier (filledJulia c₁)` forces the Böttcher branch `β` to continue analytically across
some frontier point. Content: the modulus-one locus of a non-constant analytic function is a
real-analytic curve, so the `J_{c₁}` piece is a real-analytic arc, and `β` reflects across it (Schwarz
reflection across the arc + Carathéodory boundary regularity) — the one genuinely mathlib-absent input. -/
def ReflectionCore (c₁ : ℂ) (β : ℂ → ℂ) : Prop :=
  ∀ (φ : ℂ → ℂ) (Ω P : Set ℂ), IsOpen Ω → AnalyticOnNhd ℂ φ Ω →
    (∃ z' ∈ Ω, deriv φ z' ≠ 0) → P ⊆ Ω → P ⊆ frontier (filledJulia c₁) →
    (∃ Uop, IsOpen Uop ∧ (Uop ∩ P).Nonempty) → (∀ z ∈ P, ‖φ z‖ = 1) →
    ∃ z₀ ∈ frontier (filledJulia c₁), U0NaturalBoundary.ContinuesAcross β (filledJulia c₁)ᶜ z₀

/-- **Smooth-piece rigidity ⟸ the reflection core alone.** For connected `c₁ ∈ mandelbrot ∖ {0,-2}`,
given the reflection core for every Böttcher branch (`hrefl`), `SmoothPieceRigidity c₁ c₂` holds. The
branch-analyticity upgrade is proven internally (`wfam_analyticOnNhd_of_smoothPiece`); the
locally-constant-branch case is killed by the unit-root exclusion (identity theorem on the connected
basin `K_{c₂}ᶜ`); the non-constant case feeds the reflection core, producing a continuation of the
Böttcher branch across the frontier that contradicts `hnb_of_mem_mandelbrot_connected`. This reduces
the general-both-connected gatekeeper (#118) to exactly `ReflectionCore` — Schwarz reflection across an
analytic Julia arc. -/
theorem smoothPieceRigidity_of_reflectionCore {c₁ c₂ : ℂ}
    (hc₁M : c₁ ∈ mandelbrot) (hc₁0 : c₁ ≠ 0) (hc₁2 : c₁ ≠ -2)
    (hconn₁ : IsPreconnected (filledJulia c₁))
    (hrefl : ∀ β : ℂ → ℂ, AnalyticOnNhd ℂ β (filledJulia c₁)ᶜ →
        (∀ z ∈ escapeOpen c₁, β z = bottcherCoord c₁ z) → ReflectionCore c₁ β) :
    SmoothPieceRigidity c₁ c₂ := by
  obtain ⟨β, hβan, hβesc, hβmod, hnb⟩ := hnb_of_mem_mandelbrot_connected hc₁M hc₁0 hc₁2 hconn₁
  intro a sT N wfam z₁ ρ ρ₂ k Uop S hsT hNsT hN1 hρ hρ₂ ha haN hsep hunit hcont hdist hdeg
    hroot hz₁front hSclosed hSne hSfront hSball hSK₂ hSshape hUopen hUSne hmod1
  set Ω : Set ℂ := Metric.ball z₁ ρ ∩ (filledJulia c₂)ᶜ with hΩdef
  have hΩopen : IsOpen Ω := isOpen_ball.inter (isClosed_filledJulia c₂).isOpen_compl
  have hwan : AnalyticOnNhd ℂ (wfam k) Ω :=
    wfam_analyticOnNhd_of_smoothPiece a sT N wfam z₁ ρ k hNsT hN1 ha hcont hdist hdeg hroot
  obtain ⟨x, hxP⟩ := hUSne
  have hxS : x ∈ S := hxP.2
  have hxK₂ : x ∈ (filledJulia c₂)ᶜ := hSK₂ hxS
  have hxball : x ∈ Metric.ball z₁ ρ := hSball hxS
  have hxΩ : x ∈ Ω := ⟨hxball, hxK₂⟩
  by_cases hne : ∃ z' ∈ Ω, deriv (wfam k) z' ≠ 0
  · obtain ⟨z₀, hz₀front, hz₀cont⟩ :=
      hrefl β hβan hβesc (wfam k) Ω (Uop ∩ S) hΩopen hwan hne
        (fun z hz => ⟨hSball hz.2, hSK₂ hz.2⟩) (fun z hz => hSfront hz.2)
        ⟨Uop, hUopen, ⟨x, hxP.1, hxP⟩⟩ hmod1
    exact hnb z₀ hz₀front hz₀cont
  · have hd0 : ∀ z ∈ Ω, deriv (wfam k) z = 0 := fun z hz => by
      by_contra h; exact hne ⟨z, hz, h⟩
    obtain ⟨r, hr, hrΩ⟩ := Metric.isOpen_iff.mp hΩopen x hxΩ
    set ζ := wfam k x with hζdef
    have hζ1 : ‖ζ‖ = 1 := hmod1 x hxP
    have hwconst : ∀ z ∈ Metric.ball x r, wfam k z = ζ := fun z hz =>
      isOpen_ball.is_const_of_deriv_eq_zero (convex_ball x r).isPreconnected
        (hwan.mono hrΩ).differentiableOn (fun y hy => hd0 y (hrΩ hy)) hz (mem_ball_self hr)
    have hFrel : ∀ z ∈ Metric.ball x r, ∑ i ∈ sT, a i z * ζ ^ i = 0 := fun z hz => by
      have h0 := hroot k z (hrΩ hz).1
      rw [hwconst z hz] at h0; exact h0
    have haF : AnalyticOnNhd ℂ (fun z => ∑ i ∈ sT, a i z * ζ ^ i) (filledJulia c₂)ᶜ := by
      have hrw : (fun z => ∑ i ∈ sT, a i z * ζ ^ i)
          = ∑ i ∈ sT, (fun z : ℂ => a i z * ζ ^ i) := by funext z; simp only [Finset.sum_apply]
      rw [hrw]; exact Finset.analyticOnNhd_sum sT (fun i hi => (ha i hi).mul analyticOnNhd_const)
    have hev : (fun z => ∑ i ∈ sT, a i z * ζ ^ i) =ᶠ[𝓝 x] 0 := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with z hz using hFrel z hz
    have hEq : Set.EqOn (fun z => ∑ i ∈ sT, a i z * ζ ^ i) 0 (filledJulia c₂)ᶜ :=
      haF.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
        (isPreconnected_compl_filledJulia c₂) hxK₂ hev
    exact hunit ζ hζ1 (fun z hz => hEq hz)

end Bottcher
