/-
# The natural-boundary transcendence engine, abstracted

`U0PhiCard.continues_of_analytic_relation` is the algebraic-IFT continuation step, but it is
hard-wired to the c-velocity `u₀`, its domain `Ext = {1 < ‖z‖}`, its natural boundary `‖z₀‖ = 1`, and
the unit-circle lens `lens_preconnected`. The same engine drives **every** "natural boundary ⟹
transcendental over `ℂ(z)`" argument — in particular the Becker–Bergweiler transcendence of the
inverse Böttcher coordinate `φ_b`, whose natural boundary is the Julia set `J_b`, not the unit circle.

This file abstracts the engine off those specifics. The geometry-specific inputs of the original proof
— the preconnected lens `D ∩ ball z₀ ρ` and its nonemptiness, previously supplied by `‖z₀‖ = 1` — become
a single explicit hypothesis `hlens`. Everything else (`holo_implicit`, `root_complete`,
`branch_selection`, the `anpoly`/`Qpoly` helpers) is already domain-agnostic.

* `continues_of_analytic_relation_gen` — an analytic-coefficient relation `∑ aᵢ(z)·f(z)ⁱ = 0` on an
  open `D`, squarefree at a frontier point `z₀` with a local preconnected lens, continues `f` across `z₀`.
* `no_separable_analytic_relation_gen` — if additionally `f` has a **natural boundary** at `z₀`
  (`¬ ContinuesAcross f D z₀`), no such (separable) relation exists.

Reused at `D = Ext`, `z₀` on the unit circle this reproves the `u₀` case; at `D = Ω_b`, `z₀ ∈ J_b` it is
the φ_b transcendence engine.
-/
import GaloisForLFunctions.U0.U0PhiCard

open Polynomial Filter Topology Complex Metric Set HolomorphicIFT ContinuousLinearMap
open U0 U0NaturalBoundary U0Transcendence U0PhiCard

namespace NaturalBoundaryTranscendence

/-- **Algebraic-IFT continuation across a frontier point (general domain).** If `f` is continuous on an
open set `D`, satisfies the analytic-coefficient relation `∑ᵢ aᵢ(z)·f(z)ⁱ = 0` on `D`, and at `z₀` the
specialization `∑ᵢ aᵢ(z₀)·Yⁱ` has nonzero leading coefficient and `d` distinct simple roots, then —
provided `D` has a local **preconnected lens** at `z₀` (`hlens`: `D ∩ ball z₀ ρ` preconnected and
nonempty for all small `ρ`) — `f` continues analytically across `z₀`. This is
`U0PhiCard.continues_of_analytic_relation` with `(u₀, Ext, ‖z₀‖=1, lens_preconnected)` abstracted to
`(f, D, z₀, hlens)`; the proof is the same holomorphic-IFT branch construction + monodromy-free
single-branch selection. -/
@[aesop safe]
theorem continues_of_analytic_relation_gen {d : ℕ} (hd : 1 ≤ d)
    {D : Set ℂ} {f : ℂ → ℂ} (hfD : ContinuousOn f D) (z₀ : ℂ)
    {ρ₁ : ℝ} (hρ₁ : 0 < ρ₁)
    (hlens : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ →
      IsPreconnected (D ∩ ball z₀ ρ) ∧ (D ∩ ball z₀ ρ).Nonempty)
    (a : Fin (d+1) → ℂ → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) z₀)
    (hlead : a (Fin.last d) z₀ ≠ 0)
    (rt : Fin d → ℂ) (hinj : Function.Injective rt)
    (hroot : ∀ j, (∑ i : Fin (d+1), C (a i z₀) * X ^ (i:ℕ) : ℂ[X]).IsRoot (rt j))
    (hsimple : ∀ j, (derivative (∑ i : Fin (d+1), C (a i z₀) * X ^ (i:ℕ) : ℂ[X])).eval (rt j) ≠ 0)
    (hrel : ∀ z ∈ D, ∑ i : Fin (d+1), a i z * (f z) ^ (i:ℕ) = 0) :
    ContinuesAcross f D z₀ := by
  classical
  set F : ℂ × ℂ → ℂ := fun q => ∑ i : Fin (d+1), a i q.1 * q.2 ^ (i:ℕ) with hF
  set Qz : ℂ → ℂ[X] := fun z => ∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ) with hQz
  have hfval : ∀ z w : ℂ, F (z, w) = (Qz z).eval w := fun z w => (Qpoly_eval a z w).symm
  have hbranch : ∀ j, ∃ r : ℂ → ℂ, AnalyticAt ℂ r z₀ ∧ r z₀ = rt j ∧
      ∀ᶠ z in 𝓝 z₀, F (z, r z) = 0 := by
    intro j
    have hf_an : AnalyticAt ℂ F (z₀, rt j) := anpoly_analytic a z₀ ha (rt j)
    have h0 : F (z₀, rt j) = 0 := by rw [hfval]; exact hroot j
    have hfw : (fderiv ℂ F (z₀, rt j)) (0, 1) ≠ 0 := by
      rw [hF, partial_w_deriv_an a z₀ ha (rt j)]; exact hsimple j
    exact holo_implicit hf_an h0 hfw
  choose r hr_an hr0 hr_rel using hbranch
  have E1 : ∀ᶠ z in 𝓝 z₀, ∀ j, F (z, r j z) = 0 := eventually_all.mpr hr_rel
  have E2 : ∀ᶠ z in 𝓝 z₀, ∀ i j, i ≠ j → r i z ≠ r j z := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun z h => (h hij).elim)
    · have hne : r i z₀ ≠ r j z₀ := by rw [hr0, hr0]; exact fun h => hij (hinj h)
      have hcij : ContinuousAt (fun z => r i z - r j z) z₀ :=
        ((hr_an i).continuousAt).sub ((hr_an j).continuousAt)
      have hev := hcij.eventually_ne (sub_ne_zero.mpr hne)
      filter_upwards [hev] with z hz; exact fun _ => sub_ne_zero.mp hz
  have E3 : ∀ᶠ z in 𝓝 z₀, a (Fin.last d) z ≠ 0 :=
    (ha (Fin.last d)).continuousAt.eventually_ne hlead
  have E4 : ∀ᶠ z in 𝓝 z₀, ∀ j, ContinuousAt (r j) z := by
    rw [eventually_all]; intro j
    exact (hr_an j).eventually_analyticAt.mono (fun z hz => hz.continuousAt)
  have hcombo := (E1.and (E2.and (E3.and E4)))
  rw [Metric.eventually_nhds_iff] at hcombo
  obtain ⟨ρ₀, hρ₀, hball⟩ := hcombo
  set ρ := min ρ₀ ρ₁ with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ hρ₁
  have hρle1 : ρ ≤ ρ₁ := min_le_right _ _
  set U : Set ℂ := D ∩ ball z₀ ρ with hU
  have hUsub : ∀ z ∈ U, dist z z₀ < ρ₀ :=
    fun z hz => lt_of_lt_of_le (mem_ball.mp hz.2) (min_le_left _ _)
  have hUD : ∀ z ∈ U, z ∈ D := fun z hz => hz.1
  have hpre : IsPreconnected U := (hlens ρ hρ hρle1).1
  have hUne : U.Nonempty := (hlens ρ hρ hρle1).2
  have hh : ContinuousOn f U := hfD.mono (by rw [hU]; exact Set.inter_subset_left)
  have hr_cont : ∀ j, ContinuousOn (r j) U :=
    fun j z hz => ((hball (hUsub z hz)).2.2.2 j).continuousWithinAt
  have hsep_branch : ∀ z ∈ U, ∀ i j, i ≠ j → r i z ≠ r j z :=
    fun z hz => (hball (hUsub z hz)).2.1
  have hmem : ∀ z ∈ U, ∃ j, f z = r j z := by
    intro z hz
    have hlz : a (Fin.last d) z ≠ 0 := (hball (hUsub z hz)).2.2.1
    have hQdeg : (Qz z).natDegree = d := Qpoly_natDegree a z hlz
    have hQne : Qz z ≠ 0 := by intro h; rw [h, natDegree_zero] at hQdeg; omega
    have ha' : Function.Injective (fun j => r j z) :=
      fun i j hij => by_contra fun hne => (hsep_branch z hz i j hne) hij
    have ha'root : ∀ j, (Qz z).IsRoot (r j z) := by
      intro j
      have hh2 := (hball (hUsub z hz)).1 j
      rw [hfval] at hh2; exact hh2
    have hf0root : (Qz z).IsRoot (f z) := by
      have hh3 := hrel z (hUD z hz)
      rw [show (Qz z).IsRoot (f z) = ((Qz z).eval (f z) = 0) from rfl, Qpoly_eval]; exact hh3
    exact root_complete hQne hQdeg ha' ha'root hf0root
  obtain ⟨j, hj⟩ := branch_selection hpre hUne hh hr_cont hsep_branch hmem
  refine ⟨r j, hr_an j, ?_⟩
  rw [eventually_iff]
  refine mem_nhdsWithin.mpr ⟨ball z₀ ρ, isOpen_ball, mem_ball_self hρ, ?_⟩
  intro w hw
  exact (hj w ⟨hw.2, hw.1⟩).symm

/-- **Natural boundary ⟹ no separable analytic relation (general engine).** If `f` is continuous on the
open set `D`, has a **natural boundary** at the frontier point `z₀` (`¬ ContinuesAcross f D z₀`) with a
local preconnected lens, and `∑ᵢ aᵢ(z)·f(z)ⁱ = 0` on `D` with analytic `aᵢ`, nonzero leading coefficient
at `z₀`, and **squarefree** specialization `∑ᵢ aᵢ(z₀)·Yⁱ` there, then `False`. The squarefreeness yields
`d` distinct simple roots (`nodup_roots` + `card_roots_eq_natDegree`), and
`continues_of_analytic_relation_gen` would continue `f` across `z₀`, contradicting the natural boundary.
This is `U0PhiCard.no_separable_analytic_relation` with the domain/boundary abstracted — the engine of
Becker–Bergweiler-style transcendence. -/
@[aesop safe]
theorem no_separable_analytic_relation_gen {d : ℕ} (hd : 1 ≤ d)
    {D : Set ℂ} {f : ℂ → ℂ} (hfD : ContinuousOn f D) (z₀ : ℂ)
    (hnb : ¬ ContinuesAcross f D z₀)
    {ρ₁ : ℝ} (hρ₁ : 0 < ρ₁)
    (hlens : ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ →
      IsPreconnected (D ∩ ball z₀ ρ) ∧ (D ∩ ball z₀ ρ).Nonempty)
    (a : Fin (d+1) → ℂ → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) z₀)
    (hlead : a (Fin.last d) z₀ ≠ 0)
    (hsep : (∑ i : Fin (d+1), C (a i z₀) * X ^ (i:ℕ) : ℂ[X]).Separable)
    (hrel : ∀ z ∈ D, ∑ i : Fin (d+1), a i z * (f z) ^ (i:ℕ) = 0) : False := by
  classical
  set Q₀ : ℂ[X] := ∑ i : Fin (d+1), C (a i z₀) * X ^ (i:ℕ) with hQ₀
  have hQdeg : Q₀.natDegree = d := Qpoly_natDegree a z₀ hlead
  have hQne : Q₀ ≠ 0 := by intro h; rw [h, natDegree_zero] at hQdeg; omega
  have hnodup : Q₀.roots.Nodup := nodup_roots hsep
  have hcard : Q₀.roots.toFinset.card = d := by
    rw [Multiset.toFinset_card_of_nodup hnodup, IsAlgClosed.card_roots_eq_natDegree, hQdeg]
  set s := Q₀.roots.toFinset with hs
  set rt : Fin d → ℂ := fun i => (s.equivFin.symm (finCongr hcard.symm i) : ℂ) with hrt
  have hinj : Function.Injective rt := by
    intro i j hij
    apply (finCongr hcard.symm).injective; apply s.equivFin.symm.injective; exact Subtype.ext hij
  have hroot : ∀ j, Q₀.IsRoot (rt j) := fun j =>
    isRoot_of_mem_roots (Multiset.mem_toFinset.mp (s.equivFin.symm (finCongr hcard.symm j)).2)
  have hsimple : ∀ j, (derivative Q₀).eval (rt j) ≠ 0 := by
    intro j hdx
    obtain ⟨u, v, huv⟩ := hsep
    have hr0 : Q₀.eval (rt j) = 0 := hroot j
    have key := congrArg (Polynomial.eval (rt j)) huv
    rw [eval_add, eval_mul, eval_mul, hr0, hdx, mul_zero, mul_zero, add_zero, eval_one] at key
    exact one_ne_zero key.symm
  exact hnb
    (continues_of_analytic_relation_gen hd hfD z₀ hρ₁ hlens a ha hlead rt hinj hroot hsimple hrel)

/-- **No polynomial relation against a natural-boundary arc (the transcendence reduction).** Let `f` be
continuous on an open `D` and satisfy `∑ᵢ aᵢ(z)·f(z)ⁱ = 0` on `D`, with coefficients `aᵢ` analytic on a
preconnected `Ω` (for a relation over `ℂ[z]` the `aᵢ` are entire, so `Ω` can be all of `ℂ`). Suppose the
specialization is separable at *some* `w ∈ Ω` (automatic when the relation is the minimal polynomial of
`f` over `ℂ(z)`, separable in characteristic 0), and there is an **arc** `S ⊆ Ω` accumulating at an
interior point `z₁`, *every point of which is a natural boundary of `f` carrying a local preconnected
lens*. Then `False`.

This is the engine of Becker–Bergweiler transcendence, with the analytic core isolated: a
squarefree crossing point `z₀ ∈ S` exists (`U0PhiCard.exists_separable_crossing`, off the finite
leading/discriminant locus), and `no_separable_analytic_relation_gen` continues `f` across it against
its natural boundary. The two named deep inputs `hnb`/`hlens` are the φ_b-specific content (the Julia set
`J_b` is a natural boundary of the inverse Böttcher coordinate, with a basin lens at its accessible
points); everything else is the shared algebraic engine. Specialised to `f = u₀`, `D = Ext`, `S` an arc
of the unit circle, `hnb = u0_natural_boundary`, `hlens = lens_preconnected`, this reproves the u₀ case
(`U0PhiCard.u0_phi_card_step3`). -/
@[aesop safe]
theorem no_poly_relation_of_natural_boundary_arc {d : ℕ} (hd : 1 ≤ d)
    {D : Set ℂ} {f : ℂ → ℂ} (hfD : ContinuousOn f D)
    {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (a : Fin (d+1) → ℂ → ℂ) (ha : ∀ i, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a (Fin.last d) w ≠ 0)
    (hsepw : (∑ i : Fin (d+1), C (a i w) * X ^ (i:ℕ) : ℂ[X]).Separable)
    {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) {S : Set ℂ} (hS : S ⊆ Ω)
    (haccum : ∃ᶠ z in 𝓝[≠] z₁, z ∈ S)
    (hnb : ∀ z₀ ∈ S, ¬ ContinuesAcross f D z₀)
    (hlens : ∀ z₀ ∈ S, ∃ ρ₁ : ℝ, 0 < ρ₁ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ →
      IsPreconnected (D ∩ ball z₀ ρ) ∧ (D ∩ ball z₀ ρ).Nonempty)
    (hrel : ∀ z ∈ D, ∑ i : Fin (d+1), a i z * (f z) ^ (i:ℕ) = 0) : False := by
  obtain ⟨z₀, hz₀S, hl₀, hsep₀⟩ :=
    exists_separable_crossing hd hΩc a ha hw hleadw hsepw hz₁ hS haccum
  obtain ⟨ρ₁, hρ₁, hlens₀⟩ := hlens z₀ hz₀S
  exact no_separable_analytic_relation_gen hd hfD z₀ (hnb z₀ hz₀S) hρ₁ hlens₀ a
    (fun i => ha i z₀ (hS hz₀S)) hl₀ hsep₀ hrel

end NaturalBoundaryTranscendence
