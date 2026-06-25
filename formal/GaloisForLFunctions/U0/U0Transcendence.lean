/-
# Transcendence of u₀ as a function on the exterior (Step 3 assembly)

This file assembles the holomorphic-IFT toolkit (`HolomorphicIFT`) and the proven natural boundary
(`U0NaturalBoundary`) into the transcendence of `u₀`: `u₀` satisfies no nonzero polynomial relation
`P(z, u₀(z)) = 0` over `ℂ(z)`.

The argument is the classical "algebraic functions continue across the boundary" — turned against a
natural boundary. Given a *minimal* (hence separable over `ℂ(z)`) relation `P`, the squarefree
specialization `exists_squarefree_specialization` produces a circle point `z₀` at which `P(z₀,·)` has
only simple roots. The holomorphic implicit function theorem (`holo_implicit`) gives `d` analytic root
branches near `z₀`; `root_complete` forces `u₀(z)` to be one of them at each exterior point near `z₀`;
`branch_selection` (over the *preconnected lens* `Ext ∩ ball z₀ ρ`, `lens_preconnected`) pins `u₀` to a
single analytic branch — an analytic continuation of `u₀` across `z₀`, contradicting
`u0_natural_boundary`.

This file currently establishes the geometric input — the lens neighbourhood of a boundary point is
preconnected (star-shaped from a point just outside the circle) — which `branch_selection` consumes.
-/
import GaloisForLFunctions.U0.HolomorphicIFT
import GaloisForLFunctions.U0.U0NaturalBoundary

open Polynomial Filter Topology Metric Complex Set HolomorphicIFT U0 U0NaturalBoundary
open scoped nonZeroDivisors

namespace U0Transcendence

/-- **The lens `{1 < ‖z‖} ∩ ball z₀ ρ` is star-convex from `p = (1+ρ/2)·z₀` (PROVEN), for `ρ ≤ ½`.**
The ball part is convexity; the exterior part `‖(1-t)p + ty‖ > 1` is a `normSq` estimate: writing
`y = z₀ + ζ` (`‖ζ‖ < ρ`, `Re(z̄₀ζ) > -‖ζ‖²/2` from `‖y‖>1`), the combination is `A·z₀ + t·ζ` with
`A = 1+(1-t)ρ/2`, and `normSq = A² + t²‖ζ‖² + 2Atc` decomposes as `1 + (1-t)·(positive) + At·(2c+‖ζ‖²)`,
both correction terms `≥ 0` and never simultaneously zero (the `ρ ≤ ½` budget makes the bracket
strictly positive). -/
theorem lens_starConvex (z₀ : ℂ) (hz₀ : ‖z₀‖ = 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 1/2) :
    StarConvex ℝ (((1:ℝ) + ρ/2) • z₀) ({z : ℂ | 1 < ‖z‖} ∩ ball z₀ ρ) := by
  set p : ℂ := ((1:ℝ) + ρ/2) • z₀ with hp
  have hz₀sq : normSq z₀ = 1 := by rw [Complex.normSq_eq_norm_sq, hz₀]; norm_num
  have hpmem : p ∈ {z : ℂ | 1 < ‖z‖} ∩ ball z₀ ρ := by
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_setOf_eq, hp, norm_smul, Real.norm_eq_abs, hz₀, mul_one]
      rw [abs_of_pos (by linarith)]; linarith
    · simp only [mem_ball, hp, dist_eq_norm]
      rw [show ((1:ℝ) + ρ/2) • z₀ - z₀ = (ρ/2) • z₀ by module, norm_smul, Real.norm_eq_abs, hz₀,
        mul_one, abs_of_pos (by linarith)]; linarith
  rw [starConvex_iff_segment_subset]
  rintro y ⟨hyExt, hyball⟩ x hx
  rw [segment_eq_image] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  have hyE : 1 < ‖y‖ := hyExt
  refine ⟨?_, ?_⟩
  · show (1:ℝ) < ‖(1 - t) • p + t • y‖
    set ζ : ℂ := y - z₀ with hζ
    have hy_eq : y = z₀ + ζ := by rw [hζ]; ring
    set A : ℝ := 1 + (1 - t) * ρ / 2 with hA
    have hcomb : (1 - t) • p + t • y = A • z₀ + t • ζ := by rw [hp, hy_eq, hA]; module
    have hyn : 1 < normSq y := by rw [Complex.normSq_eq_norm_sq]; nlinarith [hyE, sq_nonneg (‖y‖-1)]
    set c : ℝ := (z₀ * (starRingEnd ℂ) ζ).re with hc
    have hnsy : normSq y = 1 + normSq ζ + 2 * c := by rw [hy_eq, Complex.normSq_add, hz₀sq, ← hc]
    have hζρ : normSq ζ < ρ ^ 2 := by
      have hb : ‖ζ‖ < ρ := by rw [hζ, ← dist_eq_norm]; rwa [mem_ball] at hyball
      rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg ζ, hb]
    have hncomb : normSq (A • z₀ + t • ζ) = A^2 + t^2 * normSq ζ + 2 * A * t * c := by
      rw [Complex.real_smul, Complex.real_smul, Complex.normSq_add, Complex.normSq_mul,
        Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_ofReal, hz₀sq]
      have hre : ((A:ℂ) * z₀ * (starRingEnd ℂ) ((t:ℂ) * ζ)).re = A * t * c := by
        rw [map_mul, Complex.conj_ofReal,
          show (A:ℂ) * z₀ * ((t:ℂ) * (starRingEnd ℂ) ζ)
            = ((A*t : ℝ):ℂ) * (z₀ * (starRingEnd ℂ) ζ) by push_cast; ring,
          Complex.re_ofReal_mul, ← hc]
      rw [hre]; ring
    have hA1 : 1 ≤ A := by rw [hA]; nlinarith [ht1]
    have h2c : 0 < 2 * c + normSq ζ := by nlinarith [hnsy, hyn]
    have hbracket : 0 < ρ * (A + 1) / 2 - normSq ζ * t * (1 + ρ / 2) := by
      nlinarith [hζρ, hA1, ht0, ht1, hρ, hρ2, normSq_nonneg ζ,
        mul_nonneg (normSq_nonneg ζ) ht0, mul_le_mul_of_nonneg_left hρ2 hρ.le]
    have key_id : A^2 + t^2 * normSq ζ + 2 * A * t * c
        = 1 + (1 - t) * (ρ * (A + 1) / 2 - normSq ζ * t * (1 + ρ / 2))
          + A * t * (2 * c + normSq ζ) := by rw [hA]; ring
    have hkey : 1 < normSq (A • z₀ + t • ζ) := by
      rw [hncomb, key_id]
      rcases lt_or_eq_of_le ht1 with ht | ht
      · have h1 : 0 < (1 - t) * (ρ * (A + 1) / 2 - normSq ζ * t * (1 + ρ / 2)) :=
          mul_pos (by linarith) hbracket
        nlinarith [h1, mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ A) ht0) h2c.le]
      · subst ht
        nlinarith [mul_pos (show (0:ℝ) < A by linarith) h2c]
    have heq : ‖(1 - t) • p + t • y‖ * ‖(1 - t) • p + t • y‖ = normSq (A • z₀ + t • ζ) := by
      rw [hcomb, Complex.normSq_eq_norm_sq, pow_two]
    have h1 : (1:ℝ) < ‖(1 - t) • p + t • y‖ * ‖(1 - t) • p + t • y‖ := by rw [heq]; exact hkey
    nlinarith [h1, norm_nonneg ((1 - t) • p + t • y)]
  · exact convex_ball z₀ ρ hpmem.2 hyball (by linarith) ht0 (by ring)

/-- **The lens is preconnected (PROVEN).** Star-convex ⟹ path-connected ⟹ connected ⟹ preconnected.
This is the connectivity input `branch_selection` needs to pin `u₀` to one analytic branch on the
exterior side of a boundary crossing point. -/
theorem lens_preconnected (z₀ : ℂ) (hz₀ : ‖z₀‖ = 1) {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : ρ ≤ 1/2) :
    IsPreconnected ({z : ℂ | 1 < ‖z‖} ∩ ball z₀ ρ) := by
  have hmem : ((1:ℝ) + ρ/2) • z₀ ∈ {z : ℂ | 1 < ‖z‖} ∩ ball z₀ ρ := by
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_setOf_eq, norm_smul, Real.norm_eq_abs, hz₀, mul_one]
      rw [abs_of_pos (by linarith)]; linarith
    · simp only [mem_ball, dist_eq_norm]
      rw [show ((1:ℝ) + ρ/2) • z₀ - z₀ = (ρ/2) • z₀ by module, norm_smul, Real.norm_eq_abs, hz₀,
        mul_one, abs_of_pos (by linarith)]; linarith
  exact ((lens_starConvex z₀ hz₀ hρ hρ2).isPathConnected hmem).isConnected.isPreconnected

/-- **The exterior `Ext = {1 < ‖z‖}` is connected (PROVEN).** It is the continuous image of the
connected product `(1,∞) × 𝕊¹` under `(r, w) ↦ r·w` (polar coordinates), since every `z` with
`‖z‖ > 1` is `‖z‖ · (z/‖z‖)`. Connectedness of `Ext` is the domain on which the identity theorem
turns the ring of analytic functions into an integral domain — the engine of the reduction of an
*arbitrary* relation to a separable one. -/
theorem isConnected_Ext : IsConnected Ext := by
  have hprod : IsConnected ((Ioi (1:ℝ)) ×ˢ Metric.sphere (0:ℂ) 1) :=
    isConnected_Ioi.prod
      (isConnected_sphere (by rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]; norm_num)
        0 (by norm_num))
  have hcont : Continuous (fun p : ℝ × ℂ => (p.1 : ℂ) • p.2) := by fun_prop
  have himg := hprod.image _ hcont.continuousOn
  have hset : Ext = (fun p : ℝ × ℂ => (p.1 : ℂ) • p.2) '' ((Ioi (1:ℝ)) ×ˢ Metric.sphere (0:ℂ) 1) := by
    ext z
    simp only [Ext, mem_setOf_eq, Set.mem_image, Set.mem_prod, mem_Ioi, mem_sphere_zero_iff_norm]
    constructor
    · intro hz
      have hz0 : ‖z‖ ≠ 0 := by positivity
      refine ⟨⟨‖z‖, (‖z‖⁻¹ : ℝ) • z⟩, ⟨hz, ?_⟩, ?_⟩
      · show ‖(‖z‖⁻¹ : ℝ) • z‖ = 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), inv_mul_cancel₀ hz0]
      · show (↑‖z‖ : ℂ) • ((‖z‖⁻¹ : ℝ) • z) = z
        rw [Complex.real_smul, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul,
          mul_inv_cancel₀ hz0, Complex.ofReal_one, one_mul]
    · rintro ⟨⟨r, w⟩, ⟨hr, hw⟩, rfl⟩
      show 1 < ‖(↑r : ℂ) • w‖
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, hw, mul_one, abs_of_pos (by linarith)]
      exact hr
  rw [hset]; exact himg

/-- **The ring of analytic functions on `Ext` is an integral domain (PROVEN).** If `g, h` are analytic
on the connected `Ext` and `g·h ≡ 0` there, then `g ≡ 0` or `h ≡ 0`. (If `g(z₁) ≠ 0`, then `g ≠ 0` on
a neighbourhood, forcing `h = 0` there, so `h` vanishes on an open set and the identity theorem
`eqOn_zero_of_preconnected_of_frequently_eq_zero` propagates it to all of `Ext`.) This is the step that
lets a reducible relation `P = A·B` be split: `A(z,u₀) · B(z,u₀) ≡ 0` forces one factor's relation. -/
theorem analytic_domain {g h : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Ext) (hh : AnalyticOnNhd ℂ h Ext)
    (hgh : ∀ z ∈ Ext, g z * h z = 0) :
    (∀ z ∈ Ext, g z = 0) ∨ (∀ z ∈ Ext, h z = 0) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨⟨z₁, hz₁E, hgz₁⟩, ⟨z₂, hz₂E, hhz₂⟩⟩ := hcon
  have hgne : ∀ᶠ z in 𝓝 z₁, g z ≠ 0 := (hg z₁ hz₁E).continuousAt.eventually_ne hgz₁
  have hExt_nhds : Ext ∈ 𝓝 z₁ := isOpen_Ext.mem_nhds hz₁E
  have hzero_near : ∀ᶠ z in 𝓝 z₁, h z = 0 := by
    filter_upwards [hgne, hExt_nhds] with z hgz hzE
    rcases mul_eq_zero.mp (hgh z hzE) with h1 | h2
    · exact absurd h1 hgz
    · exact h2
  have hfreq : ∃ᶠ z in 𝓝[≠] z₁, h z = 0 :=
    (hzero_near.filter_mono nhdsWithin_le_nhds).frequently
  have hEqOn := hh.eqOn_zero_of_preconnected_of_frequently_eq_zero
    isConnected_Ext.isPreconnected hz₁E hfreq
  exact hhz₂ (hEqOn hz₂E)

/-- **The evaluated relation `z ↦ P(z, u₀(z))` is analytic on `Ext` (PROVEN).** It is the bivariate
polynomial `(z,w) ↦ P(z,w)` (analytic, `bivar_analytic`) composed with the analytic map
`z ↦ (z, u₀(z))` (`u₀` analytic on `Ext`). This is the analyticity input that `analytic_domain`
consumes when splitting a reducible relation `Ã(z,u₀)·B̃(z,u₀) ≡ 0`. -/
theorem relation_analytic (P : (Polynomial ℂ)[X]) :
    AnalyticOnNhd ℂ (fun z => P.eval₂ (evalRingHom z) (u0 z)) Ext := by
  intro z hz
  have h2 : AnalyticAt ℂ (fun w : ℂ => (w, u0 w)) z :=
    analyticAt_id.prod (u0_analyticOnNhd_Ext z hz)
  exact (bivar_analytic P (z, u0 z)).comp_of_eq h2 rfl

/-- **A separable relation forces analytic continuation across a crossing point (PROVEN).**
If `P ∈ ℂ[z][Y]` of positive `Y`-degree has `P(z₀,·)` squarefree at a circle point `z₀` (`hsep`) with
the leading coefficient surviving (`hlead`), and `u₀` satisfies the relation `P(z, u₀(z)) = 0` on the
exterior (`hrel`), then `u₀` continues analytically across `z₀`. The full Step-3 engine: the `d` simple
roots of `P(z₀,·)` give `d` analytic branches (`holo_implicit` + `partial_w_deriv`); on a small
exterior lens at `z₀` (preconnected, `lens_preconnected`) every value `u₀(z)` is one of the `d` separated
branch values (`root_complete`), so `branch_selection` pins `u₀` to a single analytic branch `r_j` —
an analytic continuation. -/
theorem continues_of_separable_relation (P : (Polynomial ℂ)[X]) (z₀ : ℂ)
    (hz₀ : ‖z₀‖ = 1)
    (hlead : P.leadingCoeff.eval z₀ ≠ 0)
    (hsep : (P.map (evalRingHom z₀)).Separable)
    (hdeg : 1 ≤ P.natDegree)
    (hrel : ∀ z ∈ Ext, P.eval₂ (evalRingHom z) (u0 z) = 0) :
    ContinuesAcross u0 Ext z₀ := by
  classical
  set f : ℂ × ℂ → ℂ := fun q => P.eval₂ (evalRingHom q.1) q.2 with hf
  set ψ := evalRingHom z₀ with hψ
  set d := P.natDegree with hd
  have hfval : ∀ z w : ℂ, f (z, w) = (P.map (evalRingHom z)).eval w := by
    intro z w; simp only [hf]; rw [eval_map]
  have hsimple : ∀ x : ℂ, (P.map ψ).eval x = 0 → (derivative (P.map ψ)).eval x ≠ 0 := by
    intro x hx hdx
    obtain ⟨u, v, huv⟩ := hsep
    have key := congrArg (Polynomial.eval x) huv
    simp only [eval_add, eval_mul, hx, hdx, mul_zero, eval_one, add_zero] at key
    exact one_ne_zero key.symm
  have hdeg_Pz : (P.map ψ).natDegree = d := natDegree_map_of_leadingCoeff_ne_zero ψ hlead
  have hPz_ne : (P.map ψ) ≠ 0 := by intro h; rw [h, natDegree_zero] at hdeg_Pz; omega
  have hnodup : (P.map ψ).roots.Nodup := nodup_roots hsep
  have hcard : (P.map ψ).roots.toFinset.card = d := by
    rw [Multiset.toFinset_card_of_nodup hnodup, IsAlgClosed.card_roots_eq_natDegree, hdeg_Pz]
  set s := (P.map ψ).roots.toFinset with hs
  set a : Fin d → ℂ := fun i => (s.equivFin.symm (finCongr hcard.symm i) : ℂ) with ha
  have hainj : Function.Injective a := by
    intro i j hij
    apply (finCongr hcard.symm).injective
    apply s.equivFin.symm.injective
    exact Subtype.ext hij
  have haroot : ∀ i, (P.map ψ).eval (a i) = 0 := by
    intro i
    have hmem : a i ∈ (P.map ψ).roots :=
      Multiset.mem_toFinset.mp (s.equivFin.symm (finCongr hcard.symm i)).2
    exact isRoot_of_mem_roots hmem
  have hbranch : ∀ i, ∃ r : ℂ → ℂ, AnalyticAt ℂ r z₀ ∧ r z₀ = a i ∧
      ∀ᶠ z in 𝓝 z₀, f (z, r z) = 0 := by
    intro i
    have hf_an : AnalyticAt ℂ f (z₀, a i) := bivar_analytic P (z₀, a i)
    have h0 : f (z₀, a i) = 0 := by rw [hfval]; exact haroot i
    have hfw : (fderiv ℂ f (z₀, a i)) (0, 1) ≠ 0 := by
      rw [hf, partial_w_deriv P z₀ (a i), ← Polynomial.derivative_map]
      exact hsimple (a i) (haroot i)
    exact holo_implicit hf_an h0 hfw
  choose r hr_an hr0 hr_rel using hbranch
  have E1 : ∀ᶠ z in 𝓝 z₀, ∀ i, f (z, r i z) = 0 := eventually_all.mpr hr_rel
  have E2 : ∀ᶠ z in 𝓝 z₀, ∀ i j, i ≠ j → r i z ≠ r j z := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun z h => (h hij).elim)
    · have hne : r i z₀ ≠ r j z₀ := by rw [hr0, hr0]; exact fun h => hij (hainj h)
      have hcij : ContinuousAt (fun z => r i z - r j z) z₀ :=
        ((hr_an i).continuousAt).sub ((hr_an j).continuousAt)
      have hev := hcij.eventually_ne (sub_ne_zero.mpr hne)
      filter_upwards [hev] with z hz; exact fun _ => sub_ne_zero.mp hz
  have E3 : ∀ᶠ z in 𝓝 z₀, P.leadingCoeff.eval z ≠ 0 :=
    (Polynomial.continuous P.leadingCoeff).continuousAt.eventually_ne hlead
  have E4 : ∀ᶠ z in 𝓝 z₀, ∀ i, ContinuousAt (r i) z := by
    rw [eventually_all]; intro i
    exact (hr_an i).eventually_analyticAt.mono (fun z hz => hz.continuousAt)
  have hcombo := (E1.and (E2.and (E3.and E4)))
  rw [Metric.eventually_nhds_iff] at hcombo
  obtain ⟨ρ₀, hρ₀, hball⟩ := hcombo
  set ρ := min ρ₀ (1/2) with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ (by norm_num)
  have hρ2 : ρ ≤ 1/2 := min_le_right _ _
  set U : Set ℂ := Ext ∩ ball z₀ ρ with hU
  have hUsub : ∀ z ∈ U, dist z z₀ < ρ₀ :=
    fun z hz => lt_of_lt_of_le (mem_ball.mp hz.2) (min_le_left _ _)
  have hUExt : ∀ z ∈ U, z ∈ Ext := fun z hz => hz.1
  have hpre : IsPreconnected U := lens_preconnected z₀ hz₀ hρ hρ2
  have hUne : U.Nonempty := by
    refine ⟨((1:ℝ) + ρ/2) • z₀, ?_, ?_⟩
    · show (1:ℝ) < ‖((1:ℝ) + ρ/2) • z₀‖
      rw [norm_smul, Real.norm_eq_abs, hz₀, mul_one, abs_of_pos (by linarith)]; linarith
    · rw [mem_ball, dist_eq_norm,
        show ((1:ℝ) + ρ/2) • z₀ - z₀ = (ρ/2) • z₀ by module, norm_smul, Real.norm_eq_abs, hz₀,
        mul_one, abs_of_pos (by linarith)]; linarith
  have hh : ContinuousOn u0 U := by
    rw [hU]
    exact u0_differentiableOn_Ext.continuousOn.mono
      (show Ext ∩ ball z₀ ρ ⊆ Ext from Set.inter_subset_left)
  have hr_cont : ∀ i, ContinuousOn (r i) U :=
    fun i z hz => ((hball (hUsub z hz)).2.2.2 i).continuousWithinAt
  have hsep_branch : ∀ z ∈ U, ∀ i j, i ≠ j → r i z ≠ r j z :=
    fun z hz => (hball (hUsub z hz)).2.1
  have hmem : ∀ z ∈ U, ∃ i, u0 z = r i z := by
    intro z hz
    set Q := P.map (evalRingHom z) with hQ
    have hlz : P.leadingCoeff.eval z ≠ 0 := (hball (hUsub z hz)).2.2.1
    have hQdeg : Q.natDegree = d := natDegree_map_of_leadingCoeff_ne_zero _ hlz
    have hQne : Q ≠ 0 := by intro h; rw [h, natDegree_zero] at hQdeg; omega
    have ha' : Function.Injective (fun i => r i z) :=
      fun i j hij => by_contra fun hne => (hsep_branch z hz i j hne) hij
    have ha'root : ∀ i, Q.IsRoot (r i z) := by
      intro i
      have hh2 := (hball (hUsub z hz)).1 i
      rw [hfval] at hh2; exact hh2
    have hu0root : Q.IsRoot (u0 z) := by
      have hh3 := hrel z (hUExt z hz); rw [← eval_map] at hh3; exact hh3
    exact root_complete hQne hQdeg ha' ha'root hu0root
  obtain ⟨j, hj⟩ := branch_selection hpre hUne hh hr_cont hsep_branch hmem
  refine ⟨r j, hr_an j, ?_⟩
  rw [eventually_iff]
  refine mem_nhdsWithin.mpr ⟨ball z₀ ρ, isOpen_ball, mem_ball_self hρ, ?_⟩
  intro w hw
  exact (hj w ⟨hw.2, hw.1⟩).symm

/-- **`u₀` satisfies no separable polynomial relation over `ℂ(z)` (PROVEN).** Capstone of the
analytic side: there is no nonzero `P ∈ ℂ[z][Y]`, separable over `ℂ(z)` and of positive `Y`-degree,
with `P(z, u₀(z)) = 0` on the exterior. Such a `P` would, by `exists_squarefree_specialization`, be
squarefree at some circle point `z₀`, where `continues_of_separable_relation` continues `u₀` across
`z₀` — contradicting the proven natural boundary `u0_natural_boundary`. This is the function-field
transcendence input that the `Transcendental K u₀` hypothesis of `u0_phi_independence` abstracts. -/
theorem u0_separable_no_relation (P : (Polynomial ℂ)[X])
    (hsep : (P.map (algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)))).Separable)
    (hdeg : 1 ≤ P.natDegree)
    (hrel : ∀ z ∈ Ext, P.eval₂ (evalRingHom z) (u0 z) = 0) : False := by
  obtain ⟨z₀, hz₀, hlead, hsep_z₀⟩ := exists_squarefree_specialization hsep hdeg
  exact u0_natural_boundary z₀ hz₀
    (continues_of_separable_relation P z₀ hz₀ hlead hsep_z₀ hdeg hrel)

/-- **`u₀` satisfies NO polynomial relation over `ℂ(z)` on the exterior — full transcendence (PROVEN).**
For every nonzero `P ∈ ℂ[z][Y]` of positive `Y`-degree, the relation `P(z, u₀(z)) = 0` fails somewhere
on `Ext`. Strong induction on `Y`-degree: over the field `ℂ(z)` (characteristic 0), an *irreducible*
`P` is separable, so `u0_separable_no_relation` applies; a *reducible* `P = A·B` clears to
`Ã·B̃ ∈ ℂ[z][Y]` with `Ã(z,u₀)·B̃(z,u₀) ≡ 0` on `Ext`, and the integral-domain property
(`analytic_domain`, from `isConnected_Ext`) forces one factor's relation — a strictly lower-degree
relation, killed by the induction hypothesis. This is the unconditional, function-field form of the
`Transcendental K u₀` input that `u0_phi_independence` abstracts: the natural boundary of `u₀` *is* its
transcendence over `ℂ(z)`. -/
theorem u0_no_relation (P : (Polynomial ℂ)[X]) (hdeg : 1 ≤ P.natDegree)
    (hrel : ∀ z ∈ Ext, P.eval₂ (evalRingHom z) (u0 z) = 0) : False := by
  classical
  set alg := algebraMap (Polynomial ℂ) (FractionRing (Polynomial ℂ)) with halg
  have halginj : Function.Injective alg := IsFractionRing.injective _ _
  have hsmul : ∀ (r : Polynomial ℂ) (p : (FractionRing (Polynomial ℂ))[X]),
      r • p = C (alg r) * p := fun r p => by
    rw [← algebraMap_smul (FractionRing (Polynomial ℂ)) r p, Polynomial.smul_eq_C_mul]
  suffices H : ∀ d : ℕ, ∀ Q : (Polynomial ℂ)[X], Q.natDegree = d → 1 ≤ Q.natDegree →
      (∀ z ∈ Ext, Q.eval₂ (evalRingHom z) (u0 z) = 0) → False by
    exact H P.natDegree P rfl hdeg hrel
  intro d
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro Q hQd hQ1 hQrel
    have hQ0 : Q ≠ 0 := fun h => by rw [h, natDegree_zero] at hQ1; omega
    set Qf := Q.map alg with hQf
    have hQfdeg : Qf.natDegree = Q.natDegree := natDegree_map_eq_of_injective halginj Q
    have hQf0 : Qf ≠ 0 := fun h => hQ0 ((Polynomial.map_eq_zero_iff halginj).mp h)
    by_cases hirr : Irreducible Qf
    · exact u0_separable_no_relation Q hirr.separable hQ1 hQrel
    · have hQf_nu : ¬ IsUnit Qf := fun hu => by
        have h0 := Polynomial.natDegree_eq_zero_of_isUnit hu
        rw [hQfdeg, hQd] at h0; omega
      obtain ⟨A, B, hAnu, hBnu, hPfAB⟩ := (irreducible_or_factor hQf_nu).resolve_left hirr
      have hA0 : A ≠ 0 := by rintro rfl; rw [zero_mul] at hPfAB; exact hQf0 hPfAB
      have hB0 : B ≠ 0 := by rintro rfl; rw [mul_zero] at hPfAB; exact hQf0 hPfAB
      obtain ⟨bA, hbA⟩ := IsLocalization.integerNormalization_map_to_map (Polynomial ℂ)⁰ A
      obtain ⟨bB, hbB⟩ := IsLocalization.integerNormalization_map_to_map (Polynomial ℂ)⁰ B
      set Atil := IsLocalization.integerNormalization (Polynomial ℂ)⁰ A with hAtil
      set Btil := IsLocalization.integerNormalization (Polynomial ℂ)⁰ B with hBtil
      have hbA0 : alg (bA : Polynomial ℂ) ≠ 0 :=
        fun h => (nonZeroDivisors.coe_ne_zero bA) (halginj (by rw [h, map_zero]))
      have hbB0 : alg (bB : Polynomial ℂ) ≠ 0 :=
        fun h => (nonZeroDivisors.coe_ne_zero bB) (halginj (by rw [h, map_zero]))
      have hAtil0 : Atil ≠ 0 := fun h => hA0
        ((IsFractionRing.integerNormalization_eq_zero_iff).mp (by rw [← hAtil, h]))
      have hBtil0 : Btil ≠ 0 := fun h => hB0
        ((IsFractionRing.integerNormalization_eq_zero_iff).mp (by rw [← hBtil, h]))
      have hdegA : 1 ≤ A.natDegree := by
        rcases Nat.eq_zero_or_pos A.natDegree with h | h
        · exfalso; apply hAnu
          rw [Polynomial.eq_C_of_natDegree_eq_zero h]
          refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_)
          intro hc; apply hA0; rw [Polynomial.eq_C_of_natDegree_eq_zero h, hc, map_zero]
        · exact h
      have hdegB : 1 ≤ B.natDegree := by
        rcases Nat.eq_zero_or_pos B.natDegree with h | h
        · exfalso; apply hBnu
          rw [Polynomial.eq_C_of_natDegree_eq_zero h]
          refine Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ?_)
          intro hc; apply hB0; rw [Polynomial.eq_C_of_natDegree_eq_zero h, hc, map_zero]
        · exact h
      have hdegAtil : Atil.natDegree = A.natDegree := by
        have h1 := natDegree_map_eq_of_injective halginj Atil
        rw [hbA, hsmul, Polynomial.natDegree_C_mul hbA0] at h1; omega
      have hdegBtil : Btil.natDegree = B.natDegree := by
        have h1 := natDegree_map_eq_of_injective halginj Btil
        rw [hbB, hsmul, Polynomial.natDegree_C_mul hbB0] at h1; omega
      have hdescent : Atil * Btil = C ((bA : Polynomial ℂ) * bB) * Q := by
        apply Polynomial.map_injective alg halginj
        rw [Polynomial.map_mul, hbA, hbB, hsmul, hsmul, Polynomial.map_mul, Polynomial.map_C,
          map_mul alg, Polynomial.C_mul, ← hQf, hPfAB]
        ring
      have hdegsum : Atil.natDegree + Btil.natDegree = d := by
        have hm := Polynomial.natDegree_mul hAtil0 hBtil0
        rw [hdescent, Polynomial.natDegree_C_mul (mul_ne_zero (nonZeroDivisors.coe_ne_zero bA)
          (nonZeroDivisors.coe_ne_zero bB)), hQd] at hm
        omega
      have heval : ∀ z ∈ Ext, (Atil.eval₂ (evalRingHom z) (u0 z))
          * (Btil.eval₂ (evalRingHom z) (u0 z)) = 0 := by
        intro z hz
        rw [← eval₂_mul, hdescent, eval₂_mul, eval₂_C, hQrel z hz, mul_zero]
      rcases analytic_domain (relation_analytic Atil) (relation_analytic Btil) heval with hAz | hBz
      · exact IH Atil.natDegree (by omega) Atil rfl (by omega) hAz
      · exact IH Btil.natDegree (by omega) Btil rfl (by omega) hBz

/-- **The relation map as a ring homomorphism (PROVEN).** `evalU0 : ℂ[z][Y] →+* (ℂ → ℂ)` sends a
bivariate polynomial `P` to the function `z ↦ P(z, u₀(z))` (`Y ↦ u₀`, coefficients evaluated at `z`).
Packaging the evaluation as a genuine ring hom is the clean *interface* through which a carrier field
`M` (the joint `M ⊇ ℂ(z)` hosting both `u₀` and `φ_b`) consumes the transcendence: a `ℂ(z)`-algebra
relation on the image of `u₀` pulls back along `evalU0` to a relation on `Ext`. -/
noncomputable def evalU0 : (Polynomial ℂ)[X] →+* (ℂ → ℂ) :=
  eval₂RingHom (Pi.ringHom (fun z => Polynomial.evalRingHom z)) u0

/-- `evalU0 P` evaluated at `z` is the relation `P(z, u₀(z))` (PROVEN). -/
theorem evalU0_apply (P : (Polynomial ℂ)[X]) (z : ℂ) :
    evalU0 P z = P.eval₂ (evalRingHom z) (u0 z) := by
  have hcomp : (Pi.evalRingHom (fun _ : ℂ => ℂ) z).comp evalU0
      = eval₂RingHom (evalRingHom z) (u0 z) := by
    apply Polynomial.ringHom_ext
    · intro p
      simp only [RingHom.comp_apply, evalU0, coe_eval₂RingHom, eval₂_C, Pi.evalRingHom_apply,
        Pi.ringHom_apply]
    · simp only [RingHom.comp_apply, evalU0, coe_eval₂RingHom, eval₂_X, Pi.evalRingHom_apply]
  have h := DFunLike.congr_fun hcomp P
  simpa only [RingHom.comp_apply, Pi.evalRingHom_apply, coe_eval₂RingHom] using h

/-- **Transcendence in ring-hom form (PROVEN).** The relation ring hom `evalU0` has *trivial kernel on
`Ext`* for positive-degree polynomials: no nonzero `P ∈ ℂ[z][Y]` of positive `Y`-degree has
`evalU0 P ≡ 0` on the exterior. This is `u0_no_relation` stated through the interface. -/
theorem u0_no_relation_ringHom (P : (Polynomial ℂ)[X]) (hdeg : 1 ≤ P.natDegree)
    (hrel : ∀ z ∈ Ext, evalU0 P z = 0) : False := by
  apply u0_no_relation P hdeg
  intro z hz; rw [← evalU0_apply]; exact hrel z hz

/-! ## Concrete carrier: `u₀` is transcendental over `ℂ(z)` (discharges `Transcendental K u₀`) -/

theorem two_mem_Ext : (2:ℂ) ∈ Ext := by
  simp only [Ext, Set.mem_setOf_eq]; rw [Complex.norm_ofNat]; norm_num

def AnSub : Subring (Germ (𝓝 (2:ℂ)) ℂ) where
  carrier := {g | ∃ f : ℂ → ℂ, (↑f = g) ∧ AnalyticAt ℂ f 2}
  mul_mem' := by rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩; exact ⟨f * g, rfl, hf.mul hg⟩
  one_mem' := ⟨1, rfl, analyticAt_const⟩
  add_mem' := by rintro _ _ ⟨f, rfl, hf⟩ ⟨g, rfl, hg⟩; exact ⟨f + g, rfl, hf.add hg⟩
  zero_mem' := ⟨0, rfl, analyticAt_const⟩
  neg_mem' := by rintro _ ⟨f, rfl, hf⟩; exact ⟨-f, rfl, hf.neg⟩

theorem AnSub_coe_eq_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 2) :
    (⟨(f : Germ (𝓝 (2:ℂ)) ℂ), ⟨f, rfl, hf⟩⟩ : AnSub) = 0 ↔ ∀ᶠ z in 𝓝 (2:ℂ), f z = 0 := by
  rw [← Subtype.coe_inj, ZeroMemClass.coe_zero,
    show (0 : Germ (𝓝 (2:ℂ)) ℂ) = ((0:ℂ→ℂ):Germ _ ℂ) from rfl, Germ.coe_eq]; rfl

instance : Nontrivial AnSub := by
  refine ⟨0, 1, ?_⟩
  rw [Ne, ← Subtype.coe_inj, ZeroMemClass.coe_zero, OneMemClass.coe_one,
    show (0 : Germ (𝓝 (2:ℂ)) ℂ) = ((0:ℂ→ℂ):Germ _ ℂ) from rfl,
    show (1 : Germ (𝓝 (2:ℂ)) ℂ) = ((1:ℂ→ℂ):Germ _ ℂ) from rfl, Germ.coe_eq]
  intro h; have := h.self_of_nhds; simp at this

instance : NoZeroDivisors AnSub := by
  refine ⟨?_⟩
  rintro ⟨a, fa, rfl, hfa⟩ ⟨b, fb, rfl, hfb⟩ hab
  rw [← Subtype.coe_inj, MulMemClass.coe_mul, ZeroMemClass.coe_zero,
    show (0 : Germ (𝓝 (2:ℂ)) ℂ) = ((0:ℂ→ℂ):Germ _ ℂ) from rfl, ← Germ.coe_mul, Germ.coe_eq] at hab
  rcases hfa.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact Or.inl ((AnSub_coe_eq_zero hfa).mpr h)
  · refine Or.inr ((AnSub_coe_eq_zero hfb).mpr ?_)
    have hpunct : ∀ᶠ z in 𝓝[≠] (2:ℂ), fb z = 0 := by
      filter_upwards [h, hab.filter_mono nhdsWithin_le_nhds] with z hfaz hprod
      exact (mul_eq_zero.mp hprod).resolve_left hfaz
    rcases hfb.eventually_eq_zero_or_eventually_ne_zero with hfb0 | hfbne
    · exact hfb0
    · exact absurd ((hpunct.and hfbne).exists.choose_spec.1)
        ((hpunct.and hfbne).exists.choose_spec.2)

instance : IsDomain AnSub :=
  { toIsCancelMulZero := NoZeroDivisors.to_isCancelMulZero AnSub
    toNontrivial := inferInstance }

theorem polyAnalytic (p : Polynomial ℂ) (z₀ : ℂ) : AnalyticAt ℂ (fun z => p.eval z) z₀ := by
  have : (fun z => p.eval z) = fun z => ∑ i ∈ Finset.range (p.natDegree+1), p.coeff i * z^i := by
    funext z; rw [Polynomial.eval_eq_sum_range]
  rw [this]
  exact Finset.analyticAt_fun_sum _ (fun i _ => analyticAt_const.mul (analyticAt_id.pow i))

noncomputable def polyToGerm : (Polynomial ℂ) →+* AnSub :=
  RingHom.codRestrict ((Germ.coeRingHom (𝓝 (2:ℂ))).comp
    (Pi.ringHom (fun z => Polynomial.evalRingHom z))) AnSub
    (fun p => ⟨fun z => p.eval z, rfl, polyAnalytic p 2⟩)

noncomputable instance : Algebra (Polynomial ℂ) AnSub := polyToGerm.toAlgebra

noncomputable def u0Germ : AnSub :=
  ⟨(u0 : Germ (𝓝 (2:ℂ)) ℂ), ⟨u0, rfl, u0_analyticOnNhd_Ext 2 two_mem_Ext⟩⟩

theorem subtype_aeval_u0Germ (P : (Polynomial ℂ)[X]) :
    (AnSub.subtype) (aeval u0Germ P) = ((evalU0 P : ℂ → ℂ) : Germ (𝓝 (2:ℂ)) ℂ) := by
  have lhs : (AnSub.subtype) (aeval u0Germ P)
      = eval₂ ((Germ.coeRingHom (𝓝 (2:ℂ))).comp (Pi.ringHom (fun z => Polynomial.evalRingHom z)))
          (u0 : Germ (𝓝 (2:ℂ)) ℂ) P := by
    rw [aeval_def, hom_eval₂, RingHom.algebraMap_toAlgebra]; rfl
  have rhs : ((evalU0 P : ℂ → ℂ) : Germ (𝓝 (2:ℂ)) ℂ)
      = eval₂ ((Germ.coeRingHom (𝓝 (2:ℂ))).comp (Pi.ringHom (fun z => Polynomial.evalRingHom z)))
          (u0 : Germ (𝓝 (2:ℂ)) ℂ) P := by
    show Germ.coeRingHom (𝓝 (2:ℂ))
        (eval₂ (Pi.ringHom (fun z => Polynomial.evalRingHom z)) u0 P) = _
    rw [hom_eval₂]; rfl
  rw [lhs, rhs]

theorem u0Germ_transcendental_polyRing : Transcendental (Polynomial ℂ) u0Germ := by
  rw [transcendental_iff]
  intro P hP
  have hgerm : ((evalU0 P : ℂ → ℂ) : Germ (𝓝 (2:ℂ)) ℂ) = 0 := by
    rw [← subtype_aeval_u0Germ, hP, map_zero]
  have hnear : ∀ᶠ z in 𝓝 (2:ℂ), evalU0 P z = 0 := by
    rwa [show (0:Germ (𝓝 (2:ℂ)) ℂ) = ((0:ℂ→ℂ):Germ _ ℂ) from rfl, Germ.coe_eq] at hgerm
  have han : AnalyticOnNhd ℂ (evalU0 P) Ext := by
    have he : (evalU0 P) = fun z => P.eval₂ (evalRingHom z) (u0 z) := funext (evalU0_apply P)
    rw [he]; exact relation_analytic P
  have hExt : ∀ z ∈ Ext, evalU0 P z = 0 := fun z hz =>
    han.eqOn_zero_of_preconnected_of_frequently_eq_zero isConnected_Ext.isPreconnected two_mem_Ext
      ((hnear.filter_mono nhdsWithin_le_nhds).frequently) hz
  rcases Nat.eq_zero_or_pos P.natDegree with hd0 | hd1
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hd0]
    have hc : ∀ z ∈ Ext, (P.coeff 0).IsRoot z := by
      intro z hz
      have hz2 := hExt z hz
      rw [Polynomial.eq_C_of_natDegree_eq_zero hd0, evalU0_apply, eval₂_C, coe_evalRingHom] at hz2
      exact hz2
    have hinf : {x | (P.coeff 0).IsRoot x}.Infinite :=
      (isConnected_Ext.isPreconnected.infinite_of_nontrivial
        ⟨2, two_mem_Ext, 3, by simp only [Ext, Set.mem_setOf_eq]; rw [Complex.norm_ofNat]; norm_num,
          by norm_num⟩).mono (fun z hz => hc z hz)
    rw [Polynomial.eq_zero_of_infinite_isRoot _ hinf, map_zero]
  · exact (u0_no_relation_ringHom P hd1 hExt).elim




theorem transcendental_algHom_inj {R A B : Type*} [CommRing R] [Ring A] [Ring B] [Algebra R A]
    [Algebra R B] (f : A →ₐ[R] B) (hf : Function.Injective f) {x : A}
    (h : Transcendental R x) : Transcendental R (f x) := by
  intro halg
  obtain ⟨p, hp0, hp⟩ := halg
  exact h ⟨p, hp0, hf (by rw [map_zero, ← aeval_algHom_apply]; exact hp)⟩

/-- The carrier field: fraction field of the analytic-germ domain. -/
noncomputable abbrev AnField := FractionRing AnSub

/-- `u₀` in the carrier field, transcendental over `ℂ[z]`. -/
noncomputable def u0Field : AnField := algebraMap AnSub AnField u0Germ

theorem u0Field_transcendental_polyRing : Transcendental (Polynomial ℂ) u0Field :=
  transcendental_algHom_inj (IsScalarTower.toAlgHom (Polynomial ℂ) AnSub AnField)
    (FaithfulSMul.algebraMap_injective AnSub AnField) u0Germ_transcendental_polyRing

theorem polyToGerm_injective : Function.Injective polyToGerm := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have hg : ((fun z => p.eval z : ℂ → ℂ) : Germ (𝓝 (2:ℂ)) ℂ) = 0 := congrArg Subtype.val hp
  rw [show (0:Germ (𝓝 (2:ℂ)) ℂ) = ((0:ℂ→ℂ):Germ _ ℂ) from rfl, Germ.coe_eq] at hg
  apply Polynomial.eq_zero_of_infinite_isRoot
  apply Set.Infinite.mono (s := {z | p.eval z = 0})
  · intro z hz; exact hz
  · obtain ⟨ε, hε, hsub⟩ := Metric.eventually_nhds_iff.mp hg
    apply Set.Infinite.mono (s := Metric.ball (2:ℂ) ε)
    · intro z hz; exact hsub (Metric.mem_ball.mp hz)
    · refine (convex_ball (2:ℂ) ε).isPreconnected.infinite_of_nontrivial
        ⟨2, Metric.mem_ball_self hε, 2 + (ε/2 : ℝ), ?_, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm,
          show (2 : ℂ) + (ε/2 : ℝ) - 2 = ((ε/2 : ℝ) : ℂ) by ring, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by linarith : (0:ℝ) < ε/2)]; linarith
      · have hne : ((ε/2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by positivity)
        intro h; exact hne (by linear_combination -h)

instance : FaithfulSMul (Polynomial ℂ) AnField :=
  (faithfulSMul_iff_algebraMap_injective (Polynomial ℂ) AnField).mpr (by
    rw [IsScalarTower.algebraMap_eq (Polynomial ℂ) AnSub AnField]
    exact (FaithfulSMul.algebraMap_injective AnSub AnField).comp polyToGerm_injective)

noncomputable instance : Algebra (FractionRing (Polynomial ℂ)) AnField :=
  FractionRing.liftAlgebra (Polynomial ℂ) AnField

instance : IsScalarTower (Polynomial ℂ) (FractionRing (Polynomial ℂ)) AnField :=
  FractionRing.isScalarTower_liftAlgebra (Polynomial ℂ) AnField

/-- **u₀ is transcendental over the field `ℂ(z) = FractionRing ℂ[z]` (PROVEN).** The concrete discharge
of the `Transcendental K u₀` hypothesis: `u₀`, as an element of the carrier field `AnField`
(fractions of analytic germs at `2 ∈ Ext`), is transcendental over `ℂ(z)`. This is `u0_no_relation`
carried through the analytic-germ domain into a genuine `ℂ(z)`-algebra, then transferred from the
polynomial ring to its fraction field via `IsFractionRing.isAlgebraic_iff`. -/
theorem u0Field_transcendental : Transcendental (FractionRing (Polynomial ℂ)) u0Field := by
  rw [Transcendental,
    ← IsFractionRing.isAlgebraic_iff (Polynomial ℂ) (FractionRing (Polynomial ℂ)) AnField]
  exact u0Field_transcendental_polyRing

end U0Transcendence
