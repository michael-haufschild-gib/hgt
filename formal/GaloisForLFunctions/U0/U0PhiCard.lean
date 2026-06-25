/-
# The card's connected proof: Step 3 (algebraic-IFT continuation against the natural boundary)

`docs/drafts/pipeline/2-fully-proven/new/u0-phi-independence.md` proves `u₀ ⟂ φ_b` (connected case) by
a route that is **not** the `q62_mixed` monodromy reduction used in `U0PhiIndep.lean`. The card's proof:

1. φ_b extends single-valuedly analytically through the basin `Ω_b` (connected case).
2. The basin crosses the unit circle (a capacity / energy argument: `cap(K_b)=1` forces `K_b` not to
   contain a continuum strictly outside the disk, so `Ω_b ∩ {|z|=1}` contains an arc).
3. A nonzero relation `P(z, u₀(z), φ_b(z)) = 0` of positive `U`-degree gives the minimal polynomial `F`
   of `u₀` over `ℂ(b)(z, φ_b)`; on `Ω_b`, `φ_b` is analytic, so `F`'s coefficients are analytic, with a
   discrete bad set (leading coeff / discriminant). At a crossing point `z₀ ∈ Ω_b ∩ {|z|=1}` off the bad
   set, `F(z₀,·)` is squarefree; the holomorphic implicit function theorem continues `u₀` across `z₀` —
   contradicting the **natural boundary** of `u₀`.

This file formalizes the u₀-side core: **Step 3** as `continues_of_analytic_relation`, the algebraic-IFT
continuation for a relation whose `Y`-coefficients are *analytic functions* (here built from `φ_b`),
generalizing `U0Transcendence.continues_of_separable_relation` from polynomial to analytic coefficients.
The remaining card inputs — φ_b analytic on a basin crossing the circle (Steps 1–2), and the squarefree
crossing point — are exactly the hypotheses fed in (`a`, `ha`, `hlead`, `rt`, `hroot`, `hsimple`), and
are the Böttcher-side analytic content. With them, `no_analytic_relation` is the card's Step-3
contradiction outright.
-/
import GaloisForLFunctions.U0.U0Transcendence

open Polynomial Filter Topology Complex Metric Set HolomorphicIFT ContinuousLinearMap
open U0 U0NaturalBoundary U0Transcendence

namespace U0PhiCard

/-- The relation `f(z,w) = ∑ᵢ aᵢ(z)·wⁱ` with analytic coefficients is analytic (the analytic-coefficient
analogue of `bivar_analytic`). -/
@[aesop safe]
theorem anpoly_analytic {d : ℕ} (a : Fin (d+1) → ℂ → ℂ) (z₀ : ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) z₀) (w₀ : ℂ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => ∑ i : Fin (d+1), a i q.1 * q.2 ^ (i : ℕ)) (z₀, w₀) :=
  Finset.analyticAt_fun_sum _
    (fun i _ => ((ha i).comp analyticAt_fst).mul (analyticAt_snd.pow (i : ℕ)))

/-- `(∑ᵢ C(aᵢ z)·Xⁱ).eval w = ∑ᵢ aᵢ(z)·wⁱ`: the specialized polynomial evaluates to the relation. -/
@[aesop safe]
theorem Qpoly_eval {d : ℕ} (a : Fin (d+1) → ℂ → ℂ) (z w : ℂ) :
    (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ) : ℂ[X]).eval w = ∑ i : Fin (d+1), a i z * w ^ (i:ℕ) := by
  simp only [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]

/-- The specialized polynomial `∑ᵢ C(aᵢ z)·Xⁱ` has degree exactly `d` when the top coefficient
`a_d(z) ≠ 0`. -/
@[aesop safe]
theorem Qpoly_natDegree {d : ℕ} (a : Fin (d+1) → ℂ → ℂ) (z : ℂ) (hlead : a (Fin.last d) z ≠ 0) :
    (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ) : ℂ[X]).natDegree = d := by
  have hcoeff : (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ) : ℂ[X]).coeff d = a (Fin.last d) z := by
    rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (Fin.last d)]
    · rw [coeff_C_mul, coeff_X_pow, Fin.val_last]; simp
    · intro i _ hi
      rw [coeff_C_mul, coeff_X_pow,
        if_neg (fun h => hi (Fin.ext (h.symm.trans (Fin.val_last d).symm))), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hle : (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ) : ℂ[X]).natDegree ≤ d := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    refine (natDegree_C_mul_le _ _).trans ?_
    rw [natDegree_X_pow]; exact Nat.le_of_lt_succ i.2
  exact le_antisymm hle (Polynomial.le_natDegree_of_ne_zero (by rw [hcoeff]; exact hlead))

/-- The partial `w`-derivative of `f(z,w) = ∑ᵢ aᵢ(z)·wⁱ` in the `(0,1)` direction is the polynomial
`w`-derivative of the specialized polynomial — the simple-root quantity `holo_implicit` consumes. -/
@[aesop safe]
theorem partial_w_deriv_an {d : ℕ} (a : Fin (d+1) → ℂ → ℂ) (z₀ : ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) z₀) (w₀ : ℂ) :
    (fderiv ℂ (fun q : ℂ × ℂ => ∑ i : Fin (d+1), a i q.1 * q.2 ^ (i:ℕ)) (z₀, w₀)) (0, 1)
    = (derivative (∑ i : Fin (d+1), C (a i z₀) * X ^ (i:ℕ) : ℂ[X])).eval w₀ := by
  set f : ℂ × ℂ → ℂ := fun q => ∑ i : Fin (d+1), a i q.1 * q.2 ^ (i:ℕ) with hf
  set Q₀ : ℂ[X] := ∑ i : Fin (d+1), C (a i z₀) * X ^ (i:ℕ) with hQ₀
  have hfdiff : HasFDerivAt f (fderiv ℂ f (z₀, w₀)) (z₀, w₀) :=
    (anpoly_analytic a z₀ ha w₀).differentiableAt.hasFDerivAt
  have hι : HasFDerivAt (fun w : ℂ => (z₀, w))
      ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ)) w₀ :=
    (hasFDerivAt_const z₀ w₀).prodMk (hasFDerivAt_id w₀)
  have hcomp : HasFDerivAt (fun w => f (z₀, w))
      ((fderiv ℂ f (z₀, w₀)).comp ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ))) w₀ :=
    hfdiff.comp w₀ hι
  have hpoly : HasDerivAt (fun w => f (z₀, w)) ((derivative Q₀).eval w₀) w₀ := by
    have hrw : (fun w => f (z₀, w)) = fun w => Q₀.eval w := by
      funext w; rw [hf, hQ₀]; simp only []; rw [Qpoly_eval]
    rw [hrw]; exact Polynomial.hasDerivAt Q₀ w₀
  have huniq := hcomp.unique hpoly.hasFDerivAt
  have hev := ContinuousLinearMap.ext_iff.mp huniq 1
  simpa using hev

/-- **The card's Step 3 (PROVEN).** A relation `∑ᵢ aᵢ(z)·u₀(z)ⁱ = 0` on `Ext`, with coefficients `aᵢ`
analytic at a circle point `z₀`, top coefficient `a_d(z₀) ≠ 0`, positive degree `d ≥ 1`, and the
specialization `∑ᵢ C(aᵢ z₀)·Xⁱ` having `d` distinct *simple* roots `rt` (the squarefree crossing the
card secures by avoiding the discrete discriminant locus), forces `u₀` to continue analytically across
`z₀`. The `d` simple roots give `d` analytic branches (`holo_implicit` + `partial_w_deriv_an`);
`root_complete` pins `u₀(z)` to the branch set for exterior `z` near `z₀`; `branch_selection` over the
preconnected lens selects one analytic branch — the continuation. This is the analytic-coefficient
generalization of `continues_of_separable_relation`. -/
@[aesop safe]
theorem continues_of_analytic_relation {d : ℕ} (hd : 1 ≤ d) (z₀ : ℂ) (hz₀ : ‖z₀‖ = 1)
    (a : Fin (d+1) → ℂ → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) z₀)
    (hlead : a (Fin.last d) z₀ ≠ 0)
    (rt : Fin d → ℂ) (hinj : Function.Injective rt)
    (hroot : ∀ j, (∑ i : Fin (d+1), C (a i z₀) * X ^ (i:ℕ) : ℂ[X]).IsRoot (rt j))
    (hsimple : ∀ j, (derivative (∑ i : Fin (d+1), C (a i z₀) * X ^ (i:ℕ) : ℂ[X])).eval (rt j) ≠ 0)
    (hrel : ∀ z ∈ Ext, ∑ i : Fin (d+1), a i z * (u0 z) ^ (i:ℕ) = 0) :
    ContinuesAcross u0 Ext z₀ := by
  classical
  set f : ℂ × ℂ → ℂ := fun q => ∑ i : Fin (d+1), a i q.1 * q.2 ^ (i:ℕ) with hf
  set Qz : ℂ → ℂ[X] := fun z => ∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ) with hQz
  have hfval : ∀ z w : ℂ, f (z, w) = (Qz z).eval w := fun z w => (Qpoly_eval a z w).symm
  have hbranch : ∀ j, ∃ r : ℂ → ℂ, AnalyticAt ℂ r z₀ ∧ r z₀ = rt j ∧
      ∀ᶠ z in 𝓝 z₀, f (z, r z) = 0 := by
    intro j
    have hf_an : AnalyticAt ℂ f (z₀, rt j) := anpoly_analytic a z₀ ha (rt j)
    have h0 : f (z₀, rt j) = 0 := by rw [hfval]; exact hroot j
    have hfw : (fderiv ℂ f (z₀, rt j)) (0, 1) ≠ 0 := by
      rw [hf, partial_w_deriv_an a z₀ ha (rt j)]; exact hsimple j
    exact holo_implicit hf_an h0 hfw
  choose r hr_an hr0 hr_rel using hbranch
  have E1 : ∀ᶠ z in 𝓝 z₀, ∀ j, f (z, r j z) = 0 := eventually_all.mpr hr_rel
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
  have hr_cont : ∀ j, ContinuousOn (r j) U :=
    fun j z hz => ((hball (hUsub z hz)).2.2.2 j).continuousWithinAt
  have hsep_branch : ∀ z ∈ U, ∀ i j, i ≠ j → r i z ≠ r j z :=
    fun z hz => (hball (hUsub z hz)).2.1
  have hmem : ∀ z ∈ U, ∃ j, u0 z = r j z := by
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
    have hu0root : (Qz z).IsRoot (u0 z) := by
      have hh3 := hrel z (hUExt z hz)
      rw [show (Qz z).IsRoot (u0 z) = ((Qz z).eval (u0 z) = 0) from rfl, Qpoly_eval]; exact hh3
    exact root_complete hQne hQdeg ha' ha'root hu0root
  obtain ⟨j, hj⟩ := branch_selection hpre hUne hh hr_cont hsep_branch hmem
  refine ⟨r j, hr_an j, ?_⟩
  rw [eventually_iff]
  refine mem_nhdsWithin.mpr ⟨ball z₀ ρ, isOpen_ball, mem_ball_self hρ, ?_⟩
  intro w hw
  exact (hj w ⟨hw.2, hw.1⟩).symm

/-- **The card's Step-3 contradiction (PROVEN).** No such analytic-coefficient relation exists: the
continuation `continues_of_analytic_relation` provides would cross the natural boundary of `u₀`. This
is the connected-case `u₀ ⟂ φ_b` conclusion once Steps 1–2 (φ_b analytic on a basin meeting the circle,
squarefree crossing) supply `a`, `hlead`, `rt`, `hroot`, `hsimple` — the Böttcher-side analytic inputs. -/
@[aesop safe]
theorem no_analytic_relation {d : ℕ} (hd : 1 ≤ d) (z₀ : ℂ) (hz₀ : ‖z₀‖ = 1)
    (a : Fin (d+1) → ℂ → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) z₀)
    (hlead : a (Fin.last d) z₀ ≠ 0)
    (rt : Fin d → ℂ) (hinj : Function.Injective rt)
    (hroot : ∀ j, (∑ i : Fin (d+1), C (a i z₀) * X ^ (i:ℕ) : ℂ[X]).IsRoot (rt j))
    (hsimple : ∀ j, (derivative (∑ i : Fin (d+1), C (a i z₀) * X ^ (i:ℕ) : ℂ[X])).eval (rt j) ≠ 0)
    (hrel : ∀ z ∈ Ext, ∑ i : Fin (d+1), a i z * (u0 z) ^ (i:ℕ) = 0) : False :=
  u0_natural_boundary z₀ hz₀
    (continues_of_analytic_relation hd z₀ hz₀ a ha hlead rt hinj hroot hsimple hrel)

/-- **The card's Step 3, in the card's own form (PROVEN).** Takes the *separability* of the
specialization `∑ᵢ C(aᵢ z₀)·Xⁱ` at the crossing point `z₀` — exactly what the card secures by passing
to the minimal polynomial `F` of `u₀` over `ℂ(z,φ_b)` (separable in characteristic 0) and choosing `z₀`
off the discriminant locus — and concludes no relation exists. The `d` distinct simple roots are
extracted from separability (`nodup_roots` + `IsAlgClosed.card_roots_eq_natDegree`), then fed to
`no_analytic_relation`. This is the connected-case `u₀ ⟂ φ_b` conclusion modulo the Böttcher inputs:
`aᵢ` analytic (φ_b analytic on the basin, Step 1), a circle crossing `z₀` in the basin (the capacity
argument, Step 2), and separability of the specialization there. -/
@[aesop safe]
theorem no_separable_analytic_relation {d : ℕ} (hd : 1 ≤ d) (z₀ : ℂ) (hz₀ : ‖z₀‖ = 1)
    (a : Fin (d+1) → ℂ → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) z₀)
    (hlead : a (Fin.last d) z₀ ≠ 0)
    (hsep : (∑ i : Fin (d+1), C (a i z₀) * X ^ (i:ℕ) : ℂ[X]).Separable)
    (hrel : ∀ z ∈ Ext, ∑ i : Fin (d+1), a i z * (u0 z) ^ (i:ℕ) = 0) : False := by
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
  exact no_analytic_relation hd z₀ hz₀ a ha hlead rt hinj hroot hsimple hrel

/-- **Generic point off a discrete bad set (the card's crossing-point choice, PROVEN).** If `g` is
analytic and not identically zero on a preconnected open `Ω`, and a subset `S ⊆ Ω` accumulates at some
`z₁ ∈ Ω` (e.g. an arc of the unit circle inside the basin), then `g` is nonzero somewhere on `S` —
vanishing on all of `S` would force `g ≡ 0` on `Ω` by the identity theorem. The card uses this to pick
a crossing point `z₀ ∈ Ω ∩ {|z|=1}` off the discrete zero locus of the leading coefficient and
discriminant of the minimal polynomial of `u₀` over `ℂ(z,φ_b)`. -/
@[aesop safe]
theorem exists_nonzero_on_accumulating {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g Ω) {w : ℂ} (hw : w ∈ Ω) (hgw : g w ≠ 0)
    {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) {S : Set ℂ} (hS : S ⊆ Ω)
    (haccum : ∃ᶠ z in 𝓝[≠] z₁, z ∈ S) :
    ∃ z₀ ∈ S, g z₀ ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hfreq : ∃ᶠ z in 𝓝[≠] z₁, g z = 0 := haccum.mono (fun z hz => hcon z hz)
  have heq := hg.eqOn_zero_of_preconnected_of_frequently_eq_zero hΩc hz₁ hfreq
  exact hgw (heq hw)

/-- A nonzero resultant of `Q` with its derivative makes `Q` separable — the squarefree criterion
(`resultant(Q,Q') ≠ 0 ⟺ Q, Q'` coprime over the field `ℂ`). At the crossing point `z₀`, this turns the
non-vanishing of the resultant of the minimal polynomial's specialization (secured by
`exists_nonzero_on_accumulating` applied to the resultant — an analytic function of `z`, since it is the
Sylvester determinant of the analytic coefficients) into the `hsep` hypothesis of
`no_separable_analytic_relation`. -/
@[aesop safe]
theorem separable_of_resultant_ne {Q : ℂ[X]} (hQ : Q ≠ 0)
    (hres : resultant Q (derivative Q) ≠ 0) : Q.Separable := by
  rw [Polynomial.Separable]
  by_contra hnc
  exact hres (by rw [resultant_eq_zero_iff]; exact ⟨Or.inl hQ, hnc⟩)

/-- The determinant of a matrix whose entries depend analytically on a parameter is analytic
(`det = ∑_σ sign σ ∏ entries`, a finite sum of products of analytic entries). -/
@[aesop safe]
theorem analyticAt_matrix_det {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℂ → Matrix ι ι ℂ} {z₀ : ℂ}
    (hM : ∀ i j, AnalyticAt ℂ (fun z => M z i j) z₀) :
    AnalyticAt ℂ (fun z => (M z).det) z₀ := by
  have heq : (fun z => (M z).det)
      = fun z => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M z (σ i) i := by
    funext z; rw [Matrix.det_apply]
    exact Finset.sum_congr rfl (fun σ _ => by rw [Units.smul_def, zsmul_eq_mul])
  rw [heq]
  exact Finset.analyticAt_fun_sum _
    (fun σ _ => analyticAt_const.mul (Finset.analyticAt_fun_prod _ (fun i _ => hM (σ i) i)))

/-- The `k`-th coefficient of the specialized polynomial `∑ᵢ C(aᵢ z)·Xⁱ` is analytic in `z`. -/
@[aesop safe]
theorem Qz_coeff_analytic {d : ℕ} (a : Fin (d+1) → ℂ → ℂ) (z₀ : ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) z₀) (k : ℕ) :
    AnalyticAt ℂ (fun z => (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ) : ℂ[X]).coeff k) z₀ := by
  have heq : (fun z => (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ) : ℂ[X]).coeff k)
      = fun z => ∑ i : Fin (d+1), a i z * ((X ^ (i:ℕ) : ℂ[X]).coeff k) := by
    funext z
    rw [Polynomial.finsetSum_coeff]
    exact Finset.sum_congr rfl (fun i _ => by rw [coeff_C_mul])
  rw [heq]
  exact Finset.analyticAt_fun_sum _ (fun i _ => (ha i).mul analyticAt_const)

/-- The `k`-th coefficient of the derivative of `∑ᵢ C(aᵢ z)·Xⁱ` is analytic in `z`. -/
@[aesop safe]
theorem Qz_deriv_coeff_analytic {d : ℕ} (a : Fin (d+1) → ℂ → ℂ) (z₀ : ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) z₀) (k : ℕ) :
    AnalyticAt ℂ
      (fun z => (derivative (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ) : ℂ[X])).coeff k) z₀ := by
  have heq : (fun z => (derivative (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ) : ℂ[X])).coeff k)
      = fun z => (k + 1 : ℂ) * (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ) : ℂ[X]).coeff (k+1) := by
    funext z; rw [coeff_derivative]; ring
  rw [heq]
  exact analyticAt_const.mul (Qz_coeff_analytic a z₀ ha (k+1))

/-- **The resultant of the specialization with its derivative is analytic in `z` (PROVEN).** Thus the
locus where `∑ᵢ aᵢ(z)·Yⁱ` fails to be squarefree is the zero set of an analytic function — exactly the
"discrete bad set" of the card's Step 3, to which `exists_nonzero_on_accumulating` applies. (The
resultant is the Sylvester determinant; its entries are coefficients of the polynomial and its
derivative, each analytic by `Qz_coeff_analytic`/`Qz_deriv_coeff_analytic`; `analyticAt_matrix_det`
finishes.) -/
@[aesop safe]
theorem resultant_specialize_analytic {d : ℕ} (a : Fin (d+1) → ℂ → ℂ) (z₀ : ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) z₀) :
    AnalyticAt ℂ (fun z => resultant (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ))
      (derivative (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ))) d (d-1)) z₀ := by
  set Qz : ℂ → ℂ[X] := fun z => ∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ) with hQz
  have heq : (fun z => resultant (Qz z) (derivative (Qz z)) d (d-1))
      = fun z => (sylvester (Qz z) (derivative (Qz z)) d (d-1)).det := by
    funext z; rw [resultant]
  rw [heq]
  apply analyticAt_matrix_det
  intro i j
  simp only [sylvester, Matrix.of_apply]
  induction j using Fin.addCases with
  | left j₁ =>
    simp only [Fin.addCases_left]; split_ifs
    · exact Qz_deriv_coeff_analytic a z₀ ha _
    · exact analyticAt_const
  | right j₁ =>
    simp only [Fin.addCases_right]; split_ifs
    · exact Qz_coeff_analytic a z₀ ha _
    · exact analyticAt_const

/-- `natDegree(derivative p) = d - 1` when `natDegree p = d ≥ 1` over `ℂ` (characteristic 0): the
leading coefficient `d · p.coeff d` of `p'` is nonzero since `d ≠ 0`. Needed to match the fixed-degree
resultant `(d, d-1)` with the default-degree resultant for the separability criterion. -/
@[aesop safe]
theorem natDegree_deriv_eq {p : ℂ[X]} {d : ℕ} (hd : 1 ≤ d) (hp : p.natDegree = d) :
    (derivative p).natDegree = d - 1 := by
  have hpne : p ≠ 0 := fun h => by rw [h, natDegree_zero] at hp; omega
  have hle : (derivative p).natDegree ≤ d - 1 :=
    (Polynomial.natDegree_derivative_le p).trans (le_of_eq (by rw [hp]))
  have hne : (derivative p).coeff (d-1) ≠ 0 := by
    rw [coeff_derivative, show (d-1)+1 = d from by omega]
    refine mul_ne_zero ?_ ?_
    · rw [← hp]; exact leadingCoeff_ne_zero.mpr hpne
    · have hc : (↑(d-1) + 1 : ℂ) = ↑d := by rw [Nat.cast_pred (by omega : 0 < d)]; ring
      rw [hc]; exact_mod_cast Nat.one_le_iff_ne_zero.mp hd
  exact le_antisymm hle (Polynomial.le_natDegree_of_ne_zero hne)

/-- **Squarefree ⟺ nonzero fixed-degree resultant (PROVEN).** When the top coefficient survives
(`a_d(z) ≠ 0`), the specialization `∑ᵢ C(aᵢ z)·Xⁱ` is separable iff its degree-`(d,d-1)` resultant with
its derivative is nonzero — bridging the analytic resultant (`resultant_specialize_analytic`) to the
separability hypothesis of `no_separable_analytic_relation`. -/
@[aesop norm simp]
theorem separable_iff_resultant_fixed {d : ℕ} (hd : 1 ≤ d) (a : Fin (d+1) → ℂ → ℂ) (z : ℂ)
    (hlead : a (Fin.last d) z ≠ 0) :
    (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ) : ℂ[X]).Separable
    ↔ resultant (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ))
        (derivative (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ))) d (d-1) ≠ 0 := by
  set Q : ℂ[X] := ∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ) with hQ
  have hdeg : Q.natDegree = d := Qpoly_natDegree a z hlead
  have hQne : Q ≠ 0 := fun h => by rw [h, natDegree_zero] at hdeg; omega
  have hderiv_deg : (derivative Q).natDegree = d - 1 := natDegree_deriv_eq hd hdeg
  have hreseq : resultant Q (derivative Q) d (d-1) = resultant Q (derivative Q) := by
    show resultant Q (derivative Q) d (d-1)
      = resultant Q (derivative Q) Q.natDegree (derivative Q).natDegree
    rw [hdeg, hderiv_deg]
  rw [hreseq]
  exact ⟨fun hsep h => (resultant_eq_zero_iff.mp h).2 hsep, separable_of_resultant_ne hQne⟩

/-- **A squarefree crossing point exists on the arc (PROVEN).** If the coefficients `aᵢ` are analytic
on a preconnected `Ω`, the specialization is separable at some `w ∈ Ω`, and `S ⊆ Ω` accumulates at
`z₁ ∈ Ω`, then there is `z₀ ∈ S` with surviving top coefficient *and* squarefree specialization. The
non-separable locus is the zero set of `z ↦ a_d(z)·resultant(z)` — analytic and not identically zero —
so `exists_nonzero_on_accumulating` finds a good point on the arc. This is the card's "choose a generic
crossing point off the discriminant locus." -/
@[aesop safe]
theorem exists_separable_crossing {d : ℕ} (hd : 1 ≤ d) {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (a : Fin (d+1) → ℂ → ℂ) (ha : ∀ i, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a (Fin.last d) w ≠ 0)
    (hsepw : (∑ i : Fin (d+1), C (a i w) * X ^ (i:ℕ) : ℂ[X]).Separable)
    {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) {S : Set ℂ} (hS : S ⊆ Ω)
    (haccum : ∃ᶠ z in 𝓝[≠] z₁, z ∈ S) :
    ∃ z₀ ∈ S, a (Fin.last d) z₀ ≠ 0 ∧ (∑ i : Fin (d+1), C (a i z₀) * X ^ (i:ℕ) : ℂ[X]).Separable := by
  set g : ℂ → ℂ := fun z => a (Fin.last d) z * resultant (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ))
    (derivative (∑ i : Fin (d+1), C (a i z) * X ^ (i:ℕ))) d (d-1) with hg
  have hgan : AnalyticOnNhd ℂ g Ω := fun z hz =>
    (ha (Fin.last d) z hz).mul (resultant_specialize_analytic a z (fun i => ha i z hz))
  have hgw : g w ≠ 0 :=
    mul_ne_zero hleadw ((separable_iff_resultant_fixed hd a w hleadw).mp hsepw)
  obtain ⟨z₀, hz₀S, hgz₀⟩ := exists_nonzero_on_accumulating hΩc hgan hw hgw hz₁ hS haccum
  obtain ⟨hl₀, hr₀⟩ := mul_ne_zero_iff.mp hgz₀
  exact ⟨z₀, hz₀S, hl₀, (separable_iff_resultant_fixed hd a z₀ hl₀).mpr hr₀⟩

/-- **The card's connected proof, Step 3, fully assembled (PROVEN).** No relation
`∑ᵢ aᵢ(z)·u₀(z)ⁱ = 0` holds on `Ext` when: the coefficients `aᵢ` are analytic on a preconnected basin
`Ω` (Step 1, φ_b analytic), the specialization is separable somewhere in `Ω` (the minimal polynomial of
`u₀` over `ℂ(z,φ_b)` is separable in char 0), and `Ω` meets the unit circle in an arc `S` accumulating
at an interior point (Step 2, the **capacity** argument that the basin crosses the circle). The proof:
`exists_separable_crossing` produces a squarefree crossing point `z₀ ∈ S` on the circle, then
`no_separable_analytic_relation` continues `u₀` across `z₀` against its natural boundary. This is the
entire u₀-side of `u0_phi_independence` (connected case); the three hypotheses `ha`/`hsepw`/`hScirc`+
`haccum` are exactly the Böttcher-side analytic inputs (φ_b analyticity, transcendence-of-φ_b via the
minimal polynomial, capacity crossing). -/
@[aesop safe]
theorem u0_phi_card_step3 {d : ℕ} (hd : 1 ≤ d) {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    (a : Fin (d+1) → ℂ → ℂ) (ha : ∀ i, AnalyticOnNhd ℂ (a i) Ω)
    {w : ℂ} (hw : w ∈ Ω) (hleadw : a (Fin.last d) w ≠ 0)
    (hsepw : (∑ i : Fin (d+1), C (a i w) * X ^ (i:ℕ) : ℂ[X]).Separable)
    {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) {S : Set ℂ} (hS : S ⊆ Ω)
    (hScirc : ∀ z ∈ S, ‖z‖ = 1) (haccum : ∃ᶠ z in 𝓝[≠] z₁, z ∈ S)
    (hrel : ∀ z ∈ Ext, ∑ i : Fin (d+1), a i z * (u0 z) ^ (i:ℕ) = 0) : False := by
  obtain ⟨z₀, hz₀S, hl₀, hsep₀⟩ :=
    exists_separable_crossing hd hΩc a ha hw hleadw hsepw hz₁ hS haccum
  exact no_separable_analytic_relation hd z₀ (hScirc z₀ hz₀S) a
    (fun i => ha i z₀ (hS hz₀S)) hl₀ hsep₀ hrel

/-- **The φ_b-specialized coefficient is analytic on the basin (PROVEN).** For a function `φ` analytic
on an open `Ω` and a polynomial `P ∈ ℂ[z][Y]`, the function `z ↦ P(z, φ(z))` is analytic on `Ω`. This
is how the card's `aᵢ(z) = (coeff of u₀ⁱ in P)(z, φ_b(z))` become analytic functions once `φ_b` is
analytic on the basin — the `ha` input to `u0_phi_card_step3`. Generalizes
`U0Transcendence.relation_analytic` from `u₀` on `Ext` to any analytic `φ` on `Ω`. -/
@[aesop safe]
theorem eval_phi_analytic {Ω : Set ℂ} {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ Ω) (P : (Polynomial ℂ)[X]) :
    AnalyticOnNhd ℂ (fun z => P.eval₂ (evalRingHom z) (φ z)) Ω := by
  intro z hz
  have h2 : AnalyticAt ℂ (fun w : ℂ => (w, φ w)) z := analyticAt_id.prod (hφ z hz)
  exact (bivar_analytic P (z, φ z)).comp_of_eq h2 rfl

/-- **The card's connected proof in literal form (deg_U ≥ 1 case, PROVEN).** No nonzero polynomial
relation `P(z, u₀(z), φ_b(z)) = 0` of positive `U`-degree holds on `Ext`, *given* the Böttcher-side
analytic inputs: `φ_b` analytic on a preconnected basin `Ω` (Step 1), the specialization of `P` in `U`
separable at some `w ∈ Ω` with surviving top coefficient (the minimal polynomial of `u₀` over
`ℂ(z,φ_b)`, separable in characteristic 0), and `Ω` meeting the unit circle in an arc `S` accumulating
at an interior point (Step 2, the capacity argument). The relation `P(z,u₀,φ_b)` is read here as
`P.eval₂ (eval₂RingHom (evalRingHom z) (φ_b z)) (u₀ z)`, viewing `P ∈ (ℂ[z][Y])[U]`. The `U`-coefficients
`(P.coeff i)(z, φ_b z)` are analytic on `Ω` by `eval_phi_analytic`; the rest is `u0_phi_card_step3`.
This is the entire u₀-side of `u0_phi_independence` (connected case), reduced to the three Böttcher
analytic hypotheses. -/
@[aesop safe]
theorem u0_phi_no_relation_3var {Ω : Set ℂ} (hΩc : IsPreconnected Ω)
    {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ Ω)
    (P : (Polynomial (Polynomial ℂ))[X]) (hd : 1 ≤ P.natDegree)
    {w : ℂ} (hw : w ∈ Ω)
    (hleadw : (∑ i : Fin (P.natDegree+1),
      C ((P.coeff i).eval₂ (evalRingHom w) (φ w)) * X ^ (i:ℕ) : ℂ[X]).coeff P.natDegree ≠ 0)
    (hsepw : (∑ i : Fin (P.natDegree+1),
      C ((P.coeff i).eval₂ (evalRingHom w) (φ w)) * X ^ (i:ℕ) : ℂ[X]).Separable)
    {z₁ : ℂ} (hz₁ : z₁ ∈ Ω) {S : Set ℂ} (hS : S ⊆ Ω)
    (hScirc : ∀ z ∈ S, ‖z‖ = 1) (haccum : ∃ᶠ z in 𝓝[≠] z₁, z ∈ S)
    (hrel : ∀ z ∈ Ext, P.eval₂ (eval₂RingHom (evalRingHom z) (φ z)) (u0 z) = 0) : False := by
  set d := P.natDegree with hd'
  set a : Fin (d+1) → ℂ → ℂ := fun i z => (P.coeff i).eval₂ (evalRingHom z) (φ z) with ha'
  have ha : ∀ i, AnalyticOnNhd ℂ (a i) Ω := fun i => eval_phi_analytic hφ (P.coeff i)
  have hlead : a (Fin.last d) w ≠ 0 := by
    have hc : (∑ i : Fin (d+1), C (a i w) * X ^ (i:ℕ) : ℂ[X]).coeff d = a (Fin.last d) w := by
      rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (Fin.last d)]
      · rw [coeff_C_mul, coeff_X_pow, Fin.val_last]; simp
      · intro i _ hi
        rw [coeff_C_mul, coeff_X_pow,
          if_neg (fun h => hi (Fin.ext (h.symm.trans (Fin.val_last d).symm))), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [← hc]; exact hleadw
  have hrel' : ∀ z ∈ Ext, ∑ i : Fin (d+1), a i z * (u0 z) ^ (i:ℕ) = 0 := by
    intro z hz
    have hz0 := hrel z hz
    rw [eval₂_eq_sum_range] at hz0
    rw [show (∑ i : Fin (d+1), a i z * (u0 z) ^ (i:ℕ))
          = ∑ k ∈ Finset.range (d+1), (P.coeff k).eval₂ (evalRingHom z) (φ z) * (u0 z) ^ k from
        Fin.sum_univ_eq_sum_range
          (fun k => (P.coeff k).eval₂ (evalRingHom z) (φ z) * (u0 z) ^ k) (d+1)]
    exact hz0
  exact u0_phi_card_step3 hd hΩc a ha hw hlead hsepw hz₁ hS hScirc haccum hrel'

/-- **Step 2 endgame: a forward-invariant unit circle forces `b = 0` (PROVEN).** If `‖w + b‖ = 1` for
every `w` on the unit circle, then `b = 0`. (Test `w = 1`, `w = -1`: `‖b‖² + 2 Re b = 0` and
`‖b‖² − 2 Re b = 0`; adding gives `‖b‖² = 0`.) This closes the card's Step 2: if the basin avoids the
circle then `K_b` = closed unit disk (capacity), so `J_b = {|z|=1}` is forward-invariant under
`z ↦ z²+b` (every `z²` ranges over the circle as `z` does), forcing `b = 0` — contradicting `b ≠ 0`.
Hence the basin *does* cross the circle, supplying the `haccum` arc of `u0_phi_no_relation_3var`. -/
@[aesop safe]
theorem eq_zero_of_norm_add_eq_one {b : ℂ} (h : ∀ w : ℂ, ‖w‖ = 1 → ‖w + b‖ = 1) : b = 0 := by
  have h1 : normSq (1 + b) = 1 := by
    rw [Complex.normSq_eq_norm_sq, h 1 (by simp)]; norm_num
  have h2 : normSq (-1 + b) = 1 := by
    rw [Complex.normSq_eq_norm_sq, h (-1) (by simp)]; norm_num
  rw [Complex.normSq_add] at h1 h2
  simp only [Complex.normSq_one, Complex.normSq_neg, Complex.one_re, map_one] at h1 h2
  have hb : normSq b = 0 := by
    have e1 : (1 : ℂ) * (starRingEnd ℂ) b = (starRingEnd ℂ) b := one_mul _
    have e2 : (-1 : ℂ) * (starRingEnd ℂ) b = -((starRingEnd ℂ) b) := by ring
    rw [e1] at h1; rw [e2] at h2
    simp only [Complex.neg_re, Complex.conj_re] at h1 h2
    nlinarith [h1, h2, normSq_nonneg b]
  exact normSq_eq_zero.mp hb

/-- **Step 2 endgame, dynamics form: a forward-invariant unit circle forces `b = 0` (PROVEN).** If
`z ↦ z²+b` maps the unit circle into itself (`‖z²+b‖=1` for all `‖z‖=1`), then `b = 0`. Every unit `w`
is `z²` for some unit `z` (square roots in `ℂ`, `IsAlgClosed.exists_pow_nat_eq`), so this reduces to
`eq_zero_of_norm_add_eq_one`. This is the form the card's Step 2 produces directly: `J_b = {|z|=1}` is
completely invariant, so `f_b` maps the circle into itself; hence `b = 0`, contradicting `b ≠ 0`, so the
basin must cross the circle — the missing geometric input is now reduced to the capacity fact
`K_b = closed unit disk` (Böttcher-side). -/
@[aesop safe]
theorem eq_zero_of_circle_invariant {b : ℂ} (h : ∀ z : ℂ, ‖z‖ = 1 → ‖z ^ 2 + b‖ = 1) : b = 0 := by
  apply eq_zero_of_norm_add_eq_one
  intro w hw
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z ^ 2 = w := IsAlgClosed.exists_pow_nat_eq w (by norm_num)
  have hzn : ‖z‖ = 1 := by
    have hpow : ‖z‖ ^ 2 = ‖w‖ := by rw [← norm_pow, hz]
    rw [hw] at hpow; nlinarith [norm_nonneg z, hpow]
  rw [← hz]; exact h z hzn

/-- **The capacity conclusion forces `b = 0` (PROVEN).** If the closed unit disk is completely
invariant under `z ↦ z²+b` (`‖z‖ ≤ 1 ↔ ‖z²+b‖ ≤ 1`), then `b = 0`. On the circle `‖z²+b‖ ≤ 1` is the
forward direction; perturbing `z` outward (`t·z`, `t>1`) keeps `‖(tz)²+b‖ > 1` by invariance, and
continuity forces `‖z²+b‖ ≥ 1` in the limit, so `‖z²+b‖ = 1` — then `eq_zero_of_circle_invariant`. This
discharges the card's entire Step 2 *modulo the single deep capacity fact* `K_b = closed unit disk`
(which holds when the basin avoids the circle, by `cap(K_b)=1` + the energy test — the Böttcher-side
input). With it, "basin avoids circle ⟹ `b = 0`" is complete, so `b ≠ 0` forces the basin to cross. -/
@[aesop safe]
theorem eq_zero_of_invariant_disk {b : ℂ} (hinv : ∀ z : ℂ, ‖z‖ ≤ 1 ↔ ‖z ^ 2 + b‖ ≤ 1) : b = 0 := by
  apply eq_zero_of_circle_invariant
  intro z hz
  refine le_antisymm ((hinv z).mp (le_of_eq hz)) ?_
  by_contra hlt
  push_neg at hlt
  have hcont : ContinuousAt (fun t : ℝ => ‖((t : ℂ) * z) ^ 2 + b‖) 1 := by fun_prop
  have hval : (fun t : ℝ => ‖((t : ℂ) * z) ^ 2 + b‖) 1 < 1 := by simp [hlt]
  have hev : ∀ᶠ t : ℝ in 𝓝 1, ‖((t : ℂ) * z) ^ 2 + b‖ < 1 := hcont.eventually_lt_const hval
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  set t : ℝ := 1 + δ/2 with ht
  have htmem : dist t 1 < δ := by
    rw [ht, Real.dist_eq, show (1 + δ/2 - 1) = δ/2 by ring, abs_of_pos (by linarith)]; linarith
  have htnorm : (1 : ℝ) < ‖(t : ℂ) * z‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hz, mul_one, ht]
    linarith
  exact absurd ((hinv ((t : ℂ) * z)).mpr (hball htmem).le) (not_le.mpr htnorm)

/-- **Basin avoids the circle ⟹ the closed disk is inside `K_b` (PROVEN).** If the basin `Ω_b = K_bᶜ`
is preconnected, avoids the unit circle, and contains a point of norm `> 1` (it contains a neighborhood
of `∞`), then `closedBall 0 1 ⊆ K_b`. The preconnected basin, disjoint from the circle, lies in one of
the two components `{‖z‖<1}`, `{‖z‖>1}`; containing a large-norm point puts it in the exterior, so the
closed disk is in its complement `K_b`. This is the first half of the card's Step 2; combined with the
deep capacity fact `cap(K_b)=1` (giving `K_b = closed disk`) and `eq_zero_of_invariant_disk`, it forces
`b = 0` — so a nonexceptional basin must cross the circle. -/
@[aesop safe]
theorem disk_subset_of_basin_avoids_circle {K : Set ℂ} (hΩc : IsPreconnected Kᶜ)
    (havoid : ∀ z ∈ Kᶜ, ‖z‖ ≠ 1) {w : ℂ} (hw : w ∈ Kᶜ) (hwn : 1 < ‖w‖) :
    Metric.closedBall (0:ℂ) 1 ⊆ K := by
  have hUo : IsOpen {z : ℂ | ‖z‖ < 1} := isOpen_lt continuous_norm continuous_const
  have hVo : IsOpen {z : ℂ | 1 < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hcover : Kᶜ ⊆ {z : ℂ | ‖z‖ < 1} ∪ {z : ℂ | 1 < ‖z‖} := by
    intro z hz
    rcases lt_trichotomy ‖z‖ 1 with h | h | h
    · exact Or.inl h
    · exact absurd h (havoid z hz)
    · exact Or.inr h
  have hdisj : Disjoint {z : ℂ | ‖z‖ < 1} {z : ℂ | 1 < ‖z‖} := by
    rw [Set.disjoint_left]; intro z h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2; linarith
  rcases hΩc.subset_or_subset hUo hVo hdisj hcover with hsub | hsub
  · exact absurd (hsub hw) (by simp only [Set.mem_setOf_eq]; linarith)
  · intro z hz
    by_contra hzK
    have hmem := hsub (show z ∈ Kᶜ from hzK)
    simp only [Set.mem_setOf_eq] at hmem
    rw [mem_closedBall, dist_zero_right] at hz
    linarith

end U0PhiCard
