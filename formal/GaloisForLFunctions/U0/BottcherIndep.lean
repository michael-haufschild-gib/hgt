/-
# Eremenko–van Strien rigidity, analytic core: algebraic-over-analytic ⟹ continues across the boundary

The both-connected case of `q62` reduces (via `Bottcher.q62_both_connected`) to the single input
`TranscendentalOverAdjoin φ_{c₁} φ_{c₂}` — `φ_{c₁}` is not algebraic over `ℂ(z)[φ_{c₂}]`. The argument is
the same "algebraic functions continue across the boundary" engine that proves `u₀` transcendental
(`U0Transcendence.continues_of_separable_relation`), now with the **base enlarged from `ℂ(z)` to
`ℂ(z)[φ_{c₂}]`**: an algebraic relation has *analytic* coefficients (polynomials in `z` and the analytic
`φ_{c₂}`), so the holomorphic implicit function theorem still continues `φ_{c₁}` across a boundary point
`z₀` of its domain — **wherever `φ_{c₂}` is analytic**. At a point of `φ_{c₁}`'s natural boundary that
lies in `φ_{c₂}`'s domain, that contradicts the boundary, forcing no relation.

This file builds the abstract analytic core (`continues_of_analytic_coeff_relation`): a general analytic
`f` on an open `D`, satisfying a polynomial relation with analytic coefficients, continues across a
boundary point `z₀` at which the specialized polynomial is squarefree, given a preconnected approach
lens. It reuses `HolomorphicIFT` (`holo_implicit`, `branch_selection`, `root_complete`) and the general
`ContinuesAcross` predicate. The Böttcher natural-boundary input and the geometry `J_{c₁} ⊄ K_{c₂}` are
the remaining bricks fed to it.
-/
import GaloisForLFunctions.U0.HolomorphicIFT
import GaloisForLFunctions.U0.U0NaturalBoundary

open Polynomial Complex Metric Filter Topology U0NaturalBoundary HolomorphicIFT

namespace BottcherIndep

/-- **Analytic-coefficient bivariate is analytic.** If `a i : ℂ → ℂ` are analytic at `z₀`, then
`(z, w) ↦ ∑ i, a i z · w ^ i` is analytic at `(z₀, w₀)` for every `w₀`. -/
theorem analytic_coeffSum {d : ℕ} (a : Fin (d + 1) → ℂ → ℂ) {z₀ : ℂ}
    (ha : ∀ i, AnalyticAt ℂ (a i) z₀) (w₀ : ℂ) :
    AnalyticAt ℂ (fun q : ℂ × ℂ => ∑ i : Fin (d + 1), a i q.1 * q.2 ^ (i : ℕ)) (z₀, w₀) := by
  have heq : (fun q : ℂ × ℂ => ∑ i : Fin (d + 1), a i q.1 * q.2 ^ (i : ℕ))
      = ∑ i : Fin (d + 1), (fun q : ℂ × ℂ => a i q.1 * q.2 ^ (i : ℕ)) := by
    funext q; rw [Finset.sum_apply]
  rw [heq]
  apply Finset.analyticAt_sum
  intro i _
  exact ((ha i).comp (analyticAt_fst (𝕜 := ℂ))).mul
    ((analyticAt_snd (𝕜 := ℂ)).pow (i : ℕ))

/-- **`∂_w` of the analytic-coefficient bivariate is the specialized polynomial's derivative.** With
`Q₀ = ∑ a_i(z₀) X^i` the specialized polynomial, `(∂_w ∑ a_i(z) w^i)|_{(z₀,w₀)} = Q₀'(w₀)`. The analog of
`HolomorphicIFT.partial_w_deriv` for analytic (rather than polynomial-in-`z`) coefficients — it supplies
the simple-root nonvanishing input of `holo_implicit`. -/
theorem partial_w_deriv_coeffSum {d : ℕ} (a : Fin (d + 1) → ℂ → ℂ) {z₀ : ℂ}
    (ha : ∀ i, AnalyticAt ℂ (a i) z₀) (w₀ : ℂ) (Q₀ : ℂ[X])
    (hQ₀ : ∀ w : ℂ, Q₀.eval w = ∑ i : Fin (d + 1), a i z₀ * w ^ (i : ℕ)) :
    (fderiv ℂ (fun q : ℂ × ℂ => ∑ i : Fin (d + 1), a i q.1 * q.2 ^ (i : ℕ)) (z₀, w₀)) (0, 1)
      = (derivative Q₀).eval w₀ := by
  set F : ℂ × ℂ → ℂ := fun q => ∑ i : Fin (d + 1), a i q.1 * q.2 ^ (i : ℕ) with hF
  have hfdiff : HasFDerivAt F (fderiv ℂ F (z₀, w₀)) (z₀, w₀) :=
    (analytic_coeffSum a ha w₀).differentiableAt.hasFDerivAt
  have hι : HasFDerivAt (fun w : ℂ => (z₀, w))
      ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ)) w₀ :=
    (hasFDerivAt_const z₀ w₀).prodMk (hasFDerivAt_id w₀)
  have hcomp : HasFDerivAt (fun w => F (z₀, w))
      ((fderiv ℂ F (z₀, w₀)).comp ((0 : ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.id ℂ ℂ))) w₀ :=
    hfdiff.comp w₀ hι
  have hpoly : HasDerivAt (fun w => F (z₀, w)) ((derivative Q₀).eval w₀) w₀ := by
    have hrw : (fun w => F (z₀, w)) = fun w => Q₀.eval w := by
      funext w; rw [hF]; exact (hQ₀ w).symm
    rw [hrw]
    exact Polynomial.hasDerivAt Q₀ w₀
  have huniq := hcomp.unique hpoly.hasFDerivAt
  have hev := ContinuousLinearMap.ext_iff.mp huniq 1
  simpa using hev

/-- The `z`-specialized polynomial `Q_z(Y) = ∑ a_i(z)·Y^i` whose roots are the local branch values. -/
noncomputable def specPoly {d : ℕ} (a : Fin (d + 1) → ℂ → ℂ) (z : ℂ) : ℂ[X] :=
  ∑ i : Fin (d + 1), Polynomial.C (a i z) * Polynomial.X ^ (i : ℕ)

theorem specPoly_eval {d : ℕ} (a : Fin (d + 1) → ℂ → ℂ) (z w : ℂ) :
    (specPoly a z).eval w = ∑ i : Fin (d + 1), a i z * w ^ (i : ℕ) := by
  rw [specPoly, Polynomial.eval_finsetSum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem specPoly_coeff {d : ℕ} (a : Fin (d + 1) → ℂ → ℂ) (z : ℂ) (j : Fin (d + 1)) :
    (specPoly a z).coeff (j : ℕ) = a j z := by
  rw [specPoly, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single j]
  · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
  · intro i _ hij
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      if_neg (fun h => hij (Fin.ext h).symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem specPoly_natDegree {d : ℕ} (a : Fin (d + 1) → ℂ → ℂ) (z : ℂ)
    (hlead : a (Fin.last d) z ≠ 0) : (specPoly a z).natDegree = d := by
  refine le_antisymm ?_ ?_
  · rw [specPoly]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => ?_)
    calc (Polynomial.C (a i z) * Polynomial.X ^ (i : ℕ)).natDegree
        ≤ (Polynomial.C (a i z)).natDegree + (Polynomial.X ^ (i : ℕ)).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ d := by
          rw [Polynomial.natDegree_C, Polynomial.natDegree_X_pow]
          have : (i : ℕ) ≤ d := Nat.lt_succ_iff.mp i.isLt
          omega
  · refine Polynomial.le_natDegree_of_ne_zero ?_
    have hc := specPoly_coeff a z (Fin.last d)
    rw [Fin.val_last] at hc
    rw [hc]; exact hlead

/-- **Algebraic-over-analytic ⟹ continues across the boundary (the E–vS analytic core).** A function `f`
analytic on an open `D`, satisfying a polynomial relation `∑ a_i(z)·f(z)^i = 0` with coefficients `a_i`
analytic at a boundary point `z₀` of `D`, continues analytically across `z₀` — provided the specialized
polynomial `∑ a_i(z₀)·Y^i` is squarefree of degree `d ≥ 1` and the `D`-side lenses `D ∩ ball z₀ ρ` are
preconnected and nonempty. The holomorphic implicit function theorem produces the `d` analytic branches;
on the lens every `f`-value is one of them (`root_complete`), so the preconnected monodromy
(`branch_selection`) pins `f` to a single analytic branch — the continuation. This generalizes
`U0Transcendence.continues_of_separable_relation` from the base `ℂ(z)` to **analytic coefficients**, so it
applies with `a_i` polynomials in `z` and a *second* analytic function `φ_{c₂}` — the relative
transcendence the both-connected case needs. -/
theorem continues_of_analytic_coeff_relation
    {f : ℂ → ℂ} {D : Set ℂ} {z₀ : ℂ} {d : ℕ} (hd : 1 ≤ d)
    (a : Fin (d + 1) → ℂ → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) z₀)
    (hlead : a (Fin.last d) z₀ ≠ 0) (hsep : (specPoly a z₀).Separable)
    (hf : ∀ z ∈ D, AnalyticAt ℂ f z)
    (hrel : ∀ z ∈ D, ∑ i : Fin (d + 1), a i z * (f z) ^ (i : ℕ) = 0)
    (hlens : ∀ ρ : ℝ, 0 < ρ → IsPreconnected (D ∩ ball z₀ ρ) ∧ (D ∩ ball z₀ ρ).Nonempty) :
    ContinuesAcross f D z₀ := by
  classical
  have hQ₀deg : (specPoly a z₀).natDegree = d := specPoly_natDegree a z₀ hlead
  have hsimple : ∀ x : ℂ, (specPoly a z₀).eval x = 0 → (derivative (specPoly a z₀)).eval x ≠ 0 := by
    intro x hx hdx
    obtain ⟨u, v, huv⟩ := hsep
    have key := congrArg (Polynomial.eval x) huv
    simp only [eval_add, eval_mul, hx, hdx, mul_zero, eval_one, add_zero] at key
    exact one_ne_zero key.symm
  have hnodup : (specPoly a z₀).roots.Nodup := nodup_roots hsep
  have hcard : (specPoly a z₀).roots.toFinset.card = d := by
    rw [Multiset.toFinset_card_of_nodup hnodup, IsAlgClosed.card_roots_eq_natDegree, hQ₀deg]
  set s := (specPoly a z₀).roots.toFinset with hsdef
  set rv : Fin d → ℂ := fun i => (s.equivFin.symm (finCongr hcard.symm i) : ℂ) with hrv
  have hrinj : Function.Injective rv := by
    intro i j hij
    apply (finCongr hcard.symm).injective; apply s.equivFin.symm.injective; exact Subtype.ext hij
  have hroot : ∀ i, (specPoly a z₀).eval (rv i) = 0 := fun i =>
    isRoot_of_mem_roots (Multiset.mem_toFinset.mp (s.equivFin.symm (finCongr hcard.symm i)).2)
  have hbranch : ∀ i, ∃ r : ℂ → ℂ, AnalyticAt ℂ r z₀ ∧ r z₀ = rv i ∧
      ∀ᶠ z in 𝓝 z₀, (∑ k : Fin (d + 1), a k z * (r z) ^ (k : ℕ)) = 0 := by
    intro i
    have hf_an : AnalyticAt ℂ (fun q : ℂ × ℂ => ∑ k : Fin (d + 1), a k q.1 * q.2 ^ (k : ℕ))
        (z₀, rv i) := analytic_coeffSum a ha (rv i)
    have h0 : (∑ k : Fin (d + 1), a k z₀ * (rv i) ^ (k : ℕ)) = 0 := by
      rw [← specPoly_eval a z₀ (rv i)]; exact hroot i
    have hfw : (fderiv ℂ (fun q : ℂ × ℂ => ∑ k : Fin (d + 1), a k q.1 * q.2 ^ (k : ℕ))
        (z₀, rv i)) (0, 1) ≠ 0 := by
      rw [partial_w_deriv_coeffSum a ha (rv i) (specPoly a z₀) (specPoly_eval a z₀)]
      exact hsimple (rv i) (hroot i)
    obtain ⟨r, hr1, hr2, hr3⟩ := holo_implicit hf_an h0 hfw
    exact ⟨r, hr1, hr2, hr3⟩
  choose r hr_an hr0 hr_rel using hbranch
  have E1 : ∀ᶠ z in 𝓝 z₀, ∀ i, (∑ k : Fin (d + 1), a k z * (r i z) ^ (k : ℕ)) = 0 :=
    eventually_all.mpr hr_rel
  have E2 : ∀ᶠ z in 𝓝 z₀, ∀ i j, i ≠ j → r i z ≠ r j z := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    by_cases hij : i = j
    · exact Eventually.of_forall (fun z h => (h hij).elim)
    · have hne : r i z₀ ≠ r j z₀ := by rw [hr0, hr0]; exact fun h => hij (hrinj h)
      have hcij : ContinuousAt (fun z => r i z - r j z) z₀ :=
        ((hr_an i).continuousAt).sub ((hr_an j).continuousAt)
      filter_upwards [hcij.eventually_ne (sub_ne_zero.mpr hne)] with z hz
      exact fun _ => sub_ne_zero.mp hz
  have E3 : ∀ᶠ z in 𝓝 z₀, a (Fin.last d) z ≠ 0 :=
    ((ha (Fin.last d)).continuousAt).eventually_ne hlead
  have E4 : ∀ᶠ z in 𝓝 z₀, ∀ i, ContinuousAt (r i) z := by
    rw [eventually_all]; intro i
    exact (hr_an i).eventually_analyticAt.mono (fun z hz => hz.continuousAt)
  have hcombo := E1.and (E2.and (E3.and E4))
  rw [Metric.eventually_nhds_iff] at hcombo
  obtain ⟨ρ, hρ, hball⟩ := hcombo
  set U : Set ℂ := D ∩ ball z₀ ρ with hUdef
  have hUsub : ∀ z ∈ U, dist z z₀ < ρ := fun z hz => mem_ball.mp hz.2
  obtain ⟨hUpre, hUne⟩ := hlens ρ hρ
  have hh : ContinuousOn f U := fun z hz => (hf z hz.1).continuousAt.continuousWithinAt
  have hr_cont : ∀ i, ContinuousOn (r i) U :=
    fun i z hz => ((hball (hUsub z hz)).2.2.2 i).continuousWithinAt
  have hsep_branch : ∀ z ∈ U, ∀ i j, i ≠ j → r i z ≠ r j z :=
    fun z hz => (hball (hUsub z hz)).2.1
  have hmem : ∀ z ∈ U, ∃ i, f z = r i z := by
    intro z hz
    have hlz : a (Fin.last d) z ≠ 0 := (hball (hUsub z hz)).2.2.1
    have hQzdeg : (specPoly a z).natDegree = d := specPoly_natDegree a z hlz
    have hQzne : (specPoly a z) ≠ 0 := fun h => by rw [h, natDegree_zero] at hQzdeg; omega
    have hrz : Function.Injective (fun i => r i z) :=
      fun i j hij => by_contra fun hne => (hsep_branch z hz i j hne) hij
    have hrzroot : ∀ i, (specPoly a z).IsRoot (r i z) := by
      intro i
      rw [Polynomial.IsRoot, specPoly_eval a z (r i z)]
      exact (hball (hUsub z hz)).1 i
    have hfzroot : (specPoly a z).IsRoot (f z) := by
      rw [Polynomial.IsRoot, specPoly_eval a z (f z)]; exact hrel z hz.1
    exact root_complete hQzne hQzdeg hrz hrzroot hfzroot
  obtain ⟨j, hj⟩ := branch_selection hUpre hUne hh hr_cont hsep_branch hmem
  refine ⟨r j, hr_an j, ?_⟩
  rw [eventually_iff]
  refine mem_nhdsWithin.mpr ⟨ball z₀ ρ, isOpen_ball, mem_ball_self hρ, ?_⟩
  intro w hw
  exact (hj w ⟨hw.2, hw.1⟩).symm

/-- **No separable analytic-coefficient relation at a natural-boundary point.** If `z₀` is a genuine
natural boundary of `f` (`f` does not continue across it from `D`), then `f` satisfies no separable,
degree-`≥1` polynomial relation with coefficients analytic at `z₀` — the contrapositive of
`continues_of_analytic_coeff_relation`. This is the form fed by the Böttcher coordinate's natural
boundary: `φ_{c₁}` does not continue across its Julia set `J_{c₁}`, yet an algebraic relation over
`ℂ(z)[φ_{c₂}]` would continue it (wherever `φ_{c₂}` is analytic) — impossible at a `J_{c₁}` point lying in
`φ_{c₂}`'s domain. -/
theorem no_separable_relation_of_natural_boundary
    {f : ℂ → ℂ} {D : Set ℂ} {z₀ : ℂ} (hnb : ¬ ContinuesAcross f D z₀)
    (hf : ∀ z ∈ D, AnalyticAt ℂ f z)
    (hlens : ∀ ρ : ℝ, 0 < ρ → IsPreconnected (D ∩ ball z₀ ρ) ∧ (D ∩ ball z₀ ρ).Nonempty)
    {d : ℕ} (hd : 1 ≤ d) (a : Fin (d + 1) → ℂ → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) z₀)
    (hlead : a (Fin.last d) z₀ ≠ 0) (hsep : (specPoly a z₀).Separable)
    (hrel : ∀ z ∈ D, ∑ i : Fin (d + 1), a i z * (f z) ^ (i : ℕ) = 0) :
    False :=
  hnb (continues_of_analytic_coeff_relation hd a ha hlead hsep hf hrel hlens)

/-- **The coefficient `z ↦ b(z, g(z))` is analytic** when `g` is analytic at `z₀` and `b ∈ ℂ[z][W]` — the
bivariate polynomial evaluated along `(id, g)`. Supplies the `analytic at z₀` inputs when the relation's
coefficients are polynomials in `z` and a *second* analytic function `g = φ_{c₂}`. -/
theorem analyticAt_evalComp (b : Polynomial (Polynomial ℂ)) {g : ℂ → ℂ} {z₀ : ℂ}
    (hg : AnalyticAt ℂ g z₀) :
    AnalyticAt ℂ (fun z => b.eval₂ (evalRingHom z) (g z)) z₀ :=
  (bivar_analytic b (z₀, g z₀)).comp_of_eq (analyticAt_id.prod hg) rfl

/-- **No polynomial relation over `ℂ(z)[g]` at a natural-boundary point of `f` (the E–vS algebraic
bridge).** If `z₀` is a natural boundary of `f`, `g` is analytic at `z₀`, and the relation coefficients
`b_i ∈ ℂ[z][W]` give a separable degree-`≥1` specialization at `z₀`, then `f` satisfies no relation
`∑ b_i(z, g(z))·f(z)^i = 0` on `D`. Applied to `f = φ_{c₁}`, `g = φ_{c₂}` this is exactly
*`φ_{c₁}` not algebraic over `ℂ(z)[φ_{c₂}]`* — the Eremenko–van Strien rigidity input
`TranscendentalOverAdjoin`, reduced to (i) `φ_{c₁}`'s natural boundary, (ii) the lens geometry, (iii) a
squarefree specialization (`exists_squarefree_specialization`). -/
theorem no_phi_relation_of_natural_boundary
    {f g : ℂ → ℂ} {D : Set ℂ} {z₀ : ℂ} (hnb : ¬ ContinuesAcross f D z₀)
    (hf : ∀ z ∈ D, AnalyticAt ℂ f z) (hg : AnalyticAt ℂ g z₀)
    (hlens : ∀ ρ : ℝ, 0 < ρ → IsPreconnected (D ∩ ball z₀ ρ) ∧ (D ∩ ball z₀ ρ).Nonempty)
    {d : ℕ} (hd : 1 ≤ d) (b : Fin (d + 1) → Polynomial (Polynomial ℂ))
    (hlead : (b (Fin.last d)).eval₂ (evalRingHom z₀) (g z₀) ≠ 0)
    (hsep : (specPoly (fun i z => (b i).eval₂ (evalRingHom z) (g z)) z₀).Separable)
    (hrel : ∀ z ∈ D,
      ∑ i : Fin (d + 1), (b i).eval₂ (evalRingHom z) (g z) * (f z) ^ (i : ℕ) = 0) :
    False :=
  no_separable_relation_of_natural_boundary hnb hf hlens hd
    (fun i z => (b i).eval₂ (evalRingHom z) (g z))
    (fun i => analyticAt_evalComp (b i) hg) hlead hsep hrel

/-! ## Geometry: a boundary point of `K_{c₁}` outside `K_{c₂}` -/

/-- **A compact set inside a "full" set once its frontier is.** If `K₂` is closed with connected,
unbounded complement (a *full* compact-like set — exactly the filled Julia set `K_c`, whose complement is
the connected basin of `∞`), and the frontier of a compact `K₁` lies in `K₂`, then `K₁ ⊆ K₂`. Proof: the
clopen-in-`K₂ᶜ` set `K₁ ∩ K₂ᶜ` is forced empty by connectedness — else it is all of `K₂ᶜ`, making the
compact `K₁` unbounded. -/
theorem compact_subset_of_full {K₁ K₂ : Set ℂ} (hK₁ : IsCompact K₁)
    (hconn : IsPreconnected K₂ᶜ) (hunb : ¬ Bornology.IsBounded K₂ᶜ)
    (hcon : ∀ z ∈ frontier K₁, z ∈ K₂) : K₁ ⊆ K₂ := by
  have hSsubInt : K₁ ∩ K₂ᶜ ⊆ interior K₁ := by
    rintro z ⟨hz1, hz2⟩
    by_contra h
    exact hz2 (hcon z ⟨subset_closure hz1, h⟩)
  have hcover : K₂ᶜ ⊆ interior K₁ ∪ K₁ᶜ := by
    intro z hz
    by_cases hz1 : z ∈ K₁
    · exact Or.inl (hSsubInt ⟨hz1, hz⟩)
    · exact Or.inr hz1
  have hK₁open : IsOpen K₁ᶜ := hK₁.isClosed.isOpen_compl
  rcases Set.eq_empty_or_nonempty (K₂ᶜ ∩ interior K₁) with hu | hu
  · intro z hz
    by_contra hz2
    have hmem : z ∈ K₂ᶜ ∩ interior K₁ := ⟨hz2, hSsubInt ⟨hz, hz2⟩⟩
    rw [hu] at hmem; exact (Set.mem_empty_iff_false z).mp hmem
  · rcases Set.eq_empty_or_nonempty (K₂ᶜ ∩ K₁ᶜ) with hv | hv
    · exfalso; apply hunb
      have hsub : K₂ᶜ ⊆ K₁ := fun z hz => by
        by_contra hz1
        have hmem : z ∈ K₂ᶜ ∩ K₁ᶜ := ⟨hz, hz1⟩
        rw [hv] at hmem; exact (Set.mem_empty_iff_false z).mp hmem
      exact hK₁.isBounded.subset hsub
    · exfalso
      obtain ⟨z, hz⟩ := hconn (interior K₁) K₁ᶜ isOpen_interior hK₁open hcover hu hv
      exact hz.2.2 (interior_subset hz.2.1)

/-- **Both-connected independence — the capstone (function level).** Let `f = φ_{c₁}` be analytic on the
basin `K₁ᶜ = ℂ\K_{c₁}` with the Julia set `frontier K₁` as its natural boundary, and `g = φ_{c₂}` analytic
on the basin `K₂ᶜ` of a *full* `K₂` (`K₂ᶜ` connected, unbounded). If `K_{c₁} ⊄ K_{c₂}` (the parameters are
distinct), then `f` satisfies **no** polynomial relation `∑ b_i(z, g(z))·f(z)^i = 0` over `ℂ(z)[g]`:
the distinct filled-Julia sets put a Julia point `z₀ ∈ J_{c₁}` inside `φ_{c₂}`'s basin
(`compact_subset_of_full`), where the relation would continue `φ_{c₁}` across its natural boundary
(`no_phi_relation_of_natural_boundary`) — impossible. This is `TranscendentalOverAdjoin φ_{c₁} φ_{c₂}` at
the function level: everything is discharged except the two named Böttcher inputs `hnb` (Julia natural
boundary) and `hfdom`/`hgdom` (full-basin analyticity). -/
theorem phi_indep_capstone {f g : ℂ → ℂ} {K₁ K₂ : Set ℂ}
    (hK₁ : IsCompact K₁)
    (hconn : IsPreconnected K₂ᶜ) (hunb : ¬ Bornology.IsBounded K₂ᶜ) (hne : ¬ K₁ ⊆ K₂)
    (hfdom : ∀ z ∈ K₁ᶜ, AnalyticAt ℂ f z) (hgdom : ∀ z ∈ K₂ᶜ, AnalyticAt ℂ g z)
    (hnb : ∀ z₀ ∈ frontier K₁, ¬ ContinuesAcross f K₁ᶜ z₀)
    (hlens : ∀ z₀ ∈ frontier K₁, ∀ ρ : ℝ, 0 < ρ →
      IsPreconnected (K₁ᶜ ∩ ball z₀ ρ) ∧ (K₁ᶜ ∩ ball z₀ ρ).Nonempty)
    {d : ℕ} (hd : 1 ≤ d) (b : Fin (d + 1) → Polynomial (Polynomial ℂ))
    (hrel : ∀ z ∈ K₁ᶜ,
      ∑ i : Fin (d + 1), (b i).eval₂ (evalRingHom z) (g z) * (f z) ^ (i : ℕ) = 0)
    (hcoeff : ∀ z₀ ∈ frontier K₁, z₀ ∉ K₂ →
      (b (Fin.last d)).eval₂ (evalRingHom z₀) (g z₀) ≠ 0 ∧
        (specPoly (fun i z => (b i).eval₂ (evalRingHom z) (g z)) z₀).Separable) :
    False := by
  -- distinct ⟹ a Julia point of c₁ lies outside K_{c₂}
  have hex : ∃ z₀ ∈ frontier K₁, z₀ ∉ K₂ := by
    by_contra hc
    push Not at hc
    exact hne (compact_subset_of_full hK₁ hconn hunb hc)
  obtain ⟨z₀, hz₀fr, hz₀K₂⟩ := hex
  obtain ⟨hlead, hsep⟩ := hcoeff z₀ hz₀fr hz₀K₂
  exact no_phi_relation_of_natural_boundary (hnb z₀ hz₀fr) hfdom (hgdom z₀ hz₀K₂)
    (hlens z₀ hz₀fr) hd b hlead hsep hrel

end BottcherIndep
