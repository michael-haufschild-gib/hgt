import GaloisForLFunctions.HTGeometry.BivariateRootCovering
import GaloisForLFunctions.Bottcher.EntirePolyGrowth

/-!
# Algebraic simple connectedness of the complex affine line

A monic polynomial in one variable over `ℂ[X]` whose specialisation at every complex parameter is
separable splits into monic linear factors over `ℂ[X]`.  Equivalently: the complex affine line has
no nontrivial connected finite étale cover.

The proof is the classical one, carried out inside this project.  The root locus of such a family
is a covering space of the parameter plane (`isCoveringMap_biRootProj`); the plane is simply
connected, so the covering admits a global continuous section; the section is analytic because it
agrees locally with the holomorphic implicit-function branch; a monic Cauchy bound makes it of
polynomial growth, hence a polynomial; and a polynomial root of a polynomial with polynomial
coefficients splits off a monic linear factor.  Induction on the degree finishes.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Topology Set
open scoped ContDiff

noncomputable section

/-- A global continuous root branch over the whole parameter plane. -/
theorem exists_continuous_biRoot {f : ℂ[X][X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsep : ∀ s : ℂ, (biFibre f s).Separable) :
    ∃ g : ℂ → ℂ, Continuous g ∧ ∀ s, biEval f (s, g s) = 0 := by
  obtain ⟨T₀, hT₀⟩ : ∃ z : ℂ, (biFibre f 0).IsRoot z := by
    apply Complex.exists_root
    rw [Polynomial.degree_eq_natDegree (biFibre_monic hf 0).ne_zero, biFibre_natDegree hf]
    exact_mod_cast hdeg
  have hmem : ((0 : ℂ), T₀) ∈ BiRootLocus f := by
    show biEval f ((0 : ℂ), T₀) = 0
    rw [biEval_eq_eval_biFibre]
    exact hT₀
  obtain ⟨G, ⟨-, hGlift⟩, -⟩ :=
    (isCoveringMap_biRootProj hf hdeg hsep).existsUnique_continuousMap_lifts
      (ContinuousMap.id ℂ) (0 : ℂ) ⟨((0 : ℂ), T₀), hmem⟩ rfl
  refine ⟨fun s => ((G s : ℂ × ℂ)).2, (continuous_snd.comp continuous_subtype_val).comp G.continuous,
    fun s => ?_⟩
  have hs : ((G s : ℂ × ℂ)).1 = s := congrFun hGlift s
  have h2 : biEval f ((G s : ℂ × ℂ)) = 0 := (G s).2
  rwa [show ((G s : ℂ × ℂ)) = (s, ((G s : ℂ × ℂ)).2) from Prod.ext hs rfl] at h2

/-- Every continuous root branch is analytic. -/
theorem analyticAt_of_continuous_biRoot {f : ℂ[X][X]}
    (hsep : ∀ s : ℂ, (biFibre f s).Separable) {g : ℂ → ℂ} (hg : Continuous g)
    (hroot : ∀ s, biEval f (s, g s) = 0) (s₀ : ℂ) : AnalyticAt ℂ g s₀ := by
  have hmem : (s₀, g s₀) ∈ BiRootLocus f := hroot s₀
  set e : BiRootLocus f := ⟨(s₀, g s₀), hmem⟩ with he
  obtain ⟨r, hr, hrs, hrroot⟩ :=
    HolomorphicIFT.holo_implicit (analyticAt_biEval f (s₀, g s₀)) (hroot s₀)
      (by simpa using biRootLocus_partial_ne e (hsep _))
  obtain ⟨φ, hφmem, hφeq⟩ := isLocalHomeomorph_biRootProj hsep e
  obtain ⟨U, hU, hUeq⟩ : ∃ U : Set (ℂ × ℂ), IsOpen U ∧
      φ.source = (fun q : BiRootLocus f => (q : ℂ × ℂ)) ⁻¹' U := by
    have := φ.open_source
    rw [isOpen_induced_iff] at this
    obtain ⟨U, hU, hUeq⟩ := this
    exact ⟨U, hU, hUeq.symm⟩
  have hmemU : (s₀, g s₀) ∈ U := by
    have : e ∈ φ.source := hφmem
    rwa [hUeq] at this
  have hev1 : ∀ᶠ s in 𝓝 s₀, (s, g s) ∈ U :=
    (continuous_id.prodMk hg).continuousAt.preimage_mem_nhds (hU.mem_nhds hmemU)
  have hev2 : ∀ᶠ s in 𝓝 s₀, (s, r s) ∈ U := by
    have hrc : ContinuousAt r s₀ := hr.continuousAt
    have : ContinuousAt (fun s => (s, r s)) s₀ := continuousAt_id.prodMk hrc
    exact this.preimage_mem_nhds (hU.mem_nhds (by rw [hrs]; exact hmemU))
  have hgr : ∀ᶠ s in 𝓝 s₀, g s = r s := by
    filter_upwards [hev1, hev2, hrroot] with s h1 h2 h3
    have hq1 : (s, g s) ∈ BiRootLocus f := hroot s
    have hq2 : (s, r s) ∈ BiRootLocus f := h3
    have hs1 : (⟨(s, g s), hq1⟩ : BiRootLocus f) ∈ φ.source := by rw [hUeq]; exact h1
    have hs2 : (⟨(s, r s), hq2⟩ : BiRootLocus f) ∈ φ.source := by rw [hUeq]; exact h2
    have : (⟨(s, g s), hq1⟩ : BiRootLocus f) = ⟨(s, r s), hq2⟩ := by
      apply φ.injOn hs1 hs2
      have h1' : (φ : BiRootLocus f → ℂ) ⟨(s, g s), hq1⟩ = s := by
        rw [← hφeq]; rfl
      have h2' : (φ : BiRootLocus f → ℂ) ⟨(s, r s), hq2⟩ = s := by
        rw [← hφeq]; rfl
      rw [h1', h2']
    exact congrArg (fun q : BiRootLocus f => (q : ℂ × ℂ).2) this
  exact hr.congr (Filter.EventuallyEq.symm hgr)

/-- The same, needing separability only at the point. -/
theorem analyticAt_of_continuous_biRoot_at {f : ℂ[X][X]} {g : ℂ → ℂ} (hg : Continuous g)
    (hroot : ∀ s, biEval f (s, g s) = 0) (s₀ : ℂ)
    (hsep0 : (biFibre f s₀).Separable) : AnalyticAt ℂ g s₀ := by
  have hmem : (s₀, g s₀) ∈ BiRootLocus f := hroot s₀
  set e : BiRootLocus f := ⟨(s₀, g s₀), hmem⟩ with he
  obtain ⟨r, hr, hrs, hrroot⟩ :=
    HolomorphicIFT.holo_implicit (analyticAt_biEval f (s₀, g s₀)) (hroot s₀)
      (by simpa using biRootLocus_partial_ne e hsep0)
  obtain ⟨φ, hφmem, hφeq⟩ := exists_chart_biRootProj e hsep0
  obtain ⟨U, hU, hUeq⟩ : ∃ U : Set (ℂ × ℂ), IsOpen U ∧
      φ.source = (fun q : BiRootLocus f => (q : ℂ × ℂ)) ⁻¹' U := by
    have := φ.open_source
    rw [isOpen_induced_iff] at this
    obtain ⟨U, hU, hUeq⟩ := this
    exact ⟨U, hU, hUeq.symm⟩
  have hmemU : (s₀, g s₀) ∈ U := by
    have : e ∈ φ.source := hφmem
    rwa [hUeq] at this
  have hev1 : ∀ᶠ s in 𝓝 s₀, (s, g s) ∈ U :=
    (continuous_id.prodMk hg).continuousAt.preimage_mem_nhds (hU.mem_nhds hmemU)
  have hev2 : ∀ᶠ s in 𝓝 s₀, (s, r s) ∈ U := by
    have hrc : ContinuousAt r s₀ := hr.continuousAt
    have : ContinuousAt (fun s => (s, r s)) s₀ := continuousAt_id.prodMk hrc
    exact this.preimage_mem_nhds (hU.mem_nhds (by rw [hrs]; exact hmemU))
  have hgr : ∀ᶠ s in 𝓝 s₀, g s = r s := by
    filter_upwards [hev1, hev2, hrroot] with s h1 h2 h3
    have hq1 : (s, g s) ∈ BiRootLocus f := hroot s
    have hq2 : (s, r s) ∈ BiRootLocus f := h3
    have hs1 : (⟨(s, g s), hq1⟩ : BiRootLocus f) ∈ φ.source := by rw [hUeq]; exact h1
    have hs2 : (⟨(s, r s), hq2⟩ : BiRootLocus f) ∈ φ.source := by rw [hUeq]; exact h2
    have : (⟨(s, g s), hq1⟩ : BiRootLocus f) = ⟨(s, r s), hq2⟩ := by
      apply φ.injOn hs1 hs2
      have h1' : (φ : BiRootLocus f → ℂ) ⟨(s, g s), hq1⟩ = s := by
        rw [← hφeq]; rfl
      have h2' : (φ : BiRootLocus f → ℂ) ⟨(s, r s), hq2⟩ = s := by
        rw [← hφeq]; rfl
      rw [h1', h2']
    exact congrArg (fun q : BiRootLocus f => (q : ℂ × ℂ).2) this
  exact hr.congr (Filter.EventuallyEq.symm hgr)

/-- Norm bound for polynomial evaluation. -/
theorem norm_eval_le_sum (p : ℂ[X]) (x : ℂ) :
    ‖p.eval x‖ ≤ (∑ i ∈ Finset.range (p.natDegree + 1), ‖p.coeff i‖) * (max 1 ‖x‖) ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro i hi
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine (pow_le_pow_left₀ (norm_nonneg _) (le_max_right 1 ‖x‖) i).trans ?_
  exact pow_le_pow_right₀ (le_max_left 1 ‖x‖)
    (by simpa using Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))

/-- **A global root branch is a polynomial.** -/
theorem exists_polynomial_biRoot {f : ℂ[X][X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsep : ∀ s : ℂ, (biFibre f s).Separable) :
    ∃ Q : ℂ[X], ∀ s : ℂ, biEval f (s, Q.eval s) = 0 := by
  classical
  obtain ⟨g, hgc, hgroot⟩ := exists_continuous_biRoot hf hdeg hsep
  have hgdiff : Differentiable ℂ g := fun s =>
    (analyticAt_of_continuous_biRoot hsep hgc hgroot s).differentiableAt
  set N : ℕ := (Finset.range f.natDegree).sup (fun i => (f.coeff i).natDegree) with hN
  set A : ℝ := ∑ i ∈ Finset.range f.natDegree,
      ∑ j ∈ Finset.range ((f.coeff i).natDegree + 1), ‖(f.coeff i).coeff j‖ with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hgrowth : ∀ s : ℂ, ‖g s‖ ≤ (1 + A) * (max 1 ‖s‖) ^ N := by
    intro s
    set M : ℝ := max 1 ‖s‖ with hM
    have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
    have hMN : (1 : ℝ) ≤ M ^ N := one_le_pow₀ hM1
    have hbound : ∑ i ∈ Finset.range f.natDegree, ‖(f.coeff i).eval s‖ ≤ A * M ^ N := by
      rw [hA, Finset.sum_mul]
      refine Finset.sum_le_sum ?_
      intro i hi
      refine (norm_eval_le_sum (f.coeff i) s).trans ?_
      refine mul_le_mul_of_nonneg_left ?_
        (Finset.sum_nonneg fun j _ => norm_nonneg _)
      have hle : (f.coeff i).natDegree ≤ N := by
        rw [hN]
        exact Finset.le_sup (f := fun i => (f.coeff i).natDegree) hi
      exact pow_le_pow_right₀ hM1 hle
    have hq : ((s, g s) : ℂ × ℂ) ∈ BiRootLocus f := hgroot s
    have h1 := biRootLocus_norm_le hf hdeg ⟨(s, g s), hq⟩
    simp only at h1
    refine h1.trans ?_
    have h2 : max 1 (∑ i ∈ Finset.range f.natDegree, ‖(f.coeff i).eval s‖) ≤ 1 + A * M ^ N := by
      refine max_le (by nlinarith) (hbound.trans (le_add_of_nonneg_left zero_le_one))
    refine h2.trans ?_
    nlinarith [mul_nonneg hA0 (le_of_lt (lt_of_lt_of_le zero_lt_one hMN))]
  obtain ⟨Q, hQ⟩ := Bottcher.exists_polynomial_of_entire_polyGrowth hgdiff hgrowth
  exact ⟨Q, fun s => by rw [← hQ s]; exact hgroot s⟩

theorem eval_eval_eq_biEval (f : ℂ[X][X]) (Q : ℂ[X]) (x : ℂ) :
    (f.eval Q).eval x = biEval f (x, Q.eval x) := by
  have h := Polynomial.hom_eval₂ f (RingHom.id ℂ[X]) (Polynomial.evalRingHom x) Q
  rw [RingHom.comp_id] at h
  change (Polynomial.evalRingHom x) (Polynomial.eval₂ (RingHom.id ℂ[X]) Q f) = _ at h
  rw [Polynomial.eval₂_id] at h
  exact h

/-- **A monic linear factor over the coefficient ring.** -/
theorem exists_monic_linear_factor {f : ℂ[X][X]} (hf : f.Monic) (hdeg : 0 < f.natDegree)
    (hsep : ∀ s : ℂ, (biFibre f s).Separable) :
    ∃ Q : ℂ[X], (X - Polynomial.C Q) ∣ f := by
  obtain ⟨Q, hQ⟩ := exists_polynomial_biRoot hf hdeg hsep
  refine ⟨Q, ?_⟩
  rw [Polynomial.dvd_iff_isRoot]
  apply Polynomial.zero_of_eval_zero
  intro x
  rw [eval_eval_eq_biEval]
  exact hQ x

/-- **A monic two-variable polynomial whose every fibre is separable splits into monic linear
factors.**  This is the algebraic simple connectedness of the complex affine line. -/
theorem exists_multiset_prod_of_forall_separable :
    ∀ (d : ℕ) (f : ℂ[X][X]), f.Monic → f.natDegree = d →
      (∀ s : ℂ, (biFibre f s).Separable) →
      ∃ L : Multiset ℂ[X], f = (L.map (fun a => X - Polynomial.C a)).prod := by
  intro d
  induction d with
  | zero =>
      intro f hf hdeg _
      refine ⟨0, ?_⟩
      simp only [Multiset.map_zero, Multiset.prod_zero]
      exact (Polynomial.eq_one_of_monic_natDegree_zero hf hdeg)
  | succ n ih =>
      intro f hf hdeg hsep
      obtain ⟨Q, h₀, hfac⟩ : ∃ Q h₀, f = (X - Polynomial.C Q) * h₀ := by
        obtain ⟨Q, hQ⟩ := exists_monic_linear_factor hf (by omega) hsep
        obtain ⟨h₀, hh₀⟩ := hQ
        exact ⟨Q, h₀, hh₀⟩
      have hlinmonic : (X - Polynomial.C Q : ℂ[X][X]).Monic := Polynomial.monic_X_sub_C Q
      have hh0monic : h₀.Monic := by
        have := hf
        rw [hfac] at this
        exact hlinmonic.of_mul_monic_left this
      have hdeg0 : h₀.natDegree = n := by
        have := congrArg Polynomial.natDegree hfac
        rw [hlinmonic.natDegree_mul hh0monic, Polynomial.natDegree_X_sub_C] at this
        omega
      have hsep0 : ∀ s : ℂ, (biFibre h₀ s).Separable := by
        intro s
        have hdvd : biFibre h₀ s ∣ biFibre f s := by
          rw [hfac, biFibre_mul]
          exact Dvd.intro_left _ rfl
        exact (hsep s).of_dvd hdvd
      obtain ⟨L, hL⟩ := ih h₀ hh0monic hdeg0 hsep0
      refine ⟨Q ::ₘ L, ?_⟩
      rw [Multiset.map_cons, Multiset.prod_cons, ← hL, hfac]

end

end GaloisForLFunctions.HTGeometry
