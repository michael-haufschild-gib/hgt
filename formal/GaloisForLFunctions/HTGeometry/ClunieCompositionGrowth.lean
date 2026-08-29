import GaloisForLFunctions.HTGeometry.CompositionValueCounting
import GaloisForLFunctions.HTGeometry.ValuePreimageInfinite

/-!
# Clunie's composition growth theorem

For transcendental entire `f` and `g` the characteristic of `f ∘ g` outgrows every multiple of the
characteristic of `g`.

The proof needs no minimum-modulus estimate.  A transcendental entire `f` takes some value `a` at
`n` distinct points `b_1, …, b_n`; every `b_j`-point of `g` is an `a`-point of `f ∘ g` of at least
the same multiplicity, so `N(r, a, f∘g) ≥ ∑_j N(r, b_j, g)`.  The second main theorem for `g` at the
`n` separated values `b_j` bounds the right-hand side below by `(n−2)T(r,g) − S(r,g)`, and the error
term is negligible along a sequence of radii.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric Real Set Filter ValueDistribution MeromorphicOn
open scoped Topology

/-- An entire function that is not a polynomial takes no value on a whole neighbourhood. -/
theorem meromorphicOrderAt_sub_const_ne_top {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (hnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, F z = p.eval z) (c : ℂ) (z : ℂ) :
    meromorphicOrderAt (fun w => F w - c) z ≠ ⊤ := by
  intro hcon
  have hdiff : Differentiable ℂ fun w => F w - c := hF.sub (differentiable_const _)
  have hfan : AnalyticOnNhd ℂ (fun w => F w - c) Set.univ :=
    hdiff.differentiableOn.analyticOnNhd isOpen_univ
  rw [meromorphicOrderAt_eq_top_iff] at hcon
  have hall := hfan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z) hcon.frequently
  refine hnp ⟨Polynomial.C c, fun w => ?_⟩
  have h := hall (Set.mem_univ w)
  simp only [Pi.zero_apply] at h
  simp only [Polynomial.eval_C]
  linear_combination h

/-- A composition of transcendental entire functions is nowhere locally constant. -/
theorem meromorphicOrderAt_comp_sub_const_ne_top {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z) (a : ℂ) (z : ℂ) :
    meromorphicOrderAt (fun w => f (g w) - a) z ≠ ⊤ := by
  intro hcon
  have hcomp : Differentiable ℂ fun w => f (g w) := fun x => (hf (g x)).comp x (hg x)
  have hdiff : Differentiable ℂ fun w => f (g w) - a := hcomp.sub (differentiable_const _)
  have hfan : AnalyticOnNhd ℂ (fun w => f (g w) - a) Set.univ :=
    hdiff.differentiableOn.analyticOnNhd isOpen_univ
  rw [meromorphicOrderAt_eq_top_iff] at hcon
  have hall := hfan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
    (Set.mem_univ z) hcon.frequently
  have hfga : ∀ w : ℂ, f (g w) = a := by
    intro w
    have h := hall (Set.mem_univ w)
    simp only [Pi.zero_apply] at h
    linear_combination h
  -- `g` is not constant near `0`, so its image is a neighbourhood of `g 0`
  have hgnc : ¬ ∀ᶠ w in 𝓝 (0 : ℂ), g w = g 0 := by
    intro hev
    refine hgnp ⟨Polynomial.C (g 0), fun w => ?_⟩
    have hzero : meromorphicOrderAt (fun w => g w - g 0) 0 = ⊤ := by
      rw [meromorphicOrderAt_eq_top_iff]
      filter_upwards [nhdsWithin_le_nhds hev] with x hx
      simp [hx]
    have := meromorphicOrderAt_sub_const_ne_top hg hgnp (g 0) 0
    exact absurd hzero this
  have hmap := (hg.analyticAt (0 : ℂ)).eventually_constant_or_nhds_le_map_nhds
  rcases hmap with h | h
  · exact absurd h hgnc
  · have hev : ∀ᶠ v in 𝓝 (g 0), f v - a = 0 := by
      refine h ?_
      rw [Filter.mem_map]
      filter_upwards with w
      simp [Set.mem_preimage, hfga w]
    have hforder : meromorphicOrderAt (fun w => f w - a) (g 0) = ⊤ := by
      rw [meromorphicOrderAt_eq_top_iff]
      exact nhdsWithin_le_nhds hev
    exact absurd hforder (meromorphicOrderAt_sub_const_ne_top hf hfnp a (g 0))

/-- **Clunie's composition growth theorem.**  For transcendental entire `f` and `g` and every `n`,
the characteristic of `f ∘ g` dominates `(n − 3)` times the characteristic of `g` along a sequence
of radii tending to infinity. -/
theorem exists_clunie_composition_growth {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z) (n : ℕ) :
    ∃ C : ℝ, ∃ᶠ r in atTop,
      ((n : ℝ) - 3) * characteristic g ⊤ r
        ≤ characteristic (fun w => f (g w)) ⊤ r + C := by
  classical
  obtain ⟨a, hainf⟩ := exists_infinite_preimage_of_not_polynomial hf hfnp
  obtain ⟨B, hBsub, hBcard⟩ := hainf.exists_subset_card_eq n
  set A : Fin n → ℂ := fun j => ((B.equivFin.symm (finCongr hBcard.symm j) : B) : ℂ) with hA
  have hAmem : ∀ j, A j ∈ B := fun j => (B.equivFin.symm (finCongr hBcard.symm j)).2
  have hAinj : Function.Injective A := by
    intro i j hij
    have h1 : (B.equivFin.symm (finCongr hBcard.symm i))
        = (B.equivFin.symm (finCongr hBcard.symm j)) := Subtype.ext hij
    have h2 := B.equivFin.symm.injective h1
    exact (finCongr hBcard.symm).injective h2
  have hfA : ∀ j, f (A j) = a := fun j => hBsub (Finset.mem_coe.mpr (hAmem j))
  -- the values are separated
  set P : Finset (ℂ × ℂ) := (B ×ˢ B).filter (fun p => p.1 ≠ p.2) with hP
  set δ : ℝ := if h : P.Nonempty then P.inf' h (fun p => ‖p.1 - p.2‖) else 1 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    split_ifs with h
    · rw [Finset.lt_inf'_iff]
      intro p hp
      have hne := (Finset.mem_filter.mp hp).2
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hne)
    · norm_num
  have hsep : ∀ i j : Fin n, i ≠ j → δ ≤ ‖A i - A j‖ := by
    intro i j hij
    have hne : A i ≠ A j := fun hcon => hij (hAinj hcon)
    have hmem : (A i, A j) ∈ P := by
      rw [hP, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hAmem i, hAmem j⟩, hne⟩
    have hPne : P.Nonempty := ⟨_, hmem⟩
    rw [hδdef, dif_pos hPne]
    exact Finset.inf'_le _ hmem
  -- nondegeneracy
  have hgo : ∀ j : Fin n, ∀ z, meromorphicOrderAt (fun w => g w - A j) z ≠ ⊤ :=
    fun j z => meromorphicOrderAt_sub_const_ne_top hg hgnp (A j) z
  have hg0 : ∀ z, meromorphicOrderAt g z ≠ ⊤ := by
    intro z
    have h := meromorphicOrderAt_sub_const_ne_top hg hgnp 0 z
    simpa using h
  have hco := meromorphicOrderAt_comp_sub_const_ne_top hf hg hfnp hgnp a
  have hgd : ∀ z, meromorphicOrderAt (deriv g) z ≠ ⊤ := by
    intro z hcon
    have hgan : AnalyticOnNhd ℂ g Set.univ := hg.differentiableOn.analyticOnNhd isOpen_univ
    have hdan : AnalyticOnNhd ℂ (deriv g) Set.univ := hgan.deriv
    rw [meromorphicOrderAt_eq_top_iff] at hcon
    have hall := hdan.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (Set.mem_univ z) hcon.frequently
    have hconst : ∀ x y : ℂ, g x = g y :=
      fun x y => is_const_of_deriv_eq_zero hg (fun w => by simpa using hall (Set.mem_univ w)) x y
    exact hgnp ⟨Polynomial.C (g 0), fun w => by simpa using hconst w 0⟩
  have hcod : ∀ r : ℝ, ∀ᶠ z in codiscreteWithin (sphere (0 : ℂ) |r|), deriv g z ≠ 0 := by
    intro r
    have hgan : AnalyticOnNhd ℂ g Set.univ := hg.differentiableOn.analyticOnNhd isOpen_univ
    have hdan : AnalyticOnNhd ℂ (deriv g) Set.univ := hgan.deriv
    have hmero : MeromorphicOn (deriv g) (sphere (0 : ℂ) |r|) :=
      fun x _ => (hdan x (Set.mem_univ x)).meromorphicAt
    exact MeromorphicAt.MeromorphicOn.codiscreteWithin_setOf_ne_zero hmero fun u _ => hgd u
  -- the second main theorem for `g` and the good radii
  obtain ⟨Csmt, hsmt⟩ := exists_sub_two_characteristic_le_sum_logCounting hg A hδpos hsep hg0
  obtain ⟨hTtop, hTlog⟩ := charMajorant_growth_of_not_polynomial hg hgnp
  obtain ⟨rn, hrntop, hTeq, hneg⟩ := exists_good_radii_error_negligible hg A hg0 hgo hTlog hTtop
  -- the first main theorem for the composite
  have hcomp : Differentiable ℂ fun w => f (g w) := fun x => (hf (g x)).comp x (hg x)
  have hmcomp : Meromorphic (fun w => f (g w)) := fun z => (hcomp.analyticAt z).meromorphicAt
  have hmsub : Meromorphic (((fun w => f (g w)) - fun _ : ℂ => a) : ℂ → ℂ) := by
    intro z
    exact (hmcomp z).sub (analyticAt_const.meromorphicAt)
  set Ka : ℝ := (Real.posLog ‖a‖ + Real.log 2)
      + max |Real.log ‖(((fun w => f (g w)) - fun _ : ℂ => a) : ℂ → ℂ) 0‖|
          |Real.log ‖meromorphicTrailingCoeffAt
            (((fun w => f (g w)) - fun _ : ℂ => a) : ℂ → ℂ) 0‖| with hKa
  have hfmt : ∀ r : ℝ, 1 ≤ r →
      logCounting (fun w => f (g w)) (a : WithTop ℂ) r
        ≤ characteristic (fun w => f (g w)) ⊤ r + Ka := by
    intro r hr
    have h1 : characteristic (fun w => f (g w)) (a : WithTop ℂ) r
        = proximity (fun w => f (g w)) (a : WithTop ℂ) r
          + logCounting (fun w => f (g w)) (a : WithTop ℂ) r := rfl
    have h2 : 0 ≤ proximity (fun w => f (g w)) (a : WithTop ℂ) r :=
      ValueDistribution.proximity_nonneg r
    have h3 := characteristic_coe_le_characteristic_top (f := fun w => f (g w)) (a₀ := a) (r := r)
      hmcomp hmsub
    rw [hKa]
    linarith
  -- assemble along the good radii
  refine ⟨Ka + Csmt, ?_⟩
  intro hne
  have hcomp' := hrntop.eventually hne
  have hgood : ∀ᶠ k in atTop, ((n : ℝ) - 3) * characteristic g ⊤ (rn k)
      ≤ characteristic (fun w => f (g w)) ⊤ (rn k) + (Ka + Csmt) := by
    filter_upwards [hTeq, hneg 1 one_pos, hrntop.eventually_ge_atTop (1 : ℝ)] with k heq hng hr1
    have hsmtk := hsmt (rn k) hr1 (hcod (rn k))
    have hbridge := sum_logCounting_le_logCounting_comp hf hg A hAinj hfA hgo hco hr1
    have hfmtk := hfmt (rn k) hr1
    rw [heq] at hng
    linarith
  obtain ⟨k, hk1, hk2⟩ := (hcomp'.and hgood).exists
  exact hk1 hk2

/-- **The composition outgrows every linear bound in the inner characteristic.**  This is the form
an algebraicity argument consumes: if `f ∘ g` were algebraic of degree `c` over a field generated by
finitely many derivatives of `g`, its characteristic would obey such a bound. -/
theorem not_eventually_characteristic_comp_le {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g)
    (hfnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, f z = p.eval z)
    (hgnp : ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, g z = p.eval z) (c d : ℝ) :
    ¬ (∀ᶠ r in atTop, characteristic (fun w => f (g w)) ⊤ r
        ≤ c * characteristic g ⊤ r + d * Real.log r + d) := by
  intro hbound
  set n : ℕ := ⌈c⌉₊ + 4 with hn
  obtain ⟨C, hclunie⟩ := exists_clunie_composition_growth hf hg hfnp hgnp n
  have hnc : c + 1 ≤ (n : ℝ) - 3 := by
    have h := Nat.le_ceil c
    rw [hn]
    push_cast
    linarith
  have hdiv := tendsto_characteristic_div_log_atTop hg hgnp
  have hlarge : ∀ᶠ r in atTop,
      d * Real.log r + d + (C + |d|) < characteristic g ⊤ r := by
    have hev := hdiv.eventually_ge_atTop (|d| + |d + (C + |d|)| + 1)
    filter_upwards [hev, eventually_ge_atTop (Real.exp 1)] with r hr hre
    have hr1 : (1 : ℝ) ≤ r := le_trans (le_trans (by norm_num) (Real.add_one_le_exp 1)) hre
    have hlog : (1 : ℝ) ≤ Real.log r := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact hre
    rw [le_div_iff₀ (by linarith)] at hr
    nlinarith [le_abs_self d, le_abs_self (d + (C + |d|)), abs_nonneg d,
      abs_nonneg (d + (C + |d|))]
  have hcontra : ∀ᶠ r in atTop, ¬ (((n : ℝ) - 3) * characteristic g ⊤ r
      ≤ characteristic (fun w => f (g w)) ⊤ r + C) := by
    filter_upwards [hbound, hlarge, hdiv.eventually_gt_atTop (0 : ℝ),
      eventually_ge_atTop (Real.exp 1)] with r hb hl hpos hre
    intro hcon
    have hr1 : (1 : ℝ) ≤ r := le_trans (le_trans (by norm_num) (Real.add_one_le_exp 1)) hre
    have hT0 : 0 ≤ characteristic g ⊤ r := ValueDistribution.characteristic_nonneg hr1
    have habs : (0 : ℝ) ≤ |d| := abs_nonneg d
    nlinarith [hcon, hb, hl, hnc, hT0, habs]
  exact (hclunie.and_eventually hcontra).exists.elim fun _ h => h.2 h.1

end GaloisForLFunctions.HTGeometry
