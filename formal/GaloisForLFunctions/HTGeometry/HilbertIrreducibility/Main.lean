/-
# Hilbert's irreducibility theorem

`ℚ` is a Hilbertian field: an irreducible `f ∈ ℚ[X][Y]` of positive degree in `Y` stays irreducible
under infinitely many rational specialisations of `X`.

The proof is the elementary analytic argument of Coleman--Zwald (arXiv:1809.10977, Theorem 7),
assembled here from
`AnalyticBranches` (analytic root branches at a regular integer point),
`SubsetCoefficients` (steps 1 and 2: the subset coefficients are not rational functions, and their
irrationality at a point forces the fibre to be irreducible),
`MonicScaling`/`GermIntegral` (the scaled branches are integral over `ℤ[X]`),
`Core` (the gap theorem for a single non-rational algebraic germ) and
`ThinSets` (finitely many gap-thin sets do not cover the integers).
-/
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.SubsetCoefficients
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.MonicScaling
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.AnalyticCoefficients
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial Filter Topology

/-- A nonzero complex polynomial does not vanish at every integer. -/
theorem exists_int_not_root {p : Polynomial ℂ} (hp : p ≠ 0) :
    ∃ m : ℤ, p.eval ((m : ℤ) : ℂ) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  refine hp (Polynomial.eq_zero_of_infinite_isRoot p ?_)
  refine Set.infinite_of_injective_forall_mem
    (f := fun m : ℤ => ((m : ℤ) : ℂ))
    (fun a b h => by
      have h' : ((a : ℤ) : ℂ) = ((b : ℤ) : ℂ) := h
      exact_mod_cast h') ?_
  exact fun m => hcon m

theorem toC_eq_map_toQ (f : Polynomial (Polynomial ℤ)) :
    toC f = (toQ f).map (Polynomial.mapRingHom (algebraMap ℚ ℂ)) := by
  rw [toQ, toC, Polynomial.map_map]
  congr 1
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_map]
  congr 1

theorem leadingCoeff_toC (f : Polynomial (Polynomial ℤ)) (s : ℂ) :
    (toC f).leadingCoeff.eval s = Polynomial.aeval s f.leadingCoeff := by
  have hinj : Function.Injective (Polynomial.mapRingHom (Int.castRingHom ℂ) :
      Polynomial ℤ →+* Polynomial ℂ) := fun a b hab =>
    Polynomial.map_injective (Int.castRingHom ℂ) Int.cast_injective hab
  have hdeg : (toC f).natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective hinj f
  rw [Polynomial.leadingCoeff, hdeg, toC, Polynomial.coeff_map]
  simp only [Polynomial.coe_mapRingHom, Polynomial.eval_map, Polynomial.aeval_def]
  congr 1

/-- **A regular integer parameter exists.** -/
theorem exists_regular_int {f : Polynomial (Polynomial ℤ)} {n : ℕ} (hn : f.natDegree = n)
    (hn1 : 1 ≤ n)
    (hsep : ((toQ f).map (algebraMap (Polynomial ℚ)
      (FractionRing (Polynomial ℚ)))).Separable) :
    ∃ s₀ : ℤ, Polynomial.aeval ((s₀ : ℤ) : ℂ) f.leadingCoeff ≠ 0 ∧
      ((toC f).map (Polynomial.evalRingHom ((s₀ : ℤ) : ℂ))).Separable := by
  classical
  set ψ : Polynomial ℚ →+* Polynomial ℂ := Polynomial.mapRingHom (algebraMap ℚ ℂ) with hψ
  have hcastinj : Function.Injective (algebraMap ℚ ℂ) := (algebraMap ℚ ℂ).injective
  have hψinj : Function.Injective ψ := fun a b hab =>
    Polynomial.map_injective _ hcastinj hab
  have hQdeg : (toQ f).natDegree = n := by rw [natDegree_toQ, hn]
  have hCdeg : (toC f).natDegree = n := by
    rw [toC_eq_map_toQ, Polynomial.natDegree_map_eq_of_injective hψinj, hQdeg]
  have hCne : toC f ≠ 0 := by
    intro h
    rw [h] at hCdeg
    simp only [Polynomial.natDegree_zero] at hCdeg
    omega
  have hderivCne : Polynomial.derivative (toC f) ≠ 0 := by
    intro h
    have := Polynomial.derivative_eq_zero.mp h
    rw [hCdeg] at this
    omega
  have hresQ : Polynomial.resultant (toQ f) (Polynomial.derivative (toQ f)) ≠ 0 :=
    HolomorphicIFT.resultant_ne_zero_of_separable (toQ f) hsep
  have hd1 : ((toQ f).map ψ).natDegree = (toQ f).natDegree :=
    Polynomial.natDegree_map_eq_of_injective hψinj _
  have hd2 : ((Polynomial.derivative (toQ f)).map ψ).natDegree
      = (Polynomial.derivative (toQ f)).natDegree :=
    Polynomial.natDegree_map_eq_of_injective hψinj _
  have hmapderiv : (Polynomial.derivative (toQ f)).map ψ = Polynomial.derivative (toC f) := by
    rw [toC_eq_map_toQ, Polynomial.derivative_map]
  have hargs : Polynomial.resultant (toQ f) (Polynomial.derivative (toQ f))
      (((toQ f).map ψ).natDegree) (((Polynomial.derivative (toQ f)).map ψ).natDegree)
      = Polynomial.resultant (toQ f) (Polynomial.derivative (toQ f)) := by rw [hd1, hd2]
  have hkey := Polynomial.resultant_map_map (toQ f) (Polynomial.derivative (toQ f))
    (((toQ f).map ψ).natDegree) (((Polynomial.derivative (toQ f)).map ψ).natDegree) ψ
  rw [hargs, ← toC_eq_map_toQ, hmapderiv] at hkey
  have hresC : Polynomial.resultant (toC f) (Polynomial.derivative (toC f)) ≠ 0 := by
    rw [hkey]
    intro h
    exact hresQ (hψinj (by rw [h]; simp))
  set p : Polynomial ℂ := (toC f).leadingCoeff * (Polynomial.derivative (toC f)).leadingCoeff
    * Polynomial.resultant (toC f) (Polynomial.derivative (toC f)) with hp
  have hpne : p ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) hresC
    · exact Polynomial.leadingCoeff_ne_zero.mpr hCne
    · exact Polynomial.leadingCoeff_ne_zero.mpr hderivCne
  obtain ⟨s₀, hs₀⟩ := exists_int_not_root hpne
  rw [hp] at hs₀
  simp only [Polynomial.eval_mul] at hs₀
  have h1 : (toC f).leadingCoeff.eval ((s₀ : ℤ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hs₀; simp at hs₀
  have h2 : (Polynomial.derivative (toC f)).leadingCoeff.eval ((s₀ : ℤ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hs₀; simp at hs₀
  have h3 : (Polynomial.resultant (toC f) (Polynomial.derivative (toC f))).eval
      ((s₀ : ℤ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hs₀; simp at hs₀
  exact ⟨s₀, by rw [← leadingCoeff_toC]; exact h1,
    HolomorphicIFT.separable_specialize _ h1 h2 h3⟩

theorem bivEval_eq_eval_fibre (f : Polynomial (Polynomial ℤ)) (s y : ℂ) :
    bivEval f s y = ((toC f).map (Polynomial.evalRingHom s)).eval y := by
  rw [toC, Polynomial.map_map, Polynomial.eval_map, bivEval]
  congr 1
  exact RingHom.ext fun z => by simp [Polynomial.aeval_def, Polynomial.eval_map]

theorem aeval_map_int {A : Type*} [CommRing A] [Algebra ℚ A] (p : Polynomial ℤ) (s : A) :
    Polynomial.aeval s (p.map (Int.castRingHom ℚ)) = Polynomial.aeval s p := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map]
  congr 1
  exact RingHom.ext fun z => by simp

theorem aeval_int_ratCast (p : Polynomial ℤ) (b : ℚ) :
    Polynomial.aeval (((b : ℚ) : ℂ)) p
      = ((Polynomial.aeval b p : ℚ) : ℂ) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def]
  have h := Polynomial.hom_eval₂ p (Int.castRingHom ℚ) (Rat.castHom ℂ) b
  rw [show ((Rat.castHom ℂ).comp (Int.castRingHom ℚ)) = Int.castRingHom ℂ from
    RingHom.ext fun z => by simp] at h
  simpa using h.symm

/-- **The scaled branches are integral over `ℤ[X]` as germs.** -/
theorem isIntegral_scaled_branch {f : Polynomial (Polynomial ℤ)} {n : ℕ} (hn : f.natDegree = n)
    (hn1 : 1 ≤ n) {s₀ : ℂ} {w : ℂ → ℂ} (hrel : ∀ᶠ s in 𝓝 s₀, bivEval f s (w s) = 0) :
    IsIntegral (Polynomial ℤ)
      (((fun s => Polynomial.aeval s f.leadingCoeff * w s : ℂ → ℂ)) : Germ (𝓝 s₀) ℂ) := by
  refine isIntegral_of_monic_bivariate (monic_monicScale f n) ?_
  filter_upwards [hrel] with s hs
  rw [bivEval_monicScale hn hn1, hs, mul_zero]

/-- **Hilbert's irreducibility theorem, integral form.** -/
theorem hilbert_irreducibility_int {f : Polynomial (Polynomial ℤ)} {n : ℕ}
    (hn : f.natDegree = n) (hn1 : 1 ≤ n)
    (hirr : Irreducible ((toQ f).map (algebraMap (Polynomial ℚ)
      (FractionRing (Polynomial ℚ))))) :
    {b : ℚ | Irreducible ((toQ f).map (Polynomial.evalRingHom b))}.Infinite := by
  classical
  have hsep : ((toQ f).map (algebraMap (Polynomial ℚ)
      (FractionRing (Polynomial ℚ)))).Separable := hirr.separable
  obtain ⟨s₀, hlead0, hsepfib⟩ := exists_regular_int hn hn1 hsep
  have hcastinj : Function.Injective (algebraMap ℚ ℂ) := (algebraMap ℚ ℂ).injective
  have hψinj : Function.Injective (Polynomial.mapRingHom (algebraMap ℚ ℂ) :
      Polynomial ℚ →+* Polynomial ℂ) := fun a b hab => Polynomial.map_injective _ hcastinj hab
  have hCdeg : (toC f).natDegree = n := by
    rw [toC_eq_map_toQ, Polynomial.natDegree_map_eq_of_injective hψinj, natDegree_toQ, hn]
  have hleadC0 : (toC f).leadingCoeff.eval ((s₀ : ℤ) : ℂ) ≠ 0 := by
    rw [leadingCoeff_toC]; exact hlead0
  obtain ⟨u, hua, hev⟩ := exists_analytic_branches hCdeg hleadC0 hsepfib
  have hdegs : ∀ᶠ s in 𝓝 (((s₀ : ℤ) : ℂ)),
      ((toC f).map (Polynomial.evalRingHom s)).natDegree = n := by
    filter_upwards [hev] with s hs using hs.2.1
  have hprod : ∀ᶠ s in 𝓝 (((s₀ : ℤ) : ℂ)), ∃ c : ℂ, c ≠ 0 ∧
      (toC f).map (Polynomial.evalRingHom s)
        = Polynomial.C c * ∏ i, (Polynomial.X - Polynomial.C (u i s)) := by
    filter_upwards [hev] with s hs
    obtain ⟨hinj, hdg, hroots⟩ := hs
    have hPsne : (toC f).map (Polynomial.evalRingHom s) ≠ 0 := by
      intro h
      rw [h] at hdg
      simp only [Polynomial.natDegree_zero] at hdg
      omega
    refine ⟨((toC f).map (Polynomial.evalRingHom s)).leadingCoeff,
      Polynomial.leadingCoeff_ne_zero.mpr hPsne, ?_⟩
    have hsplit := Polynomial.Splits.eq_prod_roots
      (IsAlgClosed.splits ((toC f).map (Polynomial.evalRingHom s)))
    rw [hroots, Multiset.map_map] at hsplit
    exact hsplit
  -- the index set of proper nonempty subsets
  set Idx : Type := {S : Finset (Fin n) // S.Nonempty ∧ S ≠ Finset.univ} with hIdx
  have hstep1 : ∀ j : Idx, ∃ k : ℕ, ¬ IsRatGerm (((s₀ : ℤ) : ℂ))
      (fun s => (∏ i ∈ (j : Finset (Fin n)),
        (Polynomial.X - Polynomial.C (u i s))).coeff k) :=
    fun j => exists_not_ratGerm hn hirr hprod hdegs (j : Finset (Fin n)) j.2.1 j.2.2
  choose kk hkk using hstep1
  -- the witness functions
  set cs : ℂ → ℂ := fun s => Polynomial.aeval s f.leadingCoeff with hcs
  set vv : Fin n → ℂ → ℂ := fun i s => cs s * u i s with hvv
  set W : Idx → ℂ → ℂ := fun j s =>
    (∏ i ∈ (j : Finset (Fin n)),
      (Polynomial.C (cs s) * Polynomial.X - Polynomial.C (vv i s))).coeff (kk j) with hW
  have hWval : ∀ (j : Idx) (s : ℂ), W j s
      = (cs s) ^ ((j : Finset (Fin n)).card)
        * (∏ i ∈ (j : Finset (Fin n)), (Polynomial.X - Polynomial.C (u i s))).coeff (kk j) := by
    intro j s
    rw [hW]
    simp only []
    rw [prod_scaled_eq, Polynomial.coeff_C_mul]
  have hcsana : ∀ s₁ : ℂ, AnalyticAt ℂ cs s₁ := fun s₁ =>
    AnalyticAt.aeval_polynomial (analyticAt_id (𝕜 := ℂ) (z := s₁)) f.leadingCoeff
  have hWana : ∀ j : Idx, AnalyticAt ℂ (W j) (((s₀ : ℤ) : ℂ)) := fun j =>
    analyticAt_coeff_prod _ (hcsana _) (fun i => (hcsana _).mul (hua i)) (kk j)
  -- integrality
  have hurel : ∀ i : Fin n, ∀ᶠ s in 𝓝 (((s₀ : ℤ) : ℂ)), bivEval f s (u i s) = 0 := by
    intro i
    filter_upwards [hev] with s hs
    obtain ⟨hinj, hdg, hroots⟩ := hs
    have hPsne : (toC f).map (Polynomial.evalRingHom s) ≠ 0 := by
      intro h
      rw [h] at hdg
      simp only [Polynomial.natDegree_zero] at hdg
      omega
    have hmem : u i s ∈ ((toC f).map (Polynomial.evalRingHom s)).roots := by
      rw [hroots]
      exact Multiset.mem_map_of_mem _ (Finset.mem_univ i)
    rw [bivEval_eq_eval_fibre]
    exact (Polynomial.mem_roots hPsne).mp hmem
  have hvint : ∀ i : Fin n,
      IsIntegral (Polynomial ℤ) ((vv i : ℂ → ℂ) : Germ (𝓝 (((s₀ : ℤ) : ℂ))) ℂ) := fun i =>
    isIntegral_scaled_branch hn hn1 (hurel i)
  have hcsint : IsIntegral (Polynomial ℤ)
      ((cs : ℂ → ℂ) : Germ (𝓝 (((s₀ : ℤ) : ℂ))) ℂ) := by
    have hid : ((cs : ℂ → ℂ) : Germ (𝓝 (((s₀ : ℤ) : ℂ))) ℂ)
        = algebraMap (Polynomial ℤ) (Germ (𝓝 (((s₀ : ℤ) : ℂ))) ℂ) f.leadingCoeff := rfl
    rw [hid]
    exact isIntegral_algebraMap
  have hWint : ∀ j : Idx,
      IsIntegral (Polynomial ℤ) ((W j : ℂ → ℂ) : Germ (𝓝 (((s₀ : ℤ) : ℂ))) ℂ) := by
    intro j
    have hfun : (W j : ℂ → ℂ) = (∏ i ∈ (j : Finset (Fin n)),
        (Polynomial.C (cs : ℂ → ℂ) * Polynomial.X
          - Polynomial.C ((vv i : ℂ → ℂ)))).coeff (kk j) := by
      funext s
      exact (coeff_prod_map (Pi.evalRingHom (fun _ : ℂ => ℂ) s) (j : Finset (Fin n))
        (cs : ℂ → ℂ) (fun i => (vv i : ℂ → ℂ)) (kk j)).symm
    have hcsint' : IsIntegral (Polynomial ℤ)
        ((Germ.coeRingHom (𝓝 (((s₀ : ℤ) : ℂ)))) (cs : ℂ → ℂ)) := hcsint
    have hvint' : ∀ i : Fin n, IsIntegral (Polynomial ℤ)
        ((Germ.coeRingHom (𝓝 (((s₀ : ℤ) : ℂ)))) ((vv i : ℂ → ℂ))) := hvint
    have hgerm := coeff_prod_map (Germ.coeRingHom (𝓝 (((s₀ : ℤ) : ℂ)))) (j : Finset (Fin n))
      (cs : ℂ → ℂ) (fun i => (vv i : ℂ → ℂ)) (kk j)
    rw [hfun]
    show IsIntegral (Polynomial ℤ) ((Germ.coeRingHom (𝓝 (((s₀ : ℤ) : ℂ)))) _)
    rw [hgerm]
    exact isIntegral_coeff_prod _ hcsint' hvint' (kk j)
  -- non-rationality
  have hWnr : ∀ j : Idx, ¬ IsRatGerm (((s₀ : ℤ) : ℂ)) (W j) := by
    intro j hrat
    apply hkk j
    obtain ⟨pp, qq, hq0, hrelq⟩ := hrat
    refine ⟨pp, qq * (f.leadingCoeff.map (Int.castRingHom ℚ)) ^ ((j : Finset (Fin n)).card),
      ?_, ?_⟩
    · rw [map_mul, map_pow, aeval_map_int]
      exact mul_ne_zero hq0 (pow_ne_zero _ hlead0)
    · filter_upwards [hrelq] with s hs
      rw [map_mul, map_pow, aeval_map_int, ← hs, hWval j s]
      ring
  -- gap thinness and the final counting
  have hThin : ∀ j : Idx, Thin {t : ℤ | ∃ c : ℚ,
      W j ((((s₀ : ℤ) : ℂ)) + (((t : ℤ)) : ℂ)⁻¹) = (c : ℂ)} :=
    fun j => thin_of_not_isRatGerm (hWana j) (hWint j) (hWnr j)
  obtain ⟨ρ, hρ, hballev⟩ := Metric.eventually_nhds_iff.mp hev
  set T₁ : ℝ := max ρ⁻¹ 1 with hT₁
  set G : Set ℤ := {t : ℤ | T₁ < (t : ℝ) ∧ ∀ j : Idx, t ∉ {t' : ℤ | ∃ c : ℚ,
      W j ((((s₀ : ℤ) : ℂ)) + (((t' : ℤ)) : ℂ)⁻¹) = (c : ℂ)}} with hG
  have hGinf : G.Infinite := by
    refine Set.infinite_of_not_bddAbove ?_
    rintro ⟨M, hM⟩
    obtain ⟨t, ht1, ht2⟩ := exists_gt_notMem_of_thin _ hThin (max T₁ (M : ℝ))
    have htG : t ∈ G := ⟨lt_of_le_of_lt (le_max_left _ _) ht1, ht2⟩
    have hle : t ≤ M := hM htG
    have hlt : (M : ℝ) < (t : ℝ) := lt_of_le_of_lt (le_max_right _ _) ht1
    have hge : (t : ℝ) ≤ (M : ℝ) := by exact_mod_cast hle
    linarith
  have hgood : ∀ t ∈ G, Irreducible ((toQ f).map (Polynomial.evalRingHom
      (((s₀ : ℤ) : ℚ) + ((t : ℤ) : ℚ)⁻¹))) := by
    intro t ht
    obtain ⟨htT, htnot⟩ := ht
    set b : ℚ := ((s₀ : ℤ) : ℚ) + ((t : ℤ) : ℚ)⁻¹ with hb
    have ht1 : (1 : ℝ) < (t : ℝ) := lt_of_le_of_lt (le_max_right _ _) htT
    have ht0 : (0 : ℝ) < (t : ℝ) := lt_trans zero_lt_one ht1
    have hbC : ((b : ℚ) : ℂ) = (((s₀ : ℤ) : ℂ)) + (((t : ℤ)) : ℂ)⁻¹ := by
      rw [hb]; push_cast; ring
    have hdist : dist (((b : ℚ) : ℂ)) (((s₀ : ℤ) : ℂ)) < ρ := by
      rw [hbC, Complex.dist_eq, add_sub_cancel_left, norm_inv]
      have hnorm : ‖(((t : ℤ)) : ℂ)‖ = (t : ℝ) := by
        simp [abs_of_pos ht0]
      rw [hnorm]
      have hρi : ρ⁻¹ < (t : ℝ) := lt_of_le_of_lt (le_max_left _ _) htT
      exact inv_lt_of_inv_lt₀ hρ hρi
    obtain ⟨hinj, hdg, hroots⟩ := hballev hdist
    refine irreducible_fibre_of_not_rational hn1 hdg hinj hroots ?_
    intro S hS1 hS2
    refine ⟨kk ⟨S, hS1, hS2⟩, ?_⟩
    rintro ⟨c, hc⟩
    refine htnot ⟨S, hS1, hS2⟩ ⟨(Polynomial.aeval b (f.leadingCoeff.map (Int.castRingHom ℚ)))
      ^ S.card * c, ?_⟩
    rw [← hbC, hWval ⟨S, hS1, hS2⟩ (((b : ℚ) : ℂ))]
    show (cs (((b : ℚ) : ℂ))) ^ S.card * _ = _
    rw [hc]
    rw [hcs]
    simp only []
    rw [aeval_int_ratCast, aeval_map_int]
    push_cast
    ring
  have hsub : (fun t : ℤ => ((s₀ : ℤ) : ℚ) + ((t : ℤ) : ℚ)⁻¹) '' G
      ⊆ {b : ℚ | Irreducible ((toQ f).map (Polynomial.evalRingHom b))} := by
    rintro b ⟨t, ht, rfl⟩
    exact hgood t ht
  have hinjon : Set.InjOn (fun t : ℤ => ((s₀ : ℤ) : ℚ) + ((t : ℤ) : ℚ)⁻¹) G := by
    intro a ha b hb hab
    have ha1 : (1 : ℝ) < (a : ℝ) := lt_of_le_of_lt (le_max_right _ _) ha.1
    have hb1 : (1 : ℝ) < (b : ℝ) := lt_of_le_of_lt (le_max_right _ _) hb.1
    have hane : ((a : ℤ) : ℚ) ≠ 0 := by
      intro h
      have : ((a : ℤ) : ℝ) = 0 := by exact_mod_cast h
      linarith
    have hbne : ((b : ℤ) : ℚ) ≠ 0 := by
      intro h
      have : ((b : ℤ) : ℝ) = 0 := by exact_mod_cast h
      linarith
    have hinv : ((a : ℤ) : ℚ)⁻¹ = ((b : ℤ) : ℚ)⁻¹ := by
      have := hab
      simp only [] at this
      linarith [this]
    have : ((a : ℤ) : ℚ) = ((b : ℤ) : ℚ) := by
      field_simp at hinv
      exact hinv.symm
    exact_mod_cast this
  exact Set.Infinite.mono hsub (hGinf.image hinjon)

/-! ### Clearing denominators -/

/-- Every bivariate polynomial over `ℚ` becomes one over `ℤ` after scaling by a nonzero integer. -/
theorem exists_int_clear (F : Polynomial (Polynomial ℚ)) :
    ∃ (d : ℤ) (f : Polynomial (Polynomial ℤ)), d ≠ 0 ∧
      toQ f = Polynomial.C (Polynomial.C ((d : ℤ) : ℚ)) * F := by
  classical
  set N : ℕ := F.natDegree with hN
  have hspec : ∀ j : ℕ, ∃ b ∈ nonZeroDivisors ℤ,
      (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (F.coeff j)).map
        (algebraMap ℤ ℚ) = b • (F.coeff j) := fun j =>
    IsLocalization.integerNormalization_spec (nonZeroDivisors ℤ) (F.coeff j)
  choose bb hbbmem hbb using hspec
  set d : ℤ := ∏ j ∈ Finset.range (N + 1), bb j with hd
  have hdne : d ≠ 0 := by
    rw [hd]
    refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
    exact nonZeroDivisors.ne_zero (hbbmem j)
  have hbb' : ∀ k : ℕ, (IsLocalization.integerNormalization (nonZeroDivisors ℤ)
      (F.coeff k)).map (Int.castRingHom ℚ) = bb k • (F.coeff k) := hbb
  have hcoeff : ∀ j : ℕ, ∃ r : Polynomial ℤ,
      r.map (Int.castRingHom ℚ) = Polynomial.C ((d : ℤ) : ℚ) * F.coeff j := by
    intro j
    by_cases hj : j ≤ N
    · refine ⟨Polynomial.C (∏ k ∈ (Finset.range (N + 1)).erase j, bb k) *
        IsLocalization.integerNormalization (nonZeroDivisors ℤ) (F.coeff j), ?_⟩
      have hzs : (bb j) • (F.coeff j) = Polynomial.C (((bb j : ℤ) : ℚ)) * F.coeff j := by
        ext m
        simp [zsmul_eq_mul]
      have hscal : (Int.castRingHom ℚ) (∏ k ∈ (Finset.range (N + 1)).erase j, bb k)
          * (((bb j : ℤ) : ℚ)) = ((d : ℤ) : ℚ) := by
        rw [hd]
        simp only [map_prod, eq_intCast]
        push_cast
        exact Finset.prod_erase_mul (Finset.range (N + 1))
          (fun k => ((bb k : ℤ) : ℚ)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
      rw [Polynomial.map_mul, Polynomial.map_C, hbb' j, hzs, ← mul_assoc, ← Polynomial.C_mul,
        hscal]
    · refine ⟨0, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  choose r hr using hcoeff
  refine ⟨d, ∑ j ∈ Finset.range (N + 1), Polynomial.monomial j (r j), hdne, ?_⟩
  have hF : Polynomial.C (Polynomial.C ((d : ℤ) : ℚ)) * F
      = ∑ j ∈ Finset.range (N + 1), Polynomial.monomial j
          (Polynomial.C ((d : ℤ) : ℚ) * F.coeff j) := by
    conv_lhs => rw [Polynomial.as_sum_range' F (N + 1) (Nat.lt_succ_self N)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Polynomial.C_mul_monomial
  rw [toQ, Polynomial.map_sum, hF]
  simp only [Polynomial.coe_mapRingHom, Polynomial.map_monomial, hr]

/-- **Hilbert's irreducibility theorem.**  An irreducible `F ∈ ℚ[X][Y]` of positive degree in `Y`
stays irreducible under infinitely many rational specialisations of `X`. -/
theorem hilbert_irreducibility {F : Polynomial (Polynomial ℚ)} (hirr : Irreducible F)
    (hdeg : 1 ≤ F.natDegree) :
    {b : ℚ | Irreducible (F.map (Polynomial.evalRingHom b))}.Infinite := by
  classical
  obtain ⟨d, f, hdne, hf⟩ := exists_int_clear F
  set φ : Polynomial ℚ →+* FractionRing (Polynomial ℚ) :=
    algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)) with hφ
  -- `F` is primitive, hence irreducible over the fraction field
  have hprim : F.IsPrimitive := by
    intro rr hrr
    obtain ⟨g, hg⟩ := hrr
    rcases hirr.isUnit_or_isUnit hg with h | h
    · exact Polynomial.isUnit_C.mp h
    · exfalso
      have hCne : (Polynomial.C rr : Polynomial (Polynomial ℚ)) ≠ 0 := by
        intro hc
        rw [hc, zero_mul] at hg
        exact hirr.ne_zero hg
      have hgne : g ≠ 0 := by
        intro hc
        rw [hc, mul_zero] at hg
        exact hirr.ne_zero hg
      have hFdeg : F.natDegree = 0 := by
        rw [hg, Polynomial.natDegree_mul hCne hgne, Polynomial.natDegree_C,
          Polynomial.natDegree_eq_zero_of_isUnit h]
      omega
  have hirrK : Irreducible (F.map φ) :=
    (hprim.irreducible_iff_irreducible_map_fraction_map
      (K := FractionRing (Polynomial ℚ))).mp hirr
  -- transfer to `toQ f`
  have hunitC : IsUnit (Polynomial.C (Polynomial.C ((d : ℤ) : ℚ)) :
      Polynomial (Polynomial ℚ)) := by
    refine Polynomial.isUnit_C.mpr (Polynomial.isUnit_C.mpr ?_)
    refine isUnit_iff_ne_zero.mpr ?_
    exact_mod_cast hdne
  have hdegQ : (toQ f).natDegree = F.natDegree := by
    rw [hf, Polynomial.natDegree_mul hunitC.ne_zero hirr.ne_zero,
      Polynomial.natDegree_eq_zero_of_isUnit hunitC, zero_add]
  have hirrQK : Irreducible ((toQ f).map φ) := by
    rw [hf, Polynomial.map_mul]
    exact ((associated_unit_mul_left (F.map φ) _
      (hunitC.map (Polynomial.mapRingHom φ))).irreducible_iff).mpr hirrK
  have hfdeg : 1 ≤ f.natDegree := by
    rw [← natDegree_toQ, hdegQ]
    exact hdeg
  obtain hinf := hilbert_irreducibility_int (n := f.natDegree) rfl hfdeg hirrQK
  refine Set.Infinite.mono ?_ hinf
  intro b hb
  simp only [Set.mem_setOf_eq] at hb ⊢
  rw [hf, Polynomial.map_mul, Polynomial.map_C] at hb
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_C] at hb
  have hCunit : IsUnit (Polynomial.C (((d : ℤ) : ℚ)) : Polynomial ℚ) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (by exact_mod_cast hdne))
  exact ((associated_unit_mul_left (F.map (Polynomial.evalRingHom b)) _
    hCunit).irreducible_iff).mp hb

/-! ### A worked instance: `Y² − X` -/

/-- `Y ^ 2 - X` is irreducible in `ℚ[X][Y]`: Eisenstein at the prime `(X)`. -/
theorem irreducible_X_sq_sub_C_X :
    Irreducible ((Polynomial.X : Polynomial (Polynomial ℚ)) ^ 2
      - Polynomial.C Polynomial.X) := by
  classical
  set F : Polynomial (Polynomial ℚ) :=
    (Polynomial.X : Polynomial (Polynomial ℚ)) ^ 2 - Polynomial.C Polynomial.X with hF
  have hdeglt : (-(Polynomial.C (Polynomial.X : Polynomial ℚ)) :
      Polynomial (Polynomial ℚ)).degree < (2 : ℕ) := by
    rw [Polynomial.degree_neg]
    exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast (by decide : (0 : ℕ) < 2))
  have hmonic : F.Monic := by
    rw [hF, sub_eq_add_neg]
    exact Polynomial.monic_X_pow_add hdeglt
  have hdeg : F.natDegree = 2 := by
    rw [hF, sub_eq_add_neg]
    refine Polynomial.natDegree_eq_of_degree_eq_some ?_
    rw [Polynomial.degree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow])]
    exact Polynomial.degree_X_pow 2
  set P0 : Ideal (Polynomial ℚ) := Ideal.span {(Polynomial.X : Polynomial ℚ)} with hP0
  have hprime : P0.IsPrime :=
    (Ideal.span_singleton_prime Polynomial.X_ne_zero).mpr Polynomial.prime_X
  have hc0 : F.coeff 0 = -(Polynomial.X : Polynomial ℚ) := by
    rw [hF]; simp
  have hc1 : F.coeff 1 = 0 := by
    rw [hF]; simp
  refine Polynomial.IsEisensteinAt.irreducible ?_ hprime hmonic.isPrimitive (by rw [hdeg]; omega)
  refine ⟨?_, ?_, ?_⟩
  · rw [hmonic.leadingCoeff]
    intro hmem
    exact hprime.ne_top (Ideal.eq_top_iff_one P0 |>.mpr hmem)
  · intro n hn
    rw [hdeg] at hn
    interval_cases n
    · rw [hc0, hP0]
      exact Ideal.mem_span_singleton.mpr ⟨-1, by ring⟩
    · rw [hc1]
      exact Ideal.zero_mem _
  · rw [hc0, hP0, Ideal.span_singleton_pow]
    intro hmem
    have hdvd : (Polynomial.X : Polynomial ℚ) ^ 2 ∣ -(Polynomial.X : Polynomial ℚ) :=
      Ideal.mem_span_singleton.mp hmem
    have hdvd' : (Polynomial.X : Polynomial ℚ) ^ 2 ∣ (Polynomial.X : Polynomial ℚ) :=
      (dvd_neg).mp hdvd
    have hle := Polynomial.natDegree_le_of_dvd hdvd' Polynomial.X_ne_zero
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X] at hle
    omega

/-- **A nontrivial instance.**  There are infinitely many rationals `b` for which `Y ^ 2 - b` is
irreducible over `ℚ`; equivalently, infinitely many rationals are not squares. -/
theorem infinite_irreducible_X_sq_sub_C :
    {b : ℚ | Irreducible (Polynomial.map (Polynomial.evalRingHom b)
      ((Polynomial.X : Polynomial (Polynomial ℚ)) ^ 2 - Polynomial.C Polynomial.X))}.Infinite := by
  refine hilbert_irreducibility irreducible_X_sq_sub_C_X ?_
  have hdeglt : (-(Polynomial.C (Polynomial.X : Polynomial ℚ)) :
      Polynomial (Polynomial ℚ)).degree < (2 : ℕ) := by
    rw [Polynomial.degree_neg]
    exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast (by decide : (0 : ℕ) < 2))
  have hdeg : ((Polynomial.X : Polynomial (Polynomial ℚ)) ^ 2
      - Polynomial.C Polynomial.X).natDegree = 2 := by
    rw [sub_eq_add_neg]
    refine Polynomial.natDegree_eq_of_degree_eq_some ?_
    rw [Polynomial.degree_add_eq_left_of_degree_lt (by rwa [Polynomial.degree_X_pow])]
    exact Polynomial.degree_X_pow 2
  rw [hdeg]
  omega

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
