import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Uniqueness of the Weierstrass division

A Weierstrass division writes a function as a continuous multiple of a monic polynomial whose roots
all lie inside a disc, plus a polynomial of degree below the number of those roots.  The two pieces
are determined: the difference of two divisions is a low-degree polynomial which is a continuous
multiple of the monic polynomial, and peeling the roots off one at a time forces it to vanish.

Peeling one root uses only continuity.  The polynomial factor `X - ρ` divides the remainder because
the remainder vanishes at `ρ`; cancelling it is legitimate away from `ρ`, and the two continuous
sides then agree at `ρ` as well because a punctured neighbourhood of a point of an open set in `ℂ`
is nonempty.  This is what encodes the multiplicity of `ρ` without any order arithmetic.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Metric Filter
open scoped Topology

/-- Two continuous functions on an open subset of `ℂ` that agree off a finite set agree
everywhere. -/
theorem eqOn_of_continuousOn_of_finite_diff {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) {F : Set ℂ} (hF : F.Finite)
    (h : ∀ z ∈ U, z ∉ F → f z = g z) {z : ℂ} (hz : z ∈ U) : f z = g z := by
  by_cases hzF : z ∉ F
  · exact h z hz hzF
  have hVopen : IsOpen (U \ (F \ {z})) :=
    hU.sdiff ((hF.subset Set.sdiff_subset).isClosed)
  have hzV : z ∈ U \ (F \ {z}) := ⟨hz, by simp⟩
  have hVmem : U \ (F \ {z}) ∈ 𝓝 z := hVopen.mem_nhds hzV
  have hfilter : 𝓝[({z}ᶜ : Set ℂ)] z = 𝓝[({z}ᶜ ∩ (U \ (F \ {z})) : Set ℂ)] z :=
    nhdsWithin_restrict' _ hVmem
  have hne : (𝓝[({z}ᶜ ∩ (U \ (F \ {z})) : Set ℂ)] z).NeBot := by
    rw [← hfilter]
    infer_instance
  have hsub : ({z}ᶜ ∩ (U \ (F \ {z})) : Set ℂ) ⊆ U := fun w hw => hw.2.1
  have hfz : Tendsto f (𝓝[({z}ᶜ ∩ (U \ (F \ {z})) : Set ℂ)] z) (𝓝 (f z)) :=
    (hf.continuousWithinAt hz).mono_left (nhdsWithin_mono _ hsub)
  have hgz : Tendsto g (𝓝[({z}ᶜ ∩ (U \ (F \ {z})) : Set ℂ)] z) (𝓝 (g z)) :=
    (hg.continuousWithinAt hz).mono_left (nhdsWithin_mono _ hsub)
  have hev : f =ᶠ[𝓝[({z}ᶜ ∩ (U \ (F \ {z})) : Set ℂ)] z] g := by
    refine eventually_nhdsWithin_of_forall ?_
    rintro w ⟨hw1, hw2, hw3⟩
    refine h w hw2 ?_
    intro hwF
    exact hw3 ⟨hwF, by simpa using hw1⟩
  exact tendsto_nhds_unique hfz (hgz.congr' hev.symm)

/-- **A low-degree polynomial which is a continuous multiple of a monic polynomial with prescribed
roots in a disc vanishes.** -/
theorem eq_zero_of_degree_lt_of_continuous_multiple {t : ℝ} :
    ∀ (ρs : Multiset ℂ), (∀ ρ ∈ ρs, ‖ρ‖ < t) → ∀ P : Polynomial ℂ,
      P.degree < (Multiset.card ρs : ℕ) → ∀ q : ℂ → ℂ,
      ContinuousOn q (ball (0 : ℂ) t) →
      (∀ z ∈ ball (0 : ℂ) t,
        P.eval z = q z * ((ρs.map fun ρ => Polynomial.X - Polynomial.C ρ).prod).eval z) →
      P = 0 := by
  intro ρs
  induction ρs using Multiset.induction with
  | empty =>
      intro _ P hdeg _ _ _
      rw [Multiset.card_zero, Nat.cast_zero] at hdeg
      exact degree_eq_bot.mp (Nat.WithBot.lt_zero_iff.mp hdeg)
  | cons ρ s ih =>
      intro hρ P hdeg q hq heq
      have hρt : ‖ρ‖ < t := hρ ρ (Multiset.mem_cons_self ρ s)
      have hρball : ρ ∈ ball (0 : ℂ) t := by
        simpa [Complex.dist_eq] using hρt
      set W : Polynomial ℂ := (s.map fun r => Polynomial.X - Polynomial.C r).prod with hW
      have hprod : ((ρ ::ₘ s).map fun r => Polynomial.X - Polynomial.C r).prod
          = (Polynomial.X - Polynomial.C ρ) * W := by
        rw [Multiset.map_cons, Multiset.prod_cons]
      have heq' : ∀ z ∈ ball (0 : ℂ) t,
          P.eval z = q z * ((z - ρ) * W.eval z) := by
        intro z hz
        have := heq z hz
        rwa [hprod, eval_mul, eval_sub, eval_X, eval_C] at this
      have hroot : P.IsRoot ρ := by
        have := heq' ρ hρball
        rwa [sub_self, zero_mul, mul_zero] at this
      obtain ⟨P', hP'⟩ := dvd_iff_isRoot.mpr hroot
      by_cases hP'0 : P' = 0
      · rw [hP', hP'0, mul_zero]
      -- the cancelled identity, first off `ρ` and then everywhere by continuity
      have hcancel : ∀ z ∈ ball (0 : ℂ) t, z ∉ ({ρ} : Set ℂ) →
          P'.eval z = q z * W.eval z := by
        intro z hz hzρ
        have hzne : z - ρ ≠ 0 := sub_ne_zero.mpr (by simpa using hzρ)
        have h1 := heq' z hz
        rw [hP', eval_mul, eval_sub, eval_X, eval_C] at h1
        refine mul_left_cancel₀ hzne ?_
        rw [h1]
        ring
      have hcont1 : ContinuousOn (fun z => P'.eval z) (ball (0 : ℂ) t) :=
        (P'.continuous_aeval).continuousOn
      have hcont2 : ContinuousOn (fun z => q z * W.eval z) (ball (0 : ℂ) t) :=
        hq.mul (W.continuous_aeval).continuousOn
      have hall : ∀ z ∈ ball (0 : ℂ) t, P'.eval z = q z * W.eval z := fun z hz =>
        eqOn_of_continuousOn_of_finite_diff isOpen_ball hcont1 hcont2
          (Set.finite_singleton ρ) hcancel hz
      -- the degree drops by one
      have hPne : P ≠ 0 := by
        rw [hP']
        exact mul_ne_zero (Polynomial.X_sub_C_ne_zero ρ) hP'0
      have hnat : P.natDegree = P'.natDegree + 1 := by
        rw [hP', natDegree_mul (Polynomial.X_sub_C_ne_zero ρ) hP'0, natDegree_X_sub_C]
        ring
      have hdegnat : P.natDegree < Multiset.card s + 1 := by
        have : (P.natDegree : WithBot ℕ) < ((Multiset.card (ρ ::ₘ s) : ℕ) : WithBot ℕ) := by
          rwa [← degree_eq_natDegree hPne]
        have h2 : P.natDegree < Multiset.card (ρ ::ₘ s) := by exact_mod_cast this
        rwa [Multiset.card_cons] at h2
      have hdeg' : P'.degree < (Multiset.card s : ℕ) := by
        rw [degree_eq_natDegree hP'0]
        exact_mod_cast (by omega : P'.natDegree < Multiset.card s)
      have hP'zero : P' = 0 :=
        ih (fun r hr => hρ r (Multiset.mem_cons_of_mem hr)) P' hdeg' q hq hall
      exact absurd hP'zero hP'0

/-- **Uniqueness of the Weierstrass division.**  The quotient and the low-degree remainder of a
division by a monic polynomial with prescribed roots inside a disc are determined. -/
theorem weierstrass_division_unique {t : ℝ} {ρs : Multiset ℂ} (hρ : ∀ ρ ∈ ρs, ‖ρ‖ < t)
    {q₁ q₂ : ℂ → ℂ} (hq₁ : ContinuousOn q₁ (ball (0 : ℂ) t))
    (hq₂ : ContinuousOn q₂ (ball (0 : ℂ) t))
    {P₁ P₂ : Polynomial ℂ} (h₁ : P₁.degree < (Multiset.card ρs : ℕ))
    (h₂ : P₂.degree < (Multiset.card ρs : ℕ))
    (heq : ∀ z ∈ ball (0 : ℂ) t,
      q₁ z * ((ρs.map fun ρ => Polynomial.X - Polynomial.C ρ).prod).eval z + P₁.eval z
        = q₂ z * ((ρs.map fun ρ => Polynomial.X - Polynomial.C ρ).prod).eval z + P₂.eval z) :
    P₁ = P₂ ∧ ∀ z ∈ ball (0 : ℂ) t, q₁ z = q₂ z := by
  set W : Polynomial ℂ := (ρs.map fun ρ => Polynomial.X - Polynomial.C ρ).prod with hW
  have hdiff : (P₁ - P₂).degree < (Multiset.card ρs : ℕ) :=
    lt_of_le_of_lt (degree_sub_le P₁ P₂) (max_lt h₁ h₂)
  have hrel : ∀ z ∈ ball (0 : ℂ) t, (P₁ - P₂).eval z = (q₂ z - q₁ z) * W.eval z := by
    intro z hz
    have h := heq z hz
    rw [eval_sub]
    linear_combination h
  have hP : P₁ - P₂ = 0 :=
    eq_zero_of_degree_lt_of_continuous_multiple ρs hρ (P₁ - P₂) hdiff (fun z => q₂ z - q₁ z)
      (hq₂.sub hq₁) hrel
  have hPeq : P₁ = P₂ := by
    have := sub_eq_zero.mp hP
    exact this
  refine ⟨hPeq, ?_⟩
  have hWne : W ≠ 0 := by
    rw [hW]
    refine Multiset.prod_ne_zero ?_
    intro hmem
    obtain ⟨r, -, hr⟩ := Multiset.mem_map.mp hmem
    exact Polynomial.X_sub_C_ne_zero r hr
  have hfin : {z : ℂ | W.eval z = 0}.Finite := by
    refine Set.Finite.subset (W.roots.toFinset.finite_toSet) ?_
    intro z hz
    simp only [Multiset.mem_toFinset, Finset.mem_coe]
    exact (mem_roots hWne).mpr hz
  refine fun z hz => eqOn_of_continuousOn_of_finite_diff isOpen_ball hq₁ hq₂ hfin ?_ hz
  intro w hw hwF
  have h0 : W.eval w ≠ 0 := hwF
  have := heq w hw
  rw [hPeq] at this
  have h2 : q₁ w * W.eval w = q₂ w * W.eval w := by linear_combination this
  exact mul_right_cancel₀ h0 h2

end GaloisForLFunctions.HTGeometry
