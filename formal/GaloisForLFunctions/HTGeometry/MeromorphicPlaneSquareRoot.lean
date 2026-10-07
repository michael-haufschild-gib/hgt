import GaloisForLFunctions.HTGeometry.MeromorphicPlaneField
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Global meromorphic squares of entire functions

A square root in the field of globally meromorphic functions has no poles when its square is
entire. Normalization therefore gives an entire root. If the square commutes with conjugation,
reflection fixes or negates that root, so its values on the real axis cannot change sign.
-/

open Complex Filter Topology
open scoped ComplexConjugate
namespace GaloisForLFunctions.HTGeometry

/-- A meromorphic square root of an entire function extends to an entire square root. -/
theorem entire_sqrt_of_isSquare_plane {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hsq : IsSquare (ofMeromorphic f (fun z => (hf.analyticAt z).meromorphicAt))) :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧ ∀ z, g z ^ 2 = f z := by
  obtain ⟨a, ha⟩ := hsq
  obtain ⟨g, hg, rfl⟩ := MeromorphicPlane.exists_rep a
  have heq : ∀ z, f =ᶠ[𝓝[≠] z] (fun w => g w ^ 2) := by
    apply (ofMeromorphic_eq_iff (fun z => (hf.analyticAt z).meromorphicAt)
      (fun z => (hg z).pow 2)).mp
    apply ha.trans
    rw [ofMeromorphic_mul]
    apply (ofMeromorphic_eq_iff _ _).mpr
    intro z
    exact Filter.Eventually.of_forall (fun w => (pow_two (g w)).symm)
  let h := toMeromorphicNFOn g Set.univ
  have hgon : MeromorphicOn g Set.univ := fun z _ => hg z
  have hheq (z : ℂ) : h =ᶠ[𝓝[≠] z] g :=
    hgon.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have han (z : ℂ) : AnalyticAt ℂ h z := by
    apply ((meromorphicNFOn_toMeromorphicNFOn g Set.univ)
      (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hgon (Set.mem_univ z)]
    have hord := (hf.analyticAt z).meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_congr (heq z)] at hord
    change 0 ≤ meromorphicOrderAt (g ^ 2) z at hord
    rw [meromorphicOrderAt_pow (hg z)] at hord
    cases hx : meromorphicOrderAt g z with
    | top => simp
    | coe n =>
      rw [hx] at hord
      change (↑(0 : ℤ) : WithTop ℤ) ≤ ↑((2 : ℤ) * n) at hord
      have hn : (0 : ℤ) ≤ 2 * n := WithTop.coe_le_coe.mp hord
      norm_cast
      omega
  refine ⟨h, fun z => (han z).differentiableAt, fun z => ?_⟩
  have he : (fun w => h w ^ 2) =ᶠ[𝓝[≠] z] f := by
    filter_upwards [hheq z, heq z] with w hw hfw
    rw [hw, ← hfw]
  exact ((ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    ((han z).continuousAt.pow 2) (hf.continuous.continuousAt)).mp he).eq_of_nhds

/-- An entire square commuting with conjugation has one weak sign on the real axis. -/
theorem entire_square_real_sign_product_nonneg {f g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hfg : ∀ z, g z ^ 2 = f z)
    (hreal : ∀ z, f (conj z) = conj (f z)) (x y : ℝ) :
    0 ≤ (f x).re * (f y).re := by
  let gc : ℂ → ℂ := conj ∘ g ∘ conj
  have hgc : Differentiable ℂ gc := fun z => by
    simpa [gc] using (hg (conj z)).conj_conj
  have heq (z : ℂ) : gc z ^ 2 = g z ^ 2 := by
    change conj (g (conj z)) ^ 2 = g z ^ 2
    rw [← map_pow, hfg, hreal, Complex.conj_conj, hfg]
  have hmul (z : ℂ) : (g z - gc z) * (g z + gc z) = 0 := by
    calc
      _ = g z ^ 2 - gc z ^ 2 := by ring
      _ = 0 := by rw [heq, sub_self]
  have h := AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero
    (fun z _ => ((hg.sub hgc).analyticAt z))
    (fun z _ => ((hg.add hgc).analyticAt z))
    (fun z (_ : z ∈ Set.univ) => hmul z) isPreconnected_univ
  have hs (t : ℝ) : gc t = conj (g t) := by simp [gc]
  rcases h with h | h
  · have him (t : ℝ) : (g t).im = 0 := by
      have ht := congrArg Complex.im (h t (Set.mem_univ _))
      simp only [Pi.sub_apply, sub_im, hs, conj_im, zero_im] at ht
      linarith
    rw [← hfg, ← hfg]
    simp only [pow_two, mul_re, him, mul_zero, sub_zero]
    exact mul_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  · have hre (t : ℝ) : (g t).re = 0 := by
      have ht := congrArg Complex.re (h t (Set.mem_univ _))
      simp only [Pi.add_apply, add_re, hs, conj_re, zero_re] at ht
      linarith
    rw [← hfg, ← hfg]
    simp only [pow_two, mul_re, hre, zero_mul, zero_sub, neg_mul_neg]
    exact mul_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

/-- A strict sign change of an entire Schwarz-real function excludes a global meromorphic root. -/
theorem not_isSquare_plane_of_real_sign_change {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hreal : ∀ z, f (conj z) = conj (f z))
    {x y : ℝ} (hsign : (f x).re * (f y).re < 0) :
    ¬ IsSquare (ofMeromorphic f (fun z => (hf.analyticAt z).meromorphicAt)) := by
  intro hsq
  obtain ⟨g, hg, hfg⟩ := entire_sqrt_of_isSquare_plane hf hsq
  exact (not_lt_of_ge (entire_square_real_sign_product_nonneg hg hfg hreal x y)) hsign

end GaloisForLFunctions.HTGeometry
