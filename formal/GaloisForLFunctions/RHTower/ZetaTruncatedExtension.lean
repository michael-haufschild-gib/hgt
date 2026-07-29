import GaloisForLFunctions.RHTower.ZetaSawtoothHolomorphy

/-!
# The truncated representation on the punctured right half-plane

`ζ(s) = Σ_{n ≤ N} n^{-s} + N^{1-s}/(s-1) - s·∫_N^∞ {u}·u^{-s-1} du`
for all `Re s > 0`, `s ≠ 1`: both sides are analytic on the punctured
half-plane, agree on `Re s > 1`, and the punctured half-plane is
preconnected — it is the chained union of four convex pieces
(`Re > 1`, upper and lower open quadrants of the half-plane, and the
open strip `0 < Re < 1`).  The identity theorem extends the equality.
-/

noncomputable section

namespace RHTower

open Set Filter

/-- The truncated ζ-representation. -/
def zetaTruncated (N : ℕ) (s : ℂ) : ℂ :=
  (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s))
    + (N : ℂ) ^ (1 - s) / (s - 1) - s * zetaSawtoothTail N s

/-- The punctured right half-plane is preconnected. -/
theorem isPreconnected_halfplane_punctured :
    IsPreconnected ({z : ℂ | 0 < z.re} \ {1}) := by
  have hre : IsLinearMap ℝ Complex.re :=
    ⟨fun a b => Complex.add_re a b, fun r z => Complex.smul_re r z⟩
  have him : IsLinearMap ℝ Complex.im :=
    ⟨fun a b => Complex.add_im a b, fun r z => Complex.smul_im r z⟩
  have hA : Convex ℝ {z : ℂ | 1 < z.re} := convex_halfSpace_gt hre 1
  have hB : Convex ℝ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | 0 < z.im}) :=
    (convex_halfSpace_gt hre 0).inter (convex_halfSpace_gt him 0)
  have hC : Convex ℝ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.im < 0}) :=
    (convex_halfSpace_gt hre 0).inter (convex_halfSpace_lt him 0)
  have hD : Convex ℝ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1}) :=
    (convex_halfSpace_gt hre 0).inter (convex_halfSpace_lt hre 1)
  have hcover : ({z : ℂ | 0 < z.re} \ {1})
      = (({z : ℂ | 1 < z.re}
          ∪ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | 0 < z.im}))
        ∪ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.im < 0}))
        ∪ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1}) := by
    ext z
    simp only [Set.mem_sdiff, Set.mem_setOf_eq, Set.mem_singleton_iff,
      Set.mem_union, Set.mem_inter_iff]
    constructor
    · rintro ⟨hre0, hne1⟩
      rcases lt_trichotomy z.im 0 with him | him | him
      · exact Or.inl (Or.inr ⟨hre0, him⟩)
      · rcases lt_trichotomy z.re 1 with hre1 | hre1 | hre1
        · exact Or.inr ⟨hre0, hre1⟩
        · exfalso
          apply hne1
          apply Complex.ext
          · simpa using hre1
          · simpa using him
        · exact Or.inl (Or.inl (Or.inl hre1))
      · exact Or.inl (Or.inl (Or.inr ⟨hre0, him⟩))
    · rintro (((h | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩)
      · refine ⟨by linarith, fun he => ?_⟩
        rw [he] at h
        simp at h
      · refine ⟨h1, fun he => ?_⟩
        rw [he] at h2
        simp at h2
      · refine ⟨h1, fun he => ?_⟩
        rw [he] at h2
        simp at h2
      · refine ⟨h1, fun he => ?_⟩
        rw [he] at h2
        simp at h2
  rw [hcover]
  have hx₁ : (2 + Complex.I) ∈ {z : ℂ | 1 < z.re}
      ∩ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | 0 < z.im}) := by
    refine ⟨?_, ?_, ?_⟩ <;>
      simp [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im]
  have hAB := IsPreconnected.union (2 + Complex.I) hx₁.1 hx₁.2
    hA.isPreconnected hB.isPreconnected
  have hx₂ : (2 - Complex.I) ∈ ({z : ℂ | 1 < z.re}
        ∪ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | 0 < z.im}))
      ∩ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.im < 0}) := by
    refine ⟨Or.inl ?_, ⟨?_, ?_⟩⟩ <;> simp <;> norm_num
  have hABC := IsPreconnected.union (2 - Complex.I) hx₂.1 hx₂.2
    hAB hC.isPreconnected
  have hx₃ : ((1 / 2 : ℝ) + Complex.I) ∈ (({z : ℂ | 1 < z.re}
        ∪ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | 0 < z.im}))
        ∪ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.im < 0}))
      ∩ ({z : ℂ | 0 < z.re} ∩ {z : ℂ | z.re < 1}) := by
    refine ⟨Or.inl (Or.inr ⟨?_, ?_⟩), ⟨?_, ?_⟩⟩ <;> simp <;> norm_num
  exact IsPreconnected.union ((1 / 2 : ℝ) + Complex.I) hx₃.1 hx₃.2
    hABC hD.isPreconnected

/-- The truncated representation is differentiable on the punctured
half-plane. -/
theorem differentiableAt_zetaTruncated {N : ℕ} (hN : 1 ≤ N) {z : ℂ}
    (hz0 : 0 < z.re) (hz1 : z ≠ 1) :
    DifferentiableAt ℂ (zetaTruncated N) z := by
  have hsum : DifferentiableAt ℂ
      (fun s : ℂ => ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-s)) z := by
    apply DifferentiableAt.fun_sum
    intro n hn
    rw [Finset.mem_Icc] at hn
    exact DifferentiableAt.const_cpow (differentiable_id.neg).differentiableAt
      (Or.inl (by exact_mod_cast (by omega : n ≠ 0)))
  have hpole : DifferentiableAt ℂ
      (fun s : ℂ => (N : ℂ) ^ (1 - s) / (s - 1)) z := by
    apply DifferentiableAt.div
    · exact DifferentiableAt.const_cpow
        ((differentiable_const 1).sub differentiable_id).differentiableAt
        (Or.inl (by exact_mod_cast (by omega : N ≠ 0)))
    · exact (differentiable_id.sub_const 1).differentiableAt
    · exact sub_ne_zero.2 hz1
  have htail : DifferentiableAt ℂ
      (fun s : ℂ => s * zetaSawtoothTail N s) z :=
    differentiableAt_id.mul (differentiableAt_zetaSawtoothTail hN hz0)
  exact (hsum.add hpole).sub htail

set_option maxHeartbeats 800000 in
/-- **The truncated representation extends to `Re s > 0`, `s ≠ 1`.** -/
theorem zeta_eq_truncated_of_re_pos {N : ℕ} (hN : 1 ≤ N) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = zetaTruncated N s := by
  have hU : IsOpen ({z : ℂ | 0 < z.re} \ {1}) :=
    (isOpen_lt continuous_const Complex.continuous_re).sdiff
      isClosed_singleton
  have hζ : AnalyticOnNhd ℂ riemannZeta ({z : ℂ | 0 < z.re} \ {1}) := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact (differentiableAt_riemannZeta hz.2).differentiableWithinAt
  have htr : AnalyticOnNhd ℂ (zetaTruncated N)
      ({z : ℂ | 0 < z.re} \ {1}) := by
    apply DifferentiableOn.analyticOnNhd _ hU
    intro z hz
    exact (differentiableAt_zetaTruncated hN hz.1 hz.2).differentiableWithinAt
  have h2mem : (2 : ℂ) ∈ ({z : ℂ | 0 < z.re} \ {1}) := by
    constructor
    · simp
    · simp only [Set.mem_singleton_iff]
      intro h
      have := congrArg Complex.re h
      simp at this
  have hev : riemannZeta =ᶠ[nhds (2 : ℂ)] zetaTruncated N := by
    have hmem : {z : ℂ | 1 < z.re} ∈ nhds (2 : ℂ) := by
      apply IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re)
      simp
    filter_upwards [hmem] with z hz
    exact zeta_eq_truncated hz hN
  exact hζ.eqOn_of_preconnected_of_eventuallyEq htr
    isPreconnected_halfplane_punctured h2mem hev
    ⟨hs0, by simpa using hs1⟩

end RHTower
