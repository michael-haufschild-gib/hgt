import Mathlib

/-!
# Nondegeneracy of finite product exponential expansions

For finitely many coordinates `j` and finitely many pairwise distinct options `z j i`, choose a
real-linear functional which separates every option pair.  At each coordinate choose the unique
maximising option.  The resulting tuple is the unique maximiser of the sum, so one exponent fiber
of a product expansion has a single nonzero coefficient.  Consequently the zero fiber of the
squared difference expansion is a strictly positive sum of integer squares.
-/

open Finset Complex
open scoped Classical

namespace GaloisForLFunctions.RHTower

/-- A real-linear functional of the form `re + t * im` can simultaneously avoid zero on any
finite family of nonzero complex numbers. -/
theorem exists_real_linear_separator {J : Type*} [Fintype J]
    (z : J → ℂ) (hz : ∀ j, z j ≠ 0) :
    ∃ t : ℝ, ∀ j, (z j).re + t * (z j).im ≠ 0 := by
  classical
  by_contra hcon
  simp only [not_exists, not_forall, not_ne_iff] at hcon
  choose f hf using hcon
  obtain ⟨x, hx, y, hy, hxy, hfeq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (Fintype.card J + 1)) (t := (Finset.univ : Finset J))
    (by simp) (f := fun i => f (i : ℝ)) (fun _ _ => Finset.mem_univ _)
  set j := f (x : ℝ) with hj
  have e1 : (z j).re + (x : ℝ) * (z j).im = 0 := hf (x : ℝ)
  have e2 : (z j).re + (y : ℝ) * (z j).im = 0 := by
    rw [hfeq]
    exact hf (y : ℝ)
  have him : (z j).im = 0 := by
    have hsub : ((x : ℝ) - (y : ℝ)) * (z j).im = 0 := by
      ring_nf
      linarith [e1, e2]
    have hne : (x : ℝ) - (y : ℝ) ≠ 0 := by
      simp only [sub_ne_zero]
      exact_mod_cast hxy
    exact (mul_eq_zero.mp hsub).resolve_left hne
  have hre : (z j).re = 0 := by
    rw [him, mul_zero, add_zero] at e1
    exact e1
  exact hz j (Complex.ext hre him)

/-- The exponent attached to a tuple of coordinatewise choices. -/
noncomputable def finiteProductExponent {J ι : Type*} [Fintype J]
    (z : J → ι → ℂ) (k : J → ι) : ℂ :=
  ∑ j, z j (k j)

/-- The integer coefficient attached to a tuple in a product expansion. -/
noncomputable def finiteProductCoefficient {J ι : Type*} [Fintype J]
    (c : ι → ℤ) (k : J → ι) : ℤ :=
  ∏ j, c (k j)

/-- **Finite-product difference nondegeneracy.** If every coordinate offers pairwise distinct
complex exponents and every option coefficient is nonzero, then the zero-exponent coefficient of
the product expansion multiplied by its exponent-negated copy is nonzero. -/
theorem finiteProductTupleDiff_nondegenerate
    {J ι : Type*} [Fintype J] [Fintype ι] [Nonempty ι]
    (z : J → ι → ℂ) (hz : ∀ j, Function.Injective (z j))
    (c : ι → ℤ) (hc : ∀ i, c i ≠ 0) :
    (∑ p ∈ (Finset.univ : Finset ((J → ι) × (J → ι))).filter
        (fun p => finiteProductExponent z p.1 - finiteProductExponent z p.2 = 0),
      finiteProductCoefficient c p.1 * finiteProductCoefficient c p.2) ≠ 0 := by
  classical
  let PairDiff := Σ j : J, {p : ι × ι // p.1 ≠ p.2}
  let diff : PairDiff → ℂ := fun p => z p.1 p.2.1.1 - z p.1 p.2.1.2
  have hdiff : ∀ p, diff p ≠ 0 := by
    intro p
    dsimp [diff]
    exact sub_ne_zero.mpr (fun h => p.2.2 (hz p.1 h))
  obtain ⟨t, ht⟩ := exists_real_linear_separator diff hdiff
  let L : ℂ →ₗ[ℝ] ℝ := Complex.reLm + t • Complex.imLm
  have hL : ∀ w : ℂ, L w = w.re + t * w.im := by
    intro w
    simp [L, smul_eq_mul]
  have hsep : ∀ j i i', i ≠ i' → L (z j i) ≠ L (z j i') := by
    intro j i i' hii hEq
    let p : PairDiff := ⟨j, ⟨(i, i'), hii⟩⟩
    have hp := ht p
    rw [← hL] at hp
    apply hp
    dsimp [diff, p]
    rw [map_sub, hEq, sub_self]
  have hmax : ∀ j : J, ∃ i : ι, ∀ i' : ι, L (z j i') ≤ L (z j i) := by
    intro j
    obtain ⟨i, _, hi⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
      (fun i => L (z j i)) Finset.univ_nonempty
    exact ⟨i, fun i' => hi i' (Finset.mem_univ i')⟩
  choose kstar hkstar using hmax
  let Ecoef : (J → ι) → ℤ := finiteProductCoefficient c
  let Eexp : (J → ι) → ℂ := finiteProductExponent z
  have hLexp : ∀ k : J → ι, L (Eexp k) = ∑ j, L (z j (k j)) := by
    intro k
    simp [Eexp, finiteProductExponent, map_sum]
  have huniq : ∀ k : J → ι, Eexp k = Eexp kstar → k = kstar := by
    intro k hk
    have hsum : ∑ j, (L (z j (kstar j)) - L (z j (k j))) = 0 := by
      rw [Finset.sum_sub_distrib, ← hLexp, ← hLexp, hk, sub_self]
    have hnonneg : ∀ j ∈ (Finset.univ : Finset J),
        0 ≤ L (z j (kstar j)) - L (z j (k j)) := by
      intro j _
      exact sub_nonneg.mpr (hkstar j (k j))
    have heach := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
    funext j
    by_contra hne
    have hj := heach j (Finset.mem_univ j)
    have heq : L (z j (kstar j)) = L (z j (k j)) := sub_eq_zero.mp hj
    exact hsep j (kstar j) (k j) (Ne.symm hne) heq
  let C : ℂ → ℤ := fun v =>
    ∑ k ∈ (Finset.univ : Finset (J → ι)).filter (fun k => Eexp k = v), Ecoef k
  let vals : Finset ℂ := (Finset.univ : Finset (J → ι)).image Eexp
  have hfilterstar :
      (Finset.univ : Finset (J → ι)).filter (fun k => Eexp k = Eexp kstar) = {kstar} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => huniq k h, fun h => by rw [h]⟩
  have hCstar : C (Eexp kstar) = Ecoef kstar := by
    simp only [C]
    rw [hfilterstar, Finset.sum_singleton]
  have hEcoefstar : Ecoef kstar ≠ 0 := by
    simp only [Ecoef, finiteProductCoefficient]
    rw [Finset.prod_ne_zero_iff]
    intro j _
    exact hc (kstar j)
  have hfiltereq :
      (Finset.univ : Finset ((J → ι) × (J → ι))).filter
          (fun p => Eexp p.1 - Eexp p.2 = 0) =
        Finset.univ.filter (fun p => Eexp p.1 = Eexp p.2) := by
    apply Finset.filter_congr
    intro p _
    simp only [sub_eq_zero]
  have hD1 :
      (∑ p ∈ (Finset.univ : Finset ((J → ι) × (J → ι))).filter
          (fun p => Eexp p.1 = Eexp p.2), Ecoef p.1 * Ecoef p.2) =
        ∑ k, Ecoef k * C (Eexp k) := by
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    simp only [C]
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k' _ => ?_)
    rw [mul_ite, mul_zero]
    by_cases h : Eexp k = Eexp k'
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]
  have hD2 : (∑ k, Ecoef k * C (Eexp k)) = ∑ v ∈ vals, (C v) ^ (2 : ℕ) := by
    rw [← Finset.sum_fiberwise_of_maps_to
      (fun k (_ : k ∈ (Finset.univ : Finset (J → ι))) =>
        Finset.mem_image_of_mem Eexp (Finset.mem_univ k))
      (fun k => Ecoef k * C (Eexp k))]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    have hstep : ∀ k ∈ (Finset.univ : Finset (J → ι)).filter (fun k => Eexp k = v),
        Ecoef k * C (Eexp k) = C v * Ecoef k := by
      intro k hk
      rw [(Finset.mem_filter.mp hk).2, mul_comm]
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
    change C v * (∑ k ∈ (Finset.univ : Finset (J → ι)).filter
      (fun k => Eexp k = v), Ecoef k) = C v ^ (2 : ℕ)
    rw [show (∑ k ∈ (Finset.univ : Finset (J → ι)).filter
      (fun k => Eexp k = v), Ecoef k) = C v from rfl, sq]
  have hpos : 0 < ∑ v ∈ vals, (C v) ^ (2 : ℕ) := by
    refine Finset.sum_pos' (fun v _ => sq_nonneg _) ⟨Eexp kstar, ?_, ?_⟩
    · exact Finset.mem_image_of_mem Eexp (Finset.mem_univ kstar)
    · rw [hCstar]
      exact sq_pos_of_ne_zero hEcoefstar
  change (∑ p ∈ (Finset.univ : Finset ((J → ι) × (J → ι))).filter
    (fun p => Eexp p.1 - Eexp p.2 = 0), Ecoef p.1 * Ecoef p.2) ≠ 0
  rw [hfiltereq, hD1, hD2]
  exact ne_of_gt hpos

end GaloisForLFunctions.RHTower
