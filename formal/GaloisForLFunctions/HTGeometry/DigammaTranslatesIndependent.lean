import GaloisForLFunctions.HTGeometry.DifferenceTwoOrbitBrick
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Digamma translates on incommensurable orbits are independent

The digamma recurrence turns a relation `∑ᵢ Eᵢ ψ(z + aᵢ) = P(z)/Q(z)` into the shift-difference
equation `R(z+1) - R(z) = ∑ᵢ Eᵢ/(z + aᵢ)`, whose pole part consists of simple poles at `-aᵢ` with
residues `Eᵢ`.  When the shifts are pairwise incommensurable — no two differ by an integer — those
poles lie on pairwise incommensurable `ℤ`-orbits, and the multi-orbit difference brick forces every
residue to vanish.

So finitely many digamma translates by pairwise non-integer-differing shifts are linearly
independent over the rational functions.  The half-translate case is `d = 2` with shifts `0, 1/2`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- Numerator of `∑ᵢ Eᵢ/(z + aᵢ)` over the common denominator `∏ᵢ (z + aᵢ)`. -/
noncomputable def digammaResidueNumerator {d : ℕ} (a E : Fin d → ℂ) : Polynomial ℂ :=
  ∑ i, C (E i) * ∏ j ∈ Finset.univ.erase i, (X + C (a j))

theorem digammaResidueNumerator_natDegree_lt {d : ℕ} (a E : Fin d → ℂ) (hd : 0 < d) :
    (digammaResidueNumerator a E).natDegree < d := by
  classical
  have hbound : (digammaResidueNumerator a E).natDegree ≤ d - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    refine le_trans (Polynomial.natDegree_prod_le _ _) ?_
    have : ∀ j : Fin d, (X + C (a j) : Polynomial ℂ).natDegree ≤ 1 := fun j => by
      rw [Polynomial.natDegree_X_add_C]
    refine le_trans (Finset.sum_le_sum fun j _ => this j) ?_
    simp [Finset.card_erase_of_mem]
  omega

theorem digammaResidueNumerator_eval {d : ℕ} (a E : Fin d → ℂ) (i : Fin d) :
    (digammaResidueNumerator a E).eval (-a i) = E i * ∏ j ∈ Finset.univ.erase i, (a j - a i) := by
  classical
  rw [digammaResidueNumerator, Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single i]
  · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
      Polynomial.eval_add, Polynomial.eval_X]
    exact congrArg (fun t => E i * t) (Finset.prod_congr rfl fun j _ => by ring)
  · intro k _ hk
    have hmem : i ∈ Finset.univ.erase k := Finset.mem_erase.mpr ⟨fun hc => hk hc.symm, by simp⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
      Polynomial.eval_add, Polynomial.eval_X]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero hmem ?_)
    ring
  · intro hc
    exact absurd (Finset.mem_univ i) hc

/-- **Independence of digamma translates on incommensurable orbits.** -/
theorem digamma_translates_independent {d : ℕ} {a E : Fin d → ℂ}
    (hsep : ∀ i j : Fin d, i ≠ j → ∀ m : ℤ, a i - a j ≠ (m : ℂ))
    {P Q : Polynomial ℂ} (hQ : Q ≠ 0) (hco : IsCoprime P Q)
    {T : Set ℂ} (hT : T.Finite)
    (h : ∀ z : ℂ, (∀ i, 0 < (z + a i).re) → z ∉ T → Q.eval z ≠ 0 →
      ∑ i, E i * Complex.digamma (z + a i) = P.eval z / Q.eval z) :
    ∀ i, E i = 0 := by
  classical
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · exact fun i => absurd i.isLt (by omega)
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hune : (Finset.univ : Finset (Fin d)).Nonempty := Finset.univ_nonempty
  set R₀ : ℝ := Finset.univ.sup' hune (fun i : Fin d => -(a i).re) with hR₀
  have hRle : ∀ i : Fin d, -(a i).re ≤ R₀ := fun i =>
    Finset.le_sup' (fun i : Fin d => -(a i).re) (Finset.mem_univ i)
  have hTshift : ((fun z : ℂ => z + 1) ⁻¹' T).Finite := by
    have hinj : Function.Injective (fun z : ℂ => z + 1) := fun x y hxy => by simpa using hxy
    exact Set.Finite.preimage hinj.injOn hT
  set S : Set ℂ :=
    {z : ℂ | R₀ < z.re} \
      ({z : ℂ | Q.eval (z + 0) = 0} ∪ {z : ℂ | Q.eval (z + 1) = 0} ∪
        (T ∪ (fun z : ℂ => z + 1) ⁻¹' T)) with hS_def
  have hSinf : S.Infinite := by
    refine Set.Infinite.sdiff ?_
      (((finite_setOf_translate_isRoot hQ 0).union
        (finite_setOf_translate_isRoot hQ 1)).union (hT.union hTshift))
    apply Set.Infinite.mono (s := (fun t : ℝ => (t : ℂ)) '' (Set.Ioi R₀))
    · rintro z ⟨t, ht, rfl⟩
      simpa using ht
    · exact (Set.Ioi_infinite R₀).image Complex.ofReal_injective.injOn
  have hnegNat : ∀ w : ℂ, 0 < w.re → ∀ m : ℕ, w ≠ -(m : ℂ) := by
    intro w hw m hwm
    have := congrArg Complex.re hwm
    simp only [Complex.neg_re, Complex.natCast_re] at this
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [this] at hw
    linarith
  have hcross : ∀ z ∈ S,
      (∏ i, (z - (-(a i))) ^ (0 + 1)) *
          (P.eval (z + 1) * Q.eval z - P.eval z * Q.eval (z + 1))
        = (digammaResidueNumerator a E).eval z * (Q.eval z * Q.eval (z + 1)) := by
    intro z hz
    obtain ⟨hzre, hzbad⟩ := hz
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_preimage, not_or] at hzbad
    obtain ⟨⟨hQ0, hQ1⟩, hT0, hT1⟩ := hzbad
    have hQz : Q.eval z ≠ 0 := by simpa using hQ0
    have hQz1 : Q.eval (z + 1) ≠ 0 := hQ1
    have hpos : ∀ i, 0 < (z + a i).re := by
      intro i
      rw [Complex.add_re]
      have := hRle i
      have hzr : R₀ < z.re := hzre
      linarith
    have hpos1 : ∀ i, 0 < (z + 1 + a i).re := by
      intro i
      have := hpos i
      rw [Complex.add_re, Complex.add_re, Complex.one_re] at *
      linarith
    have hne : ∀ i, z + a i ≠ 0 := by
      intro i hc
      have := hpos i
      rw [hc] at this
      simp at this
    have hz0 := h z hpos hT0 hQz
    have hz1 := h (z + 1) hpos1 hT1 hQz1
    have hstep : ∀ i, Complex.digamma (z + 1 + a i)
        = Complex.digamma (z + a i) + (z + a i)⁻¹ := by
      intro i
      rw [show z + 1 + a i = (z + a i) + 1 by ring]
      exact Complex.digamma_apply_add_one (z + a i) (hnegNat (z + a i) (hpos i))
    rw [Finset.sum_congr rfl fun i _ => by rw [hstep i]] at hz1
    have hdiff : ∑ i, E i * (z + a i)⁻¹
        = P.eval (z + 1) / Q.eval (z + 1) - P.eval z / Q.eval z := by
      rw [← hz0, ← hz1, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hnum : (∏ i, (z + a i)) * (∑ i, E i * (z + a i)⁻¹)
        = (digammaResidueNumerator a E).eval z := by
      rw [Finset.mul_sum, digammaResidueNumerator, Polynomial.eval_finsetSum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : z + a i ≠ 0 := hne i
      rw [← Finset.mul_prod_erase Finset.univ (fun j => z + a j) (Finset.mem_univ i)]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod,
        Polynomial.eval_add, Polynomial.eval_X]
      field_simp
    have hprodne : (∏ i, (z + a i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hne i
    have hpow : (∏ i, (z - (-(a i))) ^ (0 + 1)) = ∏ i, (z + a i) :=
      Finset.prod_congr rfl fun i _ => by ring
    rw [hpow, ← hnum, hdiff]
    field_simp
  have hAzero : digammaResidueNumerator a E = 0 := by
    refine difference_multi_orbit_pole_free_of_eval (c := fun i => -(a i)) (n := fun _ => 0)
      hQ hco ?_ ?_ hSinf hcross
    · intro i j hij m hc
      exact hsep j i (fun hc' => hij hc'.symm) m (by linear_combination hc)
    · simpa using digammaResidueNumerator_natDegree_lt a E hd
  intro i
  have hane : ∀ j : Fin d, j ≠ i → a j ≠ a i := by
    intro j hj hc
    exact hsep j i hj 0 (by rw [hc]; simp)
  have heval := digammaResidueNumerator_eval a E i
  rw [hAzero] at heval
  simp only [Polynomial.eval_zero] at heval
  have hprodne : (∏ j ∈ Finset.univ.erase i, (a j - a i)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    exact sub_ne_zero.mpr (hane j hji)
  exact (mul_eq_zero.mp heval.symm).resolve_right hprodne

/-- **Independence of the digamma modes of a product of `Γ_ℝ(s + κⱼ)` factors.** The logarithmic
derivative of such a product carries one mode `ψ((s + κⱼ)/2)` per factor.  The modes are independent
over the rational functions as soon as no two exponents differ by an even integer — the condition
that puts their poles on distinct `ℤ`-orbits after the half-argument substitution.

The completed zeta factor is `d = 1`; the two-mode statement used by the parity dichotomy is `d = 2`
with `κ = (0, 1)`, where `κ₀ - κ₁ = -1` is odd. -/
theorem digamma_halfArgument_modes_independent {d : ℕ} {κ E : Fin d → ℂ}
    (hsep : ∀ i j : Fin d, i ≠ j → ∀ m : ℤ, κ i - κ j ≠ ((2 * m : ℤ) : ℂ))
    {P Q : Polynomial ℂ} (hQ : Q ≠ 0) (hco : IsCoprime P Q) {T : Set ℂ} (hT : T.Finite)
    (h : ∀ s : ℂ, (∀ i, 0 < (s + κ i).re) → s ∉ T → Q.eval s ≠ 0 →
      ∑ i, E i * Complex.digamma ((s + κ i) / 2) = P.eval s / Q.eval s) :
    ∀ i, E i = 0 := by
  classical
  have hev : ∀ (R : Polynomial ℂ) (z : ℂ),
      (R.comp (C 2 * X)).eval z = R.eval (2 * z) := by
    intro R z
    simp [Polynomial.eval_comp]
  have hQ2 : Q.comp (C 2 * X) ≠ 0 := by
    intro h0
    refine hQ (Polynomial.funext fun w => ?_)
    have hz := congrArg (Polynomial.eval (w / 2)) h0
    rw [hev] at hz
    rw [show 2 * (w / 2) = w by ring] at hz
    simpa using hz
  have hco2 : IsCoprime (P.comp (C 2 * X)) (Q.comp (C 2 * X)) := by
    obtain ⟨u, v, huv⟩ := hco
    refine ⟨u.comp (C 2 * X), v.comp (C 2 * X), ?_⟩
    have hcomp := congrArg (fun R : Polynomial ℂ => R.comp (C 2 * X)) huv
    simpa [Polynomial.add_comp, Polynomial.mul_comp, Polynomial.one_comp] using hcomp
  have hT2 : ((fun z : ℂ => 2 * z) ⁻¹' T).Finite := by
    have hinj : Function.Injective (fun z : ℂ => 2 * z) := fun x y hxy => by
      have h2 : (2 : ℂ) * x = 2 * y := hxy
      field_simp at h2
      exact h2
    exact Set.Finite.preimage hinj.injOn hT
  refine digamma_translates_independent (a := fun i => κ i / 2) (E := E) ?_ hQ2 hco2 hT2 ?_
  · intro i j hij m hc
    refine hsep i j hij m ?_
    push_cast
    linear_combination 2 * hc
  · intro z hz hzT hQz
    rw [hev] at hQz
    have hzre : ∀ i, 0 < (2 * z + κ i).re := by
      intro i
      have hi := hz i
      rw [show (2 : ℂ) * z + κ i = 2 * (z + κ i / 2) by ring]
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      linarith
    have hval := h (2 * z) hzre hzT hQz
    rw [hev, hev, ← hval]
    exact Finset.sum_congr rfl fun i _ => by
      rw [show (2 * z + κ i) / 2 = z + κ i / 2 by ring]

end GaloisForLFunctions.HTGeometry
