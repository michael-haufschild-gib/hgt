import GaloisForLFunctions.HTGeometry.CosineStepHeightMajorization
import GaloisForLFunctions.HTGeometry.RiemannGaussian.FiniteRealRootDecomposition

/-!
# Squared-height majorization for products of cosine steps

For a nonzero real polynomial `A` write `U(A)` for its roots in the open upper half-plane (with
multiplicity).  For `a ≥ 0` and every `σ ≥ 0`,

`Σ_{w root of cos(aD)A} (Im w − σ)_+ ≤ Σ_{u ∈ U(A)} (√((Im u)² − a²) − σ)_+`
(`sum_roots_shiftAvg_im_sub_pos_le_upperRoots`),

which is the cosine height majorization stated for an arbitrary real polynomial: every such `A`
is `pairRootPoly` of its upper roots and real roots (`exists_eq_pairRootPoly`).

Weak majorization passes to squares at every threshold (`sum_max_sq_sub_le_of_majorization`):
`(t⁺)² − s` is `((t − √s)_+)² + 2√s (t − √s)_+` above the threshold.  Since `x ↦ (x − a²)_+` is
convex and increasing, squared majorization iterates.  For shifts `a₁, …, a_n ≥ 0` the product
`cos(a₁D) ⋯ cos(a_nD) A` (`cosProd`) satisfies, for every `s ≥ 0`,

`Σ_w ((Im w)⁺² − s)_+ ≤ Σ_{u ∈ U(A)} ((Im u)² − Σ a_k² − s)_+`
(`sum_roots_cosProd_sq_sub_le`).

This is the law for every vertical average `E A(z + iX)` with `X = Σ a_k ε_k` a sum of independent
symmetric signs; the squared heights lose exactly the variance `E X²`.
-/

open Polynomial Complex Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Roots of a real polynomial in the open upper half-plane, with multiplicity. -/
abbrev upperRoots (A : ℝ[X]) : Multiset ℂ := RiemannGaussian.realPolynomialUpperRootMultiset A

theorem mem_upperRoots_im_pos {A : ℝ[X]} {u : ℂ} (hu : u ∈ upperRoots A) : 0 < u.im :=
  (Multiset.mem_filter.mp hu).2

/-- `(X − z)(X − z̄) = (X − Re z)² + (Im z)²`. -/
theorem X_sub_C_mul_X_sub_C_conj (z : ℂ) :
    (X - C z) * (X - C ((starRingEnd ℂ) z)) =
      (X - C ((z.re : ℝ) : ℂ)) ^ 2 + C (((z.im ^ 2 : ℝ)) : ℂ) := by
  set u := z.re with hu
  set v := z.im with hv
  have hzc : (starRingEnd ℂ) z = (u : ℂ) - (v : ℂ) * I := by
    apply Complex.ext <;> simp [hu, hv]
  have hz : z = (u : ℂ) + (v : ℂ) * I := by
    apply Complex.ext <;> simp [hu, hv]
  rw [hzc, hz]
  simp only [C_add, C_sub, C_mul, ofReal_pow, C_pow]
  have hI : (C I : ℂ[X]) ^ 2 = -1 := by rw [← C_pow, I_sq, C_neg, C_1]
  linear_combination (-(C (v : ℂ)) ^ 2) * hI

/-- **Every nonzero real polynomial is `pairRootPoly` of its upper and real roots.** -/
theorem exists_eq_pairRootPoly (A : ℝ[X]) :
    ∃ (m l : ℕ) (x y : Fin m → ℝ) (r : Fin l → ℝ),
      A = pairRootPoly A.leadingCoeff x y r ∧
        (Finset.univ.val.map fun j => (⟨x j, y j⟩ : ℂ)) = upperRoots A := by
  classical
  set LU := (upperRoots A).toList with hLU
  set LR := (RiemannGaussian.realPolynomialRealRootMultiset A).toList with hLR
  refine ⟨LU.length, LR.length, fun j => LU[j.1].re, fun j => LU[j.1].im,
    fun k => LR[k.1].re, ?_, ?_⟩
  · apply Polynomial.map_injective Complex.ofRealHom Complex.ofRealHom.injective
    set P := A.map Complex.ofRealHom with hP
    have hsplit : C P.leadingCoeff * (P.roots.map fun z => X - C z).prod = P :=
      C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree
    have hlc : P.leadingCoeff = ((A.leadingCoeff : ℝ) : ℂ) := by
      rw [hP, leadingCoeff_map_of_injective Complex.ofRealHom.injective]; rfl
    rw [← hsplit, hlc, RiemannGaussian.realPolynomial_roots_eq_real_add_conjugatePairs A]
    simp only [RiemannGaussian.conjugatePairRootMultiset, Multiset.map_add, Multiset.prod_add,
      Multiset.map_map, Function.comp_def]
    -- real roots
    have hreal : ((RiemannGaussian.realPolynomialRealRootMultiset A).map fun z => X - C z).prod =
        ∏ k : Fin LR.length, (X - C ((LR[k.1].re : ℝ) : ℂ)) := by
      have h1 : ∀ k : Fin LR.length, ((LR[k.1].re : ℝ) : ℂ) = LR[k.1] := by
        intro k
        have hmem : LR[k.1] ∈ RiemannGaussian.realPolynomialRealRootMultiset A := by
          rw [← Multiset.mem_toList]; exact List.getElem_mem _
        exact Complex.ext (by simp) (by simp [(Multiset.mem_filter.mp hmem).2])
      simp_rw [h1]
      rw [Fin.prod_univ_fun_getElem LR (fun z => X - C z), ← Multiset.prod_coe,
        ← Multiset.map_coe, hLR, Multiset.coe_toList]
    -- conjugate pairs
    have hpair : ((upperRoots A).map fun z => X - C z).prod *
        ((upperRoots A).map fun z => X - C ((starRingEnd ℂ) z)).prod =
        ∏ j : Fin LU.length,
          ((X - C ((LU[j.1].re : ℝ) : ℂ)) ^ 2 + C (((LU[j.1].im ^ 2 : ℝ)) : ℂ)) := by
      rw [← Multiset.prod_map_mul]
      simp_rw [X_sub_C_mul_X_sub_C_conj]
      rw [Fin.prod_univ_fun_getElem LU
        (fun z => (X - C ((z.re : ℝ) : ℂ)) ^ 2 + C (((z.im ^ 2 : ℝ)) : ℂ)),
        ← Multiset.prod_coe, ← Multiset.map_coe, hLU, Multiset.coe_toList]
    simp only [pairRootPoly, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod,
      Polynomial.map_add, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X]
    rw [hreal, hpair]
    simp only [Complex.ofRealHom_eq_coe]
    ring
  · rw [Fin.univ_val_map]
    have : List.ofFn (fun j : Fin LU.length => (⟨LU[j.1].re, LU[j.1].im⟩ : ℂ)) = LU := by
      simp only [Complex.eta]
      exact List.ofFn_getElem
    rw [this, hLU, Multiset.coe_toList]

/-- **Cosine height majorization for an arbitrary real polynomial.** -/
theorem sum_roots_shiftAvg_im_sub_pos_le_upperRoots {A : ℝ[X]} (hA : A ≠ 0) {a σ : ℝ}
    (ha : 0 ≤ a) (hσ : 0 ≤ σ) :
    (((shiftAvg a A).map ofRealHom).roots.map fun w => max (w.im - σ) 0).sum ≤
      ((upperRoots A).map fun u => max (Real.sqrt (u.im ^ 2 - a ^ 2) - σ) 0).sum := by
  obtain ⟨m, l, x, y, r, hAeq, hU⟩ := exists_eq_pairRootPoly A
  have hκ : A.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hA
  have h := sum_roots_shiftAvg_im_sub_pos_le A.leadingCoeff hκ x y r ha hσ
  rw [← hAeq] at h
  refine h.trans (le_of_eq ?_)
  rw [← hU, Multiset.map_map]
  rfl

/-- **Weak majorization controls squares above every threshold.** -/
theorem sum_max_sq_le_of_majorization (h ρ : Multiset ℝ)
    (H : ∀ σ, 0 ≤ σ → (h.map fun t => max (t - σ) 0).sum ≤ (ρ.map fun t => max (t - σ) 0).sum) :
    (h.map fun t => (max t 0) ^ 2).sum ≤ (ρ.map fun t => (max t 0) ^ 2).sum := by
  set M : ℝ := (h.map fun t => |t|).sum + (ρ.map fun t => |t|).sum with hMdef
  have habs : ∀ s : Multiset ℝ, 0 ≤ (s.map fun t => |t|).sum := fun s =>
    Multiset.sum_nonneg fun z hz => by
      obtain ⟨w, -, rfl⟩ := Multiset.mem_map.mp hz; exact abs_nonneg w
  have hM0 : 0 ≤ M := by rw [hMdef]; linarith [habs h, habs ρ]
  have hle : ∀ s : Multiset ℝ, ∀ w ∈ s, w ≤ (s.map fun t => |t|).sum := by
    intro s w hw
    have h1 : |w| ≤ (s.map fun t => |t|).sum :=
      Multiset.single_le_sum (fun z hz => by
        obtain ⟨u, -, rfl⟩ := Multiset.mem_map.mp hz; exact abs_nonneg u) _
        (Multiset.mem_map_of_mem _ hw)
    linarith [le_abs_self w]
  have hhM : ∀ w ∈ h, w ≤ M := fun w hw => by
    have := hle h w hw; rw [hMdef]; linarith [habs ρ]
  have hρM : ∀ w ∈ ρ, w ≤ M := fun w hw => by
    have := hle ρ w hw; rw [hMdef]; linarith [habs h]
  have hcont : ∀ t : Multiset ℝ, Continuous fun σ : ℝ => (t.map fun w => max (w - σ) 0).sum := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp; fun_prop
    | cons w t ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      exact (by fun_prop : Continuous fun σ : ℝ => max (w - σ) 0).add ih
  have hint : ∀ t : Multiset ℝ, (∀ w ∈ t, w ≤ M) →
      ∫ σ in (0 : ℝ)..M, (t.map fun w => max (w - σ) 0).sum =
        (t.map fun w => (max w 0) ^ 2 / 2).sum := by
    intro t
    induction t using Multiset.induction_on with
    | empty => intro _; simp
    | cons w t ih =>
      intro ht
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [intervalIntegral.integral_add
        ((by fun_prop : Continuous fun σ : ℝ => max (w - σ) 0).intervalIntegrable 0 M)
        ((hcont t).intervalIntegrable 0 M),
        integral_max_sub_zero (ht w (Multiset.mem_cons_self w t)) hM0,
        ih fun u hu => ht u (Multiset.mem_cons_of_mem hu)]
  have hmono : ∫ σ in (0 : ℝ)..M, (h.map fun w => max (w - σ) 0).sum ≤
      ∫ σ in (0 : ℝ)..M, (ρ.map fun w => max (w - σ) 0).sum :=
    intervalIntegral.integral_mono_on hM0 ((hcont h).intervalIntegrable 0 M)
      ((hcont ρ).intervalIntegrable 0 M) fun σ hσ => H σ hσ.1
  rw [hint h hhM, hint ρ hρM] at hmono
  have e : ∀ s : Multiset ℝ, (s.map fun w => (max w 0) ^ 2 / 2).sum =
      (s.map fun w => (max w 0) ^ 2).sum / 2 := fun s => by rw [Multiset.sum_map_div]
  rw [e, e] at hmono
  linarith

/-- `((t⁺)² − s)_+ = ((t − √s)_+)² + 2√s (t − √s)_+`. -/
theorem max_sq_sub_eq (t : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    max ((max t 0) ^ 2 - s) 0 =
      (max (t - Real.sqrt s) 0) ^ 2 + 2 * Real.sqrt s * max (t - Real.sqrt s) 0 := by
  have hc := Real.sqrt_nonneg s
  have hcs := Real.sq_sqrt hs
  rcases le_total t (Real.sqrt s) with h | h
  · rw [max_eq_right (by linarith : t - Real.sqrt s ≤ 0),
      show (0 : ℝ) ^ 2 + 2 * Real.sqrt s * 0 = 0 by ring]
    refine max_eq_right ?_
    rcases le_total t 0 with h0 | h0
    · rw [max_eq_right h0]; linarith
    · rw [max_eq_left h0]; nlinarith
  · rw [max_eq_left (by linarith : 0 ≤ t - Real.sqrt s), max_eq_left (by linarith : 0 ≤ t),
      max_eq_left (by nlinarith)]
    nlinarith

/-- **Squared majorization at every threshold.** -/
theorem sum_max_sq_sub_le_of_majorization (h ρ : Multiset ℝ)
    (H : ∀ σ, 0 ≤ σ → (h.map fun t => max (t - σ) 0).sum ≤ (ρ.map fun t => max (t - σ) 0).sum)
    {s : ℝ} (hs : 0 ≤ s) :
    (h.map fun t => max ((max t 0) ^ 2 - s) 0).sum ≤
      (ρ.map fun t => max ((max t 0) ^ 2 - s) 0).sum := by
  set c := Real.sqrt s with hc
  have hc0 : 0 ≤ c := Real.sqrt_nonneg s
  have hshift := sum_max_sq_le_of_majorization (h.map fun t => t - c) (ρ.map fun t => t - c)
    (fun (σ : ℝ) (hσ : 0 ≤ σ) => by
      simp only [Multiset.map_map, Function.comp_def, sub_sub]
      exact H (c + σ) (by linarith))
  simp only [Multiset.map_map, Function.comp_def] at hshift
  have hlin := H c hc0
  have expand : ∀ t : Multiset ℝ, (t.map fun w => max ((max w 0) ^ 2 - s) 0).sum =
      (t.map fun w => (max (w - c) 0) ^ 2).sum + 2 * c * (t.map fun w => max (w - c) 0).sum := by
    intro t
    rw [Multiset.sum_map_mul_left.symm, ← Multiset.sum_map_add]
    congr 1
    exact Multiset.map_congr rfl fun w _ => by rw [max_sq_sub_eq w hs]
  rw [expand, expand]
  nlinarith

/-- `cos(a₁D) ⋯ cos(a_nD) A`. -/
def cosProd (as : List ℝ) (A : ℝ[X]) : ℝ[X] := as.foldr shiftAvg A

/-- The shift average of a nonzero polynomial is nonzero. -/
theorem shiftAvg_ne_zero {A : ℝ[X]} (hA : A ≠ 0) (a : ℝ) : shiftAvg a A ≠ 0 := by
  intro h0
  have hmap := congrArg (Polynomial.map Complex.ofRealHom) h0
  rw [map_shiftAvg, Polynomial.map_zero] at hmap
  set P := A.map Complex.ofRealHom with hP
  have hP0 : P ≠ 0 := (Polynomial.map_ne_zero_iff Complex.ofRealHom.injective).mpr hA
  set d := P.natDegree
  have hcomp : ∀ c : ℂ, (P.comp (X + C c)).coeff d = P.leadingCoeff := by
    intro c
    have hdeg : (P.comp (X + C c)).natDegree = d := by
      rw [natDegree_comp, natDegree_X_add_C, mul_one]
    rw [← hdeg, coeff_natDegree, leadingCoeff_comp (by rw [natDegree_X_add_C]; norm_num),
      leadingCoeff_X_add_C, one_pow, mul_one]
  have h2 := congrArg (fun Q : ℂ[X] => Q.coeff d) hmap
  simp only [shiftAvgC, coeff_C_mul, coeff_add, coeff_zero] at h2
  rw [sub_eq_add_neg, ← C_neg, ← hP, hcomp, hcomp] at h2
  have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
  apply hlc
  linear_combination h2

theorem cosProd_ne_zero {A : ℝ[X]} (hA : A ≠ 0) : ∀ as : List ℝ, cosProd as A ≠ 0
  | [] => hA
  | a :: as => shiftAvg_ne_zero (cosProd_ne_zero hA as) a

/-- A root sum whose terms vanish off the open upper half-plane is a sum over the upper roots. -/
theorem sum_upperRoots_eq_sum_roots (B : ℝ[X]) (f : ℂ → ℝ)
    (hf : ∀ w : ℂ, w.im ≤ 0 → f w = 0) :
    ((upperRoots B).map f).sum = (((B.map ofRealHom).roots).map f).sum := by
  have hsplit := Multiset.filter_add_not (fun z : ℂ => 0 < z.im) (B.map ofRealHom).roots
  conv_rhs => rw [← hsplit]
  rw [Multiset.map_add, Multiset.sum_add]
  have hz : ((((B.map ofRealHom).roots).filter fun z => ¬ 0 < z.im).map f).sum = 0 := by
    apply Multiset.sum_eq_zero
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Multiset.mem_map.mp hx
    exact hf w (not_lt.mp (Multiset.mem_filter.mp hw).2)
  rw [hz, add_zero]
  rfl

/-- The squared-height threshold sum of a real polynomial, read on its upper roots. -/
theorem sum_upperRoots_max_sub_eq (B : ℝ[X]) {c : ℝ} (hc : 0 ≤ c) :
    ((upperRoots B).map fun u => max (u.im ^ 2 - c) 0).sum =
      (((B.map ofRealHom).roots).map fun w => max ((max w.im 0) ^ 2 - c) 0).sum := by
  rw [← sum_upperRoots_eq_sum_roots B (fun w => max ((max w.im 0) ^ 2 - c) 0)
    (fun w hw => by rw [max_eq_right hw]; simp; linarith)]
  congr 1
  refine Multiset.map_congr rfl fun u hu => ?_
  rw [max_eq_left (mem_upperRoots_im_pos hu).le]

/-- **Squared-height majorization for products of cosine steps.** -/
theorem sum_roots_cosProd_sq_sub_le {A : ℝ[X]} (hA : A ≠ 0) :
    ∀ (as : List ℝ), (∀ a ∈ as, 0 ≤ a) → ∀ {s : ℝ}, 0 ≤ s →
      ((((cosProd as A).map ofRealHom).roots).map fun w => max ((max w.im 0) ^ 2 - s) 0).sum ≤
        ((upperRoots A).map fun u =>
          max (u.im ^ 2 - (as.map fun a => a ^ 2).sum - s) 0).sum
  | [], _, s, hs => by
    simp only [cosProd, List.foldr_nil, List.map_nil, List.sum_nil, sub_zero]
    rw [sum_upperRoots_max_sub_eq A hs]
  | a :: as, has, s, hs => by
    have ha : 0 ≤ a := has a List.mem_cons_self
    have has' : ∀ b ∈ as, 0 ≤ b := fun b hb => has b (List.mem_cons_of_mem a hb)
    set B := cosProd as A with hB
    have hB0 : B ≠ 0 := cosProd_ne_zero hA as
    have hstep : cosProd (a :: as) A = shiftAvg a B := rfl
    rw [hstep]
    -- one cosine step, squared
    have H : ∀ σ : ℝ, 0 ≤ σ →
        (((((shiftAvg a B).map ofRealHom).roots).map Complex.im).map
          fun t => max (t - σ) 0).sum ≤
        (((upperRoots B).map fun u => Real.sqrt (u.im ^ 2 - a ^ 2)).map
          fun t => max (t - σ) 0).sum := by
      intro σ hσ
      simp only [Multiset.map_map, Function.comp_def]
      exact sum_roots_shiftAvg_im_sub_pos_le_upperRoots hB0 ha hσ
    have hsq := sum_max_sq_sub_le_of_majorization _ _ H hs
    simp only [Multiset.map_map, Function.comp_def] at hsq
    have hrhs : ((upperRoots B).map fun u =>
        max ((max (Real.sqrt (u.im ^ 2 - a ^ 2)) 0) ^ 2 - s) 0).sum =
        ((upperRoots B).map fun u => max (u.im ^ 2 - (a ^ 2 + s)) 0).sum := by
      congr 1
      refine Multiset.map_congr rfl fun u _ => ?_
      rw [max_eq_left (Real.sqrt_nonneg _)]
      rcases le_total 0 (u.im ^ 2 - a ^ 2) with h0 | h0
      · rw [Real.sq_sqrt h0]; ring_nf
      · rw [Real.sqrt_eq_zero'.mpr h0]
        rw [max_eq_right (by nlinarith), max_eq_right (by linarith)]
    rw [hrhs, sum_upperRoots_max_sub_eq B (by positivity)] at hsq
    refine hsq.trans ((sum_roots_cosProd_sq_sub_le hA as has' (by positivity)).trans (le_of_eq ?_))
    congr 1
    refine Multiset.map_congr rfl fun u _ => ?_
    simp only [List.map_cons, List.sum_cons]
    ring_nf

end

end GaloisForLFunctions.HTGeometry
