import GaloisForLFunctions.HTGeometry.GammaMonomialExpansion
import GaloisForLFunctions.HTGeometry.RatApproximant
import GaloisForLFunctions.HTGeometry.ShiftRatioExpansion

/-!
# A balanced gamma monomial is rationally approximable

The transseries truncation of a balanced gamma monomial is a polynomial in `1/s`, hence a rational
function, so the monomial belongs to the corpus's approximation class `HasRatApprox`.  The expansion
holds on a half plane; the tube statement follows from the functional equation, whose multiplier is
rational and tends to `1`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

/-- A shifted integer power is rational. -/
theorem hasRatApprox_shift_zpow (c : ℂ) (m : ℤ) :
    HasRatApprox (fun s : ℂ => (s + c) ^ m) := by
  rcases le_or_gt 0 m with hm | hm
  · have hfun : (fun s : ℂ => (s + c) ^ m)
        = fun s : ℂ => Polynomial.eval s ((X + C c) ^ m.toNat)
            / Polynomial.eval s (1 : Polynomial ℂ) := by
      funext s
      rw [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_one, div_one, ← zpow_natCast, Int.toNat_of_nonneg hm]
    rw [hfun]
    exact hasRatApprox_ratEval _ one_ne_zero
  · have hfun : (fun s : ℂ => (s + c) ^ m)
        = fun s : ℂ => Polynomial.eval s (1 : Polynomial ℂ)
            / Polynomial.eval s ((X + C c) ^ (-m).toNat) := by
      funext s
      rw [Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
        Polynomial.eval_one, ← zpow_natCast, Int.toNat_of_nonneg (by omega : (0:ℤ) ≤ -m),
        zpow_neg, one_div, inv_inv]
    rw [hfun]
    exact hasRatApprox_ratEval _ (pow_ne_zero _ (Polynomial.X_add_C_ne_zero c))

theorem HasRatApprox.finsetProd {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ s, HasRatApprox (f i)) : HasRatApprox (fun z => ∏ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hfun : (fun z : ℂ => ∏ i ∈ (∅ : Finset ι), f i z) = fun _ : ℂ => (1 : ℂ) := by
        funext z; simp
      rw [hfun]
      exact hasRatApprox_const 1
  | insert a s ha ih =>
      have hfun : (fun z : ℂ => ∏ i ∈ insert a s, f i z)
          = fun z : ℂ => f a z * ∏ i ∈ s, f i z := by
        funext z
        rw [Finset.prod_insert ha]
      rw [hfun]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem HasRatApprox.finsetSum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ)
    (h : ∀ i ∈ s, HasRatApprox (f i)) : HasRatApprox (fun z => ∑ i ∈ s, f i z) := by
  classical
  induction s using Finset.induction with
  | empty =>
      have hfun : (fun z : ℂ => ∑ i ∈ (∅ : Finset ι), f i z) = fun _ : ℂ => (0 : ℂ) := by
        funext z; simp
      rw [hfun]
      exact hasRatApprox_const 0
  | insert a s ha ih =>
      have hfun : (fun z : ℂ => ∑ i ∈ insert a s, f i z)
          = fun z : ℂ => f a z + ∑ i ∈ s, f i z := by
        funext z
        rw [Finset.sum_insert ha]
      rw [hfun]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Approximability only depends on the values on tubes. -/
theorem hasRatApprox_of_tube_eq {f h : ℂ → ℂ} (hh : HasRatApprox h)
    (heq : ∀ M : ℝ, 0 < M → ∃ T : ℝ, 2 ≤ T ∧ ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t →
      f ((σ : ℂ) + (t : ℂ) * Complex.I) = h ((σ : ℂ) + (t : ℂ) * Complex.I)) :
    HasRatApprox f := by
  intro M hM N
  obtain ⟨p, q, C, T, hq, hC, hT, hb⟩ := hh M hM N
  obtain ⟨T', hT', heq'⟩ := heq M hM
  refine ⟨p, q, C, max T T', hq, hC, le_trans hT (le_max_left _ _), fun σ t hσ hσM ht => ?_⟩
  rw [heq' σ t hσ hσM (le_trans (le_max_right _ _) ht)]
  exact hb σ t hσ hσM (le_trans (le_max_left _ _) ht)

/-- A vertical-tube point is never a negative real shift of the origin. -/
theorem tube_add_real_ne_zero {σ t a : ℝ} (ht : 0 < t) :
    (σ : ℂ) + (t : ℂ) * Complex.I + (a : ℂ) ≠ 0 := by
  intro hcon
  have him : ((σ : ℂ) + (t : ℂ) * Complex.I + (a : ℂ)).im = t := by simp
  rw [hcon] at him
  simp only [Complex.zero_im] at him
  linarith

/-- A polynomial evaluated at the reciprocal of a real shift is rational. -/
theorem hasRatApprox_polyEval_inv_shift (Q : Polynomial ℂ) (a : ℝ) :
    HasRatApprox (fun s : ℂ => Q.eval (s + (a : ℂ))⁻¹) := by
  have hne : ((X + C (a : ℂ)) ^ Q.natDegree : Polynomial ℂ) ≠ 0 :=
    pow_ne_zero _ (Polynomial.X_add_C_ne_zero _)
  have hrat : HasRatApprox (fun s : ℂ =>
      Polynomial.eval s ((invReverse Q).comp (X + C (a : ℂ)))
        / Polynomial.eval s ((X + C (a : ℂ)) ^ Q.natDegree)) :=
    hasRatApprox_ratEval _ hne
  refine hasRatApprox_of_tube_eq hrat fun M _ => ⟨2, le_rfl, fun σ t _ _ ht => ?_⟩
  have htpos : (0 : ℝ) < t := by linarith
  have hsa : (σ : ℂ) + (t : ℂ) * Complex.I + (a : ℂ) ≠ 0 := tube_add_real_ne_zero htpos
  rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  have h := eval_inv_eq_div Q hsa
  rw [Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [← one_div]
  exact h

/-- The `n`-fold functional equation, with no half-plane hypothesis. -/
theorem gammaMonomial_shift_nat_of_ne {r : ℕ} (lam : Fin r → ℂ) (g : Fin r → ℤ) {s : ℂ}
    (hz : ∀ (j : ℕ) (k : Fin r), s + (j : ℂ) + lam k ≠ 0) (n : ℕ) :
    gammaMonomial lam g (s + (n : ℂ))
      = (∏ j ∈ Finset.range n, ∏ k, (s + (j : ℂ) + lam k) ^ (g k)) * gammaMonomial lam g s := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hrw : s + ((n + 1 : ℕ) : ℂ) = (s + (n : ℂ)) + 1 := by push_cast; ring
      rw [hrw, gammaMonomial_shift lam g (fun k => hz n k), ih, Finset.prod_range_succ]
      ring

/-- **A balanced gamma monomial is rationally approximable.** -/
theorem hasRatApprox_gammaMonomial {r : ℕ} (lam : Fin r → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (g : Fin r → ℤ) (hdeg : ∑ i, g i = 0) (hmom : ∑ i, (g i : ℝ) * lam i = 0) :
    HasRatApprox (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g) := by
  have hdegneg : ∑ i, (-(g i)) = 0 := by
    rw [Finset.sum_neg_distrib, hdeg, neg_zero]
  have hmomC : ∑ i, ((g i : ℤ) : ℂ) * ((lam i : ℝ) : ℂ) = 0 := by
    have hcast : ((∑ i, (g i : ℝ) * lam i : ℝ) : ℂ) = 0 := by rw [hmom]; simp
    rw [← hcast]; push_cast; ring
  have hmomnegC : ∑ i, (((-(g i)) : ℤ) : ℂ) * ((lam i : ℝ) : ℂ) = 0 := by
    rw [← neg_eq_zero.mpr hmomC, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by push_cast; ring
  obtain ⟨K, Rb, hK0, hRb0, hKb⟩ := exists_norm_shiftRatio_sub_one_le
    (fun i => ((lam i : ℝ) : ℂ)) (fun i => -(g i)) hdegneg hmomnegC
  intro Mt hMt N
  obtain ⟨A, R₀, hA0, hR₀, hexp⟩ := exists_norm_gammaMonomial_expansion lam hlam g hdeg hmom N
  set n : ℕ := ⌈R₀⌉₊ + 1 with hndef
  have hnR₀ : R₀ < (n : ℝ) := by
    have h := Nat.le_ceil R₀
    rw [hndef]
    push_cast
    linarith
  set G : ℂ → ℂ := fun s => (gammaExpPoly lam g N).eval (s + (((n : ℝ)) : ℂ))⁻¹
    * ∏ j ∈ Finset.range n, ∏ k, (s + ((((j : ℝ) + lam k) : ℝ) : ℂ)) ^ (-(g k)) with hGdef
  have hGrat : HasRatApprox G := by
    rw [hGdef]
    refine (hasRatApprox_polyEval_inv_shift _ ((n : ℝ))).mul ?_
    refine HasRatApprox.finsetProd _ _ fun j _ => ?_
    exact HasRatApprox.finsetProd _ _ fun k _ =>
      hasRatApprox_shift_zpow ((((j : ℝ) + lam k) : ℝ) : ℂ) (-(g k))
  obtain ⟨p, q, C, T, hq, hC0, hT2, hGb⟩ := hGrat Mt hMt N
  refine ⟨p, q, C + 2 ^ n * A, max (max T Rb) (max 2 (K + 1)), hq, by positivity, ?_, ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  intro σ t hσ hσM ht
  have htT : T ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) ht
  have htRb : Rb ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) ht
  have ht2 : (2 : ℝ) ≤ t := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht
  have htK : K + 1 ≤ t := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht
  have htpos : (0 : ℝ) < t := by linarith
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hsdef
  have hsim : s.im = t := by rw [hsdef]; simp
  have hsre : s.re = σ := by rw [hsdef]; simp
  have hzne : ∀ (j : ℕ) (k : Fin r), s + (j : ℂ) + ((lam k : ℝ) : ℂ) ≠ 0 := by
    intro j k hcon
    have him : (s + (j : ℂ) + ((lam k : ℝ) : ℂ)).im = t := by
      rw [Complex.add_im, Complex.add_im, hsim, Complex.natCast_im, Complex.ofReal_im]
      ring
    rw [hcon] at him
    simp only [Complex.zero_im] at him
    linarith
  have htsn : t ≤ ‖s + ((n : ℝ) : ℂ)‖ := by
    have him : (s + ((n : ℝ) : ℂ)).im = t := by
      rw [Complex.add_im, hsim, Complex.ofReal_im, add_zero]
    calc t = (s + ((n : ℝ) : ℂ)).im := him.symm
      _ ≤ |(s + ((n : ℝ) : ℂ)).im| := le_abs_self _
      _ ≤ ‖s + ((n : ℝ) : ℂ)‖ := Complex.abs_im_le_norm _
  -- the multiplier and its inverse
  have hprodrw : ∀ j : ℕ, ∀ k : Fin r,
      s + (j : ℂ) + ((lam k : ℝ) : ℂ) = s + ((((j : ℝ) + lam k) : ℝ) : ℂ) := by
    intro j k
    push_cast
    ring
  have hinv : ∀ j : ℕ,
      (∏ k, (s + (j : ℂ) + ((lam k : ℝ) : ℂ)) ^ (g k))
        * (∏ k, (s + ((((j : ℝ) + lam k) : ℝ) : ℂ)) ^ (-(g k))) = 1 := by
    intro j
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [hprodrw j k, ← zpow_add₀ (by rw [← hprodrw j k]; exact hzne j k)]
    simp
  have hshift := gammaMonomial_shift_nat_of_ne (fun i => ((lam i : ℝ) : ℂ)) g hzne n
  have hnc : ((n : ℂ)) = (((n : ℝ)) : ℂ) := by push_cast; ring
  rw [hnc] at hshift
  -- the value identity
  have hcollapse : (∏ j ∈ Finset.range n, ∏ k, (s + (j : ℂ) + ((lam k : ℝ) : ℂ)) ^ (g k))
      * (∏ j ∈ Finset.range n, ∏ k, (s + ((((j : ℝ) + lam k) : ℝ) : ℂ)) ^ (-(g k))) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => hinv j
  have hval : gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s
      = gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g (s + ((n : ℝ) : ℂ))
        * ∏ j ∈ Finset.range n, ∏ k, (s + ((((j : ℝ) + lam k) : ℝ) : ℂ)) ^ (-(g k)) := by
    rw [hshift, mul_assoc,
      mul_comm (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s)
        (∏ j ∈ Finset.range n, ∏ k, (s + ((((j : ℝ) + lam k) : ℝ) : ℂ)) ^ (-(g k))),
      ← mul_assoc, hcollapse, one_mul]
  -- the multiplier bound
  have hrhob : ‖∏ j ∈ Finset.range n, ∏ k, (s + ((((j : ℝ) + lam k) : ℝ) : ℂ)) ^ (-(g k))‖
      ≤ 2 ^ n := by
    rw [norm_prod]
    have hstep : ∀ j ∈ Finset.range n,
        ‖∏ k, (s + ((((j : ℝ) + lam k) : ℝ) : ℂ)) ^ (-(g k))‖ ≤ 2 := by
      intro j _
      have hsj : ‖s + (j : ℂ)‖ ≥ t := by
        have him : (s + (j : ℂ)).im = t := by
          rw [Complex.add_im, hsim, Complex.natCast_im, add_zero]
        calc t = (s + (j : ℂ)).im := him.symm
          _ ≤ |(s + (j : ℂ)).im| := le_abs_self _
          _ ≤ ‖s + (j : ℂ)‖ := Complex.abs_im_le_norm _
      have hb := hKb (s + (j : ℂ)) (by linarith) (fun k => by
        have := hzne j k
        rw [add_assoc] at this ⊢
        exact this)
      have heqp : ∏ k, ((s + (j : ℂ)) + ((lam k : ℝ) : ℂ)) ^ (-(g k))
          = ∏ k, (s + ((((j : ℝ) + lam k) : ℝ) : ℂ)) ^ (-(g k)) := by
        refine Finset.prod_congr rfl fun k _ => ?_
        rw [hprodrw j k]
      rw [heqp] at hb
      have hKt : K / ‖s + (j : ℂ)‖ ^ 2 ≤ 1 := by
        have hpos : (0 : ℝ) < ‖s + (j : ℂ)‖ := by linarith
        rw [div_le_one (by positivity)]
        nlinarith [hsj, htK, hK0]
      have hnn := norm_sub_norm_le (∏ k, (s + ((((j : ℝ) + lam k) : ℝ) : ℂ)) ^ (-(g k))) (1 : ℂ)
      rw [norm_one] at hnn
      linarith [hb, hnn, hKt]
    calc ∏ j ∈ Finset.range n, ‖∏ k, (s + ((((j : ℝ) + lam k) : ℝ) : ℂ)) ^ (-(g k))‖
        ≤ ∏ _j ∈ Finset.range n, (2 : ℝ) :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) hstep
      _ = 2 ^ n := by simp
  -- the expansion bound
  have hre : R₀ < (s + ((n : ℝ) : ℂ)).re := by
    rw [Complex.add_re, hsre, Complex.ofReal_re]
    linarith
  have hb := hexp (s + ((n : ℝ) : ℂ)) hre
  -- assemble
  have hdiff : ‖gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s - G s‖ ≤ 2 ^ n * A / t ^ N := by
    have hGs : G s = (gammaExpPoly lam g N).eval (s + ((n : ℝ) : ℂ))⁻¹
        * ∏ j ∈ Finset.range n, ∏ k, (s + ((((j : ℝ) + lam k) : ℝ) : ℂ)) ^ (-(g k)) := rfl
    rw [hval, hGs, ← sub_mul, norm_mul]
    have h1 : ‖gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g (s + ((n : ℝ) : ℂ))
        - (gammaExpPoly lam g N).eval (s + ((n : ℝ) : ℂ))⁻¹‖ ≤ A / t ^ (N + 1) := by
      refine le_trans hb ?_
      have hden : t ^ (N + 1) ≤ ‖s + ((n : ℝ) : ℂ)‖ ^ (N + 1) :=
        pow_le_pow_left₀ (by linarith) htsn _
      exact div_le_div_of_nonneg_left hA0 (by positivity) hden
    have hmul := mul_le_mul h1 hrhob (norm_nonneg _) (by positivity)
    refine le_trans hmul ?_
    have heq : A / t ^ (N + 1) * 2 ^ n = 2 ^ n * A / t ^ (N + 1) := by ring
    rw [heq]
    have hmono : t ^ N ≤ t ^ (N + 1) := by
      have ht1 : (1 : ℝ) ≤ t := by linarith
      have hpn : (0 : ℝ) ≤ t ^ N := by positivity
      calc t ^ N = t ^ N * 1 := by ring
        _ ≤ t ^ N * t := by nlinarith
        _ = t ^ (N + 1) := by ring
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) hmono
  have hGbs := hGb σ t hσ hσM htT
  rw [← hsdef] at hGbs
  have htri : ‖gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s
      - Polynomial.eval s p / Polynomial.eval s q‖
      ≤ ‖gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s - G s‖
        + ‖G s - Polynomial.eval s p / Polynomial.eval s q‖ := by
    have hsplit : gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s
        - Polynomial.eval s p / Polynomial.eval s q
        = (gammaMonomial (fun i => ((lam i : ℝ) : ℂ)) g s - G s)
          + (G s - Polynomial.eval s p / Polynomial.eval s q) := by ring
    rw [hsplit]
    exact norm_add_le _ _
  have hsum : 2 ^ n * A / t ^ N + C / t ^ N = (C + 2 ^ n * A) / t ^ N := by ring
  linarith [hdiff, hGbs, htri]

end

end GaloisForLFunctions.HTGeometry
