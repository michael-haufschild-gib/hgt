import GaloisForLFunctions.HTGeometry.BindSubstitutionNonvanishing

/-!
# Polynomial multipliers and functional hypertranscendence

The Leibniz jet map of multiplication by a nonzero polynomial is triangular with that polynomial
on every diagonal layer.  Its point map covers the complement of the polynomial's zero locus, so
the generic substitution-nonvanishing theorem transports a differential relation back through the
multiplier.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The jet variable of order `j`, with a zero extension outside an order-`n` packet. -/
def mulPolynomialJetVariable (n j : ℕ) : MvPolynomial (Fin (n + 2)) ℂ :=
  if h : j < n + 1 then MvPolynomial.X (Fin.succ ⟨j, h⟩) else 0

/-- Coordinate images for the Leibniz jet substitution attached to multiplication by `a`. -/
def mulPolynomialJetImage (n : ℕ) (a : Polynomial ℂ) :
    Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ :=
  Fin.cases (MvPolynomial.X 0) fun k =>
    ∑ i ∈ Finset.range ((k : ℕ) + 1),
      MvPolynomial.C (((k : ℕ).choose i : ℕ) : ℂ) *
        Polynomial.aeval (MvPolynomial.X 0) (Polynomial.derivative^[i] a) *
          mulPolynomialJetVariable n ((k : ℕ) - i)

/-- The polynomial substitution induced by the jets of `a * f`. -/
def mulPolynomialJetSubst (n : ℕ) (a : Polynomial ℂ) :
    MvPolynomial (Fin (n + 2)) ℂ →ₐ[ℂ] MvPolynomial (Fin (n + 2)) ℂ :=
  MvPolynomial.bind₁ (mulPolynomialJetImage n a)

@[simp]
theorem eval_mulPolynomialJetVariable_of_lt (n j : ℕ) (hj : j < n + 1)
    (v : Fin (n + 2) → ℂ) :
    MvPolynomial.eval v (mulPolynomialJetVariable n j) = v (Fin.succ ⟨j, hj⟩) := by
  simp [mulPolynomialJetVariable, hj]

/-- Evaluation of the spectral coordinate of the Leibniz substitution. -/
@[simp]
theorem eval_mulPolynomialJetImage_zero (n : ℕ) (a : Polynomial ℂ)
    (v : Fin (n + 2) → ℂ) :
    MvPolynomial.eval v (mulPolynomialJetImage n a 0) = v 0 := by
  simp [mulPolynomialJetImage]

/-- Evaluation of one positive jet coordinate of the Leibniz substitution. -/
theorem eval_mulPolynomialJetImage_succ (n : ℕ) (a : Polynomial ℂ)
    (k : Fin (n + 1)) (v : Fin (n + 2) → ℂ) :
    MvPolynomial.eval v (mulPolynomialJetImage n a k.succ) =
      ∑ i ∈ Finset.range ((k : ℕ) + 1),
        (((k : ℕ).choose i : ℕ) : ℂ) *
          Polynomial.eval (v 0) (Polynomial.derivative^[i] a) *
            v (Fin.succ ⟨(k : ℕ) - i, by omega⟩) := by
  simp only [mulPolynomialJetImage, Fin.cases_succ, map_sum, map_mul,
    MvPolynomial.eval_C, eval_aeval_X]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [eval_mulPolynomialJetVariable_of_lt]

/-- On actual smooth jets, the substitution evaluates to the jets of the polynomial product. -/
theorem bindPointMap_mulPolynomialJetImage (n : ℕ) (a : Polynomial ℂ)
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f) (z : ℂ) :
    bindPointMap (mulPolynomialJetImage n a)
        (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) =
      Fin.cons z (fun j : Fin (n + 1) =>
        iteratedDeriv (j : ℕ) (fun w => Polynomial.eval w a * f w) z) := by
  funext s
  induction s using Fin.cases with
  | zero => simp [bindPointMap]
  | succ k =>
      rw [bindPointMap, eval_mulPolynomialJetImage_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have ha : ContDiffAt ℂ ((k : ℕ) : ℕ∞) (fun w : ℂ => Polynomial.eval w a) z := by
        simpa only [Polynomial.coe_aeval_eq_eval] using!
          (Polynomial.contDiff_aeval a ((k : ℕ) : ℕ∞)).contDiffAt
      have hfz : ContDiffAt ℂ ((k : ℕ) : ℕ∞) f z :=
        hf.contDiffAt.of_le (by
          exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤))
      rw [iteratedDeriv_fun_mul ha hfz]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_range] at hi
      rw [iteratedDeriv_polynomial_eval]

/-- The lower part of the triangular point system for a fixed spectral coordinate. -/
def mulPolynomialJetLower (a : Polynomial ℂ) (z : ℂ)
    (k : ℕ) (u : ℕ → ℂ) : ℂ :=
  ∑ i ∈ Finset.range k,
    ((k.choose (i + 1) : ℕ) : ℂ) *
      Polynomial.eval z (Polynomial.derivative^[i + 1] a) * u (k - (i + 1))

/-- The lower part depends only on strictly lower jet coordinates. -/
theorem mulPolynomialJetLower_congr (a : Polynomial ℂ) (z : ℂ)
    (k : ℕ) (u u' : ℕ → ℂ) (h : ∀ j, j < k → u j = u' j) :
    mulPolynomialJetLower a z k u = mulPolynomialJetLower a z k u' := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [h (k - (i + 1)) (by omega)]

/-- The point map of the Leibniz substitution covers every packet where `a` does not vanish. -/
theorem exists_mulPolynomialJetImage_preimage (n : ℕ) (a : Polynomial ℂ)
    (w : Fin (n + 2) → ℂ) (ha : Polynomial.eval (w 0) a ≠ 0) :
    ∃ v : Fin (n + 2) → ℂ, bindPointMap (mulPolynomialJetImage n a) v = w := by
  let W : ℕ → ℂ := fun k => if h : k < n + 1 then w (Fin.succ ⟨k, h⟩) else 0
  obtain ⟨u, hu⟩ := exists_triangular_solution ha
    (mulPolynomialJetLower a (w 0))
    (mulPolynomialJetLower_congr a (w 0)) W
  let v : Fin (n + 2) → ℂ := Fin.cases (w 0) fun k => u (k : ℕ)
  refine ⟨v, ?_⟩
  funext s
  induction s using Fin.cases with
  | zero => simp [bindPointMap, v]
  | succ k =>
      rw [bindPointMap, eval_mulPolynomialJetImage_succ]
      have hsplit := hu (k : ℕ)
      have hW : W (k : ℕ) = w k.succ := by
        dsimp only [W]
        rw [dif_pos k.isLt]
      rw [hW] at hsplit
      rw [Finset.sum_range_succ']
      simp only [v, Fin.cases_zero, Fin.cases_succ, Nat.choose_zero_right,
        Nat.cast_one, Function.iterate_zero_apply, Nat.sub_zero, one_mul]
      rw [show (∑ i ∈ Finset.range (k : ℕ),
          (((k : ℕ).choose (i + 1) : ℕ) : ℂ) *
            Polynomial.eval (w 0) (Polynomial.derivative^[i + 1] a) *
              u ((k : ℕ) - (i + 1))) =
            mulPolynomialJetLower a (w 0) (k : ℕ) u by rfl,
        add_comm]
      exact hsplit

/-- The embedded multiplier polynomial is nonzero. -/
theorem aeval_X_zero_ne_zero {n : ℕ} {a : Polynomial ℂ} (ha : a ≠ 0) :
    Polynomial.aeval
      (MvPolynomial.X (0 : Fin (n + 2)) : MvPolynomial (Fin (n + 2)) ℂ) a ≠ 0 := by
  intro hzero
  apply ha
  apply Polynomial.funext
  intro z
  have hz := congrArg
    (MvPolynomial.eval (fun _ : Fin (n + 2) => z)) hzero
  simpa [eval_aeval_X] using hz

/-- The Leibniz jet substitution of a nonzero polynomial preserves nonvanishing. -/
theorem mulPolynomialJetSubst_ne_zero {n : ℕ} {a : Polynomial ℂ} (ha : a ≠ 0)
    {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0) :
    mulPolynomialJetSubst n a P ≠ 0 := by
  apply bind₁_ne_zero_of_pointMap_surjective
    (mulPolynomialJetImage n a)
    (Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 2))) a)
    (aeval_X_zero_ne_zero ha)
  · intro w hw
    apply exists_mulPolynomialJetImage_preimage n a w
    simpa [eval_aeval_X] using hw
  · exact hP

/-- A differential relation for a polynomial multiple pulls back to the original smooth function. -/
theorem differentiallyAlgebraic_of_mul_polynomial {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞) f) {a : Polynomial ℂ} (ha : a ≠ 0)
    (h : DifferentiallyAlgebraic fun z => Polynomial.eval z a * f z) :
    DifferentiallyAlgebraic f := by
  obtain ⟨n, P, hP, hrel⟩ := h
  refine ⟨n, mulPolynomialJetSubst n a P,
    mulPolynomialJetSubst_ne_zero ha hP, ?_⟩
  intro z
  rw [mulPolynomialJetSubst, eval_bind₁_eq,
    bindPointMap_mulPolynomialJetImage n a hf z]
  exact hrel z

/-- Multiplying a smooth hypertranscendental function by a nonzero polynomial preserves
hypertranscendence. -/
theorem hypertranscendental_mul_polynomial {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞) f) {a : Polynomial ℂ} (ha : a ≠ 0)
    (hHT : Hypertranscendental f) :
    Hypertranscendental fun z => Polynomial.eval z a * f z := by
  intro hDA
  exact hHT (differentiallyAlgebraic_of_mul_polynomial hf ha hDA)

/-- Infinite complex smoothness supplies differentiability of every iterated derivative. -/
theorem differentiable_iteratedDeriv_of_contDiff_top {f : ℂ → ℂ}
    (hf : ContDiff ℂ (⊤ : ℕ∞) f) (j : ℕ) :
    Differentiable ℂ (iteratedDeriv j f) :=
  (contDiff_iff_iteratedDeriv.mp hf).2 j (ENat.coe_lt_top j)

/-- **Polynomial affine gauges preserve hypertranscendence.**  This simultaneously discharges the
additive and multiplicative interfaces: a nonzero polynomial multiplier followed by an arbitrary
polynomial shift carries every entire-smooth hypertranscendental function to a
hypertranscendental function. -/
theorem hypertranscendental_polynomialGauge {C m : ℂ → ℂ}
    (a b : Polynomial ℂ) (ha : a ≠ 0)
    (hgauge : ∀ z, m z = Polynomial.eval z b + Polynomial.eval z a * C z)
    (hC : ContDiff ℂ (⊤ : ℕ∞) C) (hHT : Hypertranscendental C) :
    Hypertranscendental m := by
  have haSmooth : ContDiff ℂ (⊤ : ℕ∞) (fun z : ℂ => Polynomial.eval z a) := by
    simpa only [Polynomial.coe_aeval_eq_eval] using!
      Polynomial.contDiff_aeval a (⊤ : ℕ∞)
  have hmulSmooth : ContDiff ℂ (⊤ : ℕ∞)
      (fun z => Polynomial.eval z a * C z) := haSmooth.mul hC
  have hmulHT : Hypertranscendental (fun z => Polynomial.eval z a * C z) :=
    hypertranscendental_mul_polynomial hC ha hHT
  have hfun : m = fun z => Polynomial.eval z a * C z + Polynomial.eval z b := by
    funext z
    rw [hgauge z]
    ring
  have hDAiff :
      DifferentiallyAlgebraic
          (fun z => Polynomial.eval z a * C z + Polynomial.eval z b) ↔
        DifferentiallyAlgebraic (fun z => Polynomial.eval z a * C z) := by
    apply differentiallyAlgebraic_add_polynomial_iff
    · exact fun j => differentiable_iteratedDeriv_of_contDiff_top hmulSmooth j
    · intro c j
      have hcSmooth : ContDiff ℂ (⊤ : ℕ∞) (fun z : ℂ => Polynomial.eval z c) := by
        simpa only [Polynomial.coe_aeval_eq_eval] using!
          Polynomial.contDiff_aeval c (⊤ : ℕ∞)
      exact differentiable_iteratedDeriv_of_contDiff_top (hmulSmooth.add hcSmooth) j
  rw [hfun]
  unfold Hypertranscendental at hmulHT ⊢
  exact (not_congr hDAiff).mpr hmulHT

end

end GaloisForLFunctions.HTGeometry
