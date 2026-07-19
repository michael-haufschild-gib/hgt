import GaloisForLFunctions.HTGeometry.MulPolynomialInvariance
import GaloisForLFunctions.HTGeometry.DigammaGammaLocalHypertranscendence

/-!
# Polynomial gauges on a domain

The polynomial gauge theorems are stated for entire functions, but the objects they are meant for
are not entire: a Cauchy transform is analytic only off the real axis.  So the gauge is redone
pointwise.

Nothing algebraic changes — the jet substitution and its point map are the same, and nonvanishing
is untouched, being a statement about polynomials alone.  Only the jet identities move from global
smoothness to smoothness at the point, which is all they ever used.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The Leibniz jet identity at a single point of smoothness. -/
theorem iteratedDeriv_mul_polynomial_at {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℂ (⊤ : ℕ∞) f z) (a : Polynomial ℂ) (k : ℕ) :
    iteratedDeriv k (fun w => Polynomial.eval w a * f w) z
      = ∑ i ∈ Finset.range (k + 1),
          ((k.choose i : ℕ) : ℂ) * Polynomial.eval z (Polynomial.derivative^[i] a)
            * iteratedDeriv (k - i) f z := by
  have ha : ContDiffAt ℂ ((k : ℕ) : ℕ∞) (fun w : ℂ => Polynomial.eval w a) z := by
    simpa only [Polynomial.coe_aeval_eq_eval] using
      (Polynomial.contDiff_aeval a ((k : ℕ) : ℕ∞)).contDiffAt
  have hfz : ContDiffAt ℂ ((k : ℕ) : ℕ∞) f z :=
    hf.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤))
  rw [iteratedDeriv_fun_mul ha hfz]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedDeriv_polynomial_eval]

/-- The point map carries the jets of `f` to the jets of `a * f` at a point of smoothness. -/
theorem bindPointMap_mulPolynomialJetImage_at (n : ℕ) (a : Polynomial ℂ)
    {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℂ (⊤ : ℕ∞) f z) :
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
      rw [iteratedDeriv_mul_polynomial_at hf a]

/-- **Multiplying by a nonzero polynomial preserves differential algebraicity on a domain.** -/
theorem differentiallyAlgebraicOn_of_mul_polynomial {f : ℂ → ℂ} {U : Set ℂ}
    (hf : ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) f z) {a : Polynomial ℂ} (ha : a ≠ 0)
    (h : DifferentiallyAlgebraicOn (fun z => Polynomial.eval z a * f z) U) :
    DifferentiallyAlgebraicOn f U := by
  obtain ⟨n, P, hP, hrel⟩ := h
  refine ⟨n, mulPolynomialJetSubst n a P, mulPolynomialJetSubst_ne_zero ha hP, ?_⟩
  intro z hz
  rw [mulPolynomialJetSubst, eval_bind₁_eq,
    bindPointMap_mulPolynomialJetImage_at n a (hf z hz)]
  exact hrel z hz

/-- The additive jet identity at a single point of smoothness. -/
theorem iteratedDeriv_add_polynomial_at {f : ℂ → ℂ} {z : ℂ}
    (hf : ContDiffAt ℂ (⊤ : ℕ∞) f z) (b : Polynomial ℂ) (k : ℕ) :
    iteratedDeriv k (fun w => f w + Polynomial.eval w b) z
      = iteratedDeriv k f z + Polynomial.eval z (Polynomial.derivative^[k] b) := by
  have hb : ContDiffAt ℂ ((k : ℕ) : ℕ∞) (fun w : ℂ => Polynomial.eval w b) z := by
    simpa only [Polynomial.coe_aeval_eq_eval] using
      (Polynomial.contDiff_aeval b ((k : ℕ) : ℕ∞)).contDiffAt
  have hfz : ContDiffAt ℂ ((k : ℕ) : ℕ∞) f z :=
    hf.of_le (by exact_mod_cast (le_top : ((k : ℕ) : ℕ∞) ≤ ⊤))
  have hsum : (fun w => f w + Polynomial.eval w b) = f + fun w => Polynomial.eval w b := rfl
  rw [hsum, iteratedDeriv_add hfz hb, iteratedDeriv_polynomial_eval]

/-- **Adding a polynomial preserves differential algebraicity on a domain.** -/
theorem differentiallyAlgebraicOn_add_polynomial {f : ℂ → ℂ} {U : Set ℂ}
    (hf : ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) f z) (b : Polynomial ℂ)
    (h : DifferentiallyAlgebraicOn (fun w => f w + Polynomial.eval w b) U) :
    DifferentiallyAlgebraicOn f U := by
  classical
  obtain ⟨n, P, hP, hzero⟩ := h
  refine ⟨n, axisShiftSubst 0 (fun s : Fin (n + 2) => Polynomial.derivative^[s.1 - 1] b) P,
    axisShiftSubst_ne_zero 0 _ hP, ?_⟩
  intro z hz
  rw [eval_axisShiftSubst]
  have hjet : (fun s : Fin (n + 2) =>
      if s = 0 then (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) :
          Fin (n + 2) → ℂ) 0
        else (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) :
          Fin (n + 2) → ℂ) s
          + Polynomial.aeval
              ((Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) :
                Fin (n + 2) → ℂ) 0)
              (Polynomial.derivative^[s.1 - 1] b))
      = Fin.cons z (fun j : Fin (n + 1) =>
          iteratedDeriv (j : ℕ) (fun w => f w + Polynomial.eval w b) z) := by
    funext s
    rcases Fin.eq_zero_or_eq_succ s with hs | ⟨s', hs⟩
    · subst hs
      simp
    · subst hs
      rw [if_neg (Fin.succ_ne_zero s')]
      simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_succ, Nat.add_sub_cancel]
      rw [iteratedDeriv_add_polynomial_at (hf z hz) b]
      simp
  rw [hjet]
  exact hzero z hz

/-- **The polynomial affine gauge on a domain.**  A nonzero polynomial multiplier followed by a
polynomial shift carries a function with no differential relation on `U` to a function with none. -/
theorem not_differentiallyAlgebraicOn_polynomialGauge {C m : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (a b : Polynomial ℂ) (ha : a ≠ 0)
    (hgauge : ∀ z ∈ U, m z = Polynomial.eval z b + Polynomial.eval z a * C z)
    (hC : ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) C z)
    (hHT : ¬ DifferentiallyAlgebraicOn C U) :
    ¬ DifferentiallyAlgebraicOn m U := by
  intro hm
  refine hHT ?_
  have hmulSmooth : ∀ z ∈ U, ContDiffAt ℂ (⊤ : ℕ∞) (fun w => Polynomial.eval w a * C w) z := by
    intro z hz
    have haz : ContDiffAt ℂ (⊤ : ℕ∞) (fun w : ℂ => Polynomial.eval w a) z := by
      simpa only [Polynomial.coe_aeval_eq_eval] using
        (Polynomial.contDiff_aeval a (⊤ : ℕ∞)).contDiffAt
    exact haz.mul (hC z hz)
  have hEq : ∀ z ∈ U,
      m =ᶠ[nhds z] fun w => Polynomial.eval w a * C w + Polynomial.eval w b := by
    intro z hz
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [hgauge w hw]
    ring
  have hshift : DifferentiallyAlgebraicOn
      (fun w => Polynomial.eval w a * C w + Polynomial.eval w b) U := by
    obtain ⟨n, P, hP, hrel⟩ := hm
    refine ⟨n, P, hP, fun z hz => ?_⟩
    have hjet : ((Fin.cons z fun j : Fin (n + 1) =>
          iteratedDeriv (j : ℕ)
            (fun w => Polynomial.eval w a * C w + Polynomial.eval w b) z) :
            Fin (n + 2) → ℂ)
        = ((Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) m z) :
            Fin (n + 2) → ℂ) := by
      funext s
      rcases Fin.eq_zero_or_eq_succ s with hs | ⟨s', hs⟩
      · subst hs
        simp
      · subst hs
        simp only [Fin.cons_succ]
        exact ((hEq z hz).iteratedDeriv_eq _).symm
    rw [hjet]
    exact hrel z hz
  exact differentiallyAlgebraicOn_of_mul_polynomial hC ha
    (differentiallyAlgebraicOn_add_polynomial hmulSmooth b hshift)

end

end GaloisForLFunctions.HTGeometry
