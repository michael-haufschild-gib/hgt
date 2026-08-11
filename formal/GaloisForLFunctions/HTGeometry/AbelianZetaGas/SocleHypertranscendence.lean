import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleResponse
import GaloisForLFunctions.HTGeometry.EulerQGammaHypertranscendence

/-!
# Hypertranscendence of the socle response

The socle ladder satisfies the one-step relation `Z(σ, σs) = ζ(σ(1+s))·Z(σ, σ(s+1))`.  On the
half-plane where every depth argument has real part above one the ladder is holomorphic and
zero-free, so the pulled-back zeta function is the quotient of the ladder by its unit translate.
Differential algebraicity on a domain is closed under such quotients and under translation, so a
differential relation for the ladder would give one for `ζ(σ(1+s))`; propagating it across the
single pole and undoing the affine substitution contradicts Hilbert's theorem.

The normalizer of the socle response is a nonzero constant, so the response is hypertranscendental
for the same reason.
-/

namespace GaloisForLFunctions.HTGeometry.AbelianZetaGas

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The socle ladder pulled back along the temperature scaling. -/
def soclePullback (σ : EulerSigma) (s : ℂ) : ℂ := socleLadder σ.val ((σ.val : ℂ) * s)

theorem mul_mem_socleChamber (σ : EulerSigma) {s : ℂ} (hs : s ∈ eqgHalfPlane σ) :
    (σ.val : ℂ) * s ∈ socleChamber σ.val := by
  have hσ : (0 : ℝ) < σ.val := σ.pos
  have hre : 1 < (eqgExponent σ s).re := (mem_eqgHalfPlane σ s).mp hs
  have hval : (eqgExponent σ s).re = σ.val * (1 + s.re) := by
    simp [eqgExponent, Complex.mul_re]
  have hprod : ((σ.val : ℂ) * s).re = σ.val * s.re := by
    simp [Complex.mul_re]
  show 1 - σ.val < ((σ.val : ℂ) * s).re
  rw [hval] at hre
  rw [hprod]
  nlinarith

theorem analyticAt_soclePullback (σ : EulerSigma) {s : ℂ} (hs : s ∈ eqgHalfPlane σ) :
    AnalyticAt ℂ (soclePullback σ) s := by
  have hσ : (0 : ℝ) < σ.val := σ.pos
  have hlad : AnalyticOnNhd ℂ (socleLadder σ.val) (socleChamber σ.val) :=
    (differentiableOn_socleLadder hσ).analyticOnNhd (isOpen_socleChamber σ.val)
  have hmul : AnalyticAt ℂ (fun z : ℂ => (σ.val : ℂ) * z) s := analyticAt_const.mul analyticAt_id
  have h := AnalyticAt.comp (g := socleLadder σ.val) (f := fun z : ℂ => (σ.val : ℂ) * z) (x := s)
    (hlad _ (mul_mem_socleChamber σ hs)) hmul
  simp only [Function.comp_def] at h
  exact h

theorem soclePullback_ne_zero (σ : EulerSigma) {s : ℂ} (hs : s ∈ eqgHalfPlane σ) :
    soclePullback σ s ≠ 0 :=
  socleLadder_ne_zero_of_mem σ.pos (mul_mem_socleChamber σ hs)

/-- **The pullback ladder.**  The socle ladder pulled back along the temperature scaling satisfies
the one-step zeta relation of the Euler `q`-Gamma response. -/
theorem soclePullback_ladder (σ : EulerSigma) (s : ℂ) :
    soclePullback σ s = riemannZeta (eqgExponent σ s) * soclePullback σ (s + 1) := by
  have h := socleLadder_peel σ.pos ((σ.val : ℂ) * s)
  rw [soclePullback, soclePullback, h]
  congr 1
  · congr 1
    rw [eqgExponent]
    ring
  · congr 1
    ring

/-- **The ladder obstruction.**  Any function that is analytic and zero-free on the convergence
half plane and satisfies the one-step zeta ladder there satisfies no algebraic differential
equation on it. -/
theorem not_differentiallyAlgebraicOn_of_zetaLadder (σ : EulerSigma) {A : ℂ → ℂ}
    (hAan : ∀ s ∈ eqgHalfPlane σ, AnalyticAt ℂ A s)
    (hAne : ∀ s ∈ eqgHalfPlane σ, A s ≠ 0)
    (hlad : ∀ s ∈ eqgHalfPlane σ, A s = riemannZeta (eqgExponent σ s) * A (s + 1)) :
    ¬ DifferentiallyAlgebraicOn A (eqgHalfPlane σ) := by
  intro hDA
  have hWo := isOpen_eqgHalfPlane σ
  have hWc := isPreconnected_eqgHalfPlane σ
  have hWne := eqgHalfPlane_nonempty σ
  have hWinf := eqgHalfPlane_infinite σ
  have hAan' : AnalyticOnNhd ℂ A (eqgHalfPlane σ) := fun s hs => hAan s hs
  have hBan : AnalyticOnNhd ℂ (fun s => A (s + 1)) (eqgHalfPlane σ) := by
    intro s hs
    have h := hAan _ (add_one_mem_eqgHalfPlane σ hs)
    have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1) s := analyticAt_id.add analyticAt_const
    simpa [Function.comp_def] using
      AnalyticAt.comp (g := A) (f := fun z : ℂ => z + 1) h hshift
  have hBne : ∀ s ∈ eqgHalfPlane σ, A (s + 1) ≠ 0 := fun s hs =>
    hAne _ (add_one_mem_eqgHalfPlane σ hs)
  have hBDA : DifferentiallyAlgebraicOn (fun s => A (s + 1)) (eqgHalfPlane σ) :=
    DifferentiallyAlgebraicOn.mono (fun s hs => add_one_mem_eqgHalfPlane σ hs)
      (DifferentiallyAlgebraicOn.comp_add_const hDA 1)
  have hquot := differentiallyAlgebraicOn_div hWo hWc hWne hWinf hAan' hBan hBne hDA hBDA
  have hzeta : DifferentiallyAlgebraicOn (eqgZetaPullback σ) (eqgHalfPlane σ) := by
    refine DifferentiallyAlgebraicOn.congr hWo ?_ hquot
    intro s hs
    rw [eqgZetaPullback, div_eq_iff (hBne s hs)]
    exact hlad s hs
  have hglobal := differentiallyAlgebraic_of_on_compl_singleton
    (analyticOnNhd_eqgZetaPullback σ) hWo hWne (eqgHalfPlane_subset_compl σ) hzeta
  exact hypertranscendental_eqgZetaPullback σ hglobal

/-- **Theorem 7.1, ladder form.**  The pulled-back socle ladder satisfies no algebraic differential
equation on the convergence half plane. -/
theorem not_differentiallyAlgebraicOn_soclePullback (σ : EulerSigma) :
    ¬ DifferentiallyAlgebraicOn (soclePullback σ) (eqgHalfPlane σ) :=
  not_differentiallyAlgebraicOn_of_zetaLadder σ (fun _ hs => analyticAt_soclePullback σ hs)
    (fun _ hs => soclePullback_ne_zero σ hs) (fun s _ => soclePullback_ladder σ s)

/-! ## Argument scaling on a domain -/

open MvPolynomial in
/-- **Argument scaling preserves differential algebraicity on a domain.**  The domain-local mirror
of `DifferentiallyAlgebraic.comp_const_mul_uncond`. -/
theorem differentiallyAlgebraicOn_comp_const_mul {f : ℂ → ℂ} {U : Set ℂ}
    (hf : DifferentiallyAlgebraicOn f U) {c : ℂ} (hc : c ≠ 0) :
    DifferentiallyAlgebraicOn (fun z => f (c * z)) {z : ℂ | c * z ∈ U} := by
  obtain ⟨n, P, hP0, hPz⟩ := hf
  refine ⟨n, bind₁ (jetArgScaleSub n c) P, ?_, ?_⟩
  · intro h
    apply hP0
    have hback : bind₁ (jetArgScaleSub n c⁻¹) (bind₁ (jetArgScaleSub n c) P) = P := by
      rw [bind₁_bind₁]
      have hσ : (fun i => bind₁ (jetArgScaleSub n c⁻¹) (jetArgScaleSub n c i))
          = (X : Fin (n + 2) → MvPolynomial (Fin (n + 2)) ℂ) := by
        funext i
        induction i using Fin.cases with
        | zero =>
          simp only [jetArgScaleSub, Fin.cases_zero, map_mul, bind₁_X_right, bind₁_C_right]
          rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul]
        | succ j =>
          simp only [jetArgScaleSub, Fin.cases_succ, map_mul, bind₁_X_right, bind₁_C_right]
          rw [← mul_assoc, ← map_mul, inv_inv, ← mul_pow, inv_mul_cancel₀ hc, one_pow, map_one,
            one_mul]
      rw [hσ, bind₁_X_left]
      rfl
    rw [← hback, h, map_zero]
  · intro z hz
    rw [eval_bind₁]
    have hvec : (fun i => eval
          (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) (fun w => f (c * w)) z)
          (jetArgScaleSub n c i))
        = Fin.cons (c * z) (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f (c * z)) := by
      funext i
      induction i using Fin.cases with
      | zero =>
        simp only [jetArgScaleSub, Fin.cases_zero, eval_mul, eval_C, eval_X, Fin.cons_zero]
      | succ j =>
        simp only [jetArgScaleSub, Fin.cases_succ, eval_mul, eval_C, eval_X, Fin.cons_succ]
        rw [iteratedDeriv_comp_mul_left_uncond f c (j : ℕ) z, ← mul_assoc, ← mul_pow,
          inv_mul_cancel₀ hc, one_pow, one_mul]
    rw [hvec]
    exact hPz (c * z) hz


/-! ## Theorem 7.1 for the response -/

/-- **Theorem 7.1.**  The socle response `C_{σ,τ}` satisfies no algebraic differential equation on
the chamber where the ladder converges.  It is a nonzero constant multiple of an affine
substitution of the ladder, so the ladder obstruction applies verbatim. -/
theorem not_differentiallyAlgebraicOn_socleResponse (σ : EulerSigma) (τ : ℝ)
    (hK : socleLadder σ.val ((τ : ℝ) : ℂ) ≠ 0) :
    ¬ DifferentiallyAlgebraicOn (socleResponse σ.val τ)
      {z : ℂ | ((τ : ℝ) : ℂ) + z ∈ socleChamber σ.val} := by
  intro hDA
  have hσC : ((σ.val : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr σ.pos.ne'
  have hAval : ∀ s : ℂ,
      socleResponse σ.val τ (((σ.val : ℝ) : ℂ) * s + -((τ : ℝ) : ℂ))
        = soclePullback σ s / socleLadder σ.val ((τ : ℝ) : ℂ) := by
    intro s
    rw [socleResponse, soclePullback]
    congr 2
    ring
  have hladA : ∀ s ∈ eqgHalfPlane σ,
      soclePullback σ s / socleLadder σ.val ((τ : ℝ) : ℂ)
        = riemannZeta (eqgExponent σ s)
          * (soclePullback σ (s + 1) / socleLadder σ.val ((τ : ℝ) : ℂ)) := by
    intro s _
    rw [soclePullback_ladder σ s]
    ring
  refine not_differentiallyAlgebraicOn_of_zetaLadder σ
    (A := fun s => soclePullback σ s / socleLadder σ.val ((τ : ℝ) : ℂ))
    (fun s hs => (analyticAt_soclePullback σ hs).div analyticAt_const hK)
    (fun s hs => div_ne_zero (soclePullback_ne_zero σ hs) hK) hladA ?_
  have h1 := DifferentiallyAlgebraicOn.comp_add_const hDA (-((τ : ℝ) : ℂ))
  have h2 := differentiallyAlgebraicOn_comp_const_mul h1 hσC
  have hsub : eqgHalfPlane σ ⊆
      {s : ℂ | ((σ.val : ℝ) : ℂ) * s ∈
        {w : ℂ | w + -((τ : ℝ) : ℂ) ∈ {z : ℂ | ((τ : ℝ) : ℂ) + z ∈ socleChamber σ.val}}} := by
    intro s hs
    show ((τ : ℝ) : ℂ) + (((σ.val : ℝ) : ℂ) * s + -((τ : ℝ) : ℂ)) ∈ socleChamber σ.val
    have hval : ((τ : ℝ) : ℂ) + (((σ.val : ℝ) : ℂ) * s + -((τ : ℝ) : ℂ))
        = ((σ.val : ℝ) : ℂ) * s := by ring
    rw [hval]
    exact mul_mem_socleChamber σ hs
  refine DifferentiallyAlgebraicOn.congr (isOpen_eqgHalfPlane σ) ?_
    (DifferentiallyAlgebraicOn.mono hsub h2)
  intro s _
  exact hAval s


end

end GaloisForLFunctions.HTGeometry.AbelianZetaGas
