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

/-- **Theorem 7.1, ladder form.**  The pulled-back socle ladder satisfies no algebraic differential
equation on the convergence half plane. -/
theorem not_differentiallyAlgebraicOn_soclePullback (σ : EulerSigma) :
    ¬ DifferentiallyAlgebraicOn (soclePullback σ) (eqgHalfPlane σ) := by
  intro hDA
  have hWo := isOpen_eqgHalfPlane σ
  have hWc := isPreconnected_eqgHalfPlane σ
  have hWne := eqgHalfPlane_nonempty σ
  have hWinf := eqgHalfPlane_infinite σ
  have hAan : AnalyticOnNhd ℂ (soclePullback σ) (eqgHalfPlane σ) :=
    fun s hs => analyticAt_soclePullback σ hs
  have hBan : AnalyticOnNhd ℂ (fun s => soclePullback σ (s + 1)) (eqgHalfPlane σ) := by
    intro s hs
    have h := analyticAt_soclePullback σ (add_one_mem_eqgHalfPlane σ hs)
    have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1) s := analyticAt_id.add analyticAt_const
    simpa [Function.comp_def] using
      AnalyticAt.comp (g := soclePullback σ) (f := fun z : ℂ => z + 1) h hshift
  have hBne : ∀ s ∈ eqgHalfPlane σ, soclePullback σ (s + 1) ≠ 0 := fun s hs =>
    soclePullback_ne_zero σ (add_one_mem_eqgHalfPlane σ hs)
  have hBDA : DifferentiallyAlgebraicOn (fun s => soclePullback σ (s + 1)) (eqgHalfPlane σ) :=
    DifferentiallyAlgebraicOn.mono (fun s hs => add_one_mem_eqgHalfPlane σ hs)
      (DifferentiallyAlgebraicOn.comp_add_const hDA 1)
  have hquot := differentiallyAlgebraicOn_div hWo hWc hWne hWinf hAan hBan hBne hDA hBDA
  have hzeta : DifferentiallyAlgebraicOn (eqgZetaPullback σ) (eqgHalfPlane σ) := by
    refine DifferentiallyAlgebraicOn.congr hWo ?_ hquot
    intro s hs
    rw [eqgZetaPullback, div_eq_iff (hBne s hs)]
    exact soclePullback_ladder σ s
  have hglobal := differentiallyAlgebraic_of_on_compl_singleton
    (analyticOnNhd_eqgZetaPullback σ) hWo hWne (eqgHalfPlane_subset_compl σ) hzeta
  exact hypertranscendental_eqgZetaPullback σ hglobal

end

end GaloisForLFunctions.HTGeometry.AbelianZetaGas
