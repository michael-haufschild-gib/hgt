import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicPropagation
import GaloisForLFunctions.HTGeometry.EulerQGammaLanding
import GaloisForLFunctions.HTGeometry.ArgumentScalingInvariance
import GaloisForLFunctions.RHTower.ZetaHypertranscendental

/-!
# Hypertranscendence of the Euler q-Gamma response

On the half plane where the arithmetic Dirichlet series converges, the one-step ladder
`D(v) = ζ(v)·D(v+σ)` exhibits the pulled-back zeta function as the quotient of the response by its
unit translate.  Differential algebraicity of analytic functions on a domain is closed under
quotients by nonvanishing factors and under translation of the argument, so a differential relation
for the response would give one for `ζ(σ(1+s))`; propagating it across the single pole and undoing
the affine substitution contradicts Hilbert's theorem.  Hence the response satisfies no algebraic
differential equation.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial


noncomputable section

/-! ## Restriction and congruence for domain-local relations -/

theorem DifferentiallyAlgebraicOn.mono {f : ℂ → ℂ} {U V : Set ℂ} (hVU : V ⊆ U)
    (hf : DifferentiallyAlgebraicOn f U) : DifferentiallyAlgebraicOn f V := by
  obtain ⟨n, P, hP0, hPv⟩ := hf
  exact ⟨n, P, hP0, fun z hz => hPv z (hVU hz)⟩

theorem iteratedDeriv_eventuallyEq {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[nhds z] g) (k : ℕ) :
    iteratedDeriv k f =ᶠ[nhds z] iteratedDeriv k g := by
  induction k with
  | zero => simpa [iteratedDeriv_zero] using h
  | succ k ih =>
      have hd := ih.deriv
      simpa [iteratedDeriv_succ] using hd

theorem DifferentiallyAlgebraicOn.congr {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (heq : Set.EqOn f g U) (hf : DifferentiallyAlgebraicOn f U) :
    DifferentiallyAlgebraicOn g U := by
  obtain ⟨n, P, hP0, hPv⟩ := hf
  refine ⟨n, P, hP0, fun z hz => ?_⟩
  have hev : f =ᶠ[nhds z] g := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact heq hw
  have hjet : (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) g z) : Fin (n + 2) → ℂ)
      = Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) := by
    funext i
    induction i using Fin.cases with
    | zero => simp
    | succ j =>
        simp only [Fin.cons_succ]
        exact ((iteratedDeriv_eventuallyEq hev (j : ℕ)).eq_of_nhds).symm
  rw [hjet]
  exact hPv z hz

/-! ## The convergence half plane -/

/-- The half plane on which the pulled-back Dirichlet series converges. -/
def eqgHalfPlane (σ : EulerSigma) : Set ℂ := {s : ℂ | 1 / σ.val - 1 < s.re}

theorem mem_eqgHalfPlane (σ : EulerSigma) (s : ℂ) :
    s ∈ eqgHalfPlane σ ↔ 1 < (eqgExponent σ s).re := by
  have hσ : (0 : ℝ) < σ.val := σ.pos
  have hre : (eqgExponent σ s).re = σ.val * (1 + s.re) := by
    simp [eqgExponent, Complex.mul_re]
  simp only [eqgHalfPlane, Set.mem_setOf_eq]
  rw [hre, sub_lt_iff_lt_add', div_lt_iff₀ hσ, mul_comm]

theorem isOpen_eqgHalfPlane (σ : EulerSigma) : IsOpen (eqgHalfPlane σ) :=
  isOpen_lt continuous_const Complex.continuous_re

theorem isPreconnected_eqgHalfPlane (σ : EulerSigma) : IsPreconnected (eqgHalfPlane σ) :=
  (convex_halfSpace_re_gt (1 / σ.val - 1)).isPreconnected

theorem natCast_mem_eqgHalfPlane (σ : EulerSigma) (n : ℕ) : (n : ℂ) ∈ eqgHalfPlane σ := by
  have hσ : (1 : ℝ) < σ.val := σ.one_lt
  have hinv : 1 / σ.val < 1 := by
    rw [div_lt_one (lt_trans one_pos hσ)]
    exact hσ
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hre : ((n : ℂ)).re = (n : ℝ) := by simp
  simp only [eqgHalfPlane, Set.mem_setOf_eq]
  rw [hre]
  linarith

theorem eqgHalfPlane_nonempty (σ : EulerSigma) : (eqgHalfPlane σ).Nonempty :=
  ⟨((0 : ℕ) : ℂ), natCast_mem_eqgHalfPlane σ 0⟩

theorem eqgHalfPlane_infinite (σ : EulerSigma) : (eqgHalfPlane σ).Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ))
    (fun a b hab => Nat.cast_injective hab) ?_
  intro n
  exact natCast_mem_eqgHalfPlane σ n

theorem add_one_mem_eqgHalfPlane (σ : EulerSigma) {s : ℂ} (hs : s ∈ eqgHalfPlane σ) :
    s + 1 ∈ eqgHalfPlane σ := by
  simp only [eqgHalfPlane, Set.mem_setOf_eq] at hs ⊢
  have hre : (s + 1).re = s.re + 1 := by simp
  rw [hre]
  linarith

/-! ## The response as a function of the pulled-back variable -/

/-- The arithmetic Dirichlet response in the pulled-back variable `s ↦ σ(1+s)`. -/
def eqgResponseDirichlet (σ : EulerSigma) (s : ℂ) : ℂ := eqgDirichlet σ (eqgExponent σ s)

theorem analyticAt_eqgExponent (σ : EulerSigma) (s : ℂ) : AnalyticAt ℂ (eqgExponent σ) s := by
  have hfun : eqgExponent σ = fun z : ℂ => (σ.val : ℂ) * (1 + z) := rfl
  rw [hfun]
  exact analyticAt_const.mul (analyticAt_const.add analyticAt_id)

theorem analyticAt_eqgResponseDirichlet (σ : EulerSigma) {s : ℂ} (hs : s ∈ eqgHalfPlane σ) :
    AnalyticAt ℂ (eqgResponseDirichlet σ) s :=
  AnalyticAt.comp (g := eqgDirichlet σ) (f := eqgExponent σ)
    (analyticAt_eqgDirichlet σ ((mem_eqgHalfPlane σ s).mp hs)) (analyticAt_eqgExponent σ s)

theorem eqgResponseDirichlet_ne_zero (σ : EulerSigma) {s : ℂ} (hs : s ∈ eqgHalfPlane σ) :
    eqgResponseDirichlet σ s ≠ 0 :=
  eqgDirichlet_ne_zero σ ((mem_eqgHalfPlane σ s).mp hs)

/-- **The one-step ladder in the pulled-back variable.** -/
theorem eqgResponseDirichlet_ladder (σ : EulerSigma) {s : ℂ} (hs : s ∈ eqgHalfPlane σ) :
    eqgResponseDirichlet σ s
      = riemannZeta (eqgExponent σ s) * eqgResponseDirichlet σ (s + 1) := by
  have hw : 1 < (eqgExponent σ s).re := (mem_eqgHalfPlane σ s).mp hs
  have h := eqgDirichlet_ladder_step σ hw 1
  rw [eqgResponseDirichlet, eqgResponseDirichlet, h]
  have harg : eqgExponent σ s + ((1 : ℕ) : ℂ) * (σ.val : ℂ) = eqgExponent σ (s + 1) := by
    rw [eqgExponent, eqgExponent]
    push_cast
    ring
  rw [harg]
  congr 1
  rw [Finset.prod_range_one]
  norm_num

/-! ## The pulled-back zeta factor -/

/-- The zeta function in the pulled-back variable. -/
def eqgZetaPullback (σ : EulerSigma) (s : ℂ) : ℂ := riemannZeta (eqgExponent σ s)

/-- The unique preimage of the pole of `ζ`. -/
def eqgPolePoint (σ : EulerSigma) : ℂ := 1 / (σ.val : ℂ) - 1

theorem eqgExponent_ne_one (σ : EulerSigma) {s : ℂ} (hs : s ≠ eqgPolePoint σ) :
    eqgExponent σ s ≠ 1 := by
  intro h
  apply hs
  have hσ : ((σ.val : ℂ)) ≠ 0 := sigma_ne_zero σ
  rw [eqgExponent] at h
  rw [eqgPolePoint]
  field_simp at h ⊢
  linear_combination h

theorem analyticOnNhd_eqgZetaPullback (σ : EulerSigma) :
    AnalyticOnNhd ℂ (eqgZetaPullback σ) ({eqgPolePoint σ}ᶜ : Set ℂ) := by
  intro s hs
  have hne : eqgExponent σ s ≠ 1 := eqgExponent_ne_one σ (by simpa using hs)
  have h := AnalyticAt.comp (g := riemannZeta) (f := eqgExponent σ) (x := s)
    (analyticOn_riemannZeta _ hne) (analyticAt_eqgExponent σ s)
  have hgoal : eqgZetaPullback σ = fun x : ℂ => riemannZeta (eqgExponent σ x) := rfl
  rw [hgoal]
  simpa [Function.comp_def] using h

theorem eqgHalfPlane_subset_compl (σ : EulerSigma) :
    eqgHalfPlane σ ⊆ ({eqgPolePoint σ}ᶜ : Set ℂ) := by
  intro s hs h1
  rw [Set.mem_singleton_iff] at h1
  have hre : 1 < (eqgExponent σ s).re := (mem_eqgHalfPlane σ s).mp hs
  have hσ : ((σ.val : ℂ)) ≠ 0 := sigma_ne_zero σ
  have hval : eqgExponent σ s = 1 := by
    rw [h1, eqgExponent, eqgPolePoint]
    field_simp
    ring
  rw [hval] at hre
  simp at hre

/-- **The pulled-back zeta function is hypertranscendental**, by scaling and translation
invariance of differential algebraicity and Hilbert's theorem for `ζ`. -/
theorem hypertranscendental_eqgZetaPullback (σ : EulerSigma) :
    Hypertranscendental (eqgZetaPullback σ) := by
  intro hDA
  have hc : ((σ.val : ℂ)) ≠ 0 := sigma_ne_zero σ
  have hfun : (fun z : ℂ => (fun w : ℂ => riemannZeta (w + (σ.val : ℂ))) ((σ.val : ℂ) * z))
      = eqgZetaPullback σ := by
    funext z
    show riemannZeta ((σ.val : ℂ) * z + (σ.val : ℂ)) = riemannZeta (eqgExponent σ z)
    congr 1
    rw [eqgExponent]
    ring
  have hDA' : DifferentiallyAlgebraic
      (fun z : ℂ => (fun w : ℂ => riemannZeta (w + (σ.val : ℂ))) ((σ.val : ℂ) * z)) := by
    rw [hfun]
    exact hDA
  have h1 : DifferentiallyAlgebraic (fun w : ℂ => riemannZeta (w + (σ.val : ℂ))) :=
    (differentiallyAlgebraic_comp_const_mul_iff_uncond
      (f := fun w : ℂ => riemannZeta (w + (σ.val : ℂ))) (c := (σ.val : ℂ)) hc).mp hDA'
  have h2 : DifferentiallyAlgebraic riemannZeta :=
    (differentiallyAlgebraic_comp_add_const_iff (f := riemannZeta) ((σ.val : ℂ))).mp h1
  exact hypertranscendental_riemannZeta h2

/-! ## Theorem 7.1 -/

/-- **The Euler q-Gamma response is hypertranscendental.**  A differential relation for the
response on its convergence half plane would, through the one-step ladder
`D(v) = ζ(v)·D(v+σ)`, produce one for the pulled-back zeta function; propagating it across the
single pole and undoing the affine substitution contradicts Hilbert's theorem. -/
theorem not_differentiallyAlgebraicOn_eqgResponseDirichlet (σ : EulerSigma) :
    ¬ DifferentiallyAlgebraicOn (eqgResponseDirichlet σ) (eqgHalfPlane σ) := by
  intro hDA
  have hWo := isOpen_eqgHalfPlane σ
  have hWc := isPreconnected_eqgHalfPlane σ
  have hWne := eqgHalfPlane_nonempty σ
  have hWinf := eqgHalfPlane_infinite σ
  have hAan : AnalyticOnNhd ℂ (eqgResponseDirichlet σ) (eqgHalfPlane σ) :=
    fun s hs => analyticAt_eqgResponseDirichlet σ hs
  have hBan : AnalyticOnNhd ℂ (fun s => eqgResponseDirichlet σ (s + 1)) (eqgHalfPlane σ) := by
    intro s hs
    have h := analyticAt_eqgResponseDirichlet σ (add_one_mem_eqgHalfPlane σ hs)
    have hshift : AnalyticAt ℂ (fun z : ℂ => z + 1) s := analyticAt_id.add analyticAt_const
    simpa [Function.comp_def] using
      AnalyticAt.comp (g := eqgResponseDirichlet σ) (f := fun z : ℂ => z + 1) h hshift
  have hBne : ∀ s ∈ eqgHalfPlane σ, eqgResponseDirichlet σ (s + 1) ≠ 0 := fun s hs =>
    eqgResponseDirichlet_ne_zero σ (add_one_mem_eqgHalfPlane σ hs)
  have hBDA : DifferentiallyAlgebraicOn (fun s => eqgResponseDirichlet σ (s + 1))
      (eqgHalfPlane σ) :=
    DifferentiallyAlgebraicOn.mono (fun s hs => add_one_mem_eqgHalfPlane σ hs)
      (DifferentiallyAlgebraicOn.comp_add_const hDA 1)
  have hquot := differentiallyAlgebraicOn_div hWo hWc hWne hWinf hAan hBan hBne hDA hBDA
  have hzeta : DifferentiallyAlgebraicOn (eqgZetaPullback σ) (eqgHalfPlane σ) := by
    refine DifferentiallyAlgebraicOn.congr hWo ?_ hquot
    intro s hs
    have hlad := eqgResponseDirichlet_ladder σ hs
    rw [eqgZetaPullback]
    rw [div_eq_iff (hBne s hs)]
    exact hlad
  have hglobal := differentiallyAlgebraic_of_on_compl_singleton
    (analyticOnNhd_eqgZetaPullback σ) hWo hWne (eqgHalfPlane_subset_compl σ) hzeta
  exact hypertranscendental_eqgZetaPullback σ hglobal

/-! ## The full response -/

theorem differentiallyAlgebraicOn_of_differentiallyAlgebraic {f : ℂ → ℂ} {U : Set ℂ}
    (h : DifferentiallyAlgebraic f) : DifferentiallyAlgebraicOn f U := by
  obtain ⟨n, P, hP0, hPz⟩ := h
  exact ⟨n, P, hP0, fun z _ => hPz z⟩

/-- The scalar prefactor `ζ(σ)^s·C` of the response. -/
def eqgUnitFactor (σ : EulerSigma) (s : ℂ) : ℂ :=
  ((eqgConst σ : ℝ) : ℂ) * riemannZeta (σ.val : ℂ) ^ s

theorem eqgConst_complex_ne_zero (σ : EulerSigma) : ((eqgConst σ : ℝ) : ℂ) ≠ 0 := by
  simp only [ne_eq, Complex.ofReal_eq_zero]
  exact (eqgConst_pos σ).ne'

theorem eqgResponse_eq_unitFactor_mul (σ : EulerSigma) (s : ℂ) :
    eqgResponse σ s = eqgUnitFactor σ s * eqgResponseDirichlet σ s := by
  rw [eqgResponse, eqgUnitFactor, eqgResponseDirichlet]
  ring

theorem differentiallyAlgebraic_eqgUnitFactor (σ : EulerSigma) :
    DifferentiallyAlgebraic (eqgUnitFactor σ) := by
  have hexp : (eqgUnitFactor σ)
      = fun s : ℂ => ((eqgConst σ : ℝ) : ℂ)
          * Complex.exp (Complex.log (riemannZeta (σ.val : ℂ)) * s) := by
    funext s
    rw [eqgUnitFactor, Complex.cpow_def_of_ne_zero (zeta_sigma_ne_zero σ)]
  rw [hexp]
  exact (differentiallyAlgebraic_cexp_linear _).const_mul (eqgConst_complex_ne_zero σ)

theorem analyticAt_eqgUnitFactor (σ : EulerSigma) (s : ℂ) :
    AnalyticAt ℂ (eqgUnitFactor σ) s :=
  analyticAt_const.mul (analyticAt_zeta_sigma_cpow σ s)

theorem eqgUnitFactor_ne_zero (σ : EulerSigma) (s : ℂ) : eqgUnitFactor σ s ≠ 0 :=
  mul_ne_zero (eqgConst_complex_ne_zero σ) (zeta_sigma_cpow_ne_zero σ s)

theorem analyticAt_eqgResponse (σ : EulerSigma) {s : ℂ} (hs : s ∈ eqgHalfPlane σ) :
    AnalyticAt ℂ (eqgResponse σ) s := by
  have hfun : eqgResponse σ = fun z : ℂ => eqgUnitFactor σ z * eqgResponseDirichlet σ z := by
    funext z
    exact eqgResponse_eq_unitFactor_mul σ z
  rw [hfun]
  exact (analyticAt_eqgUnitFactor σ s).mul (analyticAt_eqgResponseDirichlet σ hs)

/-- **Theorem 7.1.**  The Euler q-Gamma response satisfies no algebraic differential equation on
its convergence half plane. -/
theorem not_differentiallyAlgebraicOn_eqgResponse (σ : EulerSigma) :
    ¬ DifferentiallyAlgebraicOn (eqgResponse σ) (eqgHalfPlane σ) := by
  intro hDA
  refine not_differentiallyAlgebraicOn_eqgResponseDirichlet σ ?_
  have hquot := differentiallyAlgebraicOn_div (isOpen_eqgHalfPlane σ)
    (isPreconnected_eqgHalfPlane σ) (eqgHalfPlane_nonempty σ) (eqgHalfPlane_infinite σ)
    (fun s hs => analyticAt_eqgResponse σ hs) (fun s _ => analyticAt_eqgUnitFactor σ s)
    (fun s _ => eqgUnitFactor_ne_zero σ s) hDA
    (differentiallyAlgebraicOn_of_differentiallyAlgebraic
      (differentiallyAlgebraic_eqgUnitFactor σ))
  refine DifferentiallyAlgebraicOn.congr (isOpen_eqgHalfPlane σ) ?_ hquot
  intro s _
  show eqgResponse σ s / eqgUnitFactor σ s = eqgResponseDirichlet σ s
  rw [eqgResponse_eq_unitFactor_mul]
  exact mul_div_cancel_left₀ _ (eqgUnitFactor_ne_zero σ s)

/-- **Theorem 7.1, cut form.**  Every cut of the analytic continuation is hypertranscendental on
the convergence half plane, since all cuts agree with the response there. -/
theorem not_differentiallyAlgebraicOn_eqgCont (σ : EulerSigma) (K : ℕ) :
    ¬ DifferentiallyAlgebraicOn (eqgCont σ K) (eqgHalfPlane σ) := by
  intro hDA
  refine not_differentiallyAlgebraicOn_eqgResponse σ ?_
  refine DifferentiallyAlgebraicOn.congr (isOpen_eqgHalfPlane σ) ?_ hDA
  intro s hs
  exact eqgCont_eq_response σ K ((mem_eqgHalfPlane σ s).mp hs)

end

end GaloisForLFunctions.HTGeometry
