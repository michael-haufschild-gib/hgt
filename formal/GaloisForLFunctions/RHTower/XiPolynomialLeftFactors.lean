import GaloisForLFunctions.RHTower.XiTiltRayGrowth
import GaloisForLFunctions.HTGeometry.SchottkyHalfPlaneGrowth
import GaloisForLFunctions.RHTower.ArithmeticJointJetExclusion

/-!
# Polynomial left factors and nonzero values of exponentially tilted Xi

Schottky growth and actual Xi ray growth exclude two omitted values on any
right half-plane. Polynomial left factors therefore have a unique root.
The corpus's unconditional simple critical zeros then force degree one.
-/

open Complex Polynomial
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Every nonzero value of tilted Xi occurs arbitrarily far in the right half-plane. -/
theorem exists_xi_tilt_eq_of_nonzero (a R : ℝ) (hR : 1 ≤ R) {w : ℂ} (hw : w ≠ 0) :
    ∃ z : ℂ, R < z.re ∧ xi z * Complex.exp (-(a : ℂ) * z) = w := by
  by_contra hn
  apply xi_tilt_not_exp_ray_bound a R
  apply exists_exp_ray_bound_of_omitting_two_halfPlane R
    (f := fun z => xi z * Complex.exp (-(a : ℂ) * z))
    (a := 0) (b := w)
  · exact (xi_differentiable.mul (by fun_prop)).differentiableOn
  · exact hw.symm
  · intro z hz
    refine ⟨mul_ne_zero (xi_ne_zero_of_one_lt_re (hR.trans_lt hz)) (Complex.exp_ne_zero _), ?_⟩
    intro he
    exact hn ⟨z, hz, he⟩

/-- Any two roots of a polynomial left factor of tilted Xi coincide. -/
theorem xi_polynomial_left_factor_root_unique (a : ℝ) {P : Polynomial ℂ} {h : ℂ → ℂ}
    (hh : Differentiable ℂ h)
    (hrel : ∀ z : ℂ, P.eval (h z) = xi z * Complex.exp (-(a : ℂ) * z))
    {b c : ℂ} (hb : P.eval b = 0) (hc : P.eval c = 0) : b = c := by
  by_contra hbc
  have homit : ∀ z : ℂ, 1 < z.re → h z ≠ b ∧ h z ≠ c := by
    intro z hz
    have hn := mul_ne_zero (xi_ne_zero_of_one_lt_re hz) (Complex.exp_ne_zero (-(a : ℂ) * z))
    constructor
    · intro he
      apply hn
      rw [← hrel z, he, hb]
    · intro he
      apply hn
      rw [← hrel z, he, hc]
  obtain ⟨C, hC, hbound⟩ := exists_exp_ray_bound_polynomial 1 P
    (exists_exp_ray_bound_of_omitting_two_halfPlane 1 hh.differentiableOn hbc homit)
  apply xi_tilt_not_exp_ray_bound a 1
  refine ⟨C, hC, fun t ht => ?_⟩
  simpa only [hrel] using hbound t ht

/-- Tilted Xi has no nonlinear polynomial left factor, unconditionally. -/
theorem xi_polynomial_left_factor_natDegree_eq_one (a : ℝ) {P : Polynomial ℂ} {h : ℂ → ℂ}
    (hh : Differentiable ℂ h)
    (hrel : ∀ z : ℂ, P.eval (h z) = xi z * Complex.exp (-(a : ℂ) * z)) :
    P.natDegree = 1 := by
  classical
  have hP : P ≠ 0 := by
    intro he
    have hz := hrel 1
    rw [he, Polynomial.eval_zero] at hz
    exact (mul_ne_zero (xi_ne_zero_of_ofReal 1) (Complex.exp_ne_zero _)) hz.symm
  have hLC : P.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hP
  obtain ⟨t, _, _, hzero, horder⟩ := DeletionMixedRefinement.exists_high_simple_critical_xi 0
  let ρ := DeletionMixedRefinement.criticalResponsePoint t
  change xi ρ = 0 at hzero
  change (analyticOrderAt xi ρ).toNat = 1 at horder
  have hroot : P.eval (h ρ) = 0 := by rw [hrel, hzero, zero_mul]
  have hroots : P.roots = Multiset.replicate P.roots.card (h ρ) := by
    apply Multiset.eq_replicate_of_mem
    intro b hb
    exact xi_polynomial_left_factor_root_unique a hh hrel ((Polynomial.mem_roots hP).mp hb) hroot
  have hshape : P = Polynomial.C P.leadingCoeff *
      (Polynomial.X - Polynomial.C (h ρ)) ^ P.roots.card := by
    calc
      P = Polynomial.C P.leadingCoeff *
          (P.roots.map (fun b => Polynomial.X - Polynomial.C b)).prod :=
        (IsAlgClosed.splits P).eq_prod_roots
      _ = _ := by rw [hroots]; simp
  have hfun : (fun z : ℂ => P.leadingCoeff * (h z - h ρ) ^ P.roots.card) =
      (fun z : ℂ => xi z * Complex.exp (-(a : ℂ) * z)) := by
    funext z
    have hz := hrel z
    rw [hshape] at hz
    simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_sub, Polynomial.eval_X] using hz
  let k : ℂ → ℂ := fun z => h z - h ρ
  have hk : AnalyticAt ℂ k ρ := (hh.analyticAt ρ).sub analyticAt_const
  have hconst : analyticOrderAt (fun _ : ℂ => P.leadingCoeff) ρ = 0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr hLC)
  have hleft : analyticOrderAt (fun z : ℂ => P.leadingCoeff * (h z - h ρ) ^ P.roots.card) ρ =
      P.roots.card • analyticOrderAt k ρ := by
    change analyticOrderAt ((fun _ : ℂ => P.leadingCoeff) * k ^ P.roots.card) ρ = _
    rw [analyticOrderAt_mul analyticAt_const (hk.pow _), hconst, zero_add, analyticOrderAt_pow hk]
  let e : ℂ → ℂ := fun z => Complex.exp (-(a : ℂ) * z)
  have hediff : Differentiable ℂ e := by dsimp [e]; fun_prop
  have hexp : analyticOrderAt e ρ = 0 := analyticOrderAt_eq_zero.mpr (Or.inr (Complex.exp_ne_zero _))
  have hright : analyticOrderAt (fun z : ℂ => xi z * Complex.exp (-(a : ℂ) * z)) ρ =
      analyticOrderAt xi ρ := by
    change analyticOrderAt (xi * e) ρ = _
    rw [analyticOrderAt_mul (xi_differentiable.analyticAt ρ) (hediff.analyticAt ρ), hexp, add_zero]
  have ho := congrArg (fun f : ℂ → ℂ => (analyticOrderAt f ρ).toNat) hfun
  rw [hleft, hright, horder] at ho
  have hmul : P.roots.card * (analyticOrderAt k ρ).toNat = 1 := by
    simpa only [nsmul_eq_mul, ENat.toNat_mul, ENat.toNat_coe] using ho
  rw [(IsAlgClosed.splits P).natDegree_eq_card_roots]
  exact Nat.eq_one_of_mul_eq_one_left
    ((Nat.mul_comm (analyticOrderAt k ρ).toNat P.roots.card).trans hmul)

end RHTower
