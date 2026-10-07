import GaloisForLFunctions.HTGeometry.AlgebraicRamifiedBranch
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.MonicScaling
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Meromorphic ramified roots without a monicity assumption

The exact identity `M(t,a(t)Y)=a(t)^(d-1)P(t,Y)` scales a polynomial
to a monic one. Over the parameter's fraction field this is an invertible
linear change of variable and multiplication by a unit, so irreducibility
is preserved. A convergent ramified root of `M` then gives a meromorphic
root of `P` by division by `a`.

This classical normalization dependency uses polynomial identities and the
qualitative identity principle. It makes no new scientific or RH claim.
-/

namespace GaloisForLFunctions.HTGeometry.AlgebraicMonicScaling

open Polynomial
open AlgebraicFiniteJetBranch HilbertIrreducibility
open scoped Topology

noncomputable section


theorem evalAt_eq_bivEval (P : BiPoly) (s w : ℂ) :
    evalAt P s w = bivEval P s w := by
  simp [evalAt, specialize, bivEval, Polynomial.eval_map,
    Polynomial.coe_aeval_eq_evalRingHom]

theorem ext_evalAt {P Q : BiPoly} (h : ∀ s w : ℂ, evalAt P s w = evalAt Q s w) :
    P = Q := by
  apply Polynomial.ext
  intro i
  apply Polynomial.funext
  intro s
  have hs : specialize P s = specialize Q s := Polynomial.funext (h s)
  simpa [specialize] using congrArg (fun R : Polynomial ℂ => R.coeff i) hs

theorem evalAt_comp (P Q : BiPoly) (s w : ℂ) :
    evalAt (P.comp Q) s w = evalAt P s (evalAt Q s w) := by
  simp [evalAt, specialize, Polynomial.map_comp, Polynomial.eval_comp]

/-- The pointwise scaling identity is an identity of bivariate polynomials. -/
theorem monicScale_comp (P : BiPoly) (hd : 0 < P.natDegree) :
    (monicScale P P.natDegree).comp (C P.leadingCoeff * X) =
      C (P.leadingCoeff ^ (P.natDegree - 1)) * P := by
  apply ext_evalAt
  intro s w
  have he : evalAt (C P.leadingCoeff * X) s w = P.leadingCoeff.eval s * w := by
    simp [evalAt, specialize]
  rw [evalAt_comp, he, evalAt_C_mul]
  simpa only [evalAt_eq_bivEval, Polynomial.eval_pow, ← Polynomial.coe_aeval_eq_eval] using
    (bivEval_monicScale (f := P) rfl hd s w)

/-- Generic irreducibility is preserved by monic scaling. -/
theorem irreducible_monicScale {K : Type*} [Field K] [Algebra (Polynomial ℂ) K]
    [IsFractionRing (Polynomial ℂ) K] (P : BiPoly) (hd : 0 < P.natDegree)
    (hirr : Irreducible (P.map (algebraMap (Polynomial ℂ) K))) :
    Irreducible (monicScale P P.natDegree) := by
  let ι : Polynomial ℂ →+* K := algebraMap (Polynomial ℂ) K
  let a := ι P.leadingCoeff
  have hP0 : P ≠ 0 := by
    intro hP
    apply hirr.ne_zero
    simp [hP]
  have ha : a ≠ 0 := by
    intro heq
    have hlead : P.leadingCoeff = 0 := (IsFractionRing.injective (Polynomial ℂ) K)
      (heq.trans (map_zero ι).symm)
    exact hP0 (Polynomial.leadingCoeff_eq_zero.mp hlead)
  letI : Invertible a := invertibleOfNonzero ha
  let e := Polynomial.algEquivCMulXAddC a 0
  let M := monicScale P P.natDegree
  have hcomp : (M.map ι).comp (C a * X) = C (a ^ (P.natDegree - 1)) * P.map ι := by
    simpa [M, a, Polynomial.map_comp] using
      congrArg (Polynomial.map ι) (monicScale_comp P hd)
  have hu : IsUnit (C (a ^ (P.natDegree - 1)) : Polynomial K) :=
    (isUnit_iff_ne_zero.mpr (pow_ne_zero _ ha)).map Polynomial.C
  have hi : Irreducible (C (a ^ (P.natDegree - 1)) * P.map ι) :=
    (irreducible_isUnit_mul hu).mpr hirr
  have he : Irreducible (e (M.map ι)) := by
    simpa only [e, Polynomial.algEquivCMulXAddC_apply, map_zero, add_zero,
      ← Polynomial.comp_eq_aeval, hcomp] using hi
  have hm : Irreducible (M.map ι) := (MulEquiv.irreducible_iff e).mp he
  exact ((monic_monicScale P P.natDegree).isPrimitive.irreducible_iff_irreducible_map_fraction_map
    (K := K)).mpr hm

theorem polynomial_eventually_ne_zero {p : Polynomial ℂ} (hp : p ≠ 0) :
    ∀ᶠ s in 𝓝[≠] (0 : ℂ), p.eval s ≠ 0 := by
  by_contra h
  have hf : ∃ᶠ s in 𝓝[≠] (0 : ℂ), p.eval s = 0 := by simpa using h
  have hz := (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) p).eqOn_zero_of_preconnected_of_frequently_eq_zero
      isPreconnected_univ (Set.mem_univ 0) hf
  apply hp
  apply Polynomial.funext
  intro s
  simpa using hz (Set.mem_univ s)

/-- An irreducible polynomial over the parameter field has a ramified meromorphic root. -/
theorem exists_ramified_meromorphic_root {K : Type*} [Field K] [Algebra (Polynomial ℂ) K]
    [IsFractionRing (Polynomial ℂ) K] (P : BiPoly) (hd : 0 < P.natDegree)
    (hirr : Irreducible (P.map (algebraMap (Polynomial ℂ) K))) :
    ∃ (N : ℕ) (f : ℂ → ℂ), 0 < N ∧ MeromorphicAt f 0 ∧
      ∀ᶠ s in 𝓝[≠] (0 : ℂ), evalAt P (s ^ N) (f s) = 0 := by
  let M := monicScale P P.natDegree
  obtain ⟨N, h, hN, hh, hroot⟩ :=
    AlgebraicRamifiedBranch.exists_ramified_analytic_root_of_irreducible M
      (monic_monicScale P P.natDegree) (irreducible_monicScale P hd hirr)
  let a := P.leadingCoeff
  have ha : a ≠ 0 := by
    intro heq
    have hP : P = 0 := Polynomial.leadingCoeff_eq_zero.mp heq
    apply hirr.ne_zero
    simp [hP]
  let b := Polynomial.expand ℂ N a
  have hb : b ≠ 0 := by
    intro heq
    apply ha
    exact Polynomial.expand_injective hN (heq.trans (map_zero (Polynomial.expand ℂ N)).symm)
  have hbeval (s : ℂ) : b.eval s = a.eval (s ^ N) := by
    simp [b, Polynomial.expand_eq_comp_X_pow, Polynomial.eval_comp]
  have hbana : AnalyticAt ℂ (fun s => a.eval (s ^ N)) 0 := by
    simpa only [← hbeval] using
      (AnalyticOnNhd.eval_polynomial (𝕜 := ℂ) b 0 (Set.mem_univ _))
  refine ⟨N, fun s => h s / a.eval (s ^ N), hN, hh.meromorphicAt.div hbana.meromorphicAt, ?_⟩
  have hbne : ∀ᶠ s in 𝓝[≠] (0 : ℂ), a.eval (s ^ N) ≠ 0 := by
    simpa only [hbeval] using polynomial_eventually_ne_zero hb
  filter_upwards [hroot.filter_mono nhdsWithin_le_nhds, hbne] with s hs hbs
  have he := bivEval_monicScale (f := P) rfl hd (s ^ N) (h s / a.eval (s ^ N))
  have he' : evalAt M (s ^ N) (h s) =
      a.eval (s ^ N) ^ (P.natDegree - 1) *
        evalAt P (s ^ N) (h s / a.eval (s ^ N)) := by
    simpa only [M, a, ← evalAt_eq_bivEval, Polynomial.coe_aeval_eq_eval,
      mul_div_cancel₀ _ hbs] using he
  rw [hs] at he'
  exact (mul_eq_zero.mp he'.symm).resolve_left (pow_ne_zero _ hbs)

end

end GaloisForLFunctions.HTGeometry.AlgebraicMonicScaling
