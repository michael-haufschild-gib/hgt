import GaloisForLFunctions.HTGeometry.PrimeTupleFormationFrame
import GaloisForLFunctions.HTGeometry.PrimePairGreenProperness
import GaloisForLFunctions.HTGeometry.FormationGradeChannels

/-!
# Grade-three alternant, causal Green exactification and seven-phase formation

For grades `a, b, c > 0` with `A = a + b + c` the three-schedule alternant has transform
`abc Δ (2z + A)/(z D_3(z))` with `Δ = (a-b)(a-c)(b-c)` and
`D_3 = (z+a)(z+b)(z+c)(z+a+b)(z+a+c)(z+b+c)(z+A)` `(PGE.7)`.  Its infinite-horizon value is
`Δ/((a+b)(a+c)(b+c))` `(PGE.9)`, so the grade-two recipe `(A/Δ) F` has limit
`A/((a+b)(a+c)(b+c))`, which decays like `R⁻²` under the common scaling of the grades.  With
`Q_3 = (a+b)(a+c)(b+c)A` the conservation law reads `Q_3 F = Δ (2∂_t + A) H` `(PGE.15)`, where
`H` is the distribution function of the seven subset phases `(PGE.13)`; the causal Green operator
`𝒞_A g(t) = ½ ∫₀ᵗ e^{-A(t-s)/2} g(s) ds` is the unique causal inverse of `2∂_t + A`
`(PGE.16)`, so `H = Q_3 𝒞_A Δ⁻¹ F` `(PGE.17)`.  For grades at least `log 2` the law dominates the
Erlang-seven law `(PGE.18)`–`(PGE.19)`, which gives the all-prime triple frame `(PGE.22)`.  The
ambient Vandermonde inverse `Δ⁻¹` is unbounded over prime triples.
-/

open MeasureTheory Set Filter Topology Equiv
open MvPolynomial (aeval)

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

open Permutohedral

/-! ### Derivatives of hypoexponential distribution functions -/

theorem hasDerivAt_expKernelConv (r : ℝ) {F : ℝ → ℝ} (hF : Continuous F) (t : ℝ) :
    HasDerivAt (expKernelConv r F) (r * (F t - expKernelConv r F t)) t := by
  have hc : Continuous fun s => r * Real.exp (r * s) * F s := by fun_prop
  have hI := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have he : HasDerivAt (fun t => Real.exp (-(r * t))) (Real.exp (-(r * t)) * (-r)) t := by
    have := ((hasDerivAt_id t).const_mul r).neg.exp
    simpa using this
  rw [show expKernelConv r F = fun t =>
    Real.exp (-(r * t)) * ∫ s in (0 : ℝ)..t, r * Real.exp (r * s) * F s from
      funext (expKernelConv_eq r F)]
  refine (he.mul hI).congr_deriv ?_
  rw [mul_sub, ← mul_assoc (Real.exp _), mul_comm (Real.exp (-(r * t))) (r * _), mul_assoc r,
    ← Real.exp_add, show r * t + -(r * t) = 0 by ring, Real.exp_zero]
  ring

/-- The derivative of a hypoexponential distribution function. -/
def hypoCDFDeriv : List ℝ → ℝ → ℝ
  | [] => fun _ => 0
  | ρ :: ρs => fun t => ρ * (hypoCDFList ρs t - hypoCDFList (ρ :: ρs) t)

theorem hasDerivAt_hypoCDFList (ρs : List ℝ) (t : ℝ) :
    HasDerivAt (hypoCDFList ρs) (hypoCDFDeriv ρs t) t := by
  cases ρs with
  | nil => exact hasDerivAt_const t 1
  | cons ρ ρs => exact hasDerivAt_expKernelConv ρ (continuous_hypoCDFList ρs) t

theorem continuous_hypoCDFDeriv (ρs : List ℝ) : Continuous (hypoCDFDeriv ρs) := by
  cases ρs with
  | nil => exact continuous_const
  | cons ρ ρs =>
    exact continuous_const.mul ((continuous_hypoCDFList ρs).sub (continuous_hypoCDFList _))

/-- The hypoexponential distribution function depends continuously on the rates. -/
theorem continuous_hypoCDFList_param {α X : Type*} [TopologicalSpace X] (f : α → X → ℝ)
    (hf : ∀ a, Continuous (f a)) :
    ∀ L : List α, Continuous fun p : X × ℝ => hypoCDFList (L.map fun a => f a p.1) p.2
  | [] => continuous_const
  | a :: L => by
    have ih := continuous_hypoCDFList_param f hf L
    simp only [List.map_cons, hypoCDFList, expKernelConv]
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (f := fun (p : X × ℝ) (s : ℝ) => f a p.1 * Real.exp (-(f a p.1 * (p.2 - s))) *
        hypoCDFList (L.map fun a => f a p.1) s) ?_ continuous_snd
    have h1 : Continuous fun q : (X × ℝ) × ℝ => f a q.1.1 := (hf a).comp
      (continuous_fst.comp continuous_fst)
    have h2 : Continuous fun q : (X × ℝ) × ℝ =>
        hypoCDFList (L.map fun a => f a q.1.1) q.2 :=
      ih.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)
    exact (h1.mul (Real.continuous_exp.comp (h1.mul ((continuous_snd.comp continuous_fst).sub
      continuous_snd)).neg)).mul h2

/-- `H_r(t)` depends continuously on the grades, through repeated grades. -/
theorem continuous_subsetCDF_grades {r : ℕ} (t : ℝ) :
    Continuous fun lam : Fin r → ℝ => subsetCDF lam t := by
  have h := continuous_hypoCDFList_param (fun (S : Finset (Fin r)) (lam : Fin r → ℝ) =>
    ∑ i ∈ S, lam i) (fun S => continuous_finsetSum _ fun i _ => continuous_apply i)
    (subsets r).toList
  exact h.comp (continuous_id.prodMk continuous_const)

/-! ### The causal Green operator of `2∂_t + A` -/

/-- The causal Green operator `𝒞_A g(t) = ½ ∫₀ᵗ e^{-A(t-s)/2} g(s) ds` `(PGE.16)`. -/
def causalGreen (A : ℝ) (g : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 / 2 * ∫ s in (0 : ℝ)..t, Real.exp (-(A * (t - s) / 2)) * g s

theorem causalGreen_eq (A : ℝ) (g : ℝ → ℝ) (t : ℝ) :
    causalGreen A g t =
      Real.exp (-(A * t / 2)) * ∫ s in (0 : ℝ)..t, 1 / 2 * Real.exp (A * s / 2) * g s := by
  rw [causalGreen, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  show 1 / 2 * (Real.exp (-(A * (t - s) / 2)) * g s) =
    Real.exp (-(A * t / 2)) * (1 / 2 * Real.exp (A * s / 2) * g s)
  rw [show -(A * (t - s) / 2) = -(A * t / 2) + A * s / 2 by ring, Real.exp_add]
  ring

theorem causalGreen_zero (A : ℝ) (g : ℝ → ℝ) : causalGreen A g 0 = 0 := by
  simp [causalGreen]

/-- `𝒞_A g` solves `2(𝒞_A g)' + A 𝒞_A g = g`. -/
theorem hasDerivAt_causalGreen (A : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (t : ℝ) :
    HasDerivAt (causalGreen A g) ((g t - A * causalGreen A g t) / 2) t := by
  have hc : Continuous fun s => 1 / 2 * Real.exp (A * s / 2) * g s := by fun_prop
  have hI := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  have hin : HasDerivAt (fun x : ℝ => -(A * x / 2)) (-(A / 2)) t := by
    have h := (hasDerivAt_id' t).const_mul (-(A / 2))
    rw [mul_one] at h
    have hf : (fun x : ℝ => -(A * x / 2)) = fun x => -(A / 2) * x := by funext x; ring
    rw [hf]
    exact h
  have he : HasDerivAt (fun t => Real.exp (-(A * t / 2)))
      (Real.exp (-(A * t / 2)) * (-(A / 2))) t :=
    hin.exp
  rw [show causalGreen A g = fun t => Real.exp (-(A * t / 2)) *
    ∫ s in (0 : ℝ)..t, 1 / 2 * Real.exp (A * s / 2) * g s from funext (causalGreen_eq A g)]
  refine (he.mul hI).congr_deriv ?_
  have h1 : Real.exp (-(A * t / 2)) * Real.exp (A * t / 2) = 1 := by
    rw [← Real.exp_add]; simp
  linear_combination (1 / 2 * g t) * h1

/-- **`𝒞_A` is the causal inverse of `2∂_t + A`**: for `u` with continuous derivative and
`u(0) = 0`, `𝒞_A(2u' + Au) = u`. -/
theorem causalGreen_inverse (A : ℝ) {u u' : ℝ → ℝ} (hu : ∀ s, HasDerivAt u (u' s) s)
    (hu' : Continuous u') (h0 : u 0 = 0) (t : ℝ) :
    causalGreen A (fun s => 2 * u' s + A * u s) t = u t := by
  have hcu : Continuous u := continuous_iff_continuousAt.2 fun s => (hu s).continuousAt
  have hd : ∀ s, HasDerivAt (fun s => Real.exp (A * s / 2) * u s)
      (1 / 2 * Real.exp (A * s / 2) * (2 * u' s + A * u s)) s := fun s => by
    have he : HasDerivAt (fun s => Real.exp (A * s / 2)) (Real.exp (A * s / 2) * (A / 2)) s :=
      ((((hasDerivAt_id' s).const_mul A).div_const 2).exp).congr_deriv (by ring)
    refine (he.mul (hu s)).congr_deriv ?_
    ring
  rw [causalGreen_eq, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (Continuous.intervalIntegrable (by fun_prop) _ _), h0, mul_zero, sub_zero, ← mul_assoc,
    ← Real.exp_add, show -(A * t / 2) + A * t / 2 = 0 by ring, Real.exp_zero, one_mul]

/-- Uniqueness: a causal solution of `2v' + Av = g`, `v(0) = 0`, is `𝒞_A g`. -/
theorem eq_causalGreen_of_solves (A : ℝ) {v v' g : ℝ → ℝ} (hv : ∀ s, HasDerivAt v (v' s) s)
    (hv' : Continuous v') (h0 : v 0 = 0) (hsolve : ∀ s, 2 * v' s + A * v s = g s) (t : ℝ) :
    v t = causalGreen A g t := by
  rw [← causalGreen_inverse A hv hv' h0 t]
  simp_rw [hsolve]

/-! ### Grade three -/

section GradeThree

variable {lam : Fin 3 → ℝ}

/-- `Q_3 = (a+b)(a+c)(b+c)A` is the subset-incidence product at grade three `(PGE.10)`. -/
theorem subsetIncidence_three (lam : Fin 3 → ℝ) :
    subsetIncidence lam = (lam 0 + lam 1) * (lam 0 + lam 2) * (lam 1 + lam 2) *
      (lam 0 + lam 1 + lam 2) := by
  rw [subsetIncidence, show (subsets 3).filter (fun S => 2 ≤ S.card) =
    {{0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide),
    Finset.prod_singleton, Finset.sum_pair (by decide), Finset.sum_pair (by decide),
    Finset.sum_pair (by decide), Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  ring

theorem delta_three (lam : Fin 3 → ℝ) :
    delta lam = (lam 0 - lam 1) * (lam 0 - lam 2) * (lam 1 - lam 2) := by
  rw [delta, Fin.prod_univ_three, show Finset.Ioi (0 : Fin 3) = {1, 2} by decide,
    show Finset.Ioi (1 : Fin 3) = {2} by decide, show Finset.Ioi (2 : Fin 3) = ∅ by decide,
    Finset.prod_pair (by decide), Finset.prod_singleton, Finset.prod_empty, mul_one]

theorem aeval_denom_three {K : Type*} [Field K] [Algebra ℚ K] (z : K) (l : Fin 3 → K) :
    aeval (point z l) (denom 3) = (z + l 0) * (z + l 1) * (z + l 2) * (z + (l 0 + l 1)) *
      (z + (l 0 + l 2)) * (z + (l 1 + l 2)) * (z + (l 0 + (l 1 + l 2))) := by
  rw [aeval_denom, subsets_three, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton,
    Finset.sum_singleton, Finset.sum_singleton, Finset.sum_singleton,
    Finset.sum_pair (by decide), Finset.sum_pair (by decide), Finset.sum_pair (by decide),
    Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
  ring

theorem aeval_formNumer_three {K : Type*} [Field K] [Algebra ℚ K] (z : K) (l : Fin 3 → K) :
    aeval (point z l) (formNumer 3) = 2 * z + (l 0 + l 1 + l 2) := by
  rw [formNumer_three]
  simp [point]

/-- **Theorem 3.1, `(PGE.7)`**: `𝓛F_{a,b,c}(z) = abc Δ (2z + A)/(z D_3(z))`. -/
theorem laplace_scheduleAlternant_three (hlam : ∀ i, 0 < lam i) {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Ioi (0 : ℝ), (scheduleAlternant lam t : ℂ) * Complex.exp (-(z * t)) =
      (lam 0 * lam 1 * lam 2 : ℝ) * (((lam 0 - lam 1) * (lam 0 - lam 2) * (lam 1 - lam 2) : ℝ) *
        (2 * z + (lam 0 + lam 1 + lam 2 : ℝ))) /
      (z * ((z + lam 0) * (z + lam 1) * (z + lam 2) * (z + (lam 0 + lam 1 : ℝ)) *
        (z + (lam 0 + lam 2 : ℝ)) * (z + (lam 1 + lam 2 : ℝ)) *
        (z + (lam 0 + lam 1 + lam 2 : ℝ)))) := by
  have hl : lamC lam = ![((lam 0 : ℝ) : ℂ), (lam 1 : ℂ), (lam 2 : ℂ)] := by
    funext i; fin_cases i <;> rfl
  rw [laplace_scheduleAlternant hlam hz, hl, aeval_formNumer_three, aeval_denom_three,
    Fin.prod_univ_three]
  have hd : delta ![((lam 0 : ℝ) : ℂ), (lam 1 : ℂ), (lam 2 : ℂ)] =
      (((lam 0 - lam 1) * (lam 0 - lam 2) * (lam 1 - lam 2) : ℝ) : ℂ) := by
    rw [delta, Fin.prod_univ_three,
      show Finset.Ioi (0 : Fin 3) = {1, 2} by decide, show Finset.Ioi (1 : Fin 3) = {2} by decide,
      show Finset.Ioi (2 : Fin 3) = ∅ by decide, Finset.prod_pair (by decide),
      Finset.prod_singleton, Finset.prod_empty, mul_one]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    push_cast
    ring
  rw [hd]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  push_cast
  ring

/-- The infinite-horizon value of a schedule coefficient: `B_π(t) → (Π_k S_k)⁻¹`. -/
theorem tendsto_scheduleCoeff {r : ℕ} {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i)
    (π : Perm (Fin r)) :
    Tendsto (scheduleCoeff lam π) atTop (𝓝 (∏ k, suffixSum lam π k)⁻¹) := by
  have h := (tendsto_hypoCDFList_atTop (suffixRates_pos hlam π)).const_mul
    (∏ k, suffixSum lam π k)⁻¹
  rw [mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  exact (scheduleCoeff_eq hlam π ht).symm

/-- The infinite-horizon value of the alternant: `F_r(t) → (Π λ_i) R_r(0;λ)`. -/
theorem tendsto_scheduleAlternant {r : ℕ} {lam : Fin r → ℝ} (hlam : ∀ i, 0 < lam i) :
    Tendsto (scheduleAlternant lam) atTop (𝓝 ((∏ i, lam i) * alternant 0 lam)) := by
  have hF : scheduleAlternant lam = fun t =>
      (∏ i, lam i) * ∑ π : Perm (Fin r), (Perm.sign π : ℤ) • scheduleCoeff lam π t :=
    funext fun t => rfl
  rw [hF, alternant]
  simp_rw [zero_add]
  refine Tendsto.const_mul _ (tendsto_finsetSum _ fun π _ => ?_)
  rw [Finset.prod_inv_distrib]
  exact (tendsto_scheduleCoeff hlam π).const_smul _

/-- **`(PGE.9)`**: `F_{a,b,c}(t) → Δ/((a+b)(a+c)(b+c))`. -/
theorem tendsto_scheduleAlternant_three (hlam : ∀ i, 0 < lam i) :
    Tendsto (scheduleAlternant lam) atTop
      (𝓝 ((lam 0 - lam 1) * (lam 0 - lam 2) * (lam 1 - lam 2) /
        ((lam 0 + lam 1) * (lam 0 + lam 2) * (lam 1 + lam 2)))) := by
  have hph : ∀ S ∈ subsets 3, (0 : ℝ) + ∑ i ∈ S, lam i ≠ 0 := fun S hS => by
    rw [zero_add]
    exact (Finset.sum_pos (fun i _ => hlam i) (Finset.mem_filter.1 hS).2).ne'
  have h := tendsto_scheduleAlternant hlam
  rw [alternant_eq 0 lam hph, aeval_formNumer_three, aeval_denom_three, delta_three,
    Fin.prod_univ_three] at h
  convert h using 2
  have h0 := hlam 0; have h1 := hlam 1; have h2 := hlam 2
  field_simp
  ring

/-- The grade-two exactifier at grade three: `(A/Δ) F → A/((a+b)(a+c)(b+c))` `(PGE.9)`. -/
theorem tendsto_totalGradeCorrection (hlam : ∀ i, 0 < lam i)
    (hΔ : (lam 0 - lam 1) * (lam 0 - lam 2) * (lam 1 - lam 2) ≠ 0) :
    Tendsto (fun t => (lam 0 + lam 1 + lam 2) /
        ((lam 0 - lam 1) * (lam 0 - lam 2) * (lam 1 - lam 2)) * scheduleAlternant lam t) atTop
      (𝓝 ((lam 0 + lam 1 + lam 2) / ((lam 0 + lam 1) * (lam 0 + lam 2) * (lam 1 + lam 2)))) := by
  have h := (tendsto_scheduleAlternant_three hlam).const_mul ((lam 0 + lam 1 + lam 2) /
    ((lam 0 - lam 1) * (lam 0 - lam 2) * (lam 1 - lam 2)))
  convert h using 2
  have h0 := hlam 0; have h1 := hlam 1; have h2 := hlam 2
  field_simp
  exact (div_self hΔ).symm

/-- The limit of the total-grade correction scales like `R⁻²` and tends to `0` `(PGE.9)`. -/
theorem totalGradeLimit_scale (lam : Fin 3 → ℝ) {R : ℝ} (hR : R ≠ 0) :
    (R * lam 0 + R * lam 1 + R * lam 2) /
        ((R * lam 0 + R * lam 1) * (R * lam 0 + R * lam 2) * (R * lam 1 + R * lam 2)) =
      R⁻¹ ^ 2 * ((lam 0 + lam 1 + lam 2) /
        ((lam 0 + lam 1) * (lam 0 + lam 2) * (lam 1 + lam 2))) := by
  by_cases h : (lam 0 + lam 1) * (lam 0 + lam 2) * (lam 1 + lam 2) = 0
  · have h' : (R * lam 0 + R * lam 1) * (R * lam 0 + R * lam 2) * (R * lam 1 + R * lam 2) = 0 := by
      rw [show (R * lam 0 + R * lam 1) * (R * lam 0 + R * lam 2) * (R * lam 1 + R * lam 2) =
        R ^ 3 * ((lam 0 + lam 1) * (lam 0 + lam 2) * (lam 1 + lam 2)) by ring, h, mul_zero]
    rw [h, h', div_zero, div_zero, mul_zero]
  · field_simp

theorem tendsto_totalGradeLimit_scale (lam : Fin 3 → ℝ) :
    Tendsto (fun R : ℝ => (R * lam 0 + R * lam 1 + R * lam 2) /
        ((R * lam 0 + R * lam 1) * (R * lam 0 + R * lam 2) * (R * lam 1 + R * lam 2))) atTop
      (𝓝 0) := by
  have h : Tendsto (fun R : ℝ => R⁻¹ ^ 2 * ((lam 0 + lam 1 + lam 2) /
      ((lam 0 + lam 1) * (lam 0 + lam 2) * (lam 1 + lam 2)))) atTop (𝓝 0) := by
    have := ((tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 2).mul_const ((lam 0 + lam 1 + lam 2) /
      ((lam 0 + lam 1) * (lam 0 + lam 2) * (lam 1 + lam 2)))
    simpa using this
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with R hR
  exact (totalGradeLimit_scale lam hR.ne').symm

/-- The time polynomial `P_3(z) = 2z + A`. -/
theorem formPoly_three (lam : Fin 3 → ℝ) :
    formPoly lam = Polynomial.C 2 * Polynomial.X + Polynomial.C (lam 0 + lam 1 + lam 2) := by
  rw [formPoly, formNumer_three]
  simp only [map_add, map_mul, MvPolynomial.aeval_X, Option.elim_none, Option.elim_some]
  rw [show (aeval fun o : Option (Fin 3) => o.elim Polynomial.X fun i => Polynomial.C (lam i))
    (2 : MvPolynomial (Option (Fin 3)) ℚ) = Polynomial.C 2 by
      rw [show (2 : MvPolynomial (Option (Fin 3)) ℚ) = MvPolynomial.C 2 by rfl,
        MvPolynomial.aeval_C]
      rfl]

theorem natDegree_formPoly_three (lam : Fin 3 → ℝ) : (formPoly lam).natDegree = 1 := by
  rw [formPoly_three]
  exact Polynomial.natDegree_linear two_ne_zero

/-- **`(PGE.15)`**: `Q_3 F(t) = Δ (2H'(t) + A H(t))` on `[0, ∞)`. -/
theorem conservation_three (hlam : ∀ i, 0 < lam i) {t : ℝ} (ht : 0 ≤ t) :
    subsetIncidence lam * scheduleAlternant lam t =
      delta lam * (2 * deriv (subsetCDF lam) t + (lam 0 + lam 1 + lam 2) * subsetCDF lam t) := by
  rw [subsetPhase_conservation hlam ht, natDegree_formPoly_three, Finset.sum_range_succ,
    Finset.sum_range_one, iteratedDeriv_zero, iteratedDeriv_one, formPoly_three]
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_zero,
    Polynomial.coeff_X_one, Polynomial.coeff_C_zero, Polynomial.coeff_C_succ]
  ring

theorem subsetRates_three_ne_nil (lam : Fin 3 → ℝ) : subsetRates lam ≠ [] := by
  intro h
  have := length_subsetRates lam
  rw [h] at this
  norm_num at this

/-- **`(PGE.17)`: causal Green exactification** `H = Q_3 𝒞_A Δ⁻¹ F` on `[0, ∞)` for distinct
grades. -/
theorem subsetCDF_eq_causalGreen (hlam : ∀ i, 0 < lam i) (hΔ : delta lam ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) :
    subsetCDF lam t = subsetIncidence lam *
      causalGreen (lam 0 + lam 1 + lam 2) (fun s => (delta lam)⁻¹ * scheduleAlternant lam s) t := by
  obtain ⟨ρ, ρs, hρ⟩ := List.exists_cons_of_ne_nil (subsetRates_three_ne_nil lam)
  have hH : subsetCDF lam = hypoCDFList (ρ :: ρs) := by rw [subsetCDF, hρ]
  have hd : ∀ s, HasDerivAt (subsetCDF lam) (hypoCDFDeriv (ρ :: ρs) s) s := fun s => by
    rw [hH]; exact hasDerivAt_hypoCDFList _ s
  have h0 : subsetCDF lam 0 = 0 := by rw [hH]; exact expKernelConv_zero _ _
  rw [← causalGreen_inverse (lam 0 + lam 1 + lam 2) hd (continuous_hypoCDFDeriv _) h0 t,
    causalGreen, causalGreen]
  have hint : ∫ s in (0 : ℝ)..t, Real.exp (-((lam 0 + lam 1 + lam 2) * (t - s) / 2)) *
      (2 * hypoCDFDeriv (ρ :: ρs) s + (lam 0 + lam 1 + lam 2) * subsetCDF lam s) =
      ∫ s in (0 : ℝ)..t, subsetIncidence lam *
        (Real.exp (-((lam 0 + lam 1 + lam 2) * (t - s) / 2)) *
          ((delta lam)⁻¹ * scheduleAlternant lam s)) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    have hc := conservation_three hlam hs.1
    rw [(hd s).deriv] at hc
    have : 2 * hypoCDFDeriv (ρ :: ρs) s + (lam 0 + lam 1 + lam 2) * subsetCDF lam s =
        subsetIncidence lam * scheduleAlternant lam s / delta lam := by
      rw [hc]; field_simp
    show Real.exp _ * (2 * hypoCDFDeriv (ρ :: ρs) s + _ * subsetCDF lam s) = _
    rw [this]
    ring
  rw [hint, intervalIntegral.integral_const_mul]
  ring

/-- **`(PGE.19)`**: for grades at least `log 2`, `H ≥ G_7`. -/
theorem erlangSeven_le_subsetCDF (hlam : ∀ i, Real.log 2 ≤ lam i) {t : ℝ} (ht : 0 ≤ t) :
    erlangCDF 7 (Real.log 2) t ≤ subsetCDF lam t := by
  have hl := Real.log_pos one_lt_two
  have h := erlangCDF_le_subsetCDF hl (fun i => hl.trans_le (hlam i)) hlam ht
  simpa using h

/-- **`(PGE.20)`**: `c_{T,7}² = ∫₀ᵀ G_7² > 0`. -/
theorem erlangFloor_seven_pos {T : ℝ} (hT : 0 < T) : 0 < erlangFloor 7 T := erlangFloor_pos 7 hT

/-- **Theorem 6.2, `(PGE.22)`: the global grade-three frame.** -/
theorem tripleFrame {T : ℝ} (hT : 0 ≤ T) (d : HistoryFamily.Controls (PrimeTuple 3)) :
    erlangFloor 7 T * ‖d‖ ^ 2 ≤ ‖(formationFamily 3).response T d‖ ^ 2 ∧
      ‖(formationFamily 3).response T d‖ ^ 2 ≤ T * ‖d‖ ^ 2 := by
  simpa using formation_frame (r := 3) hT d

end GradeThree

/-! ### The ambient Vandermonde inverse is unbounded over prime triples -/

/-- **Hostile correction 6**: `Δ⁻¹` is unbounded on prime triples, because prime-log crowding
makes `Δ(log 2, log p, log q)` arbitrarily small. -/
theorem not_bddAbove_inv_delta_primeTriples :
    ¬ BddAbove (Set.range fun x : {pqs : ℕ × ℕ × ℕ // pqs.1.Prime ∧ pqs.2.1.Prime ∧
        pqs.2.2.Prime ∧ pqs.1 < pqs.2.1 ∧ pqs.2.1 < pqs.2.2} =>
      |delta ![Real.log x.1.1, Real.log x.1.2.1, Real.log x.1.2.2]|⁻¹) := by
  rintro ⟨M, hM⟩
  obtain ⟨P⟩ := CrowdedPairs.nonempty
  have hlog2 : Real.log 2 < P.a 0 := by
    have := P.a_ge 0; have := P.base_ge 0
    have : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; norm_num at this; linarith
    linarith
  have hp2 : ∀ j, 2 < P.p j := fun j => by
    have h1 := P.a_ge j; have h2 := P.base_ge j
    have h3 : Real.log 2 < Real.log (P.p j) := by
      have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
      unfold CrowdedPairs.a at h1; linarith
    exact_mod_cast (Real.log_lt_log_iff two_pos (by exact_mod_cast (P.p_prime j).pos)).mp h3
  have hpq : ∀ j, P.p j < P.q j := fun j => by
    have h := P.a_lt_b j
    unfold CrowdedPairs.a CrowdedPairs.b at h
    exact_mod_cast (Real.log_lt_log_iff (by exact_mod_cast (P.p_prime j).pos)
      (by exact_mod_cast (P.q_prime j).pos)).mp h
  have hbound : ∀ j, |delta ![Real.log 2, P.a j, P.b j]| ≤
      (P.base j + 3) ^ 2 * (3 * P.η j) := fun j => by
    rw [delta_three]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    have ha := P.a_ge j; have hb := P.b_le j; have hab := P.a_lt_b j
    have hgap := P.b_sub_a_le j
    have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hb3 := P.base_ge j
    have hla : Real.log 2 < P.a j := by
      have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
      linarith
    rw [abs_mul, abs_mul, abs_of_neg (by linarith : Real.log 2 - P.a j < 0),
      abs_of_neg (by linarith : Real.log 2 - P.b j < 0),
      abs_of_neg (by linarith : P.a j - P.b j < 0)]
    have e1 : -(Real.log 2 - P.a j) ≤ P.base j + 3 := by linarith
    have e2 : -(Real.log 2 - P.b j) ≤ P.base j + 3 := by linarith
    have e3 : -(P.a j - P.b j) ≤ 3 * P.η j := by linarith
    have p1 : 0 ≤ -(Real.log 2 - P.a j) := by linarith
    have p2 : 0 ≤ -(Real.log 2 - P.b j) := by linarith
    have p3 : 0 ≤ -(P.a j - P.b j) := by linarith
    calc -(Real.log 2 - P.a j) * -(Real.log 2 - P.b j) * -(P.a j - P.b j)
        ≤ (P.base j + 3) * (P.base j + 3) * (3 * P.η j) := by gcongr
      _ = (P.base j + 3) ^ 2 * (3 * P.η j) := by ring
  have hpos : ∀ j, 0 < |delta ![Real.log 2, P.a j, P.b j]| := fun j => by
    rw [delta_three, abs_pos]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    have hab := P.a_lt_b j
    have hla : Real.log 2 < P.a j := by
      have := P.a_ge j; have := P.base_ge j
      have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; norm_num at this; linarith
      linarith
    exact mul_ne_zero (mul_ne_zero (by linarith) (by linarith)) (by linarith)
  have hmem : ∀ j, |delta ![Real.log 2, P.a j, P.b j]|⁻¹ ≤ M := fun j =>
    hM ⟨⟨⟨2, P.p j, P.q j⟩, Nat.prime_two, P.p_prime j, P.q_prime j, hp2 j, hpq j⟩, rfl⟩
  have hbase : Tendsto P.base atTop atTop := by
    rw [show P.base = fun j : ℕ => P.R₀ + 4 * (j : ℝ) from funext P.base_eq]
    exact tendsto_atTop_add_const_left _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  have hlim : Tendsto (fun j => (P.base j + 3) ^ 2 * (3 * P.η j)) atTop (𝓝 0) := by
    have h1 := ((tendsto_zpow_mul_crowdWidth P.hc P.hK 2).comp hbase).const_mul 48
    rw [mul_zero] at h1
    refine squeeze_zero (fun j => by have := (P.η_pos j).le; positivity) (fun j => ?_) h1
    have hb3 := P.base_ge j
    have hη := (P.η_pos j).le
    simp only [Function.comp_apply, zpow_ofNat]
    unfold CrowdedPairs.η
    have : (P.base j + 3) ^ 2 ≤ 16 * P.base j ^ 2 := by nlinarith
    nlinarith [crowdWidth_pos (c := P.c) P.hK (P.base j)]
  have hM0 : 0 < M := (inv_pos.mpr (hpos 0)).trans_le (hmem 0)
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds (inv_pos.mpr hM0))).exists
  have := hmem j
  rw [inv_le_comm₀ (hpos j) hM0] at this
  linarith [hbound j]

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
