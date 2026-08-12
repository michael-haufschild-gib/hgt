import GaloisForLFunctions.HTGeometry.HermiteSeminormGrowth
import GaloisForLFunctions.HTGeometry.DiagonalCompactOperator

/-!
# Sharp Gaussian derivative energy for polynomial filters

Route U's coefficient-uniform prime-aperture estimate needs an operator-norm fact that was absent
from the formal corpus: on polynomials of degree at most `d`, differentiation has Gaussian `L²`
norm at most `sqrt (4πd)` in the self-dual normalization.

The proof uses no coefficient estimates.  A degree-`d` polynomial times the Gaussian lies in the
first `d+1` Hermite modes.  The oscillator number operator is diagonal there with eigenvalues
`4πj`, while its annihilation operator removes the Gaussian derivative and leaves exactly the
ordinary polynomial derivative.  Pythagoras on the finite Hermite expansion therefore gives the
sharp spectral ceiling.

The closed capstone `gaussianPolynomialDerivativeEnergy_le` is the coefficient-uniform derivative
energy bound consumed by the imaginary-translation step of Route U's C43-Y heat wedge.
-/

open scoped Real SchwartzMap
open Complex MeasureTheory

noncomputable section

namespace GaloisForLFunctions

/-- Every polynomial of degree below `n` lies in the finite span of the first `n` Hermite
polynomials.  Unlike the unrestricted span theorem, this preserves the degree horizon needed by
the number-operator estimate. -/
theorem mem_span_hermitePoly_fin_of_degree_lt :
    ∀ (n : ℕ) (p : Polynomial ℝ), p.degree < (n : WithBot ℕ) →
      p ∈ Submodule.span ℝ (Set.range (fun j : Fin n => hermitePoly (j : ℕ)))
  | 0, p, hp => by
    have hp' : p.degree < ((0 : ℕ) : WithBot ℕ) := hp
    rw [Polynomial.degree_lt_iff_coeff_zero] at hp'
    have hzero : p = 0 := by
      refine Polynomial.ext fun m => ?_
      rw [Polynomial.coeff_zero]
      exact hp' m (by exact_mod_cast Nat.zero_le m)
    rw [hzero]
    exact Submodule.zero_mem _
  | (n + 1), p, hp => by
    set c : ℝ := p.coeff n / 2 ^ n with hc
    set q : Polynomial ℝ := p - c • hermitePoly n with hq
    have hdegq : q.degree < (n : WithBot ℕ) := by
      rw [Polynomial.degree_lt_iff_coeff_zero]
      intro m hm
      have hmn : n ≤ m := by exact_mod_cast hm
      rcases eq_or_lt_of_le hmn with rfl | hlt
      · rw [hq, Polynomial.coeff_sub, Polynomial.coeff_smul, hermitePoly_coeff_self, hc,
          smul_eq_mul, div_mul_cancel₀]
        · exact sub_self _
        · exact pow_ne_zero n (two_ne_zero : (2 : ℝ) ≠ 0)
      · have hp1 : p.coeff m = 0 := by
          refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hp ?_)
          exact_mod_cast Nat.succ_le_of_lt hlt
        rw [hq, Polynomial.coeff_sub, Polynomial.coeff_smul, hp1,
          hermitePoly_coeff_eq_zero hlt, smul_zero, sub_zero]
    have hqsmall := mem_span_hermitePoly_fin_of_degree_lt n q hdegq
    have hmono :
        Set.range (fun j : Fin n => hermitePoly (j : ℕ)) ⊆
          Set.range (fun j : Fin (n + 1) => hermitePoly (j : ℕ)) := by
      rintro _ ⟨j, rfl⟩
      exact ⟨Fin.castSucc j, rfl⟩
    have hqmem := Submodule.span_mono (R := ℝ) hmono hqsmall
    have hnmem : hermitePoly n ∈
        Submodule.span ℝ (Set.range (fun j : Fin (n + 1) => hermitePoly (j : ℕ))) :=
      Submodule.subset_span ⟨Fin.last n, rfl⟩
    have hp' : p = q + c • hermitePoly n := by
      rw [hq]
      abel
    rw [hp']
    exact Submodule.add_mem _ hqmem (Submodule.smul_mem _ c hnmem)

/-- `polyGaussSchwartz` carries a finite real Hermite-polynomial expansion to the corresponding
complex Schwartz-function expansion. -/
theorem polyGaussSchwartz_sum_hermitePoly {n : ℕ} (c : Fin n → ℝ) :
    polyGaussSchwartz (∑ j : Fin n, c j • hermitePoly (j : ℕ)) =
      ∑ j : Fin n, (c j : ℂ) • hermiteSchwartz (j : ℕ) := by
  change polyGaussLM (∑ j : Fin n, c j • hermitePoly (j : ℕ)) = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul]
  change c j • polyGaussSchwartz (hermitePoly (j : ℕ)) =
    (c j : ℂ) • hermiteSchwartz (j : ℕ)
  unfold hermiteSchwartz
  apply SchwartzMap.ext
  intro x
  rw [_root_.smul_apply, _root_.smul_apply]
  show ((c j : ℂ) * (((hermitePoly (j : ℕ)).eval x * gaussReal x : ℝ) : ℂ)) =
    (c j : ℂ) * (((hermitePoly (j : ℕ)).eval x * gaussReal x : ℝ) : ℂ)
  rfl

/-- A degree-`d` polynomial-Gaussian lies in the first `d+1` normalized Hermite modes. -/
theorem polyGaussSchwartz_mem_hermite_span (P : Polynomial ℝ) :
    (polyGaussSchwartz P).toLp 2 (volume : Measure ℝ) ∈
      Submodule.span ℂ (Set.range fun j : Fin (P.natDegree + 1) =>
        (hermiteUnit (j : ℕ)).toLp 2 (volume : Measure ℝ)) := by
  have hdeg : P.degree < ((P.natDegree + 1 : ℕ) : WithBot ℕ) := by
    refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
    exact_mod_cast Nat.lt_succ_self P.natDegree
  have hmem := mem_span_hermitePoly_fin_of_degree_lt (P.natDegree + 1) P hdeg
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  have hpolyGauss :
      polyGaussSchwartz P =
        ∑ j : Fin (P.natDegree + 1), (c j : ℂ) • hermiteSchwartz (j : ℕ) := by
    calc
      polyGaussSchwartz P = polyGaussSchwartz
          (∑ j : Fin (P.natDegree + 1), c j • hermitePoly (j : ℕ)) := congrArg _ hc.symm
      _ = _ := polyGaussSchwartz_sum_hermitePoly c
  rw [hpolyGauss]
  have htoLp :
      (∑ j : Fin (P.natDegree + 1), (c j : ℂ) • hermiteSchwartz (j : ℕ)).toLp 2
          (volume : Measure ℝ) =
        ∑ j : Fin (P.natDegree + 1), (c j : ℂ) •
          (hermiteSchwartz (j : ℕ)).toLp 2 (volume : Measure ℝ) := by
    change (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ))
      (∑ j : Fin (P.natDegree + 1), (c j : ℂ) • hermiteSchwartz (j : ℕ)) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, SchwartzMap.toLpCLM_apply]
  rw [htoLp]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hnorm : (0 : ℝ) < ‖(hermiteSchwartz (j : ℕ)).toLp 2 (volume : Measure ℝ)‖ :=
    hermiteNorm_pos (j : ℕ)
  have hunit :
      (hermiteSchwartz (j : ℕ)).toLp 2 (volume : Measure ℝ) =
        (‖(hermiteSchwartz (j : ℕ)).toLp 2 (volume : Measure ℝ)‖ : ℂ) •
          (hermiteUnit (j : ℕ)).toLp 2 (volume : Measure ℝ) := by
    rw [hermiteUnit, toLp_smul, smul_smul]
    simp [hnorm.ne']
  rw [hunit, smul_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- On a degree-`d` polynomial-Gaussian, the number operator has norm at most `4πd` times the
original norm. -/
theorem numberCLM_polyGauss_norm_le (P : Polynomial ℝ) :
    ‖(numberCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ)‖ ≤
      4 * π * P.natDegree * ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := by
  let e : Fin (P.natDegree + 1) → Lp ℂ 2 (volume : Measure ℝ) := fun j =>
    (hermiteUnit (j : ℕ)).toLp 2 (volume : Measure ℝ)
  have he : Orthonormal ℂ e :=
    orthonormal_hermiteSchwartz_toLp.comp (fun j : Fin (P.natDegree + 1) => (j : ℕ))
      Fin.val_injective
  have hf := polyGaussSchwartz_mem_hermite_span P
  change (polyGaussSchwartz P).toLp 2 (volume : Measure ℝ) ∈
    Submodule.span ℂ (Set.range e) at hf
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hf
  have hNeigen : ∀ j : Fin (P.natDegree + 1),
      (numberCLM (hermiteUnit (j : ℕ))).toLp 2 (volume : Measure ℝ) =
        (4 * (π : ℂ) * (j : ℕ)) • e j := by
    intro j
    rw [hermiteUnit, map_smul, numberCLM_hermiteSchwartz, smul_smul, toLp_smul]
    dsimp only [e]
    rw [hermiteUnit, toLp_smul, smul_smul]
    congr 1
    ring
  have hNsum :
      (numberCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ) =
        ∑ j : Fin (P.natDegree + 1),
          (c j * (4 * (π : ℂ) * (j : ℕ))) • e j := by
    have hcS :
        ∑ j : Fin (P.natDegree + 1), c j • hermiteUnit (j : ℕ) = polyGaussSchwartz P := by
      apply SchwartzMap.injective_toLp (F := ℂ) 2 (volume : Measure ℝ)
      change (∑ j : Fin (P.natDegree + 1), c j • hermiteUnit (j : ℕ)).toLp 2
          (volume : Measure ℝ) = (polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)
      rw [show (∑ j : Fin (P.natDegree + 1), c j • hermiteUnit (j : ℕ)).toLp 2
          (volume : Measure ℝ) = ∑ j : Fin (P.natDegree + 1), c j • e j by
            change (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ))
              (∑ j : Fin (P.natDegree + 1), c j • hermiteUnit (j : ℕ)) = _
            rw [map_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul, SchwartzMap.toLpCLM_apply]]
      exact hc
    rw [← hcS, map_sum]
    change (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ))
        (∑ j : Fin (P.natDegree + 1), numberCLM (c j • hermiteUnit (j : ℕ))) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul, SchwartzMap.toLpCLM_apply, hNeigen, smul_smul]
  rw [hNsum]
  have hnormN := HTGeometry.norm_sq_sum_smul_orthonormal he
    (fun j : Fin (P.natDegree + 1) => c j * (4 * (π : ℂ) * (j : ℕ))) Finset.univ
  have hnormP := HTGeometry.norm_sq_sum_smul_orthonormal he c Finset.univ
  have hboundSq :
      ‖∑ j : Fin (P.natDegree + 1),
          (c j * (4 * (π : ℂ) * (j : ℕ))) • e j‖ ^ 2 ≤
        (4 * π * P.natDegree) ^ 2 *
          ‖∑ j : Fin (P.natDegree + 1), c j • e j‖ ^ 2 := by
    rw [hnormN, hnormP, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul, norm_mul, Complex.norm_natCast, mul_pow, mul_pow]
    have hnorm4pi : ‖(4 : ℂ) * (π : ℂ)‖ = 4 * π := by
      rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
    rw [hnorm4pi]
    have hj : ((j : ℕ) : ℝ) ≤ P.natDegree := by
      exact_mod_cast Nat.le_of_lt_succ j.2
    have hscale : (4 * π * ((j : ℕ) : ℝ)) ^ 2 ≤ (4 * π * P.natDegree) ^ 2 := by
      have hbase : 4 * π * ((j : ℕ) : ℝ) ≤ 4 * π * P.natDegree :=
        mul_le_mul_of_nonneg_left hj (by positivity)
      exact pow_le_pow_left₀ (by positivity) hbase 2
    nlinarith [hscale, sq_nonneg ‖c j‖]
  have hboundSq' :
      ‖∑ j : Fin (P.natDegree + 1),
          (c j * (4 * (π : ℂ) * (j : ℕ))) • e j‖ ^ 2 ≤
        (4 * π * P.natDegree) ^ 2 *
          ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
    rwa [hc] at hboundSq
  have hnonneg : 0 ≤ 4 * π * P.natDegree := by positivity
  have hsquare :
      ‖(numberCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
        (4 * π * P.natDegree * ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖) ^ 2 := by
    rw [hNsum]
    nlinarith [hboundSq']
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg hnonneg (norm_nonneg _))).mp
  rw [← hNsum]
  exact hsquare

/-- The annihilation operator differentiates only the polynomial factor of a polynomial-Gaussian;
the derivative of the Gaussian cancels its coordinate term exactly. -/
theorem annihilationCLM_polyGaussSchwartz (P : Polynomial ℝ) :
    annihilationCLM (polyGaussSchwartz P) = polyGaussSchwartz P.derivative := by
  apply SchwartzMap.ext
  intro x
  rw [annihilationCLM_apply, polyGaussSchwartz_apply, polyGaussSchwartz_apply]
  have hderiv := (hasDerivAt_poly_mul_gaussReal P x).ofReal_comp.deriv
  rw [show deriv (polyGaussSchwartz P : ℝ → ℂ) x =
      deriv (fun y : ℝ => ((P.eval y * gaussReal y : ℝ) : ℂ)) x from rfl,
    hderiv]
  push_cast
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  push_cast
  ring

/-- **Coefficient-uniform Gaussian derivative energy bound.**  For every real polynomial, with no
side conditions, differentiation costs at most the top Hermite number `4π natDegree(P)` in squared
Gaussian `L²` energy.  This is the sharp finite-oscillator inequality used by Route U's
imaginary-translation and prime-aperture estimate. -/
theorem gaussianPolynomialDerivativeEnergy_le (P : Polynomial ℝ) :
    ‖(polyGaussSchwartz P.derivative).toLp 2 (volume : Measure ℝ)‖ ^ 2 ≤
      4 * π * P.natDegree * ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  have hosc := norm_toLp_annihilationCLM_sq_le (polyGaussSchwartz P)
  have hnum := numberCLM_polyGauss_norm_le P
  rw [annihilationCLM_polyGaussSchwartz] at hosc
  have hnonneg : 0 ≤ ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ := norm_nonneg _
  calc
    ‖(polyGaussSchwartz P.derivative).toLp 2 (volume : Measure ℝ)‖ ^ 2
        ≤ ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ *
          ‖(numberCLM (polyGaussSchwartz P)).toLp 2 (volume : Measure ℝ)‖ := hosc
    _ ≤ ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ *
          (4 * π * P.natDegree *
            ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖) :=
      mul_le_mul_of_nonneg_left hnum hnonneg
    _ = 4 * π * P.natDegree *
          ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by ring

/-- Hermite functions are fixed by pointwise conjugation. -/
theorem conjSLM_hermiteSchwartz_eq (n : ℕ) :
    SchwartzMap.conjSLM (hermiteSchwartz n) = hermiteSchwartz n := by
  apply SchwartzMap.ext
  intro x
  rw [SchwartzMap.conjSLM_apply, conj_hermiteSchwartz]

/-- **Sharpness on every Hermite mode.**  The degree-`n` Hermite polynomial saturates the
coefficient-uniform derivative-energy ceiling exactly. -/
theorem gaussianHermitePolynomialDerivativeEnergy_eq (n : ℕ) :
    ‖(polyGaussSchwartz (hermitePoly n).derivative).toLp 2
        (volume : Measure ℝ)‖ ^ 2 =
      4 * π * n * ‖(polyGaussSchwartz (hermitePoly n)).toLp 2
        (volume : Measure ℝ)‖ ^ 2 := by
  have h := schwartzPair_conj_numberCLM (hermiteSchwartz n)
  rw [conjSLM_hermiteSchwartz_eq, numberCLM_hermiteSchwartz,
    schwartzPair_smul_right] at h
  have hself := schwartzPair_conj_self (hermiteSchwartz n)
  rw [conjSLM_hermiteSchwartz_eq] at hself
  rw [hself] at h
  have hhermite : polyGaussSchwartz (hermitePoly n) = hermiteSchwartz n := rfl
  rw [hhermite]
  rw [← annihilationCLM_polyGaussSchwartz]
  change ‖(annihilationCLM (hermiteSchwartz n)).toLp 2 volume‖ ^ 2 = _
  symm
  exact_mod_cast h

end GaloisForLFunctions
