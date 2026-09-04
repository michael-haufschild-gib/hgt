import GaloisForLFunctions.HTGeometry.StrelitzBaseFaceDecay
import GaloisForLFunctions.HTGeometry.RootProximity

/-!
# Numerical roots of the Strelitz jet curve

The fixed nonzero highest `z`-face is split in its last variable `v`.  Its first-variable
coefficients are literal one-variable polynomials, and evaluation at the Wiman values of `u`
eventually preserves the positive `v`-degree.  The corpus root-proximity theorem then selects an
actual root of every eventual specialization; the roots converge to the observed `v = z u'`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Convert a multivariate polynomial in one indexed variable to an ordinary polynomial. -/
def finOnePolynomial (A : MvPolynomial (Fin 1) ℂ) : Polynomial ℂ :=
  ∑ e ∈ A.support, Polynomial.monomial (e 0) (A.coeff e)

/-- A one-coordinate finitely supported exponent is determined by its sole entry. -/
theorem finOneExponent_injective :
    Function.Injective (fun e : Fin 1 →₀ ℕ => e 0) := by
  intro e d h
  apply Finsupp.ext
  intro i
  fin_cases i
  exact h

/-- Coefficients are preserved by the `Fin 1` to ordinary-polynomial compiler. -/
theorem coeff_finOnePolynomial
    (A : MvPolynomial (Fin 1) ℂ) (e : Fin 1 →₀ ℕ) :
    (finOnePolynomial A).coeff (e 0) =
      if e ∈ A.support then A.coeff e else 0 := by
  classical
  rw [finOnePolynomial, Polynomial.finsetSum_coeff]
  by_cases he : e ∈ A.support
  · rw [if_pos he]
    refine Finset.sum_eq_single_of_mem e he ?_ |>.trans ?_
    · intro d hd hde
      rw [Polynomial.coeff_monomial, if_neg]
      exact fun h => hde (finOneExponent_injective h)
    · simp
  · rw [if_neg he]
    refine Finset.sum_eq_zero ?_
    intro d hd
    rw [Polynomial.coeff_monomial, if_neg]
    exact fun h => he (finOneExponent_injective h ▸ hd)

/-- The one-variable compiler preserves nonzeroness. -/
theorem finOnePolynomial_ne_zero {A : MvPolynomial (Fin 1) ℂ} (hA : A ≠ 0) :
    finOnePolynomial A ≠ 0 := by
  obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hA
  intro hzero
  have hc : (finOnePolynomial A).coeff (e 0) = 0 := by rw [hzero]; simp
  rw [coeff_finOnePolynomial, if_pos he] at hc
  exact (MvPolynomial.mem_support_iff.mp he) hc

/-- Evaluation is preserved by the one-variable compiler. -/
theorem eval_finOnePolynomial (A : MvPolynomial (Fin 1) ℂ) (u : ℂ) :
    (finOnePolynomial A).eval u = MvPolynomial.eval ![u] A := by
  classical
  rw [finOnePolynomial, Polynomial.eval_finsetSum, MvPolynomial.eval_eq']
  refine Finset.sum_congr rfl ?_
  intro e he
  rw [Polynomial.eval_monomial, Fin.prod_univ_one]
  rfl

/-- Read the fixed bivariate Strelitz face as a polynomial in `v` over `C[u]`. -/
def strelitzJetCurvePolynomial (S : MvPolynomial (Fin 2) ℂ) :
    Polynomial (MvPolynomial (Fin 1) ℂ) :=
  jetUnlift S

/-- Specialize `u`, retaining an ordinary complex polynomial in `v`. -/
def strelitzJetCurveSpecialization (S : MvPolynomial (Fin 2) ℂ) (u : ℂ) :
    Polynomial ℂ :=
  (strelitzJetCurvePolynomial S).map (MvPolynomial.eval ![u])

/-- Splitting the fixed jet curve in `v` preserves nonzeroness. -/
theorem strelitzJetCurvePolynomial_ne_zero
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0) :
    strelitzJetCurvePolynomial S ≠ 0 :=
  jetUnlift_ne_zero hS

/-- Specialization in `u` followed by evaluation in `v` recovers bivariate evaluation. -/
theorem eval_strelitzJetCurveSpecialization
    (S : MvPolynomial (Fin 2) ℂ) (u v : ℂ) :
    (strelitzJetCurveSpecialization S u).eval v =
      MvPolynomial.eval ![u, v] S := by
  rw [strelitzJetCurveSpecialization, Polynomial.eval_map,
    strelitzJetCurvePolynomial]
  calc
    Polynomial.eval₂ (MvPolynomial.eval ![u]) v (jetUnlift S) =
        MvPolynomial.eval ![u, v] (lastVariableJetLift (jetUnlift S)) := by
      rw [eval_jetLift]
      congr 2
      · funext i
        fin_cases i
        rfl
    _ = MvPolynomial.eval ![u, v] S := by rw [lastVariableJetLift_jetUnlift]

open Filter

/-- A relative error at most `1/(n+1)` from an escaping natural family forces the complex family
itself to escape in norm. -/
theorem tendsto_norm_atTop_of_nat_tendsto_atTop_of_strelitzRelativeError
    {ν : ℕ → ℕ} {u : ℕ → ℂ} (hνTop : Tendsto ν atTop atTop)
    (hu : ∀ n : ℕ, ‖u n - (ν n : ℂ)‖ ≤
      (1 / ((n : ℝ) + 1)) * (ν n : ℝ)) :
    Tendsto (fun n => ‖u n‖) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  obtain ⟨N, hN⟩ := exists_nat_ge (max 1 (2 * b))
  have hν := hνTop.eventually_ge_atTop N
  filter_upwards [hν, eventually_ge_atTop 1] with n hνN hn
  have hNν : (N : ℝ) ≤ (ν n : ℝ) := by exact_mod_cast hνN
  have hbν : b ≤ (ν n : ℝ) / 2 := by
    have hbN : 2 * b ≤ (N : ℝ) := le_trans (le_max_right 1 (2 * b)) hN
    linarith
  have hrec : (1 / ((n : ℝ) + 1)) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    norm_num
    exact_mod_cast Nat.add_le_add_right hn 1
  have herr : ‖u n - (ν n : ℂ)‖ ≤ (ν n : ℝ) / 2 := by
    have hνnonneg : (0 : ℝ) ≤ (ν n : ℝ) := by positivity
    exact (hu n).trans (by nlinarith)
  have htri : (ν n : ℝ) ≤ ‖u n - (ν n : ℂ)‖ + ‖u n‖ := by
    have h := norm_add_le ((ν n : ℂ) - u n) (u n)
    rw [sub_add_cancel, Complex.norm_natCast, norm_sub_rev] at h
    exact h
  linarith

/-- A fixed nonzero one-variable polynomial stays uniformly away from zero along a complex family
escaping in norm. -/
theorem exists_eventually_pos_le_norm_eval_finOne
    {A : MvPolynomial (Fin 1) ℂ} (hA : A ≠ 0)
    {u : ℕ → ℂ} (huTop : Tendsto (fun n => ‖u n‖) atTop atTop) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c ≤ ‖MvPolynomial.eval ![u n] A‖ := by
  let p := finOnePolynomial A
  have hp : p ≠ 0 := finOnePolynomial_ne_zero hA
  let c : ℝ := ‖p.leadingCoeff‖ / 2
  have hc : 0 < c := by
    exact half_pos (norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hp))
  refine ⟨c, hc, ?_⟩
  have hlarge := huTop.eventually_ge_atTop (growthRadius p)
  filter_upwards [hlarge] with n hn
  obtain ⟨hu1, hu2⟩ := hyps_of_growthRadius_le hp hn
  have hlow := norm_eval_ge_of_large hp hu1 hu2
  have hupow : (1 : ℝ) ≤ ‖u n‖ ^ p.natDegree := one_le_pow₀ hu1
  have hc0 : 0 ≤ c := hc.le
  rw [eval_finOnePolynomial] at hlow
  have hcPow : c ≤ c * ‖u n‖ ^ p.natDegree :=
    le_mul_of_one_le_right hc0 hupow
  exact hcPow.trans hlow

/-- Along an escaping `u`-family, specialization eventually preserves the curve's degree in `v`
and its leading coefficient has a fixed positive lower bound. -/
theorem exists_eventually_strelitzJetCurve_degree_eq_and_leadingCoeff_lower
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0)
    {u : ℕ → ℂ} (huTop : Tendsto (fun n => ‖u n‖) atTop atTop) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).natDegree =
          (strelitzJetCurvePolynomial S).natDegree ∧
        c ≤ ‖(strelitzJetCurveSpecialization S (u n)).leadingCoeff‖ := by
  have hR : strelitzJetCurvePolynomial S ≠ 0 := strelitzJetCurvePolynomial_ne_zero hS
  have hlead : (strelitzJetCurvePolynomial S).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hR
  obtain ⟨c, hc, hlower⟩ := exists_eventually_pos_le_norm_eval_finOne hlead huTop
  refine ⟨c, hc, ?_⟩
  filter_upwards [hlower] with n hn
  have hne : MvPolynomial.eval ![u n] (strelitzJetCurvePolynomial S).leadingCoeff ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hn
    linarith
  constructor
  · exact Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hne
  · rw [strelitzJetCurveSpecialization,
      Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero _ hne]
    exact hn

/-- If the fixed jet curve tends to zero while `u` escapes, it must have positive degree in `v`.
The degree-zero alternative would be a nonzero polynomial in `u`, uniformly bounded away from
zero. -/
theorem one_le_natDegree_strelitzJetCurvePolynomial_of_tendsto_eval_zero
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0)
    {u v : ℕ → ℂ} (huTop : Tendsto (fun n => ‖u n‖) atTop atTop)
    (hzero : Tendsto (fun n => ‖MvPolynomial.eval ![u n, v n] S‖)
      atTop (nhds 0)) :
    1 ≤ (strelitzJetCurvePolynomial S).natDegree := by
  have hR : strelitzJetCurvePolynomial S ≠ 0 := strelitzJetCurvePolynomial_ne_zero hS
  by_contra hdeg
  have hdeg0 : (strelitzJetCurvePolynomial S).natDegree = 0 := by omega
  have hconst : strelitzJetCurvePolynomial S =
      Polynomial.C (strelitzJetCurvePolynomial S).leadingCoeff :=
    (Polynomial.eq_C_of_natDegree_eq_zero hdeg0).trans (by
      simp [Polynomial.leadingCoeff, hdeg0])
  have heq : ∀ n, MvPolynomial.eval ![u n, v n] S =
      MvPolynomial.eval ![u n] (strelitzJetCurvePolynomial S).leadingCoeff := by
    intro n
    rw [← eval_strelitzJetCurveSpecialization, strelitzJetCurveSpecialization, hconst]
    simp
  have hlead : (strelitzJetCurvePolynomial S).leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr hR
  obtain ⟨c, hc, hlower⟩ := exists_eventually_pos_le_norm_eval_finOne hlead huTop
  have hlt := hzero.eventually_lt_const hc
  obtain ⟨n, hn, hnlt⟩ := (hlower.and hlt).exists
  rw [heq n] at hnlt
  linarith

/-- Canonical nearby root of the specialized jet-curve polynomial whenever its degree is positive;
the fallback branch is irrelevant once degree preservation is established. -/
def selectedStrelitzJetCurveRoot
    (S : MvPolynomial (Fin 2) ℂ) (u v : ℕ → ℂ) (n : ℕ) : ℂ :=
  if h : 1 ≤ (strelitzJetCurveSpecialization S (u n)).natDegree then
    Classical.choose (exists_root_pow_dist_le h (v n))
  else 0

/-- The selected point is an actual root whenever the specialization has positive degree. -/
theorem selectedStrelitzJetCurveRoot_isRoot
    (S : MvPolynomial (Fin 2) ℂ) (u v : ℕ → ℂ) (n : ℕ)
    (h : 1 ≤ (strelitzJetCurveSpecialization S (u n)).natDegree) :
    (strelitzJetCurveSpecialization S (u n)).IsRoot
      (selectedStrelitzJetCurveRoot S u v n) := by
  rw [selectedStrelitzJetCurveRoot, dif_pos h]
  exact (Classical.choose_spec (exists_root_pow_dist_le h (v n))).1

/-- Quantitative root-proximity bound for the selected specialized root. -/
theorem selectedStrelitzJetCurveRoot_pow_dist_le
    (S : MvPolynomial (Fin 2) ℂ) (u v : ℕ → ℂ) (n : ℕ)
    (h : 1 ≤ (strelitzJetCurveSpecialization S (u n)).natDegree) :
    ‖v n - selectedStrelitzJetCurveRoot S u v n‖ ^
        (strelitzJetCurveSpecialization S (u n)).natDegree *
          ‖(strelitzJetCurveSpecialization S (u n)).leadingCoeff‖ ≤
      ‖MvPolynomial.eval ![u n, v n] S‖ := by
  rw [selectedStrelitzJetCurveRoot, dif_pos h]
  have hs := (Classical.choose_spec (exists_root_pow_dist_le h (v n))).2
  calc
    ‖v n - Classical.choose (exists_root_pow_dist_le h (v n))‖ ^
          (strelitzJetCurveSpecialization S (u n)).natDegree *
        ‖(strelitzJetCurveSpecialization S (u n)).leadingCoeff‖
        ≤ ‖(strelitzJetCurveSpecialization S (u n)).eval (v n)‖ := hs
    _ = ‖MvPolynomial.eval ![u n, v n] S‖ := by
      rw [eval_strelitzJetCurveSpecialization]

/-- The selected specialized roots converge to the observed second logarithmic jet. -/
theorem tendsto_selectedStrelitzJetCurveRoot_dist_zero
    {S : MvPolynomial (Fin 2) ℂ} (hS : S ≠ 0)
    {u v : ℕ → ℂ} (huTop : Tendsto (fun n => ‖u n‖) atTop atTop)
    (hzero : Tendsto (fun n => ‖MvPolynomial.eval ![u n, v n] S‖)
      atTop (nhds 0)) :
    Tendsto (fun n => ‖v n - selectedStrelitzJetCurveRoot S u v n‖)
      atTop (nhds 0) := by
  let d := (strelitzJetCurvePolynomial S).natDegree
  have hd : 1 ≤ d :=
    one_le_natDegree_strelitzJetCurvePolynomial_of_tendsto_eval_zero hS huTop hzero
  obtain ⟨c, hc, hdata⟩ :=
    exists_eventually_strelitzJetCurve_degree_eq_and_leadingCoeff_lower hS huTop
  have hpowUpper : ∀ᶠ n : ℕ in atTop,
      ‖v n - selectedStrelitzJetCurveRoot S u v n‖ ^ d ≤
        ‖MvPolynomial.eval ![u n, v n] S‖ / c := by
    filter_upwards [hdata] with n hn
    have hdegree : 1 ≤ (strelitzJetCurveSpecialization S (u n)).natDegree := by
      rw [hn.1]
      exact hd
    have hroot := selectedStrelitzJetCurveRoot_pow_dist_le S u v n hdegree
    rw [hn.1] at hroot
    change ‖v n - selectedStrelitzJetCurveRoot S u v n‖ ^ d *
      ‖(strelitzJetCurveSpecialization S (u n)).leadingCoeff‖ ≤
        ‖MvPolynomial.eval ![u n, v n] S‖ at hroot
    rw [le_div_iff₀ hc]
    exact le_trans (mul_le_mul_of_nonneg_left hn.2 (pow_nonneg (norm_nonneg _) d)) hroot
  have hpow : Tendsto (fun n =>
      ‖v n - selectedStrelitzJetCurveRoot S u v n‖ ^ d) atTop (nhds 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => pow_nonneg (norm_nonneg _) d)
      hpowUpper ?_
    simpa [hc.ne'] using hzero.div_const c
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hsmall := hpow.eventually_lt_const (pow_pos hε d)
  filter_upwards [hsmall] with n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  by_contra hnot
  have hεle : ε ≤ ‖v n - selectedStrelitzJetCurveRoot S u v n‖ := le_of_not_gt hnot
  have := pow_le_pow_left₀ hε.le hεle d
  linarith

open GaloisForLFunctions

variable {a : ℕ → ℂ}

/-- **Strelitz numerical branch selection.** An assumed order-two ADE for an infinite entire-heat
anchor yields a fixed positive-degree polynomial in `v` over `C[u]` and, along the exact Wiman
sequence, actual roots of every eventual specialization whose distance from `v = z u'` tends to
zero. -/
theorem exists_strelitzJetCurveRoots_tendsto_of_order_two_entireHeat_isMaximumOnCircle
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) 2) :
    ∃ S : MvPolynomial (Fin 2) ℂ, S ≠ 0 ∧
      1 ≤ (strelitzJetCurvePolynomial S).natDegree ∧
      ∃ (x : ℕ → ℝ) (z root : ℕ → ℂ),
        (∀ n : ℕ, (n : ℝ) ≤ x n) ∧
        (∀ n : ℕ, ‖z n‖ = Real.exp (x n)) ∧
        (∀ n : ℕ, maxTerm a (Real.exp (x n)) ≤ ‖coeffFun a (z n)‖) ∧
        (∀ n : ℕ, coeffFun a (z n) ≠ 0) ∧
        (∀ n : ℕ, ‖eulerLogDeriv (coeffFun a) (z n) -
            (centralIndex a (Real.exp (x n)) : ℂ)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ)) ∧
        (∀ n : ℕ, ‖eulerLogDerivSecond (coeffFun a) (z n)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ) ^ 2) ∧
        Tendsto x atTop atTop ∧
        Tendsto (fun n => ‖eulerLogDeriv (coeffFun a) (z n)‖) atTop atTop ∧
        (∀ᶠ n : ℕ in atTop,
          (strelitzJetCurveSpecialization S
            (eulerLogDeriv (coeffFun a) (z n))).IsRoot (root n)) ∧
        Tendsto (fun n =>
          ‖eulerLogDerivSecond (coeffFun a) (z n) - root n‖) atTop (nhds 0) ∧
        (∀ n : ℕ, ∀ w : ℂ, ‖w‖ = ‖z n‖ →
          ‖coeffFun a w‖ ≤ ‖coeffFun a (z n)‖) := by
  obtain ⟨S, hS, x, z, hx, hz, hfloor, hfz, hu, hv,
    hxTop, hνx, hjets, hSzero, hmaxCircle⟩ :=
    exists_nonzero_strelitzBaseLeadingFace_tendsto_zero_of_order_two_entireHeat_isMaximumOnCircle
      ha hheat htrans hDA
  let u : ℕ → ℂ := fun n => eulerLogDeriv (coeffFun a) (z n)
  let v : ℕ → ℂ := fun n => eulerLogDerivSecond (coeffFun a) (z n)
  have hrTop : Tendsto (fun n => Real.exp (x n)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hxTop
  have hνTop : Tendsto (fun n => centralIndex a (Real.exp (x n))) atTop atTop :=
    (tendsto_centralIndex_atTop ha htrans).comp hrTop
  have huTop : Tendsto (fun n => ‖u n‖) atTop atTop :=
    tendsto_norm_atTop_of_nat_tendsto_atTop_of_strelitzRelativeError hνTop hu
  have hdegree : 1 ≤ (strelitzJetCurvePolynomial S).natDegree :=
    one_le_natDegree_strelitzJetCurvePolynomial_of_tendsto_eval_zero hS huTop (by
      simpa [u, v] using hSzero)
  let root : ℕ → ℂ := selectedStrelitzJetCurveRoot S u v
  obtain ⟨c, hc, hdata⟩ :=
    exists_eventually_strelitzJetCurve_degree_eq_and_leadingCoeff_lower hS huTop
  have hroot : ∀ᶠ n : ℕ in atTop,
      (strelitzJetCurveSpecialization S (u n)).IsRoot (root n) := by
    filter_upwards [hdata] with n hn
    apply selectedStrelitzJetCurveRoot_isRoot
    rw [hn.1]
    exact hdegree
  have hclose : Tendsto (fun n => ‖v n - root n‖) atTop (nhds 0) :=
    tendsto_selectedStrelitzJetCurveRoot_dist_zero hS huTop (by
      simpa [u, v] using hSzero)
  exact ⟨S, hS, hdegree, x, z, root, hx, hz, hfloor, hfz, hu, hv, hxTop,
    by simpa [u] using huTop, by simpa [u, root] using hroot,
    by simpa [v, root] using hclose, hmaxCircle⟩

/-- **Strelitz numerical branch selection.** An assumed order-two ADE for an infinite entire-heat
anchor yields a fixed positive-degree polynomial in `v` over `C[u]` and, along the exact Wiman
sequence, actual roots of every eventual specialization whose distance from `v = z u'` tends to
zero. -/
theorem exists_strelitzJetCurveRoots_tendsto_of_order_two_entireHeat
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ 2) * (n : ℂ) ^ 2 * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0)
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) 2) :
    ∃ S : MvPolynomial (Fin 2) ℂ, S ≠ 0 ∧
      1 ≤ (strelitzJetCurvePolynomial S).natDegree ∧
      ∃ (x : ℕ → ℝ) (z root : ℕ → ℂ),
        (∀ n : ℕ, (n : ℝ) ≤ x n) ∧
        (∀ n : ℕ, ‖z n‖ = Real.exp (x n)) ∧
        (∀ n : ℕ, maxTerm a (Real.exp (x n)) ≤ ‖coeffFun a (z n)‖) ∧
        (∀ n : ℕ, coeffFun a (z n) ≠ 0) ∧
        (∀ n : ℕ, ‖eulerLogDeriv (coeffFun a) (z n) -
            (centralIndex a (Real.exp (x n)) : ℂ)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ)) ∧
        (∀ n : ℕ, ‖eulerLogDerivSecond (coeffFun a) (z n)‖
          ≤ (1 / ((n : ℝ) + 1)) * (centralIndex a (Real.exp (x n)) : ℝ) ^ 2) ∧
        Tendsto x atTop atTop ∧
        Tendsto (fun n => ‖eulerLogDeriv (coeffFun a) (z n)‖) atTop atTop ∧
        (∀ᶠ n : ℕ in atTop,
          (strelitzJetCurveSpecialization S
            (eulerLogDeriv (coeffFun a) (z n))).IsRoot (root n)) ∧
        Tendsto (fun n =>
          ‖eulerLogDerivSecond (coeffFun a) (z n) - root n‖) atTop (nhds 0) := by
  obtain ⟨S, hS, hdegree, x, z, root, hx, hz, hfloor, hfz, hu, hv,
    hxTop, huTop, hroot, hclose, _⟩ :=
    exists_strelitzJetCurveRoots_tendsto_of_order_two_entireHeat_isMaximumOnCircle
      ha hheat htrans hDA
  exact ⟨S, hS, hdegree, x, z, root, hx, hz, hfloor, hfz, hu, hv,
    hxTop, huTop, hroot, hclose⟩

end

end GaloisForLFunctions.HTGeometry
