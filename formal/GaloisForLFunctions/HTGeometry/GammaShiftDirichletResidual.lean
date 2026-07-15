import GaloisForLFunctions.HTGeometry.GammaShiftJetAnnihilator
import GaloisForLFunctions.HTGeometry.LSeriesPowerTwist

/-!
# Finite Gamma-shift Dirichlet residual law

This module supplies the exact algebraic and asymptotic Dirichlet layer of the canonical finite
Gamma-jet annihilator.  It proves that the annihilator coefficients are polynomials in the
translation parameter with the sharp degree bound `deg a_k ≤ N-k`, identifies their monomial
amplitude, commutes the finite shift operator with an absolutely convergent `LSeries`, and extracts
the first nonzero Dirichlet coefficient by mathlib's far-right coefficient theorem.
-/

open scoped BigOperators Topology

namespace GaloisForLFunctions

open Filter Polynomial LSeries

noncomputable section


variable {ι : Type*} [Fintype ι]

/-- The `k`-th ascending-Pochhammer coordinate as a linear functional. -/
def ascPochhammerCoeffLinear (k : ℕ) : ℂ[X] →ₗ[ℂ] ℂ :=
  (ascPochhammerBasis ℂ).coord k

@[simp]
theorem ascPochhammerCoeffLinear_apply (P : ℂ[X]) (k : ℕ) :
    ascPochhammerCoeffLinear k P = ascPochhammerCoeff ℂ P k := by
  rfl

/-- Apply a linear functional to every coefficient of a nested polynomial. -/
def mapPolynomialCoeffs (L : ℂ[X] →ₗ[ℂ] ℂ) (P : Polynomial ℂ[X]) : ℂ[X] :=
  P.sum fun n c => Polynomial.monomial n (L c)

theorem mapPolynomialCoeffs_coeff (L : ℂ[X] →ₗ[ℂ] ℂ) (P : Polynomial ℂ[X]) (n : ℕ) :
    (mapPolynomialCoeffs L P).coeff n = L (P.coeff n) := by
  classical
  rw [mapPolynomialCoeffs, Polynomial.coeff_sum, Polynomial.sum_def]
  by_cases hn : n ∈ P.support
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      simp [Polynomial.coeff_monomial, hbn]
    · intro hnot
      exact (hnot hn).elim
  · have hc : P.coeff n = 0 := Polynomial.notMem_support_iff.mp hn
    rw [hc, map_zero]
    apply Finset.sum_eq_zero
    intro b hb
    have hbn : b ≠ n := by
      intro h
      subst h
      exact hn hb
    simp [Polynomial.coeff_monomial, hbn]

/-- The prescribed-root polynomial, with the parameter as the outer variable. -/
def gammaJetParameterRoot (shift : ι → ℂ) (mult : ι → ℕ) : Polynomial ℂ[X] :=
  ∏ i, ((Polynomial.C (Polynomial.X - Polynomial.C (shift i)) : Polynomial ℂ[X]) -
    Polynomial.X) ^ mult i

theorem gammaJetParameterRoot_eval (shift : ι → ℂ) (mult : ι → ℕ) (s : ℂ) :
    (gammaJetParameterRoot shift mult).eval (Polynomial.C s) =
      gammaJetRootPolynomial ℂ s shift mult := by
  classical
  rw [gammaJetParameterRoot, gammaJetRootPolynomial]
  rw [show (∏ i, ((Polynomial.C (Polynomial.X - Polynomial.C (shift i)) :
      Polynomial ℂ[X]) - Polynomial.X) ^ mult i) =
      (∏ i ∈ Finset.univ, ((Polynomial.C (Polynomial.X - Polynomial.C (shift i)) :
        Polynomial ℂ[X]) - Polynomial.X) ^ mult i) by rfl]
  rw [Polynomial.eval_prod]
  simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  rw [map_add]
  ring

private theorem gammaJetParameterFactor_eq (z : ℂ) :
    (Polynomial.C (Polynomial.X - Polynomial.C z) : Polynomial ℂ[X]) - Polynomial.X =
      -(Polynomial.X - Polynomial.C (Polynomial.X - Polynomial.C z)) := by
  ring

private theorem gammaJetParameterFactor_natDegree (z : ℂ) :
    ((Polynomial.C (Polynomial.X - Polynomial.C z) : Polynomial ℂ[X]) -
      Polynomial.X).natDegree = 1 := by
  rw [gammaJetParameterFactor_eq, Polynomial.natDegree_neg,
    Polynomial.natDegree_X_sub_C]

private theorem gammaJetParameterFactor_ne_zero (z : ℂ) :
    (Polynomial.C (Polynomial.X - Polynomial.C z) : Polynomial ℂ[X]) -
      Polynomial.X ≠ 0 := by
  rw [gammaJetParameterFactor_eq]
  exact neg_ne_zero.mpr (Polynomial.X_sub_C_ne_zero _)

private theorem gammaJetParameterFactor_leadingCoeff (z : ℂ) :
    ((Polynomial.C (Polynomial.X - Polynomial.C z) : Polynomial ℂ[X]) -
      Polynomial.X).leadingCoeff = -1 := by
  rw [gammaJetParameterFactor_eq, Polynomial.leadingCoeff_neg]
  rw [(Polynomial.monic_X_sub_C _).leadingCoeff]

theorem gammaJetParameterRoot_natDegree (shift : ι → ℂ) (mult : ι → ℕ) :
    (gammaJetParameterRoot shift mult).natDegree = gammaJetOrder mult := by
  classical
  rw [gammaJetParameterRoot, Polynomial.natDegree_prod]
  · rw [gammaJetOrder]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Polynomial.natDegree_pow]
    rw [gammaJetParameterFactor_natDegree, mul_one]
  · intro i hi
    exact pow_ne_zero _ (gammaJetParameterFactor_ne_zero _)

theorem gammaJetParameterRoot_topCoeff (shift : ι → ℂ) (mult : ι → ℕ) :
    (gammaJetParameterRoot shift mult).coeff (gammaJetOrder mult) =
      (-1 : ℂ[X]) ^ gammaJetOrder mult := by
  classical
  have hN := gammaJetParameterRoot_natDegree shift mult
  nth_rewrite 1 [← hN]
  rw [Polynomial.coeff_natDegree, gammaJetParameterRoot, Polynomial.leadingCoeff_prod]
  simp_rw [Polynomial.leadingCoeff_pow, gammaJetParameterFactor_leadingCoeff]
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

theorem mapPolynomialCoeffs_eval (L : ℂ[X] →ₗ[ℂ] ℂ) (P : Polynomial ℂ[X]) (s : ℂ) :
    (mapPolynomialCoeffs L P).eval s = L (P.eval (Polynomial.C s)) := by
  have hzero : mapPolynomialCoeffs L 0 = 0 := by
    ext n
    simp [mapPolynomialCoeffs_coeff]
  have hadd : ∀ A B : Polynomial ℂ[X],
      mapPolynomialCoeffs L (A + B) =
        mapPolynomialCoeffs L A + mapPolynomialCoeffs L B := by
    intro A B
    ext n
    simp [mapPolynomialCoeffs_coeff]
  have hmonomial : ∀ (n : ℕ) (c : ℂ[X]),
      mapPolynomialCoeffs L (Polynomial.monomial n c) =
        Polynomial.monomial n (L c) := by
    intro n c
    ext m
    by_cases hmn : m = n
    · subst m
      simp [mapPolynomialCoeffs_coeff]
    · have hnm : n ≠ m := Ne.symm hmn
      simp [mapPolynomialCoeffs_coeff, Polynomial.coeff_monomial, hnm]
  induction P using Polynomial.induction_on' with
  | add A B hA hB =>
      rw [hadd, Polynomial.eval_add, hA, hB, Polynomial.eval_add, map_add]
  | monomial n c =>
      rw [hmonomial, Polynomial.eval_monomial, Polynomial.eval_monomial]
      have hmap := L.map_smul (s ^ n) c
      simpa [Polynomial.smul_eq_C_mul, map_pow, mul_comm] using hmap.symm

/-- The `k`-th annihilator coefficient as a polynomial in the parameter `s`. -/
def gammaJetAnnihilatorCoeffPolynomial
    (shift : ι → ℂ) (mult : ι → ℕ) (k : ℕ) : ℂ[X] :=
  mapPolynomialCoeffs (ascPochhammerCoeffLinear k) (gammaJetParameterRoot shift mult)

theorem gammaJetAnnihilatorCoeffPolynomial_eval
    (shift : ι → ℂ) (mult : ι → ℕ) (k : ℕ) (s : ℂ) :
    (gammaJetAnnihilatorCoeffPolynomial shift mult k).eval s =
      gammaJetAnnihilatorCoeff s shift mult k := by
  rw [gammaJetAnnihilatorCoeffPolynomial, mapPolynomialCoeffs_eval,
    gammaJetParameterRoot_eval]
  rfl

/-- A nested polynomial has total degree at most `N`. -/
def BivariateTotalDegreeLE (P : Polynomial ℂ[X]) (N : ℕ) : Prop :=
  ∀ m, P.coeff m ≠ 0 → (P.coeff m).natDegree + m ≤ N


theorem BivariateTotalDegreeLE.mul {P Q : Polynomial ℂ[X]} {M N : ℕ}
    (hP : BivariateTotalDegreeLE P M) (hQ : BivariateTotalDegreeLE Q N) :
    BivariateTotalDegreeLE (P * Q) (M + N) := by
  intro m hm
  rw [Polynomial.coeff_mul] at hm ⊢
  obtain ⟨ij, hij, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
  rcases ij with ⟨i, j⟩
  rw [Finset.mem_antidiagonal] at hij
  have hPi : P.coeff i ≠ 0 := fun h => hterm (by rw [h, zero_mul])
  have hQj : Q.coeff j ≠ 0 := fun h => hterm (by rw [h, mul_zero])
  have h1 := hP i hPi
  have h2 := hQ j hQj
  have hmle : m ≤ M + N := by omega
  have hsumdeg : (∑ x ∈ Finset.antidiagonal m,
      P.coeff x.1 * Q.coeff x.2).natDegree ≤ M + N - m := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro ab hab
    rcases ab with ⟨a, b⟩
    rw [Finset.mem_antidiagonal] at hab
    by_cases hz : P.coeff a * Q.coeff b = 0
    · rw [hz, Polynomial.natDegree_zero]
      omega
    · have hPa : P.coeff a ≠ 0 := fun h => hz (by rw [h, zero_mul])
      have hQb : Q.coeff b ≠ 0 := fun h => hz (by rw [h, mul_zero])
      rw [Polynomial.natDegree_mul hPa hQb]
      have ha := hP a hPa
      have hb := hQ b hQb
      omega
  omega

theorem BivariateTotalDegreeLE.pow {P : Polynomial ℂ[X]} {M : ℕ}
    (hP : BivariateTotalDegreeLE P M) (d : ℕ) :
    BivariateTotalDegreeLE (P ^ d) (d * M) := by
  induction d with
  | zero =>
      intro m hm
      rcases m with _ | m
      · simp
      · exfalso
        apply hm
        simp [pow_zero, Polynomial.coeff_one]
  | succ d ih =>
      rw [pow_succ, Nat.succ_mul]
      exact ih.mul hP

theorem gammaJetParameterFactor_totalDegreeLE (z : ℂ) :
    BivariateTotalDegreeLE
      ((Polynomial.C (Polynomial.X - Polynomial.C z) : Polynomial ℂ[X]) - Polynomial.X) 1 := by
  intro m hm
  rcases m with _ | _ | m
  · simp
  · simp
  · exfalso
    apply hm
    simp [Polynomial.coeff_sub, Polynomial.coeff_X]

theorem gammaJetParameterRoot_totalDegreeLE (shift : ι → ℂ) (mult : ι → ℕ) :
    BivariateTotalDegreeLE (gammaJetParameterRoot shift mult) (gammaJetOrder mult) := by
  classical
  rw [gammaJetParameterRoot, gammaJetOrder]
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
      simp only [Finset.prod_empty, Finset.sum_empty]
      intro m hm
      rcases m with _ | m
      · simp
      · exfalso
        apply hm
        simp [Polynomial.coeff_one]
  | @insert i S hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      have h := (gammaJetParameterFactor_totalDegreeLE (shift i)).pow (mult i) |>.mul ih
      simpa only [Nat.mul_one] using h

/-- Equation (16): the `k`-th coefficient has parameter degree at most `N-k`. -/
theorem gammaJetAnnihilatorCoeffPolynomial_degree_add_le
    (shift : ι → ℂ) (mult : ι → ℕ) (k : ℕ) (hk : k ≤ gammaJetOrder mult) :
    (gammaJetAnnihilatorCoeffPolynomial shift mult k).natDegree + k ≤
      gammaJetOrder mult := by
  by_cases hzero : gammaJetAnnihilatorCoeffPolynomial shift mult k = 0
  · rw [hzero, Polynomial.natDegree_zero]
    simpa using hk
  · let Q := gammaJetAnnihilatorCoeffPolynomial shift mult k
    let n := Q.natDegree
    have hQ : Q ≠ 0 := by simpa [Q] using hzero
    have hlead : Q.coeff n ≠ 0 := by
      dsimp [n]
      exact Polynomial.leadingCoeff_ne_zero.mpr hQ
    have hcoordLinear : ascPochhammerCoeffLinear k
        ((gammaJetParameterRoot shift mult).coeff n) ≠ 0 := by
      rw [← mapPolynomialCoeffs_coeff]
      change Q.coeff n ≠ 0
      exact hlead
    have hcoeff : (gammaJetParameterRoot shift mult).coeff n ≠ 0 := by
      intro h
      rw [h, map_zero] at hcoordLinear
      exact hcoordLinear rfl
    have htotal := gammaJetParameterRoot_totalDegreeLE shift mult n hcoeff
    have hcoord_nonzero : ascPochhammerCoeff ℂ
        ((gammaJetParameterRoot shift mult).coeff n) k ≠ 0 := hcoordLinear
    have hkdeg : k ≤ ((gammaJetParameterRoot shift mult).coeff n).natDegree := by
      by_contra hnot
      exact hcoord_nonzero (ascPochhammerCoeff_eq_zero_of_natDegree_lt ℂ _ le_rfl
        (Nat.lt_of_not_ge hnot))
    change n + k ≤ gammaJetOrder mult
    omega

/-- Equation (14): the monomial shadow of the ascending-factorial annihilator. -/
def gammaJetDirichletAmplitude
    (s : ℂ) (shift : ι → ℂ) (mult : ι → ℕ) (T : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (gammaJetOrder mult + 1),
    gammaJetAnnihilatorCoeff s shift mult k * T ^ k

/-- The amplitude as a genuine polynomial in the parameter `s`. -/
def gammaJetDirichletAmplitudePolynomial
    (shift : ι → ℂ) (mult : ι → ℕ) (T : ℂ) : ℂ[X] :=
  ∑ k ∈ Finset.range (gammaJetOrder mult + 1),
    Polynomial.C (T ^ k) * gammaJetAnnihilatorCoeffPolynomial shift mult k

theorem gammaJetDirichletAmplitudePolynomial_eval
    (shift : ι → ℂ) (mult : ι → ℕ) (T s : ℂ) :
    (gammaJetDirichletAmplitudePolynomial shift mult T).eval s =
      gammaJetDirichletAmplitude s shift mult T := by
  rw [gammaJetDirichletAmplitudePolynomial, gammaJetDirichletAmplitude,
    Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    gammaJetAnnihilatorCoeffPolynomial_eval]
  ring

theorem gammaJetAnnihilatorCoeffPolynomial_topCoeff_zero
    (shift : ι → ℂ) (mult : ι → ℕ) {k : ℕ}
    (hk : k ≤ gammaJetOrder mult) (hk0 : k ≠ 0) :
    (gammaJetAnnihilatorCoeffPolynomial shift mult k).coeff (gammaJetOrder mult) = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have hdeg := gammaJetAnnihilatorCoeffPolynomial_degree_add_le shift mult k hk
  omega

theorem gammaJetAnnihilatorCoeffPolynomial_zero_topCoeff
    (shift : ι → ℂ) (mult : ι → ℕ) :
    (gammaJetAnnihilatorCoeffPolynomial shift mult 0).coeff (gammaJetOrder mult) =
      (-1 : ℂ) ^ gammaJetOrder mult := by
  rw [gammaJetAnnihilatorCoeffPolynomial, mapPolynomialCoeffs_coeff,
    gammaJetParameterRoot_topCoeff]
  change ascPochhammerCoeff ℂ ((-1 : ℂ[X]) ^ gammaJetOrder mult) 0 = _
  rw [ascPochhammerCoeff_zero_eq_eval_zero]
  simp

theorem gammaJetDirichletAmplitudePolynomial_degree_le
    (shift : ι → ℂ) (mult : ι → ℕ) (T : ℂ) :
    (gammaJetDirichletAmplitudePolynomial shift mult T).natDegree ≤ gammaJetOrder mult := by
  rw [gammaJetDirichletAmplitudePolynomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  have hkN : k ≤ gammaJetOrder mult := by
    have := Finset.mem_range.mp hk
    omega
  have hdeg := gammaJetAnnihilatorCoeffPolynomial_degree_add_le shift mult k hkN
  exact (Polynomial.natDegree_C_mul_le _ _).trans (by omega)

theorem gammaJetDirichletAmplitudePolynomial_topCoeff
    (shift : ι → ℂ) (mult : ι → ℕ) (T : ℂ) :
    (gammaJetDirichletAmplitudePolynomial shift mult T).coeff (gammaJetOrder mult) =
      (-1 : ℂ) ^ gammaJetOrder mult := by
  rw [gammaJetDirichletAmplitudePolynomial, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp [gammaJetAnnihilatorCoeffPolynomial_zero_topCoeff]
  · intro k hk hk0
    have hkN : k ≤ gammaJetOrder mult := by
      have := Finset.mem_range.mp hk
      omega
    rw [Polynomial.coeff_C_mul,
      gammaJetAnnihilatorCoeffPolynomial_topCoeff_zero shift mult hkN hk0, mul_zero]
  · simp


/-- A complex-coefficient polynomial divided by a prescribed top power tends to that coefficient. -/
theorem tendsto_polynomial_eval_div_pow
    (P : ℂ[X]) (N : ℕ) (hdeg : P.natDegree ≤ N) :
    Tendsto (fun x : ℝ => P.eval (x : ℂ) / (x : ℂ) ^ N)
      atTop (𝓝 (P.coeff N)) := by
  have heval : ∀ x : ℝ, P.eval (x : ℂ) / (x : ℂ) ^ N =
      ∑ i ∈ Finset.range (N + 1),
        P.coeff i * ((x : ℂ) ^ i / (x : ℂ) ^ N) := by
    intro x
    rw [P.eval_eq_sum_range' (Nat.lt_succ_of_le hdeg), Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [tendsto_congr' (Filter.Eventually.of_forall heval)]
  have hterm : ∀ i ∈ Finset.range (N + 1),
      Tendsto (fun x : ℝ => P.coeff i * ((x : ℂ) ^ i / (x : ℂ) ^ N))
        atTop (𝓝 (if i = N then P.coeff N else 0)) := by
    intro i hi
    have hiN : i ≤ N := by
      have := Finset.mem_range.mp hi
      omega
    by_cases hieq : i = N
    · subst i
      have hone : Tendsto (fun x : ℝ => (x : ℂ) ^ N / (x : ℂ) ^ N)
          atTop (𝓝 1) := by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        exact (div_self (pow_ne_zero N (Complex.ofReal_ne_zero.mpr hx.ne'))).symm
      simpa using tendsto_const_nhds.mul hone
    · have hilt : i < N := lt_of_le_of_ne hiN hieq
      have hreal : Tendsto (fun x : ℝ => x ^ i / x ^ N) atTop (𝓝 0) :=
        tendsto_pow_div_pow_atTop_zero hilt
      have hcomplex : Tendsto (fun x : ℝ => ((x ^ i / x ^ N : ℝ) : ℂ))
          atTop (𝓝 0) := Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
      have hratio : Tendsto (fun x : ℝ => (x : ℂ) ^ i / (x : ℂ) ^ N)
          atTop (𝓝 0) := by
        simpa only [Complex.ofReal_div, Complex.ofReal_pow] using hcomplex
      simpa [hieq] using tendsto_const_nhds.mul hratio
  have hsum := tendsto_finsetSum (s := Finset.range (N + 1)) hterm
  simpa [Finset.sum_ite_irrel, Finset.mem_range] using hsum

/-- Equation (18), in normalized-limit form. -/
theorem gammaJetDirichletAmplitude_normalized_tendsto
    (shift : ι → ℂ) (mult : ι → ℕ) (T : ℂ) :
    Tendsto (fun x : ℝ =>
      gammaJetDirichletAmplitude (x : ℂ) shift mult T /
        (x : ℂ) ^ gammaJetOrder mult)
      atTop (𝓝 ((-1 : ℂ) ^ gammaJetOrder mult)) := by
  simpa only [← gammaJetDirichletAmplitudePolynomial_eval,
    gammaJetDirichletAmplitudePolynomial_topCoeff] using
      tendsto_polynomial_eval_div_pow
        (gammaJetDirichletAmplitudePolynomial shift mult T)
        (gammaJetOrder mult)
        (gammaJetDirichletAmplitudePolynomial_degree_le shift mult T)

/-- Translation of one Dirichlet term exposes the inverse-base multiplier. -/
theorem LSeries_term_add_nat
    (c : ℕ → ℂ) (s : ℂ) (k n : ℕ) :
    LSeries.term c (s + k) n =
      LSeries.term c s n * ((n : ℂ)⁻¹) ^ k := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr hn), Complex.cpow_natCast]
    rw [inv_pow]
    field_simp

/-- Equation (15): exact termwise coefficient transform in every absolute-convergence point. -/
theorem gammaJetAnnihilator_LSeries_eq_tsum
    (c : ℕ → ℂ) (s : ℂ) (shift : ι → ℂ) (mult : ι → ℕ)
    (hs : LSeriesSummable c s) :
    gammaJetAnnihilator s shift mult (fun z => LSeries c z) =
      ∑' n, LSeries.term c s n *
        gammaJetDirichletAmplitude s shift mult ((n : ℂ)⁻¹) := by
  have hshift : ∀ k : ℕ, LSeriesSummable c (s + k) := by
    intro k
    exact hs.of_re_le_re (by simp)
  have hsum : ∀ k ∈ Finset.range (gammaJetOrder mult + 1),
      Summable (fun n => gammaJetAnnihilatorCoeff s shift mult k *
        LSeries.term c (s + k) n) := by
    intro k hk
    exact (hshift k).mul_left _
  rw [gammaJetAnnihilator]
  simp only [gammaJetDirichletAmplitude, LSeries]
  simp_rw [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum hsum]
  apply tsum_congr
  intro n
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [LSeries_term_add_nat]
  ring

/-- First-coefficient extraction remains exact after a fixed right translation. -/
theorem LSeries_firstCoeff_shift_tendsto
    (c : ℕ → ℂ) (a k : ℕ) (hzero : ∀ m ≤ a, c m = 0)
    (hc : LSeries.abscissaOfAbsConv c < ⊤) :
    Tendsto (fun x : ℝ =>
      ((a : ℂ) + 1) ^ (x : ℂ) * LSeries c ((x + k : ℝ) : ℂ))
      atTop (𝓝 (c (a + 1) / ((a : ℂ) + 1) ^ k)) := by
  have hfirst := LSeries.tendsto_cpow_mul_atTop (f := c) (n := a) hzero hc
  have hshift : Tendsto (fun x : ℝ => x + (k : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (k : ℝ) tendsto_id
  have hcomp := hfirst.comp hshift
  have hdiv := hcomp.div_const (((a : ℂ) + 1) ^ k)
  apply hdiv.congr'
  filter_upwards with x
  simp only [Function.comp_apply]
  push_cast
  have hbase : (a : ℂ) + 1 ≠ 0 := by
    intro h
    have hre : (a : ℝ) + 1 = 0 := by
      simpa using congrArg Complex.re h
    have hpos : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    linarith
  rw [Complex.cpow_add _ _ hbase, Complex.cpow_natCast]
  have hbasepow : ((a : ℂ) + 1) ^ k ≠ 0 := pow_ne_zero k hbase
  apply (div_eq_iff hbasepow).2
  ring

/-- Equation (13), as an exact normalized limit extracted from the first nonzero coefficient. -/
theorem gammaJetAnnihilator_LSeries_firstCoeff_tendsto
    (c : ℕ → ℂ) (a : ℕ) (hzero : ∀ m ≤ a, c m = 0)
    (hc : LSeries.abscissaOfAbsConv c < ⊤)
    (shift : ι → ℂ) (mult : ι → ℕ) :
    Tendsto (fun x : ℝ =>
      ((a : ℂ) + 1) ^ (x : ℂ) *
          gammaJetAnnihilator (x : ℂ) shift mult (fun z => LSeries c z) /
        (x : ℂ) ^ gammaJetOrder mult)
      atTop (𝓝 (c (a + 1) * (-1 : ℂ) ^ gammaJetOrder mult)) := by
  have hterm : ∀ k ∈ Finset.range (gammaJetOrder mult + 1),
      Tendsto (fun x : ℝ =>
        (gammaJetAnnihilatorCoeffPolynomial shift mult k).eval (x : ℂ) /
            (x : ℂ) ^ gammaJetOrder mult *
          (((a : ℂ) + 1) ^ (x : ℂ) * LSeries c ((x + k : ℝ) : ℂ)))
        atTop (𝓝 (if k = 0 then (-1 : ℂ) ^ gammaJetOrder mult * c (a + 1) else 0)) := by
    intro k hk
    have hkN : k ≤ gammaJetOrder mult := by
      have := Finset.mem_range.mp hk
      omega
    have hpoly := tendsto_polynomial_eval_div_pow
      (gammaJetAnnihilatorCoeffPolynomial shift mult k)
      (gammaJetOrder mult) (by
        have h := gammaJetAnnihilatorCoeffPolynomial_degree_add_le shift mult k hkN
        omega)
    have hseries := LSeries_firstCoeff_shift_tendsto c a k hzero hc
    by_cases hk0 : k = 0
    · subst k
      simpa [gammaJetAnnihilatorCoeffPolynomial_zero_topCoeff] using hpoly.mul hseries
    · have htop := gammaJetAnnihilatorCoeffPolynomial_topCoeff_zero shift mult hkN hk0
      rw [htop] at hpoly
      simpa [hk0] using hpoly.mul hseries
  have hsum := tendsto_finsetSum (s := Finset.range (gammaJetOrder mult + 1)) hterm
  have hlimval : (∑ k ∈ Finset.range (gammaJetOrder mult + 1),
      if k = 0 then (-1 : ℂ) ^ gammaJetOrder mult * c (a + 1) else 0) =
      c (a + 1) * (-1 : ℂ) ^ gammaJetOrder mult := by
    rw [Finset.sum_eq_single 0]
    · simp
      ring
    · intro k hk hk0
      simp [hk0]
    · simp
  rw [← hlimval]
  apply hsum.congr'
  filter_upwards with x
  rw [gammaJetAnnihilator]
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [gammaJetAnnihilatorCoeffPolynomial_eval]
  push_cast
  ring

/-- Nonvanishing consequence of the first-coefficient residual law. -/
theorem gammaJetAnnihilator_LSeries_ne_zero_eventually
    (c : ℕ → ℂ) (a : ℕ) (hzero : ∀ m ≤ a, c m = 0) (ha : c (a + 1) ≠ 0)
    (hc : LSeries.abscissaOfAbsConv c < ⊤)
    (shift : ι → ℂ) (mult : ι → ℕ) :
    ∀ᶠ x : ℝ in atTop,
      gammaJetAnnihilator (x : ℂ) shift mult (fun z => LSeries c z) ≠ 0 := by
  have hlim := gammaJetAnnihilator_LSeries_firstCoeff_tendsto
    c a hzero hc shift mult
  have htarget : c (a + 1) * (-1 : ℂ) ^ gammaJetOrder mult ≠ 0 :=
    mul_ne_zero ha (pow_ne_zero _ (by norm_num))
  have hnorm := hlim.norm
  have hpos : 0 < ‖c (a + 1) * (-1 : ℂ) ^ gammaJetOrder mult‖ :=
    norm_pos_iff.mpr htarget
  have hevent := hnorm.eventually (eventually_gt_nhds (half_lt_self hpos))
  filter_upwards [hevent, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  intro hres
  rw [hres, mul_zero, zero_div, norm_zero] at hx
  linarith

end
end GaloisForLFunctions
