import GaloisForLFunctions.HTGeometry.ArithmeticFunctionDeterminantCoefficient
import GaloisForLFunctions.HTGeometry.ArithmeticFunctionLSeriesDeterminant
import GaloisForLFunctions.HTGeometry.DirichletFlagVandermonde
import GaloisForLFunctions.HTGeometry.GammaShiftDirichletResidualExamples
import GaloisForLFunctions.HTGeometry.GammaShiftSimultaneousFactorization
import GaloisForLFunctions.RHTower.GammaShiftZetaReadout

/-! Simultaneous Gamma-shift zeta-jet Dirichlet flag. -/

open scoped BigOperators Topology

namespace GaloisForLFunctions

open Filter Polynomial LSeries Matrix ArithmeticFunction

noncomputable section

def zetaJetFullCoeff (j n : ℕ) : ℂ :=
  if n = 0 then 0 else (-Real.log n : ℂ) ^ j

@[simp] theorem zetaJetFullCoeff_zero (j : ℕ) : zetaJetFullCoeff j 0 = 0 := by
  simp [zetaJetFullCoeff]

theorem zetaJetFullCoeff_zero_order : zetaJetFullCoeff 0 = zetaValueCoeff := by
  funext n
  simp [zetaJetFullCoeff, zetaValueCoeff]

theorem zetaJetFullCoeff_positive_order (j : ℕ) (hj : 0 < j) :
    zetaJetFullCoeff j = (-1 : ℂ) ^ j • ⇑(zetaJetA j) := by
  funext n
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · simp [zetaJetFullCoeff, zetaJetA_apply, hj.ne']
  · simp only [zetaJetFullCoeff,
      show n + 1 + 1 ≠ 0 by omega, if_false, Pi.smul_apply, smul_eq_mul,
      zetaJetA_apply, show 2 ≤ n + 1 + 1 by omega, if_true]
    push_cast
    rw [neg_pow]

theorem zetaJetFullCoeff_LSeriesSummable (j : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (zetaJetFullCoeff j) s := by
  rcases j.eq_zero_or_pos with rfl | hj
  · rw [zetaJetFullCoeff_zero_order]
    exact (LSeriesSummable_congr s
      (fun {_} hn => zetaValueCoeff_eq_one hn)).mpr
        (LSeriesSummable_one_iff.mpr hs)
  · rw [zetaJetFullCoeff_positive_order j hj]
    exact (zetaJetA_LSeriesSummable j hs).smul _

def inverseNatPowerCoeff (c : ℕ → ℂ) (k n : ℕ) : ℂ :=
  c n * ((n : ℂ)⁻¹) ^ k

theorem inverseNatPowerCoeff_term (c : ℕ → ℂ) (k n : ℕ) (s : ℂ) :
    LSeries.term (inverseNatPowerCoeff c k) s n =
      LSeries.term c (s + k) n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries_term_add_nat]
    rw [LSeries.term_of_ne_zero hn.ne']
    rw [LSeries.term_of_ne_zero (f := c) hn.ne']
    simp only [inverseNatPowerCoeff]
    ring

theorem inverseNatPowerCoeff_LSeriesSummable (c : ℕ → ℂ) (k : ℕ) (s : ℂ) :
    LSeriesSummable (inverseNatPowerCoeff c k) s ↔
      LSeriesSummable c (s + k) :=
  summable_congr (fun n => inverseNatPowerCoeff_term c k n s)

theorem LSeries_inverseNatPowerCoeff (c : ℕ → ℂ) (k : ℕ) (s : ℂ) :
    LSeries (inverseNatPowerCoeff c k) s = LSeries c (s + k) :=
  tsum_congr (fun n => inverseNatPowerCoeff_term c k n s)

def zetaJetInversePowerCoeff (j k : ℕ) : ArithmeticFunction ℂ where
  toFun := inverseNatPowerCoeff (zetaJetFullCoeff j) k
  map_zero' := by simp [inverseNatPowerCoeff]

theorem zetaJetInversePowerCoeff_LSeriesSummable (j k : ℕ) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (⇑(zetaJetInversePowerCoeff j k)) s := by
  rw [show ⇑(zetaJetInversePowerCoeff j k) =
      inverseNatPowerCoeff (zetaJetFullCoeff j) k by rfl,
    inverseNatPowerCoeff_LSeriesSummable]
  apply zetaJetFullCoeff_LSeriesSummable
  rw [Complex.add_re, Complex.natCast_re]
  have hk : (0 : ℝ) ≤ k := by positivity
  linarith

theorem LSeries_zetaJetFullCoeff_eq_iteratedDeriv (j : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (zetaJetFullCoeff j) s = iteratedDeriv j riemannZeta s := by
  rcases j.eq_zero_or_pos with rfl | hj
  · rw [zetaJetFullCoeff_zero_order,
      LSeries_zetaValueCoeff_eq_riemannZeta hs]
    rfl
  · rw [zetaJetFullCoeff_positive_order j hj, LSeries_smul]
    exact (iteratedDeriv_riemannZeta_eq_signed_LSeries j hj hs).symm

def gammaZetaJetEntryPolynomial {r q : ℕ} (shift : Fin r → ℂ)
    (mult : Fin r → ℕ) (h j : Fin q) (n : ℕ) : ℂ[X] :=
  if n = 0 then 0 else
    Polynomial.C ((((n : ℂ)⁻¹) ^ (h : ℕ)) * zetaJetFullCoeff (j : ℕ) n) *
      (gammaJetDirichletAmplitudePolynomial shift mult (n : ℂ)⁻¹).comp
        (Polynomial.X + Polynomial.C ((h : ℕ) : ℂ))

def gammaZetaJetEntryCoeff {r q : ℕ} (shift : Fin r → ℂ)
    (mult : Fin r → ℕ) (h j : Fin q) : ArithmeticFunction ℂ[X] where
  toFun := gammaZetaJetEntryPolynomial shift mult h j
  map_zero' := by simp [gammaZetaJetEntryPolynomial]

def gammaZetaJetCoeffMatrix {r q : ℕ} (shift : Fin r → ℂ)
    (mult : Fin r → ℕ) :
    Matrix (Fin q) (Fin q) (ArithmeticFunction ℂ[X]) :=
  fun h j => gammaZetaJetEntryCoeff shift mult h j

def gammaZetaJetDetCoeff {r q : ℕ} (shift : Fin r → ℂ)
    (mult : Fin r → ℕ) : ArithmeticFunction ℂ[X] :=
  (gammaZetaJetCoeffMatrix (q := q) shift mult).det

theorem gammaJetDirichletAmplitudePolynomial_comp_add_coeff_top {r : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) (T h : ℂ) :
    ((gammaJetDirichletAmplitudePolynomial shift mult T).comp
      (Polynomial.X + Polynomial.C h)).coeff (gammaJetOrder mult) =
        (-1 : ℂ) ^ gammaJetOrder mult := by
  let P := gammaJetDirichletAmplitudePolynomial shift mult T
  let Q := Polynomial.X + Polynomial.C h
  have hPdeg : P.natDegree ≤ gammaJetOrder mult :=
    gammaJetDirichletAmplitudePolynomial_degree_le shift mult T
  have hPcoeff : P.coeff (gammaJetOrder mult) = (-1 : ℂ) ^ gammaJetOrder mult :=
    gammaJetDirichletAmplitudePolynomial_topCoeff shift mult T
  have hPne : P.coeff (gammaJetOrder mult) ≠ 0 := by
    rw [hPcoeff]
    exact pow_ne_zero _ (by norm_num)
  have hPnat : P.natDegree = gammaJetOrder mult :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hPdeg hPne
  have hQmonic : Q.Monic := Polynomial.monic_X_add_C h
  have hQnat : Q.natDegree = 1 := Polynomial.natDegree_X_add_C h
  have hcompnat : (P.comp Q).natDegree = gammaJetOrder mult := by
    rw [Polynomial.natDegree_comp, hPnat, hQnat, mul_one]
  calc
    (P.comp Q).coeff (gammaJetOrder mult) = (P.comp Q).leadingCoeff := by
      rw [← hcompnat, Polynomial.coeff_natDegree]
    _ = P.leadingCoeff * Q.leadingCoeff ^ P.natDegree :=
      Polynomial.leadingCoeff_comp (by simp [hQnat])
    _ = P.leadingCoeff := by rw [hQmonic.leadingCoeff, one_pow, mul_one]
    _ = P.coeff (gammaJetOrder mult) := by
      rw [← hPnat, Polynomial.coeff_natDegree]
    _ = (-1 : ℂ) ^ gammaJetOrder mult := hPcoeff

theorem gammaZetaJetEntryPolynomial_eval {r q : ℕ} (shift : Fin r → ℂ)
    (mult : Fin r → ℕ) (h j : Fin q) (n : ℕ) (x : ℂ) :
    (gammaZetaJetEntryPolynomial shift mult h j n).eval x =
      if n = 0 then 0 else
        (((n : ℂ)⁻¹) ^ (h : ℕ)) * zetaJetFullCoeff (j : ℕ) n *
          gammaJetDirichletAmplitude (x + (h : ℕ)) shift mult (n : ℂ)⁻¹ := by
  by_cases hn : n = 0
  · subst n
    simp [gammaZetaJetEntryPolynomial]
  · rw [gammaZetaJetEntryPolynomial, if_neg hn, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_comp]
    simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    rw [gammaJetDirichletAmplitudePolynomial_eval]
    simp [hn]

theorem gammaZetaJetEntryPolynomial_natDegree_le {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) (h j : Fin q) (n : ℕ) :
    (gammaZetaJetEntryPolynomial shift mult h j n).natDegree ≤ gammaJetOrder mult := by
  by_cases hn : n = 0
  · subst n
    simp [gammaZetaJetEntryPolynomial]
  · rw [gammaZetaJetEntryPolynomial, if_neg hn]
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    calc
      ((gammaJetDirichletAmplitudePolynomial shift mult (n : ℂ)⁻¹).comp
        (Polynomial.X + Polynomial.C ((h : ℕ) : ℂ))).natDegree
          ≤ (gammaJetDirichletAmplitudePolynomial shift mult (n : ℂ)⁻¹).natDegree *
              (Polynomial.X + Polynomial.C ((h : ℕ) : ℂ)).natDegree :=
            Polynomial.natDegree_comp_le
      _ = (gammaJetDirichletAmplitudePolynomial shift mult (n : ℂ)⁻¹).natDegree := by
        rw [Polynomial.natDegree_X_add_C, mul_one]
      _ ≤ gammaJetOrder mult := by
        exact gammaJetDirichletAmplitudePolynomial_degree_le shift mult (n : ℂ)⁻¹

theorem gammaZetaJetEntryPolynomial_coeff_top {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) (h j : Fin q) (n : ℕ) :
    (gammaZetaJetEntryPolynomial shift mult h j n).coeff (gammaJetOrder mult) =
      if n = 0 then 0 else
        (((n : ℂ)⁻¹) ^ (h : ℕ)) * zetaJetFullCoeff (j : ℕ) n *
          (-1 : ℂ) ^ gammaJetOrder mult := by
  by_cases hn : n = 0
  · subst n
    simp [gammaZetaJetEntryPolynomial]
  · rw [gammaZetaJetEntryPolynomial, if_neg hn, Polynomial.coeff_C_mul,
      gammaJetDirichletAmplitudePolynomial_comp_add_coeff_top]
    simp [hn]

theorem polynomial_det_natDegree_le {q N : ℕ}
    (M : Matrix (Fin q) (Fin q) ℂ[X])
    (hdeg : ∀ i j, (M i j).natDegree ≤ N) :
    M.det.natDegree ≤ q * N := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ hσ
  refine (Polynomial.natDegree_smul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le Finset.univ (fun i => M (σ i) i)).trans ?_
  calc
    (∑ i ∈ Finset.univ, (M (σ i) i).natDegree) ≤
        ∑ i ∈ Finset.univ, N := Finset.sum_le_sum (fun i hi => hdeg (σ i) i)
    _ = q * N := by simp

theorem polynomial_det_coeff_top {q N : ℕ}
    (M : Matrix (Fin q) (Fin q) ℂ[X])
    (hdeg : ∀ i j, (M i j).natDegree ≤ N) :
    M.det.coeff (q * N) = Matrix.det (fun i j => (M i j).coeff N) := by
  rw [Matrix.det_apply', Polynomial.finsetSum_coeff, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ hσ
  change (Polynomial.C ((↑(↑(Equiv.Perm.sign σ) : ℤ) : ℂ)) *
      ∏ i, M (σ i) i).coeff (q * N) =
    (↑(↑(Equiv.Perm.sign σ) : ℤ) : ℂ) * ∏ i, (M (σ i) i).coeff N
  rw [Polynomial.coeff_C_mul]
  congr 1
  simpa using Polynomial.coeff_prod_of_natDegree_le
    (s := (Finset.univ : Finset (Fin q))) (fun i => M (σ i) i) N
      (fun i hi => hdeg (σ i) i)

theorem gammaZetaJetDetCoeff_natDegree_le {r q : ℕ} (shift : Fin r → ℂ)
    (mult : Fin r → ℕ) (n : ℕ) :
    ((gammaZetaJetDetCoeff (q := q) shift mult) n).natDegree ≤
      q * gammaJetOrder mult := by
  rw [gammaZetaJetDetCoeff, arithmeticFunction_det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  apply polynomial_det_natDegree_le
  intro i j
  exact gammaZetaJetEntryPolynomial_natDegree_le shift mult i j (d.factors j)

theorem gammaZetaJet_factorMatrix_det_eq_zero_of_not_injective {r q n : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) (d : DirichletFactorData q n)
    (hn : 0 < n) (hnot : ¬Function.Injective d.factors) :
    Matrix.det (fun i j =>
      gammaZetaJetEntryPolynomial shift mult i j (d.factors j)) = 0 := by
  rw [Function.not_injective_iff] at hnot
  obtain ⟨j, k, hjkfac, hjkne⟩ := hnot
  let B : Matrix (Fin q) (Fin q) ℂ[X] := fun i j =>
    Polynomial.C ((((d.factors j : ℕ) : ℂ)⁻¹) ^ (i : ℕ)) *
      (gammaJetDirichletAmplitudePolynomial shift mult
        ((d.factors j : ℕ) : ℂ)⁻¹).comp
          (Polynomial.X + Polynomial.C ((i : ℕ) : ℂ))
  let c : Fin q → ℂ[X] := fun j =>
    Polynomial.C (zetaJetFullCoeff (j : ℕ) (d.factors j))
  have hmatrix : (fun i j =>
      gammaZetaJetEntryPolynomial shift mult i j (d.factors j)) =
      Matrix.of (fun i j => c j * B i j) := by
    ext i j
    have hfacne : d.factors j ≠ 0 := (d.factor_pos hn j).ne'
    rw [gammaZetaJetEntryPolynomial, if_neg hfacne]
    simp only [B, c, Matrix.of_apply, Polynomial.C_mul]
    ring_nf
  rw [hmatrix, Matrix.det_mul_row]
  rw [Matrix.det_zero_of_column_eq hjkne]
  · simp
  · intro i
    simp only [B]
    rw [hjkfac]

theorem gammaZetaJetDetCoeff_eq_zero_of_lt_factorial {r q n : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) (hn : n < q.factorial) :
    (gammaZetaJetDetCoeff (q := q) shift mult) n = 0 := by
  rcases n.eq_zero_or_pos with rfl | hnpos
  · exact (gammaZetaJetDetCoeff (q := q) shift mult).map_zero
  · rw [gammaZetaJetDetCoeff, arithmeticFunction_det_apply]
    apply Finset.sum_eq_zero
    intro d hd
    apply gammaZetaJet_factorMatrix_det_eq_zero_of_not_injective shift mult d hnpos
    intro hinj
    have hle := factorial_le_fin_prod_of_injective d.factors
      (fun i => d.factor_pos hnpos i) hinj
    rw [d.prod_factors] at hle
    omega

def dirichletInitialTopMatrix (q N : ℕ) (σ : Equiv.Perm (Fin q)) :
    Matrix (Fin q) (Fin q) ℂ := fun i j =>
  (dirichletReciprocalNode (σ j) : ℂ) ^ (i : ℕ) *
    (dirichletLogNode (σ j) : ℂ) ^ (j : ℕ) * (-1 : ℂ) ^ N

theorem gammaZetaJetEntryPolynomial_initial_coeff_top {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) (σ : Equiv.Perm (Fin q)) (i j : Fin q) :
    (gammaZetaJetEntryPolynomial shift mult i j
      ((initialDirichletFactorData q σ).factors j)).coeff (gammaJetOrder mult) =
        dirichletInitialTopMatrix q (gammaJetOrder mult) σ i j := by
  rw [initialDirichletFactorData_factors]
  rw [gammaZetaJetEntryPolynomial_coeff_top]
  rw [if_neg (by omega : (σ j : ℕ) + 1 ≠ 0)]
  simp only [zetaJetFullCoeff, if_neg (by omega : (σ j : ℕ) + 1 ≠ 0),
    dirichletInitialTopMatrix, dirichletReciprocalNode, dirichletLogNode]
  push_cast
  ring

theorem det_dirichletInitialTopMatrix (q N : ℕ) (σ : Equiv.Perm (Fin q)) :
    (dirichletInitialTopMatrix q N σ).det =
      (-1 : ℂ) ^ (q * N) * (↑(↑(Equiv.Perm.sign σ) : ℤ) : ℂ) *
        (Matrix.vandermonde
          (fun i : Fin q => (dirichletReciprocalNode i : ℂ))).det *
          ∏ j, (dirichletLogNode (σ j) : ℂ) ^ (j : ℕ) := by
  let V : Matrix (Fin q) (Fin q) ℂ :=
    (Matrix.vandermonde
      (fun i : Fin q => (dirichletReciprocalNode i : ℂ))).transpose
  let c : Fin q → ℂ := fun j =>
    (dirichletLogNode (σ j) : ℂ) ^ (j : ℕ) * (-1 : ℂ) ^ N
  have hmatrix : dirichletInitialTopMatrix q N σ =
      Matrix.of (fun i j => c j * (V.submatrix id σ) i j) := by
    ext i j
    simp [dirichletInitialTopMatrix, V, c, Matrix.vandermonde,
      Matrix.transpose, Matrix.submatrix]
    ring
  rw [hmatrix, Matrix.det_mul_row, Matrix.det_permute']
  dsimp only [V]
  rw [Matrix.det_transpose]
  have hprod : (∏ j : Fin q,
      (dirichletLogNode (σ j) : ℂ) ^ (j : ℕ) * (-1 : ℂ) ^ N) =
      (∏ j : Fin q, (dirichletLogNode (σ j) : ℂ) ^ (j : ℕ)) *
        (-1 : ℂ) ^ (q * N) := by
    change (∏ j ∈ (Finset.univ : Finset (Fin q)),
      (dirichletLogNode (σ j) : ℂ) ^ (j : ℕ) * (-1 : ℂ) ^ N) = _
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_mul]
    congr 2
    exact Nat.mul_comm N q
  rw [show (∏ j, c j) =
      ∏ j : Fin q, (dirichletLogNode (σ j) : ℂ) ^ (j : ℕ) * (-1 : ℂ) ^ N by
        rfl, hprod]
  ring

theorem sum_det_dirichletInitialTopMatrix (q N : ℕ) :
    (∑ σ : Equiv.Perm (Fin q), (dirichletInitialTopMatrix q N σ).det) =
      (-1 : ℂ) ^ (q * N) * (dirichletFlagVandermonde q : ℂ) := by
  simp_rw [det_dirichletInitialTopMatrix]
  have hlogsum : (∑ σ : Equiv.Perm (Fin q),
      (↑(↑(Equiv.Perm.sign σ) : ℤ) : ℂ) *
        ∏ j, (dirichletLogNode (σ j) : ℂ) ^ (j : ℕ)) =
      (Matrix.vandermonde
        (fun i : Fin q => (dirichletLogNode i : ℂ))).det := by
    symm
    exact Matrix.det_apply' _
  rw [show (∑ σ : Equiv.Perm (Fin q),
      (-1 : ℂ) ^ (q * N) * (↑(↑(Equiv.Perm.sign σ) : ℤ) : ℂ) *
        (Matrix.vandermonde
          (fun i : Fin q => (dirichletReciprocalNode i : ℂ))).det *
          ∏ j, (dirichletLogNode (σ j) : ℂ) ^ (j : ℕ)) =
      (-1 : ℂ) ^ (q * N) *
        (Matrix.vandermonde
          (fun i : Fin q => (dirichletReciprocalNode i : ℂ))).det *
          ∑ σ : Equiv.Perm (Fin q),
            (↑(↑(Equiv.Perm.sign σ) : ℤ) : ℂ) *
              ∏ j, (dirichletLogNode (σ j) : ℂ) ^ (j : ℕ) by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro σ hσ
      ring]
  rw [hlogsum]
  have hrecip :
      (Matrix.vandermonde
        (fun i : Fin q => (dirichletReciprocalNode i : ℂ))).det =
      ((Matrix.vandermonde
        (dirichletReciprocalNode (q := q))).det : ℂ) := by
    calc
      _ = (Complex.ofRealHom.mapMatrix
          (Matrix.vandermonde (dirichletReciprocalNode (q := q)))).det := by
        congr 1
        ext i j
        simp [Matrix.vandermonde]
      _ = Complex.ofRealHom
          (Matrix.vandermonde (dirichletReciprocalNode (q := q))).det :=
        (Complex.ofRealHom.map_det _).symm
      _ = _ := rfl
  have hlog :
      (Matrix.vandermonde
        (fun i : Fin q => (dirichletLogNode i : ℂ))).det =
      ((Matrix.vandermonde (dirichletLogNode (q := q))).det : ℂ) := by
    calc
      _ = (Complex.ofRealHom.mapMatrix
          (Matrix.vandermonde (dirichletLogNode (q := q)))).det := by
        congr 1
        ext i j
        simp [Matrix.vandermonde]
      _ = Complex.ofRealHom
          (Matrix.vandermonde (dirichletLogNode (q := q))).det :=
        (Complex.ofRealHom.map_det _).symm
      _ = _ := rfl
  rw [hrecip, hlog]
  push_cast [dirichletFlagVandermonde]
  ring

theorem gammaZetaJet_initialFactorMatrix_coeff_top {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) (σ : Equiv.Perm (Fin q)) :
    (Matrix.det (fun i j => gammaZetaJetEntryPolynomial shift mult i j
      ((initialDirichletFactorData q σ).factors j))).coeff
        (q * gammaJetOrder mult) =
      (dirichletInitialTopMatrix q (gammaJetOrder mult) σ).det := by
  rw [polynomial_det_coeff_top]
  · congr 1
    ext i j
    exact gammaZetaJetEntryPolynomial_initial_coeff_top shift mult σ i j
  · intro i j
    exact gammaZetaJetEntryPolynomial_natDegree_le shift mult i j _

theorem gammaZetaJetDetCoeff_factorial_coeff_top {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) :
    ((gammaZetaJetDetCoeff (q := q) shift mult) q.factorial).coeff
        (q * gammaJetOrder mult) =
      (-1 : ℂ) ^ (q * gammaJetOrder mult) *
        (dirichletFlagVandermonde q : ℂ) := by
  classical
  rw [gammaZetaJetDetCoeff, arithmeticFunction_det_apply,
    Polynomial.finsetSum_coeff]
  let f : DirichletFactorData q q.factorial → ℂ := fun d =>
    (Matrix.det (fun i j => gammaZetaJetEntryPolynomial shift mult i j
      (d.factors j))).coeff (q * gammaJetOrder mult)
  change (∑ d, f d) = _
  have hnoninj (d : DirichletFactorData q q.factorial)
      (hd : ¬Function.Injective d.factors) : f d = 0 := by
    simp only [f]
    rw [gammaZetaJet_factorMatrix_det_eq_zero_of_not_injective shift mult d
      (Nat.factorial_pos q) hd]
    simp
  calc
    (∑ d, f d) = ∑ d, if Function.Injective d.factors then f d else 0 := by
      apply Finset.sum_congr rfl
      intro d hd
      split_ifs with hinj
      · rfl
      · exact hnoninj d hinj
    _ = ∑ d ∈ (Finset.univ.filter
          (fun d : DirichletFactorData q q.factorial =>
            Function.Injective d.factors)), f d := by
      rw [Finset.sum_filter]
    _ = ∑ d : {d : DirichletFactorData q q.factorial //
          Function.Injective d.factors}, f d.1 := by
      exact Finset.sum_subtype
        (p := fun d : DirichletFactorData q q.factorial =>
          Function.Injective d.factors)
        (Finset.univ.filter fun d : DirichletFactorData q q.factorial =>
          Function.Injective d.factors) (fun d => by simp) f
    _ = ∑ σ : Equiv.Perm (Fin q), f (initialDirichletFactorData q σ) := by
      symm
      apply Fintype.sum_equiv (initialDirichletFactorDataEquiv q)
      intro σ
      rfl
    _ = ∑ σ : Equiv.Perm (Fin q),
          (dirichletInitialTopMatrix q (gammaJetOrder mult) σ).det := by
      apply Finset.sum_congr rfl
      intro σ hσ
      exact gammaZetaJet_initialFactorMatrix_coeff_top shift mult σ
    _ = _ := sum_det_dirichletInitialTopMatrix q (gammaJetOrder mult)

/-- Apply a coefficient ring homomorphism pointwise to an arithmetic function. -/
def mapArithmeticFunctionRingHom {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) : ArithmeticFunction R →+* ArithmeticFunction S where
  toFun f :=
    { toFun := fun n => φ (f n)
      map_zero' := by simp }
  map_one' := by
    ext n
    by_cases hn : n = 1 <;> simp [ArithmeticFunction.one_apply, hn]
  map_mul' f g := by
    ext n
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · simp only [ArithmeticFunction.mul_apply, map_sum, map_mul]
      rfl
  map_zero' := by
    ext n
    simp
  map_add' f g := by
    ext n
    simp

@[simp] theorem mapArithmeticFunctionRingHom_apply {R S : Type*}
    [CommRing R] [CommRing S] (φ : R →+* S) (f : ArithmeticFunction R) (n : ℕ) :
    mapArithmeticFunctionRingHom φ f n = φ (f n) := rfl

def gammaZetaJetEntryEvalCoeff {r q : ℕ} (shift : Fin r → ℂ)
    (mult : Fin r → ℕ) (h j : Fin q) (x : ℂ) : ArithmeticFunction ℂ :=
  mapArithmeticFunctionRingHom (Polynomial.evalRingHom x)
    (gammaZetaJetEntryCoeff shift mult h j)

def gammaZetaJetEvalCoeffMatrix {r q : ℕ} (shift : Fin r → ℂ)
    (mult : Fin r → ℕ) (x : ℂ) :
    Matrix (Fin q) (Fin q) (ArithmeticFunction ℂ) :=
  fun h j => gammaZetaJetEntryEvalCoeff shift mult h j x

theorem gammaZetaJetEntryEvalCoeff_eq_sum {r q : ℕ} (shift : Fin r → ℂ)
    (mult : Fin r → ℕ) (h j : Fin q) (x : ℂ) :
    gammaZetaJetEntryEvalCoeff shift mult h j x =
      ∑ k ∈ Finset.range (gammaJetOrder mult + 1),
        gammaJetAnnihilatorCoeff (x + (h : ℕ)) shift mult k •
          zetaJetInversePowerCoeff (j : ℕ) ((h : ℕ) + k) := by
  ext n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [gammaZetaJetEntryEvalCoeff]
  · rw [gammaZetaJetEntryEvalCoeff, mapArithmeticFunctionRingHom_apply]
    change (gammaZetaJetEntryPolynomial shift mult h j n).eval x = _
    rw [gammaZetaJetEntryPolynomial_eval, if_neg hn.ne']
    rw [gammaJetDirichletAmplitude]
    let ev : ArithmeticFunction ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun f => f n
        map_add' := fun _ _ => rfl
        map_smul' := fun c f => by simp }
    change _ = ev (∑ k ∈ Finset.range (gammaJetOrder mult + 1),
      gammaJetAnnihilatorCoeff (x + (h : ℕ)) shift mult k •
        zetaJetInversePowerCoeff (j : ℕ) ((h : ℕ) + k))
    rw [map_sum]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [ev.map_smul]
    change _ = gammaJetAnnihilatorCoeff (x + (h : ℕ)) shift mult k *
      inverseNatPowerCoeff (zetaJetFullCoeff (j : ℕ)) ((h : ℕ) + k) n
    simp only [inverseNatPowerCoeff]
    rw [pow_add]
    ring

theorem gammaZetaJetEntryEvalCoeff_LSeriesSummable {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) (h j : Fin q) (x : ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (⇑(gammaZetaJetEntryEvalCoeff shift mult h j x)) s := by
  rw [gammaZetaJetEntryEvalCoeff_eq_sum]
  rw [coe_finsetSum_arithmeticFunction]
  apply LSeriesSummable.sum
  intro k hk
  rw [show ⇑(gammaJetAnnihilatorCoeff (x + (h : ℕ)) shift mult k •
      zetaJetInversePowerCoeff (j : ℕ) ((h : ℕ) + k)) =
      gammaJetAnnihilatorCoeff (x + (h : ℕ)) shift mult k •
        ⇑(zetaJetInversePowerCoeff (j : ℕ) ((h : ℕ) + k)) by
    funext n
    simp]
  exact (zetaJetInversePowerCoeff_LSeriesSummable _ _ hs).smul _

theorem gammaZetaJetEntryEvalCoeff_LSeries_eq {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) (h j : Fin q)
    {x : ℂ} (hx : 1 < x.re) :
    LSeries (⇑(gammaZetaJetEntryEvalCoeff shift mult h j x)) x =
      gammaJetAnnihilator (x + (h : ℕ)) shift mult
        (fun z => iteratedDeriv (j : ℕ) riemannZeta z) := by
  rw [gammaZetaJetEntryEvalCoeff_eq_sum]
  rw [coe_finsetSum_arithmeticFunction]
  rw [LSeries_sum]
  · rw [gammaJetAnnihilator]
    apply Finset.sum_congr rfl
    intro k hk
    rw [show ⇑(gammaJetAnnihilatorCoeff (x + (h : ℕ)) shift mult k •
        zetaJetInversePowerCoeff (j : ℕ) ((h : ℕ) + k)) =
        gammaJetAnnihilatorCoeff (x + (h : ℕ)) shift mult k •
          ⇑(zetaJetInversePowerCoeff (j : ℕ) ((h : ℕ) + k)) by
      funext n
      simp, LSeries_smul]
    change _ * LSeries
        (inverseNatPowerCoeff (zetaJetFullCoeff (j : ℕ)) ((h : ℕ) + k)) x = _
    rw [LSeries_inverseNatPowerCoeff]
    rw [LSeries_zetaJetFullCoeff_eq_iteratedDeriv]
    · congr 2
      push_cast
      ring
    · rw [Complex.add_re, Complex.natCast_re]
      have hhk : (0 : ℝ) ≤ (h : ℕ) + k := by positivity
      linarith
  · intro k hk
    rw [show ⇑(gammaJetAnnihilatorCoeff (x + (h : ℕ)) shift mult k •
        zetaJetInversePowerCoeff (j : ℕ) ((h : ℕ) + k)) =
        gammaJetAnnihilatorCoeff (x + (h : ℕ)) shift mult k •
          ⇑(zetaJetInversePowerCoeff (j : ℕ) ((h : ℕ) + k)) by
      funext n
      simp]
    exact (zetaJetInversePowerCoeff_LSeriesSummable _ _ hx).smul _

theorem gammaZetaJetDetCoeff_eval {r q : ℕ} (shift : Fin r → ℂ)
    (mult : Fin r → ℕ) (x : ℂ) :
    mapArithmeticFunctionRingHom (Polynomial.evalRingHom x)
        (gammaZetaJetDetCoeff (q := q) shift mult) =
      (gammaZetaJetEvalCoeffMatrix (q := q) shift mult x).det := by
  exact (mapArithmeticFunctionRingHom (Polynomial.evalRingHom x)).map_det _

theorem gammaZetaJetDetCoeff_eval_LSeriesSummable {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) (x : ℂ)
    {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (fun n => ((gammaZetaJetDetCoeff (q := q) shift mult) n).eval x) s := by
  rw [show (fun n => ((gammaZetaJetDetCoeff (q := q) shift mult) n).eval x) =
      ⇑(mapArithmeticFunctionRingHom (Polynomial.evalRingHom x)
        (gammaZetaJetDetCoeff (q := q) shift mult)) by rfl]
  rw [gammaZetaJetDetCoeff_eval]
  apply arithmeticFunction_det_LSeriesSummable
  intro h j
  exact gammaZetaJetEntryEvalCoeff_LSeriesSummable shift mult h j x hs

theorem polynomialCoeffStream_LSeriesSummable_of_eval
    (P : ℕ → ℂ[X]) (d k : ℕ) (s : ℂ)
    (hdeg : ∀ n, (P n).natDegree ≤ d)
    (heval : ∀ x : ℂ, LSeriesSummable (fun n => (P n).eval x) s) :
    LSeriesSummable (polynomialCoeffStream P k) s := by
  classical
  let v : Fin (d + 1) → ℂ := fun i => (i : ℕ)
  have hv : Set.InjOn v (Finset.univ : Finset (Fin (d + 1))) := by
    intro i hi j hj hij
    apply Fin.ext
    change ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) at hij
    exact_mod_cast hij
  have hcoeff (n : ℕ) :
      (P n).coeff k = ∑ i : Fin (d + 1),
        (P n).eval (v i) *
          (Lagrange.basis Finset.univ v i).coeff k := by
    have hdegree : (P n).degree <
        ((Finset.univ : Finset (Fin (d + 1))).card : WithBot ℕ) := by
      rw [Finset.card_univ, Fintype.card_fin]
      calc
        (P n).degree ≤ ((P n).natDegree : WithBot ℕ) :=
          Polynomial.degree_le_natDegree
        _ ≤ (d : WithBot ℕ) := WithBot.coe_le_coe.mpr (hdeg n)
        _ < ((d + 1 : ℕ) : WithBot ℕ) := by norm_cast; omega
    have hinterp := Lagrange.eq_interpolate hv hdegree
    have hc := congrArg (fun Q : ℂ[X] => Q.coeff k) hinterp
    rw [Lagrange.interpolate_apply] at hc
    change (P n).coeff k = (Polynomial.lcoeff ℂ k)
      (∑ i, Polynomial.C ((P n).eval (v i)) *
        Lagrange.basis Finset.univ v i) at hc
    rw [map_sum] at hc
    change (P n).coeff k = ∑ i,
      (Polynomial.C ((P n).eval (v i)) *
        Lagrange.basis Finset.univ v i).coeff k at hc
    simp only [Polynomial.coeff_C_mul] at hc
    simpa [mul_comm] using hc
  have hstream : polynomialCoeffStream P k =
      ∑ i ∈ (Finset.univ : Finset (Fin (d + 1))),
        (Lagrange.basis Finset.univ v i).coeff k •
          (fun n => (P n).eval (v i)) := by
    funext n
    rw [polynomialCoeffStream, hcoeff]
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    simp
    ring
  rw [hstream]
  apply LSeriesSummable.sum
  intro i hi
  exact (heval (v i)).smul _

theorem gammaZetaJetDetCoeff_polynomialCoeff_LSeriesSummable {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable
      (polynomialCoeffStream
        (fun n => (gammaZetaJetDetCoeff (q := q) shift mult) n) k) s := by
  apply polynomialCoeffStream_LSeriesSummable_of_eval _
    (q * gammaJetOrder mult) k s
  · exact gammaZetaJetDetCoeff_natDegree_le shift mult
  · intro x
    exact gammaZetaJetDetCoeff_eval_LSeriesSummable shift mult x hs

theorem gammaZetaJetResidualDirichlet_normalized_tendsto {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) :
    Tendsto (fun x : ℝ =>
      (q.factorial : ℂ) ^ (x : ℂ) *
          LSeries
            (fun n => ((gammaZetaJetDetCoeff (q := q) shift mult) n).eval (x : ℂ))
            (x : ℂ) /
        (x : ℂ) ^ (q * gammaJetOrder mult))
      atTop (nhds ((-1 : ℂ) ^ (q * gammaJetOrder mult) *
        (dirichletFlagVandermonde q : ℂ))) := by
  let P : ℕ → ℂ[X] := fun n =>
    (gammaZetaJetDetCoeff (q := q) shift mult) n
  let d := q * gammaJetOrder mult
  let a := q.factorial - 1
  have hfac : 0 < q.factorial := Nat.factorial_pos q
  have ha : a + 1 = q.factorial := by
    dsimp only [a]
    omega
  have hzero : ∀ n ≤ a, P n = 0 := by
    intro n hn
    exact gammaZetaJetDetCoeff_eq_zero_of_lt_factorial shift mult (by
      dsimp only [a] at hn
      omega)
  have hlim := polynomialCoeffLSeries_firstCoeff_tendsto P d a 2
    (fun n => gammaZetaJetDetCoeff_natDegree_le shift mult n)
    hzero
    (fun k hk => gammaZetaJetDetCoeff_polynomialCoeff_LSeriesSummable
      shift mult k (by norm_num))
  have hac : (a : ℂ) + 1 = (q.factorial : ℂ) := by
    exact_mod_cast ha
  rw [hac] at hlim
  rw [ha] at hlim
  rw [show (P q.factorial).coeff d =
      (-1 : ℂ) ^ (q * gammaJetOrder mult) *
        (dirichletFlagVandermonde q : ℂ) by
    exact gammaZetaJetDetCoeff_factorial_coeff_top shift mult] at hlim
  simpa only [P, d] using hlim

theorem gammaZetaJetDetCoeff_LSeries_eq_residualDet {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) {x : ℂ} (hx : 1 < x.re) :
    LSeries
        (fun n => ((gammaZetaJetDetCoeff (q := q) shift mult) n).eval x) x =
      (gammaZetaJetResidualMatrix x shift mult
        (fun (j : Fin q) z => iteratedDeriv (j : ℕ) riemannZeta z)).det := by
  rw [show (fun n => ((gammaZetaJetDetCoeff (q := q) shift mult) n).eval x) =
      ⇑(mapArithmeticFunctionRingHom (Polynomial.evalRingHom x)
        (gammaZetaJetDetCoeff (q := q) shift mult)) by rfl]
  rw [gammaZetaJetDetCoeff_eval]
  rw [arithmeticFunction_det_LSeries]
  · congr 1
    ext h j
    exact gammaZetaJetEntryEvalCoeff_LSeries_eq shift mult h j hx
  · intro h j
    exact gammaZetaJetEntryEvalCoeff_LSeriesSummable shift mult h j x hx

/-- Equation (D4), in exact normalized-limit form. -/
theorem gammaZetaJetResidualMatrix_normalized_tendsto {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) :
    Tendsto (fun x : ℝ =>
      (q.factorial : ℂ) ^ (x : ℂ) *
          (gammaZetaJetResidualMatrix (x : ℂ) shift mult
            (fun (j : Fin q) z => iteratedDeriv (j : ℕ) riemannZeta z)).det /
        (x : ℂ) ^ (q * gammaJetOrder mult))
      atTop (nhds ((-1 : ℂ) ^ (q * gammaJetOrder mult) *
        (dirichletFlagVandermonde q : ℂ))) := by
  apply (gammaZetaJetResidualDirichlet_normalized_tendsto shift mult).congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  rw [gammaZetaJetDetCoeff_LSeries_eq_residualDet shift mult (by simpa using hx)]

theorem gammaZetaJetResidualMatrix_det_ne_zero_eventually {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ) :
    ∀ᶠ x : ℝ in atTop,
      (gammaZetaJetResidualMatrix (x : ℂ) shift mult
        (fun (j : Fin q) z => iteratedDeriv (j : ℕ) riemannZeta z)).det ≠ 0 := by
  let target : ℂ := (-1 : ℂ) ^ (q * gammaJetOrder mult) *
    (dirichletFlagVandermonde q : ℂ)
  have htarget : target ≠ 0 := by
    apply mul_ne_zero (pow_ne_zero _ (by norm_num))
    exact Complex.ofReal_ne_zero.mpr
      (ne_of_gt (dirichletFlagVandermonde_pos q))
  have hlim := gammaZetaJetResidualMatrix_normalized_tendsto (q := q) shift mult
  have hnorm := hlim.norm
  have hpos : 0 < ‖target‖ := norm_pos_iff.mpr htarget
  have hevent := hnorm.eventually (eventually_gt_nhds (half_lt_self hpos))
  filter_upwards [hevent] with x hx
  intro hzero
  change ‖(q.factorial : ℂ) ^ (x : ℂ) *
      (gammaZetaJetResidualMatrix (x : ℂ) shift mult
        (fun (j : Fin q) z => iteratedDeriv (j : ℕ) riemannZeta z)).det /
        (x : ℂ) ^ (q * gammaJetOrder mult)‖ > ‖target‖ / 2 at hx
  rw [hzero, mul_zero, zero_div, norm_zero] at hx
  linarith

theorem gammaShift_pole_free_eventually {r : ℕ} (shift : Fin r → ℂ) :
    ∀ᶠ x : ℝ in atTop, ∀ i (p : ℕ), (x : ℂ) + shift i ≠ -(p : ℂ) := by
  rw [eventually_all]
  intro i
  filter_upwards [eventually_gt_atTop (-(shift i).re)] with x hx
  intro p heq
  have hre := congrArg Complex.re heq
  simp only [Complex.add_re, Complex.ofReal_re, Complex.neg_re,
    Complex.natCast_re] at hre
  have hp : (0 : ℝ) ≤ p := by positivity
  linarith

theorem gammaJetAnnihilator_singleton_riemannZeta_normalized_tendsto
    (lambda : ℂ) :
    Tendsto (fun x : ℝ =>
      (riemannZeta ((x : ℂ) + 1) -
        ((x : ℂ) + lambda) * riemannZeta (x : ℂ)) / (x : ℂ))
      atTop (nhds (-1 : ℂ)) := by
  have hlim := gammaJetAnnihilator_riemannZeta_normalized_tendsto
    (singletonGammaShift lambda) singletonGammaMult
  rw [gammaJetOrder_singleton] at hlim
  norm_num at hlim
  apply hlim.congr'
  filter_upwards with x
  rw [gammaJetAnnihilator_singleton]

theorem gammaJetAnnihilator_pair_riemannZeta_normalized_tendsto
    (lambda1 lambda2 : ℂ) :
    Tendsto (fun x : ℝ =>
      (riemannZeta ((x : ℂ) + 2) -
          (2 * (x : ℂ) + lambda1 + lambda2 + 1) *
            riemannZeta ((x : ℂ) + 1) +
          ((x : ℂ) + lambda1) * ((x : ℂ) + lambda2) *
            riemannZeta (x : ℂ)) /
        (x : ℂ) ^ 2)
      atTop (nhds (1 : ℂ)) := by
  have hlim := gammaJetAnnihilator_riemannZeta_normalized_tendsto
    (pairGammaShift lambda1 lambda2) pairGammaMult
  rw [show (-1 : ℂ) ^ gammaJetOrder pairGammaMult = 1 by
    rw [gammaJetOrder_pair]
    norm_num] at hlim
  apply hlim.congr'
  filter_upwards with x
  rw [gammaJetAnnihilator_pair]
  rw [gammaJetOrder_pair]

theorem gammaJetAugmentedMatrix_LSeries_det_ne_zero_eventually {r : ℕ}
    (c : ℕ → ℂ) (a : ℕ) (hzero : ∀ m ≤ a, c m = 0) (ha : c (a + 1) ≠ 0)
    (hc : LSeries.abscissaOfAbsConv c < ⊤)
    (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (hshift : Function.Injective shift) :
    ∀ᶠ x : ℝ in atTop,
      (gammaJetAugmentedMatrix (x : ℂ) shift mult
        (fun z => LSeries c z)).det ≠ 0 := by
  filter_upwards [gammaJetAnnihilator_LSeries_ne_zero_eventually
      c a hzero ha hc shift mult,
    gammaShift_pole_free_eventually shift] with x hres hpole
  rw [← det_gammaJetAugmentedEliminatedMatrix,
    det_gammaJetAugmentedEliminatedMatrix_eq (x : ℂ) shift mult
      (fun z => LSeries c z) hpole]
  exact mul_ne_zero
    (det_confluentGammaShiftMatrix_ne_zero (x : ℂ) shift mult hshift hpole)
    hres

theorem gammaZetaJetMixedMatrix_det_ne_zero_eventually {r q : ℕ}
    (shift : Fin r → ℂ) (mult : Fin r → ℕ)
    (hshift : Function.Injective shift) :
    ∀ᶠ x : ℝ in atTop,
      (gammaZetaJetMixedMatrix (q := q) (x : ℂ) shift mult
        (fun (j : Fin q) z => iteratedDeriv (j : ℕ) riemannZeta z)).det ≠ 0 := by
  filter_upwards [gammaZetaJetResidualMatrix_det_ne_zero_eventually
      (q := q) shift mult, gammaShift_pole_free_eventually shift] with x hres hpole
  rw [det_gammaZetaJetMixedMatrix (x : ℂ) shift mult
    (fun (j : Fin q) z => iteratedDeriv (j : ℕ) riemannZeta z) hpole]
  exact mul_ne_zero
    (det_confluentGammaShiftMatrix_ne_zero (x : ℂ) shift mult hshift hpole)
    hres

end
end GaloisForLFunctions
