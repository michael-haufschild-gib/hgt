import GaloisForLFunctions.HTGeometry.HankelNormalizationPositivity

/-!
# Two-modulus log-coordinate Hessian

An inverse monomial becomes an exponential in logarithmic radius coordinates.  Its first
derivatives multiply it by the negative exponent vector, and its Hessian is the monomial times the
rank-one Gram matrix of that vector.  This formalizes the reusable calculus behind the
curvature-flux-torsion two-modulus potential.

Positive monomials therefore contribute positive-semidefinite Hessian blocks.  In the explicit
potential the flux Hessian is positive semidefinite, while the negative of the combined curvature
and torsion Hessian is positive semidefinite.  Along the isotropic ray their weights are `-8`,
`-10`, and `-6` respectively.
-/

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Monomial `coefficient * a1^-p * a2^-q` in logarithmic radius coordinates. -/
def logMonomial (coefficient p q x y : ℝ) : ℝ :=
  coefficient * Real.exp (-p * x - q * y)

/-- First logarithmic-radius derivative in the first coordinate. -/
def logMonomialDx (coefficient p q x y : ℝ) : ℝ :=
  -p * logMonomial coefficient p q x y

/-- First logarithmic-radius derivative in the second coordinate. -/
def logMonomialDy (coefficient p q x y : ℝ) : ℝ :=
  -q * logMonomial coefficient p q x y

/-- First diagonal entry of the logarithmic Hessian. -/
def logMonomialDxx (coefficient p q x y : ℝ) : ℝ :=
  p ^ (2 : ℕ) * logMonomial coefficient p q x y

/-- Mixed entry of the logarithmic Hessian. -/
def logMonomialDxy (coefficient p q x y : ℝ) : ℝ :=
  p * q * logMonomial coefficient p q x y

/-- Second diagonal entry of the logarithmic Hessian. -/
def logMonomialDyy (coefficient p q x y : ℝ) : ℝ :=
  q ^ (2 : ℕ) * logMonomial coefficient p q x y

/-- Exact first-coordinate derivative of a log monomial. -/
theorem logMonomial_hasDerivAt_fst (coefficient p q x y : ℝ) :
    HasDerivAt (fun u => logMonomial coefficient p q u y)
      (logMonomialDx coefficient p q x y) x := by
  have hinner : HasDerivAt (fun u : ℝ => -p * u - q * y) (-p) x := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id x).const_mul (-p)).sub_const (q * y)
  have h := ((Real.hasDerivAt_exp _).comp x hinner).const_mul coefficient
  simpa only [Function.comp_apply, logMonomial, logMonomialDx, neg_mul,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- Exact second-coordinate derivative of a log monomial. -/
theorem logMonomial_hasDerivAt_snd (coefficient p q x y : ℝ) :
    HasDerivAt (fun v => logMonomial coefficient p q x v)
      (logMonomialDy coefficient p q x y) y := by
  have hinner : HasDerivAt (fun v : ℝ => -p * x - q * v) (-q) y := by
    simpa only [id_eq, mul_one, sub_eq_add_neg, neg_mul] using
      ((hasDerivAt_id y).const_mul (-q)).const_add (-p * x)
  have h := ((Real.hasDerivAt_exp _).comp y hinner).const_mul coefficient
  simpa only [Function.comp_apply, logMonomial, logMonomialDy, neg_mul,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- Exact first-coordinate second derivative. -/
theorem logMonomialDx_hasDerivAt_fst (coefficient p q x y : ℝ) :
    HasDerivAt (fun u => logMonomialDx coefficient p q u y)
      (logMonomialDxx coefficient p q x y) x := by
  unfold logMonomialDx logMonomialDxx
  simpa [logMonomialDx, pow_two, mul_assoc] using
    (logMonomial_hasDerivAt_fst coefficient p q x y).const_mul (-p)

/-- Exact mixed second derivative. -/
theorem logMonomialDx_hasDerivAt_snd (coefficient p q x y : ℝ) :
    HasDerivAt (fun v => logMonomialDx coefficient p q x v)
      (logMonomialDxy coefficient p q x y) y := by
  unfold logMonomialDx logMonomialDxy
  simpa [logMonomialDy, mul_assoc] using
    (logMonomial_hasDerivAt_snd coefficient p q x y).const_mul (-p)

/-- Exact second-coordinate second derivative. -/
theorem logMonomialDy_hasDerivAt_snd (coefficient p q x y : ℝ) :
    HasDerivAt (fun v => logMonomialDy coefficient p q x v)
      (logMonomialDyy coefficient p q x y) y := by
  unfold logMonomialDy logMonomialDyy
  simpa [logMonomialDy, pow_two, mul_assoc] using
    (logMonomial_hasDerivAt_snd coefficient p q x y).const_mul (-q)

/-- Exponent vector of a two-radius monomial. -/
def logMonomialExponentVector (p q : ℝ) : Fin 2 → ℝ := ![p, q]

/-- Logarithmic Hessian as a weighted rank-one Gram matrix. -/
def logMonomialHessian (coefficient p q x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  logMonomial coefficient p q x y •
    Matrix.of fun i j => logMonomialExponentVector p q i * logMonomialExponentVector p q j

/-- Entrywise form of the weighted rank-one Hessian. -/
theorem logMonomialHessian_eq_entries (coefficient p q x y : ℝ) :
    logMonomialHessian coefficient p q x y =
      !![logMonomialDxx coefficient p q x y, logMonomialDxy coefficient p q x y;
         logMonomialDxy coefficient p q x y, logMonomialDyy coefficient p q x y] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [logMonomialHessian, logMonomialExponentVector, logMonomialDxx,
      logMonomialDxy, logMonomialDyy]
  all_goals ring

/-- Every individual log-monomial Hessian has zero determinant. -/
theorem logMonomialHessian_det (coefficient p q x y : ℝ) :
    (logMonomialHessian coefficient p q x y).det = 0 := by
  rw [logMonomialHessian_eq_entries, Matrix.det_fin_two]
  change
    logMonomialDxx coefficient p q x y * logMonomialDyy coefficient p q x y -
      logMonomialDxy coefficient p q x y * logMonomialDxy coefficient p q x y = 0
  unfold logMonomialDxx logMonomialDxy logMonomialDyy
  ring

/-- The vector perpendicular to the exponent vector is a canonical Hessian null direction. -/
theorem logMonomialHessian_mulVec_perp (coefficient p q x y : ℝ) :
    logMonomialHessian coefficient p q x y *ᵥ ![q, -p] = 0 := by
  funext i
  rw [logMonomialHessian_eq_entries]
  fin_cases i <;> norm_num [Matrix.mulVec, Fin.sum_univ_two]
  all_goals simp only [logMonomialDxx, logMonomialDxy, logMonomialDyy]
  all_goals ring

/-- Quadratic form of a monomial Hessian is one weighted square. -/
theorem logMonomialHessian_quadratic
    (coefficient p q x y : ℝ) (z : Fin 2 → ℝ) :
    star z ⬝ᵥ (logMonomialHessian coefficient p q x y *ᵥ z) =
      logMonomial coefficient p q x y * (p * z 0 + q * z 1) ^ (2 : ℕ) := by
  have hstar : star z = z := by ext i; simp
  rw [hstar, logMonomialHessian_eq_entries]
  norm_num [dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  unfold logMonomialDxx logMonomialDxy logMonomialDyy
  ring

/-- Every positive exponential monomial has positive-semidefinite log Hessian. -/
theorem logMonomialHessian_exp_posSemidef (gamma p q x y : ℝ) :
    (logMonomialHessian (Real.exp gamma) p q x y).PosSemidef := by
  unfold logMonomialHessian
  apply (HankelNormalization.posSemidef_rankOne (logMonomialExponentVector p q)).smul
  unfold logMonomial
  positivity

/-- Curvature-flux-torsion potential in logarithmic radius coordinates. -/
def twoModulusLogPotential (A B C q m n family x y : ℝ) : ℝ :=
  logMonomial (-2 * A) 4 4 x y +
  logMonomial (-24 * A) 2 6 x y +
  logMonomial (B * m ^ (2 : ℕ) / 2) 6 4 x y +
  logMonomial (B * q * n ^ (2 : ℕ)) 2 8 x y +
  logMonomial (-C * family ^ (2 : ℕ)) 2 4 x y

/-- First logarithmic stationarity equation. -/
def twoModulusLogForceX (A B C q m n family x y : ℝ) : ℝ :=
  logMonomialDx (-2 * A) 4 4 x y +
  logMonomialDx (-24 * A) 2 6 x y +
  logMonomialDx (B * m ^ (2 : ℕ) / 2) 6 4 x y +
  logMonomialDx (B * q * n ^ (2 : ℕ)) 2 8 x y +
  logMonomialDx (-C * family ^ (2 : ℕ)) 2 4 x y

/-- Second logarithmic stationarity equation. -/
def twoModulusLogForceY (A B C q m n family x y : ℝ) : ℝ :=
  logMonomialDy (-2 * A) 4 4 x y +
  logMonomialDy (-24 * A) 2 6 x y +
  logMonomialDy (B * m ^ (2 : ℕ) / 2) 6 4 x y +
  logMonomialDy (B * q * n ^ (2 : ℕ)) 2 8 x y +
  logMonomialDy (-C * family ^ (2 : ℕ)) 2 4 x y

/-- Expanded first stationarity equation. -/
theorem twoModulusLogForceX_eq (A B C q m n family x y : ℝ) :
    twoModulusLogForceX A B C q m n family x y =
      8 * A * Real.exp (-4 * x - 4 * y) +
      48 * A * Real.exp (-2 * x - 6 * y) -
      3 * B * m ^ (2 : ℕ) * Real.exp (-6 * x - 4 * y) -
      2 * B * q * n ^ (2 : ℕ) * Real.exp (-2 * x - 8 * y) +
      2 * C * family ^ (2 : ℕ) * Real.exp (-2 * x - 4 * y) := by
  unfold twoModulusLogForceX logMonomialDx logMonomial
  ring

/-- Expanded second stationarity equation. -/
theorem twoModulusLogForceY_eq (A B C q m n family x y : ℝ) :
    twoModulusLogForceY A B C q m n family x y =
      8 * A * Real.exp (-4 * x - 4 * y) +
      144 * A * Real.exp (-2 * x - 6 * y) -
      2 * B * m ^ (2 : ℕ) * Real.exp (-6 * x - 4 * y) -
      8 * B * q * n ^ (2 : ℕ) * Real.exp (-2 * x - 8 * y) +
      4 * C * family ^ (2 : ℕ) * Real.exp (-2 * x - 4 * y) := by
  unfold twoModulusLogForceY logMonomialDy logMonomial
  ring

/-- The first stationarity expression is the exact first partial derivative. -/
theorem twoModulusLogPotential_hasDerivAt_fst (A B C q m n family x y : ℝ) :
    HasDerivAt (fun u => twoModulusLogPotential A B C q m n family u y)
      (twoModulusLogForceX A B C q m n family x y) x := by
  exact (((logMonomial_hasDerivAt_fst (-2 * A) 4 4 x y).add
    (logMonomial_hasDerivAt_fst (-24 * A) 2 6 x y)).add
    (logMonomial_hasDerivAt_fst (B * m ^ (2 : ℕ) / 2) 6 4 x y)).add
    (logMonomial_hasDerivAt_fst (B * q * n ^ (2 : ℕ)) 2 8 x y) |>.add
    (logMonomial_hasDerivAt_fst (-C * family ^ (2 : ℕ)) 2 4 x y)

/-- The second stationarity expression is the exact second partial derivative. -/
theorem twoModulusLogPotential_hasDerivAt_snd (A B C q m n family x y : ℝ) :
    HasDerivAt (fun v => twoModulusLogPotential A B C q m n family x v)
      (twoModulusLogForceY A B C q m n family x y) y := by
  exact (((logMonomial_hasDerivAt_snd (-2 * A) 4 4 x y).add
    (logMonomial_hasDerivAt_snd (-24 * A) 2 6 x y)).add
    (logMonomial_hasDerivAt_snd (B * m ^ (2 : ℕ) / 2) 6 4 x y)).add
    (logMonomial_hasDerivAt_snd (B * q * n ^ (2 : ℕ)) 2 8 x y) |>.add
    (logMonomial_hasDerivAt_snd (-C * family ^ (2 : ℕ)) 2 4 x y)

/-- Full logarithmic Hessian of the two-modulus potential. -/
def twoModulusLogHessian (A B C q m n family x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  logMonomialHessian (-2 * A) 4 4 x y +
  logMonomialHessian (-24 * A) 2 6 x y +
  logMonomialHessian (B * m ^ (2 : ℕ) / 2) 6 4 x y +
  logMonomialHessian (B * q * n ^ (2 : ℕ)) 2 8 x y +
  logMonomialHessian (-C * family ^ (2 : ℕ)) 2 4 x y

/-- Entrywise sum of the five monomial Hessians. -/
theorem twoModulusLogHessian_eq_entries (A B C q m n family x y : ℝ) :
    twoModulusLogHessian A B C q m n family x y =
      !![
        logMonomialDxx (-2 * A) 4 4 x y + logMonomialDxx (-24 * A) 2 6 x y +
          logMonomialDxx (B * m ^ (2 : ℕ) / 2) 6 4 x y +
          logMonomialDxx (B * q * n ^ (2 : ℕ)) 2 8 x y +
          logMonomialDxx (-C * family ^ (2 : ℕ)) 2 4 x y,
        logMonomialDxy (-2 * A) 4 4 x y + logMonomialDxy (-24 * A) 2 6 x y +
          logMonomialDxy (B * m ^ (2 : ℕ) / 2) 6 4 x y +
          logMonomialDxy (B * q * n ^ (2 : ℕ)) 2 8 x y +
          logMonomialDxy (-C * family ^ (2 : ℕ)) 2 4 x y;
        logMonomialDxy (-2 * A) 4 4 x y + logMonomialDxy (-24 * A) 2 6 x y +
          logMonomialDxy (B * m ^ (2 : ℕ) / 2) 6 4 x y +
          logMonomialDxy (B * q * n ^ (2 : ℕ)) 2 8 x y +
          logMonomialDxy (-C * family ^ (2 : ℕ)) 2 4 x y,
        logMonomialDyy (-2 * A) 4 4 x y + logMonomialDyy (-24 * A) 2 6 x y +
          logMonomialDyy (B * m ^ (2 : ℕ) / 2) 6 4 x y +
          logMonomialDyy (B * q * n ^ (2 : ℕ)) 2 8 x y +
          logMonomialDyy (-C * family ^ (2 : ℕ)) 2 4 x y] := by
  unfold twoModulusLogHessian
  rw [logMonomialHessian_eq_entries, logMonomialHessian_eq_entries,
    logMonomialHessian_eq_entries, logMonomialHessian_eq_entries,
    logMonomialHessian_eq_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Positive quantized-flux part of the logarithmic Hessian. -/
def twoModulusFluxLogHessian (logB logQ m n x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  logMonomialHessian (Real.exp logB * m ^ (2 : ℕ) / 2) 6 4 x y +
  logMonomialHessian (Real.exp logB * Real.exp logQ * n ^ (2 : ℕ)) 2 8 x y

/-- Quantized flux contributes positive-semidefinite logarithmic curvature. -/
theorem twoModulusFluxLogHessian_posSemidef (logB logQ m n x y : ℝ) :
    (twoModulusFluxLogHessian logB logQ m n x y).PosSemidef := by
  apply Matrix.PosSemidef.add
  · unfold logMonomialHessian
    apply (HankelNormalization.posSemidef_rankOne (logMonomialExponentVector 6 4)).smul
    unfold logMonomial
    positivity
  · unfold logMonomialHessian
    apply (HankelNormalization.posSemidef_rankOne (logMonomialExponentVector 2 8)).smul
    unfold logMonomial
    positivity

/-- With nonzero fluxes encoded exponentially, the two non-collinear flux exponent vectors span
both radion directions and make the flux Hessian positive definite. -/
theorem twoModulusFluxLogHessian_exp_posDef
    (logB logQ logM logN x y : ℝ) :
    (twoModulusFluxLogHessian logB logQ (Real.exp logM) (Real.exp logN) x y).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (twoModulusFluxLogHessian_posSemidef logB logQ (Real.exp logM)
      (Real.exp logN) x y).isHermitian ?_
  intro z hz
  let alpha := logMonomial (Real.exp logB * Real.exp logM ^ (2 : ℕ) / 2) 6 4 x y
  let beta := logMonomial
    (Real.exp logB * Real.exp logQ * Real.exp logN ^ (2 : ℕ)) 2 8 x y
  have halpha : 0 < alpha := by unfold alpha logMonomial; positivity
  have hbeta : 0 < beta := by unfold beta logMonomial; positivity
  have hquad :
      star z ⬝ᵥ (twoModulusFluxLogHessian logB logQ (Real.exp logM)
          (Real.exp logN) x y *ᵥ z) =
        alpha * (6 * z 0 + 4 * z 1) ^ (2 : ℕ) +
          beta * (2 * z 0 + 8 * z 1) ^ (2 : ℕ) := by
    rw [twoModulusFluxLogHessian, Matrix.add_mulVec, dotProduct_add,
      logMonomialHessian_quadratic, logMonomialHessian_quadratic]
  rw [hquad]
  have hspan : 6 * z 0 + 4 * z 1 ≠ 0 ∨ 2 * z 0 + 8 * z 1 ≠ 0 := by
    by_contra h
    push Not at h
    have hz0 : z 0 = 0 := by linarith [h.1, h.2]
    have hz1 : z 1 = 0 := by linarith [h.1, h.2]
    apply hz
    funext i
    fin_cases i <;> assumption
  rcases hspan with hfirst | hsecond
  · have hpos : 0 < alpha * (6 * z 0 + 4 * z 1) ^ (2 : ℕ) :=
      mul_pos halpha (sq_pos_of_ne_zero hfirst)
    have hnonneg : 0 ≤ beta * (2 * z 0 + 8 * z 1) ^ (2 : ℕ) :=
      mul_nonneg hbeta.le (sq_nonneg _)
    linarith
  · have hnonneg : 0 ≤ alpha * (6 * z 0 + 4 * z 1) ^ (2 : ℕ) :=
      mul_nonneg halpha.le (sq_nonneg _)
    have hpos : 0 < beta * (2 * z 0 + 8 * z 1) ^ (2 : ℕ) :=
      mul_pos hbeta (sq_pos_of_ne_zero hsecond)
    linarith

/-- Attractive curvature and torsion part of the logarithmic Hessian. -/
def twoModulusAttractiveLogHessian (logA logC family x y : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  logMonomialHessian (-2 * Real.exp logA) 4 4 x y +
  logMonomialHessian (-24 * Real.exp logA) 2 6 x y +
  logMonomialHessian (-Real.exp logC * family ^ (2 : ℕ)) 2 4 x y

/-- Attractive curvature and torsion contribute negative-semidefinite logarithmic curvature. -/
theorem twoModulusAttractiveLogHessian_neg_posSemidef (logA logC family x y : ℝ) :
    (-twoModulusAttractiveLogHessian logA logC family x y).PosSemidef := by
  have hEq : -twoModulusAttractiveLogHessian logA logC family x y =
      logMonomialHessian (2 * Real.exp logA) 4 4 x y +
      logMonomialHessian (24 * Real.exp logA) 2 6 x y +
      logMonomialHessian (Real.exp logC * family ^ (2 : ℕ)) 2 4 x y := by
    ext i j
    simp [twoModulusAttractiveLogHessian, logMonomialHessian, logMonomial]
    ring
  rw [hEq]
  apply Matrix.PosSemidef.add
  · apply Matrix.PosSemidef.add
    · unfold logMonomialHessian
      apply (HankelNormalization.posSemidef_rankOne (logMonomialExponentVector 4 4)).smul
      unfold logMonomial
      positivity
    · unfold logMonomialHessian
      apply (HankelNormalization.posSemidef_rankOne (logMonomialExponentVector 2 6)).smul
      unfold logMonomial
      positivity
  · unfold logMonomialHessian
    apply (HankelNormalization.posSemidef_rankOne (logMonomialExponentVector 2 4)).smul
    unfold logMonomial
    positivity

/-- Isotropic restriction separates curvature, flux, and torsion into weights `-8`, `-10`, and
`-6`. -/
theorem twoModulusLogPotential_isotropic (A B C q m n family t : ℝ) :
    twoModulusLogPotential A B C q m n family t t =
      (-26 * A) * Real.exp (-8 * t) +
      (B * (m ^ (2 : ℕ) / 2 + q * n ^ (2 : ℕ))) * Real.exp (-10 * t) -
      (C * family ^ (2 : ℕ)) * Real.exp (-6 * t) := by
  unfold twoModulusLogPotential logMonomial
  have hexp (p q : ℝ) : Real.exp (-p * t - q * t) = Real.exp (-(p + q) * t) := by
    congr 1
    ring
  rw [hexp 4 4, hexp 2 6, hexp 6 4, hexp 2 8, hexp 2 4]
  norm_num
  ring

end GaloisForLFunctions.HTGeometry
