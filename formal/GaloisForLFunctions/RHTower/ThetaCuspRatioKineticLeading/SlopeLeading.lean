import GaloisForLFunctions.RHTower.ThetaCuspRatioKineticLeading.MinorLeading
import GaloisForLFunctions.RHTower.ThetaCuspRatioSquareSlopeSeam
import GaloisForLFunctions.RHTower.ThetaCuspRatioSourceConjugation

/-!
# Leading kinetic coefficient of the third slope and the displacement obstruction

With `C(P) = (12K+4) ∂_K P + (12K+8) U ∂_J P` the integer field satisfies
`∂_J^{n+1} Lie(P) = Lie(∂_J^{n+1} P) + (n+1) C(∂_J^n P)`.  Applied to
`integerThirdSlope = (2y-3)·Lie(minor) - 6·minor·Lie(2y-3)`, with `Lie(2y-3) = 24yJ` and the
minor's head `-D u² y⁴`, `D = 512·12^18`, this gives kinetic degree at most `17` and

`[J^17] integerThirdSlope = 48 D u² y⁴ (y+3)`.

The squared chart `u·integerThirdSlope(u,k,uz) = u²·reducedSlope(u²,k,z)` transports derivatives
with an exact factor `u^n`; cancelling the nonzero polynomial `U` and using injectivity of the
square chart gives

`deg_z reducedSlope ≤ 17`,  `[z^17] reducedSlope(v,k,z) = 48 D v^9 (3k+1)^4 (3k+4)`.

Consequently, for every centre `z₀`, the displacement polynomial `d ↦ reducedSlope(v,k,z₀-d)` has
`d^17` coefficient `-48 D v^9 (3k+1)^4 (3k+4)`, which is negative for `v > 0`, `k > -1/3`: no
representation with all nonnegative displacement coefficients exists, for the polynomial or for its
divided difference at `d = 0`.
-/

namespace HTGeometry.ThetaRatioSource
noncomputable section
open MvPolynomial ThetaRatioSquare

/-! ## Iterated kinetic derivatives -/

theorem iterate_pderivJ_integerLie (m : ℕ) (P : Poly) :
    (pderiv Coord.J)^[m+1] (integerLie P) =
      integerLie ((pderiv Coord.J)^[m+1] P)+(m+1) • kineticCommutator ((pderiv Coord.J)^[m] P) := by
  induction m with
  | zero => simp [pderivJ_integerLie]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_add, pderivJ_integerLie, map_nsmul,
      pderivJ_kineticCommutator, ← Function.iterate_succ_apply' (pderiv Coord.J),
      ← Function.iterate_succ_apply' (pderiv Coord.J)]
    simp only [Nat.succ_eq_add_one, succ_nsmul]
    abel

theorem iterate_pderivJ_X_mul (m : ℕ) (P : Poly) :
    (pderiv Coord.J)^[m+1] (X Coord.J*P) =
      X Coord.J*(pderiv Coord.J)^[m+1] P+(m+1) • (pderiv Coord.J)^[m] P := by
  induction m with
  | zero => simp [Derivation.leibniz, pderiv_X]
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_add, Derivation.leibniz, map_nsmul,
      ← Function.iterate_succ_apply' (pderiv Coord.J), ← Function.iterate_succ_apply' (pderiv Coord.J)]
    simp only [pderiv_X, smul_eq_mul, Pi.single_eq_same, mul_one, Nat.succ_eq_add_one, succ_nsmul]
    abel

theorem iterate_pderivJ_mul_of_free {c : Poly} (hc : pderiv Coord.J c = 0) (m : ℕ) (P : Poly) :
    (pderiv Coord.J)^[m] (c*P) = c*(pderiv Coord.J)^[m] P := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz, hc, smul_zero, add_zero, smul_eq_mul,
      Function.iterate_succ_apply']

/-! ## The minor's kinetic derivatives -/

/-- The minor head `-D u² y⁴`, `D = 512·12^18`. -/
def minorHead : Poly := -512*12^18*X Coord.U^2*kineticY^4

theorem kineticEquiv_minorHead :
    kineticEquiv minorHead = Polynomial.C (-512*12^18*kineticU^2*kineticYC^4) := by
  simp [minorHead, kineticEquiv_kineticY, kineticU, map_ofNat]

theorem kineticEquiv_injective : Function.Injective kineticEquiv := kineticEquiv.injective

theorem iterate_derivative_of_natDegree_le {p : Polynomial KCoeff} {n : ℕ} (h : p.natDegree ≤ n) :
    Polynomial.derivative^[n] p = Polynomial.C ((n.factorial : KCoeff)*p.coeff n) := by
  ext m
  rw [Polynomial.coeff_iterate_derivative, Polynomial.coeff_C]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [Nat.descFactorial_self, nsmul_eq_mul]
  · rw [if_neg hm.ne', Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), smul_zero]

theorem integerThirdMinor_kinetic_derivatives :
    (pderiv Coord.J)^[17] integerThirdMinor = 0 ∧
      (pderiv Coord.J)^[16] integerThirdMinor = (Nat.factorial 16 : Poly)*minorHead := by
  obtain ⟨hd, hc⟩ := integerThirdMinor_kinetic_leading
  constructor
  · apply kineticEquiv_injective
    rw [kineticEquiv_iterate_pderivJ, map_zero]
    exact Polynomial.iterate_derivative_eq_zero (by omega)
  · apply kineticEquiv_injective
    rw [kineticEquiv_iterate_pderivJ, iterate_derivative_of_natDegree_le hd, hc,
      map_mul kineticEquiv, kineticEquiv_minorHead, map_natCast, ← Polynomial.C_eq_natCast,
      ← map_mul]

/-! ## The third slope -/

theorem integerLie_integerJet_zero : integerLie (integerJet 0) = 24*kineticY*X Coord.J := by
  simp [integerJet, integerLie_expand, integerField, kineticY, pderiv_X]
  ring

theorem integerThirdSlope_eq_operator_form :
    integerThirdSlope = integerJet 0*integerLie integerThirdMinor-
      144*kineticY*(X Coord.J*integerThirdMinor) := by
  rw [integerThirdSlope, integerLie_integerJet_zero]; ring

/-- The slope head `48 D u² y⁴ (y+3)`. -/
def kineticSlopeHead : Poly := 48*512*12^18*X Coord.U^2*kineticY^4*(kineticY+3)

theorem pderivJ_minorHead : pderiv Coord.J minorHead = 0 := by
  simp [minorHead, pderiv_kineticY, pderiv_X, Derivation.leibniz]

theorem integerJet_zero_free : pderiv Coord.J (integerJet 0) = 0 := by
  simp [integerJet, pderiv_X]

theorem kineticY_free : pderiv Coord.J (144*kineticY) = 0 := by
  simp [pderiv_kineticY]

/-- **Kinetic derivatives of the third slope**: degree at most `17`, head `48 D u² y⁴(y+3)`. -/
theorem integerThirdSlope_kinetic_derivatives :
    (pderiv Coord.J)^[18] integerThirdSlope = 0 ∧
      (pderiv Coord.J)^[17] integerThirdSlope = (Nat.factorial 17 : Poly)*kineticSlopeHead := by
  obtain ⟨h17, h16⟩ := integerThirdMinor_kinetic_derivatives
  have h18 : (pderiv Coord.J)^[18] integerThirdMinor = 0 := by
    rw [Function.iterate_succ_apply', h17, map_zero]
  rw [integerThirdSlope_eq_operator_form]
  constructor
  · rw [show (18:ℕ) = 17+1 from rfl, iterate_map_sub, iterate_pderivJ_mul_of_free integerJet_zero_free,
      iterate_pderivJ_integerLie, h18, h17, iterate_pderivJ_mul_of_free kineticY_free,
      iterate_pderivJ_X_mul, h18, h17]
    simp [integerLie, kineticCommutator]
  · rw [show (17:ℕ) = 16+1 from rfl, iterate_map_sub, iterate_pderivJ_mul_of_free integerJet_zero_free,
      iterate_pderivJ_integerLie, h17, h16, iterate_pderivJ_mul_of_free kineticY_free,
      iterate_pderivJ_X_mul, h17, h16,
      kineticCommutator_of_pderivJ_eq_zero (by simp [Derivation.leibniz, pderivJ_minorHead])]
    simp only [integerLie, map_zero, zero_mul, Finset.sum_const_zero, zero_add, mul_zero,
      Derivation.leibniz, smul_eq_mul, nsmul_eq_mul, (pderiv _).map_natCast]
    simp [kineticSlopeHead, minorHead, integerJet, kineticY, pderiv_X, Derivation.leibniz, Nat.factorial]
    ring

/-! ## Transport through the shear and square charts -/

theorem pderivJ_shear (P : Poly) : pderiv Coord.J (shear P) = X Coord.U*shear (pderiv Coord.J P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]; ring
  | mul_X p i hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, shear_X, hp]
    cases i <;> simp [shearCoord, pderiv_X] <;> ring

theorem pderivJ_square (P : Poly) : pderiv Coord.J (square P) = square (pderiv Coord.J P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add, square_X, hp]
    cases i <;> simp [squareCoord, pderiv_X]

theorem iterate_pderivJ_shear (n : ℕ) (P : Poly) :
    (pderiv Coord.J)^[n] (shear P) = X Coord.U^n*shear ((pderiv Coord.J)^[n] P) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz, smul_eq_mul, smul_eq_mul, pderivJ_shear,
      Function.iterate_succ_apply']
    simp [pderiv_X]
    ring

theorem iterate_pderivJ_square (n : ℕ) (P : Poly) :
    (pderiv Coord.J)^[n] (square P) = square ((pderiv Coord.J)^[n] P) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, pderivJ_square, Function.iterate_succ_apply']

/-- The reduced slope head `48 D v^9 y⁴ (y+3)`. -/
def kineticReducedHead : Poly := 48*512*12^18*X Coord.U^9*kineticY^4*(kineticY+3)

theorem shear_kineticSlopeHead : shear kineticSlopeHead = kineticSlopeHead := by
  simp [kineticSlopeHead, kineticY, shearCoord, map_ofNat]

theorem square_kineticReducedHead : X Coord.U*square kineticReducedHead = X Coord.U^17*kineticSlopeHead := by
  simp [kineticReducedHead, kineticSlopeHead, kineticY, squareCoord, map_ofNat]
  ring

private theorem UX_free : pderiv Coord.J (X Coord.U : Poly) = 0 := by simp [pderiv_X]

/-- **Kinetic derivatives of the reduced slope**: degree at most `17` in the squared chart, head
`48 D v^9 y⁴ (y+3)`. -/
theorem reducedSlope_kinetic_derivatives :
    (pderiv Coord.J)^[18] reducedSlope = 0 ∧
      (pderiv Coord.J)^[17] reducedSlope = (Nat.factorial 17 : Poly)*kineticReducedHead := by
  obtain ⟨d18, d17⟩ := integerThirdSlope_kinetic_derivatives
  have key : ∀ n, X Coord.U^n*shear ((pderiv Coord.J)^[n] integerThirdSlope) =
      X Coord.U*square ((pderiv Coord.J)^[n] reducedSlope) := by
    intro n
    rw [← iterate_pderivJ_shear, integerSlope_shear_factor, iterate_pderivJ_mul_of_free UX_free,
      iterate_pderivJ_square]
  constructor
  · have h := key 18
    rw [d18, map_zero, mul_zero] at h
    have h' : square ((pderiv Coord.J)^[18] reducedSlope) = square 0 := by
      rw [map_zero]
      exact (mul_eq_zero.mp h.symm).resolve_left (MvPolynomial.X_ne_zero _)
    exact square_injective h'
  · have h := key 17
    rw [d17, map_mul, map_natCast, shear_kineticSlopeHead] at h
    apply square_injective
    apply mul_left_cancel₀ (MvPolynomial.X_ne_zero Coord.U)
    rw [← h, map_mul, map_natCast]
    linear_combination (-(Nat.factorial 17 : Poly))*square_kineticReducedHead

/-! ## The all-order slope response -/

/-- The slope operator `S(P) = (2y-3)·Lie(P) - 144 y J P`; `S(minor)` is the third slope. -/
def slopeOperator (P : Poly) : Poly := integerJet 0*integerLie P-144*kineticY*(X Coord.J*P)

theorem slopeOperator_minor : slopeOperator integerThirdMinor = integerThirdSlope :=
  integerThirdSlope_eq_operator_form.symm

/-- `∂_J^{n+1} S(P) = (2y-3)[Lie(∂^{n+1}P) + (n+1) C(∂^n P)] - 144y[J ∂^{n+1} P + (n+1) ∂^n P]`. -/
theorem iterate_pderivJ_slopeOperator (n : ℕ) (P : Poly) :
    (pderiv Coord.J)^[n+1] (slopeOperator P) =
      integerJet 0*(integerLie ((pderiv Coord.J)^[n+1] P)+(n+1) • kineticCommutator ((pderiv Coord.J)^[n] P))-
        144*kineticY*(X Coord.J*(pderiv Coord.J)^[n+1] P+(n+1) • (pderiv Coord.J)^[n] P) := by
  rw [slopeOperator, iterate_map_sub, iterate_pderivJ_mul_of_free integerJet_zero_free,
    iterate_pderivJ_integerLie, iterate_pderivJ_mul_of_free kineticY_free, iterate_pderivJ_X_mul]

/-! ## Kinetic coefficients of the slopes -/

theorem kineticEquiv_kineticSlopeHead :
    kineticEquiv kineticSlopeHead = Polynomial.C (48*512*12^18*kineticU^2*kineticYC^4*(kineticYC+3)) := by
  simp [kineticSlopeHead, kineticEquiv_kineticY, kineticU, map_ofNat]

theorem kineticEquiv_kineticReducedHead :
    kineticEquiv kineticReducedHead = Polynomial.C (48*512*12^18*kineticU^9*kineticYC^4*(kineticYC+3)) := by
  simp [kineticReducedHead, kineticEquiv_kineticY, kineticU, map_ofNat]

private theorem kinetic_of_derivatives {P H : Poly} {n : ℕ} {c : KCoeff}
    (h1 : (pderiv Coord.J)^[n+1] P = 0) (h2 : (pderiv Coord.J)^[n] P = (n.factorial : Poly)*H)
    (hH : kineticEquiv H = Polynomial.C c) :
    (kineticEquiv P).natDegree ≤ n ∧ (kineticEquiv P).coeff n = c := by
  constructor
  · apply natDegree_le_of_iterate_derivative
    rw [← kineticEquiv_iterate_pderivJ, h1, map_zero]
  · apply coeff_eq_of_iterate_derivative_coeff_zero
    rw [← kineticEquiv_iterate_pderivJ, h2, map_mul, hH, map_natCast]
    simp

/-- `deg_J integerThirdSlope ≤ 17` and `[J^17] integerThirdSlope = 48 D u² y⁴ (y+3)`. -/
theorem integerThirdSlope_kinetic_leading :
    (kineticEquiv integerThirdSlope).natDegree ≤ 17 ∧
      (kineticEquiv integerThirdSlope).coeff 17 = 48*512*12^18*kineticU^2*kineticYC^4*(kineticYC+3) :=
  kinetic_of_derivatives integerThirdSlope_kinetic_derivatives.1
    integerThirdSlope_kinetic_derivatives.2 kineticEquiv_kineticSlopeHead

/-- `deg_z reducedSlope ≤ 17` and `[z^17] reducedSlope = 48 D v^9 (3k+1)^4 (3k+4)`. -/
theorem reducedSlope_kinetic_leading :
    (kineticEquiv reducedSlope).natDegree ≤ 17 ∧
      (kineticEquiv reducedSlope).coeff 17 = 48*512*12^18*kineticU^9*kineticYC^4*(kineticYC+3) :=
  kinetic_of_derivatives reducedSlope_kinetic_derivatives.1 reducedSlope_kinetic_derivatives.2
    kineticEquiv_kineticReducedHead

/-! ## Evaluation charts and the displacement obstruction -/

/-- Evaluate a source polynomial at `U = v`, `K = k` and a polynomial kinetic coordinate `w`. -/
def chartPoly (v k : ℂ) (w : Polynomial ℂ) : Poly →ₐ[ℂ] Polynomial ℂ :=
  MvPolynomial.aeval (fun i => match i with
    | .U => Polynomial.C v
    | .K => Polynomial.C k
    | .J => w)

theorem derivative_chartPoly (v k : ℂ) (w : Polynomial ℂ) (P : Poly) :
    Polynomial.derivative (chartPoly v k w P) =
      chartPoly v k w (pderiv Coord.J P)*Polynomial.derivative w := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [chartPoly]
  | add p q hp hq => simp [hp, hq, add_mul]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.derivative_mul, hp, Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      map_add, map_mul, map_mul]
    cases i <;> simp [chartPoly, pderiv_X] <;> ring

theorem iterate_derivative_chartPoly (v k : ℂ) (a b : ℂ) (n : ℕ) (P : Poly) :
    Polynomial.derivative^[n] (chartPoly v k (Polynomial.C a+Polynomial.C b*Polynomial.X) P) =
      Polynomial.C (b^n)*chartPoly v k (Polynomial.C a+Polynomial.C b*Polynomial.X)
        ((pderiv Coord.J)^[n] P) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Polynomial.derivative_C_mul, derivative_chartPoly,
      Function.iterate_succ_apply']
    simp [pow_succ]
    ring

theorem chartPoly_kineticReducedHead (v k : ℂ) (w : Polynomial ℂ) :
    chartPoly v k w kineticReducedHead = Polynomial.C (48*512*12^18*v^9*(3*k+1)^4*(3*k+4)) := by
  simp only [chartPoly, kineticReducedHead, kineticY, map_mul, map_add, map_pow, map_ofNat, map_one,
    MvPolynomial.aeval_X]
  ring

theorem natDegree_le_of_iterate_derivative_complex {p : Polynomial ℂ} {n : ℕ}
    (h : Polynomial.derivative^[n+1] p = 0) : p.natDegree ≤ n := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hN
  rw [show n + m + 1 = m + (n+1) by omega]
  have hc := Polynomial.coeff_iterate_derivative (k := n+1) p m
  rw [h, Polynomial.coeff_zero, nsmul_eq_mul] at hc
  exact (mul_eq_zero.mp hc.symm).resolve_left
    (Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr (by omega)).ne')

/-- The reduced slope along a displacement `z = z₀ - d` at fixed `v, k`. -/
def displacementPoly (v k z₀ : ℂ) : Polynomial ℂ :=
  chartPoly v k (Polynomial.C z₀+Polynomial.C (-1)*Polynomial.X) reducedSlope

/-- The reduced slope as a polynomial in `z` at fixed `v, k`. -/
def kineticPoly (v k : ℂ) : Polynomial ℂ :=
  chartPoly v k (Polynomial.C 0+Polynomial.C 1*Polynomial.X) reducedSlope

private theorem chart_leading (v k a b : ℂ) :
    (chartPoly v k (Polynomial.C a+Polynomial.C b*Polynomial.X) reducedSlope).natDegree ≤ 17 ∧
      (chartPoly v k (Polynomial.C a+Polynomial.C b*Polynomial.X) reducedSlope).coeff 17 =
        b^17*(48*512*12^18*v^9*(3*k+1)^4*(3*k+4)) := by
  obtain ⟨d18, d17⟩ := reducedSlope_kinetic_derivatives
  constructor
  · apply natDegree_le_of_iterate_derivative_complex
    rw [iterate_derivative_chartPoly, d18, map_zero, mul_zero]
  · have h := Polynomial.coeff_iterate_derivative (k := 17)
      (chartPoly v k (Polynomial.C a+Polynomial.C b*Polynomial.X) reducedSlope) 0
    rw [iterate_derivative_chartPoly, d17, map_mul, map_natCast, chartPoly_kineticReducedHead, zero_add,
      Nat.descFactorial_self, nsmul_eq_mul] at h
    simp only [← Polynomial.C_eq_natCast, ← map_mul, Polynomial.coeff_C_zero] at h
    apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero 17) : ((Nat.factorial 17 : ℕ) : ℂ) ≠ 0)
    rw [← h]; ring

/-- `[z^17] reducedSlope(v,k,z) = 48 D v^9 (3k+1)^4 (3k+4)` and the degree is at most `17`. -/
theorem kineticPoly_leading (v k : ℂ) :
    (kineticPoly v k).natDegree ≤ 17 ∧
      (kineticPoly v k).coeff 17 = 48*512*12^18*v^9*(3*k+1)^4*(3*k+4) := by
  obtain ⟨h1, h2⟩ := chart_leading v k 0 1
  exact ⟨h1, by rw [kineticPoly, h2, one_pow, one_mul]⟩

/-- For `v > 0` and `k > 5/4` the kinetic degree of the reduced slope is exactly `17`, with positive
leading coefficient. -/
theorem kineticPoly_degree_exact {v k : ℝ} (hv : 0 < v) (hk : 5/4 < k) :
    (kineticPoly v k).natDegree = 17 ∧
      (kineticPoly v k).coeff 17 = ((48*512*12^18*v^9*(3*k+1)^4*(3*k+4) : ℝ) : ℂ) ∧
      0 < 48*512*12^18*v^9*(3*k+1)^4*(3*k+4) := by
  obtain ⟨h1, h2⟩ := kineticPoly_leading v k
  have hpos : 0 < 48*512*12^18*v^9*(3*k+1)^4*(3*k+4) := by
    have : 0 < 3*k+1 := by linarith
    have : 0 < 3*k+4 := by linarith
    positivity
  have hc : (kineticPoly v k).coeff 17 = ((48*512*12^18*v^9*(3*k+1)^4*(3*k+4) : ℝ) : ℂ) := by
    rw [h2]; push_cast; ring
  refine ⟨Polynomial.natDegree_eq_of_le_of_coeff_ne_zero h1 ?_, hc, hpos⟩
  rw [hc]; exact_mod_cast hpos.ne'

/-- **Displacement obstruction.**  For `v > 0`, `k > -1/3` and every centre `z₀`, the displacement
polynomial `d ↦ reducedSlope(v,k,z₀-d)` has degree exactly `17` with negative leading coefficient
`-48 D v^9 (3k+1)^4 (3k+4)`; no representation with all nonnegative coefficients exists, and its
divided difference at `d = 0` has degree `16` with the same negative leading coefficient. -/
theorem displacement_obstruction {v k : ℝ} (hv : 0 < v) (hk : -1/3 < k) (z₀ : ℂ) :
    (displacementPoly v k z₀).natDegree = 17 ∧
      (displacementPoly v k z₀).coeff 17 = ((-(48*512*12^18*v^9*(3*k+1)^4*(3*k+4)) : ℝ) : ℂ) ∧
      -(48*512*12^18*v^9*(3*k+1)^4*(3*k+4)) < 0 ∧
      ¬ (∀ n, ∃ c : ℝ, 0 ≤ c ∧ (displacementPoly v k z₀).coeff n = c) ∧
      (displacementPoly v k z₀).divX.natDegree = 16 ∧
      (displacementPoly v k z₀).divX.coeff 16 = (displacementPoly v k z₀).coeff 17 := by
  obtain ⟨h1, h2⟩ := chart_leading v k z₀ (-1)
  have hpos : 0 < 48*512*12^18*v^9*(3*k+1)^4*(3*k+4) := by
    have : 0 < 3*k+1 := by linarith
    have : 0 < 3*k+4 := by linarith
    positivity
  have hc : (displacementPoly v k z₀).coeff 17 =
      ((-(48*512*12^18*v^9*(3*k+1)^4*(3*k+4)) : ℝ) : ℂ) := by
    rw [displacementPoly, h2]; push_cast; ring
  have hne : (displacementPoly v k z₀).coeff 17 ≠ 0 := by
    rw [hc]; exact_mod_cast (neg_ne_zero.mpr hpos.ne')
  have hdeg : (displacementPoly v k z₀).natDegree = 17 :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero h1 hne
  refine ⟨hdeg, hc, neg_lt_zero.mpr hpos, ?_, ?_, ?_⟩
  · intro hall
    obtain ⟨c, hc0, hceq⟩ := hall 17
    rw [hc] at hceq
    have : -(48*512*12^18*v^9*(3*k+1)^4*(3*k+4)) = c := by exact_mod_cast hceq
    linarith
  · rw [Polynomial.natDegree_divX_eq_natDegree_tsub_one, hdeg]
  · rw [Polynomial.coeff_divX]

/-! ## Exact degrees -/

theorem kineticYC_ne_zero : kineticYC ≠ 0 := by
  intro h
  have := congrArg (MvPolynomial.eval (fun _ => (0:ℂ))) h
  simp [kineticYC] at this

theorem kineticU_ne_zero : kineticU ≠ 0 := MvPolynomial.X_ne_zero 0

/-- The kinetic degree of the third minor is exactly `16`. -/
theorem integerThirdMinor_kinetic_natDegree : (kineticEquiv integerThirdMinor).natDegree = 16 := by
  obtain ⟨h1, h2⟩ := integerThirdMinor_kinetic_leading
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero h1 ?_
  rw [h2]
  have h12 : (12:KCoeff) ≠ 0 := by
    rw [show (12:KCoeff) = C 12 by rw [map_ofNat]]; exact (MvPolynomial.C_ne_zero).mpr (by norm_num)
  have h512 : (512:KCoeff) ≠ 0 := by
    rw [show (512:KCoeff) = C 512 by rw [map_ofNat]]; exact (MvPolynomial.C_ne_zero).mpr (by norm_num)
  have := kineticU_ne_zero; have := kineticYC_ne_zero
  simp_all

/-- The `ε²` coefficient of the reversed source determinant: `q·M(F) = 512 u² y⁴`. -/
theorem reversedMinor_coeff_two :
    (hankelCubic (reversedReflection 2) (reversedReflection 4) (reversedReflection 6)
      (reversedReflection 8) (reversedReflection 10)).coeff 2 = 512*kineticU^2*kineticYC^4 := by
  rw [reversedMinor_decomposition, Polynomial.coeff_add, mul_assoc, Polynomial.coeff_X_pow_mul',
    Polynomial.coeff_X_pow_mul', if_pos le_rfl, if_neg (by norm_num), add_zero, Nat.sub_self,
    Polynomial.coeff_C_mul, Polynomial.coeff_zero_eq_eval_zero, ← Polynomial.coe_evalRingHom,
    hankelResidual_map]
  simp only [Polynomial.coe_evalRingHom]
  have ev : ∀ {n : ℕ}, 2 ≤ n → Even n →
      Polynomial.eval 0 (reversedReflection n).divX = reversedLinear n := fun hn he => by
    rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX, zero_add,
      reversedReflection_coeff_one hn he]
  rw [ev le_rfl (by decide), ev (by norm_num) (by decide), ev (by norm_num) (by decide),
    ev (by norm_num) (by decide), ev (by norm_num) (by decide), hankelResidual_reversedLinear]
  have h83 : C (8/3 : ℂ) * (3 : KCoeff) = 8 := by
    rw [show (3:KCoeff) = C 3 by rw [map_ofNat], ← map_mul, show (8:KCoeff) = C 8 by
      rw [map_ofNat]]; congr 1; norm_num
  linear_combination (64*kineticU^2*kineticYC^4)*h83

end
end HTGeometry.ThetaRatioSource
