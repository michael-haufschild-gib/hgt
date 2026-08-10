import GaloisForLFunctions.HTGeometry.QIncrementAnalytic
import GaloisForLFunctions.HTGeometry.QTranscendence
import GaloisForLFunctions.HTGeometry.QShiftInverse
import GaloisForLFunctions.HTGeometry.ShiftEliminationEngine

/-!
# The q-digamma jets are algebraically independent over `ℂ(z)`

Pastro's q-analogue of Hölder's theorem runs the shift elimination over the two-variable field
`ℂ(z,u)`, `u = qᶻ`.  A polynomial relation between `qᶻ` and the jets of `ψ_q = Γ_q'/Γ_q`, with
polynomial coefficients in `z`, is a member of the set of denominator-cleared annihilators
`qAnnihilator`.  That set is closed under subtraction and `ℂ(z,u)`-scalars, contains no nonzero
constant — because `qᶻ` is transcendental over `ℂ(z)` — and is stable under the jet substitution,
because the differentiated shift law adds the algebraic increments `δ_j = A_j(u)/(1−u)^{j+1}` to
the jets.  The elimination engine then forces every such relation to be zero.
-/

namespace GaloisForLFunctions.HTGeometry

set_option maxSynthPendingDepth 4

open MvPolynomial nonZeroDivisors GaloisForLFunctions GaloisForLFunctions.GenericShiftHolder

noncomputable section

/-! ## The integral two-variable ring and its field of fractions -/

/-- The inclusion `ℂ[z][u] → ℂ(z,u)`. -/
def toQField : Polynomial (Polynomial ℂ) →+* RatFunc (RatFunc ℂ) :=
  (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))).comp
    (Polynomial.mapRingHom (algebraMap (Polynomial ℂ) (RatFunc ℂ)))

theorem toQField_apply (p : Polynomial (Polynomial ℂ)) :
    toQField p = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
      (p.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) := rfl

theorem toQField_injective : Function.Injective toQField := by
  intro a b h
  rw [toQField_apply, toQField_apply] at h
  exact Polynomial.map_injective _ (RatFunc.algebraMap_injective ℂ)
    (RatFunc.algebraMap_injective (RatFunc ℂ) h)

theorem toQField_ne_zero {p : Polynomial (Polynomial ℂ)} (hp : p ≠ 0) : toQField p ≠ 0 :=
  fun h0 => hp (toQField_injective (by rw [h0, map_zero]))

theorem toQField_C_C (c : ℂ) :
    toQField (Polynomial.C (Polynomial.C c)) = algebraMap ℂ (RatFunc (RatFunc ℂ)) c := by
  rw [toQField_apply, Polynomial.map_C, algebraMap_polyC_qShiftField, algebraMap_polyC,
    ← IsScalarTower.algebraMap_apply]

/-- The coefficient inclusion `ℂ[z] → ℂ(z)` composed with the constant embedding is the scalar
embedding of `ℂ`. -/
theorem coeffInc_comp_C :
    (algebraMap (Polynomial ℂ) (RatFunc ℂ)).comp (Polynomial.C : ℂ →+* Polynomial ℂ)
      = algebraMap ℂ (RatFunc ℂ) := by
  apply RingHom.ext
  intro c
  rw [RingHom.comp_apply, algebraMap_polyC]

/-! ## Evaluation at `(z, qᶻ)` -/

/-- The value of the second variable: `u = qᶻ`. -/
def qPoint (q : RealEulerNome) (z : ℂ) : ℂ := (q.val : ℂ) ^ z

/-- Evaluation of `ℂ[z][u]` at `(z, qᶻ)`. -/
def qCoeffEval (q : RealEulerNome) (z : ℂ) : Polynomial (Polynomial ℂ) →+* ℂ :=
  Polynomial.eval₂RingHom (Polynomial.evalRingHom z) (qPoint q z)

theorem qCoeffEval_C (q : RealEulerNome) (z : ℂ) (p : Polynomial ℂ) :
    qCoeffEval q z (Polynomial.C p) = p.eval z := by
  simp [qCoeffEval]

theorem qCoeffEval_X (q : RealEulerNome) (z : ℂ) :
    qCoeffEval q z Polynomial.X = qPoint q z := by
  simp [qCoeffEval]

theorem qCoeffEval_map_C (q : RealEulerNome) (z : ℂ) (p : Polynomial ℂ) :
    qCoeffEval q z (p.map Polynomial.C) = p.eval (qPoint q z) := by
  rw [qCoeffEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map]
  have hcomp : (Polynomial.evalRingHom z).comp (Polynomial.C : ℂ →+* Polynomial ℂ)
      = RingHom.id ℂ := by
    apply RingHom.ext
    intro c
    simp
  rw [hcomp]
  rfl

theorem qCoeffEval_one_sub_X (q : RealEulerNome) (z : ℂ) :
    qCoeffEval q z (1 - Polynomial.X) = 1 - qPoint q z := by
  rw [map_sub, map_one, qCoeffEval_X]

/-! ## The integral shift -/

/-- The unit shift `z ↦ z + 1` of `ℂ[z]`. -/
def zShift : Polynomial ℂ →+* Polynomial ℂ :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.X + Polynomial.C 1)

theorem zShift_apply (p : Polynomial ℂ) :
    zShift p = p.comp (Polynomial.X + Polynomial.C 1) := rfl

/-- The shift `z ↦ z + 1`, `u ↦ q·u` of `ℂ[z][u]`. -/
def qIntShift (q : RealEulerNome) :
    Polynomial (Polynomial ℂ) →+* Polynomial (Polynomial ℂ) :=
  Polynomial.eval₂RingHom (Polynomial.C.comp zShift)
    (Polynomial.C (Polynomial.C ((q.val : ℂ))) * Polynomial.X)

theorem qIntShift_C (q : RealEulerNome) (p : Polynomial ℂ) :
    qIntShift q (Polynomial.C p) = Polynomial.C (zShift p) := by
  simp [qIntShift]

theorem qIntShift_X (q : RealEulerNome) :
    qIntShift q Polynomial.X
      = Polynomial.C (Polynomial.C ((q.val : ℂ))) * Polynomial.X := by
  simp [qIntShift]

/-- The integral shift realizes the q-shift of the field. -/
theorem toQField_qIntShift (q : RealEulerNome) (p : Polynomial (Polynomial ℂ)) :
    toQField (qIntShift q p) = qShift q (toQField p) := by
  have hhom : toQField.comp (qIntShift q) = (qShift q).comp toQField := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, RingHom.comp_apply, qIntShift_C, toQField_apply,
        toQField_apply, Polynomial.map_C, Polynomial.map_C, qShift_algebraMap,
        qShiftPolyMap_apply, Polynomial.map_C, Polynomial.C_comp]
      congr 2
      rw [ratShift_algebraMap, zShift_apply]
    · rw [RingHom.comp_apply, RingHom.comp_apply, qIntShift_X, toQField_apply,
        toQField_apply, Polynomial.map_X, qShift_algebraMap, qShiftPolyMap_apply,
        Polynomial.map_X, Polynomial.X_comp, Polynomial.map_mul, Polynomial.map_C,
        Polynomial.map_X, algebraMap_polyC, qConst]
  have := RingHom.congr_fun hhom p
  rwa [RingHom.comp_apply, RingHom.comp_apply] at this

/-- Evaluating after the integral shift is evaluating at `z + 1`. -/
theorem qCoeffEval_qIntShift (q : RealEulerNome) (z : ℂ) (p : Polynomial (Polynomial ℂ)) :
    qCoeffEval q z (qIntShift q p) = qCoeffEval q (z + 1) p := by
  have hhom : (qCoeffEval q z).comp (qIntShift q) = qCoeffEval q (z + 1) := by
    apply Polynomial.ringHom_ext
    · intro a
      rw [RingHom.comp_apply, qIntShift_C, qCoeffEval_C, qCoeffEval_C, zShift_apply,
        Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
    · rw [RingHom.comp_apply, qIntShift_X, map_mul, qCoeffEval_C, qCoeffEval_X,
        qCoeffEval_X, Polynomial.eval_C, qPoint, qPoint,
        Complex.cpow_add _ _ q.complex_ne_zero, Complex.cpow_one, mul_comm]
  exact RingHom.congr_fun hhom p

/-! ## The transcendence of `qᶻ` over `ℂ(z)` -/

theorem mem_qHalfPlane_ofReal {x : ℝ} (hx : 1 ≤ x) : ((x : ℝ) : ℂ) ∈ qHalfPlane := by
  show (0 : ℝ) < (((x : ℝ) : ℂ)).re
  rw [Complex.ofReal_re]
  linarith

/-- **The evaluation at `(z, qᶻ)` is injective on `ℂ[z][u]`**: a two-variable polynomial vanishing
along the curve `u = qᶻ` on the positive real axis is zero. -/
theorem qCoeffEval_eq_zero (q : RealEulerNome) {p : Polynomial (Polynomial ℂ)}
    (h : ∀ x : ℝ, 1 ≤ x → qCoeffEval q ((x : ℝ) : ℂ) p = 0) : p = 0 := by
  by_contra hp
  have hci₀ : p.coeff p.natTrailingDegree ≠ 0 :=
    Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hp
  have hmin : ∀ i < p.natTrailingDegree, p.coeff i = 0 := fun i hi =>
    Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi
  obtain ⟨x, hx, hne⟩ := exists_qcpow_combination_ne_zero q (n := p.natDegree)
    (fun i => p.coeff i) (Polynomial.natTrailingDegree_le_natDegree p) hci₀ hmin
  refine hne ?_
  have hcast : ((q.val ^ x : ℝ) : ℂ) = qPoint q ((x : ℝ) : ℂ) := by
    rw [qPoint, Complex.ofReal_cpow q.pos.le x]
  rw [hcast]
  have hexp : qCoeffEval q ((x : ℝ) : ℂ) p
      = ∑ i ∈ Finset.range (p.natDegree + 1),
          (p.coeff i).eval ((x : ℝ) : ℂ) * qPoint q ((x : ℝ) : ℂ) ^ i := by
    rw [qCoeffEval, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range]
    rfl
  rw [← hexp]
  exact h x hx

/-! ## Jets of the q-digamma function -/

/-- The q-digamma jet vector. -/
def qDigammaJet (q : RealEulerNome) (m : ℕ) (z : ℂ) : Fin m → ℂ :=
  fun j => iteratedDeriv (j : ℕ) (qDigamma q) z

/-- Evaluation of a two-variable-coefficient jet polynomial at `(z, qᶻ)` and the q-digamma
jets. -/
def qPolyJetEval (q : RealEulerNome) (m : ℕ) (z : ℂ) :
    MvPolynomial (Fin m) (Polynomial (Polynomial ℂ)) →+* ℂ :=
  eval₂Hom (qCoeffEval q z) (qDigammaJet q m z)

theorem qPolyJetEval_C (q : RealEulerNome) (m : ℕ) (z : ℂ) (p : Polynomial (Polynomial ℂ)) :
    qPolyJetEval q m z (C p) = qCoeffEval q z p := by
  simp [qPolyJetEval]

theorem qPolyJetEval_X (q : RealEulerNome) (m : ℕ) (z : ℂ) (j : Fin m) :
    qPolyJetEval q m z (X j) = qDigammaJet q m z j :=
  eval₂Hom_X' _ _ _

/-- A jet polynomial annihilates the q-digamma jets on the half-plane. -/
def AnnihilatesQDigamma (q : RealEulerNome) (m : ℕ)
    (G : MvPolynomial (Fin m) (Polynomial (Polynomial ℂ))) : Prop :=
  ∀ z ∈ qHalfPlane, qPolyJetEval q m z G = 0

/-! ## Clearing denominators in the two-variable field -/

/-- Every element of `ℂ(z,u)` is a fraction of elements of `ℂ[z][u]`. -/
theorem exists_qClear (k : RatFunc (RatFunc ℂ)) :
    ∃ a b : Polynomial (Polynomial ℂ), b ≠ 0 ∧ toQField a = k * toQField b := by
  classical
  obtain ⟨bN, hbN, hN'⟩ :=
    IsLocalization.integerNormalization_spec (Polynomial ℂ)⁰ k.num
  obtain ⟨bD, hbD, hD'⟩ :=
    IsLocalization.integerNormalization_spec (Polynomial ℂ)⁰ k.denom
  set N' := IsLocalization.integerNormalization (Polynomial ℂ)⁰ k.num with hN_def
  set D' := IsLocalization.integerNormalization (Polynomial ℂ)⁰ k.denom with hD_def
  have hbN0 : bN ≠ 0 := nonZeroDivisors.ne_zero hbN
  have hbD0 : bD ≠ 0 := nonZeroDivisors.ne_zero hbD
  have hsmul : ∀ (b : Polynomial ℂ) (P : Polynomial (RatFunc ℂ)),
      b • P = Polynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) b) * P := by
    intro b P
    rw [Algebra.smul_def, Polynomial.algebraMap_apply]
  have hNmap : toQField N' = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
      (Polynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) bN) * k.num) := by
    rw [toQField_apply, hN', hsmul]
  have hDmap : toQField D' = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
      (Polynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) bD) * k.denom) := by
    rw [toQField_apply, hD', hsmul]
  have hden : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) k.denom ≠ 0 :=
    fun h0 => k.denom_ne_zero (RatFunc.algebraMap_injective (RatFunc ℂ) (by rw [h0, map_zero]))
  have hnum : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) k.num
      = k * algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) k.denom :=
    (div_eq_iff hden).mp (RatFunc.num_div_denom k)
  have hD'0 : D' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hDmap
    have hz : Polynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) bD) * k.denom = 0 :=
      RatFunc.algebraMap_injective (RatFunc ℂ) (hDmap.symm.trans (map_zero _).symm)
    rcases mul_eq_zero.mp hz with h | h
    · exact hbD0 (RatFunc.algebraMap_injective ℂ
        (Polynomial.C_injective (by rw [h]; simp)))
    · exact k.denom_ne_zero h
  refine ⟨N' * Polynomial.C bD, D' * Polynomial.C bN,
    mul_ne_zero hD'0 (fun h0 => hbN0 (Polynomial.C_injective (by rw [h0, map_zero]))), ?_⟩
  have hCbD : toQField (Polynomial.C bD)
      = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
        (Polynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) bD)) := by
    rw [toQField_apply, Polynomial.map_C]
  have hCbN : toQField (Polynomial.C bN)
      = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
        (Polynomial.C (algebraMap (Polynomial ℂ) (RatFunc ℂ) bN)) := by
    rw [toQField_apply, Polynomial.map_C]
  rw [map_mul, map_mul, hNmap, hDmap, hCbD, hCbN]
  simp only [map_mul]
  rw [hnum]
  ring

/-! ## The denominator-cleared annihilator set -/

/-- Jet polynomials over `ℂ(z,u)` with a denominator-cleared integral form annihilating the
q-digamma jets. -/
def qAnnihilator (q : RealEulerNome) (m : ℕ) :
    Set (MvPolynomial (Fin m) (RatFunc (RatFunc ℂ))) :=
  {G | ∃ d : Polynomial (Polynomial ℂ), d ≠ 0 ∧
    ∃ G' : MvPolynomial (Fin m) (Polynomial (Polynomial ℂ)),
      MvPolynomial.map toQField G' = MvPolynomial.C (toQField d) * G ∧
      AnnihilatesQDigamma q m G'}

theorem qAnnihilator_sub (q : RealEulerNome) {m : ℕ}
    (G H : MvPolynomial (Fin m) (RatFunc (RatFunc ℂ)))
    (hG : G ∈ qAnnihilator q m) (hH : H ∈ qAnnihilator q m) :
    G - H ∈ qAnnihilator q m := by
  obtain ⟨d₁, hd₁, G', hG', hGv⟩ := hG
  obtain ⟨d₂, hd₂, H', hH', hHv⟩ := hH
  refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, C d₂ * G' - C d₁ * H', ?_, ?_⟩
  · rw [map_sub, map_mul, map_mul, MvPolynomial.map_C, MvPolynomial.map_C, hG', hH',
      map_mul, map_mul]
    ring
  · intro z hz
    rw [map_sub, map_mul, map_mul, qPolyJetEval_C, qPolyJetEval_C, hGv z hz, hHv z hz,
      mul_zero, mul_zero, sub_zero]

theorem qAnnihilator_smul (q : RealEulerNome) {m : ℕ} (k : RatFunc (RatFunc ℂ))
    (G : MvPolynomial (Fin m) (RatFunc (RatFunc ℂ))) (hG : G ∈ qAnnihilator q m) :
    C k * G ∈ qAnnihilator q m := by
  obtain ⟨d, hd, G', hG', hGv⟩ := hG
  obtain ⟨a, b, hb, hab⟩ := exists_qClear k
  refine ⟨d * b, mul_ne_zero hd hb, C a * G', ?_, ?_⟩
  · rw [map_mul, MvPolynomial.map_C, hG', hab, map_mul]
    simp only [map_mul]
    ring
  · intro z hz
    rw [map_mul, qPolyJetEval_C, hGv z hz, mul_zero]

theorem qAnnihilator_const (q : RealEulerNome) {m : ℕ} (k : RatFunc (RatFunc ℂ))
    (h : C k ∈ qAnnihilator q m) : k = 0 := by
  classical
  obtain ⟨d, hd, G', hG', hGv⟩ := h
  have hG'C : G' = C (MvPolynomial.coeff 0 G') := by
    apply MvPolynomial.ext
    intro β
    rw [MvPolynomial.coeff_C]
    by_cases hβ : 0 = β
    · rw [if_pos hβ, ← hβ]
    · rw [if_neg hβ]
      have hco := congrArg (MvPolynomial.coeff β) hG'
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C,
        if_neg hβ, mul_zero] at hco
      exact toQField_injective (hco.trans (map_zero _).symm)
  have hpoly : MvPolynomial.coeff 0 G' = 0 := by
    apply qCoeffEval_eq_zero q
    intro x hx
    have hz := hGv _ (mem_qHalfPlane_ofReal hx)
    rwa [hG'C, qPolyJetEval_C] at hz
  have h0 := congrArg (MvPolynomial.coeff 0) hG'
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_C,
    if_pos rfl, hpoly, map_zero] at h0
  exact (mul_eq_zero.mp h0.symm).resolve_left (toQField_ne_zero hd)

/-! ## Shift stability through the cleared substitution -/

/-- The common clearing factor `(1 − u)^m`. -/
def qDen (m : ℕ) : Polynomial (Polynomial ℂ) := (1 - Polynomial.X) ^ m

/-- The cleared increment numerator `A_j(u)·(1 − u)^{m−1−j}`. -/
def qPoleNum (q : RealEulerNome) (m : ℕ) (j : Fin m) : Polynomial (Polynomial ℂ) :=
  (qIncrNum q (j : ℕ)).map Polynomial.C * (1 - Polynomial.X) ^ (m - 1 - (j : ℕ))

theorem toQField_one_sub_X_pow (k : ℕ) :
    toQField ((1 - Polynomial.X) ^ k)
      = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
          ((1 - Polynomial.X) ^ k) := by
  rw [toQField_apply, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_X]

theorem toQField_qIncrNum (q : RealEulerNome) (j : ℕ) :
    toQField ((qIncrNum q j).map Polynomial.C)
      = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qIncrNumC q j) := by
  rw [toQField_apply, qIncrNumC, Polynomial.map_map, coeffInc_comp_C]

theorem toQField_qPoleNum (q : RealEulerNome) (m : ℕ) (j : Fin m) :
    toQField (qPoleNum q m j) = toQField (qDen m) * qIncr q (j : ℕ) := by
  have hj : (j : ℕ) + 1 + (m - 1 - (j : ℕ)) = m := by
    have := j.isLt
    omega
  have hne : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
      ((1 - Polynomial.X) ^ ((j : ℕ) + 1)) ≠ 0 :=
    algebraMapPoly_ne_zero (pow_ne_zero _ one_sub_X_ne_zero)
  rw [qPoleNum, qDen, map_mul, toQField_qIncrNum, toQField_one_sub_X_pow,
    toQField_one_sub_X_pow, qIncr, qPoleFactor]
  rw [show ((1 - Polynomial.X : Polynomial (RatFunc ℂ)) ^ m)
      = (1 - Polynomial.X) ^ ((j : ℕ) + 1) * (1 - Polynomial.X) ^ (m - 1 - (j : ℕ)) by
    rw [← pow_add, hj]]
  rw [map_mul]
  field_simp

/-- The denominator-cleared jet substitution: coefficients shift by `(z,u) ↦ (z+1, q·u)`, each jet
variable maps to `(1−u)^m·Y_j + A_j(u)·(1−u)^{m−1−j}`, and each monomial is padded to the uniform
clearing power `(1−u)^{m·N}`. -/
def qClearedShift (q : RealEulerNome) (m N : ℕ)
    (G' : MvPolynomial (Fin m) (Polynomial (Polynomial ℂ))) :
    MvPolynomial (Fin m) (Polynomial (Polynomial ℂ)) :=
  ∑ α ∈ G'.support,
    C (qIntShift q (MvPolynomial.coeff α G') * qDen m ^ (N - degSum α))
      * ∏ j : Fin m, (C (qDen m) * X j + C (qPoleNum q m j)) ^ (α j)

/-- The cleared substitution realizes the jet substitution after clearing `(1−u)^{m·N}`. -/
theorem map_qClearedShift (q : RealEulerNome) (m N : ℕ)
    (G' : MvPolynomial (Fin m) (Polynomial (Polynomial ℂ))) (hN : G'.totalDegree ≤ N) :
    MvPolynomial.map toQField (qClearedShift q m N G')
      = C (toQField (qDen m ^ N))
        * jetTranslateGen (qShift q) (qIncr q) m (MvPolynomial.map toQField G') := by
  classical
  conv_rhs => rw [G'.as_sum]
  rw [map_sum (MvPolynomial.map toQField), map_sum (jetTranslateGen (qShift q) (qIncr q) m),
    Finset.mul_sum, qClearedShift, map_sum (MvPolynomial.map toQField)]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hdα : degSum α ≤ N := le_trans (MvPolynomial.le_totalDegree hα) hN
  rw [MvPolynomial.map_monomial, jetTranslate_monomialGen, ← toQField_qIntShift]
  rw [map_mul, MvPolynomial.map_C, map_mul, map_pow]
  rw [map_prod]
  have hfactor : ∀ j : Fin m,
      MvPolynomial.map toQField
          ((C (qDen m) * X j + C (qPoleNum q m j)) ^ (α j))
        = (C (toQField (qDen m)) * (X j + C (qIncr q (j : ℕ)))) ^ (α j) := by
    intro j
    rw [map_pow]
    congr 1
    rw [map_add, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C,
      toQField_qPoleNum, map_mul, mul_add]
  rw [Finset.prod_congr rfl fun j _ => hfactor j]
  have hsplit : ∀ j : Fin m,
      (C (toQField (qDen m)) * (X j + C (qIncr q (j : ℕ))) : MvPolynomial (Fin m) (RatFunc (RatFunc ℂ))) ^ (α j)
        = C (toQField (qDen m)) ^ (α j) * (X j + C (qIncr q (j : ℕ))) ^ (α j) := by
    intro j
    rw [mul_pow]
  rw [Finset.prod_congr rfl fun j _ => hsplit j, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  have hpow : (C (toQField (qDen m)) : MvPolynomial (Fin m) (RatFunc (RatFunc ℂ))) ^ (∑ j : Fin m, α j)
      = C (toQField (qDen m ^ degSum α)) := by
    rw [← map_pow, ← map_pow, ← degSum_eq_univ_sum]
  rw [hpow]
  have hexp : qDen m ^ N = qDen m ^ (N - degSum α) * qDen m ^ degSum α := by
    rw [← pow_add]
    congr 1
    omega
  rw [show (∏ j : Fin m, (X j + C (qIncr q (j : ℕ))) ^ (α j)
      : MvPolynomial (Fin m) (RatFunc (RatFunc ℂ))) = transMonomialGen (qIncr q) α from rfl]
  rw [hexp]
  simp only [map_mul, map_pow]
  ring

/-- **The value law of the cleared substitution**: evaluation at `z` is `(1−qᶻ)^{m·N}` times
evaluation at `z + 1`. -/
theorem qPolyJetEval_qClearedShift (q : RealEulerNome) {m N : ℕ}
    {G' : MvPolynomial (Fin m) (Polynomial (Polynomial ℂ))} (hN : G'.totalDegree ≤ N)
    {z : ℂ} (hz : z ∈ qHalfPlane) :
    qPolyJetEval q m z (qClearedShift q m N G')
      = ((1 - qPoint q z) ^ m) ^ N * qPolyJetEval q m (z + 1) G' := by
  classical
  have hv : (1 : ℂ) - qPoint q z ≠ 0 := qcpow_ne_one q hz
  have hden : ∀ k : ℕ, qCoeffEval q z (qDen m ^ k) = ((1 - qPoint q z) ^ m) ^ k := by
    intro k
    rw [qDen, ← pow_mul, map_pow, qCoeffEval_one_sub_X, ← pow_mul]
  have hkey : ∀ j : Fin m,
      (1 - qPoint q z) ^ m * qDigammaJet q m z j
          + (qIncrNum q (j : ℕ)).eval (qPoint q z) * (1 - qPoint q z) ^ (m - 1 - (j : ℕ))
        = (1 - qPoint q z) ^ m * qDigammaJet q m (z + 1) j := by
    intro j
    have hFE := iteratedDeriv_qDigamma_shift_closed q (j : ℕ) hz
    rw [← show qPoint q z = (q.val : ℂ) ^ z from rfl] at hFE
    have hsplit : ((1 : ℂ) - qPoint q z) ^ m
        = (1 - qPoint q z) ^ ((j : ℕ) + 1) * (1 - qPoint q z) ^ (m - 1 - (j : ℕ)) := by
      rw [← pow_add]
      congr 1
      have := j.isLt
      omega
    rw [qDigammaJet, qDigammaJet, hFE, mul_add, hsplit]
    have hzpow : ((1 : ℂ) - qPoint q z) ^ ((j : ℕ) + 1) ≠ 0 := pow_ne_zero _ hv
    field_simp
  rw [qClearedShift, map_sum]
  have hterm : ∀ α ∈ G'.support,
      qPolyJetEval q m z
          (C (qIntShift q (MvPolynomial.coeff α G') * qDen m ^ (N - degSum α))
          * ∏ j : Fin m, (C (qDen m) * X j + C (qPoleNum q m j)) ^ (α j))
        = ((1 - qPoint q z) ^ m) ^ N * (qCoeffEval q (z + 1) (MvPolynomial.coeff α G')
            * ∏ j : Fin m, qDigammaJet q m (z + 1) j ^ (α j)) := by
    intro α hα
    have hdα : degSum α ≤ N := le_trans (MvPolynomial.le_totalDegree hα) hN
    rw [map_mul, qPolyJetEval_C, map_mul, qCoeffEval_qIntShift, hden, map_prod]
    have hfac : ∀ j : Fin m,
        qPolyJetEval q m z ((C (qDen m) * X j + C (qPoleNum q m j)) ^ (α j))
          = ((1 - qPoint q z) ^ m * qDigammaJet q m (z + 1) j) ^ (α j) := by
      intro j
      rw [map_pow]
      congr 1
      rw [map_add, map_mul, qPolyJetEval_C, qPolyJetEval_C, qPolyJetEval_X]
      rw [qDen, map_pow, qCoeffEval_one_sub_X, qPoleNum, map_mul, qCoeffEval_map_C,
        map_pow, qCoeffEval_one_sub_X]
      exact hkey j
    rw [Finset.prod_congr rfl fun j _ => hfac j]
    have hpull : ∏ j : Fin m, ((1 - qPoint q z) ^ m * qDigammaJet q m (z + 1) j) ^ (α j)
        = (((1 : ℂ) - qPoint q z) ^ m) ^ degSum α
          * ∏ j : Fin m, qDigammaJet q m (z + 1) j ^ (α j) := by
      rw [Finset.prod_congr rfl fun j _ => mul_pow _ _ _, Finset.prod_mul_distrib,
        Finset.prod_pow_eq_pow_sum, ← degSum_eq_univ_sum]
    rw [hpull]
    have hcombine : (((1 : ℂ) - qPoint q z) ^ m) ^ (N - degSum α)
        * (((1 : ℂ) - qPoint q z) ^ m) ^ degSum α = (((1 : ℂ) - qPoint q z) ^ m) ^ N := by
      rw [← pow_add]
      congr 1
      omega
    calc qCoeffEval q (z + 1) (MvPolynomial.coeff α G') * ((1 - qPoint q z) ^ m) ^ (N - degSum α)
          * ((((1 : ℂ) - qPoint q z) ^ m) ^ degSum α
            * ∏ j : Fin m, qDigammaJet q m (z + 1) j ^ (α j))
        = ((((1 : ℂ) - qPoint q z) ^ m) ^ (N - degSum α)
            * (((1 : ℂ) - qPoint q z) ^ m) ^ degSum α)
            * (qCoeffEval q (z + 1) (MvPolynomial.coeff α G')
              * ∏ j : Fin m, qDigammaJet q m (z + 1) j ^ (α j)) := by ring
      _ = ((1 - qPoint q z) ^ m) ^ N * (qCoeffEval q (z + 1) (MvPolynomial.coeff α G')
              * ∏ j : Fin m, qDigammaJet q m (z + 1) j ^ (α j)) := by rw [hcombine]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hexpand : qPolyJetEval q m (z + 1) G'
      = ∑ α ∈ G'.support, qCoeffEval q (z + 1) (MvPolynomial.coeff α G')
          * ∏ j : Fin m, qDigammaJet q m (z + 1) j ^ (α j) := by
    have hcast : qPolyJetEval q m (z + 1) G'
        = eval₂ (qCoeffEval q (z + 1)) (qDigammaJet q m (z + 1)) G' := rfl
    rw [hcast, eval₂_eq']
  rw [← hexpand]

theorem annihilatesQDigamma_qClearedShift (q : RealEulerNome) {m N : ℕ}
    {G' : MvPolynomial (Fin m) (Polynomial (Polynomial ℂ))} (hN : G'.totalDegree ≤ N)
    (hGv : AnnihilatesQDigamma q m G') :
    AnnihilatesQDigamma q m (qClearedShift q m N G') := by
  intro z hz
  rw [qPolyJetEval_qClearedShift q hN hz, hGv (z + 1) (mem_qHalfPlane_add_one hz), mul_zero]

theorem one_sub_X_ne_zero_int : (1 - Polynomial.X : Polynomial (Polynomial ℂ)) ≠ 0 := by
  intro h0
  have hco := congrArg (fun p => Polynomial.coeff p 1) h0
  simp [Polynomial.coeff_one] at hco

theorem qDen_ne_zero (m : ℕ) : qDen m ≠ 0 := pow_ne_zero _ one_sub_X_ne_zero_int

theorem qIntShift_ne_zero (q : RealEulerNome) {p : Polynomial (Polynomial ℂ)} (hp : p ≠ 0) :
    qIntShift q p ≠ 0 := by
  intro h0
  exact toQField_ne_zero hp
    ((qShift q).injective (by rw [← toQField_qIntShift, h0, map_zero, map_zero]))

theorem qAnnihilator_shift (q : RealEulerNome) {m : ℕ}
    (G : MvPolynomial (Fin m) (RatFunc (RatFunc ℂ))) (hG : G ∈ qAnnihilator q m) :
    jetTranslateGen (qShift q) (qIncr q) m G ∈ qAnnihilator q m := by
  obtain ⟨d, hd, G', hG', hGv⟩ := hG
  refine ⟨qDen m ^ G'.totalDegree * qIntShift q d,
    mul_ne_zero (pow_ne_zero _ (qDen_ne_zero m)) (qIntShift_ne_zero q hd),
    qClearedShift q m G'.totalDegree G', ?_,
    annihilatesQDigamma_qClearedShift q le_rfl hGv⟩
  rw [map_qClearedShift q m G'.totalDegree G' le_rfl, hG',
    map_mul (jetTranslateGen (qShift q) (qIncr q) m), jetTranslate_CGen,
    ← toQField_qIntShift, map_mul, map_mul]
  ring

/-! ## The elimination -/

/-- **The q-digamma jets are algebraically independent over `ℂ(z)` jointly with `qᶻ`**: a
two-variable-coefficient jet polynomial vanishing on the half-plane is the zero polynomial. -/
theorem annihilatesQDigamma_eq_zero (q : RealEulerNome) {m : ℕ}
    (G : MvPolynomial (Fin m) (Polynomial (Polynomial ℂ)))
    (hG : AnnihilatesQDigamma q m G) : G = 0 := by
  by_contra hG0
  refine no_shift_stable_annihilatorGen (qShift q) (qIncr q)
    (qShift_injective q) (qShift_const q) (fun hw => qShift_fixed_eq_const q hw)
    (qAnnihilator q m)
    (fun A B hA hB => qAnnihilator_sub q A B hA hB)
    (fun k A hA => qAnnihilator_smul q k A hA)
    (fun A hA => qAnnihilator_shift q A hA)
    (fun k hk => qAnnihilator_const q k hk)
    (fun {w} {δ} hres j => qIncr_not_coboundary q hres j)
    ⟨MvPolynomial.map toQField G,
      ⟨1, one_ne_zero, G, by rw [map_one, MvPolynomial.C_1, one_mul], hG⟩, ?_⟩
  intro h0
  exact hG0 (MvPolynomial.map_injective _ toQField_injective (by rw [h0, map_zero]))

end

end GaloisForLFunctions.HTGeometry
