import GaloisForLFunctions.HTGeometry.BalancedDiagonalNonvanishing
import GaloisForLFunctions.HTGeometry.GammaShiftEigenrelation

/-!
# Factorial--harmonic freeness in the Gamma pole sequence ring

The exact logarithmic coefficients of the factorially rescaled Gamma pole germs are not
independent formal parameters a priori.  They are concrete eventual sequences built from one
reciprocal signed-factorial scale and the generalized harmonic sums.  This module proves that
they nevertheless form a countably algebraically independent family over `ℂ`.

The proof has three constraint-side stages.

1. Rational functions embed in germs of complex sequences at `atTop` by evaluation on natural
   numbers.  The generalized harmonic sequences intertwine sequence shift with `jetTranslate`,
   so `no_shift_stable_annihilator` proves their joint algebraic independence over `ℂ(X)`.
2. A hypothetical algebraic relation for the signed factorial is chosen with least factorial
   degree.  Shifting and cancelling its leading term produces a forbidden rational shift
   eigenrelation, excluded by `no_shift_eigenrelation`.  Inversion then gives the reciprocal
   signed-factorial coordinate.
3. Every exact Gamma pole-log coefficient is a nonzero affine harmonic coordinate multiplied by
   a distinct positive power of the reciprocal factorial.  Evaluation at factorial variable one
   proves this weighted affine substitution injective.

No numerical approximation of Euler's constant or zeta values enters the argument: their values
are arbitrary constant translations and only the nonzero factorial slopes matter.
-/

open Filter Polynomial
open scoped Polynomial

namespace GaloisForLFunctions

noncomputable section

/-- Germs at infinity of complex sequences indexed by natural numbers. -/
abbrev NatGerm := Filter.Germ (Filter.atTop : Filter ℕ) ℂ

/-- Evaluate a complex polynomial pointwise on the natural numbers. -/
def polyNatFunctionEval : Polynomial ℂ →+* (ℕ → ℂ) where
  toFun p n := p.eval (n : ℂ)
  map_one' := by ext n; simp
  map_mul' p q := by ext n; simp
  map_zero' := by ext n; simp
  map_add' p q := by ext n; simp

/-- Polynomial evaluation in the eventual sequence ring. -/
def polyNatEval : Polynomial ℂ →+* NatGerm :=
  (Filter.Germ.coeRingHom Filter.atTop).comp polyNatFunctionEval

theorem polyNatEval_denominator_isUnit (y : nonZeroDivisors (Polynomial ℂ)) :
    IsUnit (polyNatEval y.1) := by
  rw [isUnit_iff_exists_inv]
  refine ⟨(fun n : ℕ => (y.1.eval (n : ℂ))⁻¹ : NatGerm), ?_⟩
  change (↑(fun n : ℕ => y.1.eval (n : ℂ)) : NatGerm) *
      ↑(fun n : ℕ => (y.1.eval (n : ℂ))⁻¹) = 1
  rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
  obtain ⟨N, hN⟩ := poly_eventually_ne_zero_nat y.1
    (mem_nonZeroDivisors_iff_ne_zero.mp y.2)
  exact Filter.eventually_atTop.2 ⟨N, fun n hn => by
    dsimp [polyNatEval, polyNatFunctionEval]
    exact mul_inv_cancel₀ (hN n hn)⟩

/-- Rational-function evaluation in the eventual sequence ring. -/
def ratNatEval : RatFunc ℂ →+* NatGerm :=
  IsLocalization.lift (M := nonZeroDivisors (Polynomial ℂ))
    (S := RatFunc ℂ) polyNatEval_denominator_isUnit

theorem polyNatEval_injective : Function.Injective polyNatEval := by
  intro p q hpq
  apply sub_eq_zero.mp
  by_contra hpq0
  obtain ⟨N, hN⟩ := poly_eventually_ne_zero_nat (p - q) hpq0
  have hg : polyNatEval (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  have hevent : (fun n : ℕ => (p - q).eval (n : ℂ)) =ᶠ[Filter.atTop]
      (fun _n : ℕ => 0) := by
    rw [← Filter.Germ.coe_eq]
    exact hg
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.1 hevent
  exact hN (max N M) (le_max_left _ _) (hM _ (le_max_right _ _))

theorem ratNatEval_injective : Function.Injective ratNatEval := by
  intro r s hrs
  apply sub_eq_zero.mp
  have hr : ratNatEval (r - s) = 0 := by
    rw [map_sub, hrs, sub_self]
  obtain ⟨⟨p, y⟩, hrepr⟩ := IsLocalization.mk'_surjective
    (nonZeroDivisors (Polynomial ℂ)) (r - s)
  rw [← hrepr, ratNatEval, IsLocalization.lift_mk'] at hr
  have hpy : polyNatEval p = 0 := by
    let u : NatGermˣ :=
      (IsUnit.liftRight
        (polyNatEval.toMonoidHom.restrict (nonZeroDivisors (Polynomial ℂ)))
          polyNatEval_denominator_isUnit) y
    change polyNatEval p * (↑(u⁻¹) : NatGerm) = 0 at hr
    have hc := congrArg (fun z : NatGerm => z * (↑u : NatGerm)) hr
    simpa [mul_assoc] using hc
  have hp : p = 0 := polyNatEval_injective (by rw [hpy, map_zero])
  rw [← hrepr, hp]
  exact IsLocalization.mk'_zero _

/-- Shift an eventual sequence germ by one natural-number index. -/
def natShiftGerm : NatGerm →+* NatGerm :=
  { toFun := fun f => f.compTendsto (fun n : ℕ => n + 1)
      ((Filter.tendsto_add_atTop_iff_nat 1).2 tendsto_id)
    map_one' := by
      rw [← Filter.Germ.coe_one]
      exact Filter.Germ.const_compTendsto _ _
    map_mul' := by
      intro f g
      induction f using Filter.Germ.inductionOn with
      | _ f =>
        induction g using Filter.Germ.inductionOn with
        | _ g =>
          simp only [Filter.Germ.coe_compTendsto]
          rfl
    map_zero' := by
      rw [← Filter.Germ.coe_zero]
      exact Filter.Germ.const_compTendsto _ _
    map_add' := by
      intro f g
      induction f using Filter.Germ.inductionOn with
      | _ f =>
        induction g using Filter.Germ.inductionOn with
        | _ g =>
          simp only [Filter.Germ.coe_compTendsto]
          rfl }

theorem ratNatEval_algebraMap (p : Polynomial ℂ) :
    ratNatEval (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) = polyNatEval p := by
  exact IsLocalization.lift_eq polyNatEval_denominator_isUnit p

/-- The `j`th signed factorial normalization of the depth-one generalized harmonic sum. -/
def harmonicJetSequence (j n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range n,
    ((-1 : ℂ) ^ j * (j.factorial : ℂ)) / (k : ℂ) ^ (j + 1)

theorem harmonicJetSequence_succ (j n : ℕ) :
    harmonicJetSequence j (n + 1) = harmonicJetSequence j n +
      ((-1 : ℂ) ^ j * (j.factorial : ℂ)) / (n : ℂ) ^ (j + 1) := by
  rw [harmonicJetSequence, harmonicJetSequence, Finset.sum_range_succ]

def harmonicJetGerm (j : ℕ) : NatGerm := harmonicJetSequence j

theorem ratNatEval_polePart (j : ℕ) :
    ratNatEval (polePart j) =
      (fun n : ℕ => ((-1 : ℂ) ^ j * (j.factorial : ℂ)) /
        (n : ℂ) ^ (j + 1) : NatGerm) := by
  let den : nonZeroDivisors (Polynomial ℂ) :=
    ⟨Polynomial.X ^ (j + 1), mem_nonZeroDivisors_iff_ne_zero.mpr
      (pow_ne_zero _ Polynomial.X_ne_zero)⟩
  let num : Polynomial ℂ := Polynomial.C ((-1 : ℂ) ^ j * (j.factorial : ℂ))
  have hpole : polePart j = IsLocalization.mk' (RatFunc ℂ) num den := by
    rw [IsFractionRing.mk'_eq_div]
    simp [polePart, num, den, RatFunc.algebraMap_X]
  have hspec := congrArg ratNatEval
    (IsLocalization.mk'_spec (S := RatFunc ℂ) num den)
  rw [map_mul, ratNatEval_algebraMap, ratNatEval_algebraMap] at hspec
  let c : NatGerm :=
    (fun n : ℕ => ((-1 : ℂ) ^ j * (j.factorial : ℂ)) /
      (n : ℂ) ^ (j + 1) : NatGerm)
  have hc : c * polyNatEval den.1 = polyNatEval num := by
    change (↑(fun n : ℕ => ((-1 : ℂ) ^ j * (j.factorial : ℂ)) /
          (n : ℂ) ^ (j + 1)) : NatGerm) *
        ↑(fun n : ℕ => den.1.eval (n : ℂ)) =
          ↑(fun n : ℕ => num.eval (n : ℂ))
    rw [← Filter.Germ.coe_mul, Filter.Germ.coe_eq]
    exact Filter.eventually_atTop.2 ⟨1, fun n hn => by
      simp [den, num]
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
      field_simp⟩
  rw [hpole]
  exact (polyNatEval_denominator_isUnit den).mul_right_cancel (hspec.trans hc.symm)

theorem shift_harmonicJetGerm (j : ℕ) :
    natShiftGerm (harmonicJetGerm j) = harmonicJetGerm j + ratNatEval (polePart j) := by
  change (↑(harmonicJetSequence j) : NatGerm).compTendsto
      (fun n : ℕ => n + 1) ((Filter.tendsto_add_atTop_iff_nat 1).2 tendsto_id) =
    (↑(harmonicJetSequence j) : NatGerm) + ratNatEval (polePart j)
  rw [Filter.Germ.coe_compTendsto, ratNatEval_polePart, ← Filter.Germ.coe_add]
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun n => harmonicJetSequence_succ j n

theorem shift_polyNatEval (p : Polynomial ℂ) :
    natShiftGerm (polyNatEval p) = polyNatEval
      (p.comp (Polynomial.X + Polynomial.C 1)) := by
  change (↑(fun n : ℕ => p.eval (n : ℂ)) : NatGerm).compTendsto
      (fun n : ℕ => n + 1) ((Filter.tendsto_add_atTop_iff_nat 1).2 tendsto_id) =
    ↑(fun n : ℕ => (p.comp (Polynomial.X + Polynomial.C 1)).eval (n : ℂ))
  rw [Filter.Germ.coe_compTendsto, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun n => by
    simp [Polynomial.eval_comp]

theorem shift_ratNatEval (r : RatFunc ℂ) :
    natShiftGerm (ratNatEval r) = ratNatEval (ratShift r) := by
  have hhom : natShiftGerm.comp ratNatEval = ratNatEval.comp ratShift := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial ℂ))
    apply Polynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply]
      rw [ratNatEval_algebraMap, ratShift_algebraMap,
        ratNatEval_algebraMap, shift_polyNatEval]
    · simp only [RingHom.comp_apply]
      rw [ratNatEval_algebraMap, ratShift_algebraMap,
        ratNatEval_algebraMap, shift_polyNatEval]
  exact RingHom.congr_fun hhom r

/-- Evaluation of finitely many generalized harmonic coordinates in sequence germs. -/
def harmonicJetEval (m : ℕ) :
    MvPolynomial (Fin m) (RatFunc ℂ) →+* NatGerm :=
  MvPolynomial.eval₂Hom ratNatEval (fun j => harmonicJetGerm (j : ℕ))

theorem shift_harmonicJetEval (m : ℕ) (P : MvPolynomial (Fin m) (RatFunc ℂ)) :
    natShiftGerm (harmonicJetEval m P) = harmonicJetEval m (jetTranslate m P) := by
  have hhom : natShiftGerm.comp (harmonicJetEval m) =
      (harmonicJetEval m).comp (jetTranslate m) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      simp [harmonicJetEval, shift_ratNatEval, jetTranslate_C]
    · intro j
      simp [harmonicJetEval, shift_harmonicJetGerm, jetTranslate_X]
  exact RingHom.congr_fun hhom P

/-- Every finite generalized harmonic jet family is algebraically independent over `ℂ(X)`
inside the eventual sequence ring. -/
theorem harmonicJetEval_injective (m : ℕ) : Function.Injective (harmonicJetEval m) := by
  intro P Q heq
  apply sub_eq_zero.mp
  by_contra hne
  have hzero : harmonicJetEval m (P - Q) = 0 := by
    rw [map_sub, heq, sub_self]
  exact no_shift_stable_annihilator
    {G | harmonicJetEval m G = 0}
    (fun G H hG hH => by rw [Set.mem_setOf_eq, map_sub, hG, hH, sub_zero])
    (fun k G hG => by
      change harmonicJetEval m G = 0 at hG
      change harmonicJetEval m (MvPolynomial.C k * G) = 0
      rw [map_mul]
      rw [show harmonicJetEval m (MvPolynomial.C k) = ratNatEval k by
        simp [harmonicJetEval]]
      rw [hG, mul_zero])
    (fun G hG => by rw [Set.mem_setOf_eq, ← shift_harmonicJetEval, hG, map_zero])
    (fun k hk => by
      have : ratNatEval k = 0 := by simpa [harmonicJetEval] using hk
      exact ratNatEval_injective (by rw [this, map_zero]))
    ⟨P - Q, hzero, hne⟩

/-- The square of the signed factorial sequence; the zero index contributes one. -/
def factorialSquareSequence (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.range n, if k = 0 then 1 else (k : ℂ) ^ 2

theorem factorialSquareSequence_ne_zero (n : ℕ) : factorialSquareSequence n ≠ 0 := by
  rw [factorialSquareSequence, Finset.prod_ne_zero_iff]
  intro k _hk
  by_cases hk0 : k = 0
  · simp [hk0]
  · simp [hk0]

theorem factorialSquareSequence_succ {n : ℕ} (hn : 1 ≤ n) :
    factorialSquareSequence (n + 1) = (n : ℂ) ^ 2 * factorialSquareSequence n := by
  rw [factorialSquareSequence, factorialSquareSequence, Finset.prod_range_succ,
    if_neg (by omega)]
  ring

def factorialSquareGerm : NatGerm := factorialSquareSequence

theorem factorialSquareGerm_isUnit : IsUnit factorialSquareGerm := by
  rw [isUnit_iff_exists_inv]
  refine ⟨(fun n : ℕ => (factorialSquareSequence n)⁻¹ : NatGerm), ?_⟩
  change (↑factorialSquareSequence : NatGerm) *
      ↑(fun n : ℕ => (factorialSquareSequence n)⁻¹) = 1
  rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun n =>
    mul_inv_cancel₀ (factorialSquareSequence_ne_zero n)

theorem ratNatEval_X_sq : ratNatEval ((RatFunc.X : RatFunc ℂ) ^ 2) =
    (fun n : ℕ => (n : ℂ) ^ 2 : NatGerm) := by
  rw [← RatFunc.algebraMap_X, ← map_pow, ratNatEval_algebraMap]
  apply Filter.Germ.coe_eq.mpr
  exact Filter.Eventually.of_forall fun n => by
    simp [polyNatFunctionEval]

theorem shift_factorialSquareGerm :
    natShiftGerm factorialSquareGerm =
      ratNatEval ((RatFunc.X : RatFunc ℂ) ^ 2) * factorialSquareGerm := by
  change (↑factorialSquareSequence : NatGerm).compTendsto
      (fun n : ℕ => n + 1) ((Filter.tendsto_add_atTop_iff_nat 1).2 tendsto_id) =
    ratNatEval ((RatFunc.X : RatFunc ℂ) ^ 2) * (↑factorialSquareSequence : NatGerm)
  rw [Filter.Germ.coe_compTendsto, ratNatEval_X_sq, ← Filter.Germ.coe_mul,
    Filter.Germ.coe_eq]
  exact Filter.eventually_atTop.2 ⟨1, fun n hn => factorialSquareSequence_succ hn⟩

/-- Coefficientwise shifted transform of a polynomial in the factorial-square variable. -/
def factorialSquareTranslate (m : ℕ)
    (P : Polynomial (MvPolynomial (Fin m) (RatFunc ℂ))) :
    Polynomial (MvPolynomial (Fin m) (RatFunc ℂ)) :=
  P.sum fun e a => Polynomial.monomial e
    (jetTranslate m a * MvPolynomial.C ((RatFunc.X : RatFunc ℂ) ^ 2) ^ e)

/-- Evaluate the factorial-square variable over the generalized harmonic coordinate ring. -/
def factorialSquareEval (m : ℕ) :
    Polynomial (MvPolynomial (Fin m) (RatFunc ℂ)) →+* NatGerm :=
  Polynomial.eval₂RingHom (harmonicJetEval m) factorialSquareGerm

theorem coeff_factorialSquareTranslate (m : ℕ)
    (P : Polynomial (MvPolynomial (Fin m) (RatFunc ℂ))) (e : ℕ) :
    (factorialSquareTranslate m P).coeff e =
      jetTranslate m (P.coeff e) *
        MvPolynomial.C ((RatFunc.X : RatFunc ℂ) ^ 2) ^ e := by
  classical
  rw [factorialSquareTranslate, Polynomial.sum_def, Polynomial.finsetSum_coeff]
  by_cases he : e ∈ P.support
  · rw [Finset.sum_eq_single e]
    · rw [Polynomial.coeff_monomial, if_pos rfl]
    · intro b _hb hbe
      rw [Polynomial.coeff_monomial, if_neg hbe]
    · exact fun h => (h he).elim
  · have hcoeff : P.coeff e = 0 := Polynomial.notMem_support_iff.mp he
    rw [hcoeff, map_zero, zero_mul]
    apply Finset.sum_eq_zero
    intro b hb
    rw [Polynomial.coeff_monomial, if_neg]
    exact fun hbe => he (hbe ▸ hb)

theorem factorialSquareTranslate_ne_zero {m : ℕ}
    {P : Polynomial (MvPolynomial (Fin m) (RatFunc ℂ))} (hP : P ≠ 0) :
    factorialSquareTranslate m P ≠ 0 := by
  intro h0
  have hc := congrArg (fun Q : Polynomial (MvPolynomial (Fin m) (RatFunc ℂ)) =>
    Q.coeff P.natDegree) h0
  change (factorialSquareTranslate m P).coeff P.natDegree = 0 at hc
  rw [coeff_factorialSquareTranslate, Polynomial.coeff_natDegree] at hc
  exact mul_ne_zero
    (fun h => Polynomial.leadingCoeff_ne_zero.mpr hP
      (jetTranslate_injective (by rw [h, map_zero])))
    (pow_ne_zero _ (MvPolynomial.C_ne_zero.mpr
      (pow_ne_zero _ ratFuncX_ne_zero))) hc

theorem natDegree_factorialSquareTranslate {m : ℕ}
    (P : Polynomial (MvPolynomial (Fin m) (RatFunc ℂ))) :
    (factorialSquareTranslate m P).natDegree = P.natDegree := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp [factorialSquareTranslate]
  apply le_antisymm
  · rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_factorialSquareTranslate,
      Polynomial.coeff_eq_zero_of_natDegree_lt hN, map_zero, zero_mul]
  · apply Polynomial.le_natDegree_of_ne_zero
    rw [coeff_factorialSquareTranslate, Polynomial.coeff_natDegree]
    exact mul_ne_zero
      (fun h => Polynomial.leadingCoeff_ne_zero.mpr hP
        (jetTranslate_injective (by rw [h, map_zero])))
      (pow_ne_zero _ (MvPolynomial.C_ne_zero.mpr
        (pow_ne_zero _ ratFuncX_ne_zero)))

theorem shift_factorialSquareEval (m : ℕ)
    (P : Polynomial (MvPolynomial (Fin m) (RatFunc ℂ))) :
    natShiftGerm (factorialSquareEval m P) =
      factorialSquareEval m (factorialSquareTranslate m P) := by
  change natShiftGerm (Polynomial.eval₂ (harmonicJetEval m) factorialSquareGerm P) =
    Polynomial.eval₂ (harmonicJetEval m) factorialSquareGerm
      (factorialSquareTranslate m P)
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def, map_sum]
  rw [factorialSquareTranslate, Polynomial.eval₂_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  simp only [Polynomial.eval₂_monomial, map_mul, map_pow]
  rw [shift_harmonicJetEval, shift_factorialSquareGerm]
  simp [harmonicJetEval]
  ring

/-- The factorial square is transcendental over every finite generalized-harmonic coordinate
ring in eventual sequence germs. -/
theorem factorialSquareEval_injective (m : ℕ) :
    Function.Injective (factorialSquareEval m) := by
  classical
  intro P Q hPQ
  apply sub_eq_zero.mp
  have hrel : factorialSquareEval m (P - Q) = 0 := by
    rw [map_sub, hPQ, sub_self]
  by_contra hne
  let Rel : ℕ → Prop := fun D =>
    ∃ T : Polynomial (MvPolynomial (Fin m) (RatFunc ℂ)),
      T ≠ 0 ∧ factorialSquareEval m T = 0 ∧ T.natDegree = D
  have hex : ∃ D, Rel D := ⟨(P - Q).natDegree, P - Q, hne, hrel, rfl⟩
  let D := Nat.find hex
  obtain ⟨T, hTne, hTzero, hTdeg⟩ := Nat.find_spec hex
  change T.natDegree = D at hTdeg
  have hmin : ∀ V : Polynomial (MvPolynomial (Fin m) (RatFunc ℂ)),
      V ≠ 0 → factorialSquareEval m V = 0 → D ≤ V.natDegree := by
    intro V hVne hVzero
    exact Nat.find_min' hex ⟨V, hVne, hVzero, rfl⟩
  let a := T.leadingCoeff
  let q : MvPolynomial (Fin m) (RatFunc ℂ) :=
    MvPolynomial.C ((RatFunc.X : RatFunc ℂ) ^ 2)
  have ha : a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hTne
  have hq : q ≠ 0 := MvPolynomial.C_ne_zero.mpr
    (pow_ne_zero _ ratFuncX_ne_zero)
  have hTtr_ne : factorialSquareTranslate m T ≠ 0 :=
    factorialSquareTranslate_ne_zero hTne
  have hTtr_zero : factorialSquareEval m (factorialSquareTranslate m T) = 0 := by
    rw [← shift_factorialSquareEval, hTzero, map_zero]
  let U : Polynomial (MvPolynomial (Fin m) (RatFunc ℂ)) :=
    Polynomial.C a * factorialSquareTranslate m T -
      Polynomial.C (jetTranslate m a * q ^ D) * T
  have hUzero : factorialSquareEval m U = 0 := by
    simp only [U]
    rw [map_sub, map_mul, map_mul, hTtr_zero, hTzero,
      mul_zero, mul_zero, sub_zero]
  have hUle : U.natDegree ≤ D := by
    simp only [U]
    refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_mul_le.trans (by
        rw [Polynomial.natDegree_C, zero_add,
          natDegree_factorialSquareTranslate, hTdeg])
    · exact Polynomial.natDegree_mul_le.trans (by
        rw [Polynomial.natDegree_C, zero_add, hTdeg])
  have hUcoeff : U.coeff D = 0 := by
    have hcoeffD : T.coeff D = a := by
      rw [← hTdeg, Polynomial.coeff_natDegree]
    simp only [U]
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
      coeff_factorialSquareTranslate, hcoeffD]
    change a * (jetTranslate m a * q ^ D) -
      (jetTranslate m a * q ^ D) * a = 0
    ring
  have hU : U = 0 := by
    by_contra hUne
    have hUD : D ≤ U.natDegree := hmin U hUne hUzero
    have heq : U.natDegree = D := by omega
    have hlc : U.coeff D ≠ 0 := by
      rw [← heq, Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hUne
    exact hlc hUcoeff
  have hDpos : 1 ≤ D := by
    by_contra hD
    have hD0 : D = 0 := by omega
    have hTconst : T = Polynomial.C a := by
      have hcard : T.support.card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        have hxle := Polynomial.le_natDegree_of_mem_supp x hx
        have hyle := Polynomial.le_natDegree_of_mem_supp y hy
        rw [hTdeg, hD0] at hxle hyle
        omega
      have hm := Polynomial.C_mul_X_pow_eq_self (p := T) hcard
      rw [hTdeg, hD0, pow_zero, mul_one] at hm
      exact hm.symm
    have hAeval : harmonicJetEval m a = 0 := by
      have h := hTzero
      rw [hTconst] at h
      simpa [factorialSquareEval] using h
    exact ha (harmonicJetEval_injective m (by rw [hAeval, map_zero]))
  have hsupp2 : 2 ≤ T.support.card := by
    by_contra hsupp
    have hcard : T.support.card ≤ 1 := by omega
    have hmono : Polynomial.C a * Polynomial.X ^ D = T := by
      rw [Polynomial.C_mul_X_pow_eq_monomial]
      simpa [hTdeg] using Polynomial.monomial_natDegree_leadingCoeff_eq_self hcard
    have hprod : harmonicJetEval m a * factorialSquareGerm ^ D = 0 := by
      have h := hTzero
      rw [← hmono] at h
      simpa [factorialSquareEval] using h
    have hAeval : harmonicJetEval m a = 0 := by
      apply (factorialSquareGerm_isUnit.pow D).mul_right_cancel
      simpa using hprod
    exact ha (harmonicJetEval_injective m (by rw [hAeval, map_zero]))
  have hDmem : D ∈ T.support := by
    rw [← hTdeg]
    exact Polynomial.natDegree_mem_support_of_nonzero hTne
  have herase : (T.support.erase D).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem hDmem]
    omega
  obtain ⟨d, hdmem⟩ := herase
  have hdmemT : d ∈ T.support := Finset.mem_of_mem_erase hdmem
  have hdlt : d < D := by
    have hdle := Polynomial.le_natDegree_of_mem_supp d hdmemT
    rw [hTdeg] at hdle
    exact lt_of_le_of_ne hdle (Finset.mem_erase.mp hdmem).1
  let b := T.coeff d
  have hb : b ≠ 0 := Polynomial.mem_support_iff.mp hdmemT
  have hcoef := congrArg
    (fun V : Polynomial (MvPolynomial (Fin m) (RatFunc ℂ)) => V.coeff d) hU
  change U.coeff d = 0 at hcoef
  simp only [U] at hcoef
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    coeff_factorialSquareTranslate] at hcoef
  change a * (jetTranslate m b * q ^ d) -
    (jetTranslate m a * q ^ D) * b = 0 at hcoef
  let e := D - d
  have he : 1 ≤ e := by omega
  have hDsplit : D = d + e := by omega
  have hcancel : jetTranslate m b * a =
      q ^ e * (b * jetTranslate m a) := by
    apply mul_right_cancel₀ (pow_ne_zero d hq)
    rw [hDsplit, pow_add] at hcoef
    linear_combination hcoef
  have hqpow : q ^ e = MvPolynomial.C ((RatFunc.X : RatFunc ℂ) ^ (2 * e)) := by
    change (MvPolynomial.C ((RatFunc.X : RatFunc ℂ) ^ 2)) ^ e =
      MvPolynomial.C ((RatFunc.X : RatFunc ℂ) ^ (2 * e))
    rw [← map_pow, ← pow_mul]
  rw [hqpow] at hcancel
  exact no_shift_eigenrelation hb ha (by omega : 1 ≤ 2 * e)
    (by simpa [mul_comm] using hcancel)

/-- The signed factorial sequence `(-1)^(n-1) (n-1)!`, with value one at zero. -/
def signedFactorialSequence (n : ℕ) : ℂ :=
  ∏ k ∈ Finset.range n, if k = 0 then 1 else -(k : ℂ)

theorem signedFactorialSequence_ne_zero (n : ℕ) : signedFactorialSequence n ≠ 0 := by
  rw [signedFactorialSequence, Finset.prod_ne_zero_iff]
  intro k _hk
  by_cases hk0 : k = 0
  · simp [hk0]
  · simp [hk0]

theorem signedFactorialSequence_sq (n : ℕ) :
    signedFactorialSequence n ^ 2 = factorialSquareSequence n := by
  rw [signedFactorialSequence, factorialSquareSequence, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro k _hk
  by_cases hk0 : k = 0
  · simp [hk0]
  · simp [hk0]

def signedFactorialGerm : NatGerm := signedFactorialSequence

theorem signedFactorialGerm_sq : signedFactorialGerm ^ 2 = factorialSquareGerm := by
  change (↑signedFactorialSequence : NatGerm) ^ 2 = ↑factorialSquareSequence
  rw [← Filter.Germ.coe_pow, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall signedFactorialSequence_sq

theorem signedFactorialGerm_isUnit : IsUnit signedFactorialGerm := by
  rw [isUnit_iff_exists_inv]
  refine ⟨(fun n : ℕ => (signedFactorialSequence n)⁻¹ : NatGerm), ?_⟩
  change (↑signedFactorialSequence : NatGerm) *
      ↑(fun n : ℕ => (signedFactorialSequence n)⁻¹) = 1
  rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun n =>
    mul_inv_cancel₀ (signedFactorialSequence_ne_zero n)

def signedFactorialEval (m : ℕ) :
    Polynomial (MvPolynomial (Fin m) (RatFunc ℂ)) →+* NatGerm :=
  Polynomial.eval₂RingHom (harmonicJetEval m) signedFactorialGerm

theorem signedFactorialEval_injective (m : ℕ) :
    Function.Injective (signedFactorialEval m) := by
  letI : Algebra (MvPolynomial (Fin m) (RatFunc ℂ)) NatGerm :=
    (harmonicJetEval m).toAlgebra
  have hsq : Transcendental (MvPolynomial (Fin m) (RatFunc ℂ))
      factorialSquareGerm := by
    rw [transcendental_iff]
    intro P hP
    apply factorialSquareEval_injective m
    rw [map_zero]
    simpa [factorialSquareEval, Polynomial.aeval_def] using! hP
  have hsigned : Transcendental (MvPolynomial (Fin m) (RatFunc ℂ))
      signedFactorialGerm := by
    intro halg
    apply hsq
    rw [← signedFactorialGerm_sq]
    exact halg.pow 2
  intro P Q hPQ
  apply sub_eq_zero.mp
  apply (transcendental_iff.mp hsigned) (P - Q)
  rw [Polynomial.aeval_def]
  change signedFactorialEval m (P - Q) = 0
  rw [map_sub, hPQ, sub_self]

def reciprocalSignedFactorialSequence (n : ℕ) : ℂ :=
  (signedFactorialSequence n)⁻¹

def reciprocalSignedFactorialGerm : NatGerm :=
  reciprocalSignedFactorialSequence

theorem signedFactorialGerm_mul_reciprocal :
    signedFactorialGerm * reciprocalSignedFactorialGerm = 1 := by
  change (↑signedFactorialSequence : NatGerm) *
      ↑reciprocalSignedFactorialSequence = 1
  rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
  exact Filter.Eventually.of_forall fun n =>
    mul_inv_cancel₀ (signedFactorialSequence_ne_zero n)

theorem reciprocalSignedFactorialGerm_isUnit : IsUnit reciprocalSignedFactorialGerm := by
  rw [isUnit_iff_exists_inv]
  exact ⟨signedFactorialGerm, by
    rw [mul_comm, signedFactorialGerm_mul_reciprocal]⟩

def reciprocalSignedFactorialEval (m : ℕ) :
    Polynomial (MvPolynomial (Fin m) (RatFunc ℂ)) →+* NatGerm :=
  Polynomial.eval₂RingHom (harmonicJetEval m) reciprocalSignedFactorialGerm

/-- The reciprocal signed factorial is transcendental over every finite generalized-harmonic
coordinate ring in eventual sequence germs. -/
theorem reciprocalSignedFactorialEval_injective (m : ℕ) :
    Function.Injective (reciprocalSignedFactorialEval m) := by
  letI : Algebra (MvPolynomial (Fin m) (RatFunc ℂ)) NatGerm :=
    (harmonicJetEval m).toAlgebra
  letI : Invertible signedFactorialGerm := signedFactorialGerm_isUnit.invertible
  have hsigned : Transcendental (MvPolynomial (Fin m) (RatFunc ℂ))
      signedFactorialGerm := by
    rw [transcendental_iff]
    intro P hP
    apply signedFactorialEval_injective m
    rw [map_zero]
    simpa [signedFactorialEval, Polynomial.aeval_def] using! hP
  have hinv : ⅟ signedFactorialGerm = reciprocalSignedFactorialGerm := by
    apply signedFactorialGerm_isUnit.mul_left_cancel
    rw [mul_invOf_self, signedFactorialGerm_mul_reciprocal]
  have hrecip : Transcendental (MvPolynomial (Fin m) (RatFunc ℂ))
      reciprocalSignedFactorialGerm := by
    intro halg
    apply hsigned
    apply (IsAlgebraic.invOf_iff
      (R := MvPolynomial (Fin m) (RatFunc ℂ))
      (x := signedFactorialGerm)).mp
    rwa [hinv]
  intro P Q hPQ
  apply sub_eq_zero.mp
  apply (transcendental_iff.mp hrecip) (P - Q)
  rw [Polynomial.aeval_def]
  change reciprocalSignedFactorialEval m (P - Q) = 0
  rw [map_sub, hPQ, sub_self]

/-- Coordinatewise affine substitution over `ℂ`. -/
def affineCoordinateMap (m : ℕ) (α β : Fin m → ℂ) :
    MvPolynomial (Fin m) ℂ →+* MvPolynomial (Fin m) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun j =>
    MvPolynomial.C (α j) * MvPolynomial.X j + MvPolynomial.C (β j)

def affineCoordinateMapInv (m : ℕ) (α β : Fin m → ℂ) :
    MvPolynomial (Fin m) ℂ →+* MvPolynomial (Fin m) ℂ :=
  MvPolynomial.eval₂Hom MvPolynomial.C fun j =>
    MvPolynomial.C (α j)⁻¹ * (MvPolynomial.X j - MvPolynomial.C (β j))

theorem affineCoordinateMap_injective (m : ℕ) {α β : Fin m → ℂ}
    (hα : ∀ j, α j ≠ 0) : Function.Injective (affineCoordinateMap m α β) := by
  have hcomp : (affineCoordinateMapInv m α β).comp (affineCoordinateMap m α β) =
      RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [affineCoordinateMap, affineCoordinateMapInv]
    · intro j
      simp [affineCoordinateMap, affineCoordinateMapInv]
      rw [← mul_assoc, ← MvPolynomial.C_mul]
      simp [hα j]
  apply Function.LeftInverse.injective
  intro P
  simpa using RingHom.congr_fun hcomp P

def complexToHarmonicRing (m : ℕ) :
    ℂ →+* MvPolynomial (Fin m) (RatFunc ℂ) :=
  MvPolynomial.C.comp (algebraMap ℂ (RatFunc ℂ))

/-- Send affine coordinate `j` to its harmonic affine form times factorial variable `T^(j+1)`. -/
def weightedAffineEmbedding (m : ℕ) (α β : Fin m → ℂ) :
    MvPolynomial (Fin m) ℂ →+*
      Polynomial (MvPolynomial (Fin m) (RatFunc ℂ)) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp (complexToHarmonicRing m)) fun j =>
    Polynomial.C
      (MvPolynomial.C (algebraMap ℂ (RatFunc ℂ) (α j)) * MvPolynomial.X j +
        MvPolynomial.C (algebraMap ℂ (RatFunc ℂ) (β j))) *
      Polynomial.X ^ ((j : ℕ) + 1)

theorem weightedAffineEmbedding_injective (m : ℕ) {α β : Fin m → ℂ}
    (hα : ∀ j, α j ≠ 0) : Function.Injective (weightedAffineEmbedding m α β) := by
  let coeffMap : MvPolynomial (Fin m) ℂ →+* MvPolynomial (Fin m) (RatFunc ℂ) :=
    MvPolynomial.map (algebraMap ℂ (RatFunc ℂ))
  let atOne : Polynomial (MvPolynomial (Fin m) (RatFunc ℂ)) →+*
      MvPolynomial (Fin m) (RatFunc ℂ) := Polynomial.evalRingHom 1
  have hcomp : atOne.comp (weightedAffineEmbedding m α β) =
      coeffMap.comp (affineCoordinateMap m α β) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [atOne, coeffMap, weightedAffineEmbedding, affineCoordinateMap,
        complexToHarmonicRing]
    · intro j
      simp [atOne, coeffMap, weightedAffineEmbedding, affineCoordinateMap,
        complexToHarmonicRing]
  intro P Q hPQ
  apply affineCoordinateMap_injective (m := m) (hα := hα)
  apply MvPolynomial.map_injective (algebraMap ℂ (RatFunc ℂ))
    (algebraMap ℂ (RatFunc ℂ)).injective
  have h := congrArg atOne hPQ
  change (atOne.comp (weightedAffineEmbedding m α β)) P =
    (atOne.comp (weightedAffineEmbedding m α β)) Q at h
  rw [hcomp] at h
  exact h

/-- The constant embedding of `ℂ` in the eventual sequence ring induced by rational evaluation. -/
def complexNatGerm : ℂ →+* NatGerm := ratNatEval.comp RatFunc.C

local instance natGermAlgebra : Algebra ℂ NatGerm := complexNatGerm.toAlgebra

/-- A weighted affine harmonic family in the reciprocal factorial coordinate. -/
def weightedAffineGerm (m : ℕ) (α β : Fin m → ℂ) (j : Fin m) : NatGerm :=
  reciprocalSignedFactorialGerm ^ ((j : ℕ) + 1) *
    (algebraMap ℂ NatGerm (α j) * harmonicJetGerm (j : ℕ) +
      algebraMap ℂ NatGerm (β j))

def weightedAffineGermEval (m : ℕ) (α β : Fin m → ℂ) :
    MvPolynomial (Fin m) ℂ →+* NatGerm :=
  MvPolynomial.eval₂Hom (algebraMap ℂ NatGerm) (weightedAffineGerm m α β)

theorem weightedAffineGermEval_eq_comp (m : ℕ) (α β : Fin m → ℂ) :
    weightedAffineGermEval m α β =
      (reciprocalSignedFactorialEval m).comp (weightedAffineEmbedding m α β) := by
  have hbase : algebraMap ℂ NatGerm = complexNatGerm := rfl
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [weightedAffineGermEval, reciprocalSignedFactorialEval,
      weightedAffineEmbedding, complexToHarmonicRing, harmonicJetEval]
    rw [hbase]
    rfl
  · intro j
    simp [weightedAffineGermEval, weightedAffineGerm,
      reciprocalSignedFactorialEval, weightedAffineEmbedding, harmonicJetEval]
    rw [hbase]
    simp [complexNatGerm]
    ring

theorem weightedAffineGermEval_injective (m : ℕ) {α β : Fin m → ℂ}
    (hα : ∀ j, α j ≠ 0) : Function.Injective (weightedAffineGermEval m α β) := by
  rw [weightedAffineGermEval_eq_comp]
  exact (reciprocalSignedFactorialEval_injective m).comp
    (weightedAffineEmbedding_injective m hα)

/-- Every finite weighted affine harmonic family with nonzero coordinate slopes is algebraically
independent over `ℂ`. -/
theorem algebraicIndependent_weightedAffineGerm (m : ℕ) {α β : Fin m → ℂ}
    (hα : ∀ j, α j ≠ 0) :
    AlgebraicIndependent ℂ (weightedAffineGerm m α β) := by
  rw [algebraicIndependent_iff]
  intro P hP
  apply weightedAffineGermEval_injective m hα
  rw [map_zero]
  simpa [weightedAffineGermEval, MvPolynomial.aeval_def] using hP

/-- The nonzero harmonic-coordinate slope in the exact logarithm of a scaled Gamma pole germ.
Coordinate `j` is the coefficient of order `j + 1`. -/
def gammaPoleLogSlope (j : ℕ) : ℂ := -1 / (j + 1).factorial

/-- The constant part in the exact logarithm of a scaled Gamma pole germ. -/
def gammaPoleLogConstant (j : ℕ) : ℂ :=
  if j = 0 then Real.eulerMascheroniConstant
  else riemannZeta (j + 1) / (j + 1)

/-- The eventual sequence germ of the order-`j + 1` logarithmic coefficient of the scaled Gamma
pole family. -/
def gammaPoleLogCoefficientGerm (j : ℕ) : NatGerm :=
  reciprocalSignedFactorialGerm ^ (j + 1) *
    (algebraMap ℂ NatGerm (gammaPoleLogSlope j) * harmonicJetGerm j +
      algebraMap ℂ NatGerm (gammaPoleLogConstant j))

theorem gammaPoleLogSlope_ne_zero (j : ℕ) : gammaPoleLogSlope j ≠ 0 := by
  unfold gammaPoleLogSlope
  exact div_ne_zero (neg_ne_zero.mpr one_ne_zero)
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (j + 1)))

theorem algebraicIndependent_gammaPoleLogCoefficientGerm_fin (m : ℕ) :
    AlgebraicIndependent ℂ
      (fun j : Fin m => gammaPoleLogCoefficientGerm (j : ℕ)) := by
  simpa [gammaPoleLogCoefficientGerm, weightedAffineGerm] using!
    (algebraicIndependent_weightedAffineGerm m
      (hα := fun j => gammaPoleLogSlope_ne_zero (j : ℕ))
      (β := fun j => gammaPoleLogConstant (j : ℕ)))

/-- The exact logarithmic coefficients of the complete factorially rescaled Gamma pole family are
one countably algebraically independent family of eventual sequences over `ℂ`. -/
theorem algebraicIndependent_gammaPoleLogCoefficientGerm :
    AlgebraicIndependent ℂ gammaPoleLogCoefficientGerm := by
  apply algebraicIndependent_of_finite_type
  intro t ht
  rcases ht.bddAbove with ⟨k, hk⟩
  let f : t → Fin (k + 1) := fun i => ⟨i, Nat.lt_succ_of_le (hk i.2)⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    exact Fin.ext_iff.mp hij
  have hprefix := algebraicIndependent_gammaPoleLogCoefficientGerm_fin (k + 1)
  have hsub := hprefix.comp f hf
  simpa [f, Function.comp_def] using hsub

end

end GaloisForLFunctions
