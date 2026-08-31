import GaloisForLFunctions.HTGeometry.RatFuncChainRule
import GaloisForLFunctions.HTGeometry.TranscendentalMobius
import GaloisForLFunctions.HTGeometry.RittRationalSubstitutionOrder

/-!
# From Ritt's first-order relation to the rational cocycle

A Poincaré function `y` of a rational map `R` at a fixed point with multiplier `λ` lives in a
differential field carrying the scaling operator `S : f(z) ↦ f(λz)`, and satisfies

`S y = R(y)`,   `S z = λ z`,   `d ∘ S = λ · S ∘ d`.

Ritt's theorem says that a differentially algebraic `y` satisfies an order-one relation
`(d y)^r = z^j A(y)` with `A` rational.  Applying `S` to that relation and using the chain rule
`d(R(y)) = R′(y)·d y` turns it into

`R′(y)^r A(y) = λ^{r+j} A(R(y))`,

and evaluation at a transcendental element is injective, so the identity descends to the rational
function field: `A` is a rational `(−r)`-differential invariant of `R` up to the constant
`λ^{−(r+j)}`.  That is exactly the affine transport equation whose solvability the fibre count
refutes.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {F L : Type*} [Field F] [CharZero F] [Field L] [Algebra F L]

noncomputable section

omit [CharZero F] in
theorem ratFuncEval_polyImage (y : L) (hy : Transcendental F y) (N : F[X]) :
    ratFuncEval y hy (algebraMap F[X] (RatFunc F) N) = Polynomial.aeval y N := by
  rw [algebraMap_eq_aeval_X, ← Polynomial.aeval_algHom_apply, ratFuncEval_X]

omit [CharZero F] in
/-- The chain rule for the evaluation of a polynomial. -/
theorem derivation_aeval (d : Derivation F L L) (y : L) (N : F[X]) :
    d (Polynomial.aeval y N) = Polynomial.aeval y (derivative N) * d y := by
  induction N using Polynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq]
      ring
  | monomial n a ih =>
      have hfac : (Polynomial.C a * X ^ (n + 1) : F[X]) = (Polynomial.C a * X ^ n) * X := by ring
      rw [hfac, map_mul, Polynomial.aeval_X, Derivation.leibniz, ih]
      simp only [smul_eq_mul, derivative_mul, derivative_X, mul_one, map_add, map_mul,
        Polynomial.aeval_X]
      ring

/-- **The chain rule for the evaluation of a rational function.** -/
theorem derivation_ratFuncEval (d : Derivation F L L) {y : L} (hy : Transcendental F y)
    (Q : RatFunc F) :
    d (ratFuncEval y hy Q) = ratFuncEval y hy (ratFuncDeriv Q) * d y := by
  have hz : ratFuncDeriv (0 : RatFunc F) = 0 := by
    rw [← ratFuncDerivation_apply, map_zero]
  rcases eq_or_ne Q 0 with rfl | hQ0
  · simp [hz]
  · have hden : Q.denom ≠ 0 := RatFunc.denom_ne_zero Q
    have hdenR : algebraMap F[X] (RatFunc F) Q.denom ≠ 0 := algebraMap_ne_zero_of_ne_zero hden
    have hE : Polynomial.aeval y Q.denom ≠ 0 := by
      rw [← ratFuncEval_polyImage y hy]
      intro h
      exact hdenR (ratFuncEval_injective y hy (by rw [h, map_zero]))
    have hQeq : Q = algebraMap F[X] (RatFunc F) Q.num / algebraMap F[X] (RatFunc F) Q.denom :=
      (RatFunc.num_div_denom Q).symm
    have hDQ : ratFuncDeriv Q
        = algebraMap F[X] (RatFunc F) (derivative Q.num * Q.denom - Q.num * derivative Q.denom)
          / algebraMap F[X] (RatFunc F) (Q.denom ^ 2) := by
      conv_lhs => rw [hQeq]
      exact ratFuncDeriv_div hden
    conv_lhs => rw [hQeq]
    rw [map_div₀, ratFuncEval_polyImage, ratFuncEval_polyImage, Derivation.leibniz_div,
      derivation_aeval, derivation_aeval, hDQ, map_div₀, ratFuncEval_polyImage,
      ratFuncEval_polyImage, map_sub, map_mul, map_mul, map_pow]
    simp only [smul_eq_mul]
    field_simp

omit [CharZero F] in
/-- **Substitution intertwines evaluation with an algebra endomorphism.** -/
theorem algHom_ratFuncEval {y : L} (hy : Transcendental F y) {P : RatFunc F}
    (hP : ¬ ∃ c : F, P = RatFunc.C c) (S : L →ₐ[F] L)
    (hSy : S y = ratFuncEval y hy P) (Q : RatFunc F) :
    S (ratFuncEval y hy Q) = ratFuncEval y hy (ratFuncSubstitutionAlgHom P hP Q) := by
  have hext : S.comp (ratFuncEval y hy)
      = (ratFuncEval y hy).comp (ratFuncSubstitutionAlgHom P hP) := by
    refine ratFunc_algHom_ext ?_
    simp [hSy]
  exact AlgHom.congr_fun hext Q

/-- **Ritt's relation is a rational cocycle.** -/
theorem isRatAffineTransport_of_ritt_relation
    (d : Derivation F L L) (S : L →ₐ[F] L)
    {z y : L} {lam : F} (hlam : lam ≠ 0) (hz : z ≠ 0)
    (hSz : S z = algebraMap F L lam * z)
    (hdS : ∀ x : L, d (S x) = algebraMap F L lam * S (d x))
    (hy : Transcendental F y)
    {R A : RatFunc F} (hR : ¬ ∃ c : F, R = RatFunc.C c) (hA : A ≠ 0)
    (hSy : S y = ratFuncEval y hy R)
    {r j : ℤ} (hr : r ≠ 0)
    (hritt : (d y) ^ r = z ^ j * ratFuncEval y hy A) :
    IsRatAffineTransport R hR (-r) (RatFunc.C (lam ^ (-(r + j)))) 0 A := by
  set Lam : L := algebraMap F L lam with hLam
  have hlamL : Lam ≠ 0 := (map_ne_zero_iff _ (algebraMap F L).injective).mpr hlam
  have hzj : z ^ j ≠ 0 := zpow_ne_zero j hz
  have hevA : ratFuncEval y hy A ≠ 0 := by
    intro h
    exact hA (ratFuncEval_injective y hy (by rw [h, map_zero]))
  have hdy : d y ≠ 0 := by
    intro h
    rw [h, zero_zpow r hr] at hritt
    exact (mul_ne_zero hzj hevA) hritt.symm
  have hchain : d (S y) = ratFuncEval y hy (ratFuncDeriv R) * d y := by
    rw [hSy, derivation_ratFuncEval d hy R]
  have hSdy : S (d y) = Lam⁻¹ * (ratFuncEval y hy (ratFuncDeriv R) * d y) := by
    have h := hdS y
    rw [hchain] at h
    field_simp
    linear_combination -h
  have hSinj : Function.Injective (S : L → L) := S.toRingHom.injective
  have hevR : ratFuncEval y hy (ratFuncDeriv R) ≠ 0 := by
    intro h
    rw [h, zero_mul, mul_zero] at hSdy
    exact hdy (hSinj (by rw [hSdy, map_zero]))
  have hRd : ratFuncDeriv R ≠ 0 := by
    intro h
    rw [h, map_zero] at hevR
    exact hevR rfl
  have hkey := congrArg S hritt
  rw [map_zpow₀, map_mul, map_zpow₀, hSz, hSdy,
    algHom_ratFuncEval hy hR S hSy] at hkey
  set a : L := ratFuncEval y hy (ratFuncDeriv R) with ha
  set b : L := ratFuncEval y hy A with hb
  set c : L := ratFuncEval y hy (ratFuncSubstitutionAlgHom R hR A) with hc
  have hLamr : Lam ^ r ≠ 0 := zpow_ne_zero r hlamL
  have hkey2 : (Lam ^ r)⁻¹ * (a ^ r * (z ^ j * b)) = Lam ^ j * z ^ j * c := by
    simp only [mul_zpow, inv_zpow] at hkey
    rw [hritt] at hkey
    linear_combination hkey
  have h1 : a ^ r * (z ^ j * b) = Lam ^ r * (Lam ^ j * z ^ j * c) := by
    have h : Lam ^ r * ((Lam ^ r)⁻¹ * (a ^ r * (z ^ j * b)))
        = Lam ^ r * (Lam ^ j * z ^ j * c) := by rw [hkey2]
    rw [← mul_assoc, mul_inv_cancel₀ hLamr, one_mul] at h
    exact h
  have h2 : z ^ j * (a ^ r * b) = z ^ j * (Lam ^ (r + j) * c) := by
    rw [zpow_add₀ hlamL]
    linear_combination h1
  have hcancel : a ^ r * b = Lam ^ (r + j) * c := mul_left_cancel₀ hzj h2
  have hdesc : ratFuncEval y hy ((ratFuncDeriv R) ^ r * A)
      = ratFuncEval y hy (RatFunc.C (lam ^ (r + j)) * ratFuncSubstitutionAlgHom R hR A) := by
    rw [map_mul, map_mul, map_zpow₀, ratFuncEval_C, map_zpow₀]
    exact hcancel
  have hrat : (ratFuncDeriv R) ^ r * A
      = RatFunc.C (lam ^ (r + j)) * ratFuncSubstitutionAlgHom R hR A :=
    ratFuncEval_injective y hy hdesc
  have hCne : (RatFunc.C (lam ^ (r + j)) : RatFunc F) ≠ 0 := by
    have := zpow_ne_zero (r + j) hlam
    set w := lam ^ (r + j) with hw
    simpa using this
  have hRr : (ratFuncDeriv R) ^ r ≠ 0 := zpow_ne_zero r hRd
  have hCinv : (RatFunc.C (lam ^ (-(r + j))) : RatFunc F)
      = (RatFunc.C (lam ^ (r + j)))⁻¹ := by
    rw [← map_inv₀, zpow_neg]
  rw [IsRatAffineTransport, add_zero, zpow_neg, hCinv]
  refine mul_left_cancel₀ (mul_ne_zero hCne hRr) ?_
  field_simp
  linear_combination -hrat

omit [CharZero F] in
/-- Two evaluations related by an algebra endomorphism. -/
theorem algHom_ratFuncEval_shift {y : L} (hy : Transcendental F y) (T : L →ₐ[F] L)
    (hTy : Transcendental F (T y)) (Q : RatFunc F) :
    T (ratFuncEval y hy Q) = ratFuncEval (T y) hTy Q := by
  have hext : T.comp (ratFuncEval y hy) = ratFuncEval (T y) hTy := by
    refine ratFunc_algHom_ext ?_
    simp
  exact AlgHom.congr_fun hext Q

omit [CharZero F] in
/-- Evaluation at a value of the map factors through substitution. -/
theorem ratFuncEval_of_eq_eval {y w : L} (hy : Transcendental F y) (hw : Transcendental F w)
    {R : RatFunc F} (hR : ¬ ∃ c : F, R = RatFunc.C c) (hyw : y = ratFuncEval w hw R)
    (Q : RatFunc F) :
    ratFuncEval y hy Q = ratFuncEval w hw (ratFuncSubstitutionAlgHom R hR Q) := by
  have hext : ratFuncEval y hy = (ratFuncEval w hw).comp (ratFuncSubstitutionAlgHom R hR) := by
    refine ratFunc_algHom_ext ?_
    simp [hyw]
  exact AlgHom.congr_fun hext Q

/-- **Ritt's relation is a rational cocycle, contracting form.**  The shift here is the contracting
one, `T : f(z) ↦ f(z/λ)`, which is the operator an analytic germ field at a repelling fixed point
actually carries; the Poincaré equation then reads `y = R(T y)`. -/
theorem isRatAffineTransport_of_ritt_relation_contracting
    (d : Derivation F L L) (T : L →ₐ[F] L)
    {z y : L} {mu : F} (hmu : mu ≠ 0) (hz : z ≠ 0)
    (hTz : T z = algebraMap F L mu * z)
    (hdT : ∀ x : L, d (T x) = algebraMap F L mu * T (d x))
    (hy : Transcendental F y) (hTy : Transcendental F (T y))
    {R A : RatFunc F} (hR : ¬ ∃ c : F, R = RatFunc.C c) (hA : A ≠ 0)
    (hPoin : y = ratFuncEval (T y) hTy R)
    {r j : ℤ} (hr : r ≠ 0)
    (hritt : (d y) ^ r = z ^ j * ratFuncEval y hy A) :
    IsRatAffineTransport R hR (-r) (RatFunc.C (mu ^ (r + j))) 0 A := by
  set Mu : L := algebraMap F L mu with hMu
  have hmuL : Mu ≠ 0 := (map_ne_zero_iff _ (algebraMap F L).injective).mpr hmu
  have hzj : z ^ j ≠ 0 := zpow_ne_zero j hz
  have hevA : ratFuncEval y hy A ≠ 0 := by
    intro h
    exact hA (ratFuncEval_injective y hy (by rw [h, map_zero]))
  have hdy : d y ≠ 0 := by
    intro h
    rw [h, zero_zpow r hr] at hritt
    exact (mul_ne_zero hzj hevA) hritt.symm
  -- differentiating the Poincaré equation
  have hchain : d y = ratFuncEval (T y) hTy (ratFuncDeriv R) * d (T y) := by
    conv_lhs => rw [hPoin]
    exact derivation_ratFuncEval d hTy R
  have hevR : ratFuncEval (T y) hTy (ratFuncDeriv R) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hchain
    exact hdy hchain
  have hRd : ratFuncDeriv R ≠ 0 := by
    intro h
    rw [h, map_zero] at hevR
    exact hevR rfl
  have hdTy : d (T y) = d y / ratFuncEval (T y) hTy (ratFuncDeriv R) := by
    rw [hchain]
    field_simp
  have hTdy : T (d y) = Mu⁻¹ * (d y / ratFuncEval (T y) hTy (ratFuncDeriv R)) := by
    have h := hdT y
    rw [hdTy] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hmuL, one_mul]
  -- transport Ritt's relation along the contracting shift
  have hkey := congrArg T hritt
  rw [map_zpow₀, map_mul, map_zpow₀, hTz, hTdy,
    algHom_ratFuncEval_shift hy T hTy A] at hkey
  set a : L := ratFuncEval (T y) hTy (ratFuncDeriv R) with ha
  set b : L := ratFuncEval y hy A with hb
  set c : L := ratFuncEval (T y) hTy A with hc
  have hMur : Mu ^ r ≠ 0 := zpow_ne_zero r hmuL
  have har : a ^ r ≠ 0 := zpow_ne_zero r hevR
  have hkey2 : (Mu ^ r)⁻¹ * ((z ^ j * b) / a ^ r) = Mu ^ j * z ^ j * c := by
    simp only [mul_zpow, inv_zpow, div_zpow] at hkey
    rw [hritt] at hkey
    linear_combination hkey
  have h1 : b = Mu ^ r * a ^ r * Mu ^ j * c := by
    have h : Mu ^ r * a ^ r * ((Mu ^ r)⁻¹ * ((z ^ j * b) / a ^ r))
        = Mu ^ r * a ^ r * (Mu ^ j * z ^ j * c) := by rw [hkey2]
    field_simp at h
    linear_combination h
  have hcancel : b = Mu ^ (r + j) * (a ^ r * c) := by
    rw [zpow_add₀ hmuL]
    linear_combination h1
  -- descend to the rational function field
  have hbeq : b = ratFuncEval (T y) hTy (ratFuncSubstitutionAlgHom R hR A) := by
    rw [hb, ratFuncEval_of_eq_eval hy hTy hR hPoin A]
  have hdesc : ratFuncEval (T y) hTy (ratFuncSubstitutionAlgHom R hR A)
      = ratFuncEval (T y) hTy (RatFunc.C (mu ^ (r + j)) * ((ratFuncDeriv R) ^ r * A)) := by
    rw [map_mul, ratFuncEval_C, map_mul, map_zpow₀, map_zpow₀, ← hbeq]
    exact hcancel
  have hrat : ratFuncSubstitutionAlgHom R hR A
      = RatFunc.C (mu ^ (r + j)) * ((ratFuncDeriv R) ^ r * A) :=
    ratFuncEval_injective (T y) hTy hdesc
  have hRr : (ratFuncDeriv R) ^ r ≠ 0 := zpow_ne_zero r hRd
  rw [IsRatAffineTransport, add_zero, zpow_neg, hrat]
  field_simp

end

end GaloisForLFunctions.HTGeometry
