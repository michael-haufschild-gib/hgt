import GaloisForLFunctions.HTGeometry.QDifferenceLaurentOneVariable
import GaloisForLFunctions.HTGeometry.EulerOrdinaryDerivationBridge

/-!
# Ramification of the coordinate

Substituting `z = w^q` embeds `k((z))` into `k((w))` by stretching exponents.  The dilation by
`β^q` in `z` becomes the dilation by `β` in `w`, the Euler operator is multiplied by `q`, and a
rational function of `z` becomes a rational function of `w`.  This is what makes a first-order
`q`-difference equation whose multiplier is a *rational* power of the dilation parameter accessible
to the one-variable model.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

/-- Stretching the exponents by a positive integer. -/
def stretchHom (q : ℕ) : ℤ →+ ℤ := AddMonoidHom.mulLeft (q : ℤ)

theorem stretchHom_apply (q : ℕ) (n : ℤ) : stretchHom q n = (q : ℤ) * n := rfl

theorem stretchHom_injective {q : ℕ} (hq : 0 < q) : Function.Injective (stretchHom q) := by
  intro m n h
  rw [stretchHom_apply, stretchHom_apply] at h
  exact mul_left_cancel₀ (by exact_mod_cast hq.ne') h

theorem stretchHom_le_iff {q : ℕ} (hq : 0 < q) (m n : ℤ) :
    stretchHom q m ≤ stretchHom q n ↔ m ≤ n := by
  rw [stretchHom_apply, stretchHom_apply]
  have hqz : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  constructor
  · intro h
    exact le_of_mul_le_mul_left h hqz
  · intro h
    exact mul_le_mul_of_nonneg_left h (le_of_lt hqz)

/-- The ramification `z = w^q` of Laurent series. -/
def ramify (q : ℕ) (hq : 0 < q) : LaurentSeries k →+* LaurentSeries k :=
  HahnSeries.embDomainRingHom (stretchHom q) (stretchHom_injective hq) (stretchHom_le_iff hq)

@[simp]
theorem coeff_ramify_mul (q : ℕ) (hq : 0 < q) (f : LaurentSeries k) (n : ℤ) :
    (ramify q hq f).coeff ((q : ℤ) * n) = f.coeff n := by
  have := HahnSeries.embDomain_coeff (f := ⟨⟨stretchHom q, stretchHom_injective hq⟩,
    stretchHom_le_iff hq _ _⟩) (x := f) (a := n)
  simpa [ramify, stretchHom_apply] using this

theorem coeff_ramify_of_not_dvd (q : ℕ) (hq : 0 < q) (f : LaurentSeries k) {m : ℤ}
    (hm : ∀ n : ℤ, (q : ℤ) * n ≠ m) : (ramify q hq f).coeff m = 0 := by
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨n, rfl⟩
  exact hm n rfl

/-- **Ramification turns a dilation by `β^q` into a dilation by `β`.** -/
theorem ramify_innerDilation (q : ℕ) (hq : 0 < q) (β : k) (hβ : β ≠ 0) (f : LaurentSeries k) :
    ramify q hq (innerDilation (β ^ q) (pow_ne_zero q hβ) f)
      = innerDilation β hβ (ramify q hq f) := by
  refine HahnSeries.coeff_inj.mp (funext fun m => ?_)
  by_cases hm : ∃ n : ℤ, (q : ℤ) * n = m
  · obtain ⟨n, rfl⟩ := hm
    rw [coeff_ramify_mul, coeff_innerDilation, coeff_innerDilation, coeff_ramify_mul,
      ← zpow_natCast β q, ← zpow_mul]
  · push Not at hm
    rw [coeff_ramify_of_not_dvd q hq _ hm, coeff_innerDilation,
      coeff_ramify_of_not_dvd q hq _ hm, mul_zero]

/-- **Ramification multiplies the Euler operator by `q`.** -/
theorem ramify_innerEuler (q : ℕ) (hq : 0 < q) (f : LaurentSeries k) :
    innerEuler (ramify q hq f) = ramify q hq (HahnSeries.C (q : k) * innerEuler f) := by
  refine HahnSeries.coeff_inj.mp (funext fun m => ?_)
  by_cases hm : ∃ n : ℤ, (q : ℤ) * n = m
  · obtain ⟨n, rfl⟩ := hm
    rw [coeff_innerEuler, coeff_ramify_mul, coeff_ramify_mul, coeff_C_mul, coeff_innerEuler]
    push_cast
    ring
  · push Not at hm
    rw [coeff_innerEuler, coeff_ramify_of_not_dvd q hq _ hm,
      coeff_ramify_of_not_dvd q hq _ hm, mul_zero]

/-! ## The ramified rational function field -/

/-- Substituting `X^q` for `X` in a polynomial. -/
def polyPow (q : ℕ) : Polynomial k →+* Polynomial k :=
  (Polynomial.aeval (Polynomial.X ^ q : Polynomial k)).toRingHom

theorem polyPow_apply (q : ℕ) (p : Polynomial k) :
    polyPow q p = p.comp (Polynomial.X ^ q) := by
  rw [polyPow]
  show Polynomial.aeval (Polynomial.X ^ q : Polynomial k) p = _
  rw [Polynomial.aeval_def, Polynomial.comp, Polynomial.algebraMap_eq]

theorem polyPow_injective {q : ℕ} (hq : 0 < q) : Function.Injective (polyPow (k := k) q) := by
  intro p₁ p₂ h
  rw [polyPow_apply, polyPow_apply] at h
  have hsub : (p₁ - p₂).comp (Polynomial.X ^ q : Polynomial k) = 0 := by
    rw [Polynomial.sub_comp, h, sub_self]
  have hXq : (Polynomial.X ^ q : Polynomial k) ≠ Polynomial.C ((Polynomial.X ^ q).coeff 0) := by
    intro hcon
    have hdeg := congrArg Polynomial.natDegree hcon
    rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C] at hdeg
    omega
  rcases Polynomial.comp_eq_zero_iff.mp hsub with h0 | ⟨_, h2⟩
  · exact sub_eq_zero.mp h0
  · exact absurd h2 hXq

/-- The ramification `z = w^q` of rational functions. -/
def ratFuncPow (q : ℕ) (hq : 0 < q) : RatFunc k →+* RatFunc k :=
  RatFunc.mapRingHom (polyPow q)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyPow_injective hq))

theorem ratFuncPow_div (q : ℕ) (hq : 0 < q) (p s : Polynomial k) :
    ratFuncPow q hq (algebraMap (Polynomial k) (RatFunc k) p /
        algebraMap (Polynomial k) (RatFunc k) s)
      = algebraMap (Polynomial k) (RatFunc k) (polyPow q p) /
        algebraMap (Polynomial k) (RatFunc k) (polyPow q s) :=
  RatFunc.map_apply_div (polyPow q)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyPow_injective hq)) p s

theorem ramify_algebraMap_const (q : ℕ) (hq : 0 < q) (c : k) :
    ramify q hq (algebraMap (RatFunc k) (LaurentSeries k) (algebraMap k (RatFunc k) c))
      = algebraMap (RatFunc k) (LaurentSeries k) (algebraMap k (RatFunc k) c) := by
  rw [algebraMap_const_laurentSeries, ← HahnSeries.C_apply]
  exact HahnSeries.embDomainRingHom_C

theorem ramify_algebraMap_k (q : ℕ) (hq : 0 < q) (c : k) :
    ramify q hq (algebraMap k (LaurentSeries k) c) = algebraMap k (LaurentSeries k) c := by
  rw [algebraMap_k_laurentSeries]
  exact HahnSeries.embDomainRingHom_C

theorem ramify_algebraMap_X (q : ℕ) (hq : 0 < q) :
    ramify q hq (algebraMap (RatFunc k) (LaurentSeries k) (RatFunc.X : RatFunc k))
      = algebraMap (RatFunc k) (LaurentSeries k) ((RatFunc.X : RatFunc k) ^ q) := by
  rw [map_pow, RatFunc.coe_X]
  refine HahnSeries.coeff_inj.mp (funext fun m => ?_)
  have hqz : ((q : ℤ)) ≠ 0 := by exact_mod_cast hq.ne'
  by_cases hm : ∃ j : ℤ, (q : ℤ) * j = m
  · obtain ⟨j, rfl⟩ := hm
    rw [coeff_ramify_mul, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one]
    by_cases hj : j = 1
    · subst hj
      rw [HahnSeries.coeff_single_same, mul_one, HahnSeries.coeff_single_same]
    · rw [HahnSeries.coeff_single_of_ne hj, HahnSeries.coeff_single_of_ne ?_]
      intro hcon
      refine hj ?_
      have hmul : (q : ℤ) * j = (q : ℤ) * 1 := by
        rw [mul_one]
        simpa using hcon
      exact mul_left_cancel₀ hqz hmul
  · push Not at hm
    rw [coeff_ramify_of_not_dvd q hq _ hm, HahnSeries.single_pow, one_pow, nsmul_eq_mul, mul_one,
      HahnSeries.coeff_single_of_ne ?_]
    intro hcon
    exact hm 1 (by rw [mul_one]; simpa using hcon.symm)

theorem ramify_algebraMap_polynomial (q : ℕ) (hq : 0 < q) (p : Polynomial k) :
    ramify q hq (algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap (Polynomial k) (RatFunc k) p))
      = algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap (Polynomial k) (RatFunc k) (polyPow q p)) := by
  induction p using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | monomial n c =>
      have hmono : (Polynomial.monomial n c : Polynomial k)
          = Polynomial.C c * Polynomial.X ^ n := (Polynomial.C_mul_X_pow_eq_monomial).symm
      have hpp : polyPow q (Polynomial.monomial n c)
          = Polynomial.C c * (Polynomial.X ^ q) ^ n := by
        rw [polyPow_apply, hmono, Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_pow_comp]
      have hCc : algebraMap (Polynomial k) (RatFunc k) (Polynomial.C c)
          = algebraMap k (RatFunc k) c := (algebraMap_eq_toRF_C c).symm
      have hXX : algebraMap (Polynomial k) (RatFunc k) Polynomial.X = (RatFunc.X : RatFunc k) :=
        RatFunc.algebraMap_X
      rw [hpp, hmono, map_mul, map_mul, map_pow, map_pow, map_mul, map_mul, map_pow, map_pow,
        hCc, hXX, ramify_algebraMap_const, map_pow, ramify_algebraMap_X, map_pow, map_mul,
        map_pow, map_pow, hXX]

theorem ramify_algebraMap (q : ℕ) (hq : 0 < q) (r : RatFunc k) :
    ramify q hq (algebraMap (RatFunc k) (LaurentSeries k) r)
      = algebraMap (RatFunc k) (LaurentSeries k) (ratFuncPow q hq r) := by
  refine RatFunc.induction_on (P := fun r =>
    ramify q hq (algebraMap (RatFunc k) (LaurentSeries k) r)
      = algebraMap (RatFunc k) (LaurentSeries k) (ratFuncPow q hq r)) r ?_
  intro p s _
  rw [ratFuncPow_div, map_div₀, map_div₀, map_div₀, ramify_algebraMap_polynomial,
    ramify_algebraMap_polynomial]

/-- The differential structure of `k((w))` for which the ramification is a differential
homomorphism: the Euler operator divided by the ramification index. -/
@[reducible] def ramifiedDifferential (q : ℕ) : Differential (LaurentSeries k) :=
  hahnScaledDifferential (Int.castAddHom k) (HahnSeries.C ((q : k)⁻¹))

theorem ramifiedDifferential_deriv (q : ℕ) (f : LaurentSeries k) :
    (ramifiedDifferential (k := k) q).deriv f = HahnSeries.C ((q : k)⁻¹) * innerEuler f :=
  hahnScaledDifferential_deriv _ _ _

/-- **The ramification is a differential homomorphism** for the rescaled derivation. -/
theorem ramify_deriv [CharZero k] (q : ℕ) (hq : 0 < q) (f : LaurentSeries k) :
    (ramifiedDifferential (k := k) q).deriv (ramify q hq f) = ramify q hq (innerEuler f) := by
  have hqne : (q : k) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [ramifiedDifferential_deriv, ramify_innerEuler,
    show ramify q hq ((HahnSeries.C (q : k) : LaurentSeries k) * innerEuler f)
      = ramify q hq (HahnSeries.C (q : k)) * ramify q hq (innerEuler f) from map_mul _ _ _,
    show ramify q hq (HahnSeries.C (q : k) : LaurentSeries k) = HahnSeries.C (q : k) from
      HahnSeries.embDomainRingHom_C,
    ← mul_assoc,
    show (HahnSeries.C ((q : k)⁻¹) : LaurentSeries k) * HahnSeries.C (q : k) = 1 from by
      rw [← map_mul, inv_mul_cancel₀ hqne, map_one], one_mul]

/-! ## Transport of hypertranscendence along the ramification -/

theorem ramify_aeval {ι : Type*} (q : ℕ) (hq : 0 < q) (v : ι → LaurentSeries k)
    (p : MvPolynomial ι (RatFunc k)) :
    ramify q hq (MvPolynomial.aeval v p)
      = MvPolynomial.aeval (fun i => ramify q hq (v i))
        (MvPolynomial.map (ratFuncPow q hq) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [ramify_algebraMap]
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]
  | mul_X p i h => simp [h]

/-- The jets of a ramified series for the rescaled derivation are the ramified jets. -/
theorem differentialJet_ramify [CharZero k] (q : ℕ) (hq : 0 < q) (n : ℕ) (f : LaurentSeries k) :
    @differentialJet (LaurentSeries k) _ (ramifiedDifferential (k := k) q) n (ramify q hq f)
      = ramify q hq (@differentialJet (LaurentSeries k) _ (innerDifferential (k := k)) n f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      show @differentialJet (LaurentSeries k) _ (ramifiedDifferential (k := k) q) n
          ((ramifiedDifferential (k := k) q).deriv (ramify q hq f))
        = ramify q hq (@differentialJet (LaurentSeries k) _ (innerDifferential (k := k)) n
          ((innerDifferential (k := k)).deriv f))
      rw [ramify_deriv q hq f]
      exact ih _

set_option maxHeartbeats 1000000 in
/-- **The ramification transports differential algebraicity.**  If a Laurent series is
differentially algebraic over `k(z)`, its ramified image is differentially algebraic over `k(w)`
for the rescaled derivation. -/
theorem differentialAlgebraicOver_ramify [CharZero k] (q : ℕ) (hq : 0 < q) {R : LaurentSeries k}
    (hR : @DifferentialAlgebraicOver (RatFunc k) (LaurentSeries k) _ _ _
      (innerDifferential (k := k)) R) :
    @DifferentialAlgebraicOver (RatFunc k) (LaurentSeries k) _ _ _
      (ramifiedDifferential (k := k) q) (ramify q hq R) := by
  intro hind
  refine hR ?_
  rw [DifferentialIndependent, algebraicIndependent_iff] at hind ⊢
  intro p hp
  have hramify := congrArg (ramify q hq) hp
  rw [map_zero, ramify_aeval] at hramify
  have hjets : (fun i : Unit × ℕ => ramify q hq
      (@differentialJet (LaurentSeries k) _ (innerDifferential (k := k)) i.2 R))
      = fun i : Unit × ℕ => @differentialJet (LaurentSeries k) _
        (ramifiedDifferential (k := k) q) i.2 (ramify q hq R) := by
    funext i
    exact (differentialJet_ramify q hq i.2 R).symm
  rw [hjets] at hramify
  have hmap := hind (MvPolynomial.map (ratFuncPow q hq) p) hramify
  have hinj : Function.Injective (ratFuncPow q hq) :=
    RatFunc.map_injective (R := k) (S := k) (polyPow (k := k) q)
      (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (polyPow_injective hq))
      (polyPow_injective hq)
  refine MvPolynomial.map_injective _ hinj ?_
  rw [hmap, map_zero]

set_option maxHeartbeats 1000000 in
/-- **Differential algebraicity for the rescaled derivation is the same as for the Euler
derivation.** -/
theorem differentialAlgebraicOver_ramifiedDifferential [CharZero k] (q : ℕ) (hq : 0 < q)
    {x : LaurentSeries k}
    (hx : @DifferentialAlgebraicOver (RatFunc k) (LaurentSeries k) _ _ _
      (ramifiedDifferential (k := k) q) x) :
    @DifferentialAlgebraicOver (RatFunc k) (LaurentSeries k) _ _ _
      (innerDifferential (k := k)) x := by
  have hqne : (q : k) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  haveI := IsScalarTower.of_algebraMap_eq (R := k) (S := RatFunc k) (A := LaurentSeries k)
    fun c => by
      rw [algebraMap_k_laurentSeries]
      exact (algebraMap_const_laurentSeries c).symm
  refine differentialAlgebraicOver_scaledDeriv (cylinderDifferential (1 : k))
    (cylinderDifferential ((q : k)⁻¹)) (innerDifferential (k := k))
    (ramifiedDifferential (k := k) q) (algebraMap k (RatFunc k) (q : k)) ?_ ?_ ?_ hx
  · intro y
    rw [innerDifferential_deriv, cylinderDifferential_deriv, cylDeriv_one_eq_ratFuncEulerOp,
      algebraMap_ratFuncEulerOp]
  · intro y
    rw [ramifiedDifferential_deriv, cylinderDifferential_deriv, cylDeriv, map_mul,
      algebraMap_ratFuncEulerOp, ← IsScalarTower.algebraMap_apply k (RatFunc k) (LaurentSeries k),
      algebraMap_k_laurentSeries]
  · intro f
    rw [innerDifferential_deriv, ramifiedDifferential_deriv,
      ← IsScalarTower.algebraMap_apply k (RatFunc k) (LaurentSeries k), algebraMap_k_laurentSeries,
      ← mul_assoc,
      show (HahnSeries.C ((q : k)) : LaurentSeries k) * HahnSeries.C ((q : k))⁻¹ = 1 from by
        rw [← map_mul, mul_inv_cancel₀ hqne, map_one], one_mul]

set_option maxHeartbeats 1000000 in
/-- **Hypertranscendence descends through the ramification.**  If the ramified series is
differentially transcendental over `k(w)`, the original series is differentially transcendental
over `k(z)`. -/
theorem hypertranscendentalOver_of_ramify [CharZero k] (q : ℕ) (hq : 0 < q) {R : LaurentSeries k}
    (hHT : @HypertranscendentalOver (RatFunc k) (LaurentSeries k) _ _ _
      (innerDifferential (k := k)) (ramify q hq R)) :
    @HypertranscendentalOver (RatFunc k) (LaurentSeries k) _ _ _
      (innerDifferential (k := k)) R := by
  intro hDA
  exact hHT (differentialAlgebraicOver_ramifiedDifferential q hq
    (differentialAlgebraicOver_ramify q hq hDA))

/-! ## The ramified monomial twist -/

/-- The geometric factorization `X^q - 1 = (X - 1)·(1 + X + … + X^(q-1))`. -/
def geomFactor (q : ℕ) : Polynomial k := ∑ i ∈ Finset.range q, Polynomial.X ^ i

theorem geomFactor_mul (q : ℕ) :
    (Polynomial.X - Polynomial.C 1 : Polynomial k) * geomFactor q = Polynomial.X ^ q - 1 := by
  rw [geomFactor, Polynomial.C_1, mul_comm]
  exact geom_sum_mul Polynomial.X q

theorem eval_geomFactor_one (q : ℕ) : (geomFactor (k := k) q).eval 1 = (q : k) := by
  rw [geomFactor]
  simp

theorem polyPow_linear (q : ℕ) :
    polyPow (k := k) q (Polynomial.C 1 - Polynomial.X) = Polynomial.C 1 - Polynomial.X ^ q := by
  rw [polyPow_apply, Polynomial.sub_comp, Polynomial.C_comp, Polynomial.X_comp]

theorem polyPow_C (q : ℕ) (c : k) : polyPow q (Polynomial.C c) = Polynomial.C c := by
  rw [polyPow_apply, Polynomial.C_comp]

theorem ratFuncPow_oneSubInv (q : ℕ) (hq : 0 < q) (w : k) :
    ratFuncPow q hq (algebraMap k (RatFunc k) w / toRF (Polynomial.C 1 - Polynomial.X))
      = algebraMap k (RatFunc k) w / toRF (Polynomial.C 1 - Polynomial.X ^ q) := by
  rw [algebraMap_eq_toRF_C, ratFuncPow_div, polyPow_C, polyPow_linear]

theorem ramified_increment_eq (q : ℕ) (hq : 0 < q) (p : ℕ) (w : k) :
    -((algebraMap k (RatFunc k) w / toRF (Polynomial.C 1 - Polynomial.X ^ q))
        * (RatFunc.X : RatFunc k) ^ (p : ℤ))
      = toRF (Polynomial.C w * Polynomial.X ^ p)
        / (toRF (Polynomial.X - Polynomial.C 1) * toRF (geomFactor q)) := by
  have hX : (RatFunc.X : RatFunc k) = toRF Polynomial.X := RatFunc.algebraMap_X.symm
  have hden : toRF (Polynomial.C 1 - Polynomial.X ^ q : Polynomial k)
      = -(toRF (Polynomial.X - Polynomial.C 1) * toRF (geomFactor q)) := by
    rw [show toRF (Polynomial.X - Polynomial.C 1 : Polynomial k) * toRF (geomFactor q)
        = toRF ((Polynomial.X - Polynomial.C 1) * geomFactor q) from (map_mul _ _ _).symm,
      geomFactor_mul, ← map_neg]
    congr 1
    rw [Polynomial.C_1]
    ring
  rw [hden, hX, algebraMap_eq_toRF_C,
    show toRF (Polynomial.C w * Polynomial.X ^ p : Polynomial k)
      = toRF (Polynomial.C w) * toRF (Polynomial.X ^ p) from map_mul _ _ _,
    show toRF (Polynomial.X ^ p : Polynomial k) = toRF Polynomial.X ^ (p : ℤ) from by
      rw [zpow_natCast]
      exact map_pow _ _ _]
  field_simp

set_option maxHeartbeats 1000000 in
/-- **Hypertranscendence for a ramified monomial twist.**  If the multiplier of the homogeneous
equation is `β^p` and the dilation is by `β^q`, the substitution `z = w^q` puts the equation in the
one-variable model, where the twisting element `w^(-p)` is rational. -/
theorem hypertranscendentalOver_of_ramifiedMonomialTwist [CharZero k]
    (β : k) (hβ : β ≠ 0) (hβtor : ∀ n : ℤ, n ≠ 0 → β ^ n ≠ 1) (p q : ℕ) (hq : 0 < q)
    (w : k) (hw : w ≠ 0) (R : LaurentSeries k)
    (hR : R - algebraMap k (LaurentSeries k) (β ^ p)
        * innerDilation (β ^ q) (pow_ne_zero q hβ) R
      = algebraMap (RatFunc k) (LaurentSeries k)
        (algebraMap k (RatFunc k) w / toRF (Polynomial.C 1 - Polynomial.X))) :
    @HypertranscendentalOver (RatFunc k) (LaurentSeries k) _ _ _ (innerDifferential (k := k)) R := by
  refine hypertranscendentalOver_of_ramify q hq ?_
  have hram := congrArg (ramify q hq) hR
  rw [map_sub, map_mul, ramify_algebraMap_k q hq, ramify_innerDilation q hq β hβ,
    ramify_algebraMap q hq, ratFuncPow_oneSubInv] at hram
  have hqk : ((q : k)) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [← zpow_natCast β p] at hram
  refine hypertranscendentalOver_of_monomialTwist β hβ hβtor (p : ℤ) 1 one_ne_zero
    (Polynomial.C w * Polynomial.X ^ p) (geomFactor q) ?_ ?_ ?_ _ (ramify q hq R) hram
    (ramified_increment_eq q hq p w)
  · rw [eval_geomFactor_one]
    exact hqk
  · simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      one_pow, mul_one]
    exact hw
  · intro n hn
    refine regularAt_simplePoleQuotient _ _ _ _ ?_ ?_
    · simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, one_mul]
      intro h
      exact hβtor n hn (by linear_combination h)
    · intro hcon
      have hcon' : (geomFactor (k := k) q).eval (β ^ n) = 0 := by simpa using hcon
      have hzero : ((Polynomial.X - Polynomial.C 1 : Polynomial k) * geomFactor q).eval (β ^ n)
          = 0 := by
        rw [Polynomial.eval_mul, hcon', mul_zero]
      rw [geomFactor_mul] at hzero
      simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one] at hzero
      have hpow : ((β ^ n) ^ q : k) = 1 := by linear_combination hzero
      have hqn : β ^ (n * (q : ℤ)) = 1 := by
        rw [zpow_mul, zpow_natCast]
        exact hpow
      exact hβtor (n * (q : ℤ)) (mul_ne_zero hn (by exact_mod_cast hq.ne')) hqn

/-! ## Transport along a dilation of the coordinate -/

theorem innerDilation_aeval {ι : Type*} (c : k) (hc : c ≠ 0) (v : ι → LaurentSeries k)
    (p : MvPolynomial ι (RatFunc k)) :
    innerDilation c hc (MvPolynomial.aeval v p)
      = MvPolynomial.aeval (fun i => innerDilation c hc (v i))
        (MvPolynomial.map ((ratFuncScale c hc : RatFunc k →ₐ[k] RatFunc k) :
          RatFunc k →+* RatFunc k) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [← algebraMap_ratFuncScale]
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]
  | mul_X p i h => simp [h]

theorem differentialJet_innerDilation [CharZero k] (c : k) (hc : c ≠ 0) (n : ℕ)
    (f : LaurentSeries k) :
    @differentialJet (LaurentSeries k) _ (innerDifferential (k := k)) n (innerDilation c hc f)
      = innerDilation c hc
        (@differentialJet (LaurentSeries k) _ (innerDifferential (k := k)) n f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      show @differentialJet (LaurentSeries k) _ (innerDifferential (k := k)) n
          ((innerDifferential (k := k)).deriv (innerDilation c hc f))
        = innerDilation c hc (@differentialJet (LaurentSeries k) _ (innerDifferential (k := k)) n
          ((innerDifferential (k := k)).deriv f))
      rw [innerDifferential_deriv, innerDifferential_deriv, ← innerDilation_innerEuler]
      exact ih _

set_option maxHeartbeats 1000000 in
/-- **A dilation of the coordinate preserves differential algebraicity over `k(z)`.** -/
theorem differentialAlgebraicOver_innerDilation [CharZero k] (c : k) (hc : c ≠ 0)
    {x : LaurentSeries k}
    (hx : @DifferentialAlgebraicOver (RatFunc k) (LaurentSeries k) _ _ _
      (innerDifferential (k := k)) x) :
    @DifferentialAlgebraicOver (RatFunc k) (LaurentSeries k) _ _ _
      (innerDifferential (k := k)) (innerDilation c hc x) := by
  intro hind
  refine hx ?_
  rw [DifferentialIndependent, algebraicIndependent_iff] at hind ⊢
  intro p hp
  have hdil := congrArg (innerDilation c hc) hp
  rw [map_zero, innerDilation_aeval] at hdil
  have hjets : (fun i : Unit × ℕ => innerDilation c hc
      (@differentialJet (LaurentSeries k) _ (innerDifferential (k := k)) i.2 x))
      = fun i : Unit × ℕ => @differentialJet (LaurentSeries k) _
        (innerDifferential (k := k)) i.2 (innerDilation c hc x) := by
    funext i
    exact (differentialJet_innerDilation c hc i.2 x).symm
  rw [hjets] at hdil
  have hmap := hind _ hdil
  have hinj : Function.Injective ((ratFuncScale c hc : RatFunc k →ₐ[k] RatFunc k) :
      RatFunc k →+* RatFunc k) := ratFuncScale_injective c hc
  refine MvPolynomial.map_injective _ hinj ?_
  rw [hmap, map_zero]

end

end GaloisForLFunctions.HTGeometry
