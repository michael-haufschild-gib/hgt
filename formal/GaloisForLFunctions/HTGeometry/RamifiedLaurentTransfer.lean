import GaloisForLFunctions.HTGeometry.QDifferenceLaurentOneVariable

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
  have hinj : Function.Injective (ratFuncPow q hq) := RingHom.injective (ratFuncPow q hq)
  exact MvPolynomial.map_injective _ hinj hmap

end

end GaloisForLFunctions.HTGeometry
