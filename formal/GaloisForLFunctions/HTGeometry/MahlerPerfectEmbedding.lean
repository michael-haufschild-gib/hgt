import GaloisForLFunctions.HTGeometry.MahlerPerfectBase

/-!
# The two-variable base of a Mahler equation over the perfect rational base

The Mahler substitution is an automorphism of the `p`-perfect rational base `F`, so the twisted
dilation of `F(h)` — coefficientwise substitution together with `h ↦ p⁻¹h` — is an automorphism
as well, and it is the restriction of the ambient operator on `k((w^ℚ))((h))`.
-/

namespace GaloisForLFunctions.HTGeometry

open HahnSeries

open scoped RatFunc

noncomputable section

section Twist

variable {K : Type*} [Field K]

theorem polyTwist_comp (φ ψ : K →+* K) (q r : K) (P : Polynomial K) :
    polyTwist φ q (polyTwist ψ r P) = polyTwist (φ.comp ψ) (q * φ r) P := by
  ext n
  rw [coeff_polyTwist, coeff_polyTwist, coeff_polyTwist, map_mul, map_pow, RingHom.comp_apply,
    mul_pow, mul_assoc]

theorem ratFuncTwist_comp (φ ψ : K →+* K) (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) (q r : K) (hq : q ≠ 0) (hr : r ≠ 0) (hqr : q * φ r ≠ 0)
    (f : RatFunc K) :
    ratFuncTwist φ hφ q hq (ratFuncTwist ψ hψ r hr f)
      = ratFuncTwist (φ.comp ψ) (hφ.comp hψ) (q * φ r) hqr f := by
  refine RatFunc.induction_on (P := fun f =>
    ratFuncTwist φ hφ q hq (ratFuncTwist ψ hψ r hr f)
      = ratFuncTwist (φ.comp ψ) (hφ.comp hψ) (q * φ r) hqr f) f ?_
  intro P S _
  rw [ratFuncTwist_div, ratFuncTwist_div, ratFuncTwist_div, polyTwist_comp, polyTwist_comp]

theorem ratFuncTwist_congr {φ : K →+* K} (hφ : Function.Injective φ) (φ' : K →+* K)
    (hφ' : Function.Injective φ') {q : K} (hq : q ≠ 0) (q' : K) (hq' : q' ≠ 0)
    (hh : φ = φ') (hqq : q = q') (f : RatFunc K) :
    ratFuncTwist φ hφ q hq f = ratFuncTwist φ' hφ' q' hq' f := by
  subst hh; subst hqq; rfl

theorem polyTwist_id_one (P : Polynomial K) : polyTwist (RingHom.id K) 1 P = P := by
  ext n
  rw [coeff_polyTwist, one_pow, one_mul, RingHom.id_apply]

theorem ratFuncTwist_id_one (f : RatFunc K) :
    ratFuncTwist (RingHom.id K) Function.injective_id 1 one_ne_zero f = f := by
  refine RatFunc.induction_on (P := fun f =>
    ratFuncTwist (RingHom.id K) Function.injective_id 1 one_ne_zero f = f) f ?_
  intro P S _
  rw [ratFuncTwist_div, polyTwist_id_one, polyTwist_id_one]

/-- **The twisted dilation of `K(h)` by a coefficient automorphism and a nonzero scale.** -/
def ratFuncTwistEquiv (φ : K ≃+* K) (q : K) (hq : q ≠ 0) : RatFunc K ≃+* RatFunc K where
  toFun := ratFuncTwist φ.toRingHom φ.injective q hq
  invFun := ratFuncTwist φ.symm.toRingHom φ.symm.injective (φ.symm q)⁻¹
    (inv_ne_zero (by simpa using hq))
  left_inv f := by
    have hq' : (φ.symm q)⁻¹ ≠ 0 := inv_ne_zero (by simpa using hq)
    have hone : (φ.symm q)⁻¹ * φ.symm.toRingHom q = 1 := by
      show (φ.symm q)⁻¹ * φ.symm q = 1
      exact inv_mul_cancel₀ (by simpa using hq)
    rw [ratFuncTwist_comp _ _ _ _ _ _ hq' hq (by rw [hone]; exact one_ne_zero)]
    refine (ratFuncTwist_congr _ (RingHom.id K) (fun a b h => h) _ 1 one_ne_zero
      (by ext x; simp) hone f).trans (ratFuncTwist_id_one f)
  right_inv f := by
    have hq' : (φ.symm q)⁻¹ ≠ 0 := inv_ne_zero (by simpa using hq)
    have hone : q * φ.toRingHom (φ.symm q)⁻¹ = 1 := by
      show q * φ (φ.symm q)⁻¹ = 1
      rw [map_inv₀, RingEquiv.apply_symm_apply]
      exact mul_inv_cancel₀ hq
    rw [ratFuncTwist_comp _ _ _ _ _ _ hq hq' (by rw [hone]; exact one_ne_zero)]
    refine (ratFuncTwist_congr _ (RingHom.id K) (fun a b h => h) _ 1 one_ne_zero
      (by ext x; simp) hone f).trans (ratFuncTwist_id_one f)
  map_mul' := map_mul _
  map_add' := map_add _

@[simp]
theorem ratFuncTwistEquiv_apply (φ : K ≃+* K) (q : K) (hq : q ≠ 0) (f : RatFunc K) :
    ratFuncTwistEquiv φ q hq f = ratFuncTwist φ.toRingHom φ.injective q hq f := rfl

end Twist

variable {k : Type*} [Field k]

theorem C_mem_perfectBase (p : ℕ) (hp : 1 < p) (c : k) :
    (HahnSeries.C c : HahnSeries ℚ k) ∈ perfectBase p hp := by
  rw [← ratFuncToHahn_const c]
  exact ratFuncToHahn_mem_perfectBase p hp _

/-- Constants of `k` inside the perfect base. -/
def perfectConst (p : ℕ) (hp : 1 < p) (c : k) : perfectBase (k := k) p hp :=
  ⟨HahnSeries.C c, C_mem_perfectBase p hp c⟩

@[simp]
theorem perfectConst_coe (p : ℕ) (hp : 1 < p) (c : k) :
    ((perfectConst p hp c : perfectBase (k := k) p hp) : HahnSeries ℚ k) = HahnSeries.C c := rfl

theorem perfectConst_ne_zero (p : ℕ) (hp : 1 < p) {c : k} (hc : c ≠ 0) :
    perfectConst p hp c ≠ 0 := by
  intro h
  have h' : (HahnSeries.C c : HahnSeries ℚ k) = 0 := congrArg Subtype.val h
  exact hc (by simpa using congrArg (fun x => HahnSeries.coeff x 0) h')

/-- The two-variable base of a Mahler equation, over the perfect rational base. -/
abbrev MahlerPBase (k : Type*) [Field k] (p : ℕ) (hp : 1 < p) :=
  RatFunc (perfectBase (k := k) p hp)

theorem inv_natCast_ne_zero' {p : ℕ} (hp : 1 < p) [CharZero k] : ((p : k))⁻¹ ≠ 0 := by
  have hpk : ((p : k)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact Nat.cast_ne_zero.mpr this.ne'
  exact inv_ne_zero hpk

/-- **The Mahler substitution on the two-variable perfect base**: `w ↦ w^p`, `h ↦ p⁻¹h`. -/
def mahlerPBaseDilation [CharZero k] (p : ℕ) (hp : 1 < p) :
    MahlerPBase k p hp ≃+* MahlerPBase k p hp :=
  ratFuncTwistEquiv (perfectBaseEquiv p hp) (perfectConst p hp ((p : k))⁻¹)
    (perfectConst_ne_zero p hp (inv_natCast_ne_zero' hp))

/-- The Hahn expansion of the two-variable perfect base. -/
def mahlerPEmbed (k : Type*) [Field k] (p : ℕ) (hp : 1 < p) :
    MahlerPBase k p hp →+* MahlerAmbient k :=
  (hahnMapRingHom ((perfectBase (k := k) p hp).subtype)).comp
    (algebraMap (RatFunc (perfectBase (k := k) p hp)) (LaurentSeries (perfectBase (k := k) p hp)))

/-- **The perfect base substitution is the restriction of the ambient one.** -/
theorem mahlerPEmbed_mahlerPBaseDilation [CharZero k] (p : ℕ) (hp : 1 < p)
    (x : MahlerPBase k p hp) :
    mahlerPEmbed k p hp (mahlerPBaseDilation p hp x)
      = mahlerDilation p hp (mahlerPEmbed k p hp x) := by
  have hχ : ∀ n : ℤ,
      ((perfectBase (k := k) p hp).subtype
          ((laurentChar (perfectConst p hp ((p : k))⁻¹)
            (perfectConst_ne_zero p hp (inv_natCast_ne_zero' hp))) (Multiplicative.ofAdd n)))
        = ((laurentChar (HahnSeries.C (((p : k))⁻¹) : HahnSeries ℚ k)
            (C_inv_natCast_ne_zero hp)) (Multiplicative.ofAdd n) : HahnSeries ℚ k) := by
    intro n
    rw [laurentChar_apply, laurentChar_apply, map_zpow₀]
    rfl
  have hφ : ∀ x : perfectBase (k := k) p hp,
      (perfectBase (k := k) p hp).subtype
          ((perfectBaseEquiv p hp).toRingHom x)
        = mahlerHom p (by omega) ((perfectBase (k := k) p hp).subtype x) :=
    fun x => perfectBaseEquiv_coe p hp x
  simp only [mahlerPEmbed, RingHom.coe_comp, Function.comp_apply, mahlerPBaseDilation,
    ratFuncTwistEquiv_apply, mahlerDilation, hahnTwistHom_apply]
  rw [algebraMap_ratFuncTwist, hahnTwistHom_apply,
    hahnMapRingHom_hahnTwist ((perfectBase (k := k) p hp).subtype)
      (perfectBaseEquiv p hp).toRingHom
      (mahlerHom p (by omega)) _ _ hφ hχ]

end

end GaloisForLFunctions.HTGeometry
