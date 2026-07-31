import GaloisForLFunctions.RHTower.KRealKernelCokernel

/-!
# Realization of the two `K_R` parities

The closed-cokernel layer of Deninger's `K_R` coefficient category assumes a continuous
conjugate-linear structure map.  This module exhibits one in each parity, so the layer is not an
empty quantification, and shows that the odd parity genuinely needs more than one complex
dimension.

Complex conjugation on `ℂ` is the even structure.  The quaternionic map
`(x, y) ↦ (-conj y, conj x)` on `ℂ × ℂ` is the odd one, and it is minimal: a one-dimensional
complex space carries no odd structure at all, because every conjugate-linear endomorphism of `ℂ`
squares to multiplication by a nonnegative real number.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-! ## The even parity -/

/-- Complex conjugation, as a conjugate-linear endomorphism of `ℂ`. -/
def conjSemilinear : ℂ →ₗ⋆[ℂ] ℂ where
  toFun z := starRingEnd ℂ z
  map_add' x y := by simp
  map_smul' c z := by
    simp only [smul_eq_mul, map_mul]

@[simp] theorem conjSemilinear_apply (z : ℂ) :
    conjSemilinear z = starRingEnd ℂ z := rfl

/-- Complex conjugation is an even `K_R` structure on `ℂ`. -/
def kRealConjugation : KRealStructure false ℂ where
  sigma := conjSemilinear
  sq v := by simp [kRealParityAction]

/-- The even structure map is continuous. -/
theorem continuous_kRealConjugation_sigma :
    Continuous (kRealConjugation.sigma : ℂ → ℂ) :=
  Complex.continuous_conj

/-! ## The odd parity -/

/-- The quaternionic map `(x, y) ↦ (-conj y, conj x)`, as a conjugate-linear endomorphism of
`ℂ × ℂ`. -/
def quaternionicSemilinear : (ℂ × ℂ) →ₗ⋆[ℂ] (ℂ × ℂ) where
  toFun p := (-(starRingEnd ℂ p.2), starRingEnd ℂ p.1)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk, neg_add]
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul, Prod.smul_mk,
      Prod.mk.injEq]
    constructor
    · ring
    · trivial

@[simp] theorem quaternionicSemilinear_apply (p : ℂ × ℂ) :
    quaternionicSemilinear p = (-(starRingEnd ℂ p.2), starRingEnd ℂ p.1) := rfl

/-- The quaternionic map is an odd `K_R` structure on `ℂ × ℂ`. -/
def kRealQuaternionic : KRealStructure true (ℂ × ℂ) where
  sigma := quaternionicSemilinear
  sq v := by
    simp [kRealParityAction, Prod.ext_iff]

/-- The odd structure map is continuous. -/
theorem continuous_kRealQuaternionic_sigma :
    Continuous (kRealQuaternionic.sigma : ℂ × ℂ → ℂ × ℂ) := by
  have h : (kRealQuaternionic.sigma : ℂ × ℂ → ℂ × ℂ) =
      fun p => (-(starRingEnd ℂ p.2), starRingEnd ℂ p.1) := rfl
  rw [h]
  exact ((Complex.continuous_conj.comp continuous_snd).neg).prodMk
    (Complex.continuous_conj.comp continuous_fst)

/-! ## What the two parities force -/

/-- An odd structure has no nonzero fixed vector. -/
theorem KRealStructure.eq_zero_of_sigma_eq_self {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K : KRealStructure true V) {v : V} (hv : K.sigma v = v) : v = 0 := by
  have h := K.sq v
  rw [hv, hv] at h
  have hneg : v = -v := by simpa [kRealParityAction] using h
  have hsum : v + v = 0 := by
    nth_rewrite 1 [hneg]
    simp
  have h2 : (2 : ℂ) • v = 0 := by
    simpa [two_smul] using hsum
  have hv2 : v = (2 : ℂ)⁻¹ • ((2 : ℂ) • v) := by
    rw [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0), one_smul]
  rw [h2, smul_zero] at hv2
  exact hv2

/-- An even structure map is an involution. -/
theorem KRealStructure.sigma_sigma {V : Type*} [AddCommGroup V] [Module ℂ V]
    (K : KRealStructure false V) (v : V) : K.sigma (K.sigma v) = v := by
  simpa [kRealParityAction] using K.sq v

/-- **The odd parity needs two complex dimensions.**  No conjugate-linear endomorphism of `ℂ`
squares to `-1`, so `ℂ` carries no odd `K_R` structure and the quaternionic realization above is
minimal. -/
theorem not_nonempty_kRealStructure_true_complex :
    IsEmpty (KRealStructure true ℂ) := by
  constructor
  intro K
  set c : ℂ := K.sigma 1 with hc
  have hlin : ∀ z : ℂ, K.sigma z = starRingEnd ℂ z * c := by
    intro z
    have h : K.sigma (z • (1 : ℂ)) = starRingEnd ℂ z • K.sigma 1 :=
      map_smulₛₗ K.sigma z 1
    simpa only [smul_eq_mul, mul_one, ← hc] using h
  have h1 : K.sigma c = -1 := by
    simpa [kRealParityAction] using K.sq 1
  rw [hlin c] at h1
  have hns : (Complex.normSq c : ℂ) = -1 := by
    rw [← Complex.mul_conj, mul_comm]
    exact h1
  have hreal : Complex.normSq c = -1 := by exact_mod_cast hns
  have hnn := Complex.normSq_nonneg c
  rw [hreal] at hnn
  linarith

end

end GaloisForLFunctions.RHTower
