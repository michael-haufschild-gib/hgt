import GaloisForLFunctions.CurvesOverFiniteFields.FiniteCounts
import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Principal divisors as a subgroup; the effective divisors of a class

* Nonzero constants have valuation one at every place, so `pdiv` is invariant under nonzero
  constant multiples (`pdiv_algebraMap_mul`).
* The principal divisors form a subgroup (`principal`).
* The effective divisors linearly equivalent to `D` (`effClass D`) correspond to the points of the
  projective space of `L(D)` under `[x] ↦ D − pdiv x` (`effClassMap_bijective`). Over a field with
  `q` elements there are `1 + q + ⋯ + q^{ℓ(D) − 1}` of them (`card_effClass`).
-/

noncomputable section

open Polynomial IsDedekindDomain WithZero

namespace GaloisForLFunctions.CurvesOverFiniteFields

section General

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {F : Type*} [Field F] [Algebra F R] [Algebra F K] [IsScalarTower F R K]

/-- A nonzero constant has valuation one at every place. -/
theorem valuation_algebraMap_const (v : HeightOneSpectrum R) {c : F} (hc : c ≠ 0) :
    v.valuation K (algebraMap F K c) = 1 := by
  have h1 : v.valuation K (algebraMap F K c) ≤ 1 := by
    rw [IsScalarTower.algebraMap_apply F R K]
    exact v.valuation_le_one _
  have h2 : v.valuation K (algebraMap F K c⁻¹) ≤ 1 := by
    rw [IsScalarTower.algebraMap_apply F R K]
    exact v.valuation_le_one _
  have h3 : v.valuation K (algebraMap F K c) * v.valuation K (algebraMap F K c⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hc, map_one, map_one]
  refine le_antisymm h1 ?_
  by_contra hlt
  push Not at hlt
  exact absurd h3 (ne_of_lt (mul_lt_one_of_lt_of_le hlt h2))

theorem valDiv_algebraMap_mul {c : F} (hc : c ≠ 0) {y : K} (hy : y ≠ 0)
    (h : algebraMap F K c * y ≠ 0) : valDiv (R := R) h = valDiv (R := R) hy := by
  ext v
  rw [valDiv_apply, valDiv_apply, map_mul, valuation_algebraMap_const v hc, one_mul]

theorem coe_ne_zero_of_ne_zero {S : Submodule F K} {v : S} (hv : v ≠ 0) : (v : K) ≠ 0 :=
  fun h => hv (Subtype.ext h)

end General

variable {F : Type*} [Field F] [DecidableEq (RatFunc F)] {K : Type*} [Field K] [Algebra F[X] K]
  [Algebra (RatFunc F) K] [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K]
  [Algebra.IsSeparable (RatFunc F) K] [Algebra F K] [IsScalarTower F F[X] K]
  [IsScalarTower F (RatFunc F) K]

omit [Algebra F K] [IsScalarTower F F[X] K] [IsScalarTower F (RatFunc F) K] in
theorem pdiv_congr {x y : K} (h : x = y) (hx : x ≠ 0) (hy : y ≠ 0) :
    (pdiv hx : Divisor F K) = pdiv hy := by
  subst h
  rfl

theorem pdiv_algebraMap_mul {c : F} (hc : c ≠ 0) {y : K} (hy : y ≠ 0)
    (h : algebraMap F K c * y ≠ 0) : (pdiv h : Divisor F K) = pdiv hy :=
  Prod.ext (valDiv_algebraMap_mul (R := finChart F K) hc hy h)
    (valDiv_algebraMap_mul (R := infChart F K) hc hy h)

omit [Algebra F K] [IsScalarTower F F[X] K] [IsScalarTower F (RatFunc F) K] in
theorem pdiv_one : pdiv (one_ne_zero : (1 : K) ≠ 0) = (0 : Divisor F K) := by
  refine Prod.ext ?_ ?_ <;> ext v <;> simp [pdiv, valDiv_apply]

/-- The subgroup of principal divisors. -/
def principal : AddSubgroup (Divisor F K) where
  carrier := {D | ∃ (x : K) (hx : x ≠ 0), pdiv hx = D}
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, mul_ne_zero hx hy, pdiv_mul hx hy⟩
  zero_mem' := ⟨1, one_ne_zero, pdiv_one⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, inv_ne_zero hx, pdiv_inv hx⟩

omit [Algebra F K] [IsScalarTower F F[X] K] [IsScalarTower F (RatFunc F) K] in
theorem pdiv_mem_principal {x : K} (hx : x ≠ 0) : (pdiv hx : Divisor F K) ∈ principal :=
  ⟨x, hx, rfl⟩

omit [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K] [Algebra.IsSeparable (RatFunc F) K]
  [Algebra F K] [IsScalarTower F F[X] K] [IsScalarTower F (RatFunc F) K] in
/-- `E ≤ D ⇒ 0 ≤ D − E`, coordinatewise. -/
theorem divisor_sub_nonneg {D E : Divisor F K} (h : E ≤ D) : 0 ≤ D - E :=
  Prod.le_def.mpr
    ⟨show (0 : FinPlace F K →₀ ℤ) ≤ D.1 - E.1 from sub_nonneg.mpr (Prod.le_def.mp h).1,
      show (0 : InfPlace F K →₀ ℤ) ≤ D.2 - E.2 from sub_nonneg.mpr (Prod.le_def.mp h).2⟩

omit [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K] [Algebra.IsSeparable (RatFunc F) K]
  [Algebra F K] [IsScalarTower F F[X] K] [IsScalarTower F (RatFunc F) K] in
/-- `0 ≤ E ⇒ D − E ≤ D`, coordinatewise. -/
theorem divisor_sub_le_self (D : Divisor F K) {E : Divisor F K} (h : 0 ≤ E) : D - E ≤ D :=
  Prod.le_def.mpr
    ⟨show D.1 - E.1 ≤ D.1 from sub_le_self _ (Prod.le_def.mp h).1,
      show D.2 - E.2 ≤ D.2 from sub_le_self _ (Prod.le_def.mp h).2⟩

/-- The effective divisors linearly equivalent to `D`. -/
def effClass (D : Divisor F K) : Set (Divisor F K) := {E | 0 ≤ E ∧ E - D ∈ principal}

/-- `x ∈ L(D) \ 0 ↦ D − pdiv x`, an effective divisor linearly equivalent to `D`. -/
def toEffClass (D : Divisor F K)
    (v : {v : (finSpace D ⊓ infSpace D : Submodule F K) // v ≠ 0}) : effClass D :=
  ⟨D - pdiv (coe_ne_zero_of_ne_zero v.2), divisor_sub_nonneg ((mem_ell_iff _).mp v.1.2), by
    rw [sub_sub_cancel_left, ← pdiv_inv]
    exact pdiv_mem_principal _⟩

theorem toEffClass_coe (D : Divisor F K)
    (v : {v : (finSpace D ⊓ infSpace D : Submodule F K) // v ≠ 0}) :
    (toEffClass D v : Divisor F K) = D - pdiv (coe_ne_zero_of_ne_zero v.2) := rfl

/-- The map from the projective space of `L(D)` to the effective divisors in the class of `D`. -/
def effClassMap (D : Divisor F K) :
    Projectivization F (finSpace D ⊓ infSpace D : Submodule F K) → effClass D :=
  Projectivization.lift (toEffClass D) (by
    intro a b t h
    have ht : t ≠ 0 := by
      rintro rfl
      rw [zero_smul] at h
      exact a.2 h
    have hab : ((a.1 : _) : K) = algebraMap F K t * (b.1 : K) := by
      rw [h, Submodule.coe_smul, Algebra.smul_def]
    apply Subtype.ext
    rw [toEffClass_coe, toEffClass_coe,
      pdiv_congr hab (coe_ne_zero_of_ne_zero a.2)
        (by rw [← hab]; exact coe_ne_zero_of_ne_zero a.2),
      pdiv_algebraMap_mul ht (coe_ne_zero_of_ne_zero b.2)])

theorem effClassMap_mk (D : Divisor F K) (v : (finSpace D ⊓ infSpace D : Submodule F K))
    (hv : v ≠ 0) :
    (effClassMap D (Projectivization.mk F v hv) : Divisor F K) =
      D - pdiv (coe_ne_zero_of_ne_zero hv) := rfl

variable (hconst : ∀ x : K, IsIntegral F x → ∃ a : F, algebraMap F K a = x)
include hconst

/-- **Effective divisors of a class = points of the projective space of `L(D)`.** -/
theorem effClassMap_bijective (D : Divisor F K) : Function.Bijective (effClassMap D) := by
  constructor
  · intro p₁ p₂ h
    induction p₁ using Projectivization.ind with
    | h a ha =>
    induction p₂ using Projectivization.ind with
    | h b hb =>
    have h' := congrArg Subtype.val h
    rw [effClassMap_mk, effClassMap_mk, sub_right_inj] at h'
    have ha' := coe_ne_zero_of_ne_zero ha
    have hb' := coe_ne_zero_of_ne_zero hb
    have hq : (pdiv (mul_ne_zero ha' (inv_ne_zero hb')) : Divisor F K) = 0 := by
      rw [pdiv_mul ha' (inv_ne_zero hb'), pdiv_inv hb', h', add_neg_cancel]
    obtain ⟨c, hc⟩ := exists_eq_algebraMap_of_pdiv_eq_zero hconst _ hq
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨c, Subtype.ext ?_⟩
    rw [Submodule.coe_smul, Algebra.smul_def, hc, mul_assoc, inv_mul_cancel₀ hb', mul_one]
  · rintro ⟨E, hE0, hED⟩
    obtain ⟨y, hy, hyE⟩ := hED
    have hx : y⁻¹ ≠ 0 := inv_ne_zero hy
    have hpx : (pdiv hx : Divisor F K) = D - E := by
      rw [pdiv_inv hy, hyE, neg_sub]
    have hmem : y⁻¹ ∈ finSpace D ⊓ infSpace D := by
      rw [mem_ell_iff hx, hpx]
      exact divisor_sub_le_self D hE0
    have hv : (⟨y⁻¹, hmem⟩ : (finSpace D ⊓ infSpace D : Submodule F K)) ≠ 0 := by
      intro h0
      exact hx (congrArg Subtype.val h0)
    refine ⟨Projectivization.mk F _ hv, Subtype.ext ?_⟩
    rw [effClassMap_mk]
    change D - pdiv hx = E
    rw [hpx, sub_sub_cancel]

variable [Fintype F]

/-- **Number of effective divisors in a class**: `1 + q + ⋯ + q^{ℓ(D) − 1}`. -/
theorem card_effClass (D : Divisor F K) :
    Nat.card (effClass D) = ∑ i ∈ Finset.range (ell D), Fintype.card F ^ i := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (effClassMap_bijective hconst D)),
    Projectivization.card_of_finrank F (finSpace D ⊓ infSpace D : Submodule F K) (n := ell D) rfl,
    Nat.card_eq_fintype_card]

end GaloisForLFunctions.CurvesOverFiniteFields
