import GaloisForLFunctions.CurvesOverFiniteFields.Duality

/-!
# Principal divisors

For a nonzero function `x`, `pdiv x` records `log v(x)`, the pole order, at every place.

* `pdiv` turns products into sums and inverses into negatives (`pdiv_mul`, `pdiv_inv`).
* Multiplication by `x` maps `I(D)`, `J(D)` onto `I(D + pdiv x)`, `J(D + pdiv x)`, so
  `ℓ(D + pdiv x) = ℓ(D)` and `h¹(D + pdiv x) = h¹(D)` (`ell_add_pdiv`, `hOne_add_pdiv`).
* Hence, by Riemann's theorem, `deg (pdiv x) = 0` (`deg_pdiv`): a function has as many zeros as
  poles, counted with degrees.
* `x ∈ L(D)` iff `pdiv x ≤ D` (`mem_ell_iff`), and `pdiv x = 0` only for constants
  (`exists_eq_algebraMap_of_pdiv_eq_zero`).
-/

noncomputable section

open Polynomial IsDedekindDomain WithZero

namespace GaloisForLFunctions.CurvesOverFiniteFields

section General

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem valDiv_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    valDiv (R := R) (mul_ne_zero hx hy) = valDiv (R := R) hx + valDiv (R := R) hy := by
  ext v
  rw [Finsupp.add_apply, valDiv_apply, valDiv_apply, valDiv_apply, map_mul,
    log_mul ((Valuation.ne_zero_iff _).mpr hx) ((Valuation.ne_zero_iff _).mpr hy)]

theorem valDiv_inv {x : K} (hx : x ≠ 0) :
    valDiv (R := R) (inv_ne_zero hx) = -valDiv (R := R) hx := by
  ext v
  rw [Finsupp.neg_apply, valDiv_apply, valDiv_apply, map_inv₀, log_inv]

end General

section Mul

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- Multiplication by a nonzero element, as an `F`-linear automorphism of `K`. -/
def mulLeftEquiv {x : K} (hx : x ≠ 0) : K ≃ₗ[F] K :=
  LinearEquiv.ofLinear (LinearMap.mulLeft F x) (LinearMap.mulLeft F x⁻¹)
    (by ext f; simp [hx]) (by ext f; simp [hx])

theorem mulLeftEquiv_apply {x : K} (hx : x ≠ 0) (f : K) :
    mulLeftEquiv (F := F) hx f = x * f := rfl

end Mul

variable {F : Type*} [Field F] [DecidableEq (RatFunc F)] {K : Type*} [Field K] [Algebra F[X] K]
  [Algebra (RatFunc F) K] [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K]
  [Algebra.IsSeparable (RatFunc F) K] [Algebra F K] [IsScalarTower F F[X] K]
  [IsScalarTower F (RatFunc F) K]

omit [Algebra F K] [IsScalarTower F F[X] K] [IsScalarTower F (RatFunc F) K] in
theorem pdiv_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    pdiv (mul_ne_zero hx hy) = (pdiv hx + pdiv hy : Divisor F K) :=
  Prod.ext (valDiv_mul (R := finChart F K) hx hy) (valDiv_mul (R := infChart F K) hx hy)

omit [Algebra F K] [IsScalarTower F F[X] K] [IsScalarTower F (RatFunc F) K] in
theorem pdiv_inv {x : K} (hx : x ≠ 0) : pdiv (inv_ne_zero hx) = (-pdiv hx : Divisor F K) :=
  Prod.ext (valDiv_inv (R := finChart F K) hx) (valDiv_inv (R := infChart F K) hx)

omit [IsScalarTower F (RatFunc F) K] in
/-- Multiplication by `x` carries `I(D)` onto `I(D + pdiv x)`. -/
theorem map_finSpace_pdiv {x : K} (hx : x ≠ 0) (D : Divisor F K) :
    (finSpace D).map (mulLeftEquiv (F := F) hx : K →ₗ[F] K) = finSpace (D + pdiv hx) := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show x * y ∈ finSpace (D + pdiv hx)
    refine (mem_valSpace_add_valDiv_iff (R := finChart F K) (K := K) (E := D.1)
      (f := x * y) hx).mpr ?_
    rwa [← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  · intro hf
    refine ⟨x⁻¹ * f, (mem_valSpace_add_valDiv_iff (R := finChart F K) (K := K) (E := D.1)
      (f := f) hx).mp hf, ?_⟩
    rw [LinearEquiv.coe_coe, mulLeftEquiv_apply, ← mul_assoc, mul_inv_cancel₀ hx, one_mul]

omit [IsScalarTower F F[X] K] in
/-- Multiplication by `x` carries `J(D)` onto `J(D + pdiv x)`. -/
theorem map_infSpace_pdiv {x : K} (hx : x ≠ 0) (D : Divisor F K) :
    (infSpace D).map (mulLeftEquiv (F := F) hx : K →ₗ[F] K) = infSpace (D + pdiv hx) := by
  ext f
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    show x * y ∈ infSpace (D + pdiv hx)
    refine (mem_valSpace_add_valDiv_iff (R := infChart F K) (K := K) (E := D.2)
      (f := x * y) hx).mpr ?_
    rwa [← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  · intro hf
    refine ⟨x⁻¹ * f, (mem_valSpace_add_valDiv_iff (R := infChart F K) (K := K) (E := D.2)
      (f := f) hx).mp hf, ?_⟩
    rw [LinearEquiv.coe_coe, mulLeftEquiv_apply, ← mul_assoc, mul_inv_cancel₀ hx, one_mul]

/-- Linearly equivalent divisors have the same `ℓ`. -/
theorem ell_add_pdiv {x : K} (hx : x ≠ 0) (D : Divisor F K) : ell (D + pdiv hx) = ell D := by
  unfold ell
  rw [← map_finSpace_pdiv hx D, ← map_infSpace_pdiv hx D,
    ← Submodule.map_inf (mulLeftEquiv (F := F) hx : K →ₗ[F] K) (mulLeftEquiv (F := F) hx).injective]
  exact ((mulLeftEquiv (F := F) hx).submoduleMap _).finrank_eq.symm

/-- Linearly equivalent divisors have the same `h¹`. -/
theorem hOne_add_pdiv {x : K} (hx : x ≠ 0) (D : Divisor F K) : hOne (D + pdiv hx) = hOne D := by
  unfold hOne
  rw [← map_finSpace_pdiv hx D, ← map_infSpace_pdiv hx D, ← Submodule.map_sup]
  exact (Submodule.Quotient.equiv _ _ (mulLeftEquiv (F := F) hx) rfl).finrank_eq.symm

/-- `x ∈ L(D)` iff `pdiv x ≤ D`. -/
theorem mem_ell_iff {x : K} (hx : x ≠ 0) {D : Divisor F K} :
    x ∈ finSpace D ⊓ infSpace D ↔ pdiv hx ≤ D := by
  rw [Submodule.mem_inf, Prod.le_def, Finsupp.le_def, Finsupp.le_def]
  change (∀ v : FinPlace F K, v.valuation K x ≤ exp (D.1 v)) ∧
      (∀ v : InfPlace F K, v.valuation K x ≤ exp (D.2 v)) ↔
    (∀ v : FinPlace F K, log (v.valuation K x) ≤ D.1 v) ∧
      (∀ v : InfPlace F K, log (v.valuation K x) ≤ D.2 v)
  refine and_congr (forall_congr' fun v => ?_) (forall_congr' fun v => ?_)
  · have hv0 : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    conv_lhs => rw [← exp_log hv0]
    exact exp_le_exp
  · have hv0 : v.valuation K x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    conv_lhs => rw [← exp_log hv0]
    exact exp_le_exp

variable (hconst : ∀ x : K, IsIntegral F x → ∃ a : F, algebraMap F K a = x)
include hconst

/-- **Degree of a principal divisor**: `deg (pdiv x) = 0`. Both `0` and `pdiv x` have the same
`ℓ` and `h¹`, and Riemann's theorem reads off their degrees. -/
theorem deg_pdiv {x : K} (hx : x ≠ 0) : (pdiv hx : Divisor F K).deg = 0 := by
  have h1 := (riemann_roch_chi hconst (0 + pdiv hx)).2
  have h0 := (riemann_roch_chi hconst 0).2
  rw [ell_add_pdiv, hOne_add_pdiv, zero_add] at h1
  rw [deg_zero] at h0
  linarith

/-- A function without zeros and poles is constant. -/
theorem exists_eq_algebraMap_of_pdiv_eq_zero {x : K} (hx : x ≠ 0)
    (h : pdiv hx = (0 : Divisor F K)) : ∃ a : F, algebraMap F K a = x := by
  have hmem : x ∈ finSpace (0 : Divisor F K) ⊓ infSpace 0 := (mem_ell_iff hx).mpr h.le
  rw [finSpace_zero_inf_infSpace_zero hconst, LinearMap.mem_range] at hmem
  exact hmem

end GaloisForLFunctions.CurvesOverFiniteFields
