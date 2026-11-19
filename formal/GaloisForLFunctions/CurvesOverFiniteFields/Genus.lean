import GaloisForLFunctions.CurvesOverFiniteFields.Divisors
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.RingTheory.Algebraic.Integral

/-!
# The base case: constants and the genus

Assume `F` is algebraically closed in `K` (`hconst`), i.e. `F` is the exact constant field.

* `L(0)` is the field of constants (`finSpace_zero_inf_infSpace_zero`): an element integral over
  both `F[x]` and the valuation ring at infinity has minimal polynomial over `F(x)` with
  coefficients in `F[x] ∩ O∞ = F`, so it is integral over `F`. Hence `ℓ(0) = 1`.
* `H¹(0) = K/(A + O∞)` is finite-dimensional (`finiteDimensional_hOne_zero`). Take a basis of
  `K/F(x)` inside `A` and `N` with `x^{-N} e ∈ O∞` for every basis vector. A coefficient
  `r ∈ F(x)` splits as a polynomial plus `Σ_{j<N} c_j x^{-j} + x^{-N} t` with `t ∈ O∞`
  (`exists_poly_sub_le_one`, `exists_expansion`); the middle terms span a finite space.
* With `g = dim H¹(0)` (`genus`), **Riemann's theorem**: `ℓ(D) − h¹(D) = deg D + 1 − g` for every
  divisor (`riemann_roch_chi`), hence `ℓ(D) ≥ deg D + 1 − g` (`riemann_inequality`).
-/

noncomputable section

open Polynomial IsDedekindDomain WithZero

namespace GaloisForLFunctions.CurvesOverFiniteFields

section Laurent

variable (F : Type*) [Field F] [DecidableEq (RatFunc F)]

/-- The uniformizer `1/x` at infinity. -/
abbrev xInv : RatFunc F := RatFunc.X⁻¹

theorem inftyValuation_xInv : RatFunc.inftyValuation F (xInv F) = exp (-1) := by
  rw [map_inv₀, RatFunc.inftyValuation.X, exp_neg]

/-- Every rational function differs from a polynomial by an element of the ring at infinity. -/
theorem exists_poly_sub_le_one (r : RatFunc F) :
    ∃ p : F[X], RatFunc.inftyValuation F (r - algebraMap F[X] (RatFunc F) p) ≤ 1 := by
  have hd0 : r.denom ≠ 0 := r.denom_ne_zero
  have hdm : r.denom.Monic := r.monic_denom
  have hd' : algebraMap F[X] (RatFunc F) r.denom ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr hd0
  have key := RatFunc.num_div_denom r
  rw [div_eq_iff hd'] at key
  refine ⟨r.num /ₘ r.denom, ?_⟩
  have hsub : r - algebraMap F[X] (RatFunc F) (r.num /ₘ r.denom) =
      algebraMap F[X] (RatFunc F) (r.num %ₘ r.denom) / algebraMap F[X] (RatFunc F) r.denom := by
    rw [eq_div_iff hd', sub_mul, ← key, ← map_mul, ← map_sub]
    congr 1
    linear_combination -(modByMonic_add_div r.num r.denom)
  rw [hsub]
  by_cases hrem : r.num %ₘ r.denom = 0
  · rw [hrem, map_zero, zero_div, map_zero]; exact zero_le_one
  have hd1 : r.denom ≠ 1 := fun h => hrem (by rw [h, modByMonic_one])
  have hlt := natDegree_modByMonic_lt r.num hdm hd1
  have hne : algebraMap F[X] (RatFunc F) (r.num %ₘ r.denom) /
      algebraMap F[X] (RatFunc F) r.denom ≠ 0 :=
    div_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).mpr hrem) hd'
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_of_nonzero F hne, ← exp_zero,
    exp_le_exp, intDegree_div_polynomial F hrem hd0]
  omega

/-- **Laurent expansion at infinity**: an element of the ring at infinity is a polynomial in
`1/x` of degree `< n` plus `x^{-n}` times an element of the ring at infinity. -/
theorem exists_expansion (n : ℕ) {s : RatFunc F} (hs : RatFunc.inftyValuation F s ≤ 1) :
    ∃ (c : ℕ → F) (t : RatFunc F), RatFunc.inftyValuation F t ≤ 1 ∧
      s = (∑ j ∈ Finset.range n, algebraMap F (RatFunc F) (c j) * xInv F ^ j) +
        xInv F ^ n * t := by
  induction n generalizing s with
  | zero => exact ⟨0, s, hs, by simp⟩
  | succ n ih =>
    obtain ⟨c₀, hc₀⟩ := exists_const_sub_lt_one F hs
    set s₁ := RatFunc.X * (s - algebraMap F (RatFunc F) c₀)
    have hs₁ : RatFunc.inftyValuation F s₁ ≤ 1 := by
      have h1 : RatFunc.inftyValuation F (s - algebraMap F (RatFunc F) c₀) ≤ exp (-1) := by
        rw [← lt_exp_add_one_iff]; simpa using hc₀
      rw [map_mul, RatFunc.inftyValuation.X]
      calc exp 1 * RatFunc.inftyValuation F (s - algebraMap F (RatFunc F) c₀)
          ≤ exp 1 * exp (-1) := by gcongr
        _ = 1 := by rw [← exp_add]; simp
    obtain ⟨c', t, ht, hst⟩ := ih hs₁
    refine ⟨fun j => if j = 0 then c₀ else c' (j - 1), t, ht, ?_⟩
    have hX : (RatFunc.X : RatFunc F) ≠ 0 := RatFunc.X_ne_zero
    have hs_eq : s = algebraMap F (RatFunc F) c₀ + xInv F * s₁ := by
      simp only [s₁, xInv]
      field_simp
      ring
    rw [Finset.sum_range_succ', hs_eq, hst]
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, if_true, pow_zero, mul_one,
      pow_succ, mul_add, Finset.mul_sum]
    ring_nf

end Laurent

variable {F : Type*} [Field F] [DecidableEq (RatFunc F)] {K : Type*} [Field K] [Algebra F[X] K]
  [Algebra (RatFunc F) K] [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K]
  [Algebra.IsSeparable (RatFunc F) K] [Algebra F K] [IsScalarTower F F[X] K]
  [IsScalarTower F (RatFunc F) K]

omit [IsScalarTower F (RatFunc F) K] in
theorem mem_finSpace_zero_iff {x : K} : x ∈ finSpace (0 : Divisor F K) ↔ x ∈ finChart F K := by
  change (∀ v : FinPlace F K, v.valuation K x ≤ exp ((0 : FinPlace F K →₀ ℤ) v)) ↔ _
  simp only [Finsupp.coe_zero, Pi.zero_apply, exp_zero]
  constructor
  · intro h
    obtain ⟨y, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := finChart F K) K x h
    exact y.2
  · intro hx v
    exact v.valuation_le_one (K := K) (⟨x, hx⟩ : finChart F K)

omit [IsScalarTower F[X] (RatFunc F) K] [IsScalarTower F F[X] K] in
theorem mem_infSpace_zero_iff {x : K} : x ∈ infSpace (0 : Divisor F K) ↔ x ∈ infChart F K := by
  change (∀ v : InfPlace F K, v.valuation K x ≤ exp ((0 : InfPlace F K →₀ ℤ) v)) ↔ _
  simp only [Finsupp.coe_zero, Pi.zero_apply, exp_zero]
  constructor
  · intro h
    obtain ⟨y, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := infChart F K) K x h
    exact y.2
  · intro hx v
    exact v.valuation_le_one (K := K) (⟨x, hx⟩ : infChart F K)

omit [FunctionField F K] [Algebra.IsSeparable (RatFunc F) K] [IsScalarTower F (RatFunc F) K] in
/-- An element of both charts is integral over the constants. -/
theorem isIntegral_of_mem_finChart_of_mem_infChart {x : K} (hx1 : x ∈ finChart F K)
    (hx2 : x ∈ infChart F K) : IsIntegral F x := by
  have h1 : IsIntegral F[X] x := hx1
  have h2 : IsIntegral (infRing F) x := hx2
  have e1 := minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc F) h1
  have e2 := minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc F) h2
  set q := minpoly F[X] x
  have hconstcoeff : ∀ i, (q.coeff i).natDegree = 0 := by
    intro i
    by_cases hqi : q.coeff i = 0
    · rw [hqi, natDegree_zero]
    have hmem : algebraMap F[X] (RatFunc F) (q.coeff i) ∈ infRing F := by
      have := congrArg (fun p => p.coeff i) (e1.symm.trans e2)
      simp only [coeff_map] at this
      rw [this]
      exact ((minpoly (infRing F) x).coeff i).2
    have hv := hmem
    change RatFunc.inftyValuation F _ ≤ 1 at hv
    rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation.polynomial F hqi, ← exp_zero,
      exp_le_exp] at hv
    omega
  set r := q.map (constantCoeff : F[X] →+* F)
  have hqr : q = r.map (algebraMap F F[X]) := by
    ext i : 1
    rw [coeff_map, coeff_map, Polynomial.algebraMap_eq, constantCoeff_apply,
      ← eq_C_of_natDegree_eq_zero (hconstcoeff i)]
  have hrm : r.Monic := (minpoly.monic h1).map _
  refine ⟨r, hrm, ?_⟩
  have h0 : aeval x q = 0 := minpoly.aeval F[X] x
  rw [hqr, aeval_map_algebraMap, aeval_def] at h0
  exact h0

variable (hconst : ∀ x : K, IsIntegral F x → ∃ a : F, algebraMap F K a = x)
include hconst

/-- **The constants**: `L(0) = F`. -/
theorem finSpace_zero_inf_infSpace_zero :
    finSpace (0 : Divisor F K) ⊓ infSpace (0 : Divisor F K) =
      LinearMap.range (Algebra.linearMap F K) := by
  ext x
  rw [Submodule.mem_inf, mem_finSpace_zero_iff, mem_infSpace_zero_iff, LinearMap.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨a, ha⟩ := hconst x (isIntegral_of_mem_finChart_of_mem_infChart h1 h2)
    exact ⟨a, ha⟩
  · rintro ⟨a, rfl⟩
    refine ⟨?_, ?_⟩
    · change algebraMap F K a ∈ finChart F K
      rw [IsScalarTower.algebraMap_apply F F[X] K]
      exact (finChart F K).algebraMap_mem _
    · change algebraMap F K a ∈ infChart F K
      rw [IsScalarTower.algebraMap_apply F (infRing F) K]
      exact (infChart F K).algebraMap_mem _

theorem finiteDimensional_ell_zero :
    FiniteDimensional F (finSpace (0 : Divisor F K) ⊓ infSpace (0 : Divisor F K) :
      Submodule F K) := by
  rw [finSpace_zero_inf_infSpace_zero hconst]
  infer_instance

/-- `ℓ(0) = 1`. -/
theorem ell_zero : ell (0 : Divisor F K) = 1 := by
  unfold ell
  rw [finSpace_zero_inf_infSpace_zero hconst,
    LinearMap.finrank_range_of_inj (algebraMap F K).injective, Module.finrank_self]

omit hconst

omit [Algebra F[X] K] [IsScalarTower F[X] (RatFunc F) K] [FunctionField F K] [Algebra F K]
  [IsScalarTower F F[X] K] [IsScalarTower F (RatFunc F) K] in
/-- Every element has bounded poles at infinity: `x^{-m} y ∈ O∞` for some `m`. -/
theorem exists_xInv_pow_mul_mem_infChart (y : K) :
    ∃ m : ℕ, algebraMap (RatFunc F) K (xInv F ^ m) * y ∈ infChart F K := by
  have hy : IsAlgebraic (infRing F) y :=
    (IsFractionRing.isAlgebraic_iff (infRing F) (RatFunc F) K).mpr
      (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨c, hc0, hci⟩ := hy.exists_integral_multiple
  set w : RatFunc F := (c : RatFunc F)
  have hw0 : w ≠ 0 := fun h => hc0 (Subtype.ext h)
  have hwv0 : RatFunc.inftyValuation F w ≠ 0 := (Valuation.ne_zero_iff _).mpr hw0
  have hwv : RatFunc.inftyValuation F w ≤ 1 := c.2
  set m : ℕ := (-log (RatFunc.inftyValuation F w)).toNat
  have hlog : log (RatFunc.inftyValuation F w) ≤ 0 := by
    rw [← exp_le_exp, exp_log hwv0, exp_zero]; exact hwv
  have hm : (m : ℤ) = -log (RatFunc.inftyValuation F w) := by simp only [m]; omega
  set u : RatFunc F := w * RatFunc.X ^ m
  have hu0 : u ≠ 0 := mul_ne_zero hw0 (pow_ne_zero _ RatFunc.X_ne_zero)
  have huv : RatFunc.inftyValuation F u = 1 := by
    rw [map_mul, map_pow, RatFunc.inftyValuation.X, ← exp_log hwv0, ← exp_nsmul, ← exp_add,
      nsmul_eq_mul, mul_one, hm]
    simp
  have huinv : u⁻¹ ∈ infRing F := by
    change RatFunc.inftyValuation F u⁻¹ ≤ 1
    rw [map_inv₀, huv, inv_one]
  refine ⟨m, ?_⟩
  have heq : algebraMap (RatFunc F) K (xInv F ^ m) * y =
      algebraMap (infRing F) K ⟨u⁻¹, huinv⟩ * (c • y) := by
    rw [Algebra.smul_def]
    change _ = algebraMap (RatFunc F) K u⁻¹ * (algebraMap (RatFunc F) K w * y)
    rw [← mul_assoc, ← map_mul]
    congr 2
    simp only [u, xInv, inv_pow]
    field_simp
  rw [heq]
  exact (isIntegral_algebraMap.mul hci)

/-- **Finiteness of the genus**: `K/(A + O∞)` is finite-dimensional. -/
theorem finiteDimensional_hOne_zero :
    FiniteDimensional F (K ⧸ (finSpace (0 : Divisor F K) ⊔ infSpace (0 : Divisor F K))) := by
  classical
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral F[X] (RatFunc F) K
  choose m hm using fun i : s => exists_xInv_pow_mul_mem_infChart (F := F) (b i)
  set N := Finset.univ.sup m
  set W : Submodule F K := Submodule.span F
    (Set.range fun p : s × Fin N => algebraMap (RatFunc F) K (xInv F ^ (p.2 : ℕ)) * b p.1)
  haveI : FiniteDimensional F W := FiniteDimensional.span_of_finite F (Set.finite_range _)
  set U := finSpace (0 : Divisor F K) ⊔ infSpace (0 : Divisor F K)
  have hcover : ∀ f : K, f ∈ U ⊔ W := by
    intro f
    rw [← b.sum_repr f]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨p, hp⟩ := exists_poly_sub_le_one F (b.repr f i)
    obtain ⟨c, t, ht, hst⟩ := exists_expansion F N hp
    have hsplit : b.repr f i • b i =
        algebraMap F[X] K p * b i +
          (∑ j ∈ Finset.range N, c j • (algebraMap (RatFunc F) K (xInv F ^ j) * b i)) +
          algebraMap (RatFunc F) K t *
            (algebraMap (RatFunc F) K (xInv F ^ (N - m i)) *
              (algebraMap (RatFunc F) K (xInv F ^ m i) * b i)) := by
      have hrepr : b.repr f i = algebraMap F[X] (RatFunc F) p +
          ((∑ j ∈ Finset.range N, algebraMap F (RatFunc F) (c j) * xInv F ^ j) +
            xInv F ^ N * t) := by rw [← hst]; ring
      have hpow : xInv F ^ N = xInv F ^ (N - m i) * xInv F ^ m i := by
        rw [← pow_add, Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ i))]
      rw [Algebra.smul_def, hrepr, map_add, map_add, add_mul, add_mul,
        ← IsScalarTower.algebraMap_apply, map_sum, Finset.sum_mul, add_assoc]
      congr 1
      congr 1
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, Algebra.smul_def, ← IsScalarTower.algebraMap_apply, mul_assoc]
      · rw [hpow, map_mul, map_mul]
        ring
    rw [hsplit]
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
      rw [mem_finSpace_zero_iff]
      exact (finChart F K).mul_mem ((finChart F K).algebraMap_mem p) (hb i)
    · refine Submodule.mem_sup_right (Submodule.sum_mem _ fun j hj => ?_)
      have hjN : j < N := Finset.mem_range.mp hj
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, ⟨j, hjN⟩), rfl⟩)
    · refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
      rw [mem_infSpace_zero_iff]
      have hxinv : xInv F ∈ infRing F := by
        change RatFunc.inftyValuation F (xInv F) ≤ 1
        rw [inftyValuation_xInv, ← exp_zero, exp_le_exp]; norm_num
      have htmem : t ∈ infRing F := ht
      have e1 : algebraMap (RatFunc F) K t = algebraMap (infRing F) K ⟨t, htmem⟩ := rfl
      have e2 : algebraMap (RatFunc F) K (xInv F ^ (N - m i)) =
          algebraMap (infRing F) K (⟨xInv F, hxinv⟩ ^ (N - m i)) := by
        rw [map_pow, map_pow]; rfl
      rw [e1, e2]
      exact (infChart F K).mul_mem ((infChart F K).algebraMap_mem _)
        ((infChart F K).mul_mem ((infChart F K).algebraMap_mem _) (hm i))
  refine Module.Finite.of_surjective (U.mkQ.comp W.subtype) ?_
  intro y
  obtain ⟨f, rfl⟩ := Submodule.mkQ_surjective U y
  obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.mp (hcover f)
  refine ⟨⟨w, hw⟩, ?_⟩
  change Submodule.Quotient.mk w = Submodule.Quotient.mk (a + w)
  rw [Submodule.Quotient.eq]
  rw [show w - (a + w) = -a by abel]
  exact Submodule.neg_mem _ ha

include hconst

/-- The zero divisor has finite-dimensional `L` and `H¹`. -/
theorem isFin_zero : IsFin (0 : Divisor F K) :=
  ⟨finiteDimensional_ell_zero hconst, finiteDimensional_hOne_zero⟩

omit hconst

variable (F K) in
/-- The genus: `g = dim K/(A + O∞) = h¹(0)`. -/
def genus : ℕ := hOne (0 : Divisor F K)

include hconst

/-- `χ(0) = 1 − g`. -/
theorem chi_zero : chi (0 : Divisor F K) = 1 - genus F K := by
  rw [chi, ell_zero hconst, genus]
  push_cast
  ring

/-- **Riemann's theorem**: `ℓ(D) − h¹(D) = deg D + 1 − g` for every divisor, with
`ℓ(D)` and `h¹(D)` finite. -/
theorem riemann_roch_chi (D : Divisor F K) :
    IsFin D ∧ (ell D : ℤ) - hOne D = D.deg + 1 - genus F K := by
  obtain ⟨h1, h2⟩ := chi_eq_deg_add_chi_zero (isFin_zero hconst) D
  refine ⟨h1, ?_⟩
  have h3 := chi_zero hconst
  unfold chi at h2 h3
  linarith

/-- **Riemann's inequality**: `ℓ(D) ≥ deg D + 1 − g`. -/
theorem riemann_inequality (D : Divisor F K) : D.deg + 1 - genus F K ≤ ell D := by
  have := (riemann_roch_chi hconst D).2
  have : (0 : ℤ) ≤ hOne D := Nat.cast_nonneg _
  linarith

end GaloisForLFunctions.CurvesOverFiniteFields
