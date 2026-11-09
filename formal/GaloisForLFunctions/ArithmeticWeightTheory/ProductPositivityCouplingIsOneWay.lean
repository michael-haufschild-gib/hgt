import GaloisForLFunctions.ArithmeticWeightTheory.TheGenericFibreHasUniformWeights
import GaloisForLFunctions.ArithmeticGaugeTheory.ThePoleDoesNotDecideTheHalfPowerLaw
import GaloisForLFunctions.SurfaceOfSpecZ.TheStepanovBoundIsAPrimeCount

/-!
# Product-positivity coupling in arithmetic families is one-way

In families of growing conductor or degree (`L_f = ζ · L_f^{var}`, such as Dedekind zeta functions
or Rankin–Selberg symmetric-square families), orthogonality of traces is asymptotic rather than
exact, and the base factor `ζ` is coupled to the variable factor `L_f^{var}` through nonnegative
Dirichlet and von Mangoldt coefficients of their product. This module proves that such positivity
couplings are strictly **one-way**: positivity of the base transfers to the product, whereas
positivity of the product together with variable-family data never bounds the base trace
`|c_B(log p)|` below the trivial exponent `1/2`.

1. **Abel–divisor monotonicity under symmetric shifts** (`geom_weighted_sum_ge_sum`,
   `zeta_mul_le_idRpow_mul`, `symmShift_mul_nonneg_of_zeta_mul_nonneg`,
   `symmShift_vonMangoldt_add_nonneg`).
   For every multiplicative `g : ArithmeticFunction ℝ` with `(ζ * g)(n) ≥ 0` (covering Hecke
   cofactors `m ↦ τ(m²)` and Dedekind cofactors) and every `a ≥ 0`, replacing `ζ` by the
   symmetric shift `ζ(s − a) ζ(s + a)` (`idRpow (-a) * idRpow a`) preserves nonnegativity of all
   Dirichlet and von Mangoldt product coefficients across the entire family while shifting the base
   zero width by `+a`.

2. **Simple-pole rational-prime Euler-factor doubling** (`summable_flipVM_rpow`,
   `flipSmooth_mul_nonneg`, `eventually_exists_primeWindowOf_doubledVM_sub_ge`,
   `not_both_primeWindowOf_power_bound`, `no_reverse_weight_bound_from_product_positivity`).
   For `1/2 < θ < 1`, doubling the rational-prime Euler factors `(1 − p^{−s})^{−1}` on the sparse
   prime set `flipPrimes θ` defines `doubledVM θ = Λ + flipVM θ` and `flipSmoothAF θ`:
   - `flipVM θ n · n^{−σ}` is summable for all `σ > θ` (including `σ = 1`), so the simple pole of
     residue `1` at `s = 1` and `archPoleWindow` are unchanged;
   - both Dirichlet and log-derivative product nonnegativity with any positively `ζ`-coupled
     variable cofactor `(g, lamVar)` are preserved identically;
   - by positivity and continuity of the cubic-spline autocorrelation at `0` together with
     pigeonhole clustering on `flipBlock θ k`, infinitely many primes `p` satisfy
     `primeWindowOf (doubledVM θ) p − primeWindow p ≥ c₀ · p^{θ − 1/2}`.
   Hence for every `a < 1/2`, `ζ` and `doubledVM θ` cannot both satisfy
   `|archPoleWindow p − primeWindowOf w p| ≤ K · p^a` on all primes, and no inequality derived from
   variable-family data and product-positivity couplings bounds `|c_B(log p)|` below `p^{1/2}`.
-/

open Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt Classical

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticGaugeTheory SurfaceOfSpecZ
open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold
open GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge (cubicSpline contDiff_cubicSpline
  hasCompactSupport_cubicSpline cubicSpline_eq_zero)

/-! ### 1. Abel–divisor monotonicity under symmetric shifts -/

/-- **Prime-power Abel monotonicity.** If `c₀, …, c_m` have nonnegative partial sums and `r ≥ 1`,
then `Σ_{j ≤ m} c_j ≤ Σ_{j ≤ m} r^{m − j} c_j`. -/
theorem geom_weighted_sum_ge_sum {c : ℕ → ℝ} {r : ℝ} (hr : 1 ≤ r) :
    ∀ m : ℕ, (∀ k ≤ m, 0 ≤ ∑ j ∈ range (k + 1), c j) →
      ∑ j ∈ range (m + 1), c j ≤ ∑ j ∈ range (m + 1), r ^ (m - j) * c j
  | 0, _ => by simp
  | m + 1, hc => by
    have hcm : 0 ≤ ∑ j ∈ range (m + 1), c j := hc m (Nat.le_succ m)
    have ih := geom_weighted_sum_ge_sum hr m fun k hk => hc k (Nat.le_succ_of_le hk)
    have hF_nn : 0 ≤ ∑ j ∈ range (m + 1), r ^ (m - j) * c j := hcm.trans ih
    have hrF : ∑ j ∈ range (m + 1), r ^ (m - j) * c j ≤
        r * ∑ j ∈ range (m + 1), r ^ (m - j) * c j := by
      calc ∑ j ∈ range (m + 1), r ^ (m - j) * c j
          = 1 * ∑ j ∈ range (m + 1), r ^ (m - j) * c j := (one_mul _).symm
        _ ≤ r * ∑ j ∈ range (m + 1), r ^ (m - j) * c j :=
            mul_le_mul_of_nonneg_right hr hF_nn
    have hstep : ∑ j ∈ range (m + 1), r ^ (m + 1 - j) * c j =
        r * ∑ j ∈ range (m + 1), r ^ (m - j) * c j := by
      rw [mul_sum]
      refine sum_congr rfl fun j hj => ?_
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
      rw [Nat.succ_sub hjm, pow_succ', mul_assoc]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul, hstep]
    linarith

/-- Real power arithmetic function `n ↦ n^a` (`0 ↦ 0`), representing `ζ(s − a)`. -/
def idRpow (a : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (n : ℝ) ^ a, if_pos rfl⟩

@[simp]
theorem idRpow_apply_of_ne_zero (a : ℝ) {n : ℕ} (hn : n ≠ 0) :
    idRpow a n = (n : ℝ) ^ a :=
  if_neg hn

theorem idRpow_nonneg (a : ℝ) (n : ℕ) : 0 ≤ idRpow a n := by
  by_cases hn : n = 0
  · subst hn; simp
  · rw [idRpow_apply_of_ne_zero a hn]; positivity

theorem isMultiplicative_idRpow (a : ℝ) : (idRpow a).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [idRpow], fun {m n} hm hn _ => ?_⟩
  rw [idRpow_apply_of_ne_zero a (mul_ne_zero hm hn), idRpow_apply_of_ne_zero a hm,
    idRpow_apply_of_ne_zero a hn, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

/-- **Global divisor-positivity transfer.** For every multiplicative `g : ArithmeticFunction ℝ`
with `(ζ * g)(n) ≥ 0` and every `a ≥ 0`, `(ζ * g)(n) ≤ (idRpow a * g)(n)` for all `n : ℕ`. -/
theorem zeta_mul_le_idRpow_mul {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative)
    (hpos : ∀ n : ℕ, 0 ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * g) n)
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * g) n ≤ (idRpow a * g) n := by
  have hM1 : ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * g).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_zeta.natCast.mul hg
  have hM2 : (idRpow a * g).IsMultiplicative := (isMultiplicative_idRpow a).mul hg
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one => rw [hM1.map_one, hM2.map_one]
  | coprime m k _ _ hcop ihm ihk =>
    rw [hM1.map_mul_of_coprime hcop, hM2.map_mul_of_coprime hcop]
    exact mul_le_mul ihm ihk (hpos k) ((hpos m).trans ihm)
  | prime_pow p m hp _ =>
    have hzeta : ∀ k : ℕ, ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * g) (p ^ k) =
        ∑ j ∈ range (k + 1), g (p ^ j) := fun k => by
      rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
    have hid : (idRpow a * g) (p ^ m) =
        ∑ j ∈ range (m + 1), ((p : ℝ) ^ a) ^ (m - j) * g (p ^ j) := by
      rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun d e => idRpow a d * g e),
        Nat.sum_divisors_prime_pow hp]
      refine sum_congr rfl fun j hj => ?_
      have hjm : j ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hj)
      have hpow_ne : p ^ (m - j) ≠ 0 := pow_ne_zero _ hp.ne_zero
      rw [Nat.pow_div hjm hp.pos, idRpow_apply_of_ne_zero a hpow_ne, Nat.cast_pow,
        ← Real.rpow_natCast (p : ℝ) (m - j), ← Real.rpow_mul (Nat.cast_nonneg p),
        mul_comm ((m - j : ℕ) : ℝ) a, Real.rpow_mul (Nat.cast_nonneg p), Real.rpow_natCast,
        mul_comm]
    rw [hzeta m, hid]
    refine geom_weighted_sum_ge_sum (Real.one_le_rpow (by exact_mod_cast hp.one_lt.le) ha) m ?_
    intro k _
    rw [← hzeta k]
    exact hpos (p ^ k)

/-- Right shift `idRpow a * g` preserves nonnegativity of Dirichlet coefficients. -/
theorem idRpow_mul_nonneg_of_zeta_mul_nonneg {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative)
    (hpos : ∀ n : ℕ, 0 ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * g) n)
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ (idRpow a * g) n :=
  (hpos n).trans (zeta_mul_le_idRpow_mul hg hpos ha n)

/-- **Symmetric shift preserves Dirichlet product positivity.** Replacing `ζ` by
`idRpow (-a) * idRpow a` (`ζ(s + a) ζ(s − a)`) preserves nonnegativity of all Dirichlet
coefficients with any positively `ζ`-coupled multiplicative cofactor `g`. -/
theorem symmShift_mul_nonneg_of_zeta_mul_nonneg {g : ArithmeticFunction ℝ} (hg : g.IsMultiplicative)
    (hpos : ∀ n : ℕ, 0 ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * g) n)
    {a : ℝ} (ha : 0 ≤ a) (n : ℕ) :
    0 ≤ (idRpow (-a) * (idRpow a * g)) n := by
  rw [ArithmeticFunction.mul_apply]
  exact sum_nonneg fun x _ => mul_nonneg (idRpow_nonneg (-a) x.1)
    (idRpow_mul_nonneg_of_zeta_mul_nonneg hg hpos ha x.2)

/-- **Symmetric shift preserves log-derivative positivity.** Since `cosh(a log n) ≥ 1`, any
variable von Mangoldt sequence `lamVar` with `Λ(n) + lamVar(n) ≥ 0` also satisfies
`cosh(a log n) Λ(n) + lamVar(n) ≥ 0`. -/
theorem symmShift_vonMangoldt_add_nonneg {lamVar : ℕ → ℝ}
    (hpos : ∀ n : ℕ, 0 ≤ (Λ n : ℝ) + lamVar n) (a : ℝ) (n : ℕ) :
    0 ≤ Real.cosh (a * Real.log n) * (Λ n : ℝ) + lamVar n := by
  have h1 : (Λ n : ℝ) ≤ Real.cosh (a * Real.log n) * (Λ n : ℝ) := by
    calc (Λ n : ℝ) = 1 * (Λ n : ℝ) := (one_mul _).symm
      _ ≤ Real.cosh (a * Real.log n) * (Λ n : ℝ) :=
          mul_le_mul_of_nonneg_right (Real.one_le_cosh _) ArithmeticFunction.vonMangoldt_nonneg
  linarith [hpos n]

/-! ### 2. Simple-pole rational-prime Euler-factor doubling -/

/-- Extra von Mangoldt weight from doubling the rational-prime Euler factors `(1 − p^{−s})^{−1}`
on `flipPrimes θ`: `Λ(n)` on prime powers with base prime in `flipPrimes θ`, and `0` elsewhere. -/
def flipVM (θ : ℝ) (n : ℕ) : ℝ :=
  if IsPrimePow n ∧ n.minFac ∈ flipPrimes θ then Λ n else 0

/-- Total von Mangoldt weight `Λ + flipVM θ` of `F_θ(s) = ζ(s) ∏_{p ∈ flipPrimes θ} (1 − p^{−s})^{−1}`. -/
def doubledVM (θ : ℝ) (n : ℕ) : ℝ :=
  (Λ n : ℝ) + flipVM θ n

/-- Smooth-integer indicator on `flipPrimes θ`, the Dirichlet series of
`∏_{p ∈ flipPrimes θ} (1 − p^{−s})^{−1}`. -/
def flipSmoothAF (θ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else if ∀ p : ℕ, p.Prime → p ∣ n → p ∈ flipPrimes θ then 1 else 0,
    if_pos rfl⟩

theorem flipVM_nonneg (θ : ℝ) (n : ℕ) : 0 ≤ flipVM θ n := by
  unfold flipVM
  split_ifs
  · exact ArithmeticFunction.vonMangoldt_nonneg
  · exact le_rfl

theorem flipVM_prime_of_mem {θ : ℝ} {p : ℕ} (hp : p.Prime) (hmem : p ∈ flipPrimes θ) :
    flipVM θ p = Real.log p := by
  unfold flipVM
  rw [if_pos ⟨hp.isPrimePow, by rw [hp.minFac_eq]; exact hmem⟩,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

theorem flipSmoothAF_nonneg (θ : ℝ) (n : ℕ) : 0 ≤ flipSmoothAF θ n := by
  simp only [flipSmoothAF, ArithmeticFunction.coe_mk]
  split_ifs <;> norm_num

theorem isMultiplicative_flipSmoothAF (θ : ℝ) : (flipSmoothAF θ).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, fun {m n} hm hn _ => ?_⟩
  · simp only [flipSmoothAF, ArithmeticFunction.coe_mk, one_ne_zero, ↓reduceIte]
    rw [if_pos]
    intro p hp hdvd
    exact absurd hdvd hp.not_dvd_one
  · simp only [flipSmoothAF, ArithmeticFunction.coe_mk, mul_ne_zero hm hn, hm, hn, ↓reduceIte]
    have hiff : (∀ p : ℕ, p.Prime → p ∣ m * n → p ∈ flipPrimes θ) ↔
        (∀ p : ℕ, p.Prime → p ∣ m → p ∈ flipPrimes θ) ∧
          (∀ p : ℕ, p.Prime → p ∣ n → p ∈ flipPrimes θ) :=
      ⟨fun h => ⟨fun p hp hd => h p hp (dvd_mul_of_dvd_left hd n),
          fun p hp hd => h p hp (dvd_mul_of_dvd_right hd m)⟩,
        fun ⟨h1, h2⟩ p hp hd => (hp.dvd_mul.mp hd).elim (h1 p hp) (h2 p hp)⟩
    by_cases hmn : ∀ p : ℕ, p.Prime → p ∣ m * n → p ∈ flipPrimes θ
    · obtain ⟨h1, h2⟩ := hiff.mp hmn
      rw [if_pos hmn, if_pos h1, if_pos h2, mul_one]
    · rw [if_neg hmn]
      by_cases h1 : ∀ p : ℕ, p.Prime → p ∣ m → p ∈ flipPrimes θ
      · have h2 : ¬ ∀ p : ℕ, p.Prime → p ∣ n → p ∈ flipPrimes θ :=
          fun h2 => hmn (hiff.mpr ⟨h1, h2⟩)
        rw [if_pos h1, if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]

/-- **Euler-factor doubling preserves both Dirichlet and log-derivative product nonnegativity.** -/
theorem flipSmooth_mul_nonneg (θ : ℝ) {g : ArithmeticFunction ℝ}
    (hpos : ∀ n : ℕ, 0 ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * g) n)
    {lamVar : ℕ → ℝ} (hlam : ∀ n : ℕ, 0 ≤ (Λ n : ℝ) + lamVar n) (n : ℕ) :
    0 ≤ (flipSmoothAF θ * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * g)) n ∧
      0 ≤ doubledVM θ n + lamVar n := by
  refine ⟨?_, ?_⟩
  · rw [ArithmeticFunction.mul_apply]
    exact sum_nonneg fun x _ => mul_nonneg (flipSmoothAF_nonneg θ x.1) (hpos x.2)
  · unfold doubledVM
    linarith [hlam n, flipVM_nonneg θ n]

/-- **Analyticity across `s = 1` (simple pole preserved).** For every `0 < θ` and `σ > θ` (in
particular at `σ = 1` when `θ < 1`), `Σ_n flipVM θ n · n^{−σ} < ∞`. Hence `-F_θ′/F_θ` differs
from `-ζ′/ζ` by a Dirichlet series converging absolutely on `Re s > θ`, preserving the exact
simple pole of residue `1` at `s = 1`. -/
theorem summable_flipVM_rpow {θ σ : ℝ} (hθ0 : 0 < θ) (hθσ : θ < σ) :
    Summable fun n : ℕ => flipVM θ n * (n : ℝ) ^ (-σ) := by
  have hσ0 : 0 < σ := hθ0.trans hθσ
  set q : ℝ := (2 : ℝ) ^ (-σ)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_lt_zero.mpr hσ0)
  have h1q : 0 < 1 - q := sub_pos.mpr hq1
  set r : ℝ := (4 : ℝ) ^ (θ - σ)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hθσ)
  set g : ℕ → ℝ := fun k => Real.log 4 / (1 - q) * (((k : ℝ) + 1) ^ 1 * r ^ k)
  have hg_sum : Summable g := (summable_poly_mul_geometric 1 hr0 hr1).mul_left _
  have hg_nn : ∀ k, 0 ≤ g k := fun k => by dsimp only [g]; positivity
  refine summable_of_sum_range_le (c := ∑' k, g k)
    (fun n => mul_nonneg (flipVM_nonneg θ n) (by positivity))
    (fun N => ?_)
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact tsum_nonneg hg_nn
  set K := Nat.log 4 N + 1
  set S := (range N).filter (fun n => IsPrimePow n ∧ n.minFac ∈ flipPrimes θ)
  have hsum_eq : ∑ n ∈ range N, flipVM θ n * (n : ℝ) ^ (-σ) =
      ∑ n ∈ S, (Λ n : ℝ) * (n : ℝ) ^ (-σ) := by
    rw [sum_filter]
    refine sum_congr rfl fun n _ => ?_
    unfold flipVM
    split_ifs <;> ring
  set F := (range K).biUnion (flipBlock θ)
  have hmaps : ∀ n ∈ S, n.minFac ∈ F := by
    intro n hn
    obtain ⟨hnN, _, k, hk⟩ := mem_filter.mp hn
    have h4p : 4 ^ k < n.minFac := (mem_flipBlock hk).2.1
    have hp_le_n : n.minFac ≤ n := Nat.minFac_le (Nat.pos_of_ne_zero fun h0 => by
      subst h0; exact not_isPrimePow_zero (mem_filter.mp hn).2.1)
    have h4N : 4 ^ k ≤ N := (h4p.le.trans hp_le_n).trans (mem_range.mp hnN).le
    exact mem_biUnion.mpr ⟨k, mem_range.mpr (Nat.lt_succ_of_le
      (Nat.le_log_of_pow_le (by norm_num) h4N)), hk⟩
  -- Bound the prime-power contribution above one prime `p ∈ flipBlock θ k`
  have hp_sum : ∀ p : ℕ, p.Prime →
      ∑ n ∈ S.filter (fun n => n.minFac = p), (Λ n : ℝ) * (n : ℝ) ^ (-σ) ≤
        Real.log p * (p : ℝ) ^ (-σ) / (1 - q) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hpq : (p : ℝ) ^ (-σ) ≤ q := by
      have := Real.rpow_le_rpow zero_le_two hp2 hσ0.le
      have hinv := inv_anti₀ (Real.rpow_pos_of_pos zero_lt_two σ) this
      simpa [q, Real.rpow_neg hp0.le, Real.rpow_neg zero_le_two] using hinv
    have hsub : S.filter (fun n => n.minFac = p) ⊆ (range N).image (fun j => p ^ (j + 1)) := by
      intro n hn
      obtain ⟨hnS, hmin⟩ := mem_filter.mp hn
      obtain ⟨hnN, hpp, _⟩ := mem_filter.mp hnS
      have hfac := hpp.minFac_pow_factorization_eq
      rw [hmin] at hfac
      set m := n.factorization p
      have hm1 : 1 ≤ m := by
        by_contra h0
        rw [show m = 0 by omega, pow_zero] at hfac
        exact hpp.ne_one hfac.symm
      have hmN : m - 1 < N := by
        have : m < p ^ m := Nat.lt_pow_self hp.one_lt
        have hpN : p ^ m < N := hfac.trans_lt (mem_range.mp hnN)
        omega
      exact mem_image.mpr ⟨m - 1, mem_range.mpr hmN, by rw [Nat.sub_add_cancel hm1, hfac]⟩
    calc ∑ n ∈ S.filter (fun n => n.minFac = p), (Λ n : ℝ) * (n : ℝ) ^ (-σ)
        ≤ ∑ n ∈ (range N).image (fun j => p ^ (j + 1)), (Λ n : ℝ) * (n : ℝ) ^ (-σ) :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
            mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
      _ ≤ ∑ j ∈ range N, (Λ (p ^ (j + 1)) : ℝ) * ((p ^ (j + 1) : ℕ) : ℝ) ^ (-σ) :=
          sum_image_le_of_nonneg fun _ _ =>
            mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
      _ ≤ ∑ j ∈ range N, Real.log p * (p : ℝ) ^ (-σ) * q ^ j := sum_le_sum fun j _ => by
          rw [ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero j),
            ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow,
            ← Real.rpow_natCast (p : ℝ), ← Real.rpow_mul hp0.le,
            show ((j + 1 : ℕ) : ℝ) * -σ = -σ + -σ * (j : ℝ) by push_cast; ring,
            Real.rpow_add hp0, mul_comm (-σ) (j : ℝ), Real.rpow_mul hp0.le, Real.rpow_natCast,
            ← mul_assoc]
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hpq j)
            (mul_nonneg (Real.log_nonneg (by linarith)) (by positivity))
      _ = Real.log p * (p : ℝ) ^ (-σ) * ∑ j ∈ range N, q ^ j := by rw [← mul_sum]
      _ ≤ Real.log p * (p : ℝ) ^ (-σ) * (1 / (1 - q)) := by
          refine mul_le_mul_of_nonneg_left ?_
            (mul_nonneg (Real.log_nonneg (by linarith)) (by positivity))
          rw [le_div_iff₀ h1q]
          have hgeom : (1 - q) * ∑ j ∈ range N, q ^ j = 1 - q ^ N := by
            have := geom_sum_mul q N
            linarith
          linarith [pow_nonneg hq0 N]
      _ = Real.log p * (p : ℝ) ^ (-σ) / (1 - q) := by ring
  -- Sum over `F = ⋃_{k < K} flipBlock θ k`
  have hfib : ∑ n ∈ S, (Λ n : ℝ) * (n : ℝ) ^ (-σ) =
      ∑ p ∈ F, ∑ n ∈ S.filter (fun n => n.minFac = p), (Λ n : ℝ) * (n : ℝ) ^ (-σ) :=
    (sum_fiberwise_of_maps_to hmaps _).symm
  have hblock_le : ∀ k : ℕ, ∑ p ∈ flipBlock θ k, Real.log p * (p : ℝ) ^ (-σ) / (1 - q) ≤ g k := by
    intro k
    have hterm : ∀ p ∈ flipBlock θ k,
        Real.log p * (p : ℝ) ^ (-σ) / (1 - q) ≤
          Real.log 4 * ((k : ℝ) + 1) * ((4 : ℝ) ^ (-σ)) ^ k / (1 - q) := by
      intro p hp
      obtain ⟨hpr, h4p, hp2⟩ := mem_flipBlock hp
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
      have h4k_le : (4 : ℝ) ^ k ≤ p := by exact_mod_cast h4p.le
      have hp_le : (p : ℝ) ≤ 4 ^ (k + 1) := by
        have : p ≤ 4 * 4 ^ k := by omega
        rw [pow_succ']
        exact_mod_cast this
      have hlog_le : Real.log p ≤ Real.log 4 * ((k : ℝ) + 1) := by
        calc Real.log p ≤ Real.log ((4 : ℝ) ^ (k + 1)) := Real.log_le_log hp0 hp_le
          _ = ((k + 1 : ℕ) : ℝ) * Real.log 4 := Real.log_pow 4 (k + 1)
          _ = Real.log 4 * ((k : ℝ) + 1) := by push_cast; ring
      have hrpow_le : (p : ℝ) ^ (-σ) ≤ ((4 : ℝ) ^ (-σ)) ^ k := by
        have h1 := Real.rpow_le_rpow (by positivity) h4k_le hσ0.le
        have h2 := inv_anti₀ (Real.rpow_pos_of_pos (by positivity) σ) h1
        rw [← Real.rpow_neg hp0.le, ← Real.rpow_neg (by positivity),
          ← Real.rpow_natCast (4 : ℝ) k, ← Real.rpow_mul (by norm_num), mul_comm,
          Real.rpow_mul (by norm_num), Real.rpow_natCast] at h2
        exact h2
      refine div_le_div_of_nonneg_right ?_ h1q.le
      exact mul_le_mul hlog_le hrpow_le (by positivity)
        (mul_nonneg (Real.log_nonneg (by norm_num)) (by positivity))
    have hcard : ((flipBlock θ k).card : ℝ) ≤ ((4 : ℝ) ^ θ) ^ k := by
      rw [card_flipBlock]
      exact (Nat.cast_le.mpr (min_le_left _ _)).trans (flipSize_le k)
    have hr_split : ((4 : ℝ) ^ θ) ^ k * ((4 : ℝ) ^ (-σ)) ^ k = r ^ k := by
      rw [← mul_pow, ← Real.rpow_add (by norm_num), ← sub_eq_add_neg]
    calc ∑ p ∈ flipBlock θ k, Real.log p * (p : ℝ) ^ (-σ) / (1 - q)
        ≤ ∑ _p ∈ flipBlock θ k, Real.log 4 * ((k : ℝ) + 1) * ((4 : ℝ) ^ (-σ)) ^ k / (1 - q) :=
          sum_le_sum hterm
      _ = ((flipBlock θ k).card : ℝ) *
            (Real.log 4 * ((k : ℝ) + 1) * ((4 : ℝ) ^ (-σ)) ^ k / (1 - q)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ ((4 : ℝ) ^ θ) ^ k *
            (Real.log 4 * ((k : ℝ) + 1) * ((4 : ℝ) ^ (-σ)) ^ k / (1 - q)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = g k := by
          dsimp only [g]
          rw [pow_one, ← hr_split]
          ring
  calc ∑ n ∈ range N, flipVM θ n * (n : ℝ) ^ (-σ)
      = ∑ p ∈ F, ∑ n ∈ S.filter (fun n => n.minFac = p), (Λ n : ℝ) * (n : ℝ) ^ (-σ) := by
        rw [hsum_eq, hfib]
    _ ≤ ∑ p ∈ F, Real.log p * (p : ℝ) ^ (-σ) / (1 - q) := sum_le_sum fun p hp => by
        obtain ⟨k, _, hk⟩ := mem_biUnion.mp hp
        exact hp_sum p (mem_flipBlock hk).1
    _ ≤ ∑ k ∈ range K, ∑ p ∈ flipBlock θ k, Real.log p * (p : ℝ) ^ (-σ) / (1 - q) :=
        sum_biUnion_le
    _ ≤ ∑ k ∈ range K, g k := sum_le_sum fun k _ => hblock_le k
    _ ≤ ∑' k, g k := hg_sum.sum_le_tsum (range K) fun k _ => hg_nn k

/-! ### 3. Cubic-spline prime windows and failure of reverse weight bounds -/

/-- Smoothed prime-comb kernel of an arbitrary real von Mangoldt weight `lam : ℕ → ℝ`. -/
def smoothedPrimeKernelOf (lam : ℕ → ℝ) (f : ℝ → ℝ) (m n : ℕ) : ℝ :=
  -(FrustratedArithmeticDirichletForms.weightedPrimePart lam
    (Zeta23.EF.weilTest (cx (scaleShift (Real.log m) f)) (cx (scaleShift (Real.log n) f)))).re

/-- Smoothed prime count `P_lam(d)` of `lam` in the cubic-spline window of degree `d`. -/
def primeWindowOf (lam : ℕ → ℝ) (d : ℕ) : ℝ :=
  -smoothedPrimeKernelOf lam cubicSpline d 1

@[simp]
theorem primeWindowOf_vonMangoldt (d : ℕ) :
    primeWindowOf (fun k => (Λ k : ℝ)) d = primeWindow d := rfl

/-- Real cubic-spline autocorrelation `K₀(v) = Re (B ⋆ B̃)(v) = ∫ B(u) B(u − v) du`. -/
def splineAutoCorr (v : ℝ) : ℝ :=
  (Zeta23.EF.weilTest (cx cubicSpline) (cx cubicSpline) v).re

private theorem splineAutoCorr_eq_integral (v : ℝ) :
    splineAutoCorr v = ∫ u, cubicSpline u * cubicSpline (u - v) := by
  rw [splineAutoCorr, weilTest_ofReal, Complex.ofReal_re]

theorem splineAutoCorr_nonneg (v : ℝ) : 0 ≤ splineAutoCorr v := by
  rw [splineAutoCorr_eq_integral]
  exact integral_nonneg fun u => mul_nonneg (RHTower.WeilDeletion.upow_nonneg one_pos 3 u)
    (RHTower.WeilDeletion.upow_nonneg one_pos 3 (u - v))

theorem continuous_splineAutoCorr : Continuous splineAutoCorr := by
  have hc : ContDiff ℝ 2 (cx cubicSpline) := cx_contDiff contDiff_cubicSpline
  have hs : HasCompactSupport (cx cubicSpline) := cx_hasCompactSupport hasCompactSupport_cubicSpline
  exact Complex.continuous_re.comp (Zeta23.EF.weilTest_contDiff hc hc.continuous hs).continuous

theorem splineAutoCorr_zero_pos : 0 < splineAutoCorr 0 := by
  have hc_cont : Continuous cubicSpline := contDiff_cubicSpline.continuous
  have hc_ne : ∃ u₀ : ℝ, cubicSpline u₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    have h1 : ∫ u, cubicSpline u = 1 := RHTower.WeilDeletion.integral_upow one_pos 3
    have h0 : ∫ u, cubicSpline u = 0 := by simp [hall]
    linarith
  obtain ⟨u₀, hu₀⟩ := hc_ne
  rw [splineAutoCorr_eq_integral]
  have heq : (fun u => cubicSpline u * cubicSpline (u - 0)) = fun u => cubicSpline u ^ 2 := by
    funext u; rw [sub_zero, sq]
  rw [heq]
  have hsq_cont : Continuous fun u => cubicSpline u ^ 2 := hc_cont.pow 2
  have hsq_supp : HasCompactSupport fun u => cubicSpline u ^ 2 := by
    refine HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (f := fun u => cubicSpline u ^ 2) (K := Set.Icc (-4 : ℝ) 4) fun u hu => ?_
    by_contra hI
    have habs : 4 < |u| := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hI
      rcases hI with h | h
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl h)
    exact hu (by simp [cubicSpline_eq_zero habs])
  have hsq_int : Integrable fun u => cubicSpline u ^ 2 :=
    hsq_cont.integrable_of_hasCompactSupport hsq_supp
  by_contra hle
  have hzero : ∫ u, cubicSpline u ^ 2 = 0 :=
    le_antisymm (not_lt.mp hle) (integral_nonneg fun u => sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun u => sq_nonneg _) hsq_int).mp hzero
  have hfun := (Continuous.ae_eq_iff_eq volume hsq_cont continuous_const).mp hae
  exact pow_ne_zero 2 hu₀ (congrFun hfun u₀)

private theorem weilTest_cubicSpline_eq_zero {v : ℝ} (hv : 8 < |v|) :
    Zeta23.EF.weilTest (cx cubicSpline) (cx cubicSpline) v = 0 := by
  rw [weilTest_ofReal]
  have h0 : (fun u => cubicSpline u * cubicSpline (u - v)) = fun _ => 0 := by
    funext u
    by_cases hu : 4 < |u|
    · rw [cubicSpline_eq_zero hu, zero_mul]
    · have huv : 4 < |u - v| := by
        have htri : |v| ≤ |u| + |u - v| := by
          calc |v| = |u - (u - v)| := by ring_nf
            _ ≤ |u| + |u - v| := abs_sub _ _
        linarith
      rw [cubicSpline_eq_zero huv, mul_zero]
  simp [h0]

/-- Exact finite-sum formula for `primeWindowOf lam d` at any `d ≥ 1` and cutoff above `d · e⁹`. -/
theorem primeWindowOf_eq_sum {d N : ℕ} (hd : 1 ≤ d)
    (hN : ⌊Real.exp (Real.log d + 9)⌋₊ + 1 ≤ N) (lam : ℕ → ℝ) :
    primeWindowOf lam d = ∑ n ∈ range N,
      (if 2 ≤ n then lam n / Real.sqrt n else 0) *
        (splineAutoCorr (Real.log n - Real.log d) + splineAutoCorr (-Real.log n - Real.log d)) := by
  set k := Zeta23.EF.weilTest (cx (scaleShift (Real.log d) cubicSpline))
    (cx (scaleShift (Real.log (1 : ℕ)) cubicSpline))
  have hk_eq : ∀ x : ℝ, k x = Zeta23.EF.weilTest (cx cubicSpline) (cx cubicSpline)
      (x - Real.log d) := fun x => by
    dsimp only [k]
    rw [weilTest_scaleShift, Nat.cast_one, Real.log_one, add_zero]
  have hvan : ∀ n : ℕ, N ≤ n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0 := by
    intro n hn
    have hn_gt : Real.exp (Real.log d + 9) < n := by
      have hfl := Nat.lt_floor_add_one (Real.exp (Real.log d + 9))
      have hNR : (⌊Real.exp (Real.log d + 9)⌋₊ + 1 : ℝ) ≤ n := by
        exact_mod_cast hN.trans hn
      linarith
    have hn0 : (0 : ℝ) < n := (Real.exp_pos _).trans hn_gt
    have hlog_gt : Real.log d + 9 < Real.log n := (Real.lt_log_iff_exp_lt hn0).mpr hn_gt
    have hlogd_nn : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd)
    rw [hk_eq, hk_eq]
    exact ⟨weilTest_cubicSpline_eq_zero (by rw [abs_of_pos (by linarith)]; linarith),
      weilTest_cubicSpline_eq_zero (by rw [abs_of_neg (by linarith)]; linarith)⟩
  unfold primeWindowOf smoothedPrimeKernelOf
  rw [neg_neg, FrustratedArithmeticDirichletForms.weightedPrimePart_affine hvan, Complex.re_sum]
  refine sum_congr rfl fun n _ => ?_
  rw [Complex.re_ofReal_mul, Complex.add_re, hk_eq, hk_eq, splineAutoCorr, splineAutoCorr]

theorem primeWindowOf_add {d : ℕ} (hd : 1 ≤ d) (lam₁ lam₂ : ℕ → ℝ) :
    primeWindowOf (fun n => lam₁ n + lam₂ n) d = primeWindowOf lam₁ d + primeWindowOf lam₂ d := by
  set N := ⌊Real.exp (Real.log d + 9)⌋₊ + 1
  rw [primeWindowOf_eq_sum hd le_rfl, primeWindowOf_eq_sum hd le_rfl,
    primeWindowOf_eq_sum hd le_rfl, ← sum_add_distrib]
  refine sum_congr rfl fun n _ => ?_
  split_ifs <;> ring

theorem sum_le_primeWindowOf {d : ℕ} (hd : 1 ≤ d) {lam : ℕ → ℝ} (hlam : ∀ n, 0 ≤ lam n)
    {S : Finset ℕ} (hS : ∀ q ∈ S, 2 ≤ q) :
    ∑ q ∈ S, lam q / Real.sqrt q * splineAutoCorr (Real.log q - Real.log d) ≤
      primeWindowOf lam d := by
  set N := max (⌊Real.exp (Real.log d + 9)⌋₊ + 1) (S.sup id + 1)
  rw [primeWindowOf_eq_sum hd (le_max_left _ _)]
  have hsub : S ⊆ range N := fun q hq => mem_range.mpr <|
    lt_of_lt_of_le (Nat.lt_succ_of_le (Finset.le_sup (f := id) hq)) (le_max_right _ _)
  calc ∑ q ∈ S, lam q / Real.sqrt q * splineAutoCorr (Real.log q - Real.log d)
      ≤ ∑ q ∈ S, (if 2 ≤ q then lam q / Real.sqrt q else 0) *
          (splineAutoCorr (Real.log q - Real.log d) +
            splineAutoCorr (-Real.log q - Real.log d)) := sum_le_sum fun q hq => by
        rw [if_pos (hS q hq)]
        have hw : 0 ≤ lam q / Real.sqrt q := div_nonneg (hlam q) (Real.sqrt_nonneg _)
        have hk2 : 0 ≤ splineAutoCorr (-Real.log q - Real.log d) := splineAutoCorr_nonneg _
        nlinarith
    _ ≤ ∑ n ∈ range N, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
          (splineAutoCorr (Real.log n - Real.log d) +
            splineAutoCorr (-Real.log n - Real.log d)) :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by
          split_ifs
          · exact mul_nonneg (div_nonneg (hlam n) (Real.sqrt_nonneg _))
              (add_nonneg (splineAutoCorr_nonneg _) (splineAutoCorr_nonneg _))
          · simp

/-- Logarithmic bin index partitioning `[k log 4, k log 4 + log 2]` into `M` subintervals. -/
private def logBin (M k q : ℕ) : ℕ :=
  min (M - 1) ⌊(Real.log q - k * Real.log 4) / (Real.log 2 / M)⌋₊

private theorem abs_log_sub_le_of_logBin_eq {θ : ℝ} {M k q₁ q₂ : ℕ} (hM : 1 ≤ M)
    (hq₁ : q₁ ∈ flipBlock θ k) (hq₂ : q₂ ∈ flipBlock θ k)
    (hbin : logBin M k q₁ = logBin M k q₂) :
    |Real.log q₁ - Real.log q₂| ≤ Real.log 2 / M := by
  set δ : ℝ := Real.log 2 / M
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hδ : 0 < δ := div_pos (Real.log_pos one_lt_two) hM0
  have hin : ∀ q ∈ flipBlock θ k,
      (logBin M k q : ℝ) * δ ≤ Real.log q - k * Real.log 4 ∧
        Real.log q - k * Real.log 4 ≤ ((logBin M k q : ℝ) + 1) * δ := by
    intro q hq
    obtain ⟨hpr, h4q, hq2⟩ := mem_flipBlock hq
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hpr.pos
    set x : ℝ := Real.log q - k * Real.log 4
    have hx0 : 0 ≤ x := by
      have : Real.log ((4 : ℝ) ^ k) ≤ Real.log q :=
        Real.log_le_log (by positivity) (by exact_mod_cast h4q.le)
      rw [Real.log_pow] at this
      dsimp only [x]; linarith
    have hxM : x ≤ (M : ℝ) * δ := by
      have hMδ : (M : ℝ) * δ = Real.log 2 := mul_div_cancel₀ _ hM0.ne'
      have hlog_le : Real.log q ≤ Real.log (2 * (4 : ℝ) ^ k) :=
        Real.log_le_log hq0 (by exact_mod_cast hq2)
      rw [Real.log_mul two_ne_zero (by positivity), Real.log_pow] at hlog_le
      rw [hMδ]; dsimp only [x]; linarith
    set fl := ⌊x / δ⌋₊
    by_cases hlt : fl < M - 1
    · have hjb : logBin M k q = fl := min_eq_right hlt.le
      rw [hjb]
      have h1 : (fl : ℝ) ≤ x / δ := Nat.floor_le (div_nonneg hx0 hδ.le)
      have h2 : x / δ < (fl : ℝ) + 1 := Nat.lt_floor_add_one (x / δ)
      exact ⟨(le_div_iff₀ hδ).mp h1, ((div_lt_iff₀ hδ).mp h2).le⟩
    · push Not at hlt
      have hjb : logBin M k q = M - 1 := min_eq_left hlt
      rw [hjb, Nat.cast_sub hM, Nat.cast_one]
      have h1 : ((M : ℝ) - 1) ≤ (fl : ℝ) := by exact_mod_cast hlt
      have h2 : (fl : ℝ) ≤ x / δ := Nat.floor_le (div_nonneg hx0 hδ.le)
      refine ⟨(le_div_iff₀ hδ).mp (h1.trans h2), ?_⟩
      simpa only [sub_add_cancel] using hxM
  obtain ⟨h1l, h1u⟩ := hin q₁ hq₁
  obtain ⟨h2l, h2u⟩ := hin q₂ hq₂
  rw [hbin] at h1l h1u
  rw [abs_le]
  constructor <;> linarith

/-- **Window-shift growth on `flipPrimes θ`.** For `1/2 < θ < 1`, there exists `c₀ > 0` such that
for all sufficiently large `k` some prime `p ∈ flipBlock θ k` satisfies
`primeWindowOf (doubledVM θ) p − primeWindow p ≥ c₀ · p^{θ − 1/2}`. -/
theorem eventually_exists_primeWindowOf_doubledVM_sub_ge {θ : ℝ} (hθ : 1 / 2 < θ) (hθ1 : θ < 1) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ᶠ k : ℕ in atTop, ∃ p ∈ flipBlock θ k,
      c₀ * (p : ℝ) ^ (θ - 1 / 2) ≤ primeWindowOf (doubledVM θ) p - primeWindow p := by
  have hK0 : 0 < splineAutoCorr 0 := splineAutoCorr_zero_pos
  -- Continuity of `splineAutoCorr` at `0` gives a logarithmic bin resolution `M ≥ 1`
  have hnhds : {v : ℝ | splineAutoCorr 0 / 2 < splineAutoCorr v} ∈ 𝓝 (0 : ℝ) :=
    continuous_splineAutoCorr.continuousAt.preimage_mem_nhds (Ioi_mem_nhds (half_lt_self hK0))
  obtain ⟨ε, hε0, hε⟩ := Metric.mem_nhds_iff.mp hnhds
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (Real.log 2 / ε)
  set M := M₀ + 1
  have hM1 : 1 ≤ M := Nat.succ_le_succ (Nat.zero_le M₀)
  have hM_pos : (0 : ℝ) < M := by exact_mod_cast hM1
  have hδ_lt : Real.log 2 / (M : ℝ) < ε := by
    rw [div_lt_iff₀ hM_pos]
    rw [div_lt_iff₀ hε0] at hM₀
    have hMM₀ : (M₀ : ℝ) < M := by push_cast [M]; linarith
    nlinarith [hε0]
  have hK_near : ∀ v : ℝ, |v| ≤ Real.log 2 / M → splineAutoCorr 0 / 2 ≤ splineAutoCorr v := by
    intro v hv
    refine (hε ?_).le
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact hv.trans_lt hδ_lt
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set c₀ : ℝ := Real.log 2 * (splineAutoCorr 0 / 2) / (4 * M * (2 : ℝ) ^ θ)
  have hc₀ : 0 < c₀ := by positivity
  refine ⟨c₀, hc₀, ?_⟩
  have hgrow := (tendsto_pow_atTop_atTop_of_one_lt
    (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 4) (by linarith : 0 < θ))).eventually_gt_atTop (2 : ℝ)
  filter_upwards [eventually_card_flipBlock hθ1, hgrow] with k hk_card hk_two
  have hfs_ge2 : 2 ≤ flipSize θ k := by
    have hfl : (2 : ℝ) < (4 : ℝ) ^ (θ * k) := by
      rwa [Real.rpow_mul (by norm_num), Real.rpow_natCast]
    exact Nat.le_floor hfl.le
  -- Pigeonhole `flipBlock θ k` into `range M` via `logBin M k`
  have hmaps : ∀ q ∈ flipBlock θ k, logBin M k q ∈ range M := fun q _ =>
    mem_range.mpr ((min_le_left _ _).trans_lt (Nat.sub_lt hM1 zero_lt_one))
  have hsum_fib : ∑ j ∈ range M, ((flipBlock θ k).filter (fun q => logBin M k q = j)).card =
      (flipBlock θ k).card :=
    (Finset.card_eq_sum_card_fiberwise hmaps).symm
  have hsum_le : ∑ _j ∈ range M, (((flipBlock θ k).card : ℝ) / M) ≤
      ∑ j ∈ range M, (((flipBlock θ k).filter (fun q => logBin M k q = j)).card : ℝ) := by
    rw [sum_const, card_range, nsmul_eq_mul, mul_div_cancel₀ _ hM_pos.ne', ← Nat.cast_sum,
      hsum_fib]
  have hne_M : (range M).Nonempty := nonempty_range_iff.mpr (by omega)
  obtain ⟨j, _, hj_card⟩ := exists_le_of_sum_le hne_M hsum_le
  set S := (flipBlock θ k).filter (fun q => logBin M k q = j)
  have hS_card : ((flipBlock θ k).card : ℝ) / M ≤ S.card := hj_card
  have hS_pos : 0 < S.card := by
    have hposR : (0 : ℝ) < S.card := by
      refine lt_of_lt_of_le ?_ hS_card
      rw [hk_card]
      have : (2 : ℝ) ≤ flipSize θ k := by exact_mod_cast hfs_ge2
      positivity
    exact_mod_cast hposR
  obtain ⟨p, hpS⟩ := Finset.card_pos.mp hS_pos
  have hp_blk : p ∈ flipBlock θ k := (mem_filter.mp hpS).1
  obtain ⟨hp_prime, h4p, hp2⟩ := mem_flipBlock hp_blk
  refine ⟨p, hp_blk, ?_⟩
  have hdub : doubledVM θ = fun n => (Λ n : ℝ) + flipVM θ n := rfl
  rw [← primeWindowOf_vonMangoldt, hdub, primeWindowOf_add hp_prime.one_le,
    add_sub_cancel_left]
  have hlow := sum_le_primeWindowOf hp_prime.one_le (flipVM_nonneg θ)
    (fun q hq => (mem_flipBlock (mem_filter.mp hq).1).1.two_le)
  -- Lower bound each `q ∈ S`
  have hterm_ge : ∀ q ∈ S,
      Real.log 2 / Real.sqrt (2 * (4 : ℝ) ^ k) * (splineAutoCorr 0 / 2) ≤
        flipVM θ q / Real.sqrt q * splineAutoCorr (Real.log q - Real.log p) := by
    intro q hq
    obtain ⟨hq_blk, hqj⟩ := mem_filter.mp hq
    obtain ⟨hq_prime, _, hq2⟩ := mem_flipBlock hq_blk
    rw [flipVM_prime_of_mem hq_prime ⟨k, hq_blk⟩]
    have hlog_ge : Real.log 2 ≤ Real.log q :=
      Real.log_le_log zero_lt_two (by exact_mod_cast hq_prime.two_le)
    have hsqrt_le : Real.sqrt q ≤ Real.sqrt (2 * (4 : ℝ) ^ k) :=
      Real.sqrt_le_sqrt (by exact_mod_cast hq2)
    have hsqrt_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by exact_mod_cast hq_prime.pos)
    have hdiv_ge : Real.log 2 / Real.sqrt (2 * (4 : ℝ) ^ k) ≤ Real.log q / Real.sqrt q :=
      div_le_div₀ hlog2.le hlog_ge hsqrt_pos hsqrt_le
    have hbin_eq : logBin M k q = logBin M k p := hqj.trans (mem_filter.mp hpS).2.symm
    have hK_ge := hK_near (Real.log q - Real.log p) (abs_log_sub_le_of_logBin_eq hM1 hq_blk hp_blk hbin_eq)
    exact mul_le_mul hdiv_ge hK_ge (by positivity) (by positivity)
  -- Compare `(flipSize θ k / M) / √(2 · 4^k)` with `p^{θ − 1/2}`
  have hfs_ge_half : (4 : ℝ) ^ (θ * k) / 2 ≤ flipSize θ k := by
    have hlt1 : (4 : ℝ) ^ (θ * k) < flipSize θ k + 1 := Nat.lt_floor_add_one _
    have h2le : (2 : ℝ) ≤ flipSize θ k := by exact_mod_cast hfs_ge2
    linarith
  have hS_ge : (4 : ℝ) ^ (θ * k) / (2 * M) ≤ S.card := by
    calc (4 : ℝ) ^ (θ * k) / (2 * M) = ((4 : ℝ) ^ (θ * k) / 2) / M := by ring
      _ ≤ (flipSize θ k : ℝ) / M := div_le_div_of_nonneg_right hfs_ge_half hM_pos.le
      _ = ((flipBlock θ k).card : ℝ) / M := by rw [hk_card]
      _ ≤ S.card := hS_card
  have hsqrt_ub : Real.sqrt (2 * (4 : ℝ) ^ k) ≤ 2 * (2 : ℝ) ^ k := by
    have h42 : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
      rw [← mul_pow, show (2 : ℝ) * 2 = 4 by norm_num]
    calc Real.sqrt (2 * (4 : ℝ) ^ k) ≤ Real.sqrt (4 * (4 : ℝ) ^ k) :=
          Real.sqrt_le_sqrt (by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 4) k])
      _ = Real.sqrt ((2 * (2 : ℝ) ^ k) ^ 2) := by rw [h42]; ring_nf
      _ = 2 * (2 : ℝ) ^ k := Real.sqrt_sq (by positivity)
  have hp_rpow_le : (p : ℝ) ^ (θ - 1 / 2) ≤ (2 : ℝ) ^ θ * (4 : ℝ) ^ ((θ - 1 / 2) * k) := by
    have hp_le : (p : ℝ) ≤ 2 * (4 : ℝ) ^ k := by exact_mod_cast hp2
    calc (p : ℝ) ^ (θ - 1 / 2) ≤ (2 * (4 : ℝ) ^ k) ^ (θ - 1 / 2) :=
          Real.rpow_le_rpow (Nat.cast_nonneg p) hp_le (by linarith)
      _ = (2 : ℝ) ^ (θ - 1 / 2) * ((4 : ℝ) ^ k) ^ (θ - 1 / 2) :=
          Real.mul_rpow zero_le_two (by positivity)
      _ ≤ (2 : ℝ) ^ θ * ((4 : ℝ) ^ k) ^ (θ - 1 / 2) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith))
            (by positivity)
      _ = (2 : ℝ) ^ θ * (4 : ℝ) ^ ((θ - 1 / 2) * k) := by
          rw [← Real.rpow_natCast (4 : ℝ) k, ← Real.rpow_mul (by norm_num), mul_comm]
  have h4_ratio : (4 : ℝ) ^ (θ * k) / (2 : ℝ) ^ k = (4 : ℝ) ^ ((θ - 1 / 2) * k) := by
    have h2k : (2 : ℝ) ^ k = (4 : ℝ) ^ ((1 / 2 : ℝ) * k) := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ (2 : ℝ) by norm_num, ← Real.rpow_mul zero_le_two,
        show (2 : ℝ) * (1 / 2 * k) = (k : ℝ) by ring, Real.rpow_natCast]
    rw [h2k, ← Real.rpow_sub (by norm_num)]
    congr 1; ring
  calc c₀ * (p : ℝ) ^ (θ - 1 / 2)
      ≤ c₀ * ((2 : ℝ) ^ θ * (4 : ℝ) ^ ((θ - 1 / 2) * k)) :=
        mul_le_mul_of_nonneg_left hp_rpow_le hc₀.le
    _ = Real.log 2 * (splineAutoCorr 0 / 2) *
          ((4 : ℝ) ^ (θ * k) / (2 * M)) / (2 * (2 : ℝ) ^ k) := by
        rw [← h4_ratio]; dsimp only [c₀]; field_simp
    _ ≤ Real.log 2 * (splineAutoCorr 0 / 2) * (S.card : ℝ) / Real.sqrt (2 * (4 : ℝ) ^ k) := by
        have hnum : Real.log 2 * (splineAutoCorr 0 / 2) * ((4 : ℝ) ^ (θ * k) / (2 * M)) ≤
            Real.log 2 * (splineAutoCorr 0 / 2) * (S.card : ℝ) :=
          mul_le_mul_of_nonneg_left hS_ge (by positivity)
        exact div_le_div₀ (by positivity) hnum
          (Real.sqrt_pos.mpr (by positivity)) hsqrt_ub
    _ = ∑ _q ∈ S, Real.log 2 / Real.sqrt (2 * (4 : ℝ) ^ k) * (splineAutoCorr 0 / 2) := by
        rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ q ∈ S, flipVM θ q / Real.sqrt q * splineAutoCorr (Real.log q - Real.log p) :=
        sum_le_sum hterm_ge
    _ ≤ primeWindowOf (flipVM θ) p := hlow

/-- **`ζ` and `doubledVM θ` cannot both satisfy a prime-window bound below `θ − 1/2`.** -/
theorem not_both_primeWindowOf_power_bound {θ a : ℝ} (hθ : 1 / 2 < θ) (hθ1 : θ < 1)
    (ha : a < θ - 1 / 2) {K₀ K₁ : ℝ}
    (h0 : ∀ p : ℕ, p.Prime → |archPoleWindow p - primeWindow p| ≤ K₀ * (p : ℝ) ^ a) :
    ¬ ∀ p : ℕ, p.Prime → |archPoleWindow p - primeWindowOf (doubledVM θ) p| ≤ K₁ * (p : ℝ) ^ a := by
  intro h1
  obtain ⟨c₀, hc₀, hev⟩ := eventually_exists_primeWindowOf_doubledVM_sub_ge hθ hθ1
  set D := |K₀| + |K₁| + 1
  have hD_pos : 0 < D := by positivity
  have hgrow := (tendsto_pow_atTop_atTop_of_one_lt
    (Real.one_lt_rpow (by norm_num : (1 : ℝ) < 4) (sub_pos.mpr ha))).eventually_gt_atTop (D / c₀)
  obtain ⟨k, ⟨p, hp_blk, hp_low⟩, hk_big⟩ := (hev.and hgrow).exists
  obtain ⟨hp_prime, h4p, _⟩ := mem_flipBlock hp_blk
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp_prime.one_lt.le
  have hdiff_le : primeWindowOf (doubledVM θ) p - primeWindow p ≤ (|K₀| + |K₁|) * (p : ℝ) ^ a := by
    have hb0 := (h0 p hp_prime).trans
      (mul_le_mul_of_nonneg_right (le_abs_self K₀) (by positivity))
    have hb1 := (h1 p hp_prime).trans
      (mul_le_mul_of_nonneg_right (le_abs_self K₁) (by positivity))
    have htri : |primeWindowOf (doubledVM θ) p - primeWindow p| ≤
        |archPoleWindow p - primeWindow p| + |archPoleWindow p - primeWindowOf (doubledVM θ) p| := by
      calc |primeWindowOf (doubledVM θ) p - primeWindow p|
          = |(archPoleWindow p - primeWindow p) -
              (archPoleWindow p - primeWindowOf (doubledVM θ) p)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    linarith [le_abs_self (primeWindowOf (doubledVM θ) p - primeWindow p)]
  have hgap : (4 : ℝ) ^ ((θ - 1 / 2 - a) * k) ≤ (p : ℝ) ^ (θ - 1 / 2 - a) := by
    calc (4 : ℝ) ^ ((θ - 1 / 2 - a) * k)
        = ((4 : ℝ) ^ k) ^ (θ - 1 / 2 - a) := by
          rw [mul_comm, Real.rpow_mul (by norm_num), Real.rpow_natCast]
      _ ≤ (p : ℝ) ^ (θ - 1 / 2 - a) :=
          Real.rpow_le_rpow (by positivity) (by exact_mod_cast h4p.le) (by linarith)
  have hgt_D : D / c₀ < (p : ℝ) ^ (θ - 1 / 2 - a) := by
    rw [← Real.rpow_natCast ((4 : ℝ) ^ (θ - 1 / 2 - a)) k, ← Real.rpow_mul (by norm_num)] at hk_big
    exact hk_big.trans_le hgap
  have hp0 : (0 : ℝ) < p := by linarith
  have hmul : D * (p : ℝ) ^ a < c₀ * (p : ℝ) ^ (θ - 1 / 2) := by
    have h1 := (div_lt_iff₀ hc₀).mp hgt_D
    have h2 := mul_lt_mul_of_pos_right h1 (Real.rpow_pos_of_pos hp0 a)
    rw [mul_assoc, ← Real.rpow_add hp0, sub_add_cancel] at h2
    linarith
  have hD_strict : (|K₀| + |K₁|) * (p : ℝ) ^ a < D * (p : ℝ) ^ a :=
    mul_lt_mul_of_pos_right (by dsimp only [D]; linarith) (Real.rpow_pos_of_pos hp0 a)
  linarith

/-- **One-way product-positivity coupling.** Let `(g, lamVar)` be any variable arithmetic cofactor
positively coupled to `ζ` (`(ζ * g)(n) ≥ 0` and `Λ(n) + lamVar(n) ≥ 0`). For every nontrivial
exponent `a < 1/2`, there exists a simple-pole Euler weight `(dBase, wBase)` (either `(1, Λ)` or
`(flipSmoothAF θ, doubledVM θ)`) that:
1. differs from `Λ` by a series summable at `σ = 1` (same simple pole of residue `1` at `s = 1`),
2. preserves nonnegativity of all product Dirichlet and von Mangoldt coefficients with `(g, lamVar)`,
3. violates the prime-window bound `|archPoleWindow p − primeWindowOf wBase p| ≤ K · p^a`.
Consequently, no inequality derived from variable-family moments and product-positivity couplings
bounds `|c_B(log p)| = |archPoleWindow p − primeWindow p|` below `O(p^{1/2})`. -/
theorem no_reverse_weight_bound_from_product_positivity
    {g : ArithmeticFunction ℝ}
    (hpos : ∀ n : ℕ, 0 ≤ ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * g) n)
    {lamVar : ℕ → ℝ} (hlam : ∀ n : ℕ, 0 ≤ (Λ n : ℝ) + lamVar n)
    {a : ℝ} (ha : a < 1 / 2) :
    ∃ (dBase : ArithmeticFunction ℝ) (wBase : ℕ → ℝ),
      dBase.IsMultiplicative ∧
      Summable (fun n : ℕ => (wBase n - (Λ n : ℝ)) * (n : ℝ) ^ (-1 : ℝ)) ∧
      (∀ n : ℕ, 0 ≤ (dBase * ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * g)) n) ∧
      (∀ n : ℕ, 0 ≤ wBase n + lamVar n) ∧
      ¬ ∃ K : ℝ, ∀ p : ℕ, p.Prime → |archPoleWindow p - primeWindowOf wBase p| ≤ K * (p : ℝ) ^ a := by
  by_cases h0 : ∃ K₀ : ℝ, ∀ p : ℕ, p.Prime →
      |archPoleWindow p - primeWindow p| ≤ K₀ * (p : ℝ) ^ a
  · obtain ⟨K₀, hK₀⟩ := h0
    set θ : ℝ := 1 / 2 + (max a 0 + 1 / 2) / 2
    have hθ_lo : 1 / 2 < θ := by
      have := le_max_right a 0
      dsimp only [θ]; linarith
    have hθ_hi : θ < 1 := by
      have := max_lt ha (by norm_num : (0 : ℝ) < 1 / 2)
      dsimp only [θ]; linarith
    have ha_lt : a < θ - 1 / 2 := by
      have := le_max_left a 0
      dsimp only [θ]; linarith
    refine ⟨flipSmoothAF θ, doubledVM θ, isMultiplicative_flipSmoothAF θ, ?_,
      fun n => (flipSmooth_mul_nonneg θ hpos hlam n).1,
      fun n => (flipSmooth_mul_nonneg θ hpos hlam n).2, ?_⟩
    · refine (summable_flipVM_rpow (by linarith) hθ_hi).congr fun n => ?_
      unfold doubledVM
      ring
    · rintro ⟨K₁, hK₁⟩
      exact not_both_primeWindowOf_power_bound hθ_lo hθ_hi ha_lt hK₀ hK₁
  · refine ⟨1, fun n => (Λ n : ℝ), ArithmeticFunction.isMultiplicative_one, ?_,
      fun n => by rw [one_mul]; exact hpos n, hlam, ?_⟩
    · simp only [sub_self, zero_mul, summable_zero]
    · simpa only [primeWindowOf_vonMangoldt] using h0

end GaloisForLFunctions.ArithmeticWeightTheory
