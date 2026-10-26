import GaloisForLFunctions.ArithmeticPositiveDuality.TheIntegerSuccessorForcesTheHeckeWeight
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The critical line is the positivity threshold of the integer successor

The power weights `u ↦ (nd)^{−s}` on `ℚ^×` (`u = ±n/d` in lowest terms) are positive definite for
every `s ≥ 0`: dilations alone admit all of them. Couple them with the integer successor, i.e.
consider the **Hecke states** `φ_s(x ↦ ax + b) = (nd)^{−s}·1[db ∈ ℤ]` on `Aff(ℚ)`:

* `φ_s` is positive definite **iff `s ≥ 1/2`** (`isPosDefOnGroup_heckeState_iff`). Below `1/2` the
  Hecke–Bessel law `nd·|φ(ux)|² ≤ 1` fails at `u = 2`; from `1/2` on, `φ_s` is the adelic Haar
  state times the slope weight `(nd)^{−(s − 1/2)}`.
* The slope weights `(nd)^{−t}`, `t ≥ 0`, are multipliers of positive definiteness on `Aff(ℚ)`
  (`IsPosDefOnGroup.mul_slopeWeight`): over a common denominator `a_i = A_i/D` the weight of
  `g_i⁻¹g_j` is `|A_iA_j|^{−t}·gcd(A_i,A_j)^{2t}`, and `gcd^{2t} = Σ_{d∣L} J_{2t}(d)·1[d∣A_i]1[d∣A_j]`
  with the Jordan totient `J_α = μ ⋆ n^α ≥ 0` (`gcd_rpow_eq_sum`, `jordan_nonneg`).

So the integer successor costs exactly half a unit of exponent: the critical line `Re s = 1/2` is
where positivity of the successor–dilation coupling begins.
-/

open Complex Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-! ### The Jordan totient -/

/-- `n ↦ n^α` as an arithmetic function. -/
noncomputable def powFun (α : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (n : ℝ) ^ α, by simp⟩

theorem powFun_apply {α : ℝ} {n : ℕ} (hn : n ≠ 0) : powFun α n = (n : ℝ) ^ α := by
  simp [powFun, hn]

theorem isMultiplicative_powFun (α : ℝ) : (powFun α).IsMultiplicative := by
  refine ⟨by simp [powFun], fun {m n} _ => ?_⟩
  by_cases hm : m = 0
  · simp [powFun, hm]
  by_cases hn : n = 0
  · simp [powFun, hn]
  rw [powFun_apply hm, powFun_apply hn, powFun_apply (mul_ne_zero hm hn), Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]

/-- The **Jordan totient** `J_α = μ ⋆ (n ↦ n^α)`. -/
noncomputable def jordan (α : ℝ) : ArithmeticFunction ℝ := (μ : ArithmeticFunction ℝ) * powFun α

/-- `Σ_{d ∣ n} J_α(d) = n^α`. -/
theorem sum_divisors_jordan (α : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, jordan α d = (n : ℝ) ^ α := by
  have h : jordan α * (ζ : ArithmeticFunction ℝ) = powFun α := by
    rw [jordan, mul_comm (μ : ArithmeticFunction ℝ), mul_assoc, coe_moebius_mul_coe_zeta,
      mul_one]
  have := congrArg (fun f : ArithmeticFunction ℝ => f n) h
  simp only [coe_mul_zeta_apply] at this
  rw [this, powFun_apply hn]

theorem isMultiplicative_jordan (α : ℝ) : (jordan α).IsMultiplicative :=
  isMultiplicative_moebius.intCast.mul (isMultiplicative_powFun α)

theorem jordan_prime_pow (α : ℝ) {p : ℕ} (hp : p.Prime) (j : ℕ) :
    jordan α (p ^ (j + 1)) = ((p ^ (j + 1) : ℕ) : ℝ) ^ α - ((p ^ j : ℕ) : ℝ) ^ α := by
  have h1 := sum_divisors_jordan α (pow_ne_zero (j + 1) hp.ne_zero)
  have h2 := sum_divisors_jordan α (pow_ne_zero j hp.ne_zero)
  rw [Nat.sum_divisors_prime_pow hp] at h1 h2
  rw [Finset.sum_range_succ, h2] at h1
  linarith

/-- The Jordan totient is nonnegative for `α ≥ 0`: it is multiplicative with
`J_α(p^{j+1}) = p^{(j+1)α} − p^{jα}`. -/
theorem jordan_nonneg {α : ℝ} (hα : 0 ≤ α) (n : ℕ) : 0 ≤ jordan α n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [(isMultiplicative_jordan α).multiplicative_factorization _ hn.ne', Finsupp.prod]
  refine Finset.prod_nonneg fun p hp => ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp)
  have hk : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
  obtain ⟨j, hj⟩ : ∃ j, n.factorization p = j + 1 := ⟨n.factorization p - 1, by omega⟩
  rw [hj, jordan_prime_pow α hpp j, sub_nonneg]
  exact Real.rpow_le_rpow (Nat.cast_nonneg _)
    (Nat.cast_le.mpr (Nat.pow_le_pow_right hpp.pos (Nat.le_succ j))) hα

/-- **GCD powers as a sum of squares.** For `a ∣ L`,
`gcd(a,b)^α = Σ_{d ∣ L} J_α(d)·1[d∣a]·1[d∣b]`. -/
theorem gcd_rpow_eq_sum (α : ℝ) {a b L : ℕ} (ha : a ∣ L) (hL : L ≠ 0)
    (hab : Nat.gcd a b ≠ 0) :
    ((Nat.gcd a b : ℕ) : ℝ) ^ α =
      ∑ d ∈ L.divisors, jordan α d * ((if d ∣ a then 1 else 0) * (if d ∣ b then 1 else 0)) := by
  rw [← sum_divisors_jordan α hab]
  have hsub : (Nat.gcd a b).divisors ⊆ L.divisors :=
    Nat.divisors_subset_of_dvd hL ((Nat.gcd_dvd_left a b).trans ha)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun d hd => ?_
    have hd' : d ∣ Nat.gcd a b := Nat.dvd_of_mem_divisors hd
    rw [if_pos (hd'.trans (Nat.gcd_dvd_left a b)), if_pos (hd'.trans (Nat.gcd_dvd_right a b)),
      mul_one, mul_one]
  · intro d _ hd
    have : ¬ (d ∣ a ∧ d ∣ b) := fun h => hd (Nat.mem_divisors.mpr ⟨Nat.dvd_gcd h.1 h.2, hab⟩)
    by_cases h1 : d ∣ a
    · rw [if_pos h1, if_neg fun h2 => this ⟨h1, h2⟩, mul_zero, mul_zero]
    · rw [if_neg h1, zero_mul, mul_zero]
/-! ### Integer coordinates of a finite family -/

/-- A finite family of affine maps has integer coordinates over a common denominator:
`g_i = (x ↦ (A_i x + C_i)/D)` with `A_i ≠ 0`. -/
theorem exists_int_coords {N : ℕ} (x : Fin N → AffineGroupQ) :
    ∃ D : ℕ, 0 < D ∧ ∃ A C : Fin N → ℤ, (∀ i, A i ≠ 0) ∧
      (∀ i, affSlope (x i) = A i / D) ∧ ∀ i, affShift (x i) = C i / D := by
  classical
  set D : ℕ := ∏ i, ((affSlope (x i)).den * (affShift (x i)).den) with hD_def
  have hD : 0 < D := Finset.prod_pos fun i _ => Nat.mul_pos (Rat.den_pos _) (Rat.den_pos _)
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hint : ∀ q : ℚ, q.den ∣ D → ∃ z : ℤ, (z : ℚ) = D * q := by
    rintro q ⟨t, ht⟩
    refine ⟨t * q.num, ?_⟩
    rw [ht]; push_cast
    rw [mul_comm (q.den : ℚ) t, mul_assoc, Rat.den_mul_eq_num]
  have hdvd_a : ∀ i, (affSlope (x i)).den ∣ D := fun i =>
    (Nat.dvd_mul_right _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  have hdvd_b : ∀ i, (affShift (x i)).den ∣ D := fun i =>
    (Nat.dvd_mul_left _ _).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  choose A hA using fun i => hint _ (hdvd_a i)
  choose C hC using fun i => hint _ (hdvd_b i)
  refine ⟨D, hD, A, C, fun i h => ?_, fun i => ?_, fun i => ?_⟩
  · have e := hA i
    rw [h, Int.cast_zero] at e
    rcases mul_eq_zero.mp e.symm with h' | h'
    · exact hDq h'
    · exact affSlope_ne_zero (x i) h'
  · rw [hA i]; field_simp
  · rw [hC i]; field_simp

theorem affSlope_inv_mul_of_int {g h : AffineGroupQ} {D : ℕ} (hD : 0 < D) {A A' : ℤ} (hA : A ≠ 0)
    (hg : affSlope g = A / D) (hh : affSlope h = A' / D) :
    affSlope (g⁻¹ * h) = (A' : ℚ) / A := by
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hAq : (A : ℚ) ≠ 0 := by exact_mod_cast hA
  rw [affSlope_mul, affSlope_inv, hg, hh]
  field_simp

/-! ### Slope weights are multipliers of positive definiteness -/

/-- The **slope weight** `(nd)^{−t}` of `x ↦ ax + b`, `a = ±n/d` in lowest terms. -/
def slopeWeight (t : ℝ) (g : AffineGroupQ) : ℝ :=
  (((affSlope g).num.natAbs : ℝ) * (affSlope g).den) ^ (-t)

/-- In integer coordinates `a = A'/A` the slope weight is `|AA'|^{−t}·gcd(A,A')^{2t}`. -/
theorem slopeWeight_of_int (t : ℝ) {g : AffineGroupQ} {A A' : ℤ} (hA : A ≠ 0) (hA' : A' ≠ 0)
    (hsl : affSlope g = (A' : ℚ) / A) :
    slopeWeight t g = (A.natAbs : ℝ) ^ (-t) * (A'.natAbs : ℝ) ^ (-t) *
      ((Nat.gcd A.natAbs A'.natAbs : ℕ) : ℝ) ^ (2 * t) := by
  unfold slopeWeight
  rw [hsl]
  obtain ⟨hden, hnum⟩ := lowest_terms_div (A' := A') hA
  rw [hden, hnum]
  set k := A.gcd A' with hk_def
  have hkpos : 0 < k := Int.gcd_pos_of_ne_zero_left A' hA
  have hk' : Nat.gcd A.natAbs A'.natAbs = k := rfl
  rw [hk']
  have h1 : k ∣ A.natAbs := Nat.gcd_dvd_left A.natAbs A'.natAbs
  have h2 : k ∣ A'.natAbs := Nat.gcd_dvd_right A.natAbs A'.natAbs
  rw [Nat.cast_div h2 (by exact_mod_cast hkpos.ne'), Nat.cast_div h1 (by exact_mod_cast hkpos.ne')]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hA0 : (0 : ℝ) < A.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hA
  have hA0' : (0 : ℝ) < A'.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hA'
  rw [show (A'.natAbs : ℝ) / k * ((A.natAbs : ℝ) / k) =
      (A.natAbs : ℝ) * A'.natAbs * ((k : ℝ) ^ (2 : ℝ))⁻¹ by
    rw [Real.rpow_two]; field_simp]
  rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
    Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity), ← Real.rpow_mul hkR.le]
  ring_nf

/-- **Slope weights multiply positive definiteness.** If `φ` is positive definite on `Aff(ℚ)` and
`t ≥ 0`, then `g ↦ φ(g)·(nd)^{−t}` is positive definite: over a common denominator the slope weight
is `Σ_{d∣L} J_{2t}(d)·e_d(i)e_d(j)` with `e_d(i) = |A_i|^{−t}1[d∣A_i]`, and `J_{2t} ≥ 0`. -/
theorem IsPosDefOnGroup.mul_slopeWeight {φ : AffineGroupQ → ℂ} (hφ : IsPosDefOnGroup φ) {t : ℝ}
    (ht : 0 ≤ t) : IsPosDefOnGroup fun g => φ g * (slopeWeight t g : ℂ) := by
  intro N x c
  classical
  obtain ⟨D, hD, A, C, hA0, hsl, -⟩ := exists_int_coords x
  set L : ℕ := ∏ i, (A i).natAbs with hL_def
  have hL : L ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => Int.natAbs_ne_zero.mpr (hA0 i)
  have hdvd : ∀ i, (A i).natAbs ∣ L := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  set e : ℕ → Fin N → ℝ := fun d i => ((A i).natAbs : ℝ) ^ (-t) * if d ∣ (A i).natAbs then 1 else 0
    with he_def
  have hw : ∀ i j, slopeWeight t ((x i)⁻¹ * x j) =
      ∑ d ∈ L.divisors, jordan (2 * t) d * (e d i * e d j) := by
    intro i j
    rw [slopeWeight_of_int t (hA0 i) (hA0 j) (affSlope_inv_mul_of_int hD (hA0 i) (hsl i) (hsl j)),
      gcd_rpow_eq_sum (2 * t) (hdvd i) hL
        (Nat.gcd_pos_of_pos_left _ (Int.natAbs_pos.mpr (hA0 i))).ne', Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [he_def]
    ring
  -- each divisor contributes a Gram form of `φ`
  have hd : ∀ d, ∃ r : ℝ, 0 ≤ r ∧
      ∑ i, ∑ j, star (c i * (e d i : ℂ)) * φ ((x i)⁻¹ * x j) * (c j * (e d j : ℂ)) = r :=
    fun d => hφ N x fun i => c i * (e d i : ℂ)
  choose r hr0 hr using hd
  refine ⟨∑ d ∈ L.divisors, jordan (2 * t) d * r d,
    Finset.sum_nonneg fun d _ => mul_nonneg (jordan_nonneg (by linarith) d) (hr0 d), ?_⟩
  have hstar : ∀ d i, star (c i * (e d i : ℂ)) = star (c i) * (e d i : ℂ) := fun d i => by
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, mul_comm]
  calc ∑ i, ∑ j, star (c i) * (φ ((x i)⁻¹ * x j) * (slopeWeight t ((x i)⁻¹ * x j) : ℂ)) * c j
      = ∑ i, ∑ j, ∑ d ∈ L.divisors, (jordan (2 * t) d : ℂ) *
          (star (c i * (e d i : ℂ)) * φ ((x i)⁻¹ * x j) * (c j * (e d j : ℂ))) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hw i j]
        push_cast
        rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [hstar]
        ring
    _ = ∑ i, ∑ d ∈ L.divisors, ∑ j, (jordan (2 * t) d : ℂ) *
          (star (c i * (e d i : ℂ)) * φ ((x i)⁻¹ * x j) * (c j * (e d j : ℂ))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ d ∈ L.divisors, ∑ i, ∑ j, (jordan (2 * t) d : ℂ) *
          (star (c i * (e d i : ℂ)) * φ ((x i)⁻¹ * x j) * (c j * (e d j : ℂ))) :=
        Finset.sum_comm
    _ = ((∑ d ∈ L.divisors, jordan (2 * t) d * r d : ℝ) : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← hr d, Finset.mul_sum]
        simp_rw [Finset.mul_sum]

/-! ### Hecke states and the threshold -/

/-- The **Hecke state** of exponent `s`: `φ_s(x ↦ ax + b) = (nd)^{−s}·1[db ∈ ℤ]`, `a = ±n/d`. -/
def heckeState (s : ℝ) (g : AffineGroupQ) : ℂ :=
  if (((affSlope g).den : ℚ) * affShift g).den = 1 then
    ((((affSlope g).num.natAbs : ℝ) * (affSlope g).den) ^ (-s) : ℝ) else 0

/-- From `s = 1/2` on, the Hecke state is the Haar state times a slope weight. -/
theorem heckeState_eq_mul {s : ℝ} (g : AffineGroupQ) :
    heckeState s g = haarState g * (slopeWeight (s - 1 / 2) g : ℂ) := by
  unfold heckeState haarState haarWeight slopeWeight
  split_ifs
  · have hpos : (0 : ℝ) < ((affSlope g).num.natAbs : ℝ) * (affSlope g).den := by
      have h1 : 0 < (affSlope g).num.natAbs :=
        Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr (affSlope_ne_zero g))
      have h2 : 0 < (affSlope g).den := Rat.den_pos _
      positivity
    rw [← Complex.ofReal_mul]
    congr 1
    rw [Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hpos.le, ← Real.rpow_add hpos]
    ring_nf
  · simp

theorem heckeState_hasIntegerSuccessor (s : ℝ) : HasIntegerSuccessor (heckeState s) := by
  intro b
  simp only [heckeState, affSlope_translation, affShift_translation, Rat.num_one, Rat.den_one,
    Int.natAbs_one, Nat.cast_one, one_mul, Real.one_rpow]
  split_ifs <;> simp

theorem heckeState_dilation (s : ℝ) (u : ℚˣ) :
    heckeState s (dilation u) = ((((u : ℚ).num.natAbs : ℝ) * (u : ℚ).den) ^ (-s) : ℝ) := by
  simp only [heckeState, affSlope_dilation, affShift_dilation, mul_zero, Rat.den_zero, ite_true]

/-- **The critical line is the positivity threshold of the integer successor.** The Hecke state
`(nd)^{−s}·1[db ∈ ℤ]` is positive definite on `Aff(ℚ)` iff `s ≥ 1/2`. -/
theorem isPosDefOnGroup_heckeState_iff (s : ℝ) : IsPosDefOnGroup (heckeState s) ↔ 1 / 2 ≤ s := by
  constructor
  · intro h
    have hb := normSq_dilation_le h (heckeState_hasIntegerSuccessor s) (Units.mk0 (2 : ℚ) two_ne_zero)
    have h2 : ((((Units.mk0 (2 : ℚ) two_ne_zero : ℚˣ) : ℚ).num.natAbs : ℕ) : ℝ) *
        ((((Units.mk0 (2 : ℚ) two_ne_zero : ℚˣ) : ℚ).den : ℕ) : ℝ) = 2 := by
      simp [Units.val_mk0]
    rw [heckeState_dilation, Complex.normSq_ofReal, h2] at hb
    by_contra hlt
    have hlt := not_le.mp hlt
    have : (1 : ℝ) < 2 * ((2 : ℝ) ^ (-s) * (2 : ℝ) ^ (-s)) := by
      rw [← Real.rpow_add (by norm_num), show -s + -s = -(2 * s) by ring]
      have h1 : (2 : ℝ) ^ (-(2 * s)) > (2 : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      rw [Real.rpow_neg_one] at h1
      linarith
    linarith
  · intro hs
    have hmul := isPosDefOnGroup_haarState.mul_slopeWeight (t := s - 1 / 2) (by linarith)
    have e : heckeState s = fun g => haarState g * (slopeWeight (s - 1 / 2) g : ℂ) :=
      funext heckeState_eq_mul
    rw [e]
    exact hmul

/-- Without the successor every power weight is admissible: `u ↦ (nd)^{−s}` is positive definite
on `ℚ^×` for all `s ≥ 0`. -/
theorem isPosDefOnGroup_dilation_powerWeight {s : ℝ} (hs : 0 ≤ s) :
    IsPosDefOnGroup fun u : ℚˣ => (((((u : ℚ).num.natAbs : ℝ) * (u : ℚ).den) ^ (-s) : ℝ) : ℂ) := by
  have hone : IsPosDefOnGroup (fun _ : AffineGroupQ => (1 : ℂ)) := by
    intro N x c
    refine ⟨Complex.normSq (∑ i, c i), Complex.normSq_nonneg _, ?_⟩
    rw [Complex.normSq_eq_conj_mul_self, ← Complex.star_def, star_sum, Finset.sum_mul_sum]
    simp only [mul_one]
  have h := (hone.mul_slopeWeight hs).comp_hom dilation
  have e : (fun u : ℚˣ => (((((u : ℚ).num.natAbs : ℝ) * (u : ℚ).den) ^ (-s) : ℝ) : ℂ)) =
      (fun g => (1 : ℂ) * (slopeWeight s g : ℂ)) ∘ dilation := by
    funext u
    simp only [Function.comp_apply, one_mul, slopeWeight, affSlope_dilation]
  rw [e]
  exact h

end GaloisForLFunctions.ArithmeticPositiveDuality
