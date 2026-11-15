import Mathlib.NumberTheory.Padics.Complex
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Prime.Factorial

/-!
# The Gauss sums of a prime field carry Stickelberger's valuation

Let `K = PadicAlgCl p` be an algebraic closure of `ℚ_p` with its `p`-adic norm, `ζ ∈ K` a primitive
`p`-th root of unity, `ψ(x) = ζ^x`, `π = ζ − 1`, and `ω : 𝔽_p → K` the Teichmüller character
(`ω(x)^{p−1} = 1`, `ω(x) ≡ x`). For `1 ≤ n ≤ p − 1` and `a = p − 1 − n` (so `ω^n = ω^{−a}`),

`g(ω^n) = Σ_{k<p} c_k π^k` with `c_k = Σ_x ω(x)^n C(x, k) ∈ ℤ_p`, `c_k ≡ 0` for `k < a` and
`a! c_a ≡ −1 (mod p)` (Stickelberger's congruence). Since `‖π‖^{p−1} = 1/p`, the term `c_a π^a`
dominates and `‖g(ω^n)‖ = ‖π‖^a`: the Gauss sum of `ω^{−a}` has valuation `a/(p − 1)`
(`norm_gaussSum_teichCharK_pow`). Every `K`-valued character of `𝔽_p` is a power of `ω`
(`exists_eq_teichCharK_pow`), so this is the valuation of every Gauss sum of the prime field.

* **Teichmüller lift** (`teich`, `teichChar`): Hensel's lemma for `X^{p−1} − 1` at a unit residue;
  multiplicativity by uniqueness.
* **The uniformizer** (`norm_sub_one_pow`): `Π_{μ primitive} (1 − μ) = Φ_p(1) = p` and
  `‖1 − μ‖ = ‖1 − ζ‖` for every primitive `μ`, so `‖ζ − 1‖^{p−1} = 1/p`.
* **The congruence** (`toZMod_stickCoeff_eq_zero`, `factorial_mul_toZMod_stickCoeff`):
  `k! C(x, k) = (x)_k` is a monic polynomial of degree `k` in `x`, and `Σ_{x ∈ 𝔽_p} x^e` vanishes
  for `e < p − 1` and equals `−1` at `e = p − 1`.
-/

open Polynomial Finset
open scoped Nat

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.Stickelberger

variable (p : ℕ) [hp : Fact p.Prime]

theorem neZero_p : NeZero p := ⟨hp.out.ne_zero⟩

attribute [local instance] neZero_p

/-! ### 1. Residues in `ℤ_p` and the Teichmüller lift -/

/-- The open unit ball of `ℤ_p` is the kernel of the reduction. -/
theorem norm_lt_one_iff_toZMod_eq_zero (z : ℤ_[p]) : ‖z‖ < 1 ↔ PadicInt.toZMod z = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

theorem norm_le_inv_of_toZMod_eq_zero {z : ℤ_[p]} (h : PadicInt.toZMod z = 0) :
    ‖z‖ ≤ (p : ℝ)⁻¹ := by
  obtain ⟨w, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd z).1 ((norm_lt_one_iff_toZMod_eq_zero p z).2 h)
  rw [norm_mul, PadicInt.norm_p]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one w)

theorem norm_eq_one_of_toZMod_ne_zero {z : ℤ_[p]} (h : PadicInt.toZMod z ≠ 0) : ‖z‖ = 1 :=
  le_antisymm (PadicInt.norm_le_one z)
    (not_lt.1 fun h' => h ((norm_lt_one_iff_toZMod_eq_zero p z).1 h'))

/-- **Hensel at a unit residue.** Above a unit residue lies exactly one `(p − 1)`-th root of
unity of `ℤ_p`. -/
theorem existsUnique_teich {x : ZMod p} (hx : x ≠ 0) :
    ∃! z : ℤ_[p], z ^ (p - 1) = 1 ∧ PadicInt.toZMod z = x := by
  have hp2 := hp.out.two_le
  set a : ℤ_[p] := (x.val : ℤ_[p]) with ha_def
  have hax : PadicInt.toZMod a = x := by rw [ha_def, map_natCast, ZMod.natCast_zmod_val]
  have ha1 : ‖a‖ = 1 := norm_eq_one_of_toZMod_ne_zero p (by rwa [hax])
  set F : ℤ_[p][X] := X ^ (p - 1) - 1 with hF
  have hev : ∀ z : ℤ_[p], F.aeval z = z ^ (p - 1) - 1 := fun z => by
    rw [hF, map_sub, map_pow, aeval_X, map_one]
  have hder : ‖F.derivative.aeval a‖ = 1 := by
    have e : F.derivative.aeval a = ((p - 1 : ℕ) : ℤ_[p]) * a ^ (p - 1 - 1) := by
      rw [hF, derivative_sub, derivative_X_pow, derivative_one, sub_zero, map_mul, aeval_C,
        Algebra.algebraMap_self_apply, map_pow, aeval_X]
    rw [e, norm_mul, norm_pow, ha1, one_pow, mul_one, PadicInt.norm_natCast_eq_one_iff,
      hp.out.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have hnorm : ‖F.aeval a‖ < ‖F.derivative.aeval a‖ ^ 2 := by
    rw [hder, one_pow, hev, norm_lt_one_iff_toZMod_eq_zero, map_sub, map_pow, hax, map_one,
      ZMod.pow_card_sub_one_eq_one hx, sub_self]
  obtain ⟨z, hz, hza, -, huniq⟩ := hensels_lemma hnorm
  rw [hder] at hza huniq
  refine ⟨z, ⟨?_, ?_⟩, fun w hw => huniq w ?_ ?_⟩
  · rw [hev] at hz
    exact sub_eq_zero.1 hz
  · have h := (norm_lt_one_iff_toZMod_eq_zero p (z - a)).1 hza
    rwa [map_sub, sub_eq_zero, hax] at h
  · rw [hev, hw.1, sub_self]
  · rw [norm_lt_one_iff_toZMod_eq_zero, map_sub, hw.2, hax, sub_self]

open Classical in
/-- The **Teichmüller lift** `𝔽_p → ℤ_p`: `0 ↦ 0`, and a unit residue goes to the
`(p − 1)`-th root of unity above it. -/
noncomputable def teich (x : ZMod p) : ℤ_[p] :=
  if hx : x = 0 then 0 else (existsUnique_teich p hx).exists.choose

theorem teich_zero : teich p 0 = 0 := dif_pos rfl

theorem teich_spec {x : ZMod p} (hx : x ≠ 0) :
    teich p x ^ (p - 1) = 1 ∧ PadicInt.toZMod (teich p x) = x := by
  rw [teich, dif_neg hx]
  exact (existsUnique_teich p hx).exists.choose_spec

theorem teich_eq {x : ZMod p} (hx : x ≠ 0) {z : ℤ_[p]} (hz : z ^ (p - 1) = 1)
    (hzx : PadicInt.toZMod z = x) : teich p x = z :=
  (existsUnique_teich p hx).unique (teich_spec p hx) ⟨hz, hzx⟩

theorem toZMod_teich (x : ZMod p) : PadicInt.toZMod (teich p x) = x := by
  by_cases hx : x = 0
  · rw [hx, teich_zero, map_zero]
  · exact (teich_spec p hx).2

theorem teich_mul (x y : ZMod p) : teich p (x * y) = teich p x * teich p y := by
  by_cases hx : x = 0
  · rw [hx, zero_mul, teich_zero, zero_mul]
  by_cases hy : y = 0
  · rw [hy, mul_zero, teich_zero, mul_zero]
  exact teich_eq p (mul_ne_zero hx hy)
    (by rw [mul_pow, (teich_spec p hx).1, (teich_spec p hy).1, one_mul])
    (by rw [map_mul, toZMod_teich, toZMod_teich])

theorem teich_one : teich p 1 = 1 := teich_eq p one_ne_zero (one_pow _) (map_one _)

/-- The Teichmüller character of `𝔽_p` with values in `ℤ_p`. -/
noncomputable def teichChar : MulChar (ZMod p) ℤ_[p] where
  toFun := teich p
  map_one' := teich_one p
  map_mul' := teich_mul p
  map_nonunit' := fun x hx => by
    have h0 : x = 0 := by
      by_contra h
      exact hx (isUnit_iff_ne_zero.2 h)
    show teich p x = 0
    rw [h0, teich_zero]

/-- The embedding `ℤ_p → K`. -/
noncomputable def toK : ℤ_[p] →+* PadicAlgCl p :=
  (algebraMap ℚ_[p] (PadicAlgCl p)).comp PadicInt.Coe.ringHom

theorem norm_toK (z : ℤ_[p]) : ‖toK p z‖ = ‖z‖ :=
  (PadicAlgCl.norm_extends p (z : ℚ_[p])).trans (PadicInt.padic_norm_e_of_padicInt z)

/-- The Teichmüller character with values in `K`. -/
noncomputable def teichCharK : MulChar (ZMod p) (PadicAlgCl p) := (teichChar p).ringHomComp (toK p)

theorem teichCharK_apply (x : ZMod p) : teichCharK p x = toK p (teich p x) :=
  MulChar.ringHomComp_apply _ _ _

/-! ### 2. The uniformizer `ζ − 1` -/

variable {p}

/-- In `K` a finite sum of terms of norm at most `C ≥ 0` has norm at most `C`. -/
theorem norm_sum_le_of_forall_le {ι : Type*} (s : Finset ι) (f : ι → PadicAlgCl p) {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ i ∈ s, ‖f i‖ ≤ C) : ‖∑ i ∈ s, f i‖ ≤ C :=
  Finset.sum_induction f (fun x => ‖x‖ ≤ C)
    (fun a b ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb))
    (by simpa using hC) h

theorem norm_eq_one_of_isPrimitiveRoot {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) :
    ‖ζ‖ = 1 :=
  (pow_left_inj₀ (norm_nonneg ζ) zero_le_one hp.out.ne_zero).1
    (by rw [one_pow, ← norm_pow, hζ.pow_eq_one, norm_one])

theorem norm_pow_sub_one_le {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) (j : ℕ) :
    ‖ζ ^ j - 1‖ ≤ ‖ζ - 1‖ := by
  rw [← geom_sum_mul, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _)
    (norm_sum_le_of_forall_le _ _ zero_le_one fun i _ => ?_)
  rw [norm_pow, norm_eq_one_of_isPrimitiveRoot hζ, one_pow]

/-- **The uniformizer.** `‖ζ − 1‖^{p−1} = 1/p`. -/
theorem norm_sub_one_pow {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) :
    ‖ζ - 1‖ ^ (p - 1) = (p : ℝ)⁻¹ := by
  have hμ : ∀ μ ∈ primitiveRoots p (PadicAlgCl p), ‖1 - μ‖ = ‖ζ - 1‖ := fun μ hμ' => by
    have hμp : IsPrimitiveRoot μ p := (mem_primitiveRoots hp.out.pos).1 hμ'
    obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμp.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμp.eq_pow_of_pow_eq_one hζ.pow_eq_one
    rw [norm_sub_rev]
    refine le_antisymm ?_ ?_
    · rw [← hi]
      exact norm_pow_sub_one_le hζ i
    · rw [← hj]
      exact norm_pow_sub_one_le hμp j
  have hprod : ∏ μ ∈ primitiveRoots p (PadicAlgCl p), (1 - μ) = (p : PadicAlgCl p) := by
    rw [← eval_one_cyclotomic_prime (R := PadicAlgCl p), cyclotomic_eq_prod_X_sub_primitiveRoots hζ,
      eval_prod]
    simp
  have hnp : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
    rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends, Padic.norm_p]
  rw [← hnp, ← hprod, norm_prod, Finset.prod_congr rfl hμ, Finset.prod_const,
    hζ.card_primitiveRoots, Nat.totient_prime hp.out]

theorem norm_sub_one_pos {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) : 0 < ‖ζ - 1‖ := by
  rcases (norm_nonneg (ζ - 1)).lt_or_eq with h | h
  · exact h
  · have h1 := norm_sub_one_pow hζ
    rw [← h, zero_pow (by have := hp.out.two_le; omega)] at h1
    exact absurd h1.symm (inv_ne_zero (Nat.cast_ne_zero.2 hp.out.ne_zero))

theorem norm_sub_one_lt_one {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) : ‖ζ - 1‖ < 1 := by
  by_contra h
  have h1 := one_le_pow₀ (n := p - 1) (not_lt.1 h)
  rw [norm_sub_one_pow hζ] at h1
  have : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  exact absurd h1 (not_le.2 (inv_lt_one_of_one_lt₀ this))

/-! ### 3. Stickelberger's congruence -/

/-- Binomial expansion of `(π + 1)^v` for `v < p`. -/
theorem add_one_pow_eq_sum (π : PadicAlgCl p) {v : ℕ} (hv : v < p) :
    (π + 1) ^ v = ∑ k ∈ range p, (v.choose k : PadicAlgCl p) * π ^ k := by
  rw [add_pow]
  have e : ∀ k ∈ range (v + 1),
      π ^ k * 1 ^ (v - k) * (v.choose k : PadicAlgCl p) = (v.choose k : PadicAlgCl p) * π ^ k :=
    fun k _ => by rw [one_pow, mul_one, mul_comm]
  rw [Finset.sum_congr rfl e]
  exact Finset.sum_subset (Finset.range_mono (by omega)) fun k _ hk => by
    rw [Finset.mem_range, not_lt] at hk
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]

variable (p)

/-- The coefficients `c_k = Σ_x ω(x)^n C(x, k)` of `g(ω^n)` in powers of `ζ − 1`. -/
noncomputable def stickCoeff (n k : ℕ) : ℤ_[p] :=
  ∑ x : ZMod p, teich p x ^ n * (x.val.choose k : ℤ_[p])

/-- `g(ω^n) = Σ_{k<p} c_k (ζ − 1)^k`. -/
theorem gaussSum_teichCharK_pow {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) {n : ℕ}
    (hn : n ≠ 0) :
    gaussSum (teichCharK p ^ n) (AddChar.zmodChar p hζ.pow_eq_one) =
      ∑ k ∈ range p, toK p (stickCoeff p n k) * (ζ - 1) ^ k := by
  have h1 : ∀ x : ZMod p,
      ζ ^ x.val = ∑ k ∈ range p, (x.val.choose k : PadicAlgCl p) * (ζ - 1) ^ k := fun x => by
    rw [← add_one_pow_eq_sum (ζ - 1) (ZMod.val_lt x), sub_add_cancel]
  simp only [gaussSum, MulChar.pow_apply' _ hn, teichCharK_apply, AddChar.zmodChar_apply, h1,
    stickCoeff, map_sum, map_mul, map_pow, map_natCast, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun x _ => by ring

theorem toZMod_stickCoeff (n k : ℕ) :
    PadicInt.toZMod (stickCoeff p n k) = ∑ x : ZMod p, x ^ n * (x.val.choose k : ZMod p) := by
  simp only [stickCoeff, map_sum, map_mul, map_pow, map_natCast, toZMod_teich]

/-- `k! C(x, k) = (x)_k` expands the residue sum into power sums. -/
theorem factorial_mul_sum_choose (n k : ℕ) :
    (k ! : ZMod p) * ∑ x : ZMod p, x ^ n * (x.val.choose k : ZMod p) =
      ∑ j ∈ range (k + 1), (descPochhammer (ZMod p) k).coeff j * ∑ x : ZMod p, x ^ (n + j) := by
  have h : ∀ x : ZMod p, (k ! : ZMod p) * (x ^ n * (x.val.choose k : ZMod p)) =
      ∑ j ∈ range (k + 1), (descPochhammer (ZMod p) k).coeff j * x ^ (n + j) := fun x => by
    have e : (k ! : ZMod p) * (x.val.choose k : ZMod p) = (descPochhammer (ZMod p) k).eval x := by
      rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose,
        ← descPochhammer_eval_eq_descFactorial, ZMod.natCast_zmod_val]
    rw [mul_left_comm, e, eval_eq_sum_range' (n := k + 1)
      (by rw [descPochhammer_natDegree]; omega), Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun x _ => h x, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm

theorem sum_pow_eq_zero {e : ℕ} (he : e < p - 1) : ∑ x : ZMod p, x ^ e = 0 :=
  FiniteField.sum_pow_lt_card_sub_one (ZMod p) e (by rwa [ZMod.card])

theorem sum_pow_sub_one : ∑ x : ZMod p, x ^ (p - 1) = -1 := by
  have h : ∀ x : ZMod p, x ^ (p - 1) = 1 - if x = 0 then 1 else 0 := fun x => by
    split_ifs with hx
    · rw [hx, zero_pow (by have := hp.out.two_le; omega), sub_self]
    · rw [ZMod.pow_card_sub_one_eq_one hx, sub_zero]
  rw [Finset.sum_congr rfl fun x _ => h x, Finset.sum_sub_distrib]
  simp

theorem factorial_ne_zero {k : ℕ} (hk : k < p) : (k ! : ZMod p) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p, Nat.Prime.dvd_factorial hp.out]
  omega

/-- **The coefficients below the Stickelberger index vanish mod `p`.** -/
theorem toZMod_stickCoeff_eq_zero {n k : ℕ} (h : n + k < p - 1) :
    PadicInt.toZMod (stickCoeff p n k) = 0 := by
  rw [toZMod_stickCoeff]
  refine (mul_eq_zero.1 ?_).resolve_left (factorial_ne_zero p (k := k) (by omega))
  rw [factorial_mul_sum_choose]
  exact Finset.sum_eq_zero fun j hj => by
    rw [Finset.mem_range] at hj
    rw [sum_pow_eq_zero p (by omega), mul_zero]

/-- **Stickelberger's congruence.** At the index `a = p − 1 − n`: `a! c_a ≡ −1 (mod p)`. -/
theorem factorial_mul_toZMod_stickCoeff {n a : ℕ} (h : n + a = p - 1) :
    (a ! : ZMod p) * PadicInt.toZMod (stickCoeff p n a) = -1 := by
  have hc : (descPochhammer (ZMod p) a).coeff a = 1 := by
    have := (monic_descPochhammer (ZMod p) a).coeff_natDegree
    rwa [descPochhammer_natDegree] at this
  rw [toZMod_stickCoeff, factorial_mul_sum_choose, Finset.sum_range_succ, hc, one_mul, h,
    sum_pow_sub_one, Finset.sum_eq_zero, zero_add]
  intro j hj
  rw [Finset.mem_range] at hj
  rw [sum_pow_eq_zero p (by omega), mul_zero]

theorem norm_toK_stickCoeff_le_inv {n k : ℕ} (h : n + k < p - 1) :
    ‖toK p (stickCoeff p n k)‖ ≤ (p : ℝ)⁻¹ := by
  rw [norm_toK]
  exact norm_le_inv_of_toZMod_eq_zero p (toZMod_stickCoeff_eq_zero p h)

theorem norm_toK_stickCoeff_eq_one {n a : ℕ} (h : n + a = p - 1) :
    ‖toK p (stickCoeff p n a)‖ = 1 := by
  rw [norm_toK]
  refine norm_eq_one_of_toZMod_ne_zero p fun h0 => ?_
  have h1 := factorial_mul_toZMod_stickCoeff p h
  rw [h0, mul_zero] at h1
  exact (neg_ne_zero.2 one_ne_zero) h1.symm

/-! ### 4. The valuation -/

/-- **Stickelberger's valuation for the prime field.** For `1 ≤ n ≤ p − 1`,
`‖g(ω^n)‖ = ‖ζ − 1‖^{p−1−n}`: the term `c_a π^a` of norm `‖π‖^a` dominates the others, which
have norm at most `‖π‖^{a+1}`. -/
theorem norm_gaussSum_teichCharK_pow {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) {n : ℕ}
    (hn : n ≠ 0) (hnp : n ≤ p - 1) :
    ‖gaussSum (teichCharK p ^ n) (AddChar.zmodChar p hζ.pow_eq_one)‖ = ‖ζ - 1‖ ^ (p - 1 - n) := by
  set a := p - 1 - n with ha
  have hna : n + a = p - 1 := by omega
  have hap : a < p := by omega
  set r := ‖ζ - 1‖ with hr
  have hr0 : 0 < r := norm_sub_one_pos hζ
  have hr1 : r < 1 := norm_sub_one_lt_one hζ
  have hrp : r ^ (p - 1) = (p : ℝ)⁻¹ := norm_sub_one_pow hζ
  rw [gaussSum_teichCharK_pow p hζ hn, ← Finset.add_sum_erase _ _ (Finset.mem_range.2 hap)]
  have hmain : ‖toK p (stickCoeff p n a) * (ζ - 1) ^ a‖ = r ^ a := by
    rw [norm_mul, norm_pow, norm_toK_stickCoeff_eq_one p hna, one_mul]
  have hrest : ‖∑ k ∈ (range p).erase a, toK p (stickCoeff p n k) * (ζ - 1) ^ k‖ ≤
      r ^ (a + 1) := by
    refine norm_sum_le_of_forall_le _ _ (by positivity) fun k hk => ?_
    rw [Finset.mem_erase, Finset.mem_range] at hk
    rw [norm_mul, norm_pow]
    rcases lt_or_gt_of_ne hk.1 with hka | hka
    · calc ‖toK p (stickCoeff p n k)‖ * r ^ k ≤ (p : ℝ)⁻¹ * 1 :=
            mul_le_mul (norm_toK_stickCoeff_le_inv p (by omega)) (pow_le_one₀ hr0.le hr1.le)
              (by positivity) (by positivity)
        _ = r ^ (p - 1) := by rw [mul_one, hrp]
        _ ≤ r ^ (a + 1) := pow_le_pow_of_le_one hr0.le hr1.le (by omega)
    · calc ‖toK p (stickCoeff p n k)‖ * r ^ k ≤ 1 * r ^ k :=
            mul_le_mul_of_nonneg_right (by rw [norm_toK]; exact PadicInt.norm_le_one _)
              (by positivity)
        _ = r ^ k := one_mul _
        _ ≤ r ^ (a + 1) := pow_le_pow_of_le_one hr0.le hr1.le (by omega)
  have hlt : r ^ (a + 1) < r ^ a := pow_lt_pow_right_of_lt_one₀ hr0 hr1 (by omega)
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
    (by rw [hmain]; exact (hrest.trans_lt hlt).ne'), hmain]
  exact max_eq_left (hrest.trans hlt.le)

/-- `‖g(ω^n)‖^{p−1} = p^{−(p−1−n)}`. -/
theorem norm_gaussSum_teichCharK_pow_pow {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) {n : ℕ}
    (hn : n ≠ 0) (hnp : n ≤ p - 1) :
    ‖gaussSum (teichCharK p ^ n) (AddChar.zmodChar p hζ.pow_eq_one)‖ ^ (p - 1) =
      ((p : ℝ)⁻¹) ^ (p - 1 - n) := by
  rw [norm_gaussSum_teichCharK_pow p hζ hn hnp, ← pow_mul, mul_comm, pow_mul,
    norm_sub_one_pow hζ]

/-! ### 5. Every character is a power of the Teichmüller character -/

theorem toK_injective : Function.Injective (toK p) := fun x y h => by
  have h1 := norm_toK p (x - y)
  rw [map_sub, h, sub_self, norm_zero] at h1
  exact sub_eq_zero.1 (norm_eq_zero.1 h1.symm)

theorem teich_injective : Function.Injective (teich p) := fun x y h => by
  rw [← toZMod_teich p x, h, toZMod_teich]

/-- At a generator `g` of `𝔽_p^×` the Teichmüller character is a primitive `(p − 1)`-th root of
unity: `ω` is faithful. -/
theorem isPrimitiveRoot_teichCharK {g : (ZMod p)ˣ} (hg : ∀ u, u ∈ Subgroup.zpowers g) :
    IsPrimitiveRoot (teichCharK p g) (p - 1) := by
  have hgo : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  refine ⟨?_, fun l hl => ?_⟩
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one, Units.val_one,
      map_one]
  · rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_one (teichCharK p), teichCharK_apply,
      teichCharK_apply] at hl
    rw [← hgo]
    exact orderOf_dvd_of_pow_eq_one (Units.ext (teich_injective p (toK_injective p hl)))

/-- **Every character of `𝔽_p` with values in `K` is a power `ω^n`, `1 ≤ n ≤ p − 1`.** -/
theorem exists_eq_teichCharK_pow (χ : MulChar (ZMod p) (PadicAlgCl p)) :
    ∃ n : ℕ, 1 ≤ n ∧ n ≤ p - 1 ∧ χ = teichCharK p ^ n := by
  have hp2 := hp.out.two_le
  haveI : NeZero (p - 1) := ⟨by omega⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hη := isPrimitiveRoot_teichCharK p hg
  have hχg : χ (g : ZMod p) ^ (p - 1) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one, Units.val_one,
      map_one]
  obtain ⟨j, -, hjη⟩ := hη.eq_pow_of_pow_eq_one hχg
  refine ⟨if j = 0 then p - 1 else j, by split_ifs <;> omega, by split_ifs <;> omega,
    MulChar.ext fun u => ?_⟩
  obtain ⟨k, rfl⟩ := mem_powers_iff_mem_zpowers.2 (hg u)
  rw [MulChar.pow_apply_coe, Units.val_pow_eq_pow_val, map_pow, map_pow, ← hjη, ← pow_mul,
    ← pow_mul]
  split_ifs with hj0
  · rw [hj0, zero_mul, pow_zero, mul_comm, pow_mul, hη.pow_eq_one, one_pow]
  · rw [mul_comm]

#print axioms norm_gaussSum_teichCharK_pow_pow
#print axioms exists_eq_teichCharK_pow

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.Stickelberger
