import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheGaussSumsOfAPrimeFieldCarryStickelbergersValuation
import GaloisForLFunctions.FamilyContinuationTheory.MoebiusSignedGaussPairingsEndAtThreeFifths
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# The tensor powers of a Gauss sum reach zeta at the rate of its order

Over a function field the tensor powers act on the abscissa and a bound for all of them gives the
line. Over `ℤ` the rank-one tensor powers are the powers `g(χ)^k` of the Gauss sums of a prime
field `𝔽_p`; they reach `ζ` only through the powers of `p` they contain. In an algebraic closure
`K` of `ℚ_p`, with the Teichmüller character `ω` and Stickelberger's valuation
(`norm_gaussSum_teichCharK_pow`):

* **The orbit of valuations** (`exists_norm_gaussSum_pow_orderOf`): a character `χ` of order
  `m ≥ 2` has `‖g(χ)‖^m = p^{−v}` with `1 ≤ v < m` and `gcd(v, m) = 1`. Every Gauss sum of order
  `m` is divisible by `p^{1/m}` at every place above `p`.
* **The extremal character** (`orderOf_extremalChar`, `norm_gaussSum_extremalChar_pow`):
  `χ_m = ω^{−(p−1)/m}` has order `m` and `‖g(χ_m)‖^m = 1/p`. The Galois orbit of `g(χ)` is the set
  of Gauss sums of order `m`, so the power of `p` dividing `g(χ)^k` as an algebraic integer is
  `p^{⌊k/m⌋}`.
* **Torsion** (`norm_prod_jacobiSum_extremalChar`): in `g(χ_m)^m = χ_m(−1) p ∏ J(χ_m, χ_m^i)` the
  Jacobi product is a `p`-adic unit; the `m`-th tensor power reaches `ζ` once, through the
  factor `p`.
* **The price law** (`price_eq_weight_add_logb`, `pairingC_eq_weight_add_logb`): `g(χ_m)^k` has
  weight `k/2` and carries `p^{k/m}`; the difference `(½ − 1/m) k` is the price of a completed
  factor of order `m` in the Möbius-signed Gauss pairings (`MoebiusGaussPairing.pairingC`). It
  vanishes for quadratic factors and is positive for torsion of order `≥ 3`.
-/

open Finset

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.Stickelberger

variable (p : ℕ) [hp : Fact p.Prime]

attribute [local instance] neZero_p

theorem teichCharK_pow_sub_one : teichCharK p ^ (p - 1) = 1 :=
  MulChar.ext fun u => by
    rw [MulChar.pow_apply_coe, teichCharK_apply, ← map_pow, (teich_spec p u.ne_zero).1, map_one,
      MulChar.one_apply_coe]

/-- The Teichmüller character has order `p − 1`. -/
theorem orderOf_teichCharK : orderOf (teichCharK p) = p - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  refine Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (teichCharK_pow_sub_one p)) ?_
  refine (isPrimitiveRoot_teichCharK p hg).dvd_of_pow_eq_one _ ?_
  rw [← MulChar.pow_apply_coe, pow_orderOf_eq_one, MulChar.one_apply_coe]

theorem orderOf_dvd_sub_one (χ : MulChar (ZMod p) (PadicAlgCl p)) : orderOf χ ∣ p - 1 := by
  obtain ⟨n, -, -, rfl⟩ := exists_eq_teichCharK_pow p χ
  rw [← orderOf_teichCharK p]
  exact orderOf_pow_dvd n

/-- **The orbit of valuations.** A character of order `m ≥ 2` has `‖g(χ)‖^m = p^{−v}` with
`1 ≤ v < m` coprime to `m`: for `χ = ω^n`, `d = gcd(p − 1, n)`, `n = s d`, `p − 1 = m d` and
`v = m − s`. -/
theorem exists_norm_gaussSum_pow_orderOf {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    (χ : MulChar (ZMod p) (PadicAlgCl p)) (hχ : 2 ≤ orderOf χ) :
    ∃ v : ℕ, 1 ≤ v ∧ v < orderOf χ ∧ v.Coprime (orderOf χ) ∧
      ‖gaussSum χ (AddChar.zmodChar p hζ.pow_eq_one)‖ ^ orderOf χ = ((p : ℝ)⁻¹) ^ v := by
  obtain ⟨n, hn1, hnp, rfl⟩ := exists_eq_teichCharK_pow p χ
  have hp2 := hp.out.two_le
  have hn0 : n ≠ 0 := by omega
  have hnN : n < p - 1 := by
    refine lt_of_le_of_ne hnp fun h => ?_
    rw [h, teichCharK_pow_sub_one, orderOf_one] at hχ
    omega
  have hX := norm_gaussSum_teichCharK_pow_pow p hζ hn0 hnp
  rw [orderOf_pow' _ hn0, orderOf_teichCharK]
  have hd0 : 0 < (p - 1).gcd n := Nat.gcd_pos_of_pos_left n (by omega)
  have hcop := Nat.coprime_div_gcd_div_gcd hd0
  have hNmd := Nat.div_mul_cancel (Nat.gcd_dvd_left (p - 1) n)
  have hnsd := Nat.div_mul_cancel (Nat.gcd_dvd_right (p - 1) n)
  generalize (p - 1).gcd n = d at hd0 hcop hNmd hnsd ⊢
  generalize (p - 1) / d = m at hcop hNmd ⊢
  generalize n / d = s at hcop hnsd
  have hsm : s < m := Nat.lt_of_mul_lt_mul_right (a := d) (by rw [hNmd, hnsd]; exact hnN)
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · rw [h, zero_mul] at hnsd
      omega
    · exact h
  refine ⟨m - s, by omega, by omega, (Nat.coprime_self_sub_left hsm.le).2 hcop.symm, ?_⟩
  have e1 : p - 1 - n = (m - s) * d := by rw [Nat.sub_mul, hNmd, hnsd]
  rw [e1, ← hNmd, pow_mul, pow_mul] at hX
  exact (pow_left_inj₀ (by positivity) (by positivity) hd0.ne').1 hX

/-- The **extremal character** of order `m`: `χ_m = ω^{(m−1)(p−1)/m} = ω^{−(p−1)/m}`. -/
noncomputable def extremalChar (m : ℕ) : MulChar (ZMod p) (PadicAlgCl p) :=
  teichCharK p ^ ((m - 1) * ((p - 1) / m))

theorem orderOf_extremalChar {m : ℕ} (hm : 2 ≤ m) (hmp : m ∣ p - 1) :
    orderOf (extremalChar p m) = m := by
  obtain ⟨d, hd⟩ := hmp
  have hp2 := hp.out.two_le
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hd; omega
  have hdiv : (p - 1) / m = d := by rw [hd, Nat.mul_div_cancel_left d (by omega)]
  have hcop : Nat.gcd m (m - 1) = 1 :=
    ((Nat.coprime_self_sub_right (by omega : 1 ≤ m)).2 (Nat.coprime_one_right m)).gcd_eq_one
  rw [extremalChar, hdiv, orderOf_pow' _ (Nat.mul_pos (by omega) hd0).ne', orderOf_teichCharK, hd,
    Nat.gcd_mul_right, hcop, one_mul, Nat.mul_div_cancel _ hd0]

/-- **The extremal Gauss sum of order `m` has valuation exactly `1/m`:** `‖g(χ_m)‖^m = 1/p`. -/
theorem norm_gaussSum_extremalChar_pow {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) {m : ℕ}
    (hm : 2 ≤ m) (hmp : m ∣ p - 1) :
    ‖gaussSum (extremalChar p m) (AddChar.zmodChar p hζ.pow_eq_one)‖ ^ m = (p : ℝ)⁻¹ := by
  obtain ⟨d, hd⟩ := hmp
  have hp2 := hp.out.two_le
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at hd; omega
  have hdiv : (p - 1) / m = d := by rw [hd, Nat.mul_div_cancel_left d (by omega)]
  have hn0 : (m - 1) * d ≠ 0 := (Nat.mul_pos (by omega) hd0).ne'
  have hnp : (m - 1) * d ≤ p - 1 := by rw [hd]; exact Nat.mul_le_mul_right d (by omega)
  have hX := norm_gaussSum_teichCharK_pow_pow p hζ hn0 hnp
  have e1 : p - 1 - (m - 1) * d = 1 * d := by
    rw [hd, ← Nat.sub_mul]
    congr 1
    omega
  have hX' : (‖gaussSum (teichCharK p ^ ((m - 1) * d)) (AddChar.zmodChar p hζ.pow_eq_one)‖ ^ m) ^ d =
      ((p : ℝ)⁻¹ ^ 1) ^ d := by
    rw [← pow_mul, ← pow_mul, ← hd, ← e1]
    exact hX
  rw [extremalChar, hdiv, ← pow_one ((p : ℝ)⁻¹)]
  exact (pow_left_inj₀ (by positivity) (by positivity) hd0.ne').1 hX'

/-- **Torsion reaches `ζ` once.** In `g(χ_m)^m = χ_m(−1) p ∏_{1 ≤ i ≤ m−2} J(χ_m, χ_m^i)` the Jacobi
product is a `p`-adic unit. -/
theorem norm_prod_jacobiSum_extremalChar {m : ℕ} (hm : 2 ≤ m) (hmp : m ∣ p - 1) :
    ‖∏ i ∈ Ico 1 (m - 1), jacobiSum (extremalChar p m) (extremalChar p m ^ i)‖ = 1 := by
  obtain ⟨ζ, hζ⟩ : ∃ ζ : PadicAlgCl p, IsPrimitiveRoot ζ p := by
    have : NeZero ((p : ℕ) : PadicAlgCl p) := ⟨Nat.cast_ne_zero.2 hp.out.ne_zero⟩
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p (PadicAlgCl p))
      (Polynomial.degree_cyclotomic_pos p _ hp.out.pos).ne'
    exact ⟨z, Polynomial.isRoot_cyclotomic_iff.1 hz⟩
  have hord := orderOf_extremalChar p hm hmp
  have h := gaussSum_pow_eq_prod_jacobiSum (χ := extremalChar p m) (by rw [hord]; exact hm)
    (AddChar.zmodChar_primitive_of_primitive_root p hζ)
  rw [hord] at h
  have hnorm := norm_gaussSum_extremalChar_pow p hζ hm hmp
  rw [← norm_pow, h, norm_mul, norm_mul] at hnorm
  have h1 : ‖extremalChar p m (-1)‖ = 1 := by
    have h2 : extremalChar p m (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
    exact (pow_left_inj₀ (norm_nonneg _) (zero_le_one : (0 : ℝ) ≤ 1) (two_ne_zero : (2 : ℕ) ≠ 0)).1
      (by rw [← norm_pow, h2, norm_one, one_pow])
  have h2 : ‖((Fintype.card (ZMod p) : ℕ) : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
    rw [ZMod.card, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends,
      Padic.norm_p]
  rw [h1, h2, one_mul] at hnorm
  exact mul_left_cancel₀ (inv_ne_zero (Nat.cast_ne_zero.2 hp.out.ne_zero))
    (hnorm.trans (mul_one _).symm)

/-- **The price law.** `(½ − 1/m) k = k/2 + k log_p ‖g(χ_m)‖`: the weight `k/2` of `g(χ_m)^k`
minus the power `p^{k/m}` it carries. -/
theorem price_eq_weight_add_logb {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p) {m : ℕ}
    (hm : 2 ≤ m) (hmp : m ∣ p - 1) (k : ℝ) :
    (1 / 2 - 1 / (m : ℝ)) * k =
      k / 2 + k * Real.logb p ‖gaussSum (extremalChar p m) (AddChar.zmodChar p hζ.pow_eq_one)‖ := by
  have h := congrArg (Real.logb p) (norm_gaussSum_extremalChar_pow p hζ hm hmp)
  rw [Real.logb_pow, Real.logb_inv, Real.logb_self_eq_one (by exact_mod_cast hp.out.one_lt)] at h
  have hm0 : (m : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hX : Real.logb p ‖gaussSum (extremalChar p m) (AddChar.zmodChar p hζ.pow_eq_one)‖ =
      -1 / m := eq_div_of_mul_eq hm0 (by rw [mul_comm]; exact h)
  rw [hX]
  ring

/-- **The price of a Gauss pairing is weight minus `p`-content.** For a Möbius-signed Gauss pairing
over the characters of `𝔽_p`, each completed factor `x` contributes the weight `k/2` of the
`k`-th power of the extremal Gauss sum of its order plus `k log_p` of its norm. -/
theorem pairingC_eq_weight_add_logb {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ p)
    (P : FamilyContinuationTheory.MoebiusGaussPairing (MulChar (ZMod p) (PadicAlgCl p))) :
    P.pairingC = (P.compChars.map fun x => (P.period : ℝ) / 2 + (P.period : ℝ) *
        Real.logb p ‖gaussSum (extremalChar p (orderOf x)) (AddChar.zmodChar p hζ.pow_eq_one)‖).sum +
      (P.rowChars.length : ℝ) * ((P.period : ℝ) / 2 - 1) := by
  have hmap : (P.compChars.map fun x => (1 / 2 - 1 / (orderOf x : ℝ)) * (P.period : ℝ)) =
      P.compChars.map fun x => (P.period : ℝ) / 2 + (P.period : ℝ) *
        Real.logb p ‖gaussSum (extremalChar p (orderOf x)) (AddChar.zmodChar p hζ.pow_eq_one)‖ :=
    List.map_congr_left fun x hx =>
      price_eq_weight_add_logb p hζ (P.moebius.two_le_order x (List.mem_append_left _ hx))
        (orderOf_dvd_sub_one p x) _
  rw [FamilyContinuationTheory.MoebiusGaussPairing.pairingC, hmap]

#print axioms exists_norm_gaussSum_pow_orderOf
#print axioms norm_prod_jacobiSum_extremalChar
#print axioms pairingC_eq_weight_add_logb

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.Stickelberger
