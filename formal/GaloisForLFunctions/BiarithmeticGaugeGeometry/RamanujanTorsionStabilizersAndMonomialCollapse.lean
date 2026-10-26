import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.FieldTheory.Finite.Basic

/-!
# Monomial Theta Collapse vs. Biarithmetic Rational-Torsion Rotation and Ramanujan Contrast

On higher-rank rectangular theta series over `ℤ²`, a natural candidate for escaping degree-`1`
rigidity traps is a monomial lattice dilation `(m₁, m₂) ↦ (q₁ m₁, q₂ m₂)`. Purely separable
monomial dilations suffer **monomial theta diagonal collapse**: any separable rectangular weight
`G(m₁, m₂) = g₁(m₁) g₂(m₂)` factors identically into 1D marginals under `(q₁, q₂)` and preserves
zero additive torsion `(0, 0) ∈ (ℤ/Nℤ)²`, leaving the `n = 0` Poisson pole mode untouched.

This module establishes both the exact algebraic collapse of monomial theta dilations and the
**biarithmetic rational-torsion mechanism** that breaks it:

1. **Monomial Lattice Diagonal Collapse (`monomial_theta_sum_factors`,
   `monomial_torsion_fixes_origin`, `monomial_torsion_preserves_axes`).**
   For every separable weight `G(m₁, m₂) = g₁(m₁) g₂(m₂)` and monomial dilation `(q₁, q₂)`, the
   2D lattice sum factors identically into the product of 1D marginals, and the induced action on
   `ZMod N × ZMod N` fixes `(0, 0)` and preserves both coordinate axes without cross-torsion mixing.

2. **Biarithmetic Rational-Torsion Rotation & Dyadic Fixed-Point-Free Escape
   (`torsionMulEquiv`, `torsionMulEquiv_no_fixed_points_of_sub_one_isUnit`,
   `dyadic_torsion_rotation_fixed_point_free`).**
   Replacing zero torsion by primitive rational torsion `(ZMod q)ˣ` turns coprime prime dilation
   `p` (` gcd(p, q) = 1`) into a bijection `u ↦ p u` on `(ZMod q)ˣ`. Whenever `(p : ZMod q) − 1`
   is a unit (`q ≥ 2`), this rotation has **zero fixed points**. In particular, for **every** odd
   modulus `q ≥ 3`, dyadic prime scaling `u ↦ 2 u` permutes `(ZMod q)ˣ` without a single fixed
   point (`2 − 1 = 1` is always a unit!).

3. **Primitive Ramanujan Torsion Sums & Parseval Energy (`ramanujanTorsionSum`,
   `ramanujanTorsionSum_coprime_mul`, `ramanujanTorsionSum_zero`, `sum_ramanujanTorsionSum_eq_zero`,
   `sum_normSq_ramanujanTorsionSum`, `ramanujanTorsionSum_prime`).**
   Summing `e(u x / q)` over the primitive torsion orbit `u ∈ (ZMod q)ˣ` produces the Ramanujan
   torsion kernel `c_q(x)`, which is real-valued, strictly invariant under every coprime dilation
   `x ↦ p x`, has zero residue mean `∑_{x ∈ ZMod q} c_q(x) = 0` (`q ≥ 2`), and carries exact
   Parseval energy `∑_{x ∈ ZMod q} ‖c_q(x)‖² = q φ(q)`.

4. **Pole-Cancelled Bi-Torsion Contrast (`biTorsionContrast`, `biTorsionContrast_zero`,
   `biTorsionContrast_coprime_mul`, `biTorsionContrast_primes_values`).**
   Pairing two moduli `q₁, q₂` via `Δ_{q₁, q₂}(n) = φ(q₂) c_{q₁}(n) − φ(q₁) c_{q₂}(n)`
   **identically annihilates the `n = 0` Poisson pole mode** (`Δ_{q₁, q₂}(0) = 0`), remains
   invariant under every prime `p` coprime to `q₁ q₂`, and for distinct primes `q₁ ≠ q₂` takes
   strictly nonzero, sign-separated values across `gcd(n, q₁ q₂) = 1` (`q₁ − q₂ ≠ 0`),
   `q₁ ∣ n, q₂ ∤ n` (`q₂(q₁ − 1) > 0`), and `q₂ ∣ n, q₁ ∤ n` (`−q₁(q₂ − 1) < 0`).
-/

open Finset Complex

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

/-! ## §1. Rank-2 Monomial Theta Diagonal Collapse -/

/-- **Monomial Theta Marginal Factorization (`monomial_theta_sum_factors`).**
For any finite lattice boxes `S₁, S₂ ⊆ ℤ`, separable weight `G(m₁, m₂) = g₁(m₁) g₂(m₂)`, and
monomial dilation `(q₁, q₂) ∈ ℤ × ℤ`, the 2D dilated lattice sum factors identically into the
product of 1D marginals, generating zero genuine 2D arithmetic coupling. -/
theorem monomial_theta_sum_factors {R : Type*} [CommSemiring R]
    (S₁ S₂ : Finset ℤ) (g₁ g₂ : ℤ → R) (q₁ q₂ : ℤ) :
    (∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, g₁ (q₁ * m₁) * g₂ (q₂ * m₂)) =
      (∑ m₁ ∈ S₁, g₁ (q₁ * m₁)) * (∑ m₂ ∈ S₂, g₂ (q₂ * m₂)) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m₁ _ => ?_
  rw [Finset.mul_sum]

/-- Diagonal monomial dilation on `ZMod N × ZMod N`. -/
def monomialTorsionAction (N : ℕ) (q₁ q₂ : ℕ) (x : ZMod N × ZMod N) : ZMod N × ZMod N :=
  ((q₁ : ZMod N) * x.1, (q₂ : ZMod N) * x.2)

/-- Monomial dilation fixes the zero-torsion origin `(0, 0) ∈ ZMod N × ZMod N` for all `(q₁, q₂)`. -/
@[simp] theorem monomial_torsion_fixes_origin (N q₁ q₂ : ℕ) :
    monomialTorsionAction N q₁ q₂ (0, 0) = (0, 0) := by
  simp [monomialTorsionAction]

/-- Monomial dilation preserves each coordinate axis independently, never mixing horizontal and
vertical additive torsion. -/
theorem monomial_torsion_preserves_axes (N q₁ q₂ : ℕ) (x : ZMod N) :
    (monomialTorsionAction N q₁ q₂ (x, 0)).2 = 0 ∧
      (monomialTorsionAction N q₁ q₂ (0, x)).1 = 0 := by
  simp [monomialTorsionAction]

/-! ## §2. Biarithmetic Rational-Torsion Rotation and Fixed-Point-Free Escape -/

/-- Multiplicative rotation on primitive mod-`q` rational torsion `(ZMod q)ˣ` induced by a coprime
scaling factor `p` (`Nat.Coprime p q`). -/
def torsionMulEquiv {q : ℕ} (p : ℕ) (hp : Nat.Coprime p q) : (ZMod q)ˣ ≃ (ZMod q)ˣ :=
  Equiv.mulLeft (ZMod.unitOfCoprime p hp)

@[simp] theorem coe_torsionMulEquiv {q : ℕ} (p : ℕ) (hp : Nat.Coprime p q) (u : (ZMod q)ˣ) :
    ((torsionMulEquiv p hp u : (ZMod q)ˣ) : ZMod q) = (p : ZMod q) * (u : ZMod q) := by
  simp [torsionMulEquiv]

/-- **Stabilizer Escape Criterion (`torsionMulEquiv_no_fixed_points_of_sub_one_isUnit`).**
For any modulus `q ≥ 2`, if `Nat.Coprime p q` and `(p : ZMod q) − 1` is a unit in `ZMod q`, then
coprime multiplication `u ↦ p u` has **zero fixed points** on primitive mod-`q` torsion `(ZMod q)ˣ`. -/
theorem torsionMulEquiv_no_fixed_points_of_sub_one_isUnit {q p : ℕ} (hq : 2 ≤ q)
    (hp : Nat.Coprime p q) (hsub : IsUnit ((p : ZMod q) - 1)) :
    ∀ u : (ZMod q)ˣ, torsionMulEquiv p hp u ≠ u := by
  haveI : Fact (1 < q) := ⟨by omega⟩
  obtain ⟨v, hv⟩ := hsub
  intro u hfix
  have hval : (p : ZMod q) * (u : ZMod q) = (u : ZMod q) := by
    simpa [torsionMulEquiv] using congrArg (fun w : (ZMod q)ˣ => (w : ZMod q)) hfix
  have hzero : ((p : ZMod q) - 1) * (u : ZMod q) = 0 := by
    linear_combination hval
  rw [← hv] at hzero
  have hu0 : (u : ZMod q) = 0 := by
    have hmul := congrArg (fun x : ZMod q => (v⁻¹ : (ZMod q)ˣ) * x) hzero
    simp only [← mul_assoc, Units.inv_mul, one_mul, mul_zero] at hmul
    exact hmul
  exact Units.ne_zero u hu0

/-- **Universal Dyadic Fixed-Point-Free Torsion Theorem (`dyadic_torsion_rotation_fixed_point_free`).**
For **every** odd modulus `q ≥ 3`, `Nat.Coprime 2 q` holds and dyadic scaling `u ↦ 2 u` permutes
primitive rational torsion `(ZMod q)ˣ` **without a single fixed point** (`2 − 1 = 1` is always a
unit in `ZMod q`). -/
theorem dyadic_torsion_rotation_fixed_point_free {q : ℕ} (hq : 3 ≤ q) (hodd : Odd q) :
    ∃ hcop : Nat.Coprime 2 q, ∀ u : (ZMod q)ˣ, torsionMulEquiv 2 hcop u ≠ u := by
  have hcop : Nat.Coprime 2 q :=
    Nat.prime_two.coprime_iff_not_dvd.mpr (by rwa [← Nat.not_even_iff_odd, even_iff_two_dvd] at hodd)
  refine ⟨hcop, torsionMulEquiv_no_fixed_points_of_sub_one_isUnit (by omega) hcop ?_⟩
  have h21 : ((2 : ℕ) : ZMod q) - 1 = 1 := by norm_num
  rw [h21]
  exact isUnit_one

/-! ## §3. Primitive Ramanujan Torsion Sums, Gauge Invariance, and Parseval Energy -/

/-- Finite additive character orthogonality on `ZMod q`:
`∑_{x : ZMod q} e(a x / q) = q` if `a = 0` and `0` otherwise. -/
theorem sum_stdAddChar_mul_eq (q : ℕ) [NeZero q] (a : ZMod q) :
    ∑ x : ZMod q, ZMod.stdAddChar (a * x) = if a = 0 then (q : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (ψ := ZMod.stdAddChar (N := q)) a (ZMod.isPrimitive_stdAddChar q)
  simp_rw [mul_comm a]
  rw [h, ZMod.card q]
  split_ifs <;> simp

/-- **Primitive Ramanujan Torsion Sum (`ramanujanTorsionSum`).**
Sum of `e(u x / q)` over all primitive mod-`q` torsion characteristics `u ∈ (ZMod q)ˣ`. -/
def ramanujanTorsionSum (q : ℕ) [NeZero q] (x : ZMod q) : ℂ :=
  ∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((u : ZMod q) * x)

/-- **Coprime Dilation Gauge Invariance (`ramanujanTorsionSum_coprime_mul`).**
While individual primitive torsion modes `e(u x / q)` are rotated without fixed points by coprime
primes `p`, their primitive orbit sum `c_q(x)` is **strictly invariant** under `x ↦ p x`. -/
theorem ramanujanTorsionSum_coprime_mul (q : ℕ) [NeZero q] {p : ℕ} (hp : Nat.Coprime p q)
    (x : ZMod q) :
    ramanujanTorsionSum q ((p : ZMod q) * x) = ramanujanTorsionSum q x := by
  unfold ramanujanTorsionSum
  symm
  refine (Equiv.sum_comp (torsionMulEquiv p hp)
    (fun u => ZMod.stdAddChar ((u : ZMod q) * x))).symm.trans ?_
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [coe_torsionMulEquiv]
  congr 1
  ring

/-- `ramanujanTorsionSum q x` is real-valued (`conj (c_q(x)) = c_q(x)`). -/
theorem ramanujanTorsionSum_conj (q : ℕ) [NeZero q] (x : ZMod q) :
    starRingEnd ℂ (ramanujanTorsionSum q x) = ramanujanTorsionSum q x := by
  unfold ramanujanTorsionSum
  rw [map_sum]
  have hneg : ∀ u : (ZMod q)ˣ,
      starRingEnd ℂ (ZMod.stdAddChar ((u : ZMod q) * x)) =
        ZMod.stdAddChar (((-u : (ZMod q)ˣ) : ZMod q) * x) := fun u => by
    rw [← AddChar.map_neg_eq_conj, Units.val_neg, neg_mul]
  simp_rw [hneg]
  exact Equiv.sum_comp (Equiv.neg (ZMod q)ˣ) (fun w => ZMod.stdAddChar ((w : ZMod q) * x))

/-- Evaluation at the zero residue (`x = 0`): `c_q(0) = φ(q)`. -/
@[simp] theorem ramanujanTorsionSum_zero (q : ℕ) [NeZero q] :
    ramanujanTorsionSum q 0 = (Nat.totient q : ℂ) := by
  unfold ramanujanTorsionSum
  simp [ZMod.card_units_eq_totient q]

/-- **Zero Residue Mean (`sum_ramanujanTorsionSum_eq_zero`).**
For every modulus `q ≥ 2`, `∑_{x : ZMod q} c_q(x) = 0` because every unit `u ∈ (ZMod q)ˣ` is a
non-trivial additive character frequency (`(u : ZMod q) ≠ 0`). -/
theorem sum_ramanujanTorsionSum_eq_zero {q : ℕ} (hq : 2 ≤ q) :
    haveI : NeZero q := ⟨by omega⟩
    ∑ x : ZMod q, ramanujanTorsionSum q x = 0 := by
  haveI : NeZero q := ⟨by omega⟩
  haveI : Fact (1 < q) := ⟨by omega⟩
  unfold ramanujanTorsionSum
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun u _ => ?_
  rw [sum_stdAddChar_mul_eq q (u : ZMod q), if_neg (Units.ne_zero u)]

/-- **Exact Parseval Torsion Energy (`sum_normSq_ramanujanTorsionSum`).**
For every `q ≥ 1`, `∑_{x : ZMod q} ‖c_q(x)‖² = q φ(q)`. -/
theorem sum_normSq_ramanujanTorsionSum (q : ℕ) [NeZero q] :
    ∑ x : ZMod q, Complex.normSq (ramanujanTorsionSum q x) =
      (q : ℝ) * (Nat.totient q : ℝ) := by
  classical
  have hC : ∑ x : ZMod q,
      ramanujanTorsionSum q x * starRingEnd ℂ (ramanujanTorsionSum q x) =
      (q : ℂ) * (Nat.totient q : ℂ) := by
    unfold ramanujanTorsionSum
    simp_rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    have hprod : ∀ (x : ZMod q) (u v : (ZMod q)ˣ),
        ZMod.stdAddChar ((u : ZMod q) * x) *
          starRingEnd ℂ (ZMod.stdAddChar ((v : ZMod q) * x)) =
          ZMod.stdAddChar (((u : ZMod q) - (v : ZMod q)) * x) := fun x u v => by
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul]
      congr 1; ring
    simp_rw [hprod]
    rw [Finset.sum_comm]
    have hswap : (∑ u : (ZMod q)ˣ, ∑ x : ZMod q, ∑ v : (ZMod q)ˣ,
        ZMod.stdAddChar (((u : ZMod q) - (v : ZMod q)) * x)) =
        ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ, ∑ x : ZMod q,
          ZMod.stdAddChar (((u : ZMod q) - (v : ZMod q)) * x) :=
      Finset.sum_congr rfl fun u _ => Finset.sum_comm
    rw [hswap]
    have hinner : ∀ u : (ZMod q)ˣ,
        (∑ v : (ZMod q)ˣ, ∑ x : ZMod q, ZMod.stdAddChar (((u : ZMod q) - (v : ZMod q)) * x)) =
          (q : ℂ) := fun u => by
      simp_rw [sum_stdAddChar_mul_eq q, sub_eq_zero, Units.ext_iff.symm]
      simp
    simp_rw [hinner, Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient q,
      nsmul_eq_mul, mul_comm]
  have hnorm : ∀ z : ℂ, z * starRingEnd ℂ z = ((Complex.normSq z : ℝ) : ℂ) :=
    Complex.mul_conj
  simp_rw [hnorm] at hC
  exact_mod_cast hC

/-- **Prime-Modulus Ramanujan Dichotomy (`ramanujanTorsionSum_prime`).**
For any prime modulus `q`, `c_q(x) = q − 1` if `x = 0` and `c_q(x) = −1` if `x ≠ 0`. -/
theorem ramanujanTorsionSum_prime (q : ℕ) [Fact q.Prime] (x : ZMod q) :
    ramanujanTorsionSum q x = if x = 0 then (q : ℂ) - 1 else -1 := by
  classical
  unfold ramanujanTorsionSum
  have heq : ∑ u : (ZMod q)ˣ, ZMod.stdAddChar ((u : ZMod q) * x) =
      ∑ a ∈ (Finset.univ : Finset (ZMod q)).erase 0, ZMod.stdAddChar (a * x) := by
    rw [Finset.sum_subtype (s := (Finset.univ : Finset (ZMod q)).erase 0)
      (p := fun a : ZMod q => a ≠ 0) (fun a => by simp)
      (fun a => ZMod.stdAddChar (a * x))]
    exact Fintype.sum_equiv unitsEquivNeZero _ _ (fun _ => rfl)
  have htot := sum_stdAddChar_mul_eq q x
  simp_rw [mul_comm x] at htot
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q)),
      zero_mul, AddChar.map_zero_eq_one] at htot
  rw [heq]
  split_ifs with hx
  · rw [if_pos hx] at htot
    linear_combination htot
  · rw [if_neg hx] at htot
    linear_combination htot

/-! ## §4. Pole-Cancelled Bi-Torsion Contrast (`biTorsionContrast`) -/

/-- **Pole-Cancelled Bi-Torsion Contrast (`biTorsionContrast`).**
For two moduli `q₁, q₂ ≥ 1`, `Δ_{q₁, q₂}(n) := φ(q₂) c_{q₁}(n) − φ(q₁) c_{q₂}(n)` couples two
distinct rational torsion levels while cancelling the `n = 0` Poisson pole mode identically. -/
def biTorsionContrast (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] (n : ℤ) : ℂ :=
  (Nat.totient q₂ : ℂ) * ramanujanTorsionSum q₁ (n : ZMod q₁) -
    (Nat.totient q₁ : ℂ) * ramanujanTorsionSum q₂ (n : ZMod q₂)

/-- **Exact Poisson Zero-Mode Annihilation (`biTorsionContrast_zero`).**
At the pole mode `n = 0`, `Δ_{q₁, q₂}(0) = φ(q₂) φ(q₁) − φ(q₁) φ(q₂) = 0` identically. -/
@[simp] theorem biTorsionContrast_zero (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂] :
    biTorsionContrast q₁ q₂ 0 = 0 := by
  unfold biTorsionContrast
  rw [Int.cast_zero, Int.cast_zero, ramanujanTorsionSum_zero, ramanujanTorsionSum_zero]
  ring

/-- **Coprime Dilation Invariance (`biTorsionContrast_coprime_mul`).**
For every scaling factor `p : ℕ` coprime to both `q₁` and `q₂`, `Δ_{q₁, q₂}(p n) = Δ_{q₁, q₂}(n)`. -/
theorem biTorsionContrast_coprime_mul (q₁ q₂ : ℕ) [NeZero q₁] [NeZero q₂]
    {p : ℕ} (hp₁ : Nat.Coprime p q₁) (hp₂ : Nat.Coprime p q₂) (n : ℤ) :
    biTorsionContrast q₁ q₂ ((p : ℤ) * n) = biTorsionContrast q₁ q₂ n := by
  unfold biTorsionContrast
  have hc₁ : (((p : ℤ) * n : ℤ) : ZMod q₁) = (p : ZMod q₁) * (n : ZMod q₁) := by push_cast; rfl
  have hc₂ : (((p : ℤ) * n : ℤ) : ZMod q₂) = (p : ZMod q₂) * (n : ZMod q₂) := by push_cast; rfl
  rw [hc₁, hc₂, ramanujanTorsionSum_coprime_mul q₁ hp₁, ramanujanTorsionSum_coprime_mul q₂ hp₂]

/-- **Sign-Separated Divisibility Selectivity (`biTorsionContrast_primes_values`).**
For any two distinct primes `q₁ ≠ q₂`:
1. `Δ_{q₁, q₂}(0) = 0` (Poisson pole mode killed);
2. `Δ_{q₁, q₂}(1) = q₁ − q₂ ≠ 0` (unit lattice nodes non-degenerate);
3. `Δ_{q₁, q₂}(q₁) = q₂ (q₁ − 1) > 0` (`q₁`-divisible branch strictly positive);
4. `Δ_{q₁, q₂}(q₂) = −q₁ (q₂ − 1) < 0` (`q₂`-divisible branch strictly negative). -/
theorem biTorsionContrast_primes_values {q₁ q₂ : ℕ}
    [hq₁ : Fact q₁.Prime] [hq₂ : Fact q₂.Prime] (hne : q₁ ≠ q₂) :
    biTorsionContrast q₁ q₂ 0 = 0 ∧
      biTorsionContrast q₁ q₂ 1 = (q₁ : ℂ) - (q₂ : ℂ) ∧
      biTorsionContrast q₁ q₂ q₁ = (q₂ : ℂ) * ((q₁ : ℂ) - 1) ∧
      biTorsionContrast q₁ q₂ q₂ = -(q₁ : ℂ) * ((q₂ : ℂ) - 1) := by
  have hp₁ : q₁.Prime := hq₁.out
  have hp₂ : q₂.Prime := hq₂.out
  have h1_ge2 : 2 ≤ q₁ := hp₁.two_le
  have h2_ge2 : 2 ≤ q₂ := hp₂.two_le
  have htot₁ : (Nat.totient q₁ : ℂ) = (q₁ : ℂ) - 1 := by
    rw [Nat.totient_prime hp₁, Nat.cast_sub (by omega), Nat.cast_one]
  have htot₂ : (Nat.totient q₂ : ℂ) = (q₂ : ℂ) - 1 := by
    rw [Nat.totient_prime hp₂, Nat.cast_sub (by omega), Nat.cast_one]
  have hq₁_mod_q₂ : ((q₁ : ℤ) : ZMod q₂) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact hne ((Nat.prime_dvd_prime_iff_eq hp₂ hp₁).mp hdvd).symm
  have hq₂_mod_q₁ : ((q₂ : ℤ) : ZMod q₁) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact hne ((Nat.prime_dvd_prime_iff_eq hp₁ hp₂).mp hdvd)
  refine ⟨biTorsionContrast_zero q₁ q₂, ?_, ?_, ?_⟩
  · unfold biTorsionContrast
    rw [htot₁, htot₂, Int.cast_one, Int.cast_one,
        ramanujanTorsionSum_prime q₁ 1, ramanujanTorsionSum_prime q₂ 1,
        if_neg one_ne_zero, if_neg one_ne_zero]
    ring
  · unfold biTorsionContrast
    have hz₁ : ((q₁ : ℤ) : ZMod q₁) = 0 := by rw [Int.cast_natCast, ZMod.natCast_self]
    rw [htot₁, htot₂, hz₁,
        ramanujanTorsionSum_prime q₁ 0, ramanujanTorsionSum_prime q₂ ((q₁ : ℤ) : ZMod q₂),
        if_pos rfl, if_neg hq₁_mod_q₂]
    ring
  · unfold biTorsionContrast
    have hz₂ : ((q₂ : ℤ) : ZMod q₂) = 0 := by rw [Int.cast_natCast, ZMod.natCast_self]
    rw [htot₁, htot₂, hz₂,
        ramanujanTorsionSum_prime q₁ ((q₂ : ℤ) : ZMod q₁), ramanujanTorsionSum_prime q₂ 0,
        if_neg hq₂_mod_q₁, if_pos rfl]
    ring

end GaloisForLFunctions.BiarithmeticGaugeGeometry
