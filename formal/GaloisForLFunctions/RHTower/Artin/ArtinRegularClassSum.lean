import GaloisForLFunctions.RHTower.Artin.ArtinClassFunctionOfARegularElement
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Data.Nat.Factorization.Basic

/-!
# A combination of elementary characters with values prime to `p`

For a prime `p` and a finite group `G`, let `Ψ` be the sum of the class functions
`regularClassFunction p x` over representatives `x` of the conjugacy classes of `p`-regular
elements (`regularClassSum`). Then:

* `Ψ` is a combination, with algebraic integer coefficients, of characters induced from
  Brauer-elementary subgroups (`regularClassSum_mem_inducedSpanInt`);
* its values are natural numbers (`exists_nat_regularClassSum`);
* at a `p`-regular `s` only the representative of the class of `s` contributes, and `Ψ(s)` is
  the index of a Sylow `p`-subgroup in a centralizer, prime to `p`
  (`regularClassSum_of_regular`);
* every `y` has a `p`-regular part `z`, a power of `y` with `y^{p^k} = z^{p^k}`
  (`exists_regular_part`), and `Ψ(y) ≡ Ψ(z) (mod p)`. So **no value of `Ψ` is divisible by `p`**
  (`exists_nat_not_dvd_regularClassSum`).
-/

open scoped Classical BigOperators

noncomputable section

universe u

namespace GaloisForLFunctions

variable {G : Type u} [Group G]

/-- **The `p`-regular part.** Every element `y` of a finite group has a power `z` of order prime
to `p` with `y^{p^k} = z^{p^k}` for some `k`. -/
theorem exists_regular_part [Finite G] {p : ℕ} (hp : p.Prime) (y : G) :
    ∃ z ∈ Subgroup.zpowers y, (orderOf z).Coprime p ∧ ∃ k : ℕ, y ^ p ^ k = z ^ p ^ k := by
  -- `|y| = q m` with `q = p^a` and `m` prime to `p`
  obtain ⟨a, m, hnm, hcop⟩ : ∃ a m : ℕ, p ^ a * m = orderOf y ∧ p.Coprime m :=
    ⟨_, _, Nat.ordProj_mul_ordCompl_eq_self (orderOf y) p,
      Nat.coprime_ordCompl hp (orderOf_pos y).ne'⟩
  obtain ⟨q, hq⟩ : ∃ q : ℕ, q = p ^ a := ⟨_, rfl⟩
  rw [← hq] at hnm
  -- Bézout: `q u + m v = 1`
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, (q : ℤ) * u + (m : ℤ) * v = 1 := by
    refine ⟨Nat.gcdA q m, Nat.gcdB q m, ?_⟩
    rw [← Nat.gcd_eq_gcd_ab, hq, (Nat.Coprime.pow_left a hcop).gcd_eq_one, Nat.cast_one]
  have hy : y ^ ((q * m : ℕ) : ℤ) = 1 := by rw [zpow_natCast, hnm, pow_orderOf_eq_one]
  refine ⟨y ^ ((q : ℤ) * u), Subgroup.zpow_mem_zpowers y _, ?_, a, ?_⟩
  · -- the order of `z = y^{q u}` divides `m`
    have hz : (y ^ ((q : ℤ) * u)) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul,
        show (q : ℤ) * u * (m : ℤ) = ((q * m : ℕ) : ℤ) * u by push_cast; ring,
        zpow_mul, hy, one_zpow]
    exact Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hz) hcop.symm
  · -- `y^q = z^q · (y^{q m})^v`
    have e : (q : ℤ) = (q : ℤ) * u * (q : ℤ) + ((q * m : ℕ) : ℤ) * v := by
      push_cast
      linear_combination (-(q : ℤ)) * huv
    rw [← hq]
    calc y ^ q = y ^ (q : ℤ) := (zpow_natCast y q).symm
      _ = y ^ ((q : ℤ) * u * (q : ℤ) + ((q * m : ℕ) : ℤ) * v) := congrArg (y ^ ·) e
      _ = (y ^ ((q : ℤ) * u)) ^ (q : ℤ) * (y ^ ((q * m : ℕ) : ℤ)) ^ v := by
        rw [zpow_add, zpow_mul y ((q : ℤ) * u) q, zpow_mul y ((q * m : ℕ) : ℤ) v]
      _ = (y ^ ((q : ℤ) * u)) ^ q := by rw [hy, one_zpow, mul_one, zpow_natCast]

variable [Fintype G]

theorem regularClassFunction_conj (p : ℕ) (x : G) (hx : (orderOf x).Coprime p) (y s : G) :
    regularClassFunction p x hx (y * s * y⁻¹) = regularClassFunction p x hx s :=
  inducedFunction_conj _ _ y s

/-- The sum of the class functions of representatives of the conjugacy classes of `p`-regular
elements. -/
def regularClassSum (p : ℕ) : G → ℂ :=
  ∑ c : ConjClasses G, if h : (orderOf (Quotient.out c)).Coprime p then
    regularClassFunction p (Quotient.out c) h else 0

theorem regularClassSum_apply (p : ℕ) (s : G) :
    regularClassSum p s = ∑ c : ConjClasses G,
      if h : (orderOf (Quotient.out c)).Coprime p then
        regularClassFunction p (Quotient.out c) h s else 0 := by
  rw [regularClassSum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : (orderOf (Quotient.out c)).Coprime p
  · rw [dif_pos h, dif_pos h]
  · rw [dif_neg h, dif_neg h]
    rfl

/-- The sum is a combination, with algebraic integer coefficients, of characters induced from
Brauer-elementary subgroups. -/
theorem regularClassSum_mem_inducedSpanInt {p : ℕ} (hp : p.Prime) :
    regularClassSum p ∈ inducedSpanInt (brauerElementaryFamily G) := by
  refine AddSubgroup.sum_mem _ fun c _ => ?_
  by_cases h : (orderOf (Quotient.out c)).Coprime p
  · rw [dif_pos h]
    exact regularClassFunction_mem_inducedSpanInt p _ h hp
  · rw [dif_neg h]
    exact zero_mem _

/-- The values of the sum are natural numbers. -/
theorem exists_nat_regularClassSum (p : ℕ) (s : G) : ∃ n : ℕ, regularClassSum p s = n := by
  have hterm : ∀ c : ConjClasses G, ∃ n : ℕ,
      (if h : (orderOf (Quotient.out c)).Coprime p then
        regularClassFunction p (Quotient.out c) h s else 0) = n := by
    intro c
    by_cases h : (orderOf (Quotient.out c)).Coprime p
    · rw [dif_pos h]
      exact exists_nat_regularClassFunction p _ h s
    · exact ⟨0, by rw [dif_neg h, Nat.cast_zero]⟩
  choose n hn using hterm
  refine ⟨∑ c, n c, ?_⟩
  rw [regularClassSum_apply, Nat.cast_sum]
  exact Finset.sum_congr rfl fun c _ => hn c

/-- **At a `p`-regular element the sum is the index of a Sylow `p`-subgroup in a centralizer.**
Only the representative of the class of `s` contributes. -/
theorem regularClassSum_of_regular {p : ℕ} [Fact p.Prime] {s : G}
    (hs : (orderOf s).Coprime p) : ∃ n : ℕ, ¬ p ∣ n ∧ regularClassSum p s = n := by
  have hrep : ConjClasses.mk (Quotient.out (ConjClasses.mk s)) = ConjClasses.mk s :=
    Quotient.out_eq _
  obtain ⟨y, hy⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp hrep.symm)
  have hr : (orderOf (Quotient.out (ConjClasses.mk s))).Coprime p := by
    rw [← hy, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hs
  refine ⟨centralizerSylowIndex p (Quotient.out (ConjClasses.mk s)),
    not_dvd_centralizerSylowIndex p _, ?_⟩
  rw [regularClassSum_apply, Finset.sum_eq_single (ConjClasses.mk s)]
  · rw [dif_pos hr, ← regularClassFunction_conj p _ hr y s, hy]
    exact regularClassFunction_self p _ hr
  · intro c _ hc
    by_cases h : (orderOf (Quotient.out c)).Coprime p
    · rw [dif_pos h]
      refine regularClassFunction_eq_zero p _ h hs fun z hz => hc ?_
      have hcz : ConjClasses.mk s = ConjClasses.mk (Quotient.out c) :=
        ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨z, hz⟩)
      exact (Quotient.out_eq c).symm.trans hcz.symm
    · rw [dif_neg h]
  · exact fun hnot => absurd (Finset.mem_univ _) hnot

/-- **No value of the sum is divisible by `p`**: the value at `y` is congruent modulo `p` to
the value at the `p`-regular part of `y`. -/
theorem exists_nat_not_dvd_regularClassSum {p : ℕ} (hp : p.Prime) (y : G) :
    ∃ n : ℕ, ¬ p ∣ n ∧ regularClassSum p y = n := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz, hzreg, k, hk⟩ := exists_regular_part hp y
  obtain ⟨nz, hnz, hΨz⟩ := regularClassSum_of_regular hzreg
  obtain ⟨ny, hΨy⟩ := exists_nat_regularClassSum p y
  refine ⟨ny, fun hdvd => hnz ?_, hΨy⟩
  have hmem := inducedSpanInt_le_virtualIntGroup _ (regularClassSum_mem_inducedSpanInt hp (G := G))
  have h := int_dvd_sub_of_pow_eq hmem hp k hz hk (n := ny) (n' := nz)
    (by rw [hΨy, Int.cast_natCast]) (by rw [hΨz, Int.cast_natCast])
  have h2 := dvd_sub (Int.natCast_dvd_natCast.mpr hdvd) h
  rw [sub_sub_cancel] at h2
  exact Int.natCast_dvd_natCast.mp h2

end GaloisForLFunctions
