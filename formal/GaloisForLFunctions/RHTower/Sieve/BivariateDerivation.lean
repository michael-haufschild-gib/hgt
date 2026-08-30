import GaloisForLFunctions.RHTower.Sieve.BivariateMultiplicative

/-!
# Derivations of bivariate multiplicative functions

The gcd-logarithmic Selberg family is the `s`-derivative at `s = 1` of the two-parameter family
`c_s(m,n) = μ(m)μ(n)(m,n)^s/(mn)`.  Such a derivative is not multiplicative; it satisfies the
Leibniz rule

`D (a*c) (b*d) = D a b * f c d + f a b * D c d`   for pair-coprime arguments.

This file fixes that structure and proves the rigidity statement the whole route rests on: two
derivations of the same bivariate multiplicative function that agree on simultaneous prime-power
pairs are equal.
-/

open Finset

namespace RHTower.Sieve

noncomputable section

/-- A Leibniz derivation of a bivariate multiplicative function. -/
def BivariateDerivation (f D : ℕ → ℕ → ℝ) : Prop :=
  D 1 1 = 0 ∧
    ∀ {a b c d : ℕ}, Nat.Coprime (a * b) (c * d) →
      D (a * c) (b * d) = D a b * f c d + f a b * D c d

theorem BivariateDerivation.one {f D : ℕ → ℕ → ℝ}
    (hD : BivariateDerivation f D) : D 1 1 = 0 := hD.1

theorem BivariateDerivation.leibniz {f D : ℕ → ℕ → ℝ}
    (hD : BivariateDerivation f D) {a b c d : ℕ}
    (h : Nat.Coprime (a * b) (c * d)) :
    D (a * c) (b * d) = D a b * f c d + f a b * D c d := hD.2 h

/-- **Two derivations of the same bivariate multiplicative function that agree on prime-power
pairs are equal.** -/
theorem BivariateDerivation.eq_of_prime_pow_eq
    {f D E : ℕ → ℕ → ℝ}
    (hD : BivariateDerivation f D) (hE : BivariateDerivation f E)
    (hlocal : ∀ {p : ℕ}, p.Prime → ∀ i j : ℕ,
      D (p ^ i) (p ^ j) = E (p ^ i) (p ^ j))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) : D m n = E m n := by
  induction hmn : m * n using Nat.strong_induction_on generalizing m n with
  | h k ih =>
      by_cases hk1 : k = 1
      · have hone : m * n = 1 := hmn.trans hk1
        have hm1 : m = 1 := by
          have hmle : m ≤ 1 := Nat.le_of_dvd (by omega) ⟨n, hone.symm⟩
          omega
        have hn1 : n = 1 := by
          have hndvd : n ∣ 1 := ⟨m, by
            calc
              1 = m * n := hone.symm
              _ = n * m := Nat.mul_comm _ _⟩
          have hnle : n ≤ 1 := Nat.le_of_dvd (by omega) hndvd
          omega
        subst m
        subst n
        rw [hD.one, hE.one]
      · obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd hk1
        let i : ℕ := m.factorization p
        let j : ℕ := n.factorization p
        let m' : ℕ := m / p ^ i
        let n' : ℕ := n / p ^ j
        have hm0 : m ≠ 0 := hm.ne'
        have hn0 : n ≠ 0 := hn.ne'
        have hm' : 0 < m' := Nat.ordCompl_pos p hm0
        have hn' : 0 < n' := Nat.ordCompl_pos p hn0
        have hmrec : p ^ i * m' = m := Nat.ordProj_mul_ordCompl_eq_self m p
        have hnrec : p ^ j * n' = n := Nat.ordProj_mul_ordCompl_eq_self n p
        have hij : 0 < i + j := by
          have hpk' : p ∣ m * n := by rw [hmn]; exact hpk
          rcases hp.dvd_mul.mp hpk' with hpm | hpn
          · have hi : 0 < i := hp.factorization_pos_of_dvd hm0 hpm
            omega
          · have hj : 0 < j := hp.factorization_pos_of_dvd hn0 hpn
            omega
        have hnot : ¬ p ∣ m' * n' := by
          intro hdiv
          rcases hp.dvd_mul.mp hdiv with hpm' | hpn'
          · exact Nat.not_dvd_ordCompl hp hm0 hpm'
          · exact Nat.not_dvd_ordCompl hp hn0 hpn'
        have hcop : Nat.Coprime (p ^ i * p ^ j) (m' * n') := by
          rw [← pow_add]
          exact (hp.coprime_iff_not_dvd.mpr hnot).pow_left (i + j)
        have hprod : (p ^ i * p ^ j) * (m' * n') = k := by
          rw [mul_mul_mul_comm, hmrec, hnrec, hmn]
        have hpPow : 1 < p ^ (i + j) := Nat.one_lt_pow (by omega) hp.one_lt
        have hremLt : m' * n' < k := by
          have hlt : 1 * (m' * n') < p ^ (i + j) * (m' * n') :=
            (Nat.mul_lt_mul_right (mul_pos hm' hn')).mpr hpPow
          have hprod' : p ^ (i + j) * (m' * n') = k := by
            rw [pow_add]
            exact hprod
          rw [one_mul, hprod'] at hlt
          exact hlt
        have hrem : D m' n' = E m' n' :=
          ih (m' * n') hremLt hm' hn' rfl
        calc
          D m n = D (p ^ i * m') (p ^ j * n') := by rw [hmrec, hnrec]
          _ = D (p ^ i) (p ^ j) * f m' n' + f (p ^ i) (p ^ j) * D m' n' :=
            hD.leibniz hcop
          _ = E (p ^ i) (p ^ j) * f m' n' + f (p ^ i) (p ^ j) * E m' n' := by
            rw [hlocal hp i j, hrem]
          _ = E (p ^ i * m') (p ^ j * n') := (hE.leibniz hcop).symm
          _ = E m n := by rw [hmrec, hnrec]

private theorem quotient_mul_quotient_eq' {a c x y : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hx : x ∣ a) (hy : y ∣ c) :
    (a * c) / (x * y) = (a / x) * (c / y) := by
  have hxpos : 0 < x := Nat.pos_of_dvd_of_pos hx ha
  have hypos : 0 < y := Nat.pos_of_dvd_of_pos hy hc
  apply Nat.div_eq_of_eq_mul_left (mul_pos hxpos hypos)
  calc
    a * c = ((a / x) * x) * ((c / y) * y) := by
      rw [Nat.div_mul_cancel hx, Nat.div_mul_cancel hy]
    _ = ((a / x) * (c / y)) * (x * y) := by ring

/-- **Leibniz rule for the product-divisor convolution.** -/
theorem BivariateDerivation.convolution
    {f g D E : ℕ → ℕ → ℝ}
    (hf : BivariateMultiplicative f) (hg : BivariateMultiplicative g)
    (hD : BivariateDerivation f D) (hE : BivariateDerivation g E) :
    BivariateDerivation (bivariateDirichletConvolution f g)
      (fun m n => bivariateDirichletConvolution D g m n +
        bivariateDirichletConvolution f E m n) := by
  constructor
  · let z0 : ({x // x ∈ (1 : ℕ).divisors} × {y // y ∈ (1 : ℕ).divisors}) :=
      ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩
    have hsingle : ∀ (u v : ℕ → ℕ → ℝ),
        bivariateDirichletConvolution u v 1 1 = u 1 1 * v 1 1 := by
      intro u v
      rw [bivariateDirichletConvolution, if_neg (by simp)]
      rw [Fintype.sum_eq_single z0]
      · simp [z0]
      · intro z hz
        exfalso
        apply hz
        apply Prod.ext <;> apply Subtype.ext
        · exact Nat.dvd_one.mp (Nat.dvd_of_mem_divisors z.1.2)
        · exact Nat.dvd_one.mp (Nat.dvd_of_mem_divisors z.2.2)
    show bivariateDirichletConvolution D g 1 1 +
      bivariateDirichletConvolution f E 1 1 = 0
    rw [hsingle D g, hsingle f E, hD.one, hE.one, hf.one]
    ring
  · intro a b c d h
    by_cases hab0 : a * b = 0
    · rcases Nat.mul_eq_zero.mp hab0 with rfl | rfl <;>
        simp [bivariateDirichletConvolution]
    by_cases hcd0 : c * d = 0
    · rcases Nat.mul_eq_zero.mp hcd0 with rfl | rfl <;>
        simp [bivariateDirichletConvolution]
    have ha : 0 < a := Nat.pos_of_ne_zero (fun hz => hab0 (by simp [hz]))
    have hb : 0 < b := Nat.pos_of_ne_zero (fun hz => hab0 (by simp [hz]))
    have hc : 0 < c := Nat.pos_of_ne_zero (fun hz => hcd0 (by simp [hz]))
    have hd : 0 < d := Nat.pos_of_ne_zero (fun hz => hcd0 (by simp [hz]))
    let e := pairCoprimeDivisorsEquiv ha.ne' hb.ne' hc.ne' hd.ne' h
    show bivariateDirichletConvolution D g (a * c) (b * d) +
        bivariateDirichletConvolution f E (a * c) (b * d) =
      (bivariateDirichletConvolution D g a b +
          bivariateDirichletConvolution f E a b) *
          bivariateDirichletConvolution f g c d +
        bivariateDirichletConvolution f g a b *
          (bivariateDirichletConvolution D g c d +
            bivariateDirichletConvolution f E c d)
    simp only [bivariateDirichletConvolution,
      if_neg (not_or_intro (Nat.mul_ne_zero ha.ne' hc.ne')
        (Nat.mul_ne_zero hb.ne' hd.ne')),
      if_neg (not_or_intro ha.ne' hb.ne'),
      if_neg (not_or_intro hc.ne' hd.ne')]
    have hcombine :
        (∑ z : ({x // x ∈ (a * c).divisors} × {y // y ∈ (b * d).divisors}),
            D z.1.1 z.2.1 * g ((a * c) / z.1.1) ((b * d) / z.2.1)) +
          (∑ z : ({x // x ∈ (a * c).divisors} × {y // y ∈ (b * d).divisors}),
            f z.1.1 z.2.1 * E ((a * c) / z.1.1) ((b * d) / z.2.1)) =
        ∑ q : (({x // x ∈ a.divisors} × {y // y ∈ b.divisors}) ×
            ({x // x ∈ c.divisors} × {y // y ∈ d.divisors})),
          ((D q.1.1.1 q.1.2.1 * g (a / q.1.1.1) (b / q.1.2.1) +
              f q.1.1.1 q.1.2.1 * E (a / q.1.1.1) (b / q.1.2.1)) *
            (f q.2.1.1 q.2.2.1 * g (c / q.2.1.1) (d / q.2.2.1)) +
          (f q.1.1.1 q.1.2.1 * g (a / q.1.1.1) (b / q.1.2.1)) *
            (D q.2.1.1 q.2.2.1 * g (c / q.2.1.1) (d / q.2.2.1) +
              f q.2.1.1 q.2.2.1 * E (c / q.2.1.1) (d / q.2.2.1))) := by
      rw [← e.sum_comp (fun z =>
          D z.1.1 z.2.1 * g ((a * c) / z.1.1) ((b * d) / z.2.1)),
        ← e.sum_comp (fun z =>
          f z.1.1 z.2.1 * E ((a * c) / z.1.1) ((b * d) / z.2.1)),
        ← Finset.sum_add_distrib]
      apply Fintype.sum_congr
      intro q
      have hx1 := Nat.dvd_of_mem_divisors q.1.1.2
      have hy1 := Nat.dvd_of_mem_divisors q.1.2.2
      have hx2 := Nat.dvd_of_mem_divisors q.2.1.2
      have hy2 := Nat.dvd_of_mem_divisors q.2.2.2
      have hfirst : Nat.Coprime (q.1.1.1 * q.1.2.1) (q.2.1.1 * q.2.2.1) :=
        h.of_dvd_left (mul_dvd_mul hx1 hy1) |>.of_dvd_right (mul_dvd_mul hx2 hy2)
      have hsecond : Nat.Coprime
          ((a / q.1.1.1) * (b / q.1.2.1))
          ((c / q.2.1.1) * (d / q.2.2.1)) :=
        h.of_dvd_left (mul_dvd_mul (Nat.div_dvd_of_dvd hx1) (Nat.div_dvd_of_dvd hy1))
          |>.of_dvd_right
            (mul_dvd_mul (Nat.div_dvd_of_dvd hx2) (Nat.div_dvd_of_dvd hy2))
      change D (q.1.1.1 * q.2.1.1) (q.1.2.1 * q.2.2.1) *
            g ((a * c) / (q.1.1.1 * q.2.1.1))
              ((b * d) / (q.1.2.1 * q.2.2.1)) +
          f (q.1.1.1 * q.2.1.1) (q.1.2.1 * q.2.2.1) *
            E ((a * c) / (q.1.1.1 * q.2.1.1))
              ((b * d) / (q.1.2.1 * q.2.2.1)) = _
      rw [quotient_mul_quotient_eq' ha hc hx1 hx2,
        quotient_mul_quotient_eq' hb hd hy1 hy2,
        hD.leibniz hfirst, hf.map_mul_of_pair_coprime hfirst,
        hg.map_mul_of_pair_coprime hsecond, hE.leibniz hsecond]
      ring
    rw [hcombine, Fintype.sum_prod_type]
    have hexpand : ∀ q1 : ({x // x ∈ a.divisors} × {y // y ∈ b.divisors}),
        (∑ q2 : ({x // x ∈ c.divisors} × {y // y ∈ d.divisors}),
          ((D q1.1.1 q1.2.1 * g (a / q1.1.1) (b / q1.2.1) +
              f q1.1.1 q1.2.1 * E (a / q1.1.1) (b / q1.2.1)) *
            (f q2.1.1 q2.2.1 * g (c / q2.1.1) (d / q2.2.1)) +
          (f q1.1.1 q1.2.1 * g (a / q1.1.1) (b / q1.2.1)) *
            (D q2.1.1 q2.2.1 * g (c / q2.1.1) (d / q2.2.1) +
              f q2.1.1 q2.2.1 * E (c / q2.1.1) (d / q2.2.1)))) =
        (D q1.1.1 q1.2.1 * g (a / q1.1.1) (b / q1.2.1) +
            f q1.1.1 q1.2.1 * E (a / q1.1.1) (b / q1.2.1)) *
          (∑ q2 : ({x // x ∈ c.divisors} × {y // y ∈ d.divisors}),
            f q2.1.1 q2.2.1 * g (c / q2.1.1) (d / q2.2.1)) +
        (f q1.1.1 q1.2.1 * g (a / q1.1.1) (b / q1.2.1)) *
          ((∑ q2 : ({x // x ∈ c.divisors} × {y // y ∈ d.divisors}),
            D q2.1.1 q2.2.1 * g (c / q2.1.1) (d / q2.2.1)) +
            ∑ q2 : ({x // x ∈ c.divisors} × {y // y ∈ d.divisors}),
              f q2.1.1 q2.2.1 * E (c / q2.1.1) (d / q2.2.1)) := by
      intro q1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun q1 _ => hexpand q1),
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
      Finset.sum_add_distrib]

end

end RHTower.Sieve
