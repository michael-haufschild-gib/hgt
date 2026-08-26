import GaloisForLFunctions.RHTower.Sieve.SelbergEulerCorrectionWeight

open ArithmeticFunction Finset
open scoped BigOperators ArithmeticFunction.Moebius

/-!
# Bivariate multiplicative arithmetic-function infrastructure

This module supplies the product-divisor analogue of ordinary multiplicative arithmetic functions:

* pair-coprime multiplicativity;
* unique divisor splitting across pair-coprime products;
* bivariate Dirichlet convolution and its multiplicativity;
* determination by simultaneous prime-power pairs.

The machinery lets a local two-variable Euler-factor identity propagate to every positive integer
pair without analytic uniqueness arguments.
-/

namespace RHTower.Sieve

noncomputable section

def BivariateMultiplicative {R : Type*} [CommMonoid R]
    (f : ℕ → ℕ → R) : Prop :=
  f 1 1 = 1 ∧
    ∀ {a b c d : ℕ}, Nat.Coprime (a * b) (c * d) →
      f (a * c) (b * d) = f a b * f c d

theorem BivariateMultiplicative.one {R : Type*} [CommMonoid R]
    {f : ℕ → ℕ → R} (hf : BivariateMultiplicative f) : f 1 1 = 1 := hf.1

theorem BivariateMultiplicative.map_mul_of_pair_coprime {R : Type*} [CommMonoid R]
    {f : ℕ → ℕ → R} (hf : BivariateMultiplicative f)
    {a b c d : ℕ} (h : Nat.Coprime (a * b) (c * d)) :
    f (a * c) (b * d) = f a b * f c d := hf.2 h

/-- Divisors of a coprime product split uniquely into divisors of its two factors. -/
def coprimeDivisorsEquiv {a c : ℕ} (ha : a ≠ 0) (hc : c ≠ 0)
    (h : Nat.Coprime a c) :
    ({x // x ∈ a.divisors} × {y // y ∈ c.divisors}) ≃
      {z // z ∈ (a * c).divisors} where
  toFun xy := ⟨xy.1.1 * xy.2.1, by
    rw [Nat.mem_divisors]
    refine ⟨mul_dvd_mul (Nat.dvd_of_mem_divisors xy.1.2)
      (Nat.dvd_of_mem_divisors xy.2.2), Nat.mul_ne_zero ha hc⟩⟩
  invFun z := by
    let x := Nat.gcd z.1 a
    let y := Nat.gcd z.1 c
    have hzD : z.1 ∣ a * c := Nat.dvd_of_mem_divisors z.2
    have hz0 : z.1 ≠ 0 := by
      intro hz
      have hzero : 0 ∣ a * c := by simpa [hz] using hzD
      exact Nat.mul_ne_zero ha hc (Nat.eq_zero_of_zero_dvd hzero)
    have hxy : x * y = z.1 := by
      dsimp [x, y]
      rw [← h.gcd_mul z.1, Nat.gcd_eq_left_iff_dvd.mpr hzD]
    have hx0 : x ≠ 0 := by
      intro hx
      rw [hx, zero_mul] at hxy
      exact hz0 hxy.symm
    have hy0 : y ≠ 0 := by
      intro hy
      rw [hy, mul_zero] at hxy
      exact hz0 hxy.symm
    exact ⟨⟨x, Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, ha⟩⟩,
      ⟨y, Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hc⟩⟩⟩
  left_inv xy := by
    apply Prod.ext
    · apply Subtype.ext
      have hyc : Nat.Coprime xy.2.1 a :=
        (h.of_dvd_right (Nat.dvd_of_mem_divisors xy.2.2)).symm
      calc
        Nat.gcd (xy.1.1 * xy.2.1) a = Nat.gcd (xy.2.1 * xy.1.1) a := by
          rw [Nat.mul_comm]
        _ = Nat.gcd xy.1.1 a := hyc.gcd_mul_left_cancel xy.1.1
        _ = xy.1.1 := Nat.gcd_eq_left_iff_dvd.mpr
          (Nat.dvd_of_mem_divisors xy.1.2)
    · apply Subtype.ext
      have hxa : Nat.Coprime xy.1.1 c :=
        h.of_dvd_left (Nat.dvd_of_mem_divisors xy.1.2)
      calc
        Nat.gcd (xy.1.1 * xy.2.1) c = Nat.gcd xy.2.1 c :=
          hxa.gcd_mul_left_cancel xy.2.1
        _ = xy.2.1 := Nat.gcd_eq_left_iff_dvd.mpr
          (Nat.dvd_of_mem_divisors xy.2.2)
  right_inv z := by
    apply Subtype.ext
    calc
      Nat.gcd z.1 a * Nat.gcd z.1 c = Nat.gcd z.1 (a * c) :=
        (h.gcd_mul z.1).symm
      _ = z.1 := Nat.gcd_eq_left_iff_dvd.mpr (Nat.dvd_of_mem_divisors z.2)

private theorem quotient_mul_quotient_eq {a c x y : ℕ}
    (ha : 0 < a) (hc : 0 < c) (hx : x ∣ a) (hy : y ∣ c) :
    (a * c) / (x * y) = (a / x) * (c / y) := by
  have hxpos : 0 < x := Nat.pos_of_dvd_of_pos hx ha
  have hypos : 0 < y := Nat.pos_of_dvd_of_pos hy hc
  apply Nat.div_eq_of_eq_mul_left (mul_pos hxpos hypos)
  calc
    a * c = ((a / x) * x) * ((c / y) * y) := by
      rw [Nat.div_mul_cancel hx, Nat.div_mul_cancel hy]
    _ = ((a / x) * (c / y)) * (x * y) := by ring

/-- Componentwise divisor splitting for a pair-coprime product of integer pairs. -/
def pairCoprimeDivisorsEquiv {a b c d : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (h : Nat.Coprime (a * b) (c * d)) :
    (({x // x ∈ a.divisors} × {y // y ∈ b.divisors}) ×
      ({x // x ∈ c.divisors} × {y // y ∈ d.divisors})) ≃
      ({x // x ∈ (a * c).divisors} × {y // y ∈ (b * d).divisors}) := by
  have hac : Nat.Coprime a c :=
    (h.of_dvd_left (dvd_mul_right a b)).of_dvd_right (dvd_mul_right c d)
  have hbd : Nat.Coprime b d :=
    (h.of_dvd_left (dvd_mul_left b a)).of_dvd_right (dvd_mul_left d c)
  let ea := coprimeDivisorsEquiv ha hc hac
  let eb := coprimeDivisorsEquiv hb hd hbd
  exact
    { toFun := fun q => ⟨ea ⟨q.1.1, q.2.1⟩, eb ⟨q.1.2, q.2.2⟩⟩
      invFun := fun z =>
        ⟨⟨(ea.symm z.1).1, (eb.symm z.2).1⟩,
          ⟨(ea.symm z.1).2, (eb.symm z.2).2⟩⟩
      left_inv := by
        intro q
        apply Prod.ext <;> apply Prod.ext <;> simp [ea, eb]
      right_inv := by
        intro z
        apply Prod.ext <;> simp [ea, eb] }

/-- Dirichlet convolution on the product divisor lattice. -/
def bivariateDirichletConvolution {R : Type*} [CommSemiring R]
    (f g : ℕ → ℕ → R) (m n : ℕ) : R :=
  if m = 0 ∨ n = 0 then 0 else
    ∑ xy : ({x // x ∈ m.divisors} × {y // y ∈ n.divisors}),
      f xy.1.1 xy.2.1 * g (m / xy.1.1) (n / xy.2.1)

/-- Product-divisor convolution preserves bivariate multiplicativity. -/
theorem BivariateMultiplicative.convolution {R : Type*} [CommSemiring R]
    {f g : ℕ → ℕ → R}
    (hf : BivariateMultiplicative f) (hg : BivariateMultiplicative g) :
    BivariateMultiplicative (bivariateDirichletConvolution f g) := by
  constructor
  · let z0 : ({x // x ∈ (1 : ℕ).divisors} × {y // y ∈ (1 : ℕ).divisors}) :=
        ⟨⟨1, by simp⟩, ⟨1, by simp⟩⟩
    rw [bivariateDirichletConvolution, if_neg (by simp)]
    rw [Fintype.sum_eq_single z0]
    · simp [z0, hf.one, hg.one]
    · intro z hz
      exfalso
      apply hz
      apply Prod.ext <;> apply Subtype.ext
      · exact Nat.dvd_one.mp (Nat.dvd_of_mem_divisors z.1.2)
      · exact Nat.dvd_one.mp (Nat.dvd_of_mem_divisors z.2.2)
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
    simp only [bivariateDirichletConvolution,
      if_neg (not_or_intro (Nat.mul_ne_zero ha.ne' hc.ne')
        (Nat.mul_ne_zero hb.ne' hd.ne')),
      if_neg (not_or_intro ha.ne' hb.ne'),
      if_neg (not_or_intro hc.ne' hd.ne')]
    calc
      (∑ z : ({x // x ∈ (a * c).divisors} × {y // y ∈ (b * d).divisors}),
          f z.1.1 z.2.1 * g ((a * c) / z.1.1) ((b * d) / z.2.1)) =
          ∑ q : (({x // x ∈ a.divisors} × {y // y ∈ b.divisors}) ×
            ({x // x ∈ c.divisors} × {y // y ∈ d.divisors})),
            f (e q).1.1 (e q).2.1 *
              g ((a * c) / (e q).1.1) ((b * d) / (e q).2.1) := by
            exact (e.sum_comp (fun z =>
              f z.1.1 z.2.1 * g ((a * c) / z.1.1) ((b * d) / z.2.1))).symm
      _ = ∑ q : (({x // x ∈ a.divisors} × {y // y ∈ b.divisors}) ×
            ({x // x ∈ c.divisors} × {y // y ∈ d.divisors})),
          (f q.1.1.1 q.1.2.1 * g (a / q.1.1.1) (b / q.1.2.1)) *
            (f q.2.1.1 q.2.2.1 * g (c / q.2.1.1) (d / q.2.2.1)) := by
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
        change f (q.1.1.1 * q.2.1.1) (q.1.2.1 * q.2.2.1) *
            g ((a * c) / (q.1.1.1 * q.2.1.1))
              ((b * d) / (q.1.2.1 * q.2.2.1)) = _
        rw [quotient_mul_quotient_eq ha hc hx1 hx2,
          quotient_mul_quotient_eq hb hd hy1 hy2,
          hf.map_mul_of_pair_coprime hfirst,
          hg.map_mul_of_pair_coprime hsecond]
        ring
      _ = (∑ xy : ({x // x ∈ a.divisors} × {y // y ∈ b.divisors}),
            f xy.1.1 xy.2.1 * g (a / xy.1.1) (b / xy.2.1)) *
          ∑ xy : ({x // x ∈ c.divisors} × {y // y ∈ d.divisors}),
            f xy.1.1 xy.2.1 * g (c / xy.1.1) (d / xy.2.1) := by
        rw [Fintype.sum_prod_type]
        exact (Fintype.sum_mul_sum
          (fun xy : ({x // x ∈ a.divisors} × {y // y ∈ b.divisors}) =>
            f xy.1.1 xy.2.1 * g (a / xy.1.1) (b / xy.2.1))
          (fun xy : ({x // x ∈ c.divisors} × {y // y ∈ d.divisors}) =>
            f xy.1.1 xy.2.1 * g (c / xy.1.1) (d / xy.2.1))).symm

/-- Bivariate multiplicative functions are determined on positive arguments by their values on
simultaneous prime-power pairs. -/
theorem BivariateMultiplicative.eq_of_prime_pow_eq
    {R : Type*} [CommMonoid R]
    {f g : ℕ → ℕ → R}
    (hf : BivariateMultiplicative f) (hg : BivariateMultiplicative g)
    (hlocal : ∀ {p : ℕ}, p.Prime → ∀ i j : ℕ,
      f (p ^ i) (p ^ j) = g (p ^ i) (p ^ j))
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) : f m n = g m n := by
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
        rw [hf.one, hg.one]
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
        have hrem : f m' n' = g m' n' :=
          ih (m' * n') hremLt hm' hn' rfl
        calc
          f m n = f (p ^ i * m') (p ^ j * n') := by rw [hmrec, hnrec]
          _ = f (p ^ i) (p ^ j) * f m' n' := hf.map_mul_of_pair_coprime hcop
          _ = g (p ^ i) (p ^ j) * g m' n' := by rw [hlocal hp i j, hrem]
          _ = g (p ^ i * m') (p ^ j * n') :=
            (hg.map_mul_of_pair_coprime hcop).symm
          _ = g m n := by rw [hmrec, hnrec]

end

end RHTower.Sieve
