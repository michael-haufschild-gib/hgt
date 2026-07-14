import GaloisForLFunctions.HTGeometry.MvPolynomialGradient
import GaloisForLFunctions.HTGeometry.FiniteRangeProjectiveTail

/-!
# The Shapiro--Sparer arithmetic-function Jacobian bridge

This module turns a full-rank finite prime-evaluation packet into genuine algebraic independence of
prime-supported arithmetic functions, via the classical Jacobian criterion.

The abstract engine is `algebraicIndependent_of_jacobian`: for a family `g` in a commutative algebra
over a characteristic-zero field, an invertible matrix of *scalar* derivative values
`Dᵢ(gⱼ) = algebraMap (M i j)` forces algebraic independence.  The proof applies each derivation to a
minimal-degree polynomial relation, uses the multivariate chain rule to convert it into a linear
system on the evaluated gradient, inverts the matrix, and contradicts minimality through the strictly
degree-lowering partial derivative.

The concrete engine is the prime derivation on the Dirichlet-convolution algebra
`𝒜 = ArithmeticFunction ℂ`,
\[(\partial_q b)(n)=v_q(nq)\,b(nq),\]
a genuine derivation whose value on a prime-supported function reads off `b(q)` on the identity
component `n = 1`, so that `∂_q b = b q • 1`.  Feeding the evaluation packet
`TailCoefficientIndependent.exists_fullRank_evaluation_packet` into the abstract criterion produces
algebraic independence of any finite prime-supported family whose evaluation matrix is invertible.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial ArithmeticFunction Finset

noncomputable section

/-! ## The abstract derivation-Jacobian criterion -/

section AbstractCriterion

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Ring-level multivariate chain rule for a family of additive, Leibniz, constant-killing maps. -/
theorem jacobian_aeval_eq_sum_pderiv
    (D : R → R) (hadd : ∀ a b, D (a + b) = D a + D b)
    (hleib : ∀ a b, D (a * b) = a * D b + b * D a)
    (hconst : ∀ c : K, D (algebraMap K R c) = 0)
    (g : Fin N → R) (P : MvPolynomial (Fin N) K) :
    D (MvPolynomial.aeval g P) =
      ∑ j, MvPolynomial.aeval g (MvPolynomial.pderiv j P) * D (g j) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [hconst]
  | add P Q hP hQ =>
      rw [map_add, hadd, hP, hQ, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_add (MvPolynomial.pderiv j), map_add (MvPolynomial.aeval g), add_mul]
  | mul_X P k hP =>
      rw [map_mul (MvPolynomial.aeval g) P (MvPolynomial.X k), MvPolynomial.aeval_X,
        hleib, hP, Finset.mul_sum]
      symm
      rw [show (∑ j, MvPolynomial.aeval g (MvPolynomial.pderiv j (P * MvPolynomial.X k)) * D (g j))
          = ∑ j, (MvPolynomial.aeval g (MvPolynomial.pderiv j P) * D (g j) * g k
            + (if j = k then MvPolynomial.aeval g P * D (g j) else 0)) from ?_]
      · rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ k
            (fun j => MvPolynomial.aeval g P * D (g j)), if_pos (Finset.mem_univ k)]
        rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro j _; ring
      · apply Finset.sum_congr rfl
        intro j _
        by_cases h : j = k
        · subst h
          rw [MvPolynomial.pderiv_mul, map_add, MvPolynomial.pderiv_X, Pi.single_eq_same,
            map_mul, MvPolynomial.aeval_X, mul_one, add_mul, if_pos rfl]
          ring
        · rw [MvPolynomial.pderiv_mul, map_add, MvPolynomial.pderiv_X,
            Pi.single_eq_of_ne (Ne.symm h), mul_zero, _root_.map_zero, add_zero,
            map_mul, MvPolynomial.aeval_X, if_neg h, add_zero]

/-- If a matrix over `K` is a unit and every `K`-combination `∑ⱼ Mᵢⱼ • wⱼ` vanishes, then `w = 0`. -/
theorem vec_zero_of_isUnit_smul
    (M : Matrix ι ι K) (hM : IsUnit M) (w : ι → R)
    (h : ∀ i, ∑ j, M i j • w j = 0) : ∀ j, w j = 0 := by
  classical
  obtain ⟨u, hu⟩ := hM
  set Ninv : Matrix ι ι K := ↑u⁻¹ with hNinv
  have hNM : Ninv * M = 1 := by rw [hNinv, ← hu]; exact u.inv_mul
  intro j
  have key : w j = ∑ k, Ninv j k • (∑ l, M k l • w l) := by
    calc w j = ∑ l, (1 : Matrix ι ι K) j l • w l := by
              rw [Finset.sum_eq_single j]
              · simp
              · intro l _ hl; simp [Ne.symm hl]
              · intro hj; exact absurd (Finset.mem_univ j) hj
      _ = ∑ l, (Ninv * M) j l • w l := by rw [hNM]
      _ = ∑ l, (∑ k, Ninv j k * M k l) • w l := by
              apply Finset.sum_congr rfl; intro l _; rw [Matrix.mul_apply]
      _ = ∑ l, ∑ k, (Ninv j k * M k l) • w l := by
              apply Finset.sum_congr rfl; intro l _; rw [Finset.sum_smul]
      _ = ∑ k, ∑ l, (Ninv j k * M k l) • w l := Finset.sum_comm
      _ = ∑ k, Ninv j k • (∑ l, M k l • w l) := by
              apply Finset.sum_congr rfl; intro k _
              rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro l _
              rw [mul_smul]
  rw [key]
  apply Finset.sum_eq_zero
  intro k _
  rw [h k, smul_zero]

/-- **Derivation-Jacobian criterion.**  A finite family with an invertible Jacobian of scalar
derivatives is algebraically independent over the base field.  `D i` is any additive, Leibniz,
constant-killing map. -/
theorem algebraicIndependent_of_jacobian [CharZero K] [Nontrivial R]
    (g : ι → R) (D : ι → (R → R))
    (hadd : ∀ i a b, D i (a + b) = D i a + D i b)
    (hleib : ∀ i a b, D i (a * b) = a * D i b + b * D i a)
    (hconst : ∀ i (c : K), D i (algebraMap K R c) = 0)
    (M : Matrix ι ι K) (hM : IsUnit M)
    (hDg : ∀ i j, D i (g j) = algebraMap K R (M i j)) :
    AlgebraicIndependent K g := by
  classical
  rw [algebraicIndependent_iff_ker_eq_bot]
  by_contra hker
  obtain ⟨P, hPI, hP0, hmin⟩ :=
    GaloisForLFunctions.Ideal.exists_minimal_mvPolynomial_totalDegree_ne_zero hker
  have hPeval : MvPolynomial.aeval g P = 0 := RingHom.mem_ker.mp hPI
  have hjac : ∀ i, ∑ j, M i j • MvPolynomial.aeval g (MvPolynomial.pderiv j P) = 0 := by
    intro i
    have hchain := jacobian_aeval_eq_sum_pderiv (D i) (hadd i) (hleib i) (hconst i) g P
    have hD0 : D i 0 = 0 := by
      have h := hadd i 0 0; simp only [add_zero] at h; exact self_eq_add_right.mp h
    rw [hPeval, hD0] at hchain
    calc ∑ j, M i j • MvPolynomial.aeval g (MvPolynomial.pderiv j P)
        = ∑ j, MvPolynomial.aeval g (MvPolynomial.pderiv j P) * D i (g j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hDg i j, Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one]
      _ = 0 := hchain.symm
  have hpder0 : ∀ j, MvPolynomial.aeval g (MvPolynomial.pderiv j P) = 0 :=
    vec_zero_of_isUnit_smul M hM
      (fun j => MvPolynomial.aeval g (MvPolynomial.pderiv j P)) hjac
  have hPvars : P.vars.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hvars
    have hPC := MvPolynomial.vars_eq_empty_iff_eq_C.mp hvars
    rw [hPC] at hPeval hP0
    have hcmap : algebraMap K R (P.coeff 0) = 0 := by simpa using hPeval
    have hc : P.coeff 0 = 0 := FaithfulSMul.algebraMap_injective K R (by simpa using hcmap)
    exact hP0 (by simp [hc])
  obtain ⟨i, hi⟩ := hPvars
  obtain ⟨s, hsP, his⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hi
  have hpderiv0 : MvPolynomial.pderiv i P ≠ 0 :=
    GaloisForLFunctions.pderiv_ne_zero_of_mem_support hsP his
  have hpI : MvPolynomial.pderiv i P ∈ RingHom.ker (MvPolynomial.aeval g).toRingHom :=
    RingHom.mem_ker.mpr (hpder0 i)
  have hle := hmin hpI hpderiv0
  have hlt := GaloisForLFunctions.totalDegree_pderiv_lt P i hpderiv0
  exact (not_lt_of_ge hle) hlt

end AbstractCriterion

/-! ## The prime derivation on arithmetic functions -/

/-- `ArithmeticFunction ℂ` is nontrivial: the identity differs from zero at `1`. -/
instance : Nontrivial (ArithmeticFunction ℂ) :=
  ⟨1, 0, by
    intro h
    have := congrArg (fun f : ArithmeticFunction ℂ => f 1) h
    simp [ArithmeticFunction.one_apply] at this⟩

/-- The prime derivation `(∂_q b)(n) = v_q(nq) b(nq)` on the Dirichlet-convolution algebra. -/
def primeDeriv (q : ℕ) (b : ArithmeticFunction ℂ) : ArithmeticFunction ℂ where
  toFun n := ((n * q).factorization q : ℂ) * b (n * q)
  map_zero' := by simp

@[simp] theorem primeDeriv_apply (q : ℕ) (b : ArithmeticFunction ℂ) (n : ℕ) :
    primeDeriv q b n = ((n * q).factorization q : ℂ) * b (n * q) := rfl

theorem primeDeriv_add (q : ℕ) (b c : ArithmeticFunction ℂ) :
    primeDeriv q (b + c) = primeDeriv q b + primeDeriv q c := by
  ext n
  simp [mul_add]

/-- `n * q ≠ 1` for a prime `q`. -/
theorem mul_prime_ne_one {q : ℕ} (hq : q.Prime) (n : ℕ) : n * q ≠ 1 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · have : q ≤ n * q := Nat.le_mul_of_pos_left q hn
    have := hq.two_le
    omega

theorem primeDeriv_algebraMap (q : ℕ) (hq : q.Prime) (c : ℂ) :
    primeDeriv q (algebraMap ℂ (ArithmeticFunction ℂ) c) = 0 := by
  ext n
  rw [primeDeriv_apply, ArithmeticFunction.zero_apply, Algebra.algebraMap_eq_smul_one,
    ArithmeticFunction.smul_apply, ArithmeticFunction.one_apply,
    if_neg (mul_prime_ne_one hq n)]
  simp

/-- The single-coordinate weight identity underlying Leibniz: for `n ≥ 1`,
`∑_{ad=nq} (v_q d) F(a,d) = ∑_{ef=n} (v_q(fq)) F(e, fq)`, obtained by discarding the terms with
`q ∤ d` and reindexing `(e,f) ↦ (e, fq)`. -/
theorem sum_factorization_snd_reindex (q : ℕ) (hq : q.Prime) {n : ℕ} (hn : n ≠ 0)
    (F : ℕ → ℕ → ℂ) :
    ∑ x ∈ (n * q).divisorsAntidiagonal, ((x.2.factorization q : ℂ)) * F x.1 x.2 =
      ∑ y ∈ n.divisorsAntidiagonal, (((y.2 * q).factorization q : ℂ)) * F y.1 (y.2 * q) := by
  classical
  have hnq : n * q ≠ 0 := by
    have := hq.pos; exact Nat.mul_ne_zero hn (by omega)
  -- restrict the left sum to the terms with `q ∣ x.2`
  have hfilter : ∑ x ∈ (n * q).divisorsAntidiagonal, ((x.2.factorization q : ℂ)) * F x.1 x.2 =
      ∑ x ∈ (n * q).divisorsAntidiagonal.filter (fun x => q ∣ x.2),
        ((x.2.factorization q : ℂ)) * F x.1 x.2 := by
    rw [Finset.sum_filter_of_ne]
    intro x _ hxne
    by_contra hnd
    apply hxne
    rw [Nat.factorization_eq_zero_of_not_dvd hnd]
    simp
  rw [hfilter]
  refine (Finset.sum_bij' (fun y _ => (y.1, y.2 * q)) (fun x _ => (x.1, x.2 / q)) ?_ ?_ ?_ ?_ ?_).symm
  · -- image lands in filtered set
    intro x hx
    rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨⟨hprod, _⟩, hdvd⟩ := hx
    rw [Nat.mem_divisorsAntidiagonal]
    refine ⟨?_, hn⟩
    obtain ⟨k, hk⟩ := hdvd
    have hx2 : x.2 / q = k := by rw [hk]; exact Nat.mul_div_cancel_left k hq.pos
    rw [hx2]
    have : x.1 * (k * q) = n * q := by rw [← hk]; exact hprod
    have hq0 : q ≠ 0 := by omega
    exact Nat.eq_of_mul_eq_mul_right hq.pos (by rw [← this]; ring)
  · -- forward map lands in filtered set
    intro y hy
    rw [Nat.mem_divisorsAntidiagonal] at hy
    obtain ⟨hprod, _⟩ := hy
    rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    refine ⟨⟨?_, hnq⟩, ⟨y.2, rfl⟩⟩
    rw [← hprod]; ring
  · -- left inverse
    intro y hy
    rw [Nat.mem_divisorsAntidiagonal] at hy
    have : y.2 * q / q = y.2 := Nat.mul_div_cancel y.2 hq.pos
    simp [this]
  · -- right inverse
    intro x hx
    rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨_, hdvd⟩ := hx
    have : x.2 / q * q = x.2 := Nat.div_mul_cancel hdvd
    simp [this]
  · -- integrand agreement
    intro y _
    rfl

/-- **Leibniz rule** for the prime derivation with respect to Dirichlet convolution. -/
theorem primeDeriv_mul (q : ℕ) (hq : q.Prime) (b c : ArithmeticFunction ℂ) :
    primeDeriv q (b * c) = b * primeDeriv q c + c * primeDeriv q b := by
  classical
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hn0 : n ≠ 0 := by omega
  have hnq0 : n * q ≠ 0 := Nat.mul_ne_zero hn0 hq.ne_zero
  rw [primeDeriv_apply, ArithmeticFunction.add_apply, ArithmeticFunction.mul_apply,
    ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  -- expand the constant factorization weight over the antidiagonal and split
  rw [Finset.mul_sum]
  have hsplit : ∀ x ∈ (n * q).divisorsAntidiagonal,
      ((n * q).factorization q : ℂ) * (b x.1 * c x.2)
        = ((x.1.factorization q : ℂ)) * (b x.1 * c x.2)
          + ((x.2.factorization q : ℂ)) * (b x.1 * c x.2) := by
    intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨hprod, _⟩ := hx
    have ha : x.1 ≠ 0 := by rintro h; rw [h, zero_mul] at hprod; exact hnq0 hprod.symm
    have hb2 : x.2 ≠ 0 := by rintro h; rw [h, mul_zero] at hprod; exact hnq0 hprod.symm
    have : (n * q).factorization q = x.1.factorization q + x.2.factorization q := by
      rw [← hprod, Nat.factorization_mul ha hb2]; rfl
    rw [this]
    push_cast
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
  -- identify the two halves
  have hhalf2 : ∑ x ∈ (n * q).divisorsAntidiagonal,
      ((x.2.factorization q : ℂ)) * (b x.1 * c x.2)
      = ∑ y ∈ n.divisorsAntidiagonal, b y.1 * (primeDeriv q c y.2) := by
    rw [sum_factorization_snd_reindex q hq hn0 (fun a d => b a * c d)]
    apply Finset.sum_congr rfl
    intro y _
    rw [primeDeriv_apply]; ring
  have hhalf1 : ∑ x ∈ (n * q).divisorsAntidiagonal,
      ((x.1.factorization q : ℂ)) * (b x.1 * c x.2)
      = ∑ y ∈ n.divisorsAntidiagonal, c y.1 * (primeDeriv q b y.2) := by
    -- swap the antidiagonal to reduce to the second-coordinate identity
    rw [← Nat.map_swap_divisorsAntidiagonal, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, Prod.swap]
    rw [sum_factorization_snd_reindex q hq hn0 (fun a d => b d * c a)]
    rw [← Nat.map_swap_divisorsAntidiagonal, Finset.sum_map]
    simp only [Function.Embedding.coeFn_mk, Prod.swap]
    apply Finset.sum_congr rfl
    intro y _
    rw [primeDeriv_apply]; ring
  rw [hhalf1, hhalf2]
  ring

/-- The prime derivation reads off the value at `q` on prime-supported inputs: `∂_q b = b q • 1`. -/
theorem primeDeriv_prime_supported (q : ℕ) (hq : q.Prime) (b : ArithmeticFunction ℂ)
    (hb : ∀ m, b m ≠ 0 → m.Prime) : primeDeriv q b = b q • 1 := by
  ext n
  rw [primeDeriv_apply, ArithmeticFunction.smul_apply, ArithmeticFunction.one_apply]
  by_cases hn : n = 1
  · subst hn
    have hqf : (1 * q).factorization q = 1 := by
      rw [one_mul]; exact hq.factorization_self
    rw [hqf]
    simp
  · rw [if_neg hn, smul_zero]
    by_cases hbnq : b (n * q) = 0
    · rw [hbnq, mul_zero]
    · exfalso
      have hprime : (n * q).Prime := hb (n * q) hbnq
      have hdvd : q ∣ n * q := ⟨n, by ring⟩
      rcases (hprime.eq_one_or_self_of_dvd q hdvd) with h1 | hself
      · exact hq.ne_one h1
      · -- q = n * q, so n = 1
        have : 1 * q = n * q := by rw [one_mul]; exact hself
        exact hn (Nat.eq_of_mul_eq_mul_right hq.pos this).symm

/-! ## The evaluation-packet bridge -/

/-- **Shapiro--Sparer arithmetic-function Jacobian bridge.**  A finite family of prime-supported
arithmetic functions with an invertible prime-evaluation matrix is algebraically independent over
`ℂ`.  The primes `q i` play the role of the derivation directions and the evaluation matrix is the
eval-at-1 Jacobian. -/
theorem algebraicIndependent_of_evaluation_packet
    {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ArithmeticFunction ℂ)
    (hg : ∀ j m, g j m ≠ 0 → m.Prime)
    (q : ι → ℕ) (hq : ∀ i, (q i).Prime)
    (hM : IsUnit (Matrix.of (fun i j => g j (q i)) : Matrix ι ι ℂ)) :
    AlgebraicIndependent ℂ g := by
  refine algebraicIndependent_of_jacobian (K := ℂ) g (fun i => primeDeriv (q i))
    (fun i => primeDeriv_add (q i))
    (fun i => primeDeriv_mul (q i) (hq i))
    (fun i c => primeDeriv_algebraMap (q i) (hq i) c)
    (Matrix.of (fun i j => g j (q i))) hM ?_
  intro i j
  rw [primeDeriv_prime_supported (q i) (hq i) (g j) (fun m => hg j m),
    Algebra.algebraMap_eq_smul_one]
  rfl

/-! ## Realizing prime coefficient columns as arithmetic functions -/

/-- The prime-supported arithmetic function carrying a coefficient column `a : Nat.Primes → ℂ`. -/
def arithmeticOfPrimeColumn (a : Nat.Primes → ℂ) : ArithmeticFunction ℂ where
  toFun n := if h : n.Prime then a ⟨n, h⟩ else 0
  map_zero' := by simp [Nat.not_prime_zero]

theorem arithmeticOfPrimeColumn_apply_prime (a : Nat.Primes → ℂ) (p : Nat.Primes) :
    arithmeticOfPrimeColumn a (p : ℕ) = a p := by
  show (if h : (p : ℕ).Prime then a ⟨(p : ℕ), h⟩ else 0) = a p
  rw [dif_pos p.2]

theorem arithmeticOfPrimeColumn_support (a : Nat.Primes → ℂ) {m : ℕ}
    (hm : arithmeticOfPrimeColumn a m ≠ 0) : m.Prime := by
  by_contra hnp
  exact hm (by show (if h : m.Prime then a ⟨m, h⟩ else 0) = 0; rw [dif_neg hnp])

/-- **Rectangle algebraic independence from tail rank.**  Consuming
`TailCoefficientIndependent.exists_fullRank_evaluation_packet`, a tail-independent finite family of
prime coefficient columns realizes as algebraically independent arithmetic functions.  This is the
Jacobian conversion of a full tail rank into genuine algebraic independence. -/
theorem algebraicIndependent_arithmeticColumns_of_tailIndependent
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → Nat.Primes → ℂ) (h : TailCoefficientIndependent a) :
    AlgebraicIndependent ℂ (fun i => arithmeticOfPrimeColumn (a i)) := by
  obtain ⟨points, hpacket⟩ :=
    TailCoefficientIndependent.exists_fullRank_evaluation_packet a h
  refine algebraicIndependent_of_evaluation_packet
    (fun i => arithmeticOfPrimeColumn (a i))
    (fun j m hm => arithmeticOfPrimeColumn_support (a j) hm)
    (fun i => (points i : ℕ))
    (fun i => (points i).2) ?_
  have hcast : (Matrix.of (fun i j => arithmeticOfPrimeColumn (a j) (points i : ℕ))
      : Matrix I I ℂ)
      = Matrix.of (fun row i => a i (points row)) := by
    ext i j
    simp only [Matrix.of_apply]
    exact arithmeticOfPrimeColumn_apply_prime (a j) (points i)
  rw [hcast]
  exact hpacket

/-- The prime derivation annihilates every finite-prime-support arithmetic function whose prime
support avoids `q`.  This is the mechanism that upgrades independence over `ℂ` to independence over
the finite-prime coefficient algebra: such coefficients lie in the common kernel of the chosen
derivations. -/
theorem primeDeriv_eq_zero_of_not_dvd_support (q : ℕ)
    (b : ArithmeticFunction ℂ) (hb : ∀ m, b m ≠ 0 → ¬ q ∣ m) :
    primeDeriv q b = 0 := by
  ext n
  rw [primeDeriv_apply, ArithmeticFunction.zero_apply]
  by_cases hbnq : b (n * q) = 0
  · rw [hbnq, mul_zero]
  · exact absurd ⟨n, by ring⟩ (hb (n * q) hbnq)

end

end GaloisForLFunctions.HTGeometry
