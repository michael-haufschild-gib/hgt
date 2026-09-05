import GaloisForLFunctions.RHTower.MollifiedDeviationHeadVariance
import GaloisForLFunctions.RHTower.Sieve.DirichletBilinear

/-!
# The fourth moment of the head of `ζΨ − 1`: the first Gaussian-moment law

The head `H_M(1/2 + it) = (1/log M) ∑_{k ≤ M} Λ(k) k^{-1/2-it}` of the mollified deviation is a
Dirichlet polynomial supported on prime powers.  Its fourth moment is the mean square of the
Dirichlet polynomial `H_M²`, whose coefficients are the Dirichlet self-convolution of the head
coefficients; by the Dirichlet mean value theorem this is the coefficient energy
`S₄(M) = ∑_r |(a ∗ a)_r|²` up to an error `O(M² log M · S₄ / (T₂ − T₁))`, negligible exactly when
the mollifier length satisfies `M² log M = o(T)`, i.e. `θ < 1/2`.

Unique factorization evaluates `S₄`: the solutions of `k₁k₂ = l₁l₂` in prime powers are the two
orientations `(l₁,l₂) ∈ {(k₁,k₂),(k₂,k₁)}`, except when all four are powers of one prime.  The
orientations contribute `2 S₂(M)² − ∑ a_k⁴` with `S₂(M) → 1/2` (the head variance law), and the
one-prime exceptions are `O(1/log⁴ M)`.  Hence

```text
(1/(T₂−T₁)) ∫_{T₁}^{T₂} |H_M(1/2+it)|⁴ dt → 1/2 = 2 · (1/2)²,
```

the fourth moment of the circular complex Gaussian `CN(0, 1/2)`: the head is Gaussian to fourth
order.  No zero, ordinate, or RH premise enters any statement.
-/

open ArithmeticFunction Finset Filter Topology

namespace RHTower

noncomputable section

/-! ## Real head coefficients and their self-convolution -/

/-- Real head coefficient `a_k = Λ(k)/(log M √k)`, indexed by `n ↦ k = n + 1`. -/
def headCoeffReal (M : ℕ) (n : Fin M) : ℝ :=
  Λ ((n : ℕ) + 1) / (Real.log M * Real.sqrt (((n : ℕ) : ℝ) + 1))

theorem headCoeffReal_nonneg (M : ℕ) (n : Fin M) : 0 ≤ headCoeffReal M n := by
  unfold headCoeffReal
  have hlog : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by
    have := n.isLt
    exact_mod_cast (show 1 ≤ M by omega))
  exact div_nonneg vonMangoldt_nonneg (mul_nonneg hlog (Real.sqrt_nonneg _))

theorem mollifiedDeviationHeadCoeff_eq_headCoeffReal (M : ℕ) (n : Fin M) :
    mollifiedDeviationHeadCoeff M n = ((headCoeffReal M n : ℝ) : ℂ) := rfl

/-- The self-convolution fibre of the square index `r`. -/
def headSquareFibre (M : ℕ) (r : Fin (M * M)) : Finset (Fin M × Fin M) :=
  (Finset.univ : Finset (Fin M × Fin M)).filter
    (fun q => ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) = (r : ℕ) + 1)

/-- Real coefficient of `H_M²` at the square index `r`. -/
def headSquareCoeff (M : ℕ) (r : Fin (M * M)) : ℝ :=
  ∑ q ∈ headSquareFibre M r, headCoeffReal M q.1 * headCoeffReal M q.2

theorem headSquareCoeff_nonneg (M : ℕ) (r : Fin (M * M)) : 0 ≤ headSquareCoeff M r :=
  Finset.sum_nonneg fun q _ => mul_nonneg (headCoeffReal_nonneg M q.1) (headCoeffReal_nonneg M q.2)

theorem dirConv_head_eq (M : ℕ) (r : Fin (M * M)) :
    Sieve.dirConv M M (mollifiedDeviationHeadCoeff M) (mollifiedDeviationHeadCoeff M) r =
      ((headSquareCoeff M r : ℝ) : ℂ) := by
  unfold Sieve.dirConv headSquareCoeff headSquareFibre
  push_cast
  rfl

/-- Coefficient energy of `H_M²`. -/
def headFourthEnergy (M : ℕ) : ℝ := ∑ r : Fin (M * M), headSquareCoeff M r ^ 2

/-- Coefficient energy of `H_M` (the head variance): `S₂(M) = ∑_{k≤M} Λ(k)²/k / (log M)²`. -/
def headSecondEnergy (M : ℕ) : ℝ := ∑ n : Fin M, headCoeffReal M n ^ 2

theorem headSecondEnergy_eq (M : ℕ) :
    headSecondEnergy M = (∑ k ∈ Icc 1 M, Λ k ^ 2 / (k : ℝ)) / (Real.log M) ^ 2 := by
  rw [← sum_normSq_mollifiedDeviationHeadCoeff]
  unfold headSecondEnergy
  apply Finset.sum_congr rfl
  intro n _
  rw [mollifiedDeviationHeadCoeff_eq_headCoeffReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ## The fourth moment is the mean square of `H_M²` -/

theorem normSq_pow_four_eq_normSq_dirPoly_sq (M : ℕ) (t : ℝ) :
    ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ 4 =
      ‖Sieve.dirPoly (M * M)
        (Sieve.dirConv M M (mollifiedDeviationHeadCoeff M) (mollifiedDeviationHeadCoeff M)) t‖ ^ 2 := by
  rw [← Sieve.dirPoly_mul_eq_dirPoly, norm_mul, ← sq, ← pow_mul]

theorem sum_normSq_dirConv_head (M : ℕ) :
    ∑ r : Fin (M * M),
      ‖Sieve.dirConv M M (mollifiedDeviationHeadCoeff M) (mollifiedDeviationHeadCoeff M) r‖ ^ 2 =
        headFourthEnergy M := by
  unfold headFourthEnergy
  apply Finset.sum_congr rfl
  intro r _
  rw [dirConv_head_eq, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Fourth moment on a window, with the Dirichlet mean value error.** -/
theorem head_fourthMoment_window (M : ℕ) (T₁ T₂ : ℝ) :
    |(∫ t in T₁..T₂, ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ 4)
        - (T₂ - T₁) * headFourthEnergy M|
      ≤ 8 * ((M * M : ℕ) : ℝ) * (1 + Real.log ((M * M : ℕ) : ℝ)) * headFourthEnergy M := by
  have h := Sieve.dirichlet_meanValue_window (M * M)
    (Sieve.dirConv M M (mollifiedDeviationHeadCoeff M) (mollifiedDeviationHeadCoeff M)) T₁ T₂
  rw [sum_normSq_dirConv_head] at h
  have hcongr : (∫ t in T₁..T₂, ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ 4)
      = ∫ t in T₁..T₂, ‖Sieve.dirPoly (M * M)
        (Sieve.dirConv M M (mollifiedDeviationHeadCoeff M) (mollifiedDeviationHeadCoeff M)) t‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    exact normSq_pow_four_eq_normSq_dirPoly_sq M t
  rw [hcongr]
  exact h

/-! ## Fibre expansion of the fourth energy -/

/-- Pairs of index pairs with equal products. -/
def headSameProduct (M : ℕ) : Finset ((Fin M × Fin M) × (Fin M × Fin M)) :=
  (Finset.univ : Finset ((Fin M × Fin M) × (Fin M × Fin M))).filter
    (fun x => ((x.1.1 : ℕ) + 1) * ((x.1.2 : ℕ) + 1) = ((x.2.1 : ℕ) + 1) * ((x.2.2 : ℕ) + 1))

/-- The four-fold coefficient product. -/
def headQuad (M : ℕ) (x : (Fin M × Fin M) × (Fin M × Fin M)) : ℝ :=
  headCoeffReal M x.1.1 * headCoeffReal M x.1.2 * (headCoeffReal M x.2.1 * headCoeffReal M x.2.2)

theorem headQuad_nonneg (M : ℕ) (x : (Fin M × Fin M) × (Fin M × Fin M)) : 0 ≤ headQuad M x :=
  mul_nonneg (mul_nonneg (headCoeffReal_nonneg _ _) (headCoeffReal_nonneg _ _))
    (mul_nonneg (headCoeffReal_nonneg _ _) (headCoeffReal_nonneg _ _))

theorem headFourthEnergy_eq_sum_sameProduct (M : ℕ) :
    headFourthEnergy M = ∑ x ∈ headSameProduct M, headQuad M x := by
  classical
  unfold headFourthEnergy headSquareCoeff
  -- each square is a double sum over the fibre
  have hsq : ∀ r : Fin (M * M),
      (∑ q ∈ headSquareFibre M r, headCoeffReal M q.1 * headCoeffReal M q.2) ^ 2 =
        ∑ x ∈ (headSquareFibre M r) ×ˢ (headSquareFibre M r), headQuad M x := by
    intro r
    rw [sq, Finset.sum_mul_sum, Finset.sum_product]
    rfl
  simp_rw [hsq]
  -- the fibres partition the same-product pairs by the common product index
  rw [← Finset.sum_biUnion]
  · congr 1
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_product,
      headSquareFibre, headSameProduct, Finset.mem_filter]
    constructor
    · rintro ⟨r, hr1, hr2⟩
      omega
    · intro hx
      refine ⟨Sieve.prodIdx x.1, ?_, ?_⟩
      · rw [Sieve.prodIdx_val]
      · rw [Sieve.prodIdx_val]
        exact hx.symm
  · intro r _ r' _ hrr'
    rw [Function.onFun, Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_product, headSquareFibre, Finset.mem_filter, Finset.mem_univ,
      true_and] at hx hx'
    apply hrr'
    apply Fin.ext
    omega

/-! ## Unique factorization: the solutions of `k₁ k₂ = l₁ l₂` in prime powers -/

/-- Exponent of `p` in `p^a q^b` for distinct primes. -/
theorem factorization_primePow_mul_left {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    (p ^ a * q ^ b).factorization p = a := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) (pow_ne_zero _ hq.ne_zero),
    Finsupp.add_apply, hp.factorization_pow, hq.factorization_pow, Finsupp.single_apply,
    Finsupp.single_apply, if_pos rfl, if_neg (Ne.symm hpq), add_zero]

/-- Exponent matching for `p^i q^j = p^a q^b` with distinct primes. -/
theorem exponents_eq_of_primePow_mul_eq {p q i j a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (h : p ^ i * q ^ j = p ^ a * q ^ b) : i = a ∧ j = b := by
  constructor
  · have h1 := congrArg (fun n => n.factorization p) h
    rwa [factorization_primePow_mul_left hp hq hpq, factorization_primePow_mul_left hp hq hpq] at h1
  · have h2 := congrArg (fun n => n.factorization q) h
    rw [mul_comm (p ^ i), mul_comm (p ^ a)] at h2
    rwa [factorization_primePow_mul_left hq hp (Ne.symm hpq),
      factorization_primePow_mul_left hq hp (Ne.symm hpq)] at h2

/-- A prime dividing `p^a q^b` is `p` or `q`. -/
theorem prime_eq_of_dvd_primePow_mul {r p q a b : ℕ} (hr : r.Prime) (hp : p.Prime) (hq : q.Prime)
    (h : r ∣ p ^ a * q ^ b) : r = p ∨ r = q := by
  rcases (Nat.Prime.dvd_mul hr).mp h with h1 | h1
  · left
    exact (Nat.prime_dvd_prime_iff_eq hr hp).mp (hr.dvd_of_dvd_pow h1)
  · right
    exact (Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow h1)

/-- Two-prime orientation: the only factorizations of `p^a q^b` (`p ≠ q`) into two prime powers are
the two orientations. -/
theorem primePow_mul_two_primes {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) {d e : ℕ} (hde : d * e = p ^ a * q ^ b)
    (hd : IsPrimePow d) (he : IsPrimePow e) :
    (d = p ^ a ∧ e = q ^ b) ∨ (d = q ^ b ∧ e = p ^ a) := by
  obtain ⟨r, i, hr, hi, rfl⟩ := (isPrimePow_nat_iff d).mp hd
  obtain ⟨s, j, hs, hj, rfl⟩ := (isPrimePow_nat_iff e).mp he
  have hrdvd : r ∣ p ^ a * q ^ b := by
    rw [← hde]
    exact dvd_mul_of_dvd_left (dvd_pow_self r hi.ne') _
  have hsdvd : s ∣ p ^ a * q ^ b := by
    rw [← hde]
    exact dvd_mul_of_dvd_right (dvd_pow_self s hj.ne') _
  rcases prime_eq_of_dvd_primePow_mul hr hp hq hrdvd with hrp | hrq
  · have hsq : s = q := by
      rcases prime_eq_of_dvd_primePow_mul hs hp hq hsdvd with hsp | hsq
      · exfalso
        rw [hrp, hsp, ← pow_add] at hde
        have hqdvd : q ∣ p ^ (i + j) := by
          rw [hde]
          exact dvd_mul_of_dvd_right (dvd_pow_self q hb.ne') _
        exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqdvd)).symm
      · exact hsq
    rw [hrp, hsq] at hde
    obtain ⟨hi', hj'⟩ := exponents_eq_of_primePow_mul_eq hp hq hpq hde
    left
    rw [hrp, hsq, hi', hj']
    exact ⟨rfl, rfl⟩
  · have hsp : s = p := by
      rcases prime_eq_of_dvd_primePow_mul hs hp hq hsdvd with hsp | hsq
      · exact hsp
      · exfalso
        rw [hrq, hsq, ← pow_add] at hde
        have hpdvd : p ∣ q ^ (i + j) := by
          rw [hde]
          exact dvd_mul_of_dvd_left (dvd_pow_self p ha.ne') _
        exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpdvd))
    rw [hrq, hsp, mul_comm] at hde
    obtain ⟨hj', hi'⟩ := exponents_eq_of_primePow_mul_eq hp hq hpq hde
    right
    rw [hrq, hsp, hi', hj']
    exact ⟨rfl, rfl⟩


/-- The solutions of `k₁k₂ = l₁l₂` in prime powers: an orientation, or all four powers of one
prime. -/
theorem primePow_quad_classification {k₁ k₂ l₁ l₂ : ℕ} (h1 : IsPrimePow k₁) (h2 : IsPrimePow k₂)
    (h3 : IsPrimePow l₁) (h4 : IsPrimePow l₂) (h : k₁ * k₂ = l₁ * l₂) :
    (l₁ = k₁ ∧ l₂ = k₂) ∨ (l₁ = k₂ ∧ l₂ = k₁) ∨
      ∃ p : ℕ, p.Prime ∧ (∃ a, 0 < a ∧ k₁ = p ^ a) ∧ (∃ b, 0 < b ∧ k₂ = p ^ b) ∧
        (∃ c, 0 < c ∧ l₁ = p ^ c) ∧ (∃ d, 0 < d ∧ l₂ = p ^ d) := by
  obtain ⟨p, a, hp, ha, rfl⟩ := (isPrimePow_nat_iff k₁).mp h1
  obtain ⟨q, b, hq, hb, rfl⟩ := (isPrimePow_nat_iff k₂).mp h2
  by_cases hpq : p = q
  · subst hpq
    right; right
    refine ⟨p, hp, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ?_, ?_⟩
    · have hdvd : l₁ ∣ p ^ (a + b) := by
        rw [pow_add, h]
        exact dvd_mul_right _ _
      obtain ⟨c, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      refine ⟨c, ?_, rfl⟩
      obtain ⟨r, i, hr, hi, hri⟩ := (isPrimePow_nat_iff (p ^ c)).mp h3
      rcases Nat.eq_zero_or_pos c with hc | hc
      · exfalso
        rw [hc, pow_zero] at hri
        exact hr.one_lt.ne' (by
          have := Nat.one_lt_pow hi.ne' hr.one_lt
          omega)
      · exact hc
    · have hdvd : l₂ ∣ p ^ (a + b) := by
        rw [pow_add, h]
        exact dvd_mul_left _ _
      obtain ⟨d, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      refine ⟨d, ?_, rfl⟩
      obtain ⟨r, i, hr, hi, hri⟩ := (isPrimePow_nat_iff (p ^ d)).mp h4
      rcases Nat.eq_zero_or_pos d with hd | hd
      · exfalso
        rw [hd, pow_zero] at hri
        exact hr.one_lt.ne' (by
          have := Nat.one_lt_pow hi.ne' hr.one_lt
          omega)
      · exact hd
  · rcases primePow_mul_two_primes hp hq hpq ha hb h.symm h3 h4 with ⟨h5, h6⟩ | ⟨h5, h6⟩
    · left; exact ⟨h5, h6⟩
    · right; left; exact ⟨h5, h6⟩

/-! ## The orientation part of the fourth energy -/

/-- Identical orientation `(q, q)`. -/
def headOrientId (M : ℕ) : Finset ((Fin M × Fin M) × (Fin M × Fin M)) :=
  (headSameProduct M).filter (fun x => x.2 = x.1)

/-- Swapped orientation `(q, q.swap)`. -/
def headOrientSwap (M : ℕ) : Finset ((Fin M × Fin M) × (Fin M × Fin M)) :=
  (headSameProduct M).filter (fun x => x.2 = x.1.swap)

theorem headOrientId_eq_image (M : ℕ) :
    headOrientId M = (Finset.univ : Finset (Fin M × Fin M)).image (fun q => (q, q)) := by
  ext x
  simp only [headOrientId, headSameProduct, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨x.1, Prod.ext rfl h.symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨rfl, rfl⟩

theorem headOrientSwap_eq_image (M : ℕ) :
    headOrientSwap M = (Finset.univ : Finset (Fin M × Fin M)).image (fun q => (q, q.swap)) := by
  ext x
  simp only [headOrientSwap, headSameProduct, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨x.1, Prod.ext rfl h.symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨by simp [Prod.swap]; ring, rfl⟩

theorem sum_headOrientId (M : ℕ) :
    ∑ x ∈ headOrientId M, headQuad M x = headSecondEnergy M ^ 2 := by
  rw [headOrientId_eq_image, Finset.sum_image (fun q _ q' _ h => (Prod.mk.inj h).1)]
  unfold headSecondEnergy headQuad
  rw [sq, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem sum_headOrientSwap (M : ℕ) :
    ∑ x ∈ headOrientSwap M, headQuad M x = headSecondEnergy M ^ 2 := by
  rw [headOrientSwap_eq_image, Finset.sum_image (fun q _ q' _ h => (Prod.mk.inj h).1)]
  unfold headSecondEnergy headQuad
  rw [sq, Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro n _
  apply Finset.sum_congr rfl
  intro m _
  simp only [Prod.swap]
  ring

/-- The diagonal fourth-power sum `∑ a_k⁴`. -/
def headDiagFourth (M : ℕ) : ℝ := ∑ n : Fin M, headCoeffReal M n ^ 4

theorem headOrientId_inter_swap (M : ℕ) :
    headOrientId M ∩ headOrientSwap M =
      (Finset.univ : Finset (Fin M)).image (fun n => ((n, n), (n, n))) := by
  ext x
  simp only [Finset.mem_inter, headOrientId, headOrientSwap, headSameProduct, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    have hswap : x.1 = x.1.swap := h1.symm.trans h2
    have h11 : x.1.1 = x.1.2 := by
      have := congrArg Prod.fst hswap
      simpa using this
    refine ⟨x.1.1, ?_⟩
    refine Prod.ext (Prod.ext rfl h11) ?_
    rw [h1]
    exact Prod.ext rfl h11
  · rintro ⟨n, rfl⟩
    exact ⟨⟨rfl, rfl⟩, ⟨rfl, rfl⟩⟩

theorem sum_headOrientId_inter_swap (M : ℕ) :
    ∑ x ∈ headOrientId M ∩ headOrientSwap M, headQuad M x = headDiagFourth M := by
  rw [headOrientId_inter_swap, Finset.sum_image (fun n _ n' _ h => by
    have := (Prod.mk.inj (Prod.mk.inj h).1).1
    exact this)]
  unfold headDiagFourth headQuad
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The orientation set. -/
def headOrient (M : ℕ) : Finset ((Fin M × Fin M) × (Fin M × Fin M)) :=
  (headSameProduct M).filter (fun x => x.2 = x.1 ∨ x.2 = x.1.swap)

theorem headOrient_eq_union (M : ℕ) : headOrient M = headOrientId M ∪ headOrientSwap M := by
  unfold headOrient headOrientId headOrientSwap
  rw [Finset.filter_or]

/-- **Orientation identity.** `∑_{orientations} = 2 S₂² − ∑ a_k⁴`. -/
theorem sum_headOrient (M : ℕ) :
    ∑ x ∈ headOrient M, headQuad M x = 2 * headSecondEnergy M ^ 2 - headDiagFourth M := by
  rw [headOrient_eq_union]
  have h := Finset.sum_union_inter (s₁ := headOrientId M) (s₂ := headOrientSwap M)
    (f := headQuad M)
  rw [sum_headOrientId, sum_headOrientSwap, sum_headOrientId_inter_swap] at h
  linarith

/-! ## The one-prime exceptional part -/

/-- Exponent range of the powers of `p` up to `M`. -/
def headExpRange (M p : ℕ) : Finset ℕ := (Finset.Icc 1 M).filter (fun e => p ^ e ≤ M)

/-- Index of `k` in `Fin M` (as `n = k − 1`), with a harmless wrap-around outside the range. -/
def headIdx (M : ℕ) (hM : 0 < M) (k : ℕ) : Fin M := ⟨(k - 1) % M, Nat.mod_lt _ hM⟩

theorem headIdx_val {M : ℕ} (hM : 0 < M) {k : ℕ} (hk1 : 1 ≤ k) (hkM : k ≤ M) :
    ((headIdx M hM k : ℕ)) + 1 = k := by
  simp only [headIdx]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The `Fin M` indices of the powers of `p`. -/
def headPowSet (M : ℕ) (hM : 0 < M) (p : ℕ) : Finset (Fin M) :=
  (headExpRange M p).image (fun e => headIdx M hM (p ^ e))

theorem headIdx_injOn_expRange {M : ℕ} (hM : 0 < M) {p : ℕ} (hp : p.Prime) :
    Set.InjOn (fun e => headIdx M hM (p ^ e)) (headExpRange M p) := by
  intro e he e' he' h
  dsimp only at h
  simp only [headExpRange, Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq] at he he'
  have h1 := headIdx_val hM (Nat.one_le_pow _ _ hp.pos) he.2
  have h2 := headIdx_val hM (Nat.one_le_pow _ _ hp.pos) he'.2
  have : p ^ e = p ^ e' := by
    rw [← h1, ← h2, h]
  exact Nat.pow_right_injective hp.two_le this

/-- Membership in the prime-power index set from an explicit power. -/
theorem mem_headPowSet_of_pow {M : ℕ} (hM : 0 < M) {p : ℕ} (hp : p.Prime) {n : Fin M} {e : ℕ}
    (he : 0 < e) (hn : (n : ℕ) + 1 = p ^ e) : n ∈ headPowSet M hM p := by
  simp only [headPowSet, Finset.mem_image, headExpRange, Finset.mem_filter, Finset.mem_Icc]
  refine ⟨e, ⟨⟨he, ?_⟩, ?_⟩, ?_⟩
  · -- e ≤ M since e < p^e = n + 1 ≤ M
    have := Nat.lt_pow_self (n := e) hp.one_lt
    have := n.isLt
    omega
  · have := n.isLt
    omega
  · apply Fin.ext
    have hkM : p ^ e ≤ M := by have := n.isLt; omega
    have := headIdx_val hM (Nat.one_le_pow _ _ hp.pos) hkM
    omega

/-- Distinct primes have disjoint power index sets. -/
theorem headPowSet_disjoint {M : ℕ} (hM : 0 < M) {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : Disjoint (headPowSet M hM p) (headPowSet M hM q) := by
  rw [Finset.disjoint_left]
  intro n hn hn'
  simp only [headPowSet, Finset.mem_image, headExpRange, Finset.mem_filter, Finset.mem_Icc] at hn hn'
  obtain ⟨e, ⟨⟨he1, _⟩, heM⟩, rfl⟩ := hn
  obtain ⟨e', ⟨⟨he1', _⟩, heM'⟩, h⟩ := hn'
  have h1 := headIdx_val hM (Nat.one_le_pow _ _ hp.pos) heM
  have h2 := headIdx_val hM (Nat.one_le_pow _ _ hq.pos) heM'
  have hpow : q ^ e' = p ^ e := by rw [← h1, ← h2, h]
  have hqdvd : q ∣ p ^ e := by
    rw [← hpow]
    exact dvd_pow_self q (by omega)
  exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hqdvd)).symm

/-- The exceptional (non-orientation) same-product pairs. -/
def headExc (M : ℕ) : Finset ((Fin M × Fin M) × (Fin M × Fin M)) :=
  (headSameProduct M).filter (fun x => ¬ (x.2 = x.1 ∨ x.2 = x.1.swap))

theorem headFourthEnergy_eq_orient_add_exc (M : ℕ) :
    headFourthEnergy M = ∑ x ∈ headOrient M, headQuad M x + ∑ x ∈ headExc M, headQuad M x := by
  rw [headFourthEnergy_eq_sum_sameProduct, headOrient, headExc,
    Finset.sum_filter_add_sum_filter_not]

/-- The four-fold power box of a prime. -/
def headPowBox (M : ℕ) (hM : 0 < M) (p : ℕ) : Finset ((Fin M × Fin M) × (Fin M × Fin M)) :=
  (headPowSet M hM p ×ˢ headPowSet M hM p) ×ˢ (headPowSet M hM p ×ˢ headPowSet M hM p)

theorem sum_headPowBox (M : ℕ) (hM : 0 < M) (p : ℕ) :
    ∑ x ∈ headPowBox M hM p, headQuad M x = (∑ n ∈ headPowSet M hM p, headCoeffReal M n) ^ 4 := by
  unfold headPowBox headQuad
  rw [Finset.sum_product, Finset.sum_product]
  simp_rw [Finset.sum_product]
  set P := headPowSet M hM p with hP
  set f : Fin M → ℝ := headCoeffReal M with hf
  have hSS : (∑ n ∈ P, f n) * (∑ n ∈ P, f n) = ∑ a ∈ P, ∑ b ∈ P, f a * f b :=
    Finset.sum_mul_sum P P f f
  have h4 : (∑ n ∈ P, f n) ^ 4 = ((∑ n ∈ P, f n) * (∑ n ∈ P, f n)) *
      ((∑ n ∈ P, f n) * (∑ n ∈ P, f n)) := by ring
  rw [h4, hSS, Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _
  rw [Finset.sum_comm]

/-- A nonzero head coefficient sits on a prime power. -/
theorem isPrimePow_of_headCoeffReal_ne_zero {M : ℕ} {n : Fin M} (h : headCoeffReal M n ≠ 0) :
    IsPrimePow ((n : ℕ) + 1) := by
  by_contra hcon
  apply h
  unfold headCoeffReal
  rw [vonMangoldt_eq_zero_iff.mpr hcon, zero_div]

/-- Every exceptional pair with nonzero weight lies in the power box of some prime `≤ M`. -/
theorem headExc_subset_biUnion {M : ℕ} (hM : 0 < M) :
    (headExc M).filter (fun x => headQuad M x ≠ 0) ⊆
      ((Finset.range (M + 1)).filter Nat.Prime).biUnion (fun p => headPowBox M hM p) := by
  intro x hx
  simp only [headExc, headSameProduct, Finset.mem_filter, Finset.mem_univ, true_and] at hx
  obtain ⟨⟨hprod, hnot⟩, hne⟩ := hx
  have hne' : headCoeffReal M x.1.1 ≠ 0 ∧ headCoeffReal M x.1.2 ≠ 0 ∧
      headCoeffReal M x.2.1 ≠ 0 ∧ headCoeffReal M x.2.2 ≠ 0 := by
    unfold headQuad at hne
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h0 <;> apply hne <;> rw [h0] <;> ring
  obtain ⟨h1, h2, h3, h4⟩ := hne'
  have hpp1 := isPrimePow_of_headCoeffReal_ne_zero h1
  have hpp2 := isPrimePow_of_headCoeffReal_ne_zero h2
  have hpp3 := isPrimePow_of_headCoeffReal_ne_zero h3
  have hpp4 := isPrimePow_of_headCoeffReal_ne_zero h4
  rcases primePow_quad_classification hpp1 hpp2 hpp3 hpp4 hprod with hor | hor | ⟨p, hp, ⟨a, ha, hka⟩, ⟨b, hb, hkb⟩, ⟨c, hc, hkc⟩, ⟨d, hd, hkd⟩⟩
  · exfalso
    apply hnot
    left
    obtain ⟨hl1, hl2⟩ := hor
    exact Prod.ext (Fin.ext (Nat.add_right_cancel hl1)) (Fin.ext (Nat.add_right_cancel hl2))
  · exfalso
    apply hnot
    right
    obtain ⟨hl1, hl2⟩ := hor
    show x.2 = (x.1.2, x.1.1)
    exact Prod.ext (Fin.ext (Nat.add_right_cancel hl1)) (Fin.ext (Nat.add_right_cancel hl2))
  · simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
    refine ⟨p, ⟨?_, hp⟩, ?_⟩
    · -- p ≤ p^a = x.1.1 + 1 ≤ M
      have hpa : p ≤ p ^ a := Nat.le_self_pow ha.ne' p
      have := x.1.1.isLt
      omega
    · simp only [headPowBox, Finset.mem_product]
      exact ⟨⟨mem_headPowSet_of_pow hM hp ha hka, mem_headPowSet_of_pow hM hp hb hkb⟩,
        ⟨mem_headPowSet_of_pow hM hp hc hkc, mem_headPowSet_of_pow hM hp hd hkd⟩⟩

theorem headPowBox_pairwiseDisjoint {M : ℕ} (hM : 0 < M) :
    (((Finset.range (M + 1)).filter Nat.Prime : Finset ℕ) : Set ℕ).PairwiseDisjoint
      (fun p => headPowBox M hM p) := by
  intro p hp q hq hpq
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hp hq
  rw [Function.onFun, Finset.disjoint_left]
  intro x hx hx'
  simp only [headPowBox, Finset.mem_product] at hx hx'
  have hd := headPowSet_disjoint hM hp.2 hq.2 hpq
  rw [Finset.disjoint_left] at hd
  exact hd hx.1.1 hx'.1.1

/-- **Exceptional bound.**  `∑_{exceptional} ≤ ∑_{p ≤ M} (∑_{p-powers} a)⁴`. -/
theorem sum_headExc_le (M : ℕ) (hM : 0 < M) :
    ∑ x ∈ headExc M, headQuad M x ≤
      ∑ p ∈ (Finset.range (M + 1)).filter Nat.Prime,
        (∑ n ∈ headPowSet M hM p, headCoeffReal M n) ^ 4 := by
  classical
  have hfilter : ∑ x ∈ headExc M, headQuad M x =
      ∑ x ∈ (headExc M).filter (fun x => headQuad M x ≠ 0), headQuad M x := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs with h
    · rfl
    · exact not_not.mp h
  rw [hfilter]
  calc ∑ x ∈ (headExc M).filter (fun x => headQuad M x ≠ 0), headQuad M x
      ≤ ∑ x ∈ ((Finset.range (M + 1)).filter Nat.Prime).biUnion (fun p => headPowBox M hM p),
          headQuad M x :=
        Finset.sum_le_sum_of_subset_of_nonneg (headExc_subset_biUnion hM)
          (fun x _ _ => headQuad_nonneg M x)
    _ = ∑ p ∈ (Finset.range (M + 1)).filter Nat.Prime, ∑ x ∈ headPowBox M hM p, headQuad M x :=
        Finset.sum_biUnion (headPowBox_pairwiseDisjoint hM)
    _ = _ := by
        apply Finset.sum_congr rfl
        intro p _
        exact sum_headPowBox M hM p


/-! ## Remainder bounds -/

/-- The convergent constant `∑ n^{-3/2}`. -/
def headTailConstant : ℝ := ∑' n : ℕ, (((n : ℝ)) ^ ((3 : ℝ) / 2))⁻¹

theorem summable_headTail : Summable (fun n : ℕ => (((n : ℝ)) ^ ((3 : ℝ) / 2))⁻¹) :=
  Real.summable_nat_rpow_inv.mpr (by norm_num)

theorem headTailConstant_nonneg : 0 ≤ headTailConstant :=
  tsum_nonneg fun n => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- `log⁴ k ≤ 4096 k^{1/2}` for `k ≥ 1`. -/
theorem log_pow_four_le {k : ℝ} (hk : 1 ≤ k) : Real.log k ^ 4 ≤ 4096 * k ^ ((1 : ℝ) / 2) := by
  have h := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ k) (by norm_num : (0 : ℝ) < 1 / 8)
  have hlog0 : 0 ≤ Real.log k := Real.log_nonneg hk
  have hpow : (k ^ ((1 : ℝ) / 8) / (1 / 8)) ^ 4 = 4096 * k ^ ((1 : ℝ) / 2) := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
    norm_num
    ring
  calc Real.log k ^ 4 ≤ (k ^ ((1 : ℝ) / 8) / (1 / 8)) ^ 4 := pow_le_pow_left₀ hlog0 h 4
    _ = 4096 * k ^ ((1 : ℝ) / 2) := hpow

/-- `∑_{n < M} ((n+1)^{-3/2}) ≤ headTailConstant`. -/
theorem sum_range_succ_rpow_le (M : ℕ) :
    ∑ n ∈ Finset.range M, (((n : ℝ) + 1) ^ ((3 : ℝ) / 2))⁻¹ ≤ headTailConstant := by
  have hshift : ∑ n ∈ Finset.range M, (((n : ℝ) + 1) ^ ((3 : ℝ) / 2))⁻¹ =
      ∑ n ∈ (Finset.range M).image (fun n : ℕ => n + 1),
        ((((n : ℕ) : ℝ)) ^ ((3 : ℝ) / 2))⁻¹ := by
    rw [Finset.sum_image (fun a _ b _ h => Nat.succ_injective h)]
    apply Finset.sum_congr rfl
    intro n _
    push_cast
    rfl
  rw [hshift]
  exact Summable.sum_le_tsum _ (fun n _ => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    summable_headTail

/-- The diagonal fourth-power sum is `O(1/log⁴ M)`. -/
theorem headDiagFourth_le (M : ℕ) (hM : 2 ≤ M) :
    headDiagFourth M ≤ 4096 * headTailConstant / (Real.log M) ^ 4 := by
  have hlog : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
  unfold headDiagFourth
  have hterm : ∀ n : Fin M, headCoeffReal M n ^ 4 ≤
      (4096 / (Real.log M) ^ 4) * ((((n : ℕ) : ℝ) + 1) ^ ((3 : ℝ) / 2))⁻¹ := by
    intro n
    have hk : (1 : ℝ) ≤ ((n : ℕ) : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) (n : ℕ); linarith
    have hkpos : (0 : ℝ) < ((n : ℕ) : ℝ) + 1 := by linarith
    have hΛ : Λ ((n : ℕ) + 1) ≤ Real.log (((n : ℕ) : ℝ) + 1) := by
      have := vonMangoldt_le_log (n := (n : ℕ) + 1)
      push_cast at this
      exact this
    have hΛ0 : 0 ≤ Λ ((n : ℕ) + 1) := vonMangoldt_nonneg
    unfold headCoeffReal
    rw [div_pow, mul_pow]
    have hsq : Real.sqrt (((n : ℕ) : ℝ) + 1) ^ 4 = (((n : ℕ) : ℝ) + 1) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hkpos.le]
    rw [hsq]
    have hnum : Λ ((n : ℕ) + 1) ^ 4 ≤ 4096 * (((n : ℕ) : ℝ) + 1) ^ ((1 : ℝ) / 2) :=
      le_trans (pow_le_pow_left₀ hΛ0 hΛ 4) (log_pow_four_le hk)
    have hden : (((n : ℕ) : ℝ) + 1) ^ 2 = (((n : ℕ) : ℝ) + 1) ^ ((3 : ℝ) / 2) *
        (((n : ℕ) : ℝ) + 1) ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hkpos, ← Real.rpow_natCast]
      norm_num
    rw [hden]
    have h32 : 0 < (((n : ℕ) : ℝ) + 1) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hkpos _
    have h12 : 0 < (((n : ℕ) : ℝ) + 1) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hkpos _
    rw [div_le_iff₀ (by positivity)]
    calc Λ ((n : ℕ) + 1) ^ 4 ≤ 4096 * (((n : ℕ) : ℝ) + 1) ^ ((1 : ℝ) / 2) := hnum
      _ = 4096 / (Real.log M) ^ 4 * ((((n : ℕ) : ℝ) + 1) ^ ((3 : ℝ) / 2))⁻¹ *
          ((Real.log M) ^ 4 * ((((n : ℕ) : ℝ) + 1) ^ ((3 : ℝ) / 2) *
            (((n : ℕ) : ℝ) + 1) ^ ((1 : ℝ) / 2))) := by
          field_simp
  calc ∑ n : Fin M, headCoeffReal M n ^ 4
      ≤ ∑ n : Fin M, (4096 / (Real.log M) ^ 4) * ((((n : ℕ) : ℝ) + 1) ^ ((3 : ℝ) / 2))⁻¹ :=
        Finset.sum_le_sum fun n _ => hterm n
    _ = (4096 / (Real.log M) ^ 4) *
          ∑ n ∈ Finset.range M, (((n : ℝ) + 1) ^ ((3 : ℝ) / 2))⁻¹ := by
        rw [← Finset.mul_sum]
        congr 1
        exact Fin.sum_univ_eq_sum_range (fun n : ℕ => (((n : ℝ) + 1) ^ ((3 : ℝ) / 2))⁻¹) M
    _ ≤ (4096 / (Real.log M) ^ 4) * headTailConstant := by
        gcongr
        exact sum_range_succ_rpow_le M
    _ = 4096 * headTailConstant / (Real.log M) ^ 4 := by ring

/-- `√(p^e) = (√p)^e`. -/
theorem sqrt_pow_eq_pow_sqrt {p : ℝ} (hp : 0 ≤ p) (e : ℕ) :
    Real.sqrt (p ^ e) = Real.sqrt p ^ e := by
  rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt hp]

/-- The prime-power column sum of the head coefficients is at most `4 log p /(log M √p)`. -/
theorem sum_headPowSet_le {M : ℕ} (hM : 0 < M) (hM2 : 2 ≤ M) {p : ℕ} (hp : p.Prime) :
    ∑ n ∈ headPowSet M hM p, headCoeffReal M n ≤
      4 * Real.log p / (Real.log M * Real.sqrt p) := by
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM2)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hsqrtp : (1 : ℝ) < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have hsqrt0 : 0 < Real.sqrt (p : ℝ) := by linarith
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  set r : ℝ := (Real.sqrt p)⁻¹ with hr
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := by
    rw [hr]
    exact inv_lt_one_of_one_lt₀ hsqrtp
  -- rewrite the column as a geometric sum over exponents
  unfold headPowSet
  rw [Finset.sum_image (headIdx_injOn_expRange hM hp)]
  have hterm : ∀ e ∈ headExpRange M p,
      headCoeffReal M (headIdx M hM (p ^ e)) = (Real.log p / Real.log M) * r ^ e := by
    intro e he
    simp only [headExpRange, Finset.mem_filter, Finset.mem_Icc] at he
    unfold headCoeffReal
    have hval := headIdx_val hM (Nat.one_le_pow _ _ hp.pos) he.2
    rw [hval, vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]
    have hcast : (((headIdx M hM (p ^ e) : ℕ) : ℝ)) + 1 = ((p : ℝ)) ^ e := by
      have h := congrArg (fun n : ℕ => (n : ℝ)) hval
      push_cast at h
      linarith
    rw [hcast, sqrt_pow_eq_pow_sqrt (Nat.cast_nonneg p), hr, inv_pow]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hgeom : ∑ e ∈ headExpRange M p, r ^ e ≤ r / (1 - r) := by
    calc ∑ e ∈ headExpRange M p, r ^ e ≤ ∑ e ∈ Finset.Ico 1 (M + 1), r ^ e := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro e he
            simp only [headExpRange, Finset.mem_filter, Finset.mem_Icc] at he
            simp only [Finset.mem_Ico]
            omega
          · intro e _ _
            exact pow_nonneg hr0 e
      _ ≤ r ^ 1 / (1 - r) := geom_sum_Ico_le_of_lt_one hr0 hr1
      _ = r / (1 - r) := by rw [pow_one]
  have hr4 : r / (1 - r) ≤ 4 / Real.sqrt p := by
    rw [hr]
    have h1r : 0 < 1 - (Real.sqrt (p : ℝ))⁻¹ := by linarith
    rw [div_le_div_iff₀ h1r hsqrt0]
    -- (√p)⁻¹ · √p ≤ 4 (1 − (√p)⁻¹)  ⟸  1 ≤ 4 − 4/√p ⟸ 4/√p ≤ 3 ⟸ √p ≥ 4/3
    have hinv : (Real.sqrt (p : ℝ))⁻¹ * Real.sqrt p = 1 := inv_mul_cancel₀ hsqrt0.ne'
    rw [hinv]
    have hsq2 : Real.sqrt 2 ≤ Real.sqrt p := Real.sqrt_le_sqrt hp2
    have hsq2' : (1.4 : ℝ) ≤ Real.sqrt 2 := by
      rw [Real.le_sqrt' (by norm_num)]
      norm_num
    have hinvle : (Real.sqrt (p : ℝ))⁻¹ ≤ 1 / 1.4 := by
      rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (le_trans hsq2' hsq2)
    nlinarith
  calc Real.log p / Real.log M * ∑ e ∈ headExpRange M p, r ^ e
      ≤ Real.log p / Real.log M * (r / (1 - r)) := by
        gcongr
    _ ≤ Real.log p / Real.log M * (4 / Real.sqrt p) := by
        gcongr
    _ = 4 * Real.log p / (Real.log M * Real.sqrt p) := by
        field_simp

/-- The exceptional part is `O(1/log⁴ M)`. -/
theorem sum_headExc_le_const (M : ℕ) (hM : 0 < M) (hM2 : 2 ≤ M) :
    ∑ x ∈ headExc M, headQuad M x ≤ 256 * 4096 * headTailConstant / (Real.log M) ^ 4 := by
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM2)
  refine le_trans (sum_headExc_le M hM) ?_
  have hterm : ∀ p ∈ (Finset.range (M + 1)).filter Nat.Prime,
      (∑ n ∈ headPowSet M hM p, headCoeffReal M n) ^ 4 ≤
        (256 * 4096 / (Real.log M) ^ 4) * (((p : ℝ)) ^ ((3 : ℝ) / 2))⁻¹ := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    have hpp := hp.2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hppos : (0 : ℝ) < p := by linarith
    have hsum0 : 0 ≤ ∑ n ∈ headPowSet M hM p, headCoeffReal M n :=
      Finset.sum_nonneg fun n _ => headCoeffReal_nonneg M n
    have hle := sum_headPowSet_le hM hM2 hpp
    have hsqrt0 : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hppos
    calc (∑ n ∈ headPowSet M hM p, headCoeffReal M n) ^ 4
        ≤ (4 * Real.log p / (Real.log M * Real.sqrt p)) ^ 4 := pow_le_pow_left₀ hsum0 hle 4
      _ = 256 * Real.log p ^ 4 / ((Real.log M) ^ 4 * (p : ℝ) ^ 2) := by
          rw [div_pow, mul_pow, mul_pow, show (4 : ℝ) ^ 4 = 256 by norm_num,
            show Real.sqrt (p : ℝ) ^ 4 = (p : ℝ) ^ 2 by
              rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hppos.le]]
      _ ≤ 256 * (4096 * (p : ℝ) ^ ((1 : ℝ) / 2)) / ((Real.log M) ^ 4 * (p : ℝ) ^ 2) := by
          gcongr
          exact log_pow_four_le (by linarith)
      _ = (256 * 4096 / (Real.log M) ^ 4) * (((p : ℝ)) ^ ((3 : ℝ) / 2))⁻¹ := by
          have hden : (p : ℝ) ^ 2 = (p : ℝ) ^ ((3 : ℝ) / 2) * (p : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [← Real.rpow_add hppos, ← Real.rpow_natCast]
            norm_num
          rw [hden]
          have h32 : 0 < (p : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_pos_of_pos hppos _
          have h12 : 0 < (p : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hppos _
          field_simp
  calc ∑ p ∈ (Finset.range (M + 1)).filter Nat.Prime,
        (∑ n ∈ headPowSet M hM p, headCoeffReal M n) ^ 4
      ≤ ∑ p ∈ (Finset.range (M + 1)).filter Nat.Prime,
          (256 * 4096 / (Real.log M) ^ 4) * (((p : ℝ)) ^ ((3 : ℝ) / 2))⁻¹ :=
        Finset.sum_le_sum hterm
    _ = (256 * 4096 / (Real.log M) ^ 4) *
          ∑ p ∈ (Finset.range (M + 1)).filter Nat.Prime, (((p : ℝ)) ^ ((3 : ℝ) / 2))⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (256 * 4096 / (Real.log M) ^ 4) * headTailConstant := by
        gcongr
        exact Summable.sum_le_tsum _
          (fun n _ => inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)) summable_headTail
    _ = 256 * 4096 * headTailConstant / (Real.log M) ^ 4 := by ring

/-! ## The fourth-energy limit and the fourth-moment law -/

/-- **Coefficient energy of `H_M²` tends to `1/2`.** -/
theorem tendsto_headFourthEnergy : Tendsto headFourthEnergy atTop (𝓝 (1 / 2)) := by
  have hS2 : Tendsto headSecondEnergy atTop (𝓝 (1 / 2)) := by
    refine tendsto_sum_vonMangoldt_sq_div_div_log_sq.congr' ?_
    filter_upwards with M
    rw [headSecondEnergy_eq]
  have hmain : Tendsto (fun M => 2 * headSecondEnergy M ^ 2) atTop (𝓝 (1 / 2)) := by
    have := (hS2.pow 2).const_mul 2
    norm_num at this
    exact this
  have hlog : Tendsto (fun M : ℕ => Real.log (M : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlog4 : Tendsto (fun M : ℕ => (Real.log (M : ℝ)) ^ 4) atTop atTop :=
    (tendsto_pow_atTop (n := 4) (by norm_num)).comp hlog
  have hrem : Tendsto (fun M : ℕ => (256 * 4096 * headTailConstant + 4096 * headTailConstant)
      / (Real.log M) ^ 4) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog4
  -- squeeze `headFourthEnergy − 2 S₂²` between `−D` and `E`
  have hdiff : Tendsto (fun M => headFourthEnergy M - 2 * headSecondEnergy M ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hrem
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with M hM
    rw [Real.norm_eq_abs]
    have hM0 : 0 < M := by omega
    have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
    have hsplit := headFourthEnergy_eq_orient_add_exc M
    rw [sum_headOrient] at hsplit
    have hE0 : 0 ≤ ∑ x ∈ headExc M, headQuad M x :=
      Finset.sum_nonneg fun x _ => headQuad_nonneg M x
    have hD0 : 0 ≤ headDiagFourth M := Finset.sum_nonneg fun n _ => by positivity
    have hDle := headDiagFourth_le M hM
    have hEle := sum_headExc_le_const M hM0 hM
    rw [abs_le]
    constructor
    · have : headFourthEnergy M - 2 * headSecondEnergy M ^ 2 = -headDiagFourth M +
          ∑ x ∈ headExc M, headQuad M x := by linarith
      rw [this]
      have : (256 * 4096 * headTailConstant + 4096 * headTailConstant) / (Real.log M) ^ 4
          = 256 * 4096 * headTailConstant / (Real.log M) ^ 4 +
            4096 * headTailConstant / (Real.log M) ^ 4 := by ring
      rw [this]
      linarith
    · have : headFourthEnergy M - 2 * headSecondEnergy M ^ 2 = -headDiagFourth M +
          ∑ x ∈ headExc M, headQuad M x := by linarith
      rw [this]
      have : (256 * 4096 * headTailConstant + 4096 * headTailConstant) / (Real.log M) ^ 4
          = 256 * 4096 * headTailConstant / (Real.log M) ^ 4 +
            4096 * headTailConstant / (Real.log M) ^ 4 := by ring
      rw [this]
      have h4 : 0 ≤ 4096 * headTailConstant / (Real.log M) ^ 4 := by
        have := headTailConstant_nonneg
        positivity
      linarith
  have := hmain.add hdiff
  simp only [add_zero] at this
  refine this.congr' ?_
  filter_upwards with M
  ring

/-- **The head's fourth moment is Gaussian: `(1/(T₂−T₁)) ∫ |H_M(1/2+it)|⁴ dt → 1/2`.**
For every `ε > 0` and all large `M`, on every window whose length dominates the Dirichlet
mean-value error `8 M² (1 + log M²)` by the factor `4/ε` — in particular on `[T, 2T]` with
`M = T^θ`, `θ < 1/2` — the normalized fourth moment of the head is within `ε` of
`1/2 = 2 · (1/2)²`, the fourth absolute moment of `CN(0, 1/2)`. -/
theorem exists_head_fourthMoment_close {ε : ℝ} (hε : 0 < ε) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∀ T₁ T₂ : ℝ,
      8 * ((M * M : ℕ) : ℝ) * (1 + Real.log ((M * M : ℕ) : ℝ)) ≤ (ε / 4) * (T₂ - T₁) →
      |(∫ t in T₁..T₂, ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ 4) / (T₂ - T₁)
          - 1 / 2| < ε := by
  have hδ : 0 < min (ε / 2) (1 / 2) := lt_min (by positivity) (by norm_num)
  have h := (Metric.tendsto_atTop.mp tendsto_headFourthEnergy) (min (ε / 2) (1 / 2)) hδ
  obtain ⟨M₁, hM₁⟩ := h
  refine ⟨max M₁ 2, ?_⟩
  intro M hM T₁ T₂ hT
  have hM1 : M₁ ≤ M := le_trans (le_max_left _ _) hM
  have hM2 : 2 ≤ M := le_trans (le_max_right _ _) hM
  have hSclose' : |headFourthEnergy M - 1 / 2| < min (ε / 2) (1 / 2) := by
    have := hM₁ M hM1
    rwa [Real.dist_eq] at this
  have hSclose : |headFourthEnergy M - 1 / 2| < ε / 2 :=
    lt_of_lt_of_le hSclose' (min_le_left _ _)
  have hS1 : headFourthEnergy M ≤ 1 := by
    have h1 := lt_of_lt_of_le hSclose' (min_le_right _ _)
    have := abs_lt.mp h1
    linarith [this.2]
  have hS0 : 0 ≤ headFourthEnergy M := Finset.sum_nonneg fun r _ => sq_nonneg _
  have hMM1 : (1 : ℝ) ≤ ((M * M : ℕ) : ℝ) := by
    have : 1 ≤ M * M := by nlinarith
    exact_mod_cast this
  have hlogMM : 0 < 1 + Real.log ((M * M : ℕ) : ℝ) := by
    have := Real.log_nonneg hMM1
    linarith
  have hlen : 0 < T₂ - T₁ := by
    have hpos : 0 < 8 * ((M * M : ℕ) : ℝ) * (1 + Real.log ((M * M : ℕ) : ℝ)) := by
      have : (0 : ℝ) < ((M * M : ℕ) : ℝ) := by linarith
      positivity
    have : 0 < (ε / 4) * (T₂ - T₁) := lt_of_lt_of_le hpos hT
    exact pos_of_mul_pos_right this (by positivity)
  have hwin := head_fourthMoment_window M T₁ T₂
  have hdiv : |(∫ t in T₁..T₂, ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ 4) / (T₂ - T₁)
      - headFourthEnergy M| ≤
        8 * ((M * M : ℕ) : ℝ) * (1 + Real.log ((M * M : ℕ) : ℝ)) * headFourthEnergy M / (T₂ - T₁) := by
    have : (∫ t in T₁..T₂, ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ 4) / (T₂ - T₁)
        - headFourthEnergy M
        = ((∫ t in T₁..T₂, ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ 4)
            - (T₂ - T₁) * headFourthEnergy M) / (T₂ - T₁) := by
      field_simp
    rw [this, abs_div, abs_of_pos hlen]
    exact div_le_div_of_nonneg_right hwin hlen.le
  have hsmall : 8 * ((M * M : ℕ) : ℝ) * (1 + Real.log ((M * M : ℕ) : ℝ)) * headFourthEnergy M
      / (T₂ - T₁) ≤ ε / 4 := by
    rw [div_le_iff₀ hlen]
    calc 8 * ((M * M : ℕ) : ℝ) * (1 + Real.log ((M * M : ℕ) : ℝ)) * headFourthEnergy M
        ≤ ((ε / 4) * (T₂ - T₁)) * headFourthEnergy M := by
          gcongr
      _ ≤ ((ε / 4) * (T₂ - T₁)) * 1 := by
          gcongr
      _ = ε / 4 * (T₂ - T₁) := by ring
  calc |(∫ t in T₁..T₂, ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ 4) / (T₂ - T₁)
        - 1 / 2|
      ≤ |(∫ t in T₁..T₂, ‖Sieve.dirPoly M (mollifiedDeviationHeadCoeff M) t‖ ^ 4) / (T₂ - T₁)
          - headFourthEnergy M| + |headFourthEnergy M - 1 / 2| := abs_sub_le _ _ _
    _ ≤ ε / 4 + |headFourthEnergy M - 1 / 2| := by linarith [le_trans hdiv hsmall]
    _ < ε / 4 + ε / 2 := by linarith
    _ ≤ ε := by linarith

end

end RHTower
