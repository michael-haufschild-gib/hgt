import Mathlib

/-!
# Dirichlet-coefficient extraction for jet monomials

The `j`-th jet atom is the arithmetic function `n ↦ (log n)^j` supported on `n ≥ 2` — the
coefficient function of the `j`-th derivative of `ζ − 1` up to sign.  A jet monomial is the
Dirichlet product of the atoms along a multiset `M` of jet orders.

The extraction theorem proved here: if a finite linear combination of jet monomials vanishes as
an arithmetic function, all its coefficients vanish.  The engine is a layer induction on the
number of atoms.  A product of `card M` functions supported on `{n ≥ 2}` vanishes at every `n`
with fewer than `card M` prime factors (with multiplicity); at `n = q·m` with `q` a prime not
dividing `m` and exactly `card M` prime factors in all, the product is a polynomial in `log q`
whose coefficients are the products of the peeled multisets at `m`.  Letting `q` run over primes
kills each `log q`-coefficient, which reindexes the layer to strictly smaller multisets.
-/

namespace GaloisForLFunctions

open ArithmeticFunction Finset

noncomputable section

/-- The `j`-th zeta jet atom: `(log n)^j` on `n ≥ 2`. -/
def zetaJetA (j : ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => if 2 ≤ n then (Real.log n : ℂ) ^ j else 0, by norm_num⟩

@[simp] theorem zetaJetA_apply (j n : ℕ) :
    zetaJetA j n = if 2 ≤ n then (Real.log n : ℂ) ^ j else 0 := rfl

theorem zetaJetA_apply_one (j : ℕ) : zetaJetA j 1 = 0 := by
  simp

theorem zetaJetA_apply_of_prime {j p : ℕ} (hp : p.Prime) :
    zetaJetA j p = (Real.log p : ℂ) ^ j := by
  simp [hp.two_le]

/-- The jet monomial along a multiset of jet orders. -/
def jetProd (M : Multiset ℕ) : ArithmeticFunction ℂ :=
  (M.map zetaJetA).prod

@[simp] theorem jetProd_zero : jetProd 0 = 1 := by
  simp [jetProd]

theorem jetProd_cons (j : ℕ) (M : Multiset ℕ) :
    jetProd (j ::ₘ M) = zetaJetA j * jetProd M := by
  simp [jetProd]

/-- Any integer at least two has a prime factor, hence positive factor count. -/
theorem one_le_cardFactors {d : ℕ} (hd : 2 ≤ d) : 1 ≤ cardFactors d := by
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
  obtain ⟨e, rfl⟩ := hpd
  have he : e ≠ 0 := by
    rintro rfl
    omega
  rw [cardFactors_mul hp.pos.ne' he, cardFactors_apply_prime hp]
  omega

/-- **Support bound.**  A jet monomial vanishes at every integer with fewer prime factors
(with multiplicity) than atoms. -/
theorem jetProd_apply_eq_zero_of_cardFactors_lt {M : Multiset ℕ} :
    ∀ {n : ℕ}, n ≠ 0 → cardFactors n < Multiset.card M → jetProd M n = 0 := by
  induction M using Multiset.induction_on with
  | empty =>
      intro n hn hlt
      simp at hlt
  | cons j M ih =>
      intro n hn hlt
      rw [jetProd_cons, mul_apply]
      apply Finset.sum_eq_zero
      rintro ⟨d, e⟩ hde
      rw [Nat.mem_divisorsAntidiagonal] at hde
      obtain ⟨hprod, hn0⟩ := hde
      have hd0 : d ≠ 0 := by
        rintro rfl
        rw [zero_mul] at hprod
        exact hn hprod.symm
      have he0 : e ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hprod
        exact hn hprod.symm
      by_cases hd2 : 2 ≤ d
      · have hcardFactors : cardFactors n = cardFactors d + cardFactors e := by
          rw [← hprod]
          exact cardFactors_mul hd0 he0
        have hlt' : cardFactors e < Multiset.card M := by
          have h1 := one_le_cardFactors hd2
          rw [Multiset.card_cons] at hlt
          omega
        rw [ih he0 hlt', mul_zero]
      · have hd1 : d = 1 := by omega
        rw [hd1, zetaJetA_apply_one, zero_mul]

/-- A jet monomial evaluates at one to the emptiness indicator. -/
theorem jetProd_apply_one (M : Multiset ℕ) :
    jetProd M 1 = if M = 0 then 1 else 0 := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons j M ih =>
      rw [jetProd_cons, mul_apply, Nat.divisorsAntidiagonal_one, Finset.sum_singleton,
        zetaJetA_apply_one, zero_mul]
      rw [if_neg (Multiset.cons_ne_zero)]

/-- **Prime-divisor expansion.**  At an integer with exactly one more prime factor than the tail
has atoms, a jet monomial expands over the prime divisors, one prime to the head atom. -/
theorem jetProd_cons_apply_eq_sum_primeFactors (j₀ : ℕ) (M : Multiset ℕ) {m : ℕ}
    (hm : m ≠ 0) (hcard : cardFactors m = Multiset.card M + 1) :
    jetProd (j₀ ::ₘ M) m =
      ∑ p ∈ m.primeFactors, (Real.log p : ℂ) ^ j₀ * jetProd M (m / p) := by
  classical
  rw [jetProd_cons, mul_apply]
  have hrestrict :
      ∑ x ∈ m.divisorsAntidiagonal with x.1.Prime, zetaJetA j₀ x.1 * jetProd M x.2 =
        ∑ x ∈ m.divisorsAntidiagonal, zetaJetA j₀ x.1 * jetProd M x.2 := by
    apply Finset.sum_filter_of_ne
    rintro ⟨d, e⟩ hde hne
    by_contra hdp
    apply hne
    rw [Nat.mem_divisorsAntidiagonal] at hde
    obtain ⟨hprod, _⟩ := hde
    have hd0 : d ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hprod
      exact hm hprod.symm
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hprod
      exact hm hprod.symm
    by_cases hd2 : 2 ≤ d
    · have hΩd : 2 ≤ cardFactors d := by
        have h1 := one_le_cardFactors hd2
        rcases Nat.lt_or_ge (cardFactors d) 2 with h2 | h2
        · exfalso
          apply hdp
          exact cardFactors_eq_one_iff_prime.mp (le_antisymm (Nat.lt_succ_iff.mp h2) h1)
        · exact h2
      have hcardFactors : cardFactors m = cardFactors d + cardFactors e := by
        rw [← hprod]
        exact cardFactors_mul hd0 he0
      have hlt : cardFactors e < Multiset.card M := by omega
      rw [jetProd_apply_eq_zero_of_cardFactors_lt he0 hlt, mul_zero]
    · have hd1 : d = 1 := by omega
      rw [hd1, zetaJetA_apply_one, zero_mul]
  rw [← hrestrict]
  apply Finset.sum_nbij' (i := fun x => x.1) (j := fun p => (p, m / p))
  · rintro ⟨d, e⟩ hde
    rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hde
    rw [Nat.mem_primeFactors]
    exact ⟨hde.2, ⟨e, hde.1.1.symm⟩, hm⟩
  · intro p hp
    rw [Nat.mem_primeFactors] at hp
    rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal]
    exact ⟨⟨Nat.mul_div_cancel' hp.2.1, hm⟩, hp.1⟩
  · rintro ⟨d, e⟩ hde
    rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hde
    have : e = m / d := by
      rw [← hde.1.1, Nat.mul_div_cancel_left]
      exact hde.2.pos
    rw [this]
  · intro p hp
    rfl
  · rintro ⟨d, e⟩ hde
    rw [Finset.mem_filter, Nat.mem_divisorsAntidiagonal] at hde
    have hd2 := hde.2.two_le
    have : e = m / d := by
      rw [← hde.1.1, Nat.mul_div_cancel_left]
      exact hde.2.pos
    rw [this, zetaJetA_apply (n := d), if_pos hd2]

/-- **Prime peeling.**  At `q·m` with `q` a prime not dividing `m` and total factor count equal
to the number of atoms, a jet monomial is a polynomial in `log q` whose coefficients are the
peeled monomials at `m`. -/
theorem jetProd_apply_prime_mul {N : ℕ} :
    ∀ (M : Multiset ℕ), (∀ j ∈ M, j ≤ N) →
      ∀ {q m : ℕ}, q.Prime → ¬ q ∣ m → m ≠ 0 →
        cardFactors (q * m) = Multiset.card M →
        jetProd M (q * m) =
          ∑ j ∈ Finset.range (N + 1),
            (Multiset.count j M : ℂ) * (Real.log q : ℂ) ^ j * jetProd (M.erase j) m := by
  classical
  intro M
  induction M using Multiset.induction_on with
  | empty =>
      intro _ q m hq hqm hm hcard
      exfalso
      have h1 := cardFactors_mul hq.pos.ne' hm
      rw [cardFactors_apply_prime hq] at h1
      rw [Multiset.card_zero] at hcard
      omega
  | cons j₀ M' ih =>
      intro hMN q m hq hqm hm hcard
      have hj₀N : j₀ ≤ N := hMN j₀ (Multiset.mem_cons_self j₀ M')
      have hMN' : ∀ j ∈ M', j ≤ N := fun j hj => hMN j (Multiset.mem_cons_of_mem hj)
      have hqm0 : q * m ≠ 0 := Nat.mul_ne_zero hq.pos.ne' hm
      have hΩqm : cardFactors (q * m) = cardFactors m + 1 := by
        rw [cardFactors_mul hq.pos.ne' hm, cardFactors_apply_prime hq]
        omega
      have hΩm : cardFactors m = Multiset.card M' := by
        rw [Multiset.card_cons] at hcard
        omega
      -- expand over the prime divisors of q·m
      rw [jetProd_cons_apply_eq_sum_primeFactors j₀ M' hqm0
        (by rw [hcard, Multiset.card_cons])]
      have hqpf : q ∉ m.primeFactors := by
        rw [Nat.mem_primeFactors]
        exact fun h => hqm h.2.1
      have hpf : (q * m).primeFactors = insert q m.primeFactors := by
        rw [Nat.primeFactors_mul hq.pos.ne' hm, hq.primeFactors, Finset.singleton_union]
      rw [hpf, Finset.sum_insert hqpf, Nat.mul_div_cancel_left m hq.pos]
      have hpterm : ∀ p ∈ m.primeFactors,
          (Real.log p : ℂ) ^ j₀ * jetProd M' ((q * m) / p) =
          ∑ j ∈ Finset.range (N + 1), (Multiset.count j M' : ℂ) * (Real.log q : ℂ) ^ j *
            ((Real.log p : ℂ) ^ j₀ * jetProd (M'.erase j) (m / p)) := by
        intro p hp
        rw [Nat.mem_primeFactors] at hp
        obtain ⟨hpp, hpm, -⟩ := hp
        have hdiv : (q * m) / p = q * (m / p) := Nat.mul_div_assoc q hpm
        have hmp0 : m / p ≠ 0 := by
          have := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hpm) hpp.pos
          omega
        have hqmp : ¬ q ∣ m / p := fun hd => hqm (hd.trans (Nat.div_dvd_of_dvd hpm))
        have hΩmp : cardFactors (q * (m / p)) = Multiset.card M' := by
          have hm_split : m = p * (m / p) := (Nat.mul_div_cancel' hpm).symm
          have h2 : cardFactors m = 1 + cardFactors (m / p) := by
            conv_lhs => rw [hm_split]
            rw [cardFactors_mul hpp.pos.ne' hmp0, cardFactors_apply_prime hpp]
          have h3 : cardFactors (q * (m / p)) = 1 + cardFactors (m / p) := by
            rw [cardFactors_mul hq.pos.ne' hmp0, cardFactors_apply_prime hq]
          omega
        rw [hdiv, ih hMN' hq hqmp hmp0 hΩmp, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [Finset.sum_congr rfl hpterm, Finset.sum_comm]
      have hfold : ∀ j ∈ Finset.range (N + 1),
          (∑ p ∈ m.primeFactors, (Multiset.count j M' : ℂ) * (Real.log q : ℂ) ^ j *
            ((Real.log p : ℂ) ^ j₀ * jetProd (M'.erase j) (m / p))) =
          (Multiset.count j M' : ℂ) * (Real.log q : ℂ) ^ j *
            jetProd (j₀ ::ₘ M'.erase j) m := by
        intro j _
        rw [← Finset.mul_sum]
        by_cases hjM : j ∈ M'
        · congr 1
          rw [jetProd_cons_apply_eq_sum_primeFactors j₀ (M'.erase j) hm ?_]
          rw [Multiset.card_erase_of_mem hjM, hΩm]
          have hc : 0 < Multiset.card M' :=
            Multiset.card_pos_iff_exists_mem.mpr ⟨j, hjM⟩
          exact (Nat.succ_pred_eq_of_pos hc).symm
        · simp [Multiset.count_eq_zero.mpr hjM]
      rw [Finset.sum_congr rfl hfold]
      have hRHS : ∀ j ∈ Finset.range (N + 1),
          (Multiset.count j (j₀ ::ₘ M') : ℂ) * (Real.log q : ℂ) ^ j *
            jetProd ((j₀ ::ₘ M').erase j) m =
          (Multiset.count j M' : ℂ) * (Real.log q : ℂ) ^ j *
              jetProd (j₀ ::ₘ M'.erase j) m +
            (if j = j₀ then ((Real.log q : ℂ) ^ j₀) * jetProd M' m else 0) := by
        intro j _
        by_cases hj : j = j₀
        · subst hj
          rw [Multiset.count_cons_self, Multiset.erase_cons_head, if_pos rfl]
          by_cases hjM : j ∈ M'
          · rw [Multiset.cons_erase hjM]
            push_cast
            ring
          · rw [Multiset.count_eq_zero.mpr hjM]
            push_cast
            ring
        · rw [Multiset.count_cons_of_ne hj, Multiset.erase_cons_tail _ (Ne.symm hj),
            if_neg hj, add_zero]
      rw [Finset.sum_congr rfl hRHS, Finset.sum_add_distrib,
        Finset.sum_ite_eq' (Finset.range (N + 1)) j₀]
      rw [if_pos (Finset.mem_range.mpr (by omega))]
      ring

/-- A polynomial in `log q` of bounded degree vanishing at every prime `q` outside a finite set
has zero coefficients. -/
theorem coeff_eq_zero_of_forall_prime_root {J : ℕ} (c : ℕ → ℂ) (S : Finset ℕ)
    (h : ∀ q : ℕ, q.Prime → q ∉ S →
      ∑ j ∈ Finset.range (J + 1), c j * (Real.log q : ℂ) ^ j = 0) :
    ∀ j ≤ J, c j = 0 := by
  classical
  set P : Polynomial ℂ :=
    ∑ j ∈ Finset.range (J + 1), Polynomial.C (c j) * Polynomial.X ^ j with hPdef
  have hP0 : P = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    have hinf : ({q : ℕ | q.Prime} \ ↑S).Infinite :=
      Nat.infinite_setOf_prime.diff S.finite_toSet
    have himg : ((fun q : ℕ => ((Real.log q : ℝ) : ℂ)) '' ({q : ℕ | q.Prime} \ ↑S)).Infinite := by
      apply Set.Infinite.image _ hinf
      rintro a ⟨ha, -⟩ b ⟨hb, -⟩ hab
      have ha0 : (0 : ℝ) < a := by exact_mod_cast ha.pos
      have hb0 : (0 : ℝ) < b := by exact_mod_cast hb.pos
      simp only [Complex.ofReal_inj] at hab
      have := congrArg Real.exp hab
      rw [Real.exp_log ha0, Real.exp_log hb0] at this
      exact_mod_cast this
    apply himg.mono
    rintro x ⟨q, ⟨hq, hqS⟩, rfl⟩
    rw [Set.mem_setOf_eq, Polynomial.IsRoot, hPdef, Polynomial.eval_finsetSum]
    have := h q hq (by simpa using hqS)
    simpa [Polynomial.eval_mul, Polynomial.eval_pow] using this
  intro j hj
  have hcoeff := congrArg (Polynomial.coeff · j) hP0
  simp only [hPdef, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_pow, Polynomial.coeff_zero] at hcoeff
  simp only [mul_ite, mul_one, mul_zero] at hcoeff
  rw [Finset.sum_ite_eq (Finset.range (J + 1)) j,
    if_pos (Finset.mem_range.mpr (by omega))] at hcoeff
  exact hcoeff

/-- **Layer extraction.**  A vanishing fixed-size layer of jet-monomial combinations has zero
coefficients. -/
theorem layer_coeff_eq_zero {N : ℕ} :
    ∀ (k : ℕ) (T : Finset (Multiset ℕ)) (γ : Multiset ℕ → ℂ),
      (∀ M ∈ T, Multiset.card M = k ∧ ∀ j ∈ M, j ≤ N) →
      (∀ n : ℕ, n ≠ 0 → cardFactors n = k → ∑ M ∈ T, γ M * jetProd M n = 0) →
      ∀ M ∈ T, γ M = 0 := by
  classical
  intro k
  induction k with
  | zero =>
      intro T γ hT hvan M hM
      have hM0 : M = 0 := Multiset.card_eq_zero.mp (hT M hM).1
      subst hM0
      have hTeq : T = {0} := by
        apply Finset.Subset.antisymm
        · intro M' hM'
          rw [Finset.mem_singleton]
          exact Multiset.card_eq_zero.mp (hT M' hM').1
        · exact Finset.singleton_subset_iff.mpr hM
      have h1 := hvan 1 one_ne_zero (by simp)
      rw [hTeq, Finset.sum_singleton, jetProd_apply_one, if_pos rfl, mul_one] at h1
      exact h1
  | succ k ihk =>
      intro T γ hT hvan M hM
      have hcardM : Multiset.card M = k + 1 := (hT M hM).1
      have hMne : M ≠ 0 := by
        intro h0
        rw [h0, Multiset.card_zero] at hcardM
        omega
      obtain ⟨j₀, hj₀⟩ := Multiset.exists_mem_of_ne_zero hMne
      have hpeeled : ∀ (j : ℕ) (m : ℕ), m ≠ 0 → cardFactors m = k →
          ∑ M' ∈ T, γ M' * ((Multiset.count j M' : ℂ) * jetProd (M'.erase j) m) = 0 := by
        intro j m hm hΩm
        rcases Nat.lt_or_ge N j with hjN | hjN
        · apply Finset.sum_eq_zero
          intro M' hM'
          have hnot : j ∉ M' := fun hj => by
            have := (hT M' hM').2 j hj
            omega
          rw [Multiset.count_eq_zero.mpr hnot]
          push_cast
          ring
        · have hpoly : ∀ q : ℕ, q.Prime → q ∉ m.primeFactors →
              ∑ i ∈ Finset.range (N + 1),
                (∑ M' ∈ T, γ M' * ((Multiset.count i M' : ℂ) * jetProd (M'.erase i) m)) *
                  (Real.log q : ℂ) ^ i = 0 := by
            intro q hq hqS
            have hqm : ¬ q ∣ m := fun hd => hqS (Nat.mem_primeFactors.mpr ⟨hq, hd, hm⟩)
            have hn0 : q * m ≠ 0 := Nat.mul_ne_zero hq.pos.ne' hm
            have hΩn : cardFactors (q * m) = k + 1 := by
              rw [cardFactors_mul hq.pos.ne' hm, cardFactors_apply_prime hq]
              omega
            have h0 := hvan (q * m) hn0 hΩn
            have hexp : ∀ M' ∈ T, γ M' * jetProd M' (q * m) =
                ∑ i ∈ Finset.range (N + 1),
                  γ M' * ((Multiset.count i M' : ℂ) * jetProd (M'.erase i) m) *
                    (Real.log q : ℂ) ^ i := by
              intro M' hM'
              rw [jetProd_apply_prime_mul M' (hT M' hM').2 hq hqm hm
                (by rw [hΩn, (hT M' hM').1]), Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              ring
            rw [Finset.sum_congr rfl hexp, Finset.sum_comm] at h0
            rw [← h0]
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_mul]
          exact coeff_eq_zero_of_forall_prime_root
            (fun i => ∑ M' ∈ T, γ M' * ((Multiset.count i M' : ℂ) * jetProd (M'.erase i) m))
            m.primeFactors hpoly j hjN
      set T' : Finset (Multiset ℕ) :=
        (T.filter (fun M' => j₀ ∈ M')).image (fun M' : Multiset ℕ => M'.erase j₀) with hT'def
      set γ' : Multiset ℕ → ℂ :=
        fun M' => γ (j₀ ::ₘ M') * ((Multiset.count j₀ M' : ℂ) + 1) with hγ'def
      have hinj : Set.InjOn (fun M' : Multiset ℕ => M'.erase j₀) ↑(T.filter (fun M' => j₀ ∈ M')) := by
        intro M₁ h₁ M₂ h₂ he
        rw [Finset.coe_filter, Set.mem_setOf_eq] at h₁ h₂
        rw [← Multiset.cons_erase h₁.2, ← Multiset.cons_erase h₂.2]
        simp only at he
        rw [he]
      have hT' : ∀ M' ∈ T', Multiset.card M' = k ∧ ∀ j ∈ M', j ≤ N := by
        intro M' hM'
        rw [hT'def, Finset.mem_image] at hM'
        obtain ⟨M₁, hM₁, rfl⟩ := hM'
        rw [Finset.mem_filter] at hM₁
        refine ⟨?_, ?_⟩
        · rw [Multiset.card_erase_of_mem hM₁.2, (hT M₁ hM₁.1).1]
          rfl
        · intro j hj
          exact (hT M₁ hM₁.1).2 j (Multiset.mem_of_mem_erase hj)
      have hvan' : ∀ m : ℕ, m ≠ 0 → cardFactors m = k →
          ∑ M' ∈ T', γ' M' * jetProd M' m = 0 := by
        intro m hm hΩ
        rw [hT'def, Finset.sum_image hinj]
        have hcongr : ∀ M₁ ∈ T.filter (fun M' => j₀ ∈ M'),
            γ' (M₁.erase j₀) * jetProd (M₁.erase j₀) m =
            γ M₁ * ((Multiset.count j₀ M₁ : ℂ) * jetProd (M₁.erase j₀) m) := by
          intro M₁ hM₁
          rw [Finset.mem_filter] at hM₁
          have hcnt : 1 ≤ Multiset.count j₀ M₁ := Multiset.count_pos.mpr hM₁.2
          rw [hγ'def]
          simp only
          rw [Multiset.cons_erase hM₁.2, Multiset.count_erase_self]
          rw [Nat.cast_sub hcnt]
          push_cast
          ring
        rw [Finset.sum_congr rfl hcongr]
        have hside : ∀ M₁ ∈ T,
            γ M₁ * ((Multiset.count j₀ M₁ : ℂ) * jetProd (M₁.erase j₀) m) ≠ 0 → j₀ ∈ M₁ := by
          intro M₁ _ hne
          by_contra hj
          apply hne
          rw [Multiset.count_eq_zero.mpr hj]
          push_cast
          ring
        rw [Finset.sum_filter_of_ne hside]
        exact hpeeled j₀ m hm hΩ
      have hγ'0 := ihk T' γ' hT' hvan'
      have hM'mem : M.erase j₀ ∈ T' := by
        rw [hT'def, Finset.mem_image]
        exact ⟨M, Finset.mem_filter.mpr ⟨hM, hj₀⟩, rfl⟩
      have hzero := hγ'0 (M.erase j₀) hM'mem
      rw [hγ'def] at hzero
      simp only at hzero
      rw [Multiset.cons_erase hj₀, Multiset.count_erase_self,
        Nat.cast_sub (Multiset.count_pos.mpr hj₀)] at hzero
      push_cast at hzero
      have hcnt0 : ((Multiset.count j₀ M : ℂ) - 1) + 1 ≠ 0 := by
        have h1 : 0 < Multiset.count j₀ M := Multiset.count_pos.mpr hj₀
        have heq : ((Multiset.count j₀ M : ℂ) - 1) + 1 = (Multiset.count j₀ M : ℂ) := by ring
        rw [heq]
        exact_mod_cast (by omega : Multiset.count j₀ M ≠ 0)
      rcases mul_eq_zero.mp hzero with h | h
      · exact h
      · exact absurd h hcnt0

/-- **Full extraction.**  A finite combination of jet monomials vanishing at every positive
integer has zero coefficients. -/
theorem jetProd_family_coeff_eq_zero {N : ℕ} (T : Finset (Multiset ℕ)) (γ : Multiset ℕ → ℂ)
    (hTN : ∀ M ∈ T, ∀ j ∈ M, j ≤ N)
    (hvan : ∀ n : ℕ, n ≠ 0 → ∑ M ∈ T, γ M * jetProd M n = 0) :
    ∀ M ∈ T, γ M = 0 := by
  classical
  suffices h : ∀ k, ∀ M ∈ T, Multiset.card M = k → γ M = 0 by
    intro M hM
    exact h (Multiset.card M) M hM rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
    intro M hM hcard
    apply layer_coeff_eq_zero (N := N) k (T.filter fun M' => Multiset.card M' = k) γ ?_ ?_ M
      (Finset.mem_filter.mpr ⟨hM, hcard⟩)
    · intro M' hM'
      rw [Finset.mem_filter] at hM'
      exact ⟨hM'.2, hTN M' hM'.1⟩
    · intro n hn hΩ
      have hside : ∀ M' ∈ T, γ M' * jetProd M' n ≠ 0 → Multiset.card M' = k := by
        intro M' hM' hne
        by_contra hcard'
        rcases Nat.lt_or_ge (Multiset.card M') k with hlt | hge
        · exact hne (by rw [ihk (Multiset.card M') hlt M' hM' rfl, zero_mul])
        · have hgt : cardFactors n < Multiset.card M' := by omega
          exact hne (by rw [jetProd_apply_eq_zero_of_cardFactors_lt hn hgt, mul_zero])
      rw [Finset.sum_filter_of_ne hside]
      exact hvan n hn

end

end GaloisForLFunctions
