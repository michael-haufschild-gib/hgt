import GaloisForLFunctions.QuantitativeFactorizationMatching.OreDeficiencyAndCascadeConservation
import GaloisForLFunctions.RHTower.MobiusSemiprimeTriprimeCellMatching
import GaloisForLFunctions.RHTower.Sieve.SquarefreeWindowCount

/-!
# Cellwise Matching Across Every Finite Prefix of Squarefree Factor Counts

Positive extension of the local prime–semiprime–triprime cellwise matching to every finite factor
depth `K ≥ 1`, paired with the quantitative linear-tail and small-cofactor depletion laws:

1. **All-finite-layer cellwise compensation (`exists_all_finite_layers_cell_matching`)**: For every
   fixed `K ≥ 1` and `B > 0`, on all sufficiently large dyadic blocks `(R, 2R]` partitioned into
   `J = ⌊(log R)^B⌋` equal cells, sequential cellwise injections `φ₁, …, φ_K` match **100% of
   squarefree integers with `1 ≤ ω(n) ≤ K`** to pairwise-disjoint opposite-parity `(k+1)`-primes
   `q d r` (`q ∈ {2, 3, 5}`, `Squarefree d`, `ω(d) = k - 1`, `r > 5` prime) in the same cell.
   Assembling the `K` injections produces a single disjoint `OppositeParityMatching` with zero
   unweighted Möbius sum, displacement `≤ 2R / (log R)^B`, and `Γ`-Sobolev norm bound
   `‖T_{R,K}‖_δ² ≤ C_{K,B} R^{1-δ} (log log R)^{2(K-1)} / (log R)^{2B+2}` uniformly in `0 ≤ δ ≤ 1`.
2. **Linear unmatched remainder (`eventually_unmatched_after_finite_layers_ge`)**: After any fixed
   number `K` of factor layers, `(6/π² - o(1)) R` squarefree integers in `(R, 2R]` remain outside
   the matched set.
3. **Prescribed-cofactor grading and `{2, 3, 5}`-supply threshold**: Exact `gcd(n, M₀)` stratification
   of `factorLayer S k` and comparison showing why single-prime `{2, 3, 5}` supply (`∑ 1/q = 31/30`)
   falls below the Poisson–Dirichlet growth ratio `k / log log R` once `k > (31/30) log log R`.
-/

open Finset Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.QuantitativeFactorizationMatching

open RHTower.PrimeCells RHTower.CubicGamma

/-! ### 1. Combinatorics and reciprocal-sum bounds on `m`-prime squarefree divisors -/

theorem prod_le_pow_card_of_le {T : Finset ℕ} {M : ℕ} (h : ∀ x ∈ T, x ≤ M) :
    ∏ x ∈ T, x ≤ M ^ T.card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a s has ih =>
    rw [prod_insert has, card_insert_of_notMem has, pow_succ']
    exact Nat.mul_le_mul (h a (mem_insert_self a s))
      (ih fun x hx => h x (mem_insert_of_mem hx))

theorem squarefree_and_primeFactors_prod_primes {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) :
    Squarefree (∏ p ∈ T, p) ∧ (∏ p ∈ T, p).primeFactors = T ∧ 0 < ∏ p ∈ T, p := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    have hp : p.Prime := hT p (mem_insert_self p s)
    have hs : ∀ q ∈ s, q.Prime := fun q hq => hT q (mem_insert_of_mem hq)
    obtain ⟨hsq, hpf, hpos⟩ := ih hs
    have hcop : Nat.Coprime p (∏ q ∈ s, q) :=
      Nat.Coprime.prod_right fun q hq =>
        (Nat.coprime_primes hp (hs q hq)).mpr fun heq => hps (heq ▸ hq)
    rw [prod_insert hps]
    refine ⟨Nat.squarefree_mul_iff.mpr ⟨hcop, Irreducible.squarefree hp, hsq⟩, ?_,
      Nat.mul_pos hp.pos hpos⟩
    rw [Nat.primeFactors_mul hp.ne_zero hpos.ne', hp.primeFactors, hpf, singleton_union]

/-- Squarefree integers in `[1, N]` with exactly `m` prime factors. -/
def sfLayer (N m : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun d => Squarefree d ∧ d.primeFactors.card = m

theorem mem_sfLayer {N m d : ℕ} :
    d ∈ sfLayer N m ↔ 1 ≤ d ∧ d ≤ N ∧ Squarefree d ∧ d.primeFactors.card = m := by
  simp only [sfLayer, mem_filter, mem_Icc, and_assoc]

theorem div_prime_mem_sfLayer {N m d p : ℕ} (hd : d ∈ sfLayer N (m + 1))
    (hp : p ∈ d.primeFactors) :
    p ∈ Nat.primesLE N ∧ d / p ∈ sfLayer N m ∧ p * (d / p) = d := by
  obtain ⟨hd1, hdN, hsq, hcard⟩ := mem_sfLayer.mp hd
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hdvd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
  have hmul : p * (d / p) = d := Nat.mul_div_cancel' hdvd
  have hpN : p ≤ N := (Nat.le_of_dvd (by omega) hdvd).trans hdN
  have hsq_split : Nat.Coprime p (d / p) ∧ Squarefree p ∧ Squarefree (d / p) := by
    rw [← Nat.squarefree_mul_iff, hmul]
    exact hsq
  have hq_pos : 1 ≤ d / p := by
    rcases Nat.eq_zero_or_pos (d / p) with h0 | hpos
    · rw [h0, mul_zero] at hmul; omega
    · exact hpos
  have hqN : d / p ≤ N := (Nat.div_le_self d p).trans hdN
  have hp_notMem : p ∉ (d / p).primeFactors := by
    intro hmem
    have hdvd' : p ∣ d / p := Nat.dvd_of_mem_primeFactors hmem
    exact hpp.not_dvd_one (hsq_split.1.gcd_eq_one ▸ Nat.dvd_gcd dvd_rfl hdvd')
  have hpf : d.primeFactors = insert p (d / p).primeFactors := by
    conv_lhs => rw [← hmul]
    rw [Nat.primeFactors_mul hpp.ne_zero (by omega), hpp.primeFactors, singleton_union]
  have hcard' : (d / p).primeFactors.card = m := by
    rw [hpf, card_insert_of_notMem hp_notMem] at hcard
    omega
  exact ⟨Nat.mem_primesLE.mpr ⟨hpN, hpp⟩, mem_sfLayer.mpr ⟨hq_pos, hqN, hsq_split.2.2, hcard'⟩,
    hmul⟩

/-- One-prime peeling upper bound: `m! ∑_{d ∈ sfLayer N m} 1/d ≤ (∑_{p ≤ N} 1/p)^m`. -/
theorem factorial_mul_sum_inv_sfLayer_le (N : ℕ) :
    ∀ m : ℕ, (m.factorial : ℝ) * ∑ d ∈ sfLayer N m, 1 / (d : ℝ) ≤
      (RHTower.Sieve.mertensS N) ^ m
  | 0 => by
    have hsub : sfLayer N 0 ⊆ {1} := by
      intro d hd
      obtain ⟨_, _, hsq, hcard⟩ := mem_sfLayer.mp hd
      have hemp : d.primeFactors = ∅ := card_eq_zero.mp hcard
      have h1 : d = 1 := by
        rw [← Nat.prod_primeFactors_of_squarefree hsq, hemp, prod_empty]
      exact mem_singleton.mpr h1
    calc ((0 : ℕ).factorial : ℝ) * ∑ d ∈ sfLayer N 0, 1 / (d : ℝ)
        = ∑ d ∈ sfLayer N 0, 1 / (d : ℝ) := by simp
      _ ≤ ∑ d ∈ ({1} : Finset ℕ), 1 / (d : ℝ) :=
          sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
      _ = 1 := by simp
      _ = (RHTower.Sieve.mertensS N) ^ 0 := by simp
  | m + 1 => by
    classical
    let σSet := (sfLayer N (m + 1)).sigma fun d => d.primeFactors
    let emb : (d : ℕ) × ℕ → ℕ × ℕ := fun x => (x.2, x.1 / x.2)
    have hemb_mem : σSet.image emb ⊆ Nat.primesLE N ×ˢ sfLayer N m := by
      intro z hz
      obtain ⟨⟨d, p⟩, hmem, rfl⟩ := mem_image.mp hz
      obtain ⟨hd, hp⟩ := mem_sigma.mp hmem
      obtain ⟨hpN, hq, -⟩ := div_prime_mem_sfLayer hd hp
      exact mem_product.mpr ⟨hpN, hq⟩
    have hemb_inj : Set.InjOn emb ↑σSet := by
      rintro ⟨d₁, p₁⟩ h₁ ⟨d₂, p₂⟩ h₂ heq
      obtain ⟨hd₁, hp₁⟩ := mem_sigma.mp h₁
      obtain ⟨hd₂, hp₂⟩ := mem_sigma.mp h₂
      have hm₁ := (div_prime_mem_sfLayer hd₁ hp₁).2.2
      have hm₂ := (div_prime_mem_sfLayer hd₂ hp₂).2.2
      simp only [emb, Prod.mk.injEq] at heq
      have hd_eq : d₁ = d₂ := by rw [← hm₁, ← hm₂, heq.1, heq.2]
      subst hd_eq; subst heq.1; rfl
    have hstep : (((m + 1 : ℕ) : ℝ)) * ∑ d ∈ sfLayer N (m + 1), 1 / (d : ℝ) ≤
        RHTower.Sieve.mertensS N * ∑ q ∈ sfLayer N m, 1 / (q : ℝ) := by
      have hlhs : (((m + 1 : ℕ) : ℝ)) * ∑ d ∈ sfLayer N (m + 1), 1 / (d : ℝ) =
          ∑ x ∈ σSet, (1 / (x.2 : ℝ)) * (1 / ((x.1 / x.2 : ℕ) : ℝ)) := by
        rw [sum_sigma, mul_sum]
        refine sum_congr rfl fun d hd => ?_
        obtain ⟨_, _, _, hcard⟩ := mem_sfLayer.mp hd
        have hcongr : ∑ p ∈ d.primeFactors, (1 / (p : ℝ)) * (1 / ((d / p : ℕ) : ℝ)) =
            ∑ _p ∈ d.primeFactors, 1 / (d : ℝ) := by
          refine sum_congr rfl fun p hp => ?_
          have hmul := (div_prime_mem_sfLayer hd hp).2.2
          have hcast : (p : ℝ) * ((d / p : ℕ) : ℝ) = (d : ℝ) := by exact_mod_cast hmul
          rw [one_div_mul_one_div, hcast]
        rw [hcongr, sum_const, hcard, nsmul_eq_mul]
      rw [hlhs]
      calc ∑ x ∈ σSet, (1 / (x.2 : ℝ)) * (1 / ((x.1 / x.2 : ℕ) : ℝ))
          = ∑ z ∈ σSet.image emb, (1 / (z.1 : ℝ)) * (1 / (z.2 : ℝ)) :=
            (sum_image hemb_inj).symm
        _ ≤ ∑ z ∈ Nat.primesLE N ×ˢ sfLayer N m, (1 / (z.1 : ℝ)) * (1 / (z.2 : ℝ)) :=
            sum_le_sum_of_subset_of_nonneg hemb_mem fun _ _ _ => by positivity
        _ = RHTower.Sieve.mertensS N * ∑ q ∈ sfLayer N m, 1 / (q : ℝ) := by
            rw [RHTower.Sieve.mertensS, sum_product, mul_sum]
            exact sum_congr rfl fun p _ => (mul_sum _ _ _).symm
    have hih := factorial_mul_sum_inv_sfLayer_le N m
    have hmS0 : 0 ≤ RHTower.Sieve.mertensS N :=
      sum_nonneg fun p _ => by positivity
    have hfac0 : (0 : ℝ) ≤ m.factorial := Nat.cast_nonneg _
    calc ((m + 1).factorial : ℝ) * ∑ d ∈ sfLayer N (m + 1), 1 / (d : ℝ)
        = (m.factorial : ℝ) * ((((m + 1 : ℕ) : ℝ)) * ∑ d ∈ sfLayer N (m + 1), 1 / (d : ℝ)) := by
          rw [Nat.factorial_succ]; push_cast; ring
      _ ≤ (m.factorial : ℝ) * (RHTower.Sieve.mertensS N * ∑ q ∈ sfLayer N m, 1 / (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hstep hfac0
      _ = RHTower.Sieve.mertensS N * ((m.factorial : ℝ) * ∑ q ∈ sfLayer N m, 1 / (q : ℝ)) := by
          ring
      _ ≤ RHTower.Sieve.mertensS N * (RHTower.Sieve.mertensS N) ^ m :=
          mul_le_mul_of_nonneg_left hih hmS0
      _ = (RHTower.Sieve.mertensS N) ^ (m + 1) := by rw [pow_succ']

/-- Logarithmic reciprocal sum bound: `∑_{d ∈ sfLayer N (m+1)} (log d)/d ≤ mertensA N · ∑_{q ∈ sfLayer N m} 1/q`. -/
theorem sum_log_div_sfLayer_succ_le (N m : ℕ) :
    ∑ d ∈ sfLayer N (m + 1), Real.log d / (d : ℝ) ≤
      RHTower.Sieve.mertensA N * ∑ q ∈ sfLayer N m, 1 / (q : ℝ) := by
  classical
  let σSet := (sfLayer N (m + 1)).sigma fun d => d.primeFactors
  let emb : (d : ℕ) × ℕ → ℕ × ℕ := fun x => (x.2, x.1 / x.2)
  have hemb_mem : σSet.image emb ⊆ Nat.primesLE N ×ˢ sfLayer N m := by
    intro z hz
    obtain ⟨⟨d, p⟩, hmem, rfl⟩ := mem_image.mp hz
    obtain ⟨hd, hp⟩ := mem_sigma.mp hmem
    obtain ⟨hpN, hq, -⟩ := div_prime_mem_sfLayer hd hp
    exact mem_product.mpr ⟨hpN, hq⟩
  have hemb_inj : Set.InjOn emb ↑σSet := by
    rintro ⟨d₁, p₁⟩ h₁ ⟨d₂, p₂⟩ h₂ heq
    obtain ⟨hd₁, hp₁⟩ := mem_sigma.mp h₁
    obtain ⟨hd₂, hp₂⟩ := mem_sigma.mp h₂
    have hm₁ := (div_prime_mem_sfLayer hd₁ hp₁).2.2
    have hm₂ := (div_prime_mem_sfLayer hd₂ hp₂).2.2
    simp only [emb, Prod.mk.injEq] at heq
    have hd_eq : d₁ = d₂ := by rw [← hm₁, ← hm₂, heq.1, heq.2]
    subst hd_eq; subst heq.1; rfl
  have hlhs : ∑ d ∈ sfLayer N (m + 1), Real.log d / (d : ℝ) =
      ∑ x ∈ σSet, (Real.log x.2 / (x.2 : ℝ)) * (1 / ((x.1 / x.2 : ℕ) : ℝ)) := by
    rw [sum_sigma]
    refine sum_congr rfl fun d hd => ?_
    obtain ⟨_, _, hsq, _⟩ := mem_sfLayer.mp hd
    have hlogd : Real.log (d : ℝ) = ∑ p ∈ d.primeFactors, Real.log (p : ℝ) := by
      conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
      push_cast
      exact Real.log_prod fun p hp =>
        by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    rw [hlogd, sum_div]
    refine sum_congr rfl fun p hp => ?_
    have hmul := (div_prime_mem_sfLayer hd hp).2.2
    have hcast : (p : ℝ) * ((d / p : ℕ) : ℝ) = (d : ℝ) := by exact_mod_cast hmul
    rw [← hcast]
    ring
  rw [hlhs]
  calc ∑ x ∈ σSet, (Real.log x.2 / (x.2 : ℝ)) * (1 / ((x.1 / x.2 : ℕ) : ℝ))
      = ∑ z ∈ σSet.image emb, (Real.log z.1 / (z.1 : ℝ)) * (1 / (z.2 : ℝ)) :=
        (sum_image hemb_inj).symm
    _ ≤ ∑ z ∈ Nat.primesLE N ×ˢ sfLayer N m,
          (Real.log z.1 / (z.1 : ℝ)) * (1 / (z.2 : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hemb_mem fun z hz _ => by
          obtain ⟨hp, _⟩ := mem_product.mp hz
          have hp1 : (1 : ℝ) ≤ z.1 := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
          have := Real.log_nonneg hp1
          positivity
    _ = RHTower.Sieve.mertensA N * ∑ q ∈ sfLayer N m, 1 / (q : ℝ) := by
        rw [RHTower.Sieve.mertensA, sum_product, mul_sum]
        exact sum_congr rfl fun p _ => (mul_sum _ _ _).symm

/-- Elementary symmetric reciprocal lower bound: if `∀ p ∈ P, 1 ≤ p` and `m ≤ S = ∑_{p ∈ P} 1/p`,
then `(S - m)^m ≤ m! ∑_{T ∈ P.powersetCard m} 1 / ∏_{p ∈ T} p`. -/
theorem le_factorial_mul_sum_inv_prod_powersetCard {P : Finset ℕ} (hP : ∀ p ∈ P, 1 ≤ p) :
    ∀ m : ℕ, (m : ℝ) ≤ (∑ p ∈ P, 1 / (p : ℝ)) →
      ((∑ p ∈ P, 1 / (p : ℝ)) - m) ^ m ≤
        (m.factorial : ℝ) * ∑ T ∈ P.powersetCard m, (1 / (∏ p ∈ T, (p : ℝ)))
  | 0, _ => by simp
  | m + 1, hm => by
    classical
    set S : ℝ := ∑ p ∈ P, 1 / (p : ℝ)
    have hm' : (m : ℝ) ≤ S := by push_cast at hm; linarith
    have hih := le_factorial_mul_sum_inv_prod_powersetCard hP m hm'
    have hbij : (((m + 1 : ℕ) : ℝ)) * ∑ U ∈ P.powersetCard (m + 1), (1 / (∏ q ∈ U, (q : ℝ))) =
        ∑ T ∈ P.powersetCard m,
          (1 / (∏ q ∈ T, (q : ℝ))) * (∑ p ∈ P \ T, 1 / (p : ℝ)) := by
      have hlhs : (((m + 1 : ℕ) : ℝ)) * ∑ U ∈ P.powersetCard (m + 1), (1 / (∏ q ∈ U, (q : ℝ))) =
          ∑ x ∈ (P.powersetCard (m + 1)).sigma (fun U => U), (1 / (∏ q ∈ x.1, (q : ℝ))) := by
        rw [sum_sigma, mul_sum]
        refine sum_congr rfl fun U hU => ?_
        rw [sum_const, (mem_powersetCard.mp hU).2, nsmul_eq_mul]
      have hrhs : ∑ T ∈ P.powersetCard m,
            (1 / (∏ q ∈ T, (q : ℝ))) * (∑ p ∈ P \ T, 1 / (p : ℝ)) =
          ∑ y ∈ (P.powersetCard m).sigma (fun T => P \ T),
            (1 / (∏ q ∈ y.1, (q : ℝ))) * (1 / (y.2 : ℝ)) := by
        rw [sum_sigma]
        exact sum_congr rfl fun T _ => mul_sum _ _ _
      rw [hlhs, hrhs]
      refine Finset.sum_bij (fun x _ => ⟨x.1.erase x.2, x.2⟩) ?_ ?_ ?_ ?_
      · rintro ⟨U, p⟩ hx
        obtain ⟨hU, hpU⟩ := mem_sigma.mp hx
        obtain ⟨hUP, hUcard⟩ := mem_powersetCard.mp hU
        refine mem_sigma.mpr ⟨mem_powersetCard.mpr ⟨(erase_subset p U).trans hUP, ?_⟩,
          mem_sdiff.mpr ⟨hUP hpU, notMem_erase p U⟩⟩
        rw [card_erase_of_mem hpU, hUcard]; omega
      · rintro ⟨U₁, p₁⟩ hx₁ ⟨U₂, p₂⟩ hx₂ heq
        obtain ⟨_, hp₁⟩ := mem_sigma.mp hx₁
        obtain ⟨_, hp₂⟩ := mem_sigma.mp hx₂
        simp only [Sigma.mk.inj_iff] at heq
        obtain ⟨hT_eq, rfl⟩ := heq
        have hU_eq : U₁ = U₂ := by
          rw [← insert_erase hp₁, ← insert_erase hp₂, eq_of_heq hT_eq]
        subst hU_eq; rfl
      · rintro ⟨T, p⟩ hy
        obtain ⟨hT, hp⟩ := mem_sigma.mp hy
        obtain ⟨hTP, hTcard⟩ := mem_powersetCard.mp hT
        obtain ⟨hpP, hpT⟩ := mem_sdiff.mp hp
        refine ⟨⟨insert p T, p⟩, mem_sigma.mpr ⟨mem_powersetCard.mpr
          ⟨insert_subset_iff.mpr ⟨hpP, hTP⟩, by rw [card_insert_of_notMem hpT, hTcard]⟩,
          mem_insert_self p T⟩, ?_⟩
        simp [erase_insert hpT]
      · rintro ⟨U, p⟩ hx
        obtain ⟨_, hpU⟩ := mem_sigma.mp hx
        have hprod : ∏ q ∈ U, (q : ℝ) = (p : ℝ) * ∏ q ∈ U.erase p, (q : ℝ) :=
          (mul_prod_erase U (fun q : ℕ => (q : ℝ)) hpU).symm
        rw [hprod]
        ring
    have hrem : ∀ T ∈ P.powersetCard m,
        S - ((m + 1 : ℕ) : ℝ) ≤ ∑ p ∈ P \ T, 1 / (p : ℝ) := by
      intro T hT
      obtain ⟨hTP, hTcard⟩ := mem_powersetCard.mp hT
      have hsplit : ∑ p ∈ P \ T, 1 / (p : ℝ) + ∑ p ∈ T, 1 / (p : ℝ) = S :=
        sum_sdiff hTP
      have hTle : ∑ p ∈ T, 1 / (p : ℝ) ≤ (m : ℝ) := by
        calc ∑ p ∈ T, 1 / (p : ℝ)
            ≤ ∑ _p ∈ T, (1 : ℝ) := sum_le_sum fun p hp => by
              have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hP p (hTP hp)
              exact div_le_one_of_le₀ hp1 (by positivity)
          _ = (m : ℝ) := by simp [hTcard]
      push_cast
      linarith
    have hstep : (S - ((m + 1 : ℕ) : ℝ)) * ∑ T ∈ P.powersetCard m, (1 / (∏ q ∈ T, (q : ℝ))) ≤
        (((m + 1 : ℕ) : ℝ)) * ∑ U ∈ P.powersetCard (m + 1), (1 / (∏ q ∈ U, (q : ℝ))) := by
      rw [hbij, mul_sum]
      refine sum_le_sum fun T hT => ?_
      rw [mul_comm (S - _)]
      exact mul_le_mul_of_nonneg_left (hrem T hT) (by positivity)
    have hnn : 0 ≤ S - ((m + 1 : ℕ) : ℝ) := by linarith
    have hpow_mono : (S - ((m + 1 : ℕ) : ℝ)) ^ m ≤ (S - m) ^ m := by
      gcongr
      push_cast; linarith
    have hfac0 : (0 : ℝ) ≤ m.factorial := Nat.cast_nonneg _
    calc (S - ((m + 1 : ℕ) : ℝ)) ^ (m + 1)
        = (S - ((m + 1 : ℕ) : ℝ)) * (S - ((m + 1 : ℕ) : ℝ)) ^ m := pow_succ' _ _
      _ ≤ (S - ((m + 1 : ℕ) : ℝ)) * (S - m) ^ m :=
          mul_le_mul_of_nonneg_left hpow_mono hnn
      _ ≤ (S - ((m + 1 : ℕ) : ℝ)) *
            ((m.factorial : ℝ) * ∑ T ∈ P.powersetCard m, (1 / (∏ q ∈ T, (q : ℝ)))) :=
          mul_le_mul_of_nonneg_left hih hnn
      _ = (m.factorial : ℝ) *
            ((S - ((m + 1 : ℕ) : ℝ)) * ∑ T ∈ P.powersetCard m, (1 / (∏ q ∈ T, (q : ℝ)))) := by
          ring
      _ ≤ (m.factorial : ℝ) *
            ((((m + 1 : ℕ) : ℝ)) * ∑ U ∈ P.powersetCard (m + 1), (1 / (∏ q ∈ U, (q : ℝ)))) :=
          mul_le_mul_of_nonneg_left hstep hfac0
      _ = ((m + 1).factorial : ℝ) *
            ∑ U ∈ P.powersetCard (m + 1), (1 / (∏ q ∈ U, (q : ℝ))) := by
          rw [Nat.factorial_succ]; push_cast; ring

/-! ### 2. Log-power window upper bounds for `k`-prime squarefree counts -/

/-- Squarefree `k`-primes in `(u, v]`. -/
def kPrimesIn (k : ℕ) (u v : ℝ) : Finset ℕ :=
  (Ioc ⌊u⌋₊ ⌊v⌋₊).filter fun n => Squarefree n ∧ n.primeFactors.card = k

theorem kPrimesIn_nat_eq_factorLayer (k a b : ℕ) :
    kPrimesIn k a b = factorLayer (Ioc a b) k := by
  ext n
  simp only [kPrimesIn, factorLayer, Nat.floor_natCast, mem_filter]

theorem mem_kPrimesIn {k : ℕ} {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) {n : ℕ} :
    n ∈ kPrimesIn k u v ↔ u < n ∧ (n : ℝ) ≤ v ∧ Squarefree n ∧ n.primeFactors.card = k := by
  simp only [kPrimesIn, mem_filter, mem_Ioc, Nat.floor_lt hu, Nat.le_floor_iff hv, and_assoc]

theorem kPrimesIn_one_eq_windowPrimes {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    kPrimesIn 1 u v = windowPrimes u v := by
  ext n
  rw [mem_kPrimesIn hu hv, mem_windowPrimes hu hv]
  constructor
  · rintro ⟨hun, hnv, hsq, hcard⟩
    obtain ⟨p, hp⟩ := card_eq_one.mp hcard
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by rw [hp]; simp)
    have hneq : n = p := by
      rw [← Nat.prod_primeFactors_of_squarefree hsq, hp, prod_singleton]
    exact ⟨hneq ▸ hpp, hun, hnv⟩
  · rintro ⟨hn, hun, hnv⟩
    exact ⟨hun, hnv, Irreducible.squarefree hn, by rw [hn.primeFactors, card_singleton]⟩

/-- Peeling the largest prime factor `r = max' n.primeFactors` of `n ∈ kPrimesIn (m + 1) u v`
produces `d = n / r ∈ sfLayer ⌊2R⌋₊ m` with `(d : ℝ)^{m+1} ≤ (2R)^m` and `r ∈ windowPrimes (u/d) (v/d)`. -/
theorem kPrimesIn_succ_subset_biUnion {m : ℕ} {R u v : ℝ} (hR0 : 0 ≤ R)
    (hRu : R ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * R) :
    kPrimesIn (m + 1) u v ⊆
      ((sfLayer ⌊2 * R⌋₊ m).filter (fun d => (d : ℝ) ^ (m + 1) ≤ (2 * R) ^ m)).biUnion
        fun d => (windowPrimes (u / d) (v / d)).image (d * ·) := by
  have hu0 : 0 ≤ u := hR0.trans hRu
  have hv0 : 0 ≤ v := hu0.trans huv
  intro n hn
  obtain ⟨hun, hnv, hsq, hcard⟩ := (mem_kPrimesIn hu0 hv0).mp hn
  have hne : n.primeFactors.Nonempty := card_pos.mp (by omega)
  let r := n.primeFactors.max' hne
  have hr_mem : r ∈ n.primeFactors := max'_mem _ hne
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr_mem
  have hn_pos : 0 < n := hsq.ne_zero.bot_lt
  have hmem_sf : n ∈ sfLayer ⌊2 * R⌋₊ (m + 1) :=
    mem_sfLayer.mpr ⟨hn_pos, Nat.le_floor (hnv.trans hv), hsq, hcard⟩
  obtain ⟨_, hd_sf, hmul⟩ := div_prime_mem_sfLayer hmem_sf hr_mem
  let d := n / r
  have hmul' : d * r = n := by rw [mul_comm]; exact hmul
  have hn_le_rpow : n ≤ r ^ (m + 1) := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
    rw [← hcard]
    exact prod_le_pow_card_of_le fun p hp => le_max' _ p hp
  have hd_pow_nat : d ^ (m + 1) ≤ n ^ m := by
    have h1 : d ^ (m + 1) * n ≤ n ^ m * n := by
      calc d ^ (m + 1) * n ≤ d ^ (m + 1) * r ^ (m + 1) := Nat.mul_le_mul_left _ hn_le_rpow
        _ = (d * r) ^ (m + 1) := (mul_pow d r (m + 1)).symm
        _ = n ^ (m + 1) := by rw [hmul']
        _ = n ^ m * n := pow_succ n m
    exact Nat.le_of_mul_le_mul_right h1 hn_pos
  have hd_pow : (d : ℝ) ^ (m + 1) ≤ (2 * R) ^ m := by
    calc (d : ℝ) ^ (m + 1) ≤ (n : ℝ) ^ m := by exact_mod_cast hd_pow_nat
      _ ≤ (2 * R) ^ m := by gcongr; exact hnv.trans hv
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_sfLayer.mp hd_sf).1
  refine mem_biUnion.mpr ⟨d, mem_filter.mpr ⟨hd_sf, hd_pow⟩, mem_image.mpr ⟨r, ?_, hmul'⟩⟩
  rw [mem_windowPrimes (by positivity) (by positivity)]
  refine ⟨hrp, ?_, ?_⟩
  · rw [div_lt_iff₀ hd0]
    have : (d * r : ℝ) = n := by exact_mod_cast hmul'
    linarith
  · rw [le_div_iff₀ hd0]
    have : (d * r : ℝ) = n := by exact_mod_cast hmul'
    linarith

/-- Window prime upper bound at a divisor `d ≥ 1` with `(d : ℝ)^{m+1} ≤ (2R)^m`. -/
theorem card_windowPrimes_div_divisor_le {C T : ℝ} {A m : ℕ} (hC : 0 < C) (hT : 3 ≤ T)
    (hθ : ∀ t : ℝ, T ≤ t → |Chebyshev.theta t - t| ≤ C * t / Real.log t ^ A)
    {R u v : ℝ} (hR0 : 0 < R) (hRT : (2 : ℝ) ^ m * T ^ (m + 1) ≤ R)
    (hL2 : 2 * (m : ℝ) * Real.log 2 ≤ Real.log R)
    (hRu : R ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * R)
    {d : ℕ} (hd1 : 1 ≤ d) (hdpow : (d : ℝ) ^ (m + 1) ≤ (2 * R) ^ m) :
    ((windowPrimes (u / d) (v / d)).card : ℝ) ≤
      (v - u) / Real.log R * (1 / d) +
        2 * ((m : ℝ) + 1) * (v - u) / Real.log R ^ 2 * (Real.log d / d) +
        4 * C * (2 * ((m : ℝ) + 1)) ^ (A + 1) * (R / Real.log R ^ A) / Real.log R * (1 / d) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hL0 : 0 < Real.log R := by
    rcases Nat.eq_zero_or_pos m with rfl | hmpos
    · simp only [pow_zero, one_mul, zero_add, pow_one] at hRT
      exact Real.log_pos (by linarith)
    · have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
      have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      nlinarith
  have hud_pow : R / (2 : ℝ) ^ m ≤ (u / d) ^ (m + 1) := by
    have h1 : R / (2 : ℝ) ^ m * (d : ℝ) ^ (m + 1) ≤ u ^ (m + 1) := by
      calc R / (2 : ℝ) ^ m * (d : ℝ) ^ (m + 1)
          ≤ R / (2 : ℝ) ^ m * (2 * R) ^ m := by gcongr
        _ = R ^ (m + 1) := by rw [mul_pow, pow_succ']; field_simp
        _ ≤ u ^ (m + 1) := by gcongr
    have hd_pow0 : 0 < (d : ℝ) ^ (m + 1) := by positivity
    rw [div_pow, le_div_iff₀ hd_pow0]
    exact h1
  have haT : T ≤ u / d := by
    have hTpow : T ^ (m + 1) ≤ (u / d) ^ (m + 1) := by
      have h1 : T ^ (m + 1) ≤ R / (2 : ℝ) ^ m := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      exact h1.trans hud_pow
    exact (pow_le_pow_iff_left₀ (by linarith) (by positivity) (by omega)).mp hTpow
  have hab : u / d ≤ v / d := by gcongr
  have hinc := abs_theta_increment_le hC.le hT hθ haT hab
  have hlogd : ((m : ℝ) + 1) * Real.log d ≤ (m : ℝ) * (Real.log R + Real.log 2) := by
    have h1 : Real.log ((d : ℝ) ^ (m + 1)) ≤ Real.log ((2 * R) ^ m) :=
      Real.log_le_log (by positivity) hdpow
    rw [Real.log_pow, Real.log_pow, Real.log_mul (by norm_num) hR0.ne'] at h1
    push_cast at h1
    linarith
  have hm1_pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hL_gap : Real.log R / (2 * ((m : ℝ) + 1)) ≤ Real.log R - Real.log d := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hla0 : 0 < Real.log R - Real.log d := by
    have : 0 < Real.log R / (2 * ((m : ℝ) + 1)) := by positivity
    linarith
  have hloga : Real.log R - Real.log d ≤ Real.log (u / d) := by
    rw [Real.log_div (by linarith) hd0.ne']
    have := Real.log_le_log hR0 hRu
    linarith
  have hla : 0 < Real.log (u / d) := lt_of_lt_of_le hla0 hloga
  have hθ' : Chebyshev.theta (v / d) - Chebyshev.theta (u / d) ≤
      (v - u) / d + 2 * C * (v / d) / Real.log (u / d) ^ A := by
    have := (abs_le.mp hinc).2
    have e : v / d - u / d = (v - u) / d := by ring
    linarith
  have hcard := card_windowPrimes_mul_log_le (show 1 ≤ u / d by linarith) hab
  have hc : ((windowPrimes (u / d) (v / d)).card : ℝ) ≤
      (v - u) / d / Real.log (u / d) + 2 * C * (v / d) / Real.log (u / d) ^ (A + 1) := by
    rw [pow_succ, ← div_div, ← add_div, le_div_iff₀ hla]
    linarith
  have hc1 : (v - u) / d / Real.log (u / d) ≤ (v - u) / d / (Real.log R - Real.log d) :=
    div_le_div_of_nonneg_left (by have : 0 ≤ v - u := by linarith; positivity) hla0 hloga
  have hinv : 1 / (Real.log R - Real.log d) ≤
      1 / Real.log R + 2 * ((m : ℝ) + 1) * Real.log d / Real.log R ^ 2 := by
    have hld0 : 0 ≤ Real.log d := Real.log_nonneg hd1'
    rw [div_add_div _ _ hL0.ne' (by positivity), div_le_div_iff₀ hla0 (by positivity)]
    have hprod : 0 ≤ Real.log R * Real.log d *
        (2 * ((m : ℝ) + 1) * (Real.log R - Real.log d) - Real.log R) := by
      refine mul_nonneg (mul_nonneg hL0.le hld0) ?_
      have : Real.log R ≤ 2 * ((m : ℝ) + 1) * (Real.log R - Real.log d) := by
        rwa [div_le_iff₀ (by positivity)] at hL_gap
      linarith
    nlinarith
  have hc1' : (v - u) / d / (Real.log R - Real.log d) ≤
      (v - u) / Real.log R * (1 / d) +
        2 * ((m : ℝ) + 1) * (v - u) / Real.log R ^ 2 * (Real.log d / d) := by
    have hvd0 : 0 ≤ (v - u) / d := by have : 0 ≤ v - u := by linarith; positivity
    calc (v - u) / d / (Real.log R - Real.log d)
        = (v - u) / d * (1 / (Real.log R - Real.log d)) := by ring
      _ ≤ (v - u) / d * (1 / Real.log R + 2 * ((m : ℝ) + 1) * Real.log d / Real.log R ^ 2) :=
          mul_le_mul_of_nonneg_left hinv hvd0
      _ = _ := by ring
  have hc2 : 2 * C * (v / d) / Real.log (u / d) ^ (A + 1) ≤
      4 * C * (2 * ((m : ℝ) + 1)) ^ (A + 1) * (R / Real.log R ^ A) / Real.log R * (1 / d) := by
    have hpow : (Real.log R / (2 * ((m : ℝ) + 1))) ^ (A + 1) ≤ Real.log (u / d) ^ (A + 1) := by
      gcongr
      exact hL_gap.trans hloga
    have hpow0 : 0 < (Real.log R / (2 * ((m : ℝ) + 1))) ^ (A + 1) := by positivity
    have hv0 : 0 ≤ v := by linarith
    calc 2 * C * (v / d) / Real.log (u / d) ^ (A + 1)
        ≤ 2 * C * (v / d) / (Real.log R / (2 * ((m : ℝ) + 1))) ^ (A + 1) :=
          div_le_div_of_nonneg_left (by positivity) hpow0 hpow
      _ ≤ 2 * C * (2 * R / d) / (Real.log R / (2 * ((m : ℝ) + 1))) ^ (A + 1) := by gcongr
      _ = 4 * C * (2 * ((m : ℝ) + 1)) ^ (A + 1) * (R / Real.log R ^ A) / Real.log R * (1 / d) := by
          rw [div_pow, pow_succ (Real.log R)]; field_simp; ring
  linarith

/-- Uniform upper bound on `k`-prime squarefree counts across all cells `(u, v] ⊆ [R, 2R]`
of width at least `R / (log R)^B`. -/
theorem exists_card_kPrimesIn_le (k : ℕ) (hk : 1 ≤ k) (B : ℝ) :
    ∃ K₁ R₀ : ℝ, 3 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      ∀ u v : ℝ, R ≤ u → u ≤ v → v ≤ 2 * R → R / Real.log R ^ B ≤ v - u →
        ((kPrimesIn k u v).card : ℝ) ≤
          (1 + 1 / 100) * (v - u) / (((k - 1).factorial : ℝ) * Real.log R) *
            (Real.log (Real.log R) + K₁) ^ (k - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rcases Nat.eq_zero_or_pos m with rfl | hmpos
  · obtain ⟨R₀, hR₀3, hup⟩ := exists_card_windowPrimes_le B (ε := 1 / 100) (by norm_num)
    refine ⟨0, R₀, hR₀3, fun R hR u v hRu huv hv hgap => ?_⟩
    have hu0 : 0 ≤ u := by linarith
    have hv0 : 0 ≤ v := by linarith
    rw [kPrimesIn_one_eq_windowPrimes hu0 hv0]
    simpa using hup R hR u v hRu huv hv hgap
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j + 1 := ⟨m - 1, by omega⟩
    set m' : ℕ := j + 1
    obtain ⟨A, hAB⟩ : ∃ A : ℕ, B + 1 ≤ A := ⟨⌈B⌉₊ + 1, by push_cast; linarith [Nat.le_ceil B]⟩
    obtain ⟨C, hC, T, hT, hθ⟩ := exists_abs_theta_sub_le A
    set κ : ℝ := 4 * C * (2 * ((m' : ℝ) + 1)) ^ (A + 1)
    have hκ0 : 0 < κ := by positivity
    set c₀ : ℝ := RHTower.Sieve.mertensSecondUpperConst + 1
    set C_sub : ℝ := 8 * ((m' : ℝ) + 1) * (m' : ℝ)
    have hev : ∀ᶠ R : ℝ in atTop,
        (2 : ℝ) ^ m' * T ^ (m' + 1) ≤ R ∧ 16 ≤ R ∧ 1 ≤ Real.log R ∧
        2 * (m' : ℝ) * Real.log 2 ≤ Real.log R ∧
        100 * κ ≤ Real.log R ∧ 1 ≤ Real.log (Real.log R) :=
      (eventually_ge_atTop _).and ((eventually_ge_atTop _).and
        ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and
          ((Real.tendsto_log_atTop.eventually_ge_atTop _).and
            ((Real.tendsto_log_atTop.eventually_ge_atTop _).and
              ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1)))))
    obtain ⟨X, hX⟩ := eventually_atTop.mp hev
    refine ⟨c₀ + C_sub, max X 3, le_max_right _ _, fun R hR u v hRu huv hv hgap => ?_⟩
    obtain ⟨hRT, hR16, hL1, hLm2, hLκ, hll1⟩ := hX R ((le_max_left _ _).trans hR)
    have hR0 : 0 < R := by linarith
    have hL0 : 0 < Real.log R := by linarith
    have hvu : 0 ≤ v - u := by linarith
    let N := ⌊2 * R⌋₊
    have hN2 : 2 ≤ N := Nat.le_floor (by push_cast; linarith)
    have hNle : (N : ℝ) ≤ 2 * R := Nat.floor_le (by positivity)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlogN : Real.log N ≤ 2 * Real.log R := by
      have hl2 : Real.log 2 ≤ Real.log R := by
        have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ R)
        exact this
      calc Real.log N ≤ Real.log (2 * R) := Real.log_le_log hNpos hNle
        _ = Real.log 2 + Real.log R := Real.log_mul (by norm_num) hR0.ne'
        _ ≤ 2 * Real.log R := by linarith
    have hlogN0 : 0 < Real.log N :=
      Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hmS : RHTower.Sieve.mertensS N ≤ Real.log (Real.log R) + c₀ := by
      have h1 := RHTower.Sieve.mertensS_le hN2
      have h2 : RHTower.Sieve.logLog N ≤ Real.log (Real.log R) + 1 := by
        calc RHTower.Sieve.logLog N = Real.log (Real.log N) := rfl
          _ ≤ Real.log (2 * Real.log R) := Real.log_le_log hlogN0 hlogN
          _ = Real.log 2 + Real.log (Real.log R) := Real.log_mul (by norm_num) hL0.ne'
          _ ≤ Real.log (Real.log R) + 1 := by linarith [Real.log_two_lt_d9]
      linarith
    have hmS0 : 0 ≤ RHTower.Sieve.mertensS N := sum_nonneg fun p _ => by positivity
    have hmA : RHTower.Sieve.mertensA N ≤ 4 * Real.log R := by
      have h1 := RHTower.Sieve.mertensFirst_upper (show 1 ≤ N by omega)
      linarith
    let D := (sfLayer N m').filter fun d => (d : ℝ) ^ (m' + 1) ≤ (2 * R) ^ m'
    have hsub_D : D ⊆ sfLayer N m' := filter_subset _ _
    have hcard_le : (kPrimesIn (m' + 1) u v).card ≤
        ∑ d ∈ D, (windowPrimes (u / d) (v / d)).card :=
      (card_le_card (kPrimesIn_succ_subset_biUnion hR0.le hRu huv hv)).trans
        (card_biUnion_le.trans (sum_le_sum fun _ _ => card_image_le))
    have hRA : R / Real.log R ^ A ≤ (v - u) / Real.log R :=
      (rpow_logPow_le hR0.le hL1 hAB).trans (by gcongr)
    have hκ_err : κ * (R / Real.log R ^ A) / Real.log R ≤ (1 / 100) * ((v - u) / Real.log R) := by
      calc κ * (R / Real.log R ^ A) / Real.log R
          ≤ κ * ((v - u) / Real.log R) / Real.log R := by gcongr
        _ = (κ / Real.log R) * ((v - u) / Real.log R) := by ring
        _ ≤ (1 / 100) * ((v - u) / Real.log R) := by
            gcongr
            rw [div_le_iff₀ hL0]; linarith
    have hS1 : ∑ d ∈ D, 1 / (d : ℝ) ≤
        (Real.log (Real.log R) + c₀) ^ m' / (m'.factorial : ℝ) := by
      have hfac_pos : (0 : ℝ) < m'.factorial := by exact_mod_cast Nat.factorial_pos _
      rw [le_div_iff₀ hfac_pos, mul_comm]
      calc (m'.factorial : ℝ) * ∑ d ∈ D, 1 / (d : ℝ)
          ≤ (m'.factorial : ℝ) * ∑ d ∈ sfLayer N m', 1 / (d : ℝ) :=
            mul_le_mul_of_nonneg_left
              (sum_le_sum_of_subset_of_nonneg hsub_D fun _ _ _ => by positivity) hfac_pos.le
        _ ≤ (RHTower.Sieve.mertensS N) ^ m' := factorial_mul_sum_inv_sfLayer_le N m'
        _ ≤ (Real.log (Real.log R) + c₀) ^ m' := by gcongr
    have hS2 : ∑ d ∈ D, Real.log d / (d : ℝ) ≤
        4 * Real.log R * (Real.log (Real.log R) + c₀) ^ j / (j.factorial : ℝ) := by
      have hj_pos : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos _
      have hj_sum : ∑ q ∈ sfLayer N j, 1 / (q : ℝ) ≤
          (Real.log (Real.log R) + c₀) ^ j / (j.factorial : ℝ) := by
        rw [le_div_iff₀ hj_pos, mul_comm]
        exact (factorial_mul_sum_inv_sfLayer_le N j).trans (by gcongr)
      have hD_log : ∑ d ∈ D, Real.log d / (d : ℝ) ≤
          ∑ d ∈ sfLayer N (j + 1), Real.log d / (d : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub_D fun d hd _ => by
          have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (mem_sfLayer.mp hd).1
          have := Real.log_nonneg hd1
          positivity
      have hmA0 : 0 ≤ RHTower.Sieve.mertensA N := sum_nonneg fun p hp => by
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
        have := Real.log_nonneg hp1
        positivity
      calc ∑ d ∈ D, Real.log d / (d : ℝ)
          ≤ RHTower.Sieve.mertensA N * ∑ q ∈ sfLayer N j, 1 / (q : ℝ) :=
            hD_log.trans (sum_log_div_sfLayer_succ_le N j)
        _ ≤ 4 * Real.log R * ((Real.log (Real.log R) + c₀) ^ j / (j.factorial : ℝ)) :=
            mul_le_mul hmA hj_sum (sum_nonneg fun _ _ => by positivity) (by positivity)
        _ = 4 * Real.log R * (Real.log (Real.log R) + c₀) ^ j / (j.factorial : ℝ) := by ring
    have hterm : ∀ d ∈ D, ((windowPrimes (u / d) (v / d)).card : ℝ) ≤
        (1 + 1 / 100) * ((v - u) / Real.log R) * (1 / d) +
          2 * ((m' : ℝ) + 1) * (v - u) / Real.log R ^ 2 * (Real.log d / d) := by
      intro d hd
      obtain ⟨hd_sf, hdpow⟩ := mem_filter.mp hd
      have hd1 := (mem_sfLayer.mp hd_sf).1
      have h := card_windowPrimes_div_divisor_le hC hT hθ hR0 hRT hLm2 hRu huv hv hd1 hdpow
      have hd_inv0 : (0 : ℝ) ≤ 1 / d := by positivity
      have herr := mul_le_mul_of_nonneg_right hκ_err hd_inv0
      linarith
    set X_ll : ℝ := Real.log (Real.log R) + c₀
    have hX_ll0 : 0 ≤ X_ll := hmS0.trans hmS
    have hC_sub0 : 0 ≤ C_sub := by positivity
    have hfac_rel : (m'.factorial : ℝ) = (m' : ℝ) * (j.factorial : ℝ) := by
      simp [m', Nat.factorial_succ]
    have hlog2_term :
        2 * ((m' : ℝ) + 1) * (v - u) / Real.log R ^ 2 *
            (4 * Real.log R * X_ll ^ j / (j.factorial : ℝ)) =
          (v - u) / ((m'.factorial : ℝ) * Real.log R) * (C_sub * X_ll ^ j) := by
      have hj_ne : (j.factorial : ℝ) ≠ 0 := by positivity
      have hm'_ne : (m' : ℝ) ≠ 0 := by positivity
      rw [hfac_rel]
      simp only [C_sub]
      field_simp
      ring
    have hbinom : (1 + 1 / 100) * X_ll ^ m' + C_sub * X_ll ^ j ≤
        (1 + 1 / 100) * (X_ll + C_sub) ^ m' := by
      have h1 : X_ll ^ m' + C_sub * X_ll ^ j ≤ (X_ll + C_sub) ^ m' := by
        calc X_ll ^ m' + C_sub * X_ll ^ j
            = (X_ll + C_sub) * X_ll ^ j := by simp [m', pow_succ']; ring
          _ ≤ (X_ll + C_sub) * (X_ll + C_sub) ^ j := by gcongr; linarith
          _ = (X_ll + C_sub) ^ m' := by simp [m', pow_succ']
      have hpow_nn : 0 ≤ C_sub * X_ll ^ j := by positivity
      nlinarith
    calc ((kPrimesIn (m' + 1) u v).card : ℝ)
        ≤ ∑ d ∈ D, ((windowPrimes (u / d) (v / d)).card : ℝ) := by exact_mod_cast hcard_le
      _ ≤ ∑ d ∈ D, ((1 + 1 / 100) * ((v - u) / Real.log R) * (1 / d) +
            2 * ((m' : ℝ) + 1) * (v - u) / Real.log R ^ 2 * (Real.log d / d)) :=
          sum_le_sum hterm
      _ = (1 + 1 / 100) * ((v - u) / Real.log R) * (∑ d ∈ D, 1 / (d : ℝ)) +
            2 * ((m' : ℝ) + 1) * (v - u) / Real.log R ^ 2 *
              (∑ d ∈ D, Real.log d / (d : ℝ)) := by
          rw [sum_add_distrib, mul_sum, mul_sum]
      _ ≤ (1 + 1 / 100) * ((v - u) / Real.log R) * (X_ll ^ m' / (m'.factorial : ℝ)) +
            2 * ((m' : ℝ) + 1) * (v - u) / Real.log R ^ 2 *
              (4 * Real.log R * X_ll ^ j / (j.factorial : ℝ)) := by
          gcongr
      _ = (v - u) / ((m'.factorial : ℝ) * Real.log R) *
            ((1 + 1 / 100) * X_ll ^ m' + C_sub * X_ll ^ j) := by
          rw [hlog2_term]; ring
      _ ≤ (v - u) / ((m'.factorial : ℝ) * Real.log R) *
            ((1 + 1 / 100) * (X_ll + C_sub) ^ m') :=
          mul_le_mul_of_nonneg_left hbinom (by positivity)
      _ = (1 + 1 / 100) * (v - u) / ((m'.factorial : ℝ) * Real.log R) *
            (Real.log (Real.log R) + (c₀ + C_sub)) ^ m' := by
          simp only [X_ll, add_assoc]; ring

/-! ### 3. `{2, 3, 5}`-cofactor `(m + 2)`-prime supply and single-layer cellwise matching -/

/-- `(m + 2)`-prime `{2, 3, 5}`-cofactor targets `q · (∏_{p ∈ T} p) · r ∈ (u, v]` with
`q ∈ {2, 3, 5}`, `T ∈ (largePrimesLE M).powersetCard m`, and `r` prime. -/
def layerTargets (m M : ℕ) (u v : ℝ) : Finset ℕ :=
  ({2, 3, 5} : Finset ℕ).biUnion fun q =>
    ((largePrimesLE M).powersetCard m).biUnion fun T =>
      (windowPrimes (u / (q * ∏ p ∈ T, p)) (v / (q * ∏ p ∈ T, p))).image
        fun r => q * (∏ p ∈ T, p) * r

theorem factor_structure_of_layerTarget {m M q r : ℕ} {T : Finset ℕ} {u v : ℝ}
    (hM5 : 5 < M) (hMu : 5 * (M : ℝ) ^ (m + 1) ≤ u) (huv : u ≤ v)
    (hq : q ∈ ({2, 3, 5} : Finset ℕ)) (hT : T ∈ (largePrimesLE M).powersetCard m)
    (hr : r ∈ windowPrimes (u / (q * ∏ p ∈ T, p)) (v / (q * ∏ p ∈ T, p))) :
    let d := ∏ p ∈ T, p
    let n := q * d * r
    q.Prime ∧ r.Prime ∧ M < r ∧ Squarefree d ∧ d.primeFactors = T ∧
      Squarefree n ∧ n.primeFactors = insert q (insert r T) ∧
      n.primeFactors.card = m + 2 ∧
      n.primeFactors.filter (· ≤ 5) = {q} ∧
      n.primeFactors.filter (fun p => 5 < p ∧ p ≤ M) = T ∧
      u < n ∧ (n : ℝ) ≤ v := by
  dsimp only
  obtain ⟨hqp, hq2, hq5⟩ := small_cofactor_cases hq
  obtain ⟨hTP, hTcard⟩ := mem_powersetCard.mp hT
  have hT_info : ∀ p ∈ T, p.Prime ∧ 5 < p ∧ p ≤ M := fun p hp => by
    have hmem := hTP hp
    obtain ⟨hpM, hpp⟩ := Nat.mem_primesLE.mp (mem_filter.mp hmem).1
    exact ⟨hpp, (mem_filter.mp hmem).2, hpM⟩
  obtain ⟨hsq_d, hpf_d, hd_pos⟩ := squarefree_and_primeFactors_prod_primes
    (fun p hp => (hT_info p hp).1)
  set d := ∏ p ∈ T, p
  have hd_le : d ≤ M ^ m := by
    rw [← hTcard]
    exact prod_le_pow_card_of_le fun p hp => (hT_info p hp).2.2
  have hqd_pos : (0 : ℝ) < q * d := by
    have : 0 < q * d := Nat.mul_pos hqp.pos hd_pos
    exact_mod_cast this
  have hu0 : 0 ≤ u := by
    have : (0 : ℝ) ≤ 5 * (M : ℝ) ^ (m + 1) := by positivity
    linarith
  obtain ⟨hrp, hlt, hle⟩ := (mem_windowPrimes (by positivity)
    (div_nonneg (hu0.trans huv) hqd_pos.le)).mp hr
  have hlt' : u < (q * d * r : ℕ) := by
    rw [div_lt_iff₀ hqd_pos] at hlt
    push_cast; linarith
  have hle' : ((q * d * r : ℕ) : ℝ) ≤ v := by
    rw [le_div_iff₀ hqd_pos] at hle
    push_cast; linarith
  have hMr : M < r := by
    have hqdM : (q : ℝ) * d * M ≤ u := by
      have hq5' : (q : ℝ) ≤ 5 := by exact_mod_cast hq5
      have hdM : (d : ℝ) * M ≤ (M : ℝ) ^ (m + 1) := by
        rw [pow_succ]
        have : (d : ℝ) ≤ (M : ℝ) ^ m := by exact_mod_cast hd_le
        gcongr
      calc (q : ℝ) * d * M = (q : ℝ) * ((d : ℝ) * M) := by ring
        _ ≤ 5 * (M : ℝ) ^ (m + 1) := by gcongr
        _ ≤ u := hMu
    have hMr' : (M : ℝ) < r := by
      by_contra hcon
      push Not at hcon
      have : ((q * d * r : ℕ) : ℝ) ≤ (q : ℝ) * d * M := by push_cast; gcongr
      linarith
    exact_mod_cast hMr'
  have hr_not_T : r ∉ T := fun hmem => by have := (hT_info r hmem).2.2; omega
  have hq_not_T : q ∉ T := fun hmem => by have := (hT_info q hmem).2.1; omega
  have hqr_ne : q ≠ r := by omega
  have hcop_qd : Nat.Coprime q d :=
    Nat.Coprime.prod_right fun p hp =>
      (Nat.coprime_primes hqp (hT_info p hp).1).mpr fun heq => hq_not_T (heq ▸ hp)
  have hcop_qdr : Nat.Coprime (q * d) r :=
    Nat.Coprime.mul_left ((Nat.coprime_primes hqp hrp).mpr hqr_ne)
      (Nat.Coprime.prod_left fun p hp =>
        (Nat.coprime_primes (hT_info p hp).1 hrp).mpr fun heq => hr_not_T (heq ▸ hp))
  have hsq_qd : Squarefree (q * d) :=
    Nat.squarefree_mul_iff.mpr ⟨hcop_qd, Irreducible.squarefree hqp, hsq_d⟩
  have hsq_n : Squarefree (q * d * r) :=
    Nat.squarefree_mul_iff.mpr ⟨hcop_qdr, hsq_qd, Irreducible.squarefree hrp⟩
  have hpf_n : (q * d * r).primeFactors = insert q (insert r T) := by
    rw [Nat.primeFactors_mul (Nat.mul_pos hqp.pos hd_pos).ne' hrp.ne_zero,
      Nat.primeFactors_mul hqp.ne_zero hd_pos.ne', hqp.primeFactors, hrp.primeFactors, hpf_d]
    ext x; simp only [mem_union, mem_singleton, mem_insert]; tauto
  have hcard_n : (q * d * r).primeFactors.card = m + 2 := by
    rw [hpf_n, card_insert_of_notMem (by simp [hqr_ne, hq_not_T]),
      card_insert_of_notMem hr_not_T, hTcard]
  have hfil_q : (insert q (insert r T)).filter (· ≤ 5) = {q} := by
    ext x
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro (⟨rfl, _⟩ | ⟨rfl, hx5⟩ | ⟨hxT, hx5⟩)
      · rfl
      · omega
      · have := (hT_info x hxT).2.1; omega
    · rintro rfl; exact ⟨Or.inl rfl, hq5⟩
  have hfil_T : (insert q (insert r T)).filter (fun p => 5 < p ∧ p ≤ M) = T := by
    ext x
    simp only [mem_filter, mem_insert]
    constructor
    · rintro (⟨rfl, hx⟩ | ⟨rfl, hx⟩ | ⟨hxT, _⟩)
      · omega
      · omega
      · exact hxT
    · intro hxT
      exact ⟨Or.inr (Or.inr hxT), (hT_info x hxT).2.1, (hT_info x hxT).2.2⟩
  rw [hpf_n]
  exact ⟨hqp, hrp, hMr, hsq_d, hpf_d, hsq_n, rfl, hcard_n, hfil_q, hfil_T, hlt', hle'⟩

theorem mem_layerTargets {m M : ℕ} {u v : ℝ} (hM5 : 5 < M)
    (hMu : 5 * (M : ℝ) ^ (m + 1) ≤ u) (huv : u ≤ v) {n : ℕ}
    (hn : n ∈ layerTargets m M u v) :
    u < n ∧ (n : ℝ) ≤ v ∧ Squarefree n ∧ n.primeFactors.card = m + 2 ∧
      ∃ q d r : ℕ, (q = 2 ∨ q = 3 ∨ q = 5) ∧ r.Prime ∧ 5 < r ∧
        Squarefree d ∧ d.primeFactors.card = m ∧ n = q * d * r := by
  unfold layerTargets at hn
  obtain ⟨q, hq, hn1⟩ := mem_biUnion.mp hn
  obtain ⟨T, hT, hn2⟩ := mem_biUnion.mp hn1
  obtain ⟨r, hr, rfl⟩ := mem_image.mp hn2
  have hf := factor_structure_of_layerTarget hM5 hMu huv hq hT hr
  obtain ⟨_, hrp, hMr, hsq_d, hpf_d, hsq_n, _, hcard_n, _, _, hlt, hle⟩ := hf
  refine ⟨hlt, hle, hsq_n, hcard_n, q, ∏ p ∈ T, p, r, by simpa using hq, hrp, by omega,
    hsq_d, ?_, rfl⟩
  rw [hpf_d, (mem_powersetCard.mp hT).2]

theorem card_layerTargets {m M : ℕ} {u v : ℝ} (hM5 : 5 < M)
    (hMu : 5 * (M : ℝ) ^ (m + 1) ≤ u) (huv : u ≤ v) :
    (layerTargets m M u v).card =
      ∑ q ∈ ({2, 3, 5} : Finset ℕ),
        ∑ T ∈ (largePrimesLE M).powersetCard m,
          (windowPrimes (u / (q * ∏ p ∈ T, p)) (v / (q * ∏ p ∈ T, p))).card := by
  unfold layerTargets
  rw [card_biUnion]
  · refine sum_congr rfl fun q hq => ?_
    rw [card_biUnion]
    · refine sum_congr rfl fun T hT => card_image_of_injOn fun r₁ _ r₂ _ heq => ?_
      have hqp := (small_cofactor_cases hq).1
      have hd_pos : 0 < ∏ p ∈ T, p :=
        (squarefree_and_primeFactors_prod_primes fun p hp =>
          (Nat.mem_primesLE.mp (mem_filter.mp ((mem_powersetCard.mp hT).1 hp)).1).2).2.2
      exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hqp.pos hd_pos) heq
    · intro T₁ hT₁ T₂ hT₂ hne
      simp only [Function.onFun]
      rw [disjoint_left]
      intro n hn₁ hn₂
      obtain ⟨r₁, hr₁, rfl⟩ := mem_image.mp hn₁
      obtain ⟨r₂, hr₂, heq⟩ := mem_image.mp hn₂
      have hf₁ := (factor_structure_of_layerTarget hM5 hMu huv hq hT₁ hr₁).2.2.2.2.2.2.2.2.2.1
      have hf₂ := (factor_structure_of_layerTarget hM5 hMu huv hq hT₂ hr₂).2.2.2.2.2.2.2.2.2.1
      exact hne (hf₁.symm.trans (heq ▸ hf₂)).symm
  · intro q₁ hq₁ q₂ hq₂ hne
    simp only [Function.onFun]
    rw [disjoint_left]
    intro n hn₁ hn₂
    obtain ⟨T₁, hT₁, hn₁'⟩ := mem_biUnion.mp hn₁
    obtain ⟨r₁, hr₁, rfl⟩ := mem_image.mp hn₁'
    obtain ⟨T₂, hT₂, hn₂'⟩ := mem_biUnion.mp hn₂
    obtain ⟨r₂, hr₂, heq⟩ := mem_image.mp hn₂'
    have hf₁ := (factor_structure_of_layerTarget hM5 hMu huv hq₁ hT₁ hr₁).2.2.2.2.2.2.2.2.1
    have hf₂ := (factor_structure_of_layerTarget hM5 hMu huv hq₂ hT₂ hr₂).2.2.2.2.2.2.2.2.1
    have hsing : ({q₂} : Finset ℕ) = {q₁} := hf₂.symm.trans (heq ▸ hf₁)
    exact hne (singleton_injective hsing).symm

/-- Lower bound on `(m + 2)`-prime `{2, 3, 5}`-targets across all log-power cells `(u, v] ⊆ [R, 2R]`. -/
theorem exists_card_layerTargets_ge (m : ℕ) (B : ℝ) :
    ∃ K₂ R₀ : ℝ, 80 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      let M := ⌊R ^ (1 / (2 * ((m : ℝ) + 1)))⌋₊
      5 < M ∧ 5 * (M : ℝ) ^ (m + 1) ≤ R ∧
      ∀ u v : ℝ, R ≤ u → u ≤ v → v ≤ 2 * R → R / Real.log R ^ B ≤ v - u →
        (61 / 60) * (v - u) / ((m.factorial : ℝ) * Real.log R) *
          (Real.log (Real.log R) - K₂) ^ m ≤
            ((layerTargets m M u v).card : ℝ) := by
  obtain ⟨A, hAB⟩ : ∃ A : ℕ, B + 1 ≤ A := ⟨⌈B⌉₊ + 1, by push_cast; linarith [Nat.le_ceil B]⟩
  obtain ⟨C, hC, T, hT, hθ⟩ := exists_abs_theta_sub_le A
  set ε : ℝ := 1 / 62
  have hε0 : 0 < ε := by norm_num
  set K₂ : ℝ :=
    RHTower.Sieve.mertensSecondLowerConst + 31 / 30 + Real.log (4 * ((m : ℝ) + 1)) + (m : ℝ)
  have hrpow_tendsto : Tendsto (fun R : ℝ => R ^ (1 / (2 * ((m : ℝ) + 1)))) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hev : ∀ᶠ R : ℝ in atTop,
      (5 * T) ^ 2 ≤ R ∧ 100 ≤ R ∧ 1 ≤ Real.log R ∧
      6 * Real.log 5 ≤ Real.log R ∧
      4 * C * 3 ^ A / ε ≤ Real.log R ∧
      (12 : ℝ) ≤ R ^ (1 / (2 * ((m : ℝ) + 1))) ∧
      K₂ + 1 ≤ Real.log (Real.log R) :=
    (eventually_ge_atTop _).and ((eventually_ge_atTop _).and
      ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and
        ((Real.tendsto_log_atTop.eventually_ge_atTop _).and
          ((Real.tendsto_log_atTop.eventually_ge_atTop _).and
            ((hrpow_tendsto.eventually_ge_atTop 12).and
              ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop _))))))
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  refine ⟨K₂, max X 80, le_max_right _ _, fun R hR => ?_⟩
  obtain ⟨hRT, hR100, hL1, hL5, hLC, hM12, hllK⟩ := hX R ((le_max_left _ _).trans hR)
  have hR0 : 0 < R := by linarith
  have hL0 : 0 < Real.log R := by linarith
  dsimp only
  set M := ⌊R ^ (1 / (2 * ((m : ℝ) + 1)))⌋₊
  have hM_ge : R ^ (1 / (2 * ((m : ℝ) + 1))) / 2 ≤ M := by
    have := Nat.lt_floor_add_one (R ^ (1 / (2 * ((m : ℝ) + 1))))
    linarith
  have hM5 : 5 < M := by
    have : (6 : ℝ) ≤ M := by linarith
    exact_mod_cast (show (5 : ℝ) < 6 by norm_num).trans_le this
  have hM_le : (M : ℝ) ≤ R ^ (1 / (2 * ((m : ℝ) + 1))) := Nat.floor_le (by positivity)
  have hM_pow : (M : ℝ) ^ (m + 1) ≤ R ^ ((1 : ℝ) / 2) := by
    calc (M : ℝ) ^ (m + 1)
        ≤ (R ^ (1 / (2 * ((m : ℝ) + 1)))) ^ (m + 1) := by gcongr
      _ = R ^ ((1 / (2 * ((m : ℝ) + 1))) * ((m : ℝ) + 1)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le]; push_cast; rfl
      _ = R ^ ((1 : ℝ) / 2) := by
          congr 1
          have : (m : ℝ) + 1 ≠ 0 := by positivity
          field_simp
  have h5_rpow : 5 * R ^ ((1 : ℝ) / 2) ≤ R := by
    have hsq : (5 * R ^ ((1 : ℝ) / 2)) ^ 2 ≤ R ^ 2 := by
      rw [mul_pow, ← Real.rpow_natCast (R ^ _), ← Real.rpow_mul hR0.le]
      norm_num
      rw [Real.rpow_one]
      nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hR0.le two_ne_zero).mp hsq
  have hMR : 5 * (M : ℝ) ^ (m + 1) ≤ R := by linarith
  refine ⟨hM5, hMR, fun u v hRu huv hv hgap => ?_⟩
  have hMu : 5 * (M : ℝ) ^ (m + 1) ≤ u := hMR.trans hRu
  have hvu : 0 ≤ v - u := by linarith
  -- Lower bound on each window `(u / (q d), v / (q d)]`
  have hRA : 4 * C * 3 ^ A * (R / Real.log R ^ A) ≤ ε * (v - u) := by
    have h2 : R / Real.log R ^ A ≤ R / Real.log R ^ B / Real.log R :=
      rpow_logPow_le hR0.le hL1 hAB
    have h3 : 4 * C * 3 ^ A * (R / Real.log R ^ B / Real.log R) ≤ ε * (R / Real.log R ^ B) := by
      rw [div_le_iff₀ hε0] at hLC
      have hq : 0 ≤ R / Real.log R ^ B := by positivity
      rw [mul_div_assoc', div_le_iff₀ hL0]
      nlinarith
    have h4 : ε * (R / Real.log R ^ B) ≤ ε * (v - u) := by gcongr
    have : 0 ≤ 4 * C * 3 ^ A := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 this]
  have hwin : ∀ q ∈ ({2, 3, 5} : Finset ℕ), ∀ T ∈ (largePrimesLE M).powersetCard m,
      (1 - ε) * (v - u) / (q * Real.log R) * (1 / (∏ p ∈ T, (p : ℝ))) ≤
        ((windowPrimes (u / (q * ∏ p ∈ T, p)) (v / (q * ∏ p ∈ T, p))).card : ℝ) := by
    intro q hq T hT
    obtain ⟨hqp, hq2, hq5⟩ := small_cofactor_cases hq
    obtain ⟨hTP, hTcard⟩ := mem_powersetCard.mp hT
    set d : ℕ := ∏ p ∈ T, p
    have hd_pos : 0 < d :=
      (squarefree_and_primeFactors_prod_primes fun p hp =>
        (Nat.mem_primesLE.mp (mem_filter.mp (hTP hp)).1).2).2.2
    have hd_le : (d : ℝ) ≤ R ^ ((1 : ℝ) / 2) := by
      have hd_nat : d ≤ M ^ m := by
        rw [← hTcard]
        exact prod_le_pow_card_of_le fun p hp =>
          (Nat.mem_primesLE.mp (mem_filter.mp (hTP hp)).1).1
      have hMm : (M : ℝ) ^ m ≤ (M : ℝ) ^ (m + 1) :=
        pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ M by omega)) (Nat.le_succ m)
      exact (by exact_mod_cast hd_nat : (d : ℝ) ≤ (M : ℝ) ^ m).trans (hMm.trans hM_pow)
    have hqd_pos : (0 : ℝ) < (q : ℝ) * d := by
      have : 0 < q * d := Nat.mul_pos hqp.pos hd_pos
      exact_mod_cast this
    have hqd_le : (q : ℝ) * d ≤ 5 * R ^ ((1 : ℝ) / 2) := by
      have hq5' : (q : ℝ) ≤ 5 := by exact_mod_cast hq5
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      exact mul_le_mul hq5' hd_le hd0 (by norm_num)
    have hu_div : R ^ ((1 : ℝ) / 2) / 5 ≤ u / (q * d) := by
      rw [div_le_div_iff₀ (by norm_num) hqd_pos]
      have hprod : R ^ ((1 : ℝ) / 2) * R ^ ((1 : ℝ) / 2) = R := by
        rw [← Real.rpow_add hR0]; norm_num
      calc R ^ ((1 : ℝ) / 2) * ((q : ℝ) * d)
          ≤ R ^ ((1 : ℝ) / 2) * (5 * R ^ ((1 : ℝ) / 2)) := by gcongr
        _ = 5 * R := by linarith
        _ ≤ 5 * u := by linarith
        _ = u * 5 := by ring
    have haT : T ≤ u / (q * d) := by
      have hT_le : T ≤ R ^ ((1 : ℝ) / 2) / 5 := by
        rw [le_div_iff₀ (by norm_num)]
        have h1 : (5 * T) ^ 2 ≤ (R ^ ((1 : ℝ) / 2)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hR0.le]; norm_num; exact hRT
        have := (pow_le_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero).mp h1
        linarith
      exact hT_le.trans hu_div
    have hab : u / (q * d) ≤ v / (q * d) := by gcongr
    have hinc := abs_theta_increment_le hC.le hT hθ haT hab
    have hloga : Real.log R / 3 ≤ Real.log (u / (q * d)) := by
      have h1 : Real.log (R ^ ((1 : ℝ) / 2) / 5) ≤ Real.log (u / (q * d)) :=
        Real.log_le_log (by positivity) hu_div
      rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hR0] at h1
      linarith
    have hlogb : Real.log (v / (q * d)) ≤ Real.log R := by
      have hqd2 : (2 : ℝ) ≤ (q : ℝ) * d := by
        have : 2 ≤ q * d := by
          calc 2 = 2 * 1 := by norm_num
            _ ≤ q * d := Nat.mul_le_mul hq2 hd_pos
        exact_mod_cast this
      apply Real.log_le_log (by have : 0 < v := by linarith; positivity)
      rw [div_le_iff₀ hqd_pos]
      nlinarith
    have hLA0 : 0 < (Real.log R / 3) ^ A := by positivity
    have hLA : (Real.log R / 3) ^ A ≤ Real.log (u / (q * d)) ^ A := by gcongr
    have herr : 2 * C * (v / (q * d)) / Real.log (u / (q * d)) ^ A ≤
        1 / ((q : ℝ) * d) * (4 * C * 3 ^ A * (R / Real.log R ^ A)) := by
      calc 2 * C * (v / (q * d)) / Real.log (u / (q * d)) ^ A
          ≤ 2 * C * (v / (q * d)) / (Real.log R / 3) ^ A :=
            div_le_div_of_nonneg_left (by have : 0 ≤ v := by linarith; positivity) hLA0 hLA
        _ ≤ 2 * C * (2 * R / (q * d)) / (Real.log R / 3) ^ A := by gcongr
        _ = 1 / ((q : ℝ) * d) * (4 * C * 3 ^ A * (R / Real.log R ^ A)) := by
            rw [div_pow]; field_simp; ring
    have hθge : (1 - ε) * (v - u) / ((q : ℝ) * d) ≤
        Chebyshev.theta (v / (q * d)) - Chebyshev.theta (u / (q * d)) := by
      have h1 := (abs_le.mp hinc).1
      have e : v / (q * d) - u / (q * d) = (v - u) / ((q : ℝ) * d) := by ring
      have h2 : 1 / ((q : ℝ) * d) * (4 * C * 3 ^ A * (R / Real.log R ^ A)) ≤
          1 / ((q : ℝ) * d) * (ε * (v - u)) := by gcongr
      have e2 : (1 - ε) * (v - u) / ((q : ℝ) * d) =
          (v - u) / ((q : ℝ) * d) - 1 / ((q : ℝ) * d) * (ε * (v - u)) := by ring
      linarith
    have hcard := theta_sub_le_card_mul_log (show 0 ≤ u / (q * d) by positivity) hab
    have hc0 : (0 : ℝ) ≤ (windowPrimes (u / (q * d)) (v / (q * d))).card := Nat.cast_nonneg _
    have hmain : (1 - ε) * (v - u) / ((q : ℝ) * d) ≤
        ((windowPrimes (u / (q * d)) (v / (q * d))).card : ℝ) * Real.log R :=
      hθge.trans (hcard.trans (mul_le_mul_of_nonneg_left hlogb hc0))
    have hd_cast : (d : ℝ) = ∏ p ∈ T, (p : ℝ) := by simp [d]
    rw [← hd_cast]
    calc (1 - ε) * (v - u) / (q * Real.log R) * (1 / (d : ℝ))
        = (1 - ε) * (v - u) / ((q : ℝ) * d) / Real.log R := by field_simp
      _ ≤ ((windowPrimes (u / (q * d)) (v / (q * d))).card : ℝ) * Real.log R / Real.log R := by
          gcongr
      _ = ((windowPrimes (u / (q * (∏ p ∈ T, p))) (v / (q * (∏ p ∈ T, p)))).card : ℝ) := by
          have hcast_qd : ((q * ∏ p ∈ T, p : ℕ) : ℝ) = (q : ℝ) * d := by simp [d]
          field_simp; rfl
  -- Lower bound on `∑_{T} 1 / ∏ T`
  have hM2 : 2 ≤ M := by omega
  have hlogM : Real.log R / (4 * ((m : ℝ) + 1)) ≤ Real.log M := by
    have h1 : Real.log (R ^ (1 / (2 * ((m : ℝ) + 1))) / 2) ≤ Real.log M :=
      Real.log_le_log (by positivity) hM_ge
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hR0] at h1
    have hlog2_small : Real.log 2 ≤ Real.log R / (4 * ((m : ℝ) + 1)) := by
      -- Wait: check if `4 * (m + 1) * Real.log 2 ≤ Real.log R`!
      sorry
  sorry
