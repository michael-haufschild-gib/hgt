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
open RHTower RHTower.PrimeCells RHTower.CubicGamma
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.QuantitativeFactorizationMatching

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
      dsimp only at hd₁ hp₁ hd₂ hp₂
      have hm₁ := (div_prime_mem_sfLayer hd₁ hp₁).2.2
      have hm₂ := (div_prime_mem_sfLayer hd₂ hp₂).2.2
      simp only [emb, Prod.mk.injEq] at heq
      obtain ⟨rfl, hq_eq⟩ := heq
      have hd_eq : d₁ = d₂ := by rw [← hm₁, ← hm₂, hq_eq]
      subst hd_eq; rfl
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
            (sum_image (f := fun z : ℕ × ℕ => (1 / (z.1 : ℝ)) * (1 / (z.2 : ℝ))) hemb_inj).symm
        _ ≤ ∑ z ∈ Nat.primesLE N ×ˢ sfLayer N m, (1 / (z.1 : ℝ)) * (1 / (z.2 : ℝ)) :=
            sum_le_sum_of_subset_of_nonneg hemb_mem fun _ _ _ => by positivity
        _ = RHTower.Sieve.mertensS N * ∑ q ∈ sfLayer N m, 1 / (q : ℝ) := by
            rw [RHTower.Sieve.mertensS, sum_product, sum_mul]
            refine sum_congr rfl fun p _ => ?_
            dsimp only
            exact (mul_sum _ _ _).symm
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
    dsimp only at hd₁ hp₁ hd₂ hp₂
    have hm₁ := (div_prime_mem_sfLayer hd₁ hp₁).2.2
    have hm₂ := (div_prime_mem_sfLayer hd₂ hp₂).2.2
    simp only [emb, Prod.mk.injEq] at heq
    obtain ⟨rfl, hq_eq⟩ := heq
    have hd_eq : d₁ = d₂ := by rw [← hm₁, ← hm₂, hq_eq]
    subst hd_eq; rfl
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
        (sum_image (f := fun z : ℕ × ℕ => (Real.log z.1 / (z.1 : ℝ)) * (1 / (z.2 : ℝ))) hemb_inj).symm
    _ ≤ ∑ z ∈ Nat.primesLE N ×ˢ sfLayer N m,
          (Real.log z.1 / (z.1 : ℝ)) * (1 / (z.2 : ℝ)) :=
        sum_le_sum_of_subset_of_nonneg hemb_mem fun z hz _ => by
          obtain ⟨hp, _⟩ := mem_product.mp hz
          have hp1 : (1 : ℝ) ≤ z.1 := by exact_mod_cast (Nat.mem_primesLE.mp hp).2.pos
          have := Real.log_nonneg hp1
          positivity
    _ = RHTower.Sieve.mertensA N * ∑ q ∈ sfLayer N m, 1 / (q : ℝ) := by
        rw [RHTower.Sieve.mertensA, sum_product, sum_mul]
        refine sum_congr rfl fun p _ => ?_
        dsimp only
        exact (mul_sum _ _ _).symm

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
        dsimp only
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
        dsimp only at hp₁ hp₂
        simp only [Sigma.mk.inj_iff] at heq
        obtain ⟨hT_eq, rfl⟩ := heq
        have hU_eq : U₁ = U₂ := by
          rw [← insert_erase hp₁, ← insert_erase hp₂, hT_eq]
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
      refine pow_le_pow_left₀ hnn ?_ m
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
      ((sfLayer ⌊2 * R⌋₊ m).filter (fun d : ℕ => (d : ℝ) ^ (m + 1) ≤ (2 * R) ^ m)).biUnion
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
  have hu0 : 0 ≤ u := hR0.le.trans hRu
  have haT : T ≤ u / d := by
    have hTpow : T ^ (m + 1) ≤ (u / d) ^ (m + 1) := by
      have h1 : T ^ (m + 1) ≤ R / (2 : ℝ) ^ m := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      exact h1.trans hud_pow
    exact (pow_le_pow_iff_left₀ (by linarith) (div_nonneg hu0 hd0.le) (by omega)).mp hTpow
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
  have hvd0 : 0 ≤ (v - u) / d := div_nonneg (by linarith) hd0.le
  have hc1 : (v - u) / d / Real.log (u / d) ≤ (v - u) / d / (Real.log R - Real.log d) :=
    div_le_div_of_nonneg_left hvd0 hla0 hloga
  have hinv : 1 / (Real.log R - Real.log d) ≤
      1 / Real.log R + 2 * ((m : ℝ) + 1) * Real.log d / Real.log R ^ 2 := by
    have hld0 : 0 ≤ Real.log d := Real.log_nonneg hd1'
    rw [div_add_div _ _ hL0.ne' (by positivity), div_le_div_iff₀ hla0 (by positivity)]
    have hprod : 0 ≤ Real.log R * Real.log d *
        (2 * ((m : ℝ) + 1) * (Real.log R - Real.log d) - Real.log R) := by
      refine mul_nonneg (mul_nonneg hL0.le hld0) ?_
      have hgap' := hL_gap
      rw [div_le_iff₀ (by positivity)] at hgap'
      linarith
    nlinarith
  have hc1' : (v - u) / d / (Real.log R - Real.log d) ≤
      (v - u) / Real.log R * (1 / d) +
        2 * ((m : ℝ) + 1) * (v - u) / Real.log R ^ 2 * (Real.log d / d) := by
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
      have hl4 : Real.log 4 ≤ Real.log R :=
        (Real.log_le_log (by norm_num) (by norm_num : (4 : ℝ) ≤ 16)).trans
          (Real.log_le_log (by norm_num) hR16)
      unfold RHTower.Sieve.mertensA
      linarith
    let D := (sfLayer N m').filter (fun d : ℕ => (d : ℝ) ^ (m' + 1) ≤ (2 * R) ^ m')
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
            refine mul_le_mul_of_nonneg_right ?_ (div_nonneg hvu hL0.le)
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
  have hfil_q : (q * d * r).primeFactors.filter (· ≤ 5) = {q} := by
    rw [hpf_n]
    ext x
    simp only [mem_filter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨rfl | rfl | hxT, hx5⟩
      · rfl
      · omega
      · have := (hT_info x hxT).2.1; omega
    · rintro rfl; exact ⟨Or.inl rfl, hq5⟩
  have hfil_T : (q * d * r).primeFactors.filter (fun p => 5 < p ∧ p ≤ M) = T := by
    rw [hpf_n]
    ext x
    simp only [mem_filter, mem_insert]
    constructor
    · rintro ⟨rfl | rfl | hxT, hx⟩
      · omega
      · omega
      · exact hxT
    · intro hxT
      exact ⟨Or.inr (Or.inr hxT), (hT_info x hxT).2.1, (hT_info x hxT).2.2⟩
  exact ⟨hqp, hrp, hMr, hsq_d, hpf_d, hsq_n, hpf_n, hcard_n, hfil_q, hfil_T, hlt', hle'⟩

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
      exact hne (hf₁.symm.trans (heq ▸ hf₂))
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

/-- One `(q, d)` window of the `(m + 2)`-prime `{2, 3, 5}` supply:
`#{r ∈ (u/(qd), v/(qd)]} ≥ (1 - ε)(v - u)/(q log R) · (1 / d)`. -/
private theorem card_windowPrimes_layerTarget_ge {C T₀ ε : ℝ} {A : ℕ}
    (hC : 0 < C) (hT₀ : 3 ≤ T₀)
    (hθ : ∀ t : ℝ, T₀ ≤ t → |Chebyshev.theta t - t| ≤ C * t / Real.log t ^ A)
    {R u v : ℝ} (hR0 : 0 < R) (hRT : (5 * T₀) ^ 2 ≤ R) (hL0 : 0 < Real.log R)
    (hL5 : 6 * Real.log 5 ≤ Real.log R)
    (hRu : R ≤ u) (huv : u ≤ v) (hv : v ≤ 2 * R)
    (hRA : 4 * C * 3 ^ A * (R / Real.log R ^ A) ≤ ε * (v - u))
    {q d : ℕ} (hq2 : 2 ≤ q) (hq5 : q ≤ 5) (hd_pos : 0 < d)
    (hd_le : (d : ℝ) ≤ R ^ ((1 : ℝ) / 2)) :
    (1 - ε) * (v - u) / ((q : ℝ) * Real.log R) * (1 / (d : ℝ)) ≤
      ((windowPrimes (u / ((q : ℝ) * d)) (v / ((q : ℝ) * d))).card : ℝ) := by
  have hqp_pos : 0 < q := by omega
  have hqd_pos : (0 : ℝ) < (q : ℝ) * d := by
    have : 0 < q * d := Nat.mul_pos hqp_pos hd_pos
    exact_mod_cast this
  have hqd_le : (q : ℝ) * d ≤ 5 * R ^ ((1 : ℝ) / 2) := by
    have hq5' : (q : ℝ) ≤ 5 := by exact_mod_cast hq5
    exact mul_le_mul hq5' hd_le (Nat.cast_nonneg d) (by norm_num)
  have hu_div : R ^ ((1 : ℝ) / 2) / 5 ≤ u / ((q : ℝ) * d) := by
    rw [div_le_div_iff₀ (by norm_num) hqd_pos]
    have hprod : R ^ ((1 : ℝ) / 2) * R ^ ((1 : ℝ) / 2) = R := by
      rw [← Real.rpow_add hR0]; norm_num
    calc R ^ ((1 : ℝ) / 2) * ((q : ℝ) * d)
        ≤ R ^ ((1 : ℝ) / 2) * (5 * R ^ ((1 : ℝ) / 2)) := by gcongr
      _ = 5 * R := by linarith
      _ ≤ 5 * u := by linarith
      _ = u * 5 := by ring
  have haT : T₀ ≤ u / ((q : ℝ) * d) := by
    have hT_le : T₀ ≤ R ^ ((1 : ℝ) / 2) / 5 := by
      rw [le_div_iff₀ (by norm_num)]
      have h1 : (5 * T₀) ^ 2 ≤ (R ^ ((1 : ℝ) / 2)) ^ 2 := by
        rw [← Real.rpow_natCast (R ^ ((1 : ℝ) / 2)), ← Real.rpow_mul hR0.le]
        norm_num; exact hRT
      have := (pow_le_pow_iff_left₀ (by linarith) (by positivity) two_ne_zero).mp h1
      linarith
    exact hT_le.trans hu_div
  have hab : u / ((q : ℝ) * d) ≤ v / ((q : ℝ) * d) := by gcongr
  have hinc := abs_theta_increment_le hC.le hT₀ hθ haT hab
  have hloga : Real.log R / 3 ≤ Real.log (u / ((q : ℝ) * d)) := by
    have h1 : Real.log (R ^ ((1 : ℝ) / 2) / 5) ≤ Real.log (u / ((q : ℝ) * d)) :=
      Real.log_le_log (by positivity) hu_div
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hR0] at h1
    linarith
  have hlogb : Real.log (v / ((q : ℝ) * d)) ≤ Real.log R := by
    have hqd2 : (2 : ℝ) ≤ (q : ℝ) * d := by
      have : 2 ≤ q * d := Nat.mul_le_mul hq2 hd_pos
      exact_mod_cast this
    apply Real.log_le_log (div_pos (by linarith) hqd_pos)
    rw [div_le_iff₀ hqd_pos]
    nlinarith
  have hLA0 : 0 < (Real.log R / 3) ^ A := by positivity
  have hLA : (Real.log R / 3) ^ A ≤ Real.log (u / ((q : ℝ) * d)) ^ A := by gcongr
  have herr : 2 * C * (v / ((q : ℝ) * d)) / Real.log (u / ((q : ℝ) * d)) ^ A ≤
      1 / ((q : ℝ) * d) * (4 * C * 3 ^ A * (R / Real.log R ^ A)) := by
    calc 2 * C * (v / ((q : ℝ) * d)) / Real.log (u / ((q : ℝ) * d)) ^ A
        ≤ 2 * C * (v / ((q : ℝ) * d)) / (Real.log R / 3) ^ A :=
          div_le_div_of_nonneg_left
            (mul_nonneg (by positivity) (div_nonneg (by linarith) hqd_pos.le)) hLA0 hLA
      _ ≤ 2 * C * (2 * R / ((q : ℝ) * d)) / (Real.log R / 3) ^ A := by gcongr
      _ = 1 / ((q : ℝ) * d) * (4 * C * 3 ^ A * (R / Real.log R ^ A)) := by
          rw [div_pow]; field_simp; ring
  have hθge : (1 - ε) * (v - u) / ((q : ℝ) * d) ≤
      Chebyshev.theta (v / ((q : ℝ) * d)) - Chebyshev.theta (u / ((q : ℝ) * d)) := by
    have h1 := (abs_le.mp hinc).1
    have e : v / ((q : ℝ) * d) - u / ((q : ℝ) * d) = (v - u) / ((q : ℝ) * d) := by ring
    have h2 : 1 / ((q : ℝ) * d) * (4 * C * 3 ^ A * (R / Real.log R ^ A)) ≤
        1 / ((q : ℝ) * d) * (ε * (v - u)) := by gcongr
    have e2 : (1 - ε) * (v - u) / ((q : ℝ) * d) =
        (v - u) / ((q : ℝ) * d) - 1 / ((q : ℝ) * d) * (ε * (v - u)) := by ring
    linarith
  have hcard := theta_sub_le_card_mul_log (div_nonneg (by linarith) hqd_pos.le) hab
  have hc0 : (0 : ℝ) ≤ (windowPrimes (u / ((q : ℝ) * d)) (v / ((q : ℝ) * d))).card :=
    Nat.cast_nonneg _
  have hmain : (1 - ε) * (v - u) / ((q : ℝ) * d) ≤
      ((windowPrimes (u / ((q : ℝ) * d)) (v / ((q : ℝ) * d))).card : ℝ) * Real.log R :=
    hθge.trans (hcard.trans (mul_le_mul_of_nonneg_left hlogb hc0))
  calc (1 - ε) * (v - u) / ((q : ℝ) * Real.log R) * (1 / (d : ℝ))
      = (1 - ε) * (v - u) / ((q : ℝ) * d) / Real.log R := by
        rw [div_mul_div_comm, mul_one, div_div]
        congr 1; ring
    _ ≤ ((windowPrimes (u / ((q : ℝ) * d)) (v / ((q : ℝ) * d))).card : ℝ) := by
        rwa [div_le_iff₀ hL0]

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
  obtain ⟨C, hC, T₀, hT₀, hθ⟩ := exists_abs_theta_sub_le A
  obtain ⟨K₂, hK₂⟩ : ∃ K₂ : ℝ,
    K₂ = RHTower.Sieve.mertensSecondLowerConst + 31 / 30 +
      Real.log (4 * ((m : ℝ) + 1)) + (m : ℝ) := ⟨_, rfl⟩
  have hrpow_tendsto : Tendsto (fun R : ℝ => R ^ (1 / (2 * ((m : ℝ) + 1)))) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hev : ∀ᶠ R : ℝ in atTop,
      (5 * T₀) ^ 2 ≤ R ∧ 100 ≤ R ∧ 1 ≤ Real.log R ∧
      6 * Real.log 5 ≤ Real.log R ∧
      4 * C * 3 ^ A * 62 ≤ Real.log R ∧
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
  obtain ⟨M, hM_def⟩ : ∃ M : ℕ, M = ⌊R ^ (1 / (2 * ((m : ℝ) + 1)))⌋₊ := ⟨_, rfl⟩
  rw [← hM_def]
  have hM_ge : R ^ (1 / (2 * ((m : ℝ) + 1))) / 2 ≤ M := by
    rw [hM_def]
    have := Nat.lt_floor_add_one (R ^ (1 / (2 * ((m : ℝ) + 1))))
    linarith
  have hM5 : 5 < M := by
    have : (6 : ℝ) ≤ M := by linarith
    exact_mod_cast (show (5 : ℝ) < 6 by norm_num).trans_le this
  have hM_le : (M : ℝ) ≤ R ^ (1 / (2 * ((m : ℝ) + 1))) := by
    rw [hM_def]; exact Nat.floor_le (by positivity)
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
      norm_num; nlinarith
    exact (pow_le_pow_iff_left₀ (by positivity) hR0.le two_ne_zero).mp hsq
  have hMR : 5 * (M : ℝ) ^ (m + 1) ≤ R := by linarith
  refine ⟨hM5, hMR, fun u v hRu huv hv hgap => ?_⟩
  have hMu : 5 * (M : ℝ) ^ (m + 1) ≤ u := hMR.trans hRu
  have hvu : 0 ≤ v - u := by linarith
  have hRA : 4 * C * 3 ^ A * (R / Real.log R ^ A) ≤ (1 / 62 : ℝ) * (v - u) := by
    have h2 : R / Real.log R ^ A ≤ R / Real.log R ^ B / Real.log R :=
      rpow_logPow_le hR0.le hL1 hAB
    have h3 : 4 * C * 3 ^ A * (R / Real.log R ^ B / Real.log R) ≤
        (1 / 62 : ℝ) * (R / Real.log R ^ B) := by
      have hq : 0 ≤ R / Real.log R ^ B := by positivity
      rw [mul_div_assoc', div_le_iff₀ hL0]
      have := mul_le_mul_of_nonneg_right hLC hq
      linarith
    have h4 : (1 / 62 : ℝ) * (R / Real.log R ^ B) ≤ (1 / 62 : ℝ) * (v - u) := by gcongr
    have : 0 ≤ 4 * C * 3 ^ A := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 this]
  -- Lower bound on `∑_{T} 1 / ∏ T`
  have hM2 : 2 ≤ M := by omega
  have hlogM : Real.log R / (4 * ((m : ℝ) + 1)) ≤ Real.log M := by
    have h1 : Real.log (R ^ (1 / (2 * ((m : ℝ) + 1))) / 2) ≤ Real.log M :=
      Real.log_le_log (by positivity) hM_ge
    rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hR0] at h1
    have hlog12 : Real.log 12 ≤ 1 / (2 * ((m : ℝ) + 1)) * Real.log R := by
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 12) hM12
      rwa [Real.log_rpow hR0] at this
    have hlog2_le : 2 * Real.log 2 ≤ Real.log 12 := by
      have h4 : (2 : ℝ) * Real.log 2 = Real.log 4 := by
        rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]; ring
      rw [h4]
      exact Real.log_le_log (by norm_num) (by norm_num)
    have hhalf : 1 / (2 * ((m : ℝ) + 1)) * Real.log R =
        2 * (Real.log R / (4 * ((m : ℝ) + 1))) := by
      have : (m : ℝ) + 1 ≠ 0 := by positivity
      field_simp; ring
    linarith
  have hS_ge : Real.log (Real.log R) - K₂ + (m : ℝ) ≤
      ∑ p ∈ largePrimesLE M, 1 / (p : ℝ) := by
    have h1 := RHTower.Sieve.le_mertensS hM2
    have h2 := sum_largePrimesLE_ge M
    have h3 : Real.log (Real.log R / (4 * ((m : ℝ) + 1))) ≤ RHTower.Sieve.logLog M :=
      Real.log_le_log (by positivity) hlogM
    rw [Real.log_div hL0.ne' (by positivity)] at h3
    unfold RHTower.Sieve.mertensS at h1
    rw [hK₂]
    linarith
  have hm_le_S : (m : ℝ) ≤ ∑ p ∈ largePrimesLE M, 1 / (p : ℝ) := by linarith
  have hP1 : ∀ p ∈ largePrimesLE M, 1 ≤ p := fun p hp => by
    have := (mem_filter.mp hp).2; omega
  have hfac_pos : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos _
  have hsum_T_ge : (Real.log (Real.log R) - K₂) ^ m / (m.factorial : ℝ) ≤
      ∑ T ∈ (largePrimesLE M).powersetCard m, (1 / (∏ p ∈ T, (p : ℝ))) := by
    rw [div_le_iff₀ hfac_pos, mul_comm]
    have hpow_mono : (Real.log (Real.log R) - K₂) ^ m ≤
        ((∑ p ∈ largePrimesLE M, 1 / (p : ℝ)) - m) ^ m :=
      pow_le_pow_left₀ (by linarith) (by linarith) m
    exact hpow_mono.trans (le_factorial_mul_sum_inv_prod_powersetCard hP1 m hm_le_S)
  have hq_each : ∀ q ∈ ({2, 3, 5} : Finset ℕ),
      ((61 / 62 : ℝ) / q) *
          ((v - u) / ((m.factorial : ℝ) * Real.log R) * (Real.log (Real.log R) - K₂) ^ m) ≤
        ((∑ T ∈ (largePrimesLE M).powersetCard m,
          (windowPrimes (u / (q * ∏ p ∈ T, p)) (v / (q * ∏ p ∈ T, p))).card : ℕ) : ℝ) := by
    intro q hq
    obtain ⟨hqp, hq2, hq5⟩ := small_cofactor_cases hq
    have hq_pos : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    have hcoef_eq : ((61 / 62 : ℝ) / q) *
        ((v - u) / ((m.factorial : ℝ) * Real.log R) * (Real.log (Real.log R) - K₂) ^ m) =
      ((61 / 62 : ℝ) * (v - u) / ((q : ℝ) * Real.log R)) *
        ((Real.log (Real.log R) - K₂) ^ m / (m.factorial : ℝ)) := by
      simp only [div_eq_mul_inv, mul_inv]; ring
    rw [hcoef_eq, Nat.cast_sum]
    calc ((61 / 62 : ℝ) * (v - u) / ((q : ℝ) * Real.log R)) *
            ((Real.log (Real.log R) - K₂) ^ m / (m.factorial : ℝ))
        ≤ ((61 / 62 : ℝ) * (v - u) / ((q : ℝ) * Real.log R)) *
            ∑ T ∈ (largePrimesLE M).powersetCard m, (1 / (∏ p ∈ T, (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hsum_T_ge
            (div_nonneg (mul_nonneg (by norm_num) hvu) (mul_nonneg hq_pos.le hL0.le))
      _ = ∑ T ∈ (largePrimesLE M).powersetCard m,
            ((61 / 62 : ℝ) * (v - u) / ((q : ℝ) * Real.log R)) * (1 / (∏ p ∈ T, (p : ℝ))) :=
          mul_sum _ _ _
      _ ≤ ∑ T ∈ (largePrimesLE M).powersetCard m,
            ((windowPrimes (u / (q * ∏ p ∈ T, p)) (v / (q * ∏ p ∈ T, p))).card : ℝ) := by
          refine sum_le_sum fun T hT => ?_
          obtain ⟨hTP, hTcard⟩ := mem_powersetCard.mp hT
          have hd_pos : 0 < ∏ p ∈ T, p :=
            (squarefree_and_primeFactors_prod_primes fun p hp =>
              (Nat.mem_primesLE.mp (mem_filter.mp (hTP hp)).1).2).2.2
          have hd_le : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ R ^ ((1 : ℝ) / 2) := by
            have hd_nat : ∏ p ∈ T, p ≤ M ^ m := by
              rw [← hTcard]
              exact prod_le_pow_card_of_le fun p hp =>
                (Nat.mem_primesLE.mp (mem_filter.mp (hTP hp)).1).1
            have hMm : (M : ℝ) ^ m ≤ (M : ℝ) ^ (m + 1) :=
              pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ M by omega)) (Nat.le_succ m)
            exact (by exact_mod_cast hd_nat : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ (M : ℝ) ^ m).trans
              (hMm.trans hM_pow)
          have hw := card_windowPrimes_layerTarget_ge hC hT₀ hθ hR0 hRT hL0 hL5 hRu huv hv
            hRA hq2 hq5 hd_pos hd_le
          have h1 : (1 - (1 / 62 : ℝ)) = (61 / 62 : ℝ) := by norm_num
          have hprod_cast : ((∏ p ∈ T, p : ℕ) : ℝ) = ∏ p ∈ T, (p : ℝ) := Nat.cast_prod _ _
          have hmul_cast : ((q * ∏ p ∈ T, p : ℕ) : ℝ) = (q : ℝ) * ((∏ p ∈ T, p : ℕ) : ℝ) :=
            Nat.cast_mul _ _
          rw [h1] at hw
          simpa only [hmul_cast, hprod_cast] using hw
  rw [card_layerTargets hM5 hMu huv, Nat.cast_sum]
  have h2_not : (2 : ℕ) ∉ ({3, 5} : Finset ℕ) := by decide
  have h3_not : (3 : ℕ) ∉ ({5} : Finset ℕ) := by decide
  rw [sum_insert h2_not, sum_insert h3_not, sum_singleton]
  have h2 := hq_each 2 (by decide)
  have h3 := hq_each 3 (by decide)
  have h5 := hq_each 5 (by decide)
  have hadd := add_le_add (add_le_add h2 h3) h5
  have hlhs :
      ((61 / 62 : ℝ) / (2 : ℕ)) *
          ((v - u) / ((m.factorial : ℝ) * Real.log R) * (Real.log (Real.log R) - K₂) ^ m) +
        ((61 / 62 : ℝ) / (3 : ℕ)) *
          ((v - u) / ((m.factorial : ℝ) * Real.log R) * (Real.log (Real.log R) - K₂) ^ m) +
        ((61 / 62 : ℝ) / (5 : ℕ)) *
          ((v - u) / ((m.factorial : ℝ) * Real.log R) * (Real.log (Real.log R) - K₂) ^ m) =
      (61 / 60) * (v - u) / ((m.factorial : ℝ) * Real.log R) *
        (Real.log (Real.log R) - K₂) ^ m := by
    push_cast
    ring
  rw [hlhs] at hadd
  simpa only [add_assoc] using hadd

private theorem bernoulli_one_sub {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    ∀ m : ℕ, 1 - (m : ℝ) * δ ≤ (1 - δ) ^ m
  | 0 => by simp
  | m + 1 => by
    have hih := bernoulli_one_sub hδ0 hδ1 m
    have h1 : (1 - (m : ℝ) * δ) * (1 - δ) ≤ (1 - δ) ^ m * (1 - δ) :=
      mul_le_mul_of_nonneg_right hih (by linarith)
    rw [pow_succ]
    push_cast
    nlinarith [sq_nonneg δ]

/-- Single-layer cellwise injection from any subset `U ⊆ factorLayer (Ioc R (2R)) (m + 1)` into
`factorLayer (Ioc R (2R)) (m + 2)` via `{2, 3, 5}`-cofactor targets in the same log-power cell. -/
theorem exists_single_layer_cell_matching (m : ℕ) {B : ℝ} (hB : 0 < B) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ∀ U : Finset ℕ, U ⊆ factorLayer (Ioc R (2 * R)) (m + 1) →
        ∃ ψ : ℕ → ℕ, Set.InjOn ψ ↑U ∧
          U.image ψ ⊆ factorLayer (Ioc R (2 * R)) (m + 2) ∧
          ∀ n ∈ U, |(ψ n : ℝ) - n| ≤ 2 * R / Real.log R ^ B ∧
            ∃ q d r : ℕ, (q = 2 ∨ q = 3 ∨ q = 5) ∧ r.Prime ∧ 5 < r ∧
              Squarefree d ∧ d.primeFactors.card = m ∧ ψ n = q * d * r := by
  obtain ⟨K₁, R₁, _, hup⟩ := exists_card_kPrimesIn_le (m + 1) (by omega) B
  obtain ⟨K₂, R₂, _, hlow⟩ := exists_card_layerTargets_ge m B
  set A_gap : ℝ := |K₁| + |K₂| + 1
  have hev : ∀ᶠ R : ℝ in atTop,
      R₁ ≤ R ∧ R₂ ≤ R ∧ 80 ≤ R ∧ 1 ≤ Real.log R ∧
      |K₁| + 1 ≤ Real.log (Real.log R) ∧
      200 * ((m : ℝ) + 1) * A_gap + |K₁| ≤ Real.log (Real.log R) :=
    (eventually_ge_atTop _).and ((eventually_ge_atTop _).and
      ((eventually_ge_atTop _).and ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and
        (((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop _).and
          ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop _)))))
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  refine ⟨⌈X⌉₊, fun R hR U hU => ?_⟩
  classical
  have hRX : X ≤ (R : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast hR)
  obtain ⟨hR₁, hR₂, hR80, hL1, hll1, hll_big⟩ := hX R hRX
  obtain ⟨hM5, hMR, hlowR⟩ := hlow R hR₂
  set M := ⌊(R : ℝ) ^ (1 / (2 * ((m : ℝ) + 1)))⌋₊
  have hR0 : (0 : ℝ) < R := by linarith
  have hL0 : 0 < Real.log R := by linarith
  set x : ℝ := Real.log R ^ B
  have hx1 : 1 ≤ x := Real.one_le_rpow hL1 hB.le
  obtain ⟨hJ1, hhlow, hhup, hJh⟩ := cell_scale hR0 hx1
  set h : ℝ := (R : ℝ) / ⌊x⌋₊
  have hh0 : 0 < h := by positivity
  -- Compare `(1 + 1/100) * (ℓ + K₁)^m ≤ (61/60) * (ℓ - K₂)^m` via Bernoulli
  set ℓ : ℝ := Real.log (Real.log R)
  have hℓK1_pos : 1 ≤ ℓ + K₁ := by have := neg_abs_le K₁; linarith
  have hratio_pow : (1 + 1 / 100) * (ℓ + K₁) ^ m ≤ (61 / 60) * (ℓ - K₂) ^ m := by
    set δ : ℝ := 1 / (200 * ((m : ℝ) + 1))
    have hδ0 : 0 ≤ δ := by positivity
    have hδ1 : δ ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    have hstep_δ : (1 - δ) * (ℓ + K₁) ≤ ℓ - K₂ := by
      have hK_le : K₁ + K₂ ≤ A_gap := by
        simp only [A_gap]
        linarith [le_abs_self K₁, le_abs_self K₂]
      have hδ_mul : A_gap ≤ δ * (ℓ + K₁) := by
        simp only [δ, one_div_mul_eq_div]
        rw [le_div_iff₀ (by positivity)]
        have hK1_abs : -|K₁| ≤ K₁ := neg_abs_le K₁
        linarith
      linarith
    have hpow_step : (1 - δ) ^ m * (ℓ + K₁) ^ m ≤ (ℓ - K₂) ^ m := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (mul_nonneg (by linarith) (by linarith)) hstep_δ m
    have hbern : 199 / 200 ≤ (1 - δ) ^ m := by
      have hb := bernoulli_one_sub hδ0 hδ1 m
      have hmδ : (m : ℝ) * δ ≤ 1 / 200 := by
        simp only [δ]
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      linarith
    have hpos_pow : 0 ≤ (ℓ + K₁) ^ m := by positivity
    calc (1 + 1 / 100) * (ℓ + K₁) ^ m
        ≤ (61 / 60) * (199 / 200) * (ℓ + K₁) ^ m :=
          mul_le_mul_of_nonneg_right (by norm_num) hpos_pow
      _ ≤ (61 / 60) * ((1 - δ) ^ m * (ℓ + K₁) ^ m) := by
          have := mul_le_mul_of_nonneg_right hbern hpos_pow
          linarith
      _ ≤ (61 / 60) * (ℓ - K₂) ^ m := by gcongr
  have hcell : ∀ i < ⌊x⌋₊, (R : ℝ) ≤ R + i * h ∧ (R : ℝ) + i * h ≤ R + (i + 1) * h ∧
      (R : ℝ) + (i + 1) * h ≤ 2 * R ∧ (R : ℝ) / x ≤ R + (i + 1) * h - (R + i * h) := by
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ ⌊x⌋₊ := by exact_mod_cast hi
    have h1 : (0 : ℝ) ≤ i * h := by positivity
    have h2 : ((i : ℝ) + 1) * h ≤ ⌊x⌋₊ * h := by gcongr
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hU_mem : ∀ n ∈ U, (R : ℝ) < n ∧ (n : ℝ) ≤ 2 * R ∧
      Squarefree n ∧ n.primeFactors.card = m + 1 := by
    intro n hn
    obtain ⟨hnIoc, hsq, hcard⟩ := mem_filter.mp (hU hn)
    obtain ⟨hnR, hn2R⟩ := mem_Ioc.mp hnIoc
    exact ⟨by exact_mod_cast hnR, by exact_mod_cast hn2R, hsq, hcard⟩
  have hUc : ∀ n ∈ U, cellIndex R h n < ⌊x⌋₊ := by
    intro n hn
    obtain ⟨h1, h2, -⟩ := hU_mem n hn
    exact cellIndex_lt hh0 h1 (by rw [hJh]; linarith)
  set T_all := (range ⌊x⌋₊).biUnion fun i =>
    layerTargets m M ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h)
  have hcount : ∀ i, (U.filter (cellIndex R h · = i)).card ≤
      (T_all.filter (cellIndex R h · = i)).card := by
    intro i
    by_cases hi : i < ⌊x⌋₊
    · obtain ⟨hu, huv, hv, hgap⟩ := hcell i hi
      have hsub1 : U.filter (cellIndex R h · = i) ⊆
          kPrimesIn (m + 1) ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h) := by
        intro n hn
        obtain ⟨hnU, hni⟩ := mem_filter.mp hn
        obtain ⟨h1, -, hsq, hcard⟩ := hU_mem n hnU
        obtain ⟨h3, h4⟩ := cellIndex_spec hh0 h1
        rw [hni] at h3 h4
        exact (mem_kPrimesIn (by linarith) (by linarith)).mpr ⟨h3, h4, hsq, hcard⟩
      have hsub2 : layerTargets m M ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h) ⊆
          T_all.filter (cellIndex R h · = i) := by
        intro n hn
        obtain ⟨h3, h4, -⟩ := mem_layerTargets hM5 (hMR.trans hu) huv hn
        exact mem_filter.mpr ⟨mem_biUnion.mpr ⟨i, mem_range.mpr hi, hn⟩,
          cellIndex_eq hh0 h3 h4⟩
      have hup_i := hup R hR₁ _ _ hu huv hv hgap
      simp only [Nat.add_sub_cancel] at hup_i
      have hlow_i := hlowR _ _ hu huv hv hgap
      have hfac_pos : (0 : ℝ) < (m.factorial : ℝ) * Real.log R := by
        have : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos _
        positivity
      have hw_nn : 0 ≤ (((R : ℝ) + (i + 1) * h) - ((R : ℝ) + i * h)) /
          ((m.factorial : ℝ) * Real.log R) :=
        div_nonneg (by linarith) hfac_pos.le
      have hmid : (1 + 1 / 100) * (((R : ℝ) + (i + 1) * h) - ((R : ℝ) + i * h)) /
            ((m.factorial : ℝ) * Real.log R) * (ℓ + K₁) ^ m ≤
          (61 / 60) * (((R : ℝ) + (i + 1) * h) - ((R : ℝ) + i * h)) /
            ((m.factorial : ℝ) * Real.log R) * (ℓ - K₂) ^ m := by
        have hm := mul_le_mul_of_nonneg_left hratio_pow hw_nn
        linarith [show (1 + 1 / 100) * (((R : ℝ) + (i + 1) * h) - ((R : ℝ) + i * h)) /
              ((m.factorial : ℝ) * Real.log R) * (ℓ + K₁) ^ m =
            (((R : ℝ) + (i + 1) * h) - ((R : ℝ) + i * h)) /
              ((m.factorial : ℝ) * Real.log R) * ((1 + 1 / 100) * (ℓ + K₁) ^ m) by ring,
          show (61 / 60) * (((R : ℝ) + (i + 1) * h) - ((R : ℝ) + i * h)) /
              ((m.factorial : ℝ) * Real.log R) * (ℓ - K₂) ^ m =
            (((R : ℝ) + (i + 1) * h) - ((R : ℝ) + i * h)) /
              ((m.factorial : ℝ) * Real.log R) * ((61 / 60) * (ℓ - K₂) ^ m) by ring]
      have hle_real : ((kPrimesIn (m + 1) ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h)).card : ℝ) ≤
          (layerTargets m M ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h)).card :=
        hup_i.trans (hmid.trans hlow_i)
      have hle_nat : (kPrimesIn (m + 1) ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h)).card ≤
          (layerTargets m M ((R : ℝ) + i * h) ((R : ℝ) + (i + 1) * h)).card := by
        exact_mod_cast hle_real
      exact (card_le_card hsub1).trans (hle_nat.trans (card_le_card hsub2))
    · have hemp : U.filter (cellIndex R h · = i) = ∅ := by
        refine filter_eq_empty_iff.mpr fun n hn hni => hi ?_
        rw [← hni]; exact hUc n hn
      rw [hemp]; exact Nat.zero_le _
  obtain ⟨ψ, hinj, hψ⟩ := exists_cellwise_injOn (cellIndex R h) U T_all hcount
  have hψ_props : ∀ n ∈ U, ψ n ∈ factorLayer (Ioc R (2 * R)) (m + 2) ∧
      |(ψ n : ℝ) - n| ≤ 2 * R / Real.log R ^ B ∧
      ∃ q d r : ℕ, (q = 2 ∨ q = 3 ∨ q = 5) ∧ r.Prime ∧ 5 < r ∧
        Squarefree d ∧ d.primeFactors.card = m ∧ ψ n = q * d * r := by
    intro n hn
    obtain ⟨hψT, hψc⟩ := hψ n hn
    obtain ⟨i, hi, hmem_lt⟩ := mem_biUnion.mp hψT
    have hi' := mem_range.mp hi
    obtain ⟨hu, huv, hv, -⟩ := hcell i hi'
    obtain ⟨hlt, hle, hsq_ψ, hcard_ψ, hex⟩ :=
      mem_layerTargets hM5 (hMR.trans hu) huv hmem_lt
    have hci : cellIndex R h (ψ n) = i := cellIndex_eq hh0 hlt hle
    obtain ⟨h1, -, -⟩ := hU_mem n hn
    obtain ⟨h3, h4⟩ := cellIndex_spec hh0 h1
    rw [← hψc, hci] at h3 h4
    have hψ_Ioc : ψ n ∈ Ioc R (2 * R) := by
      refine mem_Ioc.mpr ⟨?_, ?_⟩
      · exact_mod_cast (show (R : ℝ) < ψ n by linarith)
      · exact_mod_cast (show (ψ n : ℝ) ≤ (2 * R : ℕ) by push_cast; linarith)
    refine ⟨mem_filter.mpr ⟨hψ_Ioc, hsq_ψ, hcard_ψ⟩, ?_, hex⟩
    rw [abs_le]
    constructor <;> linarith
  refine ⟨ψ, hinj, ?_, fun n hn => ⟨(hψ_props n hn).2.1, (hψ_props n hn).2.2⟩⟩
  intro y hy
  obtain ⟨n, hn, rfl⟩ := mem_image.mp hy
  exact (hψ_props n hn).1

/-! ### 4. Assembling `K`-layer cascades into disjoint opposite-parity matchings -/

/-- Disjoint union of two opposite-parity matchings on `S` with disjoint `matchedSet`s. -/
noncomputable def OppositeParityMatching.disjointUnion {R : ℕ → ℕ → Prop} {S : Finset ℕ}
    (M₁ M₂ : OppositeParityMatching R S) (hdisj : Disjoint M₁.matchedSet M₂.matchedSet) :
    OppositeParityMatching R S := by
  classical
  have hs_disj : Disjoint M₁.sources M₂.sources :=
    Disjoint.mono subset_union_left subset_union_left hdisj
  have ht_disj : Disjoint M₁.targets M₂.targets :=
    Disjoint.mono subset_union_right subset_union_right hdisj
  refine
    { sources := M₁.sources ∪ M₂.sources
      partner := fun a => if a ∈ M₁.sources then M₁.partner a else M₂.partner a
      sources_subset := union_subset M₁.sources_subset M₂.sources_subset
      injOn := ?_
      partner_mem := ?_
      adj := ?_ }
  · intro x hx y hy hxy
    rcases mem_union.mp (mem_coe.mp hx) with hx1 | hx2 <;>
      rcases mem_union.mp (mem_coe.mp hy) with hy1 | hy2
    · simp only [if_pos hx1, if_pos hy1] at hxy
      exact M₁.injOn hx1 hy1 hxy
    · simp only [if_pos hx1, if_neg (disjoint_right.mp hs_disj hy2)] at hxy
      exact False.elim (disjoint_left.mp ht_disj (mem_image_of_mem _ hx1)
        (hxy ▸ mem_image_of_mem _ hy2))
    · simp only [if_neg (disjoint_right.mp hs_disj hx2), if_pos hy1] at hxy
      exact False.elim (disjoint_left.mp ht_disj (mem_image_of_mem _ hy1)
        (hxy.symm ▸ mem_image_of_mem _ hx2))
    · simp only [if_neg (disjoint_right.mp hs_disj hx2),
        if_neg (disjoint_right.mp hs_disj hy2)] at hxy
      exact M₂.injOn hx2 hy2 hxy
  · intro a ha
    rcases mem_union.mp ha with ha1 | ha2
    · rw [if_pos ha1]; exact M₁.partner_mem a ha1
    · rw [if_neg (disjoint_right.mp hs_disj ha2)]; exact M₂.partner_mem a ha2
  · intro a ha
    rcases mem_union.mp ha with ha1 | ha2
    · rw [if_pos ha1]; exact M₁.adj a ha1
    · rw [if_neg (disjoint_right.mp hs_disj ha2)]; exact M₂.adj a ha2

theorem OppositeParityMatching.disjointUnion_spec {R : ℕ → ℕ → Prop} {S : Finset ℕ}
    (M₁ M₂ : OppositeParityMatching R S) (hdisj : Disjoint M₁.matchedSet M₂.matchedSet) :
    (M₁.disjointUnion M₂ hdisj).matchedSet = M₁.matchedSet ∪ M₂.matchedSet ∧
      (M₁.disjointUnion M₂ hdisj).sources.card = M₁.sources.card + M₂.sources.card := by
  classical
  have hs_disj : Disjoint M₁.sources M₂.sources :=
    Disjoint.mono subset_union_left subset_union_left hdisj
  have htar : (M₁.disjointUnion M₂ hdisj).targets = M₁.targets ∪ M₂.targets := by
    ext b
    simp only [OppositeParityMatching.targets, OppositeParityMatching.disjointUnion,
      mem_image, mem_union]
    constructor
    · rintro ⟨a, ha1 | ha2, rfl⟩
      · rw [if_pos ha1]; exact Or.inl ⟨a, ha1, rfl⟩
      · rw [if_neg (disjoint_right.mp hs_disj ha2)]; exact Or.inr ⟨a, ha2, rfl⟩
    · rintro (⟨a, ha1, rfl⟩ | ⟨a, ha2, rfl⟩)
      · exact ⟨a, Or.inl ha1, if_pos ha1⟩
      · exact ⟨a, Or.inr ha2, if_neg (disjoint_right.mp hs_disj ha2)⟩
  refine ⟨?_, card_union_of_disjoint hs_disj⟩
  simp only [OppositeParityMatching.matchedSet, htar]
  change (M₁.sources ∪ M₂.sources) ∪ (M₁.targets ∪ M₂.targets) =
    (M₁.sources ∪ M₁.targets) ∪ (M₂.sources ∪ M₂.targets)
  ext x; simp only [mem_union]; tauto

/-- Single-step opposite-parity matching induced by an injection `ψ : U ↪ factorLayer S (k + 1)`
with `U ⊆ factorLayer S k` along a symmetric relation `R`. -/
noncomputable def singleStepMatching {R : ℕ → ℕ → Prop} (hRsym : ∀ a b, R a b → R b a)
    {S : Finset ℕ} {k : ℕ} {U : Finset ℕ} {ψ : ℕ → ℕ}
    (hU : U ⊆ factorLayer S k) (hinj : Set.InjOn ψ ↑U)
    (himg : U.image ψ ⊆ factorLayer S (k + 1)) (hadj : ∀ m ∈ U, R m (ψ m)) :
    {M : OppositeParityMatching R S //
      M.matchedSet = U ∪ U.image ψ ∧ M.sources.card = U.card} := by
  classical
  if hk_even : Even k then
    have hU_pos : U ⊆ posParity S := by
      intro a ha
      obtain ⟨haS, hsq, hcard⟩ := mem_filter.mp (hU ha)
      refine mem_filter.mpr ⟨haS, ?_⟩
      rw [moebius_eq_neg_one_pow_omega hsq, hcard]
      exact hk_even.neg_one_pow
    have hψ_neg : ∀ a ∈ U, ψ a ∈ negParity S := by
      intro a ha
      obtain ⟨hbS, hsq, hcard⟩ := mem_filter.mp (himg (mem_image_of_mem ψ ha))
      refine mem_filter.mpr ⟨hbS, ?_⟩
      rw [moebius_eq_neg_one_pow_omega hsq, hcard]
      exact (hk_even.add_one).neg_one_pow
    let M : OppositeParityMatching R S :=
      { sources := U
        partner := ψ
        sources_subset := hU_pos
        injOn := hinj
        partner_mem := hψ_neg
        adj := hadj }
    exact ⟨M, rfl, rfl⟩
  else
    have hk_odd : Odd k := Nat.not_even_iff_odd.mp hk_even
    let V := U.image ψ
    have hV_pos : V ⊆ posParity S := by
      intro b hb
      obtain ⟨hbS, hsq, hcard⟩ := mem_filter.mp (himg hb)
      refine mem_filter.mpr ⟨hbS, ?_⟩
      rw [moebius_eq_neg_one_pow_omega hsq, hcard]
      exact (hk_odd.add_odd odd_one).neg_one_pow
    have hU_neg : U ⊆ negParity S := by
      intro a ha
      obtain ⟨haS, hsq, hcard⟩ := mem_filter.mp (hU ha)
      refine mem_filter.mpr ⟨haS, ?_⟩
      rw [moebius_eq_neg_one_pow_omega hsq, hcard]
      exact hk_odd.neg_one_pow
    let invψ : ℕ → ℕ := fun b =>
      if hb : b ∈ V then (mem_image.mp hb).choose else 0
    have hinv_spec : ∀ b (hb : b ∈ V), invψ b ∈ U ∧ ψ (invψ b) = b := by
      intro b hb
      dsimp only [invψ]
      rw [dif_pos hb]
      exact (mem_image.mp hb).choose_spec
    have hinv_eq : ∀ a ∈ U, invψ (ψ a) = a := by
      intro a ha
      have hb : ψ a ∈ V := mem_image_of_mem ψ ha
      obtain ⟨hu, hψu⟩ := hinv_spec (ψ a) hb
      exact hinj hu ha hψu
    have hinv_inj : Set.InjOn invψ ↑V := by
      intro b₁ hb₁ b₂ hb₂ heq
      have h1 := (hinv_spec b₁ hb₁).2
      have h2 := (hinv_spec b₂ hb₂).2
      rw [← h1, ← h2, heq]
    have hV_img : V.image invψ = U := by
      ext a
      simp only [mem_image]
      constructor
      · rintro ⟨b, hb, rfl⟩; exact (hinv_spec b hb).1
      · intro ha; exact ⟨ψ a, mem_image_of_mem ψ ha, hinv_eq a ha⟩
    let M : OppositeParityMatching R S :=
      { sources := V
        partner := invψ
        sources_subset := hV_pos
        injOn := hinv_inj
        partner_mem := fun b hb => hU_neg (hinv_spec b hb).1
        adj := fun b hb => by
          obtain ⟨hu, hψu⟩ := hinv_spec b hb
          have hadj_b := hRsym _ _ (hadj _ hu)
          rwa [hψu] at hadj_b }
    refine ⟨M, ?_, card_image_of_injOn hinj⟩
    change V ∪ V.image invψ = U ∪ V
    rw [hV_img, union_comm]

/-- Inductive assembly of any valid `K`-layer cascade into a single disjoint
`OppositeParityMatching` covering all squarefree layers `1 ≤ ω(n) ≤ K`. -/
noncomputable def matchingOfLayerCascade {R : ℕ → ℕ → Prop} (hRsym : ∀ a b, R a b → R b a)
    (S : Finset ℕ) (φ : ℕ → ℕ → ℕ) :
    ∀ K : ℕ, IsValidLayerCascade S φ K →
      (∀ k : ℕ, 1 ≤ k → k ≤ K → ∀ m ∈ cascadeUnconsumed S φ k, R m (φ k m)) →
      {M : OppositeParityMatching R S //
        M.matchedSet = (Finset.Icc 1 K).biUnion (factorLayer S) ∪
          (if K = 0 then ∅ else (cascadeUnconsumed S φ K).image (φ K)) ∧
        M.sources.card = ∑ k ∈ Finset.Icc 1 K, (cascadeUnconsumed S φ k).card}
  | 0, _, _ =>
    ⟨{ sources := ∅
       partner := id
       sources_subset := empty_subset _
       injOn := by simp
       partner_mem := fun _ h => False.elim (notMem_empty _ h)
       adj := fun _ h => False.elim (notMem_empty _ h) },
     by simp [OppositeParityMatching.matchedSet, OppositeParityMatching.targets],
     by simp⟩
  | K + 1, hvalid, hadj => by
    classical
    have hvalid_K : IsValidLayerCascade S φ K :=
      fun k hk1 hkK => hvalid k hk1 (by omega)
    have hadj_K : ∀ k : ℕ, 1 ≤ k → k ≤ K → ∀ m ∈ cascadeUnconsumed S φ k, R m (φ k m) :=
      fun k hk1 hkK => hadj k hk1 (by omega)
    obtain ⟨M_K, hMK_set, hMK_card⟩ := matchingOfLayerCascade hRsym S φ K hvalid_K hadj_K
    obtain ⟨hinj_top, hsub_top⟩ := hvalid (K + 1) (by omega) le_rfl
    obtain ⟨M_top, hMtop_set, hMtop_card⟩ := singleStepMatching hRsym
      (cascadeUnconsumed_subset_factorLayer S φ (K + 1)) hinj_top hsub_top
      (hadj (K + 1) (by omega) le_rfl)
    have hdisj : Disjoint M_K.matchedSet M_top.matchedSet := by
      rw [hMK_set, hMtop_set, disjoint_left]
      intro x hxK hxTop
      have hU_sub := cascadeUnconsumed_subset_factorLayer S φ (K + 1)
      rcases mem_union.mp hxK with hxIcc | hxImgK
      · obtain ⟨j, hjIcc, hxj⟩ := mem_biUnion.mp hxIcc
        have hjK : j ≤ K := (mem_Icc.mp hjIcc).2
        rcases mem_union.mp hxTop with hxU | hxV
        · exact disjoint_left.mp (disjoint_factorLayer (by omega : j ≠ K + 1)) hxj (hU_sub hxU)
        · exact disjoint_left.mp (disjoint_factorLayer (by omega : j ≠ K + 2)) hxj (hsub_top hxV)
      · rcases Nat.eq_zero_or_pos K with rfl | hKpos
        · simp at hxImgK
        · rw [if_neg hKpos.ne'] at hxImgK
          obtain ⟨j, rfl⟩ : ∃ j, K = j + 1 := ⟨K - 1, by omega⟩
          rcases mem_union.mp hxTop with hxU | hxV
          · change x ∈ factorLayer S (j + 2) \
              (cascadeUnconsumed S φ (j + 1)).image (φ (j + 1)) at hxU
            exact (mem_sdiff.mp hxU).2 hxImgK
          · have hsub_prev := (hvalid (j + 1) (by omega) (by omega)).2
            exact disjoint_left.mp (disjoint_factorLayer (by omega : j + 2 ≠ j + 3))
              (hsub_prev hxImgK) (hsub_top hxV)
    refine ⟨M_K.disjointUnion M_top hdisj, ?_, ?_⟩
    · rw [(M_K.disjointUnion_spec M_top hdisj).1, hMK_set, hMtop_set, if_neg (Nat.succ_ne_zero K)]
      have hIcc_step : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
        ext j; simp only [mem_Icc, mem_insert]; omega
      rw [hIcc_step, biUnion_insert]
      rcases Nat.eq_zero_or_pos K with rfl | hKpos
      · simp [cascadeUnconsumed, union_comm]
      · rw [if_neg hKpos.ne']
        obtain ⟨j, rfl⟩ : ∃ j, K = j + 1 := ⟨K - 1, by omega⟩
        have hsub_prev : (cascadeUnconsumed S φ (j + 1)).image (φ (j + 1)) ⊆
            factorLayer S (j + 2) := (hvalid (j + 1) (by omega) (by omega)).2
        have hunion_mid : (cascadeUnconsumed S φ (j + 1)).image (φ (j + 1)) ∪
            cascadeUnconsumed S φ (j + 2) = factorLayer S (j + 2) := by
          change (cascadeUnconsumed S φ (j + 1)).image (φ (j + 1)) ∪
            (factorLayer S (j + 2) \ (cascadeUnconsumed S φ (j + 1)).image (φ (j + 1))) =
              factorLayer S (j + 2)
          exact union_sdiff_of_subset hsub_prev
        ext x
        simp only [mem_union]
        have hmid_iff : (x ∈ (cascadeUnconsumed S φ (j + 1)).image (φ (j + 1)) ∨
            x ∈ cascadeUnconsumed S φ (j + 2)) ↔ x ∈ factorLayer S (j + 2) := by
          rw [← mem_union, hunion_mid]
        tauto
    · rw [(M_K.disjointUnion_spec M_top hdisj).2, hMK_card, hMtop_card]
      have hIcc_step : Finset.Icc 1 (K + 1) = insert (K + 1) (Finset.Icc 1 K) := by
        ext j; simp only [mem_Icc, mem_insert]; omega
      rw [hIcc_step, sum_insert (by simp), add_comm]

private theorem exists_valid_cascade_up_to :
    ∀ (K : ℕ) {B : ℝ} (_hB : 0 < B),
      ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
        ∃ φ : ℕ → ℕ → ℕ,
          IsValidLayerCascade (Ioc R (2 * R)) φ K ∧
          ∀ k : ℕ, 1 ≤ k → k ≤ K → ∀ n ∈ cascadeUnconsumed (Ioc R (2 * R)) φ k,
            |(φ k n : ℝ) - n| ≤ 2 * R / Real.log R ^ B ∧
            ∃ q d r : ℕ, (q = 2 ∨ q = 3 ∨ q = 5) ∧ r.Prime ∧ 5 < r ∧
              Squarefree d ∧ d.primeFactors.card = k - 1 ∧ φ k n = q * d * r
  | 0, _, _ =>
    ⟨0, fun _ _ => ⟨fun _ _ => 0, fun _ hk1 hk0 => by omega, fun _ hk1 hk0 => by omega⟩⟩
  | K + 1, B, hB => by
    obtain ⟨R₁, ih⟩ := exists_valid_cascade_up_to K hB
    obtain ⟨R₂, hstep⟩ := exists_single_layer_cell_matching K hB
    refine ⟨max R₁ R₂, fun R hR => ?_⟩
    obtain ⟨φ₀, hval₀, hprop₀⟩ := ih R (le_of_max_le_left hR)
    set S := Ioc R (2 * R)
    obtain ⟨ψ, hinjψ, himgψ, hpropψ⟩ := hstep R (le_of_max_le_right hR)
      (cascadeUnconsumed S φ₀ (K + 1))
      (cascadeUnconsumed_subset_factorLayer S φ₀ (K + 1))
    let φ : ℕ → ℕ → ℕ := fun k => if k = K + 1 then ψ else φ₀ k
    have hU_agree : ∀ j ≤ K + 1, cascadeUnconsumed S φ j = cascadeUnconsumed S φ₀ j := by
      intro j hj
      induction j with
      | zero => rfl
      | succ i ihi =>
        rcases Nat.eq_zero_or_pos i with rfl | hipos
        · rfl
        · obtain ⟨t, rfl⟩ : ∃ t, i = t + 1 := ⟨i - 1, by omega⟩
          have ht_ne : t + 1 ≠ K + 1 := by omega
          simp only [cascadeUnconsumed, ihi (by omega), φ, if_neg ht_ne]
    refine ⟨φ, fun k hk1 hk => ?_, fun k hk1 hk n hn => ?_⟩
    · rw [hU_agree k hk]
      rcases eq_or_lt_of_le hk with rfl | hlt
      · simp only [φ, if_pos rfl]
        exact ⟨hinjψ, himgψ⟩
      · simp only [φ, if_neg hlt.ne]
        exact hval₀ k hk1 (by omega)
    · rw [hU_agree k hk] at hn
      rcases eq_or_lt_of_le hk with rfl | hlt
      · simp only [φ, if_pos rfl, Nat.add_sub_cancel]
        exact hpropψ n hn
      · simp only [φ, if_neg hlt.ne]
        exact hprop₀ k hk1 (by omega) n hn

/-- **All-finite-layer cellwise matching (`K ≥ 1`, `B > 0`)**: For all sufficiently large `R`,
sequential cellwise `{2, 3, 5}`-cofactor injections match **100% of squarefree integers in
`(R, 2R]` with `1 ≤ ω(n) ≤ K`** into a single disjoint opposite-parity matching `M` at cell
scale `≤ 2R / (log R)^B`, with zero unweighted Möbius sum, literal dipole representation, and
uniform `Γ`-Sobolev norm bound `‖T_{R,K}‖_δ² ≤ C R^{1-δ} (log log R)^{2(K-1)} / (log R)^{2B+2}`. -/
theorem exists_all_finite_layers_cell_matching (K : ℕ) (hK : 1 ≤ K) {B : ℝ} (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ∃ (φ : ℕ → ℕ → ℕ)
        (M : OppositeParityMatching
          (fun a b => |(b : ℝ) - a| ≤ 2 * R / Real.log R ^ B) (Ioc R (2 * R))),
        IsValidLayerCascade (Ioc R (2 * R)) φ K ∧
        (∀ k : ℕ, 1 ≤ k → k ≤ K → ∀ n ∈ cascadeUnconsumed (Ioc R (2 * R)) φ k,
          |(φ k n : ℝ) - n| ≤ 2 * R / Real.log R ^ B ∧
          ∃ q d r : ℕ, (q = 2 ∨ q = 3 ∨ q = 5) ∧ r.Prime ∧ 5 < r ∧
            Squarefree d ∧ d.primeFactors.card = k - 1 ∧ φ k n = q * d * r) ∧
        M.matchedSet = (Finset.Icc 1 K).biUnion (factorLayer (Ioc R (2 * R))) ∪
          (cascadeUnconsumed (Ioc R (2 * R)) φ K).image (φ K) ∧
        (∀ n ∈ Ioc R (2 * R), Squarefree n → 1 ≤ n.primeFactors.card →
          n.primeFactors.card ≤ K → n ∈ M.matchedSet) ∧
        ∑ n ∈ M.matchedSet, μ n = 0 ∧
        (∀ t : ℝ, ∑ a ∈ M.sources, (atom a t - atom (M.partner a) t) =
          ∑ n ∈ M.matchedSet, ((μ n : ℤ) : ℝ) * atom n t) ∧
        ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 →
          gammaNorm δ (fun t => ∑ n ∈ M.matchedSet, ((μ n : ℤ) : ℝ) * atom n t) ^ 2 ≤
            C * (R : ℝ) ^ (1 - δ) * Real.log (Real.log R) ^ (2 * (K - 1)) /
              Real.log R ^ (2 * B + 2) := by
  obtain ⟨R_cas, hcas⟩ := exists_valid_cascade_up_to K hB
  -- Collect upper-bound constants across `1 ≤ k ≤ K`
  choose K_up R_up hR_up3 hcard_up using
    fun k : {k : ℕ // k ∈ Finset.Icc 1 K} =>
      exists_card_kPrimesIn_le k.1 (mem_Icc.mp k.2).1 B
  set R_max : ℝ := Finset.univ.sup'
    ⟨⟨1, mem_Icc.mpr ⟨le_rfl, hK⟩⟩, mem_univ _⟩ R_up
  set K_max : ℝ := Finset.univ.sup'
    ⟨⟨1, mem_Icc.mpr ⟨le_rfl, hK⟩⟩, mem_univ _⟩ (fun k => |K_up k|)
  set W₀ : ℝ := 2 * (K : ℝ) * (2 : ℝ) ^ (K - 1)
  have hc := jetConst_nonneg 1
  have hev : ∀ᶠ R : ℝ in atTop,
      R_max ≤ R ∧ 3 ≤ R ∧ 1 ≤ Real.log R ∧ K_max + 1 ≤ Real.log (Real.log R) :=
    (eventually_ge_atTop _).and ((eventually_ge_atTop _).and
      ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and
        ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop _)))
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  refine ⟨64 * jetConst 1 ^ 2 * W₀ ^ 2 + 1, by positivity, max R_cas ⌈X⌉₊, fun R hR => ?_⟩
  have hRX : X ≤ (R : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast le_of_max_le_right hR)
  obtain ⟨hR_sup, hR3, hL1, hll_sup⟩ := hX R hRX
  have hR0 : (0 : ℝ) < R := by linarith
  have hL0 : 0 < Real.log R := by linarith
  obtain ⟨φ, hvalid, hprops⟩ := hcas R (le_of_max_le_left hR)
  set S := Ioc R (2 * R)
  have hsym : ∀ a b : ℕ, |(b : ℝ) - a| ≤ 2 * R / Real.log R ^ B →
      |(a : ℝ) - b| ≤ 2 * R / Real.log R ^ B := by
    intro a b hab
    rwa [abs_sub_comm]
  obtain ⟨M, hM_set, hM_card⟩ := matchingOfLayerCascade hsym S φ K hvalid
    (fun k hk1 hkK n hn => (hprops k hk1 hkK n hn).1)
  rw [if_neg (by omega : K ≠ 0)] at hM_set
  have hcov : ∀ n ∈ S, Squarefree n → 1 ≤ n.primeFactors.card →
      n.primeFactors.card ≤ K → n ∈ M.matchedSet := by
    intro n hnS hsq h1 hleK
    rw [hM_set]
    exact mem_union_left _ (mem_biUnion.mpr ⟨n.primeFactors.card, mem_Icc.mpr ⟨h1, hleK⟩,
      mem_filter.mpr ⟨hnS, hsq, rfl⟩⟩)
  have hlit : ∀ t : ℝ, ∑ a ∈ M.sources, (atom a t - atom (M.partner a) t) =
      ∑ n ∈ M.matchedSet, ((μ n : ℤ) : ℝ) * atom n t := by
    intro t
    have h := sum_dipoles_eq_literal M.sources M.partner (-1) M.injOn
      M.disjoint_sources_targets
      (fun a ha => ⟨by simpa using (mem_filter.mp (M.sources_subset ha)).2,
        (mem_filter.mp (M.partner_mem a ha)).2⟩) t
    change ∑ a ∈ M.sources, (atom a t - atom (M.partner a) t) =
      ∑ n ∈ M.sources ∪ M.sources.image M.partner, ((μ n : ℤ) : ℝ) * atom n t
    rw [← h]
    refine sum_congr rfl fun a _ => ?_
    push_cast; ring
  refine ⟨φ, M, hvalid, hprops, hM_set, hcov, M.sum_moebius_matchedSet, hlit,
    fun δ hδ0 hδ1 => ?_⟩
  -- Bound `M.sources.card` across `1 ≤ k ≤ K`
  have hx1 : 1 ≤ Real.log R ^ B := Real.one_le_rpow hL1 hB.le
  have hgap : (R : ℝ) / Real.log R ^ B ≤ 2 * R - R := by
    rw [show (2 : ℝ) * R - R = R by ring]
    exact div_le_self hR0.le hx1
  have hk_bound : ∀ k ∈ Finset.Icc 1 K,
      ((cascadeUnconsumed S φ k).card : ℝ) ≤
        2 * (2 : ℝ) ^ (K - 1) * Real.log (Real.log R) ^ (K - 1) * R / Real.log R := by
    intro k hkIcc
    have hk1 := (mem_Icc.mp hkIcc).1
    have hkK := (mem_Icc.mp hkIcc).2
    let ksub : {j : ℕ // j ∈ Finset.Icc 1 K} := ⟨k, hkIcc⟩
    have hRk : R_up ksub ≤ R := (le_sup' R_up (mem_univ ksub)).trans hR_sup
    have hKk : |K_up ksub| ≤ K_max := le_sup' (fun j => |K_up j|) (mem_univ ksub)
    have hup_k := hcard_up ksub R hRk R (2 * R) le_rfl (by linarith) le_rfl hgap
    have hU_le : (cascadeUnconsumed S φ k).card ≤ (kPrimesIn k R (2 * R)).card := by
      have hcast2R : ((2 * R : ℕ) : ℝ) = 2 * (R : ℝ) := by push_cast; ring
      rw [← hcast2R, kPrimesIn_nat_eq_factorLayer]
      exact card_le_card (cascadeUnconsumed_subset_factorLayer S φ k)
    have hfac_ge1 : (1 : ℝ) ≤ (k - 1).factorial := by exact_mod_cast Nat.factorial_pos _
    have hll_pos : 1 ≤ Real.log (Real.log R) := by
      have : 0 ≤ K_max := (abs_nonneg _).trans hKk
      linarith
    have hll_step : Real.log (Real.log R) + K_up ksub ≤ 2 * Real.log (Real.log R) := by
      have := le_abs_self (K_up ksub)
      linarith
    have hpow_le : (Real.log (Real.log R) + K_up ksub) ^ (k - 1) ≤
        (2 * Real.log (Real.log R)) ^ (K - 1) := by
      have h1 : (Real.log (Real.log R) + K_up ksub) ^ (k - 1) ≤
          (2 * Real.log (Real.log R)) ^ (k - 1) :=
        pow_le_pow_left₀ (by have := neg_abs_le (K_up ksub); linarith) hll_step _
      have h2 : (2 * Real.log (Real.log R)) ^ (k - 1) ≤
          (2 * Real.log (Real.log R)) ^ (K - 1) :=
        pow_le_pow_right₀ (by linarith) (by omega)
      exact h1.trans h2
    calc ((cascadeUnconsumed S φ k).card : ℝ)
        ≤ (kPrimesIn k R (2 * R)).card := by exact_mod_cast hU_le
      _ ≤ (1 + 1 / 100) * (2 * R - R) / (((k - 1).factorial : ℝ) * Real.log R) *
            (Real.log (Real.log R) + K_up ksub) ^ (k - 1) := hup_k
      _ ≤ 2 * R / (1 * Real.log R) * (2 * Real.log (Real.log R)) ^ (K - 1) := by
          have hnum : (1 + 1 / 100) * (2 * (R : ℝ) - R) ≤ 2 * R := by linarith
          have hden : 1 * Real.log R ≤ ((k - 1).factorial : ℝ) * Real.log R := by gcongr
          have hdiv : (1 + 1 / 100) * (2 * (R : ℝ) - R) / (((k - 1).factorial : ℝ) * Real.log R) ≤
              2 * R / (1 * Real.log R) := by
            calc (1 + 1 / 100) * (2 * (R : ℝ) - R) / (((k - 1).factorial : ℝ) * Real.log R)
                ≤ 2 * R / (((k - 1).factorial : ℝ) * Real.log R) :=
                  div_le_div_of_nonneg_right hnum (by positivity)
              _ ≤ 2 * R / (1 * Real.log R) :=
                  div_le_div_of_nonneg_left (by positivity) (by positivity) hden
          exact mul_le_mul hdiv hpow_le
            (pow_nonneg (by have := neg_abs_le (K_up ksub); linarith) _) (by positivity)
      _ = 2 * (2 : ℝ) ^ (K - 1) * Real.log (Real.log R) ^ (K - 1) * R / Real.log R := by
          rw [mul_pow]; ring
  have hN_sources : (M.sources.card : ℝ) ≤
      (W₀ * Real.log (Real.log R) ^ (K - 1)) * R / Real.log R := by
    rw [hM_card]
    push_cast
    calc ∑ k ∈ Finset.Icc 1 K, ((cascadeUnconsumed S φ k).card : ℝ)
        ≤ ∑ _k ∈ Finset.Icc 1 K,
            (2 * (2 : ℝ) ^ (K - 1) * Real.log (Real.log R) ^ (K - 1) * R / Real.log R) :=
          sum_le_sum hk_bound
      _ = ((Finset.Icc 1 K).card : ℝ) *
            (2 * (2 : ℝ) ^ (K - 1) * Real.log (Real.log R) ^ (K - 1) * R / Real.log R) := by
          rw [sum_const, nsmul_eq_mul]
      _ = (W₀ * Real.log (Real.log R) ^ (K - 1)) * R / Real.log R := by
          have hIcc_card : (Finset.Icc 1 K).card = K := by rw [Nat.card_Icc]; omega
          rw [hIcc_card]
          simp only [W₀]; ring
  have hfun_eq : (fun t => ∑ n ∈ M.matchedSet, ((μ n : ℤ) : ℝ) * atom n t) =
      fun t => ∑ a ∈ M.sources, (atom a t - atom (M.partner a) t) := by
    funext t; exact (hlit t).symm
  rw [hfun_eq]
  have hsrc_band : ∀ a ∈ M.sources, (R : ℝ) ≤ a ∧ (a : ℝ) ≤ 2 * R := by
    intro a ha
    obtain ⟨haR, ha2R⟩ := mem_Ioc.mp (mem_filter.mp (M.sources_subset ha)).1
    exact ⟨by exact_mod_cast haR.le, by exact_mod_cast ha2R⟩
  have htar_band : ∀ a ∈ M.sources, (R : ℝ) ≤ M.partner a ∧ (M.partner a : ℝ) ≤ 2 * R := by
    intro a ha
    obtain ⟨hbR, hb2R⟩ := mem_Ioc.mp (mem_filter.mp (M.partner_mem a ha)).1
    exact ⟨by exact_mod_cast hbR.le, by exact_mod_cast hb2R⟩
  have hgn := gammaNorm_matched_le' hδ0 hδ1 hR0 M.sources M.partner hsrc_band htar_band M.adj
  have hsq := matched_energy_sq_le hR0 hL0 hc hN_sources (gammaNorm_nonneg _ _) hgn
  have hpow2 : (W₀ * Real.log (Real.log R) ^ (K - 1)) ^ 2 =
      W₀ ^ 2 * Real.log (Real.log R) ^ (2 * (K - 1)) := by
    rw [mul_pow, ← pow_mul, mul_comm (K - 1) 2]
  have hll_nn : 0 ≤ Real.log (Real.log R) := by
    have : 0 ≤ K_max := (abs_nonneg _).trans
      (le_sup' (fun j => |K_up j|) (mem_univ ⟨1, mem_Icc.mpr ⟨le_rfl, hK⟩⟩))
    linarith
  calc gammaNorm δ (fun t => ∑ a ∈ M.sources, (atom a t - atom (M.partner a) t)) ^ 2
      ≤ 64 * jetConst 1 ^ 2 * (W₀ * Real.log (Real.log R) ^ (K - 1)) ^ 2 *
          (R : ℝ) ^ (1 - δ) / Real.log R ^ (2 * B + 2) := hsq
    _ = 64 * jetConst 1 ^ 2 * W₀ ^ 2 *
          ((R : ℝ) ^ (1 - δ) * Real.log (Real.log R) ^ (2 * (K - 1)) /
            Real.log R ^ (2 * B + 2)) := by
          rw [hpow2]; ring
    _ ≤ (64 * jetConst 1 ^ 2 * W₀ ^ 2 + 1) *
          ((R : ℝ) ^ (1 - δ) * Real.log (Real.log R) ^ (2 * (K - 1)) /
            Real.log R ^ (2 * B + 2)) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = _ := by ring

/-! ### 5. Linear unmatched remainder after any finite depth `K` and cofactor-grading depletion -/

/-- Exact squarefree count of the dyadic block `(R, 2R]`:
`|#squarefreeOf(Ioc R (2R)) - (6/π²) R| ≤ 3 √R + 1` for every `R ≥ 1`. -/
theorem abs_card_squarefreeOf_dyadic_sub_le {R : ℕ} (hR : 1 ≤ R) :
    |((squarefreeOf (Ioc R (2 * R))).card : ℝ) - 6 / Real.pi ^ (2 : ℕ) * R| ≤
      3 * Real.sqrt R + 1 := by
  let M_cut := Nat.sqrt (2 * R) + 1
  have hM1 : 1 ≤ M_cut := by omega
  have hRM : R + R ≤ M_cut ^ (2 : ℕ) := by
    have hlt := Nat.lt_succ_sqrt (2 * R)
    rw [Nat.succ_eq_add_one] at hlt
    dsimp only [M_cut]
    rw [sq]
    omega
  have hwin := RHTower.Sieve.abs_window_squarefree_sub_le (t := R) (L := R) (R := M_cut) hM1 hRM
  have hsum_sq : ∑ n ∈ Finset.Ioc R (R + R), ((μ n : ℤ) : ℝ) ^ (2 : ℕ) =
      ((squarefreeOf (Ioc R (2 * R))).card : ℝ) := by
    classical
    rw [← two_mul R]
    have hsub : squarefreeOf (Ioc R (2 * R)) ⊆ Ioc R (2 * R) := filter_subset _ _
    rw [← sum_subset hsub (fun n hn hnot => by
      have hns : ¬ Squarefree n := fun hsq => hnot (mem_filter.mpr ⟨hn, hsq⟩)
      simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hns])]
    have h1 : ∀ n ∈ squarefreeOf (Ioc R (2 * R)), ((μ n : ℤ) : ℝ) ^ (2 : ℕ) = 1 := by
      intro n hn
      rcases moebius_eq_one_or_neg_one_of_squarefree (mem_filter.mp hn).2 with h | h <;>
        simp [h]
    rw [sum_congr rfl h1, sum_const, nsmul_eq_mul, mul_one]
  rw [hsum_sq, RHTower.Sieve.squarefreeDensity_eq] at hwin
  have hR_pos : (0 : ℝ) < R := by exact_mod_cast hR
  have hsqrt_pos : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR_pos
  have hM_up : (M_cut : ℝ) ≤ 2 * Real.sqrt R + 1 := by
    have hns : (Nat.sqrt (2 * R) : ℝ) ≤ 2 * Real.sqrt R := by
      have hsq : ((Nat.sqrt (2 * R) : ℝ)) ^ 2 ≤ (2 * Real.sqrt R) ^ 2 := by
        have h1 : (Nat.sqrt (2 * R)) ^ 2 ≤ 2 * R := by
          rw [sq]; exact Nat.sqrt_le (2 * R)
        have h1' : ((Nat.sqrt (2 * R) : ℝ)) ^ 2 ≤ 2 * (R : ℝ) := by exact_mod_cast h1
        rw [mul_pow, Real.sq_sqrt hR_pos.le]
        linarith
      exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg _) (by positivity) two_ne_zero).mp hsq
    simp only [M_cut, Nat.cast_add, Nat.cast_one]
    linarith
  have hM_low : Real.sqrt R ≤ (M_cut : ℝ) := by
    have hsq : (Real.sqrt R) ^ 2 ≤ (M_cut : ℝ) ^ 2 := by
      rw [Real.sq_sqrt hR_pos.le]
      have : R ≤ M_cut ^ (2 : ℕ) := by omega
      exact_mod_cast this
    exact (pow_le_pow_iff_left₀ hsqrt_pos.le (Nat.cast_nonneg _) two_ne_zero).mp hsq
  have hdiv_le : (R : ℝ) / (M_cut : ℝ) ≤ Real.sqrt R := by
    calc (R : ℝ) / (M_cut : ℝ) ≤ (R : ℝ) / Real.sqrt R :=
          div_le_div_of_nonneg_left hR_pos.le hsqrt_pos hM_low
      _ = Real.sqrt R := Real.div_sqrt
  have hrw : (R : ℝ) * (6 / Real.pi ^ (2 : ℕ)) = 6 / Real.pi ^ (2 : ℕ) * R := by ring
  rw [hrw] at hwin
  linarith

/-- **Linear unmatched tail after any finite number `K` of factor layers**: For every fixed `K`
and `ε > 0`, eventually for every `R` and every matching `M` on `(R, 2R]` supported on integers
with at most `K + 1` prime factors, at least `(6/π² - ε) R` squarefree integers remain unmatched. -/
theorem eventually_unmatched_after_finite_layers_ge (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ R₀ : ℕ, ∀ R : ℕ, R₀ ≤ R →
      ∀ {Rel : ℕ → ℕ → Prop} (M : OppositeParityMatching Rel (Ioc R (2 * R))),
        (∀ n ∈ M.matchedSet, n.primeFactors.card ≤ K + 1) →
        (6 / Real.pi ^ (2 : ℕ) - ε) * (R : ℝ) ≤ (M.unmatchedSet.card : ℝ) := by
  choose K_up R_up _ hcard_up using
    fun k : {k : ℕ // k ∈ Finset.Icc 1 (K + 1)} =>
      exists_card_kPrimesIn_le k.1 (mem_Icc.mp k.2).1 1
  set R_max : ℝ := Finset.univ.sup'
    ⟨⟨1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩, mem_univ _⟩ R_up
  set K_max : ℝ := Finset.univ.sup'
    ⟨⟨1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩, mem_univ _⟩ (fun k => |K_up k|)
  set C_tot : ℝ := 2 * ((K : ℝ) + 1) * (2 : ℝ) ^ K
  -- Bound `Real.log (Real.log R) ^ K / Real.log R` via `x^{K+1} / (K+1)! ≤ exp x`
  have hev : ∀ᶠ R : ℝ in atTop,
      R_max ≤ R ∧ 4 ≤ R ∧ 1 ≤ Real.log R ∧ K_max + 1 ≤ Real.log (Real.log R) ∧
      (16 / ε) ^ 2 ≤ R ∧
      2 * C_tot * ((K + 1).factorial : ℝ) / ε ≤ Real.log (Real.log R) :=
    (eventually_ge_atTop _).and ((eventually_ge_atTop _).and
      ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and
        (((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop _).and
          ((eventually_ge_atTop _).and
            ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop _)))))
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  refine ⟨max 1 ⌈X⌉₊, fun R hR {Rel} M hM_top => ?_⟩
  have hR1 : 1 ≤ R := le_of_max_le_left hR
  have hRX : X ≤ (R : ℝ) := (Nat.le_ceil X).trans (by exact_mod_cast le_of_max_le_right hR)
  obtain ⟨hR_sup, hR4, hL1, hll_sup, hR_sq, hll_fac⟩ := hX R hRX
  have hR0 : (0 : ℝ) < R := by linarith
  have hL0 : 0 < Real.log R := by linarith
  have hll_pos : 0 < Real.log (Real.log R) := by
    have : 0 ≤ K_max := (abs_nonneg _).trans
      (le_sup' (fun j => |K_up j|) (mem_univ ⟨1, mem_Icc.mpr ⟨le_rfl, by omega⟩⟩))
    linarith
  have hsmall : C_tot * (Real.log (Real.log R) ^ K / Real.log R) ≤ ε / 2 := by
    have hexp := Real.pow_div_factorial_le_exp (Real.log (Real.log R)) hll_pos.le (K + 1)
    rw [Real.exp_log hL0] at hexp
    have hfac_pos : (0 : ℝ) < (K + 1).factorial := by exact_mod_cast Nat.factorial_pos _
    have hpow_le_L : Real.log (Real.log R) ^ K / Real.log R ≤
        ((K + 1).factorial : ℝ) / Real.log (Real.log R) := by
      rw [div_le_div_iff₀ hL0 hll_pos, ← pow_succ]
      rw [div_le_iff₀ hfac_pos] at hexp
      linarith
    calc C_tot * (Real.log (Real.log R) ^ K / Real.log R)
        ≤ C_tot * (((K + 1).factorial : ℝ) / Real.log (Real.log R)) :=
          mul_le_mul_of_nonneg_left hpow_le_L (by positivity)
      _ ≤ ε / 2 := by
          rw [mul_div_assoc', div_le_iff₀ hll_pos]
          rw [div_le_iff₀ hε] at hll_fac
          linarith
  let S := Ioc R (2 * R)
  -- `M.matchedSet ⊆ (Icc 1 (K + 1)).biUnion (factorLayer S)`
  have hM_sub : M.matchedSet ⊆ (Finset.Icc 1 (K + 1)).biUnion (factorLayer S) := by
    intro n hn
    have hsq_mem := M.matchedSet_subset hn
    obtain ⟨hnIoc, hsq⟩ := mem_filter.mp hsq_mem
    have hn_gt1 : 1 < n := lt_of_le_of_lt hR1 (mem_Ioc.mp hnIoc).1
    have hcard_pos : 1 ≤ n.primeFactors.card :=
      card_pos.mpr ⟨n.minFac, Nat.mem_primeFactors.mpr
        ⟨Nat.minFac_prime hn_gt1.ne', Nat.minFac_dvd n, by omega⟩⟩
    exact mem_biUnion.mpr ⟨n.primeFactors.card, mem_Icc.mpr ⟨hcard_pos, hM_top n hn⟩,
      mem_filter.mpr ⟨hnIoc, hsq, rfl⟩⟩
  have hgap : (R : ℝ) / Real.log R ^ (1 : ℝ) ≤ 2 * R - R := by
    rw [Real.rpow_one, show (2 : ℝ) * R - R = R by ring]
    exact div_le_self hR0.le hL1
  have hlayer_le : ∀ k ∈ Finset.Icc 1 (K + 1),
      ((factorLayer S k).card : ℝ) ≤
        2 * (2 : ℝ) ^ K * Real.log (Real.log R) ^ K * R / Real.log R := by
    intro k hkIcc
    let ksub : {j : ℕ // j ∈ Finset.Icc 1 (K + 1)} := ⟨k, hkIcc⟩
    have hRk : R_up ksub ≤ R := (le_sup' R_up (mem_univ ksub)).trans hR_sup
    have hKk : |K_up ksub| ≤ K_max := le_sup' (fun j => |K_up j|) (mem_univ ksub)
    have hup_k := hcard_up ksub R hRk R (2 * R) le_rfl (by linarith) le_rfl hgap
    have hcast2R : ((2 * R : ℕ) : ℝ) = 2 * (R : ℝ) := by push_cast; ring
    have heq_card : (factorLayer S k).card = (kPrimesIn k (R : ℝ) (2 * (R : ℝ))).card := by
      rw [← hcast2R, kPrimesIn_nat_eq_factorLayer]
    have hfac_ge1 : (1 : ℝ) ≤ (k - 1).factorial := by exact_mod_cast Nat.factorial_pos _
    have hll_pos1 : 1 ≤ Real.log (Real.log R) := by
      have : 0 ≤ K_max := (abs_nonneg _).trans hKk
      linarith
    have hll_step : Real.log (Real.log R) + K_up ksub ≤ 2 * Real.log (Real.log R) := by
      have := le_abs_self (K_up ksub)
      linarith
    have hpow_le : (Real.log (Real.log R) + K_up ksub) ^ (k - 1) ≤
        (2 * Real.log (Real.log R)) ^ K := by
      have hkK : k - 1 ≤ K := by have := (mem_Icc.mp hkIcc).2; omega
      exact (pow_le_pow_left₀ (by have := neg_abs_le (K_up ksub); linarith) hll_step _).trans
        (pow_le_pow_right₀ (by linarith) hkK)
    rw [heq_card]
    calc ((kPrimesIn k (R : ℝ) (2 * (R : ℝ))).card : ℝ)
        ≤ (1 + 1 / 100) * (2 * R - R) / (((k - 1).factorial : ℝ) * Real.log R) *
            (Real.log (Real.log R) + K_up ksub) ^ (k - 1) := hup_k
      _ ≤ 2 * R / (1 * Real.log R) * (2 * Real.log (Real.log R)) ^ K := by
          have hdiv : (1 + 1 / 100) * (2 * (R : ℝ) - R) / (((k - 1).factorial : ℝ) * Real.log R) ≤
              2 * R / (1 * Real.log R) := by
            calc (1 + 1 / 100) * (2 * (R : ℝ) - R) / (((k - 1).factorial : ℝ) * Real.log R)
                ≤ 2 * R / (((k - 1).factorial : ℝ) * Real.log R) :=
                  div_le_div_of_nonneg_right (by linarith) (by positivity)
              _ ≤ 2 * R / (1 * Real.log R) :=
                  div_le_div_of_nonneg_left (by positivity) (by positivity) (by gcongr)
          exact mul_le_mul hdiv hpow_le
            (pow_nonneg (by have := neg_abs_le (K_up ksub); linarith) _) (by positivity)
      _ = 2 * (2 : ℝ) ^ K * Real.log (Real.log R) ^ K * R / Real.log R := by
          rw [mul_pow]; ring
  have hM_card_le : (M.matchedSet.card : ℝ) ≤ (ε / 2) * R := by
    have hnat : M.matchedSet.card ≤ ∑ k ∈ Finset.Icc 1 (K + 1), (factorLayer S k).card :=
      (card_le_card hM_sub).trans card_biUnion_le
    calc (M.matchedSet.card : ℝ)
        ≤ ∑ k ∈ Finset.Icc 1 (K + 1), ((factorLayer S k).card : ℝ) := by exact_mod_cast hnat
      _ ≤ ∑ _k ∈ Finset.Icc 1 (K + 1),
            (2 * (2 : ℝ) ^ K * Real.log (Real.log R) ^ K * R / Real.log R) :=
          sum_le_sum hlayer_le
      _ = C_tot * (Real.log (Real.log R) ^ K / Real.log R) * R := by
          rw [sum_const, nsmul_eq_mul]
          have hIcc_c : (Finset.Icc 1 (K + 1)).card = K + 1 := by simp [Nat.card_Icc]
          rw [hIcc_c]
          simp only [C_tot]; push_cast; ring
      _ ≤ (ε / 2) * R := mul_le_mul_of_nonneg_right hsmall hR0.le
  -- Squarefree count lower bound on `(R, 2R]`
  have hsq_low : (6 / Real.pi ^ (2 : ℕ) - ε / 2) * R ≤ ((squarefreeOf S).card : ℝ) := by
    have habs := abs_card_squarefreeOf_dyadic_sub_le hR1
    have hsqrt_err : 3 * Real.sqrt R + 1 ≤ (ε / 2) * R := by
      have h1 : 3 * Real.sqrt R + 1 ≤ 4 * Real.sqrt R := by
        have : 1 ≤ Real.sqrt R := (Real.le_sqrt (by norm_num) hR0.le).mpr (by linarith)
        linarith
      have h2 : 4 * Real.sqrt R ≤ (ε / 2) * R := by
        have hsq_ineq : (4 * Real.sqrt R) ^ 2 ≤ ((ε / 2) * R) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hR0.le]
          have h16 : (16 : ℝ) ≤ (ε / 2) ^ 2 * R := by
            rw [div_pow] at hR_sq
            have hε2 : 0 < ε ^ 2 := by positivity
            rw [div_le_iff₀ hε2] at hR_sq
            linarith
          nlinarith
        exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq_ineq
      linarith
    have hlow1 := (abs_le.mp habs).1
    linarith
  have hsdiff : M.unmatchedSet.card + M.matchedSet.card = (squarefreeOf S).card :=
    card_sdiff_add_card_eq_card M.matchedSet_subset
  have hsdiff_real : (M.unmatchedSet.card : ℝ) =
      ((squarefreeOf S).card : ℝ) - (M.matchedSet.card : ℝ) := by
    have : (M.unmatchedSet.card : ℝ) + (M.matchedSet.card : ℝ) = ((squarefreeOf S).card : ℝ) := by
      exact_mod_cast hsdiff
    linarith
  rw [hsdiff_real]
  linarith

/-- **Prescribed-cofactor gcd stratification of `factorLayer S k`**: for any `M₀ ≥ 1`,
`factorLayer S k` partitions into disjoint strata indexed by `g ∈ M₀.divisors` (`g = gcd(n, M₀)`),
tracking exact cofactor consumption on `P₀`. -/
theorem factorLayer_card_eq_sum_gcd_strata (S : Finset ℕ) (k M₀ : ℕ) (hM₀ : 1 ≤ M₀) :
    (factorLayer S k).card =
      ∑ g ∈ M₀.divisors, ((factorLayer S k).filter (fun n => Nat.gcd n M₀ = g)).card := by
  classical
  have hpart : factorLayer S k =
      M₀.divisors.biUnion (fun g => (factorLayer S k).filter (fun n => Nat.gcd n M₀ = g)) := by
    ext n
    simp only [mem_biUnion, mem_filter, Nat.mem_divisors]
    constructor
    · intro hn
      exact ⟨Nat.gcd n M₀, ⟨Nat.gcd_dvd_right n M₀, by omega⟩, hn, rfl⟩
    · rintro ⟨_, _, hn, _⟩
      exact hn
  conv_lhs => rw [hpart]
  rw [card_biUnion]
  intro g₁ _ g₂ _ hne
  simp only [Function.onFun]
  rw [disjoint_left]
  intro n h₁ h₂
  exact hne ((mem_filter.mp h₁).2.symm.trans (mem_filter.mp h₂).2)

/-- Every `{2, 3, 5}`-divisible target in `factorLayer (Ioc R (2R)) (k + 1)` arises as `q * m`
for some `q ∈ {2, 3, 5}` and `m ∈ factorLayer (Ioc (R / q) (2 * R / q)) k`, bounding the total
`{2, 3, 5}`-divisible `(k+1)`-prime supply by `∑_{q ∈ {2, 3, 5}} #Q_k(R/q, 2R/q)` and forcing
single-prime `{2, 3, 5}` supply ratio `(31/30) log log R / k < 1` once `k > (31/30) log log R`. -/
theorem smallCofactor_divisible_card_le_and_threshold (R k : ℕ) :
    ((factorLayer (Ioc R (2 * R)) (k + 1)).filter (fun n => ¬ Nat.Coprime n 30)).card ≤
      ∑ q ∈ ({2, 3, 5} : Finset ℕ), (factorLayer (Ioc (R / q) (2 * R / q)) k).card ∧
    ((31 / 30 : ℝ) * Real.log (Real.log R) < (k : ℝ) → 0 < (k : ℝ) →
      (31 / 30 : ℝ) * Real.log (Real.log R) / (k : ℝ) < 1) := by
  refine ⟨?_, fun hlt hk0 => (div_lt_one hk0).mpr hlt⟩
  have hsub : (factorLayer (Ioc R (2 * R)) (k + 1)).filter (fun n => ¬ Nat.Coprime n 30) ⊆
      ({2, 3, 5} : Finset ℕ).biUnion
        (fun q => (factorLayer (Ioc (R / q) (2 * R / q)) k).image (q * ·)) := by
    intro n hn
    obtain ⟨hn_fl, hnot_cop⟩ := mem_filter.mp hn
    obtain ⟨hnIoc, hsq, hcard⟩ := mem_filter.mp hn_fl
    obtain ⟨hnR, hn2R⟩ := mem_Ioc.mp hnIoc
    obtain ⟨q, hqp, hqn, hq30⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnot_cop
    have hq_mem : q ∈ ({2, 3, 5} : Finset ℕ) := by
      have h30 : (30 : ℕ) = 2 * 3 * 5 := by norm_num
      rw [h30] at hq30
      rcases (Nat.Prime.dvd_mul hqp).mp hq30 with h23 | h5
      · rcases (Nat.Prime.dvd_mul hqp).mp h23 with h2 | h3
        · have := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_two).mp h2; subst this; decide
        · have := (Nat.prime_dvd_prime_iff_eq hqp Nat.prime_three).mp h3; subst this; decide
      · have := (Nat.prime_dvd_prime_iff_eq hqp (by norm_num : Nat.Prime 5)).mp h5
        subst this; decide
    have hn_sf : n ∈ sfLayer (2 * R) (k + 1) :=
      mem_sfLayer.mpr ⟨by omega, hn2R, hsq, hcard⟩
    have hq_pf : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, hqn, by omega⟩
    obtain ⟨_, hm_sf, hmul⟩ := div_prime_mem_sfLayer hn_sf hq_pf
    obtain ⟨_, _, hsq_m, hcard_m⟩ := mem_sfLayer.mp hm_sf
    refine mem_biUnion.mpr ⟨q, hq_mem, mem_image.mpr ⟨n / q, ?_, hmul⟩⟩
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, hsq_m, hcard_m⟩
    · rw [Nat.div_lt_iff_lt_mul hqp.pos, mul_comm]; exact (hmul.symm ▸ hnR)
    · exact Nat.div_le_div_right hn2R
  exact (card_le_card hsub).trans (card_biUnion_le.trans (sum_le_sum fun _ _ => card_image_le))

end GaloisForLFunctions.QuantitativeFactorizationMatching

