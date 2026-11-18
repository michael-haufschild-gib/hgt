import GaloisForLFunctions.QuantitativeFactorizationMatching.OreDeficiencyAndCascadeConservation
import GaloisForLFunctions.BezoutValuationIncidence.CoprimeSquarefreeDensityAndMobiusDilationMeans
import GaloisForLFunctions.BezoutValuationIncidence.CoprimeMobiusCancellationAndOddDilationMeans
import GaloisForLFunctions.RHTower.PrimeCellPartition

/-!
# Prescribed-Cofactor and Bounded-Arity Local Matching Obstructions Across All Factor Counts

Definitive negative answer to extending local or prescribed-prime squarefree matchings across all
factor counts on dyadic blocks `(X, 2X]`, classifying the deficient source families and proving
super-polynomial / linear unmatched populations on **every** sufficiently large dyadic block:

1. **Prescribed finite prime set `P₀` (`eventually_prescribedPrimeExchange_unmatched_linear`)**:
   Under all opposite-parity exchanges `a u ↔ a v` whose exchanged prime factors lie in any finite
   prime set `P₀` (with arbitrary common cofactor `a` and arbitrary group sizes), every `P₀`-rough
   squarefree integer in `(X, 2X]` has zero admissible neighbors. Both Möbius-sign halves of the
   `P₀`-rough family have exact asymptotic density `(3/π²) ∏_{p ∈ P₀} p/(p+1) > 0`, forcing at
   least `((6/π²) ∏_{p ∈ P₀} p/(p+1) - ε) X` unmatched integers on every large dyadic block.
2. **Asymmetric upward saturation (`eventually_prescribedUpward_saturated_unmatched_linear`)**:
   Every squarefree multiple of `M₀ = ∏_{p ∈ P₀} p` in `(X, 2X]` admits zero squarefree upward
   targets `a q r ∈ (X, 2X]` (`n = a p`, `q ∈ P₀`, `r` prime), forming a positive-density
   `(6 / (π² M₀)) ∏_{p ∈ P₀} p/(p+1)` family with exhausted `P₀`-cofactor headroom.
3. **Power-local bounded-arity exchanges (`eventually_powerLocal_boundedArity_isolated_ge`)**:
   For any arity bound `k`, exponent `θ < 1`, and `C > 0`, on every large dyadic block `(X, 2X]`
   at least `c X / (log X)^r` balanced `r`-primes are isolated under all exchanges of width
   `≤ C X^θ` with `ω(u), ω(v) ≤ k`, exceeding `X^β` for every `β < 1`.
4. **Log-power cell bounded-arity exchanges (`eventually_logPowerCell_boundedArity_unmatched_gt_rpow`)**:
   At the exact cell scale `H ≤ C X / (log X)^B` of the prime–semiprime construction, whenever
   `B > k`, for every `β < 1 - k / B` every matching on `(X, 2X]` leaves strictly more than `X^β`
   isolated friable squarefree integers unmatched (exceeding `X^{1/2+δ}` when `B > 2k` and
   exceeding `X^{20999/24000+δ}` when `B > 24000k`).
-/

open Finset Filter Topology
open RHTower RHTower.PrimeCells RHTower.Sieve GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators ArithmeticFunction.Moebius

noncomputable section

namespace GaloisForLFunctions.QuantitativeFactorizationMatching

/-! ### 1. Shared combinatorial, prime-product, and window-prime primitives -/

private theorem prod_primes_props {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) :
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

private theorem prod_le_pow_card_nat {T : Finset ℕ} {Z : ℕ} (h : ∀ p ∈ T, p ≤ Z) :
    ∏ p ∈ T, p ≤ Z ^ T.card := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert p s hps ih =>
    rw [prod_insert hps, card_insert_of_notMem hps, pow_succ']
    exact Nat.mul_le_mul (h p (mem_insert_self p s))
      (ih fun q hq => h q (mem_insert_of_mem hq))

/-- Elementary binomial lower bound `M^r ≤ r^r · M.choose r` for all `r ≤ M`. -/
theorem pow_le_pow_mul_choose : ∀ (r M : ℕ), r ≤ M → M ^ r ≤ r ^ r * M.choose r
  | 0, _, _ => by simp
  | _ + 1, 0, h => by omega
  | s + 1, n + 1, h => by
    have hsn : s ≤ n := by omega
    have ih := pow_le_pow_mul_choose s n hsn
    have hlin : s * (n + 1) ≤ (s + 1) * n := by nlinarith
    have hpow : s ^ s * (n + 1) ^ s ≤ (s + 1) ^ s * n ^ s := by
      rw [← mul_pow, ← mul_pow]
      exact Nat.pow_le_pow_left hlin s
    have hstep : s ^ s * (n + 1) ^ s ≤ s ^ s * ((s + 1) ^ s * n.choose s) :=
      calc s ^ s * (n + 1) ^ s
          ≤ (s + 1) ^ s * n ^ s := hpow
        _ ≤ (s + 1) ^ s * (s ^ s * n.choose s) := Nat.mul_le_mul_left _ ih
        _ = s ^ s * ((s + 1) ^ s * n.choose s) := by ring
    have hs_pos : 0 < s ^ s := by
      rcases Nat.eq_zero_or_pos s with rfl | hs0
      · simp
      · exact Nat.pow_pos hs0
    have hdiv := Nat.le_of_mul_le_mul_left hstep hs_pos
    have hch := Nat.add_one_mul_choose_eq n s
    calc (n + 1) ^ (s + 1)
        = (n + 1) * (n + 1) ^ s := pow_succ' (n + 1) s
      _ ≤ (n + 1) * ((s + 1) ^ s * n.choose s) := Nat.mul_le_mul_left _ hdiv
      _ = (s + 1) ^ s * ((n + 1) * n.choose s) := by ring
      _ = (s + 1) ^ s * ((n + 1).choose (s + 1) * (s + 1)) := by rw [hch]
      _ = (s + 1) ^ (s + 1) * (n + 1).choose (s + 1) := by rw [pow_succ']; ring

/-- Multiplicative subset-product landing lemma: if `1 < a`, `∀ q ∈ A, a ≤ q ≤ b`, and
`1 ≤ W₀ < a ^ A.card`, then some subset `S ⊆ A` satisfies `∏_{q ∈ S} q ≤ W₀ < b * ∏_{q ∈ S} q`. -/
theorem exists_subset_prod_le_and_lt_mul {A : Finset ℕ} {a b : ℝ} (ha : 1 < a)
    (hA : ∀ q ∈ A, a ≤ (q : ℝ) ∧ (q : ℝ) ≤ b) :
    ∀ {W₀ : ℝ}, 1 ≤ W₀ → W₀ < a ^ A.card →
      ∃ S ⊆ A, (∏ q ∈ S, (q : ℝ)) ≤ W₀ ∧ W₀ < b * (∏ q ∈ S, (q : ℝ)) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
    intro W₀ hW1 hWlt
    simp only [card_empty, pow_zero] at hWlt
    linarith
  | @insert q s hqs ih =>
    intro W₀ hW1 hWlt
    have hq_ab := hA q (mem_insert_self q s)
    have hq_pos : (0 : ℝ) < q := by linarith
    have hs_ab : ∀ x ∈ s, a ≤ (x : ℝ) ∧ (x : ℝ) ≤ b :=
      fun x hx => hA x (mem_insert_of_mem hx)
    rcases lt_or_ge W₀ (q : ℝ) with hlt | hge
    · exact ⟨∅, empty_subset _, by simp [hW1], by simp; linarith [hq_ab.2]⟩
    · have hW1' : 1 ≤ W₀ / (q : ℝ) := (one_le_div hq_pos).mpr hge
      have hWlt' : W₀ / (q : ℝ) < a ^ s.card := by
        rw [card_insert_of_notMem hqs, pow_succ] at hWlt
        have hmul : W₀ / (q : ℝ) * a ≤ W₀ := by
          calc W₀ / (q : ℝ) * a ≤ W₀ / (q : ℝ) * (q : ℝ) := by
                gcongr; exact hq_ab.1
            _ = W₀ := div_mul_cancel₀ W₀ hq_pos.ne'
        have ha0 : 0 < a := by linarith
        exact lt_of_mul_lt_mul_right (hmul.trans_lt hWlt) ha0.le
      obtain ⟨S', hS's, hle', hlt'⟩ := ih hs_ab hW1' hWlt'
      have hqS' : q ∉ S' := fun hmem => hqs (hS's hmem)
      refine ⟨insert q S', insert_subset_iff.mpr ⟨mem_insert_self q s,
        hS's.trans (subset_insert q s)⟩, ?_, ?_⟩
      · rw [prod_insert hqS']
        calc (q : ℝ) * ∏ x ∈ S', (x : ℝ) ≤ (q : ℝ) * (W₀ / (q : ℝ)) :=
              mul_le_mul_of_nonneg_left hle' hq_pos.le
          _ = W₀ := mul_div_cancel₀ W₀ hq_pos.ne'
      · rw [prod_insert hqS']
        have hmul_lt := mul_lt_mul_of_pos_left hlt' hq_pos
        rw [mul_div_cancel₀ W₀ hq_pos.ne'] at hmul_lt
        linarith

/-- Prime count lower bound in constant-ratio windows `(u, α u]` (`α > 1`). -/
theorem exists_windowPrimes_const_ratio_ge {α : ℝ} (hα : 1 < α) :
    ∃ U₀ : ℝ, 4 ≤ U₀ ∧ ∀ u : ℝ, U₀ ≤ u →
      ((α - 1) / 2) * u / Real.log (α * u) ≤ ((windowPrimes u (α * u)).card : ℝ) := by
  obtain ⟨C, hC, T₀, hT₀, hθ⟩ := exists_abs_theta_sub_le 1
  have hα0 : 0 < α - 1 := by linarith
  have hev : ∀ᶠ u : ℝ in atTop,
      T₀ ≤ u ∧ 4 ≤ u ∧ 4 * C * α / (α - 1) ≤ Real.log u :=
    (eventually_ge_atTop _).and ((eventually_ge_atTop _).and
      (Real.tendsto_log_atTop.eventually_ge_atTop _))
  obtain ⟨U₀, hU₀⟩ := eventually_atTop.mp hev
  refine ⟨max U₀ 4, le_max_right _ _, fun u hu => ?_⟩
  obtain ⟨hTu, hu4, hCu⟩ := hU₀ u ((le_max_left _ _).trans hu)
  have hu0 : 0 < u := by linarith
  have hab : u ≤ α * u := by nlinarith
  have hlogu : 0 < Real.log u := Real.log_pos (by linarith)
  have hlogαu : 0 < Real.log (α * u) := Real.log_pos (by nlinarith)
  have hinc := abs_theta_increment_le hC.le hT₀ hθ hTu hab
  have herr : 2 * C * (α * u) / Real.log u ^ (1 : ℕ) ≤ ((α - 1) / 2) * u := by
    rw [pow_one, div_le_iff₀ hlogu]
    rw [div_le_iff₀ hα0] at hCu
    nlinarith
  have hθ_ge : ((α - 1) / 2) * u ≤ Chebyshev.theta (α * u) - Chebyshev.theta u := by
    have h1 := (abs_le.mp hinc).1
    have e : α * u - u = (α - 1) * u := by ring
    linarith
  have hcard := theta_sub_le_card_mul_log hu0.le hab
  rw [div_le_iff₀ hlogαu]
  linarith

/-! ### 2. Prescribed finite prime set `P₀`: rough isolation and upward cofactor saturation -/

/-- Opposite-parity exchange `a = c u ↔ b = c v` whose exchanged prime factors lie in `P₀`. -/
def PrescribedPrimeExchange (P₀ : Finset ℕ) (a b : ℕ) : Prop :=
  μ a = -μ b ∧
    ∃ c u v : ℕ, a = c * u ∧ b = c * v ∧ u.primeFactors ⊆ P₀ ∧ v.primeFactors ⊆ P₀

/-- Every `P₀`-rough squarefree integer in `(X, 2X]` is completely isolated under
`PrescribedPrimeExchange P₀` (no common-cofactor `P₀`-move stays in `(X, 2X]`). -/
theorem coprime_mem_isolatedVertices_prescribedPrimeExchange {P₀ : Finset ℕ}
    (_hP₀ : ∀ p ∈ P₀, p.Prime) {X n : ℕ} (hX : 1 ≤ X)
    (hn : n ∈ squarefreeOf (Ioc X (2 * X))) (hcop : Nat.Coprime (∏ p ∈ P₀, p) n) :
    n ∈ isolatedVertices (PrescribedPrimeExchange P₀) (Ioc X (2 * X)) := by
  classical
  have hunit_of_cop : ∀ {m c w : ℕ}, m ∈ squarefreeOf (Ioc X (2 * X)) →
      Nat.Coprime (∏ p ∈ P₀, p) m → m = c * w → w.primeFactors ⊆ P₀ → w = 1 := by
    intro m c w hm hcop_m hmc hwP
    obtain ⟨hmIoc, hsq_m⟩ := mem_filter.mp hm
    have hm_pos : 0 < m := lt_of_le_of_lt (by omega) (mem_Ioc.mp hmIoc).1
    have hw_pos : 0 < w := by
      rcases Nat.eq_zero_or_pos w with rfl | hpos
      · rw [mul_zero] at hmc; omega
      · exact hpos
    have hsq_w : Squarefree w := (Nat.squarefree_mul_iff.mp (hmc ▸ hsq_m)).2.2
    have hemp : w.primeFactors = ∅ := by
      refine eq_empty_iff_forall_notMem.mpr fun p hp => ?_
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hp_dvd_w : p ∣ w := Nat.dvd_of_mem_primeFactors hp
      have hp_dvd_m : p ∣ m := hmc ▸ dvd_mul_of_dvd_right hp_dvd_w c
      have hp_dvd_M : p ∣ ∏ q ∈ P₀, q := dvd_prod_of_mem id (hwP hp)
      exact hpp.not_dvd_one (hcop_m.gcd_eq_one ▸ Nat.dvd_gcd hp_dvd_M hp_dvd_m)
    rw [← Nat.prod_primeFactors_of_squarefree hsq_w, hemp, prod_empty]
  rw [isolatedVertices, mem_union]
  rcases mem_union.mp (squarefreeOf_eq_posParity_union_negParity _ ▸ hn) with hnP | hnN
  · refine Or.inl (mem_filter.mpr ⟨hnP, fun b hb hrel => ?_⟩)
    obtain ⟨hμ, c, u, v, ha_eq, hb_eq, huP, _⟩ := hrel
    have hu1 : u = 1 := hunit_of_cop hn hcop ha_eq huP
    rw [hu1, mul_one] at ha_eq
    subst ha_eq
    have hbIoc := (mem_filter.mp hb).1
    have hcIoc := (mem_filter.mp hnP).1
    obtain ⟨hcX, _⟩ := mem_Ioc.mp hcIoc
    obtain ⟨hbX, hb2X⟩ := mem_Ioc.mp hbIoc
    have hv_ge2 : 2 ≤ v := by
      rcases eq_or_ne v 0 with rfl | hv0
      · rw [mul_zero] at hb_eq; omega
      rcases eq_or_ne v 1 with rfl | hv1
      · rw [mul_one] at hb_eq; subst hb_eq
        have h1 := (mem_filter.mp hnP).2
        have h2 := (mem_filter.mp hb).2
        omega
      · omega
    have hmul : (X + 1) * 2 ≤ n * v := Nat.mul_le_mul hcX hv_ge2
    omega
  · refine Or.inr (mem_filter.mpr ⟨hnN, fun a ha hrel => ?_⟩)
    obtain ⟨hμ, c, u, v, ha_eq, hb_eq, _, hvP⟩ := hrel
    have hv1 : v = 1 := hunit_of_cop hn hcop hb_eq hvP
    rw [hv1, mul_one] at hb_eq
    subst hb_eq
    have haIoc := (mem_filter.mp ha).1
    have hcIoc := (mem_filter.mp hnN).1
    obtain ⟨hcX, _⟩ := mem_Ioc.mp hcIoc
    obtain ⟨haX, ha2X⟩ := mem_Ioc.mp haIoc
    have hu_ge2 : 2 ≤ u := by
      rcases eq_or_ne u 0 with rfl | hu0
      · rw [mul_zero] at ha_eq; omega
      rcases eq_or_ne u 1 with rfl | hu1
      · rw [mul_one] at ha_eq; subst ha_eq
        have h1 := (mem_filter.mp ha).2
        have h2 := (mem_filter.mp hnN).2
        omega
      · omega
    have hmul : (X + 1) * 2 ≤ n * u := Nat.mul_le_mul hcX hu_ge2
    omega

/-- **Global `P₀`-rough linear unmatched theorem**: For every finite set of primes `P₀`, both
positive- and negative-Möbius `P₀`-rough families in `(X, 2X]` have asymptotic density
`(3/π²) ∏_{p ∈ P₀} p/(p+1) > 0`, and for every `ε > 0`, eventually every `PrescribedPrimeExchange P₀`
matching on `(X, 2X]` leaves at least `((6/π²) ∏_{p ∈ P₀} p/(p+1) - ε) X` unmatched integers. -/
theorem eventually_prescribedPrimeExchange_unmatched_linear (P₀ : Finset ℕ)
    (hP₀ : ∀ p ∈ P₀, p.Prime) :
    let D := (6 / Real.pi ^ (2 : ℕ)) * ∏ p ∈ P₀, (p : ℝ) / ((p : ℝ) + 1)
    0 < D ∧
    Tendsto (fun X : ℕ =>
      (((posParity (Ioc X (2 * X))).filter (Nat.Coprime (∏ p ∈ P₀, p) ·)).card : ℝ) / X)
      atTop (𝓝 (D / 2)) ∧
    Tendsto (fun X : ℕ =>
      (((negParity (Ioc X (2 * X))).filter (Nat.Coprime (∏ p ∈ P₀, p) ·)).card : ℝ) / X)
      atTop (𝓝 (D / 2)) ∧
    ∀ {ε : ℝ}, 0 < ε → ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ M : OppositeParityMatching (PrescribedPrimeExchange P₀) (Ioc X (2 * X)),
        (D - ε) * (X : ℝ) ≤ (M.unmatchedSet.card : ℝ) := by
  intro D
  set M₀ : ℕ := ∏ p ∈ P₀, p
  obtain ⟨hsq_M₀, hpf_M₀, _⟩ := prod_primes_props hP₀
  have hD_pos : 0 < D := by
    refine mul_pos (by positivity) (prod_pos fun p hp => ?_)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP₀ p hp).pos
    positivity
  have hD_eq : coprimeSquarefreeDensity M₀ = D := by
    simp only [coprimeSquarefreeDensity, squarefreeDensity_eq, M₀, hpf_M₀, D]
  -- Dyadic coprime squarefree count and Möbius sum limits along `ℕ`
  have hmean_1 : Tendsto (fun X : ℕ => coprimeSquarefreeMean M₀ (X : ℝ)) atTop (𝓝 D) := by
    rw [← hD_eq]
    exact (tendsto_coprimeSquarefreeMean_of_squarefree M₀ hsq_M₀).comp tendsto_natCast_atTop_atTop
  have hmean_2 : Tendsto (fun X : ℕ => coprimeSquarefreeMean M₀ (2 * (X : ℝ))) atTop (𝓝 D) := by
    rw [← hD_eq]
    have h2 : Tendsto (fun X : ℕ => 2 * (X : ℝ)) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_natCast_atTop_atTop
    exact (tendsto_coprimeSquarefreeMean_of_squarefree M₀ hsq_M₀).comp h2
  have hmob_1 : Tendsto (fun X : ℕ => coprimeMoebiusMean M₀ (X : ℝ)) atTop (𝓝 0) :=
    (tendsto_coprimeMoebiusMean M₀).comp tendsto_natCast_atTop_atTop
  have hmob_2 : Tendsto (fun X : ℕ => coprimeMoebiusMean M₀ (2 * (X : ℝ))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun X : ℕ => 2 * (X : ℝ)) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_natCast_atTop_atTop
    exact (tendsto_coprimeMoebiusMean M₀).comp h2
  -- Express dyadic positive and negative rough counts via `coprimeSquarefreeCount` and `coprimeMoebiusSum`
  let roughPos (X : ℕ) := (posParity (Ioc X (2 * X))).filter (Nat.Coprime M₀ ·)
  let roughNeg (X : ℕ) := (negParity (Ioc X (2 * X))).filter (Nat.Coprime M₀ ·)
  have hsum_diff : ∀ X : ℕ, 1 ≤ X →
      ((roughPos X).card : ℝ) + ((roughNeg X).card : ℝ) =
        ((2 * coprimeSquarefreeMean M₀ (2 * (X : ℝ)) - coprimeSquarefreeMean M₀ (X : ℝ)) * X) ∧
      ((roughPos X).card : ℝ) - ((roughNeg X).card : ℝ) =
        ((2 * coprimeMoebiusMean M₀ (2 * (X : ℝ)) - coprimeMoebiusMean M₀ (X : ℝ)) * X) := by
    intro X hX1
    have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
    have hIcc_split : Finset.Icc 1 (2 * X) = Finset.Icc 1 X ∪ Finset.Ioc X (2 * X) := by
      ext n; simp only [mem_Icc, mem_union, mem_Ioc]; omega
    have hIcc_disj : Disjoint (Finset.Icc 1 X) (Finset.Ioc X (2 * X)) := by
      rw [disjoint_left]; intro n h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
    have hfl_2X : ⌊2 * (X : ℝ)⌋₊ = 2 * X := by
      have : 2 * (X : ℝ) = ((2 * X : ℕ) : ℝ) := by push_cast; ring
      rw [this, Nat.floor_natCast]
    have hfl_X : ⌊(X : ℝ)⌋₊ = X := Nat.floor_natCast X
    have hsq_dyad : ∑ n ∈ Finset.Ioc X (2 * X), coprimeSquarefreeIndicator M₀ n =
        ((roughPos X).card : ℝ) + ((roughNeg X).card : ℝ) := by
      classical
      have hdisj_pn : Disjoint (roughPos X) (roughNeg X) :=
        Disjoint.mono (filter_subset _ _) (filter_subset _ _) (disjoint_posParity_negParity _)
      have hunion_sub : roughPos X ∪ roughNeg X ⊆ Finset.Ioc X (2 * X) :=
        union_subset ((filter_subset _ _).trans (filter_subset _ _))
          ((filter_subset _ _).trans (filter_subset _ _))
      rw [← sum_subset hunion_sub (fun n hnIoc hnot => by
        unfold coprimeSquarefreeIndicator
        split_ifs with hcop
        · by_cases hsq : Squarefree n
          · rcases moebius_eq_one_or_neg_one_of_squarefree hsq with h1 | h1
            · exact False.elim (hnot (mem_union_left _
                (mem_filter.mpr ⟨mem_filter.mpr ⟨hnIoc, h1⟩, hcop⟩)))
            · exact False.elim (hnot (mem_union_right _
                (mem_filter.mpr ⟨mem_filter.mpr ⟨hnIoc, h1⟩, hcop⟩)))
          · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
        · rfl), sum_union hdisj_pn]
      have hp1 : ∑ n ∈ roughPos X, coprimeSquarefreeIndicator M₀ n = ((roughPos X).card : ℝ) := by
        calc ∑ n ∈ roughPos X, coprimeSquarefreeIndicator M₀ n
            = ∑ _n ∈ roughPos X, (1 : ℝ) := sum_congr rfl fun n hn => by
              obtain ⟨hp, hcop⟩ := mem_filter.mp hn
              simp [coprimeSquarefreeIndicator, hcop, (mem_filter.mp hp).2]
          _ = ((roughPos X).card : ℝ) := by simp
      have hn1 : ∑ n ∈ roughNeg X, coprimeSquarefreeIndicator M₀ n = ((roughNeg X).card : ℝ) := by
        calc ∑ n ∈ roughNeg X, coprimeSquarefreeIndicator M₀ n
            = ∑ _n ∈ roughNeg X, (1 : ℝ) := sum_congr rfl fun n hn => by
              obtain ⟨hp, hcop⟩ := mem_filter.mp hn
              simp [coprimeSquarefreeIndicator, hcop, (mem_filter.mp hp).2]
          _ = ((roughNeg X).card : ℝ) := by simp
      rw [hp1, hn1]
    have hmob_dyad : ∑ n ∈ Finset.Ioc X (2 * X), coprimeMoebiusIndicator M₀ n =
        ((roughPos X).card : ℝ) - ((roughNeg X).card : ℝ) := by
      classical
      have hdisj_pn : Disjoint (roughPos X) (roughNeg X) :=
        Disjoint.mono (filter_subset _ _) (filter_subset _ _) (disjoint_posParity_negParity _)
      have hunion_sub : roughPos X ∪ roughNeg X ⊆ Finset.Ioc X (2 * X) :=
        union_subset ((filter_subset _ _).trans (filter_subset _ _))
          ((filter_subset _ _).trans (filter_subset _ _))
      rw [← sum_subset hunion_sub (fun n hnIoc hnot => by
        unfold coprimeMoebiusIndicator
        split_ifs with hcop
        · by_cases hsq : Squarefree n
          · rcases moebius_eq_one_or_neg_one_of_squarefree hsq with h1 | h1
            · exact False.elim (hnot (mem_union_left _
                (mem_filter.mpr ⟨mem_filter.mpr ⟨hnIoc, h1⟩, hcop⟩)))
            · exact False.elim (hnot (mem_union_right _
                (mem_filter.mpr ⟨mem_filter.mpr ⟨hnIoc, h1⟩, hcop⟩)))
          · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
        · rfl), sum_union hdisj_pn]
      have hp1 : ∑ n ∈ roughPos X, coprimeMoebiusIndicator M₀ n = ((roughPos X).card : ℝ) := by
        calc ∑ n ∈ roughPos X, coprimeMoebiusIndicator M₀ n
            = ∑ _n ∈ roughPos X, (1 : ℝ) := sum_congr rfl fun n hn => by
              obtain ⟨hp, hcop⟩ := mem_filter.mp hn
              simp [coprimeMoebiusIndicator, hcop, (mem_filter.mp hp).2]
          _ = ((roughPos X).card : ℝ) := by simp
      have hn1 : ∑ n ∈ roughNeg X, coprimeMoebiusIndicator M₀ n = -((roughNeg X).card : ℝ) := by
        calc ∑ n ∈ roughNeg X, coprimeMoebiusIndicator M₀ n
            = ∑ _n ∈ roughNeg X, (-1 : ℝ) := sum_congr rfl fun n hn => by
              obtain ⟨hp, hcop⟩ := mem_filter.mp hn
              simp [coprimeMoebiusIndicator, hcop, (mem_filter.mp hp).2]
          _ = -((roughNeg X).card : ℝ) := by simp
      rw [hp1, hn1]; ring
    constructor
    · simp only [coprimeSquarefreeMean, hfl_2X, hfl_X, coprimeSquarefreeCount]
      rw [hIcc_split, sum_union hIcc_disj, hsq_dyad]
      field_simp; ring
    · simp only [coprimeMoebiusMean, hfl_2X, hfl_X, coprimeMoebiusSum]
      rw [hIcc_split, sum_union hIcc_disj, hmob_dyad]
      field_simp; ring
  have hsum_lim : Tendsto (fun X : ℕ => (((roughPos X).card : ℝ) + ((roughNeg X).card : ℝ)) / X)
      atTop (𝓝 D) := by
    have htarget : Tendsto (fun X : ℕ =>
        2 * coprimeSquarefreeMean M₀ (2 * (X : ℝ)) - coprimeSquarefreeMean M₀ (X : ℝ))
        atTop (𝓝 (2 * D - D)) := (hmean_2.const_mul 2).sub hmean_1
    rw [show 2 * D - D = D by ring] at htarget
    refine htarget.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with X hX1
    have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
    rw [(hsum_diff X hX1).1, mul_div_cancel_right₀ _ hX0]
  have hdiff_lim : Tendsto (fun X : ℕ => (((roughPos X).card : ℝ) - ((roughNeg X).card : ℝ)) / X)
      atTop (𝓝 0) := by
    have htarget : Tendsto (fun X : ℕ =>
        2 * coprimeMoebiusMean M₀ (2 * (X : ℝ)) - coprimeMoebiusMean M₀ (X : ℝ))
        atTop (𝓝 (2 * (0 : ℝ) - 0)) := (hmob_2.const_mul 2).sub hmob_1
    norm_num at htarget
    refine htarget.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with X hX1
    have hX0 : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
    rw [(hsum_diff X hX1).2, mul_div_cancel_right₀ _ hX0]
  have hpos_lim : Tendsto (fun X : ℕ => ((roughPos X).card : ℝ) / X) atTop (𝓝 (D / 2)) := by
    have h := (hsum_lim.add hdiff_lim).div_const 2
    rw [add_zero] at h
    refine h.congr fun X => ?_
    ring
  have hneg_lim : Tendsto (fun X : ℕ => ((roughNeg X).card : ℝ) / X) atTop (𝓝 (D / 2)) := by
    have h := (hsum_lim.sub hdiff_lim).div_const 2
    rw [sub_zero] at h
    refine h.congr fun X => ?_
    ring
  refine ⟨hD_pos, hpos_lim, hneg_lim, fun {ε} hε => ?_⟩
  have hev_ge : ∀ᶠ X : ℕ in atTop,
      1 ≤ X ∧ D - ε ≤ (((roughPos X).card : ℝ) + ((roughNeg X).card : ℝ)) / X :=
    (eventually_ge_atTop 1).and (hsum_lim.eventually (Ici_mem_nhds (by linarith)))
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hev_ge
  refine ⟨X₀, fun X hX M => ?_⟩
  obtain ⟨hX1, hrat⟩ := hX₀ X hX
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX1
  have hsub_iso : roughPos X ∪ roughNeg X ⊆
      isolatedVertices (PrescribedPrimeExchange P₀) (Ioc X (2 * X)) := by
    intro n hn
    rcases mem_union.mp hn with hp | hng
    · obtain ⟨hnP, hcop⟩ := mem_filter.mp hp
      have hsq : n ∈ squarefreeOf (Ioc X (2 * X)) := by
        rw [squarefreeOf_eq_posParity_union_negParity]
        exact mem_union_left _ hnP
      exact coprime_mem_isolatedVertices_prescribedPrimeExchange hP₀ hX1 hsq hcop
    · obtain ⟨hnN, hcop⟩ := mem_filter.mp hng
      have hsq : n ∈ squarefreeOf (Ioc X (2 * X)) := by
        rw [squarefreeOf_eq_posParity_union_negParity]
        exact mem_union_right _ hnN
      exact coprime_mem_isolatedVertices_prescribedPrimeExchange hP₀ hX1 hsq hcop
  have hdisj_pn : Disjoint (roughPos X) (roughNeg X) :=
    Disjoint.mono (filter_subset _ _) (filter_subset _ _) (disjoint_posParity_negParity _)
  have hcard_le : (roughPos X).card + (roughNeg X).card ≤ M.unmatchedSet.card := by
    rw [← card_union_of_disjoint hdisj_pn]
    exact (card_le_card hsub_iso).trans (card_isolatedVertices_le_unmatched M)
  rw [le_div_iff₀ hX0] at hrat
  calc (D - ε) * (X : ℝ)
      ≤ ((roughPos X).card : ℝ) + ((roughNeg X).card : ℝ) := hrat
    _ ≤ (M.unmatchedSet.card : ℝ) := by exact_mod_cast hcard_le

/-- **Asymmetric upward cofactor-saturation obstruction**: Every squarefree multiple `n` of
`M₀ = ∏_{p ∈ P₀} p` in `(X, 2X]` admits zero squarefree upward `(1 → 2)` targets `a q r ∈ (X, 2X]`
with `n = a p`, `p, r` prime, `q ∈ P₀`; and the saturated family `{n ∈ Q(X) : M₀ ∣ n}` has
positive asymptotic density `(6 / (π² M₀)) ∏_{p ∈ P₀} p / (p + 1) > 0`. -/
theorem prescribedUpward_saturated_no_target_and_density (P₀ : Finset ℕ)
    (hP₀ : ∀ p ∈ P₀, p.Prime) :
    let M₀ := ∏ p ∈ P₀, p
    let D_sat := ((6 / Real.pi ^ (2 : ℕ)) * ∏ p ∈ P₀, (p : ℝ) / ((p : ℝ) + 1)) / M₀
    0 < D_sat ∧
    (∀ {X n a p q r : ℕ}, 1 ≤ X → n ∈ squarefreeOf (Ioc X (2 * X)) → M₀ ∣ n →
      n = a * p → p.Prime → q ∈ P₀ → r.Prime →
      ¬ (a * q * r ∈ squarefreeOf (Ioc X (2 * X)))) ∧
    Tendsto (fun X : ℕ =>
      (((squarefreeOf (Ioc X (2 * X))).filter (M₀ ∣ ·)).card : ℝ) / X)
      atTop (𝓝 D_sat) := by
  intro M₀ D_sat
  obtain ⟨hsq_M₀, hpf_M₀, hM₀_pos⟩ := prod_primes_props hP₀
  have hD_pos : 0 < D_sat := by
    have hM₀_r : (0 : ℝ) < M₀ := by exact_mod_cast hM₀_pos
    refine div_pos (mul_pos (by positivity) (prod_pos fun p hp => ?_)) hM₀_r
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hP₀ p hp).pos
    positivity
  refine ⟨hD_pos, fun {X n a p q r} hX1 hn hdvd hnap hp hq hr hmem_tar => ?_, ?_⟩
  · -- Saturated upward obstruction
    obtain ⟨hmIoc, hsq_tar⟩ := mem_filter.mp hmem_tar
    obtain ⟨hnIoc, _⟩ := mem_filter.mp hn
    have hqp : q.Prime := hP₀ q hq
    have hqM : q ∣ M₀ := dvd_prod_of_mem id hq
    have hqn : q ∣ a * p := hnap ▸ hqM.trans hdvd
    rcases eq_or_ne q p with rfl | hqp_ne
    · -- `q = p`, so `a * q * r = n * r ≥ 2 * (X + 1) > 2 * X`
      have heq_nr : a * q * r = n * r := by rw [← hnap]
      have hnX : X + 1 ≤ n := (mem_Ioc.mp hnIoc).1
      have hm2X : a * q * r ≤ 2 * X := (mem_Ioc.mp hmIoc).2
      have hr2 : 2 ≤ r := hr.two_le
      have : 2 * (X + 1) ≤ n * r := by nlinarith
      omega
    · -- `q ≠ p`, so `q ∣ a` and `q² ∣ a * q * r`, violating `Squarefree`
      have hcop_qp : Nat.Coprime q p := (Nat.coprime_primes hqp hp).mpr hqp_ne
      have hqa : q ∣ a := hcop_qp.dvd_of_dvd_mul_right hqn
      obtain ⟨b, rfl⟩ := hqa
      have hnot_sq : ¬ Squarefree (q * b * q * r) := by
        intro hsq
        have hunit : IsUnit q := hsq q ⟨b * r, by ring⟩
        exact hqp.ne_one (Nat.isUnit_iff.mp hunit)
      exact hnot_sq hsq_tar
  · -- Bijection `m ↦ M₀ * m` with `P₀`-rough squarefrees in `Ioc (X / M₀) (2 * X / M₀)`
    obtain ⟨D₀, hD₀_def⟩ : ∃ D₀ : ℝ,
      D₀ = (6 / Real.pi ^ (2 : ℕ)) * ∏ p ∈ P₀, (p : ℝ) / ((p : ℝ) + 1) := ⟨_, rfl⟩
    have hD₀_eq : coprimeSquarefreeDensity M₀ = D₀ := by
      simp only [coprimeSquarefreeDensity, squarefreeDensity_eq, M₀, hpf_M₀, hD₀_def]
    have hbij_card : ∀ X : ℕ,
        ((squarefreeOf (Ioc X (2 * X))).filter (M₀ ∣ ·)).card =
          ((squarefreeOf (Ioc (X / M₀) (2 * X / M₀))).filter (Nat.Coprime M₀ ·)).card := by
      intro X
      classical
      refine Finset.card_bij (fun n _ => n / M₀) ?_ ?_ ?_
      · intro n hn
        obtain ⟨hn_sq, hdvd⟩ := mem_filter.mp hn
        obtain ⟨hnIoc, hsq_n⟩ := mem_filter.mp hn_sq
        obtain ⟨hnX, hn2X⟩ := mem_Ioc.mp hnIoc
        have hmul : M₀ * (n / M₀) = n := Nat.mul_div_cancel' hdvd
        obtain ⟨hcop, _, hsq_q⟩ := Nat.squarefree_mul_iff.mp (hmul ▸ hsq_n)
        refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, hsq_q⟩, hcop⟩
        · rw [Nat.div_lt_iff_lt_mul hM₀_pos, mul_comm]; exact hmul.symm ▸ hnX
        · exact Nat.div_le_div_right hn2X
      · intro n₁ hn₁ n₂ hn₂ heq
        have hd₁ := (mem_filter.mp hn₁).2
        have hd₂ := (mem_filter.mp hn₂).2
        calc n₁ = M₀ * (n₁ / M₀) := (Nat.mul_div_cancel' hd₁).symm
          _ = M₀ * (n₂ / M₀) := by rw [heq]
          _ = n₂ := Nat.mul_div_cancel' hd₂
      · intro m hm
        obtain ⟨hm_sq, hcop⟩ := mem_filter.mp hm
        obtain ⟨hmIoc, hsq_m⟩ := mem_filter.mp hm_sq
        obtain ⟨hm1, hm2⟩ := mem_Ioc.mp hmIoc
        refine ⟨M₀ * m, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩,
          Nat.squarefree_mul_iff.mpr ⟨hcop, hsq_M₀, hsq_m⟩⟩, dvd_mul_right M₀ m⟩,
          Nat.mul_div_cancel_left m hM₀_pos⟩
        · rw [Nat.div_lt_iff_lt_mul hM₀_pos] at hm1
          simpa only [mul_comm] using hm1
        · calc M₀ * m ≤ M₀ * (2 * X / M₀) := Nat.mul_le_mul_left M₀ hm2
            _ ≤ 2 * X := Nat.mul_div_le (2 * X) M₀
    have hcount_eq : ∀ N : ℕ,
        (((squarefreeOf (Icc 1 N)).filter (Nat.Coprime M₀ ·)).card : ℝ) =
          coprimeSquarefreeCount M₀ N := by
      intro N
      classical
      unfold coprimeSquarefreeCount
      have hsub : (squarefreeOf (Icc 1 N)).filter (Nat.Coprime M₀ ·) ⊆ Icc 1 N :=
        (filter_subset _ _).trans (filter_subset _ _)
      calc (((squarefreeOf (Icc 1 N)).filter (Nat.Coprime M₀ ·)).card : ℝ)
          = ∑ _n ∈ (squarefreeOf (Icc 1 N)).filter (Nat.Coprime M₀ ·), (1 : ℝ) := by simp
        _ = ∑ n ∈ (squarefreeOf (Icc 1 N)).filter (Nat.Coprime M₀ ·),
              coprimeSquarefreeIndicator M₀ n :=
            sum_congr rfl fun n hn => by
              obtain ⟨hn_sq, hcop⟩ := mem_filter.mp hn
              rcases moebius_eq_one_or_neg_one_of_squarefree (mem_filter.mp hn_sq).2 with h | h <;>
                simp [coprimeSquarefreeIndicator, hcop, h]
        _ = ∑ n ∈ Icc 1 N, coprimeSquarefreeIndicator M₀ n :=
            sum_subset hsub fun n hn hnot => by
              unfold coprimeSquarefreeIndicator
              split_ifs with hcop
              · by_cases hsq : Squarefree n
                · exact False.elim (hnot (mem_filter.mpr ⟨mem_filter.mpr ⟨hn, hsq⟩, hcop⟩))
                · simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
              · rfl
    have hmean_base := tendsto_coprimeSquarefreeMean_of_squarefree M₀ hsq_M₀
    rw [hD₀_eq] at hmean_base
    have hM₀_r : (0 : ℝ) < M₀ := by exact_mod_cast hM₀_pos
    have hlim_1 : Tendsto (fun X : ℕ => coprimeSquarefreeCount M₀ (X / M₀) / (X : ℝ))
        atTop (𝓝 (D₀ / M₀)) := by
      have hscale : Tendsto (fun X : ℕ => (X : ℝ) / M₀) atTop atTop :=
        (tendsto_mul_const_atTop_of_pos (inv_pos.mpr hM₀_r)).mpr tendsto_natCast_atTop_atTop
      have hcomp := (hmean_base.comp hscale).div_const (M₀ : ℝ)
      refine hcomp.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with X _
      simp only [Function.comp_apply, coprimeSquarefreeMean, Nat.floor_div_natCast,
        Nat.floor_natCast, div_div]
      rw [div_mul_cancel₀ _ hM₀_r.ne']
    have hlim_2 : Tendsto (fun X : ℕ => coprimeSquarefreeCount M₀ (2 * X / M₀) / (X : ℝ))
        atTop (𝓝 (2 * (D₀ / M₀))) := by
      have hscale : Tendsto (fun X : ℕ => 2 * (X : ℝ) / M₀) atTop atTop := by
        have h2 : Tendsto (fun X : ℕ => 2 * (X : ℝ)) atTop atTop :=
          (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_natCast_atTop_atTop
        exact (tendsto_mul_const_atTop_of_pos (inv_pos.mpr hM₀_r)).mpr h2
      have hcomp := ((hmean_base.comp hscale).const_mul 2).div_const (M₀ : ℝ)
      rw [mul_div_assoc] at hcomp
      refine hcomp.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with X _
      have h2X : 2 * (X : ℝ) = ((2 * X : ℕ) : ℝ) := by push_cast; ring
      simp only [Function.comp_apply, coprimeSquarefreeMean, h2X, Nat.floor_div_natCast,
        Nat.floor_natCast]
      have hX_ne : (X : ℝ) ≠ 0 := by exact_mod_cast (show X ≠ 0 by omega)
      have hM_ne : (M₀ : ℝ) ≠ 0 := hM₀_r.ne'
      push_cast; field_simp
    have hdiff := hlim_2.sub hlim_1
    rw [show 2 * (D₀ / (M₀ : ℝ)) - D₀ / (M₀ : ℝ) = D_sat by simp only [D_sat, hD₀_def]; ring] at hdiff
    refine hdiff.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with X _
    rw [hbij_card X]
    obtain ⟨a_div, ha_div⟩ : ∃ a_div : ℕ, a_div = X / M₀ := ⟨_, rfl⟩
    obtain ⟨b_div, hb_div⟩ : ∃ b_div : ℕ, b_div = 2 * X / M₀ := ⟨_, rfl⟩
    rw [← ha_div, ← hb_div]
    have hle_div : a_div ≤ b_div := by rw [ha_div, hb_div]; exact Nat.div_le_div_right (by omega)
    have hsplit : Finset.Icc 1 b_div = Finset.Icc 1 a_div ∪ Finset.Ioc a_div b_div := by
      ext k; simp only [mem_Icc, mem_union, mem_Ioc]; omega
    have hdisj_i : Disjoint (Finset.Icc 1 a_div) (Finset.Ioc a_div b_div) := by
      rw [disjoint_left]; intro k h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega
    have hcard_split :
        ((squarefreeOf (Icc 1 b_div)).filter (Nat.Coprime M₀ ·)).card =
          ((squarefreeOf (Icc 1 a_div)).filter (Nat.Coprime M₀ ·)).card +
            ((squarefreeOf (Ioc a_div b_div)).filter (Nat.Coprime M₀ ·)).card := by
      classical
      have hunion_f :
          (squarefreeOf (Icc 1 b_div)).filter (Nat.Coprime M₀ ·) =
            (squarefreeOf (Icc 1 a_div)).filter (Nat.Coprime M₀ ·) ∪
              (squarefreeOf (Ioc a_div b_div)).filter (Nat.Coprime M₀ ·) := by
        ext k
        simp only [squarefreeOf, mem_filter, mem_union, hsplit]
        tauto
      rw [hunion_f, card_union_of_disjoint]
      exact Disjoint.mono ((filter_subset _ _).trans (filter_subset _ _))
        ((filter_subset _ _).trans (filter_subset _ _)) hdisj_i
    rw [← hcount_eq b_div, ← hcount_eq a_div, hcard_split]
    push_cast; ring

/-! ### 3. Bounded-arity local exchanges: deterministic smooth isolation criterion -/

/-- Opposite-parity common-cofactor exchange `a = c u ↔ b = c v` of distance `≤ H` and
exchanged prime-group arities `ω(u), ω(v) ≤ k`. -/
def BoundedArityLocalExchange (k : ℕ) (H : ℝ) (a b : ℕ) : Prop :=
  |(b : ℝ) - a| ≤ H ∧ μ a = -μ b ∧
    ∃ c u v : ℕ, a = c * u ∧ b = c * v ∧ u.primeFactors.card ≤ k ∧ v.primeFactors.card ≤ k

/-- **Universal smooth isolation criterion**: Any squarefree integer `n ∈ (X, 2X]` whose prime
factors are all `≤ Z`, where `Z^k · H ≤ X`, has zero admissible `BoundedArityLocalExchange k H`
neighbors in `(X, 2X]`. -/
theorem mem_isolatedVertices_of_primeFactors_le {k X Z n : ℕ} {H : ℝ}
    (hn : n ∈ squarefreeOf (Ioc X (2 * X)))
    (hZ : ∀ p ∈ n.primeFactors, p ≤ Z)
    (hZH : (Z : ℝ) ^ k * H ≤ X) :
    n ∈ isolatedVertices (BoundedArityLocalExchange k H) (Ioc X (2 * X)) := by
  classical
  have hno_edge : ∀ {m c w w' : ℕ}, m ∈ squarefreeOf (Ioc X (2 * X)) →
      |(m : ℝ) - n| ≤ H → μ m = -μ n → n = c * w → m = c * w' →
      w.primeFactors.card ≤ k → False := by
    intro m c w w' _ hdist hμ hnw hmw' hwk
    obtain ⟨hnIoc, hsq_n⟩ := mem_filter.mp hn
    have hnX : X < n := (mem_Ioc.mp hnIoc).1
    have hn_pos : 0 < n := by omega
    have hw_pos : 0 < w := by
      rcases Nat.eq_zero_or_pos w with rfl | hpos
      · rw [mul_zero] at hnw; omega
      · exact hpos
    have hsq_w : Squarefree w := (Nat.squarefree_mul_iff.mp (hnw ▸ hsq_n)).2.2
    have hw_le_Zk : w ≤ Z ^ k := by
      rcases Nat.eq_zero_or_pos Z with rfl | hZpos
      · have hemp : w.primeFactors = ∅ := by
          refine eq_empty_iff_forall_notMem.mpr fun p hp => ?_
          have hpp := Nat.prime_of_mem_primeFactors hp
          have hpn : p ∈ n.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨hpp, hnw ▸ dvd_mul_of_dvd_right
              (Nat.dvd_of_mem_primeFactors hp) c, hn_pos.ne'⟩
          exact absurd (hZ p hpn) (not_le_of_gt hpp.pos)
        have hw1 : w = 1 := by
          rw [← Nat.prod_primeFactors_of_squarefree hsq_w, hemp, prod_empty]
        have hn_gt1 : 1 < n := by
          rcases Nat.eq_zero_or_pos X with rfl | hXpos
          · have hH_nn : 0 ≤ H := (abs_nonneg _).trans hdist
            -- When `X = 0` and `n ∈ Ioc 0 0`, impossible!
            simp at hnIoc
          · omega
        have hp_ex : n.minFac ∈ n.primeFactors :=
          Nat.mem_primeFactors.mpr ⟨Nat.minFac_prime hn_gt1.ne', Nat.minFac_dvd n, hn_pos.ne'⟩
        have := hZ n.minFac hp_ex
        have := (Nat.minFac_prime hn_gt1.ne').two_le
        omega
      · calc w = ∏ p ∈ w.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq_w).symm
          _ ≤ Z ^ w.primeFactors.card := prod_le_pow_card_nat fun p hp => by
              have hpp := Nat.prime_of_mem_primeFactors hp
              exact hZ p (Nat.mem_primeFactors.mpr ⟨hpp,
                hnw ▸ dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors hp) c, hn_pos.ne'⟩)
          _ ≤ Z ^ k := Nat.pow_le_pow_right hZpos hwk
    have hw_ne : w ≠ w' := by
      intro heq
      have hmn : m = n := by rw [hmw', hnw, heq]
      subst hmn
      rcases moebius_eq_one_or_neg_one_of_squarefree hsq_n with h1 | h1 <;> omega
    have hdiff_ge1 : (1 : ℝ) ≤ |(w' : ℝ) - w| := by
      rcases lt_or_gt_of_ne hw_ne with hlt | hgt
      · have : (w : ℝ) + 1 ≤ w' := by exact_mod_cast hlt
        rw [abs_of_nonneg (by linarith)]; linarith
      · have : (w' : ℝ) + 1 ≤ w := by exact_mod_cast hgt
        rw [abs_of_nonpos (by linarith)]; linarith
    have hc_le_H : (c : ℝ) ≤ H := by
      calc (c : ℝ) = (c : ℝ) * 1 := (mul_one _).symm
        _ ≤ (c : ℝ) * |(w' : ℝ) - w| := mul_le_mul_of_nonneg_left hdiff_ge1 (Nat.cast_nonneg c)
        _ = |(m : ℝ) - n| := by
            rw [← abs_of_nonneg (Nat.cast_nonneg c : (0 : ℝ) ≤ c), ← abs_mul, hmw', hnw]
            push_cast; ring_nf
        _ ≤ H := hdist
    have hH0 : 0 ≤ H := (Nat.cast_nonneg c).trans hc_le_H
    have hn_le_X : (n : ℝ) ≤ X := by
      have hw_cast : (w : ℝ) ≤ (Z : ℝ) ^ k := by exact_mod_cast hw_le_Zk
      calc (n : ℝ) = (c : ℝ) * w := by exact_mod_cast hnw
        _ ≤ H * (Z : ℝ) ^ k := mul_le_mul hc_le_H hw_cast (Nat.cast_nonneg w) hH0
        _ = (Z : ℝ) ^ k * H := mul_comm _ _
        _ ≤ X := hZH
    have hnX' : (X : ℝ) < n := by exact_mod_cast hnX
    linarith
  rw [isolatedVertices, mem_union]
  rcases mem_union.mp (squarefreeOf_eq_posParity_union_negParity _ ▸ hn) with hnP | hnN
  · refine Or.inl (mem_filter.mpr ⟨hnP, fun b hb ⟨hdist, hμ, c, u, v, ha_eq, hb_eq, huk, _⟩ => ?_⟩)
    have hb_sq : b ∈ squarefreeOf (Ioc X (2 * X)) := by
      rw [squarefreeOf_eq_posParity_union_negParity]; exact mem_union_right _ hb
    exact hno_edge hb_sq hdist (by omega) ha_eq hb_eq huk
  · refine Or.inr (mem_filter.mpr ⟨hnN, fun a ha ⟨hdist, hμ, c, u, v, ha_eq, hb_eq, _, hvk⟩ => ?_⟩)
    have ha_sq : a ∈ squarefreeOf (Ioc X (2 * X)) := by
      rw [squarefreeOf_eq_posParity_union_negParity]; exact mem_union_left _ ha
    rw [abs_sub_comm] at hdist
    exact hno_edge ha_sq hdist hμ hb_eq ha_eq hvk

/-! ### 4. All-block power-local obstruction (`H ≤ C X^θ`, `θ < 1`) -/

/-- Combinatorial injection of balanced `r`-prime products `d_T * p_*` (`T ∈ P_low^(r-1)`) into
`isolatedVertices (BoundedArityLocalExchange k H) (Ioc X (2 * X))`. -/
private lemma powerLocal_family_isolated_card {k r X : ℕ} {H Y : ℝ} {P_low : Finset ℕ}
    (hr2 : 2 ≤ r) (hY_pos : 0 < Y) (hYr_split : Y * Y ^ (r - 1) = (X : ℝ))
    (hPlow_sub : ∀ p ∈ P_low, p.Prime ∧ Y / 2 < (p : ℝ) ∧ (p : ℝ) ≤ 3 / 4 * Y)
    (hZH : ((⌊(2 : ℝ) ^ r * Y⌋₊ : ℕ) : ℝ) ^ k * H ≤ X) :
    ∑ T ∈ P_low.powersetCard (r - 1),
      (windowPrimes ((X : ℝ) / (∏ p ∈ T, p)) (2 * ((X : ℝ) / (∏ p ∈ T, p)))).card ≤
      (isolatedVertices (BoundedArityLocalExchange k H) (Ioc X (2 * X))).card := by
  classical
  obtain ⟨F, hF_def⟩ : ∃ F : Finset ℕ, F = (P_low.powersetCard (r - 1)).biUnion fun T =>
    (windowPrimes ((X : ℝ) / (∏ p ∈ T, p)) (2 * ((X : ℝ) / (∏ p ∈ T, p)))).image
      fun p_star => (∏ p ∈ T, p) * p_star := ⟨_, rfl⟩
  obtain ⟨Z, hZ_def⟩ : ∃ Z : ℕ, Z = ⌊(2 : ℝ) ^ r * Y⌋₊ := ⟨_, rfl⟩
  rw [← hZ_def] at hZH
  have hT_bounds : ∀ T ∈ P_low.powersetCard (r - 1),
      Squarefree (∏ p ∈ T, p) ∧ (∏ p ∈ T, p).primeFactors = T ∧ 0 < (∏ p ∈ T, p) ∧
      (Y / 2) ^ (r - 1) ≤ ((∏ p ∈ T, p : ℕ) : ℝ) ∧
      ((∏ p ∈ T, p : ℕ) : ℝ) ≤ (3 / 4) * Y ^ (r - 1) ∧
      (∀ p ∈ T, p.Prime ∧ (p : ℝ) ≤ 3 / 4 * Y) := by
    intro T hT
    obtain ⟨hTP, hTcard⟩ := mem_powersetCard.mp hT
    have hp_in : ∀ p ∈ T, p.Prime ∧ Y / 2 < (p : ℝ) ∧ (p : ℝ) ≤ 3 / 4 * Y :=
      fun p hp => hPlow_sub p (hTP hp)
    obtain ⟨hsq_d, hpf_d, hd_pos⟩ := prod_primes_props (fun p hp => (hp_in p hp).1)
    have hd_low : (Y / 2) ^ (r - 1) ≤ ((∏ p ∈ T, p : ℕ) : ℝ) := by
      rw [Nat.cast_prod, ← hTcard]
      calc (Y / 2) ^ T.card = ∏ _p ∈ T, (Y / 2) := (prod_const _).symm
        _ ≤ ∏ p ∈ T, (p : ℝ) := prod_le_prod (fun _ _ => by positivity)
            (fun p hp => (hp_in p hp).2.1.le)
    have hd_up : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ (3 / 4) * Y ^ (r - 1) := by
      have h1 : ((∏ p ∈ T, p : ℕ) : ℝ) ≤ (3 / 4 * Y) ^ (r - 1) := by
        rw [Nat.cast_prod, ← hTcard]
        calc ∏ p ∈ T, (p : ℝ)
            ≤ ∏ _p ∈ T, (3 / 4 * Y) := prod_le_prod (fun p _ => Nat.cast_nonneg p)
              (fun p hp => (hp_in p hp).2.2)
          _ = (3 / 4 * Y) ^ T.card := prod_const _
      have h34_pow : (3 / 4 : ℝ) ^ (r - 1) ≤ 3 / 4 := by
        obtain ⟨s, hs⟩ : ∃ s, r - 1 = s + 1 := ⟨r - 2, by omega⟩
        rw [hs, pow_succ']
        have hpow_le : (3 / 4 : ℝ) ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith only [hpow_le]
      calc ((∏ p ∈ T, p : ℕ) : ℝ) ≤ (3 / 4 : ℝ) ^ (r - 1) * Y ^ (r - 1) := by
            rwa [mul_pow] at h1
        _ ≤ (3 / 4) * Y ^ (r - 1) := mul_le_mul_of_nonneg_right h34_pow (by positivity)
    exact ⟨hsq_d, hpf_d, hd_pos, hd_low, hd_up, fun p hp => ⟨(hp_in p hp).1, (hp_in p hp).2.2⟩⟩
  have hF_sub : F ⊆ isolatedVertices (BoundedArityLocalExchange k H) (Ioc X (2 * X)) := by
    intro n hn
    rw [hF_def] at hn
    obtain ⟨T, hT, hn_img⟩ := mem_biUnion.mp hn
    obtain ⟨p_star, hp_star, rfl⟩ := mem_image.mp hn_img
    obtain ⟨hsq_d, hpf_d, hd_pos, hd_low, hd_up, hT_pr⟩ := hT_bounds T hT
    obtain ⟨d, hd_def⟩ : ∃ d : ℕ, d = ∏ p ∈ T, p := ⟨_, rfl⟩
    rw [← hd_def] at hsq_d hpf_d hd_pos hd_low hd_up hp_star ⊢
    have hd_r : (0 : ℝ) < d := by exact_mod_cast hd_pos
    have hX_pos : (0 : ℝ) < X := by rw [← hYr_split]; positivity
    obtain ⟨hps_pr, hps_lt, hps_le⟩ :=
      (mem_windowPrimes (by positivity) (by positivity)).mp hp_star
    have hXd_gt : (4 / 3) * Y ≤ (X : ℝ) / d := by
      rw [le_div_iff₀ hd_r]
      calc (4 / 3) * Y * (d : ℝ) ≤ (4 / 3) * Y * ((3 / 4) * Y ^ (r - 1)) :=
            mul_le_mul_of_nonneg_left hd_up (by positivity)
        _ = Y * Y ^ (r - 1) := by ring
        _ = X := hYr_split
    have hXd_up : 2 * ((X : ℝ) / d) ≤ (2 : ℝ) ^ r * Y := by
      rw [mul_div_assoc', div_le_iff₀ hd_r]
      calc 2 * (X : ℝ) = 2 * (Y * Y ^ (r - 1)) := by rw [hYr_split]
        _ = (2 : ℝ) ^ r * Y * (Y / 2) ^ (r - 1) := by
            obtain ⟨s, hs⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
            rw [hs]; simp only [Nat.add_sub_cancel]; rw [pow_succ, div_pow]; field_simp
        _ ≤ (2 : ℝ) ^ r * Y * (d : ℝ) := mul_le_mul_of_nonneg_left hd_low (by positivity)
    have hps_notMem : p_star ∉ T := by
      intro hmem
      have hp_le := (hT_pr p_star hmem).2
      linarith only [hp_le, hXd_gt, hps_lt, hY_pos]
    have hcop_dps : Nat.Coprime d p_star := by
      rw [hd_def]
      exact Nat.Coprime.prod_left fun p hp =>
        (Nat.coprime_primes (hT_pr p hp).1 hps_pr).mpr fun heq => hps_notMem (heq ▸ hp)
    have hsq_n : Squarefree (d * p_star) :=
      Nat.squarefree_mul_iff.mpr ⟨hcop_dps, hsq_d, Irreducible.squarefree hps_pr⟩
    have hnIoc : d * p_star ∈ Ioc X (2 * X) := by
      rw [div_lt_iff₀ hd_r] at hps_lt
      rw [mul_div_assoc', le_div_iff₀ hd_r] at hps_le
      refine mem_Ioc.mpr ⟨?_, ?_⟩
      · exact_mod_cast (show (X : ℝ) < (d * p_star : ℕ) by push_cast; linarith only [hps_lt])
      · exact_mod_cast (show ((d * p_star : ℕ) : ℝ) ≤ (2 * X : ℕ) by push_cast; linarith only [hps_le])
    have hZ_all : ∀ p ∈ (d * p_star).primeFactors, p ≤ Z := by
      intro p hp
      rw [hZ_def]
      rw [Nat.primeFactors_mul hd_pos.ne' hps_pr.ne_zero, hpf_d, hps_pr.primeFactors] at hp
      rcases mem_union.mp hp with hpT | hpS
      · have h1 := (hT_pr p hpT).2
        have h4_le : (4 : ℝ) ≤ (2 : ℝ) ^ r := by
          calc (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
            _ ≤ (2 : ℝ) ^ r := pow_le_pow_right₀ (by norm_num) hr2
        exact Nat.le_floor (by nlinarith [h1, h4_le, hY_pos])
      · rw [mem_singleton.mp hpS]
        exact Nat.le_floor (hps_le.trans hXd_up)
    exact mem_isolatedVertices_of_primeFactors_le (mem_filter.mpr ⟨hnIoc, hsq_n⟩) hZ_all hZH
  have hrec : ∀ (T : Finset ℕ), T ∈ P_low.powersetCard (r - 1) →
      ∀ ps ∈ windowPrimes ((X : ℝ) / (∏ p ∈ T, p)) (2 * ((X : ℝ) / (∏ p ∈ T, p))),
        ((∏ p ∈ T, p) * ps).primeFactors.filter (· ≤ ⌊3 / 4 * Y⌋₊) = T := by
    intro T hT ps hps
    obtain ⟨_, hpf_d, hd_pos, _, hd_up, hT_pr⟩ := hT_bounds T hT
    obtain ⟨d, hd_def⟩ : ∃ d : ℕ, d = ∏ p ∈ T, p := ⟨_, rfl⟩
    rw [← hd_def] at hpf_d hd_pos hd_up hps ⊢
    have hd_r : (0 : ℝ) < d := by exact_mod_cast hd_pos
    have hX_pos : (0 : ℝ) < X := by rw [← hYr_split]; positivity
    obtain ⟨hps_pr, hps_lt, _⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hps
    rw [div_lt_iff₀ hd_r] at hps_lt
    have hps_gt : 3 / 4 * Y < (ps : ℝ) := by
      by_contra hc; push Not at hc
      have hle_prod : (d : ℝ) * ps ≤ ((3 / 4) * Y ^ (r - 1)) * (3 / 4 * Y) :=
        mul_le_mul hd_up hc (Nat.cast_nonneg ps) (by positivity)
      have h916 : ((3 / 4) * Y ^ (r - 1)) * (3 / 4 * Y) = (9 / 16) * (Y * Y ^ (r - 1)) := by ring
      rw [h916, hYr_split] at hle_prod
      linarith only [hle_prod, hps_lt, hX_pos]
    rw [Nat.primeFactors_mul hd_pos.ne' hps_pr.ne_zero, hpf_d, hps_pr.primeFactors]
    ext q
    simp only [mem_filter, mem_union, mem_singleton]
    constructor
    · rintro ⟨hqT | hq_ps, hqle⟩
      · exact hqT
      · rw [hq_ps] at hqle
        have hb : (ps : ℝ) ≤ 3 / 4 * Y :=
          (Nat.cast_le.mpr hqle).trans (Nat.floor_le (by positivity))
        linarith only [hb, hps_gt]
    · intro hqT
      exact ⟨Or.inl hqT, Nat.le_floor (hT_pr q hqT).2⟩
  have hF_card : F.card = ∑ T ∈ P_low.powersetCard (r - 1),
      (windowPrimes ((X : ℝ) / (∏ p ∈ T, p)) (2 * ((X : ℝ) / (∏ p ∈ T, p)))).card := by
    rw [hF_def, card_biUnion]
    · refine sum_congr rfl fun T hT => card_image_of_injOn fun p₁ _ p₂ _ heq => ?_
      exact Nat.eq_of_mul_eq_mul_left (hT_bounds T hT).2.2.1 heq
    · intro T₁ hT₁ T₂ hT₂ hne
      simp only [Function.onFun]
      rw [disjoint_left]
      intro n hn₁ hn₂
      obtain ⟨p₁, hp₁, rfl⟩ := mem_image.mp hn₁
      obtain ⟨p₂, hp₂, heq⟩ := mem_image.mp hn₂
      have hf₁ := hrec T₁ hT₁ p₁ hp₁
      have hf₂ := hrec T₂ hT₂ p₂ hp₂
      exact hne (hf₁.symm.trans (heq ▸ hf₂))
  rw [← hF_card]
  exact card_le_card hF_sub

/-- Upgrading `c * X / (log X)^r ≤ g X` to `X^β < g X` for every `β < 1`. -/
private lemma eventually_rpow_lt_of_div_log_pow {r X₀ : ℕ} {c : ℝ} {g : ℕ → ℝ}
    (hc : 0 < c) (hg : ∀ X : ℕ, X₀ ≤ X → c * (X : ℝ) / Real.log X ^ r ≤ g X)
    {β : ℝ} (hβ : β < 1) :
    ∃ X₁ : ℕ, ∀ Y : ℕ, X₁ ≤ Y → (Y : ℝ) ^ β < g Y := by
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = (1 - β) / 2 := ⟨_, rfl⟩
  have hη_pos : 0 < η := by rw [hη_def]; linarith only [hβ]
  have hev_β : ∀ᶠ y : ℝ in atTop,
      3 ≤ y ∧ (r.factorial : ℝ) / (η ^ r * c) + 1 ≤ y ^ η :=
    (eventually_ge_atTop 3).and ((tendsto_rpow_atTop hη_pos).eventually_ge_atTop _)
  obtain ⟨Y_cut, hY_cut⟩ := eventually_atTop.mp hev_β
  refine ⟨max X₀ ⌈Y_cut⌉₊, fun Y hY => ?_⟩
  have hY_main := hg Y (le_of_max_le_left hY)
  have hY_ge_cut : Y_cut ≤ (Y : ℝ) :=
    (Nat.le_ceil Y_cut).trans (by exact_mod_cast le_of_max_le_right hY)
  obtain ⟨hY3, hYη⟩ := hY_cut Y hY_ge_cut
  clear hev_β hY_cut hY_ge_cut
  have hY0 : (0 : ℝ) < Y := by linarith only [hY3]
  have hlogY0 : 0 < Real.log Y := Real.log_pos (by linarith only [hY3])
  have hexp_η := Real.pow_div_factorial_le_exp (η * Real.log Y) (by positivity) r
  rw [show Real.exp (η * Real.log Y) = (Y : ℝ) ^ η by
    rw [Real.rpow_def_of_pos hY0, mul_comm]] at hexp_η
  have hfac_pos : (0 : ℝ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have hlogr_le : Real.log Y ^ r ≤ ((r.factorial : ℝ) / η ^ r) * (Y : ℝ) ^ η := by
    rw [mul_pow, div_le_iff₀ hfac_pos] at hexp_η
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    linarith only [hexp_η]
  have hYβ_lt : (Y : ℝ) ^ β < c * (Y : ℝ) / Real.log Y ^ r := by
    rw [lt_div_iff₀ (by positivity)]
    have h1 : (Y : ℝ) ^ β * Real.log Y ^ r ≤
        ((r.factorial : ℝ) / η ^ r) * (Y : ℝ) ^ (β + η) := by
      calc (Y : ℝ) ^ β * Real.log Y ^ r
          ≤ (Y : ℝ) ^ β * (((r.factorial : ℝ) / η ^ r) * (Y : ℝ) ^ η) :=
            mul_le_mul_of_nonneg_left hlogr_le (by positivity)
        _ = ((r.factorial : ℝ) / η ^ r) * ((Y : ℝ) ^ β * (Y : ℝ) ^ η) := by ring
        _ = ((r.factorial : ℝ) / η ^ r) * (Y : ℝ) ^ (β + η) := by rw [← Real.rpow_add hY0]
    have hexp_sum : (Y : ℝ) = (Y : ℝ) ^ η * (Y : ℝ) ^ (β + η) := by
      rw [← Real.rpow_add hY0, hη_def,
        show (1 - β) / 2 + (β + (1 - β) / 2) = 1 by ring, Real.rpow_one]
    have hstrict : (r.factorial : ℝ) / η ^ r < c * (Y : ℝ) ^ η := by
      have hmul := mul_lt_mul_of_pos_right
        (show (r.factorial : ℝ) / (η ^ r * c) < (Y : ℝ) ^ η by linarith only [hYη])
        (show 0 < η ^ r * c by positivity)
      rw [div_mul_cancel₀ _ (by positivity)] at hmul
      rw [div_lt_iff₀ (by positivity)]
      linarith only [hmul]
    have hpos_βη : 0 < (Y : ℝ) ^ (β + η) := Real.rpow_pos_of_pos hY0 _
    have h2 : ((r.factorial : ℝ) / η ^ r) * (Y : ℝ) ^ (β + η) < c * (Y : ℝ) := by
      calc ((r.factorial : ℝ) / η ^ r) * (Y : ℝ) ^ (β + η)
          < (c * (Y : ℝ) ^ η) * (Y : ℝ) ^ (β + η) := mul_lt_mul_of_pos_right hstrict hpos_βη
        _ = c * ((Y : ℝ) ^ η * (Y : ℝ) ^ (β + η)) := by ring
        _ = c * (Y : ℝ) := by rw [← hexp_sum]
    linarith only [h1, h2]
  exact hYβ_lt.trans_le hY_main

/-- **Power-local bounded-arity isolation (`H ≤ C X^θ`, `θ < 1`)**: For every arity `k`,
exponent `θ < 1`, and constant `C > 0`, choosing `r = ⌈(k + 2) / (1 - max θ 0)⌉₊ + 2`, there
exists `c > 0` such that on **every** sufficiently large dyadic block `(X, 2X]`, at least
`c X / (log X)^r` balanced `r`-primes are isolated under `BoundedArityLocalExchange k (C X^θ)`,
forcing strictly more than `X^β` unmatched integers for every `β < 1`. -/
theorem eventually_powerLocal_boundedArity_isolated_ge (k : ℕ) {θ C : ℝ}
    (hθ : θ < 1) (hC : 0 < C) :
    let r := ⌈((k : ℝ) + 2) / (1 - max θ 0)⌉₊ + 2
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      c * (X : ℝ) / Real.log X ^ r ≤
        ((isolatedVertices (BoundedArityLocalExchange k (C * (X : ℝ) ^ θ))
          (Ioc X (2 * X))).card : ℝ) ∧
      ∀ {β : ℝ}, β < 1 → ∃ X₁ : ℕ, ∀ Y : ℕ, X₁ ≤ Y →
        ∀ M : OppositeParityMatching (BoundedArityLocalExchange k (C * (Y : ℝ) ^ θ))
            (Ioc Y (2 * Y)),
          (Y : ℝ) ^ β < (M.unmatchedSet.card : ℝ) := by
  dsimp only
  obtain ⟨r, hr_def⟩ : ∃ r : ℕ, r = ⌈((k : ℝ) + 2) / (1 - max θ 0)⌉₊ + 2 := ⟨_, rfl⟩
  rw [← hr_def]
  have hr2 : 2 ≤ r := by omega
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have h1_sub : 0 < 1 - max θ 0 := by
    have hmax : max θ 0 < 1 := max_lt hθ (by norm_num)
    linarith only [hmax]
  have hexp_lt1 : (k : ℝ) / r + max θ 0 < 1 := by
    have hr_ge : ((k : ℝ) + 2) / (1 - max θ 0) ≤ r := by
      calc ((k : ℝ) + 2) / (1 - max θ 0) ≤ ⌈((k : ℝ) + 2) / (1 - max θ 0)⌉₊ := Nat.le_ceil _
        _ ≤ r := by rw [hr_def]; push_cast; linarith
    rw [div_le_iff₀ h1_sub] at hr_ge
    rw [← lt_sub_iff_add_lt, div_lt_iff₀ hr_pos]
    linarith only [hr_ge]
  obtain ⟨δ_gap, hδ_def⟩ : ∃ δ_gap : ℝ, δ_gap = 1 - ((k : ℝ) / r + max θ 0) := ⟨_, rfl⟩
  have hδ_pos : 0 < δ_gap := by rw [hδ_def]; linarith only [hexp_lt1]
  obtain ⟨U₁, _, hwin_32⟩ := exists_windowPrimes_const_ratio_ge (α := 3 / 2) (by norm_num)
  obtain ⟨U₂, _, hwin_2⟩ := exists_windowPrimes_const_ratio_ge (α := 2) (by norm_num)
  obtain ⟨c_r, hc_def⟩ : ∃ c_r : ℝ,
    c_r = (1 / (8 * (r : ℝ))) ^ (r - 1) * ((1 / 2 : ℝ) ^ (r + 1)) := ⟨_, rfl⟩
  have hc_pos : 0 < c_r := by rw [hc_def]; positivity
  have hrpow_r : Tendsto (fun x : ℝ => x ^ (1 / (r : ℝ))) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have hev' : ∀ᶠ x : ℝ in atTop,
      2 * U₁ ≤ x ^ (1 / (r : ℝ)) ∧ U₂ ≤ x ^ (1 / (r : ℝ)) ∧
      16 ≤ x ∧ 1 ≤ Real.log x ∧
      8 * (r : ℝ) ^ 3 ≤ x ^ (1 / (2 * (r : ℝ))) ∧
      ((2 : ℝ) ^ (r + 1)) ^ k * C ≤ x ^ δ_gap :=
    (hrpow_r.eventually_ge_atTop _).and ((hrpow_r.eventually_ge_atTop _).and
      ((eventually_ge_atTop 16).and ((Real.tendsto_log_atTop.eventually_ge_atTop 1).and
        (((tendsto_rpow_atTop (by positivity : 0 < 1 / (2 * (r : ℝ)))).eventually_ge_atTop _).and
          ((tendsto_rpow_atTop hδ_pos).eventually_ge_atTop _)))))
  obtain ⟨X_base, hX_base⟩ := eventually_atTop.mp hev'
  have hmain_bound : ∀ X : ℕ, max 1 ⌈X_base⌉₊ ≤ X →
      c_r * (X : ℝ) / Real.log X ^ r ≤
        ((isolatedVertices (BoundedArityLocalExchange k (C * (X : ℝ) ^ θ))
          (Ioc X (2 * X))).card : ℝ) := by
    intro X hX
    have hX_ge : X_base ≤ (X : ℝ) :=
      (Nat.le_ceil X_base).trans (by exact_mod_cast le_of_max_le_right hX)
    obtain ⟨hU1, hU2, hX16, hL1, hr_half, hδ_bound⟩ := hX_base X hX_ge
    clear hrpow_r hev' hX_base hX_ge
    have hX0 : (0 : ℝ) < X := by linarith only [hX16]
    have hL0 : 0 < Real.log X := by linarith only [hL1]
    obtain ⟨Y, hY_def⟩ : ∃ Y : ℝ, Y = (X : ℝ) ^ (1 / (r : ℝ)) := ⟨_, rfl⟩
    rw [← hY_def] at hU1 hU2
    have hY_pos : 0 < Y := by rw [hY_def]; positivity
    have hYr : Y ^ r = (X : ℝ) := by
      rw [hY_def, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le,
        one_div_mul_cancel hr_pos.ne', Real.rpow_one]
    have hYr_split : Y * Y ^ (r - 1) = (X : ℝ) := by
      have hr_eq : r = (r - 1) + 1 := by omega
      conv_rhs => rw [← hYr, hr_eq, pow_succ']
    have h8r_log : 8 * (r : ℝ) * Real.log X ≤ Y := by
      have hY_half_pos : 0 < (X : ℝ) ^ (1 / (2 * (r : ℝ))) := by positivity
      have hexp1 := Real.pow_div_factorial_le_exp (Real.log ((X : ℝ) ^ (1 / (2 * (r : ℝ)))))
        (by rw [Real.log_rpow hX0]; positivity) 1
      rw [Real.exp_log hY_half_pos, pow_one, Nat.factorial_one, Nat.cast_one, div_one,
        Real.log_rpow hX0] at hexp1
      have hlog_le : Real.log X ≤ 2 * (r : ℝ) * (X : ℝ) ^ (1 / (2 * (r : ℝ))) := by
        rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)] at hexp1
        linarith only [hexp1]
      have hY_sq : (X : ℝ) ^ (1 / (2 * (r : ℝ))) * (X : ℝ) ^ (1 / (2 * (r : ℝ))) = Y := by
        rw [hY_def, ← Real.rpow_add hX0]; congr 1; field_simp; ring
      have hr_ge2_r : (2 : ℝ) ≤ r := by exact_mod_cast hr2
      have h16_r2 : 16 * (r : ℝ) ^ 2 ≤ (X : ℝ) ^ (1 / (2 * (r : ℝ))) := by
        calc 16 * (r : ℝ) ^ 2 = 8 * (2 * (r : ℝ) ^ 2) := by ring
          _ ≤ 8 * ((r : ℝ) * (r : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hr_ge2_r (by positivity)) (by norm_num)
          _ = 8 * (r : ℝ) ^ 3 := by ring
          _ ≤ (X : ℝ) ^ (1 / (2 * (r : ℝ))) := hr_half
      calc 8 * (r : ℝ) * Real.log X
          ≤ 8 * (r : ℝ) * (2 * (r : ℝ) * (X : ℝ) ^ (1 / (2 * (r : ℝ)))) :=
            mul_le_mul_of_nonneg_left hlog_le (by positivity)
        _ = (16 * (r : ℝ) ^ 2) * (X : ℝ) ^ (1 / (2 * (r : ℝ))) := by ring
        _ ≤ (X : ℝ) ^ (1 / (2 * (r : ℝ))) * (X : ℝ) ^ (1 / (2 * (r : ℝ))) :=
            mul_le_mul_of_nonneg_right h16_r2 hY_half_pos.le
        _ = Y := hY_sq
    have hY16 : 16 ≤ Y := by
      have hr_ge2_r : (2 : ℝ) ≤ r := by exact_mod_cast hr2
      calc (16 : ℝ) = 8 * 2 * 1 := by norm_num
        _ ≤ 8 * (r : ℝ) * Real.log X :=
            mul_le_mul (mul_le_mul_of_nonneg_left hr_ge2_r (by norm_num)) hL1 zero_le_one (by positivity)
        _ ≤ Y := h8r_log
    obtain ⟨P_low, hPlow_def⟩ : ∃ P_low : Finset ℕ,
      P_low = windowPrimes (Y / 2) (3 / 2 * (Y / 2)) := ⟨_, rfl⟩
    have hPlow_sub : ∀ p ∈ P_low, p.Prime ∧ Y / 2 < (p : ℝ) ∧ (p : ℝ) ≤ 3 / 4 * Y := fun p hp => by
      rw [hPlow_def] at hp
      obtain ⟨hpp, hlt, hle⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp hp
      exact ⟨hpp, hlt, by linarith only [hle]⟩
    have hP_low_card : Y / (8 * Real.log X) ≤ (P_low.card : ℝ) := by
      have hw := hwin_32 (Y / 2) (by linarith only [hU1])
      rw [← hPlow_def] at hw
      have hY_le_X : Y ≤ X := by
        have h1_le_r : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
        calc Y = (X : ℝ) ^ (1 / (r : ℝ)) := hY_def
          _ ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith only [hX16])
              (div_le_one_of_le₀ h1_le_r hr_pos.le)
          _ = X := Real.rpow_one _
      have hlog_up : Real.log (3 / 2 * (Y / 2)) ≤ Real.log X :=
        Real.log_le_log (by positivity) (by linarith only [hY_le_X, hY_pos])
      have hlog_pos : 0 < Real.log (3 / 2 * (Y / 2)) :=
        Real.log_pos (by linarith only [hY16])
      calc Y / (8 * Real.log X)
          = ((3 / 2 - 1) / 2) * (Y / 2) / Real.log X := by ring
        _ ≤ ((3 / 2 - 1) / 2) * (Y / 2) / Real.log (3 / 2 * (Y / 2)) :=
            div_le_div_of_nonneg_left (by positivity) hlog_pos hlog_up
        _ ≤ (P_low.card : ℝ) := hw
    have hr_le_Plow : r - 1 ≤ P_low.card := by
      have hY_div : (r : ℝ) ≤ Y / (8 * Real.log X) :=
        (le_div_iff₀ (by positivity)).mpr (by linarith only [h8r_log])
      have hr1 : ((r - 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast Nat.sub_le r 1
      exact_mod_cast (hr1.trans (hY_div.trans hP_low_card))
    have hZH : ((⌊(2 : ℝ) ^ r * Y⌋₊ : ℕ) : ℝ) ^ k * (C * (X : ℝ) ^ θ) ≤ X := by
      have hZ_le : ((⌊(2 : ℝ) ^ r * Y⌋₊ : ℕ) : ℝ) ≤ (2 : ℝ) ^ (r + 1) * Y := by
        calc ((⌊(2 : ℝ) ^ r * Y⌋₊ : ℕ) : ℝ) ≤ 1 * ((2 : ℝ) ^ r * Y) := by
              rw [one_mul]; exact Nat.floor_le (by positivity)
          _ ≤ 2 * ((2 : ℝ) ^ r * Y) := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
          _ = (2 : ℝ) ^ (r + 1) * Y := by rw [pow_succ]; ring
      have hZk : ((⌊(2 : ℝ) ^ r * Y⌋₊ : ℕ) : ℝ) ^ k ≤
          ((2 : ℝ) ^ (r + 1)) ^ k * (X : ℝ) ^ ((k : ℝ) / r) := by
        calc ((⌊(2 : ℝ) ^ r * Y⌋₊ : ℕ) : ℝ) ^ k ≤ ((2 : ℝ) ^ (r + 1) * Y) ^ k :=
              pow_le_pow_left₀ (Nat.cast_nonneg _) hZ_le k
          _ = ((2 : ℝ) ^ (r + 1)) ^ k * Y ^ k := mul_pow _ _ _
          _ = ((2 : ℝ) ^ (r + 1)) ^ k * (X : ℝ) ^ ((k : ℝ) / r) := by
              congr 1
              rw [hY_def, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le, one_div_mul_eq_div]
      have hXθ : (X : ℝ) ^ θ ≤ (X : ℝ) ^ (max θ 0) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith only [hX16]) (le_max_left θ 0)
      calc ((⌊(2 : ℝ) ^ r * Y⌋₊ : ℕ) : ℝ) ^ k * (C * (X : ℝ) ^ θ)
          ≤ (((2 : ℝ) ^ (r + 1)) ^ k * (X : ℝ) ^ ((k : ℝ) / r)) * (C * (X : ℝ) ^ (max θ 0)) :=
            mul_le_mul hZk (mul_le_mul_of_nonneg_left hXθ hC.le) (by positivity) (by positivity)
        _ = (((2 : ℝ) ^ (r + 1)) ^ k * C) * (X : ℝ) ^ ((k : ℝ) / r + max θ 0) := by
            rw [Real.rpow_add hX0]; ring
        _ ≤ (X : ℝ) ^ δ_gap * (X : ℝ) ^ ((k : ℝ) / r + max θ 0) :=
            mul_le_mul_of_nonneg_right hδ_bound (by positivity)
        _ = X := by
            rw [← Real.rpow_add hX0, hδ_def,
              show 1 - ((k : ℝ) / r + max θ 0) + ((k : ℝ) / r + max θ 0) = 1 by ring,
              Real.rpow_one]
    have hiso_sum := powerLocal_family_isolated_card hr2 hY_pos hYr_split hPlow_sub hZH
    have hinner_ge : ∀ T ∈ P_low.powersetCard (r - 1),
        ((1 / 2 : ℝ) ^ (r + 1)) * Y / Real.log X ≤
          ((windowPrimes ((X : ℝ) / (∏ p ∈ T, p)) (2 * ((X : ℝ) / (∏ p ∈ T, p)))).card : ℝ) := by
      intro T hT
      obtain ⟨hTP, hTcard⟩ := mem_powersetCard.mp hT
      obtain ⟨d, hd_def⟩ : ∃ d : ℕ, d = ∏ p ∈ T, p := ⟨_, rfl⟩
      have hd_pos : 0 < d := by
        rw [hd_def]; exact (prod_primes_props fun p hp => (hPlow_sub p (hTP hp)).1).2.2
      have hd_r : (0 : ℝ) < d := by exact_mod_cast hd_pos
      have hd_low : (Y / 2) ^ (r - 1) ≤ (d : ℝ) := by
        rw [hd_def, Nat.cast_prod, ← hTcard]
        calc (Y / 2) ^ T.card = ∏ _p ∈ T, (Y / 2) := (prod_const _).symm
          _ ≤ ∏ p ∈ T, (p : ℝ) := prod_le_prod (fun _ _ => by positivity)
              (fun p hp => (hPlow_sub p (hTP hp)).2.1.le)
      have hd_up : (d : ℝ) ≤ (3 / 4) * Y ^ (r - 1) := by
        have h1 : (d : ℝ) ≤ (3 / 4 * Y) ^ (r - 1) := by
          rw [hd_def, Nat.cast_prod, ← hTcard]
          calc ∏ p ∈ T, (p : ℝ) ≤ ∏ _p ∈ T, (3 / 4 * Y) :=
                prod_le_prod (fun p _ => Nat.cast_nonneg p) (fun p hp => (hPlow_sub p (hTP hp)).2.2)
            _ = (3 / 4 * Y) ^ T.card := prod_const _
        have h34_pow : (3 / 4 : ℝ) ^ (r - 1) ≤ 3 / 4 := by
          obtain ⟨s, hs⟩ : ∃ s, r - 1 = s + 1 := ⟨r - 2, by omega⟩
          rw [hs, pow_succ']
          have hpow_le : (3 / 4 : ℝ) ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
          linarith only [hpow_le]
        calc (d : ℝ) ≤ (3 / 4 : ℝ) ^ (r - 1) * Y ^ (r - 1) := by rwa [mul_pow] at h1
          _ ≤ (3 / 4) * Y ^ (r - 1) := mul_le_mul_of_nonneg_right h34_pow (by positivity)
      rw [← hd_def]
      have hXd_ge : (4 / 3) * Y ≤ (X : ℝ) / d := by
        rw [le_div_iff₀ hd_r]
        calc (4 / 3) * Y * (d : ℝ) ≤ (4 / 3) * Y * ((3 / 4) * Y ^ (r - 1)) :=
              mul_le_mul_of_nonneg_left hd_up (by positivity)
          _ = X := by rw [← hYr_split]; ring
      have hw2 := hwin_2 ((X : ℝ) / d) (by linarith only [hU2, hXd_ge, hY_pos])
      have hd2 : (2 : ℝ) ≤ d := by
        have hpow1 : (2 : ℝ) ^ (1 : ℕ) ≤ (2 : ℝ) ^ (r - 1) :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hpow2 : (2 : ℝ) ^ (r - 1) ≤ (Y / 2) ^ (r - 1) :=
          pow_le_pow_left₀ (by norm_num) (by linarith only [hY16]) _
        linarith only [hpow1, hpow2, hd_low]
      have hlog_le : Real.log (2 * ((X : ℝ) / d)) ≤ Real.log X := by
        apply Real.log_le_log (by positivity)
        rw [mul_div_assoc', div_le_iff₀ hd_r, mul_comm]
        exact mul_le_mul_of_nonneg_left hd2 hX0.le
      have hlog_pos : 0 < Real.log (2 * ((X : ℝ) / d)) :=
        Real.log_pos (by linarith only [hXd_ge, hY16])
      have hhalf_r : ((1 / 2 : ℝ) ^ (r + 1)) ≤ (2 - 1) / 2 * (4 / 3) := by
        have hle12 : ((1 / 2 : ℝ) ^ (r + 1)) ≤ (1 / 2 : ℝ) ^ (1 : ℕ) :=
          pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
        linarith only [hle12]
      have hnum_r : ((1 / 2 : ℝ) ^ (r + 1)) * Y ≤ (2 - 1) / 2 * ((4 / 3) * Y) := by
        calc ((1 / 2 : ℝ) ^ (r + 1)) * Y ≤ ((2 - 1) / 2 * (4 / 3)) * Y :=
              mul_le_mul_of_nonneg_right hhalf_r hY_pos.le
          _ = (2 - 1) / 2 * ((4 / 3) * Y) := by ring
      calc ((1 / 2 : ℝ) ^ (r + 1)) * Y / Real.log X
          ≤ ((2 - 1) / 2 * ((4 / 3) * Y)) / Real.log X :=
            div_le_div_of_nonneg_right hnum_r hL0.le
        _ ≤ ((2 - 1) / 2 * ((X : ℝ) / d)) / Real.log X := by gcongr
        _ ≤ ((2 - 1) / 2) * ((X : ℝ) / d) / Real.log (2 * ((X : ℝ) / d)) :=
            div_le_div_of_nonneg_left (by positivity) hlog_pos hlog_le
        _ ≤ _ := hw2
    have hchoose_ge : (1 / (8 * (r : ℝ))) ^ (r - 1) * Y ^ (r - 1) / Real.log X ^ (r - 1) ≤
        ((P_low.powersetCard (r - 1)).card : ℝ) := by
      rw [card_powersetCard]
      have hpow_ch_r : (P_low.card : ℝ) ^ (r - 1) ≤
          ((r - 1 : ℕ) : ℝ) ^ (r - 1) * (P_low.card.choose (r - 1) : ℝ) := by
        exact_mod_cast pow_le_pow_mul_choose (r - 1) P_low.card hr_le_Plow
      have hr1_le : ((r - 1 : ℕ) : ℝ) ^ (r - 1) ≤ (r : ℝ) ^ (r - 1) :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le r 1) _
      have hr_pow_pos : (0 : ℝ) < (r : ℝ) ^ (r - 1) := by positivity
      calc (1 / (8 * (r : ℝ))) ^ (r - 1) * Y ^ (r - 1) / Real.log X ^ (r - 1)
          = (Y / (8 * Real.log X)) ^ (r - 1) / (r : ℝ) ^ (r - 1) := by
            rw [div_pow, div_pow, mul_pow, mul_pow, one_pow]; field_simp
        _ ≤ (P_low.card : ℝ) ^ (r - 1) / (r : ℝ) ^ (r - 1) := by gcongr
        _ ≤ (((r - 1 : ℕ) : ℝ) ^ (r - 1) * (P_low.card.choose (r - 1) : ℝ)) / (r : ℝ) ^ (r - 1) :=
            div_le_div_of_nonneg_right hpow_ch_r hr_pow_pos.le
        _ ≤ ((r : ℝ) ^ (r - 1) * (P_low.card.choose (r - 1) : ℝ)) / (r : ℝ) ^ (r - 1) :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right hr1_le (Nat.cast_nonneg _)) hr_pow_pos.le
        _ = (P_low.card.choose (r - 1) : ℝ) := mul_div_cancel_left₀ _ hr_pow_pos.ne'
    have hsum_ge : c_r * (X : ℝ) / Real.log X ^ r ≤
        ((∑ T ∈ P_low.powersetCard (r - 1),
          (windowPrimes ((X : ℝ) / (∏ p ∈ T, p))
            (2 * ((X : ℝ) / (∏ p ∈ T, p)))).card : ℕ) : ℝ) := by
      rw [Nat.cast_sum]
      have hL_pow : Real.log X ^ r = Real.log X ^ (r - 1) * Real.log X := by
        have hr_eq : r = (r - 1) + 1 := by omega
        conv_lhs => rw [hr_eq, pow_succ]
      calc c_r * (X : ℝ) / Real.log X ^ r
          = ((1 / (8 * (r : ℝ))) ^ (r - 1) * Y ^ (r - 1) / Real.log X ^ (r - 1)) *
              (((1 / 2 : ℝ) ^ (r + 1)) * Y / Real.log X) := by
            have hX_num : c_r * (X : ℝ) = c_r * (Y * Y ^ (r - 1)) := by rw [← hYr_split]
            rw [hX_num, hc_def, hL_pow]
            simp only [div_eq_mul_inv, mul_inv]; ring
        _ ≤ ((P_low.powersetCard (r - 1)).card : ℝ) *
              (((1 / 2 : ℝ) ^ (r + 1)) * Y / Real.log X) :=
            mul_le_mul_of_nonneg_right hchoose_ge (by positivity)
        _ = ∑ _T ∈ P_low.powersetCard (r - 1),
              (((1 / 2 : ℝ) ^ (r + 1)) * Y / Real.log X) := by
            rw [sum_const, nsmul_eq_mul]
        _ ≤ _ := sum_le_sum hinner_ge
    exact hsum_ge.trans (by exact_mod_cast hiso_sum)
  refine ⟨c_r, hc_pos, max 1 ⌈X_base⌉₊, fun X hX => ⟨hmain_bound X hX, fun {β} hβ => ?_⟩⟩
  obtain ⟨X₁, hX₁⟩ := eventually_rpow_lt_of_div_log_pow hc_pos hmain_bound hβ
  exact ⟨X₁, fun Y hY M => (hX₁ Y hY).trans_le (by exact_mod_cast card_isolatedVertices_le_unmatched M)⟩

/-! ### 5. Log-power cell bounded-arity obstruction (`H ≤ C X / (log X)^B`, `B > k`) -/

/-- Geometric interval cover: if `u < val ≤ ρ ^ M * u` (`0 < u`, `1 < ρ`), some `j < M` satisfies
`ρ ^ j * u < val ≤ ρ ^ (j + 1) * u`. -/
private lemma geom_bin_index {u ρ val : ℝ} (_hu : 0 < u) (_hρ : 1 < ρ) :
    ∀ (M : ℕ), u < val → val ≤ ρ ^ M * u → ∃ j < M, ρ ^ j * u < val ∧ val ≤ ρ ^ (j + 1) * u
  | 0, h1, h2 => by simp at h2; linarith only [h1, h2]
  | m + 1, h1, h2 => by
    rcases le_or_gt val (ρ ^ m * u) with hle | hgt
    · obtain ⟨j, hjm, hj1, hj2⟩ := geom_bin_index _hu _hρ m h1 hle
      exact ⟨j, by omega, hj1, hj2⟩
    · exact ⟨m, by omega, hgt, h2⟩

/-- Pigeonhole selection of a ratio-`9/8` geometric product bin among `r₁`-subsets of `P₁ ⊆ (z/2, z]`. -/
private lemma exists_winning_geometric_bin {P₁ : Finset ℕ} {z : ℝ} {r₁ : ℕ}
    (hz : 2 ≤ z) (hr₁_pos : 0 < r₁) (hr₁_le : r₁ ≤ P₁.card)
    (hP₁ : ∀ p ∈ P₁, p.Prime ∧ z / 2 < (p : ℝ) ∧ (p : ℝ) ≤ z) :
    ∃ (B₀ : Finset (Finset ℕ)) (U : ℝ),
      B₀ ⊆ P₁.powersetCard r₁ ∧
      1 ≤ U ∧ U ≤ z ^ r₁ ∧
      (P₁.powersetCard r₁).card ≤ 6 * r₁ * B₀.card ∧
      ∀ T ∈ B₀, U < (∏ p ∈ T, (p : ℝ)) ∧ (∏ p ∈ T, (p : ℝ)) ≤ (9 / 8) * U := by
  classical
  have hz_pos : 0 < z := by linarith only [hz]
  obtain ⟨bucket, hbuck_def⟩ : ∃ bucket : ℕ → Finset (Finset ℕ), ∀ j,
    bucket j = (P₁.powersetCard r₁).filter fun (T : Finset ℕ) =>
      (9 / 8 : ℝ) ^ j * (z / 2) ^ r₁ < (∏ p ∈ T, (p : ℝ)) ∧
        (∏ p ∈ T, (p : ℝ)) ≤ (9 / 8 : ℝ) ^ (j + 1) * (z / 2) ^ r₁ :=
    ⟨fun j => (P₁.powersetCard r₁).filter fun (T : Finset ℕ) =>
      (9 / 8 : ℝ) ^ j * (z / 2) ^ r₁ < (∏ p ∈ T, (p : ℝ)) ∧
        (∏ p ∈ T, (p : ℝ)) ≤ (9 / 8 : ℝ) ^ (j + 1) * (z / 2) ^ r₁, fun _ => rfl⟩
  have hcover_bins : P₁.powersetCard r₁ ⊆ (Finset.range (6 * r₁)).biUnion bucket := by
    intro T hT
    obtain ⟨hTP, hTcard⟩ := mem_powersetCard.mp hT
    have hlow_T : (z / 2) ^ r₁ < ∏ p ∈ T, (p : ℝ) := by
      rw [← hTcard]
      have hT_ne : T.Nonempty := card_pos.mp (by omega)
      calc (z / 2) ^ T.card = ∏ _p ∈ T, (z / 2) := (prod_const _).symm
        _ < ∏ p ∈ T, (p : ℝ) := prod_lt_prod_of_nonempty (fun _ _ => by positivity)
            (fun p hp => (hP₁ p (hTP hp)).2.1) hT_ne
    have hup_T : ∏ p ∈ T, (p : ℝ) ≤ (9 / 8 : ℝ) ^ (6 * r₁) * (z / 2) ^ r₁ := by
      have h1 : ∏ p ∈ T, (p : ℝ) ≤ z ^ r₁ := by
        rw [← hTcard]
        calc ∏ p ∈ T, (p : ℝ) ≤ ∏ _p ∈ T, z := prod_le_prod (fun p _ => Nat.cast_nonneg p)
              (fun p hp => (hP₁ p (hTP hp)).2.2)
          _ = z ^ T.card := prod_const _
      have h98_6 : (2 : ℝ) ≤ (9 / 8 : ℝ) ^ (6 : ℕ) := by norm_num
      have h98_pow : (2 : ℝ) ^ r₁ ≤ (9 / 8 : ℝ) ^ (6 * r₁) := by
        rw [pow_mul]; exact pow_le_pow_left₀ (by norm_num) h98_6 r₁
      calc ∏ p ∈ T, (p : ℝ) ≤ z ^ r₁ := h1
        _ = (2 : ℝ) ^ r₁ * (z / 2) ^ r₁ := by rw [← mul_pow]; ring_nf
        _ ≤ (9 / 8 : ℝ) ^ (6 * r₁) * (z / 2) ^ r₁ :=
            mul_le_mul_of_nonneg_right h98_pow (by positivity)
    obtain ⟨j, hj, hj1, hj2⟩ := geom_bin_index (by positivity) (by norm_num) (6 * r₁) hlow_T hup_T
    exact mem_biUnion.mpr ⟨j, mem_range.mpr hj, (hbuck_def j).symm ▸ mem_filter.mpr ⟨hT, hj1, hj2⟩⟩
  have hsum_bins : (P₁.powersetCard r₁).card ≤ ∑ j ∈ Finset.range (6 * r₁), (bucket j).card :=
    (card_le_card hcover_bins).trans card_biUnion_le
  obtain ⟨j₀, _, hj₀_max⟩ :=
    Finset.exists_max_image (Finset.range (6 * r₁)) (fun j => (bucket j).card)
      (nonempty_range_iff.mpr (by omega))
  have hj₀_ge : (P₁.powersetCard r₁).card ≤ 6 * r₁ * (bucket j₀).card := by
    calc (P₁.powersetCard r₁).card
        ≤ ∑ j ∈ Finset.range (6 * r₁), (bucket j).card := hsum_bins
      _ ≤ (Finset.range (6 * r₁)).card • (bucket j₀).card := sum_le_card_nsmul _ _ _ hj₀_max
      _ = 6 * r₁ * (bucket j₀).card := by rw [card_range, smul_eq_mul]
  have hpow_card_pos : 0 < (P₁.powersetCard r₁).card := by
    rw [card_powersetCard]; exact Nat.choose_pos hr₁_le
  have hbuck_ne : (bucket j₀).Nonempty := card_pos.mp
    (Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hj₀_ge; omega)
  obtain ⟨U, hU_def⟩ : ∃ U : ℝ, U = (9 / 8 : ℝ) ^ j₀ * (z / 2) ^ r₁ := ⟨_, rfl⟩
  have hU_ge1 : 1 ≤ U := by
    rw [hU_def]
    have h1 : (1 : ℝ) ≤ (9 / 8 : ℝ) ^ j₀ := one_le_pow₀ (by norm_num)
    have h2 : (1 : ℝ) ≤ (z / 2) ^ r₁ := one_le_pow₀ (by linarith only [hz])
    nlinarith [h1, h2]
  have hU_le_zr1 : U ≤ z ^ r₁ := by
    obtain ⟨T_rep, hT_rep⟩ := hbuck_ne
    rw [hbuck_def j₀] at hT_rep
    obtain ⟨hT_mem, hU_lt, _⟩ := mem_filter.mp hT_rep
    obtain ⟨hTP, hTcard⟩ := mem_powersetCard.mp hT_mem
    have hrep_le : ∏ p ∈ T_rep, (p : ℝ) ≤ z ^ r₁ := by
      rw [← hTcard]
      calc ∏ p ∈ T_rep, (p : ℝ) ≤ ∏ _p ∈ T_rep, z := prod_le_prod (fun p _ => Nat.cast_nonneg p)
            (fun p hp => (hP₁ p (hTP hp)).2.2)
        _ = z ^ T_rep.card := prod_const _
    rw [hU_def]; exact hU_lt.le.trans hrep_le
  refine ⟨bucket j₀, U, (hbuck_def j₀).symm ▸ filter_subset _ _, hU_ge1, hU_le_zr1, hj₀_ge, ?_⟩
  intro T hT
  rw [hbuck_def j₀] at hT
  obtain ⟨_, h1, h2⟩ := mem_filter.mp hT
  refine ⟨hU_def ▸ h1, ?_⟩
  rw [hU_def]; rw [pow_succ'] at h2; linarith only [h2]

/-- Two-band friable cofactor construction producing a squarefree `Q_star ∈ (W, (14/9) W]` with all
prime factors `≤ z / 3`. -/
private lemma exists_two_band_cofactor {L_root : ℕ} {y z W κ : ℝ}
    (hLr_ge2 : 2 ≤ L_root) (hy_ge8 : 8 ≤ y) (hyz : y ≤ z / 3)
    (hκ_gt1 : 1 < κ) (hκ_pow : κ ^ L_root = 14 / 9)
    (h2y_W : (2 * y) ^ L_root ≤ W)
    (hW_pow : W / (2 * y) ^ L_root < (y / 2) ^ (windowPrimes (y / 2) y).card)
    (hκ_z3 : κ * (2 * y) ^ (((L_root + 1 : ℕ) : ℝ) / L_root) ≤ z / 3)
    (hcard_w : ∀ w : ℝ, 2 * y ≤ w → κ * w ≤ z / 3 → L_root ≤ (windowPrimes w (κ * w)).card) :
    ∃ Q_star : ℕ,
      0 < Q_star ∧ Squarefree Q_star ∧
      (∀ p ∈ Q_star.primeFactors, (p : ℝ) ≤ z / 3) ∧
      W < (Q_star : ℝ) ∧ (Q_star : ℝ) ≤ (14 / 9) * W := by
  have hy_pos : 0 < y := by linarith only [hy_ge8]
  have hL_root_pos : (0 : ℝ) < L_root := by exact_mod_cast (show 0 < L_root by omega)
  obtain ⟨P_aux, hPaux_def⟩ : ∃ P_aux : Finset ℕ, P_aux = windowPrimes (y / 2) y := ⟨_, rfl⟩
  rw [← hPaux_def] at hW_pow
  obtain ⟨W₀, hW₀_def⟩ : ∃ W₀ : ℝ, W₀ = W / (2 * y) ^ L_root := ⟨_, rfl⟩
  have hW₀_ge1 : 1 ≤ W₀ := by rw [hW₀_def]; exact (one_le_div (by positivity)).mpr h2y_W
  rw [← hW₀_def] at hW_pow
  have hP_aux_in : ∀ q ∈ P_aux, y / 2 ≤ (q : ℝ) ∧ (q : ℝ) ≤ y := fun q hq => by
    obtain ⟨_, h1, h2⟩ := (mem_windowPrimes (by positivity) (by positivity)).mp (hPaux_def ▸ hq)
    exact ⟨h1.le, h2⟩
  obtain ⟨S_init, hS_sub_aux, hS_le_W₀, hW₀_lt_yS⟩ :=
    exists_subset_prod_le_and_lt_mul (by linarith only [hy_ge8] : 1 < y / 2)
      hP_aux_in hW₀_ge1 hW_pow
  have hS_primes : ∀ q ∈ S_init, q.Prime ∧ y / 2 < (q : ℝ) ∧ (q : ℝ) ≤ y := fun q hq =>
    (mem_windowPrimes (by positivity) (by positivity)).mp (hPaux_def ▸ hS_sub_aux hq)
  obtain ⟨hsq_Qinit, hpf_Qinit, hQinit_pos⟩ := prod_primes_props (fun q hq => (hS_primes q hq).1)
  obtain ⟨Q_init, hQi_def⟩ : ∃ Q_init : ℕ, Q_init = ∏ q ∈ S_init, q := ⟨_, rfl⟩
  rw [← hQi_def] at hsq_Qinit hpf_Qinit hQinit_pos
  have hQinit_r_pos : (0 : ℝ) < Q_init := by exact_mod_cast hQinit_pos
  have hQinit_cast : (Q_init : ℝ) = ∏ q ∈ S_init, (q : ℝ) := by rw [hQi_def, Nat.cast_prod]
  obtain ⟨V, hV_def⟩ : ∃ V : ℝ, V = W / Q_init := ⟨_, rfl⟩
  have hV_low : (2 * y) ^ L_root ≤ V := by
    rw [hV_def, le_div_iff₀ hQinit_r_pos]
    rw [← hQinit_cast, hW₀_def, le_div_iff₀ (by positivity)] at hS_le_W₀
    linarith only [hS_le_W₀]
  have hV_up : V < (2 * y) ^ (L_root + 1) := by
    rw [hV_def, div_lt_iff₀ hQinit_r_pos]
    rw [← hQinit_cast, hW₀_def, div_lt_iff₀ (by positivity)] at hW₀_lt_yS
    calc W < y * (Q_init : ℝ) * (2 * y) ^ L_root := hW₀_lt_yS
      _ ≤ (2 * y) * (2 * y) ^ L_root * (Q_init : ℝ) := by
          nlinarith [show 0 < (2 * y) ^ L_root * Q_init by positivity, hy_pos]
      _ = (2 * y) ^ (L_root + 1) * (Q_init : ℝ) := by rw [pow_succ']
  have hV_pos : 0 < V := lt_of_lt_of_le (by positivity) hV_low
  obtain ⟨w, hw_def⟩ : ∃ w : ℝ, w = V ^ (1 / (L_root : ℝ)) := ⟨_, rfl⟩
  have hw_pos : 0 < w := by rw [hw_def]; positivity
  have hw_pow : w ^ L_root = V := by
    rw [hw_def, ← Real.rpow_natCast, ← Real.rpow_mul hV_pos.le,
      one_div_mul_cancel hL_root_pos.ne', Real.rpow_one]
  have hw_ge_2y : 2 * y ≤ w := by
    have hpow_le : (2 * y) ^ L_root ≤ w ^ L_root := by rw [hw_pow]; exact hV_low
    exact (pow_le_pow_iff_left₀ (by positivity) hw_pos.le (by omega)).mp hpow_le
  have hκw_le_z3 : κ * w ≤ z / 3 := by
    have hw_le : w ≤ (2 * y) ^ (((L_root + 1 : ℕ) : ℝ) / L_root) := by
      rw [hw_def]
      calc V ^ (1 / (L_root : ℝ))
          ≤ ((2 * y) ^ (L_root + 1)) ^ (1 / (L_root : ℝ)) :=
            Real.rpow_le_rpow hV_pos.le hV_up.le (by positivity)
        _ = (2 * y) ^ (((L_root + 1 : ℕ) : ℝ) / L_root) := by
            rw [← Real.rpow_natCast (2 * y), ← Real.rpow_mul (by positivity)]
            congr 1; ring
    exact (mul_le_mul_of_nonneg_left hw_le (by linarith only [hκ_gt1])).trans hκ_z3
  have hLroot_le_card : L_root ≤ (windowPrimes w (κ * w)).card := hcard_w w hw_ge_2y hκw_le_z3
  have hTw_ne : ((windowPrimes w (κ * w)).powersetCard L_root).Nonempty := by
    rw [← card_pos, card_powersetCard]; exact Nat.choose_pos hLroot_le_card
  obtain ⟨T_w, hTw_mem⟩ := hTw_ne
  obtain ⟨hTw_sub, hTw_card⟩ := mem_powersetCard.mp hTw_mem
  have hTw_primes : ∀ p ∈ T_w, p.Prime ∧ w < (p : ℝ) ∧ (p : ℝ) ≤ κ * w := fun p hp =>
    (mem_windowPrimes (by positivity) (by positivity)).mp (hTw_sub hp)
  obtain ⟨hsq_Tw, hpf_Tw, hTw_pos⟩ := prod_primes_props (fun p hp => (hTw_primes p hp).1)
  obtain ⟨Q_w, hQw_def⟩ : ∃ Q_w : ℕ, Q_w = ∏ p ∈ T_w, p := ⟨_, rfl⟩
  rw [← hQw_def] at hsq_Tw hpf_Tw hTw_pos
  have hQw_low : V < (Q_w : ℝ) := by
    rw [← hw_pow, ← hTw_card]
    have hne_Tw : T_w.Nonempty := card_pos.mp (by omega)
    calc w ^ T_w.card = ∏ _p ∈ T_w, w := (prod_const _).symm
      _ < ∏ p ∈ T_w, (p : ℝ) := prod_lt_prod_of_nonempty (fun _ _ => hw_pos)
          (fun p hp => (hTw_primes p hp).2.1) hne_Tw
      _ = (Q_w : ℝ) := by rw [hQw_def, Nat.cast_prod]
  have hQw_up : (Q_w : ℝ) ≤ (14 / 9) * V := by
    calc (Q_w : ℝ) = ∏ p ∈ T_w, (p : ℝ) := by rw [hQw_def, Nat.cast_prod]
      _ ≤ ∏ _p ∈ T_w, (κ * w) := prod_le_prod (fun p _ => Nat.cast_nonneg p)
          (fun p hp => (hTw_primes p hp).2.2)
      _ = (κ * w) ^ L_root := by rw [prod_const, hTw_card]
      _ = (14 / 9) * V := by rw [mul_pow, hκ_pow, hw_pow]
  obtain ⟨Q_star, hQs_def⟩ : ∃ Q_star : ℕ, Q_star = Q_init * Q_w := ⟨_, rfl⟩
  have hQstar_pos : 0 < Q_star := by rw [hQs_def]; exact Nat.mul_pos hQinit_pos hTw_pos
  have hcop_init_w : Nat.Coprime Q_init Q_w := by
    rw [hQi_def, hQw_def]
    exact Nat.Coprime.prod_left fun q hq => Nat.Coprime.prod_right fun p hp =>
      (Nat.coprime_primes (hS_primes q hq).1 (hTw_primes p hp).1).mpr fun heq => by
        have h1 := (hS_primes q hq).2.2
        have h2 := (hTw_primes p hp).2.1
        have hqp_eq : (q : ℝ) = p := by exact_mod_cast heq
        linarith only [h1, h2, hw_ge_2y, hy_pos, hqp_eq]
  have hsq_Qstar : Squarefree Q_star := by
    rw [hQs_def]; exact Nat.squarefree_mul_iff.mpr ⟨hcop_init_w, hsq_Qinit, hsq_Tw⟩
  have hQstar_pf_le : ∀ p ∈ Q_star.primeFactors, (p : ℝ) ≤ z / 3 := by
    intro p hp
    rw [hQs_def, Nat.primeFactors_mul hQinit_pos.ne' hTw_pos.ne', hpf_Qinit, hpf_Tw] at hp
    rcases mem_union.mp hp with hpS | hpTw
    · exact ((hS_primes p hpS).2.2).trans hyz
    · exact ((hTw_primes p hpTw).2.2).trans hκw_le_z3
  have hQstar_low : W < (Q_star : ℝ) := by
    calc W = (Q_init : ℝ) * V := by rw [hV_def, mul_div_cancel₀ _ hQinit_r_pos.ne']
      _ < (Q_init : ℝ) * Q_w := mul_lt_mul_of_pos_left hQw_low hQinit_r_pos
      _ = (Q_star : ℝ) := by rw [hQs_def, Nat.cast_mul]
  have hQstar_up : (Q_star : ℝ) ≤ (14 / 9) * W := by
    calc (Q_star : ℝ) = (Q_init : ℝ) * Q_w := by rw [hQs_def, Nat.cast_mul]
      _ ≤ (Q_init : ℝ) * ((14 / 9) * V) := mul_le_mul_of_nonneg_left hQw_up hQinit_r_pos.le
      _ = (14 / 9) * ((Q_init : ℝ) * V) := by ring
      _ = (14 / 9) * W := by rw [hV_def, mul_div_cancel₀ _ hQinit_r_pos.ne']
  exact ⟨Q_star, hQstar_pos, hsq_Qstar, hQstar_pf_le, hQstar_low, hQstar_up⟩

/-- Injection of `B₀ ⊆ P₁^(r₁)` multiplied by `Q_star` into `isolatedVertices`. -/
private lemma bin_cofactor_card_le_isolatedVertices {k X r₁ Q_star : ℕ} {H z U W : ℝ}
    {P₁ : Finset ℕ} {B₀ : Finset (Finset ℕ)}
    (hz_pos : 0 < z) (hU_pos : 0 < U) (hW_pos : 0 < W) (hUW : U * W = (X : ℝ))
    (hP₁ : ∀ p ∈ P₁, p.Prime ∧ z / 2 < (p : ℝ) ∧ (p : ℝ) ≤ z)
    (hB₀_sub : B₀ ⊆ P₁.powersetCard r₁)
    (hB₀_win : ∀ T ∈ B₀, U < (∏ p ∈ T, (p : ℝ)) ∧ (∏ p ∈ T, (p : ℝ)) ≤ (9 / 8) * U)
    (hQstar_pos : 0 < Q_star) (hsq_Qstar : Squarefree Q_star)
    (hQstar_pf_le : ∀ p ∈ Q_star.primeFactors, (p : ℝ) ≤ z / 3)
    (hQstar_low : W < (Q_star : ℝ)) (hQstar_up : (Q_star : ℝ) ≤ (14 / 9) * W)
    (hZH_cell : ((⌊z⌋₊ : ℕ) : ℝ) ^ k * H ≤ X) :
    B₀.card ≤ (isolatedVertices (BoundedArityLocalExchange k H) (Ioc X (2 * X))).card := by
  classical
  have hX_pos : (0 : ℝ) < X := by rw [← hUW]; positivity
  obtain ⟨Z, hZ_def⟩ : ∃ Z : ℕ, Z = ⌊z⌋₊ := ⟨_, rfl⟩
  rw [← hZ_def] at hZH_cell
  obtain ⟨F_cell, hFc_def⟩ : ∃ F_cell : Finset ℕ,
    F_cell = B₀.image fun T => (∏ p ∈ T, p) * Q_star := ⟨_, rfl⟩
  have hF_cell_inj : Set.InjOn (fun T : Finset ℕ => (∏ p ∈ T, p) * Q_star) ↑B₀ := by
    intro T₁ hT₁ T₂ hT₂ heq
    have hprod_eq : ∏ p ∈ T₁, p = ∏ p ∈ T₂, p := Nat.eq_of_mul_eq_mul_right hQstar_pos heq
    have hpf1 : (∏ p ∈ T₁, p).primeFactors = T₁ :=
      (prod_primes_props fun p hp => (hP₁ p ((mem_powersetCard.mp (hB₀_sub hT₁)).1 hp)).1).2.1
    have hpf2 : (∏ p ∈ T₂, p).primeFactors = T₂ :=
      (prod_primes_props fun p hp => (hP₁ p ((mem_powersetCard.mp (hB₀_sub hT₂)).1 hp)).1).2.1
    rw [← hpf1, ← hpf2, hprod_eq]
  have hF_cell_sub : F_cell ⊆ isolatedVertices (BoundedArityLocalExchange k H) (Ioc X (2 * X)) := by
    intro n hn
    rw [hFc_def] at hn
    obtain ⟨T, hT_buck, rfl⟩ := mem_image.mp hn
    obtain ⟨hT_low_U, hT_up_U⟩ := hB₀_win T hT_buck
    obtain ⟨hTP, _⟩ := mem_powersetCard.mp (hB₀_sub hT_buck)
    have hT_pr : ∀ p ∈ T, p.Prime ∧ z / 2 < (p : ℝ) ∧ (p : ℝ) ≤ z :=
      fun p hp => hP₁ p (hTP hp)
    obtain ⟨hsq_d, hpf_d, hd_pos⟩ := prod_primes_props (fun p hp => (hT_pr p hp).1)
    obtain ⟨d, hd_def⟩ : ∃ d : ℕ, d = ∏ p ∈ T, p := ⟨_, rfl⟩
    rw [← hd_def] at hsq_d hpf_d hd_pos ⊢
    have hd_cast : (d : ℝ) = ∏ p ∈ T, (p : ℝ) := by rw [hd_def, Nat.cast_prod]
    have hcop_dQ : Nat.Coprime d Q_star := by
      rw [hd_def]
      exact Nat.Coprime.prod_left fun p hp =>
        (hT_pr p hp).1.coprime_iff_not_dvd.mpr fun hdvd => by
          have hpQ : p ∈ Q_star.primeFactors :=
            Nat.mem_primeFactors.mpr ⟨(hT_pr p hp).1, hdvd, hQstar_pos.ne'⟩
          have h1 := hQstar_pf_le p hpQ
          have h2 := (hT_pr p hp).2.1
          linarith only [h1, h2, hz_pos]
    have hsq_n : Squarefree (d * Q_star) :=
      Nat.squarefree_mul_iff.mpr ⟨hcop_dQ, hsq_d, hsq_Qstar⟩
    have hn_gt_X : (X : ℝ) < (d * Q_star : ℕ) := by
      push_cast; rw [hd_cast, ← hUW]
      exact mul_lt_mul'' hT_low_U hQstar_low hU_pos.le hW_pos.le
    have hn_le_2X : ((d * Q_star : ℕ) : ℝ) ≤ 2 * X := by
      push_cast; rw [hd_cast]
      calc (∏ p ∈ T, (p : ℝ)) * Q_star
          ≤ ((9 / 8) * U) * ((14 / 9) * W) :=
            mul_le_mul hT_up_U hQstar_up (Nat.cast_nonneg _) (by positivity)
        _ = (7 / 4) * (U * W) := by ring
        _ = (7 / 4) * X := by rw [hUW]
        _ ≤ 2 * X := by linarith only [hX_pos]
    have hnIoc : d * Q_star ∈ Ioc X (2 * X) := by
      have h2X_eq : (2 : ℝ) * X = ((2 * X : ℕ) : ℝ) := by push_cast; ring
      exact mem_Ioc.mpr ⟨by exact_mod_cast hn_gt_X, by exact_mod_cast (h2X_eq ▸ hn_le_2X)⟩
    have hZ_all : ∀ p ∈ (d * Q_star).primeFactors, p ≤ Z := by
      intro p hp
      rw [hZ_def]
      rw [Nat.primeFactors_mul hd_pos.ne' hQstar_pos.ne', hpf_d] at hp
      rcases mem_union.mp hp with hpT | hpQ
      · exact Nat.le_floor (hT_pr p hpT).2.2
      · exact Nat.le_floor ((hQstar_pf_le p hpQ).trans (by linarith only [hz_pos]))
    exact mem_isolatedVertices_of_primeFactors_le (mem_filter.mpr ⟨hnIoc, hsq_n⟩) hZ_all hZH_cell
  rw [← card_image_of_injOn hF_cell_inj, ← hFc_def]
  exact card_le_card hF_cell_sub

/-- Quantitative binomial lower bound `(X : ℝ) ^ β < (B₀.card : ℝ)` from the winning bin ratio. -/
private lemma rpow_lt_bin_card_of_bounds {X r₁ m_deg B_card P_card : ℕ}
    {β β' ε₀ ε₂ γ δ_fin L z : ℝ}
    (hX16 : (16 : ℝ) ≤ X) (hL16 : 16 ≤ L) (hll2 : 2 ≤ Real.log L)
    (hL_def : L = Real.log X) (hz_def : z = L ^ γ)
    (hβ_le : β ≤ β') (hε₀_pos : 0 < ε₀) (hε₂_pos : 0 < ε₂) (hε₂_lt1 : ε₂ < 1)
    (hγ_gt1 : 1 < γ) (h1_inv_pos : 0 < 1 - 1 / γ) (h1_inv_lt1 : 1 - 1 / γ < 1)
    (hδ_fin_pos : 0 < δ_fin)
    (hexp_target : β' + δ_fin / 2 ≤ (1 - ε₀) * (1 - ε₂) * (1 - 1 / γ))
    (hm_deg_gt : γ + 1 < (m_deg : ℝ))
    (hx_δfin : (6 : ℝ) * ((m_deg.factorial : ℝ) / (δ_fin / 4) ^ m_deg) + 1 ≤ (X : ℝ) ^ (δ_fin / 4))
    (hL_ε2 : (4 : ℝ) ≤ L ^ (ε₂ * (γ - 1)))
    (hr₁_pos : 0 < r₁) (hr₁_le_P₁ : r₁ ≤ P_card)
    (hr₁_def : r₁ = ⌊(1 - ε₀) * L / Real.log z⌋₊)
    (hr₁_le_real : (r₁ : ℝ) ≤ (1 - ε₀) * L / Real.log z)
    (hPr_div_ge : L ^ (γ - 1) / 4 ≤ (P_card : ℝ) / r₁)
    (hj₀_ge : P_card.choose r₁ ≤ 6 * r₁ * B_card) :
    (X : ℝ) ^ β < (B_card : ℝ) := by
  have hX0 : (0 : ℝ) < X := by linarith only [hX16]
  have hL0 : 0 < L := by linarith only [hL16]
  have hγ_pos : 0 < γ := by linarith only [hγ_gt1]
  have hz_pos : 0 < z := by rw [hz_def]; positivity
  have hz_ge1 : 1 ≤ z := by
    rw [hz_def]; exact Real.one_le_rpow (by linarith only [hL16]) hγ_pos.le
  have hlogz_eq : Real.log z = γ * Real.log L := by rw [hz_def]; exact Real.log_rpow hL0 γ
  have hlogz_pos : 0 < Real.log z := by rw [hlogz_eq]; positivity
  have hPr_ratio : z ^ ((1 - ε₂) * (1 - 1 / γ)) ≤ (P_card : ℝ) / r₁ := by
    have hz_exp : z ^ ((1 - ε₂) * (1 - 1 / γ)) = L ^ ((1 - ε₂) * (γ - 1)) := by
      rw [hz_def, ← Real.rpow_mul hL0.le]; congr 1
      have : γ ≠ 0 := hγ_pos.ne'
      field_simp
    have habsorb : L ^ ((1 - ε₂) * (γ - 1)) ≤ L ^ (γ - 1) / 4 := by
      rw [le_div_iff₀ (by norm_num)]
      calc L ^ ((1 - ε₂) * (γ - 1)) * 4
          ≤ L ^ ((1 - ε₂) * (γ - 1)) * L ^ (ε₂ * (γ - 1)) :=
            mul_le_mul_of_nonneg_left hL_ε2 (by positivity)
        _ = L ^ (γ - 1) := by rw [← Real.rpow_add hL0]; congr 1; ring
    rw [hz_exp]; exact habsorb.trans hPr_div_ge
  have hzr1_low : (X : ℝ) ^ (1 - ε₀) / z ≤ z ^ r₁ := by
    have hlt_fl := Nat.lt_floor_add_one ((1 - ε₀) * L / Real.log z)
    rw [← hr₁_def, div_lt_iff₀ hlogz_pos] at hlt_fl
    have hexp_lt : (X : ℝ) ^ (1 - ε₀) ≤ z ^ (r₁ + 1) := by
      rw [Real.rpow_def_of_pos hX0, ← Real.rpow_natCast z, Real.rpow_def_of_pos hz_pos]
      apply Real.exp_le_exp.mpr; push_cast; rw [← hL_def]; linarith only [hlt_fl]
    rw [pow_succ] at hexp_lt
    rwa [div_le_iff₀ hz_pos]
  obtain ⟨α_exp, hα_exp_def⟩ : ∃ α_exp : ℝ, α_exp = (1 - ε₂) * (1 - 1 / γ) := ⟨_, rfl⟩
  have hα_pos : 0 < α_exp := by rw [hα_exp_def]; exact mul_pos (sub_pos.mpr hε₂_lt1) h1_inv_pos
  have hα_lt1 : α_exp < 1 := by
    rw [hα_exp_def]
    calc (1 - ε₂) * (1 - 1 / γ) ≤ 1 * (1 - 1 / γ) :=
          mul_le_mul_of_nonneg_right (by linarith only [hε₂_pos]) h1_inv_pos.le
      _ < 1 := by linarith only [h1_inv_lt1]
  have hchoose_r1 : (X : ℝ) ^ (β' + δ_fin / 2) / z ≤ (P_card.choose r₁ : ℝ) := by
    have hch_r : (P_card : ℝ) ^ r₁ ≤ (r₁ : ℝ) ^ r₁ * (P_card.choose r₁ : ℝ) := by
      exact_mod_cast pow_le_pow_mul_choose r₁ P_card hr₁_le_P₁
    have hr1_pow_pos : (0 : ℝ) < (r₁ : ℝ) ^ r₁ := by
      have : (0 : ℝ) < r₁ := by exact_mod_cast hr₁_pos
      positivity
    calc (X : ℝ) ^ (β' + δ_fin / 2) / z
        ≤ (X : ℝ) ^ ((1 - ε₀) * α_exp) / z := by
          gcongr
          · linarith only [hX16]
          · rw [hα_exp_def, ← mul_assoc]; exact hexp_target
      _ ≤ (X : ℝ) ^ ((1 - ε₀) * α_exp) / z ^ α_exp := by
          refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
          calc z ^ α_exp ≤ z ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hz_ge1 hα_lt1.le
            _ = z := Real.rpow_one z
      _ = ((X : ℝ) ^ (1 - ε₀) / z) ^ α_exp := by
          rw [Real.div_rpow (by positivity) hz_pos.le, ← Real.rpow_mul hX0.le]
      _ ≤ (z ^ r₁) ^ α_exp := Real.rpow_le_rpow (by positivity) hzr1_low hα_pos.le
      _ = (z ^ α_exp) ^ r₁ := by
          rw [← Real.rpow_natCast z, ← Real.rpow_mul hz_pos.le, mul_comm (r₁ : ℝ),
            Real.rpow_mul hz_pos.le, Real.rpow_natCast]
      _ ≤ ((P_card : ℝ) / r₁) ^ r₁ := by
          rw [hα_exp_def]; exact pow_le_pow_left₀ (by positivity) hPr_ratio r₁
      _ = (P_card : ℝ) ^ r₁ / (r₁ : ℝ) ^ r₁ := div_pow _ _ _
      _ ≤ ((r₁ : ℝ) ^ r₁ * (P_card.choose r₁ : ℝ)) / (r₁ : ℝ) ^ r₁ :=
          div_le_div_of_nonneg_right hch_r hr1_pow_pos.le
      _ = (P_card.choose r₁ : ℝ) := mul_div_cancel_left₀ _ hr1_pow_pos.ne'
  have h6r1z_lt : 6 * (r₁ : ℝ) * z < (X : ℝ) ^ (δ_fin / 2) := by
    have hr1_le_L : (r₁ : ℝ) ≤ L := by
      have hlogz_ge1 : 1 ≤ Real.log z := by
        rw [hlogz_eq]
        calc (1 : ℝ) ≤ 1 * 2 := by norm_num
          _ ≤ γ * Real.log L := mul_le_mul hγ_gt1.le hll2 (by norm_num) hγ_pos.le
      calc (r₁ : ℝ) ≤ (1 - ε₀) * L / Real.log z := hr₁_le_real
        _ ≤ (1 * L) / 1 := div_le_div₀ (mul_nonneg zero_le_one hL0.le)
            (mul_le_mul_of_nonneg_right (by linarith only [hε₀_pos]) hL0.le) zero_lt_one hlogz_ge1
        _ = L := by ring
    have hLz_le_m : L * z ≤ L ^ m_deg := by
      rw [hz_def, ← Real.rpow_one_add' hL0.le (by linarith only [hγ_pos] : 0 < 1 + γ).ne',
        ← Real.rpow_natCast L]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hL16]) (by linarith only [hm_deg_gt])
    have hexp_deg := Real.pow_div_factorial_le_exp ((δ_fin / 4) * L) (by positivity) m_deg
    rw [show Real.exp ((δ_fin / 4) * L) = (X : ℝ) ^ (δ_fin / 4) by
      rw [hL_def, Real.rpow_def_of_pos hX0, mul_comm]] at hexp_deg
    have hfac_deg_pos : (0 : ℝ) < m_deg.factorial := Nat.cast_pos.mpr (Nat.factorial_pos m_deg)
    have hLm_deg_le : L ^ m_deg ≤
        ((m_deg.factorial : ℝ) / (δ_fin / 4) ^ m_deg) * (X : ℝ) ^ (δ_fin / 4) := by
      rw [mul_pow, div_le_iff₀ hfac_deg_pos] at hexp_deg
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith only [hexp_deg]
    have hX_quarter_pos : 0 < (X : ℝ) ^ (δ_fin / 4) := by positivity
    calc 6 * (r₁ : ℝ) * z ≤ 6 * L * z := by gcongr
      _ = 6 * (L * z) := by ring
      _ ≤ 6 * L ^ m_deg := mul_le_mul_of_nonneg_left hLz_le_m (by norm_num)
      _ ≤ 6 * (((m_deg.factorial : ℝ) / (δ_fin / 4) ^ m_deg) * (X : ℝ) ^ (δ_fin / 4)) :=
          mul_le_mul_of_nonneg_left hLm_deg_le (by norm_num)
      _ = (6 * ((m_deg.factorial : ℝ) / (δ_fin / 4) ^ m_deg)) * (X : ℝ) ^ (δ_fin / 4) := by ring
      _ < (X : ℝ) ^ (δ_fin / 4) * (X : ℝ) ^ (δ_fin / 4) :=
          mul_lt_mul_of_pos_right (by linarith only [hx_δfin]) hX_quarter_pos
      _ = (X : ℝ) ^ (δ_fin / 2) := by rw [← Real.rpow_add hX0]; ring_nf
  have hj₀_r : (P_card.choose r₁ : ℝ) ≤ 6 * (r₁ : ℝ) * (B_card : ℝ) := by
    exact_mod_cast hj₀_ge
  have hr1_r_pos : (0 : ℝ) < 6 * (r₁ : ℝ) := by
    have : (0 : ℝ) < r₁ := Nat.cast_pos.mpr hr₁_pos
    positivity
  have hXβ_le_β' : (X : ℝ) ^ β ≤ (X : ℝ) ^ β' :=
    Real.rpow_le_rpow_of_exponent_le (by linarith only [hX16]) hβ_le
  have hstrict_β' : (X : ℝ) ^ β' < (X : ℝ) ^ (β' + δ_fin / 2) / (6 * (r₁ : ℝ) * z) := by
    rw [lt_div_iff₀ (by positivity), Real.rpow_add hX0]
    exact mul_lt_mul_of_pos_left h6r1z_lt (by positivity)
  have hbuck_ge : (X : ℝ) ^ (β' + δ_fin / 2) / (6 * (r₁ : ℝ) * z) ≤ (B_card : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    calc (X : ℝ) ^ (β' + δ_fin / 2)
        ≤ (P_card.choose r₁ : ℝ) * z := (div_le_iff₀ hz_pos).mp hchoose_r1
      _ ≤ (6 * (r₁ : ℝ) * (B_card : ℝ)) * z := mul_le_mul_of_nonneg_right hj₀_r hz_pos.le
      _ = (B_card : ℝ) * (6 * (r₁ : ℝ) * z) := by ring
  exact hXβ_le_β'.trans_lt (hstrict_β'.trans_le hbuck_ge)

/-- **Log-power cell bounded-arity obstruction (`B > k`)**: For every arity bound `k`,
log-power cell exponent `B > k`, constant `C > 0`, and exponent `β < 1 - k / B`, on **every**
sufficiently large dyadic block `(X, 2X]`, strictly more than `X^β` friable squarefree integers
are isolated under `BoundedArityLocalExchange k (C X / (log X)^B)` and left unmatched by every
admissible opposite-parity matching. -/
theorem eventually_logPowerCell_boundedArity_unmatched_gt_rpow (k : ℕ) {B C β : ℝ}
    (hBk : (k : ℝ) < B) (hC : 0 < C) (hβ : β < 1 - (k : ℝ) / B) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (X : ℝ) ^ β <
        ((isolatedVertices (BoundedArityLocalExchange k (C * (X : ℝ) / Real.log X ^ B))
          (Ioc X (2 * X))).card : ℝ) ∧
      ∀ M : OppositeParityMatching
          (BoundedArityLocalExchange k (C * (X : ℝ) / Real.log X ^ B)) (Ioc X (2 * X)),
        (X : ℝ) ^ β < (M.unmatchedSet.card : ℝ) := by
  have hB_pos : 0 < B := lt_of_le_of_lt (Nat.cast_nonneg k) hBk
  have hkB_nn : 0 ≤ (k : ℝ) / B := div_nonneg (Nat.cast_nonneg k) hB_pos.le
  have h1_sub_kB : 0 < 1 - (k : ℝ) / B := by
    rw [sub_pos, div_lt_one hB_pos]; exact hBk
  obtain ⟨β', hβ'_def⟩ : ∃ β' : ℝ, β' = max β ((1 - (k : ℝ) / B) / 2) := ⟨_, rfl⟩
  have hβ_le : β ≤ β' := by rw [hβ'_def]; exact le_max_left _ _
  have hβ'_pos : 0 < β' := by rw [hβ'_def]; exact lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hβ'_lt : β' < 1 - (k : ℝ) / B := by rw [hβ'_def]; exact max_lt hβ (by linarith only [h1_sub_kB])
  have h1_sub_β' : 0 < 1 - β' := by linarith only [hβ'_lt, hkB_nn]
  obtain ⟨γ, hγ_def⟩ : ∃ γ : ℝ,
    γ = if k = 0 then 2 / (1 - β') else (1 / (1 - β') + B / (k : ℝ)) / 2 := ⟨_, rfl⟩
  have hγ_gt_inv : 1 / (1 - β') < γ := by
    rw [hγ_def]
    split_ifs with hk0
    · have hpos_inv : 0 < 1 / (1 - β') := by positivity
      linarith [show 2 / (1 - β') = 2 * (1 / (1 - β')) by ring]
    · have hk_pos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
      have hlt : 1 / (1 - β') < B / (k : ℝ) := by
        rw [div_lt_div_iff₀ h1_sub_β' hk_pos]
        have h1 : (k : ℝ) / B < 1 - β' := by linarith only [hβ'_lt]
        have h2 : (k : ℝ) < (1 - β') * B := (div_lt_iff₀ hB_pos).mp h1
        linarith only [h2]
      linarith only [hlt]
  have hγ_gt1 : 1 < γ :=
    lt_trans ((one_lt_div h1_sub_β').mpr (by linarith only [hβ'_pos])) hγ_gt_inv
  have hkγ_lt_B : (k : ℝ) * γ < B := by
    rw [hγ_def]
    split_ifs with hk0
    · simp [hk0, hB_pos]
    · have hk_pos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
      have hlt : 1 / (1 - β') < B / (k : ℝ) := by
        rw [div_lt_div_iff₀ h1_sub_β' hk_pos]
        have h1 : (k : ℝ) / B < 1 - β' := by linarith only [hβ'_lt]
        have h2 : (k : ℝ) < (1 - β') * B := (div_lt_iff₀ hB_pos).mp h1
        linarith only [h2]
      have hmid : (1 / (1 - β') + B / (k : ℝ)) / 2 < B / (k : ℝ) := by linarith only [hlt]
      rwa [lt_div_iff₀ hk_pos, mul_comm] at hmid
  have hγ_pos : 0 < γ := by linarith only [hγ_gt1]
  have hβ'_lt_one_inv : β' < 1 - 1 / γ := by
    have hdiv_lt : 1 / γ < 1 - β' := by
      rw [div_lt_iff₀ hγ_pos]
      rw [div_lt_iff₀ h1_sub_β'] at hγ_gt_inv
      linarith only [hγ_gt_inv]
    linarith only [hdiv_lt]
  obtain ⟨ε₀, hε₀_def⟩ : ∃ ε₀ : ℝ, ε₀ = (1 - 1 / γ - β') / 3 := ⟨_, rfl⟩
  have hε₀_pos : 0 < ε₀ := by rw [hε₀_def]; linarith only [hβ'_lt_one_inv]
  have hε₀_lt1 : ε₀ < 1 / 2 := by
    have hinv_pos : 0 < 1 / γ := by positivity
    rw [hε₀_def]; linarith only [hinv_pos, hβ'_pos]
  obtain ⟨α_y, hαy_def⟩ : ∃ α_y : ℝ, α_y = (1 + γ) / 2 := ⟨_, rfl⟩
  have hαy_gt1 : 1 < α_y := by rw [hαy_def]; linarith only [hγ_gt1]
  have hαy_lt_γ : α_y < γ := by rw [hαy_def]; linarith only [hγ_gt1]
  obtain ⟨L_root, hLr_def⟩ : ∃ L_root : ℕ, L_root = ⌈α_y / (γ - α_y)⌉₊ + 2 := ⟨_, rfl⟩
  have hLr_ge2 : 2 ≤ L_root := by omega
  have hL_root_pos : (0 : ℝ) < L_root := by exact_mod_cast (show 0 < L_root by omega)
  have hαy_step_lt_γ : ((L_root + 1 : ℕ) : ℝ) / L_root * α_y < γ := by
    have hL_gt : α_y / (γ - α_y) < L_root := by
      calc α_y / (γ - α_y) ≤ ⌈α_y / (γ - α_y)⌉₊ := Nat.le_ceil _
        _ < L_root := by rw [hLr_def]; push_cast; linarith
    rw [div_lt_iff₀ (by linarith only [hαy_lt_γ])] at hL_gt
    rw [div_mul_eq_mul_div, div_lt_iff₀ hL_root_pos]
    push_cast; linarith only [hL_gt, hαy_gt1]
  obtain ⟨κ, hκ_def⟩ : ∃ κ : ℝ, κ = (14 / 9 : ℝ) ^ (1 / (L_root : ℝ)) := ⟨_, rfl⟩
  have hκ_gt1 : 1 < κ := by rw [hκ_def]; exact Real.one_lt_rpow (by norm_num) (by positivity)
  have hκ_pow : κ ^ L_root = 14 / 9 := by
    rw [hκ_def, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      one_div_mul_cancel hL_root_pos.ne', Real.rpow_one]
  obtain ⟨U_2, _, hwin_2⟩ := exists_windowPrimes_const_ratio_ge (α := 2) (by norm_num)
  obtain ⟨U_κ, _, hwin_κ⟩ := exists_windowPrimes_const_ratio_ge (α := κ) hκ_gt1
  obtain ⟨δ_y, hδy_def⟩ : ∃ δ_y : ℝ, δ_y = α_y - 1 := ⟨_, rfl⟩
  have hδy_pos : 0 < δ_y := by rw [hδy_def]; linarith only [hαy_gt1]
  obtain ⟨δ_z, hδz_def⟩ : ∃ δ_z : ℝ, δ_z = γ - ((L_root + 1 : ℕ) : ℝ) / L_root * α_y := ⟨_, rfl⟩
  have hδz_pos : 0 < δ_z := by rw [hδz_def]; linarith only [hαy_step_lt_γ]
  obtain ⟨δ_B, hδB_def⟩ : ∃ δ_B : ℝ, δ_B = B - (k : ℝ) * γ := ⟨_, rfl⟩
  have hδB_pos : 0 < δ_B := by rw [hδB_def]; linarith only [hkγ_lt_B]
  obtain ⟨δ_fin, hδfin_def⟩ : ∃ δ_fin : ℝ, δ_fin = (1 - ε₀) * (1 - 1 / γ) - β' := ⟨_, rfl⟩
  have h1_inv_pos : 0 < 1 - 1 / γ := by linarith only [hβ'_pos, hβ'_lt_one_inv]
  have h1_inv_lt1 : 1 - 1 / γ < 1 := by
    have hinv_pos : 0 < 1 / γ := by positivity
    linarith only [hinv_pos]
  have hδ_fin_pos : 0 < δ_fin := by
    have h1 : ε₀ * (1 - 1 / γ) < ε₀ * 1 := mul_lt_mul_of_pos_left h1_inv_lt1 hε₀_pos
    rw [hδfin_def]; linarith only [h1, hε₀_def, hε₀_pos]
  obtain ⟨ε₂, hε₂_def⟩ : ∃ ε₂ : ℝ, ε₂ = δ_fin / (2 * (1 - 1 / γ)) := ⟨_, rfl⟩
  have hε₂_pos : 0 < ε₂ := by rw [hε₂_def]; positivity
  have hexp_target : β' + δ_fin / 2 ≤ (1 - ε₀) * (1 - ε₂) * (1 - 1 / γ) := by
    have hmul : ε₂ * (1 - 1 / γ) = δ_fin / 2 := by
      rw [hε₂_def, div_mul_eq_mul_div, mul_div_mul_right _ _ h1_inv_pos.ne']
    have h1 : (1 - ε₀) * (1 - ε₂) * (1 - 1 / γ) =
        (1 - ε₀) * (1 - 1 / γ) - (1 - ε₀) * (ε₂ * (1 - 1 / γ)) := by ring
    rw [h1, hmul]
    have h2 : (1 - ε₀) * (δ_fin / 2) ≤ 1 * (δ_fin / 2) :=
      mul_le_mul_of_nonneg_right (by linarith only [hε₀_pos]) (by positivity)
    linarith only [h2, hδfin_def]
  obtain ⟨m_deg, hm_deg_def⟩ : ∃ m_deg : ℕ, m_deg = ⌈γ⌉₊ + 2 := ⟨_, rfl⟩
  have hm_deg_gt : γ + 1 < (m_deg : ℝ) := by
    calc γ + 1 ≤ ⌈γ⌉₊ + 1 := by linarith [Nat.le_ceil γ]
      _ < m_deg := by rw [hm_deg_def]; push_cast; linarith
  obtain ⟨m_L, hm_L_def⟩ : ∃ m_L : ℕ, m_L = ⌈α_y * (L_root : ℝ)⌉₊ + 1 := ⟨_, rfl⟩
  have hm_L_ge : α_y * (L_root : ℝ) ≤ (m_L : ℝ) := by
    calc α_y * (L_root : ℝ) ≤ ⌈α_y * (L_root : ℝ)⌉₊ := Nat.le_ceil _
      _ ≤ m_L := by rw [hm_L_def]; push_cast; linarith
  have hlog_atTop := Real.tendsto_log_atTop
  have hev_L : ∀ᶠ L : ℝ in atTop,
      16 ≤ L ∧ 2 ≤ Real.log L ∧
      max (2 * U_2) 8 ≤ L ^ α_y ∧ U_κ ≤ L ^ α_y ∧ 2 * U_2 ≤ L ^ γ ∧
      (32 * α_y / δ_y + 16) ≤ L ^ (δ_y / 2) ∧
      (6 : ℝ) * κ * (2 : ℝ) ^ (((L_root + 1 : ℕ) : ℝ) / L_root) ≤ L ^ δ_z ∧
      2 * (L_root : ℝ) * κ * (1 + γ) / ((κ - 1) / 2) ≤ L ^ (α_y - 1 / 2) ∧
      (4 : ℝ) * γ / (1 - ε₀) ≤ L ^ (1 / 2 : ℝ) ∧
      (4 : ℝ) ≤ L ^ (ε₂ * (γ - 1)) ∧
      C ≤ L ^ δ_B :=
    (eventually_ge_atTop 16).and ((hlog_atTop.eventually_ge_atTop 2).and
      (((tendsto_rpow_atTop (by linarith only [hαy_gt1] : 0 < α_y)).eventually_ge_atTop _).and
        (((tendsto_rpow_atTop (by linarith only [hαy_gt1] : 0 < α_y)).eventually_ge_atTop _).and
          (((tendsto_rpow_atTop hγ_pos).eventually_ge_atTop _).and
            (((tendsto_rpow_atTop (by positivity : 0 < δ_y / 2)).eventually_ge_atTop _).and
              (((tendsto_rpow_atTop hδz_pos).eventually_ge_atTop _).and
                (((tendsto_rpow_atTop (by linarith only [hαy_gt1] : 0 < α_y - 1 / 2)).eventually_ge_atTop _).and
                  (((tendsto_rpow_atTop (by norm_num : 0 < (1 / 2 : ℝ))).eventually_ge_atTop _).and
                    (((tendsto_rpow_atTop (mul_pos hε₂_pos (sub_pos.mpr hγ_gt1))).eventually_ge_atTop _).and
                      ((tendsto_rpow_atTop hδB_pos).eventually_ge_atTop _))))))))))
  have hev : ∀ᶠ x : ℝ in atTop,
      16 ≤ x ∧
      (2 : ℝ) ^ L_root * ((m_L.factorial : ℝ) / (ε₀ / 2) ^ m_L) ≤ x ^ (ε₀ / 2) ∧
      (6 : ℝ) * ((m_deg.factorial : ℝ) / (δ_fin / 4) ^ m_deg) + 1 ≤ x ^ (δ_fin / 4) ∧
      (16 ≤ Real.log x ∧ 2 ≤ Real.log (Real.log x) ∧
        max (2 * U_2) 8 ≤ Real.log x ^ α_y ∧ U_κ ≤ Real.log x ^ α_y ∧ 2 * U_2 ≤ Real.log x ^ γ ∧
        (32 * α_y / δ_y + 16) ≤ Real.log x ^ (δ_y / 2) ∧
        (6 : ℝ) * κ * (2 : ℝ) ^ (((L_root + 1 : ℕ) : ℝ) / L_root) ≤ Real.log x ^ δ_z ∧
        2 * (L_root : ℝ) * κ * (1 + γ) / ((κ - 1) / 2) ≤ Real.log x ^ (α_y - 1 / 2) ∧
        (4 : ℝ) * γ / (1 - ε₀) ≤ Real.log x ^ (1 / 2 : ℝ) ∧
        (4 : ℝ) ≤ Real.log x ^ (ε₂ * (γ - 1)) ∧
        C ≤ Real.log x ^ δ_B) :=
    (eventually_ge_atTop 16).and
      (((tendsto_rpow_atTop (by positivity : 0 < ε₀ / 2)).eventually_ge_atTop _).and
        (((tendsto_rpow_atTop (by positivity : 0 < δ_fin / 4)).eventually_ge_atTop _).and
          (hlog_atTop.eventually hev_L)))
  obtain ⟨X_cut, hX_cut⟩ := eventually_atTop.mp hev
  refine ⟨max 1 ⌈X_cut⌉₊, fun X hX => ?_⟩
  have hX_ge : X_cut ≤ (X : ℝ) :=
    (Nat.le_ceil X_cut).trans (by exact_mod_cast le_of_max_le_right hX)
  obtain ⟨hX16, hx_ε₀, hx_δfin, hL16, hll2, hy_U2, hy_Uκ, hz_U2,
    hL_δy, hL_δz, hL_κwin, hL_r1, hL_ε2, hL_δB⟩ := hX_cut X hX_ge
  clear hlog_atTop hev_L hev hX_cut hX_ge
  have hX0 : (0 : ℝ) < X := by linarith only [hX16]
  obtain ⟨L, hL_def⟩ : ∃ L : ℝ, L = Real.log X := ⟨_, rfl⟩
  rw [← hL_def] at hL16 hll2 hy_U2 hy_Uκ hz_U2 hL_δy hL_δz hL_κwin hL_r1 hL_ε2 hL_δB
  have hL0 : 0 < L := by linarith only [hL16]
  obtain ⟨y, hy_def⟩ : ∃ y : ℝ, y = L ^ α_y := ⟨_, rfl⟩
  obtain ⟨z, hz_def⟩ : ∃ z : ℝ, z = L ^ γ := ⟨_, rfl⟩
  rw [← hy_def] at hy_U2 hy_Uκ
  rw [← hz_def] at hz_U2
  have hy_pos : 0 < y := by rw [hy_def]; positivity
  have hz_pos : 0 < z := by rw [hz_def]; positivity
  have hy_ge8 : 8 ≤ y := (le_max_right _ _).trans hy_U2
  have hz_split : z = L ^ δ_z * L ^ (((L_root + 1 : ℕ) : ℝ) / L_root * α_y) := by
    rw [hz_def, hδz_def, ← Real.rpow_add hL0]; congr 1; ring
  have hκ_z3 : κ * (2 * y) ^ (((L_root + 1 : ℕ) : ℝ) / L_root) ≤ z / 3 := by
    have hy_pow_eq : (2 * y) ^ (((L_root + 1 : ℕ) : ℝ) / L_root) =
        (2 : ℝ) ^ (((L_root + 1 : ℕ) : ℝ) / L_root) * L ^ (((L_root + 1 : ℕ) : ℝ) / L_root * α_y) := by
      rw [Real.mul_rpow (by norm_num) hy_pos.le, hy_def, ← Real.rpow_mul hL0.le, mul_comm α_y]
    have h6_le : κ * (2 : ℝ) ^ (((L_root + 1 : ℕ) : ℝ) / L_root) ≤ L ^ δ_z / 6 := by
      have heq6 : 6 * (κ * (2 : ℝ) ^ (((L_root + 1 : ℕ) : ℝ) / L_root)) =
          (6 : ℝ) * κ * (2 : ℝ) ^ (((L_root + 1 : ℕ) : ℝ) / L_root) := by ring
      linarith only [heq6, hL_δz]
    rw [hy_pow_eq, hz_split, ← mul_assoc]
    calc (κ * (2 : ℝ) ^ (((L_root + 1 : ℕ) : ℝ) / L_root)) *
            L ^ (((L_root + 1 : ℕ) : ℝ) / L_root * α_y)
        ≤ (L ^ δ_z / 6) * L ^ (((L_root + 1 : ℕ) : ℝ) / L_root * α_y) :=
          mul_le_mul_of_nonneg_right h6_le
            (show 0 ≤ L ^ (((L_root + 1 : ℕ) : ℝ) / L_root * α_y) by positivity)
      _ ≤ (L ^ δ_z * L ^ (((L_root + 1 : ℕ) : ℝ) / L_root * α_y)) / 3 := by
          rw [div_mul_eq_mul_div]
          exact div_le_div_of_nonneg_left (by positivity) (by norm_num) (by norm_num)
  have hyz : y ≤ z / 3 := by
    have h2y_le : 2 * y ≤ (2 * y) ^ (((L_root + 1 : ℕ) : ℝ) / L_root) := by
      conv_lhs => rw [← Real.rpow_one (2 * y)]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hy_ge8])
        ((one_le_div hL_root_pos).mpr (by push_cast; linarith))
    have h1 : 2 * y ≤ κ * (2 * y) ^ (((L_root + 1 : ℕ) : ℝ) / L_root) :=
      h2y_le.trans (le_mul_of_one_le_left (by positivity) hκ_gt1.le)
    linarith only [h1, hκ_z3, hy_pos]
  have hz_ge8 : 8 ≤ z := by linarith only [hy_ge8, hyz]
  have hlogz_eq : Real.log z = γ * Real.log L := by rw [hz_def]; exact Real.log_rpow hL0 γ
  have hlogz_pos : 0 < Real.log z := by rw [hlogz_eq]; positivity
  have hlogL_le_rpow : ∀ {η : ℝ}, 0 < η → Real.log L ≤ (1 / η) * L ^ η := by
    intro η hη
    have hLη_pos : 0 < L ^ η := by positivity
    have hexp := Real.pow_div_factorial_le_exp (Real.log (L ^ η))
      (by rw [Real.log_rpow hL0]; positivity) 1
    rw [Real.exp_log hLη_pos, pow_one, Nat.factorial_one, Nat.cast_one, div_one,
      Real.log_rpow hL0] at hexp
    rw [one_div_mul_eq_div, le_div_iff₀ hη, mul_comm]; exact hexp
  -- 1. Band 3: `P₁ = windowPrimes (z / 2) z`, `r₁`, and geometric bin `B₀`
  obtain ⟨P₁, hP₁_def⟩ : ∃ P₁ : Finset ℕ, P₁ = windowPrimes (z / 2) z := ⟨_, rfl⟩
  have hP₁_pr : ∀ p ∈ P₁, p.Prime ∧ z / 2 < (p : ℝ) ∧ (p : ℝ) ≤ z := fun p hp =>
    (mem_windowPrimes (by positivity) (by positivity)).mp (hP₁_def ▸ hp)
  have hP₁_card : z / (4 * Real.log z) ≤ (P₁.card : ℝ) := by
    have hw := hwin_2 (z / 2) (by linarith only [hz_U2])
    rw [show 2 * (z / 2) = z by ring, ← hP₁_def] at hw
    calc z / (4 * Real.log z) = ((2 - 1) / 2) * (z / 2) / Real.log z := by ring
      _ ≤ (P₁.card : ℝ) := hw
  obtain ⟨r₁, hr₁_def⟩ : ∃ r₁ : ℕ, r₁ = ⌊(1 - ε₀) * L / Real.log z⌋₊ := ⟨_, rfl⟩
  have hr₁_ge1 : 1 ≤ r₁ := by
    rw [hr₁_def]; apply Nat.le_floor; push_cast
    rw [le_div_iff₀ hlogz_pos, one_mul, hlogz_eq]
    have hll_half := hlogL_le_rpow (by norm_num : (0 : ℝ) < 1 / 2)
    have hsq : L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ) = L := by rw [← Real.rpow_add hL0]; norm_num
    have hLw := (div_le_iff₀ (by linarith only [hε₀_lt1])).mp hL_r1
    calc γ * Real.log L
        ≤ γ * ((1 / (1 / 2 : ℝ)) * L ^ (1 / 2 : ℝ)) := mul_le_mul_of_nonneg_left hll_half hγ_pos.le
      _ = (2 * γ) * L ^ (1 / 2 : ℝ) := by ring
      _ ≤ (4 * γ) * L ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith only [hγ_pos]) (by positivity)
      _ ≤ (L ^ (1 / 2 : ℝ) * (1 - ε₀)) * L ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right hLw (by positivity)
      _ = (1 - ε₀) * (L ^ (1 / 2 : ℝ) * L ^ (1 / 2 : ℝ)) := by ring
      _ = (1 - ε₀) * L := by rw [hsq]
  have hr₁_pos : 0 < r₁ := by omega
  have h1mε₀_pos : 0 < 1 - ε₀ := by linarith only [hε₀_lt1]
  have hr₁_le_real : (r₁ : ℝ) ≤ (1 - ε₀) * L / Real.log z := by
    rw [hr₁_def]
    exact Nat.floor_le (div_nonneg (mul_nonneg h1mε₀_pos.le hL0.le) hlogz_pos.le)
  have hPr_div_ge : L ^ (γ - 1) / 4 ≤ (P₁.card : ℝ) / r₁ := by
    have hr₁_r_pos : (0 : ℝ) < r₁ := by exact_mod_cast hr₁_pos
    have hr₁_up : (r₁ : ℝ) ≤ L / Real.log z :=
      hr₁_le_real.trans (div_le_div_of_nonneg_right
        (mul_le_of_le_one_left hL0.le (by linarith only [hε₀_pos])) hlogz_pos.le)
    calc L ^ (γ - 1) / 4
        = z / (4 * L) := by rw [hz_def, Real.rpow_sub hL0, Real.rpow_one]; ring
      _ = (z / (4 * Real.log z)) / (L / Real.log z) := by field_simp
      _ ≤ (P₁.card : ℝ) / r₁ := div_le_div₀ (Nat.cast_nonneg P₁.card) hP₁_card hr₁_r_pos hr₁_up
  have hε₂_lt1 : ε₂ < 1 := by
    rw [hε₂_def, hδfin_def, div_lt_iff₀ (by positivity)]
    have hm : (1 - ε₀) * (1 - 1 / γ) ≤ 1 * (1 - 1 / γ) :=
      mul_le_mul_of_nonneg_right (by linarith only [hε₀_pos]) h1_inv_pos.le
    linarith only [hm, hβ'_pos, h1_inv_pos]
  have hr₁_le_P₁ : r₁ ≤ P₁.card := by
    have hLγ1 : (4 : ℝ) ≤ L ^ (γ - 1) := by
      calc (4 : ℝ) ≤ L ^ (ε₂ * (γ - 1)) := hL_ε2
        _ ≤ L ^ (1 * (γ - 1)) := Real.rpow_le_rpow_of_exponent_le (by linarith only [hL16])
            (mul_le_mul_of_nonneg_right hε₂_lt1.le (by linarith only [hγ_gt1]))
        _ = L ^ (γ - 1) := by ring_nf
    have hr₁_r_pos : (0 : ℝ) < r₁ := by exact_mod_cast hr₁_pos
    have hge1 : (1 : ℝ) ≤ (P₁.card : ℝ) / r₁ := by linarith only [hLγ1, hPr_div_ge]
    rw [le_div_iff₀ hr₁_r_pos, one_mul] at hge1
    exact_mod_cast hge1
  obtain ⟨B₀, U, hB₀_sub, hU_ge1, hU_le_zr1, hj₀_ge, hB₀_win⟩ :=
    exists_winning_geometric_bin (by linarith only [hz_ge8]) hr₁_pos hr₁_le_P₁ hP₁_pr
  have hU_pos : 0 < U := by linarith only [hU_ge1]
  have hzr1_le_X1ε : z ^ r₁ ≤ (X : ℝ) ^ (1 - ε₀) := by
    have hr1_exp : (r₁ : ℝ) * Real.log z ≤ (1 - ε₀) * L :=
      (le_div_iff₀ hlogz_pos).mp hr₁_le_real
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hz_pos, Real.rpow_def_of_pos hX0]
    exact Real.exp_le_exp.mpr (by rw [← hL_def]; linarith only [hr1_exp])
  obtain ⟨W, hW_def⟩ : ∃ W : ℝ, W = (X : ℝ) / U := ⟨_, rfl⟩
  have hW_pos : 0 < W := by rw [hW_def]; positivity
  have hUW : U * W = (X : ℝ) := by rw [hW_def, mul_div_cancel₀ _ hU_pos.ne']
  have hW_le_X : W ≤ X := by rw [hW_def]; exact div_le_self hX0.le hU_ge1
  have hW_ge_Xε : (X : ℝ) ^ ε₀ ≤ W := by
    rw [hW_def, le_div_iff₀ hU_pos]
    calc (X : ℝ) ^ ε₀ * U ≤ (X : ℝ) ^ ε₀ * (X : ℝ) ^ (1 - ε₀) :=
          mul_le_mul_of_nonneg_left (hU_le_zr1.trans hzr1_le_X1ε) (by positivity)
      _ = X := by rw [← Real.rpow_add hX0, show ε₀ + (1 - ε₀) = 1 by ring, Real.rpow_one]
  -- 2. Verify hypotheses for `exists_two_band_cofactor`
  have hP_aux_card : L + 1 ≤ ((windowPrimes (y / 2) y).card : ℝ) := by
    have hw := hwin_2 (y / 2) (by linarith [le_max_left (2 * U_2) 8, hy_U2])
    rw [show 2 * (y / 2) = y by ring] at hw
    have hlogy : Real.log y = α_y * Real.log L := by rw [hy_def]; exact Real.log_rpow hL0 α_y
    have hll_δ := hlogL_le_rpow (by positivity : 0 < δ_y / 2)
    have hdenom : 4 * Real.log y ≤ L ^ δ_y / 2 := by
      have h2 : 4 * Real.log y ≤ (8 * α_y / δ_y) * L ^ (δ_y / 2) := by
        rw [hlogy]
        calc 4 * (α_y * Real.log L) ≤ 4 * (α_y * ((1 / (δ_y / 2)) * L ^ (δ_y / 2))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hll_δ (by positivity)) (by norm_num)
          _ = (8 * α_y / δ_y) * L ^ (δ_y / 2) := by ring
      have hsq_δ : L ^ (δ_y / 2) * L ^ (δ_y / 2) = L ^ δ_y := by
        rw [← Real.rpow_add hL0]; ring_nf
      have h32 : 8 * α_y / δ_y ≤ L ^ (δ_y / 2) / 4 := by
        have heq32 : 32 * α_y / δ_y = 4 * (8 * α_y / δ_y) := by ring
        linarith only [heq32, hL_δy]
      calc 4 * Real.log y ≤ (L ^ (δ_y / 2) / 4) * L ^ (δ_y / 2) :=
            h2.trans (mul_le_mul_of_nonneg_right h32 (by positivity))
        _ = L ^ δ_y / 4 := by rw [div_mul_eq_mul_div, hsq_δ]
        _ ≤ L ^ δ_y / 2 := by linarith [show 0 < L ^ δ_y by positivity]
    have hy_split : y = L * L ^ δ_y := by
      rw [hy_def, ← Real.rpow_one_add' hL0.le (by linarith only [hδy_pos] : 0 < 1 + δ_y).ne', hδy_def]
      congr 1; ring
    calc L + 1 ≤ 2 * L := by linarith only [hL16]
      _ = y / (L ^ δ_y / 2) := by rw [hy_split]; field_simp
      _ ≤ y / (4 * Real.log y) := div_le_div_of_nonneg_left hy_pos.le
          (mul_pos (by norm_num) (Real.log_pos (by linarith only [hy_ge8]))) hdenom
      _ = ((2 - 1) / 2) * (y / 2) / Real.log y := by ring
      _ ≤ ((windowPrimes (y / 2) y).card : ℝ) := hw
  have h2y_Lroot_le_Xε : (2 * y) ^ L_root ≤ (X : ℝ) ^ ε₀ := by
    have h1 : (2 * y) ^ L_root ≤ (2 : ℝ) ^ L_root * L ^ m_L := by
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [hy_def, ← Real.rpow_natCast (L ^ α_y), ← Real.rpow_mul hL0.le, ← Real.rpow_natCast L]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hL16]) hm_L_ge
    have hexp_m := Real.pow_div_factorial_le_exp ((ε₀ / 2) * L) (by positivity) m_L
    rw [show Real.exp ((ε₀ / 2) * L) = (X : ℝ) ^ (ε₀ / 2) by
      rw [hL_def, Real.rpow_def_of_pos hX0, mul_comm]] at hexp_m
    have hfac_m_pos : (0 : ℝ) < m_L.factorial := by exact_mod_cast Nat.factorial_pos m_L
    have hLm_le : L ^ m_L ≤ ((m_L.factorial : ℝ) / (ε₀ / 2) ^ m_L) * (X : ℝ) ^ (ε₀ / 2) := by
      rw [mul_pow, div_le_iff₀ hfac_m_pos] at hexp_m
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      linarith only [hexp_m]
    calc (2 * y) ^ L_root ≤ (2 : ℝ) ^ L_root * L ^ m_L := h1
      _ ≤ (2 : ℝ) ^ L_root * (((m_L.factorial : ℝ) / (ε₀ / 2) ^ m_L) * (X : ℝ) ^ (ε₀ / 2)) :=
          mul_le_mul_of_nonneg_left hLm_le (by positivity)
      _ = ((2 : ℝ) ^ L_root * ((m_L.factorial : ℝ) / (ε₀ / 2) ^ m_L)) * (X : ℝ) ^ (ε₀ / 2) := by
          ring
      _ ≤ (X : ℝ) ^ (ε₀ / 2) * (X : ℝ) ^ (ε₀ / 2) :=
          mul_le_mul_of_nonneg_right hx_ε₀ (by positivity)
      _ = (X : ℝ) ^ ε₀ := by rw [← Real.rpow_add hX0]; ring_nf
  have hW_pow : W / (2 * y) ^ L_root < (y / 2) ^ (windowPrimes (y / 2) y).card := by
    have hW₀_le_X : W / (2 * y) ^ L_root ≤ X :=
      (div_le_self hW_pos.le (one_le_pow₀ (by linarith only [hy_ge8]))).trans hW_le_X
    have hexp_L : (X : ℝ) < Real.exp ((windowPrimes (y / 2) y).card : ℝ) := by
      conv_lhs => rw [← Real.exp_log hX0]
      exact Real.exp_lt_exp.mpr (by rw [← hL_def]; linarith only [hP_aux_card])
    have hexp_pow : Real.exp ((windowPrimes (y / 2) y).card : ℝ) ≤
        (4 : ℝ) ^ (windowPrimes (y / 2) y).card := by
      rw [← mul_one ((windowPrimes (y / 2) y).card : ℝ), Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) _
    have h4_le_y2 : (4 : ℝ) ^ (windowPrimes (y / 2) y).card ≤
        (y / 2) ^ (windowPrimes (y / 2) y).card :=
      pow_le_pow_left₀ (by norm_num) (by linarith only [hy_ge8]) _
    exact hW₀_le_X.trans_lt (hexp_L.trans_le (hexp_pow.trans h4_le_y2))
  have hcard_w : ∀ w : ℝ, 2 * y ≤ w → κ * w ≤ z / 3 → L_root ≤ (windowPrimes w (κ * w)).card := by
    intro w hw_ge_2y hκw_z3
    have hw_κ := hwin_κ w (by linarith only [hy_Uκ, hw_ge_2y, hy_pos])
    have hlog_κw : Real.log (κ * w) ≤ Real.log (4 * z) :=
      Real.log_le_log (mul_pos (by linarith only [hκ_gt1]) (by linarith only [hw_ge_2y, hy_pos]))
        (by linarith only [hκw_z3, hz_pos])
    have hlog_κw_pos : 0 < Real.log (κ * w) :=
      Real.log_pos (one_lt_mul_of_lt_of_le hκ_gt1 (by linarith only [hw_ge_2y, hy_ge8]))
    have hlog4z_le : Real.log (4 * z) ≤ 2 * (1 + γ) * L ^ (1 / 2 : ℝ) := by
      rw [Real.log_mul (by norm_num) hz_pos.ne', hlogz_eq]
      have hll_half := hlogL_le_rpow (by norm_num : (0 : ℝ) < 1 / 2)
      have h1_half : (1 : ℝ) ≤ L ^ (1 / 2 : ℝ) :=
        Real.one_le_rpow (by linarith only [hL16]) (by norm_num)
      have hlog4 : Real.log 4 ≤ 2 * L ^ (1 / 2 : ℝ) := by
        have hl4 : Real.log 4 ≤ 2 := by
          rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
          push_cast; linarith [Real.log_two_lt_d9]
        exact hl4.trans (le_mul_of_one_le_right (by norm_num) h1_half)
      have hγL : γ * Real.log L ≤ 2 * γ * L ^ (1 / 2 : ℝ) := by
        calc γ * Real.log L ≤ γ * ((1 / (1 / 2 : ℝ)) * L ^ (1 / 2 : ℝ)) :=
              mul_le_mul_of_nonneg_left hll_half hγ_pos.le
          _ = 2 * γ * L ^ (1 / 2 : ℝ) := by ring
      calc Real.log 4 + γ * Real.log L
          ≤ 2 * L ^ (1 / 2 : ℝ) + 2 * γ * L ^ (1 / 2 : ℝ) := add_le_add hlog4 hγL
        _ = 2 * (1 + γ) * L ^ (1 / 2 : ℝ) := by ring
    have hLroot_r : (L_root : ℝ) ≤ ((κ - 1) / 2) * w / Real.log (κ * w) := by
      rw [le_div_iff₀ hlog_κw_pos]
      have hy_split_half : L ^ (α_y - 1 / 2) * L ^ (1 / 2 : ℝ) = y := by
        rw [hy_def, ← Real.rpow_add hL0]; congr 1; ring
      have hstep1 : (L_root : ℝ) * Real.log (κ * w) ≤
          2 * (L_root : ℝ) * (1 + γ) * L ^ (1 / 2 : ℝ) := by
        have hm := mul_le_mul_of_nonneg_left (hlog_κw.trans hlog4z_le) (Nat.cast_nonneg L_root)
        linarith only [hm]
      have hstep2 : 2 * (L_root : ℝ) * (1 + γ) * L ^ (1 / 2 : ℝ) ≤ ((κ - 1) / 2) * y := by
        have hκ_pos : 0 < (κ - 1) / 2 := by linarith only [hκ_gt1]
        have hLw := (div_le_iff₀ hκ_pos).mp hL_κwin
        have hmul := mul_le_mul_of_nonneg_right hLw (show 0 ≤ L ^ (1 / 2 : ℝ) by positivity)
        have hrhs : L ^ (α_y - 1 / 2) * ((κ - 1) / 2) * L ^ (1 / 2 : ℝ) = ((κ - 1) / 2) * y := by
          rw [← hy_split_half]; ring
        rw [hrhs] at hmul
        have hle_κ : 2 * (L_root : ℝ) * (1 + γ) ≤ 2 * (L_root : ℝ) * κ * (1 + γ) := by
          have hbase : (L_root : ℝ) * (1 + γ) ≤ (L_root : ℝ) * (1 + γ) * κ :=
            le_mul_of_one_le_right (by positivity) hκ_gt1.le
          linarith only [hbase]
        exact (mul_le_mul_of_nonneg_right hle_κ (by positivity)).trans hmul
      have hstep3 : ((κ - 1) / 2) * y ≤ ((κ - 1) / 2) * w :=
        mul_le_mul_of_nonneg_left (by linarith only [hw_ge_2y, hy_pos]) (by linarith only [hκ_gt1])
      exact hstep1.trans (hstep2.trans hstep3)
    exact_mod_cast hLroot_r.trans hw_κ
  obtain ⟨Q_star, hQstar_pos, hsq_Qstar, hQstar_pf_le, hQstar_low, hQstar_up⟩ :=
    exists_two_band_cofactor hLr_ge2 hy_ge8 hyz hκ_gt1 hκ_pow
      (h2y_Lroot_le_Xε.trans hW_ge_Xε) hW_pow hκ_z3 hcard_w
  -- 3. Apply `bin_cofactor_card_le_isolatedVertices`
  have hZH_cell : ((⌊z⌋₊ : ℕ) : ℝ) ^ k * (C * (X : ℝ) / Real.log X ^ B) ≤ X := by
    have hZk : ((⌊z⌋₊ : ℕ) : ℝ) ^ k ≤ L ^ ((k : ℝ) * γ) := by
      calc ((⌊z⌋₊ : ℕ) : ℝ) ^ k ≤ z ^ k := pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hz_pos.le) k
        _ = L ^ ((k : ℝ) * γ) := by
            rw [hz_def, ← Real.rpow_natCast (L ^ γ), ← Real.rpow_mul hL0.le, mul_comm]
    have hLB_split : L ^ B = L ^ ((k : ℝ) * γ) * L ^ δ_B := by
      rw [hδB_def, ← Real.rpow_add hL0]; congr 1; ring
    rw [← hL_def]
    calc ((⌊z⌋₊ : ℕ) : ℝ) ^ k * (C * (X : ℝ) / L ^ B)
        ≤ L ^ ((k : ℝ) * γ) * (C * (X : ℝ) / (L ^ ((k : ℝ) * γ) * L ^ δ_B)) := by
          rw [← hLB_split]; exact mul_le_mul_of_nonneg_right hZk (by positivity)
      _ = (C / L ^ δ_B) * X := by
          have : L ^ ((k : ℝ) * γ) ≠ 0 := by positivity
          field_simp
      _ ≤ 1 * X := mul_le_mul_of_nonneg_right ((div_le_one (by positivity)).mpr hL_δB) hX0.le
      _ = X := one_mul _
  have hiso_card := bin_cofactor_card_le_isolatedVertices hz_pos hU_pos hW_pos hUW
    hP₁_pr hB₀_sub hB₀_win hQstar_pos hsq_Qstar hQstar_pf_le hQstar_low hQstar_up hZH_cell
  -- 4. Quantitative lower bound `(X : ℝ) ^ β < (B₀.card : ℝ)`
  rw [card_powersetCard] at hj₀_ge
  have hB₀_gt : (X : ℝ) ^ β < (B₀.card : ℝ) :=
    rpow_lt_bin_card_of_bounds hX16 hL16 hll2 hL_def hz_def hβ_le hε₀_pos hε₂_pos hε₂_lt1
      hγ_gt1 h1_inv_pos h1_inv_lt1 hδ_fin_pos hexp_target hm_deg_gt hx_δfin hL_ε2
      hr₁_pos hr₁_le_P₁ hr₁_def hr₁_le_real hPr_div_ge hj₀_ge
  have hiso_gt : (X : ℝ) ^ β <
      ((isolatedVertices (BoundedArityLocalExchange k (C * (X : ℝ) / Real.log X ^ B))
        (Ioc X (2 * X))).card : ℝ) :=
    hB₀_gt.trans_le (by exact_mod_cast hiso_card)
  exact ⟨hiso_gt, fun M => hiso_gt.trans_le
    (by exact_mod_cast card_isolatedVertices_le_unmatched M)⟩

/-- **Square-root barrier corollary (`B > 2k`)**: At log-power cell width `H ≤ C X / (log X)^B`
with `B > 2k`, there exists `δ > 0` such that on every sufficiently large dyadic block `(X, 2X]`,
every `k`-arity local opposite-parity matching leaves strictly more than `X^{1/2 + δ}` unmatched
squarefree integers (ruling out Riemann-Hypothesis-scale cancellation). -/
theorem eventually_logPowerCell_boundedArity_unmatched_gt_half (k : ℕ) {B C : ℝ}
    (hB2k : 2 * (k : ℝ) < B) (hC : 0 < C) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ M : OppositeParityMatching
          (BoundedArityLocalExchange k (C * (X : ℝ) / Real.log X ^ B)) (Ioc X (2 * X)),
        (X : ℝ) ^ (1 / 2 + δ) < (M.unmatchedSet.card : ℝ) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hB_pos : 0 < B := lt_of_le_of_lt (by positivity) hB2k
  have hBk : (k : ℝ) < B := by linarith
  have hhalf_lt : (1 / 2 : ℝ) < 1 - (k : ℝ) / B := by
    have : (k : ℝ) / B < 1 / 2 := by
      rw [div_lt_div_iff₀ hB_pos (by norm_num)]
      linarith
    linarith
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = (1 - (k : ℝ) / B - 1 / 2) / 2 := ⟨_, rfl⟩
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  obtain ⟨X₀, hX₀⟩ := eventually_logPowerCell_boundedArity_unmatched_gt_rpow k hBk hC
    (β := 1 / 2 + δ) (by rw [hδ_def]; linarith)
  exact ⟨δ, hδ_pos, X₀, fun X hX M => (hX₀ X hX).2 M⟩

/-- **Sub-`20999/24000` benchmark barrier corollary (`B > 24000k`)**: Whenever `B > 24000k`,
there exists `δ > 0` such that on every sufficiently large dyadic block `(X, 2X]`, every `k`-arity
local opposite-parity matching at cell width `≤ C X / (log X)^B` leaves strictly more than
`X^{20999/24000 + δ}` unmatched squarefree integers. -/
theorem eventually_logPowerCell_boundedArity_unmatched_gt_strip_benchmark (k : ℕ) {B C : ℝ}
    (hB_bench : 24000 * (k : ℝ) < B) (hC : 0 < C) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ M : OppositeParityMatching
          (BoundedArityLocalExchange k (C * (X : ℝ) / Real.log X ^ B)) (Ioc X (2 * X)),
        (X : ℝ) ^ (20999 / 24000 + δ) < (M.unmatchedSet.card : ℝ) := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hB_pos : 0 < B := lt_of_le_of_lt (by positivity) hB_bench
  have hBk : (k : ℝ) < B := by linarith
  have hbench_lt : (20999 / 24000 : ℝ) < 1 - (k : ℝ) / B := by
    have hk_div : (k : ℝ) / B < 1 / 24000 := by
      rw [div_lt_div_iff₀ hB_pos (by norm_num)]
      linarith
    linarith
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = (1 - (k : ℝ) / B - 20999 / 24000) / 2 := ⟨_, rfl⟩
  have hδ_pos : 0 < δ := by rw [hδ_def]; linarith
  obtain ⟨X₀, hX₀⟩ := eventually_logPowerCell_boundedArity_unmatched_gt_rpow k hBk hC
    (β := 20999 / 24000 + δ) (by rw [hδ_def]; linarith)
  exact ⟨δ, hδ_pos, X₀, fun X hX M => (hX₀ X hX).2 M⟩

end GaloisForLFunctions.QuantitativeFactorizationMatching


