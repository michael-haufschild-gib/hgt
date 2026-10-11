import GaloisForLFunctions.RHTower.JointAncestrySharpAbscissaLaw
import GaloisForLFunctions.RHTower.JointAncestryLocalExistence

/-!
# The large-prime JAS abscissa is `½ + Θ`

`JasDressedPSDAbove X σ` is positivity of the dressed JAS aggregate on all characters supported on
primes `p > X`.

* **Upper bound** (`jasDressedPSDAbove_of_xiZeroHalfPlaneBound`).  If `Re ρ ≤ ½ + α` for every
  zero, then for every `0 < ε ≤ 1` and every `X` with `log X ≥ 1/ε + 1`, positivity holds above
  `X` at `σ = 1 + α + ε`.  Per-zero phase widths are at most `(8/7) p^{−(1+ε)}`, and the tail
  `Σ_{p > X} p^{−(1+ε)} ≤ (1/ε + 1)/log X` is small.  With `α = ½` this is unconditional:
  large-prime positivity holds at every `σ > 3/2` (`exists_jasDressedPSDAbove_three_halves_add`).
* **Lower bound** (`one_add_sSup_le_of_jasDressedPSDAbove_of_chain`).  Under a half-plane bound
  below `½`, if the off-line zeros form a chain and positivity holds above some `X` at `σ`, then
  `σ ≥ 1 + δ*`: the chain-exclusion tests use only the primes of the windows `(n, n²]`, `n → ∞`.

Hence, for chains under quasi-RH, the large-prime abscissa equals `1 + δ* = ½ + Θ` in the limit
`X → ∞` (`largePrime_abscissa_eq_of_chain`): the per-zero method is exact on large primes.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- Positivity on all characters supported on primes `p > X`. -/
def JasDressedPSDAbove (X : ℕ) (σ : ℝ) : Prop :=
  ∀ S : Finset Nat.Primes, (∀ p ∈ S, X < (p : ℕ)) → JasDressedPSDOn S σ

theorem support_jasBernoulliChar_subset (P : Finset Nat.Primes) (x : P → Bool) :
    (jasBernoulliChar P x).support ⊆ P :=
  Finsupp.support_onFinset_subset

/-- Bernoulli positivity from positivity on a prime set `S ⊇ P`. -/
theorem jasBernoulliAggregate_nonneg_of_on {σ : ℝ} {S : Finset Nat.Primes}
    (h : JasDressedPSDOn S σ) (P : Finset Nat.Primes) (hP : P ⊆ S) (z : Nat.Primes → ℂ) :
    0 ≤ (∑' q : XiZeroCopy,
      (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  classical
  have hPSD := h (P → Bool) Finset.univ (jasBernoulliWeight P z) (jasBernoulliChar P)
    ((jasBernoulliChar_injective P).injOn) fun x _ => (support_jasBernoulliChar_subset P x).trans hP
  have heq : ∑ x ∈ (Finset.univ : Finset (P → Bool)), ∑ y ∈ (Finset.univ : Finset (P → Bool)),
      jasBernoulliWeight P z x * conj (jasBernoulliWeight P z y) *
        jasDressedLagAggregate σ (jasBernoulliChar P x - jasBernoulliChar P y) =
      ∑' q : XiZeroCopy,
        (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
          (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
    set c : ℝ := σ - 1 / 2
    have hs : ∀ x y : P → Bool, Summable (fun q : XiZeroCopy =>
        jasBernoulliWeight P z x * conj (jasBernoulliWeight P z y) *
          (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c)
            (jasBernoulliChar P x - jasBernoulliChar P y) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))) :=
      fun x y => (summable_jasDressedCoeff_term σ _).mul_left _
    calc _ = ∑ x : P → Bool, ∑ y : P → Bool, ∑' q : XiZeroCopy,
          jasBernoulliWeight P z x * conj (jasBernoulliWeight P z y) *
            (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c)
              (jasBernoulliChar P x - jasBernoulliChar P y) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
          simp_rw [jasDressedLagAggregate_eq_tsum, ← tsum_mul_left]
          rfl
      _ = ∑ x : P → Bool, ∑' q : XiZeroCopy, ∑ y : P → Bool,
          jasBernoulliWeight P z x * conj (jasBernoulliWeight P z y) *
            (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c)
              (jasBernoulliChar P x - jasBernoulliChar P y) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) :=
          Finset.sum_congr rfl fun x _ => (Summable.tsum_finsetSum fun y _ => hs x y).symm
      _ = ∑' q : XiZeroCopy, ∑ x : P → Bool, ∑ y : P → Bool,
          jasBernoulliWeight P z x * conj (jasBernoulliWeight P z y) *
            (jasDressedCoeff ((q.1 : ℂ) + c) ((q.1 : ℂ) - c)
              (jasBernoulliChar P x - jasBernoulliChar P y) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) :=
          (Summable.tsum_finsetSum fun x _ => summable_sum fun y _ => hs x y).symm
      _ = _ := by
          refine tsum_congr fun q => ?_
          rw [← sum_sum_bernoulli_jasDressedCoeff, Finset.sum_div]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun y _ => ?_
          ring
  rw [heq] at hPSD
  exact hPSD

/-- Log-weight Bernoulli positivity from positivity on a prime set `S ⊇ P`. -/
theorem jasLogWeightBernoulli_nonneg_of_on {σ : ℝ} {S : Finset Nat.Primes}
    (h : JasDressedPSDOn S σ) (ξ : ℂ) (P : Finset Nat.Primes) (hP : P ⊆ S) (a : Nat.Primes → ℝ)
    (ha0 : ∀ p ∈ P, 0 ≤ a p)
    (ha : ∀ p ∈ P, a p * Real.exp ((ξ.re + (σ - 1 / 2)) * Real.log p) ≤ 1 / 2) (φ : ℝ) :
    0 ≤ (∑' q : XiZeroCopy,
      (∏ p ∈ P, jasLogWeightLocal ξ (q.1 : ℂ) (a p) φ p) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := by
  classical
  set c : ℝ := σ - 1 / 2 with hc
  have hex : ∀ p : Nat.Primes, ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      (p ∈ P → t / (1 + t ^ 2) = a p * Real.exp ((ξ.re + c) * Real.log p)) := by
    intro p
    by_cases hp : p ∈ P
    · have hs0 : 0 ≤ a p * Real.exp ((ξ.re + c) * Real.log p) :=
        mul_nonneg (ha0 p hp) (Real.exp_pos _).le
      obtain ⟨t, ht0, ht1, hts⟩ := exists_div_one_add_sq_eq hs0 (ha p hp)
      exact ⟨t, ht0, ht1, fun _ => hts⟩
    · exact ⟨0, le_rfl, zero_le_one, fun h => absurd h hp⟩
  choose t ht0 ht1 hts using hex
  set z : Nat.Primes → ℂ := fun p =>
    (t p : ℂ) * cexp (((φ + ξ.im * Real.log p : ℝ) : ℂ) * I) with hz
  have hpos := jasBernoulliAggregate_nonneg_of_on h P hP z
  have hfac : ∀ q : XiZeroCopy,
      (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
        ((∏ p ∈ P, (1 + t p ^ 2) : ℝ) : ℂ) *
          ((∏ p ∈ P, jasLogWeightLocal ξ (q.1 : ℂ) (a p) φ p) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
    intro q
    rw [Complex.ofReal_prod, mul_div_assoc', ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    exact jasBernoulliFactor_eq_mul_jasLogWeightLocal ξ q.1 c (a p) φ (t p) p (hts p hp)
  simp_rw [hfac] at hpos
  rw [tsum_mul_left, Complex.re_ofReal_mul] at hpos
  have hprod : 0 < ∏ p ∈ P, (1 + t p ^ 2) := Finset.prod_pos fun p _ => by positivity
  exact (mul_nonneg_iff_of_pos_left hprod).mp hpos

/-- Large-prime positivity gives positivity of the window tests beyond `X`. -/
theorem jasWindowPositivity_of_jasDressedPSDAbove {X : ℕ} {σ : ℝ} (h : JasDressedPSDAbove X σ) :
    JasWindowPositivity σ X := by
  intro n hn ξ a ha0 ha φ
  refine jasLogWeightBernoulli_nonneg_of_on (h _ fun p hp => ?_) ξ _ subset_rfl a ha0 ha φ
  have hp' := (Finset.mem_subtype (p := Nat.Prime) (a := p)).mp hp
  exact lt_of_le_of_lt hn (Finset.mem_Ioc.mp hp').1

/-- **Lower bound.**  Under a half-plane bound below `½`, a chain of off-line zeros forces every
large-prime positivity level to be at least `1 + sup |Re ρ − ½|`. -/
theorem one_add_sSup_le_of_jasDressedPSDAbove_of_chain {alpha σ : ℝ} {X : ℕ}
    (halpha0 : 0 ≤ alpha) (halpha : alpha < 1 / 2) (hXi : XiZeroHalfPlaneBound alpha)
    (h : JasDressedPSDAbove X σ) (hch : JasOffLineChain) :
    1 + sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) ≤ σ :=
  one_add_sSup_le_of_jasWindowPositivity_of_chain halpha0 halpha hXi
    (jasWindowPositivity_of_jasDressedPSDAbove h) hch

/-- The large-prime tail: `Σ_{p ∈ S} p^{−(1+ε)} ≤ (1/ε + 1)/log X` for primes `p > X ≥ 2`. -/
theorem sum_exp_neg_one_add_le_of_gt {S : Finset Nat.Primes} {X : ℕ} (hX : 2 ≤ X)
    (hS : ∀ p ∈ S, X < (p : ℕ)) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∑ p ∈ S, Real.exp (-(1 + ε) * Real.log p) ≤ (1 / ε + 1) / Real.log X := by
  have hlogX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  rw [le_div_iff₀ hlogX, Finset.sum_mul]
  have h := sum_log_mul_exp_neg_le S (s := 1 + ε) (by linarith) (by linarith)
  have hs : 1 / (1 + ε - 1) + 1 = 1 / ε + 1 := by ring_nf
  rw [hs] at h
  refine le_trans (Finset.sum_le_sum fun p hp => ?_) h
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
  exact Real.log_le_log (by exact_mod_cast (show 0 < X by omega)) (by exact_mod_cast (hS p hp).le)

/-- **Upper bound.**  Under `Re ρ ≤ ½ + α`, positivity holds on primes `p > X` at `1 + α + ε`
whenever `log X ≥ 1/ε + 1`. -/
theorem jasDressedPSDAbove_of_xiZeroHalfPlaneBound {alpha ε : ℝ} {X : ℕ} (halpha0 : 0 ≤ alpha)
    (hXi : XiZeroHalfPlaneBound alpha) (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 2 ≤ X)
    (hlog : 1 / ε + 1 ≤ Real.log X) : JasDressedPSDAbove X (1 + alpha + ε) := by
  intro S hS
  have hlogX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have h := jasDressedPSDOn_of_phaseBudget (c := 1 / 2 + alpha + ε) (by positivity) S fun q => by
    have harg := abs_arg_jasWeight_le q
    have hq := abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q
    rw [abs_le] at hq
    have hw : ∑ p ∈ S, jasPhaseWidth (jasR1 ((q.1 : ℂ) + ((1 / 2 + alpha + ε : ℝ) : ℂ)) p)
        (jasR2 ((q.1 : ℂ) - ((1 / 2 + alpha + ε : ℝ) : ℂ)) p) ≤
        ∑ p ∈ S, 8 / 7 * Real.exp (-(1 + ε) * Real.log p) := by
      refine Finset.sum_le_sum fun p hp => jasPhaseWidth_le_of_le (Real.exp_pos _).le ?_
        (Real.exp_pos _).le ?_ ?_
      · rw [jasR1_dressed]; refine Real.exp_le_exp.mpr ?_
        have := log_prime_pos p; nlinarith
      · rw [jasR2_dressed]; refine Real.exp_le_exp.mpr ?_
        have := log_prime_pos p; nlinarith
      · -- `p ≥ 3`, so `p^{−(1+ε)} ≤ 1/3`
        have hp3 : (3 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast (show 3 ≤ (p : ℕ) by
          have := hS p hp; omega)
        have hle : Real.exp (-(1 + ε) * Real.log p) ≤ 1 / 3 := by
          have h3 : Real.exp (-Real.log 3) = 1 / 3 := by
            rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
          rw [← h3]
          refine Real.exp_le_exp.mpr ?_
          have hl : Real.log 3 ≤ Real.log p := Real.log_le_log (by norm_num) hp3
          have hl0 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
          nlinarith
        have h0 := (Real.exp_pos (-(1 + ε) * Real.log p)).le
        nlinarith
    rw [← Finset.mul_sum] at hw
    have htail := sum_exp_neg_one_add_le_of_gt hX hS hε hε1
    have hdiv : (1 / ε + 1) / Real.log X ≤ 1 := by rw [div_le_one hlogX]; exact hlog
    have hpi := Real.pi_gt_d2
    nlinarith
  have he : (1 / 2 + (1 / 2 + alpha + ε) : ℝ) = 1 + alpha + ε := by ring
  rwa [he] at h

/-- **Unconditional large-prime positivity above `3/2`.** -/
theorem exists_jasDressedPSDAbove_three_halves_add {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ X : ℕ, JasDressedPSDAbove X (3 / 2 + ε) := by
  have hXi : XiZeroHalfPlaneBound (1 / 2) := fun ρ hρ => by
    have := (xi_zero_re_mem_open_unit hρ).2
    linarith
  obtain ⟨X, hX⟩ := exists_nat_gt (Real.exp (1 / ε + 1))
  have h := jasDressedPSDAbove_of_xiZeroHalfPlaneBound (X := X + 2) (by norm_num) hXi hε hε1
    (by omega) (le_of_lt (Real.lt_log_iff_exp_lt (by positivity) |>.mpr (by push_cast; linarith)))
  exact ⟨X + 2, by rwa [show (1 + 1 / 2 + ε : ℝ) = 3 / 2 + ε by ring] at h⟩

/-- **The large-prime abscissa of a chain is `1 + δ*`.**  Under a half-plane bound below `½`, if
the off-line zeros form a chain, then (i) positivity above any `X` forces `σ ≥ 1 + δ*`, and
(ii) for every `0 < ε ≤ 1` positivity holds above some `X` at `1 + δ* + ε`. -/
theorem largePrime_abscissa_eq_of_chain {alpha : ℝ} (halpha0 : 0 ≤ alpha) (halpha : alpha < 1 / 2)
    (hXi : XiZeroHalfPlaneBound alpha) (hch : JasOffLineChain) :
    (∀ (X : ℕ) (σ : ℝ), JasDressedPSDAbove X σ →
        1 + sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) ≤ σ) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ X : ℕ, JasDressedPSDAbove X
        (1 + sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) + ε) := by
  refine ⟨fun X σ h => one_add_sSup_le_of_jasDressedPSDAbove_of_chain halpha0 halpha hXi h hch,
    fun ε hε hε1 => ?_⟩
  have hbdd : BddAbove (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    ⟨alpha, by rintro _ ⟨q, rfl⟩; exact abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q⟩
  obtain ⟨q₁, _⟩ := hch.1
  have hS0 : 0 ≤ sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    le_trans (abs_nonneg _) (le_csSup hbdd ⟨q₁, rfl⟩)
  have hXiS : XiZeroHalfPlaneBound
      (sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|)) := by
    intro ρ hρ
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have h := le_csSup hbdd ⟨q, rfl⟩
    simp only at h
    have := le_abs_self ((q.1 : ℂ).re - 1 / 2)
    linarith
  obtain ⟨X, hX⟩ := exists_nat_gt (Real.exp (1 / ε + 1))
  exact ⟨X + 2, jasDressedPSDAbove_of_xiZeroHalfPlaneBound hS0 hXiS hε hε1 (by omega)
    (le_of_lt (Real.lt_log_iff_exp_lt (by positivity) |>.mpr (by push_cast; linarith)))⟩

end

end RHTower
