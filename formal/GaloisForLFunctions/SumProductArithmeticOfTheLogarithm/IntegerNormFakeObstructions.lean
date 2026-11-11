import GaloisForLFunctions.SumProductArithmeticOfTheLogarithm.LogarithmicCountFloor
import GaloisForLFunctions.RHTower.BeurlingSystemMellin
import GaloisForLFunctions.RHTower.BeurlingDeletionSystemCount
import GaloisForLFunctions.RHTower.LandauSummabilityTransfer
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionUnrestricted
import GaloisForLFunctions.RHTower.Sieve.InvZetaRegular
import GaloisForLFunctions.RHTower.DirichletCharacterPartialSumBound
import GaloisForLFunctions.RHTower.SiegelTheoremAux

/-!
# Integer-norm Beurling fakes: definition, obstructions, and the `1/2` calibration

A discrete Beurling system `B` with integer norms (`HasIntegerNorms B`) other than the rational
primes (`NotNormEquivPrimes B`) is an **integer-norm fake at exponent `β`**
(`IsIntegerNormFakeAt B β`) when its generalized-integer count satisfies
`N_B(x) = A x + O(x^β)` (`A ≥ 0`) and `(s − 1) ζ_B(s)` extends holomorphically across
`Re s > 1/2` with a zero at some `ρ₀ ≠ 1` (`Re ρ₀ > 1/2`) where `ζ(ρ₀) ≠ 0`.

This module establishes the foundational unconditionally forced obstructions and the `β = 1/2`
Dirichlet-character calibration:

* **Sublogarithmic & finite-omission obstructions.**
  - Every discrete integer-norm system with `B.HasLinearCounting C₁` that omits only finitely many
    rational primes from `B.labelNorm` has `(s − 1) ζ_B(s)` nonvanishing off the zeros of `ζ(s)` on
    all of `{Re s > 1/2} \ {1}` (`no_fake_zero_of_finite_missing_primes`), by factoring out the
    kept primes and transferring positivity of the residual Dirichlet series across `(1/2, ∞)` via
    Landau's theorem and the zero-free strip `|Im s| < 4` of `ζ`.
  - Consequently **every** integer-norm fake at any exponent `β ≤ 1` omits infinitely many rational
    primes (`infinite_missing_primes_of_integerNormFakeAt`): neither pure generator additions on top
    of `ℙ` (`not_isIntegerNormFakeAt_of_surjective_primes`) nor finite prime deletions
    (`not_isIntegerNormFakeAt_keptPrimeSystem_of_finite`, despite `O(1)` count remainder) can ever
    produce a fake.
* **Zero-density obstruction at `β ≤ 1/2`.**
  - Any fake at exponent `β ≤ 1/2` necessarily has strictly positive density `A > 0`
    (`pos_density_of_integerNormFakeAt_le_half`), since `A = 0` forces `N_B(x) = O(x^{1/2})` and
    hence absolute convergence and Euler-inversion nonvanishing of `ζ_B` on `Re s > 1/2`.
* **Kept-prime systems and Rankin floor law.**
  - For any set `S` of primes with `∑_{p ∈ S} p^{−β} < ∞` (`0 < β ≤ 1`), the kept-prime system
    `keptPrimeSystem S` (`ℙ \ S`) satisfies `|N_B(x) − A x| ≤ 2 exp(∑_{p ∈ S} p^{−β}) x^β`
    (`keptPrimeSystem_count_sub_le_of_summable`).
* **Quadratic `L`-function model at `β = 1/2`.**
  - For any nontrivial quadratic Dirichlet character `χ` (`χ^2 = 1`, `χ ≠ 1`), the Euler-factor
    Beurling system `quadraticCharacterSystem χ` has integer norms, `N(x) = L(1, χ) x + O(x^{1/2})`,
    and `(s − 1) ζ_B(s) = ζ_u(s) L(s, χ)`, yielding an integer-norm fake at `β = 1/2` from any
    off-line zero of `L(s, χ)` not shared with `ζ(s)`
    (`isIntegerNormFakeAt_half_of_quadratic_LFunction_zero`).
-/

open Complex Finset Filter Topology
open RHTower RHTower.Sieve RHTower.BeurlingDeletion
open GaloisForLFunctions.RigidArithmeticOfCuts

noncomputable section

namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

/-! ## 1. Definition of integer-norm Beurling fakes -/

/-- `B` is not norm-equivalent to the classical system of rational primes. -/
def NotNormEquivPrimes (B : BeurlingSystem) : Prop :=
  ¬ Nonempty {e : B.Label ≃ {p : ℕ // p.Prime} //
    ∀ l, B.labelNorm l = ((e l : ℕ) : ℝ)}

/-- `B` is a discrete integer-norm Beurling fake with integer-count remainder `O(x^β)`:
`B` has integer norms, is discrete, is not the rational primes, satisfies
`|N_B(x) − A x| ≤ C x^β` (`A ≥ 0`) for `x ≥ 1`, and `(s − 1) ζ_B(s)` admits a holomorphic
continuation `G` to `{Re s > 1/2}` that vanishes at some `ρ₀ ≠ 1` in `{Re s > 1/2}` where
`ζ(ρ₀) ≠ 0`. -/
def IsIntegerNormFakeAt (B : BeurlingSystem) (β : ℝ) : Prop :=
  HasIntegerNorms B ∧
    B.IsDiscrete ∧
    NotNormEquivPrimes B ∧
    (∃ A C : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β) ∧
    ∃ G : ℂ → ℂ,
      DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re → G s = (s - 1) * B.zetaSeriesC s) ∧
      ∃ ρ₀ : ℂ, 1 / 2 < ρ₀.re ∧ ρ₀ ≠ 1 ∧ G ρ₀ = 0 ∧ riemannZeta ρ₀ ≠ 0

/-- The set of remainder exponents `β : ℝ` realized by integer-norm Beurling fakes. -/
def integerNormFakeExponents : Set ℝ :=
  {β : ℝ | ∃ B : BeurlingSystem, IsIntegerNormFakeAt B β}

theorem IsIntegerNormFakeAt.mono {B : BeurlingSystem} {β₁ β₂ : ℝ}
    (h : IsIntegerNormFakeAt B β₁) (h12 : β₁ ≤ β₂) : IsIntegerNormFakeAt B β₂ := by
  obtain ⟨hInt, hDisc, hNotP, ⟨A, C, hA, hC⟩, hG⟩ := h
  refine ⟨hInt, hDisc, hNotP, ⟨A, max C 0, hA, fun x hx => ?_⟩, hG⟩
  calc |(B.countBall x : ℝ) - A * x|
      ≤ C * x ^ β₁ := hC x hx
    _ ≤ max C 0 * x ^ β₁ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
    _ ≤ max C 0 * x ^ β₂ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx h12) (le_max_right _ _)

/-- A count asymptotic `N(x) = A x + O(x^β)` with `β < 1` uniquely determines the density `A`. -/
theorem density_unique_of_lt_one {B : BeurlingSystem} {A₁ C₁ β₁ A₂ C₂ β₂ : ℝ}
    (hβ₁ : β₁ < 1) (hβ₂ : β₂ < 1)
    (h₁ : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A₁ * x| ≤ C₁ * x ^ β₁)
    (h₂ : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A₂ * x| ≤ C₂ * x ^ β₂) :
    A₁ = A₂ := by
  have hle : ∀ x : ℝ, 1 ≤ x →
      |A₁ - A₂| ≤ max C₁ 0 * x ^ (β₁ - 1) + max C₂ 0 * x ^ (β₂ - 1) := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hdiff : |(A₁ - A₂) * x| ≤ max C₁ 0 * x ^ β₁ + max C₂ 0 * x ^ β₂ := by
      have e : (A₁ - A₂) * x =
          ((B.countBall x : ℝ) - A₂ * x) - ((B.countBall x : ℝ) - A₁ * x) := by ring
      rw [e]
      calc _ ≤ |(B.countBall x : ℝ) - A₂ * x| + |(B.countBall x : ℝ) - A₁ * x| := abs_sub _ _
        _ ≤ C₂ * x ^ β₂ + C₁ * x ^ β₁ := add_le_add (h₂ x hx) (h₁ x hx)
        _ ≤ max C₁ 0 * x ^ β₁ + max C₂ 0 * x ^ β₂ := by
            have p1 : 0 ≤ x ^ β₁ := Real.rpow_nonneg hx0.le _
            have p2 : 0 ≤ x ^ β₂ := Real.rpow_nonneg hx0.le _
            nlinarith [le_max_left C₁ 0, le_max_left C₂ 0]
    rw [abs_mul, abs_of_pos hx0] at hdiff
    rw [Real.rpow_sub hx0, Real.rpow_sub hx0, Real.rpow_one]
    calc |A₁ - A₂| ≤ (max C₁ 0 * x ^ β₁ + max C₂ 0 * x ^ β₂) / x :=
          (le_div_iff₀ hx0).mpr hdiff
      _ = _ := by ring
  have hlim : Tendsto (fun x : ℝ => max C₁ 0 * x ^ (β₁ - 1) + max C₂ 0 * x ^ (β₂ - 1))
      atTop (𝓝 0) := by
    have t1 : Tendsto (fun x : ℝ => x ^ (β₁ - 1)) atTop (𝓝 0) := by
      simpa [neg_sub] using tendsto_rpow_neg_atTop (y := 1 - β₁) (by linarith)
    have t2 : Tendsto (fun x : ℝ => x ^ (β₂ - 1)) atTop (𝓝 0) := by
      simpa [neg_sub] using tendsto_rpow_neg_atTop (y := 1 - β₂) (by linarith)
    simpa using (t1.const_mul (max C₁ 0)).add (t2.const_mul (max C₂ 0))
  have h0 : |A₁ - A₂| ≤ 0 :=
    ge_of_tendsto hlim ((eventually_ge_atTop (1 : ℝ)).mono fun x hx => hle x hx)
  exact sub_eq_zero.mp (abs_nonpos_iff.mp h0)

/-- Any `O(x^β)` remainder bound with `β ≤ 1` implies `BeurlingSystem.HasLinearCounting`. -/
theorem hasLinearCounting_of_count_sub_le {B : BeurlingSystem} {A C β : ℝ} (hβ : β ≤ 1)
    (hC : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    B.HasLinearCounting (|A| + max C 0) := by
  intro x hx
  have h1 := (le_abs_self _).trans (hC x hx)
  have h2 : C * x ^ β ≤ max C 0 * x := by
    calc C * x ^ β ≤ max C 0 * x ^ β :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
      _ ≤ max C 0 * x ^ (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx hβ) (le_max_right _ _)
      _ = max C 0 * x := by rw [Real.rpow_one]
  have h3 : A * x ≤ |A| * x := mul_le_mul_of_nonneg_right (le_abs_self A) (by linarith)
  linarith

/-! ## 2. Dyadic convergence, Euler inversion, and the zero-density obstruction -/

/-- Dyadic-block summability of `|g|^{−s}` under a power counting bound `N(X) ≤ C X^θ` (`θ ≥ 0`). -/
theorem summable_intNorm_rpow_of_countBall_le {B : BeurlingSystem} (hdisc : B.IsDiscrete)
    {C θ : ℝ} (hθ0 : 0 ≤ θ) (hC : ∀ X : ℝ, 1 ≤ X → (B.countBall X : ℝ) ≤ C * X ^ θ)
    {s : ℝ} (hs : θ < s) :
    Summable fun g : Multiset B.Label => (B.intNorm g) ^ (-s) := by
  classical
  have hC0 : 0 ≤ C := by
    have h1 := hC 1 le_rfl
    rw [Real.one_rpow, mul_one] at h1
    exact le_trans (Nat.cast_nonneg _) h1
  set r : ℝ := (2 : ℝ) ^ (θ - s) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hgeom : Summable fun k : ℕ => (2 : ℝ) ^ θ * C * r ^ k :=
    (summable_geometric_of_lt_one hr0.le hr1).mul_left _
  refine summable_of_sum_le (c := ∑' k : ℕ, (2 : ℝ) ^ θ * C * r ^ k)
    (fun g => Real.rpow_nonneg (B.intNorm_pos g).le _) fun S => ?_
  have hmaps : ∀ g ∈ S, B.dyadicIndex g ∈ S.image B.dyadicIndex :=
    fun g hg => Finset.mem_image_of_mem _ hg
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hblock : ∀ k ∈ S.image B.dyadicIndex,
      ∑ g ∈ S with B.dyadicIndex g = k, (B.intNorm g) ^ (-s) ≤ (2 : ℝ) ^ θ * C * r ^ k := by
    intro k _
    have hterm : ∀ g ∈ S.filter (fun g => B.dyadicIndex g = k),
        (B.intNorm g) ^ (-s) ≤ ((2 : ℝ) ^ k) ^ (-s) := by
      intro g hg
      have hgk : B.dyadicIndex g = k := (Finset.mem_filter.mp hg).2
      have hle : (2 : ℝ) ^ k ≤ B.intNorm g := hgk ▸ B.two_pow_dyadicIndex_le g
      exact Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
    have hfin := hdisc ((2 : ℝ) ^ (k + 1))
    have hcards : (S.filter fun g => B.dyadicIndex g = k).card ≤
        B.countBall ((2 : ℝ) ^ (k + 1)) := by
      rw [BeurlingSystem.countBall, Set.ncard_eq_toFinset_card _ hfin]
      refine Finset.card_le_card fun g hg => ?_
      rw [Set.Finite.mem_toFinset]
      have hgk := (Finset.mem_filter.mp hg).2
      exact (hgk ▸ B.intNorm_lt_two_pow_succ g).le
    have hcount : ((S.filter fun g => B.dyadicIndex g = k).card : ℝ) ≤
        C * ((2 : ℝ) ^ (k + 1)) ^ θ := by
      calc ((S.filter fun g => B.dyadicIndex g = k).card : ℝ)
          ≤ (B.countBall ((2 : ℝ) ^ (k + 1)) : ℝ) := by exact_mod_cast hcards
        _ ≤ C * ((2 : ℝ) ^ (k + 1)) ^ θ := hC _ (one_le_pow₀ (by norm_num))
    calc ∑ g ∈ S with B.dyadicIndex g = k, (B.intNorm g) ^ (-s)
        ≤ ∑ g ∈ S with B.dyadicIndex g = k, ((2 : ℝ) ^ k) ^ (-s) := Finset.sum_le_sum hterm
      _ = ((S.filter fun g => B.dyadicIndex g = k).card : ℝ) * ((2 : ℝ) ^ k) ^ (-s) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (C * ((2 : ℝ) ^ (k + 1)) ^ θ) * ((2 : ℝ) ^ k) ^ (-s) :=
          mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = (2 : ℝ) ^ θ * C * r ^ k := by
          rw [hr, ← Real.rpow_natCast r k, ← Real.rpow_mul (by norm_num),
            ← Real.rpow_natCast (2 : ℝ) (k + 1), ← Real.rpow_mul (by norm_num),
            ← Real.rpow_natCast (2 : ℝ) k, ← Real.rpow_mul (by norm_num)]
          have e : C * (2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * θ) * (2 : ℝ) ^ ((k : ℝ) * (-s)) =
              C * ((2 : ℝ) ^ (((k + 1 : ℕ) : ℝ) * θ) * (2 : ℝ) ^ ((k : ℝ) * (-s))) := by ring
          rw [e, ← Real.rpow_add (by norm_num),
            show ((k + 1 : ℕ) : ℝ) * θ + (k : ℝ) * (-s) = θ + (θ - s) * (k : ℝ) by
              push_cast; ring,
            Real.rpow_add (by norm_num)]
          ring
  calc ∑ k ∈ S.image B.dyadicIndex, ∑ g ∈ S with B.dyadicIndex g = k, (B.intNorm g) ^ (-s)
      ≤ ∑ k ∈ S.image B.dyadicIndex, (2 : ℝ) ^ θ * C * r ^ k := Finset.sum_le_sum hblock
    _ ≤ ∑' k : ℕ, (2 : ℝ) ^ θ * C * r ^ k :=
        hgeom.sum_le_tsum _ fun k _ => by positivity

/-- Dirichlet inversion `μ_B(s) ζ_B(s) = 1` holds at every `s` where `∑_g |g|^{−Re s} < ∞`. -/
theorem moebiusSeriesC_mul_zetaSeriesC_of_summable {B : BeurlingSystem} (hdisc : B.IsDiscrete)
    {s : ℂ} (hZr : Summable fun g : Multiset B.Label => (B.intNorm g) ^ (-s.re)) :
    B.moebiusSeriesC s * B.zetaSeriesC s = 1 := by
  classical
  haveI := B.countable_of_isDiscrete hdisc
  have hZ : Summable fun g : Multiset B.Label => ((B.intNorm g : ℝ) : ℂ) ^ (-s) :=
    Summable.of_norm (hZr.congr fun g => (B.norm_intNorm_cpow g s).symm)
  have hM : Summable fun g : Multiset B.Label =>
      (B.moebius g : ℂ) * ((B.intNorm g : ℝ) : ℂ) ^ (-s) := by
    refine Summable.of_norm_bounded hZr fun g => ?_
    rw [norm_mul, B.norm_intNorm_cpow]
    have hnorm : ‖(B.moebius g : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast B.abs_moebius_le_one g
    exact mul_le_of_le_one_left (Real.rpow_nonneg (B.intNorm_pos g).le _) hnorm
  set F : (Multiset B.Label) × (Multiset B.Label) → ℂ := fun p =>
    ((B.moebius p.1 : ℂ) * ((B.intNorm p.1 : ℝ) : ℂ) ^ (-s)) *
      (((B.intNorm p.2 : ℝ) : ℂ) ^ (-s)) with hF
  have hprod : Summable fun p : (Multiset B.Label) × (Multiset B.Label) =>
      (B.intNorm p.1) ^ (-s.re) * (B.intNorm p.2) ^ (-s.re) :=
    hZr.mul_of_nonneg hZr (fun g => Real.rpow_nonneg (B.intNorm_pos g).le _)
      (fun g => Real.rpow_nonneg (B.intNorm_pos g).le _)
  have hFsum : Summable F := by
    refine Summable.of_norm_bounded hprod fun p => ?_
    have hnorm : ‖(B.moebius p.1 : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast B.abs_moebius_le_one p.1
    rw [hF, norm_mul, norm_mul, B.norm_intNorm_cpow, B.norm_intNorm_cpow]
    calc ‖(B.moebius p.1 : ℂ)‖ * (B.intNorm p.1) ^ (-s.re) * (B.intNorm p.2) ^ (-s.re)
        ≤ 1 * (B.intNorm p.1) ^ (-s.re) * (B.intNorm p.2) ^ (-s.re) := by gcongr
      _ = _ := one_mul _
  rw [BeurlingSystem.moebiusSeriesC, BeurlingSystem.zetaSeriesC, hM.tsum_mul_tsum hZ hFsum]
  set e := Equiv.sigmaFiberEquiv fun p : (Multiset B.Label) × (Multiset B.Label) => p.1 + p.2
  have hsigma : Summable (F ∘ e) := e.summable_iff.mpr hFsum
  rw [(e.tsum_eq F).symm, hsigma.tsum_sigma]
  have hfibre : ∀ n : Multiset B.Label,
      (∑' c : {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n},
        F (c : (Multiset B.Label) × (Multiset B.Label)))
        = (if n = 0 then (1 : ℂ) else 0) := by
    intro n
    letI : Fintype {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n} :=
      Fintype.ofEquiv _ (BeurlingSystem.divisorPairEquiv n).symm
    rw [tsum_fintype]
    have hval : ∀ c : {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n},
        F (c : (Multiset B.Label) × (Multiset B.Label)) =
          (B.moebius ((c : (Multiset B.Label) × (Multiset B.Label)).1) : ℂ) *
            ((B.intNorm n : ℝ) : ℂ) ^ (-s) := by
      rintro ⟨⟨d, g⟩, hdg⟩
      rw [hF]
      simp only
      rw [mul_assoc, ← Complex.mul_cpow_ofReal_nonneg (B.intNorm_pos d).le (B.intNorm_pos g).le,
        ← Complex.ofReal_mul, ← B.intNorm_add, hdg]
    rw [Finset.sum_congr rfl fun c _ => hval c, ← Finset.sum_mul]
    have hsum : ∑ c : {p : (Multiset B.Label) × (Multiset B.Label) // p.1 + p.2 = n},
        (B.moebius ((c : (Multiset B.Label) × (Multiset B.Label)).1) : ℂ) =
        ((∑ d ∈ n.powerset.toFinset, B.moebius d : ℤ) : ℂ) := by
      push_cast
      rw [← Finset.sum_coe_sort n.powerset.toFinset (fun d => (B.moebius d : ℂ))]
      exact Fintype.sum_equiv (BeurlingSystem.divisorPairEquiv n) _ _ fun _ => rfl
    rw [hsum, B.sum_moebius_divisors n]
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn, hn, B.intNorm_zero]; norm_num
    · rw [if_neg hn, if_neg hn]; norm_num
  rw [tsum_congr hfibre, tsum_eq_single 0 (fun n hn => if_neg hn), if_pos rfl]

theorem zetaSeriesC_ne_zero_of_summable {B : BeurlingSystem} (hdisc : B.IsDiscrete) {s : ℂ}
    (hZr : Summable fun g : Multiset B.Label => (B.intNorm g) ^ (-s.re)) :
    B.zetaSeriesC s ≠ 0 := by
  intro h0
  have h := moebiusSeriesC_mul_zetaSeriesC_of_summable hdisc hZr
  rw [h0, mul_zero] at h
  exact zero_ne_one h

/-! ### Integer-norm fiber multiplicity and LSeries representation -/

/-- Natural-number norm of a prime label in an integer-norm Beurling system. -/
def natLabelNorm {B : BeurlingSystem} (h : HasIntegerNorms B) (l : B.Label) : ℕ :=
  Classical.choose (h l)

theorem natLabelNorm_spec {B : BeurlingSystem} (h : HasIntegerNorms B) (l : B.Label) :
    ((natLabelNorm h l : ℕ) : ℝ) = B.labelNorm l :=
  (Classical.choose_spec (h l)).symm

theorem two_le_natLabelNorm {B : BeurlingSystem} (h : HasIntegerNorms B) (l : B.Label) :
    2 ≤ natLabelNorm h l := by
  have h1 := B.one_lt_labelNorm l
  rw [← natLabelNorm_spec h l] at h1
  exact_mod_cast h1

/-- Natural-number norm of a generalized integer in an integer-norm Beurling system. -/
def natIntNorm {B : BeurlingSystem} (h : HasIntegerNorms B) (g : B.Integer) : ℕ :=
  (g.map (natLabelNorm h)).prod

theorem natIntNorm_spec {B : BeurlingSystem} (h : HasIntegerNorms B) (g : B.Integer) :
    ((natIntNorm h g : ℕ) : ℝ) = B.intNorm g := by
  induction g using Multiset.induction_on with
  | empty => simp [natIntNorm]
  | cons l g ih =>
    rw [natIntNorm, Multiset.map_cons, Multiset.prod_cons, Nat.cast_mul,
      ← Multiset.singleton_add, B.intNorm_add, B.intNorm_singleton, natLabelNorm_spec h l, ih]
    rfl

theorem one_le_natIntNorm {B : BeurlingSystem} (h : HasIntegerNorms B) (g : B.Integer) :
    1 ≤ natIntNorm h g := by
  have h1 := B.one_le_intNorm g
  rw [← natIntNorm_spec h g] at h1
  exact_mod_cast h1

theorem finite_fiber_natIntNorm {B : BeurlingSystem} (h : HasIntegerNorms B)
    (hdisc : B.IsDiscrete) (n : ℕ) :
    {g : B.Integer | natIntNorm h g = n}.Finite := by
  refine (hdisc (n : ℝ)).subset fun g hg => ?_
  rw [Set.mem_setOf_eq, ← natIntNorm_spec h g, hg]

/-- Number of generalized integers of `B` with norm `n`. -/
def intCount (B : BeurlingSystem) (h : HasIntegerNorms B) (n : ℕ) : ℕ :=
  Set.ncard {g : B.Integer | natIntNorm h g = n}

theorem intCount_zero {B : BeurlingSystem} (h : HasIntegerNorms B) :
    intCount B h 0 = 0 := by
  have hempty : {g : B.Integer | natIntNorm h g = 0} = ∅ := by
    ext g
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    have := one_le_natIntNorm h g
    omega
  rw [intCount, hempty, Set.ncard_empty]

theorem countBall_eq_sum_intCount {B : BeurlingSystem} (h : HasIntegerNorms B)
    (hdisc : B.IsDiscrete) {X : ℝ} (hX : 0 ≤ X) :
    B.countBall X = ∑ n ∈ Finset.Iic ⌊X⌋₊, intCount B h n := by
  classical
  set S := (hdisc X).toFinset
  have hcard : B.countBall X = S.card :=
    Set.ncard_eq_toFinset_card _ (hdisc X)
  rw [hcard]
  have hmaps : ∀ g ∈ S, natIntNorm h g ∈ Finset.Iic ⌊X⌋₊ := by
    intro g hg
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, ← natIntNorm_spec h g] at hg
    exact Finset.mem_Iic.mpr (Nat.le_floor hg)
  rw [← Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [intCount, Set.ncard_eq_toFinset_card _ (finite_fiber_natIntNorm h hdisc n)]
  congr 1
  ext g
  simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  constructor
  · exact fun hg => hg.2
  · intro hgn
    refine ⟨?_, hgn⟩
    rw [← natIntNorm_spec h g, hgn]
    exact (Nat.floor_le hX).trans' (by exact_mod_cast Finset.mem_Iic.mp hn)

/-- Whenever `∑_g |g|^{−Re s}` converges, `B.zetaSeriesC s` equals `LSeries (intCount B h) s`
and that `LSeries` is summable at `s`. -/
theorem zetaSeriesC_eq_LSeries_of_summable {B : BeurlingSystem} (h : HasIntegerNorms B)
    (hdisc : B.IsDiscrete) {s : ℂ}
    (hZr : Summable fun g : Multiset B.Label => (B.intNorm g) ^ (-s.re)) :
    LSeriesSummable (fun n => (intCount B h n : ℂ)) s ∧
      B.zetaSeriesC s = LSeries (fun n => (intCount B h n : ℂ)) s := by
  classical
  haveI := B.countable_of_isDiscrete hdisc
  set e := Equiv.sigmaFiberEquiv (natIntNorm h)
  have hZ : Summable fun g : Multiset B.Label => ((B.intNorm g : ℝ) : ℂ) ^ (-s) :=
    Summable.of_norm (hZr.congr fun g => (B.norm_intNorm_cpow g s).symm)
  have hsigmaR : Summable ((fun g : Multiset B.Label => (B.intNorm g) ^ (-s.re)) ∘ e) :=
    e.summable_iff.mpr hZr
  have hsigmaC : Summable ((fun g : Multiset B.Label => ((B.intNorm g : ℝ) : ℂ) ^ (-s)) ∘ e) :=
    e.summable_iff.mpr hZ
  have hfibR : ∀ n : ℕ,
      (∑' c : {g : B.Integer // natIntNorm h g = n}, (B.intNorm c.1) ^ (-s.re)) =
        (intCount B h n : ℝ) * (n : ℝ) ^ (-s.re) := by
    intro n
    letI : Fintype {g : B.Integer // natIntNorm h g = n} :=
      (finite_fiber_natIntNorm h hdisc n).fintype
    rw [tsum_fintype]
    have hval : ∀ c : {g : B.Integer // natIntNorm h g = n},
        (B.intNorm c.1) ^ (-s.re) = (n : ℝ) ^ (-s.re) := fun c => by
      rw [← natIntNorm_spec h c.1, c.2]
    simp_rw [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [intCount, Set.ncard_eq_toFinset_card _ (finite_fiber_natIntNorm h hdisc n)]
    congr 2
    exact Set.Finite.card_toFinset _
  have hfibC : ∀ n : ℕ,
      (∑' c : {g : B.Integer // natIntNorm h g = n}, ((B.intNorm c.1 : ℝ) : ℂ) ^ (-s)) =
        LSeries.term (fun m => (intCount B h m : ℂ)) s n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero]
      haveI : IsEmpty {g : B.Integer // natIntNorm h g = 0} :=
        ⟨fun c => absurd c.2 (one_le_natIntNorm h c.1).ne'⟩
      simp
    · letI : Fintype {g : B.Integer // natIntNorm h g = n} :=
        (finite_fiber_natIntNorm h hdisc n).fintype
      rw [tsum_fintype, LSeries.term_of_ne_zero hn]
      have hval : ∀ c : {g : B.Integer // natIntNorm h g = n},
          ((B.intNorm c.1 : ℝ) : ℂ) ^ (-s) = (n : ℂ) ^ (-s) := fun c => by
        rw [← natIntNorm_spec h c.1, c.2, Nat.cast_id]; push_cast; rfl
      simp_rw [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [intCount, Set.ncard_eq_toFinset_card _ (finite_fiber_natIntNorm h hdisc n),
        Set.Finite.card_toFinset, Complex.cpow_neg, div_eq_mul_inv]
  have hcolsR : Summable fun n : ℕ => (intCount B h n : ℝ) * (n : ℝ) ^ (-s.re) :=
    (hsigmaR.sigma).congr hfibR
  have hLS : LSeriesSummable (fun n => (intCount B h n : ℂ)) s := by
    refine Summable.of_norm_bounded hcolsR fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero, norm_zero, intCount_zero, Nat.cast_zero, zero_mul]
    · rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Real.rpow_neg (Nat.cast_nonneg _),
        div_eq_mul_inv]
  refine ⟨hLS, ?_⟩
  rw [BeurlingSystem.zetaSeriesC, (e.tsum_eq _).symm, hsigmaC.tsum_sigma]
  exact tsum_congr hfibC

/-- Converse fiber regrouping: `LSeriesSummable (intCount B h) (σ : ℂ)` implies
`Summable fun g => (B.intNorm g) ^ (-σ)`. -/
theorem summable_intNorm_rpow_of_lseriesSummable {B : BeurlingSystem} (h : HasIntegerNorms B)
    (hdisc : B.IsDiscrete) {σ : ℝ}
    (hLS : LSeriesSummable (fun n => (intCount B h n : ℂ)) (σ : ℂ)) :
    Summable fun g : Multiset B.Label => (B.intNorm g) ^ (-σ) := by
  classical
  set e := Equiv.sigmaFiberEquiv (natIntNorm h)
  rw [← e.summable_iff]
  have hnn : ∀ x : Σ n : ℕ, {g : B.Integer // natIntNorm h g = n},
      0 ≤ (B.intNorm (e x)) ^ (-σ) := fun x => Real.rpow_nonneg (B.intNorm_pos _).le _
  refine (summable_sigma_of_nonneg hnn).mpr ⟨fun n => ?_, ?_⟩
  · letI : Fintype {g : B.Integer // natIntNorm h g = n} :=
      (finite_fiber_natIntNorm h hdisc n).fintype
    exact summable_fintype _
  · refine (hLS.norm).congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero, norm_zero]
      haveI : IsEmpty {g : B.Integer // natIntNorm h g = 0} :=
        ⟨fun c => absurd c.2 (one_le_natIntNorm h c.1).ne'⟩
      simp
    · letI : Fintype {g : B.Integer // natIntNorm h g = n} :=
        (finite_fiber_natIntNorm h hdisc n).fintype
      rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.ofReal_re, tsum_fintype]
      have hval : ∀ c : {g : B.Integer // natIntNorm h g = n},
          (B.intNorm (e ⟨n, c⟩)) ^ (-σ) = (n : ℝ) ^ (-σ) := fun c => by
        change (B.intNorm c.1) ^ (-σ) = (n : ℝ) ^ (-σ)
        rw [← natIntNorm_spec h c.1, c.2]
      simp_rw [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [intCount, Set.ncard_eq_toFinset_card _ (finite_fiber_natIntNorm h hdisc n),
        Set.Finite.card_toFinset, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

/-- When `intCount B h` is `LSeriesSummable` at every `σ > 1/2`, `B.zetaSeriesC` is holomorphic and
nonvanishing on `{Re s > 1/2}`. -/
theorem differentiableOn_and_ne_zero_zetaSeriesC_of_half {B : BeurlingSystem}
    (h : HasIntegerNorms B) (hdisc : B.IsDiscrete)
    (hsum : ∀ σ : ℝ, 1 / 2 < σ → LSeriesSummable (fun n => (intCount B h n : ℂ)) (σ : ℂ)) :
    DifferentiableOn ℂ B.zetaSeriesC {s : ℂ | 1 / 2 < s.re} ∧
      ∀ s : ℂ, 1 / 2 < s.re → B.zetaSeriesC s ≠ 0 := by
  have habs : LSeries.abscissaOfAbsConv (fun n => (intCount B h n : ℂ)) ≤ ((1 / 2 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun σ hσ =>
      hsum σ (by exact_mod_cast hσ)
  have hZr : ∀ s : ℂ, 1 / 2 < s.re →
      Summable fun g : Multiset B.Label => (B.intNorm g) ^ (-s.re) := fun s hs =>
    summable_intNorm_rpow_of_lseriesSummable h hdisc (hsum s.re hs)
  have heq : Set.EqOn (LSeries (fun n => (intCount B h n : ℂ))) B.zetaSeriesC
      {s : ℂ | 1 / 2 < s.re} := fun s hs =>
    (zetaSeriesC_eq_LSeries_of_summable h hdisc (hZr s hs)).2.symm
  have hdiffL : DifferentiableOn ℂ (LSeries (fun n => (intCount B h n : ℂ)))
      {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    have hslt : LSeries.abscissaOfAbsConv (fun n => (intCount B h n : ℂ)) < s.re :=
      lt_of_le_of_lt habs (by exact_mod_cast hs)
    exact (LSeries.differentiableAt_of_abscissaOfAbsConv_lt_re hslt).differentiableWithinAt
  exact ⟨hdiffL.congr heq, fun s hs => zetaSeriesC_ne_zero_of_summable hdisc (hZr s hs)⟩

/-- Identity theorem on the open half-plane `{Re s > 1/2}`: two holomorphic functions agreeing on
`{Re s > 1}` agree on all of `{Re s > 1/2}`. -/
theorem eqOn_halfPlane_of_eq_on_one {F₁ F₂ : ℂ → ℂ}
    (h₁ : DifferentiableOn ℂ F₁ {s : ℂ | 1 / 2 < s.re})
    (h₂ : DifferentiableOn ℂ F₂ {s : ℂ | 1 / 2 < s.re})
    (heq : ∀ s : ℂ, 1 < s.re → F₁ s = F₂ s) :
    Set.EqOn F₁ F₂ {s : ℂ | 1 / 2 < s.re} := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconn : IsPreconnected {s : ℂ | 1 / 2 < s.re} :=
    (convex_halfSpace_gt (fun s : ℂ => s.re) (isLinearMap_re) (1 / 2)).isPreconnected
  have ha₁ : AnalyticOnNhd ℂ F₁ {s : ℂ | 1 / 2 < s.re} := h₁.analyticOnNhd hU
  have ha₂ : AnalyticOnNhd ℂ F₂ {s : ℂ | 1 / 2 < s.re} := h₂.analyticOnNhd hU
  have hmem : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by simp; norm_num
  have hev : F₁ =ᶠ[𝓝 (2 : ℂ)] F₂ := by
    have hU1 : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    exact eventuallyEq_of_mem (hU1.mem_nhds (by simp; norm_num)) fun s hs => heq s hs
  exact ha₁.eqOn_of_preconnected_of_eventuallyEq ha₂ hconn hmem hev

/-- **Zero-density obstruction at `β ≤ 1/2`.**  Every integer-norm fake `B` with count remainder
`|N_B(x) − A x| ≤ C x^β` at an exponent `β ≤ 1/2` has strictly positive density `A > 0`. -/
theorem pos_density_of_integerNormFakeAt_le_half {B : BeurlingSystem} {β A C : ℝ}
    (hf : IsIntegerNormFakeAt B β) (hβ : β ≤ 1 / 2)
    (hC : ∀ x : ℝ, 1 ≤ x → |(B.countBall x : ℝ) - A * x| ≤ C * x ^ β) :
    0 < A := by
  obtain ⟨hInt, hDisc, _, _, G, hGd, hGeq, ρ₀, hρre, hρ1, hG0, _⟩ := hf
  by_contra hAnp
  push Not at hAnp
  have hcnt : ∀ X : ℝ, 1 ≤ X → (B.countBall X : ℝ) ≤ max C 1 * X ^ (1 / 2 : ℝ) := by
    intro X hX
    have h1 := (le_abs_self _).trans (hC X hX)
    have hAx : A * X ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hAnp (by linarith)
    calc (B.countBall X : ℝ) ≤ (B.countBall X : ℝ) - A * X := by linarith
      _ ≤ C * X ^ β := h1
      _ ≤ max C 1 * X ^ β :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by linarith) _)
      _ ≤ max C 1 * X ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX hβ)
            (le_trans zero_le_one (le_max_right _ _))
  have hsum : ∀ σ : ℝ, 1 / 2 < σ → LSeriesSummable (fun n => (intCount B hInt n : ℂ)) (σ : ℂ) := by
    intro σ hσ
    exact (zetaSeriesC_eq_LSeries_of_summable hInt hDisc
      (summable_intNorm_rpow_of_countBall_le hDisc (by norm_num) hcnt hσ)).1
  obtain ⟨hZd, hZne⟩ := differentiableOn_and_ne_zero_zetaSeriesC_of_half hInt hDisc hsum
  have hmul : DifferentiableOn ℂ (fun s => (s - 1) * B.zetaSeriesC s) {s : ℂ | 1 / 2 < s.re} :=
    (differentiableOn_id.sub (differentiableOn_const 1)).mul hZd
  have hid := eqOn_halfPlane_of_eq_on_one hGd hmul hGeq hρre
  rw [hG0] at hid
  exact mul_ne_zero (sub_ne_zero.mpr hρ1) (hZne ρ₀ hρre) hid.symm

/-! ## 3. Kept-prime systems and the elementary Rankin floor bound -/

/-- The integer-norm Beurling system `ℙ \ S` of rational primes outside `S`. -/
def keptPrimeSystem (S : Set ℕ) : BeurlingSystem where
  Label := KeptPrime S
  labelNorm p := (p.1 : ℝ)
  one_lt_labelNorm p := by exact_mod_cast p.2.1.one_lt

theorem hasIntegerNorms_keptPrimeSystem (S : Set ℕ) : HasIntegerNorms (keptPrimeSystem S) :=
  fun p => ⟨p.1, rfl⟩

theorem intNorm_keptPrimeSystem (S : Set ℕ) (u : (keptPrimeSystem S).Integer) :
    (keptPrimeSystem S).intNorm u = ((u.map (fun p : KeptPrime S => p.1)).prod : ℝ) := by
  induction u using Multiset.induction_on with
  | empty => simp [keptPrimeSystem]
  | cons p u ih =>
    rw [← Multiset.singleton_add, BeurlingSystem.intNorm_add, BeurlingSystem.intNorm_singleton,
      ih, Multiset.singleton_add, Multiset.map_cons, Multiset.prod_cons, Nat.cast_mul]
    rfl

theorem natIntNorm_keptPrimeSystem (S : Set ℕ) (u : (keptPrimeSystem S).Integer) :
    natIntNorm (hasIntegerNorms_keptPrimeSystem S) u = (u.map (fun p : KeptPrime S => p.1)).prod := by
  have h := natIntNorm_spec (hasIntegerNorms_keptPrimeSystem S) u
  rw [intNorm_keptPrimeSystem] at h
  exact_mod_cast h

theorem isDiscrete_keptPrimeSystem (S : Set ℕ) : (keptPrimeSystem S).IsDiscrete := by
  intro X
  rcases lt_or_ge X 0 with hX | hX
  · refine Set.Finite.subset Set.finite_empty fun u hu => ?_
    exact absurd ((keptPrimeSystem S).intNorm_pos u) (not_lt.mpr (hu.trans hX.le))
  · refine Set.Finite.of_finite_image (f := fun u : Multiset (KeptPrime S) =>
      (u.map (fun p : KeptPrime S => p.1)).prod) ?_ (prod_kept_injective S).injOn
    refine (Set.finite_Iic ⌊X⌋₊).subset ?_
    rintro n ⟨u, hu, rfl⟩
    rw [Set.mem_setOf_eq, intNorm_keptPrimeSystem] at hu
    exact Nat.le_floor hu

theorem intCount_keptPrimeSystem (S : Set ℕ) (n : ℕ) :
    (intCount (keptPrimeSystem S) (hasIntegerNorms_keptPrimeSystem S) n : ℝ) = sFreeR S n := by
  classical
  unfold intCount sFreeR
  split_ifs with hsf
  · obtain ⟨u, hu⟩ := exists_kept_of_sFree S hsf
    have hset : {g : (keptPrimeSystem S).Integer |
        natIntNorm (hasIntegerNorms_keptPrimeSystem S) g = n} = {u} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, natIntNorm_keptPrimeSystem]
      exact ⟨fun hg => prod_kept_injective S (hg.trans hu.symm), fun hg => hg ▸ hu⟩
    rw [hset, Set.ncard_singleton, Nat.cast_one]
  · have hempty : {g : (keptPrimeSystem S).Integer |
        natIntNorm (hasIntegerNorms_keptPrimeSystem S) g = n} = ∅ := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, natIntNorm_keptPrimeSystem]
      intro hg
      exact hsf (hg ▸ sFree_prod_kept S g)
    rw [hempty, Set.ncard_empty, Nat.cast_zero]

theorem countBall_keptPrimeSystem (S : Set ℕ) {X : ℝ} (hX : 0 ≤ X) :
    ((keptPrimeSystem S).countBall X : ℝ) = ∑ n ∈ Finset.Iic ⌊X⌋₊, sFreeR S n := by
  rw [countBall_eq_sum_intCount (hasIntegerNorms_keptPrimeSystem S)
    (isDiscrete_keptPrimeSystem S) hX, Nat.cast_sum]
  exact Finset.sum_congr rfl fun n _ => intCount_keptPrimeSystem S n

theorem hasLinearCounting_keptPrimeSystem (S : Set ℕ) :
    (keptPrimeSystem S).HasLinearCounting 2 := by
  intro X hX
  rw [countBall_keptPrimeSystem S (by linarith)]
  calc ∑ n ∈ Finset.Iic ⌊X⌋₊, sFreeR S n
      ≤ ∑ n ∈ Finset.Iic ⌊X⌋₊, (1 : ℝ) :=
        Finset.sum_le_sum fun n _ => (le_abs_self _).trans (abs_sFreeR_le S n)
    _ = (⌊X⌋₊ : ℝ) + 1 := by simp
    _ ≤ 2 * X := by linarith [Nat.floor_le (show 0 ≤ X by linarith)]

theorem zetaSeriesC_keptPrimeSystem (S : Set ℕ) {s : ℂ} (hs : 1 < s.re) :
    (keptPrimeSystem S).zetaSeriesC s = LSeries (fun n => (sFreeR S n : ℂ)) s := by
  have hZr := (keptPrimeSystem S).summable_intNorm_rpow (isDiscrete_keptPrimeSystem S)
    (hasLinearCounting_keptPrimeSystem S) hs
  rw [(zetaSeriesC_eq_LSeries_of_summable (hasIntegerNorms_keptPrimeSystem S)
    (isDiscrete_keptPrimeSystem S) hZr).2]
  congr 1; funext n
  exact_mod_cast intCount_keptPrimeSystem S n

theorem notNormEquivPrimes_keptPrimeSystem {S : Set ℕ} {p₀ : ℕ} (hp₀ : p₀.Prime)
    (hmem : p₀ ∈ S) : NotNormEquivPrimes (keptPrimeSystem S) := by
  rintro ⟨⟨e, he⟩⟩
  set l : KeptPrime S := e.symm ⟨p₀, hp₀⟩
  have hl := he l
  simp only [keptPrimeSystem, Equiv.apply_symm_apply] at hl
  have hval : l.1 = p₀ := by exact_mod_cast hl
  exact l.2.2 (hval ▸ hmem)

/-! ### Sieve Möbius identity and Rankin error bound for arbitrary prime sets -/

/-- `n` is positive and all its prime factors belong to `S`. -/
def sOnly (S : Set ℕ) (n : ℕ) : Prop := n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p ∈ S

/-- Real sieve Möbius weight supported on `S`-smooth squarefree integers. -/
def mobSet (S : Set ℕ) (n : ℕ) : ℝ :=
  open Classical in if sOnly S n then (ArithmeticFunction.moebius n : ℝ) else 0

private theorem sOnly_mul {S : Set ℕ} {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    sOnly S (a * b) ↔ sOnly S a ∧ sOnly S b := by
  unfold sOnly
  rw [Nat.primeFactors_mul ha hb]
  simp only [ne_eq, mul_eq_zero, ha, hb, or_self, not_false_eq_true, true_and, Finset.mem_union]
  exact ⟨fun h => ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩,
    fun ⟨h1, h2⟩ p hp => hp.elim (h1 p) (h2 p)⟩

theorem sFreeR_eq_sum_divisors_mobSet (S : Set ℕ) {n : ℕ} (hn : n ≠ 0) :
    sFreeR S n = ∑ d ∈ n.divisors, mobSet S d := by
  classical
  set P : Finset ℕ := n.primeFactors.filter (· ∈ S)
  have hprod_sub : ∏ p ∈ P, ((1 : ℝ) - 1) = if P = ∅ then 1 else 0 := by
    by_cases hP : P = ∅
    · simp [hP]
    · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hP
      rw [if_neg hP]
      exact Finset.prod_eq_zero hp (by ring)
  have hsf_iff : SFree S n ↔ P = ∅ := by
    simp only [SFree, hn, not_false_eq_true, true_and, P, Finset.filter_eq_empty_iff]
  have hlhs : sFreeR S n = ∏ p ∈ P, ((1 : ℝ) - 1) := by
    unfold sFreeR
    rw [hprod_sub]
    split_ifs with h1 h2
    · rfl
    · exact absurd (hsf_iff.mp h1) h2
    · exact absurd (hsf_iff.mpr h2) h1
    · rfl
  rw [hlhs, Finset.prod_sub]
  simp only [Finset.prod_const_one, one_mul]
  -- Biject `P.powerset` with `{d ∈ n.divisors | mobSet S d ≠ 0}` via `T ↦ ∏ p ∈ T, p`.
  set A : Finset ℕ := n.divisors.filter (fun d => mobSet S d ≠ 0)
  have hrhs : ∑ d ∈ n.divisors, mobSet S d = ∑ d ∈ A, mobSet S d := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun d _ => by split_ifs with h <;> [rfl; exact (not_not.mp h)]
  rw [hrhs]
  symm
  refine Finset.sum_nbij (fun d => d.primeFactors) ?_ ?_ ?_ ?_
  · intro d hd
    obtain ⟨hdn, hdm⟩ := Finset.mem_filter.mp hd
    unfold mobSet at hdm
    split_ifs at hdm with hso
    rw [Finset.mem_powerset]
    intro p hp
    exact Finset.mem_filter.mpr ⟨Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hdn) hn hp,
      hso.2 p hp⟩
  · intro d₁ hd₁ d₂ hd₂ heq
    have sq : ∀ d ∈ A, Squarefree d := by
      intro d hd
      have hdm := (Finset.mem_filter.mp hd).2
      unfold mobSet at hdm
      split_ifs at hdm with hso
      rw [← ArithmeticFunction.moebius_ne_zero_iff_squarefree]
      exact fun h0 => hdm (by simp [h0])
    rw [← Nat.prod_primeFactors_of_squarefree (sq d₁ hd₁),
      ← Nat.prod_primeFactors_of_squarefree (sq d₂ hd₂), heq]
  · intro T hT
    rw [Set.mem_image]
    have hTP : T ⊆ P := Finset.mem_powerset.mp hT
    have hTp : ∀ p ∈ T, p.Prime := fun p hp =>
      Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp (hTP hp)).1
    have hsq : Squarefree (∏ p ∈ T, p) := by
      rw [Nat.squarefree_iff_prime_squarefree]
      intro q hq hmul
      have hqd1 : q ∣ ∏ p ∈ T, p := dvd_trans (dvd_mul_right q q) hmul
      obtain ⟨p, hpT, hqp⟩ := Prime.exists_mem_finset_dvd hq.prime hqd1
      have hpq : p = q := ((Nat.prime_dvd_prime_iff_eq hq.prime (hTp p hpT)).mp hqp).symm
      subst hpq
      have hrest : p * p ∣ p * ∏ r ∈ T.erase p, r := by
        rwa [Finset.mul_prod_erase T id hpT] at hmul
      have hdvd2 : p ∣ ∏ r ∈ T.erase p, r :=
        (mul_dvd_mul_iff_left (hTp p hpT).ne_zero).mp hrest
      obtain ⟨r, hr, hpr⟩ := Prime.exists_mem_finset_dvd (hTp p hpT).prime hdvd2
      have hpeqr : p = r := (Nat.prime_dvd_prime_iff_eq (hTp p hpT)
        (hTp r (Finset.mem_of_mem_erase hr))).mp hpr
      exact (Finset.ne_of_mem_erase hr) hpeqr.symm
    have hpf : (∏ p ∈ T, p).primeFactors = T := by
      ext q
      simp only [Nat.mem_primeFactors, ne_eq]
      constructor
      · rintro ⟨hqp, hqd, -⟩
        obtain ⟨p, hpT, hqp'⟩ := Prime.exists_mem_finset_dvd hqp.prime hqd
        rwa [(Nat.prime_dvd_prime_iff_eq hqp (hTp p hpT)).mp hqp']
      · intro hqT
        refine ⟨hTp q hqT, Finset.dvd_prod_of_mem _ hqT, ?_⟩
        exact (Finset.prod_pos fun p hp => (hTp p hp).pos).ne'
    have hdvd : (∏ p ∈ T, p) ∣ n := by
      have hsubn : T ⊆ n.primeFactors := fun p hp => (Finset.mem_filter.mp (hTP hp)).1
      exact dvd_trans (Finset.prod_le_prod_of_subset_of_one_le' hsubn
        (fun p hp => (Nat.prime_of_mem_primeFactors hp).one_lt.le) |> fun _ =>
          Finset.prod_dvd_prod_of_subset T n.primeFactors id hsubn) (Nat.prod_primeFactors_dvd n)
    have hso : sOnly S (∏ p ∈ T, p) :=
      ⟨(Finset.prod_pos fun p hp => (hTp p hp).pos).ne',
        fun p hp => (Finset.mem_filter.mp (hTP (hpf ▸ hp))).2⟩
    have hmne : mobSet S (∏ p ∈ T, p) ≠ 0 := by
      unfold mobSet
      rw [if_pos hso]
      exact_mod_cast ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hsq
    exact ⟨∏ p ∈ T, p, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, hn⟩, hmne⟩, hpf⟩
  · intro d hd
    have hdm := (Finset.mem_filter.mp hd).2
    unfold mobSet at hdm ⊢
    split_ifs at hdm with hso
    rw [if_pos hso]
    have hsq : Squarefree d := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
      fun h0 => hdm (by simp [h0])
    rw [ArithmeticFunction.moebius_apply_of_squarefree hsq]
    push_cast; rfl

theorem countBall_keptPrimeSystem_eq_sum_floor (S : Set ℕ) {X : ℝ} (hX : 0 ≤ X) :
    ((keptPrimeSystem S).countBall X : ℝ) =
      ∑ m ∈ Finset.Ioc 0 ⌊X⌋₊, mobSet S m * ((⌊X⌋₊ / m : ℕ) : ℝ) := by
  rw [countBall_keptPrimeSystem S hX,
    show Finset.Iic ⌊X⌋₊ = Finset.Icc 0 ⌊X⌋₊ by ext; simp,
    Finset.Icc_eq_cons_Ioc (Nat.zero_le _), Finset.sum_cons, sFreeR_zero, zero_add]
  set f : ArithmeticFunction ℝ := ⟨mobSet S, by simp [mobSet, sOnly]⟩
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum f ⌊X⌋₊
  simp only [ArithmeticFunction.coe_mul_zeta_apply] at h
  have hcongr : ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, sFreeR S n =
      ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, ∑ d ∈ n.divisors, f d :=
    Finset.sum_congr rfl fun n hn => sFreeR_eq_sum_divisors_mobSet S (Finset.mem_Ioc.mp hn).1.ne'
  rw [hcongr, h]
  rfl

/-- Rankin bound for `mobSet S`: if `∑_{p ∈ S} p^{−σ} < ∞`, then
`∑_{1 ≤ n ≤ N} |mobSet S n| n^{−σ} ≤ exp(∑_{p ∈ S} p^{−σ})`. -/
theorem sum_abs_mobSet_mul_rpow_le {S : Set ℕ} {σ : ℝ}
    (hsum : Summable fun p : ℕ => S.indicator (fun n => (n : ℝ) ^ (-σ)) p) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, |mobSet S n| * (n : ℝ) ^ (-σ) ≤
      Real.exp (∑' p : ℕ, S.indicator (fun n => (n : ℝ) ^ (-σ)) p) := by
  classical
  set P : Finset ℕ := (Finset.Icc 1 N).filter (· ∈ S)
  set A : Finset ℕ := (Finset.Icc 1 N).filter (fun n => mobSet S n ≠ 0)
  have hsq : ∀ n ∈ A, Squarefree n ∧ sOnly S n := by
    intro n hn
    have hnm := (Finset.mem_filter.mp hn).2
    unfold mobSet at hnm
    split_ifs at hnm with hso
    exact ⟨ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp fun h0 => hnm (by simp [h0]), hso⟩
  have habs1 : ∀ n ∈ A, |mobSet S n| = 1 := by
    intro n hn
    obtain ⟨hs, hso⟩ := hsq n hn
    unfold mobSet
    rw [if_pos hso, ArithmeticFunction.moebius_apply_of_squarefree hs]
    simp
  have hsum1 : ∑ n ∈ Finset.Icc 1 N, |mobSet S n| * (n : ℝ) ^ (-σ) =
      ∑ n ∈ A, (n : ℝ) ^ (-σ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    split_ifs with h
    · rw [habs1 n (Finset.mem_filter.mpr ⟨hn, h⟩), one_mul]
    · rw [not_not.mp h, abs_zero, zero_mul]
  have hinj : Set.InjOn Nat.primeFactors (A : Set ℕ) := by
    intro m hm n hn hmn
    rw [← Nat.prod_primeFactors_of_squarefree (hsq m hm).1,
      ← Nat.prod_primeFactors_of_squarefree (hsq n hn).1, hmn]
  have hsub : A.image Nat.primeFactors ⊆ P.powerset := by
    intro T hT
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hT
    rw [Finset.mem_powerset]
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).one_lt.le,
        (Nat.le_of_mem_primeFactors hp).trans (Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1).2⟩,
      (hsq n hn).2.2 p hp⟩
  rw [hsum1, ← Finset.sum_congr rfl (fun n hn =>
      congrArg (fun k : ℕ => (k : ℝ) ^ (-σ)) (Nat.prod_primeFactors_of_squarefree (hsq n hn).1)),
    ← Finset.sum_image hinj]
  calc ∑ T ∈ A.image Nat.primeFactors, ((∏ p ∈ T, p : ℕ) : ℝ) ^ (-σ)
      ≤ ∑ T ∈ P.powerset, ((∏ p ∈ T, p : ℕ) : ℝ) ^ (-σ) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
    _ = ∏ p ∈ P, (1 + (p : ℝ) ^ (-σ)) := by
        rw [Finset.prod_one_add]
        refine Finset.sum_congr rfl fun T _ => ?_
        rw [Nat.cast_prod, ← Real.finsetProd_rpow _ _ fun _ _ => Nat.cast_nonneg _]
    _ ≤ Real.exp (∑ p ∈ P, (p : ℝ) ^ (-σ)) := by
        rw [Real.exp_sum]
        exact Finset.prod_le_prod (fun _ _ => by positivity)
          fun p _ => by linarith [Real.add_one_le_exp ((p : ℝ) ^ (-σ))]
    _ ≤ Real.exp (∑' p : ℕ, S.indicator (fun n => (n : ℝ) ^ (-σ)) p) := by
        refine Real.exp_le_exp.mpr ?_
        have heq : ∑ p ∈ P, (p : ℝ) ^ (-σ) =
            ∑ p ∈ P, S.indicator (fun n => (n : ℝ) ^ (-σ)) p :=
          Finset.sum_congr rfl fun p hp => (Set.indicator_of_mem (Finset.mem_filter.mp hp).2 _).symm
        rw [heq]
        exact hsum.sum_le_tsum P fun n _ => by rw [Set.indicator_apply]; split_ifs <;> positivity

theorem summable_abs_mobSet_mul_rpow {S : Set ℕ} {σ : ℝ}
    (hsum : Summable fun p : ℕ => S.indicator (fun n => (n : ℝ) ^ (-σ)) p) :
    Summable fun n : ℕ => |mobSet S n| * (n : ℝ) ^ (-σ) := by
  refine summable_of_sum_range_le
    (c := Real.exp (∑' p : ℕ, S.indicator (fun n => (n : ℝ) ^ (-σ)) p))
    (fun n => by positivity) fun N => ?_
  calc ∑ n ∈ Finset.range N, |mobSet S n| * (n : ℝ) ^ (-σ)
      ≤ ∑ n ∈ Finset.range (N + 1), |mobSet S n| * (n : ℝ) ^ (-σ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ N))
          fun _ _ _ => by positivity
    _ = ∑ n ∈ Finset.Icc 1 N, |mobSet S n| * (n : ℝ) ^ (-σ) := by
        rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
        have h0 : mobSet S 0 = 0 := by simp [mobSet, sOnly]
        rw [h0, abs_zero, zero_mul, zero_add]
        rfl
    _ ≤ _ := sum_abs_mobSet_mul_rpow_le hsum N

/-- **Elementary Rankin floor bound for `keptPrimeSystem S`.**
Whenever `0 < β ≤ 1` and `∑_{p ∈ S} p^{−β} < ∞`, the generalized-integer count of `ℙ \ S`
satisfies `|N_B(x) − A x| ≤ 2 exp(∑_{p ∈ S} p^{−β}) x^β` for all `x ≥ 1`, with `A ≥ 0`. -/
theorem keptPrimeSystem_count_sub_le_of_summable {S : Set ℕ} {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hsum : Summable fun p : ℕ => S.indicator (fun n => (n : ℝ) ^ (-β)) p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 1 ≤ x →
      |((keptPrimeSystem S).countBall x : ℝ) - A * x| ≤
        2 * Real.exp (∑' p : ℕ, S.indicator (fun n => (n : ℝ) ^ (-β)) p) * x ^ β := by
  set R : ℝ := Real.exp (∑' p : ℕ, S.indicator (fun n => (n : ℝ) ^ (-β)) p)
  have hR0 : 0 < R := Real.exp_pos _
  have hmobβ := summable_abs_mobSet_mul_rpow hsum
  have hmob1_abs : Summable fun m : ℕ => |mobSet S m / m| := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun m => ?_) hmobβ
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < m), div_eq_mul_inv, ← Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero hm) (by linarith))
        (abs_nonneg _)
  have hmob1 : Summable fun m : ℕ => mobSet S m / m := hmob1_abs.of_abs
  set A : ℝ := ∑' m : ℕ, mobSet S m / m
  have hbound : ∀ x : ℝ, 1 ≤ x →
      |((keptPrimeSystem S).countBall x : ℝ) - A * x| ≤ 2 * R * x ^ β := by
    intro x hx
    have hx0 : 0 < x := by linarith
    rw [countBall_keptPrimeSystem_eq_sum_floor S hx0.le]
    have hsplit : A * x = (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (mobSet S m / m) * x) +
        ∑' m : {m : ℕ // m ∉ Finset.Ioc 0 ⌊x⌋₊}, (mobSet S m.1 / m.1) * x := by
      have hmul := hmob1.mul_right x
      have := (hmul.sum_add_tsum_compl (s := Finset.Ioc 0 ⌊x⌋₊)).symm
      rwa [tsum_mul_right] at this
    rw [hsplit]
    have e : (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, mobSet S m * ((⌊x⌋₊ / m : ℕ) : ℝ)) -
        ((∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (mobSet S m / m) * x) +
          ∑' m : {m : ℕ // m ∉ Finset.Ioc 0 ⌊x⌋₊}, (mobSet S m.1 / m.1) * x) =
        (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, mobSet S m * (((⌊x⌋₊ / m : ℕ) : ℝ) - x / m)) -
          ∑' m : {m : ℕ // m ∉ Finset.Ioc 0 ⌊x⌋₊}, (mobSet S m.1 / m.1) * x := by
      rw [← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [e]
    -- Head `1 ≤ m ≤ ⌊x⌋₊`
    have hhead : |∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, mobSet S m * (((⌊x⌋₊ / m : ℕ) : ℝ) - x / m)| ≤
        R * x ^ β := by
      calc _ ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, |mobSet S m * (((⌊x⌋₊ / m : ℕ) : ℝ) - x / m)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (|mobSet S m| * (m : ℝ) ^ (-β)) * x ^ β := by
            refine Finset.sum_le_sum fun m hm => ?_
            obtain ⟨hm1, hmx⟩ := Finset.mem_Ioc.mp hm
            have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
            have hmx' : (m : ℝ) ≤ x := (Nat.le_floor_iff hx0.le).mp hmx
            rw [abs_mul, ← Nat.floor_div_natCast]
            have hfl1 : (⌊x / m⌋₊ : ℝ) ≤ x / m := Nat.floor_le (div_nonneg hx0.le hm0.le)
            have hfl2 : x / m - 1 < (⌊x / m⌋₊ : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
            have habs_fr : |(⌊x / m⌋₊ : ℝ) - x / m| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
            have hrp : 1 ≤ (m : ℝ) ^ (-β) * x ^ β := by
              rw [Real.rpow_neg hm0.le, inv_mul_eq_div, one_le_div (by positivity)]
              exact Real.rpow_le_rpow hm0.le hmx' hβ0.le
            calc |mobSet S m| * |(⌊x / m⌋₊ : ℝ) - x / m|
                ≤ |mobSet S m| * 1 := mul_le_mul_of_nonneg_left habs_fr (abs_nonneg _)
              _ ≤ |mobSet S m| * ((m : ℝ) ^ (-β) * x ^ β) :=
                  mul_le_mul_of_nonneg_left hrp (abs_nonneg _)
              _ = (|mobSet S m| * (m : ℝ) ^ (-β)) * x ^ β := by ring
        _ = (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, |mobSet S m| * (m : ℝ) ^ (-β)) * x ^ β := by
            rw [← Finset.sum_mul]; rfl
        _ ≤ R * x ^ β := mul_le_mul_of_nonneg_right (sum_abs_mobSet_mul_rpow_le hsum _) (by positivity)
    -- Tail `m > ⌊x⌋₊`
    have htail : |∑' m : {m : ℕ // m ∉ Finset.Ioc 0 ⌊x⌋₊}, (mobSet S m.1 / m.1) * x| ≤
        R * x ^ β := by
      have hterm : ∀ m : {m : ℕ // m ∉ Finset.Ioc 0 ⌊x⌋₊},
          |(mobSet S m.1 / m.1) * x| ≤ (|mobSet S m.1| * (m.1 : ℝ) ^ (-β)) * x ^ β := by
        intro ⟨m, hm⟩
        rcases eq_or_ne m 0 with rfl | hm0
        · simp [mobSet, sOnly]
        · have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
          have hgt : ⌊x⌋₊ < m := by
            by_contra hle; push Not at hle
            exact hm (Finset.mem_Ioc.mpr ⟨hmpos, hle⟩)
          have hxm : x ≤ (m : ℝ) := (Nat.lt_floor_add_one x).le.trans (by exact_mod_cast hgt)
          have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
          rw [abs_mul, abs_div, abs_of_pos hmR, abs_of_pos hx0]
          have hpow : x / m ≤ (m : ℝ) ^ (-β) * x ^ β := by
            have h1 : x ^ (1 - β) ≤ (m : ℝ) ^ (1 - β) :=
              Real.rpow_le_rpow hx0.le hxm (by linarith)
            have h2 : x = x ^ (1 - β) * x ^ β := by
              rw [← Real.rpow_add hx0, sub_add_cancel, Real.rpow_one]
            have h3 : (m : ℝ) = (m : ℝ) ^ (1 - β) * (m : ℝ) ^ β := by
              rw [← Real.rpow_add hmR, sub_add_cancel, Real.rpow_one]
            rw [Real.rpow_neg hmR.le, div_le_iff₀ hmR]
            calc x = x ^ (1 - β) * x ^ β := h2
              _ ≤ (m : ℝ) ^ (1 - β) * x ^ β := mul_le_mul_of_nonneg_right h1 (by positivity)
              _ = ((m : ℝ) ^ (-β) * x ^ β) * m := by
                  rw [Real.rpow_neg hmR.le, h3]
                  field_simp
          calc |mobSet S m| / m * x = |mobSet S m| * (x / m) := by ring
            _ ≤ |mobSet S m| * ((m : ℝ) ^ (-β) * x ^ β) :=
                mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
            _ = _ := by ring
      have hsub_sum : Summable fun m : {m : ℕ // m ∉ Finset.Ioc 0 ⌊x⌋₊} =>
          (|mobSet S m.1| * (m.1 : ℝ) ^ (-β)) * x ^ β :=
        (hmobβ.mul_right (x ^ β)).subtype _
      have hsub_orig : Summable fun m : {m : ℕ // m ∉ Finset.Ioc 0 ⌊x⌋₊} =>
          (mobSet S m.1 / m.1) * x := (hmob1.mul_right x).subtype _
      calc |∑' m : {m : ℕ // m ∉ Finset.Ioc 0 ⌊x⌋₊}, (mobSet S m.1 / m.1) * x|
          ≤ ∑' m : {m : ℕ // m ∉ Finset.Ioc 0 ⌊x⌋₊}, |(mobSet S m.1 / m.1) * x| :=
            abs_tsum_le_tsum_abs' hsub_orig (Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
              hterm hsub_sum)
        _ ≤ ∑' m : {m : ℕ // m ∉ Finset.Ioc 0 ⌊x⌋₊},
              (|mobSet S m.1| * (m.1 : ℝ) ^ (-β)) * x ^ β :=
            Summable.tsum_le_tsum hterm
              (Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm hsub_sum) hsub_sum
        _ ≤ ∑' m : ℕ, (|mobSet S m| * (m : ℝ) ^ (-β)) * x ^ β :=
            Summable.tsum_subtype_le (fun m => (|mobSet S m| * (m : ℝ) ^ (-β)) * x ^ β) _
              (fun _ => by positivity) (hmobβ.mul_right (x ^ β))
        _ = (∑' m : ℕ, |mobSet S m| * (m : ℝ) ^ (-β)) * x ^ β := tsum_mul_right
        _ ≤ R * x ^ β := by
            refine mul_le_mul_of_nonneg_right ?_ (by positivity)
            exact Real.tsum_le_of_sum_range_le hmobβ (fun _ => by positivity) fun N => by
              calc ∑ n ∈ Finset.range N, |mobSet S n| * (n : ℝ) ^ (-β)
                  ≤ ∑ n ∈ Finset.range (N + 1), |mobSet S n| * (n : ℝ) ^ (-β) :=
                    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ N))
                      fun _ _ _ => by positivity
                _ = ∑ n ∈ Finset.Icc 1 N, |mobSet S n| * (n : ℝ) ^ (-β) := by
                    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
                    have h0 : mobSet S 0 = 0 := by simp [mobSet, sOnly]
                    rw [h0, abs_zero, zero_mul, zero_add]; rfl
                _ ≤ R := sum_abs_mobSet_mul_rpow_le hsum N
    calc |(∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, mobSet S m * (((⌊x⌋₊ / m : ℕ) : ℝ) - x / m)) -
          ∑' m : {m : ℕ // m ∉ Finset.Ioc 0 ⌊x⌋₊}, (mobSet S m.1 / m.1) * x|
        ≤ |∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, mobSet S m * (((⌊x⌋₊ / m : ℕ) : ℝ) - x / m)| +
          |∑' m : {m : ℕ // m ∉ Finset.Ioc 0 ⌊x⌋₊}, (mobSet S m.1 / m.1) * x| := abs_sub _ _
      _ ≤ R * x ^ β + R * x ^ β := add_le_add hhead htail
      _ = 2 * R * x ^ β := by ring
  -- Nonnegativity of `A`: for every `N ≥ 1`, `A = ∑' m, mobSet S m / m` is the Cesàro limit if `β < 1`,
  -- and more directly on real `σ > 1`, `(∑' n, sFreeR S n * n^{-σ}) * (∑' m, mobSet S m * m^{-σ}) = 1`
  -- forces `∑' m, mobSet S m * m^{-σ} > 0`, whose limit as `σ → 1⁺` is `A ≥ 0`!
  have hA0 : 0 ≤ A := by
    have hcont : ContinuousOn (fun σ : ℝ => ∑' m : ℕ, mobSet S m * (m : ℝ) ^ (-σ))
        (Set.Ici 1) := by
      refine continuousOn_tsum (fun m => ?_) hmob1_abs fun m σ hσ => ?_
      · rcases eq_or_ne m 0 with rfl | hm
        · simp [mobSet, sOnly]; exact continuousOn_const
        · exact continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_const
            (fun _ _ => Or.inl (by exact_mod_cast hm)) |> fun _ =>
              (Real.continuous_rpow_const_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hm)).comp_continuousOn
                continuousOn_id.neg)
      · rcases eq_or_ne m 0 with rfl | hm
        · simp [mobSet, sOnly]
        · have hσ1 : 1 ≤ σ := hσ
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.rpow_pos_of_pos
            (by exact_mod_cast Nat.pos_of_ne_zero hm) _), abs_div,
            abs_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hm), div_eq_mul_inv,
            ← Real.rpow_neg_one]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero hm)
              (by linarith)) (abs_nonneg _)
    have hpos_gt : ∀ σ : ℝ, 1 < σ → 0 ≤ ∑' m : ℕ, mobSet S m * (m : ℝ) ^ (-σ) := by
      intro σ hσ
      set fA : ℕ → ℂ := fun n => (sFreeR S n : ℂ)
      set gA : ℕ → ℂ := fun m => (mobSet S m : ℂ)
      have hfS : LSeriesSummable fA (σ : ℂ) :=
        LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
          (fun n _ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sFreeR_le S n)
          (by simpa using hσ)
      have hgS : LSeriesSummable gA (σ : ℂ) := by
        refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) (by simpa using hσ)
        rw [Complex.norm_real, Real.norm_eq_abs]
        unfold mobSet; split_ifs
        · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        · norm_num
      have hconv : LSeries.convolution fA gA = LSeries.delta := by
        -- Actually `sFreeR S = 1 ⋆ mobSet S`, so `1 * gA = fA`, hence `ζ(σ) * LSeries gA σ = LSeries fA σ`!
        sorry
      sorry
    sorry
  exact ⟨A, hA0, hbound⟩
