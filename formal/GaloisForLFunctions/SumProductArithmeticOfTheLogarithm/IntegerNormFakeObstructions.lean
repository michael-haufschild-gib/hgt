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

This module establishes the unconditionally forced obstructions on integer-norm fakes and the
`β = 1/2` quadratic-character calibration:

* **Finite-omission and pure-addition obstructions.**
  - Every discrete integer-norm system with `B.HasLinearCounting C₁` that omits only finitely many
    rational primes from `B.labelNorm` has `(s − 1) ζ_B(s)` nonvanishing off the zeros of `ζ(s)` on
    all of `{Re s > 1/2} \ {1}` (`no_fake_zero_of_finite_missing_primes`), by factoring out one
    copy of each kept prime and transferring positivity of the residual Dirichlet series across
    `(1/2, ∞)` via Landau's theorem and the zero-free strip `|Im s| < 4` of `ζ`.
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
  - For any set `S` of integers with `∑_{p ∈ S} p^{−β} < ∞` (`0 ≤ β < 1`), the kept-prime system
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
open RHTower RHTower.Sieve RHTower.BeurlingDeletion GaloisForLFunctions.RHTower
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

/-- Unit-density sublogarithmic rigidity: no integer-norm fake can satisfy
`|N_B(n) − n| = o(log n)`. -/
theorem not_unit_density_sublogarithmic_of_integerNormFakeAt {B : BeurlingSystem} {β : ℝ}
    (hf : IsIntegerNormFakeAt B β) :
    ¬ (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        |(B.countBall n : ℝ) - n| ≤ ε * Real.log n) :=
  fun hsmall => hf.2.2.1 (primes_of_sublogarithmic_count_error B hf.1 hf.2.1 hsmall)

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
    have hp1 : 0 ≤ (B.intNorm p.1) ^ (-s.re) := Real.rpow_nonneg (B.intNorm_pos _).le _
    have hp2 : 0 ≤ (B.intNorm p.2) ^ (-s.re) := Real.rpow_nonneg (B.intNorm_pos _).le _
    calc ‖(B.moebius p.1 : ℂ)‖ * (B.intNorm p.1) ^ (-s.re) * (B.intNorm p.2) ^ (-s.re)
        ≤ 1 * (B.intNorm p.1) ^ (-s.re) * (B.intNorm p.2) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnorm hp1) hp2
      _ = (B.intNorm p.1) ^ (-s.re) * (B.intNorm p.2) ^ (-s.re) := by rw [one_mul]
  rw [BeurlingSystem.moebiusSeriesC, BeurlingSystem.zetaSeriesC, hM.tsum_mul_tsum hZ hFsum]
  set e := Equiv.sigmaFiberEquiv fun p : (Multiset B.Label) × (Multiset B.Label) => p.1 + p.2
  have hsigma : Summable (F ∘ e) := e.summable_iff.mpr hFsum
  rw [(e.tsum_eq F).symm]
  change ∑' c, (F ∘ e) c = 1
  rw [hsigma.tsum_sigma]
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
  have hfibre' : ∀ b : Multiset B.Label,
      (∑' c : {x : (Multiset B.Label) × (Multiset B.Label) // x.1 + x.2 = b}, (F ∘ e) ⟨b, c⟩) =
        if b = 0 then 1 else 0 := hfibre
  rw [tsum_congr hfibre', tsum_eq_single 0 (fun n hn => if_neg hn), if_pos rfl]

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
    rw [← Multiset.singleton_add, B.intNorm_add, B.intNorm_singleton, ← natLabelNorm_spec h l, ← ih]
    unfold natIntNorm
    rw [Multiset.singleton_add, Multiset.map_cons, Multiset.prod_cons, Nat.cast_mul]

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
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [intCount, Set.ncard_eq_toFinset_card _ (finite_fiber_natIntNorm h hdisc n)]
  congr 1
  ext g
  simp only [S, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
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
    rw [← @Nat.card_eq_fintype_card _ (finite_fiber_natIntNorm h hdisc n).fintype,
      Nat.card_coe_set_eq, ← intCount]
  have hfibC : ∀ n : ℕ,
      (∑' c : {g : B.Integer // natIntNorm h g = n}, ((B.intNorm c.1 : ℝ) : ℂ) ^ (-s)) =
        LSeries.term (fun m => (intCount B h m : ℂ)) s n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero]
      haveI : IsEmpty {g : B.Integer // natIntNorm h g = 0} :=
        ⟨fun c => by have := one_le_natIntNorm h c.1; omega⟩
      simp
    · letI : Fintype {g : B.Integer // natIntNorm h g = n} :=
        (finite_fiber_natIntNorm h hdisc n).fintype
      rw [tsum_fintype, LSeries.term_of_ne_zero hn]
      have hval : ∀ c : {g : B.Integer // natIntNorm h g = n},
          ((B.intNorm c.1 : ℝ) : ℂ) ^ (-s) = (n : ℂ) ^ (-s) := fun c => by
        rw [← natIntNorm_spec h c.1, c.2]; push_cast; rfl
      simp_rw [hval, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← @Nat.card_eq_fintype_card _ (finite_fiber_natIntNorm h hdisc n).fintype,
        Nat.card_coe_set_eq, ← intCount, Complex.cpow_neg, div_eq_mul_inv]
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
  rw [BeurlingSystem.zetaSeriesC, (e.tsum_eq _).symm]
  change ∑' c, ((fun g : Multiset B.Label => ((B.intNorm g : ℝ) : ℂ) ^ (-s)) ∘ e) c = _
  rw [hsigmaC.tsum_sigma]
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
    exact (hasSum_fintype _).summable
  · refine (hLS.norm).congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero, norm_zero]
      haveI : IsEmpty {g : B.Integer // natIntNorm h g = 0} :=
        ⟨fun c => by have := one_le_natIntNorm h c.1; omega⟩
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
      rw [← @Nat.card_eq_fintype_card _ (finite_fiber_natIntNorm h hdisc n).fintype,
        Nat.card_coe_set_eq, ← intCount, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]

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
  have heq : ∀ s ∈ {s : ℂ | 1 / 2 < s.re},
      B.zetaSeriesC s = LSeries (fun n => (intCount B h n : ℂ)) s := fun s hs =>
    (zetaSeriesC_eq_LSeries_of_summable h hdisc (hZr s hs)).2
  have hdiffL : DifferentiableOn ℂ (LSeries (fun n => (intCount B h n : ℂ)))
      {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    have hslt : LSeries.abscissaOfAbsConv (fun n => (intCount B h n : ℂ)) < s.re :=
      lt_of_le_of_lt habs (by exact_mod_cast hs)
    exact (LSeries_hasDerivAt hslt).differentiableAt.differentiableWithinAt
  exact ⟨hdiffL.congr heq, fun s hs => zetaSeriesC_ne_zero_of_summable hdisc (hZr s hs)⟩

/-- Identity theorem on the open half-plane `{Re s > 1/2}`: two holomorphic functions agreeing on
`{Re s > 1}` agree on all of `{Re s > 1/2}`. -/
theorem eqOn_halfPlane_of_eq_on_one {F₁ F₂ : ℂ → ℂ}
    (h₁ : DifferentiableOn ℂ F₁ {s : ℂ | 1 / 2 < s.re})
    (h₂ : DifferentiableOn ℂ F₂ {s : ℂ | 1 / 2 < s.re})
    (heq : ∀ s : ℂ, 1 < s.re → F₁ s = F₂ s) :
    Set.EqOn F₁ F₂ {s : ℂ | 1 / 2 < s.re} := by
  have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hconv : Convex ℝ {s : ℂ | 1 / 2 < s.re} := by
    intro x hx y hy a b ha hb hab
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at *
    rcases eq_or_lt_of_le ha with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1; linarith
    · have h1 : a * (1 / 2) < a * x.re := mul_lt_mul_of_pos_left hx ha'
      have h2 : b * (1 / 2) ≤ b * y.re := mul_le_mul_of_nonneg_left hy.le hb
      linarith
  have hconn : IsPreconnected {s : ℂ | 1 / 2 < s.re} := hconv.isPreconnected
  have ha₁ : AnalyticOnNhd ℂ F₁ {s : ℂ | 1 / 2 < s.re} := h₁.analyticOnNhd hU
  have ha₂ : AnalyticOnNhd ℂ F₂ {s : ℂ | 1 / 2 < s.re} := h₂.analyticOnNhd hU
  have hmem : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by simp; norm_num
  have hev : F₁ =ᶠ[𝓝 (2 : ℂ)] F₂ := by
    have hU1 : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    exact eventuallyEq_of_mem (hU1.mem_nhds (by simp)) fun s hs => heq s hs
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

/-- **Nonnegativity of fake remainder exponents.**  No integer-norm Beurling fake can have a
strictly negative remainder exponent `β < 0`: on `(n, n + 1)` the integer-norm count `N_B` is
constant, so `o(1)` error forces `A = 0`, contradicting `pos_density_of_integerNormFakeAt_le_half`. -/
theorem nonneg_of_integerNormFakeAt {B : BeurlingSystem} {β : ℝ}
    (hf : IsIntegerNormFakeAt B β) : 0 ≤ β := by
  by_contra hlt
  push Not at hlt
  obtain ⟨A, C, _, hC⟩ := hf.2.2.2.1
  have hApos : 0 < A := pos_density_of_integerNormFakeAt_le_half hf (by linarith) hC
  have hInt := hf.1
  have hDisc := hf.2.1
  have hstep : ∀ n : ℕ, 1 ≤ n → A / 2 ≤ 2 * max C 0 * (n : ℝ) ^ β := by
    intro n hn
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hfl1 : ⌊(n : ℝ) + 1 / 4⌋₊ = n :=
      Nat.floor_eq_iff (by positivity) |>.mpr ⟨by linarith, by linarith⟩
    have hfl2 : ⌊(n : ℝ) + 3 / 4⌋₊ = n :=
      Nat.floor_eq_iff (by positivity) |>.mpr ⟨by linarith, by linarith⟩
    have hcnt : B.countBall ((n : ℝ) + 1 / 4) = B.countBall ((n : ℝ) + 3 / 4) := by
      rw [countBall_eq_sum_intCount hInt hDisc (by positivity),
        countBall_eq_sum_intCount hInt hDisc (by positivity), hfl1, hfl2]
    have e : A / 2 =
        ((B.countBall ((n : ℝ) + 1 / 4) : ℝ) - A * ((n : ℝ) + 1 / 4)) -
          ((B.countBall ((n : ℝ) + 3 / 4) : ℝ) - A * ((n : ℝ) + 3 / 4)) := by
      rw [hcnt]; ring
    have h1 := hC ((n : ℝ) + 1 / 4) (by linarith)
    have h2 := hC ((n : ℝ) + 3 / 4) (by linarith)
    have hp1 : ((n : ℝ) + 1 / 4) ^ β ≤ (n : ℝ) ^ β :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hlt.le
    have hp2 : ((n : ℝ) + 3 / 4) ^ β ≤ (n : ℝ) ^ β :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) hlt.le
    calc A / 2
        ≤ |((B.countBall ((n : ℝ) + 1 / 4) : ℝ) - A * ((n : ℝ) + 1 / 4)) -
            ((B.countBall ((n : ℝ) + 3 / 4) : ℝ) - A * ((n : ℝ) + 3 / 4))| := by
          rw [← e]; exact le_abs_self _
      _ ≤ |(B.countBall ((n : ℝ) + 1 / 4) : ℝ) - A * ((n : ℝ) + 1 / 4)| +
          |(B.countBall ((n : ℝ) + 3 / 4) : ℝ) - A * ((n : ℝ) + 3 / 4)| := abs_sub _ _
      _ ≤ C * ((n : ℝ) + 1 / 4) ^ β + C * ((n : ℝ) + 3 / 4) ^ β := add_le_add h1 h2
      _ ≤ max C 0 * ((n : ℝ) + 1 / 4) ^ β + max C 0 * ((n : ℝ) + 3 / 4) ^ β := by
          gcongr <;> exact le_max_left _ _
      _ ≤ max C 0 * (n : ℝ) ^ β + max C 0 * (n : ℝ) ^ β := by gcongr
      _ = 2 * max C 0 * (n : ℝ) ^ β := by ring
  have hlim : Tendsto (fun n : ℕ => 2 * max C 0 * (n : ℝ) ^ β) atTop (𝓝 0) := by
    have t1 : Tendsto (fun n : ℕ => (n : ℝ) ^ β) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := -β) (by linarith)).comp tendsto_natCast_atTop_atTop
      simpa [Function.comp_def] using this
    simpa using t1.const_mul (2 * max C 0)
  have hle0 : A / 2 ≤ 0 :=
    ge_of_tendsto hlim ((eventually_ge_atTop 1).mono fun n hn => hstep n hn)
  linarith

theorem bddBelow_integerNormFakeExponents : BddBelow integerNormFakeExponents :=
  ⟨0, fun _ ⟨_, hf⟩ => nonneg_of_integerNormFakeAt hf⟩

/-! ## 3. Kept-prime systems and the elementary Rankin floor bound -/

/-- The integer-norm Beurling system `ℙ \ S` of rational primes outside `S`. -/
def keptPrimeSystem (S : Set ℕ) : BeurlingSystem where
  Label := KeptPrime S
  labelNorm p := (p.1 : ℝ)
  one_lt_labelNorm p := by exact_mod_cast p.2.1.one_lt

theorem hasIntegerNorms_keptPrimeSystem (S : Set ℕ) : HasIntegerNorms (keptPrimeSystem S) :=
  fun p => ⟨p.1, rfl⟩

theorem intNorm_keptPrimeSystem (S : Set ℕ) (u : (keptPrimeSystem S).Integer) :
    (keptPrimeSystem S).intNorm u =
      ((Multiset.map (fun p : KeptPrime S => p.1) u).prod : ℝ) := by
  induction u using Multiset.induction_on with
  | empty => simp [BeurlingSystem.intNorm]; rfl
  | cons p u ih =>
    rw [← Multiset.singleton_add, BeurlingSystem.intNorm_add, BeurlingSystem.intNorm_singleton, ih]
    change (p.1 : ℝ) * ((Multiset.map (fun q : KeptPrime S => q.1) u).prod : ℝ) =
      ((Multiset.map (fun q : KeptPrime S => q.1) (p ::ₘ u)).prod : ℝ)
    rw [Multiset.map_cons, Multiset.prod_cons, Nat.cast_mul]

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
    set u' : (keptPrimeSystem S).Integer := u
    have hset : {g : (keptPrimeSystem S).Integer |
        natIntNorm (hasIntegerNorms_keptPrimeSystem S) g = n} = {u'} := by
      ext g
      rw [Set.mem_setOf_eq, Set.mem_singleton_iff, natIntNorm_keptPrimeSystem]
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
  have hl : (l.1 : ℝ) = ((e l : ℕ) : ℝ) := he l
  rw [e.apply_symm_apply] at hl
  have hval : l.1 = p₀ := by exact_mod_cast hl
  exact l.2.2 (hval ▸ hmem)

/-! ### Sieve Möbius identity and Rankin error bound for arbitrary prime sets -/

/-- `n` is positive and all its prime factors belong to `S`. -/
def sOnly (S : Set ℕ) (n : ℕ) : Prop := n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p ∈ S

/-- Real sieve Möbius weight supported on `S`-smooth squarefree integers. -/
def mobSet (S : Set ℕ) (n : ℕ) : ℝ :=
  open Classical in if sOnly S n then (ArithmeticFunction.moebius n : ℝ) else 0

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
    simp only [SFree, P, Finset.filter_eq_empty_iff]
    exact ⟨fun h => h.2, fun h => ⟨hn, h⟩⟩
  have hlhs : sFreeR S n = ∏ p ∈ P, ((1 : ℝ) - 1) := by
    unfold sFreeR
    rw [hprod_sub]
    by_cases h1 : SFree S n
    · rw [if_pos h1, if_pos (hsf_iff.mp h1)]
    · rw [if_neg h1, if_neg (mt hsf_iff.mpr h1)]
  rw [hlhs, Finset.prod_sub]
  simp only [Finset.prod_const_one]
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
    · rw [Finset.mem_powerset]
      intro p hp
      exact Finset.mem_filter.mpr ⟨Nat.primeFactors_mono (Nat.dvd_of_mem_divisors hdn) hn hp,
        hso.2 p hp⟩
    · exact absurd rfl hdm
  · intro d₁ hd₁ d₂ hd₂ heq
    have sq : ∀ d ∈ A, Squarefree d := by
      intro d hd
      have hdm := (Finset.mem_filter.mp hd).2
      unfold mobSet at hdm
      split_ifs at hdm with hso
      · rw [← ArithmeticFunction.moebius_ne_zero_iff_squarefree]
        exact fun h0 => hdm (by simp [h0])
      · exact absurd rfl hdm
    dsimp only at heq
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
      have hpq : p = q := ((Nat.prime_dvd_prime_iff_eq hq (hTp p hpT)).mp hqp).symm
      subst hpq
      have hrest : p * p ∣ p * ∏ r ∈ T.erase p, r := by
        rwa [Finset.mul_prod_erase T (fun x => x) hpT]
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
      exact dvd_trans (Finset.prod_dvd_prod_of_subset T n.primeFactors id hsubn)
        (Nat.prod_primeFactors_dvd n)
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
    · rw [if_pos hso]
      have hsq : Squarefree d := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
        fun h0 => hdm (by simp [h0])
      have hcf : ArithmeticFunction.cardFactors d = d.primeFactors.card := by
        rw [ArithmeticFunction.cardFactors_eq_sum_factorization, Finsupp.sum]
        have hsup : d.factorization.support = d.primeFactors := Nat.support_factorization d
        rw [hsup]
        have h1 : ∀ p ∈ d.primeFactors, d.factorization p = 1 := by
          intro p hp
          have hpp := Nat.prime_of_mem_primeFactors hp
          have hpos : 1 ≤ d.factorization p :=
            hpp.factorization_pos_of_dvd hso.1 (Nat.dvd_of_mem_primeFactors hp)
          by_contra hne1
          have hge2 : 2 ≤ d.factorization p := by omega
          have hdvd2 : p * p ∣ d := by
            rw [← sq]
            exact dvd_trans (pow_dvd_pow p hge2) (Nat.ordProj_dvd d p)
          exact Nat.squarefree_iff_prime_squarefree.mp hsq p hpp hdvd2
        rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul, mul_one]
      rw [ArithmeticFunction.moebius_apply_of_squarefree hsq, hcf]
      push_cast; ring
    · exact absurd rfl hdm

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
    · exact ⟨ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp fun h0 => hnm (by simp [h0]), hso⟩
    · exact absurd rfl hnm
  have habs1 : ∀ n ∈ A, |mobSet S n| = 1 := by
    intro n hn
    obtain ⟨hs, hso⟩ := hsq n hn
    unfold mobSet
    rw [if_pos hso, ← Int.cast_abs, ArithmeticFunction.abs_moebius_eq_one_of_squarefree hs]
    norm_num
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
    ← Finset.sum_image (f := fun T : Finset ℕ => ((∏ p ∈ T, p : ℕ) : ℝ) ^ (-σ)) hinj]
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
          Finset.sum_congr rfl fun p hp =>
            (Set.indicator_of_mem (Finset.mem_filter.mp hp).2
              (fun n : ℕ => (n : ℝ) ^ (-σ))).symm
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
Whenever `0 ≤ β < 1` and `∑_{p ∈ S} p^{−β} < ∞`, the generalized-integer count of `ℙ \ S`
satisfies `|N_B(x) − A x| ≤ 2 exp(∑_{p ∈ S} p^{−β}) x^β` for all `x ≥ 1`, with `A ≥ 0`. -/
theorem keptPrimeSystem_count_sub_le_of_summable {S : Set ℕ} {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hsum : Summable fun p : ℕ => S.indicator (fun n => (n : ℝ) ^ (-β)) p) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 1 ≤ x →
      |((keptPrimeSystem S).countBall x : ℝ) - A * x| ≤
        2 * Real.exp (∑' p : ℕ, S.indicator (fun n => (n : ℝ) ^ (-β)) p) * x ^ β := by
  let R : ℝ := Real.exp (∑' p : ℕ, S.indicator (fun n => (n : ℝ) ^ (-β)) p)
  have hmobβ := summable_abs_mobSet_mul_rpow hsum
  have htsum_le_R : (∑' m : ℕ, |mobSet S m| * (m : ℝ) ^ (-β)) ≤ R := by
    refine Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun N => ?_
    calc ∑ n ∈ Finset.range N, |mobSet S n| * (n : ℝ) ^ (-β)
        ≤ ∑ n ∈ Finset.range (N + 1), |mobSet S n| * (n : ℝ) ^ (-β) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ N))
            fun _ _ _ => by positivity
      _ = ∑ n ∈ Finset.Icc 1 N, |mobSet S n| * (n : ℝ) ^ (-β) := by
          rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
          have h0 : mobSet S 0 = 0 := by simp [mobSet, sOnly]
          rw [h0, abs_zero, zero_mul, zero_add]; rfl
      _ ≤ R := sum_abs_mobSet_mul_rpow_le hsum N
  have hmob1_abs : Summable fun m : ℕ => |mobSet S m / m| := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun m => ?_) hmobβ
    rcases eq_or_ne m 0 with rfl | hm
    · simp [mobSet, sOnly]
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < m), div_eq_mul_inv, ← Real.rpow_neg_one]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.pos_of_ne_zero hm) (by linarith))
        (abs_nonneg _)
  have hmob1 : Summable fun m : ℕ => mobSet S m / m := hmob1_abs.of_abs
  let A : ℝ := ∑' m : ℕ, mobSet S m / m
  have hbound : ∀ x : ℝ, 1 ≤ x →
      |((keptPrimeSystem S).countBall x : ℝ) - A * x| ≤ 2 * R * x ^ β := by
    intro x hx
    have hx0 : 0 < x := by linarith
    let K : ℕ := ⌊x⌋₊ + 1
    rw [countBall_keptPrimeSystem_eq_sum_floor S hx0.le]
    have hsplit : A * x = (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (mobSet S m / m) * x) +
        ∑' k : ℕ, (mobSet S (k + K) / ((k + K : ℕ) : ℝ)) * x := by
      have hmul := hmob1.mul_right x
      have hnat := (hmul.sum_add_tsum_nat_add K).symm
      rw [tsum_mul_right] at hnat
      rw [hnat]
      congr 1
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos ⌊x⌋₊)]
      have h0 : mobSet S 0 = 0 := by simp [mobSet, sOnly]
      rw [h0, zero_div, zero_mul, zero_add]
      have hIco : Finset.Ico 1 K = Finset.Ioc 0 ⌊x⌋₊ := by
        ext m; simp only [Finset.mem_Ico, Finset.mem_Ioc, K]; omega
      rw [hIco]
    rw [hsplit]
    have e : (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, mobSet S m * ((⌊x⌋₊ / m : ℕ) : ℝ)) -
        ((∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, (mobSet S m / m) * x) +
          ∑' k : ℕ, (mobSet S (k + K) / ((k + K : ℕ) : ℝ)) * x) =
        (∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, mobSet S m * (((⌊x⌋₊ / m : ℕ) : ℝ) - x / m)) -
          ∑' k : ℕ, (mobSet S (k + K) / ((k + K : ℕ) : ℝ)) * x := by
      rw [sub_add_eq_sub_sub, ← Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [e]
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
              exact Real.rpow_le_rpow hm0.le hmx' hβ0
            calc |mobSet S m| * |(⌊x / m⌋₊ : ℝ) - x / m|
                ≤ |mobSet S m| * 1 := mul_le_mul_of_nonneg_left habs_fr (abs_nonneg _)
              _ ≤ |mobSet S m| * ((m : ℝ) ^ (-β) * x ^ β) :=
                  mul_le_mul_of_nonneg_left hrp (abs_nonneg _)
              _ = (|mobSet S m| * (m : ℝ) ^ (-β)) * x ^ β := by ring
        _ = (∑ m ∈ Finset.Icc 1 ⌊x⌋₊, |mobSet S m| * (m : ℝ) ^ (-β)) * x ^ β := by
            rw [← Finset.sum_mul]; rfl
        _ ≤ R * x ^ β := mul_le_mul_of_nonneg_right (sum_abs_mobSet_mul_rpow_le hsum _) (by positivity)
    have htail : |∑' k : ℕ, (mobSet S (k + K) / ((k + K : ℕ) : ℝ)) * x| ≤ R * x ^ β := by
      have hterm : ∀ k : ℕ,
          |(mobSet S (k + K) / ((k + K : ℕ) : ℝ)) * x| ≤
            (|mobSet S (k + K)| * ((k + K : ℕ) : ℝ) ^ (-β)) * x ^ β := by
        intro k
        have hmpos : 0 < k + K := by dsimp [K]; omega
        have hgt : ⌊x⌋₊ + 1 ≤ k + K := by dsimp [K]; omega
        have hxm : x ≤ ((k + K : ℕ) : ℝ) :=
          (Nat.lt_floor_add_one x).le.trans (by exact_mod_cast hgt)
        have hmR : (0 : ℝ) < ((k + K : ℕ) : ℝ) := by exact_mod_cast hmpos
        rw [abs_mul, abs_div, abs_of_pos hmR, abs_of_pos hx0]
        have hpow : x / ((k + K : ℕ) : ℝ) ≤ ((k + K : ℕ) : ℝ) ^ (-β) * x ^ β := by
          rw [div_le_iff₀ hmR]
          have h1 : x ^ (1 - β) ≤ ((k + K : ℕ) : ℝ) ^ (1 - β) :=
            Real.rpow_le_rpow hx0.le hxm (by linarith)
          have h2 : x = x ^ (1 - β) * x ^ β := by
            rw [← Real.rpow_add hx0, sub_add_cancel, Real.rpow_one]
          have h3 : ((k + K : ℕ) : ℝ) ^ (1 - β) =
              ((k + K : ℕ) : ℝ) * ((k + K : ℕ) : ℝ) ^ (-β) := by
            rw [show 1 - β = 1 + (-β) by ring, Real.rpow_add hmR, Real.rpow_one]
          calc x = x ^ (1 - β) * x ^ β := h2
            _ ≤ ((k + K : ℕ) : ℝ) ^ (1 - β) * x ^ β :=
                mul_le_mul_of_nonneg_right h1 (by positivity)
            _ = (((k + K : ℕ) : ℝ) ^ (-β) * x ^ β) * ((k + K : ℕ) : ℝ) := by rw [h3]; ring
        calc |mobSet S (k + K)| / ((k + K : ℕ) : ℝ) * x
            = |mobSet S (k + K)| * (x / ((k + K : ℕ) : ℝ)) := by ring
          _ ≤ |mobSet S (k + K)| * (((k + K : ℕ) : ℝ) ^ (-β) * x ^ β) :=
              mul_le_mul_of_nonneg_left hpow (abs_nonneg _)
          _ = _ := by ring
      have hshift_β : Summable fun k : ℕ => |mobSet S (k + K)| * ((k + K : ℕ) : ℝ) ^ (-β) :=
        (_root_.summable_nat_add_iff K).mpr hmobβ
      have hmaj : Summable fun k : ℕ =>
          (|mobSet S (k + K)| * ((k + K : ℕ) : ℝ) ^ (-β)) * x ^ β := hshift_β.mul_right (x ^ β)
      have habs_k : Summable fun k : ℕ => |(mobSet S (k + K) / ((k + K : ℕ) : ℝ)) * x| :=
        Summable.of_nonneg_of_le (fun _ => abs_nonneg _) hterm hmaj
      have hshift_le : (∑' k : ℕ, |mobSet S (k + K)| * ((k + K : ℕ) : ℝ) ^ (-β)) ≤ R := by
        have hadd := hmobβ.sum_add_tsum_nat_add K
        have hsum_nn : 0 ≤ ∑ i ∈ Finset.range K, |mobSet S i| * (i : ℝ) ^ (-β) :=
          Finset.sum_nonneg fun _ _ => by positivity
        linarith
      calc |∑' k : ℕ, (mobSet S (k + K) / ((k + K : ℕ) : ℝ)) * x|
          ≤ ∑' k : ℕ, |(mobSet S (k + K) / ((k + K : ℕ) : ℝ)) * x| := by
            simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm habs_k
        _ ≤ ∑' k : ℕ, (|mobSet S (k + K)| * ((k + K : ℕ) : ℝ) ^ (-β)) * x ^ β :=
            habs_k.tsum_le_tsum hterm hmaj
        _ = (∑' k : ℕ, |mobSet S (k + K)| * ((k + K : ℕ) : ℝ) ^ (-β)) * x ^ β := tsum_mul_right
        _ ≤ R * x ^ β := mul_le_mul_of_nonneg_right hshift_le (by positivity)
    calc |(∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, mobSet S m * (((⌊x⌋₊ / m : ℕ) : ℝ) - x / m)) -
          ∑' k : ℕ, (mobSet S (k + K) / ((k + K : ℕ) : ℝ)) * x|
        ≤ |∑ m ∈ Finset.Ioc 0 ⌊x⌋₊, mobSet S m * (((⌊x⌋₊ / m : ℕ) : ℝ) - x / m)| +
          |∑' k : ℕ, (mobSet S (k + K) / ((k + K : ℕ) : ℝ)) * x| := abs_sub _ _
      _ ≤ R * x ^ β + R * x ^ β := add_le_add hhead htail
      _ = 2 * R * x ^ β := by ring
  have hA0 : 0 ≤ A := by
    have hle : ∀ x : ℝ, 1 ≤ x → -A ≤ 2 * R * x ^ (β - 1) := by
      intro x hx
      have hx0 : 0 < x := by linarith
      have hc0 : (0 : ℝ) ≤ ((keptPrimeSystem S).countBall x : ℝ) := Nat.cast_nonneg _
      have hb := (neg_le_abs _).trans (hbound x hx)
      have hAx : -A * x ≤ 2 * R * x ^ β := by linarith
      rw [Real.rpow_sub hx0, Real.rpow_one, mul_div_assoc, le_div_iff₀ hx0]
      linarith
    have hlim : Tendsto (fun x : ℝ => 2 * R * x ^ (β - 1)) atTop (𝓝 0) := by
      have t1 : Tendsto (fun x : ℝ => x ^ (β - 1)) atTop (𝓝 0) := by
        simpa [neg_sub] using tendsto_rpow_neg_atTop (y := 1 - β) (by linarith)
      simpa using t1.const_mul (2 * R)
    have hneg : -A ≤ 0 :=
      ge_of_tendsto hlim ((eventually_ge_atTop (1 : ℝ)).mono fun x hx => hle x hx)
    linarith
  exact ⟨A, hA0, hbound⟩

/-! ## 4. Finite-omission and pure-addition obstructions -/

private theorem LSeries_sFreeR_finset_eq {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime)
    {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (sFreeR (D : Set ℕ) n : ℂ)) s =
      (∏ p ∈ D, (1 - (p : ℂ) ^ (-s))) * riemannZeta s := by
  classical
  induction D using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, one_mul, ← LSeries_one_eq_riemannZeta hs]
    refine LSeries_congr (fun {n} hn => ?_) s
    simp [sFreeR, SFree, hn]
  | @insert q D' hqD ih =>
    have hqP : q.Prime := hD q (Finset.mem_insert_self q D')
    have hD' : ∀ p ∈ D', p.Prime := fun p hp => hD p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert hqD, mul_assoc, ← ih hD']
    set fD : ℕ → ℂ := fun n => (sFreeR (D' : Set ℕ) n : ℂ)
    set fq : ℕ → ℂ := fun k => if k = 1 then 1 else if k = q then -1 else 0
    have hfD_sum : LSeriesSummable fD s :=
      LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
        (fun n _ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_sFreeR_le _ n) hs
    have hfq_sum : LSeriesSummable fq s := by
      refine summable_of_ne_finset_zero (s := {1, q}) fun k hk => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
      rcases eq_or_ne k 0 with rfl | hk0
      · simp
      · simp [LSeries.term_of_ne_zero hk0, fq, hk.1, hk.2]
    have hLfq : LSeries fq s = 1 - (q : ℂ) ^ (-s) := by
      unfold LSeries
      rw [tsum_eq_sum (s := {1, q}) fun k hk => by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        rcases eq_or_ne k 0 with rfl | hk0
        · simp
        · simp [LSeries.term_of_ne_zero hk0, fq, hk.1, hk.2]]
      rw [Finset.sum_pair hqP.one_lt.ne]
      simp [LSeries.term_of_ne_zero hqP.ne_zero, fq,
        hqP.one_lt.ne', Complex.cpow_neg, div_eq_mul_inv]
      ring
    rw [← hLfq, ← LSeries_convolution' hfq_sum hfD_sum]
    refine LSeries_congr (fun {n} hn => ?_) s
    rw [LSeries.convolution_def]
    dsimp only
    by_cases hqn : q ∣ n
    · obtain ⟨m, rfl⟩ := hqn
      have hm0 : m ≠ 0 := right_ne_zero_of_mul hn
      have hpair : (1, q * m) ∈ (q * m).divisorsAntidiagonal ∧
          (q, m) ∈ (q * m).divisorsAntidiagonal :=
        ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul _, hn⟩,
          Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hn⟩⟩
      have hsub : ∑ x ∈ (q * m).divisorsAntidiagonal, fq x.1 * fD x.2 =
          fq 1 * fD (q * m) + fq q * fD m := by
        have hpair_sum : ∑ x ∈ ({(1, q * m), (q, m)} : Finset (ℕ × ℕ)), fq x.1 * fD x.2 =
            fq 1 * fD (q * m) + fq q * fD m :=
          Finset.sum_pair (fun h => hqP.one_lt.ne (congrArg Prod.fst h))
        rw [← hpair_sum]
        symm
        refine Finset.sum_subset (fun x hx => ?_) (fun x hx hnot => ?_)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          exact hx.elim (· ▸ hpair.1) (· ▸ hpair.2)
        · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
          have hx_eq := (Nat.mem_divisorsAntidiagonal.mp hx).1
          have hne1 : x.1 ≠ 1 := fun h1 => hnot.1 (Prod.ext h1 (by rw [h1, one_mul] at hx_eq; exact hx_eq))
          have hneq : x.1 ≠ q := fun hq => hnot.2 (Prod.ext hq
            (mul_left_cancel₀ hqP.ne_zero (by rw [← hq]; exact hx_eq)))
          simp [fq, hne1, hneq]
      rw [hsub]
      simp only [fq, ↓reduceIte, hqP.one_lt.ne', one_mul, neg_one_mul]
      have hsf_qm : SFree (D' : Set ℕ) (q * m) ↔ SFree (D' : Set ℕ) m := by
        simp only [SFree, hn, hm0, ne_eq, not_false_eq_true, true_and,
          Nat.primeFactors_mul hqP.ne_zero hm0, Finset.mem_union, hqP.primeFactors,
          Finset.mem_singleton]
        exact ⟨fun h p hp => h p (Or.inr hp),
          fun h p hp => hp.elim (fun hpq => hpq ▸ hqD) (h p)⟩
      have hsf_ins : ¬ SFree (insert q D' : Set ℕ) (q * m) := by
        intro h
        exact h.2 q (Nat.mem_primeFactors.mpr ⟨hqP, dvd_mul_right q m, hn⟩)
          (Set.mem_insert q _)
      simp only [fD, sFreeR, Finset.coe_insert, if_neg hsf_ins, Nat.cast_zero]
      by_cases hm : SFree (D' : Set ℕ) m
      · rw [if_pos (hsf_qm.mpr hm), if_pos hm]; ring
      · rw [if_neg (mt hsf_qm.mp hm), if_neg hm]; ring
    · have hsingle : ∑ x ∈ n.divisorsAntidiagonal, fq x.1 * fD x.2 = fD n := by
        rw [Finset.sum_eq_single (1, n)]
        · simp [fq]
        · intro x hx hne1
          have hx_eq := (Nat.mem_divisorsAntidiagonal.mp hx).1
          have hx1 : x.1 ≠ 1 := fun h1 => hne1 (Prod.ext h1 (by rw [h1, one_mul] at hx_eq; exact hx_eq))
          have hxq : x.1 ≠ q := fun hq => hqn ⟨x.2, by rw [← hq]; exact hx_eq.symm⟩
          simp [fq, hx1, hxq]
        · intro hmem
          exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul n, hn⟩) hmem
      rw [hsingle]
      have hsf_eq : SFree (insert q D' : Set ℕ) n ↔ SFree (D' : Set ℕ) n := by
        simp only [SFree, Finset.coe_insert, Set.mem_insert_iff, not_or]
        exact ⟨fun ⟨h0, h⟩ => ⟨h0, fun p hp => (h p hp).2⟩,
          fun ⟨h0, h⟩ => ⟨h0, fun p hp => ⟨fun hpq => hqn (hpq ▸ Nat.dvd_of_mem_primeFactors hp),
            h p hp⟩⟩⟩
      simp only [fD, sFreeR, Finset.coe_insert]
      by_cases h : SFree (D' : Set ℕ) n
      · rw [if_pos (hsf_eq.mpr h), if_pos h]
      · rw [if_neg (mt hsf_eq.mp h), if_neg h]

/-- **Finite-omission obstruction.**  Let `B` be a discrete integer-norm Beurling system with
linear counting whose omitted rational prime set
`{p : ℕ | p.Prime ∧ ∀ l : B.Label, B.labelNorm l ≠ p}` is finite.  If `(s − 1) ζ_B(s)` continues
holomorphically as `G` across `{Re s > 1/2}`, then for every `ρ₀ ≠ 1` with `Re ρ₀ > 1/2`,
`G ρ₀ = 0 ↔ riemannZeta ρ₀ = 0`. -/
theorem no_fake_zero_of_finite_missing_primes {B : BeurlingSystem} (hInt : HasIntegerNorms B)
    (hDisc : B.IsDiscrete) {C₁ : ℝ} (hLin : B.HasLinearCounting C₁)
    (hFin : {p : ℕ | p.Prime ∧ ∀ l : B.Label, B.labelNorm l ≠ p}.Finite)
    {G : ℂ → ℂ} (hGd : DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re})
    (hGeq : ∀ s : ℂ, 1 < s.re → G s = (s - 1) * B.zetaSeriesC s)
    {ρ₀ : ℂ} (hρ : 1 / 2 < ρ₀.re) (hρ1 : ρ₀ ≠ 1) :
    G ρ₀ = 0 ↔ riemannZeta ρ₀ = 0 := by
  classical
  set D : Finset ℕ := hFin.toFinset
  have hDp : ∀ p ∈ D, p.Prime := fun p hp => ((Set.Finite.mem_toFinset hFin).mp hp).1
  have hex_kept : ∀ q : KeptPrime (D : Set ℕ), ∃ l : B.Label, B.labelNorm l = (q.1 : ℝ) := by
    intro q
    by_contra hno
    push Not at hno
    exact q.2.2 ((Set.Finite.mem_toFinset hFin).mpr ⟨q.2.1, hno⟩)
  let ι : KeptPrime (D : Set ℕ) → B.Label := fun q => Classical.choose (hex_kept q)
  have hι_norm : ∀ q : KeptPrime (D : Set ℕ), B.labelNorm (ι q) = (q.1 : ℝ) :=
    fun q => Classical.choose_spec (hex_kept q)
  have hι_inj : Function.Injective ι := by
    intro q₁ q₂ heq
    apply Subtype.ext
    have h1 := hι_norm q₁
    rw [heq, hι_norm q₂] at h1
    exact_mod_cast h1.symm
  -- Complementary sub-system `B_add` on labels outside `Set.range ι`.
  let B_add : BeurlingSystem := {
    Label := {l : B.Label // l ∉ Set.range ι}
    labelNorm := fun l => B.labelNorm l.1
    one_lt_labelNorm := fun l => B.one_lt_labelNorm l.1
  }
  have hInt_add : HasIntegerNorms B_add := fun l => hInt l.1
  -- Label bijection `KeptPrime D ⊕ B_add.Label ≃ B.Label`.
  let eL : KeptPrime (D : Set ℕ) ⊕ B_add.Label ≃ B.Label :=
    ((Equiv.ofInjective ι hι_inj).sumCongr (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range ι))
  have heL_norm : ∀ x : KeptPrime (D : Set ℕ) ⊕ B_add.Label,
      B.labelNorm (eL x) =
        Sum.elim (keptPrimeSystem (D : Set ℕ)).labelNorm B_add.labelNorm x := by
    rintro (q | l)
    · exact hι_norm q
    · rfl
  -- Generalized-integer bijection `(keptPrimeSystem D).Integer × B_add.Integer ≃ B.Integer`.
  let mapEquivL : Multiset (KeptPrime (D : Set ℕ) ⊕ B_add.Label) ≃ B.Integer := {
    toFun := Multiset.map eL
    invFun := Multiset.map eL.symm
    left_inv := fun s => by simp [Multiset.map_map]
    right_inv := fun s => by simp [Multiset.map_map]
  }
  let eM : (keptPrimeSystem (D : Set ℕ)).Integer × B_add.Integer ≃ B.Integer :=
    joinEquiv.trans mapEquivL
  have heM_norm : ∀ uv : (keptPrimeSystem (D : Set ℕ)).Integer × B_add.Integer,
      B.intNorm (eM uv) =
        (keptPrimeSystem (D : Set ℕ)).intNorm uv.1 * B_add.intNorm uv.2 := by
    rintro ⟨u, v⟩
    change B.intNorm ((u.map Sum.inl + v.map Sum.inr).map eL) = _
    rw [Multiset.map_add, B.intNorm_add]
    simp only [BeurlingSystem.intNorm, Multiset.map_map, Function.comp_def, heL_norm,
      Sum.elim_inl, Sum.elim_inr]
  have hinj_right : Function.Injective (fun v : B_add.Integer => eM (0, v)) :=
    fun v₁ v₂ h => (Prod.mk.inj (eM.injective h)).2
  have hnorm_right : ∀ v : B_add.Integer, B.intNorm (eM (0, v)) = B_add.intNorm v := fun v => by
    rw [heM_norm, BeurlingSystem.intNorm_zero, one_mul]
  have hDisc_add : B_add.IsDiscrete := by
    intro X
    refine Set.Finite.of_finite_image (f := fun v => eM (0, v)) ?_ hinj_right.injOn
    refine (hDisc X).subset ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [Set.mem_setOf_eq, hnorm_right]
    exact hv
  have hLin_add : B_add.HasLinearCounting C₁ := by
    intro X hX
    have hle : B_add.countBall X ≤ B.countBall X := by
      rw [BeurlingSystem.countBall, BeurlingSystem.countBall,
        ← Set.ncard_image_of_injective _ hinj_right]
      refine Set.ncard_le_ncard ?_ (hDisc X)
      rintro _ ⟨v, hv, rfl⟩
      rw [Set.mem_setOf_eq, hnorm_right]
      exact hv
    exact (Nat.cast_le.mpr hle).trans (hLin X hX)
  -- Product factorization of `B.zetaSeriesC` on `Re s > 1`.
  have hzeta_prod : ∀ s : ℂ, 1 < s.re →
      B.zetaSeriesC s = (keptPrimeSystem (D : Set ℕ)).zetaSeriesC s * B_add.zetaSeriesC s := by
    intro s hs
    have hZ₁ := (keptPrimeSystem (D : Set ℕ)).summable_intNorm_cpow
      (isDiscrete_keptPrimeSystem _) (hasLinearCounting_keptPrimeSystem _) hs
    have hZ₂ := B_add.summable_intNorm_cpow hDisc_add hLin_add hs
    have hZB := B.summable_intNorm_cpow hDisc hLin hs
    have hpair : Summable fun uv : (keptPrimeSystem (D : Set ℕ)).Integer × B_add.Integer =>
        (((keptPrimeSystem (D : Set ℕ)).intNorm uv.1 : ℝ) : ℂ) ^ (-s) *
          ((B_add.intNorm uv.2 : ℝ) : ℂ) ^ (-s) := by
      refine (eM.summable_iff.mpr hZB).congr fun uv => ?_
      change ((B.intNorm (eM uv) : ℝ) : ℂ) ^ (-s) = _
      rw [heM_norm uv, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg ((keptPrimeSystem _).intNorm_pos _).le
          (B_add.intNorm_pos _).le]
    simp only [BeurlingSystem.zetaSeriesC]
    rw [hZ₁.tsum_mul_tsum hZ₂ hpair, ← eM.tsum_eq]
    refine tsum_congr fun uv => ?_
    rw [heM_norm uv, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg ((keptPrimeSystem _).intNorm_pos _).le
        (B_add.intNorm_pos _).le]
  -- Define `K(s) = ζ_u(s) ∏_{p ∈ D} (1 − p^{−s})`.
  set K : ℂ → ℂ := fun s => zetaResidueUnit s * ∏ p ∈ D, (1 - (p : ℂ) ^ (-s))
  have hKd : Differentiable ℂ K := by
    have hd₁ : Differentiable ℂ zetaResidueUnit :=
      fun s => (analyticAt_zetaResidueUnit s).differentiableAt
    exact hd₁.mul (Differentiable.finset_prod fun p hp =>
      (differentiable_const 1).sub
        (differentiable_id.neg.const_cpow (Or.inl (by exact_mod_cast (hDp p hp).ne_zero))))
  have hprod_ne : ∀ s : ℂ, 0 < s.re → ∏ p ∈ D, (1 - (p : ℂ) ^ (-s)) ≠ 0 := by
    intro s hs
    refine Finset.prod_ne_zero_iff.mpr fun p hp => sub_ne_zero.mpr ?_
    intro heq
    have hnorm := congrArg norm heq.symm
    rw [norm_one, Complex.norm_natCast_cpow_of_pos (hDp p hp).pos, Complex.neg_re] at hnorm
    have hlt : (p : ℝ) ^ (-s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (hDp p hp).one_lt) (by linarith)
    linarith
  have hKne_strip : ∀ s : ℂ, 1 / 2 < s.re → |s.im| < 4 → K s ≠ 0 := by
    intro s hs him
    refine mul_ne_zero ?_ (hprod_ne s (by linarith))
    rcases eq_or_ne s 1 with rfl | hs1
    · rw [zetaResidueUnit_one]; exact one_ne_zero
    · rw [zetaResidueUnit_ne_zero_iff hs1]
      rcases le_or_gt 1 s.re with h1 | h1
      · exact riemannZeta_ne_zero_of_one_le_re h1
      · exact riemannZeta_ne_zero_of_abs_im_lt_four (by linarith) h1 him
  have hG_fact : ∀ s : ℂ, 1 < s.re → G s = K s * B_add.zetaSeriesC s := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
    rw [hGeq s hs, hzeta_prod s hs, zetaSeriesC_keptPrimeSystem _ hs,
      LSeries_sFreeR_finset_eq hDp hs]
    have hzu : zetaResidueUnit s = (s - 1) * riemannZeta s := by
      simp [zetaResidueUnit, Function.update_of_ne hs1]
    dsimp only [K]
    rw [hzu]
    ring
  -- Landau transfer on `intCount B_add` across `(1/2, ∞)` using `σ₁ = 2`, centre `3`.
  have hsum_two : LSeriesSummable (fun n => (intCount B_add hInt_add n : ℂ)) (2 : ℂ) :=
    (zetaSeriesC_eq_LSeries_of_summable hInt_add hDisc_add
      (B_add.summable_intNorm_rpow hDisc_add hLin_add (by norm_num : (1 : ℝ) < 2))).1
  have hsum_half : ∀ σ : ℝ, 1 / 2 < σ →
      LSeriesSummable (fun n => (intCount B_add hInt_add n : ℂ)) (σ : ℂ) := by
    intro σ hσ
    set δ : ℝ := min ((σ - 1 / 2) / 2) 1
    have hδ0 : 0 < δ := lt_min (by linarith) one_pos
    have hδ1 : δ ≤ 1 := min_le_right _ _
    set R : NNReal := (5 / 2 - δ).toNNReal
    have hRval : (R : ℝ) = 5 / 2 - δ := Real.coe_toNNReal _ (by linarith)
    have hGd_div : DifferentiableOn ℂ (fun z => G z / K z)
        (Metric.closedBall ((2 + 1 : ℝ) : ℂ) (R : ℝ)) := by
      intro z hz
      have hdist : ‖z - 3‖ ≤ 5 / 2 - δ := by
        have h3 : ((2 + 1 : ℝ) : ℂ) = 3 := by norm_num
        rw [Metric.mem_closedBall, Complex.dist_eq, hRval, h3] at hz
        exact hz
      have hre : 1 / 2 < z.re := by
        have h1 := Complex.abs_re_le_norm (z - 3)
        simp only [Complex.sub_re, Complex.re_ofNat] at h1
        linarith [(abs_le.mp (h1.trans hdist)).1]
      have him : |z.im| < 4 := by
        have h1 := Complex.abs_im_le_norm (z - 3)
        simp only [Complex.sub_im, Complex.im_ofNat, sub_zero] at h1
        linarith [h1.trans hdist]
      have hU : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
      exact ((hGd.differentiableAt (hU.mem_nhds hre)).div (hKd.differentiableAt)
        (hKne_strip z hre him)).differentiableWithinAt
    have hagree : ∀ s : ℂ, 2 < s.re →
        G s / K s = LSeries (fun n => (intCount B_add hInt_add n : ℂ)) s := by
      intro s hs
      have hs1 : 1 < s.re := by linarith
      have him : |s.im| < 4 ∨ 1 ≤ s.re := Or.inr hs1.le
      have hKs : K s ≠ 0 := mul_ne_zero
        ((zetaResidueUnit_ne_zero_iff (fun h => by rw [h] at hs; norm_num at hs)).mpr
          (riemannZeta_ne_zero_of_one_le_re hs1.le))
        (hprod_ne s (by linarith))
      rw [hG_fact s hs1, mul_div_cancel_left₀ _ hKs,
        (zetaSeriesC_eq_LSeries_of_summable hInt_add hDisc_add
          (B_add.summable_intNorm_rpow hDisc_add hLin_add hs1)).2]
    refine landau_summability_transfer (fun n => Nat.cast_nonneg _) hsum_two hGd_div
      (fun s hs => by simpa using hagree s hs) ?_
    rw [hRval]
    have hδσ : δ ≤ (σ - 1 / 2) / 2 := min_le_left _ _
    linarith
  obtain ⟨hZd_add, hZne_add⟩ :=
    differentiableOn_and_ne_zero_zetaSeriesC_of_half hInt_add hDisc_add hsum_half
  have hG_all : Set.EqOn G (fun s => K s * B_add.zetaSeriesC s) {s : ℂ | 1 / 2 < s.re} :=
    eqOn_halfPlane_of_eq_on_one hGd (hKd.differentiableOn.mul hZd_add) hG_fact
  rw [hG_all hρ]
  have hprod0 : ∏ p ∈ D, (1 - (p : ℂ) ^ (-ρ₀)) ≠ 0 := hprod_ne ρ₀ (by linarith)
  have hadd0 : B_add.zetaSeriesC ρ₀ ≠ 0 := hZne_add ρ₀ hρ
  have hzu : zetaResidueUnit ρ₀ = (ρ₀ - 1) * riemannZeta ρ₀ := by
    simp [zetaResidueUnit, Function.update_of_ne hρ1]
  dsimp only [K]
  rw [hzu, mul_assoc, mul_assoc, mul_eq_zero, or_iff_right (sub_ne_zero.mpr hρ1),
    mul_eq_zero, or_iff_left (mul_ne_zero hprod0 hadd0)]

/-- **Infinite missing-primes theorem.**  Every integer-norm Beurling fake at any exponent `β ≤ 1`
omits infinitely many rational primes from `B.labelNorm`. -/
theorem infinite_missing_primes_of_integerNormFakeAt {B : BeurlingSystem} {β : ℝ} (hβ : β ≤ 1)
    (hf : IsIntegerNormFakeAt B β) :
    {p : ℕ | p.Prime ∧ ∀ l : B.Label, B.labelNorm l ≠ p}.Infinite := by
  intro hFin
  obtain ⟨hInt, hDisc, _, ⟨A, C, _, hC⟩, G, hGd, hGeq, ρ₀, hρre, hρ1, hG0, hζ⟩ := hf
  have hLin := hasLinearCounting_of_count_sub_le hβ hC
  exact hζ ((no_fake_zero_of_finite_missing_primes hInt hDisc hLin hFin hGd hGeq hρre hρ1).mp hG0)

/-- **Pure-addition obstruction.**  No Beurling system containing at least one label of norm `p`
for every rational prime `p` can be an integer-norm fake at any exponent `β ≤ 1`. -/
theorem not_isIntegerNormFakeAt_of_surjective_primes {B : BeurlingSystem} {β : ℝ} (hβ : β ≤ 1)
    (hsurj : ∀ p : ℕ, p.Prime → ∃ l : B.Label, B.labelNorm l = p) :
    ¬ IsIntegerNormFakeAt B β := by
  intro hf
  have hempty : {p : ℕ | p.Prime ∧ ∀ l : B.Label, B.labelNorm l ≠ p} = ∅ := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_forall, not_ne_iff]
    exact hsurj p
  exact infinite_missing_primes_of_integerNormFakeAt hβ hf (hempty ▸ Set.finite_empty)

/-- **Finite-deletion calibration (`β = 0`).**  Deleting any finite set `D` of primes yields
bounded integer-count error `|N_B(x) − A x| ≤ C` (`β = 0`), yet `keptPrimeSystem D` is never an
integer-norm fake at any `β ≤ 1`. -/
theorem not_isIntegerNormFakeAt_keptPrimeSystem_of_finite (D : Finset ℕ) :
    (∃ A C : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 1 ≤ x →
      |((keptPrimeSystem (D : Set ℕ)).countBall x : ℝ) - A * x| ≤ C) ∧
    ∀ β : ℝ, β ≤ 1 → ¬ IsIntegerNormFakeAt (keptPrimeSystem (D : Set ℕ)) β := by
  refine ⟨?_, fun β hβ hf => ?_⟩
  · have hsum : Summable fun p : ℕ => (D : Set ℕ).indicator (fun n => (n : ℝ) ^ (-(0 : ℝ))) p :=
      summable_of_ne_finset_zero (s := D) fun p hp => Set.indicator_of_notMem hp _
    obtain ⟨A, hA, hC⟩ := keptPrimeSystem_count_sub_le_of_summable le_rfl zero_lt_one hsum
    exact ⟨A, 2 * Real.exp (∑' p : ℕ, (D : Set ℕ).indicator (fun n => (n : ℝ) ^ (-(0 : ℝ))) p),
      hA, fun x hx => by simpa using hC x hx⟩
  · refine infinite_missing_primes_of_integerNormFakeAt hβ hf (D.finite_toSet.subset ?_)
    intro p ⟨hp, hno⟩
    by_contra hpD
    exact hno ⟨p, hp, hpD⟩ rfl

/-! ## 5. Disjoint-sum systems and the quadratic `L`-function model at `β = 1/2` -/

/-- Disjoint union of two Beurling systems, whose generalized-integer counts convolve
multiplicatively. -/
def sumSystem (B₁ B₂ : BeurlingSystem) : BeurlingSystem where
  Label := B₁.Label ⊕ B₂.Label
  labelNorm := Sum.elim B₁.labelNorm B₂.labelNorm
  one_lt_labelNorm l := by
    cases l with
    | inl a => exact B₁.one_lt_labelNorm a
    | inr b => exact B₂.one_lt_labelNorm b

theorem hasIntegerNorms_sumSystem {B₁ B₂ : BeurlingSystem}
    (h₁ : HasIntegerNorms B₁) (h₂ : HasIntegerNorms B₂) :
    HasIntegerNorms (sumSystem B₁ B₂) := by
  rintro (a | b)
  · exact h₁ a
  · exact h₂ b

theorem intNorm_joinEquiv_sumSystem {B₁ B₂ : BeurlingSystem}
    (u : B₁.Integer) (v : B₂.Integer) :
    (sumSystem B₁ B₂).intNorm (joinEquiv (u, v)) = B₁.intNorm u * B₂.intNorm v := by
  change (sumSystem B₁ B₂).intNorm (u.map Sum.inl + v.map Sum.inr) = _
  simp only [BeurlingSystem.intNorm, sumSystem, Multiset.map_add, Multiset.prod_add,
    Multiset.map_map, Function.comp_def, Sum.elim_inl, Sum.elim_inr]

theorem natIntNorm_joinEquiv_sumSystem {B₁ B₂ : BeurlingSystem}
    (h₁ : HasIntegerNorms B₁) (h₂ : HasIntegerNorms B₂)
    (u : B₁.Integer) (v : B₂.Integer) :
    natIntNorm (hasIntegerNorms_sumSystem h₁ h₂) (joinEquiv (u, v)) =
      natIntNorm h₁ u * natIntNorm h₂ v := by
  have h := natIntNorm_spec (hasIntegerNorms_sumSystem h₁ h₂) (joinEquiv (u, v))
  rw [intNorm_joinEquiv_sumSystem, ← natIntNorm_spec h₁ u, ← natIntNorm_spec h₂ v,
    ← Nat.cast_mul] at h
  exact_mod_cast h

theorem isDiscrete_sumSystem {B₁ B₂ : BeurlingSystem}
    (hd₁ : B₁.IsDiscrete) (hd₂ : B₂.IsDiscrete) :
    (sumSystem B₁ B₂).IsDiscrete := by
  intro X
  refine ((hd₁ X).prod (hd₂ X) |>.image joinEquiv).subset fun w hw => ?_
  have hw' : (sumSystem B₁ B₂).intNorm w ≤ X := hw
  set uv := joinEquiv.symm w
  have hw_eq : joinEquiv uv = w := joinEquiv.apply_symm_apply w
  rw [← hw_eq, intNorm_joinEquiv_sumSystem] at hw'
  have h1 : B₁.intNorm uv.1 ≤ X := by
    calc B₁.intNorm uv.1 = B₁.intNorm uv.1 * 1 := (mul_one _).symm
      _ ≤ B₁.intNorm uv.1 * B₂.intNorm uv.2 :=
          mul_le_mul_of_nonneg_left (B₂.one_le_intNorm _) (B₁.intNorm_pos _).le
      _ ≤ X := hw'
  have h2 : B₂.intNorm uv.2 ≤ X := by
    calc B₂.intNorm uv.2 = 1 * B₂.intNorm uv.2 := (one_mul _).symm
      _ ≤ B₁.intNorm uv.1 * B₂.intNorm uv.2 :=
          mul_le_mul_of_nonneg_right (B₁.one_le_intNorm _) (B₂.intNorm_pos _).le
      _ ≤ X := hw'
  exact ⟨uv, ⟨h1, h2⟩, hw_eq⟩

theorem intCount_sumSystem {B₁ B₂ : BeurlingSystem}
    (h₁ : HasIntegerNorms B₁) (h₂ : HasIntegerNorms B₂)
    (hd₁ : B₁.IsDiscrete) (hd₂ : B₂.IsDiscrete) (n : ℕ) :
    intCount (sumSystem B₁ B₂) (hasIntegerNorms_sumSystem h₁ h₂) n =
      ∑ ab ∈ n.divisorsAntidiagonal, intCount B₁ h₁ ab.1 * intCount B₂ h₂ ab.2 := by
  classical
  rcases eq_or_ne n 0 with rfl | hn
  · simp [intCount_zero]
  · set F : Finset (B₁.Integer × B₂.Integer) :=
      ((hd₁ n).toFinset ×ˢ (hd₂ n).toFinset).filter
        (fun uv => natIntNorm h₁ uv.1 * natIntNorm h₂ uv.2 = n)
    let jF : B₁.Integer × B₂.Integer → (sumSystem B₁ B₂).Integer := joinEquiv
    have hjF_inj : Function.Injective jF := joinEquiv.injective
    have hset : {w : (sumSystem B₁ B₂).Integer |
        natIntNorm (hasIntegerNorms_sumSystem h₁ h₂) w = n} =
        jF '' (F : Set (B₁.Integer × B₂.Integer)) := by
      ext w
      rw [Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro hw
        refine ⟨joinEquiv.symm w, ?_, joinEquiv.apply_symm_apply w⟩
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product,
          Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · have heq := natIntNorm_joinEquiv_sumSystem h₁ h₂ (joinEquiv.symm w).1 (joinEquiv.symm w).2
          rw [joinEquiv.apply_symm_apply, hw] at heq
          rw [Set.mem_setOf_eq, ← natIntNorm_spec h₁]
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ⟨_, heq⟩
        · have heq := natIntNorm_joinEquiv_sumSystem h₁ h₂ (joinEquiv.symm w).1 (joinEquiv.symm w).2
          rw [joinEquiv.apply_symm_apply, hw] at heq
          rw [Set.mem_setOf_eq, ← natIntNorm_spec h₂]
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ⟨_, heq.trans (mul_comm _ _)⟩
        · have heq := natIntNorm_joinEquiv_sumSystem h₁ h₂ (joinEquiv.symm w).1 (joinEquiv.symm w).2
          rw [joinEquiv.apply_symm_apply, hw] at heq
          exact heq.symm
      · rintro ⟨⟨u, v⟩, huvF, rfl⟩
        have huv := (Finset.mem_filter.mp huvF).2
        change natIntNorm (hasIntegerNorms_sumSystem h₁ h₂) (joinEquiv (u, v)) = n
        rw [natIntNorm_joinEquiv_sumSystem h₁ h₂ u v, huv]
    rw [intCount, hset, Set.ncard_image_of_injective _ hjF_inj, Set.ncard_coe_finset]
    have hmaps : ∀ uv ∈ F, (natIntNorm h₁ uv.1, natIntNorm h₂ uv.2) ∈ n.divisorsAntidiagonal :=
      fun uv huv => Nat.mem_divisorsAntidiagonal.mpr ⟨(Finset.mem_filter.mp huv).2, hn⟩
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    refine Finset.sum_congr rfl ?_
    rintro ⟨a, b⟩ hab
    have hab_eq : a * b = n := (Nat.mem_divisorsAntidiagonal.mp hab).1
    have hfib : F.filter (fun uv => (natIntNorm h₁ uv.1, natIntNorm h₂ uv.2) = (a, b)) =
        (finite_fiber_natIntNorm h₁ hd₁ a).toFinset ×ˢ
          (finite_fiber_natIntNorm h₂ hd₂ b).toFinset := by
      ext ⟨u, v⟩
      simp only [F, Finset.mem_filter, Finset.mem_product, Set.Finite.mem_toFinset,
        Set.mem_setOf_eq, Prod.mk.injEq]
      constructor
      · rintro ⟨_, hu, hv⟩
        exact ⟨hu, hv⟩
      · rintro ⟨hu, hv⟩
        refine ⟨⟨⟨?_, ?_⟩, by rw [hu, hv, hab_eq]⟩, hu, hv⟩
        · rw [← natIntNorm_spec h₁, hu]
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn) ⟨b, hab_eq.symm⟩
        · rw [← natIntNorm_spec h₂, hv]
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
            ⟨a, hab_eq.symm.trans (mul_comm a b)⟩
    rw [hfib, Finset.card_product, intCount, intCount,
      Set.ncard_eq_toFinset_card _ (finite_fiber_natIntNorm h₁ hd₁ a),
      Set.ncard_eq_toFinset_card _ (finite_fiber_natIntNorm h₂ hd₂ b)]

/-- Kept primes outside `S` given squared integer norms `p^2`. -/
def sqKeptPrimeSystem (S : Set ℕ) : BeurlingSystem where
  Label := KeptPrime S
  labelNorm p := ((p.1 ^ 2 : ℕ) : ℝ)
  one_lt_labelNorm p := by
    have h2 : 2 ≤ p.1 := p.2.1.two_le
    exact_mod_cast (by nlinarith : 1 < p.1 ^ 2)

theorem hasIntegerNorms_sqKeptPrimeSystem (S : Set ℕ) :
    HasIntegerNorms (sqKeptPrimeSystem S) :=
  fun p => ⟨p.1 ^ 2, rfl⟩

theorem intNorm_sqKeptPrimeSystem (S : Set ℕ) (u : (sqKeptPrimeSystem S).Integer) :
    (sqKeptPrimeSystem S).intNorm u = (((u.map (fun p : KeptPrime S => p.1)).prod ^ 2 : ℕ) : ℝ) := by
  induction u using Multiset.induction_on with
  | empty => simp [BeurlingSystem.intNorm]; rfl
  | cons p u ih =>
    rw [← Multiset.singleton_add, BeurlingSystem.intNorm_add, BeurlingSystem.intNorm_singleton, ih]
    change ((p.1 ^ 2 : ℕ) : ℝ) *
      (((Multiset.map (fun q : KeptPrime S => q.1) u).prod ^ 2 : ℕ) : ℝ) =
      (((Multiset.map (fun q : KeptPrime S => q.1) (p ::ₘ u)).prod ^ 2 : ℕ) : ℝ)
    rw [Multiset.map_cons, Multiset.prod_cons, ← Nat.cast_mul]
    congr 1
    ring

theorem natIntNorm_sqKeptPrimeSystem (S : Set ℕ) (u : (sqKeptPrimeSystem S).Integer) :
    natIntNorm (hasIntegerNorms_sqKeptPrimeSystem S) u =
      (u.map (fun p : KeptPrime S => p.1)).prod ^ 2 := by
  have h := natIntNorm_spec (hasIntegerNorms_sqKeptPrimeSystem S) u
  rw [intNorm_sqKeptPrimeSystem] at h
  exact_mod_cast h

theorem isDiscrete_sqKeptPrimeSystem (S : Set ℕ) : (sqKeptPrimeSystem S).IsDiscrete := by
  intro X
  rcases lt_or_ge X 0 with hX | hX
  · refine Set.Finite.subset Set.finite_empty fun u hu => ?_
    exact absurd ((sqKeptPrimeSystem S).intNorm_pos u) (not_lt.mpr (hu.trans hX.le))
  · have hinj : Function.Injective (fun u : Multiset (KeptPrime S) =>
        (u.map (fun p : KeptPrime S => p.1)).prod ^ 2) :=
      (Nat.pow_left_injective (by decide : 2 ≠ 0)).comp (prod_kept_injective S)
    refine Set.Finite.of_finite_image (f := fun u : Multiset (KeptPrime S) =>
      (u.map (fun p : KeptPrime S => p.1)).prod ^ 2) ?_ hinj.injOn
    refine (Set.finite_Iic ⌊X⌋₊).subset ?_
    rintro n ⟨u, hu, rfl⟩
    rw [Set.mem_setOf_eq, intNorm_sqKeptPrimeSystem] at hu
    exact Nat.le_floor hu

theorem intCount_sqKeptPrimeSystem (S : Set ℕ) (n : ℕ) :
    (intCount (sqKeptPrimeSystem S) (hasIntegerNorms_sqKeptPrimeSystem S) n : ℂ) =
      open Classical in if ∃ m : ℕ, m ^ 2 = n ∧ SFree S m then 1 else 0 := by
  classical
  have hinj : Function.Injective (fun u : (sqKeptPrimeSystem S).Integer =>
      (u.map (fun p : KeptPrime S => p.1)).prod ^ 2) :=
    (Nat.pow_left_injective (by decide : 2 ≠ 0)).comp (prod_kept_injective S)
  split_ifs with hex
  · obtain ⟨m, rfl, hsf⟩ := hex
    obtain ⟨u, hu⟩ := exists_kept_of_sFree S hsf
    set u' : (sqKeptPrimeSystem S).Integer := u
    have hset : {g : (sqKeptPrimeSystem S).Integer |
        natIntNorm (hasIntegerNorms_sqKeptPrimeSystem S) g = m ^ 2} = {u'} := by
      ext g
      rw [Set.mem_setOf_eq, Set.mem_singleton_iff, natIntNorm_sqKeptPrimeSystem]
      exact ⟨fun hg => hinj (hg.trans (congrArg (· ^ 2) hu.symm)),
        fun hg => hg ▸ congrArg (· ^ 2) hu⟩
    rw [intCount, hset, Set.ncard_singleton, Nat.cast_one]
  · have hempty : {g : (sqKeptPrimeSystem S).Integer |
        natIntNorm (hasIntegerNorms_sqKeptPrimeSystem S) g = n} = ∅ := by
      ext g
      rw [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, natIntNorm_sqKeptPrimeSystem]
      intro hg
      exact hex ⟨_, hg, sFree_prod_kept S g⟩
    rw [intCount, hempty, Set.ncard_empty, Nat.cast_zero]

/-- Multiplicative arithmetic indicator of `S`-free positive integers. -/
private def sFreeArith (S : Set ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => (sFreeR S n : ℂ), by simp [sFreeR, SFree]⟩

private theorem isMultiplicative_sFreeArith (S : Set ℕ) : (sFreeArith S).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [sFreeArith, sFreeR, SFree], fun {a b} ha hb _ => ?_⟩
  simp only [sFreeArith, ArithmeticFunction.coe_mk, sFreeR]
  have hab : SFree S (a * b) ↔ SFree S a ∧ SFree S b := by
    simp only [SFree, mul_ne_zero ha hb, ha, hb, ne_eq, not_false_eq_true, true_and,
      Nat.primeFactors_mul ha hb, Finset.mem_union]
    exact ⟨fun h => ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩,
      fun ⟨h1, h2⟩ p hp => hp.elim (h1 p) (h2 p)⟩
  by_cases h1 : SFree S a <;> by_cases h2 : SFree S b
  · rw [if_pos (hab.mpr ⟨h1, h2⟩), if_pos h1, if_pos h2]; simp
  · rw [if_neg (fun h => h2 (hab.mp h).2), if_pos h1, if_neg h2]; simp
  · rw [if_neg (fun h => h1 (hab.mp h).1), if_neg h1]; simp
  · rw [if_neg (fun h => h1 (hab.mp h).1), if_neg h1]; simp

/-- Multiplicative arithmetic indicator of squares of `S`-free positive integers. -/
private def sqSFreeArith (S : Set ℕ) : ArithmeticFunction ℂ :=
  ⟨fun n => open Classical in if ∃ m : ℕ, m ^ 2 = n ∧ SFree S m then 1 else 0, by
    classical
    simp only [ite_eq_right_iff, one_ne_zero]
    rintro ⟨m, hm, hsf⟩
    exact hsf.1 ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hm)⟩

private theorem coprime_sq_factor {a b m : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hcop : a.Coprime b) (hm2 : m ^ 2 = a * b) : (m.gcd a) ^ 2 = a := by
  have hm : m ≠ 0 := fun h => mul_ne_zero ha hb (by rw [← hm2, h]; simp)
  have hg0 : m.gcd a ≠ 0 := Nat.gcd_ne_zero_left hm
  refine Nat.eq_of_factorization_eq (pow_ne_zero 2 hg0) ha fun p => ?_
  rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.factorization_gcd hm ha,
    Finsupp.inf_apply]
  have hsum : 2 * m.factorization p = a.factorization p + b.factorization p := by
    have := congrArg (fun k : ℕ => k.factorization p) hm2
    rwa [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, Nat.factorization_mul ha hb,
      Finsupp.add_apply] at this
  by_cases hap : a.factorization p = 0
  · simp [hap]
  · have hbp : b.factorization p = 0 := by
      by_contra hbp
      have hpa : p ∈ a.primeFactors := Nat.support_factorization a ▸ Finsupp.mem_support_iff.mpr hap
      have hpb : p ∈ b.primeFactors := Nat.support_factorization b ▸ Finsupp.mem_support_iff.mpr hbp
      have hdvd : p ∣ a.gcd b :=
        Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hpa) (Nat.dvd_of_mem_primeFactors hpb)
      rw [hcop.gcd_eq_one] at hdvd
      exact (Nat.prime_of_mem_primeFactors hpa).not_dvd_one hdvd
    omega

private theorem isMultiplicative_sqSFreeArith (S : Set ℕ) : (sqSFreeArith S).IsMultiplicative := by
  classical
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, fun {a b} ha hb hcop => ?_⟩
  · simp only [sqSFreeArith, ArithmeticFunction.coe_mk]
    rw [if_pos ⟨1, one_pow 2, one_ne_zero, by simp⟩]
  · simp only [sqSFreeArith, ArithmeticFunction.coe_mk]
    have hiff : (∃ m : ℕ, m ^ 2 = a * b ∧ SFree S m) ↔
        (∃ m₁ : ℕ, m₁ ^ 2 = a ∧ SFree S m₁) ∧ (∃ m₂ : ℕ, m₂ ^ 2 = b ∧ SFree S m₂) := by
      constructor
      · rintro ⟨m, hm2, hsf⟩
        have hm : m ≠ 0 := hsf.1
        have h1 : (m.gcd a) ^ 2 = a := coprime_sq_factor ha hb hcop hm2
        have h2 : (m.gcd b) ^ 2 = b :=
          coprime_sq_factor hb ha hcop.symm (hm2.trans (mul_comm a b))
        have hs1 : SFree S (m.gcd a) :=
          ⟨Nat.gcd_ne_zero_left hm, fun p hp =>
            hsf.2 p (Nat.primeFactors_mono (Nat.gcd_dvd_left m a) hm hp)⟩
        have hs2 : SFree S (m.gcd b) :=
          ⟨Nat.gcd_ne_zero_left hm, fun p hp =>
            hsf.2 p (Nat.primeFactors_mono (Nat.gcd_dvd_left m b) hm hp)⟩
        exact ⟨⟨m.gcd a, h1, hs1⟩, ⟨m.gcd b, h2, hs2⟩⟩
      · rintro ⟨⟨m₁, h1, hs1⟩, ⟨m₂, h2, hs2⟩⟩
        refine ⟨m₁ * m₂, by rw [mul_pow, h1, h2], mul_ne_zero hs1.1 hs2.1, fun p hp => ?_⟩
        rw [Nat.primeFactors_mul hs1.1 hs2.1, Finset.mem_union] at hp
        exact hp.elim (hs1.2 p) (hs2.2 p)
    by_cases h1 : ∃ m₁ : ℕ, m₁ ^ 2 = a ∧ SFree S m₁ <;>
      by_cases h2 : ∃ m₂ : ℕ, m₂ ^ 2 = b ∧ SFree S m₂
    · rw [if_pos (hiff.mpr ⟨h1, h2⟩), if_pos h1, if_pos h2, mul_one]
    · rw [if_neg (fun h => h2 (hiff.mp h).2), if_pos h1, if_neg h2, mul_zero]
    · rw [if_neg (fun h => h1 (hiff.mp h).1), if_neg h1, zero_mul]
    · rw [if_neg (fun h => h1 (hiff.mp h).1), if_neg h1, zero_mul]

private theorem sFreeArith_prime_pow (S : Set ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    sFreeArith S (p ^ k) = open Classical in if k = 0 ∨ p ∉ S then 1 else 0 := by
  classical
  simp only [sFreeArith, ArithmeticFunction.coe_mk, sFreeR]
  rcases eq_or_ne k 0 with rfl | hk
  · simp [SFree]
  · have hpf : (p ^ k).primeFactors = {p} := Nat.primeFactors_prime_pow hk hp
    have hsf : SFree S (p ^ k) ↔ p ∉ S := by
      simp only [SFree, pow_ne_zero k hp.ne_zero, ne_eq, not_false_eq_true, true_and, hpf,
        Finset.mem_singleton, forall_eq]
    simp only [hk, false_or]
    by_cases hpS : p ∉ S
    · rw [if_pos (hsf.mpr hpS), if_pos hpS]; norm_num
    · rw [if_neg (mt hsf.mp hpS), if_neg hpS]; norm_num

private theorem sqSFreeArith_prime_pow (S : Set ℕ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    sqSFreeArith S (p ^ k) = open Classical in if Even k ∧ (k = 0 ∨ p ∉ S) then 1 else 0 := by
  classical
  simp only [sqSFreeArith, ArithmeticFunction.coe_mk]
  have hiff : (∃ m : ℕ, m ^ 2 = p ^ k ∧ SFree S m) ↔ Even k ∧ (k = 0 ∨ p ∉ S) := by
    constructor
    · rintro ⟨m, hm2, hsf⟩
      have hfac := congrArg (fun n : ℕ => n.factorization p) hm2
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hp.factorization_pow,
        Finsupp.single_eq_same] at hfac
      refine ⟨⟨m.factorization p, by omega⟩, ?_⟩
      rcases eq_or_ne k 0 with rfl | hk
      · exact Or.inl rfl
      · refine Or.inr (hsf.2 p ?_)
        have hdvd : p ∣ m ^ 2 := hm2 ▸ dvd_pow_self p hk
        exact Nat.mem_primeFactors.mpr ⟨hp, hp.dvd_of_dvd_pow hdvd, hsf.1⟩
    · rintro ⟨⟨r, rfl⟩, hcond⟩
      refine ⟨p ^ r, by rw [sq, ← pow_add], pow_ne_zero r hp.ne_zero, fun q hq => ?_⟩
      rcases eq_or_ne r 0 with rfl | hr
      · simp at hq
      · rw [Nat.primeFactors_prime_pow hr hp, Finset.mem_singleton] at hq
        subst hq
        exact hcond.resolve_left (by omega)
  by_cases h : Even k ∧ (k = 0 ∨ p ∉ S)
  · rw [if_pos (hiff.mpr h), if_pos h]
  · rw [if_neg (mt hiff.mp h), if_neg h]

/-- **Quadratic-character Euler-factor Beurling system.**
For a quadratic Dirichlet character `χ` modulo `N`, each rational prime `p` contributes:
* two prime labels of norm `p` when `χ(p) = 1`,
* one prime label of norm `p` when `χ(p) = 0`,
* one prime label of norm `p^2` when `χ(p) = −1`,
realizing `(1 − p^{−s})^{−1} (1 − χ(p) p^{−s})^{−1}` factor by factor. -/
def quadraticCharacterSystem {N : ℕ} (χ : DirichletCharacter ℂ N) : BeurlingSystem :=
  sumSystem (keptPrimeSystem {p : ℕ | χ (p : ZMod N) = -1})
    (sumSystem (keptPrimeSystem {p : ℕ | χ (p : ZMod N) ≠ 1})
      (sqKeptPrimeSystem {p : ℕ | χ (p : ZMod N) ≠ -1}))

theorem hasIntegerNorms_quadraticCharacterSystem {N : ℕ} (χ : DirichletCharacter ℂ N) :
    HasIntegerNorms (quadraticCharacterSystem χ) :=
  hasIntegerNorms_sumSystem (hasIntegerNorms_keptPrimeSystem _)
    (hasIntegerNorms_sumSystem (hasIntegerNorms_keptPrimeSystem _)
      (hasIntegerNorms_sqKeptPrimeSystem _))

theorem isDiscrete_quadraticCharacterSystem {N : ℕ} (χ : DirichletCharacter ℂ N) :
    (quadraticCharacterSystem χ).IsDiscrete :=
  isDiscrete_sumSystem (isDiscrete_keptPrimeSystem _)
    (isDiscrete_sumSystem (isDiscrete_keptPrimeSystem _)
      (isDiscrete_sqKeptPrimeSystem _))

/-- For any quadratic character `χ` (`χ^2 = 1`) of positive modulus `N`, `quadraticCharacterSystem χ`
is never norm-equivalent to the rational primes: at any prime `p₀ ∣ N + 1`, `χ(p₀) ∈ {±1}` either
deletes norm `p₀` (`χ(p₀) = −1`) or duplicates norm `p₀` (`χ(p₀) = 1`). -/
theorem notNormEquivPrimes_quadraticCharacterSystem {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hq : χ ^ 2 = 1) :
    NotNormEquivPrimes (quadraticCharacterSystem χ) := by
  rintro ⟨⟨e, he⟩⟩
  have hN1 : N + 1 ≠ 1 := by have := NeZero.pos N; omega
  set p₀ : ℕ := (N + 1).minFac
  have hp₀ : p₀.Prime := Nat.minFac_prime hN1
  obtain ⟨k, hk⟩ := Nat.minFac_dvd (N + 1)
  have hunit : (p₀ : ZMod N) * (k : ZMod N) = 1 := by
    have : ((p₀ * k : ℕ) : ZMod N) = ((N + 1 : ℕ) : ZMod N) := congrArg Nat.cast hk.symm
    push_cast at this
    rw [ZMod.natCast_self, zero_add] at this
    exact this
  have hne0 : χ (p₀ : ZMod N) ≠ 0 := by
    intro h0
    have hmul : χ ((p₀ : ZMod N) * (k : ZMod N)) = 0 := by rw [map_mul, h0, zero_mul]
    rw [hunit, map_one] at hmul
    exact one_ne_zero hmul
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hq (p₀ : ZMod N) with h0 | hpos | hneg
  · exact hne0 h0
  · -- `χ(p₀) = 1`: two distinct prime labels of norm `p₀`.
    have hpos_not_neg : χ (p₀ : ZMod N) ≠ -1 := by rw [hpos]; norm_num
    let l₁ : (quadraticCharacterSystem χ).Label := Sum.inl ⟨p₀, hp₀, hpos_not_neg⟩
    let l₂ : (quadraticCharacterSystem χ).Label :=
      Sum.inr (Sum.inl ⟨p₀, hp₀, not_not.mpr hpos⟩)
    have hl₁ : ((e l₁ : ℕ) : ℝ) = (p₀ : ℝ) := (he l₁).symm
    have hl₂ : ((e l₂ : ℕ) : ℝ) = (p₀ : ℝ) := (he l₂).symm
    have heq : e l₁ = e l₂ := Subtype.ext (by exact_mod_cast hl₁.trans hl₂.symm)
    exact Sum.inl_ne_inr (e.injective heq)
  · -- `χ(p₀) = −1`: no prime label has norm `p₀`.
    set l := e.symm ⟨p₀, hp₀⟩
    have hl : (quadraticCharacterSystem χ).labelNorm l = (p₀ : ℝ) := by
      have h := he l
      rwa [e.apply_symm_apply] at h
    rcases l with q | (q | q)
    · change (q.1 : ℝ) = (p₀ : ℝ) at hl
      have hqp : q.1 = p₀ := by exact_mod_cast hl
      exact q.2.2 (hqp ▸ hneg)
    · change (q.1 : ℝ) = (p₀ : ℝ) at hl
      have hqp : q.1 = p₀ := by exact_mod_cast hl
      apply q.2.2
      change χ (q.1 : ZMod N) ≠ 1
      rw [hqp, hneg]
      norm_num
    · change ((q.1 ^ 2 : ℕ) : ℝ) = (p₀ : ℝ) at hl
      have hqp : q.1 ^ 2 = p₀ := by exact_mod_cast hl
      have hdvd : q.1 ∣ p₀ := ⟨q.1, by rw [← sq, hqp]⟩
      rcases hp₀.eq_one_or_self_of_dvd q.1 hdvd with h1 | hself
      · exact absurd h1 q.2.1.ne_one
      · have := q.2.1.two_le
        nlinarith

/-- For any quadratic character `χ` (`χ^2 = 1`), the generalized-integer multiplicity of
`quadraticCharacterSystem χ` at `n` equals `(1 ⋆ χ)(n) = χ.zetaMul n`. -/
theorem intCount_quadraticCharacterSystem {N : ℕ} {χ : DirichletCharacter ℂ N}
    (hq : χ ^ 2 = 1) (n : ℕ) :
    (intCount (quadraticCharacterSystem χ) (hasIntegerNorms_quadraticCharacterSystem χ) n : ℂ) =
      χ.zetaMul n := by
  classical
  set S₁ : Set ℕ := {p : ℕ | χ (p : ZMod N) = -1}
  set S₂ : Set ℕ := {p : ℕ | χ (p : ZMod N) ≠ 1}
  set S₃ : Set ℕ := {p : ℕ | χ (p : ZMod N) ≠ -1}
  have hconv_val :
      (intCount (quadraticCharacterSystem χ) (hasIntegerNorms_quadraticCharacterSystem χ) n : ℂ) =
        (sFreeArith S₁ * (sFreeArith S₂ * sqSFreeArith S₃)) n := by
    unfold quadraticCharacterSystem hasIntegerNorms_quadraticCharacterSystem
    rw [intCount_sumSystem _ _
        (isDiscrete_keptPrimeSystem S₁)
        (isDiscrete_sumSystem (isDiscrete_keptPrimeSystem S₂) (isDiscrete_sqKeptPrimeSystem S₃)),
      Nat.cast_sum, ArithmeticFunction.mul_apply]
    refine Finset.sum_congr rfl fun ab _ => ?_
    rw [Nat.cast_mul]
    congr 1
    · have := intCount_keptPrimeSystem S₁ ab.1
      exact_mod_cast this
    · rw [intCount_sumSystem _ _ (isDiscrete_keptPrimeSystem S₂) (isDiscrete_sqKeptPrimeSystem S₃),
        Nat.cast_sum, ArithmeticFunction.mul_apply]
      refine Finset.sum_congr rfl fun cd _ => ?_
      rw [Nat.cast_mul, intCount_sqKeptPrimeSystem S₃ cd.2]
      congr 1
      have := intCount_keptPrimeSystem S₂ cd.1
      exact_mod_cast this
  rw [hconv_val]
  have hmult : (sFreeArith S₁ * (sFreeArith S₂ * sqSFreeArith S₃)).IsMultiplicative :=
    (isMultiplicative_sFreeArith S₁).mul
      ((isMultiplicative_sFreeArith S₂).mul (isMultiplicative_sqSFreeArith S₃))
  suffices hfn : sFreeArith S₁ * (sFreeArith S₂ * sqSFreeArith S₃) = χ.zetaMul by rw [hfn]
  rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hmult _
    χ.isMultiplicative_zetaMul]
  intro p k hp
  rw [zetaMul_prime_pow_eq χ hp k, RHTower.mul_apply_prime_pow _ _ hp]
  have inner_eq : ∀ j : ℕ, (sFreeArith S₂ * sqSFreeArith S₃) (p ^ j) =
      ∑ r ∈ Finset.range (j + 1), sFreeArith S₂ (p ^ r) * sqSFreeArith S₃ (p ^ (j - r)) :=
    fun j => RHTower.mul_apply_prime_pow _ _ hp
  simp_rw [inner_eq, sFreeArith_prime_pow _ hp, sqSFreeArith_prime_pow _ hp]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hq (p : ZMod N) with h0 | h1 | hm1
  · -- `χ(p) = 0`: `p ∉ S₁`, `p ∈ S₂`, `p ∈ S₃`.
    have hp1 : p ∉ S₁ := by simp [S₁, h0]
    have hp2 : p ∈ S₂ := by simp [S₂, h0]
    have hp3 : p ∈ S₃ := by simp [S₃, h0]
    simp only [hp1, not_false_eq_true, or_true, ↓reduceIte, one_mul, hp2, not_true_eq_false,
      or_false, hp3, h0]
    have hinner : ∀ j : ℕ, (∑ r ∈ Finset.range (j + 1),
        (if r = 0 then (1 : ℂ) else 0) * if Even (j - r) ∧ j - r = 0 then 1 else 0) =
        if j = 0 then 1 else 0 := by
      intro j
      rw [Finset.sum_eq_single 0]
      · rcases eq_or_ne j 0 with rfl | hj <;> simp [hj]
      · intro r _ hr0; simp [hr0]
      · simp
    simp_rw [hinner]
    rw [Finset.sum_eq_single k, Finset.sum_eq_single 0]
    · simp
    · intro t _ ht0; exact zero_pow ht0
    · simp
    · intro i hi hik
      have hne : k - i ≠ 0 := by rw [Finset.mem_range] at hi; omega
      simp [hne]
    · simp
  · -- `χ(p) = 1`: `p ∉ S₁`, `p ∉ S₂`, `p ∈ S₃`.
    have hp1 : p ∉ S₁ := by simp [S₁, h1]
    have hp2 : p ∉ S₂ := by simp [S₂, h1]
    have hp3 : p ∈ S₃ := by simp [S₃, h1]
    simp only [hp1, hp2, not_false_eq_true, or_true, ↓reduceIte, one_mul, hp3,
      not_true_eq_false, or_false, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
    have hinner : ∀ j : ℕ,
        (∑ r ∈ Finset.range (j + 1), if Even (j - r) ∧ j - r = 0 then (1 : ℂ) else 0) = 1 := by
      intro j
      rw [Finset.sum_eq_single j]
      · simp
      · intro r hr hrj
        have hne : j - r ≠ 0 := by rw [Finset.mem_range] at hr; omega
        simp [hne]
      · simp
    simp_rw [hinner]
    simp
  · -- `χ(p) = −1`: `p ∈ S₁`, `p ∈ S₂`, `p ∉ S₃`.
    have hp1 : p ∈ S₁ := by simp [S₁, hm1]
    have hp2 : p ∈ S₂ := by simp [S₂, hm1]
    have hp3 : p ∉ S₃ := by simp [S₃, hm1]
    simp only [hp1, hp2, not_true_eq_false, or_false, hp3, not_false_eq_true, or_true, and_true,
      hm1, neg_one_geom_sum]
    have hinner : ∀ j : ℕ, (∑ r ∈ Finset.range (j + 1),
        (if r = 0 then (1 : ℂ) else 0) * if Even (j - r) then 1 else 0) =
        if Even j then 1 else 0 := by
      intro j
      rw [Finset.sum_eq_single 0]
      · simp
      · intro r _ hr0; simp [hr0]
      · simp
    simp_rw [hinner]
    rw [Finset.sum_eq_single 0]
    · simp only [↓reduceIte, tsub_zero, one_mul]
      rw [Nat.even_add_one]
      by_cases hk : Even k <;> simp [hk]
    · intro i _ hi0; simp [hi0]
    · simp

/-- **Dirichlet hyperbola count law for `quadraticCharacterSystem χ`.**
For a nontrivial quadratic character `χ` modulo `N`,
`|N_B(x) − L(1, χ) x| ≤ (6 N + 1) x^{1/2}` for all `x ≥ 1`, with `L(1, χ) > 0`. -/
theorem quadraticCharacterSystem_count_sub_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hq : χ ^ 2 = 1) (hχ : χ ≠ 1) :
    0 < (DirichletCharacter.LFunction χ 1).re ∧
      ∀ x : ℝ, 1 ≤ x →
        |((quadraticCharacterSystem χ).countBall x : ℝ) -
            (DirichletCharacter.LFunction χ 1).re * x| ≤
          (6 * (N : ℝ) + 1) * x ^ (1 / 2 : ℝ) := by
  classical
  obtain ⟨hLpos, hLim⟩ := LFunction_one_pos hq hχ
  refine ⟨hLpos, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  set X : ℕ := ⌊x⌋₊
  have hX1 : 1 ≤ X := Nat.le_floor (by exact_mod_cast hx : ((1 : ℕ) : ℝ) ≤ x)
  set M : ℕ := Nat.sqrt X
  have hM2 : M * M ≤ X := Nat.sqrt_le X
  have hX_lt : X < (M + 1) * (M + 1) := Nat.lt_succ_sqrt X
  have hM_le_sq : (M : ℝ) ≤ x ^ (1 / 2 : ℝ) := by
    have hMX : (M : ℝ) ^ 2 ≤ x := by
      calc (M : ℝ) ^ 2 = ((M * M : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (X : ℝ) := by exact_mod_cast hM2
        _ ≤ x := Nat.floor_le hx0.le
    calc (M : ℝ) = ((M : ℝ) ^ 2) ^ (1 / 2 : ℝ) := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (Nat.cast_nonneg M)]; norm_num
      _ ≤ x ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by positivity) hMX (by norm_num)
  have hsq_le_M1 : x ^ (1 / 2 : ℝ) ≤ (M : ℝ) + 1 := by
    have hxM1 : x ≤ ((M : ℝ) + 1) ^ 2 := by
      have h1 : x < (X : ℝ) + 1 := Nat.lt_floor_add_one x
      have h2 : (X : ℝ) + 1 ≤ (((M + 1) * (M + 1) : ℕ) : ℝ) := by exact_mod_cast hX_lt
      calc x ≤ (X : ℝ) + 1 := h1.le
        _ ≤ (((M + 1) * (M + 1) : ℕ) : ℝ) := h2
        _ = ((M : ℝ) + 1) ^ 2 := by push_cast; ring
    calc x ^ (1 / 2 : ℝ) ≤ (((M : ℝ) + 1) ^ 2) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow hx0.le hxM1 (by norm_num)
      _ = (M : ℝ) + 1 := by
          rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]; norm_num
  -- Express `(countBall x : ℂ)` as `∑_{1 ≤ n ≤ X} χ.zetaMul n`.
  have hcount_C : (((quadraticCharacterSystem χ).countBall x : ℝ) : ℂ) =
      ∑ n ∈ Finset.Icc 1 X, χ.zetaMul n := by
    rw [countBall_eq_sum_intCount (hasIntegerNorms_quadraticCharacterSystem χ)
      (isDiscrete_quadraticCharacterSystem χ) hx0.le, Nat.cast_sum, Complex.ofReal_sum]
    simp_rw [Complex.ofReal_natCast, intCount_quadraticCharacterSystem hq]
    have hIic : Finset.Iic X = insert 0 (Finset.Icc 1 X) := by
      ext n; simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hIic, Finset.sum_insert (by simp), ArithmeticFunction.map_zero, zero_add]
  -- Hyperbola decomposition of `∑_{1 ≤ n ≤ X} (1 ⋆ χ)(n)`.
  set H : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 X ×ˢ Finset.Icc 1 X).filter (fun p => p.1 * p.2 ≤ X)
  have hH_sum : ∑ n ∈ Finset.Icc 1 X, χ.zetaMul n = ∑ p ∈ H, χ (p.2 : ZMod N) := by
    have hmaps : ∀ p ∈ H, p.1 * p.2 ∈ Finset.Icc 1 X := by
      intro p hp
      obtain ⟨hp_prod, hle⟩ := Finset.mem_filter.mp hp
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hp_prod
      exact Finset.mem_Icc.mpr
        ⟨Nat.mul_pos (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1, hle⟩
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
    have hnX : n ≤ X := (Finset.mem_Icc.mp hn).2
    have hfib_eq : H.filter (fun p => p.1 * p.2 = n) = n.divisorsAntidiagonal := by
      ext ⟨a, b⟩
      simp only [H, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
        Nat.mem_divisorsAntidiagonal]
      constructor
      · rintro ⟨_, hab⟩; exact ⟨hab, hn0⟩
      · rintro ⟨hab, -⟩
        have ha0 : 1 ≤ a := Nat.pos_of_ne_zero (left_ne_zero_of_mul (hab ▸ hn0))
        have hb0 : 1 ≤ b := Nat.pos_of_ne_zero (right_ne_zero_of_mul (hab ▸ hn0))
        exact ⟨⟨⟨⟨ha0, (Nat.le_mul_of_pos_right a hb0).trans (hab.le.trans hnX)⟩,
          ⟨hb0, (Nat.le_mul_of_pos_left b ha0).trans (hab.le.trans hnX)⟩⟩, hab.le.trans hnX⟩, hab⟩
    rw [DirichletCharacter.zetaMul, ArithmeticFunction.mul_apply, hfib_eq]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp1 : p.1 ≠ 0 := left_ne_zero_of_mul ((Nat.mem_divisorsAntidiagonal.mp hp).1 ▸ hn0)
    have hp2 : p.2 ≠ 0 := right_ne_zero_of_mul ((Nat.mem_divisorsAntidiagonal.mp hp).1 ▸ hn0)
    simp [ArithmeticFunction.zeta, ArithmeticFunction.toArithmeticFunction, hp1, hp2]
  -- Split `H` along `p.1 ≤ M` vs `M < p.1` (forcing `p.2 ≤ M`).
  have hsplit : ∑ p ∈ H, χ (p.2 : ZMod N) =
      (∑ p ∈ H with p.1 ≤ M, χ (p.2 : ZMod N)) +
        ∑ p ∈ H with ¬ p.1 ≤ M, χ (p.2 : ZMod N) :=
    (Finset.sum_filter_add_sum_filter_not H (fun p => p.1 ≤ M) _).symm
  have hA_eq : ∑ p ∈ H with p.1 ≤ M, χ (p.2 : ZMod N) =
      ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 (X / a), χ (b : ZMod N) := by
    have heqset : H.filter (fun p => p.1 ≤ M) =
        (Finset.Icc 1 M).biUnion (fun a => (Finset.Icc 1 (X / a)).map
          ⟨fun b => (a, b), fun _ _ h => (Prod.mk.inj h).2⟩) := by
      ext ⟨a, b⟩
      simp only [H, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_biUnion,
        Finset.mem_map, Function.Embedding.coeFn_mk, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨⟨⟨ha1, _⟩, ⟨hb1, _⟩⟩, hab⟩, haM⟩
        exact ⟨a, ⟨ha1, haM⟩, b, ⟨hb1, (Nat.le_div_iff_mul_le ha1).mpr (by rwa [mul_comm])⟩,
          rfl, rfl⟩
      · rintro ⟨a', ⟨ha1, haM⟩, b', ⟨hb1, hbdiv⟩, rfl, rfl⟩
        have hab : a' * b' ≤ X := by
          rw [mul_comm]; exact (Nat.le_div_iff_mul_le ha1).mp hbdiv
        have haX : a' ≤ X := haM.trans ((Nat.le_mul_self M).trans hM2)
        have hbX : b' ≤ X := (Nat.le_mul_of_pos_left b' ha1).trans hab
        exact ⟨⟨⟨⟨ha1, haX⟩, ⟨hb1, hbX⟩⟩, hab⟩, haM⟩
    rw [heqset, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun a _ => by simp
    · intro a₁ _ a₂ _ hne
      refine Finset.disjoint_left.mpr fun p hp₁ hp₂ => ?_
      obtain ⟨b₁, _, he₁⟩ := Finset.mem_map.mp hp₁
      obtain ⟨b₂, _, he₂⟩ := Finset.mem_map.mp hp₂
      exact hne (congrArg Prod.fst (he₁.trans he₂.symm))
  have hB_eq : ∑ p ∈ H with ¬ p.1 ≤ M, χ (p.2 : ZMod N) =
      ∑ b ∈ Finset.Icc 1 M, ((X / b - M : ℕ) : ℂ) * χ (b : ZMod N) := by
    have heqset : H.filter (fun p => ¬ p.1 ≤ M) =
        (Finset.Icc 1 M).biUnion (fun b => (Finset.Ioc M (X / b)).map
          ⟨fun a => (a, b), fun _ _ h => (Prod.mk.inj h).1⟩) := by
      ext ⟨a, b⟩
      simp only [H, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_biUnion,
        Finset.mem_map, Finset.mem_Ioc, Function.Embedding.coeFn_mk, Prod.mk.injEq, not_le]
      constructor
      · rintro ⟨⟨⟨_, ⟨hb1, _⟩⟩, hab⟩, haM⟩
        have hbM : b ≤ M := by
          by_contra hbM; push Not at hbM
          have : (M + 1) * (M + 1) ≤ a * b := Nat.mul_le_mul haM hbM
          omega
        exact ⟨b, ⟨hb1, hbM⟩, a, ⟨haM, (Nat.le_div_iff_mul_le hb1).mpr hab⟩, rfl, rfl⟩
      · rintro ⟨b', ⟨hb1, hbM⟩, a', ⟨haM, hadiv⟩, rfl, rfl⟩
        have hab : a' * b' ≤ X := (Nat.le_div_iff_mul_le hb1).mp hadiv
        have ha1 : 1 ≤ a' := by omega
        exact ⟨⟨⟨⟨ha1, (Nat.le_mul_of_pos_right a' hb1).trans hab⟩,
          ⟨hb1, (Nat.le_mul_of_pos_left b' ha1).trans hab⟩⟩, hab⟩, haM⟩
    rw [heqset, Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun b _ => ?_
      simp [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
    · intro b₁ _ b₂ _ hne
      refine Finset.disjoint_left.mpr fun p hp₁ hp₂ => ?_
      obtain ⟨a₁, _, he₁⟩ := Finset.mem_map.mp hp₁
      obtain ⟨a₂, _, he₂⟩ := Finset.mem_map.mp hp₂
      exact hne (congrArg Prod.snd (he₁.trans he₂.symm))
  -- Partial character sum bound on `Finset.Icc 1 K`.
  have hchar_Icc : ∀ K : ℕ, ‖∑ b ∈ Finset.Icc 1 K, χ (b : ZMod N)‖ ≤ N := by
    intro K
    have hN1 : 1 < N := by
      by_contra hle1
      have hN_eq : N = 1 := by have := NeZero.pos N; omega
      subst hN_eq
      exact hχ (by ext a; rw [Subsingleton.elim a 1, map_one]; simp)
    haveI : Fact (1 < N) := ⟨hN1⟩
    have heq : ∑ b ∈ Finset.Icc 1 K, χ (b : ZMod N) =
        ∑ m ∈ Finset.range (K + 1), χ (m : ZMod N) := by
      have h0 : χ (0 : ZMod N) = 0 := map_zero χ
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos K),
        Nat.cast_zero, h0, zero_add]
      rfl
    rw [heq]
    exact norm_dirichletCharacter_sum_range_le χ hχ (K + 1)
  have hA_norm : ‖∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 (X / a), χ (b : ZMod N)‖ ≤
      (N : ℝ) * x ^ (1 / 2 : ℝ) := by
    calc ‖∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 (X / a), χ (b : ZMod N)‖
        ≤ ∑ a ∈ Finset.Icc 1 M, ‖∑ b ∈ Finset.Icc 1 (X / a), χ (b : ZMod N)‖ := norm_sum_le _ _
      _ ≤ ∑ _a ∈ Finset.Icc 1 M, (N : ℝ) := Finset.sum_le_sum fun a _ => hchar_Icc (X / a)
      _ = (M : ℝ) * N := by simp [Nat.card_Icc]
      _ ≤ x ^ (1 / 2 : ℝ) * N := mul_le_mul_of_nonneg_right hM_le_sq (Nat.cast_nonneg N)
      _ = (N : ℝ) * x ^ (1 / 2 : ℝ) := mul_comm _ _
  -- Decompose Piece B into `x * dirichletPartialSum + frac_err - M * char_sum`.
  have hB_decomp : ∑ b ∈ Finset.Icc 1 M, ((X / b - M : ℕ) : ℂ) * χ (b : ZMod N) =
      (x : ℂ) * dirichletPartialSum (fun j => χ (j + 1)) M 1 +
        (∑ b ∈ Finset.Icc 1 M, (((X / b : ℕ) : ℝ) - x / b : ℂ) * χ (b : ZMod N)) -
        (M : ℂ) * ∑ b ∈ Finset.Icc 1 M, χ (b : ZMod N) := by
    have hsub_cast : ∀ b ∈ Finset.Icc 1 M,
        ((X / b - M : ℕ) : ℂ) * χ (b : ZMod N) =
          (((X / b : ℕ) : ℝ) : ℂ) * χ (b : ZMod N) - (M : ℂ) * χ (b : ZMod N) := by
      intro b hb
      obtain ⟨hb1, hbM⟩ := Finset.mem_Icc.mp hb
      have hle : M ≤ X / b := (Nat.le_div_iff_mul_le hb1).mpr
        ((Nat.mul_le_mul_left M hbM).trans hM2)
      rw [Nat.cast_sub hle]
      push_cast; ring
    rw [Finset.sum_congr rfl hsub_cast, Finset.sum_sub_distrib, ← Finset.mul_sum]
    congr 1
    have hdir : (x : ℂ) * dirichletPartialSum (fun j => χ (j + 1)) M 1 =
        ∑ b ∈ Finset.Icc 1 M, ((x / b : ℝ) : ℂ) * χ (b : ZMod N) := by
      unfold dirichletPartialSum
      rw [Finset.mul_sum, Finset.Icc_eq_Ico,
        ← Finset.sum_Ico_add (fun j => ((x / ((j + 1 : ℕ) : ℝ) : ℝ) : ℂ) * χ ((j + 1 : ℕ) : ZMod N)) 0 M,
        Finset.range_eq_Ico]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hcpow : (((j : ℝ) + 1 : ℂ)) ^ (-(1 : ℂ)) = (((j + 1 : ℕ) : ℝ)⁻¹ : ℂ) := by
        rw [cpow_neg_one]
        push_cast; rfl
      rw [hcpow]
      push_cast; ring
    rw [hdir, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast; ring
  have hB1_norm : ‖(x : ℂ) * dirichletPartialSum (fun j => χ (j + 1)) M 1 -
      DirichletCharacter.LFunction χ 1 * (x : ℂ)‖ ≤ 4 * (N : ℝ) * x ^ (1 / 2 : ℝ) := by
    have htr := norm_LFunction_sub_character_partial_le hχ (s := 1) (by norm_num) M
    simp only [Complex.one_re, norm_one, div_one, Real.rpow_neg_one] at htr
    have heq : (x : ℂ) * dirichletPartialSum (fun j => χ (j + 1)) M 1 -
        DirichletCharacter.LFunction χ 1 * (x : ℂ) =
        -(x : ℂ) * (DirichletCharacter.LFunction χ 1 -
          dirichletPartialSum (fun j => χ (j + 1)) M 1) := by ring
    rw [heq, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hx0.le]
    calc x * ‖DirichletCharacter.LFunction χ 1 - dirichletPartialSum (fun j => χ (j + 1)) M 1‖
        ≤ x * (2 * N * (1 + 1) * ((M : ℝ) + 1)⁻¹) :=
          mul_le_mul_of_nonneg_left htr hx0.le
      _ = 4 * (N : ℝ) * (x / ((M : ℝ) + 1)) := by ring
      _ ≤ 4 * (N : ℝ) * (x / x ^ (1 / 2 : ℝ)) := by
          gcongr
          exact Real.rpow_pos_of_pos hx0 _
      _ = 4 * (N : ℝ) * x ^ (1 / 2 : ℝ) := by
          congr 1
          conv_lhs => rw [← Real.rpow_one x]
          rw [← Real.rpow_sub hx0]
          norm_num
  have hB2_norm : ‖∑ b ∈ Finset.Icc 1 M, (((X / b : ℕ) : ℝ) - x / b : ℂ) * χ (b : ZMod N)‖ ≤
      x ^ (1 / 2 : ℝ) := by
    calc _ ≤ ∑ b ∈ Finset.Icc 1 M, ‖(((X / b : ℕ) : ℝ) - x / b : ℂ) * χ (b : ZMod N)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _b ∈ Finset.Icc 1 M, (1 : ℝ) := by
          refine Finset.sum_le_sum fun b hb => ?_
          have hb0 : (0 : ℝ) < b := by exact_mod_cast (Finset.mem_Icc.mp hb).1
          have hsub_real : (((X / b : ℕ) : ℝ) - x / b : ℂ) =
              ((((X / b : ℕ) : ℝ) - x / b : ℝ) : ℂ) := by push_cast; rfl
          rw [norm_mul, hsub_real, Complex.norm_real, Real.norm_eq_abs]
          have hfl : X / b = ⌊x / b⌋₊ := (Nat.floor_div_natCast x b).symm
          rw [hfl]
          have h1 : (⌊x / b⌋₊ : ℝ) ≤ x / b := Nat.floor_le (div_nonneg hx0.le hb0.le)
          have h2 : x / b - 1 < (⌊x / b⌋₊ : ℝ) :=
            sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one _)
          have habs : |(⌊x / b⌋₊ : ℝ) - x / b| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
          calc |(⌊x / b⌋₊ : ℝ) - x / b| * ‖χ (b : ZMod N)‖
              ≤ 1 * 1 := mul_le_mul habs (χ.norm_le_one _) (norm_nonneg _) zero_le_one
            _ = 1 := one_mul 1
      _ = (M : ℝ) := by simp [Nat.card_Icc]
      _ ≤ x ^ (1 / 2 : ℝ) := hM_le_sq
  have hB3_norm : ‖(M : ℂ) * ∑ b ∈ Finset.Icc 1 M, χ (b : ZMod N)‖ ≤
      (N : ℝ) * x ^ (1 / 2 : ℝ) := by
    rw [norm_mul, Complex.norm_natCast]
    calc (M : ℝ) * ‖∑ b ∈ Finset.Icc 1 M, χ (b : ZMod N)‖
        ≤ x ^ (1 / 2 : ℝ) * N := mul_le_mul hM_le_sq (hchar_Icc M) (norm_nonneg _) (by positivity)
      _ = (N : ℝ) * x ^ (1 / 2 : ℝ) := mul_comm _ _
  -- Combine all pieces via real part projection.
  have hLreal : DirichletCharacter.LFunction χ 1 = ((DirichletCharacter.LFunction χ 1).re : ℂ) := by
    apply Complex.ext <;> simp [hLim]
  have htot : ‖(((quadraticCharacterSystem χ).countBall x : ℝ) -
      (DirichletCharacter.LFunction χ 1).re * x : ℂ)‖ ≤
      (6 * (N : ℝ) + 1) * x ^ (1 / 2 : ℝ) := by
    have hcast : (((quadraticCharacterSystem χ).countBall x : ℝ) -
        (DirichletCharacter.LFunction χ 1).re * x : ℂ) =
        (((quadraticCharacterSystem χ).countBall x : ℝ) : ℂ) -
          DirichletCharacter.LFunction χ 1 * (x : ℂ) := by
      conv_rhs => rw [hLreal]
      push_cast; ring
    rw [hcast, hcount_C, hH_sum, hsplit, hA_eq, hB_eq, hB_decomp]
    set S_A := ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 (X / a), χ (b : ZMod N)
    set S_B1 := (x : ℂ) * dirichletPartialSum (fun j => χ (j + 1)) M 1 -
      DirichletCharacter.LFunction χ 1 * (x : ℂ)
    set S_B2 := ∑ b ∈ Finset.Icc 1 M, (((X / b : ℕ) : ℝ) - x / b : ℂ) * χ (b : ZMod N)
    set S_B3 := (M : ℂ) * ∑ b ∈ Finset.Icc 1 M, χ (b : ZMod N)
    have hid : S_A + ((x : ℂ) * dirichletPartialSum (fun j => χ (j + 1)) M 1 + S_B2 - S_B3) -
        DirichletCharacter.LFunction χ 1 * (x : ℂ) = S_A + S_B1 + S_B2 - S_B3 := by ring
    rw [hid]
    calc ‖S_A + S_B1 + S_B2 - S_B3‖
        ≤ ‖S_A + S_B1 + S_B2‖ + ‖S_B3‖ := norm_sub_le _ _
      _ ≤ ‖S_A + S_B1‖ + ‖S_B2‖ + ‖S_B3‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖S_A‖ + ‖S_B1‖ + ‖S_B2‖ + ‖S_B3‖ := by gcongr; exact norm_add_le _ _
      _ ≤ (N : ℝ) * x ^ (1 / 2 : ℝ) + 4 * (N : ℝ) * x ^ (1 / 2 : ℝ) +
          x ^ (1 / 2 : ℝ) + (N : ℝ) * x ^ (1 / 2 : ℝ) := by
          gcongr
      _ = (6 * (N : ℝ) + 1) * x ^ (1 / 2 : ℝ) := by ring
  rwa [← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at htot

/-- Analytic continuation `(s − 1) ζ_B(s) = ζ_u(s) L(s, χ)` of `quadraticCharacterSystem χ`. -/
theorem quadraticCharacterSystem_zetaSeriesC_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hq : χ ^ 2 = 1) (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    (s - 1) * (quadraticCharacterSystem χ).zetaSeriesC s =
      zetaResidueUnit s * DirichletCharacter.LFunction χ s := by
  obtain ⟨_, hcnt⟩ := quadraticCharacterSystem_count_sub_le hq hχ
  have hLin := hasLinearCounting_of_count_sub_le (by norm_num : (1 / 2 : ℝ) ≤ 1) hcnt
  have hZr := (quadraticCharacterSystem χ).summable_intNorm_rpow
    (isDiscrete_quadraticCharacterSystem χ) hLin hs
  rw [(zetaSeriesC_eq_LSeries_of_summable (hasIntegerNorms_quadraticCharacterSystem χ)
    (isDiscrete_quadraticCharacterSystem χ) hZr).2]
  have hcongr : (fun n : ℕ =>
      (intCount (quadraticCharacterSystem χ) (hasIntegerNorms_quadraticCharacterSystem χ) n : ℂ)) =
      fun n : ℕ => χ.zetaMul n := funext (intCount_quadraticCharacterSystem hq)
  rw [hcongr]
  have hz : LSeriesSummable (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n) s := by
    simpa [ArithmeticFunction.natCoe_apply] using ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
  have h1 := RHTower.LSeriesSummable_toArithmeticFunction_of_norm_le
    (fun n => χ.norm_le_one n) hs
  have hprod : LSeries (fun n => χ.zetaMul n) s =
      riemannZeta s * DirichletCharacter.LFunction χ s := by
    rw [DirichletCharacter.zetaMul, ArithmeticFunction.LSeries_mul' hz h1,
      RHTower.LSeries_toArithmeticFunction, DirichletCharacter.LFunction_eq_LSeries χ hs]
    have hζ : LSeries (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n) s =
        riemannZeta s := by
      rw [← LSeries_zeta_eq_riemannZeta hs]
      congr 1
    rw [hζ]
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  have hzu : zetaResidueUnit s = (s - 1) * riemannZeta s := by
    simp [zetaResidueUnit, Function.update_of_ne hs1]
  rw [hprod, hzu, mul_assoc]

/-- **Quadratic `L`-function fake calibration at `β = 1/2`.**
Any nontrivial quadratic Dirichlet character `χ` (`χ^2 = 1`, `χ ≠ 1`) whose `L`-function vanishes
at some `ρ₀ ≠ 1` in `{Re s > 1/2}` where `ζ(ρ₀) ≠ 0` yields a discrete integer-norm Beurling fake
at remainder exponent `β = 1/2`. -/
theorem isIntegerNormFakeAt_half_of_quadratic_LFunction_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hq : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {ρ₀ : ℂ} (hρ : 1 / 2 < ρ₀.re) (hρ1 : ρ₀ ≠ 1)
    (hL0 : DirichletCharacter.LFunction χ ρ₀ = 0) (hζ : riemannZeta ρ₀ ≠ 0) :
    IsIntegerNormFakeAt (quadraticCharacterSystem χ) (1 / 2) := by
  obtain ⟨hLpos, hcnt⟩ := quadraticCharacterSystem_count_sub_le hq hχ
  refine ⟨hasIntegerNorms_quadraticCharacterSystem χ,
    isDiscrete_quadraticCharacterSystem χ,
    notNormEquivPrimes_quadraticCharacterSystem hq,
    ⟨(DirichletCharacter.LFunction χ 1).re, 6 * (N : ℝ) + 1, hLpos.le, hcnt⟩,
    fun s => zetaResidueUnit s * DirichletCharacter.LFunction χ s, ?_, ?_,
    ρ₀, hρ, hρ1, by simp only [hL0, mul_zero], hζ⟩
  · have hd₁ : Differentiable ℂ zetaResidueUnit :=
      fun s => (analyticAt_zetaResidueUnit s).differentiableAt
    exact (hd₁.mul (DirichletCharacter.differentiable_LFunction hχ)).differentiableOn
  · exact fun s hs => (quadraticCharacterSystem_zetaSeriesC_eq hq hχ hs).symm

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
