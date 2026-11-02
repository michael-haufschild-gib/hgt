import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.AbstractHilbertTraceToolkit
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.IntrinsicWeilTraceAndWindowCorollaries

/-!
# Finite-Prime Semilocal Ground-Energy Collapse, Forced Zero Crossings, and Multiplicative Syndeticity

Generalizes the single-prime `{∞, p}` obstruction of `SemilocalPositivityObstructions` to arbitrary
real weight sequences `w : ℕ → ℝ`, arbitrary prime sets `P : Set ℕ`, and arbitrary finite sets of
primes `S : Finset ℕ`:

1. **Unrestricted weighted prime remainder families (`weightedPrimeFamily w`):**
   At each aperture `a > 0`, the visible sum `Finset.Icc 2 ⌊e^{2a}⌋` is finite, so
   `ccmWeightedPrimeRemainder w a = ccmPrimeFreeRemainder a - ccmWeightedPrimeOperator w a` defines
   an unconditional `CCMRemainderFamily` without growth or summability hypotheses on `w`.
2. **Equivalence of `P`-smooth and `P`-prime-power truncations, structural bridges, and multi-prime
   valuation-shell trace identities (`primeSetSemilocalFamily P`, `finitePrimeSetSemilocalFamily S`):**
   Because `ArithmeticFunction.vonMangoldt` vanishes off prime powers, restricting to `P`-smooth
   integers coincides identically with restricting to prime powers `p^k` (`p ∈ P`, `p` prime,
   `k ≥ 1`). For `S : Finset ℕ`, `ccmWeightedPrimeOperator (semilocalVonMangoldt S) a` decomposes as
   `∑ p ∈ S.filter Nat.Prime, ccmPrimePowerOperator p a`, recovering `primeFreeFamily` at `S = ∅`,
   `primeSingleSemilocalFamily p` at `S = {p}` (`p` prime), `ccmRestrictedWeilBoundedRemainder` on
   `0 < a ≤ ½ log q₀` whenever `S` contains all primes `< q₀`, and `visiblePrimes A` at aperture
   `A`, together with the multi-prime `ValuationShellL2` trace identity via
   `primeValuationLogOperator p m` (`opTrace = m log p`).
3. **Parametric antisymmetric gap probe and the multiplicative syndeticity law:**
   Whenever all active weights `w n ≠ 0` avoid a logarithmic interval `(2L - 2δ₀, 2L + 2δ₀)`
   (`δ₀ = min δ (1/16)`), an antisymmetric pair of smooth bumps at `±L` annihilates
   `ccmWeightedPrimeOperator w b₀` identically while the odd `sinh` polar mode drives the ground
   energy below `gapProbeConst δ - gapProbeCoeff δ · (e^{L/2} - e^{-L/2})²`. Consequently, if
   `(weightedPrimeFamily w).energy` is bounded below across apertures, the active scales must be
   eventually logarithmically `2δ`-dense for every `δ > 0`, i.e. meet every multiplicative short
   interval `(X, (1 + ε) X)` for large `X`.
4. **Constructive `Finset` pigeonhole avoidance and cardinality-only `-Θ(e^A)` collapse:**
   For every `r : ℕ`, explicit constants `finitePrimeCollapseConst r` and
   `finitePrimeCollapseCoeff r > 0` depending **only on `r`** satisfy
   `(weightedPrimeFamily w).energy A ≤ finitePrimeCollapseConst r - finitePrimeCollapseCoeff r · e^A`
   for all `A ≥ 4`, all `S : Finset ℕ` with `S.card ≤ r`, and all unrestricted weights `w : ℕ → ℝ`
   supported on `{p^k : p ∈ S, p ≥ 2, k ≥ 1}`. No sub-maximal exponential rate `O(e^{θ A})` with
   `θ < 1` can hold.
5. **Forced zero crossings, positive-trace carrier no-go, quantitative prime counting, and
   infinitude of primes:**
   For every `S : Finset ℕ`, `(finitePrimeSetSemilocalFamily S).energy` crosses zero at a critical
   aperture `a_S ∈ (½ log 2, finitePrimeZeroCrossingCeiling S.card]` (`181 / 500 < a_S` when
   `2 ∈ S`) where the Friedrichs operator acquires a nonzero kernel state, refuting all positive
   operator-trace and positive Gram-trace carriers. Conversely, `0 ≤ ccmRestrictedWeilGroundEnergy A`
   at `A ≥ finitePrimeZeroCrossingCeiling r` forces `r < (visiblePrimes A).card`, and boundedness
   below of `(primeSetSemilocalFamily P).energy` forces `(P ∩ {p | p.Prime}).Infinite`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology BigOperators
open scoped ENNReal InnerProductSpace Real
open _root_.RHTower _root_.RHTower.WeilDeletion GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace

/-! ## 1. Unrestricted weighted prime remainder families -/

theorem clm_zero_smul {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] (A : E →L[ℂ] F) :
    (0 : ℂ) • A = 0 := by
  ext x
  exact zero_smul ℂ (A x)

theorem clm_sum_smul {E F ι : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] (s : Finset ι) (c : ι → ℂ) (A : E →L[ℂ] F) :
    (∑ i ∈ s, c i) • A = ∑ i ∈ s, c i • A := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, clm_zero_smul]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      ext x
      rw [AbstractToolkit.clm_smul_apply, AbstractToolkit.clm_add_apply,
        AbstractToolkit.clm_smul_apply, add_smul]
      congr 1
      exact congrArg (fun T : E →L[ℂ] F => T x) ih

/-- Congruence of `CCMRemainderFamily.Q` at aperture `a` when bounded remainders agree. -/
theorem ccmRemainderFamily_Q_eq_of_B_eq (F₁ F₂ : CCMRemainderFamily)
    (a : SuzukiPositiveAperture) (he : F₁.B a = F₂.B a)
    (u : CCMArchimedeanFormDomain a) :
    F₁.Q a u = F₂.Q a u := by
  unfold CCMRemainderFamily.Q CCMRemainderFamily.diagonal
  rw [he]

/-- Congruence of `CCMRemainderFamily.energy` at aperture `a` when bounded remainders agree. -/
theorem ccmRemainderFamily_energy_eq_of_B_eq (F₁ F₂ : CCMRemainderFamily)
    (a : SuzukiPositiveAperture) (he : F₁.B a = F₂.B a) :
    F₁.energy a = F₂.energy a := by
  unfold CCMRemainderFamily.energy
  change ‖boundedPerturbedFormCovariance (ccmArchimedeanFormToAperture a) (F₁.B a)
      (F₁.selfAdjoint a)‖⁻¹ - boundedPerturbedFormShift (F₁.B a) =
    ‖boundedPerturbedFormCovariance (ccmArchimedeanFormToAperture a) (F₂.B a)
      (F₂.selfAdjoint a)‖⁻¹ - boundedPerturbedFormShift (F₂.B a)
  rw [boundedPerturbedFormCovariance_congr (ccmArchimedeanFormToAperture a) he (F₁.selfAdjoint a)
    (F₂.selfAdjoint a), he]

/-- Visible weighted prime-transport operator at aperture `a` for an arbitrary real weight
`w : ℕ → ℝ`. -/
def ccmWeightedPrimeOperator (w : ℕ → ℝ) (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
    ((w n : ℝ) : ℂ) • ccmPrimeTransportOperator a n

theorem ccmWeightedPrimeOperator_isSelfAdjoint (w : ℕ → ℝ) (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (ccmWeightedPrimeOperator w a) :=
  AbstractToolkit.isSelfAdjoint_sum _ _ fun n _ =>
    AbstractToolkit.isSelfAdjoint_ofReal_smul (w n) (ccmPrimeTransportOperator_isSelfAdjoint a n)

theorem re_inner_ofReal_smul_ccmPrimeTransportOperator (a : SuzukiPositiveAperture)
    (r : ℝ) (n : ℕ) (f : suzukiApertureHilbert a) :
    (inner ℂ ((((r : ℝ) : ℂ) • ccmPrimeTransportOperator a n) f) f).re =
      r * (1 / Real.sqrt n) *
        (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
          inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re := by
  rw [clm_smul_apply, inner_smul_left, Complex.conj_ofReal, inner_ccmPrimeTransportOperator,
    ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

theorem ccmWeightedPrimeOperator_diagonal_eq_of_val_eq (w : ℕ → ℝ)
    {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b} (hvu : v.1 = u.1) :
    (inner ℂ (ccmWeightedPrimeOperator w b (ccmArchimedeanFormToAperture b v))
        (ccmArchimedeanFormToAperture b v)).re =
      (inner ℂ (ccmWeightedPrimeOperator w a (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re := by
  set fa := ccmArchimedeanFormToAperture a u
  set fb := ccmArchimedeanFormToAperture b v
  have hcoe : (fb : SoninL2) = (fa : SoninL2) :=
    ccmArchimedeanFormToAperture_coe_eq_of_val_eq hvu
  unfold ccmWeightedPrimeOperator
  rw [AbstractToolkit.re_inner_clm_sum_left, AbstractToolkit.re_inner_clm_sum_left]
  have hsub : Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) ⊆
      Finset.Icc 2 (Nat.floor (Real.exp (2 * b.1))) :=
    fun _ hn => mem_Icc_floor_of_le hab hn
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [re_inner_ofReal_smul_ccmPrimeTransportOperator,
      re_inner_ofReal_smul_ccmPrimeTransportOperator, hcoe]
  · intro n hnb hna
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hnb).1
    have hlog : 2 * a.1 < Real.log n := two_mul_lt_log_of_notMem hn2 hna
    rw [re_inner_ofReal_smul_ccmPrimeTransportOperator, hcoe,
      inner_logTranslationCLM_eq_zero_of_two_mul_le a fa fa hlog.le,
      inner_neg_logTranslationCLM_eq_zero_of_two_mul_le a fa fa hlog.le,
      add_zero, Complex.zero_re, mul_zero]

/-- Bounded remainder of the restricted Weil form with prime-free core minus
`ccmWeightedPrimeOperator w a`. -/
def ccmWeightedPrimeRemainder (w : ℕ → ℝ) (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ccmPrimeFreeRemainder a - ccmWeightedPrimeOperator w a

theorem ccmWeightedPrimeRemainder_isSelfAdjoint (w : ℕ → ℝ) (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (ccmWeightedPrimeRemainder w a) :=
  AbstractToolkit.isSelfAdjoint_sub (ccmPrimeFreeRemainder_isSelfAdjoint a)
    (ccmWeightedPrimeOperator_isSelfAdjoint w a)

/-- Aperture-compatible `CCMRemainderFamily` associated to an arbitrary real arithmetic weight
`w : ℕ → ℝ`, with continuous antitone ground energy `(weightedPrimeFamily w).energy`. -/
def weightedPrimeFamily (w : ℕ → ℝ) : CCMRemainderFamily where
  B a := ccmWeightedPrimeRemainder w a
  selfAdjoint a := ccmWeightedPrimeRemainder_isSelfAdjoint w a
  compat := by
    intro a b hab u v hvu
    unfold ccmWeightedPrimeRemainder
    rw [clm_sub_apply, clm_sub_apply, inner_sub_left, inner_sub_left,
      Complex.sub_re, Complex.sub_re,
      primeFree_diagonal_eq_of_val_eq hab hvu,
      ccmWeightedPrimeOperator_diagonal_eq_of_val_eq w hab hvu]

theorem weightedPrimeFamily_Q_eq_primeFree_sub (w : ℕ → ℝ) (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    (weightedPrimeFamily w).Q a u =
      primeFreeFamily.Q a u -
        (inner ℂ (ccmWeightedPrimeOperator w a (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a u)).re := by
  unfold CCMRemainderFamily.Q CCMRemainderFamily.diagonal
  change ‖u‖ ^ 2 +
      (inner ℂ ((ccmPrimeFreeRemainder a - ccmWeightedPrimeOperator w a)
        (ccmArchimedeanFormToAperture a u)) (ccmArchimedeanFormToAperture a u)).re =
    ‖u‖ ^ 2 +
      (inner ℂ (ccmPrimeFreeRemainder a (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re - _
  rw [clm_sub_apply, inner_sub_left, Complex.sub_re]
  ring

theorem ccmWeightedPrimeOperator_congr {w₁ w₂ : ℕ → ℝ} {a : SuzukiPositiveAperture}
    (hw : ∀ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))), w₁ n = w₂ n) :
    ccmWeightedPrimeOperator w₁ a = ccmWeightedPrimeOperator w₂ a := by
  unfold ccmWeightedPrimeOperator
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [hw n hn]

theorem weightedPrimeFamily_B_congr {w₁ w₂ : ℕ → ℝ} {a : SuzukiPositiveAperture}
    (hw : ∀ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))), w₁ n = w₂ n) :
    (weightedPrimeFamily w₁).B a = (weightedPrimeFamily w₂).B a := by
  change ccmPrimeFreeRemainder a - ccmWeightedPrimeOperator w₁ a =
    ccmPrimeFreeRemainder a - ccmWeightedPrimeOperator w₂ a
  rw [ccmWeightedPrimeOperator_congr hw]

/-! ## 2. Semilocal `P`-smooth / `P`-prime-power families, bridges, and multi-prime trace laws -/

open Classical in
/-- Semilocal von Mangoldt weight retaining integers whose prime factors all belong to `P`. -/
def semilocalVonMangoldt (P : Set ℕ) (n : ℕ) : ℝ :=
  if ∀ p ∈ n.primeFactors, p ∈ P then (ArithmeticFunction.vonMangoldt n : ℝ) else 0

theorem primeFactors_prime_pow_eq {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    (p ^ k).primeFactors = {p} := by
  ext q
  simp only [Nat.mem_primeFactors, Finset.mem_singleton]
  constructor
  · rintro ⟨hq, hdvd, -⟩
    exact (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd)
  · rintro rfl
    exact ⟨hp, dvd_pow_self q (by omega), pow_ne_zero k hp.ne_zero⟩

theorem smooth_iff_primePow_of_isPrimePow {P : Set ℕ} {n : ℕ} (hn : IsPrimePow n) :
    (∀ p ∈ n.primeFactors, p ∈ P) ↔ ∃ p ∈ P, p.Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ p ^ k = n := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  rw [primeFactors_prime_pow_eq hp hk]
  simp only [Finset.mem_singleton, forall_eq]
  constructor
  · intro hpP
    exact ⟨p, hpP, hp, k, hk, rfl⟩
  · rintro ⟨q, hqP, hq, m, hm, heq⟩
    have hdvd : q ∣ p ^ k := by
      rw [← heq]
      exact dvd_pow_self q (by omega)
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hdvd)
    rwa [← hqp]

open Classical in
/-- **Identity of `P`-smooth and `P`-prime-power von Mangoldt truncations:**
since `Λ(n) = 0` off prime powers, restricting to integers whose prime factors lie in `P` equals
restricting to prime powers `p^k` (`p ∈ P`, `p` prime, `k ≥ 1`). -/
theorem semilocalVonMangoldt_eq_primePow_ite (P : Set ℕ) (n : ℕ) :
    semilocalVonMangoldt P n =
      if (∃ p ∈ P, p.Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ p ^ k = n) then
        (ArithmeticFunction.vonMangoldt n : ℝ)
      else 0 := by
  unfold semilocalVonMangoldt
  by_cases hn : IsPrimePow n
  · have hiff := smooth_iff_primePow_of_isPrimePow (P := P) hn
    by_cases h1 : ∀ p ∈ n.primeFactors, p ∈ P
    · rw [if_pos h1, if_pos (hiff.mp h1)]
    · rw [if_neg h1, if_neg (mt hiff.mpr h1)]
  · have hzero : ArithmeticFunction.vonMangoldt n = 0 :=
      ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn
    rw [hzero]
    split_ifs <;> rfl

theorem semilocalVonMangoldt_support_primePow {P : Set ℕ} {n : ℕ}
    (hne : semilocalVonMangoldt P n ≠ 0) :
    ∃ p ∈ P, p.Prime ∧ ∃ k : ℕ, 1 ≤ k ∧ p ^ k = n := by
  classical
  rw [semilocalVonMangoldt_eq_primePow_ite] at hne
  split_ifs at hne with h
  · exact h
  · exact absurd rfl hne

theorem semilocalVonMangoldt_eq_inter_primes (P : Set ℕ) (n : ℕ) :
    semilocalVonMangoldt P n = semilocalVonMangoldt (P ∩ {p : ℕ | p.Prime}) n := by
  classical
  unfold semilocalVonMangoldt
  have hiff : (∀ p ∈ n.primeFactors, p ∈ P) ↔
      (∀ p ∈ n.primeFactors, p ∈ P ∩ {p : ℕ | p.Prime}) :=
    ⟨fun h p hp => ⟨h p hp, (Nat.mem_primeFactors.mp hp).1⟩, fun h p hp => (h p hp).1⟩
  by_cases h1 : ∀ p ∈ n.primeFactors, p ∈ P
  · rw [if_pos h1, if_pos (hiff.mp h1)]
  · rw [if_neg h1, if_neg (mt hiff.mpr h1)]

theorem semilocalVonMangoldt_eq_zero_of_no_primes {P : Set ℕ} (hP : ∀ p ∈ P, ¬ p.Prime) (n : ℕ) :
    semilocalVonMangoldt P n = 0 := by
  by_contra hne
  obtain ⟨p, hpP, hp, -⟩ := semilocalVonMangoldt_support_primePow hne
  exact hP p hpP hp

theorem semilocalVonMangoldt_univ (n : ℕ) :
    semilocalVonMangoldt Set.univ n = (ArithmeticFunction.vonMangoldt n : ℝ) := by
  classical
  simp [semilocalVonMangoldt]

theorem semilocalVonMangoldt_eq_vonMangoldt_of_lt {P : Set ℕ} {q₀ n : ℕ}
    (hP : ∀ p, p.Prime → p < q₀ → p ∈ P) (hn : n < q₀) :
    semilocalVonMangoldt P n = (ArithmeticFunction.vonMangoldt n : ℝ) := by
  classical
  unfold semilocalVonMangoldt
  rw [if_pos]
  intro p hp
  obtain ⟨hpPrime, hdvd, hn0⟩ := Nat.mem_primeFactors.mp hp
  exact hP p hpPrime (lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd) hn)

/-- Semilocal `{∞} ∪ P` remainder family associated to an arbitrary set `P : Set ℕ`. -/
def primeSetSemilocalFamily (P : Set ℕ) : CCMRemainderFamily :=
  weightedPrimeFamily (semilocalVonMangoldt P)

/-- Semilocal `{∞} ∪ S` remainder family associated to a finite set of primes `S : Finset ℕ`. -/
def finitePrimeSetSemilocalFamily (S : Finset ℕ) : CCMRemainderFamily :=
  primeSetSemilocalFamily (S : Set ℕ)

/-- Finite set of primes visible at aperture `A` (`p ≤ ⌊e^{2A}⌋`). -/
def visiblePrimes (A : SuzukiPositiveAperture) : Finset ℕ :=
  (Finset.Icc 2 (Nat.floor (Real.exp (2 * A.1)))).filter Nat.Prime

/-- When `P` contains no primes, `primeSetSemilocalFamily P` coincides with `primeFreeFamily`. -/
theorem primeSetSemilocalFamily_B_eq_primeFree_of_no_primes {P : Set ℕ}
    (hP : ∀ p ∈ P, ¬ p.Prime) (a : SuzukiPositiveAperture) :
    (primeSetSemilocalFamily P).B a = primeFreeFamily.B a := by
  change ccmPrimeFreeRemainder a - ccmWeightedPrimeOperator (semilocalVonMangoldt P) a =
    ccmPrimeFreeRemainder a
  have hzero : ccmWeightedPrimeOperator (semilocalVonMangoldt P) a = 0 := by
    unfold ccmWeightedPrimeOperator
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [semilocalVonMangoldt_eq_zero_of_no_primes hP n, Complex.ofReal_zero, clm_zero_smul]
  rw [hzero, sub_zero]

@[simp] theorem finitePrimeSetSemilocalFamily_empty_B (a : SuzukiPositiveAperture) :
    (finitePrimeSetSemilocalFamily ∅).B a = primeFreeFamily.B a :=
  primeSetSemilocalFamily_B_eq_primeFree_of_no_primes (by simp) a

@[simp] theorem finitePrimeSetSemilocalFamily_empty_Q (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    (finitePrimeSetSemilocalFamily ∅).Q a u = primeFreeFamily.Q a u :=
  ccmRemainderFamily_Q_eq_of_B_eq _ _ a (finitePrimeSetSemilocalFamily_empty_B a) u

@[simp] theorem finitePrimeSetSemilocalFamily_empty_energy (a : SuzukiPositiveAperture) :
    (finitePrimeSetSemilocalFamily ∅).energy a = primeFreeFamily.energy a :=
  ccmRemainderFamily_energy_eq_of_B_eq _ _ a (finitePrimeSetSemilocalFamily_empty_B a)

/-- On `Set.univ`, `primeSetSemilocalFamily` recovers the literal all-prime restricted Weil family. -/
theorem primeSetSemilocalFamily_univ_B (a : SuzukiPositiveAperture) :
    (primeSetSemilocalFamily Set.univ).B a = ccmRestrictedWeilBoundedRemainder a := by
  change ccmPrimeFreeRemainder a - ccmWeightedPrimeOperator (semilocalVonMangoldt Set.univ) a = _
  have heq : ccmWeightedPrimeOperator (semilocalVonMangoldt Set.univ) a =
      ccmFinitePrimeOperator a := by
    unfold ccmWeightedPrimeOperator ccmFinitePrimeOperator
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [semilocalVonMangoldt_univ]
  rw [heq, ccmPrimeFreeRemainder, add_sub_cancel_right]

theorem primeSetSemilocalFamily_univ_energy (a : SuzukiPositiveAperture) :
    (primeSetSemilocalFamily Set.univ).energy a = ccmRestrictedWeilGroundEnergy a :=
  ccmRemainderFamily_energy_eq_literal_of_B_eq _ a (primeSetSemilocalFamily_univ_B a)

/-- Pointwise finite-prime decomposition of `semilocalVonMangoldt (S : Set ℕ)` into disjoint
single-prime contributions across `S.filter Nat.Prime`. -/
theorem semilocalVonMangoldt_finset_eq_sum_filter_prime (S : Finset ℕ) (n : ℕ) :
    semilocalVonMangoldt (S : Set ℕ) n =
      ∑ p ∈ S.filter Nat.Prime, semilocalVonMangoldt ({p} : Set ℕ) n := by
  classical
  by_cases hn : IsPrimePow n
  · obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
    have hpf : (q ^ k).primeFactors = {q} := primeFactors_prime_pow_eq hq hk
    by_cases hqS : q ∈ S
    · have hmem : q ∈ S.filter Nat.Prime := Finset.mem_filter.mpr ⟨hqS, hq⟩
      rw [Finset.sum_eq_single q]
      · unfold semilocalVonMangoldt
        rw [hpf, if_pos (by simp [hqS]), if_pos (by simp)]
      · intro p hp hne
        unfold semilocalVonMangoldt
        rw [hpf, if_neg]
        simp [hne.symm]
      · intro hnot
        exact absurd hmem hnot
    · rw [Finset.sum_eq_zero]
      · unfold semilocalVonMangoldt
        rw [hpf, if_neg]
        simpa using hqS
      · intro p hp
        have hne : q ≠ p := fun h => hqS (h ▸ (Finset.mem_filter.mp hp).1)
        unfold semilocalVonMangoldt
        rw [hpf, if_neg]
        simpa using hne
  · have hzero : ∀ P : Set ℕ, semilocalVonMangoldt P n = 0 := fun P => by
      unfold semilocalVonMangoldt
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn]
      split_ifs <;> rfl
    rw [hzero]
    exact (Finset.sum_eq_zero fun p _ => hzero _).symm

/-- For every prime `p`, the singleton weighted prime operator equals `ccmPrimePowerOperator p a`. -/
theorem ccmWeightedPrimeOperator_singleton_eq_ccmPrimePowerOperator {p : ℕ} (hp : p.Prime)
    (a : SuzukiPositiveAperture) :
    ccmWeightedPrimeOperator (semilocalVonMangoldt ({p} : Set ℕ)) a =
      ccmPrimePowerOperator p a := by
  classical
  set M : ℕ := Nat.floor (Real.exp (2 * a.1))
  set J : Finset ℕ := (Finset.Icc 1 M).filter (fun m => p ^ m ≤ M)
  have hJ_sub : J ⊆ Finset.Icc 1 M := Finset.filter_subset _ _
  have hp2 : 2 ≤ p := hp.two_le
  have hpow_ge2 : ∀ {m : ℕ}, 1 ≤ m → 2 ≤ p ^ m := fun {m} hm1 =>
    calc 2 ≤ p ^ 1 := by rw [pow_one]; exact hp2
      _ ≤ p ^ m := Nat.pow_le_pow_right hp.pos hm1
  have hrhs : ccmPrimePowerOperator p a =
      ∑ m ∈ J, ((ArithmeticFunction.vonMangoldt (p ^ m) : ℝ) : ℂ) •
        ccmPrimeTransportOperator a (p ^ m) := by
    unfold ccmPrimePowerOperator
    rw [← Finset.sum_subset hJ_sub]
    · refine Finset.sum_congr rfl fun m hmJ => ?_
      obtain ⟨hmI, hpm⟩ := Finset.mem_filter.mp hmJ
      have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hmI).1
      have hmem : p ^ m ∈ Finset.Icc 2 M := Finset.mem_Icc.mpr ⟨hpow_ge2 hm1, hpm⟩
      unfold ccmVisiblePrimeBlock
      rw [if_pos hmem]
    · intro m hmI hmJ
      have hnot : p ^ m ∉ Finset.Icc 2 M := fun hmem =>
        hmJ (Finset.mem_filter.mpr ⟨hmI, (Finset.mem_Icc.mp hmem).2⟩)
      exact ccmVisiblePrimeBlock_of_invisible a hnot
  have himg_sub : J.image (fun m => p ^ m) ⊆ Finset.Icc 2 M := by
    intro n hn
    obtain ⟨m, hmJ, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hmI, hpm⟩ := Finset.mem_filter.mp hmJ
    exact Finset.mem_Icc.mpr ⟨hpow_ge2 (Finset.mem_Icc.mp hmI).1, hpm⟩
  unfold ccmWeightedPrimeOperator
  change ∑ n ∈ Finset.Icc 2 M,
      ((semilocalVonMangoldt ({p} : Set ℕ) n : ℝ) : ℂ) • ccmPrimeTransportOperator a n = _
  rw [hrhs, ← Finset.sum_subset himg_sub]
  · rw [Finset.sum_image (fun m₁ _ m₂ _ h => Nat.pow_right_injective hp2 h)]
    refine Finset.sum_congr rfl fun m hmJ => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp (Finset.mem_filter.mp hmJ).1).1
    have hvm : semilocalVonMangoldt ({p} : Set ℕ) (p ^ m) =
        (ArithmeticFunction.vonMangoldt (p ^ m) : ℝ) := by
      unfold semilocalVonMangoldt
      rw [primeFactors_prime_pow_eq hp hm1, if_pos (by simp)]
    rw [hvm]
  · intro n hnI hnImg
    have hzero : semilocalVonMangoldt ({p} : Set ℕ) n = 0 := by
      by_contra hne
      obtain ⟨q, hqp, _, k, hk1, rfl⟩ := semilocalVonMangoldt_support_primePow hne
      have hqp_eq : q = p := Set.mem_singleton_iff.mp hqp
      subst hqp_eq
      have hqk_le : q ^ k ≤ M := (Finset.mem_Icc.mp hnI).2
      have hk_lt : k < q ^ k := lt_of_lt_of_le k.lt_two_pow_self (Nat.pow_le_pow_left hp2 k)
      have hkJ : k ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, by omega⟩, hqk_le⟩
      exact hnImg (Finset.mem_image.mpr ⟨k, hkJ, rfl⟩)
    rw [hzero, Complex.ofReal_zero, clm_zero_smul]

/-- **Exact finite-prime block decomposition:** for any `S : Finset ℕ`, the `{∞} ∪ S` weighted
prime operator is the sum of the single-prime operators `ccmPrimePowerOperator p a` over primes in
`S`. -/
theorem ccmWeightedPrimeOperator_finset_eq_sum_ccmPrimePowerOperator (S : Finset ℕ)
    (a : SuzukiPositiveAperture) :
    ccmWeightedPrimeOperator (semilocalVonMangoldt (S : Set ℕ)) a =
      ∑ p ∈ S.filter Nat.Prime, ccmPrimePowerOperator p a := by
  have hlhs : ccmWeightedPrimeOperator (semilocalVonMangoldt (S : Set ℕ)) a =
      ∑ p ∈ S.filter Nat.Prime,
        ccmWeightedPrimeOperator (semilocalVonMangoldt ({p} : Set ℕ)) a := by
    unfold ccmWeightedPrimeOperator
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [semilocalVonMangoldt_finset_eq_sum_filter_prime S n, Complex.ofReal_sum, clm_sum_smul]
  rw [hlhs]
  exact Finset.sum_congr rfl fun p hp =>
    ccmWeightedPrimeOperator_singleton_eq_ccmPrimePowerOperator (Finset.mem_filter.mp hp).2 a

/-- Singleton bridge: for a prime `p`, `finitePrimeSetSemilocalFamily {p}` agrees identically with
`primeSingleSemilocalFamily p`. -/
theorem finitePrimeSetSemilocalFamily_singleton_B {p : ℕ} (hp : p.Prime)
    (a : SuzukiPositiveAperture) :
    (finitePrimeSetSemilocalFamily {p}).B a = (primeSingleSemilocalFamily p).B a := by
  change ccmPrimeFreeRemainder a -
      ccmWeightedPrimeOperator (semilocalVonMangoldt (({p} : Finset ℕ) : Set ℕ)) a =
    ccmPrimeFreeRemainder a - ccmPrimePowerOperator p a
  rw [Finset.coe_singleton, ccmWeightedPrimeOperator_singleton_eq_ccmPrimePowerOperator hp a]

theorem finitePrimeSetSemilocalFamily_singleton_Q {p : ℕ} (hp : p.Prime)
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    (finitePrimeSetSemilocalFamily {p}).Q a u = (primeSingleSemilocalFamily p).Q a u :=
  ccmRemainderFamily_Q_eq_of_B_eq _ _ a (finitePrimeSetSemilocalFamily_singleton_B hp a) u

theorem finitePrimeSetSemilocalFamily_singleton_energy {p : ℕ} (hp : p.Prime)
    (a : SuzukiPositiveAperture) :
    (finitePrimeSetSemilocalFamily {p}).energy a = (primeSingleSemilocalFamily p).energy a :=
  ccmRemainderFamily_energy_eq_of_B_eq _ _ a (finitePrimeSetSemilocalFamily_singleton_B hp a)

/-- **Closed cutoff window law up to the first omitted prime `q₀`:**
if `P` contains every prime `< q₀`, then throughout `0 < a ≤ ½ log q₀` the `{∞} ∪ P` semilocal
family coincides identically with the literal all-prime restricted Weil family (including at the
closed endpoint `a = ½ log q₀`, where `ccmPrimeTransportOperator a q₀ = 0`). -/
theorem ccmWeightedPrimeOperator_semilocal_eq_finitePrime_of_le_halfLog
    {P : Set ℕ} {q₀ : ℕ} (hP : ∀ p, p.Prime → p < q₀ → p ∈ P)
    {a : SuzukiPositiveAperture} (ha : a.1 ≤ Real.log q₀ / 2) :
    ccmWeightedPrimeOperator (semilocalVonMangoldt P) a = ccmFinitePrimeOperator a := by
  unfold ccmWeightedPrimeOperator ccmFinitePrimeOperator
  refine Finset.sum_congr rfl fun n hn => ?_
  rcases lt_or_ge n q₀ with hlt | hge
  · rw [semilocalVonMangoldt_eq_vonMangoldt_of_lt hP hlt]
  · have hq₀2 : 2 ≤ q₀ := by
      by_contra hlt2
      have hlog_nonpos : Real.log (q₀ : ℝ) ≤ 0 := by
        match q₀ with
        | 0 => simp
        | 1 => simp
        | q' + 2 => omega
      linarith [a.2]
    have hlog : Real.log q₀ ≤ Real.log n :=
      Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le (by norm_num) hq₀2))
        (by exact_mod_cast hge)
    rw [ccmPrimeTransportOperator_eq_zero_of_two_mul_le_log a (by linarith),
      clm_smul_zero, clm_smul_zero]

theorem primeSetSemilocalFamily_B_eq_literal_of_le_halfLog
    {P : Set ℕ} {q₀ : ℕ} (hP : ∀ p, p.Prime → p < q₀ → p ∈ P)
    {a : SuzukiPositiveAperture} (ha : a.1 ≤ Real.log q₀ / 2) :
    (primeSetSemilocalFamily P).B a = ccmRestrictedWeilBoundedRemainder a := by
  change ccmPrimeFreeRemainder a - ccmWeightedPrimeOperator (semilocalVonMangoldt P) a = _
  rw [ccmWeightedPrimeOperator_semilocal_eq_finitePrime_of_le_halfLog hP ha,
    ccmPrimeFreeRemainder, add_sub_cancel_right]

theorem primeSetSemilocalFamily_Q_eq_literal_of_le_halfLog
    {P : Set ℕ} {q₀ : ℕ} (hP : ∀ p, p.Prime → p < q₀ → p ∈ P)
    {a : SuzukiPositiveAperture} (ha : a.1 ≤ Real.log q₀ / 2)
    (u : CCMArchimedeanFormDomain a) :
    (primeSetSemilocalFamily P).Q a u = ccmRestrictedWeilSourceQuadratic a u :=
  ccmRemainderFamily_Q_eq_literal_of_B_eq _ a
    (primeSetSemilocalFamily_B_eq_literal_of_le_halfLog hP ha) u

theorem primeSetSemilocalFamily_energy_eq_literal_of_le_halfLog
    {P : Set ℕ} {q₀ : ℕ} (hP : ∀ p, p.Prime → p < q₀ → p ∈ P)
    {a : SuzukiPositiveAperture} (ha : a.1 ≤ Real.log q₀ / 2) :
    (primeSetSemilocalFamily P).energy a = ccmRestrictedWeilGroundEnergy a :=
  ccmRemainderFamily_energy_eq_literal_of_B_eq _ a
    (primeSetSemilocalFamily_B_eq_literal_of_le_halfLog hP ha)

theorem finitePrimeSetSemilocalFamily_energy_eq_literal_of_le_halfLogTwo (S : Finset ℕ)
    {a : SuzukiPositiveAperture} (ha : a.1 ≤ Real.log 2 / 2) :
    (finitePrimeSetSemilocalFamily S).energy a = ccmRestrictedWeilGroundEnergy a :=
  primeSetSemilocalFamily_energy_eq_literal_of_le_halfLog
    (q₀ := 2) (fun _ hp hlt => absurd hlt (not_lt.mpr hp.two_le)) ha

theorem finitePrimeSetSemilocalFamily_energy_eq_literal_of_two_mem_of_le_halfLogThree
    {S : Finset ℕ} (h2 : 2 ∈ S) {a : SuzukiPositiveAperture} (ha : a.1 ≤ Real.log 3 / 2) :
    (finitePrimeSetSemilocalFamily S).energy a = ccmRestrictedWeilGroundEnergy a :=
  primeSetSemilocalFamily_energy_eq_literal_of_le_halfLog (q₀ := 3)
    (fun p hp hlt => by
      have hp2 : p = 2 := by have := hp.two_le; omega
      rwa [hp2]) ha

/-- **Aperture-local exactness of `visiblePrimes A`:**
retaining only the finite set of primes `≤ ⌊e^{2A}⌋` reproduces the literal all-prime restricted
Weil operator, quadratic form, and ground energy at aperture `A`. -/
theorem finitePrimeSetSemilocalFamily_visiblePrimes_B (A : SuzukiPositiveAperture) :
    (finitePrimeSetSemilocalFamily (visiblePrimes A)).B A =
      ccmRestrictedWeilBoundedRemainder A := by
  change ccmPrimeFreeRemainder A -
    ccmWeightedPrimeOperator (semilocalVonMangoldt (visiblePrimes A : Set ℕ)) A = _
  have heq : ccmWeightedPrimeOperator (semilocalVonMangoldt (visiblePrimes A : Set ℕ)) A =
      ccmFinitePrimeOperator A := by
    unfold ccmWeightedPrimeOperator ccmFinitePrimeOperator
    refine Finset.sum_congr rfl fun n hn => ?_
    have hsm : semilocalVonMangoldt (visiblePrimes A : Set ℕ) n =
        (ArithmeticFunction.vonMangoldt n : ℝ) := by
      classical
      unfold semilocalVonMangoldt
      rw [if_pos]
      intro p hp
      obtain ⟨hpPrime, hdvd, hn0⟩ := Nat.mem_primeFactors.mp hp
      have hp_le : p ≤ Nat.floor (Real.exp (2 * A.1)) :=
        le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd) (Finset.mem_Icc.mp hn).2
      exact Finset.mem_coe.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpPrime.two_le, hp_le⟩, hpPrime⟩)
    rw [hsm]
  rw [heq, ccmPrimeFreeRemainder, add_sub_cancel_right]

theorem finitePrimeSetSemilocalFamily_visiblePrimes_energy (A : SuzukiPositiveAperture) :
    (finitePrimeSetSemilocalFamily (visiblePrimes A)).energy A =
      ccmRestrictedWeilGroundEnergy A :=
  ccmRemainderFamily_energy_eq_literal_of_B_eq _ A
    (finitePrimeSetSemilocalFamily_visiblePrimes_B A)

/-- For every prime `p` and exponent `m ≥ 1`, `ccmVisiblePrimeBlock a (p ^ m)` equals
`Λ(p^m) • ccmPrimeTransportOperator a (p ^ m)` unconditionally (since `2a < log(p^m)` kills
`ccmPrimeTransportOperator` whenever `p^m > ⌊e^{2a}⌋`). -/
theorem ccmVisiblePrimeBlock_prime_pow_eq {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m)
    (a : SuzukiPositiveAperture) :
    ccmVisiblePrimeBlock a (p ^ m) =
      ((ArithmeticFunction.vonMangoldt (p ^ m) : ℝ) : ℂ) •
        ccmPrimeTransportOperator a (p ^ m) := by
  unfold ccmVisiblePrimeBlock
  split_ifs with hmem
  · rfl
  · have hp2 : 2 ≤ p ^ m :=
      calc 2 ≤ p ^ 1 := by rw [pow_one]; exact hp.two_le
        _ ≤ p ^ m := Nat.pow_le_pow_right hp.pos hm
    have hlog : 2 * a.1 < Real.log ((p ^ m : ℕ) : ℝ) := two_mul_lt_log_of_notMem hp2 hmem
    rw [ccmPrimeTransportOperator_eq_zero_of_two_mul_le_log a hlog.le, clm_smul_zero]

theorem inv_mul_sqrt_mul_opTrace_primeValuationLogOperator {p m : ℕ}
    (hp : p.Prime) (hm : 1 ≤ m) :
    (((1 / ((m : ℝ) * Real.sqrt ((p ^ m : ℕ) : ℝ)) : ℝ) : ℂ) *
      ContinuousLinearMap.opTrace (primeValuationLogOperator p m)) =
      ((ArithmeticFunction.vonMangoldt (p ^ m) : ℝ) : ℂ) *
        ((1 / Real.sqrt ((p ^ m : ℕ) : ℝ) : ℝ) : ℂ) := by
  have hvm : (ArithmeticFunction.vonMangoldt (p ^ m) : ℝ) = Real.log (p : ℝ) :=
    (ArithmeticFunction.vonMangoldt_apply_pow (by omega)).trans
      (ArithmeticFunction.vonMangoldt_apply_prime hp)
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [opTrace_primeValuationLogOperator, hvm]
  push_cast
  field_simp [hm0]

theorem inner_ccmVisiblePrimeBlock_prime_pow_eq_valuationLogTrace {p m : ℕ}
    (hp : p.Prime) (hm : 1 ≤ m) (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    inner ℂ (ccmVisiblePrimeBlock a (p ^ m) f) f =
      (((1 / ((m : ℝ) * Real.sqrt ((p ^ m : ℕ) : ℝ)) : ℝ) : ℂ) *
        ContinuousLinearMap.opTrace (primeValuationLogOperator p m)) *
        ContinuousLinearMap.opTrace
          (ccmApertureCompression a
            (ccmSymmetricLogTranslation (Real.log ((p ^ m : ℕ) : ℝ))) ∘L
            InnerProductSpace.rankOne ℂ f f) := by
  have hS : IsSelfAdjoint
      (ccmApertureCompression a
        (ccmSymmetricLogTranslation (Real.log ((p ^ m : ℕ) : ℝ)))) :=
    ccmApertureCompression_isSelfAdjoint a (ccmSymmetricLogTranslation_isSelfAdjoint _)
  have hlhs : inner ℂ (ccmVisiblePrimeBlock a (p ^ m) f) f =
      (((ArithmeticFunction.vonMangoldt (p ^ m) : ℝ) : ℂ) *
        ((1 / Real.sqrt ((p ^ m : ℕ) : ℝ) : ℝ) : ℂ)) *
        inner ℂ (ccmApertureCompression a
          (ccmSymmetricLogTranslation (Real.log ((p ^ m : ℕ) : ℝ))) f) f := by
    rw [ccmVisiblePrimeBlock_prime_pow_eq hp hm a, ccmPrimeTransportOperator,
      clm_smul_apply, clm_smul_apply, inner_smul_left, inner_smul_left,
      Complex.conj_ofReal, Complex.conj_ofReal, mul_assoc]
  exact hlhs.trans (congrArg₂ Mul.mul
    (inv_mul_sqrt_mul_opTrace_primeValuationLogOperator hp hm).symm
    (opTrace_comp_rankOne_self_of_isSelfAdjoint hS f).symm)

theorem re_inner_ccmPrimePowerOperator_eq_sum_valuationLogTrace {p : ℕ} (hp : p.Prime)
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    (inner ℂ (ccmPrimePowerOperator p a f) f).re =
      ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.exp (2 * a.1))),
        ((((1 / ((m : ℝ) * Real.sqrt ((p ^ m : ℕ) : ℝ)) : ℝ) : ℂ) *
          ContinuousLinearMap.opTrace (primeValuationLogOperator p m)) *
          ContinuousLinearMap.opTrace
            (ccmApertureCompression a
              (ccmSymmetricLogTranslation (Real.log ((p ^ m : ℕ) : ℝ))) ∘L
              InnerProductSpace.rankOne ℂ f f)).re := by
  unfold ccmPrimePowerOperator
  rw [AbstractToolkit.re_inner_clm_sum_left]
  refine Finset.sum_congr rfl fun m hm => ?_
  exact congrArg Complex.re
    (inner_ccmVisiblePrimeBlock_prime_pow_eq_valuationLogTrace hp (Finset.mem_Icc.mp hm).1 a f)

/-- **Exact multi-prime `{∞} ∪ S` valuation-shell operator-trace identity:**
for any `S : Finset ℕ`, `a : SuzukiPositiveAperture`, and `u : CCMArchimedeanFormDomain a`,
`(finitePrimeSetSemilocalFamily S).Q a u` equals the archimedean integral plus polar trace minus
the sum over `p ∈ S.filter Nat.Prime` and `1 ≤ m ≤ ⌊e^{2a}⌋` of the Euler weight `1 / (m √(p^m))`
times the trace of the positive `p`-adic shell operator `primeValuationLogOperator p m`
(`opTrace = m log p`) times the compressed `log(p^m)`-shift trace (and equals
`ccmRestrictedWeilSourceQuadratic a u` throughout `0 < a ≤ ½ log q₀` whenever `S` contains all
primes `< q₀`). -/
theorem finitePrimeSetSemilocalFamily_Q_eq_multiPrimeValuationTrace (S : Finset ℕ)
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    (finitePrimeSetSemilocalFamily S).Q a u =
      archPart a u +
        (ContinuousLinearMap.opTrace (ccmPolarOperator a ∘L
          InnerProductSpace.rankOne ℂ (ccmArchimedeanFormToAperture a u)
            (ccmArchimedeanFormToAperture a u))).re -
        ∑ p ∈ S.filter Nat.Prime,
          ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.exp (2 * a.1))),
            ((((1 / ((m : ℝ) * Real.sqrt ((p ^ m : ℕ) : ℝ)) : ℝ) : ℂ) *
              ContinuousLinearMap.opTrace (primeValuationLogOperator p m)) *
              ContinuousLinearMap.opTrace
                (ccmApertureCompression a
                  (ccmSymmetricLogTranslation (Real.log ((p ^ m : ℕ) : ℝ))) ∘L
                  InnerProductSpace.rankOne ℂ (ccmArchimedeanFormToAperture a u)
                    (ccmArchimedeanFormToAperture a u))).re := by
  have hQ : (finitePrimeSetSemilocalFamily S).Q a u =
      primeFreeFamily.Q a u -
        (inner ℂ (ccmWeightedPrimeOperator (semilocalVonMangoldt (S : Set ℕ)) a
          (ccmArchimedeanFormToAperture a u)) (ccmArchimedeanFormToAperture a u)).re :=
    weightedPrimeFamily_Q_eq_primeFree_sub _ a u
  have hsum :
      (inner ℂ (ccmWeightedPrimeOperator (semilocalVonMangoldt (S : Set ℕ)) a
        (ccmArchimedeanFormToAperture a u)) (ccmArchimedeanFormToAperture a u)).re =
        ∑ p ∈ S.filter Nat.Prime,
          ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.exp (2 * a.1))),
            ((((1 / ((m : ℝ) * Real.sqrt ((p ^ m : ℕ) : ℝ)) : ℝ) : ℂ) *
              ContinuousLinearMap.opTrace (primeValuationLogOperator p m)) *
              ContinuousLinearMap.opTrace
                (ccmApertureCompression a
                  (ccmSymmetricLogTranslation (Real.log ((p ^ m : ℕ) : ℝ))) ∘L
                  InnerProductSpace.rankOne ℂ (ccmArchimedeanFormToAperture a u)
                    (ccmArchimedeanFormToAperture a u))).re := by
    rw [ccmWeightedPrimeOperator_finset_eq_sum_ccmPrimePowerOperator,
      AbstractToolkit.re_inner_clm_sum_left]
    refine Finset.sum_congr rfl fun p hp => ?_
    exact re_inner_ccmPrimePowerOperator_eq_sum_valuationLogTrace
      (Finset.mem_filter.mp hp).2 a (ccmArchimedeanFormToAperture a u)
  exact hQ.trans (congrArg₂ Sub.sub
    ((primeFreeFamily_Q_eq a u).trans
      (congrArg (archPart a u + ·) (polarPart_eq_opTrace_re a u)))
    hsum)

/-! ## 3. Parametric antisymmetric gap probe and the multiplicative syndeticity law -/

/-- Reference small aperture `min δ (1 / 16) > 0` for a logarithmic gap probe of half-width `δ`. -/
def gapProbeSmallAperture (δ : ℝ) (hδ : 0 < δ) : SuzukiPositiveAperture :=
  ⟨min δ (1 / 16), lt_min hδ (by norm_num)⟩

theorem gapProbeRadius_pos {δ : ℝ} (hδ : 0 < δ) : 0 < (gapProbeSmallAperture δ hδ).1 / 2 := by
  have := (gapProbeSmallAperture δ hδ).2
  linarith

theorem gapProbeClosedBall_subset {δ : ℝ} (hδ : 0 < δ) :
    Metric.closedBall (0 : ℝ) ((gapProbeSmallAperture δ hδ).1 / 2) ⊆
      Ioo (-(gapProbeSmallAperture δ hδ).1) (gapProbeSmallAperture δ hδ).1 := by
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hx
  have ha := (gapProbeSmallAperture δ hδ).2
  constructor <;> linarith [hx.1, hx.2]

/-- Reference smooth bump form vector on `gapProbeSmallAperture δ hδ`. -/
def gapProbeFormVector (δ : ℝ) (hδ : 0 < δ) :
    CCMArchimedeanFormDomain (gapProbeSmallAperture δ hδ) :=
  (bumpInteriorSource (gapProbeSmallAperture δ hδ) 0
    ((gapProbeSmallAperture δ hδ).1 / 2) (gapProbeRadius_pos hδ)
    (gapProbeClosedBall_subset hδ)).toCCMFormVector

/-- Physical `L²` image of `gapProbeFormVector δ hδ`. -/
def gapProbeApertureVector (δ : ℝ) (hδ : 0 < δ) :
    suzukiApertureHilbert (gapProbeSmallAperture δ hδ) :=
  ccmArchimedeanFormToAperture (gapProbeSmallAperture δ hδ) (gapProbeFormVector δ hδ)

theorem gapProbeApertureVector_ne_zero {δ : ℝ} (hδ : 0 < δ) :
    gapProbeApertureVector δ hδ ≠ 0 :=
  bumpFormVector_aperture_ne_zero (gapProbeSmallAperture δ hδ)
    ((gapProbeSmallAperture δ hδ).1 / 2) (gapProbeRadius_pos hδ) (gapProbeClosedBall_subset hδ)

theorem gapProbeApertureVector_norm_sq_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < ‖gapProbeApertureVector δ hδ‖ ^ 2 :=
  sq_pos_of_pos (norm_pos_iff.mpr (gapProbeApertureVector_ne_zero hδ))

/-- Additive archimedean ceiling in the logarithmic gap-probe ground-energy bound, depending only
on the gap half-width `δ`. -/
def gapProbeConst (δ : ℝ) (hδ : 0 < δ) : ℝ :=
  (4 * ‖gapProbeFormVector δ hδ‖ ^ 2 +
    |2 * gammaHardyPhaseRate 0 - 1| * (4 * ‖gapProbeApertureVector δ hδ‖ ^ 2)) /
    (2 * ‖gapProbeApertureVector δ hδ‖ ^ 2)

/-- Positive hyperbolic polar coefficient in the logarithmic gap-probe ground-energy bound,
depending only on `δ`. -/
def gapProbeCoeff (δ : ℝ) (hδ : 0 < δ) : ℝ :=
  (polarBumpMoment 0 ((gapProbeSmallAperture δ hδ).1 / 2) (gapProbeRadius_pos hδ) (1 / 2) *
    polarBumpMoment 0 ((gapProbeSmallAperture δ hδ).1 / 2) (gapProbeRadius_pos hδ) (-1 / 2)) /
    ‖gapProbeApertureVector δ hδ‖ ^ 2

theorem gapProbeCoeff_pos {δ : ℝ} (hδ : 0 < δ) : 0 < gapProbeCoeff δ hδ := by
  unfold gapProbeCoeff
  have hmPos : 0 < polarBumpMoment 0 ((gapProbeSmallAperture δ hδ).1 / 2)
      (gapProbeRadius_pos hδ) (1 / 2) :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _)
      (polarBumpMass_pos 0 _ (gapProbeRadius_pos hδ)))
      (le_polarBumpMoment 0 _ (gapProbeRadius_pos hδ) (1 / 2))
  have hmNeg : 0 < polarBumpMoment 0 ((gapProbeSmallAperture δ hδ).1 / 2)
      (gapProbeRadius_pos hδ) (-1 / 2) :=
    lt_of_lt_of_le (mul_pos (Real.exp_pos _)
      (polarBumpMass_pos 0 _ (gapProbeRadius_pos hδ)))
      (le_polarBumpMoment 0 _ (gapProbeRadius_pos hδ) (-1 / 2))
  exact div_pos (mul_pos hmPos hmNeg) (gapProbeApertureVector_norm_sq_pos hδ)

/-- **Parametric antisymmetric gap-probe upper bound:**
if at `L ≥ 1/4` every active integer `n ∈ [2, ⌊e^{2(a₀ + L)}⌋]` with `w n ≠ 0` avoids the
logarithmic interval `(2L - 2a₀, 2L + 2a₀)` (`a₀ = min δ (1/16)`), then an antisymmetric pair of
smooth bumps at `±L` annihilates `ccmWeightedPrimeOperator w b₀` identically and bounds
`(weightedPrimeFamily w).energy b₀` above by
`gapProbeConst δ hδ - gapProbeCoeff δ hδ * (e^{L/2} - e^{-L/2})^2`. -/
theorem weightedPrimeFamily_energy_le_of_log_gap {δ : ℝ} (hδ : 0 < δ) (w : ℕ → ℝ)
    {L : ℝ} (hL : (1 / 4 : ℝ) ≤ L)
    (hgap : ∀ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * ((gapProbeSmallAperture δ hδ).1 + L)))),
      w n ≠ 0 → 2 * (gapProbeSmallAperture δ hδ).1 ≤ |Real.log n - 2 * L|) :
    let b₀ : SuzukiPositiveAperture :=
      ⟨(gapProbeSmallAperture δ hδ).1 + L,
        by linarith [(gapProbeSmallAperture δ hδ).2]⟩
    (weightedPrimeFamily w).energy b₀ ≤
      gapProbeConst δ hδ - gapProbeCoeff δ hδ * (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 := by
  let a₀ := gapProbeSmallAperture δ hδ
  have ha₀_le : a₀.1 ≤ 1 / 16 := min_le_right _ _
  have hL_pos : 0 < L := lt_of_lt_of_le (by norm_num) hL
  let b₀ : SuzukiPositiveAperture := ⟨a₀.1 + L, by linarith [a₀.2]⟩
  obtain ⟨u₀, hu₀⟩ : ∃ u₀ : CCMArchimedeanFormDomain a₀, u₀ = gapProbeFormVector δ hδ := ⟨_, rfl⟩
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : suzukiApertureHilbert a₀, f₀ = gapProbeApertureVector δ hδ := ⟨_, rfl⟩
  have hf₀_to : ccmArchimedeanFormToAperture a₀ u₀ = f₀ := by
    rw [hf₀, hu₀]; rfl
  have hf₀_pos : 0 < ‖f₀‖ ^ 2 := by
    rw [hf₀]; exact gapProbeApertureVector_norm_sq_pos hδ
  obtain ⟨mPos, hmPos_def⟩ : ∃ mPos : ℝ,
      mPos = polarBumpMoment 0 (a₀.1 / 2) (gapProbeRadius_pos hδ) (1 / 2) := ⟨_, rfl⟩
  obtain ⟨mNeg, hmNeg_def⟩ : ∃ mNeg : ℝ,
      mNeg = polarBumpMoment 0 (a₀.1 / 2) (gapProbeRadius_pos hδ) (-1 / 2) := ⟨_, rfl⟩
  have habPos : a₀.1 + |L| ≤ b₀.1 := by rw [abs_of_pos hL_pos]
  have habNeg : a₀.1 + |-L| ≤ b₀.1 := by rw [abs_neg, abs_of_pos hL_pos]
  obtain ⟨v, hv⟩ : ∃ v : CCMArchimedeanFormDomain b₀,
      v = ccmArchimedeanFormTranslate (-L) habNeg u₀ - ccmArchimedeanFormTranslate L habPos u₀ :=
    ⟨_, rfl⟩
  obtain ⟨f, hf⟩ : ∃ f : suzukiApertureHilbert b₀, f = ccmArchimedeanFormToAperture b₀ v :=
    ⟨_, rfl⟩
  have hf_coe : (f : SoninL2) = logTranslationCLM (-L) f₀.1 - logTranslationCLM L f₀.1 := by
    rw [hf, hv, map_sub, Submodule.coe_sub, ccmArchimedeanFormTranslate_physical,
      ccmArchimedeanFormTranslate_physical, hf₀_to]
  have horth : inner ℂ (logTranslationCLM (-L) f₀.1) (logTranslationCLM L f₀.1) = 0 := by
    rw [inner_logTranslationCLM (-L), neg_neg, logTranslationCLM_add_apply]
    refine inner_eq_zero_symm.mpr (inner_logTranslationCLM_eq_zero_of_two_mul_le_abs a₀ f₀ f₀ ?_)
    rw [abs_of_pos (by linarith)]
    linarith
  have hf_norm_sq : ‖f‖ ^ 2 = 2 * ‖f₀‖ ^ 2 := by
    have horth' : inner ℂ (logTranslationCLM L f₀.1) (logTranslationCLM (-L) f₀.1) = 0 :=
      inner_eq_zero_symm.mpr horth
    have hcoe_norm : ‖f‖ = ‖(f : SoninL2)‖ := rfl
    have hcoe_norm₀ : ‖f₀‖ = ‖(f₀ : SoninL2)‖ := rfl
    rw [hcoe_norm, hcoe_norm₀, hf_coe]
    have h1 : ‖logTranslationCLM (-L) f₀.1 - logTranslationCLM L f₀.1‖ ^ 2 =
        (inner ℂ (logTranslationCLM (-L) f₀.1 - logTranslationCLM L f₀.1)
          (logTranslationCLM (-L) f₀.1 - logTranslationCLM L f₀.1)).re :=
      (CCMRemainderFamily.re_inner_self _).symm
    rw [h1, inner_sub_left, inner_sub_right, inner_sub_right, horth, horth',
      sub_zero, zero_sub, sub_neg_eq_add, Complex.add_re,
      CCMRemainderFamily.re_inner_self, CCMRemainderFamily.re_inner_self,
      norm_logTranslationCLM (-L), norm_logTranslationCLM L]
    ring
  -- Every active scale `n ∈ [2, ⌊e^{2 b₀}⌋]` has zero matrix element on `f`.
  have hweight_zero : (inner ℂ (ccmWeightedPrimeOperator w b₀ f) f).re = 0 := by
    unfold ccmWeightedPrimeOperator
    refine AbstractToolkit.re_inner_clm_sum_eq_zero_of_forall _ _ f f fun n hn => ?_
    by_cases hwn : w n = 0
    · rw [hwn, Complex.ofReal_zero, clm_zero_smul, AbstractToolkit.clm_zero_apply,
        inner_zero_left, Complex.zero_re]
    · have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hlogn : (1 / 2 : ℝ) < Real.log n := half_lt_log_of_two_le hn2
      have hdist : 2 * a₀.1 ≤ |Real.log n - 2 * L| := hgap n hn hwn
      obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = Real.log n := ⟨_, rfl⟩
      have hshift_zero : inner ℂ (logTranslationCLM h f.1) f.1 = 0 := by
        rw [hf_coe, map_sub, inner_sub_left, inner_sub_right, inner_sub_right,
          inner_logTranslation_two_shifts h (-L) (-L),
          inner_logTranslation_two_shifts h (-L) L,
          inner_logTranslation_two_shifts h L (-L),
          inner_logTranslation_two_shifts h L L]
        have z1 : inner ℂ (logTranslationCLM (h + -L - -L) f₀.1) f₀.1 = 0 :=
          inner_logTranslationCLM_eq_zero_of_two_mul_le_abs a₀ f₀ f₀ (by
            rw [show h + -L - -L = h by ring, hh_def,
              abs_of_pos (lt_trans (by norm_num) hlogn)]
            linarith)
        have z2 : inner ℂ (logTranslationCLM (h + -L - L) f₀.1) f₀.1 = 0 :=
          inner_logTranslationCLM_eq_zero_of_two_mul_le_abs a₀ f₀ f₀ (by
            rw [show h + -L - L = Real.log n - 2 * L by rw [hh_def]; ring]
            exact hdist)
        have z3 : inner ℂ (logTranslationCLM (h + L - -L) f₀.1) f₀.1 = 0 :=
          inner_logTranslationCLM_eq_zero_of_two_mul_le_abs a₀ f₀ f₀ (by
            rw [hh_def, abs_of_pos (by linarith)]
            linarith)
        have z4 : inner ℂ (logTranslationCLM (h + L - L) f₀.1) f₀.1 = 0 :=
          inner_logTranslationCLM_eq_zero_of_two_mul_le_abs a₀ f₀ f₀ (by
            rw [show h + L - L = h by ring, hh_def,
              abs_of_pos (lt_trans (by norm_num) hlogn)]
            linarith)
        rw [z1, z2, z3, z4]
        ring
      have hneg_zero : inner ℂ (logTranslationCLM (-h) f.1) f.1 = 0 := by
        rw [inner_logTranslationCLM (-h), neg_neg]
        exact inner_eq_zero_symm.mpr hshift_zero
      rw [re_inner_ofReal_smul_ccmPrimeTransportOperator, ← hh_def,
        hshift_zero, hneg_zero, add_zero, Complex.zero_re, mul_zero]
  -- Polar evaluation on `v`.
  have hpol₀_plus : inner ℂ (ccmPolarApertureVector a₀ (1 / 2)) f₀ = (mPos : ℂ) := by
    rw [← hf₀_to, hu₀, hmPos_def]
    exact inner_polar_bumpInteriorSource a₀ 0 (a₀.1 / 2)
      (gapProbeRadius_pos hδ) (gapProbeClosedBall_subset hδ) (1 / 2)
  have hpol₀_minus : inner ℂ (ccmPolarApertureVector a₀ (-1 / 2)) f₀ = (mNeg : ℂ) := by
    rw [← hf₀_to, hu₀, hmNeg_def]
    exact inner_polar_bumpInteriorSource a₀ 0 (a₀.1 / 2)
      (gapProbeRadius_pos hδ) (gapProbeClosedBall_subset hδ) (-1 / 2)
  have hpol_plus : inner ℂ (ccmPolarApertureVector b₀ (1 / 2)) f =
      (((Real.exp (L / 2) - Real.exp (-L / 2)) * mPos : ℝ) : ℂ) := by
    rw [hf, hv, map_sub, inner_sub_right,
      inner_polar_ccmArchimedeanFormTranslate (-L) habNeg (1 / 2) u₀,
      inner_polar_ccmArchimedeanFormTranslate L habPos (1 / 2) u₀,
      hf₀_to, hpol₀_plus]
    have h1 : -(1 / 2 : ℝ) * -L = L / 2 := by ring
    have h2 : -(1 / 2 : ℝ) * L = -L / 2 := by ring
    rw [h1, h2]
    push_cast
    ring
  have hpol_minus : inner ℂ (ccmPolarApertureVector b₀ (-1 / 2)) f =
      (((Real.exp (-L / 2) - Real.exp (L / 2)) * mNeg : ℝ) : ℂ) := by
    rw [hf, hv, map_sub, inner_sub_right,
      inner_polar_ccmArchimedeanFormTranslate (-L) habNeg (-1 / 2) u₀,
      inner_polar_ccmArchimedeanFormTranslate L habPos (-1 / 2) u₀,
      hf₀_to, hpol₀_minus]
    have h1 : -(-1 / 2 : ℝ) * -L = -L / 2 := by ring
    have h2 : -(-1 / 2 : ℝ) * L = L / 2 := by ring
    rw [h1, h2]
    push_cast
    ring
  have hpol_re : (inner ℂ (ccmPolarOperator b₀ f) f).re =
      -2 * (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 * (mPos * mNeg) := by
    rw [inner_ccmPolarOperator, hpol_plus, hpol_minus, Complex.conj_ofReal, Complex.conj_ofReal,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.ofReal_re]
    ring
  have hv_norm : ‖v‖ ^ 2 ≤ 4 * ‖u₀‖ ^ 2 := by
    have htri : ‖v‖ ≤ 2 * ‖u₀‖ := by
      rw [hv]
      calc ‖ccmArchimedeanFormTranslate (-L) habNeg u₀ -
              ccmArchimedeanFormTranslate L habPos u₀‖
          ≤ ‖ccmArchimedeanFormTranslate (-L) habNeg u₀‖ +
              ‖ccmArchimedeanFormTranslate L habPos u₀‖ := norm_sub_le _ _
        _ = ‖u₀‖ + ‖u₀‖ := by
              rw [norm_ccmArchimedeanFormTranslate, norm_ccmArchimedeanFormTranslate]
        _ = 2 * ‖u₀‖ := by ring
    calc ‖v‖ ^ 2 ≤ (2 * ‖u₀‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ = 4 * ‖u₀‖ ^ 2 := by ring
  have hscal_le : (ccmArchimedeanRemainderScalar * inner ℂ f f).re ≤
      |2 * gammaHardyPhaseRate 0 - 1| * (4 * ‖f₀‖ ^ 2) := by
    rw [ccmArchimedeanRemainderScalar, Complex.re_ofReal_mul, CCMRemainderFamily.re_inner_self,
      hf_norm_sq]
    calc (2 * gammaHardyPhaseRate 0 - 1) * (2 * ‖f₀‖ ^ 2)
        ≤ |2 * gammaHardyPhaseRate 0 - 1| * (2 * ‖f₀‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |2 * gammaHardyPhaseRate 0 - 1| * (4 * ‖f₀‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith [hf₀_pos]) (abs_nonneg _)
  have hQ_le : (weightedPrimeFamily w).Q b₀ v ≤
      (4 * ‖u₀‖ ^ 2 + |2 * gammaHardyPhaseRate 0 - 1| * (4 * ‖f₀‖ ^ 2)) -
        2 * (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 * (mPos * mNeg) := by
    have hsub := weightedPrimeFamily_Q_eq_primeFree_sub w b₀ v
    have hform := primeFreeFamily_Q_expand b₀ v
    rw [← hf] at hsub hform
    rw [hsub, hweight_zero, sub_zero, hform, hpol_re]
    linarith only [hv_norm, hscal_le]
  have hray := (weightedPrimeFamily w).energy_mul_formNorm_sq_le b₀ v
  rw [← hf, hf_norm_sq] at hray
  have h2pos : 0 < 2 * ‖f₀‖ ^ 2 := by positivity
  have hrhs_eq :
      (gapProbeConst δ hδ - gapProbeCoeff δ hδ * (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2) *
        (2 * ‖f₀‖ ^ 2) =
      (4 * ‖u₀‖ ^ 2 + |2 * gammaHardyPhaseRate 0 - 1| * (4 * ‖f₀‖ ^ 2)) -
        2 * (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 * (mPos * mNeg) := by
    unfold gapProbeConst gapProbeCoeff
    rw [← hu₀, ← hf₀, ← hmPos_def, ← hmNeg_def, sub_mul,
      div_mul_cancel₀ _ h2pos.ne']
    have hterm : mPos * mNeg / ‖f₀‖ ^ 2 * (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 *
        (2 * ‖f₀‖ ^ 2) =
        (mPos * mNeg / ‖f₀‖ ^ 2 * ‖f₀‖ ^ 2) *
          (2 * (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2) := by ring
    rw [hterm, div_mul_cancel₀ _ hf₀_pos.ne']
    ring
  exact le_of_mul_le_mul_right (le_trans hray (hQ_le.trans_eq hrhs_eq.symm)) h2pos

/-- **Multiplicative syndeticity / bounded-logarithmic-gap law:**
if `(weightedPrimeFamily w).energy` is bounded below across apertures, then for every `δ > 0` the
active logarithmic scales `{log n : n ≥ 2, w n ≠ 0}` meet `(2L - 2δ, 2L + 2δ)` for all
sufficiently large `L`. -/
theorem eventually_log_gap_dense_of_weightedPrimeFamily_energy_bddBelow {w : ℕ → ℝ}
    (hbdd : ∃ B : ℝ, ∀ a : SuzukiPositiveAperture, B ≤ (weightedPrimeFamily w).energy a)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ L : ℝ, M₀ ≤ L →
      ∃ n : ℕ, 2 ≤ n ∧ w n ≠ 0 ∧ |Real.log n - 2 * L| < 2 * δ := by
  obtain ⟨B, hB⟩ := hbdd
  have hc : 0 < gapProbeCoeff δ hδ := gapProbeCoeff_pos hδ
  set target : ℝ := max 1 ((gapProbeConst δ hδ - B + 1) / gapProbeCoeff δ hδ)
  have htarget_pos : 0 < target := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  set M₀ : ℝ := max (1 / 4) (2 * Real.sqrt target + 1)
  have hM₀_pos : 0 < M₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨M₀, hM₀_pos, fun L hL => ?_⟩
  by_contra hnone
  push Not at hnone
  have hL_quarter : (1 / 4 : ℝ) ≤ L := le_trans (le_max_left _ _) hL
  have hL_pos : 0 < L := lt_of_lt_of_le (by norm_num) hL_quarter
  have ha₀_le_δ : (gapProbeSmallAperture δ hδ).1 ≤ δ := min_le_left _ _
  have hgap : ∀ n ∈ Finset.Icc 2
      (Nat.floor (Real.exp (2 * ((gapProbeSmallAperture δ hδ).1 + L)))),
      w n ≠ 0 → 2 * (gapProbeSmallAperture δ hδ).1 ≤ |Real.log n - 2 * L| := by
    intro n hn hwn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
    exact le_trans (by linarith) (hnone n hn2 hwn)
  let b₀ : SuzukiPositiveAperture :=
    ⟨(gapProbeSmallAperture δ hδ).1 + L, by linarith [(gapProbeSmallAperture δ hδ).2]⟩
  have hprobe : (weightedPrimeFamily w).energy b₀ ≤
      gapProbeConst δ hδ - gapProbeCoeff δ hδ * (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 :=
    weightedPrimeFamily_energy_le_of_log_gap hδ w hL_quarter hgap
  have hexp_ge : L / 2 ≤ Real.exp (L / 2) - Real.exp (-L / 2) := by
    have h1 : L / 2 + 1 ≤ Real.exp (L / 2) := Real.add_one_le_exp (L / 2)
    have h2 : Real.exp (-L / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith only [h1, h2]
  have hL_half_gt : Real.sqrt target < L / 2 := by
    have hM2 : 2 * Real.sqrt target + 1 ≤ L := le_trans (le_max_right _ _) hL
    linarith
  have hsq_gt : target < (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 := by
    calc target = Real.sqrt target ^ 2 := (Real.sq_sqrt htarget_pos.le).symm
      _ < (L / 2) ^ 2 := pow_lt_pow_left₀ hL_half_gt (Real.sqrt_nonneg _) (by norm_num)
      _ ≤ (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hexp_ge 2
  have htarget_ge : (gapProbeConst δ hδ - B + 1) / gapProbeCoeff δ hδ ≤ target :=
    le_max_right _ _
  have hmul : gapProbeConst δ hδ - B + 1 <
      gapProbeCoeff δ hδ * (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 := by
    have h1 : gapProbeConst δ hδ - B + 1 ≤ target * gapProbeCoeff δ hδ :=
      (div_le_iff₀ hc).mp htarget_ge
    have h2 : target * gapProbeCoeff δ hδ <
        (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 * gapProbeCoeff δ hδ :=
      mul_lt_mul_of_pos_right hsq_gt hc
    linarith [mul_comm ((Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2) (gapProbeCoeff δ hδ)]
  have hB_le := hB b₀
  linarith only [hB_le, hprobe, hmul]

/-- **Multiplicative `(1 + ε)` short-interval density of active weights:**
if `(weightedPrimeFamily w).energy` is bounded below across apertures, then for every `ε > 0` and
all sufficiently large `X`, the open interval `(X, (1 + ε) X)` contains an integer `n ≥ 2` with
`w n ≠ 0`. -/
theorem eventually_exists_active_in_short_interval_of_energy_bddBelow {w : ℕ → ℝ}
    (hbdd : ∃ B : ℝ, ∀ a : SuzukiPositiveAperture, B ≤ (weightedPrimeFamily w).energy a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∃ n : ℕ, 2 ≤ n ∧ w n ≠ 0 ∧ X < (n : ℝ) ∧ (n : ℝ) < (1 + ε) * X := by
  have h1ε : 1 < 1 + ε := by linarith
  have hlog_pos : 0 < Real.log (1 + ε) := Real.log_pos h1ε
  set δ : ℝ := Real.log (1 + ε) / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨M₀, _, hdense⟩ :=
    eventually_log_gap_dense_of_weightedPrimeFamily_energy_bddBelow hbdd hδ
  refine ⟨Real.exp (2 * M₀), Real.exp_pos _, fun X hX => ?_⟩
  have hX_pos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  have hlogX_ge : 2 * M₀ ≤ Real.log X := by
    calc 2 * M₀ = Real.log (Real.exp (2 * M₀)) := (Real.log_exp _).symm
      _ ≤ Real.log X := Real.log_le_log (Real.exp_pos _) hX
  set L : ℝ := Real.log X / 2 + δ
  have hM₀_le_L : M₀ ≤ L := by dsimp [L]; linarith
  obtain ⟨n, hn2, hwn, hclose⟩ := hdense L hM₀_le_L
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn2)
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hclose
  have hlog_gt : Real.log X < Real.log n := by dsimp [L] at hlo; linarith
  have hlog_lt : Real.log n < Real.log ((1 + ε) * X) := by
    rw [Real.log_mul (by positivity) hX_pos.ne']
    dsimp [L, δ] at hhi
    linarith
  have hn_gt : X < (n : ℝ) := by
    rw [← Real.exp_log hX_pos, ← Real.exp_log hn_pos]
    exact Real.exp_lt_exp.mpr hlog_gt
  have hn_lt : (n : ℝ) < (1 + ε) * X := by
    rw [← Real.exp_log hn_pos, ← Real.exp_log (mul_pos (by positivity) hX_pos)]
    exact Real.exp_lt_exp.mpr hlog_lt
  exact ⟨n, hn2, hwn, hn_gt, hn_lt⟩

/-- **Multiplicative `(1 + ε)` short-interval prime-power law for `primeSetSemilocalFamily P`:**
if `(primeSetSemilocalFamily P).energy` is bounded below across apertures, then for every `ε > 0`
every sufficiently large multiplicative interval `(X, (1 + ε) X)` contains a prime power `p^k`
(`p ∈ P`, `p` prime, `k ≥ 1`). -/
theorem eventually_exists_primePow_in_short_interval_of_primeSetSemilocal_bddBelow {P : Set ℕ}
    (hbdd : ∃ B : ℝ, ∀ a : SuzukiPositiveAperture, B ≤ (primeSetSemilocalFamily P).energy a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      ∃ p ∈ P, p.Prime ∧ ∃ k : ℕ, 1 ≤ k ∧
        X < ((p ^ k : ℕ) : ℝ) ∧ ((p ^ k : ℕ) : ℝ) < (1 + ε) * X := by
  obtain ⟨X₀, hX₀, hact⟩ :=
    eventually_exists_active_in_short_interval_of_energy_bddBelow hbdd hε
  refine ⟨X₀, hX₀, fun X hX => ?_⟩
  obtain ⟨n, _, hne, hgt, hlt⟩ := hact X hX
  obtain ⟨p, hpP, hp, k, hk1, rfl⟩ := semilocalVonMangoldt_support_primePow hne
  exact ⟨p, hpP, hp, k, hk1, hgt, hlt⟩

/-! ## 4. Constructive `Finset` pigeonhole avoidance and cardinality-only `-Θ(e^A)` collapse -/

open Classical in
/-- Exponents `k ≥ 1` of `p ≥ 2` whose half-logarithm `k (log p)/2` enters `(M - 1/8, M + 9/8)`. -/
def activeExponents (M : ℝ) (p : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.floor (max 0 (4 * M + 5)))).filter
    (fun k => M - 1 / 8 < (k : ℝ) * Real.log p / 2 ∧ (k : ℝ) * Real.log p / 2 < M + 9 / 8)

theorem mem_activeExponents_of_close {M L δ : ℝ} (hML : M ≤ L) (hLM : L ≤ M + 1)
    (hδ : δ ≤ 1 / 32) {p k : ℕ} (hp : 2 ≤ p) (hk : 1 ≤ k)
    (hclose : |(k : ℝ) * Real.log p / 2 - L| < δ) :
    k ∈ activeExponents M p := by
  classical
  unfold activeExponents
  have hlogp : (1 / 2 : ℝ) < Real.log p := half_lt_log_of_two_le hp
  have habs := abs_lt.mp hclose
  have hlo : M - 1 / 8 < (k : ℝ) * Real.log p / 2 := by linarith
  have hhi : (k : ℝ) * Real.log p / 2 < M + 9 / 8 := by linarith
  have hk_lt : (k : ℝ) < 4 * M + 5 := by
    have hmul : (k : ℝ) * (1 / 2) ≤ (k : ℝ) * Real.log p :=
      mul_le_mul_of_nonneg_left hlogp.le (Nat.cast_nonneg k)
    linarith
  have hk_le_max : (k : ℝ) ≤ max 0 (4 * M + 5) := le_trans hk_lt.le (le_max_right _ _)
  have hk_floor : k ≤ Nat.floor (max 0 (4 * M + 5)) :=
    Nat.le_floor (by exact_mod_cast hk_le_max)
  exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hk, hk_floor⟩, hlo, hhi⟩

theorem card_activeExponents_le_five (M : ℝ) {p : ℕ} (hp : 2 ≤ p) :
    (activeExponents M p).card ≤ 5 := by
  classical
  rcases (activeExponents M p).eq_empty_or_nonempty with hemp | hne
  · rw [hemp, Finset.card_empty]; omega
  · set k₀ := (activeExponents M p).min' hne
    have hk₀_mem : k₀ ∈ activeExponents M p := Finset.min'_mem _ hne
    have hk₀_lo : M - 1 / 8 < (k₀ : ℝ) * Real.log p / 2 := by
      unfold activeExponents at hk₀_mem
      exact (Finset.mem_filter.mp hk₀_mem).2.1
    have hlogp : (1 / 2 : ℝ) < Real.log p := half_lt_log_of_two_le hp
    have hsub : activeExponents M p ⊆ Finset.Icc k₀ (k₀ + 4) := by
      intro k hk
      have hk_ge : k₀ ≤ k := Finset.min'_le _ k hk
      have hk_hi : (k : ℝ) * Real.log p / 2 < M + 9 / 8 := by
        unfold activeExponents at hk
        exact (Finset.mem_filter.mp hk).2.2
      refine Finset.mem_Icc.mpr ⟨hk_ge, ?_⟩
      by_contra hgt
      have hk5 : k₀ + 5 ≤ k := by omega
      have hcast : (5 : ℝ) ≤ (k : ℝ) - (k₀ : ℝ) := by
        have : ((k₀ + 5 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk5
        push_cast at this
        linarith
      have hdiff_lt : ((k : ℝ) - (k₀ : ℝ)) * (Real.log p / 2) < 5 / 4 := by
        have heq : ((k : ℝ) - (k₀ : ℝ)) * (Real.log p / 2) =
            (k : ℝ) * Real.log p / 2 - (k₀ : ℝ) * Real.log p / 2 := by ring
        linarith
      have hdiff_gt : (5 / 4 : ℝ) < ((k : ℝ) - (k₀ : ℝ)) * (Real.log p / 2) :=
        calc (5 / 4 : ℝ) = 5 * (1 / 4) := by norm_num
          _ < 5 * (Real.log p / 2) := by linarith
          _ ≤ ((k : ℝ) - (k₀ : ℝ)) * (Real.log p / 2) :=
              mul_le_mul_of_nonneg_right hcast (by linarith)
      linarith
    calc (activeExponents M p).card
        ≤ (Finset.Icc k₀ (k₀ + 4)).card := Finset.card_le_card hsub
      _ = 5 := by rw [Nat.card_Icc]; omega

/-- Uniform gap half-width `1 / (16 * (5r + 2))` depending only on the cardinality bound `r`. -/
def finitePrimeGridStep (r : ℕ) : ℝ :=
  1 / (16 * ((5 * r + 2 : ℕ) : ℝ))

theorem finitePrimeGridStep_pos (r : ℕ) : 0 < finitePrimeGridStep r := by
  unfold finitePrimeGridStep
  have hN : (0 : ℝ) < ((5 * r + 2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < 5 * r + 2 by omega)
  positivity

theorem finitePrimeGridStep_le_one_div_32 (r : ℕ) : finitePrimeGridStep r ≤ 1 / 32 := by
  unfold finitePrimeGridStep
  have hN : (2 : ℝ) ≤ ((5 * r + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ 5 * r + 2 by omega)
  have h32 : (32 : ℝ) ≤ 16 * ((5 * r + 2 : ℕ) : ℝ) := by linarith
  exact one_div_le_one_div_of_le (by norm_num) h32

/-- **Constructive `Finset` pigeonhole shift-avoidance theorem:**
for every cardinality bound `r : ℕ`, every `S : Finset ℕ` with `S.card ≤ r`, and every `M : ℝ`,
there exists a grid shift `L ∈ [M, M + 1]` at distance `≥ 2 * finitePrimeGridStep r` from every
prime-power logarithm `k log p` (`p ∈ S`, `p ≥ 2`, `k ≥ 1`). -/
theorem exists_shift_avoiding_finite_prime_powers (r : ℕ) (S : Finset ℕ) (hS : S.card ≤ r)
    (M : ℝ) :
    ∃ L : ℝ, M ≤ L ∧ L ≤ M + 1 ∧
      ∀ p ∈ S, 2 ≤ p → ∀ k : ℕ, 1 ≤ k →
        2 * finitePrimeGridStep r ≤ |(k : ℝ) * Real.log p - 2 * L| := by
  classical
  set N : ℕ := 5 * r + 2
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  set δ : ℝ := finitePrimeGridStep r
  have hδ_eq : δ = 1 / (16 * (N : ℝ)) := rfl
  have hδ_le : δ ≤ 1 / 32 := finitePrimeGridStep_le_one_div_32 r
  let grid : ℕ → ℝ := fun j => M + (j : ℝ) / (N : ℝ)
  set J : Finset ℕ := Finset.range N
  set S₂ : Finset ℕ := S.filter (fun p => 2 ≤ p)
  have hS₂_card : S₂.card ≤ r := le_trans (Finset.card_filter_le _ _) hS
  set Bad : Finset (Σ _ : ℕ, ℕ) := S₂.sigma (fun p => activeExponents M p)
  have hBad_card : Bad.card ≤ 5 * r := by
    rw [Finset.card_sigma]
    calc ∑ p ∈ S₂, (activeExponents M p).card
        ≤ ∑ _p ∈ S₂, 5 := Finset.sum_le_sum fun p hp =>
            card_activeExponents_le_five M (Finset.mem_filter.mp hp).2
      _ = S₂.card * 5 := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 5 * r := by omega
  let hit : (Σ _ : ℕ, ℕ) → Finset ℕ := fun x =>
    J.filter (fun j => |(x.2 : ℝ) * Real.log x.1 / 2 - grid j| < δ)
  have hhit_le_one : ∀ x, (hit x).card ≤ 1 := by
    intro x
    refine Finset.card_le_one.mpr ?_
    intro j₁ hj₁ j₂ hj₂
    by_contra hne
    have h₁ := abs_lt.mp (Finset.mem_filter.mp hj₁).2
    have h₂ := abs_lt.mp (Finset.mem_filter.mp hj₂).2
    have hdiff_lt : |grid j₁ - grid j₂| < 2 * δ := by
      rw [abs_lt]
      constructor <;> linarith
    have h1_le_abs : (1 : ℝ) ≤ |(j₁ : ℝ) - (j₂ : ℝ)| := by
      have hneZ : ((j₁ : ℤ) - (j₂ : ℤ)) ≠ 0 := by omega
      have hZ := Int.one_le_abs hneZ
      have hcast : (((j₁ : ℤ) - (j₂ : ℤ) : ℤ) : ℝ) = (j₁ : ℝ) - (j₂ : ℝ) := by push_cast; ring
      have habsZ : ((|(j₁ : ℤ) - (j₂ : ℤ)| : ℤ) : ℝ) = |(j₁ : ℝ) - (j₂ : ℝ)| := by
        rw [← hcast, Int.cast_abs]
      exact_mod_cast
        (show (1 : ℝ) ≤ ((|(j₁ : ℤ) - (j₂ : ℤ)| : ℤ) : ℝ) by exact_mod_cast hZ).trans_eq habsZ
    have hgrid_diff : |grid j₁ - grid j₂| = |(j₁ : ℝ) - (j₂ : ℝ)| / (N : ℝ) := by
      have : grid j₁ - grid j₂ = ((j₁ : ℝ) - (j₂ : ℝ)) / (N : ℝ) := by dsimp [grid]; ring
      rw [this, abs_div, abs_of_pos hN_pos]
    have hge : 1 / (N : ℝ) ≤ |grid j₁ - grid j₂| := by
      rw [hgrid_diff]
      exact div_le_div_of_nonneg_right h1_le_abs hN_pos.le
    have h2δ_lt : 2 * δ < 1 / (N : ℝ) := by
      rw [hδ_eq]
      have h1 : 2 * (1 / (16 * (N : ℝ))) = (1 / 8) * (1 / (N : ℝ)) := by ring
      have h2 : 0 < 1 / (N : ℝ) := one_div_pos.mpr hN_pos
      linarith
    linarith
  have hbiUnion_lt : (Bad.biUnion hit).card < J.card := by
    calc (Bad.biUnion hit).card
        ≤ ∑ x ∈ Bad, (hit x).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ Bad, 1 := Finset.sum_le_sum fun x _ => hhit_le_one x
      _ = Bad.card := by simp
      _ ≤ 5 * r := hBad_card
      _ < 5 * r + 2 := by omega
      _ = J.card := (Finset.card_range N).symm
  obtain ⟨j, hjJ, hjNot⟩ := Finset.exists_mem_notMem_of_card_lt_card hbiUnion_lt
  have hj_lt : j < N := Finset.mem_range.mp hjJ
  have hL_lo : M ≤ grid j := by
    dsimp [grid]
    have : 0 ≤ (j : ℝ) / (N : ℝ) := div_nonneg (Nat.cast_nonneg j) hN_pos.le
    linarith
  have hL_hi : grid j ≤ M + 1 := by
    dsimp [grid]
    have hj_le : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj_lt.le
    have : (j : ℝ) / (N : ℝ) ≤ 1 := (div_le_one hN_pos).mpr hj_le
    linarith
  refine ⟨grid j, hL_lo, hL_hi, fun p hpS hp2 k hk1 => ?_⟩
  by_contra hlt
  push Not at hlt
  have hclose : |(k : ℝ) * Real.log p / 2 - grid j| < δ := by
    have heq : (k : ℝ) * Real.log p - 2 * grid j =
        2 * ((k : ℝ) * Real.log p / 2 - grid j) := by ring
    rw [heq, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hlt
    linarith
  have hk_act : k ∈ activeExponents M p :=
    mem_activeExponents_of_close hL_lo hL_hi hδ_le hp2 hk1 hclose
  have hpS₂ : p ∈ S₂ := Finset.mem_filter.mpr ⟨hpS, hp2⟩
  have hmemBad : (⟨p, k⟩ : Σ _ : ℕ, ℕ) ∈ Bad := Finset.mem_sigma.mpr ⟨hpS₂, hk_act⟩
  have hmemHit : j ∈ hit ⟨p, k⟩ := Finset.mem_filter.mpr ⟨hjJ, hclose⟩
  exact hjNot (Finset.mem_biUnion.mpr ⟨⟨p, k⟩, hmemBad, hmemHit⟩)

/-- Exponential sinh-difference lower bound `(1/4) e^L ≤ (e^{L/2} - e^{-L/2})^2` for `2 ≤ L`. -/
theorem quarter_mul_exp_le_sinh_diff_sq {L : ℝ} (hL : 2 ≤ L) :
    (1 / 4 : ℝ) * Real.exp L ≤ (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 := by
  have hexp_ge2 : (2 : ℝ) ≤ Real.exp (L / 2) := by
    calc (2 : ℝ) ≤ L / 2 + 1 := by linarith
      _ ≤ Real.exp (L / 2) := Real.add_one_le_exp (L / 2)
  have hexp_neg_le1 : Real.exp (-L / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hdiff_ge : (1 / 2 : ℝ) * Real.exp (L / 2) ≤ Real.exp (L / 2) - Real.exp (-L / 2) := by
    linarith
  calc (1 / 4 : ℝ) * Real.exp L
      = ((1 / 2 : ℝ) * Real.exp (L / 2)) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]
        norm_num
        ring_nf
    _ ≤ (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hdiff_ge 2

/-- Cardinality-only additive constant `C_r` in the finite-prime `-Θ(e^A)` collapse law. -/
def finitePrimeCollapseConst (r : ℕ) : ℝ :=
  gapProbeConst (finitePrimeGridStep r) (finitePrimeGridStep_pos r)

/-- Cardinality-only positive exponential coefficient `c_r > 0` in the finite-prime `-Θ(e^A)`
collapse law. -/
def finitePrimeCollapseCoeff (r : ℕ) : ℝ :=
  (1 / 4 : ℝ) * Real.exp (-2) *
    gapProbeCoeff (finitePrimeGridStep r) (finitePrimeGridStep_pos r)

theorem finitePrimeCollapseCoeff_pos (r : ℕ) : 0 < finitePrimeCollapseCoeff r :=
  mul_pos (mul_pos (by norm_num) (Real.exp_pos _))
    (gapProbeCoeff_pos (finitePrimeGridStep_pos r))

/-- **Cardinality-uniform `-Θ(e^A)` ground-energy collapse for unrestricted weights on `S`-prime
powers:**
for every `r : ℕ`, every `S : Finset ℕ` with `S.card ≤ r`, every real weight `w : ℕ → ℝ` supported
on `{p^k : p ∈ S, p ≥ 2, k ≥ 1}` (`n ≥ 2`), and every aperture `A ≥ 4`,
`(weightedPrimeFamily w).energy A ≤ finitePrimeCollapseConst r - finitePrimeCollapseCoeff r * e^A`,
where `finitePrimeCollapseConst r` and `finitePrimeCollapseCoeff r > 0` depend **only on `r`**
(independent of `S` and `w`). -/
theorem weightedPrimeFamily_energy_le_neg_exp_of_finitePrimePowers (r : ℕ) (S : Finset ℕ)
    (hS : S.card ≤ r) (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 2 ≤ n → w n ≠ 0 → ∃ p ∈ S, 2 ≤ p ∧ ∃ k : ℕ, 1 ≤ k ∧ p ^ k = n)
    (A : SuzukiPositiveAperture) (hA : 4 ≤ A.1) :
    (weightedPrimeFamily w).energy A ≤
      finitePrimeCollapseConst r - finitePrimeCollapseCoeff r * Real.exp A.1 := by
  obtain ⟨L, hL_lo, hL_hi, havoid⟩ :=
    exists_shift_avoiding_finite_prime_powers r S hS (A.1 - 2)
  have hL2 : 2 ≤ L := by linarith
  have hL_quarter : (1 / 4 : ℝ) ≤ L := by linarith
  let a₀ := gapProbeSmallAperture (finitePrimeGridStep r) (finitePrimeGridStep_pos r)
  have ha₀_le_step : a₀.1 ≤ finitePrimeGridStep r := min_le_left _ _
  have ha₀_le_sixteenth : a₀.1 ≤ 1 / 16 := min_le_right _ _
  let b₀ : SuzukiPositiveAperture := ⟨a₀.1 + L, by linarith [a₀.2]⟩
  have hb₀_le_A : b₀.1 ≤ A.1 := by change a₀.1 + L ≤ A.1; linarith
  have hgap : ∀ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * (a₀.1 + L)))),
      w n ≠ 0 → 2 * a₀.1 ≤ |Real.log n - 2 * L| := by
    intro n hn hwn
    obtain ⟨p, hpS, hp2, k, hk1, rfl⟩ := hw n (Finset.mem_Icc.mp hn).1 hwn
    have hlog : Real.log ((p ^ k : ℕ) : ℝ) = (k : ℝ) * Real.log p := by
      rw [Nat.cast_pow, Real.log_pow]
    rw [hlog]
    exact le_trans (by linarith) (havoid p hpS hp2 k hk1)
  have hprobe : (weightedPrimeFamily w).energy b₀ ≤
      finitePrimeCollapseConst r -
        gapProbeCoeff (finitePrimeGridStep r) (finitePrimeGridStep_pos r) *
          (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 :=
    weightedPrimeFamily_energy_le_of_log_gap (finitePrimeGridStep_pos r) w hL_quarter hgap
  have hexp_L : Real.exp (-2) * Real.exp A.1 ≤ Real.exp L := by
    calc Real.exp (-2) * Real.exp A.1
        = Real.exp (A.1 - 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hL_lo
  have hsinh_ge : (1 / 4 : ℝ) * Real.exp (-2) * Real.exp A.1 ≤
      (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 := by
    calc (1 / 4 : ℝ) * Real.exp (-2) * Real.exp A.1
        = (1 / 4 : ℝ) * (Real.exp (-2) * Real.exp A.1) := by ring
      _ ≤ (1 / 4 : ℝ) * Real.exp L := mul_le_mul_of_nonneg_left hexp_L (by norm_num)
      _ ≤ (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 := quarter_mul_exp_le_sinh_diff_sq hL2
  have hc_pos : 0 < gapProbeCoeff (finitePrimeGridStep r) (finitePrimeGridStep_pos r) :=
    gapProbeCoeff_pos (finitePrimeGridStep_pos r)
  have hterm_ge : finitePrimeCollapseCoeff r * Real.exp A.1 ≤
      gapProbeCoeff (finitePrimeGridStep r) (finitePrimeGridStep_pos r) *
        (Real.exp (L / 2) - Real.exp (-L / 2)) ^ 2 := by
    unfold finitePrimeCollapseCoeff
    have hrw : (1 / 4 : ℝ) * Real.exp (-2) *
        gapProbeCoeff (finitePrimeGridStep r) (finitePrimeGridStep_pos r) * Real.exp A.1 =
        gapProbeCoeff (finitePrimeGridStep r) (finitePrimeGridStep_pos r) *
          ((1 / 4 : ℝ) * Real.exp (-2) * Real.exp A.1) := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left hsinh_ge hc_pos.le
  exact le_trans ((weightedPrimeFamily w).energy_antitone hb₀_le_A) (by linarith only [hprobe, hterm_ge])

/-- **Exponential `-Θ(e^A)` ground-energy collapse for `finitePrimeSetSemilocalFamily S`:**
every finite-prime semilocal truncation collapses at the maximal uncompensated `s = 1` pole rate,
with constants depending only on any upper bound `r` on `S.card`. -/
theorem finitePrimeSetSemilocal_energy_le_neg_exp {r : ℕ} (S : Finset ℕ) (hS : S.card ≤ r)
    (A : SuzukiPositiveAperture) (hA : 4 ≤ A.1) :
    (finitePrimeSetSemilocalFamily S).energy A ≤
      finitePrimeCollapseConst r - finitePrimeCollapseCoeff r * Real.exp A.1 := by
  refine weightedPrimeFamily_energy_le_neg_exp_of_finitePrimePowers r S hS
    (semilocalVonMangoldt (S : Set ℕ)) (fun n _ hne => ?_) A hA
  obtain ⟨p, hpS, hpPrime, k, hk1, rfl⟩ := semilocalVonMangoldt_support_primePow hne
  exact ⟨p, Finset.mem_coe.mp hpS, hpPrime.two_le, k, hk1, rfl⟩

/-- Direct multi-prime generalization of `exists_aperture_primeFree_and_singleSemilocal_energy_lt`:
for every `S : Finset ℕ` and real bound `K`, `(finitePrimeSetSemilocalFamily S).energy b < K` for
all sufficiently large apertures `b`. -/
theorem exists_aperture_finitePrimeSetSemilocal_energy_lt (S : Finset ℕ) (K : ℝ) :
    ∃ A₀ : ℝ, 0 < A₀ ∧ ∀ b : SuzukiPositiveAperture, A₀ ≤ b.1 →
      (finitePrimeSetSemilocalFamily S).energy b < K := by
  have hc := finitePrimeCollapseCoeff_pos S.card
  set A₀ : ℝ := max 4
    ((max 0 (finitePrimeCollapseConst S.card - K) + 1) / finitePrimeCollapseCoeff S.card)
  have hA₀_pos : 0 < A₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨A₀, hA₀_pos, fun b hb => ?_⟩
  have hb4 : 4 ≤ b.1 := le_trans (le_max_left _ _) hb
  have hcol := finitePrimeSetSemilocal_energy_le_neg_exp S le_rfl b hb4
  have hquot : (max 0 (finitePrimeCollapseConst S.card - K) + 1) /
      finitePrimeCollapseCoeff S.card < Real.exp b.1 := by
    calc (max 0 (finitePrimeCollapseConst S.card - K) + 1) / finitePrimeCollapseCoeff S.card
        ≤ A₀ := le_max_right _ _
      _ ≤ b.1 := hb
      _ < b.1 + 1 := lt_add_one b.1
      _ ≤ Real.exp b.1 := by linarith [Real.add_one_le_exp b.1]
  have hmul : finitePrimeCollapseConst S.card - K + 1 <
      finitePrimeCollapseCoeff S.card * Real.exp b.1 := by
    have h1 := (div_lt_iff₀ hc).mp hquot
    have h2 : finitePrimeCollapseConst S.card - K ≤
        max 0 (finitePrimeCollapseConst S.card - K) := le_max_right _ _
    linarith [mul_comm (Real.exp b.1) (finitePrimeCollapseCoeff S.card)]
  linarith only [hcol, hmul]

/-- **Impossibility of any sub-maximal exponential rate `O(e^{θ A})` (`θ < 1`):**
for every `S : Finset ℕ`, every weight `w` supported on `S`-prime-powers, and every exponent
`θ < 1` (corresponding to any nontrivial zero-free strip width `σ = θ / 2 < 1 / 2`), no constant `C`
can bound `(weightedPrimeFamily w).energy A` below by `-C e^{θ A}` across apertures. -/
theorem not_exists_sublinear_exp_lower_bound_for_weightedFinitePrimePowers (S : Finset ℕ)
    (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 2 ≤ n → w n ≠ 0 → ∃ p ∈ S, 2 ≤ p ∧ ∃ k : ℕ, 1 ≤ k ∧ p ^ k = n)
    {θ : ℝ} (hθ : θ < 1) :
    ¬ ∃ C : ℝ, ∀ A : SuzukiPositiveAperture,
      -(C * Real.exp (θ * A.1)) ≤ (weightedPrimeFamily w).energy A := by
  rintro ⟨C, hC⟩
  set θ0 : ℝ := max 0 θ
  have hθ0_nonneg : 0 ≤ θ0 := le_max_left _ _
  have hθ0_lt : θ0 < 1 := max_lt zero_lt_one hθ
  have hgap_pos : 0 < 1 - θ0 := sub_pos.mpr hθ0_lt
  set C' : ℝ := max 0 C
  have hC'_nonneg : 0 ≤ C' := le_max_left _ _
  set K : ℝ := max 0 (finitePrimeCollapseConst S.card)
  have hK_nonneg : 0 ≤ K := le_max_left _ _
  have hc := finitePrimeCollapseCoeff_pos S.card
  set A_val : ℝ := max 4 (((K + C' + 1) / finitePrimeCollapseCoeff S.card) / (1 - θ0))
  let A : SuzukiPositiveAperture := ⟨A_val, lt_of_lt_of_le (by norm_num) (le_max_left _ _)⟩
  have hA4 : 4 ≤ A.1 := le_max_left _ _
  have hcol := weightedPrimeFamily_energy_le_neg_exp_of_finitePrimePowers S.card S le_rfl w hw A hA4
  have hlow : -(C' * Real.exp (θ0 * A.1)) ≤ (weightedPrimeFamily w).energy A := by
    have h1 : C * Real.exp (θ * A.1) ≤ C' * Real.exp (θ * A.1) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
    have h2 : C' * Real.exp (θ * A.1) ≤ C' * Real.exp (θ0 * A.1) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) A.2.le)) hC'_nonneg
    exact le_trans (by linarith) (hC A)
  have hineq : finitePrimeCollapseCoeff S.card * Real.exp A.1 ≤
      K + C' * Real.exp (θ0 * A.1) := by
    have hK : finitePrimeCollapseConst S.card ≤ K := le_max_right _ _
    linarith only [hcol, hlow, hK]
  have hmul := mul_le_mul_of_nonneg_right hineq (Real.exp_pos (-(θ0 * A.1))).le
  have hlhs : finitePrimeCollapseCoeff S.card * Real.exp A.1 * Real.exp (-(θ0 * A.1)) =
      finitePrimeCollapseCoeff S.card * Real.exp ((1 - θ0) * A.1) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2; ring
  have hrhs : (K + C' * Real.exp (θ0 * A.1)) * Real.exp (-(θ0 * A.1)) ≤ K + C' := by
    rw [add_mul, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    have hexp_le1 : Real.exp (-(θ0 * A.1)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [A.2, hθ0_nonneg])
    have hKle : K * Real.exp (-(θ0 * A.1)) ≤ K * 1 :=
      mul_le_mul_of_nonneg_left hexp_le1 hK_nonneg
    linarith only [hKle]
  have hexp_lb : (1 - θ0) * A.1 + 1 ≤ Real.exp ((1 - θ0) * A.1) :=
    Real.add_one_le_exp ((1 - θ0) * A.1)
  have hAval_ge : ((K + C' + 1) / finitePrimeCollapseCoeff S.card) / (1 - θ0) ≤ A.1 :=
    le_max_right _ _
  have hprod_ge : (K + C' + 1) / finitePrimeCollapseCoeff S.card ≤ (1 - θ0) * A.1 := by
    have := (div_le_iff₀ hgap_pos).mp hAval_ge
    linarith [mul_comm A.1 (1 - θ0)]
  have hc_prod : K + C' + 1 ≤ finitePrimeCollapseCoeff S.card * ((1 - θ0) * A.1) := by
    have := (div_le_iff₀ hc).mp hprod_ge
    linarith [mul_comm ((1 - θ0) * A.1) (finitePrimeCollapseCoeff S.card)]
  have hc_exp : finitePrimeCollapseCoeff S.card * ((1 - θ0) * A.1 + 1) ≤
      finitePrimeCollapseCoeff S.card * Real.exp ((1 - θ0) * A.1) :=
    mul_le_mul_of_nonneg_left hexp_lb hc.le
  rw [hlhs] at hmul
  linarith [hmul.trans hrhs, hc_prod, hc_exp, hc]

theorem not_exists_sublinear_exp_lower_bound_for_finitePrimeSetSemilocal (S : Finset ℕ)
    {θ : ℝ} (hθ : θ < 1) :
    ¬ ∃ C : ℝ, ∀ A : SuzukiPositiveAperture,
      -(C * Real.exp (θ * A.1)) ≤ (finitePrimeSetSemilocalFamily S).energy A := by
  refine not_exists_sublinear_exp_lower_bound_for_weightedFinitePrimePowers S
    (semilocalVonMangoldt (S : Set ℕ)) (fun n _ hne => ?_) hθ
  obtain ⟨p, hpS, hpPrime, k, hk1, rfl⟩ := semilocalVonMangoldt_support_primePow hne
  exact ⟨p, Finset.mem_coe.mp hpS, hpPrime.two_le, k, hk1, rfl⟩

/-! ## 5. Forced zero crossings, positive-trace carrier no-go, prime counting, and infinitude -/

/-- Explicit cardinality-only ceiling `≥ 4` above which every `r`-prime semilocal ground energy is
strictly below `-1`. -/
def finitePrimeZeroCrossingCeiling (r : ℕ) : ℝ :=
  max 4 ((max 0 (finitePrimeCollapseConst r) + 1) / finitePrimeCollapseCoeff r)

theorem four_le_finitePrimeZeroCrossingCeiling (r : ℕ) :
    4 ≤ finitePrimeZeroCrossingCeiling r :=
  le_max_left _ _

theorem weightedPrimeFamily_energy_lt_neg_one_of_ceiling_le {r : ℕ} (S : Finset ℕ)
    (hS : S.card ≤ r) (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 2 ≤ n → w n ≠ 0 → ∃ p ∈ S, 2 ≤ p ∧ ∃ k : ℕ, 1 ≤ k ∧ p ^ k = n)
    {A : SuzukiPositiveAperture} (hA : finitePrimeZeroCrossingCeiling r ≤ A.1) :
    (weightedPrimeFamily w).energy A < -1 := by
  have hA4 : 4 ≤ A.1 := le_trans (four_le_finitePrimeZeroCrossingCeiling r) hA
  have hcol := weightedPrimeFamily_energy_le_neg_exp_of_finitePrimePowers r S hS w hw A hA4
  have hc := finitePrimeCollapseCoeff_pos r
  have hquot : (max 0 (finitePrimeCollapseConst r) + 1) / finitePrimeCollapseCoeff r <
      Real.exp A.1 := by
    calc (max 0 (finitePrimeCollapseConst r) + 1) / finitePrimeCollapseCoeff r
        ≤ finitePrimeZeroCrossingCeiling r := le_max_right _ _
      _ ≤ A.1 := hA
      _ < A.1 + 1 := lt_add_one A.1
      _ ≤ Real.exp A.1 := by linarith [Real.add_one_le_exp A.1]
  have hmul : finitePrimeCollapseConst r + 1 < finitePrimeCollapseCoeff r * Real.exp A.1 := by
    have h1 := (div_lt_iff₀ hc).mp hquot
    have h2 : finitePrimeCollapseConst r ≤ max 0 (finitePrimeCollapseConst r) := le_max_right _ _
    linarith [mul_comm (Real.exp A.1) (finitePrimeCollapseCoeff r)]
  linarith only [hcol, hmul]

theorem finitePrimeSetSemilocal_energy_lt_neg_one_of_ceiling_le {r : ℕ} (S : Finset ℕ)
    (hS : S.card ≤ r) {A : SuzukiPositiveAperture}
    (hA : finitePrimeZeroCrossingCeiling r ≤ A.1) :
    (finitePrimeSetSemilocalFamily S).energy A < -1 := by
  refine weightedPrimeFamily_energy_lt_neg_one_of_ceiling_le S hS
    (semilocalVonMangoldt (S : Set ℕ)) (fun n _ hne => ?_) hA
  obtain ⟨p, hpS, hpPrime, k, hk1, rfl⟩ := semilocalVonMangoldt_support_primePow hne
  exact ⟨p, Finset.mem_coe.mp hpS, hpPrime.two_le, k, hk1, rfl⟩

/-- **Unconditional zero crossing of every finite-prime semilocal Weil operator:**
for **every** finite set of primes `S : Finset ℕ`, there exists a critical aperture `a` with
`½ log 2 < a ≤ finitePrimeZeroCrossingCeiling S.card` at which
`(finitePrimeSetSemilocalFamily S).energy a = 0` and the Friedrichs operator acquires a nonzero
kernel state. -/
theorem exists_finitePrimeSetSemilocal_zero_crossing (S : Finset ℕ) :
    ∃ a : SuzukiPositiveAperture,
      Real.log 2 / 2 < a.1 ∧
      a.1 ≤ finitePrimeZeroCrossingCeiling S.card ∧
      (finitePrimeSetSemilocalFamily S).energy a = 0 ∧
      ∃ x : ((finitePrimeSetSemilocalFamily S).operator a).domain,
        (x : suzukiApertureHilbert a) ≠ 0 ∧
          (finitePrimeSetSemilocalFamily S).operator a x = 0 := by
  let a₀ := halfLogTwoAperture
  let a₁ : SuzukiPositiveAperture :=
    ⟨finitePrimeZeroCrossingCeiling S.card,
      lt_of_lt_of_le (by norm_num) (four_le_finitePrimeZeroCrossingCeiling S.card)⟩
  have hlog2_lt2 : Real.log 2 < 2 := by
    have hexp2 : (2 : ℝ) < Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    have h := Real.log_lt_log (by norm_num) hexp2
    rwa [Real.log_exp] at h
  have h01 : a₀.1 ≤ a₁.1 := by
    have h4 : (4 : ℝ) ≤ a₁.1 := four_le_finitePrimeZeroCrossingCeiling S.card
    change Real.log 2 / 2 ≤ a₁.1
    linarith
  have hge_floor : (1 / 5000 : ℝ) ≤ (finitePrimeSetSemilocalFamily S).energy a₀ := by
    rw [finitePrimeSetSemilocalFamily_energy_eq_literal_of_le_halfLogTwo S le_rfl,
      ← primeFreeFamily_energy_halfLogTwo]
    exact one_div_5000_le_primeFreeFamily_energy_halfLogTwo
  have h0 : 0 < (finitePrimeSetSemilocalFamily S).energy a₀ :=
    lt_of_lt_of_le (by norm_num) hge_floor
  have h1 : (finitePrimeSetSemilocalFamily S).energy a₁ < 0 :=
    lt_trans (finitePrimeSetSemilocal_energy_lt_neg_one_of_ceiling_le S le_rfl le_rfl)
      (by norm_num)
  obtain ⟨a, ha₀, ha₁, hzero⟩ :=
    (finitePrimeSetSemilocalFamily S).exists_energy_eq_zero h01 h0 h1
  have hstrict : Real.log 2 / 2 < a.1 := by
    refine lt_of_le_of_ne ha₀ fun heq => ?_
    have ha_eq : a = a₀ := Subtype.ext heq.symm
    rw [ha_eq] at hzero
    linarith
  exact ⟨a, hstrict, ha₁, hzero,
    (finitePrimeSetSemilocalFamily S).exists_kernel_of_energy_eq_zero hzero⟩

/-- Sharpened zero-crossing lower bound when `2 ∈ S`: the critical zero-crossing aperture lies
strictly above the certified full-sector threshold `181 / 500 > ½ log 2`. -/
theorem exists_finitePrimeSetSemilocal_zero_crossing_of_two_mem {S : Finset ℕ} (h2 : 2 ∈ S) :
    ∃ a : SuzukiPositiveAperture,
      (181 / 500 : ℝ) < a.1 ∧
      a.1 ≤ finitePrimeZeroCrossingCeiling S.card ∧
      (finitePrimeSetSemilocalFamily S).energy a = 0 ∧
      ∃ x : ((finitePrimeSetSemilocalFamily S).operator a).domain,
        (x : suzukiApertureHilbert a) ≠ 0 ∧
          (finitePrimeSetSemilocalFamily S).operator a x = 0 := by
  let a₀ : SuzukiPositiveAperture := ⟨181 / 500, by norm_num⟩
  let a₁ : SuzukiPositiveAperture :=
    ⟨finitePrimeZeroCrossingCeiling S.card,
      lt_of_lt_of_le (by norm_num) (four_le_finitePrimeZeroCrossingCeiling S.card)⟩
  have h01 : a₀.1 ≤ a₁.1 :=
    le_trans (by norm_num : (181 / 500 : ℝ) ≤ 4) (four_le_finitePrimeZeroCrossingCeiling S.card)
  have hge_floor : (1 / 5000 : ℝ) ≤ (finitePrimeSetSemilocalFamily S).energy a₀ := by
    rw [finitePrimeSetSemilocalFamily_energy_eq_literal_of_two_mem_of_le_halfLogThree h2
      threeHundredSixtyTwoThousandths_lt_half_log_three.le]
    exact one_div_5000_le_ccmRestrictedWeilGroundEnergy_threeHundredSixtyTwoThousandths le_rfl
  have h0 : 0 < (finitePrimeSetSemilocalFamily S).energy a₀ :=
    lt_of_lt_of_le (by norm_num) hge_floor
  have h1 : (finitePrimeSetSemilocalFamily S).energy a₁ < 0 :=
    lt_trans (finitePrimeSetSemilocal_energy_lt_neg_one_of_ceiling_le S le_rfl le_rfl)
      (by norm_num)
  obtain ⟨a, ha₀, ha₁, hzero⟩ :=
    (finitePrimeSetSemilocalFamily S).exists_energy_eq_zero h01 h0 h1
  have hstrict : (181 / 500 : ℝ) < a.1 := by
    refine lt_of_le_of_ne ha₀ fun heq => ?_
    have ha_eq : a = a₀ := Subtype.ext heq.symm
    rw [ha_eq] at hzero
    linarith
  exact ⟨a, hstrict, ha₁, hzero,
    (finitePrimeSetSemilocalFamily S).exists_kernel_of_energy_eq_zero hzero⟩

/-- **Universal positive operator-trace carrier no-go for unrestricted weights on `S`-prime
powers:**
for every `S : Finset ℕ` and every `w : ℕ → ℝ` supported on `S`-prime-powers, no family of positive
operators on a complex Hilbert space `H` can represent `(weightedPrimeFamily w).Q a u` as its real
operator trace across apertures. -/
theorem no_positive_operator_trace_carrier_for_weightedFinitePrimePowers {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ n : ℕ, 2 ≤ n → w n ≠ 0 → ∃ p ∈ S, 2 ≤ p ∧ ∃ k : ℕ, 1 ≤ k ∧ p ^ k = n) :
    ¬ ∃ R : ∀ a : SuzukiPositiveAperture, CCMArchimedeanFormDomain a → (H →L[ℂ] H),
      (∀ a u, ContinuousLinearMap.IsPositive (R a u)) ∧
      (∀ a u, (ContinuousLinearMap.opTrace (R a u)).re = (weightedPrimeFamily w).Q a u) := by
  let a₁ : SuzukiPositiveAperture :=
    ⟨finitePrimeZeroCrossingCeiling S.card,
      lt_of_lt_of_le (by norm_num) (four_le_finitePrimeZeroCrossingCeiling S.card)⟩
  have hneg : (weightedPrimeFamily w).energy a₁ < 0 :=
    lt_trans (weightedPrimeFamily_energy_lt_neg_one_of_ceiling_le S le_rfl w hw le_rfl)
      (by norm_num)
  refine AbstractToolkit.no_positive_operator_trace_carrier_of_exists_neg
    ⟨a₁, (weightedPrimeFamily w).normalizedGround a₁, ?_⟩
  rwa [(weightedPrimeFamily w).normalizedGround_Q]

/-- **Impossibility of any positive operator-trace carrier for `finitePrimeSetSemilocalFamily S`.** -/
theorem no_positive_operator_trace_carrier_for_finitePrimeSetSemilocal {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Finset ℕ) :
    ¬ ∃ R : ∀ a : SuzukiPositiveAperture, CCMArchimedeanFormDomain a → (H →L[ℂ] H),
      (∀ a u, ContinuousLinearMap.IsPositive (R a u)) ∧
      (∀ a u,
        (ContinuousLinearMap.opTrace (R a u)).re = (finitePrimeSetSemilocalFamily S).Q a u) := by
  refine no_positive_operator_trace_carrier_for_weightedFinitePrimePowers S
    (semilocalVonMangoldt (S : Set ℕ)) fun n _ hne => ?_
  obtain ⟨p, hpS, hpPrime, k, hk1, rfl⟩ := semilocalVonMangoldt_support_primePow hne
  exact ⟨p, Finset.mem_coe.mp hpS, hpPrime.two_le, k, hk1, rfl⟩

/-- **Impossibility of any positive Gram-sandwich trace carrier for
`finitePrimeSetSemilocalFamily S`.** -/
theorem no_positive_gram_trace_for_finitePrimeSetSemilocal {H K : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (S : Finset ℕ) :
    ¬ ∃ (M : H →L[ℂ] H)
        (Ψ : ∀ a : SuzukiPositiveAperture, CCMArchimedeanFormDomain a → (H →L[ℂ] K)),
      ContinuousLinearMap.IsPositive M ∧
      (∀ a u, (ContinuousLinearMap.opTrace
        (Ψ a u ∘L M ∘L ContinuousLinearMap.adjoint (Ψ a u))).re =
          (finitePrimeSetSemilocalFamily S).Q a u) := by
  let a₁ : SuzukiPositiveAperture :=
    ⟨finitePrimeZeroCrossingCeiling S.card,
      lt_of_lt_of_le (by norm_num) (four_le_finitePrimeZeroCrossingCeiling S.card)⟩
  have hneg : (finitePrimeSetSemilocalFamily S).energy a₁ < 0 :=
    lt_trans (finitePrimeSetSemilocal_energy_lt_neg_one_of_ceiling_le S le_rfl le_rfl)
      (by norm_num)
  refine AbstractToolkit.no_positive_gram_trace_carrier_of_exists_neg
    ⟨a₁, (finitePrimeSetSemilocalFamily S).normalizedGround a₁, ?_⟩
  rwa [(finitePrimeSetSemilocalFamily S).normalizedGround_Q]

/-- **Quantitative prime-counting lower bound from aperture positivity:**
if `0 ≤ ccmRestrictedWeilGroundEnergy A` at an aperture `A ≥ finitePrimeZeroCrossingCeiling r`,
then strictly more than `r` primes are visible below `⌊e^{2A}⌋` (`r < (visiblePrimes A).card`). -/
theorem card_visiblePrimes_gt_of_groundEnergy_nonneg {r : ℕ} {A : SuzukiPositiveAperture}
    (hpos : 0 ≤ ccmRestrictedWeilGroundEnergy A)
    (hA : finitePrimeZeroCrossingCeiling r ≤ A.1) :
    r < (visiblePrimes A).card := by
  by_contra hle
  push Not at hle
  have hlt := finitePrimeSetSemilocal_energy_lt_neg_one_of_ceiling_le (visiblePrimes A) hle hA
  rw [finitePrimeSetSemilocalFamily_visiblePrimes_energy] at hlt
  linarith

/-- **Constructive Euclid-type prime generator from aperture positivity:**
for any finite set `S : Finset ℕ`, if `0 ≤ ccmRestrictedWeilGroundEnergy A` at
`A ≥ finitePrimeZeroCrossingCeiling S.card`, then there exists a prime `q ≤ ⌊e^{2A}⌋` outside
`S`. -/
theorem exists_visiblePrime_notMem_of_groundEnergy_nonneg (S : Finset ℕ)
    {A : SuzukiPositiveAperture} (hpos : 0 ≤ ccmRestrictedWeilGroundEnergy A)
    (hA : finitePrimeZeroCrossingCeiling S.card ≤ A.1) :
    ∃ q ∈ visiblePrimes A, q ∉ S :=
  Finset.exists_mem_notMem_of_card_lt_card (card_visiblePrimes_gt_of_groundEnergy_nonneg hpos hA)

/-- **Global Weil stability requires infinitely many primes:**
if `(primeSetSemilocalFamily P).energy` is bounded below across positive apertures (and in
particular if it is nonnegative across apertures), then `P` contains infinitely many primes. -/
theorem infinite_primes_of_primeSetSemilocal_energy_bddBelow {P : Set ℕ}
    (hbdd : ∃ B : ℝ, ∀ a : SuzukiPositiveAperture, B ≤ (primeSetSemilocalFamily P).energy a) :
    (P ∩ {p : ℕ | p.Prime}).Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := hbdd
  let S : Finset ℕ := hfin.toFinset
  have hw : semilocalVonMangoldt P = semilocalVonMangoldt (S : Set ℕ) := by
    ext n
    rw [semilocalVonMangoldt_eq_inter_primes P n]
    have hcoe : (S : Set ℕ) = P ∩ {p : ℕ | p.Prime} := hfin.coe_toFinset
    rw [hcoe]
  obtain ⟨A₀, hA₀, hlt⟩ := exists_aperture_finitePrimeSetSemilocal_energy_lt S B
  let b : SuzukiPositiveAperture := ⟨A₀, hA₀⟩
  have heq : (primeSetSemilocalFamily P).energy b =
      (finitePrimeSetSemilocalFamily S).energy b := by
    refine ccmRemainderFamily_energy_eq_of_B_eq _ _ b ?_
    exact weightedPrimeFamily_B_congr fun n _ => congrFun hw n
  have hBb := hB b
  have hltb := hlt b le_rfl
  linarith

theorem infinite_primes_of_primeSetSemilocal_energy_nonneg {P : Set ℕ}
    (hnonneg : ∀ a : SuzukiPositiveAperture, 0 ≤ (primeSetSemilocalFamily P).energy a) :
    (P ∩ {p : ℕ | p.Prime}).Infinite :=
  infinite_primes_of_primeSetSemilocal_energy_bddBelow ⟨0, hnonneg⟩

theorem infinite_primes_of_primeSetSemilocal_Q_nonneg {P : Set ℕ}
    (hQ : ∀ (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a),
      0 ≤ (primeSetSemilocalFamily P).Q a u) :
    (P ∩ {p : ℕ | p.Prime}).Infinite :=
  infinite_primes_of_primeSetSemilocal_energy_nonneg fun a => by
    have h := hQ a ((primeSetSemilocalFamily P).normalizedGround a)
    rwa [(primeSetSemilocalFamily P).normalizedGround_Q] at h

/-- **Complete finite-prime semilocal & multiplicative syndeticity synthesis:**
packages the multi-prime `ValuationShellL2` trace identity, the cardinality-uniform `-Θ(e^A)`
ground-energy collapse for arbitrary finite sets of primes `S` and arbitrary prime-power weights,
the unconditional forced zero crossings and Friedrichs kernels, the impossibility of positive
operator-trace carriers, the multiplicative `(1 + ε)` short-interval syndeticity law under
boundedness below, and the infinitude of primes required for global Weil positivity. -/
theorem finite_prime_semilocal_complete_resolution :
    (∀ (S : Finset ℕ) (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a),
      (finitePrimeSetSemilocalFamily S).Q a u =
        archPart a u +
          (ContinuousLinearMap.opTrace (ccmPolarOperator a ∘L
            InnerProductSpace.rankOne ℂ (ccmArchimedeanFormToAperture a u)
              (ccmArchimedeanFormToAperture a u))).re -
          ∑ p ∈ S.filter Nat.Prime,
            ∑ m ∈ Finset.Icc 1 (Nat.floor (Real.exp (2 * a.1))),
              ((((1 / ((m : ℝ) * Real.sqrt ((p ^ m : ℕ) : ℝ)) : ℝ) : ℂ) *
                ContinuousLinearMap.opTrace (primeValuationLogOperator p m)) *
                ContinuousLinearMap.opTrace
                  (ccmApertureCompression a
                    (ccmSymmetricLogTranslation (Real.log ((p ^ m : ℕ) : ℝ))) ∘L
                    InnerProductSpace.rankOne ℂ (ccmArchimedeanFormToAperture a u)
                      (ccmArchimedeanFormToAperture a u))).re) ∧
    (∀ (r : ℕ) (S : Finset ℕ), S.card ≤ r →
      ∀ (A : SuzukiPositiveAperture), 4 ≤ A.1 →
        (finitePrimeSetSemilocalFamily S).energy A ≤
          finitePrimeCollapseConst r - finitePrimeCollapseCoeff r * Real.exp A.1) ∧
    (∀ S : Finset ℕ, ∃ a : SuzukiPositiveAperture,
      Real.log 2 / 2 < a.1 ∧
      a.1 ≤ finitePrimeZeroCrossingCeiling S.card ∧
      (finitePrimeSetSemilocalFamily S).energy a = 0 ∧
      ∃ x : ((finitePrimeSetSemilocalFamily S).operator a).domain,
        (x : suzukiApertureHilbert a) ≠ 0 ∧
          (finitePrimeSetSemilocalFamily S).operator a x = 0) ∧
    (∀ S : Finset ℕ,
      ¬ ∃ R : ∀ a : SuzukiPositiveAperture, CCMArchimedeanFormDomain a →
          (ValuationShellL2 →L[ℂ] ValuationShellL2),
        (∀ a u, ContinuousLinearMap.IsPositive (R a u)) ∧
        (∀ a u,
          (ContinuousLinearMap.opTrace (R a u)).re =
            (finitePrimeSetSemilocalFamily S).Q a u)) ∧
    (∀ (P : Set ℕ),
      (∃ B : ℝ, ∀ a : SuzukiPositiveAperture, B ≤ (primeSetSemilocalFamily P).energy a) →
        (P ∩ {p : ℕ | p.Prime}).Infinite ∧
        ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℝ, 0 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
          ∃ p ∈ P, p.Prime ∧ ∃ k : ℕ, 1 ≤ k ∧
            X < ((p ^ k : ℕ) : ℝ) ∧ ((p ^ k : ℕ) : ℝ) < (1 + ε) * X) :=
  ⟨finitePrimeSetSemilocalFamily_Q_eq_multiPrimeValuationTrace,
   fun _ S hS A hA => finitePrimeSetSemilocal_energy_le_neg_exp S hS A hA,
   exists_finitePrimeSetSemilocal_zero_crossing,
   no_positive_operator_trace_carrier_for_finitePrimeSetSemilocal,
   fun _ hbdd => ⟨infinite_primes_of_primeSetSemilocal_energy_bddBelow hbdd,
     fun _ hε => eventually_exists_primePow_in_short_interval_of_primeSetSemilocal_bddBelow hbdd hε⟩⟩

end GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace

end
