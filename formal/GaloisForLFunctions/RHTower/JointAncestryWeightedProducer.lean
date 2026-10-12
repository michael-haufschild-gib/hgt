import GaloisForLFunctions.RHTower.JointAncestryWeightedLevel
import GaloisForLFunctions.RHTower.JointAncestryLogBudgetProducer

/-!
# The dressed JAS producer

The undressed producer (`exists_jasProductPositive_logBudget_vk`) stops at prime budget
`(log y)^{3/2−ε}`.  The limit comes from the tail `Σ_{|γ|>T} 1/|ρ(1−ρ)| ≍ log T / T` of the zero
weights, which has to beat `e^B`.  A dressing that decays in `|Im ρ|` removes this limit.

**Zero-sum bound** (`weightedAggregate_re_ge_exp`).  For every dressing,
`Re Σ_ρ g(ρ)w_ρ ∏_P(⋯) ≥ ∏_P(1 + |z_p|²) · (Φ_g(0) − Σ_ρ (e^{E_ρ} − 1)|g(ρ)w_ρ|)`, with
`E_ρ = Σ_P p^{−(σ−|Re ρ−½|)}`.

**Height split** (`weightedAggregate_re_nonneg_of_heightSplit`).  If the zeros up to height `T` have
width `ω`, if `|g| ≤ ε` above height `T`, and if `e^{−ω log y} B ≤ t₁` with
`(e^{t₁} − 1) V ≤ Φ_g(0)/2` and `(e^B − 1) ε W ≤ Φ_g(0)/2`, then the dressed tests are positive on
every set of primes `p > y` of budget `≤ B`.

**Gaussian dressing** (`gaussDressing`).  `g_τ(s) = e^{|τ|(s−½)²}` satisfies
`|g_τ(ρ)| ≤ e^{|τ|/4} e^{−|τ| (Im ρ)²}`, it is positive on the critical line, and
`Φ_{g_τ}(0) → Φ(0) = 2 + γ − log 4π > 0` as `τ → 0`.
-/

open Complex Filter Topology
open scoped ComplexConjugate

namespace RHTower

noncomputable section

variable (D : LagDressing)

/-! ## The dressed zero-sum bound -/

theorem summable_weightedAggregate (P : Finset Nat.Primes) (c : ℝ) (z : Nat.Primes → ℂ) :
    Summable fun q : XiZeroCopy =>
      (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + c) p) (jasHoloB ((q.1 : ℂ) - c) p) (z p)) *
        D.weight q := by
  refine Summable.of_norm_bounded ((summable_jasBernoulliAggregate P c z).norm.mul_left D.K)
    fun q => ?_
  have e : (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + c) p) (jasHoloB ((q.1 : ℂ) - c) p)
      (z p)) * D.weight q = D.g (q.1 : ℂ) * ((∏ p ∈ P, jasBernoulliFactor
        (jasHoloA ((q.1 : ℂ) + c) p) (jasHoloB ((q.1 : ℂ) - c) p) (z p)) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
    unfold LagDressing.weight; ring
  rw [e, norm_mul]
  exact mul_le_mul_of_nonneg_right (D.norm_le q) (norm_nonneg _)

/-- **The dressed zero-sum bound.** -/
theorem weightedAggregate_re_ge_exp {σ : ℝ} (P : Finset Nat.Primes) (z : Nat.Primes → ℂ) :
    (∏ p ∈ P, (1 + ‖z p‖ ^ 2)) * (dLagReal D 0 - ∑' q : XiZeroCopy,
      (Real.exp (∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p)) - 1) *
        ‖D.weight q‖) ≤
    (∑' q : XiZeroCopy, (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) * D.weight q).re := by
  obtain ⟨e, hedef⟩ : ∃ e : XiZeroCopy → ℝ, e = fun q =>
      Real.exp (∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p)) - 1 := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = ∏ p ∈ P, (1 + ‖z p‖ ^ 2) := ⟨_, rfl⟩
  have hfold : ∀ q : XiZeroCopy, (Real.exp (∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) *
      Real.log p)) - 1) * ‖D.weight q‖ = e q * ‖D.weight q‖ :=
    fun q => by rw [hedef]
  simp_rw [hfold]
  rw [← hCdef]
  have hC0 : 0 ≤ C := by rw [hCdef]; exact Finset.prod_nonneg fun _ _ => by positivity
  have he0 : ∀ q, 0 ≤ e q := fun q => by
    rw [hedef]
    linarith [Real.one_le_exp (Finset.sum_nonneg fun p (_ : p ∈ P) =>
      (Real.exp_pos (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p)).le)]
  have heB : ∀ q, e q ≤ Real.exp (∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log p)) - 1 := by
    intro q
    rw [hedef]
    have hab : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
    have : ∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p) ≤
        ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log p) :=
      Finset.sum_le_sum fun p _ => Real.exp_le_exp.mpr (by nlinarith [log_prime_pos p])
    linarith [Real.exp_le_exp.mpr this]
  obtain ⟨u, hudef⟩ : ∃ u : XiZeroCopy → Nat.Primes → ℂ, u = fun q p =>
      (z p * jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p +
        conj (z p) * jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) / ((1 + ‖z p‖ ^ 2 : ℝ) : ℂ) :=
    ⟨_, rfl⟩
  have hu : ∀ q, ∀ p, ‖u q p‖ ≤ Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p) :=
    fun q p => by
      rw [hudef]
      exact norm_jasBernoulliRatio_le (norm_jasHoloA_dressed_le_abs σ q p)
        (norm_jasHoloB_dressed_le_abs σ q p)
  have hprod : ∀ q : XiZeroCopy, ∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) +
      (σ - 1 / 2 : ℝ)) p) (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p) =
      (C : ℂ) * ∏ p ∈ P, (1 + u q p) := by
    intro q
    rw [hCdef, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [jasBernoulliFactor_eq_mul, hudef]
  have hterm : ∀ q : XiZeroCopy, C * ((D.weight q).re - e q * ‖D.weight q‖) ≤
      ((∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) * D.weight q).re := by
    intro q
    have hE : ‖∏ p ∈ P, (1 + u q p) - 1‖ ≤ e q := by
      refine (norm_prod_one_add_sub_one_le_exp P (u q)).trans ?_
      rw [hedef]
      linarith [Real.exp_le_exp.mpr (Finset.sum_le_sum fun p (_ : p ∈ P) => hu q p)]
    obtain ⟨E, hEdef⟩ : ∃ E : ℂ, E = ∏ p ∈ P, (1 + u q p) - 1 := ⟨_, rfl⟩
    rw [← hEdef] at hE
    have e' : (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) * D.weight q =
        (C : ℂ) * (D.weight q + E * D.weight q) := by
      rw [hprod q]
      have : ∏ p ∈ P, (1 + u q p) = 1 + E := by rw [hEdef]; ring
      rw [this]
      ring
    rw [e', Complex.re_ofReal_mul, Complex.add_re]
    have h1 : -(e q * ‖D.weight q‖) ≤ (E * D.weight q).re := by
      have := Complex.abs_re_le_norm (E * D.weight q)
      rw [norm_mul] at this
      have h2 : ‖E‖ * ‖D.weight q‖ ≤ e q * ‖D.weight q‖ :=
        mul_le_mul_of_nonneg_right hE (norm_nonneg _)
      linarith [neg_abs_le (E * D.weight q).re]
    exact mul_le_mul_of_nonneg_left (by linarith) hC0
  have hsum := summable_weightedAggregate D P (σ - 1 / 2) z
  have hw : Summable D.weight := D.summable_norm_weight.of_norm
  have hwre : Summable fun q => (D.weight q).re := (Complex.hasSum_re hw.hasSum).summable
  have hdw : Summable fun q => e q * ‖D.weight q‖ :=
    Summable.of_nonneg_of_le (fun q => mul_nonneg (he0 q) (norm_nonneg _))
      (fun q => mul_le_mul_of_nonneg_right (heB q) (norm_nonneg _))
      (D.summable_norm_weight.mul_left _)
  have hlow : Summable fun q : XiZeroCopy => C * ((D.weight q).re - e q * ‖D.weight q‖) :=
    (hwre.sub hdw).mul_left C
  rw [Complex.re_tsum hsum]
  refine le_trans ?_ (hlow.tsum_le_tsum hterm (Complex.hasSum_re hsum.hasSum).summable)
  rw [tsum_mul_left, hwre.tsum_sub hdw]
  have hR : ∑' q, (D.weight q).re = dLagReal D 0 := by
    rw [← Complex.re_tsum hw]
    unfold dLagReal
    rw [dLag_zero]
  rw [hR]

/-! ## The height split -/

/-- **Height-split producer for a dressing.** -/
theorem weightedAggregate_re_nonneg_of_heightSplit {σ y B T ω t₁ ε : ℝ} (hy0 : 0 < y)
    (hω0 : 0 ≤ ω) (P : Finset Nat.Primes) (hP : ∀ p ∈ P, y < ((p : ℕ) : ℝ))
    (hB : ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤ B)
    (hwidth : ∀ q : XiZeroCopy, |(q.1 : ℂ).im| ≤ T → ω ≤ 1 / 2 - |(q.1 : ℂ).re - 1 / 2|)
    (hgT : ∀ q : XiZeroCopy, T < |(q.1 : ℂ).im| → ‖D.g (q.1 : ℂ)‖ ≤ ε) (hε : 0 ≤ ε)
    (ht₁ : 0 ≤ t₁) (hexpt : (Real.exp t₁ - 1) * D.total ≤ dLagReal D 0 / 2)
    (hlow : Real.exp (-(ω * Real.log y)) * B ≤ t₁)
    (htail : (Real.exp B - 1) * (ε * lagWeightTotal) ≤ dLagReal D 0 / 2)
    (z : Nat.Primes → ℂ) :
    0 ≤ (∑' q : XiZeroCopy,
      (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) * D.weight q).re := by
  have hlogp : ∀ p ∈ P, Real.log y ≤ Real.log ((p : ℕ) : ℝ) := fun p hp =>
    Real.log_le_log hy0 (hP p hp).le
  have hlogy : ∀ p ∈ P, 0 ≤ Real.log ((p : ℕ) : ℝ) := fun p _ => log_prime_pos p |>.le
  have hb12 : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := fun q => by
    rw [abs_le]; constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
  have hB0 : 0 ≤ B := le_trans (Finset.sum_nonneg fun p _ => (Real.exp_pos _).le) hB
  have hlowsum : ∀ q : XiZeroCopy, |(q.1 : ℂ).im| ≤ T →
      ∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ)) ≤ t₁ := by
    intro q hq
    have hw := hwidth q hq
    have hterm : ∀ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ)) ≤
        Real.exp (-(ω * Real.log y)) * Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) := by
      intro p hp
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have h1 := hlogp p hp
      have h2 : ω * Real.log y ≤ (1 / 2 - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ) := by
        rcases le_or_gt 0 (Real.log y) with hly | hly
        · calc ω * Real.log y ≤ ω * Real.log ((p : ℕ) : ℝ) := mul_le_mul_of_nonneg_left h1 hω0
            _ ≤ _ := mul_le_mul_of_nonneg_right hw (hlogy p hp)
        · have : ω * Real.log y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hω0 hly.le
          have : 0 ≤ (1 / 2 - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ) :=
            mul_nonneg (by linarith) (hlogy p hp)
          linarith
      linarith
    calc ∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ))
        ≤ ∑ p ∈ P, Real.exp (-(ω * Real.log y)) *
            Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) := Finset.sum_le_sum hterm
      _ = Real.exp (-(ω * Real.log y)) *
            ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ Real.exp (-(ω * Real.log y)) * B := mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le
      _ ≤ t₁ := hlow
  have hhighsum : ∀ q : XiZeroCopy,
      ∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ)) ≤ B := by
    intro q
    refine le_trans (Finset.sum_le_sum fun p hp => Real.exp_le_exp.mpr ?_) hB
    have h1 := hlogy p hp
    have h2 := hb12 q
    nlinarith
  obtain ⟨E, hEdef⟩ : ∃ E : ℝ, E = Real.exp B - 1 := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hEdef]; linarith [Real.one_le_exp hB0]
  have hterm : ∀ q : XiZeroCopy, (Real.exp (∑ p ∈ P,
      Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ))) - 1) * ‖D.weight q‖ ≤
      (Real.exp t₁ - 1) * ‖D.weight q‖ +
        E * {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator
          (fun q => ε * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q := by
    intro q
    have hn := norm_nonneg (D.weight q)
    have ht0 : 0 ≤ Real.exp t₁ - 1 := by linarith [Real.one_le_exp ht₁]
    by_cases hq : T < |(q.1 : ℂ).im|
    · rw [Set.indicator_of_mem (show q ∈ {q : XiZeroCopy | T < |(q.1 : ℂ).im|} from hq)]
      have h1 : Real.exp (∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) *
          Real.log ((p : ℕ) : ℝ))) - 1 ≤ E := by
        rw [hEdef]; linarith [Real.exp_le_exp.mpr (hhighsum q)]
      have h2 : ‖D.weight q‖ ≤ ε * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
        rw [LagDressing.weight_eq, norm_mul]
        exact mul_le_mul_of_nonneg_right (hgT q hq) (norm_nonneg _)
      have h3 : 0 ≤ Real.exp (∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) *
          Real.log ((p : ℕ) : ℝ))) - 1 := by
        linarith [Real.one_le_exp (Finset.sum_nonneg fun p (_ : p ∈ P) =>
          (Real.exp_pos (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ))).le)]
      have h4 := mul_le_mul h1 h2 hn hE0
      nlinarith
    · rw [Set.indicator_of_notMem (show q ∉ {q : XiZeroCopy | T < |(q.1 : ℂ).im|} from hq),
        mul_zero, add_zero]
      push Not at hq
      exact mul_le_mul_of_nonneg_right (by linarith [Real.exp_le_exp.mpr (hlowsum q hq)]) hn
  have hind : Summable fun q : XiZeroCopy => {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator
      (fun q => ε * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q :=
    (summable_inv_mul_one_sub.norm.mul_left ε).indicator _
  have hsumR : Summable fun q : XiZeroCopy =>
      (Real.exp t₁ - 1) * ‖D.weight q‖ +
        E * {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator
          (fun q => ε * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q :=
    (D.summable_norm_weight.mul_left _).add (hind.mul_left _)
  have hsumL : Summable fun q : XiZeroCopy => (Real.exp (∑ p ∈ P,
      Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ))) - 1) * ‖D.weight q‖ := by
    refine Summable.of_nonneg_of_le (fun q => mul_nonneg ?_ (norm_nonneg _)) hterm hsumR
    linarith [Real.one_le_exp (Finset.sum_nonneg fun p (_ : p ∈ P) =>
      (Real.exp_pos (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ))).le)]
  have hZ := hsumL.tsum_le_tsum hterm hsumR
  rw [(D.summable_norm_weight.mul_left _).tsum_add (hind.mul_left _), tsum_mul_left,
    tsum_mul_left] at hZ
  have hind_le : ∑' q : XiZeroCopy, {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator
      (fun q => ε * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q ≤ ε * lagWeightTotal := by
    unfold lagWeightTotal
    rw [← tsum_mul_left]
    refine hind.tsum_le_tsum (fun q => ?_) (summable_inv_mul_one_sub.norm.mul_left ε)
    by_cases hq : T < |(q.1 : ℂ).im|
    · rw [Set.indicator_of_mem (show q ∈ {q : XiZeroCopy | T < |(q.1 : ℂ).im|} from hq)]; rfl
    · rw [Set.indicator_of_notMem (show q ∉ {q : XiZeroCopy | T < |(q.1 : ℂ).im|} from hq)]
      exact mul_nonneg hε (norm_nonneg _)
  have htailb : E * ∑' q : XiZeroCopy, {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator
      (fun q => ε * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q ≤ dLagReal D 0 / 2 := by
    rw [← hEdef] at htail
    exact (mul_le_mul_of_nonneg_left hind_le hE0).trans htail
  have htot : ∑' q : XiZeroCopy, ‖D.weight q‖ = D.total := rfl
  rw [htot] at hZ
  refine le_trans (mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) ?_)
    (weightedAggregate_re_ge_exp D (σ := σ) P z)
  linarith

/-! ## The Gaussian dressing -/

theorem re_sq_sub_half_le (q : XiZeroCopy) :
    (((q.1 : ℂ) - 1 / 2) ^ 2).re ≤ 1 / 4 - (q.1 : ℂ).im ^ 2 := by
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have e : (((q.1 : ℂ) - 1 / 2) ^ 2).re = ((q.1 : ℂ).re - 1 / 2) ^ 2 - (q.1 : ℂ).im ^ 2 := by
    simp [sq, Complex.mul_re]
  rw [e]
  nlinarith

/-- The Gaussian dressing `g_τ(s) = e^{|τ|(s−½)²}`. -/
def gaussDressing (τ : ℝ) : LagDressing where
  g s := Complex.exp (|τ| * (s - 1 / 2) ^ 2)
  K := Real.exp (|τ| / 4)
  K_nonneg := (Real.exp_pos _).le
  norm_le q := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (((|τ| : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2) ^ 2).re =
        |τ| * (((q.1 : ℂ) - 1 / 2) ^ 2).re := Complex.re_ofReal_mul _ _
    rw [hre]
    have := re_sq_sub_half_le q
    have ht := abs_nonneg τ
    nlinarith [sq_nonneg ((q.1 : ℂ).im)]
  ne_zero q := Complex.exp_ne_zero _
  conj_eq s := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_pow, map_sub, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
  reflect_eq s := by congr 1; ring

theorem norm_gaussDressing_g_le (τ : ℝ) (q : XiZeroCopy) :
    ‖(gaussDressing τ).g (q.1 : ℂ)‖ ≤ Real.exp (|τ| / 4) * Real.exp (-(|τ| * (q.1 : ℂ).im ^ 2)) := by
  change ‖Complex.exp (|τ| * ((q.1 : ℂ) - 1 / 2) ^ 2)‖ ≤ _
  rw [Complex.norm_exp, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : (((|τ| : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2) ^ 2).re =
      |τ| * (((q.1 : ℂ) - 1 / 2) ^ 2).re := Complex.re_ofReal_mul _ _
  rw [hre]
  have := re_sq_sub_half_le q
  have ht := abs_nonneg τ
  nlinarith

theorem gaussDressing_positiveOnLine (τ : ℝ) : (gaussDressing τ).PositiveOnLine := by
  intro q hq
  change 0 < (Complex.exp (|τ| * ((q.1 : ℂ) - 1 / 2) ^ 2)).re
  have e : (q.1 : ℂ) - 1 / 2 = ((q.1 : ℂ).im : ℂ) * I := by
    apply Complex.ext <;> simp [hq]
  rw [e, mul_pow, I_sq, show ((|τ| : ℝ) : ℂ) * (((q.1 : ℂ).im : ℂ) ^ 2 * -1) =
    ((-(|τ| * (q.1 : ℂ).im ^ 2) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp,
    Complex.ofReal_re]
  exact Real.exp_pos _

/-- `Φ_{g_τ}(0) → Φ(0)` as `τ → 0`. -/
theorem tendsto_dLagReal_gaussDressing_zero :
    Tendsto (fun τ : ℝ => dLagReal (gaussDressing τ) 0) (𝓝 0) (𝓝 poleSharpConstant) := by
  have hlim : Tendsto (fun τ : ℝ => ∑' q : XiZeroCopy, (gaussDressing τ).weight q) (𝓝 0)
      (𝓝 (∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun q =>
      Real.exp (1 / 4) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)
      (summable_inv_mul_one_sub.norm.mul_left _) (fun q => ?_) ?_
    · have hc : Continuous fun τ : ℝ => (gaussDressing τ).weight q := by
        unfold LagDressing.weight
        change Continuous fun τ : ℝ => Complex.exp (|τ| * ((q.1 : ℂ) - 1 / 2) ^ 2) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))
        fun_prop
      have := hc.tendsto 0
      convert this using 2
      change 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
        Complex.exp (|(0 : ℝ)| * ((q.1 : ℂ) - 1 / 2) ^ 2) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))
      simp
    · filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with τ hτ q
      rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hτ
      refine ((gaussDressing τ).norm_weight_le q).trans ?_
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
        (norm_nonneg _)
  have h1 := (Complex.continuous_re.tendsto _).comp hlim
  rw [tsum_inv_zero_mul_one_sub_zero, Complex.ofReal_re] at h1
  refine h1.congr fun τ => ?_
  simp only [Function.comp]
  unfold dLagReal
  rw [dLag_zero]

/-- For small `τ`, `Φ_{g_τ}(0) ≥ Φ(0)/2 > 0`. -/
theorem exists_gaussDressing_dLagReal_zero_ge :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, |τ| ≤ τ₀ → poleSharpConstant / 2 ≤ dLagReal (gaussDressing τ) 0 := by
  have hΦ := poleSharpConstant_pos
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp
    (tendsto_dLagReal_gaussDressing_zero.eventually (Ioi_mem_nhds (show poleSharpConstant / 2 <
      poleSharpConstant by linarith)))
  refine ⟨δ / 2, by positivity, fun τ hτ => ?_⟩
  have : dist τ 0 < δ := by rw [Real.dist_eq, sub_zero]; linarith
  exact (hball this).le

/-! ## The Gaussian producer at budget `exp((log y)^A)`, `A < 3/5` -/

theorem tendsto_rpow_sub_rpow_atTop {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Tendsto (fun v : ℝ => v ^ b - v ^ a) atTop atTop := by
  have h1 : Tendsto (fun v : ℝ => v ^ (b - a) - 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (tendsto_rpow_atTop (by linarith))
  refine tendsto_atTop_mono' _ ?_ h1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with v hv
  have hv0 : 0 < v := by linarith
  have e : v ^ b = v ^ (b - a) * v ^ a := by rw [← Real.rpow_add hv0]; ring_nf
  have h2 : 1 ≤ v ^ a := Real.one_le_rpow hv ha
  have h3 : 1 ≤ v ^ (b - a) := Real.one_le_rpow hv (by linarith)
  rw [e]
  nlinarith

/-- The asymptotic conditions of the Gaussian producer. -/
theorem eventually_gauss_budget_conditions {A θ β η₀ t₁ K₀ τ' H : ℝ} (hA0 : 0 ≤ A) (hAβ : A < β)
    (hθ : 0 < θ) (hβθ : A < 1 - β * θ) (hτ' : 0 < τ') (hη₀ : 0 < η₀) (ht₁ : 0 < t₁)
    (hK₀ : 0 < K₀) :
    ∀ᶠ v : ℝ in atTop, 1 ≤ v ∧ Real.log H ≤ v ^ β ∧ v ^ (-(β * θ)) ≤ η₀ ∧
      Real.exp (-(v ^ (1 - β * θ))) * Real.exp (v ^ A) ≤ t₁ ∧
      Real.exp (Real.exp (v ^ A)) * Real.exp (-(τ' * Real.exp (2 * v ^ β))) ≤ K₀ := by
  have hβ : 0 < β := by linarith
  have hβθ0 : 0 < β * θ := mul_pos hβ hθ
  refine (eventually_ge_atTop 1).and ((tendsto_rpow_atTop hβ).eventually_ge_atTop _ |>.and
    (((tendsto_rpow_neg_atTop hβθ0).eventually (ge_mem_nhds hη₀)).and ?_))
  refine Filter.Eventually.and ?_ ?_
  · have h := tendsto_rpow_sub_rpow_atTop hA0 hβθ
    have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h)
    filter_upwards [h2.eventually (ge_mem_nhds ht₁)] with v hv
    simp only [Function.comp] at hv
    rw [← Real.exp_add]
    refine le_trans (le_of_eq ?_) hv
    congr 1
    ring
  · have hX : Tendsto (fun v : ℝ => τ' * Real.exp (2 * v ^ β - v ^ A) - 1) atTop atTop := by
      refine tendsto_atTop_add_const_right _ _ (Tendsto.const_mul_atTop hτ' ?_)
      refine Real.tendsto_exp_atTop.comp (tendsto_atTop_mono' _ ?_ (tendsto_rpow_sub_rpow_atTop hA0 hAβ))
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with v hv
      have := Real.one_le_rpow hv hβ.le
      linarith
    have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hX)
    filter_upwards [h2.eventually (ge_mem_nhds hK₀), eventually_ge_atTop (1 : ℝ),
      hX.eventually_ge_atTop 0] with v hv hv1 hv2
    simp only [Function.comp] at hv
    refine le_trans ?_ hv
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hE1 : 1 ≤ Real.exp (v ^ A) := Real.one_le_exp (Real.rpow_nonneg (by linarith) _)
    have e : Real.exp (2 * v ^ β) = Real.exp (v ^ A) * Real.exp (2 * v ^ β - v ^ A) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    nlinarith

theorem norm_gaussDressing_g_le_of_lt (τ : ℝ) {T : ℝ} (hT : 0 ≤ T) (q : XiZeroCopy)
    (hq : T < |(q.1 : ℂ).im|) :
    ‖(gaussDressing τ).g (q.1 : ℂ)‖ ≤ Real.exp (|τ| / 4) * Real.exp (-(|τ| * T ^ 2)) := by
  refine (norm_gaussDressing_g_le τ q).trans (mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le)
  apply Real.exp_le_exp.mpr
  have h1 : T ^ 2 ≤ (q.1 : ℂ).im ^ 2 := by
    rw [← sq_abs ((q.1 : ℂ).im)]; exact pow_le_pow_left₀ hT hq.le 2
  have h2 := abs_nonneg τ
  have h3 := mul_le_mul_of_nonneg_left h1 h2
  linarith

theorem gaussDressing_tail_le {τ v A β K₀ : ℝ}
    (hK : Real.exp (Real.exp (v ^ A)) * Real.exp (-(|τ| * Real.exp (2 * v ^ β))) ≤ K₀)
    (hK₀def : K₀ = poleSharpConstant / (4 * (Real.exp (|τ| / 4) * lagWeightTotal))) :
    (Real.exp (Real.exp (v ^ A)) - 1) *
      (Real.exp (|τ| / 4) * Real.exp (-(|τ| * Real.exp (v ^ β) ^ 2)) * lagWeightTotal) ≤
        poleSharpConstant / 4 := by
  have hT2 : Real.exp (v ^ β) ^ 2 = Real.exp (2 * v ^ β) := by rw [sq, ← Real.exp_add]; ring_nf
  rw [hT2]
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (Real.exp (v ^ A)) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F = Real.exp (-(|τ| * Real.exp (2 * v ^ β))) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℝ, G = Real.exp (|τ| / 4) * lagWeightTotal := ⟨_, rfl⟩
  rw [← hE, ← hF] at hK ⊢
  have hG0 : 0 < G := by rw [hG]; exact mul_pos (Real.exp_pos _) lagWeightTotal_pos
  have hF0 : 0 ≤ F := by rw [hF]; exact (Real.exp_pos _).le
  have e1 : (E - 1) * (Real.exp (|τ| / 4) * F * lagWeightTotal) = G * ((E - 1) * F) := by
    rw [hG]; ring
  rw [e1]
  have h1 : G * ((E - 1) * F) ≤ G * K₀ := by
    refine mul_le_mul_of_nonneg_left ?_ hG0.le
    nlinarith
  have h2 : G * K₀ = poleSharpConstant / 4 := by
    rw [hK₀def, ← hG]; field_simp
  linarith

theorem width_of_vk {θ t₀ η₀ v β : ℝ} (hθ0 : 0 < θ) (ht₀ : 1 < t₀) (hv0 : 0 < v)
    (hvk : ∀ q : XiZeroCopy, t₀ ≤ |(q.1 : ℂ).im| →
      |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 - 1 * Real.log |(q.1 : ℂ).im| ^ (-θ))
    (hlow : ∀ q : XiZeroCopy, |(q.1 : ℂ).im| ≤ t₀ → |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 - η₀)
    (hω : v ^ (-(β * θ)) ≤ η₀) (q : XiZeroCopy) (hq : |(q.1 : ℂ).im| ≤ Real.exp (v ^ β)) :
    v ^ (-(β * θ)) ≤ 1 / 2 - |(q.1 : ℂ).re - 1 / 2| := by
  rcases le_or_gt t₀ |(q.1 : ℂ).im| with h0 | h0
  · have h1 := hvk q h0
    have hlog0 : 0 < Real.log |(q.1 : ℂ).im| := Real.log_pos (by linarith)
    have hlogT : Real.log |(q.1 : ℂ).im| ≤ v ^ β := by
      rw [← Real.log_exp (v ^ β)]; exact Real.log_le_log (by linarith) hq
    have h2 : (v ^ β) ^ (-θ) ≤ Real.log |(q.1 : ℂ).im| ^ (-θ) :=
      Real.rpow_le_rpow_of_nonpos hlog0 hlogT (by linarith)
    have h3 : (v ^ β) ^ (-θ) = v ^ (-(β * θ)) := by
      rw [← Real.rpow_mul hv0.le]; ring_nf
    rw [h3] at h2
    linarith
  · linarith [hlow q h0.le]

/-- **The Gaussian-dressed JAS producer.**  There is `τ₀ > 0` such that for every `0 < |τ| ≤ τ₀`
and every `0 ≤ A < 3/5`, for all large `y` the Gaussian-dressed tests are positive at every level
`σ` on every finite set of primes `p > y` with budget `Σ_P p^{−(σ−½)} ≤ exp((log y)^A)`. -/
theorem exists_gaussWeighted_positive_expLogBudget :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ τ : ℝ, 0 < |τ| → |τ| ≤ τ₀ → ∀ A : ℝ, 0 ≤ A → A < 3 / 5 →
      ∃ Y : ℝ, 1 < Y ∧ ∀ (σ y : ℝ), Y ≤ y → ∀ P : Finset Nat.Primes,
        (∀ p ∈ P, y < ((p : ℕ) : ℝ)) →
        ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤
          Real.exp (Real.log y ^ A) →
        ∀ z : Nat.Primes → ℂ, 0 ≤ (∑' q : XiZeroCopy,
          (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
            (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z p)) * (gaussDressing τ).weight q).re := by
  obtain ⟨τ₀, hτ₀, hΦ⟩ := exists_gaussDressing_dLagReal_zero_ge
  refine ⟨τ₀, hτ₀, fun τ hτ0 hτ A hA0 hA => ?_⟩
  have hΦ0 : poleSharpConstant / 2 ≤ dLagReal (gaussDressing τ) 0 := hΦ τ hτ
  have hpsc := poleSharpConstant_pos
  have hV := (gaussDressing τ).total_nonneg
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = 2 / 3 + (3 / 5 - A) := ⟨_, rfl⟩
  have hθ : 2 / 3 < θ := by rw [hθdef]; linarith
  have hθ0 : 0 < θ := by linarith
  have hAθ : A * θ < 1 - A := by rw [hθdef]; nlinarith
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = (A + (1 - A) / θ) / 2 := ⟨_, rfl⟩
  have hAlt : A < (1 - A) / θ := by rw [lt_div_iff₀ hθ0]; linarith
  have hAβ : A < β := by rw [hβdef]; linarith
  have hβθ : A < 1 - β * θ := by
    have : β * θ = (A * θ + (1 - A)) / 2 := by rw [hβdef]; field_simp
    rw [this]; linarith
  obtain ⟨t₀, ht₀, hvk⟩ := exists_powerLog_width_vk hθ
  obtain ⟨η₀, hη₀, hlow⟩ := exists_low_zero_width_at t₀
  obtain ⟨t₁, ht₁def⟩ : ∃ t : ℝ,
      t = Real.log (1 + poleSharpConstant / (4 * ((gaussDressing τ).total + 1))) := ⟨_, rfl⟩
  have hq0 : 0 < poleSharpConstant / (4 * ((gaussDressing τ).total + 1)) := by positivity
  have ht₁ : 0 < t₁ := by rw [ht₁def]; exact Real.log_pos (by linarith)
  have hexpt : (Real.exp t₁ - 1) * (gaussDressing τ).total ≤ dLagReal (gaussDressing τ) 0 / 2 := by
    rw [ht₁def, Real.exp_log (by linarith), add_sub_cancel_left]
    have h1 : poleSharpConstant / (4 * ((gaussDressing τ).total + 1)) * (gaussDressing τ).total ≤
        poleSharpConstant / 4 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    linarith
  obtain ⟨K₀, hK₀def⟩ : ∃ K : ℝ, K = poleSharpConstant /
      (4 * (Real.exp (|τ| / 4) * lagWeightTotal)) := ⟨_, rfl⟩
  have hK₀ : 0 < K₀ := by rw [hK₀def]; have := lagWeightTotal_pos; positivity
  obtain ⟨v₀, hv₀⟩ := eventually_atTop.mp (eventually_gauss_budget_conditions (H := t₀) hA0 hAβ
    hθ0 hβθ hτ0 hη₀ ht₁ hK₀)
  refine ⟨Real.exp (max v₀ 1), by linarith [Real.add_one_le_exp (max v₀ 1), le_max_right v₀ 1],
    fun σ y hy P hP hB z => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos _) hy
  have hvge : max v₀ 1 ≤ Real.log y := by
    rw [← Real.log_exp (max v₀ 1)]; exact Real.log_le_log (Real.exp_pos _) hy
  obtain ⟨hv1, hTt, hω, hC3, hC4⟩ := hv₀ (Real.log y) (le_trans (le_max_left _ _) hvge)
  have hv0 : 0 < Real.log y := by linarith
  have hTt0 : t₀ ≤ Real.exp (Real.log y ^ β) := by
    rw [← Real.exp_log (show (0 : ℝ) < t₀ by linarith)]; exact Real.exp_le_exp.mpr hTt
  have hωv : Real.log y ^ (-(β * θ)) * Real.log y = Real.log y ^ (1 - β * θ) := by
    rw [← Real.rpow_add_one hv0.ne']; ring_nf
  have hlow' : Real.exp (-(Real.log y ^ (-(β * θ)) * Real.log y)) * Real.exp (Real.log y ^ A) ≤ t₁ := by
    rw [hωv]; exact hC3
  have htail := gaussDressing_tail_le hC4 hK₀def
  exact weightedAggregate_re_nonneg_of_heightSplit (gaussDressing τ) hy0 (by positivity) P hP hB
    (width_of_vk hθ0 ht₀ hv0 hvk (fun q hq => hlow q hq) hω)
    (fun q hq => norm_gaussDressing_g_le_of_lt τ (Real.exp_pos _).le q hq) (by positivity)
    ht₁.le hexpt hlow' (by linarith) z

end

end RHTower
