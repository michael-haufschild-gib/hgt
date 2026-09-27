import GaloisForLFunctions.RHTower.RelaxedHodgeDictionary
import GaloisForLFunctions.RHTower.XiWardCriticalBudgetProbe

/-!
# The relaxed dictionary: error exponent `θ` confines the zeros to `|β - ½| ≤ θ/2 + ε`

Let `Z` have local count `N(t, t+1] ≤ A₀ log(|t| + 3)` and no zeros below ordinate `2`.  Suppose
the relaxed Hodge index with exponent `θ ≥ 0` holds at level `a`:
`Re W(f, f) ≥ -e^{θa} ∫|f|²` for every polar-constrained `C²` test supported in `[-a, a]`.  Then
(`relaxed_hodge_dictionary`), for every `ε > 0` and `a ≥ max(e¹², 1/ε)`, every zero with

> `10⁴ A₀ (log(|γ| + 306) + log a + 2/ε + 2) log² a ≤ εa`

satisfies `|β - ½| ≤ θ/2 + ε`.  Once `a ≥ a₀(ε, A₀)`, this covers every zero up to height
`exp(εa/(2·10⁴ A₀ log² a))` (`relaxed_hodge_dictionary_height`).  For `ζ`, the low-height
hypothesis comes from the zero-free box `|γ| ≤ √32` (`zeta_relaxed_hodge_dictionary`).

The exponent of the prime-side error at level `a` thus bounds twice the abscissa excess of the
zeros at heights up to `exp(a^{1-o(1)})`.  The trivial bound `θ = 1` (the prime-transport norm)
corresponds to the trivial region `β < 1`.  Any `θ < 1` would be a quasi-Riemann hypothesis
`β ≤ (1 + θ)/2 + ε` at these heights.

**Proof.**
* The centre is a zero `ρs` maximizing `Re ρ - λ|Im ρ - γ₀|` (`exists_penalized_deepest_zero`),
  with `λ = 1/(8b e^{2/ε})`.
* The parameters are `M = ⌈εa/2⌉` unit weights for the killing factor, the edge weight on
  `[-b, b]` with `b = a - M`, and the far radius `R = e^{2/ε} - 1`, so that `(1 + R)^M ≥ e^a`
  (`relaxed_params`).
* The edge test gains `e^{2δb}`, with `2δb ≥ θa + (3/2)εa - O(1)`.  The root ratio costs
  `e^{16 n log² a + O(log a)}` (`relaxed_condition_A`), and the tail costs `e^{-M + O(n log² a)}`
  (`relaxed_condition_B`).
* `relaxed_dictionary_linear` turns the size condition into the needed linear inequalities.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

noncomputable section
namespace RHTower

open Zeta23

/-! ### Asymptotic bounds -/

theorem exp_numeric_bounds' : (244 * 10 ^ 5 : ℝ) ≤ Real.exp 18 ∧ (512 : ℝ) ≤ Real.exp 7 ∧
    (990 : ℝ) ≤ Real.exp 7 ∧ (46656 : ℝ) ≤ Real.exp 11 ∧ (256 : ℝ) ≤ Real.exp 6 ∧
    (24 : ℝ) ≤ Real.exp 4 := by
  have he := Real.exp_one_gt_d9
  have e : ∀ k : ℕ, Real.exp k = Real.exp 1 ^ k := fun k => by rw [← Real.exp_nat_mul, mul_one]
  have lo : ∀ k : ℕ, (2.7182818283 : ℝ) ^ k ≤ Real.exp k := fun k => by
    rw [e k]; exact pow_le_pow_left₀ (by norm_num) he.le k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := lo 18; norm_num at this ⊢; linarith
  · have := lo 7; norm_num at this ⊢; linarith
  · have := lo 7; norm_num at this ⊢; linarith
  · have := lo 11; norm_num at this ⊢; linarith
  · have := lo 6; norm_num at this ⊢; linarith
  · have := lo 4; norm_num at this ⊢; linarith

/-- `122/η ≤ exp(4 log² a)` for the killing distance of the relaxed construction. -/
theorem relaxedKillScale_ge {δ ε a b : ℝ} {M n : ℕ} (hε : 0 < ε) (hεδ : ε ≤ δ) (hδ2 : δ ≤ 1 / 2)
    (ha12 : Real.exp 12 ≤ a) (haε : 1 / ε ≤ a) (hb1 : 1 ≤ b) (hba : b ≤ a) (hM : (M : ℝ) ≤ a)
    (hn : (n : ℝ) + 1 ≤ a) :
    122 / relaxedKillScale δ b M n ≤ Real.exp (4 * Real.log a ^ 2) := by
  obtain ⟨e18, -, -, -, -, -⟩ := exp_numeric_bounds'
  obtain ⟨-, -, e6, -, -, -⟩ := exp_numeric_bounds
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 12) ha12
  set ℓ := Real.log a with hℓ
  have hℓ12 : 12 ≤ ℓ := by
    have := Real.log_le_log (Real.exp_pos 12) ha12; rwa [Real.log_exp] at this
  have hae : Real.exp ℓ = a := Real.exp_log ha0
  have ha1 : 1 ≤ a := by nlinarith [Real.add_one_le_exp 12]
  have hδ0 : 0 < δ := lt_of_lt_of_le hε hεδ
  have hb0 : 0 < b := by linarith
  -- the halving radius is at least `1/(10⁵ a⁵)`
  set r₀ := min (lowHeightEps0 δ M) (1 / (10 ^ 5 * b ^ 5)) with hr₀
  have hεa : 1 ≤ ε * a := by rw [div_le_iff₀ hε] at haε; linarith
  have ha5 : a ^ 2 ≤ a ^ 5 := pow_le_pow_right₀ ha1 (by norm_num)
  have hr₀lo : 1 / (10 ^ 5 * a ^ 5) ≤ r₀ := by
    rw [hr₀, le_min_iff]
    constructor
    · unfold lowHeightEps0
      rw [min_eq_left (by linarith)]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have ha3 : (3 : ℝ) ≤ a := by have := Real.add_one_le_exp 12; linarith
      have hMa : 100 * (3 * (M : ℝ) + 3) ≤ 400 * a := by linarith
      nlinarith [pow_pos ha0 5]
    · apply one_div_le_one_div_of_le (by positivity)
      have := pow_le_pow_left₀ hb0.le hba 5
      nlinarith
  have hr₀pos : 0 < r₀ := lt_of_lt_of_le (by positivity) hr₀lo
  set m := Nat.log 2 n with hm
  have hm2 : (m : ℝ) ≤ 2 * ℓ := natLog_two_le_two_log ha1 (by linarith)
  have hbase : 4 * (100 * ((n : ℝ) + 1)) ≤ Real.exp (6 + ℓ) := by
    rw [Real.exp_add, hae]; nlinarith
  have hpow : (4 * (100 * ((n : ℝ) + 1))) ^ (m + 1) ≤ Real.exp (((m + 1 : ℕ) : ℝ) * (6 + ℓ)) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (by positivity) hbase _
  have hinvr : 1 / r₀ ≤ 10 ^ 5 * Real.exp (5 * ℓ) := by
    rw [div_le_iff₀ hr₀pos]
    have h5 : Real.exp (5 * ℓ) = a ^ 5 := by
      rw [show (5 : ℝ) * ℓ = ((5 : ℕ) : ℝ) * ℓ by norm_num, Real.exp_nat_mul, hae]
    rw [h5]
    have := hr₀lo
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  unfold relaxedKillScale
  rw [← hr₀, ← hm]
  unfold lowHeightScale
  rw [div_div_eq_mul_div, div_le_iff₀ hr₀pos]
  have hexp : 18 + 5 * ℓ + (((m + 1 : ℕ) : ℝ) * (6 + ℓ)) ≤ 4 * ℓ ^ 2 := by
    push_cast; nlinarith
  calc 122 * (2 * (4 * (100 * ((n : ℝ) + 1))) ^ (m + 1))
      = 244 * (4 * (100 * ((n : ℝ) + 1))) ^ (m + 1) := by ring
    _ ≤ 244 * Real.exp (((m + 1 : ℕ) : ℝ) * (6 + ℓ)) := by gcongr
    _ = 244 * 10 ^ 5 * (1 / (10 ^ 5)) * Real.exp (((m + 1 : ℕ) : ℝ) * (6 + ℓ)) := by ring
    _ ≤ Real.exp 18 * (1 / (10 ^ 5)) * Real.exp (((m + 1 : ℕ) : ℝ) * (6 + ℓ)) := by gcongr
    _ ≤ Real.exp 18 * (r₀ * Real.exp (5 * ℓ)) * Real.exp (((m + 1 : ℕ) : ℝ) * (6 + ℓ)) := by
        gcongr
        rw [div_le_iff₀ hr₀pos] at hinvr
        have : 1 / (10 ^ 5 : ℝ) ≤ r₀ * Real.exp (5 * ℓ) := by
          rw [div_le_iff₀ (by norm_num)]; linarith
        exact this
    _ = Real.exp (18 + 5 * ℓ + (((m + 1 : ℕ) : ℝ) * (6 + ℓ))) * r₀ := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ Real.exp (4 * ℓ ^ 2) * r₀ := by gcongr


theorem relaxedRootRatio_le_exp {δ ε a b : ℝ} {M n : ℕ} (hε : 0 < ε) (hεδ : ε ≤ δ)
    (ha0 : 0 < a) (haε : 1 / ε ≤ a) (hb0 : 0 < b)
    (hkill : 122 / relaxedKillScale δ b M n ≤ Real.exp (4 * Real.log a ^ 2)) :
    relaxedRootRatio δ b M n ≤
      Real.exp (((2 * n : ℕ) : ℝ) * (4 * Real.log a ^ 2) + 2 * (7 + Real.log a)) := by
  obtain ⟨-, -, e990, -, -, -⟩ := exp_numeric_bounds'
  have hδ0 : 0 < δ := lt_of_lt_of_le hε hεδ
  have hae : Real.exp (Real.log a) = a := Real.exp_log ha0
  have h990 : 990 / δ ≤ Real.exp (7 + Real.log a) := by
    rw [Real.exp_add, hae, div_le_iff₀ hδ0]
    have h1 : 1 ≤ ε * a := by rw [div_le_iff₀ hε] at haε; linarith
    have h2 : 1 ≤ a * δ := by nlinarith
    calc (990 : ℝ) ≤ Real.exp 7 := e990
      _ = Real.exp 7 * 1 := by ring
      _ ≤ Real.exp 7 * (a * δ) := by gcongr
      _ = Real.exp 7 * a * δ := by ring
  have hk0 : 0 ≤ 122 / relaxedKillScale δ b M n := by
    have := relaxedKillScale_pos hδ0 hb0 M n; positivity
  unfold relaxedRootRatio
  rw [Real.exp_add, Real.exp_nat_mul,
    show 2 * (7 + Real.log a) = ((2 : ℕ) : ℝ) * (7 + Real.log a) by norm_num, Real.exp_nat_mul]
  exact mul_le_mul (pow_le_pow_left₀ hk0 hkill _) (pow_le_pow_left₀ (by positivity) h990 _)
    (by positivity) (by positivity)

/-- The gain condition `hA` from a linear condition. -/
theorem relaxed_condition_A {θ ε a δ : ℝ} {M n : ℕ} (hθ : 0 ≤ θ) (hε : 0 < ε)
    (hδ : θ / 2 + ε ≤ δ) (hδ2 : δ ≤ 1 / 2) (ha12 : Real.exp 12 ≤ a) (haε : 1 / ε ≤ a)
    (hMhi : (M : ℝ) ≤ ε * a / 2 + 1) (hb4 : 4 ≤ a - M)
    (hkill : 122 / relaxedKillScale δ (a - M) M n ≤ Real.exp (4 * Real.log a ^ 2))
    (hlin : 16 * n * Real.log a ^ 2 + 11 * Real.log a + 43 ≤ ε * a) :
    512 * a * (a - M) ^ 6 * Real.exp 4 * relaxedRootRatio δ (a - M) M n ^ 2 *
        Real.exp (θ * a) ≤ Real.exp (2 * (δ - 1 / (8 * (a - M))) * (a - M)) := by
  obtain ⟨-, e512, -, -, -, -⟩ := exp_numeric_bounds'
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 12) ha12
  set ℓ := Real.log a with hℓ
  have hae : Real.exp ℓ = a := Real.exp_log ha0
  set b := a - M with hb
  have hb0 : 0 < b := by linarith
  have hba : b ≤ a := by rw [hb]; linarith [Nat.cast_nonneg (α := ℝ) M]
  have hεδ : ε ≤ δ := by linarith
  have hRR := relaxedRootRatio_le_exp hε hεδ ha0 haε hb0 hkill
  have hRR0 : 0 ≤ relaxedRootRatio δ b M n := by
    unfold relaxedRootRatio
    have := relaxedKillScale_pos (lt_of_lt_of_le hε hεδ) hb0 M n
    have := lt_of_lt_of_le hε hεδ
    positivity
  have hb6 : b ^ 6 ≤ Real.exp (6 * ℓ) := by
    rw [show (6 : ℝ) * ℓ = ((6 : ℕ) : ℝ) * ℓ by norm_num, Real.exp_nat_mul, hae]
    exact pow_le_pow_left₀ hb0.le hba 6
  have hLHS : 512 * a * b ^ 6 * Real.exp 4 * relaxedRootRatio δ b M n ^ 2 * Real.exp (θ * a) ≤
      Real.exp (7 + ℓ + 6 * ℓ + 4 +
        2 * (((2 * n : ℕ) : ℝ) * (4 * ℓ ^ 2) + 2 * (7 + ℓ)) + θ * a) := by
    have hRR2 : relaxedRootRatio δ b M n ^ 2 ≤
        Real.exp (2 * (((2 * n : ℕ) : ℝ) * (4 * ℓ ^ 2) + 2 * (7 + ℓ))) := by
      rw [show 2 * (((2 * n : ℕ) : ℝ) * (4 * ℓ ^ 2) + 2 * (7 + ℓ)) =
          ((2 : ℕ) : ℝ) * (((2 * n : ℕ) : ℝ) * (4 * ℓ ^ 2) + 2 * (7 + ℓ)) by norm_num,
        Real.exp_nat_mul]
      exact pow_le_pow_left₀ hRR0 hRR 2
    calc 512 * a * b ^ 6 * Real.exp 4 * relaxedRootRatio δ b M n ^ 2 * Real.exp (θ * a)
        ≤ Real.exp 7 * Real.exp ℓ * Real.exp (6 * ℓ) * Real.exp 4 *
            Real.exp (2 * (((2 * n : ℕ) : ℝ) * (4 * ℓ ^ 2) + 2 * (7 + ℓ))) * Real.exp (θ * a) := by
          rw [hae]; gcongr
      _ = _ := by simp only [← Real.exp_add]
  refine hLHS.trans (Real.exp_le_exp.mpr ?_)
  have e8 : 2 * (δ - 1 / (8 * b)) * b = 2 * δ * b - 1 / 4 := by field_simp; ring
  rw [e8]
  have hθδ : θ + 2 * ε ≤ 1 := by linarith
  have h2δb : (θ + 2 * ε) * b ≤ 2 * δ * b := by nlinarith
  have hexp : (θ + 2 * ε) * b = θ * a + 2 * ε * a - (θ + 2 * ε) * M := by rw [hb]; ring
  have hM1 : (θ + 2 * ε) * M ≤ M := by
    have := Nat.cast_nonneg (α := ℝ) M; nlinarith
  push_cast
  nlinarith


theorem exp_half_le_165 : Real.exp (1 / 2) ≤ 165 / 100 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]

/-- `e (e^{1/2}·168)² ≤ 101³ w₁²`: the growth factor of the tail comparison. -/
theorem tail_growth_numeric :
    Real.exp 1 * (Real.exp (1 / 2) * 168) ^ 2 ≤ 101 ^ 3 * unitWeightFloor ^ 2 := by
  have h1 := Real.exp_one_lt_d9
  have h2 := exp_half_le_165
  have hU := unitWeightFloor_ge
  have hB : (Real.exp (1 / 2) * 168) ^ 2 ≤ (165 / 100 * 168) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by nlinarith) 2
  have hU2 : (48 / 100 : ℝ) ^ 2 ≤ unitWeightFloor ^ 2 := pow_le_pow_left₀ (by norm_num) hU 2
  nlinarith [Real.exp_pos 1]

/-- The upper side of the tail comparison. -/
theorem relaxed_tail_upper {a b A₀ Γ B : ℝ} {M n : ℕ} (ha0 : 0 < a) (hb0 : 0 < b) (hba : b ≤ a)
    (hA₀ : 1 ≤ A₀) (hΓ : 0 ≤ Γ) (hB0 : 0 ≤ B) :
    Real.exp (9 / 2) * 46656 * 256 * b ^ 8 * (B ^ (2 * M) * 101 ^ (4 * n + 4) * (Γ + 2) ^ 4 *
        (24 * A₀ * Real.log (Γ + 4))) * 101 ^ (4 * n + 11) ≤
      B ^ (2 * M) * Real.exp (101 + 8 * Real.log a + 40 * n + 5 * Real.log (A₀ * (Γ + 4))) := by
  obtain ⟨e5, e4, -, -, -, -⟩ := exp_numeric_bounds
  obtain ⟨-, -, -, e11, e6, -⟩ := exp_numeric_bounds'
  set ℓ := Real.log a with hℓ
  have hae : Real.exp ℓ = a := Real.exp_log ha0
  have hA0 : 0 < A₀ := by linarith
  have hG4 : 0 < Γ + 4 := by linarith
  have hlA : 0 ≤ Real.log A₀ := Real.log_nonneg hA₀
  have hlog0 : 0 ≤ Real.log (Γ + 4) := Real.log_nonneg (by linarith)
  have hb8 : b ^ 8 ≤ Real.exp (8 * ℓ) := by
    rw [show (8 : ℝ) * ℓ = ((8 : ℕ) : ℝ) * ℓ by norm_num, Real.exp_nat_mul, hae]
    exact pow_le_pow_left₀ hb0.le hba 8
  have h101 : (101 : ℝ) ^ (4 * n + 4) * 101 ^ (4 * n + 11) ≤
      Real.exp (((8 * n + 15 : ℕ) : ℝ) * 5) := by
    rw [← pow_add, Real.exp_nat_mul, show 4 * n + 4 + (4 * n + 11) = 8 * n + 15 by ring]
    exact pow_le_pow_left₀ (by norm_num) e5 _
  have hG : (Γ + 2) ^ 4 ≤ Real.exp (((4 : ℕ) : ℝ) * Real.log (Γ + 4)) := by
    rw [Real.exp_nat_mul, Real.exp_log hG4]
    exact pow_le_pow_left₀ (by linarith) (by linarith) 4
  have hlogle : Real.log (Γ + 4) ≤ Real.exp (Real.log (Γ + 4)) := by
    rw [Real.exp_log hG4]; exact Real.log_le_self hG4.le
  have hA₀e : A₀ = Real.exp (Real.log A₀) := (Real.exp_log hA0).symm
  have hB2 : 0 ≤ B ^ (2 * M) := by positivity
  have hmid : Real.exp (9 / 2) * 46656 * 256 * b ^ 8 * ((101 : ℝ) ^ (4 * n + 4) *
      101 ^ (4 * n + 11)) * (Γ + 2) ^ 4 * (24 * A₀ * Real.log (Γ + 4)) ≤
      Real.exp (9 / 2) * Real.exp 11 * Real.exp 6 * Real.exp (8 * ℓ) *
        Real.exp (((8 * n + 15 : ℕ) : ℝ) * 5) * Real.exp (((4 : ℕ) : ℝ) * Real.log (Γ + 4)) *
        (Real.exp 4 * Real.exp (Real.log A₀) * Real.exp (Real.log (Γ + 4))) := by
    rw [← hA₀e]
    gcongr
  have hexpeq : Real.exp (9 / 2) * Real.exp 11 * Real.exp 6 * Real.exp (8 * ℓ) *
        Real.exp (((8 * n + 15 : ℕ) : ℝ) * 5) * Real.exp (((4 : ℕ) : ℝ) * Real.log (Γ + 4)) *
        (Real.exp 4 * Real.exp (Real.log A₀) * Real.exp (Real.log (Γ + 4))) =
      Real.exp (9 / 2 + 11 + 6 + 8 * ℓ + ((8 * n + 15 : ℕ) : ℝ) * 5 +
        ((4 : ℕ) : ℝ) * Real.log (Γ + 4) + (4 + Real.log A₀ + Real.log (Γ + 4))) := by
    simp only [Real.exp_add]
  have hΛ : Real.log (A₀ * (Γ + 4)) = Real.log A₀ + Real.log (Γ + 4) :=
    Real.log_mul hA0.ne' hG4.ne'
  have hle : 9 / 2 + 11 + 6 + 8 * ℓ + ((8 * n + 15 : ℕ) : ℝ) * 5 +
      ((4 : ℕ) : ℝ) * Real.log (Γ + 4) + (4 + Real.log A₀ + Real.log (Γ + 4)) ≤
      101 + 8 * ℓ + 40 * n + 5 * Real.log (A₀ * (Γ + 4)) := by
    rw [hΛ]; push_cast; nlinarith
  calc Real.exp (9 / 2) * 46656 * 256 * b ^ 8 * (B ^ (2 * M) * 101 ^ (4 * n + 4) * (Γ + 2) ^ 4 *
        (24 * A₀ * Real.log (Γ + 4))) * 101 ^ (4 * n + 11)
      = B ^ (2 * M) * (Real.exp (9 / 2) * 46656 * 256 * b ^ 8 * ((101 : ℝ) ^ (4 * n + 4) *
          101 ^ (4 * n + 11)) * (Γ + 2) ^ 4 * (24 * A₀ * Real.log (Γ + 4))) := by ring
    _ ≤ B ^ (2 * M) * Real.exp (9 / 2 + 11 + 6 + 8 * ℓ + ((8 * n + 15 : ℕ) : ℝ) * 5 +
          ((4 : ℕ) : ℝ) * Real.log (Γ + 4) + (4 + Real.log A₀ + Real.log (Γ + 4))) := by
        rw [← hexpeq]; exact mul_le_mul_of_nonneg_left hmid hB2
    _ ≤ _ := by gcongr

/-- The lower side of the tail comparison. -/
theorem relaxed_tail_lower {ℓ δ η U B : ℝ} {M n : ℕ} (hM4 : 4 * n + 11 ≤ 3 * M)
    (hgrow : Real.exp 1 * B ^ 2 ≤ 101 ^ 3 * U ^ 2) (hU0 : 0 ≤ U)
    (hη : Real.exp (-(4 * ℓ ^ 2)) ≤ η) (hδ : Real.exp (-(4 * ℓ) - 3) ≤ (δ / 2) ^ 4) :
    B ^ (2 * M) * Real.exp (M - 16 * n * ℓ ^ 2 - 4 * ℓ - 3) ≤
      (101 : ℝ) ^ (3 * M - 4 * n - 11) * (U ^ (2 * M) * η ^ (4 * n) * (δ / 2) ^ 4) *
        101 ^ (4 * n + 11) := by
  have hsplit : (101 : ℝ) ^ (3 * M - 4 * n - 11) * 101 ^ (4 * n + 11) = 101 ^ (3 * M) := by
    rw [← pow_add]; congr 1; omega
  have hexpM : Real.exp (M : ℝ) = Real.exp 1 ^ M := by rw [← Real.exp_nat_mul, mul_one]
  have hg : Real.exp M * B ^ (2 * M) ≤ (101 : ℝ) ^ (3 * M) * U ^ (2 * M) := by
    have e1 : Real.exp M * B ^ (2 * M) = (Real.exp 1 * B ^ 2) ^ M := by
      rw [hexpM, mul_pow, ← pow_mul]
    have e2 : (101 : ℝ) ^ (3 * M) * U ^ (2 * M) = ((101 : ℝ) ^ 3 * U ^ 2) ^ M := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
    rw [e1, e2]
    exact pow_le_pow_left₀ (by positivity) hgrow M
  have hη0 : 0 ≤ η := le_trans (Real.exp_pos _).le hη
  have hη4 : Real.exp (((4 * n : ℕ) : ℝ) * (-(4 * ℓ ^ 2))) ≤ η ^ (4 * n) := by
    rw [Real.exp_nat_mul]; exact pow_le_pow_left₀ (Real.exp_pos _).le hη _
  have e : Real.exp (M - 16 * n * ℓ ^ 2 - 4 * ℓ - 3) =
      Real.exp M * Real.exp (((4 * n : ℕ) : ℝ) * (-(4 * ℓ ^ 2))) * Real.exp (-(4 * ℓ) - 3) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  rw [e]
  calc B ^ (2 * M) * (Real.exp M * Real.exp (((4 * n : ℕ) : ℝ) * (-(4 * ℓ ^ 2))) *
        Real.exp (-(4 * ℓ) - 3))
      = (Real.exp M * B ^ (2 * M)) * Real.exp (((4 * n : ℕ) : ℝ) * (-(4 * ℓ ^ 2))) *
          Real.exp (-(4 * ℓ) - 3) := by ring
    _ ≤ ((101 : ℝ) ^ (3 * M) * U ^ (2 * M)) * η ^ (4 * n) * (δ / 2) ^ 4 := by
        gcongr
    _ = _ := by rw [← hsplit]; ring

/-- The tail condition `hB` from a linear condition. -/
theorem relaxed_condition_B {ε a δ A₀ Γ : ℝ} {M n : ℕ} (hε : 0 < ε) (hεδ : ε ≤ δ)
    (ha12 : Real.exp 12 ≤ a) (haε : 1 / ε ≤ a) (hA₀ : 1 ≤ A₀) (hΓ : 0 ≤ Γ)
    (hMlo : ε * a / 2 ≤ M) (hb1 : 1 ≤ a - M) (hM4 : 4 * n + 11 ≤ 3 * M)
    (hkill : 122 / relaxedKillScale δ (a - M) M n ≤ Real.exp (4 * Real.log a ^ 2))
    (hlinB : 16 * n * Real.log a ^ 2 + 40 * n + 12 * Real.log a +
      5 * Real.log (A₀ * (Γ + 4)) + 105 ≤ ε * a / 2) :
    Real.exp (9 / 2) * 46656 * 256 * (a - M) ^ 8 * ((Real.exp (1 / 2) * 168) ^ (2 * M) *
        101 ^ (4 * n + 4) * (Γ + 2) ^ 4 * (24 * A₀ * Real.log (Γ + 4))) <
      (101 : ℝ) ^ (3 * M - 4 * n - 11) * (unitWeightFloor ^ (2 * M) *
        relaxedKillScale δ (a - M) M n ^ (4 * n) * (δ / 2) ^ 4) := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 12) ha12
  set ℓ := Real.log a with hℓ
  have hae : Real.exp ℓ = a := Real.exp_log ha0
  have hb0 : 0 < a - M := by linarith
  have hδ0 : 0 < δ := lt_of_lt_of_le hε hεδ
  have hη0 := relaxedKillScale_pos hδ0 hb0 M n
  have hηlow : Real.exp (-(4 * ℓ ^ 2)) ≤ relaxedKillScale δ (a - M) M n := by
    rw [div_le_iff₀ hη0] at hkill
    rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
    nlinarith [Real.exp_pos (4 * ℓ ^ 2)]
  have hδlow : Real.exp (-(4 * ℓ) - 3) ≤ (δ / 2) ^ 4 := by
    have h1 : Real.exp (-ℓ) ≤ δ := by
      rw [Real.exp_neg, hae]
      rw [div_le_iff₀ hε] at haε
      rw [inv_le_iff_one_le_mul₀ ha0]; nlinarith
    have h16 : (16 : ℝ) ≤ Real.exp 3 := by
      have h2 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have := Real.exp_one_gt_d9
      rw [h2]; nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7182818283) this.le 3]
    have h3 : Real.exp (-(4 * ℓ) - 3) = Real.exp (-ℓ) ^ 4 / Real.exp 3 := by
      rw [← Real.exp_nat_mul, ← Real.exp_sub]; congr 1; push_cast; ring
    rw [h3, div_le_iff₀ (Real.exp_pos 3)]
    have h4 : Real.exp (-ℓ) ^ 4 ≤ δ ^ 4 := pow_le_pow_left₀ (Real.exp_pos _).le h1 4
    nlinarith [pow_pos hδ0 4]
  have hup := relaxed_tail_upper (M := M) (n := n) ha0 hb0 (by linarith) hA₀ hΓ
    (by positivity : (0 : ℝ) ≤ Real.exp (1 / 2) * 168)
  have hlow := relaxed_tail_lower hM4 tail_growth_numeric unitWeightFloor_pos.le hηlow hδlow
  have hexp : 101 + 8 * ℓ + 40 * n + 5 * Real.log (A₀ * (Γ + 4)) <
      M - 16 * n * ℓ ^ 2 - 4 * ℓ - 3 := by linarith
  have hpos : (0 : ℝ) < 101 ^ (4 * n + 11) := by positivity
  refine lt_of_mul_lt_mul_right ?_ hpos.le
  calc _ ≤ _ := hup
    _ < (Real.exp (1 / 2) * 168) ^ (2 * M) * Real.exp (M - 16 * n * ℓ ^ 2 - 4 * ℓ - 3) := by
        have : 0 < (Real.exp (1 / 2) * 168) ^ (2 * M) := by positivity
        exact mul_lt_mul_of_pos_left (Real.exp_lt_exp.mpr hexp) this
    _ ≤ _ := hlow


/-! ### The dictionary -/

/-- The linear bookkeeping of the dictionary from the size condition
`10⁴ A₀ log(Γ + 306) log² a ≤ εa`. -/
theorem relaxed_dictionary_linear {A₀ ε a Γ : ℝ} {n : ℕ} (hA₀ : 1 ≤ A₀) (hΓ : 0 ≤ Γ)
    (ha12 : Real.exp 12 ≤ a) (hn : (n : ℝ) ≤ 202 * A₀ * Real.log (Γ + 306))
    (hsize : 10 ^ 4 * A₀ * Real.log (Γ + 306) * Real.log a ^ 2 ≤ ε * a) :
    16 * n * Real.log a ^ 2 + 11 * Real.log a + 43 ≤ ε * a ∧
      16 * n * Real.log a ^ 2 + 40 * n + 12 * Real.log a + 5 * Real.log (A₀ * (Γ + 4)) + 105 ≤
        ε * a / 2 ∧
      (2 * n + 7 : ℝ) ≤ ε * a / 2 ∧ 4 ≤ ε * a := by
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 12) ha12
  set ℓ := Real.log a with hℓ
  have hℓ12 : 12 ≤ ℓ := by
    have := Real.log_le_log (Real.exp_pos 12) ha12; rwa [Real.log_exp] at this
  set L := Real.log (Γ + 306) with hL
  have hL5 : 5 ≤ L := by
    rw [hL, ← Real.log_exp 5]
    apply Real.log_le_log (Real.exp_pos 5)
    obtain ⟨e5, -⟩ := exp_numeric_bounds
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
    have : Real.exp 1 ^ 5 ≤ (2.7182818286 : ℝ) ^ 5 := pow_le_pow_left₀ (Real.exp_pos 1).le h1.le 5
    rw [h2]; norm_num at this; linarith
  have hA0 : 0 < A₀ := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hℓ2 : 144 ≤ ℓ ^ 2 := by nlinarith
  set S := A₀ * L * ℓ ^ 2 with hS
  have hS1 : 144 * 5 ≤ S := by
    rw [hS]
    have : 5 ≤ A₀ * L := by nlinarith
    nlinarith
  have hSε : 10 ^ 4 * S ≤ ε * a := by rw [hS]; linarith [hsize]
  have hnS : (n : ℝ) * ℓ ^ 2 ≤ 202 * S := by
    calc (n : ℝ) * ℓ ^ 2 ≤ (202 * A₀ * L) * ℓ ^ 2 := mul_le_mul_of_nonneg_right hn (sq_nonneg _)
      _ = 202 * S := by rw [hS]; ring
  have hnS' : (n : ℝ) ≤ 202 * S / 144 := by
    rw [le_div_iff₀ (by norm_num)]
    have : (n : ℝ) * 144 ≤ (n : ℝ) * ℓ ^ 2 := mul_le_mul_of_nonneg_left hℓ2 hn0
    linarith
  have hAL : 1 ≤ A₀ * L := by nlinarith
  have hℓS : ℓ ≤ S := by
    have h1 : ℓ ≤ ℓ ^ 2 := by nlinarith
    have h2 : ℓ ^ 2 ≤ A₀ * L * ℓ ^ 2 := le_mul_of_one_le_left (sq_nonneg _) hAL
    rw [hS]; linarith
  have hG4 : 0 < Γ + 4 := by linarith
  have hΛ : Real.log (A₀ * (Γ + 4)) ≤ 2 * S := by
    rw [Real.log_mul hA0.ne' hG4.ne']
    have h1 : Real.log A₀ ≤ A₀ := (Real.log_le_sub_one_of_pos hA0).trans (by linarith)
    have h2 : Real.log (Γ + 4) ≤ L := Real.log_le_log hG4 (by linarith)
    have h3 : A₀ + L ≤ 2 * S := by
      have h4 : A₀ ≤ A₀ * L := le_mul_of_one_le_right hA0.le (by linarith)
      have h5 : L ≤ A₀ * L := le_mul_of_one_le_left (by linarith) hA₀
      have h6 : A₀ * L ≤ S := by rw [hS]; exact le_mul_of_one_le_right (by positivity) (by linarith)
      linarith
    linarith
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem log_height_shift_le {x y a ε : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : x ≤ y + 4 * a * Real.exp (2 / ε)) (ha : 1 ≤ a) (hε : 0 < ε) :
    Real.log (x + 306) ≤ Real.log (y + 306) + Real.log a + 2 / ε + 2 := by
  have ha0 : 0 < a := by linarith
  have hpos : 0 < y + 306 := by positivity
  have he : 1 ≤ Real.exp (2 / ε) := Real.one_le_exp (by positivity)
  have h1 : x + 306 ≤ (y + 306) * (5 * a * Real.exp (2 / ε)) := by
    have h2 : 4 * a * Real.exp (2 / ε) ≤ (y + 306) * (4 * a * Real.exp (2 / ε)) :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    have h3 : y + 306 ≤ (y + 306) * (a * Real.exp (2 / ε)) :=
      le_mul_of_one_le_right hpos.le (one_le_mul_of_one_le_of_one_le ha he)
    nlinarith
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_mul hpos.ne' (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by norm_num) ha0.ne', Real.log_exp] at h2
  have h5 : Real.log 5 ≤ 2 := by
    rw [← Real.log_exp 2]
    apply Real.log_le_log (by norm_num)
    have h3 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    have := Real.exp_one_gt_d9
    rw [h3]; nlinarith
  linarith

theorem window_card_le_local_count (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3)) (γ : ℝ) :
    ((Z.finite_window (γ - (100 + 1)) (γ + (100 + 1))).toFinset.card : ℝ) ≤
      202 * A₀ * Real.log (|γ| + 306) := by
  have e : (Z.finite_window (γ - (100 + 1)) (γ + (100 + 1))).toFinset.card =
      Z.Nd (γ - (100 + 1)) (γ + (100 + 1)) :=
    (Set.ncard_eq_toFinset_card (Z.window _ _) (Z.finite_window _ _)).symm
  have hc := Nd_le_of_local_count Z hA₀ hloc (γ - 101) 202
  have hwin : γ - 101 + ((202 : ℕ) : ℝ) = γ + 101 := by push_cast; ring
  rw [hwin] at hc
  rw [e, show (100 : ℝ) + 1 = 101 by norm_num]
  refine hc.trans ?_
  have hlog : Real.log (|γ - 101| + ((202 : ℕ) : ℝ) + 3) ≤ Real.log (|γ| + 306) := by
    apply Real.log_le_log (by positivity)
    have := abs_sub γ 101
    push_cast; norm_num at this ⊢; linarith
  have hA0 : 0 ≤ A₀ := by linarith
  calc ((202 : ℕ) : ℝ) * (A₀ * Real.log (|γ - 101| + ((202 : ℕ) : ℝ) + 3))
      ≤ ((202 : ℕ) : ℝ) * (A₀ * Real.log (|γ| + 306)) := by gcongr
    _ = 202 * A₀ * Real.log (|γ| + 306) := by push_cast; ring

/-- The parameters `M = ⌈εa/2⌉`, `b = a - M`, `1 + R = e^{2/ε}` of the dictionary. -/
theorem relaxed_params {ε a : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (ha12 : Real.exp 12 ≤ a)
    (hεa : 4 ≤ ε * a) :
    ε * a / 2 ≤ (⌈ε * a / 2⌉₊ : ℝ) ∧ (⌈ε * a / 2⌉₊ : ℝ) ≤ ε * a / 2 + 1 ∧
      a / 2 ≤ a - ⌈ε * a / 2⌉₊ ∧ 4 ≤ a - ⌈ε * a / 2⌉₊ ∧ a - ⌈ε * a / 2⌉₊ ≤ a ∧
      (⌈ε * a / 2⌉₊ : ℝ) ≤ a ∧
      Real.exp (a - ⌈ε * a / 2⌉₊) ≤ Real.exp (2 / ε) ^ ⌈ε * a / 2⌉₊ := by
  set M := ⌈ε * a / 2⌉₊ with hM
  have hMlo : ε * a / 2 ≤ M := Nat.le_ceil _
  have hMhi : (M : ℝ) ≤ ε * a / 2 + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have ha : 12 ≤ a := by linarith [Real.add_one_le_exp 12]
  have ha0 : 0 < a := by linarith
  have hεa2 : ε * a / 2 ≤ a / 4 := by nlinarith
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  refine ⟨hMlo, hMhi, by linarith, by linarith, by linarith, by linarith, ?_⟩
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have h1 : a ≤ (M : ℝ) * (2 / ε) := by
    rw [mul_div_assoc', le_div_iff₀ hε]; linarith
  linarith

theorem one_le_depth_mul {ε δ a b : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (hεδ : ε ≤ δ)
    (hb : a / 2 ≤ b) (hεa : 4 ≤ ε * a) : 1 ≤ δ * (b - 2) := by
  have ha0 : 0 < a := by
    by_contra h; push Not at h; nlinarith
  have hb2 : a / 2 - 2 ≤ b - 2 := by linarith
  have h1 : ε * (a / 2 - 2) ≤ δ * (b - 2) := by
    rcases le_or_gt 0 (a / 2 - 2) with h | h
    · exact mul_le_mul hεδ hb2 h (by linarith)
    · nlinarith
  nlinarith

/-- **The relaxed dictionary.**  Let `Z` have local count `A₀`, no zeros below ordinate `2`, and let
`θ ≥ 0`, `ε > 0`.  If the relaxed Hodge index with exponent `θ` holds at a level `a ≥ max(e¹², 1/ε)`,
then every zero with `10⁴ A₀ (log(|γ| + 306) + log a + 2/ε + 2) log² a ≤ εa` satisfies
`|β - ½| ≤ θ/2 + ε`.  In particular, the relaxed Hodge index at level `a` confines the zeros up to
height `exp(cεa/(A₀ log² a))` to `|β - ½| ≤ θ/2 + ε`. -/
theorem relaxed_hodge_dictionary (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hlow : ∀ ρ ∈ Z.carrier, 2 ≤ |ρ.im|) {θ ε a : ℝ} (hθ : 0 ≤ θ) (hε : 0 < ε)
    (ha12 : Real.exp 12 ≤ a) (haε : 1 / ε ≤ a) (hrel : RelaxedHodgeIndexAtLevel Z θ a)
    {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    (hsize : 10 ^ 4 * A₀ * (Real.log (|ρ.im| + 306) + Real.log a + 2 / ε + 2) *
      Real.log a ^ 2 ≤ ε * a) :
    |ρ.re - 1 / 2| ≤ θ / 2 + ε := by
  by_contra hlt
  push Not at hlt
  have ha0 : 0 < a := lt_of_lt_of_le (Real.exp_pos 12) ha12
  have ha1 : 1 ≤ a := by linarith [Real.add_one_le_exp 12]
  set ℓ := Real.log a with hℓ
  have hℓ12 : 12 ≤ ℓ := by
    have := Real.log_le_log (Real.exp_pos 12) ha12; rwa [Real.log_exp] at this
  have hae : Real.exp ℓ = a := Real.exp_log ha0
  -- the zero of the pair to the right of the line
  obtain ⟨σ, hσ, hσre, hσim⟩ : ∃ σ ∈ Z.carrier, σ.re = 1 / 2 + |ρ.re - 1 / 2| ∧ σ.im = ρ.im := by
    rcases le_or_gt (1 / 2) ρ.re with h | h
    · exact ⟨ρ, hρ, by rw [abs_of_nonneg (by linarith)]; ring, rfl⟩
    · refine ⟨reflect ρ, Z.reflect_mem ρ hρ, ?_, Tail.reflect_im ρ⟩
      rw [abs_of_neg (by linarith)]
      simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re]; ring
  have hstσ := Z.strip σ hσ
  have hε2 : ε < 1 / 2 := by
    have : |ρ.re - 1 / 2| ≤ 1 / 2 := by linarith [hstσ.2]
    linarith
  -- the parameters
  have hεa1 : 1 ≤ ε * a := by rw [div_le_iff₀ hε] at haε; linarith
  set L₀ := Real.log (|ρ.im| + 306) with hL₀
  have hL₀0 : 0 ≤ L₀ := Real.log_nonneg (by linarith [abs_nonneg ρ.im])
  have hεa4 : 4 ≤ ε * a := by
    have h1 : 12 ≤ ℓ := hℓ12
    have h2 : 144 ≤ ℓ ^ 2 := by nlinarith
    have h3 : 2 ≤ L₀ + ℓ + 2 / ε + 2 := by
      have : 0 ≤ 2 / ε := by positivity
      linarith
    have h4 : 1 * 2 * 144 ≤ A₀ * (L₀ + ℓ + 2 / ε + 2) * ℓ ^ 2 := by
      apply mul_le_mul (mul_le_mul hA₀ h3 (by norm_num) (by linarith)) h2 (by norm_num)
        (by positivity)
    linarith
  obtain ⟨hMlo, hMhi, hb_ge, hb4, hba, hMa, hRM⟩ := relaxed_params hε hε2 ha12 hεa4
  set M := ⌈ε * a / 2⌉₊ with hMdef
  set b := a - M with hbdef
  set R := Real.exp (2 / ε) - 1 with hRdef
  have hR1 : 1 + R = Real.exp (2 / ε) := by rw [hRdef]; ring
  have hR0 : 0 ≤ R := by rw [hRdef]; linarith [Real.one_le_exp (show 0 ≤ 2 / ε by positivity)]
  rw [← hR1] at hRM
  have hb0 : 0 < b := by linarith
  set lam := 1 / (8 * b * (R + 1)) with hlam
  have hlam0 : 0 < lam := by positivity
  have hhalf : 1 / 2 ≤ σ.re := by rw [hσre]; linarith [abs_nonneg (ρ.re - 1 / 2)]
  obtain ⟨ρs, hρs, hre_ge, hdist, hdepth'⟩ :=
    exists_penalized_deepest_zero Z hσ hhalf hlam0 (show 0 ≤ R + 1 by linarith)
  set δ := ρs.re - 1 / 2 with hδdef
  have hre : ρs.re = 1 / 2 + δ := by rw [hδdef]; ring
  have hδ : θ / 2 + ε ≤ δ := by rw [hδdef]; linarith
  have hstρs := Z.strip ρs hρs
  have hδ2 : δ ≤ 1 / 2 := by linarith [hstρs.2]
  have hδ0 : 0 < δ := by linarith
  have hεδ : ε ≤ δ := by linarith
  have hlamR : lam * (R + 1) = 1 / (8 * b) := by rw [hlam]; field_simp
  have hdepth : ∀ ρ' ∈ Z.carrier, |ρ'.im - ρs.im| ≤ R + 1 → |ρ'.re - 1 / 2| ≤ δ + 1 / (8 * b) := by
    intro ρ' hρ' h
    have := hdepth' ρ' hρ' h
    rw [hlamR] at this; exact this
  -- the height of `ρs`
  have h2lam : 1 / (2 * lam) = 4 * b * Real.exp (2 / ε) := by
    rw [hlam, ← hR1]; field_simp; ring
  have hΓ : |ρs.im| ≤ |ρ.im| + 4 * a * Real.exp (2 / ε) := by
    have h1 := abs_sub_abs_le_abs_sub ρs.im σ.im
    rw [h2lam] at hdist
    have : 4 * b * Real.exp (2 / ε) ≤ 4 * a * Real.exp (2 / ε) := by gcongr
    rw [hσim] at h1 hdist
    linarith
  have hLΓ : Real.log (|ρs.im| + 306) ≤ L₀ + ℓ + 2 / ε + 2 :=
    log_height_shift_le (abs_nonneg _) (abs_nonneg _) hΓ ha1 hε
  have hnL := window_card_le_local_count Z hA₀ hloc ρs.im
  set n := (Z.finite_window (ρs.im - (100 + 1)) (ρs.im + (100 + 1))).toFinset.card with hndef
  have hsizeΓ : 10 ^ 4 * A₀ * Real.log (|ρs.im| + 306) * ℓ ^ 2 ≤ ε * a := by
    refine le_trans ?_ hsize
    have hA0 : 0 ≤ A₀ := by linarith
    have := sq_nonneg ℓ
    gcongr
  obtain ⟨hlin, hlinB, hn7, -⟩ := relaxed_dictionary_linear hA₀ (abs_nonneg _) ha12 hnL hsizeΓ
  have hM2 : 2 * n + 7 ≤ M := by
    have : ((2 * n + 7 : ℕ) : ℝ) ≤ M := by push_cast; linarith
    exact_mod_cast this
  have hM4 : 4 * n + 11 ≤ 3 * M := by omega
  have hδb : 1 ≤ δ * (b - 2) := one_le_depth_mul hε hε2 hεδ hb_ge hεa4
  have hn1 : (n : ℝ) + 1 ≤ a := by linarith
  have hkill := relaxedKillScale_ge (M := M) (n := n) hε hεδ hδ2 ha12 haε
    (by linarith) hba hMa hn1
  have hA := relaxed_condition_A hθ hε hδ hδ2 ha12 haε hMhi hb4 hkill hlin
  have hB := relaxed_condition_B hε hεδ ha12 haε hA₀ (abs_nonneg ρs.im) hMlo
    (by linarith) hM4 hkill hlinB
  have hbM : b + M = a := by rw [hbdef]; ring
  exact exists_relaxed_violation Z hA₀ hloc hlow hρs hδ0 hre (a := a) hb4 hbM.le
    hR0 hRM hdepth le_rfl hM2 hδb hA hB hrel

/-- The nontrivial zeros of `ζ` have ordinate at least `2`: `ζ` has no zero of ordinate at most
`√32` in `Re s > 0`. -/
theorem zeta_two_le_abs_im : ∀ ρ ∈ zetaZeroConfig.carrier, 2 ≤ |ρ.im| := by
  intro ρ hρ
  rw [zetaZeroConfig_carrier] at hρ
  obtain ⟨hz, h0, h1⟩ := hρ
  by_contra hlt
  push Not at hlt
  have hne1 : ρ ≠ 1 := by intro h; rw [h, Complex.one_re] at h1; linarith
  have hsq : ρ.im ^ 2 ≤ 32 := by
    have := sq_abs ρ.im
    nlinarith [abs_nonneg ρ.im]
  exact riemannZeta_ne_zero_of_im_sq_le hne1 h0 hsq hz

/-- **The relaxed dictionary for `ζ`.**  There is `A₀` such that for `θ ≥ 0`, `ε > 0`, and a level
`a ≥ max(e¹², 1/ε)` at which `Re W(f, f) ≥ -e^{θa} ∫|f|²` on polar-constrained tests, every zero of
`ζ` with `10⁴ A₀ (log(|γ| + 306) + log a + 2/ε + 2) log² a ≤ εa` has `|β - ½| ≤ θ/2 + ε`. -/
theorem zeta_relaxed_hodge_dictionary :
    ∃ A₀ : ℝ, 1 ≤ A₀ ∧ ∀ θ ε a : ℝ, 0 ≤ θ → 0 < ε → Real.exp 12 ≤ a → 1 / ε ≤ a →
      RelaxedHodgeIndexAtLevel zetaZeroConfig θ a → ∀ ρ ∈ zetaZeroConfig.carrier,
        10 ^ 4 * A₀ * (Real.log (|ρ.im| + 306) + Real.log a + 2 / ε + 2) * Real.log a ^ 2 ≤
          ε * a →
        |ρ.re - 1 / 2| ≤ θ / 2 + ε := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zetaZeroConfig_local_count
  exact ⟨A₀, hA₀, fun θ ε a hθ hε ha12 haε hrel ρ hρ hsize =>
    relaxed_hodge_dictionary zetaZeroConfig hA₀ hloc zeta_two_le_abs_im hθ hε ha12 haε hrel hρ
      hsize⟩

/-- **Height form.**  If `a ≥ max(e¹², 1/ε)` and `10⁴ A₀ (log a + 2/ε + 2) log² a ≤ εa/2`, then the
relaxed Hodge index with exponent `θ` at level `a` confines every zero with
`log(|γ| + 306) ≤ εa/(2·10⁴ A₀ log² a)` to `|β - ½| ≤ θ/2 + ε`. -/
theorem relaxed_hodge_dictionary_height (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hlow : ∀ ρ ∈ Z.carrier, 2 ≤ |ρ.im|) {θ ε a : ℝ} (hθ : 0 ≤ θ) (hε : 0 < ε)
    (ha12 : Real.exp 12 ≤ a) (haε : 1 / ε ≤ a)
    (ha : 10 ^ 4 * A₀ * (Real.log a + 2 / ε + 2) * Real.log a ^ 2 ≤ ε * a / 2)
    (hrel : RelaxedHodgeIndexAtLevel Z θ a) {ρ : ℂ} (hρ : ρ ∈ Z.carrier)
    (hγ : 2 * 10 ^ 4 * A₀ * Real.log (|ρ.im| + 306) * Real.log a ^ 2 ≤ ε * a) :
    |ρ.re - 1 / 2| ≤ θ / 2 + ε := by
  refine relaxed_hodge_dictionary Z hA₀ hloc hlow hθ hε ha12 haε hrel hρ ?_
  have e : 10 ^ 4 * A₀ * (Real.log (|ρ.im| + 306) + Real.log a + 2 / ε + 2) * Real.log a ^ 2 =
      10 ^ 4 * A₀ * Real.log (|ρ.im| + 306) * Real.log a ^ 2 +
        10 ^ 4 * A₀ * (Real.log a + 2 / ε + 2) * Real.log a ^ 2 := by ring
  rw [e]
  linarith

end RHTower
