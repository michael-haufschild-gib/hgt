import GaloisForLFunctions.RHTower.JointAncestryLevelOneCapstones

/-!
# The budget law: JAS positivity at prime budget `y^λ` is a zero-free half-plane `½ − λ`

For a set `P` of primes in a dyadic range `(y, 2y]` the prime budget at level `σ` is
`Σ_{p ∈ P} p^{−(σ−½)}`.  `JasBudgetProductPositive X σ λ` asks for positivity of the constant-vector
product tests on every such set with `y ≥ X + 1` and budget at most `y^λ`.

* **Producer** (`exists_jasBudgetProductPositive_of_halfPlane`).  A half-plane `|Re ρ − ½| ≤ α`
  with `λ < ½ − α` gives budget positivity at every level.  Each zero sees
  `Σ_P p^{−(σ−|Re ρ−½|)} ≤ y^{λ−(½−α)}`, and the hypothesis-free zero-sum bound
  `jasProductAggregate_re_ge_exp` closes.
* **Receiver** (`abs_re_sub_half_le_of_jasBudgetProductPositive`).  For `σ ≥ ½` and `λ > 0`,
  budget positivity forces `|Re ρ − ½| ≤ max(0, σ − 1, ½ − λ)`.  Subsets of the Huxley windows with
  weight `≍ e^{−cu}` have budget `≍ e^{(½−c)u}`, so the diagonal Bochner receiver runs for every
  `c > ½ − λ`.

At level `1` this is sharp up to the boundary:
* quasi-RH ⟺ budget positivity for some `λ > 0` (`exists_halfPlane_lt_half_iff_exists_jasBudgetProductPositive`);
* RH ⟺ budget positivity at `λ = ½` (`riemannHypothesis_iff_exists_jasBudgetProductPositive_half`).

So every intermediate JAS producer is exactly a zero-free half-plane of the matching width.
-/

open Filter

namespace RHTower

noncomputable section

/-- Constant-vector product positivity on every set of primes in a dyadic range `(y, 2y]`,
`y ≥ X + 1`, with prime budget `Σ p^{−(σ−½)} ≤ y^lam`. -/
def JasBudgetProductPositive (X : ℕ) (σ lam : ℝ) : Prop :=
  ∀ (y : ℝ) (P : Finset Nat.Primes), (X : ℝ) + 1 ≤ y →
    (∀ p ∈ P, y < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ 2 * y) →
    ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤ Real.exp (lam * Real.log y) →
    JasConstProductPositiveOn P σ

theorem JasProductPositiveAbove.budgetPositive {X : ℕ} {σ : ℝ} (h : JasProductPositiveAbove X σ)
    (lam : ℝ) : JasBudgetProductPositive X σ lam := by
  intro y P hy hP _
  refine h.constOn fun p hp => ?_
  have : (X : ℝ) < ((p : ℕ) : ℝ) := by linarith [(hP p hp).1]
  exact_mod_cast this

/-! ## The producer -/

/-- **Producer.**  A half-plane `|Re ρ − ½| ≤ α` with `lam < ½ − α` gives budget positivity at every
level `σ`, above some `X`. -/
theorem exists_jasBudgetProductPositive_of_halfPlane {α σ lam : ℝ} (hXi : XiZeroHalfPlaneBound α)
    (hlam : lam < 1 / 2 - α) : ∃ X : ℕ, JasBudgetProductPositive X σ lam := by
  have hab : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ α :=
    abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi
  have hW := lagWeightTotal_pos
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = Real.log (1 + poleSharpConstant / lagWeightTotal) := ⟨_, rfl⟩
  have ht : 0 < t := by
    rw [htdef]; exact Real.log_pos (by have := div_pos poleSharpConstant_pos hW; linarith)
  have hexpt : Real.exp t - 1 = poleSharpConstant / lagWeightTotal := by
    rw [htdef, Real.exp_log (by have := div_pos poleSharpConstant_pos hW; linarith)]; ring
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / 2 - α - lam := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; linarith
  -- `y^{−ε} ≤ t` for `log y ≥ max 0 (−log t / ε)`
  obtain ⟨X, hX⟩ := exists_nat_gt (Real.exp (max 0 (-Real.log t / ε)))
  refine ⟨X, fun y P hy hP hB z => ?_⟩
  have hy0 : 0 < y := by linarith [Nat.cast_nonneg (α := ℝ) X]
  have hlogy : max 0 (-Real.log t / ε) ≤ Real.log y := by
    rw [← Real.log_exp (max 0 (-Real.log t / ε))]
    exact Real.log_le_log (Real.exp_pos _) (by linarith)
  have hyε : Real.exp (-(ε * Real.log y)) ≤ t := by
    have h1 : -Real.log t / ε ≤ Real.log y := (le_max_right _ _).trans hlogy
    have h2 : -(ε * Real.log y) ≤ Real.log t := by
      rw [div_le_iff₀ hε] at h1; linarith
    calc Real.exp (-(ε * Real.log y)) ≤ Real.exp (Real.log t) := Real.exp_le_exp.mpr h2
      _ = t := Real.exp_log ht
  -- each zero sees at most `t`
  have hzero : ∀ q : XiZeroCopy,
      ∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ)) ≤ t := by
    intro q
    have hq := hab q
    have hterm : ∀ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ)) ≤
        Real.exp (-(1 / 2 - α) * Real.log y) *
          Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) := by
      intro p hp
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hlogp : Real.log y ≤ Real.log ((p : ℕ) : ℝ) := Real.log_le_log hy0 (hP p hp).1.le
      have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) X])
      have hb12 : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
        rw [abs_le]; constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
      have h1 : (1 / 2 - α) * Real.log y ≤
          (1 / 2 - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ) := by
        rcases le_or_gt 0 (1 / 2 - α) with h | h
        · calc (1 / 2 - α) * Real.log y ≤ (1 / 2 - α) * Real.log ((p : ℕ) : ℝ) :=
                mul_le_mul_of_nonneg_left hlogp h
            _ ≤ (1 / 2 - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ) :=
                mul_le_mul_of_nonneg_right (by linarith) (hly.trans hlogp)
        · have e1 : (1 / 2 - α) * Real.log y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h.le hly
          have e2 : 0 ≤ (1 / 2 - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ) :=
            mul_nonneg (by linarith) (hly.trans hlogp)
          linarith
      linarith
    calc ∑ p ∈ P, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ))
        ≤ ∑ p ∈ P, Real.exp (-(1 / 2 - α) * Real.log y) *
            Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) := Finset.sum_le_sum hterm
      _ = Real.exp (-(1 / 2 - α) * Real.log y) *
            ∑ p ∈ P, Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ Real.exp (-(1 / 2 - α) * Real.log y) * Real.exp (lam * Real.log y) :=
          mul_le_mul_of_nonneg_left hB (Real.exp_pos _).le
      _ = Real.exp (-(ε * Real.log y)) := by rw [← Real.exp_add, hεdef]; ring_nf
      _ ≤ t := hyε
  have hbound := jasProductAggregate_re_ge_exp (σ := σ) P (fun _ => z)
  refine le_trans (mul_nonneg (Finset.prod_nonneg fun _ _ => by positivity) ?_) hbound
  have hS : ∑' q : XiZeroCopy, (Real.exp (∑ p ∈ P,
      Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ))) - 1) *
        ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
      ∑' q : XiZeroCopy, (Real.exp t - 1) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
    refine Summable.tsum_le_tsum (fun q => mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)) ?_
      (summable_inv_mul_one_sub.norm.mul_left _)
    · linarith [Real.exp_le_exp.mpr (hzero q)]
    · refine Summable.of_nonneg_of_le (fun q => mul_nonneg ?_ (norm_nonneg _))
        (fun q => mul_le_mul_of_nonneg_right (by linarith [Real.exp_le_exp.mpr (hzero q)])
          (norm_nonneg _)) (summable_inv_mul_one_sub.norm.mul_left (Real.exp t - 1))
      linarith [Real.one_le_exp (Finset.sum_nonneg fun p (_ : p ∈ P) =>
        (Real.exp_pos (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ))).le)]
  rw [tsum_mul_left] at hS
  have hWt : ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ = lagWeightTotal := rfl
  rw [hWt, hexpt, div_mul_cancel₀ _ hW.ne'] at hS
  linarith

/-! ## The receiver -/

/-- Budget positivity supplies positive windows: subsets of the Huxley windows with weight
`≍ e^{−cu}` have budget `≲ e^{(½−c)u} ≤ y^λ`. -/
theorem eventually_jasPositiveWindow_of_jasBudgetProductPositive {X : ℕ} {σ lam : ℝ}
    (hpos : JasBudgetProductPositive X σ lam) (hσ : 1 / 2 ≤ σ) (hlam : 0 < lam) {δ c : ℝ}
    (hδ0 : 0 < δ) (hδ : δ < 5 / 12) (hc0 : 0 < c) (hc : σ - 1 + δ < c) (hcl : 1 / 2 - lam < c)
    (hch : c < 1 / 2) : ∀ᶠ u : ℝ in atTop, JasPositiveWindow σ δ c u := by
  obtain ⟨c', hc'def⟩ : ∃ c' : ℝ, c' = (c + max 0 (σ - 1 + δ)) / 2 := ⟨_, rfl⟩
  have hm1 := le_max_left 0 (σ - 1 + δ)
  have hm2 := le_max_right 0 (σ - 1 + δ)
  have hmc : max 0 (σ - 1 + δ) < c := max_lt hc0 hc
  have hc'0 : 0 < c' := by rw [hc'def]; linarith
  have hc'c : c' < c := by rw [hc'def]; linarith
  have hc'σ : σ - 1 + δ < c' := by rw [hc'def]; linarith
  obtain ⟨X₀, -, hX₀⟩ := exists_theta_window_lower_seven_twelfths
    (α := (7 / 12 + (1 - δ)) / 2) (by linarith) (by linarith)
  -- the card and budget conditions
  have ev5 : ∀ᶠ u : ℝ in atTop,
      Real.exp σ * Real.exp ((σ - c) * u) + 1 ≤ Real.exp ((σ - c') * u) := by
    have ht : Tendsto (fun u : ℝ => Real.exp ((c - c') * u)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith))
    have ht2 : Tendsto (fun u : ℝ => Real.exp ((σ - c') * u)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith))
    filter_upwards [ht.eventually_ge_atTop (2 * Real.exp σ), ht2.eventually_ge_atTop 2] with u h1 h2
    have e : Real.exp ((σ - c') * u) = Real.exp ((c - c') * u) * Real.exp ((σ - c) * u) := by
      rw [← Real.exp_add]; ring_nf
    have hp := Real.exp_pos ((σ - c) * u)
    have hpe := Real.exp_pos σ
    rw [e] at h2 ⊢
    nlinarith
  have ev6 : ∀ᶠ u : ℝ in atTop,
      Real.exp σ * Real.exp ((1 / 2 - c) * u) + Real.exp (-((σ - 1 / 2) * u)) ≤ Real.exp (lam * u) := by
    have ht : Tendsto (fun u : ℝ => Real.exp ((lam - (1 / 2 - c)) * u)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith))
    have ht2 : Tendsto (fun u : ℝ => Real.exp (lam * u)) atTop atTop :=
      Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hlam)
    filter_upwards [ht.eventually_ge_atTop (2 * Real.exp σ), ht2.eventually_ge_atTop 2,
      eventually_ge_atTop (0 : ℝ)] with u h1 h2 hu
    have e : Real.exp (lam * u) = Real.exp ((lam - (1 / 2 - c)) * u) * Real.exp ((1 / 2 - c) * u) := by
      rw [← Real.exp_add]; ring_nf
    have h3 : Real.exp (-((σ - 1 / 2) * u)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have hp := Real.exp_pos ((1 / 2 - c) * u)
    have hpe := Real.exp_pos σ
    have h4 : 2 * Real.exp σ * Real.exp ((1 / 2 - c) * u) ≤ Real.exp (lam * u) := by
      rw [e]; nlinarith
    linarith
  filter_upwards [eventually_diagWindow_conditions X (σ := σ) (δ := δ) (c := c')
    (α' := (7 / 12 + (1 - δ)) / 2) (X₀ := X₀) (by linarith) (by linarith) hc'0, ev5, ev6]
    with u hu h5 h6
  obtain ⟨hE1, hE1', hE2, hE3, -, hu1⟩ := hu
  obtain ⟨P, hPdef, hlogP, hMass⟩ := exists_window (X := X) (c := c') (by linarith) hδ0
    (by linarith) (by linarith) hX₀ hu1 hE1 hE1' hE2 hE3
  have hu0 : 0 ≤ u := by linarith
  -- the window lies in `(e^u, 2e^u]`
  have hmem : ∀ p ∈ P, Real.exp u < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ 2 * Real.exp u := by
    intro p hp
    rw [hPdef] at hp
    have hp' : (p : ℕ) ∈ (Finset.Ioc ⌊Real.exp u⌋₊ ⌊Real.exp u + Real.exp ((1 - δ) * u)⌋₊).filter
        Nat.Prime := Finset.mem_subtype.mp hp
    rw [Finset.mem_filter, Finset.mem_Ioc] at hp'
    have hL : Real.exp ((1 - δ) * u) ≤ Real.exp u := Real.exp_le_exp.mpr (by nlinarith)
    exact ⟨(Nat.floor_lt (Real.exp_pos u).le).mp hp'.1.1,
      le_trans (by exact_mod_cast hp'.1.2) ((Nat.floor_le (by positivity)).trans (by linarith))⟩
  have hlogup : ∀ p ∈ P, Real.log ((p : ℕ) : ℝ) ≤ u + 1 := by
    intro p hp
    have h1 := (hmem p hp).2
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := lt_trans (Real.exp_pos u) (hmem p hp).1
    have h2 : Real.log ((p : ℕ) : ℝ) ≤ Real.log (2 * Real.exp u) := Real.log_le_log hp0 h1
    rw [Real.log_mul (by norm_num) (Real.exp_pos u).ne', Real.log_exp] at h2
    linarith [Real.log_two_lt_d9]
  -- the card of the window
  have hcard : Real.exp (-(c' * u)) * Real.exp (σ * u) ≤ P.card := by
    have h1 : ∑ p ∈ P, Real.exp (-σ * Real.log ((p : ℕ) : ℝ)) ≤ P.card * Real.exp (-(σ * u)) := by
      have := Finset.sum_le_sum fun p (hp : p ∈ P) =>
        (Real.exp_le_exp.mpr (show -σ * Real.log ((p : ℕ) : ℝ) ≤ -(σ * u) by
          nlinarith [(hlogP p hp).1]))
      simpa [Finset.sum_const, nsmul_eq_mul] using this
    have h2 := hMass.trans h1
    have e : Real.exp (-(σ * u)) * Real.exp (σ * u) = 1 := by rw [← Real.exp_add]; simp
    have := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (σ * u)).le
    rw [mul_assoc, e, mul_one] at this
    exact this
  -- choose `k` primes
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = ⌈Real.exp (-(c * u)) * Real.exp (σ * (u + 1))⌉₊ := ⟨_, rfl⟩
  have hk1 : Real.exp (-(c * u)) * Real.exp (σ * (u + 1)) ≤ k := by rw [hkdef]; exact Nat.le_ceil _
  have hk2 : (k : ℝ) < Real.exp (-(c * u)) * Real.exp (σ * (u + 1)) + 1 := by
    rw [hkdef]; exact Nat.ceil_lt_add_one (by positivity)
  have hkP : k ≤ P.card := by
    have e1 : Real.exp (-(c * u)) * Real.exp (σ * (u + 1)) = Real.exp σ * Real.exp ((σ - c) * u) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(c' * u)) * Real.exp (σ * u) = Real.exp ((σ - c') * u) := by
      rw [← Real.exp_add]; ring_nf
    have : (k : ℝ) ≤ P.card := by rw [e1] at hk2; rw [e2] at hcard; linarith
    exact_mod_cast this
  obtain ⟨P', hP'P, hP'card⟩ := Finset.exists_subset_card_eq hkP
  refine ⟨P', ?_, fun p hp => hlogP p (hP'P hp), ?_⟩
  · -- positivity from the budget hypothesis
    refine hpos (Real.exp u) P' hE1' (fun p hp => hmem p (hP'P hp)) ?_
    rw [Real.log_exp]
    have hterm : ∀ p ∈ P', Real.exp (-(σ - 1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤
        Real.exp (-((σ - 1 / 2) * u)) := fun p hp =>
      Real.exp_le_exp.mpr (by nlinarith [(hlogP p (hP'P hp)).1])
    have h1 := Finset.sum_le_sum hterm
    simp only [Finset.sum_const, nsmul_eq_mul, hP'card] at h1
    have h2 : (k : ℝ) * Real.exp (-((σ - 1 / 2) * u)) ≤
        (Real.exp (-(c * u)) * Real.exp (σ * (u + 1)) + 1) * Real.exp (-((σ - 1 / 2) * u)) :=
      mul_le_mul_of_nonneg_right hk2.le (Real.exp_pos _).le
    have e : (Real.exp (-(c * u)) * Real.exp (σ * (u + 1)) + 1) * Real.exp (-((σ - 1 / 2) * u)) =
        Real.exp σ * Real.exp ((1 / 2 - c) * u) + Real.exp (-((σ - 1 / 2) * u)) := by
      rw [add_mul, one_mul, mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add σ]
      congr 2
      ring
    linarith
  · -- the weight
    have hterm : ∀ p ∈ P', Real.exp (-(σ * (u + 1))) ≤ Real.exp (-σ * Real.log ((p : ℕ) : ℝ)) :=
      fun p hp => Real.exp_le_exp.mpr (by nlinarith [hlogup p (hP'P hp)])
    have h1 := Finset.sum_le_sum hterm
    simp only [Finset.sum_const, nsmul_eq_mul, hP'card] at h1
    have h2 := mul_le_mul_of_nonneg_right hk1 (Real.exp_pos (-(σ * (u + 1)))).le
    have e : Real.exp (-(c * u)) * Real.exp (σ * (u + 1)) * Real.exp (-(σ * (u + 1))) =
        Real.exp (-(c * u)) := by
      rw [mul_assoc, ← Real.exp_add]; simp
    linarith

/-- **Receiver.**  For `σ ≥ ½` and `λ > 0`, budget positivity forces
`|Re ρ − ½| ≤ max(0, max(σ − 1, ½ − λ))`. -/
theorem abs_re_sub_half_le_of_jasBudgetProductPositive {X : ℕ} {σ lam : ℝ}
    (hpos : JasBudgetProductPositive X σ lam) (hσ : 1 / 2 ≤ σ) (hlam : 0 < lam) (q : XiZeroCopy) :
    |(q.1 : ℂ).re - 1 / 2| ≤ max 0 (max (σ - 1) (1 / 2 - lam)) :=
  abs_re_sub_half_le_of_windows (fun _ _ hδ0 hδ hc0 hc hch =>
    eventually_jasPositiveWindow_of_jasBudgetProductPositive hpos hσ hlam hδ0 hδ hc0
      (by linarith [le_max_left (σ - 1) (1 / 2 - lam)])
      (by linarith [le_max_right (σ - 1) (1 / 2 - lam)]) hch) q

/-! ## Capstones at level one -/

/-- **Quasi-RH ⟺ level-one budget positivity for some exponent `λ > 0`.** -/
theorem exists_halfPlane_lt_half_iff_exists_jasBudgetProductPositive :
    (∃ α : ℝ, α < 1 / 2 ∧ XiZeroHalfPlaneBound α) ↔
      ∃ X : ℕ, ∃ lam : ℝ, 0 < lam ∧ JasBudgetProductPositive X 1 lam := by
  constructor
  · rintro ⟨α, hα, hXi⟩
    obtain ⟨X, hX⟩ := exists_jasBudgetProductPositive_of_halfPlane (σ := 1)
      (lam := (1 / 2 - α) / 2) hXi (by linarith)
    exact ⟨X, (1 / 2 - α) / 2, by linarith, hX⟩
  · rintro ⟨X, lam, hlam, h⟩
    refine ⟨max 0 (1 / 2 - lam), max_lt (by norm_num) (by linarith), fun ρ hρ => ?_⟩
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := abs_re_sub_half_le_of_jasBudgetProductPositive h (by norm_num) hlam q
    rw [show max (1 - 1 : ℝ) (1 / 2 - lam) = max 0 (1 / 2 - lam) by norm_num,
      max_eq_right (le_max_left 0 (1 / 2 - lam))] at this
    linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

/-- **RH ⟺ level-one budget positivity at exponent `½`.** -/
theorem riemannHypothesis_iff_exists_jasBudgetProductPositive_half :
    RiemannHypothesis ↔ ∃ X : ℕ, JasBudgetProductPositive X 1 (1 / 2) := by
  constructor
  · intro hRH
    obtain ⟨X, hX⟩ := riemannHypothesis_iff_exists_jasProductPositiveAbove_one.mp hRH
    exact ⟨X, hX.budgetPositive _⟩
  · rintro ⟨X, h⟩
    refine riemannHypothesis_iff_xiZeroHalfPlaneBound_zero.mpr fun ρ hρ => ?_
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have := abs_re_sub_half_le_of_jasBudgetProductPositive h (by norm_num) (by norm_num) q
    norm_num at this
    linarith [le_abs_self ((q.1 : ℂ).re - 1 / 2)]

end

end RHTower
