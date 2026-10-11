import GaloisForLFunctions.RHTower.JointAncestryHalfPlaneExistence

/-!
# The sharp per-zero constant of the JAS abscissa law

**Theorem** (`jasDressedPSD_one_add_mul_of_xiZeroHalfPlaneBound`).  Let `K > 1` and `α > 0` with
`(K + 1)α ≤ 1` and `log((K + 1)/(K − 1)) + (22/3 + 1/7)α ≤ π/2`.  If every Xi zero has
`Re ρ ≤ ½ + α`, the dressed JAS aggregate is positive semidefinite at `σ = 1 + Kα`.

The budget condition holds for all small `α` exactly when `log((K + 1)/(K − 1)) < π/2`, that is
`K > coth(π/4) ≈ 1.525`.  With the chain exclusion this gives, off RH under a half-plane bound
below `½`, for `δ* = sup |Re ρ − ½| ≤ 1/100`:

`1 + δ* ≤ σ* ≤ 1 + (5/3) δ*`   (`one_add_sSup_le_jasAbscissa_and_le_five_thirds`).

**Proof.**  For a zero with `|Re ρ − ½| = δ ≤ α` put `a = 1 + Kα − δ`, `b = 1 + Kα + δ`.  The
radii are `p^{−a}` and `p^{−b}`, so the phase width is at most
`(p^{−a} − p^{−b})(1 + (4/3)p^{−2})`.  Writing `p^{−a} − p^{−b} = ∫_a^b log p · p^{−s} ds` and using
`Σ_p log p · p^{−s} ≤ 1/(s − 1) + 1` gives `Σ_p (p^{−a} − p^{−b}) ≤ log((b − 1)/(a − 1)) + (b − a)`,
and `(b − 1)/(a − 1) = (Kα + δ)/(Kα − δ) ≤ (K + 1)/(K − 1)`.  The weight argument is at most
`δ/7`, since off-line zeros have `|Im ρ| ≥ 14`.
-/

open Complex intervalIntegral

namespace RHTower

noncomputable section

/-- The weight argument is proportional to the distance from the critical line:
`|arg (1/(ρ(1 − ρ)))| ≤ |Re ρ − ½| / 7`. -/
theorem abs_arg_lagWeight_le_div_seven (q : XiZeroCopy) :
    |(1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).arg| ≤ |(q.1 : ℂ).re - 1 / 2| / 7 := by
  set z : ℂ := (q.1 : ℂ) * (1 - (q.1 : ℂ)) with hz
  obtain ⟨hβ0, hβ1⟩ := xiZeroCopy_re_mem_open_unit q
  set β := ((q.1 : ℂ)).re
  set γ := ((q.1 : ℂ)).im
  have hre : z.re = β * (1 - β) + γ ^ 2 := by
    rw [hz]; simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im]; ring
  have him : z.im = γ * (1 - 2 * β) := by
    rw [hz]; simp only [Complex.mul_im, Complex.sub_re, Complex.one_re, Complex.sub_im,
      Complex.one_im]; ring
  have hre_pos : 0 < z.re := by rw [hre]; nlinarith [sq_nonneg γ]
  have hargz : z.arg ≠ Real.pi := by
    intro h
    have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre_pos)
    rw [h, abs_of_pos Real.pi_pos] at this
    linarith [Real.pi_pos]
  rw [one_div, Complex.arg_inv, if_neg hargz, abs_neg]
  refine (abs_arg_le_abs_im_div_re hre_pos).trans ?_
  rw [div_le_iff₀ hre_pos, him, hre, abs_mul]
  have h12 : |1 - 2 * β| = 2 * |β - 1 / 2| := by
    rw [show 1 - 2 * β = -2 * (β - 1 / 2) by ring, abs_mul]; norm_num
  rw [h12]
  have hpos : 0 ≤ β * (1 - β) := by nlinarith
  by_cases hoff : β = 1 / 2
  · rw [hoff]; norm_num
  · have hγ : 431 / 2 ≤ γ ^ 2 := fourHundredThirtyOne_halves_le_im_sq_of_xiZeroCopy_offLine q hoff
    have hγabs : 14 ≤ |γ| := by
      by_contra hlt
      push Not at hlt
      have := mul_self_lt_mul_self (abs_nonneg γ) hlt
      nlinarith [sq_abs γ]
    have hsq : |γ| ^ 2 = γ ^ 2 := sq_abs γ
    have hd := abs_nonneg (β - 1 / 2)
    have h2 : 2 * |γ| ≤ γ ^ 2 / 7 := by rw [← hsq]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hd, mul_nonneg hd hpos]

/-- `p^{−a} − p^{−b} = ∫_a^b log p · p^{−s} ds`. -/
theorem exp_neg_sub_exp_neg_eq_integral (L a b : ℝ) :
    Real.exp (-a * L) - Real.exp (-b * L) = ∫ s in a..b, L * Real.exp (-s * L) := by
  have hderiv : ∀ s ∈ Set.uIcc a b,
      HasDerivAt (fun s : ℝ => -Real.exp (-s * L)) (L * Real.exp (-s * L)) s := by
    intro s _
    have h : HasDerivAt (fun s : ℝ => -Real.exp (-s * L)) (-(Real.exp (-s * L) * (-1 * L))) s :=
      ((hasDerivAt_neg s).mul_const L).exp.neg
    rw [show L * Real.exp (-s * L) = -(Real.exp (-s * L) * (-1 * L)) by ring]
    exact h
  rw [integral_eq_sub_of_hasDerivAt hderiv (Continuous.intervalIntegrable (by fun_prop) a b)]
  ring

/-- **The prime sum between two exponents.**  For `1 < a ≤ b ≤ 2`,
`Σ_{p ∈ P} (p^{−a} − p^{−b}) ≤ log((b − 1)/(a − 1)) + (b − a)`. -/
theorem sum_exp_neg_sub_exp_neg_le (P : Finset Nat.Primes) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b)
    (hb : b ≤ 2) :
    ∑ p ∈ P, (Real.exp (-a * Real.log p) - Real.exp (-b * Real.log p)) ≤
      Real.log ((b - 1) / (a - 1)) + (b - a) := by
  have hint : ∀ p ∈ P, IntervalIntegrable
      (fun s : ℝ => Real.log p * Real.exp (-s * Real.log p)) MeasureTheory.volume a b :=
    fun p _ => Continuous.intervalIntegrable (by fun_prop) a b
  have hsum : ∑ p ∈ P, (Real.exp (-a * Real.log p) - Real.exp (-b * Real.log p)) =
      ∑ p ∈ P, ∫ s in a..b, Real.log p * Real.exp (-s * Real.log p) :=
    Finset.sum_congr rfl fun p _ => exp_neg_sub_exp_neg_eq_integral _ a b
  rw [hsum, ← integral_finsetSum hint]
  have hcont : ContinuousOn (fun s : ℝ => (s - 1)⁻¹ + 1) (Set.uIcc a b) := by
    refine ContinuousOn.add (ContinuousOn.inv₀ (by fun_prop) fun s hs => ?_) continuousOn_const
    rw [Set.uIcc_of_le hab] at hs
    linarith [hs.1]
  have hle : ∫ s in a..b, ∑ p ∈ P, Real.log p * Real.exp (-s * Real.log p) ≤
      ∫ s in a..b, ((s - 1)⁻¹ + 1) := by
    refine integral_mono_on hab (Continuous.intervalIntegrable (by fun_prop) a b) (hcont.intervalIntegrable)
      fun s hs => ?_
    have h := sum_log_mul_exp_neg_le P (s := s) (by linarith [hs.1]) (by linarith [hs.2])
    rw [one_div] at h
    exact h
  refine hle.trans (le_of_eq ?_)
  have hinv : IntervalIntegrable (fun s : ℝ => (s - 1)⁻¹) MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.inv₀ (by fun_prop) fun s hs => ?_
    rw [Set.uIcc_of_le hab] at hs
    linarith [hs.1]
  have hshift := intervalIntegral.integral_comp_sub_right (fun s : ℝ => s⁻¹) (a := a) (b := b) 1
  rw [integral_add hinv intervalIntegrable_const, hshift,
    integral_inv_of_pos (by linarith) (by linarith), integral_const, smul_eq_mul, mul_one]

/-- `|e^{−x} − e^{x}| = e^{|x|} − e^{−|x|}`. -/
theorem abs_exp_neg_sub_exp_eq (x : ℝ) :
    |Real.exp (-x) - Real.exp x| = Real.exp |x| - Real.exp (-|x|) := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonpos (by linarith [Real.exp_le_exp.mpr (show -x ≤ x by linarith)])]
    ring
  · rw [abs_of_nonpos hx, neg_neg, abs_of_nonneg (by linarith [Real.exp_le_exp.mpr (show x ≤ -x by linarith)])]

/-- The phase width through two radii bounded by `A ≤ ½`:
`W ≤ (A − B)(1 + (4/3) X)` when `|r₁ − r₂| = A − B` and `A² ≤ X`. -/
theorem jasPhaseWidth_le_of_radii {r₁ r₂ A B X : ℝ} (h1 : 0 < r₁) (h2 : 0 < r₂) (hA1 : r₁ ≤ A)
    (hA2 : r₂ ≤ A) (hAh : A ≤ 1 / 2) (hdiff : |r₁ - r₂| = A - B) (hX : A ^ 2 ≤ X) :
    jasPhaseWidth r₁ r₂ ≤ (A - B) * (1 + 4 / 3 * X) := by
  have hA0 : 0 < A := lt_of_lt_of_le h1 hA1
  have hsq : A ^ 2 ≤ 1 / 4 := by nlinarith
  have hpos : 0 < 1 - A ^ 2 := by linarith
  have hden : 1 - A ^ 2 ≤ Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) := by
    refine Real.le_sqrt_of_sq_le ?_
    have a : 1 - A ^ 2 ≤ 1 - r₁ ^ 2 := by nlinarith
    have b : 1 - A ^ 2 ≤ 1 - r₂ ^ 2 := by nlinarith
    exact pow_two (1 - A ^ 2) ▸ mul_le_mul a b hpos.le (by linarith)
  have hD0 : 0 ≤ A - B := hdiff ▸ abs_nonneg _
  unfold jasPhaseWidth
  refine (arctan_le_self_of_nonneg' (div_nonneg (abs_nonneg _)
    (lt_of_lt_of_le hpos hden).le)).trans ?_
  rw [hdiff]
  calc (A - B) / Real.sqrt ((1 - r₁ ^ 2) * (1 - r₂ ^ 2)) ≤ (A - B) / (1 - A ^ 2) :=
        div_le_div_of_nonneg_left hD0 hpos hden
    _ ≤ (A - B) * (1 + 4 / 3 * A ^ 2) := by
        rw [div_le_iff₀ hpos]
        have h3 : 1 ≤ (1 + 4 / 3 * A ^ 2) * (1 - A ^ 2) := by nlinarith
        calc A - B = (A - B) * 1 := (mul_one _).symm
          _ ≤ (A - B) * ((1 + 4 / 3 * A ^ 2) * (1 - A ^ 2)) := mul_le_mul_of_nonneg_left h3 hD0
          _ = (A - B) * (1 + 4 / 3 * A ^ 2) * (1 - A ^ 2) := by ring
    _ ≤ (A - B) * (1 + 4 / 3 * X) := mul_le_mul_of_nonneg_left (by linarith) hD0

/-- **Sharp phase width.**  At `σ = 1 + Kα`, for a zero at distance `d = |Re ρ − ½| ≤ α`,
`W_p ≤ (p^{−(1+Kα−d)} − p^{−(1+Kα+d)})(1 + (4/3) p^{−2})`. -/
theorem jasPhaseWidth_le_sharp {ρ : ℂ} {alpha K : ℝ} (hρ : |ρ.re - 1 / 2| ≤ alpha) (hK : 1 ≤ K)
    (p : Nat.Primes) :
    jasPhaseWidth (jasR1 (ρ + ((1 / 2 + K * alpha : ℝ) : ℂ)) p)
        (jasR2 (ρ - ((1 / 2 + K * alpha : ℝ) : ℂ)) p) ≤
      (Real.exp (-(1 + K * alpha - |ρ.re - 1 / 2|) * Real.log p) -
          Real.exp (-(1 + K * alpha + |ρ.re - 1 / 2|) * Real.log p)) *
        (1 + 4 / 3 * Real.exp (-2 * Real.log p)) := by
  rw [jasR1_dressed, jasR2_dressed]
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = ρ.re - 1 / 2 := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = Real.log p := ⟨_, rfl⟩
  rw [← hL, ← hδ]
  rw [← hδ] at hρ
  have hL2 : Real.log 2 ≤ L := by
    rw [hL]; exact Real.log_le_log (by norm_num) (by exact_mod_cast p.2.two_le)
  have hL0 : 0 < L := lt_of_lt_of_le (Real.log_pos (by norm_num)) hL2
  have hre : ρ.re = 1 / 2 + δ := by rw [hδ]; ring
  rw [hre]
  have halpha : 0 ≤ alpha := le_trans (abs_nonneg _) hρ
  have hdK : |δ| ≤ K * alpha := le_trans hρ (le_mul_of_one_le_left halpha hK)
  have hdL : |δ * L| = |δ| * L := by rw [abs_mul, abs_of_pos hL0]
  refine jasPhaseWidth_le_of_radii (Real.exp_pos _) (Real.exp_pos _) ?_ ?_ ?_ ?_ ?_
  · exact Real.exp_le_exp.mpr (by nlinarith [le_abs_self δ, neg_abs_le δ])
  · exact Real.exp_le_exp.mpr (by nlinarith [le_abs_self δ, neg_abs_le δ])
  · have h2 : Real.exp (-Real.log 2) = 1 / 2 := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
    rw [← h2]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · have e1 : Real.exp (-(1 / 2 + δ + (1 / 2 + K * alpha)) * L) =
        Real.exp (-(1 + K * alpha) * L) * Real.exp (-(δ * L)) := by
      rw [← Real.exp_add]; ring_nf
    have e2 : Real.exp (-(1 - (1 / 2 + δ) + (1 / 2 + K * alpha)) * L) =
        Real.exp (-(1 + K * alpha) * L) * Real.exp (δ * L) := by
      rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp (-(1 + K * alpha - |δ|) * L) =
        Real.exp (-(1 + K * alpha) * L) * Real.exp |δ * L| := by
      rw [hdL, ← Real.exp_add]; ring_nf
    have e4 : Real.exp (-(1 + K * alpha + |δ|) * L) =
        Real.exp (-(1 + K * alpha) * L) * Real.exp (-|δ * L|) := by
      rw [hdL, ← Real.exp_add]; ring_nf
    rw [e1, e2, e3, e4, ← mul_sub, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_exp_neg_sub_exp_eq]
  · rw [sq, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)

/-- The `p^{−2}`-weighted difference: `Σ (p^{−a} − p^{−b}) p^{−2} ≤ 2(b − a)` for `1 ≤ a ≤ b`. -/
theorem sum_exp_neg_sub_mul_le (P : Finset Nat.Primes) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ p ∈ P, (Real.exp (-a * Real.log p) - Real.exp (-b * Real.log p)) *
      Real.exp (-2 * Real.log p) ≤ 2 * (b - a) := by
  have hterm : ∀ p ∈ P, (Real.exp (-a * Real.log p) - Real.exp (-b * Real.log p)) *
      Real.exp (-2 * Real.log p) ≤ (b - a) * (Real.log p * Real.exp (-2 * Real.log p)) := by
    intro p _
    have hL0 : 0 < Real.log p := log_prime_pos p
    have h1 : Real.exp (-a * Real.log p) - Real.exp (-b * Real.log p) ≤
        (b - a) * Real.log p * Real.exp (-a * Real.log p) := by
      have h := Real.add_one_le_exp (-((b - a) * Real.log p))
      have he : Real.exp (-b * Real.log p) =
          Real.exp (-a * Real.log p) * Real.exp (-((b - a) * Real.log p)) := by
        rw [← Real.exp_add]; ring_nf
      rw [he]
      have := Real.exp_pos (-a * Real.log p)
      nlinarith
    have h2 : Real.exp (-a * Real.log p) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have h3 : 0 ≤ (b - a) * Real.log p := mul_nonneg (by linarith) hL0.le
    calc (Real.exp (-a * Real.log p) - Real.exp (-b * Real.log p)) * Real.exp (-2 * Real.log p)
        ≤ ((b - a) * Real.log p * Real.exp (-a * Real.log p)) * Real.exp (-2 * Real.log p) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ ((b - a) * Real.log p * 1) * Real.exp (-2 * Real.log p) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left h2 h3
      _ = (b - a) * (Real.log p * Real.exp (-2 * Real.log p)) := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have h := sum_log_mul_exp_neg_le P (s := 2) (by norm_num) le_rfl
  have h' : (1 : ℝ) / (2 - 1) + 1 = 2 := by norm_num
  rw [h'] at h
  have hba : 0 ≤ b - a := by linarith
  calc (b - a) * ∑ p ∈ P, Real.log p * Real.exp (-2 * Real.log p) ≤ (b - a) * 2 :=
        mul_le_mul_of_nonneg_left (by linarith) hba
    _ = 2 * (b - a) := by ring

/-- **JAS positivity at `1 + Kα` under a half-plane bound.** -/
theorem jasDressedPSD_one_add_mul_of_xiZeroHalfPlaneBound {K alpha : ℝ} (hK : 1 < K)
    (halpha : 0 < alpha) (hb : (K + 1) * alpha ≤ 1)
    (hbudget : Real.log ((K + 1) / (K - 1)) + (22 / 3 + 1 / 7) * alpha ≤ Real.pi / 2)
    (hXi : XiZeroHalfPlaneBound alpha) : JasDressedPSD (1 + K * alpha) := by
  have h := jasDressedPSD_of_phaseBudget (c := 1 / 2 + K * alpha) (by positivity) fun q P => by
    obtain ⟨d, hd⟩ : ∃ d, d = |(q.1 : ℂ).re - 1 / 2| := ⟨_, rfl⟩
    have hq := abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q
    rw [← hd] at hq
    have hd0 : 0 ≤ d := by rw [hd]; exact abs_nonneg _
    have harg := abs_arg_lagWeight_le_div_seven q
    rw [← hd] at harg
    have hw := Finset.sum_le_sum fun p (_ : p ∈ P) =>
      jasPhaseWidth_le_sharp (ρ := (q.1 : ℂ)) (alpha := alpha) (K := K)
        (by rw [← hd]; exact hq) hK.le p
    simp only [← hd] at hw
    simp only [mul_add, mul_one, Finset.sum_add_distrib] at hw
    have hKa : d < K * alpha := lt_of_le_of_lt hq (by nlinarith)
    have hs1 := sum_exp_neg_sub_exp_neg_le P (a := 1 + K * alpha - d) (b := 1 + K * alpha + d)
      (by linarith) (by linarith) (by nlinarith)
    have hs2 := sum_exp_neg_sub_mul_le P (a := 1 + K * alpha - d) (b := 1 + K * alpha + d)
      (by linarith) (by linarith)
    have hs2' : ∑ p ∈ P, (Real.exp (-(1 + K * alpha - d) * Real.log p) -
        Real.exp (-(1 + K * alpha + d) * Real.log p)) * (4 / 3 * Real.exp (-2 * Real.log p)) ≤
        4 / 3 * (2 * (1 + K * alpha + d - (1 + K * alpha - d))) := by
      have hrw : ∑ p ∈ P, (Real.exp (-(1 + K * alpha - d) * Real.log p) -
          Real.exp (-(1 + K * alpha + d) * Real.log p)) * (4 / 3 * Real.exp (-2 * Real.log p)) =
          4 / 3 * ∑ p ∈ P, (Real.exp (-(1 + K * alpha - d) * Real.log p) -
            Real.exp (-(1 + K * alpha + d) * Real.log p)) * Real.exp (-2 * Real.log p) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
      rw [hrw]
      exact mul_le_mul_of_nonneg_left hs2 (by norm_num)
    have hratio : (1 + K * alpha + d - 1) / (1 + K * alpha - d - 1) ≤ (K + 1) / (K - 1) := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    have hlog := Real.log_le_log (div_pos (by linarith) (by linarith)) hratio
    have hdα : d ≤ alpha := hq
    linarith
  have he : (1 / 2 + (1 / 2 + K * alpha) : ℝ) = 1 + K * alpha := by ring
  rwa [he] at h

/-- **The sharp constant.**  For every `K > 1` with `log((K + 1)/(K − 1)) < π/2` (that is,
`K > coth(π/4)`), all sufficiently small half-plane bounds `α` give positivity at `1 + Kα`. -/
theorem exists_jasDressedPSD_one_add_mul {K : ℝ} (hK : 1 < K)
    (hlog : Real.log ((K + 1) / (K - 1)) < Real.pi / 2) :
    ∃ alpha₀ : ℝ, 0 < alpha₀ ∧ ∀ alpha : ℝ, 0 < alpha → alpha ≤ alpha₀ →
      XiZeroHalfPlaneBound alpha → JasDressedPSD (1 + K * alpha) := by
  refine ⟨min (1 / (K + 1)) ((Real.pi / 2 - Real.log ((K + 1) / (K - 1))) / (22 / 3 + 1 / 7)),
    lt_min (by positivity) (div_pos (by linarith) (by norm_num)), fun alpha h0 h1 hXi => ?_⟩
  refine jasDressedPSD_one_add_mul_of_xiZeroHalfPlaneBound hK h0 ?_ ?_ hXi
  · have := h1.trans (min_le_left _ _)
    rw [le_div_iff₀ (by linarith)] at this
    linarith
  · have := h1.trans (min_le_right _ _)
    rw [le_div_iff₀ (by norm_num)] at this
    linarith

/-- `σ* ≤ 1 + (5/3)α` for every half-plane bound `0 < α ≤ 1/100`. -/
theorem jasAbscissa_le_one_add_five_thirds_mul {alpha : ℝ} (h0 : 0 < alpha) (h1 : alpha ≤ 1 / 100)
    (hXi : XiZeroHalfPlaneBound alpha) : jasAbscissa ≤ 1 + 5 / 3 * alpha := by
  refine jasDressedPSD_iff_jasAbscissa_le.mp
    (jasDressedPSD_one_add_mul_of_xiZeroHalfPlaneBound (by norm_num) h0 (by linarith) ?_ hXi)
  have h4 : Real.log ((5 / 3 + 1) / (5 / 3 - 1)) = 2 * Real.log 2 := by
    rw [show ((5 : ℝ) / 3 + 1) / (5 / 3 - 1) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [h4]
  have := Real.log_two_lt_d9
  have := Real.pi_gt_d2
  nlinarith

/-- **The sharp two-sided abscissa law.**  Off RH, under a half-plane bound `α < ½`, with
`0 < δ* = sup |Re ρ − ½| ≤ 1/100`: `1 + δ* ≤ σ* ≤ 1 + (5/3) δ*`. -/
theorem one_add_sSup_le_jasAbscissa_and_le_five_thirds {alpha : ℝ} (halpha0 : 0 ≤ alpha)
    (halpha : alpha < 1 / 2) (hXi : XiZeroHalfPlaneBound alpha) (hRH : ¬ RiemannHypothesis)
    (hsmall : sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) ≤ 1 / 100) :
    1 + sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) ≤ jasAbscissa ∧
      jasAbscissa ≤ 1 + 5 / 3 * sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) := by
  have hbdd : BddAbove (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    ⟨alpha, by rintro _ ⟨q, rfl⟩; exact abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q⟩
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  have hS0 : 0 < sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    lt_of_lt_of_le (abs_pos.mpr (by linarith)) (le_csSup hbdd ⟨q₀, rfl⟩)
  have hXiS : XiZeroHalfPlaneBound
      (sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|)) := by
    intro ρ hρ
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    have h := le_csSup hbdd ⟨q, rfl⟩
    simp only at h
    have := le_abs_self ((q.1 : ℂ).re - 1 / 2)
    linarith
  exact ⟨(one_add_sSup_le_jasAbscissa_and_le halpha0 halpha hXi hRH (by linarith)).1,
    jasAbscissa_le_one_add_five_thirds_mul hS0 hsmall hXiS⟩

end

end RHTower
