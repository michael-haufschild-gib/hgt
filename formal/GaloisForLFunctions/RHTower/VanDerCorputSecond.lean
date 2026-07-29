/-
The van der Corput second-derivative test — the stationary-phase bound for oscillatory integrals.

If a real phase `g` has second derivative `g'' ≥ λ > 0` throughout `[a,b]`, then the oscillatory
integral of `exp(i·g)` is bounded by `6/√λ`, independently of the length of the interval, even when
`g'` vanishes inside (a stationary point / saddle).  The first-derivative test cannot see this: near a
zero of `g'` its bound `2/|g'|` blows up.  The mechanism is a split at the stationary point: within a
window of length `≤ 2μ/λ` around it the trivial bound `‖∫‖ ≤ length` applies (since `g'' ≥ λ` forces
`g'` to grow at rate `λ`), and outside `|g'| ≥ μ` so the first-derivative bound
`norm_integral_cexp_ofReal_mul_I_le_mono/anti` applies; choosing `μ = √λ` balances the two at `3/√λ`
per side.

Layer: `norm_integral_cexp_secondDeriv_oneside` (`g' ≥ 0`, the near-stationary core) and its reflection
`_oneside_neg` (`g' ≤ 0`, via `x ↦ a+b-x`, which preserves `g'' ≥ λ` and flips the sign of `g'`) give
the one-sided bounds `3/√λ`; splitting a general phase at the zero of `g'` combines them into
`norm_integral_cexp_secondDeriv` at `6/√λ`.  This is the tool the reflected Dirichlet block of the
approximate functional equation requires — its Fourier phases `τ·log x ± 2πm·x` have a genuine saddle
at `x = τ/(2πm)` where the first-derivative test fails.
-/
import GaloisForLFunctions.RHTower.VanDerCorput

open Complex intervalIntegral MeasureTheory
open scoped Interval

noncomputable section

namespace RHTower


/-- The trivial length bound: `‖∫_a^b exp(i·g)‖ ≤ b - a`, since `‖exp(i·g)‖ = 1`. -/
theorem norm_integral_cexp_le_length {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ} :
    ‖∫ x in a..b, Complex.exp ((g x : ℂ) * I)‖ ≤ b - a := by
  calc ‖∫ x in a..b, Complex.exp ((g x : ℂ) * I)‖
      ≤ ∫ x in a..b, ‖Complex.exp ((g x : ℂ) * I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
    _ = ∫ _x in a..b, (1 : ℝ) := by
        apply intervalIntegral.integral_congr; intro x _; simp [Complex.norm_exp]
    _ = b - a := by simp

/-- Lower bound on the derivative gap from a second-derivative floor: if `g'' ≥ λ` on `[a,b]`
then `λ·(y − x) ≤ g'(y) − g'(x)` for `x ≤ y` in the interval (fundamental theorem of calculus
against the constant `λ`). -/
theorem deriv_lower_length {a b lam : ℝ} {g' g'' : ℝ → ℝ}
    (hg' : ∀ z ∈ Set.uIcc a b, HasDerivAt g' (g'' z) z)
    (hg''c : ContinuousOn g'' (Set.uIcc a b))
    (hlam : ∀ z ∈ Set.uIcc a b, lam ≤ g'' z)
    {x y : ℝ} (hx : x ∈ Set.uIcc a b) (hy : y ∈ Set.uIcc a b) (hxy : x ≤ y) :
    lam * (y - x) ≤ g' y - g' x := by
  have hsub : Set.uIcc x y ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc hx hy
  have hderiv : ∀ z ∈ Set.uIcc x y, HasDerivAt g' (g'' z) z := fun z hz => hg' z (hsub hz)
  have hint : IntervalIntegrable g'' volume x y := (hg''c.mono hsub).intervalIntegrable
  have hftc : ∫ z in x..y, g'' z = g' y - g' x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← hftc]
  have hcst : IntervalIntegrable (fun _ : ℝ => lam) volume x y :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hxy hcst hint
    (fun z hz => hlam z (hsub (by rw [Set.uIcc_of_le hxy]; exact hz)))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
  linarith [hmono]

/-- **Second-derivative test, nonnegative derivative.**  For `g'' ≥ λ > 0` and `g' ≥ 0` on `[a,b]`
(so the stationary point, if any, sits at the left endpoint), `‖∫_a^b exp(i·g)‖ ≤ 3/√λ`.  Split at the
point where `g' = √λ`: left of it `g'` is small so the interval is short (`≤ 1/√λ`), right of it
`g' ≥ √λ` so the first-derivative bound gives `2/√λ`. -/
theorem norm_integral_cexp_secondDeriv_oneside
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) {g g' g'' : ℝ → ℝ}
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc a b, HasDerivAt g' (g'' x) x)
    (hg''c : ContinuousOn g'' (Set.uIcc a b))
    (hg''lb : ∀ x ∈ Set.uIcc a b, lam ≤ g'' x)
    (hg'nn : ∀ x ∈ Set.uIcc a b, 0 ≤ g' x) :
    ‖∫ x in a..b, Complex.exp ((g x : ℂ) * I)‖ ≤ 3 / Real.sqrt lam := by
  set μ := Real.sqrt lam with hμdef
  have hμpos : 0 < μ := Real.sqrt_pos.mpr hlam
  have hμ2 : μ * μ = lam := Real.mul_self_sqrt hlam.le
  have hg''nn : ∀ x ∈ Set.uIcc a b, 0 ≤ g'' x := fun x hx => le_trans hlam.le (hg''lb x hx)
  have hg'c : ContinuousOn g' (Set.uIcc a b) := fun x hx => (hg' x hx).continuousAt.continuousWithinAt
  have haU : a ∈ Set.uIcc a b := Set.left_mem_uIcc
  have hbU : b ∈ Set.uIcc a b := Set.right_mem_uIcc
  by_cases hcase1 : g' b ≤ μ
  · -- Case 1: trivial bound
    have hlen := deriv_lower_length hg' hg''c hg''lb haU hbU hab
    have hla : lam * (b - a) ≤ μ := by linarith [hg'nn a haU]
    have hN := norm_integral_cexp_le_length (a := a) (b := b) hab (g := g)
    rw [le_div_iff₀ hμpos]
    nlinarith [hN, hla, hμ2, hμpos, norm_nonneg (∫ x in a..b, Complex.exp ((g x : ℂ) * I))]
  · -- Case 2: μ < g' b
    rw [not_le] at hcase1
    have hgc : ContinuousOn g (Set.uIcc a b) :=
      fun x hx => (hg x hx).continuousAt.continuousWithinAt
    have hIcont : ContinuousOn (fun x => Complex.exp ((g x : ℂ) * I)) (Set.uIcc a b) :=
      Complex.continuous_exp.comp_continuousOn
        ((Complex.continuous_ofReal.comp_continuousOn hgc).mul continuousOn_const)
    have hInt : ∀ u v, u ∈ Set.uIcc a b → v ∈ Set.uIcc a b →
        IntervalIntegrable (fun x => Complex.exp ((g x : ℂ) * I)) volume u v :=
      fun u v hu hv => (hIcont.mono (Set.uIcc_subset_uIcc hu hv)).intervalIntegrable
    by_cases hcase2a : μ ≤ g' a
    · -- 2a: g' ≥ μ everywhere
      have hpos : ∀ x ∈ Set.uIcc a b, μ ≤ g' x := by
        intro x hx
        have hxIcc : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at hx
        have hlen := deriv_lower_length hg' hg''c hg''lb haU hx hxIcc.1
        nlinarith [hlen, hcase2a, mul_nonneg hlam.le (by linarith [hxIcc.1] : (0:ℝ) ≤ x - a)]
      have hm := norm_integral_cexp_ofReal_mul_I_le_mono hab hμpos hg hg' hg''c hpos hg''nn
      calc ‖∫ x in a..b, Complex.exp ((g x : ℂ) * I)‖ ≤ 2 / μ := hm
        _ ≤ 3 / μ := by
            have h1 : (0:ℝ) ≤ 1 / μ := le_of_lt (div_pos one_pos hμpos)
            have h3 : (3:ℝ) / μ = 2 / μ + 1 / μ := by ring
            linarith [h1, h3]
    · -- 2b: g' a < μ < g' b, IVT split
      rw [not_le] at hcase2a
      have hmem : μ ∈ Set.Icc (g' a) (g' b) := ⟨hcase2a.le, hcase1.le⟩
      have hg'cIcc : ContinuousOn g' (Set.Icc a b) := by rw [← Set.uIcc_of_le hab]; exact hg'c
      obtain ⟨q, hq, hgq⟩ := intermediate_value_Icc hab hg'cIcc hmem
      have hqU : q ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact hq
      have haq : a ≤ q := hq.1
      have hqb : q ≤ b := hq.2
      have hsplit : (∫ x in a..b, Complex.exp ((g x : ℂ) * I))
          = (∫ x in a..q, Complex.exp ((g x : ℂ) * I))
            + ∫ x in q..b, Complex.exp ((g x : ℂ) * I) :=
        (intervalIntegral.integral_add_adjacent_intervals (hInt a q haU hqU) (hInt q b hqU hbU)).symm
      have hAQ : ‖∫ x in a..q, Complex.exp ((g x : ℂ) * I)‖ ≤ 1 / μ := by
        have hlen := deriv_lower_length hg' hg''c hg''lb haU hqU haq
        rw [hgq] at hlen
        have hla : lam * (q - a) ≤ μ := by linarith [hg'nn a haU]
        have hN := norm_integral_cexp_le_length (a := a) (b := q) haq (g := g)
        rw [le_div_iff₀ hμpos]
        nlinarith [hN, hla, hμ2, hμpos, norm_nonneg (∫ x in a..q, Complex.exp ((g x : ℂ) * I))]
      have hQB : ‖∫ x in q..b, Complex.exp ((g x : ℂ) * I)‖ ≤ 2 / μ := by
        have hsubqb : Set.uIcc q b ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc hqU hbU
        have hposqb : ∀ x ∈ Set.uIcc q b, μ ≤ g' x := by
          intro x hx
          have hxIcc : x ∈ Set.Icc q b := by rwa [Set.uIcc_of_le hqb] at hx
          have hlen := deriv_lower_length hg' hg''c hg''lb hqU (hsubqb hx) hxIcc.1
          rw [hgq] at hlen
          nlinarith [hlen, mul_nonneg hlam.le (by linarith [hxIcc.1] : (0:ℝ) ≤ x - q)]
        exact norm_integral_cexp_ofReal_mul_I_le_mono hqb hμpos
          (fun x hx => hg x (hsubqb hx)) (fun x hx => hg' x (hsubqb hx))
          (hg''c.mono hsubqb) hposqb (fun x hx => hg''nn x (hsubqb hx))
      rw [hsplit]
      calc ‖(∫ x in a..q, Complex.exp ((g x : ℂ) * I))
              + ∫ x in q..b, Complex.exp ((g x : ℂ) * I)‖
          ≤ ‖∫ x in a..q, Complex.exp ((g x : ℂ) * I)‖
              + ‖∫ x in q..b, Complex.exp ((g x : ℂ) * I)‖ := norm_add_le _ _
        _ ≤ 1 / μ + 2 / μ := add_le_add hAQ hQB
        _ = 3 / μ := by ring

/-- **Second-derivative test, nonpositive derivative.**  The reflection `x ↦ a+b-x` sends this to the
nonnegative case (it preserves `g'' ≥ λ` and negates `g'`), so again `‖∫_a^b exp(i·g)‖ ≤ 3/√λ`. -/
theorem norm_integral_cexp_secondDeriv_oneside_neg
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) {g g' g'' : ℝ → ℝ}
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc a b, HasDerivAt g' (g'' x) x)
    (hg''c : ContinuousOn g'' (Set.uIcc a b))
    (hg''lb : ∀ x ∈ Set.uIcc a b, lam ≤ g'' x)
    (hg'np : ∀ x ∈ Set.uIcc a b, g' x ≤ 0) :
    ‖∫ x in a..b, Complex.exp ((g x : ℂ) * I)‖ ≤ 3 / Real.sqrt lam := by
  have hrefl_mem : ∀ y ∈ Set.uIcc a b, a + b - y ∈ Set.uIcc a b := by
    intro y hy; rw [Set.uIcc_of_le hab] at hy ⊢; exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hderiv_in : ∀ y : ℝ, HasDerivAt (fun z : ℝ => a + b - z) (-1) y :=
    fun y => by simpa using (hasDerivAt_id y).const_sub (a + b)
  set h : ℝ → ℝ := fun y => g (a + b - y) with hh
  set h' : ℝ → ℝ := fun y => -(g' (a + b - y)) with hh'
  set h'' : ℝ → ℝ := fun y => g'' (a + b - y) with hh''
  have hgh : ∀ y ∈ Set.uIcc a b, HasDerivAt h (h' y) y := by
    intro y hy
    have := (hg (a + b - y) (hrefl_mem y hy)).comp y (hderiv_in y)
    simpa [hh, hh', mul_comm] using this
  have hg'h : ∀ y ∈ Set.uIcc a b, HasDerivAt h' (h'' y) y := by
    intro y hy
    have hc := ((hg' (a + b - y) (hrefl_mem y hy)).comp y (hderiv_in y)).neg
    simpa [hh', hh'', mul_comm] using hc
  have hh''c : ContinuousOn h'' (Set.uIcc a b) :=
    hg''c.comp ((continuous_const.sub continuous_id).continuousOn) (fun y hy => hrefl_mem y hy)
  have hh''lb : ∀ y ∈ Set.uIcc a b, lam ≤ h'' y := fun y hy => hg''lb _ (hrefl_mem y hy)
  have hh'nn : ∀ y ∈ Set.uIcc a b, 0 ≤ h' y := by
    intro y hy; rw [hh']; linarith [hg'np _ (hrefl_mem y hy)]
  have hpos := norm_integral_cexp_secondDeriv_oneside hab hlam hgh hg'h hh''c hh''lb hh'nn
  have hEq : (∫ x in a..b, Complex.exp ((h x : ℂ) * I))
      = ∫ x in a..b, Complex.exp ((g x : ℂ) * I) := by
    have h2 := intervalIntegral.integral_comp_sub_left
      (f := fun x => Complex.exp ((g x : ℂ) * I)) (a := a) (b := b) (a + b)
    simpa [hh] using h2
  rw [← hEq]; exact hpos

/-- **The van der Corput second-derivative test.**  For any real phase with `g'' ≥ λ > 0` on `[a,b]`,
`‖∫_a^b exp(i·g)‖ ≤ 6/√λ`, uniformly in the length.  Split at the zero of `g'` (which exists and is
unique when `g'` changes sign, by monotonicity) into a nonpositive-derivative and a nonnegative-derivative
piece, each bounded by `3/√λ`.  This is the estimate that survives a stationary point. -/
theorem norm_integral_cexp_secondDeriv
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) {g g' g'' : ℝ → ℝ}
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc a b, HasDerivAt g' (g'' x) x)
    (hg''c : ContinuousOn g'' (Set.uIcc a b))
    (hg''lb : ∀ x ∈ Set.uIcc a b, lam ≤ g'' x) :
    ‖∫ x in a..b, Complex.exp ((g x : ℂ) * I)‖ ≤ 6 / Real.sqrt lam := by
  have hμpos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have haU : a ∈ Set.uIcc a b := Set.left_mem_uIcc
  have hbU : b ∈ Set.uIcc a b := Set.right_mem_uIcc
  have hg'c : ContinuousOn g' (Set.uIcc a b) :=
    fun x hx => (hg' x hx).continuousAt.continuousWithinAt
  have h36 : (3:ℝ) / Real.sqrt lam ≤ 6 / Real.sqrt lam := by
    have : (0:ℝ) ≤ 3 / Real.sqrt lam := le_of_lt (div_pos (by norm_num) hμpos)
    have he : (6:ℝ) / Real.sqrt lam = 3 / Real.sqrt lam + 3 / Real.sqrt lam := by ring
    linarith
  by_cases hca : 0 ≤ g' a
  · have hnn : ∀ x ∈ Set.uIcc a b, 0 ≤ g' x := by
      intro x hx
      have hxIcc : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at hx
      have hlen := deriv_lower_length hg' hg''c hg''lb haU hx hxIcc.1
      nlinarith [hlen, hca, mul_nonneg hlam.le (by linarith [hxIcc.1] : (0:ℝ) ≤ x - a)]
    exact le_trans (norm_integral_cexp_secondDeriv_oneside hab hlam hg hg' hg''c hg''lb hnn) h36
  · rw [not_le] at hca
    by_cases hcb : g' b ≤ 0
    · have hnp : ∀ x ∈ Set.uIcc a b, g' x ≤ 0 := by
        intro x hx
        have hxIcc : x ∈ Set.Icc a b := by rwa [Set.uIcc_of_le hab] at hx
        have hlen := deriv_lower_length hg' hg''c hg''lb hx hbU hxIcc.2
        nlinarith [hlen, hcb, mul_nonneg hlam.le (by linarith [hxIcc.2] : (0:ℝ) ≤ b - x)]
      exact le_trans (norm_integral_cexp_secondDeriv_oneside_neg hab hlam hg hg' hg''c hg''lb hnp) h36
    · rw [not_le] at hcb
      have hmem : (0:ℝ) ∈ Set.Icc (g' a) (g' b) := ⟨hca.le, hcb.le⟩
      have hg'cIcc : ContinuousOn g' (Set.Icc a b) := by rw [← Set.uIcc_of_le hab]; exact hg'c
      obtain ⟨c, hc, hgc⟩ := intermediate_value_Icc hab hg'cIcc hmem
      have hcU : c ∈ Set.uIcc a b := by rw [Set.uIcc_of_le hab]; exact hc
      have hac : a ≤ c := hc.1
      have hcb2 : c ≤ b := hc.2
      have hgc0 : g' c = 0 := hgc
      have hgcont : ContinuousOn g (Set.uIcc a b) :=
        fun x hx => (hg x hx).continuousAt.continuousWithinAt
      have hIcont : ContinuousOn (fun x => Complex.exp ((g x : ℂ) * I)) (Set.uIcc a b) :=
        Complex.continuous_exp.comp_continuousOn
          ((Complex.continuous_ofReal.comp_continuousOn hgcont).mul continuousOn_const)
      have hInt : ∀ u v, u ∈ Set.uIcc a b → v ∈ Set.uIcc a b →
          IntervalIntegrable (fun x => Complex.exp ((g x : ℂ) * I)) volume u v :=
        fun u v hu hv => (hIcont.mono (Set.uIcc_subset_uIcc hu hv)).intervalIntegrable
      have hsplit : (∫ x in a..b, Complex.exp ((g x : ℂ) * I))
          = (∫ x in a..c, Complex.exp ((g x : ℂ) * I))
            + ∫ x in c..b, Complex.exp ((g x : ℂ) * I) :=
        (intervalIntegral.integral_add_adjacent_intervals (hInt a c haU hcU) (hInt c b hcU hbU)).symm
      have hsubac : Set.uIcc a c ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc haU hcU
      have hsubcb : Set.uIcc c b ⊆ Set.uIcc a b := Set.uIcc_subset_uIcc hcU hbU
      have hAC : ‖∫ x in a..c, Complex.exp ((g x : ℂ) * I)‖ ≤ 3 / Real.sqrt lam := by
        have hnp : ∀ x ∈ Set.uIcc a c, g' x ≤ 0 := by
          intro x hx
          have hxIcc : x ∈ Set.Icc a c := by rwa [Set.uIcc_of_le hac] at hx
          have hlen := deriv_lower_length hg' hg''c hg''lb (hsubac hx) hcU hxIcc.2
          rw [hgc0] at hlen
          nlinarith [hlen, mul_nonneg hlam.le (by linarith [hxIcc.2] : (0:ℝ) ≤ c - x)]
        exact norm_integral_cexp_secondDeriv_oneside_neg hac hlam
          (fun x hx => hg x (hsubac hx)) (fun x hx => hg' x (hsubac hx))
          (hg''c.mono hsubac) (fun x hx => hg''lb x (hsubac hx)) hnp
      have hCB : ‖∫ x in c..b, Complex.exp ((g x : ℂ) * I)‖ ≤ 3 / Real.sqrt lam := by
        have hnn : ∀ x ∈ Set.uIcc c b, 0 ≤ g' x := by
          intro x hx
          have hxIcc : x ∈ Set.Icc c b := by rwa [Set.uIcc_of_le hcb2] at hx
          have hlen := deriv_lower_length hg' hg''c hg''lb hcU (hsubcb hx) hxIcc.1
          rw [hgc0] at hlen
          nlinarith [hlen, mul_nonneg hlam.le (by linarith [hxIcc.1] : (0:ℝ) ≤ x - c)]
        exact norm_integral_cexp_secondDeriv_oneside hcb2 hlam
          (fun x hx => hg x (hsubcb hx)) (fun x hx => hg' x (hsubcb hx))
          (hg''c.mono hsubcb) (fun x hx => hg''lb x (hsubcb hx)) hnn
      rw [hsplit]
      calc ‖(∫ x in a..c, Complex.exp ((g x : ℂ) * I))
              + ∫ x in c..b, Complex.exp ((g x : ℂ) * I)‖
          ≤ ‖∫ x in a..c, Complex.exp ((g x : ℂ) * I)‖
              + ‖∫ x in c..b, Complex.exp ((g x : ℂ) * I)‖ := norm_add_le _ _
        _ ≤ 3 / Real.sqrt lam + 3 / Real.sqrt lam := add_le_add hAC hCB
        _ = 6 / Real.sqrt lam := by ring

/-- Conjugation preserves the modulus of an oscillatory integral: `‖∫ exp(i·(−g))‖ = ‖∫ exp(i·g)‖`,
since `exp(i·(−g)) = conj (exp(i·g))` and conjugation commutes with the integral and preserves norm. -/
theorem norm_integral_cexp_neg_phase {a b : ℝ} {g : ℝ → ℝ}
    (hint : IntervalIntegrable (fun x => Complex.exp ((g x : ℂ) * I)) volume a b) :
    ‖∫ x in a..b, Complex.exp ((-(g x) : ℝ) * I)‖
      = ‖∫ x in a..b, Complex.exp ((g x : ℂ) * I)‖ := by
  have hstep : (∫ x in a..b, Complex.exp ((-(g x) : ℝ) * I))
      = (starRingEnd ℂ) (∫ x in a..b, Complex.exp ((g x : ℂ) * I)) := by
    have hconj : (∫ x in a..b, (starRingEnd ℂ) (Complex.exp ((g x : ℂ) * I)))
        = (starRingEnd ℂ) (∫ x in a..b, Complex.exp ((g x : ℂ) * I)) := by
      have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm hint
      simpa only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply] using h
    calc (∫ x in a..b, Complex.exp ((-(g x) : ℝ) * I))
        = ∫ x in a..b, (starRingEnd ℂ) (Complex.exp ((g x : ℂ) * I)) := by
          apply intervalIntegral.integral_congr
          intro x _
          show Complex.exp ((-(g x) : ℝ) * I) = (starRingEnd ℂ) (Complex.exp ((g x : ℂ) * I))
          rw [← Complex.exp_conj]
          congr 1
          simp [Complex.conj_I]
      _ = (starRingEnd ℂ) (∫ x in a..b, Complex.exp ((g x : ℂ) * I)) := hconj
  rw [hstep, Complex.norm_conj]

/-- **The van der Corput second-derivative test, concave phase.**  For `g'' ≤ −λ < 0` on `[a,b]`
(a maximum of `g'` rather than a minimum), `‖∫_a^b exp(i·g)‖ ≤ 6/√λ`.  Immediate from
`norm_integral_cexp_secondDeriv` applied to `−g` (whose second derivative is `−g'' ≥ λ`) via the
conjugation identity `norm_integral_cexp_neg_phase`.  This is the sign the reflected-block Fourier
mode `τ·log x − 2πm·x` carries (`g'' = −τ/x²`). -/
theorem norm_integral_cexp_secondDeriv_neg
    {a b lam : ℝ} (hab : a ≤ b) (hlam : 0 < lam) {g g' g'' : ℝ → ℝ}
    (hg : ∀ x ∈ Set.uIcc a b, HasDerivAt g (g' x) x)
    (hg' : ∀ x ∈ Set.uIcc a b, HasDerivAt g' (g'' x) x)
    (hg''c : ContinuousOn g'' (Set.uIcc a b))
    (hg''ub : ∀ x ∈ Set.uIcc a b, g'' x ≤ -lam) :
    ‖∫ x in a..b, Complex.exp ((g x : ℂ) * I)‖ ≤ 6 / Real.sqrt lam := by
  have hgc : ContinuousOn g (Set.uIcc a b) :=
    fun x hx => (hg x hx).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun x => Complex.exp ((g x : ℂ) * I)) volume a b :=
    (Complex.continuous_exp.comp_continuousOn
      ((Complex.continuous_ofReal.comp_continuousOn hgc).mul continuousOn_const)).intervalIntegrable
  rw [← norm_integral_cexp_neg_phase hint]
  exact norm_integral_cexp_secondDeriv hab hlam
    (fun x hx => (hg x hx).neg) (fun x hx => (hg' x hx).neg) hg''c.neg
    (fun x hx => by linarith [hg''ub x hx])

end RHTower
