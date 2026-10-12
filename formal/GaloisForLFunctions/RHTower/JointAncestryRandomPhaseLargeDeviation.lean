import GaloisForLFunctions.RHTower.JointAncestryDyadicPhaseCapstone

/-!
# The exceptional phase set is polynomially small

On a set `P` of primes in `(y, 2y]`, JAS positivity at level one fails on a proportion of phase
vectors `k : P → ℤ/N` (`z_p = r ω^{k_p}`, `N ≥ 3`) that is at most `C y^{−c}` with absolute
constants `C, c > 0`, under no hypothesis on the zeros
(`exists_card_jasPhaseAggregate_re_neg_le_dyadic_rpow`).  This sharpens the second-moment bound
`O(1/log y)` of `JointAncestryDyadicPhaseCapstone` to a power of `y`.

Proof.  For a zero `ρ` write the product as `∏_p(1 + u_p)`, `u_p = a(ω^{k_p}A_p + ω^{−k_p}B_p)`,
with `|u_p| ≤ 2a p^{−½} ≤ ½`.  Then `|∏(1 + u_p) − 1| ≤ (|S| + V)e^{|S|+V}`, where `S = Σ_p u_p` and
`V = Σ_p 4a²/p`.
* **Hoeffding.**  Each real part `Re(c·u_p)`, `|c| = 1`, has phase mean zero and size at most
  `M_p ≤ 2a p^{−½}`.  The chord bound for `exp` gives `E e^{μX} ≤ cosh μM ≤ e^{μ²M²/2}`, and
  independence over the primes gives `E e^{μ|S|} ≤ 2e^{2μ²V}`.
* **Splitting the zeros.**  Zeros with `|S| ≤ t₀` contribute at most `Φ(0)/2` in total.  The rest
  are counted through `e^{μ|S| − λt₀}`, `μ = 2 + λ`, and Markov's inequality over the phases gives
  `#bad ≤ N^{|P|}(4W/Φ(0))e^{2V − λt₀ + 2μ²V}`.
* With `V ≤ 2 log 4/log y` (Chebyshev) and `λ = t₀/(16V)`, the exponent is
  `≤ 2V − t₀²/(32V) ≤ 1 − c log y`.
-/

open Complex Filter
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Hoeffding's lemma on a finite phase space -/

/-- **Hoeffding.**  A real function on `ℤ/N` with mean zero and `|X| ≤ M` satisfies
`Σ_j e^{μX_j} ≤ N e^{μ²M²/2}`. -/
theorem sum_exp_le_of_mean_zero {N : ℕ} (X : Fin N → ℝ) (hX0 : ∑ j, X j = 0) {M : ℝ}
    (hXM : ∀ j, |X j| ≤ M) (μ : ℝ) :
    ∑ j, Real.exp (μ * X j) ≤ N * Real.exp (μ ^ 2 * M ^ 2 / 2) := by
  by_cases hM : 0 < M
  · -- chord bound
    have hchord : ∀ j, Real.exp (μ * X j) ≤
        (1 - (M + X j) / (2 * M)) * Real.exp (-(μ * M)) +
          (M + X j) / (2 * M) * Real.exp (μ * M) := by
      intro j
      have hj := abs_le.mp (hXM j)
      have ht0 : 0 ≤ (M + X j) / (2 * M) := div_nonneg (by linarith) (by linarith)
      have ht1 : 0 ≤ 1 - (M + X j) / (2 * M) := by
        rw [sub_nonneg, div_le_one (by linarith)]; linarith
      have hc := convexOn_exp.2 (Set.mem_univ (-(μ * M))) (Set.mem_univ (μ * M)) ht1 ht0
        (by ring)
      simp only [smul_eq_mul] at hc
      refine le_trans (le_of_eq ?_) hc
      congr 1
      field_simp
      ring
    refine (Finset.sum_le_sum fun j _ => hchord j).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_sub_distrib,
      ← Finset.sum_div, Finset.sum_add_distrib, hX0]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      add_zero]
    have hcosh := Real.cosh_le_exp_half_sq (μ * M)
    rw [Real.cosh_eq] at hcosh
    have e : ((N : ℝ) - N * M / (2 * M)) * Real.exp (-(μ * M)) +
        N * M / (2 * M) * Real.exp (μ * M) =
        N * ((Real.exp (μ * M) + Real.exp (-(μ * M))) / 2) := by
      field_simp; ring
    rw [e, show μ ^ 2 * M ^ 2 / 2 = (μ * M) ^ 2 / 2 by ring]
    exact mul_le_mul_of_nonneg_left hcosh (Nat.cast_nonneg _)
  · -- `M ≤ 0`: `X = 0`
    push Not at hM
    have hX : ∀ j, X j = 0 := fun j => abs_nonpos_iff.mp ((hXM j).trans hM)
    simp only [hX, mul_zero, Real.exp_zero, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_exp (by positivity))

/-! ## The phase linear terms -/

/-- The linear phase term `a(ω^j X + ω^{−j} Y)`. -/
def jasPhaseLinear (N : ℕ) (a : ℝ) (X Y : ℂ) (j : Fin N) : ℂ :=
  (a : ℂ) * (unitRoot N ^ (j : ℕ) * X + conj (unitRoot N ^ (j : ℕ)) * Y)

theorem phaseFactor_eq_one_add (N : ℕ) (a : ℝ) (X Y : ℂ) (j : Fin N) :
    phaseFactor N a X Y j = 1 + jasPhaseLinear N a X Y j := rfl

theorem sum_jasPhaseLinear {N : ℕ} (hN : 3 ≤ N) (a : ℝ) (X Y : ℂ) :
    ∑ j : Fin N, jasPhaseLinear N a X Y j = 0 := by
  have h := sum_phaseFactor hN a X Y
  simp only [phaseFactor_eq_one_add, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h
  linear_combination h

theorem norm_jasPhaseLinear_le {N : ℕ} {a : ℝ} (ha : 0 ≤ a) (X Y : ℂ) (j : Fin N) :
    ‖jasPhaseLinear N a X Y j‖ ≤ a * (‖X‖ + ‖Y‖) := by
  unfold jasPhaseLinear
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) ha
  rw [norm_mul, norm_mul, Complex.norm_conj, norm_unitRoot_pow, one_mul, one_mul]

/-- **Chernoff over the phases** in a unit direction `c`. -/
theorem sum_exp_re_mul_sum_le {N : ℕ} (hN : 3 ≤ N) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a : ℝ} (ha : 0 ≤ a) (X Y : ι → ℂ) {c : ℂ} (hc : ‖c‖ = 1) (μ : ℝ) :
    ∑ k : ι → Fin N, Real.exp (μ * (c * ∑ i, jasPhaseLinear N a (X i) (Y i) (k i)).re) ≤
      (N : ℝ) ^ Fintype.card ι *
        Real.exp (μ ^ 2 * (∑ i, (a * (‖X i‖ + ‖Y i‖)) ^ 2) / 2) := by
  have hfac : ∀ k : ι → Fin N, Real.exp (μ * (c * ∑ i, jasPhaseLinear N a (X i) (Y i) (k i)).re) =
      ∏ i, Real.exp (μ * (c * jasPhaseLinear N a (X i) (Y i) (k i)).re) := by
    intro k
    rw [← Real.exp_sum, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
  simp_rw [hfac]
  rw [← Fintype.prod_sum (fun i j => Real.exp (μ * (c * jasPhaseLinear N a (X i) (Y i) j).re))]
  have hone : ∀ i, ∑ j : Fin N, Real.exp (μ * (c * jasPhaseLinear N a (X i) (Y i) j).re) ≤
      N * Real.exp (μ ^ 2 * (a * (‖X i‖ + ‖Y i‖)) ^ 2 / 2) := by
    intro i
    refine sum_exp_le_of_mean_zero (fun j => (c * jasPhaseLinear N a (X i) (Y i) j).re) ?_ ?_ μ
    · rw [← Complex.re_sum, ← Finset.mul_sum, sum_jasPhaseLinear hN, mul_zero, Complex.zero_re]
    · intro j
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, hc, one_mul]
      exact norm_jasPhaseLinear_le ha _ _ j
  calc ∏ i, ∑ j : Fin N, Real.exp (μ * (c * jasPhaseLinear N a (X i) (Y i) j).re)
      ≤ ∏ i, ((N : ℝ) * Real.exp (μ ^ 2 * (a * (‖X i‖ + ‖Y i‖)) ^ 2 / 2)) :=
        Finset.prod_le_prod (fun i _ => Finset.sum_nonneg fun j _ => (Real.exp_pos _).le)
          fun i _ => hone i
    _ = (N : ℝ) ^ Fintype.card ι * Real.exp (μ ^ 2 * (∑ i, (a * (‖X i‖ + ‖Y i‖)) ^ 2) / 2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
        congr 2
        rw [Finset.mul_sum, Finset.sum_div]

/-- **The exponential moment of the modulus.** -/
theorem sum_exp_norm_sum_le {N : ℕ} (hN : 3 ≤ N) {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a : ℝ} (ha : 0 ≤ a) (X Y : ι → ℂ) {μ : ℝ} (hμ : 0 ≤ μ) :
    ∑ k : ι → Fin N, Real.exp (μ * ‖∑ i, jasPhaseLinear N a (X i) (Y i) (k i)‖) ≤
      2 * (N : ℝ) ^ Fintype.card ι *
        Real.exp (2 * μ ^ 2 * ∑ i, (a * (‖X i‖ + ‖Y i‖)) ^ 2) := by
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = ∑ i, (a * (‖X i‖ + ‖Y i‖)) ^ 2 := ⟨_, rfl⟩
  rw [← hVdef]
  have hpt : ∀ z : ℂ, Real.exp (μ * ‖z‖) ≤ (Real.exp (2 * μ * (1 * z).re) +
      Real.exp (2 * μ * ((-1) * z).re) + Real.exp (2 * μ * ((-I) * z).re) +
      Real.exp (2 * μ * (I * z).re)) / 2 := by
    intro z
    have h1 : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
    have hre : Real.exp (2 * μ * |z.re|) ≤ Real.exp (2 * μ * (1 * z).re) +
        Real.exp (2 * μ * ((-1) * z).re) := by
      simp only [one_mul, neg_mul, Complex.neg_re]
      rcases le_total 0 z.re with h | h
      · rw [abs_of_nonneg h]; linarith [Real.exp_pos (2 * μ * -z.re)]
      · rw [abs_of_nonpos h]; nlinarith [Real.exp_pos (2 * μ * z.re)]
    have him : Real.exp (2 * μ * |z.im|) ≤ Real.exp (2 * μ * ((-I) * z).re) +
        Real.exp (2 * μ * (I * z).re) := by
      have e1 : ((-I) * z).re = z.im := by simp
      have e2 : (I * z).re = -z.im := by simp
      rw [e1, e2]
      rcases le_total 0 z.im with h | h
      · rw [abs_of_nonneg h]; linarith [Real.exp_pos (2 * μ * -z.im)]
      · rw [abs_of_nonpos h]; nlinarith [Real.exp_pos (2 * μ * z.im)]
    have hamgm : Real.exp (μ * (|z.re| + |z.im|)) ≤
        (Real.exp (2 * μ * |z.re|) + Real.exp (2 * μ * |z.im|)) / 2 := by
      have e : Real.exp (μ * (|z.re| + |z.im|)) =
          Real.exp (μ * |z.re|) * Real.exp (μ * |z.im|) := by rw [← Real.exp_add]; ring_nf
      have e1 : Real.exp (2 * μ * |z.re|) = Real.exp (μ * |z.re|) ^ 2 := by
        rw [← Real.exp_nat_mul]; ring_nf
      have e2 : Real.exp (2 * μ * |z.im|) = Real.exp (μ * |z.im|) ^ 2 := by
        rw [← Real.exp_nat_mul]; ring_nf
      rw [e, e1, e2]
      nlinarith [sq_nonneg (Real.exp (μ * |z.re|) - Real.exp (μ * |z.im|))]
    calc Real.exp (μ * ‖z‖) ≤ Real.exp (μ * (|z.re| + |z.im|)) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h1 hμ)
      _ ≤ _ := hamgm
      _ ≤ _ := by linarith
  have hc : ∀ c : ℂ, ‖c‖ = 1 → ∑ k : ι → Fin N,
      Real.exp (2 * μ * (c * ∑ i, jasPhaseLinear N a (X i) (Y i) (k i)).re) ≤
        (N : ℝ) ^ Fintype.card ι * Real.exp (2 * μ ^ 2 * V) := by
    intro c hc
    refine (sum_exp_re_mul_sum_le hN ha X Y hc (2 * μ)).trans (le_of_eq ?_)
    rw [hVdef, show (2 * μ) ^ 2 * (∑ i, (a * (‖X i‖ + ‖Y i‖)) ^ 2) / 2 =
      2 * μ ^ 2 * ∑ i, (a * (‖X i‖ + ‖Y i‖)) ^ 2 by ring]
  refine (Finset.sum_le_sum fun k _ => hpt _).trans ?_
  rw [← Finset.sum_div]
  simp only [Finset.sum_add_distrib]
  have h1 := hc 1 (by simp)
  have h2 := hc (-1) (by simp)
  have h3 := hc (-I) (by simp)
  have h4 := hc I (by simp)
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  linarith

/-! ## Products near one -/

/-- `|∏(1 + u_i) − 1| ≤ (|Σu_i| + Σ|u_i|²) e^{|Σu_i| + Σ|u_i|²}` when every `|u_i| ≤ ½`. -/
theorem norm_prod_one_add_sub_one_le_of_half {ι : Type*} (s : Finset ι) (u : ι → ℂ)
    (hu : ∀ i ∈ s, ‖u i‖ ≤ 1 / 2) :
    ‖(∏ i ∈ s, (1 + u i)) - 1‖ ≤ (‖∑ i ∈ s, u i‖ + ∑ i ∈ s, ‖u i‖ ^ 2) *
      Real.exp (‖∑ i ∈ s, u i‖ + ∑ i ∈ s, ‖u i‖ ^ 2) := by
  have hne : ∀ i ∈ s, (1 + u i) ≠ 0 := fun i hi h => by
    have : ‖u i‖ = 1 := by
      rw [show u i = -1 by linear_combination h]; simp
    linarith [hu i hi]
  have hprod : ∏ i ∈ s, (1 + u i) = Complex.exp (∑ i ∈ s, Complex.log (1 + u i)) := by
    rw [Complex.exp_sum]
    exact Finset.prod_congr rfl fun i hi => (Complex.exp_log (hne i hi)).symm
  have hlog : ‖∑ i ∈ s, Complex.log (1 + u i)‖ ≤ ‖∑ i ∈ s, u i‖ + ∑ i ∈ s, ‖u i‖ ^ 2 := by
    have e : ∑ i ∈ s, Complex.log (1 + u i) =
        ∑ i ∈ s, u i + ∑ i ∈ s, (Complex.log (1 + u i) - u i) := by
      rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
    have h1 := hu i hi
    have h2 := Complex.norm_log_one_add_sub_self_le (show ‖u i‖ < 1 by linarith)
    refine h2.trans ?_
    have h3 : (1 - ‖u i‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h4 := sq_nonneg ‖u i‖
    nlinarith
  rw [hprod]
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (∑ i ∈ s, Complex.log (1 + u i)) 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one, pow_one] at h
  refine h.trans ?_
  exact mul_le_mul hlog (Real.exp_le_exp.mpr hlog) (Real.exp_pos _).le
    (by positivity)

/-! ## The large-deviation count -/

/-- **Large-deviation count at level one.**  For a set `P` of primes `p ≥ 4`, any
`V ≥ Σ_P 4a²/p`, any `t₀ ≥ 0` with `(t₀ + V)e^{t₀+V} ≤ Φ(0)/(2W)` and any `λ ≥ 0`, the number of
phase vectors with a negative aggregate is at most `N^{|P|}(4W/Φ(0)) e^{2V − λt₀ + 2(2+λ)²V}`. -/
theorem card_jasPhaseAggregate_re_neg_le_exp {r : ℝ} (hr : 0 ≤ r) {N : ℕ} (hN : 3 ≤ N)
    (P : Finset Nat.Primes) (hP4 : ∀ p ∈ P, (4 : ℝ) ≤ ((p : ℕ) : ℝ)) {V t₀ lam : ℝ}
    (hV : ∑ p ∈ P, 4 * (r / (1 + r ^ 2)) ^ 2 / ((p : ℕ) : ℝ) ≤ V) (ht₀ : 0 ≤ t₀) (hlam : 0 ≤ lam)
    (hsmall : (t₀ + V) * Real.exp (t₀ + V) ≤ poleSharpConstant / (2 * lagWeightTotal)) :
    ((Finset.univ.filter fun k : ↥P → Fin N => (jasPhaseAggregate 1 r N P k).re < 0).card : ℝ) ≤
      (N : ℝ) ^ P.card * (4 * lagWeightTotal / poleSharpConstant) *
        Real.exp (2 * V - lam * t₀ + 2 * (2 + lam) ^ 2 * V) := by
  classical
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = r / (1 + r ^ 2) := ⟨_, rfl⟩
  rw [← hadef] at hV
  have ha : 0 ≤ a := by rw [hadef]; positivity
  have ha2 : a ≤ 1 / 2 := by
    rw [hadef, div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (r - 1)]
  have hΦ := poleSharpConstant_pos
  have hW := lagWeightTotal_pos
  have hV0 : 0 ≤ V := le_trans (Finset.sum_nonneg fun p _ => by
    have := p.2.pos; positivity) hV
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = 2 + lam := ⟨_, rfl⟩
  have hμ0 : 0 ≤ μ := by rw [hμdef]; linarith
  -- notation
  obtain ⟨A, hAdef⟩ : ∃ A : XiZeroCopy → ↥P → ℂ,
      A = fun (q : XiZeroCopy) (p : ↥P) => jasHoloA ((q.1 : ℂ) + (1 - 1 / 2 : ℝ)) (p : Nat.Primes) :=
    ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : XiZeroCopy → ↥P → ℂ,
      B = fun (q : XiZeroCopy) (p : ↥P) => jasHoloB ((q.1 : ℂ) - (1 - 1 / 2 : ℝ)) (p : Nat.Primes) :=
    ⟨_, rfl⟩
  have hAB : ∀ q (p : ↥P), ‖A q p‖ + ‖B q p‖ ≤ 2 * Real.exp (-(1 / 2) * Real.log ((p : ℕ) : ℝ)) := by
    intro q p
    have h1 := norm_jasHoloA_le_half 1 q p
    have h2 := norm_jasHoloB_le_half 1 q p
    rw [hAdef, hBdef]
    norm_num at h1 h2 ⊢
    linarith
  have hexp_half : ∀ p : Nat.Primes, Real.exp (-(1 / 2) * Real.log ((p : ℕ) : ℝ)) ^ 2 =
      1 / ((p : ℕ) : ℝ) := by
    intro p
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by have := p.2.pos; positivity
    rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(1 / 2) * Real.log ((p : ℕ) : ℝ)) =
      -Real.log ((p : ℕ) : ℝ) by push_cast; ring, Real.exp_neg, Real.exp_log hp0, one_div]
  have hexp_le : ∀ p ∈ P, Real.exp (-(1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤ 1 / 2 := by
    intro p hp
    have hp4 := hP4 p hp
    have h := hexp_half p
    have hpos := Real.exp_pos (-(1 / 2) * Real.log ((p : ℕ) : ℝ))
    have : 1 / ((p : ℕ) : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hp4
    nlinarith
  have hMsq : ∀ q, ∑ p : ↥P, (a * (‖A q p‖ + ‖B q p‖)) ^ 2 ≤ V := by
    intro q
    refine le_trans ?_ hV
    rw [← Finset.sum_coe_sort P]
    refine Finset.sum_le_sum fun p _ => ?_
    have h1 : a * (‖A q p‖ + ‖B q p‖) ≤ a * (2 * Real.exp (-(1 / 2) * Real.log ((p : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left (hAB q p) ha
    have h0 : 0 ≤ a * (‖A q p‖ + ‖B q p‖) := by positivity
    have h2 := pow_le_pow_left₀ h0 h1 2
    have e : (a * (2 * Real.exp (-(1 / 2) * Real.log (((p : Nat.Primes) : ℕ) : ℝ)))) ^ 2 =
        4 * a ^ 2 / (((p : Nat.Primes) : ℕ) : ℝ) := by
      rw [mul_pow, mul_pow, hexp_half (p : Nat.Primes)]; ring
    rw [e] at h2
    exact h2
  -- the phase products
  obtain ⟨Pi, hPidef⟩ : ∃ Pi : XiZeroCopy → (↥P → Fin N) → ℂ,
      Pi = fun q k => ∏ p : ↥P, phaseFactor N a (A q p) (B q p) (k p) := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : XiZeroCopy → (↥P → Fin N) → ℝ,
      s = fun q k => ‖∑ p : ↥P, jasPhaseLinear N a (A q p) (B q p) (k p)‖ := ⟨_, rfl⟩
  have hu : ∀ (q : XiZeroCopy) (k : ↥P → Fin N) (p : ↥P),
      ‖jasPhaseLinear N a (A q p) (B q p) (k p)‖ ≤ 1 / 2 := by
    intro q k p
    refine (norm_jasPhaseLinear_le ha _ _ _).trans ?_
    have := hAB q p; have := hexp_le (p : Nat.Primes) p.2
    nlinarith
  have hPi : ∀ q k, ‖Pi q k - 1‖ ≤ (s q k + V) * Real.exp (s q k + V) := by
    intro q k
    have h := norm_prod_one_add_sub_one_le_of_half Finset.univ
      (fun p : ↥P => jasPhaseLinear N a (A q p) (B q p) (k p)) (fun p _ => hu q k p)
    have hsq : ∑ p : ↥P, ‖jasPhaseLinear N a (A q p) (B q p) (k p)‖ ^ 2 ≤ V := by
      refine le_trans (Finset.sum_le_sum fun p _ => pow_le_pow_left₀ (norm_nonneg _)
        (norm_jasPhaseLinear_le ha _ _ (k p)) 2) (hMsq q)
    rw [hPidef, hsdef]
    simp only [phaseFactor_eq_one_add]
    refine h.trans ?_
    have h0 : 0 ≤ ‖∑ p : ↥P, jasPhaseLinear N a (A q p) (B q p) (k p)‖ +
        ∑ p : ↥P, ‖jasPhaseLinear N a (A q p) (B q p) (k p)‖ ^ 2 := by positivity
    exact mul_le_mul (by linarith) (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
      (by positivity)
  -- the pointwise split
  obtain ⟨η₀, hη₀def⟩ : ∃ η : ℝ, η = poleSharpConstant / (2 * lagWeightTotal) := ⟨_, rfl⟩
  have hsplit : ∀ q k, ‖Pi q k - 1‖ ≤ η₀ + Real.exp (2 * V - lam * t₀) * Real.exp (μ * s q k) := by
    intro q k
    refine (hPi q k).trans ?_
    have hs0 : 0 ≤ s q k := by rw [hsdef]; exact norm_nonneg _
    have hE := Real.exp_pos (2 * V - lam * t₀)
    have hE2 := Real.exp_pos (μ * s q k)
    rcases le_or_gt (s q k) t₀ with h | h
    · have : (s q k + V) * Real.exp (s q k + V) ≤ (t₀ + V) * Real.exp (t₀ + V) :=
        mul_le_mul (by linarith) (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
          (by linarith)
      rw [hη₀def]; nlinarith
    · have h1 : (s q k + V) * Real.exp (s q k + V) ≤ Real.exp (s q k + V) * Real.exp (s q k + V) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (s q k + V)])
          (Real.exp_pos _).le
      have h2 : Real.exp (s q k + V) * Real.exp (s q k + V) ≤
          Real.exp (2 * V - lam * t₀) * Real.exp (μ * s q k) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        rw [hμdef]; nlinarith
      have hη : 0 ≤ η₀ := by rw [hη₀def]; positivity
      linarith
  -- the aggregate
  obtain ⟨w, hwdef⟩ : ∃ w : XiZeroCopy → ℂ, w = fun q => 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) :=
    ⟨_, rfl⟩
  have hws : Summable w := by rw [hwdef]; exact summable_inv_mul_one_sub
  have hwn : Summable fun q => ‖w q‖ := hws.norm
  have hWt : ∑' q, ‖w q‖ = lagWeightTotal := by rw [hwdef]; rfl
  have hagg : ∀ k, jasPhaseAggregate 1 r N P k =
      (((1 + r ^ 2) ^ P.card : ℝ) : ℂ) * ∑' q, w q * Pi q k := by
    intro k
    unfold jasPhaseAggregate
    rw [← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [Finset.prod_congr rfl fun p _ => jasBernoulliFactor_phase _ _ hr (k p),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe, hPidef,
      hwdef, hAdef, hBdef, hadef]
    push_cast
    ring
  have hbndPi : ∀ q k, ‖Pi q k - 1‖ ≤ (P.card + V) * Real.exp (P.card + V) := by
    intro q k
    refine (hPi q k).trans ?_
    have hs : s q k ≤ P.card := by
      rw [hsdef]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ p : ↥P, ‖jasPhaseLinear N a (A q p) (B q p) (k p)‖ ≤ ∑ _p : ↥P, (1 : ℝ) :=
            Finset.sum_le_sum fun p _ => by linarith [hu q k p]
        _ = P.card := by simp
    have hs0 : 0 ≤ s q k := by rw [hsdef]; exact norm_nonneg _
    exact mul_le_mul (by linarith) (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
      (by positivity)
  have hsumD : ∀ k, Summable fun q => w q * (Pi q k - 1) := fun k =>
    Summable.of_norm_bounded (hwn.mul_right _) fun q => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hbndPi q k) (norm_nonneg _)
  have hsplitagg : ∀ k, ∑' q, w q * Pi q k = (poleSharpConstant : ℂ) + ∑' q, w q * (Pi q k - 1) := by
    intro k
    have e1 : ∀ q, w q * Pi q k = w q + w q * (Pi q k - 1) := fun q => by ring
    simp_rw [e1]
    rw [hws.tsum_add (hsumD k), hwdef, tsum_inv_zero_mul_one_sub_zero]
  have hsbnd : ∀ q k, s q k ≤ P.card := by
    intro q k
    rw [hsdef]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ p : ↥P, ‖jasPhaseLinear N a (A q p) (B q p) (k p)‖ ≤ ∑ _p : ↥P, (1 : ℝ) :=
          Finset.sum_le_sum fun p _ => by linarith [hu q k p]
      _ = P.card := by simp
  have hsumT : ∀ k, Summable fun q => ‖w q‖ * Real.exp (μ * s q k) := fun k =>
    Summable.of_nonneg_of_le (fun q => by positivity)
      (fun q => mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hsbnd q k) hμ0)) (norm_nonneg _)) (hwn.mul_right _)
  -- a bad vector has a large exponential moment
  have hbad : ∀ k, (jasPhaseAggregate 1 r N P k).re < 0 →
      poleSharpConstant / 2 * Real.exp (lam * t₀ - 2 * V) ≤ ∑' q, ‖w q‖ * Real.exp (μ * s q k) := by
    intro k hk
    rw [hagg, hsplitagg, Complex.re_ofReal_mul] at hk
    have hc : 0 < ((1 + r ^ 2) ^ P.card : ℝ) := by positivity
    have hre : ((poleSharpConstant : ℂ) + ∑' q, w q * (Pi q k - 1)).re < 0 := by
      by_contra h; push Not at h; linarith [mul_nonneg hc.le h]
    rw [Complex.add_re, Complex.ofReal_re] at hre
    have h1 : poleSharpConstant ≤ ‖∑' q, w q * (Pi q k - 1)‖ := by
      have := (neg_le_abs _).trans (Complex.abs_re_le_norm (∑' q, w q * (Pi q k - 1))); linarith
    have h2 : ‖∑' q, w q * (Pi q k - 1)‖ ≤
        ∑' q, ‖w q‖ * (η₀ + Real.exp (2 * V - lam * t₀) * Real.exp (μ * s q k)) := by
      refine (norm_tsum_le_tsum_norm (hsumD k).norm).trans ?_
      refine (hsumD k).norm.tsum_le_tsum (fun q => ?_) ?_
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hsplit q k) (norm_nonneg _)
      · have := (hwn.mul_right η₀).add ((hsumT k).mul_left (Real.exp (2 * V - lam * t₀)))
        refine this.congr fun q => by ring
    have h3 : ∑' q, ‖w q‖ * (η₀ + Real.exp (2 * V - lam * t₀) * Real.exp (μ * s q k)) =
        η₀ * lagWeightTotal + Real.exp (2 * V - lam * t₀) * ∑' q, ‖w q‖ * Real.exp (μ * s q k) := by
      have e : ∀ q, ‖w q‖ * (η₀ + Real.exp (2 * V - lam * t₀) * Real.exp (μ * s q k)) =
          η₀ * ‖w q‖ + Real.exp (2 * V - lam * t₀) * (‖w q‖ * Real.exp (μ * s q k)) :=
        fun q => by ring
      simp_rw [e]
      rw [(hwn.mul_left η₀).tsum_add ((hsumT k).mul_left _), tsum_mul_left, tsum_mul_left, hWt]
    have hη : η₀ * lagWeightTotal = poleSharpConstant / 2 := by rw [hη₀def]; field_simp
    rw [h3, hη] at h2
    have hE : Real.exp (2 * V - lam * t₀) * Real.exp (lam * t₀ - 2 * V) = 1 := by
      rw [← Real.exp_add]; simp
    have hT0 : 0 ≤ ∑' q, ‖w q‖ * Real.exp (μ * s q k) := tsum_nonneg fun q => by positivity
    have h4 : poleSharpConstant / 2 ≤
        Real.exp (2 * V - lam * t₀) * ∑' q, ‖w q‖ * Real.exp (μ * s q k) := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 (Real.exp_pos (lam * t₀ - 2 * V)).le
    calc poleSharpConstant / 2 * Real.exp (lam * t₀ - 2 * V)
        = Real.exp (lam * t₀ - 2 * V) * (poleSharpConstant / 2) := by ring
      _ ≤ Real.exp (lam * t₀ - 2 * V) *
          (Real.exp (2 * V - lam * t₀) * ∑' q, ‖w q‖ * Real.exp (μ * s q k)) := h5
      _ = ∑' q, ‖w q‖ * Real.exp (μ * s q k) := by rw [← mul_assoc, mul_comm (Real.exp _), hE,
          one_mul]
  -- the total exponential moment
  have htot : ∑ k : ↥P → Fin N, ∑' q, ‖w q‖ * Real.exp (μ * s q k) ≤
      lagWeightTotal * (2 * (N : ℝ) ^ P.card * Real.exp (2 * μ ^ 2 * V)) := by
    rw [← Summable.tsum_finsetSum fun k _ => hsumT k]
    have hq : ∀ q, ∑ k : ↥P → Fin N, ‖w q‖ * Real.exp (μ * s q k) ≤
        ‖w q‖ * (2 * (N : ℝ) ^ P.card * Real.exp (2 * μ ^ 2 * V)) := by
      intro q
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have h := sum_exp_norm_sum_le hN ha (A q) (B q) hμ0
      rw [Fintype.card_coe] at h
      rw [hsdef]
      refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity))
      exact mul_le_mul_of_nonneg_left (hMsq q) (by positivity)
    refine (Summable.tsum_le_tsum hq (summable_sum fun k _ => hsumT k) (hwn.mul_right _)).trans
      (le_of_eq ?_)
    rw [tsum_mul_right, hWt]
  -- counting
  obtain ⟨m, hmdef⟩ : ∃ m : ℝ, m = poleSharpConstant / 2 * Real.exp (lam * t₀ - 2 * V) := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hmdef]; positivity
  have hcount : ((Finset.univ.filter fun k : ↥P → Fin N =>
      (jasPhaseAggregate 1 r N P k).re < 0).card : ℝ) * m ≤
      ∑ k : ↥P → Fin N, ∑' q, ‖w q‖ * Real.exp (μ * s q k) := by
    rw [show ((Finset.univ.filter fun k : ↥P → Fin N =>
        (jasPhaseAggregate 1 r N P k).re < 0).card : ℝ) * m =
        ∑ _k ∈ Finset.univ.filter (fun k : ↥P → Fin N => (jasPhaseAggregate 1 r N P k).re < 0), m by
      rw [Finset.sum_const, nsmul_eq_mul]]
    calc ∑ _k ∈ Finset.univ.filter (fun k : ↥P → Fin N => (jasPhaseAggregate 1 r N P k).re < 0), m
        ≤ ∑ k ∈ Finset.univ.filter (fun k : ↥P → Fin N => (jasPhaseAggregate 1 r N P k).re < 0),
            ∑' q, ‖w q‖ * Real.exp (μ * s q k) :=
          Finset.sum_le_sum fun k hk => hmdef ▸ hbad k (Finset.mem_filter.mp hk).2
      _ ≤ ∑ k : ↥P → Fin N, ∑' q, ‖w q‖ * Real.exp (μ * s q k) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun k _ _ => tsum_nonneg fun q => by positivity)
  have hfin := hcount.trans htot
  rw [← le_div_iff₀ hm] at hfin
  refine hfin.trans (le_of_eq ?_)
  rw [hmdef, hμdef]
  have e1 : Real.exp (2 * V - lam * t₀ + 2 * (2 + lam) ^ 2 * V) =
      Real.exp (2 * (2 + lam) ^ 2 * V) / Real.exp (lam * t₀ - 2 * V) := by
    rw [← Real.exp_sub]; ring_nf
  rw [e1]
  field_simp
  ring

/-! ## The dyadic corollary -/

/-- **The exceptional phase set on a dyadic prime set is polynomially small.**  There are
absolute constants `c > 0`, `C` and `Y` such that for every `y ≥ Y`, every set `P` of primes in
`(y, 2y]`, every `r ≥ 0` and every `N ≥ 3`, at most `C N^{|P|} y^{−c}` phase vectors give a negative
level-one JAS aggregate. -/
theorem exists_card_jasPhaseAggregate_re_neg_le_dyadic_rpow :
    ∃ c : ℝ, 0 < c ∧ ∃ C Y : ℝ, 1 < Y ∧ ∀ y : ℝ, Y ≤ y → ∀ (P : Finset Nat.Primes),
      (∀ p ∈ P, y < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ 2 * y) → ∀ (r : ℝ), 0 ≤ r → ∀ (N : ℕ), 3 ≤ N →
        ((Finset.univ.filter fun k : ↥P → Fin N => (jasPhaseAggregate 1 r N P k).re < 0).card : ℝ)
          ≤ C * (N : ℝ) ^ P.card * Real.exp (-(c * Real.log y)) := by
  have hΦ := poleSharpConstant_pos
  have hW := lagWeightTotal_pos
  have hΦW := poleSharpConstant_le_lagWeightTotal
  obtain ⟨η₀, hη₀def⟩ : ∃ η : ℝ, η = poleSharpConstant / (2 * lagWeightTotal) := ⟨_, rfl⟩
  have hη₀ : 0 < η₀ := by rw [hη₀def]; positivity
  have hη₀h : η₀ ≤ 1 / 2 := by
    rw [hη₀def, div_le_iff₀ (by positivity)]; linarith
  obtain ⟨t₀, ht₀def⟩ : ∃ t : ℝ, t = η₀ / 4 := ⟨_, rfl⟩
  have ht₀ : 0 < t₀ := by rw [ht₀def]; positivity
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨t₀ ^ 2 / (64 * Real.log 4), by positivity, 4 * lagWeightTotal / poleSharpConstant *
    Real.exp 1, max 4 (Real.exp (256 * Real.log 4 / η₀)), by
      have := le_max_left (4 : ℝ) (Real.exp (256 * Real.log 4 / η₀)); linarith, ?_⟩
  intro y hy P hP r hr N hN
  have hy4 : 4 ≤ y := le_trans (le_max_left _ _) hy
  have hy1 : 1 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos hy1
  have hlyb : 256 * Real.log 4 / η₀ ≤ Real.log y := by
    rw [← Real.log_exp (256 * Real.log 4 / η₀)]
    exact Real.log_le_log (Real.exp_pos _) (le_trans (le_max_right _ _) hy)
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = 2 * Real.log 4 / Real.log y := ⟨_, rfl⟩
  have hV0 : 0 < V := by rw [hVdef]; positivity
  have hVsmall : V ≤ η₀ / 128 := by
    rw [hVdef, div_le_iff₀ hly]
    rw [div_le_iff₀ hη₀] at hlyb
    nlinarith
  -- the hypotheses of the counting theorem
  have ha : r / (1 + r ^ 2) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (r - 1)]
  have ha0 : 0 ≤ r / (1 + r ^ 2) := by positivity
  have hV : ∑ p ∈ P, 4 * (r / (1 + r ^ 2)) ^ 2 / ((p : ℕ) : ℝ) ≤ V := by
    have h1 : ∀ p ∈ P, 4 * (r / (1 + r ^ 2)) ^ 2 / ((p : ℕ) : ℝ) ≤ 1 / ((p : ℕ) : ℝ) := by
      intro p _
      have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by have := p.2.pos; positivity
      rw [div_le_div_iff_of_pos_right hp0]
      nlinarith
    refine (Finset.sum_le_sum h1).trans ?_
    rw [hVdef]
    exact sum_inv_prime_le_of_dyadic hy1 P hP
  have hP4 : ∀ p ∈ P, (4 : ℝ) ≤ ((p : ℕ) : ℝ) := fun p hp => by linarith [(hP p hp).1]
  have hsmall : (t₀ + V) * Real.exp (t₀ + V) ≤ poleSharpConstant / (2 * lagWeightTotal) := by
    rw [← hη₀def]
    have h1 : t₀ + V ≤ η₀ / 2 := by rw [ht₀def]; linarith
    have h2 : t₀ + V ≤ 1 / 4 := by linarith
    have h3 : Real.exp (t₀ + V) ≤ 2 := by
      calc Real.exp (t₀ + V) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
        _ ≤ 2 := exp_one_half_le_two_lag
    have h0 : 0 ≤ t₀ + V := by linarith
    nlinarith
  obtain ⟨lam, hlamdef⟩ : ∃ l : ℝ, l = t₀ / (16 * V) := ⟨_, rfl⟩
  have hlam2 : 2 ≤ lam := by
    rw [hlamdef, le_div_iff₀ (by positivity), ht₀def]; linarith
  have hcount := card_jasPhaseAggregate_re_neg_le_exp hr hN P hP4 hV ht₀.le (by linarith) hsmall
    (lam := lam)
  refine hcount.trans ?_
  -- the exponent
  have hexp : 2 * V - lam * t₀ + 2 * (2 + lam) ^ 2 * V ≤ 1 - t₀ ^ 2 / (64 * Real.log 4) *
      Real.log y := by
    have h1 : (2 + lam) ^ 2 ≤ 4 * lam ^ 2 := by nlinarith
    have h2 : 2 * (2 + lam) ^ 2 * V ≤ 8 * lam ^ 2 * V := by nlinarith
    have h3 : 8 * lam ^ 2 * V = lam * t₀ / 2 := by
      rw [hlamdef]; field_simp; ring
    have h4 : lam * t₀ / 2 = t₀ ^ 2 / (32 * V) := by rw [hlamdef]; field_simp; ring
    have h5 : t₀ ^ 2 / (32 * V) = t₀ ^ 2 / (64 * Real.log 4) * Real.log y := by
      rw [hVdef]; field_simp; ring
    have h6 : 2 * V ≤ 1 := by linarith
    linarith
  have hpos : 0 ≤ (N : ℝ) ^ P.card * (4 * lagWeightTotal / poleSharpConstant) := by positivity
  calc (N : ℝ) ^ P.card * (4 * lagWeightTotal / poleSharpConstant) *
        Real.exp (2 * V - lam * t₀ + 2 * (2 + lam) ^ 2 * V)
      ≤ (N : ℝ) ^ P.card * (4 * lagWeightTotal / poleSharpConstant) *
          Real.exp (1 - t₀ ^ 2 / (64 * Real.log 4) * Real.log y) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hpos
    _ = 4 * lagWeightTotal / poleSharpConstant * Real.exp 1 * (N : ℝ) ^ P.card *
          Real.exp (-(t₀ ^ 2 / (64 * Real.log 4) * Real.log y)) := by
        rw [sub_eq_add_neg, Real.exp_add]; ring

end

end RHTower
