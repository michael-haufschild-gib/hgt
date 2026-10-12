import GaloisForLFunctions.RHTower.JointAncestryRandomPhaseLargeDeviation
import GaloisForLFunctions.RHTower.JointAncestryZeroTailBound
import GaloisForLFunctions.RHTower.JointAncestryWeightedCosProducer

/-!
# The exceptional phase set is graded by the zero widths

On a set `P` of primes in `(y, 2y]`, test level-one JAS positivity on the phase vectors
`k : P → ℤ/N` (`z_p = r ω^{k_p}`, `N ≥ 3`).  Write `ω_q = ½ − |Re q − ½|` for the width of a zero.

* **Width-graded count** (`exists_card_jasPhaseAggregate_re_neg_le_dyadic_width`).  Under no
  hypothesis on the zeros, the number of phase vectors with a negative aggregate is at most
  `C N^{|P|} Σ_q |w_q| exp(−c y^{2ω_q} log y)`.
* **Half-plane law** (`exists_card_jasPhaseAggregate_re_neg_le_dyadic_halfPlane`).  If every zero
  satisfies `Re ρ ≤ ½ + α`, the count is at most `C N^{|P|} exp(−c y^{1−2α} log y)`.
* **Unconditional bound** (`exists_card_jasPhaseAggregate_re_neg_le_dyadic_superpoly`).  For every
  `α < 3/2` the count is at most `C N^{|P|} exp(−(log y)^α)`, so the exceptional proportion is
  smaller than every power of `y`.

**Proof.**  Each zero gets its own variance.  The linear phase terms `u_p` of the zero `q` satisfy
`|u_p| ≤ 2a p^{−(1−|Re q−½|)}`, so `Σ_P |u_p|² ≤ U_q = y^{−2ω_q} Σ_P 4a²/p`.  Split the zeros at
`|Σu_p| = t₀` as in the uniform proof, but tilt each zero by its own parameter
`λ_q = t₀/(16U_q)`.  Markov's inequality over the phases gives the general count
`#bad ≤ N^{|P|}(4/Φ(0)) Σ_q |w_q| e^{2U_q − λ_q t₀ + 2(2+λ_q)²U_q}`
(`card_jasPhaseAggregate_re_neg_le_tsum`), with exponent `≤ 1 − t₀²/(32U_q)`.  For the
unconditional bound, split the zeros at height `T = exp((log y)^{α'})`, `α < α' < 3/2`.
* Below `T`, the zero-free region `ω_q ≥ (log T)^{−θ}`, `θ > 2/3`, makes `y^{2ω_q}` larger than
  `exp(2(log y)^{1−α'θ})`.
* Above `T`, the weight tail `Σ_{|Im q|>T} |w_q| = O(log T/T)` applies.

The exponent `3/2` is the reciprocal of the zero-free-region exponent `2/3`.  The constant vectors
form a proportion `N^{1−|P|} ≈ exp(−y log N/log y)` of the phase vectors.  The half-plane bound
`exp(−c y^{1−2α} log y)` falls below this proportion only when `α → 0` as `y → ∞`.
-/

open Complex Filter Asymptotics
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## The width-graded count -/

/-- At level one, `‖A‖ + ‖B‖ ≤ 2 p^{−(1 − |Re q − ½|)}`. -/
theorem norm_jasHolo_add_le_width (q : XiZeroCopy) (p : Nat.Primes) :
    ‖jasHoloA ((q.1 : ℂ) + (1 - 1 / 2 : ℝ)) p‖ + ‖jasHoloB ((q.1 : ℂ) - (1 - 1 / 2 : ℝ)) p‖ ≤
      2 * Real.exp (-(1 - |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ)) := by
  have h1 := norm_jasHoloA_dressed_le_abs 1 q p
  have h2 := norm_jasHoloB_dressed_le_abs 1 q p
  linarith

/-- `p^{−2(1−x)} = p^{−(1−2x)}/p`. -/
theorem sq_exp_width_eq (x : ℝ) (p : Nat.Primes) :
    Real.exp (-(1 - x) * Real.log ((p : ℕ) : ℝ)) ^ 2 =
      Real.exp (-(1 - 2 * x) * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) := by
  have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by have := p.2.pos; positivity
  calc Real.exp (-(1 - x) * Real.log ((p : ℕ) : ℝ)) ^ 2
      = Real.exp (-(1 - 2 * x) * Real.log ((p : ℕ) : ℝ) + -Real.log ((p : ℕ) : ℝ)) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    _ = Real.exp (-(1 - 2 * x) * Real.log ((p : ℕ) : ℝ)) / ((p : ℕ) : ℝ) := by
        rw [Real.exp_add, Real.exp_neg, Real.exp_log hp0, div_eq_mul_inv]

/-- **Width-graded large-deviation count at level one.**  Let `P` be a set of primes `p ≥ 4`,
`V ≥ Σ_P 4a²/p` and `t₀ ≥ 0` with `(t₀ + V)e^{t₀+V} ≤ Φ(0)/(2W)`.  Give every zero `q` a variance
bound `U_q ≤ V` for `Σ_P 4a² p^{−(1−2|Re q − ½|)}/p` and a tilt `0 ≤ λ_q ≤ Λ` whose exponent
`2U_q − λ_q t₀ + 2(2+λ_q)²U_q` is bounded above.  Then the number of phase vectors with a
negative aggregate is at most `N^{|P|}(4/Φ(0)) Σ_q |w_q| e^{2U_q − λ_q t₀ + 2(2+λ_q)²U_q}`. -/
theorem card_jasPhaseAggregate_re_neg_le_tsum {r : ℝ} (hr : 0 ≤ r) {N : ℕ} (hN : 3 ≤ N)
    (P : Finset Nat.Primes) (hP4 : ∀ p ∈ P, (4 : ℝ) ≤ ((p : ℕ) : ℝ)) {V t₀ Λ E : ℝ}
    (hV : ∑ p ∈ P, 4 * (r / (1 + r ^ 2)) ^ 2 / ((p : ℕ) : ℝ) ≤ V) (ht₀ : 0 ≤ t₀)
    (hsmall : (t₀ + V) * Real.exp (t₀ + V) ≤ poleSharpConstant / (2 * lagWeightTotal))
    (U lam : XiZeroCopy → ℝ)
    (hU : ∀ q : XiZeroCopy, ∑ p ∈ P, 4 * (r / (1 + r ^ 2)) ^ 2 *
      (Real.exp (-(1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ)) /
        ((p : ℕ) : ℝ)) ≤ U q)
    (hUV : ∀ q, U q ≤ V) (hlam0 : ∀ q, 0 ≤ lam q) (hlamΛ : ∀ q, lam q ≤ Λ)
    (hE : ∀ q, 2 * U q - lam q * t₀ + 2 * (2 + lam q) ^ 2 * U q ≤ E) :
    ((Finset.univ.filter fun k : ↥P → Fin N => (jasPhaseAggregate 1 r N P k).re < 0).card : ℝ) ≤
      (N : ℝ) ^ P.card * (4 / poleSharpConstant) *
        ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
          Real.exp (2 * U q - lam q * t₀ + 2 * (2 + lam q) ^ 2 * U q) := by
  classical
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = r / (1 + r ^ 2) := ⟨_, rfl⟩
  rw [← hadef] at hV hU
  have ha : 0 ≤ a := by rw [hadef]; positivity
  have hΦ := poleSharpConstant_pos
  have hW := lagWeightTotal_pos
  have hV0 : 0 ≤ V := le_trans (Finset.sum_nonneg fun p _ => by
    have := p.2.pos; positivity) hV
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
  have hexp_le : ∀ p ∈ P, Real.exp (-(1 / 2) * Real.log ((p : ℕ) : ℝ)) ≤ 1 / 2 := by
    intro p hp
    have hp4 := hP4 p hp
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by have := p.2.pos; positivity
    have h : Real.exp (-(1 / 2) * Real.log ((p : ℕ) : ℝ)) ^ 2 = 1 / ((p : ℕ) : ℝ) := by
      rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-(1 / 2) * Real.log ((p : ℕ) : ℝ)) =
        -Real.log ((p : ℕ) : ℝ) by push_cast; ring, Real.exp_neg, Real.exp_log hp0, one_div]
    have hpos := Real.exp_pos (-(1 / 2) * Real.log ((p : ℕ) : ℝ))
    have : 1 / ((p : ℕ) : ℝ) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) hp4
    nlinarith
  have hMsq : ∀ q, ∑ p : ↥P, (a * (‖A q p‖ + ‖B q p‖)) ^ 2 ≤ U q := by
    intro q
    refine le_trans ?_ (hU q)
    rw [← Finset.sum_coe_sort P]
    refine Finset.sum_le_sum fun p _ => ?_
    have h1 : a * (‖A q p‖ + ‖B q p‖) ≤
        a * (2 * Real.exp (-(1 - |(q.1 : ℂ).re - 1 / 2|) * Real.log (((p : Nat.Primes) : ℕ) : ℝ))) := by
      refine mul_le_mul_of_nonneg_left ?_ ha
      rw [hAdef, hBdef]
      exact norm_jasHolo_add_le_width q p
    have h0 : 0 ≤ a * (‖A q p‖ + ‖B q p‖) := by positivity
    have h2 := pow_le_pow_left₀ h0 h1 2
    have e := sq_exp_width_eq |(q.1 : ℂ).re - 1 / 2| (p : Nat.Primes)
    calc (a * (‖A q p‖ + ‖B q p‖)) ^ 2
        ≤ (a * (2 * Real.exp (-(1 - |(q.1 : ℂ).re - 1 / 2|) *
            Real.log (((p : Nat.Primes) : ℕ) : ℝ)))) ^ 2 := h2
      _ = 4 * a ^ 2 * Real.exp (-(1 - |(q.1 : ℂ).re - 1 / 2|) *
            Real.log (((p : Nat.Primes) : ℕ) : ℝ)) ^ 2 := by ring
      _ = _ := by rw [e]
  have hU0 : ∀ q, 0 ≤ U q := fun q =>
    le_trans (Finset.sum_nonneg fun p _ => sq_nonneg _) (hMsq q)
  -- the phase products
  obtain ⟨Pi, hPidef⟩ : ∃ Pi : XiZeroCopy → (↥P → Fin N) → ℂ,
      Pi = fun q k => ∏ p : ↥P, phaseFactor N a (A q p) (B q p) (k p) := ⟨_, rfl⟩
  obtain ⟨s, hsdef⟩ : ∃ s : XiZeroCopy → (↥P → Fin N) → ℝ,
      s = fun q k => ‖∑ p : ↥P, jasPhaseLinear N a (A q p) (B q p) (k p)‖ := ⟨_, rfl⟩
  have hu : ∀ (q : XiZeroCopy) (k : ↥P → Fin N) (p : ↥P),
      ‖jasPhaseLinear N a (A q p) (B q p) (k p)‖ ≤ 1 / 2 := by
    intro q k p
    refine (norm_jasPhaseLinear_le ha _ _ _).trans ?_
    have ha2 : a ≤ 1 / 2 := by
      rw [hadef, div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (r - 1)]
    have := hAB q p; have := hexp_le (p : Nat.Primes) p.2
    nlinarith
  have hPi : ∀ q k, ‖Pi q k - 1‖ ≤ (s q k + U q) * Real.exp (s q k + U q) := by
    intro q k
    have h := norm_prod_one_add_sub_one_le_of_half Finset.univ
      (fun p : ↥P => jasPhaseLinear N a (A q p) (B q p) (k p)) (fun p _ => hu q k p)
    have hsq : ∑ p : ↥P, ‖jasPhaseLinear N a (A q p) (B q p) (k p)‖ ^ 2 ≤ U q := by
      refine le_trans (Finset.sum_le_sum fun p _ => pow_le_pow_left₀ (norm_nonneg _)
        (norm_jasPhaseLinear_le ha _ _ (k p)) 2) (hMsq q)
    rw [hPidef, hsdef]
    simp only [phaseFactor_eq_one_add]
    refine h.trans ?_
    have h0 : 0 ≤ ‖∑ p : ↥P, jasPhaseLinear N a (A q p) (B q p) (k p)‖ +
        ∑ p : ↥P, ‖jasPhaseLinear N a (A q p) (B q p) (k p)‖ ^ 2 := by positivity
    exact mul_le_mul (by linarith) (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
      (add_nonneg (norm_nonneg _) (hU0 q))
  have hsbnd : ∀ q k, s q k ≤ P.card := by
    intro q k
    rw [hsdef]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ p : ↥P, ‖jasPhaseLinear N a (A q p) (B q p) (k p)‖ ≤ ∑ _p : ↥P, (1 : ℝ) :=
          Finset.sum_le_sum fun p _ => by linarith [hu q k p]
      _ = P.card := by simp
  have hs0 : ∀ q k, 0 ≤ s q k := fun q k => by rw [hsdef]; exact norm_nonneg _
  -- the pointwise split, with a tilt per zero
  obtain ⟨η₀, hη₀def⟩ : ∃ η : ℝ, η = poleSharpConstant / (2 * lagWeightTotal) := ⟨_, rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : XiZeroCopy → (↥P → Fin N) → ℝ,
      T = fun q k => Real.exp (2 * U q - lam q * t₀) * Real.exp ((2 + lam q) * s q k) :=
    ⟨_, rfl⟩
  have hT0 : ∀ q k, 0 ≤ T q k := fun q k => by rw [hTdef]; positivity
  have hsplit : ∀ q k, ‖Pi q k - 1‖ ≤ η₀ + T q k := by
    intro q k
    refine (hPi q k).trans ?_
    have hE1 := Real.exp_pos (2 * U q - lam q * t₀)
    have hE2 := Real.exp_pos ((2 + lam q) * s q k)
    have hUq := hUV q
    have hU0q := hU0 q
    have hsq0 := hs0 q k
    rw [hTdef]
    rcases le_or_gt (s q k) t₀ with h | h
    · have : (s q k + U q) * Real.exp (s q k + U q) ≤ (t₀ + V) * Real.exp (t₀ + V) :=
        mul_le_mul (by linarith) (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le
          (by linarith)
      rw [hη₀def]; nlinarith [mul_pos hE1 hE2]
    · have h1 : (s q k + U q) * Real.exp (s q k + U q) ≤
          Real.exp (s q k + U q) * Real.exp (s q k + U q) :=
        mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (s q k + U q)])
          (Real.exp_pos _).le
      have h2 : Real.exp (s q k + U q) * Real.exp (s q k + U q) ≤
          Real.exp (2 * U q - lam q * t₀) * Real.exp ((2 + lam q) * s q k) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_nonneg (hlam0 q) (sub_nonneg.mpr h.le)]
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
    have := hsbnd q k; have := hs0 q k; have := hUV q; have := hU0 q
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
  have hTbnd : ∀ q k, T q k ≤ Real.exp (2 * V) * Real.exp ((2 + Λ) * P.card) := by
    intro q k
    rw [hTdef]
    have hl := hlam0 q
    have hlΛ := hlamΛ q
    refine mul_le_mul (Real.exp_le_exp.mpr ?_) (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le
      (Real.exp_pos _).le
    · nlinarith [hUV q, mul_nonneg hl ht₀]
    · exact mul_le_mul (by linarith) (hsbnd q k) (hs0 q k) (by linarith)
  have hsumT : ∀ k, Summable fun q => ‖w q‖ * T q k := fun k =>
    Summable.of_nonneg_of_le (fun q => mul_nonneg (norm_nonneg _) (hT0 q k))
      (fun q => mul_le_mul_of_nonneg_left (hTbnd q k) (norm_nonneg _)) (hwn.mul_right _)
  -- a bad vector has a large tilted moment
  have hbad : ∀ k, (jasPhaseAggregate 1 r N P k).re < 0 →
      poleSharpConstant / 2 ≤ ∑' q, ‖w q‖ * T q k := by
    intro k hk
    rw [hagg, hsplitagg, Complex.re_ofReal_mul] at hk
    have hc : 0 < ((1 + r ^ 2) ^ P.card : ℝ) := by positivity
    have hre : ((poleSharpConstant : ℂ) + ∑' q, w q * (Pi q k - 1)).re < 0 := by
      by_contra h; push Not at h; linarith [mul_nonneg hc.le h]
    rw [Complex.add_re, Complex.ofReal_re] at hre
    have h1 : poleSharpConstant ≤ ‖∑' q, w q * (Pi q k - 1)‖ := by
      have := (neg_le_abs _).trans (Complex.abs_re_le_norm (∑' q, w q * (Pi q k - 1))); linarith
    have h2 : ‖∑' q, w q * (Pi q k - 1)‖ ≤ ∑' q, ‖w q‖ * (η₀ + T q k) := by
      refine (norm_tsum_le_tsum_norm (hsumD k).norm).trans ?_
      refine (hsumD k).norm.tsum_le_tsum (fun q => ?_) ?_
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hsplit q k) (norm_nonneg _)
      · exact ((hwn.mul_right η₀).add (hsumT k)).congr fun q => by ring
    have h3 : ∑' q, ‖w q‖ * (η₀ + T q k) = η₀ * lagWeightTotal + ∑' q, ‖w q‖ * T q k := by
      have e : ∀ q, ‖w q‖ * (η₀ + T q k) = η₀ * ‖w q‖ + ‖w q‖ * T q k := fun q => by ring
      simp_rw [e]
      rw [(hwn.mul_left η₀).tsum_add (hsumT k), tsum_mul_left, hWt]
    have hη : η₀ * lagWeightTotal = poleSharpConstant / 2 := by rw [hη₀def]; field_simp
    rw [h3, hη] at h2
    linarith
  -- the total tilted moment
  obtain ⟨X, hXdef⟩ : ∃ X : XiZeroCopy → ℝ,
      X = fun q => 2 * U q - lam q * t₀ + 2 * (2 + lam q) ^ 2 * U q := ⟨_, rfl⟩
  have hsumX : Summable fun q => ‖w q‖ * ((2 * (N : ℝ) ^ P.card) * Real.exp (X q)) :=
    Summable.of_nonneg_of_le (fun q => by positivity)
      (fun q => mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (by rw [hXdef]; exact hE q)) (by positivity)) (norm_nonneg _))
      (hwn.mul_right _)
  have htot : ∑ k : ↥P → Fin N, ∑' q, ‖w q‖ * T q k ≤
      ∑' q, ‖w q‖ * ((2 * (N : ℝ) ^ P.card) * Real.exp (X q)) := by
    rw [← Summable.tsum_finsetSum fun k _ => hsumT k]
    refine Summable.tsum_le_tsum (fun q => ?_) (summable_sum fun k _ => hsumT k) hsumX
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hμ0 : 0 ≤ 2 + lam q := by linarith [hlam0 q]
    have h := sum_exp_norm_sum_le hN ha (A q) (B q) hμ0
    rw [Fintype.card_coe] at h
    have e : ∑ k : ↥P → Fin N, T q k =
        Real.exp (2 * U q - lam q * t₀) * ∑ k : ↥P → Fin N, Real.exp ((2 + lam q) * s q k) := by
      rw [hTdef, Finset.mul_sum]
    rw [e, hsdef]
    have h2 : Real.exp (2 * U q - lam q * t₀) *
        ∑ k : ↥P → Fin N, Real.exp ((2 + lam q) *
          ‖∑ p : ↥P, jasPhaseLinear N a (A q p) (B q p) (k p)‖) ≤
        Real.exp (2 * U q - lam q * t₀) * (2 * (N : ℝ) ^ P.card *
          Real.exp (2 * (2 + lam q) ^ 2 * U q)) := by
      refine mul_le_mul_of_nonneg_left (h.trans ?_) (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hMsq q) (by positivity))) (by positivity)
    refine h2.trans (le_of_eq ?_)
    rw [hXdef]
    simp only
    rw [show 2 * U q - lam q * t₀ + 2 * (2 + lam q) ^ 2 * U q =
      (2 * U q - lam q * t₀) + 2 * (2 + lam q) ^ 2 * U q by ring, Real.exp_add]
    ring
  -- counting
  have hcount : ((Finset.univ.filter fun k : ↥P → Fin N =>
      (jasPhaseAggregate 1 r N P k).re < 0).card : ℝ) * (poleSharpConstant / 2) ≤
      ∑ k : ↥P → Fin N, ∑' q, ‖w q‖ * T q k := by
    rw [show ((Finset.univ.filter fun k : ↥P → Fin N =>
        (jasPhaseAggregate 1 r N P k).re < 0).card : ℝ) * (poleSharpConstant / 2) =
        ∑ _k ∈ Finset.univ.filter (fun k : ↥P → Fin N => (jasPhaseAggregate 1 r N P k).re < 0),
          poleSharpConstant / 2 by rw [Finset.sum_const, nsmul_eq_mul]]
    calc ∑ _k ∈ Finset.univ.filter (fun k : ↥P → Fin N => (jasPhaseAggregate 1 r N P k).re < 0),
          poleSharpConstant / 2
        ≤ ∑ k ∈ Finset.univ.filter (fun k : ↥P → Fin N => (jasPhaseAggregate 1 r N P k).re < 0),
            ∑' q, ‖w q‖ * T q k :=
          Finset.sum_le_sum fun k hk => hbad k (Finset.mem_filter.mp hk).2
      _ ≤ ∑ k : ↥P → Fin N, ∑' q, ‖w q‖ * T q k :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun k _ _ => tsum_nonneg fun q => mul_nonneg (norm_nonneg _) (hT0 q k))
  have hfin := hcount.trans htot
  have e : ∑' q, ‖w q‖ * ((2 * (N : ℝ) ^ P.card) * Real.exp (X q)) =
      (2 * (N : ℝ) ^ P.card) * ∑' q, ‖w q‖ * Real.exp (X q) := by
    rw [← tsum_mul_left]; exact tsum_congr fun q => by ring
  rw [e, ← le_div_iff₀ (by positivity)] at hfin
  have hS : ∑' q, ‖w q‖ * Real.exp (X q) = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
      Real.exp (2 * U q - lam q * t₀ + 2 * (2 + lam q) ^ 2 * U q) := by
    rw [hXdef, hwdef]
  rw [hS] at hfin
  refine hfin.trans (le_of_eq ?_)
  generalize (∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
      Real.exp (2 * U q - lam q * t₀ + 2 * (2 + lam q) ^ 2 * U q)) = S
  field_simp
  ring

/-! ## Dyadic prime sets -/

/-- **The width-graded count on a dyadic prime set.**  There are absolute constants `c > 0`, `C`
and `Y` such that for `y ≥ Y`, every set `P` of primes in `(y, 2y]`, every `r ≥ 0` and `N ≥ 3`,
at most `C N^{|P|} Σ_q |w_q| exp(−c y^{1−2|Re q−½|} log y)` phase vectors give a negative
level-one JAS aggregate. -/
theorem exists_card_jasPhaseAggregate_re_neg_le_dyadic_width :
    ∃ c : ℝ, 0 < c ∧ ∃ C Y : ℝ, 0 < C ∧ 1 < Y ∧ ∀ y : ℝ, Y ≤ y → ∀ (P : Finset Nat.Primes),
      (∀ p ∈ P, y < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ 2 * y) → ∀ (r : ℝ), 0 ≤ r → ∀ (N : ℕ), 3 ≤ N →
        ((Finset.univ.filter fun k : ↥P → Fin N => (jasPhaseAggregate 1 r N P k).re < 0).card : ℝ)
          ≤ C * (N : ℝ) ^ P.card * ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
            Real.exp (-(c * Real.exp ((1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log y) *
              Real.log y)) := by
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
  refine ⟨t₀ ^ 2 / (64 * Real.log 4), by positivity, 4 / poleSharpConstant * Real.exp 1,
    max 4 (Real.exp (256 * Real.log 4 / η₀)), by positivity, by
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
  have ha4 : 4 * (r / (1 + r ^ 2)) ^ 2 ≤ 1 := by
    have ha0 : 0 ≤ r / (1 + r ^ 2) := by positivity
    have ha : r / (1 + r ^ 2) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (r - 1)]
    nlinarith
  have hsuminv : ∑ p ∈ P, 1 / ((p : ℕ) : ℝ) ≤ V := by
    rw [hVdef]; exact sum_inv_prime_le_of_dyadic hy1 P hP
  have hV : ∑ p ∈ P, 4 * (r / (1 + r ^ 2)) ^ 2 / ((p : ℕ) : ℝ) ≤ V := by
    refine le_trans (Finset.sum_le_sum fun p _ => ?_) hsuminv
    have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by have := p.2.pos; positivity
    rw [div_le_div_iff_of_pos_right hp0]
    exact ha4
  have hP4 : ∀ p ∈ P, (4 : ℝ) ≤ ((p : ℕ) : ℝ) := fun p hp => by linarith [(hP p hp).1]
  have hsmall : (t₀ + V) * Real.exp (t₀ + V) ≤ poleSharpConstant / (2 * lagWeightTotal) := by
    rw [← hη₀def]
    have h1 : t₀ + V ≤ η₀ / 2 := by rw [ht₀def]; linarith
    have h3 : Real.exp (t₀ + V) ≤ 2 := by
      calc Real.exp (t₀ + V) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
        _ ≤ 2 := exp_one_half_le_two_lag
    have h0 : 0 ≤ t₀ + V := by linarith
    nlinarith
  -- per-zero variance `U_q = y^{−2ω_q} V` and tilt `λ_q = t₀/(16U_q)`
  have hwid : ∀ q : XiZeroCopy, 0 ≤ 1 - 2 * |(q.1 : ℂ).re - 1 / 2| := by
    intro q
    have h := abs_le.mpr (show -(1 / 2 : ℝ) ≤ (q.1 : ℂ).re - 1 / 2 ∧ (q.1 : ℂ).re - 1 / 2 ≤ 1 / 2 by
      constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q])
    linarith
  obtain ⟨g, hgdef⟩ : ∃ g : XiZeroCopy → ℝ,
      g = fun q => Real.exp ((1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log y) := ⟨_, rfl⟩
  have hg1 : ∀ q, 1 ≤ g q := fun q => by
    rw [hgdef]; exact Real.one_le_exp (mul_nonneg (hwid q) hly.le)
  have hgy : ∀ q, g q ≤ y := fun q => by
    rw [hgdef]
    calc Real.exp ((1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log y) ≤ Real.exp (Real.log y) := by
          refine Real.exp_le_exp.mpr ?_
          have := abs_nonneg ((q.1 : ℂ).re - 1 / 2)
          nlinarith
      _ = y := Real.exp_log (by linarith)
  obtain ⟨U, hUdef⟩ : ∃ U : XiZeroCopy → ℝ, U = fun q => V / g q := ⟨_, rfl⟩
  have hUpos : ∀ q, 0 < U q := fun q => by
    rw [hUdef]; exact div_pos hV0 (by linarith [hg1 q])
  have hUV : ∀ q, U q ≤ V := fun q => by
    rw [hUdef]; exact div_le_self hV0.le (hg1 q)
  have hU : ∀ q : XiZeroCopy, ∑ p ∈ P, 4 * (r / (1 + r ^ 2)) ^ 2 *
      (Real.exp (-(1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ)) /
        ((p : ℕ) : ℝ)) ≤ U q := by
    intro q
    have hgq : 0 < g q := by linarith [hg1 q]
    have hterm : ∀ p ∈ P, 4 * (r / (1 + r ^ 2)) ^ 2 *
        (Real.exp (-(1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ)) /
          ((p : ℕ) : ℝ)) ≤ (1 / ((p : ℕ) : ℝ)) / g q := by
      intro p hp
      have hp0 : (0 : ℝ) < ((p : ℕ) : ℝ) := by have := p.2.pos; positivity
      have hlog : Real.log y ≤ Real.log ((p : ℕ) : ℝ) :=
        Real.log_le_log (by linarith) (hP p hp).1.le
      have hexp : Real.exp (-(1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ)) ≤
          1 / g q := by
        simp only [hgdef]
        rw [le_div_iff₀ (Real.exp_pos _), ← Real.exp_add, Real.exp_le_one_iff]
        nlinarith [mul_le_mul_of_nonneg_left hlog (hwid q)]
      have hE0 := Real.exp_pos (-(1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ))
      calc 4 * (r / (1 + r ^ 2)) ^ 2 *
            (Real.exp (-(1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log ((p : ℕ) : ℝ)) /
              ((p : ℕ) : ℝ))
          ≤ 1 * ((1 / g q) / ((p : ℕ) : ℝ)) :=
            mul_le_mul ha4 (div_le_div_of_nonneg_right hexp hp0.le) (by positivity)
              (by norm_num)
        _ = (1 / ((p : ℕ) : ℝ)) / g q := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_div, hUdef]
    exact div_le_div_of_nonneg_right hsuminv hgq.le
  obtain ⟨lam, hlamdef⟩ : ∃ lam : XiZeroCopy → ℝ, lam = fun q => t₀ / (16 * U q) := ⟨_, rfl⟩
  have hlam2 : ∀ q, 2 ≤ lam q := fun q => by
    rw [hlamdef, le_div_iff₀ (by linarith [hUpos q])]
    have := hUV q
    rw [ht₀def]; linarith
  have hlamΛ : ∀ q, lam q ≤ t₀ * y / (16 * V) := fun q => by
    rw [hlamdef, hUdef]
    simp only
    have hgq : 0 < g q := by linarith [hg1 q]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : V / g q * y ≥ V := by
      rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ hgq]
      exact mul_le_mul_of_nonneg_left (hgy q) hV0.le
    nlinarith
  have hexpo : ∀ q, 2 * U q - lam q * t₀ + 2 * (2 + lam q) ^ 2 * U q ≤
      1 - t₀ ^ 2 / (64 * Real.log 4) * g q * Real.log y := by
    intro q
    have hUq := hUpos q
    have hl := hlam2 q
    have h1 : (2 + lam q) ^ 2 ≤ 4 * lam q ^ 2 := by nlinarith
    have h2 : 2 * (2 + lam q) ^ 2 * U q ≤ 8 * lam q ^ 2 * U q := by nlinarith
    have h3 : 8 * lam q ^ 2 * U q = lam q * t₀ / 2 := by
      rw [hlamdef]; field_simp; ring
    have h4 : lam q * t₀ / 2 = t₀ ^ 2 / (32 * U q) := by rw [hlamdef]; field_simp; ring
    have h5 : t₀ ^ 2 / (32 * U q) = t₀ ^ 2 / (64 * Real.log 4) * g q * Real.log y := by
      have hgq : 0 < g q := by linarith [hg1 q]
      rw [hUdef, hVdef]; field_simp; ring
    have h6 : 2 * U q ≤ 1 := by linarith [hUV q]
    linarith
  have hcount := card_jasPhaseAggregate_re_neg_le_tsum hr hN P hP4 hV ht₀.le hsmall U lam hU hUV
    (fun q => by linarith [hlam2 q]) hlamΛ (E := 1) (fun q => by
      have := hexpo q
      have : 0 ≤ t₀ ^ 2 / (64 * Real.log 4) * g q * Real.log y := by
        have := hg1 q; positivity
      linarith)
  refine hcount.trans ?_
  have hsum1 : Summable fun q : XiZeroCopy => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
      Real.exp (-(t₀ ^ 2 / (64 * Real.log 4) * g q * Real.log y)) :=
    Summable.of_nonneg_of_le (fun q => by positivity)
      (fun q => mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by
        have := hg1 q; have : 0 ≤ t₀ ^ 2 / (64 * Real.log 4) * g q * Real.log y := by positivity
        linarith)) (norm_nonneg _))
      (summable_inv_mul_one_sub.norm.mul_right 1)
  have hle : ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
      Real.exp (2 * U q - lam q * t₀ + 2 * (2 + lam q) ^ 2 * U q) ≤
      Real.exp 1 * ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
        Real.exp (-(t₀ ^ 2 / (64 * Real.log 4) * g q * Real.log y)) := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun q => ?_) ?_ (hsum1.mul_left _)
    · rw [show Real.exp 1 * (‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
          Real.exp (-(t₀ ^ 2 / (64 * Real.log 4) * g q * Real.log y))) =
          ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
            Real.exp (1 - t₀ ^ 2 / (64 * Real.log 4) * g q * Real.log y) by
        rw [show (1 : ℝ) - t₀ ^ 2 / (64 * Real.log 4) * g q * Real.log y =
          1 + -(t₀ ^ 2 / (64 * Real.log 4) * g q * Real.log y) by ring, Real.exp_add]; ring]
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hexpo q)) (norm_nonneg _)
    · refine Summable.of_nonneg_of_le (fun q => by positivity)
        (fun q => mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hexpo q)) (norm_nonneg _))
        ?_
      refine Summable.of_nonneg_of_le (fun q => by positivity)
        (fun q => mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (show
          1 - t₀ ^ 2 / (64 * Real.log 4) * g q * Real.log y ≤ 1 by
            have := hg1 q
            have : 0 ≤ t₀ ^ 2 / (64 * Real.log 4) * g q * Real.log y := by positivity
            linarith)) (norm_nonneg _))
        (summable_inv_mul_one_sub.norm.mul_right _)
  have hpos : 0 ≤ (N : ℝ) ^ P.card * (4 / poleSharpConstant) := by positivity
  calc (N : ℝ) ^ P.card * (4 / poleSharpConstant) *
        ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
          Real.exp (2 * U q - lam q * t₀ + 2 * (2 + lam q) ^ 2 * U q)
      ≤ (N : ℝ) ^ P.card * (4 / poleSharpConstant) * (Real.exp 1 *
          ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
            Real.exp (-(t₀ ^ 2 / (64 * Real.log 4) * g q * Real.log y))) :=
        mul_le_mul_of_nonneg_left hle hpos
    _ = 4 / poleSharpConstant * Real.exp 1 * (N : ℝ) ^ P.card *
          ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
            Real.exp (-(t₀ ^ 2 / (64 * Real.log 4) *
              Real.exp ((1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log y) * Real.log y)) := by
        simp only [hgdef]; ring

/-! ## The half-plane law -/

/-- **Half-plane law.**  There are absolute constants `c > 0`, `C`, `Y` such that, whenever every
zero satisfies `Re ρ ≤ ½ + α`, at most `C N^{|P|} exp(−c y^{1−2α} log y)` phase vectors give a
negative level-one aggregate, for `y ≥ Y` and every set `P` of primes in `(y, 2y]`. -/
theorem exists_card_jasPhaseAggregate_re_neg_le_dyadic_halfPlane :
    ∃ c : ℝ, 0 < c ∧ ∃ C Y : ℝ, 1 < Y ∧ ∀ alpha : ℝ, XiZeroHalfPlaneBound alpha →
      ∀ y : ℝ, Y ≤ y → ∀ (P : Finset Nat.Primes),
      (∀ p ∈ P, y < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ 2 * y) → ∀ (r : ℝ), 0 ≤ r → ∀ (N : ℕ), 3 ≤ N →
        ((Finset.univ.filter fun k : ↥P → Fin N => (jasPhaseAggregate 1 r N P k).re < 0).card : ℝ)
          ≤ C * (N : ℝ) ^ P.card *
            Real.exp (-(c * Real.exp ((1 - 2 * alpha) * Real.log y) * Real.log y)) := by
  obtain ⟨c, hc, C, Y, hC, hY, h⟩ := exists_card_jasPhaseAggregate_re_neg_le_dyadic_width
  refine ⟨c, hc, C * lagWeightTotal, Y, hY, fun alpha hXi y hy P hP r hr N hN => ?_⟩
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  refine (h y hy P hP r hr N hN).trans ?_
  have hbound : ∀ q : XiZeroCopy,
      Real.exp (-(c * Real.exp ((1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log y) * Real.log y)) ≤
        Real.exp (-(c * Real.exp ((1 - 2 * alpha) * Real.log y) * Real.log y)) := by
    intro q
    have hq := abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr ?_) hc.le) hly
    nlinarith
  have hsum : ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
      Real.exp (-(c * Real.exp ((1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log y) * Real.log y)) ≤
      lagWeightTotal * Real.exp (-(c * Real.exp ((1 - 2 * alpha) * Real.log y) * Real.log y)) := by
    rw [show lagWeightTotal = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ from rfl,
      ← tsum_mul_right]
    refine Summable.tsum_le_tsum (fun q => mul_le_mul_of_nonneg_left (hbound q) (norm_nonneg _))
      ?_ (summable_inv_mul_one_sub.norm.mul_right _)
    exact Summable.of_nonneg_of_le (fun q => by positivity)
      (fun q => mul_le_mul_of_nonneg_left (hbound q) (norm_nonneg _))
      (summable_inv_mul_one_sub.norm.mul_right _)
  calc C * (N : ℝ) ^ P.card * ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
        Real.exp (-(c * Real.exp ((1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * Real.log y) * Real.log y))
      ≤ C * (N : ℝ) ^ P.card * (lagWeightTotal *
          Real.exp (-(c * Real.exp ((1 - 2 * alpha) * Real.log y) * Real.log y))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C * lagWeightTotal * (N : ℝ) ^ P.card *
          Real.exp (-(c * Real.exp ((1 - 2 * alpha) * Real.log y) * Real.log y)) := by ring

/-! ## The unconditional bound -/

/-- The asymptotic conditions of the superpolynomial bound, in `L = log y`. -/
theorem eventually_superpoly_conditions {α α' θ η₀ c W K : ℝ} (hα0 : 0 < α) (hαα' : α < α')
    (hθ0 : 0 < θ) (hκ : α' * θ < 1) (hη₀ : 0 < η₀) (hc : 0 < c) (hW : 0 < W) (hK : 0 ≤ K) :
    ∀ᶠ L : ℝ in atTop, 1 ≤ L ∧ (L ^ α') ^ (-θ) ≤ η₀ ∧
      W * Real.exp (-(c * Real.exp (2 * (L ^ α') ^ (-θ) * L) * L)) ≤ Real.exp (-(L ^ α)) / 2 ∧
      80 * (K + L ^ α') * Real.exp (-(L ^ α')) ≤ Real.exp (-(L ^ α)) / 2 := by
  have hα'0 : 0 < α' := by linarith
  have hκ0 : 0 < 1 - α' * θ := by linarith
  -- the widths below the height `exp(L^{α'})`
  have h1 : ∀ᶠ L : ℝ in atTop, (L ^ α') ^ (-θ) ≤ η₀ :=
    ((tendsto_rpow_neg_atTop hθ0).comp (tendsto_rpow_atTop hα'0)).eventually (ge_mem_nhds hη₀)
  -- the low zeros: `L^α + log(2W) ≤ c e^{2L^κ}`
  have hx := tendsto_rpow_atTop hκ0
  have hlo := (isLittleO_rpow_exp_pos_mul_atTop (α / (1 - α' * θ))
    (show (0 : ℝ) < 2 by norm_num)).bound (show 0 < c / 2 by positivity)
  have h2a : ∀ᶠ L : ℝ in atTop, (L ^ (1 - α' * θ)) ^ (α / (1 - α' * θ)) ≤
      c / 2 * Real.exp (2 * L ^ (1 - α' * θ)) := by
    filter_upwards [hx.eventually hlo, hx.eventually (eventually_ge_atTop 0)] with L hL hL0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL0 _),
      abs_of_nonneg (Real.exp_pos _).le] at hL
    exact hL
  have h2b : ∀ᶠ L : ℝ in atTop, Real.log (2 * W) ≤ c / 2 * Real.exp (2 * L ^ (1 - α' * θ)) := by
    have : Tendsto (fun L : ℝ => c / 2 * Real.exp (2 * L ^ (1 - α' * θ))) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity)
        (Real.tendsto_exp_atTop.comp (hx.const_mul_atTop (by norm_num)))
    exact this.eventually (eventually_ge_atTop _)
  -- the high zeros
  have hy := tendsto_rpow_atTop hα'0
  have hratio : ∀ᶠ L : ℝ in atTop, L ^ (α - α') ≤ 1 / 2 := by
    have := (tendsto_rpow_neg_atTop (show 0 < α' - α by linarith)).eventually
      (ge_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))
    exact this.mono fun L hL => by rwa [show -(α' - α) = α - α' by ring] at hL
  have hlo3 := (isLittleO_pow_exp_pos_mul_atTop 1 (show (0 : ℝ) < 1 / 2 by norm_num)).bound
    (show (0 : ℝ) < 1 / 320 by norm_num)
  have h3a : ∀ᶠ L : ℝ in atTop, L ^ α' ≤ 1 / 320 * Real.exp (1 / 2 * L ^ α') := by
    filter_upwards [hy.eventually hlo3, hy.eventually (eventually_ge_atTop 0)] with L hL hL0
    rw [pow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0,
      abs_of_nonneg (Real.exp_pos _).le] at hL
    exact hL
  have h3b : ∀ᶠ L : ℝ in atTop, K ≤ L ^ α' := hy.eventually (eventually_ge_atTop K)
  filter_upwards [eventually_ge_atTop (1 : ℝ), h1, h2a, h2b, hratio, h3a, h3b] with
    L hL1 hL1' hL2a hL2b hLr hL3a hL3b
  have hL0 : 0 < L := by linarith
  refine ⟨hL1, hL1', ?_, ?_⟩
  · have e1 : (L ^ α') ^ (-θ) * L = L ^ (1 - α' * θ) := by
      rw [← Real.rpow_mul hL0.le, ← Real.rpow_add_one hL0.ne']
      congr 1; ring
    have e2 : (L ^ (1 - α' * θ)) ^ (α / (1 - α' * θ)) = L ^ α := by
      rw [← Real.rpow_mul hL0.le]; congr 1; field_simp
    rw [e2] at hL2a
    have hE := Real.exp_pos (2 * L ^ (1 - α' * θ))
    have hmain : L ^ α + Real.log (2 * W) ≤ c * Real.exp (2 * (L ^ α') ^ (-θ) * L) * L := by
      rw [show 2 * (L ^ α') ^ (-θ) * L = 2 * L ^ (1 - α' * θ) by rw [mul_assoc, e1]]
      nlinarith [mul_nonneg (mul_nonneg hc.le hE.le) (sub_nonneg.mpr hL1)]
    have hle : Real.exp (-(c * Real.exp (2 * (L ^ α') ^ (-θ) * L) * L)) ≤
        Real.exp (-(L ^ α) - Real.log (2 * W)) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_sub, Real.exp_log (by positivity)] at hle
    calc W * Real.exp (-(c * Real.exp (2 * (L ^ α') ^ (-θ) * L) * L))
        ≤ W * (Real.exp (-(L ^ α)) / (2 * W)) := mul_le_mul_of_nonneg_left hle hW.le
      _ = Real.exp (-(L ^ α)) / 2 := by field_simp
  · have hx0 : 0 ≤ L ^ α' := Real.rpow_nonneg hL0.le _
    have hsplit : L ^ α = L ^ (α - α') * L ^ α' := by
      rw [← Real.rpow_add hL0]; congr 1; ring
    have hLa : L ^ α ≤ L ^ α' / 2 := by rw [hsplit]; nlinarith
    have hexp : Real.exp (1 / 2 * L ^ α') * Real.exp (-(L ^ α')) = Real.exp (-(L ^ α' / 2)) := by
      rw [← Real.exp_add]; ring_nf
    have h4 : Real.exp (-(L ^ α' / 2)) ≤ Real.exp (-(L ^ α)) := Real.exp_le_exp.mpr (by linarith)
    have hE := Real.exp_pos (-(L ^ α'))
    calc 80 * (K + L ^ α') * Real.exp (-(L ^ α'))
        ≤ 80 * (2 * L ^ α') * Real.exp (-(L ^ α')) :=
          mul_le_mul_of_nonneg_right (by linarith) hE.le
      _ ≤ 160 * (1 / 320 * Real.exp (1 / 2 * L ^ α')) * Real.exp (-(L ^ α')) :=
          mul_le_mul_of_nonneg_right (by linarith) hE.le
      _ = Real.exp (-(L ^ α' / 2)) / 2 := by rw [← hexp]; ring
      _ ≤ Real.exp (-(L ^ α)) / 2 := by linarith

/-- **The exceptional phase set is superpolynomially small.**  For every `α < 3/2` there are `C`
and `Y` such that for `y ≥ Y`, every set `P` of primes in `(y, 2y]`, every `r ≥ 0` and `N ≥ 3`, at
most `C N^{|P|} exp(−(log y)^α)` phase vectors give a negative level-one JAS aggregate.  No
hypothesis on the zeros is used. -/
theorem exists_card_jasPhaseAggregate_re_neg_le_dyadic_superpoly {α : ℝ} (hα : α < 3 / 2) :
    ∃ C Y : ℝ, 1 < Y ∧ ∀ y : ℝ, Y ≤ y → ∀ (P : Finset Nat.Primes),
      (∀ p ∈ P, y < ((p : ℕ) : ℝ) ∧ ((p : ℕ) : ℝ) ≤ 2 * y) → ∀ (r : ℝ), 0 ≤ r → ∀ (N : ℕ), 3 ≤ N →
        ((Finset.univ.filter fun k : ↥P → Fin N => (jasPhaseAggregate 1 r N P k).re < 0).card : ℝ)
          ≤ C * (N : ℝ) ^ P.card * Real.exp (-(Real.log y ^ α)) := by
  obtain ⟨c, hc, C, Y₀, hC, hY₀, h⟩ := exists_card_jasPhaseAggregate_re_neg_le_dyadic_width
  -- exponents `α ≤ α₁ < α' < 3/2` and `2/3 < θ < 1/α'`
  obtain ⟨α₁, hα₁def⟩ : ∃ a : ℝ, a = max α 1 := ⟨_, rfl⟩
  have hα₁ : α₁ < 3 / 2 := by rw [hα₁def]; exact max_lt hα (by norm_num)
  have hαα₁ : α ≤ α₁ := by rw [hα₁def]; exact le_max_left _ _
  have hα₁1 : 1 ≤ α₁ := by rw [hα₁def]; exact le_max_right _ _
  obtain ⟨α', hα'def⟩ : ∃ a : ℝ, a = (α₁ + 3 / 2) / 2 := ⟨_, rfl⟩
  have hα₁α' : α₁ < α' := by rw [hα'def]; linarith
  have hα'32 : α' < 3 / 2 := by rw [hα'def]; linarith
  have hα'0 : 0 < α' := by linarith
  have hinv : 2 / 3 < 1 / α' := by rw [lt_div_iff₀ hα'0]; linarith
  obtain ⟨θ, hθdef⟩ : ∃ t : ℝ, t = (2 / 3 + 1 / α') / 2 := ⟨_, rfl⟩
  have hθ : 2 / 3 < θ := by rw [hθdef]; linarith
  have hθ0 : 0 < θ := by linarith
  have hκ : α' * θ < 1 := by
    have h1 : θ < 1 / α' := by rw [hθdef]; linarith
    rw [lt_div_iff₀ hα'0] at h1; linarith
  -- the zero-free region
  obtain ⟨t₁, ht₁, hvk⟩ := exists_powerLog_width_vk hθ
  obtain ⟨η₀, hη₀, hlow⟩ := exists_low_zero_width_at t₁
  -- the asymptotic conditions
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = |xiLineTwoLogDerivConstant| + Real.log 7 := ⟨_, rfl⟩
  have hK : 0 ≤ K := by
    rw [hKdef]; exact add_nonneg (abs_nonneg _) (Real.log_nonneg (by norm_num))
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (eventually_superpoly_conditions (α := α₁) (α' := α')
    (θ := θ) (η₀ := η₀) (c := c) (W := lagWeightTotal) (K := K) (by linarith) hα₁α' hθ0 hκ hη₀
    hc lagWeightTotal_pos hK)
  refine ⟨C, max Y₀ (Real.exp L₀), lt_of_lt_of_le hY₀ (le_max_left _ _), ?_⟩
  intro y hy P hP r hr N hN
  have hyY₀ : Y₀ ≤ y := le_trans (le_max_left _ _) hy
  have hy1 : 1 < y := lt_of_lt_of_le hY₀ hyY₀
  have hyL : L₀ ≤ Real.log y := by
    rw [← Real.log_exp L₀]
    exact Real.log_le_log (Real.exp_pos _) (le_trans (le_max_right _ _) hy)
  obtain ⟨hL1, hω, hlowb, hhighb⟩ := hL₀ (Real.log y) hyL
  refine (h y hyY₀ P hP r hr N hN).trans ?_
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log y := ⟨_, rfl⟩
  rw [← hLdef] at hL1 hω hlowb hhighb ⊢
  have hL0 : 0 < L := by linarith
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = Real.exp (L ^ α') := ⟨_, rfl⟩
  have hT1 : 1 ≤ T := by rw [hTdef]; exact Real.one_le_exp (Real.rpow_nonneg hL0.le _)
  have hlogT : Real.log T = L ^ α' := by rw [hTdef, Real.log_exp]
  -- the pointwise split of the zero sum
  obtain ⟨w, hwdef⟩ : ∃ w : XiZeroCopy → ℝ,
      w = fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := ⟨_, rfl⟩
  have hwn : Summable w := by rw [hwdef]; exact summable_inv_mul_one_sub.norm
  have hw0 : ∀ q, 0 ≤ w q := fun q => by rw [hwdef]; exact norm_nonneg _
  obtain ⟨b, hbdef⟩ : ∃ b : XiZeroCopy → ℝ, b = fun q =>
      Real.exp (-(c * Real.exp ((1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * L) * L)) := ⟨_, rfl⟩
  obtain ⟨βl, hβdef⟩ : ∃ β : ℝ, β = Real.exp (-(c * Real.exp (2 * (L ^ α') ^ (-θ) * L) * L)) :=
    ⟨_, rfl⟩
  obtain ⟨ind, hinddef⟩ : ∃ f : XiZeroCopy → ℝ,
      f = {q : XiZeroCopy | T < |(q.1 : ℂ).im|}.indicator w := ⟨_, rfl⟩
  have hindsum : Summable ind := by rw [hinddef]; exact hwn.indicator _
  have hb1 : ∀ q, b q ≤ 1 := fun q => by
    rw [hbdef]
    refine Real.exp_le_one_iff.mpr ?_
    have := Real.exp_pos ((1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * L)
    have : 0 ≤ c * Real.exp ((1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * L) * L := by positivity
    linarith
  have hpt : ∀ q, w q * b q ≤ ind q + w q * βl := by
    intro q
    by_cases hq : T < |(q.1 : ℂ).im|
    · have hi : ind q = w q := by
        rw [hinddef]; exact Set.indicator_of_mem (show q ∈ {q : XiZeroCopy | T < |(q.1 : ℂ).im|}
          from hq) w
      rw [hi]
      have := mul_le_mul_of_nonneg_left (hb1 q) (hw0 q)
      have : 0 ≤ w q * βl := mul_nonneg (hw0 q) (by rw [hβdef]; positivity)
      linarith
    · have hi : ind q = 0 := by
        rw [hinddef]; exact Set.indicator_of_notMem (show q ∉ {q : XiZeroCopy | T < |(q.1 : ℂ).im|}
          from hq) w
      rw [hi, zero_add]
      refine mul_le_mul_of_nonneg_left ?_ (hw0 q)
      push Not at hq
      have hωT : Real.log T ^ (-θ) ≤ η₀ := by rw [hlogT]; exact hω
      have hwid := width_of_vk_le hθ0 ht₁ hvk hlow hωT q hq
      rw [hlogT] at hwid
      rw [hbdef, hβdef]
      refine Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc.le) hL0.le))
      nlinarith
  have hsumwb : Summable fun q => w q * b q :=
    Summable.of_nonneg_of_le (fun q => mul_nonneg (hw0 q) (by rw [hbdef]; positivity))
      (fun q => by have := mul_le_mul_of_nonneg_left (hb1 q) (hw0 q); linarith) (hwn.mul_right 1)
      |>.congr fun q => rfl
  have hsum : ∑' q, w q * b q ≤ ∑' q, ind q + lagWeightTotal * βl := by
    refine (Summable.tsum_le_tsum hpt hsumwb (hindsum.add (hwn.mul_right βl))).trans (le_of_eq ?_)
    rw [hindsum.tsum_add (hwn.mul_right βl), tsum_mul_right]
    congr 2
    rw [hwdef]; rfl
  -- the tail above `T`
  have htail : ∑' q, ind q ≤ 80 * (K + L ^ α') * Real.exp (-(L ^ α')) := by
    have h0 := tsum_indicator_abs_im_gt_weight_le hT1
    rw [hinddef, hwdef]
    refine h0.trans ?_
    have hlog7 : Real.log (3 * T + 4) ≤ Real.log 7 + L ^ α' := by
      rw [← hlogT, ← Real.log_mul (by norm_num) (by linarith)]
      exact Real.log_le_log (by positivity) (by linarith)
    have hC1 : xiLineTwoLogDerivConstant ≤ |xiLineTwoLogDerivConstant| := le_abs_self _
    rw [div_eq_mul_inv, hTdef, ← Real.exp_neg, hKdef]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [← hTdef]
    linarith
  have hfinal : ∑' q, w q * b q ≤ Real.exp (-(L ^ α)) := by
    have hpow : L ^ α ≤ L ^ α₁ := Real.rpow_le_rpow_of_exponent_le hL1 hαα₁
    have hexp : Real.exp (-(L ^ α₁)) ≤ Real.exp (-(L ^ α)) := Real.exp_le_exp.mpr (by linarith)
    rw [← hβdef] at hlowb
    linarith
  have hsum' : ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
      Real.exp (-(c * Real.exp ((1 - 2 * |(q.1 : ℂ).re - 1 / 2|) * L) * L)) =
      ∑' q, w q * b q := by rw [hwdef, hbdef]
  rw [hsum']
  have hpos : 0 ≤ C * (N : ℝ) ^ P.card := by positivity
  exact mul_le_mul_of_nonneg_left hfinal hpos

end

end RHTower
