import GaloisForLFunctions.RHTower.WeilLagFunctionRecurrence

/-!
# Single-base lag sequences and isolated top levels

For a fixed integer base `b ≥ 2` the lag sequence `a_{b^m} = Φ(m log b)` samples the Weil lag
function on a lattice.  If the maximal real part `β₀ > ½` of the zeros is *attained*, then
`a_{b^m}` is unbounded above: along a sequence of exponents produced by simultaneous Dirichlet
approximation of the top-level ordinates, `a_{b^m} ≥ (c/2)·b^{m(β₀−½)}` with
`c = Σ_{β = β₀} Re(1/(ρ(1−ρ))) > 0`.  Real parts accumulating at `β₀` from below are harmless:
their contribution is `o(b^{m(β₀−½)})` by dominated convergence of the absolutely summable weights.
Consequently a bounded single-base lag sequence excludes every attained off-line maximal real
part, in particular any finite nonempty set of off-line zeros.  The only obstruction to the full
single-base criterion is a supremum of real parts that is not attained.
-/

open Complex Filter Real Topology
open GaloisForLFunctions.HTGeometry (latticeClose exists_simultaneous_dirichlet)

namespace RHTower

noncomputable section

/-- The real part of a lag weight is positive: `Re(ρ(1−ρ)) = β(1−β) + γ² > 0`. -/
theorem lagWeight_re_pos (q : XiZeroCopy) : 0 < (lagWeight q).re := by
  unfold lagWeight
  rw [one_div, Complex.inv_re]
  have hre := xiZeroCopy_re_pos q
  have hre1 := xiZeroCopy_re_lt_one q
  have hnum : 0 < ((q.1 : ℂ) * (1 - (q.1 : ℂ))).re := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      zero_sub, mul_neg, sub_neg_eq_add]
    nlinarith [sq_nonneg (q.1 : ℂ).im]
  have hne : (q.1 : ℂ) * (1 - (q.1 : ℂ)) ≠ 0 := by
    intro h; rw [h] at hnum; simp at hnum
  exact div_pos hnum (Complex.normSq_pos.mpr hne)

/-- The lag term as weight times exponential. -/
theorem weilLagTerm_eq (L : ℝ) (q : XiZeroCopy) :
    Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))
      = lagWeight q * Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) := by
  unfold lagWeight; rw [div_eq_mul_one_div, mul_comm]

theorem weilLagFunction_eq_tsum_lagWeight (L : ℝ) :
    weilLagFunction L = ∑' q : XiZeroCopy, lagWeight q * Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) := by
  unfold weilLagFunction
  exact tsum_congr fun q => weilLagTerm_eq L q

theorem summable_lagWeight_mul_exp (L : ℝ) :
    Summable fun q : XiZeroCopy => lagWeight q * Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) :=
  (summable_weilLagTerm L).congr fun q => weilLagTerm_eq L q

/-- **Attained top level.**  The real part `β₀` is attained by some zero copy and is maximal. -/
def AttainedTop (β₀ : ℝ) : Prop :=
  (∃ q : XiZeroCopy, (q.1 : ℂ).re = β₀) ∧ ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β₀

/-- The copies at the level `β₀`. -/
def topLevel (β₀ : ℝ) : Set XiZeroCopy := {q | (q.1 : ℂ).re = β₀}

/-- The real weight `Σ_{β = β₀} Re(1/(ρ(1−ρ)))` of the level `β₀`. -/
def topWeight (β₀ : ℝ) : ℝ := ∑' q : topLevel β₀, (lagWeight q).re

theorem summable_lagWeight_re_subtype (S : Set XiZeroCopy) :
    Summable fun q : S => (lagWeight q).re :=
  (summable_norm_lagWeight.subtype S).of_norm_bounded fun q => by
    rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _

theorem topWeight_pos {β₀ : ℝ} (h : ∃ q : XiZeroCopy, (q.1 : ℂ).re = β₀) : 0 < topWeight β₀ := by
  obtain ⟨q, hq⟩ := h
  have hs := summable_lagWeight_re_subtype (topLevel β₀)
  have hq' : q ∈ topLevel β₀ := hq
  exact lt_of_lt_of_le (lagWeight_re_pos q)
    (hs.le_tsum ⟨q, hq'⟩ fun r _ => (lagWeight_re_pos r).le)

/-- On the top level the exponential factors as modulus times unit phase. -/
theorem exp_lag_top {L β₀ : ℝ} {q : XiZeroCopy} (hq : (q.1 : ℂ).re = β₀) :
    Complex.exp (L * ((q.1 : ℂ) - 1 / 2))
      = (Real.exp (L * (β₀ - 1 / 2)) : ℂ) * Complex.exp (I * ((L * zeroOrdinate q : ℝ) : ℂ)) := by
  have e : (L : ℂ) * ((q.1 : ℂ) - 1 / 2)
      = ((L * (β₀ - 1 / 2) : ℝ) : ℂ) + I * ((L * zeroOrdinate q : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [zeroOrdinate, hq]
    · simp [zeroOrdinate]
  rw [e, Complex.exp_add, Complex.ofReal_exp]

/-- Below the level `β₁` the exponential is at most `e^{L(β₁−½)}` for `L ≥ 0`. -/
theorem norm_exp_lag_le {L β₁ : ℝ} (hL : 0 ≤ L) {q : XiZeroCopy} (hq : (q.1 : ℂ).re ≤ β₁) :
    ‖Complex.exp (L * ((q.1 : ℂ) - 1 / 2))‖ ≤ Real.exp (L * (β₁ - 1 / 2)) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have e : ((L : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = L * ((q.1 : ℂ).re - 1 / 2) := by
    simp [Complex.mul_re]
  rw [e]
  exact mul_le_mul_of_nonneg_left (by linarith) hL

/-- The lower-level tail `Σ_{β < β₀} ‖w‖ e^{−L(β₀−β)}` at the exponent `m`. -/
def lowerTail (β₀ b : ℝ) (m : ℕ) : ℝ :=
  ∑' q : ↑(topLevel β₀)ᶜ, ‖lagWeight q‖ * Real.exp (-((m : ℝ) * Real.log b * (β₀ - (q.1.1 : ℂ).re)))

/-- Below an attained maximum the lower tail tends to zero: dominated convergence. -/
theorem tendsto_lowerTail {β₀ b : ℝ} (hb : 1 < b) (hmax : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ β₀) :
    Tendsto (lowerTail β₀ b) atTop (𝓝 0) := by
  have hlogb : 0 < Real.log b := Real.log_pos hb
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop)
    (f := fun (m : ℕ) (q : ↑(topLevel β₀)ᶜ) =>
      ‖lagWeight q‖ * Real.exp (-((m : ℝ) * Real.log b * (β₀ - (q.1.1 : ℂ).re))))
    (g := fun _ => 0) (bound := fun q : ↑(topLevel β₀)ᶜ => ‖lagWeight q‖)
    (summable_norm_lagWeight.subtype _) ?_ ?_
  · rw [tsum_zero] at h
    exact h
  · intro q
    have hq : (q.1.1 : ℂ).re < β₀ := lt_of_le_of_ne (hmax q.1) q.2
    have hpos : 0 < Real.log b * (β₀ - (q.1.1 : ℂ).re) := by nlinarith
    have h1 : Tendsto (fun m : ℕ => (m : ℝ) * (Real.log b * (β₀ - (q.1.1 : ℂ).re))) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hpos
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul ‖lagWeight q‖
    simp only [mul_zero] at h2
    refine h2.congr fun m => ?_
    simp only [Function.comp_def]
    ring_nf
  · filter_upwards with m q
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (norm_nonneg _), abs_of_pos (Real.exp_pos _)]
    have hq : (q.1.1 : ℂ).re ≤ β₀ := hmax q.1
    have : Real.exp (-((m : ℝ) * Real.log b * (β₀ - (q.1.1 : ℂ).re))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (m : ℝ) * Real.log b * (β₀ - (q.1.1 : ℂ).re) := by
        apply mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hlogb.le); linarith
      linarith
    exact mul_le_of_le_one_right (norm_nonneg _) this

/-- The lower-level part of the lag value is at most `e^{L(β₀−½)}` times the lower tail. -/
theorem abs_re_lowerPart_le (β₀ : ℝ) (b m : ℕ) :
    |(∑' q : ↑(topLevel β₀)ᶜ, lagWeight q
        * Complex.exp (((m : ℝ) * Real.log b : ℝ) * ((q.1.1 : ℂ) - 1 / 2))).re|
      ≤ Real.exp ((m : ℝ) * Real.log b * (β₀ - 1 / 2)) * lowerTail β₀ b m := by
  set L : ℝ := (m : ℝ) * Real.log b with hLdef
  have hsum : Summable fun q : ↑(topLevel β₀)ᶜ =>
      lagWeight q * Complex.exp ((L : ℂ) * ((q.1.1 : ℂ) - 1 / 2)) :=
    (summable_lagWeight_mul_exp L).subtype _
  have hterm : ∀ q : ↑(topLevel β₀)ᶜ,
      ‖lagWeight q * Complex.exp ((L : ℂ) * ((q.1.1 : ℂ) - 1 / 2))‖
        = Real.exp (L * (β₀ - 1 / 2))
          * (‖lagWeight q‖ * Real.exp (-((m : ℝ) * Real.log b * (β₀ - (q.1.1 : ℂ).re)))) := by
    intro q
    rw [norm_mul, Complex.norm_exp]
    have e : ((L : ℂ) * ((q.1.1 : ℂ) - 1 / 2)).re = L * ((q.1.1 : ℂ).re - 1 / 2) := by
      simp [Complex.mul_re]
    rw [e, show L * ((q.1.1 : ℂ).re - 1 / 2)
        = L * (β₀ - 1 / 2) + -((m : ℝ) * Real.log b * (β₀ - (q.1.1 : ℂ).re)) by
        rw [hLdef]; ring, Real.exp_add]
    ring
  have h1 := (Complex.abs_re_le_norm _).trans (norm_tsum_le_tsum_norm hsum.norm)
  rw [tsum_congr hterm, tsum_mul_left] at h1
  exact h1

theorem integerLag_pow (b m : ℕ) :
    integerLag (b ^ m) = (weilLagFunction (m * Real.log b)).re := by
  unfold integerLag weilLagFunctionReal
  rw [Nat.cast_pow, Real.log_pow]

/-- The unit phase at the exponent `N m'` is within `2π/Q` of `1` on the approximated frequencies. -/
theorem norm_exp_phase_sub_one_le {γ b : ℝ} {N m' Q : ℕ}
    (hclose : latticeClose ((m' : ℝ) * (N * γ * Real.log b / (2 * π))) (1 / Q)) :
    ‖Complex.exp (I * ((((N * m' : ℕ) : ℝ) * Real.log b * γ : ℝ) : ℂ)) - 1‖ ≤ 2 * π / Q := by
  obtain ⟨p, hp⟩ := hclose
  set x : ℝ := 2 * π * ((m' : ℝ) * (N * γ * Real.log b / (2 * π)) - p) with hx
  have hθ : (((N * m' : ℕ) : ℝ) * Real.log b * γ : ℝ) = x + p * (2 * π) := by
    rw [hx]; push_cast; field_simp; ring
  have hper : Complex.exp (I * ((p * (2 * π) : ℝ) : ℂ)) = 1 := by
    push_cast
    rw [show I * ((p : ℂ) * (2 * π)) = (p : ℂ) * (2 * π * I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I p
  rw [hθ, Complex.ofReal_add, mul_add, Complex.exp_add, hper, mul_one]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, hx, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  calc 2 * π * |(m' : ℝ) * (N * γ * Real.log b / (2 * π)) - p| ≤ 2 * π * (1 / Q) :=
        mul_le_mul_of_nonneg_left hp.le (by positivity)
    _ = 2 * π / Q := by ring

/-- **An attained off-line maximal real part is detected by every base.**  If some `β₀ > ½` is
attained and maximal among the real parts of the zeros, then the single-base lag sequence
`a_{b^m}` is unbounded above for every integer base `b ≥ 2`. -/
theorem exists_pow_integerLag_gt_of_attainedTop {β₀ : ℝ} (hβ : 1 / 2 < β₀)
    (h : AttainedTop β₀) {b : ℕ} (hb : 2 ≤ b) (M : ℝ) :
    ∃ m : ℕ, 1 ≤ m ∧ M < integerLag (b ^ m) := by
  classical
  obtain ⟨htop, hmax⟩ := h
  set c := topWeight β₀ with hcdef
  have hc : 0 < c := topWeight_pos htop
  set W := ∑' q : XiZeroCopy, ‖lagWeight q‖ with hWdef
  have hW0 : 0 ≤ W := tsum_nonneg fun q => norm_nonneg _
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hlogb : 0 < Real.log b := Real.log_pos hb1
  set T := topLevel β₀ with hTdef
  -- (1) a finite subset of the top level carrying all but `c/8` of the weight
  have hsT : Summable fun q : T => ‖lagWeight q‖ := summable_norm_lagWeight.subtype T
  have hsTre := summable_lagWeight_re_subtype T
  have htail := tendsto_tsum_compl_atTop_zero (fun q : T => ‖lagWeight q‖)
  obtain ⟨F, hF⟩ :=
    Filter.eventually_atTop.mp (htail.eventually_lt_const (by linarith : (0 : ℝ) < c / 8))
  have hFtail : ∑' q : {x : T // x ∉ F}, ‖lagWeight q‖ < c / 8 := hF F le_rfl
  -- (2) the resolution of the simultaneous approximation
  set Q : ℕ := ⌈16 * π * W / c⌉₊ + 1 with hQdef
  have hQ0 : 0 < Q := by omega
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hQge : 16 * π * W / c ≤ Q := by
    have := Nat.le_ceil (16 * π * W / c); rw [hQdef]; push_cast; linarith
  have hQW : W * (2 * π / Q) ≤ c / 8 := by
    rw [← mul_div_assoc, div_le_iff₀ hQpos]
    have := (div_le_iff₀ hc).mp hQge
    nlinarith [Real.pi_pos]
  -- (3) the scale `N`: the lower tail is below `c/8` and the top modulus beats `M`
  set r₂ := Real.exp (Real.log b * (β₀ - 1 / 2)) with hr₂
  have hr₂1 : 1 < r₂ := Real.one_lt_exp_iff.mpr (by nlinarith)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_lowerTail hb1 hmax).eventually (eventually_le_nhds (by linarith : (0 : ℝ) < c / 8)))
  obtain ⟨N₂, hN₂⟩ := pow_unbounded_of_one_lt (2 * M / c) hr₂1
  set N := max N₁ N₂ + 1 with hNdef
  have hN0 : 0 < N := by omega
  -- (4) Dirichlet on the scaled top-level frequencies
  let e := F.equivFin
  let β : Fin F.card → ℝ := fun i => N * zeroOrdinate (e.symm i).1 * Real.log b / (2 * π)
  obtain ⟨m', hm'1, -, hclose⟩ := exists_simultaneous_dirichlet β hQ0
  set m := N * m' with hmdef
  have hmN : N ≤ m := by rw [hmdef]; exact Nat.le_mul_of_pos_right N hm'1
  refine ⟨m, by omega, ?_⟩
  set L : ℝ := m * Real.log b with hLdef
  have hL0 : 0 ≤ L := by positivity
  -- the phases on `F`
  have hphase : ∀ q ∈ F,
      ‖Complex.exp (I * ((L * zeroOrdinate q.1 : ℝ) : ℂ)) - 1‖ ≤ 2 * π / Q := by
    intro q hq
    have hc' := hclose (e ⟨q, hq⟩)
    have hβ' : β (e ⟨q, hq⟩) = N * zeroOrdinate q.1 * Real.log b / (2 * π) := by
      simp only [β, Equiv.symm_apply_apply]
    rw [hβ'] at hc'
    have := norm_exp_phase_sub_one_le (b := b) (N := N) (m' := m') hc'
    rw [hLdef, hmdef]
    have e' : (((N * m' : ℕ) : ℝ) * Real.log b * zeroOrdinate q.1 : ℝ)
        = ((N * m' : ℕ) : ℝ) * Real.log b * zeroOrdinate q.1 := rfl
    convert this using 4
  -- (5) the value as a top part plus a lower part
  set f : XiZeroCopy → ℂ := fun q => lagWeight q * Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) with hfdef
  have hf : Summable f := summable_lagWeight_mul_exp L
  have hval : integerLag (b ^ m) = (∑' q : T, f q).re + (∑' q : ↑Tᶜ, f q).re := by
    rw [integerLag_pow, weilLagFunction_eq_tsum_lagWeight, ← hLdef,
      ← hf.tsum_subtype_add_tsum_subtype_compl T, Complex.add_re]
  -- top part
  set g : T → ℂ := fun q => lagWeight q * Complex.exp (I * ((L * zeroOrdinate q.1 : ℝ) : ℂ))
    with hgdef
  have hg : Summable g := by
    refine (summable_norm_lagWeight.subtype T).of_norm_bounded fun q => ?_
    rw [hgdef]; simp only [norm_mul]
    rw [Complex.norm_exp]
    simp
  have hgre : Summable fun q : T => (g q).re :=
    hg.norm.of_norm_bounded fun q => by rw [Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
  have htopval : (∑' q : T, f q).re = Real.exp (L * (β₀ - 1 / 2)) * ∑' q : T, (g q).re := by
    have e1 : ∀ q : T, f q = (Real.exp (L * (β₀ - 1 / 2)) : ℂ) * g q := by
      intro q
      have hq : ((q.1).1 : ℂ).re = β₀ := q.2
      simp only [hfdef, hgdef]
      rw [exp_lag_top hq]; ring
    rw [tsum_congr e1, tsum_mul_left, Complex.re_ofReal_mul, Complex.re_tsum hg]
  -- the top sum is at least `5c/8`
  have hgnorm : ∀ q : T, ‖g q‖ = ‖lagWeight q‖ := by
    intro q; rw [hgdef]; simp only [norm_mul]; rw [Complex.norm_exp]; simp
  have hgF : ∀ q ∈ F, (lagWeight q).re - ‖lagWeight q‖ * (2 * π / Q) ≤ (g q).re := by
    intro q hq
    have hsplit : g q = lagWeight q + lagWeight q * (Complex.exp (I * ((L * zeroOrdinate q.1 : ℝ) : ℂ)) - 1) := by
      rw [hgdef]; ring
    rw [hsplit, Complex.add_re]
    have h1 : -(‖lagWeight q‖ * (2 * π / Q))
        ≤ (lagWeight q * (Complex.exp (I * ((L * zeroOrdinate q.1 : ℝ) : ℂ)) - 1)).re := by
      have := neg_le_of_abs_le (Complex.abs_re_le_norm
        (lagWeight q * (Complex.exp (I * ((L * zeroOrdinate q.1 : ℝ) : ℂ)) - 1)))
      rw [norm_mul] at this
      have h2 := mul_le_mul_of_nonneg_left (hphase q hq) (norm_nonneg (lagWeight q))
      linarith
    linarith
  have hsplitT := hgre.sum_add_tsum_compl (s := F)
  have hsplitW := hsTre.sum_add_tsum_compl (s := F)
  have hFnorm : ∑ q ∈ F, ‖lagWeight q‖ ≤ W := by
    calc ∑ q ∈ F, ‖lagWeight q‖ ≤ ∑' q : T, ‖lagWeight q‖ := hsT.sum_le_tsum F fun q _ => norm_nonneg _
      _ ≤ W := by
          rw [hWdef]
          exact Summable.tsum_subtype_le (fun q => ‖lagWeight q‖) T (fun q => norm_nonneg _)
            summable_norm_lagWeight
  have hFre : c - c / 8 ≤ ∑ q ∈ F, (lagWeight q).re := by
    have hre_le : ∑' q : {x : T // x ∉ F}, (lagWeight q).re ≤ ∑' q : {x : T // x ∉ F}, ‖lagWeight q‖ :=
      Summable.tsum_le_tsum (fun q => Complex.re_le_norm _) (hsTre.subtype _) (hsT.subtype _)
    have e' : ∑' q : ↑(↑F : Set T)ᶜ, (lagWeight q).re = ∑' q : {x : T // x ∉ F}, (lagWeight q).re := rfl
    have hcval : c = ∑' q : T, (lagWeight q).re := rfl
    linarith
  have hFg : ∑ q ∈ F, (lagWeight q).re - c / 8 ≤ ∑ q ∈ F, (g q).re := by
    have h1 : ∑ q ∈ F, ((lagWeight q).re - ‖lagWeight q‖ * (2 * π / Q)) ≤ ∑ q ∈ F, (g q).re :=
      Finset.sum_le_sum hgF
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul] at h1
    have h2 : (∑ q ∈ F, ‖lagWeight q‖) * (2 * π / Q) ≤ W * (2 * π / Q) :=
      mul_le_mul_of_nonneg_right hFnorm (by positivity)
    linarith
  have hgtail : |∑' q : {x : T // x ∉ F}, (g q).re| ≤ c / 8 := by
    have h1 : |∑' q : ↑(↑F : Set T)ᶜ, (g q).re| ≤ ∑' q : ↑(↑F : Set T)ᶜ, ‖(g q).re‖ := by
      rw [← Real.norm_eq_abs]
      exact norm_tsum_le_tsum_norm (hgre.norm.subtype _)
    have h2 : ∑' q : ↑(↑F : Set T)ᶜ, ‖(g q).re‖ ≤ ∑' q : ↑(↑F : Set T)ᶜ, ‖lagWeight q‖ := by
      refine Summable.tsum_le_tsum (fun q => ?_) (hgre.norm.subtype _) (hsT.subtype _)
      rw [← hgnorm q, Real.norm_eq_abs]; exact Complex.abs_re_le_norm _
    have e' : ∑' q : ↑(↑F : Set T)ᶜ, ‖lagWeight q‖ = ∑' q : {x : T // x ∉ F}, ‖lagWeight q‖ := rfl
    have e'' : ∑' q : ↑(↑F : Set T)ᶜ, (g q).re = ∑' q : {x : T // x ∉ F}, (g q).re := rfl
    rw [← e'']
    linarith
  have htopge : 5 * c / 8 ≤ ∑' q : T, (g q).re := by
    have e'' : ∑' q : ↑(↑F : Set T)ᶜ, (g q).re = ∑' q : {x : T // x ∉ F}, (g q).re := rfl
    have := (abs_le.mp hgtail).1
    linarith
  -- lower part
  have hlow : |(∑' q : ↑Tᶜ, f q).re| ≤ Real.exp (L * (β₀ - 1 / 2)) * lowerTail β₀ b m :=
    abs_re_lowerPart_le β₀ b m
  -- (6) the numerics
  have hexp2 : Real.exp (L * (β₀ - 1 / 2)) = r₂ ^ m := by
    rw [hr₂, ← Real.exp_nat_mul, hLdef]; congr 1; ring
  have hr₂m : 2 * M / c < r₂ ^ m := by
    calc 2 * M / c < r₂ ^ N₂ := hN₂
      _ ≤ r₂ ^ m := pow_le_pow_right₀ hr₂1.le (by omega)
  have htailm : lowerTail β₀ b m ≤ c / 8 := hN₁ m (by omega)
  have hMr : M < c / 2 * r₂ ^ m := by
    have := (div_lt_iff₀ hc).mp hr₂m
    linarith
  rw [hval, htopval]
  have hlow' := (abs_le.mp hlow).1
  rw [hexp2] at hlow' ⊢
  have hr₂pos : 0 < r₂ ^ m := by positivity
  have hkey : r₂ ^ m * (5 * c / 8) ≤ r₂ ^ m * ∑' q : T, (g q).re :=
    mul_le_mul_of_nonneg_left htopge hr₂pos.le
  have hkey2 : r₂ ^ m * lowerTail β₀ b m ≤ r₂ ^ m * (c / 8) :=
    mul_le_mul_of_nonneg_left htailm hr₂pos.le
  nlinarith

/-- A bounded single-base lag sequence excludes every attained off-line maximal real part. -/
theorem not_attainedTop_of_forall_le {b : ℕ} (hb : 2 ≤ b) {M : ℝ}
    (hM : ∀ m : ℕ, integerLag (b ^ m) ≤ M) {β₀ : ℝ} (hβ : 1 / 2 < β₀) : ¬ AttainedTop β₀ := by
  intro h
  obtain ⟨m, -, hm⟩ := exists_pow_integerLag_gt_of_attainedTop hβ h hb M
  exact absurd (hM m) (not_le.mpr hm)

/-- The off-line zero copies. -/
def offLineCopies : Set XiZeroCopy := {q | (q.1 : ℂ).re ≠ 1 / 2}

/-- A finite nonempty set of off-line copies has an attained maximal real part above `½`. -/
theorem exists_attainedTop_of_finite_offLine (hfin : offLineCopies.Finite)
    (hne : offLineCopies.Nonempty) : ∃ β₀ : ℝ, 1 / 2 < β₀ ∧ AttainedTop β₀ := by
  classical
  set Re : Finset ℝ := hfin.toFinset.image fun q : XiZeroCopy => (q.1 : ℂ).re with hRe
  have hmemRe : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≠ 1 / 2 → (q.1 : ℂ).re ∈ Re := by
    intro q hq
    rw [hRe, Finset.mem_image]
    exact ⟨q, by rw [Set.Finite.mem_toFinset]; exact hq, rfl⟩
  set Rs : Finset ℝ := Re.filter fun r => 1 / 2 < r with hRs
  have hRsne : Rs.Nonempty := by
    obtain ⟨q, hq⟩ := hne
    have hq' : (q.1 : ℂ).re ≠ 1 / 2 := hq
    rcases lt_or_gt_of_ne hq' with hlt | hgt
    · refine ⟨((xiZeroCopyReflectEquiv q).1 : ℂ).re, ?_⟩
      rw [hRs, Finset.mem_filter]
      have hval : ((xiZeroCopyReflectEquiv q).1 : ℂ).re = 1 - (q.1 : ℂ).re := by
        rw [xiZeroCopy_reflect_val, Complex.sub_re, Complex.one_re]
      refine ⟨hmemRe _ (by rw [hval]; intro h; linarith), by rw [hval]; linarith⟩
    · exact ⟨_, by rw [hRs, Finset.mem_filter]; exact ⟨hmemRe q hq', hgt⟩⟩
  set β₀ := Rs.max' hRsne with hβ₀
  have hβ₀half : 1 / 2 < β₀ := (Finset.mem_filter.mp (Rs.max'_mem hRsne)).2
  refine ⟨β₀, hβ₀half, ?_, ?_⟩
  · obtain ⟨q, hq⟩ := Finset.mem_image.mp (Finset.mem_filter.mp (Rs.max'_mem hRsne)).1
    exact ⟨q, hq.2⟩
  · intro q
    rcases le_or_gt ((q.1 : ℂ).re) (1 / 2) with hle | hgt
    · linarith
    · have hmem : (q.1 : ℂ).re ∈ Rs := by
        rw [hRs, Finset.mem_filter]; exact ⟨hmemRe q (by linarith), hgt⟩
      exact Rs.le_max' _ hmem

/-- **Finitely many off-line zeros are detected by every base.**  If the off-line copies form a
finite nonempty set, every single-base lag sequence is unbounded above. -/
theorem exists_pow_integerLag_gt_of_finite_offLine (hfin : offLineCopies.Finite)
    (hne : offLineCopies.Nonempty) {b : ℕ} (hb : 2 ≤ b) (M : ℝ) :
    ∃ m : ℕ, 1 ≤ m ∧ M < integerLag (b ^ m) := by
  obtain ⟨β₀, hβ, h⟩ := exists_attainedTop_of_finite_offLine hfin hne
  exact exists_pow_integerLag_gt_of_attainedTop hβ h hb M

/-- RH follows if every zero copy lies on the critical line. -/
theorem riemannHypothesis_of_forall_xiZeroCopy_re_eq_half_weilLagFunctionSingleBase
    (h : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2) : RiemannHypothesis := by
  intro s hζ htriv h1
  have hxi : xi s = 0 := xi_eq_zero_of_zeta_eq_zero hζ (fun ⟨n, hn⟩ => htriv ⟨n, hn⟩) h1
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
  rw [← hq]; exact h q

/-- **Single-base dichotomy.**  A bounded single-base lag sequence forces either RH or infinitely
many off-line zero copies. -/
theorem riemannHypothesis_or_infinite_offLine_of_forall_le {b : ℕ} (hb : 2 ≤ b) {M : ℝ}
    (hM : ∀ m : ℕ, integerLag (b ^ m) ≤ M) :
    RiemannHypothesis ∨ offLineCopies.Infinite := by
  by_cases hfin : offLineCopies.Finite
  · left
    apply riemannHypothesis_of_forall_xiZeroCopy_re_eq_half_weilLagFunctionSingleBase
    intro q
    by_contra hq
    have hne : offLineCopies.Nonempty := ⟨q, hq⟩
    obtain ⟨m, -, hm⟩ := exists_pow_integerLag_gt_of_finite_offLine hfin hne hb M
    exact absurd (hM m) (not_le.mpr hm)
  · exact Or.inr hfin

/-- **Single-base dichotomy, supremum form.**  A bounded single-base lag sequence forces either RH
or a supremum of real parts that is not attained: no zero copy has maximal real part. -/
theorem riemannHypothesis_or_not_attained_of_forall_le {b : ℕ} (hb : 2 ≤ b) {M : ℝ}
    (hM : ∀ m : ℕ, integerLag (b ^ m) ≤ M) :
    RiemannHypothesis ∨ ∀ q₀ : XiZeroCopy, ∃ q : XiZeroCopy, (q₀.1 : ℂ).re < (q.1 : ℂ).re := by
  by_cases hRH : RiemannHypothesis
  · exact Or.inl hRH
  right
  intro q₀
  by_contra hno
  push Not at hno
  -- `q₀` has maximal real part; it is off the line since RH fails
  have hmax : AttainedTop (q₀.1 : ℂ).re := ⟨⟨q₀, rfl⟩, fun q => hno q⟩
  have hβ : 1 / 2 < (q₀.1 : ℂ).re := by
    by_contra hle
    push Not at hle
    apply hRH
    apply riemannHypothesis_of_forall_xiZeroCopy_re_eq_half_weilLagFunctionSingleBase
    intro q
    -- every copy has real part `≤ ½`, and by reflection `≥ ½`
    have h1 : (q.1 : ℂ).re ≤ 1 / 2 := (hno q).trans hle
    have h2 : ((xiZeroCopyReflectEquiv q).1 : ℂ).re ≤ 1 / 2 :=
      (hno (xiZeroCopyReflectEquiv q)).trans hle
    rw [xiZeroCopy_reflect_val, Complex.sub_re, Complex.one_re] at h2
    linarith
  exact not_attainedTop_of_forall_le hb hM hβ hmax

end

end RHTower
