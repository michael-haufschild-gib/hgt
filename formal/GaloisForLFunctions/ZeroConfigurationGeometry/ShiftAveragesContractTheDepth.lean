import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Shift averages contract the depth

For a window `φ` with transform `f = φ̂`, the cosh-tilted window `2cosh(λu)φ` has transform
`f(z + iλ) + f(z − iλ)` (the pair formula of `TheCameraAndTheTilt` at `w = iλ`). The heat
multiplier `e^{tu²}` is a Gaussian average of `cosh(λu)`, and `e^{−tD²}` is the limit of iterated
shift averages `cos(λD/√n)^n`. This module proves the strict pointwise contraction of one
shift average in the polynomial model, de Bruijn's lemma.

* **Pair factors** (`pairFactor_lt`). For a conjugate pair `{ζ, ζ̄}`, `ζ = a + ib`, and
  `w± = x + i(y ± λ)`, the products `|w − ζ|²|w − ζ̄|²` satisfy
  `g(y + λ) − g(y − λ) = 8yλ((x − a)² + y² + λ² − b²)`.
* **De Bruijn's lemma** (`im_eq_zero_or_sq_add_sq_le_of_shiftAverage`). Let the roots of `p` form a
  configuration closed under conjugation, all of depth `|Im ζ| ≤ Δ`, and let `λ > 0`. Every root `z`
  of `p(z + iλ) + p(z − iλ)` is real or has `(Im z)² + λ² ≤ Δ²`. For `λ ≥ Δ` every root is real
  (`im_eq_zero_of_shiftAverage`).

* **De Bruijn's rate for iterated averages** (`roots_shiftAvgList_im_sq_le`). For a real
  polynomial (`IsRealPoly`), the averages over sizes `μ_1, …, μ_n` lower the squared depth bound
  from `D` to `max(D − Σ μ_j², 0)`. Realness is preserved by every average
  (`isRealPoly_shiftAvg`), which keeps the configuration closed under conjugation.

So one shift average lowers the squared maximal depth by `λ²`, pointwise for every point. `n`
averages of size `λ/√n` lower it by `λ²` and converge to the heat flow at time `t = λ²/2`, which
gives de Bruijn's rate `Δ² − 2t`. Here the configuration is any finite conjugation-closed one, with
no evenness. For even entire transforms of order one the same lemma is
`RHTower.DeBruijn.add_shift_ne_zero`, and the continuum assembly through the cosh-tilted kernels
`g·cosh(λx)^n → g·e^{tx²}` is `RHTower.DeBruijn.cosTransform_heat_zeros_im_sq_le`. This is the pointwise repulsion law of the field in finite
dimension. In window terms: tilting a window by `cosh(λu)` moves every zero of its transform toward
the real line, and a tilt `λ ≥ Δ` makes them all real.
-/

open Polynomial Complex
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-- `|w − ζ|² |w − ζ̄|²` for `w = x + iY`, `ζ = a + ib`. -/
theorem normSq_mul_normSq_conj (x Y a b : ℝ) :
    Complex.normSq (⟨x, Y⟩ - ⟨a, b⟩) * Complex.normSq (⟨x, Y⟩ - (starRingEnd ℂ) ⟨a, b⟩) =
      ((x - a) ^ 2 + (Y - b) ^ 2) * ((x - a) ^ 2 + (Y + b) ^ 2) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im]
  ring

/-- **The pair factor grows along the shift away from the line.** -/
theorem pairFactor_lt {x y lam a b : ℝ} (hy : 0 < y) (hl : 0 < lam)
    (hb : b ^ 2 < y ^ 2 + lam ^ 2) :
    ((x - a) ^ 2 + (y - lam - b) ^ 2) * ((x - a) ^ 2 + (y - lam + b) ^ 2) <
      ((x - a) ^ 2 + (y + lam - b) ^ 2) * ((x - a) ^ 2 + (y + lam + b) ^ 2) := by
  have hu : 0 ≤ (x - a) ^ 2 := sq_nonneg _
  have key : ((x - a) ^ 2 + (y + lam - b) ^ 2) * ((x - a) ^ 2 + (y + lam + b) ^ 2) -
      ((x - a) ^ 2 + (y - lam - b) ^ 2) * ((x - a) ^ 2 + (y - lam + b) ^ 2) =
      8 * y * lam * ((x - a) ^ 2 + y ^ 2 + lam ^ 2 - b ^ 2) := by ring
  have : 0 < 8 * y * lam * ((x - a) ^ 2 + y ^ 2 + lam ^ 2 - b ^ 2) := by
    have h1 : 0 < (x - a) ^ 2 + y ^ 2 + lam ^ 2 - b ^ 2 := by linarith
    positivity
  linarith

/-- A strict product inequality for nonnegative factors over a nonempty multiset. -/
theorem multiset_prod_lt_prod {ι : Type*} {s : Multiset ι} (hs : s ≠ 0) {f g : ι → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (hlt : ∀ i ∈ s, f i < g i) :
    (s.map f).prod < (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    have ha0 := h0 a (Multiset.mem_cons_self a s)
    have hag := hlt a (Multiset.mem_cons_self a s)
    have hf0 : 0 ≤ (s.map f).prod :=
      Multiset.prod_nonneg fun x hx => by
        obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hx
        exact h0 i (Multiset.mem_cons_of_mem hi)
    by_cases hs' : s = 0
    · simp [hs', hag]
    · have := ih hs' (fun i hi => h0 i (Multiset.mem_cons_of_mem hi))
        (fun i hi => hlt i (Multiset.mem_cons_of_mem hi))
      exact mul_lt_mul'' hag this ha0 hf0

/-- `|p(w)|⁴ = |c|⁴ ∏ |w − ζ|²|w − ζ̄|²` for a configuration closed under conjugation. -/
theorem norm_eval_pow_four {p : ℂ[X]} (hconj : p.roots.map (starRingEnd ℂ) = p.roots) (w : ℂ) :
    ‖p.eval w‖ ^ 4 = ‖p.leadingCoeff‖ ^ 4 *
      (p.roots.map fun ζ => Complex.normSq (w - ζ) * Complex.normSq (w - (starRingEnd ℂ) ζ)).prod := by
  have hev := (IsAlgClosed.splits p).eval_eq_prod_roots w
  have hsq : ‖p.eval w‖ ^ 2 = ‖p.leadingCoeff‖ ^ 2 *
      (p.roots.map fun ζ => Complex.normSq (w - ζ)).prod := by
    rw [hev, norm_mul, mul_pow, ← Complex.normSq_eq_norm_sq ((p.roots.map (w - ·)).prod),
      map_multiset_prod, Multiset.map_map]
    rfl
  have hsq' : (p.roots.map fun ζ => Complex.normSq (w - ζ)).prod =
      (p.roots.map fun ζ => Complex.normSq (w - (starRingEnd ℂ) ζ)).prod := by
    conv_lhs => rw [← hconj, Multiset.map_map]
    rfl
  rw [show ‖p.eval w‖ ^ 4 = (‖p.eval w‖ ^ 2) * (‖p.eval w‖ ^ 2) by ring, hsq]
  rw [show ‖p.leadingCoeff‖ ^ 2 * (p.roots.map fun ζ => Complex.normSq (w - ζ)).prod *
      (‖p.leadingCoeff‖ ^ 2 * (p.roots.map fun ζ => Complex.normSq (w - ζ)).prod) =
      ‖p.leadingCoeff‖ ^ 4 * ((p.roots.map fun ζ => Complex.normSq (w - ζ)).prod *
        (p.roots.map fun ζ => Complex.normSq (w - (starRingEnd ℂ) ζ)).prod) by rw [← hsq']; ring]
  rw [← Multiset.prod_map_mul]

/-- **One shift average moves every point toward the line**, upper half-plane form: for
`Im z > 0` with `(Im z)² + λ² > Δ²`, `|p(z + iλ)| > |p(z − iλ)|`. -/
theorem norm_eval_shift_lt {p : ℂ[X]} (hp0 : p ≠ 0) (hroots : p.roots ≠ 0)
    (hconj : p.roots.map (starRingEnd ℂ) = p.roots) {Δ lam : ℝ}
    (hstrip : ∀ ζ ∈ p.roots, |ζ.im| ≤ Δ) (hl : 0 < lam) {z : ℂ} (hy : 0 < z.im)
    (hz : Δ ^ 2 < z.im ^ 2 + lam ^ 2) :
    ‖p.eval (z - I * lam)‖ < ‖p.eval (z + I * lam)‖ := by
  have hc : 0 < ‖p.leadingCoeff‖ := norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hp0)
  have hfac : ∀ ζ ∈ p.roots,
      Complex.normSq (z - I * lam - ζ) * Complex.normSq (z - I * lam - (starRingEnd ℂ) ζ) <
        Complex.normSq (z + I * lam - ζ) * Complex.normSq (z + I * lam - (starRingEnd ℂ) ζ) := by
    intro ζ hζ
    have hb : ζ.im ^ 2 < z.im ^ 2 + lam ^ 2 := by
      have h1 := hstrip ζ hζ
      have h2 : ζ.im ^ 2 ≤ Δ ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      linarith
    have h := pairFactor_lt (x := z.re) (a := ζ.re) hy hl hb
    have e1 : z - I * lam = ⟨z.re, z.im - lam⟩ := Complex.ext (by simp) (by simp)
    have e2 : z + I * lam = ⟨z.re, z.im + lam⟩ := Complex.ext (by simp) (by simp)
    rw [e1, e2, show ζ = ⟨ζ.re, ζ.im⟩ from rfl, normSq_mul_normSq_conj, normSq_mul_normSq_conj]
    linarith
  have hlt := multiset_prod_lt_prod hroots
    (fun ζ _ => mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)) hfac
  have h4 : ‖p.eval (z - I * lam)‖ ^ 4 < ‖p.eval (z + I * lam)‖ ^ 4 := by
    rw [norm_eval_pow_four hconj, norm_eval_pow_four hconj]
    exact mul_lt_mul_of_pos_left hlt (by positivity)
  exact lt_of_pow_lt_pow_left₀ 4 (norm_nonneg _) h4

/-- A configuration closed under conjugation has `|p(w̄)| = |p(w)|`. -/
theorem norm_eval_conj {p : ℂ[X]} (hconj : p.roots.map (starRingEnd ℂ) = p.roots) (w : ℂ) :
    ‖p.eval ((starRingEnd ℂ) w)‖ = ‖p.eval w‖ := by
  have h4 : ‖p.eval ((starRingEnd ℂ) w)‖ ^ 4 = ‖p.eval w‖ ^ 4 := by
    rw [norm_eval_pow_four hconj, norm_eval_pow_four hconj]
    congr 2
    refine Multiset.map_congr rfl fun ζ _ => ?_
    have e1 : Complex.normSq ((starRingEnd ℂ) w - ζ) = Complex.normSq (w - (starRingEnd ℂ) ζ) := by
      rw [← Complex.normSq_conj, map_sub, Complex.conj_conj]
    have e2 : Complex.normSq ((starRingEnd ℂ) w - (starRingEnd ℂ) ζ) = Complex.normSq (w - ζ) := by
      rw [← map_sub, Complex.normSq_conj]
    rw [e1, e2, mul_comm]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (4 : ℕ) ≠ 0)).mp h4

/-- **De Bruijn's lemma.** Every root of the shift average `p(z + iλ) + p(z − iλ)` of a
conjugation-closed configuration of depth `≤ Δ` is real or has `(Im z)² + λ² ≤ Δ²`. -/
theorem im_eq_zero_or_sq_add_sq_le_of_shiftAverage {p : ℂ[X]} (hp0 : p ≠ 0)
    (hconj : p.roots.map (starRingEnd ℂ) = p.roots) {Δ lam : ℝ}
    (hstrip : ∀ ζ ∈ p.roots, |ζ.im| ≤ Δ) (hl : 0 < lam) {z : ℂ}
    (hz : p.eval (z + I * lam) + p.eval (z - I * lam) = 0) :
    z.im = 0 ∨ z.im ^ 2 + lam ^ 2 ≤ Δ ^ 2 := by
  by_contra h
  push Not at h
  obtain ⟨him, hΔ⟩ := h
  have heq : ‖p.eval (z + I * lam)‖ = ‖p.eval (z - I * lam)‖ := by
    rw [eq_neg_of_add_eq_zero_left hz, norm_neg]
  by_cases hroots : p.roots = 0
  · have hdeg : p.natDegree = 0 := by
      rw [← IsAlgClosed.card_roots_eq_natDegree (p := p), hroots, Multiset.card_zero]
    rw [eq_C_of_natDegree_eq_zero hdeg] at hz hp0
    simp only [eval_C] at hz
    have : p.coeff 0 = 0 := by linear_combination hz / 2
    exact hp0 (by rw [this, C_0])
  rcases lt_or_gt_of_ne him with hneg | hpos
  · -- reflect to the upper half-plane
    have hpos' : 0 < ((starRingEnd ℂ) z).im := by rw [Complex.conj_im]; linarith
    have hΔ' : Δ ^ 2 < ((starRingEnd ℂ) z).im ^ 2 + lam ^ 2 := by
      rw [Complex.conj_im, neg_sq]; exact hΔ
    have hlt := norm_eval_shift_lt hp0 hroots hconj hstrip hl hpos' hΔ'
    have e1 : (starRingEnd ℂ) z - I * lam = (starRingEnd ℂ) (z + I * lam) := by
      simp [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
    have e2 : (starRingEnd ℂ) z + I * lam = (starRingEnd ℂ) (z - I * lam) := by
      simp [map_sub, map_mul, Complex.conj_I, Complex.conj_ofReal]
    rw [e1, e2, norm_eval_conj hconj, norm_eval_conj hconj] at hlt
    linarith
  · have hlt := norm_eval_shift_lt hp0 hroots hconj hstrip hl hpos hΔ
    linarith

/-- **A shift of size `λ ≥ Δ` makes the configuration real.** -/
theorem im_eq_zero_of_shiftAverage {p : ℂ[X]} (hp0 : p ≠ 0)
    (hconj : p.roots.map (starRingEnd ℂ) = p.roots) {Δ lam : ℝ}
    (hstrip : ∀ ζ ∈ p.roots, |ζ.im| ≤ Δ) (hΔ0 : 0 ≤ Δ) (hl : 0 < lam) (hΔ : Δ ≤ lam) {z : ℂ}
    (hz : p.eval (z + I * lam) + p.eval (z - I * lam) = 0) : z.im = 0 := by
  rcases im_eq_zero_or_sq_add_sq_le_of_shiftAverage hp0 hconj hstrip hl hz with h | h
  · exact h
  · have h1 : Δ ^ 2 ≤ lam ^ 2 := pow_le_pow_left₀ hΔ0 hΔ 2
    have h2 : z.im ^ 2 ≤ 0 := by linarith
    exact pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm h2 (sq_nonneg _))

/-! ### Iterated shift averages: de Bruijn's rate -/

/-- The shift average `p(z + iμ) + p(z − iμ)` as a polynomial: the transform of the window tilted
by `2cosh(μu)`. -/
def shiftAvg (μ : ℝ) (p : ℂ[X]) : ℂ[X] := p.comp (X + C (I * μ)) + p.comp (X - C (I * μ))

theorem eval_shiftAvg (μ : ℝ) (p : ℂ[X]) (z : ℂ) :
    (shiftAvg μ p).eval z = p.eval (z + I * μ) + p.eval (z - I * μ) := by
  simp [shiftAvg, eval_comp]

/-- A polynomial with real coefficients: fixed by coefficientwise conjugation. -/
def IsRealPoly (p : ℂ[X]) : Prop := p.map (starRingEnd ℂ) = p

theorem roots_map_conj_of_isRealPoly {p : ℂ[X]} (hp : IsRealPoly p) :
    p.roots.map (starRingEnd ℂ) = p.roots := by
  have h := roots_map_of_injective_of_card_eq_natDegree (f := starRingEnd ℂ)
    (RingHom.injective _) (IsAlgClosed.card_roots_eq_natDegree (p := p))
  rw [h, hp]

theorem isRealPoly_shiftAvg {p : ℂ[X]} (hp : IsRealPoly p) (μ : ℝ) : IsRealPoly (shiftAvg μ p) := by
  have hc : (starRingEnd ℂ) (I * μ) = -(I * μ) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
  unfold IsRealPoly shiftAvg at *
  rw [Polynomial.map_add, map_comp, map_comp, hp, Polynomial.map_add, Polynomial.map_sub,
    map_X]
  simp only [map_C, hc, map_neg, sub_neg_eq_add, ← sub_eq_add_neg]
  rw [add_comm]

theorem shiftAvg_ne_zero {p : ℂ[X]} (hp : p ≠ 0) (μ : ℝ) : shiftAvg μ p ≠ 0 := by
  intro h
  have hlead : ∀ a : ℂ, (p.comp (X + C a)).coeff p.natDegree = p.leadingCoeff := fun a => by
    have hn : (p.comp (X + C a)).natDegree = p.natDegree := by
      rw [natDegree_comp, natDegree_X_add_C, mul_one]
    rw [← hn, coeff_natDegree, leadingCoeff_comp (by rw [natDegree_X_add_C]; exact one_ne_zero),
      leadingCoeff_X_add_C, one_pow, mul_one]
  have hc := congrArg (fun q : ℂ[X] => q.coeff p.natDegree) h
  simp only [shiftAvg, coeff_add, coeff_zero] at hc
  rw [sub_eq_add_neg, ← map_neg C, hlead, hlead] at hc
  have : p.leadingCoeff = 0 := by linear_combination hc / 2
  exact hp (leadingCoeff_eq_zero.mp this)

/-- **One shift average lowers the squared depth bound `D` to `max(D − μ², 0)`.** -/
theorem roots_shiftAvg_im_sq_le {p : ℂ[X]} (hreal : IsRealPoly p) (hp0 : p ≠ 0) {D μ : ℝ}
    (hD : 0 ≤ D) (hμ : 0 < μ) (hdepth : ∀ ζ ∈ p.roots, ζ.im ^ 2 ≤ D) :
    ∀ ζ ∈ (shiftAvg μ p).roots, ζ.im ^ 2 ≤ max (D - μ ^ 2) 0 := by
  intro z hz
  have hroot : (shiftAvg μ p).eval z = 0 := (mem_roots (shiftAvg_ne_zero hp0 μ)).mp hz
  rw [eval_shiftAvg] at hroot
  have hstrip : ∀ ζ ∈ p.roots, |ζ.im| ≤ Real.sqrt D := fun ζ hζ =>
    Real.abs_le_sqrt (hdepth ζ hζ)
  rcases im_eq_zero_or_sq_add_sq_le_of_shiftAverage hp0 (roots_map_conj_of_isRealPoly hreal)
    hstrip hμ hroot with h | h
  · rw [h]; simp
  · rw [Real.sq_sqrt hD] at h
    exact le_max_of_le_left (by linarith)

/-- The composite tilt `∏ 2cosh(μ_j u)`: iterated shift averages. -/
def shiftAvgList : List ℝ → ℂ[X] → ℂ[X]
  | [], p => p
  | μ :: μs, p => shiftAvg μ (shiftAvgList μs p)

theorem shiftAvgList_isReal_ne_zero {p : ℂ[X]} (hreal : IsRealPoly p) (hp0 : p ≠ 0) :
    ∀ μs : List ℝ, IsRealPoly (shiftAvgList μs p) ∧ shiftAvgList μs p ≠ 0
  | [] => ⟨hreal, hp0⟩
  | μ :: μs => by
    obtain ⟨h1, h2⟩ := shiftAvgList_isReal_ne_zero hreal hp0 μs
    exact ⟨isRealPoly_shiftAvg h1 μ, shiftAvg_ne_zero h2 μ⟩

/-- **De Bruijn's rate for iterated shift averages.** Tilting the window by `∏ 2cosh(μ_j u)`
lowers the squared maximal depth from `D` to `max(D − Σ μ_j², 0)`. With `Σ μ_j² = 2t` and
`μ_j → 0` the tilt `∏ cosh(μ_j u)` tends to the heat multiplier `e^{tu²}`. -/
theorem roots_shiftAvgList_im_sq_le {p : ℂ[X]} (hreal : IsRealPoly p) (hp0 : p ≠ 0) {D : ℝ}
    (hD : 0 ≤ D) (hdepth : ∀ ζ ∈ p.roots, ζ.im ^ 2 ≤ D) :
    ∀ μs : List ℝ, (∀ μ ∈ μs, 0 < μ) →
      ∀ ζ ∈ (shiftAvgList μs p).roots, ζ.im ^ 2 ≤ max (D - (μs.map fun μ => μ ^ 2).sum) 0
  | [], _ => fun ζ hζ => by
    simp only [shiftAvgList, List.map_nil, List.sum_nil, sub_zero] at hζ ⊢
    exact (hdepth ζ hζ).trans (le_max_left _ _)
  | μ :: μs, hpos => by
    obtain ⟨h1, h2⟩ := shiftAvgList_isReal_ne_zero hreal hp0 μs
    have ih := roots_shiftAvgList_im_sq_le hreal hp0 hD hdepth μs
      (fun ν hν => hpos ν (List.mem_cons_of_mem _ hν))
    have hstep := roots_shiftAvg_im_sq_le h1 h2 (le_max_right _ 0)
      (hpos μ List.mem_cons_self) ih
    intro ζ hζ
    have := hstep ζ hζ
    simp only [List.map_cons, List.sum_cons]
    refine this.trans ?_
    rcases le_total 0 (D - (μs.map fun μ => μ ^ 2).sum) with h | h
    · rw [max_eq_left h]
      exact max_le_max (by linarith) le_rfl
    · rw [max_eq_right h]
      have : D - (μ ^ 2 + (μs.map fun μ => μ ^ 2).sum) ≤ 0 := by nlinarith [sq_nonneg μ]
      simp [max_eq_right this, sq_nonneg]

end GaloisForLFunctions.ZeroConfigurationGeometry
