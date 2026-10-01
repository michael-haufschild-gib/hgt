import GaloisForLFunctions.HTGeometry.BohrFiniteRecurrence
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.Complex.Hadamard

/-!
# Recurrence on the boundedness half-plane, and the pole obstruction for every coefficient class

`not_tendsto_lseries_atTop_of_bounded_datum` needs absolute convergence on every line `σ > 1`. This
module replaces that hypothesis by holomorphy on `Re s > 1` together with absolute convergence on
some far line.

* **Uniform recurrence** (`exists_large_lseries_shift_near`). An absolutely convergent Dirichlet
  series returns uniformly close to itself under a vertical translation `s ↦ s + it`, uniformly on
  `Re s ≥ u` and at times `t` beyond any threshold. This is the simultaneous recurrence of finitely
  many characters plus a tail.
* **Three lines** (`exists_large_shift_near_of_bounded`). If `G` is holomorphic and bounded on a
  closed vertical strip `l ≤ Re s ≤ u` and recurs uniformly on `Re s = u`, then it recurs on every
  interior line. The difference `G(s + it) − G(s)` is at most `2B` on the left edge and small on the
  right edge, so Hadamard's three-lines theorem makes it small inside.
* **Pole obstruction** (`re_le_of_bounded_datum_holomorphic`). Let `L` be holomorphic on `Re s > 1`,
  equal to a real Dirichlet series absolutely convergent on some line, with
  `Re L(s) ≤ C + Re 1/(s − 1)` on `Re s > 1`. Apply recurrence to `G = e^L`, which is bounded on
  every strip `Re s ≥ l > 1`. At large heights `|G| ≤ e^{C + o(1)}`, so `L(σ) ≤ C` for every
  `σ > 1`, and `L` carries no pole at `s = 1` (`not_tendsto_re_atTop_of_bounded_datum_holomorphic`).
-/

open Complex Filter Topology Set

noncomputable section

namespace RHTower.BoundedDatumPoleObstruction

open GaloisForLFunctions

/-! ## Uniform recurrence of an absolutely convergent Dirichlet series -/

/-- A vertical translate of a Dirichlet term: `term a (s + it) n = term a s n · e^{i t (−log n)}`. -/
theorem term_add_mul_I (a : ℕ → ℂ) (s : ℂ) (t : ℝ) (n : ℕ) :
    LSeries.term a (s + (t : ℂ) * I) n =
      LSeries.term a s n * cexp (I * ((t : ℂ) * ((-Real.log n : ℝ) : ℂ))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_def]
  · rw [LSeries.term_of_ne_zero hn.ne', LSeries.term_of_ne_zero hn.ne']
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [cpow_add _ _ hn0, cpow_def_of_ne_zero hn0 ((t : ℂ) * I)]
    have hlog : Complex.log (n : ℂ) = ((Real.log n : ℝ) : ℂ) := by
      rw [ofReal_log (Nat.cast_nonneg n)]; push_cast; rfl
    rw [hlog]
    have he : cexp (I * ((t : ℂ) * ((-Real.log n : ℝ) : ℂ))) =
        (cexp (((Real.log n : ℝ) : ℂ) * ((t : ℂ) * I)))⁻¹ := by
      rw [← Complex.exp_neg]; congr 1; push_cast; ring
    rw [he]
    field_simp

/-- `‖term a s n‖ ≤ ‖a n‖ n^{−u}` on `Re s ≥ u`. -/
theorem norm_term_le_of_le_re (a : ℕ → ℂ) {u : ℝ} {s : ℂ} (hs : u ≤ s.re) (n : ℕ) :
    ‖LSeries.term a s n‖ ≤ ‖a n‖ * (n : ℝ) ^ (-u) := by
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
      (norm_nonneg _)

/-- **Uniform recurrence.** If `Σ ‖a n‖ n^{−u} < ∞`, then at times beyond any threshold the vertical
translate of `L(s) = Σ a_n n^{−s}` is uniformly within `ε` of `L` on `Re s ≥ u`. -/
theorem exists_large_lseries_shift_near (a : ℕ → ℂ) {u : ℝ}
    (hsum : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-u)) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ t : ℝ, R ≤ t ∧ ∀ s : ℂ, u ≤ s.re →
      ‖LSeries a (s + (t : ℂ) * I) - LSeries a s‖ ≤ ε := by
  set c : ℕ → ℝ := fun n => ‖a n‖ * (n : ℝ) ^ (-u) with hc
  have hc0 : ∀ n, 0 ≤ c n := fun n => by positivity
  -- the tail
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (tendsto_sum_nat_add c)) (ε / 4) (by positivity)
  have hNt : ∑' k, c (k + N) ≤ ε / 4 := by
    have := hN N le_rfl
    rw [Real.dist_eq, sub_zero] at this
    exact (le_abs_self _).trans this.le
  set S : ℝ := ∑ n ∈ Finset.range N, c n with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun n _ => hc0 n
  set δ : ℝ := ε / (2 * (S + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨t, htR, ht⟩ := exists_large_simultaneous_almostPeriod
    (fun j : Fin N => -Real.log (j : ℕ)) hδ0 R
  refine ⟨t, htR, fun s hs => ?_⟩
  set e : ℕ → ℂ := fun n => cexp (I * ((t : ℂ) * ((-Real.log n : ℝ) : ℂ))) with he
  have he1 : ∀ n, ‖e n - 1‖ ≤ 2 := by
    intro n
    have h : I * ((t : ℂ) * ((-Real.log n : ℝ) : ℂ)) = ((t * -Real.log n : ℝ) : ℂ) * I := by
      push_cast; ring
    calc ‖e n - 1‖ ≤ ‖e n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by simp only [he, h, norm_exp_ofReal_mul_I, norm_one]; norm_num
  have heN : ∀ n, n < N → ‖e n - 1‖ ≤ δ := fun n hn => by
    simpa [he] using ht ⟨n, hn⟩
  set b : ℕ → ℝ := fun n => c n * ‖e n - 1‖ with hb
  have hb0 : ∀ n, 0 ≤ b n := fun n => mul_nonneg (hc0 n) (norm_nonneg _)
  have hbs : Summable b :=
    Summable.of_nonneg_of_le hb0 (fun n => mul_le_mul_of_nonneg_left (he1 n) (hc0 n))
      (hsum.mul_right 2)
  have hterm : ∀ n, ‖LSeries.term a (s + (t : ℂ) * I) n - LSeries.term a s n‖ ≤ b n := by
    intro n
    rw [term_add_mul_I, ← mul_sub_one, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_term_le_of_le_re a hs n) (norm_nonneg _)
  have hsum1 : LSeriesSummable a (s + (t : ℂ) * I) :=
    Summable.of_norm_bounded hsum fun n => norm_term_le_of_le_re a (by simpa using hs) n
  have hsum2 : LSeriesSummable a s :=
    Summable.of_norm_bounded hsum fun n => norm_term_le_of_le_re a hs n
  have hdiff : LSeries a (s + (t : ℂ) * I) - LSeries a s =
      ∑' n, (LSeries.term a (s + (t : ℂ) * I) n - LSeries.term a s n) := by
    rw [LSeries, LSeries, hsum1.tsum_sub hsum2]
  rw [hdiff]
  refine (tsum_of_norm_bounded hbs.hasSum hterm).trans ?_
  rw [← hbs.sum_add_tsum_nat_add N]
  have h1 : ∑ n ∈ Finset.range N, b n ≤ δ * S := by
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [mul_comm δ]
    exact mul_le_mul_of_nonneg_left (heN n (Finset.mem_range.mp hn)) (hc0 n)
  have h2 : ∑' k, b (k + N) ≤ 2 * ∑' k, c (k + N) := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun k => by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left (he1 _) (hc0 _))
      ((summable_nat_add_iff N).2 hbs) (((summable_nat_add_iff N).2 hsum).mul_left 2)
  have h3 : δ * S ≤ ε / 2 := by
    rw [hδ, div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

/-! ## Three lines -/

/-- **Recurrence moves inward.** Let `G` be holomorphic on `Re s > l'` and bounded by `B` on the
closed strip `l ≤ Re s ≤ u`, `l' < l < σ₁ < u`. If `G` recurs uniformly on the line `Re s = u`,
then at times beyond any threshold `G(σ₁ + it)` is within `ε` of `G(σ₁)`. -/
theorem exists_large_shift_near_of_bounded {G : ℂ → ℂ} {l' l σ₁ u B : ℝ} (hl' : l' < l)
    (hl : l < σ₁) (hu : σ₁ < u) (hG : DifferentiableOn ℂ G {s : ℂ | l' < s.re})
    (hB : ∀ s : ℂ, l ≤ s.re → s.re ≤ u → ‖G s‖ ≤ B)
    (hrec : ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, ∃ t : ℝ, R ≤ t ∧ ∀ s : ℂ, s.re = u →
      ‖G (s + (t : ℂ) * I) - G s‖ ≤ ε)
    {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ t : ℝ, R ≤ t ∧ ‖G ((σ₁ : ℂ) + (t : ℂ) * I) - G σ₁‖ ≤ ε := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB (l : ℂ) (by simp) (by simp; linarith))
  set θ : ℝ := (σ₁ - l) / (u - l) with hθ
  have hθ0 : 0 < θ := div_pos (by linarith) (by linarith)
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by linarith)]; linarith
  set M : ℝ := 2 * B + 1 with hM
  have hM1 : 1 ≤ M := by linarith
  set η : ℝ := (ε / M) ^ (1 / θ) with hη
  have hη0 : 0 < η := Real.rpow_pos_of_pos (div_pos hε (by linarith)) _
  obtain ⟨t, htR, ht⟩ := hrec η hη0 R
  refine ⟨t, htR, ?_⟩
  set D : ℂ → ℂ := fun s => G (s + (t : ℂ) * I) - G s with hD
  have hDdiff : DifferentiableOn ℂ D {s : ℂ | l' < s.re} := by
    refine DifferentiableOn.sub ?_ hG
    refine hG.comp (differentiableOn_id.add_const _) fun s hs => ?_
    simpa using hs
  have hclos : closure (Complex.HadamardThreeLines.verticalStrip l u) ⊆ {s : ℂ | l' < s.re} := by
    refine (closure_minimal (t := re ⁻¹' Icc l u)
      (fun s (hs : s ∈ Complex.HadamardThreeLines.verticalStrip l u) =>
        show s ∈ re ⁻¹' Icc l u from ⟨hs.1.le, hs.2.le⟩)
      (isClosed_Icc.preimage continuous_re)).trans fun s hs => ?_
    exact lt_of_lt_of_le hl' hs.1
  have hDcl : DiffContOnCl ℂ D (Complex.HadamardThreeLines.verticalStrip l u) :=
    (hDdiff.mono hclos).diffContOnCl
  have hDB : ∀ s : ℂ, l ≤ s.re → s.re ≤ u → ‖D s‖ ≤ 2 * B := by
    intro s h1 h2
    have e1 := hB (s + (t : ℂ) * I) (by simpa using h1) (by simpa using h2)
    have e2 := hB s h1 h2
    calc ‖D s‖ ≤ ‖G (s + (t : ℂ) * I)‖ + ‖G s‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith
  have hbdd : BddAbove (norm ∘ D '' Complex.HadamardThreeLines.verticalClosedStrip l u) :=
    ⟨2 * B, by
      rintro _ ⟨s, hs, rfl⟩
      exact hDB s hs.1 hs.2⟩
  have hz : ((σ₁ : ℂ)) ∈ Complex.HadamardThreeLines.verticalClosedStrip l u :=
    ⟨by simp; linarith, by simp; linarith⟩
  have h3 := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (a := 2 * B) (b := η) (by linarith) hz hDcl hbdd
    (fun s hs => hDB s (by rw [show s.re = l from hs]) (by rw [show s.re = l from hs]; linarith))
    (fun s hs => ht s hs)
  simp only [ofReal_re] at h3
  rw [← hθ] at h3
  refine h3.trans ?_
  have hA : (2 * B) ^ (1 - θ) ≤ M := by
    calc (2 * B) ^ (1 - θ) ≤ M ^ (1 - θ) :=
          Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
      _ ≤ M ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hM1 (by linarith)
      _ = M := Real.rpow_one M
  have hηθ : η ^ θ = ε / M := by
    rw [hη, ← Real.rpow_mul (div_pos hε (by linarith)).le, one_div, inv_mul_cancel₀ hθ0.ne',
      Real.rpow_one]
  rw [hηθ]
  have hpos : 0 ≤ ε / M := (div_pos hε (by linarith)).le
  calc (2 * B) ^ (1 - θ) * (ε / M) ≤ M * (ε / M) := mul_le_mul_of_nonneg_right hA hpos
    _ = ε := by field_simp

/-! ## The pole obstruction on the boundedness half-plane -/

/-- `Re 1/(s − 1) ≤ 1/(Re s − 1)` on `Re s > 1`. -/
theorem re_inv_sub_one_le {s : ℂ} (hs : 1 < s.re) : (1 / (s - 1)).re ≤ 1 / (s.re - 1) := by
  have hpos : 0 < s.re - 1 := by linarith
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [sub_re, one_re, sub_im, one_im, sub_zero]
  have hden : (s.re - 1) * (s.re - 1) ≤ (s.re - 1) * (s.re - 1) + s.im * s.im := by
    nlinarith [mul_self_nonneg s.im]
  rw [div_le_div_iff₀ (by nlinarith [mul_pos hpos hpos, mul_self_nonneg s.im]) hpos]
  nlinarith

/-- `Re 1/(σ + it − 1) → 0` as `t → ∞`, quantitatively: it is at most `(σ − 1)/t²`. -/
theorem re_inv_le_div_sq {σ t : ℝ} (hσ : 1 < σ) (ht : t ≠ 0) :
    (1 / ((σ : ℂ) + (t : ℂ) * I - 1)).re ≤ (σ - 1) / t ^ 2 := by
  have hpos : 0 < σ - 1 := by linarith
  have ht2 : 0 < t ^ 2 := by positivity
  rw [one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, add_zero, one_re, sub_im, add_im, mul_im, zero_add, one_im, sub_zero]
  rw [div_le_div_iff₀ (by nlinarith [mul_pos hpos hpos, mul_self_nonneg t]) ht2]
  nlinarith [mul_self_nonneg (σ - 1)]

/-- **No pole for a bounded datum, on the boundedness half-plane.** Let `a : ℕ → ℝ` have
`Σ |a n| n^{−v} < ∞` for some `v`, and let `L` be holomorphic on `Re s > 1` with `L = Σ a_n n^{−s}`
on `Re s > v`. If `Re L(s) ≤ C + Re 1/(s − 1)` on `Re s > 1`, then `Re L(σ) ≤ C` for every
`σ > 1`. -/
theorem re_le_of_bounded_datum_holomorphic (a : ℕ → ℝ) {v C : ℝ}
    (habs : Summable fun n : ℕ => |a n| * (n : ℝ) ^ (-v)) {L : ℂ → ℂ}
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 < s.re})
    (hLeq : ∀ s : ℂ, v < s.re → L s = LSeries (fun n => (a n : ℂ)) s)
    (hbound : ∀ s : ℂ, 1 < s.re → (L s).re ≤ C + (1 / (s - 1)).re) {σ₁ : ℝ} (hσ₁ : 1 < σ₁) :
    (L σ₁).re ≤ C := by
  set u : ℝ := max σ₁ v + 2 with hu
  have hu1 : σ₁ < u := by rw [hu]; linarith [le_max_left σ₁ v]
  have huv : v < u := by rw [hu]; linarith [le_max_right σ₁ v]
  have hu2 : 2 < u := by rw [hu]; linarith [le_max_left σ₁ v]
  set l : ℝ := (1 + σ₁) / 2 with hl
  have hl1 : 1 < l := by rw [hl]; linarith
  have hlσ : l < σ₁ := by rw [hl]; linarith
  set l' : ℝ := (1 + l) / 2 with hl'
  have hl'1 : 1 < l' := by rw [hl']; linarith
  have hl'l : l' < l := by rw [hl']; linarith
  set G : ℂ → ℂ := fun s => cexp (L s) with hGdef
  have hG : DifferentiableOn ℂ G {s : ℂ | l' < s.re} :=
    (hL.mono fun s hs => lt_trans hl'1 hs).cexp
  have hnormG : ∀ s : ℂ, ‖G s‖ = Real.exp (L s).re := fun s => Complex.norm_exp _
  -- boundedness on the strip
  set B : ℝ := Real.exp (C + 1 / (l - 1)) with hBdef
  have hB : ∀ s : ℂ, l ≤ s.re → s.re ≤ u → ‖G s‖ ≤ B := by
    intro s h1 _
    have hs1 : 1 < s.re := lt_of_lt_of_le hl1 h1
    rw [hnormG]
    refine Real.exp_le_exp.mpr ((hbound s hs1).trans ?_)
    have := re_inv_sub_one_le hs1
    have h2 : 1 / (s.re - 1) ≤ 1 / (l - 1) :=
      one_div_le_one_div_of_le (by linarith) (by linarith)
    linarith
  -- recurrence on the far line
  have hsum : Summable fun n : ℕ => ‖((a n : ℝ) : ℂ)‖ * (n : ℝ) ^ (-(u - 1)) := by
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) habs
    rw [Complex.norm_real, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.cast_zero]
      rw [Real.zero_rpow (by linarith)]
      simp only [mul_zero]
      exact mul_nonneg (abs_nonneg _) (Real.rpow_nonneg le_rfl _)
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hn1 (by rw [hu]; linarith [le_max_right σ₁ v]))
        (abs_nonneg _)
  have hrec : ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, ∃ t : ℝ, R ≤ t ∧ ∀ s : ℂ, s.re = u →
      ‖G (s + (t : ℂ) * I) - G s‖ ≤ ε := by
    intro ε hε R
    set K : ℝ := Real.exp (C + 1) with hK
    obtain ⟨t, htR, ht⟩ := exists_large_lseries_shift_near (fun n => (a n : ℂ)) hsum
      (ε := min 1 (ε / (2 * K))) (lt_min one_pos (by positivity)) R
    refine ⟨t, htR, fun s hs => ?_⟩
    have hsu : u - 1 ≤ s.re := by rw [hs]; linarith
    have hs1 : 1 < s.re := by rw [hs]; linarith
    have hst : v < (s + (t : ℂ) * I).re := by simp [hs]; linarith
    have hsv : v < s.re := by rw [hs]; linarith
    have hd := ht s hsu
    rw [← hLeq _ hst, ← hLeq _ hsv] at hd
    have hd1 : ‖L (s + (t : ℂ) * I) - L s‖ ≤ 1 := hd.trans (min_le_left _ _)
    have hd2 : ‖L (s + (t : ℂ) * I) - L s‖ ≤ ε / (2 * K) := hd.trans (min_le_right _ _)
    have hGs : ‖G s‖ ≤ K := by
      rw [hnormG]
      refine Real.exp_le_exp.mpr ((hbound s hs1).trans ?_)
      have := re_inv_sub_one_le hs1
      have h2 : 1 / (s.re - 1) ≤ 1 := by
        rw [div_le_one (by linarith)]; linarith
      linarith
    have hfac : G (s + (t : ℂ) * I) - G s = G s * (cexp (L (s + (t : ℂ) * I) - L s) - 1) := by
      simp only [hGdef]
      rw [mul_sub_one, ← Complex.exp_add]
      ring_nf
    rw [hfac, norm_mul]
    have hexp := Complex.norm_exp_sub_one_le hd1
    have hK0 : 0 < K := Real.exp_pos _
    calc ‖G s‖ * ‖cexp (L (s + (t : ℂ) * I) - L s) - 1‖
        ≤ K * (2 * (ε / (2 * K))) :=
          mul_le_mul hGs (hexp.trans (by linarith)) (norm_nonneg _) hK0.le
      _ = ε := by field_simp
  -- recurrence at `σ₁` and the bound at large height
  by_contra hcon
  push Not at hcon
  set g : ℝ := (L σ₁).re - C with hg
  have hg0 : 0 < g := by linarith
  -- `‖G σ₁‖ = e^{C + g}`; choose `ε` so that `e^{C + g} − ε > e^{C + g/2}`
  set ε : ℝ := (Real.exp (C + g) - Real.exp (C + g / 2)) / 2 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    have : Real.exp (C + g / 2) < Real.exp (C + g) := Real.exp_lt_exp.mpr (by linarith)
    linarith
  -- a height beyond which the pole term is below `g/2`
  set T : ℝ := Real.sqrt (2 * (σ₁ - 1) / g) + 1 with hT
  obtain ⟨t, htT, ht⟩ := exists_large_shift_near_of_bounded hl'l hlσ hu1 hG hB hrec hε T
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) htT
  have hpole : (1 / ((σ₁ : ℂ) + (t : ℂ) * I - 1)).re ≤ g / 2 := by
    refine (re_inv_le_div_sq hσ₁ ht0.ne').trans ?_
    have hsq : 2 * (σ₁ - 1) / g < t ^ 2 := by
      have h1 : Real.sqrt (2 * (σ₁ - 1) / g) < t := by linarith
      have h0 : 0 ≤ 2 * (σ₁ - 1) / g := by positivity
      calc 2 * (σ₁ - 1) / g = Real.sqrt (2 * (σ₁ - 1) / g) ^ 2 := (Real.sq_sqrt h0).symm
        _ < t ^ 2 := by
            exact pow_lt_pow_left₀ h1 (Real.sqrt_nonneg _) (by norm_num)
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have := (div_lt_iff₀ hg0).mp hsq
    nlinarith
  have hupper : ‖G ((σ₁ : ℂ) + (t : ℂ) * I)‖ ≤ Real.exp (C + g / 2) := by
    rw [hnormG]
    refine Real.exp_le_exp.mpr ((hbound _ (by simp; linarith)).trans ?_)
    linarith
  have hGσ : ‖G (σ₁ : ℂ)‖ = Real.exp (C + g) := by
    rw [hnormG, hg]; ring_nf
  have := norm_sub_norm_le (G (σ₁ : ℂ)) (G ((σ₁ : ℂ) + (t : ℂ) * I))
  rw [norm_sub_rev] at this
  linarith

/-- **The pole obstruction, every coefficient class.** Under the hypotheses of
`re_le_of_bounded_datum_holomorphic`, `Re L(σ)` does not tend to `+∞` as `σ → 1⁺`: a Dirichlet
series whose real part is bounded by a bounded datum plus the pole term cannot carry the pole. -/
theorem not_tendsto_re_atTop_of_bounded_datum_holomorphic (a : ℕ → ℝ) {v C : ℝ}
    (habs : Summable fun n : ℕ => |a n| * (n : ℝ) ^ (-v)) {L : ℂ → ℂ}
    (hL : DifferentiableOn ℂ L {s : ℂ | 1 < s.re})
    (hLeq : ∀ s : ℂ, v < s.re → L s = LSeries (fun n => (a n : ℂ)) s)
    (hbound : ∀ s : ℂ, 1 < s.re → (L s).re ≤ C + (1 / (s - 1)).re) :
    ¬ Tendsto (fun σ : ℝ => (L (σ : ℂ)).re) (𝓝[>] 1) atTop := by
  intro htend
  obtain ⟨σ, hσC, hσ1⟩ :=
    ((htend.eventually_ge_atTop (C + 1)).and (self_mem_nhdsWithin : ∀ᶠ σ in 𝓝[>] (1 : ℝ),
      σ ∈ Ioi 1)).exists
  have := re_le_of_bounded_datum_holomorphic a habs hL hLeq hbound hσ1
  linarith

end RHTower.BoundedDatumPoleObstruction
