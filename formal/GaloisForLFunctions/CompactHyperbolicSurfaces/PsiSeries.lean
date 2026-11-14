import GaloisForLFunctions.HTGeometry.BarnesOrderOnePartialFractions
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries

/-!
# The digamma difference and its primitive

For `a > 0` and `Re s > 0`:

* `ψ_a(s) = Σ_k (1/(a+k) − 1/(s+k))` converges and is holomorphic (`differentiableOn_psiDiff`);
* the series `G_a(s) = Σ_k g_k(s)`,
  `g_k(s) = (s² − s)/(a+k) − 2s + (2k+1) Log(s+k) − g̃_k(a)` normalized by `g_k(a) = 0`,
  is a primitive of `(2s − 1) ψ_a(s)` (`hasDerivAt_gSeries`), since `g_k' = (2s − 1)(1/(a+k) − 1/(s+k))`;
* on `0 < Re w < 1`, `ψ_a(w) − ψ_a(1 − w) = −π cot(πw)` (`psiDiff_sub_psiDiff_one_sub`), from the
  partial-fraction expansion of the cotangent.
-/

open Complex Filter Set Metric
open scoped Topology Real

namespace GaloisForLFunctions.CompactHyperbolicSurfaces

noncomputable section

/-- `1/(a + k) − 1/(s + k)`. -/
def psiTerm (a : ℝ) (k : ℕ) (s : ℂ) : ℂ := 1 / ((a : ℂ) + k) - 1 / (s + k)

/-- `ψ_a(s) = Σ_k (1/(a + k) − 1/(s + k))`. -/
def psiDiff (a : ℝ) (s : ℂ) : ℂ := ∑' k : ℕ, psiTerm a k s

/-- The bounded region `{δ < Re z, |z| < M}`. -/
def psiRegion (δ M : ℝ) : Set ℂ := {z : ℂ | δ < z.re ∧ ‖z‖ < M}

theorem isOpen_psiRegion (δ M : ℝ) : IsOpen (psiRegion δ M) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_norm continuous_const)

theorem convex_psiRegion (δ M : ℝ) : Convex ℝ (psiRegion δ M) := by
  have e : psiRegion δ M = {z : ℂ | δ < z.re} ∩ ball (0 : ℂ) M := by
    ext z; simp [psiRegion]
  rw [e]
  exact Convex.inter (convex_halfSpace_re_gt δ) (convex_ball 0 M)

theorem norm_add_nat_ge {z : ℂ} (k : ℕ) : z.re + k ≤ ‖z + k‖ := by
  have := Complex.re_le_norm (z + k)
  simpa using this

/-- `‖1/(a+k) − 1/(t+k)‖ ≤ (M + a)/((a + k)(δ + k))` on `psiRegion δ M`. -/
theorem norm_psiTerm_le {a δ M : ℝ} (ha : 0 < a) (hδ : 0 < δ) {t : ℂ} (ht : t ∈ psiRegion δ M)
    (k : ℕ) : ‖psiTerm a k t‖ ≤ (M + a) / ((a + k) * (δ + k)) := by
  obtain ⟨htre, htM⟩ := ht
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : 0 < a + k := by linarith
  have h2 : δ + k ≤ ‖t + k‖ := le_trans (by linarith) (norm_add_nat_ge k)
  have h2' : 0 < ‖t + k‖ := lt_of_lt_of_le (by linarith) h2
  have ht0 : t + k ≠ 0 := norm_pos_iff.mp h2'
  have ha0 : (a : ℂ) + k ≠ 0 := by exact_mod_cast h1.ne'
  have e : psiTerm a k t = (t - a) / (((a : ℂ) + k) * (t + k)) := by
    rw [psiTerm]; field_simp; ring
  rw [e, norm_div, norm_mul, show ‖(a : ℂ) + k‖ = a + k by
    rw [show ((a : ℂ) + k) = ((a + k : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg h1.le]]
  have hnum : ‖t - a‖ ≤ M + a := by
    have := norm_sub_le t (a : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg ha.le] at this
    linarith
  rw [div_le_div_iff₀ (mul_pos h1 h2') (mul_pos h1 (by linarith))]
  have hMa : 0 ≤ M + a := le_trans (norm_nonneg _) hnum
  calc ‖t - a‖ * ((a + k) * (δ + k)) ≤ (M + a) * ((a + k) * (δ + k)) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ ≤ (M + a) * ((a + k) * ‖t + k‖) := by gcongr

theorem summable_psiBound {a δ C : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    Summable fun k : ℕ => C / ((a + k) * (δ + k)) := by
  set m := min (min a δ) 1
  have hm : 0 < m := lt_min (lt_min ha hδ) one_pos
  have hm1 : m ≤ 1 := min_le_right _ _
  have hsq := (Real.summable_one_div_nat_add_rpow 1 2).mpr one_lt_two
  have hbound : ∀ k : ℕ, ‖C / ((a + k) * (δ + k))‖ ≤ |C| / m ^ 2 * (1 / |(k : ℝ) + 1| ^ (2 : ℝ)) := by
    intro k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have h1 : m * (k + 1) ≤ a + k := by
      have : m ≤ a := le_trans (min_le_left _ _) (min_le_left _ _)
      nlinarith
    have h2 : m * (k + 1) ≤ δ + k := by
      have : m ≤ δ := le_trans (min_le_left _ _) (min_le_right _ _)
      nlinarith
    have hpos : 0 < m * (k + 1) := by positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < (a + k) * (δ + k)),
      abs_of_pos (by positivity : (0 : ℝ) < k + 1), Real.rpow_two, div_mul_div_comm, mul_one]
    apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
    calc m ^ 2 * (k + 1) ^ 2 = (m * (k + 1)) * (m * (k + 1)) := by ring
      _ ≤ (a + k) * (δ + k) := mul_le_mul h1 h2 hpos.le (by linarith)
  exact Summable.of_norm_bounded (hsq.mul_left _) hbound

theorem summable_psiTerm {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    Summable fun k => psiTerm a k s := by
  have hmem : s ∈ psiRegion (s.re / 2) (‖s‖ + 1) := ⟨by linarith, by linarith⟩
  exact Summable.of_norm_bounded (summable_psiBound (C := ‖s‖ + 1 + a) ha (by linarith))
    fun k => norm_psiTerm_le ha (by linarith) hmem k

/-- **`ψ_a` is holomorphic on `Re s > 0`.** -/
theorem differentiableOn_psiDiff {a : ℝ} (ha : 0 < a) : DifferentiableOn ℂ (psiDiff a) {s | 0 < s.re} := by
  intro s hs
  have hs' : 0 < s.re := hs
  have hmem : s ∈ psiRegion (s.re / 2) (‖s‖ + 1) := ⟨by linarith, by linarith⟩
  have hd : DifferentiableOn ℂ (psiDiff a) (psiRegion (s.re / 2) (‖s‖ + 1)) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      (summable_psiBound (C := ‖s‖ + 1 + a) ha (by linarith)) (fun k => ?_)
      (isOpen_psiRegion _ _) (fun k t ht => norm_psiTerm_le ha (by linarith) ht k)
    intro t ht
    have ht0 : t + k ≠ 0 := by
      have := norm_add_nat_ge (z := t) k
      intro h; rw [h, norm_zero] at this
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith [ht.1]
    show DifferentiableWithinAt ℂ (fun s : ℂ => 1 / ((a : ℂ) + k) - 1 / (s + k)) _ t
    exact DifferentiableAt.differentiableWithinAt (by fun_prop (disch := exact ht0))
  exact ((hd s hmem).differentiableAt ((isOpen_psiRegion _ _).mem_nhds hmem)).differentiableWithinAt

theorem psiDiff_ofReal (a b : ℝ) :
    psiDiff a b = ((∑' k : ℕ, (1 / (a + k) - 1 / (b + k)) : ℝ) : ℂ) := by
  rw [psiDiff, Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  rw [psiTerm]
  push_cast
  ring

/-! ### The primitive -/

/-- `g_k(s) = (s² − s)/(a+k) − 2s + (2k+1) Log(s+k)`, normalized by `g_k(a) = 0`. -/
def gTerm (a : ℝ) (k : ℕ) (s : ℂ) : ℂ :=
  (s * s - s) / ((a : ℂ) + k) - 2 * s + (2 * k + 1) * Complex.log (s + k) -
    (((a : ℂ) * a - a) / ((a : ℂ) + k) - 2 * a + (2 * k + 1) * Complex.log ((a : ℂ) + k))

/-- `G_a(s) = Σ_k g_k(s)`. -/
def gSeries (a : ℝ) (s : ℂ) : ℂ := ∑' k : ℕ, gTerm a k s

theorem hasDerivAt_gTerm {a : ℝ} (ha : 0 < a) (k : ℕ) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (gTerm a k) ((2 * s - 1) * psiTerm a k s) s := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hslit : s + k ∈ slitPlane := Or.inl (by simp; linarith)
  have ht0 : s + k ≠ 0 := slitPlane_ne_zero hslit
  have ha0 : (a : ℂ) + k ≠ 0 := by exact_mod_cast (show (0:ℝ) < a + k by linarith).ne'
  have h1 : HasDerivAt (fun s : ℂ => (s * s - s) / ((a : ℂ) + k)) ((2 * s - 1) / ((a : ℂ) + k)) s := by
    exact ((((hasDerivAt_id s).mul (hasDerivAt_id s)).sub (hasDerivAt_id s)).div_const
      ((a : ℂ) + k)).congr_deriv (by simp only [id]; ring)
  have h2 : HasDerivAt (fun s : ℂ => Complex.log (s + k)) (1 / (s + k)) s :=
    ((hasDerivAt_id s).add_const (k : ℂ)).clog hslit
  have h3 := ((h1.sub ((hasDerivAt_id s).const_mul 2)).add (h2.const_mul (2 * (k : ℂ) + 1))).sub_const
    (((a : ℂ) * a - a) / ((a : ℂ) + k) - 2 * a + (2 * k + 1) * Complex.log ((a : ℂ) + k))
  refine h3.congr_deriv ?_
  rw [psiTerm]
  field_simp
  ring

theorem norm_hasDeriv_gTerm_le {a δ M : ℝ} (ha : 0 < a) (hδ : 0 < δ) {t : ℂ}
    (ht : t ∈ psiRegion δ M) (k : ℕ) :
    ‖(2 * t - 1) * psiTerm a k t‖ ≤ (2 * M + 1) * (M + a) / ((a + k) * (δ + k)) := by
  rw [norm_mul, mul_div_assoc]
  have h1 : ‖2 * t - 1‖ ≤ 2 * M + 1 := by
    have := norm_sub_le (2 * t) 1
    rw [norm_mul, norm_one, show ‖(2 : ℂ)‖ = 2 by norm_num] at this
    linarith [ht.2]
  exact mul_le_mul h1 (norm_psiTerm_le ha hδ ht k) (norm_nonneg _) (by linarith [norm_nonneg t, ht.2])

/-- **`G_a` is a primitive of `(2s − 1) ψ_a(s)`** on `Re s > 0`. -/
theorem hasDerivAt_gSeries {a : ℝ} (ha : 0 < a) {s : ℂ} (hs : 0 < s.re) :
    HasDerivAt (gSeries a) ((2 * s - 1) * psiDiff a s) s := by
  set δ := min s.re a / 2
  set M := max ‖s‖ a + 1
  have hδ : 0 < δ := by simp only [δ]; positivity
  have hs_mem : s ∈ psiRegion δ M := by
    refine ⟨?_, ?_⟩
    · have := min_le_left s.re a; simp only [δ]; linarith
    · have := le_max_left ‖s‖ a; simp only [M]; linarith
  have ha_mem : (a : ℂ) ∈ psiRegion δ M := by
    refine ⟨?_, ?_⟩
    · have := min_le_right s.re a; simp only [δ, Complex.ofReal_re]; linarith
    · rw [Complex.norm_real, Real.norm_of_nonneg ha.le]
      have := le_max_right ‖s‖ a; simp only [M]; linarith
  have hg0 : Summable fun k => gTerm a k a := by
    have : ∀ k : ℕ, gTerm a k a = 0 := fun k => by rw [gTerm]; ring
    simp_rw [this]; exact summable_zero
  have h := hasDerivAt_tsum_of_isPreconnected (t := psiRegion δ M)
    (summable_psiBound (C := (2 * M + 1) * (M + a)) ha hδ) (isOpen_psiRegion δ M)
    (convex_psiRegion δ M).isPreconnected
    (fun k y hy => hasDerivAt_gTerm ha k (lt_trans hδ hy.1))
    (fun k y hy => norm_hasDeriv_gTerm_le ha hδ hy k) ha_mem hg0 hs_mem
  rw [psiDiff, ← tsum_mul_left]
  exact h

/-! ### The cotangent identity -/

theorem mem_integerComplement_of_re {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) : w ∈ Complex.integerComplement := by
  rintro ⟨n, hn⟩
  have hre : (n : ℝ) = w.re := by rw [← hn]; simp
  have h0' : (0 : ℝ) < n := by rw [hre]; exact h0
  have h1' : (n : ℝ) < 1 := by rw [hre]; exact h1
  have : (0 : ℤ) < n := by exact_mod_cast h0'
  have : n < (1 : ℤ) := by exact_mod_cast h1'
  omega

/-- `Σ_k (1/(1 − w + k) − 1/(w + k)) = −π cot(πw)` for `0 < Re w < 1`. -/
theorem hasSum_reflect_sub {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    HasSum (fun k : ℕ => 1 / (1 - w + k) - 1 / (w + k)) (-(π * Complex.cot (π * w))) := by
  have hw := mem_integerComplement_of_re h0 h1
  -- cotangent part
  have hA : HasSum (fun k : ℕ => -cotTerm w k) (-(π * Complex.cot (π * w) - 1 / w)) := by
    have h := (summable_cotTerm hw).hasSum
    rw [← cot_series_rep' hw] at h
    exact h.neg
  -- telescoping part, `1/(w + (k+1)) − 1/(w + k) = ψ-term(w) − ψ-term(w + 1)`
  have hB : HasSum (fun k : ℕ => 1 / (w + (k + 1)) - 1 / (w + k)) (-(1 / w)) := by
    have hs1 := summable_psiTerm (a := 1) one_pos h0
    have hs2 := summable_psiTerm (a := 1) one_pos (s := w + 1) (by simp; linarith)
    have hsum : Summable fun k : ℕ => 1 / (w + k) - 1 / (w + (k + 1)) := by
      refine (hs2.sub hs1).congr fun k => ?_
      simp only [psiTerm]
      ring_nf
    have htend : Tendsto (fun k : ℕ => 1 / (w + k)) atTop (𝓝 0) := by
      have := GaloisForLFunctions.HTGeometry.tendsto_inv_of_tendsto_norm_atTop
        (f := fun k : ℕ => w + k) (by
          refine tendsto_atTop_mono (fun k => ?_) (tendsto_natCast_atTop_atTop.atTop_add
            (tendsto_const_nhds (x := -‖w‖)))
          have := norm_sub_norm_le ((k : ℂ)) (-w)
          rw [sub_neg_eq_add, norm_neg, Complex.norm_natCast] at this
          rw [add_comm w]; linarith)
      simpa only [one_div] using this
    have htel := GaloisForLFunctions.HTGeometry.tsum_telescope (f := fun k : ℕ => 1 / (w + k))
      (by simpa only [Nat.cast_add, Nat.cast_one, add_assoc] using hsum) htend
    have h := hsum.hasSum
    simp only [Nat.cast_add, Nat.cast_one] at htel
    rw [htel] at h
    simpa only [Nat.cast_zero, add_zero, neg_sub] using h.neg
  have hsum := hA.add hB
  have e : -(π * Complex.cot (π * w) - 1 / w) + -(1 / w) = -(π * Complex.cot (π * w)) := by ring
  rw [e] at hsum
  refine hsum.congr_fun fun k => ?_
  simp only [cotTerm]
  rw [show (1 : ℂ) - w + k = -(w - (k + 1)) by ring, one_div_neg_eq_neg_one_div]
  ring

/-- **Reflection of `ψ_a`.**  `ψ_a(w) − ψ_a(1 − w) = −π cot(πw)` for `0 < Re w < 1`. -/
theorem psiDiff_sub_psiDiff_one_sub {a : ℝ} (ha : 0 < a) {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    psiDiff a w - psiDiff a (1 - w) = -(π * Complex.cot (π * w)) := by
  have hs1 := summable_psiTerm ha h0
  have hs2 := summable_psiTerm ha (s := 1 - w) (by simp; linarith)
  rw [psiDiff, psiDiff, ← hs1.tsum_sub hs2, ← (hasSum_reflect_sub h0 h1).tsum_eq]
  refine tsum_congr fun k => ?_
  simp only [psiTerm]
  ring

end

end GaloisForLFunctions.CompactHyperbolicSurfaces
