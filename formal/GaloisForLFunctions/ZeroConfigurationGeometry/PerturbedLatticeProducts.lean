import GaloisForLFunctions.ZeroConfigurationGeometry.HeatStepsNeverShrinkTheMesh
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Products over a perturbed lattice

Let `μ_k = (k + θ)h` be a shifted lattice and `λ_k` complex points with `|λ_k − μ_k| ≤ L` and
`|Im λ_k| ≤ 1/2`. The factors

`r_k(z) = ((z − λ_k)/(z − μ_k)) · ((i − μ_k)/(i − λ_k))`

satisfy `r_k(z) − 1 = (z − i)(λ_k − μ_k)/((z − μ_k)(i − λ_k)) = O(1/k²)` (`pertFactor_sub_one`), so
`Π_k r_k` converges absolutely off the lattice (`summable_norm_pertFactor_sub_one`). On the real
line the partial products, multiplied by `sin((π/h)(x − θh))`, are bounded by `K(1 + |x|)^p`
uniformly in the set of factors (`norm_sin_mul_prod_pertFactor_le`). Since `|Im λ_k| ≤ 1/2`,
`|i − λ_k| ≥ |i − Re λ_k|/2`, so the sums over the factors are those of the real perturbation
`Re λ_k`, up to a factor `2`.

Proof of the bound. The sine absorbs the factor of the lattice point nearest to `x`. For the
other factors `|r_k − 1| ≤ L|x − i|/(|x − μ_k| |i − λ_k|)`; split at `|μ_k| = R ≍ |x|`. Beyond `R`
the terms are `O(R/μ_k²)` with total `O(1)` (`sum_inv_sq_far_le`); inside, `|x − i| ≤ |x − μ_k| +
|i − λ_k| + L` leaves two harmonic sums of `O(log(1 + |x|))` (`sum_inv_max_dist_le`). So the log
of the product is `O(1 + log(1 + |x|))`.
-/

open Complex Set Filter Topology Finset
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

/-! ### Harmonic sums over a lattice -/

theorem log_natCast_mono {a b : ℕ} (hab : a ≤ b) : Real.log a ≤ Real.log b := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · rw [ha, Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg b
  · exact Real.log_le_log (by exact_mod_cast ha) (by exact_mod_cast hab)

/-- `Σ_{m<n} 1/max(δ, mh) ≤ 1/δ + (1 + log n)/h` for `0 < δ ≤ h`. -/
theorem sum_range_inv_max_le {h δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ ≤ h) (n : ℕ) :
    ∑ m ∈ range n, 1 / max δ ((m : ℝ) * h) ≤ 1 / δ + (1 + Real.log n) / h := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp; positivity
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ']
  have h0 : 1 / max δ (((0 : ℕ) : ℝ) * h) = 1 / δ := by simp [le_of_lt hδ]
  have hterm : ∀ m ∈ range n', 1 / max δ ((((m + 1 : ℕ) : ℝ)) * h) = (1 / h) * (1 / ((m : ℝ) + 1)) := by
    intro m _
    have hm : δ ≤ (((m + 1 : ℕ) : ℝ)) * h := by
      have : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
      nlinarith
    rw [max_eq_right hm]
    push_cast
    field_simp
  rw [h0, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hharm : ∑ m ∈ range n', 1 / ((m : ℝ) + 1) = (harmonic n' : ℝ) := by
    simp [harmonic, one_div]
  rw [hharm]
  have hb := harmonic_le_one_add_log n'
  have hlog : Real.log n' ≤ Real.log (n' + 1 : ℕ) := log_natCast_mono (Nat.le_succ n')
  have : (1 / h) * (harmonic n' : ℝ) ≤ (1 + Real.log (n' + 1 : ℕ)) / h := by
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right (by linarith) hh.le
  linarith

/-- The point `μ_k = (k + θ)h` of the shifted lattice. -/
def latPt (h θ : ℝ) (k : ℤ) : ℝ := ((k : ℝ) + θ) * h

theorem latPt_sep {h θ : ℝ} (hh : 0 < h) {j k : ℤ} (hjk : j ≠ k) :
    h ≤ |latPt h θ j - latPt h θ k| := by
  have hjk' : (1 : ℝ) ≤ |(j : ℝ) - k| := by
    have : (1 : ℤ) ≤ |j - k| := Int.one_le_abs (sub_ne_zero.mpr hjk)
    exact_mod_cast this
  rw [latPt, latPt, show ((j : ℝ) + θ) * h - ((k : ℝ) + θ) * h = ((j : ℝ) - k) * h by ring,
    abs_mul, abs_of_pos hh]
  nlinarith

/-- **Harmonic sums around any centre.** For `0 < δ ≤ h`,
`Σ_{k ∈ S} 1/max(δ, |c − μ_k|) ≤ 2(1/δ + (1 + log |S|)/h)`. -/
theorem sum_inv_max_dist_le {h θ δ : ℝ} (hh : 0 < h) (hδ : 0 < δ) (hδh : δ ≤ h) (c : ℝ)
    (S : Finset ℤ) :
    ∑ k ∈ S, 1 / max δ |c - latPt h θ k| ≤ 2 * (1 / δ + (1 + Real.log S.card) / h) := by
  classical
  have hF0 : ∀ D, h ≤ D → 0 ≤ 1 / max δ (D - h) := fun D _ =>
    one_div_nonneg.mpr (le_max_of_le_left hδ.le)
  have hFm : ∀ D D', h ≤ D → D ≤ D' → 1 / max δ (D' - h) ≤ 1 / max δ (D - h) := fun D D' _ hDD' =>
    one_div_le_one_div_of_le (lt_max_of_lt_left hδ) (max_le_max le_rfl (by linarith))
  rw [← Finset.sum_filter_add_sum_filter_not S (fun k => latPt h θ k ≤ c)]
  set A := S.filter (fun k => latPt h θ k ≤ c)
  set B := S.filter (fun k => ¬ latPt h θ k ≤ c)
  have hcount : ∀ n : ℕ, n ≤ S.card → ∑ m ∈ range n, 1 / max δ (((m : ℝ) + 1) * h - h) ≤
      1 / δ + (1 + Real.log S.card) / h := by
    intro n hn
    have e : ∀ m : ℕ, ((m : ℝ) + 1) * h - h = (m : ℝ) * h := fun m => by ring
    simp only [e]
    refine (sum_range_inv_max_le hh hδ hδh n).trans ?_
    have := log_natCast_mono hn
    have : (1 + Real.log n) / h ≤ (1 + Real.log S.card) / h :=
      div_le_div_of_nonneg_right (by linarith) hh.le
    linarith
  have hA := sum_le_sum_range_of_sep (latPt h θ) hh.le A.card A (c + h)
    (fun D => 1 / max δ (D - h)) rfl hF0 hFm
    (fun x _ x' _ hxx' => latPt_sep hh hxx')
    (fun x hx => by have := (Finset.mem_filter.mp hx).2; linarith)
  have hB := sum_le_sum_range_of_sep (fun k => -latPt h θ k) hh.le B.card B (-c + h)
    (fun D => 1 / max δ (D - h)) rfl hF0 hFm
    (fun x _ x' _ hxx' => by
      rw [show -latPt h θ x - -latPt h θ x' = -(latPt h θ x - latPt h θ x') by ring, abs_neg]
      exact latPt_sep hh hxx')
    (fun x hx => by have := (Finset.mem_filter.mp hx).2; push Not at this; linarith)
  have eA : ∑ k ∈ A, 1 / max δ |c - latPt h θ k| = ∑ k ∈ A, 1 / max δ (c + h - latPt h θ k - h) :=
    Finset.sum_congr rfl fun k hk => by
      have := (Finset.mem_filter.mp hk).2
      rw [abs_of_nonneg (by linarith)]; ring_nf
  have eB : ∑ k ∈ B, 1 / max δ |c - latPt h θ k| =
      ∑ k ∈ B, 1 / max δ (-c + h - -latPt h θ k - h) :=
    Finset.sum_congr rfl fun k hk => by
      have := (Finset.mem_filter.mp hk).2
      push Not at this
      rw [abs_of_neg (by linarith)]; ring_nf
  have hAc : A.card ≤ S.card := Finset.card_filter_le _ _
  have hBc : B.card ≤ S.card := Finset.card_filter_le _ _
  rw [eA, eB]
  linarith [hA.trans (hcount _ hAc), hB.trans (hcount _ hBc)]

/-- `Σ_{m<n+1} 1/(mh + R)² ≤ 1/R² + (1/h)(1/R − 1/(nh + R))`. -/
theorem sum_range_inv_sq_le {h R : ℝ} (hh : 0 < h) (hR : 0 < R) (n : ℕ) :
    ∑ m ∈ range (n + 1), 1 / ((m : ℝ) * h + R) ^ 2 ≤
      1 / R ^ 2 + (1 / h) * (1 / R - 1 / ((n : ℝ) * h + R)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have h1 : 0 < (n : ℝ) * h + R := by positivity
    have h2 : 0 < ((n + 1 : ℕ) : ℝ) * h + R := by positivity
    have hstep : 1 / (((n + 1 : ℕ) : ℝ) * h + R) ^ 2 ≤
        (1 / h) * (1 / ((n : ℝ) * h + R) - 1 / (((n + 1 : ℕ) : ℝ) * h + R)) := by
      have e : (1 / h) * (1 / ((n : ℝ) * h + R) - 1 / (((n + 1 : ℕ) : ℝ) * h + R)) =
          1 / (((n : ℝ) * h + R) * (((n + 1 : ℕ) : ℝ) * h + R)) := by
        push_cast; field_simp; ring
      rw [e, sq]
      apply one_div_le_one_div_of_le (by positivity)
      push_cast
      nlinarith
    linarith

/-- **The far tail.** If all `|μ_k| ≥ R > 0` on `S`, then `Σ_S 1/μ_k² ≤ 2(1/R² + 1/(hR))`. -/
theorem sum_inv_sq_far_le {h θ R : ℝ} (hh : 0 < h) (hR : 0 < R) (S : Finset ℤ)
    (hS : ∀ k ∈ S, R ≤ |latPt h θ k|) :
    ∑ k ∈ S, 1 / latPt h θ k ^ 2 ≤ 2 * (1 / R ^ 2 + 1 / (h * R)) := by
  classical
  have hF0 : ∀ D, h ≤ D → 0 ≤ 1 / (D + R - h) ^ 2 := fun D _ => by positivity
  have hFm : ∀ D D', h ≤ D → D ≤ D' → 1 / (D' + R - h) ^ 2 ≤ 1 / (D + R - h) ^ 2 :=
    fun D D' hD hDD' => one_div_le_one_div_of_le (by nlinarith)
      (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  have hcount : ∀ n : ℕ, ∑ m ∈ range n, 1 / (((m : ℝ) + 1) * h + R - h) ^ 2 ≤
      1 / R ^ 2 + 1 / (h * R) := by
    intro n
    have e : ∀ m : ℕ, ((m : ℝ) + 1) * h + R - h = (m : ℝ) * h + R := fun m => by ring
    simp only [e]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp; positivity
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    refine (sum_range_inv_sq_le hh hR n').trans ?_
    have : 0 < 1 / ((n' : ℝ) * h + R) := by positivity
    have e2 : (1 / h) * (1 / R) = 1 / (h * R) := by field_simp
    nlinarith [mul_pos (one_div_pos.mpr hh) this]
  rw [← Finset.sum_filter_add_sum_filter_not S (fun k => 0 ≤ latPt h θ k)]
  set A := S.filter (fun k => 0 ≤ latPt h θ k)
  set B := S.filter (fun k => ¬ 0 ≤ latPt h θ k)
  have hA := sum_le_sum_range_of_sep (fun k => -latPt h θ k) hh.le A.card A (h - R)
    (fun D => 1 / (D + R - h) ^ 2) rfl hF0 hFm
    (fun x _ x' _ hxx' => by
      rw [show -latPt h θ x - -latPt h θ x' = -(latPt h θ x - latPt h θ x') by ring, abs_neg]
      exact latPt_sep hh hxx')
    (fun x hx => by
      obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
      have := hS x hxS
      rw [abs_of_nonneg hx0] at this
      linarith)
  have hB := sum_le_sum_range_of_sep (latPt h θ) hh.le B.card B (h - R)
    (fun D => 1 / (D + R - h) ^ 2) rfl hF0 hFm
    (fun x _ x' _ hxx' => latPt_sep hh hxx')
    (fun x hx => by
      obtain ⟨hxS, hx0⟩ := Finset.mem_filter.mp hx
      push Not at hx0
      have := hS x hxS
      rw [abs_of_neg hx0] at this
      linarith)
  have eA : ∑ k ∈ A, 1 / latPt h θ k ^ 2 = ∑ k ∈ A, 1 / (h - R - -latPt h θ k + R - h) ^ 2 :=
    Finset.sum_congr rfl fun k _ => by ring_nf
  have eB : ∑ k ∈ B, 1 / latPt h θ k ^ 2 = ∑ k ∈ B, 1 / (h - R - latPt h θ k + R - h) ^ 2 :=
    Finset.sum_congr rfl fun k _ => by ring_nf
  rw [eA, eB]
  linarith [hA.trans (hcount _), hB.trans (hcount _)]

/-! ### The factors -/

/-- The factor `r_k(z) = ((z − ν_k)/(z − μ_k)) ((i − μ_k)/(i − ν_k))` moving the lattice point
`μ_k` to `ν_k`, normalized at `i`. -/
def pertFactor (h θ : ℝ) (ν : ℤ → ℂ) (k : ℤ) (z : ℂ) : ℂ :=
  ((z - ν k) / (z - latPt h θ k)) * ((I - latPt h θ k) / (I - ν k))

theorem I_sub_ofReal_ne_zero (t : ℝ) : (I - (t : ℂ)) ≠ 0 := fun h => by
  have := congrArg Complex.im h
  simp at this

theorem one_le_norm_I_sub_ofReal (t : ℝ) : 1 ≤ ‖I - (t : ℂ)‖ := by
  have := Complex.abs_im_le_norm (I - (t : ℂ))
  simpa using this

theorem abs_le_norm_I_sub_ofReal (t : ℝ) : |t| ≤ ‖I - (t : ℂ)‖ := by
  have := Complex.abs_re_le_norm (I - (t : ℂ))
  simpa using this

/-- Points of depth `≤ 1/2` stay away from `i`. -/
theorem I_sub_ne_zero {w : ℂ} (hw : |w.im| ≤ 1 / 2) : I - w ≠ 0 := fun h => by
  have := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.I_im, Complex.zero_im] at this
  rw [abs_le] at hw
  linarith [hw.2]

theorem half_le_norm_I_sub {w : ℂ} (hw : |w.im| ≤ 1 / 2) : 1 / 2 ≤ ‖I - w‖ := by
  have h := Complex.abs_im_le_norm (I - w)
  simp only [Complex.sub_im, Complex.I_im] at h
  rw [abs_le] at hw
  have : 1 / 2 ≤ |1 - w.im| := by rw [abs_of_pos (by linarith)]; linarith
  linarith

theorem abs_re_le_norm_I_sub (w : ℂ) : |w.re| ≤ ‖I - w‖ := by
  have h := Complex.abs_re_le_norm (I - w)
  simpa [abs_neg] using h

theorem norm_I_sub_re_le {w : ℂ} (hw : |w.im| ≤ 1 / 2) : ‖I - (w.re : ℂ)‖ ≤ 2 * ‖I - w‖ := by
  have h1 : ‖I - (w.re : ℂ)‖ ^ 2 = w.re ^ 2 + 1 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  have h2 : ‖I - w‖ ^ 2 = w.re ^ 2 + (1 - w.im) ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; simp; ring
  rw [abs_le] at hw
  have h3 : ‖I - (w.re : ℂ)‖ ^ 2 ≤ (2 * ‖I - w‖) ^ 2 := by
    rw [mul_pow, h1, h2]; nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h3

theorem abs_re_sub_le_norm (w : ℂ) (t : ℝ) : |w.re - t| ≤ ‖w - t‖ := by
  have h := Complex.abs_re_le_norm (w - t)
  simpa using h

theorem pertFactor_sub_one {h θ : ℝ} (ν : ℤ → ℂ) (k : ℤ) (hν : I - ν k ≠ 0) {z : ℂ}
    (hz : z ≠ latPt h θ k) :
    pertFactor h θ ν k z - 1 =
      (z - I) * (ν k - latPt h θ k) / ((z - latPt h θ k) * (I - ν k)) := by
  have h1 : z - (latPt h θ k : ℂ) ≠ 0 := sub_ne_zero.mpr hz
  rw [pertFactor]
  field_simp
  ring

theorem norm_pertFactor_sub_one_le {h θ L : ℝ} {ν : ℤ → ℂ}
    (hL : ∀ k, ‖ν k - latPt h θ k‖ ≤ L) (k : ℤ) (hν : I - ν k ≠ 0) {z : ℂ}
    (hz : z ≠ latPt h θ k) :
    ‖pertFactor h θ ν k z - 1‖ ≤ L * ‖z - I‖ / (‖z - latPt h θ k‖ * ‖I - ν k‖) := by
  rw [pertFactor_sub_one ν k hν hz, norm_div, norm_mul, norm_mul]
  have h1 : 0 < ‖z - (latPt h θ k : ℂ)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have h2 : 0 < ‖I - ν k‖ := norm_pos_iff.mpr hν
  apply div_le_div_of_nonneg_right _ (by positivity)
  rw [mul_comm L]
  exact mul_le_mul_of_nonneg_left (hL k) (norm_nonneg _)

theorem abs_latPt_ge {h θ : ℝ} (hh : 0 < h) (hθ : |θ| ≤ 1) (k : ℤ) :
    |(k : ℝ)| * h - h ≤ |latPt h θ k| := by
  rw [latPt, abs_mul, abs_of_pos hh]
  have : |(k : ℝ)| - 1 ≤ |(k : ℝ) + θ| := by
    have h2 := abs_sub_abs_le_abs_sub (k : ℝ) (-θ)
    rw [sub_neg_eq_add, abs_neg] at h2
    linarith
  nlinarith

/-- **The factors converge.** Off the lattice, `Σ_k |r_k(z) − 1| < ∞`. -/
theorem summable_norm_pertFactor_sub_one {h θ L : ℝ} (hh : 0 < h) (hθ : |θ| ≤ 1) {ν : ℤ → ℂ}
    (hL : ∀ k, ‖ν k - latPt h θ k‖ ≤ L) (him : ∀ k, |(ν k).im| ≤ 1 / 2) {z : ℂ}
    (hz : ∀ k, z ≠ latPt h θ k) :
    Summable fun k => ‖pertFactor h θ ν k z - 1‖ := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  set K₀ : ℝ := 2 * (‖z‖ + L + 2 * h) / h with hK₀
  refine Summable.of_norm_bounded_eventually
    ((Real.summable_one_div_int_pow.mpr (by norm_num : 1 < 2)).mul_left
      (4 * L * ‖z - I‖ / h ^ 2)) ?_
  rw [Filter.eventually_cofinite]
  refine (Finset.Icc (-⌈K₀⌉) ⌈K₀⌉).finite_toSet.subset fun k hk => ?_
  simp only [Set.mem_setOf_eq, not_le] at hk
  simp only [Finset.coe_Icc, Set.mem_Icc]
  by_contra hout
  have hbig : K₀ < |(k : ℝ)| := by
    have : ⌈K₀⌉ < |k| := by
      rw [lt_abs]
      by_contra h'
      push Not at h'
      exact hout ⟨by linarith [neg_le_abs k, h'.2], h'.1⟩
    have h3 : K₀ ≤ (⌈K₀⌉ : ℝ) := Int.le_ceil K₀
    have h4 : ((⌈K₀⌉ : ℤ) : ℝ) < ((|k| : ℤ) : ℝ) := by exact_mod_cast this
    rw [Int.cast_abs] at h4
    linarith
  have hkh : 2 * (‖z‖ + L + 2 * h) < |(k : ℝ)| * h := by
    rw [hK₀, div_lt_iff₀ hh] at hbig; linarith
  have hμ := abs_latPt_ge hh hθ k
  have ha : |(k : ℝ)| * h / 2 ≤ ‖z - latPt h θ k‖ := by
    have := norm_sub_norm_le (latPt h θ k : ℂ) z
    rw [Complex.norm_real, Real.norm_eq_abs, norm_sub_rev] at this
    nlinarith [norm_nonneg z]
  have hb : |(k : ℝ)| * h / 2 ≤ ‖I - ν k‖ := by
    have h5 := abs_re_le_norm_I_sub (ν k)
    have h6 : |latPt h θ k| - L ≤ |(ν k).re| := by
      have := abs_sub_abs_le_abs_sub (latPt h θ k) (ν k).re
      rw [abs_sub_comm] at this
      linarith [(abs_re_sub_le_norm (ν k) (latPt h θ k)).trans (hL k)]
    linarith [norm_nonneg z]
  have hk0 : 0 < |(k : ℝ)| * h / 2 := by nlinarith [norm_nonneg z]
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at hk
  refine absurd hk (not_lt.mpr ((norm_pertFactor_sub_one_le hL k (I_sub_ne_zero (him k))
    (hz k)).trans ?_))
  have hden : (|(k : ℝ)| * h / 2) * (|(k : ℝ)| * h / 2) ≤ ‖z - latPt h θ k‖ * ‖I - ν k‖ :=
    mul_le_mul ha hb hk0.le (by positivity)
  rw [show 4 * L * ‖z - I‖ / h ^ 2 * (1 / (k : ℝ) ^ 2) =
    L * ‖z - I‖ / ((|(k : ℝ)| * h / 2) * (|(k : ℝ)| * h / 2)) by
      rw [show (|(k : ℝ)| * h / 2) * (|(k : ℝ)| * h / 2) = (k : ℝ) ^ 2 * h ^ 2 / 4 by
        rw [← sq_abs (k : ℝ)]; ring]
      field_simp]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) hden

theorem multipliable_pertFactor {h θ L : ℝ} (hh : 0 < h) (hθ : |θ| ≤ 1) {ν : ℤ → ℂ}
    (hL : ∀ k, ‖ν k - latPt h θ k‖ ≤ L) (him : ∀ k, |(ν k).im| ≤ 1 / 2) {z : ℂ}
    (hz : ∀ k, z ≠ latPt h θ k) :
    Multipliable fun k => pertFactor h θ ν k z := by
  have h := multipliable_one_add_of_summable (summable_norm_pertFactor_sub_one hh hθ hL him hz)
  simpa using h

theorem pertFactor_ne_zero {h θ : ℝ} (ν : ℤ → ℂ) (k : ℤ) (hν : I - ν k ≠ 0) {z : ℂ}
    (hz : z ≠ latPt h θ k) (hzν : z ≠ ν k) : pertFactor h θ ν k z ≠ 0 := by
  have h1 : z - (latPt h θ k : ℂ) ≠ 0 := sub_ne_zero.mpr hz
  have h3 : I - (latPt h θ k : ℂ) ≠ 0 := I_sub_ofReal_ne_zero _
  rw [pertFactor]
  exact mul_ne_zero (div_ne_zero (sub_ne_zero.mpr hzν) h1) (div_ne_zero h3 hν)

/-- The infinite product does not vanish away from the `ν_k`. -/
theorem tprod_pertFactor_ne_zero {h θ L : ℝ} (hh : 0 < h) (hθ : |θ| ≤ 1) {ν : ℤ → ℂ}
    (hL : ∀ k, ‖ν k - latPt h θ k‖ ≤ L) (him : ∀ k, |(ν k).im| ≤ 1 / 2) {z : ℂ}
    (hz : ∀ k, z ≠ latPt h θ k) (hzν : ∀ k, z ≠ ν k) : ∏' k, pertFactor h θ ν k z ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable (f := fun k => pertFactor h θ ν k z - 1)
    (fun k => by simpa using pertFactor_ne_zero ν k (I_sub_ne_zero (him k)) (hz k) (hzν k))
    (summable_norm_pertFactor_sub_one hh hθ hL him hz)
  simpa using h

/-! ### The uniform bound on the real line -/

/-- `δ = min(1, h/2)`. -/
def latDelta (h : ℝ) : ℝ := min 1 (h / 2)

/-- The constant of the near/far estimate. -/
def nearFarConst (h L : ℝ) : ℝ :=
  2 + 4 / h + 4 * (1 + L) * (1 / latDelta h + (1 + Real.log (4 * (L + 2) / h + 5)) / h)

/-- **The near/far estimate.** For points at distance `≥ h/2` from `x`,
`Σ_k |x − i| / (|x − μ_k| |i − ν_k|) ≤ C + (4(1 + L)/h) log(1 + |x|)`. -/
theorem sum_dist_near_far_le {h θ L : ℝ} (hh : 0 < h) (hθ : |θ| ≤ 1) {ν : ℤ → ℝ}
    (hL : ∀ k, |ν k - latPt h θ k| ≤ L) (x : ℝ) (S : Finset ℤ)
    (hS : ∀ k ∈ S, h / 2 ≤ |x - latPt h θ k|) :
    ∑ k ∈ S, ‖(x : ℂ) - I‖ / (|x - latPt h θ k| * ‖I - ν k‖) ≤
      nearFarConst h L + 4 * (1 + L) / h * Real.log (1 + |x|) := by
  classical
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL 0)
  set δ := latDelta h with hδ
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδh : δ ≤ h / 2 := min_le_right _ _
  set R := 2 * (|x| + L + 1) with hR
  have hR2 : 2 ≤ R := by rw [hR]; linarith [abs_nonneg x]
  have hxI : ‖(x : ℂ) - I‖ ≤ |x| + 1 := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, Complex.norm_I]
  rw [← Finset.sum_filter_add_sum_filter_not S (fun k => |latPt h θ k| < R)]
  set near := S.filter (fun k => |latPt h θ k| < R)
  set far := S.filter (fun k => ¬ |latPt h θ k| < R)
  -- the far part
  have hfar : ∑ k ∈ far, ‖(x : ℂ) - I‖ / (|x - latPt h θ k| * ‖I - ν k‖) ≤ 2 + 4 / h := by
    have hterm : ∀ k ∈ far, ‖(x : ℂ) - I‖ / (|x - latPt h θ k| * ‖I - ν k‖) ≤
        2 * R * (1 / latPt h θ k ^ 2) := by
      intro k hk
      have hμ : R ≤ |latPt h θ k| := by
        have := (Finset.mem_filter.mp hk).2; push Not at this; exact this
      have ha : |latPt h θ k| / 2 ≤ |x - latPt h θ k| := by
        have := abs_sub_abs_le_abs_sub (latPt h θ k) x
        rw [abs_sub_comm] at this
        linarith [abs_nonneg x]
      have hb : |latPt h θ k| / 2 ≤ ‖I - ν k‖ := by
        have h5 := abs_le_norm_I_sub_ofReal (ν k)
        have h6 := abs_sub_abs_le_abs_sub (latPt h θ k) (ν k)
        rw [abs_sub_comm (latPt h θ k) (ν k)] at h6
        linarith [hL k, abs_nonneg x]
      have hμ0 : 0 < |latPt h θ k| := by linarith
      have hden : (|latPt h θ k| / 2) * (|latPt h θ k| / 2) ≤
          |x - latPt h θ k| * ‖I - ν k‖ := mul_le_mul ha hb (by positivity) (abs_nonneg _)
      calc ‖(x : ℂ) - I‖ / (|x - latPt h θ k| * ‖I - ν k‖)
          ≤ (R / 2) / ((|latPt h θ k| / 2) * (|latPt h θ k| / 2)) :=
            div_le_div₀ (by positivity) (by rw [hR]; linarith) (by positivity) hden
        _ = 2 * R * (1 / latPt h θ k ^ 2) := by
            rw [← sq_abs (latPt h θ k)]; field_simp
    have htail := sum_inv_sq_far_le hh (by linarith : 0 < R) far fun k hk => by
      have := (Finset.mem_filter.mp hk).2; push Not at this; exact this
    calc _ ≤ ∑ k ∈ far, 2 * R * (1 / latPt h θ k ^ 2) := Finset.sum_le_sum hterm
      _ = 2 * R * ∑ k ∈ far, 1 / latPt h θ k ^ 2 := by rw [Finset.mul_sum]
      _ ≤ 2 * R * (2 * (1 / R ^ 2 + 1 / (h * R))) := by gcongr
      _ = 4 / R + 4 / h := by field_simp; ring
      _ ≤ 2 + 4 / h := by
          have : 4 / R ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
          linarith
  -- the near part
  have hnear_card : (near.card : ℝ) ≤ (4 * (L + 2) / h + 5) * (1 + |x|) := by
    set M : ℤ := ⌈R / h⌉ + 1 with hM
    have hsub : near ⊆ Finset.Icc (-M) M := by
      intro k hk
      have hμ := (Finset.mem_filter.mp hk).2
      have h1 := abs_latPt_ge hh hθ k
      have hk' : |(k : ℝ)| < R / h + 1 := by
        have h1' : |(k : ℝ)| * h < R + h := by linarith
        have h2' : |(k : ℝ)| < (R + h) / h := (lt_div_iff₀ hh).mpr h1'
        rwa [add_div, div_self hh.ne'] at h2'
      have hc : R / h ≤ (⌈R / h⌉ : ℝ) := Int.le_ceil _
      have hkM : (|k| : ℝ) < (M : ℝ) := by
        rw [hM]; push_cast; linarith
      have : |k| < M := by exact_mod_cast hkM
      rw [Finset.mem_Icc]
      constructor <;> linarith [neg_abs_le k, le_abs_self k]
    have hcard := Finset.card_le_card hsub
    rw [Int.card_Icc] at hcard
    have hceil : (0 : ℤ) ≤ ⌈R / h⌉ := Int.ceil_nonneg (by positivity)
    have hM0 : 0 ≤ M + 1 - -M := by rw [hM]; omega
    have h2 : (near.card : ℝ) ≤ ((M + 1 - -M : ℤ) : ℝ) := by
      have ht := Int.toNat_of_nonneg hM0
      calc (near.card : ℝ) ≤ ((M + 1 - -M).toNat : ℝ) := by exact_mod_cast hcard
        _ = (((M + 1 - -M).toNat : ℤ) : ℝ) := by norm_cast
        _ = ((M + 1 - -M : ℤ) : ℝ) := by rw [ht]
    have h3 : ((M + 1 - -M : ℤ) : ℝ) ≤ 2 * R / h + 5 := by
      rw [hM]; push_cast
      have := Int.ceil_lt_add_one (R / h)
      have e : 2 * R / h = 2 * (R / h) := by ring
      linarith
    have h4 : 2 * R / h + 5 ≤ (4 * (L + 2) / h + 5) * (1 + |x|) := by
      rw [hR]
      have hx0 := abs_nonneg x
      rw [show 2 * (2 * (|x| + L + 1)) / h = 4 * (|x| + L + 1) / h by ring]
      have hLx := mul_nonneg hL0 hx0
      have : 4 * (|x| + L + 1) / h ≤ 4 * (L + 2) / h * (1 + |x|) := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (by linarith) hh.le
      have h5 : (5 : ℝ) ≤ 5 * (1 + |x|) := by linarith
      linarith
    linarith
  have hKpos : 0 < 4 * (L + 2) / h + 5 := by positivity
  have hlog : Real.log near.card ≤ Real.log (4 * (L + 2) / h + 5) + Real.log (1 + |x|) := by
    rw [← Real.log_mul hKpos.ne' (by positivity)]
    rcases Nat.eq_zero_or_pos near.card with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]
      have hK1 : 1 ≤ 4 * (L + 2) / h + 5 := by
        have : 0 ≤ 4 * (L + 2) / h := by positivity
        linarith
      exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le hK1 (by linarith [abs_nonneg x]))
    · exact Real.log_le_log (by exact_mod_cast h0) hnear_card
  have hnear : ∑ k ∈ near, ‖(x : ℂ) - I‖ / (|x - latPt h θ k| * ‖I - ν k‖) ≤
      4 * (1 + L) * (1 / δ + (1 + Real.log near.card) / h) := by
    have hterm : ∀ k ∈ near, ‖(x : ℂ) - I‖ / (|x - latPt h θ k| * ‖I - ν k‖) ≤
        (1 + L) * (1 / max δ |0 - latPt h θ k|) + (1 + L) * (1 / max δ |x - latPt h θ k|) := by
      intro k hk
      have hka : h / 2 ≤ |x - latPt h θ k| := hS k (Finset.mem_filter.mp hk).1
      set a := |x - latPt h θ k|
      set b := ‖I - (ν k : ℂ)‖
      have ha0 : 0 < a := by linarith
      have hb1 : 1 ≤ b := one_le_norm_I_sub_ofReal _
      have hnum : ‖(x : ℂ) - I‖ ≤ a + L + b := by
        have e1 : ‖(x : ℂ) - I‖ ≤ ‖(x : ℂ) - ν k‖ + ‖(ν k : ℂ) - I‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        rw [show (x : ℂ) - ν k = ((x - ν k : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, norm_sub_rev (ν k : ℂ) I] at e1
        have : |x - ν k| ≤ a + L := by
          have := abs_sub_le x (latPt h θ k) (ν k)
          rw [abs_sub_comm (latPt h θ k)] at this
          linarith [hL k]
        linarith
      have hmax1 : max δ a = a := max_eq_right (by linarith)
      have hLb : L ≤ L * b := le_mul_of_one_le_right hL0 hb1
      have hmax0 : max δ |0 - latPt h θ k| ≤ (1 + L) * b := by
        apply max_le (by linarith)
        rw [zero_sub, abs_neg]
        have h5 := abs_le_norm_I_sub_ofReal (ν k)
        have h6 := abs_sub_abs_le_abs_sub (latPt h θ k) (ν k)
        rw [abs_sub_comm (latPt h θ k) (ν k)] at h6
        linarith [hL k]
      have hmax0pos : 0 < max δ |0 - latPt h θ k| := lt_max_of_lt_left hδ0
      rw [hmax1]
      have hb' : 1 / b ≤ (1 + L) * (1 / max δ |0 - latPt h θ k|) := by
        rw [mul_one_div, div_le_div_iff₀ (by linarith) hmax0pos]
        linarith
      calc ‖(x : ℂ) - I‖ / (a * b) ≤ (a + L + b) / (a * b) :=
            div_le_div_of_nonneg_right hnum (by positivity)
        _ = 1 / b + (1 + L / b) * (1 / a) := by field_simp; ring
        _ ≤ (1 + L) * (1 / max δ |0 - latPt h θ k|) + (1 + L) * (1 / a) := by
            have : L / b ≤ L := div_le_self hL0 hb1
            have ha1 : 0 ≤ 1 / a := by positivity
            have := mul_le_mul_of_nonneg_right (show 1 + L / b ≤ 1 + L by linarith) ha1
            linarith
    have hs1 := sum_inv_max_dist_le (θ := θ) hh hδ0 (hδh.trans (by linarith)) 0 near
    have hs2 := sum_inv_max_dist_le (θ := θ) hh hδ0 (hδh.trans (by linarith)) x near
    calc _ ≤ ∑ k ∈ near, ((1 + L) * (1 / max δ |0 - latPt h θ k|) +
          (1 + L) * (1 / max δ |x - latPt h θ k|)) := Finset.sum_le_sum hterm
      _ = (1 + L) * ∑ k ∈ near, 1 / max δ |0 - latPt h θ k| +
          (1 + L) * ∑ k ∈ near, 1 / max δ |x - latPt h θ k| := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ (1 + L) * (2 * (1 / δ + (1 + Real.log near.card) / h)) +
          (1 + L) * (2 * (1 / δ + (1 + Real.log near.card) / h)) := by gcongr
      _ = 4 * (1 + L) * (1 / δ + (1 + Real.log near.card) / h) := by ring
  have hfinal : 4 * (1 + L) * (1 / δ + (1 + Real.log near.card) / h) ≤
      4 * (1 + L) * (1 / δ + (1 + Real.log (4 * (L + 2) / h + 5)) / h) +
        4 * (1 + L) / h * Real.log (1 + |x|) := by
    have : (1 + Real.log near.card) / h ≤
        (1 + Real.log (4 * (L + 2) / h + 5)) / h + Real.log (1 + |x|) / h := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hh.le
    have h1L : 0 ≤ 4 * (1 + L) := by positivity
    calc 4 * (1 + L) * (1 / δ + (1 + Real.log near.card) / h)
        = 4 * (1 + L) / δ + 4 * (1 + L) * ((1 + Real.log near.card) / h) := by ring
      _ ≤ 4 * (1 + L) / δ + 4 * (1 + L) * ((1 + Real.log (4 * (L + 2) / h + 5)) / h +
          Real.log (1 + |x|) / h) := by gcongr
      _ = _ := by ring
  rw [nearFarConst, ← hδ]
  linarith

/-- `B₁ = π(1/2 + L/h)(1 + 2L) + 1` bounds the sine times the nearest factor. -/
def nearestConst (h L : ℝ) : ℝ := π * (1 / 2 + L / h) * (1 + 2 * L) + 1

/-- **The uniform bound on the real line.** Off the lattice, uniformly in the finite set `S` of
factors, `|sin((π/h)(x − θh)) Π_{k ∈ S} r_k(x)| ≤ K (1 + |x|)^p` with `K = B₁ e^{2L C}` and
`p = 8L(1 + L)/h`. -/
theorem norm_sin_mul_prod_pertFactor_le {h θ L : ℝ} (hh : 0 < h) (hθ : |θ| ≤ 1) {ν : ℤ → ℂ}
    (hL : ∀ k, ‖ν k - latPt h θ k‖ ≤ L) (him : ∀ k, |(ν k).im| ≤ 1 / 2) (S : Finset ℤ) (x : ℝ)
    (hx : ∀ k, x ≠ latPt h θ k) :
    ‖(Real.sin (π / h * (x - θ * h)) : ℂ) * ∏ k ∈ S, pertFactor h θ ν k x‖ ≤
      nearestConst h L * Real.exp (2 * L * nearFarConst h L) *
        (1 + |x|) ^ (2 * L * (4 * (1 + L) / h)) := by
  classical
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hLre : ∀ k, |(ν k).re - latPt h θ k| ≤ L := fun k =>
    (abs_re_sub_le_norm (ν k) (latPt h θ k)).trans (hL k)
  set k₀ : ℤ := round (x / h - θ) with hk₀
  set μ₀ := latPt h θ k₀ with hμ₀
  have hnear : |x - μ₀| ≤ h / 2 := by
    have := abs_sub_round (x / h - θ)
    rw [← hk₀] at this
    have e : x - μ₀ = h * (x / h - θ - k₀) := by rw [hμ₀, latPt]; field_simp; ring
    rw [e, abs_mul, abs_of_pos hh]
    nlinarith
  have hxμ₀ : x - μ₀ ≠ 0 := sub_ne_zero.mpr (hx k₀)
  -- the sine is `± sin((π/h)(x − μ₀))`
  have hsin : |Real.sin (π / h * (x - θ * h))| ≤ π / h * |x - μ₀| := by
    have e : π / h * (x - θ * h) = π / h * (x - μ₀) + k₀ * π := by
      rw [hμ₀, latPt]; field_simp; ring
    rw [e, Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
    refine (Real.abs_sin_le_abs).trans ?_
    rw [abs_mul, abs_of_pos (by positivity : 0 < π / h)]
  -- the other factors are `h/2`-far from `x`
  have hfar : ∀ k ∈ S.erase k₀, h / 2 ≤ |x - latPt h θ k| := by
    intro k hk
    have hne := Finset.ne_of_mem_erase hk
    have := latPt_sep (θ := θ) hh hne
    have h2 := abs_sub_le (latPt h θ k) x μ₀
    rw [abs_sub_comm (latPt h θ k) x] at h2
    linarith
  have hsum := sum_dist_near_far_le hh hθ (ν := fun k => (ν k).re) hLre x (S.erase k₀) hfar
  have hterm : ∀ k ∈ S.erase k₀, ‖pertFactor h θ ν k x - 1‖ ≤
      2 * L * (‖(x : ℂ) - I‖ / (|x - latPt h θ k| * ‖I - (((ν k).re : ℝ) : ℂ)‖)) := by
    intro k hk
    have hd : 0 < |x - latPt h θ k| := lt_of_lt_of_le (by positivity) (hfar k hk)
    have hb := half_le_norm_I_sub (him k)
    have hb' : 0 < ‖I - (((ν k).re : ℝ) : ℂ)‖ := by
      linarith [one_le_norm_I_sub_ofReal (ν k).re]
    have h2 := norm_I_sub_re_le (him k)
    have h1 := norm_pertFactor_sub_one_le hL k (I_sub_ne_zero (him k)) (z := (x : ℂ))
      (by exact_mod_cast hx k)
    rw [show (x : ℂ) - latPt h θ k = ((x - latPt h θ k : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs] at h1
    refine h1.trans ?_
    have hA : 0 ≤ L * ‖(x : ℂ) - I‖ := by positivity
    calc L * ‖(x : ℂ) - I‖ / (|x - latPt h θ k| * ‖I - ν k‖) =
        2 * (L * ‖(x : ℂ) - I‖) / (|x - latPt h θ k| * (2 * ‖I - ν k‖)) := by
          field_simp
      _ ≤ 2 * (L * ‖(x : ℂ) - I‖) / (|x - latPt h θ k| * ‖I - (((ν k).re : ℝ) : ℂ)‖) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity)
            (mul_le_mul_of_nonneg_left h2 hd.le)
      _ = 2 * L * (‖(x : ℂ) - I‖ / (|x - latPt h θ k| * ‖I - (((ν k).re : ℝ) : ℂ)‖)) := by
          ring
  have hrest : ‖∏ k ∈ S.erase k₀, pertFactor h θ ν k x‖ ≤
      Real.exp (2 * L * (nearFarConst h L + 4 * (1 + L) / h * Real.log (1 + |x|))) := by
    rw [norm_prod]
    calc ∏ k ∈ S.erase k₀, ‖pertFactor h θ ν k x‖
        ≤ ∏ k ∈ S.erase k₀, Real.exp ‖pertFactor h θ ν k x - 1‖ := by
          refine Finset.prod_le_prod (fun k _ => norm_nonneg _) fun k _ => ?_
          have := norm_sub_norm_le (pertFactor h θ ν k x) 1
          rw [norm_one] at this
          linarith [Real.add_one_le_exp ‖pertFactor h θ ν k x - 1‖]
      _ = Real.exp (∑ k ∈ S.erase k₀, ‖pertFactor h θ ν k x - 1‖) := by rw [Real.exp_sum]
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          calc ∑ k ∈ S.erase k₀, ‖pertFactor h θ ν k x - 1‖
              ≤ ∑ k ∈ S.erase k₀,
                  2 * L * (‖(x : ℂ) - I‖ / (|x - latPt h θ k| * ‖I - (((ν k).re : ℝ) : ℂ)‖)) :=
                Finset.sum_le_sum hterm
            _ = 2 * L * ∑ k ∈ S.erase k₀,
                  ‖(x : ℂ) - I‖ / (|x - latPt h θ k| * ‖I - (((ν k).re : ℝ) : ℂ)‖) := by
                rw [Finset.mul_sum]
            _ ≤ _ := mul_le_mul_of_nonneg_left hsum (by positivity)
  -- the sine and the nearest factor
  have hfirst : ‖(Real.sin (π / h * (x - θ * h)) : ℂ) *
      (if k₀ ∈ S then pertFactor h θ ν k₀ x else 1)‖ ≤ nearestConst h L := by
    have hsin1 : |Real.sin (π / h * (x - θ * h))| ≤ 1 := Real.abs_sin_le_one _
    have hB1 : 1 ≤ nearestConst h L := by
      unfold nearestConst; have : 0 ≤ π * (1 / 2 + L / h) * (1 + 2 * L) := by positivity
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    split_ifs with hk
    · rw [pertFactor, norm_mul, norm_div, norm_div,
        show (x : ℂ) - latPt h θ k₀ = ((x - μ₀ : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      have hxν : ‖(x : ℂ) - ν k₀‖ ≤ h / 2 + L := by
        have := norm_sub_le_norm_sub_add_norm_sub (x : ℂ) (μ₀ : ℂ) (ν k₀)
        rw [show (x : ℂ) - μ₀ = ((x - μ₀ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, norm_sub_rev (μ₀ : ℂ)] at this
        linarith [hL k₀]
      have hb1 := half_le_norm_I_sub (him k₀)
      have hratio : ‖I - (latPt h θ k₀ : ℂ)‖ / ‖I - ν k₀‖ ≤ 1 + 2 * L := by
        rw [div_le_iff₀ (by linarith)]
        have := norm_sub_le_norm_sub_add_norm_sub I (ν k₀) (latPt h θ k₀ : ℂ)
        nlinarith [hL k₀]
      have hpos : 0 < |x - μ₀| := abs_pos.mpr hxμ₀
      calc |Real.sin (π / h * (x - θ * h))| * (‖(x : ℂ) - ν k₀‖ / |x - μ₀| *
            (‖I - (latPt h θ k₀ : ℂ)‖ / ‖I - ν k₀‖))
          ≤ (π / h * |x - μ₀|) * (‖(x : ℂ) - ν k₀‖ / |x - μ₀| * (1 + 2 * L)) := by gcongr
        _ = π / h * ‖(x : ℂ) - ν k₀‖ * (1 + 2 * L) := by field_simp
        _ ≤ π / h * (h / 2 + L) * (1 + 2 * L) := by gcongr
        _ = π * (1 / 2 + L / h) * (1 + 2 * L) := by field_simp
        _ ≤ nearestConst h L := by unfold nearestConst; linarith
    · rw [norm_one, mul_one]; linarith
  have hsplit : ∏ k ∈ S, pertFactor h θ ν k x =
      (if k₀ ∈ S then pertFactor h θ ν k₀ x else 1) * ∏ k ∈ S.erase k₀, pertFactor h θ ν k x := by
    split_ifs with hk
    · exact (Finset.mul_prod_erase S (fun k => pertFactor h θ ν k x) hk).symm
    · rw [Finset.erase_eq_of_notMem hk, one_mul]
  rw [hsplit, ← mul_assoc, norm_mul]
  have hpow : Real.exp (2 * L * (nearFarConst h L + 4 * (1 + L) / h * Real.log (1 + |x|))) =
      Real.exp (2 * L * nearFarConst h L) * (1 + |x|) ^ (2 * L * (4 * (1 + L) / h)) := by
    rw [Real.rpow_def_of_pos (by positivity), ← Real.exp_add]
    congr 1; ring
  have hB0 : 0 ≤ nearestConst h L := by unfold nearestConst; positivity
  calc _ ≤ nearestConst h L * Real.exp (2 * L * (nearFarConst h L + 4 * (1 + L) / h *
        Real.log (1 + |x|))) := mul_le_mul hfirst hrest (norm_nonneg _) hB0
    _ = _ := by rw [hpow]; ring

end GaloisForLFunctions.ZeroConfigurationGeometry
