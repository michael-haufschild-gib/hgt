import GaloisForLFunctions.RHTower.RiemannKernelSpikePrimeSums

/-!
# Kraft-sparse spike combs of Riemann's kernel are Weil-positive

For a finite set of levels `s` and real coefficients `a`, the spike comb is
`F = Σ_{L ∈ s} a_L P_L` (`spikeComb`), where `P_L` is the thin spike of Riemann's kernel `Φ` at
level `L` (`combSpike`).

**Theorem** (`eventually_re_W_spikeComb_pos`). The following holds for all large `L₀`. Suppose
- every level is at least `L₀`,
- distinct levels are at least `4/Y(L₀)` apart (`Y(L) = 2πe^{2L}`),
- the Kraft sum `Σ_L (L + 1)² e^{−L}` is at most `1`,
- and some coefficient is nonzero.
Then `Re W(F, F) > 0`. No hypothesis on the zeros of `ζ` is used.

About `e^L/L²` spikes are allowed near level `L`. The obstruction is the opposite-side prime sum
near `X = e^{2L}`, which the trivial count controls exactly when `Σ_L e^{−L}` (up to the factor
`(L + 1)²`) is bounded. This is the square-root-of-`X` limit, written as a sparsity condition.

**Proof** (`re_W_spikeComb_ge`). In the explicit formula
`W = pole + arch − Σ_n w_n (A_F(log n) + A_F(−log n))`:
- *Pole.* `F` is even, so the pole term is `2(∫F e^{u/2})² ≥ 0`.
- *Disjointness.* Distinct spikes have disjoint supports, so `∫F² = Q := Σ a_L² r_L²`.
- *Archimedean term.* It is at least `(ℓ − 10)Q − (ℓM/π)(∫|F|)²`. Since
  `∫|F| ≤ (2K/π)Σ|a_L| r_L e^{−L}`, we get `(∫|F|)² ≤ (4K²/π²)e^{−L₀}Q`. With
  `M = π³e^{L₀}/(8K²)` the term is at least `(ℓ/2 − 10)Q`.
- *Primes.* The pair bound has two parts.
  - The same-side kernel has row and column sums at most `2G` with `G ≤ 8` (levels are separated).
  - The opposite-side part is the rank-one form `2(Σ|a_L| r_L v_L)² ≤ 2Q` (Kraft).
  - Together the prime term is at most `2K²(16σ₃/π + 2)Q`, where `σ₃ = Σ w_n/n`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-- The spike comb `F = Σ_{L ∈ s} a_L P_L`. -/
def spikeComb (s : Finset ℝ) (a : ℝ → ℝ) (u : ℝ) : ℝ := ∑ L ∈ s, a L * combSpike L u

/-- The autocorrelation `A_F(x) = ∫ F(u) F(u − x) du` of the comb. -/
def spikeCombLag (s : Finset ℝ) (a : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ u, spikeComb s a u * spikeComb s a (u - x)

theorem contDiff_spikeComb (s : Finset ℝ) (a : ℝ → ℝ) : ContDiff ℝ (⊤ : ℕ∞) (spikeComb s a) := by
  unfold spikeComb
  exact ContDiff.sum fun L _ => contDiff_const.mul (contDiff_combSpike L)

theorem continuous_spikeComb (s : Finset ℝ) (a : ℝ → ℝ) : Continuous (spikeComb s a) :=
  (contDiff_spikeComb s a).continuous

theorem spikeComb_neg (s : Finset ℝ) (a : ℝ → ℝ) (u : ℝ) : spikeComb s a (-u) = spikeComb s a u := by
  unfold spikeComb; simp_rw [combSpike_neg]

/-- A support radius of the comb. -/
def spikeCombRadius (s : Finset ℝ) : ℝ := ∑ L ∈ s, (|L| + 3 * edgeWidth L)

theorem spikeComb_eq_zero_of_ge {s : Finset ℝ} {a : ℝ → ℝ} {u : ℝ} (hu : spikeCombRadius s ≤ |u|) :
    spikeComb s a u = 0 := by
  unfold spikeComb
  refine Finset.sum_eq_zero fun L hL => ?_
  have h1 : |L| + 3 * edgeWidth L ≤ spikeCombRadius s := by
    unfold spikeCombRadius
    exact Finset.single_le_sum (f := fun L => |L| + 3 * edgeWidth L)
      (fun L _ => by have := edgeWidth_pos L; positivity) hL
  rw [combSpike_eq_zero_of_ge (by linarith [le_abs_self L]), mul_zero]

theorem hasCompactSupport_spikeComb (s : Finset ℝ) (a : ℝ → ℝ) : HasCompactSupport (spikeComb s a) := by
  refine HasCompactSupport.intro
    (isCompact_Icc (a := -spikeCombRadius s) (b := spikeCombRadius s)) fun u hu => ?_
  apply spikeComb_eq_zero_of_ge
  rw [Set.mem_Icc, not_and_or] at hu
  rcases hu with h | h
  · push Not at h; exact le_abs.2 (Or.inr (by linarith))
  · push Not at h; exact le_abs.2 (Or.inl h.le)

theorem tsupport_ofReal_spikeComb (s : Finset ℝ) (a : ℝ → ℝ) :
    tsupport (fun u => (spikeComb s a u : ℂ)) ⊆ Icc (-spikeCombRadius s) (spikeCombRadius s) := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  by_contra hc
  apply hu
  have : spikeCombRadius s ≤ |u| := by
    rw [Set.mem_Icc, not_and_or] at hc
    rcases hc with h | h
    · push Not at h; exact le_abs.2 (Or.inr (by linarith))
    · push Not at h; exact le_abs.2 (Or.inl h.le)
  simp [spikeComb_eq_zero_of_ge this]

theorem contDiff_ofReal_spikeComb (s : Finset ℝ) (a : ℝ → ℝ) :
    ContDiff ℝ 2 (fun u => (spikeComb s a u : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp ((contDiff_spikeComb s a).of_le (WithTop.coe_le_coe.2 le_top))

theorem weilTest_ofReal_spikeComb (s : Finset ℝ) (a : ℝ → ℝ) (x : ℝ) :
    EF.weilTest (fun u => (spikeComb s a u : ℂ)) (fun u => (spikeComb s a u : ℂ)) x =
      (spikeCombLag s a x : ℂ) := by
  rw [WeilSpectral.weilTest_apply, spikeCombLag, ← integral_complex_ofReal]
  congr 1; funext u
  rw [Complex.conj_ofReal]; push_cast; rfl

/-! ## The autocorrelation of a comb -/

theorem spikeCombLag_neg (s : Finset ℝ) (a : ℝ → ℝ) (y : ℝ) :
    spikeCombLag s a (-y) = spikeCombLag s a y := by
  unfold spikeCombLag
  have h := integral_add_right_eq_self (μ := volume)
    (fun v => spikeComb s a (v - y) * spikeComb s a v) y
  simp only [add_sub_cancel_right] at h
  rw [show (fun u => spikeComb s a u * spikeComb s a (u - -y)) =
    fun u => spikeComb s a u * spikeComb s a (u + y) by funext u; rw [sub_neg_eq_add]]
  rw [h]
  congr 1; funext v; ring

theorem spikeCombLag_eq (s : Finset ℝ) (a : ℝ → ℝ) (x : ℝ) :
    spikeCombLag s a x = ∑ L ∈ s, ∑ L' ∈ s, a L * a L' *
      ∫ u, combSpike L u * combSpike L' (u - x) := by
  unfold spikeCombLag spikeComb
  have hpt : (fun u => (∑ L ∈ s, a L * combSpike L u) * ∑ L' ∈ s, a L' * combSpike L' (u - x)) =
      fun u => ∑ L ∈ s, ∑ L' ∈ s, a L * a L' * (combSpike L u * combSpike L' (u - x)) := by
    funext u
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun L _ => Finset.sum_congr rfl fun L' _ => ?_
    ring
  rw [hpt, integral_finsetSum _ fun L _ => integrable_finsetSum _ fun L' _ =>
    (integrable_combSpike_lag L L' x).const_mul _]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [integral_finsetSum _ fun L' _ => (integrable_combSpike_lag L L' x).const_mul _]
  refine Finset.sum_congr rfl fun L' _ => ?_
  rw [integral_const_mul]

theorem integral_combSpike_lag_nonneg (L L' x : ℝ) :
    0 ≤ ∫ u, combSpike L u * combSpike L' (u - x) :=
  integral_nonneg fun _ => mul_nonneg (combSpike_nonneg _ _) (combSpike_nonneg _ _)

theorem spikeCombLag_le (s : Finset ℝ) (a : ℝ → ℝ) (x : ℝ) :
    spikeCombLag s a x ≤ ∑ L ∈ s, ∑ L' ∈ s, |a L| * |a L'| *
      ∫ u, combSpike L u * combSpike L' (u - x) := by
  rw [spikeCombLag_eq]
  refine Finset.sum_le_sum fun L _ => Finset.sum_le_sum fun L' _ => ?_
  have h0 := integral_combSpike_lag_nonneg L L' x
  apply mul_le_mul_of_nonneg_right _ h0
  rw [← abs_mul]; exact le_abs_self _

/-! ## Disjoint spikes -/

theorem edgeWidth_anti {L L' : ℝ} (h : L ≤ L') : edgeWidth L' ≤ edgeWidth L := by
  unfold edgeWidth
  apply one_div_le_one_div_of_le (edgeRate_pos L)
  unfold edgeRate
  have := Real.exp_le_exp.mpr (show 2 * L ≤ 2 * L' by linarith)
  nlinarith [Real.pi_pos]

/-- Spikes at levels `≥ L₀` that are `4/Y(L₀)` apart have disjoint supports. -/
theorem combSpike_mul_eq_zero {L₀ L L' : ℝ} (hL : L₀ ≤ L) (hL' : L₀ ≤ L')
    (hsep : 4 * edgeWidth L₀ ≤ |L - L'|) (u : ℝ) : combSpike L u * combSpike L' u = 0 := by
  by_contra hne
  have ha : combSpike L u ≠ 0 := left_ne_zero_of_mul hne
  have hb : combSpike L' u ≠ 0 := right_ne_zero_of_mul hne
  obtain ⟨ha1, ha2⟩ := combSpike_mem_of_ne_zero ha
  obtain ⟨hb1, hb2⟩ := combSpike_mem_of_ne_zero hb
  have hw := edgeWidth_anti hL
  have hw' := edgeWidth_anti hL'
  have hw0 := edgeWidth_pos L₀
  have : |L - L'| < 3 * edgeWidth L₀ := by
    rw [abs_lt]; constructor <;> linarith
  linarith

theorem spikeComb_sq {s : Finset ℝ} {a : ℝ → ℝ}
    (hdisj : ∀ L ∈ s, ∀ L' ∈ s, L ≠ L' → ∀ u, combSpike L u * combSpike L' u = 0) (u : ℝ) :
    spikeComb s a u ^ 2 = ∑ L ∈ s, a L ^ 2 * combSpike L u ^ 2 := by
  unfold spikeComb
  rw [sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun L hL => ?_
  rw [Finset.sum_eq_single L]
  · ring
  · intro L' hL' hne
    rw [show a L * combSpike L u * (a L' * combSpike L' u) =
      a L * a L' * (combSpike L u * combSpike L' u) by ring, hdisj L hL L' hL' (Ne.symm hne) u,
      mul_zero]
  · intro h; exact absurd hL h

theorem integral_spikeComb_sq {s : Finset ℝ} {a : ℝ → ℝ}
    (hdisj : ∀ L ∈ s, ∀ L' ∈ s, L ≠ L' → ∀ u, combSpike L u * combSpike L' u = 0) :
    ∫ u, spikeComb s a u ^ 2 = ∑ L ∈ s, a L ^ 2 * spikeScale L ^ 2 := by
  rw [show (fun u => spikeComb s a u ^ 2) = fun u => ∑ L ∈ s, a L ^ 2 * combSpike L u ^ 2 by
    funext u; exact spikeComb_sq hdisj u]
  rw [integral_finsetSum _ fun L _ => (integrable_combSpike_sq L).const_mul _]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [integral_const_mul, spikeScale_sq]

/-! ## The archimedean term -/

/-- `∫P_L ≤ (2K/π) e^{−L} r_L`. -/
theorem integral_combSpike_le_scale {L : ℝ} (hL : 1 ≤ L) :
    ∫ u, combSpike L u ≤ 2 * spikeAmpConst / π * Real.exp (-L) * spikeScale L := by
  have h1 := integral_combSpike_le hL
  have hA := spikeAmp_le_scale hL
  have hc := spikeRate_pos hL
  have he7 := seven_le_exp_two_mul hL
  have hπ := Real.pi_gt_three
  have hcY : π * Real.exp (2 * L) ≤ spikeRate L := by unfold spikeRate edgeRate; nlinarith
  have hK := spikeAmpConst_pos
  have hr := spikeScale_nonneg L
  refine h1.trans ?_
  have hexp : Real.exp L * Real.exp (-L) = 1 := by rw [← Real.exp_add]; simp
  have he2 : Real.exp (2 * L) = Real.exp L * Real.exp L := by rw [← Real.exp_add]; ring_nf
  rw [mul_div_assoc', div_le_iff₀ hc]
  have hπ0 : π ≠ 0 := Real.pi_ne_zero
  calc 2 * spikeAmp L ≤ 2 * (spikeAmpConst * Real.exp L * spikeScale L) := by linarith
    _ = 2 * (spikeAmpConst * Real.exp L * spikeScale L) * (Real.exp L * Real.exp (-L)) := by
        rw [hexp, mul_one]
    _ = 2 * spikeAmpConst / π * Real.exp (-L) * spikeScale L * (π * Real.exp (2 * L)) := by
        rw [he2]; field_simp
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left hcY
        have := Real.exp_pos (-L); positivity

theorem integral_abs_spikeComb_le (s : Finset ℝ) (a : ℝ → ℝ) :
    ∫ u, ‖(spikeComb s a u : ℂ)‖ ≤ ∑ L ∈ s, |a L| * ∫ u, combSpike L u := by
  have hint : Integrable (fun u => ∑ L ∈ s, |a L| * combSpike L u) :=
    integrable_finsetSum _ fun L _ => (integrable_combSpike L).const_mul _
  have hF : Integrable (fun u => ‖(spikeComb s a u : ℂ)‖) := by
    have h := ((continuous_spikeComb s a).integrable_of_hasCompactSupport (μ := volume)
      (hasCompactSupport_spikeComb s a)).norm
    refine h.congr (Eventually.of_forall fun u => ?_)
    simp only [Complex.norm_real]
  calc ∫ u, ‖(spikeComb s a u : ℂ)‖
      ≤ ∫ u, ∑ L ∈ s, |a L| * combSpike L u := by
        refine integral_mono hF hint fun u => ?_
        simp only [Complex.norm_real, Real.norm_eq_abs]
        unfold spikeComb
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun L _ => ?_
        rw [abs_mul, abs_of_nonneg (combSpike_nonneg L u)]
    _ = _ := by
        rw [integral_finsetSum _ fun L _ => (integrable_combSpike L).const_mul _]
        refine Finset.sum_congr rfl fun L _ => ?_
        rw [integral_const_mul]

/-- **The archimedean band.** `M = π³ e^{L₀}/(8K²)`. -/
def spikeBand (L₀ : ℝ) : ℝ := π ^ 3 * Real.exp L₀ / (8 * spikeAmpConst ^ 2)

theorem spikeBand_pos (L₀ : ℝ) : 0 < spikeBand L₀ := by
  unfold spikeBand; have := spikeAmpConst_pos; positivity

/-- `(ℓM/π)(∫|F|)² ≤ (ℓ/2)Q` for Kraft-sparse combs. -/
theorem arch_correction_le {L₀ : ℝ} (hL₀ : 1 ≤ L₀) {s : Finset ℝ} {a : ℝ → ℝ}
    (hs : ∀ L ∈ s, L₀ ≤ L) (hkraft : ∑ L ∈ s, (L + 1) ^ 2 * Real.exp (-L) ≤ 1) {ℓ : ℝ}
    (hℓ : 0 ≤ ℓ) :
    ℓ * spikeBand L₀ / π * (∫ u, ‖(spikeComb s a u : ℂ)‖) ^ 2 ≤
      ℓ / 2 * ∑ L ∈ s, a L ^ 2 * spikeScale L ^ 2 := by
  have hK := spikeAmpConst_pos
  have hπ := Real.pi_pos
  have h1 := integral_abs_spikeComb_le s a
  have h2 : ∑ L ∈ s, |a L| * ∫ u, combSpike L u ≤
      2 * spikeAmpConst / π * ∑ L ∈ s, (|a L| * spikeScale L) * Real.exp (-L) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun L hL => ?_
    have := integral_combSpike_le_scale (hL₀.trans (hs L hL))
    calc |a L| * ∫ u, combSpike L u
        ≤ |a L| * (2 * spikeAmpConst / π * Real.exp (-L) * spikeScale L) :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = _ := by ring
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun L => |a L| * spikeScale L) (fun L => Real.exp (-L))
  have hexp : ∑ L ∈ s, Real.exp (-L) ^ 2 ≤ Real.exp (-L₀) := by
    calc ∑ L ∈ s, Real.exp (-L) ^ 2
        ≤ ∑ L ∈ s, Real.exp (-L₀) * ((L + 1) ^ 2 * Real.exp (-L)) := by
          refine Finset.sum_le_sum fun L hL => ?_
          have hL1 : 1 ≤ L := hL₀.trans (hs L hL)
          have e1 : Real.exp (-L) ^ 2 = Real.exp (-L) * Real.exp (-L) := sq _
          have e2 : Real.exp (-L) ≤ Real.exp (-L₀) := Real.exp_le_exp.mpr (by linarith [hs L hL])
          have e3 : 1 ≤ (L + 1) ^ 2 := by nlinarith
          have he := Real.exp_pos (-L)
          rw [e1]
          calc Real.exp (-L) * Real.exp (-L) ≤ Real.exp (-L₀) * Real.exp (-L) :=
                mul_le_mul_of_nonneg_right e2 he.le
            _ ≤ Real.exp (-L₀) * ((L + 1) ^ 2 * Real.exp (-L)) := by
                apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; nlinarith
      _ = Real.exp (-L₀) * ∑ L ∈ s, (L + 1) ^ 2 * Real.exp (-L) := by rw [Finset.mul_sum]
      _ ≤ Real.exp (-L₀) * 1 := mul_le_mul_of_nonneg_left hkraft (Real.exp_pos _).le
      _ = _ := mul_one _
  have hb : ∑ L ∈ s, (|a L| * spikeScale L) ^ 2 = ∑ L ∈ s, a L ^ 2 * spikeScale L ^ 2 := by
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [mul_pow, sq_abs]
  rw [hb] at hcs
  have hQ0 : 0 ≤ ∑ L ∈ s, a L ^ 2 * spikeScale L ^ 2 :=
    Finset.sum_nonneg fun L _ => by positivity
  have hI0 : 0 ≤ ∫ u, ‖(spikeComb s a u : ℂ)‖ := integral_nonneg fun _ => norm_nonneg _
  have hsq : (∫ u, ‖(spikeComb s a u : ℂ)‖) ^ 2 ≤
      (2 * spikeAmpConst / π) ^ 2 * (Real.exp (-L₀) * ∑ L ∈ s, a L ^ 2 * spikeScale L ^ 2) := by
    have h3 := h1.trans h2
    have h4 : (∫ u, ‖(spikeComb s a u : ℂ)‖) ^ 2 ≤
        (2 * spikeAmpConst / π * ∑ L ∈ s, (|a L| * spikeScale L) * Real.exp (-L)) ^ 2 :=
      pow_le_pow_left₀ hI0 h3 2
    refine h4.trans ?_
    rw [mul_pow]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    refine hcs.trans ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hexp hQ0
  have hcoef : 0 ≤ ℓ * spikeBand L₀ / π := by have := spikeBand_pos L₀; positivity
  calc ℓ * spikeBand L₀ / π * (∫ u, ‖(spikeComb s a u : ℂ)‖) ^ 2
      ≤ ℓ * spikeBand L₀ / π * ((2 * spikeAmpConst / π) ^ 2 *
          (Real.exp (-L₀) * ∑ L ∈ s, a L ^ 2 * spikeScale L ^ 2)) :=
        mul_le_mul_of_nonneg_left hsq hcoef
    _ = ℓ / 2 * (∑ L ∈ s, a L ^ 2 * spikeScale L ^ 2) * (Real.exp L₀ * Real.exp (-L₀)) := by
        unfold spikeBand; field_simp; ring
    _ = _ := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-! ## The prime term -/

/-- `σ₃ = Σ_n w_n/n`. -/
def spikeHarmonicConst : ℝ := ∑' n : ℕ, spikePrimeWeight n * Real.exp (-Real.log n)

theorem summable_spikeHarmonic : Summable fun n : ℕ => spikePrimeWeight n * Real.exp (-Real.log n) := by
  have hsum : Summable fun n : ℕ => 4 * ((n : ℝ) ^ ((5 : ℝ) / 4))⁻¹ :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (spikePrimeWeight_nonneg n)
    (Real.exp_pos _).le) (fun n => ?_) hsum
  unfold spikePrimeWeight
  split_ifs with h2
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
    have hΛ : ArithmeticFunction.vonMangoldt n / Real.sqrt n ≤ Real.log n * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
      rw [div_eq_mul_inv, Real.sqrt_eq_rpow, ← Real.rpow_neg hn0.le]
      exact mul_le_mul_of_nonneg_right ArithmeticFunction.vonMangoldt_le_log (by positivity)
    have hlogle : Real.log n ≤ (n : ℝ) ^ ((1 : ℝ) / 4) / (1 / 4) :=
      Real.log_le_rpow_div hn0.le (by norm_num)
    have hexp : Real.exp (-Real.log n) = (n : ℝ) ^ (-(1 : ℝ)) := by
      rw [Real.rpow_def_of_pos hn0]; ring_nf
    rw [hexp]
    calc ArithmeticFunction.vonMangoldt n / Real.sqrt n * (n : ℝ) ^ (-(1 : ℝ))
        ≤ Real.log n * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 : ℝ)) :=
          mul_le_mul_of_nonneg_right hΛ (by positivity)
      _ ≤ (n : ℝ) ^ ((1 : ℝ) / 4) / (1 / 4) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 : ℝ)) := by
          gcongr
      _ = 4 * ((n : ℝ) ^ ((1 : ℝ) / 4) * (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(1 : ℝ))) := by ring
      _ = 4 * ((n : ℝ) ^ ((5 : ℝ) / 4))⁻¹ := by
          rw [← Real.rpow_add hn0, ← Real.rpow_add hn0, ← Real.rpow_neg hn0.le]; norm_num
  · simp only [zero_mul]; positivity

theorem sum_harmonic_le (N : ℕ) :
    ∑ n ∈ Finset.range N, spikePrimeWeight n * Real.exp (-Real.log n) ≤ spikeHarmonicConst :=
  summable_spikeHarmonic.sum_le_tsum _ fun n _ =>
    mul_nonneg (spikePrimeWeight_nonneg n) (Real.exp_pos _).le

theorem spikeHarmonicConst_nonneg : 0 ≤ spikeHarmonicConst :=
  tsum_nonneg fun n => mul_nonneg (spikePrimeWeight_nonneg n) (Real.exp_pos _).le

/-- A bilinear form with nonnegative entries is at most its row/column bound times `Σ b²`. -/
theorem double_sum_le_of_row_col_bound {s : Finset ℝ} {b : ℝ → ℝ} {k : ℝ → ℝ → ℝ} {R : ℝ}
    (hk : ∀ L ∈ s, ∀ L' ∈ s, 0 ≤ k L L') (hrow : ∀ L ∈ s, ∑ L' ∈ s, k L L' ≤ R)
    (hcol : ∀ L' ∈ s, ∑ L ∈ s, k L L' ≤ R) :
    ∑ L ∈ s, ∑ L' ∈ s, b L * b L' * k L L' ≤ R * ∑ L ∈ s, b L ^ 2 := by
  have hpt : ∀ L ∈ s, ∀ L' ∈ s, b L * b L' * k L L' ≤
      (b L ^ 2 * k L L' + b L' ^ 2 * k L L') / 2 := fun L hL L' hL' => by
    have := hk L hL L' hL'
    nlinarith [sq_nonneg (b L - b L'), mul_nonneg (sq_nonneg (b L - b L')) this]
  calc ∑ L ∈ s, ∑ L' ∈ s, b L * b L' * k L L'
      ≤ ∑ L ∈ s, ∑ L' ∈ s, (b L ^ 2 * k L L' + b L' ^ 2 * k L L') / 2 :=
        Finset.sum_le_sum fun L hL => Finset.sum_le_sum fun L' hL' => hpt L hL L' hL'
    _ = (∑ L ∈ s, ∑ L' ∈ s, b L ^ 2 * k L L') / 2 +
          (∑ L ∈ s, ∑ L' ∈ s, b L' ^ 2 * k L L') / 2 := by
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun L _ => ?_
        rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun L' _ => ?_
        ring
    _ = (∑ L ∈ s, b L ^ 2 * ∑ L' ∈ s, k L L') / 2 +
          (∑ L' ∈ s, b L' ^ 2 * ∑ L ∈ s, k L L') / 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm (s := s) (t := s) (f := fun L L' => b L' ^ 2 * k L L')]
    _ ≤ (∑ L ∈ s, b L ^ 2 * R) / 2 + (∑ L' ∈ s, b L' ^ 2 * R) / 2 := by
        gcongr with L hL L' hL'
        · exact hrow L hL
        · exact hcol L' hL'
    _ = R * ∑ L ∈ s, b L ^ 2 := by rw [← Finset.sum_mul]; ring

/-- The separated-sum constant `G = 2e^{κσ/2}/(κσ) ≤ 8` at `κ = c(L₀) − 1`, `σ = 4/Y(L₀)`. -/
theorem separated_const_le {L₀ : ℝ} (hL₀ : 1 ≤ L₀) :
    2 * Real.exp ((spikeRate L₀ - 1) * (4 * edgeWidth L₀) / 2) /
        ((spikeRate L₀ - 1) * (4 * edgeWidth L₀)) ≤ 8 := by
  have hY := (edgeRate_ge hL₀).1
  have hY0 := edgeRate_pos L₀
  have ht : (spikeRate L₀ - 1) * (4 * edgeWidth L₀) = 4 - 22 / edgeRate L₀ := by
    unfold spikeRate edgeWidth; field_simp; ring
  rw [ht]
  have h1 : 22 / edgeRate L₀ ≤ 2 := by rw [div_le_iff₀ hY0]; linarith
  have h2 : 0 ≤ 22 / edgeRate L₀ := by positivity
  have he : Real.exp ((4 - 22 / edgeRate L₀) / 2) ≤ Real.exp 2 := Real.exp_le_exp.mpr (by linarith)
  have he2 : Real.exp 2 < 8 := by
    have h := Real.exp_one_lt_d9
    have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]; nlinarith [Real.exp_pos 1]
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **The prime term of a comb.** -/
theorem sum_prime_spikeComb_le {L₀ : ℝ} (hL₀ : 1 ≤ L₀) {s : Finset ℝ} {a : ℝ → ℝ}
    (hs : ∀ L ∈ s, L₀ ≤ L) (hsep : ∀ L ∈ s, ∀ L' ∈ s, L ≠ L' → 4 * edgeWidth L₀ ≤ |L - L'|)
    (hkraft : ∑ L ∈ s, (L + 1) ^ 2 * Real.exp (-L) ≤ 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, spikePrimeWeight n * (spikeCombLag s a (Real.log n) +
        spikeCombLag s a (-Real.log n)) ≤
      2 * spikeAmpConst ^ 2 * (16 / π * spikeHarmonicConst + 2) * ∑ L ∈ s, a L ^ 2 * spikeScale L ^ 2 := by
  have hK := spikeAmpConst_pos
  have hπ := Real.pi_pos
  set κ := spikeRate L₀ - 1 with hκ
  set σ := 4 * edgeWidth L₀ with hσ
  have hκ0 : 0 < κ := by rw [hκ]; unfold spikeRate; linarith [(edgeRate_ge hL₀).1]
  have hσ0 : 0 < σ := by rw [hσ]; have := edgeWidth_pos L₀; positivity
  have hG := separated_const_le hL₀
  rw [← hκ, ← hσ] at hG
  -- separated row sums
  have hsepσ : ∀ y ∈ s, ∀ y' ∈ s, y ≠ y' → σ ≤ |y - y'| := hsep
  have hrowG : ∀ z, ∑ L' ∈ s, Real.exp (-(κ * |z - L'|)) ≤ 8 := fun z =>
    (sum_exp_neg_abs_le_of_separated hσ0 hκ0 hsepσ z).trans hG
  set b : ℝ → ℝ := fun L => |a L| * spikeScale L with hb
  set v : ℝ → ℝ := fun L => (L + 1) * Real.exp (-(L / 2)) with hv
  have hb0 : ∀ L, 0 ≤ b L := fun L => mul_nonneg (abs_nonneg _) (spikeScale_nonneg L)
  set Q := ∑ L ∈ s, a L ^ 2 * spikeScale L ^ 2 with hQ
  have hbQ : ∑ L ∈ s, b L ^ 2 = Q := by
    refine Finset.sum_congr rfl fun L _ => ?_
    rw [hb]; simp only; rw [mul_pow, sq_abs]
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun L _ => by positivity
  -- the lag is even, so the sum is twice the sum at `log n`
  have heven : ∑ n ∈ Finset.range N, spikePrimeWeight n * (spikeCombLag s a (Real.log n) +
      spikeCombLag s a (-Real.log n)) =
      2 * ∑ n ∈ Finset.range N, spikePrimeWeight n * spikeCombLag s a (Real.log n) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [spikeCombLag_neg]; ring
  rw [heven]
  -- expand the lag and use the pair bounds
  have hpair : ∑ n ∈ Finset.range N, spikePrimeWeight n * spikeCombLag s a (Real.log n) ≤
      ∑ L ∈ s, ∑ L' ∈ s, |a L| * |a L'| * ∑ n ∈ Finset.range N, spikePrimeWeight n *
        ∫ u, combSpike L u * combSpike L' (u - Real.log n) := by
    calc ∑ n ∈ Finset.range N, spikePrimeWeight n * spikeCombLag s a (Real.log n)
        ≤ ∑ n ∈ Finset.range N, spikePrimeWeight n * ∑ L ∈ s, ∑ L' ∈ s, |a L| * |a L'| *
            ∫ u, combSpike L u * combSpike L' (u - Real.log n) :=
          Finset.sum_le_sum fun n _ =>
            mul_le_mul_of_nonneg_left (spikeCombLag_le s a _) (spikePrimeWeight_nonneg n)
      _ = _ := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun L _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun L' _ => ?_
          refine Finset.sum_congr rfl fun n _ => ?_
          ring
  -- bound each pair
  set T : ℝ → ℝ → ℝ := fun L L' => ∑ n ∈ Finset.range N, spikePrimeWeight n *
    Real.exp (-Real.log n) * (Real.exp (-(κ * |Real.log n - (L - L')|)) +
      Real.exp (-(κ * |Real.log n + (L - L')|))) with hT
  have hpair2 : ∑ L ∈ s, ∑ L' ∈ s, |a L| * |a L'| * ∑ n ∈ Finset.range N, spikePrimeWeight n *
      ∫ u, combSpike L u * combSpike L' (u - Real.log n) ≤
      spikeAmpConst ^ 2 * (1 / π * ∑ L ∈ s, ∑ L' ∈ s, b L * b L' * T L L' +
        2 * ∑ L ∈ s, ∑ L' ∈ s, b L * b L' * (v L * v L')) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun L hL => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun L' hL' => ?_
    have h := sum_prime_combSpike_lag_le hL₀ (hs L hL) (hs L' hL') N
    rw [← hκ] at h
    have hab : 0 ≤ |a L| * |a L'| := by positivity
    calc |a L| * |a L'| * ∑ n ∈ Finset.range N, spikePrimeWeight n *
          ∫ u, combSpike L u * combSpike L' (u - Real.log n)
        ≤ |a L| * |a L'| * (spikeAmpConst ^ 2 * spikeScale L * spikeScale L' *
            (1 / π * T L L' + 2 * ((L + 1) * Real.exp (-(L / 2))) *
              ((L' + 1) * Real.exp (-(L' / 2))))) := mul_le_mul_of_nonneg_left h hab
      _ = _ := by rw [hb, hv]; ring
  -- the same-side double sum
  have hsame : ∑ L ∈ s, ∑ L' ∈ s, b L * b L' * T L L' ≤ 16 * spikeHarmonicConst * Q := by
    have hexpand : ∑ L ∈ s, ∑ L' ∈ s, b L * b L' * T L L' =
        ∑ n ∈ Finset.range N, spikePrimeWeight n * Real.exp (-Real.log n) *
          ∑ L ∈ s, ∑ L' ∈ s, b L * b L' * (Real.exp (-(κ * |Real.log n - (L - L')|)) +
            Real.exp (-(κ * |Real.log n + (L - L')|))) := by
      rw [hT]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm (s := Finset.range N) (t := s)]
      refine Finset.sum_congr rfl fun L _ => ?_
      rw [Finset.sum_comm (s := Finset.range N) (t := s)]
      refine Finset.sum_congr rfl fun L' _ => Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [hexpand]
    have hn : ∀ n ∈ Finset.range N, spikePrimeWeight n * Real.exp (-Real.log n) *
        ∑ L ∈ s, ∑ L' ∈ s, b L * b L' * (Real.exp (-(κ * |Real.log n - (L - L')|)) +
          Real.exp (-(κ * |Real.log n + (L - L')|))) ≤
        spikePrimeWeight n * Real.exp (-Real.log n) * (16 * Q) := by
      intro n _
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (spikePrimeWeight_nonneg n) (Real.exp_pos _).le)
      rw [← hbQ]
      apply double_sum_le_of_row_col_bound (fun L _ L' _ => by positivity)
      · intro L _
        rw [Finset.sum_add_distrib]
        have h1 := hrowG (L - Real.log n)
        have h2 := hrowG (L + Real.log n)
        have e1 : ∑ L' ∈ s, Real.exp (-(κ * |Real.log n - (L - L')|)) =
            ∑ L' ∈ s, Real.exp (-(κ * |L - Real.log n - L'|)) := by
          refine Finset.sum_congr rfl fun L' _ => ?_
          rw [show Real.log n - (L - L') = -(L - Real.log n - L') by ring, abs_neg]
        have e2 : ∑ L' ∈ s, Real.exp (-(κ * |Real.log n + (L - L')|)) =
            ∑ L' ∈ s, Real.exp (-(κ * |L + Real.log n - L'|)) := by
          refine Finset.sum_congr rfl fun L' _ => ?_
          rw [show Real.log n + (L - L') = L + Real.log n - L' by ring]
        rw [e1, e2]; linarith
      · intro L' _
        rw [Finset.sum_add_distrib]
        have h1 := hrowG (L' + Real.log n)
        have h2 := hrowG (L' - Real.log n)
        have e1 : ∑ L ∈ s, Real.exp (-(κ * |Real.log n - (L - L')|)) =
            ∑ L ∈ s, Real.exp (-(κ * |L' + Real.log n - L|)) := by
          refine Finset.sum_congr rfl fun L _ => ?_
          rw [show Real.log n - (L - L') = L' + Real.log n - L by ring]
        have e2 : ∑ L ∈ s, Real.exp (-(κ * |Real.log n + (L - L')|)) =
            ∑ L ∈ s, Real.exp (-(κ * |L' - Real.log n - L|)) := by
          refine Finset.sum_congr rfl fun L _ => ?_
          rw [show Real.log n + (L - L') = -(L' - Real.log n - L) by ring, abs_neg]
        rw [e1, e2]; linarith
    calc ∑ n ∈ Finset.range N, spikePrimeWeight n * Real.exp (-Real.log n) *
          ∑ L ∈ s, ∑ L' ∈ s, b L * b L' * (Real.exp (-(κ * |Real.log n - (L - L')|)) +
            Real.exp (-(κ * |Real.log n + (L - L')|)))
        ≤ ∑ n ∈ Finset.range N, spikePrimeWeight n * Real.exp (-Real.log n) * (16 * Q) :=
          Finset.sum_le_sum hn
      _ = (∑ n ∈ Finset.range N, spikePrimeWeight n * Real.exp (-Real.log n)) * (16 * Q) := by
          rw [Finset.sum_mul]
      _ ≤ spikeHarmonicConst * (16 * Q) :=
          mul_le_mul_of_nonneg_right (sum_harmonic_le N) (by positivity)
      _ = _ := by ring
  -- the opposite-side rank-one form
  have hopp : ∑ L ∈ s, ∑ L' ∈ s, b L * b L' * (v L * v L') ≤ Q := by
    have e : ∑ L ∈ s, ∑ L' ∈ s, b L * b L' * (v L * v L') = (∑ L ∈ s, b L * v L) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun L _ => Finset.sum_congr rfl fun L' _ => ?_
      ring
    rw [e]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s b v
    have hv2 : ∑ L ∈ s, v L ^ 2 ≤ 1 := by
      refine le_trans (le_of_eq ?_) hkraft
      refine Finset.sum_congr rfl fun L _ => ?_
      rw [hv]; simp only
      rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring
    rw [hbQ] at hcs
    calc (∑ L ∈ s, b L * v L) ^ 2 ≤ Q * ∑ L ∈ s, v L ^ 2 := hcs
      _ ≤ Q * 1 := mul_le_mul_of_nonneg_left hv2 hQ0
      _ = Q := mul_one Q
  have hHc := spikeHarmonicConst_nonneg
  calc 2 * ∑ n ∈ Finset.range N, spikePrimeWeight n * spikeCombLag s a (Real.log n)
      ≤ 2 * (spikeAmpConst ^ 2 * (1 / π * ∑ L ∈ s, ∑ L' ∈ s, b L * b L' * T L L' +
          2 * ∑ L ∈ s, ∑ L' ∈ s, b L * b L' * (v L * v L'))) := by
        linarith [hpair.trans hpair2]
    _ ≤ 2 * (spikeAmpConst ^ 2 * (1 / π * (16 * spikeHarmonicConst * Q) + 2 * Q)) := by
        gcongr
    _ = _ := by ring

/-! ## The pole term and the main theorem -/

/-- The pole term of an even real test is nonnegative. -/
theorem re_pole_nonneg_of_even {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (heven : ∀ u, f (-u) = f u) :
    0 ≤ (paperFT (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) (I / 2) +
      paperFT (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) (-I / 2)).re := by
  have hc : Continuous (fun u => (f u : ℂ)) := Complex.continuous_ofReal.comp hf
  have hcc : HasCompactSupport (fun u => (f u : ℂ)) :=
    hfc.comp_left (g := fun y : ℝ => (y : ℂ)) Complex.ofReal_zero
  rw [EF.paperFT_weilTest hc hc hcc hcc, EF.paperFT_weilTest hc hc hcc hcc, conj_I_div_two,
    conj_neg_I_div_two, paperFT_ofRealFun_I_div_two, paperFT_ofRealFun_neg_I_div_two]
  simp only [Complex.conj_ofReal, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  have heq : ∫ u, f u * Real.exp (-u / 2) = ∫ u, f u * Real.exp (u / 2) := by
    rw [← integral_neg_eq_self (fun u => f u * Real.exp (u / 2))]
    congr 1; funext u; rw [heven]
  rw [heq]
  nlinarith [mul_self_nonneg (∫ u, f u * Real.exp (u / 2))]

/-- **Explicit lower bound for a Kraft-sparse comb.** -/
theorem re_W_spikeComb_ge {L₀ : ℝ} (hL₀ : 1 ≤ L₀) {s : Finset ℝ} {a : ℝ → ℝ}
    (hs : ∀ L ∈ s, L₀ ≤ L) (hsep : ∀ L ∈ s, ∀ L' ∈ s, L ≠ L' → 4 * edgeWidth L₀ ≤ |L - L'|)
    (hkraft : ∑ L ∈ s, (L + 1) ^ 2 * Real.exp (-L) ≤ 1) :
    (Real.log (1 + spikeBand L₀ / 4) / 2 - 10 -
        2 * spikeAmpConst ^ 2 * (16 / π * spikeHarmonicConst + 2)) *
        ∑ L ∈ s, a L ^ 2 * spikeScale L ^ 2 ≤
      (zetaZeroConfig.W (fun u => (spikeComb s a u : ℂ)) (fun u => (spikeComb s a u : ℂ))).re := by
  set Fc : ℝ → ℂ := fun u => (spikeComb s a u : ℂ) with hFc
  have hd := contDiff_ofReal_spikeComb s a
  have hsupp := tsupport_ofReal_spikeComb s a
  have hc : HasCompactSupport Fc :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hsupp
  have hdisj : ∀ L ∈ s, ∀ L' ∈ s, L ≠ L' → ∀ u, combSpike L u * combSpike L' u = 0 :=
    fun L hL L' hL' hne u => combSpike_mul_eq_zero (hs L hL) (hs L' hL') (hsep L hL L' hL' hne) u
  rw [zeta_W_eq_weilFullFunctional hd hc]
  unfold weilFullFunctional
  have hkc : HasCompactSupport (EF.weilTest Fc Fc) := EF.weilTest_hasCompactSupport hc hc
  -- the pole term
  have hpole := re_pole_nonneg_of_even (continuous_spikeComb s a) (hasCompactSupport_spikeComb s a)
    (spikeComb_neg s a)
  -- the archimedean term
  have hM := (spikeBand_pos L₀).le
  have harch := re_arch_ge hd hsupp hM
  have e1 : ∫ u, ‖Fc u‖ ^ 2 = ∑ L ∈ s, a L ^ 2 * spikeScale L ^ 2 := by
    rw [← integral_spikeComb_sq (a := a) hdisj]
    congr 1; funext u; rw [hFc]; simp only; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [e1] at harch
  have hℓ0 : 0 ≤ Real.log (1 + spikeBand L₀ / 4) := Real.log_nonneg (by linarith)
  have hcorr := arch_correction_le hL₀ (a := a) hs hkraft hℓ0
  -- the prime term
  obtain ⟨N, hN⟩ := exists_forall_log_eq_zero hkc
  have hterm : ∀ n : ℕ, ((if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0 : ℝ)
      : ℂ) * (EF.weilTest Fc Fc (Real.log n) + EF.weilTest Fc Fc (-Real.log n)) =
      ((spikePrimeWeight n * (spikeCombLag s a (Real.log n) + spikeCombLag s a (-Real.log n)) : ℝ) :
        ℂ) := fun n => by
    rw [hFc, weilTest_ofReal_spikeComb, weilTest_ofReal_spikeComb]; unfold spikePrimeWeight
    push_cast; ring
  have hsum : ∑' n : ℕ, ((if 2 ≤ n then ArithmeticFunction.vonMangoldt n / Real.sqrt n else 0 : ℝ)
      : ℂ) * (EF.weilTest Fc Fc (Real.log n) + EF.weilTest Fc Fc (-Real.log n)) =
      ((∑ n ∈ Finset.range N, spikePrimeWeight n * (spikeCombLag s a (Real.log n) +
        spikeCombLag s a (-Real.log n)) : ℝ) : ℂ) := by
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => ?_)]
    · push_cast
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [hterm]; push_cast; ring
    · rw [Finset.mem_range, not_lt] at hn
      rw [(hN n hn).1, (hN n hn).2, add_zero, mul_zero]
  have hprime := sum_prime_spikeComb_le hL₀ (a := a) hs hsep hkraft N
  rw [hsum]
  rw [Complex.add_re] at hpole
  rw [Complex.add_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re]
  have hQ0 : 0 ≤ ∑ L ∈ s, a L ^ 2 * spikeScale L ^ 2 := Finset.sum_nonneg fun L _ => by positivity
  nlinarith

theorem tendsto_log_one_add_spikeBand :
    Tendsto (fun L₀ => Real.log (1 + spikeBand L₀ / 4)) atTop atTop := by
  have h1 : Tendsto (fun L₀ : ℝ => spikeBand L₀ / 4) atTop atTop := by
    unfold spikeBand
    have hc : 0 < π ^ 3 / (8 * spikeAmpConst ^ 2) / 4 := by
      have := spikeAmpConst_pos; positivity
    have := Real.tendsto_exp_atTop.const_mul_atTop hc
    refine this.congr fun L₀ => ?_
    ring
  exact Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ 1 h1)

/-- **Kraft-sparse spike combs of Riemann's kernel are Weil-positive.** For all large `L₀`, every
nonzero comb `Σ a_L P_L` with levels `≥ L₀`, pairwise `4/Y(L₀)` apart and
`Σ (L + 1)² e^{−L} ≤ 1` has `Re W(F, F) > 0`. -/
theorem eventually_re_W_spikeComb_pos :
    ∀ᶠ L₀ : ℝ in atTop, ∀ (s : Finset ℝ) (a : ℝ → ℝ), (∀ L ∈ s, L₀ ≤ L) →
      (∀ L ∈ s, ∀ L' ∈ s, L ≠ L' → 4 * edgeWidth L₀ ≤ |L - L'|) →
      ∑ L ∈ s, (L + 1) ^ 2 * Real.exp (-L) ≤ 1 → (∃ L ∈ s, a L ≠ 0) →
      0 < (zetaZeroConfig.W (fun u => (spikeComb s a u : ℂ)) (fun u => (spikeComb s a u : ℂ))).re := by
  have hbig := tendsto_log_one_add_spikeBand.eventually_gt_atTop
    (2 * (10 + 2 * spikeAmpConst ^ 2 * (16 / π * spikeHarmonicConst + 2)))
  filter_upwards [hbig, eventually_ge_atTop (1 : ℝ)] with L₀ hℓ hL₀ s a hs hsep hkraft hne
  have hlow := re_W_spikeComb_ge hL₀ (a := a) hs hsep hkraft
  obtain ⟨L, hL, haL⟩ := hne
  have hQ : 0 < ∑ L ∈ s, a L ^ 2 * spikeScale L ^ 2 := by
    have hpos : 0 < a L ^ 2 * spikeScale L ^ 2 :=
      mul_pos (by positivity) (by have := spikeScale_pos (hL₀.trans (hs L hL)); positivity)
    exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun L => a L ^ 2 * spikeScale L ^ 2)
      (fun L _ => by positivity) hL)
  have hcoef : 0 < Real.log (1 + spikeBand L₀ / 4) / 2 - 10 -
      2 * spikeAmpConst ^ 2 * (16 / π * spikeHarmonicConst + 2) := by linarith
  exact lt_of_lt_of_le (mul_pos hcoef hQ) hlow

end

end RHTower
