import GaloisForLFunctions.RHTower.WeilAlmostPeriodicLockRH
import GaloisForLFunctions.RHTower.LocalRectangleArgumentBound
import GaloisForLFunctions.HTGeometry.ZetaTailBound
import GaloisForLFunctions.RHTower.WeilLockMeanMotionRigidity

/-!
# Almost-periodic locks force the true producer

**Theorem** (`almostPeriodicLock_trueProducer`). Let `G` be a Herglotz producer for the weights
`lam` with lower-line lock `G(1 − s) = V(s) G(s)`, `V(s) = Σ_j c_j u_j^{−(s−½)}`, where
`Σ_j |c_j| max(1, u_j^{−1}) K(u_j) < ∞` (the weight of `almostPeriodicLock_riemannHypothesis`) and
`Σ_j |c_j| |log u_j| < ∞`. Then `lam(n) = Λ(n)` for all `n ≥ 2`, and the Riemann hypothesis holds.

So a Herglotz producer with a weighted almost-periodic lock is the true producer.

**Proof.** Write `v(y) = V(½ − iy)` for the lock on the lower line and `g = Im(v' v̄)` for its
phase velocity.
* The limit-periodic expansion of the coefficients gives `G = s(s − 1)Γ_ℝ ζ A` on `Re s > ½`, with
  `A` continuous and bounded on `Re s ≥ ½` (`limitPeriodic_producer_factor`), and
  `A = exp(Σ lam(n) n^{−s}/log n)/ζ` on `Re s > 1`. Hence `Re A ≥ ½` on a half-plane
  `Re s ≥ σ₀` (`exists_re_ge_half_of_zetaOf_eq`).
* Dividing the lock by `s(s − 1)Γ_ℝ ζ`, which is symmetric under `s ↦ 1 − s`, gives
  `A(½ + iy) = V(½ − iy) A(½ − iy)` for `y > 0` (`lineFactor_lock`).
* So `E = A` on `Re z ≥ ½` and `E = V(1 − z) A(1 − z)` on `Re z < ½` is holomorphic on
  `Re z > −½`, `Im z > 0` (`differentiableOn_lockGlue`).
* Fix `ε` with `|V(½ + ε − iy) − v(y)| ≤ ½`. Then the argument principle for `E` on
  `[½ − ε, σ₀] × [Y₀, Y]` and for `A` on `[½ + ε, σ₀] × [−Y, −Y₀]` bounds the phase advance of
  `V(½ + ε − iy)` from above. The enclosed zeros of `E` only lower it. The horizontal edges are
  bounded by Backlund–Jensen, and the edges at `σ₀` by `π`.
* Comparing with `v` gives `∫_{Y₀}^{Y} g ≤ C` at heights `Y → ∞`. The positivity law gives
  `g ≥ 0`, and `g` is almost periodic. So `g` has mean `0`, hence `g ≡ 0`, the lock is constant,
  and phase-lock rigidity applies.
-/

open Complex Filter Topology Set MeasureTheory Metric
open scoped ComplexConjugate

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity
  HamburgerTwisted WeilSpectral CharacterZeroPlanting

noncomputable section

/-! ## The anchor -/

/-- `‖Σ lam(n) n^{−s}/log n‖ ≤ 4·2^{−σ} Σ 2|lam(n)|/n²` on `Re s = σ ≥ 2`. -/
theorem norm_LSeries_lamLog_le_rpow {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {s : ℂ}
    (hs : 2 ≤ s.re) :
    ‖LSeries (lamLog lam) s‖ ≤
      4 * (2 : ℝ) ^ (-s.re) * ∑' n : ℕ, 2 * |lam n| / (n : ℝ) ^ (2 : ℝ) := by
  have hCs : Summable fun n : ℕ => 2 * |lam n| / (n : ℝ) ^ (2 : ℝ) := by
    refine ((hsl 2 (by norm_num)).mul_left 2).congr fun n => ?_
    ring
  have hterm : ∀ n : ℕ, ‖LSeries.term (lamLog lam) s n‖ ≤
      4 * (2 : ℝ) ^ (-s.re) * (2 * |lam n| / (n : ℝ) ^ (2 : ℝ)) := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with hn
    · positivity
    · by_cases h2 : 2 ≤ n
      · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h2
        have hl := norm_lamLog_le lam n
        have hpow : (n : ℝ) ^ s.re = (n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ (s.re - 2) := by
          rw [← Real.rpow_add hnpos]; ring_nf
        have hge : (2 : ℝ) ^ (s.re - 2) ≤ (n : ℝ) ^ (s.re - 2) :=
          Real.rpow_le_rpow (by norm_num) hn2 (by linarith)
        have h2pos : (0 : ℝ) < (2 : ℝ) ^ (s.re - 2) := by positivity
        have hinv : (4 : ℝ) * (2 : ℝ) ^ (-s.re) = ((2 : ℝ) ^ (s.re - 2))⁻¹ := by
          rw [Real.rpow_sub (by norm_num), Real.rpow_neg (by norm_num)]; norm_num; ring
        rw [hinv, hpow]
        have hn2pos : (0 : ℝ) < (n : ℝ) ^ (2 : ℝ) := by positivity
        calc ‖lamLog lam n‖ / ((n : ℝ) ^ (2 : ℝ) * (n : ℝ) ^ (s.re - 2))
            ≤ 2 * |lam n| / ((n : ℝ) ^ (2 : ℝ) * (2 : ℝ) ^ (s.re - 2)) := by
              gcongr
          _ = ((2 : ℝ) ^ (s.re - 2))⁻¹ * (2 * |lam n| / (n : ℝ) ^ (2 : ℝ)) := by
              field_simp
      · have h0 : lamLog lam n = 0 := by simp [lamLog, h2]
        rw [h0, norm_zero, zero_div]; positivity
  have hsumm : Summable fun n => ‖LSeries.term (lamLog lam) s n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hCs.mul_left _)
  calc ‖LSeries (lamLog lam) s‖ ≤ ∑' n, ‖LSeries.term (lamLog lam) s n‖ :=
        norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' n : ℕ, 4 * (2 : ℝ) ^ (-s.re) * (2 * |lam n| / (n : ℝ) ^ (2 : ℝ)) :=
        hsumm.tsum_le_tsum hterm (hCs.mul_left _)
    _ = _ := tsum_mul_left

/-- **The anchor.** If `exp(Σ lam(n) n^{−s}/log n) = ζ(s) A(s)` on `Re s > 1`, then `Re A ≥ ½` on
a right half-plane. -/
theorem exists_re_ge_half_of_zetaOf_eq {lam : ℕ → ℝ} {A : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hA : ∀ s : ℂ, 1 < s.re → zetaOf lam s = riemannZeta s * A s) :
    ∃ σ₀ : ℝ, 2 ≤ σ₀ ∧ ∀ s : ℂ, σ₀ ≤ s.re → 1 / 2 ≤ (A s).re := by
  set C : ℝ := ∑' n : ℕ, 2 * |lam n| / (n : ℝ) ^ (2 : ℝ) with hC
  have hC0 : 0 ≤ C := tsum_nonneg fun n => by positivity
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (32 * (C + 1)) (by norm_num : (1 : ℝ) < 2)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  refine ⟨2 + K, by linarith, fun s hs => ?_⟩
  have hs2 : (2 : ℝ) ≤ s.re := by linarith
  have hs1 : 1 < s.re := by linarith
  have h2σ : (2 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-(2 + (K : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have h2K : (2 : ℝ) ^ (-(2 + (K : ℝ))) = 1 / 4 * ((2 : ℝ) ^ K)⁻¹ := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_add (by norm_num), Real.rpow_natCast]; norm_num
    ring
  have hpowK : (0 : ℝ) < 2 ^ K := by positivity
  have hsmall : 4 * (2 : ℝ) ^ (-s.re) * (C + 1) ≤ 1 / 32 := by
    have h1 : 4 * (2 : ℝ) ^ (-s.re) ≤ ((2 : ℝ) ^ K)⁻¹ := by
      have := mul_le_mul_of_nonneg_left (h2σ.trans h2K.le) (by norm_num : (0 : ℝ) ≤ 4)
      linarith
    calc 4 * (2 : ℝ) ^ (-s.re) * (C + 1) ≤ ((2 : ℝ) ^ K)⁻¹ * (C + 1) :=
          mul_le_mul_of_nonneg_right h1 (by linarith)
      _ ≤ 1 / 32 := by
          rw [inv_mul_le_iff₀ hpowK]; linarith
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-s.re) := by positivity
  have hL : ‖LSeries (lamLog lam) s‖ ≤ 1 / 32 := by
    refine (norm_LSeries_lamLog_le_rpow hsl hs2).trans ?_
    rw [← hC]; nlinarith
  have hζ : ‖riemannZeta s - 1‖ ≤ 1 / 32 := by
    refine (norm_riemannZeta_sub_one_le_rpow hs2).trans ?_
    nlinarith
  have hE : ‖zetaOf lam s - 1‖ ≤ 1 / 16 := by
    unfold zetaOf
    refine (Complex.norm_exp_sub_one_le (hL.trans (by norm_num))).trans ?_
    linarith
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hζn : (31 / 32 : ℝ) ≤ ‖riemannZeta s‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - riemannZeta s)
    rw [norm_one, sub_sub_cancel, norm_sub_rev] at this
    linarith
  have hAeq : A s - 1 = (zetaOf lam s - riemannZeta s) / riemannZeta s := by
    rw [hA s hs1]; field_simp
  have hA1 : ‖A s - 1‖ ≤ 3 / 31 := by
    rw [hAeq, norm_div]
    have hnum : ‖zetaOf lam s - riemannZeta s‖ ≤ 3 / 32 := by
      calc ‖zetaOf lam s - riemannZeta s‖ = ‖(zetaOf lam s - 1) - (riemannZeta s - 1)‖ := by
            ring_nf
        _ ≤ ‖zetaOf lam s - 1‖ + ‖riemannZeta s - 1‖ := norm_sub_le _ _
        _ ≤ 3 / 32 := by linarith
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hre := Complex.abs_re_le_norm (A s - 1)
  rw [Complex.sub_re, Complex.one_re] at hre
  have := (abs_le.mp (hre.trans hA1)).1
  linarith

/-! ## The factor on the line and the lock for `A` -/

/-- `s(s − 1)Γ_ℝ(s)ζ(s) = s(s − 1)Λ(s)` is symmetric under `s ↦ 1 − s` on the critical line. -/
theorem lineZeta_one_sub {s : ℂ} (hs : s.re = 1 / 2) :
    (1 - s) * (1 - s - 1) * Gammaℝ (1 - s) * riemannZeta (1 - s) =
      s * (s - 1) * Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs
  have hs0' : 1 - s ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hs]; norm_num)
  have hΓ' : Gammaℝ (1 - s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  rw [riemannZeta_def_of_ne_zero hs0, riemannZeta_def_of_ne_zero hs0',
    completedRiemannZeta_one_sub]
  field_simp
  ring

/-- **The factor extends to the line.** If `G = s(s − 1)Γ_ℝ ζ A` on `Re s > ½`, `s ≠ 1`, with `G`
continuous on `Re s ≥ ½` and `A` continuous there, the identity also holds on the line. -/
theorem eq_lineFactor_of_re_eq_half {G A : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGK : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
      G s = s * (s - 1) * Gammaℝ s * (riemannZeta s * A s))
    (hAc : ContinuousOn A {s : ℂ | 1 / 2 ≤ s.re}) {s : ℂ} (hs : s.re = 1 / 2) :
    G s = s * (s - 1) * Gammaℝ s * (riemannZeta s * A s) := by
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  set K : ℂ → ℂ := fun z => z * (z - 1) * Gammaℝ z * (riemannZeta z * A z) with hK
  have hpath : Tendsto (fun ε : ℝ => s + ε) (𝓝[>] 0) (𝓝 s) := by
    have : Tendsto (fun ε : ℝ => s + ε) (𝓝 0) (𝓝 (s + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto 0
    rw [Complex.ofReal_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hpathS : Tendsto (fun ε : ℝ => s + ε) (𝓝[>] 0) (𝓝[{z : ℂ | 1 / 2 ≤ z.re}] s) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpath, by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      show 1 / 2 ≤ (s + ε).re
      simp; linarith⟩
  have hKc : ContinuousWithinAt K {z : ℂ | 1 / 2 ≤ z.re} s := by
    have hpre : ContinuousAt (fun z : ℂ => z * (z - 1) * Gammaℝ z * riemannZeta z) s :=
      (((continuous_id.mul (continuous_id.sub continuous_const)).continuousAt).mul
        (differentiableAt_Gammaℝ_of_re_pos (by rw [hs]; norm_num)).continuousAt).mul
        (differentiableAt_riemannZeta hs1).continuousAt
    have hKeq : K = fun z => (z * (z - 1) * Gammaℝ z * riemannZeta z) * A z := by
      funext z; simp only [hK]; ring
    rw [hKeq]
    exact hpre.continuousWithinAt.mul (hAc s (by show 1 / 2 ≤ s.re; rw [hs]))
  have hG := (hGc s (by rw [hs])).tendsto.comp hpath
  have hK' := hKc.tendsto.comp hpathS
  refine tendsto_nhds_unique hG (hK'.congr' ?_)
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε
  simp only [Function.comp_apply, hK]
  refine (hGK _ (by simp only [Complex.add_re, Complex.ofReal_re]; linarith [hε.1])
    fun h => ?_).symm
  have := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.one_re] at this
  linarith [hε.2]

/-- `ζ` has isolated zeros away from the pole. -/
theorem riemannZeta_eventually_ne_zero {s : ℂ} (hs : s ≠ 1) :
    ∀ᶠ z in 𝓝[≠] s, riemannZeta z ≠ 0 := by
  have hU : AnalyticOnNhd ℂ riemannZeta {1}ᶜ :=
    (DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
      isOpen_compl_singleton)
  rcases (hU s hs).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have hconn := (isConnected_compl_singleton_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num) (1 : ℂ)).isPreconnected
    have h2 := hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hs h
      (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
    exact riemannZeta_ne_zero_of_one_lt_re (by norm_num : (1 : ℝ) < (2 : ℂ).re) h2
  · exact h

/-- **The lock for `A`.** If `G = s(s − 1)Γ_ℝ ζ A` on `Re s > ½` and
`G(1 − s) = V(s) G(s)` on the lower line, then `A(½ + iy) = V(½ − iy) A(½ − iy)` for `y > 0`. -/
theorem lineFactor_lock {G A V : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGK : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
      G s = s * (s - 1) * Gammaℝ s * (riemannZeta s * A s))
    (hAc : ContinuousOn A {s : ℂ | 1 / 2 ≤ s.re}) (hVc : Continuous V)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = V (lineS τ) * G (lineS τ)) {y : ℝ}
    (hy : 0 < y) : A (1 / 2 + y * I) = V (1 / 2 - y * I) * A (1 / 2 - y * I) := by
  -- the identity where `ζ(½ − iy) ≠ 0`
  have hpt : ∀ t : ℝ, 0 < t → riemannZeta (1 / 2 - t * I) ≠ 0 →
      A (1 / 2 + t * I) = V (1 / 2 - t * I) * A (1 / 2 - t * I) := by
    intro t ht hz
    set s : ℂ := 1 / 2 - t * I with hsdef
    have hsre : s.re = 1 / 2 := by simp [hsdef]
    have h1s : 1 - s = 1 / 2 + t * I := by rw [hsdef]; ring
    have h1sre : (1 - s).re = 1 / 2 := by rw [h1s]; simp
    have hl : lineS (-(t / 2)) = s := by
      rw [lineS_eq, hsdef]; push_cast; ring
    have hlk := hlock (-(t / 2)) (by linarith)
    rw [hl, eq_lineFactor_of_re_eq_half hGc hGK hAc h1sre,
      eq_lineFactor_of_re_eq_half hGc hGK hAc hsre] at hlk
    have hsym := lineZeta_one_sub hsre
    have hs0 : s ≠ 0 := fun h => by rw [h] at hsre; simp at hsre
    have hs1 : s - 1 ≠ 0 := fun h => by
      have := congrArg Complex.re h; simp [hsre] at this; norm_num at this
    have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; norm_num)
    have hZ : s * (s - 1) * Gammaℝ s * riemannZeta s ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero hs0 hs1) hΓ) hz
    rw [← h1s]
    apply mul_left_cancel₀ hZ
    linear_combination hlk - A (1 - s) * hsym
  -- continuity and density
  by_contra hne
  set D : ℝ → ℂ := fun t => A (1 / 2 + t * I) - V (1 / 2 - t * I) * A (1 / 2 - t * I) with hD
  have hDc : ContinuousAt D y := by
    have hA1 : ContinuousAt (fun t : ℝ => A (1 / 2 + t * I)) y := by
      have hmem : ∀ t : ℝ, (1 / 2 + (t : ℂ) * I) ∈ {s : ℂ | 1 / 2 ≤ s.re} := fun t => by simp
      exact (hAc.comp_continuous (by fun_prop) hmem).continuousAt
    have hA2 : ContinuousAt (fun t : ℝ => A (1 / 2 - t * I)) y := by
      have hmem : ∀ t : ℝ, (1 / 2 - (t : ℂ) * I) ∈ {s : ℂ | 1 / 2 ≤ s.re} := fun t => by simp
      exact (hAc.comp_continuous (by fun_prop) hmem).continuousAt
    exact hA1.sub ((hVc.comp (by fun_prop : Continuous fun t : ℝ => (1 / 2 : ℂ) - t * I)
      ).continuousAt.mul hA2)
  have hDy : D y ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  have hev : ∀ᶠ t in 𝓝 y, D t ≠ 0 := hDc.eventually_ne hDy
  have hs0 : (1 / 2 - (y : ℂ) * I) ≠ 1 := fun h => by
    have := congrArg Complex.re h; simp at this
  have hζev := riemannZeta_eventually_ne_zero hs0
  have hmap : Tendsto (fun t : ℝ => (1 / 2 : ℂ) - t * I) (𝓝[≠] y) (𝓝[≠] (1 / 2 - y * I)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((by fun_prop : Continuous fun t : ℝ => (1 / 2 : ℂ) - t * I).tendsto y).mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ y)
      intro h
      apply ht
      have := congrArg Complex.im h
      simpa using this
  have hζt := hmap.eventually hζev
  have hpos : ∀ᶠ t in 𝓝[≠] y, 0 < t :=
    (eventually_gt_nhds hy).filter_mono nhdsWithin_le_nhds
  obtain ⟨t, ht1, ht2, ht3⟩ :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (hζt.and hpos)).exists
  exact ht1 (sub_eq_zero.mpr (hpt t ht3 ht2))

/-! ## Gluing `A` across the line -/

/-- The glued function: `A` on `Re z ≥ ½`, and `V(1 − z) A(1 − z)` on `Re z < ½`. -/
def lockGlue (A V : ℂ → ℂ) (z : ℂ) : ℂ := if 1 / 2 ≤ z.re then A z else V (1 - z) * A (1 - z)

/-- The upper domain `Re z > −½`, `Im z > 0`. -/
def glueDomain : Set ℂ := {z : ℂ | -(1 / 2) < z.re ∧ 0 < z.im}

theorem isOpen_glueDomain : IsOpen glueDomain :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_const Complex.continuous_im)

theorem isConnected_glueDomain : IsConnected glueDomain := by
  refine ⟨⟨I, by simp [glueDomain]⟩, (Convex.inter ?_ ?_).isPreconnected⟩
  · exact convex_halfSpace_re_gt _
  · exact convex_halfSpace_im_gt _

theorem lockGlue_of_le {A V : ℂ → ℂ} {z : ℂ} (hz : 1 / 2 ≤ z.re) : lockGlue A V z = A z := by
  rw [lockGlue, if_pos hz]

theorem lockGlue_of_lt {A V : ℂ → ℂ} {z : ℂ} (hz : z.re < 1 / 2) :
    lockGlue A V z = V (1 - z) * A (1 - z) := by
  rw [lockGlue, if_neg (not_le.mpr hz)]

theorem norm_lockGlue_le {A V : ℂ → ℂ} {WA CV : ℝ}
    (hAb : ∀ s : ℂ, 1 / 2 ≤ s.re → ‖A s‖ ≤ WA) (hVb : ∀ s, ‖V s‖ ≤ CV) (z : ℂ) :
    ‖lockGlue A V z‖ ≤ max 1 CV * WA := by
  have hWA : 0 ≤ WA := (norm_nonneg _).trans (hAb 1 (by norm_num))
  rcases le_or_gt (1 / 2) z.re with hz | hz
  · rw [lockGlue_of_le hz]
    exact (hAb z hz).trans (le_mul_of_one_le_left hWA (le_max_left _ _))
  · rw [lockGlue_of_lt hz, norm_mul]
    exact mul_le_mul ((hVb _).trans (le_max_right _ _)) (hAb _ (by simp; linarith))
      (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _))

/-- **The glued function is holomorphic** on `Re z > −½`, `Im z > 0`. -/
theorem differentiableOn_lockGlue {A : ℂ → ℂ} {c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹)
    (hAd : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hAc : ContinuousOn A {s : ℂ | 1 / 2 ≤ s.re})
    (hlockA : ∀ y : ℝ, 0 < y → A (1 / 2 + y * I) = apLock c u (1 / 2 - y * I) * A (1 / 2 - y * I)) :
    DifferentiableOn ℂ (lockGlue A (apLock c u)) glueDomain := by
  set V := apLock c u with hV
  have hVc : Continuous V := continuous_apLock hu hc
  have hgc : ContinuousOn (fun z => V (1 - z) * A (1 - z)) {z : ℂ | z.re ≤ 1 / 2} := by
    refine (hVc.comp (continuous_const.sub continuous_id)).continuousOn.mul ?_
    refine hAc.comp (continuous_const.sub continuous_id).continuousOn fun z hz => ?_
    show 1 / 2 ≤ (1 - z).re
    simp only [Complex.sub_re, Complex.one_re]
    have : z.re ≤ 1 / 2 := hz
    linarith
  have hcont : ContinuousOn (lockGlue A V) glueDomain := by
    refine ContinuousOn.if (p := fun z : ℂ => 1 / 2 ≤ z.re) ?_ ?_ ?_
    · intro z hz
      have hzre : z.re = 1 / 2 :=
        (frontier_le_subset_eq continuous_const Complex.continuous_re hz.2).symm
      have hzim : 0 < z.im := hz.1.2
      have hz' : z = 1 / 2 + (z.im : ℂ) * I := by
        apply Complex.ext <;> simp [hzre]
      have h1 : 1 - z = 1 / 2 - (z.im : ℂ) * I := by
        apply Complex.ext <;> simp [hzre]; norm_num
      have hl := hlockA z.im hzim
      rw [← hz'] at hl
      rw [h1]
      exact hl
    · refine hAc.mono fun z hz => ?_
      have := (isClosed_le continuous_const Complex.continuous_re).closure_subset hz.2
      exact this
    · refine hgc.mono fun z hz => ?_
      have hsub : closure {z : ℂ | ¬ 1 / 2 ≤ z.re} ⊆ {z : ℂ | z.re ≤ 1 / 2} := by
        have h := closure_lt_subset_le (f := Complex.re) (g := fun _ : ℂ => (1 / 2 : ℝ))
          Complex.continuous_re continuous_const
        simpa only [not_le] using h
      exact hsub hz.2
  refine differentiableOn_of_off_vertical_line (a := 1 / 2) isOpen_glueDomain hcont ?_
  intro z hz
  have hz0 := hz.1
  rcases lt_or_gt_of_ne hz.2 with hlt | hgt
  · -- left of the line
    have hopen : IsOpen {w : ℂ | w.re < 1 / 2} := isOpen_lt Complex.continuous_re continuous_const
    have hev : lockGlue A V =ᶠ[𝓝 z] fun w => V (1 - w) * A (1 - w) := by
      filter_upwards [hopen.mem_nhds hlt] with w hw
      exact lockGlue_of_lt hw
    have h1z : 1 / 2 < (1 - z).re := by simp; linarith
    have h1z' : (1 - z).re < 3 / 2 := by have := hz0.1; simp; linarith
    have hVd : DifferentiableAt ℂ V (1 - z) := differentiableAt_apLock hu hc h1z h1z'
    have hAd' : DifferentiableAt ℂ A (1 - z) :=
      (hAd (1 - z) h1z).differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds h1z)
    have hsub : DifferentiableAt ℂ (fun w : ℂ => 1 - w) z := by fun_prop
    have hd : DifferentiableAt ℂ (fun w => V (1 - w) * A (1 - w)) z :=
      (hVd.comp z hsub).mul (hAd'.comp z hsub)
    exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
  · -- right of the line
    have hopen : IsOpen {w : ℂ | 1 / 2 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : lockGlue A V =ᶠ[𝓝 z] A := by
      filter_upwards [hopen.mem_nhds hgt] with w hw
      exact lockGlue_of_le hw.le
    exact (((hAd z hgt).differentiableAt (hopen.mem_nhds hgt)).congr_of_eventuallyEq
      hev).differentiableWithinAt

/-- On the right of the line, `E'/E = A'/A`. -/
theorem logDeriv_lockGlue_right {A V : ℂ → ℂ} {z : ℂ} (hz : 1 / 2 < z.re) :
    logDeriv (lockGlue A V) z = logDeriv A z := by
  have hev : lockGlue A V =ᶠ[𝓝 z] A := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with w hw
    exact lockGlue_of_le (le_of_lt hw)
  rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]

/-- On the left of the line, `E'/E(z) = −(V'/V + A'/A)(1 − z)`. -/
theorem logDeriv_lockGlue_left {A V : ℂ → ℂ} {z : ℂ} (hz : z.re < 1 / 2)
    (hVd : DifferentiableAt ℂ V (1 - z)) (hAd : DifferentiableAt ℂ A (1 - z))
    (hV0 : V (1 - z) ≠ 0) (hA0 : A (1 - z) ≠ 0) :
    logDeriv (lockGlue A V) z = -(logDeriv V (1 - z) + logDeriv A (1 - z)) := by
  have hev : lockGlue A V =ᶠ[𝓝 z] fun w => V (1 - w) * A (1 - w) := by
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hz] with w hw
    exact lockGlue_of_lt hw
  have hsub : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
  have hV' := hVd.hasDerivAt.comp z hsub
  have hA' := hAd.hasDerivAt.comp z hsub
  have hprod : HasDerivAt (fun w => V (1 - w) * A (1 - w))
      (deriv V (1 - z) * (-1) * A (1 - z) + V (1 - z) * (deriv A (1 - z) * (-1))) z :=
    hV'.mul hA'
  rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds, hprod.deriv, logDeriv_apply, logDeriv_apply]
  field_simp
  ring

/-! ## The shifted lock -/

/-- **A small shift moves the lock little.** There is `ε ∈ (0, ¼]` with
`|V(½ + ε − iy) − V(½ − iy)| ≤ ½` for every real `y`. -/
theorem exists_shift_apLock_close {c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ ∀ y : ℝ,
      ‖apLock c u (((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) -
        apLock c u (1 / 2 - (y : ℂ) * I)‖ ≤ 1 / 2 := by
  have hcn : Summable fun j => ‖c j‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => le_mul_of_one_le_right (norm_nonneg _) (le_max_left _ _)) hc
  have hbound : Summable fun j => ‖c j‖ * (max 1 (u j)⁻¹ + 1) :=
    (hc.add hcn).congr fun j => by ring
  set δ : ℝ → ℝ := fun ε => ∑' j, ‖c j‖ * |u j ^ (-ε) - 1| with hδ
  have hlim : Tendsto δ (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
      (f := fun ε j => ‖c j‖ * |u j ^ (-ε) - 1|) (g := fun _ => (0 : ℝ)) hbound
      (fun j => by
        have hc0 : Tendsto (fun ε : ℝ => u j ^ (-ε)) (𝓝 0) (𝓝 1) := by
          have := ((Real.continuousAt_const_rpow (b := -(0 : ℝ)) (hu j).ne').comp
            continuousAt_neg).tendsto
          simpa [Function.comp_def] using this
        have ht := ((continuous_abs.tendsto ((1 : ℝ) - 1)).comp (hc0.sub_const 1)).const_mul ‖c j‖
        simpa [Function.comp_def] using ht.mono_left nhdsWithin_le_nhds)
      (by
        filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with ε hε j
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h1 := rpow_neg_le_max (hu j) hε.1.le hε.2.le
        have h2 : 0 ≤ u j ^ (-ε) := Real.rpow_nonneg (hu j).le _
        rw [abs_le]; constructor <;> linarith)
    simpa using h
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), δ ε < 1 / 2 ∧ ε ∈ Ioo (0 : ℝ) (1 / 4) :=
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).and
      (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨ε, hδε, hεI⟩ := hev.exists
  refine ⟨ε, hεI.1, hεI.2.le, fun y => ?_⟩
  set w : ℂ := ((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I with hw
  have hwre : w.re = 1 / 2 + ε := by simp [hw]
  rw [apLock_of_mem c u (by rw [hwre]; linarith [hεI.1]) (by rw [hwre]; linarith [hεI.2]),
    apLock_of_mem c u (by simp) (by simp; norm_num)]
  have hterm1 : ∀ j, ‖c j * (u j : ℂ) ^ (-(w - 1 / 2))‖ ≤ ‖c j‖ * max 1 (u j)⁻¹ := by
    intro j
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cpow_neg_le_max (hu j) (by simp [hwre]; linarith [hεI.1])
      (by simp [hwre]; linarith [hεI.2])) (norm_nonneg _)
  have hterm2 : ∀ j, ‖c j * (u j : ℂ) ^ (-(1 / 2 - (y : ℂ) * I - 1 / 2))‖ ≤
      ‖c j‖ * max 1 (u j)⁻¹ := by
    intro j
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (norm_cpow_neg_le_max (hu j) (by simp) (by simp))
      (norm_nonneg _)
  have hs1 : Summable fun j => c j * (u j : ℂ) ^ (-(w - 1 / 2)) :=
    Summable.of_norm_bounded hc hterm1
  have hs2 : Summable fun j => c j * (u j : ℂ) ^ (-(1 / 2 - (y : ℂ) * I - 1 / 2)) :=
    Summable.of_norm_bounded hc hterm2
  have hdiff : ∀ j, ‖c j * (u j : ℂ) ^ (-(w - 1 / 2)) -
      c j * (u j : ℂ) ^ (-(1 / 2 - (y : ℂ) * I - 1 / 2))‖ = ‖c j‖ * |u j ^ (-ε) - 1| := by
    intro j
    have hu0 : (u j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hu j).ne'
    have e1 : -(w - 1 / 2) = ((-ε : ℝ) : ℂ) + (y : ℂ) * I := by rw [hw]; push_cast; ring
    have e2 : -(1 / 2 - (y : ℂ) * I - 1 / 2) = (y : ℂ) * I := by ring
    rw [e1, e2, Complex.cpow_add _ _ hu0, ← Complex.ofReal_cpow (hu j).le,
      show c j * (((u j ^ (-ε) : ℝ) : ℂ) * (u j : ℂ) ^ ((y : ℂ) * I)) -
        c j * (u j : ℂ) ^ ((y : ℂ) * I) =
        c j * (u j : ℂ) ^ ((y : ℂ) * I) * (((u j ^ (-ε) - 1 : ℝ)) : ℂ) by push_cast; ring,
      norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hu j), Complex.norm_real,
      Real.norm_eq_abs]
    simp
  have hsd : Summable fun j => ‖c j‖ * |u j ^ (-ε) - 1| := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) (hc.add hc)
    rw [← hdiff j]
    exact (norm_sub_le _ _).trans (add_le_add (hterm1 j) (hterm2 j))
  rw [← hs1.tsum_sub hs2]
  calc ‖∑' j, (c j * (u j : ℂ) ^ (-(w - 1 / 2)) -
          c j * (u j : ℂ) ^ (-(1 / 2 - (y : ℂ) * I - 1 / 2)))‖
      ≤ ∑' j, ‖c j * (u j : ℂ) ^ (-(w - 1 / 2)) -
          c j * (u j : ℂ) ^ (-(1 / 2 - (y : ℂ) * I - 1 / 2))‖ :=
        norm_tsum_le_tsum_norm (hsd.congr fun j => (hdiff j).symm)
    _ = δ ε := tsum_congr hdiff
    _ ≤ 1 / 2 := hδε.le

/-! ## Edge estimates -/

/-- **A vertical edge where `Re f > 0`.** The phase advance of `f` along `σ + it`,
`t ∈ [T₁, T₂]`, is at most `2π` in absolute value. -/
theorem abs_integral_re_logDeriv_vertical_le {f : ℂ → ℂ} {σ T₁ T₂ : ℝ} (hT : T₁ ≤ T₂)
    (hf : ∀ t ∈ Icc T₁ T₂, AnalyticAt ℂ f ((σ : ℂ) + t * I))
    (hre : ∀ t ∈ Icc T₁ T₂, 0 < (f ((σ : ℂ) + t * I)).re) :
    |∫ t in T₁..T₂, (logDeriv f ((σ : ℂ) + t * I)).re| ≤ 2 * Real.pi := by
  set p : ℝ → ℂ := fun t => (σ : ℂ) + t * I with hp
  have hpd : ∀ t : ℝ, HasDerivAt p I t := by
    intro t
    have := ((hasDerivAt_id t).ofReal_comp.mul_const I).const_add (σ : ℂ)
    simpa [hp] using this
  have hne : ∀ t ∈ Icc T₁ T₂, f (p t) ≠ 0 := fun t ht h => by
    have := hre t ht; rw [h] at this; simp at this
  have hL : ∀ t ∈ uIcc T₁ T₂, HasDerivAt (fun t : ℝ => Complex.log (f (p t)))
      (logDeriv f (p t) * I) t := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    have h1 : HasDerivAt (f ∘ p) (deriv f (p t) * I) t :=
      (hf t ht).differentiableAt.hasDerivAt.comp t (hpd t)
    have h2 : HasDerivAt (fun t : ℝ => Complex.log (f (p t))) (deriv f (p t) * I / f (p t)) t :=
      h1.clog_real (Complex.mem_slitPlane_iff.mpr (Or.inl (hre t ht)))
    rw [logDeriv_apply]
    convert h2 using 1
    ring
  have hcont : ContinuousOn (fun t => logDeriv f (p t) * I) (uIcc T₁ T₂) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact (((analyticAt_logDeriv_of_ne_zero (hf t ht) (hne t ht)).continuousAt.comp
      (f := p) (hpd t).continuousAt).mul continuousAt_const).continuousWithinAt
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hL hcont.intervalIntegrable
  have him := integral_im_eq hcont.intervalIntegrable
  rw [hFTC] at him
  have hval : (fun t => (logDeriv f (p t) * I).im) = fun t => (logDeriv f (p t)).re := by
    funext t; simp
  rw [hval] at him
  show |∫ t in T₁..T₂, (logDeriv f (p t)).re| ≤ 2 * Real.pi
  rw [← him, Complex.sub_im, Complex.log_im, Complex.log_im]
  have h1 := Complex.abs_arg_le_pi (f (p T₂))
  have h2 := Complex.abs_arg_le_pi (f (p T₁))
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith

/-- **Good heights are cofinal.** For `E` holomorphic and not identically zero on the upper glue
domain, every interval `[n, n + 1]`, `n > 0`, contains a height `Y` with `E ≠ 0` on
`[a, b] + iY`. -/
theorem exists_glue_good_height {E : ℂ → ℂ} (hE : AnalyticOnNhd ℂ E glueDomain) {z₀ : ℂ}
    (hz₀ : z₀ ∈ glueDomain) (hEz₀ : E z₀ ≠ 0) {a b n : ℝ} (ha : -(1 / 2) < a) (hab : a ≤ b)
    (hn : 0 < n) : ∃ Y ∈ Icc n (n + 1), ∀ x ∈ Icc a b, E ((x : ℂ) + Y * I) ≠ 0 := by
  classical
  set z₁ : ℂ := (a : ℂ) + n * I with hz₁
  set z₂ : ℂ := (b : ℂ) + (n + 1 : ℝ) * I with hz₂
  have hz₁re : z₁.re = a := by simp [hz₁]
  have hz₁im : z₁.im = n := by simp [hz₁]
  have hz₂re : z₂.re = b := by simp [hz₂]
  have hz₂im : z₂.im = n + 1 := by simp [hz₂]
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ glueDomain := by
    rw [hz₁re, hz₁im, hz₂re, hz₂im, uIcc_of_le hab, uIcc_of_le (by linarith)]
    intro z hz
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hz
    exact ⟨by linarith [hre.1], by linarith [him.1]⟩
  have hfin := zeros_closedRectangle_finite_of_analyticOnNhd hE isConnected_glueDomain hz₀ hEz₀
    hsub
  obtain ⟨Y, hY, hYS⟩ := (Set.Icc_infinite (by linarith : n < n + 1)).exists_notMem_finset
    (hfin.toFinset.image Complex.im)
  refine ⟨Y, hY, fun x hx h0 => hYS (Finset.mem_image.mpr ⟨(x : ℂ) + Y * I, ?_, by simp⟩)⟩
  rw [Set.Finite.mem_toFinset, Set.mem_sep_iff, hz₁re, hz₁im, hz₂re, hz₂im, uIcc_of_le hab,
    uIcc_of_le (by linarith)]
  exact ⟨Complex.mem_reProdIm.mpr ⟨by simpa using hx, by simpa using hY⟩, h0⟩

/-- **Comparison of the lock with its shift.** If `|v| = 1` and `|V(½ + ε − iy) − v(y)| ≤ ½` on
`[Y₀, Y]`, then `∫_{Y₀}^{Y} Im(v' v̄) ≤ 2π − ∫_{Y₀}^{Y} Re(V'/V)(½ + ε − iy) dy`. -/
theorem integral_lineLockVelocity_le {c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹)
    (hql : Summable fun j => ‖c j‖ * |Real.log (u j)|) {ε Y₀ Y : ℝ} (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 4) (hY : Y₀ ≤ Y) (hunit : ∀ y ∈ Icc Y₀ Y, ‖lineLock c u y‖ = 1)
    (hclose : ∀ y ∈ Icc Y₀ Y,
      ‖apLock c u (((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) - lineLock c u y‖ ≤ 1 / 2) :
    ∫ y in Y₀..Y, lineLockVelocity c u y ≤
      2 * Real.pi -
        ∫ y in Y₀..Y, (logDeriv (apLock c u) (((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I)).re := by
  have hqn : Summable fun j => ‖c j‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => le_mul_of_one_le_right (norm_nonneg _) (le_max_left _ _)) hc
  set V := apLock c u with hV
  set v := lineLock c u with hv
  set vd := lineLockDeriv c u with hvd
  set p : ℝ → ℂ := fun y => ((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I with hp
  have hpre : ∀ y, (p y).re = 1 / 2 + ε := fun y => by simp [hp]
  set U : Set ℂ := {z : ℂ | 1 / 2 < z.re ∧ z.re < 3 / 2} with hU
  have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)
  have hpU : ∀ y, p y ∈ U := fun y => ⟨by rw [hpre]; linarith, by rw [hpre]; linarith⟩
  have hVan : AnalyticOnNhd ℂ V U := DifferentiableOn.analyticOnNhd
    (fun z hz => (differentiableAt_apLock hu hc hz.1 hz.2).differentiableWithinAt) hUo
  have hpd : ∀ y : ℝ, HasDerivAt p (-I) y := by
    intro y
    have := ((hasDerivAt_id y).neg.ofReal_comp.mul_const I).const_add ((1 / 2 + ε : ℝ) : ℂ)
    simpa [hp] using this
  have hVp : ∀ y : ℝ, HasDerivAt (fun y => V (p y)) (deriv V (p y) * (-I)) y := fun y =>
    (hVan _ (hpU y)).differentiableAt.hasDerivAt.comp y (hpd y)
  -- the comparison function
  set h : ℝ → ℂ := fun y => v y * conj (V (p y)) with hh
  set h' : ℝ → ℂ := fun y => vd y * conj (V (p y)) + v y * conj (deriv V (p y) * (-I)) with hh'
  have hhd : ∀ y, HasDerivAt h (h' y) y := by
    intro y
    have h1 := hasDerivAt_lineLock hqn hql y
    have h2 := (hVp y).star
    simp only [Complex.star_def] at h2
    exact h1.mul h2
  have hre : ∀ y ∈ Icc Y₀ Y, 1 / 2 ≤ (h y).re := by
    intro y hy
    have hvy := hunit y hy
    have hcl := hclose y hy
    have heq : h y = v y * conj (v y) - v y * conj (v y - V (p y)) := by
      simp only [hh, map_sub]; ring
    have h1 : (v y * conj (v y)).re = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hvy]; simp
    have h2 : |(v y * conj (v y - V (p y))).re| ≤ 1 / 2 := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj, hvy, one_mul, norm_sub_rev]
      exact hcl
    rw [heq, Complex.sub_re, h1]
    linarith [(abs_le.mp h2).2]
  have hhne : ∀ y ∈ Icc Y₀ Y, h y ≠ 0 := fun y hy h0 => by
    have := hre y hy; rw [h0] at this; simp at this; linarith
  have hvne : ∀ y ∈ Icc Y₀ Y, v y ≠ 0 := fun y hy h0 => by
    have := hunit y hy; rw [h0, norm_zero] at this; exact zero_ne_one this
  have hVne : ∀ y ∈ Icc Y₀ Y, V (p y) ≠ 0 := fun y hy h0 => by
    apply hhne y hy; simp [hh, h0]
  -- the derivative of `log h`
  have hL : ∀ y ∈ uIcc Y₀ Y, HasDerivAt (fun y => Complex.log (h y)) (h' y / h y) y := by
    intro y hy
    rw [uIcc_of_le hY] at hy
    exact (hhd y).clog_real (Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [hre y hy])))
  have hdVc : Continuous fun y => deriv V (p y) := by
    have hcU : ContinuousOn (deriv V) U := hVan.deriv.continuousOn
    exact hcU.comp_continuous (by fun_prop) hpU
  have hVpc : Continuous fun y => V (p y) :=
    (continuous_apLock hu hc).comp (by fun_prop)
  have hvc : Continuous v := continuous_lineLock u hqn
  have hvdc : Continuous vd := continuous_lineLockDeriv hql
  have hh'c : Continuous h' :=
    (hvdc.mul (Complex.continuous_conj.comp hVpc)).add
      (hvc.mul (Complex.continuous_conj.comp (hdVc.mul continuous_const)))
  have hhc : Continuous h := hvc.mul (Complex.continuous_conj.comp hVpc)
  have hcont : ContinuousOn (fun y => h' y / h y) (uIcc Y₀ Y) := by
    rw [uIcc_of_le hY]
    exact hh'c.continuousOn.div hhc.continuousOn hhne
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hL hcont.intervalIntegrable
  have him := integral_im_eq hcont.intervalIntegrable
  rw [hFTC] at him
  -- the imaginary part of `h'/h`
  have hpt : ∀ y ∈ Icc Y₀ Y, (h' y / h y).im =
      lineLockVelocity c u y + (logDeriv V (p y)).re := by
    intro y hy
    have hvy := hunit y hy
    have hv0 := hvne y hy
    have hV0 := hVne y hy
    have hcv : conj (v y) = (v y)⁻¹ := by
      have hn : v y * conj (v y) = 1 := by
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hvy]; simp
      exact (eq_inv_of_mul_eq_one_right hn)
    have hcV : conj (V (p y)) ≠ 0 := (map_ne_zero _).mpr hV0
    have heq : h' y / h y = vd y * conj (v y) + conj (-I * logDeriv V (p y)) := by
      rw [logDeriv_apply, hcv]
      simp only [hh, hh', map_mul, map_neg, map_div₀, Complex.conj_I]
      field_simp
    rw [heq]
    show _ = (vd y * conj (v y)).im + _
    rw [Complex.add_im]
    congr 1
    simp [Complex.mul_im]
  have hint1 : IntervalIntegrable (lineLockVelocity c u) volume Y₀ Y :=
    (continuous_lineLockVelocity hqn hql).intervalIntegrable _ _
  have hlogc : ContinuousOn (fun y => (logDeriv V (p y)).re) (uIcc Y₀ Y) := by
    rw [uIcc_of_le hY]
    intro y hy
    exact (Complex.continuous_re.continuousAt.comp ((analyticAt_logDeriv_of_ne_zero
      (hVan _ (hpU y)) (hVne y hy)).continuousAt.comp (hpd y).continuousAt)).continuousWithinAt
  have hint2 : IntervalIntegrable (fun y => (logDeriv V (p y)).re) volume Y₀ Y :=
    hlogc.intervalIntegrable
  have hsplit : ∫ y in Y₀..Y, (h' y / h y).im =
      (∫ y in Y₀..Y, lineLockVelocity c u y) + ∫ y in Y₀..Y, (logDeriv V (p y)).re := by
    rw [← intervalIntegral.integral_add hint1 hint2]
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le hY] at hy
    exact hpt y hy
  rw [hsplit] at him
  have hbd : (Complex.log (h Y) - Complex.log (h Y₀)).im ≤ 2 * Real.pi := by
    rw [Complex.sub_im, Complex.log_im, Complex.log_im]
    have h1 := Complex.abs_arg_le_pi (h Y)
    have h2 := Complex.abs_arg_le_pi (h Y₀)
    rw [abs_le] at h1 h2
    linarith
  linarith

/-! ## The theorem -/

/-- **Almost-periodic locks force the true producer.** Let `G` be a Herglotz producer for the
weights `lam` with lower-line lock `G(1 − s) = V(s) G(s)`, `V(s) = Σ_j c_j u_j^{−(s−½)}`, with
`Σ_j |c_j| max(1, u_j^{−1}) K(u_j) < ∞` (`K(u) = √den(u) 8^{ω(den u)}` for rational `u`, `K = 1`
otherwise) and `Σ_j |c_j| |log u_j| < ∞`. Then `lam(n) = Λ(n)` for all `n ≥ 2`, and the Riemann
hypothesis holds. -/
theorem almostPeriodicLock_trueProducer {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (hcw : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹ * realDenWeight (u j))
    (hql : Summable fun j => ‖c j‖ * |Real.log (u j)|)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = apLock c u (lineS τ) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  /- the factorization -/
  obtain ⟨Ψ, B, hB, hW, hΨ⟩ :=
    almostPeriodicLock_limitPeriodic hsl hΦre hid hGc hGd hG2 hu hcw hlock
  have hB0 : ∀ q, 0 ≤ B q := fun q => (norm_nonneg _).trans (hB q 0)
  have h8 : Summable fun q : ℕ => (8 : ℝ) ^ (q + 1).primeFactors.card * B q :=
    Summable.of_nonneg_of_le (fun q => mul_nonneg (by positivity) (hB0 q)) (fun q => by
      have hsq : (1 : ℝ) ≤ Real.sqrt ((q : ℝ) + 1) :=
        Real.one_le_sqrt.mpr (le_add_of_nonneg_left (Nat.cast_nonneg q))
      calc (8 : ℝ) ^ (q + 1).primeFactors.card * B q
          = 1 * 8 ^ (q + 1).primeFactors.card * B q := by ring
        _ ≤ Real.sqrt ((q : ℝ) + 1) * 8 ^ (q + 1).primeFactors.card * B q :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq (by positivity))
            (hB0 q)) hW
  obtain ⟨hGK, hFA⟩ := limitPeriodic_producer_factor hsl hΦd hid hGc hGd hG2 hB hW hΨ
  set A := limitTrivialSeries Ψ with hAdef
  have hAd : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_limitTrivialSeries hB h8
  have hAc : ContinuousOn A {s : ℂ | 1 / 2 ≤ s.re} := continuousOn_limitTrivialSeries hB h8
  set WA : ℝ := ∑' q : ℕ, (8 : ℝ) ^ (q + 1).primeFactors.card * B q with hWA
  have hAb : ∀ s : ℂ, 1 / 2 ≤ s.re → ‖A s‖ ≤ WA := fun s hs => norm_limitTrivialSeries_le hB h8 hs
  have hUA : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hAan : AnalyticOnNhd ℂ A {s : ℂ | 1 / 2 < s.re} := hAd.analyticOnNhd hUA
  have hzA : ∀ s : ℂ, 1 < s.re → zetaOf lam s = riemannZeta s * A s := by
    intro s hs
    rw [← hFA s hs]
    exact (LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)).2.symm
  obtain ⟨σ₀, hσ₀2, hanchor⟩ := exists_re_ge_half_of_zetaOf_eq hsl hzA
  have hA0 : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → A s ≠ 0 := fun s hs hs1 h =>
    G_ne_zero hΦd hGd hG2 hs (by rw [hGK s hs hs1, h]; ring)
  have hAσ : ∀ s : ℂ, σ₀ ≤ s.re → A s ≠ 0 := fun s hs h => by
    have := hanchor s hs; rw [h] at this; simp at this; linarith
  /- the lock -/
  have hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹ :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))
      (fun j => le_mul_of_one_le_right
        (mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))
        (one_le_realDenWeight _)) hcw
  have hqn : Summable fun j => ‖c j‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _)
      (fun j => le_mul_of_one_le_right (norm_nonneg _) (le_max_left _ _)) hc
  set V := apLock c u with hVdef
  set CV : ℝ := ∑' j, ‖c j‖ * max 1 (u j)⁻¹ with hCV
  have hVb : ∀ s, ‖V s‖ ≤ CV := norm_apLock_le hu hc
  have hlockA : ∀ y : ℝ, 0 < y → A (1 / 2 + y * I) = V (1 / 2 - y * I) * A (1 / 2 - y * I) :=
    fun y hy => lineFactor_lock hGc hGK hAc (continuous_apLock hu hc) hlock hy
  have hunit : ∀ y : ℝ, 0 < y → ‖lineLock c u y‖ = 1 := fun y hy =>
    norm_lineLock hsl hΦd hΦre hid hGc hGd hG2 hu hc hlock hy
  have hline : ∀ y : ℝ, V (1 / 2 - y * I) = lineLock c u y := fun y => apLock_line c hu y
  /- the glued function -/
  set E := lockGlue A V with hEdef
  have hEan : AnalyticOnNhd ℂ E glueDomain :=
    (differentiableOn_lockGlue hu hc hAd hAc hlockA).analyticOnNhd isOpen_glueDomain
  set WE : ℝ := max 1 CV * WA with hWE
  have hEb : ∀ z, ‖E z‖ ≤ WE := norm_lockGlue_le hAb hVb
  have hEA : ∀ z : ℂ, 1 / 2 ≤ z.re → E z = A z := fun z hz => lockGlue_of_le hz
  have hEL : ∀ z : ℂ, z.re < 1 / 2 → E z = V (1 - z) * A (1 - z) := fun z hz =>
    lockGlue_of_lt hz
  /- the shift -/
  obtain ⟨ε, hε0, hε14, hclose⟩ := exists_shift_apLock_close hu hc
  set p : ℝ → ℂ := fun y => ((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I with hp
  have hpre : ∀ y, (p y).re = 1 / 2 + ε := fun y => by simp [hp]
  have hclose' : ∀ y : ℝ, ‖V (p y) - lineLock c u y‖ ≤ 1 / 2 := fun y => by
    rw [← hline y]; exact hclose y
  have hVp0 : ∀ y : ℝ, 0 < y → V (p y) ≠ 0 := by
    intro y hy h0
    have h1 := hclose' y
    rw [h0, zero_sub, norm_neg, hunit y hy] at h1
    norm_num at h1
  have hp1 : ∀ y : ℝ, 0 < y → p y ≠ 1 := fun y hy h => by
    have := congrArg Complex.im h; simp [hp] at this; linarith
  have hAp0 : ∀ y : ℝ, 0 < y → A (p y) ≠ 0 := fun y hy =>
    hA0 _ (by rw [hpre]; linarith) (hp1 y hy)
  /- the constants -/
  set CBE : ℝ := (Real.log (WE / (1 / 2)) / Real.log (σ₀ / (σ₀ - 1 / 2 + ε)) + 1) * Real.pi
    with hCBE
  set CBA : ℝ := (Real.log (WA / (1 / 2)) / Real.log ((σ₀ - 1 / 2 - ε / 2) / (σ₀ - 1 / 2 - ε))
    + 1) * Real.pi with hCBA
  set Cfin : ℝ := 6 * Real.pi + 2 * CBE + 2 * CBA with hCfin
  /- the horizontal bounds -/
  have hhorE : ∀ Y : ℝ, σ₀ + 1 ≤ Y → (∀ x ∈ Icc (1 / 2 - ε) σ₀, E ((x : ℂ) + Y * I) ≠ 0) →
      |∫ x in (1 / 2 - ε)..σ₀, (logDeriv E ((x : ℂ) + Y * I)).im| ≤ CBE := by
    intro Y hY hne
    refine abs_integral_im_logDeriv_horizontal_le (r := σ₀ - 1 / 2 + ε) (R := σ₀)
      (R₂ := σ₀ + 1 / 4) (M := WE) (m := 1 / 2) (by linarith)
      (by linarith) (by linarith) (by norm_num) ?_ (fun z _ => hEb z) ?_ (by linarith) (by linarith)
      hne
    · intro z hz
      refine hEan z ⟨?_, ?_⟩
      · have h1 := (Complex.abs_re_le_norm (z - ((σ₀ : ℂ) + Y * I))).trans
          (le_of_lt (mem_ball_iff_norm.mp hz))
        rw [abs_le] at h1; simp at h1; linarith [h1.1]
      · have h1 := (Complex.abs_im_le_norm (z - ((σ₀ : ℂ) + Y * I))).trans
          (le_of_lt (mem_ball_iff_norm.mp hz))
        rw [abs_le] at h1; simp at h1; linarith [h1.1]
    · rw [hEA _ (by simp; linarith)]
      exact hanchor _ (by simp)
  have hhorA : ∀ Y : ℝ, 0 < Y →
      |∫ x in (1 / 2 + ε)..σ₀, (logDeriv A ((x : ℂ) + ((-Y : ℝ) : ℂ) * I)).im| ≤ CBA := by
    intro Y hY
    refine abs_integral_im_logDeriv_horizontal_le (r := σ₀ - 1 / 2 - ε)
      (R := σ₀ - 1 / 2 - ε / 2) (R₂ := σ₀ - 1 / 2) (M := WA) (m := 1 / 2) (by linarith)
      (by linarith) (by linarith) (by norm_num) ?_ (fun z hz => hAb z ?_) ?_ (by linarith)
      (by linarith) ?_
    · intro z hz
      refine hAan z ?_
      have h1 := (Complex.abs_re_le_norm (z - ((σ₀ : ℂ) + ((-Y : ℝ) : ℂ) * I))).trans_lt
        (mem_ball_iff_norm.mp hz)
      rw [abs_lt] at h1; simp at h1; show 1 / 2 < z.re; linarith [h1.1]
    · have h1 := (Complex.abs_re_le_norm (z - ((σ₀ : ℂ) + ((-Y : ℝ) : ℂ) * I))).trans
        (mem_closedBall_iff_norm.mp hz)
      rw [abs_le] at h1; simp at h1; linarith [h1.1]
    · exact hanchor _ (by simp)
    · intro x hx
      refine hA0 _ (by simp; linarith [hx.1]) fun h => ?_
      have := congrArg Complex.im h; simp at this; linarith
  /- the base height -/
  have hz₀ : ((σ₀ : ℂ) + (σ₀ + 1 : ℝ) * I) ∈ glueDomain := ⟨by simp; linarith, by simp; linarith⟩
  have hEz₀ : E ((σ₀ : ℂ) + (σ₀ + 1 : ℝ) * I) ≠ 0 := by
    rw [hEA _ (by simp; linarith)]; exact hAσ _ (by simp)
  have hgood : ∀ n : ℝ, σ₀ + 1 ≤ n → ∃ Y ∈ Icc n (n + 1),
      ∀ x ∈ Icc (1 / 2 - ε) σ₀, E ((x : ℂ) + Y * I) ≠ 0 := fun n hn =>
    exists_glue_good_height hEan hz₀ hEz₀ (by linarith) (by linarith) (by linarith)
  obtain ⟨Y₀, hY₀, hY₀good⟩ := hgood (σ₀ + 1) le_rfl
  /- the key bound -/
  have hkey : ∀ Y : ℝ, Y₀ < Y → (∀ x ∈ Icc (1 / 2 - ε) σ₀, E ((x : ℂ) + Y * I) ≠ 0) →
      ∫ y in Y₀..Y, lineLockVelocity c u y ≤ Cfin := by
    intro Y hY hYgood
    have hY₀pos : 0 < Y₀ := by linarith [hY₀.1]
    have hYpos : ∀ y ∈ Icc Y₀ Y, 0 < y := fun y hy => by linarith [hy.1]
    -- the upper rectangle for `E`
    have hsubE : (uIcc (1 / 2 - ε) σ₀ ×ℂ uIcc Y₀ Y) ⊆ glueDomain := by
      rw [uIcc_of_le (by linarith), uIcc_of_le hY.le]
      intro z hz
      obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hz
      exact ⟨by linarith [hre.1], by linarith [him.1]⟩
    have hleftE : ∀ t ∈ uIcc Y₀ Y, E (((1 / 2 - ε : ℝ) : ℂ) + t * I) ≠ 0 := by
      intro t ht
      rw [uIcc_of_le hY.le] at ht
      have h1 : 1 - (((1 / 2 - ε : ℝ) : ℂ) + t * I) = p t := by rw [hp]; push_cast; ring
      rw [hEL _ (by simp; linarith), h1]
      exact mul_ne_zero (hVp0 t (hYpos t ht)) (hAp0 t (hYpos t ht))
    have hrightE : ∀ t ∈ uIcc Y₀ Y, E ((σ₀ : ℂ) + t * I) ≠ 0 := by
      intro t _
      rw [hEA _ (by simp; linarith)]; exact hAσ _ (by simp)
    have hQE := argument_variation_rectangle_le isOpen_glueDomain isConnected_glueDomain hEan
      hz₀ hEz₀ (c := 1 / 2 - ε) (d := σ₀) (T₁ := Y₀) (T₂ := Y) (by linarith) hY hsubE
      (fun x hx => hY₀good x (by rwa [uIcc_of_le (by linarith)] at hx))
      (fun x hx => hYgood x (by rwa [uIcc_of_le (by linarith)] at hx)) hrightE hleftE
    -- the lower rectangle for `A`
    have hconnA : IsConnected {s : ℂ | 1 / 2 < s.re} :=
      ⟨⟨1, by simp; norm_num⟩, (convex_halfSpace_re_gt _).isPreconnected⟩
    have hsubA : (uIcc (1 / 2 + ε) σ₀ ×ℂ uIcc (-Y) (-Y₀)) ⊆ {s : ℂ | 1 / 2 < s.re} := by
      rw [uIcc_of_le (by linarith)]
      intro z hz
      obtain ⟨hre, _⟩ := Complex.mem_reProdIm.mp hz
      show 1 / 2 < z.re; linarith [hre.1]
    have hAne_low : ∀ z : ℂ, 1 / 2 < z.re → z.im < 0 → A z ≠ 0 := fun z hz him =>
      hA0 z hz fun h => by rw [h] at him; simp at him
    have hQA := argument_variation_rectangle_le hUA hconnA hAan
      (x₀ := (σ₀ : ℂ)) (by simp; linarith) (hAσ _ (by simp)) (c := 1 / 2 + ε) (d := σ₀)
      (T₁ := -Y) (T₂ := -Y₀) (by linarith) (by linarith) hsubA
      (fun x hx => hAne_low _ (by
        rw [uIcc_of_le (by linarith)] at hx; simp; linarith [hx.1]) (by simp; linarith))
      (fun x hx => hAne_low _ (by
        rw [uIcc_of_le (by linarith)] at hx; simp; linarith [hx.1]) (by simp; linarith))
      (fun t _ => hAσ _ (by simp))
      (fun t ht => hAne_low _ (by simp; linarith) (by
        rw [uIcc_of_le (by linarith)] at ht; simp; linarith [ht.2]))
    -- the left edge of the upper rectangle
    have hVan : ∀ y : ℝ, DifferentiableAt ℂ V (p y) := fun y =>
      differentiableAt_apLock hu hc (by rw [hpre]; linarith) (by rw [hpre]; linarith)
    have hApd : ∀ y : ℝ, 0 < y → DifferentiableAt ℂ A (p y) := fun y _ =>
      (hAd (p y) (by show 1 / 2 < (p y).re; rw [hpre]; linarith)).differentiableAt
        (hUA.mem_nhds (by show 1 / 2 < (p y).re; rw [hpre]; linarith))
    have hleftEq : ∀ t ∈ uIcc Y₀ Y, (logDeriv E (((1 / 2 - ε : ℝ) : ℂ) + t * I)).re =
        -(logDeriv V (p t)).re - (logDeriv A (p t)).re := by
      intro t ht
      rw [uIcc_of_le hY.le] at ht
      have h1 : 1 - (((1 / 2 - ε : ℝ) : ℂ) + t * I) = p t := by rw [hp]; push_cast; ring
      have hlog : logDeriv E (((1 / 2 - ε : ℝ) : ℂ) + t * I) =
          -(logDeriv V (1 - (((1 / 2 - ε : ℝ) : ℂ) + t * I)) +
            logDeriv A (1 - (((1 / 2 - ε : ℝ) : ℂ) + t * I))) :=
        logDeriv_lockGlue_left (by simp; linarith) (by rw [h1]; exact hVan t)
          (by rw [h1]; exact hApd t (hYpos t ht)) (by rw [h1]; exact hVp0 t (hYpos t ht))
          (by rw [h1]; exact hAp0 t (hYpos t ht))
      rw [hlog, h1]
      simp only [Complex.neg_re, Complex.add_re]
      ring
    have hrightEq : ∀ t : ℝ, logDeriv E ((σ₀ : ℂ) + t * I) = logDeriv A ((σ₀ : ℂ) + t * I) :=
      fun t => logDeriv_lockGlue_right (A := A) (V := V) (by simp; linarith)
    -- continuity of the edge integrands
    have hcV : ContinuousOn (fun y => (logDeriv V (p y)).re) (uIcc Y₀ Y) := by
      rw [uIcc_of_le hY.le]
      intro y hy
      have han : AnalyticAt ℂ V (p y) := by
        set U : Set ℂ := {z : ℂ | 1 / 2 < z.re ∧ z.re < 3 / 2}
        have hUo : IsOpen U := (isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)
        exact DifferentiableOn.analyticAt (fun z hz =>
          (differentiableAt_apLock hu hc hz.1 hz.2).differentiableWithinAt)
          (hUo.mem_nhds ⟨by rw [hpre]; linarith, by rw [hpre]; linarith⟩)
      exact (Complex.continuous_re.continuousAt.comp ((analyticAt_logDeriv_of_ne_zero han
        (hVp0 y (hYpos y hy))).continuousAt.comp (by fun_prop))).continuousWithinAt
    have hcA : ContinuousOn (fun y => (logDeriv A (p y)).re) (uIcc Y₀ Y) := by
      rw [uIcc_of_le hY.le]
      intro y hy
      have han : AnalyticAt ℂ A (p y) := hAan _ (by show 1 / 2 < (p y).re; rw [hpre]; linarith)
      exact (Complex.continuous_re.continuousAt.comp ((analyticAt_logDeriv_of_ne_zero han
        (hAp0 y (hYpos y hy))).continuousAt.comp (by fun_prop))).continuousWithinAt
    have hLE : ∫ t in Y₀..Y, (logDeriv E (((1 / 2 - ε : ℝ) : ℂ) + t * I)).re =
        -(∫ y in Y₀..Y, (logDeriv V (p y)).re) - ∫ y in Y₀..Y, (logDeriv A (p y)).re := by
      rw [intervalIntegral.integral_congr hleftEq]
      have hsub := intervalIntegral.integral_sub (μ := volume) hcV.intervalIntegrable.neg
        hcA.intervalIntegrable
      simp only [Pi.neg_apply, intervalIntegral.integral_neg] at hsub
      exact hsub
    have hRE : ∫ t in Y₀..Y, (logDeriv E ((σ₀ : ℂ) + t * I)).re =
        ∫ t in Y₀..Y, (logDeriv A ((σ₀ : ℂ) + t * I)).re := by
      simp only [hrightEq]
    have hLA : ∫ y in Y₀..Y, (logDeriv A (p y)).re =
        ∫ t in (-Y)..(-Y₀), (logDeriv A (((1 / 2 + ε : ℝ) : ℂ) + t * I)).re := by
      rw [← intervalIntegral.integral_comp_neg]
    -- the vertical edges at `σ₀`
    have hS1 := abs_integral_re_logDeriv_vertical_le (f := A) (σ := σ₀) hY.le
      (fun t _ => hAan _ (by simp; linarith)) (fun t _ => by
        have := hanchor ((σ₀ : ℂ) + t * I) (by simp); linarith)
    have hS2 := abs_integral_re_logDeriv_vertical_le (f := A) (σ := σ₀)
      (T₁ := -Y) (T₂ := -Y₀) (by linarith)
      (fun t _ => hAan _ (by simp; linarith)) (fun t _ => by
        have := hanchor ((σ₀ : ℂ) + t * I) (by simp); linarith)
    -- the horizontal edges
    have hB1 := hhorE Y₀ hY₀.1 hY₀good
    have hB2 := hhorE Y (by linarith [hY₀.1]) hYgood
    have hB3 := hhorA Y (by linarith)
    have hB4 := hhorA Y₀ hY₀pos
    have hcmp : ∫ y in Y₀..Y, lineLockVelocity c u y ≤
        2 * Real.pi - ∫ y in Y₀..Y, (logDeriv V (p y)).re :=
      integral_lineLockVelocity_le hu hc hql hε0 hε14 hY.le
        (fun y hy => hunit y (hYpos y hy)) (fun y _ => hclose' y)
    rw [hRE, hLE] at hQE
    rw [hLA] at hQE
    rw [abs_le] at hS1 hS2 hB1 hB2 hB3 hB4
    linarith [hS1.1, hS1.2, hS2.1, hS2.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2, hB4.1, hB4.2]
  /- the phase velocity has bounded integral -/
  set g := lineLockVelocity c u with hgdef
  have hgc : Continuous g := continuous_lineLockVelocity hqn hql
  have hpos : ∀ y : ℝ, 0 < y → 0 ≤ g y := fun y hy =>
    lineLockVelocity_nonneg hsl hΦd hΦre hid hGc hGd hG2 hu hc hql hlock hy
  have hY₀pos : 0 < Y₀ := by linarith [hY₀.1]
  have hCBE0 : 0 ≤ CBE := (abs_nonneg _).trans (hhorE Y₀ hY₀.1 hY₀good)
  have hCBA0 : 0 ≤ CBA := (abs_nonneg _).trans (hhorA Y₀ hY₀pos)
  have hCfin0 : 0 ≤ Cfin := by rw [hCfin]; have := Real.pi_pos; linarith
  have hbd : ∀ T : ℝ, Y₀ ≤ T → ∫ y in Y₀..T, g y ≤ Cfin := by
    intro T hT
    obtain ⟨Y, hY, hYg⟩ := hgood T (by linarith [hY₀.1])
    rcases eq_or_lt_of_le (hT.trans hY.1) with h | h
    · have hTY : T = Y₀ := le_antisymm (h ▸ hY.1) hT
      rw [hTY, intervalIntegral.integral_same]; exact hCfin0
    · have hk := hkey Y h hYg
      have hsplit : ∫ y in Y₀..Y, g y = (∫ y in Y₀..T, g y) + ∫ y in T..Y, g y :=
        (intervalIntegral.integral_add_adjacent_intervals (hgc.intervalIntegrable _ _)
          (hgc.intervalIntegrable _ _)).symm
      have hnn : 0 ≤ ∫ y in T..Y, g y :=
        intervalIntegral.integral_nonneg hY.1 fun y hy => hpos y (by linarith [hy.1])
      linarith
  /- so the mean of the velocity vanishes -/
  set gC : ℝ → ℂ := fun y => ((g y : ℝ) : ℂ) with hgC
  have hgCc : Continuous gC := Complex.continuous_ofReal.comp hgc
  have hgCa : _root_.HTGeometry.IsBohrAlmostPeriodic gC :=
    isBohrAlmostPeriodic_lineLockVelocity hqn hql
  have hg00 : 0 ≤ g 0 :=
    ge_of_tendsto ((hgc.tendsto 0).mono_left nhdsWithin_le_nhds : Tendsto g (𝓝[>] 0) (𝓝 (g 0)))
      (by filter_upwards [self_mem_nhdsWithin] with z (hz : 0 < z); exact hpos z hz)
  set K : ℝ := (∫ y in (0 : ℝ)..Y₀, g y) + Cfin with hK
  have hmeanlim : Tendsto (_root_.GaloisForLFunctions.windowAverage gC) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := K)).div_atTop tendsto_id)
    filter_upwards [eventually_ge_atTop Y₀] with T hT
    have hT0 : 0 < T := hY₀pos.trans_le hT
    have hwin : _root_.GaloisForLFunctions.windowAverage gC T =
        (((T⁻¹ * ∫ y in (0 : ℝ)..T, g y) : ℝ) : ℂ) := by
      simp only [_root_.GaloisForLFunctions.windowAverage, hgC, intervalIntegral.integral_ofReal,
        Complex.real_smul]
      push_cast; ring
    have hsplit : ∫ y in (0 : ℝ)..T, g y = (∫ y in (0 : ℝ)..Y₀, g y) + ∫ y in Y₀..T, g y :=
      (intervalIntegral.integral_add_adjacent_intervals (hgc.intervalIntegrable _ _)
        (hgc.intervalIntegrable _ _)).symm
    have hnn : 0 ≤ ∫ y in (0 : ℝ)..T, g y :=
      intervalIntegral.integral_nonneg hT0.le fun y hy => by
        rcases eq_or_lt_of_le hy.1 with h | h
        · rw [← h]; exact hg00
        · exact hpos y h
    rw [hwin, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hT0,
      abs_of_nonneg hnn, id, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (by linarith [hbd T hT]) hT0.le
  /- the tail: a nonnegative almost-periodic function of mean zero vanishes -/
  have hga : _root_.HTGeometry.IsBohrAlmostPeriodic g := isBohrAlmostPeriodic_of_ofReal' hgCa
  have hnorm : _root_.HTGeometry.IsBohrAlmostPeriodic fun t => ‖gC t‖ :=
    _root_.GaloisForLFunctions.isBohrAlmostPeriodic_norm_real hgCa
  have hdiff := _root_.GaloisForLFunctions.isBohrAlmostPeriodic_sub (hgCc.norm) hnorm hgc hga
  have hzero := _root_.HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero hdiff (by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    simp only [hgC, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos t ht), sub_self])
  have hnn : ∀ t, 0 ≤ g t := fun t => by
    have h := hzero t
    simp only [hgC, Complex.norm_real, Real.norm_eq_abs] at h
    have : |g t| = g t := by linarith
    rw [← this]; exact abs_nonneg _
  have hmean : _root_.GaloisForLFunctions.bohrMean gC = 0 :=
    _root_.GaloisForLFunctions.bohrMean_eq hgCc hgCa hmeanlim
  have hg0 : ∀ t, g t = 0 := by
    intro t
    have h := _root_.GaloisForLFunctions.eq_zero_of_bohrMean_eq_zero_of_nonneg hgCc hgCa
      (fun t => by simp [hgC, hnn t])
      (fun t => by simp [hgC]) hmean t
    simpa [hgC] using h
  /- the lock is constant -/
  have hphase : ∀ y, lineLockPhase c u y = 0 := by
    intro y
    simp only [lineLockPhase]
    rw [show (fun t => lineLockVelocity c u t) = fun _ => (0 : ℝ) from funext hg0]
    simp
  have hconst : ∀ y : ℝ, 0 < y → lineLock c u y = lineLock c u 1 := by
    intro y hy
    rw [lineLock_eq_mul_exp_phase hqn hql hunit hy, hphase]
    simp
  set κ := lineLock c u 1 with hκ
  have hκ0 : κ ≠ 0 := by
    intro h
    have := hunit 1 one_pos
    rw [← hκ, h, norm_zero] at this
    exact zero_ne_one this
  refine phase_lock_rigidity hsl hΦd hΦre hid hGc hGd hG2 le_rfl (inv_ne_zero hκ0)
    (fun y hy => ?_)
  have hl := hlock (-(y / 2)) (by linarith)
  have e1 : lineS (-(y / 2)) = 1 / 2 - ((y : ℝ) : ℂ) * I := by rw [lineS_eq]; push_cast; ring
  have e2 : (1 : ℂ) - (1 / 2 - (y : ℂ) * I) = 1 / 2 + (y : ℂ) * I := by ring
  rw [e1, e2, hline y, hconst y hy] at hl
  rw [hl, ← mul_assoc, inv_mul_cancel₀ hκ0, one_mul]

end

end AbelianTwist

end RHTower
