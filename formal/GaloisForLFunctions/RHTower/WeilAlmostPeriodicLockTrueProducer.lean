import GaloisForLFunctions.RHTower.WeilAlmostPeriodicLockRH
import GaloisForLFunctions.RHTower.LocalRectangleArgumentBound
import GaloisForLFunctions.HTGeometry.ZetaTailBound

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
    (DifferentiableOn.analyticOnNhd (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
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
        rw [hz']; simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]; push_cast; ring
      rw [h1]
      conv_lhs => rw [hz']
      exact hlockA z.im hzim
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
  have hprod := hV'.mul hA'
  rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds, hprod.deriv, logDeriv_apply, logDeriv_apply]
  simp only [Function.comp_apply]
  field_simp
  ring

end

end AbelianTwist

end RHTower
