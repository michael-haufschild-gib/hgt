import GaloisForLFunctions.RHTower.WeilAlmostPeriodicLockRH
import GaloisForLFunctions.RHTower.LocalRectangleArgumentBound
import GaloisForLFunctions.HTGeometry.ZetaTailBound
import GaloisForLFunctions.RHTower.WeilLockMeanMotionRigidity

/-!
# Almost-periodic locks force the true producer

**Theorem** (`almostPeriodicLock_trueProducer`). Let `G` be a Herglotz producer for the weights
`lam` with lower-line lock `G(1 − s) = V(s) G(s)`, `V(s) = Σ_j c_j u_j^{−(s−½)}`, where
`Σ_j |c_j| max(1, u_j^{−1}) K(u_j) < ∞` (the weight of `almostPeriodicLock_riemannHypothesis`).
Then `lam(n) = Λ(n)` for all `n ≥ 2`, and the Riemann hypothesis holds.

So a Herglotz producer with a weighted almost-periodic lock is the true producer.

**Theorem** (`boundedQuotient_lock_trueProducer`). More generally, a Herglotz producer of the form
`G = s(s − 1)Γ_ℝ ζ A`, with `A` bounded and continuous on `Re s ≥ ½`, whose lock `V` is continuous,
bounded, holomorphic on `½ < Re s < 3/2` and uniformly close to its shift
`V(½ + ε − i·)` (e.g. uniformly continuous on the closed strip,
`exists_shift_close_of_uniformContinuousOn`), is the true producer. Almost periodicity enters only
through the factorization. Boundedness of `A` may be relaxed to `|A(s)| ≤ W e^{|Im s|^α}`, `α < 1`
(`slowQuotient_lock_trueProducer`): the Backlund–Jensen constants then grow like `Y^α`, and the
monotone lock phase stays below the linear wall.

**Proof.** Write `v(y) = V(½ − iy) = e^{iθ(y)}` for the lock on the lower line, with `θ`
continuous.
* The limit-periodic expansion of the coefficients gives `G = s(s − 1)Γ_ℝ ζ A` on `Re s > ½`, with
  `A` continuous and bounded on `Re s ≥ ½` (`limitPeriodic_producer_factor`), and
  `A = exp(Σ lam(n) n^{−s}/log n)/ζ` on `Re s > 1`. Hence `Re A ≥ ½` on a half-plane
  `Re s ≥ σ₀` (`exists_re_ge_half_of_zetaOf_eq`).
* Dividing the lock by `s(s − 1)Γ_ℝ ζ`, which is symmetric under `s ↦ 1 − s`, gives
  `A(½ + iy) = V(½ − iy) A(½ − iy)` for `y > 0` (`lineFactor_lock`).
* So `E = A` on `Re z ≥ ½` and `E = V(1 − z) A(1 − z)` on `Re z < ½` is holomorphic on
  `Re z > −½`, `Im z > 0` (`differentiableOn_lockGlue`). In particular the zeros of `G` on the
  line are locally finite (`lineFactor_lowerZeros_finite`), and the positivity law makes `θ`
  nondecreasing (`local_phase_monotone`, `le_of_locally_monotone_off_finite`).
* Fix `ε` with `|V(½ + ε − iy) − v(y)| ≤ ½`. The argument principle for `E` on
  `[½ − ε, σ₀] × [Y₀, Y]` and for `A` on `[½ + ε, σ₀] × [−Y, −Y₀]` bounds the phase advance of
  `V(½ + ε − iy)` from above (`apLock_shiftedPhase_bound`): the enclosed zeros of `E` only lower
  it, the horizontal edges are bounded by Backlund–Jensen, and the edges at `σ₀` by `2π`.
* Comparing with `v` (`phase_sub_le_of_shift`) shows that `θ` is bounded above. A monotone
  bounded lock phase forces the true producer (`abelian_twist_power_rigidity`).
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

/-- The strip `½ < Re s < 3/2`, where locks are holomorphic. -/
def lockStrip : Set ℂ := {z : ℂ | 1 / 2 < z.re ∧ z.re < 3 / 2}

theorem isOpen_lockStrip : IsOpen lockStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt Complex.continuous_re continuous_const)

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

/-- The glued function inherits a growth bound `|A| ≤ W e^{|Im s|^α}` on `Re s ≥ ½`. -/
theorem norm_lockGlue_le_exp {A V : ℂ → ℂ} {WA CV α : ℝ}
    (hAg : ∀ s : ℂ, 1 / 2 ≤ s.re → ‖A s‖ ≤ WA * Real.exp (|s.im| ^ α)) (hVb : ∀ s, ‖V s‖ ≤ CV)
    (z : ℂ) : ‖lockGlue A V z‖ ≤ max 1 CV * (WA * Real.exp (|z.im| ^ α)) := by
  have hWA : 0 ≤ WA * Real.exp (|z.im| ^ α) := by
    have h := (norm_nonneg _).trans (hAg ((1 / 2 : ℂ) + z.im * I) (by simp))
    simpa using h
  rcases le_or_gt (1 / 2) z.re with hz | hz
  · rw [lockGlue_of_le hz]
    exact (hAg z hz).trans (le_mul_of_one_le_left hWA (le_max_left _ _))
  · rw [lockGlue_of_lt hz, norm_mul]
    have h1 := hAg (1 - z) (by simp; linarith)
    rw [show (1 - z).im = -z.im by simp, abs_neg] at h1
    exact mul_le_mul ((hVb _).trans (le_max_right _ _)) h1 (norm_nonneg _)
      (le_trans zero_le_one (le_max_left _ _))

/-- **The glued function is holomorphic** on `Re z > −½`, `Im z > 0`. -/
theorem differentiableOn_lockGlue {A V : ℂ → ℂ} (hVc : Continuous V)
    (hVd : DifferentiableOn ℂ V lockStrip)
    (hAd : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hAc : ContinuousOn A {s : ℂ | 1 / 2 ≤ s.re})
    (hlockA : ∀ y : ℝ, 0 < y → A (1 / 2 + y * I) = V (1 / 2 - y * I) * A (1 / 2 - y * I)) :
    DifferentiableOn ℂ (lockGlue A V) glueDomain := by
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
    have hVd : DifferentiableAt ℂ V (1 - z) :=
      hVd.differentiableAt (isOpen_lockStrip.mem_nhds ⟨h1z, h1z'⟩)
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

/-! ## Monotone phases and shifted phases -/

/-- A function continuous on `[c, d]` and locally nondecreasing at every interior point satisfies
`f c ≤ f d`. -/
theorem le_of_locally_monotone {f : ℝ → ℝ} {c d : ℝ} (hcd : c ≤ d)
    (hf : ContinuousOn f (Icc c d))
    (hloc : ∀ x ∈ Ioo c d, ∃ δ > 0, ∀ y y', x - δ < y → y ≤ y' → y' < x + δ → f y ≤ f y') :
    f c ≤ f d := by
  rcases eq_or_lt_of_le hcd with h | hlt
  · rw [h]
  have hstep : ∀ c' ∈ Ioo c d, f c' ≤ f d := by
    intro c' hc'
    have hclosed : IsClosed ({t | f c' ≤ f t} ∩ Icc c' d) := by
      rw [Set.inter_comm]
      exact (hf.mono (Icc_subset_Icc hc'.1.le le_rfl)).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_Ici
    have hsub := hclosed.Icc_subset_of_forall_mem_nhdsWithin
      (show c' ∈ {t | f c' ≤ f t} from le_refl (f c'))
      (fun x hx => by
        obtain ⟨δ, hδ, hmono⟩ := hloc x ⟨hc'.1.trans_le hx.2.1, hx.2.2⟩
        filter_upwards [Ioo_mem_nhdsGT (show x < x + δ by linarith)] with t ht
        exact (show f c' ≤ f x from hx.1).trans (hmono x t (by linarith) ht.1.le ht.2))
    exact hsub ⟨hc'.2.le, le_rfl⟩
  have hcw : ContinuousWithinAt f (Ioi c) c :=
    (hf c ⟨le_rfl, hcd⟩).mono_of_mem_nhdsWithin
      (mem_of_superset (Ioo_mem_nhdsGT hlt) Ioo_subset_Icc_self)
  refine le_of_tendsto hcw.tendsto ?_
  filter_upwards [Ioo_mem_nhdsGT hlt] with t ht
  exact hstep t ht

/-- **Local to global monotonicity off a finite set.** A function continuous on `[c, d]` and
locally nondecreasing at every interior point outside a finite set satisfies `f c ≤ f d`. -/
theorem le_of_locally_monotone_off_finite {f : ℝ → ℝ} (T : Finset ℝ) :
    ∀ {c d : ℝ}, c ≤ d → ContinuousOn f (Icc c d) →
      (∀ x ∈ Ioo c d, x ∉ T →
        ∃ δ > 0, ∀ y y', x - δ < y → y ≤ y' → y' < x + δ → f y ≤ f y') → f c ≤ f d := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact fun hcd hf hloc =>
      le_of_locally_monotone hcd hf fun x hx => hloc x hx (Finset.notMem_empty x)
  | insert a T haT ih =>
    intro c d hcd hf hloc
    by_cases ha : a ∈ Ioo c d
    · have h1 : f c ≤ f a := ih ha.1.le (hf.mono (Icc_subset_Icc le_rfl ha.2.le))
        (fun x hx hxT => hloc x ⟨hx.1, hx.2.trans ha.2⟩ (by
          rw [Finset.mem_insert]; rintro (h | h)
          · exact (lt_irrefl a) (h ▸ hx.2)
          · exact hxT h))
      have h2 : f a ≤ f d := ih ha.2.le (hf.mono (Icc_subset_Icc ha.1.le le_rfl))
        (fun x hx hxT => hloc x ⟨ha.1.trans hx.1, hx.2⟩ (by
          rw [Finset.mem_insert]; rintro (h | h)
          · exact (lt_irrefl a) (h ▸ hx.1)
          · exact hxT h))
      exact h1.trans h2
    · exact ih hcd hf fun x hx hxT => hloc x hx (by
        rw [Finset.mem_insert]; rintro (h | h)
        · exact ha (h ▸ hx)
        · exact hxT h)

/-- **Comparison of a unimodular phase with a nearby smooth function.** Let `v = e^{iθ}` with `θ`
continuous, and let `W` be differentiable with `|W − v| ≤ ½` on `[Y₀, Y]`. Then
`θ(Y) − θ(Y₀) ≤ 2π + ∫_{Y₀}^{Y} Im(W'/W)`. -/
theorem phase_sub_le_of_shift {v W W' : ℝ → ℂ} {θ : ℝ → ℝ} {Y₀ Y : ℝ} (hY : Y₀ ≤ Y)
    (hθc : ContinuousOn θ (Icc Y₀ Y)) (hθ : ∀ y ∈ Icc Y₀ Y, v y = cexp ((θ y : ℂ) * I))
    (hvc : ContinuousOn v (Icc Y₀ Y)) (hW : ∀ y ∈ Icc Y₀ Y, HasDerivAt W (W' y) y)
    (hWc : ContinuousOn (fun y => W' y / W y) (Icc Y₀ Y))
    (hclose : ∀ y ∈ Icc Y₀ Y, ‖W y - v y‖ ≤ 1 / 2) :
    θ Y - θ Y₀ ≤ 2 * Real.pi + ∫ y in Y₀..Y, (W' y / W y).im := by
  have hvn : ∀ y ∈ Icc Y₀ Y, ‖v y‖ = 1 := fun y hy => by
    rw [hθ y hy, Complex.norm_exp_ofReal_mul_I]
  have hWne : ∀ y ∈ Icc Y₀ Y, W y ≠ 0 := fun y hy h => by
    have h1 := hclose y hy
    rw [h, zero_sub, norm_neg, hvn y hy] at h1
    norm_num at h1
  obtain ⟨L, hLc, hLd, hLe⟩ := exists_continuousOn_log_of_hasDerivAt hY hW hWc hWne
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => hLd y (by rwa [uIcc_of_le hY] at hy))
    ((uIcc_of_le hY).symm ▸ hWc).intervalIntegrable
  have him := integral_im_eq ((uIcc_of_le hY).symm ▸ hWc).intervalIntegrable
  rw [hFTC, Complex.sub_im] at him
  -- the comparison function
  set h : ℝ → ℂ := fun y => v y * conj (W y) with hh
  have hre : ∀ y ∈ Icc Y₀ Y, 1 / 2 ≤ (h y).re := by
    intro y hy
    have heq : h y = v y * conj (v y) - v y * conj (v y - W y) := by
      simp only [hh, map_sub]; ring
    have h1 : (v y * conj (v y)).re = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hvn y hy]; simp
    have h2 : |(v y * conj (v y - W y)).re| ≤ 1 / 2 := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_conj, hvn y hy, one_mul, norm_sub_rev]
      exact hclose y hy
    rw [heq, Complex.sub_re, h1]
    linarith [(abs_le.mp h2).2]
  have hslit : ∀ y ∈ Icc Y₀ Y, h y ∈ slitPlane := fun y hy =>
    Complex.mem_slitPlane_iff.mpr (Or.inl (by linarith [hre y hy]))
  have hWc' : ContinuousOn W (Icc Y₀ Y) := fun y hy => (hW y hy).continuousAt.continuousWithinAt
  have hhc : ContinuousOn h (Icc Y₀ Y) := hvc.mul (Complex.continuous_conj.comp_continuousOn hWc')
  have hloghc : ContinuousOn (fun y => Complex.log (h y)) (Icc Y₀ Y) :=
    hhc.clog fun y hy => hslit y hy
  -- the difference of the three phases is a multiple of `2π`
  set D : ℝ → ℝ := fun y => θ y - (L y).im - (Complex.log (h y)).im with hD
  have hDc : ContinuousOn (fun y => D y / (2 * Real.pi)) (Icc Y₀ Y) :=
    ((hθc.sub (Complex.continuous_im.comp_continuousOn hLc)).sub
      (Complex.continuous_im.comp_continuousOn hloghc)).div_const _
  have hDint : ∀ y ∈ Icc Y₀ Y, ∃ n : ℤ, D y / (2 * Real.pi) = n := by
    intro y hy
    have hexp : cexp (Complex.log (h y)) = cexp ((θ y : ℂ) * I + conj (L y)) := by
      rw [Complex.exp_log (fun h0 => by have := hre y hy; rw [h0] at this; simp at this; linarith),
        Complex.exp_add, Complex.exp_conj, ← hLe y hy, ← hθ y hy]
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    refine ⟨-n, ?_⟩
    have him' : (Complex.log (h y)).im = θ y - (L y).im + 2 * Real.pi * n := by
      rw [hn]; simp [Complex.mul_im]; ring
    have hpi := Real.pi_pos
    simp only [hD]
    rw [him', div_eq_iff (by positivity)]
    push_cast
    ring
  have hDconst := int_valued_const hY hDc hDint
  have hDeq : D Y = D Y₀ := by
    have hpi := Real.pi_pos
    field_simp at hDconst
    linarith
  simp only [hD] at hDeq
  have h1 := Complex.abs_arg_le_pi (h Y)
  have h2 := Complex.abs_arg_le_pi (h Y₀)
  rw [Complex.log_im, Complex.log_im] at hDeq
  rw [abs_le] at h1 h2
  linarith

/-! ## The theorem -/

/-- **Backlund–Jensen for the glued function at a positive height.** -/
theorem glue_horizontal_le {E : ℂ → ℂ} {σ₀ ε M Y : ℝ}
    (hEan : AnalyticOnNhd ℂ E glueDomain) (hσ₀ : 2 ≤ σ₀) (hε0 : 0 < ε) (hε : ε ≤ 1 / 4)
    (hY : σ₀ + 1 ≤ Y) (hM : ∀ z ∈ closedBall ((σ₀ : ℂ) + Y * I) σ₀, ‖E z‖ ≤ M)
    (hre : 1 / 2 ≤ (E ((σ₀ : ℂ) + Y * I)).re)
    (hne : ∀ x ∈ Icc (1 / 2 - ε) σ₀, E ((x : ℂ) + Y * I) ≠ 0) :
    |∫ x in (1 / 2 - ε)..σ₀, (logDeriv E ((x : ℂ) + Y * I)).im| ≤
      (Real.log (M / (1 / 2)) / Real.log (σ₀ / (σ₀ - 1 / 2 + ε)) + 1) * Real.pi := by
  refine abs_integral_im_logDeriv_horizontal_le (r := σ₀ - 1 / 2 + ε) (R := σ₀)
    (R₂ := σ₀ + 1 / 4) (by linarith) (by linarith) (by linarith) (by norm_num) ?_ hM hre
    (by linarith) (by linarith) hne
  intro z hz
  refine hEan z ⟨?_, ?_⟩
  · have h1 := (Complex.abs_re_le_norm (z - ((σ₀ : ℂ) + Y * I))).trans
      (le_of_lt (mem_ball_iff_norm.mp hz))
    rw [abs_le] at h1; simp at h1; linarith [h1.1]
  · have h1 := (Complex.abs_im_le_norm (z - ((σ₀ : ℂ) + Y * I))).trans
      (le_of_lt (mem_ball_iff_norm.mp hz))
    rw [abs_le] at h1; simp at h1; linarith [h1.1]

/-- **Backlund–Jensen for the quotient at a negative height.** -/
theorem quotient_horizontal_le {A : ℂ → ℂ} {σ₀ ε M Y : ℝ}
    (hAan : AnalyticOnNhd ℂ A {s : ℂ | 1 / 2 < s.re}) (hσ₀ : 2 ≤ σ₀) (hε0 : 0 < ε)
    (hε : ε ≤ 1 / 4)
    (hM : ∀ z ∈ closedBall ((σ₀ : ℂ) + ((-Y : ℝ) : ℂ) * I) (σ₀ - 1 / 2 - ε / 2), ‖A z‖ ≤ M)
    (hre : 1 / 2 ≤ (A ((σ₀ : ℂ) + ((-Y : ℝ) : ℂ) * I)).re)
    (hne : ∀ x ∈ Icc (1 / 2 + ε) σ₀, A ((x : ℂ) + ((-Y : ℝ) : ℂ) * I) ≠ 0) :
    |∫ x in (1 / 2 + ε)..σ₀, (logDeriv A ((x : ℂ) + ((-Y : ℝ) : ℂ) * I)).im| ≤
      (Real.log (M / (1 / 2)) / Real.log ((σ₀ - 1 / 2 - ε / 2) / (σ₀ - 1 / 2 - ε)) + 1) *
        Real.pi := by
  refine abs_integral_im_logDeriv_horizontal_le (r := σ₀ - 1 / 2 - ε)
    (R := σ₀ - 1 / 2 - ε / 2) (R₂ := σ₀ - 1 / 2) (by linarith) (by linarith) (by linarith)
    (by norm_num) ?_ hM hre (by linarith) (by linarith) hne
  intro z hz
  refine hAan z ?_
  have h1 := (Complex.abs_re_le_norm (z - ((σ₀ : ℂ) + ((-Y : ℝ) : ℂ) * I))).trans_lt
    (mem_ball_iff_norm.mp hz)
  rw [abs_lt] at h1; simp at h1; show 1 / 2 < z.re; linarith [h1.1]

/-- `(log(W e^t/½)/L + 1)π = (log(W/½)/L + 1)π + (π/L) t` for `W > 0`. -/
theorem backlund_const_exp {W L t : ℝ} (hW : 0 < W) (hL : L ≠ 0) :
    (Real.log (W * Real.exp t / (1 / 2)) / L + 1) * Real.pi =
      (Real.log (W / (1 / 2)) / L + 1) * Real.pi + Real.pi / L * t := by
  rw [show W * Real.exp t / (1 / 2) = W / (1 / 2) * Real.exp t by ring,
    Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp]
  field_simp
  ring

/-- **The shifted lock has bounded phase advance.** Let `A` be holomorphic on `Re s > ½`,
continuous and bounded on `Re s ≥ ½`, zero-free off `s = 1`, with `Re A ≥ ½` on `Re s ≥ σ₀`, and
let `A(½ + iy) = V(½ − iy) A(½ − iy)` for `y > 0`, where `V` is continuous, bounded, holomorphic on
`½ < Re s < 3/2` and unimodular on the lower line. If the shift `V(½ + ε − iy)` stays within `½`
of `V(½ − iy)`, then its phase advance `−∫_{Y₀}^{Y} Re(V'/V)(½ + ε − iy) dy` is bounded above at
cofinal heights `Y`. The proof is the argument principle for the glued function on
`[½ − ε, σ₀] × [Y₀, Y]` and for `A` on `[½ + ε, σ₀] × [−Y, −Y₀]`, with Backlund–Jensen on the
horizontal edges. -/
theorem lock_shiftedPhase_bound {A V : ℂ → ℂ} {WA CV α σ₀ ε : ℝ}
    (hVc : Continuous V) (hVd : DifferentiableOn ℂ V lockStrip) (hVb : ∀ s, ‖V s‖ ≤ CV)
    (hAd : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hAc : ContinuousOn A {s : ℂ | 1 / 2 ≤ s.re}) (hα : 0 ≤ α)
    (hAg : ∀ s : ℂ, 1 / 2 ≤ s.re → ‖A s‖ ≤ WA * Real.exp (|s.im| ^ α))
    (hA0 : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → A s ≠ 0)
    (hσ₀2 : 2 ≤ σ₀) (hanchor : ∀ s : ℂ, σ₀ ≤ s.re → 1 / 2 ≤ (A s).re)
    (hlockA : ∀ y : ℝ, 0 < y → A (1 / 2 + y * I) = V (1 / 2 - y * I) * A (1 / 2 - y * I))
    (hunit : ∀ y : ℝ, 0 < y → ‖V (1 / 2 - y * I)‖ = 1) (hε0 : 0 < ε) (hε14 : ε ≤ 1 / 4)
    (hclose : ∀ y : ℝ,
      ‖V (((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) - V (1 / 2 - (y : ℂ) * I)‖ ≤ 1 / 2) :
    ∃ Y₀ C₀ C₁ D : ℝ, 0 < Y₀ ∧ 0 ≤ C₁ ∧ 0 ≤ D ∧ ∀ T : ℝ, ∃ Y : ℝ, T ≤ Y ∧ Y ≤ max T Y₀ + 2 ∧
      Y₀ ≤ Y ∧ -(∫ y in Y₀..Y, (logDeriv V (((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I)).re) ≤
        C₀ + C₁ * (Y + D) ^ α := by
  have hUA : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hAan : AnalyticOnNhd ℂ A {s : ℂ | 1 / 2 < s.re} := hAd.analyticOnNhd hUA
  have hAσ : ∀ s : ℂ, σ₀ ≤ s.re → A s ≠ 0 := fun s hs h => by
    have := hanchor s hs; rw [h] at this; simp at this; linarith
  /- the glued function -/
  set E := lockGlue A V with hEdef
  have hEan : AnalyticOnNhd ℂ E glueDomain :=
    (differentiableOn_lockGlue hVc hVd hAd hAc hlockA).analyticOnNhd isOpen_glueDomain
  set WE : ℝ := max 1 CV * WA with hWE
  have hEb : ∀ z, ‖E z‖ ≤ max 1 CV * (WA * Real.exp (|z.im| ^ α)) := norm_lockGlue_le_exp hAg hVb
  have hWApos : 0 < WA := by
    have h1 := hanchor (σ₀ : ℂ) (by simp)
    have h2 := (Complex.re_le_norm _).trans (hAg (σ₀ : ℂ) (by simp; linarith))
    have h3 := Real.exp_pos (|((σ₀ : ℂ)).im| ^ α)
    by_contra hneg
    push Not at hneg
    nlinarith
  have hWEpos : 0 < WE := mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hWApos
  have hEA : ∀ z : ℂ, 1 / 2 ≤ z.re → E z = A z := fun z hz => lockGlue_of_le hz
  have hEL : ∀ z : ℂ, z.re < 1 / 2 → E z = V (1 - z) * A (1 - z) := fun z hz =>
    lockGlue_of_lt hz
  /- the shift -/
  set p : ℝ → ℂ := fun y => ((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I with hp
  have hpre : ∀ y, (p y).re = 1 / 2 + ε := fun y => by simp [hp]
  have hclose' : ∀ y : ℝ, ‖V (p y) - V (1 / 2 - (y : ℂ) * I)‖ ≤ 1 / 2 := fun y => hclose y
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
  set gY : ℝ → ℝ := fun Y => Real.exp ((Y + σ₀ + 1) ^ α) with hgY
  set LE : ℝ := Real.log (σ₀ / (σ₀ - 1 / 2 + ε)) with hLE
  set LA : ℝ := Real.log ((σ₀ - 1 / 2 - ε / 2) / (σ₀ - 1 / 2 - ε)) with hLA
  have hLE0 : 0 < LE := Real.log_pos (by rw [one_lt_div (by linarith)]; linarith)
  have hLA0 : 0 < LA := Real.log_pos (by rw [one_lt_div (by linarith)]; linarith)
  set CBE : ℝ → ℝ := fun Y => (Real.log (WE * gY Y / (1 / 2)) / LE + 1) * Real.pi with hCBE
  set CBA : ℝ → ℝ := fun Y => (Real.log (WA * gY Y / (1 / 2)) / LA + 1) * Real.pi with hCBA
  /- the growth on the Jensen discs -/
  have hexp_le : ∀ (Y : ℝ) (z : ℂ), 0 ≤ Y → |z.im| ≤ Y + σ₀ + 1 →
      Real.exp (|z.im| ^ α) ≤ gY Y := by
    intro Y z hY hz
    exact Real.exp_le_exp.mpr (Real.rpow_le_rpow (abs_nonneg _) hz hα)
  /- the horizontal bounds -/
  have hhorE : ∀ Y : ℝ, σ₀ + 1 ≤ Y → (∀ x ∈ Icc (1 / 2 - ε) σ₀, E ((x : ℂ) + Y * I) ≠ 0) →
      |∫ x in (1 / 2 - ε)..σ₀, (logDeriv E ((x : ℂ) + Y * I)).im| ≤ CBE Y := by
    intro Y hY hne
    refine glue_horizontal_le hEan hσ₀2 hε0 hε14 hY (fun z hz => ?_) ?_ hne
    · have h1 := (Complex.abs_im_le_norm (z - ((σ₀ : ℂ) + Y * I))).trans
        (mem_closedBall_iff_norm.mp hz)
      rw [abs_le] at h1; simp at h1
      have him : |z.im| ≤ Y + σ₀ + 1 := abs_le.mpr ⟨by linarith [h1.1], by linarith [h1.2]⟩
      calc ‖E z‖ ≤ max 1 CV * (WA * Real.exp (|z.im| ^ α)) := hEb z
        _ ≤ max 1 CV * (WA * gY Y) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
              (hexp_le Y z (by linarith) him) hWApos.le) (le_trans zero_le_one (le_max_left _ _))
        _ = WE * gY Y := by rw [hWE]; ring
    · rw [hEA _ (by simp; linarith)]
      exact hanchor _ (by simp)
  have hhorA : ∀ Y : ℝ, 0 < Y →
      |∫ x in (1 / 2 + ε)..σ₀, (logDeriv A ((x : ℂ) + ((-Y : ℝ) : ℂ) * I)).im| ≤ CBA Y := by
    intro Y hY
    refine quotient_horizontal_le hAan hσ₀2 hε0 hε14 (fun z hz => ?_) (hanchor _ (by simp))
      (fun x hx => ?_)
    · have h1 := (Complex.abs_re_le_norm (z - ((σ₀ : ℂ) + ((-Y : ℝ) : ℂ) * I))).trans
        (mem_closedBall_iff_norm.mp hz)
      have h2 := (Complex.abs_im_le_norm (z - ((σ₀ : ℂ) + ((-Y : ℝ) : ℂ) * I))).trans
        (mem_closedBall_iff_norm.mp hz)
      rw [abs_le] at h1 h2; simp at h1 h2
      have him : |z.im| ≤ Y + σ₀ + 1 := abs_le.mpr ⟨by linarith [h2.1], by linarith [h2.2]⟩
      calc ‖A z‖ ≤ WA * Real.exp (|z.im| ^ α) := hAg z (by linarith [h1.1])
        _ ≤ WA * gY Y := mul_le_mul_of_nonneg_left (hexp_le Y z hY.le him) hWApos.le
    · refine hA0 _ (by simp; linarith [hx.1]) fun h => ?_
      have := congrArg Complex.im h; simp at this; linarith
  have hCBEle : ∀ Y : ℝ, CBE Y = (Real.log (WE / (1 / 2)) / LE + 1) * Real.pi +
      Real.pi / LE * (Y + σ₀ + 1) ^ α := fun Y => backlund_const_exp hWEpos hLE0.ne'
  have hCBAle : ∀ Y : ℝ, CBA Y = (Real.log (WA / (1 / 2)) / LA + 1) * Real.pi +
      Real.pi / LA * (Y + σ₀ + 1) ^ α := fun Y => backlund_const_exp hWApos hLA0.ne'
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
      -(∫ y in Y₀..Y, (logDeriv V (p y)).re) ≤
        4 * Real.pi + CBE Y₀ + CBE Y + CBA Y₀ + CBA Y := by
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
      hVd.differentiableAt (isOpen_lockStrip.mem_nhds
        ⟨by rw [hpre]; linarith, by rw [hpre]; linarith⟩)
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
      have han : AnalyticAt ℂ V (p y) :=
        hVd.analyticAt (isOpen_lockStrip.mem_nhds ⟨by rw [hpre]; linarith, by rw [hpre]; linarith⟩)
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
    rw [hRE, hLE] at hQE
    rw [hLA] at hQE
    rw [abs_le] at hS1 hS2 hB1 hB2 hB3 hB4
    linarith [hS1.1, hS1.2, hS2.1, hS2.2, hB1.1, hB1.2, hB2.1, hB2.2, hB3.1, hB3.2, hB4.1, hB4.2]
  refine ⟨Y₀, 4 * Real.pi + CBE Y₀ + CBA Y₀ + (Real.log (WE / (1 / 2)) / LE + 1) * Real.pi +
    (Real.log (WA / (1 / 2)) / LA + 1) * Real.pi, Real.pi / LE + Real.pi / LA, σ₀ + 1,
    by linarith [hY₀.1], by positivity, by linarith, fun T => ?_⟩
  obtain ⟨Y, hYm, hYg⟩ := hgood (max T Y₀ + 1) (by linarith [le_max_right T Y₀, hY₀.1])
  have hY : Y₀ < Y := by linarith [le_max_right T Y₀, hYm.1]
  refine ⟨Y, by linarith [le_max_left T Y₀, hYm.1], by linarith [hYm.2], hY.le, ?_⟩
  have hk := hkey Y hY hYg
  rw [hCBEle Y, hCBAle Y] at hk
  have hr : (Y + (σ₀ + 1)) ^ α = (Y + σ₀ + 1) ^ α := by ring_nf
  rw [hr]
  linarith

/-- **Zeros of a factored producer on the lower line are locally finite.** If `G` is continuous
on `Re s ≥ ½` and equals `s(s − 1)Γ_ℝ ζ A` on `Re s > ½`, `s ≠ 1`, and `A` satisfies the lock
`A(½ + iy) = V(½ − iy) A(½ − iy)` (so that `A` glues holomorphically across the line), then `G` has
finitely many zeros on every compact piece of the lower critical line. -/
theorem lineFactor_lowerZeros_finite {G A V : ℂ → ℂ} (hVc : Continuous V)
    (hVd : DifferentiableOn ℂ V lockStrip)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGK : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
      G s = s * (s - 1) * Gammaℝ s * (riemannZeta s * A s))
    (hAd : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hAc : ContinuousOn A {s : ℂ | 1 / 2 ≤ s.re})
    (hlockA : ∀ y : ℝ, 0 < y → A (1 / 2 + y * I) = V (1 / 2 - y * I) * A (1 / 2 - y * I))
    {z₀ : ℂ} (hz₀ : z₀ ∈ glueDomain) (hEz₀ : lockGlue A V z₀ ≠ 0) :
    ∀ a b : ℝ, 0 < a → a ≤ b → {x ∈ Icc a b | G (vpt (1 / 2) x) = 0}.Finite := by
  set E := lockGlue A V with hEdef
  have hEan : AnalyticOnNhd ℂ E glueDomain :=
    (differentiableOn_lockGlue hVc hVd hAd hAc hlockA).analyticOnNhd isOpen_glueDomain
  have hEA : ∀ z : ℂ, 1 / 2 ≤ z.re → E z = A z := fun z hz => lockGlue_of_le hz
  have hvpt : ∀ x : ℝ, vpt (1 / 2) x = 1 / 2 - ((2 * x : ℝ) : ℂ) * I := fun x => by
    unfold vpt; push_cast; ring
  intro a b ha hab
  have hζU : AnalyticOnNhd ℂ riemannZeta {1}ᶜ :=
    DifferentiableOn.analyticOnNhd
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
      isOpen_compl_singleton
  have hcon : IsConnected ({1}ᶜ : Set ℂ) := isConnected_compl_singleton_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num) 1
  have hcod := hζU.preimage_zero_mem_codiscreteWithin (x := 2)
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num)) (by norm_num) hcon
  set g₁ : ℝ → ℂ := fun x => vpt (1 / 2) x with hg₁
  have hg₁c : Continuous g₁ := by simp only [hg₁, vpt]; fun_prop
  have hg₁i : Function.Injective g₁ := fun x x' h => by
    have := congrArg Complex.im h; simp [hg₁, vpt] at this; linarith
  set K : Set ℂ := g₁ '' Icc a b with hK
  have hKc : IsCompact K := isCompact_Icc.image hg₁c
  have hK1 : K ⊆ {1}ᶜ := by
    rintro _ ⟨x, _, rfl⟩ h
    have := congrArg Complex.re h; simp [hg₁, vpt] at this
  have hfinζ : (K \ (riemannZeta ⁻¹' {0}ᶜ)).Finite :=
    hKc.finite_sdiff_of_mem_codiscreteWithin (Filter.codiscreteWithin_mono hK1 hcod)
  set g₂ : ℝ → ℂ := fun x => (1 / 2 : ℂ) + ((2 * x : ℝ) : ℂ) * I with hg₂
  have hg₂i : Function.Injective g₂ := fun x x' h => by
    have := congrArg Complex.im h; simp [hg₂] at this; linarith
  set z₁ : ℂ := (1 / 2 : ℂ) + ((2 * a : ℝ) : ℂ) * I with hz₁
  set z₂ : ℂ := (1 / 2 : ℂ) + ((2 * b : ℝ) : ℂ) * I with hz₂
  have hz₁re : z₁.re = 1 / 2 := by simp [hz₁]
  have hz₂re : z₂.re = 1 / 2 := by simp [hz₂]
  have hz₁im : z₁.im = 2 * a := by simp [hz₁]
  have hz₂im : z₂.im = 2 * b := by simp [hz₂]
  have hsubE : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ glueDomain := by
    rw [hz₁re, hz₂re, hz₁im, hz₂im, uIcc_self, uIcc_of_le (by linarith : 2 * a ≤ 2 * b)]
    intro z hz
    obtain ⟨hre, him⟩ := Complex.mem_reProdIm.mp hz
    rw [Set.mem_singleton_iff] at hre
    exact ⟨by rw [hre]; norm_num, by linarith [him.1]⟩
  have hfinE := zeros_closedRectangle_finite_of_analyticOnNhd hEan isConnected_glueDomain hz₀
    hEz₀ hsubE
  refine ((hfinζ.preimage hg₁i.injOn).union (hfinE.preimage hg₂i.injOn)).subset ?_
  rintro x ⟨hx, hG0⟩
  have hre : (vpt (1 / 2) x).re = 1 / 2 := by simp [vpt]
  rw [eq_lineFactor_of_re_eq_half hGc hGK hAc hre] at hG0
  have hx0 : 0 < x := ha.trans_le hx.1
  have hv0' : vpt (1 / 2) x ≠ 0 := fun h => by
    have h1 := congrArg Complex.re h
    rw [hre, Complex.zero_re] at h1
    norm_num at h1
  have hv1 : vpt (1 / 2) x - 1 ≠ 0 := fun h => by
    have h1 := congrArg Complex.re h
    rw [Complex.sub_re, hre, Complex.one_re, Complex.zero_re] at h1
    norm_num at h1
  have hΓ : Gammaℝ (vpt (1 / 2) x) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hre]; norm_num)
  rcases mul_eq_zero.mp hG0 with h | h
  · exact absurd h (mul_ne_zero (mul_ne_zero hv0' hv1) hΓ)
  rcases mul_eq_zero.mp h with hζ | hA
  · left
    exact ⟨⟨x, hx, rfl⟩, by simpa [hg₁] using hζ⟩
  · right
    have hl := hlockA (2 * x) (by linarith)
    rw [← hvpt x, hA, mul_zero] at hl
    refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [hz₁re, hz₂re, uIcc_self, Set.mem_singleton_iff]; simp [hg₂]
    · rw [hz₁im, hz₂im, uIcc_of_le (by linarith)]
      have him2 : (g₂ x).im = 2 * x := by simp [hg₂]
      rw [him2]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · show E (g₂ x) = 0
      rw [hEA _ (by simp [hg₂]), ← hl]

/-- **Uniformly continuous locks are close to a small shift.** If `V` is uniformly continuous on
the closed strip `½ ≤ Re s ≤ 3/2`, then `|V(½ + ε − iy) − V(½ − iy)| ≤ ½` for some `ε ∈ (0, ¼]`
and all `y`. -/
theorem exists_shift_close_of_uniformContinuousOn {V : ℂ → ℂ}
    (hV : UniformContinuousOn V {z : ℂ | 1 / 2 ≤ z.re ∧ z.re ≤ 3 / 2}) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ ∀ y : ℝ,
      ‖V (((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) - V (1 / 2 - (y : ℂ) * I)‖ ≤ 1 / 2 := by
  obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuousOn_iff.mp hV (1 / 2) (by norm_num)
  set ε : ℝ := min (δ / 2) (1 / 4) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  refine ⟨ε, hε0, min_le_right _ _, fun y => ?_⟩
  have h1 : ((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I ∈ {z : ℂ | 1 / 2 ≤ z.re ∧ z.re ≤ 3 / 2} := by
    simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im]
    constructor <;> linarith [min_le_right (δ / 2) (1 / 4 : ℝ)]
  have h2 : (1 / 2 - (y : ℂ) * I) ∈ {z : ℂ | 1 / 2 ≤ z.re ∧ z.re ≤ 3 / 2} := by
    simp only [Set.mem_setOf_eq]; constructor <;> norm_num
  have hd : dist (((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) (1 / 2 - (y : ℂ) * I) < δ := by
    rw [dist_eq_norm, show ((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I - (1 / 2 - (y : ℂ) * I) =
      ((ε : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
    exact hεδ
  have := h _ h1 _ h2 hd
  rw [dist_eq_norm] at this
  exact this.le

/-- **A slowly growing quotient and a continuous lock force the true producer.** Let `G` be a
Herglotz producer for the weights `lam` that factors as `G = s(s − 1)Γ_ℝ(s) ζ(s) A(s)` on
`Re s > ½` (`s ≠ 1`), with `A` holomorphic on `Re s > ½`, continuous on `Re s ≥ ½`, and
`|A(s)| ≤ W e^{|Im s|^α}` there for some `α < 1`. Suppose the lower-line lock
`G(1 − s) = V(s) G(s)` holds with `V` continuous, bounded, holomorphic on `½ < Re s < 3/2`, and
uniformly close to a small right shift: `|V(½ + ε − iy) − V(½ − iy)| ≤ ½` for one `ε ∈ (0, ¼]`
and all `y` (true whenever `V` is uniformly continuous on the closed strip). Then
`lam(n) = Λ(n)` for all `n ≥ 2`, and RH holds.

No almost periodicity and no boundedness of the quotient is assumed: the obstruction to uniqueness
is a quotient `G/(s(s − 1)Γ_ℝ ζ)` that is singular at the critical line, not one that is large. -/
theorem slowQuotient_lock_trueProducer {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {A V : ℂ → ℂ} {WA CV α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hAd : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hAc : ContinuousOn A {s : ℂ | 1 / 2 ≤ s.re})
    (hAg : ∀ s : ℂ, 1 / 2 ≤ s.re → ‖A s‖ ≤ WA * Real.exp (|s.im| ^ α))
    (hGK : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
      G s = s * (s - 1) * Gammaℝ s * (riemannZeta s * A s))
    (hVc : Continuous V) (hVd : DifferentiableOn ℂ V lockStrip) (hVb : ∀ s, ‖V s‖ ≤ CV)
    (hshift : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ ∀ y : ℝ,
      ‖V (((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) - V (1 / 2 - (y : ℂ) * I)‖ ≤ 1 / 2)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = V (lineS τ) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hUA : IsOpen {s : ℂ | 1 / 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hzA : ∀ s : ℂ, 1 < s.re → zetaOf lam s = riemannZeta s * A s := by
    intro s hs
    have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
    have h1 := G_eq_bigG hsl hid hGd hG2 hs
    rw [hGK s (by linarith) hs1, bigG] at h1
    have hs0 : s ≠ 0 := fun h => by rw [h] at hs; simp at hs; linarith
    have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
    have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    have hpre : s * (s - 1) * Gammaℝ s ≠ 0 := mul_ne_zero (mul_ne_zero hs0 hs1') hΓ
    exact (mul_left_cancel₀ hpre h1).symm
  obtain ⟨σ₀, hσ₀2, hanchor⟩ := exists_re_ge_half_of_zetaOf_eq hsl hzA
  have hA0 : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 → A s ≠ 0 := fun s hs hs1 h =>
    G_ne_zero hΦd hGd hG2 hs (by rw [hGK s hs hs1, h]; ring)
  have hlockA : ∀ y : ℝ, 0 < y → A (1 / 2 + y * I) = V (1 / 2 - y * I) * A (1 / 2 - y * I) :=
    fun y hy => lineFactor_lock hGc hGK hAc hVc hlock hy
  have hunit : ∀ y : ℝ, 0 < y → ‖V (1 / 2 - (y : ℂ) * I)‖ = 1 := fun y hy =>
    norm_lock_eq_one hsl hΦd hΦre hid hGc hGd hG2 hVc hlock hy
  have hEz₀ : lockGlue A V ((σ₀ : ℂ) + (σ₀ + 1 : ℝ) * I) ≠ 0 := by
    rw [lockGlue_of_le (by simp; linarith)]
    exact fun h => by have := hanchor _ (show σ₀ ≤ ((σ₀ : ℂ) + (σ₀ + 1 : ℝ) * I).re by simp)
                      rw [h] at this; simp at this; linarith
  have hz₀ : ((σ₀ : ℂ) + (σ₀ + 1 : ℝ) * I) ∈ glueDomain := ⟨by simp; linarith, by simp; linarith⟩
  have hzfin := lineFactor_lowerZeros_finite hVc hVd hGc hGK hAd hAc hlockA hz₀ hEz₀
  obtain ⟨ε, hε0, hε14, hclose'⟩ := hshift
  obtain ⟨Y₀, C₀, C₁, D, hY₀pos, hC₁, hD, hgoodY⟩ :=
    lock_shiftedPhase_bound hVc hVd hVb hAd hAc hα0 hAg hA0 hσ₀2 hanchor hlockA hunit hε0 hε14
      hclose'
  set p : ℝ → ℂ := fun y => ((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I with hp
  have hpre : ∀ y, (p y).re = 1 / 2 + ε := fun y => by simp [hp]
  have hVp0 : ∀ y : ℝ, 0 < y → V (p y) ≠ 0 := by
    intro y hy h0
    have h1 := hclose' y
    rw [show V (((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) = V (p y) from rfl, h0,
      zero_sub, norm_neg, hunit y hy] at h1
    norm_num at h1
  /- the lock phase -/
  set vline : ℝ → ℂ := fun y => V (1 / 2 - (y : ℂ) * I) with hvline
  have hvc : Continuous vline := hVc.comp (by fun_prop)
  have hv0 : ‖vline 0‖ = 1 := by
    have hc0 : ContinuousAt (fun y => ‖vline y‖) 0 :=
      hvc.norm.continuousAt
    refine tendsto_nhds_unique (hc0.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto (fun y => ‖vline y‖) (𝓝[>] 0) _) (tendsto_const_nhds.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with y (hy : 0 < y)
    exact (hunit y hy).symm
  have hunit0 : ∀ y : ℝ, 0 ≤ y → ‖vline y‖ = 1 := fun y hy => by
    rcases eq_or_lt_of_le hy with h | h
    · rw [← h]; exact hv0
    · exact hunit y h
  set w : ℝ → ℂ := fun r => vline (max r 0) with hw
  have hwc : Continuous w := hvc.comp (continuous_id.max continuous_const)
  have hw0 : ∀ r, w r ≠ 0 := fun r h => by
    have := hunit0 (max r 0) (le_max_right _ _)
    rw [show vline (max r 0) = w r from rfl, h, norm_zero] at this
    exact zero_ne_one this
  have hUs : IsSimplyConnected (Set.univ : Set ℝ) := by
    rw [IsSimplyConnected]
    exact (Homeomorph.Set.univ ℝ).toHomotopyEquiv.simplyConnectedSpace
  obtain ⟨L, hLc', hLe'⟩ := Complex.exists_continuousOn_eqOn_exp_comp hUs isOpen_univ
    hwc.continuousOn (by rintro ⟨z, -, hz⟩; exact hw0 z hz)
  have hLc : Continuous L := continuousOn_univ.mp hLc'
  have hLe : ∀ r, cexp (L r) = w r := fun r => hLe' (mem_univ r)
  set θ : ℝ → ℝ := fun r => (L r).im with hθdef
  have hθc : Continuous θ := Complex.continuous_im.comp hLc
  have hθv : ∀ y : ℝ, 0 ≤ y → vline y = cexp ((θ y : ℂ) * I) := by
    intro y hy
    have h1 : cexp (L y) = vline y := by rw [hLe y]; simp [hw, max_eq_left hy]
    have h2 : (L y).re = 0 := by
      have := congrArg norm h1
      rw [Complex.norm_exp, hunit0 y hy] at this
      exact Real.exp_eq_one_iff _ |>.mp this
    rw [← h1]
    congr 1
    apply Complex.ext <;> simp [hθdef, h2]
  /- the positivity law: the lock phase is nondecreasing -/
  have hG20 : G 2 ≠ 0 := G_ne_zero hΦd hGd hG2 (by norm_num)
  obtain ⟨P, hP, hPG⟩ := exists_log_producer hΦd hGd
  set θc : ℝ → ℝ := fun x => θ (2 * x) with hθcdef
  have hθcc : Continuous θc := hθc.comp (continuous_const.mul continuous_id)
  have hvpt : ∀ x : ℝ, vpt (1 / 2) x = 1 / 2 - ((2 * x : ℝ) : ℂ) * I := fun x => by
    unfold vpt; push_cast; ring
  have hlockc : ∀ x : ℝ, 0 < x → G (1 - vpt (1 / 2) x) =
      1 * cexp ((θc x : ℂ) * I) * G (vpt (1 / 2) x) := by
    intro x hx
    have h := hlock (-x) (by linarith)
    rw [lineS_neg_eq_vpt] at h
    rw [h, one_mul, hvpt x]
    congr 1
    exact hθv (2 * x) (by linarith)
  have hθcmono : ∀ a b : ℝ, 0 < a → a ≤ b → θc a ≤ θc b := by
    intro a b ha hab
    have hfin := hzfin a b ha hab
    refine le_of_locally_monotone_off_finite hfin.toFinset hab hθcc.continuousOn ?_
    intro x hx hxT
    have hG0 : G (vpt (1 / 2) x) ≠ 0 := fun h => hxT (by
      rw [Set.Finite.mem_toFinset]; exact ⟨Ioo_subset_Icc_self hx, h⟩)
    exact local_phase_monotone hsl hΦre hid hGc hGd hG2 hG20 hP hPG hθcc hlockc (ha.trans hx.1) hG0
  have hθmono : ∀ y y' : ℝ, 0 ≤ y → y ≤ y' → θ y ≤ θ y' := by
    intro y y' hy hyy'
    rcases eq_or_lt_of_le hyy' with h | h
    · rw [h]
    have hhalf : ∀ t : ℝ, θc (t / 2) = θ t := fun t => by
      simp only [hθcdef]; congr 1; ring
    rcases eq_or_lt_of_le hy with h0 | h0
    · rw [← h0]
      refine le_of_tendsto (hθc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds :
        Tendsto θ (𝓝[>] 0) _) ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < y' by linarith)] with t ht
      have := hθcmono (t / 2) (y' / 2) (by linarith [ht.1]) (by linarith [ht.2])
      rwa [hhalf, hhalf] at this
    · have := hθcmono (y / 2) (y' / 2) (by linarith) (by linarith)
      rwa [hhalf, hhalf] at this
  /- the lock phase is bounded above -/
  have hpU : ∀ y, p y ∈ lockStrip := fun y => ⟨by rw [hpre]; linarith, by rw [hpre]; linarith⟩
  have hVanU : AnalyticOnNhd ℂ V lockStrip := hVd.analyticOnNhd isOpen_lockStrip
  have hpd : ∀ y : ℝ, HasDerivAt p (-I) y := by
    intro y
    have := ((hasDerivAt_id y).neg.ofReal_comp.mul_const I).const_add ((1 / 2 + ε : ℝ) : ℂ)
    simpa [hp] using this
  have hVp : ∀ y : ℝ, HasDerivAt (fun y => V (p y)) (deriv V (p y) * (-I)) y := fun y =>
    (hVanU _ (hpU y)).differentiableAt.hasDerivAt.comp y (hpd y)
  have hphase : ∀ Y : ℝ, Y₀ ≤ Y → ∀ Cfin : ℝ, -(∫ y in Y₀..Y, (logDeriv V (p y)).re) ≤ Cfin →
      θ Y - θ Y₀ ≤ 2 * Real.pi + Cfin := by
    intro Y hY Cfin hk
    have hcont : ContinuousOn (fun y => deriv V (p y) * (-I) / V (p y)) (Icc Y₀ Y) := by
      intro y hy
      have hd : ContinuousAt (fun y => deriv V (p y)) y :=
        (hVanU.deriv _ (hpU y)).continuousAt.comp (hpd y).continuousAt
      exact ((hd.mul continuousAt_const).div (hVp y).continuousAt
        (hVp0 y (hY₀pos.trans_le hy.1))).continuousWithinAt
    have hcmp := phase_sub_le_of_shift (v := vline) (W := fun y => V (p y))
      (W' := fun y => deriv V (p y) * (-I)) (θ := θ) hY hθc.continuousOn
      (fun y hy => hθv y (hY₀pos.le.trans hy.1)) hvc.continuousOn
      (fun y _ => hVp y) hcont (fun y _ => hclose' y)
    have hint : (∫ y in Y₀..Y, (deriv V (p y) * (-I) / V (p y)).im) =
        -∫ y in Y₀..Y, (logDeriv V (p y)).re := by
      rw [← intervalIntegral.integral_neg]
      refine intervalIntegral.integral_congr fun y _ => ?_
      simp only [logDeriv_apply]
      rw [mul_comm, mul_div_assoc]
      simp
    linarith
  set K₀ : ℝ := 2 * Real.pi + |C₀| with hK₀
  have hK₀0 : 0 ≤ K₀ := by rw [hK₀]; have := Real.pi_pos; positivity
  have hbound : ∀ y : ℝ, 0 ≤ y → θ y ≤ θ Y₀ + K₀ + C₁ * (y + Y₀ + 2 + D) ^ α := by
    intro y hy
    have hpow0 : 0 ≤ C₁ * (y + Y₀ + 2 + D) ^ α := mul_nonneg hC₁ (by positivity)
    rcases le_or_gt y Y₀ with h | h
    · linarith [hθmono y Y₀ hy h, le_abs_self C₀]
    · obtain ⟨Y, hTY, hYle, hY, hk⟩ := hgoodY y
      have h1 := hθmono y Y hy hTY
      have h2 := hphase Y hY _ hk
      have hYle' : Y + D ≤ y + Y₀ + 2 + D := by
        have : max y Y₀ = y := max_eq_left h.le
        linarith
      have h3 : (Y + D) ^ α ≤ (y + Y₀ + 2 + D) ^ α :=
        Real.rpow_le_rpow (by linarith [hY₀pos]) hYle' hα0
      have h4 := mul_le_mul_of_nonneg_left h3 hC₁
      linarith [le_abs_self C₀]
  /- the monotone twist theorem -/
  set Cm : ℝ → ℝ := fun x => θ (2 * max x 0) with hCm
  have hCmono : Monotone Cm := fun x x' hxx' =>
    hθmono _ _ (by positivity) (by have := max_le_max hxx' (le_refl (0 : ℝ)); linarith)
  have hCbd : ∃ α' K : ℝ, α' < 1 ∧ ∀ x : ℝ, 1 ≤ x → Cm x ≤ K * x ^ α' := by
    refine ⟨α, |θ Y₀| + K₀ + C₁ * (4 + Y₀ + D) ^ α, hα1, fun x hx => ?_⟩
    have hx0 : 0 ≤ x := by linarith
    have hb := hbound (2 * x) (by linarith)
    simp only [hCm, max_eq_left hx0]
    have hxα : 1 ≤ x ^ α := Real.one_le_rpow hx hα0
    have hlin : 2 * x + Y₀ + 2 + D ≤ (4 + Y₀ + D) * x := by nlinarith [hY₀pos, hD]
    have hp : (2 * x + Y₀ + 2 + D) ^ α ≤ (4 + Y₀ + D) ^ α * x ^ α := by
      rw [← Real.mul_rpow (by linarith [hY₀pos]) hx0]
      exact Real.rpow_le_rpow (by linarith [hY₀pos]) hlin hα0
    have hp' := mul_le_mul_of_nonneg_left hp hC₁
    have hθ0 : θ Y₀ ≤ |θ Y₀| * x ^ α := by
      calc θ Y₀ ≤ |θ Y₀| := le_abs_self _
        _ ≤ |θ Y₀| * x ^ α := le_mul_of_one_le_right (abs_nonneg _) hxα
    have hK : K₀ ≤ K₀ * x ^ α := le_mul_of_one_le_right hK₀0 hxα
    nlinarith
  refine abelian_twist_power_rigidity hsl hΦd hΦre hid hGc hGd hG2 hCmono hCbd (κ₀ := 1)
    (β₀ := 1) fun τ hτ => ?_
  have hx : 0 < -τ := by linarith
  have h := hlockc (-τ) hx
  rw [← lineS_neg_eq_vpt, neg_neg] at h
  rw [h]
  congr 3
  simp only [hCm, hθcdef, one_mul, max_eq_left hx.le]


/-- **A bounded quotient and a continuous lock force the true producer.** The case `α = 0` of
`slowQuotient_lock_trueProducer`: `G = s(s − 1)Γ_ℝ ζ A` with `A` bounded and continuous on
`Re s ≥ ½`, and a continuous bounded lock holomorphic on `½ < Re s < 3/2` that is uniformly close to
its small right shift. -/
theorem boundedQuotient_lock_trueProducer {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {A V : ℂ → ℂ} {WA CV : ℝ}
    (hAd : DifferentiableOn ℂ A {s : ℂ | 1 / 2 < s.re})
    (hAc : ContinuousOn A {s : ℂ | 1 / 2 ≤ s.re})
    (hAb : ∀ s : ℂ, 1 / 2 ≤ s.re → ‖A s‖ ≤ WA)
    (hGK : ∀ s : ℂ, 1 / 2 < s.re → s ≠ 1 →
      G s = s * (s - 1) * Gammaℝ s * (riemannZeta s * A s))
    (hVc : Continuous V) (hVd : DifferentiableOn ℂ V lockStrip) (hVb : ∀ s, ‖V s‖ ≤ CV)
    (hshift : ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 4 ∧ ∀ y : ℝ,
      ‖V (((1 / 2 + ε : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) - V (1 / 2 - (y : ℂ) * I)‖ ≤ 1 / 2)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = V (lineS τ) * G (lineS τ)) :
    (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧ RiemannHypothesis := by
  have hWA : 0 ≤ WA := (norm_nonneg _).trans (hAb 1 (by norm_num))
  refine slowQuotient_lock_trueProducer (WA := WA) (α := 0) hsl hΦd hΦre hid hGc hGd hG2 le_rfl
    one_pos hAd hAc (fun s hs => ?_) hGK hVc hVd hVb hshift hlock
  calc ‖A s‖ ≤ WA := hAb s hs
    _ ≤ WA * Real.exp (|s.im| ^ (0 : ℝ)) :=
        le_mul_of_one_le_right hWA (Real.one_le_exp (by positivity))

/-- **Almost-periodic locks force the true producer.** Let `G` be a Herglotz producer for the
weights `lam` with lower-line lock `G(1 − s) = V(s) G(s)`, `V(s) = Σ_j c_j u_j^{−(s−½)}`, with
`Σ_j |c_j| max(1, u_j^{−1}) K(u_j) < ∞` (`K(u) = √den(u) 8^{ω(den u)}` for rational `u`, `K = 1`
otherwise). Then `lam(n) = Λ(n)` for all `n ≥ 2`, and the Riemann hypothesis holds. -/
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
  have hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹ :=
    Summable.of_nonneg_of_le
      (fun j => mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))
      (fun j => le_mul_of_one_le_right
        (mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))
        (one_le_realDenWeight _)) hcw
  exact boundedQuotient_lock_trueProducer hsl hΦd hΦre hid hGc hGd hG2 hAd hAc hAb hGK
    (continuous_apLock hu hc)
    (fun z hz => (differentiableAt_apLock hu hc hz.1 hz.2).differentiableWithinAt)
    (norm_apLock_le hu hc) (exists_shift_apLock_close hu hc) hlock

end

end AbelianTwist

end RHTower
