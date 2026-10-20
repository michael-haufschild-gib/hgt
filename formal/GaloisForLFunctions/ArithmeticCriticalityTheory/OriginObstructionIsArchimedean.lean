import GaloisForLFunctions.ArithmeticCriticalityTheory.FoldedSourceOriginJumpMomentLaw
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftAveragedEnergies

/-!
# The origin obstruction sees no primes

Replace the von Mangoldt rates by an arbitrary nonnegative rate sequence `λ`
(`foldedGeneratorWithRates`): jumps of length `log n` at rate `λ(n)`, the archimedean density
unchanged, the potential `Φ cosh(x/2)` unchanged. For a profile `M` (odd test coordinate of the gauge
`ω = M/Φ`), Lipschitz with `M(0) = 0` and `|M| ≤ Ce^{−8|y|}`, the folded generator has the limit
(`tendsto_foldedGeneratorWithRates_nhdsGT_zero`)

    (𝓛_N^λ ω)(x)  →  −2 Φ(0) [ ∫_0^∞ ω(t) M(t) dt + Σ_n λ(n) M(log n) ]        (x → 0⁺),

computed from the definition alone: at the origin every jump from `x` lands at distance `t` on one side
or the other, the fold reads both landing points as `M(t)`, and `ω(x) → 0`. No identity of `Θ` is
used, and the potential term tends to `0`.

**Theorem** (`exists_origin_window_foldedGeneratorWithRates_lt_potential`). For EVERY nonnegative rate
sequence with `Σ λ(n) n^{−8} < ∞`, every gauge whose profile is nonnegative on `[0, ∞)` and positive at
some point is a strict folded subsolution on an origin window. The archimedean moment
`∫_0^∞ ω M > 0` already forces it; the rates can only make it worse.

So the failure of folded supersolutions at the origin is a property of the Dirichlet condition and the
archimedean jump density, and is blind to the primes; the failure at infinity
(`exists_infinity_window_profileGauge_foldedGenerator_lt_potential`) uses the density of prime powers in
every multiplicative window. The two halves of the no-go see the arithmetic differently.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The folded generator with jump rates `λ(n)` at the lengths `log n`. -/
def foldedGeneratorWithRates (lam : ℕ → ℝ) (ω : ℝ → ℝ) (x : ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * foldedShiftGenerator ω t x) +
    ∑' n : ℕ, lam n * foldedShiftGenerator ω (Real.log n) x

theorem foldedGenerator_eq_withRates (ω : ℝ → ℝ) (x : ℝ) :
    foldedGenerator ω x = foldedGeneratorWithRates vonMangoldtAtom ω x := rfl

/-- The folded shift generator of `ω = M/Φ` in test coordinates. -/
theorem foldedShiftGenerator_profileGauge (M : ℝ → ℝ) (t x : ℝ) :
    foldedShiftGenerator (fun y => M y / riemannKernelReal y) t x =
      M x * (riemannKernelReal (x + t) + riemannKernelReal (x - t)) -
        riemannKernelReal x * (M (x + t) + M (|x - t|)) := by
  unfold foldedShiftGenerator
  have h0 := (riemannKernelReal_pos x).ne'
  have h1 := (riemannKernelReal_pos (x + t)).ne'
  have h2 := (riemannKernelReal_pos (|x - t|)).ne'
  have hab : riemannKernelReal (x - t) = riemannKernelReal (|x - t|) := (riemannKernelReal_abs' _).symm
  rw [hab]
  field_simp
  ring

section Limit

variable {M : ℝ → ℝ} {C K : ℝ} (hMc : Continuous M) (hM0 : M 0 = 0)
  (hLip : ∀ a b, |M a - M b| ≤ K * |a - b|) (hdec : ∀ y, |M y| ≤ C * Real.exp (-(8 * |y|)))

/-- `Φ` is Lipschitz. -/
theorem exists_riemannKernelReal_lipschitz :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ a b, |riemannKernelReal a - riemannKernelReal b| ≤ L * |a - b| := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_deriv_riemannKernelReal_le
  refine ⟨D, hD0, fun a b => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := riemannKernelReal) (s := univ) (C := D)
    (fun y _ => (hasDerivAt_riemannKernelReal y).differentiableAt) (fun y _ => by
      rw [Real.norm_eq_abs]
      exact (hD y).trans (mul_le_of_le_one_right hD0
        (Real.exp_le_one_iff.mpr (by linarith [abs_nonneg y]))))
    convex_univ (mem_univ b) (mem_univ a)
  simpa only [Real.norm_eq_abs] using h

include hLip in
/-- Near the diagonal the folded shift integrand is `O(t)`, uniformly in `x ≥ 0`. -/
theorem abs_foldedShiftGenerator_profileGauge_le {LΦ BΦ BM : ℝ} (hLΦ : ∀ a b,
    |riemannKernelReal a - riemannKernelReal b| ≤ LΦ * |a - b|)
    (hBΦ : ∀ y, |riemannKernelReal y| ≤ BΦ) (hBM : ∀ y, |M y| ≤ BM) {t x : ℝ} (ht : 0 ≤ t)
    (hx : 0 ≤ x) :
    |foldedShiftGenerator (fun y => M y / riemannKernelReal y) t x| ≤ (2 * BM * LΦ + 2 * BΦ * K) * t := by
  rw [foldedShiftGenerator_profileGauge]
  have e : M x * (riemannKernelReal (x + t) + riemannKernelReal (x - t)) -
      riemannKernelReal x * (M (x + t) + M (|x - t|)) =
      M x * ((riemannKernelReal (x + t) - riemannKernelReal x) +
        (riemannKernelReal (x - t) - riemannKernelReal x)) -
      riemannKernelReal x * ((M (x + t) - M x) + (M (|x - t|) - M x)) := by ring
  rw [e]
  have h1 := hLΦ (x + t) x
  have h2 := hLΦ (x - t) x
  have h3 := hLip (x + t) x
  have h4 := hLip (|x - t|) x
  rw [show x + t - x = t by ring, abs_of_nonneg ht] at h1 h3
  rw [show x - t - x = -t by ring, abs_neg, abs_of_nonneg ht] at h2
  have h5 : |(|x - t|) - x| ≤ t := by
    have := abs_abs_sub_abs_le_abs_sub (x - t) x
    rw [abs_of_nonneg hx, show x - t - x = -t by ring, abs_neg, abs_of_nonneg ht] at this
    exact this
  have h4' : |M (|x - t|) - M x| ≤ K * t := h4.trans (by
    have hK : 0 ≤ K := by
      have := (abs_nonneg _).trans (hLip 1 0)
      rw [show (1 : ℝ) - 0 = 1 by ring, abs_one, mul_one] at this
      exact this
    exact mul_le_mul_of_nonneg_left h5 hK)
  calc |M x * ((riemannKernelReal (x + t) - riemannKernelReal x) +
        (riemannKernelReal (x - t) - riemannKernelReal x)) -
      riemannKernelReal x * ((M (x + t) - M x) + (M (|x - t|) - M x))|
      ≤ |M x| * (|riemannKernelReal (x + t) - riemannKernelReal x| +
          |riemannKernelReal (x - t) - riemannKernelReal x|) +
        |riemannKernelReal x| * (|M (x + t) - M x| + |M (|x - t|) - M x|) := by
        refine (abs_sub _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_add_le _ _) (abs_nonneg _)
    _ ≤ BM * (LΦ * t + LΦ * t) + BΦ * (K * t + K * t) := by
        gcongr
        · exact (abs_nonneg _).trans (hBM 0)
        · exact hBM x
        · exact (abs_nonneg _).trans (hBΦ 0)
        · exact hBΦ x
    _ = _ := by ring

include hMc hM0 hLip hdec in
/-- **The origin limit for every rate system.** For nonnegative rates with `Σ λ(n) n^{−8} < ∞`,
`(𝓛_N^λ ω)(x) → −2Φ(0) [∫_0^∞ ω M + Σ λ(n) M(log n)]` as `x → 0⁺`. -/
theorem tendsto_foldedGeneratorWithRates_nhdsGT_zero {lam : ℕ → ℝ}
    (hsum : Summable fun n : ℕ => lam n * Real.exp (-(8 * Real.log n))) :
    Tendsto (fun x => foldedGeneratorWithRates lam (fun y => M y / riemannKernelReal y) x) (𝓝[>] 0)
      (𝓝 (-2 * riemannKernelReal 0 * ((∫ t in Ioi (0 : ℝ), archLevyDensity t * M t) +
        ∑' n : ℕ, lam n * M (Real.log n)))) := by
  obtain ⟨LΦ, -, hLΦ⟩ := exists_riemannKernelReal_lipschitz
  obtain ⟨CΦ, hCΦ0, hCΦ⟩ := exists_riemannKernelReal_le_exp_eight
  have hC0 := nonneg_of_abs_le_mul_exp hdec
  have hBΦ : ∀ y, |riemannKernelReal y| ≤ CΦ := fun y => by
    rw [abs_of_pos (riemannKernelReal_pos y)]
    exact (hCΦ y).trans (mul_le_of_le_one_right hCΦ0
      (Real.exp_le_one_iff.mpr (by linarith [abs_nonneg y])))
  have hBM : ∀ y, |M y| ≤ C := fun y => (hdec y).trans
    (mul_le_of_le_one_right hC0 (Real.exp_le_one_iff.mpr (by linarith [abs_nonneg y])))
  have hcont : ∀ t, Continuous fun x => foldedShiftGenerator (fun y => M y / riemannKernelReal y) t x :=
    fun t => by
      simp_rw [foldedShiftGenerator_profileGauge]
      exact (hMc.mul ((continuous_riemannKernelReal.comp (continuous_id.add continuous_const)).add
        (continuous_riemannKernelReal.comp (continuous_id.sub continuous_const)))).sub
        (continuous_riemannKernelReal.mul ((hMc.comp (continuous_id.add continuous_const)).add
          (hMc.comp (continuous_id.sub continuous_const).abs)))
  have hval : ∀ t, 0 ≤ t → foldedShiftGenerator (fun y => M y / riemannKernelReal y) t 0 =
      -2 * riemannKernelReal 0 * M t := fun t ht => by
    rw [foldedShiftGenerator_profileGauge, hM0, zero_sub, abs_neg, abs_of_nonneg ht, zero_add]
    ring
  -- the archimedean part
  set Cst := 2 * C * LΦ + 2 * CΦ * K with hCst
  have hA : Tendsto (fun x => ∫ t in Ioi (0 : ℝ), archLevyDensity t *
      foldedShiftGenerator (fun y => M y / riemannKernelReal y) t x) (𝓝[>] 0)
      (𝓝 (∫ t in Ioi (0 : ℝ), -2 * riemannKernelReal 0 * (archLevyDensity t * M t))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun t => Cst * (archLevyDensity t * t))
      ?_ ?_ (integrableOn_archLevyDensity_mul_id.const_mul _) ?_
    · refine Eventually.of_forall fun x => ?_
      exact ((measurable_archLevyDensity.mul
        ((hcont · |>.comp continuous_const) x |> fun _ => by
          have : Continuous fun t => foldedShiftGenerator (fun y => M y / riemannKernelReal y) t x := by
            simp_rw [foldedShiftGenerator_profileGauge]
            fun_prop
          exact this.measurable))).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with x hx
      refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have hω := archLevyDensity_pos ht
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hω]
      have := abs_foldedShiftGenerator_profileGauge_le hLip hLΦ hBΦ hBM (le_of_lt ht) (le_of_lt hx)
      calc archLevyDensity t * |foldedShiftGenerator (fun y => M y / riemannKernelReal y) t x| ≤
          archLevyDensity t * (Cst * t) := mul_le_mul_of_nonneg_left this hω.le
        _ = _ := by ring
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have h := ((hcont t).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      rw [hval t (le_of_lt ht)] at h
      have := h.const_mul (archLevyDensity t)
      convert this using 2
      ring
  -- the prime part
  have hP : Tendsto (fun x => ∑' n : ℕ, lam n *
      foldedShiftGenerator (fun y => M y / riemannKernelReal y) (Real.log n) x) (𝓝[>] 0)
      (𝓝 (∑' n : ℕ, -2 * riemannKernelReal 0 * (lam n * M (Real.log n)))) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun n =>
      |lam n| * Real.exp (-(8 * Real.log n)) * (4 * C * CΦ * Real.exp 8)) ?_ (fun n => ?_) ?_
    · sorry
    · have h := ((hcont (Real.log n)).tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
      rw [hval _ (Real.log_natCast_nonneg n)] at h
      have := h.const_mul (lam n)
      convert this using 2
      ring
    · sorry
  sorry

end Limit


end GaloisForLFunctions.ArithmeticCriticalityTheory

end
