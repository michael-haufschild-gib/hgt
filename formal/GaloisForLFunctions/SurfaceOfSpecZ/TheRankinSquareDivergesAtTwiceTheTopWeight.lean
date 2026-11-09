import GaloisForLFunctions.SurfaceOfSpecZ.ThePrimesSampleEveryTopLayer

/-!
# The Rankin square diverges at twice the top weight

Deligne's purity argument rests on the series of `F ⊗ F̄`, whose coefficients `|tr|²` are nonnegative
without any hypothesis: by Landau's theorem its abscissa is a real pole, which sits at twice the top
weight. Over `ℤ` the coefficients of the Rankin square of the prime-power traces,
`Λ(n) (2 Re S(log n))²`, are nonnegative for every configuration, and:

**Theorem** (`not_summable_rankinSquare_of_max`). Let `Z` be a tempered configuration and `ρ₀` a
zero of maximal real part, off the line. Then
`Σ_n Λ(n) (2 Re S_Z(log n))² n^{−2 Re ρ₀} = ∞`; for `σ > 2 Re ρ₀` the series converges, since
`|2 Re S_Z(log n)| ≤ E n^{Re ρ₀ − ½}`. So the abscissa of the Rankin square is `2 max Re ρ`.

**Proof.** At `σ = 1 + 2b + t`, `b = Re ρ₀ − ½`, the series is the mean of `F² = (2 Re S e^{−bu})²` at
`1 + t`, whose ratio to `Σ Λ(n) n^{−1−t}` tends to `Σ_{Re z = b} |e_z|² > 0`
(`tendsto_normTraceSqMean`, `re_tsum_diagWeight_pos`), while `Σ Λ(n) n^{−1−t} → ∞`. Convergence at
`1 + 2b` would bound the series for every `t > 0`.

Off the line the spline sees `ρ₀` (`e_{ρ₀−½} ≠ 0`); on the line `B̂` may vanish at the height of `ρ₀`.
-/

open Complex Filter Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
open ArithmeticFunction

/-- **The Rankin square diverges at twice the top weight.** -/
theorem not_summable_rankinSquare_of_max (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier) (hoff : 1 / 2 < ρ₀.re)
    (hmax : ∀ ρ ∈ Z.carrier, ρ.re ≤ ρ₀.re) :
    ¬ Summable fun j : ℕ => Λ (j + 1) *
      (2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re) ^ 2 *
        ((j : ℝ) + 1) ^ (-(2 * ρ₀.re)) := by
  intro hsum
  have hb3 := contDiff_boxSpline (r := 1) one_pos 2
  have hbc := hasCompactSupport_of_support_subset_abs (boxSpline_support (r := 1) one_pos 3)
  set b : ℝ := ρ₀.re - 1 / 2 with hbdef
  have hb0 : 0 ≤ b := by rw [hbdef]; linarith
  have htop : TopDepth Z b := by
    intro z hz
    rcases mem_of_evenCoeff_ne_zero hz with h | h
    · have h1 := hmax _ h
      simp at h1
      rw [hbdef]; linarith
    · have h1 := hmax _ h
      simp at h1
      rw [hbdef]; linarith
  have hz₀ : evenCoeff Z (boxSpline 1 3) (ρ₀ - 1 / 2) ≠ 0 :=
    evenCoeff_sub_half_ne_zero_of_conj_symm Z hb3.continuous hbc
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ₀
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))
  have hA := re_tsum_diagWeight_pos hZ htop hz₀ (by simp [hbdef])
  set A := (∑' q, diagWeight Z b q).re with hAdef
  set M := ∑' j : ℕ, Λ (j + 1) * (2 * (lagStructure Z (boxSpline 1 3) (Real.log (j + 1))).re) ^ 2 *
    ((j : ℝ) + 1) ^ (-(2 * ρ₀.re)) with hMdef
  -- the mean of `F²` at `σ > 1` is bounded by the convergent series
  have hbound : ∀ σ : ℝ, 1 < σ → normTraceSqMean Z b σ ≤ M := by
    intro σ hσ
    refine Summable.tsum_le_tsum (fun j => ?_) (summable_normTraceSqMean hZ htop hσ) hsum
    have hj0 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hj1 : (1 : ℝ) ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have hexp : Real.exp (-(b * Real.log ((j : ℝ) + 1))) = ((j : ℝ) + 1) ^ (-b) := by
      rw [Real.rpow_def_of_pos hj0]; ring_nf
    have hsq : normTrace Z b (Real.log ((j : ℝ) + 1)) ^ 2 =
        (2 * (lagStructure Z (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re) ^ 2 *
          ((j : ℝ) + 1) ^ (-(2 * b)) := by
      rw [normTrace, hexp, mul_pow, ← Real.rpow_natCast (((j : ℝ) + 1) ^ (-b)) 2,
        ← Real.rpow_mul hj0.le]
      congr 2; push_cast; ring
    rw [hsq]
    have hpow : ((j : ℝ) + 1) ^ (-(2 * b)) * ((j : ℝ) + 1) ^ (-σ) ≤
        ((j : ℝ) + 1) ^ (-(2 * ρ₀.re)) := by
      rw [← Real.rpow_add hj0]
      exact Real.rpow_le_rpow_of_exponent_le hj1 (by rw [hbdef]; linarith)
    have hΛ := vonMangoldt_nonneg (n := j + 1)
    have h2 : 0 ≤ (2 * (lagStructure Z (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re) ^ 2 :=
      sq_nonneg _
    calc Λ (j + 1) * ((2 * (lagStructure Z (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re) ^ 2 *
          ((j : ℝ) + 1) ^ (-(2 * b))) * ((j : ℝ) + 1) ^ (-σ)
        = Λ (j + 1) * (2 * (lagStructure Z (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re) ^ 2 *
            (((j : ℝ) + 1) ^ (-(2 * b)) * ((j : ℝ) + 1) ^ (-σ)) := by ring
      _ ≤ Λ (j + 1) * (2 * (lagStructure Z (boxSpline 1 3) (Real.log ((j : ℝ) + 1))).re) ^ 2 *
            ((j : ℝ) + 1) ^ (-(2 * ρ₀.re)) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg hΛ h2)
  -- but its ratio to `Σ Λ(n) n^{−σ} → ∞` has a positive limit
  have hlim := tendsto_normTraceSqMean hZ htop
  have hev : ∀ᶠ σ in 𝓝[>] (1 : ℝ), A / 2 < normTraceSqMean Z b σ / vmSum σ :=
    hlim.eventually (lt_mem_nhds (by rw [← hAdef]; linarith))
  have hbig : ∀ᶠ σ in 𝓝[>] (1 : ℝ), 2 * (|M| + 1) / A < vmSum σ :=
    tendsto_vmSum_atTop.eventually (eventually_gt_atTop _)
  obtain ⟨σ, hσ1, hσ2, hσ3⟩ := (hev.and (hbig.and self_mem_nhdsWithin)).exists
  have hσ : 1 < σ := hσ3
  have hV := vmSum_pos hσ
  rw [lt_div_iff₀ hV] at hσ1
  rw [div_lt_iff₀ hA] at hσ2
  have := hbound σ hσ
  nlinarith [le_abs_self M]

end GaloisForLFunctions.SurfaceOfSpecZ
