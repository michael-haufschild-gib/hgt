import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesPrimeGammaWallXiTauColdBoundaryNoGo

/-!
# Prime/Gamma cold wall: all nonlinear Fredholm coefficients collapse

At the cold irregular boundary, normalized prime/Gamma Stokes mass condenses on prime `2`.
For every fixed determinant order at least two, the corresponding product mass therefore
condenses on the constant prime-2 tuple.  Its Fredholm matrix has repeated rows, so its
determinant vanishes exactly.  Hadamard's uniform bound then forces the full coefficient to zero.

This is coefficientwise and source-side.  It neither interchanges the cold limit with the infinite
Fredholm series nor uses completed-Xi target data.
-/

open Complex Filter Topology Set MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

namespace RHTower

noncomputable section

local instance : MeasurableSpace Nat.Primes := ⊤

private def coldPrimeTwoAllOrder : Nat.Primes := ⟨2, Nat.prime_two⟩

private def coldPrimeTwoTuple (n : ℕ) : Fin n → Nat.Primes :=
  fun _ => coldPrimeTwoAllOrder

private theorem primeFredholmIntegrand_coldPrimeTwoTuple
    {n : ℕ} (hn : 2 ≤ n) :
    routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n
        (coldPrimeTwoTuple n) = 0 := by
  unfold routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand
  apply Matrix.det_zero_of_row_eq
      (i := (⟨0, by omega⟩ : Fin n)) (j := (⟨1, by omega⟩ : Fin n))
  · intro h
    have hval : (0 : ℕ) = 1 := congrArg (fun k : Fin n => k.val) h
    omega
  · funext j
    rfl

private theorem primeTuplePMF_coldPrimeTwoTuple_real
    {d : ℝ} (hd : 0 < d) (n : ℕ) :
    (routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd n).toMeasure.real
        {coldPrimeTwoTuple n} =
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight d coldPrimeTwoAllOrder ^ n := by
  rw [measureReal_def,
    PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton _),
    routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF_toReal hd]
  simp [coldPrimeTwoTuple]

private theorem norm_integral_primeFredholmIntegrand_le_cold_complement
    {d : ℝ} (hd : 0 < d) {n : ℕ} (hn : 2 ≤ n) :
    ‖∫ a : Fin n → Nat.Primes,
        routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n a
        ∂(routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd n).toMeasure‖ ≤
      (Real.sqrt n) ^ n *
        (1 - routePPrimitiveGammaJuliaStokesWallNormalizedWeight d
          coldPrimeTwoAllOrder ^ n) := by
  let μ := (routePPrimitiveGammaJuliaStokesWallPrimeTuplePMF d hd n).toMeasure
  let q₂ := coldPrimeTwoTuple n
  let f := routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n
  let s : Set (Fin n → Nat.Primes) := {q₂}
  have hfun : f = sᶜ.indicator f := by
    funext a
    by_cases ha : a = q₂
    · subst a
      simp [f, s, q₂, primeFredholmIntegrand_coldPrimeTwoTuple hn]
    · simp [s, ha]
  rw [show (∫ a, routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand n a ∂μ) =
      ∫ a, f a ∂μ by rfl,
    hfun, integral_indicator (MeasurableSet.singleton q₂).compl]
  have hbound := norm_integral_le_of_norm_le_const
    (μ := μ.restrict {q₂}ᶜ)
    (Filter.Eventually.of_forall fun a =>
      norm_routePPrimitiveGammaJuliaStokesWallPrimeFredholmIntegrand_le n a)
  have hrestrict : (μ.restrict {q₂}ᶜ).real Set.univ = μ.real {q₂}ᶜ := by
    simp only [measureReal_def, Measure.restrict_apply_univ]
  rw [hrestrict, measureReal_compl (MeasurableSet.singleton q₂)] at hbound
  have huniv : μ.real Set.univ = 1 := by simp [μ]
  rw [huniv] at hbound
  simpa [q₂, μ, primeTuplePMF_coldPrimeTwoTuple_real hd n] using hbound

private theorem norm_primeGammaWallFredholmCoefficient_le_cold_complement
    {d : ℝ} (hd : 0 < d) {n : ℕ} (hn : 2 ≤ n) :
    ‖routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n‖ ≤
      ((Real.sqrt n) ^ n *
        (1 - routePPrimitiveGammaJuliaStokesWallNormalizedWeight d
          coldPrimeTwoAllOrder ^ n)) / (n.factorial : ℝ) := by
  rw [routePPrimitiveGammaJuliaStokesWallFredholmCoefficient,
    routePPrimitiveGammaJuliaStokesWallHalfLineLaw, if_pos hd,
    integral_routePPrimitiveGammaJuliaStokesWallFredholmIntegrand_eq_positive_pi_wallRaw hd n,
    integral_routePPrimitiveGammaJuliaStokesWallPositive_pi_wallRaw_eq_primeFredholmIntegrand hd n,
    norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right
    (norm_integral_primeFredholmIntegrand_le_cold_complement hd hn)
    (Nat.cast_nonneg n.factorial)

/-- Every fixed nonlinear Fredholm coefficient of the prime/Gamma Stokes wall vanishes at the
cold boundary: normalized mass condenses on the constant prime-2 tuple, whose determinant is zero. -/
theorem tendsto_routePPrimitiveGammaJuliaStokesPrimeGammaWallFredholmCoefficient_atTop_of_two_le
    {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun d : ℝ =>
      routePPrimitiveGammaJuliaStokesWallFredholmCoefficient
        (routePPrimitiveGammaJuliaStokesWallHalfLineLaw d) n)
      atTop (𝓝 0) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [sub_zero]
  have htwo : Tendsto (fun d : ℝ =>
      routePPrimitiveGammaJuliaStokesWallNormalizedWeight d coldPrimeTwoAllOrder)
      atTop (𝓝 1) := by
    convert tendsto_routePPrimitiveGammaJuliaStokesWallNormalizedWeight_two_atTop using 1
    funext d
    congr 2
  have hupper : Tendsto (fun d : ℝ =>
      ((Real.sqrt n) ^ n *
        (1 - routePPrimitiveGammaJuliaStokesWallNormalizedWeight d
          coldPrimeTwoAllOrder ^ n)) / (n.factorial : ℝ))
      atTop (𝓝 0) := by
    simpa using (((tendsto_const_nhds : Tendsto (fun _ : ℝ => (Real.sqrt n) ^ n)
        atTop (𝓝 ((Real.sqrt n) ^ n))).mul
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).sub
        (htwo.pow n))).div_const (n.factorial : ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0)) hupper
    (Filter.Eventually.of_forall fun d => norm_nonneg _)
    (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with d hd
      exact norm_primeGammaWallFredholmCoefficient_le_cold_complement hd hn)

end

end RHTower
