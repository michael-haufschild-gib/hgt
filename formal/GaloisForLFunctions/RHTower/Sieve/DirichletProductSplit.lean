import GaloisForLFunctions.RHTower.Sieve.DirichletMeasureSixthMoment

/-!
# Splitting a product by the size of one factor

For a product of two Dirichlet polynomials, cutting the frequency range at a threshold `V` for the
second factor gives

    ∫_0^T |P|²|Q|² ≤ V² ∫_0^T |P|² + (sup|P|)²(sup|Q|)² · |{t : |Q(t)| ≥ V}| .

Below the threshold the second factor is replaced by `V`; above it, both factors are replaced by
their trivial sizes and only the measure of the exceptional set survives.  Feeding the sixth-moment
bound into that measure is the mechanism by which a large-values estimate improves a mean square:
the exceptional set is small enough that the trivial bound on it costs nothing.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- **The product split at a threshold.** -/
theorem integral_normSq_mul_split (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    {T V Bf Bg : ℝ} (hBf : ∀ t : ℝ, ‖dirPoly N a t‖ ≤ Bf)
    (hBg : ∀ t : ℝ, ‖dirPoly M b t‖ ≤ Bg) :
    (∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2)
      ≤ V ^ 2 * (∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ^ 2)
        + Bf ^ 2 * Bg ^ 2
            * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly M b t‖} := by
  classical
  set S : Set ℝ := Set.Ioc (0 : ℝ) T with hS
  set E : Set ℝ := {t : ℝ | V ≤ ‖dirPoly M b t‖} with hE
  set f : ℝ → ℝ := fun t => ‖dirPoly N a t‖ ^ 2 with hf
  set h : ℝ → ℝ := fun t => ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2 with hh
  have hcf : Continuous f := ((continuous_dirPoly N a).norm).pow 2
  have hcg : Continuous fun t : ℝ => ‖dirPoly M b t‖ := (continuous_dirPoly M b).norm
  have hch : Continuous h := hcf.mul (hcg.pow 2)
  have hEmeas : MeasurableSet E := measurableSet_le measurable_const hcg.measurable
  have hSmeas : MeasurableSet S := measurableSet_Ioc
  have hhS : IntegrableOn h S := hch.integrableOn_Ioc
  have hfS : IntegrableOn (fun t => V ^ 2 * f t) S := (hcf.const_mul (V ^ 2)).integrableOn_Ioc
  -- the two pieces
  have hsplit : (∫ t in S ∩ E, h t) + (∫ t in S \ E, h t) = ∫ t in S, h t :=
    MeasureTheory.integral_inter_add_sdiff hEmeas hhS
  have hsplit2 : (∫ t in S ∩ E, V ^ 2 * f t) + (∫ t in S \ E, V ^ 2 * f t)
      = ∫ t in S, V ^ 2 * f t :=
    MeasureTheory.integral_inter_add_sdiff hEmeas hfS
  -- on the exceptional set both factors are replaced by their trivial sizes
  have hBf0 : (0 : ℝ) ≤ Bf := le_trans (norm_nonneg _) (hBf 0)
  have hBg0 : (0 : ℝ) ≤ Bg := le_trans (norm_nonneg _) (hBg 0)
  have hbig : (∫ t in S ∩ E, h t) ≤ Bf ^ 2 * Bg ^ 2 * volume.real (S ∩ E) := by
    have hmeas : MeasurableSet (S ∩ E) := hSmeas.inter hEmeas
    have hint : IntegrableOn h (S ∩ E) := hhS.mono_set Set.inter_subset_left
    have hconst : IntegrableOn (fun _ : ℝ => Bf ^ 2 * Bg ^ 2) (S ∩ E) := by
      apply integrableOn_const
      · exact ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_Ioc_lt_top)
      · finiteness
    have hle : ∀ t ∈ S ∩ E, h t ≤ Bf ^ 2 * Bg ^ 2 := by
      intro t _
      have h1 : ‖dirPoly N a t‖ ^ 2 ≤ Bf ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hBf t) 2
      have h2 : ‖dirPoly M b t‖ ^ 2 ≤ Bg ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hBg t) 2
      have h1n : (0 : ℝ) ≤ ‖dirPoly N a t‖ ^ 2 := by positivity
      have h2n : (0 : ℝ) ≤ ‖dirPoly M b t‖ ^ 2 := by positivity
      calc h t = ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2 := rfl
        _ ≤ Bf ^ 2 * Bg ^ 2 := by nlinarith
    have := MeasureTheory.setIntegral_mono_on hint hconst hmeas hle
    rwa [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm] at this
  -- below the threshold the second factor is at most `V`
  have hsmall : (∫ t in S \ E, h t) ≤ ∫ t in S \ E, V ^ 2 * f t := by
    have hmeas : MeasurableSet (S \ E) := hSmeas.diff hEmeas
    have hint : IntegrableOn h (S \ E) := hhS.mono_set Set.sdiff_subset
    have hint2 : IntegrableOn (fun t => V ^ 2 * f t) (S \ E) := hfS.mono_set Set.sdiff_subset
    refine MeasureTheory.setIntegral_mono_on hint hint2 hmeas ?_
    intro t ht
    have hlt : ‖dirPoly M b t‖ < V := by
      by_contra hcon
      exact ht.2 (not_lt.1 hcon)
    have h2 : ‖dirPoly M b t‖ ^ 2 ≤ V ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hlt.le 2
    have h1n : (0 : ℝ) ≤ ‖dirPoly N a t‖ ^ 2 := by positivity
    calc h t = ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2 := rfl
      _ ≤ ‖dirPoly N a t‖ ^ 2 * V ^ 2 := by nlinarith
      _ = V ^ 2 * f t := by rw [hf]; ring
  -- the discarded piece is nonnegative
  have hdrop : (0 : ℝ) ≤ ∫ t in S ∩ E, V ^ 2 * f t := by
    refine MeasureTheory.setIntegral_nonneg (hSmeas.inter hEmeas) fun t _ => ?_
    have : (0 : ℝ) ≤ f t := by rw [hf]; positivity
    nlinarith [sq_nonneg V]
  have hVf : (∫ t in S, V ^ 2 * f t) = V ^ 2 * ∫ t in S, f t := by
    rw [MeasureTheory.integral_const_mul]
  have hgoal : (∫ t in S, h t)
      ≤ V ^ 2 * (∫ t in S, f t) + Bf ^ 2 * Bg ^ 2 * volume.real (S ∩ E) := by
    linarith [hsplit, hbig, hsmall, hdrop, hsplit2, hVf]
  exact hgoal

/-- **The product split, with the sixth-moment bound on the exceptional set.** -/
theorem integral_normSq_mul_le_of_sixth (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    {T V Bf Bg A : ℝ} (hBf : ∀ t : ℝ, ‖dirPoly N a t‖ ≤ Bf)
    (hBg : ∀ t : ℝ, ‖dirPoly M b t‖ ≤ Bg)
    (hA : V ^ 6 * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly M b t‖} ≤ A) :
    V ^ 6 * (∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2)
      ≤ V ^ 8 * (∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ^ 2) + Bf ^ 2 * Bg ^ 2 * A := by
  have hsplit := integral_normSq_mul_split N M a b hBf hBg (V := V) (T := T)
  have hV6 : (0 : ℝ) ≤ V ^ 6 := by positivity
  have hK : (0 : ℝ) ≤ Bf ^ 2 * Bg ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsplit hV6
  have hexc := mul_le_mul_of_nonneg_left hA hK
  nlinarith [hmul, hexc]

/-- **The product split, fully instantiated.**  The exceptional set is measured by the sixth moment
of the second factor. -/
theorem integral_normSq_mul_le_sixth (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    {T V Bf Bg D : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V)
    (hBf : ∀ t : ℝ, ‖dirPoly N a t‖ ≤ Bf) (hBg : ∀ t : ℝ, ‖dirPoly M b t‖ ≤ Bg)
    (hD : ∀ j : Fin (M ^ 3), ((cubeFibre M j).card : ℝ) ≤ D) :
    V ^ 6 * (∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2)
      ≤ V ^ 8 * (∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ^ 2)
        + Bf ^ 2 * Bg ^ 2
            * ((T + 4 * ((M ^ 3 : ℕ) : ℝ) * (1 + Real.log ((M ^ 3 : ℕ) : ℝ)))
                * (D * (∑ n : Fin M, ‖b n‖ ^ 2) ^ 3)) :=
  integral_normSq_mul_le_of_sixth N M a b hBf hBg (volume_largeValues_sixth_le M b hT hV hD)

end RHTower.Sieve
