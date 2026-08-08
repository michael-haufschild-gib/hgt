import GaloisForLFunctions.RHTower.Sieve.DirichletMeasureSixthMoment
import GaloisForLFunctions.RHTower.Sieve.LogPolyDirPoly

/-!
# Level sets and the product split on a symmetric range

Gallagher's identity integrates over a symmetric frequency range `|w| ≤ W`, so the large-values
estimates have to be available there.  Chebyshev applied to the symmetric mean value theorem gives

    V² · |{t ∈ [-T,T] : |F(t)| ≥ V}| ≤ 2(T + 4N(1+log N)) ∑_n |a_n|² ,

and running the same argument on the cube replaces `V²` by `V⁶`.  The threshold split of a product
then holds verbatim on `[-T,T]`.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- **The measure of a level set on a symmetric range, from any mean-square bound.**  Chebyshev uses
nothing but the bound. -/
theorem volume_largeValues_symm_le_of_bound (N : ℕ) (c : Fin N → ℂ) {T V B : ℝ}
    (hV : 0 ≤ V) (hA : (∫ t in Set.Icc (-T) T, ‖dirPoly N c t‖ ^ 2) ≤ B) :
    V ^ 2 * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N c t‖} ≤ B := by
  classical
  set g : ℝ → ℝ := fun t => ‖dirPoly N c t‖ ^ 2 with hg
  have hgc : Continuous g := ((continuous_dirPoly N c).norm).pow 2
  have hint : IntegrableOn g (Set.Icc (-T) T) := hgc.integrableOn_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (-T) T)] g :=
    Filter.Eventually.of_forall fun t => by positivity
  have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnn hint (V ^ 2)
  have hmeas : MeasurableSet {x : ℝ | V ^ 2 ≤ g x} :=
    measurableSet_le measurable_const hgc.measurable
  have hsub : {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N c t‖}
      ⊆ {x : ℝ | V ^ 2 ≤ g x} ∩ Set.Icc (-T) T := by
    rintro t ⟨ht, hle⟩
    exact ⟨by simpa [hg] using pow_le_pow_left₀ hV hle 2, ht⟩
  have hfin : volume ({x : ℝ | V ^ 2 ≤ g x} ∩ Set.Icc (-T) T) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono Set.inter_subset_right)
  have hmono : volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N c t‖}
      ≤ (volume.restrict (Set.Icc (-T) T)).real {x : ℝ | V ^ 2 ≤ g x} := by
    rw [measureReal_restrict_apply hmeas]
    exact measureReal_mono hsub hfin
  have hVsq : (0 : ℝ) ≤ V ^ 2 := by positivity
  calc V ^ 2 * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N c t‖}
      ≤ V ^ 2 * (volume.restrict (Set.Icc (-T) T)).real {x : ℝ | V ^ 2 ≤ g x} :=
        mul_le_mul_of_nonneg_left hmono hVsq
    _ ≤ ∫ t in Set.Icc (-T) T, g t := hmark
    _ ≤ B := hA

/-- **The measure of a level set on a symmetric range.**  The instance at the mean value theorem. -/
theorem volume_largeValues_symm_le (N : ℕ) (c : Fin N → ℂ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ 2 * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N c t‖}
      ≤ 2 * ((T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖c m‖ ^ 2) :=
  volume_largeValues_symm_le_of_bound N c hV (integral_Icc_normSq_dirPoly_symm_le N c hT)

/-- **The sixth-power level set on a symmetric range, from any mean-square bound for the cube.** -/
theorem volume_largeValues_sixth_symm_le_of_bound (N : ℕ) (a : Fin N → ℂ) {T V B : ℝ}
    (hV : 0 ≤ V)
    (hA : (∫ t in Set.Icc (-T) T, ‖dirPoly (N ^ 3) (convCube N a) t‖ ^ 2) ≤ B) :
    V ^ 6 * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N a t‖} ≤ B := by
  have hV3 : (0 : ℝ) ≤ V ^ 3 := by positivity
  have hbase := volume_largeValues_symm_le_of_bound (N ^ 3) (convCube N a) hV3 hA
  rw [largeValues_cube_setOf N a (Set.Icc (-T) T) hV] at hbase
  have hpow : (V ^ 3) ^ 2 = V ^ 6 := by ring
  rwa [hpow] at hbase

/-- **The measure of a level set on a symmetric range, sixth-power form.** -/
theorem volume_largeValues_sixth_symm_le (N : ℕ) (a : Fin N → ℂ) {T V D : ℝ} (hT : 0 ≤ T)
    (hV : 0 ≤ V) (hD : ∀ j : Fin (N ^ 3), ((cubeFibre N j).card : ℝ) ≤ D) :
    V ^ 6 * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly N a t‖}
      ≤ 2 * ((T + 4 * ((N ^ 3 : ℕ) : ℝ) * (1 + Real.log ((N ^ 3 : ℕ) : ℝ)))
          * (D * (∑ n : Fin N, ‖a n‖ ^ 2) ^ 3)) := by
  refine volume_largeValues_sixth_symm_le_of_bound N a hV ?_
  refine le_trans (integral_Icc_normSq_dirPoly_symm_le (N ^ 3) (convCube N a) hT) ?_
  have hlogN3 : (0 : ℝ) ≤ Real.log ((N ^ 3 : ℕ) : ℝ) := by
    rcases Nat.eq_zero_or_pos (N ^ 3) with h | h
    · simp [h]
    · have h1 : 1 ≤ N ^ 3 := h
      exact Real.log_nonneg (by exact_mod_cast h1)
  have hcast : (0 : ℝ) ≤ ((N ^ 3 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfactor : (0 : ℝ)
      ≤ T + 4 * ((N ^ 3 : ℕ) : ℝ) * (1 + Real.log ((N ^ 3 : ℕ) : ℝ)) := by nlinarith
  have hstep := mul_le_mul_of_nonneg_left (sum_normSq_convCube_le N a hD) hfactor
  linarith

/-- **The product split at a threshold, on a symmetric range.** -/
theorem integral_normSq_mul_split_symm (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    {T V Bf Bg : ℝ} (hBf : ∀ t : ℝ, ‖dirPoly N a t‖ ≤ Bf)
    (hBg : ∀ t : ℝ, ‖dirPoly M b t‖ ≤ Bg) :
    (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2)
      ≤ V ^ 2 * (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2)
        + Bf ^ 2 * Bg ^ 2
            * volume.real {t ∈ Set.Icc (-T) T | V ≤ ‖dirPoly M b t‖} := by
  classical
  set S : Set ℝ := Set.Icc (-T) T with hS
  set E : Set ℝ := {t : ℝ | V ≤ ‖dirPoly M b t‖} with hE
  set f : ℝ → ℝ := fun t => ‖dirPoly N a t‖ ^ 2 with hf
  set h : ℝ → ℝ := fun t => ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2 with hh
  have hcf : Continuous f := ((continuous_dirPoly N a).norm).pow 2
  have hcg : Continuous fun t : ℝ => ‖dirPoly M b t‖ := (continuous_dirPoly M b).norm
  have hch : Continuous h := hcf.mul (hcg.pow 2)
  have hEmeas : MeasurableSet E := measurableSet_le measurable_const hcg.measurable
  have hSmeas : MeasurableSet S := measurableSet_Icc
  have hhS : IntegrableOn h S := hch.integrableOn_Icc
  have hfS : IntegrableOn (fun t => V ^ 2 * f t) S := (hcf.const_mul (V ^ 2)).integrableOn_Icc
  have hsplit : (∫ t in S ∩ E, h t) + (∫ t in S \ E, h t) = ∫ t in S, h t :=
    MeasureTheory.integral_inter_add_sdiff hEmeas hhS
  have hsplit2 : (∫ t in S ∩ E, V ^ 2 * f t) + (∫ t in S \ E, V ^ 2 * f t)
      = ∫ t in S, V ^ 2 * f t :=
    MeasureTheory.integral_inter_add_sdiff hEmeas hfS
  have hBf0 : (0 : ℝ) ≤ Bf := le_trans (norm_nonneg _) (hBf 0)
  have hBg0 : (0 : ℝ) ≤ Bg := le_trans (norm_nonneg _) (hBg 0)
  have hbig : (∫ t in S ∩ E, h t) ≤ Bf ^ 2 * Bg ^ 2 * volume.real (S ∩ E) := by
    have hmeas : MeasurableSet (S ∩ E) := hSmeas.inter hEmeas
    have hint : IntegrableOn h (S ∩ E) := hhS.mono_set Set.inter_subset_left
    have hconst : IntegrableOn (fun _ : ℝ => Bf ^ 2 * Bg ^ 2) (S ∩ E) := by
      apply integrableOn_const
      · exact ne_of_lt (lt_of_le_of_lt (measure_mono Set.inter_subset_left) measure_Icc_lt_top)
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

end RHTower.Sieve
