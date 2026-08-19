import GaloisForLFunctions.RHTower.Sieve.DirichletSymmSplit

/-!
# The exceptional-set split of Soundararajan's exposé §4

The threshold in §4 sits on the **short prime** polynomial, and on the exceptional set the second
factor is not bounded by its supremum but integrated — Halász–Montgomery supplies
`∫_{E}‖G‖²` directly.  The corpus's `Sieve/DirichletSymmSplit.integral_normSq_mul_split_symm` puts
the threshold on the second factor and pays `sup‖G‖²·|E|`, which is a different and, in §4, useless
shape.  This is the variant §4 needs:

```text
   ∫_{|t|≤T} ‖F‖²‖G‖²  ≤  V²∫_{|t|≤T}‖G‖²  +  (sup‖F‖)²·∫_{E}‖G‖² ,
   E = {t : |t| ≤ T, ‖F(t)‖ ≥ V} .
```
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- **The exceptional-set split with the threshold on the first factor.** -/
theorem integral_normSq_mul_split_exceptional (N M : ℕ) (a : Fin N → ℂ) (b : Fin M → ℂ)
    {T V Bf : ℝ} (hBf : ∀ t : ℝ, ‖dirPoly N a t‖ ≤ Bf) :
    (∫ t in Set.Icc (-T) T, ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2)
      ≤ V ^ 2 * (∫ t in Set.Icc (-T) T, ‖dirPoly M b t‖ ^ 2)
        + Bf ^ 2
            * ∫ t in Set.Icc (-T) T ∩ {t : ℝ | V ≤ ‖dirPoly N a t‖},
                ‖dirPoly M b t‖ ^ 2 := by
  classical
  set S : Set ℝ := Set.Icc (-T) T with hS
  set E : Set ℝ := {t : ℝ | V ≤ ‖dirPoly N a t‖} with hE
  set f : ℝ → ℝ := fun t => ‖dirPoly M b t‖ ^ 2 with hf
  set h : ℝ → ℝ := fun t => ‖dirPoly N a t‖ ^ 2 * ‖dirPoly M b t‖ ^ 2 with hh
  have hcF : Continuous fun t : ℝ => ‖dirPoly N a t‖ := (continuous_dirPoly N a).norm
  have hcf : Continuous f := ((continuous_dirPoly M b).norm).pow 2
  have hch : Continuous h := (hcF.pow 2).mul hcf
  have hEmeas : MeasurableSet E := measurableSet_le measurable_const hcF.measurable
  have hSmeas : MeasurableSet S := measurableSet_Icc
  have hhS : IntegrableOn h S := hch.integrableOn_Icc
  have hfS : IntegrableOn (fun t => V ^ 2 * f t) S := (hcf.const_mul (V ^ 2)).integrableOn_Icc
  have hbfS : IntegrableOn (fun t => Bf ^ 2 * f t) S := (hcf.const_mul (Bf ^ 2)).integrableOn_Icc
  have hsplit : (∫ t in S ∩ E, h t) + (∫ t in S \ E, h t) = ∫ t in S, h t :=
    MeasureTheory.integral_inter_add_sdiff hEmeas hhS
  have hsplit2 : (∫ t in S ∩ E, V ^ 2 * f t) + (∫ t in S \ E, V ^ 2 * f t)
      = ∫ t in S, V ^ 2 * f t :=
    MeasureTheory.integral_inter_add_sdiff hEmeas hfS
  have hBf0 : (0 : ℝ) ≤ Bf := le_trans (norm_nonneg _) (hBf 0)
  -- on the exceptional set the first factor is bounded by its supremum
  have hbig : (∫ t in S ∩ E, h t) ≤ Bf ^ 2 * ∫ t in S ∩ E, f t := by
    have hmeas : MeasurableSet (S ∩ E) := hSmeas.inter hEmeas
    have hint : IntegrableOn h (S ∩ E) := hhS.mono_set Set.inter_subset_left
    have hint2 : IntegrableOn (fun t => Bf ^ 2 * f t) (S ∩ E) :=
      hbfS.mono_set Set.inter_subset_left
    have hle : ∀ t ∈ S ∩ E, h t ≤ Bf ^ 2 * f t := by
      intro t _
      have h1 : ‖dirPoly N a t‖ ^ 2 ≤ Bf ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hBf t) 2
      have h2n : (0 : ℝ) ≤ f t := by rw [hf]; positivity
      calc h t = ‖dirPoly N a t‖ ^ 2 * f t := rfl
        _ ≤ Bf ^ 2 * f t := by nlinarith
    have hmono := MeasureTheory.setIntegral_mono_on hint hint2 hmeas hle
    rwa [MeasureTheory.integral_const_mul] at hmono
  -- off the exceptional set the first factor has cancellation
  have hsmall : (∫ t in S \ E, h t) ≤ ∫ t in S \ E, V ^ 2 * f t := by
    have hmeas : MeasurableSet (S \ E) := hSmeas.diff hEmeas
    have hint : IntegrableOn h (S \ E) := hhS.mono_set Set.sdiff_subset
    have hint2 : IntegrableOn (fun t => V ^ 2 * f t) (S \ E) := hfS.mono_set Set.sdiff_subset
    refine MeasureTheory.setIntegral_mono_on hint hint2 hmeas ?_
    intro t ht
    have hlt : ‖dirPoly N a t‖ < V := by
      by_contra hcon
      exact ht.2 (not_lt.1 hcon)
    have h1 : ‖dirPoly N a t‖ ^ 2 ≤ V ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hlt.le 2
    have h2n : (0 : ℝ) ≤ f t := by rw [hf]; positivity
    calc h t = ‖dirPoly N a t‖ ^ 2 * f t := rfl
      _ ≤ V ^ 2 * f t := by nlinarith
  have hdrop : (0 : ℝ) ≤ ∫ t in S ∩ E, V ^ 2 * f t := by
    refine MeasureTheory.setIntegral_nonneg (hSmeas.inter hEmeas) fun t _ => ?_
    have hfn : (0 : ℝ) ≤ f t := by rw [hf]; positivity
    nlinarith [sq_nonneg V]
  have hVf : (∫ t in S, V ^ 2 * f t) = V ^ 2 * ∫ t in S, f t :=
    MeasureTheory.integral_const_mul _ _
  linarith [hsplit, hbig, hsmall, hdrop, hsplit2, hVf]

end RHTower.Sieve
