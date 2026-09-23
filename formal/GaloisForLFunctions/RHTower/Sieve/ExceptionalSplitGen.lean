import GaloisForLFunctions.RHTower.Sieve.DirichletExceptionalSplit

/-!
# The exceptional-set split for a general pair of continuous factors

`Sieve/DirichletExceptionalSplit` states the split of exposé §4 for two `dirPoly`s.  The ladder of
`Sieve/JointLadderProduct` is written in the Gallagher variable, so the split is restated here for
an arbitrary pair of continuous complex functions:

```text
   ∫_{|w|≤W} ‖F‖²‖G‖²  ≤  V²·∫_{|w|≤W}‖G‖²  +  (sup‖F‖)²·∫_{E}‖G‖² ,
   E = {w : |w| ≤ W, ‖F(w)‖ ≥ V} .
```

Off `E` the first factor has cancellation; on `E` it is bounded by its supremum and the second
factor is *integrated* — which is what Halász–Montgomery supplies.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- **The exceptional-set split, threshold on the first factor.** -/
theorem integral_normSq_mul_split_exceptional_gen {F G : ℝ → ℂ} (hF : Continuous F)
    (hG : Continuous G) {W V Bf : ℝ} (hBf : ∀ w : ℝ, ‖F w‖ ≤ Bf) :
    (∫ w in Set.Icc (-W) W, ‖F w‖ ^ (2 : ℕ) * ‖G w‖ ^ (2 : ℕ))
      ≤ V ^ (2 : ℕ) * (∫ w in Set.Icc (-W) W, ‖G w‖ ^ (2 : ℕ))
        + Bf ^ (2 : ℕ) * ∫ w in Set.Icc (-W) W ∩ {w : ℝ | V ≤ ‖F w‖}, ‖G w‖ ^ (2 : ℕ) := by
  classical
  set S : Set ℝ := Set.Icc (-W) W with hS
  set E : Set ℝ := {w : ℝ | V ≤ ‖F w‖} with hE
  set f : ℝ → ℝ := fun w => ‖G w‖ ^ (2 : ℕ) with hf
  set g : ℝ → ℝ := fun w => ‖F w‖ ^ (2 : ℕ) * ‖G w‖ ^ (2 : ℕ) with hg
  have hcF : Continuous fun w : ℝ => ‖F w‖ := hF.norm
  have hcf : Continuous f := (hG.norm).pow 2
  have hcg : Continuous g := (hcF.pow 2).mul hcf
  have hEmeas : MeasurableSet E := measurableSet_le measurable_const hcF.measurable
  have hSmeas : MeasurableSet S := measurableSet_Icc
  have hgS : IntegrableOn g S := hcg.integrableOn_Icc
  have hfS : IntegrableOn (fun w => V ^ (2 : ℕ) * f w) S := (hcf.const_mul (V ^ (2 : ℕ))).integrableOn_Icc
  have hbfS : IntegrableOn (fun w => Bf ^ (2 : ℕ) * f w) S := (hcf.const_mul (Bf ^ (2 : ℕ))).integrableOn_Icc
  have hsplit : (∫ w in S ∩ E, g w) + (∫ w in S \ E, g w) = ∫ w in S, g w :=
    MeasureTheory.integral_inter_add_sdiff hEmeas hgS
  have hsplit2 : (∫ w in S ∩ E, V ^ (2 : ℕ) * f w) + (∫ w in S \ E, V ^ (2 : ℕ) * f w)
      = ∫ w in S, V ^ (2 : ℕ) * f w :=
    MeasureTheory.integral_inter_add_sdiff hEmeas hfS
  have hbig : (∫ w in S ∩ E, g w) ≤ Bf ^ (2 : ℕ) * ∫ w in S ∩ E, f w := by
    have hmeas : MeasurableSet (S ∩ E) := hSmeas.inter hEmeas
    have hint : IntegrableOn g (S ∩ E) := hgS.mono_set Set.inter_subset_left
    have hint2 : IntegrableOn (fun w => Bf ^ (2 : ℕ) * f w) (S ∩ E) :=
      hbfS.mono_set Set.inter_subset_left
    have hle : ∀ w ∈ S ∩ E, g w ≤ Bf ^ (2 : ℕ) * f w := by
      intro w _
      have h1 : ‖F w‖ ^ (2 : ℕ) ≤ Bf ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) (hBf w) 2
      have h2n : (0 : ℝ) ≤ f w := by rw [hf]; positivity
      calc g w = ‖F w‖ ^ (2 : ℕ) * f w := rfl
        _ ≤ Bf ^ (2 : ℕ) * f w := by nlinarith
    have hmono := MeasureTheory.setIntegral_mono_on hint hint2 hmeas hle
    rwa [MeasureTheory.integral_const_mul] at hmono
  have hsmall : (∫ w in S \ E, g w) ≤ ∫ w in S \ E, V ^ (2 : ℕ) * f w := by
    have hmeas : MeasurableSet (S \ E) := hSmeas.diff hEmeas
    have hint : IntegrableOn g (S \ E) := hgS.mono_set Set.sdiff_subset
    have hint2 : IntegrableOn (fun w => V ^ (2 : ℕ) * f w) (S \ E) := hfS.mono_set Set.sdiff_subset
    refine MeasureTheory.setIntegral_mono_on hint hint2 hmeas ?_
    intro w hw
    have hlt : ‖F w‖ < V := by
      by_contra hcon
      exact hw.2 (not_lt.1 hcon)
    have h1 : ‖F w‖ ^ (2 : ℕ) ≤ V ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) hlt.le 2
    have h2n : (0 : ℝ) ≤ f w := by rw [hf]; positivity
    calc g w = ‖F w‖ ^ (2 : ℕ) * f w := rfl
      _ ≤ V ^ (2 : ℕ) * f w := by nlinarith
  have hdrop : (0 : ℝ) ≤ ∫ w in S ∩ E, V ^ (2 : ℕ) * f w := by
    refine MeasureTheory.setIntegral_nonneg (hSmeas.inter hEmeas) fun w _ => ?_
    have hfn : (0 : ℝ) ≤ f w := by rw [hf]; positivity
    nlinarith [sq_nonneg V]
  have hVf : (∫ w in S, V ^ (2 : ℕ) * f w) = V ^ (2 : ℕ) * ∫ w in S, f w :=
    MeasureTheory.integral_const_mul _ _
  linarith [hsplit, hbig, hsmall, hdrop, hsplit2, hVf]

end

end RHTower.Sieve
