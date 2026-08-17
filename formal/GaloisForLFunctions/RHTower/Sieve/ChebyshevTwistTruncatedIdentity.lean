import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistMainTerm
import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistPoleShift
import GaloisForLFunctions.RHTower.Sieve.ChebyshevTruncatedSplit

/-!
# The truncated twisted Chebyshev identity

Assembling the twisted Perron identity, the truncation, the three-piece split and the explicit
twisted main term:

```text
2π ∑ₙ Λ(n) n^{-iτ} w(n)
  =  (tail beyond height T)
   +  ∫_{-T}^{T} dslope W (1-iτ)
   +  W(1-iτ) · ( arctan((T+τ)/(d-1)) - arctan((τ-T)/(d-1))
                   - (i/2)·log( ((d-1)²+(T+τ)²) / ((d-1)²+(τ-T)²) ) )
   +  ∫_{-T}^{T} zetaLogDerivReg(· + iτ) · W .
```

The third summand is the main term, explicit and estimate-free; the first is what a truncation
lemma bounds; and the second and fourth are the two pieces that the contour shift moves to the left
edge, where the Route-T zero-free region and the bound for `ζ'/ζ` on that abscissa take over.

As in the untwisted case the split is applied only *after* truncation: the pure pole decays like
`1/|y|` on the line and is not integrable there, even though the full integrand is.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- The Perron line stays away from the twist pole: their real parts differ. -/
theorem line_ne_twistPole {d y τ : ℝ} (hd : 1 < d) :
    ((d : ℂ) + (y : ℝ) * Complex.I) ≠ twistPole τ := by
  intro h
  have hre : ((d : ℂ) + (y : ℝ) * Complex.I).re = d := by simp
  rw [h, twistPole_re] at hre
  linarith

theorem sub_twistPole_ne_zero_line {d y τ : ℝ} (hd : 1 < d) :
    (d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1 ≠ 0 := by
  rw [← sub_twistPole]
  exact sub_ne_zero.2 (line_ne_twistPole hd)

/-- On the Perron line the divided difference at the twist pole is an explicit quotient. -/
theorem dslope_mellin_twist_line {N H : ℝ} {d y τ : ℝ} (hd : 1 < d) :
    dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
        ((d : ℂ) + (y : ℝ) * Complex.I)
      = (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I)
          - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ))
        / ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1) := by
  rw [dslope_of_ne _ (line_ne_twistPole (τ := τ) hd), slope_def_field, sub_twistPole]

/-- **The truncated twisted Chebyshev integral splits into three.**  As in the untwisted case the
splitting is legitimate only after truncation: the pure pole is not integrable on the whole line. -/
theorem integral_truncated_chebyshev_twist_split {N H : ℝ} (hH : 0 < H) {d T τ : ℝ} (hd : 1 < d) :
    (∫ y : ℝ in (-T)..T,
        (dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
              ((d : ℂ) + (y : ℝ) * Complex.I)
          + mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
              * ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
          + zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((d : ℂ) + (y : ℝ) * Complex.I)))
      = (∫ y : ℝ in (-T)..T,
            dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
              ((d : ℂ) + (y : ℝ) * Complex.I))
        + (∫ y : ℝ in (-T)..T,
            mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
              * ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹)
        + (∫ y : ℝ in (-T)..T,
            zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((d : ℂ) + (y : ℝ) * Complex.I)) := by
  have hd0 : (0 : ℝ) < d := by linarith
  have hWcont : Continuous fun y : ℝ =>
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I) :=
    continuous_mellin_smoothWeight_line hH hd0
  have hlin : Continuous fun y : ℝ =>
      (d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1 := by fun_prop
  have hinv : Continuous fun y : ℝ =>
      ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹ :=
    hlin.inv₀ fun y => sub_twistPole_ne_zero_line hd
  have h1 : Continuous fun y : ℝ =>
      dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
        ((d : ℂ) + (y : ℝ) * Complex.I) := by
    have hfun : (fun y : ℝ =>
        dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
          ((d : ℂ) + (y : ℝ) * Complex.I))
        = fun y : ℝ => (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)
            - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ))
          * ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹ := by
      funext y
      rw [dslope_mellin_twist_line hd, div_eq_mul_inv]
    rw [hfun]
    exact (hWcont.sub continuous_const).mul hinv
  have h2 : Continuous fun y : ℝ =>
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
        * ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹ :=
    continuous_const.mul hinv
  have h3 : Continuous fun y : ℝ =>
      zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I) := by
    have hreg : Continuous fun y : ℝ =>
        zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) := by
      refine continuous_iff_continuousAt.2 fun y => ?_
      have hre : ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I).re = d := by simp
      have hne : ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) ≠ 1 := by
        intro h
        rw [h] at hre
        simp at hre
        linarith
      have hz : riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) ≠ 0 :=
        riemannZeta_ne_zero_of_one_le_re (by rw [hre]; linarith)
      have hin : Continuous fun u : ℝ =>
          ((d : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I) := by fun_prop
      exact ContinuousAt.comp (g := zetaLogDerivReg)
        (f := fun u : ℝ => ((d : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
        ((differentiableAt_zetaLogDerivReg
          ((zetaResidueUnit_ne_zero_iff hne).2 hz)).continuousAt) hin.continuousAt
    exact hreg.mul hWcont
  have hA := intervalIntegral.integral_add (a := -T) (b := T) (μ := volume)
    (f := fun y : ℝ =>
      dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
        ((d : ℂ) + (y : ℝ) * Complex.I))
    (g := fun y : ℝ => mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
      * ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹)
    (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)
  have hB := intervalIntegral.integral_add (a := -T) (b := T) (μ := volume)
    (f := fun y : ℝ =>
      dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
          ((d : ℂ) + (y : ℝ) * Complex.I)
        + mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
          * ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹)
    (g := fun y : ℝ => zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
      * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
        ((d : ℂ) + (y : ℝ) * Complex.I))
    ((h1.add h2).intervalIntegrable _ _) (h3.intervalIntegrable _ _)
  rw [hB, hA]

/-- **The truncated twisted Chebyshev identity.**  The tail beyond height `T`, the divided
difference, the explicit twisted main term, and the regular part. -/
theorem tsum_vonMangoldtTwist_truncated_identity (τ : ℝ) {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {d T : ℝ} (hd : 1 < d) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        vonMangoldtTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ((∫ y : ℝ, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I))
          - ∫ y : ℝ in (-T)..T, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I))
        + (∫ y : ℝ in (-T)..T,
            dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
              ((d : ℂ) + (y : ℝ) * Complex.I))
        + mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
            * ((((Real.arctan ((T + τ) / (d - 1))
                  - Real.arctan ((-T + τ) / (d - 1)) : ℝ)) : ℂ)
              - ((((Real.log ((d - 1) ^ 2 + (T + τ) ^ 2)
                    - Real.log ((d - 1) ^ 2 + (-T + τ) ^ 2)) / 2 : ℝ)) : ℂ) * Complex.I)
        + (∫ y : ℝ in (-T)..T,
            zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((d : ℂ) + (y : ℝ) * Complex.I)) := by
  have hperron := tsum_vonMangoldtTwist_smoothWeight_eq_logDeriv_integral τ hN hH hd
  have hshift : ∀ y : ℝ, (d : ℂ) + ((y + τ : ℝ)) * Complex.I
      = (d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I := by
    intro y
    push_cast
    ring
  have hsplitline : (∫ y : ℝ in (-T)..T,
        (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I))
      = ∫ y : ℝ in (-T)..T,
          (dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
                ((d : ℂ) + (y : ℝ) * Complex.I)
            + mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
                * ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
            + zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
                * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                    ((d : ℂ) + (y : ℝ) * Complex.I)) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [hshift y]
    exact chebyshev_twist_integrand_split_line τ hd
  rw [hperron, hsplitline, integral_truncated_chebyshev_twist_split hH hd,
    integral_twist_pole_term_line hd]
  ring

end RHTower.Sieve
