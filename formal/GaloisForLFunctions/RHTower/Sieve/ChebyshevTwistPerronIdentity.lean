import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistPerron
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegTwistShift
import GaloisForLFunctions.RHTower.Sieve.ChebyshevIntegrandSplit

/-!
# The twisted Chebyshev Perron identity, with the pole isolated

The Perron integrand of the twisted von Mangoldt function is `-ζ'/ζ(s + iτ)·W(s)`.  Its only
singularity is the simple pole of `-ζ'/ζ` at `s + iτ = 1`, that is at the point `1 - iτ`, and the
cutoff's transform is evaluated at `s`, not at `s + iτ`.  Splitting the pole term at that base point
writes the integrand as

```text
(-ζ'/ζ)(s+iτ)·W(s)
  =  dslope W (1-iτ) s  +  W(1-iτ)·(s + iτ - 1)⁻¹  +  zetaLogDerivReg(s+iτ)·W(s) ,
```

valid off the pole and away from the zeros of `ζ`.  The first summand is holomorphic wherever `W`
is, the pole included; the third is holomorphic on any zero-free rectangle
(`ZetaLogDerivRegTwistShift`); and the whole residue is carried by the middle term, whose
coefficient `W(1-iτ)` is the twisted main term — of size `N/(1+|τ|)`, the `π(x)/(1+|t|)` of the
classical twisted prime sum estimate.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The pole term splits at an arbitrary base point.**  Off the base point, `f(s)/(s-a)` is the
divided difference plus the pure pole `f(a)/(s-a)`. -/
theorem inv_sub_mul_eq_dslope_add (f : ℂ → ℂ) {a s : ℂ} (h : s ≠ a) :
    (s - a)⁻¹ * f s = dslope f a s + f a * (s - a)⁻¹ := by
  have hne : s - a ≠ 0 := sub_ne_zero.2 h
  have hkey : (s - a) * dslope f a s = f s - f a := by
    simpa [smul_eq_mul] using sub_smul_dslope f a s
  have hfs : f s = f a + (s - a) * dslope f a s := by linear_combination -hkey
  rw [hfs, mul_add, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  ring

/-- The pole of the twisted integrand. -/
noncomputable def twistPole (τ : ℝ) : ℂ := 1 - (τ : ℂ) * Complex.I

theorem sub_twistPole (τ : ℝ) (s : ℂ) : s - twistPole τ = s + (τ : ℂ) * Complex.I - 1 := by
  rw [twistPole]
  ring

/-- **The twisted Chebyshev integrand, fully split.**  The whole residue sits in the pure pole at
`s = 1 - iτ`; the divided difference and the regular part are holomorphic there. -/
theorem chebyshev_twist_integrand_split_full {N H : ℝ} (τ : ℝ) {s : ℂ}
    (hs : s + (τ : ℂ) * Complex.I ≠ 1)
    (hz : riemannZeta (s + (τ : ℂ) * Complex.I) ≠ 0) :
    (-logDeriv riemannZeta (s + (τ : ℂ) * Complex.I))
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s
      = dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ) s
        + mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
            * (s + (τ : ℂ) * Complex.I - 1)⁻¹
        + zetaLogDerivReg (s + (τ : ℂ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s := by
  have hsa : s ≠ twistPole τ := by
    intro hcon
    apply hs
    rw [hcon, twistPole]
    ring
  have hsplit := neg_logDeriv_riemannZeta_eq_of_ne_zero hs hz
  have hpole := inv_sub_mul_eq_dslope_add
    (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) hsa
  rw [sub_twistPole] at hpole
  rw [hsplit, add_mul, hpole]

/-- **The twisted integrand on the Perron line.**  Right of the abscissa `ζ` has no zeros and the
translated point is never the pole, so the splitting holds on the whole line. -/
theorem chebyshev_twist_integrand_split_line {N H : ℝ} (τ : ℝ) {d y : ℝ} (hd : 1 < d) :
    (-logDeriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I)
      = dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
            ((d : ℂ) + (y : ℝ) * Complex.I)
        + mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
            * ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
        + zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I) := by
  have hre : ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I).re = d := by simp
  have hs : ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have hz : riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hre]; exact hd.le)
  exact chebyshev_twist_integrand_split_full τ hs hz

/-- **The twisted Chebyshev Perron identity, split.**  The main term is the pure pole at
`s = 1 - iτ`, whose coefficient is the cutoff's transform there; everything else is holomorphic
across the abscissa on a zero-free rectangle. -/
theorem tsum_vonMangoldtTwist_smoothWeight_eq_split_integral (τ : ℝ) {N H : ℝ} (hN : 0 < N)
    (hH : 0 < H) {d : ℝ} (hd : 1 < d) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        vonMangoldtTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, (dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
              ((d : ℂ) + (y : ℝ) * Complex.I)
            + mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
                * ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
            + zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
                * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                    ((d : ℂ) + (y : ℝ) * Complex.I)) := by
  rw [tsum_vonMangoldtTwist_smoothWeight_eq_integral τ hN hH hd]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show (∑' n : ℕ, vonMangoldtTwist τ n * (n : ℂ) ^ (-((d : ℂ) + (y : ℝ) * Complex.I))) *
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I) = _
  have hre : (1 : ℝ) < ((d : ℂ) + (y : ℝ) * Complex.I).re := by simpa using hd
  rw [tsum_vonMangoldtTwist_cpow_eq_logDeriv τ hre]
  exact chebyshev_twist_integrand_split_line τ hd

end RHTower.Sieve
