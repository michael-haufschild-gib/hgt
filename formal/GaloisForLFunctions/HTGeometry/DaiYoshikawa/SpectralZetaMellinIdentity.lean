import GaloisForLFunctions.HTGeometry.DaiYoshikawa.SpectralZetaDerivative
import GaloisForLFunctions.HTGeometry.DaiYoshikawa.MellinHeadExpansion

/-!
# The continued zeta function agrees with the Mellin transform of the heat trace

`zetaCont` was defined by a formula that is manifestly holomorphic at the origin.  This file closes
the loop: on the half-plane `Re s > 1`, where the Mellin transform of `Θ(t) − h` converges,

```text
Γ(s) · zetaCont(s) = ∫_0^∞ (Θ(t) − h) t^{s−1} dt .
```

Combined with `SpectralZetaMellinSum`, which identifies that Mellin transform with `Γ(s) Σ λ^{−s}`,
this says that `zetaCont` really is the analytic continuation of the spectral zeta function; and
`SpectralZetaDerivative` then evaluates its derivative at the origin.
-/

open MeasureTheory Set Filter Real Complex Topology

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- **`Γ(s) ζ(s)` is the Mellin transform of the regularized heat trace.** -/
theorem gamma_mul_zetaCont_eq_mellin {Θ : ℝ → ℂ} {a₀ a₁ h : ℂ} {s : ℂ} (hs : 1 < s.re)
    (hs0 : s ≠ 0) (hΓ : Complex.Gamma (s + 1) ≠ 0)
    (hhead : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (Θ t - h)) (Ioc (0 : ℝ) 1) volume)
    (htail : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) • (Θ t - h)) (Ioi (1 : ℝ)) volume)
    (hreg : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • (Θ t - a₀ * (t : ℂ) ^ (-1 : ℂ) - a₁))
      (Ioc (0 : ℝ) 1) volume) :
    Complex.Gamma s
        * zetaCont (fun t => Θ t - a₀ * (t : ℂ) ^ (-1 : ℂ) - a₁) (fun t => Θ t - h) a₀ a₁ h s
      = mellin (fun t => Θ t - h) s := by
  have hregshift : IntegrableOn
      (fun t : ℝ => (t : ℂ) ^ (s - 1) • ((Θ t - h) - a₀ * (t : ℂ) ^ (-1 : ℂ) - (a₁ - h)))
      (Ioc (0 : ℝ) 1) volume := by
    refine hreg.congr_fun (fun t _ => ?_) measurableSet_Ioc
    show (t : ℂ) ^ (s - 1) • (Θ t - a₀ * (t : ℂ) ^ (-1 : ℂ) - a₁)
      = (t : ℂ) ^ (s - 1) • ((Θ t - h) - a₀ * (t : ℂ) ^ (-1 : ℂ) - (a₁ - h))
    congr 1
    ring
  have hexp := mellinHead_eq_regularized_add (g := fun t => Θ t - h) (a₀ := a₀) (a₁ := a₁ - h)
    hs hregshift
  have hcongr : mellinHead (fun t => (Θ t - h) - a₀ * (t : ℂ) ^ (-1 : ℂ) - (a₁ - h)) s
      = mellinHead (fun t => Θ t - a₀ * (t : ℂ) ^ (-1 : ℂ) - a₁) s := by
    refine congrArg (fun f => mellinHead f s) ?_
    funext t
    ring
  rw [hcongr] at hexp
  rw [gamma_mul_zetaCont hs0 hΓ, mellin_eq_mellinHead_add_mellinTail hhead htail, hexp]
  ring

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
