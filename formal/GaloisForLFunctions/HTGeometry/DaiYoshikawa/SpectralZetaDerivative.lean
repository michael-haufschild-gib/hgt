import GaloisForLFunctions.HTGeometry.DaiYoshikawa.MellinSplit
import Mathlib.NumberTheory.Harmonic.GammaDeriv

/-!
# `ζ'(0)` from the regularized heat trace

After the Mellin integral of `Θ(t) − h` is split at `t = 1` and the two-term expansion is subtracted
from the head, one has, for `Re s > 1`,

```text
Γ(s) ζ(s) = H(s) + T(s) + a₀/(s−1) + (a₁−h)/s ,
```

with `H` the head Mellin integral of `Θ(t) − a₀/t − a₁` (holomorphic on `Re s > −1`) and `T` the
tail Mellin integral of `Θ(t) − h` (entire).  Writing `Γ(s) = Γ(s+1)/s` turns this into a formula
that is manifestly holomorphic at `s = 0`:

```text
ζ(s) = ( s (H(s) + T(s) + a₀/(s−1)) + (a₁ − h) ) / Γ(s+1) .
```

Differentiating at the origin gives

```text
ζ(0) = a₁ − h ,        ζ'(0) = H(0) + T(0) − a₀ + (a₁ − h) γ ,
```

`H(0) = ∫_0^1 (Θ(t) − a₀/t − a₁) dt/t` and `T(0) = ∫_1^∞ (Θ(t) − h) dt/t` being exactly the two
integrals of formula (3.3) in Dai–Yoshikawa, *Degeneration of Riemann surfaces and small eigenvalues
of the Laplacian* (arXiv:2509.06151v2).  The constant term produced by the computation is
`−a₀ + (a₁ − h) γ`; the paper's (3.3) prints `−Γ'(1)(a₀ − h) = (a₀ − h) γ` instead.  Nothing in the
paper depends on it, since only differences of two torsions with identical `a₀, a₁, h` are used and
the constant cancels there.
-/

open Set Filter Real Complex Topology

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

/-- The continued spectral zeta function, written so as to be manifestly holomorphic at `0`. -/
noncomputable def zetaCont (g₁ g₂ : ℝ → ℂ) (a₀ a₁ h : ℂ) (s : ℂ) : ℂ :=
  (s * (mellinHead g₁ s + mellinTail g₂ s + a₀ / (s - 1)) + (a₁ - h)) / Complex.Gamma (s + 1)

variable {g₁ g₂ : ℝ → ℂ} {a₀ a₁ h : ℂ}

/-- `ζ(0) = a₁ − h`. -/
theorem zetaCont_zero : zetaCont g₁ g₂ a₀ a₁ h 0 = a₁ - h := by
  rw [zetaCont]
  simp [Complex.Gamma_one]

/-- **The functional form on the half-plane of convergence.**

`Γ(s) ζ(s) = H(s) + T(s) + a₀/(s−1) + (a₁−h)/s` wherever `s ≠ 0` and `Γ(s+1) ≠ 0`. -/
theorem gamma_mul_zetaCont {s : ℂ} (hs : s ≠ 0) (hΓ : Complex.Gamma (s + 1) ≠ 0) :
    Complex.Gamma s * zetaCont g₁ g₂ a₀ a₁ h s
      = mellinHead g₁ s + mellinTail g₂ s + a₀ / (s - 1) + (a₁ - h) / s := by
  have hgam : Complex.Gamma (s + 1) = s * Complex.Gamma s := Complex.Gamma_add_one s hs
  have hGs : Complex.Gamma s = Complex.Gamma (s + 1) / s := by
    rw [hgam]
    field_simp
  rw [zetaCont, hGs]
  field_simp

/-- **The derivative at the origin.**

`ζ'(0) = H(0) + T(0) − a₀ + (a₁ − h) γ`. -/
theorem hasDerivAt_zetaCont_zero
    (hhead : DifferentiableAt ℂ (mellinHead g₁) 0)
    (htail : DifferentiableAt ℂ (mellinTail g₂) 0) :
    HasDerivAt (zetaCont g₁ g₂ a₀ a₁ h)
      (mellinHead g₁ 0 + mellinTail g₂ 0 - a₀
        + (a₁ - h) * (Real.eulerMascheroniConstant : ℂ)) 0 := by
  set G : ℂ → ℂ := fun s => mellinHead g₁ s + mellinTail g₂ s + a₀ / (s - 1) with hGdef
  have hpole : DifferentiableAt ℂ (fun s : ℂ => a₀ / (s - 1)) 0 := by
    refine DifferentiableAt.div (differentiableAt_const a₀) (differentiableAt_id.sub_const 1) ?_
    norm_num
  have hGdiff : DifferentiableAt ℂ G 0 := (hhead.add htail).add hpole
  obtain ⟨g', hg'⟩ : ∃ g' : ℂ, HasDerivAt G g' 0 := ⟨deriv G 0, hGdiff.hasDerivAt⟩
  have hG0 : G 0 = mellinHead g₁ 0 + mellinTail g₂ 0 - a₀ := by
    rw [hGdef]
    simp
    ring
  have hN : HasDerivAt (fun s : ℂ => s * G s + (a₁ - h)) (G 0) 0 := by
    have h1 : HasDerivAt (fun s : ℂ => s * G s) (1 * G 0 + 0 * g') 0 :=
      (hasDerivAt_id (0 : ℂ)).mul hg'
    have h2 := h1.add_const (a₁ - h)
    simpa using h2
  have hΓshift : HasDerivAt (fun s : ℂ => Complex.Gamma (s + 1))
      (-(Real.eulerMascheroniConstant : ℂ)) 0 := by
    have h1 : HasDerivAt (fun s : ℂ => s + 1) 1 0 := (hasDerivAt_id (0 : ℂ)).add_const 1
    have hg1 : HasDerivAt Complex.Gamma (-(Real.eulerMascheroniConstant : ℂ)) ((0 : ℂ) + 1) := by
      simpa using Complex.hasDerivAt_Gamma_one
    have h2 := hg1.comp (0 : ℂ) h1
    simpa [Function.comp_def] using h2
  have hΓ1 : Complex.Gamma ((0 : ℂ) + 1) = 1 := by
    norm_num [Complex.Gamma_one]
  have hΓne : Complex.Gamma ((0 : ℂ) + 1) ≠ 0 := by rw [hΓ1]; exact one_ne_zero
  have hdiv := hN.div hΓshift hΓne
  have hval : ((G 0) * Complex.Gamma ((0 : ℂ) + 1)
      - ((0 : ℂ) * G 0 + (a₁ - h)) * (-(Real.eulerMascheroniConstant : ℂ)))
      / Complex.Gamma ((0 : ℂ) + 1) ^ 2
      = mellinHead g₁ 0 + mellinTail g₂ 0 - a₀
        + (a₁ - h) * (Real.eulerMascheroniConstant : ℂ) := by
    rw [hΓ1, hG0]
    ring
  rw [hval] at hdiv
  exact hdiv

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
