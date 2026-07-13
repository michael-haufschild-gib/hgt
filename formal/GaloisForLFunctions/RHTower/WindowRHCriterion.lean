import GaloisForLFunctions.RHTower.PrimePolarResidueCancellation

/-!
# The general windowed RH detection criterion

The window-independent core of the prime-window divisor tomography, shared by
`prime-polar-moving-tent-divisor-tomography` (tent window `A_L(s-1)²`) and
`bounded-variation-prime-window-divisor-tomography` (sharp window `A_L(s-1)`).

For any window Mellin multiplier `W`, the windowed prime observable is `W(s)·(-ζ'/ζ)(s-½)`.  A zeta
zero `ρ ≠ 1` shifts (via `neg_logDeriv_zeta_shifted_residue`) into a simple pole of `-ζ'/ζ(s-½)` at
`s = ρ+½` with residue `-m(ρ)`; if `W` is continuous and nonzero there, the observable inherits a
genuine singularity (`windowObservable_no_limit`).  Hence regularity of the observable on `Re s > 1`
forces `ζ` to have no zeros with `Re > ½` — the RH criterion `RH_of_windowObservable_regular`.  Because
`rectangularWindowAmplitude_ne_zero` supplies the nonvanishing of `A_L` on the open right half-plane,
both the sharp window (`RH_of_sharpWindow_regular`) and the tent window (`W = -2·A_L(s-1)²`) are
instances.
-/

open Filter Topology

namespace RHTower


theorem neg_logDeriv_zeta_shifted_residue {ρ : ℂ} (hρ1 : ρ ≠ 1) (hζρ : riemannZeta ρ = 0) :
    ∃ m : ℕ, 1 ≤ m ∧ Tendsto (fun s => (s - (ρ + 1 / 2)) *
        (-deriv riemannZeta (s - 1 / 2) / riemannZeta (s - 1 / 2)))
      (𝓝[≠] (ρ + 1 / 2)) (𝓝 (-(m : ℂ))) := by
  obtain ⟨m, hm1, hres⟩ := neg_logDeriv_zeta_zero_residue hρ1 hζρ
  refine ⟨m, hm1, ?_⟩
  have hshift : Tendsto (fun s : ℂ => s - 1 / 2) (𝓝[≠] (ρ + 1 / 2)) (𝓝[≠] ρ) := by
    have := sub_const_punctured_tendsto (ρ + 1 / 2) (1 / 2)
    rwa [show ρ + 1 / 2 - 1 / 2 = ρ by ring] at this
  exact (hres.comp hshift).congr (fun s => by simp only [Function.comp_apply]; ring_nf)

/-- The general windowed prime observable `W(s)·(-ζ'/ζ)(s-½)`. -/
noncomputable def windowObservable (W : ℂ → ℂ) (s : ℂ) : ℂ :=
  W s * (-deriv riemannZeta (s - 1 / 2) / riemannZeta (s - 1 / 2))

/-- **General off-critical detection.**  For any window multiplier `W` continuous and nonzero at `ρ+½`,
a zeta zero `ρ` with `Re ρ > ½` makes `windowObservable W` have a genuine singularity at `s = ρ+½`. -/
theorem windowObservable_no_limit (W : ℂ → ℂ) {ρ : ℂ}
    (hρ1 : ρ ≠ 1) (hζρ : riemannZeta ρ = 0)
    (hWcont : ContinuousAt W (ρ + 1 / 2)) (hWne : W (ρ + 1 / 2) ≠ 0) :
    ¬ ∃ M : ℂ, Tendsto (windowObservable W) (𝓝[≠] (ρ + 1 / 2)) (𝓝 M) := by
  rintro ⟨M, hM⟩
  obtain ⟨m, hm1, hres⟩ := neg_logDeriv_zeta_shifted_residue hρ1 hζρ
  have ha : Tendsto (fun s : ℂ => s - (ρ + 1 / 2)) (𝓝[≠] (ρ + 1 / 2)) (𝓝 0) :=
    ((continuous_id.sub continuous_const).tendsto' (ρ + 1 / 2) 0 (by simp)).mono_left
      nhdsWithin_le_nhds
  have hWlim : Tendsto W (𝓝[≠] (ρ + 1 / 2)) (𝓝 (W (ρ + 1 / 2))) :=
    hWcont.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun s => (s - (ρ + 1 / 2)) * windowObservable W s)
      (𝓝[≠] (ρ + 1 / 2)) (𝓝 (W (ρ + 1 / 2) * -(m : ℂ))) :=
    (hWlim.mul hres).congr (fun s => by simp only [windowObservable]; ring)
  have h0 := ha.mul hM
  rw [zero_mul] at h0
  have heq := tendsto_nhds_unique h1 h0
  have hmne : (-(m : ℂ)) ≠ 0 := by
    simp only [neg_ne_zero, Nat.cast_ne_zero]; exact Nat.one_le_iff_ne_zero.mp hm1
  exact (mul_ne_zero hWne hmne) heq

/-- **General window RH criterion.**  For any *continuous* window multiplier `W` that does not vanish
at `ρ+½` for any candidate off-critical zero `ρ` (`Re ρ > ½`), regularity of `windowObservable W` on
`Re s > 1` implies `ζ` has no zeros with `Re > ½` — i.e. RH.  Both the tent (`W = -2·A_L(s-1)²`) and the
sharp bounded-variation window (`W = A_L(s-1)`) are instances, since `rectangularWindowAmplitude_ne_zero`
supplies the nonvanishing. -/
theorem RH_of_windowObservable_regular (W : ℂ → ℂ) (hWcont : Continuous W)
    (hWne : ∀ ρ : ℂ, 1 / 2 < ρ.re → W (ρ + 1 / 2) ≠ 0)
    (hreg : ∀ a : ℂ, 1 < a.re → ∃ M : ℂ, Tendsto (windowObservable W) (𝓝[≠] a) (𝓝 M)) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ ≠ 1 → ρ.re ≤ 1 / 2 := by
  intro ρ hζρ hρ1
  by_contra h
  have hgt : 1 / 2 < ρ.re := not_le.mp h
  have hre : 1 < (ρ + 1 / 2).re := by rw [Complex.add_re]; simp; linarith
  exact windowObservable_no_limit W hρ1 hζρ hWcont.continuousAt (hWne ρ hgt) (hreg (ρ + 1 / 2) hre)

/-- **The sharp bounded-variation-window RH criterion** — the instance for
`bounded-variation-prime-window-divisor-tomography` with window multiplier `A_L(s-1)`. -/
theorem RH_of_sharpWindow_regular (L : ℝ) (hL : 0 < L)
    (hreg : ∀ a : ℂ, 1 < a.re →
      ∃ M : ℂ, Tendsto (windowObservable (fun s => rectangularWindowAmplitude L (s - 1)))
        (𝓝[≠] a) (𝓝 M)) :
    ∀ ρ : ℂ, riemannZeta ρ = 0 → ρ ≠ 1 → ρ.re ≤ 1 / 2 := by
  refine RH_of_windowObservable_regular _
    ((rectangularWindowAmplitude_differentiable L).continuous.comp (continuous_id.sub continuous_const))
    (fun ρ hρ => rectangularWindowAmplitude_ne_zero hL ?_) hreg
  have e2 : ((1 / 2 : ℂ)).re = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]
  have hre : ((ρ + 1 / 2 : ℂ) - 1).re = ρ.re - 1 / 2 := by
    rw [Complex.sub_re, Complex.add_re, Complex.one_re, e2]; ring
  simp only [id_eq]; rw [hre]; linarith
