/-
# Böttcher tower — the per-level single-valued Böttcher branch

The connected-case Böttcher coordinate `φ_c` is assembled from **per-level branches**: on the
fundamental domain `levelDomain c N = {z : f_c^[N] z ∈ escapeOpen ∩ slitPlane}` the closed-form
`phiLevel c N = exp(2⁻ᴺ · bottcherLog ∘ f_c^[N])` is a single-valued analytic branch of `φ_c`, with
the Böttcher modulus `|phiLevel| = exp(G_c)` and the defining root relation
`phiLevel^{2ᴺ} = φ_c ∘ f_c^[N]`. These are the units the connected single-valued `φ_c` is glued from
(`exists_greenConjugate_glue`); this file packages them.

New file (hRigid connected lane); consumes `CoverConstruction`.
-/
import GaloisForLFunctions.Bottcher.CoverConstruction

open Complex Set

namespace Bottcher

/-- The `N`-th fundamental domain: points whose `N`-th iterate lands in `escapeOpen ∩ slitPlane`,
where the closed-form branch logarithm is single-valued analytic. -/
def levelDomain (c : ℂ) (N : ℕ) : Set ℂ :=
  {z | (quadratic c)^[N] z ∈ escapeOpen c ∩ Complex.slitPlane}

/-- **The per-level single-valued Böttcher branch** `exp(2⁻ᴺ · bottcherLog ∘ f_c^[N])`. -/
noncomputable def phiLevel (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (((((2 : ℝ) ^ N)⁻¹ : ℝ) : ℂ) * bottcherLog c ((quadratic c)^[N] z))

/-- The level branch is analytic on its fundamental domain. -/
theorem analyticOnNhd_phiLevel (c : ℂ) (N : ℕ) :
    AnalyticOnNhd ℂ (phiLevel c N) (levelDomain c N) :=
  (exists_greenConjugate_explicit c N).1.cexp

/-- The level branch is nowhere zero. -/
theorem phiLevel_ne_zero (c : ℂ) (N : ℕ) (z : ℂ) : phiLevel c N z ≠ 0 :=
  Complex.exp_ne_zero _

/-- The level branch carries the genuine Böttcher modulus `|phiLevel| = exp(G_c)`. -/
theorem norm_phiLevel {c : ℂ} {N : ℕ} {z : ℂ} (hz : z ∈ levelDomain c N) :
    ‖phiLevel c N z‖ = Real.exp (greenLimit c z) :=
  norm_exp_greenConjugate_explicit c N hz

/-- **The defining root relation** `phiLevel^{2ᴺ} = φ_c ∘ f_c^[N]`: the level branch is the
`2ᴺ`-th root realizing the iterated functional equation. -/
theorem phiLevel_pow (c : ℂ) (N : ℕ) (z : ℂ) :
    (phiLevel c N z) ^ (2 ^ N) = bottcherCoord c ((quadratic c)^[N] z) := by
  unfold phiLevel bottcherCoord
  rw [← Complex.exp_nat_mul]
  congr 1
  have h2 : ((2 : ℂ) ^ N) ≠ 0 := pow_ne_zero N (by norm_num)
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]

/-- **Chain base case**: the level-`0` branch is exactly the germ Böttcher coordinate `φ_c`, so the
glued chain extends the genuine germ. -/
theorem phiLevel_zero (c : ℂ) (z : ℂ) : phiLevel c 0 z = bottcherCoord c z := by
  unfold phiLevel bottcherCoord
  simp [Function.iterate_zero, pow_zero]

/-- The level-`0` fundamental domain is the germ slit exterior `escapeOpen ∩ slitPlane`. -/
theorem levelDomain_zero (c : ℂ) : levelDomain c 0 = escapeOpen c ∩ Complex.slitPlane := by
  unfold levelDomain
  simp [Function.iterate_zero]

end Bottcher
