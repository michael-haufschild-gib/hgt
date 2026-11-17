import GaloisForLFunctions.OrderSixMetaplecticTheory.TheQuadraticGradeCubeFactorIsAnEntireHeckeLFunction

/-!
# The twisted remainders read the zeros of the cube factor

On `V = {1 < Re s < 13/3, Im s > 0}` the traces continue `M·L_ψ` (cubic grade) and the quadratic relation
`M·(g_λJ₆λ(2)L_λ + N²χ(−4)χ(9)⁻¹λ(−2)g_{χλ}N^{s−2}L_{χ̄λ})`. Through the grade factorization
`L_ψ = C̄²Z_{ψ³}(3s/2 − 1)Q_ψ`, a holomorphic continuation of the squarefree combination to `V` (the form a
square-root remainder takes, `Re w > 1/2`) forces the trace continuation to vanish at `2(1 + ρ)/3` for every
zero `ρ` of the cube factor with `Re ρ > 1/2`, `Im ρ > 0`:

* cubic grade: every zero of `ζ(z)L(z, χ₋₃)` (`cubicGrade_remainder_forces_zero`);
* quadratic grade (`N(q) ≡ 1 mod 4`): every zero of the Hecke `L`-function `L(z, λ̃_q)`
  (`quadraticGrade_remainder_forces_zero`).

So a square-root remainder at a prime column requires the zeros of `L(·, λ̃_q)` right of the critical line to be
zeros of the trace continuation: the quadratic-grade analogue of the unit-layer law, with `ζ_K` replaced by the
quadratic Hecke `L`-function of conductor `(q)(λ)`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicJacobi SpectralTheoryOfTheCubicCover
  FamilyContinuationTheory FamilyContinuationTheory.EisensteinNorm

/-- The strip `V = {1 < Re s < 13/3, Im s > 0}` of the trace continuations. -/
def traceStrip : Set ℂ := {s : ℂ | 1 < s.re} ∩ ({s : ℂ | s.re < 13 / 3} ∩ {s : ℂ | 0 < s.im})

theorem mem_traceStrip {s : ℂ} : s ∈ traceStrip ↔ 1 < s.re ∧ s.re < 13 / 3 ∧ 0 < s.im := Iff.rfl

theorem traceStrip_isOpen : IsOpen traceStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    ((isOpen_lt Complex.continuous_re continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im))

theorem traceStrip_isPreconnected : IsPreconnected traceStrip :=
  ((convex_halfSpace_re_gt 1).inter ((convex_halfSpace_re_lt (13 / 3)).inter (convex_halfSpace_im_gt 0))).isPreconnected

/-- **Identity theorem on the strip.** Holomorphic functions on `V` that agree on `Re s > 4` agree on `V`. -/
theorem eqOn_traceStrip (f g : ℂ → ℂ) (hf : ∀ s ∈ traceStrip, DifferentiableAt ℂ f s)
    (hg : ∀ s ∈ traceStrip, DifferentiableAt ℂ g s)
    (he : ∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → f s = g s) : ∀ s ∈ traceStrip, f s = g s := by
  have hfo : DifferentiableOn ℂ f traceStrip := fun s hs => (hf s hs).differentiableWithinAt
  have hgo : DifferentiableOn ℂ g traceStrip := fun s hs => (hg s hs).differentiableWithinAt
  have hfa : AnalyticOnNhd ℂ f traceStrip := hfo.analyticOnNhd traceStrip_isOpen
  have hga : AnalyticOnNhd ℂ g traceStrip := hgo.analyticOnNhd traceStrip_isOpen
  set z₀ : ℂ := (41 / 10 : ℂ) + Complex.I with hz₀
  have hre : z₀.re = 41 / 10 := by simp [hz₀]
  have him : z₀.im = 1 := by simp [hz₀]
  have hW : IsOpen {s : ℂ | 4 < s.re ∧ s.re < 13 / 3 ∧ 0 < s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im))
  have hz₀W : z₀ ∈ {s : ℂ | 4 < s.re ∧ s.re < 13 / 3 ∧ 0 < s.im} :=
    ⟨by rw [hre]; norm_num, by rw [hre]; norm_num, by rw [him]; norm_num⟩
  have hz₀V : z₀ ∈ traceStrip := by
    refine ⟨?_, ?_, ?_⟩
    · show 1 < z₀.re
      rw [hre]
      norm_num
    · show z₀.re < 13 / 3
      rw [hre]
      norm_num
    · show 0 < z₀.im
      rw [him]
      norm_num
  have hev : f =ᶠ[𝓝 z₀] g :=
    Filter.eventuallyEq_of_mem (hW.mem_nhds hz₀W) (fun s hs => he s hs.1 hs.2.1 hs.2.2)
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga traceStrip_isPreconnected hz₀V hev

theorem cubeArg (z : ℂ) : 3 * (2 * (1 + z) / 3 / 2) - 1 = z := by ring

namespace PrimaryPrime

variable (P : PrimaryPrime)

theorem twistDirichlet_lam (s : ℂ) : P.twistDirichlet P.lam s = besselDirichlet P.quadTwistCoeff s := rfl

theorem twistDirichlet_chi_sq_lam (s : ℂ) :
    P.twistDirichlet (P.chi ^ 2 * P.lam) s = besselDirichlet P.sexticTwistCoeff s := rfl

theorem chi_sq_mul_lam_pow_three : (P.chi ^ 2 * P.lam) ^ 3 = P.lam := by
  have h6 : P.chi ^ (2 * 3) = 1 := by rw [mul_comm, pow_mul, P.chi_pow_three, one_pow]
  rw [mul_pow, ← pow_mul, h6, one_mul, P.lam_pow_three]

/-- **The quadratic-grade remainder reads the zeros of `L(·, λ̃_q)`.** Let `Λ` continue the quadratic relation
to `V`. If the squarefree combination `g_λJ₆λ(2)Q_λ + N²χ(−4)χ(9)⁻¹λ(−2)g_{χλ}N^{s−2}Q_{χ̄λ}` continues
holomorphically to `V`, then `Λ(2(1 + ρ)/3) = 0` for every zero `ρ` of `L(·, λ̃_q)` with
`2(1 + ρ)/3 ∈ V`. -/
theorem quadraticGrade_remainder_forces_zero (h2 : (2 : P.Res) ≠ 0) (hlam : P.lam (-1) = 1) (Λ : ℂ → ℂ)
    (hΛe : ∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
      Λ s = besselSqMellin s * (P.quadFactor * besselDirichlet P.quadTwistCoeff s +
        P.sexticFactor s * besselDirichlet P.sexticTwistCoeff s))
    (hΛd : ∀ s ∈ traceStrip, DifferentiableAt ℂ Λ s) (F : ℂ → ℂ) (hFd : ∀ s ∈ traceStrip, DifferentiableAt ℂ F s)
    (hFe : ∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im →
      F s = P.quadFactor * P.twistCombination P.lam s + P.sexticFactor s * P.twistCombination (P.chi ^ 2 * P.lam) s)
    (ρ : ℂ) (hρ : HeckeFamily.LFunction (P.quadHecke hlam) ρ = 0) (hV : 2 * (1 + ρ) / 3 ∈ traceStrip) :
    Λ (2 * (1 + ρ) / 3) = 0 := by
  set g : ℂ → ℂ := fun s => besselSqMellin s * (star rationalSourceThetaScalar ^ 2 * P.quadCubeFactor hlam s * F s)
    with hgdef
  have hgd : ∀ s ∈ traceStrip, DifferentiableAt ℂ g s := fun s hs =>
    (besselSqMellin_differentiableAt s (by have := (mem_traceStrip.mp hs).1; linarith)).mul
      (((differentiableAt_const _).mul (P.quadCubeFactor_differentiable h2 hlam s)).mul (hFd s hs))
  have heq := eqOn_traceStrip Λ g hΛd hgd (fun s hs4 hs hi => by
    rw [hΛe s hs4 hs hi, hgdef]
    dsimp only
    rw [hFe s hs4 hs hi, ← P.twistDirichlet_lam, ← P.twistDirichlet_chi_sq_lam,
      P.twistDirichlet_eq_quadCubeFactor hlam P.lam P.lam_pow_three s hs4,
      P.twistDirichlet_eq_quadCubeFactor hlam _ P.chi_sq_mul_lam_pow_three s hs4]
    ring)
  rw [heq _ hV, hgdef]
  simp only
  rw [quadCubeFactor, cubeArg, hρ]
  ring

/-- **The cubic-grade remainder reads the zeros of `ζ_K`.** For cubic `φ` let `Λ` continue `M·L_φ` to `V`. If
the squarefree combination `Q_φ` continues holomorphically to `V`, then `Λ(2(1 + ρ)/3) = 0` for every zero
`ρ ≠ 1` of `ζ` or of `L(·, χ₋₃)` with `2(1 + ρ)/3 ∈ V`. -/
theorem cubicGrade_remainder_forces_zero (φ : MulChar P.Res ℂ) (hφ : φ ^ 3 = 1) (Λ : ℂ → ℂ)
    (hΛe : ∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → Λ s = besselSqMellin s * P.twistDirichlet φ s)
    (hΛd : ∀ s ∈ traceStrip, DifferentiableAt ℂ Λ s) (F : ℂ → ℂ) (hFd : ∀ s ∈ traceStrip, DifferentiableAt ℂ F s)
    (hFe : ∀ s : ℂ, 4 < s.re → s.re < 13 / 3 → 0 < s.im → F s = P.twistCombination φ s)
    (ρ : ℂ) (hρ1 : ρ ≠ 1) (hρ : riemannZeta ρ = 0 ∨ DirichletCharacter.LFunction chi3D ρ = 0)
    (hV : 2 * (1 + ρ) / 3 ∈ traceStrip) :
    Λ (2 * (1 + ρ) / 3) = 0 := by
  set g : ℂ → ℂ := fun s => besselSqMellin s * (P.combinationDenom s / (s - 4 / 3) * F s) with hgdef
  have hne : ∀ s ∈ traceStrip, s - 4 / 3 ≠ 0 := fun s hs h0 => by
    have him := (mem_traceStrip.mp hs).2.2
    rw [sub_eq_zero.mp h0] at him
    norm_num at him
  have hgd : ∀ s ∈ traceStrip, DifferentiableAt ℂ g s := fun s hs =>
    (besselSqMellin_differentiableAt s (by have := (mem_traceStrip.mp hs).1; linarith)).mul
      (((P.combinationDenom_differentiable s).div (differentiableAt_id.sub_const _) (hne s hs)).mul (hFd s hs))
  have heq := eqOn_traceStrip Λ g hΛd hgd (fun s hs4 hs hi => by
    have hs0 : s - 4 / 3 ≠ 0 := hne s (mem_traceStrip.mpr ⟨by linarith, hs, hi⟩)
    have hL := P.sub_mul_twistDirichlet φ hφ s hs4
    rw [hΛe s hs4 hs hi, hgdef]
    dsimp only
    rw [hFe s hs4 hs hi]
    rw [div_mul_eq_mul_div, mul_div_assoc', eq_div_iff hs0]
    unfold combinationDenom
    linear_combination besselSqMellin s * hL)
  rw [heq _ hV, hgdef]
  simp only
  have hz : clearedCubeZeta (2 * (1 + ρ) / 3) = 0 := by
    unfold clearedCubeZeta
    rw [cubeArg, RHTower.zetaPoleFilled_of_ne hρ1]
    rcases hρ with h | h <;> simp [h]
  rw [combinationDenom, hz]
  ring

end PrimaryPrime

end GaloisForLFunctions.OrderSixMetaplecticTheory
