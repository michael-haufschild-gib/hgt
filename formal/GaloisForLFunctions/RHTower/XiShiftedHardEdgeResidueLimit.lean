import GaloisForLFunctions.RHTower.XiShiftedHardEdgeRootDivision
import GaloisForLFunctions.HTGeometry.PowerSequenceLimitOne
import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# The surviving Padé residue at a simple hard root

The scale-invariant residue law writes the Padé residue carried by one Gauss node as

`ρ = Γ / (t^{2n+1} S'(u)²)`,

with `Γ` the terminal hard-edge energy of the divided state and `t` the centre ratio.  Along a
hard-edge sequence the centre ratio tends to one, the normalized polynomials converge locally
uniformly, and the divided states converge in the dominated sense; the three limits combine into
a residue limit `ρ → γ/F'(r)²` with `γ` the terminal energy of the limiting divided state.

Because every finite divided energy is a nonnegative form value, the limiting energy is
nonnegative; when it is strictly positive the residues are eventually bounded below by a positive
constant, so the pole cannot be hidden by a vanishing ordinary Christoffel weight.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower

/-- **(GJRS.33) The residue limit.**  The scale-invariant residue law transports a convergent
terminal energy, a centre ratio tending to one, and a nonvanishing limiting derivative into a
convergent residue. -/
theorem tendsto_hardEdgeResidue {Γ tpow dS ρ : ℕ → ℝ} {γ F' : ℝ}
    (hρ : ∀ j, ρ j = Γ j / (tpow j * dS j ^ 2))
    (hΓ : Tendsto Γ atTop (𝓝 γ)) (ht : Tendsto tpow atTop (𝓝 1))
    (hd : Tendsto dS atTop (𝓝 F')) (hF : F' ≠ 0) :
    Tendsto ρ atTop (𝓝 (γ / F' ^ 2)) := by
  have hden : Tendsto (fun j => tpow j * dS j ^ 2) atTop (𝓝 (1 * F' ^ 2)) := ht.mul (hd.pow 2)
  rw [one_mul] at hden
  have hlim := hΓ.div hden (pow_ne_zero 2 hF)
  have hfun : ρ = fun j => Γ j / (tpow j * dS j ^ 2) := funext hρ
  rw [hfun]
  exact hlim

/-- **(GJRS.32) The divided terminal energy passes to the limit.**  A dominated limit of divided
hard-edge states transports the terminal energies. -/
theorem routeUHardEdgeDividedEnergy_tendsto (σ : ℝ) (S : ℕ → ℝ → ℝ) (F : ℝ → ℝ)
    (a : ℕ → ℝ) (r : ℝ) (g : ℝ → ℝ)
    (hmeas : ∀ j, AEStronglyMeasurable
      (fun v : ℝ => (S j v / (v - a j)) ^ 2 * routeUHardEdgeDensity σ (Real.sqrt v) / Real.sqrt v)
      (volume.restrict (Ioi 0)))
    (hg : IntegrableOn g (Ioi 0))
    (hdom : ∀ j, ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(S j v / (v - a j)) ^ 2 * routeUHardEdgeDensity σ (Real.sqrt v) / Real.sqrt v‖ ≤ g v)
    (hptw : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun j =>
          (S j v / (v - a j)) ^ 2 * routeUHardEdgeDensity σ (Real.sqrt v) / Real.sqrt v) atTop
        (nhds ((F v / (v - r)) ^ 2 * routeUHardEdgeDensity σ (Real.sqrt v) / Real.sqrt v)))
    (hpolar : Tendsto (fun j => (S j (-1 / 4) / (-1 / 4 - a j)) ^ 2) atTop
      (nhds ((F (-1 / 4) / (-1 / 4 - r)) ^ 2))) :
    Tendsto (fun j => routeUHardEdgePairing σ (fun v => (S j v / (v - a j)) ^ 2)) atTop
      (nhds (routeUHardEdgePairing σ (fun v => (F v / (v - r)) ^ 2))) :=
  routeUHardEdgePairing_tendsto σ (fun j v => (S j v / (v - a j)) ^ 2)
    (fun v => (F v / (v - r)) ^ 2) g hmeas hg hdom hptw hpolar

/-- **(GJRS.32) The limiting terminal energy is nonnegative.** -/
theorem routeUHardEdgeDividedEnergy_nonneg (σ : ℝ) (S : ℕ → ℝ → ℝ) (F : ℝ → ℝ)
    (a : ℕ → ℝ) (r : ℝ) (g : ℝ → ℝ)
    (hmeas : ∀ j, AEStronglyMeasurable
      (fun v : ℝ => (S j v / (v - a j)) ^ 2 * routeUHardEdgeDensity σ (Real.sqrt v) / Real.sqrt v)
      (volume.restrict (Ioi 0)))
    (hg : IntegrableOn g (Ioi 0))
    (hdom : ∀ j, ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(S j v / (v - a j)) ^ 2 * routeUHardEdgeDensity σ (Real.sqrt v) / Real.sqrt v‖ ≤ g v)
    (hptw : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun j =>
          (S j v / (v - a j)) ^ 2 * routeUHardEdgeDensity σ (Real.sqrt v) / Real.sqrt v) atTop
        (nhds ((F v / (v - r)) ^ 2 * routeUHardEdgeDensity σ (Real.sqrt v) / Real.sqrt v)))
    (hpolar : Tendsto (fun j => (S j (-1 / 4) / (-1 / 4 - a j)) ^ 2) atTop
      (nhds ((F (-1 / 4) / (-1 / 4 - r)) ^ 2)))
    (hnn : ∀ j, 0 ≤ routeUHardEdgePairing σ (fun v => (S j v / (v - a j)) ^ 2)) :
    0 ≤ routeUHardEdgePairing σ (fun v => (F v / (v - r)) ^ 2) :=
  routeUHardEdgePairing_nonneg_of_tendsto σ (fun j v => (S j v / (v - a j)) ^ 2)
    (fun v => (F v / (v - r)) ^ 2) g hmeas hg hdom hptw hpolar hnn

/-- **(GJRS.32)-(GJRS.33) Residue transport at a simple hard root.**  The Padé residues of the
canonical continuations converge to the terminal energy of the limiting divided state divided by
the squared limiting derivative, and that energy is nonnegative. -/
theorem routeUHardEdgeResidue_tendsto (σ : ℝ) (S : ℕ → ℝ → ℝ) (F : ℝ → ℝ)
    (a : ℕ → ℝ) (r : ℝ) (g : ℝ → ℝ) (tpow dS ρ : ℕ → ℝ) {F' : ℝ}
    (hmeas : ∀ j, AEStronglyMeasurable
      (fun v : ℝ => (S j v / (v - a j)) ^ 2 * routeUHardEdgeDensity σ (Real.sqrt v) / Real.sqrt v)
      (volume.restrict (Ioi 0)))
    (hg : IntegrableOn g (Ioi 0))
    (hdom : ∀ j, ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(S j v / (v - a j)) ^ 2 * routeUHardEdgeDensity σ (Real.sqrt v) / Real.sqrt v‖ ≤ g v)
    (hptw : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      Tendsto (fun j =>
          (S j v / (v - a j)) ^ 2 * routeUHardEdgeDensity σ (Real.sqrt v) / Real.sqrt v) atTop
        (nhds ((F v / (v - r)) ^ 2 * routeUHardEdgeDensity σ (Real.sqrt v) / Real.sqrt v)))
    (hpolar : Tendsto (fun j => (S j (-1 / 4) / (-1 / 4 - a j)) ^ 2) atTop
      (nhds ((F (-1 / 4) / (-1 / 4 - r)) ^ 2)))
    (hnn : ∀ j, 0 ≤ routeUHardEdgePairing σ (fun v => (S j v / (v - a j)) ^ 2))
    (hρ : ∀ j, ρ j
      = routeUHardEdgePairing σ (fun v => (S j v / (v - a j)) ^ 2) / (tpow j * dS j ^ 2))
    (ht : Tendsto tpow atTop (nhds 1)) (hd : Tendsto dS atTop (nhds F')) (hF : F' ≠ 0) :
    Tendsto ρ atTop (nhds (routeUHardEdgePairing σ (fun v => (F v / (v - r)) ^ 2) / F' ^ 2))
      ∧ 0 ≤ routeUHardEdgePairing σ (fun v => (F v / (v - r)) ^ 2) :=
  ⟨tendsto_hardEdgeResidue hρ
      (routeUHardEdgeDividedEnergy_tendsto σ S F a r g hmeas hg hdom hptw hpolar) ht hd hF,
    routeUHardEdgeDividedEnergy_nonneg σ S F a r g hmeas hg hdom hptw hpolar hnn⟩

/-- **Residue survival.**  A positive limiting terminal energy forces the residues to be eventually
bounded below by a positive constant: the pole cannot be hidden by a vanishing ordinary Christoffel
weight. -/
theorem eventually_hardEdgeResidue_gt {ρ : ℕ → ℝ} {γ F' : ℝ}
    (hlim : Tendsto ρ atTop (nhds (γ / F' ^ 2))) (hγ : 0 < γ) (hF : F' ≠ 0) :
    ∀ᶠ j in atTop, γ / (2 * F' ^ 2) < ρ j := by
  have hsq : 0 < F' ^ 2 := pow_two_pos_of_ne_zero hF
  have hpos : 0 < γ / F' ^ 2 := div_pos hγ hsq
  have hrw : γ / (2 * F' ^ 2) = γ / F' ^ 2 / 2 := by
    field_simp
  have hlt : γ / (2 * F' ^ 2) < γ / F' ^ 2 := by
    rw [hrw]
    linarith
  exact Tendsto.eventually_const_lt hlt hlim

/-- **(GJRS.31) The moving derivative converges.**  Locally uniform convergence of entire
normalizations transports the derivative at a moving point to the derivative of the limit at the
limiting point. -/
theorem tendsto_deriv_of_tendstoLocallyUniformly {S : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {a : ℕ → ℂ} {r : ℂ}
    (hS : ∀ j, Differentiable ℂ (S j))
    (hconv : TendstoLocallyUniformly S F atTop)
    (ha : Tendsto a atTop (nhds r)) :
    Tendsto (fun j => deriv (S j) (a j)) atTop (nhds (deriv F r)) := by
  have hdiffOn : ∀ᶠ j in (atTop : Filter ℕ), DifferentiableOn ℂ (S j) Set.univ :=
    Filter.Eventually.of_forall fun j => (hS j).differentiableOn
  have hOn : TendstoLocallyUniformlyOn S F atTop Set.univ := tendstoLocallyUniformlyOn_univ.2 hconv
  have hderiv : TendstoLocallyUniformly (deriv ∘ S) (deriv F) atTop :=
    tendstoLocallyUniformlyOn_univ.1 (hOn.deriv hdiffOn isOpen_univ)
  have hFdiff : DifferentiableOn ℂ F Set.univ := hOn.differentiableOn hdiffOn isOpen_univ
  have hFd : Differentiable ℂ F := differentiableOn_univ.1 hFdiff
  exact hderiv.tendsto_comp hFd.deriv.continuous.continuousAt ha

end RHTower

end
