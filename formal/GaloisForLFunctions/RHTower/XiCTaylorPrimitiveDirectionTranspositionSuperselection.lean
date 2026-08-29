import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayGlobalReassembly

/-!
# Transposition superselection for complete primitive theta directions

The XST primitive-ray decomposition sums over ordered coprime directions.  Swapping a direction's
two coordinates is the only canonical two-member orbit suggested by source symmetry.  This module
proves that the complete direction current, including its common-scale sum and positive-quadrant
integral, is invariant under this transposition.

Consequently every scalar mixing of one transpose orbit factors through the sum of its two
coefficients.  Equal source weights reinforce the unresolved current, while the antisymmetric
combination cancels only by deleting that entire source-visible packet.  The same law is
transported through the exact shell-born reflected radial bridge.  Thus transpose pairing cannot
supply the cancellation needed by the XST core-current route to RH; any surviving producer must
mix distinct transpose orbits or add genuinely signed infinite-support incidence.
-/

open Complex Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- Exchange the two positive coprime coordinates of a primitive theta direction. -/
def thetaCuspPrimitiveDirectionTranspose
    (q : ThetaCuspPrimitiveDirection) : ThetaCuspPrimitiveDirection :=
  ⟨(q.1.2, q.1.1), q.2.symm⟩

@[simp] theorem thetaCuspPrimitiveDirectionTranspose_fst
    (q : ThetaCuspPrimitiveDirection) :
    (thetaCuspPrimitiveDirectionTranspose q).1.1 = q.1.2 := rfl

@[simp] theorem thetaCuspPrimitiveDirectionTranspose_snd
    (q : ThetaCuspPrimitiveDirection) :
    (thetaCuspPrimitiveDirectionTranspose q).1.2 = q.1.1 := rfl

/-- Primitive-direction transposition is an involution. -/
@[simp] theorem thetaCuspPrimitiveDirectionTranspose_transpose
    (q : ThetaCuspPrimitiveDirection) :
    thetaCuspPrimitiveDirectionTranspose
        (thetaCuspPrimitiveDirectionTranspose q) = q := by
  apply Subtype.ext
  rfl

/-- Transposition of a primitive direction is exactly coordinate swap of its full common-scale
density. -/
theorem thetaCuspPrimitiveDirectionDensityPair_transpose_swap
    (q : ThetaCuspPrimitiveDirection) (p : ℝ × ℝ) :
    thetaCuspPrimitiveDirectionDensityPair
        (thetaCuspPrimitiveDirectionTranspose q) (p.2, p.1) =
      thetaCuspPrimitiveDirectionDensityPair q p := by
  unfold thetaCuspPrimitiveDirectionDensityPair
  apply tsum_congr
  intro g
  dsimp only [thetaCuspPrimitiveDirectionTranspose]
  ring

/-- The complete Cartesian current integrand is covariant under simultaneous direction and source
coordinate transposition. -/
theorem thetaCuspPrimitiveDirectionCoreIntegrand_transpose_swap
    (q : ThetaCuspPrimitiveDirection) (d : ℕ) (z : ℂ) (p : ℝ × ℝ) :
    thetaCuspPrimitiveDirectionCoreIntegrand
        (thetaCuspPrimitiveDirectionTranspose q) d z (p.2, p.1) =
      thetaCuspPrimitiveDirectionCoreIntegrand q d z p := by
  unfold thetaCuspPrimitiveDirectionCoreIntegrand
  rw [thetaCuspPrimitiveDirectionDensityPair_transpose_swap,
    xiCTaylorThetaTailCorePairCurrent_swap]

/-- Absolute integrability of one complete primitive-direction current in the exact product
measure used by global reassembly. -/
theorem integrable_thetaCuspPrimitiveDirectionCoreIntegrand
    (q : ThetaCuspPrimitiveDirection) (d : ℕ) (z : ℂ) :
    Integrable (thetaCuspPrimitiveDirectionCoreIntegrand q d z)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have h := integrableOn_thetaCuspPrimitiveRayCartesianCoreIntegrand
    q.1.1.pos q.1.2.pos d z
  change Integrable
    (thetaCuspPrimitiveRayCartesianCoreIntegrand
      (q.1.1 : ℕ) (q.1.2 : ℕ) d z)
    (volume.restrict thetaCuspPositiveQuadrantSet) at h
  have hmeasure :
      volume.restrict thetaCuspPositiveQuadrantSet =
        (volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)) := by
    dsimp only [thetaCuspPositiveQuadrantSet]
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  rw [hmeasure] at h
  have hfun :
      thetaCuspPrimitiveDirectionCoreIntegrand q d z =
        thetaCuspPrimitiveRayCartesianCoreIntegrand
          (q.1.1 : ℕ) (q.1.2 : ℕ) d z := by
    funext p
    unfold thetaCuspPrimitiveDirectionCoreIntegrand
      thetaCuspPrimitiveRayCartesianCoreIntegrand
    rw [thetaCuspPrimitiveDirectionDensityPair_eq_rayDensityPair]
  rw [hfun]
  exact h

/-- **Complete-direction transposition invariance.**  Coordinate symmetry survives the common-scale
sum, the full positive-quadrant integration, and all finite theta-tail layers. -/
theorem integral_thetaCuspPrimitiveDirectionCoreIntegrand_transpose
    (q : ThetaCuspPrimitiveDirection) (d : ℕ) (z : ℂ) :
    (∫ p : ℝ × ℝ,
        thetaCuspPrimitiveDirectionCoreIntegrand
          (thetaCuspPrimitiveDirectionTranspose q) d z p
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      ∫ p : ℝ × ℝ,
        thetaCuspPrimitiveDirectionCoreIntegrand q d z p
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ × ℝ → ℝ := thetaCuspPrimitiveDirectionCoreIntegrand q d z
  have hf : Integrable f (μ.prod μ) := by
    simpa only [f, μ] using
      integrable_thetaCuspPrimitiveDirectionCoreIntegrand q d z
  have hswap :
      thetaCuspPrimitiveDirectionCoreIntegrand
          (thetaCuspPrimitiveDirectionTranspose q) d z =
        f ∘ Prod.swap := by
    funext p
    exact thetaCuspPrimitiveDirectionCoreIntegrand_transpose_swap q d z (p.2, p.1)
  rw [hswap]
  change (∫ p : ℝ × ℝ, (f ∘ Prod.swap) p ∂μ.prod μ) =
    ∫ p : ℝ × ℝ, f p ∂μ.prod μ
  calc
    (∫ p : ℝ × ℝ, (f ∘ Prod.swap) p ∂μ.prod μ) =
        ∫ x : ℝ, ∫ y : ℝ, f (y, x) ∂μ ∂μ := by
      have hprod := integral_prod (f ∘ Prod.swap) hf.swap
      change (∫ p : ℝ × ℝ, f (p.2, p.1) ∂μ.prod μ) =
        ∫ x : ℝ, ∫ y : ℝ, f (y, x) ∂μ ∂μ at hprod
      exact hprod
    _ = ∫ y : ℝ, ∫ x : ℝ, f (x, y) ∂μ ∂μ := rfl
    _ = ∫ p : ℝ × ℝ, f p ∂μ.prod μ :=
      (integral_prod_symm f hf).symm

/-- Complete current carried by one coprime primitive direction. -/
def xiCTaylorThetaTailPrimitiveDirectionCurrent
    (q : ThetaCuspPrimitiveDirection) (d : ℕ) (z : ℂ) : ℝ :=
  ∫ p : ℝ × ℝ,
    thetaCuspPrimitiveDirectionCoreIntegrand q d z p
      ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))

@[simp] theorem xiCTaylorThetaTailPrimitiveDirectionCurrent_transpose
    (q : ThetaCuspPrimitiveDirection) (d : ℕ) (z : ℂ) :
    xiCTaylorThetaTailPrimitiveDirectionCurrent
        (thetaCuspPrimitiveDirectionTranspose q) d z =
      xiCTaylorThetaTailPrimitiveDirectionCurrent q d z := by
  exact integral_thetaCuspPrimitiveDirectionCoreIntegrand_transpose q d z

/-- Every scalar linear aggregate on one transpose orbit factors through the coefficient sum. -/
theorem xiCTaylorThetaTailPrimitiveDirectionCurrent_orbitMix_eq
    (q : ThetaCuspPrimitiveDirection) (d : ℕ) (z : ℂ) (a b : ℝ) :
    a * xiCTaylorThetaTailPrimitiveDirectionCurrent q d z +
        b * xiCTaylorThetaTailPrimitiveDirectionCurrent
          (thetaCuspPrimitiveDirectionTranspose q) d z =
      (a + b) * xiCTaylorThetaTailPrimitiveDirectionCurrent q d z := by
  rw [xiCTaylorThetaTailPrimitiveDirectionCurrent_transpose]
  ring

/-- **Exact transpose-orbit cancellation classification.**  An orbit aggregate vanishes precisely
when its coefficient sum vanishes or the complete source packet was already zero. -/
theorem xiCTaylorThetaTailPrimitiveDirectionCurrent_orbitMix_eq_zero_iff
    (q : ThetaCuspPrimitiveDirection) (d : ℕ) (z : ℂ) (a b : ℝ) :
    a * xiCTaylorThetaTailPrimitiveDirectionCurrent q d z +
          b * xiCTaylorThetaTailPrimitiveDirectionCurrent
            (thetaCuspPrimitiveDirectionTranspose q) d z = 0 ↔
      a + b = 0 ∨ xiCTaylorThetaTailPrimitiveDirectionCurrent q d z = 0 := by
  rw [xiCTaylorThetaTailPrimitiveDirectionCurrent_orbitMix_eq]
  exact mul_eq_zero

/-- Canonical equal-weight transposition reinforces rather than cancels one primitive packet. -/
theorem xiCTaylorThetaTailPrimitiveDirectionCurrent_add_transpose
    (q : ThetaCuspPrimitiveDirection) (d : ℕ) (z : ℂ) :
    xiCTaylorThetaTailPrimitiveDirectionCurrent q d z +
        xiCTaylorThetaTailPrimitiveDirectionCurrent
          (thetaCuspPrimitiveDirectionTranspose q) d z =
      2 * xiCTaylorThetaTailPrimitiveDirectionCurrent q d z := by
  rw [xiCTaylorThetaTailPrimitiveDirectionCurrent_transpose]
  ring

/-- The antisymmetric transpose channel is exactly source-null. -/
theorem xiCTaylorThetaTailPrimitiveDirectionCurrent_sub_transpose
    (q : ThetaCuspPrimitiveDirection) (d : ℕ) (z : ℂ) :
    xiCTaylorThetaTailPrimitiveDirectionCurrent q d z -
        xiCTaylorThetaTailPrimitiveDirectionCurrent
          (thetaCuspPrimitiveDirectionTranspose q) d z = 0 := by
  rw [xiCTaylorThetaTailPrimitiveDirectionCurrent_transpose]
  ring

/-- The same transpose invariance holds for the complete shell-born reflected radial packet. -/
theorem integral_thetaCuspPrimitiveDirectionGlobalJoint_transpose
    (q : ThetaCuspPrimitiveDirection) (d : ℕ) (z : ℂ) :
    (∫ r : ℝ in Ici
          (thetaCuspPrimitiveRayRadialLog
            ((thetaCuspPrimitiveDirectionTranspose q).1.1 : ℕ)
            ((thetaCuspPrimitiveDirectionTranspose q).1.2 : ℕ) 0 0),
        (8 * Real.exp
          (-(Real.log ((thetaCuspPrimitiveDirectionTranspose q).1.1 : ℝ) +
            Real.log ((thetaCuspPrimitiveDirectionTranspose q).1.2 : ℝ)) / 2)) *
        thetaCuspPrimitiveRayJointSeamIntegrand d z r
          (-Real.log ((thetaCuspPrimitiveDirectionTranspose q).1.1 : ℝ))
          (-Real.log ((thetaCuspPrimitiveDirectionTranspose q).1.2 : ℝ))) =
      ∫ r : ℝ in Ici
          (thetaCuspPrimitiveRayRadialLog (q.1.1 : ℕ) (q.1.2 : ℕ) 0 0),
        (8 * Real.exp
          (-(Real.log (q.1.1 : ℝ) + Real.log (q.1.2 : ℝ)) / 2)) *
        thetaCuspPrimitiveRayJointSeamIntegrand d z r
          (-Real.log (q.1.1 : ℝ)) (-Real.log (q.1.2 : ℝ)) := by
  rw [← integral_thetaCuspPrimitiveDirectionCoreIntegrand_eq_globalJoint
      (thetaCuspPrimitiveDirectionTranspose q) d z,
    ← integral_thetaCuspPrimitiveDirectionCoreIntegrand_eq_globalJoint q d z]
  exact integral_thetaCuspPrimitiveDirectionCoreIntegrand_transpose q d z

end

end RHTower
