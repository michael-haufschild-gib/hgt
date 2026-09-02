import GaloisForLFunctions.RHTower.FZZCigarParityMarkedOPEChargeIncidenceNoGo

/-!
# FZZ sphere-vacuum replica-kernel phase collapse

Halder--Jafferis' genus-zero vacuum integrand (arXiv:2402.00932v3, (3.26)) is a
finite product of conjugate position differences.  Their replica deformation
(3.29)--(3.31) keeps every exponent real.  The imported charge-incidence
classification resolves the omitted marked same-winding increment as zero and
the symmetry-normalized opposite-winding increment as

`a(k) = 2k/(k-2)`.

This file proves the all-depth source-shape statement rather than assuming its
phase consequence.  Every collision-free absolute-power product is a strictly
positive exponential of a real logarithmic action, and its exact first replica
derivative is the same positive kernel times a real logarithmic score.  Hence
both the undeformed kernel and its first replica tangent have zero
antiunitary-odd/chiral phase.

No depth, position dependence, physical level, replica point, or output
predicate can turn that identically zero phase channel into the radial wall.
This kills the FZZ-P chain

`sphere vacuum/area position-kernel phase -> chiral divisor-mode passivity
 -> Mellin completeness -> RH`.

Scope is intentionally sharp.  This does not control phases introduced by
meromorphic regularization of a divergent position integral, real sign or
magnitude after integration, external-BRST branch factors, torus/higher-genus
prime-form monodromy, or higher replica order.  Those are the positive
survivors.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Logarithmic action of a finite absolute-power kernel under real exponent motion. -/
def fzzSphereVacuumReplicaLogAction {n : ℕ}
    (distance : Fin n → ℂ) (exponent velocity : Fin n → ℝ) (δ : ℝ) : ℝ :=
  ∑ i, (exponent i + δ * velocity i) * Real.log (Complex.normSq (distance i))

/-- Real HJ-type vacuum kernel. -/
def fzzSphereVacuumReplicaKernel {n : ℕ}
    (distance : Fin n → ℂ) (exponent velocity : Fin n → ℝ) (δ : ℝ) : ℝ :=
  Real.exp (fzzSphereVacuumReplicaLogAction distance exponent velocity δ)

/-- Complexification used to expose the phase channel. -/
def fzzSphereVacuumReplicaComplexKernel {n : ℕ}
    (distance : Fin n → ℂ) (exponent velocity : Fin n → ℝ) (δ : ℝ) : ℂ :=
  (fzzSphereVacuumReplicaKernel distance exponent velocity δ : ℂ)

theorem fzzSphereVacuumReplicaLogAction_eq_affine {n : ℕ}
    (distance : Fin n → ℂ) (exponent velocity : Fin n → ℝ) (δ : ℝ) :
    fzzSphereVacuumReplicaLogAction distance exponent velocity δ =
      (∑ i, exponent i * Real.log (Complex.normSq (distance i))) +
        δ * ∑ i, velocity i * Real.log (Complex.normSq (distance i)) := by
  simp only [fzzSphereVacuumReplicaLogAction, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Collision-free logarithmic presentation equals the literal product of absolute powers. -/
theorem fzzSphereVacuumReplicaKernel_eq_prod_rpow {n : ℕ}
    {distance : Fin n → ℂ} (exponent velocity : Fin n → ℝ) (δ : ℝ)
    (hcollision : ∀ i, distance i ≠ 0) :
    fzzSphereVacuumReplicaKernel distance exponent velocity δ =
      ∏ i, Complex.normSq (distance i) ^ (exponent i + δ * velocity i) := by
  rw [fzzSphereVacuumReplicaKernel, fzzSphereVacuumReplicaLogAction, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i hi
  rw [Real.rpow_def_of_pos (Complex.normSq_pos.mpr (hcollision i))]
  congr 1
  ring

theorem fzzSphereVacuumReplicaKernel_pos {n : ℕ}
    (distance : Fin n → ℂ) (exponent velocity : Fin n → ℝ) (δ : ℝ) :
    0 < fzzSphereVacuumReplicaKernel distance exponent velocity δ := by
  exact Real.exp_pos _

/-- Exact first replica variation of every finite HJ absolute-power product. -/
theorem hasDerivAt_fzzSphereVacuumReplicaKernel {n : ℕ}
    (distance : Fin n → ℂ) (exponent velocity : Fin n → ℝ) (δ : ℝ) :
    HasDerivAt (fzzSphereVacuumReplicaKernel distance exponent velocity)
      (fzzSphereVacuumReplicaKernel distance exponent velocity δ *
        ∑ i, velocity i * Real.log (Complex.normSq (distance i))) δ := by
  have haffine := (hasDerivAt_const δ
      (∑ i, exponent i * Real.log (Complex.normSq (distance i)))).add
        ((hasDerivAt_id δ).mul_const
          (∑ i, velocity i * Real.log (Complex.normSq (distance i))))
  have hexp := haffine.exp
  convert hexp using 1
  · funext t
    rw [fzzSphereVacuumReplicaKernel,
      fzzSphereVacuumReplicaLogAction_eq_affine]
    simp
  · rw [fzzSphereVacuumReplicaKernel,
      fzzSphereVacuumReplicaLogAction_eq_affine]
    simp

/-- HJ sphere-vacuum kernel is fixed by conjugation at every replica point. -/
theorem fzzSphereVacuumReplicaComplexKernel_star_self {n : ℕ}
    (distance : Fin n → ℂ) (exponent velocity : Fin n → ℝ) (δ : ℝ) :
    star (fzzSphereVacuumReplicaComplexKernel distance exponent velocity δ) =
      fzzSphereVacuumReplicaComplexKernel distance exponent velocity δ := by
  simp [fzzSphereVacuumReplicaComplexKernel]

theorem fzzSphereVacuumReplicaComplexKernel_im_eq_zero {n : ℕ}
    (distance : Fin n → ℂ) (exponent velocity : Fin n → ℝ) (δ : ℝ) :
    (fzzSphereVacuumReplicaComplexKernel distance exponent velocity δ).im = 0 := by
  simp [fzzSphereVacuumReplicaComplexKernel]

/-- Antiunitary-odd, hence chiral, phase channel of the HJ vacuum kernel. -/
def fzzSphereVacuumReplicaChiralPhase {n : ℕ}
    (distance : Fin n → ℂ) (exponent velocity : Fin n → ℝ) (δ : ℝ) : ℂ :=
  fzzSphereVacuumReplicaComplexKernel distance exponent velocity δ -
    star (fzzSphereVacuumReplicaComplexKernel distance exponent velocity δ)

theorem fzzSphereVacuumReplicaChiralPhase_eq_zero {n : ℕ}
    (distance : Fin n → ℂ) (exponent velocity : Fin n → ℝ) (δ : ℝ) :
    fzzSphereVacuumReplicaChiralPhase distance exponent velocity δ = 0 := by
  rw [fzzSphereVacuumReplicaChiralPhase,
    fzzSphereVacuumReplicaComplexKernel_star_self]
  ring

/-- Halder--Jafferis' symmetry-normalized opposite-winding replica factor. -/
def fzzHJSphereVacuumReplicaFactor (k : ℝ) : ℝ :=
  2 * k / (k - 2)

/-- The factor used below is exactly the symmetry-normalized opposite-charge increment already
extracted from HJ's marked OPE; it is not an independent fitted coefficient. -/
theorem fzzHJSphereVacuumReplicaFactor_mul_eq_markedOppositeIncrement
    {k δ : ℝ} (hk0 : k ≠ 0) (hk2 : k ≠ 2) :
    fzzHJSphereVacuumReplicaFactor k * δ =
      (2 / (k - 2)) *
        (fzzMarkedOppositeWindingOPEExponent k δ -
          fzzMarkedOppositeWindingOPEExponent k 0) := by
  rw [fzzHJSphereVacuumReplicaFactor,
    fzzMarkedOppositeWindingOPEExponent_eq hk0 hk2,
    fzzMarkedOppositeWindingOPEExponent_eq hk0 hk2]
  field_simp [hk2]
  ring

/-- Exact marked part of HJ (3.29).  `baseLog` packages all replica-independent same-charge and
unmarked absolute-value factors; the displayed opposite-charge factors carry (3.31)'s `a(k)`. -/
def fzzHJSphereVacuumMarkedReplicaKernel {n : ℕ}
    (k δ baseLog : ℝ) (oppositeDistance : Fin n → ℂ) : ℝ :=
  Real.exp baseLog *
    fzzSphereVacuumReplicaKernel oppositeDistance (fun _ => 1 - k)
      (fun _ => fzzHJSphereVacuumReplicaFactor k) δ

theorem fzzHJSphereVacuumMarkedReplicaKernel_pos {n : ℕ}
    (k δ baseLog : ℝ) (oppositeDistance : Fin n → ℂ) :
    0 < fzzHJSphereVacuumMarkedReplicaKernel k δ baseLog oppositeDistance := by
  exact mul_pos (Real.exp_pos _)
    (fzzSphereVacuumReplicaKernel_pos oppositeDistance _ _ δ)

/-- Exact first variation of HJ's marked vacuum kernel. -/
theorem hasDerivAt_fzzHJSphereVacuumMarkedReplicaKernel {n : ℕ}
    (k δ baseLog : ℝ) (oppositeDistance : Fin n → ℂ) :
    HasDerivAt (fun t =>
        fzzHJSphereVacuumMarkedReplicaKernel k t baseLog oppositeDistance)
      (fzzHJSphereVacuumMarkedReplicaKernel k δ baseLog oppositeDistance *
        fzzHJSphereVacuumReplicaFactor k *
          ∑ i, Real.log (Complex.normSq (oppositeDistance i))) δ := by
  have h := (hasDerivAt_fzzSphereVacuumReplicaKernel oppositeDistance
    (fun _ => 1 - k) (fun _ => fzzHJSphereVacuumReplicaFactor k) δ).const_mul
      (Real.exp baseLog)
  rw [show (∑ i : Fin n, fzzHJSphereVacuumReplicaFactor k *
      Real.log (Complex.normSq (oppositeDistance i))) =
      fzzHJSphereVacuumReplicaFactor k *
        ∑ i, Real.log (Complex.normSq (oppositeDistance i)) by
    rw [Finset.mul_sum]] at h
  simpa only [fzzHJSphereVacuumMarkedReplicaKernel, mul_assoc] using h

def fzzHJSphereVacuumMarkedReplicaChiralPhase {n : ℕ}
    (k δ baseLog : ℝ) (oppositeDistance : Fin n → ℂ) : ℂ :=
  (fzzHJSphereVacuumMarkedReplicaKernel k δ baseLog oppositeDistance : ℂ) -
    star (fzzHJSphereVacuumMarkedReplicaKernel k δ baseLog oppositeDistance : ℂ)

theorem fzzHJSphereVacuumMarkedReplicaChiralPhase_eq_zero {n : ℕ}
    (k δ baseLog : ℝ) (oppositeDistance : Fin n → ℂ) :
    fzzHJSphereVacuumMarkedReplicaChiralPhase k δ baseLog oppositeDistance = 0 := by
  simp [fzzHJSphereVacuumMarkedReplicaChiralPhase]

/-- A radial-wall selector sourced only by the exact HJ marked sphere-vacuum phase. -/
def FZZHJSphereVacuumMarkedReplicaChiralPhaseWallSelector : Prop :=
  ∃ (n : ℕ) (k : ℝ), 2 < k ∧
    ∃ (distance : ℂ → Fin n → ℂ) (baseLog : ℂ → ℝ) (δ : ℝ) (P : ℂ → Prop),
      ∀ twist : ℂ,
        P (fzzHJSphereVacuumMarkedReplicaChiralPhase k δ (baseLog twist)
          (distance twist)) ↔ twist.im = 0

theorem not_fzzHJSphereVacuumMarkedReplicaChiralPhaseWallSelector :
    ¬ FZZHJSphereVacuumMarkedReplicaChiralPhaseWallSelector := by
  rintro ⟨n, k, hk, distance, baseLog, δ, P, hselector⟩
  have hzero : P 0 := by
    have h := (hselector 0).mpr (by norm_num)
    simpa [fzzHJSphereVacuumMarkedReplicaChiralPhase_eq_zero] using h
  have hI : P (fzzHJSphereVacuumMarkedReplicaChiralPhase k δ (baseLog Complex.I)
      (distance Complex.I)) := by
    simpa [fzzHJSphereVacuumMarkedReplicaChiralPhase_eq_zero] using hzero
  have := (hselector Complex.I).mp hI
  norm_num at this

/-- A wall selector sourced only by the HJ sphere-vacuum chiral phase. -/
def FZZSphereVacuumReplicaChiralPhaseWallSelector : Prop :=
  ∃ (n : ℕ) (distance : ℂ → Fin n → ℂ)
      (exponent velocity : ℂ → Fin n → ℝ) (δ : ℝ) (P : ℂ → Prop),
    ∀ twist : ℂ,
      P (fzzSphereVacuumReplicaChiralPhase (distance twist)
        (exponent twist) (velocity twist) δ) ↔ twist.im = 0

/-- **Sphere-vacuum kernel-phase route kill.** No depth, position dependence, real exponent
motion, replica point, or predicate turns the HJ phase channel into the radial wall. -/
theorem not_fzzSphereVacuumReplicaChiralPhaseWallSelector :
    ¬ FZZSphereVacuumReplicaChiralPhaseWallSelector := by
  rintro ⟨n, distance, exponent, velocity, δ, P, hselector⟩
  have hzero : P 0 := by
    have h := (hselector 0).mpr (by norm_num)
    simpa [fzzSphereVacuumReplicaChiralPhase_eq_zero] using h
  have hI : P (fzzSphereVacuumReplicaChiralPhase (distance Complex.I)
      (exponent Complex.I) (velocity Complex.I) δ) := by
    simpa [fzzSphereVacuumReplicaChiralPhase_eq_zero] using hzero
  have := (hselector Complex.I).mp hI
  norm_num at this

/-- Closed certificate for the killed FZZ-P chain. -/
def FZZCigarParitySphereVacuumReplicaKernelPhaseCollapseNoGo : Prop :=
  (∀ (n : ℕ) (distance : Fin n → ℂ) (exponent velocity : Fin n → ℝ) (δ : ℝ),
      (∀ i, distance i ≠ 0) →
      fzzSphereVacuumReplicaKernel distance exponent velocity δ =
          ∏ i, Complex.normSq (distance i) ^ (exponent i + δ * velocity i) ∧
        0 < fzzSphereVacuumReplicaKernel distance exponent velocity δ ∧
        fzzSphereVacuumReplicaChiralPhase distance exponent velocity δ = 0) ∧
    (∀ (n : ℕ) (k δ baseLog : ℝ) (oppositeDistance : Fin n → ℂ),
      HasDerivAt (fun t =>
          fzzHJSphereVacuumMarkedReplicaKernel k t baseLog oppositeDistance)
        (fzzHJSphereVacuumMarkedReplicaKernel k δ baseLog oppositeDistance *
          fzzHJSphereVacuumReplicaFactor k *
            ∑ i, Real.log (Complex.normSq (oppositeDistance i))) δ) ∧
    (∀ (n : ℕ) (k δ baseLog : ℝ) (oppositeDistance : Fin n → ℂ),
      fzzHJSphereVacuumMarkedReplicaChiralPhase k δ baseLog oppositeDistance = 0) ∧
    ¬ FZZHJSphereVacuumMarkedReplicaChiralPhaseWallSelector

theorem fzzCigarParity_sphereVacuumReplicaKernelPhaseCollapse_noGo :
    FZZCigarParitySphereVacuumReplicaKernelPhaseCollapseNoGo := by
  refine ⟨?_, ?_, ?_,
    not_fzzHJSphereVacuumMarkedReplicaChiralPhaseWallSelector⟩
  intro n distance exponent velocity δ hcollision
  exact ⟨fzzSphereVacuumReplicaKernel_eq_prod_rpow exponent velocity δ hcollision,
    fzzSphereVacuumReplicaKernel_pos distance exponent velocity δ,
    fzzSphereVacuumReplicaChiralPhase_eq_zero distance exponent velocity δ⟩
  intro n k δ baseLog oppositeDistance
  exact hasDerivAt_fzzHJSphereVacuumMarkedReplicaKernel
    k δ baseLog oppositeDistance
  intro n k δ baseLog oppositeDistance
  exact fzzHJSphereVacuumMarkedReplicaChiralPhase_eq_zero
    k δ baseLog oppositeDistance

end

end GaloisForLFunctions.RHTower
