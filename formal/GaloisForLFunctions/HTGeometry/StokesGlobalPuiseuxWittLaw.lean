import GaloisForLFunctions.HTGeometry.StokesUniversalMicrolocalWittLaw
import GaloisForLFunctions.HTGeometry.StokesCartanLorentzCapacity

/-!
# Global coefficient-generated Stokes Witt law

This module fuses an arbitrary nonempty family of common-cover Puiseux coefficient systems over a
curve of arbitrary genus.  Local physical ranks are identified.  The fused form is proved to be a
positive definite sum of terminal and threshold microlocal channels, perturbed by one square of
the common physical rank.  Consequently its negative inertia is at most one.

No rooted tree, contact matrix, cut system, or quadratic-form signature is supplied as input.
-/

open scoped BigOperators

namespace GaloisForLFunctions
namespace IrregularStokes
namespace GlobalPuiseuxWitt

noncomputable section

variable {p : ℕ}
variable {n m K N : Fin (p + 1) → ℕ}

/-- Coefficient-level local irregular data at every marked point. -/
abbrev LocalData (p : ℕ) (n m K N : Fin (p + 1) → ℕ) :=
  (a : Fin (p + 1)) → PuiseuxOrbitCoareaDatum (n a) (m a) (K a) (N a)

/-- All local orbit charges before physical-rank fusion. -/
abbrev GlobalCharge (p : ℕ) (n : Fin (p + 1) → ℕ) :=
  (a : Fin (p + 1)) → Fin (n a) → ℝ

/-- One orbit-coordinate functional. -/
def coordinateLinear {r : ℕ} (i : Fin r) : (Fin r → ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.proj i

@[simp] theorem coordinateLinear_apply {r : ℕ} (i : Fin r) (x : Fin r → ℝ) :
    coordinateLinear i x = x i := rfl

/-- Physical rank as a linear functional on one coefficient-generated local charge space. -/
noncomputable def localRankLinear {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B) : (Fin r → ℝ) →ₗ[ℝ] ℝ where
  toFun := d.toOrbitCoareaDatum.physicalRank
  map_add' := by
    intro x y
    simp [OrbitCoareaDatum.physicalRank, OrbitCoareaDatum.liftCharge,
      Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp [OrbitCoareaDatum.physicalRank, OrbitCoareaDatum.liftCharge,
      Finset.mul_sum]

@[simp] theorem localRankLinear_apply {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B) (x : Fin r → ℝ) :
    localRankLinear d x = d.toOrbitCoareaDatum.physicalRank x := rfl

/-- Linear current in one canonical threshold channel. -/
noncomputable def localCutLinear {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B) (edge : Fin d.edgeCount) :
    (Fin r → ℝ) →ₗ[ℝ] ℝ where
  toFun x := d.toOrbitCoareaDatum.cutCharge x edge
  map_add' := by
    intro x y
    simp [OrbitCoareaDatum.cutCharge, OrbitCoareaDatum.liftCharge,
      add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    simp [OrbitCoareaDatum.cutCharge, OrbitCoareaDatum.liftCharge,
      Finset.mul_sum]
    ring_nf

@[simp] theorem localCutLinear_apply {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B) (edge : Fin d.edgeCount)
    (x : Fin r → ℝ) :
    localCutLinear d edge x = d.toOrbitCoareaDatum.cutCharge x edge := rfl

/-- Positive local form: terminal orbit squares plus all coefficient-generated threshold squares. -/
noncomputable def localPositiveForm {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B) : QuadraticForm ℝ (Fin r → ℝ) :=
  (∑ i, QuadraticMap.sq.comp (coordinateLinear i)) +
    ∑ edge, d.toOrbitCoareaDatum.cuts.length edge •
      (QuadraticMap.sq.comp (localCutLinear d edge))

theorem localPositiveForm_apply {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B) (x : Fin r → ℝ) :
    localPositiveForm d x =
      d.toOrbitCoareaDatum.terminalEnergy x + d.toOrbitCoareaDatum.blockEnergy x := by
  simp only [localPositiveForm, QuadraticMap.add_apply, QuadraticMap.sum_apply,
    QuadraticMap.comp_apply, QuadraticMap.sq_apply, coordinateLinear_apply,
    QuadraticMap.smul_apply, smul_eq_mul, localCutLinear_apply,
    OrbitCoareaDatum.terminalEnergy, OrbitCoareaDatum.blockEnergy,
    OrbitCoareaDatum.cutCharge, pow_two]

theorem localPositiveForm_pos {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B) {x : Fin r → ℝ} (hx : x ≠ 0) :
    0 < localPositiveForm d x := by
  rw [localPositiveForm_apply]
  exact add_pos_of_pos_of_nonneg
    (d.toOrbitCoareaDatum.terminalEnergy_pos hx)
    (d.toOrbitCoareaDatum.blockEnergy_nonneg x)

theorem localPositiveForm_nonneg {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B) (x : Fin r → ℝ) :
    0 ≤ localPositiveForm d x := by
  by_cases hx : x = 0
  · subst x
    simp [localPositiveForm_apply, OrbitCoareaDatum.terminalEnergy,
      OrbitCoareaDatum.blockEnergy, OrbitCoareaDatum.cutCharge,
      OrbitCoareaDatum.liftCharge]
  · exact (localPositiveForm_pos d hx).le

/-- Local coefficient-generated Cartan form. -/
noncomputable def localWittForm {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B) : QuadraticForm ℝ (Fin r → ℝ) :=
  localPositiveForm d -
    (d.toOrbitCoareaDatum.cuts.root - 1) •
      (QuadraticMap.sq.comp (localRankLinear d))

theorem localWittForm_apply {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B) (x : Fin r → ℝ) :
    localWittForm d x = d.toOrbitCoareaDatum.cartanQuadratic x := by
  rw [localWittForm, QuadraticMap.sub_apply, QuadraticMap.smul_apply,
    QuadraticMap.comp_apply, QuadraticMap.sq_apply, localPositiveForm_apply]
  simp only [smul_eq_mul, localRankLinear_apply]
  simpa [pow_two] using
    (d.toOrbitCoareaDatum.cartanQuadratic_eq_positive_sub_onePort x).symm

/-- Global charges whose physical ranks agree at all marked points. -/
noncomputable def compatibleCharges (d : LocalData p n m K N) :
    Submodule ℝ (GlobalCharge p n) where
  carrier := {x | ∀ a, localRankLinear (d a) (x a) = localRankLinear (d 0) (x 0)}
  zero_mem' := by
    intro a
    change localRankLinear (d a) 0 = localRankLinear (d 0) 0
    rw [map_zero, map_zero]
  add_mem' := by
    intro x y hx hy a
    change localRankLinear (d a) (x a + y a) =
      localRankLinear (d 0) (x 0 + y 0)
    rw [map_add, map_add]
    rw [hx a, hy a]
  smul_mem' := by
    intro c x hx a
    change localRankLinear (d a) (c • x a) =
      localRankLinear (d 0) (c • x 0)
    rw [map_smul, map_smul]
    rw [hx a]

/-- Projection to one local charge space. -/
noncomputable def localProjection (d : LocalData p n m K N) (a : Fin (p + 1)) :
    compatibleCharges d →ₗ[ℝ] (Fin (n a) → ℝ) :=
  (LinearMap.proj a).comp (compatibleCharges d).subtype

@[simp] theorem localProjection_apply (d : LocalData p n m K N) (a : Fin (p + 1))
    (x : compatibleCharges d) : localProjection d a x = x.1 a := rfl

/-- Unique common physical-rank channel after fusion. -/
noncomputable def commonRankLinear (d : LocalData p n m K N) :
    compatibleCharges d →ₗ[ℝ] ℝ :=
  (localRankLinear (d 0)).comp (localProjection d 0)

@[simp] theorem commonRankLinear_apply (d : LocalData p n m K N)
    (x : compatibleCharges d) :
    commonRankLinear d x = localRankLinear (d 0) (x.1 0) := rfl

theorem compatible_localRank (d : LocalData p n m K N) (x : compatibleCharges d)
    (a : Fin (p + 1)) :
    localRankLinear (d a) (x.1 a) = commonRankLinear d x := x.2 a

/-- Sum of all positive terminal and threshold channels after fusion. -/
noncomputable def globalPositiveForm (d : LocalData p n m K N) :
    QuadraticForm ℝ (compatibleCharges d) :=
  ∑ a, (localPositiveForm (d a)).comp (localProjection d a)

/-- Curve fusion coefficient before adding local Stokes root defects. -/
def fusionCoefficient (genus punctures : ℕ) : ℝ :=
  2 * (1 - (genus : ℝ) - (punctures : ℝ))

/-- Full coefficient-generated fused Stokes form. -/
noncomputable def globalWittForm (genus : ℕ) (d : LocalData p n m K N) :
    QuadraticForm ℝ (compatibleCharges d) :=
  (∑ a, (localWittForm (d a)).comp (localProjection d a)) +
    fusionCoefficient genus (p + 1) •
      (QuadraticMap.sq.comp (commonRankLinear d))

/-- Coefficient of the sole global rank square. -/
noncomputable def globalRankCoefficient (genus : ℕ)
    (d : LocalData p n m K N) : ℝ :=
  fusionCoefficient genus (p + 1) -
    ∑ a, ((d a).toOrbitCoareaDatum.cuts.root - 1)

/-- **Global coefficient-generated Witt decomposition.**  Arbitrary genus and all marked points
share one physical-rank square; every remaining coefficient-generated channel is positive. -/
theorem globalWittForm_eq_positive_add_oneRank
    (genus : ℕ) (d : LocalData p n m K N) (x : compatibleCharges d) :
    globalWittForm genus d x = globalPositiveForm d x +
      globalRankCoefficient genus d * commonRankLinear d x ^ 2 := by
  rw [globalWittForm, QuadraticMap.add_apply, QuadraticMap.sum_apply,
    QuadraticMap.smul_apply, QuadraticMap.comp_apply, QuadraticMap.sq_apply,
    globalPositiveForm, QuadraticMap.sum_apply]
  simp only [QuadraticMap.comp_apply, localWittForm, QuadraticMap.sub_apply,
    QuadraticMap.smul_apply, QuadraticMap.sq_apply, smul_eq_mul,
    localProjection_apply, globalRankCoefficient]
  have hrank : ∀ a, localRankLinear (d a) (x.1 a) = commonRankLinear d x :=
    compatible_localRank d x
  simp_rw [hrank]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring_nf

theorem globalPositiveForm_nonneg (d : LocalData p n m K N)
    (x : compatibleCharges d) :
    0 ≤ globalPositiveForm d x := by
  rw [globalPositiveForm, QuadraticMap.sum_apply]
  apply Finset.sum_nonneg
  intro a _
  exact localPositiveForm_nonneg (d a) (x.1 a)

theorem globalPositiveForm_pos (d : LocalData p n m K N)
    {x : compatibleCharges d} (hx : x ≠ 0) :
    0 < globalPositiveForm d x := by
  have hlocal : ∃ a, x.1 a ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    apply Subtype.ext
    funext a i
    exact congrFun (h a) i
  obtain ⟨a, ha⟩ := hlocal
  rw [globalPositiveForm, QuadraticMap.sum_apply]
  apply Finset.sum_pos'
  · intro b _
    exact localPositiveForm_nonneg (d b) (x.1 b)
  · exact ⟨a, Finset.mem_univ _, localPositiveForm_pos (d a) ha⟩

/-- The common-rank-zero hyperplane is positive definite for arbitrary genus and punctures. -/
theorem globalWittForm_pos_of_commonRank_eq_zero
    (genus : ℕ) (d : LocalData p n m K N) {x : compatibleCharges d}
    (hrank : commonRankLinear d x = 0) (hx : x ≠ 0) :
    0 < globalWittForm genus d x := by
  rw [globalWittForm_eq_positive_add_oneRank genus d x, hrank]
  simpa using globalPositiveForm_pos d hx

/-- **Global Stokes Witt-index law.**  For coefficient-generated ramified irregular data on an
arbitrary marked curve, the fused Stokes form has at most one negative direction. -/
theorem globalWittForm_sigNeg_le_one (genus : ℕ)
    (d : LocalData p n m K N) :
    sigNeg (globalWittForm genus d) ≤ 1 := by
  let coeff : ℝ := globalRankCoefficient genus d
  let ell : compatibleCharges d →ₗ[ℝ] ℝ :=
    (LinearMap.lsmul ℝ ℝ (Real.sqrt (max 0 (-coeff)))).comp (commonRankLinear d)
  apply sigNeg_le_one_of_add_sq_nonneg (globalWittForm genus d) ell
  intro x
  rw [globalWittForm_eq_positive_add_oneRank]
  change 0 ≤ globalPositiveForm d x + coeff * commonRankLinear d x ^ 2 +
    (Real.sqrt (max 0 (-coeff)) * commonRankLinear d x) ^ 2
  rw [mul_pow, Real.sq_sqrt (le_max_left 0 (-coeff))]
  by_cases hcoeff : 0 ≤ coeff
  · rw [max_eq_left (neg_nonpos.mpr hcoeff)]
    nlinarith [globalPositiveForm_nonneg d x,
      mul_nonneg hcoeff (sq_nonneg (commonRankLinear d x))]
  · rw [max_eq_right (neg_nonneg.mpr (le_of_not_ge hcoeff))]
    nlinarith [globalPositiveForm_nonneg d x]

/-! ## Global multi-Rees cone -/

/-- Independent threshold parameters at every marked point. -/
abbrev ReesParameter (d : LocalData p n m K N) :=
  (a : Fin (p + 1)) → Fin (d a).edgeCount → ℝ

/-- Rees deformation of one local positive form. -/
noncomputable def localReesPositiveForm {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B)
    (parameter : Fin d.edgeCount → ℝ) : QuadraticForm ℝ (Fin r → ℝ) :=
  (∑ i, QuadraticMap.sq.comp (coordinateLinear i)) +
    ∑ edge, (parameter edge * d.toOrbitCoareaDatum.cuts.length edge) •
      (QuadraticMap.sq.comp (localCutLinear d edge))

theorem localReesPositiveForm_apply {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B)
    (parameter : Fin d.edgeCount → ℝ) (x : Fin r → ℝ) :
    localReesPositiveForm d parameter x =
      d.toOrbitCoareaDatum.terminalEnergy x +
        d.toOrbitCoareaDatum.reesBlockEnergy parameter x := by
  simp only [localReesPositiveForm, QuadraticMap.add_apply, QuadraticMap.sum_apply,
    QuadraticMap.comp_apply, QuadraticMap.sq_apply, coordinateLinear_apply,
    QuadraticMap.smul_apply, smul_eq_mul, localCutLinear_apply,
    OrbitCoareaDatum.terminalEnergy, OrbitCoareaDatum.reesBlockEnergy, pow_two]

theorem localReesPositiveForm_one {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B) :
    localReesPositiveForm d (fun _ => 1) = localPositiveForm d := by
  apply QuadraticMap.ext
  intro x
  rw [localReesPositiveForm_apply, localPositiveForm_apply,
    d.toOrbitCoareaDatum.reesBlockEnergy_one]

theorem localReesPositiveForm_nonneg {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B)
    {parameter : Fin d.edgeCount → ℝ}
    (hparameter : ∀ edge, 0 ≤ parameter edge) (x : Fin r → ℝ) :
    0 ≤ localReesPositiveForm d parameter x := by
  rw [localReesPositiveForm_apply]
  apply add_nonneg
  · simp only [OrbitCoareaDatum.terminalEnergy]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  · exact d.toOrbitCoareaDatum.reesBlockEnergy_nonneg hparameter x

theorem localReesPositiveForm_pos {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B)
    {parameter : Fin d.edgeCount → ℝ}
    (hparameter : ∀ edge, 0 ≤ parameter edge) {x : Fin r → ℝ} (hx : x ≠ 0) :
    0 < localReesPositiveForm d parameter x := by
  rw [localReesPositiveForm_apply]
  exact add_pos_of_pos_of_nonneg (d.toOrbitCoareaDatum.terminalEnergy_pos hx)
    (d.toOrbitCoareaDatum.reesBlockEnergy_nonneg hparameter x)

/-- Rees-deformed local Witt form; the global rank square is parameter-independent. -/
noncomputable def localReesWittForm {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B)
    (parameter : Fin d.edgeCount → ℝ) : QuadraticForm ℝ (Fin r → ℝ) :=
  localReesPositiveForm d parameter -
    (d.toOrbitCoareaDatum.cuts.root - 1) •
      (QuadraticMap.sq.comp (localRankLinear d))

theorem localReesWittForm_one {r s A B : ℕ}
    (d : PuiseuxOrbitCoareaDatum r s A B) :
    localReesWittForm d (fun _ => 1) = localWittForm d := by
  rw [localReesWittForm, localWittForm, localReesPositiveForm_one]

/-- Sum of all Rees-deformed positive local channels. -/
noncomputable def globalReesPositiveForm (d : LocalData p n m K N)
    (parameter : ReesParameter d) : QuadraticForm ℝ (compatibleCharges d) :=
  ∑ a, (localReesPositiveForm (d a) (parameter a)).comp (localProjection d a)

/-- Fused global Stokes form over the full multi-Rees parameter space. -/
noncomputable def globalReesWittForm (genus : ℕ) (d : LocalData p n m K N)
    (parameter : ReesParameter d) : QuadraticForm ℝ (compatibleCharges d) :=
  (∑ a, (localReesWittForm (d a) (parameter a)).comp (localProjection d a)) +
    fusionCoefficient genus (p + 1) •
      (QuadraticMap.sq.comp (commonRankLinear d))

/-- Unit specialization is exactly the undeformed fused form. -/
theorem globalReesWittForm_one (genus : ℕ) (d : LocalData p n m K N) :
    globalReesWittForm genus d (fun _ _ => 1) = globalWittForm genus d := by
  rw [globalReesWittForm, globalWittForm]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [localReesWittForm_one]

/-- Global Rees decomposition: parameters move positive local channels and leave the unique rank
coefficient fixed. -/
theorem globalReesWittForm_eq_positive_add_oneRank
    (genus : ℕ) (d : LocalData p n m K N) (parameter : ReesParameter d)
    (x : compatibleCharges d) :
    globalReesWittForm genus d parameter x = globalReesPositiveForm d parameter x +
      globalRankCoefficient genus d * commonRankLinear d x ^ 2 := by
  rw [globalReesWittForm, QuadraticMap.add_apply, QuadraticMap.sum_apply,
    QuadraticMap.smul_apply, QuadraticMap.comp_apply, QuadraticMap.sq_apply,
    globalReesPositiveForm, QuadraticMap.sum_apply]
  simp only [QuadraticMap.comp_apply, localReesWittForm, QuadraticMap.sub_apply,
    QuadraticMap.smul_apply, QuadraticMap.sq_apply, smul_eq_mul,
    localProjection_apply, globalRankCoefficient]
  have hrank : ∀ a, localRankLinear (d a) (x.1 a) = commonRankLinear d x :=
    compatible_localRank d x
  simp_rw [hrank]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring_nf

theorem globalReesPositiveForm_nonneg (d : LocalData p n m K N)
    (parameter : ReesParameter d)
    (hparameter : ∀ a edge, 0 ≤ parameter a edge) (x : compatibleCharges d) :
    0 ≤ globalReesPositiveForm d parameter x := by
  rw [globalReesPositiveForm, QuadraticMap.sum_apply]
  apply Finset.sum_nonneg
  intro a _
  exact localReesPositiveForm_nonneg (d a) (hparameter a) (x.1 a)

/-- **Global Rees Witt-index law.** Every nonnegative multi-Rees specialization, including any
simultaneous contraction of threshold intervals, has at most one negative direction. -/
theorem globalReesWittForm_sigNeg_le_one
    (genus : ℕ) (d : LocalData p n m K N) (parameter : ReesParameter d)
    (hparameter : ∀ a edge, 0 ≤ parameter a edge) :
    sigNeg (globalReesWittForm genus d parameter) ≤ 1 := by
  let coeff : ℝ := globalRankCoefficient genus d
  let ell : compatibleCharges d →ₗ[ℝ] ℝ :=
    (LinearMap.lsmul ℝ ℝ (Real.sqrt (max 0 (-coeff)))).comp (commonRankLinear d)
  apply sigNeg_le_one_of_add_sq_nonneg (globalReesWittForm genus d parameter) ell
  intro x
  rw [globalReesWittForm_eq_positive_add_oneRank]
  change 0 ≤ globalReesPositiveForm d parameter x + coeff * commonRankLinear d x ^ 2 +
    (Real.sqrt (max 0 (-coeff)) * commonRankLinear d x) ^ 2
  rw [mul_pow, Real.sq_sqrt (le_max_left 0 (-coeff))]
  by_cases hcoeff : 0 ≤ coeff
  · rw [max_eq_left (neg_nonpos.mpr hcoeff)]
    nlinarith [globalReesPositiveForm_nonneg d parameter hparameter x,
      mul_nonneg hcoeff (sq_nonneg (commonRankLinear d x))]
  · rw [max_eq_right (neg_nonneg.mpr (le_of_not_ge hcoeff))]
    nlinarith [globalReesPositiveForm_nonneg d parameter hparameter x]

end
end GlobalPuiseuxWitt
end IrregularStokes
end GaloisForLFunctions
