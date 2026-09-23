import GaloisForLFunctions.HTGeometry.PhaseSeedCollisionMoments
import GaloisForLFunctions.HTGeometry.TorusTrigPoincare

/-!
# The collision of a uniform phase seed concentrates

The unnormalized collision of an independent-phase seed against an orthonormal family is a
character combination of the phases, so the torus spectral gap bounds its variance by the total
mean square of its coordinate derivatives.  Each such derivative is twice the imaginary part of one
dual coordinate of the cubed amplitude vector; orthonormality turns the sum of their squares into
the sixth moment of the amplitudes, and the replica moment bound evaluates that.  The variance of
the collision is therefore at most ninety-six times the family size.
-/

open MeasureTheory Complex UnitAddTorus Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance phaseSeedCollisionVarianceMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance phaseSeedCollisionVarianceIsAddHaarMeasure :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local instance phaseSeedCollisionVarianceIsProbabilityMeasure :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

set_option linter.unusedSectionVars false

section Derivative

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The coordinate derivative of a product. -/
theorem pderiv_mul_of_hasFDerivAt {G H : (d → ℝ) → ℂ} {G' H' : (d → ℝ) →L[ℝ] ℂ} {x : d → ℝ}
    (hG : HasFDerivAt G G' x) (hH : HasFDerivAt H H' x) (b : d) :
    pderiv b (fun y => G y * H y) x = G x * pderiv b H x + H x * pderiv b G x := by
  have hmul : HasFDerivAt (fun y => G y * H y) (G x • H' + H x • G') x := hG.mul hH
  simp only [pderiv]
  rw [hmul.fderiv, hG.fderiv, hH.fderiv]
  simp

/-- The coordinate derivative of a finite sum. -/
theorem pderiv_finsetSum_of_hasFDerivAt {ι' : Type*} (s : Finset ι') {A : ι' → (d → ℝ) → ℂ}
    {A' : ι' → (d → ℝ) →L[ℝ] ℂ} {x : d → ℝ} (h : ∀ i ∈ s, HasFDerivAt (A i) (A' i) x) (b : d) :
    pderiv b (fun y => ∑ i ∈ s, A i y) x = ∑ i ∈ s, pderiv b (A i) x := by
  rw [pderiv, (HasFDerivAt.fun_sum h).fderiv]
  rw [FunLike.coe_sum, Finset.sum_apply]
  exact Finset.sum_congr rfl fun i hi => by rw [pderiv, (h i hi).fderiv]

end Derivative

section Quartic

variable {α ι : Type*} [Fintype α] [DecidableEq α] [Fintype ι] [DecidableEq ι]

/-- The pairing of the unit-weight phase orbit with one family vector. -/
def phaseAmp (e : ι → α → ℂ) (j : ι) : (α → ℝ) → ℂ :=
  trigLift (Finset.univ : Finset α) (fun a => -(Pi.single a 1)) (e j)

/-- The conjugate pairing, again a character combination. -/
def phaseAmpConj (e : ι → α → ℂ) (j : ι) : (α → ℝ) → ℂ :=
  trigLift (Finset.univ : Finset α) (fun a => Pi.single a 1) (fun a => (starRingEnd ℂ) (e j a))

theorem phaseAmpConj_eq (e : ι → α → ℂ) (j : ι) (x : α → ℝ) :
    phaseAmpConj e j x = (starRingEnd ℂ) (phaseAmp e j x) := by
  rw [phaseAmpConj, phaseAmp, trigLift, trigLift, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, charLift_neg_index, Complex.conj_conj]

theorem phaseAmp_eq_inner (e : ι → α → ℂ) (j : ι) (x : α → ℝ) :
    phaseAmp e j x = finiteComplexInner (torusReplicaPhaseOrbit (fun _ => (1 : ℝ)) x) (e j) := by
  rw [finiteComplexInner_torusReplicaPhaseOrbit, phaseAmp, trigLift]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Real.sqrt_one]
  push_cast
  ring

theorem normSq_phaseAmp (e : ι → α → ℂ) (j : ι) (x : α → ℝ) :
    ‖phaseAmp e j x‖ ^ (2 : ℕ) = finitePureStateFidelity (torusReplicaPhaseOrbit (fun _ => (1 : ℝ)) x) (e j) := by
  rw [finitePureStateFidelity, phaseAmp_eq_inner]

theorem hasFDerivAt_phaseAmp (e : ι → α → ℂ) (j : ι) (x : α → ℝ) :
    HasFDerivAt (phaseAmp e j)
      (∑ a : α, (e j a * charLift (-(Pi.single a 1)) x) • charPhase (-(Pi.single a 1))) x :=
  hasFDerivAt_trigLift _ _ _ x

theorem hasFDerivAt_phaseAmpConj (e : ι → α → ℂ) (j : ι) (x : α → ℝ) :
    HasFDerivAt (phaseAmpConj e j)
      (∑ a : α, ((starRingEnd ℂ) (e j a) * charLift (Pi.single a 1) x) •
        charPhase (Pi.single a 1)) x :=
  hasFDerivAt_trigLift _ _ _ x

theorem pderiv_phaseAmp (e : ι → α → ℂ) (j : ι) (b : α) (x : α → ℝ) :
    pderiv b (phaseAmp e j) x =
      -(2 * Real.pi * I) * (e j b * charLift (-(Pi.single b 1)) x) := by
  classical
  rw [phaseAmp, pderiv_trigLift, trigLift, Finset.sum_eq_single b]
  · rw [Pi.neg_apply, Pi.single_eq_same]
    push_cast
    ring
  · intro a _ hab
    rw [Pi.neg_apply, Pi.single_eq_of_ne (Ne.symm hab)]
    push_cast
    ring
  · intro hcon
    exact absurd (Finset.mem_univ b) hcon

theorem pderiv_phaseAmpConj (e : ι → α → ℂ) (j : ι) (b : α) (x : α → ℝ) :
    pderiv b (phaseAmpConj e j) x =
      (2 * Real.pi * I) * ((starRingEnd ℂ) (e j b) * charLift (Pi.single b 1) x) := by
  classical
  rw [phaseAmpConj, pderiv_trigLift, trigLift, Finset.sum_eq_single b]
  · rw [Pi.single_eq_same]
    push_cast
    ring
  · intro a _ hab
    rw [Pi.single_eq_of_ne (Ne.symm hab)]
    push_cast
    ring
  · intro hcon
    exact absurd (Finset.mem_univ b) hcon

/-- The unnormalized collision of the seed with an orthonormal family. -/
def quarticSum (e : ι → α → ℂ) : (α → ℝ) → ℂ :=
  fun x => ∑ j, (phaseAmp e j x * phaseAmpConj e j x) ^ (2 : ℕ)

theorem quarticSum_eq_ofReal (e : ι → α → ℂ) (x : α → ℝ) :
    quarticSum e x = ((∑ j, ‖phaseAmp e j x‖ ^ (4 : ℕ) : ℝ) : ℂ) := by
  rw [quarticSum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [phaseAmpConj_eq, Complex.mul_conj]
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Complex.sq_norm]
  push_cast
  ring

/-- The frequency of one quartic term. -/
def quarticFreq (p : (α × α) × (α × α)) : α → ℤ :=
  -(Pi.single p.1.1 1) + -(Pi.single p.1.2 1) + (Pi.single p.2.1 1 + Pi.single p.2.2 1)

/-- The coefficient of one quartic term. -/
def quarticCoeff (e : ι → α → ℂ) (q : ι × ((α × α) × (α × α))) : ℂ :=
  e q.1 q.2.1.1 * e q.1 q.2.1.2 *
    ((starRingEnd ℂ) (e q.1 q.2.2.1) * (starRingEnd ℂ) (e q.1 q.2.2.2))

theorem sq_phaseAmp (e : ι → α → ℂ) (j : ι) (x : α → ℝ) :
    (phaseAmp e j x) ^ (2 : ℕ) =
      ∑ p : α × α, (e j p.1 * e j p.2) *
        charLift (-(Pi.single p.1 1) + -(Pi.single p.2 1)) x := by
  rw [sq, phaseAmp, trigLift, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [charLift_add_index]
  ring

theorem sq_phaseAmpConj (e : ι → α → ℂ) (j : ι) (x : α → ℝ) :
    (phaseAmpConj e j x) ^ (2 : ℕ) =
      ∑ p : α × α, ((starRingEnd ℂ) (e j p.1) * (starRingEnd ℂ) (e j p.2)) *
        charLift (Pi.single p.1 1 + Pi.single p.2 1) x := by
  rw [sq, phaseAmpConj, trigLift, Finset.sum_mul_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [charLift_add_index]
  ring

/-- **The collision is a character combination.** -/
theorem quarticSum_eq_trigLift (e : ι → α → ℂ) :
    quarticSum e = trigLift (Finset.univ : Finset (ι × ((α × α) × (α × α))))
      (fun q => quarticFreq q.2) (quarticCoeff e) := by
  classical
  funext x
  rw [quarticSum, trigLift, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hR : (∑ p : (α × α) × (α × α), quarticCoeff e (j, p) * charLift (quarticFreq p) x) =
      ∑ p : α × α, ∑ q : α × α,
        quarticCoeff e (j, (p, q)) * charLift (quarticFreq (p, q)) x :=
    Fintype.sum_prod_type _
  rw [hR, mul_pow, sq_phaseAmp, sq_phaseAmpConj, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun q _ => ?_
  have hfreq : charLift (quarticFreq (p, q)) x =
      charLift (-(Pi.single p.1 1)) x * charLift (-(Pi.single p.2 1)) x *
        charLift (Pi.single q.1 1 + Pi.single q.2 1) x := by
    rw [quarticFreq, charLift_add_index, charLift_add_index]
  rw [hfreq, quarticCoeff, charLift_add_index (-(Pi.single p.1 1)) (-(Pi.single p.2 1)) x]
  ring

/-- The cubed amplitude of one family vector. -/
def cubedAmp (e : ι → α → ℂ) (j : ι) (x : α → ℝ) : ℂ :=
  phaseAmp e j x * phaseAmpConj e j x * phaseAmp e j x

theorem norm_cubedAmp (e : ι → α → ℂ) (j : ι) (x : α → ℝ) :
    ‖cubedAmp e j x‖ = ‖phaseAmp e j x‖ ^ (3 : ℕ) := by
  rw [cubedAmp, norm_mul, norm_mul, phaseAmpConj_eq, RCLike.norm_conj]
  ring

/-- The dual coordinate of the cubed amplitude vector. -/
def dualAmp (e : ι → α → ℂ) (b : α) (x : α → ℝ) : ℂ :=
  charLift (Pi.single b 1) x * ∑ j, cubedAmp e j x * (starRingEnd ℂ) (e j b)

theorem dualAmp_eq_sum (e : ι → α → ℂ) (b : α) (x : α → ℝ) :
    dualAmp e b x =
      ∑ j, cubedAmp e j x * (starRingEnd ℂ) (e j b) * charLift (Pi.single b 1) x := by
  rw [dualAmp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem norm_dualAmp (e : ι → α → ℂ) (b : α) (x : α → ℝ) :
    ‖dualAmp e b x‖ = ‖∑ j, cubedAmp e j x * (starRingEnd ℂ) (e j b)‖ := by
  rw [dualAmp, norm_mul, norm_charLift, one_mul]

/-- **The coordinate derivative of the collision.**  It is twice the imaginary part of one dual
coordinate of the cubed amplitude vector. -/
theorem pderiv_quarticSum (e : ι → α → ℂ) (b : α) (x : α → ℝ) :
    pderiv b (quarticSum e) x =
      (4 * Real.pi * I) * (dualAmp e b x - (starRingEnd ℂ) (dualAmp e b x)) := by
  classical
  have hq : quarticSum e = fun y => ∑ j : ι, (phaseAmp e j y * phaseAmpConj e j y) *
      (phaseAmp e j y * phaseAmpConj e j y) := by
    funext y
    rw [quarticSum]
    exact Finset.sum_congr rfl fun j _ => pow_two _
  have hprod : ∀ j : ι, HasFDerivAt (fun y => phaseAmp e j y * phaseAmpConj e j y)
      (phaseAmp e j x • (∑ a : α, ((starRingEnd ℂ) (e j a) * charLift (Pi.single a 1) x) •
          charPhase (Pi.single a 1)) +
        phaseAmpConj e j x • (∑ a : α, (e j a * charLift (-(Pi.single a 1)) x) •
          charPhase (-(Pi.single a 1)))) x :=
    fun j => (hasFDerivAt_phaseAmp e j x).mul (hasFDerivAt_phaseAmpConj e j x)
  have hsummand : ∀ j : ι, HasFDerivAt (fun y => (phaseAmp e j y * phaseAmpConj e j y) *
      (phaseAmp e j y * phaseAmpConj e j y)) _ x := fun j => (hprod j).mul (hprod j)
  have hterm : ∀ j : ι, pderiv b (fun y => (phaseAmp e j y * phaseAmpConj e j y) *
        (phaseAmp e j y * phaseAmpConj e j y)) x =
      (4 * Real.pi * I) *
        (cubedAmp e j x * (starRingEnd ℂ) (e j b) * charLift (Pi.single b 1) x -
          (starRingEnd ℂ) (cubedAmp e j x * (starRingEnd ℂ) (e j b) *
            charLift (Pi.single b 1) x)) := by
    intro j
    rw [pderiv_mul_of_hasFDerivAt (hprod j) (hprod j) b,
      pderiv_mul_of_hasFDerivAt (hasFDerivAt_phaseAmp e j x) (hasFDerivAt_phaseAmpConj e j x) b,
      pderiv_phaseAmp, pderiv_phaseAmpConj, cubedAmp, phaseAmpConj_eq]
    simp only [map_mul, Complex.conj_conj, charLift_neg_index]
    ring
  rw [hq, pderiv_finsetSum_of_hasFDerivAt _ (fun j _ => hsummand j) b,
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hterm j, ← Finset.mul_sum,
    Finset.sum_sub_distrib, ← map_sum, ← dualAmp_eq_sum]

theorem norm_pderiv_quarticSum_le (e : ι → α → ℂ) (b : α) (x : α → ℝ) :
    ‖pderiv b (quarticSum e) x‖ ≤
      8 * Real.pi * ‖∑ j, cubedAmp e j x * (starRingEnd ℂ) (e j b)‖ := by
  rw [pderiv_quarticSum, norm_mul]
  have hc : ‖(4 * Real.pi * I : ℂ)‖ = 4 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_nonneg]
    norm_num
  have hd : ‖dualAmp e b x - (starRingEnd ℂ) (dualAmp e b x)‖ ≤ 2 * ‖dualAmp e b x‖ := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [RCLike.norm_conj]
    ring_nf
    exact le_rfl
  rw [hc, norm_dualAmp] at *
  nlinarith [norm_nonneg (∑ j, cubedAmp e j x * (starRingEnd ℂ) (e j b)),
    Real.pi_pos.le, norm_nonneg (dualAmp e b x)]

/-- **Orthonormal dual coordinates preserve the square sum.** -/
theorem sum_normSq_dual (e : ι → α → ℂ)
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0) (w : ι → ℂ) :
    (∑ b : α, ‖∑ j, w j * (starRingEnd ℂ) (e j b)‖ ^ (2 : ℕ)) = ∑ j, ‖w j‖ ^ (2 : ℕ) := by
  classical
  have hb : ∀ b : α, (((‖∑ j, w j * (starRingEnd ℂ) (e j b)‖ ^ (2 : ℕ) : ℝ)) : ℂ) =
      ∑ j, ∑ k, (w j * (starRingEnd ℂ) (w k)) * ((starRingEnd ℂ) (e j b) * e k b) := by
    intro b
    rw [Complex.sq_norm, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, Complex.conj_conj]
    ring
  have hswap : (∑ b : α, ∑ j : ι, ∑ k : ι,
        (w j * (starRingEnd ℂ) (w k)) * ((starRingEnd ℂ) (e j b) * e k b)) =
      ∑ j : ι, ∑ k : ι, (w j * (starRingEnd ℂ) (w k)) * finiteComplexInner (e j) (e k) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [finiteComplexInner, Finset.mul_sum]
  have hdiag : (∑ j : ι, ∑ k : ι, (w j * (starRingEnd ℂ) (w k)) * finiteComplexInner (e j) (e k)) =
      ∑ j : ι, ((‖w j‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single j]
    · rw [horth j j, if_pos rfl, mul_one, Complex.mul_conj, Complex.sq_norm]
    · intro k _ hkj
      rw [horth j k, if_neg (Ne.symm hkj), mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ j) hcon
  have hcast : (((∑ b : α, ‖∑ j, w j * (starRingEnd ℂ) (e j b)‖ ^ (2 : ℕ) : ℝ)) : ℂ) =
      ((∑ j : ι, ‖w j‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl fun b (_ : b ∈ Finset.univ) => hb b, hswap, hdiag,
      Complex.ofReal_sum]
  exact_mod_cast hcast

theorem sum_normSq_e_le_one (e : ι → α → ℂ)
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0) (j : ι) :
    (∑ a, ‖e j a‖ ^ (2 : ℕ)) ≤ 1 := by
  have h := horth j j
  rw [if_pos rfl, finiteComplexInner] at h
  have hre : (∑ a, ((‖e j a‖ ^ (2 : ℕ) : ℝ) : ℂ)) = (1 : ℂ) := by
    rw [← h]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.sq_norm, ← Complex.mul_conj]
    ring
  rw [← Complex.ofReal_sum] at hre
  have : (∑ a, ‖e j a‖ ^ (2 : ℕ)) = 1 := by exact_mod_cast hre
  exact le_of_eq this

/-- **The total derivative energy is the sixth moment.** -/
theorem sum_normSq_pderiv_quarticSum_le (e : ι → α → ℂ)
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0) (x : α → ℝ) :
    (∑ b : α, ‖pderiv b (quarticSum e) x‖ ^ (2 : ℕ)) ≤
      64 * Real.pi ^ (2 : ℕ) * ∑ j, ‖phaseAmp e j x‖ ^ (6 : ℕ) := by
  classical
  have hstep : ∀ b : α, ‖pderiv b (quarticSum e) x‖ ^ (2 : ℕ) ≤
      64 * Real.pi ^ (2 : ℕ) * ‖∑ j, cubedAmp e j x * (starRingEnd ℂ) (e j b)‖ ^ (2 : ℕ) := by
    intro b
    have h := norm_pderiv_quarticSum_le e b x
    have hnn : (0 : ℝ) ≤ 8 * Real.pi * ‖∑ j, cubedAmp e j x * (starRingEnd ℂ) (e j b)‖ := by
      have := Real.pi_pos.le
      positivity
    nlinarith [norm_nonneg (pderiv b (quarticSum e) x)]
  refine le_trans (Finset.sum_le_sum fun b _ => hstep b) ?_
  rw [← Finset.mul_sum, sum_normSq_dual e horth (fun j => cubedAmp e j x)]
  refine mul_le_mul_of_nonneg_left (le_of_eq (Finset.sum_congr rfl fun j _ => ?_)) (by positivity)
  rw [norm_cubedAmp, ← pow_mul]

theorem integrableOn_box_normPow_trigLift {ι' : Type*} (P : Finset ι') (ν : ι' → (α → ℤ))
    (a : ι' → ℂ) (r : ℕ) :
    IntegrableOn (fun x => ‖trigLift P ν a x‖ ^ r) (torusBox α) volume := by
  haveI := isFiniteMeasure_restrict_torusBox (d := α)
  refine Integrable.of_bound (((continuous_trigLift P ν a).norm.pow r).aestronglyMeasurable)
    ((∑ p ∈ P, ‖a p‖) ^ r) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ r
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_mul, norm_charLift, mul_one]

theorem integrableOn_box_normPow_phaseAmp (e : ι → α → ℂ) (j : ι) (r : ℕ) :
    IntegrableOn (fun x => ‖phaseAmp e j x‖ ^ r) (torusBox α) volume :=
  integrableOn_box_normPow_trigLift _ _ _ r

theorem integrableOn_box_normSq_pderiv_quarticSum (e : ι → α → ℂ) (b : α) :
    IntegrableOn (fun x => ‖pderiv b (quarticSum e) x‖ ^ (2 : ℕ)) (torusBox α) volume := by
  have hrw : (fun x => ‖pderiv b (quarticSum e) x‖ ^ (2 : ℕ)) =
      fun x => ‖trigLift (Finset.univ : Finset (ι × ((α × α) × (α × α))))
        (fun q => quarticFreq q.2)
        (fun q => (2 * Real.pi * I * ((quarticFreq q.2) b : ℂ)) * quarticCoeff e q) x‖ ^ (2 : ℕ) := by
    funext x
    rw [quarticSum_eq_trigLift, pderiv_trigLift]
  rw [hrw]
  exact integrableOn_box_normPow_trigLift _ _ _ 2

/-- **The collision of a uniform phase seed concentrates.**  Its variance over the phase box is at
most ninety-six times the family size. -/
theorem integral_box_variance_quarticSum_le (e : ι → α → ℂ)
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0) :
    (∫ x in torusBox α, ‖quarticSum e x‖ ^ (2 : ℕ)) -
        ‖∫ x in torusBox α, quarticSum e x‖ ^ (2 : ℕ) ≤ 96 * (Fintype.card ι : ℝ) := by
  classical
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ (2 : ℕ) := by positivity
  have hpoin := variance_trigLift_le_sum_integral_normSq_pderiv
    (Finset.univ : Finset (ι × ((α × α) × (α × α)))) (fun q => quarticFreq q.2) (quarticCoeff e)
  rw [← quarticSum_eq_trigLift e] at hpoin
  have hsum : (∑ b : α, ∫ x in torusBox α, ‖pderiv b (quarticSum e) x‖ ^ (2 : ℕ)) ≤
      64 * Real.pi ^ (2 : ℕ) * (6 * (Fintype.card ι : ℝ)) := by
    rw [← integral_finsetSum _ fun b _ => integrableOn_box_normSq_pderiv_quarticSum e b]
    have hint2 : IntegrableOn (fun x => 64 * Real.pi ^ (2 : ℕ) * ∑ j, ‖phaseAmp e j x‖ ^ (6 : ℕ))
        (torusBox α) volume :=
      Integrable.const_mul
        (integrable_finsetSum _ fun j _ => integrableOn_box_normPow_phaseAmp e j 6) _
    refine le_trans (integral_mono
      (integrable_finsetSum _ fun b _ => integrableOn_box_normSq_pderiv_quarticSum e b) hint2
      (fun x => sum_normSq_pderiv_quarticSum_le e horth x)) ?_
    rw [integral_const_mul,
      integral_finsetSum _ fun j _ => integrableOn_box_normPow_phaseAmp e j 6]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc (∑ j : ι, ∫ x in torusBox α, ‖phaseAmp e j x‖ ^ (6 : ℕ))
        ≤ ∑ _j : ι, (6 : ℝ) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hpt : ∀ x : α → ℝ, ‖phaseAmp e j x‖ ^ (6 : ℕ) =
              finitePureStateFidelity (torusReplicaPhaseOrbit (fun _ => (1 : ℝ)) x) (e j) ^ (3 : ℕ) := by
            intro x
            rw [← normSq_phaseAmp, ← pow_mul]
          simp_rw [hpt]
          have h := integral_box_fidelity_pow_le (p := fun _ : α => (1 : ℝ))
            (fun _ => zero_le_one) (τ := (1 : ℝ)) (fun _ => le_rfl) zero_le_one
            (sum_normSq_e_le_one e horth j) 3
          norm_num at h
          exact h
      _ = 6 * (Fintype.card ι : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
          ring
  have hfinal : ((2 * Real.pi) ^ (2 : ℕ))⁻¹ * (64 * Real.pi ^ (2 : ℕ) * (6 * (Fintype.card ι : ℝ))) =
      96 * (Fintype.card ι : ℝ) := by
    field_simp
    ring
  refine le_trans hpoin (le_trans ?_ (le_of_eq hfinal))
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

theorem integrableOn_box_collision (e : ι → α → ℂ) :
    IntegrableOn (fun x => ∑ j, ‖phaseAmp e j x‖ ^ (4 : ℕ)) (torusBox α) volume :=
  integrable_finsetSum _ fun j _ => integrableOn_box_normPow_phaseAmp e j 4

/-- **The unnormalized collision has variance at most ninety-six times the family size.**  This is
the variance half of the basis-uniform collision concentration, before the `D⁻²` normalization of
the seed. -/
theorem integral_box_variance_collision_le (e : ι → α → ℂ)
    (horth : ∀ j k, finiteComplexInner (e j) (e k) = if j = k then 1 else 0) :
    (∫ x in torusBox α, (∑ j, ‖phaseAmp e j x‖ ^ (4 : ℕ)) ^ (2 : ℕ)) -
        (∫ x in torusBox α, ∑ j, ‖phaseAmp e j x‖ ^ (4 : ℕ)) ^ (2 : ℕ) ≤ 96 * (Fintype.card ι : ℝ) := by
  classical
  have hsq : ∀ x : α → ℝ, ‖quarticSum e x‖ ^ (2 : ℕ) = (∑ j, ‖phaseAmp e j x‖ ^ (4 : ℕ)) ^ (2 : ℕ) := by
    intro x
    rw [quarticSum_eq_ofReal, Complex.norm_real,
      Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => by positivity)]
  have hmean : (∫ x in torusBox α, quarticSum e x) =
      ((∫ x in torusBox α, ∑ j, ‖phaseAmp e j x‖ ^ (4 : ℕ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => quarticSum_eq_ofReal e x)
  have hmeansq : ‖∫ x in torusBox α, quarticSum e x‖ ^ (2 : ℕ) =
      (∫ x in torusBox α, ∑ j, ‖phaseAmp e j x‖ ^ (4 : ℕ)) ^ (2 : ℕ) := by
    rw [hmean, Complex.norm_real,
      Real.norm_of_nonneg (integral_nonneg fun x => Finset.sum_nonneg fun j _ => by positivity)]
  have hmain := integral_box_variance_quarticSum_le e horth
  rw [hmeansq] at hmain
  rw [integral_congr_ae (Filter.Eventually.of_forall hsq)] at hmain
  exact hmain

end Quartic

end GaloisForLFunctions.HTGeometry
