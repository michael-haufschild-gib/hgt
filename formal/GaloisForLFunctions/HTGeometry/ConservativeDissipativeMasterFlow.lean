import GaloisForLFunctions.HTGeometry.ConservativeDissipativeDetailedBalance
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false

/-!
# Positive global master dynamics and nonlinear entropy trajectories

The conservative–dissipative energy mechanism from Schaffer–Exl
(arXiv:2609.04530) becomes an actual global detailed-balance evolution.
A positive scalar lift proves strict population positivity from the
exponential series, while its scalar compensation recovers the exact
master generator. Mass conservation, reference preservation, and the
semigroup law transfer to logarithmic coordinates. Those coordinates
solve the nonlinear relative-entropy field and dissipate its energy.
-/
open scoped BigOperators NNReal
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Linear population field of the constructed detailed-balance transport. -/
def masterField (a : ι → ι → ℝ) (r p : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, (relativeEntropyJumpRate a r j i * p j - relativeEntropyJumpRate a r i j * p i)

/-- Continuous linear generator of the master equation. -/
def masterGenerator (a : ι → ι → ℝ) (r : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  LinearMap.toContinuousLinearMap {
    toFun := masterField a r
    map_add' p q := by
      funext i
      simp only [masterField, Pi.add_apply, mul_add, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    map_smul' c p := by
      funext i
      simp only [masterField, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
  }

/-- A scalar dominating every outgoing total, constructed without a rate bound. -/
def masterShift (a : ι → ι → ℝ) (r : ι → ℝ) : ℝ :=
  1 + ∑ i, ∑ j, relativeEntropyJumpRate a r i j

theorem masterShift_sub_outgoing_nonneg (a : ι → ι → ℝ) (r : ι → ℝ) (i : ι) :
    0 ≤ masterShift a r - ∑ j, relativeEntropyJumpRate a r i j := by
  have h := Finset.single_le_sum (f := fun i => ∑ j, relativeEntropyJumpRate a r i j)
    (fun k _ => Finset.sum_nonneg fun j _ => relativeEntropyJumpRate_nonneg a r k j)
    (Finset.mem_univ i)
  unfold masterShift
  linarith

/-- Positive lift of the generator; the scalar shift will be removed exactly in the flow. -/
def masterLift (a : ι → ι → ℝ) (r : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  masterGenerator a r + masterShift a r • ContinuousLinearMap.id ℝ (ι → ℝ)

theorem masterLift_apply (a : ι → ι → ℝ) (r p : ι → ℝ) (i : ι) :
    masterLift a r p i = (∑ j, relativeEntropyJumpRate a r j i * p j) +
      (masterShift a r - ∑ j, relativeEntropyJumpRate a r i j) * p i := by
  change masterField a r p i + masterShift a r * p i = _
  simp only [masterField, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

/-- Every power of the positive lift preserves positive initial populations. -/
theorem masterLift_pow_nonneg (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) (n : ℕ) (i : ι) :
    0 ≤ (((t : ℝ) • masterLift a r) ^ n) (fun j => Real.exp (r j + x j)) i := by
  induction n generalizing i with
  | zero => simpa using (Real.exp_pos (r i + x i)).le
  | succ n ih =>
    rw [pow_succ', mul_apply_eq_comp]
    change 0 ≤ (t : ℝ) * masterLift a r
      ((((t : ℝ) • masterLift a r) ^ n) (fun j => Real.exp (r j + x j))) i
    apply mul_nonneg t.coe_nonneg
    rw [masterLift_apply]
    exact add_nonneg
      (Finset.sum_nonneg fun j _ => mul_nonneg (relativeEntropyJumpRate_nonneg a r j i) (ih j))
      (mul_nonneg (masterShift_sub_outgoing_nonneg a r i) (ih i))

/-- The lifted exponential retains its positive zeroth series term. -/
theorem masterLift_exp_lower (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) (i : ι) :
    Real.exp (r i + x i) ≤
      NormedSpace.exp ((t : ℝ) • masterLift a r) (fun j => Real.exp (r j + x j)) i := by
  let v : ι → ℝ := fun j => Real.exp (r j + x j)
  let C : ((ι → ℝ) →L[ℝ] (ι → ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.apply ℝ (ι → ℝ) v)
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) ((t : ℝ) • masterLift a r)).map C C.continuous
  have hn (n : ℕ) : 0 ≤ C ((n.factorial : ℝ)⁻¹ • ((t : ℝ) • masterLift a r) ^ n) := by
    change 0 ≤ (n.factorial : ℝ)⁻¹ *
      ((((t : ℝ) • masterLift a r) ^ n) (fun j => Real.exp (r j + x j)) i)
    exact mul_nonneg (by positivity) (masterLift_pow_nonneg a r x t n i)
  have h := hs.summable.le_tsum 0 (fun n _ => hn n)
  rw [hs.tsum_eq] at h
  simpa [C, v] using h

/-- Actual global evolution of arbitrary real population vectors. -/
def masterEvolution (a : ι → ι → ℝ) (r : ι → ℝ) (t : ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  Real.exp (-(masterShift a r) * t) • NormedSpace.exp (t • masterLift a r)

/-- Actual evolution from arbitrary positive initial populations in relative logarithmic coordinates. -/
def masterPopulationFlow (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ) : ι → ℝ :=
  masterEvolution a r t (fun i => Real.exp (r i + x i))

theorem masterPopulationFlow_pos (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) (i : ι) :
    0 < masterPopulationFlow a r x t i := by
  change 0 < Real.exp (-(masterShift a r) * (t : ℝ)) *
    (NormedSpace.exp ((t : ℝ) • masterLift a r) (fun j => Real.exp (r j + x j)) i)
  exact mul_pos (Real.exp_pos _) ((Real.exp_pos _).trans_le (masterLift_exp_lower a r x t i))

/-- Cancellation of incoming and outgoing mass holds for arbitrary signed populations. -/
theorem masterField_mass (a : ι → ι → ℝ) (r p : ι → ℝ) : ∑ i, masterField a r p i = 0 := by
  simp only [masterField, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun i j => relativeEntropyJumpRate a r j i * p j)]
  exact sub_self _

/-- The scalar shift cancels exactly in the actual evolution equation. -/
theorem hasDerivAt_masterEvolution (a : ι → ι → ℝ) (r p : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => masterEvolution a r s p)
      (masterField a r (masterEvolution a r t p)) t := by
  have he : HasDerivAt (fun s : ℝ => Real.exp (-(masterShift a r) * s))
      (Real.exp (-(masterShift a r) * t) * (-(masterShift a r))) t := by
    convert ((hasDerivAt_id t).const_mul (-(masterShift a r))).exp using 1 <;>
      simp only [id_eq, mul_one]
  have ho := (hasDerivAt_exp_smul_const' (masterLift a r) t).clm_apply (hasDerivAt_const t p)
  have hd := he.smul ho
  convert hd using 1 <;> first
    | rfl
    | (simp only [mul_apply_eq_comp, map_zero, add_zero]
       change masterGenerator a r
         (Real.exp (-(masterShift a r) * t) • NormedSpace.exp (t • masterLift a r) p) = _
       rw [map_smul]
       simp only [masterLift, add_apply, smul_apply,
         ContinuousLinearMap.id_apply]
       ext i
       simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
       ring)

theorem masterEvolution_zero (a : ι → ι → ℝ) (r p : ι → ℝ) : masterEvolution a r 0 p = p := by
  simp [masterEvolution]

/-- Total population is constant along the actual global evolution. -/
theorem masterEvolution_mass (a : ι → ι → ℝ) (r p : ι → ℝ) (t : ℝ) :
    ∑ i, masterEvolution a r t p i = ∑ i, p i := by
  have hd (s : ℝ) : HasDerivAt (fun u => ∑ i, masterEvolution a r u p i) 0 s := by
    have hi (i : ι) := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt s
      (hasDerivAt_masterEvolution a r p s)
    convert HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hi i) using 1 <;> first
      | rfl
      | exact (masterField_mass a r _).symm
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa only [masterEvolution_zero] using hc

/-- The global evolution composes exactly in time. -/
theorem masterEvolution_add (a : ι → ι → ℝ) (r : ι → ℝ) (s t : ℝ) :
    masterEvolution a r (s + t) = masterEvolution a r s * masterEvolution a r t := by
  letI : NormedAlgebra ℚ ((ι → ℝ) →L[ℝ] (ι → ℝ)) :=
    NormedAlgebra.restrictScalars ℚ ℝ ((ι → ℝ) →L[ℝ] (ι → ℝ))
  have hc : Commute (s • masterLift a r) (t • masterLift a r) :=
    ((Commute.refl (masterLift a r)).smul_left s).smul_right t
  simp only [masterEvolution, mul_add, Real.exp_add, add_smul,
    NormedSpace.exp_add_of_commute hc, smul_mul_smul_comm]

/-- The generator commutes with its constructed evolution. -/
theorem masterEvolution_commute (a : ι → ι → ℝ) (r : ι → ℝ) (t : ℝ) :
    Commute (masterGenerator a r) (masterEvolution a r t) := by
  have hc : Commute (masterGenerator a r) (masterLift a r) :=
    (Commute.refl (masterGenerator a r)).add_right
      ((Commute.one_right (masterGenerator a r)).smul_right (masterShift a r))
  exact ((hc.smul_right t).exp_right).smul_right _

/-- The prescribed positive reference is fixed for every time. -/
theorem masterEvolution_reference (a : ι → ι → ℝ) (r : ι → ℝ) (t : ℝ) :
    masterEvolution a r t (fun i => Real.exp (r i)) = fun i => Real.exp (r i) := by
  let p : ι → ℝ := fun i => Real.exp (r i)
  have hg : masterGenerator a r p = 0 := by
    funext i
    apply Finset.sum_eq_zero
    intro j _
    change relativeEntropyJumpRate a r j i * Real.exp (r j) -
      relativeEntropyJumpRate a r i j * Real.exp (r i) = 0
    have h := relativeEntropyJumpRate_balance a r j i
    nlinarith
  have hd (s : ℝ) : HasDerivAt (fun u => masterEvolution a r u p) 0 s := by
    apply (hasDerivAt_masterEvolution a r p s).congr_deriv
    change masterGenerator a r (masterEvolution a r s p) = 0
    have hc := congrArg (fun L : (ι → ℝ) →L[ℝ] (ι → ℝ) => L p)
      (masterEvolution_commute a r s).eq
    change masterGenerator a r (masterEvolution a r s p) =
      masterEvolution a r s (masterGenerator a r p) at hc
    rw [hc, hg, map_zero]
  have h := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa only [masterEvolution_zero] using h

/-- The actual nonlinear trajectory in reference-relative logarithmic coordinates. -/
def masterLogFlow (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  Real.log (masterPopulationFlow a r x t i) - r i

theorem masterLogFlow_zero (a : ι → ι → ℝ) (r x : ι → ℝ) : masterLogFlow a r x 0 = x := by
  funext i
  simp [masterLogFlow, masterPopulationFlow, masterEvolution_zero]

/-- Positive population reconstruction along the actual logarithmic trajectory. -/
theorem exp_masterLogFlow (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) (i : ι) :
    Real.exp (r i + masterLogFlow a r x t i) = masterPopulationFlow a r x t i := by
  rw [masterLogFlow, ← add_sub_assoc, add_sub_cancel_left]
  exact Real.exp_log (masterPopulationFlow_pos a r x t i)

/-- The nonlinear logarithmic orbit solves the constructed relative-entropy field. -/
theorem hasDerivAt_masterLogFlow (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) (i : ι) :
    HasDerivAt (fun s => masterLogFlow a r x s i)
      (relativeEntropyField a r (masterLogFlow a r x t) i) (t : ℝ) := by
  have hp := (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt (t : ℝ)
    (hasDerivAt_masterEvolution a r (fun j => Real.exp (r j + x j)) t)
  have hd := (hp.log (masterPopulationFlow_pos a r x t i).ne').sub_const (r i)
  convert hd using 1 <;> first
    | rfl
    | (change relativeEntropyField a r (masterLogFlow a r x t) i =
         masterField a r (masterPopulationFlow a r x t) i / masterPopulationFlow a r x t i
       apply (eq_div_iff (masterPopulationFlow_pos a r x t i).ne').mpr
       have h := relativeEntropyField_masterEquation a r (masterLogFlow a r x t) i
       simp only [exp_masterLogFlow] at h
       simpa only [masterField, mul_comm] using h)

/-- Exact energy loss along the actual global nonlinear trajectory. -/
theorem hasDerivAt_masterLogFlow_energy (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) :
    HasDerivAt (fun s => relativeEntropyEnergy r (masterLogFlow a r x s))
      (-((2 : ℝ)⁻¹) * ∑ i, ∑ j, entropyConductance a i j *
        entropyProductionValue (Real.exp (masterLogFlow a r x t i))
          (Real.exp (masterLogFlow a r x t j))) (t : ℝ) := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
    (((hasDerivAt_masterLogFlow a r x t i).const_add (r i)).exp).mul
      ((hasDerivAt_masterLogFlow a r x t i).sub_const 1)
  have heq : (∑ i, (Real.exp (r i + masterLogFlow a r x t i) *
      relativeEntropyField a r (masterLogFlow a r x t) i * (masterLogFlow a r x t i - 1) +
        Real.exp (r i + masterLogFlow a r x t i) * relativeEntropyField a r (masterLogFlow a r x t) i)) =
      ∑ i, masterLogFlow a r x t i * entropyFlux a (masterLogFlow a r x t) i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [relativeEntropyField_population]
    ring
  convert hd using 1 <;> first
    | rfl
    | (rw [heq, entropyFlux_power])

/-- The actual nonlinear free energy decreases for the full forward-time orbit. -/
theorem masterLogFlow_energy_antitoneOn (a : ι → ι → ℝ) (r x : ι → ℝ) :
    AntitoneOn (fun t : ℝ => relativeEntropyEnergy r (masterLogFlow a r x t)) (Set.Ici 0) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (D := Set.Ici (0 : ℝ))
    (f' := fun t => -((2 : ℝ)⁻¹) * ∑ i, ∑ j, entropyConductance a i j *
      entropyProductionValue (Real.exp (masterLogFlow a r x t i))
        (Real.exp (masterLogFlow a r x t j))) (convex_Ici 0)
  · intro t ht
    exact ((hasDerivAt_masterLogFlow_energy a r x ⟨t, ht⟩).continuousAt).continuousWithinAt
  · intro t ht
    exact (hasDerivAt_masterLogFlow_energy a r x ⟨t, (interior_subset ht)⟩).hasDerivWithinAt
  · intro t ht
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity))
      (entropyProduction_nonneg a (masterLogFlow a r x t))

/-- The nonlinear energy never exceeds its initial value at forward times. -/
theorem masterLogFlow_energy_le_initial (a : ι → ι → ℝ) (r x : ι → ℝ) (t : ℝ≥0) :
    relativeEntropyEnergy r (masterLogFlow a r x t) ≤ relativeEntropyEnergy r x := by
  have h := masterLogFlow_energy_antitoneOn a r x (show (0 : ℝ) ∈ Set.Ici 0 from by change (0 : ℝ) ≤ 0; exact le_rfl)
    (show (t : ℝ) ∈ Set.Ici 0 from by change 0 ≤ (t : ℝ); exact t.coe_nonneg) t.coe_nonneg
  simpa only [masterLogFlow_zero] using h

/-- Logarithmic trajectories inherit the exact forward semigroup law. -/
theorem masterLogFlow_add (a : ι → ι → ℝ) (r x : ι → ℝ) (s t : ℝ≥0) :
    masterLogFlow a r x (s + t) = masterLogFlow a r (masterLogFlow a r x t) s := by
  have hp : (fun i => Real.exp (r i + masterLogFlow a r x t i)) = masterPopulationFlow a r x t := by
    funext i
    exact exp_masterLogFlow a r x t i
  funext i
  change Real.log (masterPopulationFlow a r x (s + t) i) - r i =
    Real.log (masterEvolution a r s (fun j => Real.exp (r j + masterLogFlow a r x t j)) i) - r i
  rw [hp]
  simp only [masterPopulationFlow, masterEvolution_add, mul_apply_eq_comp]

/-- The chosen reference is an exact equilibrium of the nonlinear forward flow. -/
theorem masterLogFlow_reference (a : ι → ι → ℝ) (r : ι → ℝ) (t : ℝ) :
    masterLogFlow a r 0 t = 0 := by
  funext i
  simp only [masterLogFlow, masterPopulationFlow, Pi.zero_apply, add_zero,
    masterEvolution_reference, Real.log_exp, sub_self]

/-- The actual logarithmic orbit is continuous throughout forward time, including its initial point. -/
theorem continuousOn_masterLogFlow (a : ι → ι → ℝ) (r x : ι → ℝ) :
    ContinuousOn (masterLogFlow a r x) (Set.Ici 0) := by
  intro t ht
  have hd : HasDerivAt (masterLogFlow a r x)
      (relativeEntropyField a r (masterLogFlow a r x t)) t :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_masterLogFlow a r x ⟨t, ht⟩ i)
  exact hd.continuousAt.continuousWithinAt

end
end GaloisForLFunctions.HTGeometry.SchafferExl
