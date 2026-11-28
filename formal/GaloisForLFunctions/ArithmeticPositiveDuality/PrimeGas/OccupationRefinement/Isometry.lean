import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.FiniteShells

/-! # The isometric line for associative prime-particle refinement -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement

open CoassociativeSplitting

private theorem response_one {u v : ℝ} (hu : 0<u) (hv : 0<v) (n : ℕ+) : response u v n 1=1 := by
  simpa only [response,Real.rpow_one] using probability_sum hu hv n

/-- Conservation on any specified nonvacuum state determines the line. -/
theorem shell_iff (s : ℂ) {u v : ℝ} (hu : 0<u) (hv : 0<v) (n : ℕ+) (hn : 1<n.val) :
    HasSum (shell (amplitude s u v) n) 1 ↔ s.re=1/2 := by
  have H := shell_response s hu hv n
  constructor
  · intro unit
    have h := (response_strictAnti hu hv n hn).injective ((H.unique unit).trans (response_one hu hv n).symm)
    linarith only [h]
  · intro re
    rwa [show 2*s.re=1 by linarith only [re],response_one hu hv] at H

/-- The independent routing of prime particles is an isometry of the full
gas exactly when twice the real amplitude exponent equals one. -/
theorem isometry_iff (s : ℂ) {u v : ℝ} (hu : 0<u) (hv : 0<v) :
    isometric (amplitude s u v) ↔ s.re=1/2 := by
  rw [CoassociativeSplitting.isometric_iff]
  constructor
  · exact fun h => (shell_iff s hu hv 2 (by norm_num)).mp (h 2)
  · intro re n
    have H := shell_response s hu hv n
    rwa [show 2*s.re=1 by linarith only [re],response_one hu hv] at H

/-- On the conserving line the two outgoing heat factors reproduce the
input heat evolution on the image of the splitting isometry. -/
theorem intertwines (s : {z : ℂ // z.re=1/2}) (u v : Set.Ioi (0:ℝ)) :
    ∃ T : Gas →ₗᵢ[ℂ] PairGas, (∀ f x, T f x=wave (amplitude s.val u.val v.val) f x) ∧
      ∀ (z : {z : ℂ // 1<z.re}) (f : Gas) (x : ℕ+ × ℕ+),
        T (gibbsOperator z f) x=heat z.val x.1 * heat z.val x.2 * T f x := by
  obtain ⟨T,hT⟩ := (isometry_iff s.val u.property v.property).mpr s.property
  refine ⟨T,hT,fun z f x => ?_⟩
  simp only [hT,wave,gibbsOperator_apply,heat_mul]
  ring

/-- The same occupation basis carries associative quantum refinement and
the logarithmic Hamiltonian whose operator partition function is zeta. -/
theorem quantum_gas (s : ℂ) (u v w : Set.Ioi (0:ℝ)) :
    (isometric (amplitude s u.val v.val) ↔ s.re=1/2) ∧
    (∀ (f : Gas) a b c, amplitude s u.val v.val a b * wave (amplitude s (u.val+v.val) w.val) f (a*b,c) =
      amplitude s v.val w.val b c * wave (amplitude s u.val (v.val+w.val)) f (a,b*c)) ∧
    (∀ a b : ℕ+, energy (a*b)=energy a+energy b) ∧
    ∀ z : {z : ℂ // 1<z.re}, ContinuousLinearMap.opTrace (gibbsOperator z)=riemannZeta z.val :=
  ⟨isometry_iff s u.property v.property,wave_associative s u.property v.property w.property,
    energy_mul,partition_eq_zeta⟩

#print axioms shell_iff
#print axioms isometry_iff
#print axioms intertwines
#print axioms quantum_gas

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement
