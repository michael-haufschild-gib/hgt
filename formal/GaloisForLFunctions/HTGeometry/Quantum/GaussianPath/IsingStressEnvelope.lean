import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsingStrain
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Exact strain slopes at a finite ground-state crossing

The eigenvalues have a common quadratic strain term. Among configurations
tied at zero strain, the smallest stress determines the right slope and
the largest stress determines the left slope.
-/

open Filter Set
open scoped BigOperators Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace FiniteStrain

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The lowest energy in a finite nonempty diagonal spectrum. -/
def groundEnergy (a : ι → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty a

theorem groundEnergy_le (a : ι → ℝ) (i : ι) : groundEnergy a ≤ a i :=
  Finset.inf'_le a (Finset.mem_univ i)

theorem groundEnergy_eq_of_minimizer (a : ι → ℝ) (i : ι) (hi : ∀ j, a i ≤ a j) :
    groundEnergy a = a i :=
  le_antisymm (groundEnergy_le a i) (Finset.le_inf' _ _ fun j _ => hi j)

/-- The zero-strain ground configurations. -/
def groundConfigurations (a : ι → ℝ) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => a i = groundEnergy a)

theorem mem_groundConfigurations {a : ι → ℝ} {i : ι} :
    i ∈ groundConfigurations a ↔ a i = groundEnergy a := by
  classical
  simp [groundConfigurations]

theorem groundConfigurations_nonempty (a : ι → ℝ) : (groundConfigurations a).Nonempty := by
  obtain ⟨i, _, h⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty a
  exact ⟨i, mem_groundConfigurations.mpr h.symm⟩

/-- The smallest stress eigenvalue in the ground eigenspace. -/
def groundStressMin (a b : ι → ℝ) : ℝ :=
  (groundConfigurations a).inf' (groundConfigurations_nonempty a) b

/-- The largest stress eigenvalue in the ground eigenspace. -/
def groundStressMax (a b : ι → ℝ) : ℝ :=
  (groundConfigurations a).sup' (groundConfigurations_nonempty a) b

theorem groundStressMin_le {a b : ι → ℝ} {i : ι} (hi : i ∈ groundConfigurations a) :
    groundStressMin a b ≤ b i :=
  Finset.inf'_le b hi

theorem le_groundStressMax {a b : ι → ℝ} {i : ι} (hi : i ∈ groundConfigurations a) :
    b i ≤ groundStressMax a b :=
  Finset.le_sup' b hi

theorem exists_groundStressMin (a b : ι → ℝ) :
    ∃ i ∈ groundConfigurations a, groundStressMin a b = b i :=
  Finset.exists_mem_eq_inf' (groundConfigurations_nonempty a) b

theorem exists_groundStressMax (a b : ι → ℝ) :
    ∃ i ∈ groundConfigurations a, groundStressMax a b = b i :=
  Finset.exists_mem_eq_sup' (groundConfigurations_nonempty a) b

theorem groundStressMax_neg (a b : ι → ℝ) :
    groundStressMax a (fun i => -b i) = -groundStressMin a b := by
  obtain ⟨i, hi, hmax⟩ := exists_groundStressMax a (fun i => -b i)
  obtain ⟨j, hj, hmin⟩ := exists_groundStressMin a b
  apply le_antisymm
  · rw [hmax]
    exact neg_le_neg (groundStressMin_le hi)
  · rw [hmin]
    exact le_groundStressMax (b := fun i => -b i) hj

/-- A branch has its zero-strain energy, its linear stress and a common
quadratic term. The optimized energy is the minimum over branches. -/
def strainedEnergy (a b : ι → ℝ) (k t : ℝ) : ℝ :=
  groundEnergy (fun i => a i + t * b i + k * t ^ 2)

theorem strainedEnergy_zero (a b : ι → ℝ) (k : ℝ) :
    strainedEnergy a b k 0 = groundEnergy a := by
  simp [strainedEnergy]

/-- On the right of a crossing, the energy follows exactly the branch of
least ground-space stress, with the common quadratic term retained. -/
theorem strainedEnergy_eventually_right (a b : ι → ℝ) (k : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[Ici 0] 0,
      strainedEnergy a b k t = groundEnergy a + t * groundStressMin a b + k * t ^ 2 := by
  obtain ⟨i, hmin, hslope, ht⟩ := exists_right_affine_minimizer a b
  have hi : a i = groundEnergy a := (groundEnergy_eq_of_minimizer a i hmin).symm
  have hm : groundStressMin a b = b i := by
    refine le_antisymm (groundStressMin_le (mem_groundConfigurations.mpr hi)) ?_
    apply Finset.le_inf'
    intro j hj
    exact hslope j ((mem_groundConfigurations.mp hj).trans hi.symm)
  filter_upwards [ht] with t ht
  rw [strainedEnergy, groundEnergy_eq_of_minimizer _ i
    (fun j => add_le_add (ht j) le_rfl), hi, hm]

/-- Reversing the strain selects the largest stress in the same ground space. -/
theorem strainedEnergy_eventually_left (a b : ι → ℝ) (k : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[Iic 0] 0,
      strainedEnergy a b k t = groundEnergy a + t * groundStressMax a b + k * t ^ 2 := by
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[Iic 0] 0) (𝓝[Ici 0] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have h : ContinuousAt (fun t : ℝ => -t) 0 := continuous_neg.continuousAt
      simpa only [neg_zero] using h.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Iic 0)] with t ht
      exact mem_Ici.mpr (neg_nonneg.mpr (mem_Iic.mp ht))
  have hm : groundStressMin a (fun i => -b i) = -groundStressMax a b := by
    have h := groundStressMax_neg a (fun i => -b i)
    simp only [neg_neg] at h
    linarith only [h]
  have he (t : ℝ) : strainedEnergy a (fun i => -b i) k (-t) = strainedEnergy a b k t := by
    simp only [strainedEnergy, neg_mul_neg, neg_sq]
  filter_upwards [hneg.eventually (strainedEnergy_eventually_right a (fun i => -b i) k)] with t ht
  change strainedEnergy a (fun i => -b i) k (-t) = _ at ht
  rwa [he, hm, neg_mul_neg, neg_sq] at ht

private theorem hasDerivAt_quadratic_zero (c d k : ℝ) :
    HasDerivAt (fun t : ℝ => c + t * d + k * t ^ 2) d 0 := by
  have hd : HasDerivAt (fun t : ℝ => t * d) d 0 := by
    simpa only [id_eq, one_mul] using (hasDerivAt_id (0 : ℝ)).mul_const d
  have hk : HasDerivAt (fun t : ℝ => k * t ^ 2) 0 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul k)
  have h := ((hasDerivAt_const (0 : ℝ) c).add hd).add hk
  change HasDerivAt (fun t : ℝ => c + t * d + k * t ^ 2) (0 + d + 0) 0 at h
  simpa only [zero_add, add_zero] using h

theorem hasDerivWithinAt_strainedEnergy_right (a b : ι → ℝ) (k : ℝ) :
    HasDerivWithinAt (strainedEnergy a b k) (groundStressMin a b) (Ici 0) 0 :=
  (hasDerivAt_quadratic_zero _ _ _).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    (strainedEnergy_eventually_right a b k) (mem_Ici.mpr (le_refl (0 : ℝ)))

theorem hasDerivWithinAt_strainedEnergy_left (a b : ι → ℝ) (k : ℝ) :
    HasDerivWithinAt (strainedEnergy a b k) (groundStressMax a b) (Iic 0) 0 :=
  (hasDerivAt_quadratic_zero _ _ _).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    (strainedEnergy_eventually_left a b k) (mem_Iic.mpr (le_refl (0 : ℝ)))

/-- A ground-state tie gives a cusp exactly when the tied stress
eigenvalues fail to agree. -/
theorem differentiableAt_strainedEnergy_iff (a b : ι → ℝ) (k : ℝ) :
    DifferentiableAt ℝ (strainedEnergy a b k) 0 ↔ groundStressMin a b = groundStressMax a b := by
  have hr := hasDerivWithinAt_strainedEnergy_right a b k
  have hl := hasDerivWithinAt_strainedEnergy_left a b k
  constructor
  · intro hd
    have hdr : HasDerivWithinAt (strainedEnergy a b k) (deriv (strainedEnergy a b k) 0) (Ici 0) 0 :=
      hd.hasDerivAt.hasDerivWithinAt
    have hdl : HasDerivWithinAt (strainedEnergy a b k) (deriv (strainedEnergy a b k) 0) (Iic 0) 0 :=
      hd.hasDerivAt.hasDerivWithinAt
    exact ((hr.derivWithin (uniqueDiffWithinAt_Ici 0)).symm.trans
      (hdr.derivWithin (uniqueDiffWithinAt_Ici 0))).trans
      ((hdl.derivWithin (uniqueDiffWithinAt_Iic 0)).symm.trans (hl.derivWithin (uniqueDiffWithinAt_Iic 0)))
  · intro he
    rw [he] at hr
    have hu := hl.union hr
    have hs : Iic (0 : ℝ) ∪ Ici 0 = univ := by
      ext t
      simp only [mem_union, mem_Iic, mem_Ici, mem_univ, iff_true]
      exact le_total _ _
    rw [hs, hasDerivWithinAt_univ] at hu
    exact hu.differentiableAt

end FiniteStrain

/-- Minimum diagonal path energy under an affine onsite strain. -/
def isingStrainGroundEnergy {n : ℕ} (h dh : Fin (n + 2) → ℝ) (J : Fin (n + 1) → ℝ) (t : ℝ) : ℝ :=
  FiniteStrain.groundEnergy (pathDiagEnergy (strainPath h dh J t))

theorem isingStrainGroundEnergy_eq {n : ℕ} (h dh : Fin (n + 2) → ℝ) (J : Fin (n + 1) → ℝ) :
    isingStrainGroundEnergy h dh J = FiniteStrain.strainedEnergy
      (pathDiagEnergy (strainPath h dh J 0)) (onsiteResponse dh) 0 := by
  funext t
  simp only [isingStrainGroundEnergy, FiniteStrain.strainedEnergy, zero_mul, add_zero]
  exact congrArg FiniteStrain.groundEnergy (funext (pathDiagEnergy_strain h dh J t))

/-- The two derivatives of the diagonal path energy are precisely the
extrema of the onsite response among the unstrained ground configurations. -/
theorem isingStrainGroundEnergy_oneSided_derivatives {n : ℕ}
    (h dh : Fin (n + 2) → ℝ) (J : Fin (n + 1) → ℝ) :
    HasDerivWithinAt (isingStrainGroundEnergy h dh J)
      (FiniteStrain.groundStressMin (pathDiagEnergy (strainPath h dh J 0)) (onsiteResponse dh)) (Ici 0) 0 ∧
    HasDerivWithinAt (isingStrainGroundEnergy h dh J)
      (FiniteStrain.groundStressMax (pathDiagEnergy (strainPath h dh J 0)) (onsiteResponse dh)) (Iic 0) 0 := by
  rw [isingStrainGroundEnergy_eq]
  exact ⟨FiniteStrain.hasDerivWithinAt_strainedEnergy_right _ _ _,
    FiniteStrain.hasDerivWithinAt_strainedEnergy_left _ _ _⟩

#print axioms FiniteStrain.strainedEnergy_eventually_right
#print axioms FiniteStrain.strainedEnergy_eventually_left
#print axioms FiniteStrain.differentiableAt_strainedEnergy_iff
#print axioms isingStrainGroundEnergy_oneSided_derivatives

end

end GaloisForLFunctions.HTGeometry
