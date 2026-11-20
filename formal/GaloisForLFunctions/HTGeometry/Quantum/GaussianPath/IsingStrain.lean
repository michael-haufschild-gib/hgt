import GaloisForLFunctions.HTGeometry.PathDiagonalCarrier
import Mathlib.Topology.Order.OrderClosed

/-!
# Strain response of the diagonal path carrier

With fixed bond coefficients, an affine perturbation of the onsite fields
has a one-local response, as in Halla and De (arXiv:2611.25383, Theorem 2).
At a ground-state crossing the exact local right slope is the minimum
response among the configurations tied at zero strain.
-/

open Filter Matrix
open scoped BigOperators Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite affine family has a common minimizer on a right neighbourhood of
zero. At zero it minimizes the intercept and, among tied intercepts, the slope. -/
theorem exists_right_affine_minimizer {ι : Type*} [Fintype ι] [Nonempty ι]
    (a b : ι → ℝ) :
    ∃ i, (∀ j, a i ≤ a j) ∧ (∀ j, a j = a i → b i ≤ b j) ∧
      ∀ᶠ t : ℝ in 𝓝[Set.Ici 0] 0, ∀ j, a i + t * b i ≤ a j + t * b j := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.exists_min_image Finset.univ a Finset.univ_nonempty
  let T := Finset.univ.filter fun j => a j = a m
  have hT : T.Nonempty := ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
  obtain ⟨i, hi, hb⟩ := Finset.exists_min_image T b hT
  have hi0 : a i = a m := (Finset.mem_filter.mp hi).2
  have hmin (j : ι) : a i ≤ a j := by
    rw [hi0]
    exact hm j (Finset.mem_univ j)
  have hslope (j : ι) (h : a j = a i) : b i ≤ b j :=
    hb j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans hi0⟩)
  refine ⟨i, hmin, hslope, eventually_all.mpr fun j => ?_⟩
  by_cases h : a j = a i
  · filter_upwards [self_mem_nhdsWithin (a := (0 : ℝ)) (s := Set.Ici 0)] with t ht
    rw [h]
    exact add_le_add_left (mul_le_mul_of_nonneg_left (hslope j h) ht) _
  · have hgap : a i + (0 : ℝ) * b i < a j + 0 * b j := by
      simpa only [zero_mul, add_zero] using lt_of_le_of_ne (hmin j) (Ne.symm h)
    have hleft : ContinuousAt (fun t : ℝ => a i + t * b i) 0 :=
      continuousAt_const.add (continuousAt_id.mul continuousAt_const)
    have hright : ContinuousAt (fun t : ℝ => a j + t * b j) 0 :=
      continuousAt_const.add (continuousAt_id.mul continuousAt_const)
    exact ((hleft.eventually_lt hright hgap).filter_mono nhdsWithin_le_nhds).mono
      fun _ ht => ht.le

variable {n : ℕ}

private abbrev Site (n : ℕ) := Fin (n + 2)
private abbrev Configuration (n : ℕ) := FiniteQubitConfiguration (Site n)

/-- Diagonal path coefficients with fixed ZZ bonds and affine Z fields. -/
def strainPath (h dh : Site n → ℝ) (J : Fin (n + 1) → ℝ) (t : ℝ) : PathShell n :=
  WithLp.toLp 2 fun
    | .inl (i, a) => if a = 2 then h i + t * dh i else 0
    | .inr (e, a, b) => if a = 2 ∧ b = 2 then J e else 0

/-- The response eigenvalue of a computational basis configuration. -/
def onsiteResponse (dh : Site n → ℝ) (x : Configuration n) : ℝ :=
  ∑ i, dh i * zSetSign {i} x

theorem pathDiagEnergy_strain (h dh : Site n → ℝ) (J : Fin (n + 1) → ℝ)
    (t : ℝ) (x : Configuration n) :
    pathDiagEnergy (strainPath h dh J t) x =
      pathDiagEnergy (strainPath h dh J 0) x + t * onsiteResponse dh x := by
  have hon (s : Site n) (u : ℝ) : strainPath h dh J u (.inl (s,2)) = h s + u * dh s := by
    change (if (2 : Fin 3) = 2 then h s + u * dh s else 0) = _
    rw [if_pos rfl]
  have hbond (e : Fin (n + 1)) (u : ℝ) : strainPath h dh J u (.inr (e,2,2)) = J e := by
    change (if (2 : Fin 3) = 2 ∧ (2 : Fin 3) = 2 then J e else 0) = _
    rw [if_pos ⟨rfl, rfl⟩]
  simp only [pathDiagEnergy, onsiteResponse, hon, hbond, zero_mul, add_zero, add_mul,
    mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  exact add_right_comm _ _ _

private theorem strainPath_diagonal (h dh : Site n → ℝ) (J : Fin (n + 1) → ℝ) (t : ℝ) :
    pathHamiltonian (strainPath h dh J t) =
      Matrix.diagonal (fun x => (pathDiagEnergy (strainPath h dh J t) x : ℂ)) := by
  apply pathHamiltonian_eq_diagonal
  rintro (⟨i,a⟩ | ⟨e,a,b⟩) hl
  · change (if a = 2 then h i + t * dh i else 0) = 0
    exact if_neg hl
  · change (if a = 2 ∧ b = 2 then J e else 0) = 0
    exact if_neg hl

/-- The exact Hamiltonian increment is the sum of onsite responses, even when
the fixed bond Hamiltonian has a degenerate ground eigenspace. -/
theorem pathHamiltonian_strain (h dh : Site n → ℝ) (J : Fin (n + 1) → ℝ) (t : ℝ) :
    pathHamiltonian (strainPath h dh J t) =
      pathHamiltonian (strainPath h dh J 0) +
        (t : ℂ) • Matrix.diagonal (fun x => (onsiteResponse dh x : ℂ)) := by
  classical
  rw [strainPath_diagonal, strainPath_diagonal]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_apply_eq,
      pathDiagEnergy_strain h dh J t x, Complex.ofReal_add, Complex.ofReal_mul]
  · simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hxy,
      smul_zero, add_zero]

/-- The stable right ground configuration is selected by the minimum observable
response within the zero-strain ground configurations. -/
theorem exists_strain_ground_configuration (h dh : Site n → ℝ) (J : Fin (n + 1) → ℝ) :
    ∃ x : Configuration n,
      (∀ y, pathDiagEnergy (strainPath h dh J 0) x ≤ pathDiagEnergy (strainPath h dh J 0) y) ∧
      (∀ y, pathDiagEnergy (strainPath h dh J 0) y = pathDiagEnergy (strainPath h dh J 0) x →
        onsiteResponse dh x ≤ onsiteResponse dh y) ∧
      ∀ᶠ t : ℝ in 𝓝[Set.Ici 0] 0, ∀ y,
        pathDiagEnergy (strainPath h dh J t) x ≤ pathDiagEnergy (strainPath h dh J t) y := by
  obtain ⟨x, hx, hx', ht⟩ := exists_right_affine_minimizer
    (pathDiagEnergy (strainPath h dh J 0)) (onsiteResponse dh)
  refine ⟨x, hx, hx', ?_⟩
  filter_upwards [ht] with t ht
  intro y
  rw [pathDiagEnergy_strain h dh J t x, pathDiagEnergy_strain h dh J t y]
  exact ht y

#print axioms exists_right_affine_minimizer
#print axioms pathHamiltonian_strain
#print axioms exists_strain_ground_configuration

end

end GaloisForLFunctions.HTGeometry
