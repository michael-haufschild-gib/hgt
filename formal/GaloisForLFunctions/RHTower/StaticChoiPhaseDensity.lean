import GaloisForLFunctions.RHTower.FiniteQuantumObserverGraphSharpness

/-!
# Static Choi phase density

This file identifies the Hilbert--Schmidt geometry of equal-weight phase
densities with the observer-distance geometry used by the finite spectral
recurrence theory.  The identity is exact and supplies the metric input for
static-Hamiltonian Choi plateau bounds.
-/

open MeasureTheory Set
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower

/-- Equal-weight pure-state density matrix with phases indexed by `Fin d`. -/
def uniformPhaseDensity (d : ℕ) (x : Fin d → UnitAddCircle) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 fun ij =>
    ((d : ℝ)⁻¹ : ℂ) * fourier 1 (x ij.1) *
      starRingEnd ℂ (fourier 1 (x ij.2))

@[simp] theorem uniformPhaseDensity_apply (d : ℕ)
    (x : Fin d → UnitAddCircle) (ij : Fin d × Fin d) :
    uniformPhaseDensity d x ij =
      ((d : ℝ)⁻¹ : ℂ) * fourier 1 (x ij.1) *
        starRingEnd ℂ (fourier 1 (x ij.2)) := rfl

/-- Relative phase between two points of the spectral torus. -/
def relativePhase {d : ℕ}
    (x y : Fin d → UnitAddCircle) (i : Fin d) : ℂ :=
  fourier 1 (x i - y i)

theorem relativePhase_norm {d : ℕ}
    (x y : Fin d → UnitAddCircle) (i : Fin d) :
    ‖relativePhase x y i‖ = 1 := by
  rw [relativePhase, fourier_apply, Circle.norm_coe]

/-- The Hilbert--Schmidt displacement of two phase densities is exactly the
observer-distance energy of their relative phase. -/
theorem norm_uniformPhaseDensity_sub_sq_eq_observer
    {d : ℕ} (hd : 0 < d) (x y : Fin d → UnitAddCircle) :
    ‖uniformPhaseDensity d x - uniformPhaseDensity d y‖ ^ (2 : ℕ) =
      finiteQuantumObserverDistanceSq uniformPureObserverWeight
        (relativePhase x y) (uniformPureObserverBlock d) := by
  rw [EuclideanSpace.norm_sq_eq,
    finiteQuantumObserverDistanceSq_eq_phaseEnergy,
    finiteQuantumObserverPhaseEnergy]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [uniformPureObserverUnionWeight hd]
  change
    ‖((d : ℝ)⁻¹ : ℂ) * fourier 1 (x i) * starRingEnd ℂ (fourier 1 (x j)) -
      ((d : ℝ)⁻¹ : ℂ) * fourier 1 (y i) * starRingEnd ℂ (fourier 1 (y j))‖ ^ (2 : ℕ) =
      (d : ℝ)⁻¹ ^ (2 : ℕ) *
        ‖relativePhase x y i * starRingEnd ℂ (relativePhase x y j) - 1‖ ^ (2 : ℕ)
  have hrel (k : Fin d) :
      relativePhase x y k =
        fourier 1 (x k) * starRingEnd ℂ (fourier 1 (y k)) := by
    rw [relativePhase, fourier_one, fourier_one, fourier_one,
      sub_eq_add_neg, AddCircle.toCircle_add, AddCircle.toCircle_neg,
      Circle.coe_mul, Circle.coe_inv_eq_conj]
  have hunit (z : UnitAddCircle) :
      fourier 1 z * starRingEnd ℂ (fourier 1 z) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp
  have hfactor :
      ((d : ℝ)⁻¹ : ℂ) * fourier 1 (x i) * starRingEnd ℂ (fourier 1 (x j)) -
          ((d : ℝ)⁻¹ : ℂ) * fourier 1 (y i) * starRingEnd ℂ (fourier 1 (y j)) =
        (((d : ℝ)⁻¹ : ℂ) *
          (fourier 1 (y i) * starRingEnd ℂ (fourier 1 (y j)))) *
          (relativePhase x y i * starRingEnd ℂ (relativePhase x y j) - 1) := by
    rw [hrel i, hrel j, map_mul]
    have hstarstar (z : ℂ) :
        starRingEnd ℂ (starRingEnd ℂ z) = z := star_star z
    rw [hstarstar]
    have hyprod :
        fourier 1 (y i) * starRingEnd ℂ (fourier 1 (y j)) *
            starRingEnd ℂ (fourier 1 (y i)) * fourier 1 (y j) = 1 := by
      calc
        _ = (fourier 1 (y i) * starRingEnd ℂ (fourier 1 (y i))) *
              (fourier 1 (y j) * starRingEnd ℂ (fourier 1 (y j))) := by ring
        _ = 1 := by rw [hunit (y i), hunit (y j)]; ring
    calc
      _ = ((d : ℝ)⁻¹ : ℂ) * fourier 1 (x i) *
            starRingEnd ℂ (fourier 1 (x j)) *
            (fourier 1 (y i) * starRingEnd ℂ (fourier 1 (y j)) *
              starRingEnd ℂ (fourier 1 (y i)) * fourier 1 (y j)) -
          ((d : ℝ)⁻¹ : ℂ) * fourier 1 (y i) *
            starRingEnd ℂ (fourier 1 (y j)) := by rw [hyprod]; ring
      _ = _ := by ring
  rw [hfactor, norm_mul, norm_mul]
  have hnormInv : ‖((d : ℝ)⁻¹ : ℂ)‖ = (d : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    positivity
  have hnormY :
      ‖fourier 1 (y i) * starRingEnd ℂ (fourier 1 (y j))‖ = 1 := by
    rw [norm_mul, RCLike.norm_conj, fourier_apply, fourier_apply,
      Circle.norm_coe, Circle.norm_coe]
    norm_num
  rw [hnormInv, hnormY]
  ring

/-- Exact fidelity formula for Hilbert--Schmidt displacement of equal-weight
phase densities. -/
theorem dist_uniformPhaseDensity_sq_eq_two_mul_fidelityDeficit
    {d : ℕ} (hd : 0 < d) (x y : Fin d → UnitAddCircle) :
    dist (uniformPhaseDensity d x) (uniformPhaseDensity d y) ^ (2 : ℕ) =
      2 * (1 - ‖equalPhaseAmplitude (relativePhase x y)‖ ^ (2 : ℕ)) := by
  rw [dist_eq_norm,
    norm_uniformPhaseDensity_sub_sq_eq_observer hd]
  exact uniformPureObserver_distanceSq_eq_two_mul_fidelityDeficit
    hd (relativePhase x y) (relativePhase_norm x y)

/-- A Hilbert--Schmidt displacement bound forces relative phase coherence. -/
theorem uniformPhaseDensity_pair_mem_torusCoherenceTarget
    {d : ℕ} (hd : 0 < d) {δ : ℝ} (hδ : 0 ≤ δ)
    (x y : Fin d → UnitAddCircle)
    (hxy : dist (uniformPhaseDensity d x) (uniformPhaseDensity d y) ≤ 2 * δ) :
    x - y ∈ torusCoherenceTarget (d := Fin d) (2 * δ ^ (2 : ℕ)) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  rw [torusCoherenceTarget]
  change 1 - 2 * δ ^ (2 : ℕ) ≤
    ‖equalPhaseAmplitude (fun j ↦ fourier 1 ((x - y) j))‖
  have hphase : (fun j ↦ fourier 1 ((x - y) j)) = relativePhase x y := by
    funext j
    rfl
  rw [hphase]
  have hid := dist_uniformPhaseDensity_sq_eq_two_mul_fidelityDeficit hd x y
  have hdist0 : 0 ≤ dist (uniformPhaseDensity d x) (uniformPhaseDensity d y) :=
    dist_nonneg
  have hsq :
      dist (uniformPhaseDensity d x) (uniformPhaseDensity d y) ^ (2 : ℕ) ≤
        (2 * δ) ^ (2 : ℕ) := by
    nlinarith
  have ha0 : 0 ≤ ‖equalPhaseAmplitude (relativePhase x y)‖ := norm_nonneg _
  have ha1 : ‖equalPhaseAmplitude (relativePhase x y)‖ ≤ 1 := by
    exact GaloisForLFunctions.HilbertMetric.norm_hilbertCentroid_le_of_norm_le
      (relativePhase x y) fun i ↦ (relativePhase_norm x y i).le
  nlinarith [sq_nonneg ‖equalPhaseAmplitude (relativePhase x y)‖,
    sq_nonneg (1 - ‖equalPhaseAmplitude (relativePhase x y)‖)]

end RHTower
