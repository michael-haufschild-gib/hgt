import GaloisForLFunctions.HTGeometry.CubeNoEmbedding

/-!
# A cube covered by finitely many low-dimensional charts

If the unit `m`-cube is covered by finitely many closed sets on each of which some continuous map to
`ℝ^k` is injective, then `m ≤ k`.

Baire's theorem inside the cube gives one chart with nonempty relative interior; a small closed box
inside that interior is an affine copy of the whole cube, and the chart restricted to it is a
continuous injection into `ℝ^k`.  This is the local form of the dimension bound: no global embedding
of the cube is needed, only local ones, which is what a finite atlas of regular charts provides.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

/-- The affine copy of the unit cube with corner `a` and side `s`. -/
noncomputable def cubeBox {m : ℕ} (a : Fin m → ℝ) (s : ℝ)
    (v : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm fun i => a i + s * v i

@[simp]
theorem cubeBox_apply {m : ℕ} (a : Fin m → ℝ) (s : ℝ) (v : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    cubeBox a s v i = a i + s * v i := rfl

theorem continuous_cubeBox {m : ℕ} (a : Fin m → ℝ) (s : ℝ) : Continuous (cubeBox a s) := by
  refine (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp (continuous_pi fun i => ?_)
  exact continuous_const.add (continuous_const.mul (EuclideanSpace.proj (𝕜 := ℝ) i).continuous)

theorem injective_cubeBox {m : ℕ} (a : Fin m → ℝ) {s : ℝ} (hs : s ≠ 0) :
    Function.Injective (cubeBox a s) := by
  intro v v' hvv
  refine PiLp.ext fun i => ?_
  have := congrArg (fun z : EuclideanSpace ℝ (Fin m) => z i) hvv
  simp only [cubeBox_apply] at this
  have h : s * v i = s * v' i := by linarith
  exact mul_left_cancel₀ hs h

/-- **A cube covered by finitely many charts into `ℝ^k` has `m ≤ k`.** -/
theorem le_of_unitCube_charts {m k N : ℕ}
    (F : Fin N → Set (EuclideanSpace ℝ (Fin m))) (hFclosed : ∀ j, IsClosed (F j))
    (hcover : ∀ x ∈ unitCube m, ∃ j, x ∈ F j)
    (E : Fin N → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin k))
    (hEcont : ∀ j, ContinuousOn (E j) (F j ∩ unitCube m))
    (hEinj : ∀ j, Set.InjOn (E j) (F j ∩ unitCube m)) : m ≤ k := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  -- Baire inside the cube
  set C : Set (EuclideanSpace ℝ (Fin m)) := unitCube m with hC
  haveI : Nonempty (↥C) := ⟨⟨0, zero_mem_unitCube m⟩⟩
  haveI : CompleteSpace (↥C) := (isClosed_unitCube m).completeSpace_coe
  set G : Fin N → Set (↥C) := fun j => (fun x : ↥C => (x : EuclideanSpace ℝ (Fin m))) ⁻¹' F j
    with hG
  have hGclosed : ∀ j, IsClosed (G j) := fun j => (hFclosed j).preimage continuous_subtype_val
  have hGcover : ⋃ j, G j = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    obtain ⟨j, hj⟩ := hcover (x : EuclideanSpace ℝ (Fin m)) x.2
    exact Set.mem_iUnion.mpr ⟨j, hj⟩
  obtain ⟨j, hj⟩ := nonempty_interior_of_iUnion_of_closed hGclosed hGcover
  obtain ⟨x₀, hx₀⟩ := hj
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x₀ hx₀
  have hballF : ∀ y : ↥C, dist y x₀ < ρ → (y : EuclideanSpace ℝ (Fin m)) ∈ F j := by
    intro y hy
    have hmem : y ∈ G j := interior_subset (hball hy)
    exact hmem
  -- a small affine copy of the cube inside that ball
  obtain ⟨s, hs0, hs1, hsρ⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ Real.sqrt m * (2 * s) < ρ := by
    refine ⟨min 1 (ρ / (2 * (Real.sqrt m + 1))), lt_min one_pos (by positivity),
      min_le_left _ _, ?_⟩
    have hsle : min 1 (ρ / (2 * (Real.sqrt m + 1))) ≤ ρ / (2 * (Real.sqrt m + 1)) :=
      min_le_right _ _
    have hsq : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
    have hpos : (0 : ℝ) < 2 * (Real.sqrt m + 1) := by positivity
    have hkey : Real.sqrt m * (2 * (ρ / (2 * (Real.sqrt m + 1)))) < ρ := by
      have hid : Real.sqrt m * (2 * (ρ / (2 * (Real.sqrt m + 1))))
          = (Real.sqrt m * ρ) / (Real.sqrt m + 1) := by
        field_simp
      rw [hid, div_lt_iff₀ (by positivity)]
      nlinarith
    nlinarith [hsle, hsq, hρ, hkey]
  set a : Fin m → ℝ := fun i => min ((x₀ : EuclideanSpace ℝ (Fin m)) i) (1 - s) with ha
  have hx₀mem : ∀ i, 0 ≤ (x₀ : EuclideanSpace ℝ (Fin m)) i ∧
      (x₀ : EuclideanSpace ℝ (Fin m)) i ≤ 1 := fun i => x₀.2 i
  have hbox : ∀ v ∈ unitCube m, cubeBox a s v ∈ unitCube m := by
    intro v hv i
    obtain ⟨hv0, hv1⟩ := hv i
    obtain ⟨h00, h01⟩ := hx₀mem i
    constructor
    · simp only [cubeBox_apply, ha]
      have : (0 : ℝ) ≤ min ((x₀ : EuclideanSpace ℝ (Fin m)) i) (1 - s) := le_min h00 (by linarith)
      nlinarith
    · simp only [cubeBox_apply, ha]
      have h1 : min ((x₀ : EuclideanSpace ℝ (Fin m)) i) (1 - s) ≤ 1 - s := min_le_right _ _
      nlinarith
  have hnear : ∀ v ∈ unitCube m, dist (cubeBox a s v) (x₀ : EuclideanSpace ℝ (Fin m)) < ρ := by
    intro v hv
    have hcoord : ∀ i, dist (cubeBox a s v i) ((x₀ : EuclideanSpace ℝ (Fin m)) i) ^ 2
        ≤ (2 * s) ^ 2 := by
      intro i
      obtain ⟨hv0, hv1⟩ := hv i
      obtain ⟨h00, h01⟩ := hx₀mem i
      have hai : |a i - (x₀ : EuclideanSpace ℝ (Fin m)) i| ≤ s := by
        simp only [ha]
        rcases le_total ((x₀ : EuclideanSpace ℝ (Fin m)) i) (1 - s) with hle | hle
        · rw [min_eq_left hle]
          simp [hs0.le]
        · rw [min_eq_right hle, abs_le]
          constructor <;> linarith
      rw [Real.dist_eq]
      have habs : |cubeBox a s v i - (x₀ : EuclideanSpace ℝ (Fin m)) i| ≤ 2 * s := by
        simp only [cubeBox_apply]
        have hsplit : a i + s * v i - (x₀ : EuclideanSpace ℝ (Fin m)) i
            = (a i - (x₀ : EuclideanSpace ℝ (Fin m)) i) + s * v i := by ring
        rw [hsplit]
        refine le_trans (abs_add_le _ _) ?_
        have : |s * v i| ≤ s := by
          rw [abs_mul, abs_of_pos hs0, abs_of_nonneg hv0]
          nlinarith
        linarith
      nlinarith [abs_nonneg (cubeBox a s v i - (x₀ : EuclideanSpace ℝ (Fin m)) i)]
    rw [EuclideanSpace.dist_eq]
    have hsum : ∑ i : Fin m, dist (cubeBox a s v i) ((x₀ : EuclideanSpace ℝ (Fin m)) i) ^ 2
        ≤ (m : ℝ) * (2 * s) ^ 2 := by
      calc ∑ i : Fin m, dist (cubeBox a s v i) ((x₀ : EuclideanSpace ℝ (Fin m)) i) ^ 2
          ≤ ∑ _i : Fin m, (2 * s) ^ 2 := Finset.sum_le_sum fun i _ => hcoord i
        _ = (m : ℝ) * (2 * s) ^ 2 := by simp
    calc Real.sqrt (∑ i : Fin m, dist (cubeBox a s v i) ((x₀ : EuclideanSpace ℝ (Fin m)) i) ^ 2)
        ≤ Real.sqrt ((m : ℝ) * (2 * s) ^ 2) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt m * (2 * s) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      _ < ρ := hsρ
  have hmaps : ∀ v ∈ unitCube m, cubeBox a s v ∈ F j ∩ unitCube m := by
    intro v hv
    refine ⟨?_, hbox v hv⟩
    have hmem : cubeBox a s v ∈ C := hbox v hv
    have := hballF ⟨cubeBox a s v, hmem⟩ (by
      rw [Subtype.dist_eq]
      exact hnear v hv)
    exact this
  refine not_injOn_unitCube hcon (fun v => E j (cubeBox a s v)) ?_ ?_
  · exact (hEcont j).comp (continuous_cubeBox a s).continuousOn hmaps
  · intro v hv v' hv' heq
    have := hEinj j (hmaps v hv) (hmaps v' hv') heq
    exact injective_cubeBox a (ne_of_gt hs0) this

end GaloisForLFunctions.HTGeometry
