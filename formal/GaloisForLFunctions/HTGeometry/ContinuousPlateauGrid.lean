import GaloisForLFunctions.HTGeometry.ObserverProfileStability
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
# Continuous plateaux from a grid of fixed-time bounds

A Schrödinger orbit moves at speed at most the operator norm of its generator, so a shortcut at a
narrow radius at one time is a shortcut at a wider radius at every nearby time.  Covering a window
by a finite grid of that mesh therefore converts a family of one-time smallness bounds into a
statement about the whole continuum of times in the window, with a union-bound loss equal to the
number of grid points.  Nothing here is measurable-set dependent: only subadditivity and
monotonicity of the measure are used.
-/

open Matrix MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

section Evolution

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

omit [Nonempty d] in
theorem unitaryEvolution_eq_smul_time (H : Matrix d d ℂ) (t : ℝ) :
    unitaryEvolution H t = unitaryEvolution (t • H) 1 := by
  unfold unitaryEvolution
  congr 1
  rw [one_smul, smul_comm]

omit [Fintype d] [DecidableEq d] [Nonempty d] in
theorem isSelfAdjoint_real_smul {H : Matrix d d ℂ} (hH : IsSelfAdjoint H) (t : ℝ) :
    IsSelfAdjoint (t • H) := by
  rw [IsSelfAdjoint, star_smul, star_trivial, hH.star_eq]

omit [Nonempty d] in
/-- **Operator speed.**  One Hamiltonian moves its evolution operator at most the elapsed time
times the generator norm. -/
theorem norm_unitaryEvolution_time_sub_le {H : Matrix d d ℂ} (hH : IsSelfAdjoint H) (t u : ℝ) :
    ‖unitaryEvolution H t - unitaryEvolution H u‖ ≤ ‖H‖ * |t - u| := by
  rw [unitaryEvolution_eq_smul_time H t, unitaryEvolution_eq_smul_time H u]
  refine le_trans (norm_unitaryEvolution_sub_le (t • H) (u • H)
    (isSelfAdjoint_real_smul hH t) (isSelfAdjoint_real_smul hH u) 1) ?_
  have hsub : t • H - u • H = (t - u) • H := (sub_smul t u H).symm
  rw [hsub, norm_smul]
  simp only [abs_one, one_mul, Real.norm_eq_abs]
  rw [mul_comm]

omit [Nonempty d] in
/-- **Schrödinger speed.**  One Hamiltonian moves a state at most the elapsed time times the
generator norm times the state norm. -/
theorem norm_unitaryEvolution_mulVec_time_sub_le {H : Matrix d d ℂ} (hH : IsSelfAdjoint H)
    (t u : ℝ) (psi : EuclideanSpace ℂ d) :
    ‖(EuclideanSpace.equiv d ℂ).symm (unitaryEvolution H t *ᵥ psi.ofLp)
        - (EuclideanSpace.equiv d ℂ).symm (unitaryEvolution H u *ᵥ psi.ofLp)‖
      ≤ ‖H‖ * |t - u| * ‖psi‖ := by
  have hsub : (EuclideanSpace.equiv d ℂ).symm (unitaryEvolution H t *ᵥ psi.ofLp)
      - (EuclideanSpace.equiv d ℂ).symm (unitaryEvolution H u *ᵥ psi.ofLp)
      = (EuclideanSpace.equiv d ℂ).symm
        ((unitaryEvolution H t - unitaryEvolution H u) *ᵥ psi.ofLp) := by
    rw [Matrix.sub_mulVec, map_sub]
  rw [hsub]
  refine le_trans (Matrix.l2_opNorm_mulVec _ psi) ?_
  exact mul_le_mul_of_nonneg_right (norm_unitaryEvolution_time_sub_le hH t u) (norm_nonneg psi)

end Evolution

section Grid

/-- Number of grid points covering a window of length `W` with mesh `mesh`. -/
noncomputable def plateauGridCount (W mesh : ℝ) : ℕ := ⌈W / mesh⌉₊ + 1

/-- The `j`-th grid point of a window starting at `A`. -/
def plateauGridPoint (A mesh : ℝ) (j : ℕ) : ℝ := A + j * mesh

theorem one_le_plateauGridCount (W mesh : ℝ) : 1 ≤ plateauGridCount W mesh := by
  unfold plateauGridCount
  omega

theorem plateauGridPoint_le (A : ℝ) {mesh : ℝ} (hmesh : 0 ≤ mesh) (j : ℕ) :
    A ≤ plateauGridPoint A mesh j := by
  unfold plateauGridPoint
  have : (0 : ℝ) ≤ (j : ℝ) * mesh := by positivity
  linarith

/-- Every point of the window is within one mesh of a grid point. -/
theorem exists_plateauGrid_near {W mesh : ℝ} (hmesh : 0 < mesh) (A : ℝ) {t : ℝ}
    (ht : t ∈ Set.Icc A (A + W)) :
    ∃ j : Fin (plateauGridCount W mesh), |t - plateauGridPoint A mesh j| ≤ mesh := by
  obtain ⟨htA, htW⟩ := ht
  have hnn : (0 : ℝ) ≤ (t - A) / mesh := div_nonneg (by linarith) hmesh.le
  set j0 : ℕ := ⌊(t - A) / mesh⌋₊ with hj0
  have hj0le : (j0 : ℝ) ≤ (t - A) / mesh := Nat.floor_le hnn
  have hj0lt : (t - A) / mesh < (j0 : ℝ) + 1 := Nat.lt_floor_add_one _
  have hWmesh : (t - A) / mesh ≤ W / mesh := by
    gcongr
    linarith
  have hj0bound : j0 ≤ ⌈W / mesh⌉₊ :=
    le_trans (Nat.floor_le_floor hWmesh) (Nat.floor_le_ceil _)
  have hlt : j0 < plateauGridCount W mesh := by
    unfold plateauGridCount
    omega
  refine ⟨⟨j0, hlt⟩, ?_⟩
  unfold plateauGridPoint
  have hlow : (j0 : ℝ) * mesh ≤ t - A := by
    rw [← le_div_iff₀ hmesh]
    exact hj0le
  have hhigh : t - A < ((j0 : ℝ) + 1) * mesh := by
    rw [← div_lt_iff₀ hmesh]
    exact hj0lt
  rw [abs_le]
  constructor <;> nlinarith

end Grid

section Plateau

variable {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]

/-- **Grid union bound.**  If the shortcut event at the wider radius has small mass at every grid
point of a window, and the narrow-radius shortcut event at any window time is contained in the
wide-radius shortcut event at a nearby grid point, then the whole window is hard at the narrow
radius, apart from the exceptional set and the grid union. -/
theorem measureReal_forall_notMem_ge
    (G : Set Omega) {Lc : ℝ} (hGc : mu.real Gᶜ ≤ Lc)
    (easyNarrow easyWide : ℝ → Set Omega) {mesh : ℝ}
    (htrans : ∀ t u : ℝ, |t - u| ≤ mesh → easyNarrow t ⊆ easyWide u)
    {N : ℕ} (g : Fin N → ℝ) (A W : ℝ)
    (hcover : ∀ t ∈ Set.Icc A (A + W), ∃ j, |t - g j| ≤ mesh)
    {b : ℝ} (hb : ∀ j, mu.real (G ∩ easyWide (g j)) ≤ b) :
    1 - Lc - (N : ℝ) * b ≤ mu.real {x | ∀ t ∈ Set.Icc A (A + W), x ∉ easyNarrow t} := by
  classical
  set bad : Set Omega := {x | ∃ t ∈ Set.Icc A (A + W), x ∈ easyNarrow t} with hbad
  have hsub : bad ⊆ Gᶜ ∪ ⋃ j : Fin N, (G ∩ easyWide (g j)) := by
    rintro x ⟨t, ht, hx⟩
    by_cases hG : x ∈ G
    · obtain ⟨j, hj⟩ := hcover t ht
      exact Or.inr (Set.mem_iUnion.mpr ⟨j, ⟨hG, htrans t (g j) hj hx⟩⟩)
    · exact Or.inl hG
  have hunion : mu.real (⋃ j : Fin N, (G ∩ easyWide (g j))) ≤ (N : ℝ) * b := by
    refine le_trans (measureReal_iUnion_fintype_le _) ?_
    calc
      (∑ j : Fin N, mu.real (G ∩ easyWide (g j))) ≤ ∑ _j : Fin N, b :=
        Finset.sum_le_sum fun j _ => hb j
      _ = (N : ℝ) * b := by simp [Finset.sum_const, mul_comm]
  have hbadle : mu.real bad ≤ Lc + (N : ℝ) * b :=
    le_trans (measureReal_mono hsub)
      (le_trans (measureReal_union_le _ _) (add_le_add hGc hunion))
  have hcompl : {x | ∀ t ∈ Set.Icc A (A + W), x ∉ easyNarrow t} = badᶜ := by
    ext x
    simp [hbad, not_exists]
  have hcover1 : (1 : ℝ) ≤ mu.real bad + mu.real badᶜ := by
    have huniv : mu.real (Set.univ : Set Omega) = 1 := by
      simp
    calc
      (1 : ℝ) = mu.real (Set.univ : Set Omega) := huniv.symm
      _ = mu.real (bad ∪ badᶜ) := by rw [Set.union_compl_self]
      _ ≤ mu.real bad + mu.real badᶜ := measureReal_union_le _ _
  rw [hcompl]
  linarith

end Plateau

section MetricTransfer

variable {Omega : Type*} {E : Type*} [PseudoMetricSpace E]

/-- **Mesh transfer.**  A shortcut at the narrow radius at one time is a shortcut at the wide
radius at every nearby time, as soon as the orbit speed times the mesh fits inside the radius gap.
-/
theorem easySet_subset_of_speed
    (evolve : Omega → ℝ → E) (targets : Omega → Set E) {speed epsn epsw mesh : ℝ}
    (hspeed : ∀ x t u, dist (evolve x t) (evolve x u) ≤ speed * |t - u|)
    (hspeed0 : 0 ≤ speed) (hgap : speed * mesh ≤ epsw - epsn)
    {t u : ℝ} (htu : |t - u| ≤ mesh) :
    {x | ∃ z ∈ targets x, dist (evolve x t) z ≤ epsn} ⊆
      {x | ∃ z ∈ targets x, dist (evolve x u) z ≤ epsw} := by
  rintro x ⟨z, hz, hdz⟩
  refine ⟨z, hz, ?_⟩
  have hut : |u - t| ≤ mesh := by rwa [abs_sub_comm]
  calc
    dist (evolve x u) z ≤ dist (evolve x u) (evolve x t) + dist (evolve x t) z :=
      dist_triangle _ _ _
    _ ≤ speed * |u - t| + epsn := add_le_add (hspeed x u t) hdz
    _ ≤ speed * mesh + epsn := by nlinarith
    _ ≤ epsw := by linarith

end MetricTransfer

section Capstone

variable {Omega : Type*} [MeasurableSpace Omega] (mu : Measure Omega) [IsProbabilityMeasure mu]

/-- **Continuous plateau from a late fixed-time bound.**  If the wide-radius shortcut event has
`limsup` mass at most `b` on the good set, then for every window length and every tolerance there
is one time beyond which *every* window origin keeps the whole window hard at the narrow radius,
apart from the exceptional set, the grid union bound, and the tolerance. -/
theorem exists_time_forall_interval_hard
    (G : Set Omega) {Lc : ℝ} (hGc : mu.real Gᶜ ≤ Lc)
    (easyNarrow easyWide : ℝ → Set Omega) {mesh : ℝ} (hmesh : 0 < mesh)
    (htrans : ∀ t u : ℝ, |t - u| ≤ mesh → easyNarrow t ⊆ easyWide u)
    {b : ℝ} (hlate : ∀ q : ℝ, 0 < q → ∃ T : ℝ, ∀ t, T ≤ t → mu.real (G ∩ easyWide t) ≤ b + q)
    (W : ℝ) {q : ℝ} (hq : 0 < q) :
    ∃ T : ℝ, ∀ A, T ≤ A →
      1 - Lc - (plateauGridCount W mesh : ℝ) * b - q ≤
        mu.real {x | ∀ t ∈ Set.Icc A (A + W), x ∉ easyNarrow t} := by
  have hN1 : 1 ≤ plateauGridCount W mesh := one_le_plateauGridCount W mesh
  have hNpos : (0 : ℝ) < (plateauGridCount W mesh : ℝ) := by exact_mod_cast hN1
  obtain ⟨T, hT⟩ := hlate (q / (plateauGridCount W mesh : ℝ)) (by positivity)
  refine ⟨T, fun A hA => ?_⟩
  have hgrid := measureReal_forall_notMem_ge mu G hGc easyNarrow easyWide htrans
    (g := fun j : Fin (plateauGridCount W mesh) => plateauGridPoint A mesh (j : ℕ)) A W
    (fun t ht => exists_plateauGrid_near hmesh A ht)
    (b := b + q / (plateauGridCount W mesh : ℝ))
    (fun j => hT _ (le_trans hA (plateauGridPoint_le A hmesh.le (j : ℕ))))
  have harith : (plateauGridCount W mesh : ℝ) *
      (b + q / (plateauGridCount W mesh : ℝ)) =
      (plateauGridCount W mesh : ℝ) * b + q := by
    field_simp
  rw [harith] at hgrid
  linarith

/-- **The continuous plateau theorem.**  With a uniform orbit speed and a positive radius gap the
mesh is `(epsw - epsn)/speed`, and the late fixed-time bound becomes a whole-window statement at
the narrow radius. -/
theorem exists_time_forall_interval_hard_of_speed
    {E : Type*} [PseudoMetricSpace E]
    (evolve : Omega → ℝ → E) (targets : Omega → Set E)
    {speed : ℝ} (hspeed0 : 0 < speed)
    (hspeed : ∀ x t u, dist (evolve x t) (evolve x u) ≤ speed * |t - u|)
    {epsn epsw : ℝ} (hgap : epsn < epsw)
    (G : Set Omega) {Lc : ℝ} (hGc : mu.real Gᶜ ≤ Lc)
    {b : ℝ} (hlate : ∀ q : ℝ, 0 < q → ∃ T : ℝ, ∀ t, T ≤ t →
      mu.real (G ∩ {x | ∃ z ∈ targets x, dist (evolve x t) z ≤ epsw}) ≤ b + q)
    (W : ℝ) {q : ℝ} (hq : 0 < q) :
    ∃ T : ℝ, ∀ A, T ≤ A →
      1 - Lc - (plateauGridCount W ((epsw - epsn) / speed) : ℝ) * b - q ≤
        mu.real {x | ∀ t ∈ Set.Icc A (A + W),
          x ∉ {y | ∃ z ∈ targets y, dist (evolve y t) z ≤ epsn}} := by
  have hmesh : 0 < (epsw - epsn) / speed := by
    apply div_pos (by linarith) hspeed0
  refine exists_time_forall_interval_hard mu G hGc
    (fun t => {x | ∃ z ∈ targets x, dist (evolve x t) z ≤ epsn})
    (fun t => {x | ∃ z ∈ targets x, dist (evolve x t) z ≤ epsw}) hmesh ?_ hlate W hq
  intro t u htu
  refine easySet_subset_of_speed evolve targets hspeed hspeed0.le ?_ htu
  rw [mul_div_cancel₀ _ hspeed0.ne']

end Capstone

section Orbit

variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]

omit [Nonempty d] in
/-- **Uniform orbit speed.**  A family of self-adjoint generators of norm at most `speed`, acting
on unit seeds, gives Schrödinger orbits that are `speed`-Lipschitz in time. -/
theorem dist_unitaryOrbit_le {Omega : Type*} (H : Omega → Matrix d d ℂ)
    (hH : ∀ x, IsSelfAdjoint (H x)) (psi : Omega → EuclideanSpace ℂ d)
    (hpsi : ∀ x, ‖psi x‖ ≤ 1) {speed : ℝ} (hbound : ∀ x, ‖H x‖ ≤ speed)
    (x : Omega) (t u : ℝ) :
    dist ((EuclideanSpace.equiv d ℂ).symm (unitaryEvolution (H x) t *ᵥ (psi x).ofLp))
        ((EuclideanSpace.equiv d ℂ).symm (unitaryEvolution (H x) u *ᵥ (psi x).ofLp))
      ≤ speed * |t - u| := by
  rw [dist_eq_norm]
  refine le_trans (norm_unitaryEvolution_mulVec_time_sub_le (hH x) t u (psi x)) ?_
  have h0 : (0 : ℝ) ≤ ‖H x‖ := norm_nonneg _
  have habs : (0 : ℝ) ≤ |t - u| := abs_nonneg _
  calc
    ‖H x‖ * |t - u| * ‖psi x‖ ≤ ‖H x‖ * |t - u| * 1 :=
      mul_le_mul_of_nonneg_left (hpsi x) (by positivity)
    _ = ‖H x‖ * |t - u| := by ring
    _ ≤ speed * |t - u| := mul_le_mul_of_nonneg_right (hbound x) habs

end Orbit

end GaloisForLFunctions.HTGeometry
