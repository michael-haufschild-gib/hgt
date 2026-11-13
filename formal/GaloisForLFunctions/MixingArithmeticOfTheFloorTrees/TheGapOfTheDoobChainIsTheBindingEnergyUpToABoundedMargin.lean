import GaloisForLFunctions.MixingArithmeticOfTheFloorTrees.TheBoundStatesOfAWindowAreTheSlowModesOfItsDoobChain

/-!
# The gap of the Doob chain is the binding energy up to a bounded margin

On the window `(2r, 2r + J]`, `J ≥ 2r`, at block size `2r`, the packets constant on the coarse
blocks `(2, 3]` and `(3, 4]`, refined, span a plane on which the neutral part is the fixed
`2 × 2` matrix of these two blocks (refinement invariance). Its entries do not depend on `r`, `J`
or the contacts: the blocks have ratio below two. So on that plane the neutral part is at most
`c₀ = max(N(2, 2), N(3, 3)) + |N(2, 3)|` times the mass (`sum_coarse_plane_le`).

Every hyperplane meets the plane. Taking the hyperplane orthogonal to the ground vector `φ`, the
ground-state transform turns this into a Poincaré test (`exists_doob_test_le`): there is a
nonconstant `f`, centred for `φ²`, with

  `E(f) ≤ (μ + c₀) Σ φ_i² f_i²`,

where `μ = −λ` is the binding energy. So the spectral gap of the Doob chain of every window is at
most its binding energy plus the absolute constant `c₀`. The binding energy grows like the square
root of the ratio, while the margin of gap over energy stays below `c₀`; the Riemann hypothesis is
the statement that this bounded margin is nonnegative on every window. Under it the Poincaré
constant of every Doob chain lies in `[μ, μ + c₀]`
(`poincare_constant_mem_of_riemannHypothesis`), so gap and binding energy are asymptotically
equal along the ratios.
-/

open Finset Matrix
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.AbsoluteGeometryOfSpecZ

noncomputable section

namespace GaloisForLFunctions.MixingArithmeticOfTheFloorTrees

/-- The absolute constant bounding the margin: the larger diagonal entry plus the coupling of
the coarse blocks `(2, 3]` and `(3, 4]`. -/
def marginBound (Q : ℕ) : ℝ := max (neutralBlock Q 2 2) (neutralBlock Q 3 3) + |neutralBlock Q 2 3|

/-- The packet of a coarse block `(2 + i, 3 + i]`, `i ∈ {0, 1}`, refined to block size `2r`. -/
def coarseBlock (r i : ℕ) (j : ℕ) : ℝ := refineStep r (fun l => if l = i then 1 else 0) j

/-- The refined plane of the two coarse blocks. -/
def coarsePlane (r : ℕ) (s t : ℝ) (j : ℕ) : ℝ :=
  refineStep r (fun l => if l = 0 then s else if l = 1 then t else 0) j

/-- On the refined plane the neutral part is the form of the two coarse blocks. -/
theorem sum_coarsePlane_neutralBlock {r : ℕ} (hr : 1 ≤ r) (Q : ℕ) (s t : ℝ) :
    ∑ j ∈ range (r * 2), ∑ l ∈ range (r * 2), coarsePlane r s t j * coarsePlane r s t l *
        neutralBlock Q (r * 2 + j) (r * 2 + l) =
      neutralBlock Q 2 2 * s ^ 2 + 2 * neutralBlock Q 2 3 * s * t + neutralBlock Q 3 3 * t ^ 2 := by
  have h := sum_neutralBlock_refine (R := 2) (by norm_num) hr Q 2
    (fun l => if l = 0 then s else if l = 1 then t else 0)
  unfold coarsePlane
  rw [h]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num
  rw [neutralBlock_comm Q 3 2]
  ring

/-- The mass of the refined plane. -/
theorem sum_coarsePlane_sq {r : ℕ} (hr : 1 ≤ r) (s t : ℝ) :
    ∑ j ∈ range (r * 2), coarsePlane r s t j ^ 2 = s ^ 2 + t ^ 2 := by
  unfold coarsePlane
  rw [sum_refineStep_sq hr 2]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num

/-- **On the refined plane the neutral part is at most `c₀` times the mass.** -/
theorem sum_coarse_plane_le {r : ℕ} (hr : 1 ≤ r) (Q : ℕ) (s t : ℝ) :
    ∑ j ∈ range (r * 2), ∑ l ∈ range (r * 2), coarsePlane r s t j * coarsePlane r s t l *
        neutralBlock Q (r * 2 + j) (r * 2 + l) ≤
      marginBound Q * ∑ j ∈ range (r * 2), coarsePlane r s t j ^ 2 := by
  rw [sum_coarsePlane_neutralBlock hr, sum_coarsePlane_sq hr]
  unfold marginBound
  have h1 : neutralBlock Q 2 2 ≤ max (neutralBlock Q 2 2) (neutralBlock Q 3 3) := le_max_left _ _
  have h2 : neutralBlock Q 3 3 ≤ max (neutralBlock Q 2 2) (neutralBlock Q 3 3) := le_max_right _ _
  have h3 : 2 * neutralBlock Q 2 3 * s * t ≤ |neutralBlock Q 2 3| * (s ^ 2 + t ^ 2) := by
    have hst : 2 * |s * t| ≤ s ^ 2 + t ^ 2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|s| - |t|), sq_abs s, sq_abs t]
    have hb : 2 * neutralBlock Q 2 3 * s * t ≤ |neutralBlock Q 2 3| * (2 * |s * t|) := by
      have := le_abs_self (2 * neutralBlock Q 2 3 * s * t)
      rw [show |2 * neutralBlock Q 2 3 * s * t| = |neutralBlock Q 2 3| * (2 * |s * t|) by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_two]; ring] at this
      exact this
    exact hb.trans (mul_le_mul_of_nonneg_left hst (abs_nonneg _))
  nlinarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg s),
    mul_le_mul_of_nonneg_right h2 (sq_nonneg t)]

/-- The refined plane as a vector on the window `(2r, 2r + J]`, `J ≥ 2r`. -/
def windowPlane (r J : ℕ) (s t : ℝ) (i : Fin J) : ℝ :=
  if (i : ℕ) < r * 2 then coarsePlane r s t i else 0

theorem bilin_windowPlane {r J : ℕ} (hJ : r * 2 ≤ J) (Q : ℕ) (s t : ℝ) :
    bilin (neutralWindow Q (r * 2) J) (windowPlane r J s t) (windowPlane r J s t) =
      ∑ j ∈ range (r * 2), ∑ l ∈ range (r * 2), coarsePlane r s t j * coarsePlane r s t l *
        neutralBlock Q (r * 2 + j) (r * 2 + l) := by
  have hext : ∀ j, extendFin (windowPlane r J s t) j =
      (if j < r * 2 then coarsePlane r s t j else 0) := by
    intro j
    by_cases hj : j < J
    · simp only [extendFin, dif_pos hj, windowPlane]
    · have hj2 : ¬ j < r * 2 := by omega
      simp only [extendFin, dif_neg hj, if_neg hj2]
  have hsub : range (r * 2) ⊆ range J := Finset.range_subset_range.mpr hJ
  have h : bilin (neutralWindow Q (r * 2) J) (windowPlane r J s t) (windowPlane r J s t) =
      ∑ j ∈ range J, ∑ l ∈ range J, extendFin (windowPlane r J s t) j *
        extendFin (windowPlane r J s t) l * neutralBlock Q (r * 2 + j) (r * 2 + l) :=
    sum_fin_windowMatrix_eq (neutralBlock Q) (r * 2) (windowPlane r J s t)
  rw [h]
  simp only [hext]
  calc ∑ j ∈ range J, ∑ l ∈ range J, (if j < r * 2 then coarsePlane r s t j else 0) *
        (if l < r * 2 then coarsePlane r s t l else 0) * neutralBlock Q (r * 2 + j) (r * 2 + l)
      = ∑ j ∈ range (r * 2), ∑ l ∈ range J, (if j < r * 2 then coarsePlane r s t j else 0) *
          (if l < r * 2 then coarsePlane r s t l else 0) *
            neutralBlock Q (r * 2 + j) (r * 2 + l) :=
        (Finset.sum_subset hsub fun j _ hj => Finset.sum_eq_zero fun l _ => by
          rw [if_neg (fun h => hj (Finset.mem_range.mpr h)), zero_mul, zero_mul]).symm
    _ = ∑ j ∈ range (r * 2), ∑ l ∈ range (r * 2), (if j < r * 2 then coarsePlane r s t j else 0) *
          (if l < r * 2 then coarsePlane r s t l else 0) *
            neutralBlock Q (r * 2 + j) (r * 2 + l) :=
        Finset.sum_congr rfl fun j _ => (Finset.sum_subset hsub fun l _ hl => by
          rw [if_neg (fun h => hl (Finset.mem_range.mpr h)), mul_zero, zero_mul]).symm
    _ = _ := Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => by
          rw [if_pos (Finset.mem_range.mp hj), if_pos (Finset.mem_range.mp hl)]

theorem sum_windowPlane_sq {r J : ℕ} (hr : 1 ≤ r) (hJ : r * 2 ≤ J) (s t : ℝ) :
    ∑ i, windowPlane r J s t i ^ 2 = s ^ 2 + t ^ 2 := by
  have h1 : ∑ i, windowPlane r J s t i ^ 2 =
      ∑ j ∈ range J, (if j < r * 2 then coarsePlane r s t j else 0) ^ 2 :=
    Fin.sum_univ_eq_sum_range (fun j => (if j < r * 2 then coarsePlane r s t j else 0) ^ 2) J
  rw [h1, ← sum_coarsePlane_sq hr s t, ← Finset.sum_range_add_sum_Ico _ hJ]
  have hz : ∑ j ∈ Ico (r * 2) J, (if j < r * 2 then coarsePlane r s t j else 0) ^ 2 = 0 :=
    Finset.sum_eq_zero fun j hj => by
      rw [if_neg (by have := Finset.mem_Ico.mp hj; omega)]
      ring
  rw [hz, add_zero]
  exact Finset.sum_congr rfl fun j hj => by rw [if_pos (Finset.mem_range.mp hj)]

/-- The plane is linear in its two coordinates. -/
theorem windowPlane_eq (r J : ℕ) (s t : ℝ) :
    windowPlane r J s t = fun i => s * windowPlane r J 1 0 i + t * windowPlane r J 0 1 i := by
  funext i
  unfold windowPlane coarsePlane refineStep
  by_cases h : (i : ℕ) < r * 2
  · simp only [if_pos h]
    by_cases h0 : (i : ℕ) / r = 0
    · simp only [if_pos h0]
      ring
    · by_cases h1 : (i : ℕ) / r = 1
      · simp only [if_neg h0, if_pos h1]
        ring
      · simp only [if_neg h0, if_neg h1]
        ring
  · simp only [if_neg h]
    ring

/-- Some point of the plane is orthogonal to a given vector. -/
theorem exists_windowPlane_orth (r J : ℕ) (φ : Fin J → ℝ) :
    ∃ s t : ℝ, (s ≠ 0 ∨ t ≠ 0) ∧ ∑ i, φ i * windowPlane r J s t i = 0 := by
  by_cases hq : ∑ i, φ i * windowPlane r J 0 1 i = 0
  · exact ⟨0, 1, Or.inr one_ne_zero, hq⟩
  · refine ⟨∑ i, φ i * windowPlane r J 0 1 i, -∑ i, φ i * windowPlane r J 1 0 i, Or.inl hq, ?_⟩
    rw [windowPlane_eq r J (∑ i, φ i * windowPlane r J 0 1 i) (-∑ i, φ i * windowPlane r J 1 0 i)]
    simp only [mul_add, Finset.sum_add_distrib]
    have e1 : ∑ i, φ i * ((∑ i, φ i * windowPlane r J 0 1 i) * windowPlane r J 1 0 i) =
        (∑ i, φ i * windowPlane r J 0 1 i) * ∑ i, φ i * windowPlane r J 1 0 i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∑ i, φ i * ((-∑ i, φ i * windowPlane r J 1 0 i) * windowPlane r J 0 1 i) =
        (-∑ i, φ i * windowPlane r J 1 0 i) * ∑ i, φ i * windowPlane r J 0 1 i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2]
    ring

/-- **The Doob gap is at most the binding energy plus `c₀`.** On every window `(2r, 2r + J]`
with `J ≥ 2r`, for a positive eigenvector `φ` of the neutral part with eigenvalue `λ`, some
`f` centred for `φ²`, with positive mass, has `E(f) ≤ (−λ + c₀) Σ φ_i² f_i²`. -/
theorem exists_doob_test_le {Q r J : ℕ} (hr : 1 ≤ r) (hJ : r * 2 ≤ J) {φ : Fin J → ℝ}
    (hφ : ∀ i, 0 < φ i) {lam : ℝ} (heig : neutralWindow Q (r * 2) J *ᵥ φ = lam • φ) :
    ∃ f : Fin J → ℝ, doobMean φ f = 0 ∧ 0 < doobMass φ f ∧
      doobEnergy (neutralWindow Q (r * 2) J) φ f ≤ (-lam + marginBound Q) * doobMass φ f := by
  obtain ⟨s, t, hst, horth⟩ := exists_windowPlane_orth r J φ
  have hmassx := sum_windowPlane_sq hr hJ s t
  have hpos : 0 < s ^ 2 + t ^ 2 := by
    rcases hst with h | h
    · have h2 := mul_pos (abs_pos.mpr h) (abs_pos.mpr h)
      nlinarith [abs_mul_abs_self s, sq_nonneg t]
    · have h2 := mul_pos (abs_pos.mpr h) (abs_pos.mpr h)
      nlinarith [abs_mul_abs_self t, sq_nonneg s]
  have hmass : doobMass φ (fun i => windowPlane r J s t i / φ i) =
      ∑ i, windowPlane r J s t i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by
      rw [div_pow, mul_div_cancel₀ _ (pow_ne_zero 2 (hφ i).ne')]
  refine ⟨fun i => windowPlane r J s t i / φ i, ?_, ?_, ?_⟩
  · unfold doobMean
    calc ∑ i, φ i ^ 2 * (windowPlane r J s t i / φ i) = ∑ i, φ i * windowPlane r J s t i :=
          Finset.sum_congr rfl fun i _ => by
            rw [sq, mul_assoc, mul_div_cancel₀ _ (hφ i).ne']
      _ = 0 := horth
  · rw [hmass, hmassx]
    exact hpos
  · have hdoob : bilin (neutralWindow Q (r * 2) J) (windowPlane r J s t) (windowPlane r J s t) =
        lam * doobMass φ (fun i => windowPlane r J s t i / φ i) +
          doobEnergy (neutralWindow Q (r * 2) J) φ (fun i => windowPlane r J s t i / φ i) := by
      have hx : (fun i => φ i * (windowPlane r J s t i / φ i)) = windowPlane r J s t :=
        funext fun i => mul_div_cancel₀ _ (hφ i).ne'
      calc bilin (neutralWindow Q (r * 2) J) (windowPlane r J s t) (windowPlane r J s t) =
            bilin (neutralWindow Q (r * 2) J) (fun i => φ i * (windowPlane r J s t i / φ i))
              (fun i => φ i * (windowPlane r J s t i / φ i)) := by rw [hx]
        _ = _ := bilin_mul_eq_doob (neutralWindow_symm Q (r * 2) J) heig
              (fun i => windowPlane r J s t i / φ i)
    have hform := sum_coarse_plane_le hr Q s t
    rw [← bilin_windowPlane hJ Q s t, sum_coarsePlane_sq hr] at hform
    rw [hmass, hmassx] at hdoob ⊢
    linarith

/-- **Under the Riemann hypothesis the Poincaré constant of every Doob chain lies between the
binding energy `μ = −λ` and `μ + c₀`**: every centred `f` has `E(f) ≥ μ Σ φ²f²`, and some centred
`f` of positive mass has `E(f) ≤ (μ + c₀) Σ φ²f²`. -/
theorem poincare_constant_mem_of_riemannHypothesis (hRH : RiemannHypothesis) {Q r J : ℕ}
    (hr : 1 ≤ r) (hJ : r * 2 ≤ J) (hQ : r * 2 + J ≤ Q * (r * 2)) {φ : Fin J → ℝ}
    (hφ : ∀ i, 0 < φ i) {lam : ℝ} (heig : neutralWindow Q (r * 2) J *ᵥ φ = lam • φ) :
    (∀ f : Fin J → ℝ, doobMean φ f = 0 →
        -lam * doobMass φ f ≤ doobEnergy (neutralWindow Q (r * 2) J) φ f) ∧
      ∃ f : Fin J → ℝ, doobMean φ f = 0 ∧ 0 < doobMass φ f ∧
        doobEnergy (neutralWindow Q (r * 2) J) φ f ≤ (-lam + marginBound Q) * doobMass φ f :=
  ⟨riemannHypothesis_iff_forall_doob_poincare.mp hRH Q (r * 2) J (by omega) hJ hQ φ hφ lam heig,
    exists_doob_test_le hr hJ hφ heig⟩

end GaloisForLFunctions.MixingArithmeticOfTheFloorTrees
