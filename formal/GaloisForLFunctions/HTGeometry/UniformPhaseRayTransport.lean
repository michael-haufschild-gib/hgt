import GaloisForLFunctions.HTGeometry.TorsionCapAnchoredCount

/-!
# The recurrence polygon on an arbitrary orthonormal family

The uniform phase ray of `(1)` is defined by an orthonormal family in any complex inner product
space, and the coordinate model is its pullback: the overlap of a uniform phase ray with an ambient
target equals the overlap of the coordinate ray with the pullback of that target, and the pullback is
a contraction by Bessel's inequality.

Consequently a target dictionary in the ambient space is at least as hard as its normalized pullback
dictionary, which has no more elements.  The prime-torsion recurrence polygon therefore holds for
every orthonormal family, with the same cap condition.
-/

open Real RHTower

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section AmbientRays

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {D : ℕ}

/-- **`(1)` on an orthonormal family.**  The uniform phase ray of a unimodular coordinate vector. -/
def uniformPhaseRayOf (f : Fin D → V) (q : Fin D → ℂ) : V :=
  ∑ a, (((Real.sqrt (D : ℝ))⁻¹ : ℂ) * q a) • f a

/-- The pullback of an ambient target to coordinates. -/
def pullbackVector (f : Fin D → V) (y : V) : EuclideanSpace ℂ (Fin D) :=
  WithLp.toLp 2 fun a => (inner ℂ (f a) y : ℂ)

theorem inner_uniformPhaseRayOf (f : Fin D → V) (q : Fin D → ℂ) (y : V) :
    (inner ℂ (uniformPhaseRayOf f q) y : ℂ)
      = (inner ℂ (phaseRay q) (pullbackVector f y) : ℂ) := by
  rw [uniformPhaseRayOf, sum_inner, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [inner_smul_left, RCLike.inner_apply]
  exact mul_comm _ _

/-- Bessel's inequality: pulling back is a contraction. -/
theorem norm_pullbackVector_le {f : Fin D → V} (horth : Orthonormal ℂ f) (y : V) :
    ‖pullbackVector f y‖ ≤ ‖y‖ := by
  have hb : ∑ a, ‖(inner ℂ (f a) y : ℂ)‖ ^ (2 : ℕ) ≤ ‖y‖ ^ (2 : ℕ) := horth.sum_inner_products_le y
  rw [pullbackVector, EuclideanSpace.norm_eq]
  have hcoord : ∀ a : Fin D,
      ‖((WithLp.toLp 2 fun a => (inner ℂ (f a) y : ℂ) : EuclideanSpace ℂ (Fin D))).ofLp a‖ ^ (2 : ℕ)
        = ‖(inner ℂ (f a) y : ℂ)‖ ^ (2 : ℕ) := fun a => rfl
  rw [Finset.sum_congr rfl fun a (_ : a ∈ Finset.univ) => hcoord a]
  calc Real.sqrt (∑ a, ‖(inner ℂ (f a) y : ℂ)‖ ^ (2 : ℕ)) ≤ Real.sqrt (‖y‖ ^ (2 : ℕ)) :=
        Real.sqrt_le_sqrt hb
    _ = ‖y‖ := Real.sqrt_sq (norm_nonneg y)

/-- The pullback of a uniform phase ray is its coordinate vector. -/
theorem pullbackVector_uniformPhaseRayOf {f : Fin D → V} (horth : Orthonormal ℂ f)
    (r : Fin D → ℂ) : pullbackVector f (uniformPhaseRayOf f r) = phaseRay r := by
  classical
  have hij : ∀ i j : Fin D, (inner ℂ (f i) (f j) : ℂ) = if i = j then 1 else 0 :=
    fun i j => orthonormal_iff_ite.mp horth i j
  refine PiLp.ext fun a => ?_
  show (inner ℂ (f a) (uniformPhaseRayOf f r) : ℂ) = ((Real.sqrt (D : ℝ))⁻¹ : ℂ) * r a
  rw [uniformPhaseRayOf, inner_sum]
  rw [Finset.sum_eq_single a]
  · rw [inner_smul_right, hij a a, if_pos rfl, mul_one]
  · intro b _ hba
    rw [inner_smul_right, hij a b, if_neg (Ne.symm hba), mul_zero]
  · intro ha
    exact absurd (Finset.mem_univ a) ha

theorem norm_uniformPhaseRayOf {f : Fin D → V} (horth : Orthonormal ℂ f) {q : Fin D → ℂ}
    (hq : ∀ a, ‖q a‖ = 1) (hD : 0 < D) : ‖uniformPhaseRayOf f q‖ = 1 := by
  have hinner : (inner ℂ (uniformPhaseRayOf f q) (uniformPhaseRayOf f q) : ℂ)
      = inner ℂ (phaseRay q) (phaseRay q) := by
    rw [inner_uniformPhaseRayOf, pullbackVector_uniformPhaseRayOf horth]
  have h1 : ‖uniformPhaseRayOf f q‖ ^ (2 : ℕ) = ‖phaseRay q‖ ^ (2 : ℕ) := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ), hinner]
  rw [norm_phaseRay hq hD] at h1
  nlinarith [norm_nonneg (uniformPhaseRayOf f q), h1]

/-- **`(17)` on an orthonormal family.**  The autonomous uniform-phase trajectory. -/
def flowRayOf (f : Fin D → V) (E : Fin D → ℝ) (t : ℝ) : V :=
  uniformPhaseRayOf f (flowPhaseVec E t)

theorem norm_flowRayOf {f : Fin D → V} (horth : Orthonormal ℂ f) (E : Fin D → ℝ) (t : ℝ)
    (hD : 0 < D) : ‖flowRayOf f E t‖ = 1 :=
  norm_uniformPhaseRayOf horth (fun a => norm_flowPhaseVec E t a) hD

theorem inner_flowRayOf {f : Fin D → V} (horth : Orthonormal ℂ f) (E : Fin D → ℝ) (t u : ℝ) :
    (inner ℂ (flowRayOf f E t) (flowRayOf f E u) : ℂ)
      = inner ℂ (flowRay E t) (flowRay E u) := by
  rw [flowRayOf, flowRayOf, inner_uniformPhaseRayOf, pullbackVector_uniformPhaseRayOf horth]
  rfl

/-- The squared trace distance is the projective deficit. -/
theorem sq_pureStateTraceDistance {ι : Type*} [Fintype ι] (u v : EuclideanSpace ℂ ι)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) :
    pureStateTraceDistance u v ^ (2 : ℕ) = 1 - ‖(inner ℂ u v : ℂ)‖ ^ (2 : ℕ) := by
  have h1 : ‖(inner ℂ u v : ℂ)‖ ≤ 1 := by
    refine le_trans (norm_inner_le_norm (𝕜 := ℂ) u v) ?_
    nlinarith [norm_nonneg u, norm_nonneg v]
  rw [pureStateTraceDistance, Real.sq_sqrt]
  nlinarith [norm_nonneg (inner ℂ u v : ℂ), h1]

/-- The normalized pullbacks of an ambient target dictionary. -/
def pullbackDict (f : Fin D → V) (Y : Finset V) : Finset (EuclideanSpace ℂ (Fin D)) :=
  letI := Classical.decPred fun z : EuclideanSpace ℂ (Fin D) => ‖z‖ = 1
  (Y.image fun y => (‖pullbackVector f y‖ : ℂ)⁻¹ • pullbackVector f y).filter fun z => ‖z‖ = 1

theorem card_pullbackDict_le (f : Fin D → V) (Y : Finset V) :
    (pullbackDict f Y).card ≤ Y.card :=
  le_trans (Finset.card_filter_le _ _) Finset.card_image_le

theorem norm_of_mem_pullbackDict {f : Fin D → V} {Y : Finset V}
    {z : EuclideanSpace ℂ (Fin D)} (hz : z ∈ pullbackDict f Y) : ‖z‖ = 1 := by
  simp only [pullbackDict, Finset.mem_filter] at hz
  exact hz.2

/-- **Hardness transports from coordinates to the ambient space.**  A target is at least as far from
the ambient ray as its normalized pullback is from the coordinate ray. -/
theorem sq_lt_one_sub_norm_inner_sq {f : Fin D → V} (horth : Orthonormal ℂ f) {Y : Finset V}
    (hY : ∀ y ∈ Y, ‖y‖ ≤ 1) {q : Fin D → ℂ} (hq : ∀ a, ‖q a‖ = 1) (hD : 0 < D)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hhard : ∀ z ∈ pullbackDict f Y, δ < pureStateTraceDistance (phaseRay q) z)
    {y : V} (hy : y ∈ Y) :
    δ ^ (2 : ℕ) < 1 - ‖(inner ℂ (uniformPhaseRayOf f q) y : ℂ)‖ ^ (2 : ℕ) := by
  classical
  set w : EuclideanSpace ℂ (Fin D) := pullbackVector f y with hwdef
  have hwle : ‖w‖ ≤ 1 := le_trans (norm_pullbackVector_le horth y) (hY y hy)
  have hinner : (inner ℂ (uniformPhaseRayOf f q) y : ℂ) = inner ℂ (phaseRay q) w :=
    inner_uniformPhaseRayOf f q y
  rcases eq_or_ne w 0 with hw0 | hw0
  · rw [hinner, hw0, inner_zero_right, norm_zero]
    nlinarith
  · have hwpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
    set z : EuclideanSpace ℂ (Fin D) := (‖w‖ : ℂ)⁻¹ • w with hzdef
    have hz1 : ‖z‖ = 1 := by
      rw [hzdef, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hwpos.le,
        inv_mul_cancel₀ (ne_of_gt hwpos)]
    have hzmem : z ∈ pullbackDict f Y := by
      simp only [pullbackDict, Finset.mem_filter, Finset.mem_image]
      exact ⟨⟨y, hy, rfl⟩, hz1⟩
    have hwz : w = (‖w‖ : ℂ) • z := by
      rw [hzdef, smul_smul, mul_inv_cancel₀ (by exact_mod_cast ne_of_gt hwpos), one_smul]
    have hnorm : ‖(inner ℂ (phaseRay q) w : ℂ)‖ = ‖w‖ * ‖(inner ℂ (phaseRay q) z : ℂ)‖ := by
      have hexp : (inner ℂ (phaseRay q) w : ℂ) = (‖w‖ : ℂ) * inner ℂ (phaseRay q) z := by
        conv_lhs => rw [hwz]
        rw [inner_smul_right]
      rw [hexp, norm_mul, Complex.norm_real, Real.norm_of_nonneg hwpos.le]
    have hdel := hhard z hzmem
    have hsq := sq_pureStateTraceDistance (phaseRay q) z
      (le_of_eq (norm_phaseRay hq hD)) (le_of_eq hz1)
    have hnn := pureStateTraceDistance_nonneg (phaseRay q) z
    have hd2 : δ ^ (2 : ℕ) < 1 - ‖(inner ℂ (phaseRay q) z : ℂ)‖ ^ (2 : ℕ) := by nlinarith
    have hw2 : ‖w‖ ^ (2 : ℕ) ≤ 1 := by nlinarith
    have hkey : (‖w‖ * ‖(inner ℂ (phaseRay q) z : ℂ)‖) ^ (2 : ℕ)
        ≤ ‖(inner ℂ (phaseRay q) z : ℂ)‖ ^ (2 : ℕ) := by
      nlinarith [sq_nonneg ‖(inner ℂ (phaseRay q) z : ℂ)‖]
    rw [hinner, hnorm]
    linarith

/-- **Theorem B on an arbitrary orthonormal family.**  The recurrence polygon does not depend on the
coordinate model: any orthonormal family in any complex inner product space carries it, with the same
cap condition on the ambient dictionary. -/
theorem exists_late_recurrence_hard_polygon_orthonormal {d k : ℕ} [NeZero k] (hk : k.Prime)
    (f : Fin (d + 1) → V) (horth : Orthonormal ℂ f)
    (E : Fin (d + 1) → ℝ) (hind : LinearIndependent ℚ (projectiveGapPacket E))
    (Y : Finset V) (hY : ∀ y ∈ Y, ‖y‖ ≤ 1) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hδ2 : 2 * δ ^ (2 : ℕ) ≤ 1)
    (h13 : 4 * ((k : ℝ) - 1) * (Y.card : ℝ)
      * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1)) < 1)
    {ρ : ℝ} (hρ : 0 < ρ) (A : ℝ) :
    ∃ R : ℝ, A < R ∧
      1 - ‖(inner ℂ (flowRayOf f E R) (flowRayOf f E 0) : ℂ)‖ ^ (2 : ℕ) < ρ ^ (2 : ℕ) ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ k - 1 → ∀ y ∈ Y,
        δ ^ (2 : ℕ) < 1 - ‖(inner ℂ (flowRayOf f E ((j : ℝ) * R / (k : ℝ))) y : ℂ)‖ ^ (2 : ℕ) := by
  have hk1 : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.one_lt.le
    linarith
  have hcard : ((pullbackDict f Y).card : ℝ) ≤ (Y.card : ℝ) := by
    exact_mod_cast card_pullbackDict_le f Y
  have hc : (0 : ℝ) ≤ 4 * ((k : ℝ) - 1)
      * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1)) :=
    mul_nonneg (mul_nonneg (by norm_num) hk1) (Real.exp_pos _).le
  have h13' : 4 * ((k : ℝ) - 1) * ((pullbackDict f Y).card : ℝ)
      * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1)) < 1 := by
    refine lt_of_le_of_lt ?_ h13
    calc 4 * ((k : ℝ) - 1) * ((pullbackDict f Y).card : ℝ)
          * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1))
        = (4 * ((k : ℝ) - 1) * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1)))
            * ((pullbackDict f Y).card : ℝ) := by ring
      _ ≤ (4 * ((k : ℝ) - 1) * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1)))
            * (Y.card : ℝ) := mul_le_mul_of_nonneg_left hcard hc
      _ = 4 * ((k : ℝ) - 1) * (Y.card : ℝ)
            * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1)) := by ring
  obtain ⟨R, hRA, hrec, hhard⟩ :=
    exists_late_recurrence_hard_polygon_of_cap hk E hind (pullbackDict f Y)
      (fun z hz => norm_of_mem_pullbackDict hz) hδ0 hδ2 h13' hρ A
  refine ⟨R, hRA, ?_, ?_⟩
  · rw [inner_flowRayOf horth]
    have hsq := sq_pureStateTraceDistance (flowRay E R) (flowRay E 0)
      (le_of_eq (norm_flowRay E R (Nat.succ_pos d)))
      (le_of_eq (norm_flowRay E 0 (Nat.succ_pos d)))
    have hnn := pureStateTraceDistance_nonneg (flowRay E R) (flowRay E 0)
    nlinarith
  · intro j hj1 hj2 y hy
    exact sq_lt_one_sub_norm_inner_sq horth hY (fun a => norm_flowPhaseVec E _ a)
      (Nat.succ_pos d) hδ0 hδ1 (fun z hz => hhard j hj1 hj2 z hz) hy

end AmbientRays

section ChoiFamily

variable {D : ℕ}

/-- The Choi vector `|e_a⟩|ē_a⟩` of an eigenvector. -/
def choiVec (e : Fin D → EuclideanSpace ℂ (Fin D)) (a : Fin D) :
    EuclideanSpace ℂ (Fin D × Fin D) :=
  WithLp.toLp 2 fun ij => (e a).ofLp ij.1 * (starRingEnd ℂ) ((e a).ofLp ij.2)

theorem inner_choiVec (e : Fin D → EuclideanSpace ℂ (Fin D)) (a b : Fin D) :
    (inner ℂ (choiVec e a) (choiVec e b) : ℂ)
      = (inner ℂ (e a) (e b) : ℂ) * (starRingEnd ℂ) (inner ℂ (e a) (e b) : ℂ) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, choiVec]
  rw [Fintype.sum_prod_type]
  dsimp only
  have hfac : ∀ i j : Fin D,
      (e b).ofLp i * (starRingEnd ℂ) ((e b).ofLp j)
        * (starRingEnd ℂ) ((e a).ofLp i * (starRingEnd ℂ) ((e a).ofLp j))
      = ((e b).ofLp i * (starRingEnd ℂ) ((e a).ofLp i))
        * (starRingEnd ℂ) ((e b).ofLp j * (starRingEnd ℂ) ((e a).ofLp j)) := by
    intro i j
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => hfac i j]
  rw [← Finset.sum_mul_sum, ← map_sum]

/-- **`(32)`, the eigenbasis independence.**  The Choi family of an orthonormal eigenbasis is
orthonormal, whatever the eigenbasis. -/
theorem orthonormal_choiVec {e : Fin D → EuclideanSpace ℂ (Fin D)} (he : Orthonormal ℂ e) :
    Orthonormal ℂ (choiVec e) := by
  classical
  refine orthonormal_iff_ite.mpr fun a b => ?_
  rw [inner_choiVec, orthonormal_iff_ite.mp he a b]
  by_cases hab : a = b <;> simp [hab]

/-- **`(32)`.**  The static Choi trajectory is the uniform phase ray `(17)` of the Choi family. -/
theorem choiTrajectory_eq (e : Fin D → EuclideanSpace ℂ (Fin D)) (E : Fin D → ℝ) (t : ℝ) :
    flowRayOf (choiVec e) E t
      = ∑ a, (((Real.sqrt (D : ℝ))⁻¹ : ℂ)
          * Complex.exp (((-(t * E a) : ℝ) : ℂ) * Complex.I)) • choiVec e a := rfl

/-- **The recurrence polygon on the static Choi trajectory.**  An `n`-qubit time-independent
Hamiltonian whose anchored spectral gaps are rationally independent has arbitrarily late Choi
recurrence cycles whose `k-1` equally spaced interior slices all avoid the target dictionary. -/
theorem exists_late_recurrence_hard_polygon_choi {d k : ℕ} [NeZero k] (hk : k.Prime)
    {e : Fin (d + 1) → EuclideanSpace ℂ (Fin (d + 1))} (he : Orthonormal ℂ e)
    (E : Fin (d + 1) → ℝ) (hind : LinearIndependent ℚ (projectiveGapPacket E))
    (Y : Finset (EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))) (hY : ∀ y ∈ Y, ‖y‖ ≤ 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hδ2 : 2 * δ ^ (2 : ℕ) ≤ 1)
    (h13 : 4 * ((k : ℝ) - 1) * (Y.card : ℝ)
      * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1)) < 1)
    {ρ : ℝ} (hρ : 0 < ρ) (A : ℝ) :
    ∃ R : ℝ, A < R ∧
      1 - ‖(inner ℂ (flowRayOf (choiVec e) E R) (flowRayOf (choiVec e) E 0) : ℂ)‖ ^ (2 : ℕ) < ρ ^ (2 : ℕ) ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ k - 1 → ∀ y ∈ Y,
        δ ^ (2 : ℕ) < 1
          - ‖(inner ℂ (flowRayOf (choiVec e) E ((j : ℝ) * R / (k : ℝ))) y : ℂ)‖ ^ (2 : ℕ) :=
  exists_late_recurrence_hard_polygon_orthonormal hk (choiVec e) (orthonormal_choiVec he) E hind
    Y hY hδ0 hδ1 hδ2 h13 hρ A

/-- **The genericity input.**  A maximally projective spectrum has rationally independent anchored
gaps, so the recurrence polygon applies to it verbatim. -/
theorem exists_late_recurrence_hard_polygon_choi_of_maximallyProjective {d k : ℕ} [NeZero k]
    (hk : k.Prime) {e : Fin (d + 1) → EuclideanSpace ℂ (Fin (d + 1))} (he : Orthonormal ℂ e)
    (E : Fin (d + 1) → ℝ) (hmax : MaximallyProjectiveEnergy E)
    (Y : Finset (EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))) (hY : ∀ y ∈ Y, ‖y‖ ≤ 1)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) (hδ2 : 2 * δ ^ (2 : ℕ) ≤ 1)
    (h13 : 4 * ((k : ℝ) - 1) * (Y.card : ℝ)
      * Real.exp (-((1 - 4 * δ ^ (2 : ℕ)) / 4) * ((d : ℝ) + 1)) < 1)
    {ρ : ℝ} (hρ : 0 < ρ) (A : ℝ) :
    ∃ R : ℝ, A < R ∧
      1 - ‖(inner ℂ (flowRayOf (choiVec e) E R) (flowRayOf (choiVec e) E 0) : ℂ)‖ ^ (2 : ℕ) < ρ ^ (2 : ℕ) ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ k - 1 → ∀ y ∈ Y,
        δ ^ (2 : ℕ) < 1
          - ‖(inner ℂ (flowRayOf (choiVec e) E ((j : ℝ) * R / (k : ℝ))) y : ℂ)‖ ^ (2 : ℕ) :=
  exists_late_recurrence_hard_polygon_choi hk he E
    (projectiveGapPacket_linearIndependent hmax) Y hY hδ0 hδ1 hδ2 h13 hρ A

end ChoiFamily

end

end GaloisForLFunctions.HTGeometry
