import GaloisForLFunctions.HTGeometry.ConstitutiveMarkedSymmetryQuotient

/-!
# Polar observer, compact recurrence, and open history lift

This module formalizes the exact finite-dimensional calibration in Theorem 5.1 of the restricted
history card.  A continuous additive quotient `q : V → K` represents the flat torus projection;
its kernel is the deck lattice.  The projected straight line is recurrent in compact `K`, while
the marked lift is proper.  The final section proves the rank-one polar energy identity and all
of its stated phase and time-reversal invariances.
-/

open Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Marked straight-line lift of a flat-torus one-parameter orbit. -/
def liftedStraightLine (v : V) (t : ℝ) : V := t • v

/-- Exact length of the marked straight-line lift. -/
theorem liftedStraightLine_norm (v : V) (t : ℝ) :
    ‖liftedStraightLine v t‖ = |t| * ‖v‖ := by
  simp [liftedStraightLine, norm_smul, Real.norm_eq_abs]

/-- Every nonconstant marked straight-line lift is proper. -/
theorem liftedStraightLine_isProperMap {v : V} (hv : v ≠ 0) :
    IsProperMap (liftedStraightLine v) := by
  let K : NNReal := ⟨‖v‖, norm_nonneg v⟩
  let L : NNReal := ⟨‖v‖⁻¹, by positivity⟩
  have hK : (K : ℝ) = ‖v‖ := NNReal.coe_mk _ _
  have hL : (L : ℝ) = ‖v‖⁻¹ := NNReal.coe_mk _ _
  have hlip : LipschitzWith K (liftedStraightLine v) := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    rw [hK]
    simp [liftedStraightLine, dist_eq_norm, ← sub_smul, norm_smul,
      Real.norm_eq_abs, mul_comm]
  have hanti : AntilipschitzWith L (liftedStraightLine v) := by
    refine AntilipschitzWith.of_le_mul_dist fun s t => ?_
    rw [hL]
    have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
    simp [liftedStraightLine, dist_eq_norm, ← sub_smul, norm_smul,
      Real.norm_eq_abs, mul_comm, hvn]
  exact (hanti.isClosedEmbedding hlip.uniformContinuous).isProperMap

/-- Every continuous real observable on a compact observer space is uniformly bounded. -/
theorem continuousReal_bounded_of_compactSpace
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : X → ℝ) (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  have hcompact : IsCompact (Set.range f) := by
    simpa only [Set.image_univ] using isCompact_univ.image hf
  obtain ⟨C, hC⟩ := hcompact.isBounded.subset_closedBall 0
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro x
  have hx := hC ⟨x, rfl⟩
  rw [Metric.mem_closedBall] at hx
  simpa [Real.dist_eq] using hx.trans (le_max_left C 0)

variable {K : Type*} [AddCommGroup K] [TopologicalSpace K]

/-- Projection of the marked line through a continuous additive torus quotient. -/
def projectedStraightLine (q : V →ₜ+ K) (v : V) (t : ℝ) : K := q (t • v)

theorem projectedStraightLine_continuous (q : V →ₜ+ K) (v : V) :
    Continuous (projectedStraightLine q v) := by
  exact q.continuous.comp (continuous_id.smul continuous_const)

theorem projectedStraightLine_add (q : V →ₜ+ K) (v : V) (s t : ℝ) :
    projectedStraightLine q v (s + t) =
      projectedStraightLine q v s + projectedStraightLine q v t := by
  simp [projectedStraightLine, add_smul]

/-- Projected orbit closure is compact. -/
theorem projectedStraightLine_compactClosure [CompactSpace K]
    (q : V →ₜ+ K) (v : V) :
    IsCompact (closure (Set.range (projectedStraightLine q v))) :=
  isClosed_closure.isCompact

/-- Compact projected straight lines return arbitrarily late to every zero neighbourhood. -/
theorem projectedStraightLine_recurrence [IsTopologicalAddGroup K] [CompactSpace K]
    (q : V →ₜ+ K) (v : V) {U : Set K} (hU : U ∈ 𝓝 (0 : K))
    {M : ℝ} (hM : 0 < M) :
    ∃ t : ℝ, M ≤ t ∧ projectedStraightLine q v t ∈ U := by
  let γ : ℝ → Multiplicative K := fun t => Multiplicative.ofAdd (projectedStraightLine q v t)
  have hcont : Continuous γ := projectedStraightLine_continuous q v
  have hhom : ∀ s t, γ (s + t) = γ s * γ t := by
    intro s t
    exact projectedStraightLine_add q v s t
  exact oneParameter_recurrence hcont hhom hU hM

/-- Exact projected period criterion: `T` is a period precisely when `T • v` lies in the deck
lattice, represented intrinsically as the quotient map's kernel. -/
theorem projectedStraightLine_periodic_iff (q : V →ₜ+ K) (v : V) (T t : ℝ) :
    projectedStraightLine q v (t + T) = projectedStraightLine q v t ↔
      T • v ∈ q.toAddMonoidHom.ker := by
  simp [projectedStraightLine, add_smul]

/-- No continuous real endpoint observable on a compact quotient recovers the unbounded marked
lift length. -/
theorem no_continuous_endpoint_observable_recovers_liftedLength [CompactSpace K]
    (q : V →ₜ+ K) (v : V) (hv : v ≠ 0) (f : K → ℝ) (hf : Continuous f) :
    ¬ ∀ t : ℝ, |f (projectedStraightLine q v t)| = ‖liftedStraightLine v t‖ := by
  obtain ⟨C, hC, hfC⟩ := continuousReal_bounded_of_compactSpace f hf
  intro hrecover
  let t : ℝ := (C + 1) / ‖v‖
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have ht : 0 < t := by
    dsimp only [t]
    positivity
  have hlength : ‖liftedStraightLine v t‖ = C + 1 := by
    rw [liftedStraightLine_norm, abs_of_pos ht]
    dsimp only [t]
    field_simp [ne_of_gt hvn]
  have hbound := hfC (projectedStraightLine q v t)
  rw [hrecover t, hlength] at hbound
  linarith

/-- Positive radial energy of a rank-one automorphism with modulus ratio `r`. -/
def polarLineEnergy (r : ℝ) : ℝ := r + r⁻¹ - 2

/-- Exact hyperbolic-sine presentation of rank-one polar energy. -/
theorem polarLineEnergy_eq_four_sinh_sq {r : ℝ} (hr : 0 < r) :
    polarLineEnergy r = 4 * Real.sinh (Real.log r / 2) ^ 2 := by
  let x := Real.log r / 2
  have hx : 0 < Real.exp x := Real.exp_pos _
  have hx2 : Real.exp x ^ 2 = r := by
    rw [pow_two, ← Real.exp_add]
    dsimp only [x]
    convert Real.exp_log hr using 1
    ring_nf
  change polarLineEnergy r = 4 * Real.sinh x ^ 2
  rw [Real.sinh_eq, Real.exp_neg]
  calc
    polarLineEnergy r = Real.exp x ^ 2 + (Real.exp x ^ 2)⁻¹ - 2 := by
      unfold polarLineEnergy
      rw [hx2]
    _ = 4 * ((Real.exp x - (Real.exp x)⁻¹) / 2) ^ 2 := by
      rw [← inv_pow]
      rw [div_pow]
      field_simp [ne_of_gt hx]
      ring_nf

theorem polarLineEnergy_nonneg {r : ℝ} (hr : 0 < r) :
    0 ≤ polarLineEnergy r := by
  rw [polarLineEnergy_eq_four_sinh_sq hr]
  positivity

theorem polarLineEnergy_eq_zero_iff {r : ℝ} (hr : 0 < r) :
    polarLineEnergy r = 0 ↔ r = 1 := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  constructor
  · intro h
    unfold polarLineEnergy at h
    field_simp [hr0] at h
    nlinarith [sq_nonneg (r - 1)]
  · rintro rfl
    norm_num [polarLineEnergy]

/-- Radial energy forgets time orientation. -/
theorem polarLineEnergy_inv (r : ℝ) :
    polarLineEnergy r⁻¹ = polarLineEnergy r := by
  simp [polarLineEnergy]
  ring

/-- Polar energy of an automorphism of a one-dimensional complex Hermitian space. -/
def complexPolarLineEnergy (h : ℂˣ) : ℝ :=
  polarLineEnergy ‖(h : ℂ)‖

theorem complexPolarLineEnergy_nonneg (h : ℂˣ) :
    0 ≤ complexPolarLineEnergy h := by
  exact polarLineEnergy_nonneg (norm_pos_iff.mpr h.ne_zero)

/-- Polar energy vanishes exactly on unitary line automorphisms. -/
theorem complexPolarLineEnergy_eq_zero_iff (h : ℂˣ) :
    complexPolarLineEnergy h = 0 ↔ ‖(h : ℂ)‖ = 1 :=
  polarLineEnergy_eq_zero_iff (norm_pos_iff.mpr h.ne_zero)

/-- Arbitrary unitary phases leave polar energy unchanged. -/
theorem complexPolarLineEnergy_mul_unitary (h u : ℂˣ)
    (hu : ‖(u : ℂ)‖ = 1) :
    complexPolarLineEnergy (u * h) = complexPolarLineEnergy h := by
  simp [complexPolarLineEnergy, hu]

/-- Inversion leaves polar energy unchanged. -/
theorem complexPolarLineEnergy_inv (h : ℂˣ) :
    complexPolarLineEnergy h⁻¹ = complexPolarLineEnergy h := by
  simp [complexPolarLineEnergy, norm_inv, polarLineEnergy_inv]

end

end GaloisForLFunctions.HTGeometry
