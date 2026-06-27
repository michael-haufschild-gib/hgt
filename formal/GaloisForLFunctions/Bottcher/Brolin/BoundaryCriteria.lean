/-
# Böttcher tower — Brolin: boundary criteria and hDisc closures

This module is part of the split Brolin/Riesz-measure interface. Import
`GaloisForLFunctions.Bottcher.Brolin` for the full public surface.
-/
import GaloisForLFunctions.Bottcher.Brolin.SingularTail

open Filter Topology MeasureTheory CompactlySupported Laplacian
open scoped Laplacian

namespace Bottcher

local instance : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- If the constructed boundary potential satisfies the same quadratic scaling
law as the Green function on `K_c`, then the opposite boundary inequality
follows.  Indeed, a positive value would double along a bounded filled-Julia
orbit, contradicting the carrier-only upper bound above. -/
theorem neg_logPotential_gapAMu_nonpos_of_boundary_scaling
    {c z : ℂ} (hzK : z ∈ filledJulia c)
    (hscale :
      ∀ w : ℂ, w ∈ filledJulia c →
        - logPotential (gapAMu c) (quadratic c w) =
          2 * (- logPotential (gapAMu c) w)) :
    - logPotential (gapAMu c) z ≤ 0 := by
  by_contra hle
  have hpos : 0 < - logPotential (gapAMu c) z := lt_of_not_ge hle
  set A : ℕ → ℝ :=
    fun n => - logPotential (gapAMu c) ((quadratic c)^[n] z)
  have hA : ∀ n : ℕ, A n =
      (2 ^ n : ℝ) * (- logPotential (gapAMu c) z) := by
    intro n
    induction n with
    | zero =>
        simp [A]
    | succ n ih =>
        have hnK : (quadratic c)^[n] z ∈ filledJulia c :=
          filledJulia_forward hzK n
        calc
          A (n + 1)
              = - logPotential (gapAMu c)
                  (quadratic c ((quadratic c)^[n] z)) := by
                    simp [A, Function.iterate_succ_apply']
          _ = 2 *
                (- logPotential (gapAMu c) ((quadratic c)^[n] z)) := by
                    exact hscale ((quadratic c)^[n] z) hnK
          _ = 2 * A n := by simp [A]
          _ = 2 * ((2 ^ n : ℝ) * (- logPotential (gapAMu c) z)) := by
                    rw [ih]
          _ = (2 ^ (n + 1) : ℝ) * (- logPotential (gapAMu c) z) := by
                    rw [pow_succ]
                    ring
  let B : ℝ := Real.log (2 * max 2 ‖c‖)
  have htend :
      Tendsto
        (fun n : ℕ => (2 ^ n : ℝ) * (- logPotential (gapAMu c) z))
        atTop atTop :=
    by
      simpa [mul_comm] using
        (tendsto_pow_atTop_atTop_of_one_lt
          (by norm_num : (1 : ℝ) < 2)).const_mul_atTop hpos
  rcases (eventually_atTop.1 (htend.eventually_gt_atTop B)) with ⟨N, hN⟩
  have hNK : (quadratic c)^[N] z ∈ filledJulia c := filledJulia_forward hzK N
  have hbound :
      A N ≤ B := by
    simpa [A, B] using
      neg_logPotential_gapAMu_upper_bound_of_mem_filledJulia
        (c := c) (z := (quadratic c)^[N] z) hNK
  have hgt : B < A N := by
    simpa [hA N] using hN N le_rfl
  exact not_lt_of_ge hbound hgt

/-- Disconnected-lane wrapper for the boundary-scaling contradiction.  The
pointwise doubling argument itself is carrier-only; the disconnected input is
kept here for the existing hDisc API. -/
theorem neg_logPotential_gapAMu_nonpos_of_boundary_scaling_of_mem_filledJulia
    {c z : ℂ} (_hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hscale :
      ∀ w : ℂ, w ∈ filledJulia c →
        - logPotential (gapAMu c) (quadratic c w) =
          2 * (- logPotential (gapAMu c) w)) :
    - logPotential (gapAMu c) z ≤ 0 :=
  neg_logPotential_gapAMu_nonpos_of_boundary_scaling hzK hscale

/-- The same scaling law closes the existing GAP-A representation criterion for
the constructed limiting/Riesz measure. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_boundary_scaling
    {c : ℂ} (hc : Disconnected c)
    (hscale :
      ∀ z : ℂ, z ∈ filledJulia c →
        - logPotential (gapAMu c) (quadratic c z) =
          2 * (- logPotential (gapAMu c) z)) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  rw [gapAMu_hasGreenPotentialRepresentation_iff_boundary_nonpos_of_disconnected hc]
  intro z hzK
  exact neg_logPotential_gapAMu_nonpos_of_boundary_scaling
    (c := c) (z := z) hzK hscale

/-- The collapsed shifted pushforward identity supplies the boundary scaling
needed for hDisc once the shifted boundary potential is identified with the
constructed GAP-A potential on `K_c`. -/
theorem gapAMu_boundary_scaling_of_shiftedPotential_eq
    {c : ℂ} (hc : Disconnected c)
    (hpot :
      ∀ z : ℂ, z ∈ filledJulia c →
        logPotential (shiftedLimitingBrolinMeasure c) z =
          logPotential (gapAMu c) z) :
    ∀ z : ℂ, z ∈ filledJulia c →
      - logPotential (gapAMu c) (quadratic c z) =
        2 * (- logPotential (gapAMu c) z) := by
  intro z hzK
  have h :=
    neg_logPotential_gapAMu_quadratic_eq_two_neg_shiftedPotential_unconditional
      (c := c) (z := z) hc hzK
  rw [hpot z hzK] at h
  exact h

/-- hDisc closure through the shifted potential identification: it replaces the
raw boundary-scaling hypothesis by the concrete remaining shifted/GAP-A
potential comparison on the filled Julia set. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_shiftedPotential_eq
    {c : ℂ} (hc : Disconnected c)
    (hpot :
      ∀ z : ℂ, z ∈ filledJulia c →
        logPotential (shiftedLimitingBrolinMeasure c) z =
          logPotential (gapAMu c) z) :
    HasGreenPotentialRepresentation c (gapAMu c) :=
  gapAMu_hasGreenPotentialRepresentation_of_boundary_scaling hc
    (gapAMu_boundary_scaling_of_shiftedPotential_eq hc hpot)

/-- If the shifted cluster is the constructed GAP-A measure, the unconditional
quadratic potential identity gives the boundary scaling law directly. -/
theorem gapAMu_boundary_scaling_of_shiftedLimitingBrolinMeasure_eq
    {c : ℂ} (hc : Disconnected c)
    (hν : shiftedLimitingBrolinMeasure c = gapAMu c) :
    ∀ z : ℂ, z ∈ filledJulia c →
      - logPotential (gapAMu c) (quadratic c z) =
        2 * (- logPotential (gapAMu c) z) := by
  intro z hzK
  have h :=
    neg_logPotential_gapAMu_quadratic_eq_two_neg_shiftedPotential_unconditional
      (c := c) (z := z) hc hzK
  rwa [hν] at h

/-- hDisc closure from uniqueness of the shifted cluster.  Once the shifted
compactness limit is identified with `μ_c`, the boundary scaling law follows
and the bounded-orbit doubling argument proves the Green-potential
representation. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_shiftedLimitingBrolinMeasure_eq
    {c : ℂ} (hc : Disconnected c)
    (hν : shiftedLimitingBrolinMeasure c = gapAMu c) :
    HasGreenPotentialRepresentation c (gapAMu c) :=
  gapAMu_hasGreenPotentialRepresentation_of_boundary_scaling hc
    (gapAMu_boundary_scaling_of_shiftedLimitingBrolinMeasure_eq hc hν)

/-- The shifted boundary-zero statement alone closes the GAP-A potential
representation: every boundary point has a filled-Julia preimage, and the
collapsed shifted pushforward identity gives zero potential at its image. -/
theorem gapAMu_boundary_zero_of_shiftedBoundary_zero
    {c : ℂ} (hc : Disconnected c)
    (hshift :
      ∀ z : ℂ, z ∈ filledJulia c →
        - logPotential (shiftedLimitingBrolinMeasure c) z = 0) :
    ∀ y : ℂ, y ∈ filledJulia c →
      - logPotential (gapAMu c) y = 0 := by
  intro y hy
  rcases exists_mem_filledJulia_quadratic_eq (c := c) (y := y) hy with
    ⟨z, hzK, hzy⟩
  have hscale :=
    neg_logPotential_gapAMu_quadratic_eq_two_neg_shiftedPotential_unconditional
      (c := c) (z := z) hc hzK
  rw [hzy, hshift z hzK] at hscale
  simpa using hscale

/-- hDisc closure through shifted boundary-zero.  This is the direct form of
the remaining boundary task for the shifted limiting cluster. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_shiftedBoundary_zero
    {c : ℂ} (hc : Disconnected c)
    (hshift :
      ∀ z : ℂ, z ∈ filledJulia c →
        - logPotential (shiftedLimitingBrolinMeasure c) z = 0) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  rw [gapAMu_hasGreenPotentialRepresentation_iff_boundary_zero]
  exact gapAMu_boundary_zero_of_shiftedBoundary_zero hc hshift

/-- Conversely, if the constructed GAP-A measure has the Green-potential
representation, then the shifted boundary potential is zero.  The unconditional
quadratic identity transfers boundary-zero at `f_c z` back to the shifted
preimage branch at `z`. -/
theorem shiftedBoundary_zero_of_gapAMu_hasGreenPotentialRepresentation
    {c : ℂ} (hc : Disconnected c)
    (hrep : HasGreenPotentialRepresentation c (gapAMu c)) :
    ∀ z : ℂ, z ∈ filledJulia c →
      - logPotential (shiftedLimitingBrolinMeasure c) z = 0 := by
  have hgapzero :
      ∀ y : ℂ, y ∈ filledJulia c →
        - logPotential (gapAMu c) y = 0 :=
    (gapAMu_hasGreenPotentialRepresentation_iff_boundary_zero c).mp hrep
  intro z hzK
  have hfzK : quadratic c z ∈ filledJulia c :=
    (mem_filledJulia_iff_quadratic_mem c z).mp hzK
  have hscale :=
    neg_logPotential_gapAMu_quadratic_eq_two_neg_shiftedPotential_unconditional
      (c := c) (z := z) hc hzK
  rw [hgapzero (quadratic c z) hfzK] at hscale
  linarith

/-- For disconnected parameters, shifted boundary-zero is exactly equivalent
to the GAP-A Green-potential representation for the constructed measure. -/
theorem gapAMu_hasGreenPotentialRepresentation_iff_shiftedBoundary_zero
    {c : ℂ} (hc : Disconnected c) :
    HasGreenPotentialRepresentation c (gapAMu c) ↔
      ∀ z : ℂ, z ∈ filledJulia c →
        - logPotential (shiftedLimitingBrolinMeasure c) z = 0 := by
  constructor
  · exact shiftedBoundary_zero_of_gapAMu_hasGreenPotentialRepresentation hc
  · exact gapAMu_hasGreenPotentialRepresentation_of_shiftedBoundary_zero hc

/-- At a point where the shifted singular kernel is not integrable, the
project's real-valued `logPotential` convention makes the shifted boundary
value vanish immediately.  Thus the remaining hDisc boundary problem is the
finite-integral case. -/
theorem shiftedBoundary_zero_of_not_integrable
    {c z : ℂ}
    (hnot :
      ¬ Integrable (fun w => logKernel z w)
        (shiftedLimitingBrolinMeasure c)) :
    - logPotential (shiftedLimitingBrolinMeasure c) z = 0 := by
  have hzero : logPotential (shiftedLimitingBrolinMeasure c) z = 0 := by
    unfold logPotential
    exact integral_undef hnot
  rw [hzero, neg_zero]

/-- If every shifted boundary kernel on `K_c` is nonintegrable, then hDisc
closes through shifted boundary-zero.  This isolates the genuinely hard
remaining case to finite boundary kernels. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_shiftedBoundary_not_integrable
    {c : ℂ} (hc : Disconnected c)
    (hnot :
      ∀ z : ℂ, z ∈ filledJulia c →
        ¬ Integrable (fun w => logKernel z w)
          (shiftedLimitingBrolinMeasure c)) :
    HasGreenPotentialRepresentation c (gapAMu c) :=
  gapAMu_hasGreenPotentialRepresentation_of_shiftedBoundary_zero hc
    (fun z hzK => shiftedBoundary_zero_of_not_integrable (hnot z hzK))

/-- Exact finite-kernel form of the remaining hDisc boundary problem.  The
nonintegrable boundary kernels already give shifted boundary-zero by convention;
therefore the GAP-A Green-potential representation is equivalent to proving
`U_ν(z) ≥ 0` only at the boundary points where the shifted kernel is integrable.
-/
theorem gapAMu_hasGreenPotentialRepresentation_iff_shiftedBoundary_integrable_nonnegative
    {c : ℂ} (hc : Disconnected c) :
    HasGreenPotentialRepresentation c (gapAMu c) ↔
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w)
          (shiftedLimitingBrolinMeasure c) →
        0 ≤ logPotential (shiftedLimitingBrolinMeasure c) z := by
  constructor
  · intro hrep z hzK _hint
    have hzero :=
      shiftedBoundary_zero_of_gapAMu_hasGreenPotentialRepresentation
        (c := c) hc hrep z hzK
    have hUzero :
        logPotential (shiftedLimitingBrolinMeasure c) z = 0 := by
      linarith
    rw [hUzero]
  · intro hnonneg
    apply gapAMu_hasGreenPotentialRepresentation_of_shiftedBoundary_zero hc
    intro z hzK
    by_cases hint :
      Integrable (fun w => logKernel z w)
        (shiftedLimitingBrolinMeasure c)
    · have hle :
          logPotential (shiftedLimitingBrolinMeasure c) z ≤ 0 :=
        logPotential_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
          (c := c) (z := z) hc hzK
      have hge :
          0 ≤ logPotential (shiftedLimitingBrolinMeasure c) z :=
        hnonneg z hzK hint
      have hzero :
          logPotential (shiftedLimitingBrolinMeasure c) z = 0 :=
        le_antisymm hle hge
      rw [hzero, neg_zero]
    · exact shiftedBoundary_zero_of_not_integrable hint

/-- Finite shifted-boundary kernels can be tested by the shrinking truncated
potentials.  Thus the hDisc boundary value problem is exactly the assertion
that the singular tail left after truncation disappears at each finite shifted
boundary kernel. -/
theorem shiftedBoundary_integrable_nonnegative_iff_truncation_zero
    {c : ℂ} (hc : Disconnected c) :
    (∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w)
          (shiftedLimitingBrolinMeasure c) →
        0 ≤ logPotential (shiftedLimitingBrolinMeasure c) z) ↔
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w)
          (shiftedLimitingBrolinMeasure c) →
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂shiftedLimitingBrolinMeasure c)
          atTop (𝓝 0) := by
  constructor
  · intro hnonneg z hzK hint
    have hlim :=
      integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_inv_nat_tendsto_logPotential_of_integrable
        (c := c) (z := z) hc hzK hint
    have hle :
        logPotential (shiftedLimitingBrolinMeasure c) z ≤ 0 :=
      logPotential_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hzK
    have hge :
        0 ≤ logPotential (shiftedLimitingBrolinMeasure c) z :=
      hnonneg z hzK hint
    have hzero :
        logPotential (shiftedLimitingBrolinMeasure c) z = 0 :=
      le_antisymm hle hge
    simpa [hzero] using hlim
  · intro hzero z hzK hint
    have hlim :=
      integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_inv_nat_tendsto_logPotential_of_integrable
        (c := c) (z := z) hc hzK hint
    have h0eq :
        (0 : ℝ) = logPotential (shiftedLimitingBrolinMeasure c) z :=
      tendsto_nhds_unique (hzero z hzK hint) hlim
    rw [← h0eq]

/-- hDisc, in shifted form, is equivalent to vanishing of every finite
shrinking-truncation boundary potential for the shifted limiting measure. -/
theorem gapAMu_hasGreenPotentialRepresentation_iff_shiftedBoundary_truncation_zero
    {c : ℂ} (hc : Disconnected c) :
    HasGreenPotentialRepresentation c (gapAMu c) ↔
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w)
          (shiftedLimitingBrolinMeasure c) →
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂shiftedLimitingBrolinMeasure c)
          atTop (𝓝 0) := by
  rw [gapAMu_hasGreenPotentialRepresentation_iff_shiftedBoundary_integrable_nonnegative hc,
    shiftedBoundary_integrable_nonnegative_iff_truncation_zero hc]

/-- Canonical boundary truncation-zero at the image point `f_c z` forces the
shifted boundary truncation-zero at `z`.  This is the local Riesz/pushforward
bridge from the constructed measure `μ_c` back to the shifted compactness
limit. -/
theorem shiftedBoundary_truncation_zero_of_gapAMu_boundary_truncation_zero_quadratic
    {c z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hμzero :
      ∀ y : ℂ, y ∈ filledJulia c →
        Integrable (fun w => logKernel y w) (gapAMu c) →
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel y (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
          atTop (𝓝 0))
    (hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c)) :
    Tendsto
      (fun n : ℕ =>
        ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
          ∂shiftedLimitingBrolinMeasure c)
      atTop (𝓝 0) := by
  have hfzK : quadratic c z ∈ filledJulia c :=
    (mem_filledJulia_iff_quadratic_mem c z).mp hzK
  have hμint :
      Integrable (fun y => logKernel (quadratic c z) y) (gapAMu c) :=
    integrable_logKernel_gapAMu_quadratic_of_shifted
      (c := c) (z := z) hc hzK hzint
  have hμlim :=
    integral_truncatedLogKernel_gapAMu_inv_nat_tendsto_logPotential_of_integrable
      (c := c) (z := quadratic c z) hc hfzK hμint
  have hμlimZero := hμzero (quadratic c z) hfzK hμint
  have hμeq0 :
      logPotential (gapAMu c) (quadratic c z) = 0 :=
    tendsto_nhds_unique hμlim hμlimZero
  have hpush :
      logPotential (gapAMu c) (quadratic c z) =
        2 * logPotential (shiftedLimitingBrolinMeasure c) z :=
    logPotential_gapAMu_quadratic_eq_two_shiftedPotential
      (c := c) (z := z) hc hzK hzint
  have hνeq0 :
      logPotential (shiftedLimitingBrolinMeasure c) z = 0 := by
    nlinarith
  have hνlim :=
    integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_inv_nat_tendsto_logPotential_of_integrable
      (c := c) (z := z) hc hzK hzint
  simpa [hνeq0] using hνlim

/-- Global form of the canonical-to-shifted truncation transfer. -/
theorem shiftedBoundary_truncation_zero_of_gapAMu_boundary_truncation_zero
    {c : ℂ} (hc : Disconnected c)
    (hμzero :
      ∀ y : ℂ, y ∈ filledJulia c →
        Integrable (fun w => logKernel y w) (gapAMu c) →
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel y (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
          atTop (𝓝 0)) :
    ∀ z : ℂ, z ∈ filledJulia c →
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c) →
      Tendsto
        (fun n : ℕ =>
          ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
            ∂shiftedLimitingBrolinMeasure c)
        atTop (𝓝 0) := by
  intro z hzK hzint
  exact shiftedBoundary_truncation_zero_of_gapAMu_boundary_truncation_zero_quadratic
    (c := c) (z := z) hc hzK hμzero hzint

/-- Shifted boundary truncation-zero at a filled-Julia preimage forces
canonical boundary truncation-zero at the target.  This is the reverse local
Riesz/pushforward bridge. -/
theorem gapAMu_boundary_truncation_zero_of_shiftedBoundary_truncation_zero_quadratic_preimage
    {c y z : ℂ} (hc : Disconnected c) (hzK : z ∈ filledJulia c)
    (hzy : quadratic c z = y)
    (hνzero :
      ∀ x : ℂ, x ∈ filledJulia c →
        Integrable (fun w => logKernel x w)
          (shiftedLimitingBrolinMeasure c) →
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel x (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂shiftedLimitingBrolinMeasure c)
          atTop (𝓝 0))
    (hμint : Integrable (fun w => logKernel y w) (gapAMu c)) :
    Tendsto
      (fun n : ℕ =>
        ∫ w, truncatedLogKernel y (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
      atTop (𝓝 0) := by
  have hfzK : quadratic c z ∈ filledJulia c :=
    (mem_filledJulia_iff_quadratic_mem c z).mp hzK
  have hμint_fz :
      Integrable (fun w => logKernel (quadratic c z) w) (gapAMu c) := by
    rw [hzy]
    exact hμint
  have hzint :
      Integrable (fun w => logKernel z w) (shiftedLimitingBrolinMeasure c) :=
    integrable_logKernel_shiftedLimitingBrolinMeasure_of_gapAMu_quadratic
      (c := c) (z := z) hc hzK hμint_fz
  have hνlim :=
    integral_truncatedLogKernel_shiftedLimitingBrolinMeasure_inv_nat_tendsto_logPotential_of_integrable
      (c := c) (z := z) hc hzK hzint
  have hνlimZero := hνzero z hzK hzint
  have hνeq0 :
      logPotential (shiftedLimitingBrolinMeasure c) z = 0 :=
    tendsto_nhds_unique hνlim hνlimZero
  have hpush :
      logPotential (gapAMu c) (quadratic c z) =
        2 * logPotential (shiftedLimitingBrolinMeasure c) z :=
    logPotential_gapAMu_quadratic_eq_two_shiftedPotential
      (c := c) (z := z) hc hzK hzint
  have hμeq0_fz :
      logPotential (gapAMu c) (quadratic c z) = 0 := by
    nlinarith
  have hμlim_fz :=
    integral_truncatedLogKernel_gapAMu_inv_nat_tendsto_logPotential_of_integrable
      (c := c) (z := quadratic c z) hc hfzK hμint_fz
  have hμlim_y :
      Tendsto
        (fun n : ℕ =>
          ∫ w, truncatedLogKernel y (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
        atTop (𝓝 (logPotential (gapAMu c) y)) := by
    simpa [← hzy] using hμlim_fz
  have hμeq0_y : logPotential (gapAMu c) y = 0 := by
    simpa [← hzy] using hμeq0_fz
  simpa [hμeq0_y] using hμlim_y

/-- Global shifted-to-canonical truncation transfer, using a filled-Julia
preimage of each target boundary point. -/
theorem gapAMu_boundary_truncation_zero_of_shiftedBoundary_truncation_zero
    {c : ℂ} (hc : Disconnected c)
    (hνzero :
      ∀ x : ℂ, x ∈ filledJulia c →
        Integrable (fun w => logKernel x w)
          (shiftedLimitingBrolinMeasure c) →
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel x (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂shiftedLimitingBrolinMeasure c)
          atTop (𝓝 0)) :
    ∀ y : ℂ, y ∈ filledJulia c →
      Integrable (fun w => logKernel y w) (gapAMu c) →
      Tendsto
        (fun n : ℕ =>
          ∫ w, truncatedLogKernel y (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
        atTop (𝓝 0) := by
  intro y hyK hμint
  rcases exists_mem_filledJulia_quadratic_eq (c := c) (y := y) hyK with
    ⟨z, hzK, hzy⟩
  exact
    gapAMu_boundary_truncation_zero_of_shiftedBoundary_truncation_zero_quadratic_preimage
      (c := c) (y := y) (z := z) hc hzK hzy hνzero hμint

/-- The canonical and shifted finite-kernel truncation-zero formulations are
equivalent.  This is the exact boundary passage supplied by the constructed
Riesz measure and its shifted pullback limit. -/
theorem gapAMu_boundary_truncation_zero_iff_shiftedBoundary_truncation_zero
    {c : ℂ} (hc : Disconnected c) :
    (∀ y : ℂ, y ∈ filledJulia c →
        Integrable (fun w => logKernel y w) (gapAMu c) →
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel y (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
          atTop (𝓝 0)) ↔
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w)
          (shiftedLimitingBrolinMeasure c) →
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂shiftedLimitingBrolinMeasure c)
          atTop (𝓝 0) := by
  constructor
  · exact shiftedBoundary_truncation_zero_of_gapAMu_boundary_truncation_zero hc
  · exact gapAMu_boundary_truncation_zero_of_shiftedBoundary_truncation_zero hc

/-- Expanded `G_c = -U^{μ_c}` form of the GAP-A boundary truncation criterion.
The limiting/Riesz measure `μ_c = gapAMu c` already gives the exterior
potential; the full global representation is equivalent to the finite-kernel
shrinking-truncation limit on `K_c`. -/
theorem gapAMu_green_eq_neg_logPotential_iff_boundary_truncation_zero
    {c : ℂ} (hc : Disconnected c) :
    (∀ z : ℂ, greenFunctionDyn c z = - logPotential (gapAMu c) z) ↔
      ∀ y : ℂ, y ∈ filledJulia c →
        Integrable (fun w => logKernel y w) (gapAMu c) →
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel y (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
          atTop (𝓝 0) := by
  rw [← hasGreenPotentialRepresentation_iff c (gapAMu c),
    gapAMu_hasGreenPotentialRepresentation_iff_boundary_truncation_zero hc]

/-- Expanded `G_c = -U^{μ_c}` form of the shifted finite-kernel truncation
criterion.  This is the same target as the canonical theorem, transported
through the shifted limiting measure and the quadratic pushforward. -/
theorem gapAMu_green_eq_neg_logPotential_iff_shiftedBoundary_truncation_zero
    {c : ℂ} (hc : Disconnected c) :
    (∀ z : ℂ, greenFunctionDyn c z = - logPotential (gapAMu c) z) ↔
      ∀ z : ℂ, z ∈ filledJulia c →
        Integrable (fun w => logKernel z w)
          (shiftedLimitingBrolinMeasure c) →
        Tendsto
          (fun n : ℕ =>
            ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
              ∂shiftedLimitingBrolinMeasure c)
          atTop (𝓝 0) := by
  rw [← hasGreenPotentialRepresentation_iff c (gapAMu c),
    gapAMu_hasGreenPotentialRepresentation_iff_shiftedBoundary_truncation_zero hc]

/-- GAP-A hDisc Riesz criterion core.  This packages the constructed
limiting/Riesz measure `μ_c = gapAMu c`, the already-proved exterior potential
identity, and the exact finite-kernel truncation condition equivalent to the
full global identity `G_c = -U^{μ_c}`. -/
theorem gapAMu_hDiscLimitingRieszCriterionCore {c : ℂ} (hc : Disconnected c) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (gapAMu c) ∧
      HasSubseqLogPotentialLimit c (gapAMu c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z) ∧
      ((∀ z : ℂ, greenFunctionDyn c z = - logPotential (gapAMu c) z) ↔
        ∀ y : ℂ, y ∈ filledJulia c →
          Integrable (fun w => logKernel y w) (gapAMu c) →
          Tendsto
            (fun n : ℕ =>
              ∫ w, truncatedLogKernel y (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
            atTop (𝓝 0)) ∧
      ((∀ y : ℂ, y ∈ filledJulia c →
          Integrable (fun w => logKernel y w) (gapAMu c) →
          Tendsto
            (fun n : ℕ =>
              ∫ w, truncatedLogKernel y (((n + 1 : ℕ) : ℝ)⁻¹) w ∂gapAMu c)
            atTop (𝓝 0)) ↔
        ∀ z : ℂ, z ∈ filledJulia c →
          Integrable (fun w => logKernel z w)
            (shiftedLimitingBrolinMeasure c) →
          Tendsto
            (fun n : ℕ =>
              ∫ w, truncatedLogKernel z (((n + 1 : ℕ) : ℝ)⁻¹) w
                ∂shiftedLimitingBrolinMeasure c)
            atTop (𝓝 0)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · exact gapAMu_isProbOn_filledJulia c
  · exact gapAMu_isWeakSubseqLimitOfPreBrolin c
  · exact gapAMu_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz
  · exact gapAMu_green_eq_neg_logPotential_iff_boundary_truncation_zero hc
  · exact gapAMu_boundary_truncation_zero_iff_shiftedBoundary_truncation_zero hc

/-- The already-proved shifted upper-potential bound turns the remaining
opposite signed boundary inequality into shifted boundary-zero. -/
theorem shiftedBoundary_zero_of_nonpos
    {c : ℂ} (hc : Disconnected c)
    (hshiftNonpos :
      ∀ z : ℂ, z ∈ filledJulia c →
        - logPotential (shiftedLimitingBrolinMeasure c) z ≤ 0) :
    ∀ z : ℂ, z ∈ filledJulia c →
      - logPotential (shiftedLimitingBrolinMeasure c) z = 0 := by
  intro z hzK
  exact le_antisymm (hshiftNonpos z hzK)
    (neg_nonneg.mpr
      (logPotential_shiftedLimitingBrolinMeasure_nonpos_of_mem_filledJulia_of_disconnected
        (c := c) (z := z) hc hzK))

/-- hDisc closure from the remaining shifted boundary inequality.  The shifted
measure already has the nonpositive logarithmic potential on `K_c`; proving the
opposite signed inequality for it supplies the GAP-A potential representation. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_shiftedBoundary_nonpos
    {c : ℂ} (hc : Disconnected c)
    (hshiftNonpos :
      ∀ z : ℂ, z ∈ filledJulia c →
        - logPotential (shiftedLimitingBrolinMeasure c) z ≤ 0) :
    HasGreenPotentialRepresentation c (gapAMu c) :=
  gapAMu_hasGreenPotentialRepresentation_of_shiftedBoundary_zero hc
    (shiftedBoundary_zero_of_nonpos hc hshiftNonpos)

/-- The remaining shifted signed inequality is equivalent to the disconnected
GAP-A Green-potential representation: one direction is the closure theorem
above, and the converse follows from shifted boundary-zero forced by the
representation. -/
theorem gapAMu_hasGreenPotentialRepresentation_iff_shiftedBoundary_nonpos
    {c : ℂ} (hc : Disconnected c) :
    HasGreenPotentialRepresentation c (gapAMu c) ↔
      ∀ z : ℂ, z ∈ filledJulia c →
        - logPotential (shiftedLimitingBrolinMeasure c) z ≤ 0 := by
  constructor
  · intro hrep z hzK
    rw [shiftedBoundary_zero_of_gapAMu_hasGreenPotentialRepresentation
      (c := c) hc hrep z hzK]
  · exact gapAMu_hasGreenPotentialRepresentation_of_shiftedBoundary_nonpos hc

/-- A point outside the interior of `K_c` is approached by basin points. -/
theorem mem_closure_filledJulia_compl_of_not_mem_interior
    {c z : ℂ} (hzint : z ∉ interior (filledJulia c)) :
    z ∈ closure (filledJulia c)ᶜ := by
  rwa [closure_compl]

/-- Canonical boundary upper-semicontinuity bridge for the constructed measure
`μ_c`.  If every filled-Julia point is approached by basin points, and the
canonical logarithmic potential is upper semicontinuous there, then the missing
boundary inequality `0 ≤ U^{μ_c}` follows from the already-proved exterior
identity `U^{μ_c} = -G_c` on the basin and continuity of `G_c` at the boundary.
-/
theorem gapAMu_boundary_nonnegative_of_upperSemicontinuousAt_of_basin_closure
    {c : ℂ}
    (hcl :
      ∀ z : ℂ, z ∈ filledJulia c → z ∈ closure (filledJulia c)ᶜ)
    (husc :
      ∀ z : ℂ, z ∈ filledJulia c → ∀ a : ℝ,
        logPotential (gapAMu c) z < a →
          ∀ᶠ y in 𝓝 z, logPotential (gapAMu c) y < a) :
    ∀ z : ℂ, z ∈ filledJulia c →
      0 ≤ logPotential (gapAMu c) z := by
  intro z hzK
  by_contra hnot
  have hUzneg : logPotential (gapAMu c) z < 0 := lt_of_not_ge hnot
  let a : ℝ := logPotential (gapAMu c) z / 2
  have haU : logPotential (gapAMu c) z < a := by
    dsimp [a]
    linarith
  have haneg : a < 0 := by
    dsimp [a]
    linarith
  have hUnhds : {y : ℂ | logPotential (gapAMu c) y < a} ∈ 𝓝 z :=
    husc z hzK a haU
  have hGnhds : {y : ℂ | greenFunctionDyn c y < -a} ∈ 𝓝 z := by
    exact (tendsto_greenFunctionDyn_boundary hzK).eventually
      (Iio_mem_nhds (by linarith))
  have hne : NeBot (𝓝[(filledJulia c)ᶜ] z) :=
    mem_closure_iff_nhdsWithin_neBot.mp (hcl z hzK)
  have hboth :
      ({y : ℂ | logPotential (gapAMu c) y < a} ∩
          {y : ℂ | greenFunctionDyn c y < -a} ∩
          (filledJulia c)ᶜ) ∈ 𝓝[(filledJulia c)ᶜ] z := by
    exact inter_mem
      (inter_mem (nhdsWithin_le_nhds hUnhds) (nhdsWithin_le_nhds hGnhds))
      self_mem_nhdsWithin
  obtain ⟨y, ⟨⟨hyU, hyG⟩, hyK⟩⟩ := hne.nonempty_of_mem hboth
  have hUy : logPotential (gapAMu c) y = - greenFunctionDyn c y := by
    have h := green_eq_neg_logPotential_gapAMu_on_basin (c := c) (z := y) hyK
    linarith
  have hyU' : - greenFunctionDyn c y < a := by
    simpa [hUy] using hyU
  have hyG' : greenFunctionDyn c y < -a := by
    simpa using hyG
  linarith

/-- Empty interior supplies the basin-closure input in the canonical
upper-semicontinuity route. -/
theorem gapAMu_boundary_nonnegative_of_upperSemicontinuousAt_of_empty_interior
    {c : ℂ}
    (hempty : interior (filledJulia c) = ∅)
    (husc :
      ∀ z : ℂ, z ∈ filledJulia c → ∀ a : ℝ,
        logPotential (gapAMu c) z < a →
          ∀ᶠ y in 𝓝 z, logPotential (gapAMu c) y < a) :
    ∀ z : ℂ, z ∈ filledJulia c →
      0 ≤ logPotential (gapAMu c) z := by
  exact gapAMu_boundary_nonnegative_of_upperSemicontinuousAt_of_basin_closure
    (fun z _hzK => by
      apply mem_closure_filledJulia_compl_of_not_mem_interior
      rw [hempty]
      simp)
    husc

/-- hDisc closure from the canonical potential-theoretic boundary route with
the topology supplied directly as basin-closure of `K_c`. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_upperSemicontinuousAt_basin_closure
    {c : ℂ} (hc : Disconnected c)
    (hcl :
      ∀ z : ℂ, z ∈ filledJulia c → z ∈ closure (filledJulia c)ᶜ)
    (husc :
      ∀ z : ℂ, z ∈ filledJulia c → ∀ a : ℝ,
        logPotential (gapAMu c) z < a →
          ∀ᶠ y in 𝓝 z, logPotential (gapAMu c) y < a) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  rw [gapAMu_hasGreenPotentialRepresentation_iff_boundary_integrable_nonnegative hc]
  intro z hzK _hint
  exact gapAMu_boundary_nonnegative_of_upperSemicontinuousAt_of_basin_closure
    hcl husc z hzK

/-- hDisc closure from the canonical potential-theoretic boundary route:
empty interior of `K_c` plus upper semicontinuity of the constructed
logarithmic potential on `K_c` gives the full identity `G_c = -U^{μ_c}`. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_upperSemicontinuousAt_empty_interior
    {c : ℂ} (hc : Disconnected c)
    (hempty : interior (filledJulia c) = ∅)
    (husc :
      ∀ z : ℂ, z ∈ filledJulia c → ∀ a : ℝ,
        logPotential (gapAMu c) z < a →
          ∀ᶠ y in 𝓝 z, logPotential (gapAMu c) y < a) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  exact gapAMu_hasGreenPotentialRepresentation_of_upperSemicontinuousAt_basin_closure
    hc
    (fun z _hzK => by
      apply mem_closure_filledJulia_compl_of_not_mem_interior
      rw [hempty]
      simp)
    husc

/-- Boundary lower-semicontinuity bridge for the shifted potential.  If every
filled-Julia point is approached by basin points, and `-U_ν` is lower
semicontinuous at those points, then the remaining signed hDisc boundary
inequality follows. -/
theorem shiftedBoundary_nonpos_of_lowerSemicontinuousAt_of_basin_closure
    {c : ℂ}
    (hcl :
      ∀ z : ℂ, z ∈ filledJulia c → z ∈ closure (filledJulia c)ᶜ)
    (hlsc :
      ∀ z : ℂ, z ∈ filledJulia c → ∀ a : ℝ,
        a < - logPotential (shiftedLimitingBrolinMeasure c) z →
          ∀ᶠ y in 𝓝 z,
            a < - logPotential (shiftedLimitingBrolinMeasure c) y) :
    ∀ z : ℂ, z ∈ filledJulia c →
      - logPotential (shiftedLimitingBrolinMeasure c) z ≤ 0 := by
  intro z hzK
  by_contra hnot
  let F : ℂ → ℝ :=
    fun y => - logPotential (shiftedLimitingBrolinMeasure c) y
  have hFpos : 0 < F z := lt_of_not_ge hnot
  let a : ℝ := F z / 2
  have hapos : 0 < a := by
    dsimp [a]
    linarith
  have haF : a < F z := by
    dsimp [a]
    linarith
  have hFnhds : {y : ℂ | a < F y} ∈ 𝓝 z := by
    dsimp [F] at haF ⊢
    exact hlsc z hzK a haF
  have hGnhds : {y : ℂ | greenFunctionDyn c y < a} ∈ 𝓝 z := by
    exact (tendsto_greenFunctionDyn_boundary hzK).eventually
      (Iio_mem_nhds hapos)
  have hne : NeBot (𝓝[(filledJulia c)ᶜ] z) :=
    mem_closure_iff_nhdsWithin_neBot.mp (hcl z hzK)
  have hboth :
      ({y : ℂ | a < F y} ∩ {y : ℂ | greenFunctionDyn c y < a} ∩
          (filledJulia c)ᶜ) ∈ 𝓝[(filledJulia c)ᶜ] z := by
    exact inter_mem
      (inter_mem (nhdsWithin_le_nhds hFnhds) (nhdsWithin_le_nhds hGnhds))
      self_mem_nhdsWithin
  obtain ⟨y, ⟨⟨hyF, hyG⟩, hyK⟩⟩ := hne.nonempty_of_mem hboth
  have hFy : F y = greenFunctionDyn c y := by
    dsimp [F]
    exact (green_eq_neg_logPotential_shiftedLimitingBrolinMeasure_on_basin hyK).symm
  have hyF' : a < F y := hyF
  have hyG' : greenFunctionDyn c y < a := hyG
  rw [hFy] at hyF'
  exact (not_lt_of_ge (le_of_lt hyG') hyF')

/-- Empty interior of the filled Julia set supplies the basin-closure input in
the lower-semicontinuity bridge. -/
theorem shiftedBoundary_nonpos_of_lowerSemicontinuousAt_of_empty_interior
    {c : ℂ}
    (hempty : interior (filledJulia c) = ∅)
    (hlsc :
      ∀ z : ℂ, z ∈ filledJulia c → ∀ a : ℝ,
        a < - logPotential (shiftedLimitingBrolinMeasure c) z →
          ∀ᶠ y in 𝓝 z,
            a < - logPotential (shiftedLimitingBrolinMeasure c) y) :
    ∀ z : ℂ, z ∈ filledJulia c →
      - logPotential (shiftedLimitingBrolinMeasure c) z ≤ 0 := by
  exact shiftedBoundary_nonpos_of_lowerSemicontinuousAt_of_basin_closure
    (fun z _hzK => by
      apply mem_closure_filledJulia_compl_of_not_mem_interior
      rw [hempty]
      simp)
    hlsc

/-- hDisc closure from the two analytic/topological facts that remain in the
lower-semicontinuity route: disconnected `K_c` has empty interior, and the
shifted negative potential is lower semicontinuous on `K_c`. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_shifted_lsc_empty_interior
    {c : ℂ} (hc : Disconnected c)
    (hempty : interior (filledJulia c) = ∅)
    (hlsc :
      ∀ z : ℂ, z ∈ filledJulia c → ∀ a : ℝ,
        a < - logPotential (shiftedLimitingBrolinMeasure c) z →
          ∀ᶠ y in 𝓝 z,
            a < - logPotential (shiftedLimitingBrolinMeasure c) y) :
    HasGreenPotentialRepresentation c (gapAMu c) :=
  gapAMu_hasGreenPotentialRepresentation_of_shiftedBoundary_nonpos hc
    (shiftedBoundary_nonpos_of_lowerSemicontinuousAt_of_empty_interior
      hempty hlsc)

/-- Boundary value convergence contract for the shifted compactness limit.
After the unconditional quadratic identity, this is the actual value-level
hDisc target on `K_c`: the shifted finite potentials converge to the
`logPotential` value of the shifted limit, with the existing convention handling
the nonintegrable case. -/
def HasShiftedBoundaryPotentialValueLimit (c : ℂ) (ν : Measure ℂ) : Prop :=
  ∀ z : ℂ, z ∈ filledJulia c →
    Tendsto
      (fun k =>
        - logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
      atTop (𝓝 (- logPotential ν z))

/-- Boundary singular-kernel convergence contract for the shifted compactness
limit.  This stronger form records integrability as well as value convergence;
the hDisc closure below now only needs the value-convergence component. -/
def HasShiftedBoundaryPotentialLimit (c : ℂ) (ν : Measure ℂ) : Prop :=
  ∀ z : ℂ, z ∈ filledJulia c →
    Integrable (fun w => logKernel z w) ν ∧
      Tendsto
        (fun k =>
          - logPotential (preBrolinMeasure c (shiftedBrolinIndex c k)) z)
        atTop (𝓝 (- logPotential ν z))

/-- The stronger singular-kernel contract implies the value-level boundary
contract. -/
theorem HasShiftedBoundaryPotentialLimit.valueLimit
    {c : ℂ} {ν : Measure ℂ}
    (hlim : HasShiftedBoundaryPotentialLimit c ν) :
    HasShiftedBoundaryPotentialValueLimit c ν := by
  intro z hzK
  exact (hlim z hzK).2

/-- The shifted boundary value convergence contract forces the shifted boundary
potential to vanish, because the finite shifted potentials already tend to zero
on `K_c` in the disconnected case. -/
theorem shiftedBoundary_zero_of_boundaryPotentialValueLimit
    {c : ℂ} (hc : Disconnected c)
    (hlim :
      HasShiftedBoundaryPotentialValueLimit c (shiftedLimitingBrolinMeasure c)) :
    ∀ z : ℂ, z ∈ filledJulia c →
      - logPotential (shiftedLimitingBrolinMeasure c) z = 0 := by
  intro z hzK
  exact (tendsto_nhds_unique
    (neg_logPotential_preBrolinMeasure_shiftedIndex_tendsto_zero_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK)
    (hlim z hzK)).symm

/-- Shifted boundary-zero supplies the value-level boundary convergence
contract, because the finite shifted potentials already converge to zero on
`K_c`. -/
theorem HasShiftedBoundaryPotentialValueLimit.of_shiftedBoundary_zero
    {c : ℂ} (hc : Disconnected c)
    (hshift :
      ∀ z : ℂ, z ∈ filledJulia c →
        - logPotential (shiftedLimitingBrolinMeasure c) z = 0) :
    HasShiftedBoundaryPotentialValueLimit c (shiftedLimitingBrolinMeasure c) := by
  intro z hzK
  have hfinite :=
    neg_logPotential_preBrolinMeasure_shiftedIndex_tendsto_zero_filledJulia_of_disconnected
      (c := c) (z := z) hc hzK
  simpa [hshift z hzK] using hfinite

/-- For disconnected parameters, the value-level shifted boundary convergence
contract is equivalent to shifted boundary-zero. -/
theorem HasShiftedBoundaryPotentialValueLimit_iff_shiftedBoundary_zero
    {c : ℂ} (hc : Disconnected c) :
    HasShiftedBoundaryPotentialValueLimit c (shiftedLimitingBrolinMeasure c) ↔
      ∀ z : ℂ, z ∈ filledJulia c →
        - logPotential (shiftedLimitingBrolinMeasure c) z = 0 := by
  constructor
  · exact shiftedBoundary_zero_of_boundaryPotentialValueLimit hc
  · exact HasShiftedBoundaryPotentialValueLimit.of_shiftedBoundary_zero hc

/-- Equivalent value-limit form of the disconnected GAP-A hDisc target. -/
theorem gapAMu_hasGreenPotentialRepresentation_iff_shiftedBoundaryPotentialValueLimit
    {c : ℂ} (hc : Disconnected c) :
    HasGreenPotentialRepresentation c (gapAMu c) ↔
      HasShiftedBoundaryPotentialValueLimit c (shiftedLimitingBrolinMeasure c) := by
  rw [gapAMu_hasGreenPotentialRepresentation_iff_shiftedBoundary_zero hc,
    HasShiftedBoundaryPotentialValueLimit_iff_shiftedBoundary_zero hc]

/-- The stronger shifted boundary singular-kernel convergence contract forces
shifted boundary-zero through its value-level component. -/
theorem shiftedBoundary_zero_of_boundaryPotentialLimit
    {c : ℂ} (hc : Disconnected c)
    (hlim :
      HasShiftedBoundaryPotentialLimit c (shiftedLimitingBrolinMeasure c)) :
    ∀ z : ℂ, z ∈ filledJulia c →
      - logPotential (shiftedLimitingBrolinMeasure c) z = 0 :=
  shiftedBoundary_zero_of_boundaryPotentialValueLimit hc hlim.valueLimit

/-- hDisc closure from the shifted boundary value convergence contract.  This
is the leaner remaining analytic passage after the unconditional quadratic
identity has removed the separate integrability premise. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_shiftedBoundaryPotentialValueLimit
    {c : ℂ} (hc : Disconnected c)
    (hlim :
      HasShiftedBoundaryPotentialValueLimit c (shiftedLimitingBrolinMeasure c)) :
    HasGreenPotentialRepresentation c (gapAMu c) := by
  exact gapAMu_hasGreenPotentialRepresentation_of_shiftedBoundary_zero hc
    (shiftedBoundary_zero_of_boundaryPotentialValueLimit hc hlim)

/-- hDisc closure from the exact shifted boundary singular-kernel convergence
contract.  The value-level component is sufficient. -/
theorem gapAMu_hasGreenPotentialRepresentation_of_shiftedBoundaryPotentialLimit
    {c : ℂ} (hc : Disconnected c)
    (hlim :
      HasShiftedBoundaryPotentialLimit c (shiftedLimitingBrolinMeasure c)) :
    HasGreenPotentialRepresentation c (gapAMu c) :=
  gapAMu_hasGreenPotentialRepresentation_of_shiftedBoundaryPotentialValueLimit
    hc hlim.valueLimit

/-- Disconnected hDisc boundary-truncation core for `μ_c`: the constructed
Riesz measure is the zero-target Brolin limit, has the finite-potential core,
and every positive truncation of the boundary logarithmic kernel has
nonpositive limiting integral on `K_c`. -/
theorem brolinMuRieszMeasure_hDiscBoundaryTruncationCore {c : ℂ}
    (hc : Disconnected c) :
    brolinMuRieszMeasure c = brolinMu c ∧
      IsProbOn (brolinMuRieszMeasure c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (brolinMuRieszMeasure c) ∧
      HasSubseqLogPotentialLimit c (brolinMuRieszMeasure c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (brolinMuRieszMeasure c) z) ∧
      (∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z))) ∧
      ∀ z : ℂ, z ∈ filledJulia c → ∀ {δ : ℝ}, 0 < δ →
        ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ≤ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.2.2
  · intro z hz δ hδ
    exact integral_truncatedLogKernel_brolinMuRieszMeasure_nonpos_of_mem_filledJulia_of_disconnected
      hc hz hδ

/-- Strengthened disconnected hDisc boundary-truncation core for `μ_c`: the
constructed limiting/Riesz measure has the finite-potential core and every
positive boundary truncation is sandwiched between the fixed escape-disk
diameter lower bound and zero. -/
theorem brolinMuRieszMeasure_hDiscBoundaryTruncationBoundsCore {c : ℂ}
    (hc : Disconnected c) :
    brolinMuRieszMeasure c = brolinMu c ∧
      IsProbOn (brolinMuRieszMeasure c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (brolinMuRieszMeasure c) ∧
      HasSubseqLogPotentialLimit c (brolinMuRieszMeasure c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (brolinMuRieszMeasure c) z) ∧
      (∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z))) ∧
      ∀ z : ℂ, z ∈ filledJulia c → ∀ {δ : ℝ}, 0 < δ →
        - Real.log (max δ (2 * max 2 ‖c‖)) ≤
            ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ∧
          ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ≤ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.2.2
  · intro z hz δ hδ
    exact integral_truncatedLogKernel_brolinMuRieszMeasure_bounds_of_mem_filledJulia_of_disconnected
      hc hz hδ

/-- Boundary-singular core for the constructed disconnected hDisc measure:
besides the finite-potential and truncation bounds, the measure has no atom at
any point of `K_c`, so each truncation is below the true logarithmic kernel
almost everywhere.  This is the checked input for the remaining monotone
singular-kernel passage from truncations to the actual potential on `K_c`. -/
theorem brolinMuRieszMeasure_hDiscBoundarySingularCore {c : ℂ}
    (hc : Disconnected c) :
    brolinMuRieszMeasure c = brolinMu c ∧
      IsProbOn (brolinMuRieszMeasure c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (brolinMuRieszMeasure c) ∧
      HasSubseqLogPotentialLimit c (brolinMuRieszMeasure c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z =
          - logPotential (brolinMuRieszMeasure c) z) ∧
      (∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z))) ∧
      (∀ z : ℂ, z ∈ filledJulia c → brolinMuRieszMeasure c {z} = 0) ∧
      ∀ z : ℂ, z ∈ filledJulia c → ∀ {δ : ℝ}, 0 < δ →
        (- Real.log (max δ (2 * max 2 ‖c‖)) ≤
            ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ∧
          ∫ w, truncatedLogKernel z δ w ∂brolinMuRieszMeasure c ≤ 0) ∧
        ∀ᵐ w ∂brolinMuRieszMeasure c,
          truncatedLogKernel z δ w ≤ logKernel z w := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.2.1
  · exact (brolinMuRieszMeasure_hDiscFinitePotentialCore hc).2.2.2.2.2
  · intro z hz
    exact brolinMuRieszMeasure_singleton_eq_zero_of_mem_filledJulia_of_disconnected
      hc hz
  · intro z hz δ hδ
    exact ⟨
      integral_truncatedLogKernel_brolinMuRieszMeasure_bounds_of_mem_filledJulia_of_disconnected
        hc hz hδ,
      ae_truncatedLogKernel_le_logKernel_brolinMuRieszMeasure_of_mem_filledJulia_of_disconnected
        hc hz hδ⟩

/-- GAP-A boundary-singular core for the constructed disconnected hDisc
measure `μ_c`.  It packages the exact local data needed for the final
singular-kernel passage on `K_c`: finite-potential convergence, no atoms on
`K_c`, two-sided truncation bounds, and the a.e. comparison with the true
logarithmic kernel. -/
theorem gapAMu_hDiscBoundarySingularCore {c : ℂ} (hc : Disconnected c) :
    gapAMu c = brolinMu c ∧
      IsProbOn (gapAMu c) (filledJulia c) ∧
      IsWeakSubseqLimitOfPreBrolin c (gapAMu c) ∧
      HasSubseqLogPotentialLimit c (gapAMu c) ∧
      (∀ z : ℂ, z ∉ filledJulia c →
        greenFunctionDyn c z = - logPotential (gapAMu c) z) ∧
      (∀ z : ℂ,
        Tendsto
          (fun k =>
            - logPotential (preBrolinMeasure c (brolinLimitSubsequence c k)) z)
          atTop (𝓝 (greenFunctionDyn c z))) ∧
      (∀ z : ℂ, z ∈ filledJulia c → gapAMu c {z} = 0) ∧
      ∀ z : ℂ, z ∈ filledJulia c → ∀ {δ : ℝ}, 0 < δ →
        (- Real.log (max δ (2 * max 2 ‖c‖)) ≤
            ∫ w, truncatedLogKernel z δ w ∂gapAMu c ∧
          ∫ w, truncatedLogKernel z δ w ∂gapAMu c ≤ 0) ∧
        ∀ᵐ w ∂gapAMu c,
          truncatedLogKernel z δ w ≤ logKernel z w := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact gapAMu_eq_brolinMu c
  · exact gapAMu_isProbOn_filledJulia c
  · exact gapAMu_isWeakSubseqLimitOfPreBrolin c
  · exact gapAMu_hasSubseqLogPotentialLimit c
  · intro z hz
    exact green_eq_neg_logPotential_gapAMu_on_basin hz
  · exact (brolinMuRieszMeasure_hDiscBoundarySingularCore hc).2.2.2.2.2.1
  · intro z hz
    exact gapAMu_singleton_eq_zero_of_mem_filledJulia_of_disconnected hc hz
  · intro z hz δ hδ
    constructor
    · rw [gapAMu_eq_brolinMuRieszMeasure]
      exact integral_truncatedLogKernel_brolinMuRieszMeasure_bounds_of_mem_filledJulia_of_disconnected
        hc hz hδ
    · exact ae_truncatedLogKernel_le_logKernel_gapAMu_of_mem_filledJulia_of_disconnected
        hc hz hδ

end Bottcher
