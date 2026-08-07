import GaloisForLFunctions.RHTower.GammaCoPoissonSoninQuadrantSection

/-!
# The two-path commutator of the co-Poisson quotient maps, and the anti-diagonal torsion

The two bonding maps `T_j^+ = E_j U_r^*` and `T_j^- = E_j U_r` are exchanged by the cosine
involution, and on the co-Poisson annihilator boundary they act on the quotient kernel by the two
reciprocal characters.  Two consequences are recorded here.

* The two-path commutator applied to a quotient kernel is exactly the source-error expression: the
  characters cancel and what remains is the image of the co-Poisson source defects at the two
  levels above.  On the annihilator boundary the defects vanish, so the commutator does.
* The ratio of the two edge norms is the square modulus of the character, independently of every
  aperture-kernel norm.  A rank-one reciprocal system with that flatness has exactly one gauge
  invariant, the ratio of its two edge coefficients.
-/

open Complex Real
open scoped InnerProductSpace

noncomputable section

namespace RHTower

variable {w : ℂ} {a r : ℝ}

/-- The two-path commutator `K_j = T_j^+ T_{j+1}^- - T_j^- T_{j+1}^+`. -/
def coPoissonQuotientCommutator (a r : ℝ) (ha : 0 < a) (hr : 0 < r) (j : ℕ) :
    evenSubspace →L[ℂ] evenSubspace :=
  (coPoissonQuotientForward a r ha hr j).comp (coPoissonQuotientInverse a r ha hr (j + 1)) -
    (coPoissonQuotientInverse a r ha hr j).comp (coPoissonQuotientForward a r ha hr (j + 1))

/-- **The exact off-divisor source-error syzygy.**  Applied to a quotient kernel the two-path
commutator is exactly the difference of the two source-defect transports; the two reciprocal
characters cancel identically. -/
theorem coPoissonQuotientCommutator_ladderKernel_offDivisor {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r) (j : ℕ) :
    coPoissonQuotientCommutator a r ha hr j
        (coPoissonLadderKernel w hlo hhi a r ha hr (j + 2)) =
      ((starRingEnd ℂ) (soninLadderCharacter w r) •
          coPoissonQuotientInverse a r ha hr j
            (coPoissonLadderDefect w hlo hhi a r ha hr (j + 1)) -
        (starRingEnd ℂ) ((soninLadderCharacter w r)⁻¹) •
          coPoissonQuotientForward a r ha hr j
            (coPoissonLadderDefect w hlo hhi a r ha hr (j + 1))) +
      (coPoissonQuotientInverse a r ha hr j
          (coPoissonQuotientForward a r ha hr (j + 1)
            (coPoissonLadderDefect w hlo hhi a r ha hr (j + 2))) -
        coPoissonQuotientForward a r ha hr j
          (coPoissonQuotientInverse a r ha hr (j + 1)
            (coPoissonLadderDefect w hlo hhi a r ha hr (j + 2)))) := by
  have hne : ((starRingEnd ℂ) (soninLadderCharacter w r)) ≠ 0 := by
    simpa using soninLadderCharacter_ne_zero hr w
  have hidx : j + 1 + 1 = j + 2 := by omega
  have hminus := coPoissonQuotientInverse_ladderKernel_offDivisor (w := w) (hlo := hlo)
    (hhi := hhi) (ha := ha) (hr := hr) hr1 (j + 1)
  have hplus := coPoissonQuotientForward_ladderKernel_offDivisor (w := w) (hlo := hlo)
    (hhi := hhi) (ha := ha) (hr := hr) hr1 (j + 1)
  rw [hidx] at hminus hplus
  have hf := coPoissonQuotientForward_ladderKernel_offDivisor (w := w) (hlo := hlo) (hhi := hhi)
    (ha := ha) (hr := hr) hr1 j
  have hi := coPoissonQuotientInverse_ladderKernel_offDivisor (w := w) (hlo := hlo) (hhi := hhi)
    (ha := ha) (hr := hr) hr1 j
  rw [coPoissonQuotientCommutator]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, hminus, hplus,
    map_sub, ContinuousLinearMap.map_smul, hf, hi, smul_sub, smul_smul]
  rw [← map_mul, ← map_mul, mul_inv_cancel₀ (soninLadderCharacter_ne_zero hr w),
    inv_mul_cancel₀ (soninLadderCharacter_ne_zero hr w)]
  simp only [map_one, one_smul]
  abel

/-- On the annihilator boundary the two-path commutator kills the quotient kernel. -/
theorem coPoissonQuotientCommutator_ladderKernel_eq_zero {hlo : 1 / 2 < w.re} {hhi : w.re < 1}
    {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (j : ℕ) :
    coPoissonQuotientCommutator a r ha hr j
        (coPoissonLadderKernel w hlo hhi a r ha hr (j + 2)) = 0 := by
  rw [coPoissonQuotientCommutator_ladderKernel_offDivisor hr1 j,
    coPoissonLadderDefect_eq_zero_of_annihilator hann (j + 1),
    coPoissonLadderDefect_eq_zero_of_annihilator hann (j + 2)]
  simp

/-! ## The anti-diagonal relative torsion -/

/-- **The exact edge-norm ratio.**  On the annihilator boundary the forward edge is longer than the
inverse edge by exactly the square modulus of the character, independently of every
aperture-kernel norm. -/
theorem norm_coPoissonQuotientForward_div_inverse_ladderKernel {hlo : 1 / 2 < w.re}
    {hhi : w.re < 1} {ha : 0 < a} {hr : 0 < r} (hr1 : 1 ≤ r)
    (hann : CoPoissonLadderAnnihilator w hlo hhi a r ha hr) (j : ℕ)
    (hy : coPoissonLadderKernel w hlo hhi a r ha hr j ≠ 0) :
    ‖coPoissonQuotientForward a r ha hr j (coPoissonLadderKernel w hlo hhi a r ha hr (j + 1))‖ /
        ‖coPoissonQuotientInverse a r ha hr j
          (coPoissonLadderKernel w hlo hhi a r ha hr (j + 1))‖ =
      ‖soninLadderCharacter w r‖ ^ 2 := by
  have hLpos : 0 < ‖soninLadderCharacter w r‖ := norm_soninLadderCharacter_pos hr w
  have hypos : 0 < ‖coPoissonLadderKernel w hlo hhi a r ha hr j‖ := norm_pos_iff.mpr hy
  rw [coPoissonQuotientForward_ladderKernel hr1 hann j,
    coPoissonQuotientInverse_ladderKernel hr1 hann j, norm_smul, norm_smul]
  simp only [RCLike.norm_conj, norm_inv]
  field_simp

/-- **The complete gauge invariant of a rank-one reciprocal flat system.**  If two nonzero scalar
edge families satisfy the flatness relation, their ratio does not depend on the level. -/
theorem ratio_eq_of_flat_reciprocal_edges {A B : ℕ → ℂ} (hB : ∀ j, B j ≠ 0)
    (hflat : ∀ j, A j * B (j + 1) = B j * A (j + 1)) (j : ℕ) :
    A (j + 1) / B (j + 1) = A j / B j := by
  rw [div_eq_div_iff (hB (j + 1)) (hB j)]
  linear_combination -(hflat j)

/-- Hence the ratio is constant along the whole ladder. -/
theorem ratio_const_of_flat_reciprocal_edges {A B : ℕ → ℂ} (hB : ∀ j, B j ≠ 0)
    (hflat : ∀ j, A j * B (j + 1) = B j * A (j + 1)) (j : ℕ) :
    A j / B j = A 0 / B 0 := by
  induction j with
  | zero => rfl
  | succ n ih => rw [ratio_eq_of_flat_reciprocal_edges hB hflat n, ih]

end RHTower
