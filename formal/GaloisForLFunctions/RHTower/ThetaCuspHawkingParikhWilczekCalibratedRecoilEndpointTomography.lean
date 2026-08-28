import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekBoundedPacketCountableTomography
import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekPositiveMatrixCrossGradeClassification

/-!
# Parikh--Wilczek calibrated recoil endpoint tomography

The literal Borel recoil holonomy contains a common reflection-odd wall factor multiplied by a
strictly positive, grade-dependent residual.  Dividing by that exact residual is a source-exact
calibration: throughout the open critical strip it recovers the same oriented wall coordinate at
every grade.

Coupling this calibrated orientation to the countable physical endpoint-winding basis constructed
in bounded-packet tomography yields an exact joint-kernel classification.  For every bounded
infinite grade packet, simultaneous vanishing at all physical endpoint scales occurs precisely on
the critical wall or for the zero packet.  Thus the endpoint basis removes every packet dark
sector without erasing the recoil orientation.

For the canonical constant-one bounded packet, universal flatness on the Xi divisor is equivalent
to the Riemann hypothesis, with no premises.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Source-exact recoil orientation after removing its positive grade residual. -/
def schwarzschildParikhWilczekCalibratedRecoilOrientation
    (s : ℂ) (k : ℕ) : ℝ :=
  (schwarzschildParikhWilczekBorelRecoilHolonomy s k).im /
    schwarzschildParikhWilczekBorelGradeResidual s k

/-- Residual calibration preserves exactly the common oriented wall factor. -/
theorem schwarzschildParikhWilczekCalibratedRecoilOrientation_eq_wallFactor
    (s : ℂ) (k : ℕ) (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    schwarzschildParikhWilczekCalibratedRecoilOrientation s k =
      schwarzschildParikhWilczekBorelWallFactor s := by
  rw [schwarzschildParikhWilczekCalibratedRecoilOrientation,
    schwarzschildParikhWilczekBorelRecoilHolonomy_im_factorization]
  have hres := schwarzschildParikhWilczekBorelGradeResidual_pos s k hs0 hs1
  field_simp [hres.ne']

/-- At nonzero height, the common oriented wall factor vanishes exactly on the critical line. -/
theorem schwarzschildParikhWilczekBorelWallFactor_eq_zero_iff
    (s : ℂ) (hsim : s.im ≠ 0) :
    schwarzschildParikhWilczekBorelWallFactor s = 0 ↔ s.re = 1 / 2 := by
  rw [schwarzschildParikhWilczekBorelWallFactor]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hleft | hright
    · rcases mul_eq_zero.mp hleft with htwo | him
      · norm_num at htwo
      · exact False.elim (hsim him)
    · linarith
  · intro hre
    rw [hre]
    norm_num

/-- Countable physical endpoint reporter coupling winding tomography to oriented recoil. -/
def schwarzschildParikhWilczekCalibratedRecoilEndpointResponse
    (c : ℕ → ℝ) (s : ℂ) (j : ℕ) : ℝ :=
  ∑' n : ℕ, c n *
    schwarzschildParikhWilczekWindingTerm n
      (schwarzschildParikhWilczekEndpointTomographyScale j)
      (schwarzschildParikhWilczekDimensionlessEnergyEndpoint
        (schwarzschildParikhWilczekEndpointTomographyScale j)) *
    schwarzschildParikhWilczekCalibratedRecoilOrientation s n

/-- The calibrated countable reporter factors into oriented wall and faithful endpoint sample. -/
theorem schwarzschildParikhWilczekCalibratedRecoilEndpointResponse_eq_wall_mul
    (c : ℕ → ℝ) (s : ℂ) (j : ℕ)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    schwarzschildParikhWilczekCalibratedRecoilEndpointResponse c s j =
      schwarzschildParikhWilczekBorelWallFactor s *
        schwarzschildParikhWilczekBoundedPacketEndpointResponse c j := by
  rw [schwarzschildParikhWilczekCalibratedRecoilEndpointResponse,
    schwarzschildParikhWilczekBoundedPacketEndpointResponse]
  simp_rw [schwarzschildParikhWilczekCalibratedRecoilOrientation_eq_wallFactor
    s _ hs0 hs1]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  ring

/-- Exact joint kernel: critical wall or zero bounded packet, with no further dark sector. -/
theorem schwarzschildParikhWilczekCalibratedRecoilEndpointResponse_eq_zero_iff
    {c : ℕ → ℝ} {C : ℝ} (s : ℂ)
    (hbound : ∀ n, |c n| ≤ C)
    (hs0 : 0 < s.re) (hs1 : s.re < 1) (hsim : s.im ≠ 0) :
    (∀ j : ℕ, schwarzschildParikhWilczekCalibratedRecoilEndpointResponse c s j = 0) ↔
      s.re = 1 / 2 ∨ c = 0 := by
  constructor
  · intro h
    by_cases hw : schwarzschildParikhWilczekBorelWallFactor s = 0
    · exact Or.inl ((schwarzschildParikhWilczekBorelWallFactor_eq_zero_iff
        s hsim).mp hw)
    · right
      apply (schwarzschildParikhWilczekBoundedPacketEndpointResponse_eq_zero_iff
        hbound).mp
      intro j
      have hj := h j
      rw [schwarzschildParikhWilczekCalibratedRecoilEndpointResponse_eq_wall_mul
        c s j hs0 hs1] at hj
      exact (mul_eq_zero.mp hj).resolve_left hw
  · rintro (hre | hc)
    · intro j
      rw [schwarzschildParikhWilczekCalibratedRecoilEndpointResponse_eq_wall_mul
        c s j hs0 hs1,
        (schwarzschildParikhWilczekBorelWallFactor_eq_zero_iff s hsim).mpr hre]
      simp
    · subst c
      intro j
      rw [schwarzschildParikhWilczekCalibratedRecoilEndpointResponse_eq_wall_mul
        0 s j hs0 hs1]
      simp [schwarzschildParikhWilczekBoundedPacketEndpointResponse]

/-- Canonical nonzero bounded packet used by the unconditional PW-B endpoint. -/
def schwarzschildParikhWilczekCanonicalBoundedPacket : ℕ → ℝ :=
  fun _ => 1

/-- The canonical packet is uniformly bounded by one. -/
theorem schwarzschildParikhWilczekCanonicalBoundedPacket_bound
    (n : ℕ) : |schwarzschildParikhWilczekCanonicalBoundedPacket n| ≤ 1 := by
  simp [schwarzschildParikhWilczekCanonicalBoundedPacket]

/-- **Premise-free PW-B endpoint.** Universal flatness of the source-exact calibrated countable
recoil reporter on the Xi divisor is equivalent to the Riemann hypothesis. -/
theorem riemannHypothesis_iff_schwarzschildParikhWilczekCalibratedRecoilEndpointResponse_zero :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport, ∀ j : ℕ,
        schwarzschildParikhWilczekCalibratedRecoilEndpointResponse
          schwarzschildParikhWilczekCanonicalBoundedPacket (rho : ℂ) j = 0 := by
  constructor
  · intro hRH rho j
    obtain ⟨hs0, hs1⟩ := xi_divisor_support_re_mem_open_unit rho
    rw [schwarzschildParikhWilczekCalibratedRecoilEndpointResponse_eq_wall_mul
      schwarzschildParikhWilczekCanonicalBoundedPacket (rho : ℂ) j hs0 hs1,
      schwarzschildParikhWilczekBorelWallFactor,
      xi_divisor_support_re_eq_half_of_rh hRH rho]
    norm_num
  · intro h
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    obtain ⟨hs0, hs1⟩ := xi_divisor_support_re_mem_open_unit rho
    have hkernel :=
      (schwarzschildParikhWilczekCalibratedRecoilEndpointResponse_eq_zero_iff
        (s := (rho : ℂ))
        schwarzschildParikhWilczekCanonicalBoundedPacket_bound hs0 hs1
        (xi_divisor_support_im_ne_zero rho)).mp (h rho)
    rcases hkernel with hre | hpacket
    · exact hre
    · have hvalue := congrFun hpacket 0
      simp [schwarzschildParikhWilczekCanonicalBoundedPacket] at hvalue

end

end RHTower
