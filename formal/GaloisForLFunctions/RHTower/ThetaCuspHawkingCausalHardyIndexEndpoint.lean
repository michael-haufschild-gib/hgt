import GaloisForLFunctions.RHTower.ThetaCuspHawkingWignerSmithWindingEndpoint
import GaloisForLFunctions.HTGeometry.CaratheodoryNevanlinnaPick
import GaloisForLFunctions.HTGeometry.HardyDiskModelSpace

/-!
# Causal Hardy index of theta-cusp Hawking resonances

The normalized theta-cusp moving-mirror response is a literal `XiC` form factor.  An upper
backreaction resonance `alpha` therefore gives a right-half-plane causal zero `b = -i alpha`.
The source-normalized Cayley coordinate `a = (b - 1) / (b + 1)` lies in the open disk and defines
one inner Blaschke scattering channel on `H²(D)`.

This file proves the corresponding scalar Lax--Phillips index theorem.  The scattering multiplier
is an isometry, but its outgoing range misses exactly the Szegő kernel line at `a`; the Hardy defect
has dimension one and equals the physical Wigner--Smith winding charge.  Thus KMS boundary
losslessness and ordinary Hilbert-space minimality cannot erase an isolated resonance.  Analytic
causal state space sees a genuine Gamow/model-space vector where an `L²` boundary description sees
only a measure-zero zero.

The final equivalence is deliberately marked as a reduction.  Its condition is **not** ordinary
Lax--Phillips asymptotic completeness: complete scattering can have nontrivial inner scattering
matrices and resonance model spaces.  A new RH producer would instead have to derive the much
stronger absence of this particular source-selected inner factor from independent theta dynamics.
-/

open Complex Real

noncomputable section

namespace RHTower

/-- Unit-aperture disk coordinate of a causal theta-Hawking resonance zero. -/
def thetaCuspHawkingCausalHardyNode
    (r : ThetaCuspHawkingBackreactionResonantMode) : ℂ :=
  GaloisForLFunctions.HTGeometry.cayleyRight
    (thetaCuspHawkingCausalZero r)

theorem norm_thetaCuspHawkingCausalHardyNode_lt_one
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) :
    ‖thetaCuspHawkingCausalHardyNode r‖ < 1 := by
  apply GaloisForLFunctions.HTGeometry.norm_cayleyRight_lt_one
  rw [thetaCuspHawkingCausalZero_re]
  exact hr

/-- Szegő/Gamow vector attached to an upper theta-Hawking resonance. -/
def thetaCuspHawkingCausalHardyKernel
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) : GaloisForLFunctions.HTGeometry.HardyDisk :=
  GaloisForLFunctions.HTGeometry.hardyKernel
    (norm_thetaCuspHawkingCausalHardyNode_lt_one r hr)

/-- Cayley-chart Hardy scattering operator of one causal all-pass resonance sector. -/
def thetaCuspHawkingCausalHardyScattering
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) :
    GaloisForLFunctions.HTGeometry.HardyDisk →L[ℂ]
      GaloisForLFunctions.HTGeometry.HardyDisk :=
  GaloisForLFunctions.HTGeometry.hardyMul
    (GaloisForLFunctions.HTGeometry.singleBlaschke
      (norm_thetaCuspHawkingCausalHardyNode_lt_one r hr)).toMultiplier

/-- Outgoing causal range of one Cayley-completed resonance channel. -/
def thetaCuspHawkingCausalHardyRange
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) :
    Submodule ℂ GaloisForLFunctions.HTGeometry.HardyDisk :=
  LinearMap.range
    ((thetaCuspHawkingCausalHardyScattering r hr :
      GaloisForLFunctions.HTGeometry.HardyDisk →L[ℂ]
        GaloisForLFunctions.HTGeometry.HardyDisk) :
      GaloisForLFunctions.HTGeometry.HardyDisk →ₗ[ℂ]
        GaloisForLFunctions.HTGeometry.HardyDisk)

theorem thetaCuspHawkingCausalHardyKernel_ne_zero
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) :
    thetaCuspHawkingCausalHardyKernel r hr ≠ 0 :=
  GaloisForLFunctions.HTGeometry.hardyKernel_ne_zero
    (norm_thetaCuspHawkingCausalHardyNode_lt_one r hr)

/-- The causal range is exactly the orthogonal complement of the resonance kernel line. -/
theorem thetaCuspHawkingCausalHardyRange_eq_kernel_orthogonal
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) :
    thetaCuspHawkingCausalHardyRange r hr =
      (ℂ ∙ thetaCuspHawkingCausalHardyKernel r hr)ᗮ := by
  exact GaloisForLFunctions.HTGeometry.range_hardyMul_singleBlaschke
    (norm_thetaCuspHawkingCausalHardyNode_lt_one r hr)

/-- Boundary-lossless Cayley scattering remains an isometry on the causal Hardy carrier. -/
theorem isometry_thetaCuspHawkingCausalHardyScattering
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) :
    Isometry (thetaCuspHawkingCausalHardyScattering r hr) :=
  GaloisForLFunctions.HTGeometry.isometry_hardyMul_blaschke _

/-- One upper resonance creates exactly one missing outgoing Hardy direction. -/
theorem finrank_thetaCuspHawkingCausalHardyDefect_eq_one
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) :
    Module.finrank ℂ ((thetaCuspHawkingCausalHardyRange r hr)ᗮ) = 1 := by
  exact GaloisForLFunctions.HTGeometry.finrank_orthogonal_range_singleBlaschke
    (norm_thetaCuspHawkingCausalHardyNode_lt_one r hr)

/-- Hardy defect index equals the physical Wigner--Smith winding charge. -/
theorem thetaCuspHawkingCausalHardyDefectIndex_eq_windingCharge
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) :
    (Module.finrank ℂ ((thetaCuspHawkingCausalHardyRange r hr)ᗮ) : ℝ) =
      thetaCuspHawkingAllPassWindingCharge r := by
  rw [finrank_thetaCuspHawkingCausalHardyDefect_eq_one r hr,
    thetaCuspHawkingAllPassWindingCharge_eq_one r hr]
  norm_num

/-- Losslessness does not imply absence of an inner scattering factor: the outgoing Hardy range is
proper for every upper resonance. -/
theorem thetaCuspHawkingCausalHardyRange_ne_top
    (r : ThetaCuspHawkingBackreactionResonantMode)
    (hr : 0 < r.1.im) :
    thetaCuspHawkingCausalHardyRange r hr ≠ ⊤ := by
  intro htop
  have hdim := finrank_thetaCuspHawkingCausalHardyDefect_eq_one r hr
  rw [htop, Submodule.top_orthogonal_eq_bot, finrank_bot] at hdim
  omega

/-- [OPEN PRODUCER] No upper theta-Hawking all-pass sector leaves an additional finite-rank causal
inner defect.  This is strictly stronger than Lax--Phillips asymptotic completeness and must not be
inferred from completeness, unitarity, or passive minimality. -/
def ThetaCuspHawkingCausalHardyNoInnerDefect : Prop :=
  ∀ (r : ThetaCuspHawkingBackreactionResonantMode) (hr : 0 < r.1.im),
    thetaCuspHawkingCausalHardyRange r hr = ⊤

/-- [REDUCTION] Absence of the source-selected causal inner defect is RH-strength.  This is not an
independent proof; ordinary scattering completeness is compatible with the defect. -/
theorem riemannHypothesis_iff_thetaCuspHawkingCausalHardyNoInnerDefect :
    RiemannHypothesis ↔ ThetaCuspHawkingCausalHardyNoInnerDefect := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  constructor
  · intro hreal r hr
    have hzero := hreal r.1
      (thetaCuspHawkingBackreactionResonantMode_XiC_eq_zero r)
    exfalso
    linarith
  · intro hcomplete alpha hXi
    let r : ThetaCuspHawkingBackreactionResonantMode :=
      ⟨alpha,
        (xiC_eq_zero_iff_thetaCuspHawkingBackreactionResonance alpha).mp hXi⟩
    by_contra him
    have horient : 0 < r.1.im ∨
        0 < (thetaCuspHawkingBackreactionReflectedResonantMode r).1.im := by
      rw [thetaCuspHawkingBackreactionReflectedResonantMode_im]
      rcases lt_or_gt_of_ne him with hneg | hpos
      · exact Or.inr (neg_pos.mpr hneg)
      · exact Or.inl hpos
    rcases horient with hr | hr
    · exact thetaCuspHawkingCausalHardyRange_ne_top r hr (hcomplete r hr)
    · let r' := thetaCuspHawkingBackreactionReflectedResonantMode r
      exact thetaCuspHawkingCausalHardyRange_ne_top r' hr (hcomplete r' hr)

end RHTower
