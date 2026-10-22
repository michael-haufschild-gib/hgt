import GaloisForLFunctions.RHTower.Deninger.DeningerSchwartzNuclear
import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearProduct
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerRadialEndpoints
import GaloisForLFunctions.HTGeometry.SchwartzTranslation

/-!
# The two radial nuclear spaces of the Poisson complex

Two subspaces carry the Poisson complex.  The first is the space of even Schwartz functions
vanishing at the origin together with their Fourier transform; the second is the intersection of
all the integer-weight Schwartz spaces of the multiplicative half-line, which in logarithmic
coordinates is the space of smooth functions decaying faster than every exponential at both ends.

Both are nuclear.  The first is a subspace of `𝒮(ℝ)`, which is nuclear; the second is presented,
as the card's proof does, as the compatibility subspace of the countable product of the
integer-weight copies, and countable products and subspaces of nuclear spaces are nuclear.  The
seminorm family carried by that presentation is the projective-limit family, not the subspace
family of any single weight.

Neither space is zero: an explicit even Hermite combination lies in the first, and the Gaussian in
logarithmic coordinates lies in the second.

* `deningerIsNuclearSpaceC_meyerCap` : **the constrained even space is nuclear.**
* `deningerRadialCompat`, `deningerIsNuclearSpaceC_radialCompat` : **the radial space is
  nuclear.**
* `deningerMeyerCap_ne_bot`, `deningerRadialCompat_ne_bot` : both spaces are nonzero.
-/

open scoped Real SchwartzMap
open Complex MeasureTheory GaloisForLFunctions

noncomputable section

namespace RHTower

/-! ## The constrained even space -/

/-- **Meyer's space is nuclear**, being a subspace of the nuclear space `𝒮(ℝ)`. -/
theorem deningerIsNuclearSpaceC_meyerCap :
    DeningerIsNuclearSpaceC
      (fun m : ℕ => deningerRestrictSeminorm DeningerMeyerCap (shiftedSeminorm m)) :=
  deningerIsNuclearSpaceC_subspace _ _ deningerIsNuclearSpace_shiftedSeminormFamily

/-- The same in the Schwartz presentation: the restricted finite suprema of the Schwartz
seminorms. -/
theorem deningerIsNuclearSpaceC_meyerCap_schwartz :
    DeningerIsNuclearSpaceC (fun s : Finset (ℕ × ℕ) =>
      deningerRestrictSeminorm DeningerMeyerCap (s.sup (schwartzSeminormFamily ℂ ℝ ℂ))) := by
  refine deningerIsNuclearSpaceC_of_dominating
    (fun m : ℕ => deningerRestrictSeminorm DeningerMeyerCap (shiftedSeminorm m)) _ ?_ ?_
    deningerIsNuclearSpaceC_meyerCap
  · intro s
    obtain ⟨m, C, _, hb⟩ := schwartzSup_le_shiftedSeminorm s
    exact ⟨m, C, fun v => hb (v : 𝓢(ℝ, ℂ))⟩
  · intro m
    obtain ⟨s, C, _, hb⟩ := shiftedSeminorm_le_schwartzSup m
    refine ⟨s, (C : ℝ), fun v => ?_⟩
    have h := hb (v : 𝓢(ℝ, ℂ))
    rwa [_root_.smul_apply, NNReal.smul_def, smul_eq_mul] at h

/-! ## The constrained even space is nonzero -/

/-- An explicit nonzero element of Meyer's space: the combination of the zeroth and fourth Hermite
functions vanishing at the origin.  Both have Fourier eigenvalue one, so the combination is its own
Fourier transform and the second constraint is the first. -/
def deningerMeyerCapWitness : 𝓢(ℝ, ℂ) :=
  (hermiteSchwartz 4 0) • hermiteSchwartz 0 - (hermiteSchwartz 0 0) • hermiteSchwartz 4

theorem fourierSCLM_deningerMeyerCapWitness :
    fourierSCLM deningerMeyerCapWitness = deningerMeyerCapWitness := by
  rw [deningerMeyerCapWitness, map_sub, map_smul, map_smul, fourierSCLM_hermiteSchwartz,
    fourierSCLM_hermiteSchwartz]
  norm_num

theorem deningerMeyerCapWitness_mem : deningerMeyerCapWitness ∈ DeningerMeyerCap := by
  have hzero : deningerMeyerCapWitness 0 = 0 := by
    show (hermiteSchwartz 4 0) • hermiteSchwartz 0 0 - (hermiteSchwartz 0 0) • hermiteSchwartz 4 0
      = 0
    rw [smul_eq_mul, smul_eq_mul, mul_comm, sub_self]
  refine (deningerMeyerCap_mem_iff _).mpr ⟨fun x => ?_, hzero, ?_⟩
  · show (hermiteSchwartz 4 0) • hermiteSchwartz 0 (-x) - (hermiteSchwartz 0 0)
        • hermiteSchwartz 4 (-x)
      = (hermiteSchwartz 4 0) • hermiteSchwartz 0 x - (hermiteSchwartz 0 0) • hermiteSchwartz 4 x
    have h0 : hermiteSchwartz 0 (-x) = hermiteSchwartz 0 x := hermiteSchwartz_even 0 x
    have h4 : hermiteSchwartz 4 (-x) = hermiteSchwartz 4 x := hermiteSchwartz_even 2 x
    rw [h0, h4]
  · have hcle : (FourierTransform.fourierCLE ℂ 𝓢(ℝ, ℂ) deningerMeyerCapWitness)
        = fourierSCLM deningerMeyerCapWitness := by
      rw [FourierTransform.fourierCLE_apply, fourierSCLM_eq]
    rw [hcle, fourierSCLM_deningerMeyerCapWitness]
    exact hzero

theorem deningerMeyerCapWitness_ne_zero : deningerMeyerCapWitness ≠ 0 := by
  intro hzero
  have hpair : schwartzPair (hermiteSchwartz 4) deningerMeyerCapWitness
      = -((hermiteSchwartz 0 0) * schwartzPair (hermiteSchwartz 4) (hermiteSchwartz 4)) := by
    have hw : deningerMeyerCapWitness
        = (hermiteSchwartz 4 0) • hermiteSchwartz 0
          + (-(hermiteSchwartz 0 0)) • hermiteSchwartz 4 := by
      rw [deningerMeyerCapWitness, neg_smul, ← sub_eq_add_neg]
    rw [hw, schwartzPair_add_right, schwartzPair_smul_right, schwartzPair_smul_right,
      schwartzPair_hermiteSchwartz_eq_zero (by norm_num : (4 : ℕ) ≠ 0), mul_zero, zero_add]
    ring
  rw [hzero, schwartzPair_zero_right] at hpair
  have hgauss : hermiteSchwartz 0 0 ≠ 0 := by
    rw [hermiteSchwartz_zero, gaussianSchwartz_apply]
    refine Complex.ofReal_ne_zero.mpr (gaussReal_pos 0).ne'
  exact (mul_ne_zero hgauss (schwartzPair_hermiteSchwartz_self_ne_zero 4))
    (neg_eq_zero.mp hpair.symm)

theorem deningerMeyerCap_ne_bot : DeningerMeyerCap ≠ ⊥ := by
  intro hbot
  exact deningerMeyerCapWitness_ne_zero
    ((Submodule.eq_bot_iff _).mp hbot _ deningerMeyerCapWitness_mem)

/-! ## The radial space -/

/-- **The radial space**, presented as the compatibility subspace of the product of the
integer-weight Schwartz spaces: a family `(g_s)` with `g_s(t) = e^{st}g_0(t)`.  In logarithmic
coordinates `g_s` is the `s`-th weighted transform of one function, so a member of the family is a
function all of whose exponential weightings are Schwartz. -/
def deningerRadialCompat : Submodule ℂ (∀ _ : ℤ, 𝓢(ℝ, ℂ)) where
  carrier := {g | ∀ (s : ℤ) (t : ℝ), g s t = Complex.exp ((s : ℂ) * t) * g 0 t}
  add_mem' {g h} hg hh := by
    intro s t
    show g s t + h s t = Complex.exp ((s : ℂ) * t) * (g 0 t + h 0 t)
    rw [hg s t, hh s t]
    ring
  zero_mem' := by
    intro s t
    show (0 : ℂ) = Complex.exp ((s : ℂ) * t) * 0
    rw [mul_zero]
  smul_mem' c g hg := by
    intro s t
    show c • g s t = Complex.exp ((s : ℂ) * t) * (c • g 0 t)
    rw [hg s t, smul_eq_mul, smul_eq_mul]
    ring

theorem deningerRadialCompat_mem {g : ∀ _ : ℤ, 𝓢(ℝ, ℂ)} :
    g ∈ deningerRadialCompat ↔ ∀ (s : ℤ) (t : ℝ), g s t = Complex.exp ((s : ℂ) * t) * g 0 t :=
  Iff.rfl

/-- A member of the radial space is determined by its zeroth weight. -/
theorem deningerRadialCompat_ext {g h : ∀ _ : ℤ, 𝓢(ℝ, ℂ)} (hg : g ∈ deningerRadialCompat)
    (hh : h ∈ deningerRadialCompat) (h0 : g 0 = h 0) : g = h := by
  funext s
  refine SchwartzMap.ext fun t => ?_
  rw [hg s t, hh s t, h0]

/-- **The radial space is nuclear**: a subspace of a countable product of nuclear spaces. -/
theorem deningerIsNuclearSpaceC_radialCompat :
    DeningerIsNuclearSpaceC (fun i => deningerRestrictSeminorm deningerRadialCompat
      (deningerPiFamily (fun _ : ℤ => (shiftedSeminorm : SeminormFamily ℂ 𝓢(ℝ, ℂ) ℕ)) i)) :=
  deningerIsNuclearSpaceC_subspace _ _
    (deningerIsNuclearSpace_pi _ fun _ => deningerIsNuclearSpace_shiftedSeminormFamily)

/-! ## The radial space is nonzero -/

/-- The Gaussian in logarithmic coordinates, with all its exponential weightings: each weight is a
translate of the Gaussian times a constant. -/
def deningerRadialGauss : ∀ _ : ℤ, 𝓢(ℝ, ℂ) := fun s =>
  (Complex.exp ((s : ℂ) ^ 2 / (4 * π))) •
    SchwartzMap.translateCLM ℂ (-((s : ℝ) / (2 * π))) gaussianSchwartz

theorem deningerRadialGauss_apply (s : ℤ) (t : ℝ) :
    deningerRadialGauss s t
      = Complex.exp ((s : ℂ) ^ 2 / (4 * π)) * ((gaussReal (t + -((s : ℝ) / (2 * π))) : ℝ) : ℂ) :=
  rfl

theorem deningerRadialGauss_zero : deningerRadialGauss 0 = gaussianSchwartz := by
  refine SchwartzMap.ext fun t => ?_
  rw [deningerRadialGauss_apply, gaussianSchwartz_apply]
  norm_num

theorem deningerRadialGauss_mem : deningerRadialGauss ∈ deningerRadialCompat := by
  intro s t
  rw [deningerRadialGauss_apply, deningerRadialGauss_zero, gaussianSchwartz_apply]
  have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have hl : ((gaussReal (t + -((s : ℝ) / (2 * π))) : ℝ) : ℂ)
      = Complex.exp (((-(π * (t + -((s : ℝ) / (2 * π))) ^ 2) : ℝ) : ℂ)) := by
    rw [gaussReal, Complex.ofReal_exp]
  have hr : ((gaussReal t : ℝ) : ℂ) = Complex.exp (((-(π * t ^ 2) : ℝ) : ℂ)) := by
    rw [gaussReal, Complex.ofReal_exp]
  rw [hl, hr, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hpic : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi
  push_cast
  field_simp
  ring

theorem deningerRadialGauss_ne_zero : deningerRadialGauss ≠ 0 := by
  intro hzero
  have h0 : deningerRadialGauss 0 = 0 := by rw [hzero]; rfl
  rw [deningerRadialGauss_zero] at h0
  have hval : gaussianSchwartz (0 : ℝ) = 0 := by rw [h0]; rfl
  rw [gaussianSchwartz_apply] at hval
  exact (Complex.ofReal_ne_zero.mpr (gaussReal_pos 0).ne') hval

theorem deningerRadialCompat_ne_bot : deningerRadialCompat ≠ ⊥ := by
  intro hbot
  exact deningerRadialGauss_ne_zero
    ((Submodule.eq_bot_iff _).mp hbot _ deningerRadialGauss_mem)

end RHTower

end
