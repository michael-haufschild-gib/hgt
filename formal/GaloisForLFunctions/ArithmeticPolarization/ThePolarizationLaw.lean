import Mathlib

/-!
# The polarization law

Weil's step from a polarization to purity, isolated from everything else.

* **Abstract law.** In a complex algebra with an involution, let `τ` be a linear functional and
  `ξ` a *similitude*, `ξ′ ξ = c`. If `v ≠ 0` satisfies `ξ v = μ v` and `τ(v′ v) ≠ 0` (`v` is
  *anisotropic*), then `|μ|² = c` (`normSq_eq_of_similitude`). A faithful positive trace makes
  every nonzero vector anisotropic, so every eigenvalue of left multiplication by a similitude has
  modulus `√c` (`normSq_eq_of_hasEigenvalue_of_polarization`). Neither the trace property nor
  finite dimension is used: the only input is that eigenvectors are anisotropic.
* **Spectral model.** A finite spectrum `S ⊆ ℂ^×` closed under the reflection `β ↦ 1/β̄`, with
  reflection-invariant weights, carries the Rosati form `Σ_β m_β conj(x(1/β̄)) x(β)` on functions
  `x : ℂ → ℂ`. It is real (`conj_rosatiForm`). The Frobenius `F = (β ↦ β)` is always a similitude
  of ratio one, `F′ F = 1` (`frob_star_mul_frob`): the involution is free. The form is a
  polarization iff every point of `S` is unitary (`rosatiForm_nonneg_iff_unitary`), and the
  eigenvector `δ_β` of an off-circle point is isotropic (`rosatiForm_single`): positivity is the
  whole content, and it fails exactly where eigenvectors become isotropic.
* **The two forms of the spectral model.** The Rosati form is the collided form
  `D(x) = Σ m_β |x(β)|²` minus the off-circle defect `Σ (m_β/2)|x(β) − x(1/β̄)|²`
  (`re_rosatiForm_eq_collided_sub_defect`); `D` is positive and the Frobenius preserves it iff the
  spectrum is unitary (`collided_frob_invariant_iff_unitary`), while the Rosati form is always
  Frobenius invariant: the calibration of `HeckeInvarianceOfTheCollidedPolarizationIsRH`.
-/

open Complex Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

/-! ### 1. The abstract polarization law -/

section Abstract

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- **The polarization law at one eigenvector.** A similitude `ξ′ ξ = c` has `|μ|² = c` at every
anisotropic eigenvector: `conj μ · μ · τ(v′v) = τ((ξv)′(ξv)) = τ(v′ ξ′ ξ v) = c τ(v′v)`. -/
theorem normSq_eq_of_similitude (τ : A →ₗ[ℂ] ℂ) {ξ v : A} {c : ℝ} {μ : ℂ}
    (hξ : star ξ * ξ = algebraMap ℂ A c) (hμ : ξ * v = μ • v) (hv : τ (star v * v) ≠ 0) :
    Complex.normSq μ = c := by
  have key : τ (star (ξ * v) * (ξ * v)) = (conj μ * μ) * τ (star v * v) := by
    rw [hμ, star_smul, smul_mul_smul_comm, map_smul, smul_eq_mul]
    rfl
  have key' : τ (star (ξ * v) * (ξ * v)) = (c : ℂ) * τ (star v * v) := by
    rw [star_mul, show star v * star ξ * (ξ * v) = star v * (star ξ * ξ) * v by noncomm_ring, hξ,
      Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, map_smul,
      smul_eq_mul]
  have h := key.symm.trans key'
  have h2 : conj μ * μ = (c : ℂ) := mul_right_cancel₀ hv h
  have h3 : (Complex.normSq μ : ℂ) = c := by rw [Complex.normSq_eq_conj_mul_self, h2]
  exact_mod_cast h3

/-- A **polarization**: a linear functional with `τ(v′v)` real, nonnegative, and zero only at
`v = 0`. -/
def IsPolarization (τ : A →ₗ[ℂ] ℂ) : Prop :=
  ∀ v : A, (τ (star v * v)).im = 0 ∧ 0 ≤ (τ (star v * v)).re ∧ (τ (star v * v) = 0 → v = 0)

/-- **The polarization law.** For a polarization, every eigenvalue of left multiplication by a
similitude of ratio `c` has `|μ|² = c`. This is Weil's step from Rosati positivity to purity. -/
theorem normSq_eq_of_hasEigenvalue_of_polarization {τ : A →ₗ[ℂ] ℂ} (hτ : IsPolarization τ)
    {ξ : A} {c : ℝ} (hξ : star ξ * ξ = algebraMap ℂ A c) {μ : ℂ}
    (hμ : Module.End.HasEigenvalue (LinearMap.mulLeft ℂ ξ) μ) : Complex.normSq μ = c := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := (Module.End.hasEigenvector_iff.mp hv).2
  have happ : ξ * v = μ • v := by
    have := hv.apply_eq_smul
    simpa using this
  exact normSq_eq_of_similitude τ hξ happ fun h => hv0 ((hτ v).2.2 h)

end Abstract

/-! ### 2. The spectral model of a polarized ring -/

/-- The **Rosati reflection** `β ↦ 1/β̄` of a normalized Frobenius eigenvalue (`α ↦ q/ᾱ`). -/
def refl (β : ℂ) : ℂ := (conj β)⁻¹

theorem refl_refl (β : ℂ) : refl (refl β) = β := by
  simp [refl, map_inv₀]

/-- A point is fixed by the reflection iff it is unitary. -/
theorem refl_eq_self_iff {β : ℂ} (hβ : β ≠ 0) : refl β = β ↔ ‖β‖ = 1 := by
  have hc : conj β ≠ 0 := by simpa using hβ
  rw [refl, inv_eq_iff_eq_inv, ← one_div, eq_div_iff hβ, mul_comm, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  constructor
  · intro h
    have h' : ‖β‖ ^ 2 = 1 := by exact_mod_cast h
    have := norm_nonneg β
    nlinarith
  · intro h; rw [h]; norm_num

/-- A finite **reflection-closed spectrum** with reflection-invariant positive weights. -/
structure ReflSpectrum where
  S : Finset ℂ
  zero_not_mem : (0 : ℂ) ∉ S
  refl_mem : ∀ β ∈ S, refl β ∈ S
  m : ℂ → ℝ
  m_pos : ∀ β ∈ S, 0 < m β
  m_refl : ∀ β ∈ S, m (refl β) = m β

namespace ReflSpectrum

variable (R : ReflSpectrum)

theorem ne_zero_of_mem {β : ℂ} (hβ : β ∈ R.S) : β ≠ 0 := fun h => R.zero_not_mem (h ▸ hβ)

/-- The **Rosati form** `Σ_β m_β conj(x(1/β̄)) x(β)`: the trace of `x′ x` for the involution
`x′(β) = conj(x(1/β̄))`. -/
def rosatiForm (x : ℂ → ℂ) : ℂ := ∑ β ∈ R.S, (R.m β : ℂ) * conj (x (refl β)) * x β

/-- The Rosati involution on functions on the spectrum. -/
def rstar (x : ℂ → ℂ) : ℂ → ℂ := fun β => conj (x (refl β))

/-- The Frobenius `F(β) = β` is a similitude of ratio one on the spectrum: `F′ F = 1`. -/
theorem frob_star_mul_frob {β : ℂ} (hβ : β ∈ R.S) : rstar (fun z => z) β * β = 1 := by
  have h0 := R.ne_zero_of_mem hβ
  simp [rstar, refl, map_inv₀, h0]

/-- The reflection is a bijection of the spectrum. -/
theorem sum_refl (f : ℂ → ℂ) : ∑ β ∈ R.S, f (refl β) = ∑ β ∈ R.S, f β := by
  refine Finset.sum_nbij' refl refl (fun β hβ => R.refl_mem β hβ) (fun β hβ => R.refl_mem β hβ)
    (fun β _ => refl_refl β) (fun β _ => refl_refl β)
    (fun β _ => rfl)

/-- The Rosati form is real. -/
theorem conj_rosatiForm (x : ℂ → ℂ) : conj (R.rosatiForm x) = R.rosatiForm x := by
  rw [rosatiForm, map_sum, ← R.sum_refl]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [refl_refl, R.m_refl β hβ, map_mul, map_mul, Complex.conj_ofReal,
    Complex.conj_conj]
  ring

theorem rosatiForm_im (x : ℂ → ℂ) : (R.rosatiForm x).im = 0 :=
  Complex.conj_eq_iff_im.mp (R.conj_rosatiForm x)

/-- On a unitary spectrum the Rosati form is `Σ m_β |x(β)|²`. -/
theorem rosatiForm_of_unitary (hu : ∀ β ∈ R.S, ‖β‖ = 1) (x : ℂ → ℂ) :
    R.rosatiForm x = ((∑ β ∈ R.S, R.m β * Complex.normSq (x β) : ℝ) : ℂ) := by
  rw [rosatiForm]
  push_cast
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [(refl_eq_self_iff (R.ne_zero_of_mem hβ)).mpr (hu β hβ), mul_assoc,
    ← Complex.normSq_eq_conj_mul_self]

/-- **The polarization of the spectral model is purity.** The Rosati form is nonnegative on every
function iff every point of the spectrum is unitary; at an off-circle point `β₀` the function
`δ_{β₀} − δ_{1/β̄₀}` has form `−2 m_{β₀}`. -/
theorem rosatiForm_nonneg_iff_unitary :
    (∀ x : ℂ → ℂ, 0 ≤ (R.rosatiForm x).re) ↔ ∀ β ∈ R.S, ‖β‖ = 1 := by
  classical
  constructor
  · intro h β₀ hβ₀
    by_contra hne
    have h0 := R.ne_zero_of_mem hβ₀
    have hr : refl β₀ ≠ β₀ := fun h' => hne ((refl_eq_self_iff h0).mp h')
    set x : ℂ → ℂ := fun z => if z = β₀ then 1 else if z = refl β₀ then -1 else 0
    have hxβ : x β₀ = 1 := by simp [x]
    have hxr : x (refl β₀) = -1 := by simp [x, hr]
    have hxz : ∀ z, z ≠ β₀ → z ≠ refl β₀ → x z = 0 := fun z h1 h2 => by simp [x, h1, h2]
    have hsum : R.rosatiForm x = -(2 * R.m β₀ : ℝ) := by
      rw [rosatiForm, ← Finset.sum_subset (Finset.subset_iff.mpr fun z hz => by
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hβ₀
          · exact R.refl_mem β₀ hβ₀ : ({β₀, refl β₀} : Finset ℂ) ⊆ R.S)]
      · rw [Finset.sum_pair hr.symm, refl_refl β₀, R.m_refl β₀ hβ₀, hxβ, hxr]
        push_cast; simp; ring
      · intro z _ hz
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
        rw [hxz z hz.1 hz.2, mul_zero]
    have := h x
    rw [hsum] at this
    simp at this
    linarith [R.m_pos β₀ hβ₀]
  · intro hu x
    rw [R.rosatiForm_of_unitary hu, Complex.ofReal_re]
    exact Finset.sum_nonneg fun β hβ => mul_nonneg (R.m_pos β hβ).le (Complex.normSq_nonneg _)

/-- **Eigenvectors of off-circle points are isotropic.** The eigenvector `δ_{β₀}` of the Frobenius
has Rosati form `m_{β₀}` if `β₀` is unitary and `0` otherwise: Weil's argument breaks exactly
where the anisotropy hypothesis of `normSq_eq_of_similitude` fails. -/
theorem rosatiForm_single {β₀ : ℂ} (hβ₀ : β₀ ∈ R.S) :
    R.rosatiForm (fun z => if z = β₀ then 1 else 0) =
      if ‖β₀‖ = 1 then (R.m β₀ : ℂ) else 0 := by
  classical
  have h0 := R.ne_zero_of_mem hβ₀
  rw [rosatiForm, Finset.sum_eq_single β₀]
  · by_cases hu : ‖β₀‖ = 1
    · simp [(refl_eq_self_iff h0).mpr hu, hu]
    · have hr : refl β₀ ≠ β₀ := fun h' => hu ((refl_eq_self_iff h0).mp h')
      simp [hr, hu]
  · intro z _ hz; simp [hz]
  · intro h; exact absurd hβ₀ h

/-- The **collided form** `D(x) = Σ_β m_β |x(β)|²` of the spectral model. -/
def collided (x : ℂ → ℂ) : ℝ := ∑ β ∈ R.S, R.m β * Complex.normSq (x β)

/-- The **off-circle defect** `Σ_β (m_β/2) |x(β) − x(1/β̄)|²`. -/
def defect (x : ℂ → ℂ) : ℝ := ∑ β ∈ R.S, R.m β / 2 * Complex.normSq (x β - x (refl β))

/-- **The Rosati form is the collided form minus the off-circle defect.** -/
theorem re_rosatiForm_eq_collided_sub_defect (x : ℂ → ℂ) :
    (R.rosatiForm x).re = R.collided x - R.defect x := by
  have hre : ∀ u v : ℂ, (conj u * v).re =
      (Complex.normSq u + Complex.normSq v - Complex.normSq (v - u)) / 2 := by
    intro u v
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.sub_re, Complex.sub_im]
    ring
  have hrefl : ∑ β ∈ R.S, R.m β * Complex.normSq (x (refl β)) =
      ∑ β ∈ R.S, R.m β * Complex.normSq (x β) := by
    refine Finset.sum_nbij' refl refl (fun β hβ => R.refl_mem β hβ) (fun β hβ => R.refl_mem β hβ)
      (fun β _ => refl_refl β) (fun β _ => refl_refl β) (fun β hβ => ?_)
    rw [R.m_refl β hβ]
  rw [rosatiForm, Complex.re_sum]
  simp only [mul_assoc, Complex.re_ofReal_mul, hre]
  rw [collided, defect]
  have : ∑ β ∈ R.S, R.m β * ((Complex.normSq (x (refl β)) + Complex.normSq (x β) -
      Complex.normSq (x β - x (refl β))) / 2) =
      (∑ β ∈ R.S, R.m β * Complex.normSq (x (refl β)) + ∑ β ∈ R.S, R.m β * Complex.normSq (x β)) / 2
        - ∑ β ∈ R.S, R.m β / 2 * Complex.normSq (x β - x (refl β)) := by
    rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    ring
  rw [this, hrefl]
  ring

/-- **The Frobenius preserves the collided form iff the spectrum is unitary**; it preserves the
Rosati form always (`frob_star_mul_frob`). -/
theorem collided_frob_invariant_iff_unitary :
    (∀ x : ℂ → ℂ, R.collided (fun β => β * x β) = R.collided x) ↔ ∀ β ∈ R.S, ‖β‖ = 1 := by
  classical
  constructor
  · intro h β₀ hβ₀
    have := h (fun z => if z = β₀ then 1 else 0)
    rw [collided, collided, Finset.sum_eq_single β₀, Finset.sum_eq_single β₀] at this
    · simp only [if_true, mul_one, Complex.normSq_one] at this
      have hm := R.m_pos β₀ hβ₀
      have h1 : Complex.normSq β₀ = 1 := mul_left_cancel₀ hm.ne' (this.trans (mul_one _).symm)
      rw [Complex.normSq_eq_norm_sq] at h1
      have := norm_nonneg β₀
      nlinarith
    all_goals first
      | (intro z _ hz; simp [hz])
      | (intro h'; exact absurd hβ₀ h')
  · intro hu x
    rw [collided, collided]
    refine Finset.sum_congr rfl fun β hβ => ?_
    rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq β, hu β hβ]
    ring

end ReflSpectrum

end GaloisForLFunctions.ArithmeticPolarization
