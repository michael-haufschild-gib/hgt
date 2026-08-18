import GaloisForLFunctions.RHTower.ProlatePhasedModeExpansion
import GaloisForLFunctions.RHTower.ConstrainedProlateRayleighRigidity

/-!
# The secular ground root is the leakage floor of a prolate sector

Renumbering the phase-normalized prolate modes along an injective index map `σ` produces an
orthonormal family of leakage eigenvectors whose leakage eigenvalues and constraint coordinates are
exactly the sequences `d_j = 1 − χ_{σ j}²` and `ℓ_j = ‖∫ h_{σ j}‖` for which the secular theory is
developed.  A complex expansion splits into its real and imaginary coordinate systems — the
constraint is one complex equation, hence two real ones — and this carries the coordinate Rayleigh
floor to the leakage operator itself:

```text
f = ∑ x_j h_{σ j} ,  ∫ f = 0   ⟹   re⟪B f, f⟫ ≥ μ₀ ‖f‖² ,
```

with `μ₀` the exact ground root of the sector's secular equation.  Equality forces both coordinate
systems onto the secular ray, so the floor is attained on a single complex line.
-/

noncomputable section

open Filter Set
open scoped InnerProduct InnerProductSpace

namespace RHTower

/-- The phase-normalized prolate family along an index map. -/
def sectorMode (a : ℝ) (σ : ℕ → ℕ) (j : ℕ) : evenSubspace := phasedSignedMode a (σ j)

/-- The leakage eigenvalues along the same index map. -/
def sectorLeakage (a : ℝ) (σ : ℕ → ℕ) (j : ℕ) : ℝ := evenProlateSignedLeakage a (σ j)

/-- The constraint coordinates along the same index map. -/
def sectorCoord (a : ℝ) (σ : ℕ → ℕ) (j : ℕ) : ℝ := ‖evenProlateConstraintCoord a (σ j)‖

theorem orthonormal_sectorMode {a : ℝ} (ha : 0 < a) {σ : ℕ → ℕ}
    (hσ : Function.Injective σ) : Orthonormal ℂ (sectorMode a σ) :=
  ⟨fun j => norm_phasedSignedMode ha (σ j),
    fun {_ _} hij => inner_phasedSignedMode_of_ne a fun h => hij (hσ h)⟩

theorem evenProlateLeakage_apply_sectorMode (a : ℝ) (σ : ℕ → ℕ) (j : ℕ) :
    evenProlateLeakage a (sectorMode a σ j)
      = ((sectorLeakage a σ j : ℝ) : ℂ) • sectorMode a σ j :=
  evenProlateLeakage_apply_phasedSignedMode a (σ j)

theorem inner_evenCentralIndicator_sectorMode (a : ℝ) (σ : ℕ → ℕ) (j : ℕ) :
    inner ℂ (evenCentralIndicator a) (sectorMode a σ j) = ((sectorCoord a σ j : ℝ) : ℂ) :=
  inner_evenCentralIndicator_phasedSignedMode a (σ j)

theorem sectorLeakage_nonneg (a : ℝ) (σ : ℕ → ℕ) (j : ℕ) : 0 ≤ sectorLeakage a σ j :=
  evenProlateSignedLeakage_nonneg a (σ j)

theorem sectorLeakage_le_one (a : ℝ) (σ : ℕ → ℕ) (j : ℕ) : sectorLeakage a σ j ≤ 1 :=
  evenProlateSignedLeakage_le_one a (σ j)

theorem summable_sectorCoord_sq (a : ℝ) {σ : ℕ → ℕ} (hσ : Function.Injective σ) :
    Summable fun j : ℕ => sectorCoord a σ j ^ 2 :=
  (summable_evenProlateConstraintCoord_sq a).comp_injective hσ

/-- **The two real coordinate systems of a sector expansion.**  Splitting the complex coefficients
into real and imaginary parts turns one complex constrained expansion into two real constrained
coordinate vectors whose squared norms and leakage forms add up to those of the vector. -/
theorem sector_real_parts {a : ℝ} (ha : 0 < a) {σ : ℕ → ℕ} (hσ : Function.Injective σ)
    {x : ℕ → ℂ} {f : evenSubspace}
    (hf : HasSum (fun j : ℕ => x j • sectorMode a σ j) f)
    (hcon : inner ℂ (evenCentralIndicator a) f = 0) :
    (Summable fun j : ℕ => (x j).re ^ 2) ∧ (Summable fun j : ℕ => (x j).im ^ 2) ∧
      (Summable fun j : ℕ => sectorLeakage a σ j * (x j).re ^ 2) ∧
      (Summable fun j : ℕ => sectorLeakage a σ j * (x j).im ^ 2) ∧
      (∑' j : ℕ, sectorCoord a σ j * (x j).re) = 0 ∧
      (∑' j : ℕ, sectorCoord a σ j * (x j).im) = 0 ∧
      (∑' j : ℕ, (x j).re ^ 2) + (∑' j : ℕ, (x j).im ^ 2) = ‖f‖ ^ 2 ∧
      (∑' j : ℕ, sectorLeakage a σ j * (x j).re ^ 2)
        + (∑' j : ℕ, sectorLeakage a σ j * (x j).im ^ 2)
        = (inner ℂ (evenProlateLeakage a f) f : ℂ).re := by
  classical
  set D : ℕ → ℝ := sectorLeakage a σ with hDdef
  set L : ℕ → ℝ := sectorCoord a σ with hLdef
  have hvon := orthonormal_sectorMode ha hσ
  have hns : HasSum (fun j : ℕ => ‖x j‖ ^ 2) (‖f‖ ^ 2) :=
    hasSum_norm_sq_of_hasSum_smul hvon hf
  have hls : HasSum (fun j : ℕ => D j * ‖x j‖ ^ 2)
      ((inner ℂ (evenProlateLeakage a f) f : ℂ).re) :=
    hasSum_leakage_of_hasSum_smul hvon (evenProlateLeakage_apply_sectorMode a σ) hf
  have hcs : HasSum (fun j : ℕ => x j * ((L j : ℝ) : ℂ)) 0 := by
    have h := hasSum_constraint_of_hasSum_smul (inner_evenCentralIndicator_sectorMode a σ) hf
    rwa [hcon] at h
  set u : ℕ → ℝ := fun j => (x j).re with hudef
  set w : ℕ → ℝ := fun j => (x j).im with hwdef
  have hnormsplit : ∀ j : ℕ, ‖x j‖ ^ 2 = u j ^ 2 + w j ^ 2 := by
    intro j
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hconu : (∑' j : ℕ, L j * u j) = 0 := by
    have h := Complex.reCLM.hasSum hcs
    simp only [Complex.reCLM_apply, Complex.zero_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, sub_zero] at h
    have heq : (fun j : ℕ => (x j).re * L j) = fun j : ℕ => L j * u j :=
      funext fun j => by rw [hudef]; ring
    rw [heq] at h
    exact h.tsum_eq
  have hconw : (∑' j : ℕ, L j * w j) = 0 := by
    have h := Complex.imCLM.hasSum hcs
    simp only [Complex.imCLM_apply, Complex.zero_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, mul_zero, zero_add] at h
    have heq : (fun j : ℕ => (x j).im * L j) = fun j : ℕ => L j * w j :=
      funext fun j => by rw [hwdef]; ring
    rw [heq] at h
    exact h.tsum_eq
  have hsu : Summable fun j : ℕ => u j ^ 2 :=
    Summable.of_nonneg_of_le (fun j => sq_nonneg _)
      (fun j => by rw [hnormsplit j]; linarith [sq_nonneg (w j)]) hns.summable
  have hsw : Summable fun j : ℕ => w j ^ 2 :=
    Summable.of_nonneg_of_le (fun j => sq_nonneg _)
      (fun j => by rw [hnormsplit j]; linarith [sq_nonneg (u j)]) hns.summable
  have hsdu : Summable fun j : ℕ => D j * u j ^ 2 :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (sectorLeakage_nonneg a σ j) (sq_nonneg _))
      (fun j => by
        have h1 := sectorLeakage_le_one a σ j
        nlinarith [sq_nonneg (u j)]) hsu
  have hsdw : Summable fun j : ℕ => D j * w j ^ 2 :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (sectorLeakage_nonneg a σ j) (sq_nonneg _))
      (fun j => by
        have h1 := sectorLeakage_le_one a σ j
        nlinarith [sq_nonneg (w j)]) hsw
  have e1 : (∑' j : ℕ, u j ^ 2) + (∑' j : ℕ, w j ^ 2) = ‖f‖ ^ 2 := by
    rw [← hns.tsum_eq, tsum_congr hnormsplit, Summable.tsum_add hsu hsw]
  have hsplit2 : ∀ j : ℕ, D j * ‖x j‖ ^ 2 = D j * u j ^ 2 + D j * w j ^ 2 := by
    intro j
    rw [hnormsplit j]
    ring
  have e2 : (∑' j : ℕ, D j * u j ^ 2) + (∑' j : ℕ, D j * w j ^ 2)
      = (inner ℂ (evenProlateLeakage a f) f : ℂ).re := by
    rw [← hls.tsum_eq, tsum_congr hsplit2, Summable.tsum_add hsdu hsdw]
  exact ⟨hsu, hsw, hsdu, hsdw, hconu, hconw, e1, e2⟩

/-- **The leakage floor of a prolate sector is the secular ground root.**  Every vector of the
sector annihilated by the integral functional has leakage form at least `μ₀‖f‖²`. -/
theorem sector_rayleigh_ge_infiniteSecularRoot {a : ℝ} (ha : 0 < a)
    {σ : ℕ → ℕ} (hσ : Function.Injective σ)
    (h01 : sectorLeakage a σ 0 < sectorLeakage a σ 1)
    (h12 : sectorLeakage a σ 1 < sectorLeakage a σ 2)
    (hd2 : ∀ j, sectorLeakage a σ 2 ≤ sectorLeakage a σ (j + 2))
    (hℓ0 : sectorCoord a σ 0 ≠ 0) (hℓ1 : sectorCoord a σ 1 ≠ 0)
    {x : ℕ → ℂ} {f : evenSubspace}
    (hf : HasSum (fun j : ℕ => x j • sectorMode a σ j) f)
    (hcon : inner ℂ (evenCentralIndicator a) f = 0) :
    infiniteSecularRoot (sectorLeakage a σ) (sectorCoord a σ) * ‖f‖ ^ 2
      ≤ (inner ℂ (evenProlateLeakage a f) f : ℂ).re := by
  obtain ⟨hsu, hsw, hsdu, hsdw, hconu, hconw, e1, e2⟩ := sector_real_parts ha hσ hf hcon
  have hsumL : Summable fun j : ℕ => sectorCoord a σ j ^ 2 := summable_sectorCoord_sq a hσ
  have hru := tsum_mul_sq_ge_infiniteSecularRoot h01 h12 hd2 hsumL hℓ0 hℓ1 hsu hsdu hconu
  have hrw := tsum_mul_sq_ge_infiniteSecularRoot h01 h12 hd2 hsumL hℓ0 hℓ1 hsw hsdw hconw
  rw [← e1, ← e2, mul_add]
  exact add_le_add hru hrw

/-- **Rigidity of the sector floor.**  A constrained vector of the sector attaining the floor has
coefficient vector on the complex secular ray. -/
theorem sector_coeff_eq_of_rayleigh_eq {a : ℝ} (ha : 0 < a)
    {σ : ℕ → ℕ} (hσ : Function.Injective σ)
    (h01 : sectorLeakage a σ 0 < sectorLeakage a σ 1)
    (h12 : sectorLeakage a σ 1 < sectorLeakage a σ 2)
    (hd2 : ∀ j, sectorLeakage a σ 2 ≤ sectorLeakage a σ (j + 2))
    (hℓ0 : sectorCoord a σ 0 ≠ 0) (hℓ1 : sectorCoord a σ 1 ≠ 0)
    {x : ℕ → ℂ} {f : evenSubspace}
    (hf : HasSum (fun j : ℕ => x j • sectorMode a σ j) f)
    (hcon : inner ℂ (evenCentralIndicator a) f = 0)
    (hval : (inner ℂ (evenProlateLeakage a f) f : ℂ).re
      = infiniteSecularRoot (sectorLeakage a σ) (sectorCoord a σ) * ‖f‖ ^ 2) :
    ∀ j : ℕ, x j
      = (x 0 / ((secularVector (sectorLeakage a σ) (sectorCoord a σ)
            (infiniteSecularRoot (sectorLeakage a σ) (sectorCoord a σ)) 0 : ℝ) : ℂ))
        * ((secularVector (sectorLeakage a σ) (sectorCoord a σ)
            (infiniteSecularRoot (sectorLeakage a σ) (sectorCoord a σ)) j : ℝ) : ℂ) := by
  obtain ⟨hsu, hsw, hsdu, hsdw, hconu, hconw, e1, e2⟩ := sector_real_parts ha hσ hf hcon
  set D : ℕ → ℝ := sectorLeakage a σ with hDdef
  set L : ℕ → ℝ := sectorCoord a σ with hLdef
  set μ := infiniteSecularRoot D L with hμdef
  set v : ℕ → ℝ := secularVector D L μ with hvdef
  have hsumL : Summable fun j : ℕ => L j ^ 2 := summable_sectorCoord_sq a hσ
  have hru := tsum_mul_sq_ge_infiniteSecularRoot h01 h12 hd2 hsumL hℓ0 hℓ1 hsu hsdu hconu
  have hrw := tsum_mul_sq_ge_infiniteSecularRoot h01 h12 hd2 hsumL hℓ0 hℓ1 hsw hsdw hconw
  have htotal : μ * ((∑' j : ℕ, (x j).re ^ 2) + (∑' j : ℕ, (x j).im ^ 2))
      = (∑' j : ℕ, D j * (x j).re ^ 2) + (∑' j : ℕ, D j * (x j).im ^ 2) := by
    rw [e1, e2, hval]
  have hequ : μ * ∑' j : ℕ, (x j).re ^ 2 = ∑' j : ℕ, D j * (x j).re ^ 2 := by
    nlinarith [hru, hrw, htotal]
  have heqw : μ * ∑' j : ℕ, (x j).im ^ 2 = ∑' j : ℕ, D j * (x j).im ^ 2 := by
    nlinarith [hru, hrw, htotal]
  have hu := eq_smul_secularVector_of_rayleigh_eq h01 h12 hd2 hsumL hℓ0 hℓ1 hsu hsdu hconu hequ
  have hw := eq_smul_secularVector_of_rayleigh_eq h01 h12 hd2 hsumL hℓ0 hℓ1 hsw hsdw hconw heqw
  have hv0 : v 0 ≠ 0 := by
    obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsumL hℓ0 hℓ1
    rw [hvdef, secularVector]
    exact div_ne_zero hℓ0 (sub_ne_zero.mpr (ne_of_lt hrmem.1))
  intro j
  have hxj : x j = (((x j).re : ℝ) : ℂ) + (((x j).im : ℝ) : ℂ) * Complex.I :=
    (Complex.re_add_im (x j)).symm
  have hx0 : x 0 = (((x 0).re : ℝ) : ℂ) + (((x 0).im : ℝ) : ℂ) * Complex.I :=
    (Complex.re_add_im (x 0)).symm
  rw [hxj, hx0, hu j, hw j, hu 0, hw 0]
  have hv0c : ((v 0 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv0
  push_cast
  field_simp
  ring

end RHTower

end
