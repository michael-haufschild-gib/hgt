import Mathlib

/-!
# Ihara quadratic block selector

This file is a deliberately finite proof lab, not a formalization of Ihara zeta
theory.  The model is the nontrivial quadratic factor

`P_lambda(u) = 1 - lambda u + q u^2`

appearing in the regular-graph Ihara determinant formula.  It isolates the
selector shape relevant to RH analogies:

* reciprocal functional-equation symmetry is automatic for every block;
* zeros on the critical circle are equivalent to the spectral bound
  `lambda^2 <= 4q`;
* a finite product satisfies the model RH exactly when the total off-circle
  index is zero;
* reciprocal symmetry alone does not force the selector.
-/

open scoped BigOperators ComplexOrder

namespace GaloisForLFunctions

noncomputable section

/-- The reciprocal quadratic block `1 - lambda u + q u^2`. -/
def iharaBlock (q lambda : ℝ) (u : ℂ) : ℂ :=
  1 - (lambda : ℂ) * u + (q : ℂ) * u ^ 2

/-- All zeros of the block lie on the circle with squared radius `q^{-1}`. -/
def zerosOnCriticalCircle (q lambda : ℝ) : Prop :=
  ∀ u : ℂ, iharaBlock q lambda u = 0 → Complex.normSq u = q⁻¹

/-- The spectral selector for one Ihara block. -/
def blockSpectralBound (q lambda : ℝ) : Prop :=
  lambda ^ 2 ≤ 4 * q

/-- One block contributes one unit of off-circle index exactly when the spectral selector fails. -/
def blockOffCircleIndex (q lambda : ℝ) : ℕ :=
  by
    classical
    exact if blockSpectralBound q lambda then 0 else 1

/-- The reciprocal functional-equation identity of the quadratic block. -/
theorem iharaBlock_reciprocal_identity {q lambda : ℝ} (hq : q ≠ 0) {u : ℂ} (hu : u ≠ 0) :
    (q : ℂ) * u ^ 2 * iharaBlock q lambda (((q : ℂ) * u)⁻¹) =
      iharaBlock q lambda u := by
  unfold iharaBlock
  field_simp [hq, hu]
  ring

/-- Imaginary-part equation for a zero of an Ihara block. -/
lemma iharaBlock_im_eq_zero (q lambda : ℝ) (u : ℂ) (h : iharaBlock q lambda u = 0) :
    u.im * (2 * q * u.re - lambda) = 0 := by
  have him := congrArg Complex.im h
  simp [iharaBlock, pow_two, Complex.mul_re, Complex.mul_im] at him
  ring_nf at him ⊢
  exact him

/-- Real-part equation for a zero of an Ihara block. -/
lemma iharaBlock_re_eq_zero (q lambda : ℝ) (u : ℂ) (h : iharaBlock q lambda u = 0) :
    1 - lambda * u.re + q * (u.re ^ 2 - u.im ^ 2) = 0 := by
  have hre := congrArg Complex.re h
  simp [iharaBlock, pow_two, Complex.mul_re, Complex.mul_im] at hre
  ring_nf at hre ⊢
  exact hre

private lemma eq_inv_of_mul_eq_one {q r : ℝ} (hq : q ≠ 0) (h : q * r = 1) :
    r = q⁻¹ := by
  calc
    r = q⁻¹ * (q * r) := by field_simp [hq]
    _ = q⁻¹ := by rw [h, mul_one]

/-- The spectral bound forces the actual zeros of the quadratic block onto the critical circle. -/
theorem zerosOnCriticalCircle_of_spectral_bound {q lambda : ℝ} (hq : 0 < q)
    (hdisc : blockSpectralBound q lambda) : zerosOnCriticalCircle q lambda := by
  intro u hu
  have him := iharaBlock_im_eq_zero q lambda u hu
  have hre0 := iharaBlock_re_eq_zero q lambda u hu
  rw [Complex.normSq_apply]
  rcases mul_eq_zero.mp him with huy | hx
  · rw [huy] at hre0 ⊢
    ring_nf at hre0 ⊢
    have hpoly : q * u.re ^ 2 - lambda * u.re + 1 = 0 := by linarith
    have hsq : (2 * q * u.re - lambda) ^ 2 = lambda ^ 2 - 4 * q := by
      nlinarith [hpoly]
    have hsq_nonneg : 0 ≤ (2 * q * u.re - lambda) ^ 2 := sq_nonneg _
    have hsq_le_zero : (2 * q * u.re - lambda) ^ 2 ≤ 0 := by
      dsimp [blockSpectralBound] at hdisc
      linarith
    have hx0 : 2 * q * u.re - lambda = 0 := by nlinarith
    have hnorm : q * u.re ^ 2 = 1 := by nlinarith [hpoly, hx0]
    exact eq_inv_of_mul_eq_one (ne_of_gt hq) hnorm
  · ring_nf at hre0 hx ⊢
    have h1 : 1 = lambda * u.re - q * u.re ^ 2 + q * u.im ^ 2 := by linarith
    have hlambda : lambda = 2 * q * u.re := by linarith
    have h2 : lambda * u.re = 2 * q * u.re ^ 2 := by
      rw [hlambda]
      ring
    have hnorm : q * (u.re ^ 2 + u.im ^ 2) = 1 := by nlinarith [h1, h2]
    exact eq_inv_of_mul_eq_one (ne_of_gt hq) hnorm

/-- If the spectral bound fails, an explicit real zero lies off the critical circle. -/
theorem not_zerosOnCriticalCircle_of_spectral_violation {q lambda : ℝ} (hq : 0 < q)
    (hbad : 4 * q < lambda ^ 2) : ¬ zerosOnCriticalCircle q lambda := by
  intro hcircle
  let D : ℝ := lambda ^ 2 - 4 * q
  let s : ℝ := Real.sqrt D
  let r : ℝ := (lambda + s) / (2 * q)
  have hDpos : 0 < D := by
    dsimp [D]
    linarith
  have hspos : 0 < s := by
    dsimp [s]
    exact Real.sqrt_pos_of_pos hDpos
  have hs2 : s ^ 2 = D := by
    dsimp [s]
    exact Real.sq_sqrt hDpos.le
  have htwoq : 2 * q ≠ 0 := by nlinarith [hq]
  have hroot_real : 1 - lambda * r + q * r ^ 2 = 0 := by
    dsimp [r]
    field_simp [htwoq, ne_of_gt hq]
    dsimp [D] at hs2
    nlinarith [hs2]
  have hroot_real' : 1 - lambda * r + q * (r * r) = 0 := by nlinarith [hroot_real]
  have hroot : iharaBlock q lambda (r : ℂ) = 0 := by
    apply Complex.ext
    · simp [iharaBlock, pow_two, hroot_real']
    · simp [iharaBlock, pow_two]
  have hnorm := hcircle (r : ℂ) hroot
  rw [Complex.normSq_ofReal] at hnorm
  have hnormsq : r ^ 2 = q⁻¹ := by simpa [pow_two] using hnorm
  have hqr : q * r ^ 2 = 1 := by
    rw [hnormsq]
    exact mul_inv_cancel₀ (ne_of_gt hq)
  have hlambdar : lambda * r = 2 := by nlinarith [hroot_real, hqr]
  have htwor : 2 * q * r = lambda + s := by
    dsimp [r]
    field_simp [htwoq]
  have hs_mul_r : s * r = 0 := by nlinarith [hqr, hlambdar, htwor]
  have hr0 : r = 0 := by
    exact (mul_eq_zero.mp hs_mul_r).resolve_left (ne_of_gt hspos)
  rw [hr0] at hqr
  norm_num at hqr

/-- The exact one-block selector: critical-circle zeros iff the spectral bound holds. -/
theorem zerosOnCriticalCircle_iff_spectral_bound {q lambda : ℝ} (hq : 0 < q) :
    zerosOnCriticalCircle q lambda ↔ blockSpectralBound q lambda := by
  constructor
  · intro hcircle
    by_contra hbound
    exact not_zerosOnCriticalCircle_of_spectral_violation hq (lt_of_not_ge hbound) hcircle
  · exact zerosOnCriticalCircle_of_spectral_bound hq

/-- The total off-circle index of a finite family of blocks. -/
def totalOffCircleIndex {ι : Type*} [Fintype ι] (q : ℝ) (lambda : ι → ℝ) : ℕ :=
  ∑ i, blockOffCircleIndex q (lambda i)

/-- A finite family of blocks satisfies the model RH when every block has critical-circle zeros. -/
def finiteBlockRH {ι : Type*} (q : ℝ) (lambda : ι → ℝ) : Prop :=
  ∀ i, zerosOnCriticalCircle q (lambda i)

theorem blockOffCircleIndex_eq_zero_iff (q lambda : ℝ) :
    blockOffCircleIndex q lambda = 0 ↔ blockSpectralBound q lambda := by
  by_cases h : blockSpectralBound q lambda <;> simp [blockOffCircleIndex, h]

/-- Finite product selector: model RH iff the total off-circle index vanishes. -/
theorem finiteBlockRH_iff_totalOffCircleIndex_eq_zero {ι : Type*} [Fintype ι]
    {q : ℝ} (hq : 0 < q) (lambda : ι → ℝ) :
    finiteBlockRH q lambda ↔ totalOffCircleIndex q lambda = 0 := by
  constructor
  · intro hcritical
    rw [totalOffCircleIndex, Finset.sum_eq_zero_iff]
    intro i _
    exact (blockOffCircleIndex_eq_zero_iff q (lambda i)).2
      ((zerosOnCriticalCircle_iff_spectral_bound hq).1 (hcritical i))
  · intro hindex i
    rw [totalOffCircleIndex, Finset.sum_eq_zero_iff] at hindex
    exact (zerosOnCriticalCircle_iff_spectral_bound hq).2
      ((blockOffCircleIndex_eq_zero_iff q (lambda i)).1 (hindex i (Finset.mem_univ i)))

/-- Reciprocal symmetry alone cannot force the spectral selector. -/
theorem reciprocal_identity_does_not_force_spectral_bound (q : ℝ) (hq : 0 < q) :
    ∃ lambda : ℝ,
      (∀ u : ℂ, u ≠ 0 →
        (q : ℂ) * u ^ 2 * iharaBlock q lambda (((q : ℂ) * u)⁻¹) =
          iharaBlock q lambda u) ∧
      ¬ blockSpectralBound q lambda := by
  refine ⟨3 * (q + 1), ?_, ?_⟩
  · intro u hu
    exact iharaBlock_reciprocal_identity (ne_of_gt hq) hu
  · dsimp [blockSpectralBound]
    nlinarith [sq_nonneg q, hq]

end

end GaloisForLFunctions
