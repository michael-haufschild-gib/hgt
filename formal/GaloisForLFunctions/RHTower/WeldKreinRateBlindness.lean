import GaloisForLFunctions.RHTower.WeldPolarizationDirection
import GaloisForLFunctions.RHTower.PrimeDivisorAtomsNoGo

/-!
# FE-weld rate blindness and the finite-source activation obstruction

The functional-equation twist turns every nonzero scalar weld into a hyperbolic Krein plane.  This
module separates the universal **shape** of that plane from arithmetic **activation**.

First, all positive-rate FE weld Grams are related by an invertible congruence.  In particular the
Krein isometry class forgets the numerical prime rate `log p`: every prime supplies the same local
hyperbolic plane up to scale.  Second, a scalar multiple of a nonzero rate is Krein-nonnegative
exactly when the scalar is zero.  Thus nonnegativity sees only whether a local block is activated,
not which prime rate it carries.

The existing pinned `SigmaSourceMap` then gives a decisive obstruction.  Since every finite local
Euler factor is a unit at a strip point, every source count is zero.  Consequently every FE block
activated by such a source map is the zero matrix, even at a zero of `xi`, where the analytic order
is nonzero.  A finite prime-sourced FE block therefore cannot be the divisor block: its hyperbolic
shape is universal background geometry, while the required arithmetic activation is absent.

The obstruction is not specific to `SigmaSourceMap`.  The simultaneous profile of every individual
Euler-factor order and the archimedean-factor order is the zero profile throughout the right
half-plane.  Hence no zero-preserving function of that entire factorwise profile can recover the
nonzero completed order at a `xi`-zero.  Any surviving completed obstruction must contain genuinely
non-factorwise extension data.
-/

open Complex Matrix GaloisForLFunctions

noncomputable section
namespace GaloisForLFunctions.RHTower

/-- Scalar change of basis carrying the positive rate `η` to the positive rate `θ`. -/
def weldRateCongruence (θ η : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Real.sqrt (θ / η) : ℝ) : ℂ) • 1

/-- The positive-rate change of scale is invertible. -/
theorem weldRateCongruence_det_ne_zero {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) :
    Matrix.det (weldRateCongruence θ η) ≠ 0 := by
  have hsqrt : Real.sqrt (θ / η) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (div_pos hθ hη))
  simp [weldRateCongruence, hsqrt]

/-- **Positive-rate blindness.**  Every two positive FE weld blocks are invertibly congruent. -/
theorem weldFEKreinGram_congr_of_pos {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) :
    (weldRateCongruence θ η)ᴴ * weldFEKreinGram η * weldRateCongruence θ η =
      weldFEKreinGram θ := by
  have hratio : 0 ≤ θ / η := div_nonneg hθ.le hη.le
  have hsqrt : (Real.sqrt (θ / η)) ^ 2 = θ / η := Real.sq_sqrt hratio
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weldRateCongruence, weldFEKreinGram, Matrix.mul_apply]
  all_goals norm_cast
  all_goals
    calc
      Real.sqrt (θ / η) * η * Real.sqrt (θ / η) =
          (Real.sqrt (θ / η)) ^ 2 * η := by ring
      _ = (θ / η) * η := by rw [hsqrt]
      _ = θ := by field_simp

/-- The FE weld block is Krein-nonnegative exactly at zero rate. -/
theorem weldFEKreinGram_kreinNonneg_iff (θ : ℝ) :
    _root_.RHTower.KreinNonneg (weldFEKreinGram θ) ↔ θ = 0 := by
  constructor
  · intro h
    by_contra hzero
    rcases lt_or_gt_of_ne hzero with hneg | hpos
    · have hbad := h ![(1 : ℂ), 1]
      simp [weldFEKreinGram, dotProduct] at hbad
      linarith
    · exact weldFEKreinGram_not_kreinNonneg hpos h
  · rintro rfl
    intro x
    simp [weldFEKreinGram, dotProduct]

/-- A nonzero base rate turns scalar activation into an exact zero/nonzero gate. -/
theorem scaled_weldFEKreinGram_kreinNonneg_iff {θ : ℝ} (hθ : θ ≠ 0) (a : ℝ) :
    _root_.RHTower.KreinNonneg (weldFEKreinGram (a * θ)) ↔ a = 0 := by
  rw [weldFEKreinGram_kreinNonneg_iff, mul_eq_zero]
  simp [hθ]

/-- For every integer `p ≥ 2`, the logarithmic weld block is nonnegative exactly when its
activation coefficient vanishes. -/
theorem scaled_nat_weldFEKreinGram_kreinNonneg_iff {p : ℕ} (hp : 2 ≤ p) (a : ℝ) :
    _root_.RHTower.KreinNonneg (weldFEKreinGram (a * Real.log p)) ↔ a = 0 := by
  apply scaled_weldFEKreinGram_kreinNonneg_iff
  exact ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < p by omega)))

/-- Every prime FE weld block has a negative direction. -/
theorem prime_weldFEKreinGram_not_kreinNonneg {p : ℕ} (hp : p.Prime) :
    ¬_root_.RHTower.KreinNonneg (weldFEKreinGram (Real.log p)) :=
  weldFEKreinGram_not_kreinNonneg (Real.log_pos (by exact_mod_cast hp.one_lt))

/-- The FE weld blocks of any two primes are invertibly congruent. -/
theorem prime_weldFEKreinGram_congr {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (weldRateCongruence (Real.log p) (Real.log q))ᴴ *
        weldFEKreinGram (Real.log q) * weldRateCongruence (Real.log p) (Real.log q) =
      weldFEKreinGram (Real.log p) :=
  weldFEKreinGram_congr_of_pos
    (Real.log_pos (by exact_mod_cast hp.one_lt))
    (Real.log_pos (by exact_mod_cast hq.one_lt))

/-- A pinned prime source map activates no FE weld block: each local source count is zero. -/
theorem sigmaSourceMap_weldFEKreinGram_zero {A : ℕ → ℕ} {ρ : ℂ} (hs : 0 < ρ.re)
    (hA : _root_.RHTower.SigmaSourceMap A ρ) :
    ∀ p, 2 ≤ p → weldFEKreinGram ((A p : ℝ) * Real.log p) = 0 := by
  intro p hp
  have hzero := _root_.RHTower.sigma_source_map_trivial hs hA p hp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hzero, weldFEKreinGram]

/-- **Finite-source activation obstruction.**  At a `xi`-zero every finite prime-sourced FE block
is zero while the `xi`-divisor order is nonzero. -/
theorem sigmaSourceMap_weldFEKrein_divisor_mismatch {A : ℕ → ℕ} {ρ : ℂ}
    (hs : 0 < ρ.re) (hz : _root_.RHTower.xi ρ = 0)
    (hA : _root_.RHTower.SigmaSourceMap A ρ) :
    (∀ p, 2 ≤ p → weldFEKreinGram ((A p : ℝ) * Real.log p) = 0) ∧
      analyticOrderAt _root_.RHTower.xi ρ ≠ 0 :=
  ⟨sigmaSourceMap_weldFEKreinGram_zero hs hA,
    _root_.RHTower.xi_zero_order_ne_zero hz⟩

/-- The complete factorwise divisor-order datum: all individual Euler-factor orders together with
the archimedean-factor order. -/
abbrev FactorwiseWeldOrderProfile := (ℕ → ℕ∞) × ℕ∞

/-- The pinned profile of all individual prime-factor orders and the archimedean-factor order. -/
def factorwiseWeldOrderProfile (ρ : ℂ) : FactorwiseWeldOrderProfile :=
  (fun p => if 2 ≤ p then
      analyticOrderAt (fun z => (1 - (p : ℂ) ^ (-z))⁻¹) ρ
    else 0,
   analyticOrderAt _root_.RHTower.archimedeanFactor ρ)

/-- The entire factorwise prime-plus-archimedean order profile is zero on the right half-plane. -/
theorem factorwiseWeldOrderProfile_eq_zero {ρ : ℂ} (hs : 0 < ρ.re) :
    factorwiseWeldOrderProfile ρ = 0 := by
  apply Prod.ext
  · funext p
    by_cases hp : 2 ≤ p
    · simp [factorwiseWeldOrderProfile, hp,
        _root_.RHTower.eulerInvFactor_orderAt_zero hp hs]
    · simp [factorwiseWeldOrderProfile, hp]
  · simp [factorwiseWeldOrderProfile, _root_.RHTower.archimedeanFactor_orderAt_zero hs]

/-- **No factorwise divisor assembler.**  At a `xi`-zero, no zero-preserving function of all local
Euler-factor orders and the archimedean order can recover the completed divisor order. -/
theorem no_factorwiseWeldOrderAssembler_at_xi_zero {ρ : ℂ} (hs : 0 < ρ.re)
    (hz : _root_.RHTower.xi ρ = 0) :
    ¬ ∃ assemble : FactorwiseWeldOrderProfile → ℕ∞,
        assemble 0 = 0 ∧
          assemble (factorwiseWeldOrderProfile ρ) =
            analyticOrderAt _root_.RHTower.xi ρ := by
  rintro ⟨assemble, hzero, hrecover⟩
  rw [factorwiseWeldOrderProfile_eq_zero hs, hzero] at hrecover
  exact _root_.RHTower.xi_zero_order_ne_zero hz hrecover.symm

end GaloisForLFunctions.RHTower
