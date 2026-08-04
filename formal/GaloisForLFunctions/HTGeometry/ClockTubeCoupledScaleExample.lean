import GaloisForLFunctions.HTGeometry.ClockMultiDimensionalScaleLaw
import GaloisForLFunctions.HTGeometry.ClockTubePotentialAlgebra
import GaloisForLFunctions.HTGeometry.ClockCoupledScaleExample

/-!
# A scale function coupling several transverse coordinates

The two-species law of the previous chapter asks that the effective potential of the scale be of the
admissible class on a tube. This file exhibits a scale for which it is:

`σ(ξ, η, y) = ε sin(ξ + η + y¹ + ⋯ + yᵏ)`.

It depends on all the coordinates through their sum, so it is neither a slab scale nor a separable
one in any of them, and it is bounded together with all its derivatives.

Its derivative array is small: every first derivative is `ε cos(ξ + η + ∑ yⁱ)` and every second
derivative is `-ε sin(ξ + η + ∑ yⁱ)`, so the two differentiability records below carry the whole
two-jet.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric

open scoped ContDiff

variable {k : ℕ}

/-- The coupled scale `ε sin(ξ + η + ∑ yⁱ)`. -/
noncomputable def coupledScaleMulti (ε : ℝ) : ℝ → ℝ → (Fin k → ℝ) → ℝ :=
  fun s t y => ε * Real.sin (s + t + ∑ i, y i)

/-- Its common first derivative. -/
noncomputable def coupledScaleMultiD (ε : ℝ) : ℝ → ℝ → (Fin k → ℝ) → ℝ :=
  fun s t y => ε * Real.cos (s + t + ∑ i, y i)

/-- Its common second derivative. -/
noncomputable def coupledScaleMultiDD (ε : ℝ) : ℝ → ℝ → (Fin k → ℝ) → ℝ :=
  fun s t y => -(ε * Real.sin (s + t + ∑ i, y i))

theorem continuous_realTransverseSum : Continuous fun y : Fin k → ℝ => ∑ i, y i :=
  continuous_finsetSum Finset.univ fun i _ => continuous_apply i

theorem continuous_coupledScaleMulti (ε : ℝ) :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => coupledScaleMulti ε q.1.1 q.1.2 q.2 :=
  continuous_const.mul (Real.continuous_sin.comp
    (((continuous_fst.comp continuous_fst).add (continuous_snd.comp continuous_fst)).add
      (continuous_realTransverseSum.comp continuous_snd)))

theorem continuous_coupledScaleMultiD (ε : ℝ) :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => coupledScaleMultiD ε q.1.1 q.1.2 q.2 :=
  continuous_const.mul (Real.continuous_cos.comp
    (((continuous_fst.comp continuous_fst).add (continuous_snd.comp continuous_fst)).add
      (continuous_realTransverseSum.comp continuous_snd)))

theorem continuous_coupledScaleMultiDD (ε : ℝ) :
    Continuous fun q : (ℝ × ℝ) × (Fin k → ℝ) => coupledScaleMultiDD ε q.1.1 q.1.2 q.2 :=
  (continuous_const.mul (Real.continuous_sin.comp
    (((continuous_fst.comp continuous_fst).add (continuous_snd.comp continuous_fst)).add
      (continuous_realTransverseSum.comp continuous_snd)))).neg

/-- Updating one transverse coordinate shifts the transverse sum. -/
theorem sum_update_eq (y : Fin k → ℝ) (i : Fin k) (a : ℝ) :
    ∑ j, Function.update y i a j = a + ∑ j ∈ Finset.univ \ {i}, y j := by
  classical
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]

theorem sum_eq_add_compl (y : Fin k → ℝ) (i : Fin k) :
    ∑ j, y j = y i + ∑ j ∈ Finset.univ \ {i}, y j := by
  classical
  have h := sum_update_eq y i (y i)
  rwa [Function.update_eq_self] at h

/-- **The coupled scale is continuously differentiable in all its coordinates**, with all
derivatives equal. -/
theorem isC1OnMulti_coupledScaleMulti (ε : ℝ) :
    IsC1OnMulti (coupledScaleMulti (k := k) ε) (coupledScaleMultiD ε) (coupledScaleMultiD ε)
      (fun _ => coupledScaleMultiD ε) univ where
  isOpen := isOpen_univ
  hasDerivFst := fun q _ => by
    have hEq : (fun x : ℝ => coupledScaleMulti ε x q.1.2 q.2)
        = fun x : ℝ => ε * Real.sin (x + (q.1.2 + ∑ i, q.2 i)) := by
      funext x
      rw [coupledScaleMulti, add_assoc]
    rw [hEq]
    have h := ((Real.hasDerivAt_sin (q.1.1 + (q.1.2 + ∑ i, q.2 i))).comp_add_const q.1.1
      (q.1.2 + ∑ i, q.2 i)).const_mul ε
    have hval : ε * Real.cos (q.1.1 + (q.1.2 + ∑ i, q.2 i))
        = coupledScaleMultiD ε q.1.1 q.1.2 q.2 := by
      rw [coupledScaleMultiD, add_assoc]
    rwa [hval] at h
  hasDerivSnd := fun q _ => by
    have hEq : (fun x : ℝ => coupledScaleMulti ε q.1.1 x q.2)
        = fun x : ℝ => ε * Real.sin (x + (q.1.1 + ∑ i, q.2 i)) := by
      funext x
      rw [coupledScaleMulti, show q.1.1 + x + ∑ i, q.2 i = x + (q.1.1 + ∑ i, q.2 i) from by ring]
    rw [hEq]
    have h := ((Real.hasDerivAt_sin (q.1.2 + (q.1.1 + ∑ i, q.2 i))).comp_add_const q.1.2
      (q.1.1 + ∑ i, q.2 i)).const_mul ε
    have hval : ε * Real.cos (q.1.2 + (q.1.1 + ∑ i, q.2 i))
        = coupledScaleMultiD ε q.1.1 q.1.2 q.2 := by
      rw [coupledScaleMultiD,
        show q.1.2 + (q.1.1 + ∑ i, q.2 i) = q.1.1 + q.1.2 + ∑ i, q.2 i from by ring]
    rwa [hval] at h
  hasDerivTrans := fun q _ i => by
    classical
    set c : ℝ := ∑ j ∈ Finset.univ \ {i}, q.2 j with hc
    have hEq : (fun a : ℝ => coupledScaleMulti ε q.1.1 q.1.2 (Function.update q.2 i a))
        = fun a : ℝ => ε * Real.sin (a + (q.1.1 + q.1.2 + c)) := by
      funext a
      rw [coupledScaleMulti, sum_update_eq, hc]
      congr 2
      ring
    rw [hEq]
    have h := ((Real.hasDerivAt_sin (q.2 i + (q.1.1 + q.1.2 + c))).comp_add_const (q.2 i)
      (q.1.1 + q.1.2 + c)).const_mul ε
    have hval : ε * Real.cos (q.2 i + (q.1.1 + q.1.2 + c))
        = coupledScaleMultiD ε q.1.1 q.1.2 q.2 := by
      rw [coupledScaleMultiD]
      congr 2
      rw [sum_eq_add_compl q.2 i, hc]
      ring
    rwa [hval] at h
  contFst := continuous_coupledScaleMultiD ε
  contSnd := continuous_coupledScaleMultiD ε
  contTrans := fun _ => continuous_coupledScaleMultiD ε

/-- **The first derivative of the coupled scale is again continuously differentiable**, with all
derivatives equal. -/
theorem isC1OnMulti_coupledScaleMultiD (ε : ℝ) :
    IsC1OnMulti (coupledScaleMultiD (k := k) ε) (coupledScaleMultiDD ε) (coupledScaleMultiDD ε)
      (fun _ => coupledScaleMultiDD ε) univ where
  isOpen := isOpen_univ
  hasDerivFst := fun q _ => by
    have hEq : (fun x : ℝ => coupledScaleMultiD ε x q.1.2 q.2)
        = fun x : ℝ => ε * Real.cos (x + (q.1.2 + ∑ i, q.2 i)) := by
      funext x
      rw [coupledScaleMultiD, add_assoc]
    rw [hEq]
    have h := ((Real.hasDerivAt_cos (q.1.1 + (q.1.2 + ∑ i, q.2 i))).comp_add_const q.1.1
      (q.1.2 + ∑ i, q.2 i)).const_mul ε
    have hval : ε * -Real.sin (q.1.1 + (q.1.2 + ∑ i, q.2 i))
        = coupledScaleMultiDD ε q.1.1 q.1.2 q.2 := by
      rw [coupledScaleMultiDD, add_assoc]
      ring
    rwa [hval] at h
  hasDerivSnd := fun q _ => by
    have hEq : (fun x : ℝ => coupledScaleMultiD ε q.1.1 x q.2)
        = fun x : ℝ => ε * Real.cos (x + (q.1.1 + ∑ i, q.2 i)) := by
      funext x
      rw [coupledScaleMultiD,
        show q.1.1 + x + ∑ i, q.2 i = x + (q.1.1 + ∑ i, q.2 i) from by ring]
    rw [hEq]
    have h := ((Real.hasDerivAt_cos (q.1.2 + (q.1.1 + ∑ i, q.2 i))).comp_add_const q.1.2
      (q.1.1 + ∑ i, q.2 i)).const_mul ε
    have hval : ε * -Real.sin (q.1.2 + (q.1.1 + ∑ i, q.2 i))
        = coupledScaleMultiDD ε q.1.1 q.1.2 q.2 := by
      rw [coupledScaleMultiDD,
        show q.1.2 + (q.1.1 + ∑ i, q.2 i) = q.1.1 + q.1.2 + ∑ i, q.2 i from by ring]
      ring
    rwa [hval] at h
  hasDerivTrans := fun q _ i => by
    classical
    set c : ℝ := ∑ j ∈ Finset.univ \ {i}, q.2 j with hc
    have hEq : (fun a : ℝ => coupledScaleMultiD ε q.1.1 q.1.2 (Function.update q.2 i a))
        = fun a : ℝ => ε * Real.cos (a + (q.1.1 + q.1.2 + c)) := by
      funext a
      rw [coupledScaleMultiD, sum_update_eq, hc]
      congr 2
      ring
    rw [hEq]
    have h := ((Real.hasDerivAt_cos (q.2 i + (q.1.1 + q.1.2 + c))).comp_add_const (q.2 i)
      (q.1.1 + q.1.2 + c)).const_mul ε
    have hval : ε * -Real.sin (q.2 i + (q.1.1 + q.1.2 + c))
        = coupledScaleMultiDD ε q.1.1 q.1.2 q.2 := by
      rw [coupledScaleMultiDD]
      have harg : q.2 i + (q.1.1 + q.1.2 + c) = q.1.1 + q.1.2 + ∑ j, q.2 j := by
        rw [sum_eq_add_compl q.2 i, hc]
        ring
      rw [harg]
      ring
    rwa [hval] at h
  contFst := continuous_coupledScaleMultiDD ε
  contSnd := continuous_coupledScaleMultiDD ε
  contTrans := fun _ => continuous_coupledScaleMultiDD ε

/-- The lift of the coupled scale is smooth. -/
theorem contDiff_nullMultiLift_coupledScaleMulti (ε : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (nullMultiLift (coupledScaleMulti (k := k) ε) n) := by
  have hcoord : ∀ j : Fin (k + n + 2), ContDiff ℝ ∞ fun x : Fin (k + n + 2) → ℝ => x j :=
    fun j => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (k + n + 2) => ℝ) j).contDiff
  have hsum : ContDiff ℝ ∞ fun x : Fin (k + n + 2) → ℝ =>
      ∑ i : Fin k, x (transIdx k n i) :=
    ContDiff.sum fun i _ => hcoord (transIdx k n i)
  have hlin : ContDiff ℝ ∞ fun x : Fin (k + n + 2) → ℝ =>
      (x 0 + x 1) + (x 0 - x 1) + ∑ i : Fin k, x (transIdx k n i) :=
    (((hcoord 0).add (hcoord 1)).add ((hcoord 0).sub (hcoord 1))).add hsum
  exact contDiff_const.mul (Real.contDiff_sin.comp hlin)

/-! ## The complexified effective potential -/

/-- The complexified sine of the coupled argument. -/
noncomputable def coupledMultiSin (ε : ℝ) : ℝ → ℝ → (Fin k → ℂ) → ℂ :=
  fun s t z => ((ε : ℝ) : ℂ) * Complex.sin ((s : ℂ) + (t : ℂ) + ∑ i, z i)

/-- The complexified cosine of the coupled argument. -/
noncomputable def coupledMultiCos (ε : ℝ) : ℝ → ℝ → (Fin k → ℂ) → ℂ :=
  fun s t z => ((ε : ℝ) : ℂ) * Complex.cos ((s : ℂ) + (t : ℂ) + ∑ i, z i)

/-- The complexified effective potential of the coupled scale. -/
noncomputable def coupledMultiPotential (k : ℕ) (a massSq ε : ℝ) :
    ℝ → ℝ → (Fin k → ℂ) → ℂ :=
  fun s t z => ((massSq : ℝ) : ℂ) * Complex.exp (2 * coupledMultiSin ε s t z)
    + ((a * ((k : ℝ) - 4) : ℝ) : ℂ) * coupledMultiSin ε s t z
    - ((a ^ 2 * ((k : ℝ) - 4) : ℝ) : ℂ)
      * (coupledMultiCos ε s t z * coupledMultiCos ε s t z)

theorem abs_im_coupledArg {ρ : ℝ} (_hρ : 0 ≤ ρ) (s t : ℝ) {z : Fin k → ℂ} (hz : z ∈ tube k ρ) :
    |((s : ℂ) + (t : ℂ) + ∑ i, z i).im| ≤ (k : ℝ) * ρ := by
  have him : ((s : ℂ) + (t : ℂ) + ∑ i, z i).im = ∑ i, (z i).im := by
    rw [Complex.add_im, Complex.add_im, Complex.ofReal_im, Complex.ofReal_im, Complex.im_sum]
    ring
  rw [him]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ i : Fin k, |(z i).im| ≤ ∑ _i : Fin k, ρ := Finset.sum_le_sum fun i _ => (hz i).le
    _ = (k : ℝ) * ρ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The complexified sine of the coupled argument is admissible.** -/
theorem boundedC1_coupledMultiSin (ε : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    BoundedC1TubePotential (coupledMultiSin (k := k) ε)
      (fun s t z => ((ε : ℝ) : ℂ) * Complex.cos ((s : ℂ) + (t : ℂ) + ∑ i, z i))
      (fun s t z => ((ε : ℝ) : ℂ) * Complex.cos ((s : ℂ) + (t : ℂ) + ∑ i, z i)) ρ
      (|ε| * Real.cosh ((k : ℝ) * ρ)) := by
  have hatom : BoundedC1TubePotential (k := k)
      (fun s t z => Complex.sin ((s : ℂ) + (t : ℂ) + ∑ i, z i))
      (fun s t z => Complex.cos ((s : ℂ) + (t : ℂ) + ∑ i, z i))
      (fun s t z => Complex.cos ((s : ℂ) + (t : ℂ) + ∑ i, z i)) ρ
      (Real.cosh ((k : ℝ) * ρ)) :=
    BoundedC1TubePotential.ofSum Complex.hasDerivAt_sin Complex.continuous_cos
      (Real.cosh_pos _).le (fun s t z hz => norm_sin_le_cosh
        (mul_nonneg (Nat.cast_nonneg k) hρ) (abs_im_coupledArg hρ s t hz))
  have hconst := BoundedC1TubePotential.const (k := k) ((ε : ℝ) : ℂ) ρ
  have hmul := hconst.mul hatom
  have hnorm : ‖((ε : ℝ) : ℂ)‖ = |ε| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at hmul
  exact hmul.congr_deriv (by funext s t z; ring) (by funext s t z; ring)

/-- **The complexified cosine of the coupled argument is admissible.** -/
theorem boundedC1_coupledMultiCos (ε : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    BoundedC1TubePotential (coupledMultiCos (k := k) ε)
      (fun s t z => ((ε : ℝ) : ℂ) * -Complex.sin ((s : ℂ) + (t : ℂ) + ∑ i, z i))
      (fun s t z => ((ε : ℝ) : ℂ) * -Complex.sin ((s : ℂ) + (t : ℂ) + ∑ i, z i)) ρ
      (|ε| * Real.cosh ((k : ℝ) * ρ)) := by
  have hatom : BoundedC1TubePotential (k := k)
      (fun s t z => Complex.cos ((s : ℂ) + (t : ℂ) + ∑ i, z i))
      (fun s t z => -Complex.sin ((s : ℂ) + (t : ℂ) + ∑ i, z i))
      (fun s t z => -Complex.sin ((s : ℂ) + (t : ℂ) + ∑ i, z i)) ρ
      (Real.cosh ((k : ℝ) * ρ)) :=
    BoundedC1TubePotential.ofSum Complex.hasDerivAt_cos Complex.continuous_sin.neg
      (Real.cosh_pos _).le (fun s t z hz => norm_cos_le_cosh
        (mul_nonneg (Nat.cast_nonneg k) hρ) (abs_im_coupledArg hρ s t hz))
  have hconst := BoundedC1TubePotential.const (k := k) ((ε : ℝ) : ℂ) ρ
  have hmul := hconst.mul hatom
  have hnorm : ‖((ε : ℝ) : ℂ)‖ = |ε| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  rw [hnorm] at hmul
  exact hmul.congr_deriv (by funext s t z; ring) (by funext s t z; ring)

/-- **The effective potential of the coupled scale is admissible.** -/
theorem exists_boundedC1_coupledMultiPotential (k : ℕ) (a massSq ε : ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ) :
    ∃ (Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ) (Mv : ℝ),
      BoundedC1TubePotential (coupledMultiPotential k a massSq ε) Vs Vt ρ Mv := by
  have hSin := boundedC1_coupledMultiSin (k := k) ε hρ
  have hCos := boundedC1_coupledMultiCos (k := k) ε hρ
  have hExp := hSin.cexp_two
  have hT1 := (BoundedC1TubePotential.const (k := k) ((massSq : ℝ) : ℂ) ρ).mul hExp
  have hT2 := (BoundedC1TubePotential.const (k := k)
    ((a * ((k : ℝ) - 4) : ℝ) : ℂ) ρ).mul hSin
  have hT3 := (BoundedC1TubePotential.const (k := k)
    ((a ^ 2 * ((k : ℝ) - 4) : ℝ) : ℂ) ρ).mul (hCos.mul hCos)
  exact ⟨_, _, _, (hT1.add hT2).sub hT3⟩

/-- **The effective potential of the coupled scale is real at real transverse points**, with the
expected value. -/
theorem coupledMultiPotential_ofReal (k : ℕ) (a massSq ε : ℝ) (s t : ℝ) (y : Fin k → ℝ) :
    coupledMultiPotential k a massSq ε s t (realTube y)
      = ((massSq * Real.exp (2 * (ε * Real.sin (s + t + ∑ i, y i)))
          + a * ((k : ℝ) - 4) * (ε * Real.sin (s + t + ∑ i, y i))
          - a ^ 2 * ((k : ℝ) - 4)
            * (ε * Real.cos (s + t + ∑ i, y i) * (ε * Real.cos (s + t + ∑ i, y i))) : ℝ) : ℂ) := by
  have hsum : ∑ i, realTube y i = ((∑ i, y i : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    rfl
  have hz : ((s : ℂ) + (t : ℂ) + ∑ i, realTube y i) = ((s + t + ∑ i, y i : ℝ) : ℂ) := by
    rw [hsum]
    push_cast
    ring
  rw [coupledMultiPotential, coupledMultiSin, coupledMultiCos, hz, ← Complex.ofReal_sin,
    ← Complex.ofReal_cos]
  push_cast
  ring

theorem realOnAxisTube_coupledMultiPotential (k : ℕ) (a massSq ε : ℝ) :
    RealOnAxisTube (coupledMultiPotential k a massSq ε) := by
  intro s t y
  rw [coupledMultiPotential_ofReal, Complex.ofReal_im]

/-- **The effective potential of the coupled scale, computed from the scale's derivatives, is the
real part of the complexified potential.** -/
theorem conformalPotentialMulti_coupledScaleMulti (k : ℕ) (a massSq ε : ℝ) :
    conformalPotentialMulti a massSq (coupledScaleMulti (k := k) ε) (coupledScaleMultiD ε)
        (coupledScaleMultiD ε) (fun _ => coupledScaleMultiD ε) (coupledScaleMultiDD ε)
        (coupledScaleMultiDD ε) (fun _ _ => coupledScaleMultiDD ε)
      = fun s t y => (coupledMultiPotential k a massSq ε s t (realTube y)).re := by
  funext s t y
  rw [coupledMultiPotential_ofReal, Complex.ofReal_re, conformalPotentialMulti,
    coupledScaleMulti, coupledScaleMultiD, coupledScaleMultiDD]
  have h1 : ∑ _i : Fin k, -(ε * Real.sin (s + t + ∑ i, y i))
      = (k : ℝ) * -(ε * Real.sin (s + t + ∑ i, y i)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : ∑ _i : Fin k, (ε * Real.cos (s + t + ∑ i, y i)) ^ 2
      = (k : ℝ) * (ε * Real.cos (s + t + ∑ i, y i)) ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [h1, h2]
  ring

/-! ## The scale law for the coupled scale -/

/-- An admissible potential on a tube carries a clock datum, once the radii and the rectangle are
chosen. -/
theorem tubeDatum_of_boundedC1 {V Vs Vt : ℝ → ℝ → (Fin k → ℂ) → ℂ} {ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T : ℝ}
    (hV : BoundedC1TubePotential V Vs Vt ρ₀ Mv) (hρ₀ : 0 < ρ₀) (hρ0 : 0 ≤ ρ) (hρ : ρ < ρ₀)
    (hT : 0 ≤ T)
    (hsmall : (4 * k + Mv * ρ₀ ^ 2 / 4) * T ^ 2 * Real.exp 2 / ((ρ₀ - ρ) / 2) ^ 2 < 1)
    (hρ₁0 : 0 < ρ₁) (hρ₁ : ρ₁ < ρ) (hρ₂0 : 0 < ρ₂) (hρ₂ : ρ₂ < ρ₁)
    (hρ₃0 : 0 < ρ₃) (hρ₃ : ρ₃ < ρ₂) :
    TubeDatum V Vs Vt ρ₀ Mv ρ ρ₁ ρ₂ ρ₃ T where
  pos := hρ₀
  potC1 := hV.potC1
  massNonneg := hV.boundNonneg
  mass := fun s t _ _ z hz => hV.bound s t z hz
  radNonneg := hρ0
  rad := hρ
  sideNonneg := hT
  small := hsmall
  rad₁Pos := hρ₁0
  rad₁ := hρ₁
  rad₂Pos := hρ₂0
  rad₂ := hρ₂
  rad₃Pos := hρ₃0
  rad₃ := hρ₃

/-- **The two-species scale law for an explicit scale coupling several transverse coordinates.**

For the scale `σ(ξ,η,y) = ε sin(ξ + η + y¹ + ⋯ + yᵏ)` — which depends on all the coordinates through
their sum, so it is neither a slab scale nor a separable one — two species of the same conjugation
weight and different calibrated masses return the conformal scale of the spacetime. No hypothesis is
left on the potential: its admissibility is proved, not assumed. -/
theorem twoSpecies_scale_reconstruction_coupledScaleMulti (k n : ℕ) (a ε : ℝ) {massSq : ℝ}
    (hmassSq : massSq ≠ 0) {other₁ other₂ : (Fin (k + n + 2) → ℝ) → ℝ}
    (h₁ : ∀ (u : (Fin (k + n + 2) → ℝ) → ℝ) (W : Set (Fin (k + n + 2) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.conformalPotential a massSq
              (nullMultiLift (coupledScaleMulti (k := k) ε) n)) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert other₁ u W)
    (h₂ : ∀ (u : (Fin (k + n + 2) → ℝ) → ℝ) (W : Set (Fin (k + n + 2) → ℝ)), IsOpen W →
      SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert
          ((SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.conformalPotential a 0
              (nullMultiLift (coupledScaleMulti (k := k) ε) n)) u W →
        SolvesPotentialWaveOn
          (SmoothPseudoMetric.ofSignature (slabEps (k + n))
            (slabEps_ne_zero (k + n))).chart.dalembert other₂ u W)
    (x : Fin (k + n + 2) → ℝ) :
    (other₁ x - other₂ x) / massSq
      = Real.exp (2 * nullMultiLift (coupledScaleMulti (k := k) ε) n x) := by
  obtain ⟨Vs, Vt, Mv, hV⟩ := exists_boundedC1_coupledMultiPotential k a massSq ε zero_le_one
  have hMv0 : 0 ≤ Mv := hV.boundNonneg
  obtain ⟨T, hTpos, hsmall'⟩ := exists_small_side
    (A := 4 * (k : ℝ) + Mv * (1 : ℝ) ^ 2 / 4 + 1) (B := ((1 : ℝ) - 1 / 2) / 2)
    (by positivity) (by norm_num)
  have hsmall : (4 * (k : ℝ) + Mv * (1 : ℝ) ^ 2 / 4) * T ^ 2 * Real.exp 2
      / (((1 : ℝ) - 1 / 2) / 2) ^ 2 < 1 := by
    have hden : (0 : ℝ) < (((1 : ℝ) - 1 / 2) / 2) ^ 2 := by norm_num
    rw [div_lt_one hden] at hsmall' ⊢
    have hX : (0 : ℝ) ≤ T ^ 2 * Real.exp 2 := by positivity
    nlinarith [hX]
  have hD := tubeDatum_of_boundedC1 (ρ := (1 : ℝ) / 2) (ρ₁ := (1 : ℝ) / 4)
    (ρ₂ := (1 : ℝ) / 8) (ρ₃ := (1 : ℝ) / 16) hV one_pos (by norm_num) (by norm_num)
    hTpos.le hsmall (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  exact hD.twoSpecies_scale_reconstruction_of_scale_multi
    (realOnAxisTube_coupledMultiPotential k a massSq ε)
    (fun s t z hz => hV.bound s t z hz) hTpos n a hmassSq (isC1OnMulti_coupledScaleMulti ε)
    (isC1OnMulti_coupledScaleMultiD ε) (isC1OnMulti_coupledScaleMultiD ε)
    (fun _ => isC1OnMulti_coupledScaleMultiD ε)
    (contDiff_nullMultiLift_coupledScaleMulti ε n)
    (conformalPotentialMulti_coupledScaleMulti k a massSq ε) h₁ h₂ x

end GaloisForLFunctions.HTGeometry
