import GaloisForLFunctions.RHTower.XiZeroHurwitzDifferentialIndependence
import GaloisForLFunctions.RHTower.BornTemperatureFactorType
import Mathlib.LinearAlgebra.Vandermonde

/-!
# The Xi--Hurwitz constraint-orientation law

The Hurwitz monodromy character `q(s) = exp(-2*pi*i*s)` is simultaneously the complete
differential-dependence invariant for nonintegral Hurwitz shift functions and an exact orientation
coordinate for the Xi divisor.  Functional-equation reflection is carried by `q` to complex
conjugation, while the norm of `q(s)` is `exp(2*pi*Im(s))`.

The complete family of continued Hurwitz functions indexed by the actual Xi-divisor support is
unconditionally differentially independent.  RH is exactly the additional orientation statement
that every character value equals the negative real number determined by its height.  For a finite
height-ordered zero family, this upgrades the nonzero complex Vandermonde separator used by the
independence proof to a positive real determinant.
-/

open Complex Set Function
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped Differential

namespace RHTower

noncomputable section

open HurwitzJointLadder HurwitzOrbit

/-- The Hurwitz monodromy character carried by an actual Xi-divisor value. -/
def xiHurwitzMonodromyCharacter (ρ : XiDivisorSupport) : ℂ := monoScalar (ρ : ℂ)

/-- Functional-equation reflection of an exponent becomes conjugation of its Hurwitz monodromy
character. -/
theorem monoScalar_feReflection (s : ℂ) :
    monoScalar (1 - starRingEnd ℂ s) = starRingEnd ℂ (monoScalar s) := by
  rw [monoScalar, monoScalar, ← Complex.exp_conj]
  have hsplit :
      -(2 * (Real.pi : ℂ) * I * (1 - starRingEnd ℂ s)) =
        -(2 * (Real.pi : ℂ) * I) +
          starRingEnd ℂ (-(2 * (Real.pi : ℂ) * I * s)) := by
    simp only [map_neg, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hone : Complex.exp (-(2 * (Real.pi : ℂ) * I)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    refine ⟨-1, ?_⟩
    push_cast
    ring
  rw [hsplit, Complex.exp_add, hone, one_mul]

/-- Inside the open critical strip, the monodromy character is fixed by conjugation exactly on the
critical line. -/
theorem openCriticalStrip_monoScalar_conj_fixed_iff {s : ℂ}
    (hs : 0 < s.re ∧ s.re < 1) :
    starRingEnd ℂ (monoScalar s) = monoScalar s ↔ s.re = 1 / 2 := by
  have hrefStrip : 0 < (1 - starRingEnd ℂ s).re ∧ (1 - starRingEnd ℂ s).re < 1 := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    constructor <;> linarith [hs.1, hs.2]
  constructor
  · intro hreal
    have hq : monoScalar (1 - starRingEnd ℂ s) = monoScalar s := by
      rw [monoScalar_feReflection, hreal]
    obtain ⟨m, hm⟩ :=
      (monoScalar_eq_monoScalar_iff_integerDifference
        (1 - starRingEnd ℂ s) s).mp hq
    have hfixed : 1 - starRingEnd ℂ s = s :=
      openCriticalStrip_eq_of_sub_eq_int hrefStrip hs m hm
    exact (fe_reflection_fixed_iff s).mp hfixed
  · intro hre
    have hfixed : 1 - starRingEnd ℂ s = s :=
      (fe_reflection_fixed_iff s).mpr hre
    rw [← monoScalar_feReflection, hfixed]

/-- The modulus of the monodromy character records the exponent height exactly. -/
theorem monoScalar_norm_eq_height (s : ℂ) :
    ‖monoScalar s‖ = Real.exp (2 * Real.pi * s.im) := by
  have hre : (-(2 * (Real.pi : ℂ) * I * s)).re = 2 * Real.pi * s.im := by
    simp
  rw [monoScalar, Complex.norm_exp, hre]

theorem monoScalar_re_eq_neg_height_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    (monoScalar s).re = -Real.exp (2 * Real.pi * s.im) := by
  have hre : (-(2 * (Real.pi : ℂ) * I * s)).re = 2 * Real.pi * s.im := by
    simp
  have him : (-(2 * (Real.pi : ℂ) * I * s)).im = -(2 * Real.pi * s.re) := by
    simp
  rw [monoScalar, Complex.exp_re, hre, him, hs]
  have harg : -(2 * Real.pi * (1 / 2 : ℝ)) = -Real.pi := by ring
  rw [harg, Real.cos_neg, Real.cos_pi]
  ring

/-- On the critical line, the character is the negative real exponential of the zero height. -/
theorem monoScalar_eq_neg_height_of_re_eq_half {s : ℂ} (hs : s.re = 1 / 2) :
    monoScalar s = -((Real.exp (2 * Real.pi * s.im) : ℝ) : ℂ) := by
  apply Complex.ext
  · change (monoScalar s).re = -Real.exp (2 * Real.pi * s.im)
    exact monoScalar_re_eq_neg_height_of_re_eq_half hs
  · have hstripReal : starRingEnd ℂ (monoScalar s) = monoScalar s := by
      have hfixed : 1 - starRingEnd ℂ s = s := (fe_reflection_fixed_iff s).mpr hs
      rw [← monoScalar_feReflection, hfixed]
    calc
      (monoScalar s).im = 0 := Complex.conj_eq_iff_im.mp hstripReal
      _ = (-((Real.exp (2 * Real.pi * s.im) : ℝ) : ℂ)).im := by
        rw [neg_im, ofReal_im, neg_zero]

/-- Inside the open critical strip, the character lies on the negative real ray exactly on the
critical line. -/
theorem openCriticalStrip_monoScalar_negativeReal_iff {s : ℂ}
    (hs : 0 < s.re ∧ s.re < 1) :
    ((monoScalar s).im = 0 ∧ (monoScalar s).re < 0) ↔ s.re = 1 / 2 := by
  constructor
  · rintro ⟨him, -⟩
    apply (openCriticalStrip_monoScalar_conj_fixed_iff hs).mp
    exact Complex.conj_eq_iff_im.mpr him
  · intro hre
    constructor
    · exact Complex.conj_eq_iff_im.mp
        ((openCriticalStrip_monoScalar_conj_fixed_iff hs).mpr hre)
    · rw [monoScalar_re_eq_neg_height_of_re_eq_half hre]
      exact neg_neg_of_pos (Real.exp_pos _)

/-- Distinct Xi-divisor values have distinct Hurwitz monodromy characters. -/
theorem xiHurwitzMonodromyCharacter_injective :
    Function.Injective xiHurwitzMonodromyCharacter := by
  intro ρ τ hq
  apply Subtype.ext
  obtain ⟨m, hm⟩ :=
    (monoScalar_eq_monoScalar_iff_integerDifference (ρ : ℂ) (τ : ℂ)).mp hq
  exact openCriticalStrip_eq_of_sub_eq_int
    (xi_divisor_support_re_mem_open_unit ρ)
    (xi_divisor_support_re_mem_open_unit τ) m hm

/-- **Complete Xi-indexed differential freeness.**  The entire family of analytically continued
Hurwitz functions indexed by distinct points of the actual Xi divisor is differentially independent
over `ℂ(a)`. -/
theorem xi_zero_hurwitz_differentialIndependent_all :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
      (fun ρ : XiDivisorSupport => continuedHzetaUpperEndMero (ρ : ℂ)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  unfold DifferentialIndependent
  apply algebraicIndependent_of_finite_type
  intro t ht
  let S : Set XiDivisorSupport := Prod.fst '' t
  have hS : S.Finite := ht.image Prod.fst
  letI : Fintype S := hS.fintype
  have hDI := xi_zero_hurwitz_differentialIndependent
    (ρ := fun x : S => x.1) Subtype.val_injective
  unfold DifferentialIndependent at hDI
  let e : t → S × ℕ := fun p =>
    (⟨p.1.1, ⟨p.1, p.2, rfl⟩⟩, p.1.2)
  have he : Function.Injective e := by
    intro p q hpq
    apply Subtype.ext
    exact Prod.ext
      (congrArg (fun z : S × ℕ => (z.1 : XiDivisorSupport)) hpq)
      (congrArg (fun z : S × ℕ => z.2) hpq)
  have hcomp := hDI.comp e he
  simpa only [Function.comp_apply, e] using hcomp

/-- The negative-real orientation chamber of the complete Xi-indexed Hurwitz family. -/
def XiHurwitzNegativeCharacterChamber : Prop :=
  ∀ ρ : XiDivisorSupport,
    (xiHurwitzMonodromyCharacter ρ).im = 0 ∧
      (xiHurwitzMonodromyCharacter ρ).re < 0

/-- RH is exactly the negative-real orientation chamber of the Xi-indexed Hurwitz family. -/
theorem riemannHypothesis_iff_xiHurwitzNegativeCharacterChamber :
    RiemannHypothesis ↔ XiHurwitzNegativeCharacterChamber := by
  constructor
  · intro hRH ρ
    apply (openCriticalStrip_monoScalar_negativeReal_iff
      (xi_divisor_support_re_mem_open_unit ρ)).mpr
    exact xi_divisor_support_re_eq_half_of_rh hRH ρ
  · intro hchamber
    apply riemannHypothesis_iff_xiZero_reflection_fixed.mpr
    intro ρ hρ
    let q : XiDivisorSupport := ⟨ρ, mem_xi_divisor_support_of_eq_zero hρ⟩
    have hre : ρ.re = 1 / 2 :=
      (openCriticalStrip_monoScalar_negativeReal_iff
        (xi_divisor_support_re_mem_open_unit q)).mp (hchamber q)
    exact (fe_reflection_fixed_iff ρ).mpr hre

/-- **Exact RH value law.**  RH holds exactly when every Xi-zero monodromy character is the negative
real exponential determined by that zero's height. -/
theorem riemannHypothesis_iff_xiHurwitzMonodromyCharacter_eq_neg_height :
    RiemannHypothesis ↔
      ∀ ρ : XiDivisorSupport,
        xiHurwitzMonodromyCharacter ρ =
          -((Real.exp (2 * Real.pi * (ρ : ℂ).im) : ℝ) : ℂ) := by
  constructor
  · intro hRH ρ
    exact monoScalar_eq_neg_height_of_re_eq_half
      (xi_divisor_support_re_eq_half_of_rh hRH ρ)
  · intro hchar
    apply riemannHypothesis_iff_xiHurwitzNegativeCharacterChamber.mpr
    intro ρ
    have heq := hchar ρ
    constructor
    · calc
        (xiHurwitzMonodromyCharacter ρ).im =
            (-((Real.exp (2 * Real.pi * (ρ : ℂ).im) : ℝ) : ℂ)).im :=
          congrArg Complex.im heq
        _ = 0 := by rw [neg_im, ofReal_im, neg_zero]
    · have hre := congrArg Complex.re heq
      rw [neg_re, ofReal_re] at hre
      rw [hre]
      exact neg_neg_of_pos (Real.exp_pos _)

/-- The positive radius underneath an Xi-zero Hurwitz character. -/
def xiHurwitzMonodromyRadius (ρ : XiDivisorSupport) : ℝ :=
  Real.exp (2 * Real.pi * (ρ : ℂ).im)

theorem xiHurwitzMonodromyRadius_pos (ρ : XiDivisorSupport) :
    0 < xiHurwitzMonodromyRadius ρ := Real.exp_pos _

theorem xiHurwitzMonodromyRadius_strictMono
    {n : ℕ} {ρ : Fin n → XiDivisorSupport}
    (hρ : StrictMono (fun i => (ρ i : ℂ).im)) :
    StrictMono (fun i => xiHurwitzMonodromyRadius (ρ i)) := by
  intro i j hij
  change Real.exp (2 * Real.pi * (ρ i : ℂ).im) <
    Real.exp (2 * Real.pi * (ρ j : ℂ).im)
  rw [Real.exp_lt_exp]
  exact mul_lt_mul_of_pos_left (hρ hij) (mul_pos (by norm_num) Real.pi_pos)

/-- A real Vandermonde matrix on strictly increasing nodes has positive determinant. -/
theorem det_vandermonde_pos_of_strictMono
    {n : ℕ} {r : Fin n → ℝ} (hr : StrictMono r) :
    0 < (Matrix.vandermonde r).det := by
  rw [Matrix.det_vandermonde]
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  exact sub_pos.mpr (hr (Finset.mem_Ioi.mp hj))

/-- Under RH, every finite height-ordered Xi-zero character Vandermonde lies in the positive real
determinant chamber. -/
theorem xiHurwitzMonodromy_vandermonde_det_pos_real_of_rh
    (hRH : RiemannHypothesis) {n : ℕ} (ρ : Fin n → XiDivisorSupport)
    (hρ : StrictMono (fun i => (ρ i : ℂ).im)) :
    ∃ d : ℝ, 0 < d ∧
      (Matrix.vandermonde (fun i => -xiHurwitzMonodromyCharacter (ρ i))).det = (d : ℂ) := by
  let r : Fin n → ℝ := fun i => xiHurwitzMonodromyRadius (ρ i)
  have hr : StrictMono r := xiHurwitzMonodromyRadius_strictMono hρ
  refine ⟨(Matrix.vandermonde r).det, det_vandermonde_pos_of_strictMono hr, ?_⟩
  have hnode : (fun i => -xiHurwitzMonodromyCharacter (ρ i)) =
      fun i => (r i : ℂ) := by
    funext i
    rw [(riemannHypothesis_iff_xiHurwitzMonodromyCharacter_eq_neg_height.mp hRH) (ρ i)]
    simp [r, xiHurwitzMonodromyRadius]
  rw [hnode]
  have hmatrix : Matrix.vandermonde (fun i => (r i : ℂ)) =
      (algebraMap ℝ ℂ).mapMatrix (Matrix.vandermonde r) := by
    ext i j
    simp [Matrix.vandermonde_apply]
  rw [hmatrix]
  exact (RingHom.map_det (algebraMap ℝ ℂ) (Matrix.vandermonde r)).symm

/-- **Xi--Hurwitz constraint-orientation product law.**  The complete Xi-indexed continued-Hurwitz
family is unconditionally differentially free, and RH is exactly its height-normalized negative
monodromy-character orientation. -/
theorem xi_hurwitz_constraint_orientation_product_law :
    letI := isDomain_upperEndAnalyticSubring
    letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
    letI := upperEndMeroFieldDifferential
    DifferentialIndependent (RatFunc ℂ)
        (fun ρ : XiDivisorSupport => continuedHzetaUpperEndMero (ρ : ℂ)) ∧
      (RiemannHypothesis ↔
        ∀ ρ : XiDivisorSupport,
          xiHurwitzMonodromyCharacter ρ =
            -((Real.exp (2 * Real.pi * (ρ : ℂ).im) : ℝ) : ℂ)) := by
  letI := isDomain_upperEndAnalyticSubring
  letI : Algebra ℤ upperEndAnalyticSubring := Ring.toIntAlgebra _
  letI : Algebra ℤ upperEndMeroField := Ring.toIntAlgebra _
  letI : Algebra (RatFunc ℂ) upperEndMeroField := upperEndRatfuncToMero.toAlgebra
  letI := upperEndMeroFieldDifferential
  exact ⟨xi_zero_hurwitz_differentialIndependent_all,
    riemannHypothesis_iff_xiHurwitzMonodromyCharacter_eq_neg_height⟩

end

end RHTower
