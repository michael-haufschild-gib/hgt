import GaloisForLFunctions.HTGeometry.SignedMomentSeparation
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Complex-slope Gamma lattice charge

This module formalizes the unconditional finite algebra behind the complex-slope extension of the
scaled Gamma alien charge:

* nonzero complex integer lattices intersect exactly when their slopes are rationally
  commensurate, expressed without choosing a rational quotient;
* Euler reflection preserves the complex lattice contribution at every frequency;
* the first full block of nonzero common-scale charge moments is an exact Vandermonde detector.

No Borel continuation or imported hypertranscendence theorem is hidden here. Those analytic parent
inputs remain outside this algebraic module.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

/-- Nonzero integer multiples of a complex Gamma slope. This is the finite-Borel singular support
attached to one affine factor. -/
def complexGammaIntegerLattice (lam : ℂ) : Set ℂ :=
  {t | ∃ k : ℤ, k ≠ 0 ∧ t = (k : ℂ) * lam}

/-- Two complex slopes are rationally commensurate when nonzero integer multiples agree. This
avoids choosing a representative of their quotient in `ℚ*`. -/
def ComplexGammaCommensurate (lam mu : ℂ) : Prop :=
  ∃ k l : ℤ, k ≠ 0 ∧ l ≠ 0 ∧ (k : ℂ) * lam = (l : ℂ) * mu

/-- Exact support classification: two complex Gamma singular lattices meet precisely when their
slopes are rationally commensurate. -/
theorem complexGammaIntegerLattice_inter_nonempty_iff
    (lam mu : ℂ) :
    (complexGammaIntegerLattice lam ∩ complexGammaIntegerLattice mu).Nonempty ↔
      ComplexGammaCommensurate lam mu := by
  constructor
  · rintro ⟨t, ⟨k, hk, htk⟩, ⟨l, hl, htl⟩⟩
    exact ⟨k, l, hk, hl, htk.symm.trans htl⟩
  · rintro ⟨k, l, hk, hl, hkl⟩
    exact ⟨(k : ℂ) * lam, ⟨k, hk, rfl⟩, ⟨l, hl, hkl⟩⟩

/-- Distinct rational-commensurability classes have disjoint nonzero complex singular lattices. -/
theorem complexGammaIntegerLattice_disjoint_of_not_commensurate
    {lam mu : ℂ} (h : ¬ ComplexGammaCommensurate lam mu) :
    Disjoint (complexGammaIntegerLattice lam) (complexGammaIntegerLattice mu) := by
  rw [Set.disjoint_left]
  intro t htlam htmu
  exact h ((complexGammaIntegerLattice_inter_nonempty_iff lam mu).mp
    ⟨t, htlam, htmu⟩)

/-- Contribution of one affine Gamma factor at the integer lattice label `k`. -/
noncomputable def complexGammaChargeTerm
    (m : ℤ) (lam mu : ℂ) (k : ℤ) : ℂ :=
  (m : ℂ) * lam *
    Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * mu)

/-- Reflection preserves the complex lattice charge term:
`(m, λ, μ, k) ↦ (-m, -λ, 1-μ, -k)`. -/
theorem complexGammaChargeTerm_reflection
    (m : ℤ) (lam mu : ℂ) (k : ℤ) :
    complexGammaChargeTerm (-m) (-lam) (1 - mu) (-k) =
      complexGammaChargeTerm m lam mu k := by
  have hperiod :
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) = 1 := by
    rw [show 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) =
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I k
  rw [complexGammaChargeTerm, complexGammaChargeTerm]
  rw [show -2 * (Real.pi : ℂ) * Complex.I * ((-k : ℤ) : ℂ) * (1 - mu) =
      2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) +
        (-2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * mu) by
    push_cast
    ring]
  rw [Complex.exp_add, hperiod, one_mul]
  push_cast
  ring

/-- One affine Gamma factor with arbitrary nonzero complex slope. -/
structure ComplexAffineGammaFactor where
  slope : ℂ
  offset : ℂ
  multiplicity : ℤ
  slope_ne_zero : slope ≠ 0

/-- Euler-reflected coefficient data. The analytic sine gauge is intentionally absent from the
charge datum because it is differentially algebraic. -/
def ComplexAffineGammaFactor.reflection
    (f : ComplexAffineGammaFactor) : ComplexAffineGammaFactor where
  slope := -f.slope
  offset := 1 - f.offset
  multiplicity := -f.multiplicity
  slope_ne_zero := neg_ne_zero.mpr f.slope_ne_zero

@[simp] theorem ComplexAffineGammaFactor.reflection_reflection
    (f : ComplexAffineGammaFactor) :
    f.reflection.reflection = f := by
  cases f
  simp [ComplexAffineGammaFactor.reflection]

/-- Reflection reverses lattice labels but leaves the complex singular lattice unchanged. -/
theorem complexGammaIntegerLattice_reflection
    (f : ComplexAffineGammaFactor) :
    complexGammaIntegerLattice f.reflection.slope =
      complexGammaIntegerLattice f.slope := by
  ext t
  constructor
  · rintro ⟨k, hk, htk⟩
    refine ⟨-k, neg_ne_zero.mpr hk, ?_⟩
    rw [ComplexAffineGammaFactor.reflection] at htk
    push_cast at htk ⊢
    linear_combination htk
  · rintro ⟨k, hk, htk⟩
    refine ⟨-k, neg_ne_zero.mpr hk, ?_⟩
    rw [ComplexAffineGammaFactor.reflection]
    push_cast at htk ⊢
    linear_combination htk

/-- Intrinsic contribution of one factor at a complex frequency. The quotient `t/λ` is an integer
on the support, so this is the coordinate-free version of `complexGammaChargeTerm`. -/
noncomputable def complexGammaFactorChargeAt
    (f : ComplexAffineGammaFactor) (t : ℂ) : ℂ := by
  classical
  exact
    if t ∈ complexGammaIntegerLattice f.slope then
      (f.multiplicity : ℂ) * f.slope *
        Complex.exp
          (-2 * (Real.pi : ℂ) * Complex.I *
            (t / f.slope) * f.offset)
    else 0

/-- The intrinsic factor contribution is invariant under Euler reflection. -/
theorem complexGammaFactorChargeAt_reflection
    (f : ComplexAffineGammaFactor) (t : ℂ) :
    complexGammaFactorChargeAt f.reflection t =
      complexGammaFactorChargeAt f t := by
  classical
  by_cases ht : t ∈ complexGammaIntegerLattice f.slope
  · have ht0 := ht
    obtain ⟨k, hk, htk⟩ := ht
    have htref : t ∈ complexGammaIntegerLattice f.reflection.slope := by
      rw [complexGammaIntegerLattice_reflection]
      exact ⟨k, hk, htk⟩
    rw [complexGammaFactorChargeAt, if_pos htref,
      complexGammaFactorChargeAt, if_pos ht0]
    have hratio : t / f.slope = (k : ℂ) := by
      apply (div_eq_iff f.slope_ne_zero).2
      rw [htk]
    have hratio_ref : t / f.reflection.slope = ((-k : ℤ) : ℂ) := by
      apply (div_eq_iff f.reflection.slope_ne_zero).2
      rw [htk, ComplexAffineGammaFactor.reflection]
      push_cast
      ring
    rw [hratio, hratio_ref]
    simpa [complexGammaChargeTerm, ComplexAffineGammaFactor.reflection] using
      complexGammaChargeTerm_reflection f.multiplicity f.slope f.offset k
  · have htref : t ∉ complexGammaIntegerLattice f.reflection.slope := by
      rw [complexGammaIntegerLattice_reflection]
      exact ht
    simp [complexGammaFactorChargeAt, ht, htref]

/-- Complete complex-frequency alien charge of a finite affine Gamma datum. -/
noncomputable def complexScaledGammaAlienChargeAt {d : ℕ}
    (a : Fin d → ComplexAffineGammaFactor) (t : ℂ) : ℂ :=
  ∑ i, complexGammaFactorChargeAt (a i) t

/-- Simultaneous Euler reflection of every factor leaves the complete charge unchanged. -/
theorem complexScaledGammaAlienChargeAt_reflection {d : ℕ}
    (a : Fin d → ComplexAffineGammaFactor) (t : ℂ) :
    complexScaledGammaAlienChargeAt (fun i => (a i).reflection) t =
      complexScaledGammaAlienChargeAt a t := by
  classical
  simp [complexScaledGammaAlienChargeAt,
    complexGammaFactorChargeAt_reflection]

/-- Common-scale charge after exponentiating translation-orbit representatives. -/
noncomputable def commonComplexGammaCharge {r : ℕ}
    (delta : ℂ) (node : Fin r → ℂ) (m : Fin r → ℤ) (k : ℕ) : ℂ :=
  delta * ∑ i, (m i : ℂ) * node i ^ k

/-- **Complex charge completeness.** For a nonzero common slope and distinct nonzero orbit nodes,
vanishing of the first full nonzero charge block is equivalent to vanishing of every integer orbit
multiplicity. This is the exact finite Vandermonde endgame of the complex-slope Gamma classifier. -/
theorem commonComplexGammaCharge_zero_iff {r : ℕ}
    {delta : ℂ} (hdelta : delta ≠ 0)
    {node : Fin r → ℂ} (hnode : Function.Injective node)
    (hnode0 : ∀ i, node i ≠ 0) (m : Fin r → ℤ) :
    (∀ k : Fin r, commonComplexGammaCharge delta node m ((k : ℕ) + 1) = 0) ↔
      m = 0 := by
  constructor
  · intro h
    have hker : ∀ k : Fin r,
        ∑ i, (((m i : ℂ) * node i) * node i ^ (k : ℕ)) = 0 := by
      intro k
      have hk := h k
      rw [commonComplexGammaCharge] at hk
      have hsum : ∑ i, (m i : ℂ) * node i ^ ((k : ℕ) + 1) = 0 :=
        (mul_eq_zero.mp hk).resolve_left hdelta
      rw [← hsum]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      ring
    have hzero := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hnode hker
    funext i
    have hi := congrFun hzero i
    simp only [Pi.zero_apply] at hi
    have hcast : (m i : ℂ) = 0 :=
      (mul_eq_zero.mp hi).resolve_right (hnode0 i)
    exact_mod_cast hcast
  · rintro rfl
    simp [commonComplexGammaCharge]

/-- Positive form of charge completeness: every nonzero orbit multiplicity vector is detected by
one of the first `r` nonzero complex lattice frequencies. -/
theorem exists_commonComplexGammaCharge_ne_zero {r : ℕ}
    {delta : ℂ} (hdelta : delta ≠ 0)
    {node : Fin r → ℂ} (hnode : Function.Injective node)
    (hnode0 : ∀ i, node i ≠ 0) {m : Fin r → ℤ} (hm : m ≠ 0) :
    ∃ k : Fin r, commonComplexGammaCharge delta node m ((k : ℕ) + 1) ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hm ((commonComplexGammaCharge_zero_iff hdelta hnode hnode0 m).mp h)

/-! ### Gauss-multiplication invariance -/

/-- A root-of-unity phase is one exactly when its integer frequency is divisible by the
multiplication degree. -/
theorem complex_exp_neg_two_pi_I_int_div_eq_one_iff_dvd
    {N : ℕ} (hN : 0 < N) (ell : ℤ) :
    Complex.exp
        (-2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) / (N : ℂ)) = 1 ↔
      (N : ℤ) ∣ ell := by
  constructor
  · intro h
    obtain ⟨q, hq⟩ := Complex.exp_eq_one_iff.mp h
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      exact mul_ne_zero (mul_ne_zero (by norm_num) hp) Complex.I_ne_zero
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have hratio : -(ell : ℂ) / (N : ℂ) = (q : ℂ) := by
      apply (mul_left_cancel₀ hpi)
      calc
        (2 * (Real.pi : ℂ) * Complex.I) * (-(ell : ℂ) / (N : ℂ)) =
            -2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) / (N : ℂ) := by ring
        _ = (q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := hq
        _ = (2 * (Real.pi : ℂ) * Complex.I) * (q : ℂ) := by ring
    have hcast : ell = -(q * (N : ℤ)) := by
      apply_mod_cast (show (ell : ℂ) = ((-(q * (N : ℤ)) : ℤ) : ℂ) from ?_)
      apply (div_eq_iff hN0).mp at hratio
      push_cast at hratio ⊢
      linear_combination -hratio
    exact ⟨-q, by rw [hcast]; ring⟩
  · rintro ⟨q, rfl⟩
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [show -2 * (Real.pi : ℂ) * Complex.I * (((N : ℤ) * q : ℤ) : ℂ) / (N : ℂ) =
        (-q : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
      push_cast
      field_simp]
    simpa using Complex.exp_int_mul_two_pi_mul_I (-q)

/-- Finite root sum created by decomposing one slope-`Nδ` Gamma factor into `N` slope-`δ`
factors. -/
noncomputable def complexGammaRootSum (N : ℕ) (ell : ℤ) : ℂ :=
  ∑ r ∈ Finset.range N,
    Complex.exp
      (-2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) * (r : ℂ) / (N : ℂ))

/-- Root-of-unity orthogonality: the multiplication packet is zero off the old lattice and has
weight `N` on it. -/
theorem complexGammaRootSum_eq {N : ℕ} (hN : 0 < N) (ell : ℤ) :
    complexGammaRootSum N ell = if (N : ℤ) ∣ ell then (N : ℂ) else 0 := by
  classical
  by_cases hd : (N : ℤ) ∣ ell
  · obtain ⟨q, rfl⟩ := hd
    rw [if_pos (dvd_mul_right (N : ℤ) q)]
    unfold complexGammaRootSum
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    calc
      (∑ r ∈ Finset.range N,
          Complex.exp
            (-2 * (Real.pi : ℂ) * Complex.I * ((((N : ℤ) * q : ℤ) : ℂ)) *
              (r : ℂ) / (N : ℂ))) =
          ∑ _r ∈ Finset.range N, (1 : ℂ) := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [show -2 * (Real.pi : ℂ) * Complex.I * ((((N : ℤ) * q : ℤ) : ℂ)) *
                  (r : ℂ) / (N : ℂ) =
                (-(q * (r : ℤ)) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
              push_cast
              field_simp]
            simpa using Complex.exp_int_mul_two_pi_mul_I (-(q * (r : ℤ)))
      _ = (N : ℂ) := by simp
  · rw [if_neg hd]
    unfold complexGammaRootSum
    let xi : ℂ :=
      Complex.exp
        (-2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) / (N : ℂ))
    have hxi : xi ≠ 1 := by
      exact ((complex_exp_neg_two_pi_I_int_div_eq_one_iff_dvd hN ell).not.mpr hd)
    have hpow : xi ^ N = 1 := by
      change
        Complex.exp
          (-2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) / (N : ℂ)) ^ N = 1
      rw [← Complex.exp_nat_mul]
      have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
      rw [show (N : ℂ) *
          (-2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) / (N : ℂ)) =
          (-ell : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
        field_simp]
      simpa using Complex.exp_int_mul_two_pi_mul_I (-ell)
    rw [show (∑ r ∈ Finset.range N,
        Complex.exp
          (-2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) * (r : ℂ) / (N : ℂ))) =
        ∑ r ∈ Finset.range N, xi ^ r by
      apply Finset.sum_congr rfl
      intro r hr
      change
        Complex.exp
            (-2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) * (r : ℂ) / (N : ℂ)) =
          Complex.exp
            (-2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) / (N : ℂ)) ^ r
      rw [← Complex.exp_nat_mul]
      congr 1
      ring]
    rw [geom_sum_eq hxi, hpow, sub_self, zero_div]

/-- Charge of the full factor packet on the right side of Gauss multiplication. -/
noncomputable def gaussExpandedComplexGammaCharge
    (delta mu : ℂ) (m : ℤ) (N : ℕ) (ell : ℤ) : ℂ :=
  delta * ∑ r ∈ Finset.range N,
    (m : ℂ) *
      Complex.exp
        (-2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) *
          ((mu + (r : ℂ)) / (N : ℂ)))

/-- The expanded charge factors into the original offset phase and a finite root sum. -/
theorem gaussExpandedComplexGammaCharge_factor
    {N : ℕ} (hN : 0 < N) (delta mu : ℂ) (m : ℤ) (ell : ℤ) :
    gaussExpandedComplexGammaCharge delta mu m N ell =
      delta * (m : ℂ) *
        Complex.exp
          (-2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) * mu / (N : ℂ)) *
        complexGammaRootSum N ell := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold gaussExpandedComplexGammaCharge complexGammaRootSum
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [show -2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) *
        ((mu + (r : ℂ)) / (N : ℂ)) =
      (-2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) * mu / (N : ℂ)) +
      (-2 * (Real.pi : ℂ) * Complex.I * (ell : ℂ) * (r : ℂ) / (N : ℂ)) by
    field_simp
    ring]
  rw [Complex.exp_add]
  ring

/-- Gauss multiplication creates no new charge away from the original slope lattice. -/
theorem gaussExpandedComplexGammaCharge_eq_zero_of_not_dvd
    {N : ℕ} (hN : 0 < N) (delta mu : ℂ) (m : ℤ) (ell : ℤ)
    (hd : ¬ (N : ℤ) ∣ ell) :
    gaussExpandedComplexGammaCharge delta mu m N ell = 0 := by
  rw [gaussExpandedComplexGammaCharge_factor hN,
    complexGammaRootSum_eq hN, if_neg hd, mul_zero]

/-- **Gauss-multiplication charge invariance.** On the original lattice, the sum of all `N`
expanded factor charges is exactly the charge of the slope-`Nδ` factor. -/
theorem gaussExpandedComplexGammaCharge_eq_original
    {N : ℕ} (hN : 0 < N) (delta mu : ℂ) (m q : ℤ) :
    gaussExpandedComplexGammaCharge delta mu m N ((N : ℤ) * q) =
      complexGammaChargeTerm m ((N : ℂ) * delta) mu q := by
  rw [gaussExpandedComplexGammaCharge_factor hN,
    complexGammaRootSum_eq hN, if_pos (dvd_mul_right (N : ℤ) q)]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [show -2 * (Real.pi : ℂ) * Complex.I * ((((N : ℤ) * q : ℤ) : ℂ)) * mu /
        (N : ℂ) =
      -2 * (Real.pi : ℂ) * Complex.I * (q : ℂ) * mu by
    push_cast
    field_simp]
  unfold complexGammaChargeTerm
  ring

/-! ### Finite Euler reflection pairs are charge-neutral -/

/-- Positive-slope reciprocal-Gamma half of a local Euler factor. -/
def complexEulerGammaPositiveHalf (lam : ℂ) (hlam : lam ≠ 0) :
    ComplexAffineGammaFactor where
  slope := lam
  offset := 0
  multiplicity := -1
  slope_ne_zero := hlam

/-- Reflected negative-slope reciprocal-Gamma half of a local Euler factor. -/
def complexEulerGammaNegativeHalf (lam : ℂ) (hlam : lam ≠ 0) :
    ComplexAffineGammaFactor where
  slope := -lam
  offset := 1
  multiplicity := -1
  slope_ne_zero := neg_ne_zero.mpr hlam

/-- The two reciprocal Gamma halves representing one finite Euler factor have exactly cancelling
complex lattice charge at every frequency. -/
theorem complexEulerGammaPairChargeAt_eq_zero
    (lam : ℂ) (hlam : lam ≠ 0) (t : ℂ) :
    complexGammaFactorChargeAt (complexEulerGammaPositiveHalf lam hlam) t +
      complexGammaFactorChargeAt (complexEulerGammaNegativeHalf lam hlam) t = 0 := by
  let f : ComplexAffineGammaFactor :=
    { slope := lam
      offset := 0
      multiplicity := 1
      slope_ne_zero := hlam }
  have href :
      f.reflection = complexEulerGammaNegativeHalf lam hlam := by
    simp [f, ComplexAffineGammaFactor.reflection, complexEulerGammaNegativeHalf]
  rw [← href, complexGammaFactorChargeAt_reflection]
  unfold complexGammaFactorChargeAt complexEulerGammaPositiveHalf f
  by_cases ht : t ∈ complexGammaIntegerLattice lam <;> simp [ht]

/-- Any finite semilocal family of Euler reflection pairs remains charge-neutral. -/
theorem finiteComplexEulerGammaPairChargeAt_eq_zero {d : ℕ}
    (lam : Fin d → ℂ) (hlam : ∀ i, lam i ≠ 0) (t : ℂ) :
    ∑ i, (complexGammaFactorChargeAt
          (complexEulerGammaPositiveHalf (lam i) (hlam i)) t +
        complexGammaFactorChargeAt
          (complexEulerGammaNegativeHalf (lam i) (hlam i)) t) = 0 := by
  simp [complexEulerGammaPairChargeAt_eq_zero]

/-- Reflection-odd charge of one local Euler Gamma pair. Unlike the unpolarized sum, this
source-polarized difference retains the two chiral halves with opposite signs. -/
noncomputable def complexEulerGammaOddChargeAt
    (lam : ℂ) (hlam : lam ≠ 0) (t : ℂ) : ℂ :=
  complexGammaFactorChargeAt (complexEulerGammaPositiveHalf lam hlam) t -
    complexGammaFactorChargeAt (complexEulerGammaNegativeHalf lam hlam) t

/-- Odd polarization converts reflection cancellation into exact charge doubling. -/
theorem complexEulerGammaOddChargeAt_eq_two_mul
    (lam : ℂ) (hlam : lam ≠ 0) (t : ℂ) :
    complexEulerGammaOddChargeAt lam hlam t =
      2 * complexGammaFactorChargeAt (complexEulerGammaPositiveHalf lam hlam) t := by
  have hpair := complexEulerGammaPairChargeAt_eq_zero lam hlam t
  have hnegative :
      complexGammaFactorChargeAt (complexEulerGammaNegativeHalf lam hlam) t =
        -complexGammaFactorChargeAt (complexEulerGammaPositiveHalf lam hlam) t := by
    linear_combination hpair
  unfold complexEulerGammaOddChargeAt
  rw [hnegative]
  ring

/-- Every nonzero integer frequency on one Euler slope lattice has the same doubled odd charge. -/
theorem complexEulerGammaOddChargeAt_integer
    (lam : ℂ) (hlam : lam ≠ 0) (k : ℤ) (hk : k ≠ 0) :
    complexEulerGammaOddChargeAt lam hlam ((k : ℂ) * lam) = -2 * lam := by
  rw [complexEulerGammaOddChargeAt_eq_two_mul]
  unfold complexGammaFactorChargeAt complexEulerGammaPositiveHalf
  rw [if_pos ⟨k, hk, rfl⟩]
  have hratio : (k : ℂ) * lam / lam = (k : ℂ) := by field_simp
  rw [hratio]
  simp

theorem complexEulerGammaOddChargeAt_integer_ne_zero
    (lam : ℂ) (hlam : lam ≠ 0) (k : ℤ) (hk : k ≠ 0) :
    complexEulerGammaOddChargeAt lam hlam ((k : ℂ) * lam) ≠ 0 := by
  rw [complexEulerGammaOddChargeAt_integer lam hlam k hk]
  exact mul_ne_zero (by norm_num) hlam

/-- Total odd-polarized charge of a finite complex Euler-slope family. -/
noncomputable def finiteComplexEulerGammaOddChargeAt {d : ℕ}
    (lam : Fin d → ℂ) (hlam : ∀ i, lam i ≠ 0) (t : ℂ) : ℂ :=
  ∑ i, complexEulerGammaOddChargeAt (lam i) (hlam i) t

/-- Pairwise noncommensurate slopes are individually readable after odd polarization: evaluation
on one slope lattice sees exactly that slope's doubled charge and no other factor. -/
theorem finiteComplexEulerGammaOddChargeAt_slope
    {d : ℕ} (lam : Fin d → ℂ) (hlam : ∀ i, lam i ≠ 0)
    (hsep : ∀ i j, i ≠ j → ¬ ComplexGammaCommensurate (lam i) (lam j))
    (i : Fin d) :
    finiteComplexEulerGammaOddChargeAt lam hlam (lam i) = -2 * lam i := by
  classical
  rw [finiteComplexEulerGammaOddChargeAt, Finset.sum_eq_single i]
  · simpa using complexEulerGammaOddChargeAt_integer (lam i) (hlam i) 1 (by norm_num)
  · intro j hj hji
    unfold complexEulerGammaOddChargeAt
    have hnot : lam i ∉ complexGammaIntegerLattice (lam j) := by
      intro hmem
      have hi : lam i ∈ complexGammaIntegerLattice (lam i) :=
        ⟨1, by norm_num, by simp⟩
      exact hsep i j (Ne.symm hji)
        ((complexGammaIntegerLattice_inter_nonempty_iff (lam i) (lam j)).mp
          ⟨lam i, hi, hmem⟩)
    have hnotneg : lam i ∉ complexGammaIntegerLattice (-lam j) := by
      have hlat :
          complexGammaIntegerLattice (-lam j) =
            complexGammaIntegerLattice (lam j) := by
        simpa [ComplexAffineGammaFactor.reflection] using
          complexGammaIntegerLattice_reflection
            { slope := lam j
              offset := 0
              multiplicity := 1
              slope_ne_zero := hlam j }
      rw [hlat]
      exact hnot
    simp [complexGammaFactorChargeAt, complexEulerGammaPositiveHalf,
      complexEulerGammaNegativeHalf, hnot, hnotneg]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

theorem finiteComplexEulerGammaOddChargeAt_slope_ne_zero
    {d : ℕ} (lam : Fin d → ℂ) (hlam : ∀ i, lam i ≠ 0)
    (hsep : ∀ i j, i ≠ j → ¬ ComplexGammaCommensurate (lam i) (lam j))
    (i : Fin d) :
    finiteComplexEulerGammaOddChargeAt lam hlam (lam i) ≠ 0 := by
  rw [finiteComplexEulerGammaOddChargeAt_slope lam hlam hsep i]
  exact mul_ne_zero (by norm_num) (hlam i)

end GaloisForLFunctions.HTGeometry
