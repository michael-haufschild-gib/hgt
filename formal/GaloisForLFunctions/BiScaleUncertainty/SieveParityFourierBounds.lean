import GaloisForLFunctions.BiScaleUncertainty.SieveRawMomentPerturbation
import GaloisForLFunctions.BiScaleUncertainty.SieveHalfPeriodTranslation
import GaloisForLFunctions.RHTower.XiResolventTraceMassControl

/-! Raw-array Fourier inversion and physical translation bounds. -/

open scoped BigOperators
open Finset
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
open AffineSieve
set_option autoImplicit false
variable {P : ℕ} [NeZero P]

private theorem dft_sup_bound (f : ZMod P → ℂ) (C : ℝ)
    (hf : ∀ r, ‖ZMod.dft f r‖ ≤ C) (x : ZMod P) : ‖f x‖ ≤ C := by
  have hP : (0 : ℝ) < P := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne P))
  have hh : (P : ℝ)*‖f x‖ ≤ (P : ℝ)*C := by
    calc
      (P : ℝ)*‖f x‖ = ‖ZMod.dft (ZMod.dft f) (-x)‖ := by
        rw [ZMod.dft_dft]
        simp [smul_eq_mul]
      _ ≤ ∑ r : ZMod P, ‖ZMod.stdAddChar (-(r*(-x))) * ZMod.dft f r‖ := by
        simpa only [ZMod.dft_apply, smul_eq_mul] using
          norm_sum_le (Finset.univ : Finset (ZMod P))
            (fun r => ZMod.stdAddChar (-(r*(-x))) * ZMod.dft f r)
      _ ≤ ∑ _r : ZMod P, C := by
        apply Finset.sum_le_sum
        intro r _
        simpa [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe] using hf r
      _ = (P : ℝ)*C := by simp
  nlinarith

private theorem sum_cons {m : ℕ} (F : (Fin (m+1) → ZMod P) → ℂ) :
    (∑ h, F h) = ∑ t : ZMod P, ∑ h : Fin m → ZMod P, F (Fin.cons t h) := by
  calc
    _ = ∑ x : ZMod P × (Fin m → ZMod P), F (Fin.cons x.1 x.2) :=
      (Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (m+1) => ZMod P))
        _ _ (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.sum_prod_type]

private theorem momentDFT_cons {m : ℕ} (T : (Fin (m+1) → ZMod P) → ℂ)
    (t : ZMod P) (r : Fin m → ZMod P) :
    momentDFT T (Fin.cons t r) =
      ZMod.dft (fun s => momentDFT (fun h => T (Fin.cons s h)) r) t := by
  simp only [momentDFT, ZMod.dft_apply, smul_eq_mul]
  rw [sum_cons]
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  simp_rw [Finset.mul_sum, mul_assoc]

/-- Multivariate Fourier inversion has norm at most one from coefficient sup-norm. -/
theorem momentDFT_sup_bound {m : ℕ} (T : (Fin m → ZMod P) → ℂ) (C : ℝ)
    (hT : ∀ r, ‖momentDFT T r‖ ≤ C) (v : Fin m → ZMod P) : ‖T v‖ ≤ C := by
  induction m with
  | zero =>
      have hh (w : Fin 0 → ZMod P) : T w = T v := congrArg T (Subsingleton.elim _ _)
      simpa [momentDFT, hh] using hT v
  | succ m ih =>
      have hh (r : Fin m → ZMod P) :
          ‖momentDFT (fun h => T (Fin.cons (v 0) h)) r‖ ≤ C := by
        apply dft_sup_bound (fun s => momentDFT (fun h => T (Fin.cons s h)) r) C
        intro t
        rw [← momentDFT_cons]
        exact hT (Fin.cons t r)
      have hv : Fin.cons (v 0) (fun i => v i.succ) = v := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      simpa only [hv] using ih (fun h => T (Fin.cons (v 0) h)) hh (fun i => v i.succ)

local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- A bound on every resonant product bounds every literal raw moment. -/
theorem raw_error_of_resonant_products (N : ℕ) (c e : ℕ → ℝ) (m : ℕ) (η : ℝ)
    (hη : 0 ≤ η)
    (hp : ∀ r : Fin m → ZMod N.factorial, (∑ i, r i) = 0 →
      |(∏ i, selbergMultiplesCoord N c (addOrderOf (r i))) -
        (∏ i, selbergMultiplesCoord N e (addOrderOf (r i)))| ≤ η)
    (v : Fin m → ℕ) :
    |translatedMoment N c v-translatedMoment N e v| ≤ (N.factorial : ℝ)^m*η := by
  let T : (Fin m → ZMod N.factorial) → ℂ := fun h =>
    translationMoment (residueSignal N (fun d => (c d : ℂ))) h -
      translationMoment (residueSignal N (fun d => (e d : ℂ))) h
  have hT : ∀ r, ‖momentDFT T r‖ ≤ (N.factorial : ℝ)^m*η := by
    intro r
    have he : momentDFT T r =
        momentDFT (translationMoment (residueSignal N (fun d => (c d : ℂ)))) r -
          momentDFT (translationMoment (residueSignal N (fun d => (e d : ℂ)))) r := by
      simp [T, momentDFT, mul_sub, Finset.sum_sub_distrib]
    rw [he, momentDFT_sieve, momentDFT_sieve]
    by_cases hz : (∑ i, r i) = 0
    · simp only [hz, if_true, ← mul_sub, norm_mul, norm_pow]
      have hb : ‖(∏ i, coordinate N (fun d => (c d : ℂ)) (addOrderOf (r i))) -
          (∏ i, coordinate N (fun d => (e d : ℂ)) (addOrderOf (r i)))‖ ≤ η := by
        simpa only [coordinate_ofReal, ← Complex.ofReal_prod, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs] using hp r hz
      simpa using mul_le_mul_of_nonneg_left hb (pow_nonneg (by positivity : (0 : ℝ) ≤ N.factorial) m)
    · simp only [hz, if_false, sub_self, norm_zero]
      positivity
  have hh := momentDFT_sup_bound T ((N.factorial : ℝ)^m*η) hT
    (fun i => (v i : ZMod N.factorial))
  simpa only [T, ← translatedMoment_complex_eq, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using hh

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood

open scoped BigOperators
open Finset
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
open AffineSieve
set_option autoImplicit false
variable {P : ℕ} [NeZero P]

private theorem dft_right_translation (f : ZMod P → ℂ) (t r : ZMod P) :
    ZMod.dft (fun x => f (x+t)) r = ZMod.stdAddChar (t*r)*ZMod.dft f r := by
  rw [ZMod.dft_apply, ZMod.dft_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight t) _ _ (fun x => ?_)
  change ZMod.stdAddChar (-(x*r))*f (x+t) =
    ZMod.stdAddChar (t*r)*(ZMod.stdAddChar (-((x+t)*r))*f (x+t))
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

private theorem dft_difference_bound (f g : ZMod P → ℂ) (D : ℝ)
    (h : ∀ x, ‖f x-g x‖ ≤ D) (r : ZMod P) :
    ‖ZMod.dft f r-ZMod.dft g r‖ ≤ (P : ℝ)*D := by
  rw [ZMod.dft_apply, ZMod.dft_apply, ← Finset.sum_sub_distrib]
  simp only [smul_eq_mul, ← mul_sub]
  calc
    _ ≤ ∑ x : ZMod P, ‖ZMod.stdAddChar (-(x*r))*(f x-g x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : ZMod P, D := by
      apply Finset.sum_le_sum
      intro x _
      simpa [norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe] using h x
    _ = _ := by simp

local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Every normalized Fourier coordinate is bounded by the actual translated sup-error. -/
theorem translated_coordinate_error (N : ℕ) (c e : ℕ → ℝ) (h : ℕ) (D : ℝ)
    (herr : ∀ n, |sieveSeq N e n-sieveSeq N c (n+h)| ≤ D) (r : ZMod N.factorial) :
    ‖(selbergMultiplesCoord N e (addOrderOf r) : ℂ) -
        ZMod.stdAddChar ((h : ZMod N.factorial)*r)*(selbergMultiplesCoord N c (addOrderOf r) : ℂ)‖ ≤ D := by
  have hs (x : ZMod N.factorial) :
      ‖residueSignal N (fun d => (e d : ℂ)) x -
        residueSignal N (fun d => (c d : ℂ)) (x+(h : ZMod N.factorial))‖ ≤ D := by
    have he := residueSignal_sieveSeq N e x.val
    have hc := residueSignal_sieveSeq N c (x.val+h)
    simp only [Nat.cast_add, ZMod.natCast_zmod_val] at he hc
    rw [he, hc, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact herr x.val
  have hb := dft_difference_bound (residueSignal N (fun d => (e d : ℂ)))
    (fun x => residueSignal N (fun d => (c d : ℂ)) (x+(h : ZMod N.factorial))) D hs r
  rw [dft_right_translation, dft_residueSignal, dft_residueSignal,
    coordinate_ofReal, coordinate_ofReal] at hb
  have hfactor :
      (N.factorial : ℂ)*(selbergMultiplesCoord N e (addOrderOf r) : ℂ) -
          ZMod.stdAddChar ((h : ZMod N.factorial)*r)*
            ((N.factorial : ℂ)*(selbergMultiplesCoord N c (addOrderOf r) : ℂ)) =
        (N.factorial : ℂ)*((selbergMultiplesCoord N e (addOrderOf r) : ℂ) -
          ZMod.stdAddChar ((h : ZMod N.factorial)*r)*(selbergMultiplesCoord N c (addOrderOf r) : ℂ)) := by ring
  rw [hfactor, norm_mul] at hb
  have hP : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  simp only [Complex.norm_natCast] at hb
  nlinarith only [hb, hP]

/-- Incompatible translation phases remain separated even before choosing a physical maximizer. -/
theorem phase_incompatibility (z w : ℂ) (p q : ℕ) (hz : ‖z‖ ≤ 1) (hw : ‖w‖ ≤ 1)
    (hq : Odd q) (he : z^p = w^q) :
    2 ≤ (p : ℝ)*‖1-z‖+(q : ℝ)*‖1+w‖ := by
  have hzpow := _root_.RHTower.norm_pow_sub_pow_le_of_norm_le_one
    (by norm_num : ‖(1 : ℂ)‖ ≤ 1) hz p
  have hwpow := _root_.RHTower.norm_pow_sub_pow_le_of_norm_le_one
    hw (by norm_num : ‖(-1 : ℂ)‖ ≤ 1) q
  have htri := norm_add_le ((1 : ℂ)-z^p) (z^p+1)
  rw [show ((1 : ℂ)-z^p)+(z^p+1) = 2 by ring] at htri
  rw [one_pow] at hzpow
  simp only [hq.neg_one_pow, sub_neg_eq_add] at hwpow
  rw [add_comm w] at hwpow
  simp only [he] at htri hzpow
  norm_num at htri
  linarith

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ParityNeighborhood
