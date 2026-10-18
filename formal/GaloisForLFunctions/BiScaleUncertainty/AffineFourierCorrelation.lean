import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring

/-!
# Fourier coefficients of affine correlations and divisor indicators

A Fourier transform in the translation parameter of a literal finite affine
correlation is a product of two source coefficients. Divisor indicators have
exactly the frequencies whose additive order divides their modulus. Both laws
hold on the actual finite cyclic group, including noninvertible dilations.
-/

namespace GaloisForLFunctions.BiScaleUncertainty.AffineSieve
open scoped BigOperators
open Finset ZMod
noncomputable section
set_option autoImplicit false

variable {P : ℕ} [NeZero P]

private theorem dft_translate (f : ZMod P → ℂ) (t r : ZMod P) :
    ZMod.dft (fun b => f (t+b)) r = ZMod.stdAddChar (t*r) * ZMod.dft f r := by
  rw [ZMod.dft_apply, ZMod.dft_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft t) _ _ ?_
  intro b
  change ZMod.stdAddChar (-(b*r)) * f (t+b) =
    ZMod.stdAddChar (t*r) * (ZMod.stdAddChar (-((t+b)*r)) * f (t+b))
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- Normalized bilinear correlation of a finite source with an affine pullback. -/
def correlation (f : ZMod P → ℂ) (a b : ZMod P) : ℂ :=
  (P : ℂ)⁻¹ * ∑ k, f k * f (a*k+b)

/-- Fourier transformation in the translation parameter retains a pair of source coefficients. -/
theorem dft_correlation (f : ZMod P → ℂ) (a r : ZMod P) :
    ZMod.dft (correlation f a) r =
      (P : ℂ)⁻¹ * ZMod.dft f r * ZMod.dft f (-(a*r)) := by
  rw [ZMod.dft_apply]
  simp only [correlation, smul_eq_mul]
  simp_rw [mul_left_comm (ZMod.stdAddChar _) (P : ℂ)⁻¹]
  rw [← Finset.mul_sum, mul_assoc]
  apply congrArg ((P : ℂ)⁻¹ * ·)
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h (k : ZMod P) :
      (∑ b, ZMod.stdAddChar (-(b*r)) * (f k * f (a*k+b))) =
        f k * (ZMod.stdAddChar ((a*k)*r) * ZMod.dft f r) := by
    simp_rw [mul_left_comm _ (f k)]
    rw [← Finset.mul_sum]
    congr 1
    exact dft_translate f (a*k) r
  simp_rw [h]
  calc
    _ = ZMod.dft f r * ∑ k, ZMod.stdAddChar ((a*k)*r) * f k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      congr 1
      rw [ZMod.dft_apply]
      apply Finset.sum_congr rfl
      intro k _
      simp only [smul_eq_mul, mul_neg, neg_neg]
      congr 1
      congr 1
      ring

/-- The actual divisibility indicator on the least nonnegative residue representative. -/
def divisorIndicator (d : ℕ) (k : ZMod P) : ℂ :=
  if d ∣ k.val then 1 else 0

/-- A sum over residues is a literal complete-period sum over natural representatives. -/
theorem sum_zmod_val (f : ℕ → ℂ) :
    (∑ k : ZMod P, f k.val) = ∑ k ∈ Finset.range P, f k := by
  cases P with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ P => exact Fin.sum_univ_eq_sum_range f (P+1)

omit [NeZero P] in
/-- A divisor of the period tests ordinary integer divisibility after reduction. -/
theorem divisorIndicator_natCast {d : ℕ} (hd : d ∣ P) (k : ℕ) :
    divisorIndicator d (k : ZMod P) = if d ∣ k then 1 else 0 := by
  simp only [divisorIndicator, ZMod.val_natCast, Nat.dvd_mod_iff hd]

private theorem divisorIndicator_period {d : ℕ} (hd : d ∣ P) (k : ZMod P) :
    divisorIndicator d ((d : ZMod P)+k) = divisorIndicator d k := by
  have hk : (d : ZMod P)+k = ((d+k.val : ℕ) : ZMod P) := by simp
  rw [hk, divisorIndicator_natCast hd]
  change (if d ∣ d+k.val then (1 : ℂ) else 0) = if d ∣ k.val then 1 else 0
  have hi : d ∣ d+k.val ↔ d ∣ k.val := (Nat.dvd_add_iff_right (dvd_refl d)).symm
  by_cases h : d ∣ k.val
  · rw [if_pos h, if_pos (hi.mpr h)]
  · rw [if_neg h, if_neg (fun h' => h (hi.mp h'))]

private theorem sum_divisorIndicator {d : ℕ} (hd : d ∣ P) :
    (∑ k : ZMod P, divisorIndicator d k) = (P/d : ℕ) := by
  have hshift : (∑ k : ZMod P, divisorIndicator d k) =
      ∑ k : ZMod P, divisorIndicator d (1+k) := by
    symm
    exact Fintype.sum_equiv (Equiv.addLeft (1 : ZMod P)) _ _ (fun _ => rfl)
  rw [hshift]
  have hterm (k : ZMod P) : divisorIndicator d (1+k) =
      if d ∣ k.val+1 then (1 : ℂ) else 0 := by
    have hk : 1+k = ((k.val+1 : ℕ) : ZMod P) := by simp [add_comm]
    rw [hk, divisorIndicator_natCast hd]
  simp_rw [hterm]
  change (∑ k : ZMod P, (fun n : ℕ => if d ∣ n+1 then (1 : ℂ) else 0) k.val) = _
  rw [sum_zmod_val (P := P) (fun n : ℕ => if d ∣ n+1 then (1 : ℂ) else 0)]
  simp only [Finset.sum_boole, Nat.card_multiples]

/-- Exact Fourier support and amplitude of a divisor indicator on a complete period. -/
theorem dft_divisorIndicator {d : ℕ} (hd : d ∣ P) (r : ZMod P) :
    ZMod.dft (divisorIndicator d) r =
      if addOrderOf r ∣ d then ((P/d : ℕ) : ℂ) else 0 := by
  by_cases hr : addOrderOf r ∣ d
  · rw [if_pos hr, ZMod.dft_apply]
    have hdr : (d : ZMod P)*r = 0 := by
      simpa only [nsmul_eq_mul] using (addOrderOf_dvd_iff_nsmul_eq_zero).mp hr
    have hterm (k : ZMod P) :
        ZMod.stdAddChar (-(k*r)) • divisorIndicator d k = divisorIndicator d k := by
      by_cases hk : d ∣ k.val
      · obtain ⟨j, hj⟩ := hk
        have hk' : k = (d : ZMod P)*j := by
          rw [← ZMod.natCast_zmod_val k, hj, Nat.cast_mul]
        have hkr : k*r = 0 := by rw [hk']; calc
          _ = ((d : ZMod P)*r)*j := by ring
          _ = 0 := by rw [hdr, zero_mul]
        simp [hkr]
      · simp [divisorIndicator, hk]
    simp_rw [hterm]
    exact sum_divisorIndicator hd
  · rw [if_neg hr]
    have hc : ZMod.stdAddChar ((d : ZMod P)*r) ≠ 1 := by
      intro hc
      have hdr : (d : ZMod P)*r = 0 := ZMod.injective_stdAddChar (by simpa using hc)
      exact hr ((addOrderOf_dvd_iff_nsmul_eq_zero).mpr (by simpa only [nsmul_eq_mul] using hdr))
    apply eq_zero_of_mul_eq_self_left hc
    have ht := dft_translate (divisorIndicator (P := P) d) (d : ZMod P) r
    rw [show (fun k : ZMod P => divisorIndicator d ((d : ZMod P)+k)) =
      divisorIndicator d from funext (divisorIndicator_period hd)] at ht
    exact ht.symm


end
end GaloisForLFunctions.BiScaleUncertainty.AffineSieve
