import GaloisForLFunctions.RHTower.EulerDeletionResidueFourierCoefficient
import Mathlib.Analysis.Fourier.ZMod

/-!
# Literal centered-residue finite DFT coefficient

The exact weighted-geometric coefficient is identified with the discrete
Fourier transform of the normalized residue signal on `ZMod d`. This is the
finite-signal interface for Farey-frequency regrouping of the signed source.
-/

noncomputable section
open Finset
open scoped BigOperators

namespace RHTower.Sieve

def normalizedResidueSignal (d : ℕ) [NeZero d] (r : ZMod d) : ℂ :=
  (r.val : ℂ) / (d : ℂ) - ((d : ℂ) - 1) / (2 * (d : ℂ))

private theorem sum_zmod_natCast {d : ℕ} [NeZero d] (f : ZMod d → ℂ) :
    (∑ r : ZMod d, f r) = ∑ r ∈ Finset.range d, f (r : ZMod d) := by
  have hfinEquiv (r : Fin d) : ZMod.finEquiv d r = (r.val : ZMod d) := by
    cases d with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ d =>
        apply ZMod.val_injective
        change r.val = r.val % (d + 1)
        rw [Nat.mod_eq_of_lt r.isLt]
  calc
    (∑ r : ZMod d, f r) = ∑ r : Fin d, f (ZMod.finEquiv d r) :=
      ((ZMod.finEquiv d).sum_comp f).symm
    _ = ∑ r : Fin d, f (r.val : ZMod d) := by simp_rw [hfinEquiv]
    _ = ∑ r ∈ Finset.range d, f (r : ZMod d) := by
      exact Fin.sum_univ_eq_sum_range (fun r : ℕ => f (r : ZMod d)) d

private theorem stdAddChar_mul_natCast_eq_root
    (d r t : ℕ) [NeZero d] :
    ZMod.stdAddChar ((r : ZMod d) * (t : ZMod d)) =
      ((rootOfUnity d) ^ t) ^ r := by
  have hcast : (r : ZMod d) * (t : ZMod d) = ((r * t : ℕ) : ZMod d) := by norm_cast
  rw [hcast]
  have hchar :
      ZMod.stdAddChar ((r * t : ℕ) : ZMod d) =
        Complex.exp (2 * Real.pi * Complex.I * (r * t : ℕ) / d) := by
    simpa using (ZMod.stdAddChar_coe (N := d) ((r * t : ℕ) : ℤ))
  rw [hchar, ← pow_mul, rootOfUnity_pow]
  congr 1
  push_cast
  ring

theorem dft_normalizedResidueSignal_neg (d t : ℕ) [NeZero d] (hd : 0 < d)
    (ht0 : 0 < t) (htd : t < d) :
    ZMod.dft (normalizedResidueSignal d) (-(t : ZMod d)) =
      -1 / (1 - (rootOfUnity d) ^ t) := by
  letI : NeZero d := ⟨hd.ne'⟩
  rw [ZMod.dft_apply]
  have hsign (r : ZMod d) : -(r * -(t : ZMod d)) = r * (t : ZMod d) := by ring
  simp_rw [hsign, smul_eq_mul]
  rw [sum_zmod_natCast]
  have hsum :
      (∑ r ∈ Finset.range d,
        ZMod.stdAddChar ((r : ZMod d) * (t : ZMod d)) *
          normalizedResidueSignal d (r : ZMod d)) =
        ∑ r ∈ Finset.range d,
          ((r : ℂ) / (d : ℂ) - ((d : ℂ) - 1) / (2 * (d : ℂ))) *
            ((rootOfUnity d) ^ t) ^ r := by
    apply Finset.sum_congr rfl
    intro r hr
    rw [stdAddChar_mul_natCast_eq_root]
    simp only [normalizedResidueSignal, ZMod.val_natCast,
      Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
    ring
  rw [hsum]
  have hcoeff := centered_residue_fourier_root d t hd ht0 htd
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hprim := isPrimitiveRoot_rootOfUnity hd.ne'
  have hfreq : (rootOfUnity d) ^ t ≠ 1 := by
    intro h
    have hdvd := (hprim.pow_eq_one_iff_dvd t).mp h
    have hle := Nat.le_of_dvd ht0 hdvd
    omega
  have hden : 1 - (rootOfUnity d) ^ t ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hfreq)
  have hmul : (d : ℂ) * (1 / (d : ℂ)) = 1 := by field_simp
  calc
    (∑ r ∈ Finset.range d,
        ((r : ℂ) / (d : ℂ) - ((d : ℂ) - 1) / (2 * (d : ℂ))) *
          ((rootOfUnity d) ^ t) ^ r) =
        (d : ℂ) * ((1 / (d : ℂ)) *
          ∑ r ∈ Finset.range d,
            ((r : ℂ) / (d : ℂ) - ((d : ℂ) - 1) / (2 * (d : ℂ))) *
              ((rootOfUnity d) ^ t) ^ r) := by
      simp only [← mul_assoc, hmul, one_mul]
    _ = (d : ℂ) * (-1 / ((d : ℂ) * (1 - (rootOfUnity d) ^ t))) := by rw [hcoeff]
    _ = -1 / (1 - (rootOfUnity d) ^ t) := by field_simp

theorem dft_normalizedResidueSignal_zero (d : ℕ) [NeZero d] (hd : 0 < d) :
    ZMod.dft (normalizedResidueSignal d) 0 = 0 := by
  rw [ZMod.dft_apply_zero, sum_zmod_natCast]
  have hsignal (r : ℕ) (hr : r ∈ Finset.range d) :
      normalizedResidueSignal d (r : ZMod d) =
        (r : ℂ) / (d : ℂ) - ((d : ℂ) - 1) / (2 * (d : ℂ)) := by
    simp [normalizedResidueSignal, ZMod.val_natCast,
      Nat.mod_eq_of_lt (Finset.mem_range.mp hr)]
  rw [Finset.sum_congr rfl hsignal]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hsumNat := Finset.sum_range_id_mul_two d
  have hsumC :
      (∑ r ∈ Finset.range d, (r : ℂ)) * 2 =
        (d : ℂ) * ((d : ℂ) - 1) := by
    have h := congrArg (fun n : ℕ => (n : ℂ)) hsumNat
    simp only [Nat.cast_mul, Nat.cast_sum, Nat.cast_ofNat] at h
    have hsub : (((d - 1 : ℕ) : ℂ)) = (d : ℂ) - 1 := by
      have hcast : (((d - 1 : ℕ) : ℂ)) + 1 = (d : ℂ) := by
        exact_mod_cast Nat.sub_add_cancel hd
      linear_combination hcast
    simpa [hsub] using h
  field_simp [hdC]
  linear_combination hsumC

end RHTower.Sieve
