import Mathlib.Analysis.Fourier.ZMod

/-!
# Period invariance forces finite Fourier support

Translation by a period acts diagonally after finite Fourier transform. Any
frequency whose additive character detects that translation has coefficient
zero. This is the structural support theorem behind residue-to-Farey transfer.
-/

noncomputable section
open scoped BigOperators

namespace RHTower.Sieve

theorem dft_eq_shift_phase_mul {P : ℕ} [NeZero P]
    (f : ZMod P → ℂ) (h k : ZMod P)
    (hper : ∀ x, f (x + h) = f x) :
    ZMod.dft f k = ZMod.stdAddChar (-(h * k)) * ZMod.dft f k := by
  have hshift :
      (∑ x : ZMod P, ZMod.stdAddChar (-(x * k)) * f x) =
        ∑ x : ZMod P,
          ZMod.stdAddChar (-((x + h) * k)) * f (x + h) := by
    exact (Fintype.sum_equiv (Equiv.addRight h)
      (fun x : ZMod P => ZMod.stdAddChar (-((x + h) * k)) * f (x + h))
      (fun y : ZMod P => ZMod.stdAddChar (-(y * k)) * f y)
      (fun x => rfl)).symm
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul]
  calc
    (∑ x : ZMod P, ZMod.stdAddChar (-(x * k)) * f x) =
      ∑ x : ZMod P,
        ZMod.stdAddChar (-((x + h) * k)) * f (x + h) := hshift
    _ = ZMod.stdAddChar (-(h * k)) *
          ∑ x : ZMod P, ZMod.stdAddChar (-(x * k)) * f x := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [hper]
      rw [show -((x + h) * k) = -(h * k) + -(x * k) by ring,
        AddChar.map_add_eq_mul]
      ring

theorem dft_eq_zero_of_periodic_nontrivial_phase {P : ℕ} [NeZero P]
    (f : ZMod P → ℂ) (h k : ZMod P)
    (hper : ∀ x, f (x + h) = f x)
    (hne : ZMod.stdAddChar (-(h * k)) ≠ 1) :
    ZMod.dft f k = 0 := by
  have heq := dft_eq_shift_phase_mul f h k hper
  have hz : (1 - ZMod.stdAddChar (-(h * k))) * ZMod.dft f k = 0 := by
    calc
      _ = ZMod.dft f k - ZMod.stdAddChar (-(h * k)) * ZMod.dft f k := by ring
      _ = 0 := sub_eq_zero.mpr heq
  rcases mul_eq_zero.mp hz with h | h
  · exact (hne (sub_eq_zero.mp h).symm).elim
  · exact h

/-- A signal lifted from modulus `d` to any divisible period `P` has no
Fourier coefficient at a frequency detecting translation by `d`. -/
theorem dft_periodic_lift_eq_zero {P d : ℕ} [NeZero P] [NeZero d]
    (hdvd : d ∣ P) (a : ZMod d → ℂ) (k : ZMod P)
    (hfreq : ZMod.stdAddChar (-((d : ZMod P) * k)) ≠ 1) :
    ZMod.dft (fun x : ZMod P => a (ZMod.castHom hdvd (ZMod d) x)) k = 0 := by
  let c : ZMod P →+* ZMod d := ZMod.castHom hdvd (ZMod d)
  have hper (x : ZMod P) : a (c (x + d)) = a (c x) := by
    rw [map_add]
    have hdz : c (d : ZMod P) = 0 := by
      simp [c]
    rw [hdz, add_zero]
  exact dft_eq_zero_of_periodic_nontrivial_phase
    (fun x : ZMod P => a (c x)) (d : ZMod P) k hper hfreq

/-- A periodic shift is invisible to the standard character exactly when
the ambient period divides the integer frequency product. -/
theorem stdAddChar_neg_nat_mul_eq_one_iff_dvd
    (P d k : ℕ) [NeZero P] :
    ZMod.stdAddChar (-((d : ZMod P) * (k : ZMod P))) = 1 ↔
      P ∣ d * k := by
  have hchar (x : ZMod P) : ZMod.stdAddChar x = 1 ↔ x = 0 := by
    constructor
    · intro h
      apply ZMod.injective_stdAddChar
      simpa using h
    · intro h
      simp [h]
  rw [hchar, neg_eq_zero]
  norm_cast
  exact ZMod.natCast_eq_zero_iff (d * k) P

/-- Exact arithmetic Fourier support of a signal lifted from modulus `d`. -/
theorem dft_periodic_lift_eq_zero_of_not_dvd {P d : ℕ} [NeZero P] [NeZero d]
    (hdvd : d ∣ P) (a : ZMod d → ℂ) (k : ℕ)
    (hnot : ¬ P ∣ d * k) :
    ZMod.dft (fun x : ZMod P => a (ZMod.castHom hdvd (ZMod d) x))
      (k : ZMod P) = 0 := by
  apply dft_periodic_lift_eq_zero hdvd a (k : ZMod P)
  intro hphase
  exact hnot ((stdAddChar_neg_nat_mul_eq_one_iff_dvd P d k).mp hphase)

/-- A finite superposition of periodic components has no Fourier mass at
frequencies outside every component's arithmetic annihilator. -/
theorem dft_sum_periodic_eq_zero_of_no_resonance
    {P : ℕ} [NeZero P] (S : Finset ℕ) (a : ℕ → ℂ)
    (f : ℕ → ZMod P → ℂ) (k : ℕ)
    (hper : ∀ d ∈ S, ∀ x, f d (x + (d : ZMod P)) = f d x)
    (hnot : ∀ d ∈ S, ¬ P ∣ d * k) :
    ZMod.dft (∑ d ∈ S, a d • f d) (k : ZMod P) = 0 := by
  have hzero (d : ℕ) (hd : d ∈ S) :
      ZMod.dft (f d) (k : ZMod P) = 0 := by
    apply dft_eq_zero_of_periodic_nontrivial_phase (f d) (d : ZMod P)
      (k : ZMod P) (hper d hd)
    intro hchar
    exact hnot d hd ((stdAddChar_neg_nat_mul_eq_one_iff_dvd P d k).mp hchar)
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply]
  exact Finset.sum_eq_zero (fun d hd => by simp [hzero d hd])

/-- A resonance `P ∣ d k` forces the reduced denominator of `k/P` to
divide the source modulus `d`. -/
theorem reduced_denominator_dvd_modulus_of_resonance
    {P k d : ℕ} (hP : 0 < P) (hres : P ∣ d * k) :
    P / Nat.gcd P k ∣ d := by
  have hg : 0 < Nat.gcd P k := Nat.gcd_pos_of_pos_left k hP
  have hgd : P ∣ d * Nat.gcd P k :=
    dvd_mul_gcd_of_dvd_mul hres
  apply Nat.dvd_of_mul_dvd_mul_right hg
  have hPfact : (P / Nat.gcd P k) * Nat.gcd P k = P :=
    Nat.div_mul_cancel (Nat.gcd_dvd_left P k)
  rw [hPfact]
  exact hgd

end RHTower.Sieve
