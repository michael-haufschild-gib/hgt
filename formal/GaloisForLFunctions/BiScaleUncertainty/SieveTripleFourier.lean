import GaloisForLFunctions.BiScaleUncertainty.DivisorSieveAffineSpectrum
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Triple divisor-sieve spectra and odd translated moments

The full two-lag Fourier transform reads triangular products of divisor
coordinates. Odd-order coordinates have a diagonal cubic readout. An exact
anti-period cancels every odd-length translated product on the finite group.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
variable {P : ℕ} [NeZero P]

private theorem dft_shift (f : ZMod P → ℂ) (t r : ZMod P) :
    ZMod.dft (fun b => f (t+b)) r = ZMod.stdAddChar (t*r) * ZMod.dft f r := by
  rw [ZMod.dft_apply, ZMod.dft_apply, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addLeft t) _ _ ?_
  intro b
  change ZMod.stdAddChar (-(b*r)) * f (t+b) =
    ZMod.stdAddChar (t*r) * (ZMod.stdAddChar (-((t+b)*r)) * f (t+b))
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

private theorem dft_const_mul (z : ℂ) (f : ZMod P → ℂ) (r : ZMod P) :
    ZMod.dft (fun b => z*f b) r = z*ZMod.dft f r := by
  rw [ZMod.dft_apply, ZMod.dft_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [smul_eq_mul]
  ring

private theorem dft_weighted_shift (u v : ZMod P → ℂ) (r : ZMod P) :
    ZMod.dft (fun b => ∑ n, u n*v (n+b)) r =
      (∑ n, u n*ZMod.stdAddChar (n*r))*ZMod.dft v r := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n _
  calc
    _ = u n * ZMod.dft (fun b => v (n+b)) r := by
      rw [ZMod.dft_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      simp only [smul_eq_mul]
      ring
    _ = _ := by rw [dft_shift]; ring

/-- Literal normalized three-source average with two independent translation lags. -/
def tripleCorrelation (f : ZMod P → ℂ) (h k : ZMod P) : ℂ :=
  (P : ℂ)⁻¹ * ∑ n, f n*f (n+h)*f (n+k)

/-- Unnormalized Fourier transform in both translation variables. -/
def doubleDFT (T : ZMod P → ZMod P → ℂ) (r s : ZMod P) : ℂ :=
  ZMod.dft (fun h => ZMod.dft (T h) s) r

/-- Both translation variables are recovered from their full double transform. -/
theorem doubleDFT_injective :
    Function.Injective (doubleDFT (P := P)) := by
  intro T U h
  funext x y
  have hs (s : ZMod P) :
      (fun x => ZMod.dft (T x) s) = (fun x => ZMod.dft (U x) s) := by
    apply ZMod.dft.injective
    funext r
    exact congrFun (congrFun h r) s
  have hx : ZMod.dft (T x) = ZMod.dft (U x) := by
    funext s
    exact congrFun (hs s) x
  exact congrFun (ZMod.dft.injective hx) y

/-- A triple average retains the three source frequencies forming a closed triangle. -/
theorem doubleDFT_tripleCorrelation (f : ZMod P → ℂ) (r s : ZMod P) :
    doubleDFT (tripleCorrelation f) r s =
      (P : ℂ)⁻¹ * ZMod.dft f r * ZMod.dft f s * ZMod.dft f (-(r+s)) := by
  have hinner (h : ZMod P) :
      ZMod.dft (tripleCorrelation f h) s =
        ((P : ℂ)⁻¹*ZMod.dft f s) *
          ∑ n, (f n*ZMod.stdAddChar (n*s))*f (n+h) := by
    change ZMod.dft (fun k => (P : ℂ)⁻¹ *
      ∑ n, (f n*f (n+h))*f (n+k)) s = _
    rw [dft_const_mul, dft_weighted_shift]
    simp only [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    ring
  unfold doubleDFT
  simp_rw [hinner]
  rw [dft_const_mul, dft_weighted_shift]
  have hs : (∑ n : ZMod P, (f n*ZMod.stdAddChar (n*s))*ZMod.stdAddChar (n*r)) =
      ZMod.dft f (-(r+s)) := by
    rw [ZMod.dft_apply]
    apply Finset.sum_congr rfl
    intro n _
    simp only [smul_eq_mul, mul_neg, neg_neg]
    rw [mul_assoc, ← AddChar.map_add_eq_mul]
    have he : n*s+n*r = n*(r+s) := by ring
    rw [he]
    ring
  rw [hs]
  ring

local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- Exact triangular multiples-coordinate product for the actual divisor signal. -/
theorem doubleDFT_tripleSieve (N : ℕ) (c : ℕ → ℂ) (r s : ZMod N.factorial) :
    doubleDFT (tripleCorrelation (residueSignal N c)) r s =
      (N.factorial : ℂ)^2 * coordinate N c (addOrderOf r) *
        coordinate N c (addOrderOf s) * coordinate N c (addOrderOf (r+s)) := by
  rw [doubleDFT_tripleCorrelation, dft_residueSignal, dft_residueSignal,
    dft_residueSignal, addOrderOf_neg]
  have hP : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero N
  field_simp

/-- Equality of all triple observations is exactly equality of triangular coordinate products. -/
theorem tripleSieve_eq_iff_triangles (N : ℕ) (c e : ℕ → ℂ) :
    tripleCorrelation (residueSignal N c) = tripleCorrelation (residueSignal N e) ↔
      ∀ r s : ZMod N.factorial,
        coordinate N c (addOrderOf r)*coordinate N c (addOrderOf s)*
          coordinate N c (addOrderOf (r+s)) =
        coordinate N e (addOrderOf r)*coordinate N e (addOrderOf s)*
          coordinate N e (addOrderOf (r+s)) := by
  have hP : (N.factorial : ℂ)^2 ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero N)
  constructor
  · intro h r s
    have h' := congrFun (congrFun (congrArg doubleDFT h) r) s
    rw [doubleDFT_tripleSieve, doubleDFT_tripleSieve] at h'
    exact mul_left_cancel₀ hP (by simpa only [mul_assoc] using h')
  · intro h
    apply doubleDFT_injective
    funext r s
    rw [doubleDFT_tripleSieve, doubleDFT_tripleSieve]
    simpa only [mul_assoc] using congrArg ((N.factorial : ℂ)^2 * ·) (h r s)

/-- The factorial-period frequency selected by a positive divisor has that exact order. -/
theorem frequency_order {N q : ℕ} (hq : q ∈ Finset.Icc 1 N) :
    addOrderOf ((N.factorial / q : ℕ) : ZMod N.factorial) = q := by
  have hd := Nat.dvd_factorial (Finset.mem_Icc.mp hq).1 (Finset.mem_Icc.mp hq).2
  rw [ZMod.addOrderOf_coe _ (Nat.factorial_ne_zero N),
    Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd), Nat.div_div_self hd (Nat.factorial_ne_zero N)]

/-- At an odd-order mode the diagonal double transform reads its signed cube. -/
theorem odd_order_diagonal (N : ℕ) (c : ℕ → ℂ) {q : ℕ}
    (hq : q ∈ Finset.Icc 1 N) (hodd : Odd q) :
    doubleDFT (tripleCorrelation (residueSignal N c))
      ((N.factorial/q : ℕ) : ZMod N.factorial) ((N.factorial/q : ℕ) : ZMod N.factorial) =
        (N.factorial : ℂ)^2 * coordinate N c q ^ 3 := by
  let r : ZMod N.factorial := (N.factorial/q : ℕ)
  have hr : addOrderOf r = q := frequency_order hq
  have hg : Nat.gcd q 2 = 1 := hodd.coprime_two_right
  have hrr : addOrderOf (r+r) = q := by
    simpa only [two_nsmul, hr, hg, Nat.div_one] using (addOrderOf_nsmul (n := 2) r)
  change doubleDFT (tripleCorrelation (residueSignal N c)) r r = _
  rw [doubleDFT_tripleSieve, hr, hrr]
  ring

/-- Literal complete-period average of a finite family of translated source values. -/
def translationMoment (f : ZMod P → ℂ) {m : ℕ} (h : Fin m → ZMod P) : ℂ :=
  (P : ℂ)⁻¹ * ∑ n, ∏ i, f (n+h i)

/-- A sign-reversing period annihilates every odd-length translated moment. -/
theorem translationMoment_of_antiperiodic (f : ZMod P → ℂ) (t : ZMod P)
    (ht : ∀ n, f (n+t) = -f n) (m : ℕ) (h : Fin (2*m+1) → ZMod P) :
    translationMoment f h = 0 := by
  let w : ZMod P → ℂ := fun n => ∏ i, f (n+h i)
  have hw (n : ZMod P) : w (n+t) = -w n := by
    have hn (i : Fin (2*m+1)) : f (n+t+h i) = -f (n+h i) := by
      rw [show n+t+h i = (n+h i)+t by ring, ht]
    simp only [w, hn]
    rw [Finset.prod_neg]
    simp [pow_add, pow_mul]
  have hs : (∑ n, w n) = -(∑ n, w n) := by
    calc
      _ = ∑ n : ZMod P, w (n+t) := by
        symm
        exact Fintype.sum_equiv (Equiv.addRight t) _ _ (fun _ => rfl)
      _ = _ := by simp_rw [hw]; rw [Finset.sum_neg_distrib]
  have hz : (2 : ℂ)*(∑ n, w n) = 0 := by
    calc
      _ = (∑ n, w n) - (-(∑ n, w n)) := by ring
      _ = 0 := by rw [← hs, sub_self]
  have hw0 : (∑ n, w n) = 0 := (mul_eq_zero.mp hz).resolve_left two_ne_zero
  change (P : ℂ)⁻¹ * (∑ n, w n) = 0
  rw [hw0, mul_zero]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
