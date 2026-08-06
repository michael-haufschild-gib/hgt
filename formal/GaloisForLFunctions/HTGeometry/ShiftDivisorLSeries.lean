import GaloisForLFunctions.HTGeometry.ShiftDivisorReflection
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.LSeries.Linearity

/-!
# Dirichlet symbol of a shift divisor

A finitely supported complex divisor `w` of shifts acts on Dirichlet coefficient streams by
multiplication by its **symbol** `n ↦ ∑ a w a * n ^ (-a)`.  On the region where every translate
`s + a` is in the half-plane of absolute convergence, the L-series of the twisted stream is exactly
the divisor-weighted family of translates of the original L-series:

  `LSeries (shiftDivisorStream w f) s = ∑ a w a * LSeries f (s + a)`.

Divisor reflection about `c / 2` acts on symbols by the arithmetic inversion `n ^ (-a) ↦ n ^ a`
followed by the single twist `n ^ (-c)`.  Thus a reflection eigen-divisor on the analytic side is a
symbol with a prescribed behaviour under `n ↦ n⁻¹` on the arithmetic side.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Dirichlet symbol of a finite shift divisor. -/
def shiftDivisorSymbol (w : ℂ →₀ ℂ) (n : ℕ) : ℂ :=
  w.sum fun a m => m * (n : ℂ) ^ (-a)

/-- Coefficient stream twisted by the Dirichlet symbol of a shift divisor. -/
def shiftDivisorStream (w : ℂ →₀ ℂ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  shiftDivisorSymbol w n * f n

@[simp]
theorem shiftDivisorSymbol_single (a m : ℂ) (n : ℕ) :
    shiftDivisorSymbol (Finsupp.single a m) n = m * (n : ℂ) ^ (-a) := by
  rw [shiftDivisorSymbol, Finsupp.sum_single_index (by ring)]

theorem shiftDivisorSymbol_sub (v w : ℂ →₀ ℂ) (n : ℕ) :
    shiftDivisorSymbol (v - w) n = shiftDivisorSymbol v n - shiftDivisorSymbol w n :=
  Finsupp.sum_sub_index (by intro a b₁ b₂; ring)

theorem shiftDivisorSymbol_smul (m : ℂ) (w : ℂ →₀ ℂ) (n : ℕ) :
    shiftDivisorSymbol (m • w) n = m * shiftDivisorSymbol w n := by
  rw [shiftDivisorSymbol, Finsupp.sum_smul_index' (by intro a; ring), shiftDivisorSymbol,
    Finsupp.mul_sum]
  exact Finsupp.sum_congr fun a _ => by ring

/-- Weighting a coefficient stream by `n ^ (-a)` translates every individual L-series term. -/
theorem term_cpow_shift (a s : ℂ) (f : ℕ → ℂ) (n : ℕ) :
    LSeries.term (fun m : ℕ => (m : ℂ) ^ (-a) * f m) s n = LSeries.term f (s + a) n := by
  by_cases hn : n = 0
  · simp [hn]
  · have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
    have h1 : (n : ℂ) ^ s ≠ 0 := by
      simp [Complex.cpow_eq_zero_iff, hn']
    have h2 : (n : ℂ) ^ a ≠ 0 := by
      simp [Complex.cpow_eq_zero_iff, hn']
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn,
      Complex.cpow_add _ _ hn', Complex.cpow_neg]
    field_simp

/-- Weighting by `n ^ (-a)` is exactly translation of the Dirichlet variable, for summability. -/
theorem LSeriesSummable_cpow_shift_iff (a s : ℂ) (f : ℕ → ℂ) :
    LSeriesSummable (fun m : ℕ => (m : ℂ) ^ (-a) * f m) s ↔ LSeriesSummable f (s + a) :=
  summable_congr (term_cpow_shift a s f)

/-- Weighting by `n ^ (-a)` is exactly translation of the Dirichlet variable. -/
theorem LSeries_cpow_shift (a s : ℂ) (f : ℕ → ℂ) :
    LSeries (fun m : ℕ => (m : ℂ) ^ (-a) * f m) s = LSeries f (s + a) :=
  tsum_congr (term_cpow_shift a s f)

theorem shiftDivisorStream_eq_sum (w : ℂ →₀ ℂ) (f : ℕ → ℂ) :
    shiftDivisorStream w f =
      ∑ a ∈ w.support, (w a) • fun m : ℕ => (m : ℂ) ^ (-a) * f m := by
  funext n
  simp only [shiftDivisorStream, shiftDivisorSymbol, Finsupp.sum, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **Divisor Dirichlet symbol law.** Twisting a coefficient stream by the Dirichlet symbol of a
shift divisor is exactly forming the divisor-weighted family of translates of its L-series. -/
theorem LSeries_shiftDivisorStream (w : ℂ →₀ ℂ) (f : ℕ → ℂ) (s : ℂ)
    (hs : ∀ a ∈ w.support, LSeriesSummable f (s + a)) :
    LSeries (shiftDivisorStream w f) s = shiftDivisorValue w (fun z => LSeries f z) s := by
  have hsum : ∀ a ∈ w.support,
      LSeriesSummable ((w a) • fun m : ℕ => (m : ℂ) ^ (-a) * f m) s := fun a ha =>
    LSeriesSummable.smul (w a) ((LSeriesSummable_cpow_shift_iff a s f).mpr (hs a ha))
  rw [shiftDivisorStream_eq_sum, LSeries_sum hsum, shiftDivisorValue, Finsupp.sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [LSeries_smul, LSeries_cpow_shift]

/-- Summability of the divisor-twisted stream from summability of all its translates. -/
theorem LSeriesSummable_shiftDivisorStream (w : ℂ →₀ ℂ) (f : ℕ → ℂ) (s : ℂ)
    (hs : ∀ a ∈ w.support, LSeriesSummable f (s + a)) :
    LSeriesSummable (shiftDivisorStream w f) s := by
  rw [shiftDivisorStream_eq_sum]
  exact LSeriesSummable.sum fun a ha =>
    LSeriesSummable.smul (w a) ((LSeriesSummable_cpow_shift_iff a s f).mpr (hs a ha))

/-- **Symbol reflection dictionary.** Reflecting a shift divisor inverts its Dirichlet symbol:
the weights `n ^ (-a)` become `n ^ a`, twisted by the single factor `n ^ (-c)`. -/
theorem shiftDivisorSymbol_reflectShiftDivisor (c : ℂ) (w : ℂ →₀ ℂ) {n : ℕ} (hn : n ≠ 0) :
    shiftDivisorSymbol (reflectShiftDivisor c w) n =
      (n : ℂ) ^ (-c) * w.sum fun a m => m * (n : ℂ) ^ a := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [shiftDivisorSymbol, reflectShiftDivisor, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (by intro b; ring) (by intro b m₁ m₂; ring),
    Finsupp.mul_sum]
  refine Finsupp.sum_congr fun a _ => ?_
  have : -((Equiv.subLeft c) a) = -c + a := by
    norm_num
    ring
  rw [this, Complex.cpow_add _ _ hn']
  ring

/-- **Symbol inversion law for reflection eigen-divisors.** A divisor that is an eigenvector of the
reflection about `c / 2` has a Dirichlet symbol obeying the inversion functional equation with the
same eigenvalue. -/
theorem shiftDivisorSymbol_of_reflect_eq_smul {c η : ℂ} {w : ℂ →₀ ℂ}
    (hw : reflectShiftDivisor c w = η • w) {n : ℕ} (hn : n ≠ 0) :
    (n : ℂ) ^ (-c) * (w.sum fun a m => m * (n : ℂ) ^ a) = η * shiftDivisorSymbol w n := by
  rw [← shiftDivisorSymbol_reflectShiftDivisor c w hn, hw, shiftDivisorSymbol_smul]

end

end GaloisForLFunctions.HTGeometry
