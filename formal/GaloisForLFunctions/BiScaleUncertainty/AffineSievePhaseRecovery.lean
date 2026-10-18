import GaloisForLFunctions.BiScaleUncertainty.DivisorSieveAffineSpectrum
import GaloisForLFunctions.BezoutValuationIncidence.PronicBezoutSplitAndPrimePowerIndecomposability

/-!
# Exact phase recovery from actual affine divisor-sieve moments

Literal factorial-period observations of the existing real sieve response
recover exactly products of Selberg coordinates on divisibility edges.
A finite observation family is complete, and the remaining signs are exactly
constant on components of the nonzero divisor graph. Explicit weights at
modes three and five have identical full affine data while their pointwise
absolute amplitudes differ, ruling out even absolute-origin reconstruction.
-/

open scoped BigOperators
open Finset ZMod
open GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.AffineSieve
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩


/-- Literal complete-period correlation of an actual divisor sieve with its affine pullback. -/
def affineMoment (N : ℕ) (c : ℕ → ℝ) (a b : ℕ) : ℝ :=
  (∑ k ∈ Finset.range N.factorial, sieveSeq N c k * sieveSeq N c (a*k+b)) /
    (N.factorial : ℝ)

/-- The finite Fourier coordinate is exactly the existing real Selberg coordinate. -/
theorem coordinate_ofReal (N : ℕ) (c : ℕ → ℝ) (q : ℕ) :
    coordinate N (fun d => (c d : ℂ)) q = (selbergMultiplesCoord N c q : ℂ) := by
  unfold coordinate selbergMultiplesCoord
  rw [Complex.ofReal_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : q ∣ d <;> simp [h]

/-- The finite residue signal is the existing actual sieve response. -/
theorem residueSignal_sieveSeq (N : ℕ) (c : ℕ → ℝ) (k : ℕ) :
    residueSignal N (fun d => (c d : ℂ)) (k : ZMod N.factorial) =
      (sieveSeq N c k : ℂ) := by
  rw [residueSignal_natCast]
  simp only [sieveSeq, Finset.sum_filter, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro d _
  split_ifs <;> simp

/-- The cyclic-group average agrees with the literal real complete-period observation. -/
theorem affineMoment_complex_eq (N : ℕ) (c : ℕ → ℝ) (a b : ℕ) :
    (affineMoment N c a b : ℂ) =
      correlation (residueSignal N (fun d => (c d : ℂ))) (a : ZMod N.factorial) b := by
  unfold affineMoment correlation
  push_cast
  rw [div_eq_mul_inv, mul_comm _ (N.factorial : ℂ)⁻¹]
  apply congrArg ((N.factorial : ℂ)⁻¹ * ·)
  rw [← sum_zmod_val (P := N.factorial)
    (fun k => (sieveSeq N c k : ℂ) * (sieveSeq N c (a*k+b) : ℂ))]
  apply Finset.sum_congr rfl
  intro k _
  have hk : (a : ZMod N.factorial)*k+(b : ZMod N.factorial) =
      ((a*k.val+b : ℕ) : ZMod N.factorial) := by simp
  rw [hk, residueSignal_sieveSeq]
  have hs := residueSignal_sieveSeq N c k.val
  rw [ZMod.natCast_zmod_val] at hs
  rw [hs]

/-- Every measured Fourier coefficient is the exact product of two comparable Selberg modes. -/
theorem dft_affineMoment (N : ℕ) (c : ℕ → ℝ) (a : ℕ) (r : ZMod N.factorial) :
    ZMod.dft (fun b : ZMod N.factorial => (affineMoment N c a b.val : ℂ)) r =
      (N.factorial : ℂ) * (selbergMultiplesCoord N c (addOrderOf r) : ℂ) *
        (selbergMultiplesCoord N c (addOrderOf r / Nat.gcd (addOrderOf r) a) : ℂ) := by
  have hf : (fun b : ZMod N.factorial => (affineMoment N c a b.val : ℂ)) =
      correlation (residueSignal N (fun d => (c d : ℂ))) (a : ZMod N.factorial) := by
    funext b
    simpa only [ZMod.natCast_zmod_val] using affineMoment_complex_eq N c a b.val
  rw [hf, dft_affine_signal, coordinate_ofReal, coordinate_ofReal]

private theorem allDataEqual_real_iff (N : ℕ) (c e : ℕ → ℝ) :
    AllDataEqual N (fun d => (c d : ℂ)) (fun d => (e d : ℂ)) ↔
      ∀ a b, affineMoment N c a b = affineMoment N e a b := by
  constructor
  · intro h a b
    apply Complex.ofReal_injective
    rw [affineMoment_complex_eq, affineMoment_complex_eq]
    exact h a b
  · intro h a b
    rw [← affineMoment_complex_eq, ← affineMoment_complex_eq, h a b]

/-- Complete affine observations recover exactly all comparable divisor-coordinate products. -/
theorem affineMoment_eq_iff_comparable (N : ℕ) (c e : ℕ → ℝ) :
    (∀ a b, affineMoment N c a b = affineMoment N e a b) ↔
      ∀ q ∈ Finset.Icc 1 N, ∀ d ∈ q.divisors,
        selbergMultiplesCoord N c q * selbergMultiplesCoord N c d =
          selbergMultiplesCoord N e q * selbergMultiplesCoord N e d := by
  rw [← allDataEqual_real_iff,
    (allData_iff_finiteData_iff_comparableProducts N _ _).1,
    (allData_iff_finiteData_iff_comparableProducts N _ _).2]
  simp only [ComparableProducts, coordinate_ofReal, ← Complex.ofReal_mul, Complex.ofReal_inj]

/-- Slopes up to the cutoff and one translation period determine every affine observation. -/
theorem affineMoment_finite_complete (N : ℕ) (c e : ℕ → ℝ) :
    (∀ a ∈ Finset.Icc 1 N, ∀ b ∈ Finset.range N.factorial,
      affineMoment N c a b = affineMoment N e a b) ↔
        ∀ a b, affineMoment N c a b = affineMoment N e a b := by
  rw [← allDataEqual_real_iff, (allData_iff_finiteData_iff_comparableProducts N _ _).1]
  simp only [FiniteDataEqual, ← affineMoment_complex_eq, Complex.ofReal_inj]

private theorem cast_signed (ε : Bool) (u v : ℝ) :
    ((v : ℂ) = if ε then (u : ℂ) else -(u : ℂ)) ↔ v = if ε then u else -u := by
  cases ε
  · change ((v : ℂ) = -(u : ℂ)) ↔ v = -u
    rw [← Complex.ofReal_neg, Complex.ofReal_inj]
  · change ((v : ℂ) = (u : ℂ)) ↔ v = u
    exact Complex.ofReal_inj

/-- The exact ambiguity is one sign on each component of the nonzero divisibility graph. -/
theorem affineMoment_eq_iff_signComponents (N : ℕ) (c e : ℕ → ℝ) :
    (∀ a b, affineMoment N c a b = affineMoment N e a b) ↔ ∃ ε : ℕ → Bool,
      (∀ q ∈ Finset.Icc 1 N,
        selbergMultiplesCoord N e q = if ε q then selbergMultiplesCoord N c q else -selbergMultiplesCoord N c q) ∧
      (∀ q ∈ Finset.Icc 1 N, ∀ d ∈ q.divisors,
        selbergMultiplesCoord N c q ≠ 0 → selbergMultiplesCoord N c d ≠ 0 → ε q = ε d) := by
  rw [← allDataEqual_real_iff, allData_iff_signComponents]
  simp only [coordinate_ofReal, cast_signed, SignComponents, Complex.ofReal_ne_zero]

/-- Explicit real weights realizing independent modes three and five. -/
def primePairReal (t : ℝ) (d : ℕ) : ℝ :=
  (if d = 1 then -(1+t) else 0) + (if d = 3 then 3 else 0) + (if d = 5 then 5*t else 0)

/-- The explicit real weights agree with their complex finite-period realization. -/
theorem primePairReal_cast (t : ℝ) (d : ℕ) :
    (primePairReal t d : ℂ) = primePairWeight (t : ℂ) d := by
  change (primePairReal t d : ℂ) =
    (if d = 1 then -((1 : ℂ)+(t : ℂ)) else 0) +
      (if d = 3 then (3 : ℂ) else 0) + (if d = 5 then (5 : ℂ)*(t : ℂ) else 0)
  unfold primePairReal
  split_ifs <;> push_cast <;> ring

/-- Opposite mode-five signs are invisible to every affine quadratic observation. -/
theorem primePairReal_affineMoment_eq (N a b : ℕ) :
    affineMoment (N+5) (primePairReal 1) a b = affineMoment (N+5) (primePairReal (-1)) a b := by
  apply (allDataEqual_real_iff (N+5) _ _).mp
  · simpa only [primePairReal_cast, Complex.ofReal_one, Complex.ofReal_neg] using
      primePairWeight_allDataEqual N

/-- The two-mode family has a literal integer divisibility formula. -/
theorem sieveSeq_primePairReal (N : ℕ) (t : ℝ) (k : ℕ) :
    sieveSeq (N+5) (primePairReal t) k =
      -(1+t) + (if 3 ∣ k then 3 else 0) + (if 5 ∣ k then 5*t else 0) := by
  apply Complex.ofReal_injective
  rw [← residueSignal_sieveSeq]
  simp_rw [primePairReal_cast]
  rw [residueSignal_primePairWeight]
  split_ifs <;> push_cast <;> ring

/-- Identical full affine data can hide different pointwise absolute amplitudes. -/
theorem exists_same_affine_data_distinct_absolute_origin (N : ℕ) :
    ∃ c e : ℕ → ℝ, (∀ a b, affineMoment (N+5) c a b = affineMoment (N+5) e a b) ∧
      sieveSeq (N+5) c 0 = 6 ∧ ∀ k, |sieveSeq (N+5) e k| ≤ 5 := by
  refine ⟨primePairReal 1, primePairReal (-1), primePairReal_affineMoment_eq N, ?_, ?_⟩
  · rw [sieveSeq_primePairReal]
    norm_num
  · intro k
    rw [sieveSeq_primePairReal]
    by_cases h3 : 3 ∣ k <;> by_cases h5 : 5 ∣ k <;> norm_num [h3, h5]

/-- No functional of the complete affine data recovers every absolute origin response. -/
theorem no_absolute_origin_decoder (N : ℕ) :
    ¬∃ decode : (ℕ → ℕ → ℝ) → ℝ,
      ∀ c : ℕ → ℝ, decode (affineMoment (N+5) c) = |sieveSeq (N+5) c 0| := by
  rintro ⟨decode, hdecode⟩
  obtain ⟨c, e, hdata, hc, he⟩ := exists_same_affine_data_distinct_absolute_origin N
  have hf : affineMoment (N+5) c = affineMoment (N+5) e := funext fun a => funext (hdata a)
  have ha : |sieveSeq (N+5) c 0| = |sieveSeq (N+5) e 0| := by
    rw [← hdecode c, ← hdecode e, hf]
  have hbad := he 0
  rw [← ha, hc] at hbad
  norm_num at hbad

end GaloisForLFunctions.BiScaleUncertainty.AffineSieve
