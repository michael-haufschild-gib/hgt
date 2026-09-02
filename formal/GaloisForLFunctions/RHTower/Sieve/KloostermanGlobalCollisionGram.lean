import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionParseval
import GaloisForLFunctions.RHTower.Sieve.KloostermanTransform
import GaloisForLFunctions.RHTower.Sieve.KloostermanSameModulusIntervalCompletion

/-!
# Per-modulus Gram factorization of global Kloosterman collision time slices

The common-period phase splits into one factor from each modulus.  Consequently every explicit
global collision time slice is an erased-diagonal Gram form of single-modulus source responses.
The responses are then identified with the corpus's existing complete Kloosterman transform.
All statements are exact finite identities.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- A negative global cross frequency separates into the powered unit phases of its two stored
moduli. -/
theorem stdAddChar_neg_globalCrossPhaseFrequency_mul
    (Q : Finset ℕ) (q r : ℕ) (hq : q ∈ Q) (hr : r ∈ Q)
    (x : (ZMod (q + 1))ˣ) (y : (ZMod (r + 1))ˣ)
    (k : ZMod (kloostermanGlobalPeriod Q)) :
    ZMod.stdAddChar
        (-(kloostermanGlobalCrossPhaseFrequency Q q r x y * k)) =
      (ZMod.stdAddChar (x : ZMod (q + 1))) ^ k.val *
        star ((ZMod.stdAddChar (y : ZMod (r + 1))) ^ k.val) := by
  have hmul :
      kloostermanGlobalCrossPhaseFrequency Q q r x y * k =
        k.val • kloostermanGlobalCrossPhaseFrequency Q q r x y := by
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
    ring
  rw [AddChar.map_neg_eq_conj, hmul,
    stdAddChar_nsmul_eq_pow,
    kloostermanGlobalCrossPhaseFrequency_phase Q q r hq hr x y]
  unfold kloostermanCrossPhaseRatio
  change star ((star (ZMod.stdAddChar (x : ZMod (q + 1))) *
      ZMod.stdAddChar (y : ZMod (r + 1))) ^ k.val) = _
  rw [star_pow, star_mul, star_star, mul_pow, star_pow]
  ring

/-- One source's complete unit response at a natural time. -/
def kloostermanGlobalModulusTimeResponse
    (q : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ x : (ZMod (q + 1))ˣ,
    kloostermanSourceFourier (q + 1) B b x *
      star ((ZMod.stdAddChar (x : ZMod (q + 1))) ^ n)

private theorem kloostermanUnitFourierCoeff_sourceResidue_inv
    (q : ℕ) (B : Finset ℕ) (b : ℕ → ℂ)
    (x : (ZMod (q + 1))ˣ) :
    kloostermanUnitFourierCoeff (q + 1)
        (kloostermanSourceResidue (q + 1) B b)
        (x⁻¹ : (ZMod (q + 1))ˣ) =
      kloostermanSourceFourier (q + 1) B b x := by
  rw [kloostermanSourceFourier_eq_full_inverse,
    kloostermanSourceFourierFull_eq_residueFourier]
  unfold kloostermanUnitFourierCoeff
  apply Fintype.sum_congr
  intro z
  congr 2
  ring

/-- The single-modulus response is exactly the existing complete Kloosterman transform of the
source compressed by residue class, evaluated at the negative time residue. -/
theorem kloostermanGlobalModulusTimeResponse_eq_kloostermanTransform
    (q : ℕ) (B : Finset ℕ) (b : ℕ → ℂ) (n : ℕ) :
    kloostermanGlobalModulusTimeResponse q B b n =
      kloostermanTransform (q + 1)
        (kloostermanSourceResidue (q + 1) B b)
        (-(n : ZMod (q + 1))) := by
  rw [kloostermanTransform_eq_unitFourier]
  let e : (ZMod (q + 1))ˣ ≃ (ZMod (q + 1))ˣ :=
    Equiv.inv (ZMod (q + 1))ˣ
  let f : (ZMod (q + 1))ˣ → ℂ := fun u =>
    kloostermanUnitFourierCoeff (q + 1)
        (kloostermanSourceResidue (q + 1) B b) u *
      ZMod.stdAddChar
        ((-(n : ZMod (q + 1))) * ((u⁻¹ : (ZMod (q + 1))ˣ) : ZMod (q + 1)))
  change (∑ x : (ZMod (q + 1))ˣ,
      kloostermanSourceFourier (q + 1) B b x *
        star ((ZMod.stdAddChar (x : ZMod (q + 1))) ^ n)) =
    ∑ u : (ZMod (q + 1))ˣ, f u
  rw [← e.sum_comp f]
  apply Fintype.sum_congr
  intro x
  simp only [e, f, Equiv.inv_apply, inv_inv]
  rw [kloostermanUnitFourierCoeff_sourceResidue_inv]
  congr 1
  rw [star_pow, star_stdAddChar_eq_neg, ← stdAddChar_nsmul_eq_pow]
  congr 1
  rw [nsmul_eq_mul]
  ring

/-- Over the global period, one modulus response repeats its complete local Kloosterman-transform
energy exactly `P(Q)/(q+1)` times. -/
theorem sum_normSq_kloostermanGlobalModulusTimeResponse_eq
    (Q : Finset ℕ) (q : ℕ) (hq : q ∈ Q)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ k : ZMod (kloostermanGlobalPeriod Q),
      Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val)) =
      (kloostermanGlobalPeriod Q / (q + 1)) •
        ∑ z : ZMod (q + 1),
          Complex.normSq
            (kloostermanTransform (q + 1)
              (kloostermanSourceResidue (q + 1) B b) (-z)) := by
  simp_rw [kloostermanGlobalModulusTimeResponse_eq_kloostermanTransform]
  exact sum_zmod_lift_eq_nsmul_of_dvd
    (kloostermanGlobalPeriod Q) (q + 1)
    (succ_dvd_kloostermanGlobalPeriod Q hq)
    (fun z : ZMod (q + 1) =>
      Complex.normSq
        (kloostermanTransform (q + 1)
          (kloostermanSourceResidue (q + 1) B b) (-z)))

/-- The repeated single-modulus response energy obeys the sharp complete Kloosterman-transform
bound already present in the corpus. -/
theorem sum_normSq_kloostermanGlobalModulusTimeResponse_le
    (Q : Finset ℕ) (q : ℕ) (hq : q ∈ Q)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    (∑ k : ZMod (kloostermanGlobalPeriod Q),
      Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val)) ≤
      ((kloostermanGlobalPeriod Q / (q + 1) : ℕ) : ℝ) *
        ((q + 1 : ℕ) : ℝ) ^ 2 *
          ∑ z : ZMod (q + 1),
            Complex.normSq (kloostermanSourceResidue (q + 1) B b z) := by
  rw [sum_normSq_kloostermanGlobalModulusTimeResponse_eq Q q hq]
  have hneg :
      (∑ z : ZMod (q + 1),
        Complex.normSq
          (kloostermanTransform (q + 1)
            (kloostermanSourceResidue (q + 1) B b) (-z))) =
        ∑ z : ZMod (q + 1),
          Complex.normSq
            (kloostermanTransform (q + 1)
              (kloostermanSourceResidue (q + 1) B b) z) := by
    let e : ZMod (q + 1) ≃ ZMod (q + 1) := Equiv.neg (ZMod (q + 1))
    exact e.sum_comp (fun z : ZMod (q + 1) =>
      Complex.normSq
        (kloostermanTransform (q + 1)
          (kloostermanSourceResidue (q + 1) B b) z))
  rw [hneg]
  simp only [nsmul_eq_mul]
  simpa only [mul_assoc] using
    (mul_le_mul_of_nonneg_left
      (sum_normSq_kloostermanTransform_le (q + 1)
        (kloostermanSourceResidue (q + 1) B b))
      (Nat.cast_nonneg (kloostermanGlobalPeriod Q / (q + 1))))

/-- After normalization by the global period, the repeated response costs only one modulus times
the exact source residue energy; the least-common-multiple carrier cancels completely. -/
theorem average_normSq_kloostermanGlobalModulusTimeResponse_le
    (Q : Finset ℕ) (q : ℕ) (hq : q ∈ Q)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) ≤
      ((q + 1 : ℕ) : ℝ) *
        ∑ z : ZMod (q + 1),
          Complex.normSq (kloostermanSourceResidue (q + 1) B b z) := by
  have hsum := sum_normSq_kloostermanGlobalModulusTimeResponse_le Q q hq B b
  have hperiodR : (kloostermanGlobalPeriod Q : ℝ) ≠ 0 := by
    exact_mod_cast (kloostermanGlobalPeriod_pos Q).ne'
  have hquotient :
      (((kloostermanGlobalPeriod Q / (q + 1) : ℕ) : ℝ) *
        ((q + 1 : ℕ) : ℝ)) =
        (kloostermanGlobalPeriod Q : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel (succ_dvd_kloostermanGlobalPeriod Q hq)
  calc
    (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          Complex.normSq (kloostermanGlobalModulusTimeResponse q B b k.val) ≤
        (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
          (((kloostermanGlobalPeriod Q / (q + 1) : ℕ) : ℝ) *
            ((q + 1 : ℕ) : ℝ) ^ 2 *
              ∑ z : ZMod (q + 1),
                Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        (((kloostermanGlobalPeriod Q / (q + 1) : ℕ) : ℝ) *
          ((q + 1 : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ) *
            ∑ z : ZMod (q + 1),
              Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) := by ring
    _ = (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ((kloostermanGlobalPeriod Q : ℝ) * ((q + 1 : ℕ) : ℝ) *
          ∑ z : ZMod (q + 1),
            Complex.normSq (kloostermanSourceResidue (q + 1) B b z)) := by
      rw [hquotient]
    _ = ((q + 1 : ℕ) : ℝ) *
        ∑ z : ZMod (q + 1),
          Complex.normSq (kloostermanSourceResidue (q + 1) B b z) := by
      field_simp

/-- A single modulus pair in the explicit time slice is the Gram product of its two
single-modulus responses. -/
theorem sum_globalCrossPhase_eq_modulusTimeResponse
    (Q : Finset ℕ) (q r : ℕ) (hq : q ∈ Q) (hr : r ∈ Q)
    (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ)
    (k : ZMod (kloostermanGlobalPeriod Q)) :
    (∑ x : (ZMod (q + 1))ˣ, ∑ y : (ZMod (r + 1))ˣ,
      (star (w q) * w r *
        (star (kloostermanSourceFourier (q + 1) B b x) *
          kloostermanSourceFourier (r + 1) B b y)) *
        ZMod.stdAddChar
          (-(kloostermanGlobalCrossPhaseFrequency Q q r x y * k))) =
      star (w q * kloostermanGlobalModulusTimeResponse q B b k.val) *
        (w r * kloostermanGlobalModulusTimeResponse r B b k.val) := by
  simp_rw [stdAddChar_neg_globalCrossPhaseFrequency_mul Q q r hq hr]
  unfold kloostermanGlobalModulusTimeResponse
  change _ = (starRingEnd ℂ)
    (w q * ∑ x : (ZMod (q + 1))ˣ,
      kloostermanSourceFourier (q + 1) B b x *
        star ((ZMod.stdAddChar (x : ZMod (q + 1))) ^ k.val)) * _
  rw [map_mul, map_sum]
  simp only [map_mul, starRingEnd_apply, star_star]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro x
  apply Fintype.sum_congr
  intro y
  ring

private theorem sum_star_mul_erase_eq_star_sum_mul_sum_sub_diagonal
    {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (a : ι → ℂ) :
    (∑ q ∈ Q, ∑ r ∈ Q.erase q, star (a q) * a r) =
      star (∑ q ∈ Q, a q) * (∑ q ∈ Q, a q) -
        ∑ q ∈ Q, star (a q) * a q := by
  classical
  have hfull :
      star (∑ q ∈ Q, a q) * (∑ q ∈ Q, a q) =
        ∑ q ∈ Q, ∑ r ∈ Q, star (a q) * a r := by
    change (starRingEnd ℂ) (∑ q ∈ Q, a q) * (∑ q ∈ Q, a q) = _
    rw [map_sum]
    change (∑ q ∈ Q, star (a q)) * (∑ q ∈ Q, a q) = _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
  have hdecomp :
      (∑ q ∈ Q, ∑ r ∈ Q, star (a q) * a r) =
        (∑ q ∈ Q, ∑ r ∈ Q.erase q, star (a q) * a r) +
          ∑ q ∈ Q, star (a q) * a q := by
    calc
      (∑ q ∈ Q, ∑ r ∈ Q, star (a q) * a r) =
          ∑ q ∈ Q, ((∑ r ∈ Q.erase q, star (a q) * a r) +
            star (a q) * a q) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [← Finset.sum_erase_add Q (fun r => star (a q) * a r) hq]
      _ = _ := by rw [Finset.sum_add_distrib]
  calc
    (∑ q ∈ Q, ∑ r ∈ Q.erase q, star (a q) * a r) =
        (∑ q ∈ Q, ∑ r ∈ Q, star (a q) * a r) -
          ∑ q ∈ Q, star (a q) * a q := by rw [hdecomp]; ring
    _ = _ := by rw [← hfull]

/-- Exact finite off-diagonal Hermitian Gram identity. -/
theorem sum_star_mul_erase_eq_normSq_sum_sub_diagonal
    {ι : Type*} [DecidableEq ι]
    (Q : Finset ι) (a : ι → ℂ) :
    (∑ q ∈ Q, ∑ r ∈ Q.erase q, star (a q) * a r) =
      ((Complex.normSq (∑ q ∈ Q, a q) -
        ∑ q ∈ Q, Complex.normSq (a q) : ℝ) : ℂ) := by
  rw [sum_star_mul_erase_eq_star_sum_mul_sum_sub_diagonal]
  change (starRingEnd ℂ) (∑ q ∈ Q, a q) * (∑ q ∈ Q, a q) -
      ∑ q ∈ Q, (starRingEnd ℂ) (a q) * a q = _
  rw [← Complex.normSq_eq_conj_mul_self]
  simp_rw [← Complex.normSq_eq_conj_mul_self]
  push_cast
  rfl

/-- Every collision time transform is exactly the erased-diagonal Gram form of the weighted
single-modulus responses. -/
theorem kloostermanGlobalCollisionTimeTransform_eq_modulusResponseGram
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ)
    (k : ZMod (kloostermanGlobalPeriod Q)) :
    kloostermanGlobalCollisionTimeTransform Q w B b k =
      ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        star (w q * kloostermanGlobalModulusTimeResponse q B b k.val) *
          (w r * kloostermanGlobalModulusTimeResponse r B b k.val) := by
  rw [kloostermanGlobalCollisionTimeTransform_eq_explicit]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  exact sum_globalCrossPhase_eq_modulusTimeResponse Q q r hq
    (Finset.mem_of_mem_erase hr) w B b k

/-- Each global collision time slice is real and equals total weighted response mass minus the
exact modulus diagonal. -/
theorem kloostermanGlobalCollisionTimeTransform_eq_normSq_sub_diagonal
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ)
    (k : ZMod (kloostermanGlobalPeriod Q)) :
    kloostermanGlobalCollisionTimeTransform Q w B b k =
      ((Complex.normSq
          (∑ q ∈ Q, w q * kloostermanGlobalModulusTimeResponse q B b k.val) -
        ∑ q ∈ Q,
          Complex.normSq (w q * kloostermanGlobalModulusTimeResponse q B b k.val) : ℝ) : ℂ) := by
  rw [kloostermanGlobalCollisionTimeTransform_eq_modulusResponseGram]
  exact sum_star_mul_erase_eq_normSq_sum_sub_diagonal Q
    (fun q => w q * kloostermanGlobalModulusTimeResponse q B b k.val)

/-- Exact fourth-moment form of the signed collision energy: it is the common-period average of
the squared total-response mass defect after removing the modulus diagonal. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_eq_average_responseMassDefect
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b =
      (kloostermanGlobalPeriod Q : ℝ)⁻¹ *
        ∑ k : ZMod (kloostermanGlobalPeriod Q),
          (Complex.normSq
              (∑ q ∈ Q,
                w q * kloostermanGlobalModulusTimeResponse q B b k.val) -
            ∑ q ∈ Q,
              Complex.normSq
                (w q * kloostermanGlobalModulusTimeResponse q B b k.val)) ^ 2 := by
  rw [kloostermanGlobalFrequencyCollisionEnergy_eq_average_timeTransform]
  apply congrArg (fun s : ℝ => (kloostermanGlobalPeriod Q : ℝ)⁻¹ * s)
  apply Fintype.sum_congr
  intro k
  rw [kloostermanGlobalCollisionTimeTransform_eq_normSq_sub_diagonal]
  simp only [norm_real, Real.norm_eq_abs, sq_abs]

/-- Equivalent form of the global time slice as an erased-diagonal Gram sum of existing complete
Kloosterman transforms. -/
theorem kloostermanGlobalCollisionTimeTransform_eq_kloostermanTransformGram
    (Q : Finset ℕ) (w : ℕ → ℂ)
    (B : Finset ℕ) (b : ℕ → ℂ)
    (k : ZMod (kloostermanGlobalPeriod Q)) :
    kloostermanGlobalCollisionTimeTransform Q w B b k =
      ∑ q ∈ Q, ∑ r ∈ Q.erase q,
        star (w q *
          kloostermanTransform (q + 1)
            (kloostermanSourceResidue (q + 1) B b)
            (-(k.val : ZMod (q + 1)))) *
          (w r *
            kloostermanTransform (r + 1)
              (kloostermanSourceResidue (r + 1) B b)
              (-(k.val : ZMod (r + 1)))) := by
  rw [kloostermanGlobalCollisionTimeTransform_eq_modulusResponseGram]
  simp_rw [kloostermanGlobalModulusTimeResponse_eq_kloostermanTransform]

end

end RHTower.Sieve
