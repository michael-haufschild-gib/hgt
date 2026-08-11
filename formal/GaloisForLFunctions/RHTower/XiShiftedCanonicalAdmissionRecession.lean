import GaloisForLFunctions.HTGeometry.MonicMomentAdmission
import GaloisForLFunctions.RHTower.XiShiftedAdaptiveArithmeticSourceArcsineAdmissionMargin
import GaloisForLFunctions.RHTower.XiShiftedHankelFarRightPositiveDefinite

/-!
# Canonical fixed-degree shifted-Xi admission recession

The canonical degree-`n` admission is defined in the open chamber, before any Hankel flatness, by
solving the leading monic moment orthogonality system.  Normalized shifted-Xi moments converge to
the arcsine sequence, and continuity of the inverse Hankel solve makes the admission converge
coefficientwise to the shifted monic Chebyshev polynomial.

At a flat next face the generic solver theorem identifies this same admission with the actual
terminal-normalized null flag.  Thus the construction is source-first and admission-sensitive;
it is neither an orientation map nor a fixed reporter.
-/

open Filter Matrix Polynomial Topology
open scoped BigOperators

namespace RHTower

namespace XiShiftedCanonicalAdmission

noncomputable section

namespace Arc

abbrev affine := XiShiftedArcsineAdmission.affine
abbrev L := XiShiftedArcsineAdmission.L
abbrev amplitude := XiShiftedArcsineAdmission.amplitude
abbrev monicScale := XiShiftedArcsineAdmission.monicScale

theorem L_add (P Q : Polynomial ℝ) : L (P + Q) = L P + L Q :=
  XiShiftedArcsineAdmission.L_add P Q

theorem L_two_mul (P : Polynomial ℝ) : L (2 * P) = 2 * L P :=
  XiShiftedArcsineAdmission.L_two_mul P

theorem L_C_mul (a : ℝ) (P : Polynomial ℝ) : L (Polynomial.C a * P) = a * L P :=
  XiShiftedArcsineAdmission.L_C_mul a P

theorem L_T_mul_T_of_ne {n m : ℕ} (h : n ≠ m) :
    L (Polynomial.Chebyshev.T ℝ n * Polynomial.Chebyshev.T ℝ m) = 0 :=
  XiShiftedArcsineAdmission.L_T_mul_T_of_ne h

theorem amplitude_monic {n : ℕ} (hn : n ≠ 0) : (amplitude n).Monic :=
  XiShiftedArcsineAdmission.amplitude_monic hn

end Arc

/-- The inverse affine coordinate carrying `[-1,1]` back to `[0,1]`. -/
def inverseAffine : Polynomial ℝ := (1 / 2 : ℝ) • (1 + X)

theorem inverseAffine_comp_affine : inverseAffine.comp Arc.affine = X := by
  unfold inverseAffine Arc.affine XiShiftedArcsineAdmission.affine
  simp [Polynomial.smul_eq_C_mul]
  have hC : Polynomial.C (2 : ℝ)⁻¹ * Polynomial.C (2 : ℝ) = 1 := by
    rw [← Polynomial.C_mul]
    norm_num
  rw [mul_sub, ← Polynomial.C_ofNat 2, ← mul_assoc, hC, one_mul, mul_one]
  abel

theorem inverseAffine_natDegree : inverseAffine.natDegree = 1 := by
  have hpoly : inverseAffine =
      Polynomial.C (1 / 2 : ℝ) * X + Polynomial.C (1 / 2 : ℝ) := by
    simp [inverseAffine, Polynomial.smul_eq_C_mul]
    ring
  rw [hpoly, Polynomial.natDegree_linear (by norm_num : (1 / 2 : ℝ) ≠ 0)]

theorem L_finset_sum {ι : Type*} (t : Finset ι) (f : ι → Polynomial ℝ) :
    Arc.L (∑ i ∈ t, f i) = ∑ i ∈ t, Arc.L (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Arc.L, XiShiftedArcsineAdmission.L, HTGeometry.momentFunctional_zero]
  | @insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Arc.L_add, ih]

/-- Chebyshev nearest-neighbour recurrence in the form used by the orthogonality induction. -/
theorem two_mul_X_mul_T {n : ℕ} (hn : n ≠ 0) :
    2 * X * Polynomial.Chebyshev.T ℝ n =
      Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ) +
        Polynomial.Chebyshev.T ℝ ((n - 1 : ℕ) : ℤ) := by
  have hrec := Polynomial.Chebyshev.T_add_two ℝ ((n - 1 : ℕ) : ℤ)
  rw [show ((n - 1 : ℕ) : ℤ) + 2 = (n + 1 : ℕ) by omega,
    show ((n - 1 : ℕ) : ℤ) + 1 = n by omega] at hrec
  linear_combination -hrec

/-- A Chebyshev mode is arcsine-orthogonal to every strictly lower monomial. -/
theorem L_X_pow_mul_T_eq_zero :
    ∀ i n : ℕ, i < n →
      Arc.L (X ^ i * Polynomial.Chebyshev.T ℝ n) = 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro n hin
      cases i with
      | zero =>
          have hzero := XiShiftedArcsineAdmission.L_T_mul_T_of_ne
            (n := n) (m := 0) (by omega)
          simpa using hzero
      | succ i =>
          have hrec := two_mul_X_mul_T (n := n) (by omega)
          have hpoly :
              (2 : Polynomial ℝ) *
                  (X ^ (i + 1) * Polynomial.Chebyshev.T ℝ n) =
                X ^ i * Polynomial.Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ) +
                  X ^ i * Polynomial.Chebyshev.T ℝ ((n - 1 : ℕ) : ℤ) := by
            linear_combination X ^ i * hrec
          have hfun := congrArg Arc.L hpoly
          rw [Arc.L_two_mul, Arc.L_add,
            ih i (by omega) (n + 1) (by omega),
            ih i (by omega) (n - 1) (by omega)] at hfun
          linarith

/-- A Chebyshev mode is arcsine-orthogonal to every polynomial of lower degree. -/
theorem L_mul_T_eq_zero_of_natDegree_lt
    {q : Polynomial ℝ} {n : ℕ} (hdegree : q.natDegree < n) :
    Arc.L (q * Polynomial.Chebyshev.T ℝ n) = 0 := by
  classical
  conv_lhs => rw [q.as_sum_support_C_mul_X_pow]
  rw [Finset.sum_mul, L_finset_sum]
  apply Finset.sum_eq_zero
  intro k hk
  have hkcoeff : q.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
  have hkle : k ≤ q.natDegree := Polynomial.le_natDegree_of_ne_zero hkcoeff
  have hkn : k < n := lt_of_le_of_lt hkle hdegree
  rw [show Polynomial.C (q.coeff k) * X ^ k * Polynomial.Chebyshev.T ℝ n =
      Polynomial.C (q.coeff k) *
        (X ^ k * Polynomial.Chebyshev.T ℝ n) by ring,
    Arc.L_C_mul, L_X_pow_mul_T_eq_zero k n hkn, mul_zero]

/-- The shifted monic Chebyshev amplitude satisfies the canonical arcsine admission equations. -/
theorem momentFunctional_X_pow_mul_arcsine_amplitude_eq_zero
    {n : ℕ} (_hn : n ≠ 0) (i : Fin n) :
    HTGeometry.momentFunctional
      GaloisForLFunctions.HTGeometry.normalizedCentralBinom
      (X ^ (i : ℕ) * Arc.amplitude n) = 0 := by
  let q := inverseAffine ^ (i : ℕ)
  have hqdegree : q.natDegree < n := by
    apply lt_of_le_of_lt Polynomial.natDegree_pow_le
    rw [inverseAffine_natDegree, Nat.mul_one]
    exact i.isLt
  have hzero := L_mul_T_eq_zero_of_natDegree_lt hqdegree
  have hcomp :
      (q * Polynomial.Chebyshev.T ℝ n).comp Arc.affine =
        X ^ (i : ℕ) * (Polynomial.Chebyshev.T ℝ n).comp Arc.affine := by
    simp [q, Polynomial.mul_comp, Polynomial.pow_comp, inverseAffine_comp_affine]
  have hpoly :
      X ^ (i : ℕ) * Arc.amplitude n =
        Arc.monicScale n •
          ((q * Polynomial.Chebyshev.T ℝ n).comp Arc.affine) := by
    change X ^ (i : ℕ) *
        (XiShiftedArcsineAdmission.monicScale n •
          (Polynomial.Chebyshev.T ℝ n).comp Arc.affine) = _
    rw [hcomp]
    simp [Polynomial.smul_eq_C_mul]
    ring
  rw [hpoly, HTGeometry.momentFunctional_smul]
  change Arc.monicScale n * Arc.L (q * Polynomial.Chebyshev.T ℝ n) = 0
  rw [hzero, mul_zero]

theorem amplitude_natDegree {n : ℕ} (_hn : n ≠ 0) :
    (Arc.amplitude n).natDegree = n := by
  have hs : Arc.monicScale n ≠ 0 := by
    exact inv_ne_zero (pow_ne_zero _ (by norm_num))
  change (XiShiftedArcsineAdmission.monicScale n •
    (Polynomial.Chebyshev.T ℝ n).comp Arc.affine).natDegree = n
  rw [Polynomial.natDegree_smul _ hs,
    Polynomial.natDegree_comp, Polynomial.Chebyshev.natDegree_T]
  have haff : Arc.affine.natDegree = 1 := by
    have hpoly : Arc.affine =
        Polynomial.C (2 : ℝ) * X + Polynomial.C (-1 : ℝ) := by
      unfold Arc.affine XiShiftedArcsineAdmission.affine
      simp
      change (2 : Polynomial ℝ) * X - 1 =
        (2 : Polynomial ℝ) * X + -1
      ring
    rw [hpoly, Polynomial.natDegree_linear (by norm_num : (2 : ℝ) ≠ 0)]
  rw [haff]
  simp

/-- The inverse-Hankel arcsine admission is exactly the shifted monic Chebyshev amplitude. -/
theorem monicMomentAdmissionPolynomial_normalizedCentralBinom_eq_amplitude
    {n : ℕ} (hn : n ≠ 0) :
    HTGeometry.monicMomentAdmissionPolynomial
        GaloisForLFunctions.HTGeometry.normalizedCentralBinom n =
      Arc.amplitude n := by
  symm
  apply HTGeometry.eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal
    (ne_of_gt
      (GaloisForLFunctions.HTGeometry.normalizedCentralBinom_momentHankelMatrix_det_pos n))
    (Arc.amplitude_monic hn) (amplitude_natDegree hn)
  exact momentFunctional_X_pow_mul_arcsine_amplitude_eq_zero hn

/-- Dimensionless shifted-Xi monic admission selected before the adaptive source landing. -/
def dimensionlessAdmission (w : ℝ) (n : ℕ) : Polynomial ℝ :=
  HTGeometry.monicMomentAdmissionPolynomial (xiShiftedFarRightNormalizedMoment w) n

/-- Every fixed-degree inverse-Hankel polynomial is eventually an actual shifted-Xi admission,
not merely a totalized inverse-matrix expression. -/
theorem dimensionlessAdmission_eventually_orthogonal (n : ℕ) :
    ∀ᶠ w : ℝ in atTop, ∀ i : Fin n,
      HTGeometry.momentFunctional (xiShiftedFarRightNormalizedMoment w)
        (X ^ (i : ℕ) * dimensionlessAdmission w n) = 0 := by
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually n] with w hw
  intro i
  apply HTGeometry.momentFunctional_X_pow_mul_monicMomentAdmissionPolynomial_eq_zero
  exact ne_of_gt hw.det_pos

/-- Eventually, the dimensionless admission is the unique monic degree-`n` polynomial satisfying
the shifted-Xi lower-moment equations. -/
theorem dimensionlessAdmission_eventually_unique (n : ℕ) :
    ∀ᶠ w : ℝ in atTop, ∀ p : Polynomial ℝ,
      p.Monic → p.natDegree = n →
      (∀ i : Fin n, HTGeometry.momentFunctional
        (xiShiftedFarRightNormalizedMoment w) (X ^ (i : ℕ) * p) = 0) →
      p = dimensionlessAdmission w n := by
  filter_upwards [xiShiftedFarRightNormalizedHankelMatrix_posDef_eventually n] with w hw
  intro p hp hdegree horth
  exact HTGeometry.eq_monicMomentAdmissionPolynomial_of_monic_of_orthogonal
    (ne_of_gt hw.det_pos) hp hdegree horth

/-- Every coefficient of a fixed-degree shifted-Xi admission converges to shifted Chebyshev. -/
theorem tendsto_dimensionlessAdmission_coeff
    {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    Tendsto (fun w : ℝ => (dimensionlessAdmission w n).coeff k) atTop
      (nhds ((Arc.amplitude n).coeff k)) := by
  have h := HTGeometry.tendsto_monicMomentAdmissionPolynomial_coeff
    (f := fun w => xiShiftedFarRightNormalizedMoment w)
    (s := GaloisForLFunctions.HTGeometry.normalizedCentralBinom)
    (n := n)
    (fun j => tendsto_scaled_re_xiShiftedReciprocalMoment_squareParam j)
    (ne_of_gt
      (GaloisForLFunctions.HTGeometry.normalizedCentralBinom_momentHankelMatrix_det_pos n)) k
  rw [monicMomentAdmissionPolynomial_normalizedCentralBinom_eq_amplitude hn] at h
  exact h

/-- At any flat next Xi face, terminal normalization identifies the true null flag with the same
canonical open-chamber admission. -/
theorem flat_nullVector_eq_dimensionlessAdmissionVector
    {w : ℝ} {n : ℕ} {c : Fin (n + 1) → ℝ}
    (hdet : (xiShiftedFarRightNormalizedHankelMatrix w n).det ≠ 0)
    (hc : HTGeometry.momentHankelMatrix
      (xiShiftedFarRightNormalizedMoment w) (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) = 1) :
    c = HTGeometry.monicMomentAdmissionVector
      (xiShiftedFarRightNormalizedMoment w) n := by
  exact HTGeometry.eq_monicMomentAdmissionVector_of_kernel_of_last_eq_one
    hdet hc hlast

end

end XiShiftedCanonicalAdmission

end RHTower
