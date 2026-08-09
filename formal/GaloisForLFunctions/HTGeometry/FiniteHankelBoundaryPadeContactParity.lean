import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryExtensionClass
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Padé contact parity at a flat finite Hankel face

A singular positive Hankel face has a canonical finite-atomic quadrature shadow.  Subtracting its
moments from the actual sequence gives the normal coordinates of the actual orbit relative to that
flat stratum.  Simultaneous mass-shift/Möbius transport expands those coordinates with the
negative-binomial coefficients

`(-1)^j * choose (2n+j) j`.

This module proves that every coefficient before the first nonzero flat-shadow defect vanishes and
that the first coefficient is exactly the defect with the alternating contact sign.  At contact
order one this recovers the existing first-unseen Route-U flux.  Higher coefficients provide the
formal algebraic layer for stationary crossings.
-/

open scoped BigOperators
open scoped Topology
open Matrix Polynomial
open Filter Asymptotics

namespace HTGeometry

noncomputable section

/-- Pointwise difference of two moment sequences. -/
def momentSequenceDifference (s q : ℕ → ℝ) : ℕ → ℝ := fun k => s k - q k

/-- A polynomial whose degree lies below a zero initial moment segment is annihilated. -/
theorem momentFunctional_eq_zero_of_sequence_eq_zero_below
    {a : ℕ → ℝ} {K : ℕ} (hzero : ∀ k < K, a k = 0)
    {p : Polynomial ℝ} (hp : p.natDegree < K) :
    momentFunctional a p = 0 := by
  rw [momentFunctional_eq_support_sum]
  apply Finset.sum_eq_zero
  intro k hk
  have hkne : p.coeff k ≠ 0 := Polynomial.mem_support_iff.mp hk
  have hkle : k ≤ p.natDegree := Polynomial.le_natDegree_of_ne_zero hkne
  rw [hzero k (lt_of_le_of_lt hkle hp), mul_zero]

/-- Formal normal-contact series under mass-shift/Möbius transport.  Its `j`th coefficient is the
`j`th negative-binomial transport coefficient applied to `P² Xʲ`. -/
def mobiusPadeContactSeries
    (a : ℕ → ℝ) (P : Polynomial ℝ) (n : ℕ) : PowerSeries ℝ :=
  PowerSeries.mk fun j =>
    (-1 : ℝ) ^ j * (Nat.choose (2 * n + j) j : ℝ) *
      momentFunctional a (P ^ 2 * X ^ j)

/-- Analytic scalar-series form of `mobiusPadeContactSeries`. -/
def mobiusPadeContactFPowerSeries
    (a : ℕ → ℝ) (P : Polynomial ℝ) (n : ℕ) : FormalMultilinearSeries ℝ ℝ ℝ :=
  FormalMultilinearSeries.ofScalars ℝ fun j =>
    PowerSeries.coeff j (mobiusPadeContactSeries a P n)

@[simp] theorem coeff_mobiusPadeContactSeries
    (a : ℕ → ℝ) (P : Polynomial ℝ) (n j : ℕ) :
    PowerSeries.coeff j (mobiusPadeContactSeries a P n) =
      (-1 : ℝ) ^ j * (Nat.choose (2 * n + j) j : ℝ) *
        momentFunctional a (P ^ 2 * X ^ j) := by
  simp [mobiusPadeContactSeries]

/-- All contact coefficients before the first possible defect vanish. -/
theorem coeff_mobiusPadeContactSeries_eq_zero_before_contact
    {a : ℕ → ℝ} {P : Polynomial ℝ} {n d j : ℕ}
    (hP : P.Monic) (hPdeg : P.natDegree = n)
    (hzero : ∀ k < 2 * n + d, a k = 0) (hj : j < d) :
    PowerSeries.coeff j (mobiusPadeContactSeries a P n) = 0 := by
  rw [coeff_mobiusPadeContactSeries]
  have hP2 : (P ^ 2).natDegree = 2 * n := by
    rw [pow_two, hP.natDegree_mul hP, hPdeg]
    omega
  have hmonicX : (X : Polynomial ℝ) ^ j |>.Monic := Polynomial.monic_X_pow j
  have hdeg : (P ^ 2 * X ^ j).natDegree = 2 * n + j := by
    rw [(hP.pow 2).natDegree_mul hmonicX, hP2, Polynomial.natDegree_X_pow]
  have hlt : (P ^ 2 * X ^ j).natDegree < 2 * n + d := by omega
  rw [momentFunctional_eq_zero_of_sequence_eq_zero_below hzero hlt, mul_zero]

/-- At the first nonzero normal coordinate, monicity removes every lower term of `P²`. -/
theorem momentFunctional_monic_first_contact
    {a : ℕ → ℝ} {P : Polynomial ℝ} {n d : ℕ}
    (hP : P.Monic) (hPdeg : P.natDegree = n) (hd : 0 < d)
    (hzero : ∀ k < 2 * n + d, a k = 0) :
    momentFunctional a (P ^ 2 * X ^ d) = a (2 * n + d) := by
  let top : Polynomial ℝ := X ^ (2 * n + d)
  let body : Polynomial ℝ := P ^ 2 * X ^ d
  let rem : Polynomial ℝ := body - top
  have hbodyMonic : body.Monic := (hP.pow 2).mul (Polynomial.monic_X_pow d)
  have hbodyDeg : body.natDegree = 2 * n + d := by
    dsimp only [body]
    rw [(hP.pow 2).natDegree_mul (Polynomial.monic_X_pow d),
      show (P ^ 2).natDegree = 2 * n by
        rw [pow_two, hP.natDegree_mul hP, hPdeg]
        omega,
      Polynomial.natDegree_X_pow]
  have hbodyNe : body ≠ 0 := hbodyMonic.ne_zero
  have hbodyDegree : body.degree = ((2 * n + d : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree hbodyNe, hbodyDeg]
  have htopDegree : top.degree = ((2 * n + d : ℕ) : WithBot ℕ) := by
    dsimp only [top]
    rw [degree_X_pow]
  have hlead : body.leadingCoeff = top.leadingCoeff := by
    rw [hbodyMonic.leadingCoeff]
    dsimp only [top]
    rw [leadingCoeff_X_pow]
  have hremDegree : rem.degree < ((2 * n + d : ℕ) : WithBot ℕ) := by
    dsimp only [rem]
    have h := degree_sub_lt (by rw [hbodyDegree, htopDegree]) hbodyNe hlead
    rwa [hbodyDegree] at h
  have hremNatDegree : rem.natDegree < 2 * n + d := by
    by_cases hrem : rem = 0
    · simp [hrem]
      omega
    · exact (natDegree_lt_iff_degree_lt hrem).mpr hremDegree
  have hremZero : momentFunctional a rem = 0 :=
    momentFunctional_eq_zero_of_sequence_eq_zero_below hzero hremNatDegree
  have hsplit : body = rem + top := by
    dsimp only [rem]
    ring
  rw [show P ^ 2 * X ^ d = body by rfl, hsplit, momentFunctional_add, hremZero,
    zero_add]
  dsimp only [top]
  rw [momentFunctional_X_pow]

/-- Exact first-contact coefficient: parity is the contact order and magnitude is a positive
binomial factor times the first nonzero flat-shadow defect. -/
theorem coeff_mobiusPadeContactSeries_at_first_contact
    {a : ℕ → ℝ} {P : Polynomial ℝ} {n d : ℕ}
    (hP : P.Monic) (hPdeg : P.natDegree = n) (hd : 0 < d)
    (hzero : ∀ k < 2 * n + d, a k = 0) :
    PowerSeries.coeff d (mobiusPadeContactSeries a P n) =
      (-1 : ℝ) ^ d * (Nat.choose (2 * n + d) d : ℝ) * a (2 * n + d) := by
  rw [coeff_mobiusPadeContactSeries,
    momentFunctional_monic_first_contact hP hPdeg hd hzero]

/-- Difference between the actual moment and its canonical flat-quadrature Padé shadow. -/
def finiteHankelBoundaryPadeDefect
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  s k - ∑ x ∈ finiteHankelBoundaryNodes c,
    finiteHankelBoundaryWeight s c x * x ^ k

/-- Flat quadrature kills every Padé defect through the current visible face. -/
theorem finiteHankelBoundaryPadeDefect_eq_zero_of_le
    {s : ℕ → ℝ} {n k : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) (hk : k ≤ 2 * n) :
    finiteHankelBoundaryPadeDefect s c k = 0 := by
  have hdegree : (X ^ k : Polynomial ℝ).degree ≤ ((2 * n : ℕ) : WithBot ℕ) := by
    rw [degree_X_pow]
    exact_mod_cast hk
  have hexact := momentFunctional_eq_finiteHankelBoundarySum
    c hhead hc hlast (X ^ k) hdegree
  rw [momentFunctional_X_pow] at hexact
  simp only [eval_pow, eval_X] at hexact
  exact sub_eq_zero.mpr hexact

/-- First Padé defect is exactly the canonical monic extension class. -/
theorem finiteHankelBoundaryPadeDefect_first_eq_monicRemainder
    (s : ℕ → ℝ) {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    finiteHankelBoundaryPadeDefect s c (2 * n + 1) =
      finiteHankelBoundaryMonicRemainder s c := by
  rw [finiteHankelBoundaryPadeDefect]
  exact (finiteHankelBoundaryMonicRemainder_eq_firstUnseenMomentError
    s c hhead hc hlast).symm

/-- At ordinary contact, the new series coefficient is the existing Route-U normal flux. -/
theorem finiteHankelBoundaryContactSeries_coeff_one
    {s : ℕ → ℝ} {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hhead : (momentHankelMatrix s n).PosDef)
    (hc : momentHankelMatrix s (n + 1) *ᵥ c = 0)
    (hlast : c (Fin.last n) ≠ 0) :
    PowerSeries.coeff 1
        (mobiusPadeContactSeries (finiteHankelBoundaryPadeDefect s c)
          (finiteHankelNullMonicPolynomial c) n) =
      -((2 * n + 1 : ℕ) : ℝ) * finiteHankelBoundaryMonicRemainder s c := by
  have hzero : ∀ k < 2 * n + 1, finiteHankelBoundaryPadeDefect s c k = 0 := by
    intro k hk
    apply finiteHankelBoundaryPadeDefect_eq_zero_of_le c hhead hc hlast
    omega
  rw [coeff_mobiusPadeContactSeries_at_first_contact
      (finiteHankelNullMonicPolynomial_monic c hlast)
      (finiteHankelNullMonicPolynomial_natDegree c hlast) (by omega) hzero,
    finiteHankelBoundaryPadeDefect_first_eq_monicRemainder s c hhead hc hlast,
    Nat.choose_one_right]
  push_cast
  ring

/-- Positive first contact coefficient forces the alternating sign on the first normal defect. -/
theorem signed_first_defect_pos_of_contactCoefficient_pos
    {a : ℕ → ℝ} {P : Polynomial ℝ} {n d : ℕ}
    (hP : P.Monic) (hPdeg : P.natDegree = n) (hd : 0 < d)
    (hzero : ∀ k < 2 * n + d, a k = 0)
    (hcontact : 0 < PowerSeries.coeff d (mobiusPadeContactSeries a P n)) :
    0 < (-1 : ℝ) ^ d * a (2 * n + d) := by
  rw [coeff_mobiusPadeContactSeries_at_first_contact hP hPdeg hd hzero] at hcontact
  have hchooseNat : 0 < Nat.choose (2 * n + d) d := Nat.choose_pos (by omega)
  have hchoose : 0 < (Nat.choose (2 * n + d) d : ℝ) := by exact_mod_cast hchooseNat
  nlinarith

/-- A source law with the opposite alternating sign excludes a positive contact coefficient. -/
theorem not_contactCoefficient_pos_of_source_opposite
    {a : ℕ → ℝ} {P : Polynomial ℝ} {n d : ℕ}
    (hP : P.Monic) (hPdeg : P.natDegree = n) (hd : 0 < d)
    (hzero : ∀ k < 2 * n + d, a k = 0)
    (hsource : (-1 : ℝ) ^ d * a (2 * n + d) < 0) :
    ¬ 0 < PowerSeries.coeff d (mobiusPadeContactSeries a P n) := by
  intro hcontact
  have hforced := signed_first_defect_pos_of_contactCoefficient_pos
    hP hPdeg hd hzero hcontact
  linarith

/-! ### One-sided analytic contact orientation -/

/-- For a scalar analytic germ, a right-hand nonnegative value forces its first nonzero Taylor
coefficient to be positive.  This is the analytic bridge from full right-cone positivity to contact
orientation. -/
theorem leading_scalar_coeff_pos_of_eventually_nonneg_right
    {f : ℝ → ℝ} {c : ℕ → ℝ} {d : ℕ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℝ c) 0)
    (hzero : ∀ j < d, c j = 0) (hfirst : c d ≠ 0)
    (hnonneg : ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 ≤ f u) :
    0 < c d := by
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    FormalMultilinearSeries.ofScalars ℝ c
  have hpartial (u : ℝ) : p.partialSum (d + 1) u = c d * u ^ d := by
    rw [FormalMultilinearSeries.partialSum]
    simp_rw [p, FormalMultilinearSeries.ofScalars_apply_eq]
    rw [Finset.sum_eq_single d]
    · simp
    · intro j hj hjne
      have hjlt : j < d := by
        simp only [Finset.mem_range] at hj
        omega
      rw [hzero j hjlt, zero_smul]
    · simp
  have hO := hf.isBigO_sub_partialSum_pow (d + 1)
  have hsmall :
      (fun u : ℝ => f u - c d * u ^ d) =o[𝓝 0]
        (fun u : ℝ => ‖u‖ ^ d) := by
    have hpow : (fun u : ℝ => ‖u‖ ^ (d + 1)) =o[𝓝 0]
        (fun u : ℝ => ‖u‖ ^ d) := isLittleO_norm_pow_norm_pow (Nat.lt_succ_self d)
    apply hO.trans_isLittleO hpow |>.congr'
    · filter_upwards with u
      rw [zero_add, hpartial]
    · exact Eventually.of_forall fun _ => rfl
  have hratio : Tendsto
      (fun u : ℝ => (f u - c d * u ^ d) / (‖u‖ ^ d))
      (𝓝 0) (𝓝 0) := hsmall.tendsto_div_nhds_zero
  have hratioRight : Tendsto
      (fun u : ℝ => (f u - c d * u ^ d) / (‖u‖ ^ d))
      (𝓝[>] 0) (𝓝 0) := hratio.mono_left inf_le_left
  have hquotient : Tendsto (fun u : ℝ => f u / u ^ d)
      (𝓝[>] 0) (𝓝 (c d)) := by
    have hrewrite : ∀ᶠ u in 𝓝[>] (0 : ℝ),
        f u / u ^ d = (f u - c d * u ^ d) / ‖u‖ ^ d + c d := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu0 : u ≠ 0 := ne_of_gt hu
      rw [Real.norm_eq_abs, abs_of_pos hu]
      field_simp
      ring
    rw [tendsto_congr' hrewrite]
    simpa using hratioRight.add_const (c d)
  have hquotNonneg : ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 ≤ f u / u ^ d := by
    filter_upwards [hnonneg, self_mem_nhdsWithin] with u hfu hu
    exact div_nonneg hfu (pow_nonneg hu.le _)
  exact lt_of_le_of_ne (ge_of_tendsto hquotient hquotNonneg) (Ne.symm hfirst)

/-- **Padé contact parity law.**  If the moving-null energy is analytic with the exact Möbius
contact series, is nonnegative immediately to the right, and has first nonzero flat-shadow defect
at order `2n+d`, then that defect has sign `(-1)^d`. -/
theorem signed_first_defect_pos_of_right_nonnegative_contact
    {a : ℕ → ℝ} {P : Polynomial ℝ} {n d : ℕ} {energy : ℝ → ℝ}
    (hP : P.Monic) (hPdeg : P.natDegree = n) (hd : 0 < d)
    (hzero : ∀ k < 2 * n + d, a k = 0)
    (hfirst : a (2 * n + d) ≠ 0)
    (hseries : HasFPowerSeriesAt energy (mobiusPadeContactFPowerSeries a P n) 0)
    (hnonneg : ∀ᶠ u in 𝓝[>] (0 : ℝ), 0 ≤ energy u) :
    0 < (-1 : ℝ) ^ d * a (2 * n + d) := by
  let coeff : ℕ → ℝ := fun j =>
    PowerSeries.coeff j (mobiusPadeContactSeries a P n)
  have hcoeffZero : ∀ j < d, coeff j = 0 := by
    intro j hj
    exact coeff_mobiusPadeContactSeries_eq_zero_before_contact hP hPdeg hzero hj
  have hcoeffFirst : coeff d ≠ 0 := by
    change PowerSeries.coeff d (mobiusPadeContactSeries a P n) ≠ 0
    rw [coeff_mobiusPadeContactSeries_at_first_contact hP hPdeg hd hzero]
    exact mul_ne_zero
      (mul_ne_zero (pow_ne_zero _ (by norm_num))
        (by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos (by omega)))) hfirst
  have hcoeffPos : 0 < coeff d :=
    leading_scalar_coeff_pos_of_eventually_nonneg_right
      hseries hcoeffZero hcoeffFirst hnonneg
  exact signed_first_defect_pos_of_contactCoefficient_pos
    hP hPdeg hd hzero hcoeffPos

end

end HTGeometry
