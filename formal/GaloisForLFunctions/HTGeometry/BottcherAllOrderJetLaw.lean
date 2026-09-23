/-
# Böttcher all-order parameter--spatial jet law

For the normalized quadratic Böttcher constraint, the reciprocal-coordinate displacement is

`delta(c,t) = -c t^(4 : ℕ) / (1 + c t^(2 : ℕ))`.

This module formalizes its arbitrary-power negative-binomial coefficient and uses it to extract
the complete mixed Taylor coefficient at every parameter depth.  The resulting capstone is the
closed all-order parameter--spatial derivative staircase law.
-/
import Mathlib.RingTheory.PowerSeries.Binomial
import GaloisForLFunctions.U0.ThirdVelocityJet

namespace GaloisForLFunctions

open PowerSeries

noncomputable section

abbrev BottcherSpatialSeries := PowerSeries ℂ
abbrev BottcherParameterSeries := PowerSeries BottcherSpatialSeries

/-- The `b`-th power of the reciprocal-coordinate displacement, represented as a power series in
the parameter whose coefficients are spatial power series. -/
def bottcherDisplacementPower (b : ℕ) : BottcherParameterSeries :=
  C ((-1 : ℂ) ^ b • (X ^ (4 * b) : BottcherSpatialSeries)) *
    (X ^ b * rescale (X ^ (2 : ℕ) : BottcherSpatialSeries)
      (binomialSeries BottcherSpatialSeries (-b : ℤ)))

/-- The exact coefficient of `c^k` in
`(-c t^(4 : ℕ) / (1 + c t^(2 : ℕ)))^b`.  This is the negative-binomial kernel used by every mixed
parameter--spatial jet. -/
theorem coeff_bottcherDisplacementPower (b k : ℕ) (hb : 1 ≤ b) :
    (coeff k) (bottcherDisplacementPower b) =
      if b ≤ k then
        ((-1 : ℂ) ^ k * (Nat.choose (k - 1) (b - 1) : ℂ)) •
          (X ^ (2 * (k + b)) : BottcherSpatialSeries)
      else 0 := by
  rw [bottcherDisplacementPower, coeff_C_mul, coeff_X_pow_mul']
  split_ifs with hbk
  · rw [coeff_rescale, binomialSeries_coeff, Ring.choose_neg]
    have hsumZ : (b : ℤ) + (k - b : ℕ) - 1 = (k - 1 : ℕ) := by omega
    rw [hsumZ, Ring.choose_natCast]
    have hchoose : Nat.choose (k - 1) (k - b) = Nat.choose (k - 1) (b - 1) := by
      apply Nat.choose_symm_of_eq_add
      omega
    rw [hchoose]
    norm_num [zsmul_eq_mul, Int.cast_negOnePow_natCast]
    rw [show (X ^ (2 : ℕ) : BottcherSpatialSeries) ^ (k - b) = X ^ (2 * (k - b)) by ring]
    change ((-1 : ℂ) ^ b) •
        ((X ^ (4 * b) : BottcherSpatialSeries) *
          ((X ^ (2 * (k - b)) : BottcherSpatialSeries) *
            ((((k - b : ℕ) : ℤ).negOnePow : ℤ) •
              C (Nat.choose (k - 1) (b - 1) : ℂ)))) =
      ((-1 : ℂ) ^ k * (Nat.choose (k - 1) (b - 1) : ℂ)) •
        (X ^ (2 * (k + b)) : BottcherSpatialSeries)
    rw [Int.coe_negOnePow_natCast]
    simp only [zsmul_eq_mul]
    norm_num
    simp only [Algebra.smul_def]
    rw [← mul_assoc (X ^ (4 * b) : BottcherSpatialSeries), ← pow_add]
    have hexp : 4 * b + 2 * (k - b) = 2 * (k + b) := by omega
    rw [hexp]
    have hsign : (-1 : ℂ) ^ b * (-1 : ℂ) ^ (k - b) = (-1 : ℂ) ^ k := by
      rw [← pow_add, Nat.add_sub_of_le hbk]
    have hconst :
        ((-1 : BottcherSpatialSeries) ^ (k - b) *
          (Nat.choose (k - 1) (b - 1) : BottcherSpatialSeries)) =
        C ((-1 : ℂ) ^ (k - b) *
          (Nat.choose (k - 1) (b - 1) : ℂ)) := by
      rw [show (-1 : BottcherSpatialSeries) ^ (k - b) = C ((-1 : ℂ) ^ (k - b)) by
          simp,
        show (Nat.choose (k - 1) (b - 1) : BottcherSpatialSeries) =
            C (Nat.choose (k - 1) (b - 1) : ℂ) by
          simp,
        map_mul]
    ext n
    simp only [PowerSeries.algebraMap_eq]
    rw [coeff_C_mul, coeff_C_mul, coeff_X_pow_mul']
    split_ifs with hn
    · rw [hconst, coeff_C, coeff_X_pow]
      split_ifs with hn0 hn1
      · have : n = 2 * (k + b) := by omega
        subst n
        simp only [mul_one]
        rw [← mul_assoc, hsign]
      · exfalso
        omega
      · exfalso
        omega
      · simp
    · rw [coeff_X_pow]
      split_ifs <;> simp_all
  · simp

/-- The coefficient weight in the all-order Böttcher parameter--spatial jet law. -/
def bottcherJetWeight (r a b : ℕ) : ℂ :=
  (Nat.factorial r : ℂ) /
      ((Nat.factorial a : ℂ) * (Nat.factorial b : ℂ)) *
    (-1 : ℂ) ^ (r - a) * Nat.choose (r - a - 1) (b - 1)

/-- The mixed Taylor contribution to the `r`-th parameter coefficient before the
negative-binomial displacement kernel has been expanded. -/
def bottcherMixedSubstitutionCoeff
    (J : ℕ → ℕ → BottcherSpatialSeries) (r : ℕ) : BottcherSpatialSeries :=
  ∑ a ∈ Finset.Icc 1 (r - 1), ∑ b ∈ Finset.Icc 1 (r - a),
    ((Nat.factorial r : ℂ) /
      ((Nat.factorial a : ℂ) * (Nat.factorial b : ℂ))) •
      (J a b * (coeff (r - a)) (bottcherDisplacementPower b))

/-- **Generic Böttcher substitution coefficient extractor.** Every mixed Taylor term at
parameter depth `r` has the closed negative-binomial kernel from the paper. -/
theorem bottcherMixedSubstitutionCoeff_eq
    (J : ℕ → ℕ → BottcherSpatialSeries) (r : ℕ) :
    bottcherMixedSubstitutionCoeff J r =
      ∑ a ∈ Finset.Icc 1 (r - 1), ∑ b ∈ Finset.Icc 1 (r - a),
        bottcherJetWeight r a b •
          ((X ^ (2 * (r - a + b)) : BottcherSpatialSeries) * J a b) := by
  classical
  unfold bottcherMixedSubstitutionCoeff
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mem_Icc] at ha hb
  rw [coeff_bottcherDisplacementPower b (r - a) hb.1, if_pos hb.2]
  unfold bottcherJetWeight
  simp only [Algebra.smul_def, map_mul]
  ring

/-- The `b`-fold formal spatial derivative of a spatial power series. -/
def iteratedSpatialDerivative : ℕ → BottcherSpatialSeries → BottcherSpatialSeries
  | 0, f => f
  | b + 1, f => PowerSeries.derivative ℂ (iteratedSpatialDerivative b f)

/-- The spatial derivative `J_a^(b)` read at the dyadically pulled-back point `t²`. -/
def bottcherDyadicSpatialJet
    (J : ℕ → BottcherSpatialSeries) (a b : ℕ) : BottcherSpatialSeries :=
  dyadicSubst (iteratedSpatialDerivative b (J a))

/-- The `r`-th parameter coefficient of `-log (1 + c t²)`, in derivative normalization. -/
def bottcherLogJetTerm (r : ℕ) : BottcherSpatialSeries :=
  ((-1 : ℂ) ^ r * (Nat.factorial (r - 1) : ℂ)) •
    (X ^ (2 * r) : BottcherSpatialSeries)

/-- The exact coefficient-level form of the normalized Böttcher constraint before expanding the
mixed substitution coefficient. -/
def IsBottcherLogJetSystem (J : ℕ → BottcherSpatialSeries) : Prop :=
  ∀ r, 1 ≤ r →
    dyadicSubst (J r) +
        bottcherMixedSubstitutionCoeff (bottcherDyadicSpatialJet J) r =
      2 * J r + bottcherLogJetTerm r

/-- **Böttcher all-order parameter--spatial jet law.** Every normalized logarithmic jet system
obeying the unexpanded coefficient form of the Böttcher constraint satisfies the closed
negative-binomial staircase formula at every positive parameter depth. -/
theorem bottcher_all_order_parameter_spatial_jet_law
    {J : ℕ → BottcherSpatialSeries} (hJ : IsBottcherLogJetSystem J)
    {r : ℕ} (hr : 1 ≤ r) :
    dyadicSubst (J r) =
      2 * J r + bottcherLogJetTerm r -
        ∑ a ∈ Finset.Icc 1 (r - 1), ∑ b ∈ Finset.Icc 1 (r - a),
          bottcherJetWeight r a b •
            ((X ^ (2 * (r - a + b)) : BottcherSpatialSeries) *
              bottcherDyadicSpatialJet J a b) := by
  have h := hJ r hr
  rw [bottcherMixedSubstitutionCoeff_eq] at h
  calc
    dyadicSubst (J r) =
        (dyadicSubst (J r) +
          ∑ a ∈ Finset.Icc 1 (r - 1), ∑ b ∈ Finset.Icc 1 (r - a),
            bottcherJetWeight r a b •
              ((X ^ (2 * (r - a + b)) : BottcherSpatialSeries) *
                bottcherDyadicSpatialJet J a b)) -
          ∑ a ∈ Finset.Icc 1 (r - 1), ∑ b ∈ Finset.Icc 1 (r - a),
            bottcherJetWeight r a b •
              ((X ^ (2 * (r - a + b)) : BottcherSpatialSeries) *
                bottcherDyadicSpatialJet J a b) := by abel
    _ = 2 * J r + bottcherLogJetTerm r -
          ∑ a ∈ Finset.Icc 1 (r - 1), ∑ b ∈ Finset.Icc 1 (r - a),
            bottcherJetWeight r a b •
              ((X ^ (2 * (r - a + b)) : BottcherSpatialSeries) *
                bottcherDyadicSpatialJet J a b) := by rw [h]

/-! ## Canonical all-order formal jet family -/

/-- Coefficients of the normalized solution of `f(t²) = 2 f(t) + rhs(t)`, obtained by binary
descent. -/
noncomputable def dyadicEquationSolutionCoeff (rhs : BottcherSpatialSeries) : ℕ → ℂ
  | 0 => -(coeff 0) rhs
  | n + 1 =>
      ((if 2 ∣ n + 1 then dyadicEquationSolutionCoeff rhs ((n + 1) / 2) else 0) -
        (coeff (n + 1)) rhs) / 2
decreasing_by exact Nat.div_lt_self (Nat.succ_pos n) one_lt_two

/-- The normalized formal solution of one inhomogeneous dyadic Mahler equation. -/
def dyadicEquationSolution (rhs : BottcherSpatialSeries) : BottcherSpatialSeries :=
  PowerSeries.mk (dyadicEquationSolutionCoeff rhs)

theorem coeff_dyadicEquationSolution (rhs : BottcherSpatialSeries) (n : ℕ) :
    (coeff n) (dyadicEquationSolution rhs) = dyadicEquationSolutionCoeff rhs n :=
  coeff_mk n _

/-- Binary descent is exactly the coefficient recursion of the inhomogeneous dyadic equation. -/
theorem dyadicEquationSolutionCoeff_key (rhs : BottcherSpatialSeries) (n : ℕ) :
    (if 2 ∣ n then dyadicEquationSolutionCoeff rhs (n / 2) else 0) =
      2 * dyadicEquationSolutionCoeff rhs n + (coeff n) rhs := by
  classical
  rcases n with _ | n
  · rw [if_pos ⟨0, rfl⟩]
    simp [dyadicEquationSolutionCoeff]
    ring
  · rw [show dyadicEquationSolutionCoeff rhs (n + 1) =
      ((if 2 ∣ n + 1 then dyadicEquationSolutionCoeff rhs ((n + 1) / 2) else 0) -
        (coeff (n + 1)) rhs) / 2 from by rw [dyadicEquationSolutionCoeff]]
    ring_nf

/-- The generic binary-descent solution satisfies its dyadic Mahler equation. -/
theorem dyadicSubst_dyadicEquationSolution (rhs : BottcherSpatialSeries) :
    dyadicSubst (dyadicEquationSolution rhs) =
      2 * dyadicEquationSolution rhs + rhs := by
  classical
  ext n
  rw [show (coeff n) (dyadicSubst (dyadicEquationSolution rhs)) =
    (if 2 ∣ n then (coeff (n / 2)) (dyadicEquationSolution rhs) else 0) from by
      rw [dyadicSubst, coeff_mk]]
  rw [coeff_dyadicEquationSolution]
  rw [show 2 * dyadicEquationSolution rhs =
    dyadicEquationSolution rhs + dyadicEquationSolution rhs from two_mul _]
  rw [map_add, map_add, coeff_dyadicEquationSolution]
  simpa [two_mul] using dyadicEquationSolutionCoeff_key rhs n

/-- Coefficient form of an inhomogeneous dyadic Mahler equation. -/
theorem dyadicEquation_coeff {f rhs : BottcherSpatialSeries}
    (h : dyadicSubst f = 2 * f + rhs) (n : ℕ) :
    (if 2 ∣ n then (coeff (n / 2)) f else 0) =
      2 * (coeff n) f + (coeff n) rhs := by
  have hc := congrArg (coeff n) h
  rw [show (coeff n) (dyadicSubst f) =
    (if 2 ∣ n then (coeff (n / 2)) f else 0) from by
      rw [dyadicSubst, coeff_mk]] at hc
  rw [show 2 * f = f + f from two_mul _, map_add, map_add] at hc
  simpa [two_mul] using hc

/-- The inhomogeneous dyadic equation has a unique formal power-series solution. -/
theorem dyadicEquationSolution_unique {f rhs : BottcherSpatialSeries}
    (hf : dyadicSubst f = 2 * f + rhs) :
    f = dyadicEquationSolution rhs := by
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      have hfn := dyadicEquation_coeff hf n
      have hsn := dyadicEquation_coeff (dyadicSubst_dyadicEquationSolution rhs) n
      rcases n with _ | n
      · simp only [Nat.zero_div, dvd_zero, if_pos] at hfn hsn
        linear_combination -hfn + hsn
      · by_cases hd : 2 ∣ n + 1
        · rw [if_pos hd] at hfn hsn
          rw [ih ((n + 1) / 2) (Nat.div_lt_self (Nat.succ_pos n) one_lt_two)] at hfn
          have htwo : (2 : ℂ) * (coeff (n + 1)) f =
              2 * (coeff (n + 1)) (dyadicEquationSolution rhs) := by
            linear_combination -hfn + hsn
          exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) htwo
        · rw [if_neg hd] at hfn hsn
          have htwo : (2 : ℂ) * (coeff (n + 1)) f =
              2 * (coeff (n + 1)) (dyadicEquationSolution rhs) := by
            linear_combination -hfn + hsn
          exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) htwo

/-- The canonical all-order logarithmic Böttcher jet family. At depth `r+1`, only the already
constructed depths `a < r+1` enter the mixed Taylor coefficient. -/
noncomputable def allOrderBottcherJet : ℕ → BottcherSpatialSeries
  | 0 => 0
  | r + 1 =>
      let previous : ℕ → BottcherSpatialSeries := fun a =>
        if _h : a < r + 1 then allOrderBottcherJet a else 0
      dyadicEquationSolution
        (bottcherLogJetTerm (r + 1) -
          bottcherMixedSubstitutionCoeff (bottcherDyadicSpatialJet previous) (r + 1))
termination_by r => r

theorem allOrderBottcherJet_succ (r : ℕ) :
    allOrderBottcherJet (r + 1) =
      let previous : ℕ → BottcherSpatialSeries := fun a =>
        if _h : a < r + 1 then allOrderBottcherJet a else 0
      dyadicEquationSolution
        (bottcherLogJetTerm (r + 1) -
          bottcherMixedSubstitutionCoeff (bottcherDyadicSpatialJet previous) (r + 1)) := by
  rw [allOrderBottcherJet]

/-- Truncating the recursively available jet family does not change the mixed coefficient at the
current depth, because every summand uses a strictly earlier parameter jet. -/
theorem bottcherMixedSubstitutionCoeff_previous (r : ℕ) :
    let previous : ℕ → BottcherSpatialSeries := fun a =>
      if _h : a < r then allOrderBottcherJet a else 0
    bottcherMixedSubstitutionCoeff (bottcherDyadicSpatialJet previous) r =
      bottcherMixedSubstitutionCoeff (bottcherDyadicSpatialJet allOrderBottcherJet) r := by
  classical
  dsimp only
  unfold bottcherMixedSubstitutionCoeff
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mem_Icc] at ha
  have har : a < r := by omega
  apply Finset.sum_congr rfl
  intro b hb
  rw [show bottcherDyadicSpatialJet
      (fun j => if _h : j < r then allOrderBottcherJet j else 0) a b =
      bottcherDyadicSpatialJet allOrderBottcherJet a b by
        simp [bottcherDyadicSpatialJet, har]]

/-- The canonical family satisfies the unexpanded coefficient form of the normalized Böttcher
constraint at every positive depth. -/
theorem allOrderBottcherJet_isSystem :
    IsBottcherLogJetSystem allOrderBottcherJet := by
  intro r hr
  rcases r with _ | r
  · omega
  · have hjet : allOrderBottcherJet (r + 1) =
        dyadicEquationSolution
          (bottcherLogJetTerm (r + 1) -
            bottcherMixedSubstitutionCoeff
              (bottcherDyadicSpatialJet allOrderBottcherJet) (r + 1)) := by
      rw [allOrderBottcherJet_succ]
      dsimp only
      rw [bottcherMixedSubstitutionCoeff_previous]
    rw [hjet, dyadicSubst_dyadicEquationSolution]
    abel

/-- **Unconditional all-order Böttcher parameter--spatial jet law for the canonical formal
family.** -/
theorem allOrderBottcherJet_law {r : ℕ} (hr : 1 ≤ r) :
    dyadicSubst (allOrderBottcherJet r) =
      2 * allOrderBottcherJet r + bottcherLogJetTerm r -
        ∑ a ∈ Finset.Icc 1 (r - 1), ∑ b ∈ Finset.Icc 1 (r - a),
          bottcherJetWeight r a b •
            ((X ^ (2 * (r - a + b)) : BottcherSpatialSeries) *
              bottcherDyadicSpatialJet allOrderBottcherJet a b) :=
  bottcher_all_order_parameter_spatial_jet_law allOrderBottcherJet_isSystem hr

/-- The first member of the canonical all-order family is the previously constructed first
Böttcher velocity jet. -/
theorem allOrderBottcherJet_one_eq_velocityJet :
    allOrderBottcherJet 1 = velocityJet := by
  have hcanonical :
      dyadicSubst (allOrderBottcherJet 1) =
        2 * allOrderBottcherJet 1 + (-(X ^ (2 : ℕ) : BottcherSpatialSeries)) := by
    have h := allOrderBottcherJet_law (r := 1) (by omega)
    simpa [bottcherLogJetTerm] using h
  have hvelocity :
      dyadicSubst velocityJet =
        2 * velocityJet + (-(X ^ (2 : ℕ) : BottcherSpatialSeries)) := by
    simpa [sub_eq_add_neg] using dyadicSubst_velocityJet
  calc
    allOrderBottcherJet 1 =
        dyadicEquationSolution (-(X ^ (2 : ℕ) : BottcherSpatialSeries)) :=
      dyadicEquationSolution_unique hcanonical
    _ = velocityJet := (dyadicEquationSolution_unique hvelocity).symm

end

end GaloisForLFunctions
