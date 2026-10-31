import GaloisForLFunctions.ArithmeticIncidencePositivity.ShiftedGroundStateAndFirstJetAtomPoleLaw

/-!
# Closed shift thresholds for fixed-support collars

The double-exponential collar ratio yields an explicit sufficient shift.
The positive midpoint gap then gives a concrete threshold for each actual
integer atom outside the five exceptional moduli.
-/

open MeasureTheory Set Real
open RHTower RHTower.CHMDPolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
noncomputable section
namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- The pointwise collar estimates imply positivity under explicit scalar inequalities. -/
theorem shiftedGroundState_collar_integral_pos_of_bounds
    {g : ℝ → ℝ} {L δ m B a : ℝ}
    (hL : 0 < L) (hg : Continuous g) (hm : 0 < m) (hB0 : 0 < B)
    (hδ0 : 0 < δ) (hδL : δ ≤ L / 4)
    (hg_mid : ∀ x, |x - L / 2| ≤ δ → m ≤ g x)
    (hg_low : ∀ x ∈ Icc 0 L, -B ≤ g x)
    (ha3 : L + Real.log 3 / 2 ≤ a) (ha2 : L + Real.log 2 / 2 ≤ a)
    (hexp : Real.log 2 ≤ π * Real.exp (2 * (a - L)) * (L / 2))
    (hsmall : L * B * Real.exp (5 * L + 4 * π * L) *
      Real.exp (-(2 * π * Real.exp (2 * a - L) *
        (Real.cosh (2 * δ) - Real.cosh δ))) < δ * m * (1 / 4)) :
    0 < ∫ x in Ioo (0 : ℝ) L,
      shiftDifference a x * shiftDifference a (L - x) * g x := by
  rw [setIntegral_Ioo_eq_intervalIntegral hL.le]
  set F : ℝ → ℝ := fun x => shiftDifference a x * shiftDifference a (L - x) * g x
  have hF : Continuous F :=
    ((continuous_shiftDifference a).mul
      ((continuous_shiftDifference a).comp (continuous_const.sub continuous_id))).mul hg
  have hΦaL := riemannKernelReal_pos (a - L)
  set C₀ := riemannKernelReal (a - L) ^ 2 * Real.exp (2 * π * Real.exp (2 * (a - L)))
  have hC₀ : 0 < C₀ := by positivity
  set M_out := C₀ * Real.exp (5 * L - 2 * π * Real.exp (2 * a - L) * Real.cosh (2 * δ))
  set M_in := 1 / 4 * C₀ * Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ)
  have hM_out : ∀ x ∈ Icc 0 L, δ ≤ |x - L / 2| →
      shiftDifference a x * shiftDifference a (L - x) ≤ M_out := fun x hx hxδ => by
    have h := shiftDifference_collar_le_of_abs_sub_ge ha3 hδ0.le hx hxδ
    have heq : M_out = riemannKernelReal (a - L) ^ 2 *
        Real.exp (2 * π * Real.exp (2 * (a - L)) + 5 * L -
          2 * π * Real.exp (2 * a - L) * Real.cosh (2 * δ)) := by
      dsimp [M_out, C₀]
      rw [mul_assoc, ← Real.exp_add]
      congr 2; ring
    rwa [heq]
  have hM_in : ∀ x, |x - L / 2| ≤ δ / 2 →
      M_in ≤ shiftDifference a x * shiftDifference a (L - x) := fun x hx => by
    have h := shiftDifference_collar_ge_of_abs_sub_le hL ha2 hexp hδ0.le (by linarith) hx
    have heq : M_in = 1 / 4 * riemannKernelReal (a - L) ^ 2 *
        Real.exp (2 * π * Real.exp (2 * (a - L)) - 4 * π * L -
          2 * π * Real.exp (2 * a - L) * Real.cosh δ) := by
      dsimp [M_in, C₀]
      rw [show 1 / 4 * (riemannKernelReal (a - L) ^ 2 * Real.exp (2 * π * Real.exp (2 * (a - L)))) *
          Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ) =
        1 / 4 * riemannKernelReal (a - L) ^ 2 *
          (Real.exp (2 * π * Real.exp (2 * (a - L))) *
            Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ)) by ring,
        ← Real.exp_add]
      congr 2; ring
    rwa [heq]
  have ha0 : 0 < a := by
    have : 0 < Real.log 2 := Real.log_pos one_lt_two
    linarith
  have hcoll_nn : ∀ x ∈ Icc 0 L, 0 ≤ shiftDifference a x * shiftDifference a (L - x) :=
    fun x hx => mul_nonneg (shiftDifference_nonneg_of_nonneg ha0.le hx.1)
      (shiftDifference_nonneg_of_nonneg ha0.le (by linarith [hx.2]))
  have hI1 : -(B * M_out) * (L / 2 - δ - 0) ≤ ∫ x in (0 : ℝ)..(L / 2 - δ), F x := by
    refine mul_sub_le_intervalIntegral_of_le hF (by linarith) fun x hx => ?_
    have hxL : x ∈ Icc 0 L := ⟨hx.1, by linarith [hx.2]⟩
    have hxδ : δ ≤ |x - L / 2| := by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.2]
    have h1 := hM_out x hxL hxδ
    have h2 := hg_low x hxL
    have h3 := hcoll_nn x hxL
    dsimp [F]
    calc
      -(B * M_out) = -B * M_out := by ring
      _ ≤ -B * (shiftDifference a x * shiftDifference a (L - x)) :=
        mul_le_mul_of_nonpos_left h1 (neg_nonpos.mpr hB0.le)
      _ ≤ g x * (shiftDifference a x * shiftDifference a (L - x)) :=
        mul_le_mul_of_nonneg_right h2 h3
      _ = _ := by ring
  have hI2 : 0 * (L / 2 - δ / 2 - (L / 2 - δ)) ≤ ∫ x in (L / 2 - δ)..(L / 2 - δ / 2), F x := by
    refine mul_sub_le_intervalIntegral_of_le hF (by linarith) fun x hx => ?_
    have hxL : x ∈ Icc 0 L := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxδ : |x - L / 2| ≤ δ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_nonneg (hcoll_nn x hxL) (hm.le.trans (hg_mid x hxδ))
  have hI3 : (m * M_in) * (L / 2 + δ / 2 - (L / 2 - δ / 2)) ≤
      ∫ x in (L / 2 - δ / 2)..(L / 2 + δ / 2), F x := by
    refine mul_sub_le_intervalIntegral_of_le hF (by linarith) fun x hx => ?_
    have hxδ2 : |x - L / 2| ≤ δ / 2 := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxδ : |x - L / 2| ≤ δ := hxδ2.trans (by linarith)
    have h1 := hM_in x hxδ2
    have h2 := hg_mid x hxδ
    dsimp [F]
    exact (mul_comm m M_in).le.trans
      (mul_le_mul h1 h2 hm.le ((by positivity : 0 ≤ M_in).trans h1))
  have hI4 : 0 * (L / 2 + δ - (L / 2 + δ / 2)) ≤ ∫ x in (L / 2 + δ / 2)..(L / 2 + δ), F x := by
    refine mul_sub_le_intervalIntegral_of_le hF (by linarith) fun x hx => ?_
    have hxL : x ∈ Icc 0 L := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hxδ : |x - L / 2| ≤ δ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact mul_nonneg (hcoll_nn x hxL) (hm.le.trans (hg_mid x hxδ))
  have hI5 : -(B * M_out) * (L - (L / 2 + δ)) ≤ ∫ x in (L / 2 + δ)..L, F x := by
    refine mul_sub_le_intervalIntegral_of_le hF (by linarith) fun x hx => ?_
    have hxL : x ∈ Icc 0 L := ⟨by linarith [hx.1], hx.2⟩
    have hxδ : δ ≤ |x - L / 2| := by rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.1]
    have h1 := hM_out x hxL hxδ
    have h2 := hg_low x hxL
    have h3 := hcoll_nn x hxL
    dsimp [F]
    calc
      -(B * M_out) = -B * M_out := by ring
      _ ≤ -B * (shiftDifference a x * shiftDifference a (L - x)) :=
        mul_le_mul_of_nonpos_left h1 (neg_nonpos.mpr hB0.le)
      _ ≤ g x * (shiftDifference a x * shiftDifference a (L - x)) :=
        mul_le_mul_of_nonneg_right h2 h3
      _ = _ := by ring
  rw [intervalIntegral_five_split hF L δ]
  have hdiff_pos : 0 < δ * (m * M_in) - L * (B * M_out) := by
    have hrel : L * (B * M_out) =
        C₀ * Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ) *
          (L * B * Real.exp (5 * L + 4 * π * L) *
            Real.exp (-(2 * π * Real.exp (2 * a - L) * (Real.cosh (2 * δ) - Real.cosh δ)))) := by
      dsimp [M_out]
      rw [show C₀ * Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ) *
          (L * B * Real.exp (5 * L + 4 * π * L) *
            Real.exp (-(2 * π * Real.exp (2 * a - L) * (Real.cosh (2 * δ) - Real.cosh δ)))) =
          L * B * C₀ * (Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ) *
            Real.exp (5 * L + 4 * π * L) *
            Real.exp (-(2 * π * Real.exp (2 * a - L) * (Real.cosh (2 * δ) - Real.cosh δ)))) by ring,
        ← Real.exp_add, ← Real.exp_add]
      ring_nf
    have hin_rel : δ * (m * M_in) =
        C₀ * Real.exp (-4 * π * L - 2 * π * Real.exp (2 * a - L) * Real.cosh δ) *
          (δ * m * (1 / 4)) := by
      dsimp [M_in]
      ring
    rw [hin_rel, hrel, ← mul_sub]
    exact mul_pos (by positivity) (sub_pos.mpr hsmall)
  have hBM : 0 ≤ B * M_out := by positivity
  nlinarith only [hI1, hI2, hI3, hI4, hI5, hdiff_pos,
    mul_nonneg hδ0.le hBM]

/-- Closed shift sufficient for a midpoint reserve `m` against a global loss `B`. -/
def collarPaymentShift (L δ m B : ℝ) : ℝ :=
  max (max (L + Real.log 3 / 2) (L + Real.log 2 / 2))
    (max (L + Real.log (2 * Real.log 2 / (π * L)) / 2)
      ((L + Real.log ((1 + 5 * L + 4 * π * L + |Real.log (4 * L * B / (δ * m))|) /
        (2 * π * (Real.cosh (2 * δ) - Real.cosh δ)))) / 2))

/-- The closed threshold pays the full collar integral without an asymptotic step. -/
theorem shiftedGroundState_collar_integral_pos_at_explicit_shift
    {g : ℝ → ℝ} {L δ m B a : ℝ}
    (hL : 0 < L) (hg : Continuous g) (hm : 0 < m) (hB : 0 < B)
    (hδ : 0 < δ) (hδL : δ ≤ L / 4)
    (hg_mid : ∀ x, |x - L / 2| ≤ δ → m ≤ g x)
    (hg_low : ∀ x ∈ Icc 0 L, -B ≤ g x)
    (ha : collarPaymentShift L δ m B ≤ a) :
    0 < ∫ x in Ioo (0 : ℝ) L,
      shiftDifference a x * shiftDifference a (L - x) * g x := by
  obtain ⟨⟨ha3, ha2⟩, haE, haU⟩ :=
    (max_le_iff.mp ha).imp (max_le_iff.mp) (max_le_iff.mp)
  have hπL : 0 < π * L := mul_pos Real.pi_pos hL
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hexp : Real.log 2 ≤ π * Real.exp (2 * (a - L)) * (L / 2) := by
    have h := Real.exp_le_exp.mpr
      (show Real.log (2 * Real.log 2 / (π * L)) ≤ 2 * (a - L) by linarith only [haE])
    rw [Real.exp_log (div_pos (mul_pos two_pos hlog2) hπL)] at h
    have h' := (div_le_iff₀ hπL).mp h
    nlinarith only [h']
  have hΔ : 0 < Real.cosh (2 * δ) - Real.cosh δ := by
    apply sub_pos.mpr
    rw [Real.cosh_lt_cosh, abs_of_pos hδ, abs_of_pos (mul_pos two_pos hδ)]
    linarith only [hδ]
  set D := 4 * L * B / (δ * m)
  set U := 1 + 5 * L + 4 * π * L + |Real.log D|
  have hD : 0 < D := by dsimp [D]; positivity
  have hU : 0 < U := by dsimp [U]; positivity
  have hden : 0 < 2 * π * (Real.cosh (2 * δ) - Real.cosh δ) := by positivity
  have hu : U ≤ 2 * π * Real.exp (2 * a - L) *
      (Real.cosh (2 * δ) - Real.cosh δ) := by
    have h := Real.exp_le_exp.mpr
      (show Real.log (U / (2 * π * (Real.cosh (2 * δ) - Real.cosh δ))) ≤
        2 * a - L by linarith only [haU])
    rw [Real.exp_log (div_pos hU hden)] at h
    have h' := (div_le_iff₀ hden).mp h
    nlinarith only [h']
  have hsmall : L * B * Real.exp (5 * L + 4 * π * L) *
      Real.exp (-(2 * π * Real.exp (2 * a - L) *
        (Real.cosh (2 * δ) - Real.cosh δ))) < δ * m * (1 / 4) := by
    calc
      _ = L * B * Real.exp (5 * L + 4 * π * L -
          2 * π * Real.exp (2 * a - L) * (Real.cosh (2 * δ) - Real.cosh δ)) := by
        rw [mul_assoc, ← Real.exp_add]
        rfl
      _ < L * B * Real.exp (-Real.log D) := by
        apply mul_lt_mul_of_pos_left _ (mul_pos hL hB)
        apply Real.exp_lt_exp.mpr
        dsimp [U] at hu
        linarith only [hu, le_abs_self (Real.log D)]
      _ = δ * m * (1 / 4) := by
        rw [Real.exp_neg, Real.exp_log hD]
        dsimp [D]
        field_simp [hL.ne', hB.ne', hδ.ne', hm.ne'] <;> ring
  exact shiftedGroundState_collar_integral_pos_of_bounds hL hg hm hB hδ hδL
    hg_mid hg_low ha3 ha2 hexp hsmall

/-- The midpoint margin of an integer atom. -/
def atomCollarMargin (n : ℕ) : ℝ :=
  Real.cosh (Real.log n / 2) - 1 - vonMangoldtAtom n

/-- A midpoint interval on which half the atom margin survives. -/
def atomCollarRadius (n : ℕ) : ℝ :=
  min (Real.log n / 4) (Real.log (1 + atomCollarMargin n / 2))

/-- Explicit sufficient shift for the ground-state collar of an integer atom. -/
def atomCollarShiftThreshold (n : ℕ) : ℝ :=
  collarPaymentShift (Real.log n) (atomCollarRadius n)
    (atomCollarMargin n / 2) (1 + vonMangoldtAtom n)

/-- Every nonexceptional atom is paid at every shift beyond its closed threshold. -/
theorem collarAtomMass_lt_collarPolarMass_at_explicit_shift
    {n : ℕ} (hn : 2 ≤ n) (hn5 : n ∉ atomDominatedModuli) {a : ℝ}
    (ha : atomCollarShiftThreshold n ≤ a) :
    collarAtomMass (shiftDifference a) n < collarPolarMass (shiftDifference a) n := by
  have hL : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hb : 0 < atomCollarMargin n := by
    have h := vonMangoldtAtom_lt_crossingPolarWeight_midpoint_of_not_mem hn hn5
    rw [crossingPolarWeight_eq, sub_self, Real.cosh_zero] at h
    exact sub_pos.mpr h
  have hv : 0 ≤ vonMangoldtAtom n := by
    rw [vonMangoldtAtom, if_pos hn]
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hδ : 0 < atomCollarRadius n := lt_min (by positivity)
    (Real.log_pos (by linarith only [hb]))
  have hδL : atomCollarRadius n ≤ Real.log n / 4 := min_le_left _ _
  have hgmid : ∀ x, |x - Real.log n / 2| ≤ atomCollarRadius n →
      atomCollarMargin n / 2 ≤ crossingPolarWeight (Real.log n) x - vonMangoldtAtom n := by
    intro x hx
    have hcosh : Real.cosh (Real.log n / 2 - x) ≤ 1 + atomCollarMargin n / 2 := by
      have hexp : Real.exp |Real.log n / 2 - x| ≤ 1 + atomCollarMargin n / 2 := by
        calc
          _ ≤ Real.exp (Real.log (1 + atomCollarMargin n / 2)) := by
            apply Real.exp_le_exp.mpr
            rw [abs_sub_comm]
            exact hx.trans (min_le_right _ _)
          _ = _ := Real.exp_log (by linarith only [hb])
      have h1 := Real.exp_le_exp.mpr (le_abs_self (Real.log n / 2 - x))
      have h2 := Real.exp_le_exp.mpr (neg_le_abs (Real.log n / 2 - x))
      rw [Real.cosh_eq]
      linarith only [hexp, h1, h2]
    rw [crossingPolarWeight_eq]
    dsimp [atomCollarMargin] at *
    linarith only [hcosh]
  have hglow : ∀ x ∈ Icc 0 (Real.log n), -(1 + vonMangoldtAtom n) ≤
      crossingPolarWeight (Real.log n) x - vonMangoldtAtom n := by
    intro x hx
    linarith only [crossingPolarWeight_nonneg hx.1 hx.2]
  rw [← sub_pos, collarPolarMass_sub_collarAtomMass (continuous_shiftDifference a)]
  exact shiftedGroundState_collar_integral_pos_at_explicit_shift hL
    ((continuous_crossingPolarWeight _).sub continuous_const) (by positivity)
    (by positivity) hδ hδL hgmid hglow ha

/-- A finite collection is paid simultaneously at the maximum of its thresholds. -/
theorem finite_collarAtomMass_lt_collarPolarMass_at_explicit_shift
    (S : Finset ℕ) (hS : S.Nonempty)
    (hn : ∀ n ∈ S, 2 ≤ n ∧ n ∉ atomDominatedModuli) {a : ℝ}
    (ha : S.sup' hS atomCollarShiftThreshold ≤ a) :
    ∀ n ∈ S, collarAtomMass (shiftDifference a) n < collarPolarMass (shiftDifference a) n := by
  intro n hnS
  exact collarAtomMass_lt_collarPolarMass_at_explicit_shift (hn n hnS).1 (hn n hnS).2
    ((Finset.le_sup' atomCollarShiftThreshold hnS).trans ha)

end GaloisForLFunctions.ArithmeticIncidencePositivity

#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.collarAtomMass_lt_collarPolarMass_at_explicit_shift
#print axioms GaloisForLFunctions.ArithmeticIncidencePositivity.finite_collarAtomMass_lt_collarPolarMass_at_explicit_shift
