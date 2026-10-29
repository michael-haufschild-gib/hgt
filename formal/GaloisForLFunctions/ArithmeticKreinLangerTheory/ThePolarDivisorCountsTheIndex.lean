import GaloisForLFunctions.RHTower.InfiniteSymmetry.ConfinementIsTheSquareRootCount
import GaloisForLFunctions.ArithmeticKreinLangerTheory.TheTwistTowerCompletesTheUpperCount

/-!
# The polar divisor counts the index

The infinite-symmetry route continues the affine `A₁` Weyl sum of a curve datum and finds that its
poles in the band `−1 < Re s < 0` are the shifted zeros of the datum's zeta function
(`RHTower.InfiniteSymmetry`): confinement of the polar divisor to `Re s = −1/2` is the lower
square-root count. In Krein–Langer language the polar divisor is a spectral picture of the trace
kernel.

**Position of a pole** (`re_poleParameter`). The pole attached to the eigenvalue `β_i` has real part
`−1/2 + log |β_i| / log q`: it lies right of the critical hyperplane exactly for an outer eigenvalue
(`neg_half_lt_re_poleParameter_iff`).

**The polar index formula** (`negIndex_traceKernel_eq_card_rightPoles`). The index of the trace
kernel is the number of distinct pole classes (pole parameters, modulo the period `2πi/log q`) right
of the critical hyperplane. So polar-divisor spectral theory is the index theory of the trace kernel:
confinement is index zero (`polarConfinement_iff_negIndex_eq_zero`), and over `𝔽_q` it is produced
by the twist tower of upper counts (`polarConfinement_iff_twistTower_upper`). For the golden datum
one pole class lies off the hyperplane and the index is one, the genus ceiling.
-/

open Complex Finset
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (CurveDatum)
open GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.RHTower.InfiniteSymmetry (PolarConfinement polarConfinement_iff_lowerCount)
open GaloisForLFunctions.RHTower.InfiniteSymmetry.CurveDatum (StripCondition poleParameter
  unitary_iff_poles_on_critical_hyperplane log_q_pos)

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- **Position of a pole.** `Re s_i = −1/2 + log |β_i| / log q`. -/
theorem re_poleParameter (i : ι) :
    (poleParameter D i).re = -(1 / 2 : ℝ) + Real.log ‖D.β i‖ / Real.log D.q := by
  have hq := log_q_pos D
  have hβ : ‖D.β i‖ ≠ 0 := norm_ne_zero_iff.mpr (CurveDatumKernel.β_ne_zero D i)
  have hs : D.sqrtq ≠ 0 := (Real.sqrt_pos.mpr (lt_trans one_pos D.one_lt_q)).ne'
  have hsq : Real.log D.sqrtq = Real.log D.q / 2 :=
    Real.log_sqrt (lt_trans one_pos D.one_lt_q).le
  rw [poleParameter, sub_re, div_ofReal_re, log_re, ArithmeticCastelnuovoSeveri.CurveDatum.alpha,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg D.sqrtq_pos.le, Real.log_mul hs hβ, hsq, one_re]
  field_simp
  ring

/-- A pole lies right of the critical hyperplane exactly for an outer eigenvalue. -/
theorem neg_half_lt_re_poleParameter_iff (i : ι) :
    -(1 / 2 : ℝ) < (poleParameter D i).re ↔ 1 < ‖D.β i‖ := by
  have hq := log_q_pos D
  have hβ : 0 < ‖D.β i‖ := norm_pos_iff.mpr (CurveDatumKernel.β_ne_zero D i)
  rw [re_poleParameter, lt_add_iff_pos_right, div_pos_iff_of_pos_right hq, Real.log_pos_iff hβ.le]

/-- Distinct eigenvalues give distinct pole parameters. -/
theorem poleParameter_eq_iff (i j : ι) : poleParameter D i = poleParameter D j ↔ D.β i = D.β j := by
  have hq : (Real.log D.q : ℂ) ≠ 0 := ofReal_ne_zero.mpr (log_q_pos D).ne'
  have hs : (D.sqrtq : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (lt_trans one_pos D.one_lt_q)).ne'
  constructor
  · intro h
    have hα : ArithmeticCastelnuovoSeveri.CurveDatum.alpha D i =
        ArithmeticCastelnuovoSeveri.CurveDatum.alpha D j := by
      have hlog : Complex.log (ArithmeticCastelnuovoSeveri.CurveDatum.alpha D i) =
          Complex.log (ArithmeticCastelnuovoSeveri.CurveDatum.alpha D j) := by
        simpa [poleParameter, div_left_inj' hq] using h
      have hi : ArithmeticCastelnuovoSeveri.CurveDatum.alpha D i ≠ 0 :=
        mul_ne_zero hs (CurveDatumKernel.β_ne_zero D i)
      have hj : ArithmeticCastelnuovoSeveri.CurveDatum.alpha D j ≠ 0 :=
        mul_ne_zero hs (CurveDatumKernel.β_ne_zero D j)
      rw [← Complex.exp_log hi, ← Complex.exp_log hj, hlog]
    exact mul_left_cancel₀ hs hα
  · intro h
    simp only [poleParameter, ArithmeticCastelnuovoSeveri.CurveDatum.alpha, h]

/-- **The polar index formula.** The index of the trace kernel is the number of distinct pole
parameters right of the critical hyperplane. -/
theorem negIndex_traceKernel_eq_card_rightPoles :
    negIndex (traceKernel D) =
      ((univ.filter fun i => -(1 / 2 : ℝ) < (poleParameter D i).re).image (poleParameter D)).card := by
  classical
  rw [negIndex_traceKernel]
  have hset : (univ.filter fun i => -(1 / 2 : ℝ) < (poleParameter D i).re) =
      CurveDatumKernel.outer D := by
    ext i
    simp only [mem_filter, mem_univ, true_and, CurveDatumKernel.outer]
    exact neg_half_lt_re_poleParameter_iff D i
  rw [hset]
  congr 1
  -- the two images have the same size: pole parameters and eigenvalues determine each other
  refine card_bij (fun b hb => poleParameter D (Classical.choose (mem_image.mp hb)))
    (fun b hb => mem_image.mpr ⟨_, (Classical.choose_spec (mem_image.mp hb)).1, rfl⟩) ?_ ?_
  · intro b hb b' hb' h
    have e := (poleParameter_eq_iff D _ _).mp h
    rw [(Classical.choose_spec (mem_image.mp hb)).2,
      (Classical.choose_spec (mem_image.mp hb')).2] at e
    exact e
  · intro s hs
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hs
    refine ⟨D.β i, mem_image.mpr ⟨i, hi, rfl⟩, ?_⟩
    exact (poleParameter_eq_iff D _ _).mpr (Classical.choose_spec (mem_image.mp
      (mem_image.mpr ⟨i, hi, rfl⟩))).2

/-- **Confinement is index zero.** -/
theorem polarConfinement_iff_negIndex_eq_zero (hD : StripCondition D) :
    PolarConfinement D ↔ negIndex (traceKernel D) = 0 :=
  (unitary_iff_poles_on_critical_hyperplane D hD).symm.trans (negIndex_traceKernel_eq_zero_iff D).symm

/-- **Confinement is produced by the twist tower.** Over `𝔽_q`, confinement of the polar divisor is
equivalent to upper counts, with one constant, for the quadratic twists of all `2`-power base
changes. -/
theorem polarConfinement_iff_twistTower_upper (hD : StripCondition D) :
    PolarConfinement D ↔ ∃ C : ℝ, ∀ j m : ℕ,
      twistCount D (2 ^ j) m ≤ D.q ^ (2 ^ j * m) + 1 + C * D.sqrtq ^ (2 ^ j * m) :=
  (unitary_iff_poles_on_critical_hyperplane D hD).symm.trans (unitary_iff_twistTower_upper D)

/-- **The golden datum has one pole class right of the hyperplane**, the genus ceiling. -/
theorem golden_card_rightPoles :
    ((univ.filter fun i => -(1 / 2 : ℝ) < (poleParameter ArithmeticCastelnuovoSeveri.goldenDatum i).re).image
      (poleParameter ArithmeticCastelnuovoSeveri.goldenDatum)).card = 1 := by
  have h := golden_attains_ceiling
  rw [negIndex_traceKernel_eq_card_rightPoles] at h
  simp only [Fintype.card_fin] at h
  have h2 : 2 * ((univ.filter fun i => -(1 / 2 : ℝ) <
      (poleParameter ArithmeticCastelnuovoSeveri.goldenDatum i).re).image
      (poleParameter ArithmeticCastelnuovoSeveri.goldenDatum)).card = 2 := by exact_mod_cast h
  omega

end GaloisForLFunctions.ArithmeticKreinLangerTheory

open GaloisForLFunctions.ArithmeticKreinLangerTheory in
#print axioms golden_card_rightPoles
