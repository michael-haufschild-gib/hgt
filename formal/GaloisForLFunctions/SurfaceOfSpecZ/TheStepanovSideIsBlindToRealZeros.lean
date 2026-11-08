import GaloisForLFunctions.SurfaceOfSpecZ.OneSidedHasseWeilAtTheIntegerDegrees
import GaloisForLFunctions.RHTower.ErrorExponentAbscissaExcessLaw

/-!
# The Stepanov side is blind to real zeros

`OneSidedHasseWeilAtTheIntegerDegrees` proves that an upper bound on the smoothed point counts of
`Spec ℤ`, i.e. `c_B ≥ −K`, is RH. The proof uses one arithmetic input besides Landau's theorem: `ζ`
has no real zero in the strip. This file shows that the input is necessary and sufficient for the
Stepanov side, for every configuration of zeros.

* `onLine_of_two_re_lagStructure_ge`: for a tempered configuration without real zeros, a lower bound
  `2 Re S(u) ≥ −K` on the spline lag structure puts every zero on the critical line.
* `stepanov_side_blind_to_real_zeros`: for the real pair `{¼, ¾}` (`RHTower.offLinePairConfig 0`)
  the spline lag structure is `A(e^{u/4} + e^{−u/4})` with `A > 0`: bounded below by `0`, unbounded
  above. The Stepanov side passes; the other side sees the off-line pair.

On a curve the same phenomenon is the reason Bombieri–Stepanov needs a second count: an upper bound
`N_n ≤ qⁿ + O(q^{n/2})` cannot exclude a real Frobenius eigenvalue `α > √q`, which only lowers the
point counts; the twisted curve, whose counts are `2(qⁿ + 1) − N_n` in the hyperelliptic case, supplies
the other side. Over `ℤ` the absence of real zeros of `ζ` replaces the twist.
-/

open Complex Set Filter Topology Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ

open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23

/-! ### Without real zeros the Stepanov side decides the line -/

/-- **The Stepanov side, for any configuration without real zeros.** -/
theorem onLine_of_two_re_lagStructure_ge (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) {K : ℝ}
    (hK : ∀ u : ℝ, 0 ≤ u → -K ≤ 2 * (lagStructure Z (boxSpline 1 3) u).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := by
  have hb := contDiff_boxSpline (r := 1) one_pos 2
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hbc := hasCompactSupport_of_support_subset_abs hbs
  -- exponents of `2 Re S` are non-real
  have hreal : ∀ x : ℂ, evenCoeff Z (boxSpline 1 3) x ≠ 0 → x.im = 0 → x.re ≤ 0 := by
    intro x hx him
    exfalso
    rcases mem_of_evenCoeff_ne_zero hx with h | h
    · exact hnoreal _ h (by simp [him])
    · exact hnoreal _ h (by simp [him])
  have hzero : ∀ z : ℂ, 0 < z.re → evenCoeff Z (boxSpline 1 3) z = 0 := fun z hz =>
    evenCoeff_eq_zero_of_two_re_lagStructure_ge Z hZ hb hbs le_rfl (by norm_num) hreal
      (M := K) (fun u hu => by rw [zero_mul, Real.exp_zero, mul_one]; exact hK u hu) hz
  -- a right zero would be seen
  have hright : ∀ ρ ∈ Z.carrier, ρ.re ≤ 1 / 2 := by
    intro ρ hρ
    by_contra hre
    push Not at hre
    exact evenCoeff_sub_half_ne_zero_of_conj_symm Z hb.continuous hbc
      (conj_paperFT_boxSpline _ _) (paperFT_boxSpline_neg _ _) hρ
      (paperFT_boxSpline_ne_zero one_pos 3 (im_gammaOf_ne_zero (by linarith)))
      (hzero _ (by simp; linarith))
  intro ρ hρ
  have h1 := hright ρ hρ
  have h2 := hright (Zeta23.reflect ρ) (Z.reflect_mem ρ hρ)
  have hrefl : (Zeta23.reflect ρ).re = 1 - ρ.re := by simp [Zeta23.reflect]
  linarith

/-! ### The real pair `{¼, ¾}` -/

/-- The real pair `{¾, ¼}`. -/
abbrev realPair : ZeroConfig := _root_.RHTower.offLinePairConfig 0

theorem temperedConfig_realPair : TemperedConfig realPair := by
  haveI : Finite realPair.carrier := (Set.toFinite _).to_subtype
  exact Summable.of_finite

theorem mem_realPair_iff (ρ : ℂ) : ρ ∈ realPair.carrier ↔ ρ = 3 / 4 ∨ ρ = 1 / 4 := by
  change ρ ∈ ({⟨3 / 4, 0⟩, ⟨1 / 4, 0⟩} : Set ℂ) ↔ _
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · left; rw [h]; apply Complex.ext <;> norm_num
    · right; rw [h]; apply Complex.ext <;> norm_num
  · rintro (h | h)
    · left; rw [h]; apply Complex.ext <;> norm_num
    · right; rw [h]; apply Complex.ext <;> norm_num

/-- `ĥ(−i/4)` for the spline `h = U_1^{⋆4}`, a real number. -/
def quarterValue : ℝ := (paperFT (boxSpline 1 3) (-(I * (1 / 4)))).re

theorem paperFT_spline_quarter :
    quarterValue ≠ 0 ∧ paperFT (boxSpline 1 3) (-(I * (1 / 4))) = quarterValue ∧
      paperFT (boxSpline 1 3) (-(I * (-1 / 4))) = quarterValue := by
  set w := paperFT (boxSpline 1 3) (-(I * (1 / 4))) with hw
  have heven : paperFT (boxSpline 1 3) (-(I * (-1 / 4))) = w := by
    rw [hw, ← paperFT_boxSpline_neg 1 3 (-(I * (1 / 4)))]
    congr 1; ring
  have hreal : conj w = w := by
    have h := conj_paperFT_boxSpline 1 3 (-(I * (1 / 4)))
    rw [show conj (-(I * (1 / 4) : ℂ)) = -(I * (-1 / 4)) by
      simp [map_neg, map_mul, Complex.conj_I]; ring, heven] at h
    rw [hw]; exact h
  have him : w.im = 0 := by
    have := congrArg Complex.im hreal
    simp only [Complex.conj_im] at this
    linarith
  have hne : w ≠ 0 := paperFT_boxSpline_ne_zero one_pos 3 (by simp)
  have hwr : w = (quarterValue : ℂ) := Complex.ext (by simp [quarterValue, hw]) (by simp [him])
  refine ⟨fun h0 => hne (by rw [hwr, h0, Complex.ofReal_zero]), hwr, ?_⟩
  rw [heven, hwr]

/-- **The lag structure of the real pair.** `S(u) = ĥ(−i/4)²(e^{u/4} + e^{−u/4})`. -/
theorem lagStructure_realPair (u : ℝ) :
    lagStructure realPair (boxSpline 1 3) u =
      ((quarterValue ^ 2 * (Real.exp (u / 4) + Real.exp (-u / 4)) : ℝ) : ℂ) := by
  obtain ⟨-, hr1, hr2⟩ := paperFT_spline_quarter
  have hb := contDiff_boxSpline (r := 1) one_pos 2
  have hbs := boxSpline_support (r := 1) one_pos 3
  have hbc := hasCompactSupport_of_support_subset_abs hbs
  obtain ⟨-, he⟩ := lagStructure_eq_tsum_lagCoeff realPair temperedConfig_realPair hb hbs u
  have hsupp : ∀ z ∉ ({1 / 4, -1 / 4} : Finset ℂ),
      lagCoeff realPair (boxSpline 1 3) z * cexp (z * u) = 0 := by
    intro z hz
    have hnot : (1 / 2 + z) ∉ realPair.carrier := by
      rw [mem_realPair_iff]
      rintro (h | h)
      · exact hz (by
          rw [Finset.mem_insert]; left
          linear_combination h)
      · exact hz (by
          rw [Finset.mem_insert, Finset.mem_singleton]; right
          linear_combination h)
    rw [lagCoeff, Set.indicator_of_notMem hnot, zero_mul]
  have hq : (1 / 2 + (1 / 4 : ℂ)) ∈ realPair.carrier := by
    rw [mem_realPair_iff]; left; norm_num
  have hq' : (1 / 2 + (-1 / 4 : ℂ)) ∈ realPair.carrier := by
    rw [mem_realPair_iff]; right; norm_num
  have hc1 := lagCoeff_eq_of_conj_symm realPair hb.continuous hbc (conj_paperFT_boxSpline _ _) hq
  have hc2 := lagCoeff_eq_of_conj_symm realPair hb.continuous hbc (conj_paperFT_boxSpline _ _) hq'
  have hm : ∀ ρ : ℂ, realPair.mult ρ = 1 := fun _ => rfl
  rw [he, tsum_eq_sum hsupp, Finset.sum_pair (by norm_num), hc1, hc2, hm, hm, hr1, hr2]
  have h1 : cexp ((1 / 4 : ℂ) * u) = (Real.exp (u / 4) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  have h2 : cexp ((-1 / 4 : ℂ) * u) = (Real.exp (-u / 4) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [h1, h2]
  push_cast
  ring

/-- **The Stepanov side is blind to the real pair.** For the configuration `{¼, ¾}`, which is
off the line, `2 Re S(u) ≥ 0` for every `u`, while `S` is unbounded above. -/
theorem stepanov_side_blind_to_real_zeros :
    (∃ ρ ∈ realPair.carrier, ρ.re ≠ 1 / 2) ∧
      (∀ u : ℝ, 0 ≤ 2 * (lagStructure realPair (boxSpline 1 3) u).re) ∧
      ¬ ∃ K : ℝ, ∀ u : ℝ, 0 ≤ u → (lagStructure realPair (boxSpline 1 3) u).re ≤ K := by
  refine ⟨⟨3 / 4, (mem_realPair_iff _).mpr (Or.inl rfl), by norm_num⟩, fun u => ?_, ?_⟩
  · rw [lagStructure_realPair, Complex.ofReal_re]
    have := Real.exp_pos (u / 4)
    have := Real.exp_pos (-u / 4)
    positivity
  · rintro ⟨K, hK⟩
    have hr2 : 0 < quarterValue ^ 2 := by
      have := paperFT_spline_quarter.1
      positivity
    have htend : Tendsto (fun u : ℝ => quarterValue ^ 2 * Real.exp (u / 4)) atTop atTop :=
      (Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num))).const_mul_atTop hr2
    obtain ⟨u, hu⟩ := ((htend.eventually_gt_atTop K).and (eventually_ge_atTop 0)).exists
    have hK' := hK u hu.2
    rw [lagStructure_realPair, Complex.ofReal_re] at hK'
    have := Real.exp_pos (-u / 4)
    nlinarith [hu.1]

end GaloisForLFunctions.SurfaceOfSpecZ
