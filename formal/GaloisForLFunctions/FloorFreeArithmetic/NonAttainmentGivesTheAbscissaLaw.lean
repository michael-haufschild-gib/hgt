import GaloisForLFunctions.FloorFreeArithmetic.FiniteTopLayersAreSeenOnEveryWindow
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.LengthDependentFloorsGiveTheAbscissaLaw
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheReflectionSectorsOfTheHodgeDefect

/-!
# Non-attainment gives the asymptotic abscissa law

Two receivers for the asymptotic abscissa law of `ζ` that hold at every depth with no exponent
claimed.

* **Window non-attainment.** If the abscissa law fails, the zeros of `ζ` have a finite top layer
  at some depth `b > 0`, and the spline trace normalized by `e^{bu}` is bounded away from zero
  somewhere on every late window of every positive length
  (`uniform_attainment_of_not_asymptoticAbscissaLaw`). Hence one length `L`, depending on the
  depth, with arbitrarily late windows on which the trace is `o(e^{bu})`, gives the law
  (`asymptoticAbscissaLaw_of_windowNonAttainment`). The statement compares the trace with its
  own rate, so it is the same statement at every depth.
* **Unit gap.** The zeros right of a vertical line pair off under complex conjugation, so their
  number is even when finite. The abscissa law is the statement that no line right of the
  critical line has a finite positive number of zeros to its right; at most one is none
  (`asymptoticAbscissaLaw_iff_encard_rightOf_le_one`).
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open SquareRootThreshold Zeta23 SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality
open ZeroConfigurationGeometry ZeroConfigurationGeometry.ConfigAbscissa
open ArithmeticCastelnuovoSeveri

/-! ### Window non-attainment -/

/-- **Uniform attainment in the world of a finite top layer.** If the abscissa law fails, some
depth `b > 0` bounds every zero and the trace normalized by `e^{bu}` exceeds a constant in
absolute value on every late window of every positive length. -/
theorem uniform_attainment_of_not_asymptoticAbscissaLaw
    (hnot : ¬ _root_.RHTower.AsymptoticAbscissaLaw) :
    ∃ b : ℝ, 0 < b ∧ TopDepth zetaZeroConfig b ∧ ∀ L : ℝ, 0 < L →
      ∃ c U : ℝ, 0 < c ∧ ∀ T : ℝ, U ≤ T →
        ∃ u ∈ Icc T (T + L), c ≤ |normTrace zetaZeroConfig b u| := by
  obtain ⟨b, hb, htop, S, hS, hne⟩ := exists_finite_top_of_not_abscissaLaw hnot
  exact ⟨b, hb, htop, fun L hL =>
    finite_top_seen_on_every_window temperedConfig_zetaZeroConfig htop hL S hS hne
      (fun z hz _ => evenCoeff_spline_real hz)⟩

/-- **Window non-attainment gives the abscissa law.** Suppose that for every depth `b > 0`
bounding all zeros there is a length `L > 0` and arbitrarily late windows of length `L` on which
the spline trace is at most `ε e^{bu}`, for every `ε > 0`. Then the asymptotic abscissa law
holds. Length, windows and depth are not linked by any exponent. -/
theorem asymptoticAbscissaLaw_of_windowNonAttainment
    (h : ∀ b : ℝ, 0 < b → TopDepth zetaZeroConfig b →
      ∃ L : ℝ, 0 < L ∧ WindowNonAttainment zetaZeroConfig b L) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  by_contra hnot
  obtain ⟨b, hb, htop, S, hS, hne⟩ := exists_finite_top_of_not_abscissaLaw hnot
  obtain ⟨L, hL, hN⟩ := h b hb htop
  exact not_windowNonAttainment_of_finite_top temperedConfig_zetaZeroConfig htop hL S hS hne
    (fun z hz _ => evenCoeff_spline_real hz) hN

/-- The same criterion on the unnormalized trace: `|2 Re S(u)| ≤ ε e^{bu}` on the window. -/
theorem asymptoticAbscissaLaw_of_trace_below_own_rate
    (h : ∀ b : ℝ, 0 < b → TopDepth zetaZeroConfig b → ∃ L : ℝ, 0 < L ∧
      ∀ ε : ℝ, 0 < ε → ∀ U : ℝ, ∃ T : ℝ, U ≤ T ∧ ∀ u ∈ Icc T (T + L),
        |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re| ≤ ε * Real.exp (b * u)) :
    _root_.RHTower.AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_windowNonAttainment fun b hb htop => ?_
  obtain ⟨L, hL, hwin⟩ := h b hb htop
  refine ⟨L, hL, fun ε hε U => ?_⟩
  obtain ⟨T, hT, hsmall⟩ := hwin ε hε U
  refine ⟨T, hT, fun u hu => ?_⟩
  have hexp : 0 < Real.exp (-(b * u)) := Real.exp_pos _
  have hone : Real.exp (b * u) * Real.exp (-(b * u)) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  rw [normTrace, abs_mul, abs_of_pos hexp]
  calc |2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re| * Real.exp (-(b * u))
      ≤ ε * Real.exp (b * u) * Real.exp (-(b * u)) :=
        mul_le_mul_of_nonneg_right (hsmall u hu) hexp.le
    _ = ε := by rw [mul_assoc, hone, mul_one]

/-! ### The unit gap -/

/-- The zeros of `ζ` right of a vertical line pair off under complex conjugation: their number
is even when finite. -/
theorem even_card_rightOf_zeta {h : ℝ} (hfin : (rightOf zetaZeroConfig h).Finite) :
    Even hfin.toFinset.card := by
  rw [← ZMod.natCast_eq_zero_iff_even, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_involution (fun ρ _ => conj ρ) (fun ρ _ => CharTwo.add_self_eq_zero _)
    (fun ρ hρ _ => ?_) (fun ρ hρ => ?_) (fun ρ _ => Complex.conj_conj ρ)
  · intro hfix
    apply zetaZeroConfig_im_ne_zero' ρ ((Set.Finite.mem_toFinset hfin).mp hρ).1
    have h' := congrArg Complex.im hfix
    simp only [Complex.conj_im] at h'
    linarith only [h']
  · have hρ' := (Set.Finite.mem_toFinset hfin).mp hρ
    rw [Set.Finite.mem_toFinset]
    exact ⟨_root_.RHTower.conj_mem_zetaZeroConfig hρ'.1, by simpa using hρ'.2⟩

/-- At most one zero right of a line is none. -/
theorem rightOf_zeta_eq_empty_of_encard_le_one {h : ℝ}
    (hle : (rightOf zetaZeroConfig h).encard ≤ 1) : rightOf zetaZeroConfig h = ∅ := by
  have hfin : (rightOf zetaZeroConfig h).Finite :=
    Set.encard_lt_top_iff.mp (hle.trans_lt (by norm_num))
  have hc : hfin.toFinset.card ≤ 1 := by
    rw [hfin.encard_eq_coe_toFinset_card] at hle
    exact_mod_cast hle
  obtain ⟨j, hj⟩ := even_card_rightOf_zeta hfin
  have h0 : hfin.toFinset.card = 0 := by omega
  rwa [Finset.card_eq_zero, Set.Finite.toFinset_eq_empty] at h0

/-- **The abscissa law as a unit gap.** The asymptotic abscissa law holds exactly when, for
every line `Re s = ½ + h`, `h ≥ 0`, the number of zeros to its right is at most one or
infinite. -/
theorem asymptoticAbscissaLaw_iff_encard_rightOf_le_one :
    _root_.RHTower.AsymptoticAbscissaLaw ↔
      ∀ h : ℝ, 0 ≤ h → (rightOf zetaZeroConfig h).encard ≤ 1 ∨
        (rightOf zetaZeroConfig h).Infinite := by
  rw [← ZetaAbscissa.zetaZeroConfig_abscissaLaw_iff]
  constructor
  · intro hlaw h hh
    by_cases hfin : (rightOf zetaZeroConfig h).Finite
    · left
      have hempty : rightOf zetaZeroConfig h = ∅ := by
        ext ρ
        simp only [mem_empty_iff_false, iff_false]
        rintro ⟨hρ, hgt⟩
        exact (not_lt.mpr (hlaw h hh hfin ρ hρ)) hgt
      rw [hempty, Set.encard_empty]
      exact zero_le_one
    · exact Or.inr hfin
  · intro hgap h hh hfin ρ hρ
    rcases hgap h hh with hle | hinf
    · by_contra hgt
      have hmem : ρ ∈ rightOf zetaZeroConfig h := ⟨hρ, lt_of_not_ge hgt⟩
      rw [rightOf_zeta_eq_empty_of_encard_le_one hle] at hmem
      exact hmem
    · exact absurd hfin hinf

/-- **One line with at most one zero to its right.** If the abscissa law fails, every line
between the top layer and the rest has at least two zeros to its right; so a single such line
with at most one decides the top layer. Stated contrapositively at each depth: a finite set of
zeros right of `½ + h` with at most one element is empty. -/
theorem forall_re_le_of_encard_rightOf_le_one {h : ℝ}
    (hle : (rightOf zetaZeroConfig h).encard ≤ 1) :
    ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + h := by
  intro ρ hρ
  by_contra hgt
  have hmem : ρ ∈ rightOf zetaZeroConfig h := ⟨hρ, lt_of_not_ge hgt⟩
  rw [rightOf_zeta_eq_empty_of_encard_le_one hle] at hmem
  exact hmem

end GaloisForLFunctions.FloorFreeArithmetic
