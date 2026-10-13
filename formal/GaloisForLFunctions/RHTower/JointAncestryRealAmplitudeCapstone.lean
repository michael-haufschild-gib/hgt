import GaloisForLFunctions.RHTower.JointAncestryRealAmplitudeDetection
import GaloisForLFunctions.RHTower.JointAncestryDiagonalBochnerLevel
import GaloisForLFunctions.RHTower.XiSliceEventualPositivityFiniteOffLine

/-!
# Real-amplitude JAS positivity and the zeros approaching the line

`JasRealPositiveAbove X σ` asks for `Re Σ_ρ K_{P,t}(ρ)/(ρ(1−ρ)) ≥ 0` for every finite set `P` of
primes `p > X` and every `t ∈ [0, 1]`, with the real kernel
`K_{P,t}(s) = ∏_{p ∈ P} (1 + t p^{−σ} cosh((s − ½) log p))`.

* Real test vectors are product tests: the Bernoulli factor at a real `x` is
  `(1 + x²)(1 + t p^{−σ} cosh((ρ − ½) log p))` with `t = 2x/(1 + x²)`
  (`jasBernoulliFactor_ofReal`).  So product positivity gives real positivity, and RH gives
  real positivity at level one.
* If the zeros approach the critical line (only finitely many copies at distance `> h` for every
  `h > 0`), an off-line zero forces a zero at maximal distance.  The detection theorem
  `not_jasRealPositiveAbove_of_maximal_offLine` then excludes it.

**Capstone** (`riemannHypothesis_iff_zerosApproachLine_and_jasRealPositiveAbove`):
RH holds iff the zeros approach the line and some `X` gives real-amplitude positivity at level one.
At a level `σ ≥ 1`, the same two hypotheses give `|Re ρ − ½| ≤ σ − 1`
(`abs_re_sub_half_le_of_zerosApproachLine_of_jasRealPositiveAbove`).
-/

open Complex Filter
open scoped ComplexConjugate Topology BigOperators

namespace RHTower

noncomputable section

open RHTower.BacklundConverse RHTower.CosineDefectBudget RHTower.LindelofSparse

/-- The Bernoulli factor at a real test value `x` is `(1 + x²)` times the real-amplitude factor
with `t = 2x/(1 + x²)`. -/
theorem jasBernoulliFactor_ofReal (s : ℂ) (c x : ℝ) (p : Nat.Primes) :
    jasBernoulliFactor (jasHoloA (s + c) p) (jasHoloB (s - c) p) (x : ℂ) =
      ((1 + x ^ 2 : ℝ) : ℂ) * jasRealFactor (1 / 2 + c) (2 * x / (1 + x ^ 2)) p s := by
  have hx : (1 + x ^ 2 : ℝ) ≠ 0 := by positivity
  have e := jasRealFactor_sub_one (1 / 2 + c) (2 * x / (1 + x ^ 2)) p s
  have hA : cexp (-(((1 / 2 + c : ℝ) : ℂ) + (s - 1 / 2)) * (Real.log p : ℂ)) =
      jasHoloA (s + c) p := by rw [jasHoloA]; congr 1; push_cast; ring
  have hB : cexp (-(((1 / 2 + c : ℝ) : ℂ) - (s - 1 / 2)) * (Real.log p : ℂ)) =
      jasHoloB (s - c) p := by rw [jasHoloB]; congr 1; push_cast; ring
  rw [hA, hB, sub_eq_iff_eq_add'] at e
  rw [e, jasBernoulliFactor, Complex.conj_ofReal]
  have hxc : (1 + (x : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hx
  push_cast
  field_simp
  ring

/-- **Product positivity gives real-amplitude positivity.** -/
theorem JasProductPositiveAbove.realPositive {X : ℕ} {σ : ℝ} (h : JasProductPositiveAbove X σ) :
    JasRealPositiveAbove X σ := by
  intro P hP t ht0 ht1
  obtain ⟨x, hx0, hx1, hxt⟩ := exists_div_one_add_sq_eq (s := t / 2) (by linarith) (by linarith)
  have ht : t = 2 * x / (1 + x ^ 2) := by
    have : (0 : ℝ) < 1 + x ^ 2 := by positivity
    field_simp at hxt ⊢
    linarith
  have hpos := h P hP (fun _ => (x : ℂ))
  have e : ∀ q : XiZeroCopy, (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
      (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (x : ℂ)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
      (((1 + x ^ 2) ^ P.card : ℝ) : ℂ) *
        (jasRealKernel P σ t (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
    intro q
    rw [Finset.prod_congr rfl fun p _ => jasBernoulliFactor_ofReal (q.1 : ℂ) (σ - 1 / 2) x p,
      Finset.prod_mul_distrib, Finset.prod_const, jasRealKernel, ht,
      show (1 / 2 + (σ - 1 / 2) : ℝ) = σ by ring]
    push_cast
    ring
  simp_rw [e] at hpos
  rw [tsum_mul_left, Complex.re_ofReal_mul] at hpos
  have hc : (0 : ℝ) < (1 + x ^ 2) ^ P.card := by positivity
  exact (mul_nonneg_iff_of_pos_left hc).mp hpos

/-- **RH gives real-amplitude positivity at level one.** -/
theorem exists_jasRealPositiveAbove_one_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ X : ℕ, JasRealPositiveAbove X 1 := by
  obtain ⟨X, h⟩ := riemannHypothesis_iff_exists_jasProductPositiveAbove_one.mp hRH
  exact ⟨X, h.realPositive⟩

/-- **Zeros approaching the line attain their largest distance.**  If the zeros approach the
critical line and some zero lies off it, then some zero off the line has the largest distance
`|Re ρ − ½|` among all zeros. -/
theorem exists_maximal_offLine_of_zerosApproachLine (hZ : ZerosApproachLine) {q : XiZeroCopy}
    (hq : (q.1 : ℂ).re ≠ 1 / 2) :
    ∃ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 ∧
      ∀ q' : XiZeroCopy, |(q'.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2| := by
  classical
  set d := |(q.1 : ℂ).re - 1 / 2| with hd
  have hd0 : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hq)
  have hdeep := hZ (d / 2) (by positivity)
  set S : Set XiZeroCopy := {q' | d ≤ |(q'.1 : ℂ).re - 1 / 2|} with hS
  have hSfin : S.Finite := by
    refine (hdeep.union (hdeep.preimage (xiZeroCopyReflectEquiv.injective.injOn))).subset ?_
    intro q' hq'
    simp only [hS, Set.mem_setOf_eq] at hq'
    rcases le_or_gt ((q'.1 : ℂ).re) (1 / 2) with hle | hgt
    · left
      show d / 2 < (xiSpectralPoint q').im
      rw [spectral_im_eq]
      rw [abs_of_nonpos (by linarith)] at hq'
      linarith
    · right
      show d / 2 < (xiSpectralPoint (xiZeroCopyReflectEquiv q')).im
      rw [spectral_im_eq, xiZeroCopyReflectEquiv_val, Complex.sub_re, Complex.one_re]
      rw [abs_of_pos (by linarith)] at hq'
      linarith
  obtain ⟨q₀, hq₀S, hq₀⟩ := hSfin.toFinset.exists_max_image (fun q' => |(q'.1 : ℂ).re - 1 / 2|)
    ⟨q, (Set.Finite.mem_toFinset hSfin).mpr (show d ≤ _ from le_rfl)⟩
  have hq₀d : d ≤ |(q₀.1 : ℂ).re - 1 / 2| := by
    have := (Set.Finite.mem_toFinset hSfin).mp hq₀S; simpa [hS] using this
  refine ⟨q₀, fun h => by rw [h, sub_self, abs_zero] at hq₀d; linarith, fun q' => ?_⟩
  by_cases hq' : d ≤ |(q'.1 : ℂ).re - 1 / 2|
  · exact hq₀ q' ((Set.Finite.mem_toFinset hSfin).mpr hq')
  · linarith [not_le.mp hq']

/-- **The real-amplitude abscissa under approach to the line.**  If the zeros approach the line and
real-amplitude positivity holds at a level `σ ≥ 1`, every zero satisfies `|Re ρ − ½| ≤ σ − 1`. -/
theorem abs_re_sub_half_le_of_zerosApproachLine_of_jasRealPositiveAbove
    (hZ : ZerosApproachLine) {X : ℕ} {σ : ℝ} (hσ : 1 ≤ σ) (hpos : JasRealPositiveAbove X σ)
    (q : XiZeroCopy) : |(q.1 : ℂ).re - 1 / 2| ≤ σ - 1 := by
  by_contra hlt
  push Not at hlt
  have hq : (q.1 : ℂ).re ≠ 1 / 2 := fun h => by
    rw [h, sub_self, abs_zero] at hlt; linarith
  obtain ⟨q₀, hq₀, hmax⟩ := exists_maximal_offLine_of_zerosApproachLine hZ hq
  have hδ : |(q₀.1 : ℂ).re - 1 / 2| < 1 / 2 := by
    rw [abs_lt]; constructor <;> linarith [xiZeroCopy_re_pos q₀, xiZeroCopy_re_lt_one q₀]
  exact not_jasRealPositiveAbove_of_maximal_offLine q₀ hq₀ hmax (by linarith)
    (by linarith [hmax q]) X hpos

/-- **Capstone.**  RH holds iff the zeros approach the critical line and real-amplitude JAS
positivity holds at level one above some `X`. -/
theorem riemannHypothesis_iff_zerosApproachLine_and_jasRealPositiveAbove :
    RiemannHypothesis ↔ ZerosApproachLine ∧ ∃ X : ℕ, JasRealPositiveAbove X 1 := by
  constructor
  · intro hRH
    refine ⟨fun h hh => ?_, exists_jasRealPositiveAbove_one_of_riemannHypothesis hRH⟩
    refine Set.Finite.subset (Set.finite_empty) fun q hq => ?_
    have := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
    change h < (xiSpectralPoint q).im at hq
    rw [spectral_im_eq, this, sub_self] at hq
    exact absurd hq (not_lt.mpr hh.le)
  · rintro ⟨hZ, X, hpos⟩
    intro s hζ htriv h1
    have hxi : xi s = 0 := xi_eq_zero_of_zeta_eq_zero hζ (fun ⟨n, hn⟩ => htriv ⟨n, hn⟩) h1
    obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hxi
    have := abs_re_sub_half_le_of_zerosApproachLine_of_jasRealPositiveAbove hZ le_rfl hpos q
    rw [sub_self, abs_nonpos_iff, sub_eq_zero] at this
    rw [← hq]
    exact this

/-- **Capstone, finite form.**  RH holds iff only finitely many zeros lie off the critical line and
real-amplitude JAS positivity holds at level one above some `X`. -/
theorem riemannHypothesis_iff_finiteOffLine_and_jasRealPositiveAbove :
    RiemannHypothesis ↔ FiniteOffLine ∧ ∃ X : ℕ, JasRealPositiveAbove X 1 := by
  constructor
  · intro hRH
    refine ⟨Set.Finite.subset Set.finite_empty fun q hq => ?_,
      exists_jasRealPositiveAbove_one_of_riemannHypothesis hRH⟩
    have := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q
    change (xiSpectralPoint q).im ≠ 0 at hq
    rw [spectral_im_eq, this, sub_self] at hq
    exact absurd rfl hq
  · rintro ⟨hF, hX⟩
    exact riemannHypothesis_iff_zerosApproachLine_and_jasRealPositiveAbove.mpr
      ⟨zerosApproachLine_of_finiteOffLine hF, hX⟩

end

end RHTower
