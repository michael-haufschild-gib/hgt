import GaloisForLFunctions.JointMarkedMoments.Arithmetic.InjectiveMarks
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.Stage1B0StrippedAndTinyCubeBins
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.RawNestingAndRadialExchange
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.CentralRepeatedProducts
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.QuasiRiemannHypothesis
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.SubFarkasDetectorRowCounts

/-!
# Stage-1 dual row moments and `Q = {0}` column energy

This module establishes the Stage-1 dual-row moment bounds on `(17/25, 19/26)` via `4 × 3 = 12`
sextic label transfer (`varyingReopenedRow_sextic_label_transfer`) at `Q = {0}`:

1. **Stage-1 slot-supply and large-`z_J` capacity certificates:**
   Across `r ∈ [17/25, 19/26]`, `ν ∈ [11/25, 3/4]`, `x ∈ [0, 1/2]`, and Pass-1 priority-slot hit
   width `0 ≤ z_J ≤ (25/3) (stage1Line r - (1 - r)/2)`, `stage1RemWidth r - z_J` exceeds both the
   inverse and plain witness slot requirements by at least `1/1000` (`stage1_slot_supply_with_zJ`).
   Conversely, whenever `z_J ≥ (25/3) max 0 (stage1Line r - (1 - r)/2) + 20 η` and
   `B_t ≥ z_J - 2 η`, the surviving unmarked/marked widths satisfy Stage-0 capacity at dual scale
   `stage1DualScale r` (`stage1_large_zJ_capacity`).
2. **Exact algebraic identities on `inputConjugateRow` at `Q = {0}`:**
   Absorbs `c₀^4 * d₀` into the dual frequency `w = gcdElement p C₀ D₀ * z` via sextic unit
   periodicity (`4 ≡ -2`, `5 ≡ -1 (mod 6)`), restores `residualLists` to `lists` at `x.cube = 0`,
   bounds the divisor fibers of `(C₀, D₀, z) ↦ w` and `(tup, z) ↦ d(tup)^4 * z` (via
   `JointMarkedMoments.prod_primes_injective`), and strips finite puncture prime sets without
   conductor growth via finite geometric-series Möbius unpuncturing.
3. **Dual sixth-power decomposition and three-regime moment bound:**
   Applies `ProbePhysical.sixthFrequencyEquiv` (`w = u_free * g(J₆)^6`) and partitions `u_free`
   across small/unsupported rows (`no_slot_endpoint`), moderate detector-maximum rows
   (`deleted_source_energy` + `ray_amplitude_bins`), and critical detector-maximum rows
   (`actual_supported_witness_family` + `stage1_large_value_certificate` +
   `HeckeZeroSupremum.beta ≤ 7/8`).
-/

noncomputable section

open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Classical Topology ContDiff SchwartzMap FourierTransform ComplexConjugate

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

namespace Stage1DualRowMoments

open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
open FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialRayAttachment InverseFirstRayAttachment InverseMoment
open InverseSecondPrincipalCaller InverseFirstPriorityParents InverseFirstGlobalCaps
open CanonicalCoefficientClass IdealDivisorBound Stage1CubeBins
open GaloisForLFunctions.FamilyContinuationTheory
open GaloisForLFunctions.FamilyContinuationTheory.Budget

local notation "O" => Eisenstein.O

/-! ### Part I: Stage-1 `z_J` slot-supply and large-`z_J` capacity certificates -/

/-- Across all `r ∈ [17/25, 19/26]`, `ν ∈ [11/25, 3/4]`, `x ∈ [0, 1/2]`, and priority-slot hit
width `z_J ≤ (25/3) (stage1Line r - (1 - r)/2)`, the surviving marked width `stage1RemWidth r - z_J`
exceeds both the inverse witness width and the plain witness width at `stage1DualScale r` by at
least `1/1000`. -/
theorem stage1_slot_supply_with_zJ {r ν x z_J : ℝ}
    (hr0 : 17 / 25 ≤ r) (hr1 : r ≤ 19 / 26)
    (hν0 : 11 / 25 ≤ ν) (hν1 : ν ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hzJ : z_J ≤ (25 / 3) * (stage1Line r - (1 - r) / 2)) :
    stage1DualScale r * (1 - stage1Crossing ν x) / 2 + 1 / 1000 ≤ stage1RemWidth r - z_J ∧
      stage1DualScale r *
          (1 - 2 * ((1 + ν * rowP x / (2 * rowJ ν x)) - stage1Crossing ν x)) * (2 / 9) +
          1 / 1000 ≤
        stage1RemWidth r - z_J := by
  have hD : 7 / 9 ≤ rowD x := by unfold rowD; linarith
  have hD0 : 0 < rowD x := by linarith
  have hJ := rowJ_pos (δ := ν) (x := x) (by linarith) (by linarith) hx1
  have hJ0 : 0 < rowJ ν x := by linarith
  set u := (ν - 11 / 25) / (3 / 4 - 11 / 25)
  set v := x / (1 / 2)
  have hu0 : 0 ≤ u := div_nonneg (by linarith) (by norm_num)
  have hu1 : u ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 3 / 4 - 11 / 25)).mpr (by linarith)
  have hv0 : 0 ≤ v := div_nonneg hx0 (by norm_num)
  have hv1 : v ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 2)).mpr (by linarith)
  set θ := (r - 17 / 25) / (19 / 26 - 17 / 25)
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith) (by norm_num)
  have hθ1 : 0 ≤ 1 - θ := by
    have : θ ≤ 1 := (div_le_iff₀ (by norm_num : (0 : ℝ) < 19 / 26 - 17 / 25)).mpr (by linarith)
    linarith
  have h_hi := stage1_slot_supply_certificate (r := 19 / 26) (by norm_num) le_rfl hν0 hν1 hx0 hx1
  have hdz19 : stage1Line (19 / 26) - (1 - 19 / 26) / 2 = 0 := by unfold stage1Line; norm_num
  constructor
  · let G : ℝ → ℝ := fun rc =>
      (stage1RemWidth rc - (25 / 3) * (stage1Line rc - (1 - rc) / 2) - 1 / 1000 -
        stage1DualScale rc * (1 - stage1Crossing ν x) / 2) * (2 * rowD x * rowJ ν x)
    have hG_lo : 0 ≤ G (17 / 25) := by
      have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
        (c00 := 12371 / 25000) (c01 := 13339387 / 50625000)
        (c02 := 207848947 / 1822500000) (c03 := 13664803 / 607500000)
        (c10 := 81197 / 100000) (c11 := 100188349 / 202500000)
        (c12 := 2077290469 / 7290000000) (c13 := 364724281 / 2430000000)
        (c20 := 11291 / 10000) (c21 := 2940383 / 4050000)
        (c22 := 66463703 / 145800000) (c23 := 13495787 / 48600000)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have hid : G (17 / 25) = bernstein23 u v
          (12371 / 25000) (13339387 / 50625000)
          (207848947 / 1822500000) (13664803 / 607500000)
          (81197 / 100000) (100188349 / 202500000)
          (2077290469 / 7290000000) (364724281 / 2430000000)
          (11291 / 10000) (2940383 / 4050000)
          (66463703 / 145800000) (13495787 / 48600000) := by
        dsimp [G, u, v]
        unfold stage1RemWidth stage1DualScale stage1Width stage1Line stage1Crossing
        field_simp [hD0.ne', hJ0.ne']
        unfold bernstein23 rowJ rowD rowP
        ring
      linarith
    have hG_hi : 0 ≤ G (19 / 26) := by
      dsimp [G]
      rw [hdz19, mul_zero, sub_zero]
      exact mul_nonneg (by linarith [h_hi.1]) (mul_nonneg (by linarith) hJ0.le)
    have haff : G r = (1 - θ) * G (17 / 25) + θ * G (19 / 26) := by
      dsimp [G, θ]; unfold stage1RemWidth stage1DualScale stage1Width stage1Line; ring
    have hGr : 0 ≤ G r := by rw [haff]; exact add_nonneg (mul_nonneg hθ1 hG_lo) (mul_nonneg hθ0 hG_hi)
    have hDJ : 0 < 2 * rowD x * rowJ ν x := mul_pos (by linarith) hJ0
    have hG0 : 0 ≤ stage1RemWidth r - (25 / 3) * (stage1Line r - (1 - r) / 2) - 1 / 1000 -
        stage1DualScale r * (1 - stage1Crossing ν x) / 2 := by
      dsimp [G] at hGr; nlinarith
    linarith
  · let P : ℝ → ℝ := fun rc =>
      (stage1RemWidth rc - (25 / 3) * (stage1Line rc - (1 - rc) / 2) - 1 / 1000 -
        stage1DualScale rc *
          (1 - 2 * ((1 + ν * rowP x / (2 * rowJ ν x)) - stage1Crossing ν x)) * (2 / 9)) *
        (2 * rowD x * rowJ ν x)
    have hP_lo : 0 ≤ P (17 / 25) := by
      have hpos := bernstein23_nonneg hu0 hu1 hv0 hv1
        (c00 := 1251361 / 1125000) (c01 := 92967727 / 113906250)
        (c02 := 365673809 / 607500000) (c03 := 270691223 / 607500000)
        (c10 := 5337547 / 4500000) (c11 := 756014933 / 911250000)
        (c12 := 1410801143 / 2430000000) (c13 := 987686621 / 2430000000)
        (c20 := 113393 / 90000) (c21 := 15365761 / 18225000)
        (c22 := 27178141 / 48600000) (c23 := 17852167 / 48600000)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      have hid : P (17 / 25) = bernstein23 u v
          (1251361 / 1125000) (92967727 / 113906250)
          (365673809 / 607500000) (270691223 / 607500000)
          (5337547 / 4500000) (756014933 / 911250000)
          (1410801143 / 2430000000) (987686621 / 2430000000)
          (113393 / 90000) (15365761 / 18225000)
          (27178141 / 48600000) (17852167 / 48600000) := by
        dsimp [P, u, v]
        unfold stage1RemWidth stage1DualScale stage1Width stage1Line stage1Crossing
        field_simp [hD0.ne', hJ0.ne']
        unfold bernstein23 rowJ rowD rowP
        ring
      linarith
    have hP_hi : 0 ≤ P (19 / 26) := by
      dsimp [P]
      rw [hdz19, mul_zero, sub_zero]
      exact mul_nonneg (by linarith [h_hi.2]) (mul_nonneg (by linarith) hJ0.le)
    have haff : P r = (1 - θ) * P (17 / 25) + θ * P (19 / 26) := by
      dsimp [P, θ]; unfold stage1RemWidth stage1DualScale stage1Width stage1Line; ring
    have hPr : 0 ≤ P r := by rw [haff]; exact add_nonneg (mul_nonneg hθ1 hP_lo) (mul_nonneg hθ0 hP_hi)
    have hDJ : 0 < 2 * rowD x * rowJ ν x := mul_pos (by linarith) hJ0
    have hP0 : 0 ≤ stage1RemWidth r - (25 / 3) * (stage1Line r - (1 - r) / 2) - 1 / 1000 -
        stage1DualScale r *
          (1 - 2 * ((1 + ν * rowP x / (2 * rowJ ν x)) - stage1Crossing ν x)) * (2 / 9) := by
      dsimp [P] at hPr; nlinarith
    linarith

/-- Whenever `z_J ≥ (25/3) (stage1Line r - (1 - r)/2) + 20 η` and `B_t ≥ z_J - 2 η`, the surviving
dual unmarked/marked exponents satisfy Stage-0 capacity at scale `stage1DualScale r` with `30 η`
margin. -/
theorem stage1_large_zJ_capacity {r z_rem u₀ B_t z_J η : ℝ}
    (_hr0 : 17 / 25 ≤ r) (hr1 : r ≤ 19 / 26)
    (hz : z_rem ≤ stage1Line r + 2 * η) (hu : stage1Width r - η ≤ u₀)
    (hBt : z_J - 2 * η ≤ B_t) (hη : 0 ≤ η) (_hηs : η ≤ 1 / 2000)
    (hzJ : (25 / 3) * (stage1Line r - (1 - r) / 2) + 20 * η ≤ z_J)
    (_hz_pos : 0 ≤ z_rem - u₀ - z_J) :
    (r - (B_t - z_J)) + 2 * (z_rem - u₀ - z_J) ≤ stage1DualScale r - 30 * η ∧
      2 * (r - (B_t - z_J)) + 8 * (z_rem - u₀ - z_J) ≤ 3 * stage1DualScale r - 1 / 10 := by
  have hdz0 : 0 ≤ stage1Line r - (1 - r) / 2 := by unfold stage1Line; linarith
  unfold stage1DualScale stage1Width stage1Line at *
  constructor
  · linarith
  · linarith

/-! ### Part II: Algebraic dual-row identities on `inputConjugateRow` at `Q = {0}` -/

section DualRowAlgebra

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- At `z = 0`, `primeSubsetRow p χ S 0` vanishes for every nonempty `S` and equals `1` at `∅`. -/
lemma primeSubsetRow_zero_eq_ite
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S : Finset ι) :
    primeSubsetRow p χ S 0 = if S = ∅ then 1 else 0 := by
  by_cases hS : S = ∅
  · subst hS; simp [primeSubsetRow]
  · rw [if_neg hS]
    obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    letI : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field (Ideal.span {p i})
    unfold primeSubsetRow
    apply Finset.prod_eq_zero hi
    rw [map_zero]
    exact MulChar.map_nonunit (χ i) not_isUnit_zero

/-- At `z = 0`, `inputConjugateRow` collapses to its `S = ∅` term `H ∅`. -/
lemma inputConjugateRow_at_zero (pool : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) :
    inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
        pool Ψ m c d H 0 = H ∅ := by
  unfold inputConjugateRow supportConjugateSum
  rw [Finset.sum_eq_single ∅]
  · simp [secondInputCoefficient, supportMobius, primeCoprimeMask, primeSubsetRow]
  · intro S _ hne
    rw [primeSubsetRow_zero_eq_ite, if_neg hne, star_zero, mul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.empty_mem_powerset pool))

/-- Conjugated sextic cofactor `(∏ i ∈ C₀ \ D₀, p i)^2 * (∏ i ∈ D₀, p i)` absorbing `c₀^4 * d₀` into
the dual frequency argument. -/
def gcdElement (C₀ D₀ : Finset ι) : O :=
  (∏ i ∈ C₀ \ D₀, p i) ^ 2 * ∏ i ∈ D₀, p i

include hp in
omit [∀ i, (Ideal.span {p i}).IsMaximal] in
lemma gcdElement_ne_zero (C₀ D₀ : Finset ι) : gcdElement p C₀ D₀ ≠ 0 := by
  unfold gcdElement
  exact mul_ne_zero (pow_ne_zero 2 (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))

omit [∀ i, (Ideal.span {p i}).IsMaximal] in
lemma gcdElement_norm_sq {C₀ D₀ : Finset ι} (hDC : D₀ ⊆ C₀) :
    ‖ringComplex (gcdElement p C₀ D₀)‖ ^ 2 * primeProductNorm p D₀ =
      (primeProductNorm p C₀) ^ 2 := by
  have h1 : ‖ringComplex (∏ i ∈ C₀ \ D₀, p i)‖ ^ 2 = primeProductNorm p (C₀ \ D₀) := by
    unfold primeProductNorm; rw [map_prod, norm_prod, ← Finset.prod_pow]
  have h2 : ‖ringComplex (∏ i ∈ D₀, p i)‖ ^ 2 = primeProductNorm p D₀ := by
    unfold primeProductNorm; rw [map_prod, norm_prod, ← Finset.prod_pow]
  have hunion : (C₀ \ D₀) ∪ D₀ = C₀ := Finset.sdiff_union_of_subset hDC
  have hdisj : Disjoint (C₀ \ D₀) D₀ := Finset.sdiff_disjoint
  have hprod : primeProductNorm p (C₀ \ D₀) * primeProductNorm p D₀ = primeProductNorm p C₀ := by
    rw [← primeProductNorm_union p (C₀ \ D₀) D₀ hdisj, hunion]
  unfold gcdElement
  rw [map_mul, map_pow, norm_mul, norm_pow, mul_pow, ← pow_mul,
    show 2 * 2 = 2 * 2 from rfl, pow_mul, h1, h2]
  calc
    primeProductNorm p (C₀ \ D₀) ^ 2 * primeProductNorm p D₀ * primeProductNorm p D₀
      = (primeProductNorm p (C₀ \ D₀) * primeProductNorm p D₀) ^ 2 := by ring
    _ = primeProductNorm p C₀ ^ 2 := by rw [hprod]

omit [DecidableEq ι] in
/-- On any unit modulo `p i`, `χ_i(u)^4 = star (χ_i(u)^2)` and `χ_i(u)^5 = star (χ_i(u))`. -/
lemma complexSexticChar_pow_four_five_eq_star (i : ι) {u : O} (hu : ¬ (p i ∣ u)) :
    let χ := complexSexticChar (Ideal.span {p i}) (hg i)
    let x := Ideal.Quotient.mk (Ideal.span {p i}) u
    χ x ^ 4 = star (χ x ^ 2) ∧ χ x ^ 5 = star (χ x) := by
  intro χ x
  have h6 : χ x ^ 6 = 1 := complexSexticChar_pow_six_of_not_dvd p hg i hu
  have hnorm1 : ‖χ x‖ = 1 := by
    have hpow : ‖χ x‖ ^ 6 = 1 := by rw [← norm_pow, h6, norm_one]
    have h0 : 0 ≤ ‖χ x‖ := norm_nonneg _
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : ‖χ x‖ ^ 6 < 1 ^ 6 := pow_lt_pow_left₀ hlt h0 (by decide)
      norm_num at this; linarith
    · have : 1 ^ 6 < ‖χ x‖ ^ 6 := pow_lt_pow_left₀ hgt zero_le_one (by decide)
      norm_num at this; linarith
  have hconj : star (χ x) * χ x = 1 := by
    calc star (χ x) * χ x = (Complex.normSq (χ x) : ℂ) := by
          rw [Complex.normSq_eq_conj_mul_self]; rfl
      _ = ((‖χ x‖ ^ 2 : ℝ) : ℂ) := by rw [Complex.normSq_eq_norm_sq]
      _ = 1 := by rw [hnorm1]; norm_num
  constructor
  · have hmul : χ x ^ 4 * χ x ^ 2 = 1 := by rw [← pow_add]; exact h6
    have hst : star (χ x ^ 2) * χ x ^ 2 = 1 := by
      rw [star_pow, ← mul_pow, hconj, one_pow]
    exact mul_right_cancel₀ (fun hz => by rw [hz, mul_zero] at hmul; exact one_ne_zero hmul.symm)
      (hmul.trans hst.symm)
  · have hmul : χ x ^ 5 * χ x = 1 := by rw [← pow_succ]; exact h6
    exact mul_right_cancel₀ (fun hz => by rw [hz, mul_zero] at hmul; exact one_ne_zero hmul.symm)
      (hmul.trans hconj.symm)

include hcop in
/-- Exact `c₀^4 * d₀` absorption: for `D₀ ⊆ C₀`, `c₀ = ∏ i ∈ C₀, p i`, and `d₀ = ∏ i ∈ D₀, p i`,
every subset `S` satisfies `primeSubsetRow S c₀ ^ 4 * primeSubsetRow S d₀ * star (primeSubsetRow S z)
= star (primeSubsetRow S (gcdElement p C₀ D₀ * z))` identically! -/
theorem primeSubsetRow_absorb_cd {C₀ D₀ : Finset ι} (hDC : D₀ ⊆ C₀) (S : Finset ι) (z : O) :
    let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
    primeSubsetRow p χ S (∏ i ∈ C₀, p i) ^ 4 *
        primeSubsetRow p χ S (∏ i ∈ D₀, p i) *
        star (primeSubsetRow p χ S z) =
      star (primeSubsetRow p χ S (gcdElement p C₀ D₀ * z)) := by
  intro χ
  by_cases hd : Disjoint S C₀
  · have hunion : (C₀ \ D₀) ∪ D₀ = C₀ := Finset.sdiff_union_of_subset hDC
    have hdisjCD : Disjoint (C₀ \ D₀) D₀ := Finset.sdiff_disjoint
    have hc_split : (∏ i ∈ C₀, p i) = (∏ i ∈ C₀ \ D₀, p i) * (∏ i ∈ D₀, p i) := by
      conv_lhs => rw [← hunion, Finset.prod_union hdisjCD]
    unfold primeSubsetRow
    rw [← Finset.prod_pow, star_prod, star_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    unfold gcdElement
    apply Finset.prod_congr rfl
    intro i hiS
    have hiC : i ∉ C₀ := Finset.disjoint_left.mp hd hiS
    have hiCD : i ∉ C₀ \ D₀ := fun h => hiC (Finset.sdiff_subset h)
    have hiD : i ∉ D₀ := fun h => hiC (hDC h)
    have hnd1 : ¬ (p i ∣ ∏ j ∈ C₀ \ D₀, p j) := not_dvd_prod_of_not_mem p hcop hiCD
    have hnd2 : ¬ (p i ∣ ∏ j ∈ D₀, p j) := not_dvd_prod_of_not_mem p hcop hiD
    have h4 := (complexSexticChar_pow_four_five_eq_star p hg i hnd1).1
    have h5 := (complexSexticChar_pow_four_five_eq_star p hg i hnd2).2
    rw [hc_split]
    simp only [map_mul, map_pow, star_mul]
    calc
      (χ i (Ideal.Quotient.mk (Ideal.span {p i}) (∏ j ∈ C₀ \ D₀, p j)) *
          χ i (Ideal.Quotient.mk (Ideal.span {p i}) (∏ j ∈ D₀, p j))) ^ 4 *
        χ i (Ideal.Quotient.mk (Ideal.span {p i}) (∏ j ∈ D₀, p j)) *
        star (χ i (Ideal.Quotient.mk (Ideal.span {p i}) z))
      = χ i (Ideal.Quotient.mk (Ideal.span {p i}) (∏ j ∈ C₀ \ D₀, p j)) ^ 4 *
          χ i (Ideal.Quotient.mk (Ideal.span {p i}) (∏ j ∈ D₀, p j)) ^ 5 *
          star (χ i (Ideal.Quotient.mk (Ideal.span {p i}) z)) := by ring
      _ = star (χ i (Ideal.Quotient.mk (Ideal.span {p i}) (∏ j ∈ C₀ \ D₀, p j)) ^ 2) *
          star (χ i (Ideal.Quotient.mk (Ideal.span {p i}) (∏ j ∈ D₀, p j))) *
          star (χ i (Ideal.Quotient.mk (Ideal.span {p i}) z)) := by rw [h4, h5]
      _ = _ := by simp only [star_pow]; ring
  · obtain ⟨i, hiS, hiC⟩ := Finset.not_disjoint_iff.mp hd
    letI : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field (Ideal.span {p i})
    have hdvd_c : p i ∣ ∏ j ∈ C₀, p j := Finset.dvd_prod_of_mem p hiC
    have hdvd_g : p i ∣ gcdElement p C₀ D₀ * z := by
      unfold gcdElement
      by_cases hiD : i ∈ D₀
      · exact (Finset.dvd_prod_of_mem p hiD).trans ⟨(∏ j ∈ C₀ \ D₀, p j) ^ 2 * z, by ring⟩
      · have hiCD : i ∈ C₀ \ D₀ := Finset.mem_sdiff.mpr ⟨hiC, hiD⟩
        exact (Finset.dvd_prod_of_mem p hiCD).trans
          ⟨(∏ j ∈ C₀ \ D₀, p j) * (∏ j ∈ D₀, p j) * z, by ring⟩
    have hz1 : primeSubsetRow p χ S (∏ j ∈ C₀, p j) = 0 := by
      unfold primeSubsetRow
      apply Finset.prod_eq_zero hiS
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdvd_c)]
      exact MulChar.map_nonunit (χ i) not_isUnit_zero
    have hz2 : primeSubsetRow p χ S (gcdElement p C₀ D₀ * z) = 0 := by
      unfold primeSubsetRow
      apply Finset.prod_eq_zero hiS
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdvd_g)]
      exact MulChar.map_nonunit (χ i) not_isUnit_zero
    rw [hz1, zero_pow (by decide), zero_mul, zero_mul, hz2, star_zero]

include hcop in
/-- `inputConjugateRow` at `(∏ i ∈ C₀, p i, ∏ i ∈ D₀, p i, z)` equals `inputConjugateRow` at
`(1, 1, gcdElement p C₀ D₀ * z)`. -/
theorem inputConjugateRow_absorb_cd (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    {C₀ D₀ : Finset ι} (hDC : D₀ ⊆ C₀) (H : Finset ι → ℂ) (z : O) :
    inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
        pool Ψ m (∏ i ∈ C₀, p i) (∏ i ∈ D₀, p i) H z =
      inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
        pool Ψ m 1 1 H (gcdElement p C₀ D₀ * z) := by
  unfold inputConjugateRow supportConjugateSum secondInputCoefficient
  apply Finset.sum_congr rfl
  intro S _
  have habs := primeSubsetRow_absorb_cd p hcop hg hDC S z
  have h1 : primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S 1 = 1 := by
    simp [primeSubsetRow]
  rw [h1, one_pow, mul_one, mul_one]
  calc
    supportMobius S *
        (Ψ (∏ i ∈ S, p i) * primeCoprimeMask p S m *
          primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S (∏ i ∈ C₀, p i) ^ 4 *
          primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S (∏ i ∈ D₀, p i) * H S) *
        star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S z)
      = supportMobius S * (Ψ (∏ i ∈ S, p i) * primeCoprimeMask p S m * H S) *
          (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S (∏ i ∈ C₀, p i) ^ 4 *
            primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S (∏ i ∈ D₀, p i) *
            star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S z)) := by ring
    _ = supportMobius S * (Ψ (∏ i ∈ S, p i) * primeCoprimeMask p S m * H S) *
          star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S
            (gcdElement p C₀ D₀ * z)) := by rw [habs]

include hp hcop in
/-- Injectivity of `U ↦ ∏ j ∈ U, Ideal.span {p j}` via `JointMarkedMoments.prod_primes_injective`. -/
lemma span_finset_prod_injective :
    Function.Injective (fun U : Finset ι => ∏ j ∈ U, (Ideal.span {p j} : Ideal O)) := by
  have hprime_ideal : ∀ j : ι, Prime (Ideal.span {p j} : Ideal O) := fun j =>
    Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr (hp j)) inferInstance
  have hinj_span : Function.Injective (fun j : ι => (Ideal.span {p j} : Ideal O)) := by
    intro j₁ j₂ (heq : Ideal.span {p j₁} = Ideal.span {p j₂})
    by_contra hij
    have hc : IsCoprime (Ideal.span {p j₁}) (Ideal.span {p j₂}) := hcop hij
    rw [heq] at hc
    exact (inferInstance : (Ideal.span {p j₂}).IsPrime).ne_top
      (Ideal.isUnit_iff.mp (isCoprime_self.mp hc))
  exact GaloisForLFunctions.JointMarkedMoments.prod_primes_injective hprime_ideal hinj_span

include hp hcop in
/-- Divisor-fiber bound for `(C₀, D₀, z) ↦ w = gcdElement p C₀ D₀ * z`: for any `w ≠ 0` and finite
candidate sets `cells` of `(C₀, D₀)` with `D₀ ⊆ C₀`, the number of triples `(C₀, D₀, z)` with
`gcdElement p C₀ D₀ * z = w` is at most `((idealDivisors (Ideal.span {w})).card : ℝ) ^ 2`. -/
theorem gcdElement_fiber_card_le
    (cells : Finset (Finset ι × Finset ι)) (hDC : ∀ cd ∈ cells, cd.2 ⊆ cd.1)
    (balls : Finset O) {w : O} (hw : w ≠ 0) :
    (((cells ×ˢ balls).filter (fun t => gcdElement p t.1.1 t.1.2 * t.2 = w)).card : ℝ) ≤
      ((idealDivisors (Ideal.span {w})).card : ℝ) ^ 2 := by
  let Iw : Ideal O := Ideal.span {w}
  have hIw : Iw ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hw
  let F := (cells ×ˢ balls).filter (fun t => gcdElement p t.1.1 t.1.2 * t.2 = w)
  have hprod_inj := span_finset_prod_injective p hp hcop
  let φ : (Finset ι × Finset ι) × O → Ideal O × Ideal O :=
    fun t => (∏ j ∈ t.1.1, Ideal.span {p j}, ∏ j ∈ t.1.2, Ideal.span {p j})
  have hinj : Set.InjOn φ F := by
    intro t₁ ht₁ t₂ ht₂ hφ
    have hC : t₁.1.1 = t₂.1.1 := hprod_inj (Prod.ext_iff.mp hφ).1
    have hD : t₁.1.2 = t₂.1.2 := hprod_inj (Prod.ext_iff.mp hφ).2
    have heq1 : gcdElement p t₁.1.1 t₁.1.2 * t₁.2 = w := (Finset.mem_filter.mp ht₁).2
    have heq2 : gcdElement p t₂.1.1 t₂.1.2 * t₂.2 = w := (Finset.mem_filter.mp ht₂).2
    rw [hC, hD] at heq1
    have hz : t₁.2 = t₂.2 := mul_left_cancel₀ (gcdElement_ne_zero p hp _ _) (heq1.trans heq2.symm)
    exact Prod.ext (Prod.ext hC hD) hz
  have hmaps : ∀ t ∈ F, φ t ∈ idealDivisors Iw ×ˢ idealDivisors Iw := by
    intro t ht
    obtain ⟨hmem_prod, heq⟩ := Finset.mem_filter.mp ht
    have hsub : t.1.2 ⊆ t.1.1 := hDC t.1 (Finset.mem_product.mp hmem_prod).1
    have hdvdC : (∏ i ∈ t.1.1, p i) ∣ w := by
      have hunion : (t.1.1 \ t.1.2) ∪ t.1.2 = t.1.1 := Finset.sdiff_union_of_subset hsub
      have hdisj : Disjoint (t.1.1 \ t.1.2) t.1.2 := Finset.sdiff_disjoint
      rw [← hunion, Finset.prod_union hdisj, ← heq]
      unfold gcdElement
      exact ⟨(∏ i ∈ t.1.1 \ t.1.2, p i) * t.2, by ring⟩
    have hdvdD : (∏ i ∈ t.1.2, p i) ∣ w :=
      (Finset.prod_dvd_prod_of_subset t.1.2 t.1.1 p hsub).trans hdvdC
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · rw [mem_idealDivisors hIw]
      dsimp [φ]
      rw [← SchwartzPlanePoisson.span_finset_prime_product,
        Ideal.span_singleton_dvd_span_singleton_iff_dvd]
      exact hdvdC
    · rw [mem_idealDivisors hIw]
      dsimp [φ]
      rw [← SchwartzPlanePoisson.span_finset_prime_product,
        Ideal.span_singleton_dvd_span_singleton_iff_dvd]
      exact hdvdD
  have hcard : F.card ≤ (idealDivisors Iw ×ˢ idealDivisors Iw).card :=
    Finset.card_le_card_of_injOn φ hmaps hinj
  rw [Finset.card_product, ← sq] at hcard
  exact_mod_cast hcard

include hp hcop in
/-- **`InjectiveMarks` fiber bound on `(tup, z) ↦ (∏ j ∈ tuplePrimeSet tup, p j)^4 * z`:**
Because `lists` is pairwise disjoint on `U_cand` and `i ↦ Ideal.span {p i}` is a family of distinct
prime ideals in the Dedekind domain `O` (`Unique (Ideal O)ˣ`), `JointMarkedMoments.prod_primes_injective`
implies `tup ↦ ∏ j ∈ tuplePrimeSet tup, Ideal.span {p j}` is injective! Consequently, for every
`w' ≠ 0`, at most `(idealDivisors (Ideal.span {w'})).card` pairs `(tup, z)` satisfy
`(∏ j ∈ tuplePrimeSet tup, p j)^4 * z = w'`. -/
theorem sexticTuple_fiber_card_le
    {U_cand : Finset σ} {lists : σ → Finset ι}
    (hdisj : (U_cand : Set σ).PairwiseDisjoint lists)
    (balls : Finset O) {w' : O} (hw' : w' ≠ 0) :
    (((Finset.univ ×ˢ balls : Finset ((∀ i : U_cand, lists i.val) × O)).filter
        (fun tz => (∏ j ∈ tuplePrimeSet tz.1, p j) ^ 4 * tz.2 = w')).card : ℝ) ≤
      ((idealDivisors (Ideal.span {w'})).card : ℝ) := by
  let Iw : Ideal O := Ideal.span {w'}
  have hIw : Iw ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hw'
  let F := (Finset.univ ×ˢ balls : Finset ((∀ i : U_cand, lists i.val) × O)).filter
    (fun tz => (∏ j ∈ tuplePrimeSet tz.1, p j) ^ 4 * tz.2 = w')
  have hprod_inj := span_finset_prod_injective p hp hcop
  let φ : ((∀ i : U_cand, lists i.val) × O) → Ideal O :=
    fun tz => ∏ j ∈ tuplePrimeSet tz.1, Ideal.span {p j}
  have hinj : Set.InjOn φ F := by
    intro tz₁ h₁ tz₂ h₂ hφ
    have hset : tuplePrimeSet tz₁.1 = tuplePrimeSet tz₂.1 := hprod_inj hφ
    have htup : tz₁.1 = tz₂.1 := by
      funext i
      have hmem1 : (tz₁.1 i).val ∈ tuplePrimeSet tz₁.1 :=
        Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
      rw [hset] at hmem1
      obtain ⟨i', _, heq_idx⟩ := Finset.mem_image.mp hmem1
      have hii' : i = i' := by
        by_contra hne
        have hne_val : i.val ≠ i'.val := fun hv => hne (Subtype.ext hv)
        have hd := hdisj i.property i'.property hne_val
        exact Finset.disjoint_left.mp hd (tz₁.1 i).property (heq_idx ▸ (tz₂.1 i').property)
      subst hii'
      exact Subtype.ext heq_idx.symm
    have heq1 : (∏ j ∈ tuplePrimeSet tz₁.1, p j) ^ 4 * tz₁.2 = w' := (Finset.mem_filter.mp h₁).2
    have heq2 : (∏ j ∈ tuplePrimeSet tz₂.1, p j) ^ 4 * tz₂.2 = w' := (Finset.mem_filter.mp h₂).2
    rw [htup] at heq1
    have hd0 : (∏ j ∈ tuplePrimeSet tz₂.1, p j) ^ 4 ≠ 0 :=
      pow_ne_zero 4 (Finset.prod_ne_zero_iff.mpr (fun j _ => hp j))
    exact Prod.ext htup (mul_left_cancel₀ hd0 (heq1.trans heq2.symm))
  have hmaps : ∀ tz ∈ F, φ tz ∈ idealDivisors Iw := by
    intro tz htz
    have heq : (∏ j ∈ tuplePrimeSet tz.1, p j) ^ 4 * tz.2 = w' := (Finset.mem_filter.mp htz).2
    rw [mem_idealDivisors hIw]
    dsimp [φ]
    rw [← SchwartzPlanePoisson.span_finset_prime_product,
      Ideal.span_singleton_dvd_span_singleton_iff_dvd]
    exact ⟨(∏ j ∈ tuplePrimeSet tz.1, p j) ^ 3 * tz.2, by rw [← heq]; ring⟩
  exact_mod_cast Finset.card_le_card_of_injOn φ hmaps hinj

end DualRowAlgebra

/-! ### Part III: `V₀`/`x₆` exponent certificates, `Q = {0}` parent reduction, and `7/8` cap -/

/-- Unconditional `V₀ ≥ 0`, `x₆ ≥ 0`, `z_J ≥ 0` extension of `stage1_large_value_certificate`:
because `rowCount ν x + ν ≥ 1` identically on `[0, 5/6] × [0, 1/2]` and `stage1_sixth_power_monotonicity`
saves `x₆ / 2` on sixth-power cofactors, both `V₀` and `x₆` strictly help the Stage-1 dual
large-value budget while preserving the full `1/2000` power saving. -/
theorem stage1_large_value_full {r ν x V₀ x₆ z_J : ℝ}
    (hr0 : 17 / 25 ≤ r) (hr1 : r ≤ 19 / 26)
    (hν0 : 11 / 25 ≤ ν) (hν1 : ν ≤ 3 / 4) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hV₀ : 0 ≤ V₀) (hx₆ : 0 ≤ x₆) (hzJ : 0 ≤ z_J) :
    (stage1DualScale r - V₀ - 6 * x₆) * rowCount ν x + ν * (r - V₀) +
        2 * x * ν * (stage1RemWidth r - z_J) + x₆ ≤
      (stage1DualScale r - V₀) + stage1Width r - 1 / 2000 := by
  have hbase := stage1_large_value_certificate hr0 hr1 hν0 hν1 hx0 hx1
  have hmono := stage1_sixth_power_monotonicity (H₀ := stage1DualScale r - V₀)
    hx₆ (by linarith) hν1 hx1
  have hJ := rowJ_pos (δ := ν) (x := x) (by linarith) (by linarith) hx1
  have hP0 : 0 ≤ rowP x := by unfold rowP; exact mul_nonneg (by linarith) (by linarith)
  have hrc1 : 1 ≤ rowCount ν x + ν := by
    unfold rowCount
    have hq : 0 ≤ (5 / 6 - ν) * ν * rowP x / (2 * rowJ ν x) :=
      div_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) hP0) (by linarith)
    linarith
  have hV_save : V₀ ≤ V₀ * (rowCount ν x + ν) := le_mul_of_one_le_right hV₀ hrc1
  have hzJ_save : 0 ≤ 2 * x * ν * z_J := by positivity
  linarith

/-- Regime-2 (`0 ≤ ν ≤ 11/25`) slot-splitting identity: if `S_rem` (width `z_rem' ≤ stage1RemWidth r + 3 η`)
is split into `S_keep` (width `z_keep` filling Stage-0 capacity `r_unm + 2 z_keep ≥ H_dual - 2 m_s - 20 η`)
and `S_drop` (`z_drop = z_rem' - z_keep ≥ 0`), then bounding `S_keep` by Stage-0 `deleted_source_energy`
at `Z ^ H_dual` and `S_drop` pointwise by `Z ^ (ν z_drop)` yields total exponent at most
`(stage1DualScale r - V₀) + stage1Width r + m_s + 20 η`. -/
theorem stage1_regime2_split_bound {r V₀ r_unm z_rem' z_keep H_dual ν m_s η : ℝ}
    (_hr0 : 17 / 25 ≤ r) (hr1 : r ≤ 19 / 26)
    (_hν0 : 0 ≤ ν) (hν1 : ν ≤ 11 / 25)
    (hη : 0 ≤ η) (hm_s : 0 ≤ m_s)
    (hrunm : r_unm ≤ r - V₀ + 2 * η)
    (hzrem : z_rem' ≤ stage1RemWidth r + 3 * η)
    (hH_hi : H_dual ≤ stage1DualScale r - V₀ + 4 * η)
    (hkeep : H_dual - 2 * m_s - 20 * η ≤ r_unm + 2 * z_keep)
    (hdrop0 : 0 ≤ z_rem' - z_keep) :
    H_dual + ν * (z_rem' - z_keep) ≤
      (stage1DualScale r - V₀) + stage1Width r + m_s + 20 * η := by
  have hdz0 : 0 ≤ stage1Line r - (1 - r) / 2 := by unfold stage1Line; linarith
  -- Exact identity: r + 2 * stage1RemWidth r - stage1DualScale r = 2 * (25/11) * stage1Width r.
  have hid : (r - V₀) + 2 * stage1RemWidth r - (stage1DualScale r - V₀) =
      2 * ((25 / 11) * stage1Width r) := by
    unfold stage1RemWidth stage1DualScale stage1Width stage1Line; ring
  have h2drop : 2 * (z_rem' - z_keep) ≤
      2 * ((25 / 11) * stage1Width r) + (stage1DualScale r - V₀ - H_dual) + 2 * m_s + 28 * η := by
    linarith
  have hdrop : z_rem' - z_keep ≤
      (25 / 11) * stage1Width r + (stage1DualScale r - V₀ - H_dual) / 2 + m_s + 14 * η := by
    linarith
  have hν_drop : ν * (z_rem' - z_keep) ≤ (11 / 25) * (z_rem' - z_keep) :=
    mul_le_mul_of_nonneg_right hν1 hdrop0
  have hw0 : 0 ≤ stage1Width r := by
    unfold stage1Width; exact mul_nonneg (by norm_num) hdz0
  linarith

/-- Regime-2 high-`x₆` (`H_dual ≤ r - V₀ + 4 η`, so `z_keep = 0`) bound via `no_slot_endpoint`:
`(H_dual + 5 r_unm) / 6 + (11/25) z_rem' ≤ (stage1DualScale r - V₀) - 1/20` whenever `V₀ ≤ 1/50`. -/
theorem stage1_regime2_high_x6_bound {r V₀ r_unm z_rem' H_dual ν η : ℝ}
    (hr0 : 17 / 25 ≤ r) (_hr1 : r ≤ 19 / 26)
    (_hν0 : 0 ≤ ν) (hν1 : ν ≤ 11 / 25)
    (_hV0 : 0 ≤ V₀) (_hV1 : V₀ ≤ 1 / 50)
    (_hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 2000)
    (hrunm : r_unm ≤ r - V₀ + 2 * η)
    (hzrem : z_rem' ≤ stage1RemWidth r + 3 * η)
    (hrem0 : 0 ≤ z_rem')
    (hH_le : H_dual ≤ r - V₀ + 4 * η) :
    max H_dual ((H_dual + 5 * r_unm) / 6) + ν * z_rem' ≤
      (stage1DualScale r - V₀) - 1 / 20 := by
  have hνz : ν * z_rem' ≤ (11 / 25) * z_rem' := mul_le_mul_of_nonneg_right hν1 hrem0
  have hmax : max H_dual ((H_dual + 5 * r_unm) / 6) ≤
      (stage1DualScale r - V₀) - 1 / 20 - ν * z_rem' := by
    unfold stage1DualScale stage1RemWidth stage1Width stage1Line at *
    apply max_le <;> linarith
  linarith

section ParentCleanQ0

open InversePrioritySecondSource InversePrincipalEnergy InverseSecondSourceBlocks

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hcop in
/-- **Exact `C₀, D₀` elimination at `Q = {0}`:**
Under `w = gcdElement p C₀ D₀ * z` (`D₀ ⊆ C₀`), both `C₀` and `D₀` disappear completely from
the puncture `(m * d_D) * d₀`, from the character labels `(c₀, d₀)`, and from the residual slot
lists `lists i \ (C₀ ∪ D)`! Every surviving subset `S` in `inputConjugateRow` at `w` automatically
avoids `C₀` (via `w`) and `D` (via `m * d_D`), so `lists i \ (C₀ ∪ D)` equals `lists i` on `S`. -/
theorem inputConjugateRow_q0_clean
    (pool : Finset ι) (Ψ₀ : O →* ℂ) (m : O)
    {C₀ D₀ : Finset ι} (hDC : D₀ ⊆ C₀) (D : Finset ι)
    (S_rem : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (V : 𝓢(ℝ, ℂ)) (X : ℝ) (z : O) :
    let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
    let d_D := ∏ j ∈ D, p j
    let c₀ := ∏ i ∈ C₀, p i
    let d₀ := ∏ i ∈ D₀, p i
    let w := gcdElement p C₀ D₀ * z
    inputConjugateRow p χ pool Ψ₀ ((m * d_D) * d₀) c₀ d₀
        (markedRadial p S_rem (fun i => lists i \ (C₀ ∪ D)) a ∅ V X) z =
      inputConjugateRow p χ pool Ψ₀ (m * d_D) 1 1
        (markedRadial p S_rem lists a ∅ V X) w := by
  intro χ d_D c₀ d₀ w
  rw [inputConjugateRow_old_divisor_mask p hg pool Ψ₀ (m * d_D) c₀ d₀ _ z]
  rw [inputConjugateRow_absorb_cd p hcop hg pool Ψ₀ (m * d_D) hDC _ z]
  unfold inputConjugateRow supportConjugateSum secondInputCoefficient
  apply Finset.sum_congr rfl
  intro S _
  by_cases hd : Disjoint S (C₀ ∪ D)
  · have hpm : primeMark S_rem (fun i => lists i \ (C₀ ∪ D)) a (∅ ∪ S) =
        primeMark S_rem lists a (∅ ∪ S) := by
      simp only [Finset.empty_union, InverseMoment.primeMark, InverseMoment.primeSlot]
      apply Finset.prod_congr rfl
      intro i _
      have hinter : (lists i \ (C₀ ∪ D)) ∩ S = lists i ∩ S := by
        ext q
        simp only [Finset.mem_inter, Finset.mem_sdiff]
        exact ⟨fun h => ⟨h.1.1, h.2⟩,
          fun h => ⟨⟨h.1, Finset.disjoint_left.mp hd h.2⟩, h.2⟩⟩
      simp only [Finset.sum_ite_mem, hinter]
    simp only [markedRadial, hpm]
    rfl
  · rw [Finset.disjoint_union_right, not_and_or] at hd
    rcases hd with hC | hD
    · obtain ⟨j, hjS, hjC⟩ := Finset.not_disjoint_iff.mp hC
      letI : Field (O ⧸ Ideal.span {p j}) := Ideal.Quotient.field (Ideal.span {p j})
      have hdvd_w : p j ∣ w := by
        dsimp [w]
        unfold gcdElement
        by_cases hjD₀ : j ∈ D₀
        · exact (Finset.dvd_prod_of_mem p hjD₀).trans ⟨(∏ k ∈ C₀ \ D₀, p k) ^ 2 * z, by ring⟩
        · have hjCD : j ∈ C₀ \ D₀ := Finset.mem_sdiff.mpr ⟨hjC, hjD₀⟩
          exact (Finset.dvd_prod_of_mem p hjCD).trans
            ⟨(∏ k ∈ C₀ \ D₀, p k) * (∏ k ∈ D₀, p k) * z, by ring⟩
      have h0 : primeSubsetRow p χ S w = 0 := by
        unfold primeSubsetRow
        apply Finset.prod_eq_zero hjS
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdvd_w)]
        exact MulChar.map_nonunit (χ j) not_isUnit_zero
      rw [h0, star_zero, mul_zero, mul_zero]
    · obtain ⟨j, hjS, hjD⟩ := Finset.not_disjoint_iff.mp hD
      have hdvd_m : p j ∣ m * d_D :=
        (Finset.dvd_prod_of_mem p hjD).trans ⟨m, by ring⟩
      have hm0 : primeCoprimeMask p S (m * d_D) = 0 := by
        unfold primeCoprimeMask
        apply Finset.prod_eq_zero hjS
        rw [if_pos hdvd_m]; ring
      simp only [hm0, mul_zero, zero_mul]

omit [DecidableEq ι] in
/-- Sixth-power frequency multiplication in `primeSubsetRow`: multiplying `u` by `g ^ 6` simply
multiplies `primeSubsetRow p χ S u` by `primeCoprimeMask p S g`. -/
theorem primeSubsetRow_mul_sixth_pow (S : Finset ι) (u g : O) :
    let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
    primeSubsetRow p χ S (u * g ^ 6) =
      primeCoprimeMask p S g * primeSubsetRow p χ S u := by
  intro χ
  unfold primeSubsetRow primeCoprimeMask
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  letI : Field (O ⧸ Ideal.span {p i}) := Ideal.Quotient.field (Ideal.span {p i})
  by_cases hdvd : p i ∣ g
  · have hmem : g ∈ Ideal.span {p i} := Ideal.mem_span_singleton.mpr hdvd
    rw [if_pos hdvd, map_mul, map_pow, map_mul (χ i), map_pow (χ i),
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem,
      MulChar.map_nonunit (χ i) not_isUnit_zero, zero_pow (by decide)]
    ring
  · have h6 : χ i (Ideal.Quotient.mk (Ideal.span {p i}) g) ^ 6 = 1 :=
      complexSexticChar_pow_six_of_not_dvd p hg i hdvd
    rw [if_neg hdvd, map_mul, map_pow, map_mul (χ i), map_pow (χ i), h6]
    ring

omit [DecidableEq ι] in
/-- Consequently, `inputConjugateRow` at `u * g ^ 6` equals `inputConjugateRow` at `u` with `g`
absorbed into the coprimality puncture `m * g`! -/
theorem inputConjugateRow_mul_sixth_pow
    (pool : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ) (u g : O) :
    let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
    inputConjugateRow p χ pool Ψ m c d H (u * g ^ 6) =
      inputConjugateRow p χ pool Ψ (m * g) c d H u := by
  intro χ
  unfold inputConjugateRow supportConjugateSum secondInputCoefficient
  apply Finset.sum_congr rfl
  intro S _
  rw [primeSubsetRow_mul_sixth_pow p hg S u g, star_mul]
  have hmask_real : star (primeCoprimeMask p S g) = primeCoprimeMask p S g := by
    unfold primeCoprimeMask
    rw [star_prod]
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> simp
  have hmask_mul : primeCoprimeMask p S (m * g) =
      primeCoprimeMask p S m * primeCoprimeMask p S g := by
    unfold primeCoprimeMask
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    have hprime : (Ideal.span {p i}).IsPrime := inferInstance
    by_cases hm : p i ∣ m
    · have hmg : p i ∣ m * g := dvd_mul_of_dvd_left hm g
      rw [if_pos hm, if_pos hmg]; ring
    · by_cases hg_dvd : p i ∣ g
      · have hmg : p i ∣ m * g := dvd_mul_of_dvd_right hg_dvd m
        rw [if_neg hm, if_pos hg_dvd, if_pos hmg]; ring
      · have hmg : ¬ (p i ∣ m * g) := fun h => by
          rcases hprime.mem_or_mem (Ideal.mem_span_singleton.mpr h) with h1 | h2
          · exact hm (Ideal.mem_span_singleton.mp h1)
          · exact hg_dvd (Ideal.mem_span_singleton.mp h2)
        rw [if_neg hm, if_neg hg_dvd, if_neg hmg]; ring
  rw [hmask_real, hmask_mul]
  ring

/-- Assignment-tuple decomposition of `inputConjugateRow` with `markedRadial`:
because `lists` is pairwise disjoint on `S_rem`, choosing `S ⊆ pool` and one prime `q_i ∈ lists i ∩ S`
per slot `i ∈ S_rem` is in bijection with choosing `tup : ∀ i : S_rem, lists i.val` (`Q_tup ⊆ pool`)
and `U ⊆ pool \ Q_tup` (`S = U ∪ Q_tup`). -/
theorem inputConjugateRow_markedRadial_eq_tuple_sum
    (pool : Finset ι) (Ψ₀ : O →* ℂ) (m' : O)
    (S_rem : Finset σ) (lists : σ → Finset ι)
    (hlists_pool : ∀ i ∈ S_rem, lists i ⊆ pool)
    (hdisj : (S_rem : Set σ).PairwiseDisjoint lists)
    (a : σ → ι → ℂ) (V : ℝ → ℂ) (X : ℝ) (w : O) :
    let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
    inputConjugateRow p χ pool Ψ₀ m' 1 1
        (fun S => InverseMoment.primeMark S_rem lists a S * V (primeProductNorm p S / X)) w =
      (-1 : ℂ) ^ S_rem.card *
        ∑ tup : (∀ i : S_rem, lists i.val),
          (tupleCoeff a tup * Ψ₀ (∏ j ∈ tuplePrimeSet tup, p j) *
            primeCoprimeMask p (tuplePrimeSet tup) m' *
            star (primeSubsetRow p χ (tuplePrimeSet tup) w)) *
          inputConjugateRow p χ (pool \ tuplePrimeSet tup) Ψ₀ m' 1 1
            (fun U => V ((primeProductNorm p U * primeProductNorm p (tuplePrimeSet tup)) / X)) w := by
  intro χ
  -- Expand `primeMark` via `Fintype.prod_sum` on `S_rem` and swap the finite sums.
  have hpm (S : Finset ι) :
      InverseMoment.primeMark S_rem lists a S =
        ∑ tup : (∀ i : S_rem, lists i.val),
          if tuplePrimeSet tup ⊆ S then tupleCoeff a tup else 0 := by
    unfold InverseMoment.primeMark InverseMoment.primeSlot tupleCoeff tuplePrimeSet
    rw [← Finset.prod_coe_sort S_rem
      (fun i => ∑ q ∈ lists i, if q ∈ S then a i q else 0)]
    have hstep : ∀ i : S_rem,
        (∑ q ∈ lists i.val, if q ∈ S then a i.val q else 0) =
          ∑ q : lists i.val, if q.val ∈ S then a i.val q.val else 0 := by
      intro i; exact (Finset.sum_coe_sort (lists i.val) _).symm
    simp_rw [hstep]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro tup _
    by_cases hsub : ∀ i : S_rem, (tup i).val ∈ S
    · have hsub' : Finset.univ.image (fun i : S_rem => (tup i).val) ⊆ S := by
        intro q hq; obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq; exact hsub i
      rw [if_pos hsub']
      exact Finset.prod_congr rfl (fun i _ => if_pos (hsub i))
    · have hnsub' : ¬ (Finset.univ.image (fun i : S_rem => (tup i).val) ⊆ S) := by
        intro hs; apply hsub; intro i
        exact hs (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
      rw [if_neg hnsub']
      obtain ⟨i₀, hi₀⟩ := not_forall.mp hsub
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (if_neg hi₀)
  have h1 (T : Finset ι) : primeSubsetRow p χ T 1 = 1 := by simp [primeSubsetRow]
  unfold inputConjugateRow supportConjugateSum secondInputCoefficient
  simp only [h1, one_pow, mul_one, hpm]
  -- Distribute and swap `∑ S ∈ pool.powerset` with `∑ tup`.
  have hswap :
      (∑ S ∈ pool.powerset,
        supportMobius S * (Ψ₀ (∏ i ∈ S, p i) * primeCoprimeMask p S m' *
          ((∑ tup : (∀ i : S_rem, lists i.val),
            if tuplePrimeSet tup ⊆ S then tupleCoeff a tup else 0) *
          V (primeProductNorm p S / X))) * star (primeSubsetRow p χ S w)) =
      ∑ tup : (∀ i : S_rem, lists i.val),
        ∑ S ∈ pool.powerset,
          if tuplePrimeSet tup ⊆ S then
            supportMobius S * (Ψ₀ (∏ i ∈ S, p i) * primeCoprimeMask p S m' *
              tupleCoeff a tup * V (primeProductNorm p S / X)) *
              star (primeSubsetRow p χ S w)
          else 0 := by
    trans (∑ S ∈ pool.powerset, ∑ tup : (∀ i : S_rem, lists i.val),
        if tuplePrimeSet tup ⊆ S then
          supportMobius S * (Ψ₀ (∏ i ∈ S, p i) * primeCoprimeMask p S m' *
            tupleCoeff a tup * V (primeProductNorm p S / X)) *
            star (primeSubsetRow p χ S w)
        else 0)
    · apply Finset.sum_congr rfl
      intro S _
      rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro tup _
      split_ifs <;> ring
    · exact Finset.sum_comm
  rw [hswap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro tup _
  let Q_tup := tuplePrimeSet tup
  have hQ_pool : Q_tup ⊆ pool := by
    intro q hq
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hq
    exact hlists_pool i.val i.property (tup i).property
  have hQ_card : Q_tup.card = S_rem.card := by
    dsimp [Q_tup, tuplePrimeSet]
    rw [Finset.card_image_of_injective _ (fun i₁ i₂ he => by
      by_contra hne
      have hv : i₁.val ≠ i₂.val := fun h => hne (Subtype.ext h)
      exact Finset.disjoint_left.mp (hdisj i₁.property i₂.property hv)
        (tup i₁).property (he ▸ (tup i₂).property)),
      Finset.card_attach]
  -- Bijection `U ∈ (pool \ Q_tup).powerset ↔ S ∈ pool.powerset` with `Q_tup ⊆ S` via `S = U ∪ Q_tup`.
  rw [← Finset.sum_filter]
  symm
  calc
    (-1 : ℂ) ^ S_rem.card *
        ((tupleCoeff a tup * Ψ₀ (∏ j ∈ Q_tup, p j) * primeCoprimeMask p Q_tup m' *
            star (primeSubsetRow p χ Q_tup w)) *
          ∑ U ∈ (pool \ Q_tup).powerset,
            supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U m' *
              V ((primeProductNorm p U * primeProductNorm p Q_tup) / X)) *
              star (primeSubsetRow p χ U w))
      = ∑ U ∈ (pool \ Q_tup).powerset,
          supportMobius (U ∪ Q_tup) *
            (Ψ₀ (∏ i ∈ U ∪ Q_tup, p i) * primeCoprimeMask p (U ∪ Q_tup) m' *
              tupleCoeff a tup * V (primeProductNorm p (U ∪ Q_tup) / X)) *
            star (primeSubsetRow p χ (U ∪ Q_tup) w) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro U hU
        have hdUQ : Disjoint U Q_tup :=
          Disjoint.mono_left (Finset.mem_powerset.mp hU) Finset.sdiff_disjoint
        have hmob : supportMobius (U ∪ Q_tup) = (-1 : ℂ) ^ S_rem.card * supportMobius U := by
          rw [supportMobius_union U Q_tup hdUQ]
          unfold supportMobius
          rw [hQ_card]; ring
        have hprodU : Ψ₀ (∏ i ∈ U ∪ Q_tup, p i) = Ψ₀ (∏ i ∈ U, p i) * Ψ₀ (∏ j ∈ Q_tup, p j) := by
          rw [Finset.prod_union hdUQ, map_mul]
        have hmaskU : primeCoprimeMask p (U ∪ Q_tup) m' =
            primeCoprimeMask p U m' * primeCoprimeMask p Q_tup m' := by
          unfold primeCoprimeMask; exact Finset.prod_union hdUQ
        have hrowU : star (primeSubsetRow p χ (U ∪ Q_tup) w) =
            star (primeSubsetRow p χ U w) * star (primeSubsetRow p χ Q_tup w) := by
          rw [primeSubsetRow_union p χ U Q_tup hdUQ, star_mul, mul_comm]
        have hnormU : primeProductNorm p (U ∪ Q_tup) =
            primeProductNorm p U * primeProductNorm p Q_tup :=
          primeProductNorm_union p U Q_tup hdUQ
        rw [hmob, hprodU, hmaskU, hrowU, hnormU]
        ring
    _ = _ := by
        apply Finset.sum_bij (fun U _ => U ∪ Q_tup)
        · intro U hU
          refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ?_, Finset.subset_union_right⟩
          exact Finset.union_subset ((Finset.mem_powerset.mp hU).trans Finset.sdiff_subset) hQ_pool
        · intro U₁ hU₁ U₂ hU₂ heq
          have hd1 : Disjoint U₁ Q_tup :=
            Disjoint.mono_left (Finset.mem_powerset.mp hU₁) Finset.sdiff_disjoint
          have hd2 : Disjoint U₂ Q_tup :=
            Disjoint.mono_left (Finset.mem_powerset.mp hU₂) Finset.sdiff_disjoint
          calc U₁ = (U₁ ∪ Q_tup) \ Q_tup := (Finset.union_sdiff_cancel_right hd1).symm
            _ = (U₂ ∪ Q_tup) \ Q_tup := by rw [heq]
            _ = U₂ := Finset.union_sdiff_cancel_right hd2
        · intro S hS
          obtain ⟨hSp, hQS⟩ := Finset.mem_filter.mp hS
          refine ⟨S \ Q_tup, Finset.mem_powerset.mpr (Finset.sdiff_subset_sdiff
            (Finset.mem_powerset.mp hSp) (Finset.Subset.refl _)), Finset.sdiff_union_of_subset hQS⟩
        · intro _ _; rfl

end ParentCleanQ0

/-- **Unconditional `7/8` cap on `detectorMaximum`:**
Because `ProbeFinalAssemblyUnconditional.hecke_ne_zero_of_seven_eighths_lt_re` already establishes
zero-freeness of all Hecke `L`-functions on `Re s > 7/8` away from the principal pole at `s = 1`,
every detector family `χ : ι' → HeckeFamily.Character` satisfies `detectorMaximum χ T ≤ 7/8` at
every height `T : ℝ`! -/
theorem detectorMaximum_le_seven_eighths {ι' : Type*} [Fintype ι']
    (χ : ι' → HeckeFamily.Character) (T : ℝ) :
    ProbeHighRowFamily.detectorMaximum χ T ≤ 7 / 8 := by
  rcases le_or_gt (ProbeHighRowFamily.detectorMaximum χ T) (51 / 100) with hle | hgt
  · linarith
  · obtain ⟨j, s, hz, hpole, _, hs⟩ := ProbeHighRowFamily.detectorMaximum_attained χ T hgt
    rw [← hs]
    by_contra hgt78
    have hre : (7 / 8 : ℝ) < s.re := lt_of_not_ge hgt78
    have hor : s ≠ 1 ∨ (χ j).residue ≠ 1 := by
      by_cases hs1 : s = 1
      · exact Or.inr (fun hres => hpole ⟨hres, hs1⟩)
      · exact Or.inl hs1
    exact ProbeFinalAssemblyUnconditional.hecke_nonzero (χ j) s hre hor hz

/-! ### Part IV: Crossing-branch row count, finite geometric unpuncturing, and `polynomial` bridge -/

section CrossingRowCount

open HeckeDetectorRowCount

/-- Crossing-branch variant of `count_bound_of_source_branches` at `Δ = 0`:
`hI` is only required on `crossing x t ≤ r < 1` (matching `stage1_slot_supply_with_zJ.1`), and
`hP` is only required on `r ≤ crossing x t` (matching `stage1_slot_supply_with_zJ.2`). -/
theorem count_bound_of_crossing_branches (B C U δ x t r m ε ν γ : ℝ)
    (hC : 0 ≤ C) (hU : 1 ≤ U) (hδ : 0 ≤ δ) (hδ' : δ ≤ 5 / 6)
    (hx : 0 ≤ x) (hx' : x ≤ 1 / 2)
    (ht : 1 ≤ t) (ht' : t ≤ 3 / 2) (hν : 0 ≤ ν) (hγ : 0 ≤ γ)
    (hleft : t - r - γ ≤ m) (hright : r ≤ t + γ)
    (hI0 : B ≤ C * U ^ (max 1 ((1 + 5 * r) / 6) - δ * r + ε))
    (hP0 : B ≤ C * U ^ (1 - 2 * δ * m + ε))
    (hI : crossing x t ≤ r → r < 1 → ν < (1 - r) / 2 →
      B ≤ C * U ^ (inverseExponent δ x r + ε))
    (hP : r ≤ crossing x t → m < 1 / 2 → ν < (1 - 2 * m) / (9 / 2) →
      B ≤ C * U ^ (1 - 2 * δ * m - 2 * (δ * x) * (1 - 2 * m) / (9 / 2) + ε)) :
    B ≤ C * U ^ (max (shortExponent δ x t) (longExponent δ t) + ε + 6 * ν + 5 * γ) := by
  let target := max (shortExponent δ x t) (longExponent δ t) + ε + 6 * ν + 5 * γ
  have hshort : shortExponent δ x t ≤ max (shortExponent δ x t) (longExponent δ t) := le_max_left _ _
  have hlong : longExponent δ t ≤ max (shortExponent δ x t) (longExponent δ t) := le_max_right _ _
  have hbase := short_ge_base hδ hx hx' ht'
  have hcross := crossing_bounds hx hx' ht ht'
  have hchoose := selected_short_bound (t := t) (r := r) hδ hx hx'
  have promote (p : ℝ) (hp : B ≤ C * U ^ p) (hpt : p ≤ target) : B ≤ C * U ^ target :=
    hp.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hpt) hC)
  by_cases hr1 : 1 ≤ r
  · have hmax : max 1 ((1 + 5 * r) / 6) = (1 + 5 * r) / 6 := max_eq_right (by linarith)
    rw [hmax] at hI0
    apply promote _ hI0
    have hl := long_count_bound hδ' hγ hright
    dsimp [target]
    have hcγ : (5 / 6 - δ) * γ ≤ γ := by nlinarith [mul_nonneg hδ hγ]
    nlinarith
  have hr1' : r < 1 := lt_of_not_ge hr1
  have hmax : max 1 ((1 + 5 * r) / 6) = 1 := max_eq_left (by linarith)
  rw [hmax] at hI0
  by_cases hrc : crossing x t ≤ r
  · by_cases hcap : (1 - r) / 2 ≤ ν
    · apply promote _ hI0
      have hz := inverse_zero_capacity hδ hcap
      have hv : 2 * δ * ν ≤ 6 * ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hν]
      dsimp [target]
      linarith
    · apply promote _ (hI hrc hr1' (lt_of_not_ge hcap))
      have hs := hchoose.2 hrc
      dsimp [target]
      linarith
  have hrc' : r ≤ crossing x t := (lt_of_not_ge hrc).le
  by_cases hm : 1 / 2 ≤ m
  · apply promote _ hP0
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    dsimp [target]
    linarith
  have hm' : m < 1 / 2 := lt_of_not_ge hm
  by_cases hcap : (1 - 2 * m) / (9 / 2) ≤ ν
  · apply promote _ hP0
    have hz := plain_zero_capacity hδ (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) ≤ 1) hν
      (show (1 - 2 * m) / (6 * (3 / 4)) ≤ ν by convert hcap using 1; ring)
    have hv : 6 * δ * ν ≤ 6 * ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hν]
    dsimp [target]
    linarith
  · apply promote _ (hP hrc' hm' (lt_of_not_ge hcap))
    have hmm : 1 / 3 - γ ≤ m := by linarith [hcross.2.2.1]
    have hp := plain_capacity_comparison hδ (show δ ≤ 1 by linarith) hx hx'
      (le_refl (0 : ℝ)) (by norm_num) hmm hm'.le hγ hleft
    simp only [mul_zero, add_zero] at hp
    have hs := hchoose.1 hrc'
    dsimp [target]
    linarith

/-- At the balanced adaptive cutoff `t = Endpoint.balancedCutoff δ (1/2 - x)`, `crossing x t`
equals `stage1Crossing δ x` and `max (shortExponent δ x t) (longExponent δ t)` equals
`Budget.rowCount δ x`. -/
theorem stage1_crossing_and_count_eq {δ x : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    let t := Endpoint.balancedCutoff δ (1 / 2 - x)
    crossing x t = stage1Crossing δ x ∧
      max (shortExponent δ x t) (longExponent δ t) = rowCount δ x := by
  intro t
  have hJ := rowJ_pos (δ := δ) (x := x) hδ0 hδ1 hx1
  have hD : 7 / 9 ≤ rowD x := by unfold rowD; linarith
  have hden : Endpoint.balanceDenominator δ (1 / 2 - x) = rowJ δ x := by
    unfold Endpoint.balanceDenominator Endpoint.denominator Endpoint.primeWeight rowJ rowD rowP
    ring
  have hpw : Endpoint.primeWeight (1 / 2 - x) = rowP x := by
    unfold Endpoint.primeWeight rowP; ring
  have ht_eq : t = 1 + δ * rowP x / (2 * rowJ δ x) := by
    dsimp [t]; unfold Endpoint.balancedCutoff; rw [hden, hpw]
  constructor
  · rw [ht_eq]
    unfold crossing stage1Crossing denominator rowD
    field_simp [(show (3 - 17 * x / 9 : ℝ) ≠ 0 by linarith), (show rowJ δ x ≠ 0 by linarith)]
  · rw [balanced_count_identity hδ0 hδ1 hx0 hx1]
    unfold Endpoint.balancedRowCount Endpoint.balancedCutoff rowCount
    rw [hden, hpw]
    field_simp [(show rowJ δ x ≠ 0 by linarith)]
    ring

end CrossingRowCount

section FiniteGeometricUnpuncturing

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- Single-prime step on `inputConjugateRow`: splitting `pool.powerset` at `q ∈ pool` gives
`G_{pool}(X) = G_{pool.erase q}(X) - α_q(w) * G_{pool.erase q}(X / N_q)`. -/
lemma inputConjugateRow_split_prime
    (pool : Finset ι) {q : ι} (hq : q ∈ pool)
    (Ψ₀ : O →* ℂ) (m' : O) (W : ℝ → ℂ) (X : ℝ) (w : O) :
    let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
    let N_q := ‖ringComplex (p q)‖ ^ 2
    let α := Ψ₀ (p q) * primeCoprimeMask p {q} m' * star (primeSubsetRow p χ {q} w)
    inputConjugateRow p χ (pool.erase q) Ψ₀ m' 1 1
        (fun U => W (primeProductNorm p U / X)) w =
      inputConjugateRow p χ pool Ψ₀ m' 1 1
        (fun U => W (primeProductNorm p U / X)) w +
      α * inputConjugateRow p χ (pool.erase q) Ψ₀ m' 1 1
        (fun U => W (primeProductNorm p U / (X / N_q))) w := by
  intro χ N_q α
  have hins : insert q (pool.erase q) = pool := Finset.insert_erase hq
  have hnot : q ∉ pool.erase q := fun h => (Finset.mem_erase.mp h).1 rfl
  have h1 (T : Finset ι) : primeSubsetRow p χ T 1 = 1 := by simp [primeSubsetRow]
  have hpool_sum : ∀ f : Finset ι → ℂ,
      (∑ S ∈ pool.powerset, f S) =
        (∑ S ∈ (pool.erase q).powerset, f S) +
          ∑ S ∈ (pool.erase q).powerset.image (insert q), f S := by
    intro f
    conv_lhs => rw [← hins, Finset.powerset_insert]
    exact Finset.sum_union (Finset.disjoint_iff_ne.mpr (fun S hS T hT heq => by
      obtain ⟨U, _hU, rfl⟩ := Finset.mem_image.mp hT
      exact hnot ((Finset.mem_powerset.mp hS) (heq ▸ Finset.mem_insert_self q U))))
  unfold inputConjugateRow supportConjugateSum secondInputCoefficient
  simp only [h1, one_pow, mul_one]
  rw [hpool_sum]
  rw [Finset.sum_image (fun U₁ hU₁ U₂ hU₂ heq => by
    have hq1 : q ∉ U₁ := fun h => hnot ((Finset.mem_powerset.mp hU₁) h)
    have hq2 : q ∉ U₂ := fun h => hnot ((Finset.mem_powerset.mp hU₂) h)
    exact (Finset.erase_insert hq1).symm.trans ((congrArg (fun S => S.erase q) heq).trans
      (Finset.erase_insert hq2)))]
  have hsecond :
      (∑ U ∈ (pool.erase q).powerset,
        supportMobius (insert q U) * (Ψ₀ (∏ i ∈ insert q U, p i) *
          primeCoprimeMask p (insert q U) m' * W (primeProductNorm p (insert q U) / X)) *
          star (primeSubsetRow p χ (insert q U) w)) =
      -(α * ∑ U ∈ (pool.erase q).powerset,
        supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U m' *
          W (primeProductNorm p U / (X / N_q))) * star (primeSubsetRow p χ U w)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro U hU
    have hqU : q ∉ U := fun h => hnot ((Finset.mem_powerset.mp hU) h)
    have hd : Disjoint {q} U := Finset.disjoint_singleton_left.mpr hqU
    have hinsU : insert q U = {q} ∪ U := (Finset.singleton_union q U).symm
    have hmob : supportMobius ({q} ∪ U) = -supportMobius U := by
      rw [supportMobius_union {q} U hd]; simp [supportMobius]
    have hprod : Ψ₀ (∏ i ∈ {q} ∪ U, p i) = Ψ₀ (p q) * Ψ₀ (∏ i ∈ U, p i) := by
      rw [Finset.prod_union hd, Finset.prod_singleton, map_mul]
    have hmask : primeCoprimeMask p ({q} ∪ U) m' =
        primeCoprimeMask p {q} m' * primeCoprimeMask p U m' := by
      unfold primeCoprimeMask; exact Finset.prod_union hd
    have hrow : star (primeSubsetRow p χ ({q} ∪ U) w) =
        star (primeSubsetRow p χ {q} w) * star (primeSubsetRow p χ U w) := by
      rw [primeSubsetRow_union p χ {q} U hd, star_mul, mul_comm]
    have hnorm : primeProductNorm p ({q} ∪ U) / X = primeProductNorm p U / (X / N_q) := by
      rw [primeProductNorm_union p {q} U hd]
      have hNq : primeProductNorm p {q} = N_q := by simp [primeProductNorm, N_q]
      rw [hNq, div_div_eq_mul_div, mul_comm]
    rw [hinsU, hmob, hprod, hmask, hrow, hnorm]
    dsimp [α]
    ring
  rw [hsecond]
  ring

/-- Finite geometric-series expansion of `inputConjugateRow` at `pool.erase q`:
when `b_hi * X < N_q ^ M` and `W y ≠ 0 → y ≤ b_hi`, the `M`-th remainder vanishes identically! -/
theorem inputConjugateRow_erase_prime_geom
    (hp_local : ∀ i, p i ≠ 0)
    (pool : Finset ι) {q : ι} (hq : q ∈ pool)
    (Ψ₀ : O →* ℂ) (m' : O) (W : ℝ → ℂ) {b_hi : ℝ} (hb : ∀ y, W y ≠ 0 → y ≤ b_hi)
    {X : ℝ} (hX : 0 < X) (w : O) (M : ℕ)
    (hterm : b_hi * X < (‖ringComplex (p q)‖ ^ 2) ^ M) :
    let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
    let N_q := ‖ringComplex (p q)‖ ^ 2
    let α := Ψ₀ (p q) * primeCoprimeMask p {q} m' * star (primeSubsetRow p χ {q} w)
    inputConjugateRow p χ (pool.erase q) Ψ₀ m' 1 1
        (fun U => W (primeProductNorm p U / X)) w =
      ∑ k ∈ Finset.range M,
        α ^ k * inputConjugateRow p χ pool Ψ₀ m' 1 1
          (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w := by
  intro χ N_q α
  have hNq_pos : 0 < N_q := by
    dsimp [N_q]
    exact sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero (hp_local q)))
  have hrec : ∀ K : ℕ,
      inputConjugateRow p χ (pool.erase q) Ψ₀ m' 1 1
          (fun U => W (primeProductNorm p U / X)) w =
        (∑ k ∈ Finset.range K,
          α ^ k * inputConjugateRow p χ pool Ψ₀ m' 1 1
            (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w) +
        α ^ K * inputConjugateRow p χ (pool.erase q) Ψ₀ m' 1 1
          (fun U => W (primeProductNorm p U / (X / N_q ^ K))) w := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [ih, Finset.sum_range_succ,
        inputConjugateRow_split_prime p hg pool hq Ψ₀ m' W (X / N_q ^ K) w]
      have hdiv : (X / N_q ^ K) / N_q = X / N_q ^ (K + 1) := by rw [div_div, ← pow_succ]
      dsimp only [N_q] at hdiv ⊢
      simp_rw [hdiv]
      ring
  rw [hrec M]
  have hrem0 : inputConjugateRow p χ (pool.erase q) Ψ₀ m' 1 1
      (fun U => W (primeProductNorm p U / (X / N_q ^ M))) w = 0 := by
    unfold inputConjugateRow supportConjugateSum secondInputCoefficient
    apply Finset.sum_eq_zero
    intro U _
    have hU1 : 1 ≤ primeProductNorm p U := primeProductNorm_ge_one p hp_local U
    have hXM_pos : 0 < X / N_q ^ M := div_pos hX (pow_pos hNq_pos M)
    have hgt : b_hi < primeProductNorm p U / (X / N_q ^ M) := by
      rw [lt_div_iff₀ hXM_pos, mul_div_assoc']
      exact (div_lt_one (pow_pos hNq_pos M)).mpr hterm |>.trans_le hU1
    have hw0 : W (primeProductNorm p U / (X / N_q ^ M)) = 0 := by
      by_contra hne
      exact not_le_of_gt hgt (hb _ hne)
    dsimp only
    rw [hw0, mul_zero, mul_zero, zero_mul]
  rw [hrem0, mul_zero, add_zero]

omit [DecidableEq ι] in
/-- Every prime ideal in `O` has `absNorm ≥ 2`, so `(‖ringComplex (p q)‖ ^ 2) ^ (-1/2 : ℝ) ≤ 3/4`
and `∑ k ∈ Finset.range M, (N_q ^ k) ^ (-1/2 : ℝ) ≤ 4`. -/
lemma prime_norm_rpow_neg_half_sum_le_four (hp_local : ∀ i, p i ≠ 0) (q : ι) (M : ℕ) :
    let N_q := ‖ringComplex (p q)‖ ^ 2
    2 ≤ N_q ∧ (∑ k ∈ Finset.range M, (N_q ^ (-1 / 2 : ℝ)) ^ k) ≤ 4 := by
  intro N_q
  have hpI : Prime (Ideal.span {p q}) :=
    Ideal.prime_of_isPrime (Ideal.span_singleton_eq_bot.not.mpr (hp_local q)) inferInstance
  have h2nat : 2 ≤ (Ideal.span {p q}).absNorm :=
    HeckeIdealSeries.prime_norm_two_le ⟨Ideal.span {p q}, hpI⟩
  have h2 : 2 ≤ N_q := by
    dsimp [N_q]
    rw [ringComplex_norm_sq_eq_absNorm_span]
    exact_mod_cast h2nat
  refine ⟨h2, ?_⟩
  have hNq0 : 0 < N_q := by linarith
  let r := N_q ^ (-1 / 2 : ℝ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg hNq0.le _
  have hr_34 : r ≤ 3 / 4 := by
    have hsq : r ^ 2 ≤ (3 / 4 : ℝ) ^ 2 := by
      have hr2 : r ^ 2 = N_q ^ (-1 : ℝ) := by
        dsimp [r]; rw [← Real.rpow_natCast, ← Real.rpow_mul hNq0.le]; norm_num
      rw [hr2, Real.rpow_neg_one]
      rw [inv_le_comm₀ hNq0 (by positivity)]
      linarith
    nlinarith [sq_nonneg (r - 3 / 4)]
  -- Bound finite geometric sum `∑_{k < M} r^k ≤ ∑_{k < M} (3/4)^k = 4 * (1 - (3/4)^M) ≤ 4`.
  calc
    (∑ k ∈ Finset.range M, r ^ k)
      ≤ ∑ k ∈ Finset.range M, (3 / 4 : ℝ) ^ k :=
        Finset.sum_le_sum (fun k _ => pow_le_pow_left₀ hr0 hr_34 k)
    _ = ((3 / 4 : ℝ) ^ M - 1) / (3 / 4 - 1) := geom_sum_eq (by norm_num) M
    _ = 4 * (1 - (3 / 4 : ℝ) ^ M) := by ring
    _ ≤ 4 := by
        have hp0 : 0 ≤ (3 / 4 : ℝ) ^ M := by positivity
        linarith

/-- **Multi-prime `L^2` unpuncturing theorem:**
If for all `0 < X' ≤ X`, the unpunctured `L^2` sum satisfies
`∑ w ∈ S_w, (X')⁻¹ * ‖inputConjugateRow p χ pool Ψ₀ 1 1 1 (fun U => W (primeProductNorm p U / X')) w‖^2 ≤ B_sup`,
then for ANY finite puncture set `P_punc` (`p q ∣ m'` removed),
`∑ w ∈ S_w, X⁻¹ * ‖inputConjugateRow p χ (pool \ P_punc) Ψ₀ 1 1 1 (...) w‖^2 ≤ 16 ^ P_punc.card * B_sup`! -/
theorem inputConjugateRow_unpuncture_l2_le
    (hp_local : ∀ i, p i ≠ 0)
    (pool P_punc : Finset ι) (Ψ₀ : O →* ℂ) (hΨ1 : ∀ u, ‖Ψ₀ u‖ ≤ 1)
    (W : ℝ → ℂ) {b_hi : ℝ} (_hb_pos : 0 ≤ b_hi) (hb : ∀ y, W y ≠ 0 → y ≤ b_hi)
    (S_w : Finset O) {B_sup : ℝ} (hB : 0 ≤ B_sup) {X : ℝ} (hX : 0 < X)
    (hunpunc : ∀ X' : ℝ, 0 < X' → X' ≤ X →
      (∑ w ∈ S_w, (X')⁻¹ * ‖inputConjugateRow p
          (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
          pool Ψ₀ 1 1 1 (fun U => W (primeProductNorm p U / X')) w‖ ^ 2) ≤ B_sup) :
    (∑ w ∈ S_w, X⁻¹ * ‖inputConjugateRow p
        (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
        (pool \ P_punc) Ψ₀ 1 1 1 (fun U => W (primeProductNorm p U / X)) w‖ ^ 2) ≤
      (16 : ℝ) ^ P_punc.card * B_sup := by
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  revert X hunpunc
  induction P_punc using Finset.induction_on with
  | empty =>
    intro X hX hunpunc
    simp only [Finset.sdiff_empty, Finset.card_empty, pow_zero, one_mul]
    exact hunpunc X hX le_rfl
  | @insert q P' hqP' ih =>
    intro X hX hunpunc
    have hcard_ins : (insert q P').card = P'.card + 1 := Finset.card_insert_of_notMem hqP'
    rw [hcard_ins, pow_succ']
    by_cases hq_in : q ∈ pool \ P'
    · have hsdiff : pool \ insert q P' = (pool \ P').erase q := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
      rw [hsdiff]
      let N_q := ‖ringComplex (p q)‖ ^ 2
      obtain ⟨hNq2, _⟩ := prime_norm_rpow_neg_half_sum_le_four p hp_local q 0
      have hNq_pos : 0 < N_q := by linarith
      -- Pick M large enough that b_hi * X < 2 ^ M ≤ N_q ^ M.
      let M : ℕ := ⌈b_hi * X⌉₊ + 1
      have hterm : b_hi * X < N_q ^ M := by
        calc
          b_hi * X ≤ (⌈b_hi * X⌉₊ : ℝ) := Nat.le_ceil _
          _ < (M : ℝ) := by dsimp [M]; push_cast; linarith
          _ ≤ (2 : ℝ) ^ M := by exact_mod_cast Nat.lt_two_pow_self.le
          _ ≤ N_q ^ M := pow_le_pow_left₀ (by norm_num) hNq2 M
      obtain ⟨_, hgeom4⟩ := prime_norm_rpow_neg_half_sum_le_four p hp_local q M
      let r := N_q ^ (-1 / 2 : ℝ)
      have hr_pos : 0 < r := Real.rpow_pos_of_pos hNq_pos _
      -- Pointwise Cauchy-Schwarz on `X⁻¹ * ‖F_0(X, w)‖^2` with weights `r ^ k`.
      have hpt (w : O) :
          X⁻¹ * ‖inputConjugateRow p χ ((pool \ P').erase q) Ψ₀ 1 1 1
              (fun U => W (primeProductNorm p U / X)) w‖ ^ 2 ≤
            (∑ k ∈ Finset.range M, r ^ k) *
              ∑ k ∈ Finset.range M, r ^ k *
                ((X / N_q ^ k)⁻¹ * ‖inputConjugateRow p χ (pool \ P') Ψ₀ 1 1 1
                  (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w‖ ^ 2) := by
        rw [inputConjugateRow_erase_prime_geom p hg hp_local (pool \ P') hq_in Ψ₀ 1 W hb hX w M hterm]
        let α := Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)
        have hα1 : ‖α‖ ≤ 1 := by
          dsimp [α]
          have h1 : ‖Ψ₀ (p q)‖ ≤ 1 := hΨ1 _
          have h2 : ‖primeCoprimeMask p {q} 1‖ ≤ 1 := by
            by_cases hd : p q ∣ 1 <;> simp [primeCoprimeMask, hd]
          have h3 : ‖star (primeSubsetRow p χ {q} w)‖ ≤ 1 := by
            rw [norm_star]; exact primeSubsetRow_norm_le_one p χ {q} w
          calc ‖Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)‖
              = ‖Ψ₀ (p q)‖ * ‖primeCoprimeMask p {q} 1‖ * ‖star (primeSubsetRow p χ {q} w)‖ := by
                rw [norm_mul, norm_mul]
            _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3
                (norm_nonneg _) (by norm_num)
            _ = 1 := by norm_num
        let g_k : ℕ → ℝ := fun k =>
          ‖inputConjugateRow p χ (pool \ P') Ψ₀ 1 1 1
            (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w‖
        have htri :
            ‖∑ k ∈ Finset.range M, α ^ k * inputConjugateRow p χ (pool \ P') Ψ₀ 1 1 1
                (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w‖ ≤
              ∑ k ∈ Finset.range M, (r ^ k) ^ (1 / 2 : ℝ) *
                ((r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g_k k)) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
          rw [norm_mul, norm_pow]
          have hαk : ‖α‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hα1
          have hr_id : (r ^ k) ^ (1 / 2 : ℝ) * ((r ^ k) ^ (1 / 2 : ℝ) * (N_q ^ k) ^ (1 / 2 : ℝ)) = 1 := by
            have h1 : (r ^ k) ^ (1 / 2 : ℝ) * (r ^ k) ^ (1 / 2 : ℝ) = r ^ k := by
              rw [← Real.rpow_add (pow_pos hr_pos k)]; norm_num
            have h2 : r ^ k * (N_q ^ k) ^ (1 / 2 : ℝ) = 1 := by
              dsimp [r]
              rw [← Real.rpow_natCast, ← Real.rpow_mul hNq_pos.le,
                ← Real.rpow_natCast N_q k, ← Real.rpow_mul hNq_pos.le, ← Real.rpow_add hNq_pos]
              have : (-1 / 2 : ℝ) * (k : ℝ) + (k : ℝ) * (1 / 2 : ℝ) = 0 := by ring
              rw [this, Real.rpow_zero]
            calc (r ^ k) ^ (1 / 2 : ℝ) * ((r ^ k) ^ (1 / 2 : ℝ) * (N_q ^ k) ^ (1 / 2 : ℝ))
                = ((r ^ k) ^ (1 / 2 : ℝ) * (r ^ k) ^ (1 / 2 : ℝ)) * (N_q ^ k) ^ (1 / 2 : ℝ) := by ring
              _ = 1 := by rw [h1, h2]
          calc ‖α‖ ^ k * g_k k ≤ 1 * g_k k := mul_le_mul_of_nonneg_right hαk (norm_nonneg _)
            _ = ((r ^ k) ^ (1 / 2 : ℝ) * ((r ^ k) ^ (1 / 2 : ℝ) * (N_q ^ k) ^ (1 / 2 : ℝ))) * g_k k := by
                rw [hr_id]
            _ = _ := by ring
        have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range M)
          (fun k => (r ^ k) ^ (1 / 2 : ℝ))
          (fun k => (r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g_k k))
        have hsq := pow_le_pow_left₀ (norm_nonneg _) (htri.trans hcs) 2
        rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
          Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hsq
        have hsimp1 : (∑ k ∈ Finset.range M, ((r ^ k) ^ (1 / 2 : ℝ)) ^ 2) =
            ∑ k ∈ Finset.range M, r ^ k := by
          apply Finset.sum_congr rfl; intro k _
          rw [← Real.rpow_natCast ((r ^ k) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul (pow_nonneg hr_pos.le k)]
          norm_num
        have hsimp2 (k : ℕ) :
            X⁻¹ * ((r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g_k k)) ^ 2 =
              r ^ k * ((X / N_q ^ k)⁻¹ * g_k k ^ 2) := by
          have h1 : ((r ^ k) ^ (1 / 2 : ℝ)) ^ 2 = r ^ k := by
            rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (pow_nonneg hr_pos.le k)]; norm_num
          have h2 : ((N_q ^ k) ^ (1 / 2 : ℝ)) ^ 2 = N_q ^ k := by
            rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (pow_nonneg hNq_pos.le k)]; norm_num
          rw [mul_pow, mul_pow, h1, h2, inv_div]
          ring
        calc
          X⁻¹ * ‖∑ k ∈ Finset.range M, α ^ k * inputConjugateRow p χ (pool \ P') Ψ₀ 1 1 1
              (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w‖ ^ 2
            ≤ X⁻¹ * ((∑ k ∈ Finset.range M, r ^ k) *
                ∑ k ∈ Finset.range M, ((r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g_k k)) ^ 2) := by
              rw [← hsimp1]
              exact mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr hX.le)
          _ = (∑ k ∈ Finset.range M, r ^ k) *
                ∑ k ∈ Finset.range M, X⁻¹ * ((r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g_k k)) ^ 2 := by
              rw [← mul_assoc, mul_comm X⁻¹, mul_assoc, Finset.mul_sum]
          _ = _ := by simp_rw [hsimp2]; rfl
      calc
        (∑ w ∈ S_w, X⁻¹ * ‖inputConjugateRow p χ ((pool \ P').erase q) Ψ₀ 1 1 1
            (fun U => W (primeProductNorm p U / X)) w‖ ^ 2)
          ≤ ∑ w ∈ S_w, (∑ k ∈ Finset.range M, r ^ k) *
              ∑ k ∈ Finset.range M, r ^ k *
                ((X / N_q ^ k)⁻¹ * ‖inputConjugateRow p χ (pool \ P') Ψ₀ 1 1 1
                  (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w‖ ^ 2) :=
            Finset.sum_le_sum (fun w _ => hpt w)
        _ = (∑ k ∈ Finset.range M, r ^ k) *
              ∑ k ∈ Finset.range M, r ^ k *
                ∑ w ∈ S_w, (X / N_q ^ k)⁻¹ * ‖inputConjugateRow p χ (pool \ P') Ψ₀ 1 1 1
                  (fun U => W (primeProductNorm p U / (X / N_q ^ k))) w‖ ^ 2 := by
            rw [← Finset.mul_sum, Finset.sum_comm]
            congr 1
            apply Finset.sum_congr rfl
            intro k _
            rw [← Finset.mul_sum]
        _ ≤ 4 * ∑ k ∈ Finset.range M, r ^ k * ((16 : ℝ) ^ P'.card * B_sup) := by
            apply mul_le_mul hgeom4 _ (Finset.sum_nonneg (fun k _ => mul_nonneg (pow_nonneg hr_pos.le k)
              (Finset.sum_nonneg (fun _ _ => mul_nonneg (inv_nonneg.mpr (div_pos hX (pow_pos hNq_pos k)).le)
                (sq_nonneg _))))) (by norm_num)
            apply Finset.sum_le_sum
            intro k _
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr_pos.le k)
            apply ih (div_pos hX (pow_pos hNq_pos k))
            intro X'' hX'' hle''
            exact hunpunc X'' hX'' (hle''.trans (div_le_self hX.le (one_le_pow₀ (by linarith))))
        _ = 4 * (∑ k ∈ Finset.range M, r ^ k) * ((16 : ℝ) ^ P'.card * B_sup) := by
            rw [← Finset.sum_mul]; ring
        _ ≤ 4 * 4 * ((16 : ℝ) ^ P'.card * B_sup) := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgeom4 (by norm_num))
              (mul_nonneg (by positivity) hB)
        _ = 16 * (16 : ℝ) ^ P'.card * B_sup := by ring
    · have hsdiff : pool \ insert q P' = pool \ P' := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        exact ⟨fun ⟨hp_x, hn⟩ => ⟨hp_x, fun h => hn (Or.inr h)⟩,
          fun ⟨hp_x, hn⟩ => ⟨hp_x, fun h => h.elim
            (fun heq => by subst heq; exact hq_in (Finset.mem_sdiff.mpr ⟨hp_x, hn⟩)) hn⟩⟩
      rw [hsdiff]
      calc
        (∑ w ∈ S_w, X⁻¹ * ‖inputConjugateRow p χ (pool \ P') Ψ₀ 1 1 1
            (fun U => W (primeProductNorm p U / X)) w‖ ^ 2)
          ≤ (16 : ℝ) ^ P'.card * B_sup := ih hX hunpunc
        _ ≤ 16 * (16 : ℝ) ^ P'.card * B_sup := by
            have hpos : 0 ≤ (16 : ℝ) ^ P'.card * B_sup := mul_nonneg (by positivity) hB
            linarith

/-- Puncture-to-sdiff identity and divisor bound `16 ^ P_punc.card ≤ |idealDivisors (span {m'})| ^ 4`:
replacing `primeCoprimeMask p U m'` on `pool` equals restricting `pool` to `pool \ P_punc` where
`P_punc = pool.filter (fun q => p q ∣ m')`, and `16 ^ P_punc.card ≤ ((idealDivisors (Ideal.span {m'})).card : ℝ) ^ 4`
for every `m' ≠ 0`. -/
theorem inputConjugateRow_puncture_eq_sdiff_and_card_le
    (hp_local : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (pool : Finset ι) (Ψ₀ : O →* ℂ) {m' : O} (hm' : m' ≠ 0) (H : Finset ι → ℂ) (w : O) :
    let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
    let P_punc := pool.filter (fun q => p q ∣ m')
    inputConjugateRow p χ pool Ψ₀ m' 1 1 H w =
      inputConjugateRow p χ (pool \ P_punc) Ψ₀ 1 1 1 H w ∧
      (16 : ℝ) ^ P_punc.card ≤ ((idealDivisors (Ideal.span {m'})).card : ℝ) ^ 4 := by
  intro χ P_punc
  constructor
  · unfold inputConjugateRow supportConjugateSum secondInputCoefficient
    have hsub : (pool \ P_punc).powerset ⊆ pool.powerset :=
      Finset.powerset_mono.mpr Finset.sdiff_subset
    have h1 :
        (∑ U ∈ pool.powerset,
          supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U m' *
            primeSubsetRow p χ U 1 ^ 4 * primeSubsetRow p χ U 1 * H U) *
            star (primeSubsetRow p χ U w)) =
        ∑ U ∈ (pool \ P_punc).powerset,
          supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U m' *
            primeSubsetRow p χ U 1 ^ 4 * primeSubsetRow p χ U 1 * H U) *
            star (primeSubsetRow p χ U w) := by
      symm
      apply Finset.sum_subset hsub
      intro U hUp hnot
      have hU_pool : U ⊆ pool := Finset.mem_powerset.mp hUp
      have hnd : ¬ (U ⊆ pool \ P_punc) := fun h => hnot (Finset.mem_powerset.mpr h)
      obtain ⟨q, hqU, hqnot⟩ := Finset.not_subset.mp hnd
      have hqP : q ∈ P_punc := by
        by_contra hc
        exact hqnot (Finset.mem_sdiff.mpr ⟨hU_pool hqU, hc⟩)
      have hdvd : p q ∣ m' := (Finset.mem_filter.mp hqP).2
      have hm0 : primeCoprimeMask p U m' = 0 := by
        unfold primeCoprimeMask
        apply Finset.prod_eq_zero hqU
        rw [if_pos hdvd]; ring
      rw [hm0]; ring
    rw [h1]
    apply Finset.sum_congr rfl
    intro U hU
    have hm1 : primeCoprimeMask p U m' = primeCoprimeMask p U 1 := by
      unfold primeCoprimeMask
      apply Finset.prod_congr rfl
      intro q hqU
      have hq_sdiff : q ∈ pool \ P_punc := (Finset.mem_powerset.mp hU) hqU
      have hndvd : ¬ (p q ∣ m') := fun hd =>
        (Finset.mem_sdiff.mp hq_sdiff).2 (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hq_sdiff).1, hd⟩)
      have hndvd1 : ¬ (p q ∣ 1) := fun hd =>
        (inferInstance : (Ideal.span {p q}).IsPrime).ne_top
          ((Ideal.eq_top_iff_one _).mpr (Ideal.mem_span_singleton.mpr hd))
      rw [if_neg hndvd, if_neg hndvd1]
    rw [hm1]
  · -- Inject `P_punc.powerset` into `idealDivisors (Ideal.span {m'})` via `E ↦ ∏ q ∈ E, Ideal.span {p q}`.
    let Im : Ideal O := Ideal.span {m'}
    have hIm0 : Im ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hm'
    have hprod_inj := span_finset_prod_injective p hp_local hcop
    let φ : Finset ι → Ideal O := fun E => ∏ q ∈ E, Ideal.span {p q}
    have hmaps : ∀ E ∈ P_punc.powerset, φ E ∈ idealDivisors Im := by
      intro E hE
      have hEP : E ⊆ P_punc := Finset.mem_powerset.mp hE
      rw [mem_idealDivisors hIm0]
      exact Finset.prod_dvd_of_coprime (fun i _ j _ hij => hcop hij)
        (fun q hq => Ideal.dvd_iff_le.mpr
          (Ideal.span_singleton_le_span_singleton.mpr (Finset.mem_filter.mp (hEP hq)).2))
    have hcard : P_punc.powerset.card ≤ (idealDivisors Im).card :=
      Finset.card_le_card_of_injOn φ hmaps (fun _ _ _ _ he => hprod_inj he)
    rw [Finset.card_powerset] at hcard
    have h2 : (2 : ℝ) ^ P_punc.card ≤ ((idealDivisors Im).card : ℝ) := by exact_mod_cast hcard
    calc
      (16 : ℝ) ^ P_punc.card = ((2 : ℝ) ^ P_punc.card) ^ 4 := by
          rw [← pow_mul, mul_comm, pow_mul]; norm_num
      _ ≤ ((idealDivisors Im).card : ℝ) ^ 4 := pow_le_pow_left₀ (by positivity) h2 4

/-- Single-prime step on `inputConjugateRow` with an invariant factor `Φ`: when
`∀ U ⊆ pool.erase q, Φ (insert q U) = Φ U`, erasing `q` shifts the column scale by `N_q`. -/
lemma inputConjugateRow_split_prime_invariant
    (pool : Finset ι) {q : ι} (hq : q ∈ pool)
    (Ψ₀ : O →* ℂ) (m' : O) (Φ : Finset ι → ℂ)
    (hΦ : ∀ U ∈ (pool.erase q).powerset, Φ (insert q U) = Φ U)
    (W : ℝ → ℂ) (X : ℝ) (w : O) :
    let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
    let N_q := ‖ringComplex (p q)‖ ^ 2
    let α := Ψ₀ (p q) * primeCoprimeMask p {q} m' * star (primeSubsetRow p χ {q} w)
    inputConjugateRow p χ (pool.erase q) Ψ₀ m' 1 1
        (fun U => Φ U * W (primeProductNorm p U / X)) w =
      inputConjugateRow p χ pool Ψ₀ m' 1 1
        (fun U => Φ U * W (primeProductNorm p U / X)) w +
      α * inputConjugateRow p χ (pool.erase q) Ψ₀ m' 1 1
        (fun U => Φ U * W (primeProductNorm p U / (X / N_q))) w := by
  intro χ N_q α
  have hins : insert q (pool.erase q) = pool := Finset.insert_erase hq
  have hnot : q ∉ pool.erase q := fun h => (Finset.mem_erase.mp h).1 rfl
  have h1 (T : Finset ι) : primeSubsetRow p χ T 1 = 1 := by simp [primeSubsetRow]
  have hpool_sum : ∀ f : Finset ι → ℂ,
      (∑ S ∈ pool.powerset, f S) =
        (∑ S ∈ (pool.erase q).powerset, f S) +
          ∑ S ∈ (pool.erase q).powerset.image (insert q), f S := by
    intro f
    conv_lhs => rw [← hins, Finset.powerset_insert]
    exact Finset.sum_union (Finset.disjoint_iff_ne.mpr (fun S hS T hT heq => by
      obtain ⟨U, _hU, rfl⟩ := Finset.mem_image.mp hT
      exact hnot ((Finset.mem_powerset.mp hS) (heq ▸ Finset.mem_insert_self q U))))
  unfold inputConjugateRow supportConjugateSum secondInputCoefficient
  simp only [h1, one_pow, mul_one]
  rw [hpool_sum, Finset.sum_image (fun U₁ hU₁ U₂ hU₂ heq => by
    have hq1 : q ∉ U₁ := fun h => hnot ((Finset.mem_powerset.mp hU₁) h)
    have hq2 : q ∉ U₂ := fun h => hnot ((Finset.mem_powerset.mp hU₂) h)
    exact (Finset.erase_insert hq1).symm.trans ((congrArg (fun S => S.erase q) heq).trans
      (Finset.erase_insert hq2)))]
  have hsecond :
      (∑ U ∈ (pool.erase q).powerset,
        supportMobius (insert q U) * (Ψ₀ (∏ i ∈ insert q U, p i) *
          primeCoprimeMask p (insert q U) m' *
          (Φ (insert q U) * W (primeProductNorm p (insert q U) / X))) *
          star (primeSubsetRow p χ (insert q U) w)) =
      -(α * ∑ U ∈ (pool.erase q).powerset,
        supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U m' *
          (Φ U * W (primeProductNorm p U / (X / N_q)))) * star (primeSubsetRow p χ U w)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro U hU
    have hqU : q ∉ U := fun h => hnot ((Finset.mem_powerset.mp hU) h)
    have hd : Disjoint {q} U := Finset.disjoint_singleton_left.mpr hqU
    have hinsU : insert q U = {q} ∪ U := (Finset.singleton_union q U).symm
    have hmob : supportMobius ({q} ∪ U) = -supportMobius U := by
      rw [supportMobius_union {q} U hd]; simp [supportMobius]
    have hprod : Ψ₀ (∏ i ∈ {q} ∪ U, p i) = Ψ₀ (p q) * Ψ₀ (∏ i ∈ U, p i) := by
      rw [Finset.prod_union hd, Finset.prod_singleton, map_mul]
    have hmask : primeCoprimeMask p ({q} ∪ U) m' =
        primeCoprimeMask p {q} m' * primeCoprimeMask p U m' := by
      unfold primeCoprimeMask; exact Finset.prod_union hd
    have hrow : star (primeSubsetRow p χ ({q} ∪ U) w) =
        star (primeSubsetRow p χ {q} w) * star (primeSubsetRow p χ U w) := by
      rw [primeSubsetRow_union p χ {q} U hd, star_mul, mul_comm]
    have hnorm : primeProductNorm p ({q} ∪ U) / X = primeProductNorm p U / (X / N_q) := by
      rw [primeProductNorm_union p {q} U hd]
      have hNq : primeProductNorm p {q} = N_q := by simp [primeProductNorm, N_q]
      rw [hNq, div_div_eq_mul_div, mul_comm]
    rw [hΦ U hU, hinsU, hmob, hprod, hmask, hrow, hnorm]
    dsimp [α]
    ring
  rw [hsecond]
  ring

/-- Single-prime `L^2` unpuncturing with a `q`-invariant factor `Φ`, incurring factor `16`. -/
lemma inputConjugateRow_erase_invariant_l2
    (hp_local : ∀ i, p i ≠ 0)
    (pool : Finset ι) {q : ι} (hq : q ∈ pool)
    (Ψ₀ : O →* ℂ) (hΨ1 : ∀ u, ‖Ψ₀ u‖ ≤ 1)
    (Φ : Finset ι → ℂ) (hΦ : ∀ U ∈ (pool.erase q).powerset, Φ (insert q U) = Φ U)
    (W : ℝ → ℂ) {b_hi : ℝ} (hb : ∀ y, W y ≠ 0 → y ≤ b_hi)
    (S_w : Finset O) {C_norm B : ℝ} (hC_pos : 0 < C_norm) (hB : 0 ≤ B) {X : ℝ} (hX : 0 < X)
    (hdom : ∀ X' : ℝ, 0 < X' → X' ≤ X →
      (∑ w ∈ S_w, (X' * C_norm)⁻¹ * ‖inputConjugateRow p
          (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
          pool Ψ₀ 1 1 1 (fun U => Φ U * W (primeProductNorm p U / X')) w‖ ^ 2) ≤ B) :
    (∑ w ∈ S_w, (X * C_norm)⁻¹ * ‖inputConjugateRow p
        (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
        (pool.erase q) Ψ₀ 1 1 1 (fun U => Φ U * W (primeProductNorm p U / X)) w‖ ^ 2) ≤ 16 * B := by
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  let N_q := ‖ringComplex (p q)‖ ^ 2
  obtain ⟨hNq2, _⟩ := prime_norm_rpow_neg_half_sum_le_four p hp_local q 0
  have hNq_pos : 0 < N_q := by linarith
  let M : ℕ := ⌈b_hi * X⌉₊ + 1
  have hterm : b_hi * X < N_q ^ M := by
    calc b_hi * X ≤ (⌈b_hi * X⌉₊ : ℝ) := Nat.le_ceil _
      _ < (M : ℝ) := by dsimp [M]; push_cast; linarith
      _ ≤ (2 : ℝ) ^ M := by exact_mod_cast Nat.lt_two_pow_self.le
      _ ≤ N_q ^ M := pow_le_pow_left₀ (by norm_num) hNq2 M
  obtain ⟨_, hgeom4⟩ := prime_norm_rpow_neg_half_sum_le_four p hp_local q M
  let r := N_q ^ (-1 / 2 : ℝ)
  have hr_pos : 0 < r := Real.rpow_pos_of_pos hNq_pos _
  have hgeom_id (w : O) :
      inputConjugateRow p χ (pool.erase q) Ψ₀ 1 1 1
          (fun U => Φ U * W (primeProductNorm p U / X)) w =
        ∑ k ∈ Finset.range M,
          (Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)) ^ k *
            inputConjugateRow p χ pool Ψ₀ 1 1 1
              (fun U => Φ U * W (primeProductNorm p U / (X / N_q ^ k))) w := by
    let α := Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)
    have hrec : ∀ K : ℕ,
        inputConjugateRow p χ (pool.erase q) Ψ₀ 1 1 1
            (fun U => Φ U * W (primeProductNorm p U / X)) w =
          (∑ k ∈ Finset.range K,
            α ^ k * inputConjugateRow p χ pool Ψ₀ 1 1 1
              (fun U => Φ U * W (primeProductNorm p U / (X / N_q ^ k))) w) +
          α ^ K * inputConjugateRow p χ (pool.erase q) Ψ₀ 1 1 1
            (fun U => Φ U * W (primeProductNorm p U / (X / N_q ^ K))) w := by
      intro K
      induction K with
      | zero => simp
      | succ K ih =>
        rw [ih, Finset.sum_range_succ,
          inputConjugateRow_split_prime_invariant p hg pool hq Ψ₀ 1 Φ hΦ W (X / N_q ^ K) w]
        have hdiv : (X / N_q ^ K) / N_q = X / N_q ^ (K + 1) := by rw [div_div, ← pow_succ]
        dsimp only [N_q] at hdiv ⊢
        simp_rw [hdiv]
        ring
    rw [hrec M]
    have hrem0 : inputConjugateRow p χ (pool.erase q) Ψ₀ 1 1 1
        (fun U => Φ U * W (primeProductNorm p U / (X / N_q ^ M))) w = 0 := by
      unfold inputConjugateRow supportConjugateSum secondInputCoefficient
      apply Finset.sum_eq_zero
      intro U _
      have hU1 : 1 ≤ primeProductNorm p U := primeProductNorm_ge_one p hp_local U
      have hXM_pos : 0 < X / N_q ^ M := div_pos hX (pow_pos hNq_pos M)
      have hgt : b_hi < primeProductNorm p U / (X / N_q ^ M) := by
        rw [lt_div_iff₀ hXM_pos, mul_div_assoc']
        exact (div_lt_one (pow_pos hNq_pos M)).mpr hterm |>.trans_le hU1
      have hw0 : W (primeProductNorm p U / (X / N_q ^ M)) = 0 := by
        by_contra hne; exact not_le_of_gt hgt (hb _ hne)
      dsimp only
      rw [hw0]
      ring
    rw [hrem0, mul_zero, add_zero]
  have hpt (w : O) :
      (X * C_norm)⁻¹ * ‖inputConjugateRow p χ (pool.erase q) Ψ₀ 1 1 1
          (fun U => Φ U * W (primeProductNorm p U / X)) w‖ ^ 2 ≤
        (∑ k ∈ Finset.range M, r ^ k) *
          ∑ k ∈ Finset.range M, r ^ k *
            (((X / N_q ^ k) * C_norm)⁻¹ * ‖inputConjugateRow p χ pool Ψ₀ 1 1 1
              (fun U => Φ U * W (primeProductNorm p U / (X / N_q ^ k))) w‖ ^ 2) := by
    rw [hgeom_id w]
    let α := Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)
    have hα1 : ‖α‖ ≤ 1 := by
      dsimp [α]
      have h1 : ‖Ψ₀ (p q)‖ ≤ 1 := hΨ1 _
      have h2 : ‖primeCoprimeMask p {q} 1‖ ≤ 1 := by
        by_cases hd : p q ∣ 1 <;> simp [primeCoprimeMask, hd]
      have h3 : ‖star (primeSubsetRow p χ {q} w)‖ ≤ 1 := by
        rw [norm_star]; exact primeSubsetRow_norm_le_one p χ {q} w
      calc ‖Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)‖
          = ‖Ψ₀ (p q)‖ * ‖primeCoprimeMask p {q} 1‖ * ‖star (primeSubsetRow p χ {q} w)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3
            (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    let g_k : ℕ → ℝ := fun k =>
      ‖inputConjugateRow p χ pool Ψ₀ 1 1 1
        (fun U => Φ U * W (primeProductNorm p U / (X / N_q ^ k))) w‖
    have htri :
        ‖∑ k ∈ Finset.range M, α ^ k * inputConjugateRow p χ pool Ψ₀ 1 1 1
            (fun U => Φ U * W (primeProductNorm p U / (X / N_q ^ k))) w‖ ≤
          ∑ k ∈ Finset.range M, (r ^ k) ^ (1 / 2 : ℝ) *
            ((r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g_k k)) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
      rw [norm_mul, norm_pow]
      have hαk : ‖α‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hα1
      have hr_id : (r ^ k) ^ (1 / 2 : ℝ) * ((r ^ k) ^ (1 / 2 : ℝ) * (N_q ^ k) ^ (1 / 2 : ℝ)) = 1 := by
        have h1 : (r ^ k) ^ (1 / 2 : ℝ) * (r ^ k) ^ (1 / 2 : ℝ) = r ^ k := by
          rw [← Real.rpow_add (pow_pos hr_pos k)]; norm_num
        have h2 : r ^ k * (N_q ^ k) ^ (1 / 2 : ℝ) = 1 := by
          dsimp [r]
          rw [← Real.rpow_natCast, ← Real.rpow_mul hNq_pos.le,
            ← Real.rpow_natCast N_q k, ← Real.rpow_mul hNq_pos.le, ← Real.rpow_add hNq_pos]
          have : (-1 / 2 : ℝ) * (k : ℝ) + (k : ℝ) * (1 / 2 : ℝ) = 0 := by ring
          rw [this, Real.rpow_zero]
        calc (r ^ k) ^ (1 / 2 : ℝ) * ((r ^ k) ^ (1 / 2 : ℝ) * (N_q ^ k) ^ (1 / 2 : ℝ))
            = ((r ^ k) ^ (1 / 2 : ℝ) * (r ^ k) ^ (1 / 2 : ℝ)) * (N_q ^ k) ^ (1 / 2 : ℝ) := by ring
          _ = 1 := by rw [h1, h2]
      calc ‖α‖ ^ k * g_k k ≤ 1 * g_k k := mul_le_mul_of_nonneg_right hαk (norm_nonneg _)
        _ = ((r ^ k) ^ (1 / 2 : ℝ) * ((r ^ k) ^ (1 / 2 : ℝ) * (N_q ^ k) ^ (1 / 2 : ℝ))) * g_k k := by
            rw [hr_id]
        _ = _ := by ring
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range M)
      (fun k => (r ^ k) ^ (1 / 2 : ℝ))
      (fun k => (r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g_k k))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (htri.trans hcs) 2
    rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
      Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hsq
    have hsimp1 : (∑ k ∈ Finset.range M, ((r ^ k) ^ (1 / 2 : ℝ)) ^ 2) =
        ∑ k ∈ Finset.range M, r ^ k := by
      apply Finset.sum_congr rfl; intro k _
      rw [← Real.rpow_natCast ((r ^ k) ^ (1 / 2 : ℝ)) 2, ← Real.rpow_mul (pow_nonneg hr_pos.le k)]
      norm_num
    have hsimp2 (k : ℕ) :
        (X * C_norm)⁻¹ * ((r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g_k k)) ^ 2 =
          r ^ k * (((X / N_q ^ k) * C_norm)⁻¹ * g_k k ^ 2) := by
      have h1 : ((r ^ k) ^ (1 / 2 : ℝ)) ^ 2 = r ^ k := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (pow_nonneg hr_pos.le k)]; norm_num
      have h2 : ((N_q ^ k) ^ (1 / 2 : ℝ)) ^ 2 = N_q ^ k := by
        rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (pow_nonneg hNq_pos.le k)]; norm_num
      rw [mul_pow, mul_pow, h1, h2]
      field_simp [hX.ne', hC_pos.ne', (pow_pos hNq_pos k).ne']
    calc
      (X * C_norm)⁻¹ * ‖∑ k ∈ Finset.range M, α ^ k * inputConjugateRow p χ pool Ψ₀ 1 1 1
          (fun U => Φ U * W (primeProductNorm p U / (X / N_q ^ k))) w‖ ^ 2
        ≤ (X * C_norm)⁻¹ * ((∑ k ∈ Finset.range M, r ^ k) *
            ∑ k ∈ Finset.range M, ((r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g_k k)) ^ 2) := by
          rw [← hsimp1]
          exact mul_le_mul_of_nonneg_left hsq (inv_nonneg.mpr (mul_pos hX hC_pos).le)
      _ = (∑ k ∈ Finset.range M, r ^ k) *
            ∑ k ∈ Finset.range M, (X * C_norm)⁻¹ *
              ((r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g_k k)) ^ 2 := by
          rw [← mul_assoc, mul_comm (X * C_norm)⁻¹, mul_assoc, Finset.mul_sum]
      _ = _ := by simp_rw [hsimp2]; rfl
  calc
    (∑ w ∈ S_w, (X * C_norm)⁻¹ * ‖inputConjugateRow p χ (pool.erase q) Ψ₀ 1 1 1
        (fun U => Φ U * W (primeProductNorm p U / X)) w‖ ^ 2)
      ≤ ∑ w ∈ S_w, (∑ k ∈ Finset.range M, r ^ k) *
          ∑ k ∈ Finset.range M, r ^ k *
            (((X / N_q ^ k) * C_norm)⁻¹ * ‖inputConjugateRow p χ pool Ψ₀ 1 1 1
              (fun U => Φ U * W (primeProductNorm p U / (X / N_q ^ k))) w‖ ^ 2) :=
        Finset.sum_le_sum (fun w _ => hpt w)
    _ = (∑ k ∈ Finset.range M, r ^ k) *
          ∑ k ∈ Finset.range M, r ^ k *
            ∑ w ∈ S_w, ((X / N_q ^ k) * C_norm)⁻¹ * ‖inputConjugateRow p χ pool Ψ₀ 1 1 1
              (fun U => Φ U * W (primeProductNorm p U / (X / N_q ^ k))) w‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1; apply Finset.sum_congr rfl; intro k _; rw [← Finset.mul_sum]
    _ ≤ 4 * ∑ k ∈ Finset.range M, r ^ k * B := by
        apply mul_le_mul hgeom4 _ (Finset.sum_nonneg (fun k _ => mul_nonneg (pow_nonneg hr_pos.le k)
          (Finset.sum_nonneg (fun _ _ => mul_nonneg
            (inv_nonneg.mpr (mul_pos (div_pos hX (pow_pos hNq_pos k)) hC_pos).le)
            (sq_nonneg _))))) (by norm_num)
        apply Finset.sum_le_sum
        intro k _
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr_pos.le k)
        exact hdom (X / N_q ^ k) (div_pos hX (pow_pos hNq_pos k))
          (div_le_self hX.le (one_le_pow₀ (by linarith)))
    _ = 4 * (∑ k ∈ Finset.range M, r ^ k) * B := by rw [← Finset.sum_mul]; ring
    _ ≤ 4 * 4 * B := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgeom4 (by norm_num)) hB
    _ = 16 * B := by ring

/-- **Multi-prime `L^2` unpuncturing WITH `primeMark S_rem`:**
If for all subsets `S'' ⊆ S_rem` and all `0 < X' ≤ X / ∏_{i ∈ S_rem \ S''} Z_slot i`, the unpunctured
normalized `L^2` sum on `pool` is bounded by `B_sup`, then for ANY finite puncture set `P_punc`,
the punctured normalized `L^2` sum on `pool \ P_punc` at `(S_rem, X)` is bounded by
`1024 ^ P_punc.card * B_sup`! -/
theorem inputConjugateRow_markedRadial_unpuncture_l2_le
    {σ : Type*} [DecidableEq σ]
    (hp_local : ∀ i, p i ≠ 0)
    (pool P_punc : Finset ι) (Ψ₀ : O →* ℂ) (hΨ1 : ∀ u, ‖Ψ₀ u‖ ≤ 1)
    (S_rem : Finset σ) (lists : σ → Finset ι)
    (hdisj : (S_rem : Set σ).PairwiseDisjoint lists)
    (a : σ → ι → ℂ) (ha : ∀ i ∈ S_rem, ∀ q ∈ lists i, ‖a i q‖ ≤ 1)
    (Z_slot : σ → ℝ) (hZ1 : ∀ i ∈ S_rem, 1 ≤ Z_slot i)
    (hZ_norm : ∀ i ∈ S_rem, ∀ q ∈ lists i, Z_slot i ≤ ‖ringComplex (p q)‖ ^ 2)
    (W : ℝ → ℂ) {b_hi : ℝ} (hb : ∀ y, W y ≠ 0 → y ≤ b_hi)
    (S_w : Finset O) {B_sup : ℝ} (hB : 0 ≤ B_sup) {X : ℝ} (hX : 0 < X)
    (hunpunc : ∀ S'' : Finset σ, S'' ⊆ S_rem → ∀ X' : ℝ, 0 < X' →
      X' * (∏ i ∈ S_rem \ S'', Z_slot i) ≤ X →
      (∑ w ∈ S_w, (X' * ∏ i ∈ S'', Z_slot i)⁻¹ * ‖inputConjugateRow p
          (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
          pool Ψ₀ 1 1 1
          (fun U => InverseMoment.primeMark S'' lists a U * W (primeProductNorm p U / X')) w‖ ^ 2) ≤
        B_sup) :
    (∑ w ∈ S_w, (X * ∏ i ∈ S_rem, Z_slot i)⁻¹ * ‖inputConjugateRow p
        (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
        (pool \ P_punc) Ψ₀ 1 1 1
        (fun U => InverseMoment.primeMark S_rem lists a U * W (primeProductNorm p U / X)) w‖ ^ 2) ≤
      (1024 : ℝ) ^ P_punc.card * B_sup := by
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  -- Prove simultaneously for all `S' ⊆ S_rem` and `0 < X` by induction on `P_punc`.
  suffices hgen : ∀ S' : Finset σ, S' ⊆ S_rem → ∀ X₀ : ℝ, 0 < X₀ →
      X₀ * (∏ i ∈ S_rem \ S', Z_slot i) ≤ X →
      (∑ w ∈ S_w, (X₀ * ∏ i ∈ S', Z_slot i)⁻¹ * ‖inputConjugateRow p χ
          (pool \ P_punc) Ψ₀ 1 1 1
          (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / X₀)) w‖ ^ 2) ≤
        (1024 : ℝ) ^ P_punc.card * B_sup by
    exact hgen S_rem Finset.Subset.rfl X hX (by simp)
  induction P_punc using Finset.induction_on with
  | empty =>
    intro S' hS' X₀ hX₀ hX₀_le
    simp only [Finset.sdiff_empty, Finset.card_empty, pow_zero, one_mul]
    exact hunpunc S' hS' X₀ hX₀ hX₀_le
  | @insert q P' hqP' ih =>
    intro S' hS' X₀ hX₀ hX₀_le
    have hcard_ins : (insert q P').card = P'.card + 1 := Finset.card_insert_of_notMem hqP'
    rw [hcard_ins, pow_succ']
    have hC_norm : 0 < ∏ i ∈ S', Z_slot i :=
      Finset.prod_pos (fun i hi => zero_lt_one.trans_le (hZ1 i (hS' hi)))
    have hB' : 0 ≤ (1024 : ℝ) ^ P'.card * B_sup := mul_nonneg (by positivity) hB
    by_cases hq_in : q ∈ pool \ P'
    · have hsdiff : pool \ insert q P' = (pool \ P').erase q := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]; tauto
      rw [hsdiff]
      by_cases hex : ∃ i₀ ∈ S', q ∈ lists i₀
      · obtain ⟨i₀, hi₀, hq_i₀⟩ := hex
        let S₀ := S'.erase i₀
        have hS₀_sub : S₀ ⊆ S_rem := (Finset.erase_subset i₀ S').trans hS'
        have hC₀_pos : 0 < ∏ i ∈ S₀, Z_slot i :=
          Finset.prod_pos (fun i hi => zero_lt_one.trans_le (hZ1 i (hS₀_sub hi)))
        have hq_not_S₀ : ∀ i ∈ S₀, q ∉ lists i := by
          intro i hi hqi
          obtain ⟨hne, hiS'⟩ := Finset.mem_erase.mp hi
          exact Finset.disjoint_left.mp (hdisj (hS' hiS') (hS' hi₀) hne) hqi hq_i₀
        have hΦ_S₀ : ∀ U ∈ ((pool \ P').erase q).powerset,
            InverseMoment.primeMark S₀ lists a (insert q U) = InverseMoment.primeMark S₀ lists a U := by
          intro U _
          unfold InverseMoment.primeMark InverseMoment.primeSlot
          apply Finset.prod_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro r hr
          have hrq : r ≠ q := fun he => hq_not_S₀ i hi (he ▸ hr)
          simp [Finset.mem_insert, hrq]
        have hΦ_split : ∀ U ∈ ((pool \ P').erase q).powerset,
            InverseMoment.primeMark S' lists a (insert q U) =
              InverseMoment.primeMark S' lists a U +
                a i₀ q * InverseMoment.primeMark S₀ lists a U := by
          intro U hU
          have hqU : q ∉ U := fun h =>
            (Finset.mem_erase.mp ((Finset.mem_powerset.mp hU) h)).1 rfl
          have hins_S : insert i₀ S₀ = S' := Finset.insert_erase hi₀
          have hnot_i₀ : i₀ ∉ S₀ := Finset.notMem_erase i₀ S'
          conv_lhs => rw [← hins_S]; unfold InverseMoment.primeMark; rw [Finset.prod_insert hnot_i₀]
          conv_rhs => arg 1; rw [← hins_S]; unfold InverseMoment.primeMark; rw [Finset.prod_insert hnot_i₀]
          have hslot : InverseMoment.primeSlot (lists i₀) (a i₀) (insert q U) =
              InverseMoment.primeSlot (lists i₀) (a i₀) U + a i₀ q := by
            unfold InverseMoment.primeSlot
            have h1 : (∑ r ∈ lists i₀, if r ∈ insert q U then a i₀ r else 0) =
                (∑ r ∈ (lists i₀).erase q, if r ∈ insert q U then a i₀ r else 0) +
                  (if q ∈ insert q U then a i₀ q else 0) :=
              (Finset.add_sum_erase (lists i₀) _ hq_i₀).symm.trans (add_comm _ _)
            have h2 : (∑ r ∈ lists i₀, if r ∈ U then a i₀ r else 0) =
                (∑ r ∈ (lists i₀).erase q, if r ∈ U then a i₀ r else 0) +
                  (if q ∈ U then a i₀ q else 0) :=
              (Finset.add_sum_erase (lists i₀) _ hq_i₀).symm.trans (add_comm _ _)
            rw [h1, h2, if_pos (Finset.mem_insert_self q U), if_neg hqU, add_zero]
            congr 1
            apply Finset.sum_congr rfl
            intro r hr
            have hrq : r ≠ q := (Finset.mem_erase.mp hr).1
            simp [Finset.mem_insert, hrq]
          change InverseMoment.primeSlot (lists i₀) (a i₀) (insert q U) *
              InverseMoment.primeMark S₀ lists a (insert q U) =
            InverseMoment.primeSlot (lists i₀) (a i₀) U * InverseMoment.primeMark S₀ lists a U +
              a i₀ q * InverseMoment.primeMark S₀ lists a U
          rw [hslot, hΦ_S₀ U hU]
          ring
        -- Single-prime split with S₀ error term on Q_pool = pool \ P'.
        let Q_pool := pool \ P'
        let N_q := ‖ringComplex (p q)‖ ^ 2
        obtain ⟨hNq2, _⟩ := prime_norm_rpow_neg_half_sum_le_four p hp_local q 0
        have hNq_pos : 0 < N_q := by linarith
        have hZq : Z_slot i₀ ≤ N_q := hZ_norm i₀ (hS' hi₀) q hq_i₀
        have hZ1_i₀ : 1 ≤ Z_slot i₀ := hZ1 i₀ (hS' hi₀)
        let M : ℕ := ⌈b_hi * X₀⌉₊ + 1
        have hterm : b_hi * X₀ < N_q ^ M := by
          calc b_hi * X₀ ≤ (⌈b_hi * X₀⌉₊ : ℝ) := Nat.le_ceil _
            _ < (M : ℝ) := by dsimp [M]; push_cast; linarith
            _ ≤ (2 : ℝ) ^ M := by exact_mod_cast Nat.lt_two_pow_self.le
            _ ≤ N_q ^ M := pow_le_pow_left₀ (by norm_num) hNq2 M
        obtain ⟨_, hgeom4⟩ := prime_norm_rpow_neg_half_sum_le_four p hp_local q M
        let r := N_q ^ (-1 / 2 : ℝ)
        have hr_pos : 0 < r := Real.rpow_pos_of_pos hNq_pos _
        -- Step identity on Q_pool.erase q.
        have hstep_S' (Y_s : ℝ) (w : O) :
            let α := Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)
            inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / Y_s)) w =
              inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / Y_s)) w +
              α * inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / (Y_s / N_q))) w +
              (α * a i₀ q) * inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S₀ lists a U * W (primeProductNorm p U / (Y_s / N_q))) w := by
          intro α
          have hins : insert q (Q_pool.erase q) = Q_pool := Finset.insert_erase hq_in
          have hnot : q ∉ Q_pool.erase q := fun h => (Finset.mem_erase.mp h).1 rfl
          have h1 (T : Finset ι) : primeSubsetRow p χ T 1 = 1 := by simp [primeSubsetRow]
          have hpool_sum : ∀ f : Finset ι → ℂ,
              (∑ S ∈ Q_pool.powerset, f S) =
                (∑ S ∈ (Q_pool.erase q).powerset, f S) +
                  ∑ S ∈ (Q_pool.erase q).powerset.image (insert q), f S := by
            intro f
            conv_lhs => rw [← hins, Finset.powerset_insert]
            exact Finset.sum_union (Finset.disjoint_iff_ne.mpr (fun S hS T hT heq => by
              obtain ⟨U, _hU, rfl⟩ := Finset.mem_image.mp hT
              exact hnot ((Finset.mem_powerset.mp hS) (heq ▸ Finset.mem_insert_self q U))))
          unfold inputConjugateRow supportConjugateSum secondInputCoefficient
          simp only [h1, one_pow, mul_one]
          rw [hpool_sum, Finset.sum_image (fun U₁ hU₁ U₂ hU₂ heq => by
            have hq1 : q ∉ U₁ := fun h => hnot ((Finset.mem_powerset.mp hU₁) h)
            have hq2 : q ∉ U₂ := fun h => hnot ((Finset.mem_powerset.mp hU₂) h)
            exact (Finset.erase_insert hq1).symm.trans ((congrArg (fun S => S.erase q) heq).trans
              (Finset.erase_insert hq2)))]
          have hsecond :
              (∑ U ∈ (Q_pool.erase q).powerset,
                supportMobius (insert q U) * (Ψ₀ (∏ i ∈ insert q U, p i) *
                  primeCoprimeMask p (insert q U) 1 *
                  (InverseMoment.primeMark S' lists a (insert q U) *
                    W (primeProductNorm p (insert q U) / Y_s))) *
                  star (primeSubsetRow p χ (insert q U) w)) =
              -(α * ∑ U ∈ (Q_pool.erase q).powerset,
                supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
                  (InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / (Y_s / N_q)))) *
                  star (primeSubsetRow p χ U w)) -
              ((α * a i₀ q) * ∑ U ∈ (Q_pool.erase q).powerset,
                supportMobius U * (Ψ₀ (∏ i ∈ U, p i) * primeCoprimeMask p U 1 *
                  (InverseMoment.primeMark S₀ lists a U * W (primeProductNorm p U / (Y_s / N_q)))) *
                  star (primeSubsetRow p χ U w)) := by
            rw [Finset.mul_sum, Finset.mul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib,
              ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro U hU
            have hqU : q ∉ U := fun h => hnot ((Finset.mem_powerset.mp hU) h)
            have hd : Disjoint {q} U := Finset.disjoint_singleton_left.mpr hqU
            have hinsU : insert q U = {q} ∪ U := (Finset.singleton_union q U).symm
            have hmob : supportMobius ({q} ∪ U) = -supportMobius U := by
              rw [supportMobius_union {q} U hd]; simp [supportMobius]
            have hprod : Ψ₀ (∏ i ∈ {q} ∪ U, p i) = Ψ₀ (p q) * Ψ₀ (∏ i ∈ U, p i) := by
              rw [Finset.prod_union hd, Finset.prod_singleton, map_mul]
            have hmask : primeCoprimeMask p ({q} ∪ U) 1 =
                primeCoprimeMask p {q} 1 * primeCoprimeMask p U 1 := by
              unfold primeCoprimeMask; exact Finset.prod_union hd
            have hrow : star (primeSubsetRow p χ ({q} ∪ U) w) =
                star (primeSubsetRow p χ {q} w) * star (primeSubsetRow p χ U w) := by
              rw [primeSubsetRow_union p χ {q} U hd, star_mul, mul_comm]
            have hnorm : primeProductNorm p ({q} ∪ U) / Y_s = primeProductNorm p U / (Y_s / N_q) := by
              rw [primeProductNorm_union p {q} U hd]
              have hNq : primeProductNorm p {q} = N_q := by simp [primeProductNorm, N_q]
              rw [hNq, div_div_eq_mul_div, mul_comm]
            rw [hΦ_split U hU, hinsU, hmob, hprod, hmask, hrow, hnorm]
            dsimp [α]
            ring
          rw [hsecond]
          ring
        -- Finite telescope of hstep_S' up to M.
        have hgeom_S' (w : O) :
            let α := Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)
            inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / X₀)) w =
              (∑ k ∈ Finset.range M, α ^ k *
                inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                  (fun U => InverseMoment.primeMark S' lists a U *
                    W (primeProductNorm p U / (X₀ / N_q ^ k))) w) +
              (∑ k ∈ Finset.range M, (α ^ (k + 1) * a i₀ q) *
                inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                  (fun U => InverseMoment.primeMark S₀ lists a U *
                    W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w) := by
          intro α
          have hrec : ∀ K : ℕ,
              inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                  (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / X₀)) w =
                (∑ k ∈ Finset.range K, α ^ k *
                  inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                    (fun U => InverseMoment.primeMark S' lists a U *
                      W (primeProductNorm p U / (X₀ / N_q ^ k))) w) +
                (∑ k ∈ Finset.range K, (α ^ (k + 1) * a i₀ q) *
                  inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                    (fun U => InverseMoment.primeMark S₀ lists a U *
                      W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w) +
                α ^ K * inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                  (fun U => InverseMoment.primeMark S' lists a U *
                    W (primeProductNorm p U / (X₀ / N_q ^ K))) w := by
            intro K
            induction K with
            | zero => simp
            | succ K ih_K =>
              rw [ih_K, Finset.sum_range_succ, Finset.sum_range_succ,
                hstep_S' (X₀ / N_q ^ K) w]
              have hdiv : (X₀ / N_q ^ K) / N_q = X₀ / N_q ^ (K + 1) := by rw [div_div, ← pow_succ]
              dsimp only [N_q] at hdiv ⊢
              simp_rw [hdiv]
              ring
          rw [hrec M]
          have hrem0 : inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
              (fun U => InverseMoment.primeMark S' lists a U *
                W (primeProductNorm p U / (X₀ / N_q ^ M))) w = 0 := by
            unfold inputConjugateRow supportConjugateSum secondInputCoefficient
            apply Finset.sum_eq_zero
            intro U _
            have hU1 : 1 ≤ primeProductNorm p U := primeProductNorm_ge_one p hp_local U
            have hXM_pos : 0 < X₀ / N_q ^ M := div_pos hX₀ (pow_pos hNq_pos M)
            have hgt : b_hi < primeProductNorm p U / (X₀ / N_q ^ M) := by
              rw [lt_div_iff₀ hXM_pos, mul_div_assoc']
              exact (div_lt_one (pow_pos hNq_pos M)).mpr hterm |>.trans_le hU1
            have hw0 : W (primeProductNorm p U / (X₀ / N_q ^ M)) = 0 := by
              by_contra hne; exact not_le_of_gt hgt (hb _ hne)
            dsimp only
            rw [hw0]
            ring
          rw [hrem0, mul_zero, add_zero]
        -- Pointwise bound `‖A + B‖^2 ≤ 2 ‖A‖^2 + 2 ‖B‖^2` and Cauchy-Schwarz on both sums.
        have hprod_S' : (∏ i ∈ S', Z_slot i) = Z_slot i₀ * ∏ i ∈ S₀, Z_slot i := by
          conv_lhs => rw [← Finset.insert_erase hi₀, Finset.prod_insert (Finset.notMem_erase i₀ S')]
        have hpt (w : O) :
            (X₀ * ∏ i ∈ S', Z_slot i)⁻¹ * ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / X₀)) w‖ ^ 2 ≤
              2 * (∑ k ∈ Finset.range M, r ^ k) *
                (∑ k ∈ Finset.range M, r ^ k *
                  (((X₀ / N_q ^ k) * ∏ i ∈ S', Z_slot i)⁻¹ * ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                    (fun U => InverseMoment.primeMark S' lists a U *
                      W (primeProductNorm p U / (X₀ / N_q ^ k))) w‖ ^ 2)) +
              2 * (∑ k ∈ Finset.range M, r ^ k) *
                (∑ k ∈ Finset.range M, r ^ k *
                  (((X₀ / N_q ^ (k + 1)) * ∏ i ∈ S₀, Z_slot i)⁻¹ *
                    ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                      (fun U => InverseMoment.primeMark S₀ lists a U *
                        W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w‖ ^ 2)) := by
          rw [hgeom_S' w]
          let α := Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)
          have hα1 : ‖α‖ ≤ 1 := by
            dsimp [α]
            have h1 : ‖Ψ₀ (p q)‖ ≤ 1 := hΨ1 _
            have h2 : ‖primeCoprimeMask p {q} 1‖ ≤ 1 := by
              by_cases hd : p q ∣ 1 <;> simp [primeCoprimeMask, hd]
            have h3 : ‖star (primeSubsetRow p χ {q} w)‖ ≤ 1 := by
              rw [norm_star]; exact primeSubsetRow_norm_le_one p χ {q} w
            calc ‖Ψ₀ (p q) * primeCoprimeMask p {q} 1 * star (primeSubsetRow p χ {q} w)‖
                = ‖Ψ₀ (p q)‖ * ‖primeCoprimeMask p {q} 1‖ * ‖star (primeSubsetRow p χ {q} w)‖ := by
                  rw [norm_mul, norm_mul]
              _ ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) zero_le_one) h3
                  (norm_nonneg _) (by norm_num)
              _ = 1 := by norm_num
          have ha1 : ‖a i₀ q‖ ≤ 1 := ha i₀ (hS' hi₀) q hq_i₀
          let A_sum := ∑ k ∈ Finset.range M, α ^ k *
            inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
              (fun U => InverseMoment.primeMark S' lists a U *
                W (primeProductNorm p U / (X₀ / N_q ^ k))) w
          let B_sum := ∑ k ∈ Finset.range M, (α ^ (k + 1) * a i₀ q) *
            inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
              (fun U => InverseMoment.primeMark S₀ lists a U *
                W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w
          have h2ab : ‖A_sum + B_sum‖ ^ 2 ≤ 2 * ‖A_sum‖ ^ 2 + 2 * ‖B_sum‖ ^ 2 := by
            have htri_ab := norm_add_le A_sum B_sum
            have hsq_ab := pow_le_pow_left₀ (norm_nonneg _) htri_ab 2
            nlinarith [sq_nonneg (‖A_sum‖ - ‖B_sum‖)]
          -- Helper for weighted CS on range M.
          have hcs_gen (g : ℕ → ℝ) (hg_nn : ∀ k, 0 ≤ g k) :
              (∑ k ∈ Finset.range M, g k) ^ 2 ≤
                (∑ k ∈ Finset.range M, r ^ k) * ∑ k ∈ Finset.range M, r ^ k * (N_q ^ k * g k ^ 2) := by
            have h1 : (∑ k ∈ Finset.range M, g k) =
                ∑ k ∈ Finset.range M, (r ^ k) ^ (1 / 2 : ℝ) *
                  ((r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g k)) := by
              apply Finset.sum_congr rfl; intro k _
              have hr1 : (r ^ k) ^ (1 / 2 : ℝ) * (r ^ k) ^ (1 / 2 : ℝ) = r ^ k := by
                rw [← Real.rpow_add (pow_pos hr_pos k)]; norm_num
              have hr2 : r ^ k * (N_q ^ k) ^ (1 / 2 : ℝ) = 1 := by
                dsimp [r]
                rw [← Real.rpow_natCast, ← Real.rpow_mul hNq_pos.le,
                  ← Real.rpow_natCast N_q k, ← Real.rpow_mul hNq_pos.le, ← Real.rpow_add hNq_pos]
                have : (-1 / 2 : ℝ) * (k : ℝ) + (k : ℝ) * (1 / 2 : ℝ) = 0 := by ring
                rw [this, Real.rpow_zero]
              calc g k = 1 * g k := (one_mul _).symm
                _ = (((r ^ k) ^ (1 / 2 : ℝ) * (r ^ k) ^ (1 / 2 : ℝ)) * (N_q ^ k) ^ (1 / 2 : ℝ)) * g k := by
                    rw [hr1, hr2]
                _ = _ := by ring
            have hcs0 := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range M)
              (fun k => (r ^ k) ^ (1 / 2 : ℝ))
              (fun k => (r ^ k) ^ (1 / 2 : ℝ) * ((N_q ^ k) ^ (1 / 2 : ℝ) * g k))
            rw [← h1] at hcs0
            have hsq0 := pow_le_pow_left₀ (Finset.sum_nonneg (fun k _ => hg_nn k)) hcs0 2
            rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),
              Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))] at hsq0
            refine hsq0.trans_eq ?_
            congr 1
            · apply Finset.sum_congr rfl; intro k _
              rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (pow_nonneg hr_pos.le k)]; norm_num
            · apply Finset.sum_congr rfl; intro k _
              have hp1 : ((r ^ k) ^ (1 / 2 : ℝ)) ^ 2 = r ^ k := by
                rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (pow_nonneg hr_pos.le k)]; norm_num
              have hp2 : ((N_q ^ k) ^ (1 / 2 : ℝ)) ^ 2 = N_q ^ k := by
                rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (pow_nonneg hNq_pos.le k)]; norm_num
              rw [mul_pow, mul_pow, hp1, hp2]
          let gA : ℕ → ℝ := fun k => ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
            (fun U => InverseMoment.primeMark S' lists a U *
              W (primeProductNorm p U / (X₀ / N_q ^ k))) w‖
          let gB : ℕ → ℝ := fun k => ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
            (fun U => InverseMoment.primeMark S₀ lists a U *
              W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w‖
          have hA_le : ‖A_sum‖ ≤ ∑ k ∈ Finset.range M, gA k :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => by
              rw [norm_mul, norm_pow]
              exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hα1)))
          have hB_le : ‖B_sum‖ ≤ ∑ k ∈ Finset.range M, gB k :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => by
              rw [norm_mul, norm_mul, norm_pow]
              exact mul_le_of_le_one_left (norm_nonneg _)
                ((mul_le_mul (pow_le_one₀ (norm_nonneg _) hα1) ha1 (norm_nonneg _) zero_le_one).trans_eq
                  (one_mul 1))))
          have hA_sq : (X₀ * ∏ i ∈ S', Z_slot i)⁻¹ * ‖A_sum‖ ^ 2 ≤
              (∑ k ∈ Finset.range M, r ^ k) * ∑ k ∈ Finset.range M, r ^ k *
                (((X₀ / N_q ^ k) * ∏ i ∈ S', Z_slot i)⁻¹ * gA k ^ 2) := by
            calc (X₀ * ∏ i ∈ S', Z_slot i)⁻¹ * ‖A_sum‖ ^ 2
                ≤ (X₀ * ∏ i ∈ S', Z_slot i)⁻¹ *
                    ((∑ k ∈ Finset.range M, r ^ k) * ∑ k ∈ Finset.range M, r ^ k * (N_q ^ k * gA k ^ 2)) :=
                  mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ (norm_nonneg _) hA_le 2).trans
                    (hcs_gen gA (fun _ => norm_nonneg _)))
                    (inv_nonneg.mpr (mul_pos hX₀ hC_norm).le)
              _ = _ := by
                  rw [← mul_assoc, mul_comm (X₀ * ∏ i ∈ S', Z_slot i)⁻¹, mul_assoc, Finset.mul_sum]
                  congr 1; apply Finset.sum_congr rfl; intro k _
                  field_simp [hX₀.ne', hC_norm.ne', (pow_pos hNq_pos k).ne']
          have hB_sq : (X₀ * ∏ i ∈ S', Z_slot i)⁻¹ * ‖B_sum‖ ^ 2 ≤
              (∑ k ∈ Finset.range M, r ^ k) * ∑ k ∈ Finset.range M, r ^ k *
                (((X₀ / N_q ^ (k + 1)) * ∏ i ∈ S₀, Z_slot i)⁻¹ * gB k ^ 2) := by
            have hZN1 : 1 ≤ Z_slot i₀ * N_q := by nlinarith
            have hinv_le : (X₀ * ∏ i ∈ S', Z_slot i)⁻¹ ≤
                ((X₀ / N_q) * ∏ i ∈ S₀, Z_slot i)⁻¹ := by
              rw [hprod_S']
              have hle_den : (X₀ / N_q) * ∏ i ∈ S₀, Z_slot i ≤
                  X₀ * (Z_slot i₀ * ∏ i ∈ S₀, Z_slot i) := by
                rw [div_mul_eq_mul_div, div_le_iff₀ hNq_pos]
                have hpos_X : 0 ≤ X₀ * ∏ i ∈ S₀, Z_slot i := mul_nonneg hX₀.le hC₀_pos.le
                nlinarith
              exact inv_anti₀ (mul_pos (div_pos hX₀ hNq_pos) hC₀_pos) hle_den
            calc (X₀ * ∏ i ∈ S', Z_slot i)⁻¹ * ‖B_sum‖ ^ 2
                ≤ ((X₀ / N_q) * ∏ i ∈ S₀, Z_slot i)⁻¹ *
                    ((∑ k ∈ Finset.range M, r ^ k) * ∑ k ∈ Finset.range M, r ^ k * (N_q ^ k * gB k ^ 2)) :=
                  mul_le_mul hinv_le ((pow_le_pow_left₀ (norm_nonneg _) hB_le 2).trans
                    (hcs_gen gB (fun _ => norm_nonneg _))) (sq_nonneg _)
                    (inv_nonneg.mpr (mul_pos (div_pos hX₀ hNq_pos) hC₀_pos).le)
              _ = _ := by
                  rw [← mul_assoc, mul_comm ((X₀ / N_q) * ∏ i ∈ S₀, Z_slot i)⁻¹, mul_assoc, Finset.mul_sum]
                  congr 1; apply Finset.sum_congr rfl; intro k _
                  have hdiv : (X₀ / N_q) / N_q ^ k = X₀ / N_q ^ (k + 1) := by
                    rw [div_div, ← pow_succ']
                  rw [← hdiv]
                  field_simp [(div_pos hX₀ hNq_pos).ne', hC₀_pos.ne', (pow_pos hNq_pos k).ne']
          calc (X₀ * ∏ i ∈ S', Z_slot i)⁻¹ * ‖A_sum + B_sum‖ ^ 2
              ≤ (X₀ * ∏ i ∈ S', Z_slot i)⁻¹ * (2 * ‖A_sum‖ ^ 2 + 2 * ‖B_sum‖ ^ 2) :=
                mul_le_mul_of_nonneg_left h2ab (inv_nonneg.mpr (mul_pos hX₀ hC_norm).le)
            _ = 2 * ((X₀ * ∏ i ∈ S', Z_slot i)⁻¹ * ‖A_sum‖ ^ 2) +
                  2 * ((X₀ * ∏ i ∈ S', Z_slot i)⁻¹ * ‖B_sum‖ ^ 2) := by ring
            _ ≤ _ := by
                dsimp only [gA] at hA_sq
                dsimp only [gB] at hB_sq
                linarith [hA_sq, hB_sq]
        -- Sum hpt over w ∈ S_w and apply IH to A_sum and (invariant_l2 + IH) to B_sum!
        have hsdiff_S₀ : S_rem \ S₀ = insert i₀ (S_rem \ S') := by
          ext x
          simp only [S₀, Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
          exact ⟨fun ⟨hxR, hx⟩ => by by_cases hxi : x = i₀; exact Or.inl hxi; exact Or.inr ⟨hxR, fun h => hx ⟨hxi, h⟩⟩,
            fun h => h.elim (fun hxi => by subst hxi; exact ⟨hS' hi₀, fun hc => hc.1 rfl⟩)
              (fun ⟨hxR, hx⟩ => ⟨hxR, fun hc => hx hc.2⟩)⟩
        have hnot_sdiff : i₀ ∉ S_rem \ S' := fun h => (Finset.mem_sdiff.mp h).2 hi₀
        have hA_term (k : ℕ) :
            (∑ w ∈ S_w, ((X₀ / N_q ^ k) * ∏ i ∈ S', Z_slot i)⁻¹ *
              ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S' lists a U *
                  W (primeProductNorm p U / (X₀ / N_q ^ k))) w‖ ^ 2) ≤
              (1024 : ℝ) ^ P'.card * B_sup := by
          apply ih S' hS' (X₀ / N_q ^ k) (div_pos hX₀ (pow_pos hNq_pos k))
          exact (mul_le_mul_of_nonneg_right
            (div_le_self hX₀.le (one_le_pow₀ (by linarith)))
            (Finset.prod_nonneg (fun i hi => (zero_lt_one.trans_le (hZ1 i (Finset.mem_sdiff.mp hi).1)).le))).trans
            hX₀_le
        have hB_term (k : ℕ) :
            (∑ w ∈ S_w, ((X₀ / N_q ^ (k + 1)) * ∏ i ∈ S₀, Z_slot i)⁻¹ *
              ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S₀ lists a U *
                  W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w‖ ^ 2) ≤
              16 * ((1024 : ℝ) ^ P'.card * B_sup) := by
          apply inputConjugateRow_erase_invariant_l2 p hg hp_local Q_pool hq_in Ψ₀ hΨ1
            (InverseMoment.primeMark S₀ lists a) hΦ_S₀ W hb S_w hC₀_pos hB'
            (div_pos hX₀ (pow_pos hNq_pos (k + 1)))
          intro X' hX' hX'_le
          apply ih S₀ hS₀_sub X' hX'
          rw [hsdiff_S₀, Finset.prod_insert hnot_sdiff, ← mul_assoc]
          have hX'_Z : X' * Z_slot i₀ ≤ X₀ := by
            have h1 : X' * N_q ≤ X₀ := by
              have hk1 : N_q ≤ N_q ^ (k + 1) := le_self_pow₀ (by linarith) (Nat.succ_ne_zero k)
              have h2 : X' ≤ X₀ / N_q := hX'_le.trans (div_le_div_of_nonneg_left hX₀.le hNq_pos hk1)
              exact (le_div_iff₀ hNq_pos).mp h2
            exact (mul_le_mul_of_nonneg_left hZq hX'.le).trans h1
          exact (mul_le_mul_of_nonneg_right hX'_Z
            (Finset.prod_nonneg (fun i hi => (zero_lt_one.trans_le (hZ1 i (Finset.mem_sdiff.mp hi).1)).le))).trans
            hX₀_le
        calc
          (∑ w ∈ S_w, (X₀ * ∏ i ∈ S', Z_slot i)⁻¹ * ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
              (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / X₀)) w‖ ^ 2)
            ≤ ∑ w ∈ S_w,
                (2 * (∑ k ∈ Finset.range M, r ^ k) *
                  (∑ k ∈ Finset.range M, r ^ k *
                    (((X₀ / N_q ^ k) * ∏ i ∈ S', Z_slot i)⁻¹ * ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                      (fun U => InverseMoment.primeMark S' lists a U *
                        W (primeProductNorm p U / (X₀ / N_q ^ k))) w‖ ^ 2)) +
                2 * (∑ k ∈ Finset.range M, r ^ k) *
                  (∑ k ∈ Finset.range M, r ^ k *
                    (((X₀ / N_q ^ (k + 1)) * ∏ i ∈ S₀, Z_slot i)⁻¹ *
                      ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                        (fun U => InverseMoment.primeMark S₀ lists a U *
                          W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w‖ ^ 2))) :=
              Finset.sum_le_sum (fun w _ => hpt w)
          _ = 2 * (∑ k ∈ Finset.range M, r ^ k) *
                (∑ k ∈ Finset.range M, r ^ k *
                  ∑ w ∈ S_w, ((X₀ / N_q ^ k) * ∏ i ∈ S', Z_slot i)⁻¹ *
                    ‖inputConjugateRow p χ Q_pool Ψ₀ 1 1 1
                      (fun U => InverseMoment.primeMark S' lists a U *
                        W (primeProductNorm p U / (X₀ / N_q ^ k))) w‖ ^ 2) +
              2 * (∑ k ∈ Finset.range M, r ^ k) *
                (∑ k ∈ Finset.range M, r ^ k *
                  ∑ w ∈ S_w, ((X₀ / N_q ^ (k + 1)) * ∏ i ∈ S₀, Z_slot i)⁻¹ *
                    ‖inputConjugateRow p χ (Q_pool.erase q) Ψ₀ 1 1 1
                      (fun U => InverseMoment.primeMark S₀ lists a U *
                        W (primeProductNorm p U / (X₀ / N_q ^ (k + 1)))) w‖ ^ 2) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
              congr 2
              · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _; rw [← Finset.mul_sum]
              · rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro k _; rw [← Finset.mul_sum]
          _ ≤ 2 * 4 * (∑ k ∈ Finset.range M, r ^ k * ((1024 : ℝ) ^ P'.card * B_sup)) +
                2 * 4 * (∑ k ∈ Finset.range M, r ^ k * (16 * ((1024 : ℝ) ^ P'.card * B_sup))) := by
              have hgeom4' : (∑ k ∈ Finset.range M, r ^ k) ≤ 4 := hgeom4
              apply add_le_add
              · apply mul_le_mul (by linarith [hgeom4'])
                  (Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hA_term k) (pow_nonneg hr_pos.le k)))
                  (Finset.sum_nonneg (fun k _ => mul_nonneg (pow_nonneg hr_pos.le k)
                    (Finset.sum_nonneg (fun _ _ => mul_nonneg
                      (inv_nonneg.mpr (mul_pos (div_pos hX₀ (pow_pos hNq_pos k)) hC_norm).le) (sq_nonneg _)))))
                  (by norm_num)
              · apply mul_le_mul (by linarith [hgeom4'])
                  (Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (hB_term k) (pow_nonneg hr_pos.le k)))
                  (Finset.sum_nonneg (fun k _ => mul_nonneg (pow_nonneg hr_pos.le k)
                    (Finset.sum_nonneg (fun _ _ => mul_nonneg
                      (inv_nonneg.mpr (mul_pos (div_pos hX₀ (pow_pos hNq_pos (k + 1))) hC₀_pos).le) (sq_nonneg _)))))
                  (by norm_num)
          _ = 136 * (∑ k ∈ Finset.range M, r ^ k) * ((1024 : ℝ) ^ P'.card * B_sup) := by
              rw [← Finset.sum_mul, ← Finset.sum_mul]; ring
          _ ≤ 136 * 4 * ((1024 : ℝ) ^ P'.card * B_sup) := by
              have hgeom4' : (∑ k ∈ Finset.range M, r ^ k) ≤ 4 := hgeom4
              exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgeom4' (by norm_num)) hB'
          _ ≤ 1024 * (1024 : ℝ) ^ P'.card * B_sup := by linarith [hB']
      · -- Case A: `q` belongs to no `lists i` (`i ∈ S'`).
        have hex' : ∀ i ∈ S', q ∉ lists i := fun i hi hqi => hex ⟨i, hi, hqi⟩
        have hΦ_inv : ∀ U ∈ ((pool \ P').erase q).powerset,
            InverseMoment.primeMark S' lists a (insert q U) = InverseMoment.primeMark S' lists a U := by
          intro U _
          unfold InverseMoment.primeMark InverseMoment.primeSlot
          apply Finset.prod_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro r hr
          have hrq : r ≠ q := fun he => hex' i hi (he ▸ hr)
          simp [Finset.mem_insert, hrq]
        calc
          (∑ w ∈ S_w, (X₀ * ∏ i ∈ S', Z_slot i)⁻¹ *
              ‖inputConjugateRow p χ ((pool \ P').erase q) Ψ₀ 1 1 1
                (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / X₀)) w‖ ^ 2)
            ≤ 16 * ((1024 : ℝ) ^ P'.card * B_sup) := by
              apply inputConjugateRow_erase_invariant_l2 p hg hp_local (pool \ P') hq_in Ψ₀ hΨ1
                (InverseMoment.primeMark S' lists a) hΦ_inv W hb S_w hC_norm hB' hX₀
              intro X' hX' hX'_le
              exact ih S' hS' X' hX' ((mul_le_mul_of_nonneg_right hX'_le
                (Finset.prod_nonneg (fun i hi => (zero_lt_one.trans_le (hZ1 i (Finset.mem_sdiff.mp hi).1)).le))).trans
                hX₀_le)
          _ ≤ 1024 * (1024 : ℝ) ^ P'.card * B_sup := by linarith [hB']
    · have hsdiff : pool \ insert q P' = pool \ P' := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        exact ⟨fun ⟨hp_x, hn⟩ => ⟨hp_x, fun h => hn (Or.inr h)⟩,
          fun ⟨hp_x, hn⟩ => ⟨hp_x, fun h => h.elim
            (fun heq => by subst heq; exact hq_in (Finset.mem_sdiff.mpr ⟨hp_x, hn⟩)) hn⟩⟩
      rw [hsdiff]
      calc
        (∑ w ∈ S_w, (X₀ * ∏ i ∈ S', Z_slot i)⁻¹ * ‖inputConjugateRow p χ (pool \ P') Ψ₀ 1 1 1
            (fun U => InverseMoment.primeMark S' lists a U * W (primeProductNorm p U / X₀)) w‖ ^ 2)
          ≤ (1024 : ℝ) ^ P'.card * B_sup := ih S' hS' X₀ hX₀ hX₀_le
        _ ≤ 1024 * (1024 : ℝ) ^ P'.card * B_sup := by linarith [hB']

/-- Divisor bound `(1024 : ℝ) ^ P_punc.card ≤ ((idealDivisors (Ideal.span {m'})).card : ℝ) ^ 10`
for `P_punc = pool.filter (fun q => p q ∣ m')` (`m' ≠ 0`). -/
theorem puncture_card_pow_1024_le_divisors
    (hp_local : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (pool : Finset ι) {m' : O} (hm' : m' ≠ 0) :
    let P_punc := pool.filter (fun q => p q ∣ m')
    (1024 : ℝ) ^ P_punc.card ≤ ((idealDivisors (Ideal.span {m'})).card : ℝ) ^ 10 := by
  intro P_punc
  have hIm0 : (Ideal.span {m'} : Ideal O) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hm'
  let φ : Finset ι → Ideal O := fun E => ∏ q ∈ E, Ideal.span {p q}
  have hmaps : ∀ E ∈ P_punc.powerset, φ E ∈ idealDivisors (Ideal.span {m'}) := by
    intro E hE
    have hEP : E ⊆ P_punc := Finset.mem_powerset.mp hE
    rw [mem_idealDivisors hIm0]
    exact Finset.prod_dvd_of_coprime (fun i _ j _ hij => hcop hij)
      (fun q hq => Ideal.dvd_iff_le.mpr
        (Ideal.span_singleton_le_span_singleton.mpr (Finset.mem_filter.mp (hEP hq)).2))
  have hcard : P_punc.powerset.card ≤ (idealDivisors (Ideal.span {m'})).card :=
    Finset.card_le_card_of_injOn φ hmaps
      (fun _ _ _ _ he => span_finset_prod_injective p hp_local hcop he)
  rw [Finset.card_powerset] at hcard
  have h2 : (2 : ℝ) ^ P_punc.card ≤ ((idealDivisors (Ideal.span {m'})).card : ℝ) := by
    exact_mod_cast hcard
  calc
    (1024 : ℝ) ^ P_punc.card = ((2 : ℝ) ^ P_punc.card) ^ 10 := by
        rw [← pow_mul, mul_comm, pow_mul]; norm_num
    _ ≤ ((idealDivisors (Ideal.span {m'})).card : ℝ) ^ 10 := pow_le_pow_left₀ (by positivity) h2 10

end FiniteGeometricUnpuncturing

end Stage1DualRowMoments

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
