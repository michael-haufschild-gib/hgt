import GaloisForLFunctions.RHTower.WeilPositivityFiniteLevelExistence
import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional
import GaloisForLFunctions.RHTower.WeilOddConeHalfPoleRigidity

/-!
# RH is existence of Weil-positive weights at every finite aperture

`WeilPositivityFiniteLevelExistence` splits Minkowski's problem for the Weil cone into an existence
part, reduced to finite levels by compactness, and a uniqueness part. The full cone has an
unconditional uniqueness theorem (`eq_vonMangoldt_of_weilPositiveFull`: every full-cone positive
weight is `Λ`). This module carries the existence reduction over to the full cone and closes the
split:

**Theorem** (`riemannHypothesis_iff_forall_level_exists_weilPositiveFullUpTo`). RH holds iff for
every aperture `A` there are real weights `lam` (any sign, any growth, no relation to the primes)
for which the full Weil functional of `ζ`'s archimedean datum,
`k ↦ k̂(i/2) + k̂(−i/2) − Σ_{n ≥ 2} lam(n) n^{−1/2}(k(log n) + k(−log n)) + (1/2π)∫ k̂ Ω`,
is nonnegative on every autocorrelation `f ⋆ f̃` of a `C²` test supported in `[−A, A]`.

The primes do not occur in the condition: only the archimedean factor, the pole and the positions
`log n` of the integers. Proof. Full positivity up to `A` implies symbol positivity on pole-free
tests up to `A`, hence the box `|lam(n)| ≤ √n (log n + C₀)` on the atoms seen at level `A`
(`abs_le_boxWidth_of_weilPositiveUpTo`). Clamped finite-level solutions have a coordinatewise
convergent subsequence; on each test the functional is affine in the finitely many weights it sees,
so the limit is full-cone positive (`exists_weilPositiveFull_iff_forall_level`). Uniqueness makes it
`Λ` and gives RH.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate ArithmeticFunction

noncomputable section

namespace RHTower

open Zeta23 ResonatorProfile

/-- Full-cone Weil positivity of the weights `lam` on tests supported in `[−A, A]`. -/
def WeilPositiveFullUpTo (lam : ℕ → ℝ) (A : ℝ) : Prop :=
  ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-A) A →
    0 ≤ (weilFullFunctional lam (EF.weilTest f f)).re

/-- Full positivity up to `A` gives symbol positivity on pole-free tests up to `A`. -/
theorem weilPositiveUpTo_of_weilPositiveFullUpTo {lam : ℕ → ℝ} {A : ℝ}
    (h : WeilPositiveFullUpTo lam A) : WeilPositiveUpTo lam A :=
  fun a ha haA f hf hfs hp hm =>
    integral_weilAtomSymbol_nonneg_of_re_weilFullFunctional_nonneg ha hf hfs hp hm
      (h f hf (hfs.trans (Icc_subset_Icc (by linarith) haA)))

/-- On a compactly supported test the full functional is affine in the finitely many weights it
sees. -/
theorem re_weilFullFunctional_eq_affine (lam : ℕ → ℝ) {k : ℝ → ℂ} {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → k (Real.log n) = 0 ∧ k (-Real.log n) = 0) :
    (weilFullFunctional lam k).re = (weilFullFunctional (fun _ => 0) k).re -
      ∑ n ∈ Finset.range N, (if 2 ≤ n then lam n / Real.sqrt n else 0) *
        (k (Real.log n) + k (-Real.log n)).re := by
  have key : ∀ l : ℕ → ℝ, weilFullFunctional l k =
      paperFT k (I / 2) + paperFT k (-I / 2) -
        ∑ n ∈ Finset.range N, ((if 2 ≤ n then l n / Real.sqrt n else 0 : ℝ) : ℂ) *
          (k (Real.log n) + k (-Real.log n)) +
        (1 / (2 * π) : ℂ) * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ) := by
    intro l
    unfold weilFullFunctional
    rw [tsum_eq_sum (s := Finset.range N) fun n hn => by
      rw [Finset.mem_range, not_lt] at hn
      rw [(hN n hn).1, (hN n hn).2, add_zero, mul_zero]]
  rw [key lam, key (fun _ => 0)]
  simp only [zero_div, ite_self, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, sub_zero,
    Complex.add_re, Complex.sub_re, Complex.re_sum, Complex.re_ofReal_mul]
  ring

/-- **Existence reduces to finite apertures, in the full cone.** A full-cone Weil-positive weight
system exists iff every aperture `A` admits weights that are full-cone positive up to `A`. -/
theorem exists_weilPositiveFull_iff_forall_level :
    (∃ lam : ℕ → ℝ, WeilPositiveFull lam) ↔ ∀ A : ℝ, ∃ lam : ℕ → ℝ, WeilPositiveFullUpTo lam A := by
  constructor
  · rintro ⟨lam, hlam⟩ A
    exact ⟨lam, fun f hf hfs => hlam f hf
      (IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs)⟩
  intro hex
  choose lam hlam using fun k : ℕ => hex (k : ℝ)
  -- clamp into the box
  set clamp : ℕ → ℕ → ℝ := fun k n => max (-boxWidth n) (min (boxWidth n) (lam k n)) with hclamp
  have hK : IsCompact (Set.univ.pi fun n : ℕ => Icc (-boxWidth n) (boxWidth n)) :=
    isCompact_univ_pi fun n => isCompact_Icc
  have hmem : ∀ k, clamp k ∈ Set.univ.pi fun n : ℕ => Icc (-boxWidth n) (boxWidth n) := by
    intro k n _
    have h0 : 0 ≤ boxWidth n := abs_nonneg _
    simp only [hclamp, mem_Icc]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  obtain ⟨lam₀, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hcoord : ∀ n, Tendsto (fun j => clamp (φ j) n) atTop (𝓝 (lam₀ n)) :=
    fun n => tendsto_pi_nhds.mp hlim n
  -- the clamp is inactive on each fixed atom, eventually
  have hagree : ∀ n, 2 ≤ n → ∀ᶠ j in atTop, clamp (φ j) n = lam (φ j) n := by
    intro n hn
    obtain ⟨K, hK⟩ := exists_nat_ge (atomLevel n)
    filter_upwards [hφ.tendsto_atTop.eventually_ge_atTop K] with j hj
    have hlev : atomLevel n ≤ (φ j : ℝ) := hK.trans (by exact_mod_cast hj)
    have hbox := abs_le_boxWidth_of_weilPositiveUpTo
      (weilPositiveUpTo_of_weilPositiveFullUpTo (hlam (φ j))) hn hlev
    rw [abs_le] at hbox
    simp only [hclamp]
    rw [min_eq_right hbox.2, max_eq_right hbox.1]
  refine ⟨lam₀, fun f hf hfc => ?_⟩
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  have hfs : ∀ A : ℝ, |R| ≤ A → tsupport f ⊆ Icc (-A) A := fun A hA x hx => by
    have hx' := hR hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hx'
    exact abs_le.mp (hx'.trans ((le_abs_self R).trans hA))
  set k := EF.weilTest f f with hk
  obtain ⟨N, hN⟩ := exists_forall_log_eq_zero (EF.weilTest_hasCompactSupport hfc hfc)
  set E : (ℕ → ℝ) → ℝ := fun l => (weilFullFunctional (fun _ => 0) k).re -
    ∑ n ∈ Finset.range N, (if 2 ≤ n then l n / Real.sqrt n else 0) *
      (k (Real.log n) + k (-Real.log n)).re with hE
  have hEq : ∀ l, (weilFullFunctional l k).re = E l := fun l => re_weilFullFunctional_eq_affine l hN
  have hElim : Tendsto (fun j => E (clamp (φ j))) atTop (𝓝 (E lam₀)) := by
    simp only [hE]
    refine tendsto_const_nhds.sub (tendsto_finsetSum _ fun n _ => ?_)
    by_cases hn : 2 ≤ n
    · simp only [if_pos hn]
      exact ((hcoord n).div_const _).mul_const _
    · simp only [if_neg hn]
      exact tendsto_const_nhds
  have hEagree : ∀ᶠ j in atTop, E (clamp (φ j)) = E (lam (φ j)) := by
    have hall : ∀ᶠ j in atTop, ∀ n ∈ (Finset.range N).filter (fun n => 2 ≤ n),
        clamp (φ j) n = lam (φ j) n :=
      (Finset.eventually_all _).mpr fun n hn => hagree n (Finset.mem_filter.mp hn).2
    filter_upwards [hall] with j hj
    simp only [hE]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    by_cases h2 : 2 ≤ n
    · rw [if_pos h2, if_pos h2, hj n (Finset.mem_filter.mpr ⟨hn, h2⟩)]
    · rw [if_neg h2, if_neg h2]
  have hEpos : ∀ᶠ j in atTop, 0 ≤ E (clamp (φ j)) := by
    obtain ⟨K, hK⟩ := exists_nat_ge |R|
    filter_upwards [hEagree, hφ.tendsto_atTop.eventually_ge_atTop K] with j hj hjK
    rw [hj, ← hEq]
    exact hlam (φ j) f hf (hfs _ (hK.trans (by exact_mod_cast hjK)))
  rw [hEq]
  exact ge_of_tendsto hElim hEpos

/-- **RH is finite-level existence.** RH holds iff for every aperture `A` some real weight system
makes the full Weil functional of `ζ`'s archimedean datum nonnegative on all autocorrelations of
`C²` tests supported in `[−A, A]`. -/
theorem riemannHypothesis_iff_forall_level_exists_weilPositiveFullUpTo :
    RiemannHypothesis ↔ ∀ A : ℝ, ∃ lam : ℕ → ℝ, WeilPositiveFullUpTo lam A := by
  rw [← exists_weilPositiveFull_iff_forall_level]
  constructor
  · intro h
    exact ⟨fun n => (ArithmeticFunction.vonMangoldt n : ℝ),
      WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mpr
        ⟨h, fun _ _ => rfl⟩⟩
  · rintro ⟨lam, h⟩
    exact (WeilSpectral.weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt.mp h).1

/-- **A failure of RH is visible at a finite aperture, for every weight system.** If RH fails, some
aperture `A` has the property that no real weights make the full Weil functional nonnegative on
all tests supported in `[−A, A]`. -/
theorem exists_level_forall_not_weilPositiveFullUpTo_of_not_riemannHypothesis
    (h : ¬ RiemannHypothesis) : ∃ A : ℝ, ∀ lam : ℕ → ℝ, ¬ WeilPositiveFullUpTo lam A := by
  by_contra hne
  push Not at hne
  exact h (riemannHypothesis_iff_forall_level_exists_weilPositiveFullUpTo.mpr hne)

end RHTower
