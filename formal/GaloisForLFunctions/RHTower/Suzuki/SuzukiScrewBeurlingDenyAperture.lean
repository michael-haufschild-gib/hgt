import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewDisjointCrossCoupling

/-!
# The Beurling–Deny aperture of the regular screw kernel

The restricted Weil form at aperture `a` acts on functions supported in `(-a, a)`. Off the
diagonal and off the prime-power atoms, its kernel is the regular screw kernel evaluated at the
distance, `K(|x - y|)`, with `K t = e^{t/2} - e^{-5t/2}/(1 - e^{-2t})`. The prime-power atoms
`log n`, `n ≥ 2`, enter with negative weight `-Λ(n) n^{-1/2}` and only help the inequality below.

**Theorem** (`satisfiesBeurlingDenyOn_screwEvenForm_iff`). For `a > 0`, the first Beurling–Deny
inequality on aperture `a` (nonnegative, disjointly supported functions in `(-a, a)` have
nonpositive cross value) holds for `K(|x - y|) + c · L²` exactly when `2a ≤ t_* = log ρ`, where
`ρ` is the plastic number.

* For `2a ≤ t_*`, every distance between the supports lies in `(0, t_*)`, where `K < 0`
  (`screwRegularKernel_neg_of_lt_threshold`). So the integrand is pointwise nonpositive.
* For `2a > t_*`, the two bumps of `exists_disjoint_positive_screwRegularForm` sit inside
  `(-a, a)` with every distance in `(t_*, 2a)`, and their cross value is positive.

The aperture-free predicate `SatisfiesBeurlingDeny` quantifies over all functions on the line, so
it fails at every aperture. This module gives the sharp aperture-indexed statement and its positive
half. Below `t_*/2` the Markov property holds and the restricted ground state has constant sign;
above `t_*/2` it fails.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Set MeasureTheory

/-- The even regular-kernel cross pairing `∫∫ K(|x - y|) f(y) h(x)`. -/
def screwEvenForm (f h : ℝ → ℝ) : ℝ :=
  ∫ p : ℝ × ℝ, screwRegularKernel |p.1 - p.2| * f p.2 * h p.1

/-- The first Beurling–Deny inequality on aperture `a`: nonnegative functions supported in
`(-a, a)` with disjoint supports have nonpositive cross value. -/
def SatisfiesBeurlingDenyOn (a : ℝ) (Q : (ℝ → ℝ) → (ℝ → ℝ) → ℝ) : Prop :=
  ∀ f h : ℝ → ℝ, (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ h x) →
    Function.support f ⊆ Ioo (-a) a → Function.support h ⊆ Ioo (-a) a →
    Disjoint (Function.support f) (Function.support h) → Q f h ≤ 0

/-- **Positive half.** For `2a ≤ t_*` the even regular form is nonpositive on disjointly supported
nonnegative functions in `(-a, a)`. -/
theorem screwEvenForm_nonpos_of_le {a : ℝ} (ha : 2 * a ≤ screwSignThreshold) {f h : ℝ → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hh : ∀ x, 0 ≤ h x) (hfs : Function.support f ⊆ Ioo (-a) a)
    (hhs : Function.support h ⊆ Ioo (-a) a)
    (hd : Disjoint (Function.support f) (Function.support h)) : screwEvenForm f h ≤ 0 := by
  refine integral_nonpos fun p => ?_
  show screwRegularKernel |p.1 - p.2| * f p.2 * h p.1 ≤ 0
  by_cases hfp : f p.2 = 0
  · simp [hfp]
  by_cases hhp : h p.1 = 0
  · simp [hhp]
  have hy := hfs hfp
  have hx := hhs hhp
  have hne : p.1 ≠ p.2 := by
    intro heq
    exact Set.disjoint_left.mp hd (show p.2 ∈ Function.support f from hfp)
      (show p.2 ∈ Function.support h by rw [← heq]; exact hhp)
  have hpos : 0 < |p.1 - p.2| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hlt : |p.1 - p.2| < screwSignThreshold := by
    have : |p.1 - p.2| < 2 * a := by
      rw [abs_lt]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    linarith
  have hK := screwRegularKernel_neg_of_lt_threshold hpos hlt
  rw [mul_assoc]
  exact mul_nonpos_of_nonpos_of_nonneg hK.le (mul_nonneg (hf p.2) (hh p.1))

/-- On pairs whose support differences are positive, the even form is the corpus regular form. -/
theorem screwEvenForm_eq_screwRegularForm {f h : ℝ → ℝ}
    (hpos : ∀ x ∈ tsupport h, ∀ y ∈ tsupport f, 0 < x - y) :
    screwEvenForm f h = screwRegularForm f h := by
  unfold screwEvenForm screwRegularForm
  congr 1
  funext p
  by_cases hfp : f p.2 = 0
  · simp [hfp]
  by_cases hhp : h p.1 = 0
  · simp [hhp]
  rw [abs_of_pos (hpos p.1 (subset_tsupport _ hhp) p.2 (subset_tsupport _ hfp))]

/-- **Sharp Beurling–Deny aperture.** For `a > 0` and every scalar shift `c`, the even regular
screw form satisfies the first Beurling–Deny inequality on aperture `a` iff `2a ≤ t_*`. -/
theorem satisfiesBeurlingDenyOn_screwEvenForm_iff (c : ℝ) {a : ℝ} :
    SatisfiesBeurlingDenyOn a (fun f h => screwEvenForm f h + c * screwL2Pairing f h) ↔
      2 * a ≤ screwSignThreshold := by
  constructor
  · intro hBD
    by_contra hlt
    have ha : screwSignThreshold / 2 < a := by linarith [not_le.mp hlt]
    obtain ⟨f, h, _, _, hfnn, hhnn, _, _, hfs, hhs, hdisj, _, _, hgap, hposform⟩ :=
      exists_disjoint_positive_screwRegularForm ha
    have heq : screwEvenForm f h = screwRegularForm f h :=
      screwEvenForm_eq_screwRegularForm fun x hx y hy =>
        screwSignThreshold_pos.trans (hgap x hx y hy).1
    have hle := hBD f h hfnn hhnn hfs hhs hdisj
    simp only [screwL2Pairing_eq_zero_of_disjoint hdisj, mul_zero, add_zero, heq] at hle
    linarith
  · intro ha f h hf hh hfs hhs hd
    simp only [screwL2Pairing_eq_zero_of_disjoint hd, mul_zero, add_zero]
    exact screwEvenForm_nonpos_of_le ha hf hh hfs hhs hd

end GaloisForLFunctions.RHTower

end
