import GaloisForLFunctions.HTGeometry.CompositionValuePreimages
import GaloisForLFunctions.HTGeometry.PoissonJensenUpperBound

/-!
# The composition's maximum modulus against the inner function's zero counts

Jensen's inequality bounds the zero count of a function by the logarithm of its maximum modulus.
Applied to `f ∘ g - a`, whose zeros contain those of every `g - b_i` for the `a`-points `b_i` of the
outer function, it turns the composition's maximum modulus into a *lower* bound: the composition must
be large because it has many zeros.

This is the counting form of composition growth.  Combined with the second main theorem for the inner
function, which makes the counts comparable with its characteristic, it is the growth comparison a
Clunie-type separation argument consumes.
-/

open Metric

namespace GaloisForLFunctions.HTGeometry

open scoped Classical in
/-- **The composition's maximum modulus dominates the inner counting functions.**  With `b_i` the
`a`-points of the outer function and `T i` the zeros of `g - b_i`,

  `(∑_i ∑_{ζ ∈ T i, ‖ζ - c‖ ≤ R₁} l i ζ) · log (R/R₁) ≤ log M - log ‖f (g c) - a‖`,

where `M` bounds `f ∘ g - a` on the circle of radius `R`. -/
theorem log_norm_comp_ge_count {f g : ℂ → ℂ} {a c : ℂ} {p : ℕ} (b : Fin p → ℂ)
    {T : Fin p → Finset ℂ} {l : Fin p → ℂ → ℕ} {k : Fin p → ℕ}
    {hh : Fin p → ℂ → ℂ} {H : ℂ → ℂ} {R R₁ M : ℝ} {U V : Set ℂ}
    (hR : 0 < R) (hR₁ : 0 < R₁) (hR₁R : R₁ ≤ R) (hk : ∀ i : Fin p, 1 ≤ k i)
    (hdisj : ∀ i j : Fin p, i ≠ j → Disjoint (T i) (T j))
    (hball : closedBall c R ⊆ U)
    (hgfac : ∀ i : Fin p, ∀ z ∈ U, g z - b i = (∏ ζ ∈ T i, (z - ζ) ^ (l i ζ)) * hh i z)
    (hffac : ∀ w ∈ V, f w - a = (∏ i, (w - b i) ^ (k i)) * H w)
    (hmaps : ∀ z ∈ U, g z ∈ V)
    (hFan : AnalyticOnNhd ℂ (fun z => f (g z) - a) (closedBall c R))
    (hGan : AnalyticOnNhd ℂ (fun z => (∏ i, hh i z ^ (k i)) * H (g z)) (closedBall c R))
    (hGfree : ∀ z ∈ closedBall c R, (∏ i, hh i z ^ (k i)) * H (g z) ≠ 0)
    (hTmem : ∀ ζ ∈ Finset.univ.biUnion T, ζ ∈ closedBall c R)
    (hsph : ∀ z ∈ sphere c R, f (g z) - a ≠ 0) (hFc : f (g c) - a ≠ 0)
    (hM : ∀ z ∈ sphere c R, ‖f (g z) - a‖ ≤ M) :
    (∑ i, ∑ ζ ∈ (T i).filter (fun ζ => ‖ζ - c‖ ≤ R₁), (l i ζ : ℝ)) * Real.log (R / R₁)
      ≤ Real.log M - Real.log ‖f (g c) - a‖ := by
  have hfacflat : ∀ z ∈ closedBall c R, f (g z) - a
      = (∏ ζ ∈ Finset.univ.biUnion T, (z - ζ) ^ (mergedMultiplicity T l k ζ))
        * ((∏ i, hh i z ^ (k i)) * H (g z)) := by
    intro z hz
    exact comp_flat_factor b hdisj (fun i z' hz' => hgfac i z' hz') hffac hmaps z (hball hz)
  have hjensen := sum_multiplicity_le_of_factor (f := fun z => f (g z) - a)
    (g := fun z => (∏ i, hh i z ^ (k i)) * H (g z))
    (T := Finset.univ.biUnion T) (m := mergedMultiplicity T l k) (R₁ := R₁) (M := M)
    hR hR₁ hFan hGan hGfree hTmem hfacflat hsph hFc hM
  refine le_trans (mul_le_mul_of_nonneg_right ?_ ?_) hjensen
  · -- the block counts are below the merged count
    have hcast : (∑ ζ ∈ (Finset.univ.biUnion T).filter (fun ζ => ‖ζ - c‖ ≤ R₁),
          (mergedMultiplicity T l k ζ : ℝ))
        = ((∑ ζ ∈ (Finset.univ.biUnion T).filter (fun ζ => ‖ζ - c‖ ≤ R₁),
            mergedMultiplicity T l k ζ : ℕ) : ℝ) := by
      push_cast
      rfl
    have hmerge := sum_filter_mergedMultiplicity (T := T) (l := l) (k := k) hdisj
      (fun ζ => ‖ζ - c‖ ≤ R₁)
    have hle := sum_filter_le_sum_filter_mergedMultiplicity (T := T) (l := l) (k := k) hk
      (fun ζ => ‖ζ - c‖ ≤ R₁)
    have hcast₂ : (∑ i, ∑ ζ ∈ (T i).filter (fun ζ => ‖ζ - c‖ ≤ R₁), (l i ζ : ℝ))
        = ((∑ i, ∑ ζ ∈ (T i).filter (fun ζ => ‖ζ - c‖ ≤ R₁), l i ζ : ℕ) : ℝ) := by
      push_cast
      rfl
    rw [hcast, hcast₂]
    exact_mod_cast le_trans hle (le_of_eq hmerge.symm)
  · exact Real.log_nonneg (by rw [le_div_iff₀ hR₁]; linarith)

/-! ## The raw count against the integrated one

The integrated counting function weights each zero by `log (R/‖ζ‖)`.  A zero inside radius `r`
contributes at least `log (R/r)`, so the raw count inside `r` is bounded by the integrated count at
`R` — the elementary comparison `n(r)·log(R/r) ≤ N(R)`.
-/

open scoped Classical in
/-- **`n(r)·log(R/r) ≤ N(R)`.**  The centre must not be a zero: the junk value `log (R/0) = 0` would
otherwise let a zero at the origin contribute nothing to the right-hand side. -/
theorem sum_mul_log_le_sum_mul_log (T : Finset ℂ) (m : ℂ → ℕ) {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hT0 : ∀ ζ ∈ T, ζ ≠ 0) :
    (∑ ζ ∈ T.filter (fun ζ => ‖ζ‖ ≤ r), (m ζ : ℝ)) * Real.log (R / r)
      ≤ ∑ ζ ∈ T.filter (fun ζ => ‖ζ‖ ≤ R), (m ζ : ℝ) * Real.log (R / ‖ζ‖) := by
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  have hsub : T.filter (fun ζ => ‖ζ‖ ≤ r) ⊆ T.filter (fun ζ => ‖ζ‖ ≤ R) := by
    intro ζ hζ
    obtain ⟨hζT, hζr⟩ := Finset.mem_filter.mp hζ
    exact Finset.mem_filter.mpr ⟨hζT, le_trans hζr hrR⟩
  have hnonneg : ∀ ζ ∈ T.filter (fun ζ => ‖ζ‖ ≤ R),
      ζ ∉ T.filter (fun ζ => ‖ζ‖ ≤ r) → 0 ≤ (m ζ : ℝ) * Real.log (R / ‖ζ‖) := by
    intro ζ hζ _
    obtain ⟨hζT, hζR⟩ := Finset.mem_filter.mp hζ
    have hζ0 : 0 < ‖ζ‖ := norm_pos_iff.mpr (hT0 ζ hζT)
    have hone : (1 : ℝ) ≤ R / ‖ζ‖ := by
      rw [le_div_iff₀ hζ0]
      linarith
    exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hone)
  have hterm : ∀ ζ ∈ T.filter (fun ζ => ‖ζ‖ ≤ r),
      (m ζ : ℝ) * Real.log (R / r) ≤ (m ζ : ℝ) * Real.log (R / ‖ζ‖) := by
    intro ζ hζ
    obtain ⟨hζT, hζr⟩ := Finset.mem_filter.mp hζ
    have hζ0 : 0 < ‖ζ‖ := norm_pos_iff.mpr (hT0 ζ hζT)
    have hdiv : R / r ≤ R / ‖ζ‖ := by
      refine div_le_div_of_nonneg_left (le_of_lt hR) hζ0 hζr
    have hpos : 0 < R / r := div_pos hR hr
    exact mul_le_mul_of_nonneg_left (Real.log_le_log hpos hdiv) (Nat.cast_nonneg _)
  calc (∑ ζ ∈ T.filter (fun ζ => ‖ζ‖ ≤ r), (m ζ : ℝ)) * Real.log (R / r)
      = ∑ ζ ∈ T.filter (fun ζ => ‖ζ‖ ≤ r), (m ζ : ℝ) * Real.log (R / r) := by
        rw [Finset.sum_mul]
    _ ≤ ∑ ζ ∈ T.filter (fun ζ => ‖ζ‖ ≤ r), (m ζ : ℝ) * Real.log (R / ‖ζ‖) :=
        Finset.sum_le_sum hterm
    _ ≤ ∑ ζ ∈ T.filter (fun ζ => ‖ζ‖ ≤ R), (m ζ : ℝ) * Real.log (R / ‖ζ‖) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg

open scoped Classical in
/-- **`N(r) ≤ n(r)·log(r/t₀)`.**  The reverse comparison: if every zero has modulus at least `t₀`,
the integrated count is at most the raw count times the logarithmic range.  This is the direction
that turns a *lower* bound on the integrated count into one on the raw count. -/
theorem sum_mul_log_le_card_mul_log (T : Finset ℂ) (m : ℂ → ℕ) {r t₀ : ℝ}
    (ht₀ : 0 < t₀) (hmin : ∀ ζ ∈ T, t₀ ≤ ‖ζ‖) :
    ∑ ζ ∈ T.filter (fun ζ => ‖ζ‖ ≤ r), (m ζ : ℝ) * Real.log (r / ‖ζ‖)
      ≤ (∑ ζ ∈ T.filter (fun ζ => ‖ζ‖ ≤ r), (m ζ : ℝ)) * Real.log (r / t₀) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum ?_
  intro ζ hζ
  obtain ⟨hζT, hζr⟩ := Finset.mem_filter.mp hζ
  have hζ0 : 0 < ‖ζ‖ := lt_of_lt_of_le ht₀ (hmin ζ hζT)
  have hr0 : 0 < r := lt_of_lt_of_le hζ0 hζr
  have hdiv : r / ‖ζ‖ ≤ r / t₀ := div_le_div_of_nonneg_left (le_of_lt hr0) ht₀ (hmin ζ hζT)
  have hpos : 0 < r / ‖ζ‖ := div_pos hr0 hζ0
  exact mul_le_mul_of_nonneg_left (Real.log_le_log hpos hdiv) (Nat.cast_nonneg _)

/-- **The raw count from below.**  A lower bound on the integrated count gives one on the raw count,
with the logarithmic range as the only loss. -/
theorem le_sum_of_le_sum_mul_log (T : Finset ℂ) (m : ℂ → ℕ) {r t₀ N : ℝ}
    (ht₀ : 0 < t₀) (ht₀r : t₀ < r) (hmin : ∀ ζ ∈ T, t₀ ≤ ‖ζ‖)
    (hN : N ≤ ∑ ζ ∈ T.filter (fun ζ => ‖ζ‖ ≤ r), (m ζ : ℝ) * Real.log (r / ‖ζ‖)) :
    N / Real.log (r / t₀) ≤ ∑ ζ ∈ T.filter (fun ζ => ‖ζ‖ ≤ r), (m ζ : ℝ) := by
  classical
  have hlog : 0 < Real.log (r / t₀) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ ht₀]
    linarith
  rw [div_le_iff₀ hlog]
  exact le_trans hN (sum_mul_log_le_card_mul_log T m ht₀ hmin)

open scoped Classical in
/-- **Composing the count lower bounds with the growth bound.**  If each block has at least `N i`
zeros in the sub-disc, the growth bound applies with `∑ N i` in place of the exact counts.

Stated against an abstract weight `Lg` and bound `B` so that it composes with
`log_norm_comp_ge_count` without repeating its hypotheses. -/
theorem le_of_counts_and_bound {p : ℕ} {T : Fin p → Finset ℂ} {l : Fin p → ℂ → ℕ}
    {c : ℂ} {R₁ Lg B : ℝ} {N : Fin p → ℝ}
    (hcount : ∀ i : Fin p, N i ≤ ∑ ζ ∈ (T i).filter (fun ζ => ‖ζ - c‖ ≤ R₁), (l i ζ : ℝ))
    (hLg : 0 ≤ Lg)
    (hbound : (∑ i, ∑ ζ ∈ (T i).filter (fun ζ => ‖ζ - c‖ ≤ R₁), (l i ζ : ℝ)) * Lg ≤ B) :
    (∑ i, N i) * Lg ≤ B := by
  refine le_trans (mul_le_mul_of_nonneg_right ?_ hLg) hbound
  exact Finset.sum_le_sum fun i _ => hcount i

/-- The logarithmic weight of the growth bound is nonnegative on the intended range. -/
theorem log_div_nonneg {R R₁ : ℝ} (hR₁ : 0 < R₁) (hR₁R : R₁ ≤ R) :
    0 ≤ Real.log (R / R₁) :=
  Real.log_nonneg (by rw [le_div_iff₀ hR₁]; linarith)

/-! ## From the logarithmic bound to a modulus bound

The growth bound is stated logarithmically, as `B ≤ log M - log ‖F c‖`.  Exponentiating turns it
into what the Clunie weight comparison consumes: the circle supremum is at least `exp B` times the
centre value. -/

/-- **The circle supremum is exponentially large.** -/
theorem exp_mul_le_of_log_bound {F : ℂ → ℂ} {c : ℂ} {M B : ℝ}
    (hM0 : 0 < M) (hFc : 0 < ‖F c‖) (hbound : B ≤ Real.log M - Real.log ‖F c‖) :
    Real.exp B * ‖F c‖ ≤ M := by
  have hstep : B + Real.log ‖F c‖ ≤ Real.log M := by linarith
  have hexp : Real.exp (B + Real.log ‖F c‖) ≤ Real.exp (Real.log M) :=
    Real.exp_le_exp.mpr hstep
  rw [Real.exp_add, Real.exp_log hFc, Real.exp_log hM0] at hexp
  exact hexp

/-! ## The modulus bound at the selection point

The growth bound is about the shifted function `f ∘ g − a`, while the Clunie separation wants
`‖F_last z‖` itself.  The shift costs one additive `‖a‖`, which the exponential absorbs. -/

/-- **The modulus bound at the circle maximum.**  If the growth bound holds with the circle supremum
of `‖F − a‖` bounded by `‖F z‖ + ‖a‖`, the dependent state at the maximum point satisfies the
modulus bound the Clunie separation consumes, up to the additive shift. -/
theorem exp_mul_sub_le_of_max {F : ℂ → ℂ} {a c z : ℂ} {B : ℝ}
    (hFc : 0 < ‖F c - a‖) (hpos : 0 < ‖F z‖ + ‖a‖)
    (hbound : B ≤ Real.log (‖F z‖ + ‖a‖) - Real.log ‖F c - a‖) :
    Real.exp B * ‖F c - a‖ - ‖a‖ ≤ ‖F z‖ := by
  have h := exp_mul_le_of_log_bound (F := fun _ => F c - a) (c := c)
    (M := ‖F z‖ + ‖a‖) (B := B) hpos hFc hbound
  linarith

/-- The circle supremum of the shifted function is bounded by the maximum plus the shift. -/
theorem norm_sub_le_of_max {F : ℂ → ℂ} {a : ℂ} {c z : ℂ} {R : ℝ}
    (hmax : ∀ w ∈ Metric.sphere c R, ‖F w‖ ≤ ‖F z‖) :
    ∀ w ∈ Metric.sphere c R, ‖F w - a‖ ≤ ‖F z‖ + ‖a‖ := by
  intro w hw
  calc ‖F w - a‖ ≤ ‖F w‖ + ‖a‖ := norm_sub_le _ _
    _ ≤ ‖F z‖ + ‖a‖ := by linarith [hmax w hw]

end GaloisForLFunctions.HTGeometry
