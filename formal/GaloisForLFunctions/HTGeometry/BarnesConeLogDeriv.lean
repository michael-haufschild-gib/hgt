import GaloisForLFunctions.HTGeometry.BarnesConeProduct

/-!
# The rational atom of one Barnes cone factor, and the ladder reindexing

The logarithmic derivative of a single genus-`N` cone factor collapses to a rational atom: the
exponential correction cancels between numerator and denominator, and the geometric telescoping
already built into the derivative of the elementary factor leaves

```text
logDeriv (z ↦ E_N(-z/w)) (z) = (-z/w)^N / (w + z).
```

The ladder of the Barnes hierarchy is a reindexing of the cone by one direction.  Adding the unit
vector in the direction `j` shifts the cone value by `ω_j`, and the slice on which the `j`-th
exponent vanishes is the cone of the frame with `ω_j` deleted.  Those are the two combinatorial
identities the ladder is assembled from.
-/

open Complex Set Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-! ## Nonvanishing of a nonzero cone value -/

theorem conePeriod_ne_zero (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) {n : ι → ℕ} (hn : n ≠ 0) :
    conePeriod ω n ≠ 0 := by
  classical
  obtain ⟨δ, hδpos, hδ⟩ := exists_pos_le_im ω hω
  obtain ⟨i₀, hi₀⟩ : ∃ i, n i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hn (funext fun i => hcon i)
  have hone : (1 : ℝ) ≤ ∑ i, (n i : ℝ) := by
    have hle : (n i₀ : ℝ) ≤ ∑ k, (n k : ℝ) :=
      Finset.single_le_sum (f := fun k => (n k : ℝ)) (fun k _ => Nat.cast_nonneg _)
        (Finset.mem_univ i₀)
    have h1 : (1 : ℝ) ≤ (n i₀ : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hi₀
    linarith
  have hpos : 0 < ‖conePeriod ω n‖ := by
    have := mul_sum_le_norm_conePeriod ω hδ n
    nlinarith
  exact norm_pos_iff.mp hpos

/-! ## The ladder reindexing of the cone -/

omit [Nonempty ι] in
/-- **Shifting the exponent by one unit shifts the cone value by that period.** -/
theorem conePeriod_add_single [DecidableEq ι] (ω : ι → ℂ) (n : ι → ℕ) (j : ι) :
    conePeriod ω (n + Pi.single j 1) = conePeriod ω n + ω j := by
  classical
  have hterm : ∀ i : ι, (((n + Pi.single j 1 : ι → ℕ) i : ℕ) : ℂ) * ω i =
      (n i : ℂ) * ω i + (if i = j then ω i else 0) := by
    intro i
    by_cases h : i = j
    · subst h
      simp
      ring
    · simp [h]
  rw [conePeriod, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i,
    Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ j]
  simp [conePeriod]

omit [Nonempty ι] in
/-- **The vanishing slice is the deleted-frame cone.** -/
theorem conePeriod_eq_sum_erase_of_eq_zero [DecidableEq ι] (ω : ι → ℂ) {n : ι → ℕ} {j : ι}
    (hj : n j = 0) :
    conePeriod ω n = ∑ i ∈ Finset.univ.erase j, (n i : ℂ) * ω i := by
  rw [conePeriod, ← Finset.sum_erase_add _ _ (Finset.mem_univ j), hj]
  simp

/-! ## The rational atom of one factor -/

/-- **The logarithmic derivative of one cone factor.**  The exponential correction cancels and the
collapsed derivative leaves a single rational atom. -/
theorem logDeriv_barnesConeFactor (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) {n : ι → ℕ} (hn : n ≠ 0)
    (z : ℂ) (hz : conePeriod ω n + z ≠ 0) :
    logDeriv (barnesConeFactor ω n) z =
      (-(z / conePeriod ω n)) ^ Fintype.card ι / (conePeriod ω n + z) := by
  have hw : conePeriod ω n ≠ 0 := conePeriod_ne_zero ω hω hn
  have hfun : barnesConeFactor ω n =
      fun y : ℂ => weierstrassFactor (Fintype.card ι) (-(y / conePeriod ω n)) := by
    funext y
    rw [barnesConeFactor, if_neg hn]
  have hdiv : HasDerivAt (fun y : ℂ => y / conePeriod ω n) (1 / conePeriod ω n) z := by
    simpa using (hasDerivAt_id z).div_const (conePeriod ω n)
  have harg : HasDerivAt (fun y : ℂ => -(y / conePeriod ω n))
      (-(1 / conePeriod ω n)) z := hdiv.fun_neg
  have hcomp := (hasDerivAt_weierstrassFactor (Fintype.card ι)
    (-(z / conePeriod ω n))).comp z harg
  have hfac : HasDerivAt (barnesConeFactor ω n)
      (-((-(z / conePeriod ω n)) ^ Fintype.card ι) *
        Complex.exp (weierstrassLog (Fintype.card ι) (-(z / conePeriod ω n))) *
          -(1 / conePeriod ω n)) z := by
    rw [hfun]
    exact hcomp
  have hone : (1 : ℂ) - -(z / conePeriod ω n) ≠ 0 := by
    intro hcon
    apply hz
    have hmul : conePeriod ω n * (1 - -(z / conePeriod ω n)) = conePeriod ω n + z := by
      rw [sub_neg_eq_add]
      field_simp
    rw [hcon, mul_zero] at hmul
    exact hmul.symm
  rw [logDeriv_apply, hfac.deriv, hfun]
  simp only [weierstrassFactor]
  have hexp : Complex.exp (weierstrassLog (Fintype.card ι) (-(z / conePeriod ω n))) ≠ 0 :=
    Complex.exp_ne_zero _
  have hz' : z + conePeriod ω n ≠ 0 := by
    rw [add_comm]
    exact hz
  have hcancel : (z + conePeriod ω n) * (z + conePeriod ω n)⁻¹ = 1 := mul_inv_cancel₀ hz'
  field_simp
  linear_combination (z ^ Fintype.card ι * (conePeriod ω n)⁻¹ ^ Fintype.card ι *
    (-1 : ℂ) ^ Fintype.card ι) * hcancel

end

end GaloisForLFunctions
