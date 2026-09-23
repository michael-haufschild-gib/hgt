import GaloisForLFunctions.HTGeometry.ExpPolyIsolatedZeros

/-!
# From isolated zeros to a finite zero set

Isolated zeros on a compact interval are finitely many: an infinite zero set would admit an injective
sequence, Bolzano–Weierstrass would give a convergent subsequence, and injectivity puts infinitely
many of its terms away from the limit — an accumulation point of zeros.

For an exponential polynomial `ExpPolyIsolatedZeros` rules that out, so a nonzero exponential
polynomial has a finite zero set on every compact interval.  Together with the arch bounds this is
the structural hypothesis the Sturm descent needs.

A second structural fact is recorded here: where the Sturm expression is positive, `f` cannot touch
zero from below.  Every zero is a crossing or a local minimum, so negative arches are separated by
positive ones — which are long — and the total zero count is controlled by the positive arches alone.
-/

open Set Filter

namespace GaloisForLFunctions.HTGeometry

/-- **Isolated zeros on a compact interval are finitely many.** -/
theorem finite_zeros_of_not_accumZero {f : ℝ → ℝ} {a b : ℝ}
    (h : ∀ t₀ ∈ Icc a b, ¬ AccumZero f t₀) :
    {t : ℝ | t ∈ Icc a b ∧ f t = 0}.Finite := by
  by_contra hinf
  set Z : Set ℝ := {t : ℝ | t ∈ Icc a b ∧ f t = 0} with hZ
  have hinf' : Z.Infinite := hinf
  set x : ℕ → ℝ := fun n => ((Set.Infinite.natEmbedding Z hinf' n : Z) : ℝ) with hx
  have hxmem : ∀ n, x n ∈ Icc a b := fun n => (Set.Infinite.natEmbedding Z hinf' n).2.1
  have hxzero : ∀ n, f (x n) = 0 := fun n => (Set.Infinite.natEmbedding Z hinf' n).2.2
  have hxinj : Function.Injective x := by
    intro m n hmn
    exact (Set.Infinite.natEmbedding Z hinf').injective (Subtype.ext hmn)
  obtain ⟨t₀, ht₀, φ, hφ, htend⟩ := isCompact_Icc.tendsto_subseq hxmem
  have hinj' : Function.Injective (fun n => x (φ n)) := fun m n hmn =>
    hφ.injective (hxinj hmn)
  refine h t₀ ht₀ ?_
  intro ε hε
  have hev : ∀ᶠ n in atTop, |x (φ n) - t₀| < ε := by
    rw [Metric.tendsto_atTop] at htend
    obtain ⟨N, hN⟩ := htend ε hε
    filter_upwards [eventually_ge_atTop N] with n hn
    have := hN n hn
    rwa [Real.dist_eq] at this
  have hne : ∀ᶠ n in atTop, x (φ n) ≠ t₀ := by
    by_cases hex : ∃ n₀, x (φ n₀) = t₀
    · obtain ⟨n₀, hn₀⟩ := hex
      filter_upwards [eventually_ne_atTop n₀] with n hn hcon
      exact hn (hinj' (by simp only []; rw [hcon, hn₀]))
    · push Not at hex
      exact Filter.Eventually.of_forall hex
  obtain ⟨n, hn1, hn2⟩ := (hev.and hne).exists
  exact ⟨x (φ n), hn2, hn1, hxzero (φ n)⟩

/-- **A nonzero exponential polynomial has finitely many zeros on a compact interval.** -/
theorem finite_zeros_expPoly {S : Finset ℂ} {C : ℂ → ℂ} {a b : ℝ} {y₀ : ℂ}
    (hy₀ : y₀ ∈ S) (hC : C y₀ ≠ 0)
    (hreal : ∀ t : ℝ, (∑ y ∈ S, C y * Complex.exp (y * t)).im = 0) :
    {t : ℝ | t ∈ Icc a b ∧ (∑ y ∈ S, C y * Complex.exp (y * t)).re = 0}.Finite :=
  finite_zeros_of_not_accumZero (fun _ _ => not_accumZero_of_coeff_ne hy₀ hC hreal)

/-! ## No touching zeros where the Sturm expression is positive -/

/-- **Zeros are crossings or minima.**  Where `f'' + γ² f > 0`, the function cannot attain the value
`0` at a local maximum, so it cannot touch zero from below. -/
theorem not_isLocalMax_of_sturm_pos {f fd fdd h : ℝ → ℝ} {γ t₀ : ℝ}
    (hf : ∀ t, HasDerivAt f (fd t) t) (hfd : ∀ t, HasDerivAt fd (fdd t) t)
    (hh : ∀ t, h t = fdd t + γ ^ (2 : ℕ) * f t) (hpos : 0 < h t₀) (hz : f t₀ = 0) :
    ¬ IsLocalMax f t₀ := by
  intro hmax
  -- the first derivative vanishes and the second is positive
  have hfd0 : fd t₀ = 0 := by
    have := hmax.deriv_eq_zero
    rwa [(hf t₀).deriv] at this
  have hfdd : 0 < fdd t₀ := by
    have := hpos
    rw [hh, hz] at this
    linarith
  -- hence the derivative is positive just to the right
  have hslope := hasDerivAt_iff_tendsto_slope.mp (hfd t₀)
  have hev : ∀ᶠ s in nhdsWithin t₀ (Ioi t₀), 0 < slope fd t₀ s := by
    refine (hslope.mono_left (nhdsWithin_mono t₀ (?_ : Ioi t₀ ⊆ ({t₀}ᶜ : Set ℝ)))).eventually
      (eventually_gt_nhds hfdd)
    exact fun x hx => ne_of_gt hx
  have hevfd : ∀ᶠ s in nhdsWithin t₀ (Ioi t₀), 0 < fd s := by
    filter_upwards [hev, self_mem_nhdsWithin] with s hs hs2
    have hgt : t₀ < s := hs2
    rw [slope_def_field, hfd0] at hs
    rcases div_pos_iff.mp hs with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith
    · linarith
  -- and the maximum property fails just to the right
  rw [eventually_nhdsWithin_iff] at hevfd
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hevfd
  obtain ⟨η, hη, hmaxball⟩ := Metric.eventually_nhds_iff.mp hmax
  set r : ℝ := min (δ / 2) (η / 2) with hr
  have hrpos : 0 < r := by rw [hr]; positivity
  have hmono : StrictMonoOn f (Icc t₀ (t₀ + r)) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t _ => (hf t).continuousAt.continuousWithinAt) ?_
    intro s hs
    rw [interior_Icc] at hs
    rw [(hf s).deriv]
    refine hball ?_ hs.1
    rw [Real.dist_eq, abs_of_pos (by linarith [hs.1])]
    have hrδ : r ≤ δ / 2 := min_le_left _ _
    linarith [hs.2]
  have hlt : f t₀ < f (t₀ + r) :=
    hmono (left_mem_Icc.mpr (by linarith)) (right_mem_Icc.mpr (by linarith)) (by linarith)
  have hle : f (t₀ + r) ≤ f t₀ := by
    refine hmaxball ?_
    rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hrpos]
    have : r ≤ η / 2 := min_le_right _ _
    linarith
  linarith

end GaloisForLFunctions.HTGeometry
