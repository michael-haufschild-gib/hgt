import GaloisForLFunctions.ConstituentTheoryOfTheZeros.NoAbsolutelyConvergentExpansionIsAConstituentInAStrip

/-!
# Infinitely many zeros of an expansion are not zeros of `ξ`

Let `F(s) = Σ_q c(q) q^s`, `q` over the positive reals, converge absolutely on the closed strip
`|Re s − ½| ≤ ω`, `F ≢ 0`, and let `F` have a zero in the open strip.

**Theorem** (`infinite_zeros_not_xi_zeros_of_expansion`). Infinitely many zeros of `F` in the open
strip are not zeros of `ξ`.

So the zero set of `F` in the strip is not contained in the zero set of `ξ` up to finitely many
points: no finite correction of an almost periodic pattern lies among the zeros of `ξ`.

* Purity with exceptions (`re_eq_half_of_strip_zeros_subset_xi_off_finite`): a zero off the line
  recurs along a set of heights of positive lower density; above the heights of the finitely many
  exceptions its recurrences are zeros of `ζ`, whose shifts have density zero.
* On the line, the finitely many exceptional zeros are poles of `−ζ F'/(sF)`; the jump law with
  poles (`expansion_ne_zero_of_zeros_cancelled_off_finset`) still identifies the expansions of
  `F'/F` on the two sides of the line, and `F` has no zero at all.

The same holds for Dirichlet series (`infinite_zeros_not_xi_zeros_of_LSeries`) and for exponential
polynomials with real frequencies (`infinite_zeros_not_xi_zeros_of_expSum`), in every strip about
the line.
-/

open Complex Filter Topology Set Metric MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.InfiniteRankPurityTheory

variable {c : Scale → ℂ}

/-- **A constituent up to finitely many zeros is pure.** If all but finitely many zeros of an
absolutely convergent expansion in a strip about the critical line are zeros of `ξ`, all its
zeros in the strip lie on the line. -/
theorem re_eq_half_of_strip_zeros_subset_xi_off_finite {ω : ℝ} (hω : ω ≤ 1 / 2)
    (hc : WSummable (1 / 2 - ω) (1 / 2 + ω) c) (hne : c ≠ 0)
    (hfin : {z : ℂ | |z.re - 1 / 2| < ω ∧ expansion c z = 0 ∧ xi z ≠ 0}.Finite) {ρ₀ : ℂ}
    (hρ : |ρ₀.re - 1 / 2| < ω) (hρ0 : expansion c ρ₀ = 0) : ρ₀.re = 1 / 2 := by
  by_contra hne'
  have hω0 : 0 < ω := lt_of_le_of_lt (abs_nonneg _) hρ
  have hρ' := abs_lt.mp hρ
  obtain ⟨r, hr, hdens⟩ := exists_zetaZeroShiftSet_density_zero (ρ₀ := ρ₀)
    (by linarith [hρ'.1]) (by linarith [hρ'.2]) hne'
  -- a height above the exceptional zeros
  obtain ⟨B, hB⟩ := (hfin.image fun z : ℂ => |z.im|).bddAbove
  have hB' : ∀ z : ℂ, |z.re - 1 / 2| < ω → expansion c z = 0 → xi z ≠ 0 → |z.im| ≤ B :=
    fun z h1 h2 h3 => hB ⟨z, ⟨h1, h2, h3⟩, rfl⟩
  -- a point of the strip where the expansion does not vanish
  have hFne : ∃ z₁ : ℂ, (1 / 2 - ω < z₁.re ∧ z₁.re < 1 / 2 + ω) ∧ expansion c z₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine hne (eq_zero_of_expansion_eq_zero (le_refl (1 / 2 : ℝ))
      (hc.mono (by linarith) le_rfl (by linarith)) fun z h1 h2 => ?_)
    have hre : z.re = 1 / 2 := le_antisymm h2 h1
    exact hcon z ⟨by rw [hre]; linarith, by rw [hre]; linarith⟩
  set R : ℝ := (ω - |ρ₀.re - 1 / 2|) / 2 with hR
  have hRpos : 0 < R := by
    rw [hR]
    linarith
  have hAP : IsStripAlmostPeriodicOn (expansion c) ρ₀.re R :=
    isStripAlmostPeriodicOn_expansion (hc.mono
      (by rcases abs_cases (ρ₀.re - 1 / 2) with ⟨hab, _⟩ | ⟨hab, _⟩ <;> rw [hR, hab] <;> linarith)
      (by linarith)
      (by rcases abs_cases (ρ₀.re - 1 / 2) with ⟨hab, _⟩ | ⟨hab, _⟩ <;> rw [hR, hab] <;> linarith))
  set r' : ℝ := min r (ω - |ρ₀.re - 1 / 2|) with hr'
  have hr'pos : 0 < r' := lt_min hr (by linarith)
  obtain ⟨L, hL, d, hd, hthick⟩ := exists_thick_zero_shifts_on_strip
    (differentiableOn_expansion hc) hFne (by linarith [hρ'.1]) (by linarith [hρ'.2]) hρ0 hRpos
    hAP hr'pos
  -- above the height `T₂` every recurrence is a zero of `ζ`
  set T₂ : ℝ := max B 0 + |ρ₀.im| + r' + 1 with hT₂
  have hT₂0 : 0 ≤ T₂ := by
    rw [hT₂]
    linarith [le_max_right B 0, abs_nonneg ρ₀.im]
  have hthick' : ∀ y : ℝ, ∃ τ ∈ Icc y (y + L),
      Ioo (τ - d) (τ + d) ⊆ zetaZeroShiftSet ρ₀ r ∪ Iic T₂ := by
    intro y
    obtain ⟨τ, hτ, hsub⟩ := hthick y
    refine ⟨τ, hτ, fun t ht => ?_⟩
    by_cases htT : t ≤ T₂
    · exact Or.inr htT
    left
    obtain ⟨z, hz, hz0⟩ := hsub ht
    have hzr : ‖z - ρ₀‖ < r' := mem_ball_iff_norm.mp hz
    have hzre := abs_lt.mp ((abs_re_le_norm (z - ρ₀)).trans_lt hzr)
    have hzim := abs_lt.mp ((abs_im_le_norm (z - ρ₀)).trans_lt hzr)
    rw [sub_re] at hzre
    rw [sub_im] at hzim
    have hre : (z + (t : ℂ) * I).re = z.re := by simp
    have him : (z + (t : ℂ) * I).im = z.im + t := by simp
    have hstrip : |(z + (t : ℂ) * I).re - 1 / 2| < ω := by
      rw [hre]
      have h2 : r' ≤ ω - |ρ₀.re - 1 / 2| := min_le_right _ _
      rcases abs_cases (ρ₀.re - 1 / 2) with ⟨hab, _⟩ | ⟨hab, _⟩ <;>
        rw [hab] at h2 <;> rw [abs_lt] <;> constructor <;> linarith [hzre.1, hzre.2]
    have hxiz : xi (z + (t : ℂ) * I) = 0 := by
      by_contra hx
      have hle := hB' _ hstrip hz0 hx
      rw [him] at hle
      have h1 := (abs_le.mp hle).2
      have h2 := neg_abs_le ρ₀.im
      have h3 := le_max_left B 0
      rw [hT₂] at htT
      linarith [hzim.1]
    refine ⟨z, ball_subset_ball (min_le_left _ _) hz, ?_⟩
    exact (xi_eq_zero_iff (re_pos_of_xi_eq_zero hxiz) fun h => by
      have := re_lt_one_of_xi_eq_zero hxiz
      rw [h, one_re] at this
      exact lt_irrefl _ this).mp hxiz
  -- positive lower density against density zero
  have hlow := eventually_le_volume_of_relativelyDense hL hd hthick'
  have hκ0 : 0 < d / (L + 2 * d) := by positivity
  have hup := hdens (d / (L + 2 * d) / 2) (by positivity)
  obtain ⟨T, hT1, hT2, hT0, hT3⟩ := (hlow.and (hup.and ((eventually_gt_atTop 0).and
    (eventually_gt_atTop (2 * T₂ / (d / (L + 2 * d))))))).exists
  have hsub : (zetaZeroShiftSet ρ₀ r ∪ Iic T₂) ∩ Icc 0 T ⊆
      (zetaZeroShiftSet ρ₀ r ∩ Icc 0 T) ∪ Icc 0 T₂ := by
    rintro t ⟨ht | ht, htI⟩
    · exact Or.inl ⟨ht, htI⟩
    · exact Or.inr ⟨htI.1, ht⟩
  have hvol : volume ((zetaZeroShiftSet ρ₀ r ∪ Iic T₂) ∩ Icc 0 T) ≤
      ENNReal.ofReal (d / (L + 2 * d) / 2 * T + T₂) := by
    refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
    rw [Real.volume_Icc, sub_zero, ENNReal.ofReal_add (by positivity) hT₂0]
    exact add_le_add hT2 le_rfl
  have h := hT1.trans hvol
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  rw [div_lt_iff₀ hκ0] at hT3
  nlinarith [mul_pos hκ0 hT0]

/-- **Infinitely many zeros of an expansion are not zeros of `ξ`.** Let `F(s) = Σ_q c(q) q^s`,
over the positive reals, converge absolutely on the closed strip `|Re s − ½| ≤ ω`, `0 < ω ≤ ½`,
and not vanish identically. If `F` has a zero in the open strip, infinitely many of its zeros
there are not zeros of `ξ`. -/
theorem infinite_zeros_not_xi_zeros_of_expansion {ω : ℝ} (hω0 : 0 < ω) (hω : ω ≤ 1 / 2)
    (hc : WSummable (1 / 2 - ω) (1 / 2 + ω) c) (hne : c ≠ 0) {s : ℂ} (hs : |s.re - 1 / 2| < ω)
    (hs0 : expansion c s = 0) :
    {z : ℂ | |z.re - 1 / 2| < ω ∧ expansion c z = 0 ∧ xi z ≠ 0}.Infinite := by
  intro hfin
  have hpure : ∀ z : ℂ, |z.re - 1 / 2| < ω → expansion c z = 0 → z.re = 1 / 2 := fun z hz hz0 =>
    re_eq_half_of_strip_zeros_subset_xi_off_finite hω hc hne hfin hz hz0
  have hω2 : 2 * (ω / 2) = ω := by ring
  refine expansion_ne_zero_of_zeros_cancelled_off_finset (η := ω / 2) (by positivity)
    (by linarith) (by rwa [hω2])
    (isStripAlmostPeriodicOn_expansion (hc.mono (by linarith) (by linarith) (by linarith)))
    (fun z hz hre hz0 => hre (hpure z (by rwa [hω2] at hz) hz0)) hfin.toFinset
    (fun p hp => hpure p (hfin.mem_toFinset.mp hp).1 (hfin.mem_toFinset.mp hp).2.1)
    (fun p hp => (hfin.mem_toFinset.mp hp).2.1) (fun z hre hz0 hzP => ?_) hne
    (by rwa [hω2]) hs0
  have hz : |z.re - 1 / 2| < ω := by rw [hre, sub_self, abs_zero]; exact hω0
  have hxiz : xi z = 0 := by
    by_contra hx
    exact hzP (hfin.mem_toFinset.mpr ⟨hz, hz0, hx⟩)
  exact (xi_eq_zero_iff (by rw [hre]; norm_num) fun h => by
    have := re_lt_one_of_xi_eq_zero hxiz
    rw [h, one_re] at this
    exact lt_irrefl _ this).mp hxiz

/-- **Dirichlet series.** An absolutely convergent Dirichlet series, not identically zero, with a
zero in a strip about the line inside its half-plane of absolute convergence has infinitely many
zeros in the strip that are not zeros of `ξ`. -/
theorem infinite_zeros_not_xi_zeros_of_LSeries {a : ℕ → ℂ} {x : ℝ} (hsum : LSeriesSummable a x)
    {ω : ℝ} (hω0 : 0 < ω) (hω : ω ≤ 1 / 2) (hx : x ≤ 1 / 2 - ω) {n : ℕ} (hn : a (n + 1) ≠ 0)
    {s : ℂ} (hs : |s.re - 1 / 2| < ω) (hs0 : LSeries a s = 0) :
    {z : ℂ | |z.re - 1 / 2| < ω ∧ LSeries a z = 0 ∧ xi z ≠ 0}.Infinite := by
  have hre : ∀ z : ℂ, |z.re - 1 / 2| < ω → x ≤ z.re := fun z hz => by
    linarith [(abs_lt.mp hz).1]
  refine (infinite_zeros_not_xi_zeros_of_expansion hω0 hω
    (wsummable_dirichletCoeff hsum hx (by linarith)) (dirichletCoeff_ne_zero hn) hs
    (by rw [expansion_dirichletCoeff hsum (hre s hs)]; exact hs0)).mono fun z hz => ?_
  exact ⟨hz.1, by rw [← expansion_dirichletCoeff hsum (hre z hz.1)]; exact hz.2.1, hz.2.2⟩

/-- **Exponential polynomials.** An exponential polynomial with distinct real frequencies, not
identically zero, with a zero in a strip about the line has infinitely many zeros in the strip
that are not zeros of `ξ`. -/
theorem infinite_zeros_not_xi_zeros_of_expSum {n : ℕ} (a : Fin n → ℂ) {lam : Fin n → ℝ}
    (hinj : Function.Injective lam) {k : Fin n} (hk : a k ≠ 0) {ω : ℝ} (hω0 : 0 < ω)
    (hω : ω ≤ 1 / 2) {s : ℂ} (hs : |s.re - 1 / 2| < ω) (hs0 : expSum a lam s = 0) :
    {z : ℂ | |z.re - 1 / 2| < ω ∧ expSum a lam z = 0 ∧ xi z ≠ 0}.Infinite := by
  refine (infinite_zeros_not_xi_zeros_of_expansion hω0 hω (wsummable_expCoeff a lam _ _)
    (fun h => hk (by rw [← expCoeff_ofLog a hinj k, h, Pi.zero_apply])) hs
    (by rw [expansion_expCoeff a hinj]; exact hs0)).mono fun z hz => ?_
  exact ⟨hz.1, by rw [← expansion_expCoeff a hinj]; exact hz.2.1, hz.2.2⟩

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
