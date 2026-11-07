import GaloisForLFunctions.BlackHoleRingdown.TheHorocycleReadsTheZeros

/-!
# The Farey reading of the horocycle

A source on the modular horizon is a height profile `ψ`; its pseudo-Eisenstein series
`F_ψ(z) = Σ_{(c,d) coprime} ψ(Im M_{c,d} z)` sums the profile over the cusp images `γ∞ = -d/c` of
`SL₂(ℤ)`. For an indicator profile it is an integer, the **shell count**: the number of cusp images
whose horoball shell between depths `a` and `b` contains `z` (`pseudoEisenstein_shell`).

**The horocycle mean is a count of Farey points.** Along the closed horocycle of height `y`, the cusp
images with denominator `c` are the `φ(c)` Farey fractions `d/c` with `d` coprime to `c`, and each
contributes the same kernel, the time the horocycle spends in its horoball shells
(`fareyKernel`). So (`horocycleMean_eq_fareySum`)

  `∫₀¹ F_ψ(x + iy) dx = 2ψ(y) + 2 Σ_{c ≥ 1} φ(c) ∫_ℝ ψ(y / (c²(v² + y²))) dv`,

a finite sum: denominators with `c² y > 1/a` see nothing. The echo integers of the cusp are the
totients, and the thermalization of a long horocycle is the equidistribution of the Farey points of
order `≈ y^{-1/2}`. With Zagier's theorem this reads (`riemannHypothesis_iff_fareyCount_rate`): RH
holds iff every smooth totient-weighted Farey count reaches its limit at rate `y^{3/4-ε}`. The exponent
`3/4 = 1/2 + 1/4` is the square-root size of the count of order `C = y^{-1/2}` relative to its
volume `C²`, plus the universal damping rate.

The unfolding is elementary: a window of `c` consecutive integers contains exactly `φ(c)` integers
coprime to `c` (`card_coprime_Ico`), so every point of the line is covered `φ(c)` times by the
intervals `(d, d + c]` of the coprime `d` (`sum_indicator_coprime`, `integral_sum_coprime`).
-/

open MeasureTheory Set Finset UpperHalfPlane EisensteinSeries
open scoped MatrixGroups

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open BlackHoleRingdown HTGeometry

/-! ### Coprime residues and the unfolding of one denominator -/

/-- The integers coprime to `c` in any window of `c` consecutive integers are `φ(c)` in number. -/
theorem card_coprime_Ico (c : ℕ) (m : ℤ) :
    ((Finset.Ico m (m + c)).filter (fun d => IsCoprime (c : ℤ) d)).card = c.totient := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · simp
  set k : ℤ := (m.natAbs : ℤ)
  have hk : 0 ≤ m + c * k := by
    have h1 : (1 : ℤ) ≤ c := by exact_mod_cast hc
    have h2 : -m ≤ k := by simp only [k]; rw [← Int.abs_eq_natAbs]; exact neg_le_abs m
    have h3 : (0 : ℤ) ≤ k := by simp only [k]; positivity
    nlinarith
  have hshift : ((Finset.Ico m (m + c)).filter (fun d => IsCoprime (c : ℤ) d)).card =
      ((Finset.Ico (m + c * k) (m + c * k + c)).filter (fun d => IsCoprime (c : ℤ) d)).card := by
    refine Finset.card_bij (fun d _ => d + c * k) (fun d hd => ?_) (fun a _ b _ h => by linarith)
      (fun b hb => ⟨b - c * k, ?_, by ring⟩)
    · simp only [Finset.mem_filter, Finset.mem_Ico] at hd ⊢
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      exact IsCoprime.add_mul_left_right hd.2 k
    · simp only [Finset.mem_filter, Finset.mem_Ico] at hb ⊢
      refine ⟨⟨by linarith, by linarith⟩, ?_⟩
      have := IsCoprime.add_mul_left_right hb.2 (-k)
      rwa [show b + c * -k = b - c * k by ring] at this
  rw [hshift]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = m + c * k := ⟨(m + c * k).toNat, Int.toNat_of_nonneg hk⟩
  rw [← hN, ← Nat.filter_coprime_Ico_eq_totient c N]
  symm
  refine Finset.card_bij (fun x _ => (x : ℤ)) (fun x hx => ?_) (fun a _ b _ h => by exact_mod_cast h)
    (fun b hb => ?_)
  · simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢
    refine ⟨⟨by exact_mod_cast hx.1.1, by exact_mod_cast hx.1.2⟩, ?_⟩
    exact Nat.isCoprime_iff_coprime.mpr hx.2
  · simp only [Finset.mem_filter, Finset.mem_Ico] at hb
    have hb0 : 0 ≤ b := le_trans (by positivity) hb.1.1
    refine ⟨b.toNat, ?_, Int.toNat_of_nonneg hb0⟩
    simp only [Finset.mem_filter, Finset.mem_Ico]
    have hb' : ((b.toNat : ℕ) : ℤ) = b := Int.toNat_of_nonneg hb0
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [← Nat.isCoprime_iff_coprime, hb']
    exact hb.2

/-- **Each point is covered `φ(c)` times** by the intervals `(d, d + c]` with `d` coprime to `c`, once
the window `[-D, D]` contains all the `d` that can cover it. -/
theorem sum_indicator_coprime {c : ℕ} {D : ℤ} {u : ℝ} (hlo : -(D : ℝ) ≤ u - c)
    (hhi : u ≤ D) :
    ∑ d ∈ (Finset.Icc (-D) D).filter (fun d => IsCoprime (c : ℤ) d),
      (Set.Ioc (d : ℝ) (d + c)).indicator (fun _ => (1 : ℂ)) u = c.totient := by
  rw [Finset.sum_indicator_eq_sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  rw [Finset.filter_filter]
  have hset : (Finset.Icc (-D) D).filter (fun d => IsCoprime (c : ℤ) d ∧ u ∈ Set.Ioc (d : ℝ) (d + c)) =
      (Finset.Ico (⌈u⌉ - c) (⌈u⌉ - c + c)).filter (fun d => IsCoprime (c : ℤ) d) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico, Set.mem_Ioc]
    constructor
    · rintro ⟨-, hcop, h1, h2⟩
      refine ⟨⟨?_, ?_⟩, hcop⟩
      · have : u - c ≤ d := by linarith
        have := Int.ceil_le.mpr (show u - (c : ℝ) ≤ ((d : ℤ) : ℝ) by exact_mod_cast this)
        rw [show u - (c : ℝ) = u + ((-(c : ℤ) : ℤ) : ℝ) by push_cast; ring, Int.ceil_add_intCast] at this
        linarith
      · have := Int.lt_ceil.mpr (show ((d : ℤ) : ℝ) < u by exact_mod_cast h1)
        linarith
    · rintro ⟨⟨h1, h2⟩, hcop⟩
      have hd1 : (d : ℝ) < u := Int.lt_ceil.mp (by linarith)
      have hd2 : u ≤ d + c := by
        have h3 : ⌈u⌉ ≤ d + c := by linarith
        have := Int.le_ceil u
        have h4 : ((⌈u⌉ : ℤ) : ℝ) ≤ ((d + c : ℤ) : ℝ) := by exact_mod_cast h3
        push_cast at h4
        linarith
      refine ⟨⟨?_, ?_⟩, hcop, hd1, hd2⟩
      · have : (-(D : ℝ)) ≤ d := by linarith
        exact_mod_cast this
      · have : (d : ℝ) ≤ D := by linarith
        exact_mod_cast this
  rw [hset, card_coprime_Ico]

/-- **Unfolding along the closed horocycle.** For `c ≥ 1` and a continuous `g` vanishing outside
`[-U, U]`, the mean over `[0, 1)` of the sum of `g(c x + d)` over the `d` coprime to `c` is
`φ(c)/c ∫ g`. -/
theorem integral_sum_coprime {c : ℕ} (hc : 1 ≤ c) {g : ℝ → ℂ} (hgi : Integrable g) {U : ℝ}
    (hgU : ∀ u, U < |u| → g u = 0) {D : ℤ} (hD : U + c ≤ D) :
    ∑ d ∈ (Finset.Icc (-D) D).filter (fun d => IsCoprime (c : ℤ) d),
      ∫ x in Ico (0 : ℝ) 1, g (c * x + d) = ((c.totient : ℂ) / c) * ∫ u, g u := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  -- one row: the substitution `u = c x + d`
  have hrow (d : ℤ) : ∫ x in Ico (0 : ℝ) 1, g (c * x + d) =
      (c : ℂ)⁻¹ * ∫ u, (Set.Ioc (d : ℝ) (d + c)).indicator g u := by
    rw [integral_Ico_eq_integral_Ioo, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_comp_mul_add (fun u => g u) hc0.ne', mul_zero, mul_one, zero_add,
      intervalIntegral.integral_of_le (by linarith), integral_indicator measurableSet_Ioc, add_comm (c : ℝ)]
    simp [Complex.real_smul]
  simp only [hrow]
  rw [← Finset.mul_sum, ← integral_finsetSum _ fun d _ => (hgi.indicator measurableSet_Ioc)]
  have hpt : ∀ u, ∑ d ∈ (Finset.Icc (-D) D).filter (fun d => IsCoprime (c : ℤ) d),
      (Set.Ioc (d : ℝ) (d + c)).indicator g u = (c.totient : ℂ) * g u := by
    intro u
    by_cases hu : U < |u|
    · rw [hgU u hu, mul_zero]
      exact Finset.sum_eq_zero fun d _ => by simp [Set.indicator_apply, hgU u hu]
    · push Not at hu
      have h := sum_indicator_coprime (c := c) (D := D) (u := u) (by linarith [neg_abs_le u])
        (by linarith [le_abs_self u])
      rw [← h, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hm : u ∈ Set.Ioc (d : ℝ) (d + c)
      · simp [Set.indicator_of_mem hm]
      · simp [Set.indicator_of_notMem hm]
  simp only [hpt]
  rw [integral_const_mul]
  field_simp


/-! ### Rows on the closed horocycle -/

/-- A point of the closed horocycle of height `y`. -/
abbrev horoPoint (x y : ℝ) : ℍ := ofComplex (⟨x, y⟩ : ℂ)

/-- The depth `Im M_{c,d}(x + iy)` reached by the row `(c, d)` from a point of the horocycle. -/
def rowDepth (y x : ℝ) (c d : ℤ) : ℝ := y / (((c : ℝ) * x + d) ^ 2 + ((c : ℝ) * y) ^ 2)

theorem im_rowSmul_horoPoint (p : gammaSet 1 1 0) {x y : ℝ} (hy : 0 < y) :
    (gammaSetMatrix p • horoPoint x y).im = rowDepth y x (p.1 0) (p.1 1) := by
  rw [RHTower.DeckPointPair.im_gammaSetMatrix_smul, im_ofComplex_mk hy]
  have hz : ((horoPoint x y : ℍ) : ℂ) = ⟨x, y⟩ := by
    simp only [horoPoint]
    rw [ofComplex_apply_of_im_pos hy]
    rfl
  rw [hz, rowDepth, Complex.normSq_apply]
  congr 1
  simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_im,
    Complex.mul_im]
  ring

/-- A row that reaches depth `a` has `(c y)² ≤ y/a` and `(c x + d)² ≤ y/a`. -/
theorem rowDepth_bounds {a : ℝ} (ha : 0 < a) {y x : ℝ} (hy : 0 < y) {c d : ℤ}
    (h : a ≤ rowDepth y x c d) :
    ((c : ℝ) * y) ^ 2 ≤ y / a ∧ ((c : ℝ) * x + d) ^ 2 ≤ y / a := by
  unfold rowDepth at h
  set Q := ((c : ℝ) * x + d) ^ 2 + ((c : ℝ) * y) ^ 2
  have hQ : 0 < Q := by
    by_contra hQ
    push Not at hQ
    have : y / Q ≤ 0 := div_nonpos_of_nonneg_of_nonpos hy.le hQ
    linarith
  have hle : Q ≤ y / a := by
    rw [le_div_iff₀ ha]
    rw [le_div_iff₀ hQ] at h
    linarith
  exact ⟨by nlinarith [sq_nonneg ((c : ℝ) * x + d)], by nlinarith [sq_nonneg ((c : ℝ) * y)]⟩

variable {ψ : ℝ → ℂ} {a : ℝ}

/-- **On the horocycle segment the pseudo-Eisenstein series is a finite sum over a box of rows.** -/
theorem pseudoEisenstein_horoPoint (ha : 0 < a) (hψa : ∀ t, t < a → ψ t = 0) {y : ℝ} (hy : 0 < y)
    {C D : ℕ} (hC : 1 < ((C : ℝ) + 1) ^ 2 * a * y) (hD : Real.sqrt (y / a) + C < D) {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    pseudoEisenstein ψ (horoPoint x y) = ∑ c ∈ Icc (-(C : ℤ)) C, ∑ d ∈ Icc (-(D : ℤ)) D,
      if Int.gcd c d = 1 then ψ (rowDepth y x c d) else 0 := by
  unfold pseudoEisenstein
  have e1 : (fun p : gammaSet 1 1 0 => ψ (gammaSetMatrix p • horoPoint x y).im) =
      fun p => (fun v : Fin 2 → ℤ => ψ (rowDepth y x (v 0) (v 1))) p.1 :=
    funext fun p => by rw [im_rowSmul_horoPoint p hy]
  rw [e1, tsum_subtype (gammaSet 1 1 0) (fun v : Fin 2 → ℤ => ψ (rowDepth y x (v 0) (v 1))),
    ← (Equiv.tsum_eq (finTwoArrowEquiv ℤ).symm _)]
  rw [tsum_eq_sum (s := Finset.Icc (-(C : ℤ)) C ×ˢ Finset.Icc (-(D : ℤ)) D), Finset.sum_product]
  · refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp [Set.indicator_apply, gammaSet_one_mem_iff]
  · rintro ⟨c, d⟩ hq
    simp only [Set.indicator_apply, gammaSet_one_mem_iff, finTwoArrowEquiv_symm_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Set.mem_setOf_eq]
    split_ifs with hg
    · apply hψa
      by_contra hlt
      push Not at hlt
      obtain ⟨h1, h2⟩ := rowDepth_bounds ha hy hlt
      apply hq
      simp only [Finset.mem_product, Finset.mem_Icc]
      have hya : y / a < ((C : ℝ) + 1) ^ 2 * y ^ 2 := by
        rw [div_lt_iff₀ ha]
        nlinarith
      have hc2 : (c : ℝ) ^ 2 < ((C : ℝ) + 1) ^ 2 := by nlinarith
      have hC0 : (0 : ℝ) ≤ C := by positivity
      have hc1 : (c : ℝ) < C + 1 := by nlinarith
      have hc1' : -((C : ℝ) + 1) < c := by nlinarith
      have hcabs : |(c : ℝ)| ≤ C := by
        have ha1 : c < (C : ℤ) + 1 := by exact_mod_cast hc1
        have ha2 : -((C : ℤ) + 1) < c := by exact_mod_cast hc1'
        rw [abs_le]
        constructor
        · have : -(C : ℤ) ≤ c := by omega
          exact_mod_cast this
        · have : c ≤ (C : ℤ) := by omega
          exact_mod_cast this
      have hd : |(c : ℝ) * x + d| ≤ Real.sqrt (y / a) := Real.abs_le_sqrt h2
      have hcx : |(c : ℝ) * x| ≤ C := by
        rw [abs_mul, abs_of_nonneg hx0]
        nlinarith [abs_nonneg (c : ℝ)]
      have hdabs : |(d : ℝ)| < D := by
        have : (d : ℝ) = ((c : ℝ) * x + d) - (c : ℝ) * x := by ring
        rw [this]
        calc |(c : ℝ) * x + d - (c : ℝ) * x| ≤ |(c : ℝ) * x + d| + |(c : ℝ) * x| := abs_sub _ _
          _ < D := by linarith
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · have := (abs_le.mp hcabs).1
        exact_mod_cast this
      · have := (abs_le.mp hcabs).2
        exact_mod_cast this
      · have := (abs_lt.mp hdabs).1
        have : -(D : ℤ) < d := by exact_mod_cast this
        omega
      · have := (abs_lt.mp hdabs).2
        have : d < (D : ℤ) := by exact_mod_cast this
        omega
    · rfl

/-! ### The Farey kernel and the count of cusp images -/

/-- **The Farey kernel of the denominator `c`**: the profile integrated along the horocycle over the
horoball of one cusp image `d/c`. -/
def fareyKernel (ψ : ℝ → ℂ) (y : ℝ) (c : ℕ) : ℂ := ∫ v : ℝ, ψ (y / ((c : ℝ) ^ 2 * (v ^ 2 + y ^ 2)))

/-- Denominators that are too large see nothing: the horocycle stays below depth `1/(c² y)`. -/
theorem fareyKernel_eq_zero (hψa : ∀ t, t < a → ψ t = 0) {y : ℝ} (hy : 0 < y) {c : ℕ}
    (hc : 1 < (c : ℝ) ^ 2 * a * y) : fareyKernel ψ y c = 0 := by
  have hc0 : (0 : ℝ) < c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · simp at hc
    · exact_mod_cast h
  have ha : 0 < a := by
    by_contra h
    push Not at h
    nlinarith [mul_nonneg (sq_nonneg (c : ℝ)) hy.le]
  have h1 : y < (c : ℝ) ^ 2 * a * y ^ 2 := by nlinarith
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun v => hψa _ ?_)
  have hpos : 0 < (c : ℝ) ^ 2 * (v ^ 2 + y ^ 2) := by positivity
  rw [div_lt_iff₀ hpos]
  nlinarith [mul_nonneg (mul_nonneg ha.le (sq_nonneg (c : ℝ))) (sq_nonneg v)]

/-- A symmetric sum over `[-C, C]` of an even function. -/
theorem sum_Icc_neg_eq {H : ℤ → ℂ} (hH : ∀ c, H (-c) = H c) (C : ℕ) :
    ∑ c ∈ Finset.Icc (-(C : ℤ)) C, H c = H 0 + 2 * ∑ c ∈ Finset.Icc 1 C, H c := by
  induction C with
  | zero => simp
  | succ C ih =>
    have hset : Finset.Icc (-((C + 1 : ℕ) : ℤ)) ((C + 1 : ℕ) : ℤ) =
        Finset.Icc (-(C : ℤ)) C ∪ {-((C : ℤ) + 1), (C : ℤ) + 1} := by
      ext c
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      push_cast
      omega
    have hdisj : Disjoint (Finset.Icc (-(C : ℤ)) C) {-((C : ℤ) + 1), (C : ℤ) + 1} := by
      rw [Finset.disjoint_left]
      intro c hc hc'
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hc hc'
      omega
    rw [hset, Finset.sum_union hdisj, Finset.sum_pair (by omega), ih,
      Finset.sum_Icc_succ_top (by omega), hH]
    push_cast
    ring

/-- A measurable bounded profile composed with a measurable height is integrable on `[0, 1)`. -/
theorem integrableOn_Ico_of_bounded {f : ℝ → ℂ} (hf : Measurable f) {M : ℝ} (hb : ∀ x, ‖f x‖ ≤ M) :
    IntegrableOn f (Ico (0 : ℝ) 1) :=
  Measure.integrableOn_of_bounded (by simp) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall hb)

/-- **The horocycle mean is the totient-weighted count of cusp images.** For a measurable bounded
profile vanishing below depth `a > 0`, at every height `y > 0` and every `C` with
`(C + 1)² a y > 1`:

  `∫₀¹ F_ψ(x + iy) dx = 2ψ(y) + 2 Σ_{c=1}^{C} φ(c) ∫_ℝ ψ(y / (c²(v² + y²))) dv`. -/
theorem horocycleMean_eq_fareySum (hψm : Measurable ψ) {M : ℝ} (hψb : ∀ t, ‖ψ t‖ ≤ M) (ha : 0 < a)
    (hψa : ∀ t, t < a → ψ t = 0) {y : ℝ} (hy : 0 < y) {C : ℕ}
    (hC : 1 < ((C : ℝ) + 1) ^ 2 * a * y) :
    horocycleMean (pseudoEisenstein ψ) y =
      2 * ψ y + 2 * ∑ c ∈ Icc 1 C, (c.totient : ℂ) * fareyKernel ψ y c := by
  obtain ⟨D, hD⟩ := exists_nat_gt (Real.sqrt (y / a) + C + 1)
  have hD' : Real.sqrt (y / a) + C < D := by linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (hψb 0)
  -- the integrand of one row
  set f : ℤ → ℤ → ℝ → ℂ := fun c d x => if Int.gcd c d = 1 then ψ (rowDepth y x c d) else 0 with hf
  have hfm (c d : ℤ) : Measurable (f c d) := by
    simp only [hf]
    split_ifs
    · exact hψm.comp (by unfold rowDepth; fun_prop)
    · exact measurable_const
  have hfb (c d : ℤ) (x : ℝ) : ‖f c d x‖ ≤ M := by
    simp only [hf]
    split_ifs
    · exact hψb _
    · simpa using hM
  have hfi (c d : ℤ) : IntegrableOn (f c d) (Ico (0 : ℝ) 1) := integrableOn_Ico_of_bounded (hfm c d) (hfb c d)
  unfold horocycleMean
  rw [setIntegral_congr_fun measurableSet_Ico (g := fun x => ∑ c ∈ Icc (-(C : ℤ)) C,
      ∑ d ∈ Icc (-(D : ℤ)) D, f c d x) fun x hx =>
    pseudoEisenstein_horoPoint ha hψa hy hC hD' hx.1 hx.2.le]
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => hfi c d]
  simp_rw [integral_finsetSum _ fun d _ => hfi _ d]
  -- symmetry in `c`
  set H : ℤ → ℂ := fun c => ∑ d ∈ Icc (-(D : ℤ)) D, ∫ x in Ico (0 : ℝ) 1, f c d x with hH
  have hHneg (c : ℤ) : H (-c) = H c := by
    simp only [hH]
    refine Finset.sum_nbij' (fun d => -d) (fun d => -d) ?_ ?_ (fun d _ => neg_neg d)
      (fun d _ => neg_neg d) fun d _ => ?_
    · intro d hd
      simp only [Finset.mem_Icc] at hd ⊢
      constructor <;> linarith [hd.1, hd.2]
    · intro d hd
      simp only [Finset.mem_Icc] at hd ⊢
      constructor <;> linarith [hd.1, hd.2]
    · congr 1
      funext x
      simp only [hf, Int.neg_gcd, Int.gcd_neg, rowDepth]
      congr 2
      push_cast
      ring
  change ∑ c ∈ Icc (-(C : ℤ)) C, H c = _
  rw [sum_Icc_neg_eq hHneg C]
  have hD1 : (1 : ℤ) ≤ D := by
    have : (1 : ℝ) < D := by linarith [Real.sqrt_nonneg (y / a), (Nat.cast_nonneg C : (0 : ℝ) ≤ C)]
    exact_mod_cast this.le
  -- the identity row: the two rows `(0, ±1)`
  have hH0 : H 0 = 2 * ψ y := by
    simp only [hH, hf, Int.gcd_zero_left]
    have hrow (d : ℤ) : (∫ x in Ico (0 : ℝ) 1,
        if d.natAbs = 1 then ψ (rowDepth y x 0 d) else 0) = if d.natAbs = 1 then ψ y else 0 := by
      by_cases hd : d.natAbs = 1
      · have hd2 : (d : ℝ) ^ 2 = 1 := by
          have : d ^ 2 = 1 := by
            rcases Int.natAbs_eq_iff.mp hd with h | h <;> simp [h]
          exact_mod_cast this
        have hr : ∀ x, rowDepth y x 0 d = y := fun x => by simp [rowDepth, hd2]
        simp only [hd, if_true, hr]
        simp
      · simp only [hd, if_false, integral_zero]
    simp only [hrow]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
    have hset : (Finset.Icc (-(D : ℤ)) D).filter (fun d => d.natAbs = 1) = {-1, 1} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [hset, Finset.card_pair (by norm_num)]
    simp [two_mul]
  -- a denominator `c ≥ 1`: unfolding
  have hHc (c : ℕ) (hc : c ∈ Finset.Icc 1 C) : H c = (c.totient : ℂ) * fareyKernel ψ y c := by
    have hc1 : 1 ≤ c := (Finset.mem_Icc.mp hc).1
    have hcC : c ≤ C := (Finset.mem_Icc.mp hc).2
    have hc0 : (0 : ℝ) < c := by exact_mod_cast hc1
    set U := Real.sqrt (y / a)
    set g : ℝ → ℂ := fun u => ψ (y / (u ^ 2 + ((c : ℝ) * y) ^ 2)) with hg
    have hgm : Measurable g := hψm.comp (by fun_prop)
    have hgU : ∀ u, U < |u| → g u = 0 := by
      intro u hu
      apply hψa
      have hu2 : y / a < u ^ 2 := by
        have h0 : 0 ≤ U := Real.sqrt_nonneg _
        have : U ^ 2 < |u| ^ 2 := by nlinarith
        rwa [sq_abs, Real.sq_sqrt (div_nonneg hy.le ha.le)] at this
      have hpos : 0 < u ^ 2 + ((c : ℝ) * y) ^ 2 := by positivity
      rw [div_lt_iff₀ hpos]
      rw [div_lt_iff₀ ha] at hu2
      nlinarith [sq_nonneg ((c : ℝ) * y)]
    have hgi : Integrable g := by
      have hon : IntegrableOn g (Set.Icc (-U) U) :=
        Measure.integrableOn_of_bounded (by simp) hgm.aestronglyMeasurable
          (Filter.Eventually.of_forall fun u => hψb _)
      refine (integrableOn_iff_integrable_of_support_subset fun u hu => ?_).mp hon
      by_contra hu'
      apply hu
      simp only [Set.mem_Icc, not_and_or, not_le] at hu'
      apply hgU
      rcases hu' with h | h
      · linarith [neg_le_abs u]
      · linarith [le_abs_self u]
    have hDc : U + c ≤ ((D : ℤ) : ℝ) := by
      have : (c : ℝ) ≤ C := by exact_mod_cast hcC
      push_cast
      linarith
    have hunf := integral_sum_coprime hc1 hgi hgU hDc
    have hrows : H c = ∑ d ∈ (Finset.Icc (-(D : ℤ)) D).filter (fun d => IsCoprime (c : ℤ) d),
        ∫ x in Ico (0 : ℝ) 1, g (c * x + d) := by
      simp only [hH, hf]
      have hif (d : ℤ) : (∫ x in Ico (0 : ℝ) 1,
          if Int.gcd (c : ℤ) d = 1 then ψ (rowDepth y x (c : ℤ) d) else 0) =
          if IsCoprime (c : ℤ) d then ∫ x in Ico (0 : ℝ) 1, g (c * x + d) else 0 := by
        by_cases hcop : IsCoprime (c : ℤ) d
        · have hg1 : Int.gcd (c : ℤ) d = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
          rw [if_pos hcop]
          simp only [hg1, ↓reduceIte]
          congr 1
          funext x
          simp only [hg, rowDepth]
          push_cast
          rfl
        · have hg1 : Int.gcd (c : ℤ) d ≠ 1 := fun h => hcop (Int.isCoprime_iff_gcd_eq_one.mpr h)
          rw [if_neg hcop]
          simp only [hg1, ↓reduceIte, integral_zero]
      simp only [hif]
      rw [Finset.sum_filter]
    have hscale : ∫ u, g u = (c : ℂ) * fareyKernel ψ y c := by
      have h := Measure.integral_comp_mul_left g (c : ℝ)
      have hk : fareyKernel ψ y c = ∫ v, g ((c : ℝ) * v) := by
        unfold fareyKernel
        congr 1
        funext v
        simp only [hg]
        congr 2
        ring
      rw [hk, h, abs_inv, abs_of_pos hc0, Complex.real_smul]
      push_cast
      field_simp
    rw [hrows, hunf, hscale]
    have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hc0.ne'
    field_simp
  rw [hH0, Finset.sum_congr rfl hHc]

end GaloisForLFunctions.CountingHolography

end
