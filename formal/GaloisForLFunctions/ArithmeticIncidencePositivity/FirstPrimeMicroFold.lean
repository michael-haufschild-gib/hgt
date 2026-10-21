import GaloisForLFunctions.ArithmeticIncidencePositivity.OddWindowPastFirstPrime

/-!
# The micro-fold across `½ log 2`: the first prime atom is dominated by the archimedean surplus

For an odd test supported in `[−r, r]`, `½ log 2 < r`, the prime `2` acts only on the edge strip
`S = [L − r, r]`, `L = log 2`, through `2Λ(2)/√2 ∫_S F(a) F(L − a) da`
(`FirstPrimeWindowOddStrip`). Split `F` on `S` into its even and odd parts about `L/2`:
`F(a) F(L − a) = F_e(a)² − α(a)²`, `α(a) = (F(a) − F(L − a))/2` (`reflectedOddPart`). The atom costs
only the odd part, `−2Λ(2)/√2 ∫_S α²`, and this odd part is exactly what the archimedean surplus of the
pairs inside `S` controls. For four points `x, L − x, y, L − y` of `S` the four surplus terms satisfy
(`microFold_quadruple_ge`)

    k(x, y)(F x − F y)² + k(L−x, L−y)(F(L−x) − F(L−y))² + k(x, L−y)(F x − F(L−y))² + k(L−x, y)(F(L−x) − F y)²
        ≥ 4 k₀(|x − L/2| + |y − L/2|) (α(x)² + α(y)²),

`k₀(t) = ω(t) − ω(2(L − r))`: the even parts drop out, and the two odd differences `α(x) ∓ α(y)`
recombine into `α(x)² + α(y)²` at the smaller rate. Integrating over `S × S`, whose reflections
`x ↦ L − x` preserve it (`microFold_strip_ge`):

    ∫_S ∫_S k(x, y)(F x − F y)² ≥ (2K + 2η k₀(2η)) ∫_S α²,    K = Ω(η) − Ω(2η) − η ω(2(L − r)),

`η = r − L/2`. As `η → 0` the constant tends to `log 2 + ½ > 2Λ(2)/√2 = √2 log 2`: across the
reflection about `½ log 2` the archimedean jump rate `ω(|x − y|) ≈ 1/(2|x − y|)` dominates the atom.
The constant stays above `0.9804` up to `r = 2/5` (`microFoldConstant_ge`).

**Theorems.**
* `two_mul_primeShift_le_stripSurplus`: for odd `F` supported in `[−r, r]`, `½ log 2 < r ≤ 2/5`,
  `2Λ(2)/√2 ∫ F(x) F(x + log 2) ≤ ∫_S ∫_S k(x, y)(F x − F y)²` — a Harnack inequality across the prime
  shift with explicit constant.
* `surplusEnergy_ge_potentialOff_add_strip`: the ground-state transform of the folded surplus with the
  pairs of `S × S` kept exact.
* `fourKilling_add_potentialOff_le_archJump_sub_prime`: the first prime window is atom-free — the
  archimedean jump energy minus the whole prime term dominates the killing plus the ground-state potential
  `U_h^{off}` of the pairs off `S × S`. Positivity on any window up to `2/5` thus reduces to a purely
  archimedean potential bound, with no strip charge.
-/

open MeasureTheory Set Filter Topology intervalIntegral
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- The odd part of `F` about `L/2`: `α(x) = (F(x) − F(L − x))/2`. -/
def reflectedOddPart (F : ℝ → ℝ) (L x : ℝ) : ℝ := (F x - F (L - x)) / 2

/-- The micro-fold kernel `k₀(t) = ω(t) − ω(2p)`. -/
def microFoldKernel (p t : ℝ) : ℝ := archLevyDensity t - archLevyDensity (2 * p)

theorem microFoldKernel_anti {p s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    microFoldKernel p t ≤ microFoldKernel p s := by
  unfold microFoldKernel
  linarith [strictAntiOn_archLevyDensity.antitoneOn hs (lt_of_lt_of_le hs hst) hst]

theorem microFoldKernel_nonneg {p t : ℝ} (ht : 0 < t) (ht2 : t ≤ 2 * p) : 0 ≤ microFoldKernel p t := by
  have := microFoldKernel_anti (p := p) ht ht2
  unfold microFoldKernel at this ⊢
  linarith

/-- On the strip the surplus kernel dominates the micro-fold kernel. -/
theorem microFoldKernel_mul_le {p r a b : ℝ} (hp : 0 < p) (ha : a ∈ Icc p r) (hb : b ∈ Icc p r)
    (F : ℝ → ℝ) :
    microFoldKernel p |a - b| * (F a - F b) ^ 2 ≤ surplusKernel a b * (F a - F b) ^ 2 := by
  by_cases hab : a = b
  · rw [hab, sub_self]; simp
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  unfold microFoldKernel surplusKernel
  have h1 : 2 * p ≤ a + b := by linarith [ha.1, hb.1]
  linarith [strictAntiOn_archLevyDensity.antitoneOn (show (0 : ℝ) < 2 * p by linarith)
    (show (0 : ℝ) < a + b by linarith [ha.1, hb.1]) h1]

theorem rate_le_of_le (m₁ M X Y : ℝ) (hm : M ≤ m₁) (hm1 : 0 ≤ m₁) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    M * Y ≤ m₁ * (X + Y) := by
  nlinarith

/-- The algebra of the quadruple: the even parts drop, the odd parts recombine. -/
theorem quadruple_abstract {A A' B B' S1 S2 S3 S4 m₁ m₂ M : ℝ}
    (h1 : m₁ * (A - B) ^ 2 ≤ S1) (h2 : m₁ * (A' - B') ^ 2 ≤ S2) (h3 : m₂ * (A - B') ^ 2 ≤ S3)
    (h4 : m₂ * (A' - B) ^ 2 ≤ S4)
    (c1 : M * (2 * ((A - A') / 2 - (B - B') / 2) ^ 2) ≤ m₁ * ((A - B) ^ 2 + (A' - B') ^ 2))
    (c2 : M * (2 * ((A - A') / 2 + (B - B') / 2) ^ 2) ≤ m₂ * ((A - B') ^ 2 + (A' - B) ^ 2)) :
    4 * M * (((A - A') / 2) ^ 2 + ((B - B') / 2) ^ 2) ≤ S1 + S2 + S3 + S4 := by
  have e : 4 * M * (((A - A') / 2) ^ 2 + ((B - B') / 2) ^ 2) =
      M * (2 * ((A - A') / 2 - (B - B') / 2) ^ 2) + M * (2 * ((A - A') / 2 + (B - B') / 2) ^ 2) := by
    ring
  have e1 : m₁ * ((A - B) ^ 2 + (A' - B') ^ 2) = m₁ * (A - B) ^ 2 + m₁ * (A' - B') ^ 2 := by ring
  have e2 : m₂ * ((A - B') ^ 2 + (A' - B) ^ 2) = m₂ * (A - B') ^ 2 + m₂ * (A' - B) ^ 2 := by ring
  rw [e]; rw [e1] at c1; rw [e2] at c2
  linarith

/-- **The quadruple inequality of the micro-fold.** -/
theorem microFold_quadruple_ge {p r L x y : ℝ} (hp : 0 < p) (hL : p + r = L)
    (hr3 : r - p ≤ 2 * p) (hx : x ∈ Icc p r) (hy : y ∈ Icc p r) (F : ℝ → ℝ) :
    4 * microFoldKernel p (|x - L / 2| + |y - L / 2|) *
        (reflectedOddPart F L x ^ 2 + reflectedOddPart F L y ^ 2) ≤
      surplusKernel x y * (F x - F y) ^ 2 +
        surplusKernel (L - x) (L - y) * (F (L - x) - F (L - y)) ^ 2 +
        surplusKernel x (L - y) * (F x - F (L - y)) ^ 2 +
        surplusKernel (L - x) y * (F (L - x) - F y) ^ 2 := by
  have hxL : L - x ∈ Icc p r := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hyL : L - y ∈ Icc p r := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have k1 := microFoldKernel_mul_le hp hx hy F
  have k2 := microFoldKernel_mul_le hp hxL hyL F
  have k3 := microFoldKernel_mul_le hp hx hyL F
  have k4 := microFoldKernel_mul_le hp hxL hy F
  have e1 : |x - y| = |(x - L / 2) - (y - L / 2)| := by ring_nf
  have e2 : |L - x - (L - y)| = |(x - L / 2) - (y - L / 2)| := by
    rw [abs_sub_comm]; ring_nf
  have e3 : |x - (L - y)| = |(x - L / 2) + (y - L / 2)| := by ring_nf
  have e4 : |L - x - y| = |(x - L / 2) + (y - L / 2)| := by rw [← abs_neg]; ring_nf
  rw [e1] at k1; rw [e2] at k2; rw [e3] at k3; rw [e4] at k4
  have hU : |x - L / 2| ≤ (r - p) / 2 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hV : |y - L / 2| ≤ (r - p) / 2 := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  unfold reflectedOddPart
  refine quadruple_abstract k1 k2 k3 k4 ?_ ?_
  · -- the same-side pair
    by_cases hxy : x = y
    · rw [hxy]; simp
    · have hpos : 0 < |(x - L / 2) - (y - L / 2)| :=
        abs_pos.mpr (by intro h; apply hxy; linarith)
      have hle : |(x - L / 2) - (y - L / 2)| ≤ |x - L / 2| + |y - L / 2| := abs_sub _ _
      have hk0 := microFoldKernel_nonneg (p := p) hpos (by linarith)
      have hmono := microFoldKernel_anti (p := p) hpos hle
      have e : (F x - F y) ^ 2 + (F (L - x) - F (L - y)) ^ 2 =
          2 * ((F x + F (L - x) - F y - F (L - y)) / 2) ^ 2 +
            2 * ((F x - F (L - x)) / 2 - (F y - F (L - y)) / 2) ^ 2 := by ring
      rw [e]
      exact rate_le_of_le _ _ _ _ hmono hk0 (by positivity) (by positivity)
  · -- the crossing pair
    by_cases hxy : y = L - x
    · rw [hxy, sub_sub_cancel]; ring_nf; simp
    · have hpos : 0 < |(x - L / 2) + (y - L / 2)| :=
        abs_pos.mpr (by intro h; apply hxy; linarith)
      have hle : |(x - L / 2) + (y - L / 2)| ≤ |x - L / 2| + |y - L / 2| := abs_add_le _ _
      have hk0 := microFoldKernel_nonneg (p := p) hpos (by linarith)
      have hmono := microFoldKernel_anti (p := p) hpos hle
      have e : (F x - F (L - y)) ^ 2 + (F (L - x) - F y) ^ 2 =
          2 * ((F x + F (L - x) - F y - F (L - y)) / 2) ^ 2 +
            2 * ((F x - F (L - x)) / 2 + (F y - F (L - y)) / 2) ^ 2 := by ring
      rw [e]
      exact rate_le_of_le _ _ _ _ hmono hk0 (by positivity) (by positivity)

/-! ### Integration over the strip -/

/-- A measurable function bounded on `[a, b]` is interval integrable. -/
theorem intervalIntegrable_of_abs_le {φ : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hφ : Measurable φ) (hb : ∀ x ∈ Icc a b, |φ x| ≤ C) :
    IntervalIntegrable φ volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine Measure.integrableOn_of_bounded (M := C) (by simp) hφ.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs]
  exact hb x ⟨hx.1.le, hx.2⟩

/-- The reflection `x ↦ L − x` of the strip `[p, r]`, `p + r = L`, preserves interval integrals. -/
theorem integral_strip_reflect {p r L : ℝ} (hL : p + r = L) (φ : ℝ → ℝ) :
    (∫ x in p..r, φ (L - x)) = ∫ x in p..r, φ x := by
  rw [intervalIntegral.integral_comp_sub_left, show L - r = p by linarith, show L - p = r by linarith]

/-- `∫_p^r k₀(η + |y − L/2|) dy = 2(Ω(η) − Ω(2η) − η ω(2p))`, `η = (r − p)/2`. -/
theorem integral_microFoldKernel_shift {p r L : ℝ} (hpr : p < r) (hL : p + r = L) :
    (∫ y in p..r, microFoldKernel p ((r - p) / 2 + |y - L / 2|)) =
      2 * (archLevyAntideriv ((r - p) / 2) - archLevyAntideriv (r - p) -
        (r - p) / 2 * archLevyDensity (2 * p)) := by
  set η := (r - p) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hm : L / 2 = p + η := by rw [hη]; linarith
  have h2η : r - p = 2 * η := by rw [hη]; ring
  have hcont : ContinuousOn (fun y => microFoldKernel p (η + |y - L / 2|)) (uIcc p r) := by
    unfold microFoldKernel
    refine ContinuousOn.sub ?_ continuousOn_const
    refine continuousOn_archLevyDensity.comp (by fun_prop) fun y _ => ?_
    exact mem_Ioi.mpr (by positivity)
  have s1 : uIcc p (L / 2) ⊆ uIcc p r := by
    rw [uIcc_of_le hpr.le, uIcc_of_le (by linarith : p ≤ L / 2)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have s2 : uIcc (L / 2) r ⊆ uIcc p r := by
    rw [uIcc_of_le hpr.le, uIcc_of_le (by linarith : L / 2 ≤ r)]
    exact Icc_subset_Icc (by linarith) le_rfl
  have h1 : IntervalIntegrable (fun y => microFoldKernel p (η + |y - L / 2|)) volume p (L / 2) :=
    (hcont.mono s1).intervalIntegrable
  have h2 : IntervalIntegrable (fun y => microFoldKernel p (η + |y - L / 2|)) volume (L / 2) r :=
    (hcont.mono s2).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  have hleft : (∫ y in p..L / 2, microFoldKernel p (η + |y - L / 2|)) =
      archLevyAntideriv η - archLevyAntideriv (2 * η) - η * archLevyDensity (2 * p) := by
    have e : EqOn (fun y => microFoldKernel p (η + |y - L / 2|))
        (fun y => archLevyDensity ((η + L / 2) - y) - archLevyDensity (2 * p)) (uIcc p (L / 2)) :=
      fun y hy => by
        rw [uIcc_of_le (by linarith)] at hy
        simp only [microFoldKernel]
        rw [abs_of_nonpos (by linarith [hy.2])]; ring_nf
    have hi : IntervalIntegrable (fun y => archLevyDensity ((η + L / 2) - y)) volume p (L / 2) := by
      refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_archLevyDensity.comp (by fun_prop) fun y hy => ?_
      rw [uIcc_of_le (by linarith)] at hy
      exact mem_Ioi.mpr (by linarith [hy.2])
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_comp_sub_left (fun t => archLevyDensity t) (η + L / 2),
      intervalIntegral.integral_const, smul_eq_mul,
      show η + L / 2 - L / 2 = η by ring, show η + L / 2 - p = 2 * η by linarith,
      integral_archLevyDensity_Icc hη0 (by linarith)]
    rw [hm]; ring
  have hright : (∫ y in L / 2..r, microFoldKernel p (η + |y - L / 2|)) =
      archLevyAntideriv η - archLevyAntideriv (2 * η) - η * archLevyDensity (2 * p) := by
    have e : EqOn (fun y => microFoldKernel p (η + |y - L / 2|))
        (fun y => archLevyDensity (y + (η - L / 2)) - archLevyDensity (2 * p)) (uIcc (L / 2) r) :=
      fun y hy => by
        rw [uIcc_of_le (by linarith)] at hy
        simp only [microFoldKernel]
        rw [abs_of_nonneg (by linarith [hy.1])]; ring_nf
    have hi : IntervalIntegrable (fun y => archLevyDensity (y + (η - L / 2))) volume (L / 2) r := by
      refine ContinuousOn.intervalIntegrable ?_
      refine continuousOn_archLevyDensity.comp (by fun_prop) fun y hy => ?_
      rw [uIcc_of_le (by linarith)] at hy
      exact mem_Ioi.mpr (by linarith [hy.1])
    rw [intervalIntegral.integral_congr e, intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_comp_add_right (fun t => archLevyDensity t) (η - L / 2),
      intervalIntegral.integral_const, smul_eq_mul,
      show L / 2 + (η - L / 2) = η by ring, show r + (η - L / 2) = 2 * η by linarith,
      integral_archLevyDensity_Icc hη0 (by linarith)]
    rw [hm]; ring
  rw [hleft, hright, h2η]
  ring

/-- Iterated interval integrals of a bounded jointly measurable function are interval integrable. -/
theorem intervalIntegrable_iterated {f : ℝ → ℝ → ℝ} {p r C : ℝ} (hpr : p ≤ r)
    (hf : Measurable (Function.uncurry f)) (hb : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r, |f x y| ≤ C) :
    (∀ x ∈ Icc p r, IntervalIntegrable (f x) volume p r) ∧
      IntervalIntegrable (fun x => ∫ y in p..r, f x y) volume p r := by
  have hin : ∀ x ∈ Icc p r, IntervalIntegrable (f x) volume p r := fun x hx =>
    intervalIntegrable_of_abs_le hpr (hf.comp (measurable_const.prodMk measurable_id))
      fun y hy => hb x hx y hy
  refine ⟨hin, ?_⟩
  have hmeas : Measurable fun x => ∫ y in p..r, f x y := by
    have h := (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioc p r))).measurable
    have e : (fun x => ∫ y in p..r, f x y) =
        fun x => ∫ y, Function.uncurry f (x, y) ∂(volume.restrict (Ioc p r)) := by
      funext x
      simp only [Function.uncurry_apply_pair]
      rw [intervalIntegral.integral_of_le hpr]
    rw [e]; exact h
  refine intervalIntegrable_of_abs_le (C := C * (r - p)) hpr hmeas fun x hx => ?_
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := p) (b := r) (f := f x) (C := C)
    fun y hy => by
      rw [Real.norm_eq_abs]
      rw [uIoc_of_le hpr] at hy
      exact hb x hx y ⟨hy.1.le, hy.2⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ r - p)] at this
  linarith

/-- The strip integrand `g(x, y) = k(x, y)(F x − F y)²`. -/
def stripIntegrand (F : ℝ → ℝ) (x y : ℝ) : ℝ := surplusKernel x y * (F x - F y) ^ 2

theorem measurable_stripIntegrand {F : ℝ → ℝ} (hF : Continuous F) :
    Measurable (Function.uncurry (stripIntegrand F)) := by
  have := measurable_surplusKernel
  have h2 : Measurable fun z : ℝ × ℝ => (F z.1 - F z.2) ^ 2 := by fun_prop
  exact this.mul h2

theorem measurable_uncurry_reflect_both {f : ℝ → ℝ → ℝ} (hf : Measurable (Function.uncurry f))
    (L : ℝ) : Measurable (Function.uncurry fun x y => f (L - x) (L - y)) :=
  hf.comp ((measurable_const.sub measurable_fst).prodMk (measurable_const.sub measurable_snd))

theorem measurable_uncurry_reflect_snd {f : ℝ → ℝ → ℝ} (hf : Measurable (Function.uncurry f))
    (L : ℝ) : Measurable (Function.uncurry fun x y => f x (L - y)) :=
  hf.comp (measurable_fst.prodMk (measurable_const.sub measurable_snd))

theorem measurable_uncurry_reflect_fst {f : ℝ → ℝ → ℝ} (hf : Measurable (Function.uncurry f))
    (L : ℝ) : Measurable (Function.uncurry fun x y => f (L - x) y) :=
  hf.comp ((measurable_const.sub measurable_fst).prodMk measurable_snd)

section Strip

variable {F : ℝ → ℝ} {K p r L : ℝ} (hF : Continuous F) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
  (hp : 0 < p) (hpr : p < r) (hL : p + r = L) (hr3 : r - p ≤ 2 * p) (hr1 : r - p ≤ 1)

include hFL hp hr1 in
theorem abs_strip_integrand_le {x y : ℝ} (hx : x ∈ Icc p r) (hy : y ∈ Icc p r) :
    |surplusKernel x y * (F x - F y) ^ 2| ≤ 3 / 2 * K ^ 2 * (r - p) := by
  have hpr' : 0 ≤ r - p := by linarith [hx.1, hx.2]
  by_cases hxy : x = y
  · rw [hxy, sub_self]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, abs_zero]; positivity
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
  have hdle : |x - y| ≤ r - p := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  have hk0 := surplusKernel_nonneg hx0 hy0 hxy
  have hk1 := (surplusKernel_le hx0 hy0).trans (archLevyDensity_le_of_le_one hd (by linarith))
  have hF2 : (F x - F y) ^ 2 ≤ K ^ 2 * |x - y| ^ 2 := by
    calc (F x - F y) ^ 2 = |F x - F y| ^ 2 := (sq_abs _).symm
      _ ≤ (K * |x - y|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hFL x y) 2
      _ = K ^ 2 * |x - y| ^ 2 := by ring
  rw [abs_mul, abs_of_nonneg hk0, abs_of_nonneg (sq_nonneg _)]
  calc surplusKernel x y * (F x - F y) ^ 2 ≤ 3 / 2 / |x - y| * (K ^ 2 * |x - y| ^ 2) :=
        mul_le_mul hk1 hF2 (sq_nonneg _) (by positivity)
    _ = 3 / 2 * K ^ 2 * |x - y| := by field_simp
    _ ≤ 3 / 2 * K ^ 2 * (r - p) := mul_le_mul_of_nonneg_left hdle (by positivity)

include hF hFL hp hpr hL hr3 hr1 in
/-- **The micro-fold of the strip.** With `η = (r − p)/2` and `p + r = L`,
`∫_p^r ∫_p^r k(x, y)(F x − F y)² ≥ (2(Ω(η) − Ω(2η) − η ω(2p)) + 2η k₀(2η)) ∫_p^r α²`. -/
theorem microFold_strip_ge :
    (2 * (archLevyAntideriv ((r - p) / 2) - archLevyAntideriv (r - p) -
        (r - p) / 2 * archLevyDensity (2 * p)) + (r - p) * microFoldKernel p (r - p)) *
        (∫ x in p..r, reflectedOddPart F L x ^ 2) ≤
      ∫ x in p..r, ∫ y in p..r, surplusKernel x y * (F x - F y) ^ 2 := by
  set C : ℝ := 3 / 2 * K ^ 2 * (r - p) with hC
  have hmg := measurable_stripIntegrand hF
  have hrefl : ∀ x, x ∈ Icc p r → L - x ∈ Icc p r := fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hbd : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r, |stripIntegrand F x y| ≤ C := fun x hx y hy =>
    abs_strip_integrand_le hFL hp hr1 hx hy
  obtain ⟨hi0, ho0⟩ := intervalIntegrable_iterated hpr.le hmg hbd
  have hm1 := measurable_uncurry_reflect_both hmg L
  have hm2 := measurable_uncurry_reflect_snd hmg L
  have hm3 := measurable_uncurry_reflect_fst hmg L
  obtain ⟨hi1, ho1⟩ := intervalIntegrable_iterated hpr.le hm1 fun x hx y hy =>
    hbd _ (hrefl x hx) _ (hrefl y hy)
  obtain ⟨hi2, ho2⟩ := intervalIntegrable_iterated hpr.le hm2 fun x hx y hy =>
    hbd _ hx _ (hrefl y hy)
  obtain ⟨hi3, ho3⟩ := intervalIntegrable_iterated hpr.le hm3 fun x hx y hy =>
    hbd _ (hrefl x hx) _ hy
  set T := ∫ x in p..r, ∫ y in p..r, stripIntegrand F x y with hT
  -- the three reflected copies equal `T`
  have hT1 : (∫ x in p..r, ∫ y in p..r, stripIntegrand F (L - x) (L - y)) = T := by
    have e : (fun x => ∫ y in p..r, stripIntegrand F (L - x) (L - y)) = fun x => ∫ y in p..r, stripIntegrand F (L - x) y :=
      funext fun x => integral_strip_reflect hL (stripIntegrand F (L - x))
    rw [e]
    exact integral_strip_reflect hL (fun x => ∫ y in p..r, stripIntegrand F x y)
  have hT2 : (∫ x in p..r, ∫ y in p..r, stripIntegrand F x (L - y)) = T := by
    have e : (fun x => ∫ y in p..r, stripIntegrand F x (L - y)) = fun x => ∫ y in p..r, stripIntegrand F x y :=
      funext fun x => integral_strip_reflect hL (stripIntegrand F x)
    rw [e]
  have hT3 : (∫ x in p..r, ∫ y in p..r, stripIntegrand F (L - x) y) = T :=
    integral_strip_reflect hL (fun x => ∫ y in p..r, stripIntegrand F x y)
  -- the sum of the four copies, as one iterated integral
  have hsum : (∫ x in p..r, ∫ y in p..r, (stripIntegrand F x y + stripIntegrand F (L - x) (L - y) + stripIntegrand F x (L - y) + stripIntegrand F (L - x) y)) =
      4 * T := by
    have hin : ∀ x ∈ uIcc p r, (∫ y in p..r, (stripIntegrand F x y + stripIntegrand F (L - x) (L - y) + stripIntegrand F x (L - y) + stripIntegrand F (L - x) y)) =
        (∫ y in p..r, stripIntegrand F x y) + (∫ y in p..r, stripIntegrand F (L - x) (L - y)) + (∫ y in p..r, stripIntegrand F x (L - y)) +
          ∫ y in p..r, stripIntegrand F (L - x) y := fun x hx => by
      rw [uIcc_of_le hpr.le] at hx
      rw [intervalIntegral.integral_add ((hi0 x hx).add (hi1 x hx) |>.add (hi2 x hx)) (hi3 x hx),
        intervalIntegral.integral_add ((hi0 x hx).add (hi1 x hx)) (hi2 x hx),
        intervalIntegral.integral_add (hi0 x hx) (hi1 x hx)]
    rw [intervalIntegral.integral_congr hin, intervalIntegral.integral_add ((ho0.add ho1).add ho2) ho3,
      intervalIntegral.integral_add (ho0.add ho1) ho2, intervalIntegral.integral_add ho0 ho1,
      hT1, hT2, hT3]
    ring
  -- the pointwise lower bound and its integral
  set η := (r - p) / 2 with hη
  set A := ∫ y in p..r, reflectedOddPart F L y ^ 2 with hA
  set K' := archLevyAntideriv η - archLevyAntideriv (r - p) - η * archLevyDensity (2 * p) with hK'
  have hα0 : reflectedOddPart F L (L / 2) = 0 := by
    unfold reflectedOddPart; rw [show L - L / 2 = L / 2 by ring, sub_self, zero_div]
  have hαc : Continuous fun y => reflectedOddPart F L y ^ 2 := by
    unfold reflectedOddPart; fun_prop
  have hkc : ContinuousOn (fun y => microFoldKernel p (η + |y - L / 2|)) (uIcc p r) := by
    unfold microFoldKernel
    refine ContinuousOn.sub ?_ continuousOn_const
    refine continuousOn_archLevyDensity.comp (by fun_prop) fun y _ => ?_
    exact mem_Ioi.mpr (by rw [hη]; have := abs_nonneg (y - L / 2); linarith)
  have hpt : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r,
      4 * microFoldKernel p (η + |y - L / 2|) * reflectedOddPart F L x ^ 2 +
          4 * microFoldKernel p (r - p) * reflectedOddPart F L y ^ 2 ≤
        stripIntegrand F x y + stripIntegrand F (L - x) (L - y) + stripIntegrand F x (L - y) +
          stripIntegrand F (L - x) y := by
    intro x hx y hy
    have hq := microFold_quadruple_ge hp hL hr3 hx hy F
    have hU : |x - L / 2| ≤ η := by rw [hη, abs_le]; constructor <;> linarith [hx.1, hx.2]
    have hV : |y - L / 2| ≤ η := by rw [hη, abs_le]; constructor <;> linarith [hy.1, hy.2]
    have t1 : microFoldKernel p (η + |y - L / 2|) * reflectedOddPart F L x ^ 2 ≤
        microFoldKernel p (|x - L / 2| + |y - L / 2|) * reflectedOddPart F L x ^ 2 := by
      by_cases hxm : x = L / 2
      · rw [hxm, hα0]; simp
      · have hpos : 0 < |x - L / 2| + |y - L / 2| := by
          have := abs_pos.mpr (sub_ne_zero.mpr hxm); positivity
        exact mul_le_mul_of_nonneg_right (microFoldKernel_anti hpos (by linarith)) (sq_nonneg _)
    have t2 : microFoldKernel p (r - p) * reflectedOddPart F L y ^ 2 ≤
        microFoldKernel p (|x - L / 2| + |y - L / 2|) * reflectedOddPart F L y ^ 2 := by
      by_cases hym : y = L / 2
      · rw [hym, hα0]; simp
      · have hpos : 0 < |x - L / 2| + |y - L / 2| := by
          have := abs_pos.mpr (sub_ne_zero.mpr hym); positivity
        exact mul_le_mul_of_nonneg_right (microFoldKernel_anti hpos (by rw [hη] at hU hV; linarith))
          (sq_nonneg _)
    unfold stripIntegrand
    nlinarith [hq, t1, t2]
  -- integrability of the summed integrand
  have hms : Measurable (Function.uncurry fun x y => stripIntegrand F x y +
      stripIntegrand F (L - x) (L - y) + stripIntegrand F x (L - y) + stripIntegrand F (L - x) y) := by
    have := ((hmg.add hm1).add hm2).add hm3
    exact this
  obtain ⟨his, hos⟩ := intervalIntegrable_iterated (C := 4 * C) hpr.le hms fun x hx y hy => by
    have h0 := hbd x hx y hy
    have h1 := hbd _ (hrefl x hx) _ (hrefl y hy)
    have h2 := hbd _ hx _ (hrefl y hy)
    have h3 := hbd _ (hrefl x hx) _ hy
    calc |stripIntegrand F x y + stripIntegrand F (L - x) (L - y) + stripIntegrand F x (L - y) +
          stripIntegrand F (L - x) y|
        ≤ |stripIntegrand F x y| + |stripIntegrand F (L - x) (L - y)| + |stripIntegrand F x (L - y)| +
          |stripIntegrand F (L - x) y| := by
          have := abs_add_le (stripIntegrand F x y + stripIntegrand F (L - x) (L - y) +
            stripIntegrand F x (L - y)) (stripIntegrand F (L - x) y)
          have := abs_add_le (stripIntegrand F x y + stripIntegrand F (L - x) (L - y))
            (stripIntegrand F x (L - y))
          have := abs_add_le (stripIntegrand F x y) (stripIntegrand F (L - x) (L - y))
          linarith
      _ ≤ 4 * C := by linarith
  -- inner comparison
  have hinner : ∀ x ∈ Icc p r, 4 * reflectedOddPart F L x ^ 2 * (2 * K') +
      4 * microFoldKernel p (r - p) * A ≤
      ∫ y in p..r, (stripIntegrand F x y + stripIntegrand F (L - x) (L - y) +
        stripIntegrand F x (L - y) + stripIntegrand F (L - x) y) := by
    intro x hx
    have hIK : (∫ y in p..r, microFoldKernel p (η + |y - L / 2|)) = 2 * K' := by
      rw [hη, hK', integral_microFoldKernel_shift hpr hL]
    have hiΨ1 : IntervalIntegrable (fun y => 4 * microFoldKernel p (η + |y - L / 2|) *
        reflectedOddPart F L x ^ 2) volume p r :=
      ((hkc.intervalIntegrable).const_mul 4).mul_const _
    have hiΨ2 : IntervalIntegrable (fun y => 4 * microFoldKernel p (r - p) *
        reflectedOddPart F L y ^ 2) volume p r :=
      (hαc.intervalIntegrable p r).const_mul _
    have hmono := intervalIntegral.integral_mono_on hpr.le (hiΨ1.add hiΨ2) (his x hx)
      fun y hy => hpt x hx y hy
    rw [intervalIntegral.integral_add hiΨ1 hiΨ2] at hmono
    have e1 : (∫ y in p..r, 4 * microFoldKernel p (η + |y - L / 2|) * reflectedOddPart F L x ^ 2) =
        4 * reflectedOddPart F L x ^ 2 * (2 * K') := by
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul, hIK]; ring
    have e2 : (∫ y in p..r, 4 * microFoldKernel p (r - p) * reflectedOddPart F L y ^ 2) =
        4 * microFoldKernel p (r - p) * A := by
      rw [intervalIntegral.integral_const_mul]
    rw [e1, e2] at hmono
    exact hmono
  have hiΦ : IntervalIntegrable (fun x => 4 * reflectedOddPart F L x ^ 2 * (2 * K') +
      4 * microFoldKernel p (r - p) * A) volume p r :=
    (((hαc.intervalIntegrable p r).const_mul 4).mul_const _).add intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on hpr.le hiΦ hos hinner
  rw [hsum, intervalIntegral.integral_add (((hαc.intervalIntegrable p r).const_mul 4).mul_const _)
    intervalIntegrable_const, intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, smul_eq_mul] at hmono
  have hfinal : (2 * K' + (r - p) * microFoldKernel p (r - p)) * A ≤ T := by
    nlinarith [hmono]
  exact hfinal

end Strip

/-! ### The atom costs only the reflected odd part -/

/-- **The first prime atom on an odd test sees only the odd part about `L/2`.** For odd `F` supported
in `[−r, r]`, `∫ F(x) F(x + L) dx ≤ ∫_{L−r}^{r} α²`: on the strip `F(a)F(L − a) = F_e(a)² − α(a)²`. -/
theorem integral_mul_shift_le_reflectedOdd {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) {r L : ℝ} (hr0 : 0 ≤ r) (hLr : L - r ≤ r)
    (hsupp : ∀ x, r < |x| → F x = 0) :
    (∫ x, F x * F (x + L)) ≤ ∫ a in (L - r)..r, reflectedOddPart F L a ^ 2 := by
  have hi : Integrable fun x => F x * F (x + L) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have e : (∫ x, F x * F (x + L)) = ∫ a, -(F a * F (L - a)) := by
    rw [← integral_neg_eq_self (fun x => F x * F (x + L)) volume]
    refine integral_congr_ae (Eventually.of_forall fun a => ?_)
    simp only [hodd, show -a + L = L - a by ring]
    ring
  set S := Icc (L - r) r
  have hαc : Continuous fun a => reflectedOddPart F L a ^ 2 := by
    unfold reflectedOddPart; fun_prop
  have hgi : Integrable (S.indicator fun a => reflectedOddPart F L a ^ 2) :=
    (integrable_indicator_iff measurableSet_Icc).mpr hαc.integrableOn_Icc
  have hpt : ∀ a, -(F a * F (L - a)) ≤ S.indicator (fun a => reflectedOddPart F L a ^ 2) a := by
    intro a
    by_cases ha : a ∈ S
    · rw [Set.indicator_of_mem ha]
      unfold reflectedOddPart
      nlinarith [sq_nonneg (F a + F (L - a))]
    · rw [Set.indicator_of_notMem ha]
      have : F a * F (L - a) = 0 := by
        simp only [S, mem_Icc, not_and_or, not_le] at ha
        rcases ha with h | h
        · rw [hsupp (L - a) (by rw [abs_of_pos (by linarith)]; linarith), mul_zero]
        · rw [hsupp a (by rw [abs_of_pos (by linarith)]; linarith), zero_mul]
      rw [this, neg_zero]
  have hi' : Integrable fun a => -(F a * F (L - a)) :=
    ((hF.mul (hF.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      hFc.mul_right).neg
  rw [e]
  refine (integral_mono hi' hgi hpt).trans_eq ?_
  rw [MeasureTheory.integral_indicator measurableSet_Icc, intervalIntegral.integral_of_le hLr,
    MeasureTheory.integral_Icc_eq_integral_Ioc]

/-! ### The strip energy as twice its upper triangle -/

/-- The surplus energy of the pairs inside the strip `[p, r]`, upper triangle. -/
def stripSurplus (F : ℝ → ℝ) (p r : ℝ) : ℝ :=
  ∫ x in Icc p r, ∫ y in Ioc x r, stripIntegrand F x y

theorem stripIntegrand_comm (F : ℝ → ℝ) (x y : ℝ) : stripIntegrand F x y = stripIntegrand F y x := by
  unfold stripIntegrand; rw [surplusKernel_comm]; ring

section Symmetrize

variable {F : ℝ → ℝ} {K p r : ℝ} (hF : Continuous F) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
  (hp : 0 < p) (hpr : p ≤ r) (hr1 : r - p ≤ 1)

theorem stripIntegrand_self (F : ℝ → ℝ) (x : ℝ) : stripIntegrand F x x = 0 := by
  unfold stripIntegrand; simp

include hF hFL hp hpr hr1 in
/-- **The full strip energy is twice the upper triangle.** -/
theorem integral_strip_eq_two_mul_stripSurplus :
    (∫ x in p..r, ∫ y in p..r, stripIntegrand F x y) = 2 * stripSurplus F p r := by
  set C : ℝ := 3 / 2 * K ^ 2 * (r - p) with hC
  have hmg := measurable_stripIntegrand hF
  have hbd : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r, |stripIntegrand F x y| ≤ C := fun x hx y hy =>
    abs_strip_integrand_le hFL hp hr1 hx hy
  -- the two triangles of the box
  set f : ℝ × ℝ → ℝ := fun z => if z.2 ≤ z.1 then stripIntegrand F z.1 z.2 else 0 with hf
  set f' : ℝ × ℝ → ℝ := fun z => if z.1 < z.2 then stripIntegrand F z.1 z.2 else 0 with hf'
  have hmf : Measurable f :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst) hmg measurable_const
  have hmf' : Measurable f' :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd) hmg measurable_const
  have hint : ∀ φ : ℝ × ℝ → ℝ, Measurable φ → (∀ z, φ z = 0 ∨ φ z = stripIntegrand F z.1 z.2) →
      Integrable φ ((volume.restrict (Ioc p r)).prod (volume.restrict (Ioc p r))) := by
    intro φ hφ hφv
    rw [Measure.prod_restrict]
    refine Measure.integrableOn_of_bounded (M := C) ?_ hφ.aestronglyMeasurable ?_
    · rw [Measure.prod_prod]; exact ENNReal.mul_ne_top (by simp) (by simp)
    · filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with z hz
      rw [Real.norm_eq_abs]
      rcases hφv z with h | h
      · rw [h, abs_zero]; positivity
      · rw [h]; exact hbd z.1 ⟨hz.1.1.le, hz.1.2⟩ z.2 ⟨hz.2.1.le, hz.2.2⟩
  have hif := hint f hmf fun z => by simp only [hf]; split_ifs <;> simp
  have hif' := hint f' hmf' fun z => by simp only [hf']; split_ifs <;> simp
  have hyint : ∀ x ∈ Icc p r, ∀ φ : ℝ × ℝ → ℝ, Measurable φ →
      (∀ y, φ (x, y) = 0 ∨ φ (x, y) = stripIntegrand F x y) →
      IntegrableOn (fun y => φ (x, y)) (Ioc p r) := by
    intro x hx φ hφ hφv
    refine Measure.integrableOn_of_bounded (M := C) (by simp)
      (hφ.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [Real.norm_eq_abs]
    rcases hφv y with h | h
    · rw [h, abs_zero]; positivity
    · rw [h]; exact hbd x hx y ⟨hy.1.le, hy.2⟩
  -- the box integral splits into the two triangles
  have hsplit : (∫ x in Ioc p r, ∫ y in Ioc p r, stripIntegrand F x y) =
      (∫ x in Ioc p r, ∫ y in Ioc p r, f (x, y)) + ∫ x in Ioc p r, ∫ y in Ioc p r, f' (x, y) := by
    rw [← integral_add hif.integral_prod_left hif'.integral_prod_left]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    have hxI : x ∈ Icc p r := ⟨hx.1.le, hx.2⟩
    have h1 := hyint x hxI f hmf fun y => by simp only [hf]; split_ifs <;> simp
    have h2 := hyint x hxI f' hmf' fun y => by simp only [hf']; split_ifs <;> simp
    rw [← integral_add h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioc fun y _ => ?_
    simp only [hf, hf']
    by_cases hyx : y ≤ x
    · rw [if_pos hyx, if_neg (not_lt.mpr hyx), add_zero]
    · rw [if_neg hyx, if_pos (not_le.mp hyx), zero_add]
  -- the lower triangle is the upper one, by the swap and the symmetry of the integrand
  have hlower : (∫ x in Ioc p r, ∫ y in Ioc p r, f (x, y)) =
      ∫ x in Ioc p r, ∫ y in Ioc p r, f' (x, y) := by
    rw [integral_integral_swap (f := fun x y => f (x, y)) hif]
    congr 1; funext a; congr 1; funext b
    simp only [hf, hf']
    rcases lt_trichotomy a b with h | h | h
    · rw [if_pos h.le, if_pos h, stripIntegrand_comm]
    · rw [h, if_pos le_rfl, if_neg (lt_irrefl b), stripIntegrand_self]
    · rw [if_neg (not_le.mpr h), if_neg (not_lt.mpr h.le)]
  -- the upper triangle is the strip surplus
  have hupper : (∫ x in Ioc p r, ∫ y in Ioc p r, f' (x, y)) = stripSurplus F p r := by
    unfold stripSurplus
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Ioc fun x hx => ?_
    simp only [hf']
    rw [← MeasureTheory.integral_indicator measurableSet_Ioc,
      ← MeasureTheory.integral_indicator measurableSet_Ioc]
    congr 1; funext y
    simp only [Set.indicator_apply, mem_Ioc]
    have hpx := hx.1
    by_cases h1 : x < y
    · by_cases h2 : y ≤ r
      · have h12 : p < y ∧ y ≤ r := ⟨hpx.trans h1, h2⟩
        have h12' : x < y ∧ y ≤ r := ⟨h1, h2⟩
        simp only [h12, h12', and_self, if_true]
      · have h12 : ¬(p < y ∧ y ≤ r) := fun h => h2 h.2
        have h12' : ¬(x < y ∧ y ≤ r) := fun h => h2 h.2
        simp only [h12, h12', if_false]
    · have h12' : ¬(x < y ∧ y ≤ r) := fun h => h1 h.1
      simp only [h1, false_and, if_false, ite_self]
  have hbox : (∫ x in p..r, ∫ y in p..r, stripIntegrand F x y) =
      ∫ x in Ioc p r, ∫ y in Ioc p r, stripIntegrand F x y := by
    rw [intervalIntegral.integral_of_le hpr]
    refine setIntegral_congr_fun measurableSet_Ioc fun x _ => ?_
    rw [intervalIntegral.integral_of_le hpr]
  rw [hbox, hsplit, hlower, hupper]
  ring

end Symmetrize

/-! ### The ground-state transform off the strip -/

/-- The surplus potential off the strip `[p, r]`: below `p` every partner counts, from `p` on only the
partners below `p`. -/
def surplusPotentialOff (h : ℝ → ℝ) (p r x : ℝ) : ℝ :=
  if x < p then surplusPotential h r x else ∫ y in Ioo 0 p, surplusKernel x y * (1 - h y / h x)

theorem measurable_uncurry_shear {f : ℝ → ℝ → ℝ} (hf : Measurable (Function.uncurry f)) :
    Measurable fun z : ℝ × ℝ => f z.2 (z.2 + z.1) :=
  hf.comp (measurable_snd.prodMk (measurable_snd.add measurable_fst))

section OffStrip

variable {P F : ℝ → ℝ} {B K : ℝ} (hPc : Continuous P) (hFc : Continuous F)
  (hPe : ∀ x, P (-x) = P x) (hFo : ∀ x, F (-x) = -F x) (hP0 : ∀ x, 0 ≤ P x)
  (hP1 : ∀ x, P x ≤ 1) (hPB : ∀ x, B ≤ |x| → P x = 0) (hFB : ∀ x, B ≤ |x| → F x = 0)
  (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hB0 : 0 < B) (hB1 : 2 * B ≤ 1)

include hPc hFc hFo hP0 hP1 hPB hFL hB0 hB1 in
/-- **The ground-state transform off the strip.** The pairs inside the strip `[p, r]` keep their exact
surplus, the others are transformed in the gauge `h`:
`S_P(F) ≥ ∫_{x>0} F(x)² U_h^{off}(x) dx + stripSurplus F p r`. -/
theorem surplusEnergy_ge_potentialOff_add_strip {h : ℝ → ℝ} {p r a₀ L : ℝ} (hp : 0 < p)
    (hpr : p ≤ r) (hrB : r ≤ B) (hPr : ∀ x, |x| ≤ r → P x = 1) (hFr : ∀ x, F x ≠ 0 → |x| ≤ r)
    (hh : Continuous h) (ha₀ : 0 < a₀) (hhpos : ∀ x, 0 ≤ x → x ≤ r → a₀ ≤ h x)
    (hhL : ∀ x y, 0 ≤ x → x ≤ r → 0 ≤ y → y ≤ r → |h x - h y| ≤ L * |x - y|) :
    IntegrableOn (fun x => F x ^ 2 * surplusPotentialOff h p r x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), F x ^ 2 * surplusPotentialOff h p r x) + stripSurplus F p r ≤
        surplusEnergy P F := by
  have hr1 : r ≤ 1 := by linarith
  have hr1' : r - p ≤ 1 := by linarith
  have hK0 : 0 ≤ K := by
    have := hFL 1 0; norm_num at this; linarith [abs_nonneg (F 1 - F 0)]
  have hF2 : ∀ x, 0 ≤ x → x ≤ r → F x ^ 2 ≤ K ^ 2 * r ^ 2 := fun x hx0 hxr => by
    have h1 := abs_le_mul_abs_of_odd hFo hFL x
    rw [abs_of_nonneg hx0] at h1
    have h2 : |F x| ≤ K * r := h1.trans (mul_le_mul_of_nonneg_left hxr hK0)
    calc F x ^ 2 = |F x| ^ 2 := (sq_abs _).symm
      _ ≤ (K * r) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = K ^ 2 * r ^ 2 := by ring
  have hFz : ∀ x, r < |x| → F x = 0 := fun x hx => by
    by_contra h0; exact absurd (hFr x h0) (not_le.mpr hx)
  have hmk := measurable_surplusKernel
  have hw : ∀ x y, 0 < x → x ≤ r → 0 < y → y ≤ r →
      |surplusKernel x y * (1 - h y / h x)| ≤ 3 / 2 * |L| / a₀ := fun x y hx hxr hy hyr =>
    abs_surplusKernel_mul_le hx hy (by rw [abs_le]; constructor <;> linarith) ha₀
      (hhpos x hx.le hxr) (hhL x y hx.le hxr hy.le hyr)
  set C : ℝ := K ^ 2 * r ^ 2 * (3 / 2 * |L| / a₀) + 3 / 2 * K ^ 2 * (r - p) with hC
  have hC1 : 0 ≤ K ^ 2 * r ^ 2 * (3 / 2 * |L| / a₀) := by positivity
  have hrp : 0 ≤ r - p := by linarith
  have hC2 : 0 ≤ 3 / 2 * K ^ 2 * (r - p) := by positivity
  have hwF : ∀ x y z, 0 < x → x ≤ r → 0 < y → y ≤ r → 0 ≤ z → z ≤ r →
      |F z ^ 2 * (surplusKernel x y * (1 - h y / h x))| ≤ C := fun x y z hx hxr hy hyr hz hzr => by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    have := mul_le_mul (hF2 z hz hzr) (hw x y hx hxr hy hyr) (abs_nonneg _) (by positivity)
    linarith
  -- the four pair densities
  set gA : ℝ × ℝ → ℝ := fun z => if z.2 + z.1 ≤ r ∧ z.2 < p then
    F z.2 ^ 2 * (surplusKernel z.2 (z.2 + z.1) * (1 - h (z.2 + z.1) / h z.2)) else 0 with hgA
  set gB : ℝ × ℝ → ℝ := fun z => if z.2 + z.1 ≤ r ∧ z.2 < p then
    F (z.2 + z.1) ^ 2 * (surplusKernel (z.2 + z.1) z.2 * (1 - h z.2 / h (z.2 + z.1))) else 0
    with hgB
  set gS : ℝ × ℝ → ℝ := fun z => if z.2 + z.1 ≤ r ∧ p ≤ z.2 then
    stripIntegrand F z.2 (z.2 + z.1) else 0 with hgS
  set G : ℝ × ℝ → ℝ := fun z => if z.1 < z.2 ∧ z.2 ≤ r ∧ z.1 < p then
    F z.2 ^ 2 * (surplusKernel z.2 z.1 * (1 - h z.1 / h z.2)) else 0 with hG
  have hsetA : MeasurableSet {z : ℝ × ℝ | z.2 + z.1 ≤ r ∧ z.2 < p} := by
    rw [Set.setOf_and]
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      (measurableSet_lt measurable_snd measurable_const)
  have hsetS : MeasurableSet {z : ℝ × ℝ | z.2 + z.1 ≤ r ∧ p ≤ z.2} := by
    rw [Set.setOf_and]
    exact (measurableSet_le (by fun_prop) measurable_const).inter
      (measurableSet_le measurable_const measurable_snd)
  have hsetG : MeasurableSet {z : ℝ × ℝ | z.1 < z.2 ∧ z.2 ≤ r ∧ z.1 < p} := by
    rw [Set.setOf_and, Set.setOf_and]
    exact (measurableSet_lt measurable_fst measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_const).inter
        (measurableSet_lt measurable_fst measurable_const))
  have hmA : Measurable gA := by
    refine Measurable.ite hsetA ?_ measurable_const
    exact ((hFc.measurable.comp measurable_snd).pow_const 2).mul
      ((hmk.comp (measurable_snd.prodMk (measurable_snd.add measurable_fst))).mul
        (measurable_const.sub ((hh.measurable.comp (measurable_snd.add measurable_fst)).div
          (hh.measurable.comp measurable_snd))))
  have hmB : Measurable gB := by
    refine Measurable.ite hsetA ?_ measurable_const
    exact ((hFc.measurable.comp (measurable_snd.add measurable_fst)).pow_const 2).mul
      ((hmk.comp ((measurable_snd.add measurable_fst).prodMk measurable_snd)).mul
        (measurable_const.sub ((hh.measurable.comp measurable_snd).div
          (hh.measurable.comp (measurable_snd.add measurable_fst)))))
  have hmS : Measurable gS := by
    refine Measurable.ite hsetS ?_ measurable_const
    exact measurable_uncurry_shear (measurable_stripIntegrand hFc)
  have hmG : Measurable G := by
    refine Measurable.ite hsetG ?_ measurable_const
    exact ((hFc.measurable.comp measurable_snd).pow_const 2).mul
      ((hmk.comp (measurable_snd.prodMk measurable_fst)).mul
        (measurable_const.sub ((hh.measurable.comp measurable_fst).div
          (hh.measurable.comp measurable_snd))))
  have hIA : Integrable gA ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine integrable_quadrant_of_bound hmA (C := C) (T₁ := r) (T₂ := r) (fun s x hs hx => ?_)
      (fun s x hs hx hout => ?_)
    · simp only [hgA]
      split_ifs with hxs
      · exact hwF x (x + s) x hx (by linarith) (by linarith) hxs.1 hx.le (by linarith)
      · rw [abs_zero]; positivity
    · simp only [hgA]
      rw [if_neg (by rintro ⟨h1, -⟩; rcases hout with h2 | h2 <;> linarith)]
  have hIB : Integrable gB ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine integrable_quadrant_of_bound hmB (C := C) (T₁ := r) (T₂ := r) (fun s x hs hx => ?_)
      (fun s x hs hx hout => ?_)
    · simp only [hgB]
      split_ifs with hxs
      · exact hwF (x + s) x (x + s) (by linarith) hxs.1 hx (by linarith) (by linarith) hxs.1
      · rw [abs_zero]; positivity
    · simp only [hgB]
      rw [if_neg (by rintro ⟨h1, -⟩; rcases hout with h2 | h2 <;> linarith)]
  have hIS' : Integrable gS ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine integrable_quadrant_of_bound hmS (C := C) (T₁ := r) (T₂ := r) (fun s x hs hx => ?_)
      (fun s x hs hx hout => ?_)
    · simp only [hgS]
      split_ifs with hxs
      · have : |stripIntegrand F x (x + s)| ≤ 3 / 2 * K ^ 2 * (r - p) :=
          abs_strip_integrand_le hFL hp hr1' (show x ∈ Icc p r from ⟨hxs.2, by linarith [hxs.1]⟩)
            (show x + s ∈ Icc p r from ⟨by linarith [hxs.2], hxs.1⟩)
        linarith
      · rw [abs_zero]; positivity
    · simp only [hgS]
      rw [if_neg (by rintro ⟨h1, -⟩; rcases hout with h2 | h2 <;> linarith)]
  have hIG : Integrable G ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine integrable_quadrant_of_bound hmG (C := C) (T₁ := r) (T₂ := r) (fun x y hx hy => ?_)
      (fun x y hx hy hout => ?_)
    · simp only [hG]
      split_ifs with hxy
      · exact hwF y x y hy hxy.2.1 hx (by linarith [hxy.1, hxy.2.1]) hy.le hxy.2.1
      · rw [abs_zero]; positivity
    · simp only [hG]
      rw [if_neg (by rintro ⟨h1, h2, -⟩; rcases hout with h3 | h3 <;> linarith)]
  -- the surplus density dominates the three densities
  have hIS := integrable_archLevy_mul_signedShiftJump_prod hPc hFc hP0 hP1 hPB hFL hB0 hB1
  set fS : ℝ × ℝ → ℝ := fun z =>
    (archLevyDensity z.1 - archLevyDensity (z.1 + 2 * z.2)) * signedShiftJump P F z.1 z.2 with hfS
  have hmfS : Measurable fS := by
    have hc : Continuous fun z : ℝ × ℝ => signedShiftJump P F z.1 z.2 := by
      unfold signedShiftJump; fun_prop
    exact ((measurable_archLevyDensity.comp measurable_fst).sub
      (measurable_archLevyDensity.comp (by fun_prop))).mul hc.measurable
  have hIfS : Integrable fS ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine hIS.mono' hmfS.aestronglyMeasurable (ae_quadrant fun s x hs hx => ?_)
    have hJ := signedShiftJump_nonneg' hP0 (F := F) s x
    have hω := strictAntiOn_archLevyDensity.antitoneOn hs (show (0 : ℝ) < s + 2 * x by linarith)
      (by linarith)
    have hω2 := (archLevyDensity_pos (show (0 : ℝ) < s + 2 * x by linarith)).le
    simp only [hfS, Function.uncurry_apply_pair, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (by linarith) hJ)]
    exact mul_le_mul_of_nonneg_right (by linarith) hJ
  have hpt : ∀ s x, 0 < s → 0 < x → gA (s, x) + gB (s, x) + gS (s, x) ≤ fS (s, x) := by
    intro s x hs hx
    have hJ := signedShiftJump_nonneg' hP0 (F := F) s x
    have hk := surplusKernel_nonneg hx (show 0 < x + s by linarith) (by linarith : x ≠ x + s)
    simp only [hgA, hgB, hgS, hfS]
    rw [← surplusKernel_add x s hs]
    by_cases hxs : x + s ≤ r
    · have hP1' : P x = 1 := hPr x (by rw [abs_of_pos hx]; linarith)
      have hP2' : P (x + s) = 1 := hPr (x + s) (by rw [abs_of_pos (by linarith)]; exact hxs)
      by_cases hxp : x < p
      · rw [if_pos ⟨hxs, hxp⟩, if_pos ⟨hxs, hxp⟩, if_neg (fun h => absurd h.2 (not_le.mpr hxp)),
          add_zero]
        have hgs := sq_sub_ge_groundState (F x) (F (x + s)) (lt_of_lt_of_le ha₀ (hhpos x hx.le
          (by linarith))) (lt_of_lt_of_le ha₀ (hhpos (x + s) (by linarith) hxs))
        unfold signedShiftJump
        rw [hP1', hP2', surplusKernel_comm (x + s) x]
        nlinarith [mul_le_mul_of_nonneg_left hgs hk]
      · rw [if_neg (fun h => hxp h.2), if_neg (fun h => hxp h.2), if_pos ⟨hxs, not_lt.mp hxp⟩,
          zero_add, zero_add]
        unfold signedShiftJump stripIntegrand
        rw [hP1', hP2', one_mul, one_mul]
    · rw [if_neg (fun h => hxs h.1), if_neg (fun h => hxs h.1), if_neg (fun h => hxs h.1),
        add_zero, add_zero]
      exact mul_nonneg hk hJ
  -- the iterated comparison
  have hcmp : (∫ x in Ioi (0 : ℝ), ((∫ s in Ioi (0 : ℝ), gA (s, x)) +
      (∫ s in Ioi (0 : ℝ), gB (s, x)) + ∫ s in Ioi (0 : ℝ), gS (s, x))) ≤ surplusEnergy P F := by
    have hO : Integrable (fun x => (∫ s in Ioi (0 : ℝ), gA (s, x)) + (∫ s in Ioi (0 : ℝ), gB (s, x)) +
        ∫ s in Ioi (0 : ℝ), gS (s, x)) (volume.restrict (Ioi 0)) :=
      (hIA.integral_prod_right.add hIB.integral_prod_right).add hIS'.integral_prod_right
    refine integral_mono_ae hO hIfS.integral_prod_right ?_
    filter_upwards [hIA.prod_left_ae, hIB.prod_left_ae, hIS'.prod_left_ae, hIfS.prod_left_ae,
      ae_restrict_mem measurableSet_Ioi] with x hxA hxB hxS' hxS hx0
    have hx : 0 < x := hx0
    have hAB : Integrable (fun s => gA (s, x) + gB (s, x)) (volume.restrict (Ioi 0)) := hxA.add hxB
    have hABS : Integrable (fun s => gA (s, x) + gB (s, x) + gS (s, x)) (volume.restrict (Ioi 0)) :=
      hAB.add hxS'
    rw [← integral_add hxA hxB, ← integral_add hAB hxS']
    refine integral_mono_ae hABS hxS ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hpt s x hs hx
  -- the same-side half
  have hA : ∀ x, 0 < x → (∫ s in Ioi (0 : ℝ), gA (s, x)) = if x < p then
      F x ^ 2 * ∫ y in Ioc x r, surplusKernel x y * (1 - h y / h x) else 0 := by
    intro x hx
    split_ifs with hxp
    · have e := setIntegral_Ioi_translate (fun y => gA (y - x, x)) x
      simp only [add_sub_cancel_right] at e
      rw [← e, ← MeasureTheory.integral_const_mul, ← Ioi_inter_Iic, ← setIntegral_indicator measurableSet_Iic]
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
      simp only [hgA, Set.indicator_apply, mem_Iic, add_sub_cancel, hxp, and_true]
    · refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
      simp only [hgA, Pi.zero_apply]
      rw [if_neg (fun h => hxp h.2)]
  -- the reflected half
  have hB : ∀ x, 0 < x → (∫ s in Ioi (0 : ℝ), gB (s, x)) = ∫ y in Ioi (0 : ℝ), G (x, y) := by
    intro x hx
    have e := setIntegral_Ioi_translate (fun y => gB (y - x, x)) x
    simp only [add_sub_cancel_right] at e
    rw [← e, ← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_indicator measurableSet_Ioi]
    congr 1
    funext y
    simp only [hgB, hG, Set.indicator_apply, mem_Ioi, add_sub_cancel]
    by_cases hxy : x < y
    · rw [if_pos hxy, if_pos (lt_trans hx hxy)]
      by_cases hc : y ≤ r ∧ x < p
      · rw [if_pos hc, if_pos ⟨hxy, hc.1, hc.2⟩]
      · rw [if_neg hc, if_neg (fun h => hc ⟨h.2.1, h.2.2⟩)]
    · rw [if_neg hxy]
      by_cases hy : 0 < y
      · rw [if_pos hy, if_neg (fun h => hxy h.1)]
      · rw [if_neg hy]
  have hBt : ∀ y, 0 < y → (∫ x in Ioi (0 : ℝ), G (x, y)) = if y ≤ r then
      F y ^ 2 * ∫ x in Ioo 0 (min y p), surplusKernel y x * (1 - h x / h y) else 0 := by
    intro y hy
    split_ifs with hyr
    · rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_indicator measurableSet_Ioo,
        ← MeasureTheory.integral_indicator measurableSet_Ioi]
      congr 1
      funext x
      simp only [hG, Set.indicator_apply, mem_Ioi, mem_Ioo, lt_min_iff]
      by_cases hx : 0 < x
      · by_cases hxy : x < y ∧ x < p
        · rw [if_pos hx, if_pos ⟨hxy.1, hyr, hxy.2⟩, if_pos ⟨hx, hxy⟩]
        · rw [if_pos hx, if_neg (fun h => hxy ⟨h.1, h.2.2⟩), if_neg (fun h => hxy h.2)]
      · rw [if_neg hx, if_neg (fun h => hx h.1)]
    · refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
      simp only [hG, Pi.zero_apply]
      rw [if_neg (fun h => hyr h.2.1)]
  -- the strip half
  have hS : ∀ x, 0 < x → (∫ s in Ioi (0 : ℝ), gS (s, x)) = if p ≤ x then
      ∫ y in Ioc x r, stripIntegrand F x y else 0 := by
    intro x hx
    split_ifs with hxp
    · have e := setIntegral_Ioi_translate (fun y => gS (y - x, x)) x
      simp only [add_sub_cancel_right] at e
      rw [← e, ← Ioi_inter_Iic, ← setIntegral_indicator measurableSet_Iic]
      refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
      simp only [hgS, Set.indicator_apply, mem_Iic, add_sub_cancel, hxp, and_true]
    · refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
      simp only [hgS, Pi.zero_apply]
      rw [if_neg (fun h => hxp h.2)]
  -- the potential is the sum of the two transformed halves
  have hint : ∀ x, 0 < x → x ≤ r → IntegrableOn (fun y => surplusKernel x y * (1 - h y / h x)) (Ioc 0 r) :=
    fun x hx hxr => by
      refine Measure.integrableOn_of_bounded (M := 3 / 2 * |L| / a₀) (by simp)
        ((hmk.comp (measurable_const.prodMk measurable_id)).mul (measurable_const.sub
          ((hh.measurable).div measurable_const))).aestronglyMeasurable ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      rw [Real.norm_eq_abs]
      exact hw x y hx hxr hy.1 hy.2
  have hsum : ∀ x, 0 < x → F x ^ 2 * surplusPotentialOff h p r x =
      (∫ s in Ioi (0 : ℝ), gA (s, x)) + ∫ x' in Ioi (0 : ℝ), G (x', x) := by
    intro x hx
    rw [hA x hx, hBt x hx]
    by_cases hxr : x ≤ r
    · rw [if_pos hxr]
      unfold surplusPotentialOff
      by_cases hxp : x < p
      · rw [if_pos hxp, if_pos hxp, min_eq_left hxp.le]
        unfold surplusPotential
        rw [← Ioc_union_Ioc_eq_Ioc hx.le hxr, setIntegral_union (Set.disjoint_left.mpr fun y h1 h2 =>
          by linarith [h1.2, h2.1]) measurableSet_Ioc ((hint x hx hxr).mono_set (Ioc_subset_Ioc_right hxr))
          ((hint x hx hxr).mono_set (Ioc_subset_Ioc_left hx.le)), integral_Ioc_eq_integral_Ioo (x := 0)]
        rw [mul_add]
        ring
      · rw [if_neg hxp, if_neg hxp, min_eq_right (not_lt.mp hxp)]
        ring
    · rw [if_neg hxr, if_neg (fun h => hxr (h.le.trans hpr)),
        hFz x (by rw [abs_of_pos hx]; exact not_le.mp hxr)]
      ring
  have hIsum : IntegrableOn (fun x => F x ^ 2 * surplusPotentialOff h p r x) (Ioi 0) := by
    have h1 : Integrable (fun x => (∫ s in Ioi (0 : ℝ), gA (s, x)) + ∫ x' in Ioi (0 : ℝ), G (x', x))
        (volume.restrict (Ioi 0)) := hIA.integral_prod_right.add hIG.integral_prod_right
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hsum x hx).symm
  refine ⟨hIsum, ?_⟩
  -- the strip part is the strip surplus
  have hstrip : (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), gS (s, x)) = stripSurplus F p r := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun x hx => hS x hx]
    have e1 : (∫ x in Ioi (0 : ℝ), (if p ≤ x then ∫ y in Ioc x r, stripIntegrand F x y else 0)) =
        ∫ x in Ioi (0 : ℝ), (Icc p r).indicator (fun x => ∫ y in Ioc x r, stripIntegrand F x y) x := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
      simp only [Set.indicator_apply, mem_Icc]
      by_cases hxp : p ≤ x
      · rw [if_pos hxp]
        by_cases hxr : x ≤ r
        · rw [if_pos ⟨hxp, hxr⟩]
        · rw [if_neg (fun h => hxr h.2), Ioc_eq_empty (by linarith [not_le.mp hxr]),
            Measure.restrict_empty, integral_zero_measure]
      · rw [if_neg hxp, if_neg (fun h => hxp h.1)]
    rw [e1, setIntegral_indicator measurableSet_Icc,
      Set.inter_eq_right.mpr (fun x hx => mem_Ioi.mpr (lt_of_lt_of_le hp hx.1))]
    rfl
  have hswap : (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), gB (s, x)) =
      ∫ x in Ioi (0 : ℝ), ∫ x' in Ioi (0 : ℝ), G (x', x) := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun x hx => hB x hx]
    exact integral_integral_swap (f := fun x y => G (x, y)) hIG
  have hI1 : Integrable (fun x => ∫ s in Ioi (0 : ℝ), gA (s, x)) (volume.restrict (Ioi 0)) :=
    hIA.integral_prod_right
  have hI2 : Integrable (fun x => ∫ s in Ioi (0 : ℝ), gB (s, x)) (volume.restrict (Ioi 0)) :=
    hIB.integral_prod_right
  have hI3 : Integrable (fun x => ∫ x' in Ioi (0 : ℝ), G (x', x)) (volume.restrict (Ioi 0)) :=
    hIG.integral_prod_right
  have hI4 : Integrable (fun x => ∫ s in Ioi (0 : ℝ), gS (s, x)) (volume.restrict (Ioi 0)) :=
    hIS'.integral_prod_right
  have hI12 : Integrable (fun x => (∫ s in Ioi (0 : ℝ), gA (s, x)) + ∫ s in Ioi (0 : ℝ), gB (s, x))
      (volume.restrict (Ioi 0)) := hI1.add hI2
  rw [setIntegral_congr_fun measurableSet_Ioi hsum, integral_add hI1 hI3, ← hswap, ← hstrip,
    ← integral_add hI1 hI2, ← integral_add hI12 hI4]
  exact hcmp

end OffStrip

/-! ### The atom is dominated up to the window `2/5` -/

/-- **The micro-fold constant beats the atom.** For `p + r = log 2`, `p < r ≤ 2/5`, the micro-fold
constant is at least `0.9804 ≥ 2Λ(2)/√2`: with `d = r − p`,
`C ≥ log 2 + ½ − d/(2p) − d²/12 − d³/17`, and `d/(2p) ≤ 0.183` up to `r = 2/5`. -/
theorem microFoldConstant_ge {p r : ℝ} (hL : p + r = Real.log 2) (hpr : p < r) (hr2 : r ≤ 2 / 5) :
    9804 / 10000 ≤ 2 * (archLevyAntideriv ((r - p) / 2) - archLevyAntideriv (r - p) -
        (r - p) / 2 * archLevyDensity (2 * p)) + (r - p) * microFoldKernel p (r - p) := by
  have hl0 := Real.log_two_gt_d9
  have hl1 := Real.log_two_lt_d9
  set d := r - p with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hp : 2931 / 10000 ≤ p := by linarith
  have hd1 : d ≤ 10686 / 100000 := by rw [hd]; linarith
  have hΩ1 := archLevyAntideriv_ge (show 0 < d / 2 by positivity)
  have hΩ2 := archLevyAntideriv_le_expansion hd0
  have hlog : Real.log (d / 4) = Real.log 2 + Real.log (d / 2 / 4) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]; ring_nf
  have hω1 := archLevyDensity_le_inv (show 0 < 2 * p by linarith)
  have hω2 := inv_le_archLevyDensity hd0
  have e1 : d * (1 / (2 * d) + 1 / 4 - d / 16 - d ^ 2 / 32) =
      1 / 2 + d / 4 - d ^ 2 / 16 - d ^ 3 / 32 := by field_simp
  have e2 : d * (1 / (2 * (2 * p))) ≤ 915 / 10000 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]; rw [hd]; linarith
  have k1 := mul_le_mul_of_nonneg_left hω2 hd0.le
  have k2 := mul_le_mul_of_nonneg_left hω1 hd0.le
  have hd2 : d ^ 2 ≤ 115 / 10000 := by nlinarith
  have hd3 : d ^ 3 ≤ 123 / 100000 := by nlinarith
  unfold microFoldKernel
  rw [e1] at k1
  nlinarith

section Domination

variable {F : ℝ → ℝ} {K r : ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
  (hodd : ∀ x, F (-x) = -F x) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
  (hsupp : ∀ x, r < |x| → F x = 0) (hr : Real.log 2 / 2 < r) (hr2 : r ≤ 2 / 5)

include hF hFc hodd hFL hsupp hr hr2 in
/-- **Harnack across `½ log 2`: the prime `2` is paid by the strip surplus.** For an odd test supported
in `[−r, r]`, `½ log 2 < r ≤ 2/5`, the whole prime term is dominated by the archimedean surplus of the
pairs inside the edge strip `[log 2 − r, r]`:
`2 Λ(2)/√2 ∫ F(x) F(x + log 2) dx ≤ ∫_S ∫_S k(x, y)(F x − F y)² = 2 stripSurplus`. -/
theorem two_mul_primeShift_le_stripSurplus :
    2 * (vonMangoldtAtom 2 * ∫ x, F x * F (x + Real.log 2)) ≤
      2 * stripSurplus F (Real.log 2 - r) r := by
  have hl0 := Real.log_two_gt_d9
  have hl1 := Real.log_two_lt_d9
  set L := Real.log 2 with hLdef
  set p := L - r with hpdef
  have hpr : p < r := by rw [hpdef]; linarith
  have hp : 0 < p := by rw [hpdef]; linarith
  have hL : p + r = L := by rw [hpdef]; ring
  have hr3 : r - p ≤ 2 * p := by rw [hpdef]; linarith
  have hr1 : r - p ≤ 1 := by rw [hpdef]; linarith
  have hms := microFold_strip_ge hF hFL hp hpr hL hr3 hr1
  have hT : (∫ x in p..r, ∫ y in p..r, surplusKernel x y * (F x - F y) ^ 2) =
      2 * stripSurplus F p r := integral_strip_eq_two_mul_stripSurplus hF hFL hp hpr.le hr1
  have hshift := integral_mul_shift_le_reflectedOdd hF hFc hodd (r := r) (L := L) (by linarith)
    (by rw [← hpdef]; exact hpr.le) hsupp
  rw [← hpdef] at hshift
  have hC := microFoldConstant_ge hL hpr hr2
  obtain ⟨hΛ0, hΛ1⟩ := vonMangoldtAtom_two_bounds
  have hα0 : 0 ≤ ∫ x in p..r, reflectedOddPart F L x ^ 2 :=
    intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  have k1 := mul_le_mul_of_nonneg_left hshift hΛ0
  have k2 := mul_le_mul_of_nonneg_right hC hα0
  have k3 := mul_le_mul_of_nonneg_right hΛ1 hα0
  linarith

end Domination

section Reduction

variable {P F : ℝ → ℝ} {B K : ℝ} (hPc : Continuous P) (hFc : Continuous F)
  (hPe : ∀ x, P (-x) = P x) (hFo : ∀ x, F (-x) = -F x) (hP0 : ∀ x, 0 ≤ P x)
  (hP1 : ∀ x, P x ≤ 1) (hPB : ∀ x, B ≤ |x| → P x = 0) (hFB : ∀ x, B ≤ |x| → F x = 0)
  (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hB0 : 0 < B) (hB1 : 2 * B ≤ 1)

include hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 hB1 in
/-- **The first prime window is atom-free.** For an odd test supported in `[−r, r]`,
`½ log 2 < r ≤ 2/5`, under a plateau equal to `1` on `[−r, r]`, the archimedean jump energy minus the
prime term `2Λ(2)/√2 ∫ F(x) F(x + log 2)` still dominates the killing and the ground-state potential of
the pairs off the edge strip `[log 2 − r, r]`:
`4 ∫ F²(Ω(x) − Ω(x + r)) + 2 ∫ F² U_h^{off} ≤ J_arch − 2Λ(2)/√2 ∫ F(x) F(x + log 2)`. -/
theorem fourKilling_add_potentialOff_le_archJump_sub_prime {h : ℝ → ℝ} {r a₀ L : ℝ}
    (hFcs : HasCompactSupport F) (hr : Real.log 2 / 2 < r) (hr2 : r ≤ 2 / 5) (hrB : r ≤ B)
    (hPr : ∀ x, |x| ≤ r → P x = 1) (hFr : ∀ x, F x ≠ 0 → |x| ≤ r) (hPcs : HasCompactSupport P)
    (hh : Continuous h) (ha₀ : 0 < a₀) (hhpos : ∀ x, 0 ≤ x → x ≤ r → a₀ ≤ h x)
    (hhL : ∀ x y, 0 ≤ x → x ≤ r → 0 ≤ y → y ≤ r → |h x - h y| ≤ L * |x - y|) :
    IntegrableOn (fun x => F x ^ 2 * surplusPotentialOff h (Real.log 2 - r) r x) (Ioi 0) ∧
      4 * (∫ x in Ioi (0 : ℝ), F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) +
          2 * (∫ x in Ioi (0 : ℝ), F x ^ 2 * surplusPotentialOff h (Real.log 2 - r) r x) ≤
        (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) -
          2 * (vonMangoldtAtom 2 * ∫ x, F x * F (x + Real.log 2)) := by
  have hl0 := Real.log_two_gt_d9
  have hl1 := Real.log_two_lt_d9
  have hr0 : 0 < r := by linarith
  obtain ⟨hI, hle⟩ := surplusEnergy_ge_potentialOff_add_strip hPc hFc hFo hP0 hP1 hPB hFL hB0 hB1
    (p := Real.log 2 - r) (by linarith) (by linarith) hrB hPr hFr hh ha₀ hhpos hhL
  have hfold := fourKilling_add_surplusEnergy_le_archJump hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0
    hB1 hr0 hrB hPr hFr hPcs
  have hsupp : ∀ x, r < |x| → F x = 0 := fun x hx => by
    by_contra h0; exact absurd (hFr x h0) (not_le.mpr hx)
  have hdom := two_mul_primeShift_le_stripSurplus hFc hFcs hFo hFL hsupp hr hr2
  exact ⟨hI, by linarith⟩

end Reduction

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
