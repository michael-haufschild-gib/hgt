import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeLightConeAllocation
import GaloisForLFunctions.RHTower.Sieve.ChebyshevPNT

/-!
# Outside the light cone the odd parts cannot share the surplus

The micro-folds of `SharpMicroFoldHarnack` and `NestedStripShellMicroFold` pay the odd part
`∫_{S_n} α_n²` of each atom from archimedean surplus. Every strip `S_n = [log n − r, r]` contains the
edge `r`, so a test concentrated at the edge is charged by every strip at once, while its surplus is
that of a single bump. The edge tent `τ` of width `ε` (`edgeTent`, odd extension `edgeTentOdd`) makes this
exact:

* for every `L ∈ [r, 2r − 2ε]` the shift product `F(x) F(x + L)` vanishes identically, so the atom of
  `e^L` is zero and `∫_{L−r}^{r} α_L² = ½ ∫_{L−r}^{r} F² ≥ ε³/64` (`edgeTent_oddPart_eq`);
* the surplus of all pairs of the support is small: `T(0, r) ≤ 3ε²r`
  (`stripBoxEnergy_edgeTent_le`; pointwise `k(x, y)(F x − F y)² ≤ (3/2)ε` off `[0, r − ε]²`).

So any allocation of the surplus of `[0, r]²` to the odd parts of a family of strips wider than `ε`
needs `Σ Λ(n)/√n ≤ 96 r/ε`. By the prime number theorem the thin band `2r − 1/6 ≤ log n ≤ 2r − 1/24`
carries `Σ Λ(n)/√n ≍ e^r`. Hence (`exists_edgeTent_oddPart_sharing_fails`): for all large `r` there is
an odd test on which every atom of the thin band vanishes and every one of their odd parts is paid by
its own strip (`λ₀ ≥ 2Λ(n)/√n`), yet the odd parts together exceed the whole surplus of `[0, r]²`.

The per-strip Harnack inequality across prime shifts does not globalize through the odd parts. A
global allocation must keep the even parts, which cancel the odd parts exactly on this test; the
surplus alone pays the odd parts only in the light cone (`PrimeLightConeAllocation`).
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The edge tent -/

/-- The tent of width `ε` at the edge `r`: `max(ε/2 − |x − (r − ε/2)|, 0)`, supported in `[r − ε, r]`. -/
def edgeTent (r ε x : ℝ) : ℝ := max (ε / 2 - |x - (r - ε / 2)|) 0

/-- The odd test of the edge tent: `τ(x) − τ(−x)`. -/
def edgeTentOdd (r ε x : ℝ) : ℝ := edgeTent r ε x - edgeTent r ε (-x)

theorem edgeTent_nonneg (r ε x : ℝ) : 0 ≤ edgeTent r ε x := le_max_right _ _

theorem edgeTent_eq_zero_of_le {r ε x : ℝ} (hx : x ≤ r - ε) : edgeTent r ε x = 0 := by
  unfold edgeTent
  refine max_eq_right ?_
  have : r - ε / 2 - x ≤ |x - (r - ε / 2)| := by rw [abs_sub_comm]; exact le_abs_self _
  linarith

theorem edgeTent_eq_zero_of_ge {r ε x : ℝ} (hx : r ≤ x) : edgeTent r ε x = 0 := by
  unfold edgeTent
  refine max_eq_right ?_
  have : x - (r - ε / 2) ≤ |x - (r - ε / 2)| := le_abs_self _
  linarith

/-- The tent vanishes outside `(r − ε, r)`. -/
theorem mem_of_edgeTent_ne_zero {r ε x : ℝ} (h : edgeTent r ε x ≠ 0) : r - ε < x ∧ x < r := by
  by_contra hc
  rcases not_and_or.mp hc with h1 | h1
  · exact h (edgeTent_eq_zero_of_le (not_lt.mp h1))
  · exact h (edgeTent_eq_zero_of_ge (not_lt.mp h1))

/-- Above the foot `r − ε` the tent is at most the distance to the foot. -/
theorem edgeTent_le_sub {r ε x : ℝ} (hx : r - ε ≤ x) : edgeTent r ε x ≤ x - (r - ε) := by
  unfold edgeTent
  refine max_le ?_ (by linarith)
  linarith [neg_abs_le (x - (r - ε / 2))]

/-- On the middle half of its support the tent is at least `ε/4`. -/
theorem edgeTent_ge_quarter {r ε x : ℝ} (h1 : r - ε + ε / 4 ≤ x) (h2 : x ≤ r - ε + 3 * ε / 4) :
    ε / 4 ≤ edgeTent r ε x := by
  unfold edgeTent
  refine le_trans ?_ (le_max_left _ _)
  have : |x - (r - ε / 2)| ≤ ε / 4 := by rw [abs_le]; constructor <;> linarith
  linarith

theorem abs_edgeTent_sub_le (r ε x y : ℝ) : |edgeTent r ε x - edgeTent r ε y| ≤ |x - y| := by
  unfold edgeTent
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  rw [show ε / 2 - |x - (r - ε / 2)| - (ε / 2 - |y - (r - ε / 2)|) =
    |y - (r - ε / 2)| - |x - (r - ε / 2)| by ring]
  refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
  rw [show y - (r - ε / 2) - (x - (r - ε / 2)) = y - x by ring, abs_sub_comm]

theorem continuous_edgeTent (r ε : ℝ) : Continuous (edgeTent r ε) := by
  unfold edgeTent; fun_prop

theorem continuous_edgeTentOdd (r ε : ℝ) : Continuous (edgeTentOdd r ε) := by
  unfold edgeTentOdd
  exact (continuous_edgeTent r ε).sub ((continuous_edgeTent r ε).comp continuous_neg)

theorem edgeTentOdd_odd (r ε x : ℝ) : edgeTentOdd r ε (-x) = -edgeTentOdd r ε x := by
  unfold edgeTentOdd; rw [neg_neg]; ring

theorem edgeTentOdd_lipschitz (r ε a b : ℝ) :
    |edgeTentOdd r ε a - edgeTentOdd r ε b| ≤ 2 * |a - b| := by
  unfold edgeTentOdd
  have h1 := abs_edgeTent_sub_le r ε a b
  have h2 := abs_edgeTent_sub_le r ε (-a) (-b)
  rw [show -a - -b = -(a - b) by ring, abs_neg] at h2
  have := abs_sub (edgeTent r ε a - edgeTent r ε b) (edgeTent r ε (-a) - edgeTent r ε (-b))
  rw [show edgeTent r ε a - edgeTent r ε (-a) - (edgeTent r ε b - edgeTent r ε (-b)) =
    edgeTent r ε a - edgeTent r ε b - (edgeTent r ε (-a) - edgeTent r ε (-b)) by ring]
  linarith

section Odd

variable {r ε : ℝ} (hε0 : 0 < ε) (hεr : ε < r)

include hε0 hεr in
theorem edgeTentOdd_eq_zero_of_lt {x : ℝ} (hx : r < |x|) : edgeTentOdd r ε x = 0 := by
  unfold edgeTentOdd
  rcases le_or_gt 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at hx
    rw [edgeTent_eq_zero_of_ge hx.le, edgeTent_eq_zero_of_le (by linarith)]; ring
  · rw [abs_of_neg h0] at hx
    rw [edgeTent_eq_zero_of_le (by linarith), edgeTent_eq_zero_of_ge hx.le]; ring

include hε0 hεr in
theorem hasCompactSupport_edgeTentOdd : HasCompactSupport (edgeTentOdd r ε) :=
  HasCompactSupport.intro (isCompact_Icc (a := -r) (b := r)) fun x hx => by
    refine edgeTentOdd_eq_zero_of_lt hε0 hεr ?_
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with h | h
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; exact h

include hεr in
/-- On `[0, ∞)` the odd test is the tent. -/
theorem edgeTentOdd_of_nonneg {x : ℝ} (hx : 0 ≤ x) : edgeTentOdd r ε x = edgeTent r ε x := by
  unfold edgeTentOdd; rw [edgeTent_eq_zero_of_le (x := -x) (by linarith), sub_zero]

include hεr in
/-- The odd test vanishes off `(r − ε, r) ∪ (−r, −(r − ε))`. -/
theorem mem_of_edgeTentOdd_ne_zero {x : ℝ} (h : edgeTentOdd r ε x ≠ 0) :
    (r - ε < x ∧ x < r) ∨ (r - ε < -x ∧ -x < r) := by
  unfold edgeTentOdd at h
  by_cases h1 : edgeTent r ε x = 0
  · right
    rw [h1, zero_sub, neg_ne_zero] at h
    exact mem_of_edgeTent_ne_zero h
  · left; exact mem_of_edgeTent_ne_zero h1

end Odd

/-! ### Every atom of the band vanishes on the edge tent -/

/-- For `r ≤ L ≤ 2(r − ε)` the shift product of the edge tent vanishes identically: a point of the
right tent is moved past `r`, a point of the left tent lands in `(L − r, L − r + ε) ⊂ [0, r − ε]`. -/
theorem edgeTentOdd_mul_shift_eq_zero {r ε L : ℝ} (hε0 : 0 < ε) (hεr : ε < r) (hrL : r ≤ L)
    (hL : L ≤ 2 * (r - ε)) (x : ℝ) : edgeTentOdd r ε x * edgeTentOdd r ε (x + L) = 0 := by
  by_contra h
  have h1 := mem_of_edgeTentOdd_ne_zero hεr (left_ne_zero_of_mul h)
  have h2 := mem_of_edgeTentOdd_ne_zero hεr (right_ne_zero_of_mul h)
  rcases h1 with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases h2 with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> linarith

/-- **The odd part on the edge tent.** For `r ≤ L ≤ 2(r − ε)` the atom of `e^L` vanishes and the odd
part about `L/2` carries half the mass of the strip: `2∫_{L−r}^{r} α² = ∫_{L−r}^{r} F²`. -/
theorem edgeTent_oddPart_eq {r ε L : ℝ} (hε0 : 0 < ε) (hεr : ε < r) (hrL : r ≤ L)
    (hL : L ≤ 2 * (r - ε)) :
    (∫ x, edgeTentOdd r ε x * edgeTentOdd r ε (x + L)) = 0 ∧
      2 * (∫ a in (L - r)..r, reflectedOddPart (edgeTentOdd r ε) L a ^ 2) =
        ∫ a in (L - r)..r, edgeTentOdd r ε a ^ 2 := by
  have h0 : (∫ x, edgeTentOdd r ε x * edgeTentOdd r ε (x + L)) = 0 := by
    simp_rw [edgeTentOdd_mul_shift_eq_zero hε0 hεr hrL hL, integral_zero]
  refine ⟨h0, ?_⟩
  have h := integral_mul_shift_eq_two_reflectedOdd_sub (continuous_edgeTentOdd r ε)
    (edgeTentOdd_odd r ε) (r := r) (L := L) (by linarith) (by linarith)
    fun x hx => edgeTentOdd_eq_zero_of_lt hε0 hεr hx
  rw [h0] at h
  linarith

/-- The strip carries at least `ε³/32` of tent mass whenever it reaches below `r − ε`. -/
theorem edgeTent_sq_integral_ge {r ε L : ℝ} (hε0 : 0 < ε) (hεr : ε < r) (hL : L - r ≤ r - ε) :
    ε ^ 3 / 32 ≤ ∫ a in (L - r)..r, edgeTentOdd r ε a ^ 2 := by
  set F := edgeTentOdd r ε with hFdef
  have hFc : Continuous fun a => F a ^ 2 := (continuous_edgeTentOdd r ε).pow 2
  have hsub := intervalIntegral.integral_mono_interval (μ := volume) (f := fun a => F a ^ 2)
    (a := r - ε + ε / 4) (b := r - ε + 3 * ε / 4) (c := L - r) (d := r) (by linarith) (by linarith)
    (by linarith) (Filter.Eventually.of_forall fun x => by simp only [Pi.zero_apply]; positivity)
    (hFc.intervalIntegrable _ _)
  have hlow := intervalIntegral.integral_mono_on (μ := volume) (f := fun _ => (ε / 4) ^ 2)
    (g := fun a => F a ^ 2) (a := r - ε + ε / 4) (b := r - ε + 3 * ε / 4) (by linarith)
    intervalIntegrable_const (hFc.intervalIntegrable _ _) fun x hx => by
      have hx0 : 0 ≤ x := by linarith [hx.1]
      have h := edgeTent_ge_quarter hx.1 hx.2
      rw [hFdef, edgeTentOdd_of_nonneg hεr hx0]
      exact pow_le_pow_left₀ (by positivity) h 2
  rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
  have e : (r - ε + 3 * ε / 4 - (r - ε + ε / 4)) * (ε / 4) ^ 2 = ε ^ 3 / 32 := by ring
  linarith

/-! ### The surplus of the edge tent -/

/-- `k(x, y) τ(x)² ≤ (3/2)(x − a)` for a pair across the foot `a = r − ε`, `y ≤ a < x`:
`ω(x − y) ≤ 3/(2(x − a))` because `x − y ≥ x − a` and `x − a ≤ ε ≤ 1`. -/
theorem surplusKernel_mul_edgeTent_sq_le {r ε x y : ℝ} (hε1 : ε ≤ 1) (hy0 : 0 ≤ y)
    (hya : y ≤ r - ε) (hax : r - ε < x) (hxr : x ≤ r) :
    surplusKernel x y * edgeTent r ε x ^ 2 ≤ 3 / 2 * (x - (r - ε)) := by
  set d := x - (r - ε) with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have hx0 : 0 < x := by linarith
  have hτ0 := edgeTent_nonneg r ε x
  have hτ := edgeTent_le_sub hax.le
  have hτ2 : edgeTent r ε x ^ 2 ≤ d ^ 2 := pow_le_pow_left₀ hτ0 hτ 2
  rcases eq_or_lt_of_le hy0 with hy | hy
  · rw [← hy, surplusKernel_comm, surplusKernel_zero_left hx0.le, zero_mul]; positivity
  have hxy : 0 < x - y := by linarith
  have hk := surplusKernel_le hx0 hy
  rw [abs_of_pos hxy] at hk
  have hd1 : d ≤ 1 := by rw [hd]; linarith
  -- `ω(x − y) ≤ 3/(2d)`
  have hω : archLevyDensity (x - y) ≤ 3 / 2 / d := by
    rcases le_or_gt (x - y) 1 with h1 | h1
    · refine (archLevyDensity_le_of_le_one hxy h1).trans ?_
      exact div_le_div_of_nonneg_left (by norm_num) hd0 (by rw [hd]; linarith)
    · have hmono : archLevyDensity (x - y) ≤ archLevyDensity 1 :=
        strictAntiOn_archLevyDensity.antitoneOn (show (0 : ℝ) < 1 by norm_num) hxy h1.le
      have h1' := archLevyDensity_le_of_le_one (show (0 : ℝ) < 1 by norm_num) le_rfl
      have : (3 : ℝ) / 2 / 1 ≤ 3 / 2 / d := div_le_div_of_nonneg_left (by norm_num) hd0 hd1
      linarith
  calc surplusKernel x y * edgeTent r ε x ^ 2 ≤ 3 / 2 / d * d ^ 2 :=
        mul_le_mul (hk.trans hω) hτ2 (sq_nonneg _) (by positivity)
    _ = 3 / 2 * d := by field_simp

/-- The comparison weight `(3/2)ε(1_{x > a} + 1_{y > a})`, `a = r − ε`. -/
def edgeTentWeight (r ε x y : ℝ) : ℝ :=
  3 / 2 * ε * (if r - ε < x then 1 else 0) + 3 / 2 * ε * (if r - ε < y then 1 else 0)

/-- Pointwise surplus of the edge tent on `[0, r]²`: `0 ≤ k(x, y)(F x − F y)² ≤ edgeTentWeight`. -/
theorem stripIntegrand_edgeTentOdd_bounds {r ε x y : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hεr : ε < r) (hx : x ∈ Icc 0 r) (hy : y ∈ Icc 0 r) :
    0 ≤ stripIntegrand (edgeTentOdd r ε) x y ∧
      stripIntegrand (edgeTentOdd r ε) x y ≤ edgeTentWeight r ε x y := by
  have hFx := edgeTentOdd_of_nonneg hεr hx.1
  have hFy := edgeTentOdd_of_nonneg hεr hy.1
  have hW0 : 0 ≤ edgeTentWeight r ε x y := by
    unfold edgeTentWeight; split_ifs <;> positivity
  unfold stripIntegrand
  rw [hFx, hFy]
  by_cases hxy : x = y
  · subst hxy
    rw [sub_self]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
    exact ⟨le_rfl, hW0⟩
  have hk0 := surplusKernel_nonneg' hx.1 hy.1 hxy
  refine ⟨mul_nonneg hk0 (sq_nonneg _), ?_⟩
  rcases le_or_gt x (r - ε) with hxa | hxa <;> rcases le_or_gt y (r - ε) with hya | hya
  · -- both below the foot
    rw [edgeTent_eq_zero_of_le hxa, edgeTent_eq_zero_of_le hya, sub_self]; simpa using hW0
  · -- `y` on the tent
    rw [edgeTent_eq_zero_of_le hxa, zero_sub, neg_sq, surplusKernel_comm]
    have h := surplusKernel_mul_edgeTent_sq_le hε1 hx.1 hxa hya hy.2
    unfold edgeTentWeight; rw [if_neg (not_lt.mpr hxa), if_pos hya]
    linarith [hy.2]
  · -- `x` on the tent
    rw [edgeTent_eq_zero_of_le hya, sub_zero]
    have h := surplusKernel_mul_edgeTent_sq_le hε1 hy.1 hya hxa hx.2
    unfold edgeTentWeight; rw [if_pos hxa, if_neg (not_lt.mpr hya)]
    linarith [hx.2]
  · -- both on the tent: `k ≤ 3/(2|x − y|)` and the tent is `1`-Lipschitz
    have hx0 : 0 < x := by linarith
    have hy0 : 0 < y := by linarith
    have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have hdε : |x - y| ≤ ε := by rw [abs_le]; constructor <;> linarith [hx.2, hy.2]
    have hk := (surplusKernel_le hx0 hy0).trans (archLevyDensity_le_of_le_one hd (by linarith))
    have hL := abs_edgeTent_sub_le r ε x y
    have hL2 : (edgeTent r ε x - edgeTent r ε y) ^ 2 ≤ |x - y| ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hL 2
    have h : surplusKernel x y * (edgeTent r ε x - edgeTent r ε y) ^ 2 ≤ 3 / 2 * |x - y| := by
      calc surplusKernel x y * (edgeTent r ε x - edgeTent r ε y) ^ 2 ≤
            3 / 2 / |x - y| * |x - y| ^ 2 := mul_le_mul hk hL2 (sq_nonneg _) (by positivity)
        _ = 3 / 2 * |x - y| := by field_simp
    unfold edgeTentWeight; rw [if_pos hxa, if_pos hya]
    linarith

/-- **The surplus of the edge tent.** All pairs of `[0, r]²` together carry
`T(0, r) ≤ 3ε²r` for the odd edge tent of width `ε ≤ 1`. -/
theorem stripBoxEnergy_edgeTent_le {r ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hεr : ε < r) :
    stripBoxEnergy (edgeTentOdd r ε) 0 r ≤ 3 * ε ^ 2 * r := by
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hi1 : Measurable fun z : ℝ × ℝ => if r - ε < z.1 then (1 : ℝ) else 0 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_const
      measurable_const
  have hi2 : Measurable fun z : ℝ × ℝ => if r - ε < z.2 then (1 : ℝ) else 0 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_snd) measurable_const
      measurable_const
  have hBm : Measurable (Function.uncurry (edgeTentWeight r ε)) :=
    (hi1.const_mul _).add (hi2.const_mul _)
  have hBb : ∀ x ∈ Icc 0 r, ∀ y ∈ Icc 0 r, |edgeTentWeight r ε x y| ≤ 3 * ε := fun x _ y _ => by
    unfold edgeTentWeight
    split_ifs <;> rw [abs_of_nonneg (by positivity)] <;> linarith
  have hgm := measurable_stripIntegrand (continuous_edgeTentOdd r ε)
  have hgb : ∀ x ∈ Icc 0 r, ∀ y ∈ Icc 0 r, |stripIntegrand (edgeTentOdd r ε) x y| ≤ 3 * ε :=
    fun x hx y hy => by
      obtain ⟨h0, h1⟩ := stripIntegrand_edgeTentOdd_bounds hε0 hε1 hεr hx hy
      rw [abs_of_nonneg h0]
      exact h1.trans ((le_abs_self _).trans (hBb x hx y hy))
  obtain ⟨hgi, hgo⟩ := intervalIntegrable_iterated hr0 hgm hgb
  obtain ⟨hBi, hBo⟩ := intervalIntegrable_iterated hr0 hBm hBb
  have hmono : stripBoxEnergy (edgeTentOdd r ε) 0 r ≤
      ∫ x in (0 : ℝ)..r, ∫ y in (0 : ℝ)..r, edgeTentWeight r ε x y := by
    unfold stripBoxEnergy
    refine intervalIntegral.integral_mono_on hr0 hgo hBo fun x hx => ?_
    exact intervalIntegral.integral_mono_on hr0 (hgi x hx) (hBi x hx) fun y hy =>
      (stripIntegrand_edgeTentOdd_bounds hε0 hε1 hεr hx hy).2
  -- `∫_0^r 1_{y > r − ε} dy = ε`
  have hind : (∫ y in (0 : ℝ)..r, if r - ε < y then (1 : ℝ) else 0) = ε := by
    rw [integral_ite_lt (φ := fun _ => (1 : ℝ)) (by linarith) (by linarith),
      intervalIntegral.integral_const, smul_eq_mul, mul_one]
    ring
  have hindi : IntervalIntegrable (fun y => if r - ε < y then (1 : ℝ) else 0) volume 0 r :=
    intervalIntegrable_of_abs_le (C := 1) hr0
      (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
        measurable_const) fun y _ => by split_ifs <;> simp
  have hinner : ∀ x, (∫ y in (0 : ℝ)..r, edgeTentWeight r ε x y) =
      3 / 2 * ε * (if r - ε < x then 1 else 0) * r + 3 / 2 * ε * ε := fun x => by
    unfold edgeTentWeight
    rw [intervalIntegral.integral_add intervalIntegrable_const (hindi.const_mul _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul, hind, smul_eq_mul]
    ring
  have houter : (∫ x in (0 : ℝ)..r, ∫ y in (0 : ℝ)..r, edgeTentWeight r ε x y) = 3 * ε ^ 2 * r := by
    simp_rw [hinner]
    rw [intervalIntegral.integral_add (((hindi.const_mul (3 / 2 * ε)).mul_const r))
      intervalIntegrable_const, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul, hind, intervalIntegral.integral_const, smul_eq_mul]
    ring
  linarith

/-! ### The thin band and the prime number theorem -/

/-- The thin band of `r`: `2r − 1/6 ≤ log n ≤ 2r − 1/24`, the strips of half-width in `[1/48, 1/12]`. -/
def thinBand (r : ℝ) : Finset ℕ :=
  (Finset.range ⌈Real.exp (2 * r)⌉₊).filter fun n =>
    2 * r - 1 / 6 ≤ Real.log n ∧ Real.log n ≤ 2 * r - 1 / 24

/-- `(ψ(X) − ψ(Y))/√X ≤ Σ_{thin band} Λ(n)/√n` with `X = e^{2r − 1/24}`, `Y = e^{2r − 1/6}`. -/
theorem psi_sub_div_le_sum_thinBand {r : ℝ} (hr : 1 ≤ r) :
    ((∑ n ∈ Finset.range (⌊Real.exp (2 * r - 1 / 24)⌋₊ + 1), ArithmeticFunction.vonMangoldt n) -
        ∑ n ∈ Finset.range (⌊Real.exp (2 * r - 1 / 6)⌋₊ + 1), ArithmeticFunction.vonMangoldt n) /
        Real.sqrt (Real.exp (2 * r - 1 / 24)) ≤ ∑ n ∈ thinBand r, vonMangoldtAtom n := by
  set X := Real.exp (2 * r - 1 / 24) with hX
  set Y := Real.exp (2 * r - 1 / 6) with hY
  have hYX : Y ≤ X := Real.exp_le_exp.mpr (by linarith)
  have hY2 : 2 < Y := by
    have := Real.add_one_le_exp (2 * r - 1 / 6); rw [← hY] at this; linarith
  have hX0 : 0 ≤ X := (Real.exp_pos _).le
  have hfl : ⌊Y⌋₊ + 1 ≤ ⌊X⌋₊ + 1 := Nat.add_le_add_right (Nat.floor_le_floor hYX) 1
  rw [← Finset.sum_Ico_eq_sub _ hfl, Finset.sum_div]
  have hmem : ∀ n ∈ Finset.Ico (⌊Y⌋₊ + 1) (⌊X⌋₊ + 1), Y < n ∧ (n : ℝ) ≤ X := fun n hn => by
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hn
    refine ⟨(Nat.lt_floor_add_one Y).trans_le (by exact_mod_cast h1), ?_⟩
    exact (Nat.cast_le.mpr (Nat.lt_succ_iff.mp h2)).trans (Nat.floor_le hX0)
  have hsub : Finset.Ico (⌊Y⌋₊ + 1) (⌊X⌋₊ + 1) ⊆ thinBand r := fun n hn => by
    obtain ⟨h1, h2⟩ := hmem n hn
    have hn0 : (0 : ℝ) < n := by linarith
    simp only [thinBand, Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_, ?_⟩
    · have hX2 : X < Real.exp (2 * r) := Real.exp_lt_exp.mpr (by linarith)
      have : (n : ℝ) < ⌈Real.exp (2 * r)⌉₊ := lt_of_lt_of_le (h2.trans_lt hX2) (Nat.le_ceil _)
      exact_mod_cast this
    · have := Real.log_lt_log (by positivity) h1
      rw [hY, Real.log_exp] at this; linarith
    · have := Real.log_le_log hn0 h2
      rw [hX, Real.log_exp] at this; exact this
  calc ∑ n ∈ Finset.Ico (⌊Y⌋₊ + 1) (⌊X⌋₊ + 1), ArithmeticFunction.vonMangoldt n / Real.sqrt X
      ≤ ∑ n ∈ Finset.Ico (⌊Y⌋₊ + 1) (⌊X⌋₊ + 1), vonMangoldtAtom n := by
        refine Finset.sum_le_sum fun n hn => ?_
        obtain ⟨h1, h2⟩ := hmem n hn
        have hn2 : 2 ≤ n := by
          have : (2 : ℝ) < n := hY2.trans h1
          exact_mod_cast this.le
        unfold vonMangoldtAtom
        rw [if_pos hn2]
        exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg
          (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt h2)
    _ ≤ ∑ n ∈ thinBand r, vonMangoldtAtom n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => vonMangoldtAtom_nonneg n

/-- **The thin band outgrows every linear budget.** For every `C ≥ 0`, eventually
`C r < Σ_{thin band} Λ(n)/√n`: by the prime number theorem the band carries
`(ψ(X) − ψ(e^{−1/8}X))/√X ≥ √X/11`. -/
theorem eventually_lt_sum_thinBand {C : ℝ} (hC : 0 ≤ C) :
    ∀ᶠ r in atTop, C * r < ∑ n ∈ thinBand r, vonMangoldtAtom n := by
  have hpnt := RHTower.Sieve.tendsto_sum_vonMangoldt_div
  have hlin : ∀ c : ℝ, Tendsto (fun r : ℝ => Real.exp (2 * r - c)) atTop atTop := fun c =>
    Real.tendsto_exp_atTop.comp (tendsto_atTop_add_const_right _ _
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2)))
  have h1 := (hpnt.comp (hlin (1 / 24))).eventually (lt_mem_nhds (show (99 / 100 : ℝ) < 1 by norm_num))
  have h2 := (hpnt.comp (hlin (1 / 6))).eventually
    (gt_mem_nhds (show (1 : ℝ) < 101 / 100 by norm_num))
  have h3 := (Real.tendsto_exp_div_pow_atTop 1).eventually (eventually_ge_atTop (48 * (C + 1)))
  filter_upwards [h1, h2, h3, eventually_ge_atTop (1 : ℝ)] with r h1 h2 h3 hr
  simp only [Function.comp_apply] at h1 h2
  set X := Real.exp (2 * r - 1 / 24) with hX
  set Y := Real.exp (2 * r - 1 / 6) with hY
  set ψX := ∑ n ∈ Finset.range (⌊X⌋₊ + 1), ArithmeticFunction.vonMangoldt n with hψX
  set ψY := ∑ n ∈ Finset.range (⌊Y⌋₊ + 1), ArithmeticFunction.vonMangoldt n with hψY
  have hX0 : 0 < X := Real.exp_pos _
  have hY0 : 0 < Y := Real.exp_pos _
  rw [lt_div_iff₀ hX0] at h1
  rw [div_lt_iff₀ hY0] at h2
  -- `Y = e^{−1/8} X ≤ (8/9) X`
  have hYX : Y ≤ 8 / 9 * X := by
    have e : Y = X * Real.exp (-(1 / 8)) := by rw [hX, hY, ← Real.exp_add]; ring_nf
    have h8 : 9 / 8 ≤ Real.exp (1 / 8) := by linarith [Real.add_one_le_exp (1 / 8 : ℝ)]
    have h8' : Real.exp (-(1 / 8)) ≤ 8 / 9 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
    rw [e]; nlinarith
  have hgap : X / 11 ≤ ψX - ψY := by nlinarith
  -- `√X = e^{r − 1/48} ≥ e^r/2`
  have hsq : Real.sqrt X = Real.exp (r - 1 / 48) := by
    rw [hX, ← Real.exp_half]; ring_nf
  have hsq0 : 0 < Real.sqrt X := by rw [hsq]; exact Real.exp_pos _
  have hhalf : Real.exp r / 2 ≤ Real.exp (r - 1 / 48) := by
    have e : Real.exp (r - 1 / 48) = Real.exp r * Real.exp (-(1 / 48)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have := Real.add_one_le_exp (-(1 / 48) : ℝ)
    nlinarith [Real.exp_pos r]
  have hXs : X = Real.sqrt X * Real.sqrt X := (Real.mul_self_sqrt hX0.le).symm
  have hband := psi_sub_div_le_sum_thinBand hr
  rw [← hX, ← hY, ← hψX, ← hψY] at hband
  have hdiv : Real.sqrt X / 11 ≤ (ψX - ψY) / Real.sqrt X := by
    rw [le_div_iff₀ hsq0]; nlinarith
  -- `e^r ≥ 48(C + 1) r`
  rw [pow_one, le_div_iff₀ (by linarith)] at h3
  have hCr : C * r + 1 ≤ (C + 1) * r := by nlinarith
  nlinarith

/-! ### The obstruction -/

/-- **Outside the light cone the odd parts cannot share the surplus.** For all large `r` there is an
odd test `F` (the edge tent of width `1/48`), continuous, `2`-Lipschitz and supported in `[−r, r]`,
such that for every `n` of the thin band `2r − 1/6 ≤ log n ≤ 2r − 1/24`:

* the atom of `n` vanishes, `∫ F(x) F(x + log n) dx = 0`;
* its odd part is paid by its own strip, `2Λ(n)/√n ∫_{S_n} α_n² ≤ T(S_n)` (sharp micro-fold);

and yet the odd parts together exceed the surplus of all pairs of the support:
`T(0, r) < Σ_{thin band} 2Λ(n)/√n ∫_{S_n} α_n²`. -/
theorem exists_edgeTent_oddPart_sharing_fails :
    ∃ r₀ : ℝ, ∀ r ≥ r₀, ∃ F : ℝ → ℝ, Continuous F ∧ HasCompactSupport F ∧
      (∀ x, F (-x) = -F x) ∧ (∀ a b, |F a - F b| ≤ 2 * |a - b|) ∧ (∀ x, r < |x| → F x = 0) ∧
      (∀ n ∈ thinBand r, (∫ x, F x * F (x + Real.log n)) = 0 ∧
        2 * vonMangoldtAtom n * (∫ a in (Real.log n - r)..r, reflectedOddPart F (Real.log n) a ^ 2) ≤
          stripBoxEnergy F (Real.log n - r) r) ∧
      stripBoxEnergy F 0 r <
        ∑ n ∈ thinBand r,
          2 * vonMangoldtAtom n * ∫ a in (Real.log n - r)..r, reflectedOddPart F (Real.log n) a ^ 2 := by
  obtain ⟨r₀, hr₀⟩ := Filter.eventually_atTop.mp
    ((eventually_lt_sum_thinBand (C := 4608) (by norm_num)).and (eventually_ge_atTop (1 : ℝ)))
  refine ⟨r₀, fun r hr => ?_⟩
  obtain ⟨hmass, hr1⟩ := hr₀ r hr
  set ε : ℝ := 1 / 48 with hεdef
  have hε0 : 0 < ε := by norm_num
  have hεr : ε < r := by rw [hεdef]; linarith
  set F := edgeTentOdd r ε with hFdef
  refine ⟨F, continuous_edgeTentOdd r ε, hasCompactSupport_edgeTentOdd hε0 hεr, edgeTentOdd_odd r ε,
    edgeTentOdd_lipschitz r ε, fun x hx => edgeTentOdd_eq_zero_of_lt hε0 hεr hx, ?_, ?_⟩
  · intro n hn
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hn).2
    obtain ⟨hz, -⟩ := edgeTent_oddPart_eq hε0 hεr (L := Real.log n) (by linarith)
      (by rw [hεdef]; linarith)
    refine ⟨hz, ?_⟩
    -- the sharp micro-fold of the thin strip of `n`
    have hl2 := Real.log_two_gt_d9
    set L := Real.log n with hLdef
    set p := L - r with hpdef
    have hp : 1 / 2 ≤ p := by rw [hpdef]; linarith
    have hpr : p < r := by rw [hpdef]; linarith
    have hL : p + r = L := by rw [hpdef]; ring
    have hms := sharpMicroFold_strip_ge (continuous_edgeTentOdd r ε) (edgeTentOdd_lipschitz r ε)
      (by linarith) hpr hL (by rw [hpdef]; linarith) (by rw [hpdef]; linarith)
    have hlam : 2 * vonMangoldtAtom n ≤ 19 / 10 - (r - p) / 2 / p - 3 * ((r - p) / 2) ^ 2 := by
      have hη0 : 0 ≤ (r - p) / 2 := by linarith
      have hη : (r - p) / 2 ≤ 1 / 12 := by rw [hpdef]; linarith
      have hηp : (r - p) / 2 / p ≤ 1 / 6 := by rw [div_le_iff₀ (by linarith)]; linarith
      have hη2 : 3 * ((r - p) / 2) ^ 2 ≤ 1 / 48 := by nlinarith
      linarith [vonMangoldtAtom_le n]
    have hα0 : 0 ≤ ∫ a in p..r, reflectedOddPart F L a ^ 2 :=
      intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
    have := mul_le_mul_of_nonneg_right hlam hα0
    unfold stripBoxEnergy stripIntegrand
    linarith
  · -- every odd part carries `ε³/64`, the box carries at most `3ε²r`
    have hbox := stripBoxEnergy_edgeTent_le hε0 (by rw [hεdef]; norm_num) hεr
    rw [← hFdef] at hbox
    have hterm : ∀ n ∈ thinBand r, 2 * vonMangoldtAtom n * (ε ^ 3 / 64) ≤
        2 * vonMangoldtAtom n * ∫ a in (Real.log n - r)..r, reflectedOddPart F (Real.log n) a ^ 2 :=
      fun n hn => by
        obtain ⟨h1, h2⟩ := (Finset.mem_filter.mp hn).2
        obtain ⟨-, hodd⟩ := edgeTent_oddPart_eq hε0 hεr (L := Real.log n) (by linarith)
          (by rw [hεdef]; linarith)
        have hmass' := edgeTent_sq_integral_ge hε0 hεr (L := Real.log n) (by rw [hεdef]; linarith)
        refine mul_le_mul_of_nonneg_left ?_ (by linarith [vonMangoldtAtom_nonneg n])
        linarith
    have hsum := Finset.sum_le_sum hterm
    rw [← Finset.sum_mul, ← Finset.mul_sum] at hsum
    have hpos : 0 < ε ^ 3 / 64 := by positivity
    have : 3 * ε ^ 2 * r < 2 * (∑ n ∈ thinBand r, vonMangoldtAtom n) * (ε ^ 3 / 64) := by
      rw [hεdef]; nlinarith
    linarith

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
