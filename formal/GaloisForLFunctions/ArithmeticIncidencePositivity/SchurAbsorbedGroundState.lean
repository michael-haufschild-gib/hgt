import GaloisForLFunctions.ArithmeticIncidencePositivity.SharpMicroFoldHarnack

/-!
# The ground-state remainder carries potential: a Schur step for the folded surplus

The ground-state transform of the folded surplus (`surplusEnergy_ge_potential`) splits every pair
energy exactly,

    k(F(x) − F(y))² = F(x)² k(1 − q) + F(y)² k(1 − 1/q) + k h(x)h(y)(f(x) − f(y))²,   q = h(y)/h(x),

`f = F/h`, and drops the remainder. On a rectangle of pairs `x ∈ Z`, `y ∈ H` the remainder can lend
potential from `H` to `Z`. The Schur step `A(c − t)² + Bt² ≥ c² AB/(A + B)` with `A = k/q`,
`B = β`, `c = a q`, `t = b` gives (`sq_sub_ge_groundState_schur`)

    k(a − b)² ≥ a² (k(1 − q) + kβq²/(k + βq)) + b² (k(1 − 1/q) − β):

the point `x` gains `kβq²/(k + βq)` per pair and the hub point `y` pays `β`. Integrated over the
rectangle (`surplusEnergy_ge_potential_add_schur`),

    S_P(F) ≥ ∫ F² U_h + s₀ |H| ∫_Z F² − β |Z| ∫_H F²,   s₀ ≤ kβq²/(k + βq) on Z × H.

The potential is redistributed: a deficit on `Z` is paid as long as `H` can afford `β|Z|` per unit of
mass. In the first prime window the hub is the outer part of the edge strip, where the plateau
potential is logarithmically large, and `Z` its inner edge, where the strip pairs of the
micro-fold are missing (`SharpFoldOddWindowPastSevenTwentieths`).
-/

open MeasureTheory Set Filter Topology intervalIntegral
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-- The Schur inequality of two terms: `c² AB/(A + B) ≤ A(c − t)² + B t²`. -/
theorem schur_two_terms {A B c t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : 0 < A + B) :
    c ^ 2 * (A * B / (A + B)) ≤ A * (c - t) ^ 2 + B * t ^ 2 := by
  rw [mul_div_assoc', div_le_iff₀ hAB]
  nlinarith [sq_nonneg (A * (c - t) - B * t)]

/-- **The Schur step of a pair.** For `p, q > 0`, `k, β ≥ 0`, `k + β q/p > 0`:
`k(a − b)² ≥ a²(k(1 − q/p) + kβ(q/p)²/(k + β q/p)) + b²(k(1 − p/q) − β)`. -/
theorem sq_sub_ge_groundState_schur (a b : ℝ) {p q k β : ℝ} (hp : 0 < p) (hq : 0 < q) (hk : 0 ≤ k)
    (hβ : 0 ≤ β) (hkβ : 0 < k + β * (q / p)) :
    a ^ 2 * (k * (1 - q / p) + k * β * (q / p) ^ 2 / (k + β * (q / p))) +
        b ^ 2 * (k * (1 - p / q) - β) ≤ k * (a - b) ^ 2 := by
  set t := q / p with ht
  have ht0 : 0 < t := div_pos hq hp
  have hpq : p / q = 1 / t := by rw [ht]; field_simp
  rw [hpq]
  -- the exact split, and Schur on the remainder `(k/t)(a t − b)² + β b²`
  have key : k * (a - b) ^ 2 - (a ^ 2 * (k * (1 - t)) + b ^ 2 * (k * (1 - 1 / t))) =
      k / t * (a * t - b) ^ 2 := by
    field_simp; ring
  have hA : 0 ≤ k / t := div_nonneg hk ht0.le
  have hden : 0 < k / t + β := by
    have : k / t + β = (k + β * t) / t := by field_simp
    rw [this]; exact div_pos hkβ ht0
  have schur := schur_two_terms (c := a * t) (t := b) hA hβ hden
  have e : a ^ 2 * (k * β * t ^ 2 / (k + β * t)) = (a * t) ^ 2 * (k / t * β / (k / t + β)) := by
    field_simp
  nlinarith [key, schur, e]

section Schur

variable {P F : ℝ → ℝ} {B K : ℝ} (hPc : Continuous P) (hFc : Continuous F)
  (hPe : ∀ x, P (-x) = P x) (hFo : ∀ x, F (-x) = -F x) (hP0 : ∀ x, 0 ≤ P x)
  (hP1 : ∀ x, P x ≤ 1) (hPB : ∀ x, B ≤ |x| → P x = 0) (hFB : ∀ x, B ≤ |x| → F x = 0)
  (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hB0 : 0 < B) (hB1 : 2 * B ≤ 1)

include hPc hFc hFo hP0 hP1 hPB hFL hB0 hB1 in
/-- **The ground-state transform with a Schur rectangle.** For a gauge `h ≥ a₀ > 0` on `[0, r]`,
`L`-Lipschitz there, intervals `Z = [z₁, z₂]` below `H = [y₁, y₂] ⊆ (0, r]`, `β > 0`, and
`s₀ ≤ kβq²/(k + βq)` on `Z × H` (`k` the surplus kernel, `q = h(y)/h(x)`):
`S_P(F) ≥ ∫_{x>0} F² U_h + s₀ |H| ∫_Z F² − β |Z| ∫_H F²`. -/
theorem surplusEnergy_ge_potential_add_schur {h : ℝ → ℝ} {r a₀ L z₁ z₂ y₁ y₂ β s₀ : ℝ}
    (hrB : r ≤ B) (hPr : ∀ x, |x| ≤ r → P x = 1) (hFr : ∀ x, F x ≠ 0 → |x| ≤ r)
    (hh : Continuous h) (ha₀ : 0 < a₀) (hhpos : ∀ x, 0 ≤ x → x ≤ r → a₀ ≤ h x)
    (hhL : ∀ x y, 0 ≤ x → x ≤ r → 0 ≤ y → y ≤ r → |h x - h y| ≤ L * |x - y|)
    (hz₁ : 0 < z₁) (hz : z₁ ≤ z₂) (hzy : z₂ < y₁) (hy : y₁ ≤ y₂) (hyr : y₂ ≤ r) (hβ : 0 < β)
    (hS : ∀ x ∈ Icc z₁ z₂, ∀ y ∈ Icc y₁ y₂,
      s₀ ≤ surplusKernel x y * β * (h y / h x) ^ 2 / (surplusKernel x y + β * (h y / h x))) :
    (∫ x in Ioi (0 : ℝ), F x ^ 2 * surplusPotential h r x) +
      (s₀ * (y₂ - y₁) * (∫ x in Icc z₁ z₂, F x ^ 2) - β * (z₂ - z₁) * ∫ y in Icc y₁ y₂, F y ^ 2) ≤
        surplusEnergy P F := by
  have hr1 : r ≤ 1 := by linarith
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
  -- the bounded transformed weight of a pair inside the window
  have hw : ∀ x y, 0 < x → x ≤ r → 0 < y → y ≤ r →
      |surplusKernel x y * (1 - h y / h x)| ≤ 3 / 2 * |L| / a₀ := fun x y hx hxr hy hyr =>
    abs_surplusKernel_mul_le hx hy (by rw [abs_le]; constructor <;> linarith) ha₀
      (hhpos x hx.le hxr) (hhL x y hx.le hxr hy.le hyr)
  have hwF : ∀ x y z, 0 < x → x ≤ r → 0 < y → y ≤ r → 0 ≤ z → z ≤ r →
      |F z ^ 2 * (surplusKernel x y * (1 - h y / h x))| ≤ K ^ 2 * r ^ 2 * (3 / 2 * |L| / a₀) :=
    fun x y z hx hxr hy hyr hz hzr => by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (hF2 z hz hzr) (hw x y hx hxr hy hyr) (abs_nonneg _) (by positivity)
  -- the three pair densities
  set gA : ℝ × ℝ → ℝ := fun p => if p.2 + p.1 ≤ r then
    F p.2 ^ 2 * (surplusKernel p.2 (p.2 + p.1) * (1 - h (p.2 + p.1) / h p.2)) else 0 with hgA
  set gB : ℝ × ℝ → ℝ := fun p => if p.2 + p.1 ≤ r then
    F (p.2 + p.1) ^ 2 * (surplusKernel (p.2 + p.1) p.2 * (1 - h p.2 / h (p.2 + p.1))) else 0
    with hgB
  set G : ℝ × ℝ → ℝ := fun p => if p.1 < p.2 ∧ p.2 ≤ r then
    F p.2 ^ 2 * (surplusKernel p.2 p.1 * (1 - h p.1 / h p.2)) else 0 with hG
  have hmA : Measurable gA := by
    refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) ?_ measurable_const
    exact ((hFc.measurable.comp measurable_snd).pow_const 2).mul
      ((hmk.comp (measurable_snd.prodMk (measurable_snd.add measurable_fst))).mul
        (measurable_const.sub ((hh.measurable.comp (measurable_snd.add measurable_fst)).div
          (hh.measurable.comp measurable_snd))))
  have hmB : Measurable gB := by
    refine Measurable.ite (measurableSet_le (by fun_prop) measurable_const) ?_ measurable_const
    exact ((hFc.measurable.comp (measurable_snd.add measurable_fst)).pow_const 2).mul
      ((hmk.comp ((measurable_snd.add measurable_fst).prodMk measurable_snd)).mul
        (measurable_const.sub ((hh.measurable.comp measurable_snd).div
          (hh.measurable.comp (measurable_snd.add measurable_fst)))))
  have hmG : Measurable G := by
    refine Measurable.ite ((measurableSet_lt measurable_fst measurable_snd).inter
      (measurableSet_le measurable_snd measurable_const)) ?_ measurable_const
    exact ((hFc.measurable.comp measurable_snd).pow_const 2).mul
      ((hmk.comp (measurable_snd.prodMk measurable_fst)).mul
        (measurable_const.sub ((hh.measurable.comp measurable_fst).div
          (hh.measurable.comp measurable_snd))))
  have hIA : Integrable gA ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine integrable_quadrant_of_bound hmA (C := K ^ 2 * r ^ 2 * (3 / 2 * |L| / a₀)) (T₁ := r) (T₂ := r) (fun s x hs hx => ?_)
      (fun s x hs hx hout => ?_)
    · simp only [hgA]
      split_ifs with hxs
      · exact hwF x (x + s) x hx (by linarith) (by linarith) hxs hx.le (by linarith)
      · rw [abs_zero]; positivity
    · simp only [hgA]
      rw [if_neg (by rcases hout with h1 | h1 <;> linarith)]
  have hIB : Integrable gB ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine integrable_quadrant_of_bound hmB (C := K ^ 2 * r ^ 2 * (3 / 2 * |L| / a₀)) (T₁ := r) (T₂ := r) (fun s x hs hx => ?_)
      (fun s x hs hx hout => ?_)
    · simp only [hgB]
      split_ifs with hxs
      · exact hwF (x + s) x (x + s) (by linarith) hxs hx (by linarith) (by linarith) hxs
      · rw [abs_zero]; positivity
    · simp only [hgB]
      rw [if_neg (by rcases hout with h1 | h1 <;> linarith)]
  have hIG : Integrable G ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine integrable_quadrant_of_bound hmG (C := K ^ 2 * r ^ 2 * (3 / 2 * |L| / a₀)) (T₁ := r) (T₂ := r) (fun x y hx hy => ?_)
      (fun x y hx hy hout => ?_)
    · simp only [hG]
      split_ifs with hxy
      · exact hwF y x y hy hxy.2 hx (by linarith [hxy.1, hxy.2]) hy.le hxy.2
      · rw [abs_zero]; positivity
    · simp only [hG]
      rw [if_neg (by rintro ⟨h1, h2⟩; rcases hout with h3 | h3 <;> linarith)]
  -- the Schur density of the rectangle: the lower point gains, the upper point pays
  set gC : ℝ × ℝ → ℝ := fun z => if z.2 ∈ Icc z₁ z₂ ∧ z.2 + z.1 ∈ Icc y₁ y₂ then
    s₀ * F z.2 ^ 2 - β * F (z.2 + z.1) ^ 2 else 0 with hgC
  have hmC : Measurable gC := by
    refine Measurable.ite ?_ ?_ measurable_const
    · have h1 : MeasurableSet {z : ℝ × ℝ | z.2 ∈ Icc z₁ z₂} := measurable_snd measurableSet_Icc
      have h2 : MeasurableSet {z : ℝ × ℝ | z.2 + z.1 ∈ Icc y₁ y₂} :=
        (measurable_snd.add measurable_fst) measurableSet_Icc
      exact h1.inter h2
    · exact (measurable_const.mul ((hFc.measurable.comp measurable_snd).pow_const 2)).sub
        (measurable_const.mul ((hFc.measurable.comp (measurable_snd.add measurable_fst)).pow_const 2))
  have hIC : Integrable gC ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine integrable_quadrant_of_bound hmC (C := |s₀| * (K ^ 2 * r ^ 2) + β * (K ^ 2 * r ^ 2))
      (T₁ := r) (T₂ := r) (fun s x hs hx => ?_) (fun s x hs hx hout => ?_)
    · simp only [hgC]
      split_ifs with hxs
      · have hxr : x ≤ r := by linarith [hxs.1.2]
        have h1 := hF2 x hx.le hxr
        have h2 := hF2 (x + s) (by linarith) (by linarith [hxs.2.2])
        calc |s₀ * F x ^ 2 - β * F (x + s) ^ 2| ≤ |s₀ * F x ^ 2| + |β * F (x + s) ^ 2| :=
              abs_sub _ _
          _ = |s₀| * F x ^ 2 + β * F (x + s) ^ 2 := by
              rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (F x)),
                abs_of_nonneg (sq_nonneg (F (x + s))), abs_of_pos hβ]
          _ ≤ |s₀| * (K ^ 2 * r ^ 2) + β * (K ^ 2 * r ^ 2) := by
              have := mul_le_mul_of_nonneg_left h1 (abs_nonneg s₀)
              have := mul_le_mul_of_nonneg_left h2 hβ.le
              linarith
      · rw [abs_zero]; positivity
    · simp only [hgC]
      rw [if_neg (by rintro ⟨h1, h2⟩; rcases hout with h3 | h3 <;> linarith [h1.2, h2.2])]
  -- the surplus density dominates the two transformed densities
  have hIS := integrable_archLevy_mul_signedShiftJump_prod hPc hFc hP0 hP1 hPB hFL hB0 hB1
  set fS : ℝ × ℝ → ℝ := fun p =>
    (archLevyDensity p.1 - archLevyDensity (p.1 + 2 * p.2)) * signedShiftJump P F p.1 p.2 with hfS
  have hmS : Measurable fS := by
    have hc : Continuous fun p : ℝ × ℝ => signedShiftJump P F p.1 p.2 := by
      unfold signedShiftJump; fun_prop
    exact ((measurable_archLevyDensity.comp measurable_fst).sub
      (measurable_archLevyDensity.comp (by fun_prop))).mul hc.measurable
  have hIfS : Integrable fS ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine hIS.mono' hmS.aestronglyMeasurable (ae_quadrant fun s x hs hx => ?_)
    have hJ := signedShiftJump_nonneg' hP0 (F := F) s x
    have hω := strictAntiOn_archLevyDensity.antitoneOn hs (show (0 : ℝ) < s + 2 * x by linarith)
      (by linarith)
    have hω2 := (archLevyDensity_pos (show (0 : ℝ) < s + 2 * x by linarith)).le
    simp only [hfS, Function.uncurry_apply_pair, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg (by linarith) hJ)]
    exact mul_le_mul_of_nonneg_right (by linarith) hJ
  have hpt : ∀ s x, 0 < s → 0 < x → gA (s, x) + gB (s, x) + gC (s, x) ≤ fS (s, x) := by
    intro s x hs hx
    have hJ := signedShiftJump_nonneg' hP0 (F := F) s x
    have hk := surplusKernel_nonneg hx (show 0 < x + s by linarith) (by linarith : x ≠ x + s)
    by_cases hR : x ∈ Icc z₁ z₂ ∧ x + s ∈ Icc y₁ y₂
    · -- the Schur rectangle
      have hxs : x + s ≤ r := le_trans hR.2.2 hyr
      have hP1' : P x = 1 := hPr x (by rw [abs_of_pos hx]; linarith)
      have hP2' : P (x + s) = 1 := hPr (x + s) (by rw [abs_of_pos (by linarith)]; exact hxs)
      have hpx := lt_of_lt_of_le ha₀ (hhpos x hx.le (by linarith))
      have hpy := lt_of_lt_of_le ha₀ (hhpos (x + s) (by linarith) hxs)
      have hq : 0 < h (x + s) / h x := div_pos hpy hpx
      have hkβ : 0 < surplusKernel x (x + s) + β * (h (x + s) / h x) := by positivity
      have hsch := sq_sub_ge_groundState_schur (F x) (F (x + s)) hpx hpy hk hβ.le hkβ
      have hS' := hS x hR.1 (x + s) hR.2
      have hF0 := sq_nonneg (F x)
      simp only [hgA, hgB, hgC, hfS, if_pos hxs, if_pos hR]
      rw [← surplusKernel_add x s hs, surplusKernel_comm (x + s) x]
      unfold signedShiftJump
      rw [hP1', hP2']
      nlinarith [mul_le_mul_of_nonneg_left hS' hF0]
    have hC0 : gC (s, x) = 0 := by simp only [hgC]; rw [if_neg hR]
    rw [hC0, add_zero]
    simp only [hgA, hgB, hfS]
    rw [← surplusKernel_add x s hs]
    split_ifs with hxs
    · have hP1' : P x = 1 := hPr x (by rw [abs_of_pos hx]; linarith)
      have hP2' : P (x + s) = 1 := hPr (x + s) (by rw [abs_of_pos (by linarith)]; exact hxs)
      have hgs := sq_sub_ge_groundState (F x) (F (x + s)) (lt_of_lt_of_le ha₀ (hhpos x hx.le
        (by linarith))) (lt_of_lt_of_le ha₀ (hhpos (x + s) (by linarith) hxs))
      unfold signedShiftJump
      rw [hP1', hP2', surplusKernel_comm (x + s) x]
      nlinarith [mul_le_mul_of_nonneg_left hgs hk]
    · rw [add_zero]; exact mul_nonneg hk hJ
  -- the iterated comparison
  have hcmp : (∫ x in Ioi (0 : ℝ), ((∫ s in Ioi (0 : ℝ), gA (s, x)) +
      (∫ s in Ioi (0 : ℝ), gB (s, x)) + ∫ s in Ioi (0 : ℝ), gC (s, x))) ≤ surplusEnergy P F := by
    have hO : Integrable (fun x => (∫ s in Ioi (0 : ℝ), gA (s, x)) + (∫ s in Ioi (0 : ℝ), gB (s, x)) +
        ∫ s in Ioi (0 : ℝ), gC (s, x)) (volume.restrict (Ioi 0)) :=
      (hIA.integral_prod_right.add hIB.integral_prod_right).add hIC.integral_prod_right
    refine integral_mono_ae hO hIfS.integral_prod_right ?_
    filter_upwards [hIA.prod_left_ae, hIB.prod_left_ae, hIC.prod_left_ae, hIfS.prod_left_ae,
      ae_restrict_mem measurableSet_Ioi] with x hxA hxB hxC hxS hx0
    have hx : 0 < x := hx0
    have hAB : Integrable (fun s => gA (s, x) + gB (s, x)) (volume.restrict (Ioi 0)) := hxA.add hxB
    have hABC : Integrable (fun s => gA (s, x) + gB (s, x) + gC (s, x)) (volume.restrict (Ioi 0)) :=
      hAB.add hxC
    rw [← integral_add hxA hxB, ← integral_add hAB hxC]
    refine integral_mono_ae hABC hxS ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hpt s x hs hx
  -- the same-side half
  have hA : ∀ x, 0 < x → (∫ s in Ioi (0 : ℝ), gA (s, x)) =
      F x ^ 2 * ∫ y in Ioc x r, surplusKernel x y * (1 - h y / h x) := by
    intro x hx
    have e := setIntegral_Ioi_translate (fun y => gA (y - x, x)) x
    simp only [add_sub_cancel_right] at e
    rw [← e, ← MeasureTheory.integral_const_mul, ← Ioi_inter_Iic, ← setIntegral_indicator measurableSet_Iic]
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [hgA, Set.indicator_apply, mem_Iic, add_sub_cancel]
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
      by_cases hyr : y ≤ r
      · rw [if_pos hyr, if_pos ⟨hxy, hyr⟩]
      · rw [if_neg hyr, if_neg (fun h => hyr h.2)]
    · rw [if_neg hxy]
      by_cases hy : 0 < y
      · rw [if_pos hy, if_neg (fun h => hxy h.1)]
      · rw [if_neg hy]
  have hBt : ∀ y, 0 < y → (∫ x in Ioi (0 : ℝ), G (x, y)) = if y ≤ r then
      F y ^ 2 * ∫ x in Ioo 0 y, surplusKernel y x * (1 - h x / h y) else 0 := by
    intro y hy
    split_ifs with hyr
    · rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_indicator measurableSet_Ioo,
        ← MeasureTheory.integral_indicator measurableSet_Ioi]
      congr 1
      funext x
      simp only [hG, Set.indicator_apply, mem_Ioi, mem_Ioo]
      by_cases hx : 0 < x
      · by_cases hxy : x < y
        · rw [if_pos hx, if_pos ⟨hxy, hyr⟩, if_pos ⟨hx, hxy⟩]
        · rw [if_pos hx, if_neg (fun h => hxy h.1), if_neg (fun h => hxy h.2)]
      · rw [if_neg hx, if_neg (fun h => hx h.1)]
    · refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
      simp only [hG, Pi.zero_apply]
      rw [if_neg (fun h => hyr h.2)]
  -- the potential is the sum of the two halves
  have hsum : ∀ x, 0 < x → F x ^ 2 * surplusPotential h r x =
      (∫ s in Ioi (0 : ℝ), gA (s, x)) + ∫ x' in Ioi (0 : ℝ), G (x', x) := by
    intro x hx
    rw [hA x hx, hBt x hx]
    by_cases hxr : x ≤ r
    · rw [if_pos hxr]
      have hint : IntegrableOn (fun y => surplusKernel x y * (1 - h y / h x)) (Ioc 0 r) := by
        refine Measure.integrableOn_of_bounded (M := 3 / 2 * |L| / a₀) (by simp)
          ((hmk.comp (measurable_const.prodMk measurable_id)).mul (measurable_const.sub
            ((hh.measurable).div measurable_const))).aestronglyMeasurable ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        rw [Real.norm_eq_abs]
        exact hw x y hx hxr hy.1 hy.2
      unfold surplusPotential
      rw [← Ioc_union_Ioc_eq_Ioc hx.le hxr, setIntegral_union (Set.disjoint_left.mpr fun y h1 h2 =>
        by linarith [h1.2, h2.1]) measurableSet_Ioc (hint.mono_set (Ioc_subset_Ioc_right hxr))
        (hint.mono_set (Ioc_subset_Ioc_left hx.le)), integral_Ioc_eq_integral_Ioo (x := 0)]
      have e : (∫ y in Ioo 0 x, surplusKernel x y * (1 - h y / h x)) =
          ∫ x' in Ioo 0 x, surplusKernel x x' * (1 - h x' / h x) := rfl
      rw [mul_add]
      ring
    · rw [if_neg hxr, hFz x (by rw [abs_of_pos hx]; exact not_le.mp hxr)]
      ring
  have hIsum : IntegrableOn (fun x => F x ^ 2 * surplusPotential h r x) (Ioi 0) := by
    have h1 : Integrable (fun x => (∫ s in Ioi (0 : ℝ), gA (s, x)) + ∫ x' in Ioi (0 : ℝ), G (x', x))
        (volume.restrict (Ioi 0)) := hIA.integral_prod_right.add hIG.integral_prod_right
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hsum x hx).symm
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
  -- the Schur part of the shift integral, for each lower point
  have hCx : ∀ x, 0 < x → (∫ s in Ioi (0 : ℝ), gC (s, x)) =
      (Icc z₁ z₂).indicator (fun x => s₀ * (y₂ - y₁) * F x ^ 2 - β * ∫ y in Icc y₁ y₂, F y ^ 2) x := by
    intro x hx
    by_cases hxZ : x ∈ Icc z₁ z₂
    · rw [Set.indicator_of_mem hxZ]
      have hsub : Icc (y₁ - x) (y₂ - x) ⊆ Ioi 0 := fun s hs => mem_Ioi.mpr (by linarith [hs.1, hxZ.2])
      have e1 : (∫ s in Ioi (0 : ℝ), gC (s, x)) =
          ∫ s in Ioi (0 : ℝ), (Icc (y₁ - x) (y₂ - x)).indicator
            (fun s => s₀ * F x ^ 2 - β * F (x + s) ^ 2) s := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        simp only [hgC, Set.indicator_apply, mem_Icc]
        by_cases hs : y₁ - x ≤ s ∧ s ≤ y₂ - x
        · rw [if_pos ⟨hxZ, ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩, if_pos hs, add_comm x s]
        · rw [if_neg (fun h => hs ⟨by linarith [h.2.1], by linarith [h.2.2]⟩), if_neg hs]
      have hcF : Continuous fun s => F (x + s) ^ 2 := by fun_prop
      rw [e1, setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.mpr hsub,
        MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : y₁ - x ≤ y₂ - x),
        intervalIntegral.integral_sub intervalIntegrable_const ((hcF.intervalIntegrable _ _).const_mul β),
        intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_add_left (fun y => F y ^ 2) x,
        show x + (y₁ - x) = y₁ by ring, show x + (y₂ - x) = y₂ by ring,
        intervalIntegral.integral_of_le hy, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      ring
    · rw [Set.indicator_of_notMem hxZ]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
      simp only [hgC, Pi.zero_apply]
      rw [if_neg (fun h => hxZ h.1)]
  have hI4 : Integrable (fun x => ∫ s in Ioi (0 : ℝ), gC (s, x)) (volume.restrict (Ioi 0)) :=
    hIC.integral_prod_right
  have hC : (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), gC (s, x)) =
      s₀ * (y₂ - y₁) * (∫ x in Icc z₁ z₂, F x ^ 2) - β * (z₂ - z₁) * ∫ y in Icc y₁ y₂, F y ^ 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioi hCx, setIntegral_indicator measurableSet_Icc,
      Set.inter_eq_right.mpr (fun x hx => mem_Ioi.mpr (lt_of_lt_of_le hz₁ hx.1))]
    have hcF2 : IntegrableOn (fun x => F x ^ 2) (Icc z₁ z₂) := (hFc.pow 2).integrableOn_Icc
    rw [MeasureTheory.integral_sub (hcF2.const_mul (s₀ * (y₂ - y₁))) (integrableOn_const (by simp)),
      MeasureTheory.integral_const_mul, setIntegral_const, Real.volume_real_Icc_of_le hz, smul_eq_mul]
    ring
  have hI12 : Integrable (fun x => (∫ s in Ioi (0 : ℝ), gA (s, x)) + ∫ s in Ioi (0 : ℝ), gB (s, x))
      (volume.restrict (Ioi 0)) := hI1.add hI2
  rw [setIntegral_congr_fun measurableSet_Ioi hsum, integral_add hI1 hI3, ← hswap, ← hC,
    ← integral_add hI1 hI2, ← integral_add hI12 hI4]
  exact hcmp



include hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 hB1 in
/-- **The first prime window with the strip shared and a Schur rectangle.** If the fraction `θ` of the
strip surplus pays the atom through the sharp micro-fold, the archimedean jump energy minus the prime
term dominates the killing plus the mixed potential `(1 − θ)(U_h + Schur) + θ U_h^{off}`, the Schur
part being `s₀ |H| ∫_Z F² − β |Z| ∫_H F²`. -/
theorem fourKilling_add_potentialMixSchur_le_archJump_sub_prime {h : ℝ → ℝ}
    {r a₀ L θ z₁ z₂ y₁ y₂ β s₀ : ℝ}
    (hFcs : HasCompactSupport F) (hr : Real.log 2 / 2 < r) (hr' : r ≤ Real.log 2 / 2 + 1 / 12)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hθ : 2 * (4902 / 10000) ≤ θ * (19 / 10 - (r - (Real.log 2 - r)) / 2 / (Real.log 2 - r) -
      3 * ((r - (Real.log 2 - r)) / 2) ^ 2))
    (hrB : r ≤ B) (hPr : ∀ x, |x| ≤ r → P x = 1) (hFr : ∀ x, F x ≠ 0 → |x| ≤ r)
    (hPcs : HasCompactSupport P) (hh : Continuous h) (ha₀ : 0 < a₀)
    (hhpos : ∀ x, 0 ≤ x → x ≤ r → a₀ ≤ h x)
    (hhL : ∀ x y, 0 ≤ x → x ≤ r → 0 ≤ y → y ≤ r → |h x - h y| ≤ L * |x - y|)
    (hz₁ : 0 < z₁) (hz : z₁ ≤ z₂) (hzy : z₂ < y₁) (hy : y₁ ≤ y₂) (hyr : y₂ ≤ r) (hβ : 0 < β)
    (hS : ∀ x ∈ Icc z₁ z₂, ∀ y ∈ Icc y₁ y₂,
      s₀ ≤ surplusKernel x y * β * (h y / h x) ^ 2 / (surplusKernel x y + β * (h y / h x))) :
    IntegrableOn (fun x => F x ^ 2 * ((1 - θ) * surplusPotential h r x +
        θ * surplusPotentialOff h (Real.log 2 - r) r x)) (Ioi 0) ∧
      4 * (∫ x in Ioi (0 : ℝ), F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) +
          2 * ((∫ x in Ioi (0 : ℝ), F x ^ 2 * ((1 - θ) * surplusPotential h r x +
            θ * surplusPotentialOff h (Real.log 2 - r) r x)) +
          (1 - θ) * (s₀ * (y₂ - y₁) * (∫ x in Icc z₁ z₂, F x ^ 2) -
            β * (z₂ - z₁) * ∫ y in Icc y₁ y₂, F y ^ 2)) ≤
        (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) -
          2 * (vonMangoldtAtom 2 * ∫ x, F x * F (x + Real.log 2)) := by
  have hl0 := Real.log_two_gt_d9
  have hl1 := Real.log_two_lt_d9
  have hr0 : 0 < r := by linarith
  obtain ⟨hIA, -⟩ := surplusEnergy_ge_potential hPc hFc hFo hP0 hP1 hPB hFL hB0 hB1 hrB hPr hFr
    hh ha₀ hhpos hhL
  have hA := surplusEnergy_ge_potential_add_schur hPc hFc hFo hP0 hP1 hPB hFL hB0 hB1 hrB hPr hFr
    hh ha₀ hhpos hhL hz₁ hz hzy hy hyr hβ hS
  obtain ⟨hIB, hBs⟩ := surplusEnergy_ge_potentialOff_add_strip hPc hFc hFo hP0 hP1 hPB hFL hB0 hB1
    (p := Real.log 2 - r) (by linarith) (by linarith) hrB hPr hFr hh ha₀ hhpos hhL
  have hfold := fourKilling_add_surplusEnergy_le_archJump hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0
    hB1 hr0 hrB hPr hFr hPcs
  have hsupp : ∀ x, r < |x| → F x = 0 := fun x hx => by
    by_contra h0; exact absurd (hFr x h0) (not_le.mpr hx)
  set p := Real.log 2 - r with hpdef
  have hpr : p < r := by rw [hpdef]; linarith
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hL : p + r = Real.log 2 := by rw [hpdef]; ring
  have hr3 : r - p ≤ 2 * p := by rw [hpdef]; linarith
  have hr6 : r - p ≤ 1 / 6 := by rw [hpdef]; linarith
  have hms := sharpMicroFold_strip_ge hFc hFL hp0 hpr hL hr3 hr6
  have hT : (∫ x in p..r, ∫ y in p..r, surplusKernel x y * (F x - F y) ^ 2) =
      2 * stripSurplus F p r := integral_strip_eq_two_mul_stripSurplus hFc hFL hp0 hpr.le (by linarith)
  have hshift := integral_mul_shift_le_reflectedOdd hFc hFcs hFo (r := r) (L := Real.log 2)
    (by linarith) (by rw [← hpdef]; exact hpr.le) hsupp
  rw [← hpdef] at hshift
  obtain ⟨hΛ0, hΛ1⟩ := vonMangoldtAtom_two_bounds
  have hα0 : 0 ≤ ∫ x in p..r, reflectedOddPart F (Real.log 2) x ^ 2 :=
    intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  have hdom : 2 * (vonMangoldtAtom 2 * ∫ x, F x * F (x + Real.log 2)) ≤ θ * (2 * stripSurplus F p r) := by
    have k1 := mul_le_mul_of_nonneg_left hshift hΛ0
    have k2 := mul_le_mul_of_nonneg_right hθ hα0
    have k3 := mul_le_mul_of_nonneg_right hΛ1 hα0
    have k4 := mul_le_mul_of_nonneg_left hms hθ0
    rw [hT] at k4
    nlinarith
  have h1 : IntegrableOn (fun x => (1 - θ) * (F x ^ 2 * surplusPotential h r x)) (Ioi 0) :=
    hIA.const_mul (1 - θ)
  have h2 : IntegrableOn (fun x => θ * (F x ^ 2 * surplusPotentialOff h p r x)) (Ioi 0) :=
    hIB.const_mul θ
  have h3 : IntegrableOn (fun x => (1 - θ) * (F x ^ 2 * surplusPotential h r x) +
      θ * (F x ^ 2 * surplusPotentialOff h p r x)) (Ioi 0) := h1.add h2
  have hmix : IntegrableOn (fun x => F x ^ 2 * ((1 - θ) * surplusPotential h r x +
      θ * surplusPotentialOff h p r x)) (Ioi 0) :=
    h3.congr_fun (fun x _ => by ring) measurableSet_Ioi
  refine ⟨hmix, ?_⟩
  have hsplit : (∫ x in Ioi (0 : ℝ), F x ^ 2 * ((1 - θ) * surplusPotential h r x +
      θ * surplusPotentialOff h p r x)) =
      (1 - θ) * (∫ x in Ioi (0 : ℝ), F x ^ 2 * surplusPotential h r x) +
        θ * ∫ x in Ioi (0 : ℝ), F x ^ 2 * surplusPotentialOff h p r x := by
    rw [← MeasureTheory.integral_const_mul, ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_add h1 h2]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => by ring
  rw [hsplit]
  have hθ1' : 0 ≤ 1 - θ := by linarith
  have k5 := mul_le_mul_of_nonneg_left hA hθ1'
  have k6 := mul_le_mul_of_nonneg_left hBs hθ0
  nlinarith

end Schur

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
