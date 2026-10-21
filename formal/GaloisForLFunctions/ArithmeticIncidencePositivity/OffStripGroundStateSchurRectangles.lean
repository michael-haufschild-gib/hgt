import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeAtomEvenPartPotential
import GaloisForLFunctions.ArithmeticIncidencePositivity.SchurAbsorbedGroundState

/-!
# Lending potential to the middle of the window: Schur rectangles in the off-strip transform

The ground-state transform off the strip `S = [p, r]` (`surplusEnergy_ge_potentialOff_add_strip`)
transforms every pair with its lower point below `p` and drops the remainders
`k h(x)h(y)(f(x) − f(y))²`, `f = F/h`. On a rectangle of such pairs the Schur step turns the remainder
into potential at one point, paid for at the other (`sq_sub_ge_schur_pair`):
`k(a − b)² ≥ a²k(1 − q/p) + b²k(1 − p/q) + s₀a² − βb²` whenever `s₀ ≤ kβ(q/p)²/(k + βq/p)`, `a` the
gaining point with gauge `p`, `b` the paying point with gauge `q`. Two rectangles are kept
(`surplusEnergy_ge_potentialOff_add_strip_add_schur`):

* **a hub below**, `H_A = [a₁, a₂]` below `Z_A = [b₁, b₂]`: the upper points gain `s_A |H_A|`, the hub
  pays `β_A |Z_A|`. It lends potential from the origin region, where the killing `log((x + r)/x)` is
  large, to the middle of the window.
* **a hub above**, `Z_B = [c₁, c₂]` below `p` and `H_B = [d₁, d₂] ⊆ (c₂, r]`: the lower points gain
  `s_B |H_B|`, the hub pays `β_B |Z_B|`. With `H_B` in the strip it lends the prime potential of the
  strip (`PrimeAtomEvenPartPotential`) to the middle.

The rectangles are disjoint as sets of pairs (`a₂ < c₁`), so each remainder is used once. With the
θ-split of the first prime window and the even part of the atom
(`fourKilling_add_potentialMixPrimeSchur_le_archJump_sub_prime`) they enter with the weight `θ` of the
off-strip transform.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### The Schur step of a pair and the rectangle densities -/

/-- **The Schur step of a pair, with a prescribed gain.** For `p, q > 0`, `k ≥ 0`, `β > 0` and
`s₀ ≤ kβ(q/p)²/(k + βq/p)`: `a²k(1 − q/p) + b²k(1 − p/q) + (s₀a² − βb²) ≤ k(a − b)²`. -/
theorem sq_sub_ge_schur_pair (a b : ℝ) {p q k β s₀ : ℝ} (hp : 0 < p) (hq : 0 < q) (hk : 0 ≤ k)
    (hβ : 0 < β) (hs : s₀ ≤ k * β * (q / p) ^ 2 / (k + β * (q / p))) :
    a ^ 2 * (k * (1 - q / p)) + b ^ 2 * (k * (1 - p / q)) + (s₀ * a ^ 2 - β * b ^ 2) ≤
      k * (a - b) ^ 2 := by
  have hkβ : 0 < k + β * (q / p) := by have := div_pos hq hp; positivity
  have h := sq_sub_ge_groundState_schur a b hp hq hk hkβ
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg a)]

/-- The pair density of a rectangle: pairs with lower point `z.2 ∈ [e₁, e₂]` and upper point
`z.2 + z.1 ∈ [f₁, f₂]` carry `u F(lower)² + v F(upper)²`. -/
def rectDensity (F : ℝ → ℝ) (e₁ e₂ f₁ f₂ u v : ℝ) (z : ℝ × ℝ) : ℝ :=
  if z.2 ∈ Icc e₁ e₂ ∧ z.2 + z.1 ∈ Icc f₁ f₂ then u * F z.2 ^ 2 + v * F (z.2 + z.1) ^ 2 else 0

theorem measurable_rectDensity {F : ℝ → ℝ} (hF : Continuous F) (e₁ e₂ f₁ f₂ u v : ℝ) :
    Measurable (rectDensity F e₁ e₂ f₁ f₂ u v) := by
  refine Measurable.ite ((measurable_snd measurableSet_Icc).inter
    ((measurable_snd.add measurable_fst) measurableSet_Icc)) ?_ measurable_const
  exact (measurable_const.mul ((hF.measurable.comp measurable_snd).pow_const 2)).add
    (measurable_const.mul ((hF.measurable.comp (measurable_snd.add measurable_fst)).pow_const 2))

/-- A rectangle density is integrable on the quadrant when `F²` is bounded on `[0, T] ⊇` the rectangle. -/
theorem integrable_rectDensity {F : ℝ → ℝ} (hF : Continuous F) {e₁ e₂ f₁ f₂ T M : ℝ} (he₁ : 0 ≤ e₁)
    (he : e₁ ≤ e₂) (hef : e₂ ≤ f₁) (hf : f₁ ≤ f₂) (hfT : f₂ ≤ T) (hM : ∀ y, 0 ≤ y → y ≤ T → F y ^ 2 ≤ M)
    (u v : ℝ) :
    Integrable (rectDensity F e₁ e₂ f₁ f₂ u v)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  refine integrable_quadrant_of_bound (measurable_rectDensity hF e₁ e₂ f₁ f₂ u v)
    (C := |u| * M + |v| * M) (T₁ := T) (T₂ := T) (fun s x hs hx => ?_) (fun s x hs hx hout => ?_)
  · unfold rectDensity
    split_ifs with hR
    · have h1 := hM x hx.le (by linarith [hR.1.2])
      have h2 := hM (x + s) (by linarith) (by linarith [hR.2.2])
      have hM0 : 0 ≤ M := (sq_nonneg _).trans h1
      calc |u * F x ^ 2 + v * F (x + s) ^ 2| ≤ |u * F x ^ 2| + |v * F (x + s) ^ 2| := abs_add_le _ _
        _ = |u| * F x ^ 2 + |v| * F (x + s) ^ 2 := by
            rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (F x)), abs_of_nonneg (sq_nonneg (F (x + s)))]
        _ ≤ |u| * M + |v| * M := add_le_add (mul_le_mul_of_nonneg_left h1 (abs_nonneg u))
            (mul_le_mul_of_nonneg_left h2 (abs_nonneg v))
    · have hM0 : 0 ≤ M := (sq_nonneg _).trans (hM f₁ (by linarith) (by linarith))
      rw [abs_zero]; positivity
  · unfold rectDensity
    rw [if_neg (by rintro ⟨h1, h2⟩; rcases hout with h3 | h3 <;> linarith [h1.1, h1.2, h2.2])]

/-- **The rectangle density integrates to the two masses.** For `0 < e₁ ≤ e₂ < f₁ ≤ f₂`:
`∫_{x>0} ∫_{s>0} rectDensity = u (f₂ − f₁) ∫_{[e₁,e₂]} F² + v (e₂ − e₁) ∫_{[f₁,f₂]} F²`. -/
theorem integral_rectDensity {F : ℝ → ℝ} (hF : Continuous F) {e₁ e₂ f₁ f₂ : ℝ} (he₁ : 0 < e₁)
    (he : e₁ ≤ e₂) (hef : e₂ < f₁) (hf : f₁ ≤ f₂) (u v : ℝ) :
    (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), rectDensity F e₁ e₂ f₁ f₂ u v (s, x)) =
      u * (f₂ - f₁) * (∫ x in Icc e₁ e₂, F x ^ 2) + v * (e₂ - e₁) * ∫ y in Icc f₁ f₂, F y ^ 2 := by
  -- for each lower point `x ∈ [e₁, e₂]` the upper points sweep `[f₁, f₂]`
  have hx : ∀ x, 0 < x → (∫ s in Ioi (0 : ℝ), rectDensity F e₁ e₂ f₁ f₂ u v (s, x)) =
      (Icc e₁ e₂).indicator (fun x => u * (f₂ - f₁) * F x ^ 2 + v * ∫ y in Icc f₁ f₂, F y ^ 2) x := by
    intro x hx
    by_cases hxe : x ∈ Icc e₁ e₂
    · rw [Set.indicator_of_mem hxe]
      have hsub : Icc (f₁ - x) (f₂ - x) ⊆ Ioi 0 := fun s hs => mem_Ioi.mpr (by linarith [hs.1, hxe.2])
      have e1 : (∫ s in Ioi (0 : ℝ), rectDensity F e₁ e₂ f₁ f₂ u v (s, x)) =
          ∫ s in Ioi (0 : ℝ), (Icc (f₁ - x) (f₂ - x)).indicator
            (fun s => u * F x ^ 2 + v * F (x + s) ^ 2) s := by
        refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
        simp only [rectDensity, Set.indicator_apply, mem_Icc]
        by_cases hs : f₁ - x ≤ s ∧ s ≤ f₂ - x
        · rw [if_pos ⟨hxe, ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩, if_pos hs, add_comm x s]
        · rw [if_neg (fun h => hs ⟨by linarith [h.2.1], by linarith [h.2.2]⟩), if_neg hs]
      have hcF : Continuous fun s => F (x + s) ^ 2 := by fun_prop
      rw [e1, setIntegral_indicator measurableSet_Icc, Set.inter_eq_right.mpr hsub,
        MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : f₁ - x ≤ f₂ - x),
        intervalIntegral.integral_add intervalIntegrable_const ((hcF.intervalIntegrable _ _).const_mul v),
        intervalIntegral.integral_const, smul_eq_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_add_left (fun y => F y ^ 2) x,
        show x + (f₁ - x) = f₁ by ring, show x + (f₂ - x) = f₂ by ring,
        intervalIntegral.integral_of_le hf, ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      ring
    · rw [Set.indicator_of_notMem hxe]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun s => ?_)
      simp only [rectDensity, Pi.zero_apply]
      rw [if_neg (fun h => hxe h.1)]
  rw [setIntegral_congr_fun measurableSet_Ioi hx, setIntegral_indicator measurableSet_Icc,
    Set.inter_eq_right.mpr (fun x hx => mem_Ioi.mpr (lt_of_lt_of_le he₁ hx.1))]
  have hcF2 : IntegrableOn (fun x => F x ^ 2) (Icc e₁ e₂) := (hF.pow 2).integrableOn_Icc
  rw [MeasureTheory.integral_add (hcF2.const_mul (u * (f₂ - f₁))) (integrableOn_const (by simp)),
    MeasureTheory.integral_const_mul, setIntegral_const, Real.volume_real_Icc_of_le he, smul_eq_mul]
  ring

/-- **The pair densities of the off-strip transform with two Schur rectangles.** At every pair
`(x, x + s)` the transformed same-side, reflected and strip densities plus the two rectangle densities
stay below the surplus density. -/
theorem offStrip_schur_pointwise {P F h : ℝ → ℝ} {p r a₀ a₁ a₂ b₁ b₂ βA sA c₁ c₂ d₁ d₂ βB sB : ℝ}
    (hP0 : ∀ x, 0 ≤ P x) (hPr : ∀ x, |x| ≤ r → P x = 1) (ha₀ : 0 < a₀)
    (hhpos : ∀ x, 0 ≤ x → x ≤ r → a₀ ≤ h x) (hbr : b₂ ≤ r) (hβA : 0 < βA)
    (hSA : ∀ x ∈ Icc b₁ b₂, ∀ y ∈ Icc a₁ a₂,
      sA ≤ surplusKernel x y * βA * (h y / h x) ^ 2 / (surplusKernel x y + βA * (h y / h x)))
    (hac : a₂ < c₁) (hc : c₁ ≤ c₂) (hcp : c₂ < p) (hdr : d₂ ≤ r) (hβB : 0 < βB)
    (hSB : ∀ x ∈ Icc c₁ c₂, ∀ y ∈ Icc d₁ d₂,
      sB ≤ surplusKernel x y * βB * (h y / h x) ^ 2 / (surplusKernel x y + βB * (h y / h x)))
    {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    (if x + s ≤ r ∧ x < p then
        F x ^ 2 * (surplusKernel x (x + s) * (1 - h (x + s) / h x)) else 0) +
      (if x + s ≤ r ∧ x < p then
        F (x + s) ^ 2 * (surplusKernel (x + s) x * (1 - h x / h (x + s))) else 0) +
      (if x + s ≤ r ∧ p ≤ x then stripIntegrand F x (x + s) else 0) +
      rectDensity F a₁ a₂ b₁ b₂ (-βA) sA (s, x) + rectDensity F c₁ c₂ d₁ d₂ sB (-βB) (s, x) ≤
      (archLevyDensity s - archLevyDensity (s + 2 * x)) * signedShiftJump P F s x := by
  have hJ := signedShiftJump_nonneg' hP0 (F := F) s x
  have hk := surplusKernel_nonneg hx (show 0 < x + s by linarith) (by linarith : x ≠ x + s)
  have hcomm : surplusKernel (x + s) x = surplusKernel x (x + s) := surplusKernel_comm _ _
  rw [← surplusKernel_add x s hs, hcomm]
  unfold rectDensity
  by_cases hxs : x + s ≤ r
  · have hP1' : P x = 1 := hPr x (by rw [abs_of_pos hx]; linarith)
    have hP2' : P (x + s) = 1 := hPr (x + s) (by rw [abs_of_pos (by linarith)]; exact hxs)
    unfold signedShiftJump
    rw [hP1', hP2', one_mul, one_mul]
    by_cases hxp : x < p
    · have hpx := lt_of_lt_of_le ha₀ (hhpos x hx.le (by linarith))
      have hpy := lt_of_lt_of_le ha₀ (hhpos (x + s) (by linarith) hxs)
      rw [if_pos ⟨hxs, hxp⟩, if_pos ⟨hxs, hxp⟩, if_neg (fun h' => absurd h'.2 (not_le.mpr hxp)),
        add_zero]
      by_cases hRA : x ∈ Icc a₁ a₂ ∧ x + s ∈ Icc b₁ b₂
      · -- hub below: the upper point gains, the lower point pays
        have hS' := hSA (x + s) hRA.2 x hRA.1
        rw [hcomm] at hS'
        have hsch := sq_sub_ge_schur_pair (F (x + s)) (F x) hpy hpx hk hβA hS'
        rw [if_pos hRA, if_neg (fun h' => by linarith [h'.1.1, hRA.1.2])]
        linarith only [hsch]
      by_cases hRB : x ∈ Icc c₁ c₂ ∧ x + s ∈ Icc d₁ d₂
      · -- hub above: the lower point gains, the upper point pays
        have hS' := hSB x hRB.1 (x + s) hRB.2
        have hsch := sq_sub_ge_schur_pair (F x) (F (x + s)) hpx hpy hk hβB hS'
        rw [if_neg hRA, if_pos hRB]
        linarith only [hsch]
      rw [if_neg hRA, if_neg hRB, add_zero, add_zero]
      have hgs := sq_sub_ge_groundState (F x) (F (x + s)) hpx hpy
      nlinarith [mul_le_mul_of_nonneg_left hgs hk]
    · have hRA : ¬(x ∈ Icc a₁ a₂ ∧ x + s ∈ Icc b₁ b₂) := fun h' => hxp (by linarith [h'.1.2])
      have hRB : ¬(x ∈ Icc c₁ c₂ ∧ x + s ∈ Icc d₁ d₂) := fun h' => hxp (by linarith [h'.1.2])
      rw [if_neg (fun h' => hxp h'.2), if_neg (fun h' => hxp h'.2), if_pos ⟨hxs, not_lt.mp hxp⟩,
        if_neg hRA, if_neg hRB]
      unfold stripIntegrand
      linarith only
  · have hRA : ¬(x ∈ Icc a₁ a₂ ∧ x + s ∈ Icc b₁ b₂) := fun h' => hxs (by linarith [h'.2.2])
    have hRB : ¬(x ∈ Icc c₁ c₂ ∧ x + s ∈ Icc d₁ d₂) := fun h' => hxs (by linarith [h'.2.2])
    rw [if_neg (fun h' => hxs h'.1), if_neg (fun h' => hxs h'.1), if_neg (fun h' => hxs h'.1),
      if_neg hRA, if_neg hRB]
    linarith only [mul_nonneg hk hJ]

section OffStripSchur

variable {P F : ℝ → ℝ} {B K : ℝ} (hPc : Continuous P) (hFc : Continuous F)
  (hPe : ∀ x, P (-x) = P x) (hFo : ∀ x, F (-x) = -F x) (hP0 : ∀ x, 0 ≤ P x)
  (hP1 : ∀ x, P x ≤ 1) (hPB : ∀ x, B ≤ |x| → P x = 0) (hFB : ∀ x, B ≤ |x| → F x = 0)
  (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hB0 : 0 < B) (hB1 : 2 * B ≤ 1)

include hPc hFc hFo hP0 hP1 hPB hFL hB0 hB1 in
/-- **The ground-state transform off the strip with two Schur rectangles.** The strip pairs keep their
exact surplus, the others are transformed in the gauge `h`, and the remainders of the rectangles
`H_A × Z_A` (hub below) and `Z_B × H_B` (hub above) are turned into potential:
`S_P(F) ≥ ∫ F² U_h^{off} + stripSurplus + s_A|H_A|∫_{Z_A} F² − β_A|Z_A|∫_{H_A} F²
+ s_B|H_B|∫_{Z_B} F² − β_B|Z_B|∫_{H_B} F²`. -/
theorem surplusEnergy_ge_potentialOff_add_strip_add_schur {h : ℝ → ℝ} {p r a₀ L : ℝ}
    {a₁ a₂ b₁ b₂ βA sA c₁ c₂ d₁ d₂ βB sB : ℝ} (hp : 0 < p)
    (hpr : p ≤ r) (hrB : r ≤ B) (hPr : ∀ x, |x| ≤ r → P x = 1) (hFr : ∀ x, F x ≠ 0 → |x| ≤ r)
    (hh : Continuous h) (ha₀ : 0 < a₀) (hhpos : ∀ x, 0 ≤ x → x ≤ r → a₀ ≤ h x)
    (hhL : ∀ x y, 0 ≤ x → x ≤ r → 0 ≤ y → y ≤ r → |h x - h y| ≤ L * |x - y|)
    (ha₁ : 0 < a₁) (ha : a₁ ≤ a₂) (hab : a₂ < b₁) (hb : b₁ ≤ b₂) (hbr : b₂ ≤ r) (hβA : 0 < βA)
    (hSA : ∀ x ∈ Icc b₁ b₂, ∀ y ∈ Icc a₁ a₂,
      sA ≤ surplusKernel x y * βA * (h y / h x) ^ 2 / (surplusKernel x y + βA * (h y / h x)))
    (hac : a₂ < c₁) (hc : c₁ ≤ c₂) (hcp : c₂ < p) (hcd : c₂ < d₁) (hd : d₁ ≤ d₂) (hdr : d₂ ≤ r)
    (hβB : 0 < βB)
    (hSB : ∀ x ∈ Icc c₁ c₂, ∀ y ∈ Icc d₁ d₂,
      sB ≤ surplusKernel x y * βB * (h y / h x) ^ 2 / (surplusKernel x y + βB * (h y / h x))) :
    IntegrableOn (fun x => F x ^ 2 * surplusPotentialOff h p r x) (Ioi 0) ∧
      (∫ x in Ioi (0 : ℝ), F x ^ 2 * surplusPotentialOff h p r x) + stripSurplus F p r +
        (sA * (a₂ - a₁) * (∫ x in Icc b₁ b₂, F x ^ 2) - βA * (b₂ - b₁) * ∫ y in Icc a₁ a₂, F y ^ 2) +
        (sB * (d₂ - d₁) * (∫ x in Icc c₁ c₂, F x ^ 2) - βB * (c₂ - c₁) * ∫ y in Icc d₁ d₂, F y ^ 2) ≤
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
  -- the two Schur densities
  have hc₁ : 0 < c₁ := by linarith
  have hIC := integrable_rectDensity hFc ha₁.le ha hab.le hb hbr hF2 (-βA) sA
  have hID := integrable_rectDensity hFc hc₁.le hc hcd.le hd hdr hF2 sB (-βB)
  -- the surplus density dominates the five densities
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
  have hpt : ∀ s x, 0 < s → 0 < x →
      gA (s, x) + gB (s, x) + gS (s, x) + rectDensity F a₁ a₂ b₁ b₂ (-βA) sA (s, x) + rectDensity F c₁ c₂ d₁ d₂ sB (-βB) (s, x) ≤ fS (s, x) := fun s x hs hx =>
    offStrip_schur_pointwise hP0 hPr ha₀ hhpos hbr hβA hSA hac hc hcp hdr hβB hSB hs hx
  -- the iterated comparison
  have hcmp : (∫ x in Ioi (0 : ℝ), ((∫ s in Ioi (0 : ℝ), gA (s, x)) +
      (∫ s in Ioi (0 : ℝ), gB (s, x)) + (∫ s in Ioi (0 : ℝ), gS (s, x)) +
      (∫ s in Ioi (0 : ℝ), rectDensity F a₁ a₂ b₁ b₂ (-βA) sA (s, x)) + ∫ s in Ioi (0 : ℝ), rectDensity F c₁ c₂ d₁ d₂ sB (-βB) (s, x))) ≤ surplusEnergy P F := by
    have hO : Integrable (fun x => (∫ s in Ioi (0 : ℝ), gA (s, x)) + (∫ s in Ioi (0 : ℝ), gB (s, x)) +
        (∫ s in Ioi (0 : ℝ), gS (s, x)) + (∫ s in Ioi (0 : ℝ), rectDensity F a₁ a₂ b₁ b₂ (-βA) sA (s, x)) +
        ∫ s in Ioi (0 : ℝ), rectDensity F c₁ c₂ d₁ d₂ sB (-βB) (s, x)) (volume.restrict (Ioi 0)) :=
      (((hIA.integral_prod_right.add hIB.integral_prod_right).add hIS'.integral_prod_right).add
        hIC.integral_prod_right).add hID.integral_prod_right
    refine integral_mono_ae hO hIfS.integral_prod_right ?_
    filter_upwards [hIA.prod_left_ae, hIB.prod_left_ae, hIS'.prod_left_ae, hIC.prod_left_ae,
      hID.prod_left_ae, hIfS.prod_left_ae, ae_restrict_mem measurableSet_Ioi]
      with x hxA hxB hxS' hxC hxD hxS hx0
    have hx : 0 < x := hx0
    have hAB : Integrable (fun s => gA (s, x) + gB (s, x)) (volume.restrict (Ioi 0)) := hxA.add hxB
    have hABS : Integrable (fun s => gA (s, x) + gB (s, x) + gS (s, x)) (volume.restrict (Ioi 0)) :=
      hAB.add hxS'
    have hABSC : Integrable (fun s => gA (s, x) + gB (s, x) + gS (s, x) + rectDensity F a₁ a₂ b₁ b₂ (-βA) sA (s, x))
        (volume.restrict (Ioi 0)) := hABS.add hxC
    have hABSCD : Integrable (fun s => gA (s, x) + gB (s, x) + gS (s, x) + rectDensity F a₁ a₂ b₁ b₂ (-βA) sA (s, x) + rectDensity F c₁ c₂ d₁ d₂ sB (-βB) (s, x))
        (volume.restrict (Ioi 0)) := hABSC.add hxD
    rw [← integral_add hxA hxB, ← integral_add hAB hxS', ← integral_add hABS hxC,
      ← integral_add hABSC hxD]
    refine integral_mono_ae hABSCD hxS ?_
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
  -- the Schur parts
  have hC := integral_rectDensity hFc ha₁ ha hab hb (F := F) (-βA) sA
  have hD := integral_rectDensity hFc hc₁ hc hcd hd (F := F) sB (-βB)
  have hI5 : Integrable (fun x => ∫ s in Ioi (0 : ℝ), rectDensity F a₁ a₂ b₁ b₂ (-βA) sA (s, x)) (volume.restrict (Ioi 0)) :=
    hIC.integral_prod_right
  have hI6 : Integrable (fun x => ∫ s in Ioi (0 : ℝ), rectDensity F c₁ c₂ d₁ d₂ sB (-βB) (s, x)) (volume.restrict (Ioi 0)) :=
    hID.integral_prod_right
  have hI124 : Integrable (fun x => (∫ s in Ioi (0 : ℝ), gA (s, x)) + (∫ s in Ioi (0 : ℝ), gB (s, x)) +
      ∫ s in Ioi (0 : ℝ), gS (s, x)) (volume.restrict (Ioi 0)) := hI12.add hI4
  have hI1245 : Integrable (fun x => (∫ s in Ioi (0 : ℝ), gA (s, x)) + (∫ s in Ioi (0 : ℝ), gB (s, x)) +
      (∫ s in Ioi (0 : ℝ), gS (s, x)) + ∫ s in Ioi (0 : ℝ), rectDensity F a₁ a₂ b₁ b₂ (-βA) sA (s, x)) (volume.restrict (Ioi 0)) :=
    hI124.add hI5
  have e1 := integral_add hI1245 hI6
  have e2 := integral_add hI124 hI5
  have e3 := integral_add hI12 hI4
  have e4 := integral_add hI1 hI2
  have e5 : (∫ x in Ioi (0 : ℝ), F x ^ 2 * surplusPotentialOff h p r x) =
      (∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), gA (s, x)) +
        ∫ x in Ioi (0 : ℝ), ∫ s in Ioi (0 : ℝ), gB (s, x) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hsum, integral_add hI1 hI3, ← hswap]
  linarith only [hcmp, e1, e2, e3, e4, e5, hC, hD, hstrip]

include hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0 hB1 in
/-- **The first prime window with the atom's even part and two Schur rectangles.** As
`fourKilling_add_potentialMixPrime_le_archJump_sub_prime`, with the two Schur rectangles of the
off-strip transform entering with its weight `θ`. -/
theorem fourKilling_add_potentialMixPrimeSchur_le_archJump_sub_prime {h : ℝ → ℝ} {r a₀ L θ t : ℝ}
    {a₁ a₂ b₁ b₂ βA sA c₁ c₂ d₁ d₂ βB sB : ℝ}
    (hFcs : HasCompactSupport F) (hr : Real.log 2 / 2 < r) (hr' : r ≤ Real.log 2 / 2 + 1 / 12)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hθ : (1 + t) * (2 * (4902 / 10000)) ≤ θ * (19 / 10 - (r - (Real.log 2 - r)) / 2 / (Real.log 2 - r) -
      3 * ((r - (Real.log 2 - r)) / 2) ^ 2))
    (hrB : r ≤ B) (hPr : ∀ x, |x| ≤ r → P x = 1) (hFr : ∀ x, F x ≠ 0 → |x| ≤ r)
    (hPcs : HasCompactSupport P) (hh : Continuous h) (ha₀ : 0 < a₀)
    (hhpos : ∀ x, 0 ≤ x → x ≤ r → a₀ ≤ h x)
    (hhL : ∀ x y, 0 ≤ x → x ≤ r → 0 ≤ y → y ≤ r → |h x - h y| ≤ L * |x - y|)
    (ha₁ : 0 < a₁) (ha : a₁ ≤ a₂) (hab : a₂ < b₁) (hb : b₁ ≤ b₂) (hbr : b₂ ≤ r) (hβA : 0 < βA)
    (hSA : ∀ x ∈ Icc b₁ b₂, ∀ y ∈ Icc a₁ a₂,
      sA ≤ surplusKernel x y * βA * (h y / h x) ^ 2 / (surplusKernel x y + βA * (h y / h x)))
    (hac : a₂ < c₁) (hc : c₁ ≤ c₂) (hcp : c₂ < Real.log 2 - r) (hcd : c₂ < d₁) (hd : d₁ ≤ d₂)
    (hdr : d₂ ≤ r) (hβB : 0 < βB)
    (hSB : ∀ x ∈ Icc c₁ c₂, ∀ y ∈ Icc d₁ d₂,
      sB ≤ surplusKernel x y * βB * (h y / h x) ^ 2 / (surplusKernel x y + βB * (h y / h x))) :
    IntegrableOn (fun x => F x ^ 2 * ((1 - θ) * surplusPotential h r x +
        θ * surplusPotentialOff h (Real.log 2 - r) r x)) (Ioi 0) ∧
      4 * (∫ x in Ioi (0 : ℝ), F x ^ 2 * (archLevyAntideriv x - archLevyAntideriv (x + r))) +
          2 * ((∫ x in Ioi (0 : ℝ), F x ^ 2 * ((1 - θ) * surplusPotential h r x +
            θ * surplusPotentialOff h (Real.log 2 - r) r x)) +
          49 / 100 * t * (∫ x in (Real.log 2 - r)..r, F x ^ 2) +
          θ * ((sA * (a₂ - a₁) * (∫ x in Icc b₁ b₂, F x ^ 2) - βA * (b₂ - b₁) * ∫ y in Icc a₁ a₂, F y ^ 2) +
            (sB * (d₂ - d₁) * (∫ x in Icc c₁ c₂, F x ^ 2) - βB * (c₂ - c₁) * ∫ y in Icc d₁ d₂, F y ^ 2))) ≤
        (∫ t in Ioi (0 : ℝ), archLevyDensity t * gaugeJumpProfile P F t) -
          2 * (vonMangoldtAtom 2 * ∫ x, F x * F (x + Real.log 2)) := by
  have hl0 := Real.log_two_gt_d9
  have hl1 := Real.log_two_lt_d9
  have hr0 : 0 < r := by linarith
  obtain ⟨hIA, hA⟩ := surplusEnergy_ge_potential hPc hFc hFo hP0 hP1 hPB hFL hB0 hB1 hrB hPr hFr
    hh ha₀ hhpos hhL
  obtain ⟨hIB, hBs⟩ := surplusEnergy_ge_potentialOff_add_strip_add_schur hPc hFc hFo hP0 hP1 hPB hFL
    hB0 hB1 (p := Real.log 2 - r) (by linarith) (by linarith) hrB hPr hFr hh ha₀ hhpos hhL ha₁ ha hab hb
    hbr hβA hSA hac hc hcp hcd hd hdr hβB hSB
  have hfold := fourKilling_add_surplusEnergy_le_archJump hPc hFc hPe hFo hP0 hP1 hPB hFB hFL hB0
    hB1 hr0 hrB hPr hFr hPcs
  have hsupp : ∀ x, r < |x| → F x = 0 := fun x hx => by
    by_contra h0; exact absurd (hFr x h0) (not_le.mpr hx)
  -- the sharp micro-fold pays the atom with the fraction `θ` of the strip
  set p := Real.log 2 - r with hpdef
  have hpr : p < r := by rw [hpdef]; linarith
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hL : p + r = Real.log 2 := by rw [hpdef]; ring
  have hr3 : r - p ≤ 2 * p := by rw [hpdef]; linarith
  have hr6 : r - p ≤ 1 / 6 := by rw [hpdef]; linarith
  have hms := sharpMicroFold_strip_ge hFc hFL hp0 hpr hL hr3 hr6
  have hT : (∫ x in p..r, ∫ y in p..r, surplusKernel x y * (F x - F y) ^ 2) =
      2 * stripSurplus F p r := integral_strip_eq_two_mul_stripSurplus hFc hFL hp0 hpr.le (by linarith)
  have hshift := integral_mul_shift_le_interp hFc hFcs hFo (r := r) (L := Real.log 2)
    (by linarith) (by rw [← hpdef]; exact hpr.le) hsupp ht1
  rw [← hpdef] at hshift
  obtain ⟨hΛ0, hΛ1⟩ := vonMangoldtAtom_two_bounds
  have hα0 : 0 ≤ ∫ x in p..r, reflectedOddPart F (Real.log 2) x ^ 2 :=
    intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  have hΛ2 := vonMangoldtAtom_two_ge
  have hS0 : 0 ≤ ∫ x in p..r, F x ^ 2 := intervalIntegral.integral_nonneg hpr.le fun _ _ => sq_nonneg _
  have hdom : 2 * (vonMangoldtAtom 2 * ∫ x, F x * F (x + Real.log 2)) ≤
      θ * (2 * stripSurplus F p r) - 49 / 50 * t * ∫ x in p..r, F x ^ 2 := by
    set A := ∫ x in p..r, reflectedOddPart F (Real.log 2) x ^ 2 with hA
    set B := ∫ x in p..r, F x ^ 2 with hB
    have k1 := mul_le_mul_of_nonneg_left hshift hΛ0
    have k2 := mul_le_mul_of_nonneg_right hθ hα0
    have k3 := mul_le_mul_of_nonneg_right hΛ1 (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + t) hα0)
    have k4 := mul_le_mul_of_nonneg_left hms hθ0
    have k5 := mul_le_mul_of_nonneg_right hΛ2 (mul_nonneg ht0 hS0)
    rw [hT] at k4
    nlinarith
  -- the mixed potential
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
  linarith only [k5, k6, hfold, hdom]

end OffStripSchur

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
