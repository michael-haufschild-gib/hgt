import GaloisForLFunctions.RHTower.CompositeResolventDivision
import GaloisForLFunctions.RHTower.XiWindowQuotient
import GaloisForLFunctions.HTGeometry.ExponentialLagrangeContour

/-!
# The node divisor of a window and the frame of its rectangles

Fix a height `t₀`, a half-width `X` and a depth `y₀`. The *nodes* are the zeros `ρ` of `ξ` with
`|Im ρ - t₀| < X` and `|Re ρ - ½| > y₀` (`nodeSet`); in the coordinate `γ = gammaOf ρ` they are
exactly the zeros of `Ξ` inside the rectangles `[t₀ - X, t₀ + X] × ±[y₀, 1]`. The node divisor
lists `γ` with the multiplicity of `ρ` in the divisor of `ξ` (`nodeList`), and `Ξ` has at each
node a local factor of exactly that order (`riemannXiHat_local_factor`), so the composite
resolvent division of Riemann's kernel `Φ` by the node divisor is legitimate
(`divisorData_nodeList`).

On the frame of the two rectangles, every sub-product of the window divisor is bounded below by
`(δ₀/(16e))^N`, `N` the number of window zeros with multiplicity, once `X` and `y₀` come from
the forward-difference selection (`prod_norm_sub_ge_on_frame`). The reflection
`ρ ↦ 1 - conj ρ` preserves the window divisor with multiplicity (`prod_windowCopySet_conj`).
-/

open Complex MeasureTheory Filter Topology Set Polynomial GaloisForLFunctions
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

local notation "Φ" => riemannPhiKernel

/-! ## Local factors of `Ξ` with the divisor multiplicity -/

theorem divMult_eq_order (ρ : XiDivisorSupport) :
    divMult ρ = (analyticOrderAt xi (ρ : ℂ)).toNat := by
  unfold divMult
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply (xi_analyticOnNhd _) (Set.mem_univ _),
    ← ENat.coe_toNat (xi_orderAt_ne_top _)]
  simp

/-- `Ξ` has at `gammaOf ρ` a local factor of order exactly the divisor multiplicity of `ρ`. -/
theorem riemannXiHat_local_factor (ρ : XiDivisorSupport) :
    ∃ u : ℂ → ℂ, ContinuousAt u (gammaOf (ρ : ℂ)) ∧ u (gammaOf (ρ : ℂ)) ≠ 0 ∧
      riemannXiHat =ᶠ[𝓝 (gammaOf (ρ : ℂ))] fun z => (z - gammaOf (ρ : ℂ)) ^ divMult ρ * u z := by
  have hord : analyticOrderAt xi (ρ : ℂ) = (divMult ρ : ℕ) := by
    rw [divMult_eq_order, ENat.coe_toNat (xi_orderAt_ne_top _)]
  obtain ⟨g, hg, hg0, hev⟩ := (xi_analyticAt (ρ : ℂ)).analyticOrderAt_eq_natCast.mp hord
  set γ := gammaOf (ρ : ℂ) with hγ
  have hmap : Tendsto (fun z : ℂ => 1 / 2 + I * z) (𝓝 γ) (𝓝 (ρ : ℂ)) := by
    have hc : Continuous fun z : ℂ => 1 / 2 + I * z := by fun_prop
    have := hc.tendsto γ
    rwa [hγ, one_half_add_I_mul_gammaOf] at this
  refine ⟨fun z => I ^ divMult ρ * g (1 / 2 + I * z), ?_, ?_, ?_⟩
  · refine continuousAt_const.mul (ContinuousAt.comp_of_eq hg.continuousAt (by fun_prop) ?_)
    rw [hγ, one_half_add_I_mul_gammaOf]
  · show I ^ divMult ρ * g (1 / 2 + I * gammaOf (ρ : ℂ)) ≠ 0
    rw [one_half_add_I_mul_gammaOf]
    exact mul_ne_zero (pow_ne_zero _ I_ne_zero) hg0
  · filter_upwards [hmap.eventually hev] with z hz
    rw [riemannXiHat_eq_xi, hz, smul_eq_mul]
    have e : 1 / 2 + I * z - (ρ : ℂ) = I * (z - γ) := by
      rw [hγ]
      have := one_half_add_I_mul_gammaOf (ρ : ℂ)
      linear_combination this
    rw [e, mul_pow]; ring

/-- Every zero of `Ξ` is `gammaOf` of a point of the divisor of `ξ`. -/
theorem exists_divisorSupport_of_riemannXiHat_eq_zero {z : ℂ} (hz : riemannXiHat z = 0) :
    ∃ ρ : XiDivisorSupport, gammaOf (ρ : ℂ) = z := by
  rw [riemannXiHat_eq_xi] at hz
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hz
  refine ⟨q.1, ?_⟩
  rw [hq]
  unfold gammaOf
  field_simp
  ring_nf

theorem divisorSupport_mem_carrier (ρ : XiDivisorSupport) : (ρ : ℂ) ∈ zetaZeroConfig.carrier :=
  xiZeroCopy_mem_carrier (firstCopy ρ)

theorem abs_gammaOf_divisorSupport_im_lt (ρ : XiDivisorSupport) :
    |(gammaOf (ρ : ℂ)).im| < 1 / 2 :=
  WeilEF.abs_gammaOf_im_lt ⟨divisorSupport_re_pos ρ, divisorSupport_re_lt_one ρ⟩

/-! ## The node set of a window -/

/-- The zeros with ordinate within `X` of `t₀` and depth `|β - ½| > y₀`. -/
def nodeSet (t₀ X y₀ : ℝ) : Finset XiDivisorSupport :=
  (windowSet t₀).filter fun ρ => |(ρ : ℂ).im - t₀| < X ∧ y₀ < |(ρ : ℂ).re - 1 / 2|

theorem mem_nodeSet {t₀ X y₀ : ℝ} (hX : X ≤ 2) {ρ : XiDivisorSupport} :
    ρ ∈ nodeSet t₀ X y₀ ↔ |(ρ : ℂ).im - t₀| < X ∧ y₀ < |(ρ : ℂ).re - 1 / 2| := by
  unfold nodeSet
  rw [Finset.mem_filter, mem_windowSet]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨by linarith [h.1], h⟩

/-- The node divisor as a list of points `gammaOf ρ` with the divisor multiplicities. -/
def nodeList (t₀ X y₀ : ℝ) : List (ℂ × ℕ) :=
  (nodeSet t₀ X y₀).toList.map fun ρ : XiDivisorSupport => (gammaOf (ρ : ℂ), divMult ρ)

theorem divisorEval_nodeList (t₀ X y₀ : ℝ) (z : ℂ) :
    divisorEval (nodeList t₀ X y₀) z =
      ∏ ρ ∈ nodeSet t₀ X y₀, (z - gammaOf (ρ : ℂ)) ^ divMult ρ := by
  unfold divisorEval nodeList
  rw [List.map_map]
  exact Finset.prod_map_toList _ _

theorem orderSum_nodeList (t₀ X y₀ : ℝ) :
    orderSum (nodeList t₀ X y₀) = ∑ ρ ∈ nodeSet t₀ X y₀, divMult ρ := by
  unfold orderSum nodeList
  rw [List.map_map]
  exact Finset.sum_map_toList _ _

theorem mem_nodeList {t₀ X y₀ : ℝ} {p : ℂ × ℕ} :
    p ∈ nodeList t₀ X y₀ ↔ ∃ ρ ∈ nodeSet t₀ X y₀, (gammaOf (ρ : ℂ), divMult ρ) = p := by
  unfold nodeList
  rw [List.mem_map]
  simp only [Finset.mem_toList]

theorem gammaOf_divisorSupport_injective :
    Function.Injective fun ρ : XiDivisorSupport => gammaOf (ρ : ℂ) :=
  fun _ _ h => Subtype.ext (gammaOf_injective h)

theorem divisorData_nodeList (t₀ X y₀ : ℝ) : DivisorData (nodeList t₀ X y₀) Φ := by
  refine ⟨?_, ?_, ?_⟩
  · unfold nodeList
    rw [List.pairwise_map]
    exact (Finset.nodup_toList _).imp fun h e => h (gammaOf_divisorSupport_injective e)
  · intro p hp
    obtain ⟨ρ, -, rfl⟩ := mem_nodeList.mp hp
    exact (abs_gammaOf_divisorSupport_im_lt ρ).le
  · intro p hp
    obtain ⟨ρ, -, rfl⟩ := mem_nodeList.mp hp
    obtain ⟨u, hu, hu0, hloc⟩ := riemannXiHat_local_factor ρ
    exact ⟨u, hu, hu0, hloc⟩

/-! ## Products over the window on the frame of the rectangles -/

/-- The frame of the two rectangles `[t₀ ± X] × ±[y₀, 1]`: vertical sides, inner and outer
horizontal sides. -/
def OnFrame (t₀ X y₀ : ℝ) (t : ℂ) : Prop := |t.re - t₀| = X ∨ |t.im| = y₀ ∨ |t.im| = 1

theorem prod_le_prod_mul_pow_of_subset {S V : Finset XiZeroCopy} (hSV : S ⊆ V) {a : XiZeroCopy → ℝ}
    (ha0 : ∀ q ∈ V, 0 ≤ a q) {B : ℝ} (hB : 1 ≤ B) (haB : ∀ q ∈ V, a q ≤ B) :
    ∏ q ∈ V, a q ≤ (∏ q ∈ S, a q) * B ^ V.card := by
  classical
  rw [← Finset.prod_sdiff hSV, mul_comm]
  gcongr
  · exact Finset.prod_nonneg fun q hq => ha0 q (hSV hq)
  · calc ∏ q ∈ V \ S, a q ≤ ∏ q ∈ V \ S, B :=
          Finset.prod_le_prod (fun q hq => ha0 q (Finset.sdiff_subset hq))
            fun q hq => haB q (Finset.sdiff_subset hq)
      _ = B ^ (V \ S).card := Finset.prod_const _
      _ ≤ B ^ V.card := pow_le_pow_right₀ hB (Finset.card_le_card Finset.sdiff_subset)

/-- **Window products on the frame.** If `X` and `y₀` are chosen by the forward-difference
selection, then at every frame point `t` and for every subfamily `S` of the window copies,
`Π_{q ∈ S} |t - γ_q| ≥ (δ₀/(16e))^N`, `N` the number of window copies. -/
theorem prod_norm_sub_ge_on_frame {t₀ X y₀ δ₀ : ℝ} (hX1 : 1 / 2 ≤ X) (hX2 : X ≤ 3 / 4)
    (hδ₀ : 0 < δ₀) (hδ₁ : δ₀ ≤ 1 / 2) (hy₁ : y₀ ≤ δ₀ / 2)
    (hselX : (1 / (8 * Real.exp 1)) ^ (windowCopySet t₀).card ≤
      ∏ q ∈ windowCopySet t₀, abs (X - |(q.1 : ℂ).im - t₀|))
    (hsely : (δ₀ / (8 * Real.exp 1)) ^ (windowCopySet t₀).card ≤
      ∏ q ∈ windowCopySet t₀, abs (y₀ - |(q.1 : ℂ).re - 1 / 2|))
    {t : ℂ} (ht : OnFrame t₀ X y₀ t) {S : Finset XiZeroCopy} (hS : S ⊆ windowCopySet t₀) :
    (δ₀ / (16 * Real.exp 1)) ^ (windowCopySet t₀).card ≤
      ∏ q ∈ S, ‖t - gammaOf (q.1 : ℂ)‖ := by
  classical
  set V := windowCopySet t₀
  set N := V.card
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have he1 : 2 ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hre : ∀ q : XiZeroCopy, (gammaOf (q.1 : ℂ)).re = (q.1 : ℂ).im := fun q => WeilEF.gammaOf_re _
  have him : ∀ q : XiZeroCopy, (gammaOf (q.1 : ℂ)).im = 1 / 2 - (q.1 : ℂ).re :=
    fun q => WeilEF.gammaOf_im _
  have hbase : δ₀ / (16 * Real.exp 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  rcases ht with h1 | h2 | h3
  · -- vertical sides
    have hf : ∀ q ∈ S, abs (X - |(q.1 : ℂ).im - t₀|) ≤ ‖t - gammaOf (q.1 : ℂ)‖ := by
      intro q _
      refine le_trans ?_ (Complex.abs_re_le_norm _)
      rw [Complex.sub_re, hre, ← h1]
      calc abs (|t.re - t₀| - |(q.1 : ℂ).im - t₀|) ≤ |(t.re - t₀) - ((q.1 : ℂ).im - t₀)| :=
            abs_abs_sub_abs_le_abs_sub _ _
        _ = |t.re - (q.1 : ℂ).im| := by ring_nf
    have ha2 : ∀ q ∈ V, abs (X - |(q.1 : ℂ).im - t₀|) ≤ 2 := by
      intro q hq
      have hw := mem_windowCopySet.mp hq
      rw [abs_le]; constructor <;> linarith [abs_nonneg ((q.1 : ℂ).im - t₀)]
    have hmain := prod_le_prod_mul_pow_of_subset hS (fun q _ => abs_nonneg _) (by norm_num) ha2
    have hSprod : ∏ q ∈ S, abs (X - |(q.1 : ℂ).im - t₀|) ≤ ∏ q ∈ S, ‖t - gammaOf (q.1 : ℂ)‖ :=
      Finset.prod_le_prod (fun _ _ => abs_nonneg _) hf
    have h2N : (0 : ℝ) < 2 ^ N := by positivity
    calc (δ₀ / (16 * Real.exp 1)) ^ N ≤ (1 / (16 * Real.exp 1)) ^ N := by
          gcongr; linarith
      _ = (1 / (8 * Real.exp 1)) ^ N / 2 ^ N := by
          rw [← div_pow]; congr 1; field_simp; ring
      _ ≤ (∏ q ∈ S, abs (X - |(q.1 : ℂ).im - t₀|)) := by
          rw [div_le_iff₀ h2N]; exact hselX.trans hmain
      _ ≤ _ := hSprod
  · -- inner horizontal sides
    have hf : ∀ q ∈ S, abs (y₀ - |(q.1 : ℂ).re - 1 / 2|) ≤ ‖t - gammaOf (q.1 : ℂ)‖ := by
      intro q _
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      rw [Complex.sub_im, him, ← h2]
      calc abs (|t.im| - |(q.1 : ℂ).re - 1 / 2|) = abs (|t.im| - |1 / 2 - (q.1 : ℂ).re|) := by
            rw [abs_sub_comm ((q.1 : ℂ).re)]
        _ ≤ |t.im - (1 / 2 - (q.1 : ℂ).re)| := abs_abs_sub_abs_le_abs_sub _ _
    have hb1 : ∀ q ∈ V, abs (y₀ - |(q.1 : ℂ).re - 1 / 2|) ≤ 1 := by
      intro q _
      have h0 := xiZeroCopy_re_pos q
      have h1' := xiZeroCopy_re_lt_one q
      have hy0 : 0 ≤ y₀ := by rw [← h2]; exact abs_nonneg _
      rw [abs_le]; constructor <;>
        linarith [abs_nonneg ((q.1 : ℂ).re - 1 / 2), abs_lt.mpr (⟨by linarith, by linarith⟩ :
          -(1 / 2 : ℝ) < (q.1 : ℂ).re - 1 / 2 ∧ (q.1 : ℂ).re - 1 / 2 < 1 / 2)]
    have hmain := prod_le_prod_mul_pow_of_subset hS (fun q _ => abs_nonneg _) le_rfl hb1
    rw [one_pow, mul_one] at hmain
    have hSprod : ∏ q ∈ S, abs (y₀ - |(q.1 : ℂ).re - 1 / 2|) ≤ ∏ q ∈ S, ‖t - gammaOf (q.1 : ℂ)‖ :=
      Finset.prod_le_prod (fun _ _ => abs_nonneg _) hf
    calc (δ₀ / (16 * Real.exp 1)) ^ N ≤ (δ₀ / (8 * Real.exp 1)) ^ N := by
          gcongr; linarith
      _ ≤ _ := hsely.trans (hmain.trans hSprod)
  · -- outer horizontal sides
    have hf : ∀ q ∈ S, (1 / 2 : ℝ) ≤ ‖t - gammaOf (q.1 : ℂ)‖ := by
      intro q _
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      have hq := WeilEF.abs_gammaOf_im_lt ⟨xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q⟩
      rw [Complex.sub_im]
      calc (1 / 2 : ℝ) ≤ |t.im| - |(gammaOf (q.1 : ℂ)).im| := by linarith
        _ ≤ |t.im - (gammaOf (q.1 : ℂ)).im| := abs_sub_abs_le_abs_sub _ _
    calc (δ₀ / (16 * Real.exp 1)) ^ N ≤ (1 / 2) ^ N := by gcongr
      _ ≤ (1 / 2) ^ S.card := pow_le_pow_of_le_one (by norm_num) (by norm_num)
          (Finset.card_le_card hS)
      _ = ∏ q ∈ S, (1 / 2 : ℝ) := (Finset.prod_const _).symm
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by norm_num) hf


/-! ## The reflection `ρ ↦ 1 - conj ρ` on the divisor -/

theorem xi_divisor_reflect (z : ℂ) :
    MeromorphicOn.divisor xi Set.univ (Zeta23.reflect z) = MeromorphicOn.divisor xi Set.univ z := by
  unfold Zeta23.reflect
  rw [xi_divisor_one_sub, xi_divisor_conj]

/-- The functional-equation reflection of a divisor point. -/
def reflectSupport (ρ : XiDivisorSupport) : XiDivisorSupport :=
  ⟨Zeta23.reflect (ρ : ℂ), by
    apply Function.mem_support.mpr
    rw [xi_divisor_reflect]
    exact Function.mem_support.mp ρ.2⟩

theorem reflectSupport_coe (ρ : XiDivisorSupport) :
    (reflectSupport ρ : ℂ) = Zeta23.reflect (ρ : ℂ) := rfl

theorem reflectSupport_reflectSupport (ρ : XiDivisorSupport) :
    reflectSupport (reflectSupport ρ) = ρ := by
  apply Subtype.ext
  simp only [reflectSupport_coe, Zeta23.reflect]
  simp

theorem divMult_reflectSupport (ρ : XiDivisorSupport) : divMult (reflectSupport ρ) = divMult ρ := by
  unfold divMult; rw [reflectSupport_coe, xi_divisor_reflect]

theorem gammaOf_reflectSupport (ρ : XiDivisorSupport) :
    gammaOf (reflectSupport ρ : ℂ) = (starRingEnd ℂ) (gammaOf (ρ : ℂ)) := by
  rw [reflectSupport_coe, gammaOf_reflect']

theorem reflectSupport_im (ρ : XiDivisorSupport) :
    (reflectSupport ρ : ℂ).im = (ρ : ℂ).im := by
  rw [reflectSupport_coe]; simp [Zeta23.reflect]

theorem reflectSupport_re (ρ : XiDivisorSupport) :
    (reflectSupport ρ : ℂ).re = 1 - (ρ : ℂ).re := by
  rw [reflectSupport_coe]; simp [Zeta23.reflect]

/-- The window divisor is invariant under the reflection, with multiplicity:
`Π_{V} f(conj γ_q) = Π_{V} f(γ_q)`. -/
theorem prod_windowCopySet_conj {M : Type*} [CommMonoid M] (t₀ : ℝ) (f : ℂ → M) :
    ∏ q ∈ windowCopySet t₀, f ((starRingEnd ℂ) (gammaOf (q.1 : ℂ))) =
      ∏ q ∈ windowCopySet t₀, f (gammaOf (q.1 : ℂ)) := by
  rw [prod_windowCopySet t₀ (fun z => f ((starRingEnd ℂ) (gammaOf z))),
    prod_windowCopySet t₀ (fun z => f (gammaOf z))]
  refine Finset.prod_nbij' reflectSupport reflectSupport (fun ρ hρ => ?_) (fun ρ hρ => ?_)
    (fun ρ _ => reflectSupport_reflectSupport ρ) (fun ρ _ => reflectSupport_reflectSupport ρ)
    (fun ρ _ => ?_)
  · rw [mem_windowSet, reflectSupport_im]; exact mem_windowSet.mp hρ
  · rw [mem_windowSet, reflectSupport_im]; exact mem_windowSet.mp hρ
  · rw [gammaOf_reflectSupport, divMult_reflectSupport]

end

end RHTower
