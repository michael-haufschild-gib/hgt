import GaloisForLFunctions.WindowTowerOfSpecZ.TheEndProfileOfAWindow
import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowBartaCriterion

/-!
# The ground-state transform of a window

A positive weight `h` on the window turns every jump into a Picone inequality. With the window gate
`G = h·1_{[−A,0]}` and the **Picone jump weight**

`a_h(y, u) = 2 − (G(u + y) + G(u − y))/h(u)`  (on the window, `0` off it),

every jump `y` satisfies `∫ a_h(y, u)H(u)² du ≤ ∫(H(u) − H(u + y))² du` (`integral_piconeWeight_mul_le`):
the pointwise identity `(a − b)² − a²(1 − q/p) − b²(1 − p/q) = (a√(q/p) − b√(p/q))²` with the gate
absorbing the exits. For `h = 1` the weight counts the exits (the exit potential); a non-constant `h`
also charges the interior jumps.

* **Archimedean ground-state bound** (`integral_mul_le_levyJump_of_picone`): if `a_h ≥ 0` (a balanced
  weight, e.g. `G(u ± y) ≤ h(u)`) and `V(u) ≤ ∫_0^∞ ω(y)a_h(y, u) dy` on the window, then
  `∫ V H² ≤ J_∞(H)`.
* **Ground-state criterion for Weil's window form** (`weilQuad_ge_groundState`): if moreover
  `Σ_{n≤e^A} (Λ(n)/√n)(G(u + log n) + G(u − log n)) ≤ κh(u)` on the window, then
  `Q(H) ≥ (Ω_Γ − κ)‖H‖² + ∫V H² + pole`. For `h = 1` this is the end-profile bound; a balanced weight
  is a nonlocal payment of the canonical class by the jumps, the Allegretto–Piepenbrink form of the
  window capacity problem.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole
open _root_.RHTower (archLevyDensity measurable_archLevyDensity)

variable {A : ℝ} {H : ℝ → ℝ}

/-- The **Picone jump weight** `a_h(y, u) = 2 − (G(u + y) + G(u − y))/h(u)` on the window. -/
def piconeWeight (A : ℝ) (h : ℝ → ℝ) (y u : ℝ) : ℝ :=
  (Icc (-A) 0).indicator (fun u => 2 - (windowGate A h (u + y) + windowGate A h (u - y)) / h u) u

theorem measurable_piconeWeight (A : ℝ) {h : ℝ → ℝ} (hm : Measurable h) :
    Measurable fun p : ℝ × ℝ => piconeWeight A h p.2 p.1 := by
  have hG : Measurable (windowGate A h) := hm.indicator measurableSet_Icc
  unfold piconeWeight
  simp only [indicator_apply]
  refine Measurable.ite (measurable_fst measurableSet_Icc) ?_ measurable_const
  exact measurable_const.sub (((hG.comp (measurable_fst.add measurable_snd)).add
    (hG.comp (measurable_fst.sub measurable_snd))).div (hm.comp measurable_fst))

/-- **Picone for one jump**: `∫ a_h(y, u)H(u)² ≤ ∫(H(u) − H(u + y))²`. -/
theorem integral_piconeWeight_mul_le (hH : IsWindowTest A H) {h : ℝ → ℝ} (hm : Measurable h)
    {C : ℝ} (h1 : ∀ u, 1 ≤ h u) (hC : ∀ u, h u ≤ C) (y : ℝ) :
    ∫ u, piconeWeight A h y u * H u ^ 2 ≤ ∫ u, (H u - H (u + y)) ^ 2 := by
  have hc := hH.continuous
  have hpos : ∀ u, 0 < h u := fun u => lt_of_lt_of_le one_pos (h1 u)
  have iH : Integrable fun u => H u ^ 2 := integrable_sq hc hH.hasCompactSupport
  have hGm : Measurable (windowGate A h) := hm.indicator measurableSet_Icc
  have hG0 : ∀ v, 0 ≤ windowGate A h v := fun v => indicator_nonneg (fun u _ => (hpos u).le) v
  have hGC : ∀ v, windowGate A h v ≤ C := fun v => by
    unfold windowGate
    by_cases hv : v ∈ Icc (-A) 0
    · rw [indicator_of_mem hv]; exact hC v
    · rw [indicator_of_notMem hv]; exact le_trans (by norm_num) ((h1 v).trans (hC v))
  -- bounded multipliers
  have hbdd : ∀ s : ℝ, Integrable fun u => (1 - windowGate A h (u + s) / h u) * H u ^ 2 := fun s =>
    iH.bdd_mul (c := 1 + C) ((measurable_const.sub ((hGm.comp (measurable_add_const s)).div
      hm)).aestronglyMeasurable) (Eventually.of_forall fun u => by
        show ‖1 - windowGate A h (u + s) / h u‖ ≤ 1 + C
        have h0 : 0 ≤ windowGate A h (u + s) / h u := div_nonneg (hG0 _) (hpos u).le
        have h2 : windowGate A h (u + s) / h u ≤ C :=
          (div_le_self (hG0 _) (h1 u)).trans (hGC _)
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith)
  have iJ : Integrable fun u => (H u - H (u + y)) ^ 2 :=
    integrable_sq (hc.sub (hc.comp (continuous_add_const y)))
      (hH.hasCompactSupport.sub (hasCompactSupport_comp_add hH.hasCompactSupport y))
  have iB : Integrable fun u => (1 - windowGate A h u / h (u + y)) * H (u + y) ^ 2 := by
    have := (hbdd (-y)).comp_add_right y
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [add_neg_cancel_right]
  -- pointwise Picone with gates
  have hpt : ∀ u, (1 - windowGate A h (u + y) / h u) * H u ^ 2 +
      (1 - windowGate A h u / h (u + y)) * H (u + y) ^ 2 ≤ (H u - H (u + y)) ^ 2 := fun u => by
    by_cases ha : u ∈ Icc (-A) 0
    · by_cases hb : u + y ∈ Icc (-A) 0
      · rw [windowGate, windowGate, indicator_of_mem ha, indicator_of_mem hb]
        have := two_abs_mul_le_ratio (hpos u) (hpos (u + y)) (H u) (H (u + y))
        have hab := le_abs_self (H u * H (u + y))
        nlinarith
      · have hG : windowGate A h (u + y) = 0 := indicator_of_notMem hb _
        rw [hH.vanish _ hb, hG]; simp
    · have hG : windowGate A h u = 0 := indicator_of_notMem ha _
      rw [hH.vanish _ ha, hG]; simp
  have hstep := integral_mono (f := fun u => (1 - windowGate A h (u + y) / h u) * H u ^ 2 +
      (1 - windowGate A h u / h (u + y)) * H (u + y) ^ 2)
    (g := fun u => (H u - H (u + y)) ^ 2) ((hbdd y).add iB) iJ hpt
  rw [integral_add (hbdd y) iB] at hstep
  have hshift : ∫ u, (1 - windowGate A h u / h (u + y)) * H (u + y) ^ 2 =
      ∫ u, (1 - windowGate A h (u - y) / h u) * H u ^ 2 := by
    have := integral_add_right_eq_self (μ := volume)
      (fun v => (1 - windowGate A h (v - y) / h v) * H v ^ 2) y
    rw [← this]
    exact integral_congr_ae (Eventually.of_forall fun u => by simp only [add_sub_cancel_right])
  -- assemble the Picone weight
  have hsum : ∫ u, piconeWeight A h y u * H u ^ 2 =
      (∫ u, (1 - windowGate A h (u + y) / h u) * H u ^ 2) +
        ∫ u, (1 - windowGate A h (u - y) / h u) * H u ^ 2 := by
    rw [← integral_add (hbdd y) (by simpa only [sub_eq_add_neg] using hbdd (-y))]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    show piconeWeight A h y u * H u ^ 2 = (1 - windowGate A h (u + y) / h u) * H u ^ 2 +
      (1 - windowGate A h (u - y) / h u) * H u ^ 2
    unfold piconeWeight
    by_cases hu : u ∈ Icc (-A) 0
    · rw [indicator_of_mem hu]; ring
    · rw [indicator_of_notMem hu, hH.vanish u hu]; ring
  rw [hsum, ← hshift]
  exact hstep

/-- **Archimedean ground-state bound**: for a balanced weight (`a_h ≥ 0`) and a potential
`0 ≤ V(u) ≤ ∫_0^∞ ω(y)a_h(y, u) dy` on the window, `∫ V H² ≤ J_∞(H)`. -/
theorem integral_mul_le_levyJump_of_picone (hH : IsWindowTest A H) {h : ℝ → ℝ}
    (hm : Measurable h) {C : ℝ} (h1 : ∀ u, 1 ≤ h u) (hC : ∀ u, h u ≤ C)
    (hbal : ∀ y u, 0 ≤ piconeWeight A h y u) {V : ℝ → ℝ} (hVm : Measurable V) (hV0 : ∀ u, 0 ≤ V u)
    (hV : ∀ u ∈ Icc (-A) 0, ENNReal.ofReal (V u) ≤
      ∫⁻ y in Ioi 0, ENNReal.ofReal (archLevyDensity y * piconeWeight A h y u)) :
    Integrable (fun u => V u * H u ^ 2) ∧ ∫ u, V u * H u ^ 2 ≤ levyJump H := by
  have hc := hH.continuous
  have hpos : ∀ u, 0 < h u := fun u => lt_of_lt_of_le one_pos (h1 u)
  have iH := integrable_sq hc hH.hasCompactSupport
  have hpm := measurable_piconeWeight A hm
  have hP2 : ∀ y u, piconeWeight A h y u ≤ 2 := fun y u => by
    unfold piconeWeight
    by_cases hu : u ∈ Icc (-A) 0
    · rw [indicator_of_mem hu]
      have : 0 ≤ (windowGate A h (u + y) + windowGate A h (u - y)) / h u :=
        div_nonneg (add_nonneg (indicator_nonneg (fun v _ => (hpos v).le) _)
          (indicator_nonneg (fun v _ => (hpos v).le) _)) (hpos u).le
      linarith
    · rw [indicator_of_notMem hu]; norm_num
  -- the lintegral form
  have hle : ∫⁻ u, ENNReal.ofReal (V u * H u ^ 2) ≤
      ∫⁻ y in Ioi 0, ENNReal.ofReal (archLevyDensity y * ∫ u, (H u - H (u + y)) ^ 2) := by
    have hmeas : Measurable (Function.uncurry fun u y =>
        ENNReal.ofReal (archLevyDensity y * (piconeWeight A h y u * H u ^ 2))) := by
      refine Measurable.ennreal_ofReal (Measurable.mul (measurable_archLevyDensity.comp
        measurable_snd) (Measurable.mul hpm ?_))
      exact (hc.measurable.comp measurable_fst).pow_const 2
    calc ∫⁻ u, ENNReal.ofReal (V u * H u ^ 2)
        ≤ ∫⁻ u, ∫⁻ y in Ioi 0, ENNReal.ofReal (archLevyDensity y * (piconeWeight A h y u * H u ^ 2)) := by
          refine lintegral_mono fun u => ?_
          by_cases hu : u ∈ Icc (-A) 0
          · have hexp : ∫⁻ y in Ioi 0, ENNReal.ofReal (archLevyDensity y *
                (piconeWeight A h y u * H u ^ 2)) = (∫⁻ y in Ioi 0, ENNReal.ofReal
                  (archLevyDensity y * piconeWeight A h y u)) * ENNReal.ofReal (H u ^ 2) := by
              rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
              refine setLIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
              rw [← ENNReal.ofReal_mul (mul_nonneg (archLevyDensity_nonneg hy) (hbal y u))]
              ring_nf
            rw [hexp, ENNReal.ofReal_mul (hV0 u)]
            gcongr
            exact hV u hu
          · rw [hH.vanish u hu]; simp
      _ = ∫⁻ y in Ioi 0, ∫⁻ u, ENNReal.ofReal (archLevyDensity y * (piconeWeight A h y u * H u ^ 2)) :=
          lintegral_lintegral_swap hmeas.aemeasurable
      _ ≤ ∫⁻ y in Ioi 0, ENNReal.ofReal (archLevyDensity y * ∫ u, (H u - H (u + y)) ^ 2) := by
          refine setLIntegral_mono' measurableSet_Ioi fun y hy => ?_
          have hω := archLevyDensity_nonneg (mem_Ioi.mp hy)
          have iE : Integrable fun u => piconeWeight A h y u * H u ^ 2 :=
            iH.bdd_mul (c := 2) ((hpm.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
              (Eventually.of_forall fun u => by
                show ‖piconeWeight A h y u‖ ≤ 2
                rw [Real.norm_eq_abs, abs_of_nonneg (hbal y u)]; exact hP2 y u)
          calc ∫⁻ u, ENNReal.ofReal (archLevyDensity y * (piconeWeight A h y u * H u ^ 2))
              = ENNReal.ofReal (archLevyDensity y) *
                  ∫⁻ u, ENNReal.ofReal (piconeWeight A h y u * H u ^ 2) := by
                rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
                exact lintegral_congr fun u => ENNReal.ofReal_mul hω
            _ = ENNReal.ofReal (archLevyDensity y * ∫ u, piconeWeight A h y u * H u ^ 2) := by
                rw [← ofReal_integral_eq_lintegral_ofReal iE (Eventually.of_forall fun u =>
                  mul_nonneg (hbal y u) (sq_nonneg _)), ← ENNReal.ofReal_mul hω]
            _ ≤ ENNReal.ofReal (archLevyDensity y * ∫ u, (H u - H (u + y)) ^ 2) :=
                ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
                  (integral_piconeWeight_mul_le hH hm h1 hC y) hω)
  have hfin := RHTower.SeparatedBump.lintegral_levy_ne_top hH.contDiff hH.hasCompactSupport
  have hnn : 0 ≤ᵐ[volume] fun u => V u * H u ^ 2 :=
    Eventually.of_forall fun u => mul_nonneg (hV0 u) (sq_nonneg _)
  have hmV : AEStronglyMeasurable (fun u => V u * H u ^ 2) volume :=
    (hVm.mul (hc.measurable.pow_const 2)).aestronglyMeasurable
  refine ⟨⟨hmV, (hasFiniteIntegral_iff_ofReal hnn).mpr (lt_of_le_of_lt hle hfin.lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmV, levyJump]
  exact ENNReal.toReal_mono hfin hle

/-- **The ground-state criterion for Weil's window form**: a balanced weight `h` with archimedean
potential `V` and fold constant `κ` (`Σ_n (Λ(n)/√n)(G(u + log n) + G(u − log n)) ≤ κh(u)`) gives
`Q(H) ≥ (Ω_Γ − κ)‖H‖² + ∫V H² + pole`. -/
theorem weilQuad_ge_groundState (hH : IsWindowTest A H) {h : ℝ → ℝ} (hm : Measurable h) {C : ℝ}
    (h1 : ∀ u, 1 ≤ h u) (hC : ∀ u, h u ≤ C) (hbal : ∀ y u, 0 ≤ piconeWeight A h y u)
    {V : ℝ → ℝ} (hVm : Measurable V) (hV0 : ∀ u, 0 ≤ V u)
    (hV : ∀ u ∈ Icc (-A) 0, ENNReal.ofReal (V u) ≤
      ∫⁻ y in Ioi 0, ENNReal.ofReal (archLevyDensity y * piconeWeight A h y u))
    {κ : ℝ} (hK : ∀ u ∈ Icc (-A) 0, ∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n *
      (windowGate A h (u + Real.log n) + windowGate A h (u - Real.log n)) ≤ κ * h u)
    (hκ : 0 < κ) :
    EF.gammaBracket 0 * (∫ u, H u ^ 2) + (∫ u, V u * H u ^ 2) - κ * (∫ u, H u ^ 2) +
      (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2) ≤ weilQuad H := by
  rw [weilQuad_eq_windowRep hH, integral_windowRep_vonMangoldt_mul hH]
  have hJ := (integral_mul_le_levyJump_of_picone hH hm h1 hC hbal hVm hV0 hV).2
  -- the folds, through the Barta criterion with weights `w_n/(2κ)`
  have hfold := sum_two_mul_abs_autocorr_le hH hm h1 hC (Finset.Icc 2 (windowLevel A))
    (a := fun n => primeJumpWeight n / κ) (fun n => div_nonneg (primeJumpWeight_nonneg n) hκ.le)
    (fun u hu => by
      have := hK u hu
      calc ∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n / κ *
            (windowGate A h (u + Real.log n) + windowGate A h (u - Real.log n))
          = (∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n *
            (windowGate A h (u + Real.log n) + windowGate A h (u - Real.log n))) / κ := by
            rw [Finset.sum_div]; exact Finset.sum_congr rfl fun n _ => by ring
        _ ≤ κ * h u / κ := div_le_div_of_nonneg_right this hκ.le
        _ = h u := by field_simp)
  have hsum : ∑ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n * ∫ u, H u * H (u + Real.log n) ≤
      κ / 2 * ∫ u, H u ^ 2 := by
    have hterm : ∀ n ∈ Finset.Icc 2 (windowLevel A), primeJumpWeight n * ∫ u, H u * H (u + Real.log n) ≤
        κ / 2 * (2 * (primeJumpWeight n / κ) * |∫ u, H u * H (u + Real.log n)|) := fun n _ => by
      have hw := primeJumpWeight_nonneg n
      have : κ / 2 * (2 * (primeJumpWeight n / κ) * |∫ u, H u * H (u + Real.log n)|) =
          primeJumpWeight n * |∫ u, H u * H (u + Real.log n)| := by field_simp
      rw [this]
      exact mul_le_mul_of_nonneg_left (le_abs_self _) hw
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hfold (by linarith)
  linarith

end GaloisForLFunctions.WindowTowerOfSpecZ
