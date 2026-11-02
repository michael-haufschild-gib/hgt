import GaloisForLFunctions.WindowTowerOfSpecZ.TheExitChargePaysEveryNewFold
import GaloisForLFunctions.WindowTowerOfSpecZ.TheExactPoleCapacityOfAWindow

/-!
# The end profile of a window

Every archimedean jump of a window test either stays in the window or carries a point out of it.
A point `u ∈ (−A, 0)` leaves through the right end under every jump longer than `−u` and is entered
from outside the left end under every jump longer than `A + u`. Integrating the Lévy density over
these jumps gives the **exit potential** `e_A(u) = Ω(−u) + Ω(A + u)`, `Ω(t) = ∫_t^∞ ω`
(`exitPotential`), and

* **the exit-charge inequality** (`integral_exitPotential_mul_le`): `∫ e_A H² ≤ J_∞(H)` for every window
  test — a Hardy-type inequality for the Gamma factor's jumps, proved by exchanging the jump and the
  point integrals (`lintegral_exitPotential_le`);
* **the end-profile bound** (`weilQuad_ge_endProfile`): Weil's window form is at least
  `∫ (Ω_Γ + e_A − k_A) H² + pole`, where `Ω_Γ = Ω(0)` is the Gamma constant and `k_A` the canonical
  density of CWS: the interior jumps (archimedean and prime folds) are nonnegative and can be dropped;
* **the universal end profile** (`exitPotential_sub_canonicalDensity`): on the open window
  `e_A(u) − k_A(u) = φ(−u) + φ(A + u)`, `φ(t) = Ω(t) − ψ_{1/2}(e^t)` (`endProfile`). The potential of
  every window of the tower is `Ω_Γ + φ(d₋) + φ(d₊)` with the same function `φ` of the distances `d±`
  to the two ends: the Gamma factor's exit tail minus the half-weighted Chebyshev count.
* **Pointwise payment** (`weilQuad_nonneg_of_potential`): if `Ω_Γ + φ(d₋) + φ(d₊) ≥ 2 sinh(A/2) − A`
  on the window, Weil's form is nonnegative there.

`φ` is logarithmically large near an end and decreases like `−2e^{t/2}` in the bulk, so the
pointwise payment holds only on short windows; beyond, the interior jumps must pay — a Poincaré
inequality for the censored jump process against this potential, uniformly in the length.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis RHTower.WeilMarkovPole
open RHTower.WeilLevyPoleGauss
open _root_.RHTower (archLevyDensity measurable_archLevyDensity)

variable {A : ℝ} {H : ℝ → ℝ}

/-- The **exit potential** `e_A(u) = Ω(−u) + Ω(A + u)` on the open window, `0` outside. -/
def exitPotential (A u : ℝ) : ℝ :=
  (Ioo (-A) 0).indicator (fun u => archLevyAntideriv (-u) + archLevyAntideriv (A + u)) u

/-- The **end profile** `φ(t) = Ω(t) − ψ_{1/2}(e^t)`. -/
def endProfile (t : ℝ) : ℝ := archLevyAntideriv t - halfChebyshev (Real.exp t)

/-- The number of window exits of the point `u` under the jump `y`. -/
def exitWeight (A y u : ℝ) : ℝ :=
  (Ioo (-A) 0).indicator (fun u => (if -u < y then 1 else 0) + (if A + u < y then 1 else 0)) u

theorem exitPotential_nonneg (A u : ℝ) : 0 ≤ exitPotential A u := by
  unfold exitPotential
  by_cases hu : u ∈ Ioo (-A) 0
  · rw [indicator_of_mem hu]
    exact add_nonneg (archLevyAntideriv_pos (by linarith [hu.2])).le
      (archLevyAntideriv_pos (by linarith [hu.1])).le
  · rw [indicator_of_notMem hu]

theorem exitWeight_nonneg (A y u : ℝ) : 0 ≤ exitWeight A y u := by
  unfold exitWeight
  refine indicator_nonneg (fun u _ => add_nonneg ?_ ?_) u <;> split_ifs <;> norm_num

/-! ### One jump -/

/-- **One jump**: `∫ (exits of u under y)·H(u)² ≤ ∫(H − H(·+y))²`. -/
theorem integral_exitWeight_mul_le (hH : IsWindowTest A H) (y : ℝ) :
    ∫ u, exitWeight A y u * H u ^ 2 ≤ ∫ u, (H u - H (u + y)) ^ 2 := by
  have hc := hH.continuous
  have iH := integrable_sq hc hH.hasCompactSupport
  have iJ : Integrable fun u => (H u - H (u + y)) ^ 2 :=
    integrable_sq (hc.sub (hc.comp (continuous_add_const y)))
      (hH.hasCompactSupport.sub (hasCompactSupport_comp_add hH.hasCompactSupport y))
  set S₁ := Ioo (-A) 0 ∩ Ioi (-y)
  set S₂ := Ioo (-A) 0 ∩ Iio (y - A)
  have mS₁ : MeasurableSet S₁ := measurableSet_Ioo.inter measurableSet_Ioi
  have mS₂ : MeasurableSet S₂ := measurableSet_Ioo.inter measurableSet_Iio
  -- the exits split into right exits `S₁` and left entries `S₂`
  have hsplit : ∀ u, exitWeight A y u * H u ^ 2 =
      S₁.indicator (fun u => H u ^ 2) u + S₂.indicator (fun u => H u ^ 2) u := fun u => by
    unfold exitWeight
    by_cases hu : u ∈ Ioo (-A) 0
    · rw [indicator_of_mem hu]
      have e1 : u ∈ S₁ ↔ -u < y := ⟨fun h => by linarith [mem_Ioi.mp h.2],
        fun h => ⟨hu, mem_Ioi.mpr (by linarith)⟩⟩
      have e2 : u ∈ S₂ ↔ A + u < y := ⟨fun h => by linarith [mem_Iio.mp h.2],
        fun h => ⟨hu, mem_Iio.mpr (by linarith)⟩⟩
      by_cases h1 : -u < y <;> by_cases h2 : A + u < y <;>
        simp [h1, h2, e1, e2, indicator, add_mul]
    · rw [indicator_of_notMem hu, zero_mul, indicator_of_notMem (fun h => hu h.1),
        indicator_of_notMem (fun h => hu h.1), add_zero]
  have hpt : ∀ u, S₁.indicator (fun u => H u ^ 2) u + S₂.indicator (fun u => H u ^ 2) (u + y) ≤
      (H u - H (u + y)) ^ 2 := fun u => by
    by_cases h1 : u ∈ S₁
    · have h2 : u + y ∉ S₂ := fun h => by linarith [h.1.2, mem_Ioi.mp h1.2]
      rw [indicator_of_mem h1, indicator_of_notMem h2, add_zero,
        hH.vanish (u + y) fun hm => by linarith [hm.2, mem_Ioi.mp h1.2], sub_zero]
    · rw [indicator_of_notMem h1, zero_add]
      by_cases h2 : u + y ∈ S₂
      · rw [indicator_of_mem h2, hH.vanish u fun hm => by linarith [hm.1, mem_Iio.mp h2.2],
          zero_sub, neg_sq]
      · rw [indicator_of_notMem h2]; exact sq_nonneg _
  have iS₂ : Integrable fun u => S₂.indicator (fun u => H u ^ 2) (u + y) :=
    (iH.indicator mS₂).comp_add_right y
  calc ∫ u, exitWeight A y u * H u ^ 2
      = (∫ u, S₁.indicator (fun u => H u ^ 2) u) + ∫ u, S₂.indicator (fun u => H u ^ 2) u := by
        rw [← integral_add (iH.indicator mS₁) (iH.indicator mS₂)]
        exact integral_congr_ae (Eventually.of_forall hsplit)
    _ = ∫ u, (S₁.indicator (fun u => H u ^ 2) u + S₂.indicator (fun u => H u ^ 2) (u + y)) := by
        rw [integral_add (iH.indicator mS₁) iS₂,
          integral_add_right_eq_self (fun u => S₂.indicator (fun u => H u ^ 2) u) y]
    _ ≤ ∫ u, (H u - H (u + y)) ^ 2 := integral_mono ((iH.indicator mS₁).add iS₂) iJ hpt

/-! ### Integrating over the jumps -/

/-- `∫⁻_{y>0} ω(y)·1[c < y] = Ω(c)` for `c > 0`. -/
theorem lintegral_archLevyDensity_ite {c : ℝ} (hc : 0 < c) :
    ∫⁻ y in Ioi 0, ENNReal.ofReal (archLevyDensity y * (if c < y then 1 else 0)) =
      ENNReal.ofReal (archLevyAntideriv c) := by
  have hfun : (fun y => ENNReal.ofReal (archLevyDensity y * (if c < y then 1 else 0))) =
      (Ioi c).indicator fun y => ENNReal.ofReal (archLevyDensity y) := by
    funext y
    by_cases hy : c < y
    · rw [if_pos hy, mul_one, indicator_of_mem (mem_Ioi.mpr hy)]
    · rw [if_neg hy, mul_zero, ENNReal.ofReal_zero,
        indicator_of_notMem (fun h => hy (mem_Ioi.mp h))]
  rw [hfun, lintegral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, max_eq_left hc.le,
    ← RHTower.WeilLevyCoshCrossover.integral_archLevyDensity_Ioi hc]
  exact (ofReal_integral_eq_lintegral_ofReal
    (RHTower.WeilLevyCoshCrossover.integrableOn_archLevyDensity_Ioi hc)
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx =>
      archLevyDensity_nonneg (hc.trans hx)))).symm

/-- For a fixed point, integrating the exits over the jumps gives the exit potential. -/
theorem lintegral_exitWeight (A u : ℝ) (h : ℝ) :
    ∫⁻ y in Ioi 0, ENNReal.ofReal (archLevyDensity y * (exitWeight A y u * h ^ 2)) =
      ENNReal.ofReal (exitPotential A u * h ^ 2) := by
  unfold exitWeight exitPotential
  by_cases hu : u ∈ Ioo (-A) 0
  · simp only [indicator_of_mem hu]
    have h1 : 0 < -u := by linarith [hu.2]
    have h2 : 0 < A + u := by linarith [hu.1]
    have hexp : ∀ y, ENNReal.ofReal (archLevyDensity y *
        (((if -u < y then 1 else 0) + (if A + u < y then 1 else 0)) * h ^ 2)) =
        (ENNReal.ofReal (archLevyDensity y * (if -u < y then 1 else 0)) +
          ENNReal.ofReal (archLevyDensity y * (if A + u < y then 1 else 0))) *
            ENNReal.ofReal (h ^ 2) := fun y => by
      rcases le_or_gt y 0 with hy | hy
      · have e1 : ¬ (-u < y) := by linarith
        have e2 : ¬ (A + u < y) := by linarith
        simp [e1, e2]
      · have hω := archLevyDensity_nonneg hy
        rw [← ENNReal.ofReal_add (by split_ifs <;> simp [hω]) (by split_ifs <;> simp [hω]),
          ← ENNReal.ofReal_mul (add_nonneg (by split_ifs <;> simp [hω]) (by split_ifs <;> simp [hω]))]
        congr 1; ring
    simp_rw [hexp]
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      lintegral_add_left (by
        refine Measurable.ennreal_ofReal (Measurable.mul measurable_archLevyDensity ?_)
        exact Measurable.ite measurableSet_Ioi measurable_const measurable_const),
      lintegral_archLevyDensity_ite h1, lintegral_archLevyDensity_ite h2,
      ← ENNReal.ofReal_add (archLevyAntideriv_pos h1).le (archLevyAntideriv_pos h2).le,
      ← ENNReal.ofReal_mul (add_nonneg (archLevyAntideriv_pos h1).le (archLevyAntideriv_pos h2).le)]
  · simp [indicator_of_notMem hu]

theorem measurable_exitWeight (A : ℝ) : Measurable fun p : ℝ × ℝ => exitWeight A p.2 p.1 := by
  unfold exitWeight
  simp only [indicator_apply]
  refine Measurable.ite (measurable_fst measurableSet_Ioo) (Measurable.add ?_ ?_) measurable_const
  · exact Measurable.ite (measurableSet_lt measurable_fst.neg measurable_snd) measurable_const
      measurable_const
  · exact Measurable.ite (measurableSet_lt (measurable_const.add measurable_fst) measurable_snd)
      measurable_const measurable_const

/-- **The exit-charge inequality in `ℝ≥0∞`**: `∫⁻ e_A H² ≤ ∫⁻_{y>0} ω(y)∫(H − H(·+y))²`. -/
theorem lintegral_exitPotential_le (hH : IsWindowTest A H) :
    ∫⁻ u, ENNReal.ofReal (exitPotential A u * H u ^ 2) ≤
      ∫⁻ y in Ioi 0, ENNReal.ofReal (archLevyDensity y * ∫ u, (H u - H (u + y)) ^ 2) := by
  have hc := hH.continuous
  have iH := integrable_sq hc hH.hasCompactSupport
  -- exchange the point and the jump integrals
  have hmeas : Measurable (Function.uncurry fun u y =>
      ENNReal.ofReal (archLevyDensity y * (exitWeight A y u * H u ^ 2))) := by
    refine Measurable.ennreal_ofReal (Measurable.mul (measurable_archLevyDensity.comp
      measurable_snd) (Measurable.mul (measurable_exitWeight A) ?_))
    exact (hc.measurable.comp measurable_fst).pow_const 2
  calc ∫⁻ u, ENNReal.ofReal (exitPotential A u * H u ^ 2)
      = ∫⁻ u, ∫⁻ y in Ioi 0, ENNReal.ofReal (archLevyDensity y * (exitWeight A y u * H u ^ 2)) :=
        lintegral_congr fun u => (lintegral_exitWeight A u (H u)).symm
    _ = ∫⁻ y in Ioi 0, ∫⁻ u, ENNReal.ofReal (archLevyDensity y * (exitWeight A y u * H u ^ 2)) :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ ≤ ∫⁻ y in Ioi 0, ENNReal.ofReal (archLevyDensity y * ∫ u, (H u - H (u + y)) ^ 2) := by
        refine setLIntegral_mono' measurableSet_Ioi fun y hy => ?_
        have hω := archLevyDensity_nonneg (mem_Ioi.mp hy)
        have iE : Integrable fun u => exitWeight A y u * H u ^ 2 := by
          refine (iH.const_mul 2).mono' ((((measurable_exitWeight A).comp
            (measurable_id.prodMk measurable_const)).mul (hc.measurable.pow_const 2)).aestronglyMeasurable)
            (Eventually.of_forall fun u => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (exitWeight_nonneg A y u) (sq_nonneg _))]
          have : exitWeight A y u ≤ 2 := by
            unfold exitWeight
            by_cases hu : u ∈ Ioo (-A) 0
            · rw [indicator_of_mem hu]; split_ifs <;> norm_num
            · rw [indicator_of_notMem hu]; norm_num
          exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
        calc ∫⁻ u, ENNReal.ofReal (archLevyDensity y * (exitWeight A y u * H u ^ 2))
            = ENNReal.ofReal (archLevyDensity y) *
                ∫⁻ u, ENNReal.ofReal (exitWeight A y u * H u ^ 2) := by
              rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
              exact lintegral_congr fun u => ENNReal.ofReal_mul hω
          _ = ENNReal.ofReal (archLevyDensity y * ∫ u, exitWeight A y u * H u ^ 2) := by
              rw [← ofReal_integral_eq_lintegral_ofReal iE (Eventually.of_forall fun u =>
                mul_nonneg (exitWeight_nonneg A y u) (sq_nonneg _)), ← ENNReal.ofReal_mul hω]
          _ ≤ ENNReal.ofReal (archLevyDensity y * ∫ u, (H u - H (u + y)) ^ 2) :=
              ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
                (integral_exitWeight_mul_le hH y) hω)

theorem measurable_exitPotential (A : ℝ) : Measurable (exitPotential A) := by
  unfold exitPotential
  refine Measurable.indicator ?_ measurableSet_Ioo
  unfold archLevyAntideriv
  fun_prop

/-- **The exit-charge inequality**: `∫ e_A H² ≤ J_∞(H)`, and `e_A H²` is integrable. -/
theorem integral_exitPotential_mul_le (hH : IsWindowTest A H) :
    Integrable (fun u => exitPotential A u * H u ^ 2) ∧
      ∫ u, exitPotential A u * H u ^ 2 ≤ levyJump H := by
  have hfin := RHTower.SeparatedBump.lintegral_levy_ne_top hH.contDiff hH.hasCompactSupport
  have hle := lintegral_exitPotential_le hH
  have hnn : 0 ≤ᵐ[volume] fun u => exitPotential A u * H u ^ 2 :=
    Eventually.of_forall fun u => mul_nonneg (exitPotential_nonneg A u) (sq_nonneg _)
  have hm : AEStronglyMeasurable (fun u => exitPotential A u * H u ^ 2) volume :=
    ((measurable_exitPotential A).mul (hH.continuous.measurable.pow_const 2)).aestronglyMeasurable
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal hnn).mpr (lt_of_le_of_lt hle hfin.lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm, levyJump]
  exact ENNReal.toReal_mono hfin hle

/-! ### The end profile -/

/-- **The universal end profile**: on the open window, `e_A(u) − k_A(u) = φ(−u) + φ(A + u)`. -/
theorem exitPotential_sub_canonicalDensity {u : ℝ} (hu : u ∈ Ioo (-A) 0) :
    exitPotential A u - canonicalDensity A u = endProfile (-u) + endProfile (A + u) := by
  rw [exitPotential, indicator_of_mem hu,
    canonicalDensity_eq_halfChebyshev ⟨hu.1.le, hu.2.le⟩, endProfile, endProfile]
  ring

/-- **The end-profile bound**: Weil's window form is at least
`Ω_Γ‖H‖² + ∫ e_A H² − ∫ k_A H² + pole`. -/
theorem weilQuad_ge_endProfile (hH : IsWindowTest A H) :
    EF.gammaBracket 0 * (∫ u, H u ^ 2) + (∫ u, exitPotential A u * H u ^ 2) -
        (∫ u, canonicalDensity A u * H u ^ 2) +
          (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2) ≤ weilQuad H := by
  rw [weilQuad_eq_fold_sub_canonical hH]
  have hJ := (integral_exitPotential_mul_le hH).2
  have hF : 0 ≤ ∑ n ∈ Finset.Icc 2 (windowLevel A),
      primeJumpWeight n * foldEnergy A (Real.log n) H :=
    Finset.sum_nonneg fun n _ => mul_nonneg (primeJumpWeight_nonneg n) (foldEnergy_nonneg _ _ _)
  linarith

/-- The window potential `V_A = Ω_Γ + e_A − k_A`. -/
def windowPotential (A u : ℝ) : ℝ := EF.gammaBracket 0 + exitPotential A u - canonicalDensity A u

/-- **Weil's window form dominates its potential**: `Q(H) ≥ ∫ V_A H² + pole`. -/
theorem weilQuad_ge_windowPotential (hH : IsWindowTest A H) :
    (∫ u, windowPotential A u * H u ^ 2) + (coshPairing H ^ 2 / 2 - sinhPairing H ^ 2 / 2) ≤
      weilQuad H := by
  have iH := integrable_sq hH.continuous hH.hasCompactSupport
  have iE := (integral_exitPotential_mul_le hH).1
  have iK := integrable_canonicalDensity_mul hH.continuous hH.hasCompactSupport A
  have hsplit : ∫ u, windowPotential A u * H u ^ 2 = EF.gammaBracket 0 * (∫ u, H u ^ 2) +
      (∫ u, exitPotential A u * H u ^ 2) - ∫ u, canonicalDensity A u * H u ^ 2 := by
    have e : (fun u => windowPotential A u * H u ^ 2) = fun u =>
        (EF.gammaBracket 0 * H u ^ 2 + exitPotential A u * H u ^ 2) -
          canonicalDensity A u * H u ^ 2 := by
      funext u; simp only [windowPotential]; ring
    have i1 : Integrable fun u => EF.gammaBracket 0 * H u ^ 2 + exitPotential A u * H u ^ 2 :=
      (iH.const_mul _).add iE
    rw [e, integral_sub i1 iK, integral_add (iH.const_mul _) iE, integral_const_mul]
  rw [hsplit]
  exact weilQuad_ge_endProfile hH

/-- **Pointwise payment**: if the window potential pays the pole capacity everywhere on the open
window, `V_A ≥ 2 sinh(A/2) − A`, then Weil's form is nonnegative on window tests of length `A`. -/
theorem weilQuad_nonneg_of_potential (hH : IsWindowTest A H) (hA : 0 ≤ A)
    (hV : ∀ u ∈ Ioo (-A) 0, 2 * Real.sinh (A / 2) - A ≤ windowPotential A u) :
    0 ≤ weilQuad H := by
  have iH := integrable_sq hH.continuous hH.hasCompactSupport
  have iE := (integral_exitPotential_mul_le hH).1
  have iK := integrable_canonicalDensity_mul hH.continuous hH.hasCompactSupport A
  have iV : Integrable fun u => windowPotential A u * H u ^ 2 := by
    have := ((iH.const_mul (EF.gammaBracket 0)).add iE).sub iK
    refine this.congr (Eventually.of_forall fun u => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, windowPotential]; ring
  -- the window is a.e. its interior
  have hmono : (2 * Real.sinh (A / 2) - A) * ∫ u, H u ^ 2 ≤ ∫ u, windowPotential A u * H u ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono_ae (iH.const_mul _) iV ?_
    have hnull : volume ({-A, 0} : Set ℝ) = 0 := (Set.toFinite _).measure_zero _
    filter_upwards [compl_mem_ae_iff.mpr hnull] with u hu
    by_cases hin : u ∈ Ioo (-A) 0
    · exact mul_le_mul_of_nonneg_right (hV u hin) (sq_nonneg _)
    · have h0 : H u = 0 := by
        refine hH.vanish u fun hm => hin ⟨lt_of_le_of_ne hm.1 fun h => hu ?_,
          lt_of_le_of_ne hm.2 fun h => hu ?_⟩
        · exact Or.inl h.symm
        · exact Or.inr (mem_singleton_iff.mpr h)
      simp [h0]
  have hp := pole_ge hH hA
  have hQ := weilQuad_ge_windowPotential hH
  linarith

end GaloisForLFunctions.WindowTowerOfSpecZ
