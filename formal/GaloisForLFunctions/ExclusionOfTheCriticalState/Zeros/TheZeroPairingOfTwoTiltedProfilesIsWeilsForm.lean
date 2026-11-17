import GaloisForLFunctions.ExclusionOfTheCriticalState.Zeros.TheZeroPairingOfTwoProfilesIsWeilsForm
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheEnergyDomainIsStableUnderLipschitzMultipliers
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.ActualHalfLineLevyEnergy
import GaloisForLFunctions.RHTower.WeilWorkPBAPPacketEnergy

/-!
# The zero pairing of two tilted profiles is Weil's form

If the unit tilts `e^{−u}F` and `e^{−u}G` of two profiles of the energy domain lie in the domain, the
zero pairing converges absolutely and is Weil's bare form
(`hasSum_bareMixedEnergy_of_unitTilts`):

  `Σ_z L F(z) L G(−z) = W(F, G)`.

This removes the bounded support of the second profile in
`hasSum_bareMixedEnergy_of_unitTilt_of_bounded`.

Mechanism. Cut `G` at `−N` with the Lipschitz cutoff `χ_N = max(min(u + N + 1, 1), 0)`; the head
`χ_N G` has bounded support, and the tail `R_N = (1 − χ_N) G` vanishes in every energy as `N → ∞`:
in `L²` and the weighted norm by dominated convergence, and in the Gamma energy through the Lévy form
`archForm f = 2θ'(0) ∫ f² + ∫ ω(x) ∫ (f(u) − f(u + x))²`, since
`|Δ_x(ψ H)| ≤ |Δ_x H| + min(1, x) |H(· + x)|` for the cutoff `ψ = 1 − χ_N` and
`∫ ω(x) min(1, x)² dx < ∞`. The Gamma bracket is at least `log(1 + |t|/4) − 10`, so the logarithmic
energy of the tilted tail, which bounds its reflected zero values, vanishes as well.
-/

noncomputable section
open MeasureTheory Set Filter Complex Topology Zeta23

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory HTGeometry _root_.RHTower

/-! ### The Lipschitz cutoff -/

/-- The cutoff `χ_N(u) = max(min(u + N + 1, 1), 0)`: `1` on `u ≥ −N`, `0` on `u ≤ −N − 1`. -/
def wallCut (N : ℕ) (u : ℝ) : ℝ := max (min (u + (N : ℝ) + 1) 1) 0

theorem wallCut_nonneg (N : ℕ) (u : ℝ) : 0 ≤ wallCut N u := le_max_right _ _

theorem wallCut_le_one (N : ℕ) (u : ℝ) : wallCut N u ≤ 1 :=
  max_le (min_le_right _ _) zero_le_one

theorem wallCut_eq_one {N : ℕ} {u : ℝ} (hu : -(N : ℝ) ≤ u) : wallCut N u = 1 := by
  unfold wallCut
  rw [min_eq_right (by linarith), max_eq_left zero_le_one]

theorem wallCut_eq_zero {N : ℕ} {u : ℝ} (hu : u ≤ -(N : ℝ) - 1) : wallCut N u = 0 := by
  unfold wallCut
  rw [max_eq_right (min_le_of_left_le (by linarith))]

theorem abs_wallCut_sub_le (N : ℕ) (u v : ℝ) : |wallCut N u - wallCut N v| ≤ |u - v| := by
  unfold wallCut
  refine (abs_max_sub_max_le_abs _ _ _).trans ?_
  refine (abs_min_sub_min_le_max _ _ _ _).trans ?_
  rw [sub_self, abs_zero, max_eq_left (abs_nonneg _)]
  exact le_of_eq (by congr 1; ring)

theorem measurable_wallCut (N : ℕ) : Measurable (wallCut N) := by
  unfold wallCut; fun_prop

/-- The tail cutoff `ψ_N = 1 − χ_N`. -/
def wallTail (N : ℕ) (u : ℝ) : ℝ := 1 - wallCut N u

theorem abs_wallTail_le_one (N : ℕ) (u : ℝ) : |wallTail N u| ≤ 1 := by
  unfold wallTail
  rw [abs_le]; constructor <;> linarith [wallCut_nonneg N u, wallCut_le_one N u]

theorem abs_wallTail_sub_le (N : ℕ) (u v : ℝ) :
    |wallTail N u - wallTail N v| ≤ min 1 |u - v| := by
  unfold wallTail
  rw [show 1 - wallCut N u - (1 - wallCut N v) = -(wallCut N u - wallCut N v) by ring, abs_neg]
  refine le_min ?_ (abs_wallCut_sub_le N u v)
  rw [abs_le]; constructor <;> linarith [wallCut_nonneg N u, wallCut_le_one N u,
    wallCut_nonneg N v, wallCut_le_one N v]

theorem wallTail_eq_zero {N : ℕ} {u : ℝ} (hu : -(N : ℝ) ≤ u) : wallTail N u = 0 := by
  unfold wallTail; rw [wallCut_eq_one hu, sub_self]

/-- `ψ_N(u) → 0` for every `u`. -/
theorem eventually_wallTail_eq_zero (u : ℝ) : ∀ᶠ N : ℕ in atTop, wallTail N u = 0 := by
  filter_upwards [eventually_ge_atTop (Nat.ceil (-u))] with N hN
  have h1 := Nat.le_ceil (-u)
  have h2 : (Nat.ceil (-u) : ℝ) ≤ N := by exact_mod_cast hN
  exact wallTail_eq_zero (by linarith)

theorem criticalHalfLineEnergyDomain_wallTail_mul (N : ℕ) {H : ℝ → ℝ}
    (hH : CriticalHalfLineEnergyDomain H) :
    CriticalHalfLineEnergyDomain (fun u => wallTail N u * H u) :=
  criticalHalfLineEnergyDomain_lipschitz_mul hH (measurable_const.sub (measurable_wallCut N))
    (abs_wallTail_le_one N) (Λ := 1) fun u v => by
      rw [one_mul]; exact (abs_wallTail_sub_le N u v).trans (min_le_right _ _)

theorem criticalHalfLineEnergyDomain_wallCut_mul (N : ℕ) {H : ℝ → ℝ}
    (hH : CriticalHalfLineEnergyDomain H) :
    CriticalHalfLineEnergyDomain (fun u => wallCut N u * H u) :=
  criticalHalfLineEnergyDomain_lipschitz_mul hH (measurable_wallCut N)
    (fun u => by rw [abs_of_nonneg (wallCut_nonneg N u)]; exact wallCut_le_one N u) (Λ := 1)
    fun u v => by rw [one_mul]; exact abs_wallCut_sub_le N u v

/-! ### The tail vanishes in every energy -/

/-- `∫ (ψ_N H)² → 0`. -/
theorem tendsto_integral_sq_wallTail {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H) :
    Tendsto (fun N : ℕ => ∫ u, (wallTail N u * H u) ^ 2) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ)) (fun u => H u ^ 2)
    (fun N => ((criticalHalfLineEnergyDomain_wallTail_mul N hH).sq).aestronglyMeasurable) hH.sq
    (fun N => Eventually.of_forall fun u => by
      rw [Real.norm_of_nonneg (sq_nonneg _), mul_pow]
      have h1 : wallTail N u ^ 2 ≤ 1 := by
        rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (abs_wallTail_le_one N u)
      nlinarith [sq_nonneg (H u)])
    (Eventually.of_forall fun u => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_wallTail_eq_zero u] with N hN
      simp [hN])
  simpa using h

/-- `∫ e^{2|t|} (ψ_N H)² → 0`. -/
theorem tendsto_exponentialSourceMass_wallTail {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H) :
    Tendsto (fun N : ℕ => exponentialSourceMass fun u => wallTail N u * H u) atTop (𝓝 0) := by
  have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun t => (Real.exp |t| * H t) ^ 2)
    (fun N => (criticalHalfLineEnergyDomain_wallTail_mul N hH).weighted.sq.aestronglyMeasurable)
    hH.weighted.sq
    (fun N => Eventually.of_forall fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h1 : wallTail N t ^ 2 ≤ 1 := by
        rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (abs_wallTail_le_one N t)
      rw [show (Real.exp |t| * (wallTail N t * H t)) ^ 2 =
        wallTail N t ^ 2 * (Real.exp |t| * H t) ^ 2 by ring]
      nlinarith [sq_nonneg (Real.exp |t| * H t)])
    (Eventually.of_forall fun t => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_wallTail_eq_zero t] with N hN
      simp [hN])
  simpa [exponentialSourceMass] using h

theorem archLevyDensity_nonneg {x : ℝ} (hx : 0 < x) : 0 ≤ archLevyDensity x := by
  unfold archLevyDensity
  exact div_nonneg (Real.exp_pos _).le
    (by have := Real.exp_lt_one_iff.mpr (show -2 * x < 0 by linarith); linarith)

/-- `∫_0^∞ ω(x) min(1, x)² dx < ∞`. -/
theorem integrableOn_archLevyDensity_mul_min_sq :
    IntegrableOn (fun x => archLevyDensity x * min 1 x ^ 2) (Ioi 0) := by
  have hnear : IntegrableOn (fun x => archLevyDensity x * min 1 x ^ 2) (Ioc 0 1) := by
    refine ((continuous_const : Continuous fun _ : ℝ => (3 / 2 : ℝ)).integrableOn_Ioc).mono' ?_ ?_
    · exact ((measurable_archLevyDensity'.mul ((measurable_const.min measurable_id).pow_const 2))
        ).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun x hx => ?_)
      have h0 := hx.1
      have hd := archLevyDensity_le_near h0 hx.2
      rw [min_eq_right hx.2]
      have hpos : 0 ≤ archLevyDensity x := archLevyDensity_nonneg h0
      rw [Real.norm_of_nonneg (mul_nonneg hpos (sq_nonneg _))]
      calc archLevyDensity x * x ^ 2 ≤ 3 / (2 * x) * x ^ 2 :=
            mul_le_mul_of_nonneg_right hd (sq_nonneg _)
        _ = 3 / 2 * x := by field_simp
        _ ≤ 3 / 2 := by linarith [hx.2]
  have hfar : IntegrableOn (fun x => archLevyDensity x * min 1 x ^ 2) (Ioi 1) := by
    refine ((exp_neg_integrableOn_Ioi 1 (by norm_num : (0 : ℝ) < 1 / 2)).const_mul 2).mono' ?_ ?_
    · exact ((measurable_archLevyDensity'.mul ((measurable_const.min measurable_id).pow_const 2))
        ).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => ?_)
      have h1 : (1 : ℝ) ≤ x := le_of_lt hx
      have hd := archLevyDensity_le_far h1
      have hpos : 0 ≤ archLevyDensity x := archLevyDensity_nonneg (by linarith)
      rw [min_eq_left h1, one_pow, mul_one, Real.norm_of_nonneg hpos]
      calc archLevyDensity x ≤ 2 * Real.exp (-(x / 2)) := hd
        _ = 2 * Real.exp (-(1 / 2) * x) := by congr 2; ring
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  exact hnear.union hfar

/-- **The Lévy energy of the tail vanishes.** -/
theorem tendsto_levyEnergy_wallTail {H : ℝ → ℝ} (hH : CriticalHalfLineEnergyDomain H) :
    Tendsto (fun N : ℕ => levyEnergy fun u => wallTail N u * H u) atTop (𝓝 0) := by
  have hI := integrableOn_levyMixedIntegrand hH hH
  have hm := integrableOn_archLevyDensity_mul_min_sq
  set A : ℝ := ∫ u, H u ^ 2
  have hHm := hH.memLp_real
  have hΔ : ∀ x, Integrable fun u => (H u - H (u + x)) * (H u - H (u + x)) := fun x =>
    integrable_mul_of_memLp (hHm.sub (memLp_two_shift hHm x)) (hHm.sub (memLp_two_shift hHm x))
  have hsh : ∀ x, Integrable fun u => H (u + x) ^ 2 := fun x => hH.sq.comp_add_right x
  have hshA : ∀ x, (∫ u, H (u + x) ^ 2) = A := fun x =>
    integral_add_right_eq_self (μ := volume) (fun u => H u ^ 2) x
  -- the pointwise bound on the jumps
  have hpt : ∀ (N : ℕ) (x : ℝ), 0 < x → ∀ u,
      (wallTail N u * H u - wallTail N (u + x) * H (u + x)) ^ 2 ≤
        2 * ((H u - H (u + x)) * (H u - H (u + x))) + 2 * (min 1 x ^ 2 * H (u + x) ^ 2) := by
    intro N x hx u
    have h1 := abs_wallTail_le_one N u
    have h2 := abs_wallTail_sub_le N u (u + x)
    rw [show |u - (u + x)| = x by rw [sub_add_cancel_left, abs_neg, abs_of_pos hx]] at h2
    have e : wallTail N u * H u - wallTail N (u + x) * H (u + x) =
        wallTail N u * (H u - H (u + x)) + (wallTail N u - wallTail N (u + x)) * H (u + x) := by ring
    rw [e]
    have hA2 : (wallTail N u * (H u - H (u + x))) ^ 2 ≤ (H u - H (u + x)) * (H u - H (u + x)) := by
      rw [mul_pow, ← sq]
      have : wallTail N u ^ 2 ≤ 1 := by rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) h1
      nlinarith [sq_nonneg (H u - H (u + x))]
    have hB2 : ((wallTail N u - wallTail N (u + x)) * H (u + x)) ^ 2 ≤ min 1 x ^ 2 * H (u + x) ^ 2 := by
      rw [mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    nlinarith [sq_nonneg (wallTail N u * (H u - H (u + x)) - (wallTail N u - wallTail N (u + x)) * H (u + x))]
  have hfN : ∀ N : ℕ, CriticalHalfLineEnergyDomain fun u => wallTail N u * H u := fun N =>
    criticalHalfLineEnergyDomain_wallTail_mul N hH
  have hjump : ∀ (N : ℕ) x, Integrable fun u =>
      (wallTail N u * H u - wallTail N (u + x) * H (u + x)) ^ 2 := fun N x =>
    integrable_sq_of_memLp ((hfN N).memLp_real.sub (memLp_two_shift (hfN N).memLp_real x))
  -- the inner integral is bounded and vanishes
  have hinner : ∀ (N : ℕ) (x : ℝ), 0 < x →
      ∫ u, (wallTail N u * H u - wallTail N (u + x) * H (u + x)) ^ 2 ≤
        2 * (∫ u, (H u - H (u + x)) * (H u - H (u + x))) + 2 * (min 1 x ^ 2 * A) := by
    intro N x hx
    rw [← hshA x, ← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add ((hΔ x).const_mul _) (((hsh x).const_mul _).const_mul _)]
    refine integral_mono (hjump N x) (((hΔ x).const_mul _).add (((hsh x).const_mul _).const_mul _))
      fun u => ?_
    simpa only [mul_assoc] using hpt N x hx u
  have hlim : ∀ x : ℝ, 0 < x → Tendsto (fun N : ℕ =>
      ∫ u, (wallTail N u * H u - wallTail N (u + x) * H (u + x)) ^ 2) atTop (𝓝 0) := by
    intro x hx
    have h := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
      (fun u => 2 * ((H u - H (u + x)) * (H u - H (u + x))) + 2 * (min 1 x ^ 2 * H (u + x) ^ 2))
      (fun N => (hjump N x).aestronglyMeasurable)
      (((hΔ x).const_mul _).add (((hsh x).const_mul _).const_mul _))
      (fun N => Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact hpt N x hx u)
      (Eventually.of_forall fun u => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_wallTail_eq_zero u, eventually_wallTail_eq_zero (u + x)]
          with N h1 h2
        simp [h1, h2])
    simpa using h
  -- the outer integral
  unfold levyEnergy
  have hbound : IntegrableOn (fun x => 2 * (archLevyDensity x *
      ∫ u, (H u - H (u + x)) * (H u - H (u + x))) + 2 * A * (archLevyDensity x * min 1 x ^ 2))
      (Ioi 0) := (hI.const_mul 2).add (hm.const_mul (2 * A))
  have h := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioi 0))
    (F := fun (N : ℕ) x => archLevyDensity x *
      ∫ u, (wallTail N u * H u - wallTail N (u + x) * H (u + x)) ^ 2) (f := fun _ => (0 : ℝ))
    (fun x => 2 * (archLevyDensity x * ∫ u, (H u - H (u + x)) * (H u - H (u + x))) +
      2 * A * (archLevyDensity x * min 1 x ^ 2))
    (fun N => ((integrableOn_levyMixedIntegrand (hfN N) (hfN N)).congr_fun (fun x _ => by
      simp only [sq]) measurableSet_Ioi).aestronglyMeasurable)
    hbound
    (fun N => (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => by
      have hω := archLevyDensity_nonneg (show 0 < x from hx)
      rw [Real.norm_of_nonneg (mul_nonneg hω (integral_nonneg fun u => sq_nonneg _))]
      calc archLevyDensity x * ∫ u, (wallTail N u * H u - wallTail N (u + x) * H (u + x)) ^ 2
          ≤ archLevyDensity x * (2 * (∫ u, (H u - H (u + x)) * (H u - H (u + x))) +
              2 * (min 1 x ^ 2 * A)) := mul_le_mul_of_nonneg_left (hinner N x hx) hω
        _ = _ := by ring))
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => by
      simpa using (hlim x hx).const_mul (archLevyDensity x)))
  simpa using h

/-! ### The Gamma energy and the logarithmic energy -/

theorem integral_norm_sq_paperFT_cx_eq {f : ℝ → ℝ} (hf : CriticalHalfLineEnergyDomain f) :
    ∫ r : ℝ, ‖paperFT (cx f) r‖ ^ 2 = 2 * Real.pi * ∫ u, f u ^ 2 := by
  have hpl := KernelStrip.integral_norm_sq_paperFT_of_memLp (hf.integrable.ofReal (𝕜 := ℂ))
    (memLp_cx_of_sq hf.integrable hf.sq)
  have hpl' : (∫ r : ℝ, ‖paperFT (cx f) r‖ ^ 2) =
      2 * Real.pi * ∫ u : ℝ, ‖((f u : ℝ) : ℂ)‖ ^ 2 := hpl
  rw [hpl']
  congr 1
  exact integral_congr_ae (Eventually.of_forall fun u => by
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs])

theorem neg_ten_le_gammaBracket (t : ℝ) : -10 ≤ EF.gammaBracket t := by
  have h := WeilWorkPBAP.gammaBracket_lower t
  have h0 : 0 ≤ Real.log (1 + |t| / 4) := Real.log_nonneg (by have := abs_nonneg t; linarith)
  linarith

/-- The Gamma energy of a profile of the domain is controlled by its `L²` mass and Lévy energy. -/
theorem integral_norm_sq_paperFT_mul_abs_gammaBracket_le {f : ℝ → ℝ}
    (hf : CriticalHalfLineEnergyDomain f) :
    ∫ r : ℝ, ‖paperFT (cx f) r‖ ^ 2 * |EF.gammaBracket r| ≤
      2 * Real.pi * (2 * |gammaHardyPhaseRate 0| * (∫ u, f u ^ 2) + levyEnergy f) +
        20 * (2 * Real.pi * ∫ u, f u ^ 2) := by
  have hX := integrable_norm_sq_paperFT_cx hf.integrable hf.sq
  have hlev := hf.archForm_eq_levyEnergy
  have harch : (∫ r : ℝ, ‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r) = 2 * Real.pi * archForm f := by
    unfold archForm
    field_simp
    rfl
  have hmono : ∫ r : ℝ, ‖paperFT (cx f) r‖ ^ 2 * |EF.gammaBracket r| ≤
      ∫ r : ℝ, (‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r + 20 * ‖paperFT (cx f) r‖ ^ 2) := by
    refine integral_mono (hf.gamma.norm.congr (Eventually.of_forall fun r => ?_))
      (hf.gamma.add (hX.const_mul 20)) fun r => ?_
    · simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖paperFT (cx f) (r : ℂ)‖)]
    · have h10 := neg_ten_le_gammaBracket r
      have hX0 := sq_nonneg ‖paperFT (cx f) (r : ℂ)‖
      show ‖paperFT (cx f) r‖ ^ 2 * |EF.gammaBracket r| ≤
        ‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r + 20 * ‖paperFT (cx f) r‖ ^ 2
      rcases le_or_gt 0 (EF.gammaBracket r) with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_neg h]; nlinarith
  rw [integral_add hf.gamma (hX.const_mul 20), integral_const_mul, harch, hlev,
    integral_norm_sq_paperFT_cx_eq hf] at hmono
  have hθ : 2 * gammaHardyPhaseRate 0 * (∫ u, f u ^ 2) ≤ 2 * |gammaHardyPhaseRate 0| * ∫ u, f u ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self (gammaHardyPhaseRate 0)])
      (integral_nonneg fun u => sq_nonneg _)
  nlinarith [Real.pi_pos]

/-- The logarithmic energy, which bounds the zero values, is controlled the same way. -/
theorem integral_log_mul_norm_sq_paperFT_le {f : ℝ → ℝ} (hf : CriticalHalfLineEnergyDomain f) :
    ∫ t : ℝ, (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) * ‖paperFT (cx f) t‖ ^ 2 ≤
      2 * Real.pi * (2 * |gammaHardyPhaseRate 0| * (∫ u, f u ^ 2) + levyEnergy f) +
        (|xiLineTwoLogDerivConstant| + 10 + Real.log 4) * (2 * Real.pi * ∫ u, f u ^ 2) := by
  have hX := integrable_norm_sq_paperFT_cx hf.integrable hf.sq
  have hlev := hf.archForm_eq_levyEnergy
  have harch : (∫ r : ℝ, ‖paperFT (cx f) r‖ ^ 2 * EF.gammaBracket r) = 2 * Real.pi * archForm f := by
    unfold archForm
    field_simp
    rfl
  have hmono : ∫ t : ℝ, (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) * ‖paperFT (cx f) t‖ ^ 2 ≤
      ∫ t : ℝ, (‖paperFT (cx f) t‖ ^ 2 * EF.gammaBracket t +
        (|xiLineTwoLogDerivConstant| + 10 + Real.log 4) * ‖paperFT (cx f) t‖ ^ 2) := by
    refine integral_mono (integrable_log_mul_norm_sq_paperFT hf) (hf.gamma.add (hX.const_mul _))
      fun t => ?_
    have hlog : Real.log (|t| + 4) ≤ Real.log 4 + EF.gammaBracket t + 10 := by
      have h := WeilWorkPBAP.gammaBracket_lower t
      rw [show |t| + 4 = 4 * (1 + |t| / 4) by ring, Real.log_mul (by norm_num)
        (by have := abs_nonneg t; positivity)]
      linarith
    have hX0 := sq_nonneg ‖paperFT (cx f) (t : ℂ)‖
    show (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) * ‖paperFT (cx f) t‖ ^ 2 ≤
      ‖paperFT (cx f) t‖ ^ 2 * EF.gammaBracket t +
        (|xiLineTwoLogDerivConstant| + 10 + Real.log 4) * ‖paperFT (cx f) t‖ ^ 2
    nlinarith [le_abs_self xiLineTwoLogDerivConstant]
  rw [integral_add hf.gamma (hX.const_mul _), integral_const_mul, harch, hlev,
    integral_norm_sq_paperFT_cx_eq hf] at hmono
  have hθ : 2 * gammaHardyPhaseRate 0 * (∫ u, f u ^ 2) ≤ 2 * |gammaHardyPhaseRate 0| * ∫ u, f u ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith [le_abs_self (gammaHardyPhaseRate 0)])
      (integral_nonneg fun u => sq_nonneg _)
  nlinarith [Real.pi_pos]

/-- The reflected zero values are controlled by the logarithmic energy of the unit tilt. -/
theorem tsum_norm_sq_laplace_neg_le {D : ℝ → ℝ}
    (hD1 : CriticalHalfLineEnergyDomain fun u => Real.exp (-(1 * u)) * D u) :
    ∑' q : XiZeroCopy, ‖negativeHalfLineLaplace (cx D) (-centredZero q)‖ ^ 2 ≤
      16 / Real.pi * ∫ t : ℝ, (xiLineTwoLogDerivConstant + Real.log (|t| + 4)) *
        ‖paperFT (cx fun u => Real.exp (-(1 * u)) * D u) (t : ℂ)‖ ^ 2 := by
  have h := tsum_norm_sq_laplace_zeros_le hD1 (ε := -1) (Or.inr rfl)
    (fun q => -centredZero q + ((1 : ℝ) : ℂ))
    (fun q => by
      have := abs_lt.mp (abs_re_centredZero_lt q)
      rw [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
      linarith [this.2])
    (fun q => by
      have := abs_lt.mp (abs_re_centredZero_lt q)
      rw [Complex.add_re, Complex.neg_re, Complex.ofReal_re]
      linarith [this.1])
    (fun q => by
      rw [Complex.add_im, Complex.neg_im, Complex.ofReal_im, add_zero, im_centredZero,
        neg_one_mul])
  refine le_of_eq_of_le (tsum_congr fun q => ?_) h
  rw [laplace_eq_laplace_exp_mul D 1 (-centredZero q)]

/-! ### The zero pairing -/

/-- **The zero pairing of two tilted profiles is Weil's form.** If the unit tilts of `F` and `G` lie
in the energy domain, then `Σ_z L F(z) L G(−z) = W(F, G)`, absolutely convergent. -/
theorem hasSum_bareMixedEnergy_of_unitTilts {F G : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F)
    (hF1 : CriticalHalfLineEnergyDomain (fun u => Real.exp (-(1 * u)) * F u))
    (hG : CriticalHalfLineEnergyDomain G)
    (hG1 : CriticalHalfLineEnergyDomain (fun u => Real.exp (-(1 * u)) * G u)) :
    HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
      negativeHalfLineLaplace (cx G) (-centredZero q)) ((bareMixedEnergy F G : ℝ) : ℂ) := by
  have hA := summable_norm_sq_laplace_centredZero hF1
  have hB := summable_norm_sq_laplace_neg_centredZero hG1
  have hHead : ∀ N : ℕ, CriticalHalfLineEnergyDomain fun u => wallCut N u * G u := fun N =>
    criticalHalfLineEnergyDomain_wallCut_mul N hG
  have hTail : ∀ N : ℕ, CriticalHalfLineEnergyDomain fun u => wallTail N u * G u := fun N =>
    criticalHalfLineEnergyDomain_wallTail_mul N hG
  have hTilt : ∀ N : ℕ, (fun u => Real.exp (-(1 * u)) * (wallTail N u * G u)) =
      fun u => wallTail N u * (Real.exp (-(1 * u)) * G u) := fun N => by funext u; ring
  have hTail1 : ∀ N : ℕ, CriticalHalfLineEnergyDomain
      fun u => Real.exp (-(1 * u)) * (wallTail N u * G u) := fun N => by
    rw [hTilt N]; exact criticalHalfLineEnergyDomain_wallTail_mul N hG1
  have hTB : ∀ N : ℕ, Summable fun q : XiZeroCopy =>
      ‖negativeHalfLineLaplace (cx fun u => wallTail N u * G u) (-centredZero q)‖ ^ 2 := fun N =>
    summable_norm_sq_laplace_neg_centredZero (hTail1 N)
  have hsplit : ∀ N : ℕ, (fun u => wallCut N u * G u + wallTail N u * G u) = G := fun N => by
    funext u; simp only [wallTail]; ring
  have hHeadSum : ∀ N : ℕ, HasSum (fun q : XiZeroCopy =>
      negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx fun u => wallCut N u * G u) (-centredZero q))
      ((bareMixedEnergy F (fun u => wallCut N u * G u) : ℝ) : ℂ) := fun N =>
    hasSum_bareMixedEnergy_of_unitTilt_of_bounded hF hF1 (hHead N) (T := (N : ℝ) + 1)
      fun u hu => by rw [wallCut_eq_zero (by linarith), zero_mul]
  have hLadd : ∀ (N : ℕ) (q : XiZeroCopy), negativeHalfLineLaplace (cx G) (-centredZero q) =
      negativeHalfLineLaplace (cx fun u => wallCut N u * G u) (-centredZero q) +
        negativeHalfLineLaplace (cx fun u => wallTail N u * G u) (-centredZero q) := by
    intro N q
    have hre : (centredZero q).re < 4 := by
      linarith [(abs_lt.mp (abs_re_centredZero_lt q)).2]
    unfold negativeHalfLineLaplace
    rw [← integral_add (integrable_cexp_neg_mul_cx (hHead N) hre)
      (integrable_cexp_neg_mul_cx (hTail N) hre)]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [cx, wallTail]
    push_cast
    ring
  set S := ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
    negativeHalfLineLaplace (cx G) (-centredZero q)
  have hconst : ∀ N : ℕ, S - ((bareMixedEnergy F G : ℝ) : ℂ) =
      (∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx fun u => wallTail N u * G u) (-centredZero q)) -
        ((bareMixedEnergy F (fun u => wallTail N u * G u) : ℝ) : ℂ) := by
    intro N
    have hsT := (summable_mul_and_norm_tsum_le hA (hTB N)).1
    have hadd := bareMixedEnergy_add_right hF (hHead N) (hTail N)
    rw [hsplit N] at hadd
    have hS : S = ((bareMixedEnergy F (fun u => wallCut N u * G u) : ℝ) : ℂ) +
        ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx fun u => wallTail N u * G u) (-centredZero q) := by
      rw [← (hHeadSum N).tsum_eq, ← (hHeadSum N).summable.tsum_add hsT]
      exact tsum_congr fun q => by rw [hLadd N q]; ring
    rw [hS, hadd]
    push_cast
    ring
  -- the tail vanishes in every energy
  have hlevG := tendsto_levyEnergy_wallTail hG
  have hL2G := tendsto_integral_sq_wallTail hG
  have hlevG1 := tendsto_levyEnergy_wallTail hG1
  have hL2G1 := tendsto_integral_sq_wallTail hG1
  have hE := tendsto_exponentialSourceMass_wallTail hG
  set θ := |gammaHardyPhaseRate 0|
  set K := |xiLineTwoLogDerivConstant| + 10 + Real.log 4
  have hΓbound : Tendsto (fun N : ℕ => 2 * Real.pi * (2 * θ * (∫ u, (wallTail N u * G u) ^ 2) +
      levyEnergy (fun u => wallTail N u * G u)) +
        20 * (2 * Real.pi * ∫ u, (wallTail N u * G u) ^ 2)) atTop (𝓝 0) := by
    have h := (((hL2G.const_mul (2 * θ)).add hlevG).const_mul (2 * Real.pi)).add
      ((hL2G.const_mul (2 * Real.pi)).const_mul 20)
    simp only [mul_zero, add_zero] at h
    exact h
  have hΓ : Tendsto (fun N : ℕ => ∫ r : ℝ, ‖paperFT (cx fun u => wallTail N u * G u) r‖ ^ 2 *
      |EF.gammaBracket r|) atTop (𝓝 0) :=
    squeeze_zero (fun N => integral_nonneg fun r => mul_nonneg (sq_nonneg _) (abs_nonneg _))
      (fun N => integral_norm_sq_paperFT_mul_abs_gammaBracket_le (hTail N)) hΓbound
  have hlogbound : Tendsto (fun N : ℕ => 2 * Real.pi * (2 * θ *
      (∫ u, (wallTail N u * (Real.exp (-(1 * u)) * G u)) ^ 2) +
      levyEnergy (fun u => wallTail N u * (Real.exp (-(1 * u)) * G u))) +
        K * (2 * Real.pi * ∫ u, (wallTail N u * (Real.exp (-(1 * u)) * G u)) ^ 2)) atTop (𝓝 0) := by
    have h := (((hL2G1.const_mul (2 * θ)).add hlevG1).const_mul (2 * Real.pi)).add
      ((hL2G1.const_mul (2 * Real.pi)).const_mul K)
    simp only [mul_zero, add_zero] at h
    exact h
  have hzero : Tendsto (fun N : ℕ => ∑' q : XiZeroCopy,
      ‖negativeHalfLineLaplace (cx fun u => wallTail N u * G u) (-centredZero q)‖ ^ 2)
      atTop (𝓝 0) := by
    have hlb := hlogbound.const_mul (16 / Real.pi)
    rw [mul_zero] at hlb
    refine squeeze_zero (fun N => tsum_nonneg fun q => sq_nonneg _) (fun N => ?_) hlb
    refine (tsum_norm_sq_laplace_neg_le (hTail1 N)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hTilt N]
    exact integral_log_mul_norm_sq_paperFT_le (criticalHalfLineEnergyDomain_wallTail_mul N hG1)
  set cF := Real.sqrt (∫ r : ℝ, ‖paperFT (cx F) r‖ ^ 2 * |EF.gammaBracket r|)
  set eF := Real.sqrt (exponentialSourceMass F)
  set J := Real.sqrt (∫ u, Real.exp (-|u|))
  set A := Real.sqrt (∑' q : XiZeroCopy, ‖negativeHalfLineLaplace (cx F) (centredZero q)‖ ^ 2)
  set mF := |coshHalfMoment F| + |sinhHalfMoment F|
  have hsq0 : ∀ {f : ℕ → ℝ}, Tendsto f atTop (𝓝 0) → Tendsto (fun n => Real.sqrt (f n)) atTop (𝓝 0) :=
    fun {f} hf => by
      have h := (Real.continuous_sqrt.tendsto 0).comp hf
      rw [Real.sqrt_zero] at h
      exact h
  have hbound : Tendsto (fun N : ℕ => A * Real.sqrt (∑' q : XiZeroCopy,
      ‖negativeHalfLineLaplace (cx fun u => wallTail N u * G u) (-centredZero q)‖ ^ 2) +
      ((2 * Real.pi)⁻¹ * (cF * Real.sqrt (∫ r : ℝ,
        ‖paperFT (cx fun u => wallTail N u * G u) r‖ ^ 2 * |EF.gammaBracket r|)) +
      2 * vonMangoldtThreeHalvesMass *
        (eF * Real.sqrt (exponentialSourceMass fun u => wallTail N u * G u)) +
      2 * mF * (Real.sqrt (exponentialSourceMass fun u => wallTail N u * G u) * J)))
      atTop (𝓝 0) := by
    have h1 := (hsq0 hzero).const_mul A
    have h2 := ((hsq0 hΓ).const_mul cF).const_mul (2 * Real.pi)⁻¹
    have h3 := ((hsq0 hE).const_mul eF).const_mul (2 * vonMangoldtThreeHalvesMass)
    have h4 := ((hsq0 hE).mul_const J).const_mul (2 * mF)
    have h := h1.add ((h2.add h3).add h4)
    simp only [mul_zero, zero_mul, add_zero] at h
    exact h
  have hlim : Tendsto (fun N : ℕ => (∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
      negativeHalfLineLaplace (cx fun u => wallTail N u * G u) (-centredZero q)) -
      ((bareMixedEnergy F (fun u => wallTail N u * G u) : ℝ) : ℂ)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) hbound
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact (summable_mul_and_norm_tsum_le hA (hTB N)).2
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_bareMixedEnergy_le hF (hTail N)
  have hz : S - ((bareMixedEnergy F G : ℝ) : ℂ) = 0 :=
    tendsto_nhds_unique tendsto_const_nhds (hlim.congr fun N => (hconst N).symm)
  rw [← sub_eq_zero.mp hz]
  exact (summable_mul_and_norm_tsum_le hA hB).1.hasSum

end GaloisForLFunctions.ExclusionOfTheCriticalState
