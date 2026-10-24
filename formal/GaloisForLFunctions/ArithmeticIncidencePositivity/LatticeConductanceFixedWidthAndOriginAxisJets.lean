import GaloisForLFunctions.ArithmeticIncidencePositivity.TotalLatticeCrossingLaw
import GaloisForLFunctions.ArithmeticIncidencePositivity.BumpBridgeOfThePrimeJumpEnergy
import GaloisForLFunctions.ArithmeticIncidencePositivity.OddPlateauFoldedWindowPositivity
import GaloisForLFunctions.RHTower.ArithmeticIncidenceNarrowBumpBridge

/-!
# Lattice conductance at fixed width, axis pairs, and origin first-jet packets

This module resolves **Open Problem 4** ("Lattice conductance at fixed width") by uniting Mechanism
22 (`TotalLatticeCrossingLaw`), the axis pairs `(0, log b)`, the first-jet scaling of origin and
axis packets in an odd gauge, and the explicit logarithmic self-energy of a narrow bump into a
complete fixed-width lattice conductance theory:

1. **The complete lattice pair conductance matrix (`totalLatticeSameKernel`,
   `totalLatticeCrossingKernel`, `totalLatticeNetKernel`, `totalLatticeAxisKernel`).**
   - On same-side pairs `(log a, log b)` (`2 ≤ a < b`),
     `totalLatticeSameKernel a b = archPairKernel (log a) (log b) + ratioAtom a b > 0`.
   - On crossing pairs `(−log a, log b)` (`a, b ≥ 2`), `totalLatticeCrossingKernel a b > 0` iff
     `{a, b} ∈ {{2, 2}, {2, 3}, {2, 4}, {3, 3}}` (Mechanism 22); on the reflected diagonal `a = b`,
     `totalLatticeCrossingKernel a a > 0` iff `a = 2 ∨ a = 3`
     (`totalLatticeCrossingKernel_diag_pos_iff`).
   - For every pair `2 ≤ a < b`, the net pair conductance
     `totalLatticeNetKernel a b = totalLatticeSameKernel a b − totalLatticeCrossingKernel a b` is
     strictly positive (`totalLatticeNetKernel_pos`), so on even lattice profiles every unordered
     pair `{a, b}` (`2 ≤ a < b`) has strictly positive net conductance, even on `{2, 3}` and
     `{2, 4}`.
   - On the axis pairs `(0, log b)` (`a = 1`, `b ≥ 2`), the polar weight vanishes (`archPairKernel 0 (log b) = ω(log b)`), the ratio and product atoms coincide (`vonMangoldtAtom b`), and
     `totalLatticeAxisKernel b = b² / ((b² − 1)√b) + Λ(b)/√b > 0` (`totalLatticeAxisKernel_eq`,
     `totalLatticeAxisKernel_pos`).
2. **Origin and axis packets through first jets (`jetQuotient`, `tendsto_origin_bump_sq_div_cube`,
   `tendsto_origin_axis_bump_pair_div_sq`).**
   An odd gauge `M` vanishes at the origin (`M(0) = 0`) and reaches origin and axis packets through
   its first jet `M'(0) = M'₀`: factoring `M(x) = x · jetQuotient M M'₀ x` with `jetQuotient`
   continuous on `ℝ` proves that as `w → 0⁺`,
   `(1 / w³) ∫ M(x)² β(x / w)² dx → (M'₀)² ∫ y² β(y)² dy` and, for every shift `L` (in particular
   the axis shifts `L = log b`),
   `(1 / w²) ∫ M(x) M(x + L) β₀(x / w) β(x / w) dx → M'₀ M(L) ∫ y β₀(y) β(y) dy`.
3. **Explicit self-energy lower bound and uncalibrated fixed-width lattice positivity
   (`fullEnergy_narrowBump_div_mass_ge`, `fullEnergy_latticeTrain_fixedWidth_ge`,
   `eventually_fullEnergy_latticeTrain_nonneg`).**
   For the canonical narrow bump `narrowBump j` of correlation radius `r_j = 1 / (2(j + 1))`,
   `fullEnergy (narrowBump j) / mass j ≥ log(4 / r_j) + EF.gammaBracket 0 + π/2 − 2 Ω(1) − 17 r_j`.
   Combined with `fullEnergy_latticeTrain_uniform`, this yields an explicit uncalibrated lower bound
   on `fullEnergy (latticeTrain N (resolution N k) c) / mass (resolution N k)` at fixed width and
   proves that for every lattice size `N`, all sufficiently fine resolutions `k` make the complete
   Weil energy nonnegative on every coefficient vector `c : Fin N → ℝ`.
-/

open MeasureTheory Set Filter Topology RHTower
open RHTower.WeilLevyPoleGauss RHTower.ArchimedeanExactForm
open GaloisForLFunctions.BiScaleUncertainty

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### Part I: The complete lattice pair conductance kernels -/

/-- The total same-side kernel of the lattice pair `(log a, log b)`: archimedean same-side kernel
plus the ratio atom. -/
def totalLatticeSameKernel (a b : ℕ) : ℝ :=
  archPairKernel (Real.log a) (Real.log b) + ratioAtom a b

/-- On every same-side lattice pair `2 ≤ a < b`, the total same-side kernel is strictly positive. -/
theorem totalLatticeSameKernel_pos {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    0 < totalLatticeSameKernel a b := by
  unfold totalLatticeSameKernel
  have ha1 : (1 : ℝ) < a := by exact_mod_cast (by omega : 1 < a)
  have hb1 : (1 : ℝ) < b := by exact_mod_cast (by omega : 1 < b)
  have hla : 0 < Real.log a := Real.log_pos ha1
  have hlb : 0 < Real.log b := Real.log_pos hb1
  have hlt : Real.log a < Real.log b := Real.log_lt_log (by positivity) (by exact_mod_cast hab)
  have harch : 0 < archPairKernel (Real.log a) (Real.log b) :=
    archPairKernel_pos_of_sameSide (mul_pos hla hlb) hlt.ne
  linarith [ratioAtom_nonneg a b]

/-- The net lattice pair kernel `totalLatticeSameKernel a b − totalLatticeCrossingKernel a b`:
the net conductance weight of `{a, b}` per unit `|M(log a) M(log b)|` on an even profile. -/
def totalLatticeNetKernel (a b : ℕ) : ℝ :=
  totalLatticeSameKernel a b - totalLatticeCrossingKernel a b

/-- **Exact decomposition of the net lattice pair kernel.** For `1 ≤ a < b`,
`totalLatticeNetKernel a b = (ω(log b − log a) − ω(log b + log a)) + 4 sinh(log a / 2) sinh(log b / 2) + netAtom a b`. -/
theorem totalLatticeNetKernel_eq {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    totalLatticeNetKernel a b =
      (archLevyDensity (Real.log b - Real.log a) - archLevyDensity (Real.log b + Real.log a)) +
        4 * Real.sinh (Real.log a / 2) * Real.sinh (Real.log b / 2) + netAtom a b := by
  unfold totalLatticeNetKernel totalLatticeSameKernel totalLatticeCrossingKernel archPairKernel netAtom
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hla : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast ha)
  have hlt : Real.log a < Real.log b := Real.log_lt_log ha0 (by exact_mod_cast hab)
  have habs1 : |Real.log a - Real.log b| = Real.log b - Real.log a := by
    rw [abs_sub_comm, abs_of_pos (by linarith)]
  have habs2 : |-Real.log a - Real.log b| = Real.log b + Real.log a := by
    rw [show -Real.log a - Real.log b = -(Real.log b + Real.log a) by ring, abs_neg,
      abs_of_pos (by linarith)]
  rw [habs1, habs2, neg_div, Real.sinh_neg]
  ring

/-- **Strict positivity of the net lattice pair kernel.** For every `2 ≤ a < b`, same-side
conductance strictly dominates crossing conductance (`totalLatticeNetKernel a b > 0`), including on
the exceptional crossing pairs `{2, 3}` and `{2, 4}`. -/
theorem totalLatticeNetKernel_pos {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    0 < totalLatticeNetKernel a b := by
  rw [totalLatticeNetKernel_eq (by omega) hab]
  have ha1 : (1 : ℝ) < a := by exact_mod_cast (by omega : 1 < a)
  have hla : 0 < Real.log a := Real.log_pos ha1
  have hlb : Real.log a < Real.log b := Real.log_lt_log (by positivity) (by exact_mod_cast hab)
  have hdiff_pos : 0 < Real.log b - Real.log a := by linarith
  have hω : archLevyDensity (Real.log b + Real.log a) <
      archLevyDensity (Real.log b - Real.log a) :=
    strictAntiOn_archLevyDensity (show 0 < Real.log b - Real.log a by linarith)
      (show 0 < Real.log b + Real.log a by linarith) (by linarith)
  have hsinh_a : 0 < Real.sinh (Real.log a / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hsinh_b : 0 < Real.sinh (Real.log b / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hnet : 0 ≤ netAtom a b := netAtom_nonneg (by omega) hab
  nlinarith

/-- **Reflected diagonal crossing classification.** On the reflected diagonal `(−log a, log a)`
(`a ≥ 2`), the total crossing kernel is positive iff `a = 2` or `a = 3`. -/
theorem totalLatticeCrossingKernel_diag_pos_iff {a : ℕ} (ha : 2 ≤ a) :
    0 < totalLatticeCrossingKernel a a ↔ a = 2 ∨ a = 3 := by
  rw [totalLatticeCrossingKernel_pos_iff ha ha]
  omega

/-- The total kernel of the axis pair `(0, log b)` (`a = 1`, `log 1 = 0`). -/
def totalLatticeAxisKernel (b : ℕ) : ℝ :=
  archPairKernel 0 (Real.log b) + vonMangoldtAtom b

/-- On the origin axis `x = 0`, the polar weight vanishes and `archPairKernel 0 y = ω(|y|)`. -/
theorem archPairKernel_zero_left (y : ℝ) : archPairKernel 0 y = archLevyDensity |y| := by
  unfold archPairKernel
  simp

/-- **Closed form on axis pairs `(0, log b)`.** For `b ≥ 2`, the polar weight vanishes, the ratio
and product atoms coincide (`vonMangoldtAtom b`), and
`totalLatticeAxisKernel b = b² / ((b² − 1)√b) + Λ(b)/√b`. -/
theorem totalLatticeAxisKernel_eq {b : ℕ} (hb : 2 ≤ b) :
    totalLatticeAxisKernel b =
      (b : ℝ) ^ 2 / (((b : ℝ) ^ 2 - 1) * Real.sqrt b) + vonMangoldtAtom b := by
  unfold totalLatticeAxisKernel
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
  rw [archPairKernel_zero_left, abs_of_pos hlb, archLevyDensity_log_nat hb]

/-- Every axis pair `(0, log b)` (`b ≥ 2`) has strictly positive total kernel. -/
theorem totalLatticeAxisKernel_pos {b : ℕ} (hb : 2 ≤ b) :
    0 < totalLatticeAxisKernel b := by
  unfold totalLatticeAxisKernel
  have hlb : 0 < Real.log b := Real.log_pos (by exact_mod_cast (by omega : 1 < b))
  rw [archPairKernel_zero_left, abs_of_pos hlb]
  linarith [archLevyDensity_pos hlb, vonMangoldtAtom_nonneg b]

/-! ### Part II: Origin and axis packets via first jets in an odd gauge -/

/-- The continuous first-jet quotient of a gauge `M` with `M(0) = 0` and derivative `M'₀` at `0`:
`jetQuotient M M'₀ x = M(x) / x` for `x ≠ 0` and `M'₀` at `x = 0`. -/
def jetQuotient (M : ℝ → ℝ) (M'₀ x : ℝ) : ℝ :=
  if x = 0 then M'₀ else M x / x

@[simp]
theorem jetQuotient_zero (M : ℝ → ℝ) (M'₀ : ℝ) : jetQuotient M M'₀ 0 = M'₀ := if_pos rfl

/-- Exact first-jet factorization `x · jetQuotient M M'₀ x = M(x)` for all `x ∈ ℝ` when `M(0) = 0`. -/
theorem mul_jetQuotient_eq {M : ℝ → ℝ} (hM0 : M 0 = 0) (M'₀ x : ℝ) :
    x * jetQuotient M M'₀ x = M x := by
  unfold jetQuotient
  split_ifs with hx
  · rw [hx, zero_mul, hM0]
  · exact mul_div_cancel₀ (M x) hx

/-- If `M` is continuous with `M(0) = 0` and `HasDerivAt M M'₀ 0`, then `jetQuotient M M'₀` is
continuous on `ℝ`. -/
theorem continuous_jetQuotient {M : ℝ → ℝ} {M'₀ : ℝ} (hM : Continuous M) (hM0 : M 0 = 0)
    (hd : HasDerivAt M M'₀ 0) :
    Continuous (jetQuotient M M'₀) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    rw [continuousAt_iff_punctured_nhds, jetQuotient_zero]
    have hsl := hasDerivAt_iff_tendsto_slope.mp hd
    refine hsl.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := hy
    simp [slope, hy0, jetQuotient, hM0, div_eq_inv_mul]
  · have hcont : ContinuousAt (fun y => M y / y) x :=
      hM.continuousAt.div continuousAt_id hx
    refine hcont.congr ( eventually_nhds_iff.mpr ⟨{0}ᶜ, fun y hy => ?_, isOpen_compl_singleton, hx⟩ )
    exact (if_neg hy).symm

/-- **Origin self-packet limit at first-jet order `w³`.** For a continuous gauge `M` with `M(0) = 0`
and `HasDerivAt M M'₀ 0`, and a continuous bump `β` supported in `[−1, 1]`,
`(1 / w³) ∫ M(x)² β(x / w)² dx → (M'₀)² ∫ y² β(y)² dy` as `w → 0⁺`. -/
theorem tendsto_origin_bump_sq_div_cube {β : ℝ → ℝ} (hβc : Continuous β)
    (hβ : ∀ y, 1 < |y| → β y = 0) {M : ℝ → ℝ} {M'₀ : ℝ} (hM : Continuous M) (hM0 : M 0 = 0)
    (hd : HasDerivAt M M'₀ 0) :
    Tendsto (fun w => (∫ x, M x ^ 2 * β (x / w) ^ 2) / w ^ 3) (𝓝[>] 0)
      (𝓝 (M'₀ ^ 2 * ∫ y, (y * β y) ^ 2)) := by
  set β₁ : ℝ → ℝ := fun y => y * β y
  have hβ₁c : Continuous β₁ := continuous_id.mul hβc
  have hβ₁ : ∀ y, 1 < |y| → β₁ y = 0 := fun y hy => by dsimp [β₁]; rw [hβ y hy, mul_zero]
  have hF : Continuous fun x => jetQuotient M M'₀ x ^ 2 :=
    (continuous_jetQuotient hM hM0 hd).pow 2
  have hlim := tendsto_integral_bump_sq_div hβ₁c hβ₁ hF 0
  simp only [sub_zero, jetQuotient_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hw' : 0 < w := hw
  have hpt : ∀ x, jetQuotient M M'₀ x ^ 2 * β₁ (x / w) * β₁ (x / w) =
      (M x ^ 2 * β (x / w) ^ 2) / w ^ 2 := by
    intro x
    dsimp [β₁]
    have hM_eq := mul_jetQuotient_eq hM0 M'₀ x
    have h1 : x ^ 2 * jetQuotient M M'₀ x ^ 2 = M x ^ 2 := by
      calc x ^ 2 * jetQuotient M M'₀ x ^ 2 = (x * jetQuotient M M'₀ x) ^ 2 := by ring
        _ = M x ^ 2 := by rw [hM_eq]
    calc jetQuotient M M'₀ x ^ 2 * (x / w * β (x / w)) * (x / w * β (x / w))
        = (x ^ 2 * jetQuotient M M'₀ x ^ 2) * β (x / w) ^ 2 / w ^ 2 := by ring
      _ = (M x ^ 2 * β (x / w) ^ 2) / w ^ 2 := by rw [h1]
  simp_rw [hpt, integral_div, div_div, ← pow_succ]

/-- **Origin-to-axis bump-pair limit at first-jet order `w²`.** For a continuous gauge `M` with
`M(0) = 0` and `HasDerivAt M M'₀ 0`, continuous bumps `β₀, β` supported in `[−1, 1]`, and any shift
`L : ℝ` (in particular an axis shift `L = log b`),
`(1 / w²) ∫ M(x) M(x + L) β₀(x / w) β(x / w) dx → M'₀ M(L) ∫ y β₀(y) β(y) dy` as `w → 0⁺`. -/
theorem tendsto_origin_axis_bump_pair_div_sq {β₀ β : ℝ → ℝ} (hβ₀c : Continuous β₀)
    (hβc : Continuous β) (hβ : ∀ y, 1 < |y| → β y = 0) {M : ℝ → ℝ} {M'₀ : ℝ}
    (hM : Continuous M) (hM0 : M 0 = 0) (hd : HasDerivAt M M'₀ 0) (L : ℝ) :
    Tendsto (fun w => (∫ x, M x * M (x + L) * β₀ (x / w) * β (x / w)) / w ^ 2) (𝓝[>] 0)
      (𝓝 (M'₀ * M L * ∫ y, y * β₀ y * β y)) := by
  have hQ : Continuous (jetQuotient M M'₀) := continuous_jetQuotient hM hM0 hd
  have hF : Continuous fun x => jetQuotient M M'₀ x * M (x + L) :=
    hQ.mul (hM.comp (continuous_id.add continuous_const))
  have heq : ∀ᶠ w in 𝓝[>] (0 : ℝ),
      (∫ x, M x * M (x + L) * β₀ (x / w) * β (x / w)) / w ^ 2 =
        ∫ y, (jetQuotient M M'₀ (w * y) * M (w * y + L)) * (y * β₀ y * β y) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hw' : 0 < w := hw
    have hpt : (fun x => M x * M (x + L) * β₀ (x / w) * β (x / w)) =
        fun x => w * ((fun z => (jetQuotient M M'₀ (w * z) * M (w * z + L)) *
          (z * β₀ z * β z)) (x / w)) := by
      funext x
      have hM_eq := mul_jetQuotient_eq hM0 M'₀ x
      have hwx : w * (x / w) = x := mul_div_cancel₀ x hw'.ne'
      simp only [hwx]
      calc M x * M (x + L) * β₀ (x / w) * β (x / w)
          = (x * jetQuotient M M'₀ x) * M (x + L) * β₀ (x / w) * β (x / w) := by rw [hM_eq]
        _ = (w * (x / w)) * jetQuotient M M'₀ x * M (x + L) * β₀ (x / w) * β (x / w) := by
            rw [hwx]
        _ = w * (jetQuotient M M'₀ x * M (x + L) * (x / w * β₀ (x / w) * β (x / w))) := by ring
    rw [hpt, integral_const_mul,
      Measure.integral_comp_div (fun z => (jetQuotient M M'₀ (w * z) * M (w * z + L)) *
        (z * β₀ z * β z)) w,
      abs_of_pos hw', smul_eq_mul]
    field_simp [hw'.ne']
  refine Tendsto.congr' (EventuallyEq.symm heq) ?_
  obtain ⟨K, hK⟩ : ∃ K, ∀ z ∈ Icc (-1 : ℝ) 1, |jetQuotient M M'₀ z * M (z + L)| ≤ K :=
    (isCompact_Icc.exists_bound_of_continuousOn hF.continuousOn).imp fun K hK z hz => by
      simpa using hK z hz
  have hsupp : ∀ y, 1 < |y| → y * β₀ y * β y = 0 := fun y hy => by rw [hβ y hy, mul_zero]
  have hint : Integrable (fun y => K * |y * β₀ y * β y|) := by
    refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -1) (b := 1)) ?_
    intro y hy
    by_contra hmem
    rw [mem_Icc, not_and_or, not_le, not_le] at hmem
    have : 1 < |y| := by
      rcases hmem with h | h
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl h)
    exact hy (by simp [hsupp y this])
  have hlim : Tendsto (fun w => ∫ y, (jetQuotient M M'₀ (w * y) * M (w * y + L)) *
      (y * β₀ y * β y)) (𝓝[>] 0)
      (𝓝 (∫ y, (jetQuotient M M'₀ (0 * y) * M (0 * y + L)) * (y * β₀ y * β y))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun y => K * |y * β₀ y * β y|) ?_ ?_ hint ?_
    · exact Eventually.of_forall fun w => (by fun_prop : Continuous fun y =>
        (jetQuotient M M'₀ (w * y) * M (w * y + L)) * (y * β₀ y * β y)).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with w hw
      refine Eventually.of_forall fun y => ?_
      by_cases hy : 1 < |y|
      · rw [hsupp y hy]; simp
      · rw [not_lt] at hy
        have hz : w * y ∈ Icc (-1 : ℝ) 1 := by
          have : |w * y| ≤ 1 := by
            rw [abs_mul, abs_of_pos hw.1]
            nlinarith [abs_nonneg y, hw.2]
          exact abs_le.mp this
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right (hK _ hz) (abs_nonneg _)
    · refine Eventually.of_forall fun y => ?_
      exact ((hF.comp (continuous_id.mul continuous_const)).tendsto 0).mono_left
        nhdsWithin_le_nhds |>.mul_const _
  simp only [zero_mul, zero_add, jetQuotient_zero] at hlim
  rw [show M'₀ * M L * ∫ y, y * β₀ y * β y = ∫ y, M'₀ * M L * (y * β₀ y * β y) from
    (integral_const_mul _ _).symm]
  exact hlim

/-! ### Part III: Explicit self-energy of `narrowBump` and fixed-width lattice conductance -/

open RHTower.ArithmeticIncidenceBump RHTower.WeilOneSided RHTower.ArchimedeanAnomaly
open RHTower.WeilMarkovPole Zeta23

/-- On `(0, ∞)`, `archLevySinhWeight t = 2 * archLevyDensity t`. -/
theorem archLevySinhWeight_eq_two_mul_archLevyDensity {t : ℝ} (ht : 0 < t) :
    archLevySinhWeight t = 2 * archLevyDensity t :=
  exp_half_div_sinh_eq ht

/-- **Explicit logarithmic lower bound on the self-energy of `narrowBump j`.**
For every resolution index `j : ℕ`, with correlation radius `r_j = radius j = 1 / (2(j + 1))`,
`fullEnergy (narrowBump j) / mass j ≥ log(4 / r_j) + EF.gammaBracket 0 + π / 2 − 2 Ω(1) − 17 r_j`. -/
theorem fullEnergy_narrowBump_div_mass_ge (j : ℕ) :
    Real.log (4 / radius j) + EF.gammaBracket 0 + Real.pi / 2 -
        2 * archLevyAntideriv 1 - 17 * radius j ≤
      fullEnergy (narrowBump j) / mass j := by
  rw [fullEnergy_bump]
  set f := (narrowBump j : ℝ → ℝ)
  set r := radius j
  set m := mass j
  have hm : 0 < m := mass_pos j
  have hr : 0 < r := radius_pos j
  have hr_half : r ≤ 1 / 2 := radius_le_half j
  have hf : ContDiff ℝ 2 f := (narrowBump j).contDiff.of_le (by norm_cast)
  have hfc : HasCompactSupport f := (narrowBump j).hasCompactSupport
  have hexact : archEnergy f = EF.gammaBracket 0 * m +
      ∫ t in Ioi (0 : ℝ), ((m - autocorr f t) * archLevySinhWeight t +
        4 * autocorr f t * Real.cosh (t / 2)) := by
    have h := weilArchRe_eq_exactForm hf hfc
    rwa [bump_autocorr_zero] at h
  have hint_all : IntegrableOn (fun t => (m - autocorr f t) * archLevySinhWeight t +
      4 * autocorr f t * Real.cosh (t / 2)) (Ioi 0) := by
    have hc := continuous_autocorr hf hfc
    have hs := hasCompactSupport_autocorr hfc
    have h1 := integrableOn_biScaleLevyIntegrand hf hfc
    rw [bump_autocorr_zero] at h1
    exact h1.add ((((continuous_const.mul hc).mul (by fun_prop)).integrable_of_hasCompactSupport
      (hs.mul_left.mul_right)).integrableOn)
  have hunion : Ioi (0 : ℝ) = Ioc 0 r ∪ Ioi r := (Ioc_union_Ioi_eq_Ioi hr.le).symm
  have hint_left : IntegrableOn (fun t => (m - autocorr f t) * archLevySinhWeight t +
      4 * autocorr f t * Real.cosh (t / 2)) (Ioc 0 r) :=
    hint_all.mono_set (by rw [hunion]; exact subset_union_left)
  have hint_right : IntegrableOn (fun t => (m - autocorr f t) * archLevySinhWeight t +
      4 * autocorr f t * Real.cosh (t / 2)) (Ioi r) :=
    hint_all.mono_set (by rw [hunion]; exact subset_union_right)
  have hsplit : (∫ t in Ioi (0 : ℝ), ((m - autocorr f t) * archLevySinhWeight t +
      4 * autocorr f t * Real.cosh (t / 2))) =
      (∫ t in Ioc 0 r, ((m - autocorr f t) * archLevySinhWeight t +
        4 * autocorr f t * Real.cosh (t / 2))) +
      (∫ t in Ioi r, ((m - autocorr f t) * archLevySinhWeight t +
        4 * autocorr f t * Real.cosh (t / 2))) := by
    rw [hunion, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint_left hint_right]
  -- Bound on `Ioc 0 r`: `(m - autocorr f t) * w ≥ 0` and `4 * autocorr f t * cosh(t/2) ≥ -16 * m`
  have hleft_ge : -(16 * r * m) ≤ ∫ t in Ioc 0 r, ((m - autocorr f t) * archLevySinhWeight t +
      4 * autocorr f t * Real.cosh (t / 2)) := by
    have hconst_int : IntegrableOn (fun _ : ℝ => -(16 * m)) (Ioc 0 r) :=
      integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    have hmono := setIntegral_mono_on hconst_int hint_left measurableSet_Ioc fun t ht => by
      have ht0 : 0 < t := ht.1
      have htr : t ≤ r := ht.2
      have hb := abs_le.mp (bump_autocorr_bound j t)
      have hnn : 0 ≤ (m - autocorr f t) * archLevySinhWeight t :=
        mul_nonneg (by linarith) (archLevySinhWeight_pos ht0).le
      have hcosh : Real.cosh (t / 2) ≤ 4 := by
        rw [Real.cosh_eq]
        have h1 : Real.exp (t / 2) ≤ 2 := by
          calc Real.exp (t / 2) ≤ Real.exp (Real.log 2) :=
                Real.exp_le_exp.mpr (by linarith [Real.log_two_gt_d9])
            _ = 2 := Real.exp_log (by norm_num)
        have h2 : Real.exp (-(t / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        linarith
      have hcos_pos : 0 ≤ Real.cosh (t / 2) := (Real.cosh_pos _).le
      nlinarith
    rw [setIntegral_const, Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul] at hmono
    linarith
  -- Bound on `Ioi r`: restrict to `Ioc r 1 ⊆ Ioi r` where `autocorr f t = 0`
  have hright_ge : 2 * m * (archLevyAntideriv r - archLevyAntideriv 1) ≤
      ∫ t in Ioi r, ((m - autocorr f t) * archLevySinhWeight t +
        4 * autocorr f t * Real.cosh (t / 2)) := by
    have hnn_right : ∀ t ∈ Ioi r, 0 ≤ (m - autocorr f t) * archLevySinhWeight t +
        4 * autocorr f t * Real.cosh (t / 2) := by
      intro t ht
      have ht_gt : r < |t| := lt_of_lt_of_le ht (le_abs_self t)
      rw [bump_autocorr_vanish j ht_gt]
      simp only [sub_zero, mul_zero, zero_mul, add_zero]
      exact mul_nonneg hm.le (archLevySinhWeight_pos (lt_trans hr ht)).le
    have hsub : Ioc r 1 ⊆ Ioi r := fun t ht => ht.1
    have hmono := setIntegral_mono_set hint_right
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hnn_right))
      hsub.eventuallyLE
    have hcongr : (∫ t in Ioc r 1, ((m - autocorr f t) * archLevySinhWeight t +
        4 * autocorr f t * Real.cosh (t / 2))) =
        ∫ t in Ioc r 1, (2 * m) * archLevyDensity t := by
      refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
      have ht_gt : r < |t| := lt_of_lt_of_le ht.1 (le_abs_self t)
      rw [bump_autocorr_vanish j ht_gt, archLevySinhWeight_eq_two_mul_archLevyDensity (lt_trans hr ht.1)]
      ring
    have hr1 : r ≤ 1 := by linarith
    rw [hcongr, integral_const_mul, ← intervalIntegral.integral_of_le hr1,
      integral_archLevyDensity_Icc hr hr1] at hmono
    linarith
  have hΩ_ge := archLevyAntideriv_ge hr
  have hlog_eq : -(1 / 2) * Real.log (r / 4) = Real.log (4 / r) / 2 := by
    have hinv : Real.log (4 / r) = -Real.log (r / 4) := by
      rw [← Real.log_inv (r / 4), inv_div]
    linarith
  rw [le_div_iff₀ hm, hexact, hsplit]
  nlinarith

/-- **Uncalibrated fixed-width lower bound for `latticeTrain`.**
Combining `fullEnergy_latticeTrain_uniform` with `fullEnergy_narrowBump_div_mass_ge` gives an
explicit fixed-width lower bound on the complete Weil energy of the odd integer-log lattice train
at resolution `j = resolution N k`. -/
theorem fullEnergy_latticeTrain_fixedWidth_ge (N k : ℕ) (c : Fin N → ℝ) :
    2 * coefficientEnergy c *
        (Real.log (4 / radius (resolution N k)) + EF.gammaBracket 0 + Real.pi / 2 -
          2 * archLevyAntideriv 1 - 17 * radius (resolution N k) - 1 / (2 * ((k : ℝ) + 1))) -
      2 * incidenceForm c ≤
      fullEnergy (latticeTrain N (resolution N k) c) / mass (resolution N k) := by
  set j := resolution N k
  have hcal := (abs_le.mp (fullEnergy_latticeTrain_uniform N k c)).1
  have hself := fullEnergy_narrowBump_div_mass_ge j
  have hE := coefficientEnergy_nonneg c
  have hm := mass_pos j
  have hsplit : (fullEnergy (latticeTrain N j c) -
      2 * coefficientEnergy c * fullEnergy (narrowBump j)) / mass j =
      fullEnergy (latticeTrain N j c) / mass j -
        2 * coefficientEnergy c * (fullEnergy (narrowBump j) / mass j) := by
    ring
  rw [hsplit] at hcal
  have hmul := mul_le_mul_of_nonneg_left hself (show 0 ≤ 2 * coefficientEnergy c by positivity)
  have hrew : 2 * coefficientEnergy c * (1 / (2 * ((k : ℝ) + 1))) =
      coefficientEnergy c / ((k : ℝ) + 1) := by
    rw [one_div, mul_inv_rev]
    ring
  linarith

/-- Bound on `|incidenceForm c|` in terms of `coefficientEnergy c`:
`|incidenceForm c| ≤ (4 * N * Real.log (N + 2)) * coefficientEnergy c`. -/
theorem abs_incidenceForm_le (N : ℕ) (c : Fin N → ℝ) :
    |incidenceForm c| ≤ (4 * (N : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) * coefficientEnergy c := by
  let L : ℝ := Real.log ((N + 2 : ℕ) : ℝ)
  have hL_nonneg : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N + 2 by omega))
  have hatom_bounds : ∀ m : ℕ, m ≤ (N + 2) ^ 2 →
      0 ≤ vonMangoldtAtom m ∧ vonMangoldtAtom m ≤ 2 * L := by
    intro m hm
    unfold vonMangoldtAtom
    split_ifs with hm2
    · refine ⟨div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _), ?_⟩
      have h1 : (ArithmeticFunction.vonMangoldt m : ℝ) / Real.sqrt m ≤
          ArithmeticFunction.vonMangoldt m :=
        div_le_self ArithmeticFunction.vonMangoldt_nonneg
          (Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ m by omega)))
      have h2 : (ArithmeticFunction.vonMangoldt m : ℝ) ≤ Real.log m :=
        ArithmeticFunction.vonMangoldt_le_log
      have h3 : Real.log (m : ℝ) ≤ 2 * L := by
        have hle : (m : ℝ) ≤ ((N + 2 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hm
        have hlog := Real.log_le_log (by positivity) hle
        rw [Real.log_pow] at hlog
        exact_mod_cast hlog
      linarith
    · exact ⟨le_rfl, by positivity⟩
  have hterm_le : ∀ a b : Fin N,
      |c a * c b *
        ((if b.val + 2 ∣ a.val + 2 then vonMangoldtAtom ((a.val + 2) / (b.val + 2)) else 0) +
          (if a.val + 2 ∣ b.val + 2 then vonMangoldtAtom ((b.val + 2) / (a.val + 2)) else 0) -
            vonMangoldtAtom ((a.val + 2) * (b.val + 2)))| ≤
        2 * L * (c a ^ 2 + c b ^ 2) := by
    intro a b
    have hN2 : N + 2 ≤ (N + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
    have ha_le : a.val + 2 ≤ N + 2 := by have := a.isLt; omega
    have hb_le : b.val + 2 ≤ N + 2 := by have := b.isLt; omega
    have hdiv1 : (a.val + 2) / (b.val + 2) ≤ (N + 2) ^ 2 :=
      (Nat.div_le_self _ _).trans (ha_le.trans hN2)
    have hdiv2 : (b.val + 2) / (a.val + 2) ≤ (N + 2) ^ 2 :=
      (Nat.div_le_self _ _).trans (hb_le.trans hN2)
    have hmul : (a.val + 2) * (b.val + 2) ≤ (N + 2) ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul ha_le hb_le
    have hb1 : 0 ≤ (if b.val + 2 ∣ a.val + 2 then vonMangoldtAtom ((a.val + 2) / (b.val + 2)) else 0) ∧
        (if b.val + 2 ∣ a.val + 2 then vonMangoldtAtom ((a.val + 2) / (b.val + 2)) else 0) ≤ 2 * L := by
      split_ifs
      · exact hatom_bounds _ hdiv1
      · exact ⟨le_rfl, by positivity⟩
    have hb2 : 0 ≤ (if a.val + 2 ∣ b.val + 2 then vonMangoldtAtom ((b.val + 2) / (a.val + 2)) else 0) ∧
        (if a.val + 2 ∣ b.val + 2 then vonMangoldtAtom ((b.val + 2) / (a.val + 2)) else 0) ≤ 2 * L := by
      split_ifs
      · exact hatom_bounds _ hdiv2
      · exact ⟨le_rfl, by positivity⟩
    have hb3 := hatom_bounds _ hmul
    have habs_kernel :
        |(if b.val + 2 ∣ a.val + 2 then vonMangoldtAtom ((a.val + 2) / (b.val + 2)) else 0) +
          (if a.val + 2 ∣ b.val + 2 then vonMangoldtAtom ((b.val + 2) / (a.val + 2)) else 0) -
            vonMangoldtAtom ((a.val + 2) * (b.val + 2))| ≤ 4 * L :=
      abs_le.mpr ⟨by linarith [hb1.1, hb2.1, hb3.2], by linarith [hb1.2, hb2.2, hb3.1]⟩
    have hcs : 2 * (|c a| * |c b|) ≤ c a ^ 2 + c b ^ 2 := by
      have hsq : 0 ≤ (|c a| - |c b|) ^ 2 := sq_nonneg _
      have ha2 : |c a| ^ 2 = c a ^ 2 := sq_abs (c a)
      have hb2' : |c b| ^ 2 = c b ^ 2 := sq_abs (c b)
      nlinarith
    rw [abs_mul, abs_mul]
    nlinarith [mul_nonneg (abs_nonneg (c a)) (abs_nonneg (c b))]
  unfold incidenceForm coefficientEnergy
  calc |∑ a : Fin N, ∑ b : Fin N, c a * c b *
        ((if b.val + 2 ∣ a.val + 2 then vonMangoldtAtom ((a.val + 2) / (b.val + 2)) else 0) +
          (if a.val + 2 ∣ b.val + 2 then vonMangoldtAtom ((b.val + 2) / (a.val + 2)) else 0) -
            vonMangoldtAtom ((a.val + 2) * (b.val + 2)))|
      ≤ ∑ a : Fin N, ∑ b : Fin N, |c a * c b *
        ((if b.val + 2 ∣ a.val + 2 then vonMangoldtAtom ((a.val + 2) / (b.val + 2)) else 0) +
          (if a.val + 2 ∣ b.val + 2 then vonMangoldtAtom ((b.val + 2) / (a.val + 2)) else 0) -
            vonMangoldtAtom ((a.val + 2) * (b.val + 2)))| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a : Fin N, ∑ b : Fin N, 2 * L * (c a ^ 2 + c b ^ 2) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm_le a b
    _ = (4 * (N : ℝ) * L) * ∑ a : Fin N, c a ^ 2 := by
        simp_rw [mul_add, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
        ring

/-- **Explicit fixed-width positivity of `latticeTrain` above a resolution threshold.**
Whenever `8 * (k + 1) ≥ exp(2 Ω(1) + 9 + 4 N log(N + 2) − EF.gammaBracket 0)`, the complete Weil
energy `fullEnergy (latticeTrain N (resolution N k) c)` is nonnegative for every coefficient vector
`c : Fin N → ℝ`. -/
theorem fullEnergy_latticeTrain_nonneg_of_le (N k : ℕ)
    (hk : Real.exp (2 * archLevyAntideriv 1 + 9 +
      4 * (N : ℝ) * Real.log ((N + 2 : ℕ) : ℝ) - EF.gammaBracket 0) ≤ 8 * ((k : ℝ) + 1))
    (c : Fin N → ℝ) :
    0 ≤ fullEnergy (latticeTrain N (resolution N k) c) := by
  set j := resolution N k
  have hm : 0 < mass j := mass_pos j
  have hlow := fullEnergy_latticeTrain_fixedWidth_ge N k c
  have hinc : incidenceForm c ≤
      (4 * (N : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) * coefficientEnergy c :=
    (le_abs_self _).trans (abs_incidenceForm_le N c)
  have hj_ge : (k : ℝ) ≤ (j : ℝ) := by
    have hle : k ≤ j := by
      dsimp only [j, resolution]
      have h1 : 1 ≤ 128 * (N + 2) ^ 4 := Nat.one_le_iff_ne_zero.mpr (by positivity)
      nlinarith
    exact_mod_cast hle
  have hrad_inv : 8 * ((k : ℝ) + 1) ≤ 4 / radius j := by
    unfold radius
    rw [div_div_eq_mul_div, div_one]
    linarith
  have hlog_ge : 2 * archLevyAntideriv 1 + 9 +
      4 * (N : ℝ) * Real.log ((N + 2 : ℕ) : ℝ) - EF.gammaBracket 0 ≤
      Real.log (4 / radius j) := by
    have hexp_pos : 0 < Real.exp (2 * archLevyAntideriv 1 + 9 +
        4 * (N : ℝ) * Real.log ((N + 2 : ℕ) : ℝ) - EF.gammaBracket 0) := Real.exp_pos _
    have hlog := Real.log_le_log hexp_pos (hk.trans hrad_inv)
    rwa [Real.log_exp] at hlog
  have hr_half : radius j ≤ 1 / 2 := radius_le_half j
  have hk_inv : 1 / (2 * ((k : ℝ) + 1)) ≤ 1 / 2 := by
    refine one_div_le_one_div_of_le (by norm_num) ?_
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  have hpi : 0 ≤ Real.pi / 2 := by positivity
  have hE : 0 ≤ coefficientEnergy c := coefficientEnergy_nonneg c
  have hdiv_nonneg : 0 ≤ fullEnergy (latticeTrain N j c) / mass j := by
    have hbracket : 0 ≤ Real.log (4 / radius j) + EF.gammaBracket 0 + Real.pi / 2 -
        2 * archLevyAntideriv 1 - 17 * radius j - 1 / (2 * ((k : ℝ) + 1)) -
        4 * (N : ℝ) * Real.log ((N + 2 : ℕ) : ℝ) := by
      linarith
    have hprod : 0 ≤ 2 * coefficientEnergy c *
        (Real.log (4 / radius j) + EF.gammaBracket 0 + Real.pi / 2 -
          2 * archLevyAntideriv 1 - 17 * radius j - 1 / (2 * ((k : ℝ) + 1)) -
          4 * (N : ℝ) * Real.log ((N + 2 : ℕ) : ℝ)) := by positivity
    nlinarith
  have hmul := mul_nonneg hdiv_nonneg hm.le
  rwa [div_mul_cancel₀ _ hm.ne'] at hmul

/-- **Uniform fixed-width positivity for `latticeTrain`.**
For every lattice size `N : ℕ`, there exists a resolution threshold `K : ℕ` such that for all
`k ≥ K` and all coefficient vectors `c : Fin N → ℝ`,
`0 ≤ fullEnergy (latticeTrain N (resolution N k) c)`. -/
theorem eventually_fullEnergy_latticeTrain_nonneg (N : ℕ) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ c : Fin N → ℝ,
      0 ≤ fullEnergy (latticeTrain N (resolution N k) c) := by
  obtain ⟨K, hK⟩ := exists_nat_gt (Real.exp (2 * archLevyAntideriv 1 + 9 +
    4 * (N : ℝ) * Real.log ((N + 2 : ℕ) : ℝ) - EF.gammaBracket 0))
  refine ⟨K, fun k hk c => fullEnergy_latticeTrain_nonneg_of_le N k ?_ c⟩
  have hkR : (K : ℝ) ≤ k := Nat.cast_le.mpr hk
  linarith

end GaloisForLFunctions.ArithmeticIncidencePositivity

end

