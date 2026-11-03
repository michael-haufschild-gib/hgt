import GaloisForLFunctions.SignedWindowCriticality.TheMarkovPartDiesBeforeTheFirstPrime
import GaloisForLFunctions.ArithmeticCriticalityTheory.GeneralGaugeGroundStateRepresentation

/-!
# No Markov ground state on a window longer than the death width

The Markov part `M = W − pole` is a jump form with nonnegative rates (archimedean and prime) and
the potential `Φ cosh(x/2)` in the Doob gauge of Riemann's kernel `Φ`. Its two-sided generator is
`𝓛_D ω(x) = ∫ ω(t)𝓛^t ω(x) dt + Σ_n w_n 𝓛^{log n} ω(x)` (ACT).

* **Window Allegretto–Piepenbrink** (`markovEnergy_phiDoob_mul_nonneg_of_windowSupersolution`). A
  nonnegative `C²_c` gauge `ω` with `𝓛_D ω ≥ Φ cosh(x/2) ω` on an open interval `(b, c)` gives
  `M(Φ(ωu)) ≥ 0` for every `u ∈ C²_c` vanishing off `(b, c)`: in ACT's ground-state representation
  `M(Φ(ωu)) = J_{Φω}(u) + ∫ u²ω(𝓛_Dω − Φ cosh ω)`, both terms are nonnegative.
* **No-go** (`not_exists_markovWindowSupersolution`). If `c − b > e^{−3/4}`, no nonnegative `C²_c`
  gauge, positive on `(b, c)`, is a supersolution of the Markov generator on `(b, c)`: a translate of
  the Markov-negative plateau of `TheMarkovPartDiesBeforeTheFirstPrime` factors through it.

The no-go concerns the Markov part alone. On the unit odd window the interval `(0, ½)` is longer
than `e^{−3/4}`, so a supersolution certificate of the Markov generator cannot exist there; the
pole's squares must be kept.

The generator of a `C²_c` gauge is continuous (`continuous_twoSidedGenerator_of_contDiff`): the
archimedean part by dominated convergence with the Lipschitz bound `|𝓛^t ω| ≤ 2Φ(0)²Λt`, the prime
part by locally uniform summability.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open _root_.RHTower _root_.RHTower.CHMDPolar _root_.RHTower.WeilMarkovPole
open GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### Translation invariance of the Markov form -/

/-- The Markov form is translation invariant. -/
theorem markovForm_comp_sub (N : ℕ) (g : ℝ → ℝ) (s : ℝ) :
    markovForm N (fun u => g (u - s)) = markovForm N g := by
  have hsq : (∫ u, g (u - s) ^ 2) = ∫ u, g u ^ 2 :=
    integral_sub_right_eq_self (μ := volume) (fun u => g u ^ 2) s
  have hsh : ∀ y : ℝ, (∫ u, (g (u - s) - g (u + y - s)) ^ 2) = ∫ u, (g u - g (u + y)) ^ 2 := by
    intro y
    have := integral_sub_right_eq_self (μ := volume) (fun u => (g u - g (u + y)) ^ 2) s
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [sub_add_eq_add_sub]
  unfold markovForm levyJump primeJump
  simp_rw [hsq, hsh]

/-- Every interval of length `e^{−3/4}` carries a Markov-negative nonnegative `C²` test. -/
theorem exists_markovEnergy_neg_of_support_Icc (s : ℝ) :
    ∃ G : ℝ → ℝ, ContDiff ℝ 2 G ∧ (∀ u, u ∉ Icc s (s + markovDeathWidth) → G u = 0) ∧
      (∀ u, 0 ≤ G u) ∧ markovEnergy (fun u => (G u : ℂ)) < 0 := by
  obtain ⟨g, hg, hgsupp, hg0, hM0, hform, -⟩ := exists_markovEnergy_neg_of_support_le
  set G : ℝ → ℝ := fun u => g (u - s) with hG
  have hGc : ContDiff ℝ 2 G := hg.comp (contDiff_id.sub contDiff_const)
  have hGsupp : ∀ u, u ∉ Icc s (s + markovDeathWidth) → G u = 0 := by
    intro u hu
    exact hgsupp _ fun h => hu ⟨by linarith [h.1], by linarith [h.2]⟩
  have hGcs : HasCompactSupport G :=
    HasCompactSupport.intro (isCompact_Icc (a := s) (b := s + markovDeathWidth)) hGsupp
  have hN : ∀ n : ℕ, 1 < n → ∀ u, G u * G (u + Real.log n) = 0 := by
    intro n hn u
    by_cases hu : u ∈ Icc s (s + markovDeathWidth)
    · have hlog2 : Real.log 2 ≤ Real.log n :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have : u + Real.log n ∉ Icc s (s + markovDeathWidth) := fun h => by
        linarith [h.2, hu.1, markovDeathWidth_lt_log_two]
      rw [hGsupp _ this, mul_zero]
    · rw [hGsupp u hu, zero_mul]
  refine ⟨G, hGc, hGsupp, fun u => hg0 _, ?_⟩
  rw [← markovForm_eq_markovEnergy hGc hGcs hN, hG, markovForm_comp_sub]
  nlinarith

/-! ### Continuity of the generator of a `C²_c` gauge -/

theorem continuous_archTwoSidedGenerator_of_contDiff {z : ℝ → ℝ} (hz : ContDiff ℝ 2 z)
    (hzc : HasCompactSupport z) :
    Continuous fun x => ∫ t in Ioi (0 : ℝ), archLevyDensity t * twoSidedShiftGenerator z t x := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_lipschitz_bound_of_compactSupport (hz.of_le (by norm_num)) hzc
  set K := 2 * riemannKernelReal 0 ^ 2 * Λ
  refine continuous_of_dominated (bound := fun t => K * (archLevyDensity t * t)) (fun x => ?_)
    (fun x => ?_) (integrableOn_archLevyDensity_mul_id.const_mul K)
    (Eventually.of_forall fun t => continuous_const.mul (continuous_twoSidedShiftGenerator
      hz.continuous t))
  · exact (measurable_archLevyDensity.mul ((continuous_twoSidedShiftGenerator_uncurry
      hz.continuous).comp (continuous_id.prodMk continuous_const)).measurable).aestronglyMeasurable
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (archLevyDensity_pos ht0)]
    have hb := abs_twoSidedShiftGenerator_le_lipschitz hΛ ht0.le x
    nlinarith [mul_le_mul_of_nonneg_left hb (archLevyDensity_pos ht0).le]

theorem continuous_primeTwoSidedGenerator_of_bound {z : ℝ → ℝ} (hz : Continuous z) {Z : ℝ}
    (hZ : ∀ x, |z x| ≤ Z) :
    Continuous fun x => ∑' n : ℕ, vonMangoldtAtom n * twoSidedShiftGenerator z (Real.log n) x := by
  have hZ0 : 0 ≤ Z := le_trans (abs_nonneg _) (hZ 0)
  have hOn : ∀ M : ℝ, ContinuousOn
      (fun x => ∑' n : ℕ, vonMangoldtAtom n * twoSidedShiftGenerator z (Real.log n) x)
      (Icc (-M) M) := by
    intro M
    set K := 2 * Z * riemannKernelReal 0 * (2 * (riemannKernelReal 0 / riemannKernelReal M))
    refine continuousOn_tsum (u := fun n => K * (vonMangoldtAtom n * riemannKernelReal
      (M - Real.log n))) (fun n => (continuous_const.mul (continuous_twoSidedShiftGenerator hz
        _)).continuousOn) ((summable_atom_mul_kernel_sub M).mul_left K) fun n x hx => ?_
    have hxM : |x| ≤ M := abs_le.mpr ⟨hx.1, hx.2⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (vonMangoldtAtom_nonneg n)]
    have hb := abs_twoSidedShiftGenerator_le_kernel hZ (Real.log n) x
    have hk := riemannKernelReal_add_add_sub_le hxM n
    have hc : 0 ≤ 2 * Z * riemannKernelReal 0 := by
      have := riemannKernelReal_pos 0
      positivity
    have hG := hb.trans (mul_le_mul_of_nonneg_left hk hc)
    have ha := vonMangoldtAtom_nonneg n
    calc vonMangoldtAtom n * |twoSidedShiftGenerator z (Real.log n) x|
        ≤ vonMangoldtAtom n * (2 * Z * riemannKernelReal 0 *
          (2 * (riemannKernelReal 0 / riemannKernelReal M) * riemannKernelReal
            (M - Real.log n))) := mul_le_mul_of_nonneg_left hG ha
      _ = K * (vonMangoldtAtom n * riemannKernelReal (M - Real.log n)) := by ring
  refine continuous_iff_continuousAt.mpr fun x => ?_
  exact (hOn (|x| + 1)).continuousAt (Icc_mem_nhds (by linarith [neg_abs_le x])
    (by linarith [le_abs_self x]))

/-- The two-sided generator of a `C²_c` gauge is continuous. -/
theorem continuous_twoSidedGenerator_of_contDiff {z : ℝ → ℝ} (hz : ContDiff ℝ 2 z)
    (hzc : HasCompactSupport z) : Continuous (twoSidedGenerator z) := by
  obtain ⟨Z, hZ⟩ := hzc.exists_bound_of_continuous hz.continuous
  have hZ' : ∀ x, |z x| ≤ Z := fun x => by simpa [Real.norm_eq_abs] using hZ x
  unfold twoSidedGenerator
  exact (continuous_archTwoSidedGenerator_of_contDiff hz hzc).add
    (continuous_primeTwoSidedGenerator_of_bound hz.continuous hZ')

/-! ### Window Allegretto–Piepenbrink -/

/-- **Window Allegretto–Piepenbrink.** A nonnegative `C²_c` gauge that is a supersolution of the
Markov generator on `(b, c)` makes the Markov energy nonnegative on every test `Φ(ωu)` with
`u ∈ C²_c` vanishing off `(b, c)`. -/
theorem markovEnergy_phiDoob_mul_nonneg_of_windowSupersolution {ω u : ℝ → ℝ} {b c : ℝ}
    (hω : ContDiff ℝ 2 ω) (hωc : HasCompactSupport ω) (hω0 : ∀ x, 0 ≤ ω x)
    (hsuper : ∀ x ∈ Ioo b c,
      riemannKernelReal x * Real.cosh (x / 2) * ω x ≤ twoSidedGenerator ω x)
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (hub : ∀ x, x ∉ Ioo b c → u x = 0) :
    0 ≤ markovEnergy (fun x => (phiDoobTest (fun y => ω y * u y) x : ℂ)) := by
  obtain ⟨Z, hZ⟩ := hωc.exists_bound_of_continuous hω.continuous
  have hZ' : ∀ x, |ω x| ≤ Z := fun x => by simpa [Real.norm_eq_abs] using hZ x
  have hZ0 : 0 ≤ Z := le_trans (abs_nonneg _) (hZ' 0)
  obtain ⟨R, -, hR⟩ := ArithmeticCriticalityTheory.exists_support_radius hωc
  have hΦ0 := riemannKernelReal_pos 0
  set C := riemannKernelReal 0 * Z * Real.exp (24 * R)
  have hC0 : 0 ≤ C := by positivity
  have hM : ∀ y, |riemannKernelReal y * ω y| ≤ C * Real.exp (-(24 * |y|)) := by
    intro y
    by_cases hy : |y| ≤ R
    · have he : 1 ≤ Real.exp (24 * R) * Real.exp (-(24 * |y|)) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by linarith)
      have h1 : |riemannKernelReal y * ω y| ≤ riemannKernelReal 0 * Z := by
        rw [abs_mul, abs_of_pos (riemannKernelReal_pos y)]
        exact mul_le_mul (riemannKernelReal_le_zero_point y) (hZ' y) (abs_nonneg _) hΦ0.le
      calc |riemannKernelReal y * ω y| ≤ riemannKernelReal 0 * Z := h1
        _ = riemannKernelReal 0 * Z * 1 := by ring
        _ ≤ riemannKernelReal 0 * Z * (Real.exp (24 * R) * Real.exp (-(24 * |y|))) :=
          mul_le_mul_of_nonneg_left he (by positivity)
        _ = C * Real.exp (-(24 * |y|)) := by ring
    · rw [hR y (not_le.mp hy), mul_zero, abs_zero]; positivity
  set g : ℝ → ℝ := fun x =>
    (twoSidedGenerator ω x - riemannKernelReal x * Real.cosh (x / 2) * ω x) / riemannKernelReal x
  have hsrc : ∀ x, twoSidedGenerator ω x - riemannKernelReal x * Real.cosh (x / 2) * ω x =
      riemannKernelReal x * g x := fun x => by
    simp only [g]; field_simp [(riemannKernelReal_pos x).ne']
  have hg : Continuous g :=
    ((continuous_twoSidedGenerator_of_contDiff hω hωc).sub
      ((continuous_riemannKernelReal.mul (Real.continuous_cosh.comp
        (continuous_id.div_const 2))).mul hω.continuous)).div continuous_riemannKernelReal
      fun x => (riemannKernelReal_pos x).ne'
  rw [markovEnergy_phiDoob_mul_eq_signedJump_add_source hω hC0 hM
    (integrableOn_archLevy_twoSidedShiftGenerator_of_contDiff hω hωc)
    (summable_atom_twoSidedShiftGenerator hZ') hsrc hg hu huc]
  set Mg : ℝ → ℝ := fun y => riemannKernelReal y * ω y
  have hMg0 : ∀ y, 0 ≤ Mg y := fun y => mul_nonneg (riemannKernelReal_pos y).le (hω0 y)
  have hJ : 0 ≤ signedJumpEnergy Mg u := by
    unfold signedJumpEnergy
    have hsj : ∀ t x, 0 ≤ signedShiftJump Mg u t x := fun t x => by
      unfold signedShiftJump; exact mul_nonneg (mul_nonneg (hMg0 x) (hMg0 _)) (sq_nonneg _)
    refine add_nonneg (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
      (tsum_nonneg fun n => mul_nonneg (vonMangoldtAtom_nonneg n)
        (integral_nonneg fun x => hsj _ x))
    exact mul_nonneg (archLevyDensity_pos ht).le (integral_nonneg fun x => hsj t x)
  have hS : 0 ≤ ∫ x, u x ^ 2 * Mg x * g x := by
    refine integral_nonneg fun x => ?_
    by_cases hx : x ∈ Ioo b c
    · have hgx : 0 ≤ g x := div_nonneg (sub_nonneg.mpr (hsuper x hx))
        (riemannKernelReal_pos x).le
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (hMg0 x)) hgx
    · simp [hub x hx]
  linarith

/-! ### The no-go -/

/-- A quotient `G/D` is `C²` when `D` is `C²` and nonzero on an open set containing the closed
support of the `C²` function `G`. -/
theorem contDiff_div_of_support {G D : ℝ → ℝ} (hG : ContDiff ℝ 2 G) (hD : ContDiff ℝ 2 D)
    {U K : Set ℝ} (hDU : ∀ x ∈ U, D x ≠ 0) (hK : IsClosed K) (hKU : K ⊆ U)
    (hGK : ∀ x, x ∉ K → G x = 0) : ContDiff ℝ 2 fun x => G x / D x := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  by_cases hx : x ∈ U
  · exact hG.contDiffAt.div hD.contDiffAt (hDU x hx)
  · have hxK : x ∉ K := fun h => hx (hKU h)
    have hev : (fun x => G x / D x) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hK.isOpen_compl.mem_nhds hxK] with y hy
      rw [hGK y hy, zero_div]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- **No Markov ground state on a window longer than `e^{−3/4}`.** If `c − b > e^{−3/4}`, no
nonnegative `C²_c` gauge positive on `(b, c)` is a supersolution of the Markov generator there. -/
theorem not_exists_markovWindowSupersolution {b c : ℝ} (hbc : markovDeathWidth < c - b) :
    ¬ ∃ ω : ℝ → ℝ, ContDiff ℝ 2 ω ∧ HasCompactSupport ω ∧ (∀ x, 0 ≤ ω x) ∧
      (∀ x ∈ Ioo b c, 0 < ω x) ∧
      ∀ x ∈ Ioo b c, riemannKernelReal x * Real.cosh (x / 2) * ω x ≤ twoSidedGenerator ω x := by
  rintro ⟨ω, hω, hωc, hω0, hωpos, hsuper⟩
  set w := markovDeathWidth with hw
  set s := b + (c - b - w) / 2 with hs
  obtain ⟨G, hG, hGsupp, -, hGneg⟩ := exists_markovEnergy_neg_of_support_Icc s
  rw [← hw] at hGsupp
  have hw0 : 0 < w := markovDeathWidth_pos
  have hKU : Icc s (s + w) ⊆ Ioo b c := fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  set D : ℝ → ℝ := fun x => riemannKernelReal x * ω x
  have hD : ContDiff ℝ 2 D := contDiff_riemannKernelReal.mul hω
  have hDU : ∀ x ∈ Ioo b c, D x ≠ 0 := fun x hx =>
    (mul_pos (riemannKernelReal_pos x) (hωpos x hx)).ne'
  set u : ℝ → ℝ := fun x => G x / D x
  have hu : ContDiff ℝ 2 u :=
    contDiff_div_of_support hG hD hDU isClosed_Icc hKU hGsupp
  have hu0 : ∀ x, x ∉ Icc s (s + w) → u x = 0 := fun x hx => by
    simp only [u, hGsupp x hx, zero_div]
  have huc : HasCompactSupport u :=
    HasCompactSupport.intro (isCompact_Icc (a := s) (b := s + w)) hu0
  have hub : ∀ x, x ∉ Ioo b c → u x = 0 := fun x hx => hu0 x fun h => hx (hKU h)
  have hrec : (fun x => (phiDoobTest (fun y => ω y * u y) x : ℂ)) = fun x => (G x : ℂ) := by
    funext x
    congr 1
    simp only [phiDoobTest]
    by_cases hx : x ∈ Ioo b c
    · simp only [u, D]
      field_simp [(riemannKernelReal_pos x).ne', (hωpos x hx).ne']
    · have hxK : x ∉ Icc s (s + w) := fun h => hx (hKU h)
      rw [hub x hx, hGsupp x hxK, mul_zero, mul_zero]
  have h := markovEnergy_phiDoob_mul_nonneg_of_windowSupersolution hω hωc hω0 hsuper hu huc hub
  rw [hrec] at h
  linarith

end GaloisForLFunctions.SignedWindowCriticality

end
