import GaloisForLFunctions.HTGeometry.LogDerivPoissonJensen
import GaloisForLFunctions.RHTower.DeBruijnCollisionJumpLaw
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Tangent-disc Poisson–Jensen extraction of the lower Blaschke factor of `H_t`

From the Gaussian-weighted theta kernel `Φ_t(x) = Φ(x) e^{t x²}` of `H_t` alone (source data
only), this module extracts the lower-half-plane Blaschke factor of `H_t` along the horizontal
contours `Im z = ∓1`, preserving full zero multiplicities without reference to the zero locus.

* **Source construction**:
  * `heatThetaKernel t x = Φ(x) e^{t x²}`, `heatSourceEntire t z = ∫ Φ_t(x) e^{i z x} dx`.
  * `heatTangentPJ t R z`: boundary Herglotz derivative average of `log ‖H_t‖` on the disc
    `D(−i R, R)` tangent to `ℝ` at `0`, minus `(H_t'/H_t)(z)`.
  * `heatLowerBlaschkeLogDeriv t z = lim_{R → +∞} heatTangentPJ t R z`.
  * `heatLowerBlaschkeBoundary t r = exp(− ∫_{r}^{+∞} heatLowerBlaschkeLogDeriv t (σ − i) dσ)` and
    Schwarz mate `heatUpperBlaschkeBoundary t r = (conj(heatLowerBlaschkeBoundary t r))⁻¹`.
* **Imaginary-axis positivity** (`heatSourceEntire_I_mul_re_pos`, `re_ne_zero_of_riemannHeat_eq_zero`):
  `Re H_t(i y) > 0` for all `t ≥ 0, y ∈ ℝ`, so `H_t` has no purely imaginary zeros; `Im z < 0`
  corresponds bijectively (preserving multiplicity) to nonreal right zeros under `s = 1/2 + i z`.
* **Tangent-disc selection** (`heatLowerBlaschkeLogDeriv_eq`): since `‖u + i R‖² − R² = ‖u‖² + 2 R Im u`
  and `H_t(0) ≠ 0`, no real or upper-half-plane zero of `H_t` ever enters `closedBall (−i R) R`,
  while every lower-half-plane zero enters `ball (−i R) R` for large `R`. Passing `R → +∞` in
  `logDeriv_poissonJensen` cancels `R²` algebraically and yields `(B_t'/B_t)(z)` with no growth
  estimate on `log ‖H_t‖`.
* **Boundary evaluation and time continuity** (`heatLowerBlaschkeBoundary_eq`,
  `heatUpperBlaschkeBoundary_eq`, `tendsto_heatLowerBlaschkeBoundary_nhds`): integrating along
  `σ − i` recovers `B_t(r ∓ i)` with uniform strip bounds and continuity in `t ∈ (0, ∞)` across
  both real-axis and off-axis collisions.
-/

open Complex Metric Set Filter Topology MeasureTheory
open Real (circleAverage)
open scoped ComplexConjugate BigOperators
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.PoissonJensen
open RHTower RHTower.DeBruijn

noncomputable section

namespace GaloisForLFunctions.AdelicKreinGeometry

/-! ### Source-only definitions from the Gaussian-weighted theta kernel -/

/-- The Gaussian-weighted Riemann theta kernel `Φ_t(x) = Φ(x) e^{t x²}`. -/
def heatThetaKernel (t : ℝ) (x : ℝ) : ℝ :=
  riemannKernelReal x * Real.exp (t * x ^ 2)

/-- The entire cosine/Fourier transform `H_t(z) = ∫ Φ_t(x) e^{i z x} dx` built directly from
`heatThetaKernel t`. -/
def heatSourceEntire (t : ℝ) (z : ℂ) : ℂ :=
  cosTransform (heatThetaKernel t) z

theorem heatSourceEntire_eq_riemannHeat (t : ℝ) :
    heatSourceEntire t = riemannHeat t := rfl

/-- Differentiated Poisson–Jensen functional of `H_t` on the disc `D(−i R, R)` tangent to `ℝ` at
the origin. -/
def heatTangentPJ (t R : ℝ) (z : ℂ) : ℂ :=
  circleAverage
    (fun ζ => herglotzDerivKernel (-I * (R : ℂ)) z ζ *
      ((Real.log ‖heatSourceEntire t ζ‖ : ℝ) : ℂ)) (-I * (R : ℂ)) R -
    logDeriv (heatSourceEntire t) z

/-- Source-defined logarithmic derivative `lim_{R → +∞} heatTangentPJ t R z` of the lower-half-plane
Blaschke factor of `H_t`. -/
def heatLowerBlaschkeLogDeriv (t : ℝ) (z : ℂ) : ℂ :=
  limUnder atTop (fun R : ℝ => heatTangentPJ t R z)

/-- Source-defined lower horizontal boundary value `B_t(r − i)` reconstructed from
`heatLowerBlaschkeLogDeriv t` on `(r, +∞)`. -/
def heatLowerBlaschkeBoundary (t : ℝ) (r : ℝ) : ℂ :=
  cexp (- ∫ σ in Ioi r, heatLowerBlaschkeLogDeriv t ((σ : ℂ) - I))

/-- Source-defined upper horizontal boundary value `B_t(r + i)` via Schwarz reflection across `ℝ`. -/
def heatUpperBlaschkeBoundary (t : ℝ) (r : ℝ) : ℂ :=
  (conj (heatLowerBlaschkeBoundary t r))⁻¹

/-! ### Imaginary-axis positivity and coordinate dictionary -/

/-- On the imaginary axis `z = i y`, `H_t(i y) = ∫ Φ_t(x) e^{−y x} dx` is real and strictly
positive for every `t ≥ 0` and `y ∈ ℝ`. -/
theorem heatSourceEntire_I_mul_re_pos {t : ℝ} (ht : 0 ≤ t) (y : ℝ) :
    0 < (heatSourceEntire t (I * (y : ℂ))).re := by
  have hg : SuperExpKernel (heatThetaKernel t) := riemannKernel_superExp.mul_exp_sq ht
  set h : ℝ → ℝ := fun x => heatThetaKernel t x * Real.exp (-y * x)
  have hcont : Continuous h := hg.continuous.mul (by fun_prop)
  have hnonneg : ∀ x, 0 ≤ h x := fun x => mul_nonneg (hg.nonneg x) (Real.exp_pos _).le
  have hpos0 : 0 < h 0 := by simp [h, hg.pos_zero]
  have hint : Integrable h := by
    refine (hg.integrable_mul_exp |y|).mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (hg.nonneg x)
    calc -y * x ≤ |-y * x| := le_abs_self _
      _ = |y| * |x| := by rw [abs_mul, abs_neg]
  have hint_pos : 0 < ∫ x, h x := by
    rw [integral_pos_iff_support_of_nonneg hnonneg hint]
    have hopen : IsOpen {x : ℝ | 0 < h x} := isOpen_lt continuous_const hcont
    exact lt_of_lt_of_le (hopen.measure_pos volume ⟨0, hpos0⟩)
      (measure_mono fun x hx => Function.mem_support.mpr (ne_of_gt hx))
  have heq : heatSourceEntire t (I * (y : ℂ)) = ((∫ x, h x : ℝ) : ℂ) := by
    unfold heatSourceEntire cosTransform
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hexp : I * (I * (y : ℂ)) * (x : ℂ) = ((-y * x : ℝ) : ℂ) := by
      calc I * (I * (y : ℂ)) * (x : ℂ) = (I * I) * (y : ℂ) * (x : ℂ) := by ring
        _ = ((-y * x : ℝ) : ℂ) := by rw [Complex.I_mul_I]; push_cast; ring
    dsimp only [h]
    rw [hexp, ← Complex.ofReal_exp]
    push_cast
    rfl
  rw [heq, Complex.ofReal_re]
  exact hint_pos

theorem heatSourceEntire_I_mul_ne_zero {t : ℝ} (ht : 0 ≤ t) (y : ℝ) :
    heatSourceEntire t (I * (y : ℂ)) ≠ 0 := by
  intro h0
  have hpos := heatSourceEntire_I_mul_re_pos ht y
  rw [h0, Complex.zero_re] at hpos
  exact lt_irrefl 0 hpos

/-- `H_t` (`t ≥ 0`) has no zeros on the imaginary axis `Re z = 0` (the real axis in `s = 1/2 + i z`
coordinates). -/
theorem re_ne_zero_of_riemannHeat_eq_zero {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : riemannHeat t z = 0) : z.re ≠ 0 := by
  intro hre
  have hzI : z = I * (z.im : ℂ) := by
    apply Complex.ext <;> simp [hre]
  rw [hzI] at hz
  exact heatSourceEntire_I_mul_ne_zero ht z.im hz

/-- Under `s = 1/2 + i z`, the lower-half-plane zeros `{H_t(z) = 0, Im z < 0}` are precisely the
nonreal right zeros `{H_t(z) = 0, Re(1/2 + i z) > 1/2, Im(1/2 + i z) ≠ 0}`. -/
theorem riemannHeat_eq_zero_and_im_neg_iff {t : ℝ} (ht : 0 ≤ t) (z : ℂ) :
    (riemannHeat t z = 0 ∧ z.im < 0) ↔
      (riemannHeat t z = 0 ∧ 1 / 2 < (1 / 2 + I * z).re ∧ (1 / 2 + I * z).im ≠ 0) := by
  have hre : (1 / 2 + I * z).re = 1 / 2 - z.im := by simp [sub_eq_add_neg]
  have him : (1 / 2 + I * z).im = z.re := by simp
  rw [hre, him]
  constructor
  · rintro ⟨hz, hneg⟩
    exact ⟨hz, by linarith, re_ne_zero_of_riemannHeat_eq_zero ht hz⟩
  · rintro ⟨hz, hgt, -⟩
    exact ⟨hz, by linarith⟩

/-! ### The finite lower-half-plane zero set and multiplicity identities -/

/-- The finite set of lower-half-plane zeros of `H_t` (`t > 0`), i.e., nonreal right zeros in
`s = 1/2 + i z` coordinates (`∅` for `t ≤ 0`). -/
def heatRightZeroSet (t : ℝ) : Finset ℂ :=
  if ht : 0 < t then
    (riemannHeat_nonreal_zeros_finite ht).toFinset.filter (fun z => z.im < 0)
  else ∅

theorem mem_heatRightZeroSet {t : ℝ} (ht : 0 < t) {z : ℂ} :
    z ∈ heatRightZeroSet t ↔ riemannHeat t z = 0 ∧ z.im < 0 := by
  rw [heatRightZeroSet, dif_pos ht, Finset.mem_filter, Set.Finite.mem_toFinset]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.ne⟩, h.2⟩⟩

theorem heatRightZeroSet_eq_empty_of_le_zero {t : ℝ} (ht : t ≤ 0) :
    heatRightZeroSet t = ∅ := by
  rw [heatRightZeroSet, dif_neg (not_lt.mpr ht)]

theorem heatRightZeroSet_eq_empty_of_eighth_le {t : ℝ} (ht : 1 / 8 ≤ t) :
    heatRightZeroSet t = ∅ := by
  have ht0 : 0 < t := by linarith
  refine Finset.eq_empty_of_forall_notMem fun z hz => ?_
  obtain ⟨hz0, hneg⟩ := (mem_heatRightZeroSet ht0).mp hz
  exact hneg.ne (riemannHeat_zeros_real ht hz0)

/-- Strict strip contraction: for `t > 0`, every zero of `H_t` satisfies `|Im z| < 1/2`. -/
theorem abs_im_lt_half_of_riemannHeat_eq_zero {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : riemannHeat t z = 0) : |z.im| < 1 / 2 := by
  have hsq := riemannHeat_zeros_im_sq_le ht hz
  have hlt : max (1 / 4 - 2 * t) 0 < (1 / 2 : ℝ) ^ 2 := by
    refine max_lt ?_ (by norm_num)
    linarith
  have habs_sq : |z.im| ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    rw [sq_abs]
    exact hsq.trans_lt hlt
  nlinarith [abs_nonneg z.im]

/-- Outside the open strip `|Im z| < 1/2`, `H_t` (`t > 0`) is zero-free. -/
theorem riemannHeat_ne_zero_of_half_le_abs_im {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : 1 / 2 ≤ |z.im|) : riemannHeat t z ≠ 0 := fun h0 =>
  (not_lt.mpr hz) (abs_im_lt_half_of_riemannHeat_eq_zero ht h0)

/-- Total multiplicity of the nonreal right zeros of `H_t` (`0` for `t ≤ 0`). -/
def heatRightZeroMultiplicity (t : ℝ) : ℕ :=
  ∑ u ∈ heatRightZeroSet t, zeroMult (riemannHeat t) u

/-- Conjugation pairs lower- and upper-half-plane zeros of `H_t` with equal multiplicities, so
`2 * heatRightZeroMultiplicity t = nonrealZeroCount t`. -/
theorem two_mul_heatRightZeroMultiplicity (t : ℝ) :
    2 * heatRightZeroMultiplicity t = nonrealZeroCount t := by
  by_cases ht : 0 < t
  · set F := (riemannHeat_nonreal_zeros_finite ht).toFinset
    rw [nonrealZeroCount_eq ht, ← Finset.sum_filter_add_sum_filter_not F (fun z : ℂ => z.im < 0)]
    have hlow : F.filter (fun z : ℂ => z.im < 0) = heatRightZeroSet t := by
      rw [heatRightZeroSet, dif_pos ht]
    rw [hlow]
    have hbij : (∑ u ∈ heatRightZeroSet t, zeroMult (riemannHeat t) u) =
        ∑ v ∈ F.filter (fun z : ℂ => ¬ z.im < 0), zeroMult (riemannHeat t) v := by
      refine Finset.sum_bij (fun u _ => conj u) ?_ ?_ ?_ ?_
      · intro u hu
        obtain ⟨hu0, huneg⟩ := (mem_heatRightZeroSet ht).mp hu
        have hc0 : riemannHeat t (conj u) = 0 := by
          rw [riemannHeat_conj ht.le, hu0, map_zero]
        have hcim : 0 < (conj u).im := by rw [Complex.conj_im]; linarith
        exact Finset.mem_filter.mpr
          ⟨Set.Finite.mem_toFinset _ |>.mpr ⟨hc0, hcim.ne'⟩, not_lt.mpr hcim.le⟩
      · intro u₁ _ u₂ _ h
        exact (starRingEnd ℂ).injective h
      · intro v hv
        obtain ⟨hvF, hvnot⟩ := Finset.mem_filter.mp hv
        obtain ⟨hv0, hvim⟩ := (Set.Finite.mem_toFinset _).mp hvF
        have hvpos : 0 < v.im := lt_of_le_of_ne (not_lt.mp hvnot) hvim.symm
        refine ⟨conj v, (mem_heatRightZeroSet ht).mpr ⟨?_, ?_⟩, conj_conj v⟩
        · rw [riemannHeat_conj ht.le, hv0, map_zero]
        · rw [Complex.conj_im]; linarith
      · intro u _
        exact (zeroMult_riemannHeat_conj ht.le u).symm
    rw [← hbij, ← heatRightZeroMultiplicity]
    ring
  · simp [heatRightZeroMultiplicity, heatRightZeroSet, nonrealZeroCount, ht]

theorem heatRightZeroMultiplicity_eq_div (t : ℝ) :
    heatRightZeroMultiplicity t = nonrealZeroCount t / 2 := by
  rw [← two_mul_heatRightZeroMultiplicity, Nat.mul_div_cancel_left _ (by norm_num)]

theorem even_nonrealZeroCount (t : ℝ) : Even (nonrealZeroCount t) :=
  ⟨heatRightZeroMultiplicity t, by rw [← two_mul_heatRightZeroMultiplicity]; ring⟩

theorem heatRightZeroMultiplicity_eq_card_of_simple {t : ℝ}
    (hsimple : ∀ u ∈ heatRightZeroSet t, zeroMult (riemannHeat t) u = 1) :
    heatRightZeroMultiplicity t = (heatRightZeroSet t).card := by
  rw [heatRightZeroMultiplicity, Finset.sum_congr rfl hsimple, Finset.sum_const, smul_eq_mul,
    mul_one]

/-! ### Tangent-disc divisor geometry and limit of `heatTangentPJ` -/

private theorem norm_sub_neg_I_mul_sq (u : ℂ) (R : ℝ) :
    ‖u - (-I * (R : ℂ))‖ ^ 2 = ‖u‖ ^ 2 + 2 * R * u.im + R ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  have hre : (u - (-I * (R : ℂ))).re = u.re := by simp
  have him : (u - (-I * (R : ℂ))).im = u.im + R := by simp
  rw [Complex.normSq_apply, Complex.normSq_apply, hre, him]
  ring

private theorem mem_ball_tangentDisc_of_gt {u : ℂ} (hu : u.im < 0) {R : ℝ}
    (hR : ‖u‖ ^ 2 / (-2 * u.im) < R) : u ∈ ball (-I * (R : ℂ)) R := by
  have hden : 0 < -2 * u.im := by linarith
  have hRpos : 0 < R := lt_of_le_of_lt (div_nonneg (sq_nonneg _) hden.le) hR
  have hmul : ‖u‖ ^ 2 < R * (-2 * u.im) := (div_lt_iff₀ hden).mp hR
  have hsq : ‖u - (-I * (R : ℂ))‖ ^ 2 < R ^ 2 := by
    rw [norm_sub_neg_I_mul_sq]
    linarith
  rw [mem_ball_iff_norm]
  nlinarith [norm_nonneg (u - (-I * (R : ℂ)))]

private theorem im_neg_of_mem_closedBall_tangentDisc_of_zero {t R : ℝ} (ht : 0 ≤ t) (hR : 0 < R)
    {u : ℂ} (hu : u ∈ closedBall (-I * (R : ℂ)) |R|) (hz : riemannHeat t u = 0) :
    u.im < 0 := by
  rw [mem_closedBall_iff_norm, abs_of_pos hR] at hu
  have hsq : ‖u - (-I * (R : ℂ))‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
  rw [norm_sub_neg_I_mul_sq] at hsq
  have hle : 2 * R * u.im ≤ -(‖u‖ ^ 2) := by linarith
  have him_nonpos : u.im ≤ 0 := by
    nlinarith [sq_nonneg ‖u‖]
  rcases lt_or_eq_of_le him_nonpos with hlt | heq
  · exact hlt
  · exfalso
    rw [heq] at hle
    have hu0 : ‖u‖ = 0 := by nlinarith [norm_nonneg u]
    rw [norm_eq_zero.mp hu0] at hz
    exact riemannHeat_zero_ne ht hz

private theorem divisor_riemannHeat_tangentDisc {t R : ℝ} (ht : 0 < t) (hR : 0 < R)
    (hball : ∀ u ∈ heatRightZeroSet t, u ∈ ball (-I * (R : ℂ)) R) (u : ℂ) :
    MeromorphicOn.divisor (riemannHeat t) (closedBall (-I * (R : ℂ)) |R|) u =
      if u ∈ heatRightZeroSet t then (zeroMult (riemannHeat t) u : ℤ) else 0 := by
  classical
  set c : ℂ := -I * (R : ℂ)
  set CB : Set ℂ := closedBall c |R|
  have habs : |R| = R := abs_of_pos hR
  have hfan : AnalyticOnNhd ℂ (riemannHeat t) CB :=
    ((differentiable_riemannHeat ht.le).differentiableOn.analyticOnNhd isOpen_univ).mono
      (subset_univ _)
  by_cases hu : u ∈ heatRightZeroSet t
  · rw [if_pos hu]
    have huCB : u ∈ CB := by
      rw [show CB = closedBall c R by rw [← habs]]
      exact ball_subset_closedBall (hball u hu)
    rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfan huCB]
    have hord : analyticOrderAt (riemannHeat t) u = (zeroMult (riemannHeat t) u : ℕ∞) := by
      rw [zeroMult, ENat.coe_toNat (analyticOrderAt_riemannHeat_ne_top ht.le u)]
    rw [hord]
    rfl
  · rw [if_neg hu]
    by_cases huCB : u ∈ CB
    · have hnz : riemannHeat t u ≠ 0 := fun hz =>
        hu ((mem_heatRightZeroSet ht).mpr
          ⟨hz, im_neg_of_mem_closedBall_tangentDisc_of_zero ht.le hR huCB hz⟩)
      rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfan huCB,
        (hfan u huCB).analyticOrderAt_eq_zero.mpr hnz]
      rfl
    · by_contra hdiv
      exact huCB ((MeromorphicOn.divisor (riemannHeat t) CB).supportWithinDomain
        (Function.mem_support.mpr hdiv))

private theorem tendsto_tangentReflectionTerm {u z : ℂ} (hu : u.im < 0) (hz : z.im < 0) :
    Tendsto (fun R : ℝ =>
        -(conj (u - (-I * (R : ℂ))) /
          ((R : ℂ) ^ 2 - conj (u - (-I * (R : ℂ))) * (z - (-I * (R : ℂ))))))
      atTop (𝓝 (1 / (z - conj u))) := by
  have hzc_ne : z - conj u ≠ 0 := by
    intro h0
    have him := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at him
    linarith
  have hIzc_ne : I * (z - conj u) ≠ 0 := mul_ne_zero I_ne_zero hzc_ne
  have hinv : Tendsto (fun R : ℝ => ((R : ℂ))⁻¹) atTop (𝓝 0) := by
    have hr : Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp hr
  have hnum : Tendsto (fun R : ℝ => -(-I + conj u * ((R : ℂ))⁻¹)) atTop (𝓝 I) := by
    have h1 := tendsto_const_nhds (x := (-I : ℂ)).add (hinv.const_mul (conj u))
    rw [mul_zero, add_zero] at h1
    simpa using h1.neg
  have hden : Tendsto (fun R : ℝ => I * (z - conj u) - conj u * z * ((R : ℂ))⁻¹)
      atTop (𝓝 (I * (z - conj u))) := by
    have h1 := tendsto_const_nhds (x := I * (z - conj u)).sub (hinv.const_mul (conj u * z))
    simpa using h1
  have hquot := hnum.div hden hIzc_ne
  have hlim_eq : I / (I * (z - conj u)) = 1 / (z - conj u) := by
    field_simp [I_ne_zero, hzc_ne]
  rw [hlim_eq] at hquot
  refine hquot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  have hRc : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
  have hconj : conj (u - (-I * (R : ℂ))) = conj u - I * (R : ℂ) := by
    simp [Complex.conj_ofReal, sub_eq_add_neg]
  have hden_alg : (R : ℂ) ^ 2 - (conj u - I * (R : ℂ)) * (z - (-I * (R : ℂ))) =
      I * (R : ℂ) * (z - conj u) - conj u * z := by
    calc (R : ℂ) ^ 2 - (conj u - I * (R : ℂ)) * (z - (-I * (R : ℂ)))
        = (R : ℂ) ^ 2 - (conj u * z + I * (R : ℂ) * (conj u - z) - I ^ 2 * (R : ℂ) ^ 2) := by ring
      _ = I * (R : ℂ) * (z - conj u) - conj u * z := by rw [Complex.I_sq]; ring
  rw [hconj, hden_alg]
  have hN : -(-I + conj u * ((R : ℂ))⁻¹) * (R : ℂ) = -(conj u - I * (R : ℂ)) := by
    field_simp [hRc]; ring
  have hD : (I * (z - conj u) - conj u * z * ((R : ℂ))⁻¹) * (R : ℂ) =
      I * (R : ℂ) * (z - conj u) - conj u * z := by
    field_simp [hRc]
  calc -(-I + conj u * ((R : ℂ))⁻¹) / (I * (z - conj u) - conj u * z * ((R : ℂ))⁻¹)
      = (-(-I + conj u * ((R : ℂ))⁻¹) * (R : ℂ)) /
          ((I * (z - conj u) - conj u * z * ((R : ℂ))⁻¹) * (R : ℂ)) :=
        (mul_div_mul_right _ _ hRc).symm
    _ = -(conj u - I * (R : ℂ)) / (I * (R : ℂ) * (z - conj u) - conj u * z) := by rw [hN, hD]
    _ = -((conj u - I * (R : ℂ)) / (I * (R : ℂ) * (z - conj u) - conj u * z)) :=
        neg_div _ _

/-- **Tangent-disc Poisson–Jensen limit**: at every lower-half-plane point `z` where `H_t(z) ≠ 0`
(`t > 0`), `heatTangentPJ t R z` converges as `R → +∞` to the exact logarithmic derivative of the
lower Blaschke product of `H_t`, preserving all zero multiplicities. -/
theorem tendsto_heatTangentPJ_atTop {t : ℝ} (ht : 0 < t) {z : ℂ} (hz_im : z.im < 0)
    (hz_ne : riemannHeat t z ≠ 0) :
    Tendsto (fun R : ℝ => heatTangentPJ t R z) atTop
      (𝓝 (∑ u ∈ heatRightZeroSet t,
        (zeroMult (riemannHeat t) u : ℂ) * (1 / (z - conj u) - 1 / (z - u)))) := by
  classical
  set R₀ : ℝ := 1 + ‖z‖ ^ 2 / (-2 * z.im) +
    ∑ u ∈ heatRightZeroSet t, ‖u‖ ^ 2 / (-2 * u.im)
  have hsum_nn : 0 ≤ ∑ u ∈ heatRightZeroSet t, ‖u‖ ^ 2 / (-2 * u.im) :=
    Finset.sum_nonneg fun u hu => by
      have hu_im := ((mem_heatRightZeroSet ht).mp hu).2
      exact div_nonneg (sq_nonneg _) (by linarith)
  have hzio_nn : 0 ≤ ‖z‖ ^ 2 / (-2 * z.im) := div_nonneg (sq_nonneg _) (by linarith)
  have hev : ∀ᶠ R : ℝ in atTop, heatTangentPJ t R z =
      ∑ u ∈ heatRightZeroSet t, (zeroMult (riemannHeat t) u : ℂ) *
        (-(conj (u - (-I * (R : ℂ))) /
            ((R : ℂ) ^ 2 - conj (u - (-I * (R : ℂ))) * (z - (-I * (R : ℂ))))) -
          1 / (z - u)) := by
    filter_upwards [eventually_ge_atTop R₀] with R hRR₀
    have hR : 0 < R := by linarith
    set c : ℂ := -I * (R : ℂ)
    have hball : ∀ u ∈ heatRightZeroSet t, u ∈ ball c R := by
      intro u hu
      have hu_im := ((mem_heatRightZeroSet ht).mp hu).2
      have hle : ‖u‖ ^ 2 / (-2 * u.im) ≤ ∑ w ∈ heatRightZeroSet t, ‖w‖ ^ 2 / (-2 * w.im) :=
        Finset.single_le_sum (f := fun w : ℂ => ‖w‖ ^ 2 / (-2 * w.im))
          (fun w hw => div_nonneg (sq_nonneg _)
            (by have := ((mem_heatRightZeroSet ht).mp hw).2; linarith)) hu
      exact mem_ball_tangentDisc_of_gt hu_im (by linarith)
    have hz_ball : z ∈ ball c R := mem_ball_tangentDisc_of_gt hz_im (by linarith)
    have hdiv := divisor_riemannHeat_tangentDisc ht hR hball
    have hfan : AnalyticOnNhd ℂ (riemannHeat t) (closedBall c |R|) :=
      ((differentiable_riemannHeat ht.le).differentiableOn.analyticOnNhd isOpen_univ).mono
        (subset_univ _)
    have h₂f : ∀ u : (closedBall c |R| : Set ℂ),
        meromorphicOrderAt (riemannHeat t) u ≠ ⊤ := by
      intro u
      rw [(hfan u u.2).meromorphicOrderAt_eq]
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_riemannHeat_ne_top ht.le u)
      rw [← hk]
      exact WithTop.coe_ne_top
    have hbd : ∀ u ∈ sphere c |R|,
        MeromorphicOn.divisor (riemannHeat t) (closedBall c |R|) u = 0 := by
      intro u hus
      rw [hdiv u, if_neg]
      intro huZ
      have hub := mem_ball_iff_norm.mp (hball u huZ)
      rw [mem_sphere_iff_norm, abs_of_pos hR] at hus
      linarith
    have hz_notMem : z ∉ heatRightZeroSet t := fun hzZ =>
      hz_ne ((mem_heatRightZeroSet ht).mp hzZ).1
    have hwdiv : MeromorphicOn.divisor (riemannHeat t) (closedBall c |R|) z = 0 := by
      rw [hdiv z, if_neg hz_notMem]
    have hpj := logDeriv_poissonJensen hR hfan.meromorphicOn h₂f hbd hz_ball
      ((differentiable_riemannHeat ht.le).analyticAt z) hz_ne hwdiv
    have hfinsum : (∑ᶠ u : ℂ,
        (MeromorphicOn.divisor (riemannHeat t) (closedBall c |R|) u : ℂ) *
          (1 / (z - u) + conj (u - c) / ((R : ℂ) ^ 2 - conj (u - c) * (z - c)))) =
        ∑ u ∈ heatRightZeroSet t, (zeroMult (riemannHeat t) u : ℂ) *
          (1 / (z - u) + conj (u - c) / ((R : ℂ) ^ 2 - conj (u - c) * (z - c))) := by
      rw [finsum_eq_sum_of_support_subset _ (s := heatRightZeroSet t)]
      · refine Finset.sum_congr rfl fun u hu => ?_
        rw [hdiv u, if_pos hu, Int.cast_natCast]
      · intro u hu
        rw [Function.mem_support] at hu
        by_contra hun
        have hun' : u ∉ heatRightZeroSet t := Finset.mem_coe.not.mp hun
        apply hu
        rw [hdiv u, if_neg hun', Int.cast_zero, zero_mul]
    rw [hfinsum] at hpj
    unfold heatTangentPJ
    rw [heatSourceEntire_eq_riemannHeat]
    change circleAverage (fun ζ => herglotzDerivKernel c z ζ *
        ((Real.log ‖riemannHeat t ζ‖ : ℝ) : ℂ)) c R - logDeriv (riemannHeat t) z = _
    rw [hpj]
    have hcancel : ∀ a b : ℂ, b - (a + b) = -a := fun a b => by ring
    rw [hcancel, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    dsimp only [c]
    ring
  have hlim : Tendsto (fun R : ℝ =>
      ∑ u ∈ heatRightZeroSet t, (zeroMult (riemannHeat t) u : ℂ) *
        (-(conj (u - (-I * (R : ℂ))) /
            ((R : ℂ) ^ 2 - conj (u - (-I * (R : ℂ))) * (z - (-I * (R : ℂ))))) -
          1 / (z - u)))
      atTop (𝓝 (∑ u ∈ heatRightZeroSet t,
        (zeroMult (riemannHeat t) u : ℂ) * (1 / (z - conj u) - 1 / (z - u)))) :=
    tendsto_finsetSum _ fun u hu =>
      ((tendsto_tangentReflectionTerm ((mem_heatRightZeroSet ht).mp hu).2 hz_im).sub
        tendsto_const_nhds).const_mul _
  exact hlim.congr' (hev.mono fun R hR => hR.symm)

/-- Explicit evaluation of `heatLowerBlaschkeLogDeriv t z` at every lower-half-plane point where
`H_t(z) ≠ 0` (`t > 0`). -/
theorem heatLowerBlaschkeLogDeriv_eq {t : ℝ} (ht : 0 < t) {z : ℂ} (hz_im : z.im < 0)
    (hz_ne : riemannHeat t z ≠ 0) :
    heatLowerBlaschkeLogDeriv t z =
      ∑ u ∈ heatRightZeroSet t,
        (zeroMult (riemannHeat t) u : ℂ) * (1 / (z - conj u) - 1 / (z - u)) :=
  (tendsto_heatTangentPJ_atTop ht hz_im hz_ne).limUnder_eq

/-! ### Rational Blaschke product, horizontal boundary evaluation, and strip bounds -/

/-- The meromorphic lower-half-plane Blaschke product `∏_{u ∈ Z_−(t)} ((z − ū)/(z − u))^{m_t(u)}`.
Defined here only for identification and residue evaluation; the state itself uses only
`heatLowerBlaschkeBoundary` and `heatUpperBlaschkeBoundary`. -/
def heatBlaschkeMeromorphic (t : ℝ) (z : ℂ) : ℂ :=
  ∏ u ∈ heatRightZeroSet t,
    ((z - conj u) / (z - u)) ^ zeroMult (riemannHeat t) u

theorem heatBlaschkeMeromorphic_eq_one_of_eighth_le {t : ℝ} (ht : 1 / 8 ≤ t) (z : ℂ) :
    heatBlaschkeMeromorphic t z = 1 := by
  rw [heatBlaschkeMeromorphic, heatRightZeroSet_eq_empty_of_eighth_le ht, Finset.prod_empty]

theorem half_le_norm_sub_of_abs_im_eq_one {z w : ℂ} (hz : |z.im| = 1) (hw : |w.im| ≤ 1 / 2) :
    1 / 2 ≤ ‖z - w‖ := by
  have h1 : |z.im| - |w.im| ≤ |z.im - w.im| := abs_sub_abs_le_abs_sub z.im w.im
  have h2 : |(z - w).im| ≤ ‖z - w‖ := Complex.abs_im_le_norm (z - w)
  rw [Complex.sub_im] at h2
  linarith

theorem sub_ne_zero_of_abs_im_eq_one {z w : ℂ} (hz : |z.im| = 1) (hw : |w.im| ≤ 1 / 2) :
    z - w ≠ 0 := by
  intro h0
  have := half_le_norm_sub_of_abs_im_eq_one hz hw
  rw [h0, norm_zero] at this
  linarith

/-- Whenever `|Im u| ≤ 1/2` and `‖z − u‖ ≥ 1/2`, the elementary Blaschke factor satisfies
`‖(z − ū)/(z − u)‖ ≤ 3`. -/
theorem norm_blaschkeFactor_le_three {z u : ℂ} (hu : |u.im| ≤ 1 / 2) (hzu : 1 / 2 ≤ ‖z - u‖) :
    ‖(z - conj u) / (z - u)‖ ≤ 3 := by
  have hpos : 0 < ‖z - u‖ := by linarith
  have hdiff : u - conj u = ((2 * u.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [two_mul]
  have hnorm_diff : ‖u - conj u‖ ≤ 1 := by
    rw [hdiff, norm_mul, norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hnum : ‖z - conj u‖ ≤ 3 * ‖z - u‖ := by
    calc ‖z - conj u‖ = ‖(z - u) + (u - conj u)‖ := by ring_nf
      _ ≤ ‖z - u‖ + ‖u - conj u‖ := norm_add_le _ _
      _ ≤ ‖z - u‖ + 1 := by linarith
      _ ≤ 3 * ‖z - u‖ := by linarith
  rw [norm_div, div_le_iff₀ hpos]
  exact hnum

/-- On the closed upper half-plane `Im z ≥ 0`, every lower-half-plane Blaschke factor has modulus
at most `1`. -/
theorem norm_blaschkeFactor_le_one_of_im_nonneg {z u : ℂ} (hz : 0 ≤ z.im) (hu : u.im ≤ 0) :
    ‖(z - conj u) / (z - u)‖ ≤ 1 := by
  by_cases hzu : z - u = 0
  · rw [hzu, div_zero, norm_zero]
    norm_num
  · have hpos : 0 < ‖z - u‖ := norm_pos_iff.mpr hzu
    rw [norm_div, div_le_iff₀ hpos, one_mul]
    have hsq : ‖z - conj u‖ ^ 2 ≤ ‖z - u‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_apply, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.conj_re, Complex.conj_im]
      have hmul : z.im * u.im ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hz hu
      nlinarith
    nlinarith [norm_nonneg (z - conj u)]

private theorem blaschkeQuotient_mem_slitPlane (σ : ℝ) {u : ℂ} (hu : |u.im| ≤ 1 / 2) :
    (((σ : ℂ) - I - conj u) / ((σ : ℂ) - I - u)) ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  set a : ℂ := (σ : ℂ) - I - conj u
  set b : ℂ := (σ : ℂ) - I - u
  have hb_im : |((σ : ℂ) - I).im| = 1 := by simp
  have hb_ne : b ≠ 0 := sub_ne_zero_of_abs_im_eq_one hb_im hu
  rw [Complex.div_re, ← add_div]
  refine div_pos ?_ (Complex.normSq_pos.mpr hb_ne)
  have hare : a.re = σ - u.re := by simp [a]
  have hbre : b.re = σ - u.re := by simp [b]
  have haim : a.im = -1 + u.im := by simp [a]
  have hbim : b.im = -1 - u.im := by simp [b]
  rw [hare, hbre, haim, hbim]
  obtain ⟨hu1, hu2⟩ := abs_le.mp hu
  have hsq : u.im ^ 2 ≤ 1 / 4 := by nlinarith
  nlinarith [sq_nonneg (σ - u.re)]

private theorem hasDerivAt_clog_blaschkeQuotient (σ : ℝ) {u : ℂ} (hu : |u.im| ≤ 1 / 2) :
    HasDerivAt
      (fun x : ℝ => Complex.log (((x : ℂ) - I - conj u) / ((x : ℂ) - I - u)))
      (1 / ((σ : ℂ) - I - conj u) - 1 / ((σ : ℂ) - I - u)) σ := by
  have him1 : |((σ : ℂ) - I).im| = 1 := by simp
  have huc : |(conj u).im| ≤ 1 / 2 := by rw [Complex.conj_im, abs_neg]; exact hu
  have ha_ne : (σ : ℂ) - I - conj u ≠ 0 := sub_ne_zero_of_abs_im_eq_one him1 huc
  have hb_ne : (σ : ℂ) - I - u ≠ 0 := sub_ne_zero_of_abs_im_eq_one him1 hu
  have hg₁ : HasDerivAt (fun x : ℝ => (x : ℂ) - I - conj u) 1 σ := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := σ)).sub_const I).sub_const (conj u)
  have hg₂ : HasDerivAt (fun x : ℝ => (x : ℂ) - I - u) 1 σ := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := σ)).sub_const I).sub_const u
  have hq : HasDerivAt
      (fun x : ℝ => Complex.log (((x : ℂ) - I - conj u) / ((x : ℂ) - I - u)))
      (((1 * ((σ : ℂ) - I - u) - ((σ : ℂ) - I - conj u) * 1) / ((σ : ℂ) - I - u) ^ 2) /
        (((σ : ℂ) - I - conj u) / ((σ : ℂ) - I - u))) σ :=
    (hg₁.div hg₂ hb_ne).clog_real (blaschkeQuotient_mem_slitPlane σ hu)
  have hval : (((1 * ((σ : ℂ) - I - u) - ((σ : ℂ) - I - conj u) * 1) / ((σ : ℂ) - I - u) ^ 2) /
      (((σ : ℂ) - I - conj u) / ((σ : ℂ) - I - u))) =
      1 / ((σ : ℂ) - I - conj u) - 1 / ((σ : ℂ) - I - u) := by
    field_simp [ha_ne, hb_ne]
  rwa [hval] at hq

private theorem integrable_blaschkeLogDerivTerm {u : ℂ} (hu : |u.im| ≤ 1 / 2) :
    Integrable (fun σ : ℝ => 1 / ((σ : ℂ) - I - conj u) - 1 / ((σ : ℂ) - I - u)) := by
  have huc : |(conj u).im| ≤ 1 / 2 := by rw [Complex.conj_im, abs_neg]; exact hu
  have ha_ne : ∀ σ : ℝ, (σ : ℂ) - I - conj u ≠ 0 := fun σ =>
    sub_ne_zero_of_abs_im_eq_one (by simp) huc
  have hb_ne : ∀ σ : ℝ, (σ : ℂ) - I - u ≠ 0 := fun σ =>
    sub_ne_zero_of_abs_im_eq_one (by simp) hu
  have hcont : Continuous (fun σ : ℝ =>
      1 / ((σ : ℂ) - I - conj u) - 1 / ((σ : ℂ) - I - u)) := by
    refine Continuous.sub ?_ ?_
    · exact continuous_const.div (by fun_prop) ha_ne
    · exact continuous_const.div (by fun_prop) hb_ne
  have hmaj : Integrable (fun σ : ℝ => (4 * ‖conj u - u‖) * (1 + (σ - u.re) ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq.comp_sub_right u.re).const_mul _
  refine hmaj.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun σ => ?_)
  set a : ℂ := (σ : ℂ) - I - conj u
  set b : ℂ := (σ : ℂ) - I - u
  have hdiff : 1 / a - 1 / b = (conj u - u) / (a * b) := by
    have hsub : b - a = conj u - u := by dsimp [a, b]; ring
    rw [div_sub_div _ _ (ha_ne σ) (hb_ne σ), one_mul, mul_one, hsub]
  rw [hdiff, norm_div]
  obtain ⟨hu1, hu2⟩ := abs_le.mp hu
  have ha_sq : (1 + (σ - u.re) ^ 2) / 4 ≤ ‖a‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hare : a.re = σ - u.re := by simp [a]
    have haim : a.im = -1 + u.im := by simp [a]
    rw [hare, haim]
    nlinarith [sq_nonneg (σ - u.re)]
  have hb_sq : (1 + (σ - u.re) ^ 2) / 4 ≤ ‖b‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hbre : b.re = σ - u.re := by simp [b]
    have hbim : b.im = -1 - u.im := by simp [b]
    rw [hbre, hbim]
    nlinarith [sq_nonneg (σ - u.re)]
  have hab_pos : 0 < 1 + (σ - u.re) ^ 2 := by positivity
  have hab_norm : (1 + (σ - u.re) ^ 2) / 4 ≤ ‖a * b‖ := by
    rw [norm_mul]
    have hnn : 0 ≤ (1 + (σ - u.re) ^ 2) / 4 := by positivity
    have hmul : ((1 + (σ - u.re) ^ 2) / 4) ^ 2 ≤ (‖a‖ * ‖b‖) ^ 2 := by
      rw [mul_pow]
      calc ((1 + (σ - u.re) ^ 2) / 4) ^ 2
          = ((1 + (σ - u.re) ^ 2) / 4) * ((1 + (σ - u.re) ^ 2) / 4) := sq _
        _ ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := mul_le_mul ha_sq hb_sq hnn (sq_nonneg _)
    exact (sq_le_sq₀ hnn (mul_nonneg (norm_nonneg a) (norm_nonneg b))).mp hmul
  calc ‖conj u - u‖ / ‖a * b‖
      ≤ ‖conj u - u‖ / ((1 + (σ - u.re) ^ 2) / 4) :=
        div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hab_norm
    _ = (4 * ‖conj u - u‖) * (1 + (σ - u.re) ^ 2)⁻¹ := by field_simp [hab_pos.ne']

private theorem tendsto_clog_blaschkeQuotient_atTop {u : ℂ} (hu : |u.im| ≤ 1 / 2) :
    Tendsto (fun σ : ℝ => Complex.log (((σ : ℂ) - I - conj u) / ((σ : ℂ) - I - u)))
      atTop (𝓝 0) := by
  have hq1 : Tendsto (fun σ : ℝ => ((σ : ℂ) - I - conj u) / ((σ : ℂ) - I - u))
      atTop (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hinv : Tendsto (fun σ : ℝ => ‖u - conj u‖ * (σ - u.re)⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun σ : ℝ => (σ - u.re)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (-u.re) tendsto_id)
      simpa using h1.const_mul ‖u - conj u‖
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hinv
    filter_upwards [eventually_ge_atTop (u.re + 1)] with σ hσ
    have hpos : 0 < σ - u.re := by linarith
    have hb_ne : (σ : ℂ) - I - u ≠ 0 := sub_ne_zero_of_abs_im_eq_one (by simp) hu
    have hsub : ((σ : ℂ) - I - conj u) / ((σ : ℂ) - I - u) - 1 =
        (u - conj u) / ((σ : ℂ) - I - u) := by
      field_simp [hb_ne]; ring
    rw [hsub, norm_div]
    have hle_norm : σ - u.re ≤ ‖(σ : ℂ) - I - u‖ := by
      have hre : ((σ : ℂ) - I - u).re = σ - u.re := by simp
      calc σ - u.re ≤ |σ - u.re| := le_abs_self _
        _ = |((σ : ℂ) - I - u).re| := by rw [hre]
        _ ≤ ‖(σ : ℂ) - I - u‖ := Complex.abs_re_le_norm _
    calc ‖u - conj u‖ / ‖(σ : ℂ) - I - u‖
        ≤ ‖u - conj u‖ / (σ - u.re) :=
          div_le_div_of_nonneg_left (norm_nonneg _) hpos hle_norm
      _ = ‖u - conj u‖ * (σ - u.re)⁻¹ := div_eq_mul_inv _ _
  simpa [Complex.log_one] using hq1.clog Complex.one_mem_slitPlane

private theorem integral_Ioi_blaschkeLogDerivTerm (r : ℝ) {u : ℂ} (hu : |u.im| ≤ 1 / 2) :
    (∫ σ in Ioi r, (1 / ((σ : ℂ) - I - conj u) - 1 / ((σ : ℂ) - I - u))) =
      -Complex.log (((r : ℂ) - I - conj u) / ((r : ℂ) - I - u)) := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' (a := r)
    (fun σ _ => hasDerivAt_clog_blaschkeQuotient σ hu)
    (integrable_blaschkeLogDerivTerm hu).integrableOn
    (tendsto_clog_blaschkeQuotient_atTop hu), zero_sub]

/-- **Lower horizontal boundary identification**: for every `t > 0` and `r ∈ ℝ`, the source-defined
boundary value `heatLowerBlaschkeBoundary t r` equals `B_t(r − i)`. -/
theorem heatLowerBlaschkeBoundary_eq {t : ℝ} (ht : 0 < t) (r : ℝ) :
    heatLowerBlaschkeBoundary t r = heatBlaschkeMeromorphic t ((r : ℂ) - I) := by
  have hline : ∀ σ : ℝ, heatLowerBlaschkeLogDeriv t ((σ : ℂ) - I) =
      ∑ u ∈ heatRightZeroSet t, (zeroMult (riemannHeat t) u : ℂ) *
        (1 / ((σ : ℂ) - I - conj u) - 1 / ((σ : ℂ) - I - u)) := by
    intro σ
    refine heatLowerBlaschkeLogDeriv_eq ht (by simp) ?_
    exact riemannHeat_ne_zero_of_half_le_abs_im ht (by simp; norm_num)
  have hint : ∀ u ∈ heatRightZeroSet t,
      IntegrableOn (fun σ : ℝ => (zeroMult (riemannHeat t) u : ℂ) *
        (1 / ((σ : ℂ) - I - conj u) - 1 / ((σ : ℂ) - I - u))) (Ioi r) := fun u hu => by
    have hu_strip : |u.im| ≤ 1 / 2 :=
      (abs_im_lt_half_of_riemannHeat_eq_zero ht ((mem_heatRightZeroSet ht).mp hu).1).le
    exact ((integrable_blaschkeLogDerivTerm hu_strip).const_mul _).integrableOn
  have hint_eq : (∫ σ in Ioi r, heatLowerBlaschkeLogDeriv t ((σ : ℂ) - I)) =
      ∑ u ∈ heatRightZeroSet t, -(zeroMult (riemannHeat t) u : ℂ) *
        Complex.log (((r : ℂ) - I - conj u) / ((r : ℂ) - I - u)) := by
    have hcongr : (∫ σ in Ioi r, heatLowerBlaschkeLogDeriv t ((σ : ℂ) - I)) =
        ∫ σ in Ioi r, ∑ u ∈ heatRightZeroSet t, (zeroMult (riemannHeat t) u : ℂ) *
          (1 / ((σ : ℂ) - I - conj u) - 1 / ((σ : ℂ) - I - u)) :=
      setIntegral_congr_fun measurableSet_Ioi fun σ _ => hline σ
    rw [hcongr, integral_finsetSum _ hint]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu_strip : |u.im| ≤ 1 / 2 :=
      (abs_im_lt_half_of_riemannHeat_eq_zero ht ((mem_heatRightZeroSet ht).mp hu).1).le
    rw [integral_const_mul, integral_Ioi_blaschkeLogDerivTerm r hu_strip]
    ring
  unfold heatLowerBlaschkeBoundary heatBlaschkeMeromorphic
  rw [hint_eq, ← Finset.sum_neg_distrib, Complex.exp_sum]
  refine Finset.prod_congr rfl fun u hu => ?_
  have hu_strip : |u.im| ≤ 1 / 2 :=
    (abs_im_lt_half_of_riemannHeat_eq_zero ht ((mem_heatRightZeroSet ht).mp hu).1).le
  have huc : |(conj u).im| ≤ 1 / 2 := by rw [Complex.conj_im, abs_neg]; exact hu_strip
  have ha_ne : (r : ℂ) - I - conj u ≠ 0 := sub_ne_zero_of_abs_im_eq_one (by simp) huc
  have hb_ne : (r : ℂ) - I - u ≠ 0 := sub_ne_zero_of_abs_im_eq_one (by simp) hu_strip
  have hq_ne : ((r : ℂ) - I - conj u) / ((r : ℂ) - I - u) ≠ 0 := div_ne_zero ha_ne hb_ne
  rw [show -(-(zeroMult (riemannHeat t) u : ℂ) *
      Complex.log (((r : ℂ) - I - conj u) / ((r : ℂ) - I - u))) =
      (zeroMult (riemannHeat t) u : ℂ) *
        Complex.log (((r : ℂ) - I - conj u) / ((r : ℂ) - I - u)) by ring,
    Complex.exp_nat_mul, Complex.exp_log hq_ne]

/-- **Upper horizontal boundary identification**: for every `t > 0` and `r ∈ ℝ`, the Schwarz mate
`heatUpperBlaschkeBoundary t r` equals `B_t(r + i)`. -/
theorem heatUpperBlaschkeBoundary_eq {t : ℝ} (ht : 0 < t) (r : ℝ) :
    heatUpperBlaschkeBoundary t r = heatBlaschkeMeromorphic t ((r : ℂ) + I) := by
  unfold heatUpperBlaschkeBoundary
  rw [heatLowerBlaschkeBoundary_eq ht r]
  unfold heatBlaschkeMeromorphic
  rw [map_prod, ← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun u _ => ?_
  rw [map_pow, ← inv_pow]
  congr 1
  rw [map_div₀, inv_div]
  have h1 : conj ((r : ℂ) - I - u) = (r : ℂ) + I - conj u := by simp [Complex.conj_ofReal]
  have h2 : conj ((r : ℂ) - I - conj u) = (r : ℂ) + I - u := by simp [Complex.conj_ofReal]
  rw [h1, h2]

/-- Uniform modulus bound on `heatBlaschkeMeromorphic t z` whenever `‖z − u‖ ≥ 1/2` for all
`u ∈ heatRightZeroSet t`. -/
theorem norm_heatBlaschkeMeromorphic_le {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hdist : ∀ u ∈ heatRightZeroSet t, 1 / 2 ≤ ‖z - u‖) :
    ‖heatBlaschkeMeromorphic t z‖ ≤ (3 : ℝ) ^ heatRightZeroMultiplicity t := by
  unfold heatBlaschkeMeromorphic
  rw [heatRightZeroMultiplicity]
  calc ‖∏ u ∈ heatRightZeroSet t, ((z - conj u) / (z - u)) ^ zeroMult (riemannHeat t) u‖
      ≤ ∏ u ∈ heatRightZeroSet t,
          ‖((z - conj u) / (z - u)) ^ zeroMult (riemannHeat t) u‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ u ∈ heatRightZeroSet t, (3 : ℝ) ^ zeroMult (riemannHeat t) u := by
        refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun u hu => ?_
        rw [norm_pow]
        have hu_strip : |u.im| ≤ 1 / 2 :=
          (abs_im_lt_half_of_riemannHeat_eq_zero ht ((mem_heatRightZeroSet ht).mp hu).1).le
        exact pow_le_pow_left₀ (norm_nonneg _)
          (norm_blaschkeFactor_le_three hu_strip (hdist u hu)) _
    _ = (3 : ℝ) ^ ∑ u ∈ heatRightZeroSet t, zeroMult (riemannHeat t) u :=
        Finset.prod_pow_eq_pow_sum _ _ _

theorem norm_heatLowerBlaschkeBoundary_le {t : ℝ} (ht : 0 < t) (r : ℝ) :
    ‖heatLowerBlaschkeBoundary t r‖ ≤ (3 : ℝ) ^ heatRightZeroMultiplicity t := by
  rw [heatLowerBlaschkeBoundary_eq ht r]
  refine norm_heatBlaschkeMeromorphic_le ht fun u hu => ?_
  have hu_strip : |u.im| ≤ 1 / 2 :=
    (abs_im_lt_half_of_riemannHeat_eq_zero ht ((mem_heatRightZeroSet ht).mp hu).1).le
  exact half_le_norm_sub_of_abs_im_eq_one (by simp) hu_strip

theorem norm_heatUpperBlaschkeBoundary_le_one {t : ℝ} (ht : 0 < t) (r : ℝ) :
    ‖heatUpperBlaschkeBoundary t r‖ ≤ 1 := by
  rw [heatUpperBlaschkeBoundary_eq ht r]
  unfold heatBlaschkeMeromorphic
  calc ‖∏ u ∈ heatRightZeroSet t,
        (((r : ℂ) + I - conj u) / ((r : ℂ) + I - u)) ^ zeroMult (riemannHeat t) u‖
      ≤ ∏ u ∈ heatRightZeroSet t,
          ‖(((r : ℂ) + I - conj u) / ((r : ℂ) + I - u)) ^ zeroMult (riemannHeat t) u‖ :=
        Finset.norm_prod_le _ _
    _ ≤ ∏ _u ∈ heatRightZeroSet t, (1 : ℝ) := by
        refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun u hu => ?_
        rw [norm_pow]
        have hu_im : u.im ≤ 0 := ((mem_heatRightZeroSet ht).mp hu).2.le
        exact pow_le_one₀ (norm_nonneg _)
          (norm_blaschkeFactor_le_one_of_im_nonneg (by simp) hu_im)
    _ = 1 := Finset.prod_const_one

theorem continuous_heatLowerBlaschkeBoundary {t : ℝ} (ht : 0 < t) :
    Continuous (heatLowerBlaschkeBoundary t) := by
  have heq : heatLowerBlaschkeBoundary t = fun r : ℝ =>
      heatBlaschkeMeromorphic t ((r : ℂ) - I) := funext (heatLowerBlaschkeBoundary_eq ht)
  rw [heq]
  unfold heatBlaschkeMeromorphic
  refine continuous_finsetProd _ fun u hu => ?_
  have hu_strip : |u.im| ≤ 1 / 2 :=
    (abs_im_lt_half_of_riemannHeat_eq_zero ht ((mem_heatRightZeroSet ht).mp hu).1).le
  refine Continuous.pow (Continuous.div (by fun_prop) (by fun_prop) fun r => ?_) _
  exact sub_ne_zero_of_abs_im_eq_one (by simp) hu_strip

theorem continuous_heatUpperBlaschkeBoundary {t : ℝ} (ht : 0 < t) :
    Continuous (heatUpperBlaschkeBoundary t) := by
  have heq : heatUpperBlaschkeBoundary t = fun r : ℝ =>
      heatBlaschkeMeromorphic t ((r : ℂ) + I) := funext (heatUpperBlaschkeBoundary_eq ht)
  rw [heq]
  unfold heatBlaschkeMeromorphic
  refine continuous_finsetProd _ fun u hu => ?_
  have hu_strip : |u.im| ≤ 1 / 2 :=
    (abs_im_lt_half_of_riemannHeat_eq_zero ht ((mem_heatRightZeroSet ht).mp hu).1).le
  refine Continuous.pow (Continuous.div (by fun_prop) (by fun_prop) fun r => ?_) _
  exact sub_ne_zero_of_abs_im_eq_one (by simp) hu_strip

/-! ### Continuity in the heat time `t > 0` across real and off-axis collisions -/

private theorem norm_prod_sub_prod_le {α : Type*} (S : Finset α) (f g : α → ℂ) {B : ℝ}
    (hB1 : 1 ≤ B) (hf : ∀ i ∈ S, ‖f i‖ ≤ B) (hg : ∀ i ∈ S, ‖g i‖ ≤ B) :
    ‖∏ i ∈ S, f i - ∏ i ∈ S, g i‖ ≤ B ^ S.card * ∑ i ∈ S, ‖f i - g i‖ := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hB0 : 0 ≤ B := by linarith
      have hf' : ∀ i ∈ s, ‖f i‖ ≤ B := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hg' : ∀ i ∈ s, ‖g i‖ ≤ B := fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have hfa : ‖f a‖ ≤ B := hf a (Finset.mem_insert_self a s)
      have hga : ‖g a‖ ≤ B := hg a (Finset.mem_insert_self a s)
      have hPf : ‖∏ i ∈ s, f i‖ ≤ B ^ s.card := by
        calc ‖∏ i ∈ s, f i‖ ≤ ∏ i ∈ s, ‖f i‖ := Finset.norm_prod_le s f
          _ ≤ ∏ _i ∈ s, B := Finset.prod_le_prod (fun _ _ => norm_nonneg _) hf'
          _ = B ^ s.card := Finset.prod_const B
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha,
        Finset.sum_insert ha]
      have hsplit : f a * (∏ i ∈ s, f i) - g a * (∏ i ∈ s, g i) =
          (f a - g a) * (∏ i ∈ s, f i) + g a * ((∏ i ∈ s, f i) - (∏ i ∈ s, g i)) := by ring
      have hpow_le : B ^ s.card ≤ B ^ (s.card + 1) := by
        rw [pow_succ]
        exact le_mul_of_one_le_right (pow_nonneg hB0 _) hB1
      calc ‖f a * (∏ i ∈ s, f i) - g a * (∏ i ∈ s, g i)‖
          = ‖(f a - g a) * (∏ i ∈ s, f i) + g a * ((∏ i ∈ s, f i) - (∏ i ∈ s, g i))‖ := by
            rw [hsplit]
        _ ≤ ‖(f a - g a) * (∏ i ∈ s, f i)‖ + ‖g a * ((∏ i ∈ s, f i) - (∏ i ∈ s, g i))‖ :=
            norm_add_le _ _
        _ = ‖f a - g a‖ * ‖∏ i ∈ s, f i‖ + ‖g a‖ * ‖(∏ i ∈ s, f i) - (∏ i ∈ s, g i)‖ := by
            rw [norm_mul, norm_mul]
        _ ≤ ‖f a - g a‖ * B ^ s.card + B * (B ^ s.card * ∑ i ∈ s, ‖f i - g i‖) :=
            add_le_add (mul_le_mul_of_nonneg_left hPf (norm_nonneg _))
              (mul_le_mul hga (ih hf' hg') (norm_nonneg _) hB0)
        _ ≤ ‖f a - g a‖ * B ^ (s.card + 1) + B ^ (s.card + 1) * ∑ i ∈ s, ‖f i - g i‖ := by
            have h1 : ‖f a - g a‖ * B ^ s.card ≤ ‖f a - g a‖ * B ^ (s.card + 1) :=
              mul_le_mul_of_nonneg_left hpow_le (norm_nonneg _)
            have h2 : B * (B ^ s.card * ∑ i ∈ s, ‖f i - g i‖) =
                B ^ (s.card + 1) * ∑ i ∈ s, ‖f i - g i‖ := by rw [pow_succ]; ring
            linarith
        _ = B ^ (s.card + 1) * (‖f a - g a‖ + ∑ i ∈ s, ‖f i - g i‖) := by ring

private theorem norm_pow_sub_pow_le (a b : ℂ) (m : ℕ) {B : ℝ} (hB1 : 1 ≤ B)
    (ha : ‖a‖ ≤ B) (hb : ‖b‖ ≤ B) :
    ‖a ^ m - b ^ m‖ ≤ B ^ m * ((m : ℝ) * ‖a - b‖) := by
  have h := norm_prod_sub_prod_le (Finset.range m) (fun _ => a) (fun _ => b) hB1
    (fun _ _ => ha) (fun _ _ => hb)
  simpa [Finset.prod_const, Finset.sum_const, nsmul_eq_mul] using h

private def blaschkeTruncFactor (z₀ w : ℂ) : ℂ :=
  if w.im < 0 then (z₀ - conj w) / (z₀ - w) else 1

private theorem norm_blaschkeTruncFactor_le_three {z₀ w : ℂ} (hz₀ : |z₀.im| = 1)
    (hw : |w.im| ≤ 1 / 2) : ‖blaschkeTruncFactor z₀ w‖ ≤ 3 := by
  unfold blaschkeTruncFactor
  split_ifs with hneg
  · exact norm_blaschkeFactor_le_three hw (half_le_norm_sub_of_abs_im_eq_one hz₀ hw)
  · norm_num

private theorem continuousAt_blaschkeTruncFactor {z₀ e : ℂ} (hz₀ : |z₀.im| = 1)
    (he : |e.im| < 1 / 2) : ContinuousAt (blaschkeTruncFactor z₀) e := by
  have hg_cont : ContinuousAt (fun w : ℂ => (z₀ - conj w) / (z₀ - w)) e := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    exact sub_ne_zero_of_abs_im_eq_one hz₀ he.le
  rcases lt_trichotomy e.im 0 with hlt | heq | hgt
  · have hev : blaschkeTruncFactor z₀ =ᶠ[𝓝 e] fun w : ℂ => (z₀ - conj w) / (z₀ - w) := by
      filter_upwards [(isOpen_lt Complex.continuous_im continuous_const).mem_nhds hlt] with w hw
      exact if_pos hw
    exact hg_cont.congr hev.symm
  · rw [Metric.continuousAt_iff] at hg_cont ⊢
    intro ε hε
    obtain ⟨δ, hδ, hδg⟩ := hg_cont ε hε
    have hge1 : (z₀ - conj e) / (z₀ - e) = 1 := by
      have hce : conj e = e := Complex.ext (by simp) (by simp [heq])
      rw [hce, div_self (sub_ne_zero_of_abs_im_eq_one hz₀ he.le)]
    have hhe1 : blaschkeTruncFactor z₀ e = 1 := if_neg (by linarith)
    refine ⟨δ, hδ, fun w hw => ?_⟩
    rw [hhe1]
    unfold blaschkeTruncFactor
    split_ifs with hwneg
    · rw [← hge1]
      exact hδg hw
    · simp [hε]
  · have hev : blaschkeTruncFactor z₀ =ᶠ[𝓝 e] fun _ : ℂ => (1 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_im).mem_nhds hgt] with w hw
      exact if_neg (not_lt.mpr hw.le)
    exact continuousAt_const.congr hev.symm

private theorem heatBlaschkeMeromorphic_eq_prod_superset {s : ℝ} (hs : 0 < s) (z₀ : ℂ)
    {Z : Finset ℂ} (hsub : heatRightZeroSet s ⊆ Z) :
    heatBlaschkeMeromorphic s z₀ =
      ∏ w ∈ Z, (blaschkeTruncFactor z₀ w) ^ zeroMult (riemannHeat s) w := by
  classical
  unfold heatBlaschkeMeromorphic
  have hcongr : (∏ u ∈ heatRightZeroSet s,
      ((z₀ - conj u) / (z₀ - u)) ^ zeroMult (riemannHeat s) u) =
      ∏ u ∈ heatRightZeroSet s, (blaschkeTruncFactor z₀ u) ^ zeroMult (riemannHeat s) u := by
    refine Finset.prod_congr rfl fun u hu => ?_
    have huneg := ((mem_heatRightZeroSet hs).mp hu).2
    unfold blaschkeTruncFactor
    rw [if_pos huneg]
  rw [hcongr]
  exact Finset.prod_subset hsub fun w _ hw_not => by
    by_cases hw0 : riemannHeat s w = 0
    · have hnotneg : ¬ w.im < 0 := fun hneg =>
        hw_not ((mem_heatRightZeroSet hs).mpr ⟨hw0, hneg⟩)
      unfold blaschkeTruncFactor
      rw [if_neg hnotneg, one_pow]
    · rw [zeroMult_riemannHeat_eq_zero hs.le hw0, pow_zero]

private def clusterPerturbConst (N M : ℕ) : ℝ :=
  ((3 : ℝ) ^ M) ^ N * (N : ℝ) * (((3 : ℝ) ^ M) ^ M * (M : ℝ) * ((3 : ℝ) ^ M * (M : ℝ)))

private theorem clusterPerturbConst_nonneg (N M : ℕ) : 0 ≤ clusterPerturbConst N M := by
  unfold clusterPerturbConst
  positivity

private theorem norm_prod_cluster_pow_sub_le (E : Finset ℂ) (W : ℂ → Finset ℂ)
    (ms mt : ℂ → ℕ) (h : ℂ → ℂ) (M : ℕ) {η : ℝ} (hη : 0 ≤ η)
    (hM : ∀ e ∈ E, mt e ≤ M)
    (hsum : ∀ e ∈ E, ∑ w ∈ W e, ms w = mt e)
    (h1 : ∀ e ∈ E, ∀ w ∈ W e, 1 ≤ ms w)
    (hhe : ∀ e ∈ E, ‖h e‖ ≤ 3)
    (hhw : ∀ e ∈ E, ∀ w ∈ W e, ‖h w‖ ≤ 3)
    (hdiff : ∀ e ∈ E, ∀ w ∈ W e, ‖h w - h e‖ ≤ η) :
    ‖(∏ e ∈ E, ∏ w ∈ W e, (h w) ^ ms w) - ∏ e ∈ E, (h e) ^ mt e‖ ≤
      clusterPerturbConst E.card M * η := by
  classical
  have hB1 : (1 : ℝ) ≤ (3 : ℝ) ^ M := one_le_pow₀ (by norm_num)
  have hB0 : (0 : ℝ) ≤ (3 : ℝ) ^ M := zero_le_one.trans hB1
  have hBM0 : 0 ≤ ((3 : ℝ) ^ M) ^ M := pow_nonneg hB0 M
  have hBN0 : 0 ≤ ((3 : ℝ) ^ M) ^ E.card := pow_nonneg hB0 E.card
  have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hBMη0 : 0 ≤ (3 : ℝ) ^ M * (M : ℝ) * η := mul_nonneg (mul_nonneg hB0 hM0) hη
  have hf_le : ∀ e ∈ E, ‖∏ w ∈ W e, (h w) ^ ms w‖ ≤ (3 : ℝ) ^ M := fun e he => by
    calc ‖∏ w ∈ W e, (h w) ^ ms w‖
        ≤ ∏ w ∈ W e, ‖(h w) ^ ms w‖ := Finset.norm_prod_le _ _
      _ ≤ ∏ w ∈ W e, (3 : ℝ) ^ ms w := Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun w hw => by
          rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hhw e he w hw) _
      _ = (3 : ℝ) ^ ∑ w ∈ W e, ms w := Finset.prod_pow_eq_pow_sum _ _ _
      _ = (3 : ℝ) ^ mt e := by rw [hsum e he]
      _ ≤ (3 : ℝ) ^ M := pow_le_pow_right₀ (by norm_num) (hM e he)
  have hg_le : ∀ e ∈ E, ‖(h e) ^ mt e‖ ≤ (3 : ℝ) ^ M := fun e he => by
    rw [norm_pow]
    exact (pow_le_pow_left₀ (norm_nonneg _) (hhe e he) _).trans
      (pow_le_pow_right₀ (by norm_num) (hM e he))
  have he_diff : ∀ e ∈ E,
      ‖(∏ w ∈ W e, (h w) ^ ms w) - (h e) ^ mt e‖ ≤
        ((3 : ℝ) ^ M) ^ M * (M : ℝ) * ((3 : ℝ) ^ M * (M : ℝ) * η) := fun e he => by
    have hge_prod : (h e) ^ mt e = ∏ w ∈ W e, (h e) ^ ms w := by
      rw [← hsum e he, ← Finset.prod_pow_eq_pow_sum]
    rw [hge_prod]
    have hWcard : (W e).card ≤ M := by
      calc (W e).card = ∑ _w ∈ W e, 1 := Finset.card_eq_sum_ones _
        _ ≤ ∑ w ∈ W e, ms w := Finset.sum_le_sum (h1 e he)
        _ = mt e := hsum e he
        _ ≤ M := hM e he
    have hmw_le : ∀ w ∈ W e, ms w ≤ M := fun w hw =>
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hw).trans
        ((hsum e he).le.trans (hM e he))
    have hfw : ∀ w ∈ W e, ‖(h w) ^ ms w‖ ≤ (3 : ℝ) ^ M := fun w hw => by
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) (hhw e he w hw) _).trans
        (pow_le_pow_right₀ (by norm_num) (hmw_le w hw))
    have hgw : ∀ w ∈ W e, ‖(h e) ^ ms w‖ ≤ (3 : ℝ) ^ M := fun w hw => by
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) (hhe e he) _).trans
        (pow_le_pow_right₀ (by norm_num) (hmw_le w hw))
    have hw_diff : ∀ w ∈ W e, ‖(h w) ^ ms w - (h e) ^ ms w‖ ≤ (3 : ℝ) ^ M * (M : ℝ) * η :=
      fun w hw => by
        have hpow := norm_pow_sub_pow_le (h w) (h e) (ms w) (by norm_num : (1 : ℝ) ≤ 3)
          (hhw e he w hw) (hhe e he)
        have h3le : (3 : ℝ) ^ ms w ≤ (3 : ℝ) ^ M := pow_le_pow_right₀ (by norm_num) (hmw_le w hw)
        have hm_cast : (ms w : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmw_le w hw
        calc ‖(h w) ^ ms w - (h e) ^ ms w‖
            ≤ (3 : ℝ) ^ ms w * ((ms w : ℝ) * ‖h w - h e‖) := hpow
          _ ≤ (3 : ℝ) ^ M * ((M : ℝ) * η) :=
              mul_le_mul h3le
                (mul_le_mul hm_cast (hdiff e he w hw) (norm_nonneg _) (Nat.cast_nonneg _))
                (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) hB0
          _ = (3 : ℝ) ^ M * (M : ℝ) * η := by ring
    have hprod_W := norm_prod_sub_prod_le (W e) (fun w => (h w) ^ ms w) (fun w => (h e) ^ ms w)
      hB1 hfw hgw
    have hB_card : ((3 : ℝ) ^ M) ^ (W e).card ≤ ((3 : ℝ) ^ M) ^ M := pow_le_pow_right₀ hB1 hWcard
    have hW_cast : ((W e).card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hWcard
    calc ‖(∏ w ∈ W e, (h w) ^ ms w) - ∏ w ∈ W e, (h e) ^ ms w‖
        ≤ ((3 : ℝ) ^ M) ^ (W e).card * ∑ w ∈ W e, ‖(h w) ^ ms w - (h e) ^ ms w‖ := hprod_W
      _ ≤ ((3 : ℝ) ^ M) ^ M * ∑ _w ∈ W e, ((3 : ℝ) ^ M * (M : ℝ) * η) :=
          mul_le_mul hB_card (Finset.sum_le_sum hw_diff)
            (Finset.sum_nonneg fun _ _ => norm_nonneg _) hBM0
      _ = ((3 : ℝ) ^ M) ^ M * (((W e).card : ℝ) * ((3 : ℝ) ^ M * (M : ℝ) * η)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((3 : ℝ) ^ M) ^ M * ((M : ℝ) * ((3 : ℝ) ^ M * (M : ℝ) * η)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hW_cast hBMη0) hBM0
      _ = ((3 : ℝ) ^ M) ^ M * (M : ℝ) * ((3 : ℝ) ^ M * (M : ℝ) * η) := by ring
  have houter := norm_prod_sub_prod_le E (fun e => ∏ w ∈ W e, (h w) ^ ms w)
    (fun e => (h e) ^ mt e) hB1 hf_le hg_le
  calc ‖(∏ e ∈ E, ∏ w ∈ W e, (h w) ^ ms w) - ∏ e ∈ E, (h e) ^ mt e‖
      ≤ ((3 : ℝ) ^ M) ^ E.card * ∑ e ∈ E, ‖(∏ w ∈ W e, (h w) ^ ms w) - (h e) ^ mt e‖ := houter
    _ ≤ ((3 : ℝ) ^ M) ^ E.card *
          ∑ _e ∈ E, (((3 : ℝ) ^ M) ^ M * (M : ℝ) * ((3 : ℝ) ^ M * (M : ℝ) * η)) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum he_diff) hBN0
    _ = clusterPerturbConst E.card M * η := by
        rw [Finset.sum_const, nsmul_eq_mul]
        unfold clusterPerturbConst
        ring

private theorem exists_enclosing_zeroFinset_riemannHeat {t₁ : ℝ} (ht₁ : 0 < t₁) :
    ∃ (R : ℝ) (E : Finset ℂ), 0 < R ∧
      (∀ w ∈ sphere (0 : ℂ) R, riemannHeat t₁ w ≠ 0) ∧
      (∀ z, z ∈ E ↔ riemannHeat t₁ z = 0 ∧ ‖z‖ < R) ∧
      (∀ s, t₁ / 2 ≤ s → ∀ z, riemannHeat s z = 0 → z.im ≠ 0 → ‖z‖ < R) := by
  classical
  have ht₀ : 0 < min (t₁ / 2) (1 / 8) := lt_min (by linarith) (by norm_num)
  obtain ⟨X₀, hX₀⟩ := exists_riemannHeat_zeros_real_uniform (t₀ := min (t₁ / 2) (1 / 8)) ht₀
  have hinside : ∀ s, t₁ / 2 ≤ s → ∀ z, riemannHeat s z = 0 → z.im ≠ 0 → ‖z‖ < max X₀ 0 + 1 := by
    intro s hs z hz him
    have ht₀_s : min (t₁ / 2) (1 / 8) ≤ s := (min_le_left _ _).trans hs
    have hs0 : 0 < s := ht₀.trans_le ht₀_s
    rcases le_or_gt s (1 / 8) with hs8 | hs8
    · have hre : |z.re| < X₀ := lt_of_not_ge fun h => him (hX₀ s ⟨ht₀_s, hs8⟩ z hz h)
      have him2 := abs_im_le_half_of_riemannHeat_eq_zero hs0 hz
      have h3 := Complex.norm_le_abs_re_add_abs_im z
      linarith [le_max_left X₀ 0]
    · exact absurd (riemannHeat_zeros_real hs8.le hz) him
  have han : AnalyticOnNhd ℂ (riemannHeat t₁) (closedBall 0 (max X₀ 0 + 2)) := fun z _ =>
    (differentiable_riemannHeat ht₁.le).analyticAt z
  have hfin := finite_zeros_closedBall han (fun z _ h =>
    analyticOrderAt_riemannHeat_ne_top ht₁.le z (analyticOrderAt_eq_top.mpr h))
  obtain ⟨R, hRI, hRn⟩ :=
    (Set.Ioo_infinite (by linarith : max X₀ 0 + 1 < max X₀ 0 + 2)).exists_notMem_finset
      (hfin.toFinset.image (fun z => ‖z‖))
  have hRX : max X₀ 0 + 1 < R := hRI.1
  have hRpos : 0 < R := by linarith [le_max_right X₀ 0]
  have hsphR : ∀ w ∈ sphere (0 : ℂ) R, riemannHeat t₁ w ≠ 0 := by
    intro w hw h0
    rw [mem_sphere, dist_zero_right] at hw
    apply hRn
    refine Finset.mem_image.mpr ⟨w, ?_, hw⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨by rw [mem_closedBall, dist_zero_right]; linarith [hRI.2], h0⟩
  refine ⟨R, hfin.toFinset.filter (fun z => ‖z‖ < R), hRpos, hsphR, ?_, ?_⟩
  · intro z
    rw [Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨fun h => ⟨h.1.2, h.2⟩,
      fun h => ⟨⟨by rw [mem_closedBall, dist_zero_right]; linarith [hRI.2], h.1⟩, h.2⟩⟩
  · intro s hs z hz him
    exact (hinside s hs z hz him).trans hRX

/-- **Continuity of `heatBlaschkeMeromorphic s z₀` in `s ∈ (0, ∞)`** on the horizontal lines
`|Im z₀| = 1`: as `s → t₁ > 0`, lower-half-plane zeros colliding on `ℝ` satisfy
`(z₀ − w̄)/(z₀ − w) → (z₀ − x)/(z₀ − x) = 1`, while off-axis zeros conserve total multiplicity in
each isolating disc. -/
theorem tendsto_heatBlaschkeMeromorphic_nhds {t₁ : ℝ} (ht₁ : 0 < t₁) {z₀ : ℂ}
    (hz₀ : |z₀.im| = 1) :
    Tendsto (fun s => heatBlaschkeMeromorphic s z₀) (𝓝 t₁)
      (𝓝 (heatBlaschkeMeromorphic t₁ z₀)) := by
  classical
  obtain ⟨R, E, hRpos, hsphR, hmemE, hinsideR⟩ := exists_enclosing_zeroFinset_riemannHeat ht₁
  have hZ₁_sub_E : heatRightZeroSet t₁ ⊆ E := fun z hz => by
    obtain ⟨hz0, hzneg⟩ := (mem_heatRightZeroSet ht₁).mp hz
    exact (hmemE z).mpr ⟨hz0, hinsideR t₁ (by linarith) z hz0 hzneg.ne⟩
  obtain ⟨M₁, hM₁_def⟩ : ∃ M₁ : ℕ, M₁ = ∑ e ∈ E, zeroMult (riemannHeat t₁) e := ⟨_, rfl⟩
  have he_le_M₁ : ∀ e ∈ E, zeroMult (riemannHeat t₁) e ≤ M₁ := fun e he => by
    rw [hM₁_def]; exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) he
  clear hM₁_def
  have hK0 : 0 ≤ clusterPerturbConst E.card M₁ := clusterPerturbConst_nonneg E.card M₁
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = ε / (clusterPerturbConst E.card M₁ + 1) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hη_def]; exact div_pos hε (by linarith)
  have hKη_lt : clusterPerturbConst E.card M₁ * η < ε := by
    rw [hη_def, mul_div_assoc', div_lt_iff₀ (by linarith)]
    nlinarith
  clear hη_def
  have hδe_ex : ∀ e ∈ E, ∃ δe > 0, ∀ w ∈ ball e δe,
      ‖blaschkeTruncFactor z₀ w - blaschkeTruncFactor z₀ e‖ ≤ η := by
    intro e he
    have he_im := abs_im_lt_half_of_riemannHeat_eq_zero ht₁ ((hmemE e).mp he).1
    obtain ⟨δe, hδe, hprop⟩ :=
      (Metric.continuousAt_iff.mp (continuousAt_blaschkeTruncFactor hz₀ he_im)) η hη
    exact ⟨δe, hδe, fun w hw => (dist_eq_norm (blaschkeTruncFactor z₀ w)
      (blaschkeTruncFactor z₀ e) ▸ hprop (mem_ball.mp hw)).le⟩
  choose! δe hδe hδe_bound using hδe_ex
  choose ρ₀ hρ₀ hρ₀prop using fun e => eventually_zeroSumBall_riemannHeat_eq ht₁ e
  obtain ⟨d, hd, hdsep⟩ := exists_pos_sep E
  obtain ⟨rad, hrad_def⟩ : ∃ rad : ℂ → ℝ,
      rad = fun e => min (min (ρ₀ e) (δe e / 2)) (min (d / 3) ((R - ‖e‖) / 2)) := ⟨_, rfl⟩
  have hrad_pos : ∀ e ∈ E, 0 < rad e := fun e he => by
    have heR := ((hmemE e).mp he).2
    rw [hrad_def]
    exact lt_min (lt_min (hρ₀ e) (half_pos (hδe e he))) (lt_min (by positivity) (by linarith))
  have hrad_ρ₀ : ∀ e, rad e ≤ ρ₀ e := fun e => by
    rw [hrad_def]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hrad_δe : ∀ e ∈ E, rad e < δe e := fun e he => by
    rw [hrad_def]
    exact lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _)) (half_lt_self (hδe e he))
  have hrad_d : ∀ e, rad e ≤ d / 3 := fun e => by
    rw [hrad_def]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hrad_R : ∀ e, rad e ≤ (R - ‖e‖) / 2 := fun e => by
    rw [hrad_def]; exact (min_le_right _ _).trans (min_le_right _ _)
  clear hrad_def
  have hdisj : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → Disjoint (ball e (rad e)) (ball e' (rad e')) := by
    intro e he e' he' hne
    refine Set.disjoint_left.mpr fun w hw hw' => ?_
    have h1 := hdsep e he e' he' hne
    have h2 : dist e e' ≤ dist e w + dist w e' := dist_triangle _ _ _
    rw [mem_ball] at hw hw'
    rw [dist_comm] at hw
    linarith [hrad_d e, hrad_d e']
  have hinR : ∀ e ∈ E, ∀ w ∈ ball e (rad e), w ∈ ball (0 : ℂ) R := by
    intro e he w hw
    have heR := ((hmemE e).mp he).2
    rw [mem_ball, dist_eq_norm] at hw
    rw [mem_ball, dist_zero_right]
    have := norm_le_norm_add_norm_sub' w e
    linarith [hrad_R e]
  have hbig := eventually_zeroSumBall_riemannHeat_eq_of_sphere ht₁ hRpos hsphR
  have hsmall : ∀ᶠ s in 𝓝 t₁, ∀ e ∈ E,
      zeroSumBall (riemannHeat s) e (rad e) = (zeroMult (riemannHeat t₁) e : ℂ) ∧
        ∀ w ∈ sphere e (rad e), riemannHeat s w ≠ 0 :=
    (Filter.eventually_all_finset E).mpr fun e he =>
      (hρ₀prop e (rad e) (hrad_pos e he) (hrad_ρ₀ e)).2.2
  have hcountE : zeroSumBall (riemannHeat t₁) 0 R =
      ∑ e ∈ E, (zeroMult (riemannHeat t₁) e : ℂ) := by
    obtain ⟨Z, hZb, hZz, hZs⟩ := exists_zeroSet_zeroSumBall hRpos (by linarith : R < 2 * R)
      isOpen_univ (subset_univ _) (differentiable_riemannHeat ht₁.le).differentiableOn hsphR
    have hZE : Z = E := by
      ext z
      refine ⟨fun hz => ?_, fun hz => ?_⟩
      · have hb := hZb z hz
        rw [mem_ball, dist_zero_right] at hb
        exact (hmemE z).mpr ⟨(hZz z (hZb z hz)).mpr hz, hb⟩
      · obtain ⟨h0, hR⟩ := (hmemE z).mp hz
        exact (hZz z (by rw [mem_ball, dist_zero_right]; exact hR)).mp h0
    rw [hZs, hZE]
  have hs_gt : ∀ᶠ s in 𝓝 t₁, t₁ / 2 < s := lt_mem_nhds (by linarith)
  filter_upwards [hbig, hsmall, hs_gt] with s ⟨hbs, hbsph⟩ hsm hs2
  have hs0 : 0 < s := by linarith
  have hdiffs := differentiable_riemannHeat hs0.le
  obtain ⟨Zb, hZbb, hZbz, hZbs⟩ := exists_zeroSet_zeroSumBall hRpos (by linarith : R < 2 * R)
    isOpen_univ (subset_univ _) hdiffs.differentiableOn hbsph
  have hZe : ∀ e ∈ E, ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball e (rad e)) ∧
      (∀ z ∈ ball e (rad e), riemannHeat s z = 0 ↔ z ∈ Z) ∧
      zeroSumBall (riemannHeat s) e (rad e) = ∑ ρ ∈ Z, (zeroMult (riemannHeat s) ρ : ℂ) :=
    fun e he => exists_zeroSet_zeroSumBall (hrad_pos e he)
      (by linarith [hrad_pos e he] : rad e < 2 * rad e) isOpen_univ (subset_univ _)
      hdiffs.differentiableOn (hsm e he).2
  choose! W hWb hWz hWs using hZe
  have hWsub : ∀ e ∈ E, W e ⊆ Zb := fun e he z hz =>
    (hZbz z (hinR e he z (hWb e he z hz))).mp ((hWz e he z (hWb e he z hz)).mpr hz)
  have hWdisj : (E : Set ℂ).PairwiseDisjoint W := fun e he e' he' hne =>
    Finset.disjoint_left.mpr fun z hz hz' =>
      (Set.disjoint_left.mp (hdisj e he e' he' hne)) (hWb e he z hz) (hWb e' he' z hz')
  have hsum_e : ∀ e ∈ E, ∑ z ∈ W e, zeroMult (riemannHeat s) z =
      zeroMult (riemannHeat t₁) e := by
    intro e he
    have h1 : ((∑ z ∈ W e, zeroMult (riemannHeat s) z : ℕ) : ℂ) =
        (zeroMult (riemannHeat t₁) e : ℂ) := by
      push_cast
      rw [← hWs e he, (hsm e he).1]
    exact_mod_cast h1
  have hsumN : ∑ z ∈ Zb, zeroMult (riemannHeat s) z =
      ∑ e ∈ E, ∑ z ∈ W e, zeroMult (riemannHeat s) z := by
    have h1 : ((∑ z ∈ Zb, zeroMult (riemannHeat s) z : ℕ) : ℂ) =
        ((∑ e ∈ E, ∑ z ∈ W e, zeroMult (riemannHeat s) z : ℕ) : ℂ) := by
      push_cast
      rw [← hZbs, hbs, hcountE]
      exact Finset.sum_congr rfl fun e he => by rw [← hWs e he, (hsm e he).1]
    exact_mod_cast h1
  have hcov := subset_biUnion_of_sum_eq (fun z hz => one_le_zeroMult_riemannHeat hs0.le
    ((hZbz z (hZbb z hz)).mpr hz)) hWsub hWdisj hsumN
  have hZs_sub : heatRightZeroSet s ⊆ E.biUnion W := by
    intro w hw
    obtain ⟨hw0, hwneg⟩ := (mem_heatRightZeroSet hs0).mp hw
    have hwR : w ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right]
      exact hinsideR s hs2.le w hw0 hwneg.ne
    exact hcov ((hZbz w hwR).mp hw0)
  have hBs : heatBlaschkeMeromorphic s z₀ =
      ∏ e ∈ E, ∏ w ∈ W e, (blaschkeTruncFactor z₀ w) ^ zeroMult (riemannHeat s) w := by
    rw [heatBlaschkeMeromorphic_eq_prod_superset hs0 z₀ hZs_sub, Finset.prod_biUnion hWdisj]
  have hBt₁ : heatBlaschkeMeromorphic t₁ z₀ =
      ∏ e ∈ E, (blaschkeTruncFactor z₀ e) ^ zeroMult (riemannHeat t₁) e :=
    heatBlaschkeMeromorphic_eq_prod_superset ht₁ z₀ hZ₁_sub_E
  rw [dist_eq_norm, hBs, hBt₁]
  refine (norm_prod_cluster_pow_sub_le E W (zeroMult (riemannHeat s))
    (zeroMult (riemannHeat t₁)) (blaschkeTruncFactor z₀) M₁ hη.le he_le_M₁ hsum_e
    (fun e he w hw => one_le_zeroMult_riemannHeat hs0.le ((hWz e he w (hWb e he w hw)).mpr hw))
    (fun e he => norm_blaschkeTruncFactor_le_three hz₀
      (abs_im_le_half_of_riemannHeat_eq_zero ht₁ ((hmemE e).mp he).1))
    (fun e he w hw => norm_blaschkeTruncFactor_le_three hz₀
      (abs_im_le_half_of_riemannHeat_eq_zero hs0 ((hWz e he w (hWb e he w hw)).mpr hw)))
    (fun e he w hw => hδe_bound e he w
      (ball_subset_ball (hrad_δe e he).le (hWb e he w hw)))).trans_lt hKη_lt

theorem tendsto_heatLowerBlaschkeBoundary_nhds {t₁ : ℝ} (ht₁ : 0 < t₁) (r : ℝ) :
    Tendsto (fun s => heatLowerBlaschkeBoundary s r) (𝓝 t₁)
      (𝓝 (heatLowerBlaschkeBoundary t₁ r)) := by
  rw [heatLowerBlaschkeBoundary_eq ht₁ r]
  refine (tendsto_heatBlaschkeMeromorphic_nhds ht₁ (z₀ := (r : ℂ) - I) (by simp)).congr' ?_
  filter_upwards [lt_mem_nhds ht₁] with s hs
  exact (heatLowerBlaschkeBoundary_eq hs r).symm

theorem tendsto_heatUpperBlaschkeBoundary_nhds {t₁ : ℝ} (ht₁ : 0 < t₁) (r : ℝ) :
    Tendsto (fun s => heatUpperBlaschkeBoundary s r) (𝓝 t₁)
      (𝓝 (heatUpperBlaschkeBoundary t₁ r)) := by
  rw [heatUpperBlaschkeBoundary_eq ht₁ r]
  refine (tendsto_heatBlaschkeMeromorphic_nhds ht₁ (z₀ := (r : ℂ) + I) (by simp)).congr' ?_
  filter_upwards [lt_mem_nhds ht₁] with s hs
  exact (heatUpperBlaschkeBoundary_eq hs r).symm

end GaloisForLFunctions.AdelicKreinGeometry
