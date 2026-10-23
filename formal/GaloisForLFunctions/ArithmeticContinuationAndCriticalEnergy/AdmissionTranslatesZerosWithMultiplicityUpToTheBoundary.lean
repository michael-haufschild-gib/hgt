import GaloisForLFunctions.RHTower.PMPowerDampedMobiusCriterion
import GaloisForLFunctions.RHTower.ReceiverDampingsAccumulateAboveTheZeros
import GaloisForLFunctions.HTGeometry.HalfLineLaplaceL2
import GaloisForLFunctions.SquareRootThreshold.TheReceiverDampingReadsTheZeroWidth

/-!
# Admission translates zeros with multiplicity, up to the boundary line

Let `ε ∈ (0, ½]` be an admissible damping of the damped Möbius receiver (`ε ∈ receiverDampings`).
Then every zero `ρ` of `ζ` with `½ + ε ≤ Re ρ < 1` is translated to a zero `ρ − ε` of at least the
same multiplicity (`analyticOrderAt_le_analyticOrderAt_sub_of_mem_receiverDampings`). Previously
only the translation of the zero itself was known, and only in the open region `Re ρ > ½ + ε`; the
multiplicity and the boundary line `Re ρ = ½ + ε` are new. On the boundary the translate lies on
the critical line (`riemannZeta_criticalLine_eq_zero_of_mem_receiverDampings`).

**The boundary of the zero width.** If `Θ = sup Re ρ > ½` is attained at a zero `ρ₀`, admission at
the width `Θ − ½` forces `½ + i Im ρ₀` to be a critical zero of multiplicity at least that of `ρ₀`
(`analyticOrderAt_le_of_zetaZeroAbscissa_mem_receiverDampings`). When an extremal zero casts no such
critical-line shadow, the admissible dampings at or above the width are exactly `(Θ − ½, ∞)`: the
threshold of admission is not attained (`receiverDampings_inter_Ici_eq_Ioi`).

**Mechanism.** The cleared Mellin identity `s Z(s + ε) M(s) = (s + ε − 1)(1 − 2^{1−s}) ζ(s)`,
`Z(w) = (w − 1)ζ(w)`, holds on `½ < Re s < 1`, and the Mellin transform of the admitted `L²` source,
supported on `(0, 1]`, is the Laplace transform of an `L²` datum, so
`|M(s)| ≤ C (2(Re s − ½))^{−1/2}` (`exists_norm_mellin_pmPowerDampedFermiSource_le`). Approaching
`s₁ = ρ − ε` from the right, `|Z(ρ + u)| = O(uⁿ)` against `|ζ(s₁ + u)| ≍ u^k` forces `k ≥ n`: the
loss `u^{−1/2}` of the Mellin transform is less than one power of `u`.
-/

open Complex Set Filter Topology MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

open _root_.RHTower

set_option autoImplicit false

/-- **The Mellin transform of an admitted source is `O((Re s − ½)^{−1/2})`.** -/
theorem exists_norm_mellin_pmPowerDampedFermiSource_le {ε : ℝ}
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi 0))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 1 / 2 < s.re →
      ‖mellin (pmPowerDampedFermiSource ε) s‖ ≤ C / Real.sqrt (2 * (s.re - 1 / 2)) := by
  have hsupp : ∀ t : ℝ, 1 < t → pmPowerDampedFermiSource ε t = 0 :=
    fun _ ht => pmPowerDampedFermiSource_eq_zero_of_one_lt ε ht
  have hhead : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioo (0 : ℝ) 1)) :=
    hf.mono_measure (Measure.restrict_mono Ioo_subset_Ioi_self le_rfl)
  have hlp := memLp_two_logChartHead (by norm_num : (0 : ℝ) < 1) hhead
  refine ⟨HTGeometry.rayL2Norm (logChartHead 1 (pmPowerDampedFermiSource ε)),
    HTGeometry.rayL2Norm_nonneg _, fun s hs => ?_⟩
  rw [pm_mellin_eq_head_laplace hsupp s]
  have hre : (s - 1 / 2).re = s.re - 1 / 2 := by simp
  have h := HTGeometry.norm_laplaceRay_le hlp (w := s - 1 / 2) (by rw [hre]; linarith)
  rwa [hre] at h

theorem analyticAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt
    (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)

/-- **The translation estimate.** If the source at damping `ε ∈ (0, ½]` is admitted and `ζ` vanishes
to order at least `n` at `ρ`, `½ + ε ≤ Re ρ < 1`, then it vanishes to order at least `n` at `ρ − ε`. -/
theorem natCast_le_analyticOrderAt_sub_of_memLp {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hf : MemLp (pmPowerDampedFermiSource ε) 2 (volume.restrict (Ioi 0)))
    {ρ : ℂ} (hρ : 1 / 2 + ε ≤ ρ.re) (hρ1 : ρ.re < 1) {n : ℕ}
    (hn : (n : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    (n : ℕ∞) ≤ analyticOrderAt riemannZeta (ρ - ε) := by
  set s₁ : ℂ := ρ - ε with hs₁
  have hs₁re : s₁.re = ρ.re - ε := by simp [hs₁]
  have hρne : ρ ≠ 1 := fun h => by rw [h, one_re] at hρ1; exact lt_irrefl _ hρ1
  have hs₁ne : s₁ ≠ 1 := fun h => by rw [h, one_re] at hs₁re; linarith
  by_contra hlt
  push Not at hlt
  obtain ⟨k, hk⟩ : ∃ k : ℕ, analyticOrderAt riemannZeta s₁ = k :=
    ⟨_, (ENat.coe_toNat (ne_top_of_lt hlt)).symm⟩
  have hkn : k < n := by rw [hk] at hlt; exact_mod_cast hlt
  obtain ⟨h, hh, hh0, hζh⟩ := ((analyticAt_riemannZeta_of_ne_one hs₁ne).analyticOrderAt_eq_natCast).mp hk
  obtain ⟨g, hg, hζg⟩ := (natCast_le_analyticOrderAt (analyticAt_riemannZeta_of_ne_one hρne)).mp hn
  obtain ⟨C, hC0, hC⟩ := exists_norm_mellin_pmPowerDampedFermiSource_le hf
  set R : ℂ → ℂ := fun s => (s + (ε : ℂ) - 1) * (1 - (2 : ℂ) ^ (1 - s)) with hR
  -- the two paths `u ↦ s₁ + u`, `u ↦ ρ + u`
  have hpath₁ : Tendsto (fun u : ℝ => s₁ + (u : ℂ)) (𝓝[>] 0) (𝓝 s₁) := by
    have : Tendsto (fun u : ℝ => s₁ + (u : ℂ)) (𝓝 0) (𝓝 (s₁ + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto (0 : ℝ)
    rw [Complex.ofReal_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hpath : Tendsto (fun u : ℝ => ρ + (u : ℂ)) (𝓝[>] 0) (𝓝 ρ) := by
    have : Tendsto (fun u : ℝ => ρ + (u : ℂ)) (𝓝 0) (𝓝 (ρ + ((0 : ℝ) : ℂ))) :=
      (continuous_const.add Complex.continuous_ofReal).tendsto (0 : ℝ)
    rw [Complex.ofReal_zero, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  -- `R h` is continuous at `s₁`
  have hRcont : ContinuousAt (fun s => R s * h s) s₁ := by
    have hpow : ContinuousAt (fun s : ℂ => (2 : ℂ) ^ (1 - s)) s₁ := by
      simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
      exact (continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).continuousAt
    exact (((continuousAt_id.add continuousAt_const).sub continuousAt_const).mul
      (continuousAt_const.sub hpow)).mul hh.continuousAt
  have hlim1 : Tendsto (fun u : ℝ => R (s₁ + u) * h (s₁ + u)) (𝓝[>] 0) (𝓝 (R s₁ * h s₁)) :=
    hRcont.tendsto.comp hpath₁
  -- the same function tends to `0`
  set A : ℝ := (‖s₁‖ + 1) * (‖ρ - 1‖ + 1) * (‖g ρ‖ + 1) * C with hA
  have hA0 : 0 ≤ A := by positivity
  have hbound : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ),
      ‖R (s₁ + (u : ℂ)) * h (s₁ + (u : ℂ))‖ ≤ A * Real.sqrt u := by
    have hE1 : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), u ∈ Ioo 0 (min (1 / 2) ε) :=
      Ioo_mem_nhdsGT (lt_min (by norm_num) hε0)
    have hE2 := hpath₁.eventually hζh
    have hE3 := hpath.eventually hζg
    have hE4 : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), ‖g (ρ + (u : ℂ))‖ ≤ ‖g ρ‖ + 1 := by
      have := hpath.eventually (hg.continuousAt.eventually (Metric.ball_mem_nhds (g ρ) one_pos))
      filter_upwards [this] with u hu
      rw [dist_eq_norm] at hu
      have := norm_sub_norm_le (g (ρ + (u : ℂ))) (g ρ)
      linarith
    have hE5 := hpath.eventually (zetaResidueUnit_eventuallyEq hρne)
    filter_upwards [hE1, hE2, hE3, hE4, hE5] with u hu hζ1 hζ2 hgu hZ
    obtain ⟨hu0, hu1⟩ := hu
    have hu12 : u < 1 / 2 := lt_of_lt_of_le hu1 (min_le_left _ _)
    have huε : u < ε := lt_of_lt_of_le hu1 (min_le_right _ _)
    set s : ℂ := s₁ + u with hs
    have hsre : s.re = ρ.re - ε + u := by simp [hs, hs₁re]
    have hstrip : 1 / 2 < s.re ∧ s.re < 1 := by constructor <;> linarith
    have hsε : s + (ε : ℂ) = ρ + u := by rw [hs, hs₁]; ring
    have hid := pmPowerDamped_cleared_mellin ε hε0 hε1 hf hstrip
    rw [hsε] at hid
    -- the local forms
    have hz1 : riemannZeta s = (u : ℂ) ^ k * h s := by
      rw [hζ1]; simp [hs, smul_eq_mul]
    have hz2 : riemannZeta (ρ + u) = (u : ℂ) ^ n * g (ρ + u) := by
      rw [hζ2]; simp [smul_eq_mul]
    have hZu : zetaResidueUnit (ρ + u) = (ρ + u - 1) * ((u : ℂ) ^ n * g (ρ + u)) := by
      rw [hZ, hz2]
    -- `R(s) h(s) = s Z(ρ + u) M(s) / u^k`
    have hu0C : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
    have hkey : R s * h s = s * zetaResidueUnit (ρ + u) *
        mellin (pmPowerDampedFermiSource ε) s / (u : ℂ) ^ k := by
      rw [hid, hz1, eq_div_iff (pow_ne_zero k hu0C)]
      simp only [hR]
      ring
    rw [hkey, hZu, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]
    -- the factors
    have hs1 : ‖s‖ ≤ ‖s₁‖ + 1 := by
      rw [hs]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]
      linarith
    have hs2 : ‖ρ + (u : ℂ) - 1‖ ≤ ‖ρ - 1‖ + 1 := by
      rw [show ρ + (u : ℂ) - 1 = (ρ - 1) + u by ring]
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu0]
      linarith
    have hM : ‖mellin (pmPowerDampedFermiSource ε) s‖ ≤ C / Real.sqrt (2 * u) := by
      refine (hC s hstrip.1).trans ?_
      have h2u : 0 < 2 * u := by linarith
      exact div_le_div_of_nonneg_left hC0 (Real.sqrt_pos.mpr h2u)
        (Real.sqrt_le_sqrt (by rw [hsre]; linarith))
    have hpow : u ^ n / u ^ k ≤ u := by
      rw [div_le_iff₀ (pow_pos hu0 k), ← pow_succ']
      exact pow_le_pow_of_le_one hu0.le (by linarith) (by omega)
    have hsqrt : u / Real.sqrt (2 * u) ≤ Real.sqrt u := by
      have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
      rw [div_le_iff₀ (Real.sqrt_pos.mpr (by linarith)), Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      have h2 : 1 ≤ Real.sqrt 2 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
      have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
      nlinarith
    have hfac : 0 ≤ ‖g (ρ + u)‖ := norm_nonneg _
    calc ‖s‖ * (‖ρ + (u : ℂ) - 1‖ * (u ^ n * ‖g (ρ + u)‖)) *
          ‖mellin (pmPowerDampedFermiSource ε) s‖ / u ^ k
        ≤ (‖s₁‖ + 1) * ((‖ρ - 1‖ + 1) * (u ^ n * (‖g ρ‖ + 1))) * (C / Real.sqrt (2 * u)) /
            u ^ k := by
          gcongr
      _ = A * ((u ^ n / u ^ k) / Real.sqrt (2 * u)) := by rw [hA]; ring
      _ ≤ A * (u / Real.sqrt (2 * u)) := by
          gcongr
      _ ≤ A * Real.sqrt u := mul_le_mul_of_nonneg_left hsqrt hA0
  have hlim0 : Tendsto (fun u : ℝ => R (s₁ + u) * h (s₁ + u)) (𝓝[>] 0) (𝓝 0) := by
    have hsq : Tendsto (fun u : ℝ => A * Real.sqrt u) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun u : ℝ => A * Real.sqrt u) (𝓝 0) (𝓝 (A * Real.sqrt 0)) :=
        (continuous_const.mul Real.continuous_sqrt).tendsto 0
      rw [Real.sqrt_zero, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact squeeze_zero_norm' hbound hsq
  have heq := tendsto_nhds_unique hlim1 hlim0
  have hR0 : R s₁ ≠ 0 := by
    simp only [hR]
    refine mul_ne_zero ?_ (_root_.RHTower.one_sub_two_cpow_ne_zero (by rw [hs₁re]; linarith))
    rw [hs₁, show ρ - (ε : ℂ) + ε - 1 = ρ - 1 by ring]
    exact sub_ne_zero.mpr hρne
  exact mul_ne_zero hR0 hh0 heq

/-- An order bound in `ℕ∞` from its natural-number truncations. -/
theorem le_of_forall_natCast_le {a b : ℕ∞} (h : ∀ n : ℕ, (n : ℕ∞) ≤ a → (n : ℕ∞) ≤ b) :
    a ≤ b := by
  induction a using ENat.recTopCoe with
  | top =>
    induction b using ENat.recTopCoe with
    | top => exact le_rfl
    | coe m =>
      have := h (m + 1) le_top
      exact absurd (by exact_mod_cast this) (Nat.not_succ_le_self m)
  | coe m => exact h m le_rfl

/-- **Admission translates zeros with multiplicity, up to the boundary.** For an admissible damping
`ε ≤ ½` and every `ρ` with `½ + ε ≤ Re ρ < 1`, `ord_ρ ζ ≤ ord_{ρ−ε} ζ`. -/
theorem analyticOrderAt_le_analyticOrderAt_sub_of_mem_receiverDampings {ε : ℝ}
    (hε : ε ∈ receiverDampings) (hε1 : ε ≤ 1 / 2) {ρ : ℂ} (hρ : 1 / 2 + ε ≤ ρ.re)
    (hρ1 : ρ.re < 1) :
    analyticOrderAt riemannZeta ρ ≤ analyticOrderAt riemannZeta (ρ - ε) :=
  le_of_forall_natCast_le fun _ hn => natCast_le_analyticOrderAt_sub_of_memLp hε.1 hε1
    ((mem_receiverDampings_iff_memLp hε.1).mp hε) hρ hρ1 hn

/-- **On the boundary line the translate is a critical zero.** For an admissible damping `ε < ½`, a
zero with `Re ρ = ½ + ε` forces `ζ(½ + i Im ρ) = 0`. -/
theorem riemannZeta_criticalLine_eq_zero_of_mem_receiverDampings {ε : ℝ}
    (hε : ε ∈ receiverDampings) (hε1 : ε < 1 / 2) {ρ : ℂ} (hρ : ρ.re = 1 / 2 + ε)
    (hz : riemannZeta ρ = 0) : riemannZeta (1 / 2 + (ρ.im : ℂ) * I) = 0 := by
  have hρ1 : ρ.re < 1 := by linarith
  have hρne : ρ ≠ 1 := fun h => by rw [h, one_re] at hρ1; exact lt_irrefl _ hρ1
  have h1 : ((1 : ℕ) : ℕ∞) ≤ analyticOrderAt riemannZeta ρ := by
    rw [Nat.cast_one, Order.one_le_iff_ne_zero]
    exact ((analyticAt_riemannZeta_of_ne_one hρne).analyticOrderAt_ne_zero).mpr hz
  have h2 := natCast_le_analyticOrderAt_sub_of_memLp hε.1 hε1.le
    ((mem_receiverDampings_iff_memLp hε.1).mp hε) hρ.ge hρ1 h1
  rw [Nat.cast_one, Order.one_le_iff_ne_zero] at h2
  have h3 := apply_eq_zero_of_analyticOrderAt_ne_zero h2
  have hs : ρ - (ε : ℂ) = 1 / 2 + (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp [hρ]
  rwa [hs] at h3

/-- **Admission at the zero width forces critical shadows of the extremal zeros.** If `Θ > ½` is
attained at a zero `ρ₀` and the width `Θ − ½` is admissible, then `½ + i Im ρ₀` is a zero of `ζ`
of multiplicity at least that of `ρ₀`. -/
theorem analyticOrderAt_le_of_zetaZeroAbscissa_mem_receiverDampings {ρ₀ : ℂ}
    (hz : riemannZeta ρ₀ = 0) (hmax : ρ₀.re = zetaZeroAbscissa) (hgt : 1 / 2 < ρ₀.re)
    (hadm : zetaZeroAbscissa - 1 / 2 ∈ receiverDampings) :
    analyticOrderAt riemannZeta ρ₀ ≤ analyticOrderAt riemannZeta (1 / 2 + (ρ₀.im : ℂ) * I) := by
  have hρ1 : ρ₀.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  have hε1 : zetaZeroAbscissa - 1 / 2 ≤ 1 / 2 := by linarith
  have h := analyticOrderAt_le_analyticOrderAt_sub_of_mem_receiverDampings hadm hε1
    (ρ := ρ₀) (by linarith) hρ1
  have hs : ρ₀ - ((zetaZeroAbscissa - 1 / 2 : ℝ) : ℂ) = 1 / 2 + (ρ₀.im : ℂ) * I := by
    apply Complex.ext <;> simp [hmax]
  rwa [hs] at h

/-- **The threshold of admission is not attained without critical shadows.** If an extremal zero
`ρ₀` (`Re ρ₀ = Θ > ½`) has larger multiplicity than `½ + i Im ρ₀`, the admissible dampings at or above
the width are exactly `(Θ − ½, ∞)`. -/
theorem receiverDampings_inter_Ici_eq_Ioi {ρ₀ : ℂ} (hz : riemannZeta ρ₀ = 0)
    (hmax : ρ₀.re = zetaZeroAbscissa) (hgt : 1 / 2 < ρ₀.re)
    (hshadow : analyticOrderAt riemannZeta (1 / 2 + (ρ₀.im : ℂ) * I) <
      analyticOrderAt riemannZeta ρ₀) :
    receiverDampings ∩ Ici (zetaZeroAbscissa - 1 / 2) = Ioi (zetaZeroAbscissa - 1 / 2) := by
  have hwidth : SquareRootThreshold.zetaZeroWidth = zetaZeroAbscissa - 1 / 2 :=
    SquareRootThreshold.zetaZeroWidth_eq_zetaZeroAbscissa_sub_half
  ext x
  constructor
  · rintro ⟨hx, hxi⟩
    rcases (mem_Ici.mp hxi).lt_or_eq with hlt | heq
    · exact hlt
    · rw [← heq] at hx
      exact absurd (analyticOrderAt_le_of_zetaZeroAbscissa_mem_receiverDampings hz hmax hgt hx)
        (not_le.mpr hshadow)
  · intro hx
    refine ⟨SquareRootThreshold.Ioi_zetaZeroWidth_subset_receiverDampings ?_, mem_Ici.mpr hx.le⟩
    rw [hwidth]
    exact hx

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
