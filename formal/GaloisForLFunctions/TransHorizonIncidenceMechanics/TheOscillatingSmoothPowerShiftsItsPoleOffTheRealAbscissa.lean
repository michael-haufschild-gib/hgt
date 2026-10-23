import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheOscillatingSmoothPowerIsPaidExactlyAtTheZerosOfZeta
import GaloisForLFunctions.TransHorizonIncidenceMechanics.APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa
import GaloisForLFunctions.TransHorizonIncidenceMechanics.TheHalfDampedReceiverIsTheLogarithmicEnergyOfThePartialPoleSums
import GaloisForLFunctions.RHTower.Sieve.VinogradovKorobovInvZeta
import GaloisForLFunctions.RHTower.ReceiverDampingsAccumulateAboveTheZeros

/-!
# The oscillating smooth power shifts its pole off the real abscissa

For `0 < ε ≤ 1/2` and `t ∈ ℝ`, the oscillating smooth power
`c_{ε,t}(d) = d^{-ε} cos(t log d) = Re(d^{ρ−1})`, `ρ = 1 − ε + it`, lies in the damped class
`𝒞(1, ε)` (`dampedClass_one_oscillatingSmoothPower`).

* **Off-axis pole shift and real-abscissa regularity (`t ≠ 0`).** On `σ > 1 − ε` the real-axis
  Dirichlet series of `c_{ε,t}` is `Σ_d c_{ε,t}(d) d^{-σ} = Re ζ((σ + ε) − it)`
  (`tsum_oscillatingSmoothPower_mul_rpow`). When `t ≠ 0`, the point `1 − it ≠ 1` is a regular point
  of `ζ`, so as `σ ↓ 1 − ε` the real-axis Dirichlet series converges to `Re ζ(1 − it)`
  (`tendsto_dirichletSeries_oscillatingSmoothPower_nhdsGT`) and is Lipschitz at the real abscissa
  `1 − ε` (`exists_abs_dirichletSeries_oscillatingSmoothPower_sub_le_mul`) for every `t ≠ 0` and
  every `ε`, whether `c_{ε,t}` is paid or unpaid. Real-axis abscissa blowup and Lipschitz tests
  cannot detect unpaid oscillating probes because the oscillation shifts the pole from `1 − ε` to
  the conjugate complex points `1 − ε ± it`.
* **Unconditional sub-half exclusions and finiteness of paid parameters.** Combining the shifted-pole
  residue detection `zeta_eq_zero_of_receiverBounded_oscillatingSmoothPower` with the unconditional
  zero-free regions and zero isolation of `(s − 1)ζ(s)`:
  - at `t = 0`, `c_{ε,0}` is unpaid for every `0 < ε ≤ 1/2`
    (`not_receiverBounded_oscillatingSmoothPower_zero`);
  - on every bounded frequency box `|t| ≤ T`, there is `δ > 0` such that `c_{ε,t}` is unpaid for all
    `0 < ε ≤ min(δ, 1/2)` (`exists_delta_not_receiverBounded_oscillatingSmoothPower_box`);
  - on the Vinogradov–Korobov strip, `c_{ε,t}` is unpaid for `|t| ≥ T₀` and
    `0 < ε < min(1/2, vkHadamardWidth |t|)` (`exists_not_receiverBounded_oscillatingSmoothPower_vk`),
    and globally for all `t ∈ ℝ` on `0 < ε ≤ min(1/2, min(δ, vkHadamardWidth(max(K₀, |t|) + 1))/4)`
    (`exists_not_receiverBounded_oscillatingSmoothPower_vk_uniform`);
  - at every frequency `t ∈ ℝ`, the set of paid sub-half dampings `ε ∈ (0, 1/2]` is finite
    (`finite_damping_receiverBounded_oscillatingSmoothPower`), and at every damping `0 < ε ≤ 1/2`
    and height `T ≥ 0`, the set of paid frequencies `t ∈ [−T, T]` is finite
    (`finite_freq_receiverBounded_oscillatingSmoothPower`).
* **The shifted-pole hyperplane law on the critical Wiener algebra.** For any critical Wiener kernel
  `k` (`Σ_j |k(j)| j^{-1/2} < ∞`), `0 < ε < 1/2`, and `t ∈ ℝ`, the centred prefix of
  `k ⋆ c_{ε,t}` tracks `Re((K(ρ)ζ(ρ)/ρ) n^ρ)` up to a remainder of uniformly bounded pronic norm,
  where `K(ρ) = Σ_j k(j) j^{-ρ}` is the kernel's Dirichlet series at the shifted pole `ρ = 1 − ε + it`.
  Hence `k ⋆ c_{ε,t}` is paid if and only if `K(1 − ε + it) = 0` or `ζ(1 − ε + it) = 0`
  (`receiverBounded_dirichletConv_oscillatingSmoothPower_iff`).
-/

open Complex Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### §1. Off-axis pole shift and real-abscissa regularity -/

/-- The oscillating smooth power `d^{-ε} cos(t log d)` lies in the damped class `𝒞(1, ε)`. -/
theorem dampedClass_one_oscillatingSmoothPower (ε t : ℝ) :
    DampedClass 1 ε (oscillatingSmoothPower ε t) := fun d => by
  simp only [oscillatingSmoothPower, one_mul]
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  exact mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg d) _) (Real.abs_cos_le_one _)

/-- For `d ≥ 1`, `c_{ε,t}(d) d^{-σ} = Re(1 / d^{(σ + ε) − it})`. -/
theorem oscillatingSmoothPower_mul_rpow_eq_re (ε t σ : ℝ) {d : ℕ} (hd : 1 ≤ d) :
    oscillatingSmoothPower ε t d * (d : ℝ) ^ (-σ) =
      (1 / (d : ℂ) ^ (((σ + ε : ℝ) : ℂ) - (t : ℂ) * I)).re := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [oscillatingSmoothPower, mul_right_comm, ← Real.rpow_add hd0,
    show -ε + -σ = -(σ + ε) by ring, Real.rpow_def_of_pos hd0,
    show (d : ℂ) = ((d : ℝ) : ℂ) by push_cast; rfl, one_div, ← Complex.cpow_neg,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hd0.ne'), ← Complex.ofReal_log hd0.le,
    Complex.exp_re]
  congr 2 <;>
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im] <;> ring

/-- **The real-axis Dirichlet series of the oscillating smooth power.** For `σ > 1 − ε`,
`Σ_d c_{ε,t}(d) d^{-σ} = Re ζ((σ + ε) − it)`. -/
theorem hasSum_oscillatingSmoothPower_mul_rpow {ε t σ : ℝ} (hσ : 1 - ε < σ) :
    HasSum (fun d : ℕ => oscillatingSmoothPower ε t d * (d : ℝ) ^ (-σ))
      (riemannZeta (((σ + ε : ℝ) : ℂ) - (t : ℂ) * I)).re := by
  set w : ℂ := ((σ + ε : ℝ) : ℂ) - (t : ℂ) * I with hw
  have hw1 : 1 < w.re := by
    simp only [hw, sub_re, ofReal_re, mul_re, I_re, mul_zero, I_im, ofReal_im, zero_mul, sub_zero]
    linarith
  have hsum : Summable (fun d : ℕ => 1 / (d : ℂ) ^ w) :=
    Complex.summable_one_div_nat_cpow.mpr hw1
  have hz := (zeta_eq_tsum_one_div_nat_cpow hw1) ▸ hsum.hasSum
  have hw0 : w ≠ 0 := fun h => by rw [h, zero_re] at hw1; linarith
  refine (Complex.hasSum_re hz).congr_fun fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [Nat.cast_zero, Complex.zero_cpow hw0, div_zero, zero_re]
    rcases le_or_gt σ 0 with hσ0 | hσ0
    · have hε0 : 0 < ε := by linarith
      rw [oscillatingSmoothPower, Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hε0.ne'),
        zero_mul, zero_mul]
    · rw [Nat.cast_zero, Real.zero_rpow (neg_ne_zero.mpr hσ0.ne'), mul_zero]
  · exact oscillatingSmoothPower_mul_rpow_eq_re ε t σ hd

/-- On `σ > 1 − ε`, `Σ_d c_{ε,t}(d) d^{-σ} = Re ζ((σ + ε) − it)`. -/
theorem tsum_oscillatingSmoothPower_mul_rpow {ε t σ : ℝ} (hσ : 1 - ε < σ) :
    (∑' d : ℕ, oscillatingSmoothPower ε t d * (d : ℝ) ^ (-σ)) =
      (riemannZeta (((σ + ε : ℝ) : ℂ) - (t : ℂ) * I)).re :=
  (hasSum_oscillatingSmoothPower_mul_rpow hσ).tsum_eq

/-- **For `t ≠ 0`, the real-axis Dirichlet series of `c_{ε,t}` converges at the real abscissa.**
As `σ ↓ 1 − ε`, `Σ_d c_{ε,t}(d) d^{-σ} → Re ζ(1 − it)`, even when `c_{ε,t}` is unpaid. -/
theorem tendsto_dirichletSeries_oscillatingSmoothPower_nhdsGT (ε : ℝ) {t : ℝ} (ht : t ≠ 0) :
    Tendsto (fun σ : ℝ => ∑' d : ℕ, oscillatingSmoothPower ε t d * (d : ℝ) ^ (-σ))
      (𝓝[>] (1 - ε)) (𝓝 (riemannZeta (1 - (t : ℂ) * I)).re) := by
  have hne : (1 : ℂ) - (t : ℂ) * I ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp only [sub_im, one_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero, zero_sub, neg_eq_zero] at this
    exact ht this
  have hpath : Continuous (fun σ : ℝ => ((σ + ε : ℝ) : ℂ) - (t : ℂ) * I) :=
    (Complex.continuous_ofReal.comp (continuous_id.add continuous_const)).sub continuous_const
  have hpath0 : ((1 - ε + ε : ℝ) : ℂ) - (t : ℂ) * I = 1 - (t : ℂ) * I := by
    rw [sub_add_cancel, ofReal_one]
  have hζ : ContinuousAt (fun σ : ℝ => (riemannZeta (((σ + ε : ℝ) : ℂ) - (t : ℂ) * I)).re)
      (1 - ε) := by
    refine Complex.continuous_re.continuousAt.comp ?_
    exact (differentiableAt_riemannZeta (hpath0.symm ▸ hne)).continuousAt.comp hpath.continuousAt
  have htend : Tendsto (fun σ : ℝ => (riemannZeta (((σ + ε : ℝ) : ℂ) - (t : ℂ) * I)).re)
      (𝓝[>] (1 - ε)) (𝓝 (riemannZeta (1 - (t : ℂ) * I)).re) := by
    simpa [hpath0] using hζ.tendsto.mono_left nhdsWithin_le_nhds
  refine htend.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  exact (tsum_oscillatingSmoothPower_mul_rpow hσ).symm

/-- **For `t ≠ 0`, the real-axis Dirichlet series of `c_{ε,t}` is Lipschitz at the real abscissa
`1 − ε` unconditionally.** Unlike positive-drift weights, whose Dirichlet series blow up at `1 − ε`,
every nonzero-frequency oscillating smooth power satisfies the real-abscissa Lipschitz bound of
`exists_abs_dirichletSeries_sub_le_mul`, paid or unpaid. -/
theorem exists_abs_dirichletSeries_oscillatingSmoothPower_sub_le_mul (ε : ℝ) {t : ℝ}
    (ht : t ≠ 0) :
    ∃ M η : ℝ, 0 < η ∧ ∀ σ : ℝ, 1 - ε < σ → σ < 1 - ε + η →
      |(∑' d : ℕ, oscillatingSmoothPower ε t d * (d : ℝ) ^ (-σ)) -
        (riemannZeta (1 - (t : ℂ) * I)).re| ≤ M * (σ - (1 - ε)) := by
  set w₀ : ℂ := 1 - (t : ℂ) * I with hw₀
  have hne : w₀ ≠ 1 := by
    intro h
    have := congrArg Complex.im h
    simp only [hw₀, sub_im, one_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero,
      add_zero, zero_sub, neg_eq_zero] at this
    exact ht this
  set g : ℂ → ℂ := fun z => riemannZeta (z + ((ε : ℝ) : ℂ) - (t : ℂ) * I) with hg
  have hgw₀ : ((1 - ε : ℝ) : ℂ) + ((ε : ℝ) : ℂ) - (t : ℂ) * I = w₀ := by
    rw [← ofReal_add, sub_add_cancel, ofReal_one, hw₀]
  have hgdiff : DifferentiableAt ℂ g ((1 - ε : ℝ) : ℂ) := by
    have hshift : DifferentiableAt ℂ (fun z : ℂ => z + ((ε : ℝ) : ℂ) - (t : ℂ) * I)
        ((1 - ε : ℝ) : ℂ) :=
      (differentiableAt_id.add (differentiableAt_const _)).sub (differentiableAt_const _)
    exact (differentiableAt_riemannZeta (hgw₀.symm ▸ hne)).comp _ hshift
  have hderiv : HasDerivAt (fun x : ℝ => g x) (deriv g ((1 - ε : ℝ) : ℂ)) (1 - ε) :=
    hgdiff.hasDerivAt.comp_ofReal
  obtain ⟨M, hM⟩ := hderiv.isBigO_sub.bound
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.mp hM
  refine ⟨M, η, hη, fun σ haσ hσ => ?_⟩
  have hση : dist σ (1 - ε) < η := by
    rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
  have hb : ‖g (σ : ℂ) - g ((1 - ε : ℝ) : ℂ)‖ ≤ M * ‖σ - (1 - ε)‖ := hball hση
  rw [Real.norm_eq_abs, abs_of_pos (by linarith : 0 < σ - (1 - ε))] at hb
  have hre : (∑' d : ℕ, oscillatingSmoothPower ε t d * (d : ℝ) ^ (-σ)) -
      (riemannZeta (1 - (t : ℂ) * I)).re = (g (σ : ℂ) - g ((1 - ε : ℝ) : ℂ)).re := by
    rw [tsum_oscillatingSmoothPower_mul_rpow haσ, Complex.sub_re]
    simp only [hg, hgw₀, hw₀, ofReal_add]
  rw [hre]
  exact (Complex.abs_re_le_norm _).trans hb

/-! ### §2. Unconditional sub-half exclusions and finiteness of paid parameters -/

/-- **At zero frequency, every sub-half oscillating smooth power is unpaid.** -/
theorem not_receiverBounded_oscillatingSmoothPower_zero {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ¬ ReceiverBounded (oscillatingSmoothPower ε 0) := by
  intro h
  have hz := zeta_eq_zero_of_receiverBounded_oscillatingSmoothPower hε hε2 0 h
  simp only [oscillationExponent, ofReal_zero, zero_mul, add_zero] at hz
  exact riemannZeta_ne_zero_of_pos_of_lt_one (by linarith) (by linarith) hz

/-- **On every bounded frequency box, a positive sub-half collar is unconditionally unpaid.** -/
theorem exists_delta_not_receiverBounded_oscillatingSmoothPower_box (T : ℝ) :
    ∃ δ > 0, ∀ ε t : ℝ, 0 < ε → ε ≤ min δ (1 / 2) → |t| ≤ T →
      ¬ ReceiverBounded (oscillatingSmoothPower ε t) := by
  obtain ⟨δ, hδ, hbox⟩ := RHTower.Sieve.exists_zero_free_box T
  refine ⟨δ, hδ, fun ε t hε hεm ht hpaid => ?_⟩
  have hεδ : ε ≤ δ := hεm.trans (min_le_left _ _)
  have hε2 : ε ≤ 1 / 2 := hεm.trans (min_le_right _ _)
  have hz := zeta_eq_zero_of_receiverBounded_oscillatingSmoothPower hε hε2 t hpaid
  have hre : (oscillationExponent ε t).re = 1 - ε := oscillationExponent_re ε t
  have him : (oscillationExponent ε t).im = t := oscillationExponent_im ε t
  have hne1 : oscillationExponent ε t ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    rw [hre, one_re] at this
    linarith
  exact hbox (oscillationExponent ε t) (by linarith) (by linarith) (by rwa [him]) hne1 hz

/-- **Unconditional non-admission on the Vinogradov–Korobov sub-half strip.** -/
theorem exists_not_receiverBounded_oscillatingSmoothPower_vk :
    ∃ T₀ : ℝ, Real.exp (Real.exp 1) ≤ T₀ ∧ ∀ ε t : ℝ, T₀ ≤ |t| → 0 < ε →
      ε < min (1 / 2) (RHTower.vkHadamardWidth |t|) →
      ¬ ReceiverBounded (oscillatingSmoothPower ε t) := by
  obtain ⟨T₀, hT₀, hvk⟩ := RHTower.Sieve.exists_vk_zero_free_region_abs
  refine ⟨T₀, hT₀, fun ε t ht hε hεw hpaid => ?_⟩
  have hε2 : ε ≤ 1 / 2 := (hεw.trans_le (min_le_left _ _)).le
  have hεv : ε < RHTower.vkHadamardWidth |t| := hεw.trans_le (min_le_right _ _)
  have hz := zeta_eq_zero_of_receiverBounded_oscillatingSmoothPower hε hε2 t hpaid
  exact hvk (1 - ε) t ht (by linarith) (by linarith) hz

/-- **Uniform all-frequency Vinogradov–Korobov sub-half exclusion.** Combining the high-ordinate
Vinogradov–Korobov strip with the compact low-ordinate thickening gives an explicit positive width
below which `oscillatingSmoothPower ε t` is unpaid at every frequency `t ∈ ℝ`. -/
theorem exists_not_receiverBounded_oscillatingSmoothPower_vk_uniform :
    ∃ δ K₀ : ℝ, 0 < δ ∧ Real.exp (Real.exp 30) ≤ K₀ ∧
      ∀ (ε t K : ℝ), K₀ ≤ K → |t| ≤ K → 0 < ε →
        ε ≤ min (1 / 2) (min δ (RHTower.vkHadamardWidth (K + 1)) / 4) →
        ¬ ReceiverBounded (oscillatingSmoothPower ε t) := by
  obtain ⟨C, δ, K₀, -, hδ, -, hK₀, hzf, -⟩ := RHTower.Sieve.exists_bound_invZeta_vk_uniform
  refine ⟨δ, K₀, hδ, hK₀, fun ε t K hK ht hε hεw hpaid => ?_⟩
  have hε2 : ε ≤ 1 / 2 := hεw.trans (min_le_left _ _)
  have hεv : ε ≤ min δ (RHTower.vkHadamardWidth (K + 1)) / 4 := hεw.trans (min_le_right _ _)
  have hz := zeta_eq_zero_of_receiverBounded_oscillatingSmoothPower hε hε2 t hpaid
  have hre : (oscillationExponent ε t).re = 1 - ε := oscillationExponent_re ε t
  have him : (oscillationExponent ε t).im = t := oscillationExponent_im ε t
  have hne1 : oscillationExponent ε t ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    rw [hre, one_re] at this
    linarith
  exact hzf (oscillationExponent ε t) K hK (by rwa [him]) (by linarith) hne1 hz

/-- **Paid sub-half dampings are isolated at every frequency.** For any `t, ε₀ ∈ ℝ`,
`oscillatingSmoothPower ε t` is unpaid on a punctured neighbourhood of `ε₀`. -/
theorem eventually_not_receiverBounded_oscillatingSmoothPower_nhdsNE (t ε₀ : ℝ) :
    ∀ᶠ ε in 𝓝[≠] ε₀, 0 < ε → ε ≤ 1 / 2 → ¬ ReceiverBounded (oscillatingSmoothPower ε t) := by
  have htend : Tendsto (fun ε : ℝ => oscillationExponent ε t) (𝓝[≠] ε₀)
      (𝓝[≠] (oscillationExponent ε₀ t)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun ε : ℝ => oscillationExponent ε t) := by
        unfold oscillationExponent; fun_prop
      exact (hc.tendsto ε₀).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [Set.mem_compl_singleton_iff] at hε ⊢
      intro heq
      have := congrArg Complex.re heq
      rw [oscillationExponent_re, oscillationExponent_re] at this
      exact hε (by linarith)
  filter_upwards [htend.eventually (RHTower.eventually_zetaResidueUnit_ne_zero _)] with ε hne
    hε hε2 hpaid
  have hz := zeta_eq_zero_of_receiverBounded_oscillatingSmoothPower hε hε2 t hpaid
  have hne1 : oscillationExponent ε t ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    rw [oscillationExponent_re, one_re] at this
    linarith
  exact hne (by rw [RHTower.zetaResidueUnit, Function.update_of_ne hne1, hz, mul_zero])

/-- A subset of a compact set whose points are isolated in the ambient space is finite. -/
theorem finite_of_subset_isCompact_of_isolated {α : Type*} [TopologicalSpace α] {S K : Set α}
    (hK : IsCompact K) (hSK : S ⊆ K) (hiso : ∀ x ∈ K, ∀ᶠ y in 𝓝[≠] x, y ∉ S) : S.Finite := by
  classical
  have hopen : ∀ x : K, ∃ U : Set α, (∀ y ∈ U, y ≠ (x : α) → y ∉ S) ∧ IsOpen U ∧ (x : α) ∈ U :=
    fun x => mem_nhds_iff.mp (eventually_nhdsWithin_iff.mp (hiso x.1 x.2))
  choose U hUdisj hUopen hxU using hopen
  obtain ⟨t, hcov⟩ := hK.elim_finite_subcover U hUopen fun x hx =>
    Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxU ⟨x, hx⟩⟩
  refine (t.finite_toSet.image Subtype.val).subset fun y hyS => ?_
  obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (hcov (hSK hyS))
  by_cases heq : y = x.1
  · exact ⟨x, hxt, heq.symm⟩
  · exact False.elim (hUdisj x y hyx heq hyS)

/-- **At every frequency `t ∈ ℝ`, the set of paid sub-half dampings `ε ∈ (0, 1/2]` is finite.** -/
theorem finite_damping_receiverBounded_oscillatingSmoothPower (t : ℝ) :
    {ε : ℝ | 0 < ε ∧ ε ≤ 1 / 2 ∧ ReceiverBounded (oscillatingSmoothPower ε t)}.Finite := by
  obtain ⟨δ, hδ, hbox⟩ := exists_delta_not_receiverBounded_oscillatingSmoothPower_box |t|
  set d := min δ (1 / 2)
  refine finite_of_subset_isCompact_of_isolated (K := Set.Icc d (1 / 2)) isCompact_Icc
    (fun ε hε => ?_) (fun ε₀ _ => ?_)
  · refine ⟨?_, hε.2.1⟩
    by_contra hlt
    exact hbox ε t hε.1 (not_le.mp hlt).le le_rfl hε.2.2
  · filter_upwards [eventually_not_receiverBounded_oscillatingSmoothPower_nhdsNE t ε₀] with ε hε
    rintro ⟨h1, h2, h3⟩
    exact hε h1 h2 h3

/-- **At every frequency `t ∈ ℝ`, the set of paid sub-half dampings has empty derived set.** -/
theorem derivedSet_damping_receiverBounded_oscillatingSmoothPower_eq_empty (t : ℝ) :
    derivedSet {ε : ℝ | 0 < ε ∧ ε ≤ 1 / 2 ∧ ReceiverBounded (oscillatingSmoothPower ε t)} = ∅ := by
  ext ε₀
  simp only [mem_derivedSet, Set.mem_empty_iff_false, iff_false]
  intro hacc
  have hev : ∀ᶠ ε in 𝓝[≠] ε₀,
      ε ∉ {ε : ℝ | 0 < ε ∧ ε ≤ 1 / 2 ∧ ReceiverBounded (oscillatingSmoothPower ε t)} := by
    filter_upwards [eventually_not_receiverBounded_oscillatingSmoothPower_nhdsNE t ε₀] with ε hε h
    exact hε h.1 h.2.1 h.2.2
  rw [accPt_iff_frequently_nhdsNE] at hacc
  exact hacc hev

/-- **At every sub-half damping `0 < ε ≤ 1/2` and height `T`, the set of paid frequencies in
`[−T, T]` is finite.** -/
theorem finite_freq_receiverBounded_oscillatingSmoothPower {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (T : ℝ) :
    {t : ℝ | |t| ≤ T ∧ ReceiverBounded (oscillatingSmoothPower ε t)}.Finite := by
  refine finite_of_subset_isCompact_of_isolated (K := Set.Icc (-T) T) isCompact_Icc
    (fun t ht => abs_le.mp ht.1) (fun t₀ _ => ?_)
  have htend : Tendsto (fun t : ℝ => oscillationExponent ε t) (𝓝[≠] t₀)
      (𝓝[≠] (oscillationExponent ε t₀)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun t : ℝ => oscillationExponent ε t) := by
        unfold oscillationExponent; fun_prop
      exact (hc.tendsto t₀).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      rw [Set.mem_compl_singleton_iff] at ht ⊢
      intro heq
      have := congrArg Complex.im heq
      rw [oscillationExponent_im, oscillationExponent_im] at this
      exact ht this
  filter_upwards [htend.eventually (RHTower.eventually_zetaResidueUnit_ne_zero _)] with t hne h
  have hz := zeta_eq_zero_of_receiverBounded_oscillatingSmoothPower hε hε2 t h.2
  have hne1 : oscillationExponent ε t ≠ 1 := by
    intro h1
    have := congrArg Complex.re h1
    rw [oscillationExponent_re, one_re] at this
    linarith
  exact hne (by rw [RHTower.zetaResidueUnit, Function.update_of_ne hne1, hz, mul_zero])

/-! ### §3. The shifted-pole hyperplane law on the critical Wiener algebra -/

/-- The complex pole value `K(ρ) = Σ_j k(j) j^{-ρ}` of a real kernel `k` at `ρ ∈ ℂ`. -/
def complexPoleValue (k : ℕ → ℝ) (ρ : ℂ) : ℂ :=
  ∑' j : ℕ, (k j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ)

/-- The partial complex pole sum `S_{k,ρ}(n) = Σ_{1 ≤ j ≤ n} k(j) j^{-ρ}`. -/
def partialComplexPoleSum (k : ℕ → ℝ) (ρ : ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ Icc 1 n, (k j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ)

/-- For `k` in the critical Wiener algebra and `Re ρ ≥ 1/2`, the complex pole series converges
absolutely. -/
theorem summable_norm_complexPoleValue {k : ℕ → ℝ} (hk : CriticalWiener k) {ρ : ℂ}
    (hρ : 1 / 2 ≤ ρ.re) :
    Summable (fun j : ℕ => ‖(k j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ)‖) := by
  refine hk.of_nonneg_of_le (fun _ => norm_nonneg _) fun j => ?_
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [Complex.zero_cpow (show -ρ ≠ 0 by
      intro h; have := congrArg Complex.re h; simp at this; linarith)]
  · have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_cpow_eq_rpow_re_of_pos hj0, neg_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) (by linarith)) (abs_nonneg _)

/-- For `ε < 1`, `oscillationExponent ε t ≠ 0`. -/
theorem oscillationExponent_ne_zero {ε : ℝ} (hε1 : ε < 1) (t : ℝ) :
    oscillationExponent ε t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [oscillationExponent_re, zero_re] at this
  linarith

/-- For `0 < Re ρ < 1`, `0 ≤ floorSumRate ρ`. -/
theorem floorSumRate_nonneg {ρ : ℂ} (hρ0 : 0 < ρ.re) (hρ1 : ρ.re < 1) :
    0 ≤ floorSumRate ρ := by
  unfold floorSumRate
  have h1 : 0 ≤ partialSumRate (2 - ρ) :=
    partialSumRate_nonneg (by simp only [sub_re]; norm_num; linarith)
  have h2 : 0 ≤ partialSumRate ρ := partialSumRate_nonneg hρ0
  have h3 : 0 ≤ partialSumRate (1 - ρ) :=
    partialSumRate_nonneg (by simp only [sub_re, one_re]; linarith)
  have h4 : 0 ≤ 1 + 1 / ρ.re := by positivity
  positivity

/-- On `[a, b]` with `0 < a` and `Re ρ ≤ 1`,
`‖b^ρ − a^ρ‖ ≤ ‖ρ‖ a^{Re ρ − 1} (b − a)`. -/
theorem norm_cpow_sub_cpow_le {ρ : ℂ} (hρ1 : ρ.re ≤ 1) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖((b : ℝ) : ℂ) ^ ρ - ((a : ℝ) : ℂ) ^ ρ‖ ≤ ‖ρ‖ * a ^ (ρ.re - 1) * (b - a) := by
  exact norm_image_sub_le_of_norm_deriv_le_segment'
    (f := fun y : ℝ => ((y : ℝ) : ℂ) ^ ρ) (f' := fun y => ρ * ((y : ℝ) : ℂ) ^ (ρ - 1))
    (a := a) (b := b) (C := ‖ρ‖ * a ^ (ρ.re - 1))
    (fun y hy => by
      have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
      have hd := hasDerivAt_ofReal_cpow_one_sub (w := 1 - ρ) hy0
      rw [sub_sub_cancel, neg_sub] at hd
      exact hd.hasDerivWithinAt)
    (fun y hy => by
      have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, sub_re, one_re]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos ha hy.1 (by linarith)) (norm_nonneg _))
    b ⟨hab, le_rfl⟩

/-- The dilated remainder of the oscillating smooth power at scale `j`:
`A_{ε,t}(⌊n/j⌋) − Re((ζ(ρ)/ρ) n^ρ j^{-ρ})`. -/
def oscillatingDilationRemainder (ε t : ℝ) (n j : ℕ) : ℝ :=
  weightCenteredPrefix (oscillatingSmoothPower ε t)
    (riemannZeta (2 - oscillationExponent ε t)).re (n / j) -
    (riemannZeta (oscillationExponent ε t) / oscillationExponent ε t *
      ((n : ℝ) : ℂ) ^ oscillationExponent ε t *
      ((j : ℝ) : ℂ) ^ (-oscillationExponent ε t)).re

/-- **The prefix of `k ⋆ c_{ε,t}`.** At every `n`,
`A_{k ⋆ c_{ε,t}}(n) = Re((ζ(ρ)/ρ) n^ρ S_{k,ρ}(n)) + Σ_{1 ≤ j ≤ n} k(j) R_{ε,t}(n, j) + m A_k(n)`. -/
theorem weightCenteredPrefix_dirichletConv_oscillatingSmoothPower (k : ℕ → ℝ) (mk ε t : ℝ)
    (n : ℕ) :
    weightCenteredPrefix (RHTower.dirichletConv k (oscillatingSmoothPower ε t))
      (mk * (riemannZeta (2 - oscillationExponent ε t)).re) n =
      (riemannZeta (oscillationExponent ε t) / oscillationExponent ε t *
        ((n : ℝ) : ℂ) ^ oscillationExponent ε t *
        partialComplexPoleSum k (oscillationExponent ε t) n).re +
      ∑ j ∈ Icc 1 n, k j * oscillatingDilationRemainder ε t n j +
      (riemannZeta (2 - oscillationExponent ε t)).re * weightCenteredPrefix k mk n := by
  rw [weightCenteredPrefix_dirichletConv, partialComplexPoleSum, mul_sum, Complex.re_sum,
    ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  simp only [oscillatingDilationRemainder]
  have hmul : (riemannZeta (oscillationExponent ε t) / oscillationExponent ε t *
      ((n : ℝ) : ℂ) ^ oscillationExponent ε t *
      ((k j : ℂ) * ((j : ℝ) : ℂ) ^ (-oscillationExponent ε t))).re =
      k j * (riemannZeta (oscillationExponent ε t) / oscillationExponent ε t *
        ((n : ℝ) : ℂ) ^ oscillationExponent ε t *
        ((j : ℝ) : ℂ) ^ (-oscillationExponent ε t)).re := by
    rw [show riemannZeta (oscillationExponent ε t) / oscillationExponent ε t *
        ((n : ℝ) : ℂ) ^ oscillationExponent ε t *
        ((k j : ℂ) * ((j : ℝ) : ℂ) ^ (-oscillationExponent ε t)) =
      (k j : ℂ) * (riemannZeta (oscillationExponent ε t) / oscillationExponent ε t *
        ((n : ℝ) : ℂ) ^ oscillationExponent ε t *
        ((j : ℝ) : ℂ) ^ (-oscillationExponent ε t)) by ring, Complex.re_ofReal_mul]
  rw [hmul]
  ring

/-- **Each dilated oscillating remainder has pronic norm `O(j^{-1/2})`.** -/
theorem pronicNorm_oscillatingDilationRemainder_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (t : ℝ)
    {j : ℕ} (hj : 1 ≤ j) (T : ℕ) :
    pronicNorm (fun n => if j ≤ n then oscillatingDilationRemainder ε t n j else 0) T ≤
      (floorSumRate (oscillationExponent ε t) + ‖riemannZeta (oscillationExponent ε t)‖) *
        Real.sqrt (1 + 1 / ε) * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
  set ρ := oscillationExponent ε t with hρ
  set C := floorSumRate ρ + ‖riemannZeta ρ‖ with hC
  have h1ε : 0 < 1 - ε := by linarith
  have hρre : ρ.re = 1 - ε := oscillationExponent_re ε t
  have hρ0 : ρ ≠ 0 := oscillationExponent_ne_zero hε1 t
  have hC0 : 0 ≤ C :=
    add_nonneg (floorSumRate_nonneg (by rw [hρre]; exact h1ε) (by rw [hρre]; linarith))
      (norm_nonneg _)
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  -- pointwise bound on `j ≤ n`
  have hpt : ∀ n : ℕ, j ≤ n →
      |oscillatingDilationRemainder ε t n j| ≤ C * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := by
    intro n hjn
    have hN1 : 1 ≤ n / j := (Nat.le_div_iff_mul_le hj).mpr (by omega)
    have hNR0 : (0 : ℝ) < ((n / j : ℕ) : ℝ) := by exact_mod_cast hN1
    have hNR1 : (1 : ℝ) ≤ ((n / j : ℕ) : ℝ) := by exact_mod_cast hN1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (hj.trans hjn)
    have hle : ((n / j : ℕ) : ℝ) ≤ (n : ℝ) / j := Nat.cast_div_le
    have hdiff : (n : ℝ) / j - ((n / j : ℕ) : ℝ) ≤ 1 := by
      have := (abs_le.mp (abs_natDiv_sub_div_le n j hj)).1
      linarith
    have hpre := abs_weightCenteredPrefix_oscillatingSmoothPower_sub_le hε hε1 t hN1
    rw [(hasSum_oscillatingSmoothPower_div hε t).tsum_eq, ← hρ] at hpre
    have hsqmono : Real.sqrt ((n / j : ℕ) : ℝ) ^ (1 - ε) ≤
        Real.sqrt ((n : ℝ) / j) ^ (1 - ε) :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hle) h1ε.le
    have hsq1 : (1 : ℝ) ≤ Real.sqrt ((n : ℝ) / j) ^ (1 - ε) :=
      Real.one_le_rpow (Real.one_le_sqrt.mpr (hNR1.trans hle)) h1ε.le
    have hdiv_cpow : (((n : ℝ) / j : ℝ) : ℂ) ^ ρ =
        ((n : ℝ) : ℂ) ^ ρ * ((j : ℝ) : ℂ) ^ (-ρ) := ofReal_div_cpow hn0 hj0 ρ
    have hstep := norm_cpow_sub_cpow_le (ρ := ρ) (by rw [hρre]; linarith) hNR0 hle
    rw [hρre, show 1 - ε - 1 = -ε by ring, hdiv_cpow] at hstep
    have hrpow1 : (((n / j : ℕ) : ℝ) ^ (-ε)) * ((n : ℝ) / j - ((n / j : ℕ) : ℝ)) ≤ 1 := by
      have h1 : ((n / j : ℕ) : ℝ) ^ (-ε) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hNR1 (by linarith)
      exact (mul_le_mul h1 hdiff (sub_nonneg.mpr hle) zero_le_one).trans (by norm_num)
    have hstep' : ‖((n : ℝ) : ℂ) ^ ρ * ((j : ℝ) : ℂ) ^ (-ρ) - (((n / j : ℕ) : ℝ) : ℂ) ^ ρ‖ ≤
        ‖ρ‖ := hstep.trans (by
      calc ‖ρ‖ * ((n / j : ℕ) : ℝ) ^ (-ε) * ((n : ℝ) / j - ((n / j : ℕ) : ℝ))
          = ‖ρ‖ * (((n / j : ℕ) : ℝ) ^ (-ε) * ((n : ℝ) / j - ((n / j : ℕ) : ℝ))) := by ring
        _ ≤ ‖ρ‖ * 1 := mul_le_mul_of_nonneg_left hrpow1 (norm_nonneg ρ)
        _ = ‖ρ‖ := mul_one _)
    have hre_diff : |(riemannZeta ρ / ρ * ((n : ℝ) : ℂ) ^ ρ * ((j : ℝ) : ℂ) ^ (-ρ)).re -
        (riemannZeta ρ * (((n / j : ℕ) : ℝ) : ℂ) ^ ρ / ρ).re| ≤
        ‖riemannZeta ρ‖ * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := by
      rw [← Complex.sub_re]
      refine (Complex.abs_re_le_norm _).trans ?_
      have hfac : riemannZeta ρ / ρ * ((n : ℝ) : ℂ) ^ ρ * ((j : ℝ) : ℂ) ^ (-ρ) -
          riemannZeta ρ * (((n / j : ℕ) : ℝ) : ℂ) ^ ρ / ρ =
          (riemannZeta ρ / ρ) *
            (((n : ℝ) : ℂ) ^ ρ * ((j : ℝ) : ℂ) ^ (-ρ) - (((n / j : ℕ) : ℝ) : ℂ) ^ ρ) := by
        ring
      rw [hfac, norm_mul, norm_div]
      calc ‖riemannZeta ρ‖ / ‖ρ‖ *
            ‖((n : ℝ) : ℂ) ^ ρ * ((j : ℝ) : ℂ) ^ (-ρ) - (((n / j : ℕ) : ℝ) : ℂ) ^ ρ‖
          ≤ ‖riemannZeta ρ‖ / ‖ρ‖ * ‖ρ‖ :=
            mul_le_mul_of_nonneg_left hstep' (by positivity)
        _ = ‖riemannZeta ρ‖ * 1 := by rw [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hρ0), mul_one]
        _ ≤ ‖riemannZeta ρ‖ * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) :=
            mul_le_mul_of_nonneg_left hsq1 (norm_nonneg _)
    have hsplit : oscillatingDilationRemainder ε t n j =
        (weightCenteredPrefix (oscillatingSmoothPower ε t) (riemannZeta (2 - ρ)).re (n / j) -
          (riemannZeta ρ * (((n / j : ℕ) : ℝ) : ℂ) ^ ρ / ρ).re) -
        ((riemannZeta ρ / ρ * ((n : ℝ) : ℂ) ^ ρ * ((j : ℝ) : ℂ) ^ (-ρ)).re -
          (riemannZeta ρ * (((n / j : ℕ) : ℝ) : ℂ) ^ ρ / ρ).re) := by
      simp only [oscillatingDilationRemainder, hρ]; ring
    rw [hsplit]
    calc _ ≤ |weightCenteredPrefix (oscillatingSmoothPower ε t) (riemannZeta (2 - ρ)).re (n / j) -
          (riemannZeta ρ * (((n / j : ℕ) : ℝ) : ℂ) ^ ρ / ρ).re| +
          |(riemannZeta ρ / ρ * ((n : ℝ) : ℂ) ^ ρ * ((j : ℝ) : ℂ) ^ (-ρ)).re -
            (riemannZeta ρ * (((n / j : ℕ) : ℝ) : ℂ) ^ ρ / ρ).re| := abs_sub _ _
      _ ≤ floorSumRate ρ * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) +
          ‖riemannZeta ρ‖ * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) :=
        add_le_add (hpre.trans (mul_le_mul_of_nonneg_left hsqmono
          (floorSumRate_nonneg (by rw [hρre]; exact h1ε) (by rw [hρre]; linarith)))) hre_diff
      _ = C * Real.sqrt ((n : ℝ) / j) ^ (1 - ε) := by rw [hC]; ring
  -- sum the energy over `j ≤ n ≤ T`
  have hsum : ∑ n ∈ Icc 1 T, (if j ≤ n then oscillatingDilationRemainder ε t n j else 0) ^ 2 /
      ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (C * Real.sqrt (1 + 1 / ε) * (j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
    have hfil : ∑ n ∈ Icc 1 T, (if j ≤ n then oscillatingDilationRemainder ε t n j else 0) ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) =
        ∑ n ∈ Icc j T, oscillatingDilationRemainder ε t n j ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1)) := by
      rw [← sum_filter_add_sum_filter_not (Icc 1 T) (fun n => j ≤ n)]
      have h1 : ∑ n ∈ (Icc 1 T).filter (fun n => ¬ j ≤ n),
          (if j ≤ n then oscillatingDilationRemainder ε t n j else 0) ^ 2 /
            ((n : ℝ) * ((n : ℝ) + 1)) = 0 :=
        sum_eq_zero fun n hn => by rw [if_neg (mem_filter.mp hn).2]; simp
      have h2 : (Icc 1 T).filter (fun n => j ≤ n) = Icc j T := by
        ext n; simp only [mem_filter, mem_Icc]; omega
      rw [h1, add_zero, h2]
      exact sum_congr rfl fun n hn => by rw [if_pos (mem_Icc.mp hn).1]
    rw [hfil]
    have hterm : ∀ n ∈ Icc j T, oscillatingDilationRemainder ε t n j ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) ≤
        C ^ 2 * (j : ℝ) ^ (-(1 - ε)) * (n : ℝ) ^ (-(1 + ε)) := by
      intro n hn
      have hjn := (mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (hj.trans hjn)
      have hpr : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
      have hr0 : 0 ≤ Real.sqrt ((n : ℝ) / j) := Real.sqrt_nonneg _
      have hr2 : (Real.sqrt ((n : ℝ) / j) ^ (1 - ε)) ^ 2 =
          (j : ℝ) ^ (-(1 - ε)) * (n : ℝ) ^ (1 - ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hr0, Real.sqrt_eq_rpow, ← Real.rpow_mul
          (div_nonneg hn0.le hj0.le), Real.div_rpow hn0.le hj0.le, Real.rpow_neg hj0.le]
        push_cast
        rw [show 1 / 2 * ((1 - ε) * 2) = 1 - ε by ring]
        ring
      have hsq : oscillatingDilationRemainder ε t n j ^ 2 ≤
          C ^ 2 * ((j : ℝ) ^ (-(1 - ε)) * (n : ℝ) ^ (1 - ε)) := by
        rw [← hr2, ← mul_pow, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hpt n hjn) 2
      have hpow : (n : ℝ) ^ (1 - ε) = (n : ℝ) ^ (-(1 + ε)) * ((n : ℝ) * n) := by
        rw [show 1 - ε = -(1 + ε) + 1 + 1 by ring, Real.rpow_add_one hn0.ne',
          Real.rpow_add_one hn0.ne']
        ring
      rw [div_le_iff₀ hpr]
      calc oscillatingDilationRemainder ε t n j ^ 2
          ≤ C ^ 2 * ((j : ℝ) ^ (-(1 - ε)) * (n : ℝ) ^ (1 - ε)) := hsq
        _ = C ^ 2 * (j : ℝ) ^ (-(1 - ε)) * (n : ℝ) ^ (-(1 + ε)) * ((n : ℝ) * n) := by
            rw [hpow]; ring
        _ ≤ C ^ 2 * (j : ℝ) ^ (-(1 - ε)) * (n : ℝ) ^ (-(1 + ε)) * ((n : ℝ) * ((n : ℝ) + 1)) := by
            gcongr; linarith
    have hrp := sum_Icc_rpow_neg_one_sub_le hε hj T
    have haj : (j : ℝ) ^ (-(1 - ε)) * (j : ℝ) ^ (-ε) = ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
      rw [← Real.rpow_add hj0, ← Real.rpow_natCast, ← Real.rpow_mul hj0.le]
      congr 1; push_cast; ring
    calc ∑ n ∈ Icc j T, oscillatingDilationRemainder ε t n j ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ ∑ n ∈ Icc j T, C ^ 2 * (j : ℝ) ^ (-(1 - ε)) * (n : ℝ) ^ (-(1 + ε)) := sum_le_sum hterm
      _ = C ^ 2 * (j : ℝ) ^ (-(1 - ε)) * ∑ n ∈ Icc j T, (n : ℝ) ^ (-(1 + ε)) := by rw [mul_sum]
      _ ≤ C ^ 2 * (j : ℝ) ^ (-(1 - ε)) * ((1 + 1 / ε) * (j : ℝ) ^ (-ε)) :=
          mul_le_mul_of_nonneg_left hrp (mul_nonneg (sq_nonneg C) (Real.rpow_nonneg hj0.le _))
      _ = C ^ 2 * (1 + 1 / ε) * ((j : ℝ) ^ (-(1 - ε)) * (j : ℝ) ^ (-ε)) := by ring
      _ = (C * Real.sqrt (1 + 1 / ε) * (j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
          rw [haj, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  rw [pronicNorm]
  exact (Real.sqrt_le_sqrt hsum).trans (Real.sqrt_sq (by positivity)).le

/-- Below scale `j`, the pole-deficit term `1_{n < j} n^{1−ε} j^{-(1−ε)}` has pronic norm
at most `√(1 + 1/(1 − 2ε)) j^{-1/2}` for `0 < ε < 1/2`. -/
theorem pronicNorm_poleDeficit_below_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) {j : ℕ}
    (hj : 1 ≤ j) (T : ℕ) :
    pronicNorm (fun n => if n < j then (n : ℝ) ^ (1 - ε) * (j : ℝ) ^ (-(1 - ε)) else 0) T ≤
      Real.sqrt (1 + 1 / (1 - 2 * ε)) * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have h12ε : 0 < 1 - 2 * ε := by linarith
  set a := (j : ℝ) ^ (-(1 - ε)) with ha
  have hsum : ∑ n ∈ Icc 1 T,
      (if n < j then (n : ℝ) ^ (1 - ε) * a else 0) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
      (Real.sqrt (1 + 1 / (1 - 2 * ε)) * (j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
    have hterm : ∀ n ∈ Icc 1 T,
        (if n < j then (n : ℝ) ^ (1 - ε) * a else 0) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤
        if n < j then a ^ 2 * (n : ℝ) ^ (-(2 * ε)) else 0 := by
      intro n hn
      split_ifs with hlt
      · have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hpr : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
        have hpow : ((n : ℝ) ^ (1 - ε)) ^ 2 = (n : ℝ) ^ (-(2 * ε)) * ((n : ℝ) * n) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le,
            show (1 - ε) * ((2 : ℕ) : ℝ) = -(2 * ε) + 1 + 1 by push_cast; ring,
            Real.rpow_add_one hn0.ne', Real.rpow_add_one hn0.ne']
          ring
        rw [div_le_iff₀ hpr, mul_pow, hpow]
        calc (n : ℝ) ^ (-(2 * ε)) * ((n : ℝ) * n) * a ^ 2
            = a ^ 2 * (n : ℝ) ^ (-(2 * ε)) * ((n : ℝ) * n) := by ring
          _ ≤ a ^ 2 * (n : ℝ) ^ (-(2 * ε)) * ((n : ℝ) * ((n : ℝ) + 1)) := by
              gcongr; linarith
      · simp
    have hsub : (Icc 1 T).filter (· < j) ⊆ Icc 1 (j - 1) := fun n hn => by
      simp only [mem_filter, mem_Icc] at hn ⊢; omega
    have hhead : ∑ n ∈ (Icc 1 T).filter (· < j), (n : ℝ) ^ (-(2 * ε)) ≤
        1 + (j : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) := by
      calc ∑ n ∈ (Icc 1 T).filter (· < j), (n : ℝ) ^ (-(2 * ε))
          ≤ ∑ n ∈ Icc 1 (j - 1), (n : ℝ) ^ (-(2 * ε)) :=
            sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _
        _ ≤ 1 + ((j - 1 : ℕ) : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) :=
            RHTower.sum_rpow_neg_head_le (by linarith) (by linarith) _
        _ ≤ 1 + (j : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) := by
            gcongr; exact_mod_cast Nat.sub_le j 1
    have ha2 : a ^ 2 = (j : ℝ) ^ (-(2 - 2 * ε)) := by
      rw [ha, ← Real.rpow_natCast, ← Real.rpow_mul hj0.le]; congr 1; push_cast; ring
    have hjhalf : ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = (j : ℝ) ^ (-1 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hj0.le]; congr 1; push_cast; ring
    have ha2j : a ^ 2 * (j : ℝ) ^ (1 - 2 * ε) = ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
      rw [ha2, hjhalf, ← Real.rpow_add hj0]; congr 1; ring
    have ha2le : a ^ 2 ≤ ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
      rw [ha2, hjhalf]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hj) (by linarith)
    calc ∑ n ∈ Icc 1 T,
          (if n < j then (n : ℝ) ^ (1 - ε) * a else 0) ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        ≤ ∑ n ∈ Icc 1 T, (if n < j then a ^ 2 * (n : ℝ) ^ (-(2 * ε)) else 0) := sum_le_sum hterm
      _ = a ^ 2 * ∑ n ∈ (Icc 1 T).filter (· < j), (n : ℝ) ^ (-(2 * ε)) := by
          rw [← sum_filter, mul_sum]
      _ ≤ a ^ 2 * (1 + (j : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) :=
          mul_le_mul_of_nonneg_left hhead (sq_nonneg a)
      _ = a ^ 2 + a ^ 2 * (j : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε) := by ring
      _ ≤ ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 +
          ((j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 / (1 - 2 * ε) := by rw [ha2j]; gcongr
      _ = (Real.sqrt (1 + 1 / (1 - 2 * ε)) * (j : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  rw [pronicNorm]
  exact (Real.sqrt_le_sqrt hsum).trans (Real.sqrt_sq (by positivity)).le

/-- On `[1, T]`, `pronicNorm (n^{1−ε}) T ≤ √(1 + 1/(1 − 2ε)) (T + 1)^{1/2 − ε}` for `0 < ε < 1/2`. -/
theorem pronicNorm_rpow_one_sub_le {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (T : ℕ) :
    pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 - ε)) T ≤
      Real.sqrt (1 + 1 / (1 - 2 * ε)) * ((T : ℝ) + 1) ^ (1 / 2 - ε) := by
  have h := pronicNorm_poleDeficit_below_le hε hε2 (j := T + 1) (by omega) T
  have h1 : pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 - ε)) T *
      (((T + 1 : ℕ) : ℝ) ^ (-(1 - ε))) =
      pronicNorm (fun n => if n < T + 1 then (n : ℝ) ^ (1 - ε) *
        ((T + 1 : ℕ) : ℝ) ^ (-(1 - ε)) else 0) T := by
    have hpos : 0 ≤ ((T + 1 : ℕ) : ℝ) ^ (-(1 - ε)) := Real.rpow_nonneg (by positivity) _
    rw [mul_comm, ← abs_of_nonneg hpos, ← pronicNorm_smul]
    refine pronicNorm_congr fun n hn => ?_
    have hnT : n < T + 1 := by have := (mem_Icc.mp hn).2; omega
    rw [if_pos hnT, abs_of_nonneg hpos, mul_comm]
  have hT1 : (0 : ℝ) < ((T + 1 : ℕ) : ℝ) := by positivity
  have hexp : ((T + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
      ((T + 1 : ℕ) : ℝ) ^ (1 / 2 - ε) * ((T + 1 : ℕ) : ℝ) ^ (-(1 - ε)) := by
    rw [← Real.rpow_add hT1]; congr 1; ring
  rw [← h1, hexp, ← mul_assoc] at h
  have h2 := le_of_mul_le_mul_right h (Real.rpow_pos_of_pos hT1 (-(1 - ε)))
  simpa [Nat.cast_succ] using h2

/-- **The prefix of `k ⋆ c_{ε,t}` tracks `Re((K(ρ)ζ(ρ)/ρ) n^ρ)` in pronic norm.** For `0 < ε < 1/2`,
`t ∈ ℝ`, and `k` in the critical Wiener algebra, there is `B` such that at every cutoff `T`,
`|pronicNorm (A_{k ⋆ c_{ε,t}}) T − pronicNorm (fun n => Re((K(ρ)ζ(ρ)/ρ) n^ρ)) T| ≤ B`. -/
theorem exists_abs_pronicNorm_dirichletConv_oscillatingSmoothPower_sub_le {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) (t : ℝ) {k : ℕ → ℝ} (hk : CriticalWiener k) :
    ∃ B : ℝ, ∀ T : ℕ,
      |pronicNorm (weightCenteredPrefix (RHTower.dirichletConv k (oscillatingSmoothPower ε t))
          (∑' d : ℕ, RHTower.dirichletConv k (oscillatingSmoothPower ε t) d / d)) T -
        pronicNorm (fun n : ℕ =>
          (complexPoleValue k (oscillationExponent ε t) *
            riemannZeta (oscillationExponent ε t) / oscillationExponent ε t *
            ((n : ℝ) : ℂ) ^ oscillationExponent ε t).re) T| ≤ B := by
  have hε1 : ε < 1 := by linarith
  have h12ε : 0 < 1 - 2 * ε := by linarith
  set ρ := oscillationExponent ε t with hρ
  have hρre : ρ.re = 1 - ε := oscillationExponent_re ε t
  have hρhalf : 1 / 2 ≤ ρ.re := by rw [hρre]; linarith
  set a₀ := riemannZeta ρ / ρ with ha₀
  set K := complexPoleValue k ρ with hK
  set mc := (riemannZeta (2 - ρ)).re with hmc
  set mk := ∑' j : ℕ, k j / j with hmk
  have hW : Summable (fun j : ℕ => |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ))) := hk
  set G := ∑' j : ℕ, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) with hG
  set C₁ := (floorSumRate ρ + ‖riemannZeta ρ‖) * Real.sqrt (1 + 1 / ε) with hC₁
  set C₂ := ‖a₀‖ * Real.sqrt (1 + 1 / (1 - 2 * ε)) with hC₂
  refine ⟨(C₁ + C₂ + |mc| * (Real.sqrt 2 + 1) + C₂) * G, fun T => ?_⟩
  have hcsum : Summable (fun d : ℕ => |oscillatingSmoothPower ε t d / d|) :=
    (summable_div_of_dampedClass hε (dampedClass_one_oscillatingSmoothPower ε t)).abs
  have hmean : (∑' d : ℕ, RHTower.dirichletConv k (oscillatingSmoothPower ε t) d / d) = mk * mc :=
    (hasSum_dirichletConv_div hk.summable_abs_div.of_abs.hasSum
      (hasSum_oscillatingSmoothPower_div hε t) hk.summable_abs_div hcsum).tsum_eq
  rw [hmean]
  -- split `K` at `T`
  have hKsum : Summable (fun j : ℕ => (k j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ)) :=
    (summable_norm_complexPoleValue hk hρhalf).of_norm
  set τ : ℂ := ∑' m : ℕ,
    (k (m + (T + 1)) : ℂ) * (((m + (T + 1) : ℕ) : ℝ) : ℂ) ^ (-ρ) with hτ
  have hKsplit : K = ∑ j ∈ Icc 1 T, (k j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ) + τ := by
    have h := hKsum.sum_add_tsum_nat_add (T + 1)
    have h0 : (k 0 : ℂ) * (((0 : ℕ) : ℝ) : ℂ) ^ (-ρ) = 0 := by
      rw [Nat.cast_zero, Complex.ofReal_zero, Complex.zero_cpow (show -ρ ≠ 0 by
        intro h0; have := congrArg Complex.re h0; simp [hρre] at this; linarith), mul_zero]
    have hrange : ∑ j ∈ range (T + 1), (k j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ) =
        ∑ j ∈ Icc 1 T, (k j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ) := by
      symm
      refine sum_subset (fun d hd => by simp only [mem_Icc, mem_range] at hd ⊢; omega)
        fun d hd hd' => ?_
      simp only [mem_Icc, mem_range, not_and, not_le] at hd hd'
      obtain rfl : d = 0 := by omega
      exact h0
    rw [hrange] at h
    exact h.symm
  -- on `n ∈ Icc 1 T`, decompose `A_{k⋆c}(n) − Re(K a₀ n^ρ)` into four pieces
  set D₁ : ℕ → ℝ := fun n =>
    ∑ j ∈ Icc 1 T, k j * (if j ≤ n then oscillatingDilationRemainder ε t n j else 0)
  set D₂ : ℕ → ℝ := fun n =>
    ∑ j ∈ Icc 1 T, k j * (if n < j then
      -(a₀ * ((n : ℝ) : ℂ) ^ ρ * ((j : ℝ) : ℂ) ^ (-ρ)).re else 0)
  set D₃ : ℕ → ℝ := fun n => mc * weightCenteredPrefix k mk n
  set D₄ : ℕ → ℝ := fun n => -(τ * a₀ * ((n : ℝ) : ℂ) ^ ρ).re
  have hrep : ∀ n ∈ Icc 1 T,
      weightCenteredPrefix (RHTower.dirichletConv k (oscillatingSmoothPower ε t)) (mk * mc) n =
      (K * a₀ * ((n : ℝ) : ℂ) ^ ρ).re + ((D₁ n + D₂ n) + (D₃ n + D₄ n)) := by
    intro n hn
    have hnT := (mem_Icc.mp hn).2
    have hD₁ : D₁ n = ∑ j ∈ Icc 1 n, k j * oscillatingDilationRemainder ε t n j := by
      simp only [D₁, mul_ite, mul_zero, ← sum_filter]
      congr 1; ext j; simp only [mem_filter, mem_Icc]; omega
    have hpart : partialComplexPoleSum k ρ n =
        K - ∑ j ∈ Icc 1 T, (if n < j then (k j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ) else 0) - τ := by
      rw [hKsplit, partialComplexPoleSum, ← sum_filter_add_sum_filter_not (Icc 1 T) (fun j => j ≤ n)]
      have hfil1 : (Icc 1 T).filter (fun j => j ≤ n) = Icc 1 n := by
        ext j; simp only [mem_filter, mem_Icc]; omega
      have hfil2 : ∑ j ∈ (Icc 1 T).filter (fun j => ¬ j ≤ n),
          (k j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ) =
          ∑ j ∈ Icc 1 T, (if n < j then (k j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ) else 0) := by
        rw [← sum_filter]; congr 1; ext j; simp only [mem_filter, mem_Icc]; omega
      rw [hfil1, hfil2]; ring
    have hD₂ : D₂ n = -(a₀ * ((n : ℝ) : ℂ) ^ ρ *
        ∑ j ∈ Icc 1 T, (if n < j then (k j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ) else 0)).re := by
      simp only [D₂, mul_sum, Complex.re_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun j _ => ?_
      split_ifs with hnj
      · rw [show a₀ * ((n : ℝ) : ℂ) ^ ρ * ((k j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ)) =
            (k j : ℂ) * (a₀ * ((n : ℝ) : ℂ) ^ ρ * ((j : ℝ) : ℂ) ^ (-ρ)) by ring,
          Complex.re_ofReal_mul]
        ring
      · simp
    rw [weightCenteredPrefix_dirichletConv_oscillatingSmoothPower, ← hρ, ← ha₀, ← hmc, hD₁, hpart]
    have hlin : (a₀ * ((n : ℝ) : ℂ) ^ ρ *
        (K - ∑ j ∈ Icc 1 T, (if n < j then (k j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ) else 0) - τ)).re =
        (K * a₀ * ((n : ℝ) : ℂ) ^ ρ).re + D₂ n + D₄ n := by
      rw [hD₂]
      simp only [D₄]
      rw [show a₀ * ((n : ℝ) : ℂ) ^ ρ *
          (K - ∑ j ∈ Icc 1 T, (if n < j then (k j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ) else 0) - τ) =
          K * a₀ * ((n : ℝ) : ℂ) ^ ρ -
          a₀ * ((n : ℝ) : ℂ) ^ ρ *
            ∑ j ∈ Icc 1 T, (if n < j then (k j : ℂ) * ((j : ℝ) : ℂ) ^ (-ρ) else 0) -
          τ * a₀ * ((n : ℝ) : ℂ) ^ ρ by ring, Complex.sub_re, Complex.sub_re]
      ring
    rw [hlin]
    simp only [D₃]
    ring
  -- bound the four error pieces
  have hG0 : ∀ j : ℕ, 0 ≤ |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) := fun j => by positivity
  have hB₁ : pronicNorm D₁ T ≤ C₁ * G := by
    refine (pronicNorm_sum_le (Icc 1 T) _ T).trans ?_
    calc ∑ j ∈ Icc 1 T, pronicNorm (fun n =>
          k j * (if j ≤ n then oscillatingDilationRemainder ε t n j else 0)) T
        = ∑ j ∈ Icc 1 T, |k j| *
            pronicNorm (fun n => if j ≤ n then oscillatingDilationRemainder ε t n j else 0) T :=
          sum_congr rfl fun j _ => pronicNorm_smul _ _ _
      _ ≤ ∑ j ∈ Icc 1 T, |k j| * (C₁ * (j : ℝ) ^ (-(1 / 2 : ℝ))) :=
          sum_le_sum fun j hj => mul_le_mul_of_nonneg_left
            (pronicNorm_oscillatingDilationRemainder_le hε hε1 t (mem_Icc.mp hj).1 T) (abs_nonneg _)
      _ = C₁ * ∑ j ∈ Icc 1 T, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
      _ ≤ C₁ * G := mul_le_mul_of_nonneg_left (hW.sum_le_tsum _ fun j _ => hG0 j) (by positivity)
  have hB₂ : pronicNorm D₂ T ≤ C₂ * G := by
    refine (pronicNorm_sum_le (Icc 1 T) _ T).trans ?_
    have hj_le : ∀ j ∈ Icc 1 T,
        pronicNorm (fun n => if n < j then
          -(a₀ * ((n : ℝ) : ℂ) ^ ρ * ((j : ℝ) : ℂ) ^ (-ρ)).re else 0) T ≤
        C₂ * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
      intro j hj
      have hj1 := (mem_Icc.mp hj).1
      have hj0 : (0 : ℝ) < j := by exact_mod_cast hj1
      have hpt : ∀ n ∈ Icc 1 T,
          |if n < j then -(a₀ * ((n : ℝ) : ℂ) ^ ρ * ((j : ℝ) : ℂ) ^ (-ρ)).re else 0| ≤
          ‖a₀‖ * (if n < j then (n : ℝ) ^ (1 - ε) * (j : ℝ) ^ (-(1 - ε)) else 0) := by
        intro n hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        split_ifs with hlt
        · rw [abs_neg]
          refine (Complex.abs_re_le_norm _).trans ?_
          rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn0,
            Complex.norm_cpow_eq_rpow_re_of_pos hj0, neg_re, hρre, mul_assoc]
        · simp
      have hcomp : pronicNorm (fun n => if n < j then
          -(a₀ * ((n : ℝ) : ℂ) ^ ρ * ((j : ℝ) : ℂ) ^ (-ρ)).re else 0) T ≤
          ‖a₀‖ * pronicNorm (fun n => if n < j then
            (n : ℝ) ^ (1 - ε) * (j : ℝ) ^ (-(1 - ε)) else 0) T := by
        rw [← abs_of_nonneg (norm_nonneg a₀), ← pronicNorm_smul]
        unfold pronicNorm
        refine Real.sqrt_le_sqrt (sum_le_sum fun n hn => ?_)
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        rw [← sq_abs, ← sq_abs (‖a₀‖ * _), abs_mul, abs_of_nonneg (norm_nonneg a₀),
          abs_of_nonneg (by split_ifs <;> positivity)]
        exact pow_le_pow_left₀ (abs_nonneg _) (hpt n hn) 2
      exact hcomp.trans ((mul_le_mul_of_nonneg_left
        (pronicNorm_poleDeficit_below_le hε hε2 hj1 T) (norm_nonneg a₀)).trans
        (by rw [hC₂, mul_assoc]))
    calc ∑ j ∈ Icc 1 T, pronicNorm (fun n => k j * (if n < j then
          -(a₀ * ((n : ℝ) : ℂ) ^ ρ * ((j : ℝ) : ℂ) ^ (-ρ)).re else 0)) T
        = ∑ j ∈ Icc 1 T, |k j| * pronicNorm (fun n => if n < j then
            -(a₀ * ((n : ℝ) : ℂ) ^ ρ * ((j : ℝ) : ℂ) ^ (-ρ)).re else 0) T :=
          sum_congr rfl fun j _ => pronicNorm_smul _ _ _
      _ ≤ ∑ j ∈ Icc 1 T, |k j| * (C₂ * (j : ℝ) ^ (-(1 / 2 : ℝ))) :=
          sum_le_sum fun j hj => mul_le_mul_of_nonneg_left (hj_le j hj) (abs_nonneg _)
      _ = C₂ * ∑ j ∈ Icc 1 T, |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) := by
          rw [mul_sum]; exact sum_congr rfl fun j _ => by ring
      _ ≤ C₂ * G := mul_le_mul_of_nonneg_left (hW.sum_le_tsum _ fun j _ => hG0 j) (by positivity)
  have hB₃ : pronicNorm D₃ T ≤ |mc| * (Real.sqrt 2 + 1) * G := by
    simp only [D₃]
    rw [pronicNorm_smul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (pronicNorm_weightCenteredPrefix_le_critical hk T) (abs_nonneg _)
  have hB₄ : pronicNorm D₄ T ≤ C₂ * G := by
    have hT1 : (0 : ℝ) < (T : ℝ) + 1 := by positivity
    have hτbound : ‖τ‖ ≤ ((T : ℝ) + 1) ^ (-(1 / 2 - ε)) * G := by
      have hsumtail : Summable (fun m : ℕ =>
          |k (m + (T + 1))| * ((m + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) :=
        (summable_nat_add_iff (f := fun j : ℕ => |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ))) (T + 1)).mpr hW
      have hterm : ∀ m : ℕ,
          ‖(k (m + (T + 1)) : ℂ) * (((m + (T + 1) : ℕ) : ℝ) : ℂ) ^ (-ρ)‖ ≤
          ((T : ℝ) + 1) ^ (-(1 / 2 - ε)) *
            (|k (m + (T + 1))| * ((m + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by
        intro m
        have hm0 : (0 : ℝ) < ((m + (T + 1) : ℕ) : ℝ) := by positivity
        have hmT : (T : ℝ) + 1 ≤ ((m + (T + 1) : ℕ) : ℝ) := by
          push_cast; linarith [Nat.cast_nonneg (α := ℝ) m]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_cpow_eq_rpow_re_of_pos hm0, neg_re, hρre,
          show -(1 - ε) = -(1 / 2 - ε) + -(1 / 2 : ℝ) by ring, Real.rpow_add hm0]
        calc |k (m + (T + 1))| * (((m + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 - ε)) *
              ((m + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)))
            = ((m + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 - ε)) *
              (|k (m + (T + 1))| * ((m + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) := by ring
          _ ≤ ((T : ℝ) + 1) ^ (-(1 / 2 - ε)) *
              (|k (m + (T + 1))| * ((m + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_right
              (Real.rpow_le_rpow_of_nonpos hT1 hmT (by linarith)) (by positivity)
      have h1 := tsum_of_norm_bounded (hsumtail.mul_left (((T : ℝ) + 1) ^ (-(1 / 2 - ε)))).hasSum
        hterm
      have h2 : ∑' m : ℕ, |k (m + (T + 1))| * ((m + (T + 1) : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ G := by
        have h := hW.sum_add_tsum_nat_add (T + 1)
        have h0 : 0 ≤ ∑ j ∈ range (T + 1), |k j| * (j : ℝ) ^ (-(1 / 2 : ℝ)) :=
          sum_nonneg fun j _ => hG0 j
        linarith
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hT1.le _))
    have hpt : ∀ n ∈ Icc 1 T, |D₄ n| ≤ ‖τ‖ * ‖a₀‖ * (n : ℝ) ^ (1 - ε) := by
      intro n hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
      simp only [D₄, abs_neg]
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hn0, hρre]
    have hcomp : pronicNorm D₄ T ≤ ‖τ‖ * ‖a₀‖ * pronicNorm (fun n : ℕ => (n : ℝ) ^ (1 - ε)) T := by
      have hnn : 0 ≤ ‖τ‖ * ‖a₀‖ := by positivity
      rw [← abs_of_nonneg hnn, ← pronicNorm_smul]
      unfold pronicNorm
      refine Real.sqrt_le_sqrt (sum_le_sum fun n hn => ?_)
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      rw [← sq_abs, ← sq_abs (‖τ‖ * ‖a₀‖ * _), abs_mul, abs_of_nonneg hnn,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hpt n hn) 2
    have hcancel : ((T : ℝ) + 1) ^ (-(1 / 2 - ε)) * ((T : ℝ) + 1) ^ (1 / 2 - ε) = 1 := by
      rw [← Real.rpow_add hT1, neg_add_cancel, Real.rpow_zero]
    calc pronicNorm D₄ T
        ≤ ‖τ‖ * ‖a₀‖ * (Real.sqrt (1 + 1 / (1 - 2 * ε)) * ((T : ℝ) + 1) ^ (1 / 2 - ε)) :=
          hcomp.trans (mul_le_mul_of_nonneg_left (pronicNorm_rpow_one_sub_le hε hε2 T)
            (by positivity))
      _ ≤ (((T : ℝ) + 1) ^ (-(1 / 2 - ε)) * G) * ‖a₀‖ *
          (Real.sqrt (1 + 1 / (1 - 2 * ε)) * ((T : ℝ) + 1) ^ (1 / 2 - ε)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hτbound (norm_nonneg a₀))
            (by positivity)
      _ = C₂ * G * (((T : ℝ) + 1) ^ (-(1 / 2 - ε)) * ((T : ℝ) + 1) ^ (1 / 2 - ε)) := by
          rw [hC₂]; ring
      _ = C₂ * G := by rw [hcancel, mul_one]
  -- triangle inequality on `pronicNorm`
  set M : ℕ → ℝ := fun n => (K * a₀ * ((n : ℝ) : ℂ) ^ ρ).re
  set R : ℕ → ℝ := fun n => (D₁ n + D₂ n) + (D₃ n + D₄ n)
  have hR : pronicNorm R T ≤ (C₁ + C₂ + |mc| * (Real.sqrt 2 + 1) + C₂) * G := by
    have h1 := (pronicNorm_add_le (fun n => D₁ n + D₂ n) (fun n => D₃ n + D₄ n) T).trans
      (add_le_add ((pronicNorm_add_le D₁ D₂ T).trans (add_le_add hB₁ hB₂))
        ((pronicNorm_add_le D₃ D₄ T).trans (add_le_add hB₃ hB₄)))
    linarith
  have h1 := pronicNorm_add_le M R T
  rw [← pronicNorm_congr hrep] at h1
  have h2 : pronicNorm M T ≤
      pronicNorm (weightCenteredPrefix (RHTower.dirichletConv k (oscillatingSmoothPower ε t))
        (mk * mc)) T + pronicNorm R T := by
    have h := pronicNorm_add_le
      (weightCenteredPrefix (RHTower.dirichletConv k (oscillatingSmoothPower ε t)) (mk * mc))
      (fun n => (-1) * R n) T
    rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at h
    refine le_of_eq_of_le (pronicNorm_congr fun n hn => ?_) h
    rw [hrep n hn]; ring
  have hM : ∀ n, (K * riemannZeta ρ / ρ * ((n : ℝ) : ℂ) ^ ρ).re = M n := fun n => by
    simp only [M, ha₀, mul_div_assoc]
  simp_rw [hM]
  rw [abs_le]
  constructor <;> linarith

/-- **Harmonic lower bound for `Re(a n^ρ)`.** For `0 < ε ≤ 1/2`, `t ∈ ℝ`, `ρ = 1 − ε + it`, and
`a ∈ ℂ`, if `pronicNorm (fun n => Re(a n^ρ)) T` is uniformly bounded in `T` (and `a.re = 0 → a = 0`
when `t = 0`), then `a = 0`. -/
theorem eq_zero_of_pronicNorm_re_cpow_bounded {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) (t : ℝ)
    {a : ℂ} (ha0 : t = 0 → a.re = 0 → a = 0) {B : ℝ}
    (hB : ∀ T : ℕ, pronicNorm (fun n : ℕ => (a * ((n : ℝ) : ℂ) ^ oscillationExponent ε t).re) T ≤
      B) :
    a = 0 := by
  by_contra hane
  set ρ := oscillationExponent ε t with hρ
  set M : ℕ → ℝ := fun n => (a * ((n : ℝ) : ℂ) ^ ρ).re with hM
  set u : ℕ → ℝ := fun n => (a * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I)).re with hu
  have hMu : ∀ n : ℕ, 1 ≤ n → M n = (n : ℝ) ^ (1 - ε) * u n := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsplit : ((n : ℝ) : ℂ) ^ ρ =
        (((n : ℝ) ^ (1 - ε) : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I) := by
      rw [hρ, oscillationExponent, Complex.cpow_add _ _ (by exact_mod_cast hn0.ne'),
        Complex.ofReal_cpow hn0.le]
    simp only [hM, hu]
    rw [hsplit, mul_left_comm, Complex.re_ofReal_mul]
  have hlow : ∀ T : ℕ, ∑ n ∈ Icc 1 T, u n ^ 2 / n ≤ 2 * B ^ 2 := by
    intro T
    have hMsq : ∑ n ∈ Icc 1 T, M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) ≤ B ^ 2 := by
      have h1 := pow_le_pow_left₀ (pronicNorm_nonneg M T) (hB T) 2
      rwa [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)] at h1
    have hterm : ∀ n ∈ Icc 1 T, u n ^ 2 / n ≤ 2 * (M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := by
      intro n hn
      have hn1 := (mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      have hpow : (n : ℝ) ≤ ((n : ℝ) ^ (1 - ε)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
        calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (n : ℝ) ^ ((1 - ε) * ((2 : ℕ) : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le hnR (by push_cast; linarith)
      rw [hMu n hn1, mul_pow]
      rw [div_le_iff₀ hn0, mul_comm 2, mul_assoc]
      have hpr : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hpr]
      have hu2 : 0 ≤ u n ^ 2 := sq_nonneg _
      calc u n ^ 2 * ((n : ℝ) * ((n : ℝ) + 1)) ≤ u n ^ 2 * (2 * (n : ℝ) * n) :=
            mul_le_mul_of_nonneg_left (by nlinarith) hu2
        _ = ((n : ℝ) * u n ^ 2) * (2 * n) := by ring
        _ ≤ (((n : ℝ) ^ (1 - ε)) ^ 2 * u n ^ 2) * (2 * n) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hu2) (by positivity)
    calc _ ≤ ∑ n ∈ Icc 1 T, 2 * (M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) := sum_le_sum hterm
      _ = 2 * ∑ n ∈ Icc 1 T, M n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by rw [mul_sum]
      _ ≤ 2 * B ^ 2 := by linarith
  have husq : ∀ n : ℕ, 1 ≤ n → u n ^ 2 =
      (‖a‖ ^ 2 + (a ^ 2 * ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I)).re) / 2 := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    set z := a * ((n : ℝ) : ℂ) ^ ((t : ℂ) * I) with hz
    have hw : ‖((n : ℝ) : ℂ) ^ ((t : ℂ) * I)‖ = 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0]; simp
    have hz2 : z ^ 2 = a ^ 2 * ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) := by
      rw [hz, mul_pow, sq (((n : ℝ) : ℂ) ^ ((t : ℂ) * I)),
        ← Complex.cpow_add _ _ (by exact_mod_cast hn0.ne')]
      push_cast; ring_nf
    have hnorm : ‖z‖ ^ 2 = ‖a‖ ^ 2 := by rw [hz, norm_mul, hw, mul_one]
    have hre : ∀ x : ℂ, x.re ^ 2 = (‖x‖ ^ 2 + (x ^ 2).re) / 2 := fun x => by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, sq x, Complex.mul_re]; ring
    show z.re ^ 2 = _
    rw [hre z, hnorm, hz2]
  have hsum : ∀ T : ℕ, ∑ n ∈ Icc 1 T, u n ^ 2 / n =
      ‖a‖ ^ 2 / 2 * ∑ n ∈ Icc 1 T, 1 / (n : ℝ) +
        (a ^ 2 * ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) / ((n : ℝ) : ℂ)).re / 2 := by
    intro T
    rw [mul_sum, mul_sum, Complex.re_sum, sum_div, ← sum_add_distrib]
    refine sum_congr rfl fun n hn => ?_
    have hn1 := (mem_Icc.mp hn).1
    have hdiv : (a ^ 2 * (((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) / ((n : ℝ) : ℂ))).re =
        (a ^ 2 * ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I)).re / n := by
      rw [← mul_div_assoc, Complex.div_ofReal_re]
    rw [husq n hn1, hdiv]
    ring
  rcases eq_or_ne t 0 with ht0 | ht0
  · have hare : a.re ≠ 0 := fun h => hane (ha0 ht0 h)
    have hu0 : ∀ n : ℕ, u n = a.re := fun n => by simp [hu, ht0]
    obtain ⟨T, -, hT⟩ := not_bddAbove_sum_Icc_one_div (2 * B ^ 2 / a.re ^ 2)
    have h := hlow T
    have heq : ∑ n ∈ Icc 1 T, u n ^ 2 / n = a.re ^ 2 * ∑ n ∈ Icc 1 T, 1 / (n : ℝ) := by
      rw [mul_sum]; exact sum_congr rfl fun n _ => by rw [hu0]; ring
    rw [heq] at h
    have ha2 : 0 < a.re ^ 2 := sq_pos_of_ne_zero hare
    rw [div_lt_iff₀ ha2] at hT
    linarith
  · set w : ℂ := 1 - ((2 * t : ℝ) : ℂ) * I with hw
    have hwre : 0 < w.re := by simp [hw]
    have hwne : w ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp [hw] at this
      exact ht0 this
    set B₂ := 1 / ‖((2 * t : ℝ) : ℂ) * I‖ + ‖riemannZeta w‖ + partialSumRate w with hB₂
    have hS : ∀ T : ℕ, 1 ≤ T →
        ‖∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) / ((n : ℝ) : ℂ)‖ ≤ B₂ := by
      intro T hT
      have hT0 : (0 : ℝ) < T := by exact_mod_cast hT
      have hcp : ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) / ((n : ℝ) : ℂ) =
          cpowPartialSum w T := by
        rw [cpowPartialSum]
        refine sum_congr rfl fun n hn => ?_
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
        have hnC : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
        rw [hw, show -(1 - ((2 * t : ℝ) : ℂ) * I) = ((2 * t : ℝ) : ℂ) * I - 1 by ring,
          Complex.cpow_sub _ _ hnC, Complex.cpow_one]
      have h := norm_cpowPartialSum_sub_le hwre hwne hT le_rfl (by linarith)
      rw [show (1 : ℂ) - w = ((2 * t : ℝ) : ℂ) * I by rw [hw]; ring] at h
      have hT1 : ‖((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I)‖ = 1 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hT0]; simp
      have hTpow : (T : ℝ) ^ (-w.re) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hT) (by linarith)
      have hrate0 := partialSumRate_nonneg hwre
      rw [hcp]
      calc ‖cpowPartialSum w T‖ ≤ ‖((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
            (((2 * t : ℝ) : ℂ) * I)‖ + ‖riemannZeta w‖ +
            ‖cpowPartialSum w T - ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
              (((2 * t : ℝ) : ℂ) * I) - riemannZeta w‖ := by
            have e : cpowPartialSum w T = ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
                (((2 * t : ℝ) : ℂ) * I) + riemannZeta w +
                (cpowPartialSum w T - ((T : ℝ) : ℂ) ^ (((2 * t : ℝ) : ℂ) * I) /
                  (((2 * t : ℝ) : ℂ) * I) - riemannZeta w) := by ring
            exact (congrArg norm e).le.trans
              ((norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _))
        _ ≤ 1 / ‖((2 * t : ℝ) : ℂ) * I‖ + ‖riemannZeta w‖ + partialSumRate w * 1 := by
            rw [norm_div, hT1]
            gcongr
            exact h.trans (mul_le_mul_of_nonneg_left hTpow hrate0)
        _ = B₂ := by rw [mul_one]
    have hna : 0 < ‖a‖ ^ 2 := by
      have : 0 < ‖a‖ := norm_pos_iff.mpr hane
      positivity
    obtain ⟨T, hT1, hT⟩ := not_bddAbove_sum_Icc_one_div ((4 * B ^ 2 + ‖a‖ ^ 2 * B₂) / ‖a‖ ^ 2)
    have h := hlow T
    rw [hsum T] at h
    have hre : |(a ^ 2 * ∑ n ∈ Icc 1 T, ((n : ℝ) : ℂ) ^ ((2 * t : ℝ) * I) / ((n : ℝ) : ℂ)).re| ≤
        ‖a‖ ^ 2 * B₂ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hS T hT1) (by positivity)
    rw [div_lt_iff₀ hna] at hT
    have := (abs_le.mp hre).1
    nlinarith

/-- At `t = 0`, `complexPoleValue k (oscillationExponent ε 0)` has vanishing imaginary part. -/
theorem im_complexPoleValue_zero (k : ℕ → ℝ) (ε : ℝ) :
    (complexPoleValue k (oscillationExponent ε 0)).im = 0 := by
  have hterm : ∀ j : ℕ,
      (k j : ℂ) * ((j : ℝ) : ℂ) ^ (-oscillationExponent ε 0) =
      ((k j * (j : ℝ) ^ (-(1 - ε)) : ℝ) : ℂ) := fun j => by
    simp only [oscillationExponent, ofReal_zero, zero_mul, add_zero]
    rw [← ofReal_neg, ← Complex.ofReal_cpow (Nat.cast_nonneg j), ← ofReal_mul]
  unfold complexPoleValue
  simp_rw [hterm, ← Complex.ofReal_tsum, ofReal_im]

/-- **The shifted-pole hyperplane law on the critical Wiener algebra.** For `0 < ε < 1/2`,
`t ∈ ℝ`, and `k` in the critical Wiener algebra `Σ_j |k(j)| j^{-1/2} < ∞`, the convolution
`k ⋆ oscillatingSmoothPower ε t` has bounded receiver if and only if
`Σ_j k(j) j^{-(1 − ε + it)} = 0` or `ζ(1 − ε + it) = 0`. -/
theorem receiverBounded_dirichletConv_oscillatingSmoothPower_iff {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) (t : ℝ) {k : ℕ → ℝ} (hk : CriticalWiener k) :
    ReceiverBounded (RHTower.dirichletConv k (oscillatingSmoothPower ε t)) ↔
      complexPoleValue k (oscillationExponent ε t) = 0 ∨
        riemannZeta (oscillationExponent ε t) = 0 := by
  obtain ⟨B, hB⟩ := exists_abs_pronicNorm_dirichletConv_oscillatingSmoothPower_sub_le hε hε2 t hk
  set ρ := oscillationExponent ε t with hρ
  set c := RHTower.dirichletConv k (oscillatingSmoothPower ε t)
  set m := ∑' d : ℕ, c d / d
  set a := complexPoleValue k ρ * riemannZeta ρ / ρ with ha
  set M : ℕ → ℝ := fun n => (a * ((n : ℝ) : ℂ) ^ ρ).re
  constructor
  · rintro ⟨E, hE⟩
    have hM : ∀ T : ℕ, pronicNorm M T ≤ Real.sqrt E + B := fun T => by
      have h1 : pronicNorm (weightCenteredPrefix c m) T ≤ Real.sqrt E := by
        rw [pronicNorm]; exact Real.sqrt_le_sqrt (hE T)
      have h2 := (abs_le.mp (hB T)).1
      linarith
    have ha0 : t = 0 → a.re = 0 → a = 0 := by
      intro ht0 hare
      have hK_im : (complexPoleValue k ρ).im = 0 := by
        rw [hρ, ht0]; exact im_complexPoleValue_zero k ε
      have hK_eq : complexPoleValue k ρ = ((complexPoleValue k ρ).re : ℂ) :=
        Complex.ext rfl hK_im
      have hρ_eq : ρ = ((1 - ε : ℝ) : ℂ) := by
        simp [hρ, oscillationExponent, ht0]
      have ha_re : a.re =
          (complexPoleValue k ρ).re * (riemannZeta ((1 - ε : ℝ) : ℂ)).re / (1 - ε) := by
        rw [ha, hK_eq, hρ_eq, Complex.div_ofReal_re, Complex.re_ofReal_mul]
      have hz_neg : (riemannZeta ((1 - ε : ℝ) : ℂ)).re < 0 := by
        have hz := riemannZeta_re_le_of_lt_one (σ := 1 - ε) (by linarith) (by linarith)
        have hneg : -(1 - ε) / (1 - (1 - ε)) < 0 := div_neg_of_neg_of_pos (by linarith) (by linarith)
        linarith
      rw [ha_re, div_eq_zero_iff, mul_eq_zero] at hare
      have hK_re : (complexPoleValue k ρ).re = 0 :=
        (hare.resolve_right (by linarith)).resolve_right hz_neg.ne
      have hK0 : complexPoleValue k ρ = 0 := Complex.ext hK_re hK_im
      rw [ha, hK0, zero_mul, zero_div]
    have haz := eq_zero_of_pronicNorm_re_cpow_bounded hε hε2.le t ha0 hM
    have hρ0 : ρ ≠ 0 := oscillationExponent_ne_zero (by linarith) t
    rw [ha, div_eq_zero_iff, mul_eq_zero] at haz
    exact haz.resolve_right hρ0
  · intro hzero
    have ha_zero : a = 0 := by
      rcases hzero with hK | hζ
      · simp [ha, hK]
      · simp [ha, hζ]
    refine ⟨B ^ 2, fun T => ?_⟩
    have hM0 : pronicNorm M T = 0 := by
      simp [M, ha_zero, pronicNorm]
    have h1 := (abs_le.mp (hB T)).2
    rw [hM0, sub_zero] at h1
    rw [weightPronicEnergy_eq_sq_pronicNorm]
    exact pow_le_pow_left₀ (pronicNorm_nonneg _ T) h1 2

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
