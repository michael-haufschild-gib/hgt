import GaloisForLFunctions.RHTower.WeilConeSettledLockRigidity
import GaloisForLFunctions.RHTower.WeilAlmostPeriodicLockRigidity
import GaloisForLFunctions.RHTower.HamburgerTwistedRadialDefect

/-!
# Almost-periodic locks with a settling remainder

Let `G` be a producer for a full-cone Weil-positive `lam`, with lower-line lock

`G(1 − s) = κ₀ (P(x) + r(x)) G(s)`,  `s = ½ − 2ix`, `x > 1`,

where `P(x) = Σ_j p_j e^{iω_j x}` with `Σ_j |p_j| e^{|ω_j|/2} < ∞` and no nonzero frequency
resonant (`e^{−ω_j/2} ∉ ℚ_{>0}`), and `r` is bounded and measurable.

**Theorem** (`ap_settled_lock_rigidity`).  If the remainder is small in block mean,
`∫_T^{2T} |r(x)| |G(½+2ix)/(s(s−1)Γ_ℝ(s))| dx = o(T)`, then `κ₀ p₀ ≠ 0` (`p₀` the mean of `P`),
`lam = Λ` and RH holds.

**Corollary** (`ap_uniformly_settled_lock_rigidity`).  In the class of
`exists_setIntegral_exp_mul_le`, the block condition holds when
`|r(x)| = O((log T)^{−κ²/4−η})` on `(T, 2T]`.

So an almost-periodic lock may carry an arbitrary rough perturbation that settles at a
log-power rate.  The almost-periodic part may have phase variation of linear order, and the
perturbation may have linear total variation.

**Proof.**  Write the lock as `G(1 − s) = κ₀p₀ G(s) + s(s−1)Γ_ℝ(s) e` with
`e = κ₀((P − p₀) + r) φ_G`.  The radial limits of the defect `e` vanish at every height `m`.
* For `P − p₀` this follows from the twisted far integrals (`tendsto_ap_far_sub_mean`): each
  nonzero frequency is non-resonant, and dominated convergence applies with the uniform bound
  `O(e^{|ω|/2})`.
* For `r` it follows from Abel-sublinearity (`tendsto_mul_abelMass_of_blocks`).
* At height `0` every polynomially bounded defect vanishes radially (`tendsto_mul_defectLaplace_zero`).

If `κ₀p₀ = 0` the reflected radial limit `β/π ≠ 0` would vanish.  Otherwise
`phase_lock_rigidity_of_radial_defect` applies.
-/

open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz IntegerMassRigidity FractionalMassRigidity AbelianTwist PhaseLockRigidity
  HamburgerStability

/-- At height `0` every polynomially bounded defect vanishes radially. -/
theorem tendsto_mul_defectLaplace_zero {g : ℝ → ℂ} {Cg : ℝ} {N : ℕ}
    (hgm : AEStronglyMeasurable g volume) (hgb : ∀ t, ‖g t‖ ≤ Cg * (1 + |t|) ^ N) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace g ((ε : ℂ) + ((0 : ℕ) : ℂ) * I)) (𝓝[>] 0)
      (𝓝 0) := by
  have hpi := Real.pi_pos
  refine squeeze_zero_norm'
    (a := fun ε : ℝ => 3 / (2 * Real.pi) * abelMass g 2 * ε ^ (1 / 2 : ℝ)) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hτ : 0 < ((ε : ℂ)).re := by simpa using hε'
    have h := norm_defectLaplace_le hgm hgb hτ
    have hn : ‖(ε : ℂ)‖ = ε := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε']
    have hre : ((ε : ℂ)).re / ‖(ε : ℂ)‖ = 1 := by rw [hn]; simp [hε'.ne']
    rw [hre, hn, mul_one] at h
    rw [norm_mul, hn]
    have hA0 : 0 ≤ abelMass g 2 := integral_nonneg fun t => by positivity
    calc ε * ‖defectLaplace g ε‖ ≤ ε * (3 / (2 * Real.pi) * ε ^ (-(1 / 2 : ℝ)) * abelMass g 2) :=
          mul_le_mul_of_nonneg_left h hε'.le
      _ = 3 / (2 * Real.pi) * abelMass g 2 * (ε * ε ^ (-(1 / 2 : ℝ))) := by ring
      _ = 3 / (2 * Real.pi) * abelMass g 2 * ε ^ (1 / 2 : ℝ) := by
          congr 1
          have e1 : ε * ε ^ (-(1 / 2 : ℝ)) = ε ^ (1 : ℝ) * ε ^ (-(1 / 2 : ℝ)) := by
            rw [Real.rpow_one]
          rw [e1, ← Real.rpow_add hε']
          norm_num
  · have hc : ContinuousAt (fun ε : ℝ => ε ^ (1 / 2 : ℝ)) 0 :=
      Real.continuousAt_rpow_const 0 (1 / 2) (Or.inr (by norm_num))
    have h0 : Tendsto (fun ε : ℝ => ε ^ (1 / 2 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
      have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa [Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using this
    simpa using h0.const_mul (3 / (2 * Real.pi) * abelMass g 2)

/-- **The far part of a non-resonant almost-periodic defect vanishes radially.** -/
theorem tendsto_ap_far_sub_mean {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {p : ℕ → ℂ} {ω : ℕ → ℝ} (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2))
    {m : ℕ} (hm : 1 ≤ m) (hres : ∀ j, ω j ≠ 0 → ∀ n : ℕ, (n : ℝ) ≠ m * Real.exp (-(ω j / 2))) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * ∫ t in Iic (-1 : ℝ),
      ((apFactor p ω (-t) - apMean p ω) * phiG G t) * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I))
      (𝓝[>] 0) (𝓝 0) := by
  have hp1 := summable_norm_of_exp hp
  obtain ⟨K, hK0, hK⟩ := exists_norm_twistRadial_uniform hsl hΦre hid hGc hGd hG2 hm
  set F : ℕ → ℝ → ℂ := fun j ε => (ε : ℂ) * ∫ t in Iic (-1 : ℝ),
    phiG (twistG (ω j) G) t * pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I) with hF
  set F' : ℕ → ℝ → ℂ := fun j ε => if ω j = 0 then 0 else F j ε with hF'
  have hser : Tendsto (fun ε => ∑' j, p j * F' j ε) (𝓝[>] 0) (𝓝 0) := by
    have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
      (f := fun ε j => p j * F' j ε) (g := fun _ => (0 : ℂ))
      (bound := fun j => ‖p j‖ * Real.exp (|ω j| / 2) * K) (hp.mul_right K) (fun j => ?_) ?_
    · simpa using h
    · by_cases hj : ω j = 0
      · simp only [hF', hj, if_true, mul_zero]; exact tendsto_const_nhds
      · have h1 := (tendsto_far_nonres hsl hΦd hΦre hid hGc hGd hG2 (ω j) hm (hres j hj)).const_mul
          (p j)
        rw [mul_zero] at h1
        simpa only [hF', hj, if_false, hF] using h1
    · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε j
      by_cases hj : ω j = 0
      · simp only [hF', hj, if_true, mul_zero, norm_zero]; positivity
      · simp only [hF', hj, if_false, norm_mul]
        have h1 := hK (ω j) ε hε.1 hε.2.le
        calc ‖p j‖ * ‖F j ε‖ ≤ ‖p j‖ * (K * Real.exp (|ω j| / 2)) :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = ‖p j‖ * Real.exp (|ω j| / 2) * K := by ring
  refine hser.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  set τ : ℂ := (ε : ℂ) + (m : ℂ) * I with hτ
  have hτre0 : 0 < τ.re := by simp [hτ]; exact hε.1
  have hphik := (MonotoneTwistLock.integrable_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2
    hτre0).integrableOn (s := Iic (-1 : ℝ))
  have hint := (integrable_apFactor_phiG_mul_pairKernel hsl hΦre hid hGc hGd hG2 (ω := ω) hp1
    hτre0).integrableOn (s := Iic (-1 : ℝ))
  have hsplit : ∫ t in Iic (-1 : ℝ), ((apFactor p ω (-t) - apMean p ω) * phiG G t) *
      pairKernel (2 * t) τ = (∫ t in Iic (-1 : ℝ), (apFactor p ω (-t) * phiG G t) *
        pairKernel (2 * t) τ) - apMean p ω * ∫ t in Iic (-1 : ℝ), phiG G t * pairKernel (2 * t) τ := by
    rw [← integral_const_mul, ← integral_sub hint (hphik.const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    ring
  rw [hsplit, far_apFactor_eq_tsum hsl hΦre hid hGc hGd hG2 hp1 hτre0]
  unfold apMean
  have hs1 : Summable fun j => p j * ∫ t in Iic (-1 : ℝ),
      phiG (twistG (ω j) G) t * pairKernel (2 * t) τ := by
    refine Summable.of_norm_bounded (hp1.mul_right
      (∫ t in Iic (-1 : ℝ), ‖phiG G t * pairKernel (2 * t) τ‖)) fun j => ?_
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans
      (le_of_eq ?_)) (norm_nonneg _)
    congr 1; funext t
    simp only [norm_mul, norm_phiG_twistG]
  have hs2 : Summable fun j => (if ω j = 0 then p j else 0) := by
    refine Summable.of_norm_bounded hp1 fun j => ?_
    split_ifs <;> simp
  rw [← tsum_mul_right, ← hs1.tsum_sub (hs2.mul_right _), ← tsum_mul_left]
  congr 1; funext j
  by_cases hj : ω j = 0
  · simp only [hF', hj, if_true, twistG_zero]; ring
  · simp only [hF', hj, if_false, hF, zero_mul, sub_zero]; ring

/-- **Almost-periodic locks with a settling remainder are rigid.** -/
theorem ap_settled_lock_rigidity {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {p : ℕ → ℂ} {ω : ℕ → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2))
    (hres : ∀ j, ω j ≠ 0 → ∀ m n : ℕ, 1 ≤ m → (n : ℝ) ≠ m * Real.exp (-(ω j / 2)))
    {r : ℝ → ℂ} (hrm : Measurable r) {Cr : ℝ} (hrb : ∀ x, ‖r x‖ ≤ Cr) {κ₀ : ℂ}
    (hlock : ∀ τ : ℝ, τ < -1 →
      G (1 - lineS τ) = κ₀ * (apFactor p ω (-τ) + r (-τ)) * G (lineS τ))
    (hblock : ∀ η : ℝ, 0 < η → ∃ T₀ : ℝ, ∀ T, T₀ ≤ T →
      ∫ x in Ioc T (2 * T), ‖r x‖ * ‖phiG G x‖ ≤ η * T) :
    κ₀ * apMean p ω ≠ 0 ∧ (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧
      RiemannHypothesis := by
  have hsl := fun (σ : ℝ) (hσ : 1 < σ) =>
    WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW hσ
  have hid := fun (s : ℂ) (hs : 1 < s.re) => weilContinuation_eq_lamTwo hW hs
  have hΦre := fun (s : ℂ) (hs : 1 / 2 < s.re) => re_weilContinuation_nonneg hW hs
  have hΦd := differentiableOn_weilContinuation hW
  have hp1 := summable_norm_of_exp hp
  obtain ⟨CB, N, hCB, hpoly⟩ := exists_poly_bound_lineG hsl hΦre hid hGc hGd hG2
  have hCr : 0 ≤ Cr := (norm_nonneg _).trans (hrb 0)
  set S : ℝ := ∑' j, ‖p j‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun j => norm_nonneg _
  have hP : ∀ x, ‖apFactor p ω x‖ ≤ S := fun x => norm_apFactor_le hp1 x
  have hM : ‖apMean p ω‖ ≤ S := by
    unfold apMean
    have hsi : Summable fun j => ‖if ω j = 0 then p j else 0‖ :=
      Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => by split_ifs <;> simp) hp1
    refine (norm_tsum_le_tsum_norm hsi).trans (Summable.tsum_le_tsum (fun j => ?_) hsi hp1)
    split_ifs <;> simp
  have hPc : Continuous fun t : ℝ => apFactor p ω (-t) :=
    (continuous_apFactor hp1).comp continuous_neg
  have hφc := continuous_phiG (G := G) hGc
  -- the two defects
  set eA : ℝ → ℂ := fun t => κ₀ * ((apFactor p ω (-t) - apMean p ω) * phiG G t) with heA
  set eR : ℝ → ℂ := fun t => κ₀ * (r (-t) * phiG G t) with heR
  have heAm : Measurable eA := (measurable_const.mul
    ((hPc.sub continuous_const).mul hφc).measurable)
  have heRm : Measurable eR := measurable_const.mul ((hrm.comp measurable_neg).mul hφc.measurable)
  have heAb : ∀ t, ‖eA t‖ ≤ (‖κ₀‖ * (2 * S) * CB) * (1 + |t|) ^ N := by
    intro t
    simp only [heA, norm_mul]
    have h1 : ‖apFactor p ω (-t) - apMean p ω‖ ≤ 2 * S :=
      (norm_sub_le _ _).trans (by linarith [hP (-t)])
    calc ‖κ₀‖ * (‖apFactor p ω (-t) - apMean p ω‖ * ‖phiG G t‖)
        ≤ ‖κ₀‖ * ((2 * S) * (CB * (1 + |t|) ^ N)) := by
          gcongr
          exact (hpoly t).1
      _ = (‖κ₀‖ * (2 * S) * CB) * (1 + |t|) ^ N := by ring
  have heRb : ∀ t, ‖eR t‖ ≤ (‖κ₀‖ * Cr * CB) * (1 + |t|) ^ N := by
    intro t
    simp only [heR, norm_mul]
    calc ‖κ₀‖ * (‖r (-t)‖ * ‖phiG G t‖) ≤ ‖κ₀‖ * (Cr * (CB * (1 + |t|) ^ N)) := by
          gcongr
          · exact hrb _
          · exact (hpoly t).1
      _ = (‖κ₀‖ * Cr * CB) * (1 + |t|) ^ N := by ring
  set e : ℝ → ℂ := fun t => eA t + eR t with he
  have hem : Measurable e := heAm.add heRm
  have heb : ∀ t, ‖e t‖ ≤ ((‖κ₀‖ * (2 * S) * CB) + (‖κ₀‖ * Cr * CB)) * (1 + |t|) ^ N := by
    intro t
    calc ‖e t‖ ≤ ‖eA t‖ + ‖eR t‖ := norm_add_le _ _
      _ ≤ _ := by have := heAb t; have := heRb t; nlinarith
  -- the lock in defect form
  set c : ℂ := κ₀ * apMean p ω with hc
  have hD : ∀ τ, lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) ≠ 0 := fun τ =>
    mul_ne_zero (mul_ne_zero (lineS_ne_zero τ) (sub_ne_zero.mpr (lineS_ne_one τ)))
      (Gammaℝ_lineS_ne_zero τ)
  have hlock' : ∀ τ : ℝ, τ < -1 → G (1 - lineS τ) =
      c * G (lineS τ) + lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ) * e τ := by
    intro τ hτ
    rw [hlock τ hτ]
    simp only [he, heA, heR, hc]
    unfold phiG
    set D := lineS τ * (lineS τ - 1) * Complex.Gammaℝ (lineS τ)
    have hDG : D * (G (lineS τ) / D) = G (lineS τ) := mul_div_cancel₀ _ (hD τ)
    calc κ₀ * (apFactor p ω (-τ) + r (-τ)) * G (lineS τ)
        = κ₀ * apMean p ω * G (lineS τ) + (κ₀ * ((apFactor p ω (-τ) - apMean p ω) +
            r (-τ))) * (D * (G (lineS τ) / D)) := by rw [hDG]; ring
      _ = _ := by ring
  -- radial limits of the defect
  have hAbel : Tendsto (fun δ => δ * abelMass ((Iio (-1 : ℝ)).indicator eR) δ) (𝓝[>] 0)
      (𝓝 0) := by
    have hgm : Measurable ((Iio (-1 : ℝ)).indicator eR) := heRm.indicator measurableSet_Iio
    refine tendsto_mul_abelMass_of_blocks hgm (fun t => (norm_indicator_le_norm_self _ t).trans
      (heRb t)) (fun t ht => ?_) fun η hη => ?_
    · rw [Set.indicator_of_notMem (show t ∉ Iio (-1 : ℝ) from fun h => by
        simp only [mem_Iio] at h; linarith)]
    · obtain ⟨T₀, hT₀⟩ := hblock (η / (‖κ₀‖ + 1)) (by positivity)
      refine ⟨max T₀ 1, by positivity, fun T hT => ?_⟩
      have hT1 : 1 ≤ T := (le_max_right _ _).trans hT
      have hbT := hT₀ T ((le_max_left _ _).trans hT)
      have heq : ∀ τ ∈ Ioc T (2 * T), ‖(Iio (-1 : ℝ)).indicator eR (-τ)‖ =
          ‖κ₀‖ * (‖r τ‖ * ‖phiG G τ‖) := by
        intro τ hτ
        rw [Set.indicator_of_mem (show -τ ∈ Iio (-1 : ℝ) by
          simp only [mem_Iio]; linarith [hτ.1])]
        simp only [heR, norm_mul, neg_neg]
        rw [norm_phiG_neg hW hGc hGd hG2]
      rw [setIntegral_congr_fun measurableSet_Ioc heq, integral_const_mul]
      have hI0 : 0 ≤ ∫ x in Ioc T (2 * T), ‖r x‖ * ‖phiG G x‖ :=
        setIntegral_nonneg measurableSet_Ioc fun x _ => by positivity
      have hk : ‖κ₀‖ ≤ ‖κ₀‖ + 1 := by linarith
      calc ‖κ₀‖ * ∫ x in Ioc T (2 * T), ‖r x‖ * ‖phiG G x‖
          ≤ (‖κ₀‖ + 1) * ∫ x in Ioc T (2 * T), ‖r x‖ * ‖phiG G x‖ :=
            mul_le_mul_of_nonneg_right hk hI0
        _ ≤ (‖κ₀‖ + 1) * (η / (‖κ₀‖ + 1) * T) := mul_le_mul_of_nonneg_left hbT (by positivity)
        _ = η * T := by field_simp
  have hRrad : ∀ m : ℕ, Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace
      ((Iio (-1 : ℝ)).indicator eR) ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := fun m =>
    tendsto_mul_defectLaplace_radial (heRm.indicator measurableSet_Iio).aestronglyMeasurable
      (fun t => (norm_indicator_le_norm_self _ t).trans (heRb t)) hAbel m
  have hArad : ∀ m : ℕ, Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace
      ((Iio (-1 : ℝ)).indicator eA) ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      exact tendsto_mul_defectLaplace_zero (heAm.indicator measurableSet_Iio).aestronglyMeasurable
        (fun t => (norm_indicator_le_norm_self _ t).trans (heAb t))
    · have hfar := tendsto_ap_far_sub_mean hsl hΦd hΦre hid hGc hGd hG2 hp (m := m) hm0
        (fun j hj n => hres j hj m n hm0)
      have h := hfar.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ) * κ₀)
      rw [mul_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      unfold defectLaplace
      have hind : (fun t => (Iio (-1 : ℝ)).indicator eA t * pairKernel (2 * t)
          ((ε : ℂ) + (m : ℂ) * I)) = (Iio (-1 : ℝ)).indicator (fun t => eA t *
          pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)) := by
        funext t
        by_cases ht : t ∈ Iio (-1 : ℝ)
        · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
        · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht, zero_mul]
      rw [hind, integral_indicator measurableSet_Iio, ← integral_Iic_eq_integral_Iio]
      simp only [heA]
      rw [show (fun t => κ₀ * ((apFactor p ω (-t) - apMean p ω) * phiG G t) *
          pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)) = fun t => κ₀ *
          (((apFactor p ω (-t) - apMean p ω) * phiG G t) *
            pairKernel (2 * t) ((ε : ℂ) + (m : ℂ) * I)) by funext t; ring, integral_const_mul]
      ring
  have hrad : ∀ m : ℕ, Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace
      ((Iio (-1 : ℝ)).indicator e) ((ε : ℂ) + (m : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
    intro m
    have h := (hArad m).add (hRrad m)
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0 : ℝ) < ε := hε
    have hτ : 0 < ((ε : ℂ) + (m : ℂ) * I).re := by simpa using hε'
    have hlin := HamburgerTwisted.defectLaplace_indicator_eq (g := e) (Φ := eA) (r := eR)
      (s := Iio (-1 : ℝ))
      (Cg := (‖κ₀‖ * (2 * S) * CB) + (‖κ₀‖ * Cr * CB)) (N := N)
      heAm.aestronglyMeasurable (fun t => (heAb t).trans (by
        have := (norm_nonneg _).trans (heRb t)
        have h1 : 0 ≤ (1 + |t|) ^ N := by positivity
        nlinarith))
      heRm.aestronglyMeasurable (fun t => (heRb t).trans (by
        have := (norm_nonneg _).trans (heAb t)
        have h1 : 0 ≤ (1 + |t|) ^ N := by positivity
        nlinarith))
      (measurableSet_Iio (a := (-1 : ℝ))) 1 (fun t _ => by simp [he]) hτ
    rw [hlin, one_mul, mul_add]
  -- the mean is nonzero
  have hc0 : c ≠ 0 := by
    intro hc0
    have hβ : betaG G ≠ 0 := by
      unfold betaG
      exact div_ne_zero (G_ne_zero hΦd hGd hG2 (by norm_num : (1 / 2 : ℝ) < (1 : ℂ).re))
        two_ne_zero
    have hrefl := tendsto_lower_reflected_radial hsl hΦre hid hGc hGd hG2 (m := 1) le_rfl
    -- `φ*` agrees with `e` below `−1`
    have hnear : Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace
        ((Icc (-1 : ℝ) 1).indicator ((Iio (0 : ℝ)).indicator (phiStar G)))
          ((ε : ℂ) + ((1 : ℕ) : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
      have hsm : AEStronglyMeasurable ((Iio (0 : ℝ)).indicator (phiStar G)) volume := by
        refine (Measurable.indicator ?_ measurableSet_Iio).aestronglyMeasurable
        have h1 := hφc.sub (continuous_gG (G := G) hGc)
        exact (h1.congr fun t => phiG_sub_gG G t).measurable
      have hpoly' : ∀ t, ‖(Iio (0 : ℝ)).indicator (phiStar G) t‖ ≤
          (CB + CB) * (1 + |t|) ^ N := by
        intro t
        refine (norm_indicator_le_norm_self _ t).trans ?_
        rw [← phiG_sub_gG]
        refine (norm_sub_le _ _).trans ?_
        have := (hpoly t).1; have := (hpoly t).2
        nlinarith
      exact tendsto_mul_defectLaplace_radial
        (hsm.indicator measurableSet_Icc)
        (fun t => (norm_indicator_le_norm_self _ t).trans (hpoly' t))
        (HamburgerTwisted.tendsto_mul_abelMass_indicator_Icc hsm hpoly' 1) 1
    -- split `1_{t<0} φ*` at `−1`
    have hsm : AEStronglyMeasurable ((Iio (0 : ℝ)).indicator (phiStar G)) volume := by
      refine (Measurable.indicator ?_ measurableSet_Iio).aestronglyMeasurable
      have h1 := hφc.sub (continuous_gG (G := G) hGc)
      exact (h1.congr fun t => phiG_sub_gG G t).measurable
    have hpoly' : ∀ t, ‖(Iio (0 : ℝ)).indicator (phiStar G) t‖ ≤ (CB + CB) * (1 + |t|) ^ N := by
      intro t
      refine (norm_indicator_le_norm_self _ t).trans ?_
      rw [← phiG_sub_gG]
      refine (norm_sub_le _ _).trans ?_
      have := (hpoly t).1; have := (hpoly t).2
      nlinarith
    set Ce : ℝ := (‖κ₀‖ * (2 * S) * CB) + (‖κ₀‖ * Cr * CB) with hCe
    have hCe0 : 0 ≤ Ce := by positivity
    have hpt : ∀ t, (Iio (0 : ℝ)).indicator (phiStar G) t =
        1 * (Iio (-1 : ℝ)).indicator e t +
          (Icc (-1 : ℝ) 1).indicator ((Iio (0 : ℝ)).indicator (phiStar G)) t := by
      intro t
      rcases lt_or_ge t (-1) with ht | ht
      · rw [Set.indicator_of_mem (show t ∈ Iio (0 : ℝ) by simp only [mem_Iio]; linarith),
          Set.indicator_of_mem (show t ∈ Iio (-1 : ℝ) from ht),
          Set.indicator_of_notMem (show t ∉ Icc (-1 : ℝ) 1 from fun h => by linarith [h.1]),
          one_mul, add_zero]
        unfold phiStar
        rw [hlock' t ht, hc0, zero_mul, zero_add, mul_div_cancel_left₀ _ (hD t)]
      · rw [Set.indicator_of_notMem (show t ∉ Iio (-1 : ℝ) from fun h => by
          simp only [mem_Iio] at h; linarith), mul_zero, zero_add]
        rcases le_or_gt t 1 with ht1 | ht1
        · rw [Set.indicator_of_mem (show t ∈ Icc (-1 : ℝ) 1 from ⟨ht, ht1⟩)]
        · rw [Set.indicator_of_notMem (show t ∉ Icc (-1 : ℝ) 1 from fun h => by linarith [h.2])]
          rw [Set.indicator_of_notMem (show t ∉ Iio (0 : ℝ) by
            simp only [mem_Iio, not_lt]; linarith)]
    have hsplitJ : ∀ ε : ℝ, 0 < ε → (ε : ℂ) * defectLaplace ((Iio (0 : ℝ)).indicator (phiStar G))
        ((ε : ℂ) + ((1 : ℕ) : ℂ) * I) = (ε : ℂ) * defectLaplace ((Iio (-1 : ℝ)).indicator e)
          ((ε : ℂ) + ((1 : ℕ) : ℂ) * I) + (ε : ℂ) * defectLaplace
            ((Icc (-1 : ℝ) 1).indicator ((Iio (0 : ℝ)).indicator (phiStar G)))
            ((ε : ℂ) + ((1 : ℕ) : ℂ) * I) := by
      intro ε hε
      have hτ : 0 < ((ε : ℂ) + ((1 : ℕ) : ℂ) * I).re := by simpa using hε
      have hlin := HamburgerTwisted.defectLaplace_indicator_eq
        (g := (Iio (0 : ℝ)).indicator (phiStar G)) (Φ := (Iio (-1 : ℝ)).indicator e)
        (r := (Icc (-1 : ℝ) 1).indicator ((Iio (0 : ℝ)).indicator (phiStar G)))
        (Cg := Ce + (CB + CB)) (N := N) (s := univ)
        (hem.indicator measurableSet_Iio).aestronglyMeasurable
        (fun t => ((norm_indicator_le_norm_self _ t).trans (heb t)).trans (by
          have h1 : 0 ≤ (1 + |t|) ^ N := by positivity
          nlinarith))
        (hsm.indicator measurableSet_Icc)
        (fun t => ((norm_indicator_le_norm_self _ t).trans (hpoly' t)).trans (by
          have h1 : 0 ≤ (1 + |t|) ^ N := by positivity
          nlinarith))
        MeasurableSet.univ 1 (fun t _ => hpt t) hτ
      simp only [Set.indicator_univ, one_mul] at hlin
      rw [hlin, mul_add]
    have hsum := (hrad 1).add hnear
    rw [add_zero] at hsum
    have hlim0 : Tendsto (fun ε : ℝ => (ε : ℂ) * defectLaplace ((Iio (0 : ℝ)).indicator
        (phiStar G)) ((ε : ℂ) + ((1 : ℕ) : ℂ) * I)) (𝓝[>] 0) (𝓝 0) := by
      refine hsum.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (hsplitJ ε hε).symm
    have hβπ := tendsto_nhds_unique hrefl hlim0
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_pos.ne'
    exact hβ ((div_eq_zero_iff.mp hβπ).resolve_right hpi)
  have hc' : (c⁻¹)⁻¹ = c := inv_inv c
  have hres' := phase_lock_rigidity_of_radial_defect hsl hΦd hΦre hid hGc hGd hG2 hem heb
    (by norm_num : (0 : ℝ) ≤ 1) (by simpa using hrad) (κ := c⁻¹) (inv_ne_zero hc0)
    (fun τ hτ => by rw [hc']; exact hlock' τ hτ)
  exact ⟨hc0, hres'⟩


/-- **Almost-periodic locks with a uniformly settling remainder.**  In the class of
`exists_setIntegral_exp_mul_le` (`|lam(n)| ≤ κ log n`, summable rest weight), the lock
`G(1 − s) = κ₀ (P(x) + r(x)) G(s)` with `P` non-resonant almost-periodic and
`|r(x)| ≤ C (log T)^{−κ²/4 − η}` on `(T, 2T]` forces `κ₀p₀ ≠ 0`, `lam = Λ` and RH. -/
theorem ap_uniformly_settled_lock_rigidity {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hA : Summable (restWeight lam)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {p : ℕ → ℂ} {ω : ℕ → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2))
    (hres : ∀ j, ω j ≠ 0 → ∀ m n : ℕ, 1 ≤ m → (n : ℝ) ≠ m * Real.exp (-(ω j / 2)))
    {r : ℝ → ℂ} (hrm : Measurable r) {Cr : ℝ} (hrb : ∀ x, ‖r x‖ ≤ Cr) {κ₀ : ℂ}
    (hlock : ∀ τ : ℝ, τ < -1 →
      G (1 - lineS τ) = κ₀ * (apFactor p ω (-τ) + r (-τ)) * G (lineS τ))
    {η Cm T₁ : ℝ} (hη : 0 < η)
    (hunif : ∀ T : ℝ, T₁ ≤ T → ∀ x ∈ Ioc T (2 * T),
      ‖r x‖ ≤ Cm * Real.log T ^ (-(κ ^ 2 / 4 + η))) :
    κ₀ * apMean p ω ≠ 0 ∧ (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧
      RiemannHypothesis :=
  ap_settled_lock_rigidity hW hGc hGd hG2 hp hres hrm hrb hlock
    (blockMeans_of_uniform hW hA hκ hlam hGc hGd hG2 hrm hrb hη hunif)

/-- The mean-square version: `∫_T^{2T} |r|² ≤ C T (log T)^{−κ² − η}` suffices. -/
theorem ap_meanSquare_settled_lock_rigidity {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hA : Summable (restWeight lam)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hlam : ∀ n : ℕ, 2 ≤ n → |lam n| ≤ κ * Real.log n) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {p : ℕ → ℂ} {ω : ℕ → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2))
    (hres : ∀ j, ω j ≠ 0 → ∀ m n : ℕ, 1 ≤ m → (n : ℝ) ≠ m * Real.exp (-(ω j / 2)))
    {r : ℝ → ℂ} (hrm : Measurable r) {Cr : ℝ} (hrb : ∀ x, ‖r x‖ ≤ Cr) {κ₀ : ℂ}
    (hlock : ∀ τ : ℝ, τ < -1 →
      G (1 - lineS τ) = κ₀ * (apFactor p ω (-τ) + r (-τ)) * G (lineS τ))
    {η Cm T₁ : ℝ} (hη : 0 < η)
    (hmean : ∀ T : ℝ, T₁ ≤ T → ∫ x in Ioc T (2 * T), ‖r x‖ ^ 2 ≤
      Cm * T * Real.log T ^ (-(κ ^ 2 + η))) :
    κ₀ * apMean p ω ≠ 0 ∧ (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧
      RiemannHypothesis :=
  ap_settled_lock_rigidity hW hGc hGd hG2 hp hres hrm hrb hlock
    (blockMeans_of_meanSquare hW hA hκ hlam hGc hGd hG2 hrm hrb hη hmean)


/-- **Every producer: almost-periodic locks with a power-small remainder.**  No class condition
on `lam`: `∫_T^{2T} |r| = O(T^{1−δ})` suffices (producer Lindelöf on the line). -/
theorem ap_power_settled_lock_rigidity {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {G : ℂ → ℂ}
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (weilContinuation hW s * G s) s)
    (hG2 : G 2 = bigG lam 2) {p : ℕ → ℂ} {ω : ℕ → ℝ}
    (hp : Summable fun j => ‖p j‖ * Real.exp (|ω j| / 2))
    (hres : ∀ j, ω j ≠ 0 → ∀ m n : ℕ, 1 ≤ m → (n : ℝ) ≠ m * Real.exp (-(ω j / 2)))
    {r : ℝ → ℂ} (hrm : Measurable r) {Cr : ℝ} (hrb : ∀ x, ‖r x‖ ≤ Cr) {κ₀ : ℂ}
    (hlock : ∀ τ : ℝ, τ < -1 →
      G (1 - lineS τ) = κ₀ * (apFactor p ω (-τ) + r (-τ)) * G (lineS τ))
    {δ Cm T₁ : ℝ} (hδ : 0 < δ)
    (hpow : ∀ T : ℝ, T₁ ≤ T → ∫ x in Ioc T (2 * T), ‖r x‖ ≤ Cm * T ^ (1 - δ)) :
    κ₀ * apMean p ω ≠ 0 ∧ (∀ n : ℕ, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n) ∧
      RiemannHypothesis :=
  ap_settled_lock_rigidity hW hGc hGd hG2 hp hres hrm hrb hlock
    (blockMeans_of_powerL1 hW hGc hGd hG2 hrm hrb hδ hpow)

end RHTower.WeilSpectral
