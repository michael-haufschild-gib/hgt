import GaloisForLFunctions.RHTower.GammaTestPairingMajorant

/-!
# The Gamma jump transposes to the reflected shift

`R_σ` is translation invariant and built from a symmetric second difference, so moving each
translate onto the other factor exchanges the two exponential weights — which is exactly the
reflection `σ ↦ −σ`:

`∫ (R_σ U)φ = ∫ U (R_{−σ}φ)`.

Two interchanges are needed, dominated differently.  In the first the base-point integral is against
the test function, so the corpus majorant applies as a *product*.  In the second the test function
sits inside the difference, and the scale majorant of `GammaTestPairingMajorant` is what dominates.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The reflected shift is the shift of the reflected profile. -/
theorem shiftedSecondDifference_neg (σ : ℝ) (φ : ℝ → ℝ) (L s : ℝ) :
    shiftedSecondDifference (-σ) φ L s
      = shiftedSecondDifference σ (fun x => φ (-x)) (-L) s := by
  rw [shiftedSecondDifference, shiftedSecondDifference]
  have h1 : -(-L) = L := by ring
  have h2 : -(-L + s) = L - s := by ring
  have h3 : -(-L - s) = L + s := by ring
  rw [h1, h2, h3, neg_mul, neg_neg]
  ring

theorem integral_abs_shiftedSecondDifference_neg_mul_kernel_le {φ : ℝ → ℝ} {K B N R σ : ℝ}
    (hφc : Continuous φ)
    (hφK : ∀ x y : ℝ, |φ x - φ y| ≤ K * |x - y|) (hφB : ∀ x, |φ x| ≤ B)
    (hsupp : ∀ x : ℝ, R < |x| → φ x = 0) (hR : 0 ≤ R)
    (hφint : Integrable φ) (hN : (∫ x, |φ x|) = N)
    (hσ0 : 0 ≤ σ) {s : ℝ} (hs : 0 < s) :
    (∫ L, |shiftedSecondDifference (-σ) φ L s| * gammaTransportKernel s)
      ≤ gammaTransposeMajorant K B N R σ s := by
  have hrefl : (∫ L, |shiftedSecondDifference (-σ) φ L s| * gammaTransportKernel s)
      = ∫ L, |shiftedSecondDifference σ (fun x => φ (-x)) L s| * gammaTransportKernel s := by
    have h1 : ∀ L : ℝ, |shiftedSecondDifference (-σ) φ L s| * gammaTransportKernel s
        = (fun M : ℝ => |shiftedSecondDifference σ (fun x => φ (-x)) M s|
            * gammaTransportKernel s) (-L) := by
      intro L
      rw [shiftedSecondDifference_neg]
    rw [integral_congr_ae (Filter.Eventually.of_forall h1)]
    exact integral_neg_eq_self
      (fun M : ℝ => |shiftedSecondDifference σ (fun x => φ (-x)) M s|
        * gammaTransportKernel s) volume
  rw [hrefl]
  refine integral_abs_shiftedSecondDifference_mul_kernel_le (φ := fun x => φ (-x))
    (hφc.comp continuous_neg) (fun x y => ?_) (fun x => hφB _) (fun x hx => ?_) hR
    (hφint.comp_neg) ?_ hσ0 hs
  · have := hφK (-x) (-y)
    calc |φ (-x) - φ (-y)| ≤ K * |(-x) - (-y)| := this
      _ = K * |x - y| := by rw [show (-x) - (-y) = -(x - y) by ring, abs_neg]
  · exact hsupp (-x) (by rwa [abs_neg])
  · rw [← hN]
    exact integral_neg_eq_self (fun x => |φ x|) volume


/-- Integrability of the pairing integrand with the test function outside the difference. -/
theorem integrable_uncurry_jump_test {U φ : ℝ → ℝ} {KU BU σ : ℝ}
    (hUm : Measurable U) (hUK : ∀ x y : ℝ, |U x - U y| ≤ KU * |x - y|) (hUB : ∀ x, |U x| ≤ BU)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (hφm : Measurable φ) (hφint : Integrable φ) :
    Integrable
      (Function.uncurry fun L s => shiftedSecondDifference σ U L s * gammaTransportKernel s * φ L)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmajInt : IntegrableOn (gammaPairingMajorant KU BU σ) (Ioi 0) :=
    integrableOn_gammaPairingMajorant hσ1
  have hdom : Integrable
      (fun z : ℝ × ℝ => |φ z.1| * gammaPairingMajorant KU BU σ z.2)
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    Integrable.mul_prod hφint.abs hmajInt
  have hD : Measurable (Function.uncurry fun L s : ℝ => shiftedSecondDifference σ U L s) := by
    unfold shiftedSecondDifference
    fun_prop
  have hmeas2 : Measurable
      (Function.uncurry fun L s => shiftedSecondDifference σ U L s
        * gammaTransportKernel s * φ L) :=
    (hD.mul (measurable_gammaTransportKernel.comp measurable_snd)).mul (hφm.comp measurable_fst)
  refine Integrable.mono' hdom hmeas2.aestronglyMeasurable ?_
  filter_upwards [ae_snd_pos_prod_restrict] with z hz
  have hbound := abs_shiftedSecondDifference_mul_kernel_le hUK hUB hσ0 hz z.1
  show ‖shiftedSecondDifference σ U z.1 z.2 * gammaTransportKernel z.2 * φ z.1‖
      ≤ |φ z.1| * gammaPairingMajorant KU BU σ z.2
  rw [Real.norm_eq_abs, abs_mul]
  calc |shiftedSecondDifference σ U z.1 z.2 * gammaTransportKernel z.2| * |φ z.1|
      ≤ gammaPairingMajorant KU BU σ z.2 * |φ z.1| :=
        mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
    _ = |φ z.1| * gammaPairingMajorant KU BU σ z.2 := by ring

/-- Integrability of the transposed pairing integrand. -/
theorem integrable_uncurry_test_jump {U φ : ℝ → ℝ} {K B N R BU σ : ℝ}
    (hUm : Measurable U) (hUB : ∀ x, |U x| ≤ BU)
    (hφc : Continuous φ) (hφm : Measurable φ)
    (hφK : ∀ x y : ℝ, |φ x - φ y| ≤ K * |x - y|) (hφB : ∀ x, |φ x| ≤ B)
    (hsupp : ∀ x : ℝ, R < |x| → φ x = 0) (hR : 0 ≤ R)
    (hφint : Integrable φ) (hN : (∫ x, |φ x|) = N)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    Integrable
      (Function.uncurry fun L s =>
        U L * (shiftedSecondDifference (-σ) φ L s * gammaTransportKernel s))
      ((volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hBU : 0 ≤ BU := le_trans (abs_nonneg _) (hUB 0)
  have hD : Measurable (Function.uncurry fun L s : ℝ => shiftedSecondDifference (-σ) φ L s) := by
    unfold shiftedSecondDifference
    fun_prop
  have hmeas : Measurable (Function.uncurry fun L s =>
      U L * (shiftedSecondDifference (-σ) φ L s * gammaTransportKernel s)) :=
    (hUm.comp measurable_fst).mul
      (hD.mul (measurable_gammaTransportKernel.comp measurable_snd))
  -- for each scale, the base-point slice is integrable
  have hslice : ∀ s : ℝ, 0 < s → Integrable
      (fun L => U L * (shiftedSecondDifference (-σ) φ L s * gammaTransportKernel s)) := by
    intro s hs
    have hcont : Continuous fun L : ℝ => shiftedSecondDifference (-σ) φ L s := by
      have : Continuous fun L : ℝ => 2 * φ L - Real.exp (-(-σ * s)) * φ (L + s)
          - Real.exp (-σ * s) * φ (L - s) :=
        ((continuous_const.mul hφc).sub
          (continuous_const.mul (hφc.comp (continuous_id.add continuous_const)))).sub
          (continuous_const.mul (hφc.comp (continuous_id.sub continuous_const)))
      exact this
    have hcs : HasCompactSupport fun L : ℝ => shiftedSecondDifference (-σ) φ L s := by
      refine HasCompactSupport.intro (isCompact_Icc (a := -(R + s)) (b := R + s)) fun L hL => ?_
      refine shiftedSecondDifference_eq_zero_of_support hsupp (-σ) hs.le ?_
      rw [mem_Icc, not_and_or] at hL
      rcases hL with h | h
      · rw [not_le] at h
        rw [abs_of_neg (by linarith : L < 0)]
        linarith
      · rw [not_le] at h
        rw [abs_of_pos (by linarith : 0 < L)]
        linarith
    have hg : Integrable
        (fun L => shiftedSecondDifference (-σ) φ L s * gammaTransportKernel s) :=
      ((hcont.integrable_of_hasCompactSupport hcs)).mul_const _
    refine hg.bdd_mul (c := BU) hUm.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hUB x
  refine (integrable_prod_iff' hmeas.aestronglyMeasurable).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact hslice s hs
  · have hmm : AEStronglyMeasurable
        (fun s : ℝ => ∫ L : ℝ, ‖Function.uncurry (fun L s =>
          U L * (shiftedSecondDifference (-σ) φ L s * gammaTransportKernel s)) (L, s)‖)
        (volume.restrict (Ioi (0 : ℝ))) :=
      (hmeas.aestronglyMeasurable.prod_swap.norm).integral_prod_right'
    refine Integrable.mono' ((integrableOn_gammaTransposeMajorant (K := K) (B := B) (N := N)
      (R := R) hσ1).const_mul BU) hmm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hspos : (0 : ℝ) < s := hs
    have hkpos : 0 < gammaTransportKernel s := gammaTransportKernel_pos hspos
    have hptw : ∀ L : ℝ, ‖U L * (shiftedSecondDifference (-σ) φ L s * gammaTransportKernel s)‖
        ≤ BU * (|shiftedSecondDifference (-σ) φ L s| * gammaTransportKernel s) := by
      intro L
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hkpos]
      exact mul_le_mul_of_nonneg_right (hUB L) (by positivity)
    have hint1 : Integrable
        (fun L => BU * (|shiftedSecondDifference (-σ) φ L s| * gammaTransportKernel s)) := by
      have hcont : Continuous fun L : ℝ => shiftedSecondDifference (-σ) φ L s := by
        have : Continuous fun L : ℝ => 2 * φ L - Real.exp (-(-σ * s)) * φ (L + s)
            - Real.exp (-σ * s) * φ (L - s) :=
          ((continuous_const.mul hφc).sub
            (continuous_const.mul (hφc.comp (continuous_id.add continuous_const)))).sub
            (continuous_const.mul (hφc.comp (continuous_id.sub continuous_const)))
        exact this
      have hcs : HasCompactSupport fun L : ℝ => |shiftedSecondDifference (-σ) φ L s| := by
        refine HasCompactSupport.intro (isCompact_Icc (a := -(R + s)) (b := R + s)) fun L hL => ?_
        refine abs_eq_zero.mpr (shiftedSecondDifference_eq_zero_of_support hsupp (-σ) hs.le ?_)
        rw [mem_Icc, not_and_or] at hL
        rcases hL with h | h
        · rw [not_le] at h
          rw [abs_of_neg (by linarith : L < 0)]
          linarith
        · rw [not_le] at h
          rw [abs_of_pos (by linarith : 0 < L)]
          linarith
      exact (((hcont.abs).integrable_of_hasCompactSupport hcs).mul_const _).const_mul _
    have hle := MeasureTheory.integral_mono ((hslice s hspos).norm) hint1 hptw
    rw [integral_const_mul] at hle
    have hmaj := integral_abs_shiftedSecondDifference_neg_mul_kernel_le hφc hφK hφB hsupp hR
      hφint hN hσ0 hspos
    have hBU' : (0 : ℝ) ≤ BU := hBU
    have hchain : (∫ L : ℝ, ‖U L * (shiftedSecondDifference (-σ) φ L s
        * gammaTransportKernel s)‖) ≤ BU * gammaTransposeMajorant K B N R σ s :=
      le_trans hle (mul_le_mul_of_nonneg_left hmaj hBU')
    have hnn : (0 : ℝ) ≤ ∫ L : ℝ, ‖U L * (shiftedSecondDifference (-σ) φ L s
        * gammaTransportKernel s)‖ := integral_nonneg fun L => norm_nonneg _
    simp only [Function.uncurry]
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact hchain


/-- **The second difference transposes onto the test function.** -/
theorem integral_shiftedSecondDifference_mul_test {U φ : ℝ → ℝ} {BU : ℝ}
    (hUm : Measurable U) (hUB : ∀ x, |U x| ≤ BU)
    (hφint : Integrable φ) (σ s : ℝ) :
    (∫ L, shiftedSecondDifference σ U L s * φ L)
      = ∫ L, U L * shiftedSecondDifference (-σ) φ L s := by
  have hbd : ∀ f : ℝ → ℝ, Measurable f → (∀ x, |f x| ≤ BU) → ∀ g : ℝ → ℝ, Integrable g →
      Integrable (fun L => f L * g L) := by
    intro f hf hfb g hg
    refine hg.bdd_mul (c := BU) hf.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hfb x
  have hUs : Measurable fun L : ℝ => U (L + s) := hUm.comp (measurable_id.add_const s)
  have hUs' : Measurable fun L : ℝ => U (L - s) := hUm.comp (measurable_id.sub_const s)
  have h0 : Integrable fun L => U L * φ L := hbd U hUm hUB φ hφint
  have h1 : Integrable fun L => U (L + s) * φ L :=
    hbd _ hUs (fun x => hUB _) φ hφint
  have h2 : Integrable fun L => U (L - s) * φ L :=
    hbd _ hUs' (fun x => hUB _) φ hφint
  have h3 : Integrable fun L => U L * φ (L + s) :=
    hbd U hUm hUB _ (hφint.comp_add_right s)
  have h4 : Integrable fun L => U L * φ (L - s) :=
    hbd U hUm hUB _ (hφint.comp_sub_right s)
  have htr1 : (∫ L, U (L + s) * φ L) = ∫ L, U L * φ (L - s) := by
    have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun M : ℝ => U M * φ (M - s)) s
    simpa using h
  have htr2 : (∫ L, U (L - s) * φ L) = ∫ L, U L * φ (L + s) := by
    have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (fun M : ℝ => U M * φ (M + s)) s
    simpa using h
  have hLHS : (∫ L, shiftedSecondDifference σ U L s * φ L)
      = 2 * (∫ L, U L * φ L) - Real.exp (-(σ * s)) * (∫ L, U (L + s) * φ L)
        - Real.exp (σ * s) * ∫ L, U (L - s) * φ L := by
    have hfun : ∀ L : ℝ, shiftedSecondDifference σ U L s * φ L
        = 2 * (U L * φ L) - Real.exp (-(σ * s)) * (U (L + s) * φ L)
          - Real.exp (σ * s) * (U (L - s) * φ L) := by
      intro L
      rw [shiftedSecondDifference]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hfun)]
    have hA : (∫ L, (2 * (U L * φ L) - Real.exp (-(σ * s)) * (U (L + s) * φ L))
        - Real.exp (σ * s) * (U (L - s) * φ L))
        = (∫ L, 2 * (U L * φ L) - Real.exp (-(σ * s)) * (U (L + s) * φ L))
          - ∫ L, Real.exp (σ * s) * (U (L - s) * φ L) :=
      integral_sub ((h0.const_mul 2).sub (h1.const_mul _)) (h2.const_mul _)
    have hB : (∫ L, 2 * (U L * φ L) - Real.exp (-(σ * s)) * (U (L + s) * φ L))
        = (∫ L, 2 * (U L * φ L)) - ∫ L, Real.exp (-(σ * s)) * (U (L + s) * φ L) :=
      integral_sub (h0.const_mul 2) (h1.const_mul _)
    rw [hA, hB, integral_const_mul, integral_const_mul, integral_const_mul]
  have hRHS : (∫ L, U L * shiftedSecondDifference (-σ) φ L s)
      = 2 * (∫ L, U L * φ L) - Real.exp (σ * s) * (∫ L, U L * φ (L + s))
        - Real.exp (-(σ * s)) * ∫ L, U L * φ (L - s) := by
    have hfun : ∀ L : ℝ, U L * shiftedSecondDifference (-σ) φ L s
        = 2 * (U L * φ L) - Real.exp (σ * s) * (U L * φ (L + s))
          - Real.exp (-(σ * s)) * (U L * φ (L - s)) := by
      intro L
      rw [shiftedSecondDifference, neg_mul, neg_neg]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hfun)]
    have hA : (∫ L, (2 * (U L * φ L) - Real.exp (σ * s) * (U L * φ (L + s)))
        - Real.exp (-(σ * s)) * (U L * φ (L - s)))
        = (∫ L, 2 * (U L * φ L) - Real.exp (σ * s) * (U L * φ (L + s)))
          - ∫ L, Real.exp (-(σ * s)) * (U L * φ (L - s)) :=
      integral_sub ((h0.const_mul 2).sub (h3.const_mul _)) (h4.const_mul _)
    have hB : (∫ L, 2 * (U L * φ L) - Real.exp (σ * s) * (U L * φ (L + s)))
        = (∫ L, 2 * (U L * φ L)) - ∫ L, Real.exp (σ * s) * (U L * φ (L + s)) :=
      integral_sub (h0.const_mul 2) (h3.const_mul _)
    rw [hA, hB, integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hLHS, hRHS, htr1, htr2]
  ring


set_option maxHeartbeats 1000000 in
/-- **The Gamma jump transposes to the reflected shift.** -/
theorem integral_shiftedGammaJump_mul_test {U φ : ℝ → ℝ} {KU BU K B N R σ : ℝ}
    (hUm : Measurable U) (hUK : ∀ x y : ℝ, |U x - U y| ≤ KU * |x - y|) (hUB : ∀ x, |U x| ≤ BU)
    (hφc : Continuous φ) (hφm : Measurable φ)
    (hφK : ∀ x y : ℝ, |φ x - φ y| ≤ K * |x - y|) (hφB : ∀ x, |φ x| ≤ B)
    (hsupp : ∀ x : ℝ, R < |x| → φ x = 0) (hR : 0 ≤ R)
    (hφint : Integrable φ) (hN : (∫ x, |φ x|) = N)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    (∫ L, shiftedGammaJump σ U L * φ L) = ∫ L, U L * shiftedGammaJump (-σ) φ L := by
  have hL : (∫ L, shiftedGammaJump σ U L * φ L)
      = ∫ L, ∫ s in Ioi (0 : ℝ),
          shiftedSecondDifference σ U L s * gammaTransportKernel s * φ L := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun L => ?_)
    show (∫ s in Ioi (0 : ℝ), shiftedSecondDifference σ U L s * gammaTransportKernel s) * φ L
      = ∫ s in Ioi (0 : ℝ), shiftedSecondDifference σ U L s * gammaTransportKernel s * φ L
    exact (integral_mul_const _ _).symm
  have hswap1 := integral_integral_swap
    (integrable_uncurry_jump_test hUm hUK hUB hσ0 hσ1 hφm hφint)
  have hinner : ∀ s : ℝ,
      (∫ L, shiftedSecondDifference σ U L s * gammaTransportKernel s * φ L)
        = ∫ L, U L * (shiftedSecondDifference (-σ) φ L s * gammaTransportKernel s) := by
    intro s
    have h1 : ∀ L : ℝ, shiftedSecondDifference σ U L s * gammaTransportKernel s * φ L
        = (shiftedSecondDifference σ U L s * φ L) * gammaTransportKernel s := fun L => by ring
    have h2 : ∀ L : ℝ, U L * (shiftedSecondDifference (-σ) φ L s * gammaTransportKernel s)
        = (U L * shiftedSecondDifference (-σ) φ L s) * gammaTransportKernel s := fun L => by ring
    rw [integral_congr_ae (Filter.Eventually.of_forall h1),
      integral_congr_ae (Filter.Eventually.of_forall h2), integral_mul_const, integral_mul_const,
      integral_shiftedSecondDifference_mul_test hUm hUB hφint σ s]
  have hswap2 := integral_integral_swap
    (integrable_uncurry_test_jump (K := K) (B := B) (N := N) (R := R)
      hUm hUB hφc hφm hφK hφB hsupp hR hφint hN hσ0 hσ1)
  rw [hL, hswap1, integral_congr_ae (Filter.Eventually.of_forall hinner), ← hswap2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun L => ?_)
  show (∫ s in Ioi (0 : ℝ), U L * (shiftedSecondDifference (-σ) φ L s * gammaTransportKernel s))
    = U L * ∫ s in Ioi (0 : ℝ), shiftedSecondDifference (-σ) φ L s * gammaTransportKernel s
  exact integral_const_mul _ _

end GaloisForLFunctions.RHTower
