import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaClosedSource
import GaloisForLFunctions.RHTower.SuzukiCausalDepthGammaTwoLegSourceNormalGraphDomainNoGo

/-!
# The closed two-leg Gamma source genuinely leaves the bounded class

The first surviving Gamma coordinate has a nonsummable squared row after the
literal two-leg gain. Consequently no bounded operator can preserve all the
finite source columns. This separates the closed realization from the bounded
and trace-class constructions excluded earlier.
-/

open Filter Topology
open scoped BigOperators ENNReal InnerProduct
set_option autoImplicit false

noncomputable section

namespace RHTower

private theorem gamma_depth_zero_cayley (p : Nat.Primes) :
    Real.tanh (suzukiCausalDepthGammaFrequency (p, 0)) =
      ((p : ℝ) - 1) / ((p : ℝ) + 1) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have he : Real.exp (Real.log (p : ℝ) / 2) ≠ 0 := (Real.exp_pos _).ne'
  have he2 : Real.exp (Real.log (p : ℝ) / 2) *
      Real.exp (Real.log (p : ℝ) / 2) = p := by
    rw [← Real.exp_add, add_halves, Real.exp_log hp]
  simp only [suzukiCausalDepthGammaFrequency, xiGammaEulerValuationNat,
    zero_add, pow_one]
  rw [Real.tanh_eq, Real.exp_neg]
  field_simp
  nlinarith [he2]

private theorem gamma_depth_zero_exp_characteristic (p : Nat.Primes) :
    Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) *
      semilocalArchimedeanCharacteristic (suzukiCausalDepthGammaFrequency (p, 0)) ^ 2 =
      2 / ((p : ℝ) + 1) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have he : Real.exp (Real.log (p : ℝ) / 2) ≠ 0 := (Real.exp_pos _).ne'
  have he2 : Real.exp (Real.log (p : ℝ) / 2) *
      Real.exp (Real.log (p : ℝ) / 2) = p := by
    rw [← Real.exp_add, add_halves, Real.exp_log hp]
  simp only [suzukiCausalDepthGammaFrequency, xiGammaEulerValuationNat,
    zero_add, pow_one]
  rw [semilocalArchimedeanCharacteristic_sq, Real.cosh_eq,
    show -(1 / 2 : ℝ) * Real.log (p : ℝ) = -(Real.log (p : ℝ) / 2) by ring,
    Real.exp_neg]
  field_simp
  nlinarith [he2]

/-- The first surviving row retains prime-harmonic mass after cancellation-free recovery. -/
theorem suzukiGammaTwoLegColumn_first_norm_sq
    (h a : Set.Ioi (0 : ℝ)) (p : Nat.Primes) :
    ‖suzukiGammaTwoLegColumn h a (p, 0) (Sum.inr 0)‖ ^ 2 =
      (h.1 * Real.sqrt h.1)⁻¹ ^ 2 * Real.log (p : ℝ) *
        ((p : ℝ) / ((p : ℝ) + 1)) ^ 2 *
        (((p : ℝ) - 1) / ((p : ℝ) + 1)) ^ 2 *
        (1 - xiMobiusContinuousApertureDiskNode ((h.1 / 2) * a.1) p) ^ 4 /
        ((p : ℝ) + 1) := by
  have hc : semilocalArchimedeanJacobiNormalization 1 ^ 2 = (1 / 2 : ℝ) := by
    rw [semilocalArchimedeanJacobiNormalization_sq_eq_normalizedCentralBinom]
    norm_num [GaloisForLFunctions.HTGeometry.normalizedCentralBinom, Nat.centralBinom]
  rw [suzukiGammaTwoLegColumn_inr, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [suzukiCausalDepthGammaWeightedFeature, suzukiCausalDepthGammaFeature,
    suzukiCausalDepthGammaSurvivingDegree, gammaConductorJacobiFeature, pow_one]
  rw [show
    ((p : ℝ) * (suzukiCausalDepthGammaWeight h.1 a.1 (p, 0) *
      (semilocalArchimedeanJacobiNormalization 1 *
        semilocalArchimedeanCharacteristic (suzukiCausalDepthGammaFrequency (p, 0)) *
          Real.tanh (suzukiCausalDepthGammaFrequency (p, 0))))) ^ 2 =
      ((p : ℝ) * suzukiCausalDepthGammaWeight h.1 a.1 (p, 0)) ^ 2 *
        semilocalArchimedeanJacobiNormalization 1 ^ 2 *
        semilocalArchimedeanCharacteristic (suzukiCausalDepthGammaFrequency (p, 0)) ^ 2 *
        Real.tanh (suzukiCausalDepthGammaFrequency (p, 0)) ^ 2 by ring,
    sq_prime_mul_suzukiCausalDepthGammaWeight_zero_eq, hc]
  calc
    _ = ((p : ℝ) ^ 2 * Real.log (p : ℝ) *
        ((h.1 * Real.sqrt h.1)⁻¹) ^ 2 * (((p : ℝ) + 1)⁻¹) ^ 2 *
        (1 - xiMobiusContinuousApertureDiskNode ((h.1 / 2) * a.1) p) ^ 4) *
        (1 / 2) *
        (Real.exp (-(1 / 2 : ℝ) * Real.log (p : ℝ)) *
          semilocalArchimedeanCharacteristic (suzukiCausalDepthGammaFrequency (p, 0)) ^ 2) *
        Real.tanh (suzukiCausalDepthGammaFrequency (p, 0)) ^ 2 := by ring
    _ = _ := by
      rw [gamma_depth_zero_exp_characteristic, gamma_depth_zero_cayley]
      ring

theorem not_summable_suzukiGammaTwoLegColumn_first_norm_sq
    (h a : Set.Ioi (0 : ℝ)) :
    ¬ Summable (fun p : Nat.Primes =>
      ‖suzukiGammaTwoLegColumn h a (p, 0) (Sum.inr 0)‖ ^ 2) := by
  have hh : 0 < h.1 := h.2
  have ha : 0 < a.1 := a.2
  let C : ℝ := (h.1 * Real.sqrt h.1)⁻¹ ^ 2 * Real.log 2 / 1152
  have hC : 0 < C := by dsimp [C]; positivity
  have hscale : 0 < (h.1 / 2) * a.1 := by positivity
  have hdisk : Tendsto
      (fun p : Nat.Primes => xiMobiusContinuousApertureDiskNode ((h.1 / 2) * a.1) p)
      cofinite (𝓝 0) := by
    have ht := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
      (Filter.Tendsto.const_mul_atTop hscale
        GaloisForLFunctions.HTGeometry.tendsto_primeRealLog_cofinite_atTop))
    refine ht.congr fun p => ?_
    change Real.exp (-(((h.1 / 2) * a.1) * Real.log (p : ℝ))) =
      Real.exp (-((h.1 / 2) * a.1) * Real.log (p : ℝ))
    rw [neg_mul]
  have hsmall : ∀ᶠ p : Nat.Primes in cofinite,
      xiMobiusContinuousApertureDiskNode ((h.1 / 2) * a.1) p < 1 / 2 :=
    hdisk.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hlower : ∀ᶠ p : Nat.Primes in cofinite,
      C * (1 / (p : ℝ)) ≤
        ‖suzukiGammaTwoLegColumn h a (p, 0) (Sum.inr 0)‖ ^ 2 := by
    filter_upwards [hsmall] with p hd
    have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast p.property.two_le
    have hden : (0 : ℝ) < (p : ℝ) + 1 := by positivity
    have hr : (1 / 2 : ℝ) ≤ (p : ℝ) / ((p : ℝ) + 1) := by
      rw [le_div_iff₀ hden]; linarith
    have hs : (1 / 3 : ℝ) ≤ ((p : ℝ) - 1) / ((p : ℝ) + 1) := by
      rw [le_div_iff₀ hden]; linarith
    have ht : (1 / 2 : ℝ) ≤ 1 - xiMobiusContinuousApertureDiskNode ((h.1 / 2) * a.1) p := by
      linarith
    have hlog : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.strictMonoOn_log.monotoneOn (by norm_num) hp hp2
    have hr3 : (1 / 8 : ℝ) ≤ ((p : ℝ) / ((p : ℝ) + 1)) ^ 3 := by
      calc (1 / 8 : ℝ) = (1 / 2 : ℝ) ^ 3 := by norm_num
           _ ≤ _ := by gcongr
    have hs2 : (1 / 9 : ℝ) ≤ (((p : ℝ) - 1) / ((p : ℝ) + 1)) ^ 2 := by
      calc (1 / 9 : ℝ) = (1 / 3 : ℝ) ^ 2 := by norm_num
           _ ≤ _ := by gcongr
    have ht4 : (1 / 16 : ℝ) ≤
        (1 - xiMobiusContinuousApertureDiskNode ((h.1 / 2) * a.1) p) ^ 4 := by
      calc (1 / 16 : ℝ) = (1 / 2 : ℝ) ^ 4 := by norm_num
           _ ≤ _ := by gcongr
    rw [suzukiGammaTwoLegColumn_first_norm_sq]
    have hmain : C ≤
        (h.1 * Real.sqrt h.1)⁻¹ ^ 2 * Real.log (p : ℝ) *
          ((p : ℝ) / ((p : ℝ) + 1)) ^ 3 *
          (((p : ℝ) - 1) / ((p : ℝ) + 1)) ^ 2 *
          (1 - xiMobiusContinuousApertureDiskNode ((h.1 / 2) * a.1) p) ^ 4 := by
      calc C = (h.1 * Real.sqrt h.1)⁻¹ ^ 2 * Real.log 2 *
          (1 / 8) * (1 / 9) * (1 / 16) := by dsimp [C]; ring
           _ ≤ _ := by gcongr
    apply (mul_le_mul_iff_of_pos_right hp).mp
    convert hmain using 1
    · field_simp
    · ring
  intro hsum
  have hs : Summable (fun p : Nat.Primes => C * (1 / (p : ℝ))) :=
    Summable.of_norm_bounded_eventually hsum (by
      filter_upwards [hlower] with p hp
      simpa [Real.norm_eq_abs, abs_of_pos hC] using hp)
  exact Nat.Primes.not_summable_one_div ((summable_mul_left_iff hC.ne').mp hs)

/-- No bounded operator can reproduce even the depth-zero literal source columns. -/
theorem no_bounded_suzukiGammaTwoLeg_column_realization
    (h a : Set.Ioi (0 : ℝ)) :
    ¬ ∃ T : SuzukiCausalDepthGammaTraceL2 →L[ℂ] SuzukiCausalDepthGammaTraceL2,
      ∀ p : Nat.Primes,
        T (lp.single 2 (Sum.inl (p, 0)) (1 : ℂ)) = suzukiGammaTwoLegColumn h a (p, 0) := by
  rintro ⟨T, hT⟩
  let v := T.adjoint (lp.single 2 (Sum.inr 0) (1 : ℂ))
  have hs := HilbertSchmidt.summable_coe_sq v
  have hi : Function.Injective (fun p : Nat.Primes =>
      (Sum.inl (p, 0) : SuzukiCausalDepthGammaTraceIndex)) := by
    intro p q hpq
    exact congrArg Prod.fst (Sum.inl.inj hpq)
  have hrow (p : Nat.Primes) :
      ‖v (Sum.inl (p, 0))‖ =
        ‖suzukiGammaTwoLegColumn h a (p, 0) (Sum.inr 0)‖ := by
    have hid := ContinuousLinearMap.adjoint_inner_left T
      (lp.single 2 (Sum.inl (p, 0)) (1 : ℂ))
      (lp.single 2 (Sum.inr 0) (1 : ℂ))
    rw [hT p, lp.inner_single_right, lp.inner_single_left] at hid
    have hn := congrArg norm hid
    simpa [v, RCLike.inner_apply] using hn
  apply not_summable_suzukiGammaTwoLegColumn_first_norm_sq h a
  exact (hs.comp_injective hi).congr fun p => by rw [hrow]

/-- The actual closed synthesis has no bounded extension to its ambient Hilbert space. -/
theorem suzukiGammaTwoLegClosedSynthesis_no_bounded_extension
    (h a : Set.Ioi (0 : ℝ)) :
    ¬ ∃ T : SuzukiCausalDepthGammaTraceL2 →L[ℂ] SuzukiCausalDepthGammaTraceL2,
      ∀ x : (suzukiGammaTwoLegClosedSynthesis h a).domain,
        T x = suzukiGammaTwoLegClosedSynthesis h a x := by
  rintro ⟨T, hT⟩
  apply no_bounded_suzukiGammaTwoLeg_column_realization h a
  refine ⟨T, fun p => ?_⟩
  rcases (LinearPMap.mem_graph_iff _).mp
      (suzukiGammaTwoLegClosedSynthesis_single_graph h a (Sum.inl (p, 0))) with
    ⟨x, hx, hy⟩
  rw [← hx, hT x]
  exact hy

/-- The literal inverse-Wold two-leg source weight is recovered, without changing its tail. -/
theorem suzukiGammaTwoLegColumn_sourceNormal_coordinate
    (h a : Set.Ioi (0 : ℝ)) (pe : Nat.Primes × ℕ) (k : ℕ) :
    suzukiGammaTwoLegColumn h a pe (Sum.inr k) =
      (suzukiCausalDepthGammaTwoLegSourceNormalWeight h.1 a.1 pe *
        suzukiCausalDepthGammaFeature k (suzukiCausalDepthGammaFrequency pe) : ℝ) := by
  rw [suzukiGammaTwoLegColumn_inr, suzukiCausalDepthGammaTwoLegSourceNormalWeight_eq]
  simp only [suzukiCausalDepthGammaWeightedFeature, mul_assoc]

/-- A fixed, unconditional closed realization of the canonical two-leg Gamma source.
Its finite packets are literal, its domain is dense, and bounded realization is impossible. -/
theorem suzukiGammaCanonicalTwoLegSource_closed_dense_unbounded :
    let h : Set.Ioi (0 : ℝ) := ⟨1, by norm_num⟩
    (suzukiGammaTwoLegClosedSynthesis h h).IsClosed ∧
      Dense ((suzukiGammaTwoLegClosedSynthesis h h).domain : Set SuzukiCausalDepthGammaTraceL2) ∧
      (∀ s : Finset (Nat.Primes × ℕ), ∀ c : (Nat.Primes × ℕ) → ℂ,
        ((∑ pe ∈ s, c pe • lp.single 2 (Sum.inl pe) (1 : ℂ)),
          ∑ pe ∈ s, c pe • suzukiGammaTwoLegColumn h h pe) ∈
            (suzukiGammaTwoLegClosedSynthesis h h).graph) ∧
      ¬ ∃ T : SuzukiCausalDepthGammaTraceL2 →L[ℂ] SuzukiCausalDepthGammaTraceL2,
        ∀ x : (suzukiGammaTwoLegClosedSynthesis h h).domain,
          T x = suzukiGammaTwoLegClosedSynthesis h h x := by
  dsimp only
  exact ⟨suzukiGammaTwoLegClosedSynthesis_isClosed _ _,
    suzukiGammaTwoLegClosedSynthesis_dense_domain _ _,
    suzukiGammaTwoLegClosedSynthesis_finite_packet _ _,
    suzukiGammaTwoLegClosedSynthesis_no_bounded_extension _ _⟩

end RHTower
