import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberFiniteCoreCurrentBridge

/-!
# Global completion-scaled finite-core product-fibre bridge

The real value correlations left by the completion monomial are absolutely summable.  After the
exact product-fibre regrouping, their full sum is the norm-square of the complete canonical
finite-core value packet.  Thus completion creates one radial current term and no new arithmetic
seam.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- The complex full-density moment is the sum of the complexified square-index atom moments. -/
theorem integral_thetaCuspTailSecondDensity_mul_complexPower_eq_tsum_atomMoment
    (m : ℕ) :
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) * (x : ℂ) ^ m) =
      ∑' n : ℕ, (thetaCuspTailSecondDensityAtomMoment (n + 1) m : ℂ) := by
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) * (x : ℂ) ^ m) =
      fun x : ℝ => ((x ^ m * thetaCuspTailSecondDensity x : ℝ) : ℂ) by
    funext x
    push_cast
    ring]
  rw [← Complex.ofReal_tsum,
    ← integral_pow_mul_thetaCuspTailSecondDensity_eq_tsum_atomMoment]
  exact integral_ofReal
    (X := ℝ) (μ := volume.restrict (Ioi 0)) (𝕜 := ℂ)

/-- The sum of all finite-core atom value packets is the full canonical core integral. -/
theorem tsum_thetaCuspTailSecondDensityAtomCoreValueMomentPacket_eq_integral
    (d : ℕ) (z : ℂ) :
    (∑' n : ℕ, thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z n) =
      ∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondCoreAtom d z x := by
  let A : ℂ := z ^ (2 : ℕ) + 1 / 4
  let c : ℕ → ℂ := thetaCuspTailSecondSectionSourceCoefficient z
  let M : ℕ → ℕ → ℂ := fun r n =>
    (thetaCuspTailSecondDensityAtomMoment (n + 1) (2 * r + 2) : ℂ)
  have hM (r : ℕ) : Summable (M r) := by
    exact (summable_thetaCuspTailSecondDensityAtomMoment (2 * r + 2)).map
      Complex.ofRealCLM Complex.ofRealCLM.continuous
  have hrow : Summable (fun n : ℕ =>
      ∑ r ∈ Finset.range (d + 1), c r * M r n) := by
    exact summable_sum fun r _hr => (hM r).mul_left (c r)
  have hrowTsum :
      (∑' n : ℕ, ∑ r ∈ Finset.range (d + 1), c r * M r n) =
        ∑ r ∈ Finset.range (d + 1),
          c r * (∑' n : ℕ, M r n) := by
    have hsum : HasSum
        (∑ r ∈ Finset.range (d + 1), fun n : ℕ => c r * M r n)
        (∑ r ∈ Finset.range (d + 1), c r * (∑' n : ℕ, M r n)) := by
      simpa only [Finset.sum_fn] using
        hasSum_sum
          (s := Finset.range (d + 1))
          (f := fun r n => c r * M r n)
          (a := fun r => c r * (∑' n : ℕ, M r n))
          (fun r _hr => by
            simpa only [tsum_mul_left] using ((hM r).mul_left (c r)).hasSum)
    simpa only [Finset.sum_fn] using hsum.tsum_eq
  have hmass : Summable (fun n : ℕ =>
      (thetaCuspTailSecondDensityAtomMoment (n + 1) 0 : ℂ)) :=
    (summable_thetaCuspTailSecondDensityAtomMoment 0).map
      Complex.ofRealCLM Complex.ofRealCLM.continuous
  have hpacket :
      (fun n : ℕ => thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z n) =
        fun n : ℕ =>
          (thetaCuspTailSecondDensityAtomMoment (n + 1) 0 : ℂ) -
            A * (∑ r ∈ Finset.range (d + 1), c r * M r n) := by
    funext n
    rfl
  rw [hpacket, hmass.tsum_sub (hrow.mul_left A), tsum_mul_left, hrowTsum]
  rw [← integral_thetaCuspTailSecondDensity_mul_complexPower_eq_tsum_atomMoment 0]
  simp only [M]
  simp_rw [← integral_thetaCuspTailSecondDensity_mul_complexPower_eq_tsum_atomMoment]
  have hmassInt := integrableOn_thetaCuspTailSecondDensity_complex
  have hsectionInt := integrableOn_thetaCuspTailSecondDensity_mul_section d z
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensity x : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) =
      fun x : ℝ => (thetaCuspTailSecondDensity x : ℂ) -
        A * ((thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondSection d z x) by
    funext x
    unfold thetaCuspTailSecondCoreAtom
    dsimp [A]
    ring,
    integral_sub hmassInt (hsectionInt.const_mul A), integral_const_mul]
  congr 1
  · simp
  · congr 1
    change (∑ r ∈ Finset.range (d + 1), c r *
        ∫ x : ℝ in Ioi 0,
          (thetaCuspTailSecondDensity x : ℂ) * (x : ℂ) ^ (2 * r + 2)) =
      ∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensity x : ℂ) *
          thetaCuspTailSecondSection d z x
    simp_rw [thetaCuspTailSecondSection_eq_sourcePowerPacket]
    rw [show (fun x : ℝ =>
        (thetaCuspTailSecondDensity x : ℂ) *
          (∑ r ∈ Finset.range (d + 1), c r * (x : ℂ) ^ (2 * r + 2))) =
        fun x : ℝ => ∑ r ∈ Finset.range (d + 1),
          c r * ((thetaCuspTailSecondDensity x : ℂ) *
            (x : ℂ) ^ (2 * r + 2)) by
      funext x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring]
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro r _hr
      rw [MeasureTheory.integral_const_mul]
    · intro r _hr
      have hbase : IntegrableOn (fun x : ℝ =>
          (thetaCuspTailSecondDensity x : ℂ) * (x : ℂ) ^ (2 * r + 2))
          (Ioi 0) := by
        rw [show (fun x : ℝ =>
            (thetaCuspTailSecondDensity x : ℂ) * (x : ℂ) ^ (2 * r + 2)) =
          fun x : ℝ =>
            ((x ^ (2 * r + 2) * thetaCuspTailSecondDensity x : ℝ) : ℂ) by
          funext x
          push_cast
          ring]
        exact (integrableOn_pow_mul_thetaCuspTailSecondDensity (2 * r + 2)).ofReal
      exact hbase.const_mul (c r)

/-- The complete atom value packet is exactly twice the canonical finite Taylor core value. -/
theorem tsum_thetaCuspTailSecondDensityAtomCoreValueMomentPacket_eq_two_mul_eval
    (d : ℕ) (z : ℂ) :
    (∑' n : ℕ, thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z n) =
      2 * (xiCTaylorThetaTailCorePolynomial d).eval z := by
  rw [tsum_thetaCuspTailSecondDensityAtomCoreValueMomentPacket_eq_integral,
    xiCTaylorThetaTailCorePolynomial_eval_eq_second_integral]
  ring

/-- Real Hermitian value correlation of an arbitrary summable packet on one positive product
fibre. -/
def thetaPositiveProductFiberRealValueCorrelation
    (V : ℕ → ℂ) (k : ℕ) : ℝ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    (V q.1 * (starRingEnd ℂ) (V q.2)).re

/-- Product-fibre real correlations of an absolutely summable packet remain summable. -/
theorem summable_thetaPositiveProductFiberRealValueCorrelation
    {V : ℕ → ℂ} (hV : Summable V) :
    Summable (thetaPositiveProductFiberRealValueCorrelation V) := by
  let C : ℕ × ℕ → ℂ := fun q => V q.1 * (starRingEnd ℂ) (V q.2)
  have hstar : Summable (fun n : ℕ => ‖(starRingEnd ℂ) (V n)‖) := by
    simpa only [Complex.norm_conj] using hV.norm
  have hC : Summable C := by
    simpa only [C] using
      (summable_mul_of_summable_norm hV.norm hstar)
  have hCre : Summable (fun q : ℕ × ℕ => (C q).re) := by
    exact (hC.map Complex.reCLM Complex.reCLM.continuous).congr
      (fun q => rfl)
  have hfiber := hCre.hasSum.tsum_fiberwise thetaPositivePairProduct
  apply Summable.congr hfiber.summable
  intro k
  unfold thetaPositiveProductFiberRealValueCorrelation
  rw [thetaPositivePairProduct_fiber]
  simpa only [C] using
    (Finset.tsum_subtype' (thetaPositiveFactorPairs k)
      (fun q => (C q).re))

/-- The global real product-fibre correlation is the norm-square of the complete packet sum. -/
theorem tsum_thetaPositiveProductFiberRealValueCorrelation_eq_normSq
    {V : ℕ → ℂ} (hV : Summable V) :
    (∑' k : ℕ, thetaPositiveProductFiberRealValueCorrelation V k) =
      Complex.normSq (∑' n : ℕ, V n) := by
  let C : ℕ × ℕ → ℂ := fun q => V q.1 * (starRingEnd ℂ) (V q.2)
  have hstar : Summable (fun n : ℕ => ‖(starRingEnd ℂ) (V n)‖) := by
    simpa only [Complex.norm_conj] using hV.norm
  have hC : Summable C := by
    simpa only [C] using
      (summable_mul_of_summable_norm hV.norm hstar)
  have hCre : Summable (fun q : ℕ × ℕ => (C q).re) := by
    exact (hC.map Complex.reCLM Complex.reCLM.continuous).congr
      (fun q => rfl)
  change (∑' k : ℕ, ∑ q ∈ thetaPositiveFactorPairs k, (C q).re) = _
  rw [← tsum_eq_tsum_thetaPositiveFactorPairs (fun q : ℕ × ℕ => (C q).re) hCre,
    ← Complex.re_tsum hC]
  rw [show (∑' q : ℕ × ℕ, C q) =
      (∑' n : ℕ, V n) * (starRingEnd ℂ) (∑' n : ℕ, V n) by
    rw [Complex.conj_tsum,
      tsum_mul_tsum_of_summable_norm hV.norm hstar]]
  rw [Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- The canonical finite-core real value correlation is the generic packet correlation. -/
theorem xiCTaylorThetaTailCoreProductFiberValueCorrelation_eq_generic
    (d : ℕ) (z : ℂ) :
    xiCTaylorThetaTailCoreProductFiberValueCorrelation d z =
      thetaPositiveProductFiberRealValueCorrelation
        (thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z) := by
  rfl

/-- The real value correlation is summable after exact regrouping by positive product fibres. -/
theorem summable_xiCTaylorThetaTailCoreProductFiberValueCorrelation
    (d : ℕ) (z : ℂ) :
    Summable (xiCTaylorThetaTailCoreProductFiberValueCorrelation d z) := by
  rw [xiCTaylorThetaTailCoreProductFiberValueCorrelation_eq_generic]
  exact summable_thetaPositiveProductFiberRealValueCorrelation
    (summable_thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z)

/-- **Global value-correlation collapse.**  The radial correlation left by completion is exactly
four times the canonical core norm-square. -/
theorem tsum_xiCTaylorThetaTailCoreProductFiberValueCorrelation_eq
    (d : ℕ) (z : ℂ) :
    (∑' k : ℕ, xiCTaylorThetaTailCoreProductFiberValueCorrelation d z k) =
      4 * Complex.normSq ((xiCTaylorThetaTailCorePolynomial d).eval z) := by
  rw [xiCTaylorThetaTailCoreProductFiberValueCorrelation_eq_generic,
    tsum_thetaPositiveProductFiberRealValueCorrelation_eq_normSq
      (summable_thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z),
    tsum_thetaCuspTailSecondDensityAtomCoreValueMomentPacket_eq_two_mul_eval,
    Complex.normSq_mul]
  norm_num [Complex.normSq_apply]

/-- The completion-scaled fibre currents are absolutely summable. -/
theorem summable_xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent
    (d : ℕ) (z : ℂ) :
    Summable (xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent d z) := by
  apply Summable.congr
    ((summable_xiCTaylorThetaTailCoreProductFiberMomentCurrent d z).mul_left
        (4 * Complex.normSq z ^ (2 : ℕ)) |>.sub
      ((summable_xiCTaylorThetaTailCoreProductFiberValueCorrelation d z).mul_left
        (8 * Complex.normSq z * z.im)))
  intro k
  exact (xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent_eq d z k).symm

/-- **Global completion-scaled current bridge.**  Completion leaves the original core current and
one exact radial norm-square term; no window or top-edge term has been separated or estimated. -/
theorem tsum_xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent_eq
    (d : ℕ) (z : ℂ) :
    (∑' k : ℕ,
      xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent d z k) =
      16 * Complex.normSq z ^ (2 : ℕ) *
          orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z -
        32 * Complex.normSq z * z.im *
          Complex.normSq ((xiCTaylorThetaTailCorePolynomial d).eval z) := by
  have hJ := summable_xiCTaylorThetaTailCoreProductFiberMomentCurrent d z
  have hR := summable_xiCTaylorThetaTailCoreProductFiberValueCorrelation d z
  rw [tsum_congr fun k =>
      xiCTaylorThetaTailCoreProductFiberCompletedTwoPhaseCurrent_eq d z k,
    (hJ.mul_left (4 * Complex.normSq z ^ (2 : ℕ))).tsum_sub
      (hR.mul_left (8 * Complex.normSq z * z.im)),
    tsum_mul_left, tsum_mul_left,
    tsum_xiCTaylorThetaTailCoreProductFiberValueCorrelation_eq]
  have hcurrent := xiCTaylorThetaTailCore_current_eq_tsum_productFiberMomentCurrent d z
  have hcurrent' :
      (∑' k : ℕ, xiCTaylorThetaTailCoreProductFiberMomentCurrent d z k) =
        4 * orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z := by
    linarith
  rw [hcurrent']
  ring

end

end RHTower
