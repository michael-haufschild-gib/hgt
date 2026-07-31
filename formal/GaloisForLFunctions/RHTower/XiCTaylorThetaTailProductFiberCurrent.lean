import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberTranslation
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailSquareIndexPolarization

/-!
# Product-fibre expansion of the theta-tail core current

The exact differentiated theta density has Gaussian decay in its positive square index.  Hence
every atom moment, and therefore every finite core value and derivative packet, is absolutely
summable over that index.  This module records those summability statements and uses them to
regroup the ordered atom-pair current by the arithmetic product of the two positive indices.

No sign or absolute-value majorant is inserted into the current itself: the regrouping preserves
the full signed symmetric correlation on each product fibre.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- Every fixed raw moment of a differentiated density atom is summable over the positive square
index. -/
theorem summable_thetaCuspTailSecondDensityAtomMoment (m : ℕ) :
    Summable (fun n : ℕ =>
      thetaCuspTailSecondDensityAtomMoment (n + 1) m) := by
  let C : ℝ := 5 * Real.exp Real.pi *
    thetaCuspTailSecondDensityAtomMoment 1 m
  have hgauss : Summable (fun n : ℕ =>
      (n : ℝ) ^ 4 * Real.exp (-Real.pi * (n : ℝ) ^ 2)) := by
    simpa only [Nat.cast_ofNat] using
      summable_pow_mul_exp_neg_nat_sq 4 Real.pi_pos
  have hmajor : Summable (fun n : ℕ =>
      C * (((n + 1 : ℕ) : ℝ) ^ 4 *
        Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2)))) :=
    ((summable_nat_add_iff 1).mpr hgauss).mul_left C
  apply Summable.of_nonneg_of_le
    (fun n => thetaCuspTailSecondDensityAtomMoment_nonneg (n + 1) m)
  · intro n
    have h := thetaCuspTailSecondDensityAtomMoment_le_first
      (Nat.succ_pos n) m
    calc
      thetaCuspTailSecondDensityAtomMoment (n + 1) m ≤
          (5 * (((n + 1 : ℕ) : ℝ)) ^ 4 *
            Real.exp (-Real.pi * ((((n + 1 : ℕ) : ℝ)) ^ 2 - 1))) *
              thetaCuspTailSecondDensityAtomMoment 1 m := h
      _ = C * (((n + 1 : ℕ) : ℝ) ^ 4 *
          Real.exp (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2))) := by
        dsimp [C]
        rw [show -Real.pi * ((((n + 1 : ℕ) : ℝ)) ^ 2 - 1) =
            Real.pi + (-Real.pi * (((n + 1 : ℕ) : ℝ) ^ 2)) by ring,
          Real.exp_add]
        ring
  · exact hmajor

/-- The finite core value contributed by one positive-index density atom, written in raw moments.
-/
def thetaCuspTailSecondDensityAtomCoreValueMomentPacket
    (d : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  (thetaCuspTailSecondDensityAtomMoment (n + 1) 0 : ℂ) -
    (z ^ 2 + 1 / 4) *
      ∑ r ∈ Finset.range (d + 1),
        thetaCuspTailSecondSectionSourceCoefficient z r *
          (thetaCuspTailSecondDensityAtomMoment (n + 1) (2 * r + 2) : ℂ)

/-- The finite core derivative contributed by one positive-index density atom, written in raw
moments. -/
def thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket
    (d : ℕ) (z : ℂ) (n : ℕ) : ℂ :=
  ∑ r ∈ Finset.range (d + 1),
    thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient z r *
      (thetaCuspTailSecondDensityAtomMoment (n + 1) (2 * r + 2) : ℂ)

theorem summable_thetaCuspTailSecondDensityAtomCoreValueMomentPacket
    (d : ℕ) (z : ℂ) :
    Summable (thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z) := by
  have h0 : Summable (fun n : ℕ =>
      (thetaCuspTailSecondDensityAtomMoment (n + 1) 0 : ℂ)) :=
    (summable_thetaCuspTailSecondDensityAtomMoment 0).map
      Complex.ofRealCLM Complex.ofRealCLM.continuous
  have hs : Summable (fun n : ℕ =>
      ∑ r ∈ Finset.range (d + 1),
        thetaCuspTailSecondSectionSourceCoefficient z r *
          (thetaCuspTailSecondDensityAtomMoment (n + 1) (2 * r + 2) : ℂ)) := by
    apply summable_sum
    intro r _hr
    exact ((summable_thetaCuspTailSecondDensityAtomMoment (2 * r + 2)).map
      Complex.ofRealCLM Complex.ofRealCLM.continuous).mul_left _
  exact h0.sub (hs.mul_left (z ^ 2 + 1 / 4))

theorem summable_thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket
    (d : ℕ) (z : ℂ) :
    Summable (thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket d z) := by
  apply summable_sum
  intro r _hr
  exact ((summable_thetaCuspTailSecondDensityAtomMoment (2 * r + 2)).map
    Complex.ofRealCLM Complex.ofRealCLM.continuous).mul_left _

/-- The complex raw moment of an atom is its defining real moment. -/
theorem integral_thetaCuspTailSecondDensityAtom_mul_complexPower
    (n m : ℕ) :
    (∫ x : ℝ in Ioi 0,
        (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) * (x : ℂ) ^ m) =
      (thetaCuspTailSecondDensityAtomMoment (n + 1) m : ℂ) := by
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) * (x : ℂ) ^ m) =
      fun x : ℝ => ((x ^ m *
        thetaCuspTailSecondDensityAtom (n + 1) x : ℝ) : ℂ) by
    funext x
    push_cast
    ring]
  rw [thetaCuspTailSecondDensityAtomMoment]
  exact integral_ofReal (X := ℝ) (μ := volume.restrict (Ioi 0)) (𝕜 := ℂ)

theorem integrableOn_thetaCuspTailSecondDensityAtom_mul_complexPower
    (n m : ℕ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) * (x : ℂ) ^ m)
        (Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ =>
      ((x ^ m * thetaCuspTailSecondDensityAtom (n + 1) x : ℝ) : ℂ))
        (Ioi 0) :=
    (integrableOn_pow_mul_thetaCuspTailSecondDensityAtom m
      (Nat.succ_pos n)).ofReal
  convert h using 1
  funext x
  push_cast
  ring

/-- Integration against one density atom sends a finite source-power packet to the corresponding
finite atom-moment packet. -/
theorem integral_thetaCuspTailSecondDensityAtom_mul_finitePowerPacket
    {ι : Type*} (s : Finset ι) (m : ι → ℕ) (a : ι → ℂ) (n : ℕ) :
    (∫ x : ℝ in Ioi 0,
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
        (∑ i ∈ s, a i * (x : ℂ) ^ m i)) =
      ∑ i ∈ s, a i *
        (thetaCuspTailSecondDensityAtomMoment (n + 1) (m i) : ℂ) := by
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
        (∑ i ∈ s, a i * (x : ℂ) ^ m i)) =
      fun x : ℝ => ∑ i ∈ s,
        a i * ((thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
          (x : ℂ) ^ m i) by
    funext x
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring]
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _hi
    rw [MeasureTheory.integral_const_mul,
      integral_thetaCuspTailSecondDensityAtom_mul_complexPower]
  · intro i _hi
    exact (integrableOn_thetaCuspTailSecondDensityAtom_mul_complexPower
      n (m i)).const_mul (a i)

theorem integrableOn_thetaCuspTailSecondDensityAtom_mul_finitePowerPacket
    {ι : Type*} (s : Finset ι) (m : ι → ℕ) (a : ι → ℂ) (n : ℕ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
        (∑ i ∈ s, a i * (x : ℂ) ^ m i)) (Ioi 0) := by
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
        (∑ i ∈ s, a i * (x : ℂ) ^ m i)) =
      fun x : ℝ => ∑ i ∈ s,
        a i * ((thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
          (x : ℂ) ^ m i) by
    funext x
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    ring]
  exact MeasureTheory.integrable_finsetSum _ fun i _hi =>
    (integrableOn_thetaCuspTailSecondDensityAtom_mul_complexPower
      n (m i)).const_mul (a i)

theorem integrableOn_thetaCuspTailSecondDensityAtom_mul_coreAtomDerivative
    (d : ℕ) (z : ℂ) (n : ℕ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
        thetaCuspTailSecondCoreAtomDerivative d z x) (Ioi 0) := by
  simp_rw [thetaCuspTailSecondCoreAtomDerivative_eq_sourcePowerPacket]
  exact integrableOn_thetaCuspTailSecondDensityAtom_mul_finitePowerPacket
    (Finset.range (d + 1)) (fun r => 2 * r + 2)
      (thetaCuspTailSecondCoreAtomDerivativeSourceCoefficient z) n

theorem integrableOn_thetaCuspTailSecondDensityAtom_mul_coreAtom
    (d : ℕ) (z : ℂ) (n : ℕ) :
    IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) (Ioi 0) := by
  have hmass : IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ)) (Ioi 0) := by
    simpa only [pow_zero, mul_one] using
      integrableOn_thetaCuspTailSecondDensityAtom_mul_complexPower n 0
  have hsection : IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
        thetaCuspTailSecondSection d z x) (Ioi 0) := by
    simp_rw [thetaCuspTailSecondSection_eq_sourcePowerPacket]
    exact integrableOn_thetaCuspTailSecondDensityAtom_mul_finitePowerPacket
      (Finset.range (d + 1)) (fun r => 2 * r + 2)
        (thetaCuspTailSecondSectionSourceCoefficient z) n
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) =
      fun x : ℝ =>
        (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) -
          (z ^ 2 + 1 / 4) *
            ((thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
              thetaCuspTailSecondSection d z x) by
    funext x
    unfold thetaCuspTailSecondCoreAtom
    ring]
  exact hmass.sub (hsection.const_mul _)

/-- The actual half-line core value of one density atom is its finite moment packet. -/
theorem integral_thetaCuspTailSecondDensityAtom_mul_coreAtom
    (d : ℕ) (z : ℂ) (n : ℕ) :
    (∫ x : ℝ in Ioi 0,
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) =
      thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z n := by
  have hmassInt : IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ)) (Ioi 0) := by
    simpa only [pow_zero, mul_one] using
      integrableOn_thetaCuspTailSecondDensityAtom_mul_complexPower n 0
  have hsectionInt : IntegrableOn (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
        thetaCuspTailSecondSection d z x) (Ioi 0) := by
    simp_rw [thetaCuspTailSecondSection_eq_sourcePowerPacket]
    rw [show (fun x : ℝ =>
        (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
          (∑ r ∈ Finset.range (d + 1),
            thetaCuspTailSecondSectionSourceCoefficient z r *
              (x : ℂ) ^ (2 * r + 2))) =
        fun x : ℝ => ∑ r ∈ Finset.range (d + 1),
          thetaCuspTailSecondSectionSourceCoefficient z r *
            ((thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
              (x : ℂ) ^ (2 * r + 2)) by
      funext x
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring]
    exact MeasureTheory.integrable_finsetSum _ fun r _hr =>
      (integrableOn_thetaCuspTailSecondDensityAtom_mul_complexPower
        n (2 * r + 2)).const_mul _
  rw [show (fun x : ℝ =>
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
        thetaCuspTailSecondCoreAtom d z x) =
      fun x : ℝ =>
        (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) -
          (z ^ 2 + 1 / 4) *
            ((thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
              thetaCuspTailSecondSection d z x) by
    funext x
    unfold thetaCuspTailSecondCoreAtom
    ring]
  rw [MeasureTheory.integral_sub hmassInt (hsectionInt.const_mul _),
    MeasureTheory.integral_const_mul]
  have hmass := integral_thetaCuspTailSecondDensityAtom_mul_complexPower n 0
  simp only [pow_zero, mul_one] at hmass
  rw [hmass]
  simp_rw [thetaCuspTailSecondSection_eq_sourcePowerPacket]
  rw [integral_thetaCuspTailSecondDensityAtom_mul_finitePowerPacket]
  rfl

/-- The actual half-line spectral derivative of one density atom is its finite derivative moment
packet. -/
theorem integral_thetaCuspTailSecondDensityAtom_mul_coreAtomDerivative
    (d : ℕ) (z : ℂ) (n : ℕ) :
    (∫ x : ℝ in Ioi 0,
      (thetaCuspTailSecondDensityAtom (n + 1) x : ℂ) *
        thetaCuspTailSecondCoreAtomDerivative d z x) =
      thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket d z n := by
  simp_rw [thetaCuspTailSecondCoreAtomDerivative_eq_sourcePowerPacket]
  rw [integral_thetaCuspTailSecondDensityAtom_mul_finitePowerPacket]
  rfl

/-- One ordered atom-pair integral is the exact symmetric polarization of the two finite atom
moment packets. -/
theorem integral_xiCTaylorThetaTailCoreAtomPairCorrelationKernel_eq_momentPackets
    (d : ℕ) (z : ℂ) (q : ℕ × ℕ) :
    (∫ p : ℝ × ℝ,
      xiCTaylorThetaTailCoreAtomPairCorrelationKernel d z q p
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      ((thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket d z q.1 *
          (starRingEnd ℂ)
            (thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z q.2)).im +
        (thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket d z q.2 *
          (starRingEnd ℂ)
            (thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z q.1)).im) / 2 := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let f₁ : ℝ → ℂ := fun x =>
    (thetaCuspTailSecondDensityAtom (q.1 + 1) x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x
  let g₁ : ℝ → ℂ := fun x =>
    (thetaCuspTailSecondDensityAtom (q.1 + 1) x : ℂ) *
      thetaCuspTailSecondCoreAtom d z x
  let f₂ : ℝ → ℂ := fun x =>
    (thetaCuspTailSecondDensityAtom (q.2 + 1) x : ℂ) *
      thetaCuspTailSecondCoreAtomDerivative d z x
  let g₂ : ℝ → ℂ := fun x =>
    (thetaCuspTailSecondDensityAtom (q.2 + 1) x : ℂ) *
      thetaCuspTailSecondCoreAtom d z x
  let H₁ : ℝ × ℝ → ℝ := fun p =>
    (f₁ p.1 * (starRingEnd ℂ) (g₂ p.2)).im
  let H₂ : ℝ × ℝ → ℝ := fun p =>
    (f₂ p.2 * (starRingEnd ℂ) (g₁ p.1)).im
  have hf₁ : Integrable f₁ mu :=
    integrableOn_thetaCuspTailSecondDensityAtom_mul_coreAtomDerivative d z q.1
  have hg₁ : Integrable g₁ mu :=
    integrableOn_thetaCuspTailSecondDensityAtom_mul_coreAtom d z q.1
  have hf₂ : Integrable f₂ mu :=
    integrableOn_thetaCuspTailSecondDensityAtom_mul_coreAtomDerivative d z q.2
  have hg₂ : Integrable g₂ mu :=
    integrableOn_thetaCuspTailSecondDensityAtom_mul_coreAtom d z q.2
  have hg₁conj : Integrable (fun x => (starRingEnd ℂ) (g₁ x)) mu :=
    (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hg₁
  have hg₂conj : Integrable (fun x => (starRingEnd ℂ) (g₂ x)) mu :=
    (RCLike.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.integrable_comp hg₂
  have hprod₁ : Integrable (fun p : ℝ × ℝ =>
      f₁ p.1 * (starRingEnd ℂ) (g₂ p.2)) (mu.prod mu) :=
    hf₁.mul_prod hg₂conj
  have hprod₂ : Integrable (fun p : ℝ × ℝ =>
      f₂ p.2 * (starRingEnd ℂ) (g₁ p.1)) (mu.prod mu) := by
    simpa only [mul_comm] using hg₁conj.mul_prod hf₂
  have hH₁ : Integrable H₁ (mu.prod mu) := hprod₁.im
  have hH₂ : Integrable H₂ (mu.prod mu) := hprod₂.im
  have hmul₁ : (∫ p : ℝ × ℝ,
      f₁ p.1 * (starRingEnd ℂ) (g₂ p.2) ∂mu.prod mu) =
      (∫ x : ℝ, f₁ x ∂mu) *
        (starRingEnd ℂ) (∫ y : ℝ, g₂ y ∂mu) := by
    have h := MeasureTheory.integral_prod_mul (μ := mu) (ν := mu)
      f₁ (fun y => (starRingEnd ℂ) (g₂ y))
    rw [integral_conj] at h
    exact h
  have hmul₂ : (∫ p : ℝ × ℝ,
      f₂ p.2 * (starRingEnd ℂ) (g₁ p.1) ∂mu.prod mu) =
      (∫ y : ℝ, f₂ y ∂mu) *
        (starRingEnd ℂ) (∫ x : ℝ, g₁ x ∂mu) := by
    have h := MeasureTheory.integral_prod_mul (μ := mu) (ν := mu)
      (fun x => (starRingEnd ℂ) (g₁ x)) f₂
    rw [integral_conj] at h
    simpa only [mul_comm] using h
  have him₁ : (∫ p : ℝ × ℝ, H₁ p ∂mu.prod mu) =
      ((∫ x : ℝ, f₁ x ∂mu) *
        (starRingEnd ℂ) (∫ y : ℝ, g₂ y ∂mu)).im := by
    rw [← hmul₁]
    simpa only [H₁, RCLike.im_eq_complex_im] using integral_im hprod₁
  have him₂ : (∫ p : ℝ × ℝ, H₂ p ∂mu.prod mu) =
      ((∫ y : ℝ, f₂ y ∂mu) *
        (starRingEnd ℂ) (∫ x : ℝ, g₁ x ∂mu)).im := by
    rw [← hmul₂]
    simpa only [H₂, RCLike.im_eq_complex_im] using integral_im hprod₂
  have hf₁int : (∫ x : ℝ, f₁ x ∂mu) =
      thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket d z q.1 := by
    exact integral_thetaCuspTailSecondDensityAtom_mul_coreAtomDerivative d z q.1
  have hg₁int : (∫ x : ℝ, g₁ x ∂mu) =
      thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z q.1 := by
    exact integral_thetaCuspTailSecondDensityAtom_mul_coreAtom d z q.1
  have hf₂int : (∫ x : ℝ, f₂ x ∂mu) =
      thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket d z q.2 := by
    exact integral_thetaCuspTailSecondDensityAtom_mul_coreAtomDerivative d z q.2
  have hg₂int : (∫ x : ℝ, g₂ x ∂mu) =
      thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z q.2 := by
    exact integral_thetaCuspTailSecondDensityAtom_mul_coreAtom d z q.2
  rw [show (fun p : ℝ × ℝ =>
      xiCTaylorThetaTailCoreAtomPairCorrelationKernel d z q p) =
      fun p : ℝ × ℝ => (H₁ p + H₂ p) / 2 by
    funext p
    rcases p with ⟨x, y⟩
    unfold xiCTaylorThetaTailCoreAtomPairCorrelationKernel
      xiCTaylorThetaTailCorePairCurrent H₁ H₂ f₁ f₂ g₁ g₂
    simp only [map_mul, Complex.conj_ofReal,
      Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
    ring]
  rw [show (fun p : ℝ × ℝ => (H₁ p + H₂ p) / 2) =
      fun p : ℝ × ℝ => (1 / 2 : ℝ) * (H₁ p + H₂ p) by
    funext p
    ring]
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add hH₁ hH₂, him₁, him₂,
    hf₁int, hg₂int, hf₂int, hg₁int]
  ring

/-- The unsymmetrized complex correlation of two atom moment packets. -/
def xiCTaylorThetaTailCoreAtomPairComplexMomentCorrelation
    (d : ℕ) (z : ℂ) (q : ℕ × ℕ) : ℂ :=
  thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket d z q.1 *
    (starRingEnd ℂ)
      (thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z q.2)

/-- The exact real current carried by one ordered pair of atom moment packets. -/
def xiCTaylorThetaTailCoreAtomPairMomentCurrent
    (d : ℕ) (z : ℂ) (q : ℕ × ℕ) : ℝ :=
  ((xiCTaylorThetaTailCoreAtomPairComplexMomentCorrelation d z q).im +
    (xiCTaylorThetaTailCoreAtomPairComplexMomentCorrelation d z q.swap).im) / 2

theorem integral_xiCTaylorThetaTailCoreAtomPairCorrelationKernel_eq_pairMomentCurrent
    (d : ℕ) (z : ℂ) (q : ℕ × ℕ) :
    (∫ p : ℝ × ℝ,
      xiCTaylorThetaTailCoreAtomPairCorrelationKernel d z q p
        ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      xiCTaylorThetaTailCoreAtomPairMomentCurrent d z q := by
  simpa only [xiCTaylorThetaTailCoreAtomPairMomentCurrent,
    xiCTaylorThetaTailCoreAtomPairComplexMomentCorrelation,
    Prod.swap_prod_mk, Prod.fst, Prod.snd] using!
      integral_xiCTaylorThetaTailCoreAtomPairCorrelationKernel_eq_momentPackets d z q

/-- Absolute summability of the unsymmetrized complex atom correlation. -/
theorem summable_xiCTaylorThetaTailCoreAtomPairComplexMomentCorrelation
    (d : ℕ) (z : ℂ) :
    Summable (xiCTaylorThetaTailCoreAtomPairComplexMomentCorrelation d z) := by
  let D := thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket d z
  let V := thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z
  have hD : Summable D :=
    summable_thetaCuspTailSecondDensityAtomCoreDerivativeMomentPacket d z
  have hV : Summable V :=
    summable_thetaCuspTailSecondDensityAtomCoreValueMomentPacket d z
  have hVconjNorm : Summable (fun n : ℕ => ‖(starRingEnd ℂ) (V n)‖) := by
    simpa only [Complex.norm_conj] using hV.norm
  have h := summable_mul_of_summable_norm hD.norm hVconjNorm
  exact h

/-- The exact ordered atom-pair current is absolutely summable.  This is the analytic permission
to regroup it by the product of its two positive indices. -/
theorem summable_xiCTaylorThetaTailCoreAtomPairMomentCurrent
    (d : ℕ) (z : ℂ) :
    Summable (xiCTaylorThetaTailCoreAtomPairMomentCurrent d z) := by
  let A := xiCTaylorThetaTailCoreAtomPairComplexMomentCorrelation d z
  have hA : Summable A :=
    summable_xiCTaylorThetaTailCoreAtomPairComplexMomentCorrelation d z
  have hAim : Summable (fun q : ℕ × ℕ => (A q).im) := by
    simpa only [Function.comp_apply] using!
      hA.map Complex.imCLM Complex.imCLM.continuous
  have hswap : Summable (fun q : ℕ × ℕ => (A q.swap).im) := by
    have h := hAim.comp_injective Prod.swap_injective
    simpa only [Function.comp_apply] using! h
  have hcurrent := (hAim.add hswap).mul_left (1 / 2 : ℝ)
  change Summable (fun q : ℕ × ℕ =>
    ((A q).im + (A q.swap).im) / 2)
  simpa only [div_eq_mul_inv, one_div, invOf_eq_inv, one_mul, mul_comm]
    using hcurrent

theorem summable_integral_xiCTaylorThetaTailCoreAtomPairCorrelationKernel
    (d : ℕ) (z : ℂ) :
    Summable (fun q : ℕ × ℕ =>
      ∫ p : ℝ × ℝ,
        xiCTaylorThetaTailCoreAtomPairCorrelationKernel d z q p
          ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) :=
  (summable_xiCTaylorThetaTailCoreAtomPairMomentCurrent d z).congr fun q =>
    (integral_xiCTaylorThetaTailCoreAtomPairCorrelationKernel_eq_pairMomentCurrent
      d z q).symm

/-- The signed current of the complete finite packet with fixed positive-index product `k`. -/
def xiCTaylorThetaTailCoreProductFiberMomentCurrent
    (d : ℕ) (z : ℂ) (k : ℕ) : ℝ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    xiCTaylorThetaTailCoreAtomPairMomentCurrent d z q

/-- Divisor reflection makes the two halves of the symmetric atom-pair polarization identical on
each fixed product fibre.  Thus a fibre current is one unsymmetrized Dirichlet-convolution
coefficient, not an average of two unrelated terms. -/
theorem xiCTaylorThetaTailCoreProductFiberMomentCurrent_eq_unsymmetrized
    (d k : ℕ) (z : ℂ) :
    xiCTaylorThetaTailCoreProductFiberMomentCurrent d z k =
      ∑ q ∈ thetaPositiveFactorPairs k,
        (xiCTaylorThetaTailCoreAtomPairComplexMomentCorrelation d z q).im := by
  let A : (ℕ × ℕ) → ℝ := fun q =>
    (xiCTaylorThetaTailCoreAtomPairComplexMomentCorrelation d z q).im
  have hswap : (∑ q ∈ thetaPositiveFactorPairs k, A q.swap) =
      ∑ q ∈ thetaPositiveFactorPairs k, A q := by
    refine Finset.sum_bij' (fun q _ => q.swap) (fun q _ => q.swap)
      (fun q hq => thetaPositiveFactorPairs_swap_mem hq)
      (fun q hq => thetaPositiveFactorPairs_swap_mem hq) ?_ ?_ ?_
    · intro q _hq
      exact Prod.swap_swap q
    · intro q _hq
      exact Prod.swap_swap q
    · intro q _hq
      rfl
  unfold xiCTaylorThetaTailCoreProductFiberMomentCurrent
  rw [show (∑ q ∈ thetaPositiveFactorPairs k,
      xiCTaylorThetaTailCoreAtomPairMomentCurrent d z q) =
      ((∑ q ∈ thetaPositiveFactorPairs k, A q) +
        ∑ q ∈ thetaPositiveFactorPairs k, A q.swap) / 2 by
    unfold xiCTaylorThetaTailCoreAtomPairMomentCurrent A
    rw [← Finset.sum_add_distrib]
    simp only [Finset.sum_div]]
  rw [hswap]
  ring

theorem summable_xiCTaylorThetaTailCoreProductFiberMomentCurrent
    (d : ℕ) (z : ℂ) :
    Summable (xiCTaylorThetaTailCoreProductFiberMomentCurrent d z) := by
  have h := (summable_xiCTaylorThetaTailCoreAtomPairMomentCurrent d z).hasSum
    |>.tsum_fiberwise thetaPositivePairProduct
  rw [show xiCTaylorThetaTailCoreProductFiberMomentCurrent d z =
      fun k => ∑' q : thetaPositivePairProduct ⁻¹' {k},
        xiCTaylorThetaTailCoreAtomPairMomentCurrent d z q by
    funext k
    rw [xiCTaylorThetaTailCoreProductFiberMomentCurrent,
      thetaPositivePairProduct_fiber]
    exact (Finset.tsum_subtype' (thetaPositiveFactorPairs k)
      (xiCTaylorThetaTailCoreAtomPairMomentCurrent d z)).symm]
  exact h.summable

/-- Exact product-fibre expansion of the full raw theta-tail core current.  Each inner sum is a
finite arithmetic divisor-reflection packet, and the outer sum is absolutely convergent. -/
theorem xiCTaylorThetaTailCore_current_eq_tsum_productFiberMomentCurrent
    (d : ℕ) (z : ℂ) :
    orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
      (1 / 4 : ℝ) *
        ∑' k : ℕ, xiCTaylorThetaTailCoreProductFiberMomentCurrent d z k := by
  rw [xiCTaylorThetaTailCore_current_eq_tsum_atomPairIntegral]
  congr 1
  rw [show (fun q : ℕ × ℕ =>
      ∫ p : ℝ × ℝ,
        xiCTaylorThetaTailCoreAtomPairCorrelationKernel d z q p
          ∂((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0)))) =
      xiCTaylorThetaTailCoreAtomPairMomentCurrent d z by
    funext q
    exact integral_xiCTaylorThetaTailCoreAtomPairCorrelationKernel_eq_pairMomentCurrent
      d z q]
  exact tsum_eq_tsum_thetaPositiveFactorPairs
    (xiCTaylorThetaTailCoreAtomPairMomentCurrent d z)
    (summable_xiCTaylorThetaTailCoreAtomPairMomentCurrent d z)

end

end RHTower
