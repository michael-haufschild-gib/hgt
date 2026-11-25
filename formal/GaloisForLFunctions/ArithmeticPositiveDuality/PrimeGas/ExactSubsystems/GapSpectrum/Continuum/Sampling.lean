import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.Continuum.Discrete

/-! # The joint Borel law of the common divisor and the measured energy gap -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open MeasureTheory

private def assemblePair : (ℕ+ × ReducedDirection) ≃ (ℕ+ × ℕ+) :=
  (Equiv.prodComm ℕ+ ReducedDirection).trans _root_.RHTower.thetaCuspPrimitiveRayIndexEquivPositivePair

/-- Undoing the primitive decomposition takes the independent scale and line laws to the original Gibbs samples. -/
theorem primitive_product_samples {x : ℝ} (hx : 1/2 < x) :
    Measure.map (fun p : ℕ+ × ReducedDirection => (p.2.val.1*p.1,p.2.val.2*p.1))
      ((scaleLaw x (by linarith) : Measure ℕ+).prod (directionLaw x hx : Measure ReducedDirection)) =
      (gibbsPairLaw x hx : Measure (ℕ+ × ℕ+)) := by
  change Measure.map assemblePair _ = _
  apply Measure.ext_of_singleton
  intro q
  obtain ⟨⟨k,d⟩,rfl⟩ := assemblePair.surjective q
  have he : assemblePair ⁻¹' {assemblePair (k,d)} = {(k,d)} := by
    ext p
    exact assemblePair.injective.eq_iff
  rw [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _),he,
    ← Set.singleton_prod_singleton,Measure.prod_prod,scaleLaw_atom,directionLaw_atom,gibbsPairLaw_atom]
  rcases d with ⟨⟨a,b⟩,hc⟩
  change ENNReal.ofReal (commonScaleWeight x k).re * ENNReal.ofReal (overlapCoefficient x (gapFrequency (a,b))).re =
    ENNReal.ofReal (gapAmplitude x (a*k,b*k)).re
  obtain ⟨u,hu,heu⟩ := commonScaleWeight_positive (by linarith : 1/4 < x) k
  obtain ⟨v,hv,hev⟩ := primitive_line_positive hx (⟨(a,b),hc⟩ : ReducedDirection)
  change (v:ℂ) = overlapCoefficient x (gapFrequency (a,b)) at hev
  rw [gapAmplitude_disintegrates hx hc,← heu,← hev,← Complex.ofReal_mul]
  simp only [Complex.ofReal_re]
  rw [ENNReal.ofReal_mul hv.le,mul_comm]

/-- Read the signed energy gap directly from the two Gibbs samples. -/
def sampledGapLaw (x u : ℝ) (hx : 1/2 < x) : ProbabilityMeasure ℝ :=
  (gibbsPairLaw x hx).map (f := fun q => u*gapFrequency q) Measurable.of_discrete.aemeasurable

/-- Read the arithmetic common divisor and the signed energy gap in the same sample. -/
def sampledJointLaw (x u : ℝ) (hx : 1/2 < x) : ProbabilityMeasure (ℕ+ × ℝ) :=
  (gibbsPairLaw x hx).map (f := fun q => (q.1.gcd q.2,u*gapFrequency q)) Measurable.of_discrete.aemeasurable

private theorem observables_assemble (u : ℝ) (p : ℕ+ × ReducedDirection) :
    ((assemblePair p).1.gcd (assemblePair p).2,u*gapFrequency (assemblePair p)) =
      (p.1,u*gapFrequency p.2.val) := by
  rcases p with ⟨k,⟨⟨a,b⟩,hc⟩⟩
  change ((a*k).gcd (b*k),u*gapFrequency (a*k,b*k)) = (k,u*gapFrequency (a,b))
  rw [gapFrequency_scale]
  congr 1
  apply PNat.coe_injective
  rw [PNat.gcd_coe,PNat.mul_coe,PNat.mul_coe,Nat.gcd_mul_right,(PNat.coprime_coe.mpr hc).gcd_eq_one,one_mul]

/-- Gcd and scaled frequency are independent for every physical temperature and every real scaling. -/
theorem sampled_joint_eq_product {x : ℝ} (hx : 1/2 < x) (u : ℝ) :
    sampledJointLaw x u hx = (scaleLaw x (by linarith)).prod (sampledGapLaw x u hx) := by
  let A := (scaleLaw x (by linarith) : Measure ℕ+)
  let B := (directionLaw x hx : Measure ReducedDirection)
  let F := fun q : ℕ+ × ℕ+ => (q.1.gcd q.2,u*gapFrequency q)
  let G := fun d : ReducedDirection => u*gapFrequency d.val
  have he : Measure.map assemblePair (A.prod B) = (gibbsPairLaw x hx : Measure (ℕ+ × ℕ+)) :=
    primitive_product_samples hx
  have hj : (sampledJointLaw x u hx : Measure (ℕ+ × ℝ)) = A.prod (B.map G) := by
    change Measure.map F _ = _
    rw [← he,Measure.map_map Measurable.of_discrete Measurable.of_discrete]
    have hf : F ∘ assemblePair = Prod.map id G := funext (observables_assemble u)
    rw [hf,← Measure.map_prod_map A B measurable_id Measurable.of_discrete,Measure.map_id]
  have hm := congrArg (Measure.map (Prod.snd : ℕ+ × ℝ → ℝ)) hj
  change Measure.map Prod.snd (Measure.map F _) = _ at hm
  rw [Measure.map_map measurable_snd Measurable.of_discrete,Measure.map_snd_prod,measure_univ,one_smul] at hm
  have hgap : (sampledGapLaw x u hx : Measure ℝ) = B.map G := hm
  apply Subtype.ext
  change (sampledJointLaw x u hx : Measure (ℕ+ × ℝ)) = A.prod (sampledGapLaw x u hx : Measure ℝ)
  rw [hj,hgap]

#print axioms primitive_product_samples
#print axioms sampled_joint_eq_product

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
