import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.ResonantDraws.RelativeAccuracy.PhysicalDate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw

/-! # Scalar snapshots from the actual first crossing and first return -/
open Set Filter MeasureTheory ProbabilityTheory
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.RelativeAccuracy
noncomputable section
open FirstPassageSelection

/-- At every late prescribed delay the empty-circuit probability has
relative error at most five times two to minus M. Conditioning on this reading changes the
probability of each measurable expansion-closed event by at most twenty times two to minus M.
The same deadline works from time zero, the crossing and the first return. -/
theorem gaussian_finite_first_passage_posterior (A : ℕ) :
    ∃ C : ℕ, ∀ k j s : ℕ,
      let n := k+1
      let N := k+3
      let D : ℕ := 2^N
      let M := D^(A+1)
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let σ := crossingOrigin n j (9/80)
      let Δ := crossingWait n j s
      ∀ x : ℝ, 1/(2:ℝ)^M≤x → x+1/(2:ℝ)^(M^2)≤1/2 →
      ∀ t ≥ (2:ℝ)^(D^C), ∀ o ∈ ({0,σ,fun y => σ y+Δ y} : Set ((PrefixIndex n → ℝ) → ℝ)),
        let p := zeroGateArcDensity D x
        let E := {y | pathGateDistance n 0 y (o y+t)≤zeroGateArcTolerance x}
        |μ.real E/p-1| ≤ 5*(1/(2:ℝ)^M) ∧ ∀ B, MeasurableSet B → expansionClosed B →
          |μ.real (B ∩ E)/μ.real E-μ.real B| ≤ 20*(1/(2:ℝ)^M) := by
  obtain ⟨C,hC⟩ := gaussian_relative_scalar_snapshot A
  refine ⟨C,fun k j s => ?_⟩
  intro n N D M μ σ Δ x hx hx' t ht o ho p E
  have hσ : ∀ a > (0:ℝ), ∀ y, a*σ (a • y)=σ y := fun a ha => smul_crossingOrigin n j (9/80) ha
  have hΔ : ∀ a > (0:ℝ), ∀ y, a*Δ (a • y)=Δ y := fun a ha => smul_crossingWait n j s ha
  have hor : Measurable o ∧ ∀ a > (0:ℝ), ∀ y, a*o (a • y)=o y := by
    rcases ho with h | h | h
    · subst o; exact ⟨measurable_const,fun _ _ _ => mul_zero _⟩
    · subst o; exact ⟨measurable_crossingOrigin ..,hσ⟩
    · change o=(fun y => σ y+Δ y) at h
      subst o
      exact ⟨(measurable_crossingOrigin ..).add (measurable_crossingWait ..),
        fun a ha y => by rw [mul_add,hσ a ha y,hΔ a ha y]⟩
  have hh := hC k x hx hx' t ht o hor.1 hor.2
  have hq := hh univ MeasurableSet.univ (fun _ _ _ _ => mem_univ _)
  simp only [univ_inter,probReal_univ,one_mul] at hq
  let e := μ.real E
  let v := 1/(2:ℝ)^M
  let d := 5*v
  have hD : 8≤D := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (by dsimp only [N]; omega : 3≤N)
  have hM : D≤M := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<D) (by omega : 1≤A+1)
  have hD₀ : (0:ℝ)<D := Nat.cast_pos.mpr (by omega)
  have hv : 0<v := one_div_pos.mpr (pow_pos (by norm_num) _)
  have hden : (16:ℝ)≤(2:ℝ)^M := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by omega : 4≤M)
  have hp : 0<p := mul_pos hD₀ (pow_pos ((one_div_pos.mpr (pow_pos (by norm_num) _)).trans_le hx) _)
  have hd : d≤1/2 := by
    change 5*(1/(2:ℝ)^M)≤1/2
    rw [mul_one_div,div_le_iff₀ (by positivity)]
    linarith only [hden]
  have he : |e-p|≤d*p := hq.trans_eq (by dsimp only [d,v]; ring)
  have he₀ : p/2≤e := by linarith only [(abs_le.mp he).1,mul_le_mul_of_nonneg_right hd hp.le]
  have hep : 0<e := (half_pos hp).trans_le he₀
  constructor
  · change |e/p-1|≤d
    rw [show e/p-1=(e-p)/p by field_simp [hp.ne'],abs_div,abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr he
  intro B hm hB
  let b := μ.real B
  let a := μ.real (B ∩ E)
  have hb : 0≤b := measureReal_nonneg
  have hb' : b≤1 := (measureReal_mono (subset_univ _)).trans_eq probReal_univ
  have hab : |a-b*p|≤d*p := (hh B hm hB).trans_eq (by dsimp only [d]; ring)
  have hdep : |a-b*e|≤2*(d*p) := calc
    _ = |(a-b*p)+b*(p-e)| := by ring_nf
    _ ≤ |a-b*p|+|b*(p-e)| := abs_add_le ..
    _ ≤ d*p+d*p := by
      rw [abs_mul,abs_of_nonneg hb,abs_sub_comm p e]
      exact add_le_add hab ((mul_le_mul_of_nonneg_left he hb).trans
        (mul_le_of_le_one_left (mul_nonneg (by dsimp only [d]; positivity) hp.le) hb'))
    _ = _ := (two_mul _).symm
  change |a/e-b|≤20*v
  rw [show a/e-b=(a-b*e)/e by field_simp [hep.ne'],abs_div,abs_of_pos hep,div_le_iff₀ hep]
  apply hdep.trans
  have h := mul_le_mul_of_nonneg_left he₀ (show 0≤(20:ℝ)*v by positivity)
  exact (show 2*(d*p)=(20*v)*(p/2) by dsimp only [d]; ring).le.trans h

#print axioms gaussian_finite_first_passage_posterior

/-- Uniform joint distribution of the actual first crossing and first wait
after reading an empty circuit at a prescribed delay from the crossing. -/
theorem gaussian_finite_joint_first_passage (A : ℕ) :
    ∃ C : ℕ, ∀ k j s : ℕ,
      let n := k+1
      let D : ℕ := 2^(k+3)
      let M := D^(A+1)
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let σ := crossingOrigin n j (9/80)
      let Δ := crossingWait n j s
      ∀ x : ℝ, 1/(2:ℝ)^M≤x → x+1/(2:ℝ)^(M^2)≤1/2 → ∀ t ≥ (2:ℝ)^(D^C),
        let E := {y | pathGateDistance n 0 y (σ y+t)≤zeroGateArcTolerance x}
        ∀ u v : ℝ, 0≤u → 0≤v →
          let B := {y | σ y≤u ∧ Δ y≤v}
          |μ.real (B ∩ E)/μ.real E-μ.real B|≤20*(1/(2:ℝ)^M) := by
  obtain ⟨C,hc⟩ := gaussian_finite_first_passage_posterior A
  refine ⟨C,fun k j s => ?_⟩
  intro n D M μ σ Δ x hx hx' t ht E u v hu hv B
  have hb : MeasurableSet B := (measurableSet_Iic.preimage (measurable_crossingOrigin n j (9/80))).inter
    (measurableSet_Iic.preimage (measurable_crossingWait n j s))
  apply (hc k j s x hx hx' t ht σ (by simp)).2 B hb
  intro a ha y hy
  have hp := zero_lt_one.trans_le ha
  have hσ := smul_crossingOrigin n j (9/80) hp y
  have hΔ := smul_crossingWait n j s hp y
  exact ⟨(le_of_mul_le_mul_left (hσ.le.trans (hy.1.trans (le_mul_of_one_le_left hu ha))) hp),
    le_of_mul_le_mul_left (hΔ.le.trans (hy.2.trans (le_mul_of_one_le_left hv ha))) hp⟩

#print axioms gaussian_finite_joint_first_passage
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ResonantDraws.RelativeAccuracy
