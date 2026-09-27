import GaloisForLFunctions.RHTower.CCMWeilFrustratedTriangle
import GaloisForLFunctions.RHTower.ThetaPrimeFrustratedTriangle

/-!
# Actual prime frustration gives a strict collective Weil lower bound

For cofinally large prime positions we construct three compact interior sources
with negative, negative, positive full couplings. Their entire real span has a
strictly positive correction to the separate-edge lower estimate. This asserts
a gain over that estimate, not nonnegativity of the full form on arbitrary sources.
-/

noncomputable section

open MeasureTheory Set
open scoped SchwartzMap

namespace RHTower

open ThetaSourceWard

theorem ccmWeilRealPolar_compactReal_eq (a : SuzukiPositiveAperture)
    (phi psi : 𝓢(ℝ, ℝ)) (hpc : HasCompactSupport phi) (hqc : HasCompactSupport psi)
    (hps : tsupport phi ⊆ Ioo (-a.1) a.1) (hqs : tsupport psi ⊆ Ioo (-a.1) a.1) :
    ccmWeilRealPolar a (ccmThetaSourceOfCompactRealProfile a phi hpc hps).toCCMFormVector
      (ccmThetaSourceOfCompactRealProfile a psi hqc hqs).toCCMFormVector =
      thetaRealWeilPolar phi psi := by
  have hadd : tsupport (phi + psi) ⊆ Ioo (-a.1) a.1 :=
    (tsupport_add phi psi).trans (union_subset hps hqs)
  have hsub : tsupport (phi - psi) ⊆ Ioo (-a.1) a.1 :=
    (tsupport_sub phi psi).trans (union_subset hps hqs)
  let u := ccmThetaSourceOfCompactRealProfile a phi hpc hps
  let v := ccmThetaSourceOfCompactRealProfile a psi hqc hqs
  let w := ccmThetaSourceOfCompactRealProfile a (phi + psi) (hpc.add hqc) hadd
  let z := ccmThetaSourceOfCompactRealProfile a (phi - psi) (hpc.sub hqc) hsub
  have hw : w.toCCMFormVector = u.toCCMFormVector + v.toCCMFormVector := by
    have h := ccmSmoothSourceFormVector_eq_add_smul u v w 1 (fun x => by
      simp only [u, v, w, ccmThetaSourceOfCompactRealProfile_apply, add_apply,
        Complex.ofReal_add, one_mul]
      ring)
    simpa only [one_smul] using h
  have hz : z.toCCMFormVector = u.toCCMFormVector - v.toCCMFormVector := by
    have h := ccmSmoothSourceFormVector_eq_add_smul u v z (-1) (fun x => by
      simp only [u, v, z, ccmThetaSourceOfCompactRealProfile_apply, sub_apply,
        Complex.ofReal_sub]
      ring)
    simpa only [neg_one_smul, sub_eq_add_neg] using h
  change (ccmRestrictedWeilSourceQuadratic a (u.toCCMFormVector + v.toCCMFormVector) -
    ccmRestrictedWeilSourceQuadratic a (u.toCCMFormVector - v.toCCMFormVector)) / 4 = _
  rw [← hw, ← hz]
  simp only [w, z, ccmCompactRealProfileEnergy_eq, thetaRealWeilPolar]

/-- All signs and the positive correction are constructed, for cofinally large primes. -/
theorem exists_cofinal_ccmPrime_frustrated_triangle (N : ℕ) :
    ∃ (p q : ℕ) (r m : ℝ) (a : SuzukiPositiveAperture)
      (u v w : CCMComplexSmoothInteriorSource a),
      N ≤ p ∧ Nat.Prime p ∧ Nat.Prime q ∧ 2 * p < q ∧ 0 < r ∧ 0 < m ∧
      Function.support u = Metric.ball 0 r ∧
      Function.support v = Metric.ball (Real.log p) r ∧
      Function.support w = Metric.ball (Real.log q) r ∧
      ccmWeilRealPolar a u.toCCMFormVector v.toCCMFormVector < 0 ∧
      ccmWeilRealPolar a u.toCCMFormVector w.toCCMFormVector < 0 ∧
      0 < ccmWeilRealPolar a v.toCCMFormVector w.toCCMFormVector ∧
      ∀ x y z : ℝ,
        ccmWeilTriangleSeparateLower a u.toCCMFormVector v.toCCMFormVector w.toCCMFormVector x y z +
          m * (x ^ 2 + y ^ 2 + z ^ 2) ≤
        ccmRestrictedWeilSourceQuadratic a
          ((x : ℂ) • u.toCCMFormVector + (y : ℂ) • v.toCCMFormVector + (z : ℂ) • w.toCCMFormVector) := by
  obtain ⟨p, q, r, hr, hpN, hp, hq, hpq, h₁, h₂, h₃⟩ :=
    exists_cofinal_thetaPrime_frustrated_triangle N
  let phi := thetaTranslatedBumpGround r hr 0
  let psi := thetaTranslatedBumpGround r hr (Real.log p)
  let chi := thetaTranslatedBumpGround r hr (Real.log q)
  have hpc := compact_thetaTranslatedBumpGround r hr 0
  have hqc := compact_thetaTranslatedBumpGround r hr (Real.log p)
  have hcc := compact_thetaTranslatedBumpGround r hr (Real.log q)
  obtain ⟨A, hA, hbound⟩ := ((hpc.union hqc).union hcc).isBounded.exists_pos_norm_lt
  let a : SuzukiPositiveAperture := ⟨A, hA⟩
  have hs : (tsupport phi ∪ tsupport psi) ∪ tsupport chi ⊆ Ioo (-a.1) a.1 := by
    intro x hx
    exact abs_lt.mp (by simpa only [Real.norm_eq_abs] using hbound x hx)
  have hps : tsupport phi ⊆ Ioo (-a.1) a.1 := fun _ hx => hs (Or.inl (Or.inl hx))
  have hqs : tsupport psi ⊆ Ioo (-a.1) a.1 := fun _ hx => hs (Or.inl (Or.inr hx))
  have hcs : tsupport chi ⊆ Ioo (-a.1) a.1 := fun _ hx => hs (Or.inr hx)
  let u := ccmThetaSourceOfCompactRealProfile a phi hpc hps
  let v := ccmThetaSourceOfCompactRealProfile a psi hqc hqs
  let w := ccmThetaSourceOfCompactRealProfile a chi hcc hcs
  have huv : ccmWeilRealPolar a u.toCCMFormVector v.toCCMFormVector < 0 := by
    rw [ccmWeilRealPolar_compactReal_eq]
    exact h₁
  have huw : ccmWeilRealPolar a u.toCCMFormVector w.toCCMFormVector < 0 := by
    rw [ccmWeilRealPolar_compactReal_eq]
    exact h₂
  have hvw : 0 < ccmWeilRealPolar a v.toCCMFormVector w.toCCMFormVector := by
    rw [ccmWeilRealPolar_compactReal_eq]
    exact h₃
  let m := min (-ccmWeilRealPolar a u.toCCMFormVector v.toCCMFormVector)
    (min (-ccmWeilRealPolar a u.toCCMFormVector w.toCCMFormVector)
      (ccmWeilRealPolar a v.toCCMFormVector w.toCCMFormVector))
  have hm : 0 < m := lt_min (neg_pos.mpr huv) (lt_min (neg_pos.mpr huw) hvw)
  refine ⟨p, q, r, m, a, u, v, w, hpN, hp, hq, hpq, hr, hm, ?_, ?_, ?_, huv, huw, hvw, ?_⟩
  · rw [support_ccmThetaSourceOfCompactRealProfile]
    exact support_thetaTranslatedBumpGround r hr 0
  · rw [support_ccmThetaSourceOfCompactRealProfile]
    exact support_thetaTranslatedBumpGround r hr (Real.log p)
  · rw [support_ccmThetaSourceOfCompactRealProfile]
    exact support_thetaTranslatedBumpGround r hr (Real.log q)
  · exact ccmWeil_frustratedTriangle_lower a u.toCCMFormVector v.toCCMFormVector w.toCCMFormVector
      huv.le huw.le hvw.le

end RHTower
