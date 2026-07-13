import GaloisForLFunctions.RHTower.XiHedenmalmJordanMatrix
import GaloisForLFunctions.RHTower.RHLadderHedenmalmSimplicityCollision

/-!
# Normal local Hedenmalm blocks collide with a positive RH-ladder rung

The canonical local Hedenmalm matrix at an Xi divisor point is a single Jordan block.  Requiring
that block to commute with its conjugate transpose removes only the nilpotent divided-chain part:
it is equivalent to simplicity of that divisor point and imposes no reality condition on its
spectral value.  Thus global local normality is strictly weaker than the existing Hermitian
criterion, which encodes both RH and simplicity.

Combining this orientation-free simplicity constraint with any positive RH-ladder rung gives a
cross-route collision: a hypothetical right-half zero would have both order one and even order.
-/

open Complex

noncomputable section

namespace RHTower

/-- A local Hedenmalm Jordan block is normal when it commutes with its conjugate transpose. -/
def XiLocalJordanNormal (rho : XiDivisorSupport) : Prop :=
  Commute (xiLocalJordanMatrix rho) (xiLocalJordanMatrix rho).conjTranspose

/-- The divisor multiplicity used as the local Jordan-block dimension is exactly the natural
analytic order of `xi` at that support point. -/
theorem xiSupportMultiplicity_eq_analyticOrderAt_toNat (rho : XiDivisorSupport) :
    xiSupportMultiplicity rho = (analyticOrderAt xi (rho : ℂ)).toNat := by
  rw [xiSupportMultiplicity,
    MeromorphicOn.divisor_apply xi_analyticOnNhd_univ.meromorphicOn
      (Set.mem_univ (rho : ℂ)),
    (xi_analyticOnNhd_univ (rho : ℂ) (Set.mem_univ _)).meromorphicOrderAt_eq]
  have hcoe : ((((analyticOrderAt xi (rho : ℂ)).toNat : ℕ) : ℕ∞)) =
      analyticOrderAt xi (rho : ℂ) :=
    ENat.coe_toNat (xi_orderAt_ne_top (rho : ℂ))
  rw [← hcoe]
  simp

/-- A canonical local Hedenmalm Jordan block is normal exactly when the corresponding Xi divisor
point is simple.  Unlike Hermiticity, normality places no reality condition on the centered
spectral point. -/
theorem xiLocalJordanNormal_iff_multiplicity_one (rho : XiDivisorSupport) :
    XiLocalJordanNormal rho ↔ xiSupportMultiplicity rho = 1 := by
  constructor
  · intro hnormal
    by_contra hne
    have hm2 : 2 ≤ xiSupportMultiplicity rho := by
      have hmpos := xiSupportMultiplicity_pos rho
      omega
    let i0 : Fin (xiSupportMultiplicity rho) := ⟨0, by omega⟩
    let i1 : Fin (xiSupportMultiplicity rho) := ⟨1, by omega⟩
    have hi01 : i0 ≠ i1 := by
      intro heq
      have hval := congrArg Fin.val heq
      simp [i0, i1] at hval
    have hleft :
        (xiLocalJordanMatrix rho * (xiLocalJordanMatrix rho).conjTranspose) i0 i0 =
          xiSpectralPointSupport rho *
              (starRingEnd ℂ) (xiSpectralPointSupport rho) + 1 := by
      rw [Matrix.mul_apply]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i1)]
      have hi0mem : i0 ∈ Finset.univ.erase i1 :=
        Finset.mem_erase.mpr ⟨hi01, Finset.mem_univ _⟩
      rw [Finset.sum_eq_single_of_mem i0 hi0mem]
      · simp [xiLocalJordanMatrix, i0, i1, hi01]
      · intro b hb hb0
        have hb1 : b ≠ i1 := (Finset.mem_erase.mp hb).1
        have hbval1 : b.val ≠ 1 := by
          intro heq
          apply hb1
          apply Fin.ext
          simpa [i1] using heq
        simp [xiLocalJordanMatrix, i0, hb0.symm, hbval1.symm]
    have hright :
        ((xiLocalJordanMatrix rho).conjTranspose * xiLocalJordanMatrix rho) i0 i0 =
          (starRingEnd ℂ) (xiSpectralPointSupport rho) *
            xiSpectralPointSupport rho := by
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single i0]
      · simp [xiLocalJordanMatrix, i0]
      · intro b _hb hb0
        simp [xiLocalJordanMatrix, i0, hb0]
      · simp
    have h00 := congrFun (congrFun hnormal.eq i0) i0
    rw [hleft, hright] at h00
    rw [mul_comm (xiSpectralPointSupport rho)
      ((starRingEnd ℂ) (xiSpectralPointSupport rho))] at h00
    norm_num at h00
  · intro hm
    haveI : Subsingleton (Fin (xiSupportMultiplicity rho)) := by
      rw [hm]
      infer_instance
    apply Commute.eq
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    rw [Fintype.sum_eq_single i (fun x hx =>
          (hx (Subsingleton.elim x i)).elim),
        Fintype.sum_eq_single i (fun x hx =>
          (hx (Subsingleton.elim x i)).elim)]
    simp [xiLocalJordanMatrix, mul_comm]

/-- Every canonical local Hedenmalm block is normal exactly when all centered Xi zeros are simple.
This is the orientation-free part of the existing Hermitian local-block criterion. -/
theorem all_xiLocalJordanNormal_iff_simple :
    (∀ rho : XiDivisorSupport, XiLocalJordanNormal rho) ↔ XiZerosSimple := by
  constructor
  · intro hall alpha halpha
    obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy alpha).mp halpha
    have hm : xiSupportMultiplicity q.1 = 1 :=
      (xiLocalJordanNormal_iff_multiplicity_one q.1).mp (hall q.1)
    have hvalue : xiThetaEigenFourier (xiSpectralPointSupport q.1)
        (xiSpectralPointSupport q.1) ≠ 0 :=
      (xiThetaEigenFourier_self_ne_zero_iff_multiplicity_one q.1).mpr hm
    have hderiv : deriv XiC (xiSpectralPointSupport q.1) ≠ 0 := by
      intro hzero
      apply hvalue
      rw [xiThetaEigenFourier_self, hzero, mul_zero]
    have hsupp : xiSpectralPointSupport q.1 = alpha := by
      simpa only [xiSpectralPoint_eq_support] using hq
    simpa only [hsupp] using hderiv
  · intro hsimple rho
    apply (xiLocalJordanNormal_iff_multiplicity_one rho).mpr
    exact xiDivisorMultiplicity_eq_one_of_simple hsimple rho

/-- Normality only at the existing right-half Xi divisor points.  This condition allows
off-critical simple zeros and therefore does not itself assert RH. -/
def XiRightHalfLocalJordanNormal : Prop :=
  ∀ rho : XiDivisorSupport, (rho : ℂ) ∈ rightHalf → XiLocalJordanNormal rho

/-- **Weak right-half Jordan-normality--ladder collision.**  A positive ladder rung makes every
hypothetical right-half Xi order even, while local normality at that same point makes its order
one.  No simplicity condition on critical-line or left-half zeros is needed. -/
theorem riemannHypothesis_of_rhLadder_of_rightHalfLocalJordanNormal
    {k : ℕ} (hk : 1 ≤ k) (hladder : RHLadder k)
    (hnormal : XiRightHalfLocalJordanNormal) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  have hfirst : RHLadder 1 := rhLadder_imp_one hk hladder
  have heven : Even (analyticOrderAt xi rho).toNat :=
    rhLadder_one_iff_even_order.mp hfirst rho hrho hzero
  let support : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hnormalSupport : XiLocalJordanNormal support := by
    apply hnormal support
    simpa only [support] using hrho
  have hm : xiSupportMultiplicity support = 1 :=
    (xiLocalJordanNormal_iff_multiplicity_one support).mp hnormalSupport
  have horder : (analyticOrderAt xi rho).toNat = 1 := by
    rw [← xiSupportMultiplicity_eq_analyticOrderAt_toNat support]
    exact hm
  rw [horder] at heven
  obtain ⟨n, hn⟩ := heven
  omega

/-- The first ladder rung and right-half local normality are already sufficient. -/
theorem riemannHypothesis_of_rhLadder_one_of_rightHalfLocalJordanNormal
    (hladder : RHLadder 1) (hnormal : XiRightHalfLocalJordanNormal) :
    RiemannHypothesis :=
  riemannHypothesis_of_rhLadder_of_rightHalfLocalJordanNormal le_rfl hladder hnormal

/-- **Jordan-normality--ladder collision.**  Global normality of the local Hedenmalm divided-chain
blocks supplies Xi simplicity.  Any positive RH-ladder rung supplies even order at a hypothetical
right-half zero, so the two constraints force RH. -/
theorem riemannHypothesis_of_rhLadder_of_all_xiLocalJordanNormal
    {k : ℕ} (hk : 1 ≤ k) (hladder : RHLadder k)
    (hnormal : ∀ rho : XiDivisorSupport, XiLocalJordanNormal rho) :
    RiemannHypothesis :=
  riemannHypothesis_of_rhLadder_of_xiZerosSimple hk hladder
    (all_xiLocalJordanNormal_iff_simple.mp hnormal)

/-- The first ladder rung already suffices once every local Hedenmalm block is normal. -/
theorem riemannHypothesis_of_rhLadder_one_of_all_xiLocalJordanNormal
    (hladder : RHLadder 1)
    (hnormal : ∀ rho : XiDivisorSupport, XiLocalJordanNormal rho) :
    RiemannHypothesis :=
  riemannHypothesis_of_rhLadder_of_all_xiLocalJordanNormal le_rfl hladder hnormal

end RHTower
