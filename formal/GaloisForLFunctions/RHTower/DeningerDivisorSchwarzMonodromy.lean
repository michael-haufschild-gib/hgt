import GaloisForLFunctions.RHTower.DeningerDivisorGaugeWardIdentity

/-!
# The Schwarz gauge and the canonical monodromy of the Deninger divisor flow

The displacement Ward identity exhibits the reflect gauge as the positivity-extremal point of the
anti-linear gauge orbit: cup diagonal identically `1`, commutation defect exactly the
critical-line displacement.  This file constructs the opposite extremal point and the composite
of the two.

* **The Schwarz gauge** `σ_S x = conj ∘ x ∘ S`, where `S` is complex conjugation lifted to the
  multiplicity-exact divisor copies (`xi_divisor_conj` supplies invariance of the divisor).  It
  commutes with Frobenius **unconditionally** — the equivariance-extremal gauge — and its cup
  diagonal at a copy is `1` exactly on the critical line and `0` off it: the Ward invisibility
  law is realised, not merely bounded, on this gauge.

* **The canonical monodromy** `D = σ_S ∘ σ_R`, a *linear* endomorphism sending `δ_ρ` to
  `δ_{1 - conj ρ}`.  Its Frobenius commutator is diagonal with entry exactly
  `1 - ρ - conj ρ = -2 (Re ρ - 1/2)` times the monodromy, so `[θ, D] = 0 ↔ RiemannHypothesis`:
  the Riemann hypothesis is the triviality of the interaction between the two canonical
  symmetries of the divisor.  Its cup diagonal vanishes identically — the total linear-blindness
  law of the Ward file is saturated by the canonical monodromy itself, because the divisor has no
  real point.

Everything is unconditional except where `RiemannHypothesis` is the explicit hypothesis or
conclusion.
-/

noncomputable section

open Complex

namespace RHTower

/-- Complex conjugation lifted to the multiplicity-exact divisor copy index, using invariance of
the xi divisor under conjugation. -/
def xiZeroCopyConjEquiv : XiZeroCopy ≃ XiZeroCopy :=
  Equiv.sigmaCongr xiZeroConjEquiv (fun ρ => Equiv.cast (by
    change Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) =
      Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) ((starRingEnd ℂ) (ρ : ℂ))))
    rw [xi_divisor_conj]))

@[simp]
theorem xiZeroCopyConjEquiv_apply_apply (q : XiZeroCopy) :
    xiZeroCopyConjEquiv (xiZeroCopyConjEquiv q) = q := by
  have hfst :
      (xiZeroCopyConjEquiv (xiZeroCopyConjEquiv q)).1 = q.1 := by
    apply Subtype.ext
    simp [xiZeroCopyConjEquiv, xiZeroConjEquiv, Equiv.sigmaCongr,
      Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft]
  apply Sigma.ext hfst
  apply (Fin.heq_ext_iff (congrArg (fun rho : XiDivisorSupport =>
    Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ))) hfst)).2
  simp [xiZeroCopyConjEquiv, xiZeroConjEquiv, Equiv.sigmaCongr,
    Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft]
  exact Fin.val_eq_val_of_heq (cast_heq _ q.2)

theorem xiZeroCopyConjEquiv_symm_apply (q : XiZeroCopy) :
    xiZeroCopyConjEquiv.symm q = xiZeroCopyConjEquiv q := by
  rw [Equiv.symm_apply_eq]
  exact (xiZeroCopyConjEquiv_apply_apply q).symm

/-- The Frobenius eigenvalue at a conjugated copy is the conjugated eigenvalue. -/
theorem deningerDivisorThetaEigen_conjEquiv (q : XiZeroCopy) :
    deningerDivisorThetaEigen (xiZeroCopyConjEquiv q) =
      (starRingEnd ℂ) (deningerDivisorThetaEigen q) := by
  change (xiZeroConjEquiv q.1 : ℂ) = (starRingEnd ℂ) (q.1 : ℂ)
  rfl

/-- The Schwarz gauge: coefficientwise conjugation transported along divisor conjugation. -/
def deningerDivisorSchwarzGauge :
    DeningerDivisorH1 →ₗ⋆[ℂ] DeningerDivisorH1 where
  toFun x :=
    Finsupp.equivMapDomain xiZeroCopyConjEquiv
      (Finsupp.mapRange (starRingEnd ℂ) (map_zero _) x)
  map_add' x y := by
    ext p
    simp [Finsupp.equivMapDomain_apply, Finsupp.mapRange_apply]
  map_smul' c x := by
    ext p
    simp [Finsupp.equivMapDomain_apply, Finsupp.mapRange_apply, smul_eq_mul]

@[simp]
theorem deningerDivisorSchwarzGauge_apply (x : DeningerDivisorH1) (p : XiZeroCopy) :
    deningerDivisorSchwarzGauge x p =
      (starRingEnd ℂ) (x (xiZeroCopyConjEquiv p)) := by
  change (Finsupp.equivMapDomain xiZeroCopyConjEquiv
    (Finsupp.mapRange (starRingEnd ℂ) (map_zero _) x)) p = _
  rw [Finsupp.equivMapDomain_apply, Finsupp.mapRange_apply,
    xiZeroCopyConjEquiv_symm_apply]

theorem deningerDivisorSchwarzGauge_single (r : XiZeroCopy) (c : ℂ) :
    deningerDivisorSchwarzGauge (Finsupp.single r c) =
      Finsupp.single (xiZeroCopyConjEquiv r) ((starRingEnd ℂ) c) := by
  change Finsupp.equivMapDomain xiZeroCopyConjEquiv
      (Finsupp.mapRange (starRingEnd ℂ) (map_zero _) (Finsupp.single r c)) = _
  rw [Finsupp.mapRange_single, Finsupp.equivMapDomain_single]

/-- **The Schwarz gauge commutes with Frobenius on basis vectors, unconditionally.**  The
eigenvalue at the conjugated copy is the conjugated eigenvalue, which is exactly what an
anti-linear map transports. -/
theorem deningerDivisorSchwarzGauge_comm_single (r : XiZeroCopy) (c : ℂ) :
    deningerDivisorTheta (deningerDivisorSchwarzGauge (Finsupp.single r c)) =
      deningerDivisorSchwarzGauge (deningerDivisorTheta (Finsupp.single r c)) := by
  rw [deningerDivisorSchwarzGauge_single, deningerDivisorTheta_single,
    deningerDivisorTheta_single, deningerDivisorSchwarzGauge_single, map_mul,
    deningerDivisorThetaEigen_conjEquiv]

/-- **The Schwarz gauge commutes with Frobenius, unconditionally.**  The equivariance-extremal
point of the gauge orbit exists with no hypothesis. -/
theorem deningerDivisorSchwarzGauge_comm (x : DeningerDivisorH1) :
    deningerDivisorTheta (deningerDivisorSchwarzGauge x) =
      deningerDivisorSchwarzGauge (deningerDivisorTheta x) := by
  induction x using Finsupp.induction with
  | zero => simp
  | single_add r c f _ _ ih =>
      rw [map_add, map_add, map_add, map_add, ih,
        deningerDivisorSchwarzGauge_comm_single]

/-- On the critical line the reflected copy and the conjugated copy coincide. -/
theorem xiZeroCopyReflectEquiv_eq_conjEquiv_of_re_eq_half (q : XiZeroCopy)
    (h : (deningerDivisorThetaEigen q).re = 1 / 2) :
    xiZeroCopyReflectEquiv q = xiZeroCopyConjEquiv q := by
  have hadd := Complex.add_conj (deningerDivisorThetaEigen q)
  rw [h] at hadd
  have hsum : deningerDivisorThetaEigen q +
      (starRingEnd ℂ) (deningerDivisorThetaEigen q) = 1 := by
    rw [hadd]
    norm_num
  have hq : deningerDivisorThetaEigen q = (q.1 : ℂ) := rfl
  rw [hq] at hsum
  have hval : (1 : ℂ) - (q.1 : ℂ) = (starRingEnd ℂ) (q.1 : ℂ) := by
    linear_combination -hsum
  have hfst : (xiZeroCopyReflectEquiv q).1 = (xiZeroCopyConjEquiv q).1 :=
    Subtype.ext hval
  apply Sigma.ext hfst
  apply (Fin.heq_ext_iff (congrArg (fun rho : XiDivisorSupport =>
    Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ))) hfst)).2
  simp [xiZeroCopyReflectEquiv, xiZeroCopyConjEquiv, xiZeroReflectEquiv,
    xiZeroConjEquiv, Equiv.sigmaCongr, Equiv.sigmaCongrRight,
    Equiv.sigmaCongrLeft]
  exact (Fin.val_eq_val_of_heq (cast_heq _ q.2)).trans
    (Fin.val_eq_val_of_heq (cast_heq _ q.2)).symm

/-- On the critical line the Schwarz gauge has cup diagonal `1`. -/
theorem deningerDivisorSchwarzGauge_diag_of_re_eq_half (q : XiZeroCopy)
    (h : (deningerDivisorThetaEigen q).re = 1 / 2) :
    deningerDivisorCupTrace (Finsupp.single q 1)
      (deningerDivisorSchwarzGauge (Finsupp.single q 1)) = 1 := by
  rw [deningerDivisorSchwarzGauge_single, map_one,
    deningerDivisorCupTrace_single,
    if_pos (xiZeroCopyReflectEquiv_eq_conjEquiv_of_re_eq_half q h), one_mul]

/-- Off the critical line the Schwarz gauge has cup diagonal `0`: the Ward invisibility law is
realised on the equivariance-extremal gauge. -/
theorem deningerDivisorSchwarzGauge_diag_of_offline (q : XiZeroCopy)
    (h : (deningerDivisorThetaEigen q).re ≠ 1 / 2) :
    deningerDivisorCupTrace (Finsupp.single q 1)
      (deningerDivisorSchwarzGauge (Finsupp.single q 1)) = 0 :=
  deningerDivisor_antilinearGauge_diag_eq_zero_of_offline
    deningerDivisorSchwarzGauge q h
    (deningerDivisorSchwarzGauge_comm_single q 1)

/-- The cup diagonal of the Schwarz gauge detects exactly the critical line. -/
theorem deningerDivisorSchwarzGauge_diag_ne_zero_iff (q : XiZeroCopy) :
    deningerDivisorCupTrace (Finsupp.single q 1)
        (deningerDivisorSchwarzGauge (Finsupp.single q 1)) ≠ 0 ↔
      (deningerDivisorThetaEigen q).re = 1 / 2 := by
  constructor
  · intro hne
    by_contra hoff
    exact hne (deningerDivisorSchwarzGauge_diag_of_offline q hoff)
  · intro h
    rw [deningerDivisorSchwarzGauge_diag_of_re_eq_half q h]
    exact one_ne_zero

/-- The canonical monodromy `D = σ_S ∘ σ_R`: the linear composite of the two canonical
anti-linear symmetries, sending `δ_ρ` to `δ_{1 - conj ρ}`. -/
def deningerDivisorMonodromy : Module.End ℂ DeningerDivisorH1 where
  toFun x := deningerDivisorSchwarzGauge (deningerDivisorReflectGauge x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' c x := by
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, RingHom.id_apply,
      Complex.conj_conj]

theorem deningerDivisorMonodromy_single (r : XiZeroCopy) (c : ℂ) :
    deningerDivisorMonodromy (Finsupp.single r c) =
      Finsupp.single (xiZeroCopyConjEquiv (xiZeroCopyReflectEquiv r)) c := by
  change deningerDivisorSchwarzGauge
    (deningerDivisorReflectGauge (Finsupp.single r c)) = _
  rw [deningerDivisorReflectGauge_single, deningerDivisorSchwarzGauge_single,
    Complex.conj_conj]

/-- The Frobenius eigenvalue at the monodromy image is `1 - conj ρ`. -/
theorem deningerDivisorThetaEigen_monodromy (r : XiZeroCopy) :
    deningerDivisorThetaEigen (xiZeroCopyConjEquiv (xiZeroCopyReflectEquiv r)) =
      1 - (starRingEnd ℂ) (deningerDivisorThetaEigen r) := by
  rw [deningerDivisorThetaEigen_conjEquiv]
  have h := deningerDivisorThetaEigen_add_reflect r
  have hR : deningerDivisorThetaEigen (xiZeroCopyReflectEquiv r) =
      1 - deningerDivisorThetaEigen r := by
    linear_combination h
  rw [hR, map_sub, map_one]

/-- **Exact Frobenius commutator of the canonical monodromy**: diagonal, with entry exactly the
critical-line displacement `1 - ρ - conj ρ = -2 (Re ρ - 1/2)`. -/
theorem deningerDivisorMonodromy_defect (r : XiZeroCopy) (c : ℂ) :
    deningerDivisorTheta (deningerDivisorMonodromy (Finsupp.single r c)) -
        deningerDivisorMonodromy (deningerDivisorTheta (Finsupp.single r c)) =
      Finsupp.single (xiZeroCopyConjEquiv (xiZeroCopyReflectEquiv r))
        (((1 : ℂ) - (starRingEnd ℂ) (deningerDivisorThetaEigen r) -
            deningerDivisorThetaEigen r) * c) := by
  rw [deningerDivisorMonodromy_single, deningerDivisorTheta_single,
    deningerDivisorTheta_single, deningerDivisorMonodromy_single,
    deningerDivisorThetaEigen_monodromy, ← Finsupp.single_sub]
  congr 1
  ring

/-- Under RH the canonical monodromy commutes with Frobenius. -/
theorem deningerDivisorMonodromy_comm_of_riemannHypothesis
    (hRH : RiemannHypothesis) (x : DeningerDivisorH1) :
    deningerDivisorTheta (deningerDivisorMonodromy x) =
      deningerDivisorMonodromy (deningerDivisorTheta x) := by
  induction x using Finsupp.induction with
  | zero => simp
  | single_add r c f _ _ ih =>
      rw [map_add, map_add, map_add, map_add, ih]
      congr 1
      have hre : (deningerDivisorThetaEigen r).re = 1 / 2 :=
        xi_divisor_support_re_eq_half_of_rh hRH r.1
      have hadd := Complex.add_conj (deningerDivisorThetaEigen r)
      rw [hre] at hadd
      have hfactor : (1 : ℂ) -
          (starRingEnd ℂ) (deningerDivisorThetaEigen r) -
            deningerDivisorThetaEigen r = 0 := by
        have hsum : deningerDivisorThetaEigen r +
            (starRingEnd ℂ) (deningerDivisorThetaEigen r) = 1 := by
          rw [hadd]
          norm_num
        linear_combination -hsum
      have hdefect := deningerDivisorMonodromy_defect r c
      rw [hfactor, zero_mul, Finsupp.single_zero] at hdefect
      exact sub_eq_zero.mp hdefect

/-- **RH is the triviality of the canonical monodromy's interaction with Frobenius**:
`[θ, D] = 0 ↔ RiemannHypothesis`. -/
theorem deningerDivisorMonodromy_comm_iff_riemannHypothesis :
    (∀ x : DeningerDivisorH1,
      deningerDivisorTheta (deningerDivisorMonodromy x) =
        deningerDivisorMonodromy (deningerDivisorTheta x)) ↔
      RiemannHypothesis := by
  constructor
  · intro hcomm
    apply riemannHypothesis_of_forall_deningerDivisorThetaEigen_re_eq_half
    intro q
    have hdefect := deningerDivisorMonodromy_defect q 1
    rw [sub_eq_zero.mpr (hcomm (Finsupp.single q 1))] at hdefect
    have hfactor : (1 : ℂ) -
        (starRingEnd ℂ) (deningerDivisorThetaEigen q) -
          deningerDivisorThetaEigen q = 0 := by
      have happ := congrArg
        (fun y : DeningerDivisorH1 =>
          y (xiZeroCopyConjEquiv (xiZeroCopyReflectEquiv q))) hdefect
      simpa using happ.symm
    have hre := congrArg Complex.re hfactor
    simp only [sub_re, one_re, conj_re, zero_re] at hre
    linarith
  · exact deningerDivisorMonodromy_comm_of_riemannHypothesis

/-- **The canonical monodromy saturates the total linear-blindness law**: its cup diagonal
vanishes identically, because the xi divisor has no real point. -/
theorem deningerDivisorMonodromy_diag_eq_zero (q : XiZeroCopy) :
    deningerDivisorCupTrace (Finsupp.single q 1)
      (deningerDivisorMonodromy (Finsupp.single q 1)) = 0 := by
  rw [deningerDivisorMonodromy_single, deningerDivisorCupTrace_single, if_neg]
  intro h
  have hval := congrArg (fun p : XiZeroCopy => ((p.1 : ℂ)).im) h
  have him : ((xiZeroCopyReflectEquiv q).1 : ℂ).im = 0 := by
    have hconj : ((xiZeroCopyConjEquiv (xiZeroCopyReflectEquiv q)).1 : ℂ) =
        (starRingEnd ℂ) (((xiZeroCopyReflectEquiv q).1 : ℂ)) := rfl
    simp only [hconj, conj_im] at hval
    linarith
  exact xi_divisor_support_im_ne_zero (xiZeroCopyReflectEquiv q).1 him

end RHTower
