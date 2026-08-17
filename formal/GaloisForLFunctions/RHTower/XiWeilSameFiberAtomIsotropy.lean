import GaloisForLFunctions.RHTower.CCMCliffordWeilProduct

/-!
# Same-fibre Xi atoms are isotropic off the critical-reflection fixed locus

The unconditional CCM/Weil Hilbert form pairs one Xi coordinate with its critical-line-reflected
coordinate.  Consequently a packet supported on only one non-fixed fibre is isotropic.  Nonzero
positive energy appears only after adjoining the reflected fibre, where the resulting packet is
reflection-even and its Weil square is its Hilbert norm square.

This is a sharp obstruction to deriving same-fibre fixed-star descent from the existing conformal
Krein law: the form supplies cross-fibre covariance, not a same-fibre metric identification.
-/

open Complex

namespace RHTower

noncomputable section

private abbrev XiWeilCarrier := lp (fun _ : XiZeroCopy => ℂ) 2

/-- One multiplicity-exact coordinate atom in the Xi Weil carrier. -/
def xiWeilCoordinateAtom (q : XiZeroCopy) (a : ℂ) : XiWeilCarrier :=
  lp.single 2 q a

@[simp]
theorem xiWeilCoordinateAtom_apply
    (q r : XiZeroCopy) (a : ℂ) :
    xiWeilCoordinateAtom q a r = if r = q then a else 0 := by
  classical
  rw [xiWeilCoordinateAtom, lp.single_apply]
  by_cases h : r = q
  · subst r
    simp
  · simp [h]

/-- Critical-line reflection sends a coordinate atom to the reflected coordinate. -/
theorem xiWeilLineConjLinearIsometry_coordinateAtom
    (q : XiZeroCopy) (a : ℂ) :
    xiWeilLineConjLinearIsometry (xiWeilCoordinateAtom q a) =
      xiWeilCoordinateAtom (xiZeroCopyLineConjEquiv q) a := by
  classical
  apply Subtype.ext
  funext r
  rw [xiWeilLineConjLinearIsometry_apply, xiWeilLineConjLp_apply]
  simp only [xiWeilCoordinateAtom_apply]
  by_cases h : r = xiZeroCopyLineConjEquiv q
  · subst r
    rw [DeningerMeyerGaussianGreen.xiZeroCopyLineConjEquiv_apply_apply]
    simp
  · have h' : xiZeroCopyLineConjEquiv r ≠ q := by
      intro hr
      apply h
      have := congrArg xiZeroCopyLineConjEquiv hr
      simpa [DeningerMeyerGaussianGreen.xiZeroCopyLineConjEquiv_apply_apply] using this
    simp [h, h']

/-- A single non-fixed reflection coordinate is isotropic for the unconditional Xi Weil form. -/
theorem xiWeilCliffordPairing_coordinateAtom_eq_zero_of_not_fixed
    (q : XiZeroCopy) (a : ℂ)
    (hq : xiZeroCopyLineConjEquiv q ≠ q) :
    xiWeilCliffordPairing (xiWeilCoordinateAtom q a)
      (xiWeilCoordinateAtom q a) = 0 := by
  classical
  rw [xiWeilCliffordPairing,
    xiWeilLineConjLinearIsometry_coordinateAtom]
  change inner ℂ
      (lp.single (E := fun _ : XiZeroCopy => ℂ) 2
        (xiZeroCopyLineConjEquiv q) a)
      (lp.single (E := fun _ : XiZeroCopy => ℂ) 2 q a) = 0
  rw [lp.inner_single_left,
    lp.single_apply_ne (E := fun _ : XiZeroCopy => ℂ) 2 q a hq]
  simp

/-- Adjoining the reflected coordinate turns the same atom into the positive reflection-even
packet; its Weil square is exactly its Hilbert norm square. -/
theorem xiWeilCliffordPairing_coordinateReflectionPair_eq_normSq
    (q : XiZeroCopy) (a : ℂ) :
    let v := xiWeilCoordinateAtom q a +
      xiWeilCoordinateAtom (xiZeroCopyLineConjEquiv q) a
    xiWeilCliffordPairing v v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  dsimp only
  have hfix : xiWeilLineConjLinearIsometry
      (xiWeilCoordinateAtom q a +
        xiWeilCoordinateAtom (xiZeroCopyLineConjEquiv q) a) =
      xiWeilCoordinateAtom q a +
        xiWeilCoordinateAtom (xiZeroCopyLineConjEquiv q) a := by
    rw [map_add, xiWeilLineConjLinearIsometry_coordinateAtom,
      xiWeilLineConjLinearIsometry_coordinateAtom,
      DeningerMeyerGaussianGreen.xiZeroCopyLineConjEquiv_apply_apply]
    abel
  rw [xiWeilCliffordPairing, hfix, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- A unit coordinate atom has nonzero same-fibre Weil square exactly on the fixed locus. -/
theorem xiWeilCliffordPairing_coordinateAtom_one_eq_one_iff
    (q : XiZeroCopy) :
    xiWeilCliffordPairing (xiWeilCoordinateAtom q 1)
      (xiWeilCoordinateAtom q 1) = 1 ↔
      xiZeroCopyLineConjEquiv q = q := by
  constructor
  · intro hpair
    by_contra hnot
    rw [xiWeilCliffordPairing_coordinateAtom_eq_zero_of_not_fixed q 1 hnot] at hpair
    norm_num at hpair
  · intro hfix
    rw [xiWeilCliffordPairing,
      xiWeilLineConjLinearIsometry_coordinateAtom, hfix,
      inner_self_eq_norm_sq_to_K, xiWeilCoordinateAtom,
      lp.norm_single (E := fun _ : XiZeroCopy => ℂ)
        (p := 2) (by norm_num) q (1 : ℂ)]
    norm_num

/-- Copy-level critical-line reflection fixes an atom exactly on the critical line. -/
theorem xiZeroCopyLineConjEquiv_eq_self_iff_re_eq_half
    (q : XiZeroCopy) :
    xiZeroCopyLineConjEquiv q = q ↔ (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hfix
    have hfst := congrArg (fun r : XiZeroCopy => (r.1 : ℂ)) hfix
    change 1 - (starRingEnd ℂ) (q.1 : ℂ) = (q.1 : ℂ) at hfst
    have hre := congrArg Complex.re hfst
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re] at hre
    linarith
  · intro hre
    have hfst : (xiZeroCopyLineConjEquiv q).1 = q.1 := by
      apply Subtype.ext
      change 1 - (starRingEnd ℂ) (q.1 : ℂ) = (q.1 : ℂ)
      apply Complex.ext
      · simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
        linarith
      · simp
    apply Sigma.ext hfst
    apply (Fin.heq_ext_iff (congrArg (fun rho : XiDivisorSupport =>
      Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ))) hfst)).2
    simp [xiZeroCopyLineConjEquiv, xiZeroCopyConjEquiv,
      xiZeroCopyReflectEquiv, xiZeroConjEquiv, xiZeroReflectEquiv,
      Equiv.sigmaCongr, Equiv.sigmaCongrRight, Equiv.sigmaCongrLeft]
    exact Fin.val_eq_val_of_heq (cast_heq _ q.2)

/-- Exact same-fibre classifier: a unit Xi atom has unit Weil square precisely on the critical
line.  Off the line the same atom is isotropic, while its reflected two-fibre completion is
positive. -/
theorem xiWeilCliffordPairing_coordinateAtom_one_eq_one_iff_re_eq_half
    (q : XiZeroCopy) :
    xiWeilCliffordPairing (xiWeilCoordinateAtom q 1)
      (xiWeilCoordinateAtom q 1) = 1 ↔ (q.1 : ℂ).re = 1 / 2 := by
  rw [xiWeilCliffordPairing_coordinateAtom_one_eq_one_iff,
    xiZeroCopyLineConjEquiv_eq_self_iff_re_eq_half]

end

end RHTower
