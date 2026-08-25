import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCubicMicrolocalWittSignatureRigidity

/-!
# Cubic Xi two-branch contact-threshold classification

The first multibranch coefficient-generated irregular type is completely classifiable.  On a sphere
with one marked point, one Stokes orbit, and exactly two Puiseux branches, unit-Rees Witt value is
controlled by their mutual normalized highest-difference contact `c`:

`4 W = (5 - 2c) rank²`.

Consequently the negative completed-Xi cubic Malgrange residual lands if and only if `c > 5/2`.
Above that sharp wall an explicit real square-root charge lands, and every landing has the uniquely
forced rank magnitude.  Thus genuine multibranch contact is not only necessary after the
single-branch no-go: its first possible sector has an exact phase boundary.

No arithmetic source-to-charge map or meromorphic-connection existence statement is asserted.
-/

open GaloisForLFunctions
open GaloisForLFunctions.IrregularStokes
open GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt

namespace RHTower

noncomputable section

private theorem twoBranchOneOrbit_localWittForm_eq_contactCoefficient
    {K N : ℕ} (d : PuiseuxOrbitCoareaDatum 1 2 K N) (x : Fin 1 → ℝ) :
    localWittForm d x =
      (5 - 2 * (d.branches.contactNumerator 0 1 / (N : ℝ))) * x 0 ^ 2 := by
  have horbit : ∀ i : Fin 2, d.orbit i = 0 := fun i => Subsingleton.elim _ _
  have hsym : d.branches.contactNumerator 1 0 =
      d.branches.contactNumerator 0 1 :=
    d.branches.contactNumerator_symm 1 0
  have h00 : d.branches.canonicalCuts.contact 0 0 = 0 := by
    rw [d.branches.canonicalCuts_contact_eq]
    simp
  have h01 : d.branches.canonicalCuts.contact 0 1 =
      d.branches.contactNumerator 0 1 / (N : ℝ) :=
    d.branches.canonicalCuts_contact_eq 0 1
  have h10 : d.branches.canonicalCuts.contact 1 0 =
      d.branches.contactNumerator 0 1 / (N : ℝ) := by
    rw [d.branches.canonicalCuts_contact_eq, hsym]
  have h11 : d.branches.canonicalCuts.contact 1 1 = 0 := by
    rw [d.branches.canonicalCuts_contact_eq]
    simp
  rw [localWittForm_apply]
  simp [OrbitCoareaDatum.cartanQuadratic, OrbitCoareaDatum.terminalEnergy,
    OrbitCoareaDatum.physicalRank, OrbitCoareaDatum.contactPairing,
    OrbitCoareaDatum.liftCharge, PuiseuxOrbitCoareaDatum.toOrbitCoareaDatum,
    horbit]
  rw [h00, h01, h10, h11]
  ring

private theorem sphereOnePunctureTwoBranchOneOrbit_commonRank_eq_two_mul
    {K N : Fin 1 → ℕ}
    (d : LocalData 0 (fun _ => 1) (fun _ => 2) K N)
    (x : compatibleCharges d) :
    commonRankLinear d x = 2 * x.1 0 0 := by
  have horbit : ∀ i : Fin 2, (d 0).orbit i = 0 := fun i => Subsingleton.elim _ _
  simp [commonRankLinear_apply, localRankLinear_apply, OrbitCoareaDatum.physicalRank,
    OrbitCoareaDatum.liftCharge, PuiseuxOrbitCoareaDatum.toOrbitCoareaDatum, horbit]

/-- Exact unit-Rees contact law in the first multibranch sector.  All global and local terms reduce
to one rank square and the normalized mutual highest-difference contact. -/
theorem routePPrimitiveGammaJuliaStokesCubicSphereUnitWittForm_twoBranchOneOrbit_contactLaw
    {K N : Fin 1 → ℕ}
    (d : LocalData 0 (fun _ => 1) (fun _ => 2) K N)
    (x : compatibleCharges d) :
    4 * globalReesWittForm 0 d (fun _ _ => 1) x =
      (5 - 2 * ((d 0).branches.contactNumerator 0 1 / (N 0 : ℝ))) *
        commonRankLinear d x ^ 2 := by
  rw [globalReesWittForm_one, globalWittForm, QuadraticMap.add_apply,
    QuadraticMap.sum_apply, QuadraticMap.smul_apply, QuadraticMap.comp_apply,
    QuadraticMap.sq_apply]
  simp only [smul_eq_mul]
  simp_rw [QuadraticMap.comp_apply, localProjection_apply,
    twoBranchOneOrbit_localWittForm_eq_contactCoefficient]
  rw [Fin.sum_univ_one,
    sphereOnePunctureTwoBranchOneOrbit_commonRank_eq_two_mul]
  norm_num [fusionCoefficient]
  ring

/-- Every minimal two-branch cubic landing has exactly the rank magnitude dictated by excess
contact above the sharp `5/2` wall and the completed-Xi residual. -/
theorem routePPrimitiveGammaJuliaStokesCubicSphereUnitLanding_twoBranchOneOrbit_chargeMagnitude
    {K N : Fin 1 → ℕ}
    {d : LocalData 0 (fun _ => 1) (fun _ => 2) K N}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      0 d (fun _ _ => 1)) :
    (2 * ((d 0).branches.contactNumerator 0 1 / (N 0 : ℝ)) - 5) *
        commonRankLinear d x.1 ^ 2 =
      -4 * (normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4) := by
  have hlaw :=
    routePPrimitiveGammaJuliaStokesCubicSphereUnitWittForm_twoBranchOneOrbit_contactLaw
      d x.1
  rw [x.2] at hlaw
  linarith

/-- **Sharp minimal multibranch landing classification.**  A genus-zero, one-puncture,
one-orbit, two-branch coefficient system carries the negative completed-Xi cubic anomaly exactly
when its mutual normalized highest-difference contact exceeds `5/2`. -/
theorem nonempty_routePPrimitiveGammaJuliaStokesCubicSphereUnitLandingFiber_twoBranchOneOrbit_iff_contact
    {K N : Fin 1 → ℕ}
    (d : LocalData 0 (fun _ => 1) (fun _ => 2) K N) :
    Nonempty (routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      0 d (fun _ _ => 1)) ↔
      (5 : ℝ) / 2 < (d 0).branches.contactNumerator 0 1 / (N 0 : ℝ) := by
  constructor
  · rintro ⟨x⟩
    have hlaw :=
      routePPrimitiveGammaJuliaStokesCubicSphereUnitWittForm_twoBranchOneOrbit_contactLaw
        d x.1
    rw [x.2] at hlaw
    have htarget := normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg
    have hrank_ne :=
      routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber_commonRank_ne_zero
        (fun _ _ => zero_le_one) x
    have hrank_pos : 0 < commonRankLinear d x.1 ^ 2 := sq_pos_of_ne_zero hrank_ne
    nlinarith
  · intro hcontact
    let target : ℝ :=
      normalizedPrimeArchMoment 2 - normalizedPrimeArchMoment 0 ^ 3 / 4
    let contact : ℝ := (d 0).branches.contactNumerator 0 1 / (N 0 : ℝ)
    let u : ℝ := Real.sqrt ((-target) / (2 * contact - 5))
    let raw : GlobalCharge 0 (fun _ => 1) := fun _ _ => u
    have hraw : ∀ a,
        localRankLinear (d a) (raw a) = localRankLinear (d 0) (raw 0) := by
      intro a
      have ha : a = 0 := Subsingleton.elim _ _
      subst a
      rfl
    let y : compatibleCharges d := ⟨raw, hraw⟩
    have htarget : target < 0 := by
      exact normalizedPrimeArchMoment_two_sub_zero_cube_div_four_neg
    have hdenom : 0 < 2 * contact - 5 := by
      dsimp [contact]
      nlinarith
    have hquot : 0 ≤ (-target) / (2 * contact - 5) :=
      div_nonneg (neg_nonneg.mpr htarget.le) hdenom.le
    have hu_sq : u ^ 2 = (-target) / (2 * contact - 5) := by
      dsimp [u]
      exact Real.sq_sqrt hquot
    have hratio : (2 * contact - 5) * u ^ 2 = -target := by
      rw [hu_sq]
      field_simp [hdenom.ne']
    have hrank : commonRankLinear d y = 2 * u := by
      rw [sphereOnePunctureTwoBranchOneOrbit_commonRank_eq_two_mul]
    refine ⟨⟨y, ?_⟩⟩
    have hlaw :=
      routePPrimitiveGammaJuliaStokesCubicSphereUnitWittForm_twoBranchOneOrbit_contactLaw d y
    rw [hrank] at hlaw
    change globalReesWittForm 0 d (fun _ _ => 1) y = target
    change 4 * globalReesWittForm 0 d (fun _ _ => 1) y =
      (5 - 2 * contact) * (2 * u) ^ 2 at hlaw
    nlinarith

/-- Integral form of the sharp phase boundary: the doubled highest-difference numerator must exceed
five times the common cover degree, and this condition is also sufficient. -/
theorem nonempty_routePPrimitiveGammaJuliaStokesCubicSphereUnitLandingFiber_twoBranchOneOrbit_iff_contactNumerator
    {K N : Fin 1 → ℕ}
    (d : LocalData 0 (fun _ => 1) (fun _ => 2) K N) :
    Nonempty (routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      0 d (fun _ _ => 1)) ↔
      5 * N 0 < 2 * (d 0).branches.contactNumerator 0 1 := by
  rw [
    nonempty_routePPrimitiveGammaJuliaStokesCubicSphereUnitLandingFiber_twoBranchOneOrbit_iff_contact]
  have hN : (0 : ℝ) < N 0 := by
    exact_mod_cast (d 0).branches.coverDegree_pos
  constructor
  · intro h
    rw [lt_div_iff₀ hN] at h
    have hreal : (5 : ℝ) * N 0 < 2 * (d 0).branches.contactNumerator 0 1 := by
      nlinarith
    exact_mod_cast hreal
  · intro h
    have hreal : (5 : ℝ) * N 0 < 2 * (d 0).branches.contactNumerator 0 1 := by
      exact_mod_cast h
    rw [lt_div_iff₀ hN]
    nlinarith

/-- Any minimal two-branch sphere landing forces the declared exponent ceiling beyond the sharp
`5N/2` contact wall. -/
theorem routePPrimitiveGammaJuliaStokesCubicSphereUnitLanding_twoBranchOneOrbit_five_mul_cover_lt_two_mul_ceiling
    {K N : Fin 1 → ℕ}
    {d : LocalData 0 (fun _ => 1) (fun _ => 2) K N}
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      0 d (fun _ _ => 1)) :
    5 * N 0 < 2 * K 0 := by
  have hcontact :=
    (nonempty_routePPrimitiveGammaJuliaStokesCubicSphereUnitLandingFiber_twoBranchOneOrbit_iff_contactNumerator
      d).mp ⟨x⟩
  have hle := (d 0).branches.contactNumerator_le 0 1
  omega

end

end RHTower
