import GaloisForLFunctions.RHTower.RoutePPrimitiveGammaJuliaStokesCubicTwoBranchContactThresholdClassification
import GaloisForLFunctions.HTGeometry.StokesEquivariantSpectrumIntegrality
import GaloisForLFunctions.HTGeometry.RootBlockMomentSelection

/-!
# Cubic Xi genuine two-sheet contact-seven wall

The abstract two-branch landing wall is sharpened by actual cyclic Puiseux continuation.  On a
two-sheet cover whose monodromy exchanges the sheets, a cubic completed-Xi landing cannot have
highest-difference numerator `6`: order-two equivariance would make that coefficient invariant,
contradicting its role as the highest sheet difference.  Thus every genuine landing has numerator
at least `7`.

The bound is sharp.  We construct an equivariant two-sheet coefficient spectrum supported at
exponent `7/2`; its unique monodromy orbit has contact numerator exactly `7`, and the completed-Xi
cubic unit landing fibre is nonempty.

No global meromorphic connection or arithmetic source-to-charge map is asserted.
-/

open GaloisForLFunctions
open GaloisForLFunctions.IrregularStokes
open GaloisForLFunctions.IrregularStokes.GlobalPuiseuxWitt

namespace RHTower

noncomputable section

/-- Regard a genuine two-sheet swap spectrum as one local Stokes orbit.  The theorem below requires
the spectrum's actual monodromy to exchange the two sheets, so this orbit is not an arbitrary
grouping. -/
noncomputable def routePPrimitiveGammaJuliaStokesGenuineTwoSheetSingleOrbitDatum
    {K : ℕ} (f : EquivariantFinitePuiseuxFamily 2 K 2) :
    PuiseuxOrbitCoareaDatum 1 2 K 2 where
  branches := f.toFinitePuiseuxFamily
  orbit := fun _ => 0
  orbit_surjective := by
    intro i
    exact ⟨0, Subsingleton.elim _ _⟩

/-- Genuine order-two continuation removes contact numerator `6` from the abstract landing
chamber.  Therefore every two-sheet swap-equivariant cubic landing starts at numerator `7`. -/
theorem routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetUnitLanding_contactNumerator_seven_le
    {K : ℕ} (f : EquivariantFinitePuiseuxFamily 2 K 2)
    (hmonodromy : f.monodromy 0 = 1)
    (x : routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      0 (fun _ : Fin 1 =>
        routePPrimitiveGammaJuliaStokesGenuineTwoSheetSingleOrbitDatum f)
        (fun (_ : Fin 1) _ => 1)) :
    7 ≤ f.contactNumerator 0 1 := by
  have hcontact :=
    (nonempty_routePPrimitiveGammaJuliaStokesCubicSphereUnitLandingFiber_twoBranchOneOrbit_iff_contactNumerator
      (fun _ : Fin 1 =>
        routePPrimitiveGammaJuliaStokesGenuineTwoSheetSingleOrbitDatum f)).mp ⟨x⟩
  simp only [routePPrimitiveGammaJuliaStokesGenuineTwoSheetSingleOrbitDatum] at hcontact
  by_contra hseven
  have hk : f.contactNumerator 0 1 = 6 := by omega
  let e : Fin (K + 1) :=
    ⟨f.contactNumerator 0 1, Nat.lt_succ_of_le (f.contactNumerator_le 0 1)⟩
  have hdiff : f.coeff 0 e ≠ f.coeff 1 e :=
    f.toFinitePuiseuxFamily.coeff_ne_at_contact (by omega)
  have hequiv := f.coeff_equivariant (0 : Fin 2) e
  rw [hmonodromy] at hequiv
  have hroot_inv_sq : f.root⁻¹ ^ (2 : ℕ) = 1 := by
    rw [inv_pow, f.root_primitive.pow_eq_one, inv_one]
  have hfactor : f.root⁻¹ ^ e.val = 1 := by
    have heval : e.val = 6 := by simp [e, hk]
    rw [heval]
    calc
      f.root⁻¹ ^ (6 : ℕ) = (f.root⁻¹ ^ (2 : ℕ)) ^ (3 : ℕ) := by ring
      _ = 1 := by rw [hroot_inv_sq]; norm_num
  rw [hfactor, one_mul] at hequiv
  exact hdiff hequiv.symm

private noncomputable def genuineTwoSheetSevenRoot : ℂ :=
  GaloisForLFunctions.HTGeometry.unitRoot 2

private noncomputable def genuineTwoSheetSevenRatio : ℂ :=
  genuineTwoSheetSevenRoot⁻¹ ^ (7 : ℕ)

private noncomputable def genuineTwoSheetSevenCoeff (i : Fin 2) (e : Fin 8) : ℂ :=
  if e.val = 7 then if i = 0 then 1 else genuineTwoSheetSevenRatio else 0

private theorem genuineTwoSheetSevenRoot_primitive :
    IsPrimitiveRoot genuineTwoSheetSevenRoot 2 := by
  exact GaloisForLFunctions.HTGeometry.unitRoot_isPrimitiveRoot (by norm_num)

private theorem genuineTwoSheetSevenRoot_inv_sq : genuineTwoSheetSevenRoot⁻¹ ^ (2 : ℕ) = 1 := by
  rw [inv_pow, genuineTwoSheetSevenRoot_primitive.pow_eq_one, inv_one]

private theorem genuineTwoSheetSevenRatio_sq : genuineTwoSheetSevenRatio ^ (2 : ℕ) = 1 := by
  rw [genuineTwoSheetSevenRatio]
  calc
    (genuineTwoSheetSevenRoot⁻¹ ^ (7 : ℕ)) ^ (2 : ℕ) =
        (genuineTwoSheetSevenRoot⁻¹ ^ (2 : ℕ)) ^ (7 : ℕ) := by ring
    _ = 1 := by rw [genuineTwoSheetSevenRoot_inv_sq]; norm_num

private theorem genuineTwoSheetSevenRatio_ne_one : genuineTwoSheetSevenRatio ≠ 1 := by
  have hroot_ne_one : genuineTwoSheetSevenRoot ≠ 1 := by
    intro hroot
    have hdvd :=
      (genuineTwoSheetSevenRoot_primitive.pow_eq_one_iff_dvd 1).mp (by simp [hroot])
    norm_num at hdvd
  have hinv_ne_one : genuineTwoSheetSevenRoot⁻¹ ≠ 1 := by
    intro hinv
    apply hroot_ne_one
    have h := congrArg Inv.inv hinv
    simpa using h
  intro hratio
  apply hinv_ne_one
  rw [genuineTwoSheetSevenRatio] at hratio
  calc
    genuineTwoSheetSevenRoot⁻¹ =
        (genuineTwoSheetSevenRoot⁻¹ ^ (2 : ℕ)) ^ (3 : ℕ) * genuineTwoSheetSevenRoot⁻¹ := by
      rw [genuineTwoSheetSevenRoot_inv_sq]
      simp
    _ = genuineTwoSheetSevenRoot⁻¹ ^ (7 : ℕ) := by ring
    _ = 1 := hratio

/-- Explicit genuine cyclic Puiseux spectrum supported at exponent `7/2`.  Its monodromy swaps the
two sheets, and its top coefficients form the primitive order-two orbit. -/
noncomputable def routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily :
    EquivariantFinitePuiseuxFamily 2 7 2 where
  coeff := genuineTwoSheetSevenCoeff
  coverDegree_pos := by norm_num
  constant_zero := by
    intro i
    simp [genuineTwoSheetSevenCoeff]
  coeff_injective := by
    intro i j h
    have htop := congrFun h (7 : Fin 8)
    fin_cases i <;> fin_cases j
    all_goals
      simp [genuineTwoSheetSevenCoeff, genuineTwoSheetSevenRatio_ne_one,
        Ne.symm genuineTwoSheetSevenRatio_ne_one] at htop ⊢
  monodromy := Equiv.swap 0 1
  monodromy_pow := by
    ext i
    fin_cases i <;> simp [pow_two]
  root := genuineTwoSheetSevenRoot
  root_primitive := genuineTwoSheetSevenRoot_primitive
  coeff_equivariant := by
    intro i e
    by_cases he : e.val = 7
    · have heq : e = (7 : Fin 8) := Fin.ext he
      subst e
      fin_cases i
      · simp [genuineTwoSheetSevenCoeff, genuineTwoSheetSevenRatio]
      · change (1 : ℂ) = genuineTwoSheetSevenRatio * genuineTwoSheetSevenRatio
        rw [← pow_two, genuineTwoSheetSevenRatio_sq]
    · simp [genuineTwoSheetSevenCoeff, he]

@[simp] theorem routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily_monodromy_zero :
    routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily.monodromy 0 = 1 := by
  simp [routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily]

/-- The explicit genuine spectrum attains the sharp integral contact numerator `7`. -/
theorem routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily_contactNumerator :
    routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily.contactNumerator 0 1 = 7 := by
  have hle :=
    routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily.contactNumerator_le 0 1
  have hdiff :
      routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily.coeff 0 (7 : Fin 8) ≠
        routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily.coeff 1
          (7 : Fin 8) := by
    change (1 : ℂ) ≠ genuineTwoSheetSevenRatio
    exact Ne.symm genuineTwoSheetSevenRatio_ne_one
  have hsup := Finset.le_sup (s := Finset.univ)
    (f := fun e =>
      if routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily.coeff 0 e =
          routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily.coeff 1 e
      then 0 else e.val)
    (Finset.mem_univ (7 : Fin 8))
  simp only [hdiff, if_false] at hsup
  have hge : 7 ≤
      routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily.contactNumerator 0 1 := by
    simpa [FinitePuiseuxFamily.contactNumerator] using hsup
  omega

/-- **Sharpness of the genuine contact-seven wall.**  The explicit swap-equivariant exponent
`7/2` spectrum carries a completed-Xi cubic unit landing. -/
theorem nonempty_routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenUnitLandingFiber :
    Nonempty (routePPrimitiveGammaJuliaStokesCubicMalgrangeLandingFiber
      0 (fun _ : Fin 1 =>
        routePPrimitiveGammaJuliaStokesGenuineTwoSheetSingleOrbitDatum
          routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily)
        (fun (_ : Fin 1) _ => 1)) := by
  apply
    (nonempty_routePPrimitiveGammaJuliaStokesCubicSphereUnitLandingFiber_twoBranchOneOrbit_iff_contactNumerator
      (fun _ : Fin 1 =>
        routePPrimitiveGammaJuliaStokesGenuineTwoSheetSingleOrbitDatum
          routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily)).2
  norm_num [routePPrimitiveGammaJuliaStokesGenuineTwoSheetSingleOrbitDatum,
    routePPrimitiveGammaJuliaStokesCubicGenuineTwoSheetSevenFamily_contactNumerator]

end

end RHTower
