import GaloisForLFunctions.HTGeometry.HLSTheorem
import GaloisForLFunctions.HTGeometry.HLSPhysicalAssumptions

/-!
# The Lorentz-scalar odd sector and spin-statistics

The algebraic Haag--Łopuszański--Sohnius classification leaves one sector besides the Weyl
supercharges: Lorentz scalars in the odd part.  This module proves the two halves of the
argument that removes it in a physical theory.

* `act_poincare_zero_on_scalar`: an odd Lorentz scalar commutes with the **entire** Poincaré
  algebra — both the Lorentz generators and the translations.  Hence it maps a one-particle
  state to one-particle states of the same mass and the same spin.
* `hls_spin_statistics_forbids_statistics_flip`: no statistics-reversing map between
  one-particle labels can preserve the spin, because `HLSOneParticleData` ties statistics to
  the parity of twice the spin.

Together they are exactly the Haag--Łopuszański--Sohnius exclusion of scalar supercharges.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Matrix

theorem hlsSl2_eq_coords (x : HLSSl2) :
    x = x 0 • hlsSl2E + x 1 • hlsSl2F + x 2 • hlsSl2H := by
  funext i
  fin_cases i <;> simp [hlsSl2E, hlsSl2F, hlsSl2H]

@[simp] theorem hlsLorL_add (x y : HLSSl2) {B : Type*} [LieRing B] [LieAlgebra ℂ B] :
    (hlsLorL (x + y) : HLSEven B) = hlsLorL x + hlsLorL y := by
  simp [hlsLorL, Prod.ext_iff]

@[simp] theorem hlsLorR_add (x y : HLSSl2) {B : Type*} [LieRing B] [LieAlgebra ℂ B] :
    (hlsLorR (x + y) : HLSEven B) = hlsLorR x + hlsLorR y := by
  simp [hlsLorR, Prod.ext_iff]

namespace HLSGradedSymmetry

variable {B : Type*} [LieRing B] [LieAlgebra ℂ B]
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (S : HLSGradedSymmetry B V)

theorem eL_zero_on_wt_scalar {v : V} (hv : v ∈ S.wt 0 0) :
    S.act (hlsLorL hlsSl2E) v = 0 :=
  S.eL_zero_of_bot hv (S.wt_eq_bot (by norm_num))

theorem fL_zero_on_wt_scalar {v : V} (hv : v ∈ S.wt 0 0) :
    S.act (hlsLorL hlsSl2F) v = 0 :=
  S.fL_zero_of_bot hv (S.wt_eq_bot (by norm_num))

theorem eR_zero_on_wt_scalar {v : V} (hv : v ∈ S.wt 0 0) :
    S.act (hlsLorR hlsSl2E) v = 0 :=
  S.eR_zero_of_bot hv (S.wt_eq_bot (by norm_num))

theorem fR_zero_on_wt_scalar {v : V} (hv : v ∈ S.wt 0 0) :
    S.act (hlsLorR hlsSl2F) v = 0 :=
  S.fR_zero_of_bot hv (S.wt_eq_bot (by norm_num))

/-- Every undotted Lorentz generator annihilates the odd Lorentz-scalar sector. -/
theorem act_lorL_zero_on_scalar {v : V} (hv : v ∈ S.wt 0 0) (x : HLSSl2) :
    S.act (hlsLorL x) v = 0 := by
  conv_lhs => rw [hlsSl2_eq_coords x]
  rw [hlsLorL_add, hlsLorL_add, hlsLorL_smul, hlsLorL_smul, hlsLorL_smul]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    S.eL_zero_on_wt_scalar hv, S.fL_zero_on_wt_scalar hv,
    show S.act (hlsLorL hlsSl2H) v = 0 from S.hL_zero_on_wt_scalar hv, smul_zero, add_zero]

/-- Every dotted Lorentz generator annihilates the odd Lorentz-scalar sector. -/
theorem act_lorR_zero_on_scalar {v : V} (hv : v ∈ S.wt 0 0) (x : HLSSl2) :
    S.act (hlsLorR x) v = 0 := by
  conv_lhs => rw [hlsSl2_eq_coords x]
  rw [hlsLorR_add, hlsLorR_add, hlsLorR_smul, hlsLorR_smul, hlsLorR_smul]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    S.eR_zero_on_wt_scalar hv, S.fR_zero_on_wt_scalar hv,
    show S.act (hlsLorR hlsSl2H) v = 0 from S.hR_zero_on_wt_scalar hv, smul_zero, add_zero]

variable [FiniteDimensional ℂ V]

/-- **An odd Lorentz scalar commutes with the whole Poincaré algebra.**  It is annihilated by
every Lorentz generator and by every translation, so as an operator on states it preserves
mass and spin while reversing statistics. -/
theorem act_poincare_zero_on_scalar {v : V} (hv : v ∈ S.wt 0 0)
    (x y : HLSSl2) (P : Matrix (Fin 2) (Fin 2) ℂ) :
    S.act (hlsLorL x) v = 0 ∧ S.act (hlsLorR y) v = 0 ∧ S.act (hlsMom P) v = 0 :=
  ⟨S.act_lorL_zero_on_scalar hv x, S.act_lorR_zero_on_scalar hv y, S.act_mom_scalar hv P⟩

end HLSGradedSymmetry

/-- **Spin-statistics forbids a statistics-reversing spin-preserving transition.**
If a symmetry connects one-particle labels `a` and `b` of equal twice-spin but opposite
statistics, the spin-statistics correspondence recorded in `HLSOneParticleData` fails.  This is
the Haag--Łopuszański--Sohnius reason why an odd Lorentz scalar cannot act nontrivially on the
one-particle states of a physical theory. -/
theorem hls_spin_statistics_forbids_statistics_flip {A : Type*} {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (P : HLSOneParticleData A E) {a b : A}
    (hspin : P.spinTwice a = P.spinTwice b)
    (hflip : P.fermionic a ↔ ¬ P.fermionic b) : False := by
  have ha := P.spin_statistics a
  have hb := P.spin_statistics b
  rw [hspin] at ha
  have hab : P.fermionic a ↔ P.fermionic b := ha.trans hb.symm
  rcases Classical.em (P.fermionic b) with h | h
  · exact (hflip.mp (hab.mpr h)) h
  · exact h (hab.mp (hflip.mpr h))

end GaloisForLFunctions.HTGeometry
