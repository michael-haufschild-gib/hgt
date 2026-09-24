import GaloisForLFunctions.RHTower.MobiusDivisorThirdSectorMixedSign
import GaloisForLFunctions.RHTower.MobiusDivisorNegativeSupport

/-!
# Upper-third primes cannot discharge parity defects

The source-specific partner orientation from `MobiusDivisorThirdSectorMixedSign`
excludes every fresh prime above one-third of the cutoff from the literal
negative-support set, after any processed prime core. The existing
negative-support transport theorem then forces good-parity energy to fall and
reversed-sign defect energy to rise under such an insertion. This identifies
which primes can repair the defect but does not bound the complete all-cutoff
history or prove RH.
-/

noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

/-- A fresh upper-third prime cannot lie in the negative-support set of any
    processed prime core. -/
theorem third_sector_not_mem_negativeSupport
    (M : ℕ) (P : Finset ℕ) (hP : ∀ r∈P,r.Prime)
    {p : ℕ} (hp : p.Prime) (hpP : p∉P) (hMp : M<3*p) :
    p∉mobiusDivisorNegativeSupport M P := by
  intro h
  obtain ⟨_,R,hR,hpR,hneg⟩ := Finset.mem_filter.mp h
  let S := R.erase p
  have hpS : p∉S := Finset.notMem_erase p R
  have hS : ∀ r∈S,r.Prime := by
    intro r hr
    have hrR := (Finset.mem_erase.mp hr).2
    exact (Finset.mem_filter.mp (Finset.mem_powerset.mp hR hrR)).2
  have hs := third_sector_partner_oriented_nonpos M P S hP hS hp hpP hpS hMp
  have he : insert p S=R := Finset.insert_erase hpR
  have hor : 0 ≤ mobiusDivisorOrientedFibre M P R := by
    rw [← he,mobiusDivisorOrientedFibre,Finset.card_insert_of_notMem hpS,pow_succ]
    nlinarith only [hs]
  exact (not_lt_of_ge hor) hneg

/-- Above one-third cutoff, prime insertion can only decrease good-parity
    energy and increase reversed-sign defect energy, regardless of old core. -/
theorem third_sector_good_defect_monotone
    (M : ℕ) (P : Finset ℕ) (hP : ∀ r∈P,r.Prime)
    {p : ℕ} (hp : p.Prime) (hpM : p<M)
    (hpP : p∉P) (hMp : M<3*p) :
    mobiusDivisorParityGoodEnergy M (insert p P) ≤ mobiusDivisorParityGoodEnergy M P ∧
    mobiusDivisorParityDefectEnergy M P ≤ mobiusDivisorParityDefectEnergy M (insert p P) := by
  exact mobiusDivisorParityEnergy_insert_outside_negativeSupport M P
    (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hpM,hp⟩)
    (third_sector_not_mem_negativeSupport M P hP hp hpP hMp)

end RHTower
