import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockWindows
import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeBlockPersistence

/-! Exact coefficient maps at arithmetic birth thresholds. The lower free branch
reduces modulo two, the upper annihilator branch includes into the ring, and
all maps within one coefficient window retain the same scalar or residue class. -/

noncomputable section
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- Crossing the two-tag birth reduces the lower coefficient modulo two. -/
theorem twoPrimeLower_free_modTwo_transition (m : ℕ) {N M : ℕ} (h : N ≤ M)
    (hm : m ≤ N) (hN : N < 2*m) (h2 : 2*m ≤ M) (h3 : M < 3*m)
    (x : TwoPrimeLowerHomology R m N) :
    twoPrimeLowerModTwoEquiv R m M h2 h3 (twoPrimeLowerHomologyMap R m h x) =
      Submodule.Quotient.mk (twoPrimeLowerFreeEquiv R m N hm hN x) := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeLowerRelations R m N) x
  rfl

/-- Crossing the three-tag birth includes the annihilator coefficient into the free ring. -/
theorem twoPrimeUpper_annihilator_free_transition (m : ℕ) {N M : ℕ} (h : N ≤ M)
    (h2 : 2*m ≤ N) (h3 : N < 3*m) (hM : 3*m ≤ M) (h6 : M < 6*m)
    (x : TwoPrimeUpperHomology R m N) :
    twoPrimeUpperFreeEquiv R m M hM h6 (twoPrimeUpperHomologyMap R m h x) =
      (twoPrimeUpperAnnihilatorEquiv R m N h2 h3 x).val := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeUpperRelations R m N) x
  rfl

/-- Height maps inside the lower free window retain its coefficient. -/
theorem twoPrimeLower_free_transition (m : ℕ) {N M : ℕ} (h : N ≤ M)
    (hm : m ≤ N) (h2 : M < 2*m) (x : TwoPrimeLowerHomology R m N) :
    twoPrimeLowerFreeEquiv R m M (hm.trans h) h2 (twoPrimeLowerHomologyMap R m h x) =
      twoPrimeLowerFreeEquiv R m N hm (h.trans_lt h2) x := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeLowerRelations R m N) x
  rfl

/-- Height maps inside the lower torsion window retain its residue class. -/
theorem twoPrimeLower_modTwo_transition (m : ℕ) {N M : ℕ} (h : N ≤ M)
    (h2 : 2*m ≤ N) (h3 : M < 3*m) (x : TwoPrimeLowerHomology R m N) :
    twoPrimeLowerModTwoEquiv R m M (h2.trans h) h3 (twoPrimeLowerHomologyMap R m h x) =
      twoPrimeLowerModTwoEquiv R m N h2 (h.trans_lt h3) x := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeLowerRelations R m N) x
  rfl

/-- Height maps inside the upper annihilator window retain its two-torsion coefficient. -/
theorem twoPrimeUpper_annihilator_transition (m : ℕ) {N M : ℕ} (h : N ≤ M)
    (h2 : 2*m ≤ N) (h3 : M < 3*m) (x : TwoPrimeUpperHomology R m N) :
    twoPrimeUpperAnnihilatorEquiv R m M (h2.trans h) h3 (twoPrimeUpperHomologyMap R m h x) =
      twoPrimeUpperAnnihilatorEquiv R m N h2 (h.trans_lt h3) x := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeUpperRelations R m N) x
  rfl

/-- Height maps inside the upper free window retain its coefficient. -/
theorem twoPrimeUpper_free_transition (m : ℕ) {N M : ℕ} (h : N ≤ M)
    (h3 : 3*m ≤ N) (h6 : M < 6*m) (x : TwoPrimeUpperHomology R m N) :
    twoPrimeUpperFreeEquiv R m M (h3.trans h) h6 (twoPrimeUpperHomologyMap R m h x) =
      twoPrimeUpperFreeEquiv R m N h3 (h.trans_lt h6) x := by
  obtain ⟨c,rfl⟩ := Submodule.mkQ_surjective (twoPrimeUpperRelations R m N) x
  rfl

#print axioms twoPrimeLower_free_modTwo_transition
#print axioms twoPrimeUpper_annihilator_free_transition
#print axioms twoPrimeLower_free_transition
#print axioms twoPrimeLower_modTwo_transition
#print axioms twoPrimeUpper_annihilator_transition
#print axioms twoPrimeUpper_free_transition
end GaloisForLFunctions.EffectiveScalingGeometry
