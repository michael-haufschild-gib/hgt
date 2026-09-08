import GaloisForLFunctions.RHTower.MobiusDivisorEvenCorePrimeReserve

/-!
# Reserve pairs containing every sufficiently large prescribed prime

The even-core reserve window is inverted: fixing the larger prime r,
the prime interval theorem supplies a smaller partner p in
(r/(L+1), r/L). Every sufficiently large prescribed prime is therefore
included in a pair with positive complete coefficient reserve. The final
core remains even, and actual arithmetic energies inherit this reserve
at every sufficiently large cutoff for each selected pair. Thresholds
depend on the current core; no global exhaustion bound is asserted.
-/

noncomputable section
set_option autoImplicit false
open Finset Set Filter Topology MeasureTheory
namespace RHTower

/-- Every sufficiently large prescribed prime belongs to a pair giving
a positive source reserve. The smaller partner is selected in an inverse
ratio window. This is universal in the prescribed prime beyond the
core-dependent threshold, rather than merely an unbounded pair choice. -/
theorem exists_mobiusDivisorEvenCore_prescribed_prime_pair_reserve (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀r∈P,r.Prime) (heven : Even P.card) :
    ∃c T : ℝ,0<c ∧ ∀r : ℕ,r.Prime → T≤(r:ℝ) →
      ∃p : ℕ,p.Prime ∧ p<r ∧ p∉P ∧ r∉P ∧
        Even (insert p (insert r P)).card ∧
        c/(r:ℝ) ≤ (∑'n,mobiusDivisorFixedCoreBlockMass P n)-
          ∑'n,mobiusDivisorFixedCoreBlockMass (insert p (insert r P)) n := by
  obtain ⟨L,c,T,hL,hc,hreserve⟩ := exists_mobiusDivisorEvenCore_pair_reserve P hP hprime heven
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hL1 : 0<L+1 := by linarith
  obtain ⟨Z,hZ⟩ := Filter.eventually_atTop.mp (prime_between (one_div_pos.mpr hL0))
  let A : ℝ := max Z (max T (((P.sup id:ℕ):ℝ)+1))
  refine ⟨c,(L+1)*A,hc,?_⟩
  intro r hr hrT
  have hrR : (0:ℝ)<r := by exact_mod_cast hr.pos
  have hA : A≤(r:ℝ)/(L+1) := (le_div_iff₀ hL1).mpr (by simpa [mul_comm] using hrT)
  obtain ⟨p,hp,hplo,hphi⟩ := hZ ((r:ℝ)/(L+1)) ((le_max_left _ _).trans hA)
  have hpR : (0:ℝ)<p := by exact_mod_cast hp.pos
  have he : (1+1/L)*((r:ℝ)/(L+1))=(r:ℝ)/L := by field_simp
  rw [he] at hphi
  have hpL : L*(p:ℝ)≤r := by
    have h := (lt_div_iff₀ hL0).mp hphi
    nlinarith only [h]
  have hrU : (r:ℝ)≤(L+1)*(p:ℝ) := by
    have h := (div_lt_iff₀ hL1).mp hplo
    nlinarith only [h]
  have hpqR : (p:ℝ)<r := calc
    _ < (r:ℝ)/L := hphi
    _ ≤ (r:ℝ) := (div_le_self hrR.le hL)
  have hpq : p<r := by exact_mod_cast hpqR
  have hpT : T≤(p:ℝ) := ((le_max_left _ _).trans (le_max_right Z _)).trans (hA.trans hplo.le)
  have hsup : ((P.sup id:ℕ):ℝ)+1<(p:ℝ) :=
    ((le_max_right _ _).trans (le_max_right Z _)).trans_lt (hA.trans_lt hplo)
  have hpP : p∉P := by
    intro h
    have hle : p≤P.sup id := Finset.le_sup (f := id) h
    have hleR : (p:ℝ)≤((P.sup id:ℕ):ℝ) := by exact_mod_cast hle
    linarith
  have hrP : r∉P := by
    intro h
    have hle : r≤P.sup id := Finset.le_sup (f := id) h
    have hleR : (r:ℝ)≤((P.sup id:ℕ):ℝ) := by exact_mod_cast hle
    linarith
  have hpi : p∉insert r P := by simp [hpq.ne,hpP]
  have hnew : Even (insert p (insert r P)).card := by
    rw [card_insert_of_notMem hpi,card_insert_of_notMem hrP]
    obtain ⟨k,hk⟩ := heven
    exact ⟨k+1,by omega⟩
  have hrel := hreserve p r hp hr hpP hrP hpq.ne' hpT hpL hrU
  rw [Finset.insert_comm r p P] at hrel
  exact ⟨p,hp,hpq,hpP,hrP,hnew,
    (div_le_div_of_nonneg_left hc.le hpR hpqR.le).trans hrel⟩

/-- Prescribed large primes can be included in a reserve-producing block
for the actual arithmetic energies. The cutoff onset may depend on the
prescribed prime and its selected partner. -/
theorem exists_mobiusDivisorEvenCore_prescribed_prime_energy_reserve (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀r∈P,r.Prime) (heven : Even P.card) :
    ∃c T : ℝ,0<c ∧ ∀r : ℕ,r.Prime → T≤(r:ℝ) →
      ∃p : ℕ,p.Prime ∧ p<r ∧ p∉P ∧ r∉P ∧
        Even (insert p (insert r P)).card ∧ ∀ᶠM : ℕ in atTop,
        c/(r:ℝ)*(M:ℝ)^2 ≤ mobiusDivisorSelectionEnergy M P-
          mobiusDivisorSelectionEnergy M (insert p (insert r P)) := by
  obtain ⟨c,T,hc,hpairs⟩ := exists_mobiusDivisorEvenCore_prescribed_prime_pair_reserve
    P hP hprime heven
  refine ⟨c/2,T,by positivity,?_⟩
  intro r hr hrT
  obtain ⟨p,hp,hpr,hpP,hrP,hnew,hreserve⟩ := hpairs r hr hrT
  refine ⟨p,hp,hpr,hpP,hrP,hnew,?_⟩
  have hboth : ∀q∈insert p (insert r P),q.Prime := by
    intro q hq
    rcases mem_insert.mp hq with rfl | hq
    · exact hp
    rcases mem_insert.mp hq with rfl | hq
    · exact hr
    · exact hprime q hq
  have ht := (tendsto_mobiusDivisorSelectionEnergy_div_sq P hprime).sub
    (tendsto_mobiusDivisorSelectionEnergy_div_sq _ hboth)
  have hrR : (0:ℝ)<r := by exact_mod_cast hr.pos
  have hstrict : (c/2)/(r:ℝ) < (∑'n,mobiusDivisorFixedCoreBlockMass P n)-
        ∑'n,mobiusDivisorFixedCoreBlockMass (insert p (insert r P)) n := by
    apply lt_of_lt_of_le _ hreserve
    exact div_lt_div_of_pos_right (by linarith) hrR
  have he := ht.eventually (eventually_gt_nhds hstrict)
  filter_upwards [he,eventually_gt_atTop (0:ℕ)] with M hM hM0
  have hMR : (0:ℝ)<M := by exact_mod_cast hM0
  simp only [← sub_div] at hM
  exact (le_div_iff₀ (pow_pos hMR 2)).mp hM.le

end RHTower
