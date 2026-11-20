import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheEffectOfOnePrimeBlockOnTheUnitaryCut
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.WeightedSectionsOfTheUnitaryFactorPairs

/-!
# Removing a prime-power block from the integer conductor

Write k=b n with b the full power of p in k. A unitary divisor d of n
crosses the cut when b is added exactly if n < b d² and d² ≤ b n.
When this two-sided interval is empty, the arithmetic test on k factors
through the actual smaller-divisor test on n. One change of the
occupation probability at p detects the equality of these two cuts.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- A direction has zero pivots precisely when deleting its prime
power from the integer gives the correct test on every configuration. -/
theorem unitary_pivot_free_iff_arithmetic_deletion {k p : ℕ} (hp : p∈k.primeFactors) :
    unitaryPivots k p=∅ ↔ ∀ S⊆k.primeFactors,
      (S∈smallUnitarySubsets k ↔ S.erase p∈smallUnitarySubsets (ordCompl[p] k)) := by
  let n := ordCompl[p] k
  let b := p^k.factorization p
  have bp : 0<b := pow_pos (Nat.prime_of_mem_primeFactors hp).pos _
  have support : n.primeFactors=k.primeFactors.erase p := unitary_cofactor_primeFactors k p
  constructor
  · intro empty S hs
    let T := S.erase p
    let d := primePowerSubset n T
    have sub : T⊆n.primeFactors := by
      rw [support]
      exact fun q h => mem_erase.mpr ⟨(mem_erase.mp h).1,hs (mem_erase.mp h).2⟩
    have cap (lo : d^2≤k) : b*d^2≤n := by
      by_contra! big
      have edge := (unitary_pivot_cofactor_window hp T).mpr ⟨sub,lo,big⟩
      simpa only [empty,notMem_empty] using edge
    have lo (h : b*d^2≤n) : d^2≤n := (Nat.le_mul_of_pos_left _ bp).trans h
    have below (h : d^2≤n) : d^2≤k := h.trans (Nat.ordCompl_le k p)
    obtain ⟨off,on,cof⟩ := unitary_cofactor_cut_sections hp sub
    by_cases present : p∈S
    · have eq : insert p T=S := insert_erase present
      rw [eq] at on
      exact on.trans ((show b*d^2≤n ↔ d^2≤n from ⟨lo,fun h => cap (below h)⟩).trans cof.symm)
    · have eq : T=S := erase_eq_of_notMem present
      have fromOff : T∈smallUnitarySubsets k ↔ T∈smallUnitarySubsets n :=
        off.trans ((show d^2≤k ↔ d^2≤n from ⟨fun h => lo (cap h),below⟩).trans cof.symm)
      change S∈smallUnitarySubsets k ↔ T∈smallUnitarySubsets n
      exact (show (S∈smallUnitarySubsets k) ↔ T∈smallUnitarySubsets k by rw [eq]).trans fromOff
  · intro delete
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨T,edge⟩
    obtain ⟨sub,lo,big⟩ := (unitary_pivot_cofactor_window hp T).mp edge
    have ss := sub
    rw [support] at ss
    have subP := ss.trans (erase_subset p k.primeFactors)
    have fresh : p∉T := fun hit => notMem_erase p k.primeFactors (ss hit)
    obtain ⟨off,on,_⟩ := unitary_cofactor_cut_sections hp sub
    have lower := (delete T subP).mp (off.mpr lo)
    rw [erase_eq_of_notMem fresh] at lower
    have upper := delete (insert p T) (insert_subset hp subP)
    rw [erase_insert fresh] at upper
    exact big.not_ge (on.mp (upper.mpr lower))

/-- One interior occupation experiment detects whether the whole
arithmetic cut can be replaced by the smaller conductor's cut. -/
theorem unitary_single_probe_detects_deletion {k p : ℕ} (hp : p∈k.primeFactors) {u : ℕ → ℝ}
    (inside : ∀ q∈k.primeFactors.erase p, 0<u q ∧ u q<1) {x y : ℝ} (step : x<y) :
    unitaryIndependentCut k (Function.update u p y)=unitaryIndependentCut k (Function.update u p x) ↔
      ∀ S⊆k.primeFactors, (S∈smallUnitarySubsets k ↔ S.erase p∈smallUnitarySubsets (ordCompl[p] k)) := by
  rw [←unitary_pivot_free_iff_arithmetic_deletion hp]
  constructor
  · intro eq
    apply not_nonempty_iff_eq_empty.mp
    exact fun live => ((unitary_block_strict_response_iff hp inside step).mpr live).ne eq
  · intro empty
    rw [←sub_eq_zero,unitary_cut_single_block_response hp,unitaryPivotalProbability,empty,sum_empty,mul_zero]

private theorem on_cube (k : ℕ) (u : ℕ → ℝ) :
    unitaryIndependentCut k u=∑ S ∈ k.primeFactors.powerset,
      (if S∈smallUnitarySubsets k then unitaryBlockPatternMass k.primeFactors u S else 0) := by
  rw [←sum_filter,unitaryIndependentCut]
  have id : k.primeFactors.powerset.filter (·∈smallUnitarySubsets k)=smallUnitarySubsets k := by
    ext S
    exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨(mem_filter.mp h).1,h⟩⟩
  rw [id]

/-- Removing a pivot-free block preserves the entire probability law for
every choice of occupation parameters, including all deterministic corners. -/
theorem unitary_independent_cut_after_deletion {k p : ℕ} (hp : p∈k.primeFactors)
    (empty : unitaryPivots k p=∅) (u : ℕ → ℝ) :
    unitaryIndependentCut k u=unitaryIndependentCut (ordCompl[p] k) u := by
  let P := k.primeFactors
  let B := P.erase p
  let n := ordCompl[p] k
  let f (S : Finset ℕ) := if S∈smallUnitarySubsets k then unitaryBlockPatternMass P u S else 0
  have law := (unitary_pivot_free_iff_arithmetic_deletion hp).mp empty
  have cube : unitaryIndependentCut k u=∑ S ∈ (insert p B).powerset,f S := by
    rw [show insert p B=P from insert_erase hp]
    exact on_cube k u
  rw [cube,sum_powerset_insert (show p∉B from notMem_erase p P),←sum_add_distrib,on_cube n,unitary_cofactor_primeFactors]
  refine sum_congr rfl fun S hs => ?_
  have sB := mem_powerset.mp hs
  have sub := sB.trans (erase_subset p P)
  have fresh : p∉S := fun h => notMem_erase p P (sB h)
  have a := law S sub
  have b := law (insert p S) (insert_subset hp sub)
  rw [erase_eq_of_notMem fresh] at a
  rw [erase_insert fresh] at b
  have forget := unitary_pattern_mass_erase P (insert p S) p u
  rw [erase_insert fresh] at forget
  dsimp only [f,n]
  simp only [a,b]
  by_cases hit : S∈smallUnitarySubsets (ordCompl[p] k)
  · simp only [hit,if_true]
    rw [unitary_pattern_mass_at_site hp u S,unitary_pattern_mass_at_site hp u (insert p S),
      if_neg fresh,if_pos (mem_insert_self ..),←forget]
    change (1-u p)*unitaryBlockPatternMass B u S+u p*unitaryBlockPatternMass B u S=
      unitaryBlockPatternMass B u S
    ring
  · simp only [hit,if_false,add_zero]

/-- Functional equality of the two independent probability laws is
equivalent to vanishing of the p-direction pivotal family. -/
theorem unitary_probability_deletion_iff {k p : ℕ} (hp : p∈k.primeFactors) :
    (∀ u : ℕ → ℝ, unitaryIndependentCut k u=unitaryIndependentCut (ordCompl[p] k) u) ↔
      unitaryPivots k p=∅ := by
  constructor
  · intro equal
    let n := ordCompl[p] k
    let u : ℕ → ℝ := fun _ => 1/2
    have independent (x : ℝ) : unitaryIndependentCut n (Function.update u p x)=unitaryIndependentCut n u := by
      unfold unitaryIndependentCut
      apply sum_congr rfl
      intro S _
      unfold unitaryBlockPatternMass
      apply prod_congr rfl
      intro q hq
      have h : q∈k.primeFactors.erase p := (unitary_cofactor_primeFactors k p) ▸ hq
      rw [Function.update_of_ne (mem_erase.mp h).1]
    have probe : unitaryIndependentCut k (Function.update u p 1)=unitaryIndependentCut k (Function.update u p 0) := by
      rw [equal,equal,independent,independent]
    apply (unitary_pivot_free_iff_arithmetic_deletion hp).mpr
    exact (unitary_single_probe_detects_deletion hp (u:=u) (fun _ _ => by dsimp [u]; norm_num)
      zero_lt_one).mp probe
  · exact fun empty u => unitary_independent_cut_after_deletion hp empty u

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
