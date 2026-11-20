import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.TheSymplecticFourierIdentityOfCyclicAmbiguity
import GaloisForLFunctions.ArithmeticCountingPositivity.AUniformSquarefreeMajority
import GaloisForLFunctions.RHTower.Sieve.SquarefreeIndicator

/-!
# Every cyclic lag of the Möbius profile carries energy

Periodize μ(1),…,μ(q) after taking those exact integer values. Summing
the ambiguity weights over frequency counts pairs of squarefree
positions at the requested cyclic separation. A squarefree majority
gives a uniform lower bound at every lag. For q≥4 each row contains at
least two positive frequencies, regardless of the signs of the samples.
-/
noncomputable section
open Finset Complex ArithmeticFunction
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable (q : ℕ) [NeZero q]

def cyclicMoebiusProfile (x : ZMod q) : ℂ := ((moebius (x.val+1) : ℤ) : ℂ)

def squarefreeCyclicSites : Finset (ZMod q) :=
  univ.filter fun x => Squarefree (x.val+1)

def squarefreeCyclicPairs (b : ZMod q) : Finset (ZMod q) :=
  univ.filter fun x => Squarefree (x.val+1) ∧ Squarefree ((x+b).val+1)

private theorem sites_card :
    (squarefreeCyclicSites q).card=((Icc 1 q).filter Squarefree).card := by
  classical
  refine card_bij (fun (x : ZMod q) _ => x.val+1) ?_ ?_ ?_
  · intro x hx
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,ZMod.val_lt x⟩,(mem_filter.mp hx).2⟩
  · intro x hx y hy h
    exact ZMod.val_injective q (by omega)
  · intro n hn
    obtain ⟨hn,hf⟩ := mem_filter.mp hn
    obtain ⟨hn0,hnq⟩ := mem_Icc.mp hn
    have hlt : n-1<q := by omega
    have hx : ((n-1:ℕ):ZMod q).val+1=n := by rw [ZMod.val_natCast_of_lt hlt]; omega
    exact ⟨((n-1:ℕ):ZMod q),mem_filter.mpr ⟨mem_univ _,hx.symm ▸ hf⟩,hx⟩

omit [NeZero q] in
private theorem squarefree_intensity (x : ZMod q) :
    ‖cyclicMoebiusProfile q x‖^2 = if Squarefree (x.val+1) then 1 else 0 := by
  have h : cyclicMoebiusProfile q x = (((moebius (x.val+1):ℤ):ℝ):ℂ) := by
    simp [cyclicMoebiusProfile]
  rw [h,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  exact _root_.RHTower.Sieve.moebius_sq_eq_indicator _

omit [NeZero q] in
private theorem squarefree_modulus (x : ZMod q) :
    ‖cyclicMoebiusProfile q x‖ = if Squarefree (x.val+1) then 1 else 0 := by
  have h := congrArg Real.sqrt (squarefree_intensity q x)
  rw [Real.sqrt_sq (norm_nonneg _)] at h
  split_ifs at h ⊢ <;> simpa only [Real.sqrt_one,Real.sqrt_zero] using h

private theorem sum_mask (P : ZMod q → Prop) [DecidablePred P] :
    (∑ x : ZMod q, if P x then (1:ℝ) else 0) = ((univ.filter P).card:ℝ) := by
  rw [←sum_filter]
  simp

/-- Each frequency row has exactly q times the squarefree overlap as
its total mass. Cyclic wraparound is taken after sampling the integers. -/
theorem cyclic_moebius_frequency_mass (b : ZMod q) :
    (∑ a,cyclicAmbiguityWeight (cyclicMoebiusProfile q) a b) = (q:ℝ)*(squarefreeCyclicPairs q b).card := by
  rw [cyclic_ambiguity_frequency_mass]
  congr 1
  calc _ = ∑ x : ZMod q, if Squarefree (x.val+1) ∧ Squarefree ((x+b).val+1) then (1:ℝ) else 0 := by
         refine sum_congr rfl fun x _ => ?_
         rw [squarefree_intensity,squarefree_intensity]
         by_cases h : Squarefree (x.val+1) <;> by_cases h' : Squarefree ((x+b).val+1) <;> simp [h,h']
       _ = _ := sum_mask q _

/-- The squarefree surplus guarantees a positive density of pairs for
every cyclic shift, including shifts depending arbitrarily on q. -/
theorem squarefree_cyclic_overlap_lower (b : ZMod q) :
    (q:ℝ)/36 ≤ ((squarefreeCyclicPairs q b).card:ℝ) := by
  classical
  let f (x : ZMod q) : ℝ := if Squarefree (x.val+1) then 1 else 0
  let g (x : ZMod q) : ℝ := if Squarefree (x.val+1) ∧ Squarefree ((x+b).val+1) then 1 else 0
  have hrow (x : ZMod q) : f x+f (x+b)≤1+g x := by
    by_cases h : Squarefree (x.val+1) <;> by_cases h' : Squarefree ((x+b).val+1) <;>
      norm_num [f,g,h,h']
  have hh := sum_le_sum (s:=univ) (fun x _ => hrow x)
  simp only [sum_add_distrib,sum_const,card_univ,ZMod.card,nsmul_eq_mul,mul_one] at hh
  have hshift : ∑ x, f (x+b) = ∑ x, f x :=
    Fintype.sum_equiv (Equiv.addRight b) _ _ (fun _ => rfl)
  rw [hshift,show (∑ x,f x)=((squarefreeCyclicSites q).card:ℝ) from sum_mask q _,
    show (∑ x,g x)=((squarefreeCyclicPairs q b).card:ℝ) from sum_mask q _,sites_card] at hh
  linarith only [hh,ArithmeticCountingPositivity.squarefree_majority_all_cutoffs q]

/-- Every cyclic lag has quadratic total frequency energy. -/
theorem every_cyclic_moebius_lag_has_quadratic_energy (b : ZMod q) :
    (q:ℝ)^2/36 ≤ ∑ a,cyclicAmbiguityWeight (cyclicMoebiusProfile q) a b := by
  rw [cyclic_moebius_frequency_mass]
  calc (q:ℝ)^2/36 = (q:ℝ)*((q:ℝ)/36) := by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (squarefree_cyclic_overlap_lower q b) (Nat.cast_nonneg q)

private theorem pointwise_pair_bound (a b : ZMod q) :
    cyclicAmbiguityWeight (cyclicMoebiusProfile q) a b ≤ ((squarefreeCyclicPairs q b).card:ℝ)^2 := by
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  apply (norm_sum_le _ _).trans_eq
  calc _ = ∑ x : ZMod q, if Squarefree (x.val+1) ∧ Squarefree ((x+b).val+1) then (1:ℝ) else 0 := by
         refine sum_congr rfl fun x _ => ?_
         simp only [norm_mul,Complex.norm_conj,ZMod.stdAddChar_apply,Circle.norm_coe,mul_one,squarefree_modulus]
         by_cases h : Squarefree (x.val+1) <;> by_cases h' : Squarefree ((x+b).val+1) <;> simp [h,h']
       _ = ((squarefreeCyclicPairs q b).card:ℝ) := sum_mask q _

def activeMoebiusFrequencies (b : ZMod q) : Finset (ZMod q) :=
  univ.filter fun a => 0<cyclicAmbiguityWeight (cyclicMoebiusProfile q) a b

/-- The number of occupied frequencies times the number of squarefree
pairs is at least one complete period, separately at every shift. -/
theorem cyclic_moebius_row_uncertainty (b : ZMod q) :
    q ≤ (activeMoebiusFrequencies q b).card*(squarefreeCyclicPairs q b).card := by
  let E := activeMoebiusFrequencies q b
  let P : ℝ := (squarefreeCyclicPairs q b).card
  have hq : 0 < (q:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  have hp : 0 < P := (div_pos hq (by norm_num : (0:ℝ)<36)).trans_le (squarefree_cyclic_overlap_lower q b)
  have hmass : (∑ a ∈ E,cyclicAmbiguityWeight (cyclicMoebiusProfile q) a b)=(q:ℝ)*P := by
    rw [←cyclic_moebius_frequency_mass]
    apply sum_subset (subset_univ _)
    intro a _ hn
    exact le_antisymm (le_of_not_gt fun h => hn (mem_filter.mpr ⟨mem_univ _,h⟩)) (sq_nonneg _)
  have hs := sum_le_sum (s:=E) (fun a _ => pointwise_pair_bound q a b)
  rw [hmass,sum_const,nsmul_eq_mul] at hs
  have hh : (q:ℝ)*P ≤ ((E.card:ℝ)*P)*P := hs.trans_eq (by dsimp only [P]; ring)
  have he := le_of_mul_le_mul_right hh hp
  dsimp only [E,P] at he
  exact_mod_cast he

private theorem cyclic_pairs_lt_period (hq : 4≤q) (b : ZMod q) :
    (squarefreeCyclicPairs q b).card < q := by
  have hlt : 3<q := by omega
  let x : ZMod q := ((3:ℕ):ZMod q)
  have hx : x.val+1=4 := by rw [show x.val=3 from ZMod.val_natCast_of_lt hlt]
  have hn : ¬Squarefree (4:ℕ) := by
    intro h
    exact (Nat.squarefree_iff_prime_squarefree.mp h 2 Nat.prime_two) (by norm_num)
  have hxout : x∉squarefreeCyclicPairs q b := fun h => hn (hx ▸ (mem_filter.mp h).2.1)
  have hsub : squarefreeCyclicPairs q b ⊂ univ :=
    Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,fun he => hxout (by rw [he]; exact mem_univ x)⟩
  have hs := card_lt_card hsub
  simpa only [card_univ,ZMod.card] using hs

/-- No nontrivial cyclic lag collapses onto a single Fourier mode.
The conclusion also holds at lag zero. -/
theorem two_le_active_moebius_frequencies (hq : 4≤q) (b : ZMod q) :
    2 ≤ (activeMoebiusFrequencies q b).card := by
  have hp := cyclic_pairs_lt_period q hq b
  have h := cyclic_moebius_row_uncertainty q b
  by_contra! hsmall
  have hh := Nat.mul_le_mul_right (squarefreeCyclicPairs q b).card
    (show (activeMoebiusFrequencies q b).card≤1 by omega)
  rw [one_mul] at hh
  exact (h.trans hh).not_gt hp

#print axioms cyclic_moebius_frequency_mass
#print axioms squarefree_cyclic_overlap_lower
#print axioms every_cyclic_moebius_lag_has_quadratic_energy
#print axioms cyclic_moebius_row_uncertainty
#print axioms two_le_active_moebius_frequencies
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
