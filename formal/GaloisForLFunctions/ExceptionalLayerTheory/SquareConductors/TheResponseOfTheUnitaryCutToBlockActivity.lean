import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheBoundaryMeasureOfSmallUnitaryDivisors
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.OneExchangeAtTheUnitarySquareRoot
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Sensitivity of the square-root cut under independent block births

The finite-volume activity in Erbar–Huesmann–Stange, Lemma 2.6,
assigns weight z^j to a configuration with j occupied blocks. On
unitary divisors its normalizing partition function is (1+z)^r.
Birth-and-death balance expresses the derivative of the smaller-side
probability exactly in terms of the configurations that cross the cut.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Partition function restricted to unitary divisors on the smaller side. -/
def unitaryCutPartition (k : ℕ) (z : ℝ) : ℝ :=
  ∑ S ∈ smallUnitarySubsets k, z^S.card

/-- Probability of the smaller side when each block has birth activity z
and unit death rate. Its occupation probability is z/(1+z). -/
def unitaryCutProbability (k : ℕ) (z : ℝ) : ℝ :=
  unitaryCutPartition k z/(1+z)^k.primeFactors.card

/-- Pivotal configurations weighted by activity, with an edge counted
in each direction in which a birth crosses the square root. -/
def unitaryExitPartition (k : ℕ) (z : ℝ) : ℝ :=
  ∑ p ∈ k.primeFactors, ∑ S ∈ unitaryPivots k p, z^S.card

private def cutSlope (k : ℕ) (z : ℝ) :=
  ∑ S ∈ smallUnitarySubsets k, (S.card:ℝ)*z^(S.card-1)

private theorem power_slope (z : ℝ) (j : ℕ) :
    z*((j:ℝ)*z^(j-1))=(j:ℝ)*z^j := by
  cases j with
  | zero => simp
  | succ j => rw [Nat.succ_sub_one,pow_succ]; ring

private theorem exit_score (k : ℕ) (z : ℝ) :
    unitaryExitPartition k z=(k.primeFactors.card:ℝ)*unitaryCutPartition k z-(1+z)*cutSlope k z := by
  rw [unitaryExitPartition,unitaryPivots_radial_flux k (fun j => z^j)]
  simp only [nsmul_eq_mul]
  rw [unitaryCutPartition,cutSlope,mul_sum,mul_sum,←sum_sub_distrib]
  refine sum_congr rfl fun S hs => ?_
  rw [Nat.cast_sub (card_le_card (mem_powerset.mp (mem_filter.mp hs).1))]
  linear_combination power_slope z S.card

private theorem normalized_score {q v r Z J B : ℝ} (hq : q≠0) (hv : v≠0)
    (h : B=r*Z-q*J) :
    (J*v-Z*(r*v/q))/v^2 = -B/(v*q) := by
  apply (eq_div_iff (mul_ne_zero hv hq)).mpr
  calc _ = q*J-r*Z := by field_simp [hq,hv]
       _ = -B := by linarith only [h]

/-- Exact response at any nonnegative activity. Each pivotal edge
contributes the probability weight of its lower endpoint divided by
1+z, with a negative sign. -/
theorem unitary_cut_activity_response (k : ℕ) {z : ℝ} (hz : 0≤z) :
    HasDerivAt (unitaryCutProbability k) (-unitaryExitPartition k z/(1+z)^(k.primeFactors.card+1)) z := by
  let r := k.primeFactors.card
  let q := 1+z
  have qp : 0<q := add_pos_of_pos_of_nonneg zero_lt_one hz
  have hp : HasDerivAt (unitaryCutPartition k) (cutSlope k z) z :=
    HasDerivAt.fun_sum (fun S _ => hasDerivAt_pow S.card z)
  have den : HasDerivAt (fun u : ℝ => (1+u)^r) ((r:ℝ)*q^r/q) z := by
    have d := (((hasDerivAt_const z (1:ℝ)).add (hasDerivAt_id z)).pow r)
    apply d.congr_deriv
    simp only [zero_add,mul_one]
    apply (eq_div_iff qp.ne').mpr
    exact (mul_comm ..).trans (power_slope q r)
  apply (hp.div den (pow_ne_zero r qp.ne')).congr_deriv
  rw [pow_succ]
  exact normalized_score qp.ne' (pow_ne_zero r qp.ne') (exit_score k z)

private theorem positive_exit_activity {k : ℕ} (hk : 1<k) {z : ℝ} (hz : 0<z) :
    0<unitaryExitPartition k z := by
  have pivot : ∃ p ∈ k.primeFactors, (unitaryPivots k p).Nonempty := by
    by_contra absent
    have empty (p : ℕ) (hp : p∈k.primeFactors) : unitaryPivots k p=∅ :=
      not_nonempty_iff_eq_empty.mp (fun h => absent ⟨p,hp,h⟩)
    have total := unitaryPivots_factorial_mass hk
    have zero : (∑ p ∈ k.primeFactors, ∑ S ∈ unitaryPivots k p,
        S.card.factorial*(k.primeFactors.card-S.card-1).factorial)=0 :=
      sum_eq_zero fun p hp => by rw [empty p hp,sum_empty]
    exact (Nat.factorial_pos _).ne' (total.symm.trans zero)
  obtain ⟨p,hp,S,hS⟩ := pivot
  exact sum_pos' (fun j _ => sum_nonneg (fun T _ => (pow_pos hz T.card).le))
    ⟨p,hp,sum_pos' (fun T _ => (pow_pos hz T.card).le) ⟨S,hS,pow_pos hz S.card⟩⟩

/-- At every nontrivial integer the smaller-side probability strictly
decreases throughout the positive activity axis. -/
theorem unitary_cut_probability_strictAnti {k : ℕ} (hk : 1<k) :
    StrictAntiOn (unitaryCutProbability k) (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 0)
  · exact fun z hz => (unitary_cut_activity_response k (le_of_lt hz)).continuousAt.continuousWithinAt
  · intro z hz
    have pos : 0<z := interior_subset hz
    rw [(unitary_cut_activity_response k pos.le).deriv]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos (positive_exit_activity hk pos)) (by positivity)

/-- For a block just below the square root, the departure from the
full opposite face is the difference between the singleton weight z
and the opposite corner weight z^b, where b is the number of other blocks. -/
theorem one_exchange_activity_law {k p : ℕ} (hp : p∈k.primeFactors)
    (low : (p^k.factorization p)^2<k) (high : k<(2*p^k.factorization p)^2)
    {z : ℝ} (hz : 0≤z) :
    let b := (k.primeFactors.erase p).card
    unitaryCutProbability k z=1/(1+z)+(z-z^b)/(1+z)^(b+1) := by
  intro b
  let B := k.primeFactors.erase p
  have faces : (∑ S ∈ B.powerset, z^S.card)=(1+z)^b := by
    simpa only [prod_const] using (prod_one_add (f:=fun _ : ℕ => z) B).symm
  have shape := unitary_one_exchange_price hp low high (fun S => z^S.card)
  change unitaryCutPartition k z+z^b=z^({p}:Finset ℕ).card+∑ S ∈ B.powerset,z^S.card at shape
  rw [faces,card_singleton,pow_one] at shape
  have rank : k.primeFactors.card=b+1 := by
    dsimp only [b]
    rw [card_erase_of_mem hp]
    have := card_pos.mpr (show k.primeFactors.Nonempty from ⟨p,hp⟩)
    omega
  have qp : 0<1+z := add_pos_of_pos_of_nonneg zero_lt_one hz
  rw [unitaryCutProbability,rank,
    show unitaryCutPartition k z=(1+z)^b+(z-z^b) by linarith only [shape],add_div,pow_succ]
  field_simp [qp.ne']

private theorem pivot_at_cut {k q : ℕ} (hq : q∈k.primeFactors) (S : Finset ℕ) :
    S∈unitaryPivots k q ↔ q∉S ∧ S∈smallUnitarySubsets k ∧ insert q S∉smallUnitarySubsets k := by
  have hk := Nat.pos_of_ne_zero (Nat.mem_primeFactors.mp hq).2.2
  have small {T : Finset ℕ} (sub : T⊆k.primeFactors) :
      T∈smallUnitarySubsets k ↔ (primePowerSubset k T)^2≤k := by
    simp only [smallUnitarySubsets,mem_filter,mem_powerset,sub,true_and,unitarySubset_small_iff_square hk sub]
  constructor
  · intro h
    obtain ⟨sub,lo,hi⟩ := mem_filter.mp h
    have support := (mem_powerset.mp sub).trans (erase_subset q k.primeFactors)
    have fresh : q∉S := fun hit => notMem_erase q k.primeFactors (mem_powerset.mp sub hit)
    refine ⟨fresh,(small support).mpr lo,fun inside => ?_⟩
    have cap := (small (insert_subset hq support)).mp inside
    rw [show primePowerSubset k (insert q S)=q^k.factorization q*primePowerSubset k S from prod_insert fresh] at cap
    exact hi.not_ge cap
  · rintro ⟨fresh,inside,out⟩
    have sub := mem_powerset.mp (mem_filter.mp inside).1
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (fun i hi => mem_erase.mpr ⟨fun eq => fresh (eq ▸ hi),sub hi⟩),
      (small sub).mp inside,?_⟩
    apply lt_of_not_ge
    intro cap
    apply out ((small (insert_subset hq sub)).mpr ?_)
    rwa [show primePowerSubset k (insert q S)=q^k.factorization q*primePowerSubset k S from prod_insert fresh]

/-- For a one-exchange cut the distinguished block crosses from every
proper nonempty subset of the opposite face. Each other block crosses
from exactly two configurations: the distinguished singleton and the
opposite face with that other block deleted. -/
theorem one_exchange_pivotal_directions {k p : ℕ} (hp : p∈k.primeFactors)
    (low : (p^k.factorization p)^2<k) (high : k<(2*p^k.factorization p)^2) :
    let B := k.primeFactors.erase p
    unitaryPivots k p=(B.powerset.erase B).erase ∅ ∧
      ∀ q∈B, unitaryPivots k q={{p},B.erase q} := by
  intro B
  have hpB : p∉B := notMem_erase p k.primeFactors
  have cut (S : Finset ℕ) : S∈smallUnitarySubsets k ↔ S={p} ∨ (S≠B ∧ S⊆B) := by
    rw [small_unitary_subsets_one_exchange hp low high]
    simp only [mem_insert,mem_erase,mem_powerset,B]
  have noB : B≠{p} := fun eq => hpB (eq.symm ▸ mem_singleton_self p)
  constructor
  · ext S
    rw [pivot_at_cut hp,cut,cut,mem_erase,mem_erase,mem_powerset]
    constructor
    · rintro ⟨fresh,s,h⟩
      have ne : S≠{p} := fun eq => fresh (eq.symm ▸ mem_singleton_self p)
      refine ⟨?_,s.resolve_left ne⟩
      rintro rfl
      exact h (Or.inl (by simp))
    · rintro ⟨hn,neq,sub⟩
      have fresh : p∉S := fun h => hpB (sub h)
      refine ⟨fresh,Or.inr ⟨neq,sub⟩,?_⟩
      rintro (eq|⟨_,wide⟩)
      · have erase := congrArg (fun A : Finset ℕ => A.erase p) eq
        exact hn (by simpa only [erase_insert fresh,erase_singleton] using erase)
      · exact hpB (wide (mem_insert_self ..))
  · intro q hq
    have qne := (mem_erase.mp hq).1
    have qP := (mem_erase.mp hq).2
    ext S
    rw [pivot_at_cut qP,cut,cut,mem_insert,mem_singleton]
    constructor
    · rintro ⟨fresh,s,out⟩
      rcases s with one|⟨_,sub⟩
      · exact Or.inl one
      · right
        have fill : insert q S=B := by
          by_contra no
          exact out (Or.inr ⟨no,insert_subset hq sub⟩)
        have eq := congrArg (fun T : Finset ℕ => T.erase q) fill
        simpa only [erase_insert fresh] using eq
    · rintro (rfl|rfl)
      · refine ⟨by simpa only [mem_singleton] using qne,Or.inl rfl,?_⟩
        rintro (eq|⟨_,sub⟩)
        · exact qne (mem_singleton.mp (eq ▸ mem_insert_self q ({p}:Finset ℕ)))
        · exact hpB (sub (mem_insert_of_mem (mem_singleton_self p)))
      · refine ⟨notMem_erase q B,Or.inr ⟨?_,erase_subset q B⟩,?_⟩
        · intro same
          exact notMem_erase q B (same.symm ▸ hq)
        · rw [insert_erase hq]
          exact fun h => (h.resolve_left noB).1 rfl

/-- A one-exchange cut with b other blocks has 2^b−2+2b
boundary edges, despite differing from a full face at just two vertices. -/
theorem one_exchange_boundary_size {k p : ℕ} (hp : p∈k.primeFactors)
    (low : (p^k.factorization p)^2<k) (high : k<(2*p^k.factorization p)^2) :
    let b := (k.primeFactors.erase p).card
    (∑ q ∈ k.primeFactors, (unitaryPivots k q).card)=(2^b-2)+2*b := by
  intro b
  let B := k.primeFactors.erase p
  obtain ⟨main,rest⟩ := one_exchange_pivotal_directions hp low high
  change unitaryPivots k p=(B.powerset.erase B).erase ∅ at main
  have size : (unitaryPivots k p).card=2^b-2 := by
    rw [main]
    change _=2^B.card-2
    by_cases empty : B=∅
    · simp [empty]
    · have bottom : ∅∈B.powerset.erase B := mem_erase.mpr ⟨Ne.symm empty,mem_powerset.mpr (empty_subset _)⟩
      rw [card_erase_of_mem bottom,card_erase_of_mem (mem_powerset.mpr Subset.rfl),card_powerset]
      omega
  have side (q : ℕ) (hq : q∈B) : (unitaryPivots k q).card=2 := by
    rw [rest q hq]
    have fresh : ({p}:Finset ℕ)∉({B.erase q}:Finset (Finset ℕ)) := by
      intro h
      have eq := mem_singleton.mp h
      exact notMem_erase p k.primeFactors (erase_subset q B (eq ▸ mem_singleton_self p))
    rw [card_insert_of_notMem fresh,card_singleton]
  calc _ = ∑ q ∈ insert p B,(unitaryPivots k q).card := by rw [show insert p B=k.primeFactors from insert_erase hp]
       _ = _ := by
         rw [sum_insert (show p∉B from notMem_erase p k.primeFactors),size,sum_congr rfl side,
           sum_const,nsmul_eq_mul]
         change 2^b-2+b*2=2^b-2+2*b
         rw [Nat.mul_comm b 2]

#print axioms one_exchange_boundary_size
#print axioms one_exchange_pivotal_directions
#print axioms unitary_cut_activity_response
#print axioms unitary_cut_probability_strictAnti
#print axioms one_exchange_activity_law
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
