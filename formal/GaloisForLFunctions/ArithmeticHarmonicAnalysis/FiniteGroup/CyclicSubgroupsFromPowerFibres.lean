import GaloisForLFunctions.RHTower.Artin.ArtinCyclicInductionIdentity
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Cyclic subgroup counts from power fibers

Each element generates one cyclic subgroup, and each cyclic subgroup of
order d accounts for φ(d) generators. Decomposing the fiber of x ↦ xⁿ
over one by the order of its elements recovers the whole distribution of
cyclic subgroup orders. This counting argument applies to nonabelian
groups as well.
-/

noncomputable section
open Finset
open scoped Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.CyclicCensus

variable (G : Type*) [Group G] [Fintype G]

/-- Actual cyclic subgroups at one order. -/
def ofOrder (d : ℕ) := (cyclicSubgroups G).filter fun C => Nat.card C=d

private theorem generator_fiber (d : ℕ) (C : Subgroup G) (hc : C∈ofOrder G d) :
    ((univ.filter fun x : G => orderOf x=d).filter fun x => Subgroup.zpowers x=C).card =
      d.totient := by
  classical
  obtain ⟨hcyc,hsize⟩ := mem_filter.mp hc
  obtain ⟨g,_,hg⟩ := mem_image.mp hcyc
  letI : IsCyclic C := hg ▸ Subgroup.isCyclic_zpowers g
  have hd : d ∣ Fintype.card C := by rw [← Nat.card_eq_fintype_card,hsize]
  rw [← IsCyclic.card_orderOf_eq_totient (α := C) hd]
  symm
  refine card_bij (fun (x : C) _ => (x : G)) ?_ (fun _ _ _ _ he => Subtype.ext he) ?_
  · intro x hx
    have ho := (Subgroup.orderOf_coe x).trans (mem_filter.mp hx).2
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,ho⟩,?_⟩
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le_of_mem x.property)
    rw [Nat.card_zpowers,hsize,ho]
  · intro b hb
    obtain ⟨hb,he⟩ := mem_filter.mp hb
    have hm : b∈C := he ▸ Subgroup.mem_zpowers b
    exact ⟨⟨b,hm⟩,mem_filter.mpr ⟨mem_univ _,(Subgroup.orderOf_mk _ _).trans (mem_filter.mp hb).2⟩,rfl⟩

/-- Partition elements of exact order d by the subgroup they generate. -/
theorem generators (d : ℕ) :
    (univ.filter fun x : G => orderOf x=d).card = (ofOrder G d).card * d.totient := by
  classical
  rw [card_eq_sum_card_fiberwise (f := fun x : G => Subgroup.zpowers x) (t := ofOrder G d)
    (fun x hx => mem_filter.mpr ⟨zpowers_mem_cyclicSubgroups x,
      (Nat.card_zpowers x).trans (mem_filter.mp hx).2⟩)]
  simp only [sum_congr rfl (fun C hc => generator_fiber G d C hc),sum_const,nsmul_eq_mul]

/-- Dirichlet divisor transform connecting torsion counts and cyclic subgroups. -/
theorem power_fiber (n : ℕ) (hn : 0<n) :
    Nat.card {x : G // x^n=1} = ∑ d ∈ n.divisors, (ofOrder G d).card * d.totient := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,card_eq_sum_card_fiberwise (f := orderOf)
    (t := n.divisors) (fun x hx => Nat.mem_divisors.mpr
      ⟨orderOf_dvd_iff_pow_eq_one.mpr (mem_filter.mp hx).2,hn.ne'⟩)]
  apply sum_congr rfl
  intro d hd
  rw [← generators]
  congr 1
  ext x
  simp only [mem_filter,mem_univ,true_and,and_iff_right_iff_imp]
  intro he
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [he]
  exact (Nat.mem_divisors.mp hd).1

/-- At a prime power the inverse transform uses two adjacent torsion
counts. It needs neither cyclicity of the ambient group nor division. -/
theorem prime_layer {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Nat.card {x : G // x^(p^(k+1))=1} =
      Nat.card {x : G // x^(p^k)=1} + (ofOrder G (p^(k+1))).card*(p^(k+1)).totient := by
  rw [power_fiber G _ (pow_pos hp.pos _),power_fiber G _ (pow_pos hp.pos _),
    Nat.sum_divisors_prime_pow hp,Nat.sum_divisors_prime_pow hp,sum_range_succ]

/-- Every common annihilating exponent partitions all cyclic subgroups by its divisors. -/
theorem total_over_exponent (n : ℕ) (hn : 0<n) (ha : ∀ x : G, x^n=1) :
    (cyclicSubgroups G).card = ∑ d ∈ n.divisors, (ofOrder G d).card := by
  classical
  apply card_eq_sum_card_fiberwise (f := fun C : Subgroup G => Nat.card C)
  intro C hc
  obtain ⟨g,_,rfl⟩ := mem_image.mp hc
  rw [Nat.card_zpowers]
  exact Nat.mem_divisors.mpr ⟨orderOf_dvd_iff_pow_eq_one.mpr (ha g),hn.ne'⟩

/-- The positive power-fiber sizes and the counts of cyclic subgroups of
each positive order determine one another, across any two finite groups. -/
theorem power_fibers_determine_orders (H : Type*) [Group H] [Fintype H] :
    (∀ n : ℕ, 0<n → Nat.card {x : G // x^n=1}=Nat.card {y : H // y^n=1}) ↔
    ∀ d : ℕ, 0<d → (ofOrder G d).card=(ofOrder H d).card := by
  constructor
  · intro hh n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      have he := hh n hn
      rw [power_fiber G n hn,power_fiber H n hn] at he
      have hmem := Nat.mem_divisors.mpr ⟨dvd_rfl,hn.ne'⟩
      have hrest : ∑ d ∈ n.divisors.erase n, (ofOrder G d).card*d.totient =
          ∑ d ∈ n.divisors.erase n, (ofOrder H d).card*d.totient := by
        refine sum_congr rfl fun d hd => ?_
        obtain ⟨hne,hd⟩ := mem_erase.mp hd
        have hdiv := (Nat.mem_divisors.mp hd).1
        rw [ih d (lt_of_le_of_ne (Nat.le_of_dvd hn hdiv) hne) (Nat.pos_of_dvd_of_pos hdiv hn)]
      rw [← sum_erase_add _ _ hmem,← sum_erase_add _ _ hmem,hrest] at he
      exact Nat.eq_of_mul_eq_mul_right (Nat.totient_pos hn) (Nat.add_left_cancel he)
  · intro he n hn
    rw [power_fiber G n hn,power_fiber H n hn]
    exact sum_congr rfl fun d hd => by rw [he d (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 hn)]

end GaloisForLFunctions.ArithmeticHarmonicAnalysis.CyclicCensus

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.CyclicCensus.generators
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.CyclicCensus.power_fiber
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.CyclicCensus.prime_layer
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.CyclicCensus.total_over_exponent
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.CyclicCensus.power_fibers_determine_orders
