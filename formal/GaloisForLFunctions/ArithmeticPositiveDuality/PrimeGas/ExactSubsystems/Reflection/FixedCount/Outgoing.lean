import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.FixedCount.Uniform
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Packets.Exchange.Wave
import GaloisForLFunctions.HTGeometry.FiniteKMSWightman

/-! # Reflection tests using normalized outgoing probabilities with arbitrary relabeling -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount

open Finset Real _root_.HTGeometry
open scoped ComplexConjugate

/-- At any nonzero inverse temperature, one permutation matches opposite Gibbs laws precisely
when its paired energies have a common sum. -/
theorem permuted_gibbs_iff {X : Type*} [Fintype X] (E : X → ℝ) (R : Equiv.Perm X) (b : ℝ) :
    (∀ x, finiteGibbsStateWeight b E x = finiteGibbsStateWeight (-b) E (R x)) ↔
      b = 0 ∨ ∃ L : ℝ, ∀ x, E x + E (R x) = L := by
  constructor
  · intro h
    by_cases hb : b = 0
    · exact Or.inl hb
    refine Or.inr ⟨(log (finiteGibbsPartition (-b) E) - log (finiteGibbsPartition b E))/b, fun x => ?_⟩
    letI : Nonempty X := ⟨x⟩
    have he := congrArg log (h x)
    simp only [finiteGibbsStateWeight, log_div (exp_pos _).ne' (finiteGibbsPartition_pos _ _).ne',
      log_exp, neg_neg] at he
    apply (eq_div_iff hb).mpr
    linarith only [he]
  · rintro (rfl | ⟨L, h⟩)
    · intro x; simp [finiteGibbsStateWeight]
    · have factor (x : X) : exp (-(-b)*E (R x)) = exp (b*L)*exp (-b*E x) := by
        rw [← exp_add, ← h x]
        congr 1; ring
      have z : finiteGibbsPartition (-b) E = exp (b*L)*finiteGibbsPartition b E := by
        unfold finiteGibbsPartition
        rw [← Equiv.sum_comp R (fun x => exp (-(-b)*E x))]
        simp only [factor, mul_sum]
      intro x
      rw [finiteGibbsStateWeight, finiteGibbsStateWeight, factor, z, mul_div_mul_left _ _ (exp_pos _).ne']

variable {S : Finset Nat.Primes} {c : S → ℕ} {m : ℕ}

def levels (c : S → ℕ) (m : ℕ) : Finset ℕ+ := univ.image (level (c := c) (m := m))

/-- Conditional probability of one conserved integer label in the complete two-copy output
of a wave with equal amplitudes on the occupation sector. -/
def outgoingShare (s : ℂ) (x : State c m) : ℝ :=
  let U := levels c m
  ExactSubsystems.ThermalShells.Packets.Exchange.outputTest U s (fun n => if level x = n then 1 else 0) /
    ExactSubsystems.ThermalShells.Packets.Exchange.outputTest U s (fun _ => 1)

theorem outgoing_gibbs (s : ℂ) (x : State c m) :
    outgoingShare s x = finiteGibbsStateWeight (2*s.re-1) (fun y : State c m => energy (level y)) x := by
  classical
  let U := levels c m
  have hx : level x ∈ U := mem_image.mpr ⟨x, mem_univ x, rfl⟩
  have hn := (ExactSubsystems.ThermalShells.Packets.Exchange.hasSum_output U s
    (fun n => if level x = n then 1 else 0) (fun n _ => by split <;> norm_num)).tsum_eq
  have hd := (ExactSubsystems.ThermalShells.Packets.Exchange.hasSum_output U s
    (fun _ => 1) (fun _ _ => zero_le_one)).tsum_eq
  have z : (∑ n ∈ U, shellMass s n) = ∑ y : State c m, shellMass s (level y) :=
    sum_image (fun _ _ _ _ h => level_injective h)
  calc outgoingShare s x = (∑ n ∈ U, shellMass s n * (if level x = n then 1 else 0)) /
             (∑ n ∈ U, shellMass s n * 1) := congrArg₂ (fun a b : ℝ => a/b) hn hd
       _ = _ := by
          simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, if_pos hx]
          rw [z]
          simp only [finiteGibbsStateWeight, finiteGibbsPartition, shellMass, neg_sub]

/-- A nonempty sector matches the two outgoing laws after some relabeling of its basis. -/
def Matched (S : Finset Nat.Primes) (c : S → ℕ) (m : ℕ) (s : ℂ) : Prop :=
  Nonempty (State c m) ∧ ∃ R : Equiv.Perm (State c m),
    ∀ x, outgoingShare s x = outgoingShare (1-conj s) (R x)

theorem fixed_permutation_iff (s : ℂ) (R : Equiv.Perm (State c m)) :
    (∀ x, outgoingShare s x = outgoingShare (1-conj s) (R x)) ↔
      s.re = 1/2 ∨ ∃ L : ℝ, ∀ x, energy (level x) + energy (level (R x)) = L := by
  simp_rw [outgoing_gibbs]
  have flip : 2*(1-conj s).re-1 = -(2*s.re-1) := by rw [Complex.sub_re, Complex.one_re, Complex.conj_re]; ring
  have mid : 2*s.re-1 = 0 ↔ s.re = 1/2 := by constructor <;> intro h <;> linarith only [h]
  rw [flip, permuted_gibbs_iff, mid]

/-- Away from the line the unlabeled laws, if matched, determine the permutation uniquely. -/
theorem matching_permutation_unique (s : ℂ) (hs : s.re ≠ 1/2) (R Q : Equiv.Perm (State c m))
    (hr : ∀ x, outgoingShare s x = outgoingShare (1-conj s) (R x))
    (hq : ∀ x, outgoingShare s x = outgoingShare (1-conj s) (Q x)) : R = Q := by
  obtain ⟨_, hR⟩ := ((fixed_permutation_iff s R).mp hr).resolve_left hs
  obtain ⟨_, hQ⟩ := ((fixed_permutation_iff s Q).mp hq).resolve_left hs
  exact Equiv.ext fun x => state_ext fun i => Nat.add_left_cancel
    ((reflecting_map_counts ⟨x⟩ R hR x i).trans (reflecting_map_counts ⟨x⟩ Q hQ x i).symm)

theorem matched_iff_line_or_reflection (S : Finset Nat.Primes) (c : S → ℕ) (m : ℕ) (s : ℂ) :
    Matched S c m s ↔ Nonempty (State c m) ∧ (s.re = 1/2 ∨ Reflects S c m) := by
  constructor
  · rintro ⟨hne, R, h⟩
    refine ⟨hne, ?_⟩
    rcases (fixed_permutation_iff s R).mp h with h | ⟨L, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨hne, L, R, h⟩
  · rintro ⟨hne, hs | ⟨_, L, R, h⟩⟩
    · exact ⟨hne, Equiv.refl _, (fixed_permutation_iff s _).mpr (Or.inl hs)⟩
    · exact ⟨hne, R, (fixed_permutation_iff s R).mpr (Or.inr ⟨L, h⟩)⟩

/-- A single pair of reflected parameters decides the full coordinate criterion off the
isometry line. On the line every feasible sector matches. -/
theorem outgoing_reflection_iff (S : Finset Nat.Primes) (c : S → ℕ) (m : ℕ) (s : ℂ) :
    Matched S c m s ↔ m ≤ capacity c ∧ (s.re = 1/2 ∨ (∑ i, pairCount c m i) = 2*m) := by
  rw [matched_iff_line_or_reflection, feasible_iff, reflection_iff]
  tauto

/-- With three or more prime modes, every nonvacuum unrestricted sector detects whole-gas
isometry even when the observed outgoing basis labels can be permuted arbitrarily. -/
theorem unrestricted_match_iff_isometry (S : Finset Nat.Primes) (hr : 2 < S.card) (m : ℕ) (hm : 0 < m)
    (s : ℂ) : Matched S (fun _ => m) m s ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x := by
  rw [split_isometric_iff, matched_iff_line_or_reflection, unrestricted_reflection_iff, feasible_iff]
  have hcap : m ≤ capacity (fun _ : S => m) := by
    simpa [capacity] using (Nat.mul_le_mul_right m (show 1 ≤ S.card by omega))
  have hfalse : ¬(m = 0 ∨ (0 < S.card ∧ S.card ≤ 2)) := by omega
  simp only [hcap, hfalse, or_false, true_and]

def firstThree : Finset Nat.Primes := {⟨2, Nat.prime_two⟩, ⟨3, Nat.prime_three⟩, ⟨5, Nat.prime_five⟩}

private theorem firstThree_card : firstThree.card = 3 := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  let q : Nat.Primes := ⟨3, Nat.prime_three⟩
  let r : Nat.Primes := ⟨5, Nat.prime_five⟩
  have hpq : p ≠ q := fun h => (by norm_num : (2 : ℕ) ≠ 3) (congrArg Subtype.val h)
  have hpr : p ≠ r := fun h => (by norm_num : (2 : ℕ) ≠ 5) (congrArg Subtype.val h)
  have hqr : q ≠ r := fun h => (by norm_num : (3 : ℕ) ≠ 5) (congrArg Subtype.val h)
  have h₁ : p ∉ ({q,r} : Finset Nat.Primes) := by simpa only [mem_insert, mem_singleton, not_or] using And.intro hpq hpr
  have h₂ : q ∉ ({r} : Finset Nat.Primes) := fun h => hqr (mem_singleton.mp h)
  change ({p,q,r} : Finset Nat.Primes).card = 3
  rw [card_insert_of_notMem h₁, card_insert_of_notMem h₂, card_singleton]

/-- The six two-particle labels 4,6,9,10,15,25 suffice even if all labels are forgotten
when comparing the two measured probability lists. -/
theorem six_label_match_iff_critical (s : ℂ) :
    Matched firstThree (fun _ => 2) 2 s ↔ s.re = 1/2 :=
  (unrestricted_match_iff_isometry firstThree (by rw [firstThree_card]; norm_num) 2 (by norm_num) s).trans
    (split_isometric_iff s)

#print axioms six_label_match_iff_critical
#print axioms permuted_gibbs_iff
#print axioms outgoing_gibbs
#print axioms fixed_permutation_iff
#print axioms matching_permutation_unique
#print axioms outgoing_reflection_iff
#print axioms unrestricted_match_iff_isometry

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.FixedCount
