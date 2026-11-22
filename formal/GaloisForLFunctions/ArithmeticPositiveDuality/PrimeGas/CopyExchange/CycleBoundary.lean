import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange.PermutationTrace
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting

/-!
# The shortest cycle sets the boundary

For a nonempty set of copies, increasing the real part by any positive amount
from the boundary gives a trace-class heat operator on the fixed labels.
A single cycle of length r realizes the boundary 1/r.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange

open scoped Classical

variable {I : Type*} [Fintype I]

def cycleLengths (π : Equiv.Perm I) := Finset.univ.image (cycleLength π)

private theorem lengths_nonempty [Nonempty I] (π : Equiv.Perm I) : (cycleLengths π).Nonempty :=
  ⟨_,Finset.mem_image.mpr ⟨cycleOf π (Classical.arbitrary I),Finset.mem_univ _,rfl⟩⟩

def shortestCycle [Nonempty I] (π : Equiv.Perm I) : ℕ := (cycleLengths π).min' (lengths_nonempty π)

theorem exists_shortest [Nonempty I] (π : Equiv.Perm I) : ∃ c, cycleLength π c = shortestCycle π := by
  obtain ⟨c,_,hc⟩ := Finset.mem_image.mp (Finset.min'_mem _ (lengths_nonempty π))
  exact ⟨c,hc⟩

theorem shortest_pos [Nonempty I] (π : Equiv.Perm I) : 0 < shortestCycle π := by
  obtain ⟨c,hc⟩ := exists_shortest π
  rw [← hc]
  exact cycleLength_pos π c

theorem shortest_le [Nonempty I] (π : Equiv.Perm I) (c : Cycle π) : shortestCycle π ≤ cycleLength π c :=
  Finset.min'_le _ _ (Finset.mem_image.mpr ⟨c,Finset.mem_univ _,rfl⟩)

theorem fixedHeat_shortest_iff [Nonempty I] (π : Equiv.Perm I) (s : ℂ) :
    HasFixedHeat π s ↔ 1/(shortestCycle π : ℝ) < s.re := by
  have hpos : 0 < (shortestCycle π : ℝ) := by exact_mod_cast shortest_pos π
  rw [fixedHeat_traceClass_iff,div_lt_iff₀ hpos,mul_comm s.re]
  constructor
  · intro h
    obtain ⟨c,hc⟩ := exists_shortest π
    simpa only [← hc] using h c
  · intro h c
    have hs : 0 < s.re := by
      by_contra! hn
      linarith only [mul_nonpos_of_nonneg_of_nonpos hpos.le hn,h]
    have hc : (shortestCycle π : ℝ) ≤ cycleLength π c := by exact_mod_cast shortest_le π c
    exact h.trans_le (mul_le_mul_of_nonneg_right hc hs.le)

/-- The boundary is characterized without analytic continuation. -/
theorem fixedHeat_boundary_iff [Nonempty I] (π : Equiv.Perm I) (s : ℂ) :
    (¬HasFixedHeat π s ∧ ∀ δ : ℝ, 0 < δ → HasFixedHeat π (s+(δ : ℂ))) ↔
      s.re = 1/(shortestCycle π : ℝ) := by
  simp only [fixedHeat_shortest_iff, not_lt, Complex.add_re, Complex.ofReal_re]
  constructor
  · rintro ⟨hs,hr⟩
    apply le_antisymm hs
    by_contra! h
    have hh := hr _ (sub_pos.mpr h)
    linarith only [hh]
  · intro h
    exact ⟨h.le,fun δ hδ => by linarith only [h,hδ]⟩

theorem shortest_two_iff [Nonempty I] (π : Equiv.Perm I) :
    shortestCycle π = 2 ↔ (∀ c, cycleLength π c ≠ 1) ∧ ∃ c, cycleLength π c = 2 := by
  constructor
  · intro h
    refine ⟨fun c => ?_,?_⟩
    · have hb := shortest_le π c
      omega
    · simpa only [h] using exists_shortest π
  · rintro ⟨h1,c,h2⟩
    obtain ⟨j,hj⟩ := exists_shortest π
    have hb := shortest_le π c
    have hp := shortest_pos π
    have hn := h1 j
    omega

/-- The fixed-label heat boundary agrees with probability-preserving binary splitting. -/
def DetectsSplit (π : Equiv.Perm I) : Prop :=
  ∀ s : ℂ, (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x) ↔
    (¬HasFixedHeat π s ∧ ∀ δ : ℝ, 0 < δ → HasFixedHeat π (s+(δ : ℂ)))

/-- Exactly the permutations with a two-cycle and no fixed position detect isometric binary splitting. -/
theorem split_detecting_permutations [Nonempty I] (π : Equiv.Perm I) :
    DetectsSplit π ↔ (∀ c, cycleLength π c ≠ 1) ∧ ∃ c, cycleLength π c = 2 := by
  unfold DetectsSplit
  simp only [split_isometric_iff,fixedHeat_boundary_iff,← shortest_two_iff]
  constructor
  · intro h
    have hh := (h (1/2)).mp (by norm_num)
    have hp : (shortestCycle π : ℝ) ≠ 0 := by exact_mod_cast (shortest_pos π).ne'
    have he : (1/2 : ℝ) = 1/(shortestCycle π : ℝ) := by simpa using hh
    field_simp [hp] at he
    exact_mod_cast he
  · intro h s
    rw [h]
    norm_num

private abbrev rotationUnique (n : ℕ) : Unique (Cycle (finRotate (n+1))) where
  default := cycleOf _ 0
  uniq c := by
    let π := finRotate (n+1)
    obtain ⟨i,rfl⟩ := cycleOf_surjective π c
    have h : cycleOf π ∘ π = cycleOf π := funext (cycleOf_step π)
    exact congrFun ((SymmetricCharacters.fixed_finRotate_iff n _).mp h) i

private theorem rotation_length (n : ℕ) (c : Cycle (finRotate (n+1))) :
    cycleLength (finRotate (n+1)) c = n+1 := by
  letI := rotationUnique n
  let e : {i : Fin (n+1) // cycleOf (finRotate (n+1)) i = c} ≃ Fin (n+1) :=
    ⟨Subtype.val, fun i => ⟨i,Subsingleton.elim _ _⟩,fun _ => rfl,fun _ => rfl⟩
  exact (Fintype.card_congr e).trans (Fintype.card_fin _)

theorem rotation_partition (n : ℕ) (s : ℂ) :
    cyclePartition (finRotate (n+1)) s = riemannZeta (((n+1 : ℕ) : ℂ)*s) := by
  letI := rotationUnique n
  rw [cyclePartition,Fintype.prod_unique,rotation_length]

theorem rotation_boundary (n : ℕ) (s : ℂ) :
    HasFixedHeat (finRotate (n+1)) s ↔ 1/((n+1 : ℕ) : ℝ) < s.re := by
  obtain ⟨c,hc⟩ := exists_shortest (finRotate (n+1))
  rw [fixedHeat_shortest_iff,← hc,rotation_length]

#print axioms fixedHeat_shortest_iff
#print axioms fixedHeat_boundary_iff
#print axioms shortest_two_iff
#print axioms split_detecting_permutations
#print axioms rotation_partition
#print axioms rotation_boundary

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange
