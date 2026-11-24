import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.Analysis.Complex.Basic

/-! # Positive integer nodes for a nonzero spectral detector -/
open MvPolynomial Finset
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section

/-- Every nonzero polynomial of total degree at most d has a nonzero value
on the positive integer grid of side d+1. The coordinates are stored one
below their actual value. -/
theorem positive_grid {n d : ℕ} (p : MvPolynomial (Fin n) ℂ) (hp : p≠0) (hd : p.totalDegree≤d) :
    ∃ b : Fin n→ℕ, (∀ i, b i≤d) ∧ eval (fun i => (b i:ℂ)+1) p≠0 := by
  classical
  let node : ℕ ↪ ℂ := ⟨fun a => (a:ℂ)+1,fun a b h => by
    exact_mod_cast add_right_cancel h⟩
  let S := (range (d+1)).map node
  have hS : S.card=d+1 := by simp [S]
  have hs : p.support.Nonempty := by
    rw [nonempty_iff_ne_empty,ne_eq,support_eq_empty]
    exact hp
  obtain ⟨t,ht,he⟩ := exists_mem_eq_sup _ hs (fun t => Finsupp.sum t fun _ e => e)
  have hdeg : p.totalDegree=t.degree := by
    simpa only [totalDegree,Finsupp.degree_apply,Finsupp.sum] using he
  have hcard (i : Fin n) : t i<S.card := by
    rw [hS]
    exact Nat.lt_succ_of_le ((Finsupp.le_degree i t).trans (hdeg ▸ hd))
  obtain ⟨y,hy,hn⟩ := combinatorial_nullstellensatz_exists_eval_nonzero p t (mem_support_iff.mp ht)
    hdeg (fun _ => S) hcard
  choose b hb hval using fun i => mem_map.mp (hy i)
  have hx : (fun i => (b i:ℂ)+1)=y := funext hval
  exact ⟨b,fun i => Nat.le_of_lt_succ (mem_range.mp (hb i)),by rwa [hx]⟩

#print axioms positive_grid
end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
