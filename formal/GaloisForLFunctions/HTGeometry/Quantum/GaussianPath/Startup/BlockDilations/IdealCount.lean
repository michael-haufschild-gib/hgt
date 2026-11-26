import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PacketPatterns
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.PatternCount

/-! # Circuit counting for independent rotations of disjoint Pauli packets -/

open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ}

/-- Regularity uses only the internal longitudinal mass, the internal
coefficient norm and the chosen wire and error thresholds. -/
def regularPacket (R : Finset (Fin (n+2))) (u : PathShell n) (h ε : ℝ) (r : ℕ) : Prop :=
  let v := pathShellOnSites R u
  π≤2*h*∑ j : Fin (n+2), |v (.inl (j,2))| ∧
  2*ε+h*‖v‖*(sqrt 21+2+2*sqrt (21*(2*(r:ℝ))))<1

/-- Of all binary patterns of local dilations on a common baseline,
a bounded circuit can fit only exponentially few when many packets
are regular. The estimate is uniform in the baseline matrix. -/
theorem ideal_pattern_count (R : I→Finset (Fin (n+2))) (hR : Pairwise (fun i j => Disjoint (R i) (R j)))
    (u : PathShell n) (W : Reg (n+2)) (h ε : ℝ) (r s : ℕ) :
    open Classical in
    let G := univ.filter fun i => regularPacket (R i) u h ε r
    let C := univ.filter fun x : I→Bool => HasProjectiveCircuitApproximation (n+2) ε s (idealPattern R u x h W)
    C.card*2^(Fintype.card I-2*s/(r+1))≤3^G.card*4^(Fintype.card I-G.card) := by
  classical
  intro G C
  let tag (i : I) := if packetFit (R i) r ε W then true else false
  let E := univ.filter fun x : I→Bool => (G.filter fun i => x i=tag i).card≤2*s/(r+1)
  have hsub : C⊆E := by
    intro x hx
    let T := G.filter fun i => x i=tag i
    have hf : HasProjectiveCircuitApproximation (n+2) ε s (idealPattern R u x h W) := (mem_filter.mp hx).2
    have failed (i : I) (hi : i∈T) : ¬packetFit (R i) r ε (idealPattern R u x h W) := by
      obtain ⟨hiG,hbit⟩ := mem_filter.mp hi
      have hreg : regularPacket (R i) u h ε r := (mem_filter.mp hiG).2
      intro hh
      have hh' := (pattern_fit_iff R hR u x h W i r ε).mp hh
      rw [hbit] at hh'
      by_cases hw : packetFit (R i) r ε W
      · simp [tag,hw] at hh'
        exact hreg.2.not_ge (longitudinal_flip_cost (R i) u W r h ε hreg.1 hw hh')
      · simp [tag,hw] at hh'
    have hb := failed_packets_cost R hR T r s ε _ hf failed
    exact mem_filter.mpr ⟨mem_univ _,(Nat.le_div_iff_mul_le (Nat.succ_pos r)).mpr hb⟩
  exact (Nat.mul_le_mul_right _ (card_le_card hsub)).trans (few_matching_patterns G tag _)

#print axioms ideal_pattern_count
end
end GaloisForLFunctions.HTGeometry.BlockDilations
