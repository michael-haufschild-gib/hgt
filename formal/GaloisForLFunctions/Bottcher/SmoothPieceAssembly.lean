/-
# From modulus-one fibre roots to a relatively open smooth Julia piece (P5, partial)

Chains the root-limit lemma (`RootLimitModulus`) with the modulus-one pigeonhole
(`FiniteCoverRelInterior`) through the algebraic identification of roots with analytic branch values
(`HolomorphicIFT.root_complete`).  Given a finite family of continuous branch functions `g_j` that
are the complete simple-root set of the fibre polynomial on a closed Julia piece `S`, and that every
point of `S` carries a modulus-one fibre root (the output of the root-limit lemma), some single
branch has modulus `1` on a relatively open subset of `S` — a relatively open Julia arc lying in the
smooth real-analytic curve `{‖g_j‖ = 1}`.  This is the pigeonhole spine of the connected-case
root-limit route; the branch family's existence (off the discriminant) and the modulus-one supply
(the hole-free accessible tip) are the two inputs it consumes.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.RootLimitModulus
import GaloisForLFunctions.Bottcher.FiniteCoverRelInterior
import GaloisForLFunctions.Bottcher.RelativeBranchFamily
import GaloisForLFunctions.U0.HolomorphicIFT

open Set Topology Filter Polynomial

namespace Bottcher

/-- **A modulus-one root is a branch value.**  At `w`, if the `N` distinct branch values `b j` are
roots of the degree-`N` fibre polynomial, then every root — in particular a modulus-one root — is one
of them.  Direct `root_complete`. -/
theorem exists_branch_eq_of_isRoot {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s) {w : ℂ} (hlead : a N w ≠ 0)
    {b : Fin N → ℂ} (hbinj : Function.Injective b)
    (hbroot : ∀ j, (fibrePoly a s w).IsRoot (b j))
    {x : ℂ} (hxroot : (fibrePoly a s w).IsRoot x) : ∃ j, x = b j := by
  have hdeg : (fibrePoly a s w).natDegree = N := natDegree_fibrePoly_eq hsupp hN hlead
  have hpne : fibrePoly a s w ≠ 0 := by
    intro h
    have : (fibrePoly a s w).coeff N = a N w := by rw [coeff_fibrePoly, if_pos hN]
    rw [h, Polynomial.coeff_zero] at this
    exact hlead this.symm
  exact HolomorphicIFT.root_complete hpne hdeg hbinj hbroot hxroot

/-- **Modulus-one fibre roots yield a relatively open smooth Julia piece.**  On a closed nonempty
`S ⊆ ℂ` where the fibre polynomial has nonvanishing leading coefficient and a complete family of `N`
continuous, pointwise-distinct branch roots `g_j`, if every point of `S` carries a modulus-one fibre
root, then some `{‖g_j‖ = 1}` contains a nonempty relatively open subset of `S`. -/
theorem exists_relOpen_smooth_piece_of_modulus_one_roots
    {a : ℕ → ℂ → ℂ} {s : Finset ℕ} {N : ℕ}
    (hsupp : s ⊆ Finset.range (N + 1)) (hN : N ∈ s)
    {S : Set ℂ} (hScl : IsClosed S) (hSne : S.Nonempty)
    (g : Fin N → ℂ → ℂ) (hgcont : ∀ j, Continuous (g j))
    (hlead : ∀ w ∈ S, a N w ≠ 0)
    (hginj : ∀ w ∈ S, Function.Injective (fun j => g j w))
    (hgroot : ∀ w ∈ S, ∀ j, (fibrePoly a s w).IsRoot (g j w))
    (hmodroot : ∀ w ∈ S, ∃ x : ℂ, ‖x‖ = 1 ∧ (fibrePoly a s w).IsRoot x) :
    ∃ j : Fin N, ∃ U : Set ℂ, IsOpen U ∧ (U ∩ S).Nonempty ∧ ∀ w ∈ U ∩ S, ‖g j w‖ = 1 := by
  have hcov : ∀ w ∈ S, ∃ j : Fin N, ‖g j w‖ = 1 := by
    intro w hw
    obtain ⟨x, hxnorm, hxroot⟩ := hmodroot w hw
    obtain ⟨j, hj⟩ := exists_branch_eq_of_isRoot hsupp hN (hlead w hw)
      (hginj w hw) (hgroot w hw) hxroot
    exact ⟨j, by rw [← hj]; exact hxnorm⟩
  exact exists_relOpen_subset_modulus_one hScl hSne g hgcont hcov

end Bottcher
