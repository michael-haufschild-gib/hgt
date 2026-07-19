import GaloisForLFunctions.HTGeometry.ProjectiveCauchyBaseRigidity
import GaloisForLFunctions.HTGeometry.ProjectiveNevanlinnaKernelContinuity

/-!
# Rigidity of the Nevanlinna jet kernel

Assembling the two halves.  The Nevanlinna jet column expands in the projective Cauchy powers with
the triangular jet coefficient array, block diagonal over the nodes.  The Cauchy powers are rigid,
and away from the critical locus the coefficient array has injective transpose blockwise, so the
Nevanlinna kernel is rigid.

Noncriticality enters exactly once, through the diagonal `r! · a z · (q' z) ^ r` of the coefficient
array.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- The block diagonal coefficient array converting projective Cauchy powers into Nevanlinna jets. -/
def nevanlinnaPacketCoeffMatrix {ι : Type*} [DecidableEq ι] (a q : ℂ → ℂ)
    (n : ι → ℕ) (z : ι → ℂ) : (Σ i, Fin (n i)) → (Σ i, Fin (n i)) → ℂ :=
  fun s k => if s.1 = k.1 then nevanlinnaJetCoeff a q s.2.1 k.2.1 (z s.1) else 0

/-- The Nevanlinna jet column is the coefficient array applied to the projective Cauchy powers. -/
theorem projectiveNevanlinnaJetExpansionColumn_eq_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a q : ℂ → ℂ)
    (n : ι → ℕ) (z : ι → ℂ) (t : OnePoint ℝ) (s : Σ i, Fin (n i)) :
    projectiveNevanlinnaJetExpansionColumn a q z n t s =
      ∑ k : Σ i, Fin (n i), nevanlinnaPacketCoeffMatrix a q n z s k *
        projectiveCauchyPower (q (z k.1)) k.2.1 t := by
  classical
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single s.1]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp [nevanlinnaPacketCoeffMatrix]
  · intro i' _ hne
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [nevanlinnaPacketCoeffMatrix, if_neg (Ne.symm hne), zero_mul]
  · intro hmem
    exact absurd (Finset.mem_univ s.1) hmem

/-- **Rigidity of the Nevanlinna jet kernel.**  At distinct noncritical upper-half-plane nodes,
against a measure of infinite support, an almost-everywhere vanishing real part of a packet
combination of Nevanlinna jet columns forces every coefficient to vanish. -/
theorem nevanlinnaJetColumn_coeff_eq_zero_of_ae_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {ν : Measure ℝ} (hsupp : ν.support.Infinite)
    (a q : ℂ → ℂ) (n : ι → ℕ) (z : ι → ℂ)
    (hx : Function.Injective fun i => q (z i))
    (hupper : ∀ i, 0 < (q (z i)).im)
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0)
    (c : (Σ i, Fin (n i)) → ℂ)
    (hc : ∀ᵐ r : ℝ ∂ν,
      (∑ s : Σ i, Fin (n i),
        c s * projectiveNevanlinnaJetExpansionColumn a q z n (r : OnePoint ℝ) s).re = 0) :
    ∀ s, c s = 0 := by
  classical
  set B : ℝ → (Σ i, Fin (n i)) → ℂ :=
    fun r k => projectiveCauchyPower (q (z k.1)) k.2.1 (r : OnePoint ℝ) with hBdef
  set M : (Σ i, Fin (n i)) → (Σ i, Fin (n i)) → ℂ :=
    nevanlinnaPacketCoeffMatrix a q n z with hMdef
  set K : ℝ → (Σ i, Fin (n i)) → ℂ :=
    fun r s => projectiveNevanlinnaJetExpansionColumn a q z n (r : OnePoint ℝ) s with hKdef
  have hexp : ∀ (r : ℝ) (s : Σ i, Fin (n i)), K r s = ∑ k : Σ i, Fin (n i), M s k * B r k :=
    fun r s => projectiveNevanlinnaJetExpansionColumn_eq_sum a q n z (r : OnePoint ℝ) s
  -- Base rigidity of the projective Cauchy powers.
  have hBrig : ∀ d : (Σ i, Fin (n i)) → ℂ,
      (∀ᵐ r : ℝ ∂ν, (∑ k : Σ i, Fin (n i), d k * B r k).re = 0) → ∀ k, d k = 0 := by
    intro d hd
    exact projectiveCauchyPower_sigma_coeff_eq_zero_of_ae_re hsupp
      (fun i => q (z i)) hx hupper n d hd
  -- Blockwise triangular injectivity of the coefficient array.
  have hMinj : ∀ e : (Σ i, Fin (n i)) → ℂ,
      (∀ k : Σ i, Fin (n i), ∑ s : Σ i, Fin (n i), e s * M s k = 0) → ∀ s, e s = 0 := by
    intro e he
    refine sigma_annihilator_eq_zero_of_blockwise M ?_ ?_ e he
    · intro s k hne
      simp only [hMdef, nevanlinnaPacketCoeffMatrix, if_neg hne]
    · intro i d hd
      refine nevanlinnaJetCoeff_transpose_annihilator_eq_zero (ha i) (hq i) (n i) d ?_
      intro k
      have hk := hd k
      simpa [hMdef, nevanlinnaPacketCoeffMatrix] using hk
  exact kernel_ae_re_rigidity_of_transpose_injective ν B M K hexp hBrig hMinj c hc

end

end GaloisForLFunctions.HTGeometry
