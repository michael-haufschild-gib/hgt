import GaloisForLFunctions.HTGeometry.ScaledGammaBorelResidue
import GaloisForLFunctions.HTGeometry.FiniteShiftedLaurentCyclicDivisorMomentUniversalityLaw

/-!
# Common-scale completeness of the scaled Gamma alien character

After Gauss multiplication and Gamma recurrence, one rational-commensurability block is a finite
family at a common positive scale whose offset phases are distinct.  This file proves that its
scaled Borel-residue character is faithful: vanishing at every nonzero lattice point is equivalent
to vanishing of every reduced orbit charge.  The proof uses a consecutive Laurent-moment
Vandermonde block and therefore needs only the first `d` positive lattice frequencies.
-/

open Complex
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A Gamma commensurability block after common-scale and shift-orbit reduction.  Distinctness of
the exponential phases is the canonical reducedness condition. -/
structure ReducedGammaAlienBlock (d : ℕ) where
  scale : ℝ
  scale_pos : 0 < scale
  offset : Fin d → ℂ
  multiplicity : Fin d → ℤ
  phase_injective : Function.Injective
    (fun i => cexp (-2 * (Real.pi : ℂ) * I * offset i))

/-- Positive affine Gamma factors represented by a reduced block. -/
def ReducedGammaAlienBlock.factor {d : ℕ}
    (B : ReducedGammaAlienBlock d) (i : Fin d) : PositiveAffineGammaFactor where
  scale := B.scale
  offset := B.offset i
  multiplicity := B.multiplicity i
  scale_pos := B.scale_pos

/-- Offset phase of one reduced orbit. -/
noncomputable def ReducedGammaAlienBlock.phase {d : ℕ}
    (B : ReducedGammaAlienBlock d) (i : Fin d) : ℂ :=
  cexp (-2 * (Real.pi : ℂ) * I * B.offset i)

theorem ReducedGammaAlienBlock.phase_injective' {d : ℕ}
    (B : ReducedGammaAlienBlock d) : Function.Injective B.phase :=
  B.phase_injective

theorem ReducedGammaAlienBlock.phase_ne_zero {d : ℕ}
    (B : ReducedGammaAlienBlock d) (i : Fin d) : B.phase i ≠ 0 :=
  Complex.exp_ne_zero _

/-- Card equation `(15)` at a common scale: the alien character is the finite Laurent Fourier
transform of the reduced orbit charges. -/
theorem scaledGammaAlienChargeAt_reducedBlock_integer {d : ℕ}
    (B : ReducedGammaAlienBlock d) (r : ℤ) (hr : r ≠ 0) :
    scaledGammaAlienChargeAt B.factor ((r : ℝ) * B.scale) =
      (B.scale : ℂ) * ∑ i,
        (B.multiplicity i : ℂ) * B.phase i ^ r := by
  rw [scaledGammaAlienChargeAt]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [ReducedGammaAlienBlock.factor]
  rw [if_pos ⟨r, hr, rfl⟩]
  have hratio : (r : ℝ) * B.scale / B.scale = (r : ℝ) := by
    field_simp [B.scale_pos.ne']
  rw [hratio]
  simp only [ReducedGammaAlienBlock.phase]
  push_cast
  rw [show -2 * (Real.pi : ℂ) * I * (r : ℂ) * B.offset i =
      (r : ℂ) * (-2 * (Real.pi : ℂ) * I * B.offset i) by ring,
    Complex.exp_int_mul]
  ring

/-- **Common-scale scaled-alien-charge completeness.**  A reduced block has zero character at all
nonzero frequencies exactly when every canonical shift-orbit charge is zero. -/
theorem scaledGammaAlienChargeZero_reducedBlock_iff {d : ℕ}
    (B : ReducedGammaAlienBlock d) :
    ScaledGammaAlienChargeZero B.factor ↔ ∀ i, B.multiplicity i = 0 := by
  constructor
  · intro hzero
    let lam : Fin d → ℂ := B.phase
    let c : Fin d → ℂ := fun i => (B.multiplicity i : ℂ)
    have hlam : Function.Injective lam := B.phase_injective'
    have hlam0 : ∀ i, lam i ≠ 0 := B.phase_ne_zero
    have hmom : (fun e : Fin d → ℂ =>
        fun k : Fin d => GaloisForLFunctions.signedLaurentMoment lam e (1 + (k : ℕ))) c = 0 := by
      funext k
      have hr : (1 + (k : ℕ) : ℤ) ≠ 0 := by omega
      have hz := hzero (((1 + (k : ℕ) : ℤ) : ℝ) * B.scale) (by
        exact mul_ne_zero (by exact_mod_cast hr) B.scale_pos.ne')
      rw [scaledGammaAlienChargeAt_reducedBlock_integer
        B (1 + (k : ℕ) : ℤ) hr] at hz
      have hscale : (B.scale : ℂ) ≠ 0 := by exact_mod_cast B.scale_pos.ne'
      have hsum : ∑ i, (B.multiplicity i : ℂ) * B.phase i ^ (1 + (k : ℕ) : ℤ) = 0 :=
        (mul_eq_zero.mp hz).resolve_left hscale
      simpa [GaloisForLFunctions.signedLaurentMoment, lam, c] using hsum
    have hmom' : (fun e : Fin d → ℂ =>
        fun k : Fin d => GaloisForLFunctions.signedLaurentMoment lam e (1 + (k : ℕ))) c =
        (fun e : Fin d → ℂ =>
          fun k : Fin d => GaloisForLFunctions.signedLaurentMoment lam e (1 + (k : ℕ))) 0 := by
      funext k
      have hk := congrFun hmom k
      simpa [GaloisForLFunctions.signedLaurentMoment] using hk
    have hc : c = 0 :=
      (GaloisForLFunctions.signedLaurentMoment_shiftedBlock_injective hlam hlam0 1) hmom'
    intro i
    have hi := congrFun hc i
    change (B.multiplicity i : ℂ) = 0 at hi
    exact_mod_cast hi
  · intro hm t ht
    rw [scaledGammaAlienChargeAt]
    apply Finset.sum_eq_zero
    intro i hi
    simp [ReducedGammaAlienBlock.factor, hm i]

/-! ## Separation of rational-commensurability blocks -/

/-- Membership in the nonzero integer lattice carried by a positive Gamma scale. -/
def gammaAlienLattice (scale t : ℝ) : Prop :=
  ∃ k : ℤ, k ≠ 0 ∧ t = (k : ℝ) * scale

/-- A reduced block with its finite arity hidden, allowing finitely many blocks of different
sizes to be assembled. -/
structure GammaAlienBlock where
  arity : ℕ
  data : ReducedGammaAlienBlock arity

/-- Alien character contributed by one reduced block. -/
def GammaAlienBlock.chargeAt (B : GammaAlienBlock) (t : ℝ) : ℂ :=
  scaledGammaAlienChargeAt B.data.factor t

theorem GammaAlienBlock.chargeAt_eq_zero_of_not_lattice
    (B : GammaAlienBlock) {t : ℝ}
    (ht : ¬ gammaAlienLattice B.data.scale t) : B.chargeAt t = 0 := by
  rw [GammaAlienBlock.chargeAt, scaledGammaAlienChargeAt]
  apply Finset.sum_eq_zero
  intro i hi
  have hnot : ¬ ∃ k : ℤ, k ≠ 0 ∧
      t = (k : ℝ) * (B.data.factor i).scale := by
    simpa only [gammaAlienLattice, ReducedGammaAlienBlock.factor] using ht
  rw [if_neg hnot]

/-- Canonical finite decomposition into rational-commensurability blocks.  Distinct blocks have
disjoint nonzero scaled integer lattices, exactly as for irrational scale ratios. -/
structure ReducedGammaAlienDecomposition (b : ℕ) where
  block : Fin b → GammaAlienBlock
  lattice_disjoint : ∀ {i j : Fin b}, i ≠ j → ∀ {t : ℝ}, t ≠ 0 →
    gammaAlienLattice (block i).data.scale t →
      ¬ gammaAlienLattice (block j).data.scale t

/-- Full scaled alien character, as the disjoint sum of its commensurability blocks. -/
def ReducedGammaAlienDecomposition.characterAt {b : ℕ}
    (D : ReducedGammaAlienDecomposition b) (t : ℝ) : ℂ :=
  ∑ i, (D.block i).chargeAt t

/-- Vanishing of the full decomposed character at every nonzero Borel frequency. -/
def ReducedGammaAlienDecomposition.CharacterZero {b : ℕ}
    (D : ReducedGammaAlienDecomposition b) : Prop :=
  ∀ t : ℝ, t ≠ 0 → D.characterAt t = 0

theorem ReducedGammaAlienDecomposition.characterAt_eq_block_of_mem
    {b : ℕ} (D : ReducedGammaAlienDecomposition b) (i : Fin b)
    {t : ℝ} (ht0 : t ≠ 0)
    (ht : gammaAlienLattice (D.block i).data.scale t) :
    D.characterAt t = (D.block i).chargeAt t := by
  rw [ReducedGammaAlienDecomposition.characterAt]
  apply Finset.sum_eq_single i
  · intro j hj hji
    apply GammaAlienBlock.chargeAt_eq_zero_of_not_lattice
    exact D.lattice_disjoint hji.symm ht0 ht
  · simp

/-- **Global scaled-alien-charge completeness.**  Across disjoint rational-commensurability
classes, the full character vanishes exactly when every reduced shift-orbit charge vanishes. -/
theorem reducedGammaAlienDecomposition_characterZero_iff {b : ℕ}
    (D : ReducedGammaAlienDecomposition b) :
    D.CharacterZero ↔
      ∀ i : Fin b, ∀ j : Fin (D.block i).arity,
        (D.block i).data.multiplicity j = 0 := by
  constructor
  · intro hzero i
    have hblock : ScaledGammaAlienChargeZero (D.block i).data.factor := by
      intro t ht0
      by_cases ht : gammaAlienLattice (D.block i).data.scale t
      · have hg := hzero t ht0
        rw [D.characterAt_eq_block_of_mem i ht0 ht] at hg
        exact hg
      · exact (D.block i).chargeAt_eq_zero_of_not_lattice ht
    exact (scaledGammaAlienChargeZero_reducedBlock_iff (D.block i).data).mp hblock
  · intro hm t ht0
    rw [ReducedGammaAlienDecomposition.characterAt]
    apply Finset.sum_eq_zero
    intro i hi
    have hblock : ScaledGammaAlienChargeZero (D.block i).data.factor :=
      (scaledGammaAlienChargeZero_reducedBlock_iff (D.block i).data).mpr (hm i)
    exact hblock t ht0

end

end GaloisForLFunctions.HTGeometry
