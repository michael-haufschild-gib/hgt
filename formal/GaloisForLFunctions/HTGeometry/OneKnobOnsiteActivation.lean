import GaloisForLFunctions.HTGeometry.BlockAffineLineAvoidance
import GaloisForLFunctions.HTGeometry.OneKnobProjectiveActivation
import GaloisForLFunctions.HTGeometry.SeparableSpectrumRankBound
import GaloisForLFunctions.HTGeometry.DisjointPacketSpectrum
import GaloisForLFunctions.HTGeometry.GenericLocalCollisionExtremality

/-!
# One interaction knob activates the full projective rank above an onsite background

Splitting the coefficient space of a real-affine Hermitian family into an onsite background block
and an interaction direction block, almost every pair of a background and a direction spans a line
along which all but countably many coupling strengths give a maximally projective spectrum.

The uncoupled point is always exceptional: an onsite Hamiltonian is a sum of operators on disjoint
single-site packets, so its levels are sums of local levels and its anchored rational rank is at most
the number of sites times one less than the number of local levels — strictly below the maximal
rank.
-/

open Filter MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section BlockActivation

/-- **Countable exceptional coupling set along a one-knob line, complex obstructions.** -/
theorem countable_exceptional_blockLine_complexSpectral
    {m : ℕ} (p : Fin m → Prop) [DecidablePred p] {I : Type*} [Fintype I]
    (coefficient : Fin (Fintype.card I) → MvPolynomial (Fin m) ℂ)
    (hwitness : ∀ k : I → ℤ, SpectralCharacterBalanced k → k ≠ 0 →
      ∃ x : Fin m → ℝ, MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (x t : ℂ))
        (complexSpectralCoefficientObstructionPullback coefficient k) ≠ 0) :
    ∀ᵐ va : ({i : Fin m // p i} → ℝ) × ({i : Fin m // ¬ p i} → ℝ) ∂volume,
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C, blockPoint p va.1 va.2 g ∈
          complexSpectralCoefficientProjectiveGenericSet coefficient := by
  classical
  let J := {k : I → ℤ // SpectralCharacterBalanced k ∧ k ≠ 0}
  letI : Countable J := by
    dsimp [J]
    infer_instance
  letI : Encodable J := Encodable.ofCountable J
  let P : ℕ → MvPolynomial (Fin m) ℂ := fun r =>
    match (Encodable.decode r : Option J) with
    | none => 1
    | some k => complexSpectralCoefficientObstructionPullback coefficient k.1
  have hPne : ∀ r, P r ≠ 0 := by
    intro r
    unfold P
    split
    · exact one_ne_zero
    · rename_i k _
      obtain ⟨x, hx⟩ := hwitness k.1 k.2.1 k.2.2
      intro hzero
      rw [hzero] at hx
      simp at hx
  filter_upwards [countable_complexBlockLineAvoidance_ae p P hPne] with va hva
  obtain ⟨C, hC, hgC⟩ := hva
  refine ⟨C, hC, fun g hg => ?_⟩
  intro k hbalanced hk
  have hj := hgC g hg (Encodable.encode (⟨k, hbalanced, hk⟩ : J))
  simpa [P, Encodable.encodek] using hj

/-- **Countable exceptional coupling set along a one-knob line, polynomial Hermitian family.** -/
theorem countable_exceptional_blockLine_polynomialMatrixGenericSet
    {m : ℕ} (p : Fin m → Prop) [DecidablePred p] {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ))
    (p₀ : Fin m → ℝ) (energy : I → ℝ)
    (hmax : MaximallyProjectiveEnergy energy) (hinjective : Function.Injective energy)
    (hroot : ∀ i, matrixCharpolyRelation
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (p₀ t : ℂ))),
        (energy i : ℂ)) = 0) :
    ∀ᵐ va : ({i : Fin m // p i} → ℝ) × ({i : Fin m // ¬ p i} → ℝ) ∂volume,
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C, blockPoint p va.1 va.2 g ∈ polynomialMatrixProjectiveGenericSet M := by
  have hcoefficient : ∀ j,
      MvPolynomial.eval₂ (RingHom.id ℂ) (fun t => (p₀ t : ℂ))
          (matrixCharacteristicElementaryPolynomial M j) =
        MvPolynomial.eval₂ (Rat.castHom ℂ) (fun a => (energy a : ℂ))
          (MvPolynomial.esymm I ℚ (j.1 + 1)) := by
    intro j
    rw [eval_matrixCharacteristicElementaryPolynomial]
    exact matrixCharacteristicElementaryCoefficient_eq_rootPacket
      _ (fun i => ((energy i : ℝ) : ℂ))
      (fun a b h => hinjective (Complex.ofReal_injective h)) hroot j
  exact countable_exceptional_blockLine_complexSpectral p
    (matrixCharacteristicElementaryPolynomial M)
    fun k hbalanced hk => ⟨p₀,
      complexSpectralCoefficientObstructionPullback_has_real_witness
        (matrixCharacteristicElementaryPolynomial M) p₀ energy hmax hcoefficient k hbalanced hk⟩

/-- **Countable exceptional coupling set along a one-knob line, maximal-rank locus.** -/
theorem countable_exceptional_blockLine_polynomialHermitianMatrixMaximalSet
    {m : ℕ} (p : Fin m → Prop) [DecidablePred p] {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I (MvPolynomial (Fin m) ℂ))
    (hhermitian : ∀ x : Fin m → ℝ,
      (M.map (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (x t : ℂ)))).IsHermitian)
    (p₀ : Fin m → ℝ)
    (hmax : MaximallyProjectiveEnergy (hhermitian p₀).eigenvalues) :
    ∀ᵐ va : ({i : Fin m // p i} → ℝ) × ({i : Fin m // ¬ p i} → ℝ) ∂volume,
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C, blockPoint p va.1 va.2 g ∈
          polynomialHermitianMatrixMaximalSet M hhermitian := by
  have hline := countable_exceptional_blockLine_polynomialMatrixGenericSet p M p₀
    (hhermitian p₀).eigenvalues hmax hmax.injective
    (hermitianEigenvalue_matrixCharpolyRelation _ (hhermitian p₀))
  filter_upwards [hline] with va hav
  obtain ⟨C, hC, hgC⟩ := hav
  refine ⟨C, hC, fun g hg => ?_⟩
  exact maximallyProjectiveEnergy_eigenvalues_of_mem_polynomialMatrixGenericSet
    M _ (hgC g hg) (hhermitian _)

/-- **One-knob activation for a real-affine Hermitian family with a coordinate splitting.** -/
theorem countable_exceptional_blockLine_realAffineHermitianMaximalSet
    {m : ℕ} (p : Fin m → Prop) [DecidablePred p] {I : Type*} [Fintype I] [DecidableEq I]
    (base : Matrix I I ℂ) (generator : Fin m → Matrix I I ℂ)
    (hbase : base.IsHermitian) (hgenerator : ∀ t, (generator t).IsHermitian)
    (p₀ : Fin m → ℝ)
    (hmax : MaximallyProjectiveEnergy
      (realAffineMatrix_isHermitian base generator hbase hgenerator p₀).eigenvalues) :
    ∀ᵐ va : ({i : Fin m // p i} → ℝ) × ({i : Fin m // ¬ p i} → ℝ) ∂volume,
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C, blockPoint p va.1 va.2 g ∈
          realAffineHermitianMaximalSet base generator hbase hgenerator := by
  have hherm : ∀ x : Fin m → ℝ,
      (((realAffineMatrixPolynomial base generator)).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => (x t : ℂ)))).IsHermitian := by
    intro x
    rw [eval_realAffineMatrixPolynomial]
    exact realAffineMatrix_isHermitian base generator hbase hgenerator x
  have hmax₀ : MaximallyProjectiveEnergy (hherm p₀).eigenvalues := by
    have heig : (hherm p₀).eigenvalues =
        (realAffineMatrix_isHermitian base generator hbase hgenerator p₀).eigenvalues := by
      apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff (hherm p₀)
        (realAffineMatrix_isHermitian base generator hbase hgenerator p₀)).2
      rw [eval_realAffineMatrixPolynomial]
    rw [heig]
    exact hmax
  exact countable_exceptional_blockLine_polynomialHermitianMatrixMaximalSet p
    (realAffineMatrixPolynomial base generator) hherm p₀ hmax₀

end BlockActivation

section OnsiteCeiling

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] [∀ v, Nonempty (A v)]

/-- **Onsite rank ceiling.**  A sum of operators on disjoint single-site packets has anchored
rational rank at most the sum over sites of one less than the number of local levels. -/
theorem anchoredTemporalRank_sum_liftLocalMatrix_le
    (B : ∀ c : V, Matrix (LocalConfiguration A {c}) (LocalConfiguration A {c}) ℂ)
    (hB : ∀ c, (B c).IsHermitian) (r : ∀ v, A v) :
    anchoredTemporalRank
        (isHermitian_sum_liftLocalMatrix (fun c : V => ({c} : Finset V)) B hB
          Finset.univ).eigenvalues r ≤
      ∑ c : V, (Fintype.card (LocalConfiguration A ({c} : Finset V)) - 1) := by
  classical
  have hdisj : ∀ c d : V, c ≠ d →
      Disjoint ({c} : Finset V) ({d} : Finset V) := by
    intro c d hcd
    simp [hcd]
  have hrange := range_eigenvalues_sum_liftLocalMatrix (A := A)
    (fun c : V => ({c} : Finset V)) hdisj B hB Finset.univ
  refine anchoredTemporalRank_le_of_separable _ (fun c => (hB c).eigenvalues) ?_ r
  rw [hrange]


/-- **Onsite spectra are never maximally projective.**  On at least two sites with at least two
levels each, the anchored rank of an onsite Hamiltonian is strictly below the maximal rank. -/
theorem not_maximallyProjective_sum_liftLocalMatrix [Nonempty V]
    {n q : ℕ} (hn : 2 ≤ n) (hq : 2 ≤ q)
    (hV : Fintype.card V = n) (hA : ∀ v, Fintype.card (A v) = q)
    (B : ∀ c : V, Matrix (LocalConfiguration A {c}) (LocalConfiguration A {c}) ℂ)
    (hB : ∀ c, (B c).IsHermitian) :
    ¬ MaximallyProjectiveEnergy
      (isHermitian_sum_liftLocalMatrix (fun c : V => ({c} : Finset V)) B hB
        Finset.univ).eigenvalues := by
  classical
  intro hmax
  obtain ⟨r⟩ : Nonempty (∀ v, A v) := inferInstance
  have hle := anchoredTemporalRank_sum_liftLocalMatrix_le B hB r
  have hcardLocal : ∀ c : V, Fintype.card (LocalConfiguration A ({c} : Finset V)) = q := by
    intro c
    rw [show Fintype.card (LocalConfiguration A ({c} : Finset V)) = Fintype.card (A c) by
      simp [LocalConfiguration]]
    exact hA c
  have hsum : (∑ c : V, (Fintype.card (LocalConfiguration A ({c} : Finset V)) - 1)) =
      n * (q - 1) := by
    rw [Finset.sum_congr rfl fun c _ => by rw [hcardLocal c], Finset.sum_const,
      Finset.card_univ, hV, smul_eq_mul]
  have hcardTotal : Fintype.card (∀ v, A v) = q ^ n := by
    rw [Fintype.card_pi, Finset.prod_congr rfl fun v _ => hA v, Finset.prod_const,
      Finset.card_univ, hV]
  have heq := anchoredTemporalRank_eq_card_sub_one_of_maximallyProjective _ hmax r
  rw [hsum] at hle
  rw [heq, hcardTotal] at hle
  exact absurd hle (Nat.not_le.mpr (separable_rank_lt n q hn hq))

end OnsiteCeiling

section OneKnobOnsite

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] [∀ v, Nonempty (A v)]

/-- **One-knob activation above an onsite background.**  For almost every onsite background and
interaction direction, all but countably many coupling strengths give a maximally projective
spectrum, and the uncoupled point is always exceptional. -/
theorem countable_exceptional_blockLine_onsite
    {n q : ℕ} (hn : 2 ≤ n) (hq : 2 ≤ q)
    (hV : Fintype.card V = n) (hA : ∀ v, Fintype.card (A v) = q)
    {m : ℕ} (p : Fin m → Prop) [DecidablePred p]
    (generator : Fin m → Matrix (∀ v, A v) (∀ v, A v) ℂ)
    (hgenerator : ∀ t, (generator t).IsHermitian)
    (p₀ : Fin m → ℝ)
    (hmax : MaximallyProjectiveEnergy
      (realAffineMatrix_isHermitian 0 generator Matrix.isHermitian_zero hgenerator p₀).eigenvalues)
    (honsite : ∀ (v : {i : Fin m // p i} → ℝ) (a : {i : Fin m // ¬ p i} → ℝ),
      ∃ B : ∀ c : V, Matrix (LocalConfiguration A {c}) (LocalConfiguration A {c}) ℂ,
      ∃ _hB : ∀ c, (B c).IsHermitian,
        realAffineMatrix 0 generator (blockPoint p v a 0) =
          ∑ c : V, liftLocalMatrix ({c} : Finset V) (B c)) :
    ∀ᵐ va : ({i : Fin m // p i} → ℝ) × ({i : Fin m // ¬ p i} → ℝ) ∂volume,
      ∃ C : Set ℝ, C.Countable ∧ (0 : ℝ) ∈ C ∧
        ∀ g ∉ C, blockPoint p va.1 va.2 g ∈
          realAffineHermitianMaximalSet 0 generator Matrix.isHermitian_zero hgenerator := by
  classical
  filter_upwards [countable_exceptional_blockLine_realAffineHermitianMaximalSet p
    0 generator Matrix.isHermitian_zero hgenerator p₀ hmax] with va hva
  obtain ⟨C, hC, hgC⟩ := hva
  have hzero : blockPoint p va.1 va.2 0 ∉
      realAffineHermitianMaximalSet 0 generator Matrix.isHermitian_zero hgenerator := by
    intro hmem
    obtain ⟨B, hB, hEq⟩ := honsite va.1 va.2
    have hproj := maximallyProjective_of_mem_realAffineHermitianMaximalSet
      0 generator Matrix.isHermitian_zero hgenerator hmem
    have hherm2 := isHermitian_sum_liftLocalMatrix (fun c : V => ({c} : Finset V)) B hB
      Finset.univ
    have heig : (realAffineMatrix_isHermitian 0 generator Matrix.isHermitian_zero hgenerator
        (blockPoint p va.1 va.2 0)).eigenvalues = hherm2.eigenvalues :=
      (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff _ _).2 (by rw [hEq])
    rw [heig] at hproj
    exact not_maximallyProjective_sum_liftLocalMatrix hn hq hV hA B hB hproj
  refine ⟨C, hC, ?_, hgC⟩
  by_contra h0
  exact hzero (hgC 0 h0)

end OneKnobOnsite

end

end GaloisForLFunctions.HTGeometry
