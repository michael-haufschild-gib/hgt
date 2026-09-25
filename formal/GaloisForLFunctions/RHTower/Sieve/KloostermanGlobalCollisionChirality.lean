import GaloisForLFunctions.RHTower.Sieve.KloostermanGlobalCollisionExactReal
import GaloisForLFunctions.RHTower.Sieve.KloostermanPhysicalResidueModulusBilinear

/-!
# Orientation chirality of the global Kloosterman collision receiver

Under pairwise-coprime clocks the factor-two collision bound has an exact
polarization deficit: half the squared difference between forced orientation
mates. Orientation reversal conjugates the complete modulus weights and source.
For physical Dirichlet phases with real base data, conjugation reverses height,
so the sole collision saving is exactly the odd-in-height tuple energy. This
identifies a quantitative producer obligation; it does not estimate that energy.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

private theorem normSq_pair_polarization (u v : ℂ) :
    Complex.normSq (u + v) + Complex.normSq (u - v) =
      2 * (Complex.normSq u + Complex.normSq v) := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im]
  ring

private theorem exact_two_fiber_defect
    {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (ν : α → β) (flip : α → α) (a : α → ℂ)
    (hν : ∀ p, ν (flip p) = ν p)
    (hne : ∀ p, flip p ≠ p)
    (hflip : ∀ p, flip (flip p) = p)
    (hcard : ∀ p, (Finset.univ.filter fun u : α => ν p = ν u).card = 2) :
    (∑ z : β, Complex.normSq (∑ p : α, if ν p = z then a p else 0)) +
      (1 / 2 : ℝ) * ∑ p : α, Complex.normSq (a p - a (flip p)) =
      2 * ∑ p : α, Complex.normSq (a p) := by
  classical
  have hpoint : ∀ z : β,
      Complex.normSq (∑ p : α, if ν p = z then a p else 0) +
        (1 / 2 : ℝ) * (∑ p : α,
          if ν p = z then Complex.normSq (a p - a (flip p)) else 0) =
        2 * ∑ p : α, (if ν p = z then Complex.normSq (a p) else 0) := by
    intro z
    let S : Finset α := Finset.univ.filter fun p => ν p = z
    by_cases hS : S.Nonempty
    · obtain ⟨p, hp⟩ := hS
      have hpz : ν p = z := (Finset.mem_filter.mp hp).2
      have hfpz : ν (flip p) = z := (hν p).trans hpz
      have hmemflip : flip p ∈ S := by simp [S, hfpz]
      have hcardS : S.card = 2 := by
        have hfilter : (Finset.univ.filter fun u : α => ν p = ν u) = S := by
          ext u
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
          rw [hpz]
          exact eq_comm
        rw [← hfilter]
        exact hcard p
      have hpaircard : ({p, flip p} : Finset α).card = 2 :=
        Finset.card_pair ((hne p).symm)
      have hsub : ({p, flip p} : Finset α) ⊆ S := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hp
        · exact hmemflip
      have hSeq : S = {p, flip p} := by
        symm
        apply Finset.eq_of_subset_of_card_le hsub
        omega
      rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]
      change Complex.normSq (∑ u ∈ S, a u) +
          (1 / 2 : ℝ) * ∑ u ∈ S, Complex.normSq (a u - a (flip u)) =
        2 * ∑ u ∈ S, Complex.normSq (a u)
      rw [hSeq, Finset.sum_pair ((hne p).symm),
        Finset.sum_pair ((hne p).symm), Finset.sum_pair ((hne p).symm), hflip]
      have hminus : Complex.normSq (a (flip p) - a p) =
          Complex.normSq (a p - a (flip p)) := by
        rw [← neg_sub, Complex.normSq_neg]
      rw [hminus]
      have hpolar := normSq_pair_polarization (a p) (a (flip p))
      nlinarith
    · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
      rw [← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]
      change Complex.normSq (∑ u ∈ S, a u) +
          (1 / 2 : ℝ) * ∑ u ∈ S, Complex.normSq (a u - a (flip u)) =
        2 * ∑ u ∈ S, Complex.normSq (a u)
      simp [hEmpty]
  have hcount (D : α → ℝ) :
      (∑ z : β, ∑ p : α, if ν p = z then D p else 0) = ∑ p : α, D p := by
    rw [Finset.sum_comm]
    apply Fintype.sum_congr
    intro p
    simp
  calc
    (∑ z : β, Complex.normSq (∑ p : α, if ν p = z then a p else 0)) +
        (1 / 2 : ℝ) * ∑ p : α, Complex.normSq (a p - a (flip p)) =
      ∑ z : β,
        (Complex.normSq (∑ p : α, if ν p = z then a p else 0) +
          (1 / 2 : ℝ) * ∑ p : α,
            if ν p = z then Complex.normSq (a p - a (flip p)) else 0) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hcount]
    _ = ∑ z : β, 2 * ∑ p : α,
          if ν p = z then Complex.normSq (a p) else 0 :=
      Finset.sum_congr rfl (fun z _ => hpoint z)
    _ = 2 * ∑ p : α, Complex.normSq (a p) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Fintype.sum_congr
      intro p
      simp

private theorem kloostermanGlobalCrossTupleReverseNeg_involutive
    {Q : Finset ℕ} (p : KloostermanGlobalCrossTuple Q) :
    kloostermanGlobalCrossTupleReverseNeg
        (kloostermanGlobalCrossTupleReverseNeg p) = p := by
  rcases p with ⟨q, r, ⟨⟨x, y⟩, hqr⟩⟩
  unfold kloostermanGlobalCrossTupleReverseNeg
  simp only [neg_neg]

theorem kloostermanGlobalFrequencyCollisionEnergy_add_chirality_eq_two_crossTuple
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (hpos : ∀ q ∈ Q, 0 < q)
    (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b +
      (1 / 2 : ℝ) * ∑ p : KloostermanGlobalCrossTuple Q,
        Complex.normSq
          (kloostermanGlobalCrossTupleCoefficient Q w B b p -
            kloostermanGlobalCrossTupleCoefficient Q w B b
              (kloostermanGlobalCrossTupleReverseNeg p)) =
      2 * ∑ p : KloostermanGlobalCrossTuple Q,
        Complex.normSq (kloostermanGlobalCrossTupleCoefficient Q w B b p) := by
  unfold kloostermanGlobalFrequencyCollisionEnergy
  simp_rw [kloostermanGlobalFrequencyCoefficient_eq_crossTupleSum, Complex.sq_norm]
  exact exact_two_fiber_defect
    (kloostermanLiteralCrossTupleFrequency Q)
    (kloostermanGlobalCrossTupleReverseNeg)
    (kloostermanGlobalCrossTupleCoefficient Q w B b)
    (kloostermanLiteralCrossTupleFrequency_reverseNeg Q)
    (kloostermanGlobalCrossTupleReverseNeg_ne)
    kloostermanGlobalCrossTupleReverseNeg_involutive
    (card_filter_kloostermanLiteralCrossTupleFrequency_eq_two Q hpair hpos)

/-- Negating the unit frequency is conjugation of the complete source data. -/
theorem kloostermanSourceFourier_neg_eq_star_conjSource
    (q : ℕ) [NeZero q] (B : Finset ℕ) (b : ℕ → ℂ)
    (x : (ZMod q)ˣ) :
    kloostermanSourceFourier q B b (-x) =
      star (kloostermanSourceFourier q B (fun n => star (b n)) x) := by
  unfold kloostermanSourceFourier
  change (∑ n ∈ B, b n * ZMod.stdAddChar
      ((n : ZMod q) * (((-x)⁻¹ : (ZMod q)ˣ) : ZMod q))) =
    (starRingEnd ℂ) (∑ n ∈ B, star (b n) * ZMod.stdAddChar
      ((n : ZMod q) * ((x⁻¹ : (ZMod q)ˣ) : ZMod q)))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n hn
  conv_rhs => rw [map_mul]
  simp only [starRingEnd_apply, star_star]
  congr 1
  rw [star_stdAddChar_eq_neg q]
  congr 1
  simp

/-- The orientation mate is the same tuple coefficient after conjugating all source data. -/
theorem kloostermanGlobalCrossTupleCoefficient_reverseNeg_eq_conjData
    (Q : Finset ℕ) (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ)
    (p : KloostermanGlobalCrossTuple Q) :
    kloostermanGlobalCrossTupleCoefficient Q w B b
        (kloostermanGlobalCrossTupleReverseNeg p) =
      kloostermanGlobalCrossTupleCoefficient Q
        (fun q => star (w q)) B (fun n => star (b n)) p := by
  rcases p with ⟨q, r, ⟨⟨x, y⟩, hqr⟩⟩
  unfold kloostermanGlobalCrossTupleReverseNeg kloostermanGlobalCrossTupleCoefficient
  simp only
  rw [kloostermanSourceFourier_neg_eq_star_conjSource (r + 1) B b y,
    kloostermanSourceFourier_neg_eq_star_conjSource (q + 1) B b x]
  simp only [star_star]
  ring

/-- Exact orientation deficit equals the coefficient's conjugation-odd energy. -/
theorem kloostermanGlobalFrequencyCollisionEnergy_add_conjOdd_eq_two_crossTuple
    (Q : Finset ℕ)
    (hpair : (Q : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun q => q + 1)))
    (hpos : ∀ q ∈ Q, 0 < q)
    (w : ℕ → ℂ) (B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanGlobalFrequencyCollisionEnergy Q w B b +
      (1 / 2 : ℝ) * ∑ p : KloostermanGlobalCrossTuple Q,
        Complex.normSq
          (kloostermanGlobalCrossTupleCoefficient Q w B b p -
            kloostermanGlobalCrossTupleCoefficient Q
              (fun q => star (w q)) B (fun n => star (b n)) p) =
      2 * ∑ p : KloostermanGlobalCrossTuple Q,
        Complex.normSq (kloostermanGlobalCrossTupleCoefficient Q w B b p) := by
  simpa only [kloostermanGlobalCrossTupleCoefficient_reverseNeg_eq_conjData] using
    kloostermanGlobalFrequencyCollisionEnergy_add_chirality_eq_two_crossTuple
      Q hpair hpos w B b

/-- Conjugating the corpus's physical Dirichlet coefficient reverses physical height. -/
theorem star_physicalDirichletTerm_eq_neg_height
    (a : ℕ → ℂ) (n : ℕ) (t : ℝ) :
    star (physicalDirichletTerm a n t) =
      physicalDirichletTerm (fun k => star (a k)) n (-t) := by
  unfold physicalDirichletTerm
  change (starRingEnd ℂ) (a n * Complex.exp
      (((2 * Real.pi * ((t / (2 * Real.pi)) * Real.log n) : ℝ) : ℂ) * Complex.I)) = _
  rw [map_mul, ← Complex.exp_conj]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf

/-- Orientation reversal of the physical coefficient is literal height reversal for real data. -/
theorem kloostermanPhysicalCrossTupleCoefficient_reverseNeg_eq_negHeight
    (Q : Finset ℕ) (w a : ℕ → ℝ) (B : Finset ℕ) (t : ℝ)
    (p : KloostermanGlobalCrossTuple Q) :
    kloostermanGlobalCrossTupleCoefficient Q (fun q => (w q : ℂ)) B
        (fun n => physicalDirichletTerm (fun k => (a k : ℂ)) n t)
        (kloostermanGlobalCrossTupleReverseNeg p) =
      kloostermanGlobalCrossTupleCoefficient Q (fun q => (w q : ℂ)) B
        (fun n => physicalDirichletTerm (fun k => (a k : ℂ)) n (-t)) p := by
  rw [kloostermanGlobalCrossTupleCoefficient_reverseNeg_eq_conjData]
  congr 1
  · funext q
    simp
  · funext n
    rw [star_physicalDirichletTerm_eq_neg_height]
    simp

/-- Exact source-faithful prime-clock law: every collision saving is height-odd energy. -/
theorem kloostermanPrimeGlobalCollisionEnergy_add_heightOdd_eq_two_crossTuple
    (P : Finset Nat.Primes) (w a : ℕ → ℝ) (B : Finset ℕ) (t : ℝ) :
    let Q := kloostermanPrimeIndexSet (P.image Subtype.val)
    let bt : ℕ → ℂ := fun n => physicalDirichletTerm (fun k => (a k : ℂ)) n t
    let bmt : ℕ → ℂ := fun n => physicalDirichletTerm (fun k => (a k : ℂ)) n (-t)
    kloostermanGlobalFrequencyCollisionEnergy Q (fun q => (w q : ℂ)) B bt +
      (1 / 2 : ℝ) * ∑ p : KloostermanGlobalCrossTuple Q,
        Complex.normSq
          (kloostermanGlobalCrossTupleCoefficient Q (fun q => (w q : ℂ)) B bt p -
            kloostermanGlobalCrossTupleCoefficient Q (fun q => (w q : ℂ)) B bmt p) =
      2 * ∑ p : KloostermanGlobalCrossTuple Q,
        Complex.normSq
          (kloostermanGlobalCrossTupleCoefficient Q (fun q => (w q : ℂ)) B bt p) := by
  dsimp only
  have hprime : ∀ p ∈ P.image Subtype.val, p.Prime := by
    intro p hp
    obtain ⟨p, _hp, rfl⟩ := Finset.mem_image.mp hp
    exact p.property
  have h := kloostermanGlobalFrequencyCollisionEnergy_add_chirality_eq_two_crossTuple
    (kloostermanPrimeIndexSet (P.image Subtype.val))
    (kloostermanPrimeIndexSet_pairwise_coprime _ hprime)
    (kloostermanPrimeIndexSet_pos _ hprime)
    (fun q => (w q : ℂ)) B
    (fun n => physicalDirichletTerm (fun k => (a k : ℂ)) n t)
  simpa only [kloostermanPhysicalCrossTupleCoefficient_reverseNeg_eq_negHeight] using h

end
end RHTower.Sieve
