import GaloisForLFunctions.RHTower.FiniteAtomicObserverTimeGapLaw

/-!
# All-pair quantum-return rigidity

Every balanced two-level observer sees one squared labelled energy gap.  For
an arbitrary nonempty label type, the family of all such return records
therefore determines the entire energy assignment up to exactly two
unobservable operations: a common translation and a common reflection.

The label type is not assumed finite.  Each interrogation uses only a
two-point probability spectrum, while the collection of interrogations may
range over an infinite energy family.
-/

open MeasureTheory

noncomputable section

namespace RHTower

/-- Equal weights for an addressable balanced two-level observer. -/
def balancedPairWeight : Fin 2 → ℝ := ![1 / 2, 1 / 2]

/-- Two labelled levels selected from an arbitrary energy assignment. -/
def labelledPairEnergy
    {I : Type*} (energy : I → ℝ) (i j : I) : Fin 2 → ℝ :=
  ![energy i, energy j]

/-- Projective return probability of a balanced labelled pair. -/
def labelledPairReturnRecord
    {I : Type*} (energy : I → ℝ) (i j : I) (t : ℝ) : ℝ :=
  projectiveReturnRecord
    (finiteAtomicObserverSpectrum balancedPairWeight
      (labelledPairEnergy energy i j)) t

theorem balancedPairWeight_nonneg :
    ∀ i, 0 ≤ balancedPairWeight i := by
  intro i
  fin_cases i <;> norm_num [balancedPairWeight]

theorem balancedPairWeight_sum :
    ∑ i, balancedPairWeight i = 1 := by
  simp [balancedPairWeight, Fin.sum_univ_two]
  norm_num

/-- A balanced two-level return is exactly the cosine record of its labelled
energy gap. -/
theorem labelledPairReturnRecord_eq_cos
    {I : Type*} (energy : I → ℝ) (i j : I) (t : ℝ) :
    labelledPairReturnRecord energy i j t =
      (1 + Real.cos (t * (energy i - energy j))) / 2 := by
  apply Complex.ofReal_injective
  change
    (projectiveReturnRecord
      (finiteAtomicObserverSpectrum balancedPairWeight
        (labelledPairEnergy energy i j)) t : ℂ) =
      (((1 + Real.cos (t * (energy i - energy j))) / 2 : ℝ) : ℂ)
  rw [projectiveReturnRecord_finiteAtomicObserverSpectrum
    balancedPairWeight (labelledPairEnergy energy i j)
    balancedPairWeight_nonneg balancedPairWeight_sum t]
  simp [Fintype.sum_prod_type, balancedPairWeight, labelledPairEnergy,
    GaloisForLFunctions.HTGeometry.energyGapCocycle,
    Fin.sum_univ_two, Complex.exp_mul_I,
    Complex.ofReal_cos]
  ring_nf
  have hneg :
      (-((t : ℂ) * (energy i : ℂ)) +
          (t : ℂ) * (energy j : ℂ)) =
        -((t : ℂ) * (energy i : ℂ) -
          (t : ℂ) * (energy j : ℂ)) := by
    ring
  rw [hneg]
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- Equality of all cosine times forces equality of squared frequencies. -/
theorem cos_mul_eq_cos_mul_all_imp_sq_eq
    {a b : ℝ} (h : ∀ t : ℝ, Real.cos (t * a) = Real.cos (t * b)) :
    a ^ 2 = b ^ 2 := by
  have hf :
      (fun t : ℝ => Real.cos (t * a)) =
        (fun t : ℝ => Real.cos (t * b)) := funext h
  have hd :=
    congrArg (fun f : ℝ → ℝ => deriv (deriv f) 0) hf
  have hfirst (c : ℝ) :
      deriv (fun t : ℝ => Real.cos (t * c)) =
        fun t : ℝ => -Real.sin (t * c) * c := by
    funext t
    have hc :=
      (Real.hasDerivAt_cos (t * c)).comp t
        ((hasDerivAt_id t).mul_const c)
    convert hc.deriv using 1
    all_goals ring
  have hsecond (c : ℝ) :
      deriv (deriv (fun t : ℝ => Real.cos (t * c))) 0 =
        -c ^ 2 := by
    rw [hfirst c]
    have hs :=
      (Real.hasDerivAt_sin (0 * c)).comp 0
        ((hasDerivAt_id 0).mul_const c)
    have hscaled := hs.neg.mul_const c
    convert hscaled.deriv using 1
    all_goals norm_num
    all_goals ring
  change
    deriv (deriv (fun t : ℝ => Real.cos (t * a))) 0 =
      deriv (deriv (fun t : ℝ => Real.cos (t * b))) 0 at hd
  rw [hsecond a, hsecond b] at hd
  linarith

/-- Complete all-pair return equality determines every squared labelled
gap. -/
theorem pairReturn_eq_all_imp_gap_sq_eq
    {I : Type*} (left right : I → ℝ)
    (h :
      ∀ i j t,
        labelledPairReturnRecord left i j t =
          labelledPairReturnRecord right i j t) :
    ∀ i j, (left i - left j) ^ 2 =
      (right i - right j) ^ 2 := by
  intro i j
  apply cos_mul_eq_cos_mul_all_imp_sq_eq
  intro t
  have ht := h i j t
  rw [labelledPairReturnRecord_eq_cos,
    labelledPairReturnRecord_eq_cos] at ht
  linarith

/-- **One-dimensional labelled distance rigidity.**  Any two real
assignments with the same squared distance between every labelled pair
differ by one global translation and either the identity or one global
reflection. -/
theorem pairwise_sq_gap_rigidity
    {I : Type*} [Nonempty I]
    (left right : I → ℝ)
    (hgap :
      ∀ i j, (left i - left j) ^ 2 =
        (right i - right j) ^ 2) :
    ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
      ∃ shift : ℝ, ∀ i, right i = sign * left i + shift := by
  classical
  by_cases hconst : ∀ i j, left i = left j
  · let base : I := Classical.choice ‹Nonempty I›
    refine ⟨1, Or.inl rfl, right base - left base, ?_⟩
    intro i
    have hleft : left i = left base := hconst i base
    have hrightSq :
        (right i - right base) ^ 2 = 0 := by
      rw [← hgap i base, hleft, sub_self, zero_pow (by omega)]
    have hright : right i = right base := by
      have hz : right i - right base = 0 :=
        sq_eq_zero_iff.mp hrightSq
      linarith
    rw [hleft, hright]
    ring
  · push Not at hconst
    obtain ⟨base, anchor, hanchor⟩ := hconst
    let a := left anchor - left base
    let b := right anchor - right base
    have ha : a ≠ 0 := sub_ne_zero.mpr hanchor.symm
    have hab : a ^ 2 = b ^ 2 := by
      dsimp [a, b]
      exact hgap anchor base
    have hfactor : (b - a) * (b + a) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with hplus | hminus
    · refine ⟨1, Or.inl rfl, right base - left base, ?_⟩
      intro i
      have hbi : b = a := sub_eq_zero.mp hplus
      have hi0 := hgap i base
      have hi1 := hgap i anchor
      have hi1' :
          ((left i - left base) - a) ^ 2 =
            ((right i - right base) - b) ^ 2 := by
        dsimp [a, b]
        convert hi1 using 1 <;> ring
      rw [hbi] at hi1'
      have hprod :
          a * ((right i - right base) -
            (left i - left base)) = 0 := by
        nlinarith [hi0, hi1', hbi]
      have hzero :
          (right i - right base) -
            (left i - left base) = 0 :=
        (mul_eq_zero.mp hprod).resolve_left ha
      have hy :
          right i - right base = left i - left base := by
        linarith
      linarith
    · refine ⟨-1, Or.inr rfl, right base + left base, ?_⟩
      intro i
      have hbi : b = -a := by linarith
      have hi0 := hgap i base
      have hi1 := hgap i anchor
      have hi1' :
          ((left i - left base) - a) ^ 2 =
            ((right i - right base) - b) ^ 2 := by
        dsimp [a, b]
        convert hi1 using 1 <;> ring
      rw [hbi] at hi1'
      have hprod :
          a * ((right i - right base) +
            (left i - left base)) = 0 := by
        nlinarith [hi0, hi1', hbi]
      have hzero :
          (right i - right base) +
            (left i - left base) = 0 :=
        (mul_eq_zero.mp hprod).resolve_left ha
      have hy :
          right i - right base = -(left i - left base) := by
        linarith
      linarith

/-- Equality of every balanced labelled-pair return record reconstructs an
arbitrary nonempty energy family up to translation and reflection. -/
theorem labelledPairReturnRecord_rigidity
    {I : Type*} [Nonempty I]
    (left right : I → ℝ)
    (h :
      ∀ i j t,
        labelledPairReturnRecord left i j t =
          labelledPairReturnRecord right i j t) :
    ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
      ∃ shift : ℝ, ∀ i, right i = sign * left i + shift := by
  exact pairwise_sq_gap_rigidity left right
    (pairReturn_eq_all_imp_gap_sq_eq left right h)

/-- Common translation and reflection are invisible to every balanced
labelled-pair return record. -/
theorem labelledPairReturnRecord_translation_reflection_invariant
    {I : Type*} (energy : I → ℝ)
    (sign shift : ℝ) (hsign : sign = 1 ∨ sign = -1) :
    ∀ i j t,
      labelledPairReturnRecord
          (fun k => sign * energy k + shift) i j t =
        labelledPairReturnRecord energy i j t := by
  intro i j t
  rw [labelledPairReturnRecord_eq_cos,
    labelledPairReturnRecord_eq_cos]
  rcases hsign with rfl | rfl
  · congr 2
    ring
  · rw [show
      t * ((-1 : ℝ) * energy i + shift -
        ((-1 : ℝ) * energy j + shift)) =
        -(t * (energy i - energy j)) by ring]
    rw [Real.cos_neg]

/-- **All-pair quantum-return rigidity law.**  Two arbitrary nonempty
labelled energy families have exactly the same balanced-pair return record
for every pair and every time if and only if they differ by one global
energy translation and, possibly, one global reversal. -/
theorem labelledPairReturnRecord_complete_iff
    {I : Type*} [Nonempty I]
    (left right : I → ℝ) :
    (∀ i j t,
        labelledPairReturnRecord left i j t =
          labelledPairReturnRecord right i j t) ↔
      ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
        ∃ shift : ℝ, ∀ i,
          right i = sign * left i + shift := by
  constructor
  · exact labelledPairReturnRecord_rigidity left right
  · rintro ⟨sign, hsign, shift, hright⟩ i j t
    have hrightFun :
        right = fun k => sign * left k + shift :=
      funext hright
    rw [hrightFun]
    exact
      (labelledPairReturnRecord_translation_reflection_invariant
        left sign shift hsign i j t).symm

end RHTower
