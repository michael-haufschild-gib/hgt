import GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierPointedKreinBoundaryRelation

open Complex
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower

noncomputable section

def sourceHorizontalSecondCartierKreinHermitianIncidence
    (w : SourceHorizontalSecondCartierKreinJet) : ℂ :=
  w.1 * star (w.2.1 + w.2.2)

def sourceHorizontalSecondCartierKreinPolarizedBoundary
    (c : ℂ) (v : SourceHorizontalBilateralSecondJetSource)
    (w : SourceHorizontalSecondCartierKreinJet) : Prop :=
  (v, w) ∈ sourceHorizontalSecondCartierKreinBoundaryRelation c ∧
    sourceHorizontalSecondCartierKreinHermitianIncidence w = 2 * star c

def sourceHorizontalSecondCartierKreinPolarizedForward (c : ℂ) :
    SourceHorizontalSecondCartierKreinJet := (2, (c, 0))

def sourceHorizontalSecondCartierKreinPolarizedInverse (c : ℂ) :
    SourceHorizontalSecondCartierKreinJet := (2, (0, c))

def sourceHorizontalSecondCartierKreinPolarizedGhost (c : ℂ) :
    SourceHorizontalSecondCartierKreinJet :=
  sourceHorizontalSecondCartierKreinUnit +
    sourceHorizontalSecondCartierKreinGhost c

theorem sourceHorizontalSecondCartierKreinHermitianIncidence_transfer
    {lam : ℂ} (hlam : lam ≠ 0) (w : SourceHorizontalSecondCartierKreinJet) :
    sourceHorizontalSecondCartierKreinHermitianIncidence
        (sourceHorizontalSecondCartierKreinJetTransfer lam w) =
      sourceHorizontalSecondCartierKreinHermitianIncidence w := by
  rw [sourceHorizontalSecondCartierKreinHermitianIncidence,
    sourceHorizontalSecondCartierKreinJetTransfer]
  rw [sourceHorizontalSecondCartierPointedKrein_sourceTransfer_sum,
    star_mul, star_inv₀, star_star]
  field_simp [hlam]
  rw [sourceHorizontalSecondCartierKreinHermitianIncidence]

theorem sourceHorizontalSecondCartierKreinPolarizedBoundary_transfer
    {lam : ℂ} (hlam : lam ≠ 0) (c : ℂ)
    (v : SourceHorizontalBilateralSecondJetSource)
    (w : SourceHorizontalSecondCartierKreinJet)
    (h : sourceHorizontalSecondCartierKreinPolarizedBoundary c v w) :
    sourceHorizontalSecondCartierKreinPolarizedBoundary c
      (sourceHorizontalSecondCartierKreinSourceTransfer lam v)
      (sourceHorizontalSecondCartierKreinJetTransfer lam w) := by
  exact ⟨sourceHorizontalSecondCartierPointedKrein_relation_covariant c lam v w h.1,
    (sourceHorizontalSecondCartierKreinHermitianIncidence_transfer hlam w).trans h.2⟩

theorem sourceHorizontalSecondCartierKreinHermitianIncidence_swap
    (w : SourceHorizontalSecondCartierKreinJet) :
    sourceHorizontalSecondCartierKreinHermitianIncidence
        (sourceHorizontalSecondCartierKreinJetSwap w) =
      sourceHorizontalSecondCartierKreinHermitianIncidence w := by
  rcases w with ⟨u, a, b⟩
  change u * star (b + a) = u * star (a + b)
  rw [add_comm]

theorem sourceHorizontalSecondCartierKreinPolarizedBoundary_swap
    (c : ℂ) (v : SourceHorizontalBilateralSecondJetSource)
    (w : SourceHorizontalSecondCartierKreinJet)
    (h : sourceHorizontalSecondCartierKreinPolarizedBoundary c v w) :
    sourceHorizontalSecondCartierKreinPolarizedBoundary c
      (sourceHorizontalSecondCartierKreinSourceSwap v)
      (sourceHorizontalSecondCartierKreinJetSwap w) := by
  exact ⟨sourceHorizontalSecondCartierPointedKrein_swap_relation c v w h.1,
    (sourceHorizontalSecondCartierKreinHermitianIncidence_swap w).trans h.2⟩

theorem sourceHorizontalSecondCartierKreinPolarizedBoundary_forward (c : ℂ) :
    sourceHorizontalSecondCartierKreinPolarizedBoundary c
      sourceHorizontalBilateralSecondJetForward
      (sourceHorizontalSecondCartierKreinPolarizedForward c) := by
  constructor
  · change c = c * 1 ∧ 0 = c * 0
    simp
  · simp [sourceHorizontalSecondCartierKreinHermitianIncidence,
      sourceHorizontalSecondCartierKreinPolarizedForward]

theorem sourceHorizontalSecondCartierKreinPolarizedBoundary_inverse (c : ℂ) :
    sourceHorizontalSecondCartierKreinPolarizedBoundary c
      sourceHorizontalBilateralSecondJetInverse
      (sourceHorizontalSecondCartierKreinPolarizedInverse c) := by
  constructor
  · change 0 = c * 0 ∧ c = c * 1
    simp
  · simp [sourceHorizontalSecondCartierKreinHermitianIncidence,
      sourceHorizontalSecondCartierKreinPolarizedInverse]

theorem sourceHorizontalSecondCartierKreinPolarizedBoundary_ghost (c : ℂ) :
    sourceHorizontalSecondCartierKreinPolarizedBoundary c
      sourceHorizontalBilateralSecondJetGhost
      (sourceHorizontalSecondCartierKreinPolarizedGhost c) := by
  constructor
  · rw [sourceHorizontalSecondCartierPointedKrein_relation_iff]
    refine ⟨1, ?_⟩
    ext <;> simp [sourceHorizontalSecondCartierKreinPolarizedGhost,
      sourceHorizontalSecondCartierKreinUnit,
      sourceHorizontalSecondCartierKreinGhost,
      sourceHorizontalBilateralSecondJetGhost]
  · simp [sourceHorizontalSecondCartierKreinHermitianIncidence,
      sourceHorizontalSecondCartierKreinPolarizedGhost,
      sourceHorizontalSecondCartierKreinUnit,
      sourceHorizontalSecondCartierKreinGhost, star_add]
    ring

theorem sourceHorizontalSecondCartierKreinPolarizedBoundary_neg_ghost (c : ℂ) :
    sourceHorizontalSecondCartierKreinPolarizedBoundary c
      (-sourceHorizontalBilateralSecondJetGhost)
      (-sourceHorizontalSecondCartierKreinPolarizedGhost c) := by
  constructor
  · rw [sourceHorizontalSecondCartierPointedKrein_relation_iff]
    refine ⟨-1, ?_⟩
    ext <;> simp [sourceHorizontalSecondCartierKreinPolarizedGhost,
      sourceHorizontalSecondCartierKreinUnit,
      sourceHorizontalSecondCartierKreinGhost,
      sourceHorizontalBilateralSecondJetGhost]
  · simp [sourceHorizontalSecondCartierKreinHermitianIncidence,
      sourceHorizontalSecondCartierKreinPolarizedGhost,
      sourceHorizontalSecondCartierKreinUnit,
      sourceHorizontalSecondCartierKreinGhost, star_add, star_neg]
    ring

theorem sourceHorizontalSecondCartierKreinPolarizedBoundary_zero_iff (c : ℂ) :
    sourceHorizontalSecondCartierKreinPolarizedBoundary c 0 0 ↔ c = 0 := by
  constructor
  · intro h
    have hz : (0 : ℂ) = 2 * star c := by
      simpa [sourceHorizontalSecondCartierKreinHermitianIncidence] using h.2
    have hstar : star c = 0 := by
      exact (mul_eq_zero.mp hz.symm).resolve_left (by norm_num)
    exact star_eq_zero.mp hstar
  · rintro rfl
    constructor
    · exact (sourceHorizontalSecondCartierKreinBoundaryRelation 0).zero_mem
    · simp [sourceHorizontalSecondCartierKreinHermitianIncidence]

theorem sourceHorizontalSecondCartierKreinPolarizedBoundary_not_additive
    {c : ℂ} (hc : c ≠ 0) :
    sourceHorizontalSecondCartierKreinPolarizedBoundary c
        sourceHorizontalBilateralSecondJetGhost
        (sourceHorizontalSecondCartierKreinPolarizedGhost c) ∧
      sourceHorizontalSecondCartierKreinPolarizedBoundary c
        (-sourceHorizontalBilateralSecondJetGhost)
        (-sourceHorizontalSecondCartierKreinPolarizedGhost c) ∧
      ¬ sourceHorizontalSecondCartierKreinPolarizedBoundary c
        (sourceHorizontalBilateralSecondJetGhost +
          -sourceHorizontalBilateralSecondJetGhost)
        (sourceHorizontalSecondCartierKreinPolarizedGhost c +
          -sourceHorizontalSecondCartierKreinPolarizedGhost c) := by
  refine ⟨sourceHorizontalSecondCartierKreinPolarizedBoundary_ghost c,
    sourceHorizontalSecondCartierKreinPolarizedBoundary_neg_ghost c, ?_⟩
  simpa using (sourceHorizontalSecondCartierKreinPolarizedBoundary_zero_iff c).not.mpr hc

/-- For nonzero scale the shell cannot be repackaged as a complex-linear boundary relation. -/
theorem sourceHorizontalSecondCartierKreinPolarizedBoundary_not_submodule
    {c : ℂ} (hc : c ≠ 0) :
    ¬ ∃ S : Submodule ℂ
        (SourceHorizontalBilateralSecondJetSource ×
          SourceHorizontalSecondCartierKreinJet),
      ∀ v w, sourceHorizontalSecondCartierKreinPolarizedBoundary c v w ↔
        (v, w) ∈ S := by
  rintro ⟨S, hS⟩
  have hzero : sourceHorizontalSecondCartierKreinPolarizedBoundary c 0 0 :=
    (hS 0 0).2 S.zero_mem
  exact hc ((sourceHorizontalSecondCartierKreinPolarizedBoundary_zero_iff c).1 hzero)

theorem sourceHorizontalSecondCartierKreinPolarizedGhost_ne_zero (c : ℂ) :
    sourceHorizontalSecondCartierKreinPolarizedGhost c ≠ 0 := by
  intro h
  have hanchor := congrArg Prod.fst h
  norm_num [sourceHorizontalSecondCartierKreinPolarizedGhost,
    sourceHorizontalSecondCartierKreinUnit,
    sourceHorizontalSecondCartierKreinGhost] at hanchor

theorem sourceHorizontalSecondCartierKreinPolarizedGhost_not_bipositive
    [PartialOrder SourceHorizontalSecondCartierKreinJet]
    [IsOrderedAddMonoid SourceHorizontalSecondCartierKreinJet]
    (c : ℂ) :
    ¬ (0 ≤ sourceHorizontalSecondCartierKreinPolarizedGhost c ∧
      0 ≤ -sourceHorizontalSecondCartierKreinPolarizedGhost c) := by
  rintro ⟨hpos, hneg⟩
  have hle : sourceHorizontalSecondCartierKreinPolarizedGhost c ≤ 0 :=
    neg_nonneg.mp hneg
  exact sourceHorizontalSecondCartierKreinPolarizedGhost_ne_zero c
    (le_antisymm hle hpos)

def sourceHorizontalSecondCartierKreinPolarizedLift
    (c : ℂ) (v : SourceHorizontalBilateralSecondJetSource) :
    SourceHorizontalSecondCartierKreinJet :=
  ((2 * star c) / star (c * (v.1 + v.2)), (c * v.1, c * v.2))

theorem sourceHorizontalSecondCartierKreinPolarizedBoundary_unique
    {c : ℂ} {v : SourceHorizontalBilateralSecondJetSource}
    (hden : c * (v.1 + v.2) ≠ 0)
    (w : SourceHorizontalSecondCartierKreinJet) :
    sourceHorizontalSecondCartierKreinPolarizedBoundary c v w ↔
      w = sourceHorizontalSecondCartierKreinPolarizedLift c v := by
  have hstar : star (c * (v.1 + v.2)) ≠ 0 := star_ne_zero.mpr hden
  constructor
  · rintro ⟨hrel, hinc⟩
    rw [sourceHorizontalSecondCartierPointedKrein_relation_iff] at hrel
    rcases hrel with ⟨a, rfl⟩
    have hsum : c * v.1 + c * v.2 = c * (v.1 + v.2) := by ring
    rw [sourceHorizontalSecondCartierKreinHermitianIncidence, hsum] at hinc
    have ha : a = (2 * star c) / star (c * (v.1 + v.2)) :=
      (eq_div_iff hstar).2 hinc
    simp [sourceHorizontalSecondCartierKreinPolarizedLift, ha]
  · rintro rfl
    constructor
    · change c * v.1 = c * v.1 ∧ c * v.2 = c * v.2
      exact ⟨rfl, rfl⟩
    · rw [sourceHorizontalSecondCartierKreinHermitianIncidence]
      change ((2 * star c) / star (c * (v.1 + v.2))) *
        star (c * v.1 + c * v.2) = 2 * star c
      rw [show c * v.1 + c * v.2 = c * (v.1 + v.2) by ring]
      exact div_mul_cancel₀ (2 * star c) hstar

theorem sourceHorizontalSecondCartierKreinPolarizedBoundary_existsUnique
    {c : ℂ} {v : SourceHorizontalBilateralSecondJetSource}
    (hden : c * (v.1 + v.2) ≠ 0) :
    ∃! w : SourceHorizontalSecondCartierKreinJet,
      sourceHorizontalSecondCartierKreinPolarizedBoundary c v w := by
  refine ⟨sourceHorizontalSecondCartierKreinPolarizedLift c v, ?_, ?_⟩
  · exact (sourceHorizontalSecondCartierKreinPolarizedBoundary_unique hden _).2 rfl
  · intro w hw
    exact (sourceHorizontalSecondCartierKreinPolarizedBoundary_unique hden w).1 hw

@[simp] theorem sourceHorizontalSecondCartierKreinPolarizedForward_swap (c : ℂ) :
    sourceHorizontalSecondCartierKreinJetSwap
        (sourceHorizontalSecondCartierKreinPolarizedForward c) =
      sourceHorizontalSecondCartierKreinPolarizedInverse c := by
  rfl

@[simp] theorem sourceHorizontalSecondCartierKreinPolarizedInverse_swap (c : ℂ) :
    sourceHorizontalSecondCartierKreinJetSwap
        (sourceHorizontalSecondCartierKreinPolarizedInverse c) =
      sourceHorizontalSecondCartierKreinPolarizedForward c := by
  rfl

@[simp] theorem sourceHorizontalSecondCartierKreinPolarizedGhost_swap (c : ℂ) :
    sourceHorizontalSecondCartierKreinJetSwap
        (sourceHorizontalSecondCartierKreinPolarizedGhost c) =
      sourceHorizontalSecondCartierKreinPolarizedGhost c := by
  ext <;> simp [sourceHorizontalSecondCartierKreinJetSwap,
    sourceHorizontalSecondCartierKreinPolarizedGhost,
    sourceHorizontalSecondCartierKreinUnit,
    sourceHorizontalSecondCartierKreinGhost]

theorem sourceHorizontalSecondCartierKreinPolarizedGhost_form_self (c : ℂ) :
    sourceHorizontalSecondCartierKreinForm
        (sourceHorizontalSecondCartierKreinPolarizedGhost c)
        (sourceHorizontalSecondCartierKreinPolarizedGhost c) =
      2 * c + 2 * star c := by
  simp [sourceHorizontalSecondCartierKreinForm,
    sourceHorizontalSecondCartierKreinPolarizedGhost,
    sourceHorizontalSecondCartierKreinUnit,
    sourceHorizontalSecondCartierKreinGhost, star_add]
  ring

/-! ## Actual Xi-selected nonlinear polarization -/

def sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (v : SourceHorizontalBilateralSecondJetSource)
    (w : SourceHorizontalSecondCartierKreinJet) : Prop :=
  sourceHorizontalSecondCartierKreinPolarizedBoundary
    (sourceHorizontalActualXiSecondCartierKreinScale x u q r N) v w

def sourceHorizontalActualXiSecondCartierKreinPolarizedGhost
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :
    SourceHorizontalSecondCartierKreinJet :=
  sourceHorizontalSecondCartierKreinPolarizedGhost
    (sourceHorizontalActualXiSecondCartierKreinScale x u q r N)

theorem sourceHorizontalActualXiSecondCartierKreinScale_re_pos
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N) :
    0 < (sourceHorizontalActualXiSecondCartierKreinScale x u q r N).re := by
  have hc : sourceHorizontalActualXiConormalCoefficient x u q r ≠ 0 :=
    sourceHorizontalActualXiConormalCoefficient_ne_zero q hkappa hr
  simp only [sourceHorizontalActualXiSecondCartierKreinScale, ofReal_re]
  exact mul_pos (mul_pos (by norm_num) (Complex.normSq_pos.mpr hc)) hjet

theorem sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary_ghost
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :
    sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary x u q r N
      sourceHorizontalBilateralSecondJetGhost
      (sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N) := by
  exact sourceHorizontalSecondCartierKreinPolarizedBoundary_ghost _

theorem sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary_neg_ghost
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :
    sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary x u q r N
      (-sourceHorizontalBilateralSecondJetGhost)
      (-sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N) := by
  exact sourceHorizontalSecondCartierKreinPolarizedBoundary_neg_ghost _

theorem sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary_primeTransfer
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (p : Nat.Primes) (v : SourceHorizontalBilateralSecondJetSource)
    (w : SourceHorizontalSecondCartierKreinJet)
    (h : sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary
      x u q r N v w) :
    sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary x u q r N
      (sourceHorizontalSecondCartierKreinSourceTransfer
        (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p) v)
      (sourceHorizontalSecondCartierKreinJetTransfer
        (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p) w) := by
  exact sourceHorizontalSecondCartierKreinPolarizedBoundary_transfer
    (sourceHorizontalSecondCartierPointedKrein_actual_primeCharacter_ne_zero q p)
    _ _ _ h

theorem sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary_swap
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ)
    (v : SourceHorizontalBilateralSecondJetSource)
    (w : SourceHorizontalSecondCartierKreinJet)
    (h : sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary
      x u q r N v w) :
    sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary x u q r N
      (sourceHorizontalSecondCartierKreinSourceSwap v)
      (sourceHorizontalSecondCartierKreinJetSwap w) := by
  exact sourceHorizontalSecondCartierKreinPolarizedBoundary_swap _ _ _ h

theorem sourceHorizontalActualXiSecondCartierKreinPolarizedGhost_form_re_pos
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N) :
    0 < (sourceHorizontalSecondCartierKreinForm
      (sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N)
      (sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N)).re := by
  rw [sourceHorizontalActualXiSecondCartierKreinPolarizedGhost,
    sourceHorizontalSecondCartierKreinPolarizedGhost_form_self]
  have hstar :
      star (sourceHorizontalActualXiSecondCartierKreinScale x u q r N) =
        sourceHorizontalActualXiSecondCartierKreinScale x u q r N := by
    rw [sourceHorizontalActualXiSecondCartierKreinScale,
      Complex.star_def, Complex.conj_ofReal]
  rw [hstar]
  have heq :
      2 * sourceHorizontalActualXiSecondCartierKreinScale x u q r N +
          2 * sourceHorizontalActualXiSecondCartierKreinScale x u q r N =
        4 * sourceHorizontalActualXiSecondCartierKreinScale x u q r N := by ring
  rw [heq]
  have hpos := sourceHorizontalActualXiSecondCartierKreinScale_re_pos
    q hkappa hr N hjet
  simpa [Complex.mul_re] using
    (mul_pos (by norm_num : (0 : ℝ) < 4) hpos)

theorem sourceHorizontalActualXiSecondCartierKreinPolarizedGhost_eq_of_support
    (x u r : ℝ) {q s : XiRightZeroCopy} (h : s.1.1 = q.1.1) (N : ℕ) :
    sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u s r N =
      sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N := by
  rw [sourceHorizontalActualXiSecondCartierKreinPolarizedGhost,
    sourceHorizontalActualXiSecondCartierKreinPolarizedGhost,
    sourceHorizontalActualXiSecondCartierKreinScale,
    sourceHorizontalActualXiSecondCartierKreinScale,
    sourceHorizontalActualXiConormalCoefficient_eq_of_support x u r h]

theorem sourceHorizontalActualXiSecondCartierKreinPolarizedGhost_fiber_sum
    (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N : ℕ) :
    (∑ s : XiRightSupportFiber q,
      sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u s.1 r N) =
      xiSupportMultiplicity q.1.1 •
        sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N := by
  calc
    (∑ s : XiRightSupportFiber q,
      sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u s.1 r N) =
        ∑ _s : XiRightSupportFiber q,
          sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N := by
            apply Finset.sum_congr rfl
            intro s _hs
            exact sourceHorizontalActualXiSecondCartierKreinPolarizedGhost_eq_of_support
              x u r s.2 N
    _ = Fintype.card (XiRightSupportFiber q) •
          sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N := by simp
    _ = xiSupportMultiplicity q.1.1 •
          sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N := by
            rw [routePPrimitiveGammaJuliaXiActualSupportFiber_card]

/-- Actual Xi-selected capstone: same nonlinear shell admits both orientations, excludes their
linear cancellation, has positive selected Krein square, is prime-transfer invariant, and counts
every divisor copy. -/
theorem sourceHorizontalActualXiSecondCartierKreinHermitianPolarization_capstone
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (p : Nat.Primes) :
    sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary x u q r N
        sourceHorizontalBilateralSecondJetGhost
        (sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N) ∧
      sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary x u q r N
        (-sourceHorizontalBilateralSecondJetGhost)
        (-sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N) ∧
      ¬ sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary x u q r N 0 0 ∧
      0 < (sourceHorizontalSecondCartierKreinForm
        (sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N)
        (sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N)).re ∧
      sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary x u q r N
        (sourceHorizontalSecondCartierKreinSourceTransfer
          (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
          sourceHorizontalBilateralSecondJetGhost)
        (sourceHorizontalSecondCartierKreinJetTransfer
          (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p)
          (sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N)) ∧
      (∑ s : XiRightSupportFiber q,
        sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u s.1 r N) =
        xiSupportMultiplicity q.1.1 •
          sourceHorizontalActualXiSecondCartierKreinPolarizedGhost x u q r N := by
  have hc : sourceHorizontalActualXiSecondCartierKreinScale x u q r N ≠ 0 :=
    sourceHorizontalSecondCartierPointedKrein_actual_scale_ne_zero
      q hkappa hr N hjet
  refine ⟨sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary_ghost x u q r N,
    sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary_neg_ghost x u q r N,
    ?_, sourceHorizontalActualXiSecondCartierKreinPolarizedGhost_form_re_pos
      q hkappa hr N hjet, ?_,
    sourceHorizontalActualXiSecondCartierKreinPolarizedGhost_fiber_sum x u q r N⟩
  · exact (sourceHorizontalSecondCartierKreinPolarizedBoundary_zero_iff _).not.mpr hc
  · exact sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary_primeTransfer
      x u q r N p _ _
      (sourceHorizontalActualXiSecondCartierKreinPolarizedBoundary_ghost x u q r N)

end

end RHTower
