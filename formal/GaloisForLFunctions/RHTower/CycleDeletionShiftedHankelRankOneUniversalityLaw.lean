import GaloisForLFunctions.RHTower.PrimeCycleDeletionCoherence
import GaloisForLFunctions.RHTower.EulerSourceJetJacobian

/-!
# Cycle-deletion and shifted-Hankel rank-one universality

Shape-blind deletion of labels from arbitrary cycle shapes is exactly vanishing of every shifted
two-row Hankel cross-minor.  The equivalence holds for nonvanishing real or complex weight
sequences.  On degree-one Euler coefficient streams, all-order quadratic prime-ray compatibility
therefore reduces to prime-power support, one base normalization at each prime, and shape-blind
cycle deletion on each ray.
-/

namespace RHTower

/-- Every two-row shifted Hankel cross-minor of a positive-indexed sequence vanishes. -/
def ShiftedHankelCrossMinorsVanish (w : ℕ → ℝ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    w (m + 1) * w n = w m * w (n + 1)

/-- **Cycle-deletion/Hankel universality over `ℝ`.**  Shape-blind cycle deletion is exactly the
rank-one shifted-Hankel condition. -/
theorem cycleDeletionShapeBlind_iff_shiftedHankelCrossMinorsVanish
    (w : ℕ → ℝ) (hw : ∀ k : ℕ, 0 < k → w k ≠ 0) :
    CycleDeletionShapeBlind (fun k => w (k + 1) / w k) ↔
      ShiftedHankelCrossMinorsVanish w := by
  rw [cycleDeletionShapeBlind_iff_constant_ratio]
  constructor
  · intro h m n hm hn
    have hmn : w (m + 1) / w m = w (n + 1) / w n :=
      (h m hm).trans (h n hn).symm
    have hcross := (div_eq_div_iff (hw m hm) (hw n hn)).mp hmn
    simpa [mul_comm] using hcross
  · intro h k hk
    apply (div_eq_div_iff (hw k hk) (hw 1 (by omega))).2
    have hminor := h k 1 hk (by omega)
    simpa [mul_comm] using hminor

/-- Complex total deletion score for a cycle shape. -/
def complexCycleDeletionShapeScore (r : ℕ → ℂ) (parts : List ℕ) : ℂ :=
  (parts.map fun k : ℕ => (k : ℂ) * r k).sum

/-- Complex deletion lift mass is blind to cycle shape at fixed total size. -/
def ComplexCycleDeletionShapeBlind (r : ℕ → ℂ) : Prop :=
  ∀ parts parts' : List ℕ,
    (∀ k ∈ parts, 0 < k) →
    (∀ k ∈ parts', 0 < k) →
    parts.sum = parts'.sum →
    complexCycleDeletionShapeScore r parts = complexCycleDeletionShapeScore r parts'

/-- Complex shape-blind deletion is equivalent to a constant positive-length ratio. -/
theorem complexCycleDeletionShapeBlind_iff_constant_ratio (r : ℕ → ℂ) :
    ComplexCycleDeletionShapeBlind r ↔ ∀ k : ℕ, 0 < k → r k = r 1 := by
  constructor
  · intro h k hk
    have hs := h [k] (List.replicate k 1)
      (by simp [hk]) (by simp) (by simp)
    simp [complexCycleDeletionShapeScore] at hs
    exact hs.resolve_right hk.ne'
  · intro h parts parts' hparts hparts' hsum
    have score_eq (l : List ℕ) (hl : ∀ k ∈ l, 0 < k) :
        complexCycleDeletionShapeScore r l = (l.sum : ℂ) * r 1 := by
      induction l with
      | nil => simp [complexCycleDeletionShapeScore]
      | cons k l ih =>
          have hk : 0 < k := hl k (by simp)
          have hl' : ∀ a ∈ l, 0 < a := by
            intro a ha
            exact hl a (by simp [ha])
          rw [complexCycleDeletionShapeScore]
          simp only [List.map_cons, List.sum_cons]
          rw [h k hk]
          have ih' := ih hl'
          rw [complexCycleDeletionShapeScore] at ih'
          rw [ih']
          push_cast
          ring
    rw [score_eq parts hparts, score_eq parts' hparts', hsum]

/-- Every shifted complex Hankel cross-minor vanishes. -/
def ComplexShiftedHankelCrossMinorsVanish (w : ℕ → ℂ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    w (m + 1) * w n = w m * w (n + 1)

/-- **Cycle-deletion/Hankel universality over `ℂ`.**  Complex shape-blind cycle deletion is
exactly the rank-one shifted-Hankel condition. -/
theorem complexCycleDeletionShapeBlind_iff_shiftedHankelCrossMinorsVanish
    (w : ℕ → ℂ) (hw : ∀ k : ℕ, 0 < k → w k ≠ 0) :
    ComplexCycleDeletionShapeBlind (fun k => w (k + 1) / w k) ↔
      ComplexShiftedHankelCrossMinorsVanish w := by
  rw [complexCycleDeletionShapeBlind_iff_constant_ratio]
  constructor
  · intro h m n hm hn
    have hmn : w (m + 1) / w m = w (n + 1) / w n :=
      (h m hm).trans (h n hn).symm
    have hcross := (div_eq_div_iff (hw m hm) (hw n hn)).mp hmn
    simpa [mul_comm] using hcross
  · intro h k hk
    apply (div_eq_div_iff (hw k hk) (hw 1 (by omega))).2
    have hminor := h k 1 hk (by omega)
    simpa [mul_comm] using hminor

/-- **Euler source/cycle-deletion classification.**  The all-order quadratic Euler source image
is equivalent to support, one base normalization, and shape-blind deletion on every nonvanishing
prime-power ray. -/
theorem degreeOneEulerQuadraticCompatible_iff_cycleDeletionShapeBlind
    (c : ℕ → ℂ)
    (hnz : ∀ (p m : ℕ), p.Prime → m ≠ 0 → c (p ^ m) ≠ 0) :
    DegreeOneEulerQuadraticCompatible c ↔
      (∀ n : ℕ, ¬ IsPrimePow n → c n = 0) ∧
        ∀ p : ℕ, p.Prime →
          c p * c p = (Real.log p : ℂ) * c (p ^ 2) ∧
          ComplexCycleDeletionShapeBlind
            (fun m => c (p ^ (m + 1)) / c (p ^ m)) := by
  constructor
  · intro hc
    refine ⟨hc.1, ?_⟩
    intro p hp
    constructor
    · simpa using hc.2 p 1 1 hp one_ne_zero one_ne_zero
    · apply (complexCycleDeletionShapeBlind_iff_shiftedHankelCrossMinorsVanish
        (fun m => c (p ^ m)) (fun k hk => hnz p k hp hk.ne')).2
      intro m n hm hn
      calc
        c (p ^ (m + 1)) * c (p ^ n) =
            (Real.log p : ℂ) * c (p ^ ((m + 1) + n)) :=
          hc.2 p (m + 1) n hp (by omega) hn.ne'
        _ = (Real.log p : ℂ) * c (p ^ (m + (n + 1))) := by
          congr 3
          omega
        _ = c (p ^ m) * c (p ^ (n + 1)) :=
          (hc.2 p m (n + 1) hp hm.ne' (by omega)).symm
  · rintro ⟨hsupport, hcycle⟩
    apply degreeOneEulerQuadraticCompatible_of_rayCompatible
    refine ⟨hsupport, ?_⟩
    intro p m hp hm
    have hlog : (Real.log p : ℂ) ≠ 0 := by
      exact_mod_cast (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    have hconstant := (complexCycleDeletionShapeBlind_iff_constant_ratio
      (fun k => c (p ^ (k + 1)) / c (p ^ k))).mp (hcycle p hp).2
    have hrec : ∀ k : ℕ, 0 < k →
        c (p ^ (k + 1)) = (c (p ^ 2) / c p) * c (p ^ k) := by
      intro k hk
      have hkRatio := hconstant k hk
      have hkRatio' : c (p ^ (k + 1)) / c (p ^ k) = c (p ^ 2) / c p := by
        simpa using hkRatio
      exact (div_eq_iff (hnz p k hp hk.ne')).mp hkRatio'
    have hgeom : ∀ k : ℕ, 0 < k →
        c (p ^ k) = c p * (c (p ^ 2) / c p) ^ (k - 1) := by
      intro k hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
      induction j with
      | zero => simp
      | succ j ih =>
          rw [hrec (j + 1) (by omega), ih (by omega)]
          simp only [Nat.succ_sub_one]
          rw [pow_succ]
          ring
    have hratio : c (p ^ 2) / c p = c p / (Real.log p : ℂ) := by
      apply (div_eq_div_iff (by simpa using hnz p 1 hp one_ne_zero) hlog).2
      simpa [mul_comm] using (hcycle p hp).1.symm
    rw [hgeom m (Nat.pos_of_ne_zero hm), hratio]
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    simp only [Nat.succ_sub_one, pow_succ]
    field_simp

end RHTower
