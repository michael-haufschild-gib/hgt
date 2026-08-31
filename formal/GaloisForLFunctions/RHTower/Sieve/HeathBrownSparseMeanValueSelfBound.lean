import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueSquareLift

/-!
# Self-bound closure for the Heath--Brown sparse mean value

This file supplies the finite zero-extension and scalar quadratic steps needed to turn the
Cauchy/divisor square lift into a closed estimate.  Every coefficient and analytic premise is
constructed internally.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- Solve the nonnegative scalar self-bound used after a Cauchy square lift. -/
theorem le_two_mul_add_sq_mul_of_le_add_of_sq_le_mul
    {x y a b k : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hb : 0 ≤ b) (hk : 0 ≤ k) (hxy : x ≤ a + b * y)
    (hy2 : y ^ 2 ≤ k * x) :
    x ≤ 2 * a + b ^ 2 * k := by
  have hby2 : (b * y) ^ 2 ≤ (b ^ 2 * k) * x := by
    calc
      (b * y) ^ 2 = b ^ 2 * y ^ 2 := by ring
      _ ≤ b ^ 2 * (k * x) := by gcongr
      _ = (b ^ 2 * k) * x := by ring
  have hamgm : 2 * (b * y) ≤ x + b ^ 2 * k := by
    by_contra h
    have hgt : x + b ^ 2 * k < 2 * (b * y) := lt_of_not_ge h
    have hleft : 0 ≤ x + b ^ 2 * k := by positivity
    have hright : 0 ≤ b * y := mul_nonneg hb hy
    nlinarith [sq_nonneg (x - b ^ 2 * k)]
  linarith

/-- Unit coefficients through `K`, zero thereafter. -/
def heathBrownDenseCutoffWeight (K : ℕ) : ℕ → Set.Icc (0 : ℝ) 1 :=
  fun n => if n ≤ K then heathBrownDenseUnitWeight n else ⟨0, by constructor <;> norm_num⟩

/-- Full positive intervals are monotone in their natural endpoint. -/
theorem heathBrownPositiveInterval_mono {K N : ℕ} (hK : 1 ≤ K) (hN : 1 ≤ N)
    (hKN : K ≤ N) :
    heathBrownPositiveInterval K hK ⊆ heathBrownPositiveInterval N hN := by
  intro n hn
  rw [heathBrownPositiveInterval, Finset.mem_Icc] at hn ⊢
  constructor
  · exact hn.1
  · change (n : ℕ) ≤ N
    have hnK : (n : ℕ) ≤ K := by exact_mod_cast hn.2
    exact hnK.trans hKN

/-- Zero extension to a larger positive interval preserves the dense Dirichlet factor. -/
theorem heathBrownDenseFactor_cutoff_eq
    {K N : ℕ} (hK : 1 ≤ K) (hN : 1 ≤ N) (hKN : K ≤ N) (t : ℝ) :
    heathBrownDenseFactor (heathBrownPositiveInterval N hN)
        (heathBrownDenseCutoffWeight K) t =
      heathBrownDenseFactor (heathBrownPositiveInterval K hK)
        heathBrownDenseUnitWeight t := by
  unfold heathBrownDenseFactor
  have hsub := heathBrownPositiveInterval_mono hK hN hKN
  calc
    (∑ n ∈ heathBrownPositiveInterval N hN,
        ((((heathBrownDenseCutoffWeight K) (n : ℕ) : ℝ) : ℂ)) *
          heathBrownDirichletPhase n t) =
        ∑ n ∈ heathBrownPositiveInterval K hK,
          ((((heathBrownDenseCutoffWeight K) (n : ℕ) : ℝ) : ℂ)) *
            heathBrownDirichletPhase n t := by
      symm
      apply Finset.sum_subset hsub
      intro n hnN hnK
      have hnle : ¬(n : ℕ) ≤ K := by
        intro hnle
        apply hnK
        rw [heathBrownPositiveInterval, Finset.mem_Icc]
        constructor
        · exact (Finset.mem_Icc.mp hnN).1
        · exact hnle
      simp [heathBrownDenseCutoffWeight, hnle]
    _ = ∑ n ∈ heathBrownPositiveInterval K hK,
          ((((heathBrownDenseUnitWeight) (n : ℕ) : ℝ) : ℂ)) *
            heathBrownDirichletPhase n t := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnle : (n : ℕ) ≤ K := (Finset.mem_Icc.mp hn).2
      simp [heathBrownDenseCutoffWeight, hnle]

/-- A full unit interval embeds into every larger full unit interval after zero extension. -/
theorem integral_Icc_normSq_heathBrown_fullUnit_mono
    (A : Finset PNat) (eps : ℕ → Circle) (T : Set.Ioi (0 : ℝ))
    {K N : ℕ} (hK : 1 ≤ K) (hN : 1 ≤ N) (hKN : K ≤ N) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A eps t *
          heathBrownDenseFactor (heathBrownPositiveInterval K hK)
            heathBrownDenseUnitWeight t‖ ^ 2) ≤
      (25 * Real.pi / 8) *
        ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
          ‖heathBrownSparseFactor A (fun _ => 1) t *
            heathBrownDenseFactor (heathBrownPositiveInterval N hN)
              heathBrownDenseUnitWeight t‖ ^ 2 := by
  have h := integral_Icc_normSq_heathBrown_factors_le_unit A
    (heathBrownPositiveInterval N hN) eps (heathBrownDenseCutoffWeight K) T
  simpa only [heathBrownDenseFactor_cutoff_eq hK hN hKN] using h

/-- Enlarging a symmetric height window increases a nonnegative full-unit mean square. -/
theorem integral_Icc_normSq_heathBrown_fullUnit_height_mono
    (A : Finset PNat) (N : ℕ) (hN : 1 ≤ N) {V W : ℝ} (hVW : V ≤ W) :
    (∫ t in Set.Icc (-V) V,
        ‖heathBrownSparseFactor A (fun _ => 1) t *
          heathBrownDenseFactor (heathBrownPositiveInterval N hN)
            heathBrownDenseUnitWeight t‖ ^ 2) ≤
      ∫ t in Set.Icc (-W) W,
        ‖heathBrownSparseFactor A (fun _ => 1) t *
          heathBrownDenseFactor (heathBrownPositiveInterval N hN)
            heathBrownDenseUnitWeight t‖ ^ 2 := by
  let f : ℝ → ℝ := fun t =>
    ‖heathBrownSparseFactor A (fun _ => 1) t *
      heathBrownDenseFactor (heathBrownPositiveInterval N hN)
        heathBrownDenseUnitWeight t‖ ^ 2
  have hf : Continuous f :=
    ((continuous_heathBrownSparseFactor A (fun _ => 1)).mul
      (continuous_heathBrownDenseFactor (heathBrownPositiveInterval N hN)
        heathBrownDenseUnitWeight)).norm.pow 2
  have hsub : Set.Icc (-V) V ⊆ Set.Icc (-W) W := by
    intro t ht
    rw [Set.mem_Icc] at ht ⊢
    constructor <;> linarith
  have hfull : Integrable f (volume.restrict (Set.Icc (-W) W)) := hf.integrableOn_Icc
  exact integral_mono_measure
    (Measure.restrict_mono hsub le_rfl)
    (Filter.Eventually.of_forall fun _ => by dsimp only [f]; positivity) hfull

/-- The explicit ordinary sparse-factor mean-square envelope is nonnegative. -/
theorem heathBrownSparseMeanSquareEnvelope_nonneg
    (A : Finset PNat) {X W : ℝ} (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ X)
    (hW : 0 ≤ W) :
    0 ≤ (5 * Real.pi * Real.exp 1 * X + (5 * Real.pi / 2) * W) *
      (A.card : ℝ) := by
  by_cases hAempty : A = ∅
  · simp [hAempty]
  · obtain ⟨n, hn⟩ := Finset.nonempty_iff_ne_empty.mpr hAempty
    have hX : 0 ≤ X := le_trans (by positivity) (hA n hn)
    positivity

/-- Square lift followed by zero extension into an ambient dense interval. -/
theorem integral_Icc_normSq_heathBrown_fullUnit_sq_le_ambientSquareLift
    (A : Finset PNat) (T : Set.Ioi (0 : ℝ)) (hT : 1 ≤ (T : ℝ))
    {X : ℝ} (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ X)
    {K N : ℕ} (hK : 1 ≤ K) (hN : 1 ≤ N) (hKsqN : K * K ≤ N)
    {eta : ℝ} (heta : 0 < eta) :
    (∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
        ‖heathBrownSparseFactor A (fun _ => 1) t *
          heathBrownDenseFactor (heathBrownPositiveInterval K hK)
            heathBrownDenseUnitWeight t‖ ^ 2) ^ 2 ≤
      ((5 * Real.pi * Real.exp 1 * X + (5 * Real.pi / 2) * (T : ℝ)) *
        (A.card : ℝ)) *
      (heathBrownSquareDivisorScale K eta ^ 2 * (25 * Real.pi / 8) *
        ((25 * Real.pi / 8) *
          ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
            ‖heathBrownSparseFactor A (fun _ => 1) t *
              heathBrownDenseFactor (heathBrownPositiveInterval N hN)
                heathBrownDenseUnitWeight t‖ ^ 2)) := by
  have hlift := integral_Icc_normSq_heathBrown_fullUnit_sq_le_squareLift
    A T hT hA hK heta
  have hKsq : 1 ≤ K * K := by simpa using Nat.mul_le_mul hK hK
  have hext := integral_Icc_normSq_heathBrown_fullUnit_mono
    A (fun _ => 1) T hKsq hN hKsqN
  have hMS : 0 ≤
      ((5 * Real.pi * Real.exp 1 * X + (5 * Real.pi / 2) * (T : ℝ)) *
        (A.card : ℝ)) :=
    heathBrownSparseMeanSquareEnvelope_nonneg A hA T.property.le
  calc
    _ ≤ ((5 * Real.pi * Real.exp 1 * X + (5 * Real.pi / 2) * (T : ℝ)) *
          (A.card : ℝ)) *
        (heathBrownSquareDivisorScale K eta ^ 2 * (25 * Real.pi / 8) *
          ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
            ‖heathBrownSparseFactor A (fun _ => 1) t *
              heathBrownDenseFactor
                (heathBrownPositiveInterval (K * K) hKsq)
                heathBrownDenseUnitWeight t‖ ^ 2) := hlift
    _ ≤ ((5 * Real.pi * Real.exp 1 * X + (5 * Real.pi / 2) * (T : ℝ)) *
          (A.card : ℝ)) *
        (heathBrownSquareDivisorScale K eta ^ 2 * (25 * Real.pi / 8) *
          ((25 * Real.pi / 8) *
            ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
              ‖heathBrownSparseFactor A (fun _ => 1) t *
                heathBrownDenseFactor (heathBrownPositiveInterval N hN)
                  heathBrownDenseUnitWeight t‖ ^ 2)) := by
      gcongr

/-- Closed one-step self-bound obtained from the two-scale recurrence and square lift. -/
theorem integral_Icc_normSq_heathBrown_fullUnit_le_oneStepSelfBound
    (A : Finset PNat) (T : Set.Ioi (0 : ℝ)) (hT : 2 ≤ (T : ℝ))
    {X : ℝ} (hA : ∀ n ∈ A, ((n : ℕ) : ℝ) ≤ X)
    {K N : ℕ} (hK : 1 ≤ K) (hN : 1 ≤ N) (hKsqN : K * K ≤ N)
    {eta : ℝ} (heta : 0 < eta) :
    let I : ℝ := ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
      ‖heathBrownSparseFactor A (fun _ => 1) t *
        heathBrownDenseFactor (heathBrownPositiveInterval N hN)
          heathBrownDenseUnitWeight t‖ ^ 2
    let a : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
      (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
        ((2 * (N / K) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2)
    let b : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
      (((N / K + 1 : ℕ) : ℝ) * (5 / (2 * (T : ℝ))))
    let k : ℝ :=
      ((5 * Real.pi * Real.exp 1 * X +
          (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) * (A.card : ℝ)) *
        (heathBrownSquareDivisorScale K eta ^ 2 * (25 * Real.pi / 8) *
          (25 * Real.pi / 8))
    I ≤ 2 * a + b ^ 2 * k := by
  dsimp only
  let I : ℝ := ∫ t in Set.Icc (-(T : ℝ)) (T : ℝ),
    ‖heathBrownSparseFactor A (fun _ => 1) t *
      heathBrownDenseFactor (heathBrownPositiveInterval N hN)
        heathBrownDenseUnitWeight t‖ ^ 2
  let J : ℝ := ∫ t in Set.Icc (-(heathBrownHalfHeight T : ℝ))
      (heathBrownHalfHeight T : ℝ),
    ‖heathBrownSparseFactor A (fun _ => 1) t *
      heathBrownDenseFactor (heathBrownPositiveInterval K hK)
        heathBrownDenseUnitWeight t‖ ^ 2
  let a : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
    (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
      ((2 * (N / K) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2)
  let b : ℝ := (5 * Real.pi / 2) * (T : ℝ) *
    (((N / K + 1 : ℕ) : ℝ) * (5 / (2 * (T : ℝ))))
  let k : ℝ :=
    ((5 * Real.pi * Real.exp 1 * X +
        (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) * (A.card : ℝ)) *
      (heathBrownSquareDivisorScale K eta ^ 2 * (25 * Real.pi / 8) *
        (25 * Real.pi / 8))
  have hTone : 1 ≤ (T : ℝ) := by linarith
  have hKleN : K ≤ N := by
    calc
      K = K * 1 := by omega
      _ ≤ K * K := Nat.mul_le_mul_left K hK
      _ ≤ N := hKsqN
  have hB : ∀ n ∈ heathBrownPositiveInterval N hN, (n : ℕ) ≤ N := by
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    exact_mod_cast hn'.2
  have hrec := integral_Icc_normSq_heathBrown_factors_le_twoScaleIntegral
    A (heathBrownPositiveInterval N hN) (fun _ => 1) heathBrownDenseUnitWeight
    T hTone hB hK hKleN
  have hIrec : I ≤ a + b * J := by
    calc
      I ≤ (5 * Real.pi / 2) * (T : ℝ) *
          (15 * (T : ℝ)⁻¹ * (N : ℝ) ^ 2 * (A.card : ℝ) ^ 2 +
            ((N / K + 1 : ℕ) : ℝ) *
              ((5 / (2 * (T : ℝ))) * J) +
            ((2 * (N / K) + 1 : ℕ) : ℝ) * (A.card : ℝ) ^ 2) := by
        simpa only [I, J] using hrec
      _ = a + b * J := by dsimp only [a, b]; ring
  have hhalf : 1 ≤ (heathBrownHalfHeight T : ℝ) := by
    change 1 ≤ (T : ℝ) / 2
    linarith
  have hlift := integral_Icc_normSq_heathBrown_fullUnit_sq_le_ambientSquareLift
    A (heathBrownHalfHeight T) hhalf hA hK hN hKsqN heta
  have hheight := integral_Icc_normSq_heathBrown_fullUnit_height_mono
    A N hN (V := (heathBrownHalfHeight T : ℝ)) (W := (T : ℝ))
    (by
      change (T : ℝ) / 2 ≤ (T : ℝ)
      linarith [T.property])
  have hMSHalf : 0 ≤
      (5 * Real.pi * Real.exp 1 * X +
          (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) * (A.card : ℝ) :=
    heathBrownSparseMeanSquareEnvelope_nonneg A hA
      (heathBrownHalfHeight T).property.le
  have hJlift : J ^ 2 ≤ k * I := by
    calc
      J ^ 2 ≤
          ((5 * Real.pi * Real.exp 1 * X +
              (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) *
            (A.card : ℝ)) *
          (heathBrownSquareDivisorScale K eta ^ 2 * (25 * Real.pi / 8) *
            ((25 * Real.pi / 8) *
              ∫ t in Set.Icc (-(heathBrownHalfHeight T : ℝ))
                  (heathBrownHalfHeight T : ℝ),
                ‖heathBrownSparseFactor A (fun _ => 1) t *
                  heathBrownDenseFactor (heathBrownPositiveInterval N hN)
                    heathBrownDenseUnitWeight t‖ ^ 2)) := by
        simpa only [J] using hlift
      _ ≤ ((5 * Real.pi * Real.exp 1 * X +
              (5 * Real.pi / 2) * (heathBrownHalfHeight T : ℝ)) *
            (A.card : ℝ)) *
          (heathBrownSquareDivisorScale K eta ^ 2 * (25 * Real.pi / 8) *
            ((25 * Real.pi / 8) * I)) := by
        gcongr
      _ = k * I := by dsimp only [k]; ring
  have hI0 : 0 ≤ I := by
    dsimp only [I]
    exact integral_nonneg fun _ => by positivity
  have hJ0 : 0 ≤ J := by
    dsimp only [J]
    exact integral_nonneg fun _ => by positivity
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have hk0 : 0 ≤ k := by
    dsimp only [k]
    have hMS := heathBrownSparseMeanSquareEnvelope_nonneg A hA
      (heathBrownHalfHeight T).property.le
    positivity
  exact le_two_mul_add_sq_mul_of_le_add_of_sq_le_mul
    hI0 hJ0 hb0 hk0 hIrec hJlift

end RHTower.Sieve
