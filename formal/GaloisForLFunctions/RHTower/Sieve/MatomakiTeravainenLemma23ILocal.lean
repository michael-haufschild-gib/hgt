import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLemma23IPaperScale

/-!
# Local coefficient bounds for Matomäki--Teräväinen Lemma 2.3(i)

Every coefficient read by the literal error at `n` divides `n`.  Therefore the paper-scale
mean-square theorem only needs a coefficient bound up to the summation endpoint, as used in the
iteration after (2.15).  A finite truncation converts that local fact to the existing global form.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- `c₁,n` only reads coefficients at divisors of `n`. -/
theorem mtC1Coefficient_congr_of_le (α β : ℕ → ℂ) (z D : ℕ)
    {n : ℕ} (hn : 0 < n) (hαβ : ∀ m, m ≤ n → α m = β m) :
    mtC1Coefficient α z D n = mtC1Coefficient β z D n := by
  unfold mtC1Coefficient
  apply Finset.sum_congr rfl
  intro m hm
  rw [hαβ m (Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hm))]

/-- One endpoint coefficient only reads coefficients at divisors of `n`. -/
theorem mtC2BoundaryCoefficient_congr_of_le (α β : ℕ → ℂ)
    (S : Finset ℕ) (level : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    (hαβ : ∀ m, m ≤ n → α m = β m) :
    mtC2BoundaryCoefficient α S level n =
      mtC2BoundaryCoefficient β S level n := by
  unfold mtC2BoundaryCoefficient
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs with hqn
  · apply Finset.sum_congr rfl
    intro m hm
    have hquotPos : 0 < n / q := by
      have hqNe : q ≠ 0 := by
        intro hqEq
        subst q
        simp at hqn
        omega
      have hqPos : 0 < q := Nat.pos_of_ne_zero hqNe
      exact Nat.div_pos (Nat.le_of_dvd hn hqn) hqPos
    have hmLe : m ≤ n :=
      (Nat.le_of_dvd hquotPos (Nat.dvd_of_mem_divisors hm)).trans
        (Nat.div_le_self n q)
    rw [hαβ m hmLe]
  · rfl

/-- `c₂,n` only reads coefficients at divisors of `n`. -/
theorem mtC2Coefficient_congr_of_le (α β : ℕ → ℂ)
    (lowerSpill upperSpill : Finset ℕ) (level : ℕ → ℕ)
    {n : ℕ} (hn : 0 < n) (hαβ : ∀ m, m ≤ n → α m = β m) :
    mtC2Coefficient α lowerSpill upperSpill level n =
      mtC2Coefficient β lowerSpill upperSpill level n := by
  unfold mtC2Coefficient
  rw [mtC2BoundaryCoefficient_congr_of_le α β upperSpill level hn hαβ,
    mtC2BoundaryCoefficient_congr_of_le α β lowerSpill level hn hαβ]

/-- `c₃,n` only reads coefficients at divisors of `n`. -/
theorem mtC3Coefficient_congr_of_le (α β : ℕ → ℂ)
    (S : Finset ℕ) (lower : ℕ → ℕ) {n : ℕ} (hn : 0 < n)
    (hαβ : ∀ m, m ≤ n → α m = β m) :
    mtC3Coefficient α S lower n = mtC3Coefficient β S lower n := by
  unfold mtC3Coefficient
  apply Finset.sum_congr rfl
  intro q hq
  split_ifs with hqn
  · apply Finset.sum_congr rfl
    intro m hm
    have hquotPos : 0 < n / q := by
      have hqNe : q ≠ 0 := by
        intro hqEq
        subst q
        simp at hqn
        omega
      have hqPos : 0 < q := Nat.pos_of_ne_zero hqNe
      exact Nat.div_pos (Nat.le_of_dvd hn hqn) hqPos
    have hmLe : m ≤ n :=
      (Nat.le_of_dvd hquotPos (Nat.dvd_of_mem_divisors hm)).trans
        (Nat.div_le_self n q)
    rw [hαβ m hmLe]
  · rfl

/-- Literal combined error only reads coefficients at divisors of `n`. -/
theorem mtLemma23Error_congr_of_le (α β : ℕ → ℂ)
    (z D : ℕ) (lowerSpill upperSpill P : Finset ℕ) (lower : ℕ → ℕ)
    {n : ℕ} (hn : 0 < n) (hαβ : ∀ m, m ≤ n → α m = β m) :
    mtLemma23Error α z D lowerSpill upperSpill P lower n =
      mtLemma23Error β z D lowerSpill upperSpill P lower n := by
  unfold mtLemma23Error
  rw [mtC1Coefficient_congr_of_le α β z D hn hαβ,
    mtC2Coefficient_congr_of_le α β lowerSpill upperSpill lower hn hαβ,
    mtC3Coefficient_congr_of_le α β P lower hn hαβ]

/-- Coefficient truncation at a finite ambient endpoint. -/
def mtTruncateCoefficient (α : ℕ → ℂ) (N m : ℕ) : ℂ :=
  if m ≤ N then α m else 0

theorem mtTruncateCoefficient_eq (α : ℕ → ℂ) {N m : ℕ} (hm : m ≤ N) :
    mtTruncateCoefficient α N m = α m := by
  simp [mtTruncateCoefficient, hm]

theorem norm_mtTruncateCoefficient_le (α : ℕ → ℂ) (N : ℕ) {B : ℝ}
    (hB : 0 ≤ B) (hα : ∀ {m : ℕ}, m ≤ N → ‖α m‖ ≤ B) (m : ℕ) :
    ‖mtTruncateCoefficient α N m‖ ≤ B := by
  by_cases hm : m ≤ N
  · simpa [mtTruncateCoefficient, hm] using hα hm
  · simp [mtTruncateCoefficient, hm, hB]

/-- Paper-scale Lemma 2.3(i) with the coefficient bound restricted to the actual summation
endpoint. -/
theorem eventually_sum_norm_sq_mtLemma23Error_le_log_rpow_local
    (A : ℕ) (hA : 2 ≤ A) :
    ∀ᶠ X : ℝ in atTop,
      ∀ (α : ℕ → ℂ) (lower : ℕ → ℕ)
        (z₁ aLower bLower aUpper bUpper Y : ℕ) (B : ℝ),
      1 ≤ Y → (Y : ℝ) ≤ 4 * X → 1 ≤ z₁ → (z₁ : ℝ) ≤ X →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aLower - 1 : ℕ) : ℝ) →
      aLower ≤ bLower →
      ((bLower - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aLower - 1 : ℕ) : ℝ) →
      mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((aUpper - 1 : ℕ) : ℝ) →
      aUpper ≤ bUpper →
      ((bUpper - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((aUpper - 1 : ℕ) : ℝ) →
      (∀ q ∈ primesIco (mtLowerCutoffNat X) z₁,
        mtLowerCutoff X / (1 + mtPaperWidth A X) ≤ ((lower q - 1 : ℕ) : ℝ)) →
      (∀ q ∈ primesIco (mtLowerCutoffNat X) z₁, lower q ≤ q) →
      (∀ q ∈ primesIco (mtLowerCutoffNat X) z₁, ((q - 1 : ℕ) : ℝ) ≤
        (1 + mtPaperWidth A X) * ((lower q - 1 : ℕ) : ℝ)) →
      0 ≤ B → (∀ {m : ℕ}, m ≤ Y → ‖α m‖ ≤ B) →
      ∑ n ∈ Finset.Icc 1 Y,
          ‖mtLemma23Error α (mtLowerCutoffNat X) (mtTruncationNat X)
            (primesIco aLower bLower) (primesIco aUpper bUpper)
            (primesIco (mtLowerCutoffNat X) z₁) lower n‖ ^ 2 ≤
        15 * B ^ 2 * (Y : ℝ) * (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := by
  filter_upwards [eventually_sum_norm_sq_mtLemma23Error_le_log_rpow A hA]
    with X hglobal
  intro α lower z₁ aLower bLower aUpper bUpper Y B hY hYX hz₁ hZ₁X
    hLowerCut hLowerOrder hLowerBand hUpperCut hUpperOrder hUpperBand
    hlowerCut hlower hband hB hα
  let β := mtTruncateCoefficient α Y
  have hβ : ∀ m, ‖β m‖ ≤ B :=
    norm_mtTruncateCoefficient_le α Y hB (fun hm => hα hm)
  have hbound := hglobal β lower z₁ aLower bLower aUpper bUpper Y B
    hY hYX hz₁ hZ₁X hLowerCut hLowerOrder hLowerBand hUpperCut hUpperOrder hUpperBand
    hlowerCut hlower hband hB hβ
  calc
    ∑ n ∈ Finset.Icc 1 Y,
        ‖mtLemma23Error α (mtLowerCutoffNat X) (mtTruncationNat X)
          (primesIco aLower bLower) (primesIco aUpper bUpper)
          (primesIco (mtLowerCutoffNat X) z₁) lower n‖ ^ 2 =
      ∑ n ∈ Finset.Icc 1 Y,
        ‖mtLemma23Error β (mtLowerCutoffNat X) (mtTruncationNat X)
          (primesIco aLower bLower) (primesIco aUpper bUpper)
          (primesIco (mtLowerCutoffNat X) z₁) lower n‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro n hnMem
      have hnPos : 0 < n := by
        rw [Finset.mem_Icc] at hnMem
        omega
      apply congrArg (fun w : ℂ => ‖w‖ ^ 2)
      apply mtLemma23Error_congr_of_le α β _ _ _ _ _ _ hnPos
      intro m hm
      symm
      exact mtTruncateCoefficient_eq α
        (hm.trans (Finset.mem_Icc.mp hnMem).2)
    _ ≤ 15 * B ^ 2 * (Y : ℝ) *
        (Real.log X) ^ (-((3 * A : ℕ) : ℝ)) := hbound

end

end RHTower.Sieve
