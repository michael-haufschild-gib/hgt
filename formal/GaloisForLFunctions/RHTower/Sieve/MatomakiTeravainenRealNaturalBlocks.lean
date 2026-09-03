import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenWattDIOverHeight

/-!
# Real-to-natural block bridges for Matomäki--Teräväinen pieces

Proposition 2.2 stores factor intervals with real endpoints, while the Type-I moment machinery
uses exact natural Watt blocks.  A real dyadic coefficient interval `(M,2M]` is the sum of two
literal natural dyadic blocks: the aligned block starting at `floor M`, plus the possible one-point
rounding tail in the block starting at `2 floor M`.  A unit-coefficient interval `(L,U]` is exactly
the natural block `(floor L,floor U]`.

These identities lose no coefficients and introduce no rounding majorant.
-/

namespace RHTower.Sieve

open Complex Finset ArithmeticFunction

noncomputable section

/-- Coefficients on the real dyadic interval `(M,2M]`. -/
def mtRealDyadicSourceCoeff (a : ℕ → ℂ) (M : ℝ) : ℕ → ℂ :=
  fun n => mtRealIntervalAF a M (2 * M) n

/-- Part of a coefficient sequence strictly above the first aligned natural dyadic block. -/
def mtNaturalDyadicTailCoeff (c : ℕ → ℂ) (A : ℕ) : ℕ → ℂ :=
  fun n => if 2 * A < n then c n else 0

/-- A sequence supported on `(M,2M]` splits coefficientwise into the aligned natural block
`(floor M,2 floor M]` and its possible rounding tail. -/
theorem coeff_eq_two_natural_dyadic_blocks
    (c : ℕ → ℂ) {M : ℝ} (hM : 1 ≤ M)
    (hsupp : ∀ n, c n ≠ 0 → M < (n : ℝ) ∧ (n : ℝ) ≤ 2 * M)
    (n : ℕ) :
    c n =
      mtRealIntervalAF c (⌊M⌋₊ : ℝ) (2 * ⌊M⌋₊ : ℝ) n +
      mtRealIntervalAF (mtNaturalDyadicTailCoeff c ⌊M⌋₊)
        (2 * ⌊M⌋₊ : ℝ) (4 * ⌊M⌋₊ : ℝ) n := by
  let A := ⌊M⌋₊
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hA : 0 < A := by
    dsimp only [A]
    exact Nat.floor_pos.mpr hM
  change c n =
    mtRealIntervalAF c (A : ℝ) (2 * A : ℝ) n +
      mtRealIntervalAF (mtNaturalDyadicTailCoeff c A)
        (2 * A : ℝ) (4 * A : ℝ) n
  by_cases hc : c n = 0
  · by_cases hnzero : n = 0
    · subst n
      simpa [mtRealIntervalAF] using hc
    · simp [mtRealIntervalAF, mtNaturalDyadicTailCoeff, hnzero, hc]
  have hn := hsupp n hc
  have hn0 : 0 < n := by
    by_contra hnzero
    have : n = 0 := Nat.eq_zero_of_not_pos hnzero
    subst n
    norm_num only [Nat.cast_zero] at hn
    exact (not_lt_of_ge hM0) hn.1
  rw [mtRealIntervalAF_apply_of_pos _ _ _ hn0,
    mtRealIntervalAF_apply_of_pos _ _ _ hn0]
  have hAn : (A : ℝ) < n :=
    (Nat.floor_le hM0).trans_lt hn.1
  by_cases hnA : n ≤ 2 * A
  · have hfirst : (A : ℝ) < n ∧ (n : ℝ) ≤ 2 * (A : ℝ) := by
      exact ⟨hAn, by exact_mod_cast hnA⟩
    have hnotSecond : ¬(2 * (A : ℝ) < n ∧ (n : ℝ) ≤ 4 * (A : ℝ)) := by
      intro h
      have hlowNat : 2 * A < n := by exact_mod_cast h.1
      exact (not_lt_of_ge hnA) hlowNat
    rw [if_pos hfirst, if_neg hnotSecond]
    simp
  · have hlow : 2 * A < n := Nat.lt_of_not_ge hnA
    have hMlt : M < (A : ℝ) + 1 := by
      dsimp only [A]
      exact Nat.lt_floor_add_one M
    have hnltReal : (n : ℝ) < (2 * A + 2 : ℕ) := by
      push_cast
      linarith
    have hnlt : n < 2 * A + 2 := by exact_mod_cast hnltReal
    have hupper : n ≤ 4 * A := by omega
    have hnotFirst : ¬((A : ℝ) < n ∧ (n : ℝ) ≤ 2 * (A : ℝ)) := by
      intro h
      have : n ≤ 2 * A := by exact_mod_cast h.2
      exact hnA this
    have hsecond : 2 * (A : ℝ) < n ∧ (n : ℝ) ≤ 4 * (A : ℝ) := by
      exact ⟨by exact_mod_cast hlow, by exact_mod_cast hupper⟩
    rw [if_neg hnotFirst, if_pos hsecond]
    simp [mtNaturalDyadicTailCoeff, hlow]

/-- Exact Perron-line form of the real dyadic coefficient split.  Both summands are literal Watt
blocks, including the possible rounding tail. -/
theorem perronPoly_mtRealDyadicSource_eq_two_wattBlocks
    (a : ℕ → ℂ) {M : ℝ} (hM : 1 ≤ M) (t : ℝ) :
    perronPoly (mtRealDyadicSourceCoeff a M) ⌈2 * M⌉₊ 1 t =
      mtWattCoefficientBlock (mtRealDyadicSourceCoeff a M) ⌊M⌋₊ t +
        mtWattCoefficientBlock
          (mtNaturalDyadicTailCoeff (mtRealDyadicSourceCoeff a M) ⌊M⌋₊)
          (2 * ⌊M⌋₊) t := by
  let c := mtRealDyadicSourceCoeff a M
  let A := ⌊M⌋₊
  let c₀ : ℕ → ℂ := fun n =>
    mtRealIntervalAF c (A : ℝ) (2 * (A : ℝ)) n
  let c₁ : ℕ → ℂ := fun n =>
    mtRealIntervalAF (mtNaturalDyadicTailCoeff c A) (2 * (A : ℝ))
      (2 * (2 * (A : ℝ))) n
  have hc : ∀ n, c n ≠ 0 → M < (n : ℝ) ∧ (n : ℝ) ≤ 2 * M := by
    intro n hn
    dsimp only [c, mtRealDyadicSourceCoeff] at hn ⊢
    exact (mtRealIntervalAF_scaleSupported a M (2 * M) hn).2
  have hcoeff : c = c₀ + c₁ := by
    funext n
    change c n = c₀ n + c₁ n
    simpa only [c₀, c₁, show (2 : ℝ) * (2 * A) = 4 * A by ring]
      using coeff_eq_two_natural_dyadic_blocks c hM hc n
  have hsupp : ∀ n, c n ≠ 0 → n ∈ Finset.Icc 1 ⌈2 * M⌉₊ := by
    intro n hn
    exact mtRealIntervalAF_support_nat a M (2 * M) n (by
      simpa only [c, mtRealDyadicSourceCoeff] using hn)
  have hsupp₀ : ∀ n, c₀ n ≠ 0 → n ∈ Finset.Icc 1 (2 * A) := by
    intro n hn
    exact mtWattCoefficientBlock_support c A n (by
      simpa only [c₀] using hn)
  have hsupp₁ : ∀ n, c₁ n ≠ 0 → n ∈ Finset.Icc 1 (4 * A) := by
    intro n hn
    rw [show 4 * A = 2 * (2 * A) by omega]
    exact mtWattCoefficientBlock_support
      (mtNaturalDyadicTailCoeff c A) (2 * A) n (by
        simpa only [c₁, Nat.cast_mul, Nat.cast_ofNat] using hn)
  have hblock₀ :
      mtWattCoefficientBlock (mtRealDyadicSourceCoeff a M) ⌊M⌋₊ t =
        perronPoly c₀ (2 * A) 1 t := by rfl
  have hblock₁ :
      mtWattCoefficientBlock
          (mtNaturalDyadicTailCoeff (mtRealDyadicSourceCoeff a M) ⌊M⌋₊)
          (2 * ⌊M⌋₊) t =
        perronPoly c₁ (4 * A) 1 t := by
    rw [show 4 * A = 2 * (2 * A) by omega]
    simp only [mtWattCoefficientBlock, c₁, c, A, Nat.cast_mul, Nat.cast_ofNat]
  rw [perronPoly_eq_LSeries_of_support hsupp, hblock₀, hblock₁]
  rw [perronPoly_eq_LSeries_of_support hsupp₀,
    perronPoly_eq_LSeries_of_support hsupp₁,
    ← LSeries_add (LSeriesSummable_of_support hsupp₀ _)
      (LSeriesSummable_of_support hsupp₁ _), ← hcoeff]

/-- Unit coefficients on a real interval `(L,U]` equal unit coefficients on the natural interval
`(floor L,floor U]`. -/
theorem mtRealUnitIntervalAF_eq_floor
    (L U : ℝ) (hL : 0 ≤ L) (hU : 0 ≤ U) :
    (fun n => mtRealIntervalAF (fun _ => (1 : ℂ)) L U n) =
      fun n => mtRealIntervalAF (fun _ => (1 : ℂ))
        (⌊L⌋₊ : ℝ) (⌊U⌋₊ : ℝ) n := by
  funext n
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  rw [mtRealIntervalAF_apply_of_pos _ _ _ hnpos,
    mtRealIntervalAF_apply_of_pos _ _ _ hnpos]
  have hlower : (⌊L⌋₊ : ℝ) < (n : ℝ) ↔ L < (n : ℝ) := by
    exact_mod_cast (Nat.floor_lt (n := n) hL)
  have hupper : (n : ℝ) ≤ (⌊U⌋₊ : ℝ) ↔ (n : ℝ) ≤ U := by
    constructor
    · intro h
      exact h.trans (Nat.floor_le hU)
    · intro h
      exact_mod_cast (Nat.le_floor h)
  by_cases h : L < (n : ℝ) ∧ (n : ℝ) ≤ U
  · have h' : (⌊L⌋₊ : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (⌊U⌋₊ : ℝ) :=
      ⟨hlower.mpr h.1, hupper.mpr h.2⟩
    have hNat : ⌊L⌋₊ < n ∧ n ≤ ⌊U⌋₊ := by exact_mod_cast h'
    simp [h, hNat]
  · have h' : ¬((⌊L⌋₊ : ℝ) < (n : ℝ) ∧ (n : ℝ) ≤ (⌊U⌋₊ : ℝ)) := by
      intro h'
      exact h ⟨hlower.mp h'.1, hupper.mp h'.2⟩
    have hNat : ¬(⌊L⌋₊ < n ∧ n ≤ ⌊U⌋₊) := by
      exact_mod_cast h'
    simp [h, hNat]

/-- Exact Perron-line identification of a real unit interval with its natural Watt unit block. -/
theorem perronPoly_mtRealUnitInterval_eq_mtWattUnitBlock
    {L U : ℝ} (hL : 0 ≤ L) (hU : 0 ≤ U) (t : ℝ) :
    perronPoly (fun n => mtRealIntervalAF (fun _ => (1 : ℂ)) L U n)
        ⌈U⌉₊ 1 t = mtWattUnitBlock ⌊L⌋₊ ⌊U⌋₊ t := by
  let c : ℕ → ℂ := fun n => mtRealIntervalAF (fun _ => (1 : ℂ)) L U n
  let d : ℕ → ℂ := fun n => mtRealIntervalAF (fun _ => (1 : ℂ))
    (⌊L⌋₊ : ℝ) (⌊U⌋₊ : ℝ) n
  have hcd : c = d := mtRealUnitIntervalAF_eq_floor L U hL hU
  have hc : ∀ n, c n ≠ 0 → n ∈ Finset.Icc 1 ⌈U⌉₊ := by
    intro n hn
    exact mtRealIntervalAF_support_nat (fun _ => (1 : ℂ)) L U n (by
      simpa only [c] using hn)
  have hd : ∀ n, d n ≠ 0 → n ∈ Finset.Icc 1 ⌊U⌋₊ := by
    intro n hn
    simpa only [Nat.ceil_natCast] using
      (mtRealIntervalAF_support_nat (fun _ => (1 : ℂ))
        (⌊L⌋₊ : ℝ) (⌊U⌋₊ : ℝ) n (by simpa only [d] using hn))
  rw [perronPoly_eq_LSeries_of_support hc]
  rw [mtWattUnitBlock, perronPoly_eq_LSeries_of_support hd, ← hcd]

/-- Exact scalar condition making the floored unit interval nonempty and dyadic.  The source
conditions `1 ≤ delta*M ≤ floor M` imply
`floor M < floor ((1+delta)M) ≤ 2 floor M`. -/
theorem mtRealUnitFloor_window
    {M delta : ℝ} (hM : 0 ≤ M)
    (hlow : 1 ≤ delta * M) (hhigh : delta * M ≤ (⌊M⌋₊ : ℝ)) :
    ⌊M⌋₊ < ⌊(1 + delta) * M⌋₊ ∧
      ⌊(1 + delta) * M⌋₊ ≤ 2 * ⌊M⌋₊ := by
  let A := ⌊M⌋₊
  let N' := ⌊(1 + delta) * M⌋₊
  have hMlt : M < (A : ℝ) + 1 := by
    dsimp only [A]
    exact Nat.lt_floor_add_one M
  have hsuccReal : ((A + 1 : ℕ) : ℝ) ≤ (1 + delta) * M := by
    push_cast
    linarith [Nat.floor_le hM]
  have hsucc : A + 1 ≤ N' := by
    dsimp only [N']
    exact Nat.le_floor hsuccReal
  have hupperReal : (1 + delta) * M < ((2 * A + 1 : ℕ) : ℝ) := by
    push_cast
    linarith
  have hupperLt : N' < 2 * A + 1 := by
    dsimp only [N']
    rw [Nat.floor_lt' (by omega : 2 * A + 1 ≠ 0)]
    exact hupperReal
  exact ⟨by omega, by omega⟩

end

end RHTower.Sieve
