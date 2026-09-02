import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierHeathBrownSupport
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueSquareLift

/-!
# Squared unit block as a Heath--Brown dense factor

The fourth power in the Watt/DI moment is the square norm of the squared reciprocal unit block.
This file identifies its raw coefficient with an ordered factor-pair count and packages the square
as the exact real-coefficient dense factor accepted by Heath--Brown's Lemma 3.4.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Exact reciprocal indicator coefficient of the truncated unit block. -/
theorem mtWattUnitCoeff_eq_indicator_inv
    (N N' : ℕ) (j : Fin N') :
    mtWattUnitCoeff N N' j =
      if N < (j : ℕ) + 1 then (((((j : ℕ) + 1 : ℝ))⁻¹ : ℝ) : ℂ) else 0 := by
  rw [mtWattUnitCoeff, twistedTruncCoeff,
    mtRealIntervalAF_apply_of_pos _ _ _ (by omega)]
  have hjupper : (j : ℕ) + 1 ≤ N' := j.isLt
  by_cases hj : N < (j : ℕ) + 1
  · have hreal : (N : ℝ) < (((j : ℕ) + 1 : ℕ) : ℝ) ∧
        (((j : ℕ) + 1 : ℕ) : ℝ) ≤ (N' : ℝ) := by
      exact_mod_cast (show N < (j : ℕ) + 1 ∧ (j : ℕ) + 1 ≤ N' from ⟨hj, hjupper⟩)
    rw [if_pos hreal, if_pos hj, one_mul, Real.rpow_neg_one]
  · have hreal : ¬((N : ℝ) < (((j : ℕ) + 1 : ℕ) : ℝ) ∧
        (((j : ℕ) + 1 : ℕ) : ℝ) ≤ (N' : ℝ)) := by
      intro h
      apply hj
      exact_mod_cast h.1
    rw [if_neg hreal, if_neg hj, zero_mul]

/-- Ordered supported factor pairs contributing to one coefficient of the squared unit block. -/
def mtWattUnitPairFibre (N N' : ℕ) (r : Fin (N' * N')) :
    Finset (Fin N' × Fin N') :=
  ((Finset.univ : Finset (Fin N' × Fin N')).filter fun q =>
      ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) = (r : ℕ) + 1).filter fun q =>
        N < (q.1 : ℕ) + 1 ∧ N < (q.2 : ℕ) + 1

/-- Raw ordered factor-pair multiplicity. -/
def mtWattUnitPairCount (N N' : ℕ) (r : Fin (N' * N')) : ℕ :=
  (mtWattUnitPairFibre N N' r).card

/-- A squared reciprocal-unit coefficient is raw pair multiplicity divided by its anchor. -/
theorem mtWattUnitSquareCoeff_eq_pairCount_div
    (N N' : ℕ) (r : Fin (N' * N')) :
    mtWattUnitSquareCoeff N N' r =
      (((mtWattUnitPairCount N N' r : ℝ) /
        (((r : ℕ) + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
  classical
  let F : Finset (Fin N' × Fin N') :=
    (Finset.univ : Finset (Fin N' × Fin N')).filter fun q =>
      ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) = (r : ℕ) + 1
  let c : ℂ := ((↑((r : ℕ) + 1) : ℝ)⁻¹ : ℂ)
  have hterm : ∀ q ∈ F,
      mtWattUnitCoeff N N' q.1 * mtWattUnitCoeff N N' q.2 =
        if N < (q.1 : ℕ) + 1 ∧ N < (q.2 : ℕ) + 1 then c else 0 := by
    intro q hq
    rw [mtWattUnitCoeff_eq_indicator_inv,
      mtWattUnitCoeff_eq_indicator_inv]
    by_cases h₁ : N < (q.1 : ℕ) + 1
    · by_cases h₂ : N < (q.2 : ℕ) + 1
      · rw [if_pos h₁, if_pos h₂, if_pos ⟨h₁, h₂⟩]
        have hprod := (Finset.mem_filter.mp hq).2
        dsimp only [c]
        push_cast
        rw [← mul_inv]
        congr 1
        exact_mod_cast hprod
      · rw [if_pos h₁, if_neg h₂, mul_zero, if_neg]
        exact fun h => h₂ h.2
    · rw [if_neg h₁, zero_mul, if_neg]
      exact fun h => h₁ h.1
  rw [mtWattUnitSquareCoeff, dirConv]
  change (∑ q ∈ F,
      mtWattUnitCoeff N N' q.1 * mtWattUnitCoeff N N' q.2) = _
  calc
    (∑ q ∈ F, mtWattUnitCoeff N N' q.1 * mtWattUnitCoeff N N' q.2) =
        ∑ q ∈ F, if N < (q.1 : ℕ) + 1 ∧ N < (q.2 : ℕ) + 1 then c else 0 := by
      exact Finset.sum_congr rfl hterm
    _ = ∑ _q ∈ mtWattUnitPairFibre N N' r, c := by
      rw [mtWattUnitPairFibre]
      simp only [F, Finset.sum_filter]
    _ = (mtWattUnitPairCount N N' r : ℂ) * c := by
      simp [mtWattUnitPairCount]
    _ = (((mtWattUnitPairCount N N' r : ℝ) /
        (((r : ℕ) + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by
      dsimp only [c]
      push_cast
      rw [div_eq_mul_inv]

/-- Total real coefficient whose quotient by the anchor is the squared unit-block coefficient. -/
def mtWattUnitSquareRawCoeff (N N' m : ℕ) : ℝ :=
  if h : 1 ≤ m ∧ m ≤ N' * N' then
    mtWattUnitPairCount N N' ⟨m - 1, by omega⟩
  else 0

theorem mtWattUnitSquareRawCoeff_apply_finSucc
    (N N' : ℕ) (r : Fin (N' * N')) :
    mtWattUnitSquareRawCoeff N N' ((r : ℕ) + 1) =
      mtWattUnitPairCount N N' r := by
  rw [mtWattUnitSquareRawCoeff, dif_pos]
  · congr 2
  · exact ⟨by omega, r.isLt⟩

/-- A full positive-interval one-line factor is a standard Dirichlet polynomial at reflected
height, with the anchor division absorbed into its coefficient. -/
theorem heathBrownDenseOneLineFactor_positiveInterval_eq_dirPoly
    {K : ℕ} (hK : 1 ≤ K) (a : ℕ → ℝ) (t : ℝ) :
    heathBrownDenseOneLineFactor (heathBrownPositiveInterval K hK) a t =
      dirPoly K (fun r => (((a ((r : ℕ) + 1) /
        (((r : ℕ) + 1 : ℕ) : ℝ) : ℝ)) : ℂ)) (-t) := by
  rw [heathBrownDenseOneLineFactor, dirPoly]
  rw [← sum_fin_heathBrownFinSucc_eq_positiveInterval hK]
  apply Finset.sum_congr rfl
  intro r hr
  rw [heathBrownDirichletPhase]
  congr 2
  simp [heathBrownFinSucc]

/-- Exact dense-factor realization of the square of the reciprocal unit block. -/
theorem heathBrownDenseOneLineFactor_mtWattUnitSquareRawCoeff_eq
    (N : ℕ) {N' : ℕ} (hN' : 1 ≤ N') (t : ℝ) :
    heathBrownDenseOneLineFactor
        (heathBrownPositiveInterval (N' * N')
          (Nat.mul_pos (by omega) (by omega)))
        (mtWattUnitSquareRawCoeff N N') t =
      (mtWattUnitBlock N N' t) ^ 2 := by
  rw [heathBrownDenseOneLineFactor_positiveInterval_eq_dirPoly]
  calc
    dirPoly (N' * N')
        (fun r => (((mtWattUnitSquareRawCoeff N N' ((r : ℕ) + 1) /
          (((r : ℕ) + 1 : ℕ) : ℝ) : ℝ)) : ℂ)) (-t) =
        dirPoly (N' * N') (mtWattUnitSquareCoeff N N') (-t) := by
      apply Finset.sum_congr rfl
      intro r hr
      change (((mtWattUnitSquareRawCoeff N N' ((r : ℕ) + 1) /
          (((r : ℕ) + 1 : ℕ) : ℝ) : ℝ)) : ℂ) * _ = _
      rw [mtWattUnitSquareRawCoeff_apply_finSucc]
      exact congrArg (fun z : ℂ => z *
        Complex.exp ((((-t) * Real.log (((r : ℕ) : ℝ) + 1) : ℝ) : ℂ) * Complex.I))
        (mtWattUnitSquareCoeff_eq_pairCount_div N N' r).symm
    _ = (mtWattUnitBlock N N' t) ^ 2 := by
      rw [pow_two, mtWattUnitBlock_eq_dirPoly]
      exact (dirPoly_mul_eq_dirPoly N' N'
        (mtWattUnitCoeff N N') (mtWattUnitCoeff N N') (-t)).symm

/-- Supported ordered pairs form a subset of the unrestricted product fibre. -/
theorem mtWattUnitPairCount_le_heathBrownSquareFibreCard
    (N N' : ℕ) (r : Fin (N' * N')) :
    mtWattUnitPairCount N N' r ≤ heathBrownSquareFibreCard N' r := by
  classical
  rw [mtWattUnitPairCount, mtWattUnitPairFibre, heathBrownSquareFibreCard]
  calc
    (((Finset.univ : Finset (Fin N' × Fin N')).filter fun q =>
          ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) = (r : ℕ) + 1).filter fun q =>
        N < (q.1 : ℕ) + 1 ∧ N < (q.2 : ℕ) + 1).card ≤
        ((Finset.univ : Finset (Fin N' × Fin N')).filter fun q =>
          ((q.1 : ℕ) + 1) * ((q.2 : ℕ) + 1) = (r : ℕ) + 1).card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = ((Finset.univ : Finset (Fin N' × Fin N')).filter fun q =>
        prodIdx q = r).card := congrArg Finset.card (filter_prodIdx_eq r)

theorem mtWattUnitSquareRawCoeff_nonneg (N N' m : ℕ) :
    0 ≤ mtWattUnitSquareRawCoeff N N' m := by
  rw [mtWattUnitSquareRawCoeff]
  split <;> positivity

/-- Uniform divisor-scale bound for every totalized raw square coefficient. -/
theorem mtWattUnitSquareRawCoeff_le_divisorScale
    (N : ℕ) {N' : ℕ} (hN' : 1 ≤ N') {eta : ℝ} (heta : 0 < eta) (m : ℕ) :
    mtWattUnitSquareRawCoeff N N' m ≤ heathBrownSquareDivisorScale N' eta := by
  rw [mtWattUnitSquareRawCoeff]
  split
  next h =>
    let r : Fin (N' * N') := ⟨m - 1, by omega⟩
    calc
      (mtWattUnitPairCount N N' r : ℝ) ≤
          (heathBrownSquareFibreCard N' r : ℝ) := by
        exact_mod_cast mtWattUnitPairCount_le_heathBrownSquareFibreCard N N' r
      _ ≤ heathBrownSquareDivisorScale N' eta :=
        cast_heathBrownSquareFibreCard_le_divisorScale heta r
  next h =>
    exact zero_le_one.trans (one_le_heathBrownSquareDivisorScale hN' heta)

theorem abs_mtWattUnitSquareRawCoeff_le_divisorScale
    (N : ℕ) {N' : ℕ} (hN' : 1 ≤ N') {eta : ℝ} (heta : 0 < eta) (m : ℕ) :
    |mtWattUnitSquareRawCoeff N N' m| ≤ heathBrownSquareDivisorScale N' eta := by
  rw [abs_of_nonneg (mtWattUnitSquareRawCoeff_nonneg N N' m)]
  exact mtWattUnitSquareRawCoeff_le_divisorScale N hN' heta m

/-- The canonical dense-coefficient maximum inherits the same divisor-scale envelope. -/
theorem heathBrownDenseCoefficientMax_mtWattUnitSquareRawCoeff_le_divisorScale
    (N : ℕ) {N' : ℕ} (hN' : 1 ≤ N') {eta : ℝ} (heta : 0 < eta) :
    heathBrownDenseCoefficientMax
        (heathBrownPositiveInterval (N' * N')
          (Nat.mul_pos (by omega) (by omega)))
        (mtWattUnitSquareRawCoeff N N') ≤
      heathBrownSquareDivisorScale N' eta := by
  classical
  let hsq : 1 ≤ N' * N' := Nat.mul_pos (by omega) (by omega)
  let B := heathBrownPositiveInterval (N' * N') hsq
  have hB : B.Nonempty :=
    ⟨heathBrownPositivePart 1,
      heathBrownPositivePart_mem_positiveInterval hsq
        (Finset.mem_Icc.mpr ⟨le_rfl, hsq⟩)⟩
  change heathBrownDenseCoefficientMax B (mtWattUnitSquareRawCoeff N N') ≤ _
  rw [heathBrownDenseCoefficientMax, dif_pos hB]
  apply Finset.sup'_le hB
  intro m hm
  exact abs_mtWattUnitSquareRawCoeff_le_divisorScale N hN' heta (m : ℕ)

/-- Positive-integer realization of the dyadic interval `(K,2K]`. -/
def mtWattPositiveDyadicInterval (K : ℕ) : Finset PNat :=
  Finset.Ioc (heathBrownPositivePart K) (heathBrownPositivePart (2 * K))

@[simp] theorem mem_mtWattPositiveDyadicInterval
    {K : ℕ} (hK : 1 ≤ K) {m : PNat} :
    m ∈ mtWattPositiveDyadicInterval K ↔ K < (m : ℕ) ∧ (m : ℕ) ≤ 2 * K := by
  rw [mtWattPositiveDyadicInterval, Finset.mem_Ioc]
  change (heathBrownPositivePart K : ℕ) < (m : ℕ) ∧
      (m : ℕ) ≤ (heathBrownPositivePart (2 * K) : ℕ) ↔ _
  rw [coe_heathBrownPositivePart_of_pos hK,
    coe_heathBrownPositivePart_of_pos (by omega : 1 ≤ 2 * K)]

/-- No reciprocal pair supported on `(N,N']²` has product at most `N²`. -/
theorem mtWattUnitPairCount_eq_zero_of_anchor_le_sq
    (N N' : ℕ) (r : Fin (N' * N'))
    (hr : (r : ℕ) + 1 ≤ N * N) :
    mtWattUnitPairCount N N' r = 0 := by
  classical
  rw [mtWattUnitPairCount, mtWattUnitPairFibre, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro q hq hsupp
  have hprod := (Finset.mem_filter.mp hq).2
  have hlarge : (N + 1) * (N + 1) ≤ (r : ℕ) + 1 := by
    rw [← hprod]
    exact Nat.mul_le_mul (by omega) (by omega)
  have hstrict : N * N < (N + 1) * (N + 1) := by nlinarith
  omega

theorem mtWattUnitSquareRawCoeff_eq_zero_of_le_sq
    (N N' m : ℕ) (hm : m ≤ N * N) :
    mtWattUnitSquareRawCoeff N N' m = 0 := by
  rw [mtWattUnitSquareRawCoeff]
  split
  next h =>
    let r : Fin (N' * N') := ⟨m - 1, by omega⟩
    change (mtWattUnitPairCount N N' r : ℝ) = 0
    rw [mtWattUnitPairCount_eq_zero_of_anchor_le_sq N N' r (by
      dsimp only [r]
      omega)]
    norm_num
  next => rfl

theorem mtWattUnitSquareRawCoeff_eq_zero_of_sq_lt
    (N N' m : ℕ) (hm : N' * N' < m) :
    mtWattUnitSquareRawCoeff N N' m = 0 := by
  rw [mtWattUnitSquareRawCoeff, dif_neg]
  exact fun h => by omega

theorem disjoint_mtWattPositiveDyadicInterval_sq_two_sq
    {N : ℕ} (hN : 1 ≤ N) :
    Disjoint (mtWattPositiveDyadicInterval (N * N))
      (mtWattPositiveDyadicInterval (2 * (N * N))) := by
  rw [Finset.disjoint_left]
  intro m hm₁ hm₂
  rw [mem_mtWattPositiveDyadicInterval (Nat.mul_pos (by omega) (by omega))] at hm₁
  rw [mem_mtWattPositiveDyadicInterval (by
    have hsq : 0 < N * N := Nat.mul_pos (by omega) (by omega)
    omega)] at hm₂
  omega

/-- The full squared unit block has exactly two dyadic dense pieces; coefficients outside its
actual product range vanish rather than becoming additional hypotheses. -/
theorem heathBrownDenseOneLineFactor_mtWattUnitSquareRawCoeff_eq_twoDyadic
    {N N' : ℕ} (hN : 1 ≤ N) (hN' : 1 ≤ N') (hN'le : N' ≤ 2 * N) (t : ℝ) :
    heathBrownDenseOneLineFactor
        (heathBrownPositiveInterval (N' * N')
          (Nat.mul_pos (by omega) (by omega)))
        (mtWattUnitSquareRawCoeff N N') t =
      heathBrownDenseOneLineFactor
          (mtWattPositiveDyadicInterval (N * N))
          (mtWattUnitSquareRawCoeff N N') t +
        heathBrownDenseOneLineFactor
          (mtWattPositiveDyadicInterval (2 * (N * N)))
          (mtWattUnitSquareRawCoeff N N') t := by
  classical
  let hsq : 1 ≤ N' * N' := Nat.mul_pos (by omega) (by omega)
  let full : Finset PNat := heathBrownPositiveInterval (N' * N') hsq
  let low : Finset PNat := mtWattPositiveDyadicInterval (N * N)
  let high : Finset PNat := mtWattPositiveDyadicInterval (2 * (N * N))
  let active : Finset PNat := full.filter fun m => N * N < (m : ℕ)
  let F : PNat → ℂ := fun m =>
    (((mtWattUnitSquareRawCoeff N N' (m : ℕ) / ((m : ℕ) : ℝ) : ℝ)) : ℂ) *
      heathBrownDirichletPhase m t
  have hactive_union : active ⊆ low ∪ high := by
    intro m hm
    simp only [active, Finset.mem_filter] at hm
    have hmfull := hm.1
    have hmlower := hm.2
    simp only [full, heathBrownPositiveInterval, Finset.mem_Icc] at hmfull
    change 1 ≤ (m : ℕ) ∧ (m : ℕ) ≤ N' * N' at hmfull
    have hsqle : N' * N' ≤ 4 * (N * N) := by
      have hmul := Nat.mul_le_mul hN'le hN'le
      nlinarith
    have hsqle' : N' * N' ≤ 2 * (2 * (N * N)) := by nlinarith
    by_cases hhalf : (m : ℕ) ≤ 2 * (N * N)
    · rw [Finset.mem_union]
      exact Or.inl ((mem_mtWattPositiveDyadicInterval
        (Nat.mul_pos (by omega) (by omega))).mpr ⟨hmlower, hhalf⟩)
    · rw [Finset.mem_union]
      exact Or.inr ((mem_mtWattPositiveDyadicInterval (by
        have hsqN : 0 < N * N := Nat.mul_pos (by omega) (by omega)
        omega)).mpr
        ⟨by omega, hmfull.2.trans hsqle'⟩)
  have hfull_active : (∑ m ∈ full, F m) = ∑ m ∈ active, F m := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro m hmfull hmnot
    have hmle : (m : ℕ) ≤ N * N := by
      by_contra h
      apply hmnot
      simp only [Finset.mem_filter]
      exact ⟨hmfull, by omega⟩
    change F m = 0
    simp only [F, mtWattUnitSquareRawCoeff_eq_zero_of_le_sq N N' (m : ℕ) hmle,
      zero_div, Complex.ofReal_zero, zero_mul]
  have hunion_active : (∑ m ∈ active, F m) = ∑ m ∈ low ∪ high, F m := by
    apply Finset.sum_subset hactive_union
    intro m hmunion hmnot
    have hmhigh : N * N < (m : ℕ) := by
      rw [Finset.mem_union] at hmunion
      rcases hmunion with hmlow | hmhigh
      · exact (mem_mtWattPositiveDyadicInterval
          (Nat.mul_pos (by omega) (by omega))).mp hmlow |>.1
      · have := (mem_mtWattPositiveDyadicInterval (by
          have hsqN : 0 < N * N := Nat.mul_pos (by omega) (by omega)
          omega)).mp hmhigh |>.1
        omega
    have hmout : N' * N' < (m : ℕ) := by
      by_contra h
      apply hmnot
      simp only [active, Finset.mem_filter]
      refine ⟨?_, hmhigh⟩
      simp only [full, heathBrownPositiveInterval, Finset.mem_Icc]
      change 1 ≤ (m : ℕ) ∧ (m : ℕ) ≤ N' * N'
      exact ⟨m.property, by omega⟩
    change F m = 0
    simp only [F, mtWattUnitSquareRawCoeff_eq_zero_of_sq_lt N N' (m : ℕ) hmout,
      zero_div, Complex.ofReal_zero, zero_mul]
  rw [heathBrownDenseOneLineFactor, heathBrownDenseOneLineFactor,
    heathBrownDenseOneLineFactor]
  change (∑ m ∈ full, F m) = (∑ m ∈ low, F m) + ∑ m ∈ high, F m
  rw [hfull_active, hunion_active,
    Finset.sum_union (disjoint_mtWattPositiveDyadicInterval_sq_two_sq hN)]

end

end RHTower.Sieve
