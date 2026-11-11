import GaloisForLFunctions.VerifiedHeightRungs.ThePrimePolynomialIsRarelyLarge

/-!
# Separated zeros in every long window

`exists_separated_zeros_of_volume_lt`: cut a window into `M` slots of length `2σ`. A good height in the middle half-unit
of a slot has a zero within `σ/4`, so within `σ/2` of the slot centre. If the heights that are not good have measure
below `σ/2 · (M − n)`, at least `n + 1` slots are good, and the zeros of the good slots, in increasing order, have
consecutive gaps above `σ`: pairwise gaps `σ|i − j|`.
-/

open Complex MeasureTheory Real Set Filter Topology Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.VerifiedHeightRungs

open _root_.RHTower Zeta23

noncomputable section

/-! ### Slots -/

/-- **Few bad heights give many separated zeros.** In `M` slots of length `2σ` starting at `c`, if the heights outside
`G` have measure below `σ/2 · (M − n)` and every height of `G` has a zero within `σ/4`, then `n + 1` zeros of the window
have pairwise gaps `σ|i − j|`. -/
theorem exists_separated_zeros_of_volume_lt {c σ : ℝ} (hσ : 0 < σ) {M n : ℕ} {G : Set ℝ}
    (hbad : volume (Icc c (c + 2 * M * σ) \ G) < ENNReal.ofReal (σ / 2 * ((M : ℝ) - n)))
    (hzero : ∀ t ∈ Icc c (c + 2 * M * σ), t ∈ G → ∃ ρ ∈ zetaZeroConfig.carrier, |ρ.im - t| < σ / 4) :
    ∃ node : ℕ → zetaZeroConfig.carrier,
      (∀ j ∈ range (n + 1), c ≤ ((node j : ℂ)).im ∧ ((node j : ℂ)).im ≤ c + 2 * M * σ) ∧
      ∀ i ∈ range (n + 1), ∀ j ∈ range (n + 1),
        σ * |(i : ℝ) - j| ≤ |((node i : ℂ)).im - ((node j : ℂ)).im| := by
  classical
  -- The middle half-unit of slot `k`.
  set J : ℕ → Set ℝ := fun k => Icc (c + 2 * k * σ + 3 * σ / 4) (c + 2 * k * σ + 5 * σ / 4) with hJ
  have hJsub : ∀ k ∈ range M, J k ⊆ Icc c (c + 2 * M * σ) := by
    intro k hk t ht
    have hkM : (k : ℝ) + 1 ≤ M := by exact_mod_cast Finset.mem_range.1 hk
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    obtain ⟨h1, h2⟩ := ht
    constructor <;> nlinarith only [h1, h2, hkM, hk0, hσ]
  set Good := (range M).filter (fun k => ∃ t ∈ J k, t ∈ G) with hGood
  -- At least `n + 1` slots are good.
  have hcard : n + 1 ≤ Good.card := by
    by_contra hlt
    push Not at hlt
    set Bad := range M \ Good with hBad
    have hBc : Bad.card = M - Good.card := by
      rw [hBad, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_range]
    have hGM : Good.card ≤ M := (Finset.card_filter_le _ _).trans (Finset.card_range M).le
    have hBcR : (M : ℝ) - n ≤ Bad.card := by
      rw [hBc, Nat.cast_sub hGM]
      have : (Good.card : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.1 hlt
      linarith only [this]
    have hsub : (⋃ k ∈ Bad, J k) ⊆ Icc c (c + 2 * M * σ) \ G := by
      intro t ht
      simp only [Set.mem_iUnion] at ht
      obtain ⟨k, hk, htk⟩ := ht
      have hkM : k ∈ range M := (Finset.mem_sdiff.1 hk).1
      have hkG : k ∉ Good := (Finset.mem_sdiff.1 hk).2
      refine ⟨hJsub k hkM htk, fun htG => hkG ?_⟩
      exact Finset.mem_filter.2 ⟨hkM, t, htk, htG⟩
    have hdisj : (Bad : Set ℕ).PairwiseDisjoint J := by
      intro i _ j _ hij
      refine Set.disjoint_left.2 fun t hti htj => hij ?_
      obtain ⟨h1, h2⟩ := hti
      obtain ⟨h3, h4⟩ := htj
      have hlt1 : (i : ℝ) < j + 1 := by nlinarith only [h1, h4, hσ]
      have hlt2 : (j : ℝ) < i + 1 := by nlinarith only [h2, h3, hσ]
      have a1 : i < j + 1 := by exact_mod_cast hlt1
      have a2 : j < i + 1 := by exact_mod_cast hlt2
      omega
    have hvol : volume (⋃ k ∈ Bad, J k) = ∑ k ∈ Bad, volume (J k) :=
      measure_biUnion_finset hdisj fun k _ => measurableSet_Icc
    have hJk : ∀ k, volume (J k) = ENNReal.ofReal (σ / 2) := fun k => by
      rw [hJ, Real.volume_Icc]
      congr 1
      ring
    simp only [hJk, Finset.sum_const, nsmul_eq_mul] at hvol
    have hlow : ENNReal.ofReal (σ / 2 * ((M : ℝ) - n)) ≤ volume (⋃ k ∈ Bad, J k) := by
      rw [hvol, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left hBcR (by positivity : (0 : ℝ) ≤ σ / 2)
      linarith only [this]
    exact absurd ((hlow.trans (measure_mono hsub)).trans_lt hbad) (lt_irrefl _)
  -- A zero near the centre of every good slot.
  have hne : Nonempty zetaZeroConfig.carrier := by
    obtain ⟨k, hk⟩ := Finset.card_pos.1 (lt_of_lt_of_le (Nat.succ_pos n) hcard)
    obtain ⟨hkM, t, htk, htG⟩ := Finset.mem_filter.1 hk
    obtain ⟨ρ, hρ, -⟩ := hzero t (hJsub k hkM htk) htG
    exact ⟨⟨ρ, hρ⟩⟩
  have hz : ∀ k : ℕ, ∃ ρ : zetaZeroConfig.carrier, k ∈ Good →
      c + 2 * k * σ + σ / 2 < (ρ : ℂ).im ∧ (ρ : ℂ).im < c + 2 * k * σ + 3 * σ / 2 := by
    intro k
    by_cases hk : k ∈ Good
    · obtain ⟨hkM, t, htk, htG⟩ := Finset.mem_filter.1 hk
      obtain ⟨ρ, hρ, hρt⟩ := hzero t (hJsub k hkM htk) htG
      obtain ⟨h1, h2⟩ := htk
      obtain ⟨h3, h4⟩ := abs_lt.1 hρt
      exact ⟨⟨ρ, hρ⟩, fun _ => ⟨by change _ < ρ.im; linarith only [h1, h3],
        by change ρ.im < _; linarith only [h2, h4]⟩⟩
    · exact ⟨hne.some, fun h => absurd h hk⟩
  choose z hzP using hz
  -- The good slots in increasing order.
  set e := Good.orderEmbOfFin rfl with he
  set s : ℕ → ℕ := fun j => if h : j < Good.card then e ⟨j, h⟩ else 0 with hs
  have hsG : ∀ j ∈ range (n + 1), s j ∈ Good := by
    intro j hj
    have hjc : j < Good.card := lt_of_lt_of_le (Finset.mem_range.1 hj) hcard
    simp only [hs, dif_pos hjc]
    exact Finset.orderEmbOfFin_mem Good rfl _
  have hsmono : ∀ j, j + 1 < n + 1 → s j < s (j + 1) := by
    intro j hj
    have hjc : j + 1 < Good.card := lt_of_lt_of_le hj hcard
    have hjc' : j < Good.card := by omega
    simp only [hs, dif_pos hjc, dif_pos hjc']
    exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self j))
  set v : ℕ → ℝ := fun j => ((z (s j) : ℂ)).im with hv
  have hstep : ∀ j, j + 1 < n + 1 → v j + σ ≤ v (j + 1) := by
    intro j hj
    have h1 := hzP (s j) (hsG j (Finset.mem_range.2 (by omega)))
    have h2 := hzP (s (j + 1)) (hsG (j + 1) (Finset.mem_range.2 hj))
    have h3 : ((s j : ℕ) : ℝ) + 1 ≤ (s (j + 1) : ℕ) := by exact_mod_cast hsmono j hj
    simp only [hv]
    nlinarith only [h1.2, h2.1, h3, hσ]
  have htel : ∀ i j, i ≤ j → j < n + 1 → ((j : ℝ) - i) * σ ≤ v j - v i := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => intro _; simp
    | succ j hij ih =>
      intro hj
      have h1 := ih (by omega)
      have h2 := hstep j hj
      push_cast
      linarith only [h1, h2]
  refine ⟨fun j => z (s j), fun j hj => ?_, fun i hi j hj => ?_⟩
  · have hG := hsG j hj
    have hsM : (s j : ℝ) + 1 ≤ M := by exact_mod_cast Finset.mem_range.1 (Finset.mem_filter.1 hG).1
    have hs0 : (0 : ℝ) ≤ s j := Nat.cast_nonneg _
    obtain ⟨h1, h2⟩ := hzP (s j) hG
    constructor <;> nlinarith only [h1, h2, hsM, hs0, hσ]
  · have hin : i < n + 1 := Finset.mem_range.1 hi
    have hjn : j < n + 1 := Finset.mem_range.1 hj
    rcases le_total i j with hij | hji
    · have h := htel i j hij hjn
      have hij' : (i : ℝ) ≤ j := by exact_mod_cast hij
      rw [abs_of_nonpos (by linarith only [hij']), abs_sub_comm]
      calc σ * -((i : ℝ) - j) = ((j : ℝ) - i) * σ := by ring
        _ ≤ v j - v i := h
        _ ≤ |v j - v i| := le_abs_self _
    · have h := htel j i hji hin
      have hji' : (j : ℝ) ≤ i := by exact_mod_cast hji
      rw [abs_of_nonneg (by linarith only [hji'])]
      calc σ * ((i : ℝ) - j) = ((i : ℝ) - j) * σ := by ring
        _ ≤ v i - v j := h
        _ ≤ |v i - v j| := le_abs_self _

end

end GaloisForLFunctions.VerifiedHeightRungs
