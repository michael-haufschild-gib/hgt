import GaloisForLFunctions.HTGeometry.PolynomialPatternWeight
import GaloisForLFunctions.HTGeometry.PolynomialPowerConvexConfinement
import Mathlib.Order.PiLex

/-!
# Moment signatures of multiplicity patterns and power-sum gaps

A pattern `p : Fin M → Fin (D + 1)` places multiplicity `p r` at the integer point `r`; its moments
are `m_j(p) = ∑_r p r · r^j` and its power valuation is `V_β(p, x) = ∑_r p r · (x + r)^β`. Patterns
in a finite set are ordered lexicographically by their moment signature `(m_2, …, m_{R+1})`, and the
minimal cluster is the set of patterns attaining the minimal signature. If two patterns have the same
total count `D` and the same first moment, and their moments agree below index `j` with
`m_j(p₀) < m_j(p)` for some `2 ≤ j ≤ ⌈β⌉ - 1`, then the asymptotics of finite differences of `x^β`
give a power gap `V_β(p, x) - V_β(p₀, x) ≥ c x^{β - (⌈β⌉ - 1)}` for all large `x`.

## Main results

- `polynomialPatternMoment`, `polynomialPatternSignature`: moments and moment signature.
- `polynomialPatternMinimalCluster`: patterns of minimal signature; nonempty and contained in `S`.
- `exists_first_signature_moment_lt_of_mem_not_cluster`: a pattern outside the minimal cluster has
  a first signature index where its moment strictly exceeds that of a cluster member.
- `polynomialPatternPowerValuation_sub`: the difference of power valuations is a finite power
  difference of the pattern-difference polynomial.
- `eventually_polynomialPatternPower_gap_of_signature_lt`: for `β > 2`, equal counts, equal first
  moments and a first moment gap at index `i + 2`, there is `c > 0` with
  `c · x^{β - (⌈β⌉ - 1)} ≤ V_β(p, x) - V_β(p₀, x)` eventually as `x → ∞`.

## Hypotheses

All results are unconditional. The gap theorem assumes `2 < β`, equal total counts `D`, equal first
moments, and the stated first strict moment inequality.
-/

open Filter Finset PowerSeries MvPolynomial Polynomial Topology Asymptotics Set

namespace GaloisForLFunctions

noncomputable section

/-- The `j`-th moment `∑_r p r · r^j` of a multiplicity pattern. -/
def polynomialPatternMoment {M D : ℕ} (p : Fin M → Fin (D + 1)) (j : ℕ) : ℕ :=
  ∑ r : Fin M, (p r : ℕ) * (r : ℕ) ^ j

theorem atomPatternKey_moment {M D : ℕ} (p : Fin M → Fin (D + 1)) (j : ℕ) :
    (atomPatternKey p).sum (fun r k => (k : ℝ) * (r : ℝ) ^ j) =
      (polynomialPatternMoment p j : ℕ) := by
  classical
  rw [atomPatternKey, polynomialPatternMoment,
    ← Finsupp.sum_finsetSum_index (s := Finset.univ)
      (g := fun r : Fin M => Finsupp.single (r : ℕ) (p r : ℕ))
      (h := fun r k => (k : ℝ) * (r : ℝ) ^ j)]
  push_cast
  · apply Finset.sum_congr rfl
    intro r _
    rw [Finsupp.sum_single_index]
    push_cast
    ring
  · intro a
    simp
  · intro a b c
    push_cast
    ring

/-- For patterns of equal total count `D`, the `j`-th stretched moment of their difference
polynomial is `m_j(p₁) - m_j(p₀)`. -/
theorem stretchedMoment_atomPatternDifference {M D : ℕ}
    (p₀ p₁ : Fin M → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hcount₁ : (∑ r, (p₁ r : ℕ)) = D) (j : ℕ) :
    stretchedMoment
        (polynomialRealCoeffFinsupp (atomPatternDifferencePolynomial p₀ p₁)) j =
      (polynomialPatternMoment p₁ j : ℝ) - polynomialPatternMoment p₀ j := by
  rw [polynomialRealCoeffFinsupp_atomPatternDifferencePolynomial p₀ p₁
    hcount₀ hcount₁, stretchedMoment_tupleDifference]
  let t₁ := tupleOfFinsupp (atomPatternKey p₁) D
    (by simpa [atomPatternKey_count] using hcount₁)
  let t₀ := tupleOfFinsupp (atomPatternKey p₀) D
    (by simpa [atomPatternKey_count] using hcount₀)
  have ht₁ : (∑ i, (t₁ i : ℝ) ^ j) = (polynomialPatternMoment p₁ j : ℝ) := by
    rw [← valuation_eq_key_sum t₁ (fun r => (r : ℝ) ^ j),
      key_tupleOfFinsupp, atomPatternKey_moment]
  have ht₀ : (∑ i, (t₀ i : ℝ) ^ j) = (polynomialPatternMoment p₀ j : ℝ) := by
    rw [← valuation_eq_key_sum t₀ (fun r => (r : ℝ) ^ j),
      key_tupleOfFinsupp, atomPatternKey_moment]
  simpa only [t₁, t₀] using congrArg₂ (· - ·) ht₁ ht₀

/-- The moment signature `[m_2(p), …, m_{R+1}(p)]`, compared lexicographically. -/
def polynomialPatternSignature {M D : ℕ} (R : ℕ)
    (p : Fin M → Fin (D + 1)) : List ℕ :=
  List.ofFn fun i : Fin R => polynomialPatternMoment p ((i : ℕ) + 2)

/-- The lexicographically minimal moment signature over a nonempty finite set of patterns. -/
noncomputable def minimalPolynomialPatternSignature {M D R : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty) : List ℕ :=
  (S.image (polynomialPatternSignature R)).min'
    (Finset.image_nonempty.mpr hS)

/-- The patterns of `S` attaining the minimal moment signature. -/
noncomputable def polynomialPatternMinimalCluster {M D R : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty) :
    Finset (Fin M → Fin (D + 1)) :=
  S.filter fun p => polynomialPatternSignature R p =
    minimalPolynomialPatternSignature (R := R) S hS

theorem polynomialPatternMinimalCluster_nonempty {M D R : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty) :
    (polynomialPatternMinimalCluster (R := R) S hS).Nonempty := by
  classical
  have hminmem : minimalPolynomialPatternSignature (R := R) S hS ∈
      S.image (polynomialPatternSignature R) := Finset.min'_mem _ _
  obtain ⟨p, hpS, hp⟩ := Finset.mem_image.mp hminmem
  exact ⟨p, Finset.mem_filter.mpr ⟨hpS, hp⟩⟩

theorem polynomialPatternMinimalCluster_subset {M D R : ℕ}
    (S : Finset (Fin M → Fin (D + 1))) (hS : S.Nonempty) :
    polynomialPatternMinimalCluster (R := R) S hS ⊆ S :=
  Finset.filter_subset _ _

theorem signature_eq_of_mem_polynomialPatternMinimalCluster {M D R : ℕ}
    {S : Finset (Fin M → Fin (D + 1))} {hS : S.Nonempty}
    {p : Fin M → Fin (D + 1)}
    (hp : p ∈ polynomialPatternMinimalCluster (R := R) S hS) :
    polynomialPatternSignature R p = minimalPolynomialPatternSignature (R := R) S hS :=
  (Finset.mem_filter.mp hp).2

/-- A pattern of `S` outside the minimal cluster has a strictly larger signature. -/
theorem minimalSignature_lt_of_mem_not_cluster {M D R : ℕ}
    {S : Finset (Fin M → Fin (D + 1))} (hS : S.Nonempty)
    {p : Fin M → Fin (D + 1)} (hpS : p ∈ S)
    (hpC : p ∉ polynomialPatternMinimalCluster (R := R) S hS) :
    minimalPolynomialPatternSignature (R := R) S hS < polynomialPatternSignature R p := by
  classical
  have hle : minimalPolynomialPatternSignature (R := R) S hS ≤ polynomialPatternSignature R p :=
    Finset.min'_le _ _ (Finset.mem_image.mpr ⟨p, hpS, rfl⟩)
  have hne : minimalPolynomialPatternSignature (R := R) S hS ≠ polynomialPatternSignature R p := by
    intro heq
    exact hpC (Finset.mem_filter.mpr ⟨hpS, heq.symm⟩)
  exact lt_of_le_of_ne hle hne

/-- Lexicographic order on `List.ofFn`: `f < g` gives a first index where `f` is smaller and
all earlier entries agree. -/
theorem exists_first_ofFn_lt {R : ℕ} {f g : Fin R → ℕ}
    (h : List.ofFn f < List.ofFn g) :
    ∃ i : Fin R, (∀ k : Fin R, k < i → f k = g k) ∧ f i < g i := by
  induction R with
  | zero => simp at h
  | succ R ih =>
      rw [List.ofFn_succ, List.ofFn_succ] at h
      by_cases hzero : f 0 = g 0
      · have htail : List.ofFn (fun i => f i.succ) <
            List.ofFn (fun i => g i.succ) := by
          change List.Lex (· < ·) _ _
          change List.Lex (· < ·)
            (f 0 :: List.ofFn (fun i => f i.succ))
            (g 0 :: List.ofFn (fun i => g i.succ)) at h
          rw [hzero] at h
          exact List.lex_cons_iff.mp h
        obtain ⟨i, hprev, hi⟩ := ih htail
        refine ⟨i.succ, ?_, hi⟩
        intro k hk
        cases k using Fin.cases with
        | zero => exact hzero
        | succ j => exact hprev j (by simpa using hk)
      · refine ⟨0, ?_, lt_of_le_of_ne (List.head_le_of_lt h) hzero⟩
        intro k hk
        exact (Fin.not_lt_zero k hk).elim

/-- For `p₀` in the minimal cluster and `p ∈ S` outside it, there is a first index `i` with
`m_{k+2}(p₀) = m_{k+2}(p)` for `k < i` and `m_{i+2}(p₀) < m_{i+2}(p)`. -/
theorem exists_first_signature_moment_lt_of_mem_not_cluster {M D R : ℕ}
    {S : Finset (Fin M → Fin (D + 1))} (hS : S.Nonempty)
    {p₀ p : Fin M → Fin (D + 1)}
    (hp₀ : p₀ ∈ polynomialPatternMinimalCluster (R := R) S hS)
    (hpS : p ∈ S) (hpC : p ∉ polynomialPatternMinimalCluster (R := R) S hS) :
    ∃ i : Fin R,
      (∀ k : Fin R, k < i →
        polynomialPatternMoment p₀ ((k : ℕ) + 2) =
          polynomialPatternMoment p ((k : ℕ) + 2)) ∧
      polynomialPatternMoment p₀ ((i : ℕ) + 2) <
        polynomialPatternMoment p ((i : ℕ) + 2) := by
  have hlt := minimalSignature_lt_of_mem_not_cluster hS hpS hpC
  rw [← signature_eq_of_mem_polynomialPatternMinimalCluster hp₀] at hlt
  exact exists_first_ofFn_lt hlt

theorem polynomialPatternMoment_zero {M D : ℕ}
    (p : Fin M → Fin (D + 1)) :
    polynomialPatternMoment p 0 = ∑ r, (p r : ℕ) := by
  simp [polynomialPatternMoment]

theorem polynomialPatternMoment_one {M D : ℕ}
    (p : Fin M → Fin (D + 1)) :
    polynomialPatternMoment p 1 = ∑ r : Fin M, (r : ℕ) * (p r : ℕ) := by
  rw [polynomialPatternMoment]
  apply Finset.sum_congr rfl
  intro r _
  simp [Nat.mul_comm]

/-- The power valuation `V_β(p, x) = ∑_r p r · (x + r)^β`. -/
def polynomialPatternPowerValuation {M D : ℕ} (β : ℝ)
    (p : Fin M → Fin (D + 1)) (x : ℝ) : ℝ :=
  ∑ r : Fin M, (p r : ℝ) * (x + (r : ℝ)) ^ β

/-- For patterns of equal count `D`, `V_β(p₁, x) - V_β(p₀, x)` is the finite power difference of
`x^β` along the pattern-difference polynomial. -/
theorem polynomialPatternPowerValuation_sub {M D : ℕ}
    (β x : ℝ) (p₀ p₁ : Fin M → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hcount₁ : (∑ r, (p₁ r : ℕ)) = D) :
    polynomialPatternPowerValuation β p₁ x -
        polynomialPatternPowerValuation β p₀ x =
      polynomialPowerFiniteDifference β
        (polynomialRealCoeffFinsupp (atomPatternDifferencePolynomial p₀ p₁)) x := by
  rw [polynomialRealCoeffFinsupp_atomPatternDifferencePolynomial p₀ p₁
    hcount₀ hcount₁, polynomialPowerFiniteDifference_tupleDifference]
  let t₁ := tupleOfFinsupp (atomPatternKey p₁) D
    (by simpa [atomPatternKey_count] using hcount₁)
  let t₀ := tupleOfFinsupp (atomPatternKey p₀) D
    (by simpa [atomPatternKey_count] using hcount₀)
  have ht (p : Fin M → Fin (D + 1))
      (hcount : (∑ r, (p r : ℕ)) = D) :
      let t := tupleOfFinsupp (atomPatternKey p) D
        (by simpa [atomPatternKey_count] using hcount)
      (∑ i, (x + t i) ^ β) = polynomialPatternPowerValuation β p x := by
    dsimp only
    rw [← valuation_eq_key_sum
        (tupleOfFinsupp (atomPatternKey p) D
          (by simpa [atomPatternKey_count] using hcount))
        (fun r => (x + r) ^ β),
      key_tupleOfFinsupp, polynomialPatternPowerValuation]
    rw [atomPatternKey]
    rw [← Finsupp.sum_finsetSum_index (s := Finset.univ)
      (g := fun r : Fin M => Finsupp.single (r : ℕ) (p r : ℕ))
      (h := fun r k => (k : ℝ) * (x + r) ^ β)]
    · apply Finset.sum_congr rfl
      intro r _
      rw [Finsupp.sum_single_index]
      simp
    · intro a
      simp
    · intro a b c
      push_cast
      ring
  rw [ht p₁ hcount₁, ht p₀ hcount₀]

/-- If `j < β` then the falling factorial `β (β - 1) ⋯ (β - j + 1)` is positive. -/
theorem descPochhammer_eval_pos_of_natCast_lt {β : ℝ} {j : ℕ}
    (hjβ : (j : ℝ) < β) : 0 < (descPochhammer ℝ j).eval β := by
  rw [descPochhammer_eval_eq_prod_range]
  apply Finset.prod_pos
  intro k hk
  have hklt : k < j := Finset.mem_range.mp hk
  have : (k : ℝ) < β := (Nat.cast_lt.mpr hklt).trans hjβ
  linarith

/-- If `f ~ g` at infinity and `g` is eventually positive, then eventually `g / 2 ≤ f`. -/
theorem eventually_half_le_of_isEquivalent_positive {f g : ℝ → ℝ}
    (hfg : f ~[atTop] g) (hg : ∀ᶠ x in atTop, 0 < g x) :
    ∀ᶠ x in atTop, g x / 2 ≤ f x := by
  have hb := hfg.isLittleO.bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [hb, hg] with x hbound hgx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hgx] at hbound
  change |f x - g x| ≤ 1 / 2 * g x at hbound
  have hneg : -(f x - g x) ≤ |f x - g x| := neg_le_abs _
  linarith

/-- Assuming `2 < β`, equal counts `D`, equal first moments, and moments agreeing below index
`i + 2` with `m_{i+2}(p₀) < m_{i+2}(p)`, there is `c > 0` with
`c · x^{β - (⌈β⌉ - 1)} ≤ V_β(p, x) - V_β(p₀, x)` for all large `x`. -/
theorem eventually_polynomialPatternPower_gap_of_signature_lt
    {β : ℝ} (hβ : 2 < β) {M D : ℕ}
    (p₀ p : Fin M → Fin (D + 1))
    (hcount₀ : (∑ r, (p₀ r : ℕ)) = D)
    (hcount : (∑ r, (p r : ℕ)) = D)
    (hsum : (∑ r : Fin M, (r : ℕ) * (p₀ r : ℕ)) =
      ∑ r : Fin M, (r : ℕ) * (p r : ℕ))
    (i : Fin (Nat.ceil β - 2))
    (hprev : ∀ k : Fin (Nat.ceil β - 2), k < i →
      polynomialPatternMoment p₀ ((k : ℕ) + 2) =
        polynomialPatternMoment p ((k : ℕ) + 2))
    (hi : polynomialPatternMoment p₀ ((i : ℕ) + 2) <
      polynomialPatternMoment p ((i : ℕ) + 2)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (β - (Nat.ceil β - 1 : ℕ)) ≤
        polynomialPatternPowerValuation β p x -
          polynomialPatternPowerValuation β p₀ x := by
  let j := (i : ℕ) + 2
  let d := polynomialRealCoeffFinsupp (atomPatternDifferencePolynomial p₀ p)
  have hceil3 : 3 ≤ Nat.ceil β := by
    by_contra hnot
    have hceil2 : Nat.ceil β ≤ 2 := by omega
    have : β ≤ (2 : ℝ) := Nat.ceil_le.mp hceil2
    linarith
  have hjceil : j ≤ Nat.ceil β - 1 := by
    dsimp [j]
    omega
  have hceilLt : ((Nat.ceil β - 1 : ℕ) : ℝ) < β := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ β by linarith)
    have hcast : ((Nat.ceil β - 1 : ℕ) : ℝ) = (Nat.ceil β : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    rw [hcast]
    linarith
  have hjβ : (j : ℝ) < β := by
    exact (Nat.cast_le.mpr hjceil).trans_lt hceilLt
  have hcancel : ∀ k < j, stretchedMoment d k = 0 := by
    intro k hk
    dsimp [d]
    rw [stretchedMoment_atomPatternDifference p₀ p hcount₀ hcount]
    rcases lt_trichotomy k 1 with hk0 | hk1 | hk2
    · have : k = 0 := by omega
      subst k
      rw [polynomialPatternMoment_zero, polynomialPatternMoment_zero,
        hcount₀, hcount]
      simp
    · subst k
      rw [polynomialPatternMoment_one, polynomialPatternMoment_one, hsum]
      simp
    · let u : Fin (Nat.ceil β - 2) := ⟨k - 2, by omega⟩
      have hui : u < i := by apply Fin.mk_lt_mk.mpr; dsimp [u, j] at *; omega
      have heq := hprev u hui
      have hu : (u : ℕ) + 2 = k := by dsimp [u]; omega
      rw [hu] at heq
      rw [heq]
      simp
  have hmomentPos : 0 < stretchedMoment d j := by
    dsimp [d]
    rw [stretchedMoment_atomPatternDifference p₀ p hcount₀ hcount]
    apply sub_pos.mpr
    exact_mod_cast hi
  have hpochPos : 0 < (descPochhammer ℝ j).eval β :=
    descPochhammer_eval_pos_of_natCast_lt hjβ
  let c₀ := polynomialPowerDifferenceCoefficient β d j
  have hc₀ : 0 < c₀ := by
    dsimp [c₀, polynomialPowerDifferenceCoefficient]
    exact div_pos (mul_pos hmomentPos hpochPos) (by positivity)
  have hequiv := polynomialPowerFiniteDifference_isEquivalent d j hcancel
    hmomentPos.ne' hpochPos.ne'
  have hleadPos : ∀ᶠ x : ℝ in atTop, 0 < c₀ * x ^ (β - j) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact mul_pos hc₀ (Real.rpow_pos_of_pos hx _)
  have hhalf := eventually_half_le_of_isEquivalent_positive hequiv hleadPos
  refine ⟨c₀ / 2, by positivity, ?_⟩
  filter_upwards [hhalf, eventually_ge_atTop (1 : ℝ)] with x hx hgone
  rw [polynomialPatternPowerValuation_sub β x p₀ p hcount₀ hcount]
  have hpow : x ^ (β - (Nat.ceil β - 1 : ℕ)) ≤ x ^ (β - j) := by
    apply Real.rpow_le_rpow_of_exponent_le hgone
    exact sub_le_sub_left (Nat.cast_le.mpr hjceil) β
  have hmul : (c₀ / 2) * x ^ (β - (Nat.ceil β - 1 : ℕ)) ≤
      (c₀ / 2) * x ^ (β - j) :=
    mul_le_mul_of_nonneg_left hpow (by positivity)
  have hx' : (c₀ / 2) * x ^ (β - j) ≤ polynomialPowerFiniteDifference β d x := by
    convert hx using 1 ; ring
  have hstep := hmul.trans hx'
  simpa [c₀, d] using hstep


end

end GaloisForLFunctions
