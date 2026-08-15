import GaloisForLFunctions.HTGeometry.AnchoredProjectiveRecurrenceConservationLaw

/-!
# The projective rank of a separable spectrum

An energy level that is a sum of one local level per site has anchored gaps in the rational span of
the local gaps against one fixed local reference level.  There are at most one fewer such local gaps
per level than the number of levels, so the anchored rational rank of a separable spectrum is at
most the number of sites times one less than the number of local levels.

That bound is strictly smaller than the maximal rank of the full level set, so no separable spectrum
is maximally projective.
-/

open Filter Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section SeparableRank

variable {S : Type*} [Fintype S] {C : Type*} [Fintype C] [DecidableEq C]
variable {L : C → Type*} [∀ c, Fintype (L c)] [∀ c, DecidableEq (L c)]

set_option linter.unusedSectionVars false

/-- The local gaps of a separable spectrum against one fixed local reference configuration. -/
def localGapFinset (lam : ∀ c, L c → ℝ) (y : ∀ c, L c) : Finset ℝ :=
  Finset.univ.biUnion fun c : C =>
    (Finset.univ.erase (y c)).image fun l => lam c l - lam c (y c)

theorem card_localGapFinset_le (lam : ∀ c, L c → ℝ) (y : ∀ c, L c) :
    (localGapFinset lam y).card ≤ ∑ c : C, (Fintype.card (L c) - 1) := by
  classical
  refine le_trans (Finset.card_biUnion_le) ?_
  refine Finset.sum_le_sum fun c _ => ?_
  refine le_trans (Finset.card_image_le) ?_
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

theorem mem_span_localGapFinset (lam : ∀ c, L c → ℝ) (y x : ∀ c, L c) :
    (∑ c, lam c (x c)) - ∑ c, lam c (y c) ∈
      Submodule.span ℚ ((localGapFinset lam y : Finset ℝ) : Set ℝ) := by
  classical
  have hsplit : (∑ c, lam c (x c)) - ∑ c, lam c (y c) =
      ∑ c, (lam c (x c) - lam c (y c)) := by
    rw [Finset.sum_sub_distrib]
  rw [hsplit]
  refine Submodule.sum_mem _ fun c _ => ?_
  by_cases hc : x c = y c
  · rw [hc, sub_self]
    exact Submodule.zero_mem _
  · refine Submodule.subset_span ?_
    refine Finset.mem_coe.mpr ?_
    refine Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ c, ?_⟩
    exact Finset.mem_image.mpr ⟨x c, Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩, rfl⟩

/-- **Separable spectra have small anchored rank.**  A spectrum whose levels are sums of one local
level per site has anchored rational rank at most the sum over sites of one less than the number of
local levels. -/
theorem anchoredTemporalRank_le_of_separable (energy : S → ℝ) (lam : ∀ c, L c → ℝ)
    (hrange : Set.range energy ⊆ Set.range fun x : ∀ c, L c => ∑ c, lam c (x c))
    (ref : S) :
    anchoredTemporalRank energy ref ≤ ∑ c : C, (Fintype.card (L c) - 1) := by
  classical
  obtain ⟨y, hy⟩ := hrange ⟨ref, rfl⟩
  simp only at hy
  have hsub : anchoredGapSubspace energy ref ≤
      Submodule.span ℚ ((localGapFinset lam y : Finset ℝ) : Set ℝ) := by
    rw [anchoredGapSubspace]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    obtain ⟨x, hx⟩ := hrange ⟨i, rfl⟩
    simp only at hx
    show energy i - energy ref ∈ Submodule.span ℚ ((localGapFinset lam y : Finset ℝ) : Set ℝ)
    have hrewrite : energy i - energy ref =
        (∑ c, lam c (x c)) - ∑ c, lam c (y c) := by
      rw [hx, hy]
    rw [hrewrite]
    exact mem_span_localGapFinset lam y x
  have hfin : Module.Finite ℚ
      (Submodule.span ℚ ((localGapFinset lam y : Finset ℝ) : Set ℝ)) :=
    FiniteDimensional.span_of_finite ℚ (localGapFinset lam y).finite_toSet
  refine le_trans (Submodule.finrank_mono hsub) ?_
  refine le_trans (finrank_span_finset_le_card (localGapFinset lam y)) ?_
  exact card_localGapFinset_le lam y

end SeparableRank

section RankGap

theorem geom_sum_mul (q n : ℕ) (hq : 1 ≤ q) :
    (q - 1) * ∑ i ∈ Finset.range n, q ^ i = q ^ n - 1 := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      have hqk : 1 ≤ q ^ k := Nat.one_le_pow k q (by omega)
      have hstep : (q - 1) * q ^ k = q ^ (k + 1) - q ^ k := by
        rw [Nat.sub_one_mul, pow_succ]
        ring_nf
      rw [hstep]
      have hle : q ^ k ≤ q ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
      omega

theorem succ_add_le_two_pow (n : ℕ) (hn : 2 ≤ n) : n + 2 ≤ 2 ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
      rcases Nat.lt_or_ge k 2 with hk | hk
      · interval_cases k
        · omega
        · norm_num
      · have hk2 := ih hk
        have hdouble : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by ring
        omega

theorem lt_geom_sum (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    n < ∑ i ∈ Finset.range n, q ^ i := by
  have hmono : ∑ i ∈ Finset.range n, 2 ^ i ≤ ∑ i ∈ Finset.range n, q ^ i :=
    Finset.sum_le_sum fun i _ => Nat.pow_le_pow_left hq i
  have hgeo : (2 - 1) * ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := geom_sum_mul 2 n (by omega)
  have hpow := succ_add_le_two_pow n hn
  omega

/-- The separable rank ceiling is strictly below the full level count. -/
theorem separable_rank_lt (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    n * (q - 1) < q ^ n - 1 := by
  have hgeo : (q - 1) * ∑ i ∈ Finset.range n, q ^ i = q ^ n - 1 :=
    geom_sum_mul q n (by omega)
  have hlt : n < ∑ i ∈ Finset.range n, q ^ i := lt_geom_sum n q hn hq
  have hq0 : 0 < q - 1 := by omega
  calc n * (q - 1) = (q - 1) * n := by ring
    _ < (q - 1) * ∑ i ∈ Finset.range n, q ^ i := by
        exact mul_lt_mul_of_pos_left hlt hq0
    _ = q ^ n - 1 := hgeo

end RankGap

end

end GaloisForLFunctions.HTGeometry
