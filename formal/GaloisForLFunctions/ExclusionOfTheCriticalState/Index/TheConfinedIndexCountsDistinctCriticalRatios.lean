import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.EveryConfinedEigenspaceIsSimple
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.TheLadderBoundsTheNegativeSquaresOfEveryWindow
import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.WindowTestsCarryTheNegativeSpacesOfTheConfinedForm
import GaloisForLFunctions.HTGeometry.InertiaScalingSwap

/-!
# The confined Weil index counts distinct critical ratios

At a fixed positive ratio r, a compactly supported test family realizes k
negative directions exactly when k distinct positive ratios strictly below r
carry null states. The states at earlier ratios are mutually orthogonal for
the confinement pairing. Their negative span at r survives window recovery.
Conversely the ladder of a negative test family has distinct ratios by
simplicity, and its last ratio must already have been crossed.
-/

noncomputable section
open MeasureTheory Filter Set Topology Zeta23
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticOrientationGeometry CriticalArithmeticCorrelationTheory
  ArithmeticCastelnuovoSeveri HTGeometry CohomologyOfWindowsOfSpecZ _root_.RHTower

private theorem unit_null_at_same_ratio {s : ℝ} {F : ℝ → ℝ} (hF : IsConfinedNullVector s F) :
    ∃ G, IsConfinedNullVector s G ∧ (∫ u, G u ^ 2) = 1 := by
  let c := (Real.sqrt (∫ u, F u ^ 2))⁻¹
  have hpos : 0 < ∫ u, F u ^ 2 :=
    lt_of_le_of_ne (integral_nonneg fun u => sq_nonneg (F u)) hF.2.1.symm
  have hmass : (∫ u, (c * F u) ^ 2) = 1 := by
    simp only [mul_pow, integral_const_mul, c, inv_pow, Real.sq_sqrt hpos.le, inv_mul_cancel₀ hpos.ne']
  refine ⟨fun u => c * F u, ⟨hF.1.const_mul c, hmass.trans_ne one_ne_zero, ?_⟩, hmass⟩
  intro H hH
  have h := criticalHalfLineMixedEnergy_add_const_mul_left s hF.1 hF.1 hH (c-1)
  have he : (fun u => F u + (c-1)*F u) = fun u => c*F u := by funext u; ring
  rwa [he, hF.2.2 H hH, mul_zero, add_zero] at h

/-- A uniform negative margin for real combinations also bounds the complex Hermitian index from below. -/
theorem negIndex_of_negative_window_family {n : ℕ} {r δ : ℝ} (hδ : 0 < δ)
    {H : Fin n → ℝ → ℝ} (hH : ∀ i, IsHalfLineTest (H i))
    (hneg : ∀ t : Fin n → ℝ, criticalHalfLineFullEnergy r (fun u => ∑ i, t i * H i u) ≤
      -(δ * ∑ i, t i ^ 2)) : n ≤ hermNegIndex (confinedGram r H) := by
  classical
  have hp : IsPosDefOn (-(confinedGram r H)) ⊤ := by
    intro x _ hx
    rw [hermQuad_neg, neg_pos, hermQuad_eq_re_add_im (fun i j => confinedGram_im r H i j),
      hermQuad_confinedGram_ofReal r hH, hermQuad_confinedGram_ofReal r hH]
    have hr := hneg (fun i => (x i).re)
    have hi := hneg (fun i => (x i).im)
    have hpos : 0 < ∑ i, ((x i).re ^ 2 + (x i).im ^ 2) := by
      obtain ⟨i, hxi⟩ : ∃ i, x i ≠ 0 := by
        by_contra! h
        exact hx (funext h)
      apply Finset.sum_pos' (fun i _ => add_nonneg (sq_nonneg _) (sq_nonneg _))
      refine ⟨i, Finset.mem_univ _, ?_⟩
      have hsq := sq_pos_of_pos (norm_pos_iff.mpr hxi)
      rw [Complex.sq_norm, Complex.normSq_apply] at hsq
      simpa only [pow_two] using hsq
    rw [Finset.sum_add_distrib] at hpos
    linarith only [hr, hi, mul_pos hδ hpos]
  simpa [hermNegIndex] using finrank_le_posIndex hp

private theorem alias_gap_positive {s r : ℝ} (hs : 0 < s) (hsr : s < r) :
    0 < criticalAliasCoefficient s - criticalAliasCoefficient r := by
  rw [sub_pos, criticalAliasCoefficient_eq_div s, criticalAliasCoefficient_eq_div r]
  exact div_lt_div_of_pos_left (criticalAliasCoefficient_positive one_pos) hs hsr

/-- Distinct earlier null ratios give a real window family with a uniform negative margin. -/
theorem negative_window_family_of_distinct_critical_ratios {n : ℕ} {r : ℝ} (hr : 0 < r)
    {s : Fin (n+1) → ℝ} (hs : Function.Injective s) (hlo : ∀ i, 0 < s i)
    (hhi : ∀ i, s i < r) (hnull : ∀ i, ∃ F, IsConfinedNullVector (s i) F) :
    ∃ (H : Fin (n+1) → ℝ → ℝ) (δ : ℝ), (∀ i, IsHalfLineTest (H i)) ∧ 0 < δ ∧
      ∀ t : Fin (n+1) → ℝ, criticalHalfLineFullEnergy r (fun u => ∑ i, t i * H i u) ≤
        -(δ * ∑ i, t i ^ 2) := by
  classical
  choose Φ hΦ hunit using fun i => unit_null_at_same_ratio (hnull i).choose_spec
  let W := criticalHalfLineExponentialPair
  have horth (i j) (hij : i ≠ j) : W (Φ i) (Φ j) = 0 := by
    have h := (hΦ i).mixedEnergy_eq (s j) (hΦ j).1
    rw [criticalHalfLineMixedEnergy_comm, (hΦ j).2.2 _ (hΦ i).1] at h
    have hne : criticalAliasCoefficient (s j) ≠ criticalAliasCoefficient (s i) :=
      fun he => hij (hs (criticalAliasCoefficient_injective_positive (hlo j) (hlo i) he)).symm
    exact (mul_eq_zero.mp h.symm).resolve_left (sub_ne_zero.mpr hne)
  -- The least of the positive diagonal gaps survives simultaneous window approximation.
  let d := fun i => (criticalAliasCoefficient (s i) - criticalAliasCoefficient r) * W (Φ i) (Φ i)
  have hd (i) : 0 < d i := mul_pos (alias_gap_positive (hlo i) (hhi i))
    (exponentialPair_self_pos (hΦ i).1 (hΦ i).2.1)
  let δ := Finset.univ.inf' Finset.univ_nonempty d
  have hδ : 0 < δ := (Finset.lt_inf'_iff _).mpr fun i _ => hd i
  have hmin (i) : δ ≤ d i := Finset.inf'_le _ (Finset.mem_univ i)
  have hZ := (hΦ 0).1.const_mul 0
  have ho (i) : W (Φ i) (fun u => 0 * Φ 0 u) = 0 := by
    rw [show W = criticalHalfLineExponentialPair from rfl, exponentialPair_const_mul, zero_mul]
  have hneg (t : Fin (n+1) → ℝ) :
      criticalHalfLineFullEnergy r (fun u => ∑ i, t i * Φ i u) ≤ -(δ * ∑ i, t i ^ 2) := by
    have h := fullEnergy_add_sum_nullVectors r hΦ horth hZ ho t Finset.univ
    rw [criticalHalfLineFullEnergy_const_mul] at h
    simp only [zero_mul, zero_add, zero_pow two_ne_zero] at h
    rw [h, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hg := mul_le_mul_of_nonneg_right (hmin i) (sq_nonneg (t i))
    dsimp only [d, W] at hg
    linarith only [hg]
  obtain ⟨H, hw, hH⟩ := exists_window_family_of_negative hr (fun i => (hΦ i).1)
    (fun i => (hunit i).le) hδ hneg
  have htest (i) : IsHalfLineTest (H i) := by
    obtain ⟨A, -, hA⟩ := hw i
    exact ⟨hA.1, A, hA.2⟩
  exact ⟨H, δ/2, htest, half_pos hδ, hH⟩

/-- Compact window tests realize all the negative directions of any finite
set of distinct critical ratios below r. -/
theorem window_index_of_distinct_critical_ratios {n : ℕ} {r : ℝ} (hr : 0 < r)
    {s : Fin (n+1) → ℝ} (hs : Function.Injective s) (hlo : ∀ i, 0 < s i)
    (hhi : ∀ i, s i < r) (hnull : ∀ i, ∃ F, IsConfinedNullVector (s i) F) :
    ∃ (S : Finset ℝ) (H : S → ℝ → ℝ), (∀ i, IsHalfLineTest (H i)) ∧
      n + 1 ≤ hermNegIndex (confinedGram r H) := by
  classical
  obtain ⟨H, δ, htest, hδ, hH⟩ := negative_window_family_of_distinct_critical_ratios hr hs hlo hhi hnull
  let S := Finset.univ.image s
  have hcard : S.card = n+1 := by simp [S, Finset.card_image_of_injective _ hs]
  let e : S ≃ Fin (n+1) := S.equivFin.trans (finCongr hcard)
  refine ⟨S, fun i => H (e i), fun i => htest _, ?_⟩
  change n+1 ≤ hermNegIndex ((confinedGram r H).submatrix e e)
  rw [negIndex_submatrix_equiv]
  exact negIndex_of_negative_window_family hδ htest hH

private theorem ladder_of_index_ge {n : ℕ} {r : ℝ} (hr : 0 < r)
    {S : Finset ℝ} {H : S → ℝ → ℝ} (hH : ∀ i, IsHalfLineTest (H i))
    (hneg : n+1 ≤ hermNegIndex (confinedGram r H)) :
    ∃ (s : Fin (n+1) → ℝ) (Φ : Fin (n+1) → ℝ → ℝ), IsCriticalLadder n s Φ := by
  have hcount := (confinedIndex_law (n+1)).mp ⟨r, hr, S, H, hH, hneg⟩
  rcases riemannHypothesis_or_criticalLadder with hRH | ⟨_, _, _, _, _, hl⟩
  · rw [riemannHypothesis_iff_no_rightZero.mp hRH, Set.encard_empty] at hcount
    exact False.elim (not_le_of_gt (by exact_mod_cast Nat.succ_pos n :
      (0 : ℕ∞) < ((n+1 : ℕ) : ℕ∞)) hcount)
  · obtain ⟨s, Φ, hL, -, -⟩ := hl n hcount
    exact ⟨s, Φ, hL⟩

/-- At each positive ratio, the number of distinct earlier null ratios counts
all realizable negative squares, independently of the full zero divisor. -/
theorem confined_index_at_ratio_iff_distinct_critical_ratios (n : ℕ) {r : ℝ} (hr : 0 < r) :
    (∃ (S : Finset ℝ) (H : S → ℝ → ℝ), (∀ i, IsHalfLineTest (H i)) ∧
      n+1 ≤ hermNegIndex (confinedGram r H)) ↔
    ∃ s : Fin (n+1) → ℝ, StrictMono s ∧ ∀ i,
      0 < s i ∧ s i < r ∧ ∃ F, IsConfinedNullVector (s i) F := by
  constructor
  · rintro ⟨S, H, hH, hneg⟩
    obtain ⟨s, Φ, hL⟩ := ladder_of_index_ge hr hH hneg
    have hlast : s (Fin.last n) < r := by
      by_contra! he
      have hupper := hL.hermNegIndex_confinedGram_le_of_le (Fin.last n) hr he hH
      change hermNegIndex (confinedGram r H) ≤ n at hupper
      omega
    exact ⟨s, hL.strictMono_ratio, fun i =>
      ⟨hL.pos i, (hL.mono (Fin.le_last i)).trans_lt hlast, Φ i, hL.null i⟩⟩
  · rintro ⟨s, hs, hc⟩
    exact window_index_of_distinct_critical_ratios hr hs.injective
      (fun i => (hc i).1) (fun i => (hc i).2.1) (fun i => (hc i).2.2)

/-- Negative indices attained by finite families of smooth half-line tests at r. -/
def windowIndicesAt (r : ℝ) : Set ℕ :=
  {k | ∃ (S : Finset ℝ) (H : S → ℝ → ℝ), (∀ i, IsHalfLineTest (H i)) ∧
    k = hermNegIndex (confinedGram r H)}

/-- Every positive index reached or exceeded somewhere is the exact maximum
on a nonempty interval of ratios, simultaneously for all window tests. -/
theorem exists_interval_of_exact_confined_index {n : ℕ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    {S₀ : Finset ℝ} {H₀ : S₀ → ℝ → ℝ} (hH₀ : ∀ i, IsHalfLineTest (H₀ i))
    (hn : n+1 ≤ hermNegIndex (confinedGram r₀ H₀)) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∀ r ∈ Ioc a b, IsGreatest (windowIndicesAt r) (n+1) := by
  classical
  by_cases hnext : ∃ (t : ℝ) (_ : 0 < t) (S : Finset ℝ) (H : S → ℝ → ℝ),
      (∀ i, IsHalfLineTest (H i)) ∧ n+2 ≤ hermNegIndex (confinedGram t H)
  · obtain ⟨t, ht, S, H, hH, hbig⟩ := hnext
    obtain ⟨s, Φ, hL⟩ := ladder_of_index_ge (n := n+1) ht hH hbig
    let i := (Fin.last n).castSucc
    let j := Fin.last (n+1)
    have hij : i < j := Fin.castSucc_lt_last _
    refine ⟨s i, s j, hL.pos i, hL.strictMono_ratio hij, ?_⟩
    intro r hr
    have hrpos := (hL.pos i).trans hr.1
    have cap {S : Finset ℝ} {H : S → ℝ → ℝ} (hH : ∀ k, IsHalfLineTest (H k)) :
        hermNegIndex (confinedGram r H) ≤ n+1 :=
      hL.hermNegIndex_confinedGram_le_of_le j hrpos hr.2 hH
    have hseen (k : Fin (n+1)) : s k.castSucc < r :=
      (hL.mono (Fin.mk_le_mk.mpr (Nat.le_of_lt_succ k.2))).trans_lt hr.1
    obtain ⟨S', H', hH', hk⟩ := window_index_of_distinct_critical_ratios hrpos
      (s := fun k : Fin (n+1) => s k.castSucc)
      (hL.strictMono_ratio.injective.comp (Fin.castSucc_injective _))
      (fun k => hL.pos k.castSucc) hseen (fun k => ⟨Φ k.castSucc, hL.null k.castSucc⟩)
    refine ⟨⟨S', H', hH', le_antisymm hk (cap hH')⟩, ?_⟩
    rintro _ ⟨S', H', hH', rfl⟩
    exact cap hH'
  · refine ⟨r₀, r₀+1, hr₀, by linarith, ?_⟩
    intro r hr
    have hpos := hr₀.trans hr.1
    have cap {S : Finset ℝ} {H : S → ℝ → ℝ} (hH : ∀ k, IsHalfLineTest (H k)) :
        hermNegIndex (confinedGram r H) ≤ n+1 :=
      Nat.lt_succ_iff.mp (lt_of_not_ge fun h => hnext ⟨r, hpos, S, H, hH, h⟩)
    have hlow := hn.trans (hermNegIndex_confinedGram_mono hr₀ hr.1.le
      (fun i => (hH₀ i).1.continuous) (fun i => (hH₀ i).hasCompactSupport))
    refine ⟨⟨S₀, H₀, hH₀, le_antisymm hlow (cap hH₀)⟩, ?_⟩
    rintro _ ⟨S', H', hH', rfl⟩
    exact cap hH'

/-- Off RH the maximum window index equals two throughout an interval of
positive length, even when infinitely many zeros lie off the line. -/
theorem riemannHypothesis_or_interval_of_confined_index_two :
    RiemannHypothesis ∨ ∃ a b : ℝ, 0 < a ∧ a < b ∧
      ∀ r ∈ Ioc a b, IsGreatest (windowIndicesAt r) 2 := by
  by_cases h : RiemannHypothesis
  · exact Or.inl h
  · obtain ⟨r, hr, S, H, hH, h2⟩ := exists_two_le_hermNegIndex_confinedGram_of_not_RH h
    exact Or.inr (exists_interval_of_exact_confined_index (n := 1) hr hH h2)

#print axioms window_index_of_distinct_critical_ratios
#print axioms confined_index_at_ratio_iff_distinct_critical_ratios
#print axioms exists_interval_of_exact_confined_index
#print axioms riemannHypothesis_or_interval_of_confined_index_two

end GaloisForLFunctions.ExclusionOfTheCriticalState
