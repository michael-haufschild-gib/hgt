import GaloisForLFunctions.RHTower.ChronologicalOffLineZeroFloor
import GaloisForLFunctions.RHTower.HardyLittlewoodExponentLaw

/-!
# Unless RH holds, sharp Möbius chronological errors escape to infinity

Let `r_N(t) = e^{-t} + Σ_{k ≤ N} μ(k) (1/(kt) - 1/(e^{kt} - 1))` be the chronological heat error of
the sharp Möbius row.

**Theorem** (`riemannHypothesis_of_frequently_sharpMobius_le`).  If `‖r_N‖_{L²(0,∞)} ≤ B` for
infinitely many `N`, then RH holds.  Equivalently, if RH fails then `‖r_N‖_{L²(0,∞)} → ∞`.

**Proof.**  For fixed `t > 0`, `r_N(t) → 0`: the harmonic charge `Σ_{k ≤ N} μ(k)/k` tends to `0`
(prime number theorem) and `Σ_k μ(k)/(e^{kt} - 1) = e^{-t}` (Möbius–Lambert).  On `[δ, ∞)` the
errors are bounded uniformly in `N`.  Hence a bounded subsequence tends to `0` weakly in
`L²(0,∞)`: the middle range is dominated convergence, the two ends cost at most `B` times the
`L²` mass of the test function there.  The Banach–Saks selection of an almost orthogonal
subfamily makes Cesàro means of the errors tend to `0` in norm.  A Cesàro mean of sharp Möbius
rows is a row `μ(k) w_k` with `0 ≤ w_k ≤ 1`, so bounded rows reach arbitrarily small error, and
`riemannHypothesis_of_forall_exists_chronologicalL2Norm_lt` gives RH.

Thus the chronological route needs no decay at all: boundedness along a subsequence of the most
naive rows is already equivalent in strength to RH, while an off-line zero forces escape.
-/

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- The sharp Möbius row. -/
def sharpMobiusRow (k : ℕ) : ℝ := (ArithmeticFunction.moebius k : ℝ)

/-- The sharp Möbius chronological error at cutoff `N`. -/
def sharpMobiusError (N : ℕ) (t : ℝ) : ℝ := chronologicalHeatError sharpMobiusRow N t

private theorem sum_Ioc_eq_sum_range_succ_of_zero {f : ℕ → ℝ} (hf : f 0 = 0) (N : ℕ) :
    ∑ k ∈ Finset.Ioc 0 N, f k = ∑ k ∈ Finset.range (N + 1), f k := by
  induction N with
  | zero => simp [hf]
  | succ N ih => rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), ih, Finset.sum_range_succ _ (N + 1)]

theorem tendsto_chronologicalHarmonicCharge_sharpMobius :
    Tendsto (fun N => chronologicalHarmonicCharge sharpMobiusRow N) atTop (𝓝 0) := by
  refine tendsto_sum_range_succ_moebius_div.congr fun N => ?_
  unfold chronologicalHarmonicCharge sharpMobiusRow
  rw [sum_Ioc_eq_sum_range_succ_of_zero (f := fun k => (ArithmeticFunction.moebius k : ℝ) / k)
    (by simp)]

theorem tendsto_chronologicalBoseSum_sharpMobius {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N => chronologicalBoseSum sharpMobiusRow N t) atTop (𝓝 (Real.exp (-t))) := by
  have h := (hasSum_moebius_div_exp_sub_one ht).tendsto_sum_nat
  have h' := h.comp (tendsto_add_atTop_nat 1)
  refine h'.congr fun N => ?_
  unfold chronologicalBoseSum sharpMobiusRow
  simp only [Function.comp_apply]
  rw [sum_Ioc_eq_sum_range_succ_of_zero
    (f := fun k => (ArithmeticFunction.moebius k : ℝ) / (Real.exp (k * t) - 1)) (by simp)]

/-- The sharp Möbius errors tend to `0` pointwise on `(0,∞)`. -/
theorem tendsto_sharpMobiusError {t : ℝ} (ht : 0 < t) :
    Tendsto (fun N => sharpMobiusError N t) atTop (𝓝 0) := by
  have hc := tendsto_chronologicalHarmonicCharge_sharpMobius
  have hb := tendsto_chronologicalBoseSum_sharpMobius ht
  have h := ((hc.div_const t).add (tendsto_const_nhds (x := Real.exp (-t)))).sub hb
  rw [zero_div, zero_add, sub_self] at h
  refine h.congr fun N => ?_
  unfold sharpMobiusError
  rw [chronologicalHeatError_charge_decomposition _ N ht]

/-- On `[δ, ∞)` the sharp Möbius errors are bounded uniformly in the cutoff. -/
theorem exists_abs_sharpMobiusError_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ N : ℕ, ∀ t : ℝ, δ ≤ t → |sharpMobiusError N t| ≤ M := by
  obtain ⟨Cm, hCm⟩ : ∃ Cm, ∀ N, |chronologicalHarmonicCharge sharpMobiusRow N| ≤ Cm := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto _
      tendsto_chronologicalHarmonicCharge_sharpMobius).subset_closedBall 0
    exact ⟨R, fun N => by
      have := hR ⟨N, rfl⟩
      simpa [Metric.mem_closedBall, Real.dist_eq] using this⟩
  set S := ∑' k : ℕ, 1 / (Real.exp (k * δ) - 1) with hS
  have hsum := summable_one_div_exp_mul_sub_one hδ
  refine ⟨|Cm| / δ + 1 + S, fun N t ht => ?_⟩
  have ht0 : 0 < t := hδ.trans_le ht
  unfold sharpMobiusError
  rw [chronologicalHeatError_charge_decomposition _ N ht0]
  have hcharge : |chronologicalHarmonicCharge sharpMobiusRow N / t| ≤ |Cm| / δ := by
    rw [abs_div, abs_of_pos ht0]
    have h1 : |chronologicalHarmonicCharge sharpMobiusRow N| ≤ |Cm| := (hCm N).trans (le_abs_self _)
    calc |chronologicalHarmonicCharge sharpMobiusRow N| / t ≤ |Cm| / t :=
          div_le_div_of_nonneg_right h1 ht0.le
      _ ≤ |Cm| / δ := div_le_div_of_nonneg_left (abs_nonneg _) hδ ht
  have hexp : |Real.exp (-t)| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hbose : |chronologicalBoseSum sharpMobiusRow N t| ≤ S := by
    unfold chronologicalBoseSum
    calc |∑ k ∈ Finset.Ioc 0 N, sharpMobiusRow k / (Real.exp (k * t) - 1)|
        ≤ ∑ k ∈ Finset.Ioc 0 N, |sharpMobiusRow k / (Real.exp (k * t) - 1)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ioc 0 N, 1 / (Real.exp (k * δ) - 1) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
          have hkδ : 0 < (k : ℝ) * δ := by positivity
          have hkt : (k : ℝ) * δ ≤ k * t := mul_le_mul_of_nonneg_left ht (by linarith)
          have hd1 : 0 < Real.exp (k * δ) - 1 := by
            have := Real.one_lt_exp_iff.mpr hkδ; linarith
          have hd2 : Real.exp (k * δ) - 1 ≤ Real.exp (k * t) - 1 := by
            have := Real.exp_le_exp.mpr hkt; linarith
          have hmu : |sharpMobiusRow k| ≤ 1 := by
            unfold sharpMobiusRow
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one
          rw [abs_div, abs_of_pos (hd1.trans_le hd2)]
          calc |sharpMobiusRow k| / (Real.exp (k * t) - 1) ≤ 1 / (Real.exp (k * t) - 1) :=
                div_le_div_of_nonneg_right hmu (hd1.trans_le hd2).le
            _ ≤ 1 / (Real.exp (k * δ) - 1) := one_div_le_one_div_of_le hd1 hd2
      _ ≤ S := hsum.sum_le_tsum _ (fun k _ => one_div_exp_mul_sub_one_nonneg k hδ)
  calc |chronologicalHarmonicCharge sharpMobiusRow N / t + Real.exp (-t) -
        chronologicalBoseSum sharpMobiusRow N t|
      ≤ |chronologicalHarmonicCharge sharpMobiusRow N / t| + |Real.exp (-t)| +
          |chronologicalBoseSum sharpMobiusRow N t| := by
        have h1 := abs_sub (chronologicalHarmonicCharge sharpMobiusRow N / t + Real.exp (-t))
          (chronologicalBoseSum sharpMobiusRow N t)
        have h2 := abs_add_le (chronologicalHarmonicCharge sharpMobiusRow N / t) (Real.exp (-t))
        linarith
    _ ≤ |Cm| / δ + 1 + S := by linarith

/-- Cauchy–Schwarz for real square-integrable functions. -/
theorem abs_integral_mul_le_sqrt_mul_sqrt {μ : Measure ℝ} {f g : ℝ → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) :
    |∫ t, f t * g t ∂μ| ≤ Real.sqrt (∫ t, f t ^ 2 ∂μ) * Real.sqrt (∫ t, g t ^ 2 ∂μ) := by
  have hcs := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf) (by simpa using hg)
  have hA : (∫ t, ‖f t‖ ^ (2 : ℝ) ∂μ) = ∫ t, f t ^ 2 ∂μ := by
    congr 1; ext t; rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  have hB : (∫ t, ‖g t‖ ^ (2 : ℝ) ∂μ) = ∫ t, g t ^ 2 ∂μ := by
    congr 1; ext t; rw [Real.norm_eq_abs, Real.rpow_two, sq_abs]
  rw [hA, hB] at hcs
  calc |∫ t, f t * g t ∂μ| ≤ ∫ t, |f t * g t| ∂μ := abs_integral_le_integral_abs
    _ = ∫ t, ‖f t‖ * ‖g t‖ ∂μ := by congr 1; ext t; rw [abs_mul]; rfl
    _ ≤ _ := hcs
    _ = _ := by rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- **Weak convergence.**  Along any cutoff sequence on which the sharp Möbius errors stay
bounded in `L²(0,∞)`, they tend to `0` weakly. -/
theorem tendsto_integral_mul_sharpMobiusError {h : ℝ → ℝ}
    (hh : MemLp h 2 chronologicalPositiveVolume) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop)
    {B : ℝ} (hB : ∀ j, chronologicalL2Norm (sharpMobiusError (φ j)) ≤ B) :
    Tendsto (fun j => ∫ t in Ioi (0 : ℝ), h t * sharpMobiusError (φ j) t) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hB0 : 0 ≤ B := (chronologicalL2Norm_nonneg _).trans (hB 0)
  set O : ℕ → Set ℝ := fun n => Ioc 0 (1 / ((n : ℝ) + 1)) ∪ Ioi ((n : ℝ) + 1) with hOdef
  have hOanti : Antitone O := by
    intro m n hmn x hx
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hmn 1
    rcases hx with hx | hx
    · left
      exact ⟨hx.1, hx.2.trans (one_div_le_one_div_of_le (by positivity) hmn')⟩
    · right
      exact lt_of_le_of_lt hmn' hx
  have hOinter : (⋂ n, O n) = ∅ := by
    ext x
    simp only [mem_iInter, mem_empty_iff_false, iff_false, not_forall]
    rcases le_or_gt x 0 with hx | hx
    · refine ⟨0, fun h => ?_⟩
      rcases h with h | h
      · exact absurd h.1 (not_lt.mpr hx)
      · simp at h; linarith
    · obtain ⟨n, hn⟩ := exists_nat_gt (max x (1 / x))
      refine ⟨n, fun h => ?_⟩
      rcases h with h | h
      · have h1 : x ≤ 1 / ((n : ℝ) + 1) := h.2
        have h2 : 1 / x < (n : ℝ) + 1 := by linarith [le_max_right x (1 / x)]
        have h3 : 1 / ((n : ℝ) + 1) < x := by
          rw [div_lt_iff₀ (by positivity)]
          rw [div_lt_iff₀ hx] at h2
          linarith
        linarith
      · have : x < (n : ℝ) + 1 := by linarith [le_max_left x (1 / x)]
        exact absurd h (not_lt.mpr this.le)
  have hOsub : ∀ n, O n ⊆ Ioi (0 : ℝ) := by
    intro n x hx
    rcases hx with hx | hx
    · exact hx.1
    · exact lt_trans (by positivity : (0 : ℝ) < (n : ℝ) + 1) hx
  have hOm : ∀ n, MeasurableSet (O n) := fun n => measurableSet_Ioc.union measurableSet_Ioi
  have hh2 : IntegrableOn (fun t => h t ^ 2) (Ioi 0) := hh.integrable_sq
  have hlim := tendsto_setIntegral_of_antitone (μ := volume) (f := fun t => h t ^ 2) hOm hOanti
    ⟨0, hh2.mono_set (hOsub 0)⟩
  rw [hOinter, Measure.restrict_empty, integral_zero_measure] at hlim
  set η : ℝ := ε / (2 * (B + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < η ^ 2))).exists
  set δ : ℝ := 1 / ((n : ℝ) + 1) with hδ
  set T : ℝ := (n : ℝ) + 1 with hT
  have hδ0 : 0 < δ := by positivity
  have hδT : δ ≤ T := by
    rw [hδ, hT, div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  obtain ⟨M, hM⟩ := exists_abs_sharpMobiusError_le hδ0
  -- the middle range by dominated convergence
  have hhfin : IntegrableOn h (Ioc δ T) := by
    have hm : MemLp h 2 (volume.restrict (Ioc δ T)) :=
      hh.mono_measure (Measure.restrict_mono (fun x hx => hδ0.trans hx.1) le_rfl)
    exact hm.integrable (by norm_num)
  have hmid : Tendsto (fun j => ∫ t in Ioc δ T, h t * sharpMobiusError (φ j) t) atTop (𝓝 0) := by
    have hconv := tendsto_integral_of_dominated_convergence (μ := volume.restrict (Ioc δ T))
      (F := fun j t => h t * sharpMobiusError (φ j) t) (f := fun _ => (0 : ℝ))
      (fun t => |M| * ‖h t‖)
      (fun j => ((hh.1.mono_measure (Measure.restrict_mono
        (fun x hx => hδ0.trans hx.1) le_rfl)).mul
        ((chronologicalHeatError_memLp _ _).1.mono_measure (Measure.restrict_mono
        (fun x hx => hδ0.trans hx.1) le_rfl))))
      (hhfin.norm.const_mul _)
      (fun j => by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right ((Real.norm_eq_abs _).le.trans
          ((hM (φ j) t ht.1.le).trans (le_abs_self M))) (norm_nonneg _))
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        have := (tendsto_sharpMobiusError (hδ0.trans ht.1)).comp hφ
        simpa using (tendsto_const_nhds (x := h t)).mul this)
    simpa using hconv
  obtain ⟨J, hJ⟩ := (Metric.tendsto_atTop.mp hmid) (ε / 2) (by positivity)
  refine ⟨J, fun j hj => ?_⟩
  set r := sharpMobiusError (φ j) with hr
  have hrm : MemLp r 2 chronologicalPositiveVolume := chronologicalHeatError_memLp _ _
  have hint : IntegrableOn (fun t => h t * r t) (Ioi 0) := hh.integrable_mul hrm
  -- split `(0,∞) = O n ∪ (δ, T]`
  have hsplit : Ioi (0 : ℝ) = O n ∪ Ioc δ T := by
    ext x
    simp only [hOdef, mem_Ioi, mem_union, mem_Ioc]
    constructor
    · intro hx
      by_cases h1 : x ≤ δ
      · exact Or.inl (Or.inl ⟨hx, h1⟩)
      · by_cases h2 : x ≤ T
        · exact Or.inr ⟨lt_of_not_ge h1, h2⟩
        · exact Or.inl (Or.inr (lt_of_not_ge h2))
    · rintro ((⟨h1, _⟩ | h1) | ⟨h1, _⟩)
      · exact h1
      · exact lt_trans (by positivity) h1
      · exact hδ0.trans h1
  have hdisj : Disjoint (O n) (Ioc δ T) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    rcases hx with hx | hx
    · exact absurd hx.2 (not_le.mpr hx'.1)
    · exact absurd hx (not_lt.mpr hx'.2)
  have hsum : (∫ t in Ioi (0 : ℝ), h t * r t) =
      (∫ t in O n, h t * r t) + ∫ t in Ioc δ T, h t * r t := by
    rw [hsplit, setIntegral_union hdisj measurableSet_Ioc
      (hint.mono_set (hOsub n)) (hint.mono_set (fun x hx => hδ0.trans hx.1))]
  -- the outer part is small by Cauchy–Schwarz
  have hhO : MemLp h 2 (volume.restrict (O n)) :=
    hh.mono_measure (Measure.restrict_mono (hOsub n) le_rfl)
  have hrO : MemLp r 2 (volume.restrict (O n)) :=
    hrm.mono_measure (Measure.restrict_mono (hOsub n) le_rfl)
  have hcs := abs_integral_mul_le_sqrt_mul_sqrt hhO hrO
  have hhOsmall : Real.sqrt (∫ t in O n, h t ^ 2) ≤ η := by
    rw [Real.sqrt_le_left hη0.le]
    exact hn.le
  have hrOsmall : Real.sqrt (∫ t in O n, r t ^ 2) ≤ B := by
    have hle : (∫ t in O n, r t ^ 2) ≤ ∫ t in Ioi (0 : ℝ), r t ^ 2 :=
      setIntegral_mono_set hrm.integrable_sq (Eventually.of_forall fun t => sq_nonneg _)
        (Eventually.of_forall (hOsub n))
    calc Real.sqrt (∫ t in O n, r t ^ 2) ≤ Real.sqrt (∫ t in Ioi (0 : ℝ), r t ^ 2) :=
          Real.sqrt_le_sqrt hle
      _ = chronologicalL2Norm r := (chronologicalL2Norm_eq_sqrt hrm.1).symm
      _ ≤ B := hB j
  have houter : |∫ t in O n, h t * r t| ≤ η * B :=
    hcs.trans (mul_le_mul hhOsmall hrOsmall (Real.sqrt_nonneg _) hη0.le)
  have hηB : η * B < ε / 2 := by
    rw [hη]
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hmidj := hJ j hj
  rw [Real.dist_eq, sub_zero] at hmidj ⊢
  rw [hsum]
  calc |(∫ t in O n, h t * r t) + ∫ t in Ioc δ T, h t * r t|
      ≤ |∫ t in O n, h t * r t| + |∫ t in Ioc δ T, h t * r t| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (houter.trans hηB.le) hmidj
    _ = ε := by ring

/-- **Banach–Saks selection.**  If `a i j → 0` as `j → ∞` for every `i`, there are `L` indices
whose pairwise values (earlier index first) are at most `c`. -/
theorem exists_finset_pairwise_small (a : ℕ → ℕ → ℝ) (ha : ∀ i, Tendsto (a i) atTop (𝓝 0))
    {c : ℝ} (hc : 0 < c) (L : ℕ) :
    ∃ S : Finset ℕ, S.card = L ∧ ∀ i ∈ S, ∀ j ∈ S, i < j → |a i j| ≤ c := by
  induction L with
  | zero => exact ⟨∅, rfl, by simp⟩
  | succ L ih =>
    obtain ⟨S, hcard, hS⟩ := ih
    have hev : ∀ᶠ j in atTop, (∀ i ∈ S, |a i j| ≤ c) ∧ S.sup id < j := by
      refine (Filter.eventually_all_finset S |>.mpr fun i _ => ?_).and (eventually_gt_atTop _)
      have := (ha i).eventually (Metric.closedBall_mem_nhds (0 : ℝ) hc)
      filter_upwards [this] with j hj
      simpa [Metric.mem_closedBall, Real.dist_eq] using hj
    obtain ⟨j, hj, hjS⟩ := hev.exists
    have hjnot : j ∉ S := fun hmem => by
      have := Finset.le_sup (f := id) hmem
      simp at this; omega
    refine ⟨insert j S, by rw [Finset.card_insert_of_notMem hjnot, hcard], ?_⟩
    intro i hi k hk hik
    rcases Finset.mem_insert.mp hi with hi' | hi'
    · rcases Finset.mem_insert.mp hk with hk' | hk'
      · rw [hi', hk'] at hik; exact absurd hik (lt_irrefl _)
      · have := Finset.le_sup (f := id) hk'
        simp only [id_eq] at this; rw [hi'] at hik; omega
    · rcases Finset.mem_insert.mp hk with hk' | hk'
      · rw [hk']; exact hj i hi'
      · exact hS i hi' k hk' hik

/-- Double sums over an almost orthogonal family: `Σ_{i,j ∈ S} a i j ≤ |S| B + |S|² c`. -/
theorem sum_sum_le_of_pairwise_small {a : ℕ → ℕ → ℝ} (hsymm : ∀ i j, a i j = a j i)
    {B c : ℝ} (hc : 0 ≤ c) (hdiag : ∀ i, a i i ≤ B) {S : Finset ℕ}
    (hS : ∀ i ∈ S, ∀ j ∈ S, i < j → |a i j| ≤ c) :
    ∑ i ∈ S, ∑ j ∈ S, a i j ≤ S.card * B + S.card ^ 2 * c := by
  have hterm : ∀ i ∈ S, ∀ j ∈ S, a i j ≤ (if i = j then B else 0) + c := by
    intro i hi j hj
    rcases lt_trichotomy i j with hij | rfl | hij
    · rw [if_neg hij.ne]; have := hS i hi j hj hij; linarith [le_abs_self (a i j)]
    · rw [if_pos rfl]; linarith [hdiag i]
    · rw [if_neg hij.ne', hsymm]; have := hS j hj i hi hij; linarith [le_abs_self (a j i)]
  calc ∑ i ∈ S, ∑ j ∈ S, a i j ≤ ∑ i ∈ S, ∑ j ∈ S, ((if i = j then B else 0) + c) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
    _ = S.card * B + S.card ^ 2 * c := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const, nsmul_eq_mul]
        rw [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
        ring

private theorem sum_Ioc_ite_le_real {M N : ℕ} (h : N ≤ M) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.Ioc 0 M, (if k ≤ N then f k else 0) = ∑ k ∈ Finset.Ioc 0 N, f k := by
  rw [← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  omega

/-- A Cesàro mean of sharp Möbius errors is the error of a row bounded by `1`. -/
theorem chronologicalHeatError_cesaro_sharpMobius {φ : ℕ → ℕ} {S : Finset ℕ}
    (hS : S.Nonempty) {t : ℝ} :
    chronologicalHeatError
        (fun k => (S.card : ℝ)⁻¹ * ∑ j ∈ S, if k ≤ φ j then sharpMobiusRow k else 0)
        (S.sup φ) t =
      (S.card : ℝ)⁻¹ * ∑ j ∈ S, sharpMobiusError (φ j) t := by
  have hcard : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hinner : ∀ j ∈ S, ∑ k ∈ Finset.Ioc 0 (φ j), sharpMobiusRow k * fusionBoseDefect (k * t) =
      ∑ k ∈ Finset.Ioc 0 (S.sup φ),
        (if k ≤ φ j then sharpMobiusRow k else 0) * fusionBoseDefect (k * t) := by
    intro j hj
    rw [← sum_Ioc_ite_le_real (Finset.le_sup hj)]
    exact Finset.sum_congr rfl fun k _ => by split_ifs <;> simp
  unfold sharpMobiusError chronologicalHeatError
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_add, ← mul_assoc,
    inv_mul_cancel₀ hcard, one_mul]
  congr 1
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, Finset.sum_mul]

/-- **Escape dichotomy.**  If the sharp Möbius chronological errors are bounded in
`L²(0,∞)` along infinitely many cutoffs, RH holds. -/
theorem riemannHypothesis_of_frequently_sharpMobius_le {B : ℝ}
    (hfreq : ∃ᶠ N in atTop, chronologicalL2Norm (sharpMobiusError N) ≤ B) :
    RiemannHypothesis := by
  obtain ⟨φ, hφmono, hφB⟩ := extraction_of_frequently_atTop hfreq
  have hφ : Tendsto φ atTop atTop := hφmono.tendsto_atTop
  have hB0 : 0 ≤ B := (chronologicalL2Norm_nonneg _).trans (hφB 0)
  set R : ℕ → ℝ → ℝ := fun j => sharpMobiusError (φ j) with hRdef
  have hRm : ∀ j, MemLp (R j) 2 chronologicalPositiveVolume :=
    fun j => chronologicalHeatError_memLp _ _
  set a : ℕ → ℕ → ℝ := fun i j => ∫ t in Ioi (0 : ℝ), R i t * R j t with hadef
  have ha : ∀ i, Tendsto (a i) atTop (𝓝 0) :=
    fun i => tendsto_integral_mul_sharpMobiusError (hRm i) hφ hφB
  have hsymm : ∀ i j, a i j = a j i := fun i j => by
    simp only [hadef]; congr 1; ext t; ring
  have hdiag : ∀ i, a i i ≤ B ^ 2 := by
    intro i
    have h := hφB i
    rw [chronologicalL2Norm_eq_sqrt (hRm i).1] at h
    have h0 : 0 ≤ ∫ t in Ioi (0 : ℝ), R i t ^ 2 :=
      setIntegral_nonneg measurableSet_Ioi fun t _ => sq_nonneg _
    have := (Real.sqrt_le_left hB0).mp h
    simpa [hadef, sq] using this
  apply riemannHypothesis_of_forall_exists_chronologicalL2Norm_lt 1 zero_le_one
  intro ε hε
  obtain ⟨L, hL⟩ := exists_nat_gt ((B ^ 2 + 1) / ε ^ 2)
  have hLpos : (0 : ℝ) < L := lt_of_le_of_lt (by positivity) hL
  have hL1 : 1 ≤ L := by exact_mod_cast hLpos
  obtain ⟨S, hcard, hS⟩ := exists_finset_pairwise_small a ha (c := 1 / L) (by positivity) L
  have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨S.sup φ, fun k => (S.card : ℝ)⁻¹ * ∑ j ∈ S, if k ≤ φ j then sharpMobiusRow k else 0,
    fun k _ => ?_, ?_⟩
  · rw [abs_mul, abs_inv, Nat.abs_cast]
    have hsum : |∑ j ∈ S, if k ≤ φ j then sharpMobiusRow k else 0| ≤ S.card := by
      calc |∑ j ∈ S, if k ≤ φ j then sharpMobiusRow k else 0|
          ≤ ∑ j ∈ S, |if k ≤ φ j then sharpMobiusRow k else 0| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ S, (1 : ℝ) := by
            refine Finset.sum_le_sum fun j _ => ?_
            split_ifs
            · unfold sharpMobiusRow; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
            · simp
        _ = S.card := by simp
    have hc0 : (0 : ℝ) < S.card := by exact_mod_cast hSne.card_pos
    calc (S.card : ℝ)⁻¹ * |∑ j ∈ S, if k ≤ φ j then sharpMobiusRow k else 0|
        ≤ (S.card : ℝ)⁻¹ * S.card := mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 1 := inv_mul_cancel₀ hc0.ne'
  · set A : ℝ → ℝ := fun t => (S.card : ℝ)⁻¹ * ∑ j ∈ S, R j t with hAdef
    have hAm : MemLp A 2 chronologicalPositiveVolume :=
      (memLp_finsetSum S fun j _ => hRm j).const_mul _
    have heq : chronologicalL2Norm (chronologicalHeatError
        (fun k => (S.card : ℝ)⁻¹ * ∑ j ∈ S, if k ≤ φ j then sharpMobiusRow k else 0)
        (S.sup φ)) = chronologicalL2Norm A := by
      rw [chronologicalL2Norm_eq_sqrt (chronologicalHeatError_memLp _ _).1,
        chronologicalL2Norm_eq_sqrt hAm.1]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
      simp only [hAdef, hRdef]
      rw [chronologicalHeatError_cesaro_sharpMobius hSne]
    rw [heq, chronologicalL2Norm_eq_sqrt hAm.1]
    have hint : ∀ i j, Integrable (fun t => R i t * R j t) chronologicalPositiveVolume :=
      fun i j => (hRm i).integrable_mul (hRm j)
    have hsq : (∫ t in Ioi (0 : ℝ), A t ^ 2) =
        ((S.card : ℝ)⁻¹) ^ 2 * ∑ i ∈ S, ∑ j ∈ S, a i j := by
      have hexp : ∀ t, A t ^ 2 = ((S.card : ℝ)⁻¹) ^ 2 * ∑ i ∈ S, ∑ j ∈ S, R i t * R j t := by
        intro t
        simp only [hAdef]
        rw [mul_pow, sq (∑ j ∈ S, R j t), Finset.sum_mul_sum]
      simp_rw [hexp]
      rw [integral_const_mul]
      congr 1
      rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => hint i j]
    have hdouble := sum_sum_le_of_pairwise_small hsymm (by positivity) hdiag hS
    rw [hcard] at hdouble
    have hbound : (∫ t in Ioi (0 : ℝ), A t ^ 2) ≤ (B ^ 2 + 1) / L := by
      rw [hsq, hcard]
      have hL0 : (L : ℝ) ≠ 0 := hLpos.ne'
      calc ((L : ℝ)⁻¹) ^ 2 * ∑ i ∈ S, ∑ j ∈ S, a i j
          ≤ ((L : ℝ)⁻¹) ^ 2 * (L * B ^ 2 + L ^ 2 * (1 / L)) :=
            mul_le_mul_of_nonneg_left hdouble (by positivity)
        _ = (B ^ 2 + 1) / L := by field_simp
    have hsmall : (B ^ 2 + 1) / L < ε ^ 2 := by
      rw [div_lt_iff₀ hLpos]
      rw [div_lt_iff₀ (by positivity)] at hL
      linarith
    rw [Real.sqrt_lt' hε]
    linarith

end RHTower
