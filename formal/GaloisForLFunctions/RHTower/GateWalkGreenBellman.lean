import GaloisForLFunctions.RHTower.GateInverseWordCapacity
import GaloisForLFunctions.RHTower.GateWordInformationProjection

/-!
# The killed gate-walk Green function and its tropical limit

Geometrically killing the uniform gate walk and recording whether its endpoint lies in a target tube
produces a resolvent of the one-gate transfer operator.  Its iterates count the words of each length
that reach the tube, so the Green function is a weighted count of reaching words.

A shortest reaching word contributes an exactly known weight and no shorter word contributes
anything, which sandwiches the Green function between two powers of the fugacity.  Dividing the
logarithms by the logarithm of the inverse fugacity recovers the minimal reaching length exactly:
robust word complexity is the zero-fugacity valuation of the killed resolvent.
-/

open scoped ENNReal Topology
open Filter

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.RHTower

section GateGreen

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] [Nonempty Γ]
variable {X : Type*} [PseudoMetricSpace X]

/-- The one-gate transfer operator of the backward gate action. -/
noncomputable def gateAvgOp (act : Γ → X → X) (inv : Γ → Γ) (f : X → ℝ≥0∞) : X → ℝ≥0∞ :=
  fun v => ((Fintype.card Γ : ℝ≥0∞))⁻¹ * ∑ g : Γ, f (backAct act inv g v)

/-- The number of words of a fixed length whose endpoint lies in the target tube. -/
noncomputable def reachingWordCount (act : Γ → X → X) (χ : X) (ε : ℝ) (ℓ : ℕ) (v : X) : ℝ≥0∞ :=
  ∑' w : List Γ,
    Set.indicator {w : List Γ | w.length = ℓ ∧ wordEval act w χ ∈ tube ε v} 1 w

/-- **Transfer-operator word count.**  The iterated one-gate transfer operator applied to the seed
tube counts the words of that length reaching the target tube. -/
theorem gateAvgOp_iterate (act : Γ → X → X) (inv : Γ → Γ)
    (hinv : ∀ g x, act (inv g) (act g x) = x)
    (hiso : ∀ g x y, dist (act g x) (act g y) = dist x y) (χ : X) (ε : ℝ) (ℓ : ℕ) (v : X) :
    (gateAvgOp act inv)^[ℓ] (Set.indicator (tube ε χ) 1) v =
      ((Fintype.card Γ : ℝ≥0∞) ^ ℓ)⁻¹ * reachingWordCount act χ ε ℓ v := by
  classical
  induction ℓ generalizing v with
  | zero =>
    have hsingle : reachingWordCount act χ ε 0 v =
        Set.indicator (tube ε χ) (1 : X → ℝ≥0∞) v := by
      rw [reachingWordCount]
      have hterm : ∀ w : List Γ,
          Set.indicator {w : List Γ | w.length = 0 ∧ wordEval act w χ ∈ tube ε v} 1 w =
          if w = [] then Set.indicator (tube ε χ) (1 : X → ℝ≥0∞) v else 0 := by
        intro w
        by_cases hw : w = []
        · subst hw
          by_cases hv : v ∈ tube ε χ
          · rw [Set.indicator_of_mem (show ([] : List Γ) ∈
              {w : List Γ | w.length = 0 ∧ wordEval act w χ ∈ tube ε v} from
                ⟨rfl, mem_tube_comm.mpr hv⟩), Set.indicator_of_mem hv, if_pos rfl]
            rfl
          · rw [Set.indicator_of_notMem (show ([] : List Γ) ∉
              {w : List Γ | w.length = 0 ∧ wordEval act w χ ∈ tube ε v} from
                fun hc => hv (mem_tube_comm.mp hc.2)), Set.indicator_of_notMem hv, if_pos rfl]
        · rw [Set.indicator_of_notMem (show w ∉
            {w : List Γ | w.length = 0 ∧ wordEval act w χ ∈ tube ε v} from
              fun hc => hw (List.length_eq_zero_iff.mp hc.1)), if_neg hw]
      rw [tsum_congr hterm, tsum_ite_eq]
    simp [hsingle]
  | succ ℓ ih =>
    have hstep : ∀ g : Γ, (gateAvgOp act inv)^[ℓ] (Set.indicator (tube ε χ) 1)
        (backAct act inv g v) =
        ((Fintype.card Γ : ℝ≥0∞) ^ ℓ)⁻¹ * reachingWordCount act χ ε ℓ (backAct act inv g v) :=
      fun g => ih _
    have hcons : ∀ g : Γ, reachingWordCount act χ ε ℓ (backAct act inv g v) =
        ∑' w : List Γ,
          Set.indicator {w : List Γ | w.length = ℓ + 1 ∧ wordEval act w χ ∈ tube ε v} 1 (g :: w) := by
      intro g
      rw [reachingWordCount]
      refine tsum_congr fun w => ?_
      have hpull : wordEval act (g :: w) χ ∈ tube ε v ↔
          wordEval act w χ ∈ tube ε (backAct act inv g v) := by
        have := preimage_tube act inv hinv hiso ε g v
        constructor
        · intro h
          rw [← this]
          exact h
        · intro h
          rw [← this] at h
          exact h
      by_cases hw : w.length = ℓ ∧ wordEval act w χ ∈ tube ε (backAct act inv g v)
      · rw [Set.indicator_of_mem (show w ∈ {w : List Γ | w.length = ℓ ∧
          wordEval act w χ ∈ tube ε (backAct act inv g v)} from hw),
          Set.indicator_of_mem (show (g :: w) ∈ {w : List Γ | w.length = ℓ + 1 ∧
            wordEval act w χ ∈ tube ε v} from ⟨by simp [hw.1], hpull.mpr hw.2⟩)]
        rfl
      · rw [Set.indicator_of_notMem (show w ∉ {w : List Γ | w.length = ℓ ∧
          wordEval act w χ ∈ tube ε (backAct act inv g v)} from hw),
          Set.indicator_of_notMem (show (g :: w) ∉ {w : List Γ | w.length = ℓ + 1 ∧
            wordEval act w χ ∈ tube ε v} from fun hc =>
              hw ⟨by simpa using hc.1, hpull.mp hc.2⟩)]
  -- assemble
    have hnil : Set.indicator {w : List Γ | w.length = ℓ + 1 ∧ wordEval act w χ ∈ tube ε v}
        (1 : List Γ → ℝ≥0∞) [] = 0 := by
      refine Set.indicator_of_notMem (fun hc => ?_) _
      simpa using hc.1
    have hsplit : reachingWordCount act χ ε (ℓ + 1) v =
        ∑ g : Γ, reachingWordCount act χ ε ℓ (backAct act inv g v) := by
      rw [reachingWordCount, tsum_list_split, hnil, zero_add]
      have hprod : (∑' p : Γ × List Γ,
          Set.indicator {w : List Γ | w.length = ℓ + 1 ∧ wordEval act w χ ∈ tube ε v} 1
            (p.1 :: p.2)) =
          ∑' g : Γ, ∑' w : List Γ,
            Set.indicator {w : List Γ | w.length = ℓ + 1 ∧ wordEval act w χ ∈ tube ε v} 1
              (g :: w) :=
        ENNReal.tsum_prod (f := fun g w =>
          Set.indicator {w : List Γ | w.length = ℓ + 1 ∧ wordEval act w χ ∈ tube ε v} 1 (g :: w))
      rw [hprod, tsum_fintype]
      exact Finset.sum_congr rfl fun g _ => (hcons g).symm
    rw [Function.iterate_succ_apply', gateAvgOp,
      Finset.sum_congr rfl fun g _ => hstep g, ← Finset.mul_sum, hsplit, pow_succ]
    rw [ENNReal.mul_inv (by simp) (by simp)]
    ring

/-- The normalized killed gate-walk Green function of the target tube. -/
noncomputable def gateGreen (act : Γ → X → X) (χ : X) (ε : ℝ) (a : ℝ≥0∞) (v : X) : ℝ≥0∞ :=
  (1 - a) * ∑' w : List Γ, Set.indicator {w : List Γ | wordEval act w χ ∈ tube ε v}
    (fun w => (a / Fintype.card Γ) ^ w.length) w

theorem gateGreen_eq_zero_of_unreachable (act : Γ → X → X) (χ : X) (ε : ℝ) (a : ℝ≥0∞) (v : X)
    (h : ∀ w : List Γ, wordEval act w χ ∉ tube ε v) : gateGreen act χ ε a v = 0 := by
  classical
  rw [gateGreen]
  refine mul_eq_zero.mpr (Or.inr (ENNReal.tsum_eq_zero.mpr fun w => ?_))
  exact Set.indicator_of_notMem
    (show w ∉ {w : List Γ | wordEval act w χ ∈ tube ε v} from h w) _

/-- Lower half of the exact Green sandwich: a shortest reaching word contributes its exact
weight. -/
theorem gateGreen_ge (act : Γ → X → X) (χ : X) (ε : ℝ) (a : ℝ≥0∞) (v : X) {w₀ : List Γ}
    (hw₀ : wordEval act w₀ χ ∈ tube ε v) :
    (1 - a) * (a / Fintype.card Γ) ^ w₀.length ≤ gateGreen act χ ε a v := by
  classical
  rw [gateGreen]
  refine mul_le_mul_right ?_ _
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum w₀)
  rw [Set.indicator_of_mem (show w₀ ∈ {w : List Γ | wordEval act w χ ∈ tube ε v} from hw₀)]

/-- Upper half of the exact Green sandwich: no word shorter than the complexity reaches the
target. -/
theorem gateGreen_le (act : Γ → X → X) (χ : X) (ε : ℝ) {a : ℝ≥0∞} (ha : a < 1) (v : X) {c : ℕ}
    (hmin : ∀ w : List Γ, wordEval act w χ ∈ tube ε v → c ≤ w.length) :
    gateGreen act χ ε a v ≤ a ^ c := by
  classical
  have hMne : (Fintype.card Γ : ℝ≥0∞) ≠ 0 := by simp
  have hMtop : (Fintype.card Γ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsub : (1 : ℝ≥0∞) - a ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    exact tsub_le_self
  have hterm : ∀ w : List Γ,
      Set.indicator {w : List Γ | wordEval act w χ ∈ tube ε v}
        (fun w => (a / Fintype.card Γ) ^ w.length) w ≤
      (if c ≤ w.length then (a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length else 0) := by
    intro w
    by_cases hw : wordEval act w χ ∈ tube ε v
    · rw [Set.indicator_of_mem (show w ∈ {w : List Γ | wordEval act w χ ∈ tube ε v} from hw),
        if_pos (hmin w hw)]
    · rw [Set.indicator_of_notMem (show w ∉ {w : List Γ | wordEval act w χ ∈ tube ε v} from hw)]
      exact bot_le
  have hlevel : (∑' w : List Γ,
      (if c ≤ w.length then (a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length else 0)) =
      ∑' n : ℕ, (if c ≤ n then a ^ n else 0) := by
    rw [tsum_list_length_apply (Γ := Γ)
      (fun n => if c ≤ n then (a / (Fintype.card Γ : ℝ≥0∞)) ^ n else 0)]
    refine tsum_congr fun n => ?_
    by_cases hn : c ≤ n
    · rw [if_pos hn, if_pos hn, ← mul_pow, ENNReal.mul_div_cancel hMne hMtop]
    · rw [if_neg hn, if_neg hn, mul_zero]
  have hshift : (∑' n : ℕ, (if c ≤ n then a ^ n else 0)) = a ^ c * ∑' k : ℕ, a ^ k := by
    have hinj : Function.Injective (fun k : ℕ => k + c) := add_left_injective c
    have hsupp : Function.support (fun n : ℕ => if c ≤ n then a ^ n else 0) ⊆
        Set.range (fun k : ℕ => k + c) := by
      intro n hn
      by_cases hc : c ≤ n
      · exact ⟨n - c, Nat.sub_add_cancel hc⟩
      · exact absurd (if_neg hc) hn
    rw [← hinj.tsum_eq hsupp]
    have hval : ∀ k : ℕ, (if c ≤ k + c then a ^ (k + c) else 0) = a ^ c * a ^ k := by
      intro k
      rw [if_pos (by omega), pow_add, mul_comm]
    rw [tsum_congr hval, ENNReal.tsum_mul_left]
  calc gateGreen act χ ε a v
      ≤ (1 - a) * ∑' w : List Γ,
          (if c ≤ w.length then (a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length else 0) := by
        rw [gateGreen]
        exact mul_le_mul_right (ENNReal.tsum_le_tsum hterm) _
    _ = (1 - a) * (a ^ c * (1 - a)⁻¹) := by rw [hlevel, hshift, ENNReal.tsum_geometric]
    _ = a ^ c := by
        rw [← mul_assoc, mul_comm (1 - a), mul_assoc, ENNReal.mul_inv_cancel
          (tsub_pos_of_lt ha).ne' hsub, mul_one]


/-- The real-valued killed Green function at a real fugacity. -/
noncomputable def gateGreenReal (act : Γ → X → X) (χ : X) (ε : ℝ) (a : ℝ) (v : X) : ℝ :=
  (gateGreen act χ ε (ENNReal.ofReal a) v).toReal

theorem gateGreen_ne_top (act : Γ → X → X) (χ : X) (ε : ℝ) {a : ℝ} (ha1 : a < 1) (v : X) :
    gateGreen act χ ε (ENNReal.ofReal a) v ≠ ⊤ := by
  have halt : ENNReal.ofReal a < 1 := by
    rcases le_or_gt a 0 with h | h
    · rw [ENNReal.ofReal_of_nonpos h]
      exact zero_lt_one
    · rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h.le).mpr ha1
  refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
  simpa using gateGreen_le act χ ε halt v (c := 0) (fun w _ => Nat.zero_le _)

/-- **Exact Green sandwich.**  At a fugacity in the unit interval the real Green function is
squeezed between the two powers of the minimal reaching length. -/
theorem gateGreenReal_sandwich (act : Γ → X → X) (χ : X) (ε : ℝ) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (v : X) {w₀ : List Γ} (hw₀ : wordEval act w₀ χ ∈ tube ε v)
    (hmin : ∀ w : List Γ, wordEval act w χ ∈ tube ε v → w₀.length ≤ w.length) :
    (1 - a) * (a / Fintype.card Γ) ^ w₀.length ≤ gateGreenReal act χ ε a v ∧
      gateGreenReal act χ ε a v ≤ a ^ w₀.length := by
  have hM : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos (α := Γ)
  have halt : ENNReal.ofReal a < 1 := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ha0.le).mpr ha1
  have hGtop : gateGreen act χ ε (ENNReal.ofReal a) v ≠ ⊤ := gateGreen_ne_top act χ ε ha1 v
  have hlow := gateGreen_ge act χ ε (ENNReal.ofReal a) v hw₀
  have hhigh := gateGreen_le act χ ε halt v hmin
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal a = ENNReal.ofReal (1 - a) := by
    rw [ENNReal.ofReal_sub _ ha0.le, ENNReal.ofReal_one]
  have hlowreal : ((1 - ENNReal.ofReal a) *
      (ENNReal.ofReal a / (Fintype.card Γ : ℝ≥0∞)) ^ w₀.length).toReal =
      (1 - a) * (a / Fintype.card Γ) ^ w₀.length := by
    rw [hsub, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
      ENNReal.toReal_ofReal ha0.le, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - a)]
  have hlowtop : (1 - ENNReal.ofReal a) *
      (ENNReal.ofReal a / (Fintype.card Γ : ℝ≥0∞)) ^ w₀.length ≠ ⊤ := by
    rw [hsub]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ?_)
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (by simp)
  constructor
  · rw [← hlowreal, gateGreenReal]
    exact (ENNReal.toReal_le_toReal hlowtop hGtop).mpr hlow
  · rw [gateGreenReal, show a ^ w₀.length = ((ENNReal.ofReal a) ^ w₀.length).toReal by
      rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal ha0.le]]
    exact (ENNReal.toReal_le_toReal hGtop (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)).mpr hhigh

theorem gateGreenReal_pos (act : Γ → X → X) (χ : X) (ε : ℝ) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (v : X) {w₀ : List Γ} (hw₀ : wordEval act w₀ χ ∈ tube ε v)
    (hmin : ∀ w : List Γ, wordEval act w χ ∈ tube ε v → w₀.length ≤ w.length) :
    0 < gateGreenReal act χ ε a v := by
  have hM : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos (α := Γ)
  refine lt_of_lt_of_le ?_ (gateGreenReal_sandwich act χ ε ha0 ha1 v hw₀ hmin).1
  exact mul_pos (by linarith) (pow_pos (div_pos ha0 hM) _)

/-- **Two-sided complexity estimate.**  The logarithms of the Green sandwich bracket the minimal
reaching length. -/
theorem complexity_log_sandwich (act : Γ → X → X) (χ : X) (ε : ℝ) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (v : X) {w₀ : List Γ} (hw₀ : wordEval act w₀ χ ∈ tube ε v)
    (hmin : ∀ w : List Γ, wordEval act w χ ∈ tube ε v → w₀.length ≤ w.length) :
    (Real.log (1 - a) - Real.log (gateGreenReal act χ ε a v)) /
        Real.log (Fintype.card Γ / a) ≤ (w₀.length : ℝ) ∧
      (w₀.length : ℝ) ≤ -Real.log (gateGreenReal act χ ε a v) / Real.log (1 / a) := by
  have hM : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos (α := Γ)
  have hM1 : (1 : ℝ) ≤ Fintype.card Γ := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero (α := Γ))
  have hGpos := gateGreenReal_pos act χ ε ha0 ha1 v hw₀ hmin
  have hsand := gateGreenReal_sandwich act χ ε ha0 ha1 v hw₀ hmin
  have hLa : 0 < Real.log (1 / a) := by
    rw [one_div]
    exact Real.log_pos (one_lt_inv_iff₀.mpr ⟨ha0, ha1⟩)
  have hLMa : 0 < Real.log (Fintype.card Γ / a) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ ha0]
    linarith
  have hlogM : Real.log ((Fintype.card Γ : ℝ) / a) = Real.log (Fintype.card Γ) - Real.log a :=
    Real.log_div hM.ne' ha0.ne'
  have hupper : Real.log (gateGreenReal act χ ε a v) ≤ (w₀.length : ℝ) * Real.log a := by
    refine le_trans (Real.log_le_log hGpos hsand.2) (le_of_eq ?_)
    rw [Real.log_pow]
  have hlowpos : (0:ℝ) < (1 - a) * (a / Fintype.card Γ) ^ w₀.length :=
    mul_pos (by linarith) (pow_pos (div_pos ha0 hM) _)
  have hlower : Real.log (1 - a) +
      (w₀.length : ℝ) * (Real.log a - Real.log (Fintype.card Γ)) ≤
      Real.log (gateGreenReal act χ ε a v) := by
    refine le_trans (le_of_eq ?_) (Real.log_le_log hlowpos hsand.1)
    rw [Real.log_mul (by linarith) (pow_ne_zero _ (div_pos ha0 hM).ne'), Real.log_pow,
      Real.log_div ha0.ne' hM.ne']
  constructor
  · rw [div_le_iff₀ hLMa, hlogM]
    linarith
  · rw [le_div_iff₀ hLa, one_div, Real.log_inv]
    linarith

/-- **Tropical Green exponent.**  The minimal reaching length is the zero-fugacity valuation of the
killed Green function. -/
theorem tendsto_neg_log_gateGreenReal (act : Γ → X → X) (χ : X) (ε : ℝ) (v : X) {w₀ : List Γ}
    (hw₀ : wordEval act w₀ χ ∈ tube ε v)
    (hmin : ∀ w : List Γ, wordEval act w χ ∈ tube ε v → w₀.length ≤ w.length) :
    Filter.Tendsto
      (fun t : ℝ => -Real.log (gateGreenReal act χ ε t v) / Real.log (1 / t))
      (𝓝[>] (0 : ℝ)) (𝓝 (w₀.length : ℝ)) := by
  have hM : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos (α := Γ)
  have hlogtop : Filter.Tendsto (fun t : ℝ => Real.log (1 / t)) (𝓝[>] (0 : ℝ)) Filter.atTop := by
    have hb : Filter.Tendsto Real.log (𝓝[>] (0 : ℝ)) Filter.atBot := Real.tendsto_log_nhdsGT_zero
    have := Filter.tendsto_neg_atTop_iff.mpr hb
    refine this.congr fun t => ?_
    rw [one_div, Real.log_inv]
  have hnum : Filter.Tendsto
      (fun t : ℝ => (w₀.length : ℝ) * Real.log (Fintype.card Γ) - Real.log (1 - t))
      (𝓝[>] (0 : ℝ)) (𝓝 ((w₀.length : ℝ) * Real.log (Fintype.card Γ))) := by
    have hcont : Filter.Tendsto (fun t : ℝ => Real.log (1 - t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : ContinuousAt (fun t : ℝ => Real.log (1 - t)) 0 := by
        refine ContinuousAt.log ?_ (by norm_num)
        exact (continuous_const.sub continuous_id).continuousAt
      have := hc.tendsto
      simpa using this.mono_left nhdsWithin_le_nhds
    simpa using Filter.Tendsto.const_sub
      ((w₀.length : ℝ) * Real.log (Fintype.card Γ)) hcont
  have hupper : Filter.Tendsto
      (fun t : ℝ => (w₀.length : ℝ) +
        ((w₀.length : ℝ) * Real.log (Fintype.card Γ) - Real.log (1 - t)) / Real.log (1 / t))
      (𝓝[>] (0 : ℝ)) (𝓝 (w₀.length : ℝ)) := by
    have hzero := Filter.Tendsto.const_add ((w₀.length : ℝ))
      (Filter.Tendsto.div_atTop hnum hlogtop)
    simpa using hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    exact (complexity_log_sandwich act χ ε ht0 ht1 v hw₀ hmin).2
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    obtain ⟨ht0, ht1⟩ := ht
    have hLa : 0 < Real.log (1 / t) := by
      rw [one_div]
      exact Real.log_pos (one_lt_inv_iff₀.mpr ⟨ht0, ht1⟩)
    have hone := (complexity_log_sandwich act χ ε ht0 ht1 v hw₀ hmin).1
    have hlogM : Real.log ((Fintype.card Γ : ℝ) / t) = Real.log (Fintype.card Γ) + Real.log (1 / t) := by
      rw [Real.log_div hM.ne' ht0.ne', one_div, Real.log_inv]
      ring
    rw [div_le_iff₀ hLa, add_mul, div_mul_cancel₀ _ hLa.ne']
    rw [div_le_iff₀ (by rw [hlogM]; positivity), hlogM] at hone
    linarith


end GateGreen

section SoftCalibration

variable {Γ : Type*} [Fintype Γ] [DecidableEq Γ] [Nonempty Γ]
variable {X : Type*} [PseudoMetricSpace X]

/-- The radial soft target kernel of a tube. -/
noncomputable def softKernel (β ε : ℝ) (x v : X) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * max (dist x v - ε) 0))

theorem softKernel_le_one {β : ℝ} (hβ : 0 ≤ β) (ε : ℝ) (x v : X) : softKernel β ε x v ≤ 1 := by
  rw [softKernel, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Real.exp_zero]
  refine Real.exp_le_exp.mpr ?_
  have : 0 ≤ max (dist x v - ε) 0 := le_max_right _ _
  nlinarith

theorem softKernel_pos (β ε : ℝ) (x v : X) : 0 < softKernel β ε x v := by
  rw [softKernel]
  exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)

theorem softKernel_ne_top (β ε : ℝ) (x v : X) : softKernel β ε x v ≠ ⊤ := ENNReal.ofReal_ne_top

theorem softKernel_of_mem_tube {β ε : ℝ} {x v : X} (h : x ∈ tube ε v) :
    softKernel β ε x v = 1 := by
  have hle : dist x v - ε ≤ 0 := by
    have : dist x v ≤ ε := h
    linarith
  rw [softKernel, max_eq_right hle, mul_zero, Real.exp_zero, ENNReal.ofReal_one]

/-- The soft-target killed Green function. -/
noncomputable def softGreen (act : Γ → X → X) (χ : X) (β ε : ℝ) (a : ℝ≥0∞) (v : X) : ℝ≥0∞ :=
  (1 - a) * ∑' w : List Γ, (a / Fintype.card Γ) ^ w.length *
    softKernel β ε (wordEval act w χ) v

theorem softGreen_ge_of_reaching (act : Γ → X → X) (χ : X) (β ε : ℝ) (a : ℝ≥0∞) (v : X)
    {w : List Γ} (hw : wordEval act w χ ∈ tube ε v) :
    (1 - a) * (a / Fintype.card Γ) ^ w.length ≤ softGreen act χ β ε a v := by
  rw [softGreen]
  refine mul_le_mul_right ?_ _
  refine le_trans (le_of_eq ?_) (ENNReal.le_tsum w)
  rw [softKernel_of_mem_tube hw, mul_one]

theorem softGreen_le_one (act : Γ → X → X) (χ : X) {β ε : ℝ} (hβ : 0 ≤ β) {a : ℝ≥0∞}
    (ha : a < 1) (v : X) : softGreen act χ β ε a v ≤ 1 := by
  have hMne : (Fintype.card Γ : ℝ≥0∞) ≠ 0 := by simp
  have hMtop : (Fintype.card Γ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsub : (1 : ℝ≥0∞) - a ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hterm : ∀ w : List Γ, (a / Fintype.card Γ) ^ w.length *
      softKernel β ε (wordEval act w χ) v ≤ (a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length := by
    intro w
    calc (a / Fintype.card Γ) ^ w.length * softKernel β ε (wordEval act w χ) v
        ≤ (a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length * 1 :=
          mul_le_mul_right (softKernel_le_one hβ ε _ v) _
      _ = (a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length := mul_one _
  have hgeom : (∑' w : List Γ, (a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length) = (1 - a)⁻¹ := by
    rw [tsum_list_length_apply (Γ := Γ) (fun n => (a / (Fintype.card Γ : ℝ≥0∞)) ^ n)]
    have hstep : ∀ n : ℕ, (Fintype.card Γ : ℝ≥0∞) ^ n *
        (a / (Fintype.card Γ : ℝ≥0∞)) ^ n = a ^ n := by
      intro n
      rw [← mul_pow, ENNReal.mul_div_cancel hMne hMtop]
    rw [tsum_congr hstep, ENNReal.tsum_geometric]
  calc softGreen act χ β ε a v
      ≤ (1 - a) * ∑' w : List Γ, (a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length := by
        rw [softGreen]
        exact mul_le_mul_right (ENNReal.tsum_le_tsum hterm) _
    _ = 1 := by
        rw [hgeom, ENNReal.mul_inv_cancel (tsub_pos_of_lt ha).ne' hsub]

/-- **Gate Harnack inequality.**  Moving the target by one gate costs at most one gate weight. -/
theorem softGreen_gate_harnack (act : Γ → X → X) (χ : X) (β ε : ℝ)
    (hiso : ∀ g x y, dist (act g x) (act g y) = dist x y) (a : ℝ≥0∞) (v : X) (g : Γ) :
    (a / Fintype.card Γ) * softGreen act χ β ε a v ≤ softGreen act χ β ε a (act g v) := by
  have hkernel : ∀ w : List Γ,
      softKernel β ε (wordEval act (g :: w) χ) (act g v) =
      softKernel β ε (wordEval act w χ) v := by
    intro w
    rw [softKernel, softKernel, wordEval, hiso g (wordEval act w χ) v]
  have hcons : Function.Injective (fun w : List Γ => g :: w) := by
    intro w w' h
    simpa using h
  have hle : (∑' w : List Γ, (a / (Fintype.card Γ : ℝ≥0∞)) ^ (g :: w).length *
      softKernel β ε (wordEval act (g :: w) χ) (act g v)) ≤
      ∑' u : List Γ, (a / (Fintype.card Γ : ℝ≥0∞)) ^ u.length *
        softKernel β ε (wordEval act u χ) (act g v) :=
    ENNReal.tsum_comp_le_tsum_of_injective hcons
      (fun u => (a / (Fintype.card Γ : ℝ≥0∞)) ^ u.length *
        softKernel β ε (wordEval act u χ) (act g v))
  have hrew : (∑' w : List Γ, (a / (Fintype.card Γ : ℝ≥0∞)) ^ (g :: w).length *
      softKernel β ε (wordEval act (g :: w) χ) (act g v)) =
      (a / (Fintype.card Γ : ℝ≥0∞)) * ∑' w : List Γ,
        (a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length * softKernel β ε (wordEval act w χ) v := by
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun w => ?_
    rw [hkernel w, List.length_cons, pow_succ]
    ring
  rw [hrew] at hle
  rw [softGreen, softGreen, ← mul_assoc, mul_comm (a / (Fintype.card Γ : ℝ≥0∞)) (1 - a),
    mul_assoc]
  exact mul_le_mul_right hle _

/-- **Radial Lipschitz transfer.**  Moving the target changes every kernel value by at most the
exponential of the displacement. -/
theorem softKernel_le_mul (β : ℝ) (hβ : 0 ≤ β) (ε : ℝ) (x v v' : X) :
    softKernel β ε x v ≤ ENNReal.ofReal (Real.exp (β * dist v v')) * softKernel β ε x v' := by
  have hlip : max (dist x v' - ε) 0 - max (dist x v - ε) 0 ≤ dist v v' := by
    rcases le_total (dist x v' - ε) 0 with h | h
    · rw [max_eq_right h]
      have : 0 ≤ max (dist x v - ε) 0 := le_max_right _ _
      have hd : 0 ≤ dist v v' := dist_nonneg
      linarith
    · rw [max_eq_left h]
      have hge : dist x v' ≤ dist x v + dist v v' := dist_triangle x v v'
      have : dist x v - ε ≤ max (dist x v - ε) 0 := le_max_left _ _
      linarith
  rw [softKernel, softKernel, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
  nlinarith [hlip]

theorem softGreen_pos (act : Γ → X → X) (χ : X) (β ε : ℝ) {a : ℝ≥0∞} (ha : a < 1) (v : X) :
    0 < softGreen act χ β ε a v := by
  have hsub : (0 : ℝ≥0∞) < 1 - a := tsub_pos_of_lt ha
  rw [softGreen]
  refine ENNReal.mul_pos hsub.ne' (ne_of_gt ?_)
  refine lt_of_lt_of_le ?_ (ENNReal.le_tsum ([] : List Γ))
  simpa using softKernel_pos β ε χ v

/-- The real-valued soft-target Green function. -/
noncomputable def softGreenReal (act : Γ → X → X) (χ : X) (β ε : ℝ) (a : ℝ) (v : X) : ℝ :=
  (softGreen act χ β ε (ENNReal.ofReal a) v).toReal

theorem ofReal_lt_one_of_lt_one {a : ℝ} (ha1 : a < 1) : ENNReal.ofReal a < 1 := by
  rcases le_or_gt a 0 with h | h
  · rw [ENNReal.ofReal_of_nonpos h]
    exact zero_lt_one
  · rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h.le).mpr ha1

theorem softGreen_ne_top (act : Γ → X → X) (χ : X) {β ε : ℝ} (hβ : 0 ≤ β) {a : ℝ}
    (ha1 : a < 1) (v : X) : softGreen act χ β ε (ENNReal.ofReal a) v ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top
    (softGreen_le_one act χ hβ (ofReal_lt_one_of_lt_one ha1) v)

theorem softGreenReal_pos (act : Γ → X → X) (χ : X) {β ε : ℝ} (hβ : 0 ≤ β) {a : ℝ}
    (ha1 : a < 1) (v : X) : 0 < softGreenReal act χ β ε a v := by
  rw [softGreenReal]
  refine ENNReal.toReal_pos (softGreen_pos act χ β ε (ofReal_lt_one_of_lt_one ha1) v).ne' ?_
  exact softGreen_ne_top act χ hβ ha1 v

theorem softGreenReal_ge_of_reaching (act : Γ → X → X) (χ : X) {β ε : ℝ} (hβ : 0 ≤ β) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (v : X) {w : List Γ} (hw : wordEval act w χ ∈ tube ε v) :
    (1 - a) * (a / Fintype.card Γ) ^ w.length ≤ softGreenReal act χ β ε a v := by
  have hM : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos (α := Γ)
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal a = ENNReal.ofReal (1 - a) := by
    rw [ENNReal.ofReal_sub _ ha0.le, ENNReal.ofReal_one]
  have hbase := softGreen_ge_of_reaching act χ β ε (ENNReal.ofReal a) v hw
  have hlowreal : ((1 - ENNReal.ofReal a) *
      (ENNReal.ofReal a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length).toReal =
      (1 - a) * (a / Fintype.card Γ) ^ w.length := by
    rw [hsub, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div,
      ENNReal.toReal_ofReal ha0.le, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - a)]
  have hlowtop : (1 - ENNReal.ofReal a) *
      (ENNReal.ofReal a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length ≠ ⊤ := by
    rw [hsub]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ?_)
    exact ENNReal.div_ne_top ENNReal.ofReal_ne_top (by simp)
  rw [← hlowreal, softGreenReal]
  exact (ENNReal.toReal_le_toReal hlowtop (softGreen_ne_top act χ hβ ha1 v)).mpr hbase

/-- The external robust Bellman calibration of a target. -/
noncomputable def bellmanCalibration (act : Γ → X → X) (χ : X) (β ε a : ℝ) (v : X) : ℝ :=
  (Real.log (1 - a) - Real.log (softGreenReal act χ β ε a v)) /
    Real.log (Fintype.card Γ / a)

theorem softGreen_le_mul (act : Γ → X → X) (χ : X) {β : ℝ} (hβ : 0 ≤ β) (ε : ℝ) (a : ℝ≥0∞)
    (v v' : X) :
    softGreen act χ β ε a v ≤
      ENNReal.ofReal (Real.exp (β * dist v v')) * softGreen act χ β ε a v' := by
  have hterm : ∀ w : List Γ, (a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length *
      softKernel β ε (wordEval act w χ) v ≤
      ENNReal.ofReal (Real.exp (β * dist v v')) *
        ((a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length *
          softKernel β ε (wordEval act w χ) v') := by
    intro w
    have h := softKernel_le_mul β hβ ε (wordEval act w χ) v v'
    calc (a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length * softKernel β ε (wordEval act w χ) v
        ≤ (a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length *
          (ENNReal.ofReal (Real.exp (β * dist v v')) *
            softKernel β ε (wordEval act w χ) v') := mul_le_mul_right h _
      _ = ENNReal.ofReal (Real.exp (β * dist v v')) *
          ((a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length *
            softKernel β ε (wordEval act w χ) v') := by ring
  rw [softGreen, softGreen]
  calc (1 - a) * ∑' w : List Γ, (a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length *
        softKernel β ε (wordEval act w χ) v
      ≤ (1 - a) * ∑' w : List Γ, ENNReal.ofReal (Real.exp (β * dist v v')) *
          ((a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length *
            softKernel β ε (wordEval act w χ) v') :=
        mul_le_mul_right (ENNReal.tsum_le_tsum hterm) _
    _ = ENNReal.ofReal (Real.exp (β * dist v v')) *
        ((1 - a) * ∑' w : List Γ, (a / (Fintype.card Γ : ℝ≥0∞)) ^ w.length *
          softKernel β ε (wordEval act w χ) v') := by
        rw [ENNReal.tsum_mul_left]
        ring

theorem softGreenReal_le_mul (act : Γ → X → X) (χ : X) {β : ℝ} (hβ : 0 ≤ β) (ε : ℝ) {a : ℝ}
    (ha1 : a < 1) (v v' : X) :
    softGreenReal act χ β ε a v ≤
      Real.exp (β * dist v v') * softGreenReal act χ β ε a v' := by
  have hbase := softGreen_le_mul act χ hβ ε (ENNReal.ofReal a) v v'
  have hne : ENNReal.ofReal (Real.exp (β * dist v v')) *
      softGreen act χ β ε (ENNReal.ofReal a) v' ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (softGreen_ne_top act χ hβ ha1 v')
  have := (ENNReal.toReal_le_toReal (softGreen_ne_top act χ hβ ha1 v) hne).mpr hbase
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)] at this

theorem softGreenReal_gate_harnack (act : Γ → X → X) (χ : X) {β ε : ℝ} (hβ : 0 ≤ β)
    (hiso : ∀ g x y, dist (act g x) (act g y) = dist x y) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (v : X) (g : Γ) :
    a / Fintype.card Γ * softGreenReal act χ β ε a v ≤ softGreenReal act χ β ε a (act g v) := by
  have hM : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos (α := Γ)
  have hbase := softGreen_gate_harnack act χ β ε hiso (ENNReal.ofReal a) v g
  have hne : ENNReal.ofReal a / (Fintype.card Γ : ℝ≥0∞) *
      softGreen act χ β ε (ENNReal.ofReal a) v ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.div_ne_top ENNReal.ofReal_ne_top (by simp)) ?_
    exact softGreen_ne_top act χ hβ ha1 v
  have := (ENNReal.toReal_le_toReal hne (softGreen_ne_top act χ hβ ha1 (act g v))).mpr hbase
  rwa [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_ofReal ha0.le,
    ENNReal.toReal_natCast] at this

/-- **Bellman lower certificate.**  The calibration never exceeds the length of a reaching word. -/
theorem bellmanCalibration_le (act : Γ → X → X) (χ : X) {β ε : ℝ} (hβ : 0 ≤ β) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (v : X) {w : List Γ} (hw : wordEval act w χ ∈ tube ε v) :
    bellmanCalibration act χ β ε a v ≤ (w.length : ℝ) := by
  have hM : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos (α := Γ)
  have hM1 : (1 : ℝ) ≤ Fintype.card Γ := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero (α := Γ))
  have hLMa : 0 < Real.log ((Fintype.card Γ : ℝ) / a) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ ha0]
    linarith
  have hGpos := softGreenReal_pos act χ (ε := ε) hβ ha1 v
  have hlowpos : (0:ℝ) < (1 - a) * (a / Fintype.card Γ) ^ w.length :=
    mul_pos (by linarith) (pow_pos (div_pos ha0 hM) _)
  have hlog : Real.log (1 - a) + (w.length : ℝ) * (Real.log a - Real.log (Fintype.card Γ)) ≤
      Real.log (softGreenReal act χ β ε a v) := by
    refine le_trans (le_of_eq ?_)
      (Real.log_le_log hlowpos (softGreenReal_ge_of_reaching act χ hβ ha0 ha1 v hw))
    rw [Real.log_mul (by linarith) (pow_ne_zero _ (div_pos ha0 hM).ne'), Real.log_pow,
      Real.log_div ha0.ne' hM.ne']
  rw [bellmanCalibration, div_le_iff₀ hLMa, Real.log_div hM.ne' ha0.ne']
  linarith

/-- **Gate step inequality.**  Moving the target by one gate raises the calibration by at most
one. -/
theorem bellmanCalibration_gate_step (act : Γ → X → X) (χ : X) {β ε : ℝ} (hβ : 0 ≤ β)
    (hiso : ∀ g x y, dist (act g x) (act g y) = dist x y) {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (v : X) (g : Γ) :
    bellmanCalibration act χ β ε a (act g v) ≤ bellmanCalibration act χ β ε a v + 1 := by
  have hM : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos (α := Γ)
  have hM1 : (1 : ℝ) ≤ Fintype.card Γ := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero (α := Γ))
  have hLMa : 0 < Real.log ((Fintype.card Γ : ℝ) / a) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ ha0]
    linarith
  have hGv := softGreenReal_pos act χ (ε := ε) hβ ha1 v
  have hGgv := softGreenReal_pos act χ (ε := ε) hβ ha1 (act g v)
  have hharn := softGreenReal_gate_harnack act χ (ε := ε) hβ hiso ha0 ha1 v g
  have hstep : Real.log (a / Fintype.card Γ) + Real.log (softGreenReal act χ β ε a v) ≤
      Real.log (softGreenReal act χ β ε a (act g v)) := by
    refine le_trans (le_of_eq ?_) (Real.log_le_log (by positivity) hharn)
    rw [Real.log_mul (div_pos ha0 hM).ne' hGv.ne']
  have hswap : Real.log (a / (Fintype.card Γ : ℝ)) = -Real.log ((Fintype.card Γ : ℝ) / a) := by
    rw [Real.log_div ha0.ne' hM.ne', Real.log_div hM.ne' ha0.ne']
    ring
  rw [hswap] at hstep
  rw [bellmanCalibration, bellmanCalibration, div_le_iff₀ hLMa]
  have hexp : ((Real.log (1 - a) - Real.log (softGreenReal act χ β ε a v)) /
      Real.log ((Fintype.card Γ : ℝ) / a) + 1) * Real.log ((Fintype.card Γ : ℝ) / a) =
      (Real.log (1 - a) - Real.log (softGreenReal act χ β ε a v)) +
        Real.log ((Fintype.card Γ : ℝ) / a) := by
    field_simp
  rw [hexp]
  linarith

/-- **Radial Lipschitz calibration.**  The calibration is Lipschitz in the target. -/
theorem abs_bellmanCalibration_sub_le (act : Γ → X → X) (χ : X) {β ε : ℝ} (hβ : 0 ≤ β) {a : ℝ}
    (ha0 : 0 < a) (ha1 : a < 1) (v v' : X) :
    |bellmanCalibration act χ β ε a v - bellmanCalibration act χ β ε a v'| ≤
      β * dist v v' / Real.log (Fintype.card Γ / a) := by
  have hM : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos (α := Γ)
  have hM1 : (1 : ℝ) ≤ Fintype.card Γ := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero (α := Γ))
  have hLMa : 0 < Real.log ((Fintype.card Γ : ℝ) / a) := by
    refine Real.log_pos ?_
    rw [lt_div_iff₀ ha0]
    linarith
  have hGv := softGreenReal_pos act χ (ε := ε) hβ ha1 v
  have hGv' := softGreenReal_pos act χ (ε := ε) hβ ha1 v'
  have hone : Real.log (softGreenReal act χ β ε a v) -
      Real.log (softGreenReal act χ β ε a v') ≤ β * dist v v' := by
    have hle := softGreenReal_le_mul act χ hβ ε ha1 v v'
    have := Real.log_le_log hGv hle
    rw [Real.log_mul (Real.exp_ne_zero _) hGv'.ne', Real.log_exp] at this
    linarith
  have htwo : Real.log (softGreenReal act χ β ε a v') -
      Real.log (softGreenReal act χ β ε a v) ≤ β * dist v v' := by
    have hle := softGreenReal_le_mul act χ hβ ε ha1 v' v
    have := Real.log_le_log hGv' hle
    rw [Real.log_mul (Real.exp_ne_zero _) hGv.ne', Real.log_exp, dist_comm v' v] at this
    linarith
  have hdiff : bellmanCalibration act χ β ε a v - bellmanCalibration act χ β ε a v' =
      (Real.log (softGreenReal act χ β ε a v') - Real.log (softGreenReal act χ β ε a v)) /
        Real.log ((Fintype.card Γ : ℝ) / a) := by
    rw [bellmanCalibration, bellmanCalibration, div_sub_div_same]
    congr 1
    ring
  rw [hdiff, abs_div, abs_of_pos hLMa]
  gcongr
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **Complete-union control by one scalar collision.**  The probability of a retained event on
which the target is reachable within a fixed length is controlled by one soft Green moment. -/
theorem measure_reachable_le_lintegral (act : Γ → X → X) (χ : X) (β ε : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) (V : Ω → X) (R : Set Ω)
    {a : ℝ≥0∞} (ha0 : a ≠ 0) (ha1 : a < 1) (s : ℕ)
    (hE : MeasurableSet {ω : Ω | ∃ w : List Γ, w.length ≤ s ∧ wordEval act w χ ∈ tube ε (V ω)}) :
    μ ({ω : Ω | ∃ w : List Γ, w.length ≤ s ∧ wordEval act w χ ∈ tube ε (V ω)} ∩ R) ≤
      (∫⁻ ω in R, softGreen act χ β ε a (V ω) ∂μ) /
        ((1 - a) * (a / Fintype.card Γ) ^ s) := by
  classical
  have hMne : (Fintype.card Γ : ℝ≥0∞) ≠ 0 := by simp
  have hMtop : (Fintype.card Γ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hatop : a ≠ ⊤ := ne_top_of_lt ha1
  have hM1 : (1 : ℝ≥0∞) ≤ (Fintype.card Γ : ℝ≥0∞) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_ne_zero (α := Γ))
  have haM : a / (Fintype.card Γ : ℝ≥0∞) ≤ 1 :=
    ENNReal.div_le_of_le_mul (by simpa using le_trans ha1.le hM1)
  have hcne : (1 - a) * (a / (Fintype.card Γ : ℝ≥0∞)) ^ s ≠ 0 := by
    refine mul_ne_zero (tsub_pos_of_lt ha1).ne' (pow_ne_zero _ ?_)
    simp [ENNReal.div_eq_zero_iff, ha0, hMtop]
  have hctop : (1 - a) * (a / (Fintype.card Γ : ℝ≥0∞)) ^ s ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)
      (ENNReal.pow_ne_top (ENNReal.div_ne_top hatop hMne))
  have hpoint : ∀ ω : Ω,
      Set.indicator {ω : Ω | ∃ w : List Γ, w.length ≤ s ∧ wordEval act w χ ∈ tube ε (V ω)} 1 ω ≤
      softGreen act χ β ε a (V ω) / ((1 - a) * (a / Fintype.card Γ) ^ s) := by
    intro ω
    by_cases hω : ω ∈ {ω : Ω | ∃ w : List Γ, w.length ≤ s ∧ wordEval act w χ ∈ tube ε (V ω)}
    · obtain ⟨w, hwlen, hw⟩ := id hω
      rw [Set.indicator_of_mem hω]
      show (1 : ℝ≥0∞) ≤ _
      rw [ENNReal.le_div_iff_mul_le (Or.inl hcne) (Or.inl hctop), one_mul]
      refine le_trans ?_ (softGreen_ge_of_reaching act χ β ε a (V ω) hw)
      exact mul_le_mul_right (pow_le_pow_right_of_le_one' haM hwlen) _
    · rw [Set.indicator_of_notMem hω]
      exact bot_le
  calc μ ({ω : Ω | ∃ w : List Γ, w.length ≤ s ∧ wordEval act w χ ∈ tube ε (V ω)} ∩ R)
      = (μ.restrict R) {ω : Ω | ∃ w : List Γ, w.length ≤ s ∧ wordEval act w χ ∈ tube ε (V ω)} :=
        (MeasureTheory.Measure.restrict_apply hE).symm
    _ = ∫⁻ ω in R,
          Set.indicator {ω : Ω | ∃ w : List Γ, w.length ≤ s ∧
            wordEval act w χ ∈ tube ε (V ω)} 1 ω ∂μ :=
        (MeasureTheory.lintegral_indicator_one hE).symm
    _ ≤ ∫⁻ ω in R, softGreen act χ β ε a (V ω) /
          ((1 - a) * (a / Fintype.card Γ) ^ s) ∂μ :=
        MeasureTheory.lintegral_mono hpoint
    _ = (∫⁻ ω in R, softGreen act χ β ε a (V ω) ∂μ) /
          ((1 - a) * (a / Fintype.card Γ) ^ s) := by
        set c : ℝ≥0∞ := (1 - a) * (a / (Fintype.card Γ : ℝ≥0∞)) ^ s with hc
        simp only [ENNReal.div_eq_inv_mul]
        exact MeasureTheory.lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hcne)

end SoftCalibration


end GaloisForLFunctions.RHTower
