import GaloisForLFunctions.RHTower.JitteredUnitCellPartition

/-!
# Unit granularity is supercritical: random unit-cell systems are almost surely not Weil-positive

One uniform atom of mass one in each unit cell `[k+1, k+2)` of `[1, ∞)`, minus the atom
`e^{1/20000} δ_{e^{1/10000}}`, has Weil density `2(archDensity t − cellSum 1 u t)` on the critical
line.  The theorem `ae_exists_archDensity_lt_cellSum_one`: **almost surely the density is negative
at arbitrarily large heights**, so almost surely the system is not Weil-positive.

Proof:
* On the block event of `[2^j, 2^{j+1})` (probability `≥ 1/(8(C+1))` for `j ≥ 2000`) some integer
  height carries `cellSum ≥ (23/40) j log 2 − C₀`, while `archDensity ≤ ½ log t + 2`.
* Continuity from above gives probability `≥ 1/(8(C+1))` to infinitely many block events, hence to
  the event `E` that `cellSum(n) − ½ log n` is unbounded above along integers (coordinates clamped
  to `[0, 1]`).
* Changing finitely many cells moves `cellSum` by a bounded amount, so `E` lies in the tail
  σ-algebra of the independent coordinates; Kolmogorov's zero–one law gives `P(E) = 1`.
-/

open Real MeasureTheory ProbabilityTheory Set Filter

noncomputable section

namespace RHTower
namespace RandomCellWeil

/-! ### The archimedean ceiling -/

/-- `archDensity t ≤ ½ log |t| + 2` for `|t| > 4800`. -/
theorem archDensity_le_log {t : ℝ} (ht : 4800 < |t|) :
    archDensity t ≤ (1 / 2) * Real.log |t| + 2 := by
  set z : ℂ := ((5 / 4 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I with hz
  have hre : z.re = 5 / 4 := by simp [hz]
  have him : z.im = t / 2 := by simp [hz]
  have hnorm_lo : |t| / 2 ≤ ‖z‖ := by
    have h1 := Complex.abs_im_le_norm z
    rw [him, abs_div, abs_two] at h1
    exact h1
  have hnorm_hi : ‖z‖ ≤ |t| := by
    have h := Complex.norm_le_abs_re_add_abs_im z
    have e1 : |(5 / 4 : ℝ)| = 5 / 4 := by norm_num
    have e2 : |t / 2| = |t| / 2 := by rw [abs_div, abs_two]
    rw [hre, him, e1, e2] at h
    linarith
  have h2400 : 2400 ≤ ‖z‖ := by linarith
  have hasym := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos
    (z := z) (by rw [hre]; norm_num) (by linarith)
  have hupre : (Complex.digamma z).re ≤ Real.log ‖z‖ + 3 / ‖z‖ := by
    have h := Complex.abs_re_le_norm (Complex.digamma z - Complex.log z)
    rw [Complex.sub_re, Complex.log_re] at h
    have := abs_le.mp (h.trans hasym)
    linarith [this.2]
  have hlogz : Real.log ‖z‖ ≤ Real.log |t| := Real.log_le_log (by linarith) hnorm_hi
  have h3 : 3 / ‖z‖ ≤ 3 / 2400 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2400
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hcos := Real.cos_le_one (t / 10000)
  unfold archDensity
  rw [← hz]
  nlinarith

/-! ### Clamped coordinates -/

/-- The clamp of a real number to `[0, 1]`. -/
def clamp01 (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clamp01_mem (x : ℝ) : clamp01 x ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem clamp01_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : clamp01 x = x := by
  unfold clamp01
  rw [min_eq_right hx.2, max_eq_right hx.1]

theorem measurable_clamp01 : Measurable clamp01 := by
  unfold clamp01
  fun_prop

/-- The clamped configuration. -/
def clampU (u : ℕ → ℝ) : ℕ → ℝ := fun k => clamp01 (u k)

theorem clampU_mem (u : ℕ → ℝ) (k : ℕ) : clampU u k ∈ Icc (0 : ℝ) 1 := clamp01_mem _

theorem clampU_of_mem {u : ℕ → ℝ} (hu : ∀ k, u k ∈ Icc (0 : ℝ) 1) : clampU u = u := by
  funext k; exact clamp01_of_mem (hu k)

/-! ### The unbounded-excess event -/

/-- The event that `unitSum (clampU u) n − ½ log n` is unbounded above along integers `n`. -/
def excessEvent : Set (ℕ → ℝ) :=
  {u | ∀ M : ℕ, ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧ (M : ℝ) + (1 / 2) * Real.log n ≤ unitSum (clampU u) n}

/-- The tail of the clamped sum beyond the first `m` cells. -/
def tailSum (m : ℕ) (u : ℕ → ℝ) (t : ℝ) : ℝ := ∑' i, unitTerm (i + m) (clamp01 (u (i + m))) t

/-- The same event written with the tail beyond `m` cells. -/
def tailEvent (m : ℕ) : Set (ℕ → ℝ) :=
  {u | ∀ M : ℕ, ∀ n₀ : ℕ, ∃ n : ℕ, n₀ ≤ n ∧ (M : ℝ) + (1 / 2) * Real.log n ≤ tailSum m u n}

theorem abs_head_le (m : ℕ) (u : ℕ → ℝ) (t : ℝ) :
    |∑ k ∈ Finset.range m, unitTerm k (clampU u k) t| ≤ 2 * m := by
  have h := abs_field_le (u := clampU u) (clampU_mem u) m t
  simpa [field] using h

theorem unitSum_clamp_split (m : ℕ) (u : ℕ → ℝ) (t : ℝ) :
    unitSum (clampU u) t = ∑ k ∈ Finset.range m, unitTerm k (clampU u k) t + tailSum m u t := by
  have hs := summable_unitTerm (clampU_mem u) t
  rw [unitSum, ← hs.sum_add_tsum_nat_add m]
  rfl

theorem excessEvent_eq_tailEvent (m : ℕ) : excessEvent = tailEvent m := by
  ext u
  simp only [excessEvent, tailEvent, Set.mem_setOf_eq]
  constructor
  · intro h M n₀
    obtain ⟨n, hn, hle⟩ := h (M + 2 * m) n₀
    refine ⟨n, hn, ?_⟩
    rw [unitSum_clamp_split m] at hle
    have := (abs_le.mp (abs_head_le m u n)).2
    push_cast at hle
    linarith
  · intro h M n₀
    obtain ⟨n, hn, hle⟩ := h (M + 2 * m) n₀
    refine ⟨n, hn, ?_⟩
    rw [unitSum_clamp_split m]
    have := (abs_le.mp (abs_head_le m u n)).1
    push_cast at hle
    linarith

/-! ### Tail measurability -/

/-- The σ-algebra of the `k`-th coordinate. -/
abbrev coordSigma (k : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  MeasurableSpace.comap (fun u : ℕ → ℝ => u k) inferInstance

theorem coordSigma_le (k : ℕ) : coordSigma k ≤ MeasurableSpace.pi :=
  (measurable_pi_apply k).comap_le

theorem iIndep_coordSigma : iIndep coordSigma cellLaw := by
  have h := iIndepFun_infinitePi (P := fun _ : ℕ => unitLaw) (X := fun _ (v : ℝ) => v)
    (fun _ => measurable_id)
  exact h.iIndep

theorem measurable_tailSum (m : ℕ) (t : ℝ) :
    Measurable[⨆ i ≥ m, coordSigma i] (fun u => tailSum m u t) := by
  set mm : MeasurableSpace (ℕ → ℝ) := ⨆ i ≥ m, coordSigma i with hmm
  have hterm : ∀ i : ℕ, Measurable[mm]
      (fun w : ℕ → ℝ => unitTerm (i + m) (clamp01 (w (i + m))) t) := by
    intro i
    have hproj : Measurable[mm] (fun w : ℕ → ℝ => w (i + m)) := by
      apply Measurable.of_comap_le
      exact le_iSup₂_of_le (i + m) (by omega) le_rfl
    exact ((measurable_unitTerm (i + m) t).comp measurable_clamp01).comp hproj
  have hpart : ∀ N : ℕ, Measurable[mm]
      (fun w : ℕ → ℝ => ∑ i ∈ Finset.range N, unitTerm (i + m) (clamp01 (w (i + m))) t) :=
    fun N => Finset.measurable_sum _ (fun i _ => hterm i)
  have hlim : Tendsto (fun (N : ℕ) (w : ℕ → ℝ) =>
      ∑ i ∈ Finset.range N, unitTerm (i + m) (clamp01 (w (i + m))) t) atTop
      (nhds (fun w => tailSum m w t)) := by
    rw [tendsto_pi_nhds]
    intro w
    have hs := summable_unitTerm (clampU_mem w) t
    have hs' := (summable_nat_add_iff m).mpr hs
    exact hs'.hasSum.tendsto_sum_nat
  exact @measurable_of_tendsto_metrizable (ℕ → ℝ) ℝ mm _ _ _ _ _ _ hpart hlim

theorem measurableSet_tailEvent (m : ℕ) :
    MeasurableSet[⨆ i ≥ m, coordSigma i] (tailEvent m) := by
  have : tailEvent m = ⋂ M : ℕ, ⋂ n₀ : ℕ, ⋃ n : ℕ, ⋃ (_ : n₀ ≤ n),
      {u | (M : ℝ) + (1 / 2) * Real.log n ≤ tailSum m u n} := by
    ext u; simp [tailEvent]
  rw [this]
  refine MeasurableSet.iInter (fun M => MeasurableSet.iInter (fun n₀ =>
    MeasurableSet.iUnion (fun n => MeasurableSet.iUnion (fun _ => ?_))))
  exact measurableSet_le measurable_const (measurable_tailSum m n)

theorem measurableSet_excessEvent_tail :
    MeasurableSet[limsup coordSigma atTop] excessEvent := by
  rw [Filter.limsup_eq_iInf_iSup_of_nat]
  refine MeasurableSpace.measurableSet_iInf.mpr (fun m => ?_)
  rw [excessEvent_eq_tailEvent m]
  exact measurableSet_tailEvent m

/-! ### Infinitely many block events -/

/-- The probability lower bound `p₀ = 1/(8(C+1))`. -/
def blockProb : ℝ := 1 / (8 * (pairConst + 1))

theorem blockProb_pos : 0 < blockProb := by
  unfold blockProb; have := pairConst_pos; positivity

theorem block_hyp (j : ℕ) : 16 ≤ 2 ^ (j + 2000) ∧ 1328 ≤ Real.log ((2 ^ (j + 2000) : ℕ) : ℝ) := by
  constructor
  · calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (j + 2000) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · push_cast
    rw [Real.log_pow]
    have := Real.log_two_gt_d9
    have hj : (2000 : ℝ) ≤ ((j + 2000 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
    nlinarith

theorem measure_blockEvent_ge (j : ℕ) :
    ENNReal.ofReal blockProb ≤ cellLaw (blockEvent (2 ^ (j + 2000))) := by
  obtain ⟨h1, h2⟩ := block_hyp j
  rw [← ofReal_measureReal (μ := cellLaw) (s := blockEvent _)]
  exact ENNReal.ofReal_le_ofReal (measureReal_blockEvent_ge h1 h2)

/-- The union of the block events from index `J` on. -/
def blocksFrom (J : ℕ) : Set (ℕ → ℝ) := ⋃ j ≥ J, blockEvent (2 ^ (j + 2000))

theorem blocksFrom_antitone : Antitone blocksFrom := by
  intro J J' hJ u hu
  simp only [blocksFrom, Set.mem_iUnion] at hu ⊢
  obtain ⟨j, hj, hu⟩ := hu
  exact ⟨j, le_trans hJ hj, hu⟩

theorem measure_iInter_blocksFrom_ge :
    ENNReal.ofReal blockProb ≤ cellLaw (⋂ J, blocksFrom J) := by
  rw [blocksFrom_antitone.measure_iInter (fun J => (MeasurableSet.biUnion (Set.to_countable _)
    (fun j _ => measurableSet_blockEvent _)).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
  refine le_iInf (fun J => le_trans (measure_blockEvent_ge J) (measure_mono ?_))
  intro u hu
  simp only [blocksFrom, Set.mem_iUnion]
  exact ⟨J, le_rfl, hu⟩

theorem blockConst_pos : 0 < blockConst := by
  unfold blockConst
  have h8 : (1 : ℝ) ≤ 2 * markovConst := by
    unfold markovConst; linarith [pairConst_pos]
  have := Real.log_nonneg h8
  linarith

theorem iInter_blocksFrom_subset :
    (⋂ J, blocksFrom J) ∩ {u | ∀ k, u k ∈ Icc (0 : ℝ) 1} ⊆ excessEvent := by
  rintro u ⟨hu, hu01⟩
  simp only [Set.mem_setOf_eq] at hu01
  simp only [excessEvent, Set.mem_setOf_eq, clampU_of_mem hu01]
  intro M n₀
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlog2 : 0 < Real.log 2 := by linarith
  have hC := blockConst_pos
  obtain ⟨J, hJ⟩ := exists_nat_gt ((M + blockConst + 1) * 40 / 3 / Real.log 2 + n₀)
  have hJmem := Set.mem_iInter.mp hu J
  simp only [blocksFrom, Set.mem_iUnion] at hJmem
  obtain ⟨j, hj, hev⟩ := hJmem
  obtain ⟨h16, _⟩ := block_hyp j
  obtain ⟨n, hn1, hn2, hval⟩ := exists_unitSum_ge_of_blockEvent h16 hev hu01
  set b := j + 2000 with hb
  clear_value b
  have hq0 : 0 ≤ (M + blockConst + 1) * 40 / 3 / Real.log 2 := by
    apply div_nonneg _ hlog2.le
    have : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hJb : (J : ℝ) ≤ b := by exact_mod_cast (show J ≤ b by omega)
  have hbpow : (b : ℝ) ≤ ((2 ^ b : ℕ) : ℝ) := by exact_mod_cast (Nat.lt_two_pow_self).le
  have hn1r : ((2 ^ b : ℕ) : ℝ) ≤ n := by exact_mod_cast hn1
  refine ⟨n, ?_, ?_⟩
  · have : (n₀ : ℝ) ≤ n := by linarith
    exact_mod_cast this
  · have hpow : Real.log ((2 ^ b : ℕ) : ℝ) = b * Real.log 2 := by
      push_cast; rw [Real.log_pow]
    rw [hpow] at hval
    have hnpos : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hn1r
    have hnlt : (n : ℝ) < ((2 ^ (b + 1) : ℕ) : ℝ) := by
      exact_mod_cast (show n < 2 ^ (b + 1) by rw [pow_succ]; omega)
    have hlogn : Real.log n ≤ (b + 1) * Real.log 2 := by
      have := Real.log_le_log hnpos hnlt.le
      rwa [show ((2 ^ (b + 1) : ℕ) : ℝ) = 2 ^ (b + 1) by push_cast; ring, Real.log_pow,
        show ((b + 1 : ℕ) : ℝ) = (b : ℝ) + 1 by push_cast; ring] at this
    have hbig : (M + blockConst + 1) * 40 / 3 < b * Real.log 2 := by
      have h1 : (M + blockConst + 1) * 40 / 3 / Real.log 2 < b := by
        have : (0 : ℝ) ≤ n₀ := Nat.cast_nonneg n₀
        linarith
      rwa [div_lt_iff₀ hlog2] at h1
    linarith

/-- **The excess event is almost sure.** -/
theorem measure_excessEvent : cellLaw excessEvent = 1 := by
  rcases measure_zero_or_one_of_measurableSet_limsup_atTop coordSigma_le iIndep_coordSigma
    measurableSet_excessEvent_tail with h | h
  · exfalso
    have hgood : cellLaw {u : ℕ → ℝ | ∀ k, u k ∈ Icc (0 : ℝ) 1}ᶜ = 0 := by
      rw [Set.compl_setOf]
      exact ae_iff.mp ae_forall_mem_Icc
    have hle : cellLaw (⋂ J, blocksFrom J) ≤ cellLaw excessEvent := by
      calc cellLaw (⋂ J, blocksFrom J)
          = cellLaw ((⋂ J, blocksFrom J) ∩ {u | ∀ k, u k ∈ Icc (0 : ℝ) 1}) :=
            (measure_inter_conull hgood).symm
        _ ≤ cellLaw excessEvent := measure_mono iInter_blocksFrom_subset
    have := measure_iInter_blocksFrom_ge
    rw [h] at hle
    have hp : 0 < ENNReal.ofReal blockProb := ENNReal.ofReal_pos.mpr blockProb_pos
    exact absurd (lt_of_lt_of_le hp (this.trans hle)) (lt_irrefl 0)
  · exact h

/-- **Integer granularity is supercritical.** For one uniform atom of mass one in each unit cell of
`[1, ∞)` (minus the atom `e^{1/20000} δ_{e^{1/10000}}`), almost surely the Weil density
`2(archDensity t − cellSum 1 u t)` is negative at arbitrarily large heights: the random system is
almost surely not Weil-positive for the archimedean datum of `ζ`. -/
theorem ae_exists_archDensity_lt_cellSum_one :
    ∀ᵐ u ∂cellLaw, ∀ T₀ : ℝ, ∃ t : ℝ, T₀ ≤ t ∧ archDensity t < cellSum 1 u t := by
  have hmeas : MeasurableSet excessEvent := by
    have hle : limsup coordSigma atTop ≤ MeasurableSpace.pi := by
      rw [Filter.limsup_eq_iInf_iSup_of_nat]
      exact iInf_le_of_le 0 (iSup₂_le (fun i _ => coordSigma_le i))
    exact hle _ measurableSet_excessEvent_tail
  have hE : ∀ᵐ u ∂cellLaw, u ∈ excessEvent := by
    rw [ae_iff]
    have hc : cellLaw excessEventᶜ = 0 := (prob_compl_eq_zero_iff hmeas).mpr measure_excessEvent
    rw [← Set.compl_setOf] at *
    simpa [Set.compl_def] using hc
  filter_upwards [hE, ae_forall_mem_Icc] with u hEu hu01
  intro T₀
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge T₀
  obtain ⟨n, hn, hle⟩ := hEu 3 (max n₁ 4801)
  rw [clampU_of_mem hu01, unitSum_eq_cellSum] at hle
  have hn4801 : (4801 : ℝ) ≤ n := by exact_mod_cast le_trans (le_max_right _ _) hn
  refine ⟨n, le_trans hn₁ (by exact_mod_cast le_trans (le_max_left _ _) hn), ?_⟩
  have habs : |(n : ℝ)| = n := abs_of_nonneg (Nat.cast_nonneg n)
  have harch := archDensity_le_log (t := (n : ℝ)) (by rw [habs]; linarith)
  rw [habs] at harch
  push_cast at hle
  linarith

end RandomCellWeil
end RHTower
