import GaloisForLFunctions.HTGeometry.RamificationInformationChain
import GaloisForLFunctions.RHTower.HighExponentShellCriticalClock
import GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.MarkedEulerShellSkeleton

/-!
# Normalization-wall coercivity and relative properness of formation work

For `m ≥ 12` the shell series has a pole at `σ = 1` (`S_j(σ) = ζ(σ) H_j(σ)`, `H_j(1) > 0`), so
`S_j(σ) → +∞` as `σ ↓ 1`, while `S_m(rσ) → S_m(r) < ∞` by continuity of Dirichlet series on
`σ > 1`.  Hence, as `σ ↓ 1`,

`α_{m,r}(σ) → 0`, `β_{m,r}(σ) → 1`, `W_{m,r}(σ) → +∞`, `Aff → 0`, `TV → 1`;

and as `σ → +∞`, since `2^m` is the unique smallest element of `A_m` and `2^{rm} = (2^m)^r` the
unique smallest of `A_{rm}`, dominated convergence gives `α → 1`, `β → 0`, `W → 0`.  The work is
continuous on `(1, ∞)` and proper on every chart `(1, Σ]`: bounded work stays away from the wall.

Without parameter transport the composition law fails: `W_{m,sr}(σ) = W_{rm,s}(σ) + W_{m,r}(σ)`
for all `σ` would force `W_{m,r}(sσ) = W_{m,r}(σ)`, impossible as `σ ↓ 1`.  The inherited fibre at
the same temperature is not the source fibre: `P_{m,σ} ≠ P_{m,rσ}`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationExcess

open _root_.RHTower

variable {m r : ℕ}

/-! ### Continuity of Dirichlet series on `σ > 1` -/

section Continuity

variable {α : Type*} {f : α → ℕ} (hf : Function.Injective f) (hf2 : ∀ a, 2 ≤ f a)
include hf hf2

theorem continuousOn_dirichletSum {σ₀ : ℝ} (hσ₀ : 1 < σ₀) :
    ContinuousOn (dirichletSum f) (Ici σ₀) := by
  refine continuousOn_tsum (fun a => ?_) (summable_dirichlet hf hσ₀) fun a σ hσ => ?_
  · exact (continuous_const.rpow continuous_neg fun _ => Or.inl (pos_f hf2 a).ne').continuousOn
  · rw [Real.norm_of_nonneg (Real.rpow_nonneg (pos_f hf2 a).le _)]
    exact Real.rpow_le_rpow_of_exponent_le (by have := hf2 a; exact_mod_cast (by omega : 1 ≤ f a))
      (neg_le_neg hσ)

theorem continuousAt_dirichletSum {σ : ℝ} (hσ : 1 < σ) : ContinuousAt (dirichletSum f) σ := by
  have h := continuousOn_dirichletSum hf hf2 (σ₀ := (1 + σ) / 2) (by linarith)
  exact h.continuousAt (Ici_mem_nhds (by linarith))

end Continuity

theorem eulerShellSum_eq_dirichletSum (m : ℕ) :
    eulerShellSum m = dirichletSum (fun n : EulerShell m => (n : ℕ)) := rfl

theorem continuousAt_eulerShellSum (m : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    ContinuousAt (eulerShellSum m) σ := by
  rw [eulerShellSum_eq_dirichletSum]
  exact continuousAt_dirichletSum (shell_injective m) (shell_two_le m) hσ

/-! ### The pole at `σ = 1` -/

theorem eulerShellSum_eq_shellMellin (hm : 1 ≤ m) {σ : ℝ} (hσ : 1 < σ) :
    eulerShellSum m σ = shellMellin m σ := by
  rw [shellMellin_eq_tsum (by omega) hσ, eulerShellSum]
  change ∑' x : ({n : ℕ | 2 ≤ n ∧ shellIndicator m n = 1} : Set ℕ), ((x : ℕ) : ℝ) ^ (-σ) = _
  rw [tsum_subtype {n : ℕ | 2 ≤ n ∧ shellIndicator m n = 1} (fun n : ℕ => (n : ℝ) ^ (-σ))]
  refine tsum_congr fun n => ?_
  by_cases hn : 2 ≤ n ∧ shellIndicator m n = 1
  · rw [indicator_of_mem (show n ∈ {n : ℕ | 2 ≤ n ∧ shellIndicator m n = 1} from hn), hn.2,
      Int.cast_one, one_mul, Real.rpow_neg (Nat.cast_nonneg n)]
  · rw [indicator_of_notMem (show n ∉ {n : ℕ | 2 ≤ n ∧ shellIndicator m n = 1} from hn)]
    have h0 : shellIndicator m n = 0 := by
      rcases shellIndicator_eq_zero_or_one m n with h | h
      · exact h
      · exfalso
        apply hn
        refine ⟨?_, h⟩
        by_contra! hlt
        interval_cases n
        · simp at h
        · rw [HTGeometry.ConstraintFrameRelativity.shellIndicator_one (by omega)] at h
          exact absurd h (by norm_num)
    rw [h0, Int.cast_zero, zero_mul]

/-- **`(FE.40)`**: for `j ≥ 12`, `S_j(σ) → +∞` as `σ ↓ 1`. -/
theorem tendsto_eulerShellSum_atTop {j : ℕ} (hj : 12 ≤ j) :
    Tendsto (eulerShellSum j) (𝓝[>] 1) atTop := by
  have hres := tendsto_shellMellin_residue hj
  have hpos := shellResidue_pos (m := j) (by omega)
  have hinv : Tendsto (fun σ : ℝ => (σ - 1)⁻¹) (𝓝[>] 1) atTop := by
    have h1 : Tendsto (fun σ : ℝ => σ - 1) (𝓝[>] 1) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := (continuous_id.sub (continuous_const (y := (1 : ℝ)))).tendsto' (1 : ℝ) 0
          (by simp)
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with σ hσ
        exact sub_pos.2 (mem_Ioi.1 hσ)
    exact tendsto_inv_nhdsGT_zero.comp h1
  have hprod := hres.pos_mul_atTop hpos hinv
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have hσ' : (1 : ℝ) < σ := hσ
  rw [eulerShellSum_eq_shellMellin (by omega) hσ']
  field_simp [(sub_pos.2 hσ').ne']

/-! ### The boundary formation law at the normalization wall -/

section Wall

variable (hm : 12 ≤ m) (hr : 2 ≤ r)
include hm hr

theorem tendsto_survival_wall : Tendsto (survival m r) (𝓝[>] 1) (𝓝 0) := by
  have hrm : 12 ≤ r * m := by nlinarith
  have hnum : Tendsto (fun σ : ℝ => eulerShellSum m (r * σ)) (𝓝[>] 1)
      (𝓝 (eulerShellSum m (r * 1))) := by
    have hr1 : 1 < (r : ℝ) * 1 := by
      have : (2 : ℝ) ≤ r := by exact_mod_cast hr
      linarith
    exact ((continuousAt_eulerShellSum m hr1).tendsto.comp
      ((continuous_const.mul continuous_id).tendsto 1)).mono_left nhdsWithin_le_nhds
  exact hnum.div_atTop (tendsto_eulerShellSum_atTop hrm)

/-- **Theorem 7.1 `(FE.41)`**: as `σ ↓ 1`, `α → 0`, `β → 1`, `W → +∞`. -/
theorem wall_limits :
    Tendsto (survival m r) (𝓝[>] 1) (𝓝 0) ∧ Tendsto (excessFraction m r) (𝓝[>] 1) (𝓝 1) ∧
      Tendsto (formationWork m r) (𝓝[>] 1) atTop := by
  have hα := tendsto_survival_wall hm hr
  refine ⟨hα, ?_, ?_⟩
  · have h1 : Tendsto (fun σ => 1 - survival m r σ) (𝓝[>] 1) (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hα
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    linarith [survival_add_excessFraction (m := m) (by omega) hr hσ]
  · have hα' : Tendsto (survival m r) (𝓝[>] 1) (𝓝[>] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hα
        (by filter_upwards [self_mem_nhdsWithin] with σ hσ using
          survival_pos (m := m) (by omega) hr hσ)
    exact tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hα')

/-- **Theorem 7.1 `(FE.42)`**: as `σ ↓ 1`, `Aff(P_{rm,σ}, I) = √α → 0` and
`TV(P_{rm,σ}, I) = β → 1`. -/
theorem wall_affinity_tv :
    Tendsto (fun σ => Real.sqrt (survival m r σ)) (𝓝[>] 1) (𝓝 0) ∧
      Tendsto (excessFraction m r) (𝓝[>] 1) (𝓝 1) := by
  refine ⟨?_, (wall_limits hm hr).2.1⟩
  have := (Real.continuous_sqrt.tendsto 0).comp (tendsto_survival_wall hm hr)
  rw [Real.sqrt_zero] at this
  exact this

end Wall

/-! ### The low-temperature end -/

/-- The smallest element of `A_m` is `2^m`, and it is the only one of that size. -/
theorem two_pow_le_of_shell (n : EulerShell m) : 2 ^ m ≤ (n : ℕ) := by
  have h1 := (shellIndicator_eq_one_iff m n).1 n.2.2
  obtain ⟨-, hnot⟩ := h1
  simp only [MFree, not_forall, not_not] at hnot
  obtain ⟨p, hp, hdvd⟩ := hnot
  have hn0 : (n : ℕ) ≠ 0 := by have := n.2.1; omega
  exact (Nat.pow_le_pow_left hp.two_le m).trans (Nat.le_of_dvd (by omega) hdvd)

/-- The scaled shell sum `Σ_{n ∈ A_m} (n/2^m)^{-t}` tends to `1` as `t → ∞`. -/
theorem tendsto_scaled_shellSum (hm : 1 ≤ m) :
    Tendsto (fun t : ℝ => ((2 : ℝ) ^ m) ^ t * eulerShellSum m t) atTop (𝓝 1) := by
  set a₀ : EulerShell m := ⟨2 ^ m, Nat.one_lt_two_pow (by omega), shellIndicator_two_pow m⟩
  have hM : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hpos : ∀ n : EulerShell m, (0 : ℝ) < (n : ℕ) := fun n => by
    exact_mod_cast (show 0 < (n : ℕ) by have := n.2.1; omega)
  set F : ℝ → EulerShell m → ℝ := fun t n => ((((n : ℕ) : ℝ) / (2 : ℝ) ^ m)⁻¹) ^ t
  have hF : ∀ (t : ℝ) (n : EulerShell m), ((2 : ℝ) ^ m) ^ t * ((n : ℕ) : ℝ) ^ (-t) = F t n :=
    fun t n => by
    simp only [F]
    rw [inv_div, Real.div_rpow hM.le (hpos n).le, Real.rpow_neg (hpos n).le, div_eq_mul_inv]
  have hratio : ∀ n : EulerShell m, 1 ≤ ((n : ℕ) : ℝ) / (2 : ℝ) ^ m := fun n => by
    rw [one_le_div hM]
    exact_mod_cast two_pow_le_of_shell n
  have hlim : ∀ n, Tendsto (fun t => F t n) atTop (𝓝 (if n = a₀ then 1 else 0)) := fun n => by
    split_ifs with h
    · subst h
      simp only [F, a₀]
      push_cast
      simp
    · have hlt : 1 < ((n : ℕ) : ℝ) / (2 : ℝ) ^ m := by
        rcases (hratio n).lt_or_eq with h' | h'
        · exact h'
        · exfalso
          apply h
          apply Subtype.ext
          have : ((n : ℕ) : ℝ) = (2 : ℝ) ^ m := (div_eq_one_iff_eq hM.ne').1 h'.symm
          exact_mod_cast this
      have hq := inv_pos.2 (div_pos (hpos n) hM)
      exact tendsto_rpow_atTop_of_base_lt_one _ (by linarith) (inv_lt_one_of_one_lt₀ hlt)
  have hbound : ∀ᶠ t in atTop, ∀ n, ‖F t n‖ ≤ F 2 n := by
    filter_upwards [eventually_ge_atTop 2] with t ht n
    simp only [F]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (inv_pos.2 (div_pos (hpos n) hM)).le _)]
    exact Real.rpow_le_rpow_of_exponent_ge (inv_pos.2 (div_pos (hpos n) hM))
      (inv_le_one_of_one_le₀ (hratio n)) ht
  have hsum : Summable (F 2) := by
    refine ((summable_shell m (σ := 2) (by norm_num)).mul_left (((2 : ℝ) ^ m) ^ (2 : ℝ))).congr
      fun n => hF 2 n
  have h := tendsto_tsum_of_dominated_convergence hsum hlim hbound
  rw [tsum_ite_eq] at h
  refine h.congr fun t => ?_
  rw [eulerShellSum, ← tsum_mul_left]
  exact tsum_congr fun n => (hF t n).symm

/-- **Theorem 7.1 `(FE.43)`**: as `σ → +∞`, `α → 1`, `β → 0`, `W → 0`. -/
theorem lowTemperature_limits (hm : 1 ≤ m) (hr : 2 ≤ r) :
    Tendsto (survival m r) atTop (𝓝 1) ∧ Tendsto (excessFraction m r) atTop (𝓝 0) ∧
      Tendsto (formationWork m r) atTop (𝓝 0) := by
  have hrm : 1 ≤ r * m := one_le_mul_m hm hr
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hnum := (tendsto_scaled_shellSum hm).comp
    (tendsto_id.const_mul_atTop hr0 : Tendsto (fun σ : ℝ => (r : ℝ) * σ) atTop atTop)
  have hden := tendsto_scaled_shellSum hrm
  have hα : Tendsto (survival m r) atTop (𝓝 1) := by
    have := hnum.div hden one_ne_zero
    rw [div_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with σ hσ
    have hS := eulerShellSum_pos hrm hσ
    have hscale : ((2 : ℝ) ^ m) ^ ((r : ℝ) * σ) = ((2 : ℝ) ^ (r * m)) ^ σ := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      ring
    have hS' := eulerShellSum_pos hm (one_lt_mul_of_two_le hr hσ)
    simp only [Pi.div_apply, Function.comp_apply, survival]
    rw [hscale]
    have hpow : (0 : ℝ) < ((2 : ℝ) ^ (r * m)) ^ σ := by positivity
    field_simp
  refine ⟨hα, ?_, ?_⟩
  · have h1 : Tendsto (fun σ => 1 - survival m r σ) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hα
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with σ hσ
    linarith [survival_add_excessFraction hm hr hσ]
  · have := ((Real.continuousAt_log one_ne_zero).tendsto.comp hα).neg
    rw [Real.log_one, neg_zero] at this
    exact this

/-! ### Relative properness of the normalization wall -/

theorem continuousOn_formationWork (hm : 1 ≤ m) (hr : 2 ≤ r) :
    ContinuousOn (formationWork m r) (Ioi 1) := by
  intro σ hσ
  have hσ' : (1 : ℝ) < σ := hσ
  have hrσ := one_lt_mul_of_two_le hr hσ'
  have h1 := continuousAt_eulerShellSum m hrσ
  have h2 := continuousAt_eulerShellSum (r * m) hσ'
  have hc : ContinuousAt (fun σ : ℝ => eulerShellSum m (r * σ)) σ :=
    h1.comp (continuous_const.mul continuous_id).continuousAt
  have hα : ContinuousAt (survival m r) σ :=
    hc.div h2 (eulerShellSum_pos (one_le_mul_m hm hr) hσ').ne'
  exact (((Real.continuousAt_log (survival_pos hm hr hσ').ne').comp hα).neg).continuousWithinAt

/-- **Corollary 7.2 (relative properness)**: on `(1, Σ]` bounded work stays a positive distance
from the wall `σ = 1`. -/
theorem work_bounded_away (hm : 12 ≤ m) (hr : 2 ≤ r) (B : ℝ) :
    ∃ ε > 0, ∀ σ, 1 < σ → formationWork m r σ ≤ B → 1 + ε ≤ σ := by
  have h := ((wall_limits hm hr).2.2).eventually (eventually_gt_atTop B)
  obtain ⟨U, hU, hUB⟩ := Filter.eventually_iff_exists_mem.1 h
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhdsWithin_iff.1 hU
  refine ⟨ε / 2, by positivity, fun σ hσ hWσ => ?_⟩
  by_contra! hlt
  have hmem : σ ∈ Metric.ball 1 ε ∩ Ioi 1 := by
    refine ⟨?_, hσ⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
    linarith
  exact absurd hWσ (not_le.2 (hUB σ (hεU hmem)))

/-- **Corollary 7.2 (properness)**: the preimage in `(1, T]` of a compact set of works is
compact. -/
theorem work_isCompact_preimage (hm : 12 ≤ m) (hr : 2 ≤ r) (T : ℝ) {K : Set ℝ}
    (hK : IsCompact K) : IsCompact {σ | σ ∈ Ioc 1 T ∧ formationWork m r σ ∈ K} := by
  obtain ⟨B, hB⟩ := hK.isBounded.bddAbove
  obtain ⟨ε, hε, hεB⟩ := work_bounded_away hm hr B
  have hsub : {σ | σ ∈ Ioc 1 T ∧ formationWork m r σ ∈ K} =
      Icc (1 + ε) T ∩ formationWork m r ⁻¹' K := by
    ext σ
    simp only [mem_setOf_eq, mem_Ioc, mem_Icc, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨hεB σ h1 (hB h3), h2⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, h2⟩, h3⟩
  rw [hsub]
  have hcont : ContinuousOn (formationWork m r) (Icc (1 + ε) T) :=
    (continuousOn_formationWork (by omega) hr).mono fun σ hσ => by
      simp only [mem_Ioi]; linarith [hσ.1]
  exact isCompact_Icc.of_isClosed_subset
    (hcont.preimage_isClosed_of_isClosed isClosed_Icc hK.isClosed) inter_subset_left

/-! ### Hostile conjecture loops -/

/-- **Loop 4**: without parameter transport the composition law fails: the unshifted identity
`W_{m,sr}(σ) = W_{rm,s}(σ) + W_{m,r}(σ)` does not hold for all `σ > 1`. -/
theorem not_unshifted_additivity {s : ℕ} (hm : 12 ≤ m) (hr : 2 ≤ r) (hs : 2 ≤ s) :
    ¬ ∀ σ, 1 < σ →
      formationWork m (s * r) σ = formationWork (r * m) s σ + formationWork m r σ := by
  intro h
  have hs1 : (1 : ℝ) < s * 1 := by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith
  -- shifted: `W_{m,r}(sσ) = W_{m,r}(σ)` near the wall
  have heq : ∀ σ, 1 < σ → formationWork m r ((s : ℝ) * σ) = formationWork m r σ := fun σ hσ => by
    have h1 := work_comp (m := m) (by omega) hr hs hσ
    have h2 := h σ hσ
    linarith
  -- `W_{m,r}(sσ) → W_{m,r}(s)` while `W_{m,r}(σ) → ∞`
  have hc : Tendsto (fun σ : ℝ => formationWork m r ((s : ℝ) * σ)) (𝓝[>] 1)
      (𝓝 (formationWork m r ((s : ℝ) * 1))) :=
    ((continuousOn_formationWork (by omega) hr).continuousAt (Ioi_mem_nhds hs1)).tendsto.comp
      ((continuous_const.mul continuous_id).tendsto 1) |>.mono_left nhdsWithin_le_nhds
  have hinf := (wall_limits hm hr).2.2
  have hinf' : Tendsto (fun σ : ℝ => formationWork m r ((s : ℝ) * σ)) (𝓝[>] 1) atTop :=
    hinf.congr' (by filter_upwards [self_mem_nhdsWithin] with σ hσ using (heq σ hσ).symm)
  exact not_tendsto_nhds_of_tendsto_atTop hinf' _ hc

/-- **Loop 2**: the inherited fibre at the same temperature is not the source fibre:
`P_{m,σ} ≠ P_{m,rσ}`. -/
theorem shellProb_ne_of_two_le (hm : 1 ≤ m) (hr : 2 ≤ r) {σ : ℝ} (hσ : 1 < σ) :
    shellProb m σ ≠ shellProb m (r * σ) := by
  intro h
  haveI := nonempty_shell hm
  have hrσ := one_lt_mul_of_two_le hr hσ
  set a : EulerShell m := ⟨2 ^ m, Nat.one_lt_two_pow (by omega), shellIndicator_two_pow m⟩
  set b : EulerShell m := ⟨3 ^ m, by
    have : 3 ≤ 3 ^ m := Nat.le_self_pow (by omega) 3
    omega, HTGeometry.ConstraintMotiveRelativity.shellIndicator_prime_pow Nat.prime_three m⟩
  have hpa : (0 : ℝ) < (a : ℕ) := by simp [a]
  have hpb : (0 : ℝ) < (b : ℕ) := by simp [b]
  have hS := eulerShellSum_pos hm hσ
  have hS' := eulerShellSum_pos hm hrσ
  have ha := congrFun h a
  have hb := congrFun h b
  rw [shellProb_eq, shellProb_eq] at ha hb
  have e : (((a : ℕ) : ℝ) ^ (-σ) / eulerShellSum m σ) / (((b : ℕ) : ℝ) ^ (-σ) / eulerShellSum m σ) =
      (((a : ℕ) : ℝ) ^ (-(r * σ)) / eulerShellSum m (r * σ)) /
        (((b : ℕ) : ℝ) ^ (-(r * σ)) / eulerShellSum m (r * σ)) := by rw [ha, hb]
  rw [div_div_div_cancel_right₀ hS.ne', div_div_div_cancel_right₀ hS'.ne',
    ← Real.div_rpow hpa.le hpb.le, ← Real.div_rpow hpa.le hpb.le] at e
  have hq0 : 0 < ((a : ℕ) : ℝ) / (b : ℕ) := div_pos hpa hpb
  have hq : ((a : ℕ) : ℝ) / (b : ℕ) < 1 := by
    rw [div_lt_one hpb]
    simp only [a, b]
    push_cast
    exact pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  have hlog := congrArg Real.log e
  rw [Real.log_rpow hq0, Real.log_rpow hq0] at hlog
  have hl : Real.log (((a : ℕ) : ℝ) / (b : ℕ)) ≠ 0 := (Real.log_neg hq0 hq).ne
  have hexp := mul_right_cancel₀ hl hlog
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  nlinarith

end GaloisForLFunctions.HTGeometry.FormationExcess
