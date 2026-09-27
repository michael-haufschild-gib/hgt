import GaloisForLFunctions.RHTower.STCSourceWorkGradeDuality
import GaloisForLFunctions.RHTower.FrankensteinSourceTailSoninGaussianWronskianBridge
import GaloisForLFunctions.RHTower.XiPrimeSeamReflectionEnergy
import GaloisForLFunctions.RHTower.STCPrimeSquarePositivityWall
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Source phase work versus prime-seam energy: grade duality and edge costs

The complete-source/Sonin phase work at horizontal grade `t ∈ (0,1)` is
`W(t) = c t²(1-t²)/(1+t²)²`, `c = (log 2)²/4`; the canonical all-prime seam has reciprocal-prime
energy `E(t) = Σ_p (log p)²/p² (p^t + p^{-t} - 2) = 4 Σ_p (log p)²/p² sinh²(t log p/2)`.

* `W` is invariant under the grade involution `t ↦ t* = √((1-t²)/(1+3t²))`, whose only fixed
  point in `(0,1)` is `1/√3`, while `E` is strictly increasing.  Hence no function `Φ` satisfies
  `E = Φ ∘ W` on `(0,1)`.
* As `t → 0+`: `t* → 1-`, `E(t) → 0`, `E(t*) → ∞` and `W(t*) = W(t) → 0`; no comparison
  `E ≤ Φ(W)` with `Φ` bounded near zero holds.
* Outer edge: `E(1-δ) = F(δ) - 2F(1) + F(2-δ)` with `F(u) = Σ (log p)² p^{-1-u}`,
  `F(δ) - δ^{-2}` converges, `δ² E(1-δ) → 1`, `W(1-δ)/δ → (log 2)²/8`, and
  `δ³ E(1-δ)/W(1-δ) → 8/(log 2)²`.
* The chronological slope `W'(t) = 2c t(1-3t²)/(1+t²)³` resolves the two branches: the pair
  `(W(t), sign W'(t))` determines `t ∈ (0,1)`.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-! ### Source work and grade duality -/

/-- Complete-source/Sonin phase work at horizontal grade `t`. -/
def stcSourceWork (t : ℝ) : ℝ := Real.log 2 ^ 2 / 4 * stcWorkShape (t ^ 2)

theorem stcSourceWork_eq (t : ℝ) :
    stcSourceWork t = Real.log 2 ^ 2 / 4 * t ^ 2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2 := by
  unfold stcSourceWork stcWorkShape
  ring

/-- The actual complete-source/Sonin work at a Xi-divisor copy is `W` at its centered rate. -/
theorem sourceTailSoninPhaseWork_eq_stcSourceWork (q : XiZeroCopy) :
    sourceTailSoninPhaseWork q = (stcSourceWork (primeDepthBVWoldXiCenteredRate q.1) : ℂ) := by
  rw [sourceTailSoninPhaseWork_eq_shape]
  rfl

theorem stcSourceWork_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : 0 < stcSourceWork t := by
  rw [stcSourceWork_eq]
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht2 : t ^ 2 < 1 := by nlinarith
  have : 0 < 1 - t ^ 2 := by linarith
  positivity

theorem stcWorkDual_mem {s : ℝ} (h0 : 0 < s) (h1 : s < 1) :
    0 < stcWorkDual s ∧ stcWorkDual s < 1 := by
  unfold stcWorkDual
  have hd : 0 < 1 + 3 * s := by linarith
  constructor
  · exact div_pos (by linarith) hd
  · rw [div_lt_one hd]; linarith

theorem stcWorkDual_eq_self_iff {s : ℝ} (hs : 0 ≤ s) : stcWorkDual s = s ↔ s = 1 / 3 := by
  unfold stcWorkDual
  have hd : 0 < 1 + 3 * s := by linarith
  rw [div_eq_iff hd.ne']
  constructor
  · intro h
    have : (3 * s - 1) * (s + 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · linarith
  · intro h; subst h; norm_num

/-- The dual grade `t* = √((1-t²)/(1+3t²))`. -/
def stcDualGrade (t : ℝ) : ℝ := Real.sqrt (stcWorkDual (t ^ 2))

theorem stcDualGrade_sq {t : ℝ} (h1 : t ^ 2 ≤ 1) : stcDualGrade t ^ 2 = stcWorkDual (t ^ 2) := by
  unfold stcDualGrade
  rw [Real.sq_sqrt]
  unfold stcWorkDual
  exact div_nonneg (by linarith) (by positivity)

theorem stcDualGrade_mem {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    0 < stcDualGrade t ∧ stcDualGrade t < 1 := by
  have hs0 : 0 < t ^ 2 := by positivity
  have hs1 : t ^ 2 < 1 := by nlinarith
  obtain ⟨hj0, hj1⟩ := stcWorkDual_mem hs0 hs1
  refine ⟨Real.sqrt_pos.mpr hj0, ?_⟩
  unfold stcDualGrade
  rw [Real.sqrt_lt' one_pos]
  simpa using hj1

theorem stcSourceWork_dualGrade {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    stcSourceWork (stcDualGrade t) = stcSourceWork t := by
  unfold stcSourceWork
  rw [stcDualGrade_sq (by nlinarith), stcWorkShape_dual _ (sq_nonneg t)]

theorem stcDualGrade_involutive {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    stcDualGrade (stcDualGrade t) = t := by
  have h2 : stcDualGrade t ^ 2 = stcWorkDual (t ^ 2) := stcDualGrade_sq (by nlinarith)
  show Real.sqrt (stcWorkDual (stcDualGrade t ^ 2)) = t
  rw [h2, stcWorkDual_involutive _ (sq_nonneg t), Real.sqrt_sq h0.le]

/-- The dual grade coincides with `t` exactly at `t = 1/√3`. -/
theorem stcDualGrade_eq_self_iff {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    stcDualGrade t = t ↔ t = Real.sqrt (1 / 3) := by
  have hm := stcDualGrade_mem h0 h1
  constructor
  · intro h
    have hsq : stcWorkDual (t ^ 2) = t ^ 2 := by
      rw [← stcDualGrade_sq (by nlinarith), h]
    have := (stcWorkDual_eq_self_iff (sq_nonneg t)).mp hsq
    rw [← this, Real.sqrt_sq h0.le]
  · intro h
    have ht2 : t ^ 2 = 1 / 3 := by rw [h, Real.sq_sqrt (by norm_num)]
    unfold stcDualGrade
    rw [ht2, (stcWorkDual_eq_self_iff (by norm_num)).mpr rfl, ← ht2, Real.sqrt_sq h0.le]

/-! ### Seam energy -/

/-- Reciprocal-prime seam energy density at horizontal grade `t`. -/
def stcSeamEnergyTerm (t : ℝ) (p : Nat.Primes) : ℝ :=
  4 * Real.log (p : ℝ) ^ 2 * (p : ℝ) ^ (-2 : ℝ) * Real.sinh (t * Real.log (p : ℝ) / 2) ^ 2

/-- One-particle reciprocal-prime energy of the canonical all-prime seam. -/
def stcSeamEnergy (t : ℝ) : ℝ := ∑' p : Nat.Primes, stcSeamEnergyTerm t p

theorem stcSeamEnergyTerm_nonneg (t : ℝ) (p : Nat.Primes) : 0 ≤ stcSeamEnergyTerm t p := by
  unfold stcSeamEnergyTerm
  have : 0 ≤ (p : ℝ) ^ (-2 : ℝ) := Real.rpow_nonneg (by positivity) _
  positivity

/-- Exponential form `(log p)²/p² (p^t + p^{-t} - 2)`. -/
theorem stcSeamEnergyTerm_eq_rpow (t : ℝ) (p : Nat.Primes) :
    stcSeamEnergyTerm t p =
      Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2 * ((p : ℝ) ^ t + (p : ℝ) ^ (-t) - 2) := by
  have hp : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  unfold stcSeamEnergyTerm
  set x := t * Real.log (p : ℝ) / 2 with hxdef
  have hpt : (p : ℝ) ^ t = Real.exp x ^ 2 := by
    rw [Real.rpow_def_of_pos hp, ← Real.exp_nat_mul, hxdef]; congr 1; push_cast; ring
  have hpmt : (p : ℝ) ^ (-t) = Real.exp (-x) ^ 2 := by
    rw [Real.rpow_def_of_pos hp, ← Real.exp_nat_mul, hxdef]; congr 1; push_cast; ring
  have hp2 : (p : ℝ) ^ (-2 : ℝ) = ((p : ℝ) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hp.le]; norm_cast
  have hprod : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  have key : ((Real.exp x - Real.exp (-x)) / 2) ^ 2 * 4 =
      Real.exp x ^ 2 + Real.exp (-x) ^ 2 - 2 := by linear_combination (-2 : ℝ) * hprod
  rw [hpt, hpmt, hp2, Real.sinh_eq, ← key, div_eq_mul_inv (Real.log (p : ℝ) ^ 2)]
  ring

theorem stcSeamEnergy_eq_rpow (t : ℝ) :
    stcSeamEnergy t = ∑' p : Nat.Primes,
      Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2 * ((p : ℝ) ^ t + (p : ℝ) ^ (-t) - 2) :=
  tsum_congr (stcSeamEnergyTerm_eq_rpow t)

/-- The density is the canonical seam charge square at `ρ = (1+t)/2 + iγ`, any ordinate `γ`. -/
theorem stcSeamEnergyTerm_eq_orbitwise (t γ : ℝ) (p : Nat.Primes) :
    stcSeamEnergyTerm t p =
      ‖orbitwiseNatPrimeSeamCharge (p : ℕ) ⟨(1 + t) / 2, γ⟩‖ ^ 2 / (p : ℝ) := by
  rw [orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_sinh]
  unfold stcSeamEnergyTerm
  congr 3
  ring

/-- The seam energy is the existing canonical one-particle seam energy, independent of height. -/
theorem stcSeamEnergy_eq_orbitwise (t γ : ℝ) :
    stcSeamEnergy t = orbitwisePrimeSeamWeightedNormSq ⟨(1 + t) / 2, γ⟩ :=
  tsum_congr (stcSeamEnergyTerm_eq_orbitwise t γ)

theorem summable_stcSeamEnergyTerm {t : ℝ} (ht : |t| < 1) :
    Summable (stcSeamEnergyTerm t) := by
  have hstrip : 0 < (⟨(1 + t) / 2, 0⟩ : ℂ).re ∧ (⟨(1 + t) / 2, 0⟩ : ℂ).re < 1 := by
    have := abs_lt.mp ht
    constructor <;> simp <;> linarith
  refine (summable_orbitwisePrimeSeam_weighted_norm_sq hstrip).congr fun p => ?_
  exact (stcSeamEnergyTerm_eq_orbitwise t 0 p).symm

theorem stcSeamEnergyTerm_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (p : Nat.Primes) :
    stcSeamEnergyTerm s p ≤ stcSeamEnergyTerm t p := by
  unfold stcSeamEnergyTerm
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast p.property.one_lt.le)
  have hA : 0 ≤ Real.sinh (s * Real.log (p : ℝ) / 2) :=
    Real.sinh_nonneg_iff.mpr (by positivity)
  have hB : Real.sinh (s * Real.log (p : ℝ) / 2) ≤ Real.sinh (t * Real.log (p : ℝ) / 2) :=
    Real.sinh_le_sinh.mpr (by nlinarith)
  have hc : 0 ≤ 4 * Real.log (p : ℝ) ^ 2 * (p : ℝ) ^ (-2 : ℝ) := by
    have : 0 ≤ (p : ℝ) ^ (-2 : ℝ) := Real.rpow_nonneg (by positivity) _
    positivity
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hA hB 2) hc

/-- **Strict monotonicity of the seam energy** on `[0,1)`. -/
theorem stcSeamEnergy_strictMonoOn : StrictMonoOn stcSeamEnergy (Set.Ico 0 1) := by
  intro s hs t ht hst
  have hs1 : |s| < 1 := abs_lt.mpr ⟨by linarith [hs.1], hs.2⟩
  have ht1 : |t| < 1 := abs_lt.mpr ⟨by linarith [ht.1, hs.1], ht.2⟩
  let two : Nat.Primes := ⟨2, Nat.prime_two⟩
  have hstrict : stcSeamEnergyTerm s two < stcSeamEnergyTerm t two := by
    unfold stcSeamEnergyTerm
    have hlog : 0 < Real.log ((two : ℕ) : ℝ) := Real.log_pos (by norm_num [two])
    have hA : 0 ≤ Real.sinh (s * Real.log ((two : ℕ) : ℝ) / 2) :=
      Real.sinh_nonneg_iff.mpr (by have := hs.1; positivity)
    have hB : Real.sinh (s * Real.log ((two : ℕ) : ℝ) / 2) <
        Real.sinh (t * Real.log ((two : ℕ) : ℝ) / 2) :=
      Real.sinh_lt_sinh.mpr (div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hst hlog) two_pos)
    have hc : 0 < 4 * Real.log ((two : ℕ) : ℝ) ^ 2 * ((two : ℕ) : ℝ) ^ (-2 : ℝ) := by
      have : 0 < ((two : ℕ) : ℝ) ^ (-2 : ℝ) := Real.rpow_pos_of_pos (by norm_num [two]) _
      positivity
    exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hB hA two_ne_zero) hc
  exact Summable.tsum_lt_tsum (fun p => stcSeamEnergyTerm_mono hs.1 hst.le p) hstrict
    (summable_stcSeamEnergyTerm hs1) (summable_stcSeamEnergyTerm ht1)

/-- **No factorization through the work.** No function `Φ` satisfies `E(t) = Φ(W(t))` for every
pre-divisor grade `0 < t < 1`. -/
theorem not_exists_stcSeamEnergy_factor_through_work :
    ¬ ∃ Φ : ℝ → ℝ, ∀ t : ℝ, 0 < t → t < 1 → stcSeamEnergy t = Φ (stcSourceWork t) := by
  rintro ⟨Φ, hΦ⟩
  have h0 : (0 : ℝ) < 1 / 2 := by norm_num
  have h1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨hd0, hd1⟩ := stcDualGrade_mem h0 h1
  have hne : stcDualGrade (1 / 2) ≠ 1 / 2 := by
    intro h
    have := (stcDualGrade_eq_self_iff h0 h1).mp h
    have hsq : (1 / 2 : ℝ) ^ 2 = 1 / 3 := by rw [this, Real.sq_sqrt (by norm_num)]
    norm_num at hsq
  have hE : stcSeamEnergy (stcDualGrade (1 / 2)) = stcSeamEnergy (1 / 2) := by
    rw [hΦ _ hd0 hd1, hΦ _ h0 h1, stcSourceWork_dualGrade h0 h1]
  exact hne (stcSeamEnergy_strictMonoOn.injOn ⟨hd0.le, hd1⟩ ⟨h0.le, h1⟩ hE)

/-! ### The two ends of the duality -/

theorem stcSeamEnergy_zero : stcSeamEnergy 0 = 0 := by
  simp [stcSeamEnergy, stcSeamEnergyTerm]

/-- `E(t) → 0` as `t → 0+`. -/
theorem tendsto_stcSeamEnergy_zero : Tendsto stcSeamEnergy (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun t p => stcSeamEnergyTerm t p) (g := fun p => stcSeamEnergyTerm 0 p)
    (bound := stcSeamEnergyTerm (1 / 2))
    (summable_stcSeamEnergyTerm (by norm_num)) (fun p => ?_) ?_
  · have h0 : ∑' p : Nat.Primes, stcSeamEnergyTerm 0 p = 0 := by simp [stcSeamEnergyTerm]
    rw [h0] at h
    exact h
  · have hc : Continuous fun t : ℝ => stcSeamEnergyTerm t p := by
      unfold stcSeamEnergyTerm; fun_prop
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · have hI : Set.Ioo (0 : ℝ) (1 / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hI] with t ht p
    rw [Real.norm_eq_abs, abs_of_nonneg (stcSeamEnergyTerm_nonneg t p)]
    exact stcSeamEnergyTerm_mono ht.1.le ht.2.le p

private theorem not_summable_stcSeamEnergyTerm_one : ¬ Summable (stcSeamEnergyTerm 1) := by
  intro hs
  apply Nat.Primes.not_summable_one_div
  refine Summable.of_norm_bounded_eventually (hs.mul_left 3) ?_
  have hfin : {p : Nat.Primes | (p : ℕ) ≤ 2}.Finite :=
    (Set.finite_le_nat 2).preimage Subtype.val_injective.injOn
  filter_upwards [hfin.compl_mem_cofinite] with p hp
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hp
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog : 1 ≤ Real.log (p : ℝ) := by
    rw [Real.le_log_iff_exp_le hp0]
    linarith [Real.exp_one_lt_d9]
  rw [Real.norm_eq_abs, abs_of_pos (by positivity), stcSeamEnergyTerm_eq_rpow,
    Real.rpow_one, Real.rpow_neg_one]
  have hinv : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hp0
  have hsq : 1 ≤ Real.log (p : ℝ) ^ 2 := by nlinarith
  have key : (p : ℝ) ≤ 3 * (Real.log (p : ℝ) ^ 2 * ((p : ℝ) + (p : ℝ)⁻¹ - 2)) := by
    have hq : (0 : ℝ) ≤ (p : ℝ) + (p : ℝ)⁻¹ - 2 := by linarith
    nlinarith
  have heq : 3 * (Real.log (p : ℝ) ^ 2 / (p : ℝ) ^ 2 * ((p : ℝ) + (p : ℝ)⁻¹ - 2)) =
      3 * (Real.log (p : ℝ) ^ 2 * ((p : ℝ) + (p : ℝ)⁻¹ - 2)) / (p : ℝ) / (p : ℝ) := by
    field_simp
  rw [heq, div_div, div_le_div_iff₀ hp0 (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_right key hp0.le]

/-- `E(t) → +∞` as `t → 1-`. -/
theorem tendsto_stcSeamEnergy_one : Tendsto stcSeamEnergy (𝓝[<] 1) atTop := by
  rw [tendsto_atTop]
  intro M
  have hnon := not_summable_stcSeamEnergyTerm_one
  have hex : ∃ u : Finset Nat.Primes, M < ∑ p ∈ u, stcSeamEnergyTerm 1 p := by
    by_contra h
    push Not at h
    exact hnon (summable_of_sum_le (fun p => stcSeamEnergyTerm_nonneg 1 p) h)
  obtain ⟨u, hu⟩ := hex
  have hcont : Continuous fun t : ℝ => ∑ p ∈ u, stcSeamEnergyTerm t p := by
    unfold stcSeamEnergyTerm; fun_prop
  have hev : ∀ᶠ t in 𝓝[<] (1 : ℝ), M < ∑ p ∈ u, stcSeamEnergyTerm t p :=
    (hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds hu)
  have hI : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[<] (1 : ℝ) := Ioo_mem_nhdsLT (by norm_num)
  filter_upwards [hev, hI] with t ht htI
  have hsum := summable_stcSeamEnergyTerm (abs_lt.mpr ⟨by linarith [htI.1], htI.2⟩)
  exact ht.le.trans (hsum.sum_le_tsum u fun p _ => stcSeamEnergyTerm_nonneg t p)

theorem tendsto_stcDualGrade_zero : Tendsto stcDualGrade (𝓝[>] 0) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hc : ContinuousAt stcDualGrade 0 := by
      unfold stcDualGrade stcWorkDual
      refine Real.continuous_sqrt.continuousAt.comp ?_
      exact ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
    have : stcDualGrade 0 = 1 := by simp [stcDualGrade, stcWorkDual]
    rw [← this]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  · have hI : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [hI] with t ht
    exact (stcDualGrade_mem ht.1 ht.2).2

theorem tendsto_stcSourceWork_zero : Tendsto stcSourceWork (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous stcSourceWork := by
    unfold stcSourceWork stcWorkShape
    refine continuous_const.mul (Continuous.div (by fun_prop) (by fun_prop) fun x => ?_)
    positivity
  have h0 : stcSourceWork 0 = 0 := by simp [stcSourceWork, stcWorkShape]
  have h := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  rwa [h0] at h

/-- **Unbounded mismatch at the ends of the duality.** Along `t → 0+`, the dual grade has the
same vanishing work but divergent seam energy. -/
theorem tendsto_stcSeamEnergy_dualGrade : Tendsto (fun t => stcSeamEnergy (stcDualGrade t))
    (𝓝[>] 0) atTop :=
  tendsto_stcSeamEnergy_one.comp tendsto_stcDualGrade_zero

/-- **No comparison `E ≤ Φ(W)` with `Φ` bounded near zero** holds over the whole strip. -/
theorem no_bounded_stcSourceWork_comparison :
    ¬ ∃ Φ : ℝ → ℝ, (∃ δ > 0, ∃ M : ℝ, ∀ w, 0 < w → w < δ → Φ w ≤ M) ∧
      ∀ t : ℝ, 0 < t → t < 1 → stcSeamEnergy t ≤ Φ (stcSourceWork t) := by
  rintro ⟨Φ, ⟨δ, hδ, M, hM⟩, hcomp⟩
  have hI : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  obtain ⟨t, htE, htW, htI⟩ := ((tendsto_stcSeamEnergy_dualGrade.eventually_gt_atTop M).and
    ((tendsto_stcSourceWork_zero.eventually (gt_mem_nhds hδ)).and hI)).exists
  obtain ⟨hd0, hd1⟩ := stcDualGrade_mem htI.1 htI.2
  have hW : stcSourceWork (stcDualGrade t) = stcSourceWork t := stcSourceWork_dualGrade htI.1 htI.2
  have h1 := hcomp _ hd0 hd1
  rw [hW] at h1
  have h2 := hM _ (stcSourceWork_pos htI.1 htI.2) htW
  linarith

/-! ### Sharp outer-edge transport cost -/

/-- `(5)`: `E(1-δ) = F(δ) - 2F(1) + F(2-δ)` with `F(u) = Σ_p (log p)² p^{-1-u}`. -/
theorem stcSeamEnergy_one_sub {δ : ℝ} (h0 : 0 < δ) (h2 : δ < 2) :
    stcSeamEnergy (1 - δ) =
      primeLogSquareMoment (1 + δ) - 2 * primeLogSquareMoment 2 + primeLogSquareMoment (3 - δ) := by
  rw [stcSeamEnergy_eq_orbitwise (1 - δ) 0,
    orbitwisePrimeSeamWeightedNormSq_eq_primeLogSquareMoment_secondDifference
      (by constructor <;> simp <;> linarith)]
  simp only
  ring_nf

theorem primeLogSquareMoment_antitoneOn {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    primeLogSquareMoment b ≤ primeLogSquareMoment a := by
  refine Summable.tsum_le_tsum (fun p => ?_) (summable_primeLogSquareMoment (ha.trans_le hab))
    (summable_primeLogSquareMoment ha)
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_lt.le
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp (by linarith))
    (sq_nonneg _)

theorem primeLogSquareMoment_nonneg (a : ℝ) : 0 ≤ primeLogSquareMoment a :=
  tsum_nonneg fun p => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by positivity) _)

private theorem primeLogSquareComplex_ofReal {x : ℝ} :
    primeLogSquareComplex (x : ℂ) = (primeLogSquareMoment x : ℂ) := by
  unfold primeLogSquareComplex primeLogSquareMoment
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun p => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_cpow (by positivity)]
  push_cast
  ring_nf

/-- **Prime pole of the log-square moment.** `F(δ) - δ^{-2}` converges as `δ → 0+`; in
particular `F(δ) = δ^{-2} + O(1)`. -/
theorem exists_tendsto_primeLogSquareMoment_sub_pole :
    ∃ L : ℝ, Tendsto (fun δ : ℝ => primeLogSquareMoment (1 + δ) - (δ ^ 2)⁻¹) (𝓝[>] 0)
      (𝓝 L) := by
  obtain ⟨G, hG, hQ⟩ := primeLogCriticalContinuation_laurent_one
  have hQ' : ∀ᶠ s in 𝓝 (1 : ℂ), s ≠ 1 →
      primeLogCriticalContinuation s = (s - 1)⁻¹ + G s := eventually_nhdsWithin_iff.mp hQ
  have hGd : ∀ᶠ s in 𝓝 (1 : ℂ), DifferentiableAt ℂ G s :=
    hG.eventually_analyticAt.mono fun s hs => hs.differentiableAt
  have hF : ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      primeLogSquareContinuation s = ((s - 1) ^ 2)⁻¹ - deriv G s := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hQ'.eventually_nhds,
      nhdsWithin_le_nhds hGd] with s hs hnear hdG
    have hs' : s ≠ 1 := hs
    have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs'
    have hloc : primeLogCriticalContinuation =ᶠ[𝓝 s] fun z => (z - 1)⁻¹ + G z := by
      filter_upwards [hnear, isOpen_ne.mem_nhds hs'] with z hz hz'
      exact hz hz'
    have hinv : HasDerivAt (fun z : ℂ => (z - 1)⁻¹) (-1 / (s - 1) ^ 2) s := by
      have h1 : HasDerivAt (fun z : ℂ => z - 1) 1 s := (hasDerivAt_id s).sub_const 1
      exact h1.inv hs1
    have hsum : HasDerivAt (fun z => (z - 1)⁻¹ + G z) (-1 / (s - 1) ^ 2 + deriv G s) s :=
      hinv.add hdG.hasDerivAt
    rw [primeLogSquareContinuation, hloc.deriv_eq, hsum.deriv]
    field_simp
    ring
  have hcoe : Tendsto (fun δ : ℝ => ((1 + δ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : ContinuousAt (fun δ : ℝ => ((1 + δ : ℝ) : ℂ)) 0 := by fun_prop
      simpa using h.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with δ hδ
      intro h
      simp only [Set.mem_singleton_iff] at h
      have : (1 + δ : ℝ) = 1 := by exact_mod_cast h
      have hδ' : (0 : ℝ) < δ := hδ
      linarith
  have hGt : Tendsto (fun δ : ℝ => deriv G ((1 + δ : ℝ) : ℂ)) (𝓝[>] (0 : ℝ))
      (𝓝 (deriv G 1)) :=
    hG.deriv.continuousAt.tendsto.comp (hcoe.mono_right nhdsWithin_le_nhds)
  refine ⟨(-deriv G 1).re, ?_⟩
  have hre := (Complex.continuous_re.tendsto _).comp hGt.neg
  refine hre.congr' ?_
  filter_upwards [hcoe.eventually hF, self_mem_nhdsWithin] with δ hδ hδpos
  have hδ' : (0 : ℝ) < δ := hδpos
  have hs : 1 < ((1 + δ : ℝ) : ℂ).re := by simp; linarith
  rw [primeLogSquareContinuation_eq hs, primeLogSquareComplex_ofReal] at hδ
  have hc : (((1 + δ : ℝ) : ℂ) - 1) = ((δ : ℝ) : ℂ) := by push_cast; ring
  rw [hc] at hδ
  have hδre := congrArg Complex.re hδ
  simp only [Function.comp_apply, Complex.ofReal_re, Complex.sub_re, Complex.neg_re] at hδre ⊢
  rw [hδre]
  have : (((δ : ℂ) ^ 2)⁻¹).re = (δ ^ 2)⁻¹ := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.ofReal_re]
  rw [this]
  ring

/-- `δ² E(1-δ) → 1` as `δ → 0+`: the seam energy blows up like `δ^{-2}` at the outer edge. -/
theorem tendsto_sq_mul_stcSeamEnergy_one_sub :
    Tendsto (fun δ : ℝ => δ ^ 2 * stcSeamEnergy (1 - δ)) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨L, hL⟩ := exists_tendsto_primeLogSquareMoment_sub_pole
  have hδ : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hsq : Tendsto (fun δ : ℝ => δ ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hδ.pow 2
  have hmain : Tendsto (fun δ : ℝ => 1 + δ ^ 2 * (primeLogSquareMoment (1 + δ) - (δ ^ 2)⁻¹) -
      2 * δ ^ 2 * primeLogSquareMoment 2) (𝓝[>] (0 : ℝ)) (𝓝 (1 + 0 * L - 2 * 0 *
        primeLogSquareMoment 2)) :=
    (tendsto_const_nhds.add (hsq.mul hL)).sub ((hsq.const_mul 2).mul tendsto_const_nhds)
  have htail : Tendsto (fun δ : ℝ => δ ^ 2 * primeLogSquareMoment (3 - δ)) (𝓝[>] (0 : ℝ))
      (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ (by simpa using hsq.mul_const (primeLogSquareMoment 2))
    · exact Eventually.of_forall fun δ => mul_nonneg (sq_nonneg δ) (primeLogSquareMoment_nonneg _)
    · have hI : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
      filter_upwards [hI] with δ hδI
      exact mul_le_mul_of_nonneg_left
        (primeLogSquareMoment_antitoneOn (by norm_num) (by linarith [hδI.2])) (sq_nonneg δ)
  have hall := hmain.add htail
  norm_num at hall
  refine hall.congr' ?_
  have hI : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [hI] with δ hδI
  rw [stcSeamEnergy_one_sub hδI.1 (by linarith [hδI.2])]
  have : δ ≠ 0 := hδI.1.ne'
  field_simp
  ring

/-- `W(1-δ)/δ → (log 2)²/8` as `δ → 0+`. -/
theorem tendsto_stcSourceWork_one_sub_div :
    Tendsto (fun δ : ℝ => stcSourceWork (1 - δ) / δ) (𝓝[>] 0) (𝓝 (Real.log 2 ^ 2 / 8)) := by
  let r : ℝ → ℝ := fun δ =>
    Real.log 2 ^ 2 / 4 * (1 - δ) ^ 2 * (2 - δ) / (1 + (1 - δ) ^ 2) ^ 2
  have hr : ContinuousAt r 0 := by
    refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
    norm_num
  have hr0 : r 0 = Real.log 2 ^ 2 / 8 := by simp only [r]; norm_num; ring
  rw [← hr0]
  refine (hr.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ' : δ ≠ 0 := ne_of_gt hδ
  simp only [r]
  rw [stcSourceWork_eq]
  have hden : (1 + (1 - δ) ^ 2) ≠ 0 := by positivity
  field_simp
  ring

/-- **Cubic singular gain.** `δ³ E(1-δ)/W(1-δ) → 8/(log 2)²`. -/
theorem tendsto_cube_mul_stcSeamEnergy_div_work :
    Tendsto (fun δ : ℝ => δ ^ 3 * stcSeamEnergy (1 - δ) / stcSourceWork (1 - δ)) (𝓝[>] 0)
      (𝓝 (8 / Real.log 2 ^ 2)) := by
  have hl : Real.log 2 ^ 2 / 8 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have h := tendsto_sq_mul_stcSeamEnergy_one_sub.div tendsto_stcSourceWork_one_sub_div hl
  have hval : 1 / (Real.log 2 ^ 2 / 8) = 8 / Real.log 2 ^ 2 := by field_simp
  rw [hval] at h
  refine h.congr' ?_
  have hI : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [hI] with δ hδI
  have hW := stcSourceWork_pos (t := 1 - δ) (by linarith [hδI.2]) (by linarith [hδI.1])
  have hδ : δ ≠ 0 := hδI.1.ne'
  simp only [Pi.div_apply]
  field_simp

/-! ### Chronological grade slope -/

/-- The chronological grade slope `W'(t) = 2c t(1-3t²)/(1+t²)³`. -/
def stcSourceWorkSlope (t : ℝ) : ℝ :=
  2 * (Real.log 2 ^ 2 / 4) * t * (1 - 3 * t ^ 2) / (1 + t ^ 2) ^ 3

theorem hasDerivAt_stcSourceWork (t : ℝ) :
    HasDerivAt stcSourceWork (stcSourceWorkSlope t) t := by
  have hfun : stcSourceWork = (fun t : ℝ => Real.log 2 ^ 2 / 4 * (t ^ 2 * (1 - t ^ 2))) /
      (fun t : ℝ => (1 + t ^ 2) ^ 2) := by
    funext t; simp only [Pi.div_apply]; rw [stcSourceWork_eq]; ring
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
  have h2 : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * t)) t := h1.const_sub 1
  have hnum : HasDerivAt (fun t : ℝ => Real.log 2 ^ 2 / 4 * (t ^ 2 * (1 - t ^ 2)))
      (Real.log 2 ^ 2 / 4 * (2 * t * (1 - t ^ 2) + t ^ 2 * (-(2 * t)))) t :=
    (h1.fun_mul h2).const_mul _
  have hd1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * t) t := h1.const_add 1
  have hd := hd1.fun_pow 2
  have hden : (1 + t ^ 2) ^ 2 ≠ 0 := by positivity
  refine (hnum.div hd hden).congr_deriv ?_
  unfold stcSourceWorkSlope
  norm_num
  field_simp
  ring

/-- Sign structure: `W'` is positive below `1/√3`, zero at it and negative above it on `(0,1)`. -/
theorem stcSourceWorkSlope_sign {t : ℝ} (h0 : 0 < t) :
    (0 < stcSourceWorkSlope t ↔ t ^ 2 < 1 / 3) ∧ (stcSourceWorkSlope t = 0 ↔ t ^ 2 = 1 / 3) ∧
      (stcSourceWorkSlope t < 0 ↔ 1 / 3 < t ^ 2) := by
  have hc : 0 < 2 * (Real.log 2 ^ 2 / 4) * t / (1 + t ^ 2) ^ 3 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have heq : stcSourceWorkSlope t = 2 * (Real.log 2 ^ 2 / 4) * t / (1 + t ^ 2) ^ 3 *
      (1 - 3 * t ^ 2) := by
    unfold stcSourceWorkSlope; ring
  rw [heq]
  refine ⟨⟨fun h => ?_, fun h => mul_pos hc (by linarith)⟩,
    ⟨fun h => ?_, fun h => by rw [h]; ring⟩, ⟨fun h => ?_, fun h => mul_neg_of_pos_of_neg hc
      (by linarith)⟩⟩
  · have := (pos_iff_pos_of_mul_pos h).mp hc; linarith
  · rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hc.ne'
    · linarith
  · have := (mul_neg_iff.mp h)
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · linarith

private theorem workShape_eq_iff {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    stcWorkShape u = stcWorkShape v ↔ u = v ∨ 1 - u - v - 3 * u * v = 0 := by
  unfold stcWorkShape
  have hu1 : (1 + u) ^ 2 ≠ 0 := by positivity
  have hv1 : (1 + v) ^ 2 ≠ 0 := by positivity
  rw [div_eq_div_iff hu1 hv1]
  constructor
  · intro h
    have : (u - v) * (1 - u - v - 3 * u * v) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · left; linarith
    · right; exact h1
  · rintro (h | h)
    · rw [h]
    · linear_combination (u - v) * h

/-- **Chronological branch resolution.** On `(0,1)`, the pair `(W(t), sign W'(t))` determines `t`. -/
theorem stcSourceWork_branch_injective {s t : ℝ} (hs0 : 0 < s) (ht0 : 0 < t) (hW : stcSourceWork s = stcSourceWork t)
    (hsign : SignType.sign (stcSourceWorkSlope s) = SignType.sign (stcSourceWorkSlope t)) :
    s = t := by
  have hshape : stcWorkShape (s ^ 2) = stcWorkShape (t ^ 2) := by
    unfold stcSourceWork at hW
    have hc : Real.log 2 ^ 2 / 4 ≠ 0 := by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      positivity
    exact mul_left_cancel₀ hc hW
  rcases (workShape_eq_iff (sq_nonneg s) (sq_nonneg t)).mp hshape with h | h
  · nlinarith [sq_nonneg (s - t), sq_nonneg (s + t)]
  · -- the dual branch: `s² - 1/3` and `t² - 1/3` have opposite signs
    obtain ⟨hs1', hs2', hs3'⟩ := stcSourceWorkSlope_sign hs0
    obtain ⟨ht1', ht2', ht3'⟩ := stcSourceWorkSlope_sign ht0
    have hopp : (s ^ 2 - 1 / 3) * (t ^ 2 - 1 / 3) ≤ 0 := by nlinarith [sq_nonneg (s ^ 2 - t ^ 2)]
    have hsq : s ^ 2 = 1 / 3 := by
      rcases lt_trichotomy (s ^ 2) (1 / 3) with hlt | heq | hgt
      · have hpos : 0 < stcSourceWorkSlope s := hs1'.mpr hlt
        rw [sign_pos hpos] at hsign
        have htpos : 0 < stcSourceWorkSlope t := sign_eq_one_iff.mp hsign.symm
        have := ht1'.mp htpos
        nlinarith
      · exact heq
      · have hneg : stcSourceWorkSlope s < 0 := hs3'.mpr hgt
        rw [sign_neg hneg] at hsign
        have htneg : stcSourceWorkSlope t < 0 := sign_eq_neg_one_iff.mp hsign.symm
        have := ht3'.mp htneg
        nlinarith
    have htsq : t ^ 2 = 1 / 3 := by rw [hsq] at h; linarith
    nlinarith [sq_nonneg (s - t), sq_nonneg (s + t)]

/-! ### The work diagonal supplies no all-prime square budget -/

theorem stcSourceWork_ne_zero_iff (t : ℝ) : stcSourceWork t ≠ 0 ↔ t ≠ 0 ∧ t ^ 2 ≠ 1 := by
  rw [stcSourceWork_eq]
  have hl : Real.log 2 ^ 2 / 4 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    positivity
  have hd : (1 + t ^ 2) ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    refine ⟨fun ht => h (by simp [ht]), fun ht => h (by rw [ht]; ring)⟩
  · rintro ⟨h0, h1⟩
    refine div_ne_zero (mul_ne_zero (mul_ne_zero hl (pow_ne_zero 2 h0)) ?_) hd
    intro h; apply h1; linarith

/-- **No summed Bockstein budget.** At a Xi-divisor copy with nonzero phase work (equivalently
centered rate `t ≠ 0`, `t² ≠ 1`), the normalized literal Route-R prime Bockstein squares are one
positive constant at every prime, so they are not summable over the primes. -/
theorem not_summable_normalizedRouteRPrimeGammaBockstein_normSq (q : XiZeroCopy)
    (hq : stcSourceWork (primeDepthBVWoldXiCenteredRate q.1) ≠ 0) :
    ¬ Summable (fun p : Nat.Primes => Complex.normSq
      (((primeActivationOccupancyFisherTwist (-(2 * (q.1 : ℂ).re - 1)) p -
          primeActivationOccupancyFisherTwist (2 * (q.1 : ℂ).re - 1) p : ℝ) : ℂ) /
        routeRPrimeGammaXiWronskianTransferFactor p q)) := by
  simp only [normalizedRouteRPrimeGammaBockstein_eq_gaussianSourceWronskian]
  rw [summable_const_iff]
  intro h0
  apply hq
  have hw := sourceTailSoninPhaseWork_eq_gaussianWronskianGain_normSq q
  rw [h0, mul_zero, sourceTailSoninPhaseWork_eq_stcSourceWork] at hw
  exact_mod_cast hw

end

end RHTower
