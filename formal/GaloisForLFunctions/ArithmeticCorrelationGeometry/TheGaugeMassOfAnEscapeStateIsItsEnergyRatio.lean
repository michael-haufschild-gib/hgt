import GaloisForLFunctions.ArithmeticCorrelationGeometry.EscapeStatesAreSpectralMeasuresOnTheGaugeTorus
import GaloisForLFunctions.ArithmeticDefectRigidity.TheAdmittedCofactorKernelIsUnique

/-!
# The gauge mass of an escape state is its energy ratio

An escape state `L` of the damped Möbius receiver has a spectral measure `ν_L` on the gauge torus
(`EscapeStatesAreSpectralMeasuresOnTheGaugeTorus`). Its total mass is
`K̃_∞(1,1) = inf_d d·K(d,d)` (`gaugeMass_eq_iInf`). This module computes it from the receiver
energy `E(N) = Σ_{n ≤ N} A(n)²/(n(n+1))`.

* **Fibre sandwich** (`pronicNorm_rowDilate_sq_le`, `pronicNorm_rowDilate_sq_ge`). The dilation
  `D_j v(n) = v(⌊n/j⌋)` folds the horizons `jm, …, jm + j − 1` onto `m`, with pronic mass exactly
  `1/j` of the level `m`. On `[1, T]`, with `M = ⌊(T+1)/j⌋`:
  `(1/j) E_v(M − 1) ≤ ‖D_j v‖²_T ≤ (1/j) E_v(M)`.
* **Diagonal = energy ratio** (`energyRatio_sub_one_le_mul_cofactorGram`,
  `mul_cofactorGram_le_energyRatio`). For the actual receiver at horizon `T + 1`,
  `E(M − 1)/E(T+1) ≤ d·K_T(d,d) ≤ E(M)/E(T+1)`, `M = ⌊(T+2)/d⌋`. So the gauge mass of an escape
  state is the asymptotic energy ratio `inf_d lim E(T/d)/E(T)` along its horizons
  (`gaugeMass_le_energyRatio`, `energyRatio_le_mul_kernel`).
* **Admission gives a probability measure** (`gaugeMass_eq_one_of_admits`). If the receiver energy
  is bounded, every escape-state limit has gauge mass one.
* **Power-type escape is invisible** (`gaugeMass_eq_zero_of_powerGrowth`). If along the horizons of
  `L` the energy grows like a positive power, `c N^κ ≤ E(N) ≤ C N^κ`, the spectral measure of `L`
  is zero.

Gauge status: the gauge torus sees exactly the scale-invariant part of the escaping energy. A
receiver whose energy is bounded or slowly varying has escape states of full gauge mass; energy
that grows by a power, the signature of an off-line zero, carries no gauge spectrum at all.
-/

open MeasureTheory Finset Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open BezoutValuationIncidence ArithmeticContinuationAndCriticalEnergy ArithmeticDefectRigidity

/-! ### The fibre sandwich -/

theorem pronicNorm_sq_mono {N N' : ℕ} (h : N ≤ N') (v : ℕ → ℝ) :
    pronicNorm N v ^ 2 ≤ pronicNorm N' v ^ 2 := by
  rw [pronicNorm_sq, pronicNorm_sq]
  exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h) fun n _ _ =>
    div_nonneg (sq_nonneg _) (by positivity)

/-- **Upper fibre bound.** `‖D_j v‖²_T ≤ (1/j) E_v(⌊(T+1)/j⌋)`. -/
theorem pronicNorm_rowDilate_sq_le {j : ℕ} (hj : 1 ≤ j) (T : ℕ) (v : ℕ → ℝ) (hv0 : v 0 = 0) :
    pronicNorm T (rowDilate j v) ^ 2 ≤ (1 / (j : ℝ)) * pronicNorm ((T + 1) / j) v ^ 2 := by
  set M := (T + 1) / j
  set v' : ℕ → ℝ := fun m => if m ≤ M then v m else 0
  have hv'0 : v' 0 = 0 := by simp [v', hv0]
  have hrow : pronicNorm T (rowDilate j v) = pronicNorm T (rowDilate j v') := by
    unfold pronicNorm
    congr 1
    refine sum_congr rfl fun n hn => ?_
    have hn' : n / j ≤ M := Nat.div_le_div_right (by have := (mem_Icc.mp hn).2; omega)
    simp only [rowDilate, v', if_pos hn']
  have hsharp := pronicNorm_rowDilate_le_sharp hj T v' hv'0
  have hsq : pronicNorm T (rowDilate j v') ^ 2 ≤ (1 / (j : ℝ)) * pronicNorm T v' ^ 2 := by
    have := pow_le_pow_left₀ (pronicNorm_nonneg _ _) hsharp 2
    have hj0 : (0 : ℝ) ≤ j := by positivity
    rwa [mul_pow, div_pow, one_pow, Real.sq_sqrt hj0] at this
  have htrunc : pronicNorm T v' ^ 2 ≤ pronicNorm M v ^ 2 := by
    rw [pronicNorm_sq, pronicNorm_sq]
    calc ∑ n ∈ Icc 1 T, v' n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))
        = ∑ n ∈ (Icc 1 T).filter (· ≤ M), v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
          rw [sum_filter]
          refine sum_congr rfl fun n _ => ?_
          by_cases h : n ≤ M <;> simp [v', h]
      _ ≤ ∑ n ∈ Icc 1 M, v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
          refine sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ =>
            div_nonneg (sq_nonneg _) (by positivity)
          obtain ⟨h1, h2⟩ := mem_filter.mp hn
          exact mem_Icc.mpr ⟨(mem_Icc.mp h1).1, h2⟩
  rw [hrow]
  exact hsq.trans (mul_le_mul_of_nonneg_left htrunc (by positivity))

/-- **Exact fibre identity.** On complete fibres, `‖D_j v‖²_{jK + j − 1} = (1/j) E_v(K)`. -/
theorem pronicNorm_rowDilate_sq_eq {j : ℕ} (hj : 1 ≤ j) (v : ℕ → ℝ) (hv0 : v 0 = 0) (K : ℕ) :
    pronicNorm (j * K + (j - 1)) (rowDilate j v) ^ 2 = (1 / (j : ℝ)) * pronicNorm K v ^ 2 := by
  have hIoc : ∀ N, Icc 1 N = Ioc 0 N := fun N => by ext n; simp only [mem_Icc, mem_Ioc]; omega
  induction K with
  | zero =>
    rw [pronicNorm_sq, pronicNorm_sq, mul_zero, zero_add]
    have h0 : ∀ n ∈ Icc 1 (j - 1), rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) = 0 := by
      intro n hn
      have : n / j = 0 := Nat.div_eq_of_lt (by have := (mem_Icc.mp hn).2; omega)
      simp [rowDilate, this, hv0]
    rw [sum_congr rfl h0]
    simp
  | succ K ih =>
    simp only [pronicNorm_sq] at ih ⊢
    have hsplit : j * (K + 1) + (j - 1) = (j * K + (j - 1)) + j := by rw [mul_add, mul_one]; omega
    have hblock : Ioc (j * K + (j - 1)) (j * K + (j - 1) + j) =
        Icc (j * (K + 1)) (j * (K + 1) + j - 1) := by
      ext n; simp only [mem_Ioc, mem_Icc, mul_add, mul_one]; omega
    have hL : ∑ n ∈ Icc 1 (j * (K + 1) + (j - 1)), rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
        ∑ n ∈ Icc 1 (j * K + (j - 1)), rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) +
          ∑ n ∈ Icc (j * (K + 1)) (j * (K + 1) + j - 1),
            rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      rw [hsplit, hIoc, hIoc, ← sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.le_add_right _ j), hblock]
    have hR : ∑ n ∈ Icc 1 (K + 1), v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
        ∑ n ∈ Icc 1 K, v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) +
          v (K + 1) ^ 2 / (((K + 1 : ℕ) : ℝ) * (((K + 1 : ℕ) : ℝ) + 1)) := by
      rw [hIoc, hIoc, sum_Ioc_succ_top (Nat.zero_le K)]
    rw [hL, hR, ih, mul_add]
    congr 1
    have hval : ∀ n ∈ Icc (j * (K + 1)) (j * (K + 1) + j - 1),
        rowDilate j v n ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) =
          v (K + 1) ^ 2 * (1 / ((n : ℝ) * ((n : ℝ) + 1))) := by
      intro n hn
      obtain ⟨h1, h2⟩ := mem_Icc.mp hn
      have hdiv : n / j = K + 1 :=
        Nat.div_eq_of_lt_le (by rw [mul_comm]; exact h1)
          (by rw [add_mul, one_mul, mul_comm]; omega)
      rw [rowDilate, hdiv]
      ring
    rw [sum_congr rfl hval, ← mul_sum, sum_Icc_pronic_dilation_fibre hj (by omega)]
    push_cast
    have hj0 : (j : ℝ) ≠ 0 := by positivity
    field_simp

/-- **Lower fibre bound.** `(1/j) E_v(⌊(T+1)/j⌋ − 1) ≤ ‖D_j v‖²_T`. -/
theorem pronicNorm_rowDilate_sq_ge {j : ℕ} (hj : 1 ≤ j) (T : ℕ) (v : ℕ → ℝ) (hv0 : v 0 = 0) :
    (1 / (j : ℝ)) * pronicNorm ((T + 1) / j - 1) v ^ 2 ≤ pronicNorm T (rowDilate j v) ^ 2 := by
  rcases Nat.eq_zero_or_pos ((T + 1) / j) with h0 | hpos
  · rw [h0, Nat.zero_sub, pronicNorm_sq]
    simp only [Icc_eq_empty_of_lt one_pos, sum_empty, mul_zero]
    exact sq_nonneg _
  rw [← pronicNorm_rowDilate_sq_eq hj v hv0]
  refine pronicNorm_sq_mono ?_ _
  have hle : j * ((T + 1) / j) ≤ T + 1 := Nat.mul_div_le (T + 1) j
  have hsub : j * ((T + 1) / j - 1) + j = j * ((T + 1) / j) := by
    have h1 : (T + 1) / j - 1 + 1 = (T + 1) / j := Nat.sub_add_cancel hpos
    calc j * ((T + 1) / j - 1) + j = j * ((T + 1) / j - 1 + 1) := by ring
      _ = j * ((T + 1) / j) := by rw [h1]
  omega

/-! ### The diagonal of an escape state is an energy ratio -/

/-- The receiver energy is the pronic mass of the receiver prefix. -/
theorem dampedMobiusEnergy_eq_pronicNorm_sq (ε : ℝ) (N : ℕ) :
    dampedMobiusEnergy ε N = pronicNorm N (RHTower.pmPowerDampedCenteredDivisorPrefix ε) ^ 2 := by
  rw [pronicNorm_centeredPrefix, Real.sq_sqrt (dampedMobiusEnergy_nonneg ε N)]

theorem cofactorGram_self (ε : SubcriticalDamping) (T : ℕ) (d : ℕ+) :
    cofactorGram ε T d d = pronicNorm (T + 1) (rowDilate d (RHTower.pmPowerDampedCenteredDivisorPrefix ε)) ^ 2 /
      dampedMobiusEnergy ε (T + 1) := by
  rw [cofactorGram, pronicNorm_sq]
  congr 1
  unfold pronicPairing
  exact sum_congr rfl fun n _ => by ring

/-- **Upper energy ratio.** `d·K_T(d,d) ≤ E(⌊(T+2)/d⌋)/E(T+1)`. -/
theorem mul_cofactorGram_le_energyRatio (ε : SubcriticalDamping) (T : ℕ) (d : ℕ+) :
    (d : ℝ) * cofactorGram ε T d d ≤
      dampedMobiusEnergy ε ((T + 1 + 1) / d) / dampedMobiusEnergy ε (T + 1) := by
  have hE := receiverEnergy_succ_pos ε T
  have hd : (0 : ℝ) < d := by exact_mod_cast d.pos
  rw [cofactorGram_self, ← mul_div_assoc, div_le_div_iff_of_pos_right hE,
    dampedMobiusEnergy_eq_pronicNorm_sq]
  have := pronicNorm_rowDilate_sq_le d.pos (T + 1) _
    (ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero (ε : ℝ))
  calc (d : ℝ) * pronicNorm (T + 1) (rowDilate d (RHTower.pmPowerDampedCenteredDivisorPrefix ε)) ^ 2
      ≤ (d : ℝ) * ((1 / (d : ℝ)) * pronicNorm ((T + 1 + 1) / d)
          (RHTower.pmPowerDampedCenteredDivisorPrefix ε) ^ 2) := mul_le_mul_of_nonneg_left this hd.le
    _ = _ := by field_simp

/-- **Lower energy ratio.** `E(⌊(T+2)/d⌋ − 1)/E(T+1) ≤ d·K_T(d,d)`. -/
theorem energyRatio_sub_one_le_mul_cofactorGram (ε : SubcriticalDamping) (T : ℕ) (d : ℕ+) :
    dampedMobiusEnergy ε ((T + 1 + 1) / d - 1) / dampedMobiusEnergy ε (T + 1) ≤
      (d : ℝ) * cofactorGram ε T d d := by
  have hE := receiverEnergy_succ_pos ε T
  have hd : (0 : ℝ) < d := by exact_mod_cast d.pos
  rw [cofactorGram_self, ← mul_div_assoc, div_le_div_iff_of_pos_right hE,
    dampedMobiusEnergy_eq_pronicNorm_sq]
  have := pronicNorm_rowDilate_sq_ge d.pos (T + 1) _
    (ArithmeticContinuationAndCriticalEnergy.pmPowerDampedCenteredDivisorPrefix_zero (ε : ℝ))
  calc pronicNorm ((T + 1 + 1) / d - 1) (RHTower.pmPowerDampedCenteredDivisorPrefix ε) ^ 2
      = (d : ℝ) * ((1 / (d : ℝ)) * pronicNorm ((T + 1 + 1) / d - 1)
          (RHTower.pmPowerDampedCenteredDivisorPrefix ε) ^ 2) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left this hd.le

/-! ### Gauge mass -/

/-- The gauge mass of a dilation-contractive kernel: the total mass `K̃_∞(1,1)` of its spectral
measure. -/
def gaugeMass (K : ℕ+ → ℕ+ → ℝ) : ℝ := asymKernel K 1 1

/-- **The gauge mass is `inf_d d·K(d,d)`.** -/
theorem gaugeMass_eq_iInf {K : ℕ+ → ℕ+ → ℝ} (hsymm : ∀ j k, K j k = K k j)
    (hpsd : ∀ (S : Finset ℕ+) (c : ℕ+ → ℝ), 0 ≤ ∑ j ∈ S, ∑ k ∈ S, c j * c k * K j k)
    (hcontr : ∀ (p : ℕ+) (S : Finset ℕ+) (c : ℕ+ → ℝ),
      ∑ j ∈ S, ∑ k ∈ S, c j * c k * K (p * j) (p * k) ≤
        (1 / (p : ℝ)) * ∑ j ∈ S, ∑ k ∈ S, c j * c k * K j k) :
    gaugeMass K = ⨅ d : ℕ+, (d : ℝ) * K d d := by
  have h := asymKernel_form hsymm hpsd hcontr {1} fun _ => 1
  simp only [sum_singleton, mul_one, one_mul] at h
  rw [gaugeMass, h, asymForm]
  congr 1
  funext d
  simp only [dilForm, sum_singleton, mul_one, one_mul, critKernel]
  have hd : (0 : ℝ) ≤ d := by positivity
  rw [Real.mul_self_sqrt hd]

namespace ActualCofactorLimitMass

variable {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)

theorem gaugeMass_eq : gaugeMass L.kernel = ⨅ d : ℕ+, (d : ℝ) * L.kernel d d :=
  gaugeMass_eq_iInf L.kernel_symm L.packet_nonneg L.packet_dilation_le

theorem tendsto_mul_cofactorGram (d : ℕ+) :
    Tendsto (fun m => (d : ℝ) * cofactorGram ε (L.subsequence m) d d) atTop
      (𝓝 ((d : ℝ) * L.kernel d d)) :=
  tendsto_const_nhds.mul (L.converges d d)

/-- **The diagonal of an escape state is bounded by its energy ratio**: for every `δ > 0`,
eventually `d·K(d,d) ≤ E(⌊(T+2)/d⌋)/E(T+1) + δ` along the horizons of `L`. -/
theorem mul_kernel_le_energyRatio (d : ℕ+) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m in atTop, (d : ℝ) * L.kernel d d ≤
      dampedMobiusEnergy ε ((L.subsequence m + 1 + 1) / d) /
        dampedMobiusEnergy ε (L.subsequence m + 1) + δ := by
  filter_upwards [(tendsto_order.mp (tendsto_mul_cofactorGram L d)).1 _
    (sub_lt_self _ hδ)] with m hm
  have := mul_cofactorGram_le_energyRatio ε (L.subsequence m) d
  linarith

/-- **The energy ratio is bounded by the diagonal**: for every `δ > 0`, eventually
`E(⌊(T+2)/d⌋ − 1)/E(T+1) ≤ d·K(d,d) + δ`. -/
theorem energyRatio_le_mul_kernel (d : ℕ+) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m in atTop, dampedMobiusEnergy ε ((L.subsequence m + 1 + 1) / d - 1) /
        dampedMobiusEnergy ε (L.subsequence m + 1) ≤ (d : ℝ) * L.kernel d d + δ := by
  filter_upwards [(tendsto_order.mp (tendsto_mul_cofactorGram L d)).2 _
    (lt_add_of_pos_right _ hδ)] with m hm
  have := energyRatio_sub_one_le_mul_cofactorGram ε (L.subsequence m) d
  linarith

theorem tendsto_subsequence_atTop : Tendsto L.subsequence atTop atTop :=
  L.strictMono.tendsto_atTop

theorem tendsto_div_atTop (d : ℕ+) (k : ℕ) :
    Tendsto (fun m => (L.subsequence m + 1 + 1) / (d : ℕ) - k) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun b => ?_
  obtain ⟨m₀, hm₀⟩ := tendsto_atTop_atTop.mp tendsto_subsequence_atTop L ((b + k) * d)
  refine ⟨m₀, fun m hm => ?_⟩
  have h1 := hm₀ m hm
  have h2 : b + k ≤ (L.subsequence m + 1 + 1) / (d : ℕ) := by
    rw [Nat.le_div_iff_mul_le d.pos]
    omega
  omega

/-- **Admission gives full gauge mass.** If the receiver energy is bounded, every escape-state
limit has `d·K(d,d) = 1` for all `d`, so its spectral measure is a probability measure. -/
theorem gaugeMass_eq_one_of_admits (hadm : Admits dampedMobiusEnergy ε) :
    gaugeMass L.kernel = 1 := by
  obtain ⟨e, he, hlim⟩ := exists_positive_receiverEnergy_limit_of_admits ε hadm
  have hdiag : ∀ d : ℕ+, (d : ℝ) * L.kernel d d = 1 := by
    intro d
    have hden : Tendsto (fun m => dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 e) :=
      hlim.comp ((tendsto_add_atTop_nat 1).comp tendsto_subsequence_atTop L)
    have hup : Tendsto (fun m => dampedMobiusEnergy ε ((L.subsequence m + 1 + 1) / d) /
        dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 1) := by
      have := (hlim.comp (by simpa using tendsto_div_atTop L d 0)).div hden he.ne'
      rwa [div_self he.ne'] at this
    have hlo : Tendsto (fun m => dampedMobiusEnergy ε ((L.subsequence m + 1 + 1) / d - 1) /
        dampedMobiusEnergy ε (L.subsequence m + 1)) atTop (𝓝 1) := by
      have := (hlim.comp (tendsto_div_atTop L d 1)).div hden he.ne'
      rwa [div_self he.ne'] at this
    refine le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_)
      (le_of_forall_pos_le_add fun δ hδ => ?_)
    · obtain ⟨m, hm1, hm2⟩ := ((mul_kernel_le_energyRatio L d (half_pos hδ)).and
        ((tendsto_order.mp hup).2 _ (lt_add_of_pos_right 1 (half_pos hδ)))).exists
      linarith
    · obtain ⟨m, hm1, hm2⟩ := ((energyRatio_le_mul_kernel L d (half_pos hδ)).and
        ((tendsto_order.mp hlo).1 _ (sub_lt_self 1 (half_pos hδ)))).exists
      linarith
  rw [gaugeMass_eq L]
  simp_rw [hdiag]
  exact ciInf_const

/-- **Power-type escape has no gauge spectrum.** If the receiver energy is eventually trapped
between `c N^κ` and `C N^κ` with `κ > 0`, the spectral measure of every escape state is zero. -/
theorem gaugeMass_eq_zero_of_powerGrowth {κ c C : ℝ} (hκ : 0 < κ) (hc : 0 < c)
    (hpow : ∀ᶠ N : ℕ in atTop, c * (N : ℝ) ^ κ ≤ dampedMobiusEnergy ε N ∧
      dampedMobiusEnergy ε N ≤ C * (N : ℝ) ^ κ) :
    gaugeMass L.kernel = 0 := by
  have hsymm := L.kernel_symm
  have hpsd := L.packet_nonneg
  have hcontr := L.packet_dilation_le
  have hnonneg : 0 ≤ gaugeMass L.kernel := by
    have := asymKernel_psd hsymm hpsd hcontr {1} fun _ => 1
    simpa [gaugeMass] using this
  have hC : 0 < C := by
    obtain ⟨N, hN⟩ := (hpow.and (eventually_ge_atTop 1)).exists
    have hNpos : (0 : ℝ) < (N : ℝ) ^ κ := Real.rpow_pos_of_pos (by exact_mod_cast hN.2) _
    nlinarith [hN.1.1, hN.1.2]
  -- `d·K(d,d) ≤ (C/c)(2/d)^κ` for every `d`
  have hdiag : ∀ d : ℕ+, (d : ℝ) * L.kernel d d ≤ C / c * (2 / (d : ℝ)) ^ κ := by
    intro d
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hev1 := (tendsto_div_atTop L d 0).eventually hpow
    have hev2 := ((tendsto_add_atTop_nat 1).comp tendsto_subsequence_atTop L).eventually hpow
    obtain ⟨m, hm, h1, h2⟩ := ((mul_kernel_le_energyRatio L d hδ).and (hev1.and hev2)).exists
    simp only [Function.comp_apply, Nat.sub_zero] at h1 h2
    set T := L.subsequence m
    set M := (T + 1 + 1) / (d : ℕ)
    have hT : (0 : ℝ) < ((T + 1 : ℕ) : ℝ) := by positivity
    have hEpos : 0 < dampedMobiusEnergy ε (T + 1) :=
      lt_of_lt_of_le (mul_pos hc (Real.rpow_pos_of_pos hT _)) h2.1
    have hMle : (M : ℝ) ≤ 2 / (d : ℝ) * ((T + 1 : ℕ) : ℝ) := by
      have hd : (0 : ℝ) < d := by exact_mod_cast d.pos
      have hMd : (M : ℝ) * d ≤ (T : ℝ) + 2 := by
        have := Nat.div_mul_le_self (T + 1 + 1) d
        exact_mod_cast (by omega : M * (d : ℕ) ≤ T + 2)
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]
      push_cast
      linarith [(T.cast_nonneg : (0 : ℝ) ≤ T)]
    have hratio : dampedMobiusEnergy ε M / dampedMobiusEnergy ε (T + 1) ≤
        C / c * (2 / (d : ℝ)) ^ κ := by
      rw [div_le_iff₀ hEpos]
      calc dampedMobiusEnergy ε M ≤ C * (M : ℝ) ^ κ := h1.2
        _ ≤ C * (2 / (d : ℝ) * ((T + 1 : ℕ) : ℝ)) ^ κ :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hMle hκ.le) hC.le
        _ = C / c * (2 / (d : ℝ)) ^ κ * (c * ((T + 1 : ℕ) : ℝ) ^ κ) := by
            rw [Real.mul_rpow (by positivity) hT.le]
            field_simp
        _ ≤ C / c * (2 / (d : ℝ)) ^ κ * dampedMobiusEnergy ε (T + 1) :=
            mul_le_mul_of_nonneg_left h2.1 (by positivity)
    linarith
  -- the infimum over `d` of `(C/c)(2/d)^κ` is zero
  refine le_antisymm (le_of_forall_pos_le_add fun δ hδ => ?_) hnonneg
  have hlim : Tendsto (fun n : ℕ => C / c * (2 / ((n + 1 : ℕ) : ℝ)) ^ κ) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 2 / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
      have := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
      exact this.comp (tendsto_add_atTop_nat 1) |>.congr fun n => by simp
    have := ((Real.continuousAt_rpow_const 0 κ (Or.inr hκ)).tendsto.comp h0).const_mul (C / c)
    simpa [Real.zero_rpow hκ.ne'] using this
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  rw [gaugeMass_eq L]
  have hbdd : BddBelow (Set.range fun d : ℕ+ => (d : ℝ) * L.kernel d d) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨d, rfl⟩
    have := asymKernel_psd hsymm hpsd hcontr {1} fun _ => 1
    have hd := L.packet_nonneg {d} fun _ => 1
    simp only [sum_singleton, mul_one] at hd
    exact mul_nonneg (by positivity) hd
  calc (⨅ d : ℕ+, (d : ℝ) * L.kernel d d) ≤ ((n.succPNat : ℕ+) : ℝ) * L.kernel n.succPNat n.succPNat :=
        ciInf_le hbdd _
    _ ≤ C / c * (2 / ((n.succPNat : ℕ+) : ℝ)) ^ κ := hdiag _
    _ ≤ 0 + δ := by
        have : ((n.succPNat : ℕ+) : ℝ) = ((n + 1 : ℕ) : ℝ) := by simp
        rw [this]
        linarith

end ActualCofactorLimitMass

end GaloisForLFunctions.ArithmeticCorrelationGeometry
