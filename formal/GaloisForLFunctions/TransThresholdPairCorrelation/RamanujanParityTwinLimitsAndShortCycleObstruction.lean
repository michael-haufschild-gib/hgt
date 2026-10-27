import GaloisForLFunctions.TransThresholdPairCorrelation.ParitySensitiveRamanujanStabilizerTransfer
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.TheRamanujanTwinsSurviveExactlyOnPerOrderRelations
import GaloisForLFunctions.RenormalizedBiarithmeticGeometry.ThePoleNodeCompletesTheArchimedeanGerm
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheWeilPrimeKernelIsARenormalizedTorsionEnergy
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheStripLivesOnShortCycles
import GaloisForLFunctions.ArithmeticIncidencePositivity.SchurLendingOddWindowThreeHundredSixtyTwoThousandths
import GaloisForLFunctions.ArithmeticCriticalityTheory.ParityFoldedCurvedGaugeWeilPositivity

/-!
# Closed-Form Ramanujan Parity-Twin Limits, Pole-Node Erasure, and Short-Cycle Positivity

This module resolves Open Topic #1 of `RenormalizedBiarithmeticGeometry` unconditionally by
evaluating in closed form the Cesàro Gram matrices, scheme-independent survival cones, and
renormalized `r → 1⁻` limit matrices of both even-shifted (`2k`) and torsion-aligned (`k + 1`,
`2(k + 1)`) Ramanujan periodic germs, proving the exact **Pole-Node Erasure Law** that explains why
periodic-germ survival erases the prime-side torsion intersection `Λ(t)` on general short cycles,
and establishing three unconditional positive survivors:

1. **Closed-Form Cesàro Gram and Scheme-Independent `{q, 2q}` Survival Cone
   (`cesaroGram_evenShift_ramanujanMode_eq`, `evenShift_ramanujanParityTwin_survivalCone_eq`,
   `parityTwinPair_unrestricted_vs_evenShift_survivalCone`):**
   For any `ord : Fin N → ℕ` with `0 < ord α` and `¬ 4 ∣ ord α`, the Cesàro Gram of
   `k ↦ ramanujanMode (ord α) (2 * k)` over `∏ γ, oddCore (ord γ)` equals
   `if oddCore (ord α) = oddCore (ord β) then φ(oddCore (ord α)) else 0`, and **every**
   renormalization has survival cone `{C | ∀ m, ∑_{oddCore(ord α) = m} C α = 0}`. On a single
   parity-twin pair `![q, 2 * q]` (`q` odd), unrestricted shifts have survival cone `{0}`, whereas
   even shifts have the rank-1 survival line `{C | C 0 + C 1 = 0}`.

2. **Closed-Form Twisted Digamma and Cyclotomic-Harmonic Limit Matrices
   (`tendsto_divisibilityGerm_add_log`, `tendsto_shiftedDivisibilityGerm_add_log`,
   `tendsto_evenShift_ramanujanGerm_closedForm`, `tendsto_torsionAligned_ramanujanGerm_closedForm`):**
   Evaluates the `r → 1⁻` renormalized limits in closed form via double Möbius inversion:
   * Unshifted / `evenShift_ramanujanParityTwin`:
     `-orbitIntersection q_α q_β - cyclotomicDigamma q_α q_β (1 + x α + x β)`;
   * Torsion-aligned (`k + 1` or `2(k + 1)`):
     `-orbitIntersection q_α q_β - cyclotomicHarmonic q_α q_β (x α + x β)`, which reduces at the
     pole nodes `x α = x β = 0` to `-orbitIntersection q_α q_β` (`= -φ(q_α) Λ(t)` on `q_β = q_α t`).

3. **Pole-Node Erasure Law (`poleNode_erasure_of_nodeIndependent_kernel`,
   `quad_torsionAlignedLimit_eq_neg_cyclotomicHarmonic_on_cone`):**
   Because `-orbitIntersection q_α q_β` depends only on the discrete orders `(q_α, q_β)` and is
   independent of the continuous nodes `(x α, x β)`, it vanishes identically on the entire survival
   cone `∀ m, ∑_{q_α = m} C α = 0` — including under pole-node completion (`x = 0`). Thus periodic
   germ survival erases `Λ(t)` completely and leaves a source-independent cyclotomic-archimedean
   kernel.

4. **Three Unconditional Positive Survivors:**
   * **Unconstrained PSD Cyclotomic-Harmonic Kernel (`cyclotomicHarmonicKernel_nonneg`):**
     Pole-node completion (`x = 0` per order) makes
     `cyclotomicHarmonic m_i m_j (x_i) + cyclotomicHarmonic m_i m_j (x_j) - cyclotomicHarmonic m_i m_j (x_i + x_j)`
     positive semidefinite on arbitrary `(m_i, x_i) ∈ ℕ_+ × ℝ_{≥0}`, generalizing
     `RBG.harmonicKernel_nonneg` (`m_i ≡ 1`).
   * **Dyadic Parity-Split Scale Anomaly (`torsionEnergy_dyadic_parity_split`,
     `tendsto_oddTorsionEnergy_add_half_log`):**
     Splits `torsionEnergy r q (2 * q)` (`q` odd) into `(1/2) torsionEnergy (r^2) q q - oddTorsionEnergy r q q`,
     locating `I(q, 2q) = φ(q) log 2` in the dyadic scale anomaly between `+c_q` even frequencies
     and `-c_q` odd frequencies.
   * **Midpoint Parity-Transposition & Coercive `m = 1` Short-Cycle Weil Positivity
     (`shortCycle_re_W_eq_even_add_odd`, `even_shortCycle_m_one_re_W_ge`):**
     Midpoint centering `T_{-v/2}(g - T_v g)` transposes even tests into the odd Weil sector and
     odd tests into the even Weil sector with zero cross-term, proving unconditionally that for
     every symmetric `g ∈ C²(ℝ, ℂ)` (`∀ x, g (-x) = g x`) supported in `[-η, η]` with
     `0 < η ≤ 181/500 - (log 2)/2` (`> 3/200`),
     `1/1000 * ∫ ‖g - T_{\log 2} g‖² ≤ Re W_ζ(g - T_{\log 2} g, g - T_{\log 2} g)`.
-/

open MeasureTheory Real Set Finset Filter Topology Complex
open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.TransThresholdPairCorrelation

open Zeta23 RHTower
open GaloisForLFunctions.RenormalizedBiarithmeticGeometry
open GaloisForLFunctions.ArithmeticEffectivityTheory
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticIncidencePositivity
open GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ## §1. Closed-Form Cesàro Gram and Scheme-Independent `{q, 2q}` Survival Cone -/

/-- Closed-form Cesàro Gram matrix of Ramanujan torsion modes over their common period. -/
theorem cesaroGram_ramanujanMode_eq {N : ℕ} (ord : Fin N → ℕ) (hord : ∀ α, 0 < ord α)
    (α β : Fin N) :
    cesaroGram (fun γ => ramanujanMode (ord γ)) (twinPeriod ord) α β =
      if ord α = ord β then (Nat.totient (ord α) : ℝ) else 0 := by
  simp only [cesaroGram, Matrix.of_apply, periodMean]
  rw [sum_ramanujanMode_mul (hord α) (hord β) (dvd_twinPeriod ord α) (dvd_twinPeriod ord β)]
  split_ifs with h
  · subst h
    have hq : (0 : ℝ) < twinPeriod ord := by exact_mod_cast prod_pos fun γ _ => hord γ
    exact mul_div_cancel_left₀ _ hq.ne'
  · simp

/-- Closed-form Cesàro Gram matrix of torsion-aligned Ramanujan modes `k ↦ ramanujanMode (ord α) (k + 1)`. -/
theorem cesaroGram_torsionAligned_ramanujanMode_eq {N : ℕ} (ord : Fin N → ℕ)
    (hord : ∀ α, 0 < ord α) (α β : Fin N) :
    cesaroGram (fun γ k => ramanujanMode (ord γ) (k + 1)) (twinPeriod ord) α β =
      if ord α = ord β then (Nat.totient (ord α) : ℝ) else 0 := by
  have hper : ∀ k, ramanujanMode (ord α) k * ramanujanMode (ord β) k =
      (fun j => ramanujanMode (ord α) j * ramanujanMode (ord β) j) k := fun _ => rfl
  have hp_prod : ∀ k,
      ramanujanMode (ord α) (k + twinPeriod ord) * ramanujanMode (ord β) (k + twinPeriod ord) =
        ramanujanMode (ord α) k * ramanujanMode (ord β) k := by
    intro k
    rw [ramanujanMode_twinPeriodic ord hord α k, ramanujanMode_twinPeriodic ord hord β k]
  have hshift := sum_range_shift_of_periodic hp_prod 1
  have h1 : (∑ k ∈ range (twinPeriod ord),
      ramanujanMode (ord α) (k + 1) * ramanujanMode (ord β) (k + 1)) =
      ∑ k ∈ range (twinPeriod ord), ramanujanMode (ord α) k * ramanujanMode (ord β) k := by
    rw [← hshift]
    exact sum_congr rfl fun k _ => by rw [Nat.add_comm 1 k]
  rw [← cesaroGram_ramanujanMode_eq ord hord α β]
  simp only [cesaroGram, Matrix.of_apply, periodMean, h1]

/-- **Closed-Form Cesàro Gram of the Even-Shift Parity-Twin Germ:**
For `0 < ord α` and `¬ 4 ∣ ord α`, the Cesàro Gram of `k ↦ ramanujanMode (ord α) (2 * k)` over
`∏ γ, oddCore (ord γ)` equals `φ(oddCore (ord α))` on shared odd-core fibers and `0` otherwise. -/
theorem cesaroGram_evenShift_ramanujanMode_eq {N : ℕ} (ord : Fin N → ℕ)
    (hord : ∀ α, 0 < ord α) (hn4 : ∀ α, ¬ 4 ∣ ord α) (α β : Fin N) :
    cesaroGram (fun γ k => ramanujanMode (ord γ) (2 * k)) (∏ γ, oddCore (ord γ)) α β =
      if oddCore (ord α) = oddCore (ord β) then (Nat.totient (oddCore (ord α)) : ℝ) else 0 := by
  have hcore : ∀ γ, 0 < oddCore (ord γ) := fun γ => (oddCore_odd_and_pos (hord γ) (hn4 γ)).1
  have hmode : (fun γ k => ramanujanMode (ord γ) (2 * k)) =
      fun γ k => ramanujanMode (oddCore (ord γ)) k :=
    funext fun γ => funext fun k => ramanujanMode_evenShift_eq_oddCore (hord γ) (hn4 γ) k
  rw [hmode]
  exact cesaroGram_ramanujanMode_eq (fun γ => oddCore (ord γ)) hcore α β

/-- **Scheme-Independent Survival Cone of the Even-Shift Ramanujan Parity-Twin Germ:**
Every renormalization of the even-shift Ramanujan periodic germ (`0 < ord α`, `¬ 4 ∣ ord α`,
`0 < N`) has survival cone **equal** to `{C | ∀ m, ∑_{oddCore(ord α) = m} C α = 0}`. -/
theorem evenShift_ramanujanParityTwin_survivalCone_eq {N : ℕ} (ord : Fin N → ℕ)
    (hord : ∀ α, 0 < ord α) (hn4 : ∀ α, ¬ 4 ∣ ord α) (hN : 0 < N)
    {x : Fin N → ℝ} (hx : ∀ α, 0 ≤ x α) {t : ℝ → ℝ} {C' A' : Matrix (Fin N) (Fin N) ℝ}
    (hC : ∀ α β, Tendsto (fun r =>
      periodicGerm (fun γ k => ramanujanMode (ord γ) (2 * k)) x r α β - t r * C' α β)
        (𝓝[<] 1) (𝓝 (A' α β))) :
    survivalCone C' =
      {C | ∀ m : ℕ, ∑ α ∈ univ.filter (fun α => oddCore (ord α) = m), C α = 0} := by
  have hcore : ∀ γ, 0 < oddCore (ord γ) := fun γ => (oddCore_odd_and_pos (hord γ) (hn4 γ)).1
  have hmode : (fun γ k => ramanujanMode (ord γ) (2 * k)) =
      fun γ k => ramanujanMode (oddCore (ord γ)) k :=
    funext fun γ => funext fun k => ramanujanMode_evenShift_eq_oddCore (hord γ) (hn4 γ) k
  rw [hmode] at hC
  exact ramanujanTwin_survivalCone_eq (fun γ => oddCore (ord γ)) hcore hN hx hC

/-- **Sharp Contrast Between Unrestricted and Even-Shift Survival on a `{q, 2q}` Twin Pair:**
For any odd modulus `q` (`q % 2 = 1`) and node vector `x : Fin 2 → ℝ` (`0 ≤ x α`), placing the
distinct orders `![q, 2 * q]` at the two nodes yields survival cone `{0}` on unrestricted lags,
but yields the nontrivial rank-1 survival line `{C : Fin 2 → ℝ | C 0 + C 1 = 0}` on even lags `2k`. -/
theorem parityTwinPair_unrestricted_vs_evenShift_survivalCone {q : ℕ} (hq_odd : q % 2 = 1)
    {x : Fin 2 → ℝ} (hx : ∀ α, 0 ≤ x α) :
    (∀ {t : ℝ → ℝ} {C' A' : Matrix (Fin 2) (Fin 2) ℝ},
      (∀ α β, Tendsto (fun r =>
        periodicGerm (fun γ => ramanujanMode (![q, 2 * q] γ)) x r α β - t r * C' α β)
          (𝓝[<] 1) (𝓝 (A' α β))) →
        survivalCone C' = {0}) ∧
    (∀ {t : ℝ → ℝ} {C' A' : Matrix (Fin 2) (Fin 2) ℝ},
      (∀ α β, Tendsto (fun r =>
        periodicGerm (fun γ k => ramanujanMode (![q, 2 * q] γ) (2 * k)) x r α β - t r * C' α β)
          (𝓝[<] 1) (𝓝 (A' α β))) →
        survivalCone C' = {C : Fin 2 → ℝ | C 0 + C 1 = 0}) := by
  have hq0 : 0 < q := by omega
  have hord : ∀ α : Fin 2, 0 < ![q, 2 * q] α := by
    intro α; fin_cases α <;> simp <;> omega
  have hn4 : ∀ α : Fin 2, ¬ 4 ∣ ![q, 2 * q] α := by
    intro α; fin_cases α <;> simp <;> omega
  have hinj : Function.Injective ![q, 2 * q] := by
    intro α β h
    fin_cases α <;> fin_cases β <;> simp at h ⊢ <;> omega
  have hcore0 : oddCore q = q := by simp [oddCore, hq_odd]
  have hcore1 : oddCore (2 * q) = q := by
    have hev : ¬ ((2 * q) % 2 = 1) := by omega
    simp [oddCore, hev]
  refine ⟨fun hC => ramanujan_survivalCone_eq_zero_of_injective ![q, 2 * q] hord hinj two_pos hx hC,
    fun hC => ?_⟩
  rw [evenShift_ramanujanParityTwin_survivalCone_eq ![q, 2 * q] hord hn4 two_pos hx hC]
  ext C
  simp only [Set.mem_setOf_eq]
  have hcore_eq : ∀ α : Fin 2, oddCore (![q, 2 * q] α) = q := by
    intro α; fin_cases α <;> simp [hcore0, hcore1]
  simp_rw [hcore_eq]
  constructor
  · intro h
    have hq_eq := h q
    simpa [Fin.sum_univ_two] using hq_eq
  · intro h m
    by_cases hm : q = m
    · subst hm; simpa [Fin.sum_univ_two] using h
    · simp [hm]

/-! ## §2. Arithmetic-Progression Germ Limits (`[L ∣ k]` and `[L ∣ k + 1]`) -/

/-- Scale-logarithm limit: `log(1 - r^L) - log(1 - r) → log L` as `r → 1⁻` for `0 < L`. -/
theorem tendsto_log_one_sub_pow_sub_log {L : ℕ} (hL : 0 < L) :
    Tendsto (fun r : ℝ => Real.log (1 - r ^ L) - Real.log (1 - r)) (𝓝[<] 1)
      (𝓝 (Real.log (L : ℝ))) := by
  have hsum_cont : Continuous fun r : ℝ => ∑ i ∈ range L, r ^ i :=
    continuous_finset_sum _ fun i _ => continuous_pow i
  have hsum_one : (∑ i ∈ range L, (1 : ℝ) ^ i) = (L : ℝ) := by simp
  have hL_ne : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hlim : Tendsto (fun r : ℝ => Real.log (∑ i ∈ range L, r ^ i)) (𝓝[<] 1)
      (𝓝 (Real.log (L : ℝ))) := by
    have hc : ContinuousAt (fun r : ℝ => Real.log (∑ i ∈ range L, r ^ i)) 1 :=
      (hsum_cont.continuousAt.log (by rw [hsum_one]; exact hL_ne))
    simpa [hsum_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  have hr1 : 0 < 1 - r := sub_pos.mpr hr.2
  have hgeom_pos : 0 < ∑ i ∈ range L, r ^ i := by
    rcases Nat.exists_eq_succ_of_ne_zero hL.ne' with ⟨m, rfl⟩
    rw [Finset.sum_range_succ']
    have hnn : 0 ≤ ∑ i ∈ range m, r ^ (i + 1) :=
      sum_nonneg fun i _ => pow_nonneg hr.1.le _
    linarith [pow_zero r]
  have hfac : 1 - r ^ L = (1 - r) * ∑ i ∈ range L, r ^ i := by
    have h := geom_sum_mul_neg r L
    linarith
  rw [hfac, Real.log_mul hr1.ne' hgeom_pos.ne']
  ring

/-- `r ↦ r^L` maps `𝓝[<] 1` into `𝓝[<] 1` for `0 < L`. -/
private theorem tendsto_pow_nhdsLT_one {L : ℕ} (hL : 0 < L) :
    Tendsto (fun r : ℝ => r ^ L) (𝓝[<] 1) (𝓝[<] 1) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · simpa using ((continuous_pow L).tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
    exact Set.mem_Iio.mpr (pow_lt_one₀ hr.1.le hr.2 hL.ne')

/-- Exact `HasSum` evaluation of the unshifted divisibility germ `∑_{k ≥ 0} r^k [L ∣ k] / (k + w)`. -/
theorem hasSum_divisibilityGerm {L : ℕ} (hL : 0 < L) {r w : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hw : 0 < w) :
    HasSum (fun k : ℕ => r ^ k * (if L ∣ k then (1 : ℝ) else 0) / ((k : ℝ) + w))
      ((1 / (L : ℝ)) * latticeGerm (r ^ L) (w / L)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hlat := (hasSum_latticeGerm (pow_nonneg hr0 L) (pow_lt_one₀ hr0 hr1 hL.ne')
    (div_pos hw hL')).mul_left (1 / (L : ℝ))
  refine (Function.Injective.hasSum_iff (mul_right_injective₀ hL.ne') ?_).mp ?_
  · intro k hk
    have hnd : ¬ L ∣ k := by
      rintro ⟨j, rfl⟩
      exact hk ⟨j, rfl⟩
    simp [hnd]
  · refine hlat.congr_fun fun j => ?_
    change r ^ (L * j) * (if L ∣ L * j then (1 : ℝ) else 0) / (((L * j : ℕ) : ℝ) + w) = _
    rw [if_pos (dvd_mul_right L j), mul_one, pow_mul, Nat.cast_mul]
    field_simp [hL'.ne']

/-- **Renormalized Limit of the Unshifted Divisibility Germ (`[L ∣ k]`):**
For `0 < L` and `0 < w`,
`∑' k, r^k [L ∣ k] / (k + w) + (1 / L) log(1 - r) → (-(digamma (w / L)).re - γ - log L) / L`. -/
theorem tendsto_divisibilityGerm_add_log {L : ℕ} (hL : 0 < L) {w : ℝ} (hw : 0 < w) :
    Tendsto (fun r : ℝ =>
      (∑' k : ℕ, r ^ k * (if L ∣ k then (1 : ℝ) else 0) / ((k : ℝ) + w)) +
        (1 / (L : ℝ)) * Real.log (1 - r))
      (𝓝[<] 1)
      (𝓝 (((-((Complex.digamma ((w / (L : ℝ) : ℝ) : ℂ)).re +
        Real.eulerMascheroniConstant) - Real.log (L : ℝ)) / (L : ℝ)))) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hwL : 0 < w / (L : ℝ) := div_pos hw hL'
  have h1 := ((tendsto_latticeGerm_add_log hwL).comp (tendsto_pow_nhdsLT_one hL)).div_const (L : ℝ)
  rw [latticeGermLimit_eq hwL] at h1
  have h2 := (tendsto_log_one_sub_pow_sub_log hL).div_const (L : ℝ)
  have hsub := h1.sub h2
  rw [sub_div] at hsub
  refine hsub.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  rw [(hasSum_divisibilityGerm hL hr.1.le hr.2 hw).tsum_eq]
  dsimp only [Function.comp_def]
  field_simp [hL'.ne']
  ring

/-- Exact `HasSum` evaluation of the torsion-aligned divisibility germ
`∑_{k ≥ 0} r^k [L ∣ k + 1] / (k + 1 + u)`. -/
theorem hasSum_shiftedDivisibilityGerm {L : ℕ} (hL : 0 < L) {r u : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hu : -(L : ℝ) < u) :
    HasSum (fun k : ℕ => r ^ k * (if L ∣ k + 1 then (1 : ℝ) else 0) / ((k : ℝ) + 1 + u))
      ((r ^ (L - 1) / (L : ℝ)) * latticeGerm (r ^ L) (1 + u / L)) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hz : 0 < 1 + u / (L : ℝ) := by
    rw [show (1 : ℝ) + u / L = (L + u) / L by field_simp [hL'.ne']]
    exact div_pos (by linarith) hL'
  have hlat := (hasSum_latticeGerm (pow_nonneg hr0 L) (pow_lt_one₀ hr0 hr1 hL.ne') hz).mul_left
    (r ^ (L - 1) / (L : ℝ))
  have hinj : Function.Injective (fun j : ℕ => L * j + (L - 1)) := by
    intro j₁ j₂ h
    exact mul_left_cancel₀ hL.ne' (Nat.add_right_cancel h)
  refine (Function.Injective.hasSum_iff hinj ?_).mp ?_
  · intro k hk
    have hnd : ¬ L ∣ k + 1 := by
      rintro ⟨m, hm⟩
      have hm1 : 1 ≤ m := by omega
      apply hk
      refine ⟨m - 1, ?_⟩
      have hmul : L * (m - 1) + L = L * m := by
        rcases Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0) with ⟨j, rfl⟩
        simp [Nat.mul_succ]
      omega
    simp [hnd]
  · refine hlat.congr_fun fun j => ?_
    change r ^ (L * j + (L - 1)) * (if L ∣ (L * j + (L - 1)) + 1 then (1 : ℝ) else 0) /
      (((L * j + (L - 1) : ℕ) : ℝ) + 1 + u) = _
    have hidx : (L * j + (L - 1)) + 1 = L * (j + 1) := by
      rw [Nat.add_assoc, Nat.sub_add_cancel hL, Nat.mul_succ]
    have hdvd : L ∣ (L * j + (L - 1)) + 1 := ⟨j + 1, hidx⟩
    have hcast : ((L * j + (L - 1) : ℕ) : ℝ) + 1 = (L : ℝ) * ((j : ℝ) + 1) := by
      exact_mod_cast hidx
    rw [if_pos hdvd, mul_one, pow_add, pow_mul, hcast]
    field_simp [hL'.ne']
    ring

/-- **Renormalized Limit of the Torsion-Aligned Divisibility Germ (`[L ∣ k + 1]`):**
For `0 < L` and `-(L : ℝ) < u` (in particular `0 ≤ u`),
`∑' k, r^k [L ∣ k + 1] / (k + 1 + u) + (1 / L) log(1 - r) → (-harmonicFn(u / L) - log L) / L`. -/
theorem tendsto_shiftedDivisibilityGerm_add_log {L : ℕ} (hL : 0 < L) {u : ℝ} (hu : -(L : ℝ) < u) :
    Tendsto (fun r : ℝ =>
      (∑' k : ℕ, r ^ k * (if L ∣ k + 1 then (1 : ℝ) else 0) / ((k : ℝ) + 1 + u)) +
        (1 / (L : ℝ)) * Real.log (1 - r))
      (𝓝[<] 1)
      (𝓝 ((-harmonicFn (u / (L : ℝ)) - Real.log (L : ℝ)) / (L : ℝ))) := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hz : 0 < 1 + u / (L : ℝ) := by
    rw [show (1 : ℝ) + u / L = (L + u) / L by field_simp [hL'.ne']]
    exact div_pos (by linarith) hL'
  have hr_pow : Tendsto (fun r : ℝ => r ^ (L - 1) / (L : ℝ)) (𝓝[<] 1) (𝓝 (1 / (L : ℝ))) := by
    simpa using (((continuous_pow (L - 1)).div_const (L : ℝ)).tendsto 1).mono_left nhdsWithin_le_nhds
  have hlat := (tendsto_latticeGerm_add_log hz).comp (tendsto_pow_nhdsLT_one hL)
  rw [latticeGermLimit_eq hz] at hlat
  have hterm1 := hr_pow.mul hlat
  have hterm2 := hr_pow.mul (tendsto_log_one_sub_pow_sub_log hL)
  have hmullog : Tendsto (fun r : ℝ => (1 - r) * Real.log (1 - r)) (𝓝[<] 1) (𝓝 0) := by
    have hc : Continuous fun r : ℝ => (1 - r) * Real.log (1 - r) :=
      Real.continuous_mul_log.comp (continuous_const.sub continuous_id')
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hgeom_cont : Tendsto (fun r : ℝ => (∑ i ∈ range (L - 1), r ^ i) / (L : ℝ))
      (𝓝[<] 1) (𝓝 (((L - 1 : ℕ) : ℝ) / (L : ℝ))) := by
    have hc : Continuous fun r : ℝ => (∑ i ∈ range (L - 1), r ^ i) / (L : ℝ) :=
      (continuous_finset_sum _ fun i _ => continuous_pow i).div_const _
    simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
  have hterm3 := hgeom_cont.mul hmullog
  have hcomb := (hterm1.sub hterm2).add hterm3
  have htarget :
      (1 / (L : ℝ)) * (-((Complex.digamma ((1 + u / (L : ℝ) : ℝ) : ℂ)).re +
          Real.eulerMascheroniConstant)) -
        (1 / (L : ℝ)) * Real.log (L : ℝ) +
        (((L - 1 : ℕ) : ℝ) / (L : ℝ)) * 0 =
      (-harmonicFn (u / (L : ℝ)) - Real.log (L : ℝ)) / (L : ℝ) := by
    unfold harmonicFn
    ring
  rw [htarget] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  rw [(hasSum_shiftedDivisibilityGerm hL hr.1.le hr.2 hu).tsum_eq]
  dsimp only [Function.comp_def]
  have h1r : (1 - r) * ∑ i ∈ range (L - 1), r ^ i = 1 - r ^ (L - 1) := by
    have h := geom_sum_mul_neg r (L - 1)
    linarith
  have halg : (∑ i ∈ range (L - 1), r ^ i) / (L : ℝ) * ((1 - r) * Real.log (1 - r)) =
      (1 - r ^ (L - 1)) / (L : ℝ) * Real.log (1 - r) := by
    rw [show (∑ i ∈ range (L - 1), r ^ i) / (L : ℝ) * ((1 - r) * Real.log (1 - r)) =
      ((1 - r) * ∑ i ∈ range (L - 1), r ^ i) / (L : ℝ) * Real.log (1 - r) by ring, h1r]
  rw [halg]
  field_simp [hL'.ne']
  ring

/-! ## §3. Closed-Form Twisted Digamma and Cyclotomic-Harmonic Limit Matrices -/

/-- The cyclotomic digamma kernel:
`∑_{b ∣ n} μ(n/b) ∑_{a ∣ m} μ(m/a) gcd(a, b) (Re ψ(w / lcm(a, b)) + γ)`. -/
def cyclotomicDigamma (m n : ℕ) (w : ℝ) : ℝ :=
  doubleMoebius m n fun a b =>
    (Nat.gcd a b : ℝ) *
      ((Complex.digamma ((w / (Nat.lcm a b : ℝ) : ℝ) : ℂ)).re + Real.eulerMascheroniConstant)

/-- The cyclotomic harmonic kernel:
`∑_{b ∣ n} μ(n/b) ∑_{a ∣ m} μ(m/a) gcd(a, b) H(u / lcm(a, b))`. -/
def cyclotomicHarmonic (m n : ℕ) (u : ℝ) : ℝ :=
  doubleMoebius m n fun a b =>
    (Nat.gcd a b : ℝ) * harmonicFn (u / (Nat.lcm a b : ℝ))

theorem cyclotomicHarmonic_zero (m n : ℕ) : cyclotomicHarmonic m n 0 = 0 := by
  have hH0 : harmonicFn 0 = 0 := by simp [harmonicFn, Complex.digamma_one]
  simp [cyclotomicHarmonic, doubleMoebius, zero_div, hH0]

theorem cyclotomicHarmonic_symm (m n : ℕ) (u : ℝ) :
    cyclotomicHarmonic m n u = cyclotomicHarmonic n m u := by
  unfold cyclotomicHarmonic
  rw [doubleMoebius_swap]
  unfold doubleMoebius
  refine sum_congr rfl fun a _ => congrArg _ (sum_congr rfl fun b _ => ?_)
  rw [Nat.gcd_comm, Nat.lcm_comm]

/-- Double Möbius transform of `gcd(a, b)` evaluates to `φ(m) [m = n]`. -/
theorem doubleMoebius_gcd_eq {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    doubleMoebius m n (fun a b => (Nat.gcd a b : ℝ)) =
      if m = n then (Nat.totient m : ℝ) else 0 := by
  rw [doubleMoebius_swap]
  have h1 : ∀ a ∈ m.divisors,
      ∑ b ∈ n.divisors, (μ (n / b) : ℝ) * (Nat.gcd a b : ℝ) =
        if n ∣ a then (Nat.totient n : ℝ) else 0 :=
    fun a _ => sum_moebius_mul_gcd a hn
  rw [sum_congr rfl fun a ha => congrArg ((μ (m / a) : ℝ) * ·) (h1 a ha),
    sum_moebius_ite_dvd hm (fun _ => (Nat.totient n : ℝ))]
  split_ifs with hnm hmn
  · subst hmn
    rw [Nat.div_self hm]
    simp [ArithmeticFunction.moebius_apply_one]
  · have hgt : 1 < m / n := by
      rcases hnm with ⟨k, rfl⟩
      have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
      have hk1 : k ≠ 1 := fun hk1 => hmn (by simp [hk1])
      rw [Nat.mul_div_cancel_left k hn]
      omega
    have hsum := sum_divisors_moebius (Nat.zero_lt_of_lt hgt)
    rw [if_neg hgt.ne'] at hsum
    rw [← sum_mul, hsum, zero_mul]
  · exact absurd (hmn ▸ dvd_refl m) hnm
  · rfl

/-- Product of two Ramanujan modes as a `doubleMoebius` transform of `[lcm(a, b) ∣ t] a b`. -/
theorem ramanujanMode_mul_eq_doubleMoebius {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (t : ℕ) :
    ramanujanMode m t * ramanujanMode n t =
      doubleMoebius m n (fun a b => if Nat.lcm a b ∣ t then (a : ℝ) * b else 0) := by
  have hm_sum : ramanujanMode m t =
      ∑ a ∈ m.divisors, (μ (m / a) : ℝ) * (if a ∣ t then (a : ℝ) else 0) := by
    rw [ramanujanMode_eq_ramanujanLagCoefficient hm t, ramanujanLagCoefficient]
    refine sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [moebiusReal]
  have hn_sum : ramanujanMode n t =
      ∑ b ∈ n.divisors, (μ (n / b) : ℝ) * (if b ∣ t then (b : ℝ) else 0) := by
    rw [ramanujanMode_eq_ramanujanLagCoefficient hn t, ramanujanLagCoefficient]
    refine sum_congr rfl fun b _ => ?_
    split_ifs <;> simp [moebiusReal]
  rw [hm_sum, hn_sum, doubleMoebius_swap]
  rw [sum_mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [Nat.lcm_dvd_iff]
  by_cases ha : a ∣ t <;> by_cases hb : b ∣ t <;> simp [ha, hb] <;> ring

private theorem mul_div_lcm_eq_gcd {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (a : ℝ) * b / (Nat.lcm a b : ℝ) = (Nat.gcd a b : ℝ) := by
  have hlcm_pos : (0 : ℝ) < Nat.lcm a b := by exact_mod_cast Nat.lcm_pos ha hb
  rw [div_eq_iff hlcm_pos.ne']
  exact_mod_cast (Nat.gcd_mul_lcm a b).symm

/-- **Closed-Form Limit Matrix of `evenShift_ramanujanParityTwin`:**
For any `ord : Fin N → ℕ` with `0 < ord α` and `¬ 4 ∣ ord α`, let `q α := oddCore (ord α)`.
For any node map `x : Fin N → ℝ` (`0 ≤ x α`), as `r → 1⁻`,
`periodicGerm (fun γ k => ramanujanMode (ord γ) (2 * k)) x r α β + cesaroGram ... α β * log(1 - r)`
converges to `-orbitIntersection (q α) (q β) - cyclotomicDigamma (q α) (q β) (1 + x α + x β)`. -/
theorem tendsto_evenShift_ramanujanGerm_closedForm {N : ℕ} (ord : Fin N → ℕ)
    (hord : ∀ α, 0 < ord α) (hn4 : ∀ α, ¬ 4 ∣ ord α)
    {x : Fin N → ℝ} (hx : ∀ α, 0 ≤ x α) (α β : Fin N) :
    Tendsto (fun r =>
      periodicGerm (fun γ k => ramanujanMode (ord γ) (2 * k)) x r α β -
        (-Real.log (1 - r)) *
          cesaroGram (fun γ k => ramanujanMode (ord γ) (2 * k)) (∏ γ, oddCore (ord γ)) α β)
      (𝓝[<] 1)
      (𝓝 (-orbitIntersection (oddCore (ord α)) (oddCore (ord β)) -
        cyclotomicDigamma (oddCore (ord α)) (oddCore (ord β)) (1 + x α + x β))) := by
  set m := oddCore (ord α)
  set n := oddCore (ord β)
  set w := 1 + x α + x β
  have hm : 0 < m := (oddCore_odd_and_pos (hord α) (hn4 α)).1
  have hn : 0 < n := (oddCore_odd_and_pos (hord β) (hn4 β)).1
  have hw : 0 < w := by dsimp [w]; linarith [hx α, hx β]
  have hces := cesaroGram_evenShift_ramanujanMode_eq ord hord hn4 α β
  change _ = if m = n then (Nat.totient m : ℝ) else 0 at hces
  rw [← doubleMoebius_gcd_eq hm hn] at hces
  have hlim_ab : ∀ b ∈ n.divisors, ∀ a ∈ m.divisors,
      Tendsto (fun r : ℝ =>
        (a : ℝ) * b *
            (∑' k : ℕ, r ^ k * (if Nat.lcm a b ∣ k then (1 : ℝ) else 0) / ((k : ℝ) + w)) +
          (Nat.gcd a b : ℝ) * Real.log (1 - r))
        (𝓝[<] 1)
        (𝓝 (-logEnergy a b -
          (Nat.gcd a b : ℝ) *
            ((Complex.digamma ((w / (Nat.lcm a b : ℝ) : ℝ) : ℂ)).re +
              Real.eulerMascheroniConstant))) := by
    intro b hb a ha
    have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
    have hb0 : 0 < b := Nat.pos_of_mem_divisors hb
    have hL : 0 < Nat.lcm a b := Nat.lcm_pos ha0 hb0
    have hL' : (0 : ℝ) < Nat.lcm a b := by exact_mod_cast hL
    have hdiv := (tendsto_divisibilityGerm_add_log hL hw).const_mul ((a : ℝ) * b)
    have hgcd := mul_div_lcm_eq_gcd ha0 hb0
    have hJ : logEnergy a b = (Nat.gcd a b : ℝ) * Real.log (Nat.lcm a b : ℝ) :=
      logEnergy_eq ha0 hb0
    have hval : ((a : ℝ) * b) *
        ((-((Complex.digamma ((w / (Nat.lcm a b : ℝ) : ℝ) : ℂ)).re +
            Real.eulerMascheroniConstant) - Real.log (Nat.lcm a b : ℝ)) /
          (Nat.lcm a b : ℝ)) =
        -logEnergy a b -
          (Nat.gcd a b : ℝ) *
            ((Complex.digamma ((w / (Nat.lcm a b : ℝ) : ℝ) : ℂ)).re +
              Real.eulerMascheroniConstant) := by
      rw [hJ, ← hgcd]
      field_simp [hL'.ne']
      ring
    rw [hval] at hdiv
    refine hdiv.congr' (Eventually.of_forall fun r => ?_)
    dsimp only
    rw [mul_add, ← mul_assoc, show ((a : ℝ) * b) * (1 / (Nat.lcm a b : ℝ)) =
      (a : ℝ) * b / (Nat.lcm a b : ℝ) by ring, hgcd]
  have hsum_lim : Tendsto (fun r : ℝ =>
      ∑ b ∈ n.divisors, (μ (n / b) : ℝ) * ∑ a ∈ m.divisors, (μ (m / a) : ℝ) *
        ((a : ℝ) * b *
            (∑' k : ℕ, r ^ k * (if Nat.lcm a b ∣ k then (1 : ℝ) else 0) / ((k : ℝ) + w)) +
          (Nat.gcd a b : ℝ) * Real.log (1 - r)))
      (𝓝[<] 1)
      (𝓝 (-orbitIntersection m n - cyclotomicDigamma m n w)) := by
    have h := tendsto_finset_sum n.divisors fun b hb =>
      (tendsto_finset_sum m.divisors fun a ha =>
        (hlim_ab b hb a ha).const_mul (μ (m / a) : ℝ)).const_mul (μ (n / b) : ℝ)
    have htarget : (∑ b ∈ n.divisors, (μ (n / b) : ℝ) * ∑ a ∈ m.divisors, (μ (m / a) : ℝ) *
        (-logEnergy a b -
          (Nat.gcd a b : ℝ) *
            ((Complex.digamma ((w / (Nat.lcm a b : ℝ) : ℝ) : ℂ)).re +
              Real.eulerMascheroniConstant))) =
        -orbitIntersection m n - cyclotomicDigamma m n w := by
      rw [orbitIntersection_eq_doubleMoebius hm hn]
      simp only [cyclotomicDigamma, doubleMoebius, mul_sub, sum_sub_distrib, mul_neg,
        sum_neg_distrib, neg_sub_left]
      ring
    rwa [htarget] at h
  refine hsum_lim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  have hhas : HasSum (fun k : ℕ =>
      r ^ k * (ramanujanMode m k * ramanujanMode n k) / ((k : ℝ) + w))
      (∑ b ∈ n.divisors, (μ (n / b) : ℝ) * ∑ a ∈ m.divisors, (μ (m / a) : ℝ) *
        ((a : ℝ) * b *
          ∑' k : ℕ, r ^ k * (if Nat.lcm a b ∣ k then (1 : ℝ) else 0) / ((k : ℝ) + w))) := by
    have hinner : ∀ b ∈ n.divisors, ∀ a ∈ m.divisors,
        HasSum (fun k : ℕ => (μ (n / b) : ℝ) * ((μ (m / a) : ℝ) *
          (r ^ k * (if Nat.lcm a b ∣ k then (a : ℝ) * b else 0) / ((k : ℝ) + w))))
          ((μ (n / b) : ℝ) * ((μ (m / a) : ℝ) *
            ((a : ℝ) * b *
              ∑' k : ℕ, r ^ k * (if Nat.lcm a b ∣ k then (1 : ℝ) else 0) / ((k : ℝ) + w)))) := by
      intro b hb a ha
      have hL : 0 < Nat.lcm a b := Nat.lcm_pos (Nat.pos_of_mem_divisors ha) (Nat.pos_of_mem_divisors hb)
      have hs := hasSum_divisibilityGerm hL hr.1.le hr.2 hw
      rw [hs.tsum_eq]
      refine ((hs.mul_left ((a : ℝ) * b)).mul_left (μ (m / a) : ℝ) |>.mul_left (μ (n / b) : ℝ)).congr_fun
        fun k => ?_
      by_cases hd : Nat.lcm a b ∣ k <;> simp [hd] <;> ring
    have h2 := hasSum_sum fun b hb => hasSum_sum fun a ha => hinner b hb a ha
    simp_rw [← mul_sum] at h2
    refine h2.congr_fun fun k => ?_
    rw [ramanujanMode_mul_eq_doubleMoebius hm hn k]
    simp only [doubleMoebius, mul_sum, sum_div]
    exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by ring
  have hpg : periodicGerm (fun γ k => ramanujanMode (ord γ) (2 * k)) x r α β =
      ∑' k : ℕ, r ^ k * (ramanujanMode m k * ramanujanMode n k) / ((k : ℝ) + w) := by
    simp only [periodicGerm, Matrix.of_apply, twistedGerm]
    refine tsum_congr fun k => ?_
    rw [ramanujanMode_evenShift_eq_oddCore (hord α) (hn4 α) k,
      ramanujanMode_evenShift_eq_oddCore (hord β) (hn4 β) k]
  rw [hpg, hhas.tsum_eq, hces]
  simp only [doubleMoebius, mul_add, sum_add_distrib, mul_sum]
  refine Eq.trans ?_ (by ring)
  congr 1
  · exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by ring
  · rw [neg_neg, mul_comm (Real.log (1 - r)), mul_sum]
    exact sum_congr rfl fun b _ => by
      rw [mul_sum]
      exact sum_congr rfl fun a _ => by ring

/-- **Closed-Form Limit Matrix of Torsion-Aligned Ramanujan Germs (`k + 1`):**
For any `ord : Fin N → ℕ` (`0 < ord α`) and `x : Fin N → ℝ` (`0 ≤ x α`), the torsion-aligned
periodic germ `k ↦ ramanujanMode (ord α) (k + 1)` renormalizes as `r → 1⁻` to
`-orbitIntersection (ord α) (ord β) - cyclotomicHarmonic (ord α) (ord β) (x α + x β)`.
At the pole nodes `x α = x β = 0`, this limit equals `-orbitIntersection (ord α) (ord β)`. -/
theorem tendsto_torsionAligned_ramanujanGerm_closedForm {N : ℕ} (ord : Fin N → ℕ)
    (hord : ∀ α, 0 < ord α) {x : Fin N → ℝ} (hx : ∀ α, 0 ≤ x α) (α β : Fin N) :
    Tendsto (fun r =>
      periodicGerm (fun γ k => ramanujanMode (ord γ) (k + 1)) x r α β -
        (-Real.log (1 - r)) *
          cesaroGram (fun γ k => ramanujanMode (ord γ) (k + 1)) (twinPeriod ord) α β)
      (𝓝[<] 1)
      (𝓝 (-orbitIntersection (ord α) (ord β) -
        cyclotomicHarmonic (ord α) (ord β) (x α + x β))) := by
  set m := ord α
  set n := ord β
  set u := x α + x β
  have hm : 0 < m := hord α
  have hn : 0 < n := hord β
  have hu0 : 0 ≤ u := add_nonneg (hx α) (hx β)
  have hces := cesaroGram_torsionAligned_ramanujanMode_eq ord hord α β
  change _ = if m = n then (Nat.totient m : ℝ) else 0 at hces
  rw [← doubleMoebius_gcd_eq hm hn] at hces
  have hlim_ab : ∀ b ∈ n.divisors, ∀ a ∈ m.divisors,
      Tendsto (fun r : ℝ =>
        (a : ℝ) * b *
            (∑' k : ℕ, r ^ k * (if Nat.lcm a b ∣ k + 1 then (1 : ℝ) else 0) / ((k : ℝ) + 1 + u)) +
          (Nat.gcd a b : ℝ) * Real.log (1 - r))
        (𝓝[<] 1)
        (𝓝 (-logEnergy a b -
          (Nat.gcd a b : ℝ) * harmonicFn (u / (Nat.lcm a b : ℝ)))) := by
    intro b hb a ha
    have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
    have hb0 : 0 < b := Nat.pos_of_mem_divisors hb
    have hL : 0 < Nat.lcm a b := Nat.lcm_pos ha0 hb0
    have hL' : (0 : ℝ) < Nat.lcm a b := by exact_mod_cast hL
    have huL : -(Nat.lcm a b : ℝ) < u := by linarith
    have hdiv := (tendsto_shiftedDivisibilityGerm_add_log hL huL).const_mul ((a : ℝ) * b)
    have hgcd := mul_div_lcm_eq_gcd ha0 hb0
    have hJ : logEnergy a b = (Nat.gcd a b : ℝ) * Real.log (Nat.lcm a b : ℝ) :=
      logEnergy_eq ha0 hb0
    have hval : ((a : ℝ) * b) *
        ((-harmonicFn (u / (Nat.lcm a b : ℝ)) - Real.log (Nat.lcm a b : ℝ)) /
          (Nat.lcm a b : ℝ)) =
        -logEnergy a b - (Nat.gcd a b : ℝ) * harmonicFn (u / (Nat.lcm a b : ℝ)) := by
      rw [hJ, ← hgcd]
      field_simp [hL'.ne']
      ring
    rw [hval] at hdiv
    refine hdiv.congr' (Eventually.of_forall fun r => ?_)
    dsimp only
    rw [mul_add, ← mul_assoc, show ((a : ℝ) * b) * (1 / (Nat.lcm a b : ℝ)) =
      (a : ℝ) * b / (Nat.lcm a b : ℝ) by ring, hgcd]
  have hsum_lim : Tendsto (fun r : ℝ =>
      ∑ b ∈ n.divisors, (μ (n / b) : ℝ) * ∑ a ∈ m.divisors, (μ (m / a) : ℝ) *
        ((a : ℝ) * b *
            (∑' k : ℕ, r ^ k * (if Nat.lcm a b ∣ k + 1 then (1 : ℝ) else 0) / ((k : ℝ) + 1 + u)) +
          (Nat.gcd a b : ℝ) * Real.log (1 - r)))
      (𝓝[<] 1)
      (𝓝 (-orbitIntersection m n - cyclotomicHarmonic m n u)) := by
    have h := tendsto_finset_sum n.divisors fun b hb =>
      (tendsto_finset_sum m.divisors fun a ha =>
        (hlim_ab b hb a ha).const_mul (μ (m / a) : ℝ)).const_mul (μ (n / b) : ℝ)
    have htarget : (∑ b ∈ n.divisors, (μ (n / b) : ℝ) * ∑ a ∈ m.divisors, (μ (m / a) : ℝ) *
        (-logEnergy a b - (Nat.gcd a b : ℝ) * harmonicFn (u / (Nat.lcm a b : ℝ)))) =
        -orbitIntersection m n - cyclotomicHarmonic m n u := by
      rw [orbitIntersection_eq_doubleMoebius hm hn]
      simp only [cyclotomicHarmonic, doubleMoebius, mul_sub, sum_sub_distrib, mul_neg,
        sum_neg_distrib, neg_sub_left]
      ring
    rwa [htarget] at h
  refine hsum_lim.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  have hhas : HasSum (fun k : ℕ =>
      r ^ k * (ramanujanMode m (k + 1) * ramanujanMode n (k + 1)) / ((k : ℝ) + (1 + u)))
      (∑ b ∈ n.divisors, (μ (n / b) : ℝ) * ∑ a ∈ m.divisors, (μ (m / a) : ℝ) *
        ((a : ℝ) * b *
          ∑' k : ℕ, r ^ k * (if Nat.lcm a b ∣ k + 1 then (1 : ℝ) else 0) / ((k : ℝ) + 1 + u))) := by
    have hinner : ∀ b ∈ n.divisors, ∀ a ∈ m.divisors,
        HasSum (fun k : ℕ => (μ (n / b) : ℝ) * ((μ (m / a) : ℝ) *
          (r ^ k * (if Nat.lcm a b ∣ k + 1 then (a : ℝ) * b else 0) / ((k : ℝ) + (1 + u)))))
          ((μ (n / b) : ℝ) * ((μ (m / a) : ℝ) *
            ((a : ℝ) * b *
              ∑' k : ℕ, r ^ k * (if Nat.lcm a b ∣ k + 1 then (1 : ℝ) else 0) / ((k : ℝ) + 1 + u)))) := by
      intro b hb a ha
      have ha0 : 0 < a := Nat.pos_of_mem_divisors ha
      have hb0 : 0 < b := Nat.pos_of_mem_divisors hb
      have hL : 0 < Nat.lcm a b := Nat.lcm_pos ha0 hb0
      have hL' : (0 : ℝ) < Nat.lcm a b := by exact_mod_cast hL
      have hs := hasSum_shiftedDivisibilityGerm hL hr.1.le hr.2 (by linarith : -(Nat.lcm a b : ℝ) < u)
      rw [hs.tsum_eq]
      refine ((hs.mul_left ((a : ℝ) * b)).mul_left (μ (m / a) : ℝ) |>.mul_left (μ (n / b) : ℝ)).congr_fun
        fun k => ?_
      rw [show (k : ℝ) + (1 + u) = (k : ℝ) + 1 + u by ring]
      by_cases hd : Nat.lcm a b ∣ k + 1 <;> simp [hd] <;> ring
    have h2 := hasSum_sum fun b hb => hasSum_sum fun a ha => hinner b hb a ha
    simp_rw [← mul_sum] at h2
    refine h2.congr_fun fun k => ?_
    rw [ramanujanMode_mul_eq_doubleMoebius hm hn (k + 1)]
    simp only [doubleMoebius, mul_sum, sum_div]
    exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by ring
  have hpg : periodicGerm (fun γ k => ramanujanMode (ord γ) (k + 1)) x r α β =
      ∑' k : ℕ, r ^ k * (ramanujanMode m (k + 1) * ramanujanMode n (k + 1)) / ((k : ℝ) + (1 + u)) := by
    simp only [periodicGerm, Matrix.of_apply, twistedGerm, u, add_assoc]
  rw [hpg, hhas.tsum_eq, hces]
  simp only [doubleMoebius, mul_add, sum_add_distrib, mul_sum]
  refine Eq.trans ?_ (by ring)
  congr 1
  · exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by ring
  · rw [neg_neg, mul_comm (Real.log (1 - r)), mul_sum]
    exact sum_congr rfl fun b _ => by
      rw [mul_sum]
      exact sum_congr rfl fun a _ => by ring

/-! ## §4. Exact Obstruction (`RBG` Open Topic #1): Pole-Node Erasure of `orbitIntersection` -/

/-- **Pole-Node Erasure Law:**
Any kernel `K (q α) (q β)` that depends only on the discrete fiber map `q : Fin N → ℕ` (and is
independent of the continuous nodes `x α`) pairs to `0` identically on the survival cone
`∀ m, ∑_{q α = m} C α = 0` — including after adjoining pole nodes `x = 0` to each fiber. -/
theorem poleNode_erasure_of_nodeIndependent_kernel {N : ℕ} (q : Fin N → ℕ) (K : ℕ → ℕ → ℝ)
    {C : Fin N → ℝ} (hC : ∀ m : ℕ, ∑ α ∈ univ.filter (fun α => q α = m), C α = 0) :
    quad (Matrix.of fun α β => K (q α) (q β)) C = 0 := by
  classical
  simp only [quad, Matrix.of_apply]
  rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image q) (g := q)
    (fun α _ => mem_image_of_mem q (mem_univ α))]
  refine sum_eq_zero fun m _ => ?_
  have hinner : ∀ α ∈ univ.filter (fun α => q α = m),
      ∑ β, C α * K (q α) (q β) * C β =
        C α * ∑ n ∈ univ.image q, K m n * ∑ β ∈ univ.filter (fun β => q β = n), C β := by
    intro α hα
    rw [(mem_filter.mp hα).2, mul_sum]
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := univ.image q) (g := q)
      (fun β _ => mem_image_of_mem q (mem_univ β))]
    refine sum_congr rfl fun n _ => ?_
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun β hβ => ?_
    rw [(mem_filter.mp hβ).2]
    ring
  rw [sum_congr rfl hinner, ← sum_mul, hC m, zero_mul]

/-- **Exact Erasure of `-orbitIntersection` (`Λ(t)`) on the Survival Cone:**
On the survival cone of either the torsion-aligned Ramanujan germ (`q α = ord α`) or the
even-shifted parity-twin germ (`q α = oddCore (ord α)`), the prime-side torsion intersection
`-orbitIntersection (q α) (q β)` drops out identically, reducing the renormalized quadratic form
to the purely cyclotomic-archimedean form `-∑_{α, β} C α C β cyclotomicHarmonic (q α) (q β) (x α + x β)`
(and likewise `-cyclotomicDigamma` in the unshifted convention). -/
theorem quad_torsionAlignedLimit_eq_neg_cyclotomicHarmonic_on_cone {N : ℕ}
    (q : Fin N → ℕ) (x : Fin N → ℝ) {C : Fin N → ℝ}
    (hC : ∀ m : ℕ, ∑ α ∈ univ.filter (fun α => q α = m), C α = 0) :
    quad (Matrix.of fun α β =>
        -orbitIntersection (q α) (q β) - cyclotomicHarmonic (q α) (q β) (x α + x β)) C =
      -∑ α, ∑ β, C α * C β * cyclotomicHarmonic (q α) (q β) (x α + x β) := by
  have herase := poleNode_erasure_of_nodeIndependent_kernel q
    (fun m n => -orbitIntersection m n) hC
  simp only [quad, Matrix.of_apply] at herase ⊢
  have hsplit : (∑ α, ∑ β,
      C α * (-orbitIntersection (q α) (q β) - cyclotomicHarmonic (q α) (q β) (x α + x β)) * C β) =
      (∑ α, ∑ β, C α * (-orbitIntersection (q α) (q β)) * C β) -
        ∑ α, ∑ β, C α * C β * cyclotomicHarmonic (q α) (q β) (x α + x β) := by
    simp only [ ← sum_sub_distrib]
    exact sum_congr rfl fun α _ => sum_congr rfl fun β _ => by ring
  rw [hsplit, herase, zero_sub]

theorem quad_evenShiftLimit_eq_neg_cyclotomicDigamma_on_cone {N : ℕ}
    (ord : Fin N → ℕ) (x : Fin N → ℝ) {C : Fin N → ℝ}
    (hC : ∀ m : ℕ, ∑ α ∈ univ.filter (fun α => oddCore (ord α) = m), C α = 0) :
    quad (Matrix.of fun α β =>
        -orbitIntersection (oddCore (ord α)) (oddCore (ord β)) -
          cyclotomicDigamma (oddCore (ord α)) (oddCore (ord β)) (1 + x α + x β)) C =
      -∑ α, ∑ β, C α * C β *
        cyclotomicDigamma (oddCore (ord α)) (oddCore (ord β)) (1 + x α + x β) := by
  have herase := poleNode_erasure_of_nodeIndependent_kernel (fun α => oddCore (ord α))
    (fun m n => -orbitIntersection m n) hC
  simp only [quad, Matrix.of_apply] at herase ⊢
  have hsplit : (∑ α, ∑ β,
      C α * (-orbitIntersection (oddCore (ord α)) (oddCore (ord β)) -
        cyclotomicDigamma (oddCore (ord α)) (oddCore (ord β)) (1 + x α + x β)) * C β) =
      (∑ α, ∑ β, C α * (-orbitIntersection (oddCore (ord α)) (oddCore (ord β))) * C β) -
        ∑ α, ∑ β, C α * C β *
          cyclotomicDigamma (oddCore (ord α)) (oddCore (ord β)) (1 + x α + x β) := by
    simp only [← sum_sub_distrib]
    exact sum_congr rfl fun α _ => sum_congr rfl fun β _ => by ring
  rw [hsplit, herase, zero_sub]

/-! ## §5. Positive Survivor 1: Unconstrained PSD Cyclotomic-Harmonic Kernel via Pole-Node Completion -/

/-- **Unconstrained Positive Semidefiniteness of the Cyclotomic-Harmonic Kernel:**
Adjoining the pole node `x = 0` to each torsion order `ord i > 0` completes the torsion-aligned
Ramanujan germ into an unconstrained positive semidefinite kernel on `(ℕ_+ × ℝ_{≥0})`:
`0 ≤ ∑_{i, j} c_i c_j (cyclotomicHarmonic (ord i) (ord j) (x i) + cyclotomicHarmonic (ord i) (ord j) (x j) - cyclotomicHarmonic (ord i) (ord j) (x i + x j))`.
At `ord i ≡ 1`, this recovers `RBG.harmonicKernel_nonneg`. -/
theorem cyclotomicHarmonicKernel_nonneg {N : ℕ} {ord : Fin N → ℕ} (hord : ∀ i, 0 < ord i)
    {x : Fin N → ℝ} (hx : ∀ i, 0 ≤ x i) (c : Fin N → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j *
      (cyclotomicHarmonic (ord i) (ord j) (x i) +
        cyclotomicHarmonic (ord i) (ord j) (x j) -
        cyclotomicHarmonic (ord i) (ord j) (x i + x j)) := by
  let ord2 : Fin (N + N) → ℕ := Fin.addCases ord ord
  let x2 : Fin (N + N) → ℝ := Fin.addCases x (fun _ => 0)
  let C2 : Fin (N + N) → ℝ := Fin.addCases c (fun i => -c i)
  have hord2 : ∀ α, 0 < ord2 α := fun α => by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) α <;> simp [ord2, hord i]
  have hx2 : ∀ α, 0 ≤ x2 α := fun α => by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) α
    · simp [x2, hx i]
    · simp [x2]
  have hq : 0 < twinPeriod ord2 := prod_pos fun γ _ => hord2 γ
  have hper : ∀ α, Function.Periodic (fun k => ramanujanMode (ord2 α) (k + 1)) (twinPeriod ord2) :=
    fun α k => by
      have hp := ramanujanMode_twinPeriodic ord2 hord2 α (k + 1)
      rwa [show k + 1 + twinPeriod ord2 = k + twinPeriod ord2 + 1 by ring] at hp
  have hrel : ∀ k, ∑ α : Fin (N + N), C2 α * ramanujanMode (ord2 α) (k + 1) = 0 := by
    intro k
    rw [Fin.sum_univ_add]
    simp only [C2, ord2, Fin.addCases_left, Fin.addCases_right, neg_mul, sum_neg_distrib,
      add_neg_cancel]
  have hQ : ∀ᶠ r in 𝓝[<] (1 : ℝ),
      0 ≤ quad (periodicGerm (fun α k => ramanujanMode (ord2 α) (k + 1)) x2 r) C2 := by
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
    exact periodicGerm_quad_nonneg _ hq hper hx2 hr.1.le hr.2 C2
  let Alim : Matrix (Fin (N + N)) (Fin (N + N)) ℝ := Matrix.of fun α β =>
    -orbitIntersection (ord2 α) (ord2 β) - cyclotomicHarmonic (ord2 α) (ord2 β) (x2 α + x2 β)
  have hlim := fun α β => tendsto_torsionAligned_ramanujanGerm_closedForm ord2 hord2 hx2 α β
  have hnonneg : 0 ≤ quad Alim C2 :=
    quad_nonneg_of_regularized
      (by filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr C
          exact periodicGerm_quad_nonneg _ hq hper hx2 hr.1.le hr.2 C)
      hlim ((mem_survivalCone_cesaroGram_iff _ hq hper C2).mpr hrel)
  have hexpand : quad Alim C2 =
      ∑ i, ∑ j, c i * c j *
        (cyclotomicHarmonic (ord i) (ord j) (x i) +
          cyclotomicHarmonic (ord i) (ord j) (x j) -
          cyclotomicHarmonic (ord i) (ord j) (x i + x j)) := by
    simp only [quad, Alim, Matrix.of_apply]
    rw [Fin.sum_univ_add]
    simp_rw [Fin.sum_univ_add]
    simp only [ord2, x2, C2, Fin.addCases_left, Fin.addCases_right, add_zero, zero_add,
      cyclotomicHarmonic_zero, sub_zero, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    ring
  rwa [hexpand] at hnonneg

/-! ## §6. Positive Survivor 2: Dyadic Parity-Split Scale Anomaly (`I(q, 2q) = φ(q) log 2`) -/

/-- On odd frequencies `2j + 1` and odd moduli `q` (`q % 2 = 1`), the `2q` Ramanujan mode flips
sign relative to `q`: `ramanujanMode (2 * q) (2 * j + 1) = -ramanujanMode q (2 * j + 1)`. -/
theorem ramanujanMode_two_mul_odd_oddShift {q : ℕ} (hq : q % 2 = 1) (j : ℕ) :
    ramanujanMode (2 * q) (2 * j + 1) = -ramanujanMode q (2 * j + 1) := by
  have hq0 : 0 < q := by omega
  have h2q0 : 0 < 2 * q := by omega
  have hφq : (q.totient : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr hq0).ne'
  rw [ramanujanMode_eq_ramanujanLagCoefficient h2q0, ramanujanMode_eq_ramanujanLagCoefficient hq0]
  have hs1 := sieveLagMultiplier_eq_moebius_totient_quotient (q := 2 * q) (h := 2 * j + 1)
  have hs2 := sieveLagMultiplier_eq_moebius_totient_quotient (q := q) (h := 2 * j + 1)
  have hcop2 : Nat.Coprime 2 (2 * j + 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]; omega
  have hgcd : Nat.gcd (2 * q) (2 * j + 1) = Nat.gcd q (2 * j + 1) :=
    hcop2.gcd_mul_left_cancel q
  set g := Nat.gcd q (2 * j + 1)
  have hg_dvd : g ∣ q := Nat.gcd_dvd_left q (2 * j + 1)
  have hg_odd : g % 2 = 1 := by
    by_contra hev
    have : 2 ∣ q := dvd_trans (by omega : 2 ∣ g) hg_dvd
    omega
  have hquot : 2 * q / g = 2 * (q / g) := Nat.mul_div_assoc 2 hg_dvd
  have hq_div_odd : (q / g) % 2 = 1 := by
    have hmul := Nat.div_mul_cancel hg_dvd
    by_contra hev
    have : 2 ∣ q := ⟨(q / g) / 2 * g, by omega⟩
    omega
  have hcop_qg : Nat.Coprime 2 (q / g) := coprime_two_of_odd hq_div_odd
  have hμ : (μ (2 * (q / g)) : ℝ) = -(μ (q / g) : ℝ) := by
    have hm := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_qg
    rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two] at hm
    exact_mod_cast (by linarith : μ (2 * (q / g)) = -μ (q / g))
  have hφ_quot : ((2 * (q / g)).totient : ℝ) = ((q / g).totient : ℝ) := by
    exact_mod_cast totient_two_mul_of_odd hq_div_odd
  have hs_neg : sieveLagMultiplier (2 * q) (2 * j + 1) = -sieveLagMultiplier q (2 * j + 1) := by
    rw [hs1, hs2, hgcd, hquot, hμ, hφ_quot]
    ring
  unfold sieveLagMultiplier at hs_neg
  rw [totient_two_mul_of_odd hq, neg_div] at hs_neg
  exact (div_left_inj' hφq).mp hs_neg

/-- The odd-frequency Abel torsion energy:
`oddTorsionEnergy r m n = ∑' j : ℕ, r^(2j + 1) / (2j + 1) * c_m(2j + 1) c_n(2j + 1)`. -/
def oddTorsionEnergy (r : ℝ) (m n : ℕ) : ℝ :=
  (torsionEnergy r m n - torsionEnergy (-r) m n) / 2

/-- `oddTorsionEnergy r m n` is positive semidefinite for `0 ≤ r < 1`. -/
theorem sum_sum_oddTorsionEnergy_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (S : Finset ℕ) (y : ℕ → ℝ) :
    0 ≤ ∑ m ∈ S, ∑ n ∈ S, y m * y n * oddTorsionEnergy r m n := by
  have hhas : ∀ m n, HasSum (fun j : ℕ =>
      r ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) *
        (ramanujanMode m (2 * j + 1) * ramanujanMode n (2 * j + 1)))
      (oddTorsionEnergy r m n) := by
    intro m n
    have h1 : ∀ z : ℂ, ‖z‖ ≤ 1 →
        HasSum (fun j : ℕ => r ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) * (z ^ (2 * j + 1)).re)
          ((-Real.log ‖1 - (r : ℂ) * z‖ - -Real.log ‖1 - ((-r : ℝ) : ℂ) * z‖) / 2) := by
      intro z hz
      have hp := hasSum_neg_log_norm_one_sub hr0 hr1 hz
      have hnr : ‖((-r : ℝ) : ℂ) * z‖ < 1 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hr0]
        nlinarith [norm_nonneg z]
      have hm_tay := Complex.reCLM.hasSum (Complex.hasSum_taylorSeries_neg_log hnr)
      simp only [Complex.reCLM_apply, Complex.neg_re, Complex.log_re] at hm_tay
      have hm : HasSum (fun k : ℕ => (-r) ^ k / k * (z ^ k).re)
          (-Real.log ‖1 - ((-r : ℝ) : ℂ) * z‖) := by
        refine hm_tay.congr_fun fun k => ?_
        rw [mul_pow, ← Complex.ofReal_pow, ← Complex.ofReal_natCast, Complex.div_ofReal_re,
          Complex.re_ofReal_mul]
        ring
      have hdiff := (hp.sub hm).div_const 2
      have hinj : Function.Injective (fun j : ℕ => 2 * j + 1) := fun a b h => by omega
      refine (Function.Injective.hasSum_iff hinj ?_).mp ?_
      · intro k hk
        have hev : Even k := by
          rcases Nat.even_or_odd k with he | ⟨j, rfl⟩
          · exact he
          · exact absurd ⟨j, rfl⟩ hk
        rcases hev with ⟨j, rfl⟩
        have hpow : (-r) ^ (j + j) = r ^ (j + j) := by
          rw [show j + j = 2 * j by ring, pow_mul, pow_mul, neg_sq]
        simp [hpow]
      · refine hdiff.congr_fun fun j => ?_
        dsimp only [Function.comp_def]
        have hpow : (-r) ^ (2 * j + 1) = -(r ^ (2 * j + 1)) :=
           Odd.neg_pow ⟨j, rfl⟩ r
        rw [hpow]
        ring
    have hsum := hasSum_sum fun ζ (hζ : ζ ∈ primitiveRoots m ℂ) => hasSum_sum
      fun η (hη : η ∈ primitiveRoots n ℂ) => h1 (ζ * conj η) (by
        rw [norm_mul, Complex.norm_conj, norm_of_mem_primitiveRoots hζ,
          norm_of_mem_primitiveRoots hη, one_mul])
    have hval : (∑ ζ ∈ primitiveRoots m ℂ, ∑ η ∈ primitiveRoots n ℂ,
        (-Real.log ‖1 - (r : ℂ) * (ζ * conj η)‖ -
          -Real.log ‖1 - ((-r : ℝ) : ℂ) * (ζ * conj η)‖) / 2) =
        oddTorsionEnergy r m n := by
      simp only [oddTorsionEnergy, torsionEnergy, ← sum_div, ← sum_sub_distrib]
    rw [hval] at hsum
    refine hsum.congr_fun fun j => ?_
    simp only [ramanujanMode, ramanujanSum_eq_ofReal, Complex.ofReal_re]
    have hprod : ramanujanMode m (2 * j + 1) * ramanujanMode n (2 * j + 1) =
        (ramanujanSum m (2 * j + 1) * conj (ramanujanSum n (2 * j + 1))).re := by
      rw [ramanujanSum_eq_ofReal, ramanujanSum_eq_ofReal, Complex.conj_ofReal,
        ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [hprod, ramanujanSum, ramanujanSum, map_sum, sum_mul_sum, Complex.re_sum, mul_sum]
    refine sum_congr rfl fun ζ _ => ?_
    rw [Complex.re_sum, mul_sum]
    refine sum_congr rfl fun η _ => ?_
    rw [mul_pow, map_pow]
  have htot := hasSum_sum fun m (_ : m ∈ S) => hasSum_sum fun n (_ : n ∈ S) =>
    (hhas m n).mul_left (y m * y n)
  refine htot.nonneg fun j => ?_
  have hsq : ∑ m ∈ S, ∑ n ∈ S,
      y m * y n * (r ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) *
        (ramanujanMode m (2 * j + 1) * ramanujanMode n (2 * j + 1))) =
      r ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) *
        (∑ m ∈ S, y m * ramanujanMode m (2 * j + 1)) ^ 2 := by
    rw [sq, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun m _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun n _ => by ring
  rw [hsq]
  exact mul_nonneg (div_nonneg (pow_nonneg hr0 _) (Nat.cast_nonneg _)) (sq_nonneg _)

/-- **Dyadic Parity-Split Identity for `torsionEnergy r q (2 * q)`:**
For every odd modulus `q` (`q % 2 = 1`) and `0 ≤ r < 1`,
`torsionEnergy r q (2 * q) = (1 / 2) * torsionEnergy (r ^ 2) q q - oddTorsionEnergy r q q`. -/
theorem torsionEnergy_dyadic_parity_split {q : ℕ} (hq : q % 2 = 1) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    torsionEnergy r q (2 * q) =
      (1 / 2) * torsionEnergy (r ^ 2) q q - oddTorsionEnergy r q q := by
  have hq0 : 0 < q := by omega
  have h2q0 : 0 < 2 * q := by omega
  have hp := hasSum_torsionEnergy hr0 hr1 q (2 * q)
  -- Also compute `(torsionEnergy r q q + torsionEnergy (-r) q q) / 2 = (1/2) * torsionEnergy (r^2) q q`.
  have heven_qq : (torsionEnergy r q q + torsionEnergy (-r) q q) / 2 =
      (1 / 2) * torsionEnergy (r ^ 2) q q := by
    have hr2_lt : r ^ 2 < 1 := pow_lt_one₀ hr0 hr1 (by norm_num)
    have h_r2 := (hasSum_torsionEnergy (sq_nonneg r) hr2_lt q q).mul_left (1 / 2 : ℝ)
    have h_avg : HasSum (fun k : ℕ =>
        ((r ^ k + (-r) ^ k) / 2) / k * (ramanujanSum q k * conj (ramanujanSum q k)).re)
        ((torsionEnergy r q q + torsionEnergy (-r) q q) / 2) := by
      have hp_qq := hasSum_torsionEnergy hr0 hr1 q q
      have hm_qq : HasSum (fun k : ℕ => (-r) ^ k / k * (ramanujanSum q k * conj (ramanujanSum q k)).re)
          (torsionEnergy (-r) q q) := by
        have h := hasSum_sum fun ζ (hζ : ζ ∈ primitiveRoots q ℂ) => hasSum_sum
          fun η (hη : η ∈ primitiveRoots q ℂ) => by
            have hnr : ‖((-r : ℝ) : ℂ) * (ζ * conj η)‖ < 1 := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hr0,
                norm_mul, Complex.norm_conj, norm_of_mem_primitiveRoots hζ,
                norm_of_mem_primitiveRoots hη]
              linarith
            have ht := Complex.reCLM.hasSum (Complex.hasSum_taylorSeries_neg_log hnr)
            simp only [Complex.reCLM_apply, Complex.neg_re, Complex.log_re] at ht
            exact ht.congr_fun fun k => by
              rw [mul_pow, ← Complex.ofReal_pow, ← Complex.ofReal_natCast, Complex.div_ofReal_re,
                Complex.re_ofReal_mul]
              ring
        rw [torsionEnergy]
        refine h.congr_fun fun k => ?_
        rw [ramanujanSum, ramanujanSum, map_sum, sum_mul_sum, Complex.re_sum, mul_sum]
        refine sum_congr rfl fun ζ _ => ?_
        rw [Complex.re_sum, mul_sum]
        refine sum_congr rfl fun η _ => ?_
        rw [mul_pow, map_pow]
      exact ((hp_qq.add hm_qq).div_const 2).congr_fun fun k => by ring
    have h_even_inj : HasSum (fun k : ℕ =>
        ((r ^ k + (-r) ^ k) / 2) / k * (ramanujanSum q k * conj (ramanujanSum q k)).re)
        ((1 / 2) * torsionEnergy (r ^ 2) q q) := by
      refine (Function.Injective.hasSum_iff (mul_right_injective₀ (by norm_num : (2 : ℕ) ≠ 0)) ?_).mp ?_
      · intro k hk
        rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · exact absurd ⟨j, by ring⟩ hk
        · rw [Odd.neg_pow ⟨j, rfl⟩ r]; ring
      · refine h_r2.congr_fun fun j => ?_
        dsimp only [Function.comp_def]
        have hpow1 : (-r) ^ (2 * j) = (r ^ 2) ^ j := by rw [pow_mul, neg_sq]
        have hpow2 : r ^ (2 * j) = (r ^ 2) ^ j := pow_mul r 2 j
        have hc : ramanujanSum q (2 * j) = ramanujanSum q j := by
          rw [ramanujanSum_eq_ofReal, ramanujanSum_eq_ofReal,
            ramanujanMode_eq_ramanujanLagCoefficient hq0 (2 * j),
            ramanujanMode_eq_ramanujanLagCoefficient hq0 j,
            ramanujanLagCoefficient_odd_two_mul hq j]
        rw [hpow1, hpow2, hc, Nat.cast_mul, Nat.cast_ofNat]
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp
        · have hj' : (j : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
          field_simp [hj']
          ring
    exact h_avg.unique h_even_inj
  -- Similarly `torsionEnergy r q (2 * q) = torsionEnergy (-r) q q`!
  have h_neg : torsionEnergy r q (2 * q) = torsionEnergy (-r) q q := by
    have hm_qq : HasSum (fun k : ℕ => (-r) ^ k / k * (ramanujanSum q k * conj (ramanujanSum q k)).re)
        (torsionEnergy (-r) q q) := by
      have h := hasSum_sum fun ζ (hζ : ζ ∈ primitiveRoots q ℂ) => hasSum_sum
        fun η (hη : η ∈ primitiveRoots q ℂ) => by
          have hnr : ‖((-r : ℝ) : ℂ) * (ζ * conj η)‖ < 1 := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hr0,
              norm_mul, Complex.norm_conj, norm_of_mem_primitiveRoots hζ,
              norm_of_mem_primitiveRoots hη]
            linarith
          have ht := Complex.reCLM.hasSum (Complex.hasSum_taylorSeries_neg_log hnr)
          simp only [Complex.reCLM_apply, Complex.neg_re, Complex.log_re] at ht
          exact ht.congr_fun fun k => by
            rw [mul_pow, ← Complex.ofReal_pow, ← Complex.ofReal_natCast, Complex.div_ofReal_re,
              Complex.re_ofReal_mul]
            ring
      rw [torsionEnergy]
      refine h.congr_fun fun k => ?_
      rw [ramanujanSum, ramanujanSum, map_sum, sum_mul_sum, Complex.re_sum, mul_sum]
      refine sum_congr rfl fun ζ _ => ?_
      rw [Complex.re_sum, mul_sum]
      refine sum_congr rfl fun η _ => ?_
      rw [mul_pow, map_pow]
    refine hp.unique (hm_qq.congr_fun fun k => ?_)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · simp only [ramanujanSum_eq_ofReal, Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
      rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · have hpow : (-r) ^ (j + j) = r ^ (j + j) := by
          rw [show j + j = 2 * j by ring, pow_mul, pow_mul, neg_sq]
        have hc1 : ramanujanMode (2 * q) (j + j) = ramanujanMode q (j + j) := by
          rw [show j + j = 2 * j by ring,
            ramanujanMode_eq_ramanujanLagCoefficient h2q0,
            ramanujanMode_eq_ramanujanLagCoefficient hq0,
            ramanujanLagCoefficient_two_mul_odd_two_mul hq j,
            ramanujanLagCoefficient_odd_two_mul hq j]
        rw [hpow, hc1]
      · rw [Odd.neg_pow ⟨j, rfl⟩ r, ramanujanMode_two_mul_odd_oddShift hq j]
        ring
  unfold oddTorsionEnergy
  linarith [heven_qq, h_neg]

/-- **Dyadic Scale-Anomaly Limit for `oddTorsionEnergy`:**
For every odd modulus `q` (`q % 2 = 1`),
`oddTorsionEnergy r q q + (φ(q) / 2) * log(1 - r) → -(1 / 2) * orbitIntersection q q + (φ(q) / 2) * log 2`
as `r → 1⁻`, while `(1/2) * torsionEnergy (r^2) q q - oddTorsionEnergy r q q → -φ(q) * log 2`. -/
theorem tendsto_oddTorsionEnergy_add_half_log {q : ℕ} (hq : q % 2 = 1) :
    Tendsto (fun r : ℝ =>
      oddTorsionEnergy r q q + ((Nat.totient q : ℝ) / 2) * Real.log (1 - r))
      (𝓝[<] 1)
      (𝓝 (-(1 / 2 : ℝ) * orbitIntersection q q + ((Nat.totient q : ℝ) / 2) * Real.log 2)) := by
  have hq0 : 0 < q := by omega
  have hne : q ≠ 2 * q := by omega
  have ht_q2q : Tendsto (fun r : ℝ => torsionEnergy r q (2 * q)) (𝓝[<] 1)
      (𝓝 (-((Nat.totient q : ℝ) * Real.log 2))) := by
    have h := (tendsto_torsionEnergy_of_ne hne).mono_left nhdsWithin_le_nhds
    have hI : orbitIntersection q (2 * q) = (Nat.totient q : ℝ) * Real.log 2 := by
      have hh := orbitIntersection_hecke hq0 (t := 2) (by norm_num)
      rw [Nat.mul_comm q 2, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two] at hh
      exact hh
    rwa [hI] at h
  have ht_r2 : Tendsto (fun r : ℝ =>
      (1 / 2 : ℝ) * (torsionEnergy (r ^ 2) q q + (Nat.totient q : ℝ) * Real.log |1 - r ^ 2|))
      (𝓝[<] 1) (𝓝 ((1 / 2 : ℝ) * (-orbitIntersection q q))) := by
    have hcomp := (tendsto_torsionEnergy_self_add_log q).comp
      (((continuous_pow 2).tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds)
    simpa [one_pow] using hcomp.const_mul (1 / 2 : ℝ)
  have ht_log1r : Tendsto (fun r : ℝ => ((Nat.totient q : ℝ) / 2) * Real.log (1 + r))
      (𝓝[<] 1) (𝓝 (((Nat.totient q : ℝ) / 2) * Real.log 2)) := by
    have hc : ContinuousAt (fun r : ℝ => ((Nat.totient q : ℝ) / 2) * Real.log (1 + r)) 1 :=
      continuousAt_const.mul ((continuous_const.add continuous_id').continuousAt.log (by norm_num))
    simpa [show (1 : ℝ) + 1 = 2 by norm_num] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hcomb := (ht_r2.sub ht_q2q).sub ht_log1r
  have htarget : (1 / 2 : ℝ) * (-orbitIntersection q q) - -((Nat.totient q : ℝ) * Real.log 2) -
      ((Nat.totient q : ℝ) / 2) * Real.log 2 =
      -(1 / 2 : ℝ) * orbitIntersection q q + ((Nat.totient q : ℝ) / 2) * Real.log 2 := by ring
  rw [htarget] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with r hr
  rw [torsionEnergy_dyadic_parity_split hq hr.1.le hr.2]
  have hr2_lt : r ^ 2 < 1 := pow_lt_one₀ hr.1.le hr.2 (by norm_num)
  have habs : |1 - r ^ 2| = (1 - r) * (1 + r) := by
    rw [abs_of_pos (sub_pos.mpr hr2_lt)]
    ring
  rw [habs, Real.log_mul (sub_pos.mpr hr.2).ne' (by linarith : (1 + r) ≠ 0)]
  ring

/-! ## §7. Positive Survivor 3: Midpoint Parity-Transposition & Coercive `m = 1` Short-Cycle Positivity -/

/-- Even part of a complex test `g : ℝ → ℂ`. -/
def evenPartComplex (g : ℝ → ℂ) (x : ℝ) : ℂ := (g x + g (-x)) / 2

/-- Odd part of a complex test `g : ℝ → ℂ`. -/
def oddPartComplex (g : ℝ → ℂ) (x : ℝ) : ℂ := (g x - g (-x)) / 2

private theorem evenPartComplex_neg (g : ℝ → ℂ) (x : ℝ) :
    evenPartComplex g (-x) = evenPartComplex g x := by
  simp only [evenPartComplex, neg_neg]
  ring

private theorem oddPartComplex_neg (g : ℝ → ℂ) (x : ℝ) :
    oddPartComplex g (-x) = -oddPartComplex g x := by
  simp only [oddPartComplex, neg_neg]
  ring

private theorem contDiff_evenPartComplex {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (evenPartComplex g) :=
  (hg.add (hg.comp contDiff_neg)).div_const 2

private theorem contDiff_oddPartComplex {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) :
    ContDiff ℝ 2 (oddPartComplex g) :=
  (hg.sub (hg.comp contDiff_neg)).div_const 2

private theorem hasCompactSupport_evenPartComplex {g : ℝ → ℂ} (hgc : HasCompactSupport g) :
    HasCompactSupport (evenPartComplex g) := by
  have hneg : HasCompactSupport (fun x => g (-x)) := hgc.comp_homeomorph (Homeomorph.neg ℝ)
  exact (hgc.add hneg).smul_left

private theorem hasCompactSupport_oddPartComplex {g : ℝ → ℂ} (hgc : HasCompactSupport g) :
    HasCompactSupport (oddPartComplex g) := by
  have hneg : HasCompactSupport (fun x => g (-x)) := hgc.comp_homeomorph (Homeomorph.neg ℝ)
  exact (hgc.sub hneg).smul_left

/-- Translation isometry of `zetaZeroConfig.W`: `W(T_v f, T_v f) = W(f, f)`. -/
theorem zetaZeroConfig_W_translate_self {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (v : ℝ) :
    zetaZeroConfig.W (translate v f) (translate v f) = zetaZeroConfig.W f f := by
  rw [W_self_eq_towerMoment_zero _ temperedConfig_zetaZeroConfig (translate_contDiff hf v)
    (translate_hasCompactSupport hfc v) 1, towerMoment_translate_zero,
    ← W_self_eq_towerMoment_zero _ temperedConfig_zetaZeroConfig hf hfc 1]

/-- **Midpoint Parity-Transposition Law for Short Cycles `g - T_v g`:**
Under the midpoint shift `T_{-(v / 2)}`, the short-cycle difference `g - T_v g` maps even tests
to strictly odd tests and odd tests to strictly even tests, so `Re W_ζ(g - T_v g, g - T_v g)`
splits orthogonally without cross-term into its even-profile and odd-profile short-cycle parts. -/
theorem shortCycle_re_W_eq_even_add_odd {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (v : ℝ) :
    (zetaZeroConfig.W (g - translate v g) (g - translate v g)).re =
      (zetaZeroConfig.W (evenPartComplex g - translate v (evenPartComplex g))
        (evenPartComplex g - translate v (evenPartComplex g))).re +
      (zetaZeroConfig.W (oddPartComplex g - translate v (oddPartComplex g))
        (oddPartComplex g - translate v (oddPartComplex g))).re := by
  set ge := evenPartComplex g
  set go := oddPartComplex g
  have hge : ContDiff ℝ 2 ge := contDiff_evenPartComplex hg
  have hgo : ContDiff ℝ 2 go := contDiff_oddPartComplex hg
  have hgec : HasCompactSupport ge := hasCompactSupport_evenPartComplex hgc
  have hgoc : HasCompactSupport go := hasCompactSupport_oddPartComplex hgc
  set h : ℝ → ℂ := translate (-(v / 2)) (g - translate v g)
  set h1 : ℝ → ℂ := translate (-(v / 2)) (ge - translate v ge)
  set h2 : ℝ → ℂ := translate (-(v / 2)) (go - translate v go)
  have hh_d : ContDiff ℝ 2 h := translate_contDiff (hg.sub (translate_contDiff hg v)) _
  have hh_c : HasCompactSupport h :=
    translate_hasCompactSupport (hgc.sub (translate_hasCompactSupport hgc v)) _
  have hh1_d : ContDiff ℝ 2 h1 := translate_contDiff (hge.sub (translate_contDiff hge v)) _
  have hh1_c : HasCompactSupport h1 :=
    translate_hasCompactSupport (hgec.sub (translate_hasCompactSupport hgec v)) _
  have hh2_d : ContDiff ℝ 2 h2 := translate_contDiff (hgo.sub (translate_contDiff hgo v)) _
  have hh2_c : HasCompactSupport h2 :=
    translate_hasCompactSupport (hgoc.sub (translate_hasCompactSupport hgoc v)) _
  have hh1_odd : ∀ x, h1 (-x) = -h1 x := by
    intro x
    simp only [h1, translate, Pi.sub_apply]
    have e1 : -x - -(v / 2) = -(x - v / 2) := by ring
    have e2 : -x - -(v / 2) - v = -(x + v / 2) := by ring
    have e3 : x - -(v / 2) = x + v / 2 := by ring
    have e4 : x - -(v / 2) - v = x - v / 2 := by ring
    rw [e1, e2, e3, e4, evenPartComplex_neg g (x - v / 2), evenPartComplex_neg g (x + v / 2)]
    ring
  have hh2_ev : ∀ x, h2 (-x) = h2 x := by
    intro x
    simp only [h2, translate, Pi.sub_apply]
    have e1 : -x - -(v / 2) = -(x - v / 2) := by ring
    have e2 : -x - -(v / 2) - v = -(x + v / 2) := by ring
    have e3 : x - -(v / 2) = x + v / 2 := by ring
    have e4 : x - -(v / 2) - v = x - v / 2 := by ring
    rw [e1, e2, e3, e4, oddPartComplex_neg g (x - v / 2), oddPartComplex_neg g (x + v / 2)]
    ring
  have hh_sum : ∀ x, h x = h1 x + h2 x := by
    intro x
    simp only [h, h1, h2, translate, Pi.sub_apply, ge, go, evenPartComplex, oddPartComplex]
    ring
  have hev_re : evenPartReal (fun x => (h x).re) = fun x => (h2 x).re := by
    funext x
    unfold evenPartReal
    rw [hh_sum x, hh_sum (-x), hh1_odd x, hh2_ev x]
    simp only [Complex.add_re, Complex.neg_re]
    ring
  have hodd_re : oddPartReal (fun x => (h x).re) = fun x => (h1 x).re := by
    funext x
    unfold oddPartReal
    rw [hh_sum x, hh_sum (-x), hh1_odd x, hh2_ev x]
    simp only [Complex.add_re, Complex.neg_re]
    ring
  have hev_im : evenPartReal (fun x => (h x).im) = fun x => (h2 x).im := by
    funext x
    unfold evenPartReal
    rw [hh_sum x, hh_sum (-x), hh1_odd x, hh2_ev x]
    simp only [Complex.add_im, Complex.neg_im]
    ring
  have hodd_im : oddPartReal (fun x => (h x).im) = fun x => (h1 x).im := by
    funext x
    unfold oddPartReal
    rw [hh_sum x, hh_sum (-x), hh1_odd x, hh2_ev x]
    simp only [Complex.add_im, Complex.neg_im]
    ring
  rw [← zetaZeroConfig_W_translate_self (hg.sub (translate_contDiff hg v))
      (hgc.sub (translate_hasCompactSupport hgc v)) (-(v / 2)),
    ← zetaZeroConfig_W_translate_self (hge.sub (translate_contDiff hge v))
      (hgec.sub (translate_hasCompactSupport hgec v)) (-(v / 2)),
    ← zetaZeroConfig_W_translate_self (hgo.sub (translate_contDiff hgo v))
      (hgoc.sub (translate_hasCompactSupport hgoc v)) (-(v / 2))]
  change (zetaZeroConfig.W h h).re = (zetaZeroConfig.W h1 h1).re + (zetaZeroConfig.W h2 h2).re
  rw [GaloisForLFunctions.ArithmeticPositivityTheory.zeta_W_re_eq_fullZeroForm_re_add_im hh_d hh_c,
    GaloisForLFunctions.ArithmeticPositivityTheory.zeta_W_re_eq_fullZeroForm_re_add_im hh1_d hh1_c,
    GaloisForLFunctions.ArithmeticPositivityTheory.zeta_W_re_eq_fullZeroForm_re_add_im hh2_d hh2_c,
    fullZeroForm_eq_even_add_odd (Complex.reCLM.contDiff.comp hh_d)
      (hh_c.comp_left Complex.zero_re),
    fullZeroForm_eq_even_add_odd (Complex.imCLM.contDiff.comp hh_d)
      (hh_c.comp_left Complex.zero_im),
    hev_re, hodd_re, hev_im, hodd_im]
  ring

/-- **Coercive `m = 1` Short-Cycle Weil Positivity Past `3/10` (`p = 2`):**
While `ACS.zeta_twoWindows_local_global` (`η ≤ 3/10`) stops short of `m = 1` (`(log 2)/2 ≈ 0.3466`),
for every symmetric test `g ∈ C²(ℝ, ℂ)` (`∀ x, g (-x) = g x`) supported in `[-η, η]` with
`0 < η ≤ 181/500 - (log 2)/2` (`> 3/200`), midpoint parity-transposition maps `g - T_{\log 2} g`
isometrically into the Schur-lending odd window `[-181/500, 181/500]`, giving unconditionally:
`1 / 1000 * ∫ x, ‖g x - translate (Real.log 2) g x‖ ^ 2 ≤ Re W_ζ(g - T_{\log 2} g, g - T_{\log 2} g)`. -/
theorem even_shortCycle_m_one_re_W_ge {g : ℝ → ℂ} {η : ℝ}
    (hη_hi : η ≤ 181 / 500 - Real.log 2 / 2)
    (hg : ContDiff ℝ 2 g) (hgs : tsupport g ⊆ Icc (-η) η)
    (hev : ∀ x, g (-x) = g x) :
    1 / 1000 * ∫ x, ‖(g - translate (Real.log 2) g) x‖ ^ 2 ≤
      (zetaZeroConfig.W (g - translate (Real.log 2) g) (g - translate (Real.log 2) g)).re := by
  have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
  set v := Real.log 2
  have hv0 : 0 ≤ v := (Real.log_pos one_lt_two).le
  set f := g - translate v g
  have hf_d : ContDiff ℝ 2 f := hg.sub (translate_contDiff hg v)
  have hf_c : HasCompactSupport f := hgc.sub (translate_hasCompactSupport hgc v)
  set h := translate (-(v / 2)) f
  have hh_d : ContDiff ℝ 2 h := translate_contDiff hf_d _
  have hh_c : HasCompactSupport h := translate_hasCompactSupport hf_c _
  have hh_odd : ∀ x, h (-x) = -h x := by
    intro x
    simp only [h, f, translate, Pi.sub_apply]
    have e1 : -x - -(v / 2) = -(x - v / 2) := by ring
    have e2 : -x - -(v / 2) - v = -(x + v / 2) := by ring
    have e3 : x - -(v / 2) = x + v / 2 := by ring
    have e4 : x - -(v / 2) - v = x - v / 2 := by ring
    rw [e1, e2, e3, e4, hev (x - v / 2), hev (x + v / 2)]
    ring
  have hh_zero : ∀ x, 181 / 500 < |x| → h x = 0 := by
    intro x hx
    simp only [h, f, translate, Pi.sub_apply]
    have hnot1 : x - -(v / 2) ∉ tsupport g := by
      intro hm
      have := mem_Icc.mp (hgs hm)
      rcases lt_or_gt_of_ne (by linarith [abs_nonneg x] : |x| ≠ 0) with hlt | hgt
      · linarith [abs_nonneg x]
      · rcases le_or_gt 0 x with hx0 | hx0
        · rw [abs_of_nonneg hx0] at hx; linarith
        · rw [abs_of_neg hx0] at hx; linarith
    have hnot2 : x - -(v / 2) - v ∉ tsupport g := by
      intro hm
      have := mem_Icc.mp (hgs hm)
      rcases le_or_gt 0 x with hx0 | hx0
      · rw [abs_of_nonneg hx0] at hx; linarith
      · rw [abs_of_neg hx0] at hx; linarith
    rw [image_eq_zero_of_notMem_tsupport hnot1, image_eq_zero_of_notMem_tsupport hnot2, sub_zero]
  have hRe_d : ContDiff ℝ 2 (fun x => (h x).re) := Complex.reCLM.contDiff.comp hh_d
  have hIm_d : ContDiff ℝ 2 (fun x => (h x).im) := Complex.imCLM.contDiff.comp hh_d
  have hRe_c : HasCompactSupport (fun x => (h x).re) := hh_c.comp_left Complex.zero_re
  have hIm_c : HasCompactSupport (fun x => (h x).im) := hh_c.comp_left Complex.zero_im
  have h1 := fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths hRe_d hRe_c
    (fun x => by simp [hh_odd x]) (fun x hx => by simp [hh_zero x hx])
  have h2 := fullZeroForm_ge_of_odd_support_le_threeHundredSixtyTwoThousandths hIm_d hIm_c
    (fun x => by simp [hh_odd x]) (fun x hx => by simp [hh_zero x hx])
  have hint (u : ℝ → ℝ) (hu : Continuous u) (huc : HasCompactSupport u) :
      Integrable (fun x => u x ^ 2) volume := by
    have hs : HasCompactSupport (fun x => u x ^ 2) :=
      HasCompactSupport.of_support_subset_isCompact huc.isCompact fun x hx =>
        subset_tsupport u (by simpa using hx)
    exact (hu.pow 2).integrable_of_hasCompactSupport hs
  have hnorm_h : ∫ x, ‖h x‖ ^ 2 = (∫ x, (h x).re ^ 2) + ∫ x, (h x).im ^ 2 := by
    rw [← integral_add (hint _ hRe_d.continuous hRe_c) (hint _ hIm_d.continuous hIm_c)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have hnorm_eq : ∫ x, ‖h x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
    simp only [h, translate]
    exact integral_sub_right_eq_self (fun x => ‖f x‖ ^ 2) (-(v / 2))
  rw [← zetaZeroConfig_W_translate_self hf_d hf_c (-(v / 2))]
  change _ ≤ (zetaZeroConfig.W h h).re
  rw [GaloisForLFunctions.ArithmeticPositivityTheory.zeta_W_re_eq_fullZeroForm_re_add_im hh_d hh_c,
    ← hnorm_eq, hnorm_h]
  linarith

/-- Explicit positive aperture witness: `3 / 200 ≤ 181 / 500 - Real.log 2 / 2`. -/
theorem three_twoHundredths_le_shortCycle_m_one_aperture :
    (3 / 200 : ℝ) ≤ 181 / 500 - Real.log 2 / 2 := by
  linarith [Real.log_two_lt_d9]

end GaloisForLFunctions.TransThresholdPairCorrelation

end
