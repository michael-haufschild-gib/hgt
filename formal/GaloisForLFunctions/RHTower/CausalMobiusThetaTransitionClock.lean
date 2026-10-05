import GaloisForLFunctions.RHTower.CausalMobiusThetaSmoothGauge
import GaloisForLFunctions.RHTower.EulerDeletionClockRefinement
import GaloisForLFunctions.RHTower.EulerDeletionHighClockLayerTail

/-!
# The transition-clock covariance of the causal theta coordinate

* the clock ratio at a prime-power step is the underlying prime:
  `clock(l+1) = p · clock(l)` when `l+1 = p^k`;
* **(22b)** `|⟨C_N, L_l q_N^flat⟩_H| ≤ C N^{5/2}/clock(l)²` (for every layer `l`);
* **(23)** for every fixed `δ > 0`,
  `B(N) = Σ_{l<min(K_N,N), l+1 prime power, N^{1−δ}<clock(l+1)<N^{5/4+δ}} ⟨L_l P_N, q_N^flat⟩_H + O_δ(1)`;
* consequently RH is equivalent to subpower growth of this transition-clock covariance, and an
  off-line zero with displacement `β` forces it to violate every `O(N^ε)` with `ε < β`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

open DeletionResidueMartingale

/-! ## The clock ratio at prime-power steps -/

theorem pow_dvd_lcm_or {p k a b : ℕ} (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : p ^ k ∣ Nat.lcm a b) : p ^ k ∣ a ∨ p ^ k ∣ b := by
  rw [hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero ha hb), Nat.factorization_lcm ha hb] at h
  rw [hp.pow_dvd_iff_le_factorization ha, hp.pow_dvd_iff_le_factorization hb]
  simp only [Finsupp.sup_apply] at h
  exact le_sup_iff.1 h

theorem exists_dvd_of_pow_dvd_clock {p k n : ℕ} (hp : p.Prime) (hk : 0 < k) (h : p ^ k ∣ clock n) :
    ∃ i < n, p ^ k ∣ i + 1 := by
  induction n with
  | zero =>
    exfalso
    have h1 : clock 0 = 1 := by simp [clock]
    rw [h1] at h
    have := Nat.le_of_dvd one_pos h
    have := Nat.one_lt_pow hk.ne' hp.one_lt
    omega
  | succ n ih =>
    rw [clock_succ_eq_lcm] at h
    rcases pow_dvd_lcm_or hp (clock_pos n).ne' (by omega) h with h1 | h1
    · obtain ⟨i, hi, hd⟩ := ih h1
      exact ⟨i, by omega, hd⟩
    · exact ⟨n, by omega, h1⟩

/-- **The clock ratio at a prime-power step is its underlying prime.** -/
theorem clock_succ_eq_minFac_mul {l : ℕ} (hl : IsPrimePow (l + 1)) :
    clock (l + 1) = (l + 1).minFac * clock l := by
  obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff _).1 hl
  have hmin : (l + 1).minFac = p := by rw [← hpk]; exact hp.pow_minFac hk.ne'
  rw [hmin, clock_succ_eq_lcm, ← hpk]
  set c := clock l
  have hlt : p ^ (k - 1) < p ^ k := Nat.pow_lt_pow_right hp.one_lt (by omega)
  have hk1 : p ^ (k - 1) ∣ c := dvd_clock (Nat.one_le_pow _ _ hp.pos) (by omega)
  have hk2 : ¬ p ^ k ∣ c := by
    intro h
    obtain ⟨i, hi, hd⟩ := exists_dvd_of_pow_dvd_clock hp hk h
    have := Nat.le_of_dvd (by omega) hd
    omega
  have hg : Nat.gcd c (p ^ k) = p ^ (k - 1) := by
    obtain ⟨j, hj, hgj⟩ := (Nat.dvd_prime_pow hp).1 (Nat.gcd_dvd_right c (p ^ k))
    have h1 : p ^ (k - 1) ∣ Nat.gcd c (p ^ k) := Nat.dvd_gcd hk1 (Nat.pow_dvd_pow p (by omega))
    rw [hgj] at h1 ⊢
    have hj1 : k - 1 ≤ j := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h1
    have hj2 : j ≠ k := by
      rintro rfl
      exact hk2 (hgj ▸ Nat.gcd_dvd_left c (p ^ j))
    congr 1
    omega
  have hgl := Nat.gcd_mul_lcm c (p ^ k)
  rw [hg] at hgl
  have hpk' : c * p ^ k = p ^ (k - 1) * (p * c) := by
    rw [show p ^ k = p * p ^ (k - 1) by rw [← pow_succ']; congr 1; omega]
    ring
  apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos (k - 1))
  rw [hgl, hpk']

theorem clock_succ_le_mul (l : ℕ) : clock (l + 1) ≤ (l + 1) * clock l := by
  rw [clock_succ_eq_lcm, mul_comm]
  exact Nat.lcm_le_mul (clock_pos l) (by omega)

/-! ## Growth of the logarithmic clock threshold -/

theorem exists_logarithmicClockThreshold_le_rpow {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 1 ≤ N → (logarithmicClockThreshold N : ℝ) ≤ C * (N : ℝ) ^ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨5 * (2 ^ ε / (ε * Real.log 2) + 1), by positivity, fun N hN => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNε : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hNR hε.le
  have hL : (Nat.log2 (N + 1) : ℝ) ≤ Real.log ((N : ℝ) + 1) / Real.log 2 := by
    rw [Nat.log2_eq_log_two]
    have := Real.natLog_le_logb (N + 1) 2
    push_cast at this
    rwa [Real.logb] at this
  have hlog : Real.log ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) ^ ε / ε := Real.log_le_rpow_div (by positivity) hε
  have hpow : ((N : ℝ) + 1) ^ ε ≤ 2 ^ ε * (N : ℝ) ^ ε := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hε.le
  unfold logarithmicClockThreshold
  push_cast
  calc 5 * ((Nat.log2 (N + 1) : ℝ) + 1) ≤ 5 * (2 ^ ε * (N : ℝ) ^ ε / (ε * Real.log 2) + (N : ℝ) ^ ε) := by
        gcongr
        calc (Nat.log2 (N + 1) : ℝ) ≤ Real.log ((N : ℝ) + 1) / Real.log 2 := hL
          _ ≤ ((N : ℝ) + 1) ^ ε / ε / Real.log 2 := by gcongr
          _ ≤ 2 ^ ε * (N : ℝ) ^ ε / ε / Real.log 2 := by gcongr
          _ = 2 ^ ε * (N : ℝ) ^ ε / (ε * Real.log 2) := by rw [div_div]
    _ = 5 * (2 ^ ε / (ε * Real.log 2) + 1) * (N : ℝ) ^ ε := by ring

/-! ## History layers: symmetry, support, innovations -/

theorem inner_historyLayer_left (l : ℕ) (x y : Lp ℝ 2 cellMeasure) :
    inner ℝ (historyLayer l x) y = inner ℝ x (historyLayer l y) := by
  simp only [historyLayer, sub_apply, inner_sub_left, inner_sub_right,
    Submodule.inner_starProjection_left_eq_right]

theorem historyLayer_mem (l : ℕ) (x : Lp ℝ 2 cellMeasure) : historyLayer l x ∈ historySpace (l + 1) := by
  simp only [historyLayer, sub_apply]
  exact Submodule.sub_mem _ (Submodule.starProjection_apply_mem _ _)
    (historySpace_mono (by omega) (Submodule.starProjection_apply_mem _ _))

theorem inner_eq_inner_starProjection_of_mem {K : Submodule ℝ (Lp ℝ 2 cellMeasure)} [K.HasOrthogonalProjection]
    {u : Lp ℝ 2 cellMeasure} (hu : u ∈ K) (y : Lp ℝ 2 cellMeasure) :
    inner ℝ u y = inner ℝ u (K.starProjection y) := by
  rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.2 hu]

theorem inner_signedInnovation_eq_zero {a b : ℕ} (hab : a ≠ b) :
    inner ℝ (signedInnovation a) (signedInnovation b) = 0 := by
  rw [signedInnovation, signedInnovation, inner_smul_left, inner_smul_right]
  rcases lt_or_gt_of_ne hab with h | h
  · rw [real_inner_comm, innovation_orthogonal h]; simp
  · rw [innovation_orthogonal h]; simp

theorem norm_sq_sum_signedInnovation (S : Finset ℕ) :
    ‖∑ l ∈ S, signedInnovation l‖ ^ 2 = ∑ l ∈ S, ‖signedInnovation l‖ ^ 2 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, norm_add_sq_real, ih, inner_sum,
      Finset.sum_eq_zero fun l hl => inner_signedInnovation_eq_zero (fun h => ha (by rw [h]; exact hl))]
    ring

theorem norm_sum_signedInnovation_le {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Finset.range N) :
    ‖∑ l ∈ S, signedInnovation l‖ ≤ Real.sqrt 2 := by
  refine Real.le_sqrt_of_sq_le ?_
  rw [norm_sq_sum_signedInnovation]
  calc ∑ l ∈ S, ‖signedInnovation l‖ ^ 2 ≤ ∑ l ∈ Finset.range N, ‖signedInnovation l‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hS fun _ _ _ => sq_nonneg _
    _ = ‖martingalePart N‖ ^ 2 := (martingalePart_sq N).symm
    _ ≤ 2 := martingalePart_sq_le_two N

/-! ## (22b) Long-clock layers see almost no source -/

theorem abs_inner_sourceVec_le (N : ℕ) (u : Lp ℝ 2 cellMeasure)
    (hu : Summable fun j => cellWeight j * |u j|) :
    |inner ℝ (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N) u| ≤
      N * ∑' j, cellWeight j * |u j| := by
  set C := sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N
  have hC : ∀ j, |C j| ≤ N := fun j => by
    rw [sourceVec_apply_eq_cell]; exact abs_moebiusCell_le N (j + 1)
  have h := hasSum_inner C u
  have hb : ∀ j, ‖C j * u j * cellWeight j‖ ≤ N * (cellWeight j * |u j|) := fun j => by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (cellWeight_pos j)]
    calc |C j| * |u j| * cellWeight j ≤ N * |u j| * cellWeight j :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC j) (abs_nonneg _))
            (cellWeight_pos j).le
      _ = N * (cellWeight j * |u j|) := by ring
  rw [← h.tsum_eq, ← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm (Summable.of_norm_bounded (hu.mul_left _) hb |>.norm)).trans
    (Summable.tsum_le_tsum hb (Summable.of_norm_bounded (hu.mul_left _) hb).norm (hu.mul_left _))

/-- **(22b)** `|⟨C_N, L_l q_N^flat⟩_H| ≤ C N^{5/2}/clock(l)²` for every layer `l`. -/
theorem exists_abs_inner_sourceVec_historyLayer_flat_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, gaugeActive N → ∀ l : ℕ,
      |inner ℝ (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)
        (historyLayer l (flatWaveletVec N))| ≤ C * ((N : ℝ) ^ 2 * Real.sqrt N) / (clock l : ℝ) ^ 2 := by
  obtain ⟨C1, hC10, hC1⟩ := exists_tsum_cellWeight_abs_sub_projection_flat_le
  refine ⟨2 * C1, by positivity, fun N h l => ?_⟩
  set v := flatWaveletVec N
  have hNR : (0 : ℝ) < N := by exact_mod_cast h.1
  have hdev : ∀ Q : ℕ, 1 ≤ Q →
      |inner ℝ (sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N)
        (v - (periodicSpace Q).starProjection v)| ≤ N * (C1 * (N * Real.sqrt N) / (Q : ℝ) ^ 2) := by
    intro Q hQ
    obtain ⟨hs, hle⟩ := hC1 N h Q hQ
    have hpt : ∀ j, (v - (periodicSpace Q).starProjection v) j = v j - (periodicSpace Q).starProjection v j :=
      fun j => cell_point_eq_of_ae (Lp.coeFn_sub _ _) j
    have hs' : Summable fun j => cellWeight j * |(v - (periodicSpace Q).starProjection v) j| :=
      hs.congr fun j => by rw [hpt]
    refine (abs_inner_sourceVec_le N _ hs').trans ?_
    gcongr
    refine le_of_eq_of_le (tsum_congr fun j => by rw [hpt]) hle
  have hlayer : historyLayer l v = (v - (periodicSpace (clock l)).starProjection v) -
      (v - (periodicSpace (clock (l + 1))).starProjection v) := by
    simp only [historyLayer, sub_apply, historySpace_eq_periodicSpace]
    abel
  have hcl : (clock l : ℝ) ≤ clock (l + 1) := by exact_mod_cast Nat.le_of_dvd (clock_pos _) (clock_dvd (by omega))
  have hc0 : (0 : ℝ) < clock l := by exact_mod_cast clock_pos l
  rw [hlayer, inner_sub_right]
  have h1 := hdev (clock l) (clock_pos l)
  have h2 := hdev (clock (l + 1)) (clock_pos (l + 1))
  have h2' : (N : ℝ) * (C1 * (N * Real.sqrt N) / (clock (l + 1) : ℝ) ^ 2) ≤
      N * (C1 * (N * Real.sqrt N) / (clock l : ℝ) ^ 2) := by gcongr
  calc _ ≤ _ := abs_sub _ _
    _ ≤ N * (C1 * (N * Real.sqrt N) / (clock l : ℝ) ^ 2) +
        N * (C1 * (N * Real.sqrt N) / (clock l : ℝ) ^ 2) := add_le_add h1 (h2.trans h2')
    _ = 2 * C1 * ((N : ℝ) ^ 2 * Real.sqrt N) / (clock l : ℝ) ^ 2 := by ring

/-! ## The three clock bands -/

/-- Prime-power layers below the logarithmic threshold. -/
def primePowerLayers (N : ℕ) : Finset ℕ :=
  (Finset.range (min (logarithmicClockThreshold N) N)).filter fun l => IsPrimePow (l + 1)

/-- Short clocks `clock(l+1) ≤ N^{1−δ}`. -/
def shortLayers (δ : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (primePowerLayers N).filter fun l => (clock (l + 1) : ℝ) ≤ (N : ℝ) ^ (1 - δ)

/-- The transition band `N^{1−δ} < clock(l+1) < N^{5/4+δ}`. -/
def transitionLayers (δ : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (primePowerLayers N).filter fun l =>
    (N : ℝ) ^ (1 - δ) < clock (l + 1) ∧ (clock (l + 1) : ℝ) < (N : ℝ) ^ (5 / 4 + δ)

/-- Long clocks: all remaining layers (`clock(l+1) ≥ N^{5/4+δ}`). -/
def longLayers (δ : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (primePowerLayers N).filter fun l =>
    ¬ ((clock (l + 1) : ℝ) ≤ (N : ℝ) ^ (1 - δ)) ∧ ¬ ((clock (l + 1) : ℝ) < (N : ℝ) ^ (5 / 4 + δ))

/-- **The transition-clock covariance** of (23). -/
def transitionCovariance (δ : ℝ) (N : ℕ) : ℝ :=
  ∑ l ∈ transitionLayers δ N, inner ℝ (historyLayer l (predictableDrift N)) (flatWaveletVec N)

theorem mem_primePowerLayers {N l : ℕ} :
    l ∈ primePowerLayers N ↔ l < min (logarithmicClockThreshold N) N ∧ IsPrimePow (l + 1) := by
  simp [primePowerLayers]

theorem sum_primePowerLayers_eq_bands (δ : ℝ) (N : ℕ) (f : ℕ → ℝ) :
    ∑ l ∈ primePowerLayers N, f l =
      ∑ l ∈ shortLayers δ N, f l + ∑ l ∈ transitionLayers δ N, f l + ∑ l ∈ longLayers δ N, f l := by
  classical
  simp only [shortLayers, transitionLayers, longLayers]
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  set c : ℝ := (clock (l + 1) : ℝ)
  by_cases h1 : c ≤ (N : ℝ) ^ (1 - δ)
  · have h2 : ¬ ((N : ℝ) ^ (1 - δ) < c ∧ c < (N : ℝ) ^ (5 / 4 + δ)) := fun h => absurd h.1 (not_lt.2 h1)
    rw [if_pos h1, if_neg h2, if_neg (fun h => h.1 h1)]
    ring
  · by_cases h3 : c < (N : ℝ) ^ (5 / 4 + δ)
    · rw [if_neg h1, if_pos ⟨not_le.1 h1, h3⟩, if_neg (fun h => h.2 h3)]
      ring
    · rw [if_neg h1, if_neg (fun h => h3 h.2), if_pos ⟨h1, h3⟩]
      ring

theorem layer_lt_of_mem_primePowerLayers {N l : ℕ} (hl : l ∈ primePowerLayers N) :
    l < N ∧ l + 1 ≤ logarithmicClockThreshold N := by
  have h := (mem_primePowerLayers.1 hl).1
  exact ⟨lt_of_lt_of_le h (min_le_right _ _), by have := min_le_left (logarithmicClockThreshold N) N; omega⟩

theorem card_primePowerLayers_le (N : ℕ) :
    ((primePowerLayers N).card : ℝ) ≤ logarithmicClockThreshold N := by
  have : (primePowerLayers N).card ≤ logarithmicClockThreshold N :=
    (Finset.card_filter_le _ _).trans (by simp)
  exact_mod_cast this

theorem clock_succ_le_threshold_mul {N l : ℕ} (hl : l ∈ primePowerLayers N) :
    (clock (l + 1) : ℝ) ≤ logarithmicClockThreshold N * clock l := by
  have h1 := clock_succ_le_mul l
  have h2 := (layer_lt_of_mem_primePowerLayers hl).2
  have : clock (l + 1) ≤ logarithmicClockThreshold N * clock l :=
    h1.trans (Nat.mul_le_mul_right _ h2)
  exact_mod_cast this

theorem one_le_logarithmicClockThreshold (N : ℕ) : (1 : ℝ) ≤ logarithmicClockThreshold N := by
  have : 1 ≤ logarithmicClockThreshold N := by unfold logarithmicClockThreshold; omega
  exact_mod_cast this

theorem sqrt_div_div_sqrt_le {Q c K N : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K) (hN : 0 < N)
    (h : Q ≤ K * (c + 1)) : Real.sqrt (Q / N) / Real.sqrt (c + 1) ≤ Real.sqrt K / Real.sqrt N := by
  have hc1 : 0 < Real.sqrt (c + 1) := Real.sqrt_pos.2 (by linarith)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN
  rw [Real.sqrt_div' _ hN.le, div_div, div_le_div_iff₀ (by positivity) hsN]
  calc Real.sqrt Q * Real.sqrt N ≤ Real.sqrt (K * (c + 1)) * Real.sqrt N := by
        gcongr
    _ = Real.sqrt K * (Real.sqrt N * Real.sqrt (c + 1)) := by
        rw [Real.sqrt_mul hK]; ring

/-- The short clocks contribute `O_δ(1)` (progression bounds (22) with `A = 1/δ`). -/
theorem exists_abs_sum_shortLayers_le {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, gaugeActive N →
      |∑ l ∈ shortLayers δ N, inner ℝ (historyLayer l (predictableDrift N)) (flatWaveletVec N)| ≤ C := by
  classical
  obtain ⟨CA, hCA0, hCA⟩ := exists_norm_starProjection_periodicSpace_flat_le (A := 1 / δ) (by positivity)
  obtain ⟨CK, hCK0, hCK⟩ := exists_logarithmicClockThreshold_le_rpow (ε := 1 / 4) (by norm_num)
  refine ⟨2 * Real.sqrt 10 * CA * CK ^ 2, by positivity, fun N h => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h.1
  have hNR : (0 : ℝ) < N := by linarith
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  set K := (logarithmicClockThreshold N : ℝ) with hKdef
  have hK1 : 1 ≤ K := one_le_logarithmicClockThreshold N
  have hterm : ∀ l ∈ shortLayers δ N, |inner ℝ (historyLayer l (predictableDrift N)) (flatWaveletVec N)| ≤
      2 * Real.sqrt 10 * CA * (Real.sqrt K / Real.sqrt N) := by
    intro l hl
    simp only [shortLayers, Finset.mem_filter] at hl
    obtain ⟨hlpp, hQle⟩ := hl
    obtain ⟨hlN, -⟩ := layer_lt_of_mem_primePowerLayers hlpp
    set Q := clock (l + 1) with hQdef
    have hQ1 : 1 ≤ Q := clock_pos _
    have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
    have hNpow : (N : ℝ) ^ (1 - δ) ≤ N := by
      calc (N : ℝ) ^ (1 - δ) ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
        _ = N := Real.rpow_one _
    have hQN : Q ≤ N := by exact_mod_cast hQle.trans hNpow
    -- the layer lies in the next history, so it sees only the periodic projection
    have h1 : inner ℝ (historyLayer l (predictableDrift N)) (flatWaveletVec N) =
        inner ℝ (historyLayer l (predictableDrift N)) ((periodicSpace Q).starProjection (flatWaveletVec N)) :=
      inner_eq_inner_starProjection_of_mem (K := historySpace (l + 1)) (historyLayer_mem l _) _
    have hL : ‖historyLayer l (predictableDrift N)‖ ≤ Real.sqrt 10 * N / Real.sqrt ((clock l : ℝ) + 1) := by
      have hE := predictableDrift_layer_energy_le_clock_tail N l hlN
      have hc : (0 : ℝ) < (clock l : ℝ) + 1 := by positivity
      rw [← Real.sqrt_mul_self (by positivity : (0 : ℝ) ≤ N), ← Real.sqrt_mul (by norm_num),
        ← Real.sqrt_div' _ hc.le]
      refine Real.le_sqrt_of_sq_le (hE.trans ?_)
      gcongr
      nlinarith
    have hP := hCA N h Q hQ1 hQN
    have hrat : ((Q : ℝ) / N) ^ (1 / δ) ≤ (N : ℝ)⁻¹ := by
      have hx : (Q : ℝ) / N ≤ (N : ℝ) ^ (-δ) := by
        rw [div_le_iff₀ hNR]
        calc (Q : ℝ) ≤ (N : ℝ) ^ (1 - δ) := hQle
          _ = (N : ℝ) ^ (-δ) * N := by
              rw [sub_eq_neg_add, Real.rpow_add hNR, Real.rpow_one]
      calc ((Q : ℝ) / N) ^ (1 / δ) ≤ ((N : ℝ) ^ (-δ)) ^ (1 / δ) :=
            Real.rpow_le_rpow (by positivity) hx (by positivity)
        _ = (N : ℝ)⁻¹ := by
            rw [← Real.rpow_mul hNR.le, show -δ * (1 / δ) = -1 by field_simp, Real.rpow_neg_one]
    have hE2 : ((N : ℝ) ^ 2)⁻¹ + ((Q : ℝ) / N) ^ (1 / δ) ≤ 2 / N := by
      have : ((N : ℝ) ^ 2)⁻¹ ≤ (N : ℝ)⁻¹ := by
        apply inv_anti₀ hNR; nlinarith
      calc ((N : ℝ) ^ 2)⁻¹ + ((Q : ℝ) / N) ^ (1 / δ) ≤ (N : ℝ)⁻¹ + (N : ℝ)⁻¹ := add_le_add this hrat
        _ = 2 / N := by ring
    have hPQ : ‖(periodicSpace Q).starProjection (flatWaveletVec N)‖ ≤
        CA * Real.sqrt ((Q : ℝ) / N) * (2 / N) :=
      hP.trans (mul_le_mul_of_nonneg_left hE2 (by positivity))
    have hratio : (Q : ℝ) ≤ K * ((clock l : ℝ) + 1) := by
      have := clock_succ_le_threshold_mul hlpp
      nlinarith
    have hsq := sqrt_div_div_sqrt_le (Q := (Q : ℝ)) (c := (clock l : ℝ)) (K := K) (N := N)
      (by positivity) (by linarith) hNR hratio
    rw [h1]
    calc |inner ℝ (historyLayer l (predictableDrift N)) ((periodicSpace Q).starProjection (flatWaveletVec N))|
        ≤ ‖historyLayer l (predictableDrift N)‖ * ‖(periodicSpace Q).starProjection (flatWaveletVec N)‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ (Real.sqrt 10 * N / Real.sqrt ((clock l : ℝ) + 1)) * (CA * Real.sqrt ((Q : ℝ) / N) * (2 / N)) :=
          mul_le_mul hL hPQ (norm_nonneg _) (by positivity)
      _ = 2 * Real.sqrt 10 * CA * (Real.sqrt ((Q : ℝ) / N) / Real.sqrt ((clock l : ℝ) + 1)) := by
          field_simp
      _ ≤ 2 * Real.sqrt 10 * CA * (Real.sqrt K / Real.sqrt N) := by gcongr
  have hcard : ((shortLayers δ N).card : ℝ) ≤ K := by
    refine le_trans ?_ (card_primePowerLayers_le N)
    exact_mod_cast Finset.card_filter_le _ _
  have hKsq : K ^ 2 ≤ CK ^ 2 * Real.sqrt N := by
    have h1 := hCK N h.1
    have hK0 : 0 ≤ K := by linarith
    calc K ^ 2 ≤ (CK * (N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ hK0 h1 2
      _ = CK ^ 2 * Real.sqrt N := by
          rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul hNR.le,
            Real.sqrt_eq_rpow]
          norm_num
  have hsqK : Real.sqrt K ≤ K := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  calc |∑ l ∈ shortLayers δ N, inner ℝ (historyLayer l (predictableDrift N)) (flatWaveletVec N)|
      ≤ ∑ l ∈ shortLayers δ N, |inner ℝ (historyLayer l (predictableDrift N)) (flatWaveletVec N)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ shortLayers δ N, 2 * Real.sqrt 10 * CA * (Real.sqrt K / Real.sqrt N) :=
        Finset.sum_le_sum hterm
    _ = (shortLayers δ N).card * (2 * Real.sqrt 10 * CA * (Real.sqrt K / Real.sqrt N)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ K * (2 * Real.sqrt 10 * CA * (K / Real.sqrt N)) := by gcongr
    _ = 2 * Real.sqrt 10 * CA * (K ^ 2 / Real.sqrt N) := by ring
    _ ≤ 2 * Real.sqrt 10 * CA * (CK ^ 2 * Real.sqrt N / Real.sqrt N) := by gcongr
    _ = 2 * Real.sqrt 10 * CA * CK ^ 2 := by field_simp

theorem rpow_five_halves_eq {N : ℝ} (hN : 0 < N) : N ^ (5 / 2 : ℝ) = N ^ 2 * Real.sqrt N := by
  rw [Real.sqrt_eq_rpow, show (5 / 2 : ℝ) = 2 + 1 / 2 by norm_num, Real.rpow_add hN,
    show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

/-- The long clocks contribute `O_δ(1)`: the literal source part by **(22b)**, the innovation part
through orthogonality of the history layers. -/
theorem exists_abs_sum_longLayers_le {δ : ℝ} (hδ : 0 < δ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, gaugeActive N →
      |∑ l ∈ longLayers δ N, inner ℝ (historyLayer l (predictableDrift N)) (flatWaveletVec N)| ≤ C := by
  classical
  obtain ⟨C22, hC220, hC22⟩ := exists_abs_inner_sourceVec_historyLayer_flat_le
  obtain ⟨CK, hCK0, hCK⟩ := exists_logarithmicClockThreshold_le_rpow (ε := δ / 2) (by positivity)
  obtain ⟨Bf, hBf0, hBf⟩ := exists_norm_flatWaveletVec_le
  refine ⟨C22 * CK ^ 3 + Real.sqrt 2 * Bf, by positivity, fun N h => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast h.1
  have hNR : (0 : ℝ) < N := by linarith
  set K := (logarithmicClockThreshold N : ℝ) with hKdef
  have hK1 : 1 ≤ K := one_le_logarithmicClockThreshold N
  set Cv := sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N
  set q := flatWaveletVec N
  have hsplit : ∀ l ∈ longLayers δ N, inner ℝ (historyLayer l (predictableDrift N)) q =
      inner ℝ Cv (historyLayer l q) - inner ℝ (signedInnovation l) q := by
    intro l hl
    simp only [longLayers, Finset.mem_filter] at hl
    obtain ⟨hlN, -⟩ := layer_lt_of_mem_primePowerLayers hl.1
    have hP : predictableDrift N = Cv - martingalePart N := by
      rw [show Cv = martingalePart N + predictableDrift N from source_eq_martingale_add_drift N]
      abel
    rw [hP, map_sub, inner_sub_left, inner_historyLayer_left, historyLayer_martingalePart,
      if_pos hlN]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← sum_inner]
  have hsub : longLayers δ N ⊆ Finset.range N := fun l hl => by
    simp only [longLayers, Finset.mem_filter] at hl
    exact Finset.mem_range.2 (layer_lt_of_mem_primePowerLayers hl.1).1
  have hinn : |inner ℝ (∑ l ∈ longLayers δ N, signedInnovation l) q| ≤ Real.sqrt 2 * Bf :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (norm_sum_signedInnovation_le hsub) (hBf N h.1) (norm_nonneg _) (by positivity))
  have hterm : ∀ l ∈ longLayers δ N, |inner ℝ Cv (historyLayer l q)| ≤
      C22 * K ^ 2 * ((N : ℝ) ^ (2 * δ))⁻¹ := by
    intro l hl
    simp only [longLayers, Finset.mem_filter] at hl
    obtain ⟨hlpp, -, hlong⟩ := hl
    have hlong' : (N : ℝ) ^ (5 / 4 + δ) ≤ clock (l + 1) := not_lt.1 hlong
    have hratio := clock_succ_le_threshold_mul hlpp
    have hc0 : (0 : ℝ) < clock l := by exact_mod_cast clock_pos l
    have hXpos : 0 < (N : ℝ) ^ (5 / 4 + δ) := by positivity
    -- `clock(l) ≥ N^{5/4+δ}/K`
    have hcl : (N : ℝ) ^ (5 / 4 + δ) ≤ K * clock l := hlong'.trans hratio
    have hsq : ((N : ℝ) ^ (5 / 4 + δ)) ^ 2 = (N : ℝ) ^ (5 / 2 : ℝ) * (N : ℝ) ^ (2 * δ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNR.le, ← Real.rpow_add hNR]
      congr 1; push_cast; ring
    refine (hC22 N h l).trans ?_
    rw [← rpow_five_halves_eq hNR, div_le_iff₀ (by positivity)]
    have h1 : ((N : ℝ) ^ (5 / 4 + δ)) ^ 2 ≤ K ^ 2 * (clock l : ℝ) ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hXpos.le hcl 2
    rw [hsq] at h1
    have hN2 : 0 < (N : ℝ) ^ (2 * δ) := by positivity
    calc C22 * (N : ℝ) ^ (5 / 2 : ℝ) = C22 * ((N : ℝ) ^ (5 / 2 : ℝ) * (N : ℝ) ^ (2 * δ)) *
          ((N : ℝ) ^ (2 * δ))⁻¹ := by field_simp
      _ ≤ C22 * (K ^ 2 * (clock l : ℝ) ^ 2) * ((N : ℝ) ^ (2 * δ))⁻¹ := by gcongr
      _ = C22 * K ^ 2 * ((N : ℝ) ^ (2 * δ))⁻¹ * (clock l : ℝ) ^ 2 := by ring
  have hcard : ((longLayers δ N).card : ℝ) ≤ K := by
    refine le_trans ?_ (card_primePowerLayers_le N)
    exact_mod_cast Finset.card_filter_le _ _
  have hK3 : K ^ 3 * ((N : ℝ) ^ (2 * δ))⁻¹ ≤ CK ^ 3 := by
    have h1 := hCK N h.1
    have hK0 : 0 ≤ K := by linarith
    have hN2 : 0 < (N : ℝ) ^ (2 * δ) := by positivity
    rw [mul_inv_le_iff₀ hN2]
    calc K ^ 3 ≤ (CK * (N : ℝ) ^ (δ / 2)) ^ 3 := pow_le_pow_left₀ hK0 h1 3
      _ = CK ^ 3 * (N : ℝ) ^ (3 * (δ / 2)) := by
          rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (δ / 2)) 3, ← Real.rpow_mul hNR.le]
          push_cast
          ring_nf
      _ ≤ CK ^ 3 * (N : ℝ) ^ (2 * δ) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)) (by positivity)
  have hlong : |∑ l ∈ longLayers δ N, inner ℝ Cv (historyLayer l q)| ≤ C22 * CK ^ 3 := by
    calc |∑ l ∈ longLayers δ N, inner ℝ Cv (historyLayer l q)| ≤
          ∑ l ∈ longLayers δ N, |inner ℝ Cv (historyLayer l q)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l ∈ longLayers δ N, C22 * K ^ 2 * ((N : ℝ) ^ (2 * δ))⁻¹ := Finset.sum_le_sum hterm
      _ = (longLayers δ N).card * (C22 * K ^ 2 * ((N : ℝ) ^ (2 * δ))⁻¹) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K * (C22 * K ^ 2 * ((N : ℝ) ^ (2 * δ))⁻¹) := by gcongr
      _ = C22 * (K ^ 3 * ((N : ℝ) ^ (2 * δ))⁻¹) := by ring
      _ ≤ C22 * CK ^ 3 := by gcongr
  calc _ ≤ |∑ l ∈ longLayers δ N, inner ℝ Cv (historyLayer l q)| +
        |inner ℝ (∑ l ∈ longLayers δ N, signedInnovation l) q| := abs_sub _ _
    _ ≤ C22 * CK ^ 3 + Real.sqrt 2 * Bf := add_le_add hlong hinn

/-! ## (23) Localization to the transition clocks -/

theorem inner_cellUnitVec_flatWaveletVec {N : ℕ} (hN : 1 ≤ N) :
    inner ℝ cellUnitVec (flatWaveletVec N) = thetaCuspSeed (1 / N) / Real.sqrt N := by
  have h := hasSum_inner_cellUnitVec_left (flatWaveletVec N)
  simp only [flatWaveletVec_apply hN] at h
  exact h.unique (hasSum_flatCellWavelet_mul_cellWeight hN)

/-- **(23)** For every fixed `δ > 0`:
`B(N) = Σ_{l<min(K_N,N), l+1 prime power, N^{1−δ}<clock(l+1)<N^{5/4+δ}} ⟨L_l P_N, q_N^flat⟩_H + O_δ(1)`. -/
theorem exists_abs_causalMobiusThetaTail_sub_transitionCovariance_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → |causalMobiusThetaTail N - transitionCovariance δ N| ≤ C := by
  obtain ⟨Ce, hCe0, hCe⟩ := exists_abs_thetaCellDefect_le
  obtain ⟨Bf, hBf0, hBf⟩ := exists_norm_flatWaveletVec_le
  obtain ⟨Sb, hSb0, hSb⟩ := exists_abs_sum_moebius_log_div_le
  obtain ⟨Cs, hCs0, hCs⟩ := exists_abs_thetaCuspSeed_le_sq
  obtain ⟨CS, hCS0, hCS⟩ := exists_abs_sum_shortLayers_le hδ
  obtain ⟨CL, hCL0, hCL⟩ := exists_abs_sum_longLayers_le hδ
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 eventually_gaugeActive
  set Cact := Ce + Real.sqrt 2 * Bf + Sb * Cs + Real.sqrt 110 * Bf + CS + CL
  set Cfin := ∑ N ∈ Finset.range N₀, |causalMobiusThetaTail N - transitionCovariance δ N|
  have hCfin0 : 0 ≤ Cfin := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨Cact + Cfin, by positivity, fun N hN => ?_⟩
  by_cases hNN : N < N₀
  · exact (Finset.single_le_sum
      (f := fun N : ℕ => |causalMobiusThetaTail (N : ℝ) - transitionCovariance δ N|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.2 hNN)).trans (le_add_of_nonneg_left (by positivity))
  have h : gaugeActive N := hN₀ N (not_lt.1 hNN)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNR : (0 : ℝ) < N := by linarith
  have hs1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hN1
  have hden : 1 ≤ (N : ℝ) ^ 2 * Real.sqrt N := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hN1) hs1
  set P := predictableDrift N
  set q := flatWaveletVec N
  set m := min (logarithmicClockThreshold N) N
  -- the exact decomposition
  have hB := causalMobiusThetaTail_natCast_eq_inner_flat hN
  rw [source_eq_martingale_add_drift, inner_add_left] at hB
  have hdecomp : P = (historySpace 0).starProjection P +
      ∑ l ∈ primePowerLayers N, historyLayer l P + (P - (historySpace m).starProjection P) := by
    rw [primePowerLayers, ← sum_historyLayer_predictableDrift_eq_primePower,
      ← starProjection_historySpace_eq_base_add_sum_historyLayer]
    abel
  have hPq : inner ℝ P q = inner ℝ ((historySpace 0).starProjection P) q +
      (∑ l ∈ shortLayers δ N, inner ℝ (historyLayer l P) q + transitionCovariance δ N +
        ∑ l ∈ longLayers δ N, inner ℝ (historyLayer l P) q) +
      inner ℝ (P - (historySpace m).starProjection P) q := by
    conv_lhs => rw [hdecomp]
    rw [inner_add_left, inner_add_left, sum_inner, sum_primePowerLayers_eq_bands δ N]
    rfl
  have hkey : causalMobiusThetaTail N - transitionCovariance δ N =
      thetaCellDefect N + inner ℝ (martingalePart N) q + inner ℝ ((historySpace 0).starProjection P) q +
        inner ℝ (P - (historySpace m).starProjection P) q +
        ∑ l ∈ shortLayers δ N, inner ℝ (historyLayer l P) q +
        ∑ l ∈ longLayers δ N, inner ℝ (historyLayer l P) q := by
    rw [hB, hPq]; ring
  -- the bounds
  have e1 : |thetaCellDefect N| ≤ Ce := (hCe N hN).trans (div_le_self hCe0 hden)
  have e2 : |inner ℝ (martingalePart N) q| ≤ Real.sqrt 2 * Bf :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul
      (Real.le_sqrt_of_sq_le (martingalePart_sq_le_two N)) (hBf N hN) (norm_nonneg _) (by positivity))
  have e3 : |inner ℝ ((historySpace 0).starProjection P) q| ≤ Sb * Cs := by
    rw [starProjection_historySpace_zero_predictableDrift, inner_smul_left,
      inner_cellUnitVec_flatWaveletVec hN, conj_trivial, abs_mul]
    refine mul_le_mul (hSb N) ?_ (abs_nonneg _) hSb0
    rw [abs_div, abs_of_pos (Real.sqrt_pos.2 hNR)]
    calc |thetaCuspSeed (1 / N)| / Real.sqrt N ≤ |thetaCuspSeed (1 / N)| := div_le_self (abs_nonneg _) hs1
      _ ≤ Cs * (1 / N) ^ 2 := hCs _
      _ ≤ Cs * 1 := by
          gcongr
          rw [div_pow, one_pow]
          exact div_le_one_of_le₀ (one_le_pow₀ hN1) (by positivity)
      _ = Cs := mul_one _
  have e4 : |inner ℝ (P - (historySpace m).starProjection P) q| ≤ Real.sqrt 110 * Bf := by
    refine (abs_real_inner_le_norm _ _).trans (mul_le_mul ?_ (hBf N hN) (norm_nonneg _) (by positivity))
    refine Real.le_sqrt_of_sq_le ((predictableDrift_logClockProjection_error_norm_sq_le N).trans ?_)
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have e5 := hCS N h
  have e6 := hCL N h
  rw [hkey]
  have hsum := abs_add_le (thetaCellDefect N + inner ℝ (martingalePart N) q +
    inner ℝ ((historySpace 0).starProjection P) q + inner ℝ (P - (historySpace m).starProjection P) q +
    ∑ l ∈ shortLayers δ N, inner ℝ (historyLayer l P) q) (∑ l ∈ longLayers δ N, inner ℝ (historyLayer l P) q)
  have hsum2 := abs_add_le (thetaCellDefect N + inner ℝ (martingalePart N) q +
    inner ℝ ((historySpace 0).starProjection P) q + inner ℝ (P - (historySpace m).starProjection P) q)
    (∑ l ∈ shortLayers δ N, inner ℝ (historyLayer l P) q)
  have hsum3 := abs_add_le (thetaCellDefect N + inner ℝ (martingalePart N) q +
    inner ℝ ((historySpace 0).starProjection P) q) (inner ℝ (P - (historySpace m).starProjection P) q)
  have hsum4 := abs_add_le (thetaCellDefect N + inner ℝ (martingalePart N) q)
    (inner ℝ ((historySpace 0).starProjection P) q)
  have hsum5 := abs_add_le (thetaCellDefect N) (inner ℝ (martingalePart N) q)
  linarith

/-! ## The transition covariance decides RH -/

/-- **RH ⟺ subpower growth of the transition-clock covariance** (for each fixed `δ > 0`). -/
theorem riemannHypothesis_iff_transitionCovariance_subpower {δ : ℝ} (hδ : 0 < δ) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |transitionCovariance δ N| ≤ C * (N : ℝ) ^ ε := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_causalMobiusThetaTail_sub_transitionCovariance_le hδ
  rw [riemannHypothesis_iff_causalMobiusThetaTail_nat_subpower]
  constructor
  · intro h ε hε
    obtain ⟨C, hC⟩ := h ε hε
    exact ⟨_, natPowerBound_of_abs_sub_le hε.le hD hC⟩
  · intro h ε hε
    obtain ⟨C, hC⟩ := h ε hε
    exact ⟨_, natPowerBound_of_abs_sub_le hε.le (fun N hN => by rw [abs_sub_comm]; exact hD N hN) hC⟩

/-- An off-line zero with horizontal displacement `β` excites the transition clocks: the
covariance violates every `O(N^ε)` bound with `ε < β`. -/
theorem not_transitionCovariance_bound_of_offline_zero {δ : ℝ} (hδ : 0 < δ) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε < |ρ.re - 1 / 2|) :
    ¬ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → |transitionCovariance δ N| ≤ C * (N : ℝ) ^ ε := by
  rintro ⟨C, hC⟩
  obtain ⟨D, hD0, hD⟩ := exists_abs_causalMobiusThetaTail_sub_transitionCovariance_le hδ
  have hB := natPowerBound_of_abs_sub_le hε0 (fun N hN => by rw [abs_sub_comm]; exact hD N hN) hC
  obtain ⟨C', hC'⟩ := exists_causalMobiusThetaTail_bound_of_nat hε0 hB
  rcases le_or_gt (1 / 2 : ℝ) ρ.re with hr | hr
  · rw [abs_of_nonneg (by linarith)] at hε
    exact causalMobiusThetaTail_growth_excludes_zero hε0 hC' hρ (by linarith) h1
  · rw [abs_of_neg (by linarith)] at hε
    have hz : riemannZeta (1 - ρ) = 0 := (riemannZeta_one_sub_eq_zero_iff h0 h1).2 hρ
    exact causalMobiusThetaTail_growth_excludes_zero hε0 hC' hz (by simp; linarith) (by simp; linarith)

end

end RHTower
