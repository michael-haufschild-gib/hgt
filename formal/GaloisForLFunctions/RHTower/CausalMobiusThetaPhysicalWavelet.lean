import GaloisForLFunctions.RHTower.CausalMobiusThetaPhysicalSource
import GaloisForLFunctions.RHTower.EulerDeletionNestedProjectionCovariance

/-!
# The theta wavelet in the physical Hilbert space

The physical inner product `⟨u,v⟩_H = Σ_{r≥1} u(r)v(r)/(r(r+1))` is the `L²` inner product of
the physical cell law `cellMeasure` (cell `j` is `r = j + 1`).  This module realizes the smooth
complete-cell wavelet `q_N` as a vector of that space and proves:

* `sup_N ‖q_N‖_H < ∞`, `q_N(r) = O_r(N^{−5/2})`, and `q_N ⇀ 0` weakly;
* the moments `Σ q_N(r)/(r(r+1)) = g(1/N)/√N` and `Σ r q_N(r)/(r(r+1)) = k(log N)`;
* `e_N = O(N^{−5/2})`, **(15)** `B(N) = ⟨C_N,q_N⟩_H + e_N`, **(16)** `|B(N)| ≤ C(1+E_N)`,
  **(17)** `B(N) = ⟨P_N,q_N⟩_H + O(1)`;
* the continuum profile `Q(u) = −u²g'(u)` with `∫₀^∞ Q/u² = g(0) = 0`, `∫₀^∞ Q/u = ∫₀^∞ g = 0`,
  `g = −2π(u³e^{−πu²})'`, and `q_N(⌊uN⌋)/√N → Q(u)`;
* **(20)** `RH ⟺ ∀ε, |⟨P_N,q_N⟩_H| = O(N^ε)`; subpower `E_N` or `‖P_N‖` implies RH; an off-line
  zero with displacement `β` violates every `O(N^ε)` bound with `ε < β` for all three.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

namespace DeletionResidueMartingale

theorem cellWeight_pos (j : ℕ) : 0 < cellWeight j := by unfold cellWeight; positivity

theorem cellMeasure_singleton_eq (j : ℕ) : cellMeasure {j} = ENNReal.ofReal (cellWeight j) := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]; rfl

theorem hasSum_integral_cellMeasure {f : ℕ → ℝ} (hf : Integrable f cellMeasure) :
    HasSum (fun j => cellWeight j * f j) (∫ j, f j ∂cellMeasure) := by
  rw [← Measure.sum_smul_dirac cellMeasure] at hf
  have h := hasSum_integral_measure hf
  rw [Measure.sum_smul_dirac] at h
  have he : (fun j => cellWeight j * f j) =
      fun i => ∫ x, f x ∂(cellMeasure {i} • Measure.dirac i) := by
    funext j
    rw [integral_smul_measure, integral_dirac, smul_eq_mul, ← measureReal_def, cellMeasure_singleton]
  rw [he]
  exact h

/-- A real sequence with convergent weighted square series lies in the physical `L²`. -/
theorem memLp_two_of_summable {f : ℕ → ℝ} (hf : Summable fun j => f j ^ 2 * cellWeight j) :
    MemLp f 2 cellMeasure := by
  have hm : AEStronglyMeasurable f cellMeasure := (measurable_of_countable f).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun j => sq_nonneg (f j)),
    lintegral_countable']
  simp_rw [cellMeasure_singleton_eq, ← ENNReal.ofReal_mul (sq_nonneg _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => mul_nonneg (sq_nonneg _) (cellWeight_pos j).le) hf]
  exact ENNReal.ofReal_lt_top

/-- The physical vector of a real sequence (zero if the sequence is not square-summable). -/
def physVec (f : ℕ → ℝ) : Lp ℝ 2 cellMeasure := by
  classical
  exact if h : Summable (fun j => f j ^ 2 * cellWeight j) then (memLp_two_of_summable h).toLp f else 0

theorem physVec_apply {f : ℕ → ℝ} (hf : Summable fun j => f j ^ 2 * cellWeight j) (j : ℕ) :
    physVec f j = f j := by
  unfold physVec
  rw [dif_pos hf]
  exact cell_point_eq_of_ae (MemLp.coeFn_toLp _) j

theorem hasSum_inner (u v : Lp ℝ 2 cellMeasure) :
    HasSum (fun j => u j * v j * cellWeight j) (inner ℝ u v) := by
  rw [L2.inner_def]
  have h := hasSum_integral_cellMeasure (L2.integrable_inner (𝕜 := ℝ) u v)
  convert h using 1
  funext j
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem inner_eq_tsum (u v : Lp ℝ 2 cellMeasure) :
    inner ℝ u v = ∑' j, u j * v j * cellWeight j := (hasSum_inner u v).tsum_eq.symm

theorem hasSum_norm_sq (v : Lp ℝ 2 cellMeasure) :
    HasSum (fun j => v j ^ 2 * cellWeight j) (‖v‖ ^ 2) := by
  have h := hasSum_inner v v
  rw [real_inner_self_eq_norm_sq] at h
  convert h using 2 with j
  ring

end DeletionResidueMartingale

/-! ## Increments of the seed -/

/-- `|g'(x)| ≤ K x (1+x)^{−4}` for `x ≥ 0`. -/
theorem exists_abs_thetaCuspSeedDeriv_le_profile :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 ≤ x → |thetaCuspSeedDeriv x| ≤ K * (x / (1 + x) ^ 4) := by
  obtain ⟨K1, hK1, h1⟩ := exists_abs_thetaCuspSeedDeriv_le_mul
  obtain ⟨K3, hK3, h3⟩ := exists_abs_thetaCuspSeedDeriv_le_inv_cube
  refine ⟨16 * K1 + 2 * K3, by positivity, fun x hx => ?_⟩
  have hpos : 0 < (1 + x) ^ 4 := by positivity
  have hq : 0 ≤ x / (1 + x) ^ 4 := by positivity
  rcases le_total x 1 with hx1 | hx1
  · have h := h1 x
    rw [abs_of_nonneg hx] at h
    have h16 : (1 + x) ^ 4 ≤ 16 := by
      calc (1 + x) ^ 4 ≤ 2 ^ 4 := by gcongr; linarith
        _ = 16 := by norm_num
    have hx' : x ≤ 16 * (x / (1 + x) ^ 4) := by
      rw [mul_div_assoc', le_div_iff₀ hpos]
      nlinarith
    calc |thetaCuspSeedDeriv x| ≤ K1 * x := h
      _ ≤ K1 * (16 * (x / (1 + x) ^ 4)) := mul_le_mul_of_nonneg_left hx' hK1
      _ ≤ (16 * K1 + 2 * K3) * (x / (1 + x) ^ 4) := by nlinarith
  · have hinv : ((1 + x) ^ 3)⁻¹ ≤ 2 * (x / (1 + x) ^ 4) := by
      rw [show 2 * (x / (1 + x) ^ 4) = 2 * x / (1 + x) * ((1 + x) ^ 3)⁻¹ by field_simp]
      refine le_mul_of_one_le_left (by positivity) ?_
      rw [le_div_iff₀ (by positivity)]
      linarith
    calc |thetaCuspSeedDeriv x| ≤ K3 * ((1 + x) ^ 3)⁻¹ := h3 x hx
      _ ≤ K3 * (2 * (x / (1 + x) ^ 4)) := mul_le_mul_of_nonneg_left hinv hK3
      _ ≤ (16 * K1 + 2 * K3) * (x / (1 + x) ^ 4) := by nlinarith

theorem abs_thetaCuspSeed_sub_le {a b M : ℝ} (hab : a ≤ b)
    (hM : ∀ x ∈ Icc a b, |thetaCuspSeedDeriv x| ≤ M) :
    |thetaCuspSeed a - thetaCuspSeed b| ≤ M * (b - a) := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := thetaCuspSeed)
    (f' := thetaCuspSeedDeriv) (fun x _ => (hasDerivAt_thetaCuspSeed x).hasDerivWithinAt)
    (fun x hx => by rw [Real.norm_eq_abs]; exact hM x (Ico_subset_Icc_self hx)) b ⟨hab, le_rfl⟩
  rwa [Real.norm_eq_abs, abs_sub_comm] at h

/-- `|g(r/N) − g((r+1)/N)| ≤ K (r+1)/N²`. -/
theorem exists_abs_thetaSeed_increment_le_linear : ∃ K : ℝ, 0 ≤ K ∧ ∀ N r : ℕ, 1 ≤ N →
    |thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N)| ≤ K * ((r : ℝ) + 1) / (N : ℝ) ^ 2 := by
  obtain ⟨K, hK, h⟩ := exists_abs_thetaCuspSeedDeriv_le_mul
  refine ⟨K, hK, fun N r hN => ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hab : (r : ℝ) / N ≤ ((r : ℝ) + 1) / N := by gcongr; linarith
  refine (abs_thetaCuspSeed_sub_le hab (M := K * (((r : ℝ) + 1) / N)) fun x hx => ?_).trans
    (le_of_eq ?_)
  · have hx0 : 0 ≤ x := le_trans (by positivity) hx.1
    calc |thetaCuspSeedDeriv x| ≤ K * |x| := h x
      _ ≤ K * (((r : ℝ) + 1) / N) := by
          rw [abs_of_nonneg hx0]; exact mul_le_mul_of_nonneg_left hx.2 hK
  · field_simp
    ring

/-- `|g(r/N) − g((r+1)/N)| ≤ K (r+1) N² (N+r)^{−4}`. -/
theorem exists_abs_thetaSeed_increment_le_profile : ∃ K : ℝ, 0 ≤ K ∧ ∀ N r : ℕ, 1 ≤ N →
    |thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N)| ≤
      K * (((r : ℝ) + 1) * (N : ℝ) ^ 2 / ((N : ℝ) + r) ^ 4) := by
  obtain ⟨K, hK, h⟩ := exists_abs_thetaCuspSeedDeriv_le_profile
  refine ⟨K, hK, fun N r hN => ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hab : (r : ℝ) / N ≤ ((r : ℝ) + 1) / N := by gcongr; linarith
  have hbound : ∀ x ∈ Icc ((r : ℝ) / N) (((r : ℝ) + 1) / N), |thetaCuspSeedDeriv x| ≤
      K * ((((r : ℝ) + 1) / N) / (1 + (r : ℝ) / N) ^ 4) := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans (by positivity) hx.1
    refine (h x hx0).trans (mul_le_mul_of_nonneg_left ?_ hK)
    apply div_le_div₀ (by positivity) hx.2 (by positivity)
    gcongr
    exact hx.1
  refine (abs_thetaCuspSeed_sub_le hab hbound).trans (le_of_eq ?_)
  have hNr : (0 : ℝ) < N + r := by positivity
  field_simp
  ring

/-! ## The uniform physical energy of the wavelet -/

theorem wavelet_energy_rational_le {a n : ℝ} (ha : 1 ≤ a) (hn : 1 ≤ n) :
    a * (a + 1) ^ 3 * n ^ 3 / (n + a) ^ 8 ≤ 8 * n / ((n + a - 1) * (n + a)) := by
  have hna : 0 < n + a - 1 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : (a + 1) ^ 3 ≤ 8 * a ^ 3 := by
    calc (a + 1) ^ 3 ≤ (2 * a) ^ 3 := by gcongr; linarith
      _ = 8 * a ^ 3 := by ring
  have h2 : (n + a - 1) * (n + a) ≤ (n + a) ^ 2 := by nlinarith
  have h3 : a ^ 4 * n ^ 2 ≤ (n + a) ^ 6 := by
    have ha' : a ^ 4 ≤ (n + a) ^ 4 := by gcongr; linarith
    have hn' : n ^ 2 ≤ (n + a) ^ 2 := by gcongr; linarith
    calc a ^ 4 * n ^ 2 ≤ (n + a) ^ 4 * (n + a) ^ 2 := mul_le_mul ha' hn' (by positivity) (by positivity)
      _ = (n + a) ^ 6 := by ring
  calc a * (a + 1) ^ 3 * n ^ 3 * ((n + a - 1) * (n + a)) ≤ a * (8 * a ^ 3) * n ^ 3 * (n + a) ^ 2 := by
        gcongr
    _ = 8 * n * (a ^ 4 * n ^ 2) * (n + a) ^ 2 := by ring
    _ ≤ 8 * n * (n + a) ^ 6 * (n + a) ^ 2 := by gcongr
    _ = 8 * n * (n + a) ^ 8 := by ring

theorem thetaCellWavelet_sq_mul_cellWeight {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    thetaCellWavelet N (j + 1) ^ 2 * DeletionResidueMartingale.cellWeight j =
      ((j : ℝ) + 1) * ((j : ℝ) + 2) * (thetaCuspSeed (((j + 1 : ℕ) : ℝ) / N) -
        thetaCuspSeed ((((j + 1 : ℕ) : ℝ) + 1) / N)) ^ 2 / N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [thetaCellWavelet, DeletionResidueMartingale.cellWeight, div_pow,
    Real.sq_sqrt (Nat.cast_nonneg N)]
  push_cast
  field_simp
  ring

/-- `sup_N ‖q_N‖_H < ∞`: `Σ_{r≥1} q_N(r)²/(r(r+1)) ≤ Q` for all `N ≥ 1`. -/
theorem exists_thetaCellWavelet_energy_le : ∃ Q : ℝ, 0 ≤ Q ∧ ∀ N : ℕ, 1 ≤ N →
    Summable (fun j => thetaCellWavelet N (j + 1) ^ 2 * DeletionResidueMartingale.cellWeight j) ∧
      ∑' j, thetaCellWavelet N (j + 1) ^ 2 * DeletionResidueMartingale.cellWeight j ≤ Q := by
  obtain ⟨K, hK, hinc⟩ := exists_abs_thetaSeed_increment_le_profile
  refine ⟨8 * K ^ 2, by positivity, fun N hN => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set T : ℕ → ℝ := fun j => (N : ℝ) * (1 / ((N : ℝ) + j) - 1 / ((N : ℝ) + j + 1)) with hT
  have hT0 : ∀ j, 0 ≤ T j := fun j => by
    simp only [T]
    refine mul_nonneg (by positivity) (sub_nonneg.2 ?_)
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hTsum : ∀ M, ∑ j ∈ Finset.range M, T j ≤ 1 := by
    intro M
    have h := Finset.sum_range_sub' (fun j : ℕ => 1 / ((N : ℝ) + j)) M
    simp only [T, ← Finset.mul_sum]
    have hsh : ∀ j : ℕ, 1 / ((N : ℝ) + j) - 1 / ((N : ℝ) + j + 1) =
        1 / ((N : ℝ) + j) - 1 / ((N : ℝ) + ((j + 1 : ℕ) : ℝ)) := by intro j; push_cast; ring_nf
    rw [Finset.sum_congr rfl fun j _ => hsh j, h]
    simp only [Nat.cast_zero, add_zero]
    rw [mul_sub, mul_one_div_cancel (by positivity)]
    have : 0 ≤ (N : ℝ) * (1 / ((N : ℝ) + M)) := by positivity
    linarith
  have hTs : Summable T := summable_of_sum_range_le hT0 hTsum
  have hterm : ∀ j, thetaCellWavelet N (j + 1) ^ 2 * DeletionResidueMartingale.cellWeight j ≤
      8 * K ^ 2 * T j := by
    intro j
    rw [thetaCellWavelet_sq_mul_cellWeight hN]
    have hb := hinc N (j + 1) hN
    have hsq : (thetaCuspSeed (((j + 1 : ℕ) : ℝ) / N) - thetaCuspSeed ((((j + 1 : ℕ) : ℝ) + 1) / N)) ^ 2 ≤
        (K * ((((j + 1 : ℕ) : ℝ) + 1) * (N : ℝ) ^ 2 / ((N : ℝ) + ((j + 1 : ℕ) : ℝ)) ^ 4)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
    have hrat := wavelet_energy_rational_le (a := (j : ℝ) + 1) (n := N) (by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]) hNR
    have hTj : T j = (N : ℝ) / ((N + ((j : ℝ) + 1) - 1) * (N + ((j : ℝ) + 1))) := by
      simp only [T]
      rw [show (N : ℝ) + ((j : ℝ) + 1) - 1 = N + j by ring]
      have h1 : (N : ℝ) + j ≠ 0 := by positivity
      have h2 : (N : ℝ) + ((j : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    rw [hTj]
    push_cast at hsq ⊢
    calc ((j : ℝ) + 1) * ((j : ℝ) + 2) * (thetaCuspSeed (((j : ℝ) + 1) / N) -
          thetaCuspSeed (((j : ℝ) + 1 + 1) / N)) ^ 2 / N
        ≤ ((j : ℝ) + 1) * ((j : ℝ) + 2) * (K * (((j : ℝ) + 1 + 1) * (N : ℝ) ^ 2 /
            ((N : ℝ) + ((j : ℝ) + 1)) ^ 4)) ^ 2 / N := by gcongr
      _ = K ^ 2 * (((j : ℝ) + 1) * ((j : ℝ) + 1 + 1) ^ 3 * (N : ℝ) ^ 3 / ((N : ℝ) + ((j : ℝ) + 1)) ^ 8) := by
          have : (N : ℝ) ≠ 0 := by positivity
          field_simp
          ring
      _ ≤ K ^ 2 * (8 * N / ((N + ((j : ℝ) + 1) - 1) * (N + ((j : ℝ) + 1)))) :=
          mul_le_mul_of_nonneg_left hrat (by positivity)
      _ = 8 * K ^ 2 * ((N : ℝ) / ((N + ((j : ℝ) + 1) - 1) * (N + ((j : ℝ) + 1)))) := by ring
  have hnn : ∀ j, 0 ≤ thetaCellWavelet N (j + 1) ^ 2 * DeletionResidueMartingale.cellWeight j :=
    fun j => mul_nonneg (sq_nonneg _) (DeletionResidueMartingale.cellWeight_pos j).le
  refine ⟨Summable.of_nonneg_of_le hnn hterm (hTs.mul_left _), ?_⟩
  refine Real.tsum_le_of_sum_range_le hnn fun M => ?_
  calc ∑ j ∈ Finset.range M, thetaCellWavelet N (j + 1) ^ 2 * DeletionResidueMartingale.cellWeight j
      ≤ ∑ j ∈ Finset.range M, 8 * K ^ 2 * T j := Finset.sum_le_sum fun j _ => hterm j
    _ = 8 * K ^ 2 * ∑ j ∈ Finset.range M, T j := by rw [Finset.mul_sum]
    _ ≤ 8 * K ^ 2 * 1 := mul_le_mul_of_nonneg_left (hTsum M) (by positivity)
    _ = 8 * K ^ 2 := mul_one _

/-! ## The wavelet vector -/

/-- The wavelet `q_N` in the physical Hilbert space (cell `j` is `r = j + 1`). -/
def thetaWaveletVec (N : ℕ) : Lp ℝ 2 DeletionResidueMartingale.cellMeasure :=
  DeletionResidueMartingale.physVec fun j => thetaCellWavelet N (j + 1)

theorem summable_thetaCellWavelet_sq {N : ℕ} (hN : 1 ≤ N) :
    Summable fun j => thetaCellWavelet N (j + 1) ^ 2 * DeletionResidueMartingale.cellWeight j := by
  obtain ⟨Q, -, hQ⟩ := exists_thetaCellWavelet_energy_le
  exact (hQ N hN).1

theorem thetaWaveletVec_apply {N : ℕ} (hN : 1 ≤ N) (j : ℕ) :
    thetaWaveletVec N j = thetaCellWavelet N (j + 1) :=
  DeletionResidueMartingale.physVec_apply (summable_thetaCellWavelet_sq hN) j

/-- `sup_N ‖q_N‖_H < ∞`. -/
theorem exists_norm_thetaWaveletVec_le : ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ‖thetaWaveletVec N‖ ≤ B := by
  obtain ⟨Q, hQ0, hQ⟩ := exists_thetaCellWavelet_energy_le
  refine ⟨Real.sqrt Q, Real.sqrt_nonneg _, fun N hN => ?_⟩
  have h := DeletionResidueMartingale.hasSum_norm_sq (thetaWaveletVec N)
  have hsq : ‖thetaWaveletVec N‖ ^ 2 ≤ Q := by
    rw [← h.tsum_eq]
    calc ∑' j, thetaWaveletVec N j ^ 2 * DeletionResidueMartingale.cellWeight j
        = ∑' j, thetaCellWavelet N (j + 1) ^ 2 * DeletionResidueMartingale.cellWeight j :=
          tsum_congr fun j => by rw [thetaWaveletVec_apply hN]
      _ ≤ Q := (hQ N hN).2
  exact Real.le_sqrt_of_sq_le hsq

/-- For each fixed cell, `|q_N(r)| ≤ K r (r+1)² N^{−5/2}`. -/
theorem exists_abs_thetaCellWavelet_le_cell : ∃ K : ℝ, 0 ≤ K ∧ ∀ N r : ℕ, 1 ≤ N →
    |thetaCellWavelet N r| ≤ K * ((r : ℝ) * ((r : ℝ) + 1) ^ 2) / ((N : ℝ) ^ 2 * Real.sqrt N) := by
  obtain ⟨K, hK, h⟩ := exists_abs_thetaSeed_increment_le_linear
  refine ⟨K, hK, fun N r hN => ?_⟩
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  rw [thetaCellWavelet, abs_div, abs_of_pos hs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r * (r + 1))]
  calc (r : ℝ) * (r + 1) * |thetaCuspSeed (r / N) - thetaCuspSeed (((r : ℝ) + 1) / N)| / Real.sqrt N
      ≤ (r : ℝ) * (r + 1) * (K * ((r : ℝ) + 1) / (N : ℝ) ^ 2) / Real.sqrt N := by gcongr; exact h N r hN
    _ = _ := by field_simp

/-- `q_N(r) → 0` for each fixed cell `r`. -/
theorem tendsto_thetaCellWavelet (r : ℕ) : Tendsto (fun N : ℕ => thetaCellWavelet N r) atTop (𝓝 0) := by
  obtain ⟨K, hK, h⟩ := exists_abs_thetaCellWavelet_le_cell
  have hlim : Tendsto (fun N : ℕ => K * ((r : ℝ) * ((r : ℝ) + 1) ^ 2) / (N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Real.norm_eq_abs]
  refine (h N r hN).trans ?_
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 hNR
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  calc (N : ℝ) = N * 1 * 1 := by ring
    _ ≤ N * N * Real.sqrt N := by gcongr
    _ = (N : ℝ) ^ 2 * Real.sqrt N := by ring

/-- `q_N ⇀ 0` weakly in the physical Hilbert space. -/
theorem tendsto_inner_thetaWaveletVec (v : Lp ℝ 2 DeletionResidueMartingale.cellMeasure) :
    Tendsto (fun N => inner ℝ v (thetaWaveletVec N)) atTop (𝓝 0) := by
  open DeletionResidueMartingale in
  obtain ⟨B, hB0, hB⟩ := exists_norm_thetaWaveletVec_le
  have hf := hasSum_norm_sq v
  set f : ℕ → ℝ := fun j => v j ^ 2 * cellWeight j with hfdef
  have hf0 : ∀ j, 0 ≤ f j := fun j => mul_nonneg (sq_nonneg _) (cellWeight_pos j).le
  let t : ℕ → ℕ → ℝ := fun M j => if j < M then 0 else v j
  have hts : ∀ M, Summable fun j => t M j ^ 2 * cellWeight j := by
    intro M
    refine hf.summable.of_nonneg_of_le
      (fun j => mul_nonneg (sq_nonneg _) (cellWeight_pos j).le) fun j => ?_
    by_cases h : j < M
    · simp only [t, if_pos h]; simpa using hf0 j
    · simp only [t, if_neg h, f]; exact le_rfl
  have hnorm : ∀ M, ‖physVec (t M)‖ ^ 2 = ∑' j, f (j + M) := by
    intro M
    rw [← (hasSum_norm_sq _).tsum_eq]
    simp_rw [physVec_apply (hts M)]
    rw [← (hts M).sum_add_tsum_nat_add M,
      Finset.sum_eq_zero fun j hj => by simp [t, Finset.mem_range.1 hj], zero_add]
    refine tsum_congr fun j => ?_
    simp [t, f]
  have hsplit : ∀ M N, 1 ≤ N → inner ℝ v (thetaWaveletVec N) =
      ∑ j ∈ Finset.range M, v j * thetaCellWavelet N (j + 1) * cellWeight j +
        inner ℝ (physVec (t M)) (thetaWaveletVec N) := by
    intro M N hN
    have h1 := hasSum_inner v (thetaWaveletVec N)
    have h2 := hasSum_inner (physVec (t M)) (thetaWaveletVec N)
    have h3 : HasSum (fun j => if j < M then v j * thetaWaveletVec N j * cellWeight j else 0)
        (∑ j ∈ Finset.range M, if j < M then v j * thetaWaveletVec N j * cellWeight j else 0) :=
      hasSum_sum_of_ne_finset_zero fun j hj => by
        rw [if_neg (by simpa [Finset.mem_range] using hj)]
    have h4 := h3.add h2
    have heq : (fun j => (if j < M then v j * thetaWaveletVec N j * cellWeight j else 0) +
        physVec (t M) j * thetaWaveletVec N j * cellWeight j) =
        fun j => v j * thetaWaveletVec N j * cellWeight j := by
      funext j
      rw [physVec_apply (hts M)]
      by_cases h : j < M <;> simp [t, h]
    rw [heq] at h4
    rw [h1.unique h4]
    congr 1
    exact Finset.sum_congr rfl fun j hj => by
      rw [if_pos (Finset.mem_range.1 hj), thetaWaveletVec_apply hN]
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ := ε / (2 * (B + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨M, hM⟩ := ((tendsto_sum_nat_add f).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < δ ^ 2))).exists
  have hfin : Tendsto (fun N : ℕ => ∑ j ∈ Finset.range M,
      v j * thetaCellWavelet N (j + 1) * cellWeight j) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range M) fun j _ =>
      ((tendsto_thetaCellWavelet (j + 1)).const_mul (v j)).mul_const (cellWeight j)
    simpa using this
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 hfin (ε / 2) (by positivity)
  refine ⟨max N0 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hA := hN0 N (le_of_max_le_left hN)
  rw [Real.dist_eq, sub_zero] at hA ⊢
  rw [hsplit M N hN1]
  have hnM : ‖physVec (t M)‖ < δ := by
    rw [← sq_lt_sq₀ (norm_nonneg _) hδ.le, hnorm M]; exact hM
  have hδB : δ * B ≤ ε / 2 := by
    have hB1 : B / (B + 1) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
    calc δ * B = ε / 2 * (B / (B + 1)) := by rw [hδdef]; field_simp
      _ ≤ ε / 2 * 1 := mul_le_mul_of_nonneg_left hB1 (by positivity)
      _ = ε / 2 := mul_one _
  calc |∑ j ∈ Finset.range M, v j * thetaCellWavelet N (j + 1) * cellWeight j +
        inner ℝ (physVec (t M)) (thetaWaveletVec N)|
      ≤ |∑ j ∈ Finset.range M, v j * thetaCellWavelet N (j + 1) * cellWeight j| +
        |inner ℝ (physVec (t M)) (thetaWaveletVec N)| := abs_add_le _ _
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add_of_lt_of_le hA ?_
        calc |inner ℝ (physVec (t M)) (thetaWaveletVec N)| ≤
              ‖physVec (t M)‖ * ‖thetaWaveletVec N‖ := abs_real_inner_le_norm _ _
          _ ≤ δ * B := mul_le_mul hnM.le (hB N hN1) (norm_nonneg _) hδ.le
          _ ≤ ε / 2 := hδB
    _ = ε := by ring

/-! ## The two exact discrete moments -/

/-- `Σ_{r≥1} q_N(r)/(r(r+1)) = g(1/N)/√N`. -/
theorem hasSum_thetaCellWavelet_mul_cellWeight {N : ℕ} (hN : 1 ≤ N) :
    HasSum (fun j => thetaCellWavelet N (j + 1) * DeletionResidueMartingale.cellWeight j)
      (thetaCuspSeed (1 / N) / Real.sqrt N) := by
  set u : ℕ → ℝ := fun j => thetaCuspSeed (((j + 1 : ℕ) : ℝ) / N) with hu_def
  have hu : Summable u := (summable_nat_add_iff 1).2 (summable_thetaCuspSeed_div hN)
  have h1 := hu.hasSum
  have h2 : HasSum (fun j => u (j + 1)) (∑' j, u j - u 0) := by
    simpa using (hasSum_nat_add_iff' 1).2 h1
  have h3 := (h1.sub h2).div_const (Real.sqrt N)
  have heq : (fun j => (u j - u (j + 1)) / Real.sqrt N) =
      fun j => thetaCellWavelet N (j + 1) * DeletionResidueMartingale.cellWeight j := by
    funext j
    rw [thetaCellWavelet_mul_cellWeight]
    simp only [u]
    push_cast
    ring_nf
  rw [heq, sub_sub_cancel] at h3
  simpa [u] using h3

/-- `Σ_{r≥1} r q_N(r)/(r(r+1)) = k(log N)`, absolutely convergent. -/
theorem hasSum_natCast_mul_thetaCellWavelet_mul_cellWeight {N : ℕ} (hN : 1 ≤ N) :
    HasSum (fun j : ℕ => ((j : ℝ) + 1) * thetaCellWavelet N (j + 1) *
      DeletionResidueMartingale.cellWeight j) (thetaCuspFullSource (Real.log N)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  set u : ℕ → ℝ := fun j => thetaCuspSeed (((j + 1 : ℕ) : ℝ) / N) with hu_def
  set p : ℕ → ℝ := fun j => ((j : ℝ) + 1) * u j with hp_def
  have hu : Summable u := (summable_nat_add_iff 1).2 (summable_thetaCuspSeed_div hN)
  have hp : Summable p := by
    have h := (summable_nat_add_iff 1).2 (summable_natCast_mul_abs_thetaCuspSeed_div hN)
    refine Summable.of_norm_bounded h fun j => ?_
    simp only [p, u, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (j : ℝ) + 1)]
    push_cast
    exact le_rfl
  have hp2 : HasSum (fun j => p j - p (j + 1)) (p 0) := by
    have h2 : HasSum (fun j => p (j + 1)) (∑' j, p j - p 0) := by
      simpa using (hasSum_nat_add_iff' 1).2 hp.hasSum
    simpa [sub_sub_cancel] using hp.hasSum.sub h2
  have hu2 : HasSum (fun j => u (j + 1)) (∑' j, u j - u 0) := by
    simpa using (hasSum_nat_add_iff' 1).2 hu.hasSum
  have h := ((hp2.add hu2).div_const (Real.sqrt N))
  have heq : (fun j => (p j - p (j + 1) + u (j + 1)) / Real.sqrt N) =
      fun j : ℕ => ((j : ℝ) + 1) * thetaCellWavelet N (j + 1) * DeletionResidueMartingale.cellWeight j := by
    funext j
    rw [mul_assoc, thetaCellWavelet_mul_cellWeight]
    simp only [p, u]
    push_cast
    ring
  have hval : (p 0 + (∑' j, u j - u 0)) / Real.sqrt N = thetaCuspFullSource (Real.log N) := by
    have hsum : ∑' j, u j = ∑' r : ℕ, thetaCuspSeed (r / N) := by
      rw [(summable_thetaCuspSeed_div hN).tsum_eq_zero_add]
      simp [u, thetaCuspSeed_zero]
    simp only [p, Nat.cast_zero, zero_add, one_mul]
    rw [add_sub_cancel, hsum, tsum_thetaCuspSeed_div_eq hN]
    field_simp
  rw [heq, hval] at h
  exact h

/-! ## The scalar defect -/

theorem abs_moebiusHarmonic_le (N : ℕ) : |moebiusHarmonic N| ≤ 1 + Real.log N := by
  rw [moebiusHarmonic]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ d ∈ Finset.Icc 1 N, |((ArithmeticFunction.moebius d : ℤ) : ℝ) / d|
      ≤ ∑ d ∈ Finset.Icc 1 N, (1 : ℝ) / d := Finset.sum_le_sum fun d hd => by
          rw [abs_div, Nat.abs_cast]
          gcongr
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    _ = (harmonic N : ℝ) := by rw [harmonic_eq_sum_Icc]
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N

/-- `e_N = O(N^{−5/2})`. -/
theorem exists_abs_thetaCellDefect_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    |thetaCellDefect N| ≤ C / ((N : ℝ) ^ 2 * Real.sqrt N) := by
  obtain ⟨Cs, hCs0, hCs⟩ := exists_abs_thetaCuspSeed_le_sq
  obtain ⟨C3, hC30, hC3⟩ := exists_abs_thetaCuspFullSource_le 3
  refine ⟨Cs + 2 * C3, by positivity, fun N hN => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have h1 : |thetaCuspSeed (1 / N) / Real.sqrt N| ≤ Cs / ((N : ℝ) ^ 2 * Real.sqrt N) := by
    rw [abs_div, abs_of_pos hs]
    calc |thetaCuspSeed (1 / N)| / Real.sqrt N ≤ Cs * (1 / N) ^ 2 / Real.sqrt N := by
          gcongr; exact hCs _
      _ = _ := by field_simp
  have hlog : 1 + Real.log N ≤ 2 * Real.sqrt N := by
    have h := Real.log_le_sub_one_of_pos hs
    rw [Real.log_sqrt hN0.le] at h
    linarith
  have hk : |thetaCuspFullSource (Real.log N)| ≤ C3 / (N : ℝ) ^ 3 := by
    have h := hC3 (Real.log N)
    have he : Real.exp (-(3 * |Real.log N|)) = ((N : ℝ) ^ 3)⁻¹ := by
      rw [abs_of_nonneg (Real.log_nonneg hNR),
        ← Real.exp_log (show (0 : ℝ) < ((N : ℝ) ^ 3)⁻¹ by positivity), Real.log_inv, Real.log_pow]
      push_cast
      ring_nf
    rwa [he, ← div_eq_mul_inv] at h
  have h2 : |moebiusHarmonic N * thetaCuspFullSource (Real.log N)| ≤
      2 * C3 / ((N : ℝ) ^ 2 * Real.sqrt N) := by
    rw [abs_mul]
    calc |moebiusHarmonic N| * |thetaCuspFullSource (Real.log N)| ≤
          (2 * Real.sqrt N) * (C3 / (N : ℝ) ^ 3) :=
          mul_le_mul ((abs_moebiusHarmonic_le N).trans hlog) hk (abs_nonneg _) (by positivity)
      _ = 2 * C3 / ((N : ℝ) ^ 2 * Real.sqrt N) := by
          rw [show (N : ℝ) ^ 3 = N ^ 2 * (Real.sqrt N * Real.sqrt N) by rw [hss]; ring]
          field_simp
  rw [thetaCellDefect, add_div]
  exact (abs_sub _ _).trans (add_le_add h1 h2)

/-! ## (15)–(17) in the physical Hilbert space -/

/-- **(15)** `B(N) = ⟨C_N, q_N⟩_H + e_N`. -/
theorem causalMobiusThetaTail_natCast_eq_inner {N : ℕ} (hN : 1 ≤ N) :
    causalMobiusThetaTail N = inner ℝ (DeletionResidueMartingale.sourceVec
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N) (thetaWaveletVec N) + thetaCellDefect N := by
  rw [causalMobiusThetaTail_natCast_eq_cell_pairing hN, DeletionResidueMartingale.inner_eq_tsum]
  congr 1
  refine tsum_congr fun j => ?_
  rw [DeletionResidueMartingale.sourceVec_apply_eq_cell, thetaWaveletVec_apply hN]

theorem norm_sourceVec_moebius_eq (N : ℕ) :
    ‖DeletionResidueMartingale.sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N‖ =
      ‖DeletionCoefficientTransfer.source (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (DeletionResidueMartingale.sourceVec_energy _ N)

/-- **(16)** `|B(N)| ≤ C (1 + E_N)` with `E_N` the physical norm of the Möbius source. -/
theorem exists_abs_causalMobiusThetaTail_le_physicalNorm : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
    |causalMobiusThetaTail N| ≤
      C * (1 + ‖DeletionCoefficientTransfer.source (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N‖) := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_thetaWaveletVec_le
  obtain ⟨Ce, hCe0, hCe⟩ := exists_abs_thetaCellDefect_le
  refine ⟨B + Ce, by positivity, fun N hN => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 1 ≤ (N : ℝ) ^ 2 * Real.sqrt N :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hNR) (Real.one_le_sqrt.2 hNR)
  set E := ‖DeletionCoefficientTransfer.source (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N‖
  have hE0 : 0 ≤ E := norm_nonneg _
  rw [causalMobiusThetaTail_natCast_eq_inner hN]
  have hi : |inner ℝ (DeletionResidueMartingale.sourceVec
      (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N) (thetaWaveletVec N)| ≤ E * B := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [norm_sourceVec_moebius_eq]
    exact mul_le_mul_of_nonneg_left (hB N hN) hE0
  have he : |thetaCellDefect N| ≤ Ce := (hCe N hN).trans (div_le_self hCe0 hden)
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ E * B + Ce := add_le_add hi he
    _ ≤ (B + Ce) * (1 + E) := by nlinarith

/-- **(17)** `B(N) = ⟨P_N, q_N⟩_H + O(1)` with `P_N` the literal predictable drift. -/
theorem exists_abs_causalMobiusThetaTail_sub_inner_predictableDrift_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ N : ℕ, 1 ≤ N → |causalMobiusThetaTail N -
      inner ℝ (DeletionResidueMartingale.predictableDrift N) (thetaWaveletVec N)| ≤ C := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_thetaWaveletVec_le
  obtain ⟨Ce, hCe0, hCe⟩ := exists_abs_thetaCellDefect_le
  refine ⟨Real.sqrt 2 * B + Ce, by positivity, fun N hN => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hden : 1 ≤ (N : ℝ) ^ 2 * Real.sqrt N :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ hNR) (Real.one_le_sqrt.2 hNR)
  rw [causalMobiusThetaTail_natCast_eq_inner hN, DeletionResidueMartingale.source_eq_martingale_add_drift,
    inner_add_left]
  have hI : ‖DeletionResidueMartingale.martingalePart N‖ ≤ Real.sqrt 2 :=
    Real.le_sqrt_of_sq_le (DeletionResidueMartingale.martingalePart_sq_le_two N)
  have hi : |inner ℝ (DeletionResidueMartingale.martingalePart N) (thetaWaveletVec N)| ≤
      Real.sqrt 2 * B :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul hI (hB N hN) (norm_nonneg _) (by positivity))
  have he : |thetaCellDefect N| ≤ Ce := (hCe N hN).trans (div_le_self hCe0 hden)
  calc _ = |inner ℝ (DeletionResidueMartingale.martingalePart N) (thetaWaveletVec N) +
        thetaCellDefect N| := by ring_nf
    _ ≤ _ := abs_add_le _ _
    _ ≤ _ := add_le_add hi he

/-! ## The continuum profile `Q(u) = −u² g'(u)` -/

/-- The continuum profile of the complete-cell wavelet. -/
def thetaCellProfile (u : ℝ) : ℝ := -(u ^ 2 * thetaCuspSeedDeriv u)

theorem exists_abs_pow_mul_exp_neg_pi_sq_le_inv_one_add_sq (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, |x| ^ k * Real.exp (-Real.pi * x ^ 2) ≤ M * (1 + x ^ 2)⁻¹ := by
  obtain ⟨M0, hM0, h0⟩ := exists_abs_pow_mul_exp_neg_pi_sq_le k
  obtain ⟨M2, hM2, h2⟩ := exists_abs_pow_mul_exp_neg_pi_sq_le (k + 2)
  refine ⟨M0 + M2, by positivity, fun x => ?_⟩
  rw [le_mul_inv_iff₀ (by positivity)]
  have hx : |x| ^ (k + 2) = |x| ^ k * x ^ 2 := by rw [pow_add, sq_abs]
  have h2x := h2 x
  rw [hx] at h2x
  calc |x| ^ k * Real.exp (-Real.pi * x ^ 2) * (1 + x ^ 2) =
        |x| ^ k * Real.exp (-Real.pi * x ^ 2) + |x| ^ k * x ^ 2 * Real.exp (-Real.pi * x ^ 2) := by ring
    _ ≤ M0 + M2 := add_le_add (h0 x) h2x

theorem integrable_of_abs_le_inv_one_add_sq {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (h : ∀ x, |f x| ≤ M * (1 + x ^ 2)⁻¹) : Integrable f :=
  (integrable_inv_one_add_sq.const_mul M).mono' hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact h x)

theorem tendsto_atTop_zero_of_abs_le_inv_one_add_sq {f : ℝ → ℝ} {M : ℝ}
    (h : ∀ x, |f x| ≤ M * (1 + x ^ 2)⁻¹) : Tendsto f atTop (𝓝 0) := by
  have hlim : Tendsto (fun x : ℝ => M * (1 + x ^ 2)⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => 1 + x ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
    simpa using this.inv_tendsto_atTop.const_mul M
  exact squeeze_zero_norm (fun x => by rw [Real.norm_eq_abs]; exact h x) hlim

/-- A family of Gaussian bounds by `(1 + x²)^{−1}` for the seed and its moments. -/
theorem exists_seed_gaussian_bounds : ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ,
    |thetaCuspSeed x| ≤ M * (1 + x ^ 2)⁻¹ ∧ |x * thetaCuspSeed x| ≤ M * (1 + x ^ 2)⁻¹ ∧
    |thetaCuspSeedDeriv x| ≤ M * (1 + x ^ 2)⁻¹ ∧ |x * thetaCuspSeedDeriv x| ≤ M * (1 + x ^ 2)⁻¹ ∧
    |x ^ 3 * Real.exp (-Real.pi * x ^ 2)| ≤ M * (1 + x ^ 2)⁻¹ := by
  choose M hM0 hM using exists_abs_pow_mul_exp_neg_pi_sq_le_inv_one_add_sq
  set T : ℝ := M 1 + M 2 + M 3 + M 4 + M 5 + M 6 with hT
  have hT0 : 0 ≤ T := by
    have := hM0 1; have := hM0 2; have := hM0 3; have := hM0 4; have := hM0 5; have := hM0 6
    linarith
  have hp : 0 < Real.pi := Real.pi_pos
  set c : ℝ := 2 * Real.pi * (4 * Real.pi ^ 2 + 14 * Real.pi + 6) + 4 * Real.pi ^ 2 + 6 * Real.pi + 1
    with hc
  refine ⟨c * T, by positivity, fun x => ?_⟩
  set i : ℝ := (1 + x ^ 2)⁻¹ with hi_def
  have hi : 0 ≤ i := by positivity
  set e : ℝ := Real.exp (-Real.pi * x ^ 2) with he_def
  have he : 0 < e := Real.exp_pos _
  have hb : ∀ k ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ), |x| ^ k * e ≤ T * i := by
    intro k hk
    refine (hM k x).trans (mul_le_mul_of_nonneg_right ?_ hi)
    have := hM0 1; have := hM0 2; have := hM0 3; have := hM0 4; have := hM0 5; have := hM0 6
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> linarith
  have b1 := hb 1 (by simp); have b2 := hb 2 (by simp); have b3 := hb 3 (by simp)
  have b4 := hb 4 (by simp); have b5 := hb 5 (by simp); have b6 := hb 6 (by simp)
  have hTi : 0 ≤ T * i := mul_nonneg hT0 hi
  have hfin : ∀ d : ℝ, d ≤ c → d * (T * i) ≤ c * T * i := fun d hd => by
    rw [mul_assoc c]; exact mul_le_mul_of_nonneg_right hd hTi
  have hA1 : 4 * Real.pi ^ 2 + 6 * Real.pi ≤ c := by
    have : 0 ≤ 2 * Real.pi * (4 * Real.pi ^ 2 + 14 * Real.pi + 6) := by positivity
    linarith
  have hA2 : 2 * Real.pi * (4 * Real.pi ^ 2 + 14 * Real.pi + 6) ≤ c := by
    have : 0 ≤ 4 * Real.pi ^ 2 + 6 * Real.pi := by positivity
    linarith
  have hA3 : (1 : ℝ) ≤ c := by
    have : 0 ≤ 2 * Real.pi * (4 * Real.pi ^ 2 + 14 * Real.pi + 6) + 4 * Real.pi ^ 2 + 6 * Real.pi :=
      by positivity
    linarith
  have hg := abs_thetaCuspSeed_le_poly x
  have hg' := abs_thetaCuspSeedDeriv_le_poly x
  have hP : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  have hQ : 0 ≤ 6 * Real.pi := by positivity
  have hR : 0 ≤ 2 * Real.pi * (4 * Real.pi ^ 2) := by positivity
  have hS : 0 ≤ 2 * Real.pi * (14 * Real.pi) := by positivity
  have hU : 0 ≤ 2 * Real.pi * 6 := by positivity
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · calc |thetaCuspSeed x| ≤ (4 * Real.pi ^ 2 * |x| ^ 4 + 6 * Real.pi * |x| ^ 2) * e := hg
      _ = 4 * Real.pi ^ 2 * (|x| ^ 4 * e) + 6 * Real.pi * (|x| ^ 2 * e) := by ring
      _ ≤ 4 * Real.pi ^ 2 * (T * i) + 6 * Real.pi * (T * i) :=
          add_le_add (mul_le_mul_of_nonneg_left b4 hP) (mul_le_mul_of_nonneg_left b2 hQ)
      _ = (4 * Real.pi ^ 2 + 6 * Real.pi) * (T * i) := by ring
      _ ≤ c * T * i := hfin _ hA1
  · rw [abs_mul]
    calc |x| * |thetaCuspSeed x| ≤ |x| * ((4 * Real.pi ^ 2 * |x| ^ 4 + 6 * Real.pi * |x| ^ 2) * e) :=
          mul_le_mul_of_nonneg_left hg (abs_nonneg x)
      _ = 4 * Real.pi ^ 2 * (|x| ^ 5 * e) + 6 * Real.pi * (|x| ^ 3 * e) := by ring
      _ ≤ 4 * Real.pi ^ 2 * (T * i) + 6 * Real.pi * (T * i) :=
          add_le_add (mul_le_mul_of_nonneg_left b5 hP) (mul_le_mul_of_nonneg_left b3 hQ)
      _ = (4 * Real.pi ^ 2 + 6 * Real.pi) * (T * i) := by ring
      _ ≤ c * T * i := hfin _ hA1
  · calc |thetaCuspSeedDeriv x| ≤ 2 * Real.pi * (4 * Real.pi ^ 2 * |x| ^ 5 + 14 * Real.pi * |x| ^ 3 +
          6 * |x|) * e := hg'
      _ = 2 * Real.pi * (4 * Real.pi ^ 2) * (|x| ^ 5 * e) +
          2 * Real.pi * (14 * Real.pi) * (|x| ^ 3 * e) + 2 * Real.pi * 6 * (|x| ^ 1 * e) := by ring
      _ ≤ 2 * Real.pi * (4 * Real.pi ^ 2) * (T * i) + 2 * Real.pi * (14 * Real.pi) * (T * i) +
          2 * Real.pi * 6 * (T * i) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left b5 hR) (mul_le_mul_of_nonneg_left b3 hS))
            (mul_le_mul_of_nonneg_left b1 hU)
      _ = 2 * Real.pi * (4 * Real.pi ^ 2 + 14 * Real.pi + 6) * (T * i) := by ring
      _ ≤ c * T * i := hfin _ hA2
  · rw [abs_mul]
    calc |x| * |thetaCuspSeedDeriv x| ≤ |x| * (2 * Real.pi * (4 * Real.pi ^ 2 * |x| ^ 5 +
          14 * Real.pi * |x| ^ 3 + 6 * |x|) * e) := mul_le_mul_of_nonneg_left hg' (abs_nonneg x)
      _ = 2 * Real.pi * (4 * Real.pi ^ 2) * (|x| ^ 6 * e) +
          2 * Real.pi * (14 * Real.pi) * (|x| ^ 4 * e) + 2 * Real.pi * 6 * (|x| ^ 2 * e) := by ring
      _ ≤ 2 * Real.pi * (4 * Real.pi ^ 2) * (T * i) + 2 * Real.pi * (14 * Real.pi) * (T * i) +
          2 * Real.pi * 6 * (T * i) :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left b6 hR) (mul_le_mul_of_nonneg_left b4 hS))
            (mul_le_mul_of_nonneg_left b2 hU)
      _ = 2 * Real.pi * (4 * Real.pi ^ 2 + 14 * Real.pi + 6) * (T * i) := by ring
      _ ≤ c * T * i := hfin _ hA2
  · rw [abs_mul, abs_pow, abs_of_pos he]
    calc |x| ^ 3 * e ≤ T * i := b3
      _ = 1 * (T * i) := (one_mul _).symm
      _ ≤ c * T * i := hfin _ hA3

/-- The explicit total derivative `g(u) = −2π (u³ e^{−πu²})'`. -/
theorem hasDerivAt_neg_two_pi_gaussCube (u : ℝ) :
    HasDerivAt (fun u : ℝ => -(2 * Real.pi) * (u ^ 3 * Real.exp (-Real.pi * u ^ 2)))
      (thetaCuspSeed u) u := by
  have h := ((hasDerivAt_pow 3 u).fun_mul
    (((hasDerivAt_pow 2 u).const_mul (-Real.pi)).exp)).const_mul (-(2 * Real.pi))
  refine h.congr_deriv ?_
  simp only [thetaCuspSeed, Nat.cast_ofNat]
  ring

/-- `∫₀^∞ g = 0`. -/
theorem integral_Ioi_thetaCuspSeed : ∫ u in Ioi (0 : ℝ), thetaCuspSeed u = 0 := by
  obtain ⟨M, hM0, hM⟩ := exists_seed_gaussian_bounds
  have hint : Integrable thetaCuspSeed :=
    integrable_of_abs_le_inv_one_add_sq continuous_thetaCuspSeed fun x => (hM x).1
  have hlim : Tendsto (fun u : ℝ => -(2 * Real.pi) * (u ^ 3 * Real.exp (-Real.pi * u ^ 2))) atTop
      (𝓝 0) := by
    have := (tendsto_atTop_zero_of_abs_le_inv_one_add_sq fun x => (hM x).2.2.2.2).const_mul
      (-(2 * Real.pi))
    simpa using this
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (f := fun u : ℝ => -(2 * Real.pi) *
    (u ^ 3 * Real.exp (-Real.pi * u ^ 2))) (by fun_prop : Continuous _).continuousWithinAt
    (fun x _ => hasDerivAt_neg_two_pi_gaussCube x) hint.integrableOn hlim
  simpa using h

/-- `∫₀^∞ Q(u)/u² du = g(0)`. -/
theorem integral_Ioi_thetaCellProfile_div_sq_eq :
    ∫ u in Ioi (0 : ℝ), thetaCellProfile u / u ^ 2 = thetaCuspSeed 0 := by
  obtain ⟨M, hM0, hM⟩ := exists_seed_gaussian_bounds
  have hcongr : ∫ u in Ioi (0 : ℝ), thetaCellProfile u / u ^ 2 =
      ∫ u in Ioi (0 : ℝ), -thetaCuspSeedDeriv u := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have : u ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hu)
    rw [thetaCellProfile, neg_div, mul_div_cancel_left₀ _ this]
  have hint : Integrable fun u => -thetaCuspSeedDeriv u :=
    (integrable_of_abs_le_inv_one_add_sq continuous_thetaCuspSeedDeriv fun x => (hM x).2.2.1).neg
  have hlim : Tendsto (fun u => -thetaCuspSeed u) atTop (𝓝 0) := by
    simpa using (tendsto_atTop_zero_of_abs_le_inv_one_add_sq fun x => (hM x).1).neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (f := fun u => -thetaCuspSeed u)
    continuous_thetaCuspSeed.neg.continuousWithinAt
    (fun x _ => (hasDerivAt_thetaCuspSeed x).neg) hint.integrableOn hlim
  rw [hcongr, h]
  ring

/-- **Zeroth physical Mellin moment:** `∫₀^∞ Q(u)/u² du = g(0) = 0`. -/
theorem integral_Ioi_thetaCellProfile_div_sq : ∫ u in Ioi (0 : ℝ), thetaCellProfile u / u ^ 2 = 0 := by
  rw [integral_Ioi_thetaCellProfile_div_sq_eq, thetaCuspSeed_zero]

/-- **First physical Mellin moment:** `∫₀^∞ Q(u)/u du = ∫₀^∞ g = 0`. -/
theorem integral_Ioi_thetaCellProfile_div :
    ∫ u in Ioi (0 : ℝ), thetaCellProfile u / u = ∫ u in Ioi (0 : ℝ), thetaCuspSeed u ∧
      ∫ u in Ioi (0 : ℝ), thetaCellProfile u / u = 0 := by
  obtain ⟨M, hM0, hM⟩ := exists_seed_gaussian_bounds
  have hcongr : ∫ u in Ioi (0 : ℝ), thetaCellProfile u / u =
      ∫ u in Ioi (0 : ℝ), -(u * thetaCuspSeedDeriv u) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have : u ≠ 0 := ne_of_gt hu
    rw [thetaCellProfile, neg_div, sq, mul_assoc, mul_div_cancel_left₀ _ this]
  have hint : Integrable fun u => -(u * thetaCuspSeedDeriv u) :=
    (integrable_of_abs_le_inv_one_add_sq (continuous_id.mul continuous_thetaCuspSeedDeriv)
      fun x => (hM x).2.2.2.1).neg
  set F : ℝ → ℝ := fun u => -(u * thetaCuspSeed u) + -(2 * Real.pi) * (u ^ 3 * Real.exp (-Real.pi * u ^ 2))
  have hF : ∀ x, HasDerivAt F (-(x * thetaCuspSeedDeriv x)) x := by
    intro x
    have h := ((hasDerivAt_id x).fun_mul (hasDerivAt_thetaCuspSeed x)).neg.add
      (hasDerivAt_neg_two_pi_gaussCube x)
    refine h.congr_deriv ?_
    simp only [id]
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    have h1 : Tendsto (fun x => -(x * thetaCuspSeed x)) atTop (𝓝 0) := by
      simpa using (tendsto_atTop_zero_of_abs_le_inv_one_add_sq fun x => (hM x).2.1).neg
    have h2 : Tendsto (fun x => -(2 * Real.pi) * (x ^ 3 * Real.exp (-Real.pi * x ^ 2))) atTop (𝓝 0) := by
      simpa using (tendsto_atTop_zero_of_abs_le_inv_one_add_sq fun x => (hM x).2.2.2.2).const_mul
        (-(2 * Real.pi))
    simpa only [add_zero] using h1.add h2
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := 0) (f := F)
    (((continuous_id.mul continuous_thetaCuspSeed).neg.add (by fun_prop)) : Continuous F).continuousWithinAt
    (fun x _ => hF x) hint.integrableOn hlim
  have hzero : ∫ u in Ioi (0 : ℝ), thetaCellProfile u / u = 0 := by
    rw [hcongr, h]; simp [F]
  exact ⟨by rw [hzero, integral_Ioi_thetaCuspSeed], hzero⟩

/-- At continuum scale the wavelet profile is `Q`: `q_N(⌊uN⌋)/√N → Q(u)` for every `u > 0`. -/
theorem tendsto_thetaCellWavelet_floor_div_sqrt {u : ℝ} (hu : 0 < u) :
    Tendsto (fun N : ℕ => thetaCellWavelet N ⌊u * N⌋₊ / Real.sqrt N) atTop
      (𝓝 (thetaCellProfile u)) := by
  set a : ℕ → ℝ := fun N => (⌊u * N⌋₊ : ℝ) / N with ha
  set b : ℕ → ℝ := fun N => ((⌊u * N⌋₊ : ℝ) + 1) / N with hb
  have hab : ∀ N : ℕ, 1 ≤ N → a N < b N := fun N hN => by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    simp only [a, b]; gcongr; linarith
  have hc : ∀ N : ℕ, ∃ c : ℝ, 1 ≤ N → c ∈ Ioo (a N) (b N) ∧
      thetaCuspSeedDeriv c = (thetaCuspSeed (b N) - thetaCuspSeed (a N)) / (b N - a N) := by
    intro N
    by_cases hN : 1 ≤ N
    · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope thetaCuspSeed thetaCuspSeedDeriv (hab N hN)
        continuous_thetaCuspSeed.continuousOn fun x _ => hasDerivAt_thetaCuspSeed x
      exact ⟨c, fun _ => ⟨hc, hcd⟩⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose c hcN using hc
  have hNat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ha_lim : Tendsto a atTop (𝓝 u) := (tendsto_nat_floor_mul_div_atTop hu.le).comp hNat
  have hb_lim : Tendsto b atTop (𝓝 u) := by
    have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / N) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat
    have := ha_lim.add h1
    rw [add_zero] at this
    refine this.congr' (Eventually.of_forall fun N => ?_)
    simp only [a, b]; ring
  have hc_lim : Tendsto c atTop (𝓝 u) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ha_lim hb_lim ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN using ((hcN N hN).1).1.le
    · filter_upwards [eventually_ge_atTop 1] with N hN using ((hcN N hN).1).2.le
  have hlim : Tendsto (fun N : ℕ => a N * b N * -thetaCuspSeedDeriv (c N)) atTop
      (𝓝 (thetaCellProfile u)) := by
    have := (ha_lim.mul hb_lim).mul ((continuous_thetaCuspSeedDeriv.tendsto u).comp hc_lim).neg
    simpa [thetaCellProfile, sq, mul_assoc] using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNR.le
  have hd : b N - a N = 1 / N := by simp only [a, b]; field_simp; ring
  have hcd := (hcN N hN).2
  rw [hd] at hcd
  have hcd' : thetaCuspSeed (a N) - thetaCuspSeed (b N) = -thetaCuspSeedDeriv (c N) / N := by
    rw [hcd]; field_simp; ring
  simp only [thetaCellWavelet]
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.2 hNR
  change a N * b N * -thetaCuspSeedDeriv (c N) =
    ↑⌊u * ↑N⌋₊ * (↑⌊u * ↑N⌋₊ + 1) * (thetaCuspSeed (a N) - thetaCuspSeed (b N)) / Real.sqrt N /
      Real.sqrt N
  rw [hcd', div_div, hs]
  simp only [a, b]
  field_simp

/-! ## Integer and real subpower bounds -/

/-- An integer-point bound for `B` with fixed exponent `a ≥ 0` propagates to all `t ≥ 1`. -/
theorem exists_causalMobiusThetaTail_bound_of_nat {a C : ℝ} (ha : 0 ≤ a)
    (h : ∀ N : ℕ, 1 ≤ N → |causalMobiusThetaTail N| ≤ C * (N : ℝ) ^ a) :
    ∃ C' : ℝ, ∀ t : ℝ, 1 ≤ t → |causalMobiusThetaTail t| ≤ C' * t ^ a := by
  obtain ⟨C2, hC2⟩ := exists_abs_causalTail_sub_le
  refine ⟨max C 0 + |C2|, fun t ht => ?_⟩
  set N := ⌊t⌋₊ with hNdef
  have hN : 1 ≤ N := Nat.le_floor (by simpa using ht)
  have hNt : (N : ℝ) ≤ t := Nat.floor_le (by linarith)
  have htN : t < N + 1 := Nat.lt_floor_add_one t
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h1 := hC2 N hN t hNt htN
  have h2 := h N hN
  have hNe : (N : ℝ) ^ a ≤ t ^ a := Real.rpow_le_rpow (by positivity) hNt ha
  have hte : 1 ≤ t ^ a := Real.one_le_rpow ht ha
  have hNe0 : 0 ≤ (N : ℝ) ^ a := by positivity
  have hsq : (Real.sqrt N)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.2 hNR)
  have hsq0 : 0 ≤ (Real.sqrt N)⁻¹ := by positivity
  have h3 : |causalMobiusThetaTail t| ≤ |causalMobiusThetaTail N| +
      |causalMobiusThetaTail t - causalMobiusThetaTail N| := by
    have := abs_sub_abs_le_abs_sub (causalMobiusThetaTail t) (causalMobiusThetaTail N)
    linarith
  have h4 : C * (N : ℝ) ^ a ≤ max C 0 * t ^ a :=
    (mul_le_mul_of_nonneg_right (le_max_left C 0) hNe0).trans
      (mul_le_mul_of_nonneg_left hNe (le_max_right C 0))
  have h5 : C2 * (Real.sqrt N)⁻¹ ≤ |C2| * t ^ a := by
    calc C2 * (Real.sqrt N)⁻¹ ≤ |C2| * (Real.sqrt N)⁻¹ := mul_le_mul_of_nonneg_right (le_abs_self _) hsq0
      _ ≤ |C2| * 1 := mul_le_mul_of_nonneg_left hsq (abs_nonneg _)
      _ ≤ |C2| * t ^ a := mul_le_mul_of_nonneg_left hte (abs_nonneg _)
  linarith

/-- The criterion (2) read on the integer cells. -/
theorem riemannHypothesis_iff_causalMobiusThetaTail_nat_subpower :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |causalMobiusThetaTail N| ≤ C * (N : ℝ) ^ ε := by
  rw [riemannHypothesis_iff_causalMobiusThetaTail_subpower]
  constructor
  · intro h ε hε
    obtain ⟨C, hC⟩ := h ε hε
    exact ⟨C, fun N hN => hC N (by exact_mod_cast hN)⟩
  · intro h ε hε
    obtain ⟨C, hC⟩ := h ε hε
    exact exists_causalMobiusThetaTail_bound_of_nat hε.le hC

theorem natPowerBound_of_abs_sub_le {f g : ℕ → ℝ} {D a C : ℝ} (ha : 0 ≤ a)
    (hD : ∀ N : ℕ, 1 ≤ N → |f N - g N| ≤ D) (hf : ∀ N : ℕ, 1 ≤ N → |f N| ≤ C * (N : ℝ) ^ a) :
    ∀ N : ℕ, 1 ≤ N → |g N| ≤ (max C 0 + |D|) * (N : ℝ) ^ a := by
  intro N hN
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNe : 1 ≤ (N : ℝ) ^ a := Real.one_le_rpow hNR ha
  have h1 := hD N hN
  have h2 := hf N hN
  have h3 : |g N| ≤ |f N| + |f N - g N| := by
    have := abs_sub_abs_le_abs_sub (g N) (f N)
    rw [abs_sub_comm] at this
    linarith
  have h4 : C * (N : ℝ) ^ a ≤ max C 0 * (N : ℝ) ^ a :=
    mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)
  have h5 : D ≤ |D| * (N : ℝ) ^ a :=
    (le_abs_self D).trans (le_mul_of_one_le_right (abs_nonneg _) hNe)
  nlinarith

/-- **(20)** `RH ⟺ ∀ ε > 0, |⟨P_N, q_N⟩_H| = O_ε(N^ε)`. -/
theorem riemannHypothesis_iff_predictableDrift_wavelet_subpower :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |inner ℝ (DeletionResidueMartingale.predictableDrift N) (thetaWaveletVec N)| ≤
        C * (N : ℝ) ^ ε := by
  obtain ⟨D, hD0, hD⟩ := exists_abs_causalMobiusThetaTail_sub_inner_predictableDrift_le
  rw [riemannHypothesis_iff_causalMobiusThetaTail_nat_subpower]
  constructor
  · intro h ε hε
    obtain ⟨C, hC⟩ := h ε hε
    exact ⟨_, natPowerBound_of_abs_sub_le hε.le hD hC⟩
  · intro h ε hε
    obtain ⟨C, hC⟩ := h ε hε
    exact ⟨_, natPowerBound_of_abs_sub_le hε.le (fun N hN => by rw [abs_sub_comm]; exact hD N hN) hC⟩

/-- Subpower physical-source norm `E_N = O(N^ε)` is a source-only sufficient condition for RH. -/
theorem riemannHypothesis_of_physicalNorm_subpower
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ‖DeletionCoefficientTransfer.source (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N‖ ≤
        C * (N : ℝ) ^ ε) : RiemannHypothesis := by
  obtain ⟨C16, hC160, hC16⟩ := exists_abs_causalMobiusThetaTail_le_physicalNorm
  rw [riemannHypothesis_iff_causalMobiusThetaTail_nat_subpower]
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨C16 * (1 + max C 0), fun N hN => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNe : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hNR hε.le
  have h1 := hC16 N hN
  have h2 := hC N hN
  have h3 : C * (N : ℝ) ^ ε ≤ max C 0 * (N : ℝ) ^ ε :=
    mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)
  have h4 : 0 ≤ max C 0 := le_max_right C 0
  calc |causalMobiusThetaTail N| ≤ C16 * (1 + ‖DeletionCoefficientTransfer.source
        (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N‖) := h1
    _ ≤ C16 * ((N : ℝ) ^ ε + max C 0 * (N : ℝ) ^ ε) := by
        gcongr; linarith
    _ = C16 * (1 + max C 0) * (N : ℝ) ^ ε := by ring

/-- The same implication with the physical norm replaced by the predictable-drift norm. -/
theorem riemannHypothesis_of_predictableDrift_norm_subpower
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ‖DeletionResidueMartingale.predictableDrift N‖ ≤ C * (N : ℝ) ^ ε) : RiemannHypothesis := by
  obtain ⟨B, hB0, hB⟩ := exists_norm_thetaWaveletVec_le
  rw [riemannHypothesis_iff_predictableDrift_wavelet_subpower]
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨B * C, fun N hN => ?_⟩
  calc |inner ℝ (DeletionResidueMartingale.predictableDrift N) (thetaWaveletVec N)| ≤
        ‖DeletionResidueMartingale.predictableDrift N‖ * ‖thetaWaveletVec N‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ (C * (N : ℝ) ^ ε) * B := mul_le_mul (hC N hN) (hB N hN) (norm_nonneg _)
        ((norm_nonneg _).trans (hC N hN))
    _ = B * C * (N : ℝ) ^ ε := by ring

/-- At an off-line zero with horizontal displacement `β > 0`, the single coordinate
`⟨P_N, q_N⟩_H` violates every `O(N^ε)` bound with `ε < β`. -/
theorem not_predictableDrift_wavelet_bound_of_offline_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < |ρ.re - 1 / 2|) :
    ¬ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |inner ℝ (DeletionResidueMartingale.predictableDrift N) (thetaWaveletVec N)| ≤
        C * (N : ℝ) ^ ε := by
  rintro ⟨C, hC⟩
  obtain ⟨D, hD0, hD⟩ := exists_abs_causalMobiusThetaTail_sub_inner_predictableDrift_le
  have hB := natPowerBound_of_abs_sub_le hε0 (fun N hN => by rw [abs_sub_comm]; exact hD N hN) hC
  obtain ⟨C', hC'⟩ := exists_causalMobiusThetaTail_bound_of_nat hε0 hB
  rcases le_or_gt (1 / 2 : ℝ) ρ.re with hr | hr
  · rw [abs_of_nonneg (by linarith)] at hε
    exact causalMobiusThetaTail_growth_excludes_zero hε0 hC' hρ (by linarith) h1
  · rw [abs_of_neg (by linarith)] at hε
    have hz : riemannZeta (1 - ρ) = 0 := (riemannZeta_one_sub_eq_zero_iff h0 h1).2 hρ
    exact causalMobiusThetaTail_growth_excludes_zero hε0 hC' hz (by simp; linarith) (by simp; linarith)

/-- Hence the physical norm violates every `O(N^ε)` bound with `ε < β` as well. -/
theorem not_physicalNorm_bound_of_offline_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < |ρ.re - 1 / 2|) :
    ¬ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      ‖DeletionCoefficientTransfer.source (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N‖ ≤
        C * (N : ℝ) ^ ε := by
  rintro ⟨C, hC⟩
  obtain ⟨B, hB0, hB⟩ := exists_norm_thetaWaveletVec_le
  refine not_predictableDrift_wavelet_bound_of_offline_zero hρ h0 h1 hε0 hε
    ⟨B * (max C 0 + 2), fun N hN => ?_⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNe : 1 ≤ (N : ℝ) ^ ε := Real.one_le_rpow hNR hε0
  have hP : ‖DeletionResidueMartingale.predictableDrift N‖ ≤
      ‖DeletionResidueMartingale.sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N‖ +
        Real.sqrt 2 := by
    have := DeletionResidueMartingale.source_eq_martingale_add_drift N
    have hI : ‖DeletionResidueMartingale.martingalePart N‖ ≤ Real.sqrt 2 :=
      Real.le_sqrt_of_sq_le (DeletionResidueMartingale.martingalePart_sq_le_two N)
    calc ‖DeletionResidueMartingale.predictableDrift N‖ =
          ‖DeletionResidueMartingale.sourceVec (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) N -
            DeletionResidueMartingale.martingalePart N‖ := by rw [this]; abel_nf
      _ ≤ _ := (norm_sub_le _ _).trans (add_le_add le_rfl hI)
  have hs2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  rw [norm_sourceVec_moebius_eq] at hP
  have h2 := hC N hN
  have h3 : C * (N : ℝ) ^ ε ≤ max C 0 * (N : ℝ) ^ ε :=
    mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)
  calc |inner ℝ (DeletionResidueMartingale.predictableDrift N) (thetaWaveletVec N)| ≤
        ‖DeletionResidueMartingale.predictableDrift N‖ * ‖thetaWaveletVec N‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ (max C 0 * (N : ℝ) ^ ε + 2 * (N : ℝ) ^ ε) * B :=
        mul_le_mul (by linarith) (hB N hN) (norm_nonneg _) (by positivity)
    _ = B * (max C 0 + 2) * (N : ℝ) ^ ε := by ring

/-- And so does the predictable-drift norm. -/
theorem not_predictableDrift_norm_bound_of_offline_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < |ρ.re - 1 / 2|) :
    ¬ ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → ‖DeletionResidueMartingale.predictableDrift N‖ ≤ C * (N : ℝ) ^ ε := by
  rintro ⟨C, hC⟩
  obtain ⟨B, hB0, hB⟩ := exists_norm_thetaWaveletVec_le
  refine not_predictableDrift_wavelet_bound_of_offline_zero hρ h0 h1 hε0 hε ⟨B * max C 0, fun N hN => ?_⟩
  have h3 : C * (N : ℝ) ^ ε ≤ max C 0 * (N : ℝ) ^ ε :=
    mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)
  calc |inner ℝ (DeletionResidueMartingale.predictableDrift N) (thetaWaveletVec N)| ≤
        ‖DeletionResidueMartingale.predictableDrift N‖ * ‖thetaWaveletVec N‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ (max C 0 * (N : ℝ) ^ ε) * B :=
        mul_le_mul ((hC N hN).trans h3) (hB N hN) (norm_nonneg _) (by positivity)
    _ = B * max C 0 * (N : ℝ) ^ ε := by ring

end

end RHTower
