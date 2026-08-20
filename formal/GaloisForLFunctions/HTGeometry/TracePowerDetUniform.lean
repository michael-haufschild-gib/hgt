/-
# The regularized determinant converges uniformly on discs

The geometric majorant of the regularized exponent is uniform in the spectral variable on any disc
strictly inside the reciprocal rate, so the tail of the series is small uniformly there and the
finitely many remaining terms converge one by one.  The exponent therefore converges *uniformly* on
the disc, and since it stays uniformly bounded, so does the determinant: this is the compact-open
continuity of `det_p` in the power traces, which is the topology the determinant-completion law is
stated in.

Main results:
* `norm_tracePowerDetExp_sub_le` — the head/tail split of the exponent difference.
* `tendstoUniformlyOn_tracePowerDetExp` — **the exponent converges uniformly on discs**.
* `tendstoUniformlyOn_tracePowerDet`, `tendstoLocallyUniformlyOn_tracePowerDet` —
  **the determinant converges uniformly on discs**.
-/
import GaloisForLFunctions.HTGeometry.TracePowerDeterminant

open Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Estimate

variable {p : ℕ} {τ σ : ℕ → ℂ} {B S ρ : ℝ}

theorem norm_tracePowerDetTerm_le_rpow (hp : 0 < p) {z : ℂ} (hzρ : ‖z‖ ≤ ρ) (hρ0 : 0 ≤ ρ)
    (k : ℕ) :
    ‖z ^ (k + p) / ((k + p : ℕ) : ℂ) * τ (k + p) - z ^ (k + p) / ((k + p : ℕ) : ℂ) * σ (k + p)‖
      ≤ ρ ^ (k + p) * ‖τ (k + p) - σ (k + p)‖ := by
  rw [← mul_sub, norm_mul, norm_div, norm_pow]
  refine mul_le_mul ?_ le_rfl (norm_nonneg _) (by positivity)
  have hden : (1 : ℝ) ≤ ‖((k + p : ℕ) : ℂ)‖ := one_le_norm_natCast_add hp k
  have hnum : ‖z‖ ^ (k + p) ≤ ρ ^ (k + p) := pow_le_pow_left₀ (norm_nonneg z) hzρ _
  calc ‖z‖ ^ (k + p) / ‖((k + p : ℕ) : ℂ)‖ ≤ ‖z‖ ^ (k + p) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [pow_nonneg (norm_nonneg z) (k + p)]
    _ ≤ ρ ^ (k + p) := hnum

theorem summable_diffMajorant (hB1 : 1 ≤ B)
    (hτ : ∀ k, ‖τ (k + p)‖ ≤ S * B ^ k) (hσ : ∀ k, ‖σ (k + p)‖ ≤ S * B ^ k)
    (hρ0 : 0 ≤ ρ) (hρB : ρ * B < 1) :
    Summable fun k : ℕ => ρ ^ (k + p) * ‖τ (k + p) - σ (k + p)‖ := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hρB0 : 0 ≤ ρ * B := mul_nonneg hρ0 hB0
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geometric_of_lt_one hρB0 hρB).mul_left (2 * S * ρ ^ p))
  have hdiff : ‖τ (k + p) - σ (k + p)‖ ≤ 2 * S * B ^ k := by
    have := norm_sub_le (τ (k + p)) (σ (k + p))
    have h1 := hτ k
    have h2 := hσ k
    linarith
  calc ρ ^ (k + p) * ‖τ (k + p) - σ (k + p)‖ ≤ ρ ^ (k + p) * (2 * S * B ^ k) :=
        mul_le_mul_of_nonneg_left hdiff (by positivity)
    _ = 2 * S * ρ ^ p * (ρ * B) ^ k := by rw [pow_add, mul_pow]; ring

/-- **The head/tail split of the exponent difference.** -/
theorem norm_tracePowerDetExp_sub_le (hp : 0 < p) (hB1 : 1 ≤ B)
    (hτ : ∀ k, ‖τ (k + p)‖ ≤ S * B ^ k) (hσ : ∀ k, ‖σ (k + p)‖ ≤ S * B ^ k)
    {z : ℂ} (hzρ : ‖z‖ ≤ ρ) (hρ0 : 0 ≤ ρ) (hρB : ρ * B < 1) (K : ℕ) :
    ‖tracePowerDetExp p τ z - tracePowerDetExp p σ z‖
      ≤ (∑ k ∈ Finset.range K, ρ ^ (k + p) * ‖τ (k + p) - σ (k + p)‖)
        + 2 * S * ρ ^ p * ((ρ * B) ^ K / (1 - ρ * B)) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hρB0 : 0 ≤ ρ * B := mul_nonneg hρ0 hB0
  have hzB : ‖z‖ * B < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hzρ hB0) hρB
  have hsτ := summable_tracePowerDetExp hp hB1 hτ hzB
  have hsσ := summable_tracePowerDetExp hp hB1 hσ hzB
  have hmaj := summable_diffMajorant hB1 hτ hσ hρ0 hρB
  have hsub : tracePowerDetExp p τ z - tracePowerDetExp p σ z
      = ∑' k : ℕ, (z ^ (k + p) / ((k + p : ℕ) : ℂ) * τ (k + p)
        - z ^ (k + p) / ((k + p : ℕ) : ℂ) * σ (k + p)) := (hsτ.tsum_sub hsσ).symm
  have hnormsum : Summable fun k : ℕ =>
      ‖z ^ (k + p) / ((k + p : ℕ) : ℂ) * τ (k + p)
        - z ^ (k + p) / ((k + p : ℕ) : ℂ) * σ (k + p)‖ :=
    hmaj.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => norm_tracePowerDetTerm_le_rpow hp hzρ hρ0 k)
  have hnormle : ‖tracePowerDetExp p τ z - tracePowerDetExp p σ z‖
      ≤ ∑' k : ℕ, ρ ^ (k + p) * ‖τ (k + p) - σ (k + p)‖ := by
    rw [hsub]
    exact (norm_tsum_le_tsum_norm hnormsum).trans
      (hnormsum.tsum_le_tsum (fun k => norm_tracePowerDetTerm_le_rpow hp hzρ hρ0 k) hmaj)
  refine hnormle.trans ?_
  have hsplit := hmaj.sum_add_tsum_nat_add K
  have htail : (∑' j : ℕ, ρ ^ (j + K + p) * ‖τ (j + K + p) - σ (j + K + p)‖)
      ≤ 2 * S * ρ ^ p * ((ρ * B) ^ K / (1 - ρ * B)) := by
    have hshift : Summable fun j : ℕ => ρ ^ (j + K + p) * ‖τ (j + K + p) - σ (j + K + p)‖ :=
      (summable_nat_add_iff (f := fun k : ℕ => ρ ^ (k + p) * ‖τ (k + p) - σ (k + p)‖) K).mpr hmaj
    have hgeom : Summable fun j : ℕ => 2 * S * ρ ^ p * (ρ * B) ^ K * (ρ * B) ^ j :=
      (summable_geometric_of_lt_one hρB0 hρB).mul_left _
    have hle : ∀ j : ℕ, ρ ^ (j + K + p) * ‖τ (j + K + p) - σ (j + K + p)‖
        ≤ 2 * S * ρ ^ p * (ρ * B) ^ K * (ρ * B) ^ j := by
      intro j
      have hdiff : ‖τ (j + K + p) - σ (j + K + p)‖ ≤ 2 * S * B ^ (j + K) := by
        have h0 := norm_sub_le (τ (j + K + p)) (σ (j + K + p))
        have h1 := hτ (j + K)
        have h2 := hσ (j + K)
        linarith
      calc ρ ^ (j + K + p) * ‖τ (j + K + p) - σ (j + K + p)‖
          ≤ ρ ^ (j + K + p) * (2 * S * B ^ (j + K)) :=
            mul_le_mul_of_nonneg_left hdiff (by positivity)
        _ = 2 * S * ρ ^ p * (ρ * B) ^ K * (ρ * B) ^ j := by
            rw [show j + K + p = p + (K + j) by ring, pow_add, pow_add,
              show j + K = K + j by ring, pow_add, mul_pow, mul_pow]
            ring
    refine (hshift.tsum_le_tsum hle hgeom).trans (le_of_eq ?_)
    rw [tsum_mul_left, tsum_geometric_of_lt_one hρB0 hρB]
    field_simp
  have hheadnn : (0 : ℝ) ≤ ∑ k ∈ Finset.range K, ρ ^ (k + p) * ‖τ (k + p) - σ (k + p)‖ :=
    Finset.sum_nonneg fun k _ => by positivity
  linarith [hsplit, htail]

/-- The regularized exponent is uniformly bounded on the disc. -/
theorem norm_tracePowerDetExp_le (hp : 0 < p) (hB1 : 1 ≤ B)
    (hσ : ∀ k, ‖σ (k + p)‖ ≤ S * B ^ k) {z : ℂ} (hzρ : ‖z‖ ≤ ρ) (hρ0 : 0 ≤ ρ)
    (hρB : ρ * B < 1) :
    ‖tracePowerDetExp p σ z‖ ≤ S * ρ ^ p / (1 - ρ * B) := by
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hρB0 : 0 ≤ ρ * B := mul_nonneg hρ0 hB0
  have hzB : ‖z‖ * B < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_right hzρ hB0) hρB
  have hsum := summable_tracePowerDetExp hp hB1 hσ hzB
  have hS0 : (0 : ℝ) ≤ S := by
    have h := hσ 0
    have h2 : (0 : ℝ) ≤ ‖σ (0 + p)‖ := norm_nonneg _
    simpa using le_trans h2 h
  have hgeom : Summable fun k : ℕ => S * ρ ^ p * (ρ * B) ^ k :=
    (summable_geometric_of_lt_one hρB0 hρB).mul_left _
  have hle : ∀ k : ℕ, ‖z ^ (k + p) / ((k + p : ℕ) : ℂ) * σ (k + p)‖
      ≤ S * ρ ^ p * (ρ * B) ^ k := by
    intro k
    refine (norm_tracePowerDetTerm_le hp hσ z k).trans ?_
    have h1 : ‖z‖ ^ p ≤ ρ ^ p := pow_le_pow_left₀ (norm_nonneg z) hzρ p
    have h2 : (‖z‖ * B) ^ k ≤ (ρ * B) ^ k :=
      pow_le_pow_left₀ (mul_nonneg (norm_nonneg z) hB0)
        (mul_le_mul_of_nonneg_right hzρ hB0) k
    have h3 : (0 : ℝ) ≤ (‖z‖ * B) ^ k := pow_nonneg (mul_nonneg (norm_nonneg z) hB0) k
    have h4 : (0 : ℝ) ≤ S * ρ ^ p := mul_nonneg hS0 (pow_nonneg hρ0 p)
    calc S * ‖z‖ ^ p * (‖z‖ * B) ^ k ≤ S * ρ ^ p * (‖z‖ * B) ^ k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hS0) h3
      _ ≤ S * ρ ^ p * (ρ * B) ^ k := mul_le_mul_of_nonneg_left h2 h4
  have hnormsum : Summable fun k : ℕ => ‖z ^ (k + p) / ((k + p : ℕ) : ℂ) * σ (k + p)‖ :=
    hgeom.of_nonneg_of_le (fun k => norm_nonneg _) hle
  refine (norm_tsum_le_tsum_norm hnormsum).trans ?_
  refine (hnormsum.tsum_le_tsum hle hgeom).trans (le_of_eq ?_)
  rw [tsum_mul_left, tsum_geometric_of_lt_one hρB0 hρB]
  field_simp

end Estimate

section Uniform

variable {p : ℕ} {L : Type*} {l : Filter L} {τ : L → ℕ → ℂ} {σ : ℕ → ℂ} {B S ρ : ℝ}

/-- **The regularized exponent converges uniformly on discs.** -/
theorem tendstoUniformlyOn_tracePowerDetExp (hp : 0 < p) (hB1 : 1 ≤ B)
    (hbound : ∀ (a : L) (k : ℕ), ‖τ a (k + p)‖ ≤ S * B ^ k)
    (hboundσ : ∀ k, ‖σ (k + p)‖ ≤ S * B ^ k)
    (hconv : ∀ k : ℕ, Tendsto (fun a => τ a (k + p)) l (nhds (σ (k + p))))
    (hρ0 : 0 ≤ ρ) (hρB : ρ * B < 1) :
    TendstoUniformlyOn (fun a z => tracePowerDetExp p (τ a) z) (tracePowerDetExp p σ) l
      (closedBall (0 : ℂ) ρ) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hB0 : (0 : ℝ) ≤ B := le_trans zero_le_one hB1
  have hρB0 : 0 ≤ ρ * B := mul_nonneg hρ0 hB0
  have htail0 : Tendsto (fun K : ℕ => 2 * S * ρ ^ p * ((ρ * B) ^ K / (1 - ρ * B)))
      atTop (nhds 0) := by
    have hgeo : Tendsto (fun K : ℕ => (ρ * B) ^ K) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hρB0 hρB
    have h := ((hgeo.div_const (1 - ρ * B)).const_mul (2 * S * ρ ^ p))
    simpa using h
  obtain ⟨K, hK⟩ := (htail0.eventually_lt_const (by linarith : (0 : ℝ) < ε / 2)).exists
  have hhead : Tendsto (fun a => ∑ k ∈ Finset.range K,
      ρ ^ (k + p) * ‖τ a (k + p) - σ (k + p)‖) l (nhds 0) := by
    have hterms : ∀ k ∈ Finset.range K,
        Tendsto (fun a => ρ ^ (k + p) * ‖τ a (k + p) - σ (k + p)‖) l (nhds 0) := by
      intro k _
      have h1 : Tendsto (fun a => τ a (k + p) - σ (k + p)) l (nhds 0) := by
        simpa using (hconv k).sub (tendsto_const_nhds (x := σ (k + p)))
      have h2 : Tendsto (fun a => ‖τ a (k + p) - σ (k + p)‖) l (nhds 0) := by
        simpa using h1.norm
      simpa using h2.const_mul (ρ ^ (k + p))
    have h := tendsto_finsetSum (Finset.range K) hterms
    simpa using h
  filter_upwards [hhead.eventually_lt_const (by linarith : (0 : ℝ) < ε / 2)] with a ha z hz
  rw [dist_eq_norm, ← norm_neg, neg_sub]
  have hzρ : ‖z‖ ≤ ρ := by simpa using mem_closedBall_zero_iff.mp hz
  have hsplit := norm_tracePowerDetExp_sub_le hp hB1 (hbound a) hboundσ hzρ hρ0 hρB K
  linarith [hsplit, ha, hK]

/-- **The regularized determinant converges uniformly on discs.**  This is the compact-open
continuity of `det_p` in the power traces. -/
theorem tendstoUniformlyOn_tracePowerDet (hp : 0 < p) (hB1 : 1 ≤ B)
    (hbound : ∀ (a : L) (k : ℕ), ‖τ a (k + p)‖ ≤ S * B ^ k)
    (hboundσ : ∀ k, ‖σ (k + p)‖ ≤ S * B ^ k)
    (hconv : ∀ k : ℕ, Tendsto (fun a => τ a (k + p)) l (nhds (σ (k + p))))
    (hρ0 : 0 ≤ ρ) (hρB : ρ * B < 1) :
    TendstoUniformlyOn (fun a z => tracePowerDet p (τ a) z) (tracePowerDet p σ) l
      (closedBall (0 : ℂ) ρ) := by
  have hM : ∀ z ∈ closedBall (0 : ℂ) ρ, ‖tracePowerDetExp p σ z‖ ≤ S * ρ ^ p / (1 - ρ * B) := by
    intro z hz
    exact norm_tracePowerDetExp_le hp hB1 hboundσ (by simpa using mem_closedBall_zero_iff.mp hz)
      hρ0 hρB
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = S * ρ ^ p / (1 - ρ * B) := ⟨_, rfl⟩
  have hexpM : (0 : ℝ) < Real.exp M := Real.exp_pos M
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min 1 (ε / (4 * Real.exp M)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact lt_min one_pos (by positivity)
  have huni := (Metric.tendstoUniformlyOn_iff.mp
    (tendstoUniformlyOn_tracePowerDetExp hp hB1 hbound hboundσ hconv hρ0 hρB)) δ hδ0
  filter_upwards [huni] with a ha z hz
  have hw : ‖tracePowerDetExp p σ z - tracePowerDetExp p (τ a) z‖ < δ := by
    have := ha z hz
    rwa [dist_eq_norm] at this
  have hwle1 : ‖tracePowerDetExp p σ z - tracePowerDetExp p (τ a) z‖ ≤ 1 := by
    have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
    linarith
  have hfac : tracePowerDet p σ z - tracePowerDet p (τ a) z
      = tracePowerDet p σ z
        * (1 - Complex.exp (tracePowerDetExp p σ z - tracePowerDetExp p (τ a) z)) := by
    have hexp : -tracePowerDetExp p σ z
        + (tracePowerDetExp p σ z - tracePowerDetExp p (τ a) z)
        = -tracePowerDetExp p (τ a) z := by ring
    rw [tracePowerDet, tracePowerDet, mul_sub, mul_one, ← Complex.exp_add, hexp]
  have hdetnorm : ‖tracePowerDet p σ z‖ ≤ Real.exp M := by
    rw [tracePowerDet, Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have h1 : (-tracePowerDetExp p σ z).re ≤ ‖-tracePowerDetExp p σ z‖ :=
      Complex.re_le_norm _
    have h2 : ‖-tracePowerDetExp p σ z‖ = ‖tracePowerDetExp p σ z‖ := norm_neg _
    have h3 := hM z hz
    rw [← hMdef] at h3
    linarith [h1, h2.le, h2.ge]
  have hexpsub : ‖1 - Complex.exp (tracePowerDetExp p σ z - tracePowerDetExp p (τ a) z)‖
      ≤ 2 * δ := by
    rw [← norm_neg, neg_sub]
    refine le_trans (Complex.norm_exp_sub_one_le hwle1) ?_
    linarith
  have hfinal : dist (tracePowerDet p σ z) (tracePowerDet p (τ a) z) ≤ Real.exp M * (2 * δ) := by
    rw [dist_eq_norm, hfac, norm_mul]
    exact mul_le_mul hdetnorm hexpsub (norm_nonneg _) (le_of_lt hexpM)
  have hδle : Real.exp M * (2 * δ) ≤ ε / 2 := by
    have hδ2 : δ ≤ ε / (4 * Real.exp M) := by rw [hδdef]; exact min_le_right _ _
    have : Real.exp M * (2 * δ) ≤ Real.exp M * (2 * (ε / (4 * Real.exp M))) := by
      nlinarith [hexpM, hδ2]
    calc Real.exp M * (2 * δ) ≤ Real.exp M * (2 * (ε / (4 * Real.exp M))) := this
      _ = ε / 2 := by field_simp; ring
  linarith [hfinal, hδle]

end Uniform

end

end GaloisForLFunctions.HTGeometry
