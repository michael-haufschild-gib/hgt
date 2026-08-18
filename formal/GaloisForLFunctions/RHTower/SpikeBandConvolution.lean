import GaloisForLFunctions.HTGeometry.SpikeConvolutionKernel
import GaloisForLFunctions.RHTower.GaussSpikeMass

/-!
# A harmonic kernel against a power spike, on the band

Splitting the band at half and twice the read frequency bounds the harmonic convolution of the
weight `r^{-c}` by a logarithmic multiple of `(1 + s)^{-c}`.  Below half the read frequency the
kernel is uniformly small and the weight has a convergent head; between half and twice it the weight
is comparable to `s^{-c}` and the harmonic factor contributes the logarithm; above twice it the
kernel is comparable to `1/r` and the weight to `(2s)^{-c}`.

The logarithm is not an artefact: at `r ≍ s` the summand is `≍ 1/((1 + |s − r|) s^{-c})` and the
harmonic factor really does sum to a logarithm.  It is also all that is lost, which is what the
exponent ladder of the iteration needs.
-/

open Finset

namespace RHTower

/-- **Below half the read frequency.**  The kernel is uniformly at most `1/(1 + s/2)` there and the
weight has a convergent head. -/
theorem band_low_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (N s : ℕ) (hs : 1 ≤ s) :
    (1 + (s : ℝ)) ^ c * ∑ r ∈ (Finset.Icc 1 N).filter (fun r => 2 * r ≤ s),
        1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c)
      ≤ 2 + 2 / (1 - c) := by
  classical
  have hcpos : (0 : ℝ) < 1 - c := by linarith
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hden : (0 : ℝ) < 1 + (s : ℝ) / 2 := by linarith
  -- pointwise bound on the filtered range
  have hstep : ∀ r ∈ (Finset.Icc 1 N).filter (fun r => 2 * r ≤ s),
      1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c)
        ≤ (1 / (1 + (s : ℝ) / 2)) * ((r : ℝ)) ^ (-c) := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    have hr1 : 1 ≤ r := hr.1.1
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    have hrs : 2 * (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hr.2
    have habs : |(s : ℝ) - (r : ℝ)| = (s : ℝ) - (r : ℝ) := by
      rw [abs_of_nonneg]
      linarith
    have hlow : 1 + (s : ℝ) / 2 ≤ 1 + |(s : ℝ) - (r : ℝ)| := by
      rw [habs]
      linarith
    have hrc : (0 : ℝ) < (r : ℝ) ^ c := Real.rpow_pos_of_pos hr0 _
    have hprod : (1 + (s : ℝ) / 2) * (r : ℝ) ^ c
        ≤ (1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c :=
      mul_le_mul_of_nonneg_right hlow hrc.le
    have h1 : 1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c)
        ≤ 1 / ((1 + (s : ℝ) / 2) * (r : ℝ) ^ c) := by
      refine one_div_le_one_div_of_le (by positivity) hprod
    have h2 : 1 / ((1 + (s : ℝ) / 2) * (r : ℝ) ^ c)
        = (1 / (1 + (s : ℝ) / 2)) * ((r : ℝ)) ^ (-c) := by
      rw [Real.rpow_neg hr0.le, ← one_div, one_div_mul_one_div]
    rw [← h2]
    exact h1
  -- the filtered range sits inside `Icc 1 s`
  have hsub : (Finset.Icc 1 N).filter (fun r => 2 * r ≤ s) ⊆ Finset.Icc 1 s := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    rw [Finset.mem_Icc]
    exact ⟨hr.1.1, by omega⟩
  have hhead : ∑ r ∈ (Finset.Icc 1 N).filter (fun r => 2 * r ≤ s), ((r : ℝ)) ^ (-c)
      ≤ 1 + (s : ℝ) ^ (1 - c) / (1 - c) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) (sum_rpow_neg_head_le hc0 hc1 s)
    intro r _ _
    exact Real.rpow_nonneg (by positivity) _
  have hsum : ∑ r ∈ (Finset.Icc 1 N).filter (fun r => 2 * r ≤ s),
      1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c)
      ≤ (1 / (1 + (s : ℝ) / 2)) * (1 + (s : ℝ) ^ (1 - c) / (1 - c)) := by
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hhead (by positivity)
  -- assemble
  have hs0 : (0 : ℝ) < 1 + (s : ℝ) := by linarith
  have hpc : (1 + (s : ℝ)) ^ c ≤ 1 + (s : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ 1 + (s : ℝ)) hc1.le
    simpa using this
  have hmix : (1 + (s : ℝ)) ^ c * (s : ℝ) ^ (1 - c) ≤ 1 + (s : ℝ) := by
    have h1 : (s : ℝ) ^ (1 - c) ≤ (1 + (s : ℝ)) ^ (1 - c) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have h2 : (1 + (s : ℝ)) ^ c * (1 + (s : ℝ)) ^ (1 - c) = 1 + (s : ℝ) := by
      rw [← Real.rpow_add hs0]
      norm_num
    calc (1 + (s : ℝ)) ^ c * (s : ℝ) ^ (1 - c)
        ≤ (1 + (s : ℝ)) ^ c * (1 + (s : ℝ)) ^ (1 - c) :=
          mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hs0.le _)
      _ = 1 + (s : ℝ) := h2
  have hhalf : (1 + (s : ℝ)) / 2 ≤ 1 + (s : ℝ) / 2 := by linarith
  have hfinal : (1 + (s : ℝ)) ^ c * ((1 / (1 + (s : ℝ) / 2)) * (1 + (s : ℝ) ^ (1 - c) / (1 - c)))
      ≤ 2 + 2 / (1 - c) := by
    have hnum : (1 + (s : ℝ)) ^ c * (1 + (s : ℝ) ^ (1 - c) / (1 - c))
        ≤ (1 + (s : ℝ)) * (1 + 1 / (1 - c)) := by
      have hexp : (1 + (s : ℝ)) ^ c * ((s : ℝ) ^ (1 - c) / (1 - c))
          ≤ (1 + (s : ℝ)) / (1 - c) := by
        rw [mul_div_assoc']
        exact div_le_div_of_nonneg_right hmix hcpos.le
      have hexpand : (1 + (s : ℝ)) ^ c * (1 + (s : ℝ) ^ (1 - c) / (1 - c))
          = (1 + (s : ℝ)) ^ c + (1 + (s : ℝ)) ^ c * ((s : ℝ) ^ (1 - c) / (1 - c)) := by
        ring
      rw [hexpand]
      have : (1 + (s : ℝ)) * (1 + 1 / (1 - c)) = (1 + (s : ℝ)) + (1 + (s : ℝ)) / (1 - c) := by
        field_simp
      rw [this]
      linarith [hpc, hexp]
    have hnn : (0 : ℝ) ≤ (1 + (s : ℝ)) ^ c * (1 + (s : ℝ) ^ (1 - c) / (1 - c)) := by
      have h1 : (0 : ℝ) ≤ (1 + (s : ℝ)) ^ c := Real.rpow_nonneg hs0.le _
      have h2 : (0 : ℝ) ≤ (s : ℝ) ^ (1 - c) := Real.rpow_nonneg (by positivity) _
      have : (0 : ℝ) ≤ 1 + (s : ℝ) ^ (1 - c) / (1 - c) := by positivity
      positivity
    have hdiv : (1 + (s : ℝ)) ^ c * (1 + (s : ℝ) ^ (1 - c) / (1 - c)) / (1 + (s : ℝ) / 2)
        ≤ ((1 + (s : ℝ)) * (1 + 1 / (1 - c))) / ((1 + (s : ℝ)) / 2) := by
      have hstep1 : (1 + (s : ℝ)) ^ c * (1 + (s : ℝ) ^ (1 - c) / (1 - c)) / (1 + (s : ℝ) / 2)
          ≤ (1 + (s : ℝ)) ^ c * (1 + (s : ℝ) ^ (1 - c) / (1 - c)) / ((1 + (s : ℝ)) / 2) :=
        div_le_div_of_nonneg_left hnn (by positivity) hhalf
      have hstep2 : (1 + (s : ℝ)) ^ c * (1 + (s : ℝ) ^ (1 - c) / (1 - c)) / ((1 + (s : ℝ)) / 2)
          ≤ ((1 + (s : ℝ)) * (1 + 1 / (1 - c))) / ((1 + (s : ℝ)) / 2) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      exact le_trans hstep1 hstep2
    have hval : ((1 + (s : ℝ)) * (1 + 1 / (1 - c))) / ((1 + (s : ℝ)) / 2) = 2 + 2 / (1 - c) := by
      field_simp
    calc (1 + (s : ℝ)) ^ c * ((1 / (1 + (s : ℝ) / 2)) * (1 + (s : ℝ) ^ (1 - c) / (1 - c)))
        = (1 + (s : ℝ)) ^ c * (1 + (s : ℝ) ^ (1 - c) / (1 - c)) / (1 + (s : ℝ) / 2) := by
          field_simp
      _ ≤ ((1 + (s : ℝ)) * (1 + 1 / (1 - c))) / ((1 + (s : ℝ)) / 2) := hdiv
      _ = 2 + 2 / (1 - c) := hval
  refine le_trans ?_ hfinal
  exact mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hs0.le _)

/-- **Above twice the read frequency.**  There the kernel is comparable to `1/r` and the weight to
`(2s)^{-c}`, so the whole range costs one harmonic sum. -/
theorem band_high_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (N s : ℕ) (hs : 1 ≤ s) :
    (1 + (s : ℝ)) ^ c * ∑ r ∈ (Finset.Icc 1 N).filter (fun r => 2 * s < r),
        1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c)
      ≤ 2 * (1 + Real.log (N : ℝ)) := by
  classical
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < (s : ℝ) := by linarith
  have h2s : (0 : ℝ) < 2 * (s : ℝ) := by linarith
  have hstep : ∀ r ∈ (Finset.Icc 1 N).filter (fun r => 2 * s < r),
      1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c)
        ≤ (2 * (2 * (s : ℝ)) ^ (-c)) * (1 / (r : ℝ)) := by
    intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc] at hr
    have hr1 : 1 ≤ r := hr.1.1
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    have hrs : 2 * (s : ℝ) < (r : ℝ) := by exact_mod_cast hr.2
    have habs : |(s : ℝ) - (r : ℝ)| = (r : ℝ) - (s : ℝ) := by
      rw [abs_of_nonpos (by linarith)]
      ring
    have hker : (r : ℝ) / 2 ≤ 1 + |(s : ℝ) - (r : ℝ)| := by
      rw [habs]
      linarith
    have hrc : (0 : ℝ) < (r : ℝ) ^ c := Real.rpow_pos_of_pos hr0 _
    have hweight : (r : ℝ) ^ (-c) ≤ (2 * (s : ℝ)) ^ (-c) := by
      have hle : (2 * (s : ℝ)) ^ c ≤ (r : ℝ) ^ c :=
        Real.rpow_le_rpow h2s.le hrs.le hc0.le
      rw [Real.rpow_neg h2s.le, Real.rpow_neg hr0.le, inv_le_inv₀]
      · exact hle
      · exact Real.rpow_pos_of_pos hr0 _
      · exact Real.rpow_pos_of_pos h2s _
    have hprod : ((r : ℝ) / 2) * (r : ℝ) ^ c ≤ (1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c :=
      mul_le_mul_of_nonneg_right hker hrc.le
    have h1 : 1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c)
        ≤ 1 / (((r : ℝ) / 2) * (r : ℝ) ^ c) :=
      one_div_le_one_div_of_le (by positivity) hprod
    have h2 : 1 / (((r : ℝ) / 2) * (r : ℝ) ^ c) = (2 * (r : ℝ) ^ (-c)) * (1 / (r : ℝ)) := by
      rw [Real.rpow_neg hr0.le]
      field_simp
    have h3 : (2 * (r : ℝ) ^ (-c)) * (1 / (r : ℝ))
        ≤ (2 * (2 * (s : ℝ)) ^ (-c)) * (1 / (r : ℝ)) := by
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      linarith [hweight]
    rw [h2] at h1
    exact le_trans h1 h3
  have hsub : (Finset.Icc 1 N).filter (fun r => 2 * s < r) ⊆ Finset.Icc 1 N :=
    Finset.filter_subset _ _
  have hharm : ∑ r ∈ (Finset.Icc 1 N).filter (fun r => 2 * s < r), 1 / (r : ℝ)
      ≤ 1 + Real.log (N : ℝ) := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) ?_
    · intro r _ _
      positivity
    · exact RHTower.Sieve.sum_Icc_one_div_le_one_add_log N
  have hsum : ∑ r ∈ (Finset.Icc 1 N).filter (fun r => 2 * s < r),
      1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c)
      ≤ (2 * (2 * (s : ℝ)) ^ (-c)) * (1 + Real.log (N : ℝ)) := by
    refine le_trans (Finset.sum_le_sum hstep) ?_
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left hharm ?_
    have := Real.rpow_pos_of_pos h2s (-c)
    positivity
  have hfac : (1 + (s : ℝ)) ^ c * (2 * (2 * (s : ℝ)) ^ (-c)) ≤ 2 := by
    have hle : (1 + (s : ℝ)) ^ c ≤ (2 * (s : ℝ)) ^ c :=
      Real.rpow_le_rpow (by positivity) (by linarith) hc0.le
    have hinv : (2 * (s : ℝ)) ^ (-c) = ((2 * (s : ℝ)) ^ c)⁻¹ := by
      rw [Real.rpow_neg h2s.le]
    have hpos : (0 : ℝ) < (2 * (s : ℝ)) ^ c := Real.rpow_pos_of_pos h2s _
    rw [hinv]
    have : (1 + (s : ℝ)) ^ c * (2 * ((2 * (s : ℝ)) ^ c)⁻¹)
        = 2 * ((1 + (s : ℝ)) ^ c / (2 * (s : ℝ)) ^ c) := by
      field_simp
    rw [this]
    have hdiv : (1 + (s : ℝ)) ^ c / (2 * (s : ℝ)) ^ c ≤ 1 := by
      rw [div_le_one hpos]
      exact hle
    linarith
  have hlog : (0 : ℝ) ≤ 1 + Real.log (N : ℝ) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp
    · have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have := Real.log_nonneg hN1
      linarith
  calc (1 + (s : ℝ)) ^ c * ∑ r ∈ (Finset.Icc 1 N).filter (fun r => 2 * s < r),
        1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c)
      ≤ (1 + (s : ℝ)) ^ c * ((2 * (2 * (s : ℝ)) ^ (-c)) * (1 + Real.log (N : ℝ))) := by
        refine mul_le_mul_of_nonneg_left hsum ?_
        exact Real.rpow_nonneg (by linarith) _
    _ = ((1 + (s : ℝ)) ^ c * (2 * (2 * (s : ℝ)) ^ (-c))) * (1 + Real.log (N : ℝ)) := by ring
    _ ≤ 2 * (1 + Real.log (N : ℝ)) := mul_le_mul_of_nonneg_right hfac hlog


/-- The harmonic factor over a symmetric window about the read frequency. -/
theorem sum_harmonic_window_le (s : ℕ) (hs : 1 ≤ s) :
    ∑ r ∈ Finset.Icc 1 (2 * s), 1 / (1 + |(s : ℝ) - (r : ℝ)|)
      ≤ 2 * (1 + Real.log (s : ℝ)) := by
  classical
  have hsplit : Finset.Icc 1 (2 * s) = Finset.Icc 1 s ∪ Finset.Icc (s + 1) (2 * s) := by
    ext r
    simp only [Finset.mem_Icc, Finset.mem_union]
    omega
  have hdisj : Disjoint (Finset.Icc 1 s) (Finset.Icc (s + 1) (2 * s)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    rw [Finset.mem_Icc] at ha hb
    omega
  rw [hsplit, Finset.sum_union hdisj]
  have hleft : ∑ r ∈ Finset.Icc 1 s, 1 / (1 + |(s : ℝ) - (r : ℝ)|)
      = ∑ k ∈ Finset.Icc 1 s, 1 / (k : ℝ) := by
    have hcongr : ∀ r ∈ Finset.Icc 1 s,
        1 / (1 + |(s : ℝ) - (r : ℝ)|) = 1 / (1 + ((s : ℝ) - (r : ℝ))) := by
      intro r hr
      rw [Finset.mem_Icc] at hr
      have : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hr.2
      rw [abs_of_nonneg (by linarith)]
    rw [Finset.sum_congr rfl hcongr]
    refine Finset.sum_nbij' (i := fun r => s + 1 - r) (j := fun k => s + 1 - k) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_Icc] at ha ⊢
      omega
    · intro b hb
      rw [Finset.mem_Icc] at hb ⊢
      omega
    · intro a ha
      rw [Finset.mem_Icc] at ha
      omega
    · intro b hb
      rw [Finset.mem_Icc] at hb
      omega
    · intro a ha
      rw [Finset.mem_Icc] at ha
      have hcast : ((s + 1 - a : ℕ) : ℝ) = (s : ℝ) + 1 - (a : ℝ) := by
        have : a ≤ s + 1 := by omega
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast]
      ring_nf
  have hright : ∑ r ∈ Finset.Icc (s + 1) (2 * s), 1 / (1 + |(s : ℝ) - (r : ℝ)|)
      ≤ ∑ k ∈ Finset.Icc 1 s, 1 / (k : ℝ) := by
    have hcongr : ∀ r ∈ Finset.Icc (s + 1) (2 * s),
        1 / (1 + |(s : ℝ) - (r : ℝ)|) = 1 / (1 + ((r : ℝ) - (s : ℝ))) := by
      intro r hr
      rw [Finset.mem_Icc] at hr
      have : (s : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : s ≤ r)
      rw [abs_of_nonpos (by linarith)]
      ring_nf
    rw [Finset.sum_congr rfl hcongr]
    have hbij : ∑ r ∈ Finset.Icc (s + 1) (2 * s), 1 / (1 + ((r : ℝ) - (s : ℝ)))
        = ∑ k ∈ Finset.Icc 1 s, 1 / (1 + (k : ℝ)) := by
      refine Finset.sum_nbij' (i := fun r => r - s) (j := fun k => k + s) ?_ ?_ ?_ ?_ ?_
      · intro a ha
        rw [Finset.mem_Icc] at ha ⊢
        omega
      · intro b hb
        rw [Finset.mem_Icc] at hb ⊢
        omega
      · intro a ha
        rw [Finset.mem_Icc] at ha
        omega
      · intro b hb
        rw [Finset.mem_Icc] at hb
        omega
      · intro a ha
        rw [Finset.mem_Icc] at ha
        have hcast : ((a - s : ℕ) : ℝ) = (a : ℝ) - (s : ℝ) := by
          have : s ≤ a := by omega
          push_cast [Nat.cast_sub this]
          ring
        rw [hcast]
    rw [hbij]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk.1
    exact one_div_le_one_div_of_le hk0 (by linarith)
  have hharm : ∑ k ∈ Finset.Icc 1 s, 1 / (k : ℝ) ≤ 1 + Real.log (s : ℝ) :=
    RHTower.Sieve.sum_Icc_one_div_le_one_add_log s
  rw [hleft]
  linarith [hright, hharm]


/-- **Between half and twice the read frequency.**  There the weight is comparable to `(s/2)^{-c}`
and the harmonic factor produces the logarithm.  Non-emptiness of the range forces `s < 2N`, which
turns that logarithm into one in `N`. -/
theorem band_mid_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (N s : ℕ) (hs : 1 ≤ s) :
    (1 + (s : ℝ)) ^ c * ∑ r ∈ (Finset.Icc 1 N).filter (fun r => s < 2 * r ∧ r ≤ 2 * s),
        1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c)
      ≤ 8 * (1 + Real.log (2 * (N : ℝ))) := by
  classical
  have hs1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hs0 : (0 : ℝ) < (s : ℝ) := by linarith
  have hhalf : (0 : ℝ) < (s : ℝ) / 2 := by linarith
  rcases Finset.eq_empty_or_nonempty
      ((Finset.Icc 1 N).filter (fun r => s < 2 * r ∧ r ≤ 2 * s)) with hempty | ⟨r₀, hr₀⟩
  · rw [hempty, Finset.sum_empty, mul_zero]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · norm_num
    · have hN1 : (1 : ℝ) ≤ 2 * (N : ℝ) := by
        have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      have := Real.log_nonneg hN1
      linarith
  · rw [Finset.mem_filter, Finset.mem_Icc] at hr₀
    have hsN : (s : ℝ) ≤ 2 * (N : ℝ) := by
      have : s ≤ 2 * N := by omega
      exact_mod_cast this
    have hlogle : Real.log (s : ℝ) ≤ Real.log (2 * (N : ℝ)) :=
      Real.log_le_log hs0 hsN
    have hstep : ∀ r ∈ (Finset.Icc 1 N).filter (fun r => s < 2 * r ∧ r ≤ 2 * s),
        1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c)
          ≤ ((s : ℝ) / 2) ^ (-c) * (1 / (1 + |(s : ℝ) - (r : ℝ)|)) := by
      intro r hr
      rw [Finset.mem_filter, Finset.mem_Icc] at hr
      have hr1 : 1 ≤ r := hr.1.1
      have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
      have hrs : (s : ℝ) < 2 * (r : ℝ) := by exact_mod_cast hr.2.1
      have hhr : (s : ℝ) / 2 ≤ (r : ℝ) := by linarith
      have hweight : (r : ℝ) ^ (-c) ≤ ((s : ℝ) / 2) ^ (-c) := by
        have hle : ((s : ℝ) / 2) ^ c ≤ (r : ℝ) ^ c := Real.rpow_le_rpow hhalf.le hhr hc0.le
        rw [Real.rpow_neg hhalf.le, Real.rpow_neg hr0.le, inv_le_inv₀]
        · exact hle
        · exact Real.rpow_pos_of_pos hr0 _
        · exact Real.rpow_pos_of_pos hhalf _
      have habs : (0 : ℝ) < 1 + |(s : ℝ) - (r : ℝ)| := by positivity
      have hsplit : 1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c)
          = (r : ℝ) ^ (-c) * (1 / (1 + |(s : ℝ) - (r : ℝ)|)) := by
        rw [Real.rpow_neg hr0.le]
        field_simp
      rw [hsplit]
      refine mul_le_mul_of_nonneg_right hweight (by positivity)
    have hsub : (Finset.Icc 1 N).filter (fun r => s < 2 * r ∧ r ≤ 2 * s)
        ⊆ Finset.Icc 1 (2 * s) := by
      intro r hr
      rw [Finset.mem_filter, Finset.mem_Icc] at hr
      rw [Finset.mem_Icc]
      exact ⟨hr.1.1, hr.2.2⟩
    have hwindow : ∑ r ∈ (Finset.Icc 1 N).filter (fun r => s < 2 * r ∧ r ≤ 2 * s),
        1 / (1 + |(s : ℝ) - (r : ℝ)|) ≤ 2 * (1 + Real.log (s : ℝ)) := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_) (sum_harmonic_window_le s hs)
      intro r _ _
      positivity
    have hsum : ∑ r ∈ (Finset.Icc 1 N).filter (fun r => s < 2 * r ∧ r ≤ 2 * s),
        1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c)
        ≤ ((s : ℝ) / 2) ^ (-c) * (2 * (1 + Real.log (s : ℝ))) := by
      refine le_trans (Finset.sum_le_sum hstep) ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left hwindow ?_
      exact (Real.rpow_pos_of_pos hhalf _).le
    have hfac : (1 + (s : ℝ)) ^ c * ((s : ℝ) / 2) ^ (-c) ≤ 4 := by
      have hratio : (1 + (s : ℝ)) ≤ 4 * ((s : ℝ) / 2) := by linarith
      have hle : (1 + (s : ℝ)) ^ c ≤ (4 * ((s : ℝ) / 2)) ^ c :=
        Real.rpow_le_rpow (by linarith) hratio hc0.le
      have hmul : (4 * ((s : ℝ) / 2)) ^ c = (4 : ℝ) ^ c * ((s : ℝ) / 2) ^ c :=
        Real.mul_rpow (by norm_num) hhalf.le
      have hinv : ((s : ℝ) / 2) ^ (-c) = (((s : ℝ) / 2) ^ c)⁻¹ := Real.rpow_neg hhalf.le _
      have hpos : (0 : ℝ) < ((s : ℝ) / 2) ^ c := Real.rpow_pos_of_pos hhalf _
      have h4 : (4 : ℝ) ^ c ≤ 4 := by
        have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hc1.le
        simpa using this
      rw [hinv]
      rw [mul_inv_le_iff₀ hpos]
      calc (1 + (s : ℝ)) ^ c ≤ (4 : ℝ) ^ c * ((s : ℝ) / 2) ^ c := by rw [← hmul]; exact hle
        _ ≤ 4 * ((s : ℝ) / 2) ^ c := mul_le_mul_of_nonneg_right h4 hpos.le
    have hlognn : (0 : ℝ) ≤ 1 + Real.log (s : ℝ) := by
      have := Real.log_nonneg hs1
      linarith
    calc (1 + (s : ℝ)) ^ c * ∑ r ∈ (Finset.Icc 1 N).filter (fun r => s < 2 * r ∧ r ≤ 2 * s),
          1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c)
        ≤ (1 + (s : ℝ)) ^ c * (((s : ℝ) / 2) ^ (-c) * (2 * (1 + Real.log (s : ℝ)))) := by
          refine mul_le_mul_of_nonneg_left hsum ?_
          exact Real.rpow_nonneg (by linarith) _
      _ = ((1 + (s : ℝ)) ^ c * ((s : ℝ) / 2) ^ (-c)) * (2 * (1 + Real.log (s : ℝ))) := by ring
      _ ≤ 4 * (2 * (1 + Real.log (s : ℝ))) := by
          refine mul_le_mul_of_nonneg_right hfac (by linarith)
      _ = 8 * (1 + Real.log (s : ℝ)) := by ring
      _ ≤ 8 * (1 + Real.log (2 * (N : ℝ))) := by linarith


/-- **A harmonic kernel against a power spike keeps the power and loses only a logarithm.**  This is
the estimate that makes the two-piece amplitude class stable under a harmonic convolution: the spike
exponent is unchanged and its height is multiplied by a logarithm. -/
theorem sum_harmonic_rpow_neg_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (N s : ℕ) (hs : 1 ≤ s) :
    (1 + (s : ℝ)) ^ c * ∑ r ∈ Finset.Icc 1 N,
        1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c)
      ≤ (2 + 2 / (1 - c)) + 8 * (1 + Real.log (2 * (N : ℝ)))
        + 2 * (1 + Real.log (N : ℝ)) := by
  classical
  set f : ℕ → ℝ := fun r => 1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c) with hf
  set T : Finset ℕ := Finset.Icc 1 N with hT
  have hsplit1 : ∑ r ∈ T, f r
      = ∑ r ∈ T.filter (fun r => 2 * r ≤ s), f r
        + ∑ r ∈ T.filter (fun r => ¬ (2 * r ≤ s)), f r :=
    (Finset.sum_filter_add_sum_filter_not T _ f).symm
  have hsplit2 : ∑ r ∈ T.filter (fun r => ¬ (2 * r ≤ s)), f r
      = ∑ r ∈ (T.filter (fun r => ¬ (2 * r ≤ s))).filter (fun r => r ≤ 2 * s), f r
        + ∑ r ∈ (T.filter (fun r => ¬ (2 * r ≤ s))).filter (fun r => ¬ (r ≤ 2 * s)), f r :=
    (Finset.sum_filter_add_sum_filter_not _ _ f).symm
  have hmidset : (T.filter (fun r => ¬ (2 * r ≤ s))).filter (fun r => r ≤ 2 * s)
      = T.filter (fun r => s < 2 * r ∧ r ≤ 2 * s) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun r _ => ?_
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h2⟩
  have hhighset : (T.filter (fun r => ¬ (2 * r ≤ s))).filter (fun r => ¬ (r ≤ 2 * s))
      = T.filter (fun r => 2 * s < r) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun r _ => ?_
    constructor
    · rintro ⟨h1, h2⟩
      omega
    · intro h
      exact ⟨by omega, by omega⟩
  rw [hsplit1, hsplit2, hmidset, hhighset, mul_add, mul_add]
  have h1 := band_low_le hc0 hc1 N s hs
  have h2 := band_mid_le hc0 hc1 N s hs
  have h3 := band_high_le hc0 hc1 N s hs
  linarith


/-! ### The harmonic convolution of a power spike -/

private theorem natAbs_cast_eq_abs (x : ℤ) : ((x.natAbs : ℝ)) = |(x : ℝ)| := by
  rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]

/-- **The harmonic convolution of a power spike, at an arbitrary integer read point.**  The two
sides of the read point are covered by the band split and by the weighted arithmetic-geometric
mean respectively. -/
theorem sum_harmonic_rpow_neg_le_int {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (N : ℕ) (x : ℤ) :
    ∑ r ∈ Finset.Icc 1 N, 1 / ((1 + ((x - (r : ℤ)).natAbs : ℝ)) * (r : ℝ) ^ c)
      ≤ (12 + 2 / (1 - c)) * (1 + Real.log (2 * (N : ℝ) + 2))
        / (1 + (x.natAbs : ℝ)) ^ c := by
  classical
  have hC0 : (0 : ℝ) < 2 / (1 - c) := by
    have : (0 : ℝ) < 1 - c := by linarith
    positivity
  have hL0 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ) + 2) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hden : (0 : ℝ) < (1 + (x.natAbs : ℝ)) ^ c := by
    have : (0 : ℝ) < 1 + (x.natAbs : ℝ) := by positivity
    exact Real.rpow_pos_of_pos this c
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [show Finset.Icc 1 0 = (∅ : Finset ℕ) by decide, Finset.sum_empty]
    positivity
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : Real.log (N : ℝ) ≤ Real.log (2 * (N : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2N : Real.log (2 * (N : ℝ)) ≤ Real.log (2 * (N : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  rcases le_or_gt x 0 with hx | hx
  · -- the read point is on the far side
    set m : ℕ := (-x).toNat with hm
    have hxm : (x : ℝ) = -(m : ℝ) := by
      have h : (m : ℤ) = -x := Int.toNat_of_nonneg (by omega)
      have h2 : ((m : ℤ) : ℝ) = ((-x : ℤ) : ℝ) := by rw [h]
      push_cast at h2
      linarith
    have habs : (x.natAbs : ℝ) = (m : ℝ) := by
      rw [natAbs_cast_eq_abs, hxm, abs_neg, abs_of_nonneg (by positivity)]
    have hcongr : ∀ r ∈ Finset.Icc 1 N,
        1 / ((1 + ((x - (r : ℤ)).natAbs : ℝ)) * (r : ℝ) ^ c)
          = 1 / ((1 + (m : ℝ) + (r : ℝ)) * (r : ℝ) ^ c) := by
      intro r hr
      rw [Finset.mem_Icc] at hr
      have hr0 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr.1
      rw [natAbs_cast_eq_abs]
      push_cast
      rw [hxm, abs_of_nonpos (by linarith)]
      ring_nf
    rw [Finset.sum_congr rfl hcongr]
    have hharm : ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) ≤ 1 + Real.log (N : ℝ) :=
      RHTower.Sieve.sum_Icc_one_div_le_one_add_log N
    have hmpos : (0 : ℝ) < (1 + (m : ℝ)) ^ c :=
      Real.rpow_pos_of_pos (by positivity) c
    have hkey : ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ)
        ≤ (12 + 2 / (1 - c)) * (1 + Real.log (2 * (N : ℝ) + 2)) := by
      nlinarith [hharm, hlogN, hL0, hC0]
    rw [habs]
    refine le_trans
      (GaloisForLFunctions.HTGeometry.sum_harmonic_rpow_neg_le_of_nonpos hc0 hc1 N (m := m)) ?_
    rw [le_div_iff₀ hmpos]
    have hsimp : (1 / (1 + (m : ℝ)) ^ c * ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ))
        * (1 + (m : ℝ)) ^ c = ∑ k ∈ Finset.Icc 1 N, 1 / (k : ℝ) := by
      field_simp
    rw [hsimp]
    exact hkey
  · -- the read point is inside the positive range
    set s : ℕ := x.toNat with hs
    have hxs : (x : ℝ) = (s : ℝ) := by
      have h : (s : ℤ) = x := Int.toNat_of_nonneg (by omega)
      have h2 : ((s : ℤ) : ℝ) = ((x : ℤ) : ℝ) := by rw [h]
      push_cast at h2
      linarith
    have hs1 : 1 ≤ s := by omega
    have habs : (x.natAbs : ℝ) = (s : ℝ) := by
      rw [natAbs_cast_eq_abs, hxs, abs_of_nonneg (by positivity)]
    have hcongr : ∀ r ∈ Finset.Icc 1 N,
        1 / ((1 + ((x - (r : ℤ)).natAbs : ℝ)) * (r : ℝ) ^ c)
          = 1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c) := by
      intro r _
      rw [natAbs_cast_eq_abs]
      push_cast
      rw [hxs]
    rw [Finset.sum_congr rfl hcongr, habs]
    have hband := sum_harmonic_rpow_neg_le hc0 hc1 N s hs1
    have hspos : (0 : ℝ) < (1 + (s : ℝ)) ^ c :=
      Real.rpow_pos_of_pos (by positivity) c
    rw [le_div_iff₀ hspos]
    calc (∑ r ∈ Finset.Icc 1 N, 1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c))
          * (1 + (s : ℝ)) ^ c
        = (1 + (s : ℝ)) ^ c * ∑ r ∈ Finset.Icc 1 N,
            1 / ((1 + |(s : ℝ) - (r : ℝ)|) * (r : ℝ) ^ c) := by ring
      _ ≤ 2 + 2 / (1 - c) + 8 * (1 + Real.log (2 * (N : ℝ)))
            + 2 * (1 + Real.log (N : ℝ)) := hband
      _ ≤ (12 + 2 / (1 - c)) * (1 + Real.log (2 * (N : ℝ) + 2)) := by
          nlinarith [hlogN, hlog2N, hL0, hC0]

/-- The height a harmonic kernel adds to the spike: a constant depending only on the exponent,
times a logarithm in the band width. -/
noncomputable def spikeConvConst (c : ℝ) (N : ℕ) : ℝ :=
  (12 + 2 / (1 - c)) * (1 + Real.log (2 * (N : ℝ) + 2))

theorem one_le_spikeConvConst {c : ℝ} (hc1 : c < 1) (N : ℕ) : 1 ≤ spikeConvConst c N := by
  have hC0 : (0 : ℝ) < 2 / (1 - c) := by
    have : (0 : ℝ) < 1 - c := by linarith
    positivity
  have hL0 : (0 : ℝ) ≤ Real.log (2 * (N : ℝ) + 2) := by
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  rw [spikeConvConst]
  nlinarith

theorem spikeConvConst_nonneg {c : ℝ} (hc1 : c < 1) (N : ℕ) : 0 ≤ spikeConvConst c N :=
  le_trans zero_le_one (one_le_spikeConvConst hc1 N)

/-- **The near half of the spike is read as a spike of the same exponent.** -/
theorem sum_kernel_mul_spikeProfile_pos_band_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) {n N : ℕ}
    {w : ℤ → ℝ} (hw : ∀ l : ℤ, w l ≤ K / (1 + (l.natAbs : ℝ))) (j : ℤ) :
    ∑ r ∈ Finset.Icc 1 N,
        w (j - (-(n : ℤ) + (r : ℤ))) * spikeProfile B c n (-(n : ℤ) + (r : ℤ))
      ≤ K * B * (n : ℝ) ^ c * spikeConvConst c N
        / (1 + ((((n : ℤ) + j)).natAbs : ℝ)) ^ c := by
  classical
  set σ : ℤ := (n : ℤ) + j with hσ
  have hstep : ∀ r ∈ Finset.Icc 1 N,
      w (j - (-(n : ℤ) + (r : ℤ))) * spikeProfile B c n (-(n : ℤ) + (r : ℤ))
        ≤ K * B * (n : ℝ) ^ c * (1 / ((1 + ((σ - (r : ℤ)).natAbs : ℝ)) * (r : ℝ) ^ c)) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr1 : 1 ≤ r := hr.1
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    have harg : j - (-(n : ℤ) + (r : ℤ)) = σ - (r : ℤ) := by rw [hσ]; ring
    have hk : w (j - (-(n : ℤ) + (r : ℤ))) ≤ K / (1 + ((σ - (r : ℤ)).natAbs : ℝ)) := by
      rw [harg]; exact hw _
    have hsp : spikeProfile B c n (-(n : ℤ) + (r : ℤ)) ≤ B * (n : ℝ) ^ c / (r : ℝ) ^ c := by
      refine le_trans (spikeProfile_pos_side hB hc0 n r hr1) ?_
      rw [Real.div_rpow (by positivity) hr0.le]
      ring_nf
      exact le_rfl
    have hnn : (0 : ℝ) ≤ 1 + ((σ - (r : ℤ)).natAbs : ℝ) := by positivity
    have hprod := mul_le_mul hk hsp (spikeProfile_nonneg hB n _)
      (by positivity)
    refine le_trans hprod (le_of_eq ?_)
    field_simp
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hkey := sum_harmonic_rpow_neg_le_int hc0 hc1 N σ
  have hpos : (0 : ℝ) ≤ K * B * (n : ℝ) ^ c := by positivity
  calc K * B * (n : ℝ) ^ c
        * ∑ r ∈ Finset.Icc 1 N, 1 / ((1 + ((σ - (r : ℤ)).natAbs : ℝ)) * (r : ℝ) ^ c)
      ≤ K * B * (n : ℝ) ^ c
        * (spikeConvConst c N / (1 + (σ.natAbs : ℝ)) ^ c) :=
        mul_le_mul_of_nonneg_left hkey hpos
    _ = K * B * (n : ℝ) ^ c * spikeConvConst c N / (1 + (σ.natAbs : ℝ)) ^ c := by
        rw [spikeConvConst]; ring

/-- **The far half of the spike is read as a spike of the same exponent.** -/
theorem sum_kernel_mul_spikeProfile_neg_band_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) {n N : ℕ}
    {w : ℤ → ℝ} (hw : ∀ l : ℤ, w l ≤ K / (1 + (l.natAbs : ℝ))) (j : ℤ) :
    ∑ r ∈ Finset.Icc 1 N,
        w (j - (-(n : ℤ) - (r : ℤ))) * spikeProfile B c n (-(n : ℤ) - (r : ℤ))
      ≤ K * B * (n : ℝ) ^ c * spikeConvConst c N
        / (1 + ((((n : ℤ) + j)).natAbs : ℝ)) ^ c := by
  classical
  set σ : ℤ := (n : ℤ) + j with hσ
  have hstep : ∀ r ∈ Finset.Icc 1 N,
      w (j - (-(n : ℤ) - (r : ℤ))) * spikeProfile B c n (-(n : ℤ) - (r : ℤ))
        ≤ K * B * (n : ℝ) ^ c * (1 / ((1 + (((-σ) - (r : ℤ)).natAbs : ℝ)) * (r : ℝ) ^ c)) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr1 : 1 ≤ r := hr.1
    have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    have harg : j - (-(n : ℤ) - (r : ℤ)) = -((-σ) - (r : ℤ)) := by rw [hσ]; ring
    have hk : w (j - (-(n : ℤ) - (r : ℤ))) ≤ K / (1 + (((-σ) - (r : ℤ)).natAbs : ℝ)) := by
      rw [harg]
      refine le_trans (hw _) ?_
      rw [Int.natAbs_neg]
    have hsp : spikeProfile B c n (-(n : ℤ) - (r : ℤ)) ≤ B * (n : ℝ) ^ c / (r : ℝ) ^ c := by
      refine le_trans (spikeProfile_neg_side hB hc0 n r hr1) ?_
      rw [Real.div_rpow (by positivity) hr0.le]
      ring_nf
      exact le_rfl
    have hprod := mul_le_mul hk hsp (spikeProfile_nonneg hB n _) (by positivity)
    refine le_trans hprod (le_of_eq ?_)
    field_simp
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hkey := sum_harmonic_rpow_neg_le_int hc0 hc1 N (-σ)
  have hnat : ((-σ).natAbs : ℝ) = (σ.natAbs : ℝ) := by rw [Int.natAbs_neg]
  rw [hnat] at hkey
  have hpos : (0 : ℝ) ≤ K * B * (n : ℝ) ^ c := by positivity
  calc K * B * (n : ℝ) ^ c
        * ∑ r ∈ Finset.Icc 1 N, 1 / ((1 + (((-σ) - (r : ℤ)).natAbs : ℝ)) * (r : ℝ) ^ c)
      ≤ K * B * (n : ℝ) ^ c
        * (spikeConvConst c N / (1 + (σ.natAbs : ℝ)) ^ c) :=
        mul_le_mul_of_nonneg_left hkey hpos
    _ = K * B * (n : ℝ) ^ c * spikeConvConst c N / (1 + (σ.natAbs : ℝ)) ^ c := by
        rw [spikeConvConst]; ring

/-- **The peak of the spike is read as a spike of the same exponent.** -/
theorem kernel_mul_spikeProfile_peak_band_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) {n N : ℕ}
    {w : ℤ → ℝ} (hw : ∀ l : ℤ, w l ≤ K / (1 + (l.natAbs : ℝ))) (j : ℤ) :
    w (j - (-(n : ℤ))) * spikeProfile B c n (-(n : ℤ))
      ≤ K * B * (n : ℝ) ^ c * spikeConvConst c N
        / (1 + ((((n : ℤ) + j)).natAbs : ℝ)) ^ c := by
  set σ : ℤ := (n : ℤ) + j with hσ
  have harg : j - (-(n : ℤ)) = σ := by rw [hσ]; ring
  have hbase : (1 : ℝ) ≤ 1 + (σ.natAbs : ℝ) := by
    have : (0 : ℝ) ≤ (σ.natAbs : ℝ) := Nat.cast_nonneg _
    linarith
  have hrpow : (1 + (σ.natAbs : ℝ)) ^ c ≤ 1 + (σ.natAbs : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hbase hc1.le
    simpa using this
  have hrpos : (0 : ℝ) < (1 + (σ.natAbs : ℝ)) ^ c :=
    Real.rpow_pos_of_pos (by positivity) c
  have hk : w (j - (-(n : ℤ))) ≤ K / (1 + (σ.natAbs : ℝ)) := by
    rw [harg]; exact hw _
  have hsp : spikeProfile B c n (-(n : ℤ)) ≤ B * (n : ℝ) ^ c :=
    spikeProfile_peak_le hB hc0 n
  have hprod := mul_le_mul hk hsp (spikeProfile_nonneg hB n _) (by positivity)
  refine le_trans hprod ?_
  have hCle : (1 : ℝ) ≤ spikeConvConst c N := one_le_spikeConvConst hc1 N
  have hstep : K / (1 + (σ.natAbs : ℝ)) * (B * (n : ℝ) ^ c)
      ≤ K * B * (n : ℝ) ^ c / (1 + (σ.natAbs : ℝ)) ^ c := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hrpos]
    have hmass : (0 : ℝ) ≤ K * (B * (n : ℝ) ^ c) := by positivity
    nlinarith [hrpow, hmass]
  refine le_trans hstep ?_
  rw [div_le_div_iff₀ hrpos hrpos]
  have hmass : (0 : ℝ) ≤ K * B * (n : ℝ) ^ c := by positivity
  nlinarith [mul_nonneg (mul_nonneg hmass (sub_nonneg.mpr hCle)) hrpos.le]

/-- **A harmonic kernel maps the whole spike to a spike of the same exponent, paying a
logarithm.**  The spike exponent `c` is unchanged; its height is multiplied by
`K · spikeConvConst c N`, a constant depending only on the exponent and, logarithmically, on the
band width. -/
theorem sum_kernel_mul_spikeProfile_band_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) {n N : ℕ}
    {w : ℤ → ℝ} (hw : ∀ l : ℤ, w l ≤ K / (1 + (l.natAbs : ℝ))) (j : ℤ) :
    (∑ r ∈ Finset.Icc 1 N,
        (w (j - (-(n : ℤ) + (r : ℤ))) * spikeProfile B c n (-(n : ℤ) + (r : ℤ))
          + w (j - (-(n : ℤ) - (r : ℤ))) * spikeProfile B c n (-(n : ℤ) - (r : ℤ))))
        + w (j - (-(n : ℤ))) * spikeProfile B c n (-(n : ℤ))
      ≤ 3 * K * spikeConvConst c N
        * (B * ((n : ℝ) / (1 + ((((n : ℤ) + j)).natAbs : ℝ))) ^ c) := by
  classical
  have h1 := sum_kernel_mul_spikeProfile_pos_band_le hc0 hc1 hK hB hw (n := n) (N := N) j
  have h2 := sum_kernel_mul_spikeProfile_neg_band_le hc0 hc1 hK hB hw (n := n) (N := N) j
  have h3 := kernel_mul_spikeProfile_peak_band_le hc0 hc1 hK hB hw (n := n) (N := N) j
  rw [Finset.sum_add_distrib]
  have hexp : (B * ((n : ℝ) / (1 + ((((n : ℤ) + j)).natAbs : ℝ))) ^ c)
      = B * (n : ℝ) ^ c / (1 + ((((n : ℤ) + j)).natAbs : ℝ)) ^ c := by
    rw [Real.div_rpow (by positivity) (by positivity)]
    ring
  rw [hexp]
  have hgoal : 3 * K * spikeConvConst c N * (B * (n : ℝ) ^ c
      / (1 + ((((n : ℤ) + j)).natAbs : ℝ)) ^ c)
      = 3 * (K * B * (n : ℝ) ^ c * spikeConvConst c N
        / (1 + ((((n : ℤ) + j)).natAbs : ℝ)) ^ c) := by
    ring
  rw [hgoal]
  linarith


/-! ### The two-piece output of the convolution -/

private theorem kernel_far_le {K : ℝ} (hK : 0 ≤ K) {w : ℤ → ℝ}
    (hw : ∀ l : ℤ, w l ≤ K / (1 + (l.natAbs : ℝ))) {j l : ℤ}
    (h : 2 * (l.natAbs : ℝ) ≤ (j.natAbs : ℝ)) :
    w (j - l) ≤ 2 * K / (1 + (j.natAbs : ℝ)) := by
  have htri : (j.natAbs : ℝ) ≤ (l.natAbs : ℝ) + ((j - l).natAbs : ℝ) := by
    have h : j.natAbs ≤ l.natAbs + (j - l).natAbs := by omega
    exact_mod_cast h
  have hhalf : (j.natAbs : ℝ) / 2 ≤ ((j - l).natAbs : ℝ) := by linarith
  have hpos : (0 : ℝ) < 1 + ((j - l).natAbs : ℝ) := by positivity
  have hjpos : (0 : ℝ) < 1 + (j.natAbs : ℝ) := by positivity
  refine le_trans (hw _) ?_
  rw [div_le_div_iff₀ hpos hjpos]
  nlinarith [hK, hhalf, hpos]

/-- **A read frequency far beyond the band sees the spike only through its total mass.**  Every
band frequency lies within `3n/2` of the origin, so a read frequency at distance at least `4n`
is separated from the whole spike by at least half its own distance. -/
theorem sum_kernel_mul_spikeProfile_far_le {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) {n N : ℕ} (hN : 2 * N ≤ n)
    {w : ℤ → ℝ} (hw : ∀ l : ℤ, w l ≤ K / (1 + (l.natAbs : ℝ)))
    {j : ℤ} (hj : 4 * (n : ℝ) ≤ (j.natAbs : ℝ)) :
    (∑ r ∈ Finset.Icc 1 N,
        (w (j - (-(n : ℤ) + (r : ℤ))) * spikeProfile B c n (-(n : ℤ) + (r : ℤ))
          + w (j - (-(n : ℤ) - (r : ℤ))) * spikeProfile B c n (-(n : ℤ) - (r : ℤ))))
        + w (j - (-(n : ℤ))) * spikeProfile B c n (-(n : ℤ))
      ≤ 2 * K * (B * (3 * (n : ℝ) ^ c + 2 * (n : ℝ) / (1 - c))) / (1 + (j.natAbs : ℝ)) := by
  classical
  have hNn : N ≤ n := by omega
  have hjpos : (0 : ℝ) < 1 + (j.natAbs : ℝ) := by positivity
  have hker : (0 : ℝ) ≤ 2 * K / (1 + (j.natAbs : ℝ)) := by positivity
  -- every band frequency is far from the read frequency
  have hposfar : ∀ r ∈ Finset.Icc 1 N,
      w (j - (-(n : ℤ) + (r : ℤ))) ≤ 2 * K / (1 + (j.natAbs : ℝ)) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    refine kernel_far_le hK hw ?_
    have hnat : ((-(n : ℤ) + (r : ℤ)).natAbs : ℝ) ≤ (n : ℝ) := by
      have h : (-(n : ℤ) + (r : ℤ)).natAbs ≤ n := by omega
      exact_mod_cast h
    linarith
  have hnegfar : ∀ r ∈ Finset.Icc 1 N,
      w (j - (-(n : ℤ) - (r : ℤ))) ≤ 2 * K / (1 + (j.natAbs : ℝ)) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    refine kernel_far_le hK hw ?_
    have hnat : ((-(n : ℤ) - (r : ℤ)).natAbs : ℝ) ≤ 3 * (n : ℝ) / 2 := by
      have h : (-(n : ℤ) - (r : ℤ)).natAbs * 2 ≤ 3 * n := by omega
      have h2 : ((-(n : ℤ) - (r : ℤ)).natAbs : ℝ) * 2 ≤ 3 * (n : ℝ) := by exact_mod_cast h
      linarith
    linarith
  have hpeakfar : w (j - (-(n : ℤ))) ≤ 2 * K / (1 + (j.natAbs : ℝ)) := by
    refine kernel_far_le hK hw ?_
    have hnat : ((-(n : ℤ)).natAbs : ℝ) = (n : ℝ) := by
      have h : (-(n : ℤ)).natAbs = n := by omega
      exact_mod_cast h
    linarith
  -- the spike masses
  have hposmass : ∑ r ∈ Finset.Icc 1 N, spikeProfile B c n (-(n : ℤ) + (r : ℤ))
      ≤ B * ((n : ℝ) ^ c + (n : ℝ) / (1 - c)) := by
    have h1 : ∑ r ∈ Finset.Icc 1 N, spikeProfile B c n (-(n : ℤ) + (r : ℤ))
        ≤ ∑ r ∈ Finset.Icc 1 N, B * ((n : ℝ) / (r : ℝ)) ^ c :=
      Finset.sum_le_sum fun r hr => spikeProfile_pos_side hB hc0 n r (Finset.mem_Icc.mp hr).1
    have h2 : ∑ r ∈ Finset.Icc 1 N, B * ((n : ℝ) / (r : ℝ)) ^ c
        ≤ B * ((n : ℝ) ^ c + (n : ℝ) / (1 - c)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (spike_mass_le hc0 hc1 hNn) hB
    linarith
  have hnegmass : ∑ r ∈ Finset.Icc 1 N, spikeProfile B c n (-(n : ℤ) - (r : ℤ))
      ≤ B * ((n : ℝ) ^ c + (n : ℝ) / (1 - c)) := by
    have h1 : ∑ r ∈ Finset.Icc 1 N, spikeProfile B c n (-(n : ℤ) - (r : ℤ))
        ≤ ∑ r ∈ Finset.Icc 1 N, B * ((n : ℝ) / (r : ℝ)) ^ c :=
      Finset.sum_le_sum fun r hr => spikeProfile_neg_side hB hc0 n r (Finset.mem_Icc.mp hr).1
    have h2 : ∑ r ∈ Finset.Icc 1 N, B * ((n : ℝ) / (r : ℝ)) ^ c
        ≤ B * ((n : ℝ) ^ c + (n : ℝ) / (1 - c)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (spike_mass_le hc0 hc1 hNn) hB
    linarith
  have hpeakmass : spikeProfile B c n (-(n : ℤ)) ≤ B * (n : ℝ) ^ c :=
    spikeProfile_peak_le hB hc0 n
  -- assemble
  have hbound : (∑ r ∈ Finset.Icc 1 N,
      (w (j - (-(n : ℤ) + (r : ℤ))) * spikeProfile B c n (-(n : ℤ) + (r : ℤ))
        + w (j - (-(n : ℤ) - (r : ℤ))) * spikeProfile B c n (-(n : ℤ) - (r : ℤ))))
      + w (j - (-(n : ℤ))) * spikeProfile B c n (-(n : ℤ))
      ≤ (2 * K / (1 + (j.natAbs : ℝ)))
          * ((∑ r ∈ Finset.Icc 1 N, spikeProfile B c n (-(n : ℤ) + (r : ℤ)))
            + (∑ r ∈ Finset.Icc 1 N, spikeProfile B c n (-(n : ℤ) - (r : ℤ)))
            + spikeProfile B c n (-(n : ℤ))) := by
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine add_le_add (Finset.sum_le_sum fun r hr => ?_)
      (mul_le_mul_of_nonneg_right hpeakfar (spikeProfile_nonneg hB n _))
    exact add_le_add
      (mul_le_mul_of_nonneg_right (hposfar r hr) (spikeProfile_nonneg hB n _))
      (mul_le_mul_of_nonneg_right (hnegfar r hr) (spikeProfile_nonneg hB n _))
  refine le_trans hbound ?_
  have htotal : (∑ r ∈ Finset.Icc 1 N, spikeProfile B c n (-(n : ℤ) + (r : ℤ)))
      + (∑ r ∈ Finset.Icc 1 N, spikeProfile B c n (-(n : ℤ) - (r : ℤ)))
      + spikeProfile B c n (-(n : ℤ))
      ≤ B * (3 * (n : ℝ) ^ c + 2 * (n : ℝ) / (1 - c)) := by
    have : B * ((n : ℝ) ^ c + (n : ℝ) / (1 - c)) + B * ((n : ℝ) ^ c + (n : ℝ) / (1 - c))
        + B * (n : ℝ) ^ c = B * (3 * (n : ℝ) ^ c + 2 * (n : ℝ) / (1 - c)) := by ring
    linarith
  calc (2 * K / (1 + (j.natAbs : ℝ)))
        * ((∑ r ∈ Finset.Icc 1 N, spikeProfile B c n (-(n : ℤ) + (r : ℤ)))
          + (∑ r ∈ Finset.Icc 1 N, spikeProfile B c n (-(n : ℤ) - (r : ℤ)))
          + spikeProfile B c n (-(n : ℤ)))
      ≤ (2 * K / (1 + (j.natAbs : ℝ))) * (B * (3 * (n : ℝ) ^ c + 2 * (n : ℝ) / (1 - c))) :=
        mul_le_mul_of_nonneg_left htotal hker
    _ = 2 * K * (B * (3 * (n : ℝ) ^ c + 2 * (n : ℝ) / (1 - c))) / (1 + (j.natAbs : ℝ)) := by
        ring

/-- The bulk height a harmonic kernel creates out of a spike of unit height. -/
noncomputable def spikeConvBulkConst (c : ℝ) (N : ℕ) : ℝ :=
  30 * spikeConvConst c N + 6 + 4 / (1 - c)

/-- **A harmonic kernel maps the two-piece class to the two-piece class.**  The spike is read as a
spike of the same exponent with height multiplied by `3 K · spikeConvConst c N`, plus a bulk term
of height `spikeConvBulkConst c N · K · B · n^θ` at any exponent `0 < θ ≤ 1`.  Since the spike the
class carries has height `B ≍ A n^(-θ)`, that bulk height is `≍ K A`: independent of `n`. -/
theorem sum_kernel_mul_spikeProfile_two_piece_le {c θ : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {K B : ℝ} (hK : 0 ≤ K) (hB : 0 ≤ B) {n N : ℕ}
    (hn : 1 ≤ n) (hN : 2 * N ≤ n)
    {w : ℤ → ℝ} (hw : ∀ l : ℤ, w l ≤ K / (1 + (l.natAbs : ℝ))) (j : ℤ) :
    (∑ r ∈ Finset.Icc 1 N,
        (w (j - (-(n : ℤ) + (r : ℤ))) * spikeProfile B c n (-(n : ℤ) + (r : ℤ))
          + w (j - (-(n : ℤ) - (r : ℤ))) * spikeProfile B c n (-(n : ℤ) - (r : ℤ))))
        + w (j - (-(n : ℤ))) * spikeProfile B c n (-(n : ℤ))
      ≤ spikeConvBulkConst c N * K * B * (n : ℝ) ^ θ / (1 + (j.natAbs : ℝ)) ^ θ
        + spikeProfile (3 * K * spikeConvConst c N * B) c n j := by
  classical
  set u : ℝ := 1 + (j.natAbs : ℝ) with hudef
  have hu1 : (1 : ℝ) ≤ u := by
    have : (0 : ℝ) ≤ (j.natAbs : ℝ) := Nat.cast_nonneg _
    rw [hudef]; linarith
  have hupos : (0 : ℝ) < u := by linarith
  have huθ : (0 : ℝ) < u ^ θ := Real.rpow_pos_of_pos hupos θ
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hnθ : (0 : ℝ) < (n : ℝ) ^ θ := Real.rpow_pos_of_pos hnpos θ
  have hC1 : (1 : ℝ) ≤ spikeConvConst c N := one_le_spikeConvConst hc1 N
  have hcinv : (0 : ℝ) < 4 / (1 - c) := by
    have : (0 : ℝ) < 1 - c := by linarith
    positivity
  have hCb : 30 * spikeConvConst c N ≤ spikeConvBulkConst c N := by
    rw [spikeConvBulkConst]; linarith
  have hCbpos : (0 : ℝ) ≤ spikeConvBulkConst c N := by
    rw [spikeConvBulkConst]; nlinarith
  have hband := sum_kernel_mul_spikeProfile_band_le hc0 hc1 hK hB hw (n := n) (N := N) j
  by_cases hin : 2 * ((((n : ℤ) + j).natAbs : ℝ)) < (n : ℝ)
  · -- inside the band: the output is a spike of the same exponent
    have hsp : spikeProfile (3 * K * spikeConvConst c N * B) c n j
        = 3 * K * spikeConvConst c N * (B * ((n : ℝ) / (1 + ((((n : ℤ) + j)).natAbs : ℝ))) ^ c) := by
      rw [spikeProfile, if_pos hin]; ring
    have hbulk : (0 : ℝ) ≤ spikeConvBulkConst c N * K * B * (n : ℝ) ^ θ / u ^ θ := by
      positivity
    rw [hsp]
    linarith
  · -- outside the band: the output is bulk
    have hsp0 : spikeProfile (3 * K * spikeConvConst c N * B) c n j = 0 := by
      rw [spikeProfile, if_neg hin]
    rw [hsp0, add_zero]
    have hout : (n : ℝ) ≤ 2 * ((((n : ℤ) + j).natAbs : ℝ)) := by
      exact le_of_not_gt hin
    rcases le_or_gt (4 * (n : ℝ)) ((j.natAbs : ℝ)) with hjfar | hjnear
    · -- far beyond the band: the spike is seen only through its total mass
      refine le_trans (sum_kernel_mul_spikeProfile_far_le hc0 hc1 hK hB hN hw hjfar) ?_
      have hnc : (n : ℝ) ^ c ≤ (n : ℝ) := by
        have := Real.rpow_le_rpow_of_exponent_le hn1 hc1.le
        simpa using this
      have hun : (n : ℝ) ≤ u := by rw [hudef]; linarith
      have hsplit : u = u ^ θ * u ^ (1 - θ) := by
        rw [← Real.rpow_add hupos]; norm_num
      have hlow : (n : ℝ) ≤ (n : ℝ) ^ θ * u ^ (1 - θ) := by
        have h1 : (n : ℝ) ^ (1 - θ) ≤ u ^ (1 - θ) :=
          Real.rpow_le_rpow hnpos.le hun (by linarith)
        have h2 : (n : ℝ) ^ θ * (n : ℝ) ^ (1 - θ) = (n : ℝ) := by
          rw [← Real.rpow_add hnpos]; norm_num
        nlinarith [hnθ, h1, h2]
      have hnum : 2 * K * (B * (3 * (n : ℝ) ^ c + 2 * (n : ℝ) / (1 - c)))
          ≤ spikeConvBulkConst c N * K * B * ((n : ℝ) ^ θ * u ^ (1 - θ)) := by
        have hmass : 3 * (n : ℝ) ^ c + 2 * (n : ℝ) / (1 - c) ≤ (3 + 2 / (1 - c)) * (n : ℝ) := by
          have : (0 : ℝ) < 1 - c := by linarith
          rw [add_mul]
          have h2 : 2 * (n : ℝ) / (1 - c) = 2 / (1 - c) * (n : ℝ) := by ring
          rw [h2]
          linarith
        have hKB : (0 : ℝ) ≤ K * B := mul_nonneg hK hB
        have hCb2 : 2 * (3 + 2 / (1 - c)) ≤ spikeConvBulkConst c N := by
          have hdiv : 4 / (1 - c) = 2 * (2 / (1 - c)) := by ring
          rw [spikeConvBulkConst, hdiv]
          nlinarith [hC1]
        calc 2 * K * (B * (3 * (n : ℝ) ^ c + 2 * (n : ℝ) / (1 - c)))
            = (K * B) * (2 * (3 * (n : ℝ) ^ c + 2 * (n : ℝ) / (1 - c))) := by ring
          _ ≤ (K * B) * (2 * ((3 + 2 / (1 - c)) * (n : ℝ))) := by
              refine mul_le_mul_of_nonneg_left ?_ hKB
              linarith
          _ = (K * B) * ((2 * (3 + 2 / (1 - c))) * (n : ℝ)) := by ring
          _ ≤ (K * B) * (spikeConvBulkConst c N * (n : ℝ)) := by
              refine mul_le_mul_of_nonneg_left ?_ hKB
              exact mul_le_mul_of_nonneg_right hCb2 hnpos.le
          _ ≤ (K * B) * (spikeConvBulkConst c N * ((n : ℝ) ^ θ * u ^ (1 - θ))) := by
              refine mul_le_mul_of_nonneg_left ?_ hKB
              exact mul_le_mul_of_nonneg_left hlow hCbpos
          _ = spikeConvBulkConst c N * K * B * ((n : ℝ) ^ θ * u ^ (1 - θ)) := by ring
      rw [div_le_div_iff₀ hupos huθ]
      calc 2 * K * (B * (3 * (n : ℝ) ^ c + 2 * (n : ℝ) / (1 - c))) * u ^ θ
          ≤ spikeConvBulkConst c N * K * B * ((n : ℝ) ^ θ * u ^ (1 - θ)) * u ^ θ :=
            mul_le_mul_of_nonneg_right hnum huθ.le
        _ = spikeConvBulkConst c N * K * B * (n : ℝ) ^ θ * (u ^ θ * u ^ (1 - θ)) := by ring
        _ = spikeConvBulkConst c N * K * B * (n : ℝ) ^ θ * u := by rw [← hsplit]
    · -- outside the band but within reach: the band estimate is already bounded
      have hbase : (n : ℝ) / (1 + ((((n : ℤ) + j)).natAbs : ℝ)) ≤ 2 := by
        have hd : (0 : ℝ) < 1 + ((((n : ℤ) + j)).natAbs : ℝ) := by positivity
        rw [div_le_iff₀ hd]
        linarith
      have hpow : ((n : ℝ) / (1 + ((((n : ℤ) + j)).natAbs : ℝ))) ^ c ≤ 2 := by
        have h1 : ((n : ℝ) / (1 + ((((n : ℤ) + j)).natAbs : ℝ))) ^ c ≤ (2 : ℝ) ^ c :=
          Real.rpow_le_rpow (by positivity) hbase hc0.le
        have h2 : (2 : ℝ) ^ c ≤ 2 := by
          have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hc1.le
          simpa using this
        linarith
      have hbandval : (∑ r ∈ Finset.Icc 1 N,
          (w (j - (-(n : ℤ) + (r : ℤ))) * spikeProfile B c n (-(n : ℤ) + (r : ℤ))
            + w (j - (-(n : ℤ) - (r : ℤ))) * spikeProfile B c n (-(n : ℤ) - (r : ℤ))))
          + w (j - (-(n : ℤ))) * spikeProfile B c n (-(n : ℤ))
          ≤ 6 * K * spikeConvConst c N * B := by
        refine le_trans hband ?_
        have hKC : (0 : ℝ) ≤ 3 * K * spikeConvConst c N := by nlinarith [hK, hC1]
        have hspike : B * ((n : ℝ) / (1 + ((((n : ℤ) + j)).natAbs : ℝ))) ^ c ≤ B * 2 :=
          mul_le_mul_of_nonneg_left hpow hB
        calc 3 * K * spikeConvConst c N
              * (B * ((n : ℝ) / (1 + ((((n : ℤ) + j)).natAbs : ℝ))) ^ c)
            ≤ 3 * K * spikeConvConst c N * (B * 2) := mul_le_mul_of_nonneg_left hspike hKC
          _ = 6 * K * spikeConvConst c N * B := by ring
      refine le_trans hbandval ?_
      have huθle : u ^ θ ≤ 5 * (n : ℝ) ^ θ := by
        have h5 : u ≤ 5 * (n : ℝ) := by rw [hudef]; linarith
        have h1 : u ^ θ ≤ (5 * (n : ℝ)) ^ θ := Real.rpow_le_rpow hupos.le h5 hθ0.le
        have h2 : (5 * (n : ℝ)) ^ θ = (5 : ℝ) ^ θ * (n : ℝ) ^ θ :=
          Real.mul_rpow (by norm_num) hnpos.le
        have h3 : (5 : ℝ) ^ θ ≤ 5 := by
          have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 5) hθ1
          simpa using this
        nlinarith [hnθ, h1, h2, h3]
      rw [le_div_iff₀ huθ]
      have hKB : (0 : ℝ) ≤ K * B := mul_nonneg hK hB
      have hstep : 6 * K * spikeConvConst c N * B * u ^ θ
          ≤ 6 * K * spikeConvConst c N * B * (5 * (n : ℝ) ^ θ) := by
        refine mul_le_mul_of_nonneg_left huθle ?_
        nlinarith [hKB, hC1]
      refine le_trans hstep ?_
      have : 6 * K * spikeConvConst c N * B * (5 * (n : ℝ) ^ θ)
          = 30 * spikeConvConst c N * (K * B) * (n : ℝ) ^ θ := by ring
      rw [this]
      have hfin : 30 * spikeConvConst c N * (K * B) ≤ spikeConvBulkConst c N * K * B := by
        have h := mul_le_mul_of_nonneg_right hCb hKB
        calc 30 * spikeConvConst c N * (K * B) ≤ spikeConvBulkConst c N * (K * B) := h
          _ = spikeConvBulkConst c N * K * B := by ring
      exact mul_le_mul_of_nonneg_right hfin hnθ.le


/-! ### The class is stable under a harmonic convolution -/

/-- A symmetric integer interval splits into its centre and the pairs at each distance. -/
theorem sum_Icc_symm_split {M : Type*} [AddCommMonoid M] (a : ℤ) (f : ℤ → M) :
    ∀ N : ℕ, ∑ l ∈ Finset.Icc (a - (N : ℤ)) (a + (N : ℤ)), f l
      = f a + ∑ r ∈ Finset.Icc 1 N, (f (a + (r : ℤ)) + f (a - (r : ℤ))) := by
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
    have hset : Finset.Icc (a - ((N + 1 : ℕ) : ℤ)) (a + ((N + 1 : ℕ) : ℤ))
        = insert (a - ((N + 1 : ℕ) : ℤ))
            (insert (a + ((N + 1 : ℕ) : ℤ)) (Finset.Icc (a - (N : ℤ)) (a + (N : ℤ)))) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      push_cast
      omega
    have hnot1 : a + ((N + 1 : ℕ) : ℤ) ∉ Finset.Icc (a - (N : ℤ)) (a + (N : ℤ)) := by
      simp only [Finset.mem_Icc]
      push_cast
      omega
    have hnot2 : a - ((N + 1 : ℕ) : ℤ)
        ∉ insert (a + ((N + 1 : ℕ) : ℤ)) (Finset.Icc (a - (N : ℤ)) (a + (N : ℤ))) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]
      push_cast
      omega
    have hIcc : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hset, Finset.sum_insert hnot2, Finset.sum_insert hnot1, ih, hIcc,
      Finset.sum_insert (by simp)]
    push_cast
    abel

/-- The radius of the band carrying the spike. -/
def bandRadius (n : ℕ) : ℕ := (n - 1) / 2

theorem two_mul_bandRadius_le (n : ℕ) : 2 * bandRadius n ≤ n := by
  rw [bandRadius]; omega

theorem spikeProfile_eq_zero_of_notMem {B c : ℝ} {n : ℕ} {l : ℤ}
    (h : l ∉ Finset.Icc (-(n : ℤ) - (bandRadius n : ℤ)) (-(n : ℤ) + (bandRadius n : ℤ))) :
    spikeProfile B c n l = 0 := by
  rw [Finset.mem_Icc] at h
  rw [bandRadius] at h
  have hnat : n ≤ 2 * (((n : ℤ) + l).natAbs) := by omega
  have hcast : (n : ℝ) ≤ 2 * ((((n : ℤ) + l).natAbs : ℝ)) := by exact_mod_cast hnat
  rw [spikeProfile, if_neg (not_lt.mpr hcast)]

/-- **The two-piece amplitude class is stable under a harmonic convolution.**  The bulk part is
transferred at any exponent below `θ`; the spike part is transferred as a spike of the same
exponent `c`, with a height multiplied by a logarithm, together with a bulk term of height
`spikeConvBulkConst · K · B · n^γ`. -/
theorem tsum_harmonic_two_piece_le {A θ γ c B K : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hθ1 : θ ≤ 1) (hγ0 : 0 < γ) (hγθ : γ < θ)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hB : 0 ≤ B) {n : ℕ} (hn : 1 ≤ n)
    {g : ℤ → ℂ} (hg : TwoPieceAmplitude A θ B c n g) (j : ℤ) :
    ∑' l : ℤ, K / (1 + ((l - j).natAbs : ℝ)) * ‖g l‖
      ≤ (K * A * (2 ^ γ * (2 * (∑' x : ℤ,
            GaloisForLFunctions.intPowWeight (θ + 1 - γ) x).toReal))
          + spikeConvBulkConst c (bandRadius n) * K * B * (n : ℝ) ^ γ)
          / (1 + (j.natAbs : ℝ)) ^ γ
        + spikeProfile (3 * K * spikeConvConst c (bandRadius n) * B) c n j := by
  classical
  have hθ0 : (0 : ℝ) < θ := lt_trans hγ0 hγθ
  set N : ℕ := bandRadius n with hNdef
  set ker : ℤ → ℝ := fun l => K / (1 + ((l - j).natAbs : ℝ)) with hkerdef
  set w : ℤ → ℝ := fun x => K / (1 + ((x.natAbs) : ℝ)) with hwdef
  have hkerw : ∀ l : ℤ, ker l = w (j - l) := by
    intro l
    have : (l - j).natAbs = (j - l).natAbs := by omega
    rw [hkerdef, hwdef]
    simp only
    rw [this]
  have hkernn : ∀ l : ℤ, 0 ≤ ker l := by
    intro l; rw [hkerdef]; positivity
  set bulk : ℤ → ℝ := fun l => ker l * (A / (1 + (l.natAbs : ℝ)) ^ θ) with hbulkdef
  set spk : ℤ → ℝ := fun l => ker l * spikeProfile B c n l with hspkdef
  -- the pointwise split
  have hle : ∀ l : ℤ, ker l * ‖g l‖ ≤ bulk l + spk l := by
    intro l
    have := mul_le_mul_of_nonneg_left (hg l) (hkernn l)
    rw [mul_add] at this
    exact this
  -- summability of the bulk piece
  have hbulkform : ∀ l : ℤ, bulk l
      = K * A * (1 / ((1 + |(l : ℝ)|) ^ θ * (1 + |((j - l : ℤ) : ℝ)|))) := by
    intro l
    have hsym : (l - j).natAbs = (j - l).natAbs := by omega
    rw [hbulkdef, hkerdef]
    simp only
    rw [hsym, natAbs_cast_eq_abs, natAbs_cast_eq_abs]
    have h1 : (0 : ℝ) < 1 + |((j - l : ℤ) : ℝ)| := by
      have := abs_nonneg (((j - l : ℤ) : ℝ)); linarith
    have h2 : (0 : ℝ) < (1 + |(l : ℝ)|) ^ θ := by
      have := abs_nonneg ((l : ℝ))
      exact Real.rpow_pos_of_pos (by linarith) θ
    field_simp
  have hbulksum : Summable bulk := by
    refine Summable.congr ((GaloisForLFunctions.summable_harmonicPowConv j hθ0).mul_left (K * A))
      fun l => ?_
    rw [hbulkform l]
  -- summability of the spike piece
  have hspksupp : ∀ l : ℤ,
      l ∉ Finset.Icc (-(n : ℤ) - (N : ℤ)) (-(n : ℤ) + (N : ℤ)) → spk l = 0 := by
    intro l hl
    rw [hspkdef]
    simp only
    rw [spikeProfile_eq_zero_of_notMem (B := B) (c := c) (n := n) (l := l) hl, mul_zero]
  have hspksum : Summable spk := summable_of_ne_finset_zero hspksupp
  have hallsum : Summable (fun l : ℤ => ker l * ‖g l‖) := by
    refine Summable.of_nonneg_of_le (fun l => mul_nonneg (hkernn l) (norm_nonneg _)) hle
      (hbulksum.add hspksum)
  -- the tsum split
  have hsplit : ∑' l : ℤ, ker l * ‖g l‖ ≤ (∑' l : ℤ, bulk l) + ∑' l : ℤ, spk l := by
    rw [← Summable.tsum_add hbulksum hspksum]
    exact hallsum.tsum_le_tsum hle (hbulksum.add hspksum)
  -- the bulk half
  have hbulkbound : (∑' l : ℤ, bulk l)
      ≤ K * A * (2 ^ γ * (2 * (∑' x : ℤ,
          GaloisForLFunctions.intPowWeight (θ + 1 - γ) x).toReal))
        / (1 + (j.natAbs : ℝ)) ^ γ := by
    rw [tsum_congr hbulkform, tsum_mul_left]
    have hconv := GaloisForLFunctions.tsum_harmonicPowConv_real_le j hθ1 hγ0 hγθ
    have hKA : (0 : ℝ) ≤ K * A := mul_nonneg hK hA
    have := mul_le_mul_of_nonneg_left hconv hKA
    rw [natAbs_cast_eq_abs j]
    calc K * A * ∑' l : ℤ, 1 / ((1 + |(l : ℝ)|) ^ θ * (1 + |((j - l : ℤ) : ℝ)|))
        ≤ K * A * (2 ^ γ * (2 * (∑' x : ℤ,
            GaloisForLFunctions.intPowWeight (θ + 1 - γ) x).toReal)
              / (1 + |(j : ℝ)|) ^ γ) := this
      _ = K * A * (2 ^ γ * (2 * (∑' x : ℤ,
            GaloisForLFunctions.intPowWeight (θ + 1 - γ) x).toReal))
              / (1 + |(j : ℝ)|) ^ γ := by ring
  -- the spike half
  have hspkbound : (∑' l : ℤ, spk l)
      ≤ spikeConvBulkConst c N * K * B * (n : ℝ) ^ γ / (1 + (j.natAbs : ℝ)) ^ γ
        + spikeProfile (3 * K * spikeConvConst c N * B) c n j := by
    rw [tsum_eq_sum hspksupp]
    have hcongr : ∀ l ∈ Finset.Icc (-(n : ℤ) - (N : ℤ)) (-(n : ℤ) + (N : ℤ)),
        spk l = w (j - l) * spikeProfile B c n l := by
      intro l _
      rw [hspkdef]
      simp only
      rw [hkerw l]
    rw [Finset.sum_congr rfl hcongr]
    have hsplitsum := sum_Icc_symm_split (-(n : ℤ))
      (fun l => w (j - l) * spikeProfile B c n l) N
    rw [hsplitsum]
    have hmain := sum_kernel_mul_spikeProfile_two_piece_le (c := c) (θ := γ) hc0 hc1 hγ0
      (le_of_lt (lt_of_lt_of_le hγθ hθ1)) hK hB hn (two_mul_bandRadius_le n)
      (w := w) (fun l => le_rfl) j
    rw [← hNdef] at hmain
    linarith
  -- assemble
  have hdiv : (K * A * (2 ^ γ * (2 * (∑' x : ℤ,
        GaloisForLFunctions.intPowWeight (θ + 1 - γ) x).toReal))
        + spikeConvBulkConst c N * K * B * (n : ℝ) ^ γ) / (1 + (j.natAbs : ℝ)) ^ γ
      = K * A * (2 ^ γ * (2 * (∑' x : ℤ,
          GaloisForLFunctions.intPowWeight (θ + 1 - γ) x).toReal))
          / (1 + (j.natAbs : ℝ)) ^ γ
        + spikeConvBulkConst c N * K * B * (n : ℝ) ^ γ / (1 + (j.natAbs : ℝ)) ^ γ := by
    ring
  rw [hdiv]
  linarith


end RHTower
