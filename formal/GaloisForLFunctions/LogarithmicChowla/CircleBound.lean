import GaloisForLFunctions.LogarithmicChowla.CircleMethod

/-!
# The circle bound

If the prime kernel `K_k(β)` is at most `η` whenever `β` is farther than `W/2^k` from every
fraction `a/q` with `q ≤ Q₀`, and `4TW ≤ 2^k`, then

`|avg_{p∈𝐏_k} c(ph)| ≤ η + 4 Σ_{1 ≤ s ≤ hQ₀} Σ_{b<s} V(b/s, T)` (`abs_avg_corr_le`).

* The Fejér densities have mean one (`sum_fejer_div`), so the minor residues cost `η`
  (`abs_sum_fejer_mul_le`).
* A major residue `r`, with `|hr/R − a/q| ≤ W/2^k`, has `r/R` within `W/2^k ≤ 1/(4T)` of
  `a/(qh) ≡ b/s` modulo `1`, `s = qh`, `b = a mod s` (`mem_arc_of_near`); a union bound over the
  arcs (`sum_major_le`) and the arc masses give
  `4V(b/s,T)(M+1)/M + 8T/M` per arc. Letting `M → ∞` leaves the bound.
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Complex Filter Topology

noncomputable section

variable {U : Ultrafilter ℝ}

/-- The Fejér densities have mean one. -/
theorem sum_fejer_div (hU : (U : Filter ℝ) ≤ atTop) {M R : ℕ} (hM : 0 < M) (hMR : M ≤ R) :
    (∑ r ∈ range R, fejer U M R r) / R = 1 := by
  have hR0 : 0 < R := lt_of_lt_of_le hM hMR
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR0
  have hMM : (0 : ℝ) < M := by exact_mod_cast hM
  have hpt : ∀ n, n ≠ 0 → ∑ r ∈ range R, Complex.normSq (lamSum n M (r / R)) = R * M := by
    intro n hn
    simp only [lamSum_eq_sum]
    rw [sum_normSq_eq hR0 hMR]
    congr 1
    have : ∀ s ∈ range M, Complex.normSq ((lam (n + s) : ℝ) : ℂ) = 1 := by
      intro s _
      rw [Complex.normSq_ofReal]
      rcases lam_eq_one_or (show n + s ≠ 0 by omega) with h | h <;> rw [h] <;> norm_num
    rw [sum_congr rfl this]
    simp
  have hL : limAvg U (fun n => ∑ r ∈ range R, Complex.normSq (lamSum n M (r / R))) = R * M := by
    rw [limAvg_congr_pos (g := fun _ => (R : ℝ) * M) hpt, limAvg_const hU]
  simp only [fejer, ← sum_div]
  rw [← limAvg_sum hU _ fun r _ => bdd_normSq_lamSum M _, hL]
  field_simp

/-- **Minor residues.** If `|K_k(hr/R)| ≤ η` off `𝔐`, then
`|R⁻¹ Σ_r F(r) Re K_k(hr/R)| ≤ η + R⁻¹ Σ_{r ∈ 𝔐} F(r)`. -/
theorem abs_sum_fejer_mul_le (hU : (U : Filter ℝ) ≤ atTop) {h k M R : ℕ} (hM : 0 < M)
    (hMR : M ≤ R) (𝔐 : Finset ℕ) [DecidablePred (· ∈ 𝔐)] {η : ℝ} (hη : 0 ≤ η)
    (hminor : ∀ r ∈ range R, r ∉ 𝔐 → ‖primeKernel k (h * r / R)‖ ≤ η) :
    |(∑ r ∈ range R, fejer U M R r * (primeKernel k (h * r / R)).re) / R|
      ≤ η + (∑ r ∈ (range R).filter (· ∈ 𝔐), fejer U M R r) / R := by
  have hRR : (0 : ℝ) < R := by exact_mod_cast lt_of_lt_of_le hM hMR
  have hF := fejer_nonneg hU M R
  rw [abs_div, abs_of_pos hRR, div_le_iff₀ hRR, add_mul, div_mul_cancel₀ _ hRR.ne']
  have hmean := sum_fejer_div hU hM hMR
  rw [div_eq_one_iff_eq hRR.ne'] at hmean
  calc |∑ r ∈ range R, fejer U M R r * (primeKernel k (h * r / R)).re|
      ≤ ∑ r ∈ range R, fejer U M R r * |(primeKernel k (h * r / R)).re| := by
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun r _ => ?_))
        rw [abs_mul, abs_of_nonneg (hF r)]
    _ = ∑ r ∈ (range R).filter (· ∈ 𝔐), fejer U M R r * |(primeKernel k (h * r / R)).re|
        + ∑ r ∈ (range R).filter (· ∉ 𝔐), fejer U M R r * |(primeKernel k (h * r / R)).re| :=
        (sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ ∑ r ∈ (range R).filter (· ∈ 𝔐), fejer U M R r * 1
        + ∑ r ∈ (range R).filter (· ∉ 𝔐), fejer U M R r * η := by
        refine add_le_add (sum_le_sum fun r _ => ?_) (sum_le_sum fun r hr => ?_)
        · exact mul_le_mul_of_nonneg_left
            ((Complex.abs_re_le_norm _).trans (norm_primeKernel_le k _)) (hF r)
        · obtain ⟨hr1, hr2⟩ := mem_filter.mp hr
          exact mul_le_mul_of_nonneg_left
            ((Complex.abs_re_le_norm _).trans (hminor r hr1 hr2)) (hF r)
    _ ≤ ∑ r ∈ (range R).filter (· ∈ 𝔐), fejer U M R r + η * R := by
        simp only [mul_one]
        refine add_le_add le_rfl ?_
        rw [← sum_mul, mul_comm, ← hmean]
        refine mul_le_mul_of_nonneg_left ?_ hη
        exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun r _ _ => hF r
    _ = η * R + ∑ r ∈ (range R).filter (· ∈ 𝔐), fejer U M R r := add_comm _ _

/-- A residue near `a/q` after dilation by `h` lies on the arc of some `b/s`, `s = qh`. -/
theorem mem_arc_of_near {R T h q r : ℕ} (hr : r < R) (hh : 0 < h) (hq : 0 < q) {a : ℤ} {w : ℝ}
    (hw : w ≤ 1 / (4 * T)) (hnear : |(h : ℝ) * r / R - a / q| ≤ w) :
    ∃ b ∈ range (q * h), r ∈ arcSet R T (b / (q * h : ℕ)) := by
  set s : ℕ := q * h with hs
  have hs0 : 0 < s := Nat.mul_pos hq hh
  have hsZ : (0 : ℤ) < s := by exact_mod_cast hs0
  refine ⟨(a % s).toNat, ?_, ?_⟩
  · rw [mem_range]
    have h1 := Int.emod_lt_of_pos a hsZ
    have h2 := Int.emod_nonneg a hsZ.ne'
    omega
  · rw [mem_arcSet]
    refine ⟨hr, a / s, ?_⟩
    have hb : (((a % s).toNat : ℕ) : ℝ) = ((a % s : ℤ) : ℝ) := by
      rw [show (((a % s).toNat : ℕ) : ℝ) = (((a % s).toNat : ℤ) : ℝ) by push_cast; rfl,
        Int.toNat_of_nonneg (Int.emod_nonneg a hsZ.ne')]
    have hdecomp : (a : ℝ) = s * ((a / s : ℤ) : ℝ) + ((a % s : ℤ) : ℝ) := by
      have := Int.mul_ediv_add_emod a s
      exact_mod_cast this.symm
    have hhR : (0 : ℝ) < h := by exact_mod_cast hh
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hsR : (s : ℝ) = q * h := by rw [hs]; push_cast; ring
    have key : (r : ℝ) / R - (((a % s).toNat : ℕ) : ℝ) / s - ((a / s : ℤ) : ℝ)
        = ((h : ℝ) * r / R - a / q) / h := by
      rw [hb, hsR]
      have : ((a % s : ℤ) : ℝ) = a - s * ((a / s : ℤ) : ℝ) := by linarith
      rw [this, hsR]
      field_simp
      ring
    rw [key, abs_div, abs_of_pos hhR, div_le_iff₀ hhR]
    calc |(h : ℝ) * r / R - a / q| ≤ w := hnear
      _ ≤ 1 / (4 * T) := hw
      _ ≤ 1 / (4 * T) * h := le_mul_of_one_le_right (by positivity) (by exact_mod_cast hh)

/-- **The major residues.** A residue near some `a/q`, `q ≤ Q₀`, after dilation by `h` costs at
most the arcs of the fractions `b/s`, `s ≤ hQ₀`. -/
theorem sum_major_le (hU : (U : Filter ℝ) ≤ atTop) {h Q₀ T M R : ℕ} (hh : 0 < h) {w : ℝ}
    (hw : w ≤ 1 / (4 * T)) (𝔐 : Finset ℕ) [DecidablePred (· ∈ 𝔐)]
    (hmajor : ∀ r ∈ (range R).filter (· ∈ 𝔐),
      ∃ q ∈ Icc 1 Q₀, ∃ a : ℤ, |(h : ℝ) * r / R - a / q| ≤ w) :
    ∑ r ∈ (range R).filter (· ∈ 𝔐), fejer U M R r
      ≤ ∑ s ∈ Icc 1 (h * Q₀), ∑ b ∈ range s, ∑ r ∈ arcSet R T (b / s), fejer U M R r := by
  classical
  have hF := fejer_nonneg hU M R
  have hpt : ∀ r ∈ (range R).filter (· ∈ 𝔐), fejer U M R r
      ≤ ∑ s ∈ Icc 1 (h * Q₀), ∑ b ∈ range s,
          (if r ∈ arcSet R T (b / s) then fejer U M R r else 0) := by
    intro r hr
    obtain ⟨q, hq, a, ha⟩ := hmajor r hr
    obtain ⟨hq1, hq2⟩ := mem_Icc.mp hq
    have hrR : r < R := mem_range.mp (mem_filter.mp hr).1
    obtain ⟨b, hb, hmem⟩ := mem_arc_of_near hrR hh hq1 hw ha
    have hs : q * h ∈ Icc 1 (h * Q₀) := by
      rw [mem_Icc]
      constructor
      · exact Nat.mul_pos hq1 hh
      · rw [mul_comm]
        exact Nat.mul_le_mul_left h hq2
    have hinner : fejer U M R r ≤ ∑ b ∈ range (q * h),
        (if r ∈ arcSet R T (b / (q * h : ℕ)) then fejer U M R r else 0) := by
      have := single_le_sum (f := fun b : ℕ =>
          if r ∈ arcSet R T (b / (q * h : ℕ)) then fejer U M R r else 0)
        (fun b _ => by split_ifs <;> simp [hF r]) hb
      exact (le_of_eq (if_pos hmem).symm).trans this
    refine hinner.trans ?_
    exact single_le_sum (f := fun s : ℕ => ∑ b ∈ range s,
        (if r ∈ arcSet R T (b / s) then fejer U M R r else 0))
      (fun s _ => sum_nonneg fun b _ => by split_ifs <;> simp [hF r]) hs
  calc ∑ r ∈ (range R).filter (· ∈ 𝔐), fejer U M R r
      ≤ ∑ r ∈ (range R).filter (· ∈ 𝔐), ∑ s ∈ Icc 1 (h * Q₀), ∑ b ∈ range s,
          (if r ∈ arcSet R T (b / s) then fejer U M R r else 0) := sum_le_sum hpt
    _ = ∑ s ∈ Icc 1 (h * Q₀), ∑ b ∈ range s, ∑ r ∈ (range R).filter (· ∈ 𝔐),
          (if r ∈ arcSet R T (b / s) then fejer U M R r else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun s _ => ?_
        rw [sum_comm]
    _ ≤ ∑ s ∈ Icc 1 (h * Q₀), ∑ b ∈ range s, ∑ r ∈ arcSet R T (b / s), fejer U M R r := by
        refine sum_le_sum fun s _ => sum_le_sum fun b _ => ?_
        rw [← sum_filter]
        refine sum_le_sum_of_subset_of_nonneg (fun r hr => (mem_filter.mp hr).2)
          fun r _ _ => hF r

/-- The residues `r < R` with `hr/R` within `W/2^k` of some `a/q`, `q ≤ Q₀`. -/
def majorSet (R h Q₀ k : ℕ) (W : ℝ) : Finset ℕ := by
  classical
  exact (range R).filter fun r => ∃ q ∈ Icc 1 Q₀, ∃ a : ℤ, |(h : ℝ) * r / R - a / q| ≤ W / 2 ^ k

theorem mem_majorSet {R h Q₀ k r : ℕ} {W : ℝ} :
    r ∈ majorSet R h Q₀ k W ↔
      r < R ∧ ∃ q ∈ Icc 1 Q₀, ∃ a : ℤ, |(h : ℝ) * r / R - a / q| ≤ W / 2 ^ k := by
  classical
  simp [majorSet]

theorem tendsto_arc_term (v t : ℝ) :
    Tendsto (fun M : ℕ => 4 * v * ((M : ℝ) + 1) / M + 8 * t / M) atTop (𝓝 (4 * v)) := by
  have h0 := tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hlim : Tendsto (fun M : ℕ => 4 * v * (1 + 1 / (M : ℝ)) + 8 * t * (1 / (M : ℝ))) atTop
      (𝓝 (4 * v)) := by
    have := ((h0.const_add 1).const_mul (4 * v)).add (h0.const_mul (8 * t))
    simpa using this
  refine hlim.congr' ((eventually_gt_atTop 0).mono fun M hM => ?_)
  have : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp

/-- **The circle bound.** -/
theorem abs_avg_corr_le (hU : (U : Filter ℝ) ≤ atTop) (h k Q₀ T : ℕ) (hh : 0 < h) (hT : 0 < T)
    {η W : ℝ} (hη : 0 ≤ η) (hTW : 4 * T * W ≤ 2 ^ k)
    (hK : ∀ β : ℝ, (∀ q ∈ Icc 1 Q₀, ∀ a : ℤ, W / 2 ^ k < |β - a / q|) →
      ‖primeKernel k β‖ ≤ η) :
    |(∑ p : primesAt k, corr U ((p : ℕ) * h)) / (primesAt k).card|
      ≤ η + 4 * ∑ s ∈ Icc 1 (h * Q₀), ∑ b ∈ range s, twistVar U (b / s) T := by
  have hw : W / 2 ^ k ≤ 1 / (4 * T) := by
    have hTR : (0 : ℝ) < T := by exact_mod_cast hT
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  set G : ℕ → ℝ := fun M => η + ∑ s ∈ Icc 1 (h * Q₀), ∑ b ∈ range s,
      (4 * twistVar U (b / s) T * ((M : ℝ) + 1) / M + 8 * T / M) + 2 ^ (k + 1) * h / M with hG
  -- the bound at a window length `M`
  have hbound : ∀ M : ℕ, 0 < M →
      |(∑ p : primesAt k, corr U ((p : ℕ) * h)) / (primesAt k).card| ≤ G M := by
    intro M hM
    set R := M + 2 ^ (k + 1) * h + T with hR
    have hMR : M ≤ R := by omega
    set 𝔐 : Finset ℕ := majorSet R h Q₀ k W with h𝔐
    have hminor : ∀ r ∈ range R, r ∉ 𝔐 → ‖primeKernel k (h * r / R)‖ ≤ η := by
      intro r hr hr𝔐
      refine hK _ fun q hq a => ?_
      by_contra hle
      push Not at hle
      exact hr𝔐 (mem_majorSet.mpr ⟨mem_range.mp hr, q, hq, a, hle⟩)
    have hmajor : ∀ r ∈ (range R).filter (· ∈ 𝔐),
        ∃ q ∈ Icc 1 Q₀, ∃ a : ℤ, |(h : ℝ) * r / R - a / q| ≤ W / 2 ^ k := fun r hr =>
      (mem_majorSet.mp (mem_filter.mp hr).2).2
    have h1 := abs_avg_corr_sub_le hU h k M R hM (by omega)
    have h2 := abs_sum_fejer_mul_le hU hM hMR 𝔐 hη hminor
    have h3 := sum_major_le hU (T := T) (M := M) hh hw 𝔐 hmajor
    have h4 : ∀ s ∈ Icc 1 (h * Q₀), ∀ b ∈ range s,
        (∑ r ∈ arcSet R T (b / s), fejer U M R r) / R
          ≤ 4 * twistVar U (b / s) T * (M + 1) / M + 8 * T / M := by
      intro s _ b _
      have := arc_mass_le hU M T R hM hT (by omega) (b / s)
      simpa only [fejer, sum_div] using this
    have hRR : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
    have h5 : (∑ r ∈ (range R).filter (· ∈ 𝔐), fejer U M R r) / R
        ≤ ∑ s ∈ Icc 1 (h * Q₀), ∑ b ∈ range s,
            (4 * twistVar U (b / s) T * (M + 1) / M + 8 * T / M) := by
      calc (∑ r ∈ (range R).filter (· ∈ 𝔐), fejer U M R r) / R
          ≤ (∑ s ∈ Icc 1 (h * Q₀), ∑ b ∈ range s, ∑ r ∈ arcSet R T (b / s), fejer U M R r) / R :=
            div_le_div_of_nonneg_right h3 hRR.le
        _ = ∑ s ∈ Icc 1 (h * Q₀), ∑ b ∈ range s,
              (∑ r ∈ arcSet R T (b / s), fejer U M R r) / R := by
            rw [sum_div]
            refine sum_congr rfl fun s _ => ?_
            rw [sum_div]
        _ ≤ _ := sum_le_sum fun s hs => sum_le_sum fun b hb => h4 s hs b hb
    have := abs_sub_abs_le_abs_sub
      ((∑ p : primesAt k, corr U ((p : ℕ) * h)) / (primesAt k).card)
      ((∑ r ∈ range R, fejer U M R r * (primeKernel k (h * r / R)).re) / R)
    simp only [hG]
    linarith
  -- let `M → ∞`
  have hlim : Tendsto G atTop
      (𝓝 (η + ∑ s ∈ Icc 1 (h * Q₀), ∑ b ∈ range s, 4 * twistVar U (b / s) T + 0)) := by
    have h0 := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((2 : ℝ) ^ (k + 1) * h)
    rw [mul_zero] at h0
    have hsum := tendsto_finsetSum (Icc 1 (h * Q₀)) fun s _ =>
      tendsto_finsetSum (range s) fun b _ => tendsto_arc_term (twistVar U (b / s) T) T
    refine ((hsum.const_add η).add h0).congr fun M => ?_
    simp only [hG]
    rw [mul_one_div]
  have hle := ge_of_tendsto hlim ((eventually_gt_atTop 0).mono fun M hM => hbound M hM)
  rw [add_zero] at hle
  simpa only [mul_sum] using hle

end

end GaloisForLFunctions.LogarithmicChowla
