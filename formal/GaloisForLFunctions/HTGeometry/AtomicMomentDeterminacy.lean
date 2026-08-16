import Mathlib

/-!
# Summable atomic data is determined by its power moments

A countable family of nonzero atoms `z j` with absolutely summable weights `c j`, accumulating only
at the origin, is determined by the moments `Σ_j c_j z_j^n`.  This is the moment determinacy the
shifted reciprocal tower needs: the all-order tower is faithful to the reciprocal divisor.

The proof is **elementary** — no polynomial-density theorem is used.  Normalize by an atom `z_{j₀}`
of maximal modulus among those carrying nonzero weight; every normalized atom then lies in the
closed unit disc, and `z_{j₀}` is the unique one equal to `1`.  Averaging the vanishing moments over
`n < N` and letting `N → ∞`, Tannery's theorem exchanges the limit with the sum: each normalized
atom other than `1` has vanishing Cesàro mean, and the surviving term is exactly `c_{j₀}`.  Hence
`c_{j₀} = 0`, contradicting the choice.

## Main results

* `norm_geomSum_le_of_norm_le_one`, `tendsto_geomSum_cesaro_of_norm_le_one` — the Cesàro means of a
  non-unit geometric progression in the closed unit disc vanish;
* `coeff_eq_zero_of_atomicMoments_vanish` — the determinacy theorem;
* `atomicData_eq_of_moments_eq` — its difference form: equal moments force equal weights;
* `atomicData_withCenter_eq_of_moments_eq` — the same with one extra atom at the accumulation point.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open Filter Topology
open scoped BigOperators

/-! ### Cesàro means of geometric progressions in the closed unit disc -/

theorem norm_geomSum_le_of_norm_le_one {w : ℂ} (hw : ‖w‖ ≤ 1) (hne : w ≠ 1) (K : ℕ) :
    ‖∑ m ∈ Finset.range K, w ^ m‖ ≤ 2 / ‖1 - w‖ := by
  have hsub : w - 1 ≠ 0 := sub_ne_zero.mpr hne
  rw [geom_sum_eq hne, norm_div]
  have hnum : ‖w ^ K - 1‖ ≤ 2 := by
    calc ‖w ^ K - 1‖ ≤ ‖w ^ K‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
          gcongr
          · rw [norm_pow]
            exact pow_le_one₀ (norm_nonneg w) hw
          · rw [norm_one]
      _ = 2 := by norm_num
  have hden : ‖w - 1‖ = ‖1 - w‖ := by
    rw [← norm_neg]
    ring_nf
  rw [hden]
  have hpos : 0 < ‖1 - w‖ := by
    rw [← hden]
    exact norm_pos_iff.mpr hsub
  gcongr

theorem norm_geomSum_le_card {w : ℂ} (hw : ‖w‖ ≤ 1) (K : ℕ) :
    ‖∑ m ∈ Finset.range K, w ^ m‖ ≤ (K : ℝ) := by
  calc ‖∑ m ∈ Finset.range K, w ^ m‖ ≤ ∑ m ∈ Finset.range K, ‖w ^ m‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.range K, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg w) hw
    _ = (K : ℝ) := by simp

/-- **Vanishing Cesàro mean.**  A geometric progression in the closed unit disc with ratio different
from `1` has vanishing discrete Cesàro mean. -/
theorem tendsto_geomSum_cesaro_of_norm_le_one {w : ℂ} (hw : ‖w‖ ≤ 1) (hne : w ≠ 1) :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹ : ℂ) * ∑ m ∈ Finset.range N, w ^ m) atTop (𝓝 0) := by
  refine squeeze_zero_norm' (a := fun N : ℕ => (2 / ‖1 - w‖) / (N : ℝ)) ?_ ?_
  · refine Eventually.of_forall fun N => ?_
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg N)]
    calc (N : ℝ)⁻¹ * ‖∑ m ∈ Finset.range N, w ^ m‖
        ≤ (N : ℝ)⁻¹ * (2 / ‖1 - w‖) :=
          mul_le_mul_of_nonneg_left (norm_geomSum_le_of_norm_le_one hw hne N)
            (inv_nonneg.mpr (Nat.cast_nonneg N))
      _ = (2 / ‖1 - w‖) / (N : ℝ) := by ring
  · simpa [div_eq_mul_inv, mul_comm] using
      (tendsto_const_div_atTop_nhds_zero_nat (2 / ‖1 - w‖))

/-- The Cesàro mean of the constant progression is `1`. -/
theorem tendsto_geomSum_cesaro_one :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹ : ℂ) * ∑ _m ∈ Finset.range N, (1 : ℂ) ^ _m)
      atTop (𝓝 1) := by
  have hfun : ∀ N : ℕ, N ≠ 0 →
      ((N : ℝ)⁻¹ : ℂ) * ∑ _m ∈ Finset.range N, (1 : ℂ) ^ _m = 1 := by
    intro N hN
    have hNne : ((N : ℝ) : ℂ) ≠ 0 := by
      simpa using (Nat.cast_ne_zero (R := ℂ)).mpr hN
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    field_simp
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop 0] with N hN
  exact (hfun N (by omega)).symm

/-! ### Moment determinacy -/

/-- The shifted Cesàro mean of a geometric progression in the closed unit disc. -/
theorem tendsto_shiftedGeomSum_cesaro {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Tendsto (fun N : ℕ => ((N : ℝ)⁻¹ : ℂ) * ∑ m ∈ Finset.range N, w ^ (m + 1))
      atTop (𝓝 (if w = 1 then 1 else 0)) := by
  have hrw : ∀ N : ℕ, ((N : ℝ)⁻¹ : ℂ) * ∑ m ∈ Finset.range N, w ^ (m + 1)
      = w * (((N : ℝ)⁻¹ : ℂ) * ∑ m ∈ Finset.range N, w ^ m) := by
    intro N
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun m _ => by rw [pow_succ]; ring)
  simp only [hrw]
  by_cases hw1 : w = 1
  · subst hw1
    rw [if_pos rfl]
    simpa using tendsto_geomSum_cesaro_one.const_mul (1 : ℂ)
  · rw [if_neg hw1]
    simpa using (tendsto_geomSum_cesaro_of_norm_le_one hw hw1).const_mul w

theorem norm_shiftedGeomSum_le_card {w : ℂ} (hw : ‖w‖ ≤ 1) (K : ℕ) :
    ‖∑ m ∈ Finset.range K, w ^ (m + 1)‖ ≤ (K : ℝ) := by
  calc ‖∑ m ∈ Finset.range K, w ^ (m + 1)‖ ≤ ∑ m ∈ Finset.range K, ‖w ^ (m + 1)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.range K, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun m _ => ?_)
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg w) hw
    _ = (K : ℝ) := by simp

/-- **Summable atomic data is determined by its power moments.**  If the atoms are nonzero, the
weights absolutely summable, the atoms accumulate only at the origin, and every moment of order at
least one vanishes, then every weight vanishes.  Only moments of order `≥ 1` are used, so an extra
atom sitting at the accumulation point is harmless. -/
theorem coeff_eq_zero_of_atomicMoments_vanish
    {c z : ℕ → ℂ} (hinj : Function.Injective z) (hznz : ∀ j, z j ≠ 0)
    (hsum : Summable fun j => ‖c j‖)
    (hz : Tendsto (fun j => ‖z j‖) atTop (𝓝 0))
    (hmom : ∀ n : ℕ, 1 ≤ n → ∑' j, c j * (z j) ^ n = 0) :
    ∀ j, c j = 0 := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨j₁, hj₁⟩ := hcon
  have hpos₁ : 0 < ‖z j₁‖ := norm_pos_iff.mpr (hznz j₁)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hz.eventually (gt_mem_nhds hpos₁))
  have hsubset : {j : ℕ | ‖z j₁‖ ≤ ‖z j‖} ⊆ Set.Iio N := by
    intro j hj
    simp only [Set.mem_Iio]
    by_contra hge
    push Not at hge
    exact absurd (hN j hge) (not_lt.mpr hj)
  have hfin : {j : ℕ | ‖z j₁‖ ≤ ‖z j‖}.Finite :=
    Set.Finite.subset (Set.finite_Iio N) hsubset
  set F : Finset ℕ := hfin.toFinset with hF
  set T : Finset ℕ := F.filter (fun j => c j ≠ 0) with hT
  have hmemF : ∀ j, j ∈ F ↔ ‖z j₁‖ ≤ ‖z j‖ := by
    intro j
    rw [hF, Set.Finite.mem_toFinset]
    exact Iff.rfl
  have hmemT : ∀ j, j ∈ T ↔ (‖z j₁‖ ≤ ‖z j‖ ∧ c j ≠ 0) := by
    intro j
    rw [hT, Finset.mem_filter, hmemF]
  have hj₁T : j₁ ∈ T := (hmemT j₁).mpr ⟨le_refl _, hj₁⟩
  obtain ⟨j₀, hj₀T, hj₀max⟩ := T.exists_max_image (fun j => ‖z j‖) ⟨j₁, hj₁T⟩
  have hj₀c : c j₀ ≠ 0 := ((hmemT j₀).mp hj₀T).2
  have hj₀le : ∀ j, c j ≠ 0 → ‖z j‖ ≤ ‖z j₀‖ := by
    intro j hj
    by_contra hgt
    push Not at hgt
    have h1 : ‖z j₁‖ ≤ ‖z j₀‖ := hj₀max j₁ hj₁T
    exact absurd (hj₀max j ((hmemT j).mpr ⟨le_trans h1 (le_of_lt hgt), hj⟩)) (not_le.mpr hgt)
  set u : ℕ → ℂ := fun j => z j / z j₀ with hu
  have hz₀ne : z j₀ ≠ 0 := hznz j₀
  have huone : u j₀ = 1 := div_self hz₀ne
  have huniq : ∀ j, u j = 1 → j = j₀ := by
    intro j hj
    have hzz : z j = z j₀ := by
      have := hj
      rw [hu, div_eq_one_iff_eq hz₀ne] at this
      exact this
    exact hinj hzz
  have hule : ∀ j, c j ≠ 0 → ‖u j‖ ≤ 1 := by
    intro j hj
    rw [hu, norm_div]
    exact div_le_one_of_le₀ (hj₀le j hj) (norm_nonneg _)
  have hmomu : ∀ m : ℕ, ∑' j, c j * (u j) ^ (m + 1) = 0 := by
    intro m
    have hrew : ∀ j, c j * (u j) ^ (m + 1)
        = ((z j₀) ^ (m + 1))⁻¹ * (c j * (z j) ^ (m + 1)) := by
      intro j
      rw [hu, div_pow]
      field_simp
    calc ∑' j, c j * (u j) ^ (m + 1)
        = ∑' j, ((z j₀) ^ (m + 1))⁻¹ * (c j * (z j) ^ (m + 1)) := tsum_congr hrew
      _ = ((z j₀) ^ (m + 1))⁻¹ * ∑' j, c j * (z j) ^ (m + 1) := by rw [tsum_mul_left]
      _ = 0 := by rw [hmom (m + 1) (by omega), mul_zero]
  have hsummu : ∀ m : ℕ, Summable fun j => c j * (u j) ^ (m + 1) := by
    intro m
    refine Summable.of_norm_bounded hsum (fun j => ?_)
    by_cases hj : c j = 0
    · simp [hj]
    · rw [norm_mul, norm_pow]
      calc ‖c j‖ * ‖u j‖ ^ (m + 1) ≤ ‖c j‖ * 1 := by
            gcongr
            exact pow_le_one₀ (norm_nonneg _) (hule j hj)
        _ = ‖c j‖ := by ring
  set f : ℕ → ℕ → ℂ :=
    fun N j => c j * (((N : ℝ)⁻¹ : ℂ) * ∑ m ∈ Finset.range N, (u j) ^ (m + 1)) with hf
  have hbound : ∀ N : ℕ, ∀ j, ‖f N j‖ ≤ ‖c j‖ := by
    intro N j
    by_cases hj : c j = 0
    · simp [hf, hj]
    · rw [hf, norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Nat.cast_nonneg N)]
      rcases Nat.eq_zero_or_pos N with rfl | hN0
      · simp
      · have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN0
        have hle : (N : ℝ)⁻¹ * ‖∑ m ∈ Finset.range N, (u j) ^ (m + 1)‖ ≤ 1 := by
          rw [inv_mul_le_iff₀ hNpos, mul_one]
          exact norm_shiftedGeomSum_le_card (hule j hj) N
        calc ‖c j‖ * ((N : ℝ)⁻¹ * ‖∑ m ∈ Finset.range N, (u j) ^ (m + 1)‖)
            ≤ ‖c j‖ * 1 := mul_le_mul_of_nonneg_left hle (norm_nonneg _)
          _ = ‖c j‖ := by ring
  have hpt : ∀ j, Tendsto (f · j) atTop (𝓝 (if j = j₀ then c j₀ else 0)) := by
    intro j
    by_cases hj : c j = 0
    · have hne : j ≠ j₀ := fun h => hj₀c (h ▸ hj)
      rw [if_neg hne]
      simpa [hf, hj] using tendsto_const_nhds (α := ℕ) (x := (0 : ℂ))
    · have hlim := (tendsto_shiftedGeomSum_cesaro (hule j hj)).const_mul (c j)
      by_cases hjj : j = j₀
      · subst hjj
        rw [if_pos rfl]
        simpa [hf, huone] using hlim
      · have hune : u j ≠ 1 := fun h => hjj (huniq j h)
        rw [if_neg hjj]
        simpa [hf, hune] using hlim
  have hlim := tendsto_tsum_of_dominated_convergence (f := f)
    (g := fun j => if j = j₀ then c j₀ else 0) (bound := fun j => ‖c j‖)
    hsum hpt (Eventually.of_forall hbound)
  have hzero : ∀ N : ℕ, (∑' j, f N j) = 0 := by
    intro N
    have hswap : (∑' j, f N j)
        = ((N : ℝ)⁻¹ : ℂ) * ∑ m ∈ Finset.range N, ∑' j, c j * (u j) ^ (m + 1) := by
      calc (∑' j, f N j)
          = ∑' j, ∑ m ∈ Finset.range N, ((N : ℝ)⁻¹ : ℂ) * (c j * (u j) ^ (m + 1)) := by
            refine tsum_congr (fun j => ?_)
            show c j * (((N : ℝ)⁻¹ : ℂ) * ∑ m ∈ Finset.range N, (u j) ^ (m + 1))
              = ∑ m ∈ Finset.range N, ((N : ℝ)⁻¹ : ℂ) * (c j * (u j) ^ (m + 1))
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl (fun m _ => by ring)
        _ = ∑ m ∈ Finset.range N, ∑' j, ((N : ℝ)⁻¹ : ℂ) * (c j * (u j) ^ (m + 1)) :=
            Summable.tsum_finsetSum (fun m _ => (hsummu m).mul_left _)
        _ = ∑ m ∈ Finset.range N, ((N : ℝ)⁻¹ : ℂ) * ∑' j, c j * (u j) ^ (m + 1) :=
            Finset.sum_congr rfl (fun m _ => tsum_mul_left)
        _ = ((N : ℝ)⁻¹ : ℂ) * ∑ m ∈ Finset.range N, ∑' j, c j * (u j) ^ (m + 1) := by
            rw [Finset.mul_sum]
    rw [hswap, Finset.sum_congr rfl (fun m _ => hmomu m)]
    simp
  rw [funext hzero] at hlim
  have hlimval : (∑' j, if j = j₀ then c j₀ else 0) = c j₀ := by
    rw [tsum_eq_single j₀]
    · rw [if_pos rfl]
    · intro b hb
      rw [if_neg hb]
  rw [hlimval] at hlim
  exact hj₀c (tendsto_nhds_unique hlim tendsto_const_nhds)

/-- Every power moment of summable atomic data converges. -/
theorem summable_atomicMoment {c z : ℕ → ℂ} (hsum : Summable fun j => ‖c j‖)
    (hz : Tendsto (fun j => ‖z j‖) atTop (𝓝 0)) (n : ℕ) :
    Summable fun j => c j * (z j) ^ n := by
  obtain ⟨M, hM⟩ := hz.bddAbove_range
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg (z 0)) (hM ⟨0, rfl⟩)
  refine Summable.of_norm_bounded (hsum.mul_right (M ^ n)) (fun j => ?_)
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg _) (hM ⟨j, rfl⟩) n

/-- **Difference form.**  Two summable atomic data on the same atom set with equal power moments
have equal weights: the all-order moment tower is faithful to the weighted divisor. -/
theorem atomicData_eq_of_moments_eq
    {c c' z : ℕ → ℂ} (hinj : Function.Injective z) (hznz : ∀ j, z j ≠ 0)
    (hsum : Summable fun j => ‖c j‖) (hsum' : Summable fun j => ‖c' j‖)
    (hz : Tendsto (fun j => ‖z j‖) atTop (𝓝 0))
    (hmom : ∀ n : ℕ, 1 ≤ n → ∑' j, c j * (z j) ^ n = ∑' j, c' j * (z j) ^ n) :
    ∀ j, c j = c' j := by
  have hsub : Summable fun j => ‖c j - c' j‖ :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => norm_sub_le _ _)
      (hsum.add hsum')
  have hkey : ∀ n : ℕ, 1 ≤ n → ∑' j, (c j - c' j) * (z j) ^ n = 0 := by
    intro n hn
    have h1 := summable_atomicMoment hsum hz n
    have h2 := summable_atomicMoment hsum' hz n
    calc ∑' j, (c j - c' j) * (z j) ^ n
        = ∑' j, (c j * (z j) ^ n - c' j * (z j) ^ n) := tsum_congr (fun j => by ring)
      _ = (∑' j, c j * (z j) ^ n) - ∑' j, c' j * (z j) ^ n := h1.tsum_sub h2
      _ = 0 := by rw [hmom n hn, sub_self]
  intro j
  exact sub_eq_zero.mp (coeff_eq_zero_of_atomicMoments_vanish hinj hznz hsub hz hkey j)

/-- **With an atom at the accumulation point.**  Allowing each datum one extra atom at the
accumulation point, equality of all moments (order `0` included) forces equality of every weight,
including the mass at the accumulation point.  This is the protector-tail form: the support is the
shifted reciprocal zero support together with its hard-edge accumulation point. -/
theorem atomicData_withCenter_eq_of_moments_eq
    {c c' z : ℕ → ℂ} {c₀ c₀' : ℂ} (hinj : Function.Injective z) (hznz : ∀ j, z j ≠ 0)
    (hsum : Summable fun j => ‖c j‖) (hsum' : Summable fun j => ‖c' j‖)
    (hz : Tendsto (fun j => ‖z j‖) atTop (𝓝 0))
    (hmom : ∀ n : ℕ, 1 ≤ n → ∑' j, c j * (z j) ^ n = ∑' j, c' j * (z j) ^ n)
    (hmom0 : c₀ + ∑' j, c j = c₀' + ∑' j, c' j) :
    (∀ j, c j = c' j) ∧ c₀ = c₀' := by
  have hcc : ∀ j, c j = c' j :=
    atomicData_eq_of_moments_eq hinj hznz hsum hsum' hz hmom
  refine ⟨hcc, ?_⟩
  have hts : (∑' j, c j) = ∑' j, c' j := tsum_congr hcc
  rw [hts] at hmom0
  exact add_right_cancel hmom0

end GaloisForLFunctions.HTGeometry

