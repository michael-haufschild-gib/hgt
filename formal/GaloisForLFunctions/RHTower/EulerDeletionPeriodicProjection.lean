import GaloisForLFunctions.RHTower.CausalMobiusThetaHistoryLocalization
import Mathlib.Analysis.SumOverResidueClass

/-!
# Projection onto periodic physical sequences

`periodicSpace Q` is the closed subspace of physical observables determined by the residue of the
cell modulo `Q`; the chronological history spaces are `historySpace L = periodicSpace (clock L)`.
On a residue fibre `b + Qℕ` the orthogonal projection is the weighted fibre mean
`S_b/V_b`, with `S_b = Σ_k v(b+Qk) w(b+Qk)` and `V_b = Σ_k w(b+Qk) ≥ w(b)`.  Consequences:

* `‖P_Q v‖² = Σ_{b<Q} S_b²/V_b`;
* `Σ_j w_j |v_j − (P_Q v)_j| ≤ (6/Q²) Σ_j |v_j|` for every absolutely summable `v`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

namespace DeletionResidueMartingale

/-- Physical observables determined by the residue modulo `Q`. -/
def periodicSpace (Q : ℕ) : Submodule ℝ (Lp ℝ 2 cellMeasure) :=
  lpMeas ℝ ℝ (residueSigma Q) 2 cellMeasure

instance (Q : ℕ) : (periodicSpace Q).HasOrthogonalProjection := by
  haveI : Fact (residueSigma Q ≤ (inferInstance : MeasurableSpace ℕ)) := ⟨le_top⟩
  unfold periodicSpace
  infer_instance

theorem historySpace_eq_periodicSpace (L : ℕ) : historySpace L = periodicSpace (clock L) := rfl

theorem periodicSpace_factors (Q : ℕ) (v : Lp ℝ 2 cellMeasure) (hv : v ∈ periodicSpace Q) :
    ∃ h : ℕ → ℝ, ∀ j : ℕ, v j = h (j % Q) := by
  change v ∈ lpMeas ℝ ℝ (residueSigma Q) 2 cellMeasure at hv
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hv
  have hg₀ : StronglyMeasurable[residueSigma Q] (hv.mk (v : ℕ → ℝ)) := hv.stronglyMeasurable_mk
  obtain ⟨h, -, hfac⟩ := hg₀.exists_eq_measurable_comp (f := fun j : ℕ => j % Q)
  refine ⟨h, fun j => ?_⟩
  rw [cell_point_eq_of_ae hv.ae_eq_mk j, hfac]
  rfl

theorem mem_periodicSpace_of_apply (Q : ℕ) (v : Lp ℝ 2 cellMeasure) (h : ℕ → ℝ)
    (hv : ∀ j, v j = h (j % Q)) : v ∈ periodicSpace Q := by
  change v ∈ lpMeas ℝ ℝ (residueSigma Q) 2 cellMeasure
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  refine ⟨fun j => h (j % Q), ?_, Eventually.of_forall hv⟩
  exact (measurable_of_countable h).stronglyMeasurable.comp_measurable
    (comap_measurable (fun j : ℕ => j % Q))

/-- Regrouping a summable series by residue classes. -/
theorem tsum_eq_sum_range_tsum_progression {f : ℕ → ℝ} (hf : Summable f) {Q : ℕ} (hQ : 0 < Q) :
    ∑' j, f j = ∑ b ∈ Finset.range Q, ∑' k, f (b + Q * k) := by
  haveI : NeZero Q := ⟨hQ.ne'⟩
  rw [Nat.sumByResidueClasses hf Q]
  obtain ⟨n, rfl⟩ : ∃ n, Q = n + 1 := ⟨Q - 1, by omega⟩
  exact Fin.sum_univ_eq_sum_range (fun b => ∑' k, f (b + (n + 1) * k)) (n + 1)

theorem progression_injective (b Q : ℕ) (hQ : 0 < Q) : Function.Injective fun k : ℕ => b + Q * k :=
  fun _ _ h => Nat.eq_of_mul_eq_mul_left hQ (by simpa using h)

/-- The physical fibre mass `V_b`. -/
def cellFibreMass (Q b : ℕ) : ℝ := ∑' k, cellWeight (b + Q * k)

/-- The physical fibre moment `S_b`. -/
def cellFibreSum (f : ℕ → ℝ) (Q b : ℕ) : ℝ := ∑' k, f (b + Q * k) * cellWeight (b + Q * k)

theorem summable_cellWeight_progression (b Q : ℕ) (hQ : 0 < Q) :
    Summable fun k => cellWeight (b + Q * k) :=
  hasSum_cellWeight.summable.comp_injective (progression_injective b Q hQ)

theorem cellWeight_le_cellFibreMass (b Q : ℕ) (hQ : 0 < Q) : cellWeight b ≤ cellFibreMass Q b := by
  have h := (summable_cellWeight_progression b Q hQ).le_tsum 0
    (fun k _ => (cellWeight_pos _).le)
  simpa [cellFibreMass] using h

theorem cellFibreMass_pos (b Q : ℕ) (hQ : 0 < Q) : 0 < cellFibreMass Q b :=
  (cellWeight_pos b).trans_le (cellWeight_le_cellFibreMass b Q hQ)

/-- `V_b ≥ 1/(Q(Q+1))` on the first period. -/
theorem inv_le_cellFibreMass {b Q : ℕ} (hQ : 0 < Q) (hb : b < Q) :
    ((Q : ℝ) * (Q + 1))⁻¹ ≤ cellFibreMass Q b := by
  refine le_trans ?_ (cellWeight_le_cellFibreMass b Q hQ)
  rw [cellWeight, one_div]
  have h1 : (b : ℝ) + 1 ≤ Q := by exact_mod_cast hb
  apply inv_anti₀ (by positivity)
  nlinarith

theorem summable_mul_cellWeight_of_lp (v : Lp ℝ 2 cellMeasure) :
    Summable fun j => v j * cellWeight j :=
  (hasSum_inner_cellUnitVec_left v).summable

theorem summable_progression_of_summable {f : ℕ → ℝ} (hf : Summable f) (b Q : ℕ) (hQ : 0 < Q) :
    Summable fun k => f (b + Q * k) :=
  hf.comp_injective (progression_injective b Q hQ)

/-- **The periodic projection is the weighted fibre mean.** -/
theorem starProjection_periodicSpace_eq {Q : ℕ} (hQ : 0 < Q) (v : Lp ℝ 2 cellMeasure) :
    (periodicSpace Q).starProjection v =
      physVec fun j => cellFibreSum v Q (j % Q) / cellFibreMass Q (j % Q) := by
  set c : ℕ → ℝ := fun b => cellFibreSum v Q b / cellFibreMass Q b with hc
  set C : ℝ := ∑ b ∈ Finset.range Q, |c b|
  have hcb : ∀ j, |c (j % Q)| ≤ C := fun j =>
    Finset.single_le_sum (f := fun b => |c b|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.mod_lt j hQ))
  have hsq : Summable fun j => (c (j % Q)) ^ 2 * cellWeight j := by
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (sq_nonneg _) (cellWeight_pos j).le)
      (fun j => ?_) (hasSum_cellWeight.summable.mul_left (C ^ 2))
    exact mul_le_mul_of_nonneg_right (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hcb j) 2)
      (cellWeight_pos j).le
  set u := physVec fun j => c (j % Q)
  have hu : ∀ j, u j = c (j % Q) := physVec_apply hsq
  have hmem : u ∈ periodicSpace Q := mem_periodicSpace_of_apply Q u c hu
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem fun w hw => ?_
  obtain ⟨h, hh⟩ := periodicSpace_factors Q w hw
  have hdiff : ∀ j, (v - u) j = v j - c (j % Q) := fun j => by
    rw [cell_point_eq_of_ae (Lp.coeFn_sub v u) j, Pi.sub_apply, hu]
  have hs := hasSum_inner (v - u) w
  rw [← hs.tsum_eq, tsum_eq_sum_range_tsum_progression hs.summable hQ]
  refine Finset.sum_eq_zero fun b hb => ?_
  have hbQ : b < Q := Finset.mem_range.1 hb
  have hmod : ∀ k, (b + Q * k) % Q = b := fun k => by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbQ]
  have hterm : ∀ k, (v - u) (b + Q * k) * w (b + Q * k) * cellWeight (b + Q * k) =
      h b * (v (b + Q * k) * cellWeight (b + Q * k)) - h b * c b * cellWeight (b + Q * k) := by
    intro k
    rw [hdiff, hh, hmod]
    ring
  rw [tsum_congr hterm]
  have hs1 := (summable_progression_of_summable (summable_mul_cellWeight_of_lp v) b Q hQ).mul_left (h b)
  have hs2 := (summable_cellWeight_progression b Q hQ).mul_left (h b * c b)
  rw [Summable.tsum_sub hs1 hs2, tsum_mul_left, tsum_mul_left]
  have hV := cellFibreMass_pos b Q hQ
  simp only [c, cellFibreSum, cellFibreMass] at hV ⊢
  field_simp
  ring

theorem starProjection_periodicSpace_apply {Q : ℕ} (hQ : 0 < Q) (v : Lp ℝ 2 cellMeasure) (j : ℕ) :
    (periodicSpace Q).starProjection v j = cellFibreSum v Q (j % Q) / cellFibreMass Q (j % Q) := by
  rw [starProjection_periodicSpace_eq hQ]
  refine physVec_apply ?_ j
  set C : ℝ := ∑ b ∈ Finset.range Q, |cellFibreSum v Q b / cellFibreMass Q b|
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (sq_nonneg _) (cellWeight_pos j).le)
    (fun j => ?_) (hasSum_cellWeight.summable.mul_left (C ^ 2))
  have hcb : |cellFibreSum v Q (j % Q) / cellFibreMass Q (j % Q)| ≤ C :=
    Finset.single_le_sum (f := fun b => |cellFibreSum v Q b / cellFibreMass Q b|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.2 (Nat.mod_lt j hQ))
  exact mul_le_mul_of_nonneg_right (by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hcb 2)
    (cellWeight_pos j).le

/-- `‖P_Q v‖² = Σ_{b<Q} S_b²/V_b`. -/
theorem norm_sq_starProjection_periodicSpace {Q : ℕ} (hQ : 0 < Q) (v : Lp ℝ 2 cellMeasure) :
    ‖(periodicSpace Q).starProjection v‖ ^ 2 =
      ∑ b ∈ Finset.range Q, cellFibreSum v Q b ^ 2 / cellFibreMass Q b := by
  have hs := hasSum_norm_sq ((periodicSpace Q).starProjection v)
  rw [← hs.tsum_eq, tsum_eq_sum_range_tsum_progression hs.summable hQ]
  refine Finset.sum_congr rfl fun b hb => ?_
  have hbQ : b < Q := Finset.mem_range.1 hb
  have hmod : ∀ k, (b + Q * k) % Q = b := fun k => by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbQ]
  simp_rw [starProjection_periodicSpace_apply hQ, hmod]
  rw [tsum_mul_left]
  have hV := cellFibreMass_pos b Q hQ
  rw [cellFibreMass] at hV ⊢
  field_simp

/-- `‖P_Q v‖² ≤ Q(Q+1) Σ_{b<Q} S_b²`. -/
theorem norm_sq_starProjection_periodicSpace_le {Q : ℕ} (hQ : 0 < Q) (v : Lp ℝ 2 cellMeasure) :
    ‖(periodicSpace Q).starProjection v‖ ^ 2 ≤
      (Q : ℝ) * (Q + 1) * ∑ b ∈ Finset.range Q, cellFibreSum v Q b ^ 2 := by
  rw [norm_sq_starProjection_periodicSpace hQ, Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  have hV := inv_le_cellFibreMass hQ (Finset.mem_range.1 hb)
  have hV0 := cellFibreMass_pos b Q hQ
  rw [div_eq_mul_inv, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [inv_le_comm₀ hV0 (by positivity)]
  exact hV

/-! ## Weighted `L¹` deviation from the fibre mean -/

/-- For one fibre: `Σ_k c_k |x_k − m| ≤ 2 Σ_{k≥1} c_k |x_k − x_0|` with `m` the weighted mean. -/
theorem tsum_weight_abs_sub_mean_le {c x : ℕ → ℝ} (hc : ∀ k, 0 ≤ c k) (hcs : Summable c)
    (hcx : Summable fun k => c k * |x k|) (hV : 0 < ∑' k, c k) :
    ∑' k, c k * |x k - (∑' k, c k * x k) / ∑' k, c k| ≤
      2 * ∑' k, c (k + 1) * |x (k + 1) - x 0| := by
  set V := ∑' k, c k with hVdef
  set m := (∑' k, c k * x k) / V with hmdef
  have hcx' : Summable fun k => c k * x k :=
    Summable.of_norm_bounded hcx fun k => by rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc k)]
  have habs : ∀ a : ℝ, Summable fun k => c k * |x k - a| := by
    intro a
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (hc k) (abs_nonneg _)) (fun k => ?_)
      (hcx.add (hcs.mul_right |a|))
    calc c k * |x k - a| ≤ c k * (|x k| + |a|) := mul_le_mul_of_nonneg_left (abs_sub _ _) (hc k)
      _ = c k * |x k| + c k * |a| := by ring
  have hd := habs (x 0)
  have hdm := habs m
  have hrepr : x 0 - m = (∑' k, c k * (x 0 - x k)) / V := by
    have hs : (fun k => c k * (x 0 - x k)) = fun k => x 0 * c k - c k * x k := by
      funext k; ring
    rw [hs, Summable.tsum_sub (hcs.mul_left _) hcx', tsum_mul_left, hmdef]
    field_simp
    rw [hVdef]
  have hnorm : |∑' k, c k * (x 0 - x k)| ≤ ∑' k, c k * |x k - x 0| := by
    have hs : Summable fun k => ‖c k * (x 0 - x k)‖ := hd.congr fun k => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc k), abs_sub_comm]
    refine (norm_tsum_le_tsum_norm hs).trans (le_of_eq (tsum_congr fun k => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc k), abs_sub_comm]
  have hmean : V * |x 0 - m| ≤ ∑' k, c k * |x k - x 0| := by
    rw [hrepr, abs_div, abs_of_pos hV, mul_div_cancel₀ _ hV.ne']
    exact hnorm
  have h1 : ∑' k, c k * |x k - m| ≤ ∑' k, (c k * |x k - x 0| + c k * |x 0 - m|) := by
    refine Summable.tsum_le_tsum (fun k => ?_) hdm (hd.add (hcs.mul_right _))
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left (abs_sub_le (x k) (x 0) m) (hc k)
  rw [Summable.tsum_add hd (hcs.mul_right _), tsum_mul_right] at h1
  have h3 : ∑' k, c k * |x k - x 0| = ∑' k, c (k + 1) * |x (k + 1) - x 0| := by
    rw [hd.tsum_eq_zero_add]; simp
  linarith

/-- **Weighted `L¹` deviation:** `Σ_j w_j |v_j − (P_Q v)_j| ≤ (6/Q²) Σ_j |v_j|`. -/
theorem tsum_cellWeight_abs_sub_starProjection_periodicSpace_le {Q : ℕ} (hQ : 0 < Q)
    (v : Lp ℝ 2 cellMeasure) (hv : Summable fun j => |v j|) :
    Summable (fun j => cellWeight j * |v j - (periodicSpace Q).starProjection v j|) ∧
      ∑' j, cellWeight j * |v j - (periodicSpace Q).starProjection v j| ≤
        6 / (Q : ℝ) ^ 2 * ∑' j, |v j| := by
  set P := (periodicSpace Q).starProjection v with hPdef
  have hP : ∀ j, P j = cellFibreSum v Q (j % Q) / cellFibreMass Q (j % Q) :=
    starProjection_periodicSpace_apply hQ v
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hcw_le_half : ∀ j, cellWeight j ≤ 1 := fun j => by
    rw [cellWeight, div_le_one (by positivity)]; nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  set C : ℝ := ∑ b ∈ Finset.range Q, |cellFibreSum v Q b / cellFibreMass Q b|
  have hPb : ∀ j, |P j| ≤ C := fun j => by
    rw [hP]
    exact Finset.single_le_sum (f := fun b => |cellFibreSum v Q b / cellFibreMass Q b|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.2 (Nat.mod_lt j hQ))
  have hsum : Summable fun j => cellWeight j * |v j - P j| := by
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (cellWeight_pos j).le (abs_nonneg _))
      (fun j => ?_) (hv.add (hasSum_cellWeight.summable.mul_left C))
    calc cellWeight j * |v j - P j| ≤ cellWeight j * (|v j| + C) :=
          mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add le_rfl (hPb j)))
            (cellWeight_pos j).le
      _ = cellWeight j * |v j| + C * cellWeight j := by ring
      _ ≤ |v j| + C * cellWeight j := by
          gcongr; exact mul_le_of_le_one_left (abs_nonneg _) (hcw_le_half j)
  refine ⟨hsum, ?_⟩
  have hvabs := tsum_eq_sum_range_tsum_progression hv hQ
  rw [tsum_eq_sum_range_tsum_progression hsum hQ]
  have hfib : ∀ b ∈ Finset.range Q, ∑' k, cellWeight (b + Q * k) * |v (b + Q * k) - P (b + Q * k)| ≤
      2 / (Q : ℝ) ^ 2 * ∑' k, |v (b + Q * k)| + 4 / (Q : ℝ) ^ 2 * |v b| := by
    intro b hb
    have hbQ : b < Q := Finset.mem_range.1 hb
    have hmod : ∀ k, (b + Q * k) % Q = b := fun k => by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hbQ]
    set c : ℕ → ℝ := fun k => cellWeight (b + Q * k)
    set x : ℕ → ℝ := fun k => v (b + Q * k)
    have hc : ∀ k, 0 ≤ c k := fun k => (cellWeight_pos _).le
    have hcs : Summable c := summable_cellWeight_progression b Q hQ
    have hxs : Summable fun k => |x k| := summable_progression_of_summable hv b Q hQ
    have hcx : Summable fun k => c k * |x k| :=
      Summable.of_nonneg_of_le (fun k => mul_nonneg (hc k) (abs_nonneg _))
        (fun k => mul_le_of_le_one_left (abs_nonneg _) (hcw_le_half _)) hxs
    have hmean : (∑' k, c k * x k) / ∑' k, c k = cellFibreSum v Q b / cellFibreMass Q b := by
      simp only [c, x, cellFibreSum, cellFibreMass, mul_comm]
    have hstep := tsum_weight_abs_sub_mean_le hc hcs hcx (cellFibreMass_pos b Q hQ)
    rw [hmean] at hstep
    have hPk : ∀ k, P (b + Q * k) = cellFibreSum v Q b / cellFibreMass Q b := fun k => by rw [hP, hmod]
    have hl : ∑' k, cellWeight (b + Q * k) * |v (b + Q * k) - P (b + Q * k)| =
        ∑' k, c k * |x k - cellFibreSum v Q b / cellFibreMass Q b| :=
      tsum_congr fun k => by rw [hPk]
    rw [hl]
    refine hstep.trans ?_
    -- termwise majorant
    have hw1 : ∀ k, c (k + 1) ≤ 1 / (Q : ℝ) ^ 2 := fun k => by
      simp only [c, cellWeight]
      rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul]
      have : (Q : ℝ) ≤ (b : ℝ) + Q * ((k : ℝ) + 1) := by nlinarith [(Nat.cast_nonneg b : (0:ℝ) ≤ b),
        (Nat.cast_nonneg k : (0:ℝ) ≤ k)]
      push_cast
      nlinarith
    have hw2 : ∀ k, c (k + 1) ≤ 2 / (Q : ℝ) ^ 2 * cellWeight k := fun k => by
      simp only [c, cellWeight]
      rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
      push_cast
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
      have h1 : (Q : ℝ) * ((k : ℝ) + 1) ≤ (b : ℝ) + Q * ((k : ℝ) + 1) + 1 := by linarith
      have h2 : (Q : ℝ) * ((k : ℝ) + 1) ≤ (b : ℝ) + Q * ((k : ℝ) + 1) + 2 := by linarith
      have h3 : ((k : ℝ) + 2) ≤ 2 * ((k : ℝ) + 1) := by linarith
      have h4 : (Q : ℝ) ^ 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2)) ≤
          2 * ((Q * ((k : ℝ) + 1)) * (Q * ((k : ℝ) + 1))) := by nlinarith
      have h5 : (Q * ((k : ℝ) + 1)) * (Q * ((k : ℝ) + 1)) ≤
          ((b : ℝ) + Q * ((k : ℝ) + 1) + 1) * ((b : ℝ) + Q * ((k : ℝ) + 1) + 2) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
      nlinarith
    have hs1 : Summable fun k => |x (k + 1)| := (summable_nat_add_iff 1).2 hxs
    have hmaj : Summable fun k => 1 / (Q : ℝ) ^ 2 * |x (k + 1)| + 2 / (Q : ℝ) ^ 2 * |x 0| * cellWeight k :=
      (hs1.mul_left _).add (hasSum_cellWeight.summable.mul_left _)
    have hlhs : Summable fun k => c (k + 1) * |x (k + 1) - x 0| :=
      Summable.of_nonneg_of_le (fun k => mul_nonneg (hc _) (abs_nonneg _)) (fun k => ?_) hmaj
    · have hle : ∑' k, c (k + 1) * |x (k + 1) - x 0| ≤
          ∑' k, (1 / (Q : ℝ) ^ 2 * |x (k + 1)| + 2 / (Q : ℝ) ^ 2 * |x 0| * cellWeight k) :=
        Summable.tsum_le_tsum (fun k => ?_) hlhs hmaj
      · rw [Summable.tsum_add (hs1.mul_left _) (hasSum_cellWeight.summable.mul_left _), tsum_mul_left,
          tsum_mul_left, hasSum_cellWeight.tsum_eq, mul_one] at hle
        have hdrop : ∑' k, |x (k + 1)| ≤ ∑' k, |x k| := by
          rw [hxs.tsum_eq_zero_add]; linarith [abs_nonneg (x 0)]
        have hx0 : x 0 = v b := by simp [x]
        calc 2 * ∑' k, c (k + 1) * |x (k + 1) - x 0| ≤
              2 * (1 / (Q : ℝ) ^ 2 * ∑' k, |x (k + 1)| + 2 / (Q : ℝ) ^ 2 * |x 0|) := by linarith
          _ ≤ 2 * (1 / (Q : ℝ) ^ 2 * ∑' k, |x k| + 2 / (Q : ℝ) ^ 2 * |x 0|) := by
              gcongr
          _ = 2 / (Q : ℝ) ^ 2 * ∑' k, |v (b + Q * k)| + 4 / (Q : ℝ) ^ 2 * |v b| := by
              rw [hx0]; simp only [x]; ring
      · calc c (k + 1) * |x (k + 1) - x 0| ≤ c (k + 1) * (|x (k + 1)| + |x 0|) :=
              mul_le_mul_of_nonneg_left (abs_sub _ _) (hc _)
          _ = c (k + 1) * |x (k + 1)| + c (k + 1) * |x 0| := by ring
          _ ≤ 1 / (Q : ℝ) ^ 2 * |x (k + 1)| + 2 / (Q : ℝ) ^ 2 * cellWeight k * |x 0| :=
              add_le_add (mul_le_mul_of_nonneg_right (hw1 k) (abs_nonneg _))
                (mul_le_mul_of_nonneg_right (hw2 k) (abs_nonneg _))
          _ = _ := by ring
    · calc c (k + 1) * |x (k + 1) - x 0| ≤ c (k + 1) * (|x (k + 1)| + |x 0|) :=
            mul_le_mul_of_nonneg_left (abs_sub _ _) (hc _)
        _ = c (k + 1) * |x (k + 1)| + c (k + 1) * |x 0| := by ring
        _ ≤ 1 / (Q : ℝ) ^ 2 * |x (k + 1)| + 2 / (Q : ℝ) ^ 2 * cellWeight k * |x 0| :=
            add_le_add (mul_le_mul_of_nonneg_right (hw1 k) (abs_nonneg _))
              (mul_le_mul_of_nonneg_right (hw2 k) (abs_nonneg _))
        _ = _ := by ring
  calc ∑ b ∈ Finset.range Q, ∑' k, cellWeight (b + Q * k) * |v (b + Q * k) - P (b + Q * k)|
      ≤ ∑ b ∈ Finset.range Q, (2 / (Q : ℝ) ^ 2 * ∑' k, |v (b + Q * k)| + 4 / (Q : ℝ) ^ 2 * |v b|) :=
        Finset.sum_le_sum hfib
    _ = 2 / (Q : ℝ) ^ 2 * ∑' j, |v j| + 4 / (Q : ℝ) ^ 2 * ∑ b ∈ Finset.range Q, |v b| := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← hvabs]
    _ ≤ 2 / (Q : ℝ) ^ 2 * ∑' j, |v j| + 4 / (Q : ℝ) ^ 2 * ∑' j, |v j| := by
        gcongr
        exact hv.sum_le_tsum _ fun j _ => abs_nonneg _
    _ = 6 / (Q : ℝ) ^ 2 * ∑' j, |v j| := by ring

end DeletionResidueMartingale

end

end RHTower
