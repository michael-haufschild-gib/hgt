/-
# The transfer function of a Hilbert-space contraction

A contraction `V` of a Hilbert space carrying `p z • ev z + w` to `ev z + h z • w`, for a
distinguished unit vector `w` orthogonal to every `ev z`, has a transfer function: a holomorphic
function of the open unit disc, bounded by one, whose value at `p z` is `h z`.

Writing `P` for the projection killing the `w` direction, `A = P V P` and `B = P (V w)`, the
hypothesis says `(1 - p z A) (ev z) = B`, so `ev z` is the sum of the geometric series
`∑ (p z)^n A^n B`, and the transfer function `D + u ∑ u^n ⟪w, V (A^n B)⟫` reproduces the prescribed
values.  Its bound comes from testing the contraction on `u • v + w` with `v` the same geometric
series.
-/
import GaloisForLFunctions.HTGeometry.BoundedCoeffPowerSeries

noncomputable section

open Filter Metric Topology
open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **The transfer function.**  A contraction interpolating the colligation relations produces a
Schur function of the open unit disc taking the prescribed values. -/
theorem exists_transferFunction {X : Type*} (V : E →L[ℂ] E) (hV : ∀ v, ‖V v‖ ≤ ‖v‖)
    (w : E) (hw : ‖w‖ = 1) (ev : X → E) (p hval : X → ℂ)
    (hperp : ∀ x, ⟪w, ev x⟫_ℂ = 0)
    (hp : ∀ z, ‖p z‖ < 1)
    (hstep : ∀ z, V (p z • ev z + w) = ev z + hval z • w) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball 0 1) ∧
      (∀ u : ℂ, ‖u‖ < 1 → ‖G u‖ ≤ 1) ∧ (∀ z, G (p z) = hval z) := by
  classical
  have hww : ⟪w, w⟫_ℂ = 1 := by
    have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w
    rw [hw] at this
    simpa using this
  -- the projection killing the distinguished direction
  set P : E →L[ℂ] E := ContinuousLinearMap.id ℂ E - (innerSL ℂ w).smulRight w with hPdef
  have hPapp : ∀ v, P v = v - ⟪w, v⟫_ℂ • w := by
    intro v
    simp [hPdef]
  have hwP : ∀ v, ⟪w, P v⟫_ℂ = 0 := by
    intro v
    rw [hPapp, inner_sub_right, inner_smul_right, hww, mul_one, sub_self]
  have hsplit : ∀ v : E, P v + ⟪w, v⟫_ℂ • w = v := by
    intro v
    rw [hPapp]
    abel
  have hpyth : ∀ v : E, ‖v‖ * ‖v‖ = ‖P v‖ * ‖P v‖ + ‖⟪w, v⟫_ℂ‖ * ‖⟪w, v⟫_ℂ‖ := by
    intro v
    have hz : ⟪P v, ⟪w, v⟫_ℂ • w⟫_ℂ = 0 := by
      rw [inner_smul_right]
      have : ⟪P v, w⟫_ℂ = 0 := by
        have := hwP v
        rw [← inner_conj_symm] at this
        simpa using congrArg (starRingEnd ℂ) this
      rw [this, mul_zero]
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P v) (⟪w, v⟫_ℂ • w) hz
    rw [hsplit v, norm_smul, hw, mul_one] at this
    exact this
  have hPnorm : ∀ v : E, ‖P v‖ ≤ ‖v‖ := by
    intro v
    nlinarith [hpyth v, norm_nonneg (P v), norm_nonneg v, norm_nonneg (⟪w, v⟫_ℂ)]
  have hPw : P w = 0 := by rw [hPapp, hww, one_smul, sub_self]
  have hPev : ∀ z, P (ev z) = ev z := by
    intro z
    rw [hPapp, hperp z, zero_smul, sub_zero]
  -- the colligation blocks
  set A : E →L[ℂ] E := P ∘L (V ∘L P) with hAdef
  have hAapp : ∀ v, A v = P (V (P v)) := by intro v; simp [hAdef]
  have hAnorm : ∀ v, ‖A v‖ ≤ ‖v‖ := by
    intro v
    rw [hAapp]
    exact le_trans (hPnorm _) (le_trans (hV _) (hPnorm v))
  set B : E := P (V w) with hBdef
  set D : ℂ := ⟪w, V w⟫_ℂ with hDdef
  have hwB : ⟪w, B⟫_ℂ = 0 := hwP _
  have hwA : ∀ v, ⟪w, A v⟫_ℂ = 0 := by intro v; rw [hAapp]; exact hwP _
  -- the two colligation relations
  have hR1 : ∀ z, p z • A (ev z) + B = ev z := by
    intro z
    have h := congrArg P (hstep z)
    simp only [map_add, map_smul, hPev, hPw, smul_zero, add_zero] at h
    rw [hAapp, hPev z, hBdef]
    exact h
  have hR2 : ∀ z, p z * ⟪w, V (ev z)⟫_ℂ + D = hval z := by
    intro z
    have h := congrArg (fun v => ⟪w, v⟫_ℂ) (hstep z)
    simp only [map_add, map_smul, inner_add_right, inner_smul_right, hperp z, hww,
      mul_one, zero_add] at h
    rw [hDdef]
    exact h
  -- powers of the block
  have hApow : ∀ (n : ℕ) (v : E), ‖(A ^ n) v‖ ≤ ‖v‖ := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ k ih =>
        intro v
        rw [pow_succ]
        have hmul : (A ^ k * A) v = (A ^ k) (A v) := rfl
        rw [hmul]
        exact le_trans (ih (A v)) (hAnorm v)
  set cf : ℕ → ℂ := fun n => ⟪w, V ((A ^ n) B)⟫_ℂ with hcfdef
  have hcf : ∀ n, ‖cf n‖ ≤ ‖B‖ := by
    intro n
    rw [hcfdef]
    calc ‖⟪w, V ((A ^ n) B)⟫_ℂ‖ ≤ ‖w‖ * ‖V ((A ^ n) B)‖ := norm_inner_le_norm _ _
      _ ≤ 1 * ‖B‖ := by
          rw [hw]
          exact mul_le_mul_of_nonneg_left (le_trans (hV _) (hApow n B)) (by norm_num)
      _ = ‖B‖ := one_mul _
  set G : ℂ → ℂ := fun u => D + u * boundedFun cf u with hGdef
  -- the distinguished direction is orthogonal to every iterate
  have hwAB : ∀ n : ℕ, ⟪w, (A ^ n) B⟫_ℂ = 0 := by
    intro n
    cases n with
    | zero => simpa using hwB
    | succ k =>
        have : (A ^ (k + 1)) B = A ((A ^ k) B) := by
          rw [pow_succ']
          rfl
        rw [this]
        exact hwA _
  -- the geometric series of a contraction
  have hsumgeo : ∀ u : ℂ, ‖u‖ < 1 → Summable (fun n => u ^ n • ((A ^ n) B)) := by
    intro u hu
    refine Summable.of_norm_bounded (g := fun n => ‖u‖ ^ n * ‖B‖) ?_ ?_
    · exact (summable_geometric_of_lt_one (norm_nonneg _) hu).mul_right _
    · intro n
      rw [norm_smul, norm_pow]
      exact mul_le_mul_of_nonneg_left (hApow n B) (by positivity)
  have hgeo : ∀ z : X, HasSum (fun n => (p z) ^ n • ((A ^ n) B)) (ev z) := by
    intro z
    have hsum := hsumgeo (p z) (hp z)
    rw [hsum.hasSum_iff_tendsto_nat]
    have htel : ∀ N : ℕ, ev z = (∑ n ∈ Finset.range N, (p z) ^ n • ((A ^ n) B))
        + (p z) ^ N • ((A ^ N) (ev z)) := by
      intro N
      induction N with
      | zero => simp
      | succ k ih =>
          have hstepk : (A ^ k) (ev z) = p z • ((A ^ (k + 1)) (ev z)) + (A ^ k) B := by
            conv_lhs => rw [← hR1 z]
            rw [map_add, map_smul]
            congr 2
          calc ev z
              = (∑ n ∈ Finset.range k, (p z) ^ n • ((A ^ n) B))
                  + (p z) ^ k • ((A ^ k) (ev z)) := ih
            _ = (∑ n ∈ Finset.range (k + 1), (p z) ^ n • ((A ^ n) B))
                  + (p z) ^ (k + 1) • ((A ^ (k + 1)) (ev z)) := by
                rw [Finset.sum_range_succ, hstepk, smul_add, smul_smul, pow_succ]
                module
    have heq : ∀ N : ℕ, (∑ n ∈ Finset.range N, (p z) ^ n • ((A ^ n) B))
        = ev z - (p z) ^ N • ((A ^ N) (ev z)) := fun N => eq_sub_of_add_eq (htel N).symm
    have htail : Filter.Tendsto (fun N : ℕ => (p z) ^ N • ((A ^ N) (ev z))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (g := fun N : ℕ => ‖p z‖ ^ N * ‖ev z‖)
        (fun N => norm_nonneg _) (fun N => ?_) ?_
      · rw [norm_smul, norm_pow]
        exact mul_le_mul_of_nonneg_left (hApow N (ev z)) (by positivity)
      · simpa using
          (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg (p z)) (hp z)).mul_const ‖ev z‖
    have hconst : Filter.Tendsto (fun _ : ℕ => ev z) atTop (𝓝 (ev z)) := tendsto_const_nhds
    have hd := hconst.sub htail
    rw [sub_zero] at hd
    exact hd.congr (fun N => (heq N).symm)
  -- the linear functional reading off the transfer coefficients
  have hLsum : ∀ u : ℂ, ‖u‖ < 1 →
      HasSum (fun n => u ^ n * cf n) (⟪w, V (∑' n, u ^ n • ((A ^ n) B))⟫_ℂ) := by
    intro u hu
    have h := ((innerSL ℂ w).comp V).hasSum ((hsumgeo u hu).hasSum)
    simpa [hcfdef, map_smul, smul_eq_mul] using h
  have hLev : ∀ z : X, HasSum (fun n => (p z) ^ n * cf n) (⟪w, V (ev z)⟫_ℂ) := by
    intro z
    have h := ((innerSL ℂ w).comp V).hasSum (hgeo z)
    simpa [hcfdef, map_smul, smul_eq_mul] using h
  refine ⟨G, ?_, ?_, ?_⟩
  · exact (differentiableOn_const D).add
      (differentiableOn_id.mul (differentiableOn_boundedFun hcf))
  · -- the transfer function is a contraction of the disc
    intro u hu
    set v : E := ∑' n, u ^ n • ((A ^ n) B) with hvdef
    have hsumv := hsumgeo u hu
    have hwv : ⟪w, v⟫_ℂ = 0 := by
      have h : HasSum (fun n => ⟪w, u ^ n • ((A ^ n) B)⟫_ℂ) (⟪w, v⟫_ℂ) := by
        have hh := (innerSL ℂ w).hasSum hsumv.hasSum
        rw [hvdef]
        exact hh
      have h0 : (fun n => ⟪w, u ^ n • ((A ^ n) B)⟫_ℂ) = fun _ : ℕ => (0 : ℂ) := by
        funext n
        rw [inner_smul_right, hwAB n, mul_zero]
      rw [h0] at h
      exact (h.unique hasSum_zero)
    have hPv : P v = v := by rw [hPapp, hwv, zero_smul, sub_zero]
    have hA1 : HasSum (fun n => u ^ n • ((A ^ (n + 1)) B)) (A v) := by
      have h := A.hasSum hsumv.hasSum
      rw [hvdef]
      refine h.congr_fun (fun n => ?_)
      rw [map_smul]
      congr 1
      show (A ^ (n + 1)) B = A ((A ^ n) B)
      rw [pow_succ']
      rfl
    have hAv : ∑' n, u ^ (n + 1) • ((A ^ (n + 1)) B) = u • A v := by
      have h2 := hA1.const_smul (b := u)
      refine (h2.congr_fun (fun n => ?_)).tsum_eq
      rw [smul_smul, ← pow_succ']
    have hrec : v = B + u • A v := by
      rw [← hAv, hvdef, hsumv.tsum_eq_zero_add]
      simp
    have hLv : ⟪w, V v⟫_ℂ = ∑' n, u ^ n * cf n := ((hLsum u hu).tsum_eq).symm
    have hbf : boundedFun cf u = ∑' n, cf n * u ^ n := rfl
    have hGu : G u = D + u * ⟪w, V v⟫_ℂ := by
      show D + u * boundedFun cf u = D + u * ⟪w, V v⟫_ℂ
      rw [hbf, hLv]
      congr 2
      exact tsum_congr (fun n => mul_comm _ _)
    set x : E := u • v + w with hxdef
    have hPVx : P (V x) = v := by
      rw [hxdef, map_add, map_smul, map_add, map_smul]
      rw [show P (V v) = A v by rw [hAapp, hPv], ← hBdef]
      exact (add_comm (u • A v) B).trans hrec.symm
    have hwVx : ⟪w, V x⟫_ℂ = G u := by
      rw [hxdef, map_add, map_smul, inner_add_right, inner_smul_right, hGu, ← hDdef]
      ring
    have hVx : V x = v + G u • w := by
      have := hsplit (V x)
      rw [hPVx, hwVx] at this
      exact this.symm
    have hvw : ⟪v, w⟫_ℂ = 0 := by
      rw [← inner_conj_symm, hwv]
      simp
    have h1 : ‖V x‖ * ‖V x‖ = ‖v‖ * ‖v‖ + ‖G u‖ * ‖G u‖ := by
      have hz : ⟪v, G u • w⟫_ℂ = 0 := by rw [inner_smul_right, hvw, mul_zero]
      have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero v (G u • w) hz
      rw [norm_smul, hw, mul_one] at hpy
      rw [hVx]
      exact hpy
    have h2 : ‖x‖ * ‖x‖ = ‖u‖ * ‖u‖ * (‖v‖ * ‖v‖) + 1 := by
      have hz : ⟪u • v, w⟫_ℂ = 0 := by rw [inner_smul_left, hvw, mul_zero]
      have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (u • v) w hz
      rw [← hxdef, norm_smul, hw] at this
      rw [this]
      ring
    have h3 := hV x
    have h4 : ‖V x‖ * ‖V x‖ ≤ ‖x‖ * ‖x‖ :=
      mul_le_mul h3 h3 (norm_nonneg _) (norm_nonneg _)
    have hnn : 0 ≤ ‖v‖ := norm_nonneg v
    have hun : ‖u‖ * ‖u‖ ≤ 1 := by nlinarith [norm_nonneg u]
    nlinarith [norm_nonneg (G u), h1, h2, h4]
  · intro z
    have h := (hLev z).tsum_eq
    have hbf : boundedFun cf (p z) = ∑' n, cf n * (p z) ^ n := rfl
    have hb : boundedFun cf (p z) = ⟪w, V (ev z)⟫_ℂ := by
      rw [hbf, ← h]
      exact tsum_congr (fun n => mul_comm _ _)
    show D + (p z) * boundedFun cf (p z) = hval z
    rw [hb]
    have h2 := hR2 z
    linear_combination h2

end GaloisForLFunctions.HTGeometry
