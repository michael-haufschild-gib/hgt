/-
# Power traces are continuous in the Schatten norm

Each telescoping term is a product of exactly `k` Schatten-`p` operators, so the product estimate
applies to it; the trace norm is dominated by the Schatten `p/k` norm because `p/k ≤ 1`; and the
trace is dominated by the trace norm.  Summing the `k` terms leaves a constant times the Schatten
norm of the difference, so every power trace at or above the exponent is continuous.

Main results:
* `traceNorm_telescope_term_le` — **the quantitative telescoping estimate**.
* `norm_opTrace_pow_sub_le_mul` — the whole difference against the Schatten norm.
* `tendsto_opTrace_pow_of_tendsto_schattenNorm` — **the power traces converge**.
-/
import GaloisForLFunctions.HTGeometry.TelescopingPowerTrace
import GaloisForLFunctions.HTGeometry.SchattenNormMonotone

open Filter Topology ContinuousLinearMap

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **The quantitative telescoping estimate.** -/
theorem traceNorm_telescope_term_le {p : ℝ} (hp : 0 < p) {A B : H →L[ℂ] H}
    (hA : MemSchattenClass p A) (hB : MemSchattenClass p B) (hD : MemSchattenClass p (A - B))
    {k j : ℕ} (hj : j < k) (hpk : p ≤ (k : ℝ)) :
    traceNorm H (A ^ j * (A - B) * B ^ (k - 1 - j))
      ≤ schattenProdConst p k
        * ((schattenNorm p A) ^ j
          * (schattenNorm p (A - B) * (schattenNorm p B) ^ (k - 1 - j))) := by
  classical
  set L : List (H →L[ℂ] H) :=
    List.replicate j A ++ (A - B) :: List.replicate (k - 1 - j) B with hLdef
  have hLne : L ≠ [] := by
    rw [hLdef]
    intro hcon
    have := congrArg List.length hcon
    simp at this
  have hmem : ∀ X ∈ L, MemSchattenClass p X := by
    intro X hX
    rw [hLdef, List.mem_append] at hX
    rcases hX with hX | hX
    · rw [List.eq_of_mem_replicate hX]; exact hA
    · rcases List.mem_cons.mp hX with hX | hX
      · rw [hX]; exact hD
      · rw [List.eq_of_mem_replicate hX]; exact hB
  have hlen : L.length = k := by
    rw [hLdef]
    simp only [List.length_append, List.length_replicate, List.length_cons]
    omega
  have hprod : L.prod = A ^ j * (A - B) * B ^ (k - 1 - j) := by
    rw [hLdef, List.prod_append, List.prod_replicate, List.prod_cons, List.prod_replicate,
      mul_assoc]
  have hmapprod : (L.map (schattenNorm p)).prod
      = (schattenNorm p A) ^ j
        * (schattenNorm p (A - B) * (schattenNorm p B) ^ (k - 1 - j)) := by
    rw [hLdef]
    simp only [List.map_append, List.map_replicate, List.map_cons, List.prod_append,
      List.prod_replicate, List.prod_cons]
  have hkR : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le hp hpk
  have hsle : p / (k : ℝ) ≤ 1 := by
    rw [div_le_one hkR]
    exact hpk
  have hspos : 0 < p / (k : ℝ) := div_pos hp hkR
  have hclass : MemSchattenClass (p / (L.length : ℝ)) L.prod :=
    memSchattenClass_list_prod hp L hLne hmem
  rw [hlen] at hclass
  have hstep1 : traceNorm H L.prod ≤ schattenNorm (p / (k : ℝ)) L.prod :=
    traceNorm_le_schattenNorm hspos hsle hclass
  have hstep2 := schattenNorm_list_prod_le hp L hLne hmem
  rw [hlen, hmapprod] at hstep2
  rw [← hprod]
  exact le_trans hstep1 hstep2

/-- The whole power-trace difference against the Schatten norm of the difference. -/
theorem norm_opTrace_pow_sub_le_mul {p : ℝ} (hp : 0 < p) {A B : H →L[ℂ] H}
    (hA : MemSchattenClass p A) (hB : MemSchattenClass p B) (hD : MemSchattenClass p (A - B))
    {k : ℕ} (hk0 : 0 < k) (hpk : p ≤ (k : ℝ)) {C : ℝ} (hCA : schattenNorm p A ≤ C) :
    ‖opTrace (A ^ k) - opTrace (B ^ k)‖
      ≤ (∑ j ∈ Finset.range k,
          schattenProdConst p k * (C ^ j * (schattenNorm p B) ^ (k - 1 - j)))
        * schattenNorm p (A - B) := by
  have hC0 : 0 ≤ C := le_trans (schattenNorm_nonneg p A) hCA
  refine le_trans (norm_opTrace_pow_sub_le hp hA hB hD hk0 hpk) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hjk : j < k := Finset.mem_range.mp hj
  refine le_trans (traceNorm_telescope_term_le hp hA hB hD hjk hpk) ?_
  have hApow : (schattenNorm p A) ^ j ≤ C ^ j :=
    pow_le_pow_left₀ (schattenNorm_nonneg p A) hCA j
  have hrest : 0 ≤ schattenNorm p (A - B) * (schattenNorm p B) ^ (k - 1 - j) :=
    mul_nonneg (schattenNorm_nonneg _ _) (pow_nonneg (schattenNorm_nonneg _ _) _)
  have hinner : (schattenNorm p A) ^ j
        * (schattenNorm p (A - B) * (schattenNorm p B) ^ (k - 1 - j))
      ≤ C ^ j * (schattenNorm p (A - B) * (schattenNorm p B) ^ (k - 1 - j)) :=
    mul_le_mul_of_nonneg_right hApow hrest
  have hmul := mul_le_mul_of_nonneg_left hinner (schattenProdConst_nonneg p k)
  refine le_trans hmul (le_of_eq ?_)
  ring

/-- **The power traces converge.** -/
theorem tendsto_opTrace_pow_of_tendsto_schattenNorm {p : ℝ} (hp : 0 < p)
    {A : ℕ → H →L[ℂ] H} {B : H →L[ℂ] H}
    (hA : ∀ n, MemSchattenClass p (A n)) (hB : MemSchattenClass p B)
    (hD : ∀ n, MemSchattenClass p (A n - B))
    {C : ℝ} (hCA : ∀ n, schattenNorm p (A n) ≤ C)
    (htend : Tendsto (fun n => schattenNorm p (A n - B)) atTop (nhds 0))
    {k : ℕ} (hk0 : 0 < k) (hpk : p ≤ (k : ℝ)) :
    Tendsto (fun n => opTrace ((A n) ^ k)) atTop (nhds (opTrace (B ^ k))) := by
  set K : ℝ := ∑ j ∈ Finset.range k,
    schattenProdConst p k * (C ^ j * (schattenNorm p B) ^ (k - 1 - j)) with hKdef
  have hbound : ∀ n, ‖opTrace ((A n) ^ k) - opTrace (B ^ k)‖
      ≤ K * schattenNorm p (A n - B) :=
    fun n => norm_opTrace_pow_sub_le_mul hp (hA n) hB (hD n) hk0 hpk (hCA n)
  have hzero : Tendsto (fun n => K * schattenNorm p (A n - B)) atTop (nhds 0) := by
    have := htend.const_mul K
    simpa using this
  have hdiff : Tendsto (fun n => opTrace ((A n) ^ k) - opTrace (B ^ k)) atTop (nhds 0) :=
    squeeze_zero_norm hbound hzero
  have hshift := hdiff.add_const (opTrace (B ^ k))
  simpa using hshift

end

end GaloisForLFunctions.HTGeometry
