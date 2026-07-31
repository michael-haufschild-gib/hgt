import GaloisForLFunctions.RHTower.WeakSchattenResidue
import GaloisForLFunctions.HTGeometry.HarmonicResidueTransfer

/-!
# Exact Schatten depth from one critical asymptotic

The endpoint layer of the Schatten calculus asks for two separate inputs: a weak endpoint bound on
the approximation numbers, and the existence of an honest logarithmic limit of the critical energy
— the Connes measurability condition.  Both follow from a single pointwise asymptotic of the
approximation numbers at the critical exponent.

If `(n + 1) · a_n(T)^p → R`, then the weak endpoint bound holds because a convergent sequence is
bounded, and the logarithmic residue exists and equals `R` because logarithmic averaging preserves
limits.  With `R > 0` this determines the Schatten depth of `T` exactly: no class at or below `p`,
every class strictly above `p`.
-/

open Filter Topology Finset

namespace RHTower

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The two logarithmic normalizations `log N` and `log (N + 1)` are asymptotically equal. -/
theorem tendsto_log_div_log_natCast_succ :
    Tendsto (fun N : ℕ => Real.log (N : ℝ) / Real.log ((N : ℝ) + 1)) atTop (nhds 1) := by
  have hL : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1)) atTop atTop := by
    apply Real.tendsto_log_atTop.comp
    exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) - Real.log (N : ℝ))
      atTop (nhds 0) := by
    have h1 : Tendsto (fun N : ℕ => (1 : ℝ) + 1 / (N : ℝ)) atTop (nhds 1) := by
      simpa using tendsto_one_div_atTop_nhds_zero_nat.const_add (1 : ℝ)
    have h2 : Tendsto (fun N : ℕ => Real.log ((1 : ℝ) + 1 / (N : ℝ))) atTop (nhds 0) := by
      have hc := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp h1
      simpa [Function.comp_def] using hc
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    field_simp
  have hratio : Tendsto (fun N : ℕ =>
      (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) / Real.log ((N : ℝ) + 1))
      atTop (nhds 0) := hd.div_atTop hL
  have key : Tendsto (fun N : ℕ =>
      1 - (Real.log ((N : ℝ) + 1) - Real.log (N : ℝ)) / Real.log ((N : ℝ) + 1))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hratio
  refine key.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hNone : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hLpos : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
  field_simp
  ring

/-- A critical asymptotic gives the weak endpoint bound: a convergent sequence is bounded. -/
theorem memWeakSchattenClass_of_tendsto_mul_succ
    {p R : ℝ} {T : H →L[ℂ] H}
    (h : Tendsto (fun n : ℕ => approxNumber T n ^ p * ((n : ℝ) + 1)) atTop (nhds R)) :
    MemWeakSchattenClass p T := by
  obtain ⟨C, hC⟩ := h.bddAbove_range
  refine ⟨max C 0, le_max_right _ _, fun n => ?_⟩
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hle : approxNumber T n ^ p * ((n : ℝ) + 1) ≤ C := hC (Set.mem_range_self n)
  rw [le_div_iff₀ hn]
  exact le_trans hle (le_max_left _ _)

/-- A critical asymptotic gives the logarithmic residue: logarithmic averaging preserves limits,
and the two logarithmic normalizations agree asymptotically. -/
theorem hasSchattenLogResidue_of_tendsto_mul_succ
    {p R : ℝ} {T : H →L[ℂ] H}
    (h : Tendsto (fun n : ℕ => approxNumber T n ^ p * ((n : ℝ) + 1)) atTop (nhds R)) :
    HasSchattenLogResidue p T R := by
  have hlog :=
    GaloisForLFunctions.tendsto_logResidue_of_mul_succ_tendsto
      (a := fun n : ℕ => approxNumber T n ^ p) h
  have hprod := hlog.mul tendsto_log_div_log_natCast_succ
  rw [mul_one] at hprod
  refine hprod.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNtwo : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNlog : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hLpos : 0 < Real.log ((N : ℝ) + 1) := Real.log_pos (by linarith)
  rw [schattenPowerPartialSum]
  field_simp

/-- **Critical asymptotic determines the Schatten depth.**  A single pointwise asymptotic
`(n + 1) · a_n(T)^p → R` with `R > 0` fixes the exact critical depth of `T`: it belongs to no
Schatten class at or below `p`, and to every Schatten class strictly above `p`. -/
theorem exact_schattenDepth_of_tendsto_mul_succ
    {p R : ℝ} (hp : 0 < p) (hR : 0 < R) {T : H →L[ℂ] H}
    (h : Tendsto (fun n : ℕ => approxNumber T n ^ p * ((n : ℝ) + 1)) atTop (nhds R)) :
    (∀ q : ℝ, 0 < q → q ≤ p → ¬ MemSchattenClass q T) ∧
      (∀ q : ℝ, p < q → MemSchattenClass q T) :=
  exact_schattenDepth_of_weak_of_positive_logResidue hp hR
    (memWeakSchattenClass_of_tendsto_mul_succ h)
    (hasSchattenLogResidue_of_tendsto_mul_succ h)

end

end RHTower
