import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

/-!
# Trace-norm limits: the Schatten-1 class is closed under limits and the trace passes through

The corpus's Schatten framework (`SchattenApproximation`, `TraceNorm`,
`TraceClassOperatorTrace`) carries approximation numbers, the trace norm, and the bound
`‖opTrace T‖ ≤ traceNorm T`.  This file adds the pieces the pro-nuclear Kähler trace tower's
limit theorem needs:

* `HasRankLE.add` and `approxNumber_add_le` — **Ky Fan subadditivity**:
  `a_{m+n}(S + T) ≤ a_m(S) + a_n(T)`;
* `MemSchattenClass.one_add`, `one_neg`, `one_sub` — the Schatten-1 class is an additive
  group of operators;
* `memSchattenClass_one_of_traceNorm_limit` — a trace-norm limit of Schatten-1 operators is
  Schatten-1;
* `opTrace_tendsto_of_traceNorm_tendsto` — **the trace passes to the limit**:
  `Tr K_a → Tr K` whenever `‖K_a - K‖₁ → 0`;
* `traceTower_limit` — the packaged limit theorem of the trace-tower card: trace-norm
  convergence of the finite Kähler–Riemann stages yields a trace-class limit with converging
  traces.

All unconditional; no spectral, zeta, or positivity input.
-/

namespace RHTower

open ContinuousLinearMap
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Rank bounds add: the sum of a rank-`≤ m` and a rank-`≤ n` operator has rank
`≤ m + n`. -/
theorem HasRankLE.add {F G : H →L[ℂ] H} {m n : ℕ}
    (hF : HasRankLE F m) (hG : HasRankLE G n) : HasRankLE (F + G) (m + n) := by
  obtain ⟨V, hVfd, hVrk, hV⟩ := hF
  obtain ⟨W, hWfd, hWrk, hW⟩ := hG
  refine ⟨V ⊔ W, inferInstance, ?_, fun x => ?_⟩
  · have h := Submodule.finrank_sup_add_finrank_inf_eq V W
    have hnn : 0 ≤ Module.finrank ℂ ↥(V ⊓ W) := Nat.zero_le _
    omega
  · exact Submodule.add_mem_sup (hV x) (hW x)

/-- **Ky Fan subadditivity of approximation numbers**:
`a_{m+n}(S + T) ≤ a_m(S) + a_n(T)`. -/
theorem approxNumber_add_le (S T : H →L[ℂ] H) (m n : ℕ) :
    approxNumber (S + T) (m + n) ≤ approxNumber S m + approxNumber T n := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨F, hFrk, hFlt⟩ := exists_hasRankLE_norm_sub_lt S m
    (by linarith : approxNumber S m < approxNumber S m + ε / 2)
  obtain ⟨G, hGrk, hGlt⟩ := exists_hasRankLE_norm_sub_lt T n
    (by linarith : approxNumber T n < approxNumber T n + ε / 2)
  calc approxNumber (S + T) (m + n)
      ≤ ‖(S + T) - (F + G)‖ :=
        approxNumber_le _ _ _ (hFrk.add hGrk)
    _ = ‖(S - F) + (T - G)‖ := by
          rw [show (S + T) - (F + G) = (S - F) + (T - G) from by abel]
    _ ≤ ‖S - F‖ + ‖T - G‖ := norm_add_le _ _
    _ ≤ approxNumber S m + approxNumber T n + ε := by linarith

/-- Summability of approximation numbers from Schatten-1 membership, in raw form. -/
theorem MemSchattenClass.one_summable {T : H →L[ℂ] H}
    (hT : MemSchattenClass 1 T) : Summable fun n => approxNumber T n := by
  have := hT
  unfold MemSchattenClass at this
  exact this.congr fun n => Real.rpow_one _

/-- Schatten-1 membership from raw summability of the approximation numbers. -/
theorem memSchattenClass_one_of_summable {T : H →L[ℂ] H}
    (hT : Summable fun n => approxNumber T n) : MemSchattenClass 1 T := by
  unfold MemSchattenClass
  exact hT.congr fun n => (Real.rpow_one _).symm

/-- **The Schatten-1 class is closed under addition.** -/
theorem MemSchattenClass.one_add {S T : H →L[ℂ] H}
    (hS : MemSchattenClass 1 S) (hT : MemSchattenClass 1 T) :
    MemSchattenClass 1 (S + T) := by
  apply memSchattenClass_one_of_summable
  have hsum := hS.one_summable.add hT.one_summable
  have heven : Summable fun k => approxNumber (S + T) (2 * k) := by
    apply Summable.of_nonneg_of_le (fun k => approxNumber_nonneg _ _)
      (fun k => ?_) hsum
    have h := approxNumber_add_le S T k k
    calc approxNumber (S + T) (2 * k)
        = approxNumber (S + T) (k + k) := by ring_nf
      _ ≤ approxNumber S k + approxNumber T k := h
  have hodd : Summable fun k => approxNumber (S + T) (2 * k + 1) := by
    apply Summable.of_nonneg_of_le (fun k => approxNumber_nonneg _ _)
      (fun k => ?_) hsum
    calc approxNumber (S + T) (2 * k + 1)
        ≤ approxNumber (S + T) (2 * k) :=
          approxNumber_antitone _ (by omega)
      _ = approxNumber (S + T) (k + k) := by ring_nf
      _ ≤ approxNumber S k + approxNumber T k := approxNumber_add_le S T k k
  exact heven.even_add_odd hodd

/-- The Schatten-1 class is closed under negation. -/
theorem MemSchattenClass.one_neg [CompleteSpace H] {T : H →L[ℂ] H}
    (hT : MemSchattenClass 1 T) : MemSchattenClass 1 (-T) := by
  apply memSchattenClass_one_of_summable
  have h : ∀ n, approxNumber (-T) n = approxNumber T n := by
    intro n
    have hsmul := approxNumber_smul T (-1 : ℂ) n
    rw [neg_one_smul] at hsmul
    rw [hsmul]
    simp
  exact hT.one_summable.congr fun n => (h n).symm

/-- **The Schatten-1 class is closed under subtraction.** -/
theorem MemSchattenClass.one_sub [CompleteSpace H] {S T : H →L[ℂ] H}
    (hS : MemSchattenClass 1 S) (hT : MemSchattenClass 1 T) :
    MemSchattenClass 1 (S - T) := by
  rw [sub_eq_add_neg]
  exact hS.one_add hT.one_neg

/-- **A trace-norm limit of Schatten-1 operators is Schatten-1**: if every stage is
Schatten-1 and every stage differs from `K` by a Schatten-1 operator, then `K` is
Schatten-1. -/
theorem memSchattenClass_one_of_traceNorm_limit [CompleteSpace H]
    {ι : Type*} [Nonempty ι]
    {Ka : ι → H →L[ℂ] H} {K : H →L[ℂ] H}
    (hKa : ∀ a, MemSchattenClass 1 (Ka a))
    (hdiff : ∀ a, MemSchattenClass 1 (Ka a - K)) :
    MemSchattenClass 1 K := by
  obtain ⟨a⟩ := (inferInstance : Nonempty ι)
  have h : K = Ka a - (Ka a - K) := (sub_sub_cancel _ _).symm
  rw [h]
  exact (hKa a).one_sub (hdiff a)

/-- **The trace passes to the limit**: if the stages converge to `K` in trace norm, the
ordinary operator traces converge to the trace of the limit. -/
theorem opTrace_tendsto_of_traceNorm_tendsto [CompleteSpace H] {ι : Type*}
    {l : Filter ι} [l.NeBot] {Ka : ι → H →L[ℂ] H} {K : H →L[ℂ] H}
    (hKa : ∀ a, MemSchattenClass 1 (Ka a))
    (hdiff : ∀ a, MemSchattenClass 1 (Ka a - K))
    (htend : Filter.Tendsto (fun a => traceNorm H (Ka a - K)) l (nhds 0)) :
    Filter.Tendsto (fun a => opTrace (Ka a)) l (nhds (opTrace K)) := by
  haveI : Nonempty ι := Filter.nonempty_of_neBot l
  have hK : MemSchattenClass 1 K :=
    memSchattenClass_one_of_traceNorm_limit hKa hdiff
  rw [← tendsto_sub_nhds_zero_iff]
  apply squeeze_zero_norm (fun a => ?_) htend
  rw [show opTrace (Ka a) - opTrace K = opTrace (Ka a - K) from
    (opTrace_sub_of_memSchattenClass_one (hKa a) hK).symm]
  exact norm_opTrace_le_traceNorm (hdiff a)

/-- **The trace-tower limit theorem** (the abstract half of
`DAC_PRO_NUCLEAR_KAHLER_TRACE_LIMIT`): trace-norm convergence of the finite stages yields a
Schatten-1 limit whose trace is the limit of the stage traces. -/
theorem traceTower_limit [CompleteSpace H] {ι : Type*} {l : Filter ι}
    [l.NeBot] {Ka : ι → H →L[ℂ] H} {K : H →L[ℂ] H}
    (hKa : ∀ a, MemSchattenClass 1 (Ka a))
    (hdiff : ∀ a, MemSchattenClass 1 (Ka a - K))
    (htend : Filter.Tendsto (fun a => traceNorm H (Ka a - K)) l (nhds 0)) :
    MemSchattenClass 1 K ∧
      Filter.Tendsto (fun a => opTrace (Ka a)) l (nhds (opTrace K)) :=
  haveI : Nonempty ι := Filter.nonempty_of_neBot l
  ⟨memSchattenClass_one_of_traceNorm_limit hKa hdiff,
    opTrace_tendsto_of_traceNorm_tendsto hKa hdiff htend⟩

end RHTower
