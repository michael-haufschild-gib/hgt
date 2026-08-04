import GaloisForLFunctions.HTGeometry.VolterraLinearIntegralEquation

/-!
# The Volterra equation with a strongly continuous kernel

A propagator group is never continuous in the operator norm, so the kernel of the Duhamel equation of
an evolution problem is not norm continuous either. What it is, is *strongly* continuous: it carries
a continuous curve of vectors to a jointly continuous family. That is all the Picard iteration
consumes — the kernel is only ever applied to the iterates, which are continuous by construction.

This file re-runs the perturbation series under that weaker hypothesis. The bounds are unchanged: the
`n`-th increment is still at most `F Mⁿ |t|ⁿ / n!`, so existence, uniqueness, continuity and the
exponential bound all hold with no smallness hypothesis. A norm continuous kernel is strongly
continuous, so nothing is lost.
-/

namespace GaloisForLFunctions.HTGeometry

open Set MeasureTheory intervalIntegral

open scoped Interval

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A kernel is **strongly continuous** if it carries every continuous curve of vectors to a jointly
continuous family. -/
def StrongKernel (K : ℝ → ℝ → X →L[ℝ] X) : Prop :=
  ∀ u : ℝ → X, Continuous u → Continuous fun p : ℝ × ℝ => K p.1 p.2 (u p.2)

/-- A kernel continuous in the operator norm is strongly continuous. -/
theorem StrongKernel.of_continuous {K : ℝ → ℝ → X →L[ℝ] X}
    (hK : Continuous fun p : ℝ × ℝ => K p.1 p.2) : StrongKernel K :=
  fun _u hu => continuous_apply_pair hK hu

theorem continuous_volterraIterate_of_strong {f : ℝ → X} {K : ℝ → ℝ → X →L[ℝ] X}
    (hf : Continuous f) (hK : StrongKernel K) (n : ℕ) :
    Continuous (volterraIterate f K n) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    have hint : Continuous fun t : ℝ =>
        ∫ s in (0 : ℝ)..t, K t s (volterraIterate f K n s) := by
      refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (t : ℝ) (s : ℝ) => K t s (volterraIterate f K n s))
        (hK _ ih) continuous_id
    exact hf.add hint

/-- **The Picard increments decay factorially.** -/
theorem norm_volterraIterate_succ_sub_le_of_strong {f : ℝ → X} {K : ℝ → ℝ → X →L[ℝ] X} {M F : ℝ}
    (hf : Continuous f) (hK : StrongKernel K)
    (hM : 0 ≤ M) (hF : 0 ≤ F) (hKb : ∀ t s : ℝ, ‖K t s‖ ≤ M) (hfb : ∀ t : ℝ, ‖f t‖ ≤ F) :
    ∀ (n : ℕ) (t : ℝ),
      ‖volterraIterate f K (n + 1) t - volterraIterate f K n t‖
        ≤ F * M ^ (n + 1) * |t| ^ (n + 1) / (n + 1).factorial := by
  intro n
  induction n with
  | zero =>
    intro t
    have hdiff : volterraIterate f K 1 t - volterraIterate f K 0 t
        = ∫ s in (0 : ℝ)..t, K t s (f s) := by
      rw [volterraIterate_succ, volterraIterate_zero]
      abel
    have hbound : ∀ s ∈ Ι (0 : ℝ) t, ‖K t s (f s)‖ ≤ F * M * |s| ^ 0 := by
      intro s _
      have h1 : ‖K t s (f s)‖ ≤ ‖K t s‖ * ‖f s‖ := (K t s).le_opNorm (f s)
      have h2 : ‖K t s‖ * ‖f s‖ ≤ M * F :=
        mul_le_mul (hKb t s) (hfb s) (norm_nonneg _) hM
      calc ‖K t s (f s)‖ ≤ M * F := le_trans h1 h2
        _ = F * M * |s| ^ 0 := by ring
    have hcont : Continuous fun s : ℝ => K t s (f s) := by
      have := hK _ hf
      exact this.comp (continuous_const.prodMk continuous_id)
    have hle := norm_integral_le_abs_of_norm_le (a := (0 : ℝ)) (b := t)
      (f := fun s => K t s (f s)) (g := fun s => F * M * |s| ^ 0)
      (hcont.norm.intervalIntegrable 0 t)
      ((continuous_const.mul ((continuous_abs.pow 0))).intervalIntegrable 0 t) hbound
    rw [hdiff]
    refine le_trans hle ?_
    have hval : (∫ s in (0 : ℝ)..t, F * M * |s| ^ 0) = F * M * ∫ s in (0 : ℝ)..t, |s| ^ 0 := by
      rw [intervalIntegral.integral_const_mul]
    rw [hval, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ F * M), abs_integral_abs_pow]
    simp
  | succ n ih =>
    intro t
    have hIA : IntervalIntegrable (fun s : ℝ => K t s (volterraIterate f K (n + 1) s))
        volume 0 t :=
      ((hK _ (continuous_volterraIterate_of_strong hf hK (n + 1))).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t
    have hIB : IntervalIntegrable (fun s : ℝ => K t s (volterraIterate f K n s)) volume 0 t :=
      ((hK _ (continuous_volterraIterate_of_strong hf hK n)).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t
    have hdiff : volterraIterate f K (n + 2) t - volterraIterate f K (n + 1) t
        = ∫ s in (0 : ℝ)..t,
          K t s (volterraIterate f K (n + 1) s - volterraIterate f K n s) := by
      rw [volterraIterate_succ, volterraIterate_succ (n := n), add_sub_add_left_eq_sub,
        ← intervalIntegral.integral_sub hIA hIB]
      refine intervalIntegral.integral_congr fun s _ => ?_
      rw [map_sub]
    set c : ℝ := F * M ^ (n + 2) / (n + 1).factorial with hc
    have hc0 : 0 ≤ c := by
      rw [hc]
      have : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
      positivity
    have hbound : ∀ s ∈ Ι (0 : ℝ) t,
        ‖K t s (volterraIterate f K (n + 1) s - volterraIterate f K n s)‖
          ≤ c * |s| ^ (n + 1) := by
      intro s _
      have h1 : ‖K t s (volterraIterate f K (n + 1) s - volterraIterate f K n s)‖
          ≤ ‖K t s‖ * ‖volterraIterate f K (n + 1) s - volterraIterate f K n s‖ :=
        (K t s).le_opNorm _
      have h2 := ih s
      have hfac : (0 : ℝ) < (n + 1).factorial := by exact_mod_cast Nat.factorial_pos (n + 1)
      calc ‖K t s (volterraIterate f K (n + 1) s - volterraIterate f K n s)‖
          ≤ ‖K t s‖ * ‖volterraIterate f K (n + 1) s - volterraIterate f K n s‖ := h1
        _ ≤ M * (F * M ^ (n + 1) * |s| ^ (n + 1) / (n + 1).factorial) := by
            refine mul_le_mul (hKb t s) h2 (norm_nonneg _) hM
        _ = c * |s| ^ (n + 1) := by
            rw [hc]
            field_simp
            ring
    have hcont : Continuous fun s : ℝ =>
        K t s (volterraIterate f K (n + 1) s - volterraIterate f K n s) := by
      have hu : Continuous fun s : ℝ =>
          volterraIterate f K (n + 1) s - volterraIterate f K n s :=
        (continuous_volterraIterate_of_strong hf hK (n + 1)).sub (continuous_volterraIterate_of_strong hf hK n)
      exact (hK _ hu).comp (continuous_const.prodMk continuous_id)
    have hle := norm_integral_le_abs_of_norm_le (a := (0 : ℝ)) (b := t)
      (f := fun s => K t s (volterraIterate f K (n + 1) s - volterraIterate f K n s))
      (g := fun s => c * |s| ^ (n + 1)) (hcont.norm.intervalIntegrable 0 t)
      ((continuous_const.mul ((continuous_abs.pow (n + 1)))).intervalIntegrable 0 t) hbound
    rw [hdiff]
    refine le_trans hle ?_
    have hval : (∫ s in (0 : ℝ)..t, c * |s| ^ (n + 1))
        = c * ∫ s in (0 : ℝ)..t, |s| ^ (n + 1) := by
      rw [intervalIntegral.integral_const_mul]
    rw [hval, abs_mul, abs_of_nonneg hc0, abs_integral_abs_pow, hc]
    refine le_of_eq ?_
    have hfacpos : (0 : ℝ) < ((n + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (n + 1)
    have hfac2 : ((n + 1 + 1).factorial : ℝ) = ((n : ℝ) + 1 + 1) * ((n + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    rw [hfac2]
    push_cast
    field_simp

/-- **The Picard increments are summable at every time.** -/
theorem summable_volterraIncrements_of_strong [CompleteSpace X] {f : ℝ → X} {K : ℝ → ℝ → X →L[ℝ] X}
    {M F : ℝ}
    (hf : Continuous f) (hK : StrongKernel K)
    (hM : 0 ≤ M) (hF : 0 ≤ F) (hKb : ∀ t s : ℝ, ‖K t s‖ ≤ M) (hfb : ∀ t : ℝ, ‖f t‖ ≤ F)
    (t : ℝ) :
    Summable fun n : ℕ => volterraIterate f K (n + 1) t - volterraIterate f K n t :=
  Summable.of_norm_bounded (summable_volterraBound (M := M) (T := |t|) hF)
    fun n => norm_volterraIterate_succ_sub_le_of_strong hf hK hM hF hKb hfb n t

/-- **The Picard iterates converge to the solution.** -/
theorem tendsto_volterraIterate_of_strong [CompleteSpace X] {f : ℝ → X} {K : ℝ → ℝ → X →L[ℝ] X}
    {M F : ℝ}
    (hf : Continuous f) (hK : StrongKernel K)
    (hM : 0 ≤ M) (hF : 0 ≤ F) (hKb : ∀ t s : ℝ, ‖K t s‖ ≤ M) (hfb : ∀ t : ℝ, ‖f t‖ ≤ F)
    (t : ℝ) :
    Filter.Tendsto (fun n => volterraIterate f K n t) Filter.atTop
      (nhds (volterraSolution f K t)) := by
  have hsum := (summable_volterraIncrements_of_strong hf hK hM hF hKb hfb t).hasSum
  have hbase := hsum.tendsto_sum_nat.const_add (f t)
  refine hbase.congr fun N => ?_
  rw [Finset.sum_range_sub (fun n => volterraIterate f K n t), volterraIterate_zero]
  abel

/-- **The solution is continuous.** -/
theorem continuous_volterraSolution_of_strong [CompleteSpace X] {f : ℝ → X} {K : ℝ → ℝ → X →L[ℝ] X}
    {M F : ℝ}
    (hf : Continuous f) (hK : StrongKernel K)
    (hM : 0 ≤ M) (hF : 0 ≤ F) (hKb : ∀ t s : ℝ, ‖K t s‖ ≤ M) (hfb : ∀ t : ℝ, ‖f t‖ ≤ F) :
    Continuous (volterraSolution f K) := by
  refine continuous_iff_continuousAt.mpr fun t₀ => ?_
  set T : ℝ := |t₀| + 1 with hT
  have hTpos : 0 < T := by
    rw [hT]
    positivity
  have hopen : IsOpen {t : ℝ | |t| < T} := isOpen_lt continuous_abs continuous_const
  have hmem : t₀ ∈ {t : ℝ | |t| < T} := by
    rw [Set.mem_setOf_eq, hT]
    linarith
  have hcontOn : ContinuousOn (volterraSolution f K) {t : ℝ | |t| < T} := by
    refine ContinuousOn.add hf.continuousOn ?_
    refine continuousOn_tsum
      (fun n => ((continuous_volterraIterate_of_strong hf hK (n + 1)).sub
        (continuous_volterraIterate_of_strong hf hK n)).continuousOn)
      (summable_volterraBound (M := M) (T := T) hF) ?_
    intro n t ht
    refine le_trans (norm_volterraIterate_succ_sub_le_of_strong hf hK hM hF hKb hfb n t) ?_
    have habs : |t| ≤ T := le_of_lt ht
    have hfac : (0 : ℝ) < ((n + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_pos (n + 1)
    have hmono : |t| ^ (n + 1) ≤ T ^ (n + 1) := pow_le_pow_left₀ (abs_nonneg t) habs (n + 1)
    have hcoef : (0 : ℝ) ≤ F * M ^ (n + 1) := mul_nonneg hF (pow_nonneg hM _)
    have hnum : F * M ^ (n + 1) * |t| ^ (n + 1) ≤ F * M ^ (n + 1) * T ^ (n + 1) :=
      mul_le_mul_of_nonneg_left hmono hcoef
    calc F * M ^ (n + 1) * |t| ^ (n + 1) / ((n + 1).factorial : ℝ)
        = F * M ^ (n + 1) * |t| ^ (n + 1) * (((n + 1).factorial : ℝ))⁻¹ := by
          rw [div_eq_mul_inv]
      _ ≤ F * M ^ (n + 1) * T ^ (n + 1) * (((n + 1).factorial : ℝ))⁻¹ :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = F * M ^ (n + 1) * T ^ (n + 1) / ((n + 1).factorial : ℝ) := by rw [div_eq_mul_inv]
  exact hcontOn.continuousAt (hopen.mem_nhds hmem)

/-- The Picard iterates are bounded uniformly in the index, by the exponential of the kernel
bound. -/
theorem norm_volterraIterate_le_of_strong {f : ℝ → X} {K : ℝ → ℝ → X →L[ℝ] X} {M F : ℝ}
    (hf : Continuous f) (hK : StrongKernel K)
    (hM : 0 ≤ M) (hF : 0 ≤ F) (hKb : ∀ t s : ℝ, ‖K t s‖ ≤ M) (hfb : ∀ t : ℝ, ‖f t‖ ≤ F)
    (n : ℕ) (t : ℝ) : ‖volterraIterate f K n t‖ ≤ F * Real.exp (M * |t|) := by
  have htel : volterraIterate f K n t
      = f t + ∑ m ∈ Finset.range n,
        (volterraIterate f K (m + 1) t - volterraIterate f K m t) := by
    rw [Finset.sum_range_sub (fun m => volterraIterate f K m t), volterraIterate_zero]
    abel
  have hterm : ∀ m ∈ Finset.range n,
      ‖volterraIterate f K (m + 1) t - volterraIterate f K m t‖
        ≤ F * ((M * |t|) ^ (m + 1) / ((m + 1).factorial : ℝ)) := by
    intro m _
    have hEq : F * M ^ (m + 1) * |t| ^ (m + 1) / ((m + 1).factorial : ℝ)
        = F * ((M * |t|) ^ (m + 1) / ((m + 1).factorial : ℝ)) := by
      rw [mul_pow]
      ring
    exact le_of_le_of_eq (norm_volterraIterate_succ_sub_le_of_strong hf hK hM hF hKb hfb m t) hEq
  have hsum : ‖∑ m ∈ Finset.range n,
      (volterraIterate f K (m + 1) t - volterraIterate f K m t)‖
      ≤ ∑ m ∈ Finset.range n, F * ((M * |t|) ^ (m + 1) / ((m + 1).factorial : ℝ)) :=
    le_trans (norm_sum_le _ _) (Finset.sum_le_sum hterm)
  have hshift : F + ∑ m ∈ Finset.range n,
      F * ((M * |t|) ^ (m + 1) / ((m + 1).factorial : ℝ))
      = F * ∑ j ∈ Finset.range (n + 1), (M * |t|) ^ j / (j.factorial : ℝ) := by
    rw [Finset.sum_range_succ' (fun j => (M * |t|) ^ j / (j.factorial : ℝ)) n, mul_add,
      Finset.mul_sum]
    simp [add_comm]
  have hx : (0 : ℝ) ≤ M * |t| := mul_nonneg hM (abs_nonneg t)
  have hexp := Real.sum_le_exp_of_nonneg hx (n + 1)
  calc ‖volterraIterate f K n t‖
      = ‖f t + ∑ m ∈ Finset.range n,
        (volterraIterate f K (m + 1) t - volterraIterate f K m t)‖ := by rw [htel]
    _ ≤ ‖f t‖ + ‖∑ m ∈ Finset.range n,
        (volterraIterate f K (m + 1) t - volterraIterate f K m t)‖ := norm_add_le _ _
    _ ≤ F + ∑ m ∈ Finset.range n, F * ((M * |t|) ^ (m + 1) / ((m + 1).factorial : ℝ)) :=
        add_le_add (hfb t) hsum
    _ = F * ∑ j ∈ Finset.range (n + 1), (M * |t|) ^ j / (j.factorial : ℝ) := hshift
    _ ≤ F * Real.exp (M * |t|) := mul_le_mul_of_nonneg_left hexp hF

/-- **The solution satisfies the Volterra equation.** -/
theorem volterraSolution_eq_of_strong [CompleteSpace X] {f : ℝ → X} {K : ℝ → ℝ → X →L[ℝ] X} {M F : ℝ}
    (hf : Continuous f) (hK : StrongKernel K)
    (hM : 0 ≤ M) (hF : 0 ≤ F) (hKb : ∀ t s : ℝ, ‖K t s‖ ≤ M) (hfb : ∀ t : ℝ, ‖f t‖ ≤ F)
    (t : ℝ) :
    volterraSolution f K t
      = f t + ∫ s in (0 : ℝ)..t, K t s (volterraSolution f K s) := by
  have hcontSol := continuous_volterraSolution_of_strong hf hK hM hF hKb hfb
  set C : ℝ := M * (F * Real.exp (M * |t|)) with hC
  have hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun s => K t s (volterraIterate f K n s)) (volume.restrict (Set.uIoc 0 t)) := fun n =>
    ((hK _ (continuous_volterraIterate_of_strong hf hK n)).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hdom : ∀ n : ℕ, ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      ‖K t s (volterraIterate f K n s)‖ ≤ C := by
    intro n
    filter_upwards with s hs
    have habs : |s| ≤ |t| := abs_le_abs_of_mem_uIoc_zero hs
    have h1 : ‖K t s (volterraIterate f K n s)‖ ≤ ‖K t s‖ * ‖volterraIterate f K n s‖ :=
      (K t s).le_opNorm _
    have h2 : ‖volterraIterate f K n s‖ ≤ F * Real.exp (M * |t|) := by
      refine le_trans (norm_volterraIterate_le_of_strong hf hK hM hF hKb hfb n s) ?_
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hM)) hF
    exact le_trans h1 (mul_le_mul (hKb t s) h2 (norm_nonneg _) hM)
  have hptw : ∀ᵐ s : ℝ, s ∈ Set.uIoc 0 t →
      Filter.Tendsto (fun n => K t s (volterraIterate f K n s)) Filter.atTop
        (nhds (K t s (volterraSolution f K s))) := by
    filter_upwards with s _
    exact ((K t s).continuous.tendsto _).comp
      (tendsto_volterraIterate_of_strong hf hK hM hF hKb hfb s)
  have hint := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun _ : ℝ => C) (l := Filter.atTop)
    (Filter.Eventually.of_forall hmeas) (Filter.Eventually.of_forall hdom)
    intervalIntegrable_const hptw
  have hlhs : Filter.Tendsto (fun n => volterraIterate f K (n + 1) t) Filter.atTop
      (nhds (volterraSolution f K t)) :=
    (tendsto_volterraIterate_of_strong hf hK hM hF hKb hfb t).comp (Filter.tendsto_add_atTop_nat 1)
  have hshape : Filter.Tendsto
      (fun n => f t + ∫ s in (0 : ℝ)..t, K t s (volterraIterate f K n s)) Filter.atTop
      (nhds (volterraSolution f K t)) :=
    hlhs.congr fun n => volterraIterate_succ f K n t
  exact tendsto_nhds_unique hshape (hint.const_add (f t))

/-- **The Volterra equation has at most one continuous solution.** The difference of two solutions
is bounded by `W (M|t|)ⁿ/n!` for every `n`, and the factorial wins. -/
theorem volterra_eq_of_eq_of_eq_of_strong {f : ℝ → X} {K : ℝ → ℝ → X →L[ℝ] X} {M : ℝ}
    (hK : StrongKernel K) (hM : 0 ≤ M)
    (hKb : ∀ t s : ℝ, ‖K t s‖ ≤ M) {u v : ℝ → X} (hu : Continuous u) (hv : Continuous v)
    (heu : ∀ t : ℝ, u t = f t + ∫ s in (0 : ℝ)..t, K t s (u s))
    (hev : ∀ t : ℝ, v t = f t + ∫ s in (0 : ℝ)..t, K t s (v s)) : u = v := by
  funext t₀
  set w : ℝ → X := fun t => u t - v t with hw
  have hwc : Continuous w := hu.sub hv
  have hweq : ∀ t : ℝ, w t = ∫ s in (0 : ℝ)..t, K t s (w s) := by
    intro t
    have hIu : IntervalIntegrable (fun s : ℝ => K t s (u s)) volume 0 t :=
      ((hK _ hu).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t
    have hIv : IntervalIntegrable (fun s : ℝ => K t s (v s)) volume 0 t :=
      ((hK _ hv).comp
        (continuous_const.prodMk continuous_id)).intervalIntegrable 0 t
    show u t - v t = ∫ s in (0 : ℝ)..t, K t s (u s - v s)
    rw [heu t, hev t, add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub hIu hIv]
    refine intervalIntegral.integral_congr fun s _ => ?_
    rw [← map_sub]
  set T : ℝ := |t₀| with hT
  have hTnn : 0 ≤ T := abs_nonneg t₀
  obtain ⟨W, hW⟩ := (isCompact_Icc (a := -T) (b := T)).exists_bound_of_continuousOn
    hwc.continuousOn
  have hW0 : 0 ≤ W := le_trans (norm_nonneg (w 0)) (hW 0 ⟨by linarith, hTnn⟩)
  have hstep : ∀ (n : ℕ) (r : ℝ), r ∈ Set.Icc (-T) T →
      ‖w r‖ ≤ W * (M * |r|) ^ n / (n.factorial : ℝ) := by
    intro n
    induction n with
    | zero =>
      intro r hr
      simpa using hW r hr
    | succ n ih =>
      intro r hr
      have hsub : ∀ s ∈ Set.uIoc (0 : ℝ) r, ‖K r s (w s)‖
          ≤ (M * (W * M ^ n / (n.factorial : ℝ))) * |s| ^ n := by
        intro s hs
        have habs : |s| ≤ |r| := abs_le_abs_of_mem_uIoc_zero hs
        have hrT : |r| ≤ T := abs_le.mpr ⟨hr.1, hr.2⟩
        have hsT : |s| ≤ T := le_trans habs hrT
        have hmem : s ∈ Set.Icc (-T) T := abs_le.mp hsT
        have h1 : ‖K r s (w s)‖ ≤ ‖K r s‖ * ‖w s‖ := (K r s).le_opNorm _
        have h2 := ih s hmem
        have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
        calc ‖K r s (w s)‖ ≤ ‖K r s‖ * ‖w s‖ := h1
          _ ≤ M * (W * (M * |s|) ^ n / (n.factorial : ℝ)) :=
              mul_le_mul (hKb r s) h2 (norm_nonneg _) hM
          _ = (M * (W * M ^ n / (n.factorial : ℝ))) * |s| ^ n := by
              rw [mul_pow]
              field_simp
      have hcont : Continuous fun s : ℝ => K r s (w s) :=
        (hK _ hwc).comp (continuous_const.prodMk continuous_id)
      have hle := norm_integral_le_abs_of_norm_le (a := (0 : ℝ)) (b := r)
        (f := fun s => K r s (w s))
        (g := fun s => (M * (W * M ^ n / (n.factorial : ℝ))) * |s| ^ n)
        (hcont.norm.intervalIntegrable 0 r)
        ((continuous_const.mul (continuous_abs.pow n)).intervalIntegrable 0 r) hsub
      rw [hweq r]
      refine le_trans hle ?_
      have hval : (∫ s in (0 : ℝ)..r, (M * (W * M ^ n / (n.factorial : ℝ))) * |s| ^ n)
          = (M * (W * M ^ n / (n.factorial : ℝ))) * ∫ s in (0 : ℝ)..r, |s| ^ n := by
        rw [intervalIntegral.integral_const_mul]
      have hc0 : (0 : ℝ) ≤ M * (W * M ^ n / (n.factorial : ℝ)) := by
        have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
        positivity
      rw [hval, abs_mul, abs_of_nonneg hc0, abs_integral_abs_pow]
      refine le_of_eq ?_
      have hfacpos : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
      have hfac2 : ((n + 1).factorial : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hfac2, mul_pow]
      field_simp
      ring
  have hzero : ‖w t₀‖ ≤ 0 := by
    have hmem : t₀ ∈ Set.Icc (-T) T := abs_le.mp (le_refl |t₀|)
    have hlim : Filter.Tendsto (fun n : ℕ => W * (M * |t₀|) ^ n / (n.factorial : ℝ))
        Filter.atTop (nhds 0) := by
      have hsummable : Summable fun n : ℕ => W * ((M * |t₀|) ^ n / (n.factorial : ℝ)) :=
        (Real.summable_pow_div_factorial (M * |t₀|)).mul_left W
      simpa [mul_div_assoc] using hsummable.tendsto_atTop_zero
    refine ge_of_tendsto hlim ?_
    filter_upwards with n
    exact hstep n t₀ hmem
  have : w t₀ = 0 := by
    have := norm_le_zero_iff.mp hzero
    exact this
  rw [hw] at this
  exact sub_eq_zero.mp this

/-- **The solution obeys the same exponential bound as the iterates.** -/
theorem norm_volterraSolution_le_of_strong [CompleteSpace X] {f : ℝ → X} {K : ℝ → ℝ → X →L[ℝ] X} {M F : ℝ}
    (hf : Continuous f) (hK : StrongKernel K)
    (hM : 0 ≤ M) (hF : 0 ≤ F) (hKb : ∀ t s : ℝ, ‖K t s‖ ≤ M) (hfb : ∀ t : ℝ, ‖f t‖ ≤ F)
    (t : ℝ) : ‖volterraSolution f K t‖ ≤ F * Real.exp (M * |t|) := by
  have htend := (tendsto_volterraIterate_of_strong hf hK hM hF hKb hfb t).norm
  refine le_of_tendsto htend ?_
  filter_upwards with n
  exact norm_volterraIterate_le_of_strong hf hK hM hF hKb hfb n t

end GaloisForLFunctions.HTGeometry
