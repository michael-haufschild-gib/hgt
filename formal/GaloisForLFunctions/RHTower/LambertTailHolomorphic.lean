import GaloisForLFunctions.RHTower.LambertSumHolomorphic

/-!
# The Lambert tail is holomorphic on a growing disc

Dropping the first `N` terms enlarges the disc on which the remaining series is holomorphic: only
`‖u_n‖ ≤ 1/2` for `n ≥ N` is needed, and that holds out to radius `(2π(N+1))^s/2`.  Since those
radii are unbounded in `N`, every point of the plane is interior to some tail's disc of holomorphy,
and the finitely many discarded terms are explicit rational functions.

That is the mechanism of the meromorphic continuation: the transform differs from a holomorphic
function, on each such disc, by a finite sum of rational terms whose poles are the lattice points
already classified.

* `GaloisForLFunctions.RHTower.lambertTermFun`;
* `GaloisForLFunctions.RHTower.differentiableOn_lambertTail`;
* `GaloisForLFunctions.RHTower.exists_index_lambertTail_differentiableOn`.
-/

open Complex Metric

namespace GaloisForLFunctions.RHTower

/-- The `n`-th term of the Lambert series, as a function of `ξ`. -/
noncomputable def lambertTermFun (s α : ℝ) (n : ℕ) (ξ : ℂ) : ℂ :=
  (1 / ((n : ℂ) + 1)) * (lambertVar s ξ n * (Real.sin α : ℂ)
    / (1 + 2 * lambertVar s ξ n * (Real.cos α : ℂ) + (lambertVar s ξ n) ^ 2))

/-- **The tail from index `N` is holomorphic out to radius `(2π(N+1))^s/2`.** -/
theorem differentiableOn_lambertTail {s : ℝ} (hs : 0 < s) (α : ℝ) (N : ℕ) {M : ℝ} (hM0 : 0 < M)
    (hM : M ≤ (2 * Real.pi * ((N : ℝ) + 1)) ^ s / 2) :
    DifferentiableOn ℂ (fun ξ : ℂ => ∑' n : ℕ, lambertTermFun s α (n + N) ξ) (ball (0 : ℂ) M) := by
  classical
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpis : (0 : ℝ) < (2 * Real.pi) ^ s := Real.rpow_pos_of_pos hpi s
  have hNbase : (0 : ℝ) < 2 * Real.pi * ((N : ℝ) + 1) := by positivity
  have hNs : (0 : ℝ) < (2 * Real.pi * ((N : ℝ) + 1)) ^ s := Real.rpow_pos_of_pos hNbase s
  set C : ℝ := M / (2 * Real.pi) ^ s with hCdef
  have hC0 : 0 ≤ C := by positivity
  -- the variables of the tail are small
  have hsmall : ∀ (n : ℕ) (ξ : ℂ), ξ ∈ ball (0 : ℂ) M →
      ‖lambertVar s ξ (n + N)‖ ≤ 1 / 2 := by
    intro n ξ hξ
    have hξM : ‖ξ‖ ≤ M := le_of_lt (by simpa using mem_ball_zero_iff.1 hξ)
    have hmono : (2 * Real.pi * ((N : ℝ) + 1)) ^ s
        ≤ (2 * Real.pi * (((n + N : ℕ) : ℝ) + 1)) ^ s := by
      refine Real.rpow_le_rpow hNbase.le ?_ hs.le
      have : ((N : ℝ)) ≤ ((n + N : ℕ) : ℝ) := by
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) n]
      nlinarith
    have hden : (0 : ℝ) < (2 * Real.pi * (((n + N : ℕ) : ℝ) + 1)) ^ s := by
      refine Real.rpow_pos_of_pos ?_ s
      positivity
    rw [lambertVar, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden,
      div_le_iff₀ hden]
    nlinarith
  -- decay in the running index
  have hdecay : ∀ (n : ℕ) (ξ : ℂ), ξ ∈ ball (0 : ℂ) M →
      ‖lambertVar s ξ (n + N)‖ ≤ C / ((n : ℝ) + 1) ^ s := by
    intro n ξ hξ
    have hξM : ‖ξ‖ ≤ M := le_of_lt (by simpa using mem_ball_zero_iff.1 hξ)
    have hb := norm_lambertVar_le_of_mem_ball hs hξM (n + N)
    refine le_trans hb ?_
    have hle : ((n : ℝ) + 1) ≤ (((n + N : ℕ) : ℝ) + 1) := by
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) N]
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hmono : ((n : ℝ) + 1) ^ s ≤ (((n + N : ℕ) : ℝ) + 1) ^ s :=
      Real.rpow_le_rpow h1.le hle hs.le
    have hp1 : (0 : ℝ) < ((n : ℝ) + 1) ^ s := Real.rpow_pos_of_pos h1 s
    have hp2 : (0 : ℝ) < (((n + N : ℕ) : ℝ) + 1) ^ s :=
      Real.rpow_pos_of_pos (by positivity) s
    rw [div_le_div_iff₀ hp2 hp1]
    nlinarith
  -- the quadratic is bounded below
  have hquad : ∀ (n : ℕ) (ξ : ℂ), ξ ∈ ball (0 : ℂ) M →
      (1 : ℝ) / 4 ≤ ‖1 + 2 * lambertVar s ξ (n + N) * (Real.cos α : ℂ)
        + (lambertVar s ξ (n + N)) ^ 2‖ := by
    intro n ξ hξ
    have hsm := hsmall n ξ hξ
    have hle1 : ‖lambertVar s ξ (n + N)‖ ≤ 1 := by linarith
    have hbase := norm_lambertQuadratic_ge α hle1
    nlinarith [norm_nonneg (lambertVar s ξ (n + N))]
  -- termwise domination
  have hbound : ∀ (n : ℕ) (ξ : ℂ), ξ ∈ ball (0 : ℂ) M →
      ‖lambertTermFun s α (n + N) ξ‖ ≤ 4 * C / ((n : ℝ) + 1) ^ (1 + s) := by
    intro n ξ hξ
    have hb := hdecay n ξ hξ
    have hq := hquad n ξ hξ
    have hqpos : (0 : ℝ) < ‖1 + 2 * lambertVar s ξ (n + N) * (Real.cos α : ℂ)
        + (lambertVar s ξ (n + N)) ^ 2‖ := by linarith
    have hsinle : ‖(Real.sin α : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one _
    have hNpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hMpos : (0 : ℝ) < ((n + N : ℕ) : ℝ) + 1 := by positivity
    have hnormn : ‖(1 : ℂ) / (((n + N : ℕ) : ℂ) + 1)‖ ≤ 1 / ((n : ℝ) + 1) := by
      have hcast : (((n + N : ℕ) : ℂ) + 1) = ((((n + N : ℕ) : ℝ) + 1 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [norm_div, norm_one, hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos]
      have hle : ((n : ℝ) + 1) ≤ (((n + N : ℕ) : ℝ) + 1) := by
        push_cast
        linarith [Nat.cast_nonneg (α := ℝ) N]
      exact one_div_le_one_div_of_le hNpos hle
    have hnum : ‖lambertVar s ξ (n + N) * (Real.sin α : ℂ)‖ ≤ C / ((n : ℝ) + 1) ^ s := by
      calc ‖lambertVar s ξ (n + N) * (Real.sin α : ℂ)‖
          = ‖lambertVar s ξ (n + N)‖ * ‖(Real.sin α : ℂ)‖ := norm_mul _ _
        _ ≤ (C / ((n : ℝ) + 1) ^ s) * 1 :=
            mul_le_mul hb hsinle (norm_nonneg _) (by positivity)
        _ = C / ((n : ℝ) + 1) ^ s := by ring
    have hfrac : ‖lambertVar s ξ (n + N) * (Real.sin α : ℂ)
        / (1 + 2 * lambertVar s ξ (n + N) * (Real.cos α : ℂ) + (lambertVar s ξ (n + N)) ^ 2)‖
        ≤ 4 * (C / ((n : ℝ) + 1) ^ s) := by
      rw [norm_div, div_le_iff₀ hqpos]
      nlinarith [norm_nonneg (lambertVar s ξ (n + N) * (Real.sin α : ℂ))]
    have hps : (0 : ℝ) < ((n : ℝ) + 1) ^ s := Real.rpow_pos_of_pos hNpos s
    calc ‖lambertTermFun s α (n + N) ξ‖
        = ‖(1 : ℂ) / (((n + N : ℕ) : ℂ) + 1)‖ * ‖lambertVar s ξ (n + N) * (Real.sin α : ℂ)
            / (1 + 2 * lambertVar s ξ (n + N) * (Real.cos α : ℂ)
              + (lambertVar s ξ (n + N)) ^ 2)‖ := by
          rw [lambertTermFun, norm_mul]
      _ ≤ (1 / ((n : ℝ) + 1)) * (4 * (C / ((n : ℝ) + 1) ^ s)) := by
          refine mul_le_mul hnormn hfrac (norm_nonneg _) (by positivity)
      _ = 4 * C / ((n : ℝ) + 1) ^ (1 + s) := by
          rw [Real.rpow_add hNpos, Real.rpow_one]
          field_simp
  -- each term is holomorphic
  have hterm : ∀ n : ℕ,
      DifferentiableOn ℂ (fun ξ : ℂ => lambertTermFun s α (n + N) ξ) (ball (0 : ℂ) M) := by
    intro n
    have hvar : DifferentiableOn ℂ (fun ξ : ℂ => lambertVar s ξ (n + N)) (ball (0 : ℂ) M) := by
      unfold lambertVar
      fun_prop
    unfold lambertTermFun
    refine DifferentiableOn.const_mul ?_ _
    refine DifferentiableOn.div (hvar.mul_const _) ?_ ?_
    · exact ((differentiableOn_const 1).add ((hvar.const_mul 2).mul_const _)).add (hvar.pow 2)
    · intro ξ hξ
      have hq := hquad n ξ hξ
      intro hcon
      rw [hcon, norm_zero] at hq
      linarith
  have hu : Summable fun n : ℕ => 4 * C / ((n : ℝ) + 1) ^ (1 + s) := by
    have hbase : Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ (1 + s) :=
      summable_one_div_nat_add_one_rpow (by linarith)
    have hmul := hbase.mul_left (4 * C)
    refine hmul.congr fun n => ?_
    rw [mul_one_div]
  exact differentiableOn_tsum_of_summable_norm hu hterm isOpen_ball
    (fun n w hw => hbound n w hw)

/-- **Every radius is reached by some tail.**  The discs of holomorphy of the tails exhaust the
plane, so the transform continues meromorphically past every lattice point. -/
theorem exists_index_lambertTail_differentiableOn {s : ℝ} (hs : 0 < s) (α : ℝ) {M : ℝ}
    (hM0 : 0 < M) :
    ∃ N : ℕ, DifferentiableOn ℂ (fun ξ : ℂ => ∑' n : ℕ, lambertTermFun s α (n + N) ξ)
      (ball (0 : ℂ) M) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set T : ℝ := (2 * M) ^ (1 / s) with hT
  have hT0 : (0 : ℝ) < T := Real.rpow_pos_of_pos (by positivity) _
  have hTs : T ^ s = 2 * M := by
    rw [hT, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 2 * M), one_div,
      inv_mul_cancel₀ hs.ne', Real.rpow_one]
  obtain ⟨N, hN⟩ := exists_nat_gt (T / (2 * Real.pi))
  refine ⟨N, differentiableOn_lambertTail hs α N hM0 ?_⟩
  have hTle : T ≤ 2 * Real.pi * ((N : ℝ) + 1) := by
    have h1 : T / (2 * Real.pi) < (N : ℝ) := hN
    rw [div_lt_iff₀ hpi] at h1
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hmono : T ^ s ≤ (2 * Real.pi * ((N : ℝ) + 1)) ^ s :=
    Real.rpow_le_rpow hT0.le hTle hs.le
  rw [hTs] at hmono
  linarith

end GaloisForLFunctions.RHTower
