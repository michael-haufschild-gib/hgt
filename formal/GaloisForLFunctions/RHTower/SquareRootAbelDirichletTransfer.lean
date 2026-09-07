import GaloisForLFunctions.RHTower.SquareRootAbelDirichletContinuation
import Mathlib.NumberTheory.LSeries.Basic

/-!
# Exact transfer from square-root Abel means to Dirichlet continuation

Two finite Abel summations give the explicit candidate series and two boundary
terms. Linear weighted-prefix growth makes those terms vanish on a safe
half-plane, identifying the candidate with the literal L-series.
-/

noncomputable section
open Filter Topology Finset
namespace RHTower
open GaloisForLFunctions.RHTower

/-- The square-root weighted prefix of the summatory coefficients. -/
def squareRootAbelPrefix (g : ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ k ∈ Icc 1 N, ((Real.sqrt ((k:ℝ)+1)-Real.sqrt k:ℝ):ℂ)*∑ n ∈ Icc 1 k, g n

/-- The exact next weighted-prefix increment. -/
theorem squareRootAbelPrefix_succ (g : ℕ → ℂ) (N : ℕ) :
    squareRootAbelPrefix g (N+1) = squareRootAbelPrefix g N +
      ((Real.sqrt ((N:ℝ)+2)-Real.sqrt ((N:ℝ)+1):ℝ):ℂ)*∑ n ∈ Icc 1 (N+1), g n := by
  unfold squareRootAbelPrefix
  rw [sum_Icc_succ_top (by omega : 1 ≤ N+1)]
  push_cast
  ring_nf

/-- Recover the summatory coefficients by cancelling the square-root increment. -/
theorem sum_eq_clock_mul_squareRootAbelPrefix_step (g : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ Icc 1 (N+1), g n) =
      (squareRootAbelReciprocalClock ((N:ℝ)+1):ℂ)*
        (squareRootAbelPrefix g (N+1)-squareRootAbelPrefix g N) := by
  rw [squareRootAbelPrefix_succ,add_sub_cancel_left]
  have hc := squareRootAbelReciprocalClock_mul_step (by positivity : 0 ≤ (N:ℝ)+1)
  rw [show (N:ℝ)+1+1=(N:ℝ)+2 by ring] at hc
  rw [← mul_assoc,← Complex.ofReal_mul,hc,Complex.ofReal_one,one_mul]

/-- Exact two-stage Abel identity, including both finite boundary terms. -/
theorem sum_dirichlet_eq_squareRootAbel (g : ℕ → ℂ) (s : ℂ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, g n*(n:ℂ)^(-s)) =
      (∑ n ∈ Icc 1 N, g n)*((N:ℂ)+1)^(-s) +
      squareRootAbelPrefix g N*squareRootAbelDirichletKernel ((N:ℝ)+1) s +
      ∑ n ∈ range N, squareRootAbelDirichletTerm (squareRootAbelPrefix g) n s := by
  have hfirst := HTGeometry.sum_mul_eq_partial_mul_diff_ring g (fun n => (n:ℂ)^(-s)) N
  have hreplace : (∑ m ∈ Icc 1 N,
      (∑ k ∈ Icc 1 m, g k)*((m:ℂ)^(-s)-((m+1:ℕ):ℂ)^(-s))) =
      ∑ m ∈ Icc 1 N,
        (((Real.sqrt ((m:ℝ)+1)-Real.sqrt m:ℝ):ℂ)*∑ k ∈ Icc 1 m,g k)*
          squareRootAbelDirichletKernel m s := by
    apply sum_congr rfl
    intro m hm
    have hc := squareRootAbelReciprocalClock_mul_step (Nat.cast_nonneg (α := ℝ) m)
    have hcc : (squareRootAbelReciprocalClock m:ℂ)*
        ((Real.sqrt ((m:ℝ)+1)-Real.sqrt m:ℝ):ℂ)=1 := by exact_mod_cast hc
    unfold squareRootAbelDirichletKernel
    push_cast
    calc
      _ = ((squareRootAbelReciprocalClock m:ℂ)*
          ((Real.sqrt ((m:ℝ)+1):ℂ)-(Real.sqrt (m:ℝ):ℂ)))*
          (∑ k ∈ Icc 1 m,g k)*((m:ℂ)^(-s)-((m:ℂ)+1)^(-s)) := by
        rw [← Complex.ofReal_sub,hcc,one_mul]
      _ = _ := by ring
  rw [hreplace] at hfirst
  have hsecond := HTGeometry.sum_mul_eq_partial_mul_diff_ring
    (fun m => (((Real.sqrt ((m:ℝ)+1)-Real.sqrt m:ℝ):ℂ)*∑ k ∈ Icc 1 m,g k))
    (fun m => squareRootAbelDirichletKernel m s) N
  rw [hsecond] at hfirst
  have hsum : (∑ n ∈ range N, squareRootAbelDirichletTerm (squareRootAbelPrefix g) n s) =
      ∑ m ∈ Icc 1 N, squareRootAbelPrefix g m*
        (squareRootAbelDirichletKernel m s-squareRootAbelDirichletKernel (m+1:ℕ) s) := by
    rw [← Ico_add_one_right_eq_Icc,sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_right,squareRootAbelDirichletTerm,Nat.add_comm 1]
    apply sum_congr rfl
    intro n hn
    push_cast
    ring_nf
  rw [hsum]
  simpa only [squareRootAbelPrefix,Nat.cast_add,Nat.cast_one,add_assoc,add_comm,add_left_comm]
    using hfirst

/-- Linear weighted-prefix growth bounds the original summatory coefficients. -/
theorem norm_sum_le_of_squareRootAbelPrefix_bound {g : ℕ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ n, ‖squareRootAbelPrefix g n‖ ≤ C*((n:ℝ)+1)) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N,g n‖ ≤ 6*C*((N:ℝ)+1)^((3:ℝ)/2) := by
  cases N with
  | zero => simp; positivity
  | succ N =>
    rw [sum_eq_clock_mul_squareRootAbelPrefix_step,norm_mul,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (squareRootAbelReciprocalClock_nonneg _)]
    have hdiff : ‖squareRootAbelPrefix g (N+1)-squareRootAbelPrefix g N‖ ≤
        2*C*((N:ℝ)+2) := by
      refine (norm_sub_le _ _).trans ((add_le_add (hA (N+1)) (hA N)).trans ?_)
      push_cast
      nlinarith [mul_nonneg hC (Nat.cast_nonneg (α := ℝ) N)]
    have hu : squareRootAbelReciprocalClock ((N:ℝ)+1) ≤ 3*Real.sqrt ((N:ℝ)+2) :=
      (squareRootAbelReciprocalClock_le
        (by have := Nat.cast_nonneg (α := ℝ) N; linarith)).trans
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith)) (by positivity))
    calc
      _ ≤ (3*Real.sqrt ((N:ℝ)+2))*(2*C*((N:ℝ)+2)) :=
        mul_le_mul hu hdiff (norm_nonneg _) (by positivity)
      _ = 6*C*((N:ℝ)+2)^((3:ℝ)/2) := by
        rw [Real.sqrt_eq_rpow]
        calc
          _ = 6*C*(((N:ℝ)+2)^((1:ℝ)/2)*((N:ℝ)+2)^(1:ℝ)) := by rw [Real.rpow_one]; ring
          _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 2; ring
      _ = _ := by push_cast; ring_nf

/-- The coefficient boundary vanishes on the safe half-plane. -/
theorem tendsto_squareRootAbel_first_boundary {g : ℕ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ n, ‖squareRootAbelPrefix g n‖ ≤ C*((n:ℝ)+1))
    {s : ℂ} (hs : (3/2:ℝ) < s.re) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N,g n)*((N:ℂ)+1)^(-s)) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => 6*C*((N:ℝ)+1)^(-(s.re-3/2))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_nat_atTop (show 0 < s.re-3/2 by linarith)).comp
      (tendsto_add_atTop_nat 1)).const_mul (6*C)
  apply squeeze_zero_norm' _ ht
  filter_upwards with N
  have hx : 0 < (N:ℝ)+1 := by positivity
  have hn : ‖((N:ℂ)+1)^(-s)‖ = ((N:ℝ)+1)^(-s.re) := by
    have h := Complex.norm_cpow_eq_rpow_re_of_pos hx (y := -s)
    simpa only [Complex.ofReal_add,Complex.ofReal_natCast,Complex.ofReal_one,Complex.neg_re] using h
  rw [norm_mul,hn]
  calc
    _ ≤ (6*C*((N:ℝ)+1)^((3:ℝ)/2))*((N:ℝ)+1)^(-s.re) :=
      mul_le_mul_of_nonneg_right (norm_sum_le_of_squareRootAbelPrefix_bound hC hA N) (by positivity)
    _ = _ := by rw [mul_assoc,← Real.rpow_add hx]; congr 2; ring

/-- The weighted-prefix boundary vanishes throughout the strict half-plane. -/
theorem tendsto_squareRootAbel_second_boundary {A : ℕ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ n, ‖A n‖ ≤ C*((n:ℝ)+1))
    {s : ℂ} (hs : (1/2:ℝ) < s.re) :
    Tendsto (fun N : ℕ => A N*squareRootAbelDirichletKernel ((N:ℝ)+1) s) atTop (𝓝 0) := by
  have ht : Tendsto (fun N : ℕ => 3*C*‖s‖*((N:ℝ)+1)^(-(s.re-1/2))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_nat_atTop (show 0 < s.re-1/2 by linarith)).comp
      (tendsto_add_atTop_nat 1)).const_mul (3*C*‖s‖)
  apply squeeze_zero_norm' _ ht
  filter_upwards with N
  have hx : 0 < (N:ℝ)+1 := by positivity
  rw [norm_mul]
  calc
    _ ≤ (C*((N:ℝ)+1))*(3*‖s‖*((N:ℝ)+1)^(-s.re-1/2)) :=
      mul_le_mul (hA N) (norm_squareRootAbelDirichletKernel_le
        (by have := Nat.cast_nonneg (α := ℝ) N; linarith) (by linarith)) (norm_nonneg _) (by positivity)
    _ = (3*C*‖s‖)*(((N:ℝ)+1)^(1:ℝ)*((N:ℝ)+1)^(-s.re-1/2)) := by
      rw [Real.rpow_one]
      ring
    _ = _ := by rw [← Real.rpow_add hx]; congr 2; ring

/-- The holomorphic candidate agrees with the literal absolutely convergent L-series. -/
theorem squareRootAbelDirichletSum_eq_LSeries {g : ℕ → ℂ} {C : ℝ}
    (hC : 0 ≤ C) (hA : ∀ n, ‖squareRootAbelPrefix g n‖ ≤ C*((n:ℝ)+1))
    {s : ℂ} (hs : (3/2:ℝ) < s.re) (hg : LSeriesSummable g s) :
    squareRootAbelDirichletSum (squareRootAbelPrefix g) s = LSeries g s := by
  have hseries := (summable_squareRootAbelDirichletTerm hC hA
    (show (1/2:ℝ) < s.re by linarith)).hasSum.tendsto_sum_nat
  have hcombined := ((tendsto_squareRootAbel_first_boundary hC hA hs).add
    (tendsto_squareRootAbel_second_boundary hC hA (show (1/2:ℝ) < s.re by linarith))).add hseries
  have hcont : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N,g n*(n:ℂ)^(-s)) atTop
      (𝓝 (squareRootAbelDirichletSum (squareRootAbelPrefix g) s)) := by
    simpa only [zero_add,← sum_dirichlet_eq_squareRootAbel,squareRootAbelDirichletSum] using hcombined
  have hpartial : ∀ N : ℕ, (∑ n ∈ Icc 1 N,g n*(n:ℂ)^(-s)) =
      ∑ n ∈ range (N+1), LSeries.term g s n := by
    intro N
    calc
      _ = ∑ n ∈ Icc 1 N,LSeries.term g s n := by
        apply sum_congr rfl
        intro n hn
        rw [LSeries.term_of_ne_zero (by have := (mem_Icc.mp hn).1; omega),
          Complex.cpow_neg,div_eq_mul_inv]
      _ = _ := by
        rw [← Ico_add_one_right_eq_Icc,sum_Ico_eq_sub _ (by omega : 1 ≤ N+1)]
        simp
  have hls : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N,g n*(n:ℂ)^(-s)) atTop
      (𝓝 (LSeries g s)) := by
    simp_rw [hpartial]
    exact hg.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hcont hls

end RHTower
