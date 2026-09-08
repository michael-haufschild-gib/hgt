import GaloisForLFunctions.RHTower.MobiusDivisorSqrtGrowthObstruction

/-!
# Cofinal square-root escape and fixed-grid sampling

Finite prefixes cannot absorb the unbounded normalized signed source.
Chebyshev bounds give square-root control of each Abel increment, so
sampling along any fixed positive integer grid preserves the escape.
-/

noncomputable section
open Finset
namespace RHTower

/-- The actual normalized signed source escapes every fixed square-root envelope
arbitrarily far out. -/
theorem exists_sum_mobiusDivisorDilationChannel_gt_sqrt_after (C : ℝ) (M₀ : ℕ) :
    ∃ M : ℕ,M₀ ≤ M ∧ C*Real.sqrt M < |∑ d  ∈  Icc 1 M,mobiusDivisorDilationChannel M d| := by
  let D : ℝ := ∑ m  ∈  range M₀,|∑ d  ∈  Icc 1 m,mobiusDivisorDilationChannel m d|
  have hD : 0 ≤ D := sum_nonneg (fun _ _ => abs_nonneg _)
  have hex : ∃ M : ℕ,(|C|+D)*Real.sqrt M < |∑ d  ∈  Icc 1 M,mobiusDivisorDilationChannel M d| := by
    by_contra hn
    push Not at hn
    exact not_exists_sqrt_bound_sum_mobiusDivisorDilationChannel ⟨|C|+D,hn⟩
  obtain ⟨M,hM⟩ := hex
  have hMpos : 0<M := by
    by_contra hn
    have he : M=0 := by omega
    simp [he] at hM
  have hM1 : 1 ≤ Real.sqrt M := by
    calc
      1 = Real.sqrt 1 := Real.sqrt_one.symm
      _  ≤  _ := Real.sqrt_le_sqrt (by exact_mod_cast hMpos)
  have htail : M₀ ≤ M := by
    by_contra hn
    have hle : |∑ d  ∈  Icc 1 M,mobiusDivisorDilationChannel M d| ≤ D :=
      single_le_sum (f := fun m => |∑ d ∈ Icc 1 m,mobiusDivisorDilationChannel m d|) (fun _ _ => abs_nonneg _)
        (mem_range.mpr (by omega))
    have hscale : D ≤ (|C|+D)*Real.sqrt M := by
      nlinarith [abs_nonneg C,mul_nonneg (abs_nonneg C) (Real.sqrt_nonneg (M:ℝ))]
    linarith
  exact ⟨M,htail,lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (Real.sqrt_nonneg _)) hM⟩

private theorem defect_linear_bound : ∃ D : ℝ,0 ≤ D ∧ ∀ k : ℕ,1 ≤ k → |psiDefect k| ≤ D*k := by
  refine ⟨Real.log 4+5+2*|Real.eulerMascheroniConstant|,by positivity,?_⟩
  intro k hk
  have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hb := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α:=ℝ) k)
  have hn := Chebyshev.psi_nonneg (k:ℝ)
  rw [psiDefect,chebyshevPsi_eq_psi]
  apply abs_le.mpr
  constructor <;> nlinarith [le_abs_self Real.eulerMascheroniConstant,
    neg_abs_le Real.eulerMascheroniConstant,
    mul_le_mul_of_nonneg_left hkR (abs_nonneg Real.eulerMascheroniConstant)]

/-- Every source increment has an unconditional square-root bound, uniformly in the cutoff. -/
theorem exists_sqrt_bound_sum_mobiusDivisorDilationChannel_increment :
    ∃ D : ℝ,0 ≤ D ∧ ∀ M : ℕ,
      |(∑ d  ∈  Icc 1 (M+1),mobiusDivisorDilationChannel (M+1) d)-
        (∑ d  ∈  Icc 1 M,mobiusDivisorDilationChannel M d)| ≤ D*Real.sqrt M := by
  obtain ⟨D,hD,hdef⟩ := defect_linear_bound
  refine ⟨D,hD,?_⟩
  intro M
  rcases Nat.eq_zero_or_pos M with rfl|hM
  · simp [mobiusDivisorDilationChannel]
  have hMR : (0:ℝ)<M := by exact_mod_cast hM
  have hstep : 0 ≤ Real.sqrt (M+1:ℕ)-Real.sqrt M :=
    sub_nonneg.mpr (Real.sqrt_le_sqrt (by push_cast; linarith))
  rw [sum_mobiusDivisorDilationChannel_eq_psiDefect_abel,
    sum_mobiusDivisorDilationChannel_eq_psiDefect_abel,
    sum_Ico_succ_top (by omega : 1 ≤ M),add_sub_cancel_left,abs_mul,abs_of_nonneg hstep]
  have hb := mul_le_mul_of_nonneg_left (hdef M hM) hstep
  have hclock := squareRootAbelReciprocalClock_mul_step hMR.le
  unfold squareRootAbelReciprocalClock at hclock
  have hsq := Real.sq_sqrt hMR.le
  have hstepbound : (Real.sqrt (M+1:ℕ)-Real.sqrt M)*(M:ℝ) ≤ Real.sqrt M := by
    have hr := Real.sqrt_le_sqrt (show (M:ℝ) ≤ (M:ℝ)+1 by linarith)
    have hp := mul_nonneg hstep (Real.sqrt_nonneg (M:ℝ))
    push_cast at hstep ⊢
    nlinarith [mul_nonneg hstep (sub_nonneg.mpr hr),
      mul_nonneg (Real.sqrt_nonneg (M:ℝ)) (show 0 ≤ 1-(Real.sqrt ((M:ℝ)+1)-Real.sqrt M)*Real.sqrt M by nlinarith)]
  exact hb.trans (by nlinarith only [mul_le_mul_of_nonneg_left hstepbound hD])

private theorem sqrt_increment_gap_bound (f : ℕ → ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hstep : ∀ k,|f (k+1)-f k| ≤ D*Real.sqrt k) {a b : ℕ} (hab : a ≤ b) :
    |f b-f a| ≤ D*(b-a:ℕ)*Real.sqrt b := by
  have htel : (∑ k ∈ Ico a b,(f (k+1)-f k))=f b-f a := by
    rw [sum_Ico_eq_sub _ hab,sum_range_sub,sum_range_sub]
    ring
  rw [← htel]
  calc
    _ ≤ ∑ k ∈ Ico a b,|f (k+1)-f k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Ico a b,D*Real.sqrt b := by
      apply sum_le_sum
      intro k hk
      exact (hstep k).trans (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (by exact_mod_cast (mem_Ico.mp hk).2.le)) hD)
    _ = _ := by simp only [sum_const,Nat.card_Ico,nsmul_eq_mul]; ring

/-- A bounded distance between sampled cutoffs cannot hide square-root escape:
every fixed positive integer grid still has unbounded normalized signed source. -/
theorem not_exists_sqrt_bound_sum_mobiusDivisorDilationChannel_grid
    {c : ℕ} (hc : 0<c) :
    ¬ ∃ C : ℝ,∀ N : ℕ,
      |∑ d ∈ Icc 1 (c*N),mobiusDivisorDilationChannel (c*N) d| ≤ C*Real.sqrt (c*N:ℕ) := by
  rintro ⟨C,hgrid⟩
  obtain ⟨D,hD,hstep⟩ := exists_sqrt_bound_sum_mobiusDivisorDilationChannel_increment
  apply not_exists_sqrt_bound_sum_mobiusDivisorDilationChannel
  refine ⟨|C|+D*c,?_⟩
  intro M
  have hmod := Nat.mod_add_div M c
  have hless := Nat.mod_lt M hc
  have ha : c*(M/c) ≤ M := by omega
  have hgap : M-c*(M/c) ≤ c := by omega
  have hdiff := sqrt_increment_gap_bound
    (fun M => ∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d) hD hstep ha
  have hgs : |∑ d ∈ Icc 1 (c*(M/c)),mobiusDivisorDilationChannel (c*(M/c)) d| ≤
      |C| *Real.sqrt M := by
    exact ((hgrid (M/c)).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.sqrt_nonneg _))).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast ha)) (abs_nonneg C))
  have hgapR : ((M-c*(M/c):ℕ):ℝ) ≤ c := by exact_mod_cast hgap
  have hdb : D*(M-c*(M/c):ℕ)*Real.sqrt M ≤ D*c*Real.sqrt M := by gcongr
  have ht := abs_sub_le (∑ d ∈ Icc 1 M,mobiusDivisorDilationChannel M d)
    (∑ d ∈ Icc 1 (c*(M/c)),mobiusDivisorDilationChannel (c*(M/c)) d) 0
  simp only [sub_zero] at ht
  nlinarith only [ht,hdiff,hgs,hdb]

/-- Square-root escape survives both fixed-grid sampling and deletion of any finite prefix. -/
theorem exists_sum_mobiusDivisorDilationChannel_grid_gt_sqrt_after
    {c : ℕ} (hc : 0<c) (C : ℝ) (N₀ : ℕ) :
    ∃ N : ℕ,N₀ ≤ N ∧ C*Real.sqrt (c*N:ℕ) <
      |∑ d ∈ Icc 1 (c*N),mobiusDivisorDilationChannel (c*N) d| := by
  let D : ℝ := ∑ n ∈ range N₀,|∑ d ∈ Icc 1 (c*n),mobiusDivisorDilationChannel (c*n) d|
  have hD : 0 ≤ D := sum_nonneg (fun _ _ => abs_nonneg _)
  have hex : ∃ N : ℕ,(|C|+D)*Real.sqrt (c*N:ℕ) <
      |∑ d ∈ Icc 1 (c*N),mobiusDivisorDilationChannel (c*N) d| := by
    by_contra hn
    push Not at hn
    exact not_exists_sqrt_bound_sum_mobiusDivisorDilationChannel_grid hc ⟨|C|+D,hn⟩
  obtain ⟨N,hN⟩ := hex
  have hNpos : 0<N := by
    by_contra hn
    have he : N=0 := by omega
    simp [he] at hN
  have hroot : 1 ≤ Real.sqrt (c*N:ℕ) := by
    calc
      1 = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by exact_mod_cast (Nat.mul_pos hc hNpos))
  have htail : N₀ ≤ N := by
    by_contra hn
    have hle : |∑ d ∈ Icc 1 (c*N),mobiusDivisorDilationChannel (c*N) d| ≤ D :=
      single_le_sum (f := fun n => |∑ d ∈ Icc 1 (c*n),mobiusDivisorDilationChannel (c*n) d|)
        (fun _ _ => abs_nonneg _) (mem_range.mpr (by omega))
    have hscale : D ≤ (|C|+D)*Real.sqrt (c*N:ℕ) := by
      nlinarith [abs_nonneg C,mul_nonneg (abs_nonneg C) (Real.sqrt_nonneg (c*N:ℕ))]
    linarith
  exact ⟨N,htail,lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right (by linarith [le_abs_self C]) (Real.sqrt_nonneg _)) hN⟩

end RHTower
