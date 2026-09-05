import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleScaling
import GaloisForLFunctions.RHTower.DirichletAbelConvergence

/-!
# Euler-deletion prefix law and half-plane convergence

The modulus-`q` deletion coefficients have an exact summatory law:

```text
∑_{n < N} (1 - q [q ∣ n+1]) = N mod q.
```

For the canonical modulus `q + 1`, every coefficient prefix is therefore bounded by `q`.
Abel summation then gives ordered convergence of the weighted deletion path throughout
`Re s > 0`.  This is the first analytic admission gate for the quasi-shuffle architecture:
the level-one path exists without absolute convergence or reflection symmetry.

No claim about convergence of the chronological second level is made here.
-/

namespace RHTower

open scoped BigOperators

/-- Integer endpoint of the first `N` modulus-`q` deletion jumps. -/
def deletionCoeffPartialSum (q N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range N, blockDeletionCoefficient q (n + 1)

/-- Exact endpoint law: every complete deletion block closes, leaving only its remainder. -/
theorem deletionCoeffPartialSum_eq_mod (q N : ℕ) :
    deletionCoeffPartialSum q N = ((N % q : ℕ) : ℤ) := by
  rw [deletionCoeffPartialSum]
  calc
    (∑ n ∈ Finset.range N, blockDeletionCoefficient q (n + 1)) =
        (N : ℤ) - (q : ℤ) * ((Finset.range N).filter (fun n => q ∣ n + 1)).card := by
      simp only [blockDeletionCoefficient]
      rw [Finset.sum_sub_distrib]
      have hind :
          (∑ x ∈ Finset.range N, (q : ℤ) * if q ∣ x + 1 then 1 else 0) =
            ∑ x ∈ (Finset.range N).filter (fun n => q ∣ n + 1), (q : ℤ) := by
        simp_rw [mul_ite, mul_one, mul_zero]
        rw [Finset.sum_filter]
      rw [hind]
      simp [mul_comm]
    _ = (N : ℤ) - (q : ℤ) * (N / q : ℕ) := by rw [Nat.card_multiples]
    _ = (N % q : ℕ) := by
      have hnat : N % q + q * (N / q) = N := Nat.mod_add_div N q
      have hz : ((N % q : ℕ) : ℤ) + (q : ℤ) * (N / q : ℕ) = (N : ℤ) := by
        exact_mod_cast hnat
      omega

/-- Zero-indexed complex coefficient of the modulus-`q + 1` deletion series. -/
def eulerDeletionDirichletCoefficient (q n : ℕ) : ℂ :=
  blockDeletionCoefficient (q + 1) (n + 1)

/-- Exact complex endpoint of a canonical deletion prefix. -/
theorem eulerDeletionDirichletCoefficient_partialSum (q N : ℕ) :
    ∑ n ∈ Finset.range N, eulerDeletionDirichletCoefficient q n = (N % (q + 1) : ℕ) := by
  simp only [eulerDeletionDirichletCoefficient]
  rw [← Int.cast_sum]
  change ((deletionCoeffPartialSum (q + 1) N : ℤ) : ℂ) = _
  exact congrArg (fun z : ℤ => (z : ℂ))
    (deletionCoeffPartialSum_eq_mod (q + 1) N)

/-- Every canonical deletion prefix has norm at most the number of unit jumps in one block. -/
theorem eulerDeletionDirichletCoefficient_partialSum_norm_le (q N : ℕ) :
    ‖∑ n ∈ Finset.range N, eulerDeletionDirichletCoefficient q n‖ ≤ q := by
  rw [eulerDeletionDirichletCoefficient_partialSum]
  rw [Complex.norm_natCast]
  have hmod := Nat.mod_lt N (Nat.succ_pos q)
  exact_mod_cast (Nat.lt_succ_iff.mp hmod)

/-- The weighted Euler-deletion path has an ordered limit throughout `Re s > 0`. -/
theorem tendsto_eulerDeletionDirichletCoefficient {q : ℕ} {s : ℂ} (hs : 0 < s.re) :
    ∃ L : ℂ,
      Filter.Tendsto
        (fun N => ∑ n ∈ Finset.range N,
          eulerDeletionDirichletCoefficient q n * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s))
        Filter.atTop (nhds L) := by
  exact GaloisForLFunctions.RHTower.tendsto_dirichlet_partialSum_of_bounded
    (eulerDeletionDirichletCoefficient_partialSum_norm_le q) hs

/-! ## Exact finite dilation law -/

/-- Reindex a one-indexed interval as a zero-indexed range. -/
theorem sum_Icc_eq_sum_range_succ {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ n ∈ Finset.range N, f (n + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

/-- Reindex the multiples of `p` in `[1, N]` by their cofactors. -/
theorem sum_Icc_filter_dvd_reindex {M : Type*} [AddCommMonoid M]
    (p N : ℕ) (hp : 0 < p) (f : ℕ → M) :
    ∑ n ∈ (Finset.Icc 1 N).filter (fun n => p ∣ n), f n =
      ∑ m ∈ Finset.Icc 1 (N / p), f (p * m) := by
  classical
  refine (Finset.sum_nbij' (i := fun m => p * m) (j := fun n => n / p) ?_ ?_ ?_ ?_ ?_).symm
  · intro m hm
    rw [Finset.mem_Icc] at hm
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩
    · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    · rw [mul_comm]
      exact (Nat.le_div_iff_mul_le hp).mp hm.2
  · intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hn2⟩, hpn⟩ := hn
    rw [Finset.mem_Icc]
    refine ⟨?_, Nat.div_le_div_right hn2⟩
    exact Nat.one_le_div_iff hp |>.mpr (Nat.le_of_dvd (by omega) hpn)
  · intro m _hm
    exact Nat.mul_div_cancel_left m hp
  · intro n hn
    simp only [Finset.mem_filter] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m _hm
    rfl

/-- Generic finite Euler deletion: subtract the dilation channel before choosing a weight. -/
theorem eulerDeletion_weighted_Icc_eq_dilation
    (p N : ℕ) (hp : 0 < p) (f : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc 1 N, (blockDeletionCoefficient p n : ℂ) * f n =
      ∑ n ∈ Finset.Icc 1 N, f n -
        (p : ℂ) * ∑ m ∈ Finset.Icc 1 (N / p), f (p * m) := by
  rw [← sum_Icc_filter_dvd_reindex p N hp f]
  rw [Finset.mul_sum, Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hd : p ∣ n
  · simp [blockDeletionCoefficient, hd]
    ring
  · simp [blockDeletionCoefficient, hd]

/-- Ordinary one-indexed finite Dirichlet prefix. -/
noncomputable def zetaDirichletPrefix (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, ((n : ℝ) : ℂ) ^ (-s)

/-- Weighted modulus-`p` Euler-deletion prefix. -/
noncomputable def eulerDeletionDirichletPrefix (p N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    (blockDeletionCoefficient p n : ℂ) * ((n : ℝ) : ℂ) ^ (-s)

/-- Actual complex multiplier induced by the dilation `n ↦ p n`. -/
noncomputable def complexEulerDilationFactor (p : ℕ) (s : ℂ) : ℂ :=
  (p : ℂ) * (((p : ℝ) : ℂ) ^ (-s))

/-- Exact finite Euler-dilation identity, including the floor cutoff of the dilated channel. -/
theorem eulerDeletionDirichletPrefix_eq_dilation
    (p N : ℕ) (hp : 0 < p) (s : ℂ) :
    eulerDeletionDirichletPrefix p N s =
      zetaDirichletPrefix N s -
        complexEulerDilationFactor p s * zetaDirichletPrefix (N / p) s := by
  rw [eulerDeletionDirichletPrefix, zetaDirichletPrefix, zetaDirichletPrefix,
    eulerDeletion_weighted_Icc_eq_dilation p N hp]
  rw [complexEulerDilationFactor, Finset.mul_sum, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hpow : (((p * m : ℕ) : ℝ) : ℂ) ^ (-s) =
      (((p : ℕ) : ℝ) : ℂ) ^ (-s) * (((m : ℕ) : ℝ) : ℂ) ^ (-s) := by
    simpa only [Nat.cast_mul, Complex.ofReal_mul] using
      (Complex.mul_cpow_ofReal_nonneg hp0 hm0 (-s))
  rw [hpow]
  ring

/-- The actual complex dilation multiplier has the quadratic scale used by the finite signature. -/
theorem normSq_complexEulerDilationFactor
    (p : ℕ) (hp : 0 < p) (s : ℂ) :
    Complex.normSq (complexEulerDilationFactor p s) =
      eulerDilationQuadraticScale (p : ℝ) s.re := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [Complex.normSq_eq_norm_sq, complexEulerDilationFactor, norm_mul,
    Complex.norm_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hpR,
    Complex.neg_re, Real.rpow_def_of_pos hpR, eulerDilationQuadraticScale,
    ← Real.exp_log hpR, pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [Real.log_exp]
  ring

end RHTower
