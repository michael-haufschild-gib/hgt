import GaloisForLFunctions.RigidArithmeticOfCuts.TheShortSumBarrierHasALeftEndpoint
import GaloisForLFunctions.RHTower.Sieve.DirichletMeasureLargeValues

/-!
# Cancellation at almost every height

A pointwise bound for `S_y(t) = Σ_{y < p ≤ 2y} p^{it}` at all heights below the Vinogradov–Korobov length would move the zero-free
region, and it is open. What is true at each end is exact.

* **Some height fails up to `log T`.** For `T ≥ 4(D+1) 4^{2y(2D+1)}` there is `t ≤ T` with `‖S_y(t)‖ ≥ (1 − 5/(D+1)) |P|`: no
  cancellation at all (`exists_height_window_no_cancellation`).
* **Almost every height works.** Off a set of measure `≪ T Y^{-2ε}` in `(0, T]`, square-root cancellation holds at all dyadic lengths
  from `Y` up to `T/log T` simultaneously (`exists_cancellation_off_small_set`).

So the failure of pointwise bounds below VK lives on a set of heights of small measure, at every length, and that set is nonempty
for `y ≲ log T`. Between these two statements, what is missing is the size of the exceptional set at lengths above `log T`.
-/

open Finset MeasureTheory Complex

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- The primes in the dyadic window `(y, 2y]`. -/
def primeWindow (y : ℕ) : Finset ℕ := (Ioc y (2 * y)).filter Nat.Prime

theorem card_primeWindow_le (y : ℕ) : ((primeWindow y).card : ℝ) ≤ y := by
  have h1 : (primeWindow y).card ≤ (Ioc y (2 * y)).card := card_filter_le _ _
  rw [Nat.card_Ioc] at h1
  have h2 : 2 * y - y = y := by omega
  rw [h2] at h1
  exact_mod_cast h1

/-- The prime sum on a dyadic window. -/
def windowSum (y : ℕ) (t : ℝ) : ℂ :=
  ∑ p ∈ primeWindow y, Complex.exp (((t * Real.log p : ℝ) : ℂ) * I)

/-- A sum over `Fin (2y)`, indexed by `n + 1`, restricted to the window. -/
private lemma sum_fin_window {M : Type*} [AddCommMonoid M] (y : ℕ) (f : ℕ → M) :
    ∑ n : Fin (2 * y), (if ((n : ℕ) + 1).Prime ∧ y < (n : ℕ) + 1 then f ((n : ℕ) + 1) else 0) =
      ∑ p ∈ primeWindow y, f p := by
  classical
  have h1 := Fin.sum_univ_eq_sum_range
    (fun n : ℕ => if (n + 1).Prime ∧ y < n + 1 then f (n + 1) else 0) (2 * y)
  rw [h1, range_eq_Ico, Finset.sum_Ico_add' (fun m => if m.Prime ∧ y < m then f m else 0) 0 (2 * y) 1,
    ← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext m
  simp only [primeWindow, mem_filter, mem_Ico, mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp, hy⟩
    exact ⟨⟨hy, by omega⟩, hp⟩
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨⟨by omega, by omega⟩, hp, h1⟩

/-- The coefficients of the window as a Dirichlet polynomial. -/
private def windowCoeff (y : ℕ) (n : Fin (2 * y)) : ℂ :=
  if ((n : ℕ) + 1).Prime ∧ y < (n : ℕ) + 1 then 1 else 0

private lemma dirPoly_windowCoeff (y : ℕ) (t : ℝ) :
    _root_.RHTower.Sieve.dirPoly (2 * y) (windowCoeff y) t = windowSum y t := by
  rw [_root_.RHTower.Sieve.dirPoly, windowSum,
    ← sum_fin_window y (fun p : ℕ => Complex.exp (((t * Real.log p : ℝ) : ℂ) * I))]
  refine sum_congr rfl fun n _ => ?_
  rw [windowCoeff]
  split_ifs
  · push_cast
    ring
  · simp

private lemma sum_norm_windowCoeff (y : ℕ) :
    ∑ m : Fin (2 * y), ‖windowCoeff y m‖ ^ 2 = ((primeWindow y).card : ℝ) := by
  have h : ((primeWindow y).card : ℝ) = ∑ p ∈ primeWindow y, (1 : ℝ) := by simp
  rw [h, ← sum_fin_window y (fun _ => (1 : ℝ))]
  refine sum_congr rfl fun n _ => ?_
  rw [windowCoeff]
  split_ifs <;> simp

/-- **The large values of a window sum have small measure.** -/
theorem volume_large_windowSum_le (y : ℕ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ 2 * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖windowSum y t‖} ≤
      (T + 8 * (y : ℝ) * (1 + Real.log (2 * y))) * y := by
  have h := _root_.RHTower.Sieve.volume_largeValues_le (2 * y) (windowCoeff y) hT hV
  simp_rw [dirPoly_windowCoeff] at h
  rw [sum_norm_windowCoeff] at h
  refine h.trans ?_
  have hcast : ((2 * y : ℕ) : ℝ) = 2 * (y : ℝ) := by push_cast; ring
  rw [hcast]
  have hlog : 0 ≤ 1 + Real.log (2 * (y : ℝ)) := by
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · simp
    · have h1 : (1 : ℝ) ≤ 2 * (y : ℝ) := by
        have : (1 : ℝ) ≤ y := by exact_mod_cast hy
        linarith
      have := Real.log_nonneg h1
      linarith
  have h2 : T + 4 * (2 * (y : ℝ)) * (1 + Real.log (2 * (y : ℝ))) =
      T + 8 * (y : ℝ) * (1 + Real.log (2 * y)) := by ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left (card_primeWindow_le y) (by positivity)

/-- **Square-root cancellation off a small set, at all dyadic lengths at once.** -/
theorem exists_cancellation_off_small_set {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (T : ℝ) (i₀ i₁ : ℕ), 0 < T →
      (∀ i ∈ Ico i₀ i₁, 8 * ((2 : ℝ) ^ i) * (1 + Real.log (2 * (2 : ℝ) ^ i)) ≤ T) →
      ∃ E : Set ℝ, E ⊆ Set.Ioc (0 : ℝ) T ∧
        volume.real E ≤ C * T * ((2 : ℝ) ^ (-(2 * ε))) ^ i₀ ∧
        ∀ t ∈ Set.Ioc (0 : ℝ) T \ E, ∀ i ∈ Ico i₀ i₁,
          ‖windowSum (2 ^ i) t‖ < ((2 : ℝ) ^ i) ^ (1 / 2 + ε) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  set q : ℝ := (2 : ℝ) ^ (-(2 * ε)) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos h2 _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨2 / (1 - q), div_nonneg (by norm_num) (by linarith), fun T i₀ i₁ hT hsmall => ?_⟩
  set V : ℕ → ℝ := fun i => ((2 : ℝ) ^ i) ^ (1 / 2 + ε) with hV
  set F : ℕ → Set ℝ := fun i => {t ∈ Set.Ioc (0 : ℝ) T | V i ≤ ‖windowSum (2 ^ i) t‖} with hF
  refine ⟨⋃ i ∈ Ico i₀ i₁, F i, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨i, _, hi⟩ := Set.mem_iUnion₂.mp ht
    exact hi.1
  · have hbound : ∀ i ∈ Ico i₀ i₁, volume.real (F i) ≤ 2 * T * q ^ i := by
      intro i hi
      have hpow : (0 : ℝ) < (2 : ℝ) ^ i := by positivity
      have hVpos : 0 < V i := Real.rpow_pos_of_pos hpow _
      have hmain := volume_large_windowSum_le (2 ^ i) hT.le hVpos.le
      have hcast : (((2 : ℕ) ^ i : ℕ) : ℝ) = (2 : ℝ) ^ i := by push_cast; rfl
      rw [hcast] at hmain
      have hsm := hsmall i hi
      have h3 : T + 8 * ((2 : ℝ) ^ i) * (1 + Real.log (2 * (2 : ℝ) ^ i)) ≤ 2 * T := by linarith
      have hV2 : V i ^ 2 = (2 : ℝ) ^ i * ((2 : ℝ) ^ i) ^ (2 * ε) := by
        rw [hV]
        simp only
        rw [← Real.rpow_natCast (((2 : ℝ) ^ i) ^ (1 / 2 + ε)) 2, ← Real.rpow_mul hpow.le]
        have h4 : (1 / 2 + ε) * ((2 : ℕ) : ℝ) = 1 + 2 * ε := by
          push_cast
          ring
        rw [h4, Real.rpow_add hpow, Real.rpow_one]
      have hqi : q ^ i * ((2 : ℝ) ^ i) ^ (2 * ε) = 1 := by
        rw [hq, ← Real.rpow_natCast ((2 : ℝ) ^ (-(2 * ε))) i, ← Real.rpow_mul h2.le,
          ← Real.rpow_natCast (2 : ℝ) i, ← Real.rpow_mul h2.le, ← Real.rpow_add h2]
        have h5 : -(2 * ε) * ((i : ℕ) : ℝ) + ((i : ℕ) : ℝ) * (2 * ε) = 0 := by ring
        rw [h5, Real.rpow_zero]
      have hX : 0 < ((2 : ℝ) ^ i) ^ (2 * ε) := Real.rpow_pos_of_pos hpow _
      have hcancel : (2 : ℝ) ^ i * ((2 : ℝ) ^ i) ^ (2 * ε) * volume.real (F i) ≤
          (2 : ℝ) ^ i * ((2 : ℝ) ^ i) ^ (2 * ε) * (2 * T * q ^ i) := by
        have h6 : (2 : ℝ) ^ i * ((2 : ℝ) ^ i) ^ (2 * ε) * (2 * T * q ^ i) =
            2 * T * (2 : ℝ) ^ i * (q ^ i * ((2 : ℝ) ^ i) ^ (2 * ε)) := by ring
        rw [h6, hqi, mul_one, ← hV2]
        refine hmain.trans ?_
        exact mul_le_mul_of_nonneg_right h3 hpow.le
      exact le_of_mul_le_mul_left hcancel (by positivity)
    refine (measureReal_biUnion_finset_le _ _).trans ((sum_le_sum hbound).trans ?_)
    rw [← mul_sum]
    have hgeom : ∑ i ∈ Ico i₀ i₁, q ^ i ≤ q ^ i₀ / (1 - q) := geom_sum_Ico_le_of_lt_one hq0.le hq1
    calc 2 * T * ∑ i ∈ Ico i₀ i₁, q ^ i ≤ 2 * T * (q ^ i₀ / (1 - q)) :=
          mul_le_mul_of_nonneg_left hgeom (by positivity)
      _ = _ := by ring
  · rintro t ⟨ht, htE⟩ i hi
    by_contra hge
    push Not at hge
    exact htE (Set.mem_iUnion₂.mpr ⟨i, hi, ht, hge⟩)

/-- **Some height has no cancellation.** Up to height `T ≥ 4(D+1) 4^{2y(2D+1)}`, a dyadic window can be fully aligned. -/
theorem exists_height_window_no_cancellation (y D : ℕ) {T : ℝ}
    (hT : 4 * ((D : ℝ) + 1) * (4 : ℝ) ^ ((2 * D + 1) * (2 * y)) ≤ T) :
    ∃ t ∈ Set.Icc (0 : ℝ) T, (1 - 5 / ((D : ℝ) + 1)) * ((primeWindow y).card : ℝ) ≤ ‖windowSum y t‖ := by
  classical
  obtain ⟨t, ht, h⟩ := exists_height_aligned (2 * y) D (fun _ => 0)
    (fun p => if p ∈ primeWindow y then 1 else 0) (fun p _ => by split_ifs <;> norm_num) hT
  refine ⟨t, ht, ?_⟩
  have hsub : primeWindow y ⊆ primesUpTo (2 * y) := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_filter.mp hp
    have h3 := (mem_Ioc.mp h1).2
    exact mem_filter.mpr ⟨mem_range.mpr (by omega), h2⟩
  have hsum1 : ∑ p ∈ primesUpTo (2 * y), (if p ∈ primeWindow y then (1 : ℝ) else 0) =
      ((primeWindow y).card : ℝ) := by
    rw [sum_ite_mem, inter_eq_right.mpr hsub]
    simp
  have hsum2 : ∑ p ∈ primesUpTo (2 * y), (if p ∈ primeWindow y then (1 : ℝ) else 0) *
      Real.cos (t * Real.log p - 0) = (windowSum y t).re := by
    have h3 : ∀ p ∈ primesUpTo (2 * y), (if p ∈ primeWindow y then (1 : ℝ) else 0) *
        Real.cos (t * Real.log p - 0) =
        if p ∈ primeWindow y then Real.cos (t * Real.log p) else 0 := by
      intro p _
      split_ifs <;> simp
    rw [sum_congr rfl h3, sum_ite_mem, inter_eq_right.mpr hsub, windowSum, Complex.re_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [Complex.exp_ofReal_mul_I_re]
  rw [hsum1, hsum2] at h
  exact h.trans (Complex.re_le_norm _)

end GaloisForLFunctions.RigidArithmeticOfCuts
