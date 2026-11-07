import Mathlib

/-!
# Uniform averages from a complementary translate

A continuous real observable on a compact normed additive group has uniform
orbit average `c/2` if its sum with a translate by an element of order at most
two is identically `c`, and the integer orbit of the rotation is dense.

Approximate the complementary translate by one fixed orbit point. Uniform
continuity controls the paired values; shifting a finite orbit sum changes
only two bounded boundary blocks. The starting point remains unrestricted.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

private theorem abs_prefix_sum_le {u : ℕ → ℝ} {M : ℝ}
    (hu : ∀ i, |u i| ≤ M) (n : ℕ) :
    |∑ i ∈ Finset.range n, u i| ≤ (n : ℝ) * M := by
  apply abs_le.mpr
  constructor
  · have h := Finset.sum_le_sum (s := Finset.range n)
      (fun i _ => (abs_le.mp (hu i)).1)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_neg] using h
  · have h := Finset.sum_le_sum (s := Finset.range n)
      (fun i _ => (abs_le.mp (hu i)).2)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h

/-- Shifting a bounded finite sum changes only its two boundary blocks. -/
private theorem abs_prefix_shift_le {u : ℕ → ℝ} {M : ℝ}
    (hu : ∀ i, |u i| ≤ M) (n k : ℕ) :
    |(∑ i ∈ Finset.range n, u (i + k)) - ∑ i ∈ Finset.range n, u i| ≤
      2 * (k : ℝ) * M := by
  have he : (∑ i ∈ Finset.range n, u i) + (∑ i ∈ Finset.range k, u (n + i)) =
      (∑ i ∈ Finset.range k, u i) + (∑ i ∈ Finset.range n, u (k + i)) := by
    rw [← Finset.sum_range_add, ← Finset.sum_range_add, Nat.add_comm n k]
  simp_rw [Nat.add_comm n, Nat.add_comm k] at he
  have hA := abs_le.mp (abs_prefix_sum_le (fun i => hu (i + n)) k)
  have hB := abs_le.mp (abs_prefix_sum_le hu k)
  apply abs_le.mpr
  constructor <;> linarith only [he, hA.1, hA.2, hB.1, hB.2]

variable {G : Type*} [NormedAddCommGroup G]

/-- A finite sum along a translation orbit. -/
def rotationSum (f : G → ℝ) (a : G) (n : ℕ) (x : G) : ℝ :=
  ∑ i ∈ Finset.range n, f (x - i • a)

private theorem rotationSum_shift_bound {f : G → ℝ} {a : G} {M : ℝ}
    (hf : ∀ x, |f x| ≤ M) (n k : ℕ) (x : G) :
    |rotationSum f a n (x - k • a) - rotationSum f a n x| ≤ 2 * (k : ℝ) * M := by
  have h := abs_prefix_shift_le (u := fun i => f (x - i • a))
    (fun i => hf _) n k
  have he : rotationSum f a n (x - k • a) =
      ∑ i ∈ Finset.range n, f (x - (i + k) • a) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [add_nsmul]
    abel
  rw [he]
  exact h

private theorem exists_nat_close_involution {a h : G}
    (hd : DenseRange (fun k : ℤ => k • a)) (hh : h + h = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ k : ℕ, dist h (k • a) < δ := by
  have hneg : -h = h := by
    calc
      -h = -h + (h + h) := by rw [hh, add_zero]
      _ = h := by abel
  obtain ⟨k, hk⟩ := hd.exists_dist_lt h hδ
  cases k with
  | ofNat k => exact ⟨k, by simpa using hk⟩
  | negSucc k =>
    refine ⟨k + 1, ?_⟩
    have he : dist h ((k + 1) • a) = dist h (-((k + 1) • a)) := by
      calc
        _ = dist (-h) (-((k + 1) • a)) := (dist_neg_neg _ _).symm
        _ = _ := by rw [hneg]
    rw [he]
    simpa using hk

private theorem rotationSum_pair_bound {f : G → ℝ} {a : G} {c ε : ℝ} {k : ℕ}
    (hp : ∀ x, |f x + f (x - k • a) - c| ≤ ε) (n : ℕ) (x : G) :
    |rotationSum f a n x + rotationSum f a n (x - k • a) - (n : ℝ) * c| ≤
      (n : ℝ) * ε := by
  have h := abs_prefix_sum_le (fun i => hp (x - i • a)) n
  have he (i : ℕ) : x - i • a - k • a = x - k • a - i • a := by abel
  simpa only [he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, rotationSum] using h

/-- A complementary translate fixes the uniform average along a dense rotation orbit. -/
theorem uniform_rotation_average_of_complement [CompactSpace G]
    (f : C(G, ℝ)) {a h : G} {c : ℝ}
    (hd : DenseRange (fun k : ℤ => k • a)) (hh : h + h = 0)
    (hc : ∀ x, f x + f (x - h) = c) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x,
      |rotationSum f a n x / (n : ℝ) - c / 2| < ε := by
  intro ε hε
  have hu := CompactSpace.uniformContinuous_of_continuous f.continuous
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  obtain ⟨k, hk⟩ := exists_nat_close_involution hd hh hδ
  have hp (x : G) : |f x + f (x - k • a) - c| ≤ ε := by
    have hdist : dist (x - k • a) (x - h) < δ := by
      have he : dist (x - k • a) (x - h) = dist h (k • a) := by
        simp only [dist_eq_norm]
        congr 1
        abel
      rwa [he]
    have hv := hclose hdist
    rw [Real.dist_eq] at hv
    have he : f x + f (x - k • a) - c = f (x - k • a) - f (x - h) := by
      linear_combination hc x
    rw [he]
    exact hv.le
  have hM (x : G) : |f x| ≤ ‖f‖ := by
    simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (2 * (k : ℝ) * ‖f‖ / ε))
  refine ⟨N, ?_⟩
  intro n hn x
  have hNn : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
  have hN1 := lt_of_le_of_lt (le_max_left 1 (2 * (k : ℝ) * ‖f‖ / ε)) hN
  have hn0 : 0 < (n : ℝ) := by linarith only [hN1, hNn]
  have hcut : 2 * (k : ℝ) * ‖f‖ / ε < (n : ℝ) :=
    (lt_of_le_of_lt (le_max_right 1 (2 * (k : ℝ) * ‖f‖ / ε)) hN).trans_le hNn
  have hkbound := (div_lt_iff₀ hε).mp hcut
  have hpSum := abs_le.mp (rotationSum_pair_bound hp n x)
  have hsSum := abs_le.mp (rotationSum_shift_bound (a := a) hM n k x)
  have hb : |2 * rotationSum f a n x - (n : ℝ) * c| ≤
      (n : ℝ) * ε + 2 * (k : ℝ) * ‖f‖ := by
    apply abs_le.mpr
    constructor <;> linarith only [hpSum.1, hpSum.2, hsSum.1, hsSum.2]
  have he : rotationSum f a n x / (n : ℝ) - c / 2 =
      (2 * rotationSum f a n x - (n : ℝ) * c) / (2 * (n : ℝ)) := by
    field_simp
  rw [he, abs_div, abs_of_pos (show 0 < 2 * (n : ℝ) by positivity)]
  apply (div_lt_iff₀ (by positivity : 0 < 2 * (n : ℝ))).mpr
  linarith only [hb, hkbound]

end GaloisForLFunctions.SumProductArithmeticOfTheLogarithm
