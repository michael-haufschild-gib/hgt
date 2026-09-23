import GaloisForLFunctions.RHTower.Sieve.IntervalMultiples
import GaloisForLFunctions.RHTower.Sieve.HeathBrownPrimitiveRayMass

/-!
# Real-ratio Heath--Brown primitive-ray recurrence

The integer layer count naturally produces `floor(N/N0)+1` when `N0 ≤ N`.  For the unrestricted
auxiliary scale in Heath--Brown's Lemma 6, the source estimate is instead expressed using the real
ratio `N/N0`.  The missing case `N < N0` follows ray by ray from

`floor(N/k) ≤ (N/N0) * (floor(N0/k)+1)`.

Primitive-window packing absorbs the endpoint, giving one uniform real-ratio recurrence.
-/

namespace RHTower.Sieve

noncomputable section

private theorem heathBrownPrimitiveLogRayMass_zero
    (m1 m2 delta : ℝ) :
    heathBrownPrimitiveLogRayMass 0 m1 m2 delta = 0 := by
  simp [heathBrownPrimitiveLogRayMass]

private theorem cast_natDiv_le_realRatio_mul_natDiv_add_one
    {N N0 k : ℕ} (hN0 : 1 ≤ N0) (hk : 0 < k) :
    ((N / k : ℕ) : ℝ) ≤
      (N : ℝ) / (N0 : ℝ) * (((N0 / k : ℕ) : ℝ) + 1) := by
  have hNk := (cast_div_bounds (n := N) (d := k) hk).1
  have hN0k := (cast_div_bounds (n := N0) (d := k) hk).2.le
  have hN0real : (0 : ℝ) < (N0 : ℝ) := by exact_mod_cast hN0
  have hkreal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  calc
    ((N / k : ℕ) : ℝ) ≤ (N : ℝ) / (k : ℝ) := hNk
    _ = ((N : ℝ) / (N0 : ℝ)) * ((N0 : ℝ) / (k : ℝ)) := by
      field_simp [ne_of_gt hN0real, ne_of_gt hkreal]
    _ ≤ ((N : ℝ) / (N0 : ℝ)) * (((N0 / k : ℕ) : ℝ) + 1) := by
      gcongr

private theorem cast_heathBrownPrimitiveLogRayMass_le_realRatio_of_lt
    {N N0 : ℕ} (hN : 1 ≤ N) (hN0 : 1 ≤ N0) (hNN0 : N < N0)
    {m1 m2 delta : ℝ} (hm1 : 0 < m1) (hm2 : 0 < m2) (hm : m2 ≤ m1)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (heathBrownPrimitiveLogRayMass N m1 m2 delta : ℝ) ≤
      4 * delta * (N : ℝ) ^ (2 : ℕ) +
        ((N : ℝ) / (N0 : ℝ)) *
          (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
        (N : ℝ) / (N0 : ℝ) := by
  let D := heathBrownPrimitiveLogWindow N m1 m2 delta
  let D0 := heathBrownPrimitiveLogWindow N0 m1 m2 delta
  let x : ℝ := (N : ℝ) / (N0 : ℝ)
  have hsub : D ⊆ D0 := by
    intro p hp
    change p ∈ heathBrownPrimitiveLogWindow N m1 m2 delta at hp
    change p ∈ heathBrownPrimitiveLogWindow N0 m1 m2 delta
    rw [mem_heathBrownPrimitiveLogWindow_height] at hp ⊢
    exact ⟨hp.1, hp.2.1, hp.2.2.1.trans hNN0.le, hp.2.2.2⟩
  have hsumNat :
      ∑ p ∈ D, N0 / heathBrownDirectionHeight p ≤
        heathBrownPrimitiveLogRayMass N0 m1 m2 delta := by
    rw [heathBrownPrimitiveLogRayMass]
    exact Finset.sum_le_sum_of_subset hsub
  have hsum :
      ∑ p ∈ D, ((N0 / heathBrownDirectionHeight p : ℕ) : ℝ) ≤
        (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) := by
    exact_mod_cast hsumNat
  have hpoint : ∀ p ∈ D,
      ((N / heathBrownDirectionHeight p : ℕ) : ℝ) ≤
        x * (((N0 / heathBrownDirectionHeight p : ℕ) : ℝ) + 1) := by
    intro p hp
    exact cast_natDiv_le_realRatio_mul_natDiv_add_one hN0
      (heathBrownDirectionHeight_pos_of_mem (by simpa [D] using hp))
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hcard := card_heathBrownPrimitiveLogWindow_le hN hm1 hm2 hm hdelta0 hdelta1
  rw [heathBrownPrimitiveLogRayMass]
  push_cast
  calc
    (∑ p ∈ D, ((N / heathBrownDirectionHeight p : ℕ) : ℝ)) ≤
        ∑ p ∈ D, x * (((N0 / heathBrownDirectionHeight p : ℕ) : ℝ) + 1) := by
      exact Finset.sum_le_sum hpoint
    _ = x *
        ((∑ p ∈ D, ((N0 / heathBrownDirectionHeight p : ℕ) : ℝ)) + (D.card : ℝ)) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp
      ring
    _ ≤ x * ((heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
        (4 * delta * (N : ℝ) ^ (2 : ℕ) + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hx0
      exact add_le_add hsum (by simpa [D] using hcard)
    _ ≤ 4 * delta * (N : ℝ) ^ (2 : ℕ) +
        x * (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) + x := by
      have hx1 : x ≤ 1 := by
        dsimp [x]
        exact (div_le_one (by exact_mod_cast hN0)).mpr (by exact_mod_cast hNN0.le)
      have hpack0 : 0 ≤ 4 * delta * (N : ℝ) ^ (2 : ℕ) := by positivity
      nlinarith
    _ = 4 * delta * (N : ℝ) ^ (2 : ℕ) +
        ((N : ℝ) / (N0 : ℝ)) *
          (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
        (N : ℝ) / (N0 : ℝ) := by rfl

/-- Uniform real-ratio primitive-ray recurrence for every positive auxiliary scale. -/
theorem cast_heathBrownPrimitiveLogRayMass_le_twoScale_realRatio
    {N N0 : ℕ} (hN0 : 1 ≤ N0)
    {m1 m2 delta : ℝ} (hm1 : 0 < m1) (hm2 : 0 < m2) (hm : m2 ≤ m1)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1) :
    (heathBrownPrimitiveLogRayMass N m1 m2 delta : ℝ) ≤
      19 * delta * (N : ℝ) ^ (2 : ℕ) +
        (2 * (N : ℝ) / (N0 : ℝ)) *
          (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
        3 * (N : ℝ) / (N0 : ℝ) := by
  by_cases hNzero : N = 0
  · subst N
    rw [heathBrownPrimitiveLogRayMass_zero]
    norm_num
  have hN : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hNzero
  by_cases hN0N : N0 ≤ N
  · have hbase := cast_heathBrownPrimitiveLogRayMass_le_twoScale
      hN0 hN0N hm1 hm2 hm hdelta0 hdelta1
    have hdiv := (cast_div_bounds (n := N) (d := N0) (by omega)).1
    have hratio1 : (1 : ℝ) ≤ (N : ℝ) / (N0 : ℝ) := by
      rw [one_le_div (by exact_mod_cast hN0)]
      exact_mod_cast hN0N
    have hcoef1 : (((N / N0 + 1 : ℕ) : ℝ)) ≤
        2 * (N : ℝ) / (N0 : ℝ) := by
      push_cast
      calc
        ((N / N0 : ℕ) : ℝ) + 1 ≤ (N : ℝ) / (N0 : ℝ) + 1 :=
          by simpa [add_comm] using add_le_add_right hdiv 1
        _ ≤ 2 * ((N : ℝ) / (N0 : ℝ)) := by linarith
        _ = 2 * (N : ℝ) / (N0 : ℝ) := by ring
    have hcoef2 : (((2 * (N / N0) + 1 : ℕ) : ℝ)) ≤
        3 * (N : ℝ) / (N0 : ℝ) := by
      push_cast
      calc
        2 * ((N / N0 : ℕ) : ℝ) + 1 ≤
            2 * ((N : ℝ) / (N0 : ℝ)) + 1 := by linarith
        _ ≤ 3 * ((N : ℝ) / (N0 : ℝ)) := by linarith
        _ = 3 * (N : ℝ) / (N0 : ℝ) := by ring
    calc
      (heathBrownPrimitiveLogRayMass N m1 m2 delta : ℝ) ≤
          15 * delta * (N : ℝ) ^ (2 : ℕ) +
            ((N / N0 + 1 : ℕ) : ℝ) *
              (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
            ((2 * (N / N0) + 1 : ℕ) : ℝ) := hbase
      _ ≤ 15 * delta * (N : ℝ) ^ (2 : ℕ) +
            (2 * (N : ℝ) / (N0 : ℝ)) *
              (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
            3 * (N : ℝ) / (N0 : ℝ) := by gcongr
      _ ≤ 19 * delta * (N : ℝ) ^ (2 : ℕ) +
            (2 * (N : ℝ) / (N0 : ℝ)) *
              (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) +
            3 * (N : ℝ) / (N0 : ℝ) := by
        have hdiag0 : 0 ≤ delta * (N : ℝ) ^ (2 : ℕ) := by positivity
        linarith
  · exact (cast_heathBrownPrimitiveLogRayMass_le_realRatio_of_lt
        hN hN0 (Nat.lt_of_not_ge hN0N) hm1 hm2 hm hdelta0 hdelta1).trans
      (by
        have hratio0 : 0 ≤ (N : ℝ) / (N0 : ℝ) := by positivity
        have hmass0 : 0 ≤
            (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) := by positivity
        have hdiag0 : 0 ≤ delta * (N : ℝ) ^ (2 : ℕ) := by positivity
        have hmix0 : 0 ≤ (N : ℝ) / (N0 : ℝ) *
            (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) :=
          mul_nonneg hratio0 hmass0
        have hdiag : 4 * delta * (N : ℝ) ^ (2 : ℕ) ≤
            19 * delta * (N : ℝ) ^ (2 : ℕ) := by nlinarith
        have hcoef : (N : ℝ) / (N0 : ℝ) ≤ 2 * (N : ℝ) / (N0 : ℝ) := by
          calc
            (N : ℝ) / (N0 : ℝ) ≤ 2 * ((N : ℝ) / (N0 : ℝ)) := by linarith
            _ = 2 * (N : ℝ) / (N0 : ℝ) := by ring
        have hmix : (N : ℝ) / (N0 : ℝ) *
              (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) ≤
            (2 * (N : ℝ) / (N0 : ℝ)) *
              (heathBrownPrimitiveLogRayMass N0 m1 m2 delta : ℝ) :=
          mul_le_mul_of_nonneg_right hcoef hmass0
        have hratio : (N : ℝ) / (N0 : ℝ) ≤ 3 * (N : ℝ) / (N0 : ℝ) := by
          calc
            (N : ℝ) / (N0 : ℝ) ≤ 3 * ((N : ℝ) / (N0 : ℝ)) := by linarith
            _ = 3 * (N : ℝ) / (N0 : ℝ) := by ring
        linarith)

end

end RHTower.Sieve
