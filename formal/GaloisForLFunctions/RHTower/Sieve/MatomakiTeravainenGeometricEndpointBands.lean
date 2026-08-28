import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenMinimalGeometricRooted

/-!
# Rounded geometric endpoint bands

Two successor-width factors absorb all natural endpoint rounding in initial, terminal, and
internal geometric collars.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

theorem mtGeometricInitialEndpoint_band
    {delta width : ℝ} (hdelta : 0 ≤ delta) {start z₀ : ℕ}
    (hz₀ : 1 ≤ z₀)
    (hprogress : 1 ≤ delta * ((z₀ - 1 : ℕ) : ℝ))
    (hQ : mtGeometricLevel delta start 0 ≤ (z₀ : ℝ) * (1 + delta))
    (hwidth : (1 + delta) ^ 2 ≤ 1 + width) :
    ((mtMinimalGeometricEndpoint delta start 0 - 1 : ℕ) : ℝ) ≤
      (1 + width) * ((z₀ - 1 : ℕ) : ℝ) := by
  have hzCast : (z₀ : ℝ) = ((z₀ - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hz₀]
    push_cast
    ring
  have hzStep : (z₀ : ℝ) ≤ (1 + delta) * ((z₀ - 1 : ℕ) : ℝ) := by
    rw [hzCast]
    nlinarith
  have hdeltaOne : 0 ≤ 1 + delta := by linarith
  have hdeltaPos : 0 < delta := by
    nlinarith [show (0 : ℝ) ≤ ((z₀ - 1 : ℕ) : ℝ) from Nat.cast_nonneg _]
  calc
    ((mtMinimalGeometricEndpoint delta start 0 - 1 : ℕ) : ℝ) =
        (Nat.floor (mtGeometricLevel delta start 0) : ℝ) := by
      simp [mtMinimalGeometricEndpoint, mtRealBlockEndpoint]
    _ ≤ mtGeometricLevel delta start 0 :=
      Nat.floor_le (mtGeometricLevel_pos hdeltaPos start 0).le
    _ ≤ (z₀ : ℝ) * (1 + delta) := hQ
    _ ≤ ((1 + delta) * ((z₀ - 1 : ℕ) : ℝ)) * (1 + delta) :=
      mul_le_mul_of_nonneg_right hzStep hdeltaOne
    _ = (1 + delta) ^ 2 * ((z₀ - 1 : ℕ) : ℝ) := by ring
    _ ≤ (1 + width) * ((z₀ - 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hwidth (Nat.cast_nonneg _)

theorem mtGeometricTerminalEndpoint_band
    {delta width : ℝ} (hdelta : 0 < delta) {start z₀ z₁ : ℕ}
    (hz₀ : 1 ≤ z₀) (hz₀z₁ : z₀ ≤ z₁)
    (hroot : mtGeometricLevel delta start 0 < (z₁ : ℝ))
    (hprogress : 1 ≤ delta * ((z₀ - 1 : ℕ) : ℝ))
    (hwidth : (1 + delta) ^ 2 ≤ 1 + width) :
    let t := mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta
    ((mtMinimalGeometricEndpoint delta start t - 1 : ℕ) : ℝ) ≤
      (1 + width) * ((z₁ - 1 : ℕ) : ℝ) := by
  dsimp only
  let t := mtMinimalGeometricDepth delta start (z₁ : ℝ) hdelta
  have ht : 0 < t := mtMinimalGeometricDepth_pos hdelta start hroot
  obtain ⟨k, hk⟩ : ∃ k, t = k + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  have hklt : k < t := by omega
  have hprev : mtGeometricLevel delta start k < (z₁ : ℝ) :=
    mtGeometricLevel_lt_of_lt_minimalDepth hdelta start (z₁ : ℝ) hklt
  have hsub : z₀ - 1 ≤ z₁ - 1 := Nat.sub_le_sub_right hz₀z₁ 1
  have hprogressRoot : 1 ≤ delta * ((z₁ - 1 : ℕ) : ℝ) :=
    hprogress.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hsub) hdelta.le)
  have hz₁One : 1 ≤ z₁ := hz₀.trans hz₀z₁
  have hz₁Cast : (z₁ : ℝ) = ((z₁ - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hz₁One]
    push_cast
    ring
  have hz₁Step : (z₁ : ℝ) ≤ (1 + delta) * ((z₁ - 1 : ℕ) : ℝ) := by
    rw [hz₁Cast]
    nlinarith
  have hlevel : mtGeometricLevel delta start t < (z₁ : ℝ) * (1 + delta) := by
    rw [hk, mtGeometricLevel_succ_eq]
    exact mul_lt_mul_of_pos_right hprev (by linarith)
  calc
    ((mtMinimalGeometricEndpoint delta start t - 1 : ℕ) : ℝ) =
        (Nat.floor (mtGeometricLevel delta start t) : ℝ) := by
      simp [mtMinimalGeometricEndpoint, mtRealBlockEndpoint]
    _ ≤ mtGeometricLevel delta start t :=
      Nat.floor_le (mtGeometricLevel_pos hdelta start t).le
    _ ≤ (z₁ : ℝ) * (1 + delta) := hlevel.le
    _ ≤ ((1 + delta) * ((z₁ - 1 : ℕ) : ℝ)) * (1 + delta) :=
      mul_le_mul_of_nonneg_right hz₁Step (by linarith)
    _ = (1 + delta) ^ 2 * ((z₁ - 1 : ℕ) : ℝ) := by ring
    _ ≤ (1 + width) * ((z₁ - 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hwidth (Nat.cast_nonneg _)

theorem mtMinimalGeometricBlock_lower_le
    {delta : ℝ} (hdelta : 0 < delta) {start : ℕ}
    {t : ℕ} (i : Fin t) {q : ℕ}
    (hq : q ∈ mtAdjacentPrimeBlock (mtMinimalGeometricEndpoint delta start) i) :
    mtMinimalGeometricEndpoint delta start i.1 ≤ q := by
  have hqReal := (mem_mtAdjacentPrimeBlock_real_iff
    (mtGeometricLevel delta start)
    (fun j => (mtGeometricLevel_pos hdelta start j).le) i q).mp hq
  have hfloor : Nat.floor (mtGeometricLevel delta start i.1) < q :=
    (Nat.floor_lt (mtGeometricLevel_pos hdelta start i.1).le).mpr hqReal.1
  simp only [mtMinimalGeometricEndpoint, mtRealBlockEndpoint]
  omega

theorem mtMinimalGeometricBlock_band
    {delta width : ℝ} (hdelta : 0 < delta) {start z₀ : ℕ}
    (hz₀ : 1 ≤ z₀)
    (hz₀Endpoint : z₀ ≤ mtMinimalGeometricEndpoint delta start 0)
    (hprogress : 1 ≤ delta * ((z₀ - 1 : ℕ) : ℝ))
    (hwidth : (1 + delta) ^ 2 ≤ 1 + width)
    {t : ℕ} (i : Fin t) {q : ℕ}
    (hq : q ∈ mtAdjacentPrimeBlock (mtMinimalGeometricEndpoint delta start) i) :
    ((q - 1 : ℕ) : ℝ) ≤
      (1 + width) *
        ((mtMinimalGeometricEndpoint delta start i.1 - 1 : ℕ) : ℝ) := by
  let endpoint := mtMinimalGeometricEndpoint delta start
  have hmono := mtMinimalGeometricEndpoint_monotone hdelta start
  have hz₀i : z₀ ≤ endpoint i.1 := hz₀Endpoint.trans (hmono (Nat.zero_le i.1))
  have hsub : z₀ - 1 ≤ endpoint i.1 - 1 := Nat.sub_le_sub_right hz₀i 1
  have hprogressI : 1 ≤ delta * ((endpoint i.1 - 1 : ℕ) : ℝ) :=
    hprogress.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hsub) hdelta.le)
  have hiOne : 1 ≤ endpoint i.1 := hz₀.trans hz₀i
  have hiCast : (endpoint i.1 : ℝ) =
      ((endpoint i.1 - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub hiOne]
    push_cast
    ring
  have hiStep : (endpoint i.1 : ℝ) ≤
      (1 + delta) * ((endpoint i.1 - 1 : ℕ) : ℝ) := by
    rw [hiCast]
    nlinarith
  have hqReal := (mem_mtAdjacentPrimeBlock_real_iff
    (mtGeometricLevel delta start)
    (fun j => (mtGeometricLevel_pos hdelta start j).le) i q).mp hq
  have hQiEndpoint : mtGeometricLevel delta start i.1 < (endpoint i.1 : ℝ) := by
    dsimp [endpoint, mtMinimalGeometricEndpoint, mtRealBlockEndpoint]
    simpa only [Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (mtGeometricLevel delta start i.1)
  have hnext : mtGeometricLevel delta start (i.1 + 1) =
      mtGeometricLevel delta start i.1 * (1 + delta) :=
    mtGeometricLevel_succ_eq delta start i.1
  have hqNext : (q : ℝ) ≤
      mtGeometricLevel delta start i.1 * (1 + delta) := by
    simpa only [hnext] using hqReal.2.1
  calc
    ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.sub_le q 1
    _ ≤ mtGeometricLevel delta start i.1 * (1 + delta) := hqNext
    _ ≤ (endpoint i.1 : ℝ) * (1 + delta) :=
      mul_le_mul_of_nonneg_right hQiEndpoint.le (by linarith)
    _ ≤ ((1 + delta) * ((endpoint i.1 - 1 : ℕ) : ℝ)) * (1 + delta) :=
      mul_le_mul_of_nonneg_right hiStep (by linarith)
    _ = (1 + delta) ^ 2 * ((endpoint i.1 - 1 : ℕ) : ℝ) := by ring
    _ ≤ (1 + width) * ((endpoint i.1 - 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hwidth (Nat.cast_nonneg _)

end

end RHTower.Sieve
