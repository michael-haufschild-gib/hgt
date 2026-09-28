import GaloisForLFunctions.RHTower.BohrMoments
import GaloisForLFunctions.RHTower.Sieve.JutilaLocalLargeValues
import GaloisForLFunctions.RHTower.Sieve.HuxleyDirichletLargeValues
import GaloisForLFunctions.RHTower.Sieve.HuxleyExplicitLargeValues

/-!
# Counting separated large values of a real-coefficient Dirichlet polynomial

For `F(t) = Σ_{n ∈ S} b_n n^{-it}` with real `b` and a `1`-separated set `W` of diameter at most `D`
on which `|F| ≥ V`, this file records the two counts consumed by zero-density arguments, both in
terms of the mass `G = Σ_{n ∈ S} b_n²`:

* **mean value theorem** (`S ⊆ [1, L]`):
  `#W·V² ≤ (D + 1 + 4L(1 + log L))(1 + 2 log L)·G`;
* **Huxley** (`S ⊆ [N, 2N)`, `G(1 + 1536√(3N/4π)) ≤ V²/3`):
  `#W·V² ≤ (D(1284G)²/V⁴ + 1)·2G(N + 12πN(1 + log(D + 1)))`.

A range `[A, A·2^ℓ)` is split into `ℓ` dyadic blocks.  Some block carries `V/ℓ` at every point,
so the Huxley count applies blockwise.
-/

namespace RHTower

noncomputable section

open Complex Finset RHTower.Sieve
open scoped InnerProductSpace

/-- The coefficients of `F` as a complex sequence vanishing off `S`. -/
def dpolySupportCoeff (b : ℕ → ℝ) (S : Finset ℕ) : ℕ → ℂ := fun n => if n ∈ S then (b n : ℂ) else 0

theorem dpoly_eq_sum_Ico_dpolySupportCoeff {b : ℕ → ℝ} {S : Finset ℕ} {A B : ℕ} (hS : S ⊆ Ico A B)
    (t : ℝ) :
    dpoly b S t = ∑ n ∈ Ico A B, dpolySupportCoeff b S n *
      Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I) := by
  unfold dpoly dpolySupportCoeff
  rw [← Finset.sum_subset hS]
  · refine sum_congr rfl fun n hn => ?_
    rw [if_pos hn, cterm]
    congr 1
    push_cast
    ring_nf
  · intro n _ hn
    rw [if_neg hn, zero_mul]

theorem sum_normSq_dpolySupportCoeff {b : ℕ → ℝ} {S : Finset ℕ} {A B : ℕ} (hS : S ⊆ Ico A B) :
    ∑ n ∈ Ico A B, ‖dpolySupportCoeff b S n‖ ^ 2 = ∑ n ∈ S, (b n) ^ 2 := by
  unfold dpolySupportCoeff
  rw [← Finset.sum_subset hS]
  · refine sum_congr rfl fun n hn => ?_
    rw [if_pos hn, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · intro n _ hn
    rw [if_neg hn, norm_zero]
    norm_num

/-! ## The mean value count -/

/-- `F` as a `dirPoly` of length `L`, up to complex conjugation. -/
theorem norm_dpoly_eq_norm_dirPoly {b : ℕ → ℝ} {S : Finset ℕ} {L : ℕ} (hS : S ⊆ Icc 1 L)
    (t : ℝ) :
    ‖dpoly b S t‖ = ‖dirPoly L (fun m : Fin L => dpolySupportCoeff b S ((m : ℕ) + 1)) t‖ := by
  have hS' : S ⊆ Ico 1 (L + 1) := by
    intro n hn
    have := mem_Icc.mp (hS hn)
    rw [mem_Ico]
    omega
  rw [dpoly_eq_sum_Ico_dpolySupportCoeff hS' t]
  have hdir : dirPoly L (fun m : Fin L => dpolySupportCoeff b S ((m : ℕ) + 1)) t
      = (starRingEnd ℂ) (∑ n ∈ Ico 1 (L + 1), dpolySupportCoeff b S n *
          Complex.exp (((-(t * Real.log (n : ℝ)) : ℝ) : ℂ) * Complex.I)) := by
    rw [map_sum, Finset.sum_Ico_eq_sum_range, show L + 1 - 1 = L by omega, dirPoly,
      ← Fin.sum_univ_eq_sum_range (fun k : ℕ => (starRingEnd ℂ) (dpolySupportCoeff b S (1 + k) *
        Complex.exp (((-(t * Real.log ((1 + k : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I))) L]
    refine sum_congr rfl fun m _ => ?_
    have hc : (starRingEnd ℂ) (dpolySupportCoeff b S (1 + (m : ℕ))) = dpolySupportCoeff b S ((m : ℕ) + 1) := by
      unfold dpolySupportCoeff
      rw [show 1 + (m : ℕ) = (m : ℕ) + 1 by ring]
      split_ifs <;> simp
    rw [map_mul, hc, ← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    congr 2
    push_cast
    ring_nf
  rw [hdir, Complex.norm_conj]

/-- **The mean value count.** -/
theorem card_mul_sq_le_of_dpoly_large_mvt {b : ℕ → ℝ} {S : Finset ℕ} {L : ℕ} (hL : 2 ≤ L)
    (hS : S ⊆ Icc 1 L) {W : Finset ℝ} {D V : ℝ} (hD : 0 ≤ D)
    (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x - y|) (hdiam : ∀ x ∈ W, ∀ y ∈ W, |x - y| ≤ D)
    (hbig : ∀ t ∈ W, V ≤ ‖dpoly b S t‖) (hV : 0 ≤ V) :
    (W.card : ℝ) * V ^ 2
      ≤ (D + 1 + 4 * (L : ℝ) * (1 + Real.log L)) * (1 + 2 * Real.log L) * ∑ n ∈ S, (b n) ^ 2 := by
  set a : Fin L → ℂ := fun m => dpolySupportCoeff b S ((m : ℕ) + 1) with ha
  have hmvt := sum_normSq_dirPoly_finset_le L hL a hD hsep hdiam
  have hmass : ∑ m : Fin L, ‖a m‖ ^ (2 : ℕ) = ∑ n ∈ S, (b n) ^ 2 := by
    have hS' : S ⊆ Ico 1 (L + 1) := by
      intro n hn
      have := mem_Icc.mp (hS hn)
      rw [mem_Ico]
      omega
    rw [← sum_normSq_dpolySupportCoeff hS', Finset.sum_Ico_eq_sum_range, show L + 1 - 1 = L by omega,
      ← Fin.sum_univ_eq_sum_range (fun k : ℕ => ‖dpolySupportCoeff b S (1 + k)‖ ^ 2) L]
    refine sum_congr rfl fun m _ => ?_
    simp only [ha, add_comm]
  rw [hmass] at hmvt
  refine le_trans ?_ hmvt
  calc (W.card : ℝ) * V ^ 2 = ∑ _t ∈ W, V ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ t ∈ W, ‖dirPoly L a t‖ ^ (2 : ℕ) := by
        refine sum_le_sum fun t ht => ?_
        rw [← norm_dpoly_eq_norm_dirPoly hS t]
        exact pow_le_pow_left₀ hV (hbig t ht) 2

/-! ## The Huxley count on a dyadic block -/

theorem dpoly_eq_blockPoly {b : ℕ → ℝ} {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Ico N (2 * N)) (t : ℝ) :
    dpoly b S t = blockPoly N (dpolySupportCoeff b S) 0 t := by
  rw [dpoly_eq_sum_Ico_dpolySupportCoeff hS t, blockPoly]
  refine sum_congr rfl fun n _ => ?_
  simp

/-- **The Huxley count on a dyadic block.** -/
theorem card_mul_sq_le_of_dpoly_large_huxley {b : ℕ → ℝ} {S : Finset ℕ} {N : ℕ} (hN : 1 ≤ N)
    (hS : S ⊆ Ico N (2 * N)) {W : Finset ℝ} {D V G : ℝ} (hD : 0 ≤ D) (hV : 0 < V)
    (hG : ∑ n ∈ S, (b n) ^ 2 ≤ G)
    (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x - y|) (hdiam : ∀ x ∈ W, ∀ y ∈ W, |x - y| ≤ D)
    (hbig : ∀ t ∈ W, V ≤ ‖dpoly b S t‖)
    (hthresh : G * (1 + 1536 * Real.sqrt (3 * (N : ℝ) / (4 * Real.pi))) ≤ V ^ 2 / 3) :
    (W.card : ℝ) * V ^ 2
      ≤ (D * (1284 * G) ^ 2 / V ^ 4 + 1) *
          (2 * G * ((N : ℝ) + 12 * Real.pi * (N : ℝ) * (1 + Real.log (D + 1)))) := by
  have hmass : ‖blockCoeff N (dpolySupportCoeff b S) 0‖ ^ (2 : ℕ) ≤ G := by
    rw [norm_blockCoeff_sq]
    have h := sum_normSq_dpolySupportCoeff (b := b) hS
    simp only [neg_zero, Real.rpow_zero, one_pow, mul_one]
    linarith
  have hbig' : ∀ t ∈ W, V ≤ ‖⟪dyadicDirRow N t, blockCoeff N (dpolySupportCoeff b S) 0⟫_ℂ‖ := by
    intro t ht
    rw [inner_dyadicDirRow_blockCoeff, ← dpoly_eq_blockPoly hS]
    exact hbig t ht
  have h := huxley_large_values_finset_explicit_energy hN (blockCoeff N (dpolySupportCoeff b S) 0)
    (by norm_num : (0 : ℝ) < 1) hV hD hmass W hsep hdiam hbig' hthresh
  simpa [div_one] using h

/-! ## Splitting a range into dyadic blocks -/

/-- The `r`-th dyadic block `{n ∈ S : ⌊log₂(n/A)⌋ = r}` of a support starting at `A`. -/
def rangeBlock (S : Finset ℕ) (A r : ℕ) : Finset ℕ :=
  S.filter (fun n => Nat.log 2 (n / A) = r)

theorem rangeBlock_subset {S : Finset ℕ} {A : ℕ} (hA : 0 < A) (hS : ∀ n ∈ S, A ≤ n) (r : ℕ) :
    rangeBlock S A r ⊆ Ico (A * 2 ^ r) (2 * (A * 2 ^ r)) := by
  intro n hn
  rw [rangeBlock, mem_filter] at hn
  obtain ⟨hnS, hr⟩ := hn
  have hq1 : 1 ≤ n / A := (Nat.one_le_div_iff hA).mpr (hS n hnS)
  have hlow := Nat.pow_log_le_self 2 (by omega : n / A ≠ 0)
  have hhigh := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (n / A)
  rw [hr] at hlow hhigh
  rw [mem_Ico]
  constructor
  · calc A * 2 ^ r ≤ A * (n / A) := Nat.mul_le_mul_left _ hlow
      _ ≤ n := Nat.mul_div_le n A
  · calc n < A * (n / A + 1) := Nat.lt_mul_div_succ n hA
      _ ≤ A * 2 ^ (r + 1) := Nat.mul_le_mul_left _ hhigh
      _ = 2 * (A * 2 ^ r) := by ring

theorem dpoly_eq_sum_rangeBlock {b : ℕ → ℝ} {S : Finset ℕ} {A ℓ : ℕ} (hA : 0 < A)
    (hS : ∀ n ∈ S, A ≤ n ∧ n < A * 2 ^ ℓ) (t : ℝ) :
    dpoly b S t = ∑ r ∈ range ℓ, dpoly b (rangeBlock S A r) t := by
  classical
  have hmaps : ∀ n ∈ S, Nat.log 2 (n / A) ∈ range ℓ := by
    intro n hn
    obtain ⟨h1, h2⟩ := hS n hn
    have hq1 : 1 ≤ n / A := (Nat.one_le_div_iff hA).mpr h1
    have hq : n / A < 2 ^ ℓ := by
      rw [Nat.div_lt_iff_lt_mul hA]
      linarith [h2]
    rw [mem_range]
    exact (Nat.log_lt_iff_lt_pow (by norm_num) (by omega)).mpr hq
  unfold dpoly rangeBlock
  rw [Finset.sum_fiberwise_of_maps_to hmaps]

/-- **The Huxley count on a range of `ℓ` dyadic blocks.**  If every block satisfies the Huxley
threshold at level `V/ℓ` with mass bound `G` and length at most `N₀`, then
`#W·(V/ℓ)² ≤ ℓ·(D(1284G)²/(V/ℓ)⁴ + 1)·2G(N₀ + 12πN₀(1 + log(D+1)))`. -/
theorem card_mul_sq_le_of_dpoly_large_huxley_range {b : ℕ → ℝ} {S : Finset ℕ} {A ℓ : ℕ}
    (hA : 1 ≤ A) (hℓ : 1 ≤ ℓ) (hS : ∀ n ∈ S, A ≤ n ∧ n < A * 2 ^ ℓ)
    {W : Finset ℝ} {D V G N₀ : ℝ} (hD : 0 ≤ D) (hV : 0 < V)
    (hG : ∑ n ∈ S, (b n) ^ 2 ≤ G) (hN₀ : ∀ r < ℓ, ((A * 2 ^ r : ℕ) : ℝ) ≤ N₀)
    (hsep : ∀ x ∈ W, ∀ y ∈ W, x ≠ y → 1 ≤ |x - y|) (hdiam : ∀ x ∈ W, ∀ y ∈ W, |x - y| ≤ D)
    (hbig : ∀ t ∈ W, V ≤ ‖dpoly b S t‖)
    (hthresh : G * (1 + 1536 * Real.sqrt (3 * N₀ / (4 * Real.pi))) ≤ (V / ℓ) ^ 2 / 3) :
    (W.card : ℝ) * (V / ℓ) ^ 2
      ≤ ℓ * ((D * (1284 * G) ^ 2 / (V / ℓ) ^ 4 + 1) *
          (2 * G * (N₀ + 12 * Real.pi * N₀ * (1 + Real.log (D + 1))))) := by
  classical
  have hA0 : 0 < A := by omega
  have hℓR : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hVl : 0 < V / ℓ := div_pos hV hℓR
  have hG0 : 0 ≤ G := le_trans (sum_nonneg fun n _ => sq_nonneg (b n)) hG
  -- every point has a large block
  have hpick : ∀ t ∈ W, ∃ r ∈ range ℓ, V / ℓ ≤ ‖dpoly b (rangeBlock S A r) t‖ := by
    intro t ht
    have h := hbig t ht
    rw [dpoly_eq_sum_rangeBlock hA0 hS t] at h
    by_contra hcon
    push Not at hcon
    have hlt : ∑ r ∈ range ℓ, ‖dpoly b (rangeBlock S A r) t‖ < ∑ _r ∈ range ℓ, V / ℓ :=
      Finset.sum_lt_sum_of_nonempty (by simp; omega) hcon
    have hsum : ∑ _r ∈ range ℓ, V / (ℓ : ℝ) = V := by
      rw [sum_const, card_range, nsmul_eq_mul]
      field_simp
    linarith [norm_sum_le (range ℓ) (fun r => dpoly b (rangeBlock S A r) t)]
  have hcover : W ⊆ (range ℓ).biUnion
      (fun r => W.filter (fun t => V / ℓ ≤ ‖dpoly b (rangeBlock S A r) t‖)) := by
    intro t ht
    obtain ⟨r, hr, hrt⟩ := hpick t ht
    exact mem_biUnion.mpr ⟨r, hr, mem_filter.mpr ⟨ht, hrt⟩⟩
  set E : ℝ := (D * (1284 * G) ^ 2 / (V / ℓ) ^ 4 + 1) *
    (2 * G * (N₀ + 12 * Real.pi * N₀ * (1 + Real.log (D + 1)))) with hE
  have hblock : ∀ r ∈ range ℓ,
      ((W.filter (fun t => V / ℓ ≤ ‖dpoly b (rangeBlock S A r) t‖)).card : ℝ) * (V / ℓ) ^ 2
        ≤ E := by
    intro r hr
    have hr' := mem_range.mp hr
    have hN1 : 1 ≤ A * 2 ^ r := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hsub := rangeBlock_subset hA0 (fun n hn => (hS n hn).1) r
    have hGr : ∑ n ∈ rangeBlock S A r, (b n) ^ 2 ≤ G :=
      le_trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ S)
        (fun n _ _ => sq_nonneg (b n))) hG
    have hNr := hN₀ r hr'
    have hthr : G * (1 + 1536 * Real.sqrt (3 * ((A * 2 ^ r : ℕ) : ℝ) / (4 * Real.pi)))
        ≤ (V / ℓ) ^ 2 / 3 := by
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hG0) hthresh
      gcongr
    have h := card_mul_sq_le_of_dpoly_large_huxley hN1 hsub hD hVl hGr
      (fun x hx y hy hxy => hsep x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 hxy)
      (fun x hx y hy => hdiam x (mem_filter.mp hx).1 y (mem_filter.mp hy).1)
      (fun t ht => (mem_filter.mp ht).2) hthr
    have hlog : 0 ≤ 1 + Real.log (D + 1) := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ D + 1 by linarith)]
    refine le_trans h ?_
    rw [hE]
    gcongr
  calc (W.card : ℝ) * (V / ℓ) ^ 2
      ≤ ((range ℓ).biUnion
          (fun r => W.filter (fun t => V / ℓ ≤ ‖dpoly b (rangeBlock S A r) t‖))).card
          * (V / ℓ) ^ 2 := by
        gcongr
    _ ≤ (∑ r ∈ range ℓ,
          ((W.filter (fun t => V / ℓ ≤ ‖dpoly b (rangeBlock S A r) t‖)).card : ℝ)) * (V / ℓ) ^ 2 := by
        gcongr
        exact_mod_cast card_biUnion_le
    _ = ∑ r ∈ range ℓ,
          ((W.filter (fun t => V / ℓ ≤ ‖dpoly b (rangeBlock S A r) t‖)).card : ℝ) * (V / ℓ) ^ 2 := by
        rw [sum_mul]
    _ ≤ ∑ _r ∈ range ℓ, E := sum_le_sum hblock
    _ = ℓ * E := by rw [sum_const, card_range, nsmul_eq_mul]

end

end RHTower
