import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiGapScheduleMiddleGapLimit

/-!
# Quarter-wave packets for one-gap Fermi schedules

Any profile `y₀, …, y_L` is synthesized on every dyadic ray by the coefficients
`c(1) = y₀`, `c(2^(k+1)) = 2^(k+1) y_{k+1} - 2^k y_k`; above `L` the ray halves. If `y_k² ≤ 1`,
each ray carries physical sieve energy at least `(S - 2)/b²`, `S = Σ_{k≤L} y_k²`, and one-gap
energy at most `E/b²`, where `E` collects the base value, the observed jumps and the tail `y_L²/3`.

With the gap at level `h + 1` two quarter waves are ground modes of the two mixed chains:

* **bottom:** `y_k = sin((k+1)θ)` on the levels `k ≤ h`, zero above, `θ = π/(2h+3)`;
* **top:** `y_k = sin((L+1-k)θ')` on the levels `h < k ≤ L`, zero below, `θ' = π/(2(L-h)+1)`.

For `v_j = sin(jθ)` with `(2n+1)θ = π` the reflection `v_{n+1} = v_n` closes the chain at its
free end, and the recurrence `v_{j+1} + v_{j-1} = 2 cos θ v_j` gives jump energy exactly
`(2 - 2 cos θ)` times the mass `(2n+1)/4`. Hence

`K_{h+1}(N) ≥ ((2h+3)² - 8(2h+3))/π²` and `K_{h+1}(N) ≥ ((2(L-h)+1)² - 8(2(L-h)+1))/π²`,

matching the two-chain upper bound up to lower order.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Profile packets -/

/-- Dyadic coefficients whose normalized rays follow the profile `y₀, …, y_L`. -/
def fermiDyadicProfilePacket (L : ℕ) (y : ℕ → ℝ) (d : ℕ) : ℝ :=
  (if d = 1 then y 0 else 0) +
    ∑ k ∈ range L, if d = 2 ^ (k + 1) then (2 : ℝ) ^ (k + 1) * y (k + 1) - (2 : ℝ) ^ k * y k
    else 0

private theorem pow_dvd_odd_ray' (a k : ℕ) {b : ℕ} (hb : Odd b) :
    (2 : ℕ) ^ a ∣ 2 ^ k * b ↔ a ≤ k := by
  rw [(Nat.Coprime.pow_left a hb.coprime_two_left).dvd_mul_right,
    Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2 : ℕ))]

private theorem prefix_telescope' (L k : ℕ) (f : ℕ → ℝ) :
    f 0 + (∑ j ∈ range L, if j < k then f (j + 1) - f j else 0) = f (min L k) := by
  have hs : (range L).filter (fun j => j < k) = range (min L k) := by
    ext j; simp
  rw [← Finset.sum_filter, hs, Finset.sum_range_sub]
  ring

/-- On the ray over an odd base, the packet response is `2^min(k,L) y_{min(k,L)}`. -/
theorem sieveSeq_fermiDyadicProfilePacket_ray {L N : ℕ} (hLN : 2 ^ L ≤ N) (y : ℕ → ℝ) (k : ℕ)
    {b : ℕ} (hb : Odd b) :
    sieveSeq N (fermiDyadicProfilePacket L y) (2 ^ k * b) =
      (2 : ℝ) ^ (min L k) * y (min L k) := by
  have hN1 : 1 ≤ N := le_trans Nat.one_le_two_pow hLN
  unfold sieveSeq fermiDyadicProfilePacket
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_Icc]
  rw [if_pos ⟨⟨le_rfl, hN1⟩, one_dvd _⟩]
  let f := fun j : ℕ => (2 : ℝ) ^ j * y j
  have ht (j : ℕ) (hj : j ∈ range L) :
      (if (1 ≤ 2 ^ (j + 1) ∧ 2 ^ (j + 1) ≤ N) ∧ 2 ^ (j + 1) ∣ 2 ^ k * b then
        (2 : ℝ) ^ (j + 1) * y (j + 1) - (2 : ℝ) ^ j * y j
      else 0) = if j < k then f (j + 1) - f j else 0 := by
    have hjL := mem_range.mp hj
    have hle : 2 ^ (j + 1) ≤ N := le_trans (Nat.pow_le_pow_right (by norm_num) hjL) hLN
    have hpos : 1 ≤ 2 ^ (j + 1) := Nat.one_le_two_pow
    simp only [hle, hpos, true_and, pow_dvd_odd_ray' (j + 1) k hb,
      show j + 1 ≤ k ↔ j < k by omega]
    rfl
  rw [Finset.sum_congr rfl ht]
  have h0 : y 0 = f 0 := by simp [f]
  rw [h0, prefix_telescope']

private theorem packet_head {L N : ℕ} (hLN : 2 ^ L ≤ N) (y : ℕ → ℝ) {b : ℕ} (hb : Odd b)
    {k : ℕ} (hk : k ≤ L) :
    fermiNormalizedDyadicSieve N (fermiDyadicProfilePacket L y) b k = y k := by
  unfold fermiNormalizedDyadicSieve
  rw [sieveSeq_fermiDyadicProfilePacket_ray hLN y k hb, Nat.min_eq_right hk]
  field_simp

private theorem packet_tail {L N : ℕ} (hLN : 2 ^ L ≤ N) (y : ℕ → ℝ) {b : ℕ} (hb : Odd b)
    (j : ℕ) :
    fermiNormalizedDyadicSieve N (fermiDyadicProfilePacket L y) b (L + j) = y L / (2 : ℝ) ^ j := by
  unfold fermiNormalizedDyadicSieve
  rw [sieveSeq_fermiDyadicProfilePacket_ray hLN y (L + j) hb, Nat.min_eq_left (by omega), pow_add]
  field_simp

private theorem weight_ceiling' (k b : ℕ) (hb : 0 < b) :
    (b : ℝ) ^ 2 * fermiDyadicPronicWeight k b ≤ 1 := by
  have h := (fermiDyadicPronicWeight_bounds k b hb).2
  have hb2 : (0 : ℝ) < (b : ℝ) ^ 2 := by positivity
  rw [← le_div_iff₀' hb2]; simpa using h

/-- On every ray a bounded profile carries physical sieve energy at least `(S - 2)/b²`. -/
theorem fermiRaySieveEnergy_profilePacket_ge {L N : ℕ} (hLN : 2 ^ L ≤ N) (y : ℕ → ℝ)
    (hy : ∀ k ≤ L, y k ^ 2 ≤ 1) {b : ℕ} (hb : Odd b) :
    (∑ k ∈ range (L + 1), y k ^ 2) - 2 ≤
      (b : ℝ) ^ 2 * fermiRaySieveEnergy N (fermiDyadicProfilePacket L y) b := by
  have hb0 : 0 < b := hb.pos
  have hs := (fermiRay_weighted_summable N (fermiDyadicProfilePacket L y) hb0).1
  have hpart := hs.sum_le_tsum (range (L + 1))
    (fun k _ => mul_nonneg (sq_nonneg _) (fermiDyadicPronicWeight_nonneg _ _))
  unfold fermiRaySieveEnergy
  have hterm (k : ℕ) (hk : k ∈ range (L + 1)) :
      y k ^ 2 - 1 / (2 : ℝ) ^ k ≤ (b : ℝ) ^ 2 *
        (fermiNormalizedDyadicSieve N (fermiDyadicProfilePacket L y) b k ^ 2 *
          fermiDyadicPronicWeight k b) := by
    have hkL : k ≤ L := by have := mem_range.mp hk; omega
    rw [packet_head hLN y hb hkL]
    have hw := fermiDyadicPronicWeight_floor k b hb0
    have hp1 := hy k hkL
    have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hfrac : 1 - 1 / (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k / ((2 : ℝ) ^ k + 1) := by
      have he : (2 : ℝ) ^ k / ((2 : ℝ) ^ k + 1) = 1 - 1 / ((2 : ℝ) ^ k + 1) := by
        field_simp; ring
      have hi : 1 / ((2 : ℝ) ^ k + 1) ≤ 1 / (2 : ℝ) ^ k :=
        one_div_le_one_div_of_le h2 (by linarith)
      linarith
    have e1 := mul_le_mul_of_nonneg_left (hfrac.trans hw) (sq_nonneg (y k))
    have e2 : y k ^ 2 * (1 / (2 : ℝ) ^ k) ≤ 1 * (1 / (2 : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_right hp1 (by positivity)
    have e3 : (b : ℝ) ^ 2 * (y k ^ 2 * fermiDyadicPronicWeight k b) =
        y k ^ 2 * ((b : ℝ) ^ 2 * fermiDyadicPronicWeight k b) := by ring
    rw [e3]
    nlinarith
  have hgeom : (∑ k ∈ range (L + 1), 1 / (2 : ℝ) ^ k) ≤ 2 := by
    have := sum_geometric_two_le (L + 1)
    simpa [one_div, inv_pow] using this
  calc (∑ k ∈ range (L + 1), y k ^ 2) - 2
      ≤ ∑ k ∈ range (L + 1), (y k ^ 2 - 1 / (2 : ℝ) ^ k) := by
        rw [Finset.sum_sub_distrib]; linarith
    _ ≤ ∑ k ∈ range (L + 1), (b : ℝ) ^ 2 *
        (fermiNormalizedDyadicSieve N (fermiDyadicProfilePacket L y) b k ^ 2 *
          fermiDyadicPronicWeight k b) := Finset.sum_le_sum hterm
    _ = (b : ℝ) ^ 2 * ∑ k ∈ range (L + 1),
        fermiNormalizedDyadicSieve N (fermiDyadicProfilePacket L y) b k ^ 2 *
          fermiDyadicPronicWeight k b := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hpart (by positivity)

/-- On every ray the one-gap energy of a packet is at most `E/b²`, with
`E = y₀² + Σ_{k<L, k≠h} (y_k - y_{k+1})² + y_L²/3`. -/
theorem fermiRayGapEnergy_profilePacket_le {L N h : ℕ} (hLN : 2 ^ L ≤ N) (hhL : h < L)
    (y : ℕ → ℝ) {b : ℕ} (hb : Odd b) :
    (b : ℝ) ^ 2 * fermiRayGapEnergy N (fermiDyadicProfilePacket L y) b h ≤
      y 0 ^ 2 + (∑ k ∈ (range L).erase h, (y k - y (k + 1)) ^ 2) + y L ^ 2 / 3 := by
  have hb0 : 0 < b := hb.pos
  set c := fermiDyadicProfilePacket L y
  have hxy (k : ℕ) : fermiNormalizedDyadicJump N c b k =
      fermiNormalizedDyadicSieve N c b k - fermiNormalizedDyadicSieve N c b (k + 1) :=
    fermiNormalizedDyadicJump_eq_sub N c hb0 k
  have hs := (fermiRay_weighted_summable N c hb0).2
  have hxtail (j : ℕ) : fermiNormalizedDyadicJump N c b (j + L) = y L / (2 : ℝ) ^ (j + 1) := by
    rw [hxy, show j + L = L + j by ring, show L + j + 1 = L + (j + 1) by ring,
      packet_tail hLN y hb, packet_tail hLN y hb, pow_succ]
    field_simp; ring
  have hsq_tail : Summable (fun j : ℕ => (y L) ^ 2 / 4 * (1 / 4 : ℝ) ^ j) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have htail_val : ∑' j : ℕ, (y L) ^ 2 / 4 * (1 / 4 : ℝ) ^ j = y L ^ 2 / 3 := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    ring
  have hxtail_sq (j : ℕ) : fermiNormalizedDyadicJump N c b (j + L) ^ 2 =
      (y L) ^ 2 / 4 * (1 / 4 : ℝ) ^ j := by
    have h4 : ((2 : ℝ) ^ (j + 1)) ^ 2 = 4 * 4 ^ j := by
      rw [← pow_mul, show (j + 1) * 2 = 2 * j + 2 by ring, pow_add, pow_mul]
      norm_num; ring
    rw [hxtail, div_pow, h4, one_div_pow]
    field_simp
  set f : ℕ → ℝ := fun k => fermiNormalizedDyadicJump N c b k ^ 2 *
    fermiDyadicPronicWeight (k + 1) b with hf
  unfold fermiRayGapEnergy fermiRayAllBoundaryEnergy
  have hsplit := hs.sum_add_tsum_nat_add L
  have hfh : fermiNormalizedDyadicJump N c b h ^ 2 * fermiDyadicPronicWeight (h + 1) b = f h := rfl
  rw [hfh, ← hsplit, ← add_sum_erase (range L) f (mem_range.mpr hhL)]
  have hbase : (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b 0 ^ 2 *
      fermiDyadicPronicWeight 0 b) ≤ y 0 ^ 2 := by
    rw [packet_head hLN y hb (Nat.zero_le _)]
    have := weight_ceiling' 0 b hb0
    nlinarith [sq_nonneg (y 0)]
  have hhead : (b : ℝ) ^ 2 * ∑ k ∈ (range L).erase h, f k ≤
      ∑ k ∈ (range L).erase h, (y k - y (k + 1)) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hkL := mem_range.mp (mem_of_mem_erase hk)
    simp only [hf]
    rw [hxy, packet_head hLN y hb hkL.le, packet_head hLN y hb hkL]
    have := weight_ceiling' (k + 1) b hb0
    nlinarith [sq_nonneg (y k - y (k + 1))]
  have htail : (b : ℝ) ^ 2 * ∑' j : ℕ, f (j + L) ≤ y L ^ 2 / 3 := by
    rw [← tsum_mul_left, ← htail_val]
    refine Summable.tsum_le_tsum (fun j => ?_) (((summable_nat_add_iff L).mpr hs).mul_left _)
      hsq_tail
    simp only [hf]
    rw [← hxtail_sq j]
    have := weight_ceiling' (j + L + 1) b hb0
    nlinarith [sq_nonneg (fermiNormalizedDyadicJump N c b (j + L))]
  have e : (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b 0 ^ 2 * fermiDyadicPronicWeight 0 b +
      (f h + ∑ k ∈ (range L).erase h, f k + ∑' j, f (j + L)) - f h) =
      (b : ℝ) ^ 2 * (fermiNormalizedDyadicSieve N c b 0 ^ 2 * fermiDyadicPronicWeight 0 b) +
        (b : ℝ) ^ 2 * ∑ k ∈ (range L).erase h, f k + (b : ℝ) ^ 2 * ∑' j, f (j + L) := by ring
  rw [e]
  linarith

/-- **Packet ratio.** If the one-gap energy of a bounded packet is positive, the one-gap inverse
constant is at least `(S - 2)/E`. -/
theorem fermiGapInverseConstant_ge_profilePacket {L N h : ℕ} (hLN : 2 ^ L ≤ N) (hhL : h < L)
    (y : ℕ → ℝ) (hy : ∀ k ≤ L, y k ^ 2 ≤ 1)
    (hpos : 0 < fermiGapPronicEnergy N (fermiDyadicProfilePacket L y) (h + 1))
    {E : ℝ} (hE : 0 < E)
    (hEdef : y 0 ^ 2 + (∑ k ∈ (range L).erase h, (y k - y (k + 1)) ^ 2) + y L ^ 2 / 3 ≤ E) :
    ((∑ k ∈ range (L + 1), y k ^ 2) - 2) / E ≤ fermiGapInverseConstant N (h + 1) := by
  set c := fermiDyadicProfilePacket L y
  set S := ∑ k ∈ range (L + 1), y k ^ 2
  have hbdd : BddAbove (fermiGapRatios N (h + 1) Set.univ) :=
    ⟨fermiGapRayConstant N h 0, fun _ ht => fermiGapRatio_le N _ (Nat.zero_le h)
      (by have := Nat.le_log_of_pow_le (by norm_num) hLN; omega) ht⟩
  obtain ⟨hP, hPs⟩ := sieveTotalPronicEnergy_eq_sum_rays N c
  obtain ⟨hQ, hQs⟩ := fermiGapPronicEnergy_eq_sum_rays N c h
  have hodd (j : ℕ) : Odd (2 * j + 1) := ⟨j, rfl⟩
  have hkey : (S - 2) / E * fermiGapPronicEnergy N c (h + 1) ≤ sieveTotalPronicEnergy N c := by
    rw [hP, hQ, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun j => ?_) (hQs.mul_left _) hPs
    have hb2 : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have hPj := fermiRaySieveEnergy_profilePacket_ge hLN y hy (hodd j)
    have hQj := fermiRayGapEnergy_profilePacket_le hLN hhL y (hodd j)
    have hQnn := fermiRayGapEnergy_nonneg N c (by omega : 0 < 2 * j + 1) h
    rw [← mul_le_mul_iff_of_pos_left hb2]
    by_cases hS : S - 2 ≤ 0
    · have : (S - 2) / E * fermiRayGapEnergy N c (2 * j + 1) h ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hS hE.le) hQnn
      have hP0 : 0 ≤ fermiRaySieveEnergy N c (2 * j + 1) :=
        tsum_nonneg fun k => mul_nonneg (sq_nonneg _) (fermiDyadicPronicWeight_nonneg _ _)
      nlinarith
    · push Not at hS
      have hQE : ((2 * j + 1 : ℕ) : ℝ) ^ 2 * fermiRayGapEnergy N c (2 * j + 1) h ≤ E :=
        hQj.trans hEdef
      calc ((2 * j + 1 : ℕ) : ℝ) ^ 2 * ((S - 2) / E * fermiRayGapEnergy N c (2 * j + 1) h)
          = (S - 2) / E * (((2 * j + 1 : ℕ) : ℝ) ^ 2 * fermiRayGapEnergy N c (2 * j + 1) h) := by
            ring
        _ ≤ (S - 2) / E * E := mul_le_mul_of_nonneg_left hQE (by positivity)
        _ = S - 2 := by field_simp
        _ ≤ _ := hPj
  have hmem : sieveTotalPronicEnergy N c / fermiGapPronicEnergy N c (h + 1) ∈
      fermiGapRatios N (h + 1) Set.univ := ⟨c, Set.mem_univ _, hpos, rfl⟩
  calc (S - 2) / E ≤ sieveTotalPronicEnergy N c / fermiGapPronicEnergy N c (h + 1) := by
        rw [le_div_iff₀ hpos]; exact hkey
    _ ≤ _ := le_csSup hbdd hmem

/-! ### Quarter waves -/

private theorem two_sin_mul_sum_cos_even' (θ : ℝ) (n : ℕ) :
    2 * Real.sin θ * (∑ k ∈ range n, Real.cos (2 * ((k : ℝ) + 1) * θ)) =
      Real.sin ((2 * (n : ℝ) + 1) * θ) - Real.sin θ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h := Real.sin_sub_sin ((2 * ((n + 1 : ℕ) : ℝ) + 1) * θ) ((2 * (n : ℝ) + 1) * θ)
    have e1 : ((2 * ((n + 1 : ℕ) : ℝ) + 1) * θ - (2 * (n : ℝ) + 1) * θ) / 2 = θ := by
      push_cast; ring
    have e2 : ((2 * ((n + 1 : ℕ) : ℝ) + 1) * θ + (2 * (n : ℝ) + 1) * θ) / 2 =
        2 * ((n : ℝ) + 1) * θ := by push_cast; ring
    rw [e1, e2] at h
    linarith

/-- The quarter-wave angle `π/(2n+1)` of a mixed chain of length `n`. -/
def quarterWaveAngle (n : ℕ) : ℝ := Real.pi / (2 * (n : ℝ) + 1)

private theorem quarterWaveAngle_pos (n : ℕ) : 0 < quarterWaveAngle n := by
  unfold quarterWaveAngle; positivity

private theorem quarterWaveAngle_mul (n : ℕ) :
    (2 * (n : ℝ) + 1) * quarterWaveAngle n = Real.pi := by
  unfold quarterWaveAngle; field_simp

/-- **Quarter-wave mass.** `Σ_{j=1}^n sin²(jθ) = (2n+1)/4` for `θ = π/(2n+1)`, `n ≥ 1`. -/
theorem quarterWave_mass {n : ℕ} (hn : 1 ≤ n) :
    (∑ k ∈ range n, Real.sin (((k : ℝ) + 1) * quarterWaveAngle n) ^ 2) =
      (2 * (n : ℝ) + 1) / 4 := by
  set θ := quarterWaveAngle n
  have hθ := quarterWaveAngle_pos n
  have hπ := quarterWaveAngle_mul n
  have hθπ : θ < Real.pi := by
    have : (3 : ℝ) ≤ 2 * (n : ℝ) + 1 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    nlinarith [Real.pi_pos]
  have hsin : Real.sin θ ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hθ hθπ).ne'
  have hcos : (∑ k ∈ range n, Real.cos (2 * ((k : ℝ) + 1) * θ)) = -1 / 2 := by
    have h := two_sin_mul_sum_cos_even' θ n
    rw [hπ, Real.sin_pi] at h
    have : 2 * Real.sin θ * ((∑ k ∈ range n, Real.cos (2 * ((k : ℝ) + 1) * θ)) + 1 / 2) = 0 := by
      linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 (mul_ne_zero two_ne_zero hsin)
    · linarith
  have hsq (k : ℕ) : Real.sin (((k : ℝ) + 1) * θ) ^ 2 =
      1 / 2 - Real.cos (2 * ((k : ℝ) + 1) * θ) / 2 := by
    rw [show 2 * ((k : ℝ) + 1) * θ = 2 * (((k : ℝ) + 1) * θ) by ring, Real.cos_two_mul,
      Real.cos_sq']
    ring
  simp_rw [hsq]
  have hdiv : (∑ x ∈ range n, Real.cos (2 * ((x : ℝ) + 1) * θ) / 2) =
      (∑ x ∈ range n, Real.cos (2 * ((x : ℝ) + 1) * θ)) / 2 := (Finset.sum_div _ _ _).symm
  rw [Finset.sum_sub_distrib, hdiv, hcos, Finset.sum_const, Finset.card_range]
  simp
  ring

/-- **Quarter-wave energy.** With `v_j = sin(jθ)`, `θ = π/(2n+1)`, the chain pinned at `v₀ = 0`
and free at `n` has `Σ_{j<n} (v_{j+1} - v_j)² = (2 - 2 cos θ) Σ_{j<n} v_{j+1}²`. -/
theorem quarterWave_energy (n : ℕ) :
    (∑ j ∈ range n, (Real.sin (((j : ℝ) + 1) * quarterWaveAngle n) -
        Real.sin ((j : ℝ) * quarterWaveAngle n)) ^ 2) =
      (2 - 2 * Real.cos (quarterWaveAngle n)) *
        ∑ j ∈ range n, Real.sin (((j : ℝ) + 1) * quarterWaveAngle n) ^ 2 := by
  set θ := quarterWaveAngle n
  set v : ℕ → ℝ := fun j => Real.sin ((j : ℝ) * θ) with hv
  have hv0 : v 0 = 0 := by simp [hv]
  have hvs (j : ℕ) : Real.sin (((j : ℝ) + 1) * θ) = v (j + 1) := by simp [hv]
  have hvs' (j : ℕ) : Real.sin ((j : ℝ) * θ) = v j := rfl
  simp only [hvs, hvs']
  have hrec (j : ℕ) : v (j + 2) + v j = 2 * Real.cos θ * v (j + 1) := by
    simp only [hv]
    have h1 := Real.sin_add (((j + 1 : ℕ) : ℝ) * θ) θ
    have h2 := Real.sin_sub (((j + 1 : ℕ) : ℝ) * θ) θ
    rw [show ((j + 2 : ℕ) : ℝ) * θ = ((j + 1 : ℕ) : ℝ) * θ + θ by push_cast; ring,
      show (j : ℝ) * θ = ((j + 1 : ℕ) : ℝ) * θ - θ by push_cast; ring, h1, h2]
    ring
  -- the free end: `v_{n+1} = v_n`
  have hfree : v (n + 1) = v n := by
    simp only [hv]
    have hπ := quarterWaveAngle_mul n
    rw [show ((n + 1 : ℕ) : ℝ) * θ = Real.pi - (n : ℝ) * θ by push_cast; linarith,
      Real.sin_pi_sub]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set c := Real.cos θ
  set T := ∑ j ∈ range n, v (j + 1) ^ 2
  set A := ∑ j ∈ range n, v j * v (j + 1)
  have hTlow : (∑ j ∈ range n, v j ^ 2) = T - v n ^ 2 := by
    simp only [T]
    have h1 := Finset.sum_range_succ (fun j => v j ^ 2) n
    have h2 := Finset.sum_range_succ' (fun j => v j ^ 2) n
    rw [hv0] at h2
    linarith
  -- `2A = 2cT - v_n²` from the recurrence and the free end
  have hA : 2 * A = 2 * c * T - v n ^ 2 := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hA1 : A = ∑ j ∈ range m, v (j + 1) * v (j + 2) := by
      simp only [A]; rw [Finset.sum_range_succ', hv0]; simp
    have hA2 : (∑ j ∈ range m, v (j + 1) * v (j + 2)) =
        2 * c * (∑ j ∈ range m, v (j + 1) ^ 2) - ∑ j ∈ range m, v j * v (j + 1) := by
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun j _ => ?_
      have : v (j + 2) = 2 * c * v (j + 1) - v j := by linarith [hrec j]
      rw [this]; ring
    have hT' : (∑ j ∈ range m, v (j + 1) ^ 2) = T - v (m + 1) ^ 2 := by
      simp only [T]; rw [Finset.sum_range_succ]; ring
    have hA' : (∑ j ∈ range m, v j * v (j + 1)) = A - v m * v (m + 1) := by
      simp only [A]; rw [Finset.sum_range_succ]; ring
    have hend : v m = (2 * c - 1) * v (m + 1) := by
      have := hrec m
      rw [show m + 2 = m + 1 + 1 by ring, hfree] at this
      linarith
    rw [hA2, hT', hA', hend] at hA1
    linarith
  have hE : (∑ j ∈ range n, (v (j + 1) - v j) ^ 2) =
      T + (∑ j ∈ range n, v j ^ 2) - 2 * A := by
    simp only [T, A]
    rw [← sum_add_distrib, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by ring
  rw [hE, hTlow]
  linarith

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
