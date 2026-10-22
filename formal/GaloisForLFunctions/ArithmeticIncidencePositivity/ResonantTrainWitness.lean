import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeTowerEulerEnvelope

/-!
# The resonant train: the Euler envelope of a tower is attained

The tower law bounds the geometric lag charge of a test by the Euler envelope `z/(1−z) · A(0)`
minus a discount. This file supplies the matching witness: the **resonant train**, `M + 1` disjoint
copies of one bump at the spacing `L`,

    S = Σ_{k ≤ M} g(· + kL),      A_S(mL) = (M + 1 − m) A_g(0),

whose lag charge is `A_g(0) Σ_{m ≤ M} z^m (M + 1 − m)`, that is `(M+1)(z − z^{M+1})/(1−z)` times
`A_g(0)` up to the bounded correction `z/(1−z)²`. Since `A_S(0) = (M+1) A_g(0)`, the charge is a
fraction `z/(1−z) − z^{M+1}/(1−z) − z/((M+1)(1−z)²)` of the mass: the envelope is sharp, and its
extremal tests are the trains carried by a **multiplicative progression** `{1, p, p², …}` — at
`L = log p` the train sits on the tower of `p`. The content of the tower law is therefore its
discount, not its envelope.
-/

open MeasureTheory Set
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

variable {g : ℝ → ℝ}

/-- The resonant train: `M + 1` unit copies of `g` at the spacing `L`. -/
def resonantTrain (g : ℝ → ℝ) (L : ℝ) (M : ℕ) : ℝ → ℝ :=
  translateComb g (M + 1) (fun _ => 1) (fun k => (k : ℝ) * L)

/-- The autocorrelation of a bump vanishes at every nonzero multiple of a spacing exceeding its
diameter. -/
theorem autoCorr_eq_zero_of_mul_spacing {w L : ℝ} (hw : 0 ≤ w) (hL : 2 * w < L)
    (hsupp : ∀ x, w < |x| → g x = 0) {n : ℤ} (hn : n ≠ 0) :
    autoCorr g ((n : ℝ) * L) = 0 := by
  have hL0 : 0 < L := by linarith
  have habs : 1 ≤ |(n : ℝ)| := by
    have h1 : (1 : ℤ) ≤ |n| := Int.one_le_abs (by omega)
    have h2 : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h1
    rwa [Int.cast_abs, Int.cast_one] at h2
  refine autoCorr_eq_zero_of_support hsupp ?_
  rw [abs_mul, abs_of_pos hL0]
  calc 2 * w < L := hL
    _ = 1 * L := by ring
    _ ≤ |(n : ℝ)| * L := mul_le_mul_of_nonneg_right habs hL0.le

/-- **The autocorrelation of the resonant train.** At the lag `mL` the train correlates with itself
in exactly `M + 1 − m` of its `M + 1` copies. -/
theorem autoCorr_resonantTrain (hg : Continuous g) (hgc : HasCompactSupport g) {w L : ℝ}
    (hw : 0 ≤ w) (hL : 2 * w < L) (hsupp : ∀ x, w < |x| → g x = 0) (M m : ℕ) :
    autoCorr (resonantTrain g L M) ((m : ℝ) * L)
      = ((M + 1 - m : ℕ) : ℝ) * autoCorr g 0 := by
  have hgn : ContCompact g := ⟨hg, hgc⟩
  have hexp : autoCorr (resonantTrain g L M) ((m : ℝ) * L)
      = ∑ j ∈ Finset.range (M + 1), ∑ k ∈ Finset.range (M + 1),
          autoCorr g (((k : ℝ) * L + (m : ℝ) * L) - (j : ℝ) * L) := by
    rw [autoCorr_eq_testPairing,
      show resonantTrain g L M
        = translateComb g (M + 1) (fun _ => 1) (fun k => (k : ℝ) * L) from rfl,
      show (fun u => translateComb g (M + 1) (fun _ => 1) (fun k => (k : ℝ) * L)
            (u + (m : ℝ) * L))
          = translateComb g (M + 1) (fun _ => 1) (fun k => (k : ℝ) * L + (m : ℝ) * L) by
        funext u
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show u + (m : ℝ) * L + (k : ℝ) * L = u + ((k : ℝ) * L + (m : ℝ) * L) by ring],
      testPairing_comb hgn]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hrow : ∀ j ∈ Finset.range (M + 1),
      ∑ k ∈ Finset.range (M + 1),
          autoCorr g (((k : ℝ) * L + (m : ℝ) * L) - (j : ℝ) * L)
        = if m ≤ j then autoCorr g 0 else 0 := by
    intro j hj
    have hterm : ∀ k ∈ Finset.range (M + 1),
        autoCorr g (((k : ℝ) * L + (m : ℝ) * L) - (j : ℝ) * L)
          = if j = k + m then autoCorr g 0 else 0 := by
      intro k _
      by_cases h : j = k + m
      · rw [if_pos h, h]
        push_cast
        rw [show ((k : ℝ) * L + (m : ℝ) * L) - ((k : ℝ) + (m : ℝ)) * L = 0 by ring]
      · rw [if_neg h]
        have hne : ((k : ℤ) + (m : ℤ) - (j : ℤ)) ≠ 0 := fun hc => h (by omega)
        have hcast : ((k : ℝ) * L + (m : ℝ) * L) - (j : ℝ) * L
            = (((k : ℤ) + (m : ℤ) - (j : ℤ) : ℤ) : ℝ) * L := by push_cast; ring
        rw [hcast]
        exact autoCorr_eq_zero_of_mul_spacing hw hL hsupp hne
    rw [Finset.sum_congr rfl hterm]
    by_cases hmj : m ≤ j
    · rw [if_pos hmj]
      have hmem : j - m ∈ Finset.range (M + 1) := by
        rw [Finset.mem_range] at hj ⊢
        omega
      rw [Finset.sum_eq_single_of_mem (j - m) hmem (fun k _ hk => ?_)]
      · rw [if_pos (by omega : j = j - m + m)]
      · rw [if_neg (by omega : ¬ j = k + m)]
    · rw [if_neg hmj]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg (by omega : ¬ j = k + m)]
  have hfilter : (Finset.range (M + 1)).filter (fun j => m ≤ j) = Finset.Ico m (M + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hexp, Finset.sum_congr rfl hrow, ← Finset.sum_filter, hfilter, Finset.sum_const,
    Nat.card_Ico, nsmul_eq_mul]

/-- The mass of the resonant train is `M + 1` times the mass of its bump. -/
theorem autoCorr_resonantTrain_zero (hg : Continuous g) (hgc : HasCompactSupport g) {w L : ℝ}
    (hw : 0 ≤ w) (hL : 2 * w < L) (hsupp : ∀ x, w < |x| → g x = 0) (M : ℕ) :
    autoCorr (resonantTrain g L M) 0 = ((M : ℝ) + 1) * autoCorr g 0 := by
  have h := autoCorr_resonantTrain hg hgc hw hL hsupp M 0
  rw [Nat.cast_zero, zero_mul] at h
  rw [h]
  norm_num

/-- **The Euler envelope is attained.** The geometric lag charge of the resonant train is

    A_g(0) Σ_{m ≤ M} z^m (M + 1 − m) ≥ (M+1)(z − z^{M+1})/(1−z) · A_g(0) − z/(1−z)² · A_g(0),

so, against its mass `(M+1) A_g(0)`, the train charges the fraction
`z/(1−z) − z^{M+1}/(1−z) − z/((M+1)(1−z)²)` of its mass: the envelope `z/(1−z)` of the tower law is
sharp. -/
theorem geoLagCharge_resonantTrain_ge (hg : Continuous g) (hgc : HasCompactSupport g) {w L z : ℝ}
    (hw : 0 ≤ w) (hL : 2 * w < L) (hsupp : ∀ x, w < |x| → g x = 0) (hz0 : 0 < z) (hz1 : z < 1)
    (M : ℕ) :
    (((M : ℝ) + 1) * ((z - z ^ (M + 1)) / (1 - z)) - z / (1 - z) ^ 2) * autoCorr g 0
      ≤ geoLagCharge z L (resonantTrain g L M) := by
  have hA0 : 0 ≤ autoCorr g 0 := autoCorr_zero_nonneg hg hgc
  have hz1' : (0 : ℝ) < 1 - z := by linarith
  -- the charge is the finite sum of the train's correlations
  have hcharge : geoLagCharge z L (resonantTrain g L M)
      = ∑ m ∈ Finset.range M, z ^ (m + 1) * (((M - m : ℕ) : ℝ) * autoCorr g 0) := by
    rw [geoLagCharge]
    refine tsum_eq_sum ?_ |>.trans (Finset.sum_congr rfl fun m hm => ?_) |>.trans rfl
    · intro m hm
      have hmM : M ≤ m := by
        rcases Nat.lt_or_ge m M with h | h
        · exact absurd (Finset.mem_range.mpr h) hm
        · exact h
      have harg : (((m : ℝ) + 1)) * L = ((m + 1 : ℕ) : ℝ) * L := by push_cast; ring
      rw [harg, autoCorr_resonantTrain hg hgc hw hL hsupp M (m + 1),
        show M + 1 - (m + 1) = 0 by omega]
      norm_num
    · have harg : (((m : ℝ) + 1)) * L = ((m + 1 : ℕ) : ℝ) * L := by push_cast; ring
      rw [harg, autoCorr_resonantTrain hg hgc hw hL hsupp M (m + 1),
        show M + 1 - (m + 1) = M - m by omega]
  -- the scalar estimate
  have hgeo : ∑ m ∈ Finset.range M, z ^ (m + 1) * ((M : ℝ) - (m : ℝ))
      = ((M : ℝ) + 1) * ((z - z ^ (M + 1)) / (1 - z))
        - ∑ m ∈ Finset.range M, ((m : ℝ) + 1) * z ^ (m + 1) := by
    have hsum : ∑ m ∈ Finset.range M, z ^ (m + 1) = (z - z ^ (M + 1)) / (1 - z) := by
      have h := geom_sum_mul z M
      have hz : ∑ m ∈ Finset.range M, z ^ (m + 1) = z * ∑ m ∈ Finset.range M, z ^ m := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring
      have hgs : ∑ m ∈ Finset.range M, z ^ m = (1 - z ^ M) / (1 - z) := by
        rw [eq_div_iff (ne_of_gt hz1')]
        linear_combination -h
      rw [hz, hgs]
      field_simp
      ring
    rw [← hsum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    ring
  have hlin : ∑ m ∈ Finset.range M, ((m : ℝ) + 1) * z ^ (m + 1) ≤ z / (1 - z) ^ 2 := by
    have hnorm : ‖z‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hz0]; exact hz1
    have hsum0 : Summable fun n : ℕ => (n : ℝ) * z ^ n := by
      have h := summable_pow_mul_geometric_of_norm_lt_one (k := 1) (r := z) hnorm
      simpa [pow_one] using h
    have hsummable : Summable fun n : ℕ => ((n : ℝ) + 1) * z ^ (n + 1) := by
      have h := (summable_nat_add_iff 1).mpr hsum0
      exact h.congr fun n => by push_cast; ring
    have hnn : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) * z ^ (n + 1) := fun n => by positivity
    refine le_trans (hsummable.sum_le_tsum _ (fun n _ => hnn n)) ?_
    have hzero : ∑' n : ℕ, (n : ℝ) * z ^ n = ∑' n : ℕ, ((n : ℝ) + 1) * z ^ (n + 1) := by
      rw [hsum0.tsum_eq_zero_add]
      simp only [Nat.cast_zero, zero_mul, zero_add]
      exact tsum_congr fun n => by push_cast; ring
    rw [← hzero, tsum_coe_mul_geometric_of_norm_lt_one hnorm]
  rw [hcharge]
  have hrw : ∑ m ∈ Finset.range M, z ^ (m + 1) * (((M - m : ℕ) : ℝ) * autoCorr g 0)
      = (∑ m ∈ Finset.range M, z ^ (m + 1) * ((M : ℝ) - (m : ℝ))) * autoCorr g 0 := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmM : m < M := Finset.mem_range.mp hm
    rw [show (((M - m : ℕ) : ℝ)) = (M : ℝ) - (m : ℝ) by
      have : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM.le
      push_cast [Nat.cast_sub hmM.le]
      ring]
    ring
  rw [hrw, hgeo]
  have hstep : ((M : ℝ) + 1) * ((z - z ^ (M + 1)) / (1 - z)) - z / (1 - z) ^ 2
      ≤ ((M : ℝ) + 1) * ((z - z ^ (M + 1)) / (1 - z))
        - ∑ m ∈ Finset.range M, ((m : ℝ) + 1) * z ^ (m + 1) := by
    linarith only [hlin]
  exact mul_le_mul_of_nonneg_right hstep hA0

/-! ### The coupling weight `½` is sharp -/

/-- Away from the lattice of multiples of the spacing the train has no correlation. -/
theorem autoCorr_resonantTrain_eq_zero (hg : Continuous g) (hgc : HasCompactSupport g) {w L : ℝ}
    (hw : 0 ≤ w) (M : ℕ) (hsupp : ∀ x, w < |x| → g x = 0) {t : ℝ}
    (ht : ∀ n : ℤ, 2 * w < |t + (n : ℝ) * L|) :
    autoCorr (resonantTrain g L M) t = 0 := by
  have hgn : ContCompact g := ⟨hg, hgc⟩
  rw [autoCorr_eq_testPairing,
    show resonantTrain g L M
      = translateComb g (M + 1) (fun _ => 1) (fun k => (k : ℝ) * L) from rfl,
    show (fun u => translateComb g (M + 1) (fun _ => 1) (fun k => (k : ℝ) * L) (u + t))
        = translateComb g (M + 1) (fun _ => 1) (fun k => (k : ℝ) * L + t) by
      funext u
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show u + t + (k : ℝ) * L = u + ((k : ℝ) * L + t) by ring],
    testPairing_comb hgn]
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
  have hcast : (k : ℝ) * L + t - (j : ℝ) * L = t + (((k : ℤ) - (j : ℤ) : ℤ) : ℝ) * L := by
    push_cast
    ring
  rw [hcast, autoCorr_eq_zero_of_support hsupp (ht _)]
  ring

/-- **The coupling weight `½` is sharp.** For every `θ > ½` the one-parameter coupling law fails,
on the train resonant at `b = L` and blind at `a = L/2`: the admissible range of the edge weight of
the coupling graph is exactly `[0, ½]`. -/
theorem exists_resonantTrain_coupling_fails (hg : Continuous g) (hgc : HasCompactSupport g)
    {w L : ℝ} (hw : 0 ≤ w) (hwL : 4 * w < L) (hsupp : ∀ x, w < |x| → g x = 0)
    (hpos : 0 < autoCorr g 0) {θ : ℝ} (hθ : 1 / 2 < θ) :
    ∃ M : ℕ, autoCorr (resonantTrain g L M) 0
        + θ * (autoCorr (resonantTrain g L M) (L / 2 + L)
          + autoCorr (resonantTrain g L M) (L / 2 - L))
      < autoCorr (resonantTrain g L M) (L / 2) + 2 * θ * autoCorr (resonantTrain g L M) L := by
  have hL0 : 0 < L := by linarith
  have hwL' : 2 * w < L := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℕ, 1 / (2 * θ - 1) < (M : ℝ) := exists_nat_gt _
  refine ⟨M, ?_⟩
  -- the three blind lags: `L/2`, `3L/2` and `−L/2` are all at distance `≥ L/2 > 2w` from the lattice
  have hblind : ∀ c : ℝ, (∃ i : ℤ, c = (2 * (i : ℝ) + 1) * (L / 2)) →
      autoCorr (resonantTrain g L M) c = 0 := by
    intro c hc
    obtain ⟨i, hi⟩ := hc
    refine autoCorr_resonantTrain_eq_zero hg hgc hw M hsupp fun n => ?_
    have hval : c + (n : ℝ) * L = (2 * ((i : ℝ) + (n : ℝ)) + 1) * (L / 2) := by
      rw [hi]; ring
    rw [hval, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < L / 2)]
    have hodd : 1 ≤ |2 * ((i : ℝ) + (n : ℝ)) + 1| := by
      have hz : ((2 * (i + n) + 1 : ℤ) : ℝ) = 2 * ((i : ℝ) + (n : ℝ)) + 1 := by push_cast; ring
      have h1 : (1 : ℤ) ≤ |2 * (i + n) + 1| := Int.one_le_abs (by omega)
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|2 * (i + n) + 1| : ℤ) : ℝ) := by exact_mod_cast h1
      rwa [Int.cast_abs, Int.cast_one, hz] at h2
    nlinarith [hodd]
  have h1 : autoCorr (resonantTrain g L M) (L / 2) = 0 := hblind _ ⟨0, by push_cast; ring⟩
  have h2 : autoCorr (resonantTrain g L M) (L / 2 + L) = 0 := hblind _ ⟨1, by push_cast; ring⟩
  have h3 : autoCorr (resonantTrain g L M) (L / 2 - L) = 0 := hblind _ ⟨-1, by push_cast; ring⟩
  have h4 : autoCorr (resonantTrain g L M) L = (M : ℝ) * autoCorr g 0 := by
    have h := autoCorr_resonantTrain hg hgc hw hwL' hsupp M 1
    rw [Nat.cast_one, one_mul] at h
    rw [h, show M + 1 - 1 = M by omega]
  have h0 : autoCorr (resonantTrain g L M) 0 = ((M : ℝ) + 1) * autoCorr g 0 :=
    autoCorr_resonantTrain_zero hg hgc hw hwL' hsupp M
  rw [h0, h1, h2, h3, h4]
  have h2θ : (0 : ℝ) < 2 * θ - 1 := by linarith
  have hMpos : 0 < (M : ℝ) := lt_trans (div_pos one_pos h2θ) hM
  have hkey : (M : ℝ) + 1 < 2 * θ * (M : ℝ) := by
    rw [div_lt_iff₀ (by linarith)] at hM
    nlinarith [hM]
  nlinarith [hkey, hpos]

end GaloisForLFunctions.ArithmeticIncidencePositivity
