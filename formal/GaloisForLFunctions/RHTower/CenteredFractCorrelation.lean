import Mathlib

/-!
# Correlations of the centred fractional part

Let `ψ(x) = {x} - ½`.  For integers `m, m' ≥ 1`,
`∫_0^1 ψ(m x) ψ(m' x) dx = gcd(m, m')² / (12 m m')`.

The proof is elementary.  Hermite's identity `Σ_{a<N} ⌊y + a/N⌋ = ⌊Ny⌋` gives the distribution
relation `Σ_{a<N} ψ(y + a/N) = ψ(Ny)`.  The autocorrelation `∫_0^1 ψ(y)ψ(y + c) dy =
c²/2 - c/2 + 1/12` (`0 ≤ c < 1`) is a two-piece polynomial integral; summing it over `c = a/N`
gives `∫_0^1 ψ(y)ψ(Ny) dy = 1/(12N)`.  For coprime `u, v` the distribution relation and a
permutation of residues reduce `∫ψ(uy)ψ(vy)` to `∫ψ(y)ψ(uvy)`, and a common factor `g` is removed
by periodicity.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace RHTower

noncomputable section

/-- The centred fractional part `ψ(x) = {x} - ½`. -/
def centeredFract (x : ℝ) : ℝ := Int.fract x - 1 / 2

theorem centeredFract_periodic : Function.Periodic centeredFract 1 := fun x => by
  simp [centeredFract, Int.fract_add_one]

theorem centeredFract_add_intCast (x : ℝ) (m : ℤ) : centeredFract (x + m) = centeredFract x := by
  simp [centeredFract, Int.fract_add_intCast]

theorem measurable_centeredFract : Measurable centeredFract :=
  measurable_fract.sub_const _

theorem abs_centeredFract_le (x : ℝ) : |centeredFract x| ≤ 1 / 2 := by
  unfold centeredFract
  have h0 := Int.fract_nonneg x
  have h1 := Int.fract_lt_one x
  rw [abs_le]; constructor <;> linarith

/-- Products of centred fractional parts at linear arguments are interval integrable. -/
theorem intervalIntegrable_centeredFract_mul (α β γ δ : ℝ) (a b : ℝ) :
    IntervalIntegrable (fun y => centeredFract (α * y + β) * centeredFract (γ * y + δ))
      volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => (1 / 4 : ℝ))
    intervalIntegrable_const ?_ ?_
  · exact ((measurable_centeredFract.comp ((measurable_const_mul α).add_const β)).mul
      (measurable_centeredFract.comp ((measurable_const_mul γ).add_const δ))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    dsimp only
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := abs_centeredFract_le (α * y + β)
    have h2 := abs_centeredFract_le (γ * y + δ)
    have := mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    linarith

/-- **Hermite's identity.**  `Σ_{a<N} ⌊y + a/N⌋ = ⌊Ny⌋` for `N ≥ 1`. -/
theorem sum_floor_add_div_eq_floor_mul {N : ℕ} (hN : 1 ≤ N) (y : ℝ) :
    ∑ a ∈ Finset.range N, ⌊y + (a : ℝ) / N⌋ = ⌊(N : ℝ) * y⌋ := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set F : ℝ → ℝ := fun y => (∑ a ∈ Finset.range N, (⌊y + (a : ℝ) / N⌋ : ℝ))
    - (⌊(N : ℝ) * y⌋ : ℝ) with hF
  have hper : Function.Periodic F (1 / N) := by
    intro y
    simp only [hF]
    have h1 : ∑ a ∈ Finset.range N, (⌊y + 1 / N + (a : ℝ) / N⌋ : ℝ)
        = ∑ a ∈ Finset.range N, (⌊y + (a : ℝ) / N⌋ : ℝ) + 1 := by
      have e : ∀ a : ℕ, y + 1 / N + (a : ℝ) / N = y + ((a + 1 : ℕ) : ℝ) / N := fun a => by
        push_cast; ring
      simp_rw [e]
      have h2 := Finset.sum_range_succ (fun a : ℕ => (⌊y + (a : ℝ) / N⌋ : ℝ)) N
      have h3 := Finset.sum_range_succ' (fun a : ℕ => (⌊y + (a : ℝ) / N⌋ : ℝ)) N
      have h4 : (⌊y + (N : ℝ) / N⌋ : ℝ) = ⌊y⌋ + 1 := by
        rw [div_self hN0.ne', Int.floor_add_one]; push_cast; ring
      have h5 : (⌊y + ((0 : ℕ) : ℝ) / N⌋ : ℝ) = ⌊y⌋ := by simp
      linarith
    have h6 : (⌊(N : ℝ) * (y + 1 / N)⌋ : ℝ) = ⌊(N : ℝ) * y⌋ + 1 := by
      rw [mul_add, mul_one_div_cancel hN0.ne', Int.floor_add_one]; push_cast; ring
    rw [h1, h6]; ring
  have hzero : ∀ s : ℝ, 0 ≤ s → s < 1 / N → F s = 0 := by
    intro s hs0 hs1
    simp only [hF]
    have h1 : ∀ a ∈ Finset.range N, (⌊s + (a : ℝ) / N⌋ : ℝ) = 0 := by
      intro a ha
      have ha' : (a : ℝ) ≤ N - 1 := by
        have := Finset.mem_range.mp ha
        have : (a : ℝ) + 1 ≤ N := by exact_mod_cast this
        linarith
      have h2 : ⌊s + (a : ℝ) / N⌋ = 0 := by
        rw [Int.floor_eq_zero_iff]
        constructor
        · positivity
        · have : (a : ℝ) / N ≤ (N - 1) / N := div_le_div_of_nonneg_right ha' hN0.le
          have e : (N - 1 : ℝ) / N = 1 - 1 / N := by field_simp
          linarith
      rw [h2]; simp
    have h3 : ⌊(N : ℝ) * s⌋ = 0 := by
      rw [Int.floor_eq_zero_iff]
      constructor
      · positivity
      · have := mul_lt_mul_of_pos_left hs1 hN0
        rwa [mul_one_div_cancel hN0.ne'] at this
    rw [Finset.sum_eq_zero h1, h3]; simp
  -- reduce `y` to `[0, 1/N)`
  set j := ⌊(N : ℝ) * y⌋ with hj
  have hs : y - (j : ℝ) * (1 / (N : ℝ)) ∈ Set.Ico (0 : ℝ) (1 / (N : ℝ)) := by
    have h1 := Int.floor_le ((N : ℝ) * y)
    have h2 := Int.lt_floor_add_one ((N : ℝ) * y)
    rw [← hj] at h1 h2
    constructor
    · rw [sub_nonneg, mul_one_div, div_le_iff₀ hN0]; linarith
    · rw [sub_lt_iff_lt_add]
      have e : 1 / (N : ℝ) + (j : ℝ) * (1 / (N : ℝ)) = ((j : ℝ) + 1) / N := by ring
      rw [e, lt_div_iff₀ hN0]; linarith
  have hFy : F y = 0 := by
    rw [← hper.sub_int_mul_eq j]
    exact hzero _ hs.1 hs.2
  simp only [hF, sub_eq_zero] at hFy
  exact_mod_cast hFy

/-- **The distribution relation.**  `Σ_{a<N} ψ(y + a/N) = ψ(Ny)` for `N ≥ 1`. -/
theorem sum_centeredFract_add_div {N : ℕ} (hN : 1 ≤ N) (y : ℝ) :
    ∑ a ∈ Finset.range N, centeredFract (y + (a : ℝ) / N) = centeredFract ((N : ℝ) * y) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hH := sum_floor_add_div_eq_floor_mul hN y
  have hHR : ∑ a ∈ Finset.range N, (⌊y + (a : ℝ) / N⌋ : ℝ) = (⌊(N : ℝ) * y⌋ : ℝ) := by
    exact_mod_cast hH
  unfold centeredFract
  simp only [Int.fract]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hHR, Finset.sum_add_distrib,
    ← Finset.sum_div]
  have hs : ∑ a ∈ Finset.range N, (a : ℝ) = (N : ℝ) * (N - 1) / 2 := by
    have := Finset.sum_range_id_mul_two N
    have h2 : ((∑ i ∈ Finset.range N, i : ℕ) : ℝ) * 2 = (N : ℝ) * ((N - 1 : ℕ) : ℝ) := by
      exact_mod_cast this
    push_cast at h2
    rw [Nat.cast_sub hN] at h2
    push_cast at h2
    linarith
  rw [hs]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-- **The autocorrelation.**  `∫_0^1 ψ(y) ψ(y + c) dy = c²/2 - c/2 + 1/12` for `0 ≤ c < 1`. -/
theorem integral_centeredFract_mul_add {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    ∫ y in (0 : ℝ)..1, centeredFract y * centeredFract (y + c) = c ^ 2 / 2 - c / 2 + 1 / 12 := by
  have hint := intervalIntegrable_centeredFract_mul 1 0 1 c
  simp only [one_mul, add_zero] at hint
  rw [← integral_add_adjacent_intervals (hint 0 (1 - c)) (hint (1 - c) 1)]
  have hae : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 1 - c := by
    rw [ae_iff]; simp
  have h1 : ∫ y in (0 : ℝ)..(1 - c), centeredFract y * centeredFract (y + c)
      = ∫ y in (0 : ℝ)..(1 - c), (y - 1 / 2) * (y + c - 1 / 2) := by
    refine integral_congr_ae (hae.mono fun y hy hmem => ?_)
    rw [uIoc_of_le (by linarith)] at hmem
    have hy1 : y < 1 - c := lt_of_le_of_ne hmem.2 hy
    unfold centeredFract
    rw [Int.fract_eq_self.mpr ⟨hmem.1.le, by linarith⟩,
      Int.fract_eq_self.mpr ⟨by linarith [hmem.1], by linarith⟩]
  have hae1 : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ 1 := by
    rw [ae_iff]; simp
  have h2 : ∫ y in (1 - c)..1, centeredFract y * centeredFract (y + c)
      = ∫ y in (1 - c)..1, (y - 1 / 2) * (y + c - 3 / 2) := by
    refine integral_congr_ae (hae1.mono fun y hy hmem => ?_)
    rw [uIoc_of_le (by linarith)] at hmem
    have hy1 : y < 1 := lt_of_le_of_ne hmem.2 hy
    unfold centeredFract
    have e : y + c = (y + c - 1) + ((1 : ℤ) : ℝ) := by push_cast; ring
    rw [Int.fract_eq_self.mpr ⟨by linarith [hmem.1], hy1⟩, e,
      Int.fract_add_intCast, Int.fract_eq_self.mpr ⟨by linarith [hmem.1], by linarith⟩]
    ring
  rw [h1, h2]
  have d1 : ∀ y ∈ uIcc (0 : ℝ) (1 - c), HasDerivAt
      (fun y : ℝ => y ^ 3 / 3 + (c - 1) * y ^ 2 / 2 - (c - 1 / 2) * y / 2)
      ((y - 1 / 2) * (y + c - 1 / 2)) y := by
    intro y _
    have := ((((hasDerivAt_pow 3 y).div_const 3).add (((hasDerivAt_pow 2 y).const_mul
      (c - 1)).div_const 2)).sub (((hasDerivAt_id y).const_mul (c - 1 / 2)).div_const 2))
    refine this.congr_deriv ?_
    simp; ring
  have d2 : ∀ y ∈ uIcc (1 - c) 1, HasDerivAt
      (fun y : ℝ => y ^ 3 / 3 + (c - 2) * y ^ 2 / 2 - (c - 3 / 2) * y / 2)
      ((y - 1 / 2) * (y + c - 3 / 2)) y := by
    intro y _
    have := ((((hasDerivAt_pow 3 y).div_const 3).add (((hasDerivAt_pow 2 y).const_mul
      (c - 2)).div_const 2)).sub (((hasDerivAt_id y).const_mul (c - 3 / 2)).div_const 2))
    refine this.congr_deriv ?_
    simp; ring
  rw [integral_eq_sub_of_hasDerivAt d1 (Continuous.intervalIntegrable (by fun_prop) _ _),
    integral_eq_sub_of_hasDerivAt d2 (Continuous.intervalIntegrable (by fun_prop) _ _)]
  ring


/-- `Σ_{a < N} a² = (N - 1) N (2N - 1)/6`. -/
theorem sum_range_natCast_sq_closed (N : ℕ) :
    ∑ a ∈ Finset.range N, ((a : ℝ)) ^ 2 = ((N : ℝ) - 1) * N * (2 * N - 1) / 6 := by
  induction N with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `Σ_{a < N} a = (N - 1) N/2`. -/
theorem sum_range_natCast_closed (N : ℕ) :
    ∑ a ∈ Finset.range N, (a : ℝ) = ((N : ℝ) - 1) * N / 2 := by
  induction N with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- **`∫_0^1 ψ(y) ψ(Ny) dy = 1/(12N)`** for `N ≥ 1`. -/
theorem integral_centeredFract_mul_nat {N : ℕ} (hN : 1 ≤ N) :
    ∫ y in (0 : ℝ)..1, centeredFract y * centeredFract ((N : ℝ) * y) = 1 / (12 * N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : ∀ y, centeredFract y * centeredFract ((N : ℝ) * y)
      = ∑ a ∈ Finset.range N, centeredFract y * centeredFract (y + (a : ℝ) / N) := by
    intro y; rw [← Finset.mul_sum, sum_centeredFract_add_div hN]
  simp_rw [h1]
  rw [intervalIntegral.integral_finsetSum fun a _ => by
    have := intervalIntegrable_centeredFract_mul 1 0 1 ((a : ℝ) / N) 0 1
    simpa using this]
  have h2 : ∀ a ∈ Finset.range N, ∫ y in (0 : ℝ)..1, centeredFract y * centeredFract
      (y + (a : ℝ) / N) = ((a : ℝ) / N) ^ 2 / 2 - ((a : ℝ) / N) / 2 + 1 / 12 := by
    intro a ha
    have ha' : (a : ℝ) < N := by exact_mod_cast Finset.mem_range.mp ha
    exact integral_centeredFract_mul_add (by positivity) (by rw [div_lt_one hN0]; exact ha')
  rw [Finset.sum_congr rfl h2]
  have e : ∑ a ∈ Finset.range N, (((a : ℝ) / N) ^ 2 / 2 - ((a : ℝ) / N) / 2 + 1 / 12)
      = (∑ a ∈ Finset.range N, (a : ℝ) ^ 2) / (2 * N ^ 2)
        - (∑ a ∈ Finset.range N, (a : ℝ)) / (2 * N) + N / 12 := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_div]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    congr 1
    · congr 1
      · exact Finset.sum_congr rfl fun a _ => by field_simp
      · exact Finset.sum_congr rfl fun a _ => by field_simp
    · ring
  rw [e, sum_range_natCast_sq_closed, sum_range_natCast_closed]
  field_simp
  ring

/-- `Σ_{a<u} ψ(w - v a/u) = ψ(u w)` for coprime `u ≥ 1`, `v`. -/
theorem sum_centeredFract_sub_mul_div {u v : ℕ} (hu : 1 ≤ u) (huv : Nat.Coprime u v) (w : ℝ) :
    ∑ a ∈ Finset.range u, centeredFract (w - (v : ℝ) * a / u) = centeredFract ((u : ℝ) * w) := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have huz : (0 : ℤ) < u := by exact_mod_cast hu
  set r : ℕ → ℕ := fun a => ((-((v : ℤ) * a)) % (u : ℤ)).toNat with hr
  have hr_lt : ∀ a, r a < u := by
    intro a
    have h1 := Int.emod_nonneg (-((v : ℤ) * a)) huz.ne'
    have h2 := Int.emod_lt_of_pos (-((v : ℤ) * a)) huz
    simp only [hr]; omega
  have hr_cast : ∀ a, ((r a : ℕ) : ℤ) = (-((v : ℤ) * a)) % (u : ℤ) := by
    intro a
    have h1 := Int.emod_nonneg (-((v : ℤ) * a)) huz.ne'
    simp only [hr]; omega
  -- each term only depends on the residue
  have hterm : ∀ a : ℕ,
      centeredFract (w - (v : ℝ) * a / u) = centeredFract (w + (r a : ℝ) / u) := by
    intro a
    set k := (-((v : ℤ) * a)) / (u : ℤ) with hk
    have hdiv : (-((v : ℤ) * a)) = (u : ℤ) * k + (r a : ℤ) := by
      rw [hr_cast a, hk]; exact (Int.mul_ediv_add_emod _ _).symm
    have hreal : -((v : ℝ) * a) = (u : ℝ) * k + (r a : ℝ) := by exact_mod_cast hdiv
    have e : w - (v : ℝ) * a / u = (w + (r a : ℝ) / u) + (k : ℝ) := by
      field_simp
      linarith
    rw [e, centeredFract_add_intCast]
  -- `r` permutes `range u`
  have hinj : Set.InjOn r (Finset.range u : Set ℕ) := by
    intro a ha b hb hab
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    have h1 : (-((v : ℤ) * a)) % (u : ℤ) = (-((v : ℤ) * b)) % (u : ℤ) := by
      rw [← hr_cast a, ← hr_cast b, hab]
    have h2 : (u : ℤ) ∣ (v : ℤ) * ((b : ℤ) - a) := by
      have := Int.ModEq.dvd h1
      have e : -((v : ℤ) * b) - -((v : ℤ) * a) = -((v : ℤ) * ((b : ℤ) - a)) := by ring
      rw [e, dvd_neg] at this
      exact this
    have h3 : (u : ℤ) ∣ (b : ℤ) - a :=
      Int.dvd_of_dvd_mul_right_of_gcd_one h2 (by exact_mod_cast huv)
    obtain ⟨t, ht⟩ := h3
    have : t = 0 := by
      by_contra htne
      have h5 : (u : ℤ) ≤ |(b : ℤ) - a| := by
        rw [ht, abs_mul, abs_of_pos huz]
        have : 1 ≤ |t| := Int.one_le_abs htne
        nlinarith
      have h6 : |(b : ℤ) - a| < u := by
        rw [abs_sub_lt_iff]; constructor <;> omega
      linarith
    rw [this, mul_zero, sub_eq_zero] at ht
    exact_mod_cast ht.symm
  have himage : (Finset.range u).image r = Finset.range u := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro b hb
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_range.mpr (hr_lt a)
    · rw [Finset.card_image_of_injOn hinj]
  calc ∑ a ∈ Finset.range u, centeredFract (w - (v : ℝ) * a / u)
      = ∑ a ∈ Finset.range u, centeredFract (w + (r a : ℝ) / u) :=
        Finset.sum_congr rfl fun a _ => hterm a
    _ = ∑ b ∈ (Finset.range u).image r, centeredFract (w + (b : ℝ) / u) :=
        (Finset.sum_image (f := fun b : ℕ => centeredFract (w + (b : ℝ) / u)) hinj).symm
    _ = ∑ b ∈ Finset.range u, centeredFract (w + (b : ℝ) / u) := by rw [himage]
    _ = centeredFract ((u : ℝ) * w) := sum_centeredFract_add_div hu w

/-- **Coprime correlations.**  `∫_0^1 ψ(u y) ψ(v y) dy = 1/(12uv)` for coprime `u, v ≥ 1`. -/
theorem integral_centeredFract_mul_coprime {u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v)
    (huv : Nat.Coprime u v) :
    ∫ y in (0 : ℝ)..1, centeredFract ((u : ℝ) * y) * centeredFract ((v : ℝ) * y)
      = 1 / (12 * ((u * v : ℕ) : ℝ)) := by
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have h1 : ∀ y, centeredFract ((u : ℝ) * y) * centeredFract ((v : ℝ) * y)
      = ∑ a ∈ Finset.range u, centeredFract (y + (a : ℝ) / u) * centeredFract ((v : ℝ) * y) := by
    intro y; rw [← Finset.sum_mul, sum_centeredFract_add_div hu]
  simp_rw [h1]
  rw [intervalIntegral.integral_finsetSum fun a _ => by
    have := intervalIntegrable_centeredFract_mul 1 ((a : ℝ) / u) (v : ℝ) 0 0 1
    simpa using this]
  set H : ℕ → ℝ → ℝ := fun a z =>
    centeredFract z * centeredFract ((v : ℝ) * z - (v : ℝ) * a / u) with hH
  have h2 : ∀ a ∈ Finset.range u,
      ∫ y in (0 : ℝ)..1, centeredFract (y + (a : ℝ) / u) * centeredFract ((v : ℝ) * y)
        = ∫ z in (0 : ℝ)..1, H a z := by
    intro a _
    have hper : Function.Periodic (H a) 1 := by
      intro z
      simp only [hH]
      have e : (v : ℝ) * (z + 1) - (v : ℝ) * a / u
          = ((v : ℝ) * z - (v : ℝ) * a / u) + ((v : ℤ) : ℝ) := by push_cast; ring
      rw [centeredFract_periodic z, e, centeredFract_add_intCast]
    have h3 : ∫ y in (0 : ℝ)..1, centeredFract (y + (a : ℝ) / u) * centeredFract ((v : ℝ) * y)
        = ∫ y in (0 : ℝ)..1, H a (y + (a : ℝ) / u) := by
      refine intervalIntegral.integral_congr fun y _ => ?_
      simp only [hH]
      congr 2
      field_simp
      ring
    rw [h3, intervalIntegral.integral_comp_add_right (H a) ((a : ℝ) / u), zero_add,
      add_comm 1, hper.intervalIntegral_add_eq ((a : ℝ) / u) 0, zero_add]
  rw [Finset.sum_congr rfl h2, ← intervalIntegral.integral_finsetSum fun a _ => by
    have := intervalIntegrable_centeredFract_mul 1 0 (v : ℝ) (-((v : ℝ) * a / u)) 0 1
    simpa [hH, sub_eq_add_neg] using this]
  have h4 : ∀ z, ∑ a ∈ Finset.range u, H a z
      = centeredFract z * centeredFract (((u * v : ℕ) : ℝ) * z) := by
    intro z
    simp only [hH]
    rw [← Finset.mul_sum, sum_centeredFract_sub_mul_div hu huv ((v : ℝ) * z)]
    push_cast; ring_nf
  simp_rw [h4]
  exact integral_centeredFract_mul_nat (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega)
    (by omega)))

/-- **Franel's correlation.**  `∫_0^1 ψ(m x) ψ(m' x) dx = gcd(m, m')²/(12 m m')` for
`m, m' ≥ 1`. -/
theorem integral_centeredFract_mul_mul {m m' : ℕ} (hm : 1 ≤ m) (hm' : 1 ≤ m') :
    ∫ x in (0 : ℝ)..1, centeredFract ((m : ℝ) * x) * centeredFract ((m' : ℝ) * x)
      = ((Nat.gcd m m' : ℕ) : ℝ) ^ 2 / (12 * m * m') := by
  set g := Nat.gcd m m' with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hm
  obtain ⟨u, hu⟩ := Nat.gcd_dvd_left m m'
  obtain ⟨v, hv⟩ := Nat.gcd_dvd_right m m'
  rw [← hg] at hu hv
  have hu1 : 1 ≤ u := by
    rcases Nat.eq_zero_or_pos u with h | h
    · rw [h, mul_zero] at hu; omega
    · exact h
  have hv1 : 1 ≤ v := by
    rcases Nat.eq_zero_or_pos v with h | h
    · rw [h, mul_zero] at hv; omega
    · exact h
  have hcop : Nat.Coprime u v := by
    have := Nat.coprime_div_gcd_div_gcd hg0 (m := m) (n := m')
    rw [← hg] at this
    have e1 : m / g = u := by rw [hu, Nat.mul_div_cancel_left _ hg0]
    have e2 : m' / g = v := by rw [hv, Nat.mul_div_cancel_left _ hg0]
    rwa [e1, e2] at this
  set Hf : ℝ → ℝ := fun y => centeredFract ((u : ℝ) * y) * centeredFract ((v : ℝ) * y) with hHf
  have hper : Function.Periodic Hf 1 := by
    intro y
    simp only [hHf]
    have e1 : (u : ℝ) * (y + 1) = (u : ℝ) * y + ((u : ℤ) : ℝ) := by push_cast; ring
    have e2 : (v : ℝ) * (y + 1) = (v : ℝ) * y + ((v : ℤ) : ℝ) := by push_cast; ring
    rw [e1, e2, centeredFract_add_intCast, centeredFract_add_intCast]
  have hint : ∀ t₁ t₂, IntervalIntegrable Hf volume t₁ t₂ := fun t₁ t₂ => by
    have := intervalIntegrable_centeredFract_mul (u : ℝ) 0 (v : ℝ) 0 t₁ t₂
    simpa [hHf] using this
  have hg0' : (0 : ℝ) < g := by exact_mod_cast hg0
  have h1 : ∫ x in (0 : ℝ)..1, centeredFract ((m : ℝ) * x) * centeredFract ((m' : ℝ) * x)
      = ∫ x in (0 : ℝ)..1, Hf ((g : ℝ) * x) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hHf]
    rw [hu, hv]; push_cast; ring_nf
  have h2 : ∫ x in (0 : ℝ)..1, Hf ((g : ℝ) * x) = ∫ y in (0 : ℝ)..1, Hf y := by
    rw [intervalIntegral.integral_comp_mul_left Hf hg0'.ne', mul_zero, mul_one]
    have h3 := hper.intervalIntegral_add_zsmul_eq (g : ℤ) 0 hint
    simp only [zero_add, zsmul_eq_mul, Int.cast_natCast, mul_one] at h3
    rw [h3, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hg0'.ne', one_mul]
  rw [h1, h2]
  simp only [hHf]
  rw [integral_centeredFract_mul_coprime hu1 hv1 hcop, hu, hv]
  push_cast
  field_simp

end

end RHTower
