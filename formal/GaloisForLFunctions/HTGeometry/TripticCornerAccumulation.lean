import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# Mixed-quadrant accumulation for a rank-three period pattern

Let `τ` and `σ` lie in the upper half plane and let `1, τ, σ` be independent over the integers.
If a function meromorphic on the plane has a principal-part coefficient that is `1`-periodic and
takes one constant value `v` on a mixed quadrant of the lattice pattern `p + nτ + mσ`, then
`v = 0`.

The mechanism is that a mixed quadrant contains points whose imaginary parts stay bounded: pick
`m` as the negative of the ceiling of `n·Im τ / Im σ`.  Reducing the real part by an integer keeps
the coefficient, by periodicity, and places the points in one compact rectangle.  Integer
independence makes them pairwise distinct, so a nonzero `v` would give infinitely many poles in a
compact set.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

/-- The compensating index making the imaginary part bounded. -/
noncomputable def cornerIndex (τ σ : ℂ) (n : ℕ) : ℤ := -⌈(n : ℝ) * τ.im / σ.im⌉

theorem cornerIndex_im_bound {τ σ : ℂ} (hσ : 0 < σ.im) (n : ℕ) :
    -σ.im < (n : ℝ) * τ.im + (cornerIndex τ σ n : ℝ) * σ.im ∧
      (n : ℝ) * τ.im + (cornerIndex τ σ n : ℝ) * σ.im ≤ 0 := by
  set C : ℝ := ((⌈(n : ℝ) * τ.im / σ.im⌉ : ℤ) : ℝ) with hC
  have hceil : C < (n : ℝ) * τ.im / σ.im + 1 := Int.ceil_lt_add_one _
  have hceil' : (n : ℝ) * τ.im / σ.im ≤ C := Int.le_ceil _
  have hupper : (n : ℝ) * τ.im ≤ C * σ.im := (div_le_iff₀ hσ).mp hceil'
  have hlower : (C - 1) * σ.im < (n : ℝ) * τ.im := by
    have h : C - 1 < (n : ℝ) * τ.im / σ.im := by linarith
    exact (lt_div_iff₀ hσ).mp h
  refine ⟨?_, ?_⟩
  · simp only [cornerIndex, Int.cast_neg, ← hC]
    nlinarith [hlower]
  · simp only [cornerIndex, Int.cast_neg, ← hC]
    nlinarith [hupper]

theorem cornerIndex_tendsto_atBot {τ σ : ℂ} (hτ : 0 < τ.im) (hσ : 0 < σ.im) :
    Filter.Tendsto (fun n : ℕ => cornerIndex τ σ n) Filter.atTop Filter.atBot := by
  have hmain : ∀ M : ℕ, ∀ n : ℕ, (M : ℝ) * σ.im / τ.im ≤ (n : ℝ) →
      cornerIndex τ σ n ≤ -(M : ℤ) := by
    intro M n hn
    have hle : (M : ℝ) ≤ (n : ℝ) * τ.im / σ.im := by
      rw [le_div_iff₀ hσ]
      have : (M : ℝ) * σ.im ≤ (n : ℝ) * τ.im := by
        rw [div_le_iff₀ hτ] at hn
        linarith
      linarith
    have hceil : (M : ℤ) ≤ ⌈(n : ℝ) * τ.im / σ.im⌉ := by
      exact_mod_cast Int.le_ceil_iff.mpr (by push_cast; linarith [Int.le_ceil ((n : ℝ) * τ.im / σ.im)])
    simp only [cornerIndex]
    omega
  refine Filter.tendsto_atBot.mpr ?_
  intro b
  obtain ⟨M, hM⟩ := exists_nat_ge (-b : ℤ)
  refine Filter.eventually_atTop.mpr ⟨⌈(M : ℝ) * σ.im / τ.im⌉.toNat, ?_⟩
  intro n hn
  have hn' : (M : ℝ) * σ.im / τ.im ≤ (n : ℝ) := by
    have h1 : ((⌈(M : ℝ) * σ.im / τ.im⌉.toNat : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2 : (M : ℝ) * σ.im / τ.im ≤ ((⌈(M : ℝ) * σ.im / τ.im⌉ : ℤ) : ℝ) := Int.le_ceil _
    have h3 : ((⌈(M : ℝ) * σ.im / τ.im⌉ : ℤ) : ℝ) ≤ ((⌈(M : ℝ) * σ.im / τ.im⌉.toNat : ℤ) : ℝ) := by
      exact_mod_cast Int.self_le_toNat _
    linarith
  have := hmain M n hn'
  omega


/-- A `1`-periodic principal-part coefficient is invariant under every integer translation. -/
theorem laurentCoeff_add_intCast {F : ℂ → ℂ} {ℓ : ℤ}
    (hper : ∀ z : ℂ, laurentCoeff F (z + 1) ℓ = laurentCoeff F z ℓ) (z : ℂ) (j : ℤ) :
    laurentCoeff F (z + (j : ℂ)) ℓ = laurentCoeff F z ℓ := by
  induction j using Int.induction_on with
  | zero => simp
  | succ k ih =>
      have hstep : z + ((k : ℤ) + 1 : ℤ) = (z + ((k : ℤ) : ℂ)) + 1 := by push_cast; ring
      rw [hstep, hper, ih]
  | pred k ih =>
      have hstep : (z + ((-(k : ℤ) - 1 : ℤ) : ℂ)) + 1 = z + ((-(k : ℤ) : ℤ) : ℂ) := by
        push_cast; ring
      have h := hper (z + ((-(k : ℤ) - 1 : ℤ) : ℂ))
      rw [hstep, ih] at h
      exact h.symm

/-- **Mixed-quadrant accumulation.**  A `1`-periodic principal-part coefficient that is constant on
a mixed quadrant of the rank-three pattern `p + nτ + mσ` has that constant equal to zero. -/
theorem laurentCoeff_const_eq_zero_of_mixedQuadrant
    {F : ℂ → ℂ} (hF : MeromorphicOn F Set.univ) {ℓ : ℤ} (hℓ : ℓ < 0)
    (hper : ∀ z : ℂ, laurentCoeff F (z + 1) ℓ = laurentCoeff F z ℓ)
    {τ σ : ℂ} (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (p : ℂ) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) (v : ℂ) (N : ℕ)
    (hconst : ∀ n m : ℤ, (N : ℤ) ≤ n → m ≤ -(N : ℤ) →
      laurentCoeff F (p + ((ε * n : ℤ) : ℂ) * τ + ((ε * m : ℤ) : ℂ) * σ) ℓ = v) :
    v = 0 := by
  classical
  set c : ℕ → ℤ := fun n => cornerIndex τ σ n with hc
  set q : ℕ → ℂ :=
    fun n => p + ((ε * (n : ℤ) : ℤ) : ℂ) * τ + ((ε * c n : ℤ) : ℂ) * σ with hq
  set jj : ℕ → ℤ := fun n => -⌊(q n).re⌋ with hjj
  set w : ℕ → ℂ := fun n => q n + ((jj n : ℤ) : ℂ) with hw
  set M : ℝ := 1 + |p.im| + σ.im with hM
  -- the points stay in one closed ball
  have hεabs : |((ε : ℤ) : ℝ)| = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  have him : ∀ n : ℕ, |(w n).im| ≤ |p.im| + σ.im := by
    intro n
    have hb := cornerIndex_im_bound (τ := τ) hσ n
    have hqim : (q n).im
        = p.im + ((ε : ℤ) : ℝ) * ((n : ℝ) * τ.im + (c n : ℝ) * σ.im) := by
      simp only [hq, Complex.add_im, Complex.mul_im, Complex.intCast_im, Complex.intCast_re,
        zero_mul, add_zero]
      push_cast
      ring
    have hwim : (w n).im = (q n).im := by
      simp [hw, Complex.add_im, Complex.intCast_im]
    rw [hwim, hqim]
    have hbound : |(n : ℝ) * τ.im + (c n : ℝ) * σ.im| ≤ σ.im := by
      rw [abs_le]
      constructor <;> [linarith [hb.1]; linarith [hb.2, hσ]]
    calc |p.im + ((ε : ℤ) : ℝ) * ((n : ℝ) * τ.im + (c n : ℝ) * σ.im)|
        ≤ |p.im| + |((ε : ℤ) : ℝ) * ((n : ℝ) * τ.im + (c n : ℝ) * σ.im)| := abs_add_le _ _
      _ = |p.im| + |(n : ℝ) * τ.im + (c n : ℝ) * σ.im| := by rw [abs_mul, hεabs, one_mul]
      _ ≤ |p.im| + σ.im := by linarith
  have hre : ∀ n : ℕ, |(w n).re| ≤ 1 := by
    intro n
    have hwre : (w n).re = Int.fract ((q n).re) := by
      simp only [hw, hjj, Complex.add_re, Int.cast_neg, Complex.neg_re, Complex.intCast_re,
        Int.fract]
      ring
    rw [hwre, abs_le]
    constructor
    · linarith [Int.fract_nonneg ((q n).re)]
    · linarith [Int.fract_lt_one ((q n).re)]
  have hball : ∀ n : ℕ, w n ∈ Metric.closedBall (0 : ℂ) M := by
    intro n
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc ‖w n‖ ≤ |(w n).re| + |(w n).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 + (|p.im| + σ.im) := add_le_add (hre n) (him n)
      _ = M := by rw [hM]; ring
  -- beyond a threshold the coefficient is the constant `v`
  obtain ⟨N₁, hN₁⟩ : ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → c n ≤ -(N : ℤ) := by
    have htend := cornerIndex_tendsto_atBot (τ := τ) (σ := σ) hτ hσ
    obtain ⟨N₁, hN₁⟩ := (Filter.tendsto_atBot.mp htend (-(N : ℤ))).exists_forall_of_atTop
    exact ⟨N₁, hN₁⟩
  set N' : ℕ := max N N₁ with hN'
  have hvalue : ∀ n : ℕ, N' ≤ n → laurentCoeff F (w n) ℓ = v := by
    intro n hn
    have h1 : (N : ℤ) ≤ (n : ℤ) := by
      have : N ≤ n := le_trans (le_max_left _ _) hn
      exact_mod_cast this
    have h2 : c n ≤ -(N : ℤ) := hN₁ n (le_trans (le_max_right _ _) hn)
    rw [hw, laurentCoeff_add_intCast hper]
    exact hconst (n : ℤ) (c n) h1 h2
  -- distinct indices give distinct points
  have hinj : Set.InjOn w (Set.Ici N') := by
    intro n₁ _ n₂ _ heq
    have hzero : ((ε * (n₁ : ℤ) - ε * (n₂ : ℤ) : ℤ) : ℂ) * τ
        + ((ε * c n₁ - ε * c n₂ : ℤ) : ℂ) * σ + ((jj n₁ - jj n₂ : ℤ) : ℂ) = 0 := by
      have h := heq
      simp only [hw, hq] at h
      push_cast at h ⊢
      linear_combination h
    obtain ⟨hn, -, -⟩ := hindep _ _ _ hzero
    have hεne : ε ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
    have : (n₁ : ℤ) = (n₂ : ℤ) := by
      have := hn
      rcases hε with rfl | rfl <;> omega
    exact_mod_cast this
  -- conclude
  by_contra hv
  have hfin := finite_setOf_laurentCoeff_ne_zero_of_bounded hF hℓ
    (S := Metric.closedBall (0 : ℂ) M) (Metric.isBounded_closedBall)
  have hmaps : w '' (Set.Ici N') ⊆
      {a : ℂ | a ∈ Metric.closedBall (0 : ℂ) M ∧ laurentCoeff F a ℓ ≠ 0} := by
    rintro _ ⟨n, hn, rfl⟩
    exact ⟨hball n, by rw [hvalue n hn]; exact hv⟩
  have hIci : (Set.Ici N').Finite := Set.Finite.of_finite_image (hfin.subset hmaps) hinj
  exact (Set.Ici_infinite N') hIci


/-- **Finiteness of the nonzero principal-part coefficients along a lattice orbit.**  If the
coefficient function is invariant under `1` and under `τ`, then along the `σ`-orbit of a point only
finitely many members carry a nonzero coefficient: the orbit reduces into one compact fundamental
rectangle, injectively by integer independence. -/
theorem finite_setOf_laurentCoeff_ne_zero_orbit
    {G : ℂ → ℂ} (hG : MeromorphicOn G Set.univ) {ℓ : ℤ} (hℓ : ℓ < 0)
    {τ σ : ℂ} (hτ : 0 < τ.im)
    (hper1 : ∀ z : ℂ, laurentCoeff G (z + 1) ℓ = laurentCoeff G z ℓ)
    (hperτ : ∀ z : ℂ, laurentCoeff G (z + τ) ℓ = laurentCoeff G z ℓ)
    (hindep : ∀ m n j : ℤ, (m : ℂ) * σ + (n : ℂ) * τ + (j : ℂ) = 0 → m = 0 ∧ n = 0 ∧ j = 0)
    (p : ℂ) :
    {m : ℤ | laurentCoeff G (p + (m : ℂ) * σ) ℓ ≠ 0}.Finite := by
  classical
  set x : ℤ → ℂ := fun m => p + (m : ℂ) * σ with hx
  set t : ℤ → ℤ := fun m => -⌊(x m).im / τ.im⌋ with ht
  set y : ℤ → ℂ := fun m => x m + ((t m : ℤ) : ℂ) * τ with hy
  set sh : ℤ → ℤ := fun m => -⌊(y m).re⌋ with hsh
  set w : ℤ → ℂ := fun m => y m + ((sh m : ℤ) : ℂ) with hw
  set M : ℝ := 1 + τ.im with hM
  have hyim : ∀ m : ℤ, (y m).im = Int.fract ((x m).im / τ.im) * τ.im := by
    intro m
    have hyim0 : (y m).im = (x m).im + ((t m : ℤ) : ℝ) * τ.im := by
      simp [hy, Complex.add_im, Complex.mul_im]
    have hu : (x m).im = ((x m).im / τ.im) * τ.im := by
      field_simp
    rw [hyim0]
    simp only [ht, Int.cast_neg, Int.fract]
    linear_combination hu
  have him : ∀ m : ℤ, |(w m).im| ≤ τ.im := by
    intro m
    have hwim : (w m).im = (y m).im := by
      simp [hw, Complex.add_im, Complex.intCast_im]
    rw [hwim, hyim m, abs_le]
    constructor
    · nlinarith [Int.fract_nonneg ((x m).im / τ.im), hτ]
    · nlinarith [Int.fract_lt_one ((x m).im / τ.im), hτ, Int.fract_nonneg ((x m).im / τ.im)]
  have hre : ∀ m : ℤ, |(w m).re| ≤ 1 := by
    intro m
    have hwre : (w m).re = Int.fract ((y m).re) := by
      simp only [hw, hsh, Complex.add_re, Int.cast_neg, Complex.neg_re, Complex.intCast_re,
        Int.fract]
      ring
    rw [hwre, abs_le]
    constructor
    · linarith [Int.fract_nonneg ((y m).re)]
    · linarith [Int.fract_lt_one ((y m).re)]
  have hball : ∀ m : ℤ, w m ∈ Metric.closedBall (0 : ℂ) M := by
    intro m
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc ‖w m‖ ≤ |(w m).re| + |(w m).im| := Complex.norm_le_abs_re_add_abs_im _
      _ ≤ 1 + τ.im := add_le_add (hre m) (him m)
      _ = M := by rw [hM]
  have hcoef : ∀ m : ℤ, laurentCoeff G (w m) ℓ = laurentCoeff G (x m) ℓ := by
    intro m
    rw [hw, laurentCoeff_add_intCast hper1, hy, laurentCoeff_add_zsmul_of_period hperτ]
  have hinj : Set.InjOn w {m : ℤ | laurentCoeff G (x m) ℓ ≠ 0} := by
    intro m₁ _ m₂ _ heq
    have hzero : ((m₁ - m₂ : ℤ) : ℂ) * σ + ((t m₁ - t m₂ : ℤ) : ℂ) * τ
        + ((sh m₁ - sh m₂ : ℤ) : ℂ) = 0 := by
      have h := heq
      simp only [hw, hy, hx] at h
      push_cast at h ⊢
      linear_combination h
    obtain ⟨hm, -, -⟩ := hindep _ _ _ hzero
    omega
  have hfin := finite_setOf_laurentCoeff_ne_zero_of_bounded hG hℓ
    (S := Metric.closedBall (0 : ℂ) M) (Metric.isBounded_closedBall)
  have hmaps : w '' {m : ℤ | laurentCoeff G (x m) ℓ ≠ 0} ⊆
      {a : ℂ | a ∈ Metric.closedBall (0 : ℂ) M ∧ laurentCoeff G a ℓ ≠ 0} := by
    rintro _ ⟨m, hm, rfl⟩
    exact ⟨hball m, by rw [hcoef m]; exact hm⟩
  exact Set.Finite.of_finite_image (hfin.subset hmaps) hinj

end GaloisForLFunctions.HTGeometry
