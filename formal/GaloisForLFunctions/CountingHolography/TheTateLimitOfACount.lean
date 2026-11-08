import GaloisForLFunctions.ArithmeticScatteringHolography.TheIntegerProbesOfTheHorizon
import GaloisForLFunctions.CountingHolography.TheCountLawAtEveryGenus

/-!
# The Tate limit of a count

Over `ℤ` the probes are the integer vectors `a`, the sources `f_a = Σ aₙ B(· - log n)`, and the Krein
square of a probe is `Q(a) = W(f_a, f_a)` (`ArithmeticScatteringHolography.integerProbe`).

**What a count must be.** The Gram matrix of the probes is a function of the ratio of the integers
(`atomGram_eq_ratio`):

  `Q(a) = Σ_{m,n} a_m a_n C(log(m/n))`,  `C(u) = W(B(· - u), B)`,

so the leading term of any count of integer sources is the multiplicative Toeplitz form of the spline
correlation, and a count is a function of sources whose quadratic growth sees only ratios.

**A count needs no law.** A nonnegative function `K` whose quadratic growth along integer rays is `Q`,
`K(m a)/m² → Q(a)`, forces `Q ≥ 0` (`nonneg_of_tateLimit`). No parallelogram law and no bound at finite
size are needed: the law is recovered in the limit. Hence the count door over `ℤ`
(`riemannHypothesis_iff_tateLimit_of_count`): **RH holds iff the Krein square of the integer probes is
the Tate limit of a count.** Under RH the count `⌊Q⌋` is at distance `< 1` from `Q` and obeys the
parallelogram law up to `6` (`floorCount_near`, `floorCount_parallelogram`), so the question of a count
at bounded distance with an approximate law is RH-strength exactly, in both directions; its content is
that the count be defined without `Q`.

**The Born rule over `ℤ`.** Hecke at `p` moves every atom `B(· - log n)` to `B(· - log p n)` and is an
exact isometry of `Q` (`integerProbe_dilate`): the integer probes carry a quadratic form covariant under
every Hecke operator, unconditionally. Over `ℤ` the quadratic half of the count law holds; the missing
half is the count, and a count with Tate limit `Q` is asymptotically Hecke invariant
(`tateLimit_dilate`).

**The fakes.** The count of a probe on a black hole is exactly homogeneous,
`#ℤ[π]/(m(y - xπ)) = m² #ℤ[π]/(y - xπ)` (`probeCount_smul`), so its Tate limit is `|𝒬|`: quadratic
exactly under universal damping. A fake has a count whose leading term is not a form.
-/

open Filter Topology Finset Matrix

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open ArithmeticScatteringHolography HTGeometry

/-! ### The Tate principle for counts -/

/-- **A count needs no law.** A nonnegative function whose quadratic growth along a ray has limit
`Q x` forces `Q x ≥ 0`. -/
theorem nonneg_of_tateLimit {M : Type*} [AddCommMonoid M] {K : M → ℝ} (hK : ∀ x, 0 ≤ K x) {x : M}
    {Qx : ℝ} (h : Tendsto (fun m : ℕ => K (m • x) / (m : ℝ) ^ 2) atTop (𝓝 Qx)) : 0 ≤ Qx :=
  ge_of_tendsto' h fun _ => div_nonneg (hK _) (sq_nonneg _)

/-- The floor of a nonnegative quadratic quantity has the quadratic growth of the quantity. -/
theorem tendsto_floor_div_sq {Q : ℝ} (hQ : 0 ≤ Q) :
    Tendsto (fun m : ℕ => (⌊(m : ℝ) ^ 2 * Q⌋₊ : ℝ) / (m : ℝ) ^ 2) atTop (𝓝 Q) := by
  have hlow : ∀ᶠ m : ℕ in atTop, Q - 1 / (m : ℝ) ^ 2 ≤ (⌊(m : ℝ) ^ 2 * Q⌋₊ : ℝ) / (m : ℝ) ^ 2 := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    rw [le_div_iff₀ hm', sub_mul, div_mul_cancel₀ _ hm'.ne']
    linarith [Nat.lt_floor_add_one ((m : ℝ) ^ 2 * Q)]
  have hup : ∀ᶠ m : ℕ in atTop, (⌊(m : ℝ) ^ 2 * Q⌋₊ : ℝ) / (m : ℝ) ^ 2 ≤ Q := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hm' : (0 : ℝ) < (m : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ hm']
    linarith [Nat.floor_le (mul_nonneg hm'.le hQ)]
  have hlim : Tendsto (fun m : ℕ => Q - 1 / (m : ℝ) ^ 2) atTop (𝓝 Q) := by
    have h0 : Tendsto (fun m : ℕ => 1 / (m : ℝ) ^ 2) atTop (𝓝 0) := by
      have h2 : Tendsto (fun m : ℕ => (m : ℝ) ^ 2) atTop atTop :=
        (tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop
      have h3 := h2.inv_tendsto_atTop
      simp only [one_div]
      exact h3
    simpa using tendsto_const_nhds.sub h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds hlow hup

/-! ### The probes of `ℤ` -/

/-- **The Krein square of an integer probe is homogeneous of degree two.** -/
theorem integerProbe_smul (N : ℕ) (m : ℕ) (a : Fin N → ℤ) :
    integerProbe N (m • a) = (m : ℝ) ^ 2 * integerProbe N a := by
  unfold integerProbe hermQuad
  have e : (fun i => (((m • a) i : ℤ) : ℂ)) = (m : ℂ) • fun i => (a i : ℂ) := by
    funext i
    simp
  have hs : star (m : ℂ) = (m : ℂ) := by simp
  rw [e, star_smul, hs, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc, show (m : ℂ) * (m : ℂ) = (((m : ℝ) ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul]

/-- **What a count must be.** The Gram matrix of the integer probes depends only on the ratio of the two
integers: the entry at `(m, n)` is the spline correlation at `log(m/n)`. -/
theorem atomGram_eq_ratio (N : ℕ) (i j : Fin N) :
    atomGram N i j = ArithmeticPositiveDuality.splineCorr
      (Real.log (((i : ℝ) + 1) / ((j : ℝ) + 1))) := by
  rw [atomGram]
  rw [show (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) =
    ArithmeticPositiveDuality.vonMangoldtWeight from rfl]
  rw [ArithmeticPositiveDuality.weilGram_translate_cubicSpline, Real.log_div (by positivity)
    (by positivity)]

/-- **The count door over `ℤ`.** RH holds exactly when the Krein square of the integer probes is the
quadratic growth rate of a count along integer rays. -/
theorem riemannHypothesis_iff_tateLimit_of_count :
    RiemannHypothesis ↔ ∃ K : ∀ N, (Fin N → ℤ) → ℕ, ∀ N (a : Fin N → ℤ),
      Tendsto (fun m : ℕ => (K N (m • a) : ℝ) / (m : ℝ) ^ 2) atTop (𝓝 (integerProbe N a)) := by
  constructor
  · intro hRH
    have hn := riemannHypothesis_iff_integerProbes.mp hRH
    refine ⟨fun N a => ⌊integerProbe N a⌋₊, fun N a => ?_⟩
    simp only [integerProbe_smul]
    exact tendsto_floor_div_sq (hn N a)
  · rintro ⟨K, hK⟩
    refine riemannHypothesis_iff_integerProbes.mpr fun N a => ?_
    exact nonneg_of_tateLimit (K := fun b => (K N b : ℝ)) (fun _ => Nat.cast_nonneg _) (hK N a)

/-- **A count at bounded distance forces RH.** Any bound, at each size `N`, suffices. -/
theorem riemannHypothesis_of_count_at_bounded_distance (K : ∀ N, (Fin N → ℤ) → ℕ)
    (B : ℕ → ℝ) (hB : ∀ N a, |integerProbe N a - K N a| ≤ B N) : RiemannHypothesis := by
  refine riemannHypothesis_iff_integerProbes.mpr fun N a => ?_
  by_contra hneg
  push Not at hneg
  -- amplify the probe until the defect exceeds the bound
  obtain ⟨m, hm⟩ := exists_nat_gt ((B N + 1) / (-integerProbe N a))
  have hpos : 0 < -integerProbe N a := by linarith
  have hm1 : (1 : ℝ) ≤ m := by
    have : 0 ≤ (B N + 1) / (-integerProbe N a) :=
      div_nonneg (by linarith [abs_nonneg (integerProbe N a - K N a), hB N a]) hpos.le
    have h1 : (0 : ℝ) < m := by linarith
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at h1)
  have hb := hB N (m • a)
  rw [integerProbe_smul] at hb
  have hK0 : (0 : ℝ) ≤ K N (m • a) := Nat.cast_nonneg _
  have hmsq : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hlt : B N + 1 < m * (-integerProbe N a) := by rwa [div_lt_iff₀ hpos] at hm
  have : (m : ℝ) * (-integerProbe N a) ≤ (m : ℝ) ^ 2 * (-integerProbe N a) :=
    mul_le_mul_of_nonneg_right hmsq hpos.le
  have habs := (abs_le.mp hb).1
  linarith

/-- The floor count is at distance below one. -/
theorem floorCount_near {Q : ℝ} (hQ : 0 ≤ Q) : |Q - (⌊Q⌋₊ : ℝ)| < 1 := by
  rw [abs_lt]
  constructor
  · linarith [Nat.floor_le hQ]
  · linarith [Nat.lt_floor_add_one Q]

/-- **The floor count obeys the parallelogram law up to `6`.** -/
theorem floorCount_parallelogram {Q : (Fin N → ℤ) → ℝ} (hQ : ∀ a, 0 ≤ Q a)
    (hpar : ∀ a b, Q (a + b) + Q (a - b) = 2 * Q a + 2 * Q b) (a b : Fin N → ℤ) :
    |((⌊Q (a + b)⌋₊ : ℝ) + ⌊Q (a - b)⌋₊) - 2 * ⌊Q a⌋₊ - 2 * ⌊Q b⌋₊| ≤ 6 := by
  have h1 := abs_lt.mp (floorCount_near (hQ (a + b)))
  have h2 := abs_lt.mp (floorCount_near (hQ (a - b)))
  have h3 := abs_lt.mp (floorCount_near (hQ a))
  have h4 := abs_lt.mp (floorCount_near (hQ b))
  have hp := hpar a b
  rw [abs_le]
  constructor <;> linarith

/-- Under RH the integer probes carry a count at distance below one obeying the law up to `6`. -/
theorem exists_near_count_of_riemannHypothesis (hRH : RiemannHypothesis) :
    ∃ K : ∀ N, (Fin N → ℤ) → ℕ, ∀ N (a b : Fin N → ℤ),
      |integerProbe N a - K N a| < 1 ∧
        |((K N (a + b) : ℝ) + K N (a - b)) - 2 * K N a - 2 * K N b| ≤ 6 := by
  have hn := riemannHypothesis_iff_integerProbes.mp hRH
  refine ⟨fun N a => ⌊integerProbe N a⌋₊, fun N a b => ⟨floorCount_near (hn N a), ?_⟩⟩
  exact floorCount_parallelogram (hn N) (integerProbe_parallelogram N) a b

/-! ### The fakes -/

/-- **The count of a probe is exactly homogeneous**, on every black hole: its Tate limit is `|𝒬|`. -/
theorem probeCount_smul (q t x y : ℤ) (m : ℕ) :
    probeCount q t (m * x) (m * y) = m ^ 2 * probeCount q t x y := by
  unfold probeCount kreinSquare
  rw [show (m * y : ℤ) ^ 2 - t * (m * x) * (m * y) + q * (m * x) ^ 2 =
    (m : ℤ) ^ 2 * (y ^ 2 - t * x * y + q * x ^ 2) by ring, Int.natAbs_mul, Int.natAbs_pow,
    Int.natAbs_natCast]

/-! ### The Born rule over `ℤ` -/

/-- The atom `n = i + 1` moved to `p n`, at the index `p (i + 1) - 1`. -/
def dilateIndex {p : ℕ} (hp : 0 < p) (N : ℕ) (i : Fin N) : Fin (p * N) :=
  ⟨p * ((i : ℕ) + 1) - 1, by
    have h1 : p * ((i : ℕ) + 1) ≤ p * N := Nat.mul_le_mul_left p i.2
    have h2 : 1 ≤ p * ((i : ℕ) + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    generalize p * ((i : ℕ) + 1) = A at h1 h2
    omega⟩

theorem dilateIndex_val {p : ℕ} (hp : 0 < p) (N : ℕ) (i : Fin N) :
    ((dilateIndex hp N i : ℕ) : ℝ) + 1 = p * ((i : ℝ) + 1) := by
  have h2 : 1 ≤ p * ((i : ℕ) + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  simp only [dilateIndex]
  rw [Nat.cast_sub h2]
  push_cast
  ring

theorem dilateIndex_injective {p : ℕ} (hp : 0 < p) (N : ℕ) : Function.Injective (dilateIndex hp N) := by
  intro i j h
  have h' := congrArg (fun k : Fin (p * N) => ((k : ℕ) : ℝ) + 1) h
  simp only [dilateIndex_val] at h'
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have : (i : ℝ) = j := by
    have := mul_left_cancel₀ hp'.ne' h'
    linarith
  exact Fin.ext (by exact_mod_cast this)

/-- **Hecke at `p` on the integer probes**: every atom `B(· - log n)` is moved to `B(· - log p n)`. -/
def dilate {p : ℕ} (hp : 0 < p) {N : ℕ} (a : Fin N → ℤ) : Fin (p * N) → ℤ :=
  Function.extend (dilateIndex hp N) a 0

/-- A quadratic form of a vector extended by zero along an embedding is the form of the restricted
matrix. -/
theorem hermQuad_extend {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ] {e : ι → κ}
    (he : Function.Injective e) (M : Matrix κ κ ℂ) (x : ι → ℂ) :
    hermQuad M (Function.extend e x 0) = hermQuad (M.submatrix e e) x := by
  classical
  have hsum : ∀ F : κ → ℂ, (∀ k, k ∉ Finset.univ.image e → F k = 0) →
      ∑ k, F k = ∑ i, F (e i) := by
    intro F hF
    rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) fun k _ hk => hF k hk,
      Finset.sum_image fun i _ j _ h => he h]
  have hoff : ∀ k, k ∉ Finset.univ.image e → Function.extend e x 0 k = 0 := by
    intro k hk
    refine Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => hk ?_
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  unfold hermQuad
  congr 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.submatrix_apply]
  rw [hsum _ fun k hk => by rw [hoff k hk, star_zero, zero_mul]]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [he.extend_apply]
  congr 1
  rw [hsum _ fun l hl => by rw [hoff l hl, mul_zero]]
  exact Finset.sum_congr rfl fun j _ => by rw [he.extend_apply]

/-- **The Born rule over `ℤ`.** Hecke at every `p` is an exact isometry of the Krein square of the
integer probes: the dilation of a probe by `p` has the same Krein square. Together with the
parallelogram law (`integerProbe_parallelogram`), the quadratic half of the count law holds over `ℤ`
unconditionally; the missing half is the count. -/
theorem integerProbe_dilate {p : ℕ} (hp : 0 < p) {N : ℕ} (a : Fin N → ℤ) :
    integerProbe (p * N) (dilate hp a) = integerProbe N a := by
  have hcast : (fun k => ((dilate hp a k : ℤ) : ℂ)) =
      Function.extend (dilateIndex hp N) (fun i => (a i : ℂ)) 0 := by
    funext k
    by_cases hk : ∃ i, dilateIndex hp N i = k
    · obtain ⟨i, rfl⟩ := hk
      simp only [dilate, (dilateIndex_injective hp N).extend_apply]
    · simp only [dilate, Function.extend_apply' _ _ _ hk, Pi.zero_apply, Int.cast_zero]
  unfold integerProbe
  rw [hcast, hermQuad_extend (dilateIndex_injective hp N)]
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, atomGram_eq_ratio, dilateIndex_val]
  have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [mul_div_mul_left _ _ hp']

/-- **A count is asymptotically Hecke invariant.** If `K` has Tate limit `Q`, the Tate limits of a probe
and of its dilation agree. -/
theorem tateLimit_dilate {K : ∀ N, (Fin N → ℤ) → ℕ}
    (hK : ∀ N (a : Fin N → ℤ),
      Tendsto (fun m : ℕ => (K N (m • a) : ℝ) / (m : ℝ) ^ 2) atTop (𝓝 (integerProbe N a)))
    {p : ℕ} (hp : 0 < p) {N : ℕ} (a : Fin N → ℤ) :
    Tendsto (fun m : ℕ => (K (p * N) (m • dilate hp a) : ℝ) / (m : ℝ) ^ 2) atTop
      (𝓝 (integerProbe N a)) := by
  rw [← integerProbe_dilate hp a]
  exact hK _ _

end GaloisForLFunctions.CountingHolography

end
