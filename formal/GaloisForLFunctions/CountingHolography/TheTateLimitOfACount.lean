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

end GaloisForLFunctions.CountingHolography

end
