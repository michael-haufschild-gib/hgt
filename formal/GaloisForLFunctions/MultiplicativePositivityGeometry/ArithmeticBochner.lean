import GaloisForLFunctions.MultiplicativePositivityGeometry.LocallyFiniteBochner
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Arithmetic Bochner theorem: locally finite divisors of one Dirichlet series

Every locally finite even positive-definite `D` is the boundary divisor of a single Dirichlet series
`Σ_n Λ(n) g(log n) n^{−s}` with a fixed profile `g ≥ 0` (`arithmetic_bochner`), i.e. of `−Z'/Z` for
`Z(s) = exp Σ_n Λ(n) g(log n) n^{−s}/log n`. The weights depend on the damping only through
`n^{−x}`; no weight is chosen per damping, as in the abstract range theorem.

* **Exponential partition** (`expPart`). With dampings `a_N ↓ 0` the functions
  `φ_N(t) = e^{−a_N t} − e^{−a_{N−1} t}` (`e^{−a_{−1} t} := 0`) are nonnegative with sum `1`, and
  `g = Σ_N φ_N P_N` with `P_N ≥ 0` the Bohr polynomial of the `N`-th Fejér truncation of `D`.
* **Blocks are differences of ζ-traces** (`tsum_block_eq`). `Λ(n) n^{−1−x} φ_N(log n)` is the
  difference of the von Mangoldt weights at dampings `x + a_N` and `x + a_{N−1}`, so the `N`-th block
  of the trace is the `D_N`-convolution of `X(x + a_N, ·) − X(x + a_{N−1}, ·)`, where
  `X(a, w) = Re(−ζ'/ζ)(1 + a + iw)`.
* **Diagonal.** At `w = 0` the weights `x (X(x + a_N, 0) − X(x + a_{N−1}, 0)) ≥ 0` sum to
  `x X(x, 0) → 1` and each tends to `0`, so they average `D_N(u) → D(u)` (`tendsto_toeplitz`).
* **Off the diagonal.** `X` is uniformly continuous on `[0, 2] × {1/(N+1) ≤ |w| ≤ 3(N+1)}`, since
  `ζ` has no zero on `Re s ≥ 1` and its pole is at `1`. Taking `a_{N−1}` below the modulus makes the
  `N`-th off-diagonal block at most `D(0) 2^{−N}`, uniformly in `x`; times `x` it vanishes.
-/

open Finset Filter Topology Complex

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-! ### The ζ-trace up to the line -/

/-- `X(a, w) = Re(−ζ'/ζ)(1 + a + iw)`. -/
noncomputable def zetaX (a w : ℝ) : ℝ := ArithmeticCastelnuovoSeveri.zetaRealLogDeriv (1 + a) w

theorem zetaX_eq_trace {a : ℝ} (ha : 0 < a) (w : ℝ) :
    zetaX a w = cosineTrace (zetaBoundaryWeight a) logFrequency w :=
  zetaRealLogDeriv_eq_cosineTrace ha w

theorem zetaX_eq (a w : ℝ) : zetaX a w =
    (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (w : ℂ) * I) /
      riemannZeta (((1 + a : ℝ) : ℂ) + (w : ℂ) * I)).re := rfl

/-- `X` is continuous at every `(a, w)` with `a ≥ 0` other than the pole `(0, 0)`. -/
theorem continuousAt_zetaX {a w : ℝ} (ha : 0 ≤ a) (hw : 0 < a ∨ w ≠ 0) :
    ContinuousAt (fun p : ℝ × ℝ => zetaX p.1 p.2) (a, w) := by
  have hre : (((1 + a : ℝ) : ℂ) + (w : ℂ) * I).re = 1 + a := by simp
  have him : (((1 + a : ℝ) : ℂ) + (w : ℂ) * I).im = w := by simp
  have hs1 : (((1 + a : ℝ) : ℂ) + (w : ℂ) * I) ≠ 1 := by
    intro h
    rw [h] at hre him
    simp only [Complex.one_re, Complex.one_im] at hre him
    rcases hw with h | h
    · linarith
    · exact h him.symm
  have hsz := riemannZeta_ne_zero_of_one_le_re (s := ((1 + a : ℝ) : ℂ) + (w : ℂ) * I)
    (by rw [hre]; linarith)
  have hF := (RHTower.differentiableAt_neg_logDeriv_riemannZeta hs1 hsz).continuousAt
  have hin : ContinuousAt (fun p : ℝ × ℝ => ((1 + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * I) (a, w) := by
    fun_prop
  have hcomp := ContinuousAt.comp (g := fun z => -deriv riemannZeta z / riemannZeta z)
    (f := fun p : ℝ × ℝ => ((1 + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * I) (x := (a, w)) hF hin
  have h := Complex.continuous_re.continuousAt.comp hcomp
  simp only [zetaX_eq]
  exact h

/-- The compact block `[0, 2] × {δ ≤ |w| ≤ W}`. -/
def stripBlock (δ W : ℝ) : Set (ℝ × ℝ) := Set.Icc 0 2 ×ˢ {w | δ ≤ |w| ∧ |w| ≤ W}

theorem isCompact_stripBlock (δ W : ℝ) : IsCompact (stripBlock δ W) := by
  refine isCompact_Icc.prod ((isCompact_Icc (a := -W) (b := W)).of_isClosed_subset ?_ ?_)
  · exact (isClosed_le continuous_const continuous_abs).inter
      (isClosed_le continuous_abs continuous_const)
  · intro w hw
    exact abs_le.mp hw.2

theorem continuousOn_zetaX_stripBlock {δ W : ℝ} (hδ : 0 < δ) :
    ContinuousOn (fun p : ℝ × ℝ => zetaX p.1 p.2) (stripBlock δ W) := by
  rintro ⟨a, w⟩ ⟨ha, hw⟩
  exact (continuousAt_zetaX ha.1 (Or.inr (abs_pos.mp (hδ.trans_le hw.1)))).continuousWithinAt

/-- A uniform modulus of continuity in the damping on `[0, 2] × {δ ≤ |w| ≤ W}`. -/
theorem exists_modulus_zetaX {δ W ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ η > 0, ∀ a b w, a ∈ Set.Icc (0 : ℝ) 2 → b ∈ Set.Icc (0 : ℝ) 2 → δ ≤ |w| → |w| ≤ W →
      |a - b| < η → |zetaX a w - zetaX b w| < ε := by
  have hu := (isCompact_stripBlock δ W).uniformContinuousOn_of_continuous
    (continuousOn_zetaX_stripBlock hδ)
  obtain ⟨η, hη, h⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  refine ⟨η, hη, fun a b w ha hb hw1 hw2 hab => ?_⟩
  have := h (a, w) ⟨ha, hw1, hw2⟩ (b, w) ⟨hb, hw1, hw2⟩ (by
    rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_left (abs_nonneg _)]
    exact hab)
  rwa [Real.dist_eq] at this

/-- A uniform bound on `[0, 2] × {δ ≤ |w| ≤ W}`. -/
theorem exists_bound_zetaX {δ W : ℝ} (hδ : 0 < δ) :
    ∃ C, ∀ a w, a ∈ Set.Icc (0 : ℝ) 2 → δ ≤ |w| → |w| ≤ W → |zetaX a w| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_stripBlock δ W).exists_bound_of_continuousOn
    (continuousOn_zetaX_stripBlock hδ)
  exact ⟨C, fun a w ha h1 h2 => by simpa [Real.norm_eq_abs] using hC (a, w) ⟨ha, h1, h2⟩⟩

theorem zetaBoundaryWeight_anti {a b : ℝ} (hab : a ≤ b) (n : ℕ) :
    zetaBoundaryWeight b n ≤ zetaBoundaryWeight a n := by
  unfold zetaBoundaryWeight
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn)
      (by linarith)) ArithmeticFunction.vonMangoldt_nonneg

theorem zetaX_zero_nonneg {a : ℝ} (ha : 0 < a) : 0 ≤ zetaX a 0 := by
  rw [zetaX_eq_trace ha]
  unfold cosineTrace
  exact tsum_nonneg fun n => by
    rw [mul_zero, Real.cos_zero, mul_one]; exact zetaBoundaryWeight_nonneg a n

/-- `X(·, 0) = Σ Λ(n) n^{−1−a}` decreases in the damping. -/
theorem zetaX_zero_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : zetaX b 0 ≤ zetaX a 0 := by
  rw [zetaX_eq_trace (ha.trans_le hab), zetaX_eq_trace ha]
  unfold cosineTrace
  simp only [mul_zero, Real.cos_zero, mul_one]
  exact Summable.tsum_le_tsum (zetaBoundaryWeight_anti hab)
    (summable_zetaBoundaryWeight (ha.trans_le hab)) (summable_zetaBoundaryWeight ha)

/-- Multiplying by `n^{−a}` shifts the damping by `a`. -/
theorem zetaBoundaryWeight_mul_exp (x a : ℝ) (n : ℕ) :
    zetaBoundaryWeight x n * Real.exp (-(a * logFrequency n)) = zetaBoundaryWeight (x + a) n := by
  unfold zetaBoundaryWeight logFrequency
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [show -(a * Real.log n) = Real.log n * (-a) by ring, ← Real.rpow_def_of_pos hn0, mul_assoc,
      ← Real.rpow_add hn0, show -(1 + x) + -a = -(1 + (x + a)) by ring]

/-! ### Convolution with a general kernel -/

/-- `E(0) Q(u) + Σ_{z ∈ Z} E(z)(Q(u − z) + Q(u + z))`. -/
noncomputable def convQ (E : ℝ → ℝ) (Z : Finset ℝ) (Q : ℝ → ℝ) (u : ℝ) : ℝ :=
  E 0 * Q u + ∑ z ∈ Z, E z * (Q (u - z) + Q (u + z))

theorem convQ_sub (E : ℝ → ℝ) (Z : Finset ℝ) (Q₁ Q₂ : ℝ → ℝ) (u : ℝ) :
    convQ E Z (fun w => Q₁ w - Q₂ w) u = convQ E Z Q₁ u - convQ E Z Q₂ u := by
  unfold convQ
  rw [show E 0 * Q₁ u + ∑ z ∈ Z, E z * (Q₁ (u - z) + Q₁ (u + z)) -
      (E 0 * Q₂ u + ∑ z ∈ Z, E z * (Q₂ (u - z) + Q₂ (u + z))) =
      E 0 * (Q₁ u - Q₂ u) + (∑ z ∈ Z, E z * (Q₁ (u - z) + Q₁ (u + z)) -
        ∑ z ∈ Z, E z * (Q₂ (u - z) + Q₂ (u + z))) by ring, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun z _ => by ring

/-- The trace of the von Mangoldt weights at damping `y` twisted by a Bohr polynomial. -/
theorem tsum_bohr_eq {E : ℝ → ℝ} {Z : Finset ℝ} {y : ℝ} (hy : 0 < y) (u : ℝ) :
    ∑' n, zetaBoundaryWeight y n * bohrPoly E Z (logFrequency n) * Real.cos (logFrequency n * u) =
      convQ E Z (zetaX y) u := by
  have h := cosineTrace_apWeight (c₀ := E 0) (Z := Z) (b := fun z => 2 * E z) hy u
  simp only [← zetaX_eq_trace hy] at h
  unfold cosineTrace apWeight at h
  rw [show (∑' n, zetaBoundaryWeight y n * bohrPoly E Z (logFrequency n) *
      Real.cos (logFrequency n * u)) = ∑' n, zetaBoundaryWeight y n *
        apPoly (E 0) Z (fun z => 2 * E z) (logFrequency n) * Real.cos (logFrequency n * u) from rfl,
    h]
  unfold convQ
  congr 1
  exact Finset.sum_congr rfl fun z _ => by ring

theorem summable_bohr {E : ℝ → ℝ} {Z : Finset ℝ} {y : ℝ} (hy : 0 < y) (u : ℝ) :
    Summable fun n => zetaBoundaryWeight y n * bohrPoly E Z (logFrequency n) *
      Real.cos (logFrequency n * u) :=
  Summable.of_norm_bounded (summable_abs_apWeight (E 0) Z (fun z => 2 * E z) hy) fun n => by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- The convolution error at `u` is controlled by `Q − Q(0) δ₀` at the differences `u − v`. -/
theorem abs_convQ_sub_le {E : ℝ → ℝ} {Z : Finset ℝ} (hcfg : IsFiniteConfig E Z) {Q : ℝ → ℝ}
    {u M B : ℝ} (hM : ∀ v, |E v| ≤ M)
    (hY : ∀ v, (v = 0 ∨ v ∈ Z ∨ -v ∈ Z) → |Q (u - v) - diracAt (u - v) * Q 0| ≤ B) :
    |convQ E Z Q u - E u * Q 0| ≤ M * B * (1 + 2 * Z.card) := by
  have hY0 : |Q u - diracAt u * Q 0| ≤ B := by simpa using hY 0 (Or.inl rfl)
  have hYm : ∀ z ∈ Z, |Q (u - z) - diracAt (u - z) * Q 0| ≤ B :=
    fun z hz => hY z (Or.inr (Or.inl hz))
  have hYp : ∀ z ∈ Z, |Q (u + z) - diracAt (u + z) * Q 0| ≤ B := fun z hz => by
    simpa using hY (-z) (Or.inr (Or.inr (by simpa using hz)))
  have halg : convQ E Z Q u - E u * Q 0 = E 0 * (Q u - diracAt u * Q 0) +
      ∑ z ∈ Z, E z * ((Q (u - z) - diracAt (u - z) * Q 0) +
        (Q (u + z) - diracAt (u + z) * Q 0)) := by
    rw [← congrFun (apDivisor_bohr hcfg) u]
    simp only [convQ, apDivisor]
    have hz : ∀ z ∈ Z, E z * ((Q (u - z) - diracAt (u - z) * Q 0) +
        (Q (u + z) - diracAt (u + z) * Q 0)) =
        E z * (Q (u - z) + Q (u + z)) - 2 * E z / 2 * (diracAt (u + z) + diracAt (u - z)) * Q 0 :=
      fun z _ => by ring
    rw [Finset.sum_congr rfl hz, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  rw [halg]
  refine (abs_add_le _ _).trans ?_
  have hsum : |∑ z ∈ Z, E z * ((Q (u - z) - diracAt (u - z) * Q 0) +
      (Q (u + z) - diracAt (u + z) * Q 0))| ≤ ∑ z ∈ Z, M * (B + B) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun z hz => ?_)
    rw [abs_mul]
    exact mul_le_mul (hM z) ((abs_add_le _ _).trans (add_le_add (hYm z hz) (hYp z hz)))
      (abs_nonneg _) hM0
  rw [abs_mul]
  have h0 := mul_le_mul (hM 0) hY0 (abs_nonneg _) hM0
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

/-! ### A Toeplitz lemma -/

/-- Nonnegative weights with total mass tending to `1`, each tending to `0`, average a convergent
bounded sequence to its limit. -/
theorem tendsto_toeplitz {l : Filter ℝ} {q : ℝ → ℕ → ℝ} {e : ℕ → ℝ} {L B : ℝ}
    (hq : ∀ᶠ x in l, ∀ N, 0 ≤ q x N) (hs : ∀ᶠ x in l, Summable (q x))
    (hsum : Tendsto (fun x => ∑' N, q x N) l (𝓝 1)) (hN : ∀ N, Tendsto (fun x => q x N) l (𝓝 0))
    (he : Tendsto e atTop (𝓝 L)) (hb : ∀ N, |e N| ≤ B) :
    Tendsto (fun x => ∑' N, q x N * e N) l (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hb 0)
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.mp he (ε / 8) (by positivity)
  have hfin : Tendsto (fun x => ∑ N ∈ range M, q x N) l (𝓝 0) := by
    simpa using tendsto_finsetSum (range M) fun N _ => hN N
  have h1 := Metric.tendsto_nhds.mp hfin (ε / (4 * (B + |L| + 1))) (by positivity)
  have h2 := Metric.tendsto_nhds.mp hsum (min 1 (ε / (4 * (|L| + 1)))) (by positivity)
  filter_upwards [hq, hs, h1, h2] with x hqx hsx h1x h2x
  rw [Real.dist_eq] at h1x h2x ⊢
  have hsum2 : ∑' N, q x N ≤ 2 := by
    have := (abs_lt.mp h2x).2
    linarith [min_le_left 1 (ε / (4 * (|L| + 1)))]
  have hqe : Summable fun N => q x N * (e N - L) :=
    Summable.of_norm_bounded (hsx.mul_left (B + |L|)) fun N => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hqx N), mul_comm]
      exact mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (add_le_add (hb N) le_rfl)) (hqx N)
  have hsplit : ∑' N, q x N * e N - L =
      ∑' N, q x N * (e N - L) + L * (∑' N, q x N - 1) := by
    rw [show (fun N => q x N * (e N - L)) = fun N => q x N * e N - L * q x N by funext N; ring,
      Summable.tsum_sub (hqe.add (hsx.mul_left L) |>.congr fun N => by ring) (hsx.mul_left L),
      tsum_mul_left]
    ring
  rw [hsplit]
  -- Split the deviations at `M`.
  have htail : ∑' N, q x N * (e N - L) =
      ∑ N ∈ range M, q x N * (e N - L) + ∑' N, q x (N + M) * (e (N + M) - L) :=
    (Summable.sum_add_tsum_nat_add M hqe).symm
  have hhead : |∑ N ∈ range M, q x N * (e N - L)| ≤ (B + |L|) * ∑ N ∈ range M, q x N := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun N _ => ?_
    rw [abs_mul, abs_of_nonneg (hqx N), mul_comm]
    exact mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (add_le_add (hb N) le_rfl)) (hqx N)
  have hrest : |∑' N, q x (N + M) * (e (N + M) - L)| ≤ ε / 8 * ∑' N, q x N := by
    have hs' : Summable fun N => q x (N + M) * (e (N + M) - L) := (summable_nat_add_iff M).mpr hqe
    calc |∑' N, q x (N + M) * (e (N + M) - L)| ≤ ∑' N, ε / 8 * q x (N + M) := by
          rw [← Real.norm_eq_abs]
          refine (norm_tsum_le_tsum_norm (hs'.norm)).trans (Summable.tsum_le_tsum (fun N => ?_)
            hs'.norm (((summable_nat_add_iff M).mpr hsx).mul_left _))
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hqx _), mul_comm]
          exact mul_le_mul_of_nonneg_right (by
            have := hM (N + M) (Nat.le_add_left M N)
            rw [Real.dist_eq] at this; exact this.le) (hqx _)
      _ = ε / 8 * ∑' N, q x (N + M) := tsum_mul_left
      _ ≤ ε / 8 * ∑' N, q x N := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← Summable.sum_add_tsum_nat_add M hsx]
          exact le_add_of_nonneg_left (Finset.sum_nonneg fun N _ => hqx N)
  have hfinx : ∑ N ∈ range M, q x N < ε / (4 * (B + |L| + 1)) := by
    have := (abs_lt.mp (by simpa using h1x)).2; linarith
  have hhead' : (B + |L|) * ∑ N ∈ range M, q x N < ε / 4 := by
    have hpos : 0 ≤ ∑ N ∈ range M, q x N := Finset.sum_nonneg fun N _ => hqx N
    calc (B + |L|) * ∑ N ∈ range M, q x N ≤ (B + |L| + 1) * ∑ N ∈ range M, q x N :=
          mul_le_mul_of_nonneg_right (by linarith) hpos
      _ < (B + |L| + 1) * (ε / (4 * (B + |L| + 1))) :=
          mul_lt_mul_of_pos_left hfinx (by positivity)
      _ = ε / 4 := by field_simp
  have hL : |L * (∑' N, q x N - 1)| ≤ ε / 4 := by
    rw [abs_mul]
    have hlt : |∑' N, q x N - 1| < ε / (4 * (|L| + 1)) :=
      lt_of_lt_of_le h2x (min_le_right _ _)
    calc |L| * |∑' N, q x N - 1| ≤ (|L| + 1) * |∑' N, q x N - 1| :=
          mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ (|L| + 1) * (ε / (4 * (|L| + 1))) :=
          mul_le_mul_of_nonneg_left hlt.le (by positivity)
      _ = ε / 4 := by field_simp
  rw [htail]
  calc |∑ N ∈ range M, q x N * (e N - L) + ∑' N, q x (N + M) * (e (N + M) - L) +
        L * (∑' N, q x N - 1)|
      ≤ |∑ N ∈ range M, q x N * (e N - L)| + |∑' N, q x (N + M) * (e (N + M) - L)| +
        |L * (∑' N, q x N - 1)| := abs_add_three _ _ _
    _ < ε / 4 + ε / 8 * 2 + ε / 4 := by
        have := mul_le_mul_of_nonneg_left hsum2 (by positivity : (0 : ℝ) ≤ ε / 8)
        linarith
    _ < ε := by linarith

/-! ### Block scales -/

variable {D : ℝ → ℝ}

/-- `S_N = 1 + 2 #Z_N`. -/
noncomputable def blockSize (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) : ℝ :=
  1 + 2 * (fejerHeights hloc N).card

theorem one_le_blockSize (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) :
    1 ≤ blockSize hloc N := by
  unfold blockSize
  have := (Nat.cast_nonneg (fejerHeights hloc N).card : (0 : ℝ) ≤ _)
  linarith

theorem blockModulus_exists (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) :
    ∃ η > 0, ∀ a b w, a ∈ Set.Icc (0 : ℝ) 2 → b ∈ Set.Icc (0 : ℝ) 2 →
      1 / ((N : ℝ) + 1) ≤ |w| → |w| ≤ 3 * ((N : ℝ) + 1) → |a - b| < η →
        |zetaX a w - zetaX b w| < 1 / (2 ^ N * blockSize hloc N) :=
  exists_modulus_zetaX (by positivity) (by have := one_le_blockSize hloc N; positivity)

/-- A modulus of `X` on the `N`-th block for the tolerance `2^{−N}/S_N`. -/
noncomputable def blockModulus (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) : ℝ :=
  Classical.choose (blockModulus_exists hloc N)

theorem blockModulus_pos (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) :
    0 < blockModulus hloc N :=
  (Classical.choose_spec (blockModulus_exists hloc N)).1

theorem blockModulus_spec (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) {a b w : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 2) (hb : b ∈ Set.Icc (0 : ℝ) 2) (hw1 : 1 / ((N : ℝ) + 1) ≤ |w|)
    (hw2 : |w| ≤ 3 * ((N : ℝ) + 1)) (hab : |a - b| < blockModulus hloc N) :
    |zetaX a w - zetaX b w| < 1 / (2 ^ N * blockSize hloc N) :=
  (Classical.choose_spec (blockModulus_exists hloc N)).2 a b w ha hb hw1 hw2 hab

/-- `T_N = Σ_{j < N + 2} (2^j S_j + 1/η_j)`. -/
noncomputable def blockScale (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) : ℝ :=
  ∑ j ∈ range (N + 2), (2 ^ j * blockSize hloc j + 1 / blockModulus hloc j)

theorem blockScale_term_pos (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (j : ℕ) :
    0 < 2 ^ j * blockSize hloc j + 1 / blockModulus hloc j := by
  have := one_le_blockSize hloc j
  have := blockModulus_pos hloc j
  positivity

theorem blockScale_term_le (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) {N j : ℕ}
    (hj : j < N + 2) :
    2 ^ j * blockSize hloc j + 1 / blockModulus hloc j ≤ blockScale hloc N :=
  Finset.single_le_sum (f := fun j => 2 ^ j * blockSize hloc j + 1 / blockModulus hloc j)
    (fun i _ => (blockScale_term_pos hloc i).le) (Finset.mem_range.mpr hj)

theorem blockScale_pos (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) :
    0 < blockScale hloc N :=
  (blockScale_term_pos hloc 0).trans_le (blockScale_term_le hloc (by omega))

/-- The dampings `a_N = 1/T_N`. -/
noncomputable def blockDamp (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) : ℝ :=
  1 / blockScale hloc N

theorem blockDamp_pos (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) :
    0 < blockDamp hloc N :=
  one_div_pos.mpr (blockScale_pos hloc N)

theorem blockDamp_le_one (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) :
    blockDamp hloc N ≤ 1 := by
  have h := blockScale_term_le hloc (N := N) (j := 0) (by omega)
  have h1 := one_le_blockSize hloc 0
  have h2 := blockModulus_pos hloc 0
  have : 1 ≤ blockScale hloc N := by
    have : (0 : ℝ) ≤ 1 / blockModulus hloc 0 := by positivity
    simp only [pow_zero, one_mul] at h
    linarith
  exact (div_le_one (blockScale_pos hloc N)).mpr this

theorem blockDamp_succ_lt (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) :
    blockDamp hloc (N + 1) < blockDamp hloc N := by
  unfold blockDamp
  refine one_div_lt_one_div_of_lt (blockScale_pos hloc N) ?_
  unfold blockScale
  rw [show N + 1 + 2 = (N + 2) + 1 by ring, Finset.sum_range_succ _ (N + 2)]
  linarith [blockScale_term_pos hloc (N + 2)]

/-- `a_N ≤ η_{N+1}`: consecutive dampings are closer than the next modulus. -/
theorem blockDamp_le_modulus (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) :
    blockDamp hloc N ≤ blockModulus hloc (N + 1) := by
  unfold blockDamp
  rw [one_div_le (blockScale_pos hloc N) (blockModulus_pos hloc (N + 1))]
  have h := blockScale_term_le hloc (N := N) (j := N + 1) (by omega)
  have : 0 ≤ 2 ^ (N + 1) * blockSize hloc (N + 1) := by
    have := one_le_blockSize hloc (N + 1); positivity
  linarith

/-- `a_N S_{N+1} ≤ 2^{−(N+1)}`. -/
theorem blockDamp_mul_le (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) :
    blockDamp hloc N * blockSize hloc (N + 1) ≤ (1 / 2) ^ (N + 1) := by
  have h := blockScale_term_le hloc (N := N) (j := N + 1) (by omega)
  have hS := one_le_blockSize hloc (N + 1)
  have hη : 0 ≤ 1 / blockModulus hloc (N + 1) := (one_div_pos.mpr (blockModulus_pos hloc _)).le
  have hT := blockScale_pos hloc N
  unfold blockDamp
  rw [one_div_pow, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hT (by positivity), one_mul]
  nlinarith

theorem tendsto_blockDamp (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) :
    Tendsto (blockDamp hloc) atTop (𝓝 0) := by
  have hg : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ (N + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  refine squeeze_zero (fun N => (blockDamp_pos hloc N).le) (fun N => ?_) hg
  have := blockDamp_mul_le hloc N
  have := one_le_blockSize hloc (N + 1)
  nlinarith [blockDamp_pos hloc N]

/-! ### The exponential partition and the profile -/

/-- `e^{−a_{N−1} t}`, with `e^{−a_{−1} t} = 0`. -/
noncomputable def prevExp (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) :
    ℕ → ℝ → ℝ
  | 0, _ => 0
  | N + 1, t => Real.exp (-(blockDamp hloc N * t))

/-- `φ_N(t) = e^{−a_N t} − e^{−a_{N−1} t}`. -/
noncomputable def expPart (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ)
    (t : ℝ) : ℝ :=
  Real.exp (-(blockDamp hloc N * t)) - prevExp hloc N t

theorem expPart_nonneg (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ expPart hloc N t := by
  cases N with
  | zero => simp only [expPart, prevExp, sub_zero]; positivity
  | succ N =>
    simp only [expPart, prevExp, sub_nonneg]
    exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_right
      (blockDamp_succ_lt hloc N).le ht))

/-- `φ_N(t) S_N ≤ (S_0 + t) 2^{−N}`. -/
theorem expPart_mul_le (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) {t : ℝ}
    (ht : 0 ≤ t) : expPart hloc N t * blockSize hloc N ≤ (blockSize hloc 0 + t) * (1 / 2) ^ N := by
  cases N with
  | zero =>
    simp only [expPart, prevExp, sub_zero, pow_zero, mul_one]
    have h1 : Real.exp (-(blockDamp hloc 0 * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [blockDamp_pos hloc 0])
    nlinarith [one_le_blockSize hloc 0]
  | succ N =>
    simp only [expPart, prevExp]
    have h1 : Real.exp (-(blockDamp hloc (N + 1) * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith [blockDamp_pos hloc (N + 1)])
    have h2 : 1 - blockDamp hloc N * t ≤ Real.exp (-(blockDamp hloc N * t)) := by
      linarith [Real.add_one_le_exp (-(blockDamp hloc N * t))]
    have h3 := blockDamp_mul_le hloc N
    have hS := one_le_blockSize hloc (N + 1)
    have h4 : (Real.exp (-(blockDamp hloc (N + 1) * t)) - Real.exp (-(blockDamp hloc N * t))) *
        blockSize hloc (N + 1) ≤ blockDamp hloc N * t * blockSize hloc (N + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h5 : blockDamp hloc N * t * blockSize hloc (N + 1) ≤ t * (1 / 2) ^ (N + 1) := by
      nlinarith
    have h6 : t * (1 / 2) ^ (N + 1) ≤ (blockSize hloc 0 + t) * (1 / 2) ^ (N + 1) :=
      mul_le_mul_of_nonneg_right (by linarith [one_le_blockSize hloc 0]) (by positivity)
    linarith

/-- The Bohr polynomial of the `N`-th Fejér truncation. -/
noncomputable def blockBohr (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ)
    (t : ℝ) : ℝ :=
  bohrPoly (fejerConfig D N) (fejerHeights hloc N) t

theorem abs_fejerConfig_le (hpd : IsEvenPosDef D) (N : ℕ) (v : ℝ) :
    |fejerConfig D N v| ≤ D 0 := by
  unfold fejerConfig
  rw [abs_mul, abs_of_nonneg (fejerFactor_nonneg _ _)]
  exact (mul_le_of_le_one_right (abs_nonneg _) (fejerFactor_le_one (by positivity) v)).trans
    (hpd.abs_le_apply_zero v)

theorem abs_blockBohr_le (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) (t : ℝ) :
    |blockBohr hloc N t| ≤ D 0 * blockSize hloc N := by
  refine (abs_apPoly_le _ _ _ t).trans ?_
  have h : ∑ z ∈ fejerHeights hloc N, |2 * fejerConfig D N z| ≤
      ∑ z ∈ fejerHeights hloc N, 2 * D 0 :=
    Finset.sum_le_sum fun z _ => by
      rw [abs_mul, abs_two]; linarith [abs_fejerConfig_le hpd N z]
  rw [Finset.sum_const, nsmul_eq_mul] at h
  unfold blockSize
  linarith [abs_fejerConfig_le hpd N 0]

theorem blockBohr_nonneg (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) (t : ℝ) :
    0 ≤ blockBohr hloc N t :=
  bohrPoly_nonneg (fejerConfig_isFiniteConfig hpd hloc N) (fejerConfig_isEvenPosDef hpd N) t

theorem abs_part_le (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |expPart hloc N t * blockBohr hloc N t| ≤ D 0 * (blockSize hloc 0 + t) * (1 / 2) ^ N := by
  rw [abs_mul, abs_of_nonneg (expPart_nonneg hloc N ht)]
  have hD0 := hpd.apply_zero_nonneg
  calc expPart hloc N t * |blockBohr hloc N t| ≤ expPart hloc N t * (D 0 * blockSize hloc N) :=
        mul_le_mul_of_nonneg_left (abs_blockBohr_le hpd hloc N t) (expPart_nonneg hloc N ht)
    _ = D 0 * (expPart hloc N t * blockSize hloc N) := by ring
    _ ≤ D 0 * ((blockSize hloc 0 + t) * (1 / 2) ^ N) :=
        mul_le_mul_of_nonneg_left (expPart_mul_le hloc N ht) hD0
    _ = _ := by ring

theorem summable_part (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) {t : ℝ} (ht : 0 ≤ t) :
    Summable fun N => expPart hloc N t * blockBohr hloc N t :=
  Summable.of_norm_bounded (summable_geometric_two.mul_left (D 0 * (blockSize hloc 0 + t)))
    fun N => by rw [Real.norm_eq_abs]; exact abs_part_le hpd hloc N ht

/-- The profile `g(t) = Σ_N φ_N(t) P_N(t)`. -/
noncomputable def arithProfile (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite)
    (t : ℝ) : ℝ :=
  ∑' N, expPart hloc N t * blockBohr hloc N t

theorem arithProfile_nonneg (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ arithProfile hloc t :=
  tsum_nonneg fun N => mul_nonneg (expPart_nonneg hloc N ht) (blockBohr_nonneg hpd hloc N t)

theorem arithProfile_le (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) {t : ℝ} (ht : 0 ≤ t) :
    arithProfile hloc t ≤ 2 * D 0 * (blockSize hloc 0 + t) := by
  have h := Summable.tsum_le_tsum (fun N => (le_abs_self _).trans (abs_part_le hpd hloc N ht))
    (summable_part hpd hloc ht) (summable_geometric_two.mul_left (D 0 * (blockSize hloc 0 + t)))
  rw [tsum_mul_left, tsum_geometric_two] at h
  unfold arithProfile
  linarith

/-! ### The arithmetic weights -/

theorem summable_zetaBoundaryWeight_mul_log {x : ℝ} (hx : 0 < x) :
    Summable fun n => zetaBoundaryWeight x n * logFrequency n := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (zetaBoundaryWeight_nonneg x n)
    (Real.log_natCast_nonneg n)) (fun n => ?_)
    ((summable_zetaBoundaryWeight (half_pos hx)).mul_left (2 / x))
  unfold zetaBoundaryWeight logFrequency
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog := Real.log_le_rpow_div hn0.le (half_pos hx)
    have e : (n : ℝ) ^ (-(1 + x)) * (n : ℝ) ^ (x / 2) = (n : ℝ) ^ (-(1 + x / 2)) := by
      rw [← Real.rpow_add hn0]; congr 1; ring
    calc (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + x)) * Real.log n
        ≤ (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + x)) *
            ((n : ℝ) ^ (x / 2) / (x / 2)) :=
          mul_le_mul_of_nonneg_left hlog (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.rpow_nonneg hn0.le _))
      _ = 2 / x * ((ArithmeticFunction.vonMangoldt n : ℝ) *
            ((n : ℝ) ^ (-(1 + x)) * (n : ℝ) ^ (x / 2))) := by ring
      _ = _ := by rw [e]

/-- `Λ(n) n^{−1−x} g(log n)`. -/
noncomputable def arithWeight (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (x : ℝ)
    (n : ℕ) : ℝ :=
  zetaBoundaryWeight x n * arithProfile hloc (logFrequency n)

theorem summable_arithWeight (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) {x : ℝ} (hx : 0 < x) :
    Summable (arithWeight hloc x) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (zetaBoundaryWeight_nonneg x n)
    (arithProfile_nonneg hpd hloc (Real.log_natCast_nonneg n))) (fun n => ?_)
    (((summable_zetaBoundaryWeight hx).mul_left (2 * D 0 * blockSize hloc 0)).add
      ((summable_zetaBoundaryWeight_mul_log hx).mul_left (2 * D 0)))
  unfold arithWeight
  have h := arithProfile_le hpd hloc (Real.log_natCast_nonneg n)
  have hz := zetaBoundaryWeight_nonneg x n
  calc zetaBoundaryWeight x n * arithProfile hloc (logFrequency n)
      ≤ zetaBoundaryWeight x n * (2 * D 0 * (blockSize hloc 0 + logFrequency n)) :=
        mul_le_mul_of_nonneg_left h hz
    _ = _ := by ring

/-! ### Block traces -/

/-- `X(x + a_{N−1}, w)`, with `X(x + a_{−1}, ·) = 0`. -/
noncomputable def prevX (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) :
    ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 0
  | N + 1, x, w => zetaX (x + blockDamp hloc N) w

/-- `Δ_N(x, w) = X(x + a_N, w) − X(x + a_{N−1}, w)`. -/
noncomputable def blockDiff (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ)
    (x w : ℝ) : ℝ :=
  zetaX (x + blockDamp hloc N) w - prevX hloc N x w

/-- **Blocks are differences of ζ-traces.** The `N`-th block of the trace is the convolution of
`Δ_N(x, ·)` with the `N`-th truncation. -/
theorem tsum_block_eq (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ) {x : ℝ}
    (hx : 0 < x) (u : ℝ) :
    ∑' n, zetaBoundaryWeight x n * (expPart hloc N (logFrequency n) *
        blockBohr hloc N (logFrequency n)) * Real.cos (logFrequency n * u) =
      convQ (fejerConfig D N) (fejerHeights hloc N) (blockDiff hloc N x) u := by
  have hy : ∀ M, 0 < x + blockDamp hloc M := fun M => add_pos hx (blockDamp_pos hloc M)
  have hshift : ∀ M n, zetaBoundaryWeight x n * Real.exp (-(blockDamp hloc M * logFrequency n)) =
      zetaBoundaryWeight (x + blockDamp hloc M) n := fun M n => zetaBoundaryWeight_mul_exp x _ n
  cases N with
  | zero =>
    have hfun : blockDiff hloc 0 x = zetaX (x + blockDamp hloc 0) := funext fun w => by
      simp [blockDiff, prevX]
    rw [hfun, ← tsum_bohr_eq (hy 0) u]
    refine tsum_congr fun n => ?_
    simp only [expPart, prevExp, sub_zero, blockBohr]
    rw [← hshift 0 n]
    ring
  | succ N =>
    have hfun : blockDiff hloc (N + 1) x = fun w => zetaX (x + blockDamp hloc (N + 1)) w -
        zetaX (x + blockDamp hloc N) w := rfl
    rw [hfun, convQ_sub, ← tsum_bohr_eq (hy (N + 1)) u, ← tsum_bohr_eq (hy N) u,
      ← Summable.tsum_sub (summable_bohr (hy (N + 1)) u) (summable_bohr (hy N) u)]
    refine tsum_congr fun n => ?_
    simp only [expPart, prevExp, blockBohr]
    rw [← hshift (N + 1) n, ← hshift N n]
    ring

theorem blockDiff_zero_nonneg (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ)
    {x : ℝ} (hx : 0 < x) : 0 ≤ blockDiff hloc N x 0 := by
  cases N with
  | zero =>
    simp only [blockDiff, prevX, sub_zero]
    exact zetaX_zero_nonneg (add_pos hx (blockDamp_pos hloc 0))
  | succ N =>
    simp only [blockDiff, prevX, sub_nonneg]
    exact zetaX_zero_anti (add_pos hx (blockDamp_pos hloc _))
      (by linarith [blockDamp_succ_lt hloc N])

theorem blockDiff_zero_le (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ)
    {x : ℝ} (hx : 0 < x) : blockDiff hloc N x 0 ≤ zetaX (blockDamp hloc N) 0 := by
  have h1 : zetaX (x + blockDamp hloc N) 0 ≤ zetaX (blockDamp hloc N) 0 :=
    zetaX_zero_anti (blockDamp_pos hloc N) (by linarith)
  cases N with
  | zero => simpa only [blockDiff, prevX, sub_zero] using h1
  | succ N =>
    simp only [blockDiff, prevX]
    have := zetaX_zero_nonneg (add_pos hx (blockDamp_pos hloc N))
    linarith

/-- Telescoping: `Σ_{N ≤ M} Δ_N(x, 0) = X(x + a_M, 0)`. -/
theorem sum_blockDiff_zero (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (x : ℝ)
    (M : ℕ) : ∑ N ∈ range (M + 1), blockDiff hloc N x 0 = zetaX (x + blockDamp hloc M) 0 := by
  induction M with
  | zero => simp [blockDiff, prevX]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    simp [blockDiff, prevX]

theorem hasSum_blockDiff_zero (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) {x : ℝ}
    (hx : 0 < x) : HasSum (fun N => blockDiff hloc N x 0) (zetaX x 0) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun N => blockDiff_zero_nonneg hloc N hx)]
  have hlim : Tendsto (fun M : ℕ => (x + blockDamp hloc M, (0 : ℝ))) atTop (𝓝 (x, 0)) := by
    have := (tendsto_blockDamp hloc).const_add x
    rw [add_zero] at this
    exact this.prodMk_nhds tendsto_const_nhds
  have hc := (continuousAt_zetaX hx.le (Or.inl hx)).tendsto.comp hlim
  rw [← tendsto_add_atTop_iff_nat 1]
  exact hc.congr fun M => (sum_blockDiff_zero hloc x M).symm

/-- The trace of the arithmetic weights is the sum of the block convolutions. -/
theorem arithTrace_eq (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) {x : ℝ} (hx : 0 < x) (u : ℝ) :
    cosineTrace (arithWeight hloc x) logFrequency u =
      ∑' N, convQ (fejerConfig D N) (fejerHeights hloc N) (blockDiff hloc N x) u := by
  set f : ℕ → ℕ → ℝ := fun n N => zetaBoundaryWeight x n * (expPart hloc N (logFrequency n) *
    blockBohr hloc N (logFrequency n)) * Real.cos (logFrequency n * u) with hf_def
  have hg1 : Summable fun n => zetaBoundaryWeight x n * (D 0 * (blockSize hloc 0 + logFrequency n)) :=
    (((summable_zetaBoundaryWeight hx).mul_left (D 0 * blockSize hloc 0)).add
      ((summable_zetaBoundaryWeight_mul_log hx).mul_left (D 0))).congr fun n => by ring
  have hD0 := hpd.apply_zero_nonneg
  have hS : ∀ n : ℕ, 0 ≤ blockSize hloc 0 + logFrequency n := fun n => by
    have h1 := one_le_blockSize hloc 0
    have h2 : 0 ≤ logFrequency n := Real.log_natCast_nonneg n
    linarith
  have hf : Summable (Function.uncurry f) := by
    refine Summable.of_norm_bounded (Summable.mul_of_nonneg hg1 summable_geometric_two
      (fun n => mul_nonneg (zetaBoundaryWeight_nonneg x n) (mul_nonneg hD0 (hS n)))
      (fun N => by positivity)) fun p => ?_
    obtain ⟨n, N⟩ := p
    simp only [Function.uncurry_apply_pair, hf_def, Real.norm_eq_abs]
    rw [abs_mul, abs_mul, abs_of_nonneg (zetaBoundaryWeight_nonneg x n)]
    have h := abs_part_le hpd hloc N (Real.log_natCast_nonneg n)
    calc zetaBoundaryWeight x n * |expPart hloc N (logFrequency n) *
          blockBohr hloc N (logFrequency n)| * |Real.cos (logFrequency n * u)|
        ≤ zetaBoundaryWeight x n * (D 0 * (blockSize hloc 0 + logFrequency n) * (1 / 2) ^ N) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left h (zetaBoundaryWeight_nonneg x n))
            (Real.abs_cos_le_one _) (abs_nonneg _) (mul_nonneg (zetaBoundaryWeight_nonneg x n)
              (mul_nonneg (mul_nonneg hD0 (hS n)) (by positivity)))
      _ = _ := by ring
  have hrow : ∀ n, HasSum (f n) (zetaBoundaryWeight x n * arithProfile hloc (logFrequency n) *
      Real.cos (logFrequency n * u)) := fun n =>
    ((summable_part hpd hloc (Real.log_natCast_nonneg n)).hasSum.mul_left
      (zetaBoundaryWeight x n)).mul_right _
  unfold cosineTrace arithWeight
  calc ∑' n, zetaBoundaryWeight x n * arithProfile hloc (logFrequency n) *
        Real.cos (logFrequency n * u) = ∑' n, ∑' N, f n N :=
        tsum_congr fun n => (hrow n).tsum_eq.symm
    _ = ∑' N, ∑' n, f n N := hf.tsum_comm.symm
    _ = _ := tsum_congr fun N => tsum_block_eq hloc N hx u

/-! ### The boundary limit -/

/-- The off-diagonal remainder of the `N`-th block at `u`. -/
noncomputable def blockRem (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (N : ℕ)
    (x u : ℝ) : ℝ :=
  convQ (fejerConfig D N) (fejerHeights hloc N) (blockDiff hloc N x) u -
    fejerConfig D N u * blockDiff hloc N x 0

theorem abs_prevX_le (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) {C x w : ℝ} (N : ℕ)
    (hC : 0 ≤ C) (h : ∀ M, |zetaX (x + blockDamp hloc M) w| ≤ C) : |prevX hloc N x w| ≤ C := by
  cases N with
  | zero => simpa [prevX] using hC
  | succ N => exact h N

/-- **Off-diagonal blocks are summably small**, uniformly for `0 < x ≤ 1`. -/
theorem exists_blockRem_bound (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (u : ℝ) :
    ∃ K : ℕ → ℝ, Summable K ∧ ∀ N x, 0 < x → x ≤ 1 → |blockRem hloc N x u| ≤ K N := by
  obtain ⟨δ, hδ, hgap⟩ := exists_gap hloc u
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℕ, M₀ = ⌈1 / δ⌉₊ + ⌈|u|⌉₊ + 1 := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ := exists_bound_zetaX (δ := δ) (W := |u| + M₀ + 1) hδ
  have hD0 := hpd.apply_zero_nonneg
  refine ⟨fun N => D 0 * (1 / 2) ^ N +
      (if N < M₀ then D 0 * (2 * |C|) * blockSize hloc N else 0),
    (summable_geometric_two.mul_left (D 0)).add (summable_of_ne_finset_zero (s := range M₀)
      fun N hN => by rw [Finset.mem_range] at hN; rw [if_neg hN]), fun N x hx0 hx1 => ?_⟩
  have hpts : ∀ v, (v = 0 ∨ v ∈ fejerHeights hloc N ∨ -v ∈ fejerHeights hloc N) →
      (D v ≠ 0 ∨ v = 0) ∧ |v| ≤ (N : ℝ) + 1 := by
    intro v hv
    rcases hv with rfl | hv | hv
    · exact ⟨Or.inr rfl, by simp; positivity⟩
    · exact ⟨Or.inl (mem_fejerHeights.mp hv).1.1, (mem_fejerHeights.mp hv).1.2⟩
    · have h := (mem_fejerHeights.mp hv).1
      rw [hpd.even, abs_neg] at h
      exact ⟨Or.inl h.1, h.2⟩
  have hcfg := fejerConfig_isFiniteConfig hpd hloc N
  have hxa : ∀ M, x + blockDamp hloc M ∈ Set.Icc (0 : ℝ) 2 := fun M =>
    ⟨by linarith [blockDamp_pos hloc M], by linarith [blockDamp_le_one hloc M]⟩
  -- The value at `w = 0` cancels; at the other differences `|w| ≥ δ`.
  have hdiag : ∀ B : ℝ, 0 ≤ B → (∀ w, w ≠ 0 → δ ≤ |w| → |w| ≤ |u| + N + 1 →
      |blockDiff hloc N x w| ≤ B) → |blockRem hloc N x u| ≤ D 0 * B * blockSize hloc N := by
    intro B hB hw
    unfold blockRem blockSize
    refine abs_convQ_sub_le hcfg (abs_fejerConfig_le hpd N) fun v hv => ?_
    obtain ⟨hv1, hv2⟩ := hpts v hv
    by_cases h0 : u - v = 0
    · rw [h0, diracAt, if_pos rfl, one_mul, sub_self, abs_zero]
      exact hB
    · rw [diracAt, if_neg h0, zero_mul, sub_zero]
      have hvu : v ≠ u := fun h => h0 (by rw [h, sub_self])
      refine hw _ h0 (hgap v hv1 hvu) ?_
      have := abs_sub u v
      linarith
  beta_reduce
  by_cases hN : N < M₀
  · rw [if_pos hN]
    have hb := hdiag (2 * |C|) (by positivity) fun w _ hwδ hwW => by
      have hW : |w| ≤ |u| + M₀ + 1 := by
        have : (N : ℝ) ≤ M₀ := by exact_mod_cast hN.le
        linarith
      have hX : ∀ M, |zetaX (x + blockDamp hloc M) w| ≤ |C| := fun M =>
        (hC _ w (hxa M) hwδ hW).trans (le_abs_self C)
      unfold blockDiff
      calc |zetaX (x + blockDamp hloc N) w - prevX hloc N x w|
          ≤ |zetaX (x + blockDamp hloc N) w| + |prevX hloc N x w| := abs_sub _ _
        _ ≤ |C| + |C| := add_le_add (hX N) (abs_prevX_le hloc N (abs_nonneg C) hX)
        _ = 2 * |C| := by ring
    have : 0 ≤ D 0 * (1 / 2) ^ N := by positivity
    linarith
  · rw [if_neg hN, add_zero]
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    have hc1 : ⌈1 / δ⌉₊ ≤ N' + 1 := by omega
    have hc2 : ⌈|u|⌉₊ ≤ N' + 1 := by omega
    have hc1' : (⌈1 / δ⌉₊ : ℝ) ≤ N' + 1 := by exact_mod_cast hc1
    have hc2' : (⌈|u|⌉₊ : ℝ) ≤ N' + 1 := by exact_mod_cast hc2
    have hb := hdiag (1 / (2 ^ (N' + 1) * blockSize hloc (N' + 1))) (by
      have := one_le_blockSize hloc (N' + 1); positivity) fun w _ hwδ hwW => by
      unfold blockDiff
      simp only [prevX]
      have hδN : 1 / (((N' + 1 : ℕ) : ℝ) + 1) ≤ |w| := by
        refine le_trans ?_ hwδ
        rw [one_div_le (by positivity) hδ]
        push_cast
        linarith [Nat.le_ceil (1 / δ)]
      have hWN : |w| ≤ 3 * (((N' + 1 : ℕ) : ℝ) + 1) := by
        push_cast at hwW ⊢
        linarith [Nat.le_ceil |u|]
      have hab : |(x + blockDamp hloc (N' + 1)) - (x + blockDamp hloc N')| <
          blockModulus hloc (N' + 1) := by
        rw [show (x + blockDamp hloc (N' + 1)) - (x + blockDamp hloc N') =
          -(blockDamp hloc N' - blockDamp hloc (N' + 1)) by ring, abs_neg,
          abs_of_pos (sub_pos.mpr (blockDamp_succ_lt hloc N'))]
        linarith [blockDamp_le_modulus hloc N', blockDamp_pos hloc (N' + 1)]
      exact (blockModulus_spec hloc (N' + 1) (hxa _) (hxa _) hδN hWN hab).le
    calc |blockRem hloc (N' + 1) x u|
        ≤ D 0 * (1 / (2 ^ (N' + 1) * blockSize hloc (N' + 1))) * blockSize hloc (N' + 1) := hb
      _ = D 0 * (1 / 2) ^ (N' + 1) := by
          have := one_le_blockSize hloc (N' + 1)
          rw [one_div_pow]
          field_simp

/-- **The arithmetic trace converges to `D`.** -/
theorem tendsto_arithTrace (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) (u : ℝ) :
    Tendsto (fun x => x * cosineTrace (arithWeight hloc x) logFrequency u) (𝓝[>] 0)
      (𝓝 (D u)) := by
  obtain ⟨K, hK, hRK⟩ := exists_blockRem_bound hpd hloc u
  -- Diagonal: Toeplitz averaging of the truncations.
  have hmain : Tendsto (fun x => ∑' N, x * blockDiff hloc N x 0 * fejerConfig D N u) (𝓝[>] 0)
      (𝓝 (D u)) := by
    refine tendsto_toeplitz (q := fun x N => x * blockDiff hloc N x 0)
      (e := fun N => fejerConfig D N u) (B := D 0) ?_ ?_ ?_ (fun N => ?_) ?_
      (fun N => abs_fejerConfig_le hpd N u)
    · filter_upwards [self_mem_nhdsWithin] with x hx N
      exact mul_nonneg (le_of_lt hx) (blockDiff_zero_nonneg hloc N hx)
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact (hasSum_blockDiff_zero hloc hx).summable.mul_left x
    · have h := zeta_isBoundaryDivisor.tendsto 0
      rw [zetaBoundaryDivisor_eq, if_pos rfl] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [tsum_mul_left, (hasSum_blockDiff_zero hloc hx).tsum_eq, zetaX_eq_trace hx]
    · have h0 : Tendsto (fun x : ℝ => x * zetaX (blockDamp hloc N) 0) (𝓝[>] 0) (𝓝 0) := by
        simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const
          (zetaX (blockDamp hloc N) 0)).mono_left nhdsWithin_le_nhds
      refine squeeze_zero' ?_ ?_ h0
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact mul_nonneg (le_of_lt hx) (blockDiff_zero_nonneg hloc N hx)
      · filter_upwards [self_mem_nhdsWithin] with x hx
        exact mul_le_mul_of_nonneg_left (blockDiff_zero_le hloc N hx) (le_of_lt hx)
    · have := (tendsto_fejerFactor u).const_mul (D u)
      rw [mul_one] at this
      exact this
  -- Off the diagonal: at most `x Σ K`.
  have hrem : Tendsto (fun x => x * ∑' N, blockRem hloc N x u) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun x : ℝ => x * ∑' N, K N) (𝓝[>] 0) (𝓝 0) := by
      simpa using ((tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (∑' N, K N)).mono_left
        nhdsWithin_le_nhds
    refine squeeze_zero_norm' ?_ h0
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hx.1]
    refine mul_le_mul_of_nonneg_left ?_ hx.1.le
    have hs : Summable fun N => blockRem hloc N x u :=
      Summable.of_norm_bounded hK fun N => by rw [Real.norm_eq_abs]; exact hRK N x hx.1 hx.2
    rw [← Real.norm_eq_abs]
    exact (norm_tsum_le_tsum_norm hs.norm).trans (Summable.tsum_le_tsum
      (fun N => by rw [Real.norm_eq_abs]; exact hRK N x hx.1 hx.2) hs.norm hK)
  have hlim := hmain.add hrem
  rw [add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with x hx
  have hs1 : Summable fun N => fejerConfig D N u * blockDiff hloc N x 0 :=
    Summable.of_norm_bounded ((hasSum_blockDiff_zero hloc hx.1).summable.mul_left (D 0))
      fun N => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (blockDiff_zero_nonneg hloc N hx.1)]
        exact mul_le_mul_of_nonneg_right (abs_fejerConfig_le hpd N u)
          (blockDiff_zero_nonneg hloc N hx.1)
  have hs2 : Summable fun N => blockRem hloc N x u :=
    Summable.of_norm_bounded hK fun N => by rw [Real.norm_eq_abs]; exact hRK N x hx.1 hx.2
  have hconv : (fun N => convQ (fejerConfig D N) (fejerHeights hloc N) (blockDiff hloc N x) u) =
      fun N => fejerConfig D N u * blockDiff hloc N x 0 + blockRem hloc N x u :=
    funext fun N => by unfold blockRem; ring
  have e1 : x * ∑' N, fejerConfig D N u * blockDiff hloc N x 0 =
      ∑' N, x * blockDiff hloc N x 0 * fejerConfig D N u := by
    rw [← tsum_mul_left]
    exact tsum_congr fun N => by ring
  rw [arithTrace_eq hpd hloc hx.1 u, hconv, Summable.tsum_add hs1 hs2, mul_add, e1]

/-- **The arithmetic realization.** A locally finite even positive-definite `D` is the boundary
divisor of the single Dirichlet series `Σ_n Λ(n) g(log n) n^{−s}` with the profile
`g = arithProfile ≥ 0`. -/
theorem arithmetic_isBoundaryDivisor (hpd : IsEvenPosDef D)
    (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) :
    IsBoundaryDivisor logFrequency (arithWeight hloc) D where
  nonneg x _ n := mul_nonneg (zetaBoundaryWeight_nonneg x n)
    (arithProfile_nonneg hpd hloc (Real.log_natCast_nonneg n))
  summable _ hx := summable_arithWeight hpd hloc hx
  tendsto := tendsto_arithTrace hpd hloc

/-- **Arithmetic Bochner theorem.** For locally finite `D` the following are equivalent: `D` is the
boundary divisor of some nonnegative weights; `D` is even and positive definite; `D` is the boundary
divisor of one Dirichlet series `Σ Λ(n) g(log n) n^{−s}` with `g ≥ 0`. -/
theorem arithmetic_bochner (hloc : ∀ R : ℝ, {v : ℝ | D v ≠ 0 ∧ |v| ≤ R}.Finite) :
    ((∃ (ι : Type) (lam : ι → ℝ) (w : ℝ → ι → ℝ), IsBoundaryDivisor lam w D) ↔
        IsEvenPosDef D) ∧
      (IsEvenPosDef D ↔ ∃ g : ℝ → ℝ, (∀ t, 0 ≤ t → 0 ≤ g t) ∧
        IsBoundaryDivisor logFrequency (fun x n => zetaBoundaryWeight x n * g (logFrequency n)) D) :=
  ⟨locallyFinite_boundary_divisor_iff hloc,
    ⟨fun hpd => ⟨arithProfile hloc, fun _ ht => arithProfile_nonneg hpd hloc ht,
      arithmetic_isBoundaryDivisor hpd hloc⟩, fun ⟨_, _, hg⟩ => hg.isEvenPosDef⟩⟩

end GaloisForLFunctions.MultiplicativePositivityGeometry
