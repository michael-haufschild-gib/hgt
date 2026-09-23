import GaloisForLFunctions.RHTower.PrimeHigherMertens

/-!
# Bounded critical prime sampling forces logarithmic kernel microlocalization

Let `H` be a Hilbert space carrying a family of normalized evaluation vectors `e x`, `‖e x‖ = 1`,
indexed by the prime-logarithm coordinate.  Say the family is *Bessel for the critical prime
weights* `w_p = (log p)² / p` when

`∑_p w_p |⟪e (log p), f⟫|² ≤ B² ‖f‖²`   for every `f`.

Testing this on `f = e x` gives the exact necessary condition `∑_p w_p C(x, log p) ≤ B²`, where
`C(x, y) = |⟪e y, e x⟫|²` is the squared normalized kernel coherence.  Because the prime mass of a
logarithmic window has the uniform asymptotic

`∑_{|log p - x| ≤ r} (log p)² / p = 2 x r + o(1)`   uniformly for `0 < r ≤ 1`,

any radius on which the coherence stays above a fixed level `c > 0` satisfies `x r(x) ≤ B²/(2c)`
asymptotically.  At a prime cutoff `N` this is the `O(1/log N)` law.

The window asymptotic is the second-order Mertens theorem `∑_{p ≤ X} (log p)²/p = (log X)²/2 + C
+ o(1)`, which the corpus already proves unconditionally from the de la Vallée Poussin error term.

For a de Branges carrier with phase `φ` the coherence is
`C(x, y) = sin(φ x - φ y)² / ((x - y)² φ'(x) φ'(y))`, and local phase regularity turns the coherence
law into the phase-speed bound `φ'(x) ≫ x`.
-/

open Filter Topology Set MeasureTheory
open scoped InnerProductSpace ComplexConjugate

namespace RHTower

noncomputable section

/-! ## The prime mass of a logarithmic window -/

/-- `∑_{e^{x-r} < p ≤ e^{x+r}} (log p)² / p`. -/
def primeLogWindowMass (x r : ℝ) : ℝ :=
  primeLogPowSum 2 (Real.exp (x + r)) - primeLogPowSum 2 (Real.exp (x - r))

theorem primeLogWindowMass_eq_sum (x : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    primeLogWindowMass x r
      = ∑ n ∈ Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊, primeLogPowWeight 2 n := by
  have hle : ⌊Real.exp (x - r)⌋₊ ≤ ⌊Real.exp (x + r)⌋₊ :=
    Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith))
  have hunion : Finset.Icc 0 ⌊Real.exp (x - r)⌋₊
      ∪ Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊
      = Finset.Icc 0 ⌊Real.exp (x + r)⌋₊ := by
    ext a
    simp only [Finset.mem_union, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hdisj : Disjoint (Finset.Icc 0 ⌊Real.exp (x - r)⌋₊)
      (Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    have h1 := (Finset.mem_Icc.mp ha).2
    have h2 := (Finset.mem_Ioc.mp ha').1
    omega
  rw [primeLogWindowMass, primeLogPowSum, primeLogPowSum, ← hunion, Finset.sum_union hdisj]
  ring

/-- Every index of the window sum lies in the logarithmic window. -/
theorem abs_log_sub_le_of_mem_window {x r : ℝ} {n : ℕ}
    (hn : n ∈ Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊) :
    |Real.log n - x| ≤ r := by
  obtain ⟨h1, h2⟩ := Finset.mem_Ioc.mp hn
  have hn0 : n ≠ 0 := by omega
  have hlow : Real.exp (x - r) < (n : ℝ) := (Nat.floor_lt' hn0).mp h1
  have hhigh : (n : ℝ) ≤ Real.exp (x + r) :=
    (Nat.le_floor_iff (Real.exp_nonneg _)).mp h2
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (Real.exp_pos _) hlow
  have hL : x - r < Real.log n := by
    have := Real.log_lt_log (Real.exp_pos (x - r)) hlow
    rwa [Real.log_exp] at this
  have hR : Real.log n ≤ x + r := by
    have := Real.log_le_log hnpos hhigh
    rwa [Real.log_exp] at this
  rw [abs_le]
  constructor <;> linarith

/-- **Equation (8).**  Uniformly for `0 < r ≤ 1`, the prime mass of the logarithmic window of
radius `r` about `x` is `2 x r + o(1)`. -/
theorem primeLogWindowMass_uniform_asymptotic {ε : ℝ} (hε : 0 < ε) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ r : ℝ, 0 < r → r ≤ 1 →
      |primeLogWindowMass x r - 2 * x * r| < ε := by
  set C : ℝ := mertensLogPowConstantFull 1 with hC
  have hT : Tendsto (fun X : ℝ => primeLogPowSum 2 X - (Real.log X) ^ (2 : ℕ) / 2) atTop (𝓝 C) := by
    have h := tendsto_primeLogPowSum_sub 1
    refine h.congr fun X => ?_
    norm_num
  obtain ⟨X₀, hX₀⟩ := (eventually_atTop.mp
    (hT.eventually (Metric.ball_mem_nhds C (half_pos hε))))
  set Y : ℝ := max 1 X₀ with hY
  have hY1 : (0 : ℝ) < Y := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨Real.log Y + 1, fun x hx r hr0 hr1 => ?_⟩
  have hge : ∀ s : ℝ, x - 1 ≤ s → X₀ ≤ Real.exp s := by
    intro s hs
    have h1 : Real.log Y ≤ s := by linarith
    have h2 : Real.exp (Real.log Y) ≤ Real.exp s := Real.exp_le_exp.mpr h1
    rw [Real.exp_log hY1] at h2
    exact le_trans (le_max_right _ _) h2
  have hplus : X₀ ≤ Real.exp (x + r) := hge _ (by linarith)
  have hminus : X₀ ≤ Real.exp (x - r) := hge _ (by linarith)
  have hFp := hX₀ _ hplus
  have hFm := hX₀ _ hminus
  rw [Real.dist_eq] at hFp hFm
  have hsplit : primeLogWindowMass x r - 2 * x * r
      = (primeLogPowSum 2 (Real.exp (x + r)) - (Real.log (Real.exp (x + r))) ^ (2 : ℕ) / 2 - C)
        - (primeLogPowSum 2 (Real.exp (x - r)) - (Real.log (Real.exp (x - r))) ^ (2 : ℕ) / 2 - C) := by
    rw [primeLogWindowMass, Real.log_exp, Real.log_exp]
    ring
  rw [hsplit]
  calc |(primeLogPowSum 2 (Real.exp (x + r)) - (Real.log (Real.exp (x + r))) ^ (2 : ℕ) / 2 - C)
        - (primeLogPowSum 2 (Real.exp (x - r)) - (Real.log (Real.exp (x - r))) ^ (2 : ℕ) / 2 - C)|
      ≤ |primeLogPowSum 2 (Real.exp (x + r)) - (Real.log (Real.exp (x + r))) ^ (2 : ℕ) / 2 - C|
        + |primeLogPowSum 2 (Real.exp (x - r)) - (Real.log (Real.exp (x - r))) ^ (2 : ℕ) / 2 - C| :=
        abs_sub _ _
    _ < ε := by linarith

/-! ## Normalized kernel coherence -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Equation (1).**  The squared normalized kernel coherence. -/
def kernelCoherence (K : ℝ → ℝ → ℂ) (x y : ℝ) : ℝ :=
  ‖K x y‖ ^ (2 : ℕ) / (‖K x x‖ * ‖K y y‖)

/-- The coherence is unchanged by a nonvanishing gauge `K (x,y) ↦ G x * conj (G y) * K (x,y)`. -/
theorem kernelCoherence_gauge (K : ℝ → ℝ → ℂ) {G : ℝ → ℂ} (hG : ∀ x, G x ≠ 0) (x y : ℝ) :
    kernelCoherence (fun u v => G u * conj (G v) * K u v) x y = kernelCoherence K x y := by
  have hnorm : ∀ u v : ℝ, ‖G u * conj (G v) * K u v‖ = ‖G u‖ * ‖G v‖ * ‖K u v‖ := by
    intro u v
    rw [norm_mul, norm_mul, RCLike.norm_conj]
  have hGx : ‖G x‖ ≠ 0 := norm_ne_zero_iff.mpr (hG x)
  have hGy : ‖G y‖ ≠ 0 := norm_ne_zero_iff.mpr (hG y)
  rw [kernelCoherence, kernelCoherence, hnorm, hnorm, hnorm]
  rw [show (‖G x‖ * ‖G y‖ * ‖K x y‖) ^ (2 : ℕ)
      = (‖G x‖ ^ (2 : ℕ) * ‖G y‖ ^ (2 : ℕ)) * ‖K x y‖ ^ (2 : ℕ) by ring,
    show ‖G x‖ * ‖G x‖ * ‖K x x‖ * (‖G y‖ * ‖G y‖ * ‖K y y‖)
      = (‖G x‖ ^ (2 : ℕ) * ‖G y‖ ^ (2 : ℕ)) * (‖K x x‖ * ‖K y y‖) by ring]
  exact mul_div_mul_left _ _ (by positivity)

/-- The squared coherence of two normalized evaluation vectors. -/
def unitCoherence (e : ℝ → H) (x y : ℝ) : ℝ := ‖⟪e y, e x⟫_ℂ‖ ^ (2 : ℕ)

theorem kernelCoherence_gram (k : ℝ → H) (x y : ℝ) :
    kernelCoherence (fun u v => ⟪k v, k u⟫_ℂ) x y
      = ‖⟪k y, k x⟫_ℂ‖ ^ (2 : ℕ) / (‖k x‖ ^ (2 : ℕ) * ‖k y‖ ^ (2 : ℕ)) := by
  have hself : ∀ u : ℝ, ‖⟪k u, k u⟫_ℂ‖ = ‖k u‖ ^ (2 : ℕ) := by
    intro u
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [kernelCoherence, hself, hself]

theorem norm_normalized (k : ℝ → H) {x : ℝ} (hk : k x ≠ 0) :
    ‖((‖k x‖ : ℂ))⁻¹ • k x‖ = 1 := by
  have hne : ‖k x‖ ≠ 0 := norm_ne_zero_iff.mpr hk
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hne]

/-- Normalizing the evaluation vectors turns the kernel coherence into the unit coherence. -/
theorem unitCoherence_normalized (k : ℝ → H) (x y : ℝ) :
    unitCoherence (fun t => ((‖k t‖ : ℂ))⁻¹ • k t) x y
      = kernelCoherence (fun u v => ⟪k v, k u⟫_ℂ) x y := by
  rw [unitCoherence, kernelCoherence_gram, inner_smul_left, inner_smul_right, map_inv₀,
    Complex.conj_ofReal, norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    abs_of_nonneg (norm_nonneg _), mul_pow, mul_pow, div_eq_mul_inv, mul_inv, ← inv_pow,
    ← inv_pow]
  ring

theorem unitCoherence_self {e : ℝ → H} (hunit : ∀ y, ‖e y‖ = 1) (x : ℝ) :
    unitCoherence e x x = 1 := by
  rw [unitCoherence, inner_self_eq_norm_sq_to_K, hunit x]
  norm_num

theorem unitCoherence_nonneg (e : ℝ → H) (x y : ℝ) : 0 ≤ unitCoherence e x y := by
  rw [unitCoherence]
  positivity

/-! ## The Bessel hypothesis and the kernel testing law -/

/-- **Equation (4).**  The normalized critical-prime sampling operator is bounded by `B`. -/
def PrimeSamplingBessel (e : ℝ → H) (B : ℝ) : Prop :=
  ∀ (S : Finset ℕ) (f : H),
    ∑ n ∈ S, primeLogPowWeight 2 n * ‖⟪e (Real.log n), f⟫_ℂ‖ ^ (2 : ℕ) ≤ B ^ (2 : ℕ) * ‖f‖ ^ (2 : ℕ)

theorem primeLogPowWeight_two_nonneg (n : ℕ) : 0 ≤ primeLogPowWeight 2 n := by
  rw [primeLogPowWeight]
  split
  · exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  · exact le_refl 0

/-- **Equation (5).**  Testing the Bessel bound on a normalized evaluation vector. -/
theorem primeSampling_kernel_test {e : ℝ → H} {B : ℝ} (hunit : ∀ y, ‖e y‖ = 1)
    (hB : PrimeSamplingBessel e B) (S : Finset ℕ) (x : ℝ) :
    ∑ n ∈ S, primeLogPowWeight 2 n * unitCoherence e x (Real.log n) ≤ B ^ (2 : ℕ) := by
  have h := hB S (e x)
  rw [hunit x] at h
  simpa only [unitCoherence, one_pow, mul_one] using h

/-- **Equation (7).**  A uniform coherence floor on a logarithmic window bounds the window's
prime mass. -/
theorem primeLogWindowMass_le {e : ℝ → H} {B c : ℝ} (hunit : ∀ y, ‖e y‖ = 1)
    (hB : PrimeSamplingBessel e B) (x : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hcoh : ∀ y : ℝ, |y - x| ≤ r → c ≤ unitCoherence e x y) :
    c * primeLogWindowMass x r ≤ B ^ (2 : ℕ) := by
  have hstep : c * primeLogWindowMass x r
      ≤ ∑ n ∈ Finset.Ioc ⌊Real.exp (x - r)⌋₊ ⌊Real.exp (x + r)⌋₊,
          primeLogPowWeight 2 n * unitCoherence e x (Real.log n) := by
    rw [primeLogWindowMass_eq_sum x hr, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [mul_comm c (primeLogPowWeight 2 n)]
    exact mul_le_mul_of_nonneg_left (hcoh _ (abs_log_sub_le_of_mem_window hn))
      (primeLogPowWeight_two_nonneg n)
  exact le_trans hstep (primeSampling_kernel_test hunit hB _ x)

/-! ## The logarithmic microlocalization theorem -/

/-- **Equation (11).**  A fixed positive coherence level cannot persist on a radius wider than
`B² / (2 c x)`. -/
theorem prime_coherence_radius_bound {e : ℝ → H} {B c : ℝ} (hunit : ∀ y, ‖e y‖ = 1)
    (hB : PrimeSamplingBessel e B) (hc : 0 < c) {r : ℝ → ℝ}
    (hr0 : ∀ x, 0 < r x) (hr1 : ∀ x, r x ≤ 1)
    (hcoh : ∀ x y : ℝ, |y - x| ≤ r x → c ≤ unitCoherence e x y)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, x * r x ≤ B ^ (2 : ℕ) / (2 * c) + ε := by
  obtain ⟨X, hX⟩ := primeLogWindowMass_uniform_asymptotic hε
  filter_upwards [eventually_ge_atTop X] with x hx
  have hw := hX x hx (r x) (hr0 x) (hr1 x)
  have hbound := primeLogWindowMass_le hunit hB x (hr0 x).le (fun y hy => hcoh x y hy)
  rw [abs_lt] at hw
  have h2 : c * (2 * x * r x - ε) < c * primeLogWindowMass x (r x) :=
    mul_lt_mul_of_pos_left (by linarith [hw.1]) hc
  have h3 : c * (2 * x * r x - ε) < B ^ (2 : ℕ) := lt_of_lt_of_le h2 hbound
  have hexp : B ^ (2 : ℕ) / (2 * c) * (2 * c) = B ^ (2 : ℕ) := by field_simp
  nlinarith [h3, hexp, hc, hε]

/-- **Equation (12).**  At the prime cutoff `N` the coherence radius is `O(1/log N)`. -/
theorem prime_coherence_radius_cutoff {e : ℝ → H} {B c : ℝ} (hunit : ∀ y, ‖e y‖ = 1)
    (hB : PrimeSamplingBessel e B) (hc : 0 < c) {r : ℝ → ℝ}
    (hr0 : ∀ x, 0 < r x) (hr1 : ∀ x, r x ≤ 1)
    (hcoh : ∀ x y : ℝ, |y - x| ≤ r x → c ≤ unitCoherence e x y)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℝ in atTop,
      r (Real.log N) ≤ (B ^ (2 : ℕ) / (2 * c) + ε) / Real.log N := by
  have hmain := prime_coherence_radius_bound hunit hB hc hr0 hr1 hcoh hε
  have hlog : Tendsto (fun N : ℝ => Real.log N) atTop atTop := Real.tendsto_log_atTop
  filter_upwards [hlog.eventually hmain, hlog.eventually_gt_atTop 0] with N hN hpos
  rw [le_div_iff₀ hpos]
  linarith [hN]

/-! ## The de Branges phase corollary -/

theorem abs_sin_ge_of_abs_le {u : ℝ} (h : |u| ≤ Real.pi / 2) :
    2 / Real.pi * |u| ≤ |Real.sin u| := by
  have hpi := Real.pi_pos
  rcases le_or_gt 0 u with hu | hu
  · have hle : u ≤ Real.pi / 2 := by rwa [abs_of_nonneg hu] at h
    rw [abs_of_nonneg hu,
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hu (by linarith))]
    exact Real.mul_le_sin hu hle
  · have hu' : (0 : ℝ) ≤ -u := by linarith
    have hle : -u ≤ Real.pi / 2 := by rwa [abs_of_neg hu] at h
    rw [abs_of_neg hu, ← abs_neg (Real.sin u), ← Real.sin_neg,
      abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hu' (by linarith))]
    exact Real.mul_le_sin hu' hle

theorem sq_sin_ge_of_abs_le {u : ℝ} (h : |u| ≤ Real.pi / 2) :
    (2 / Real.pi) ^ (2 : ℕ) * u ^ (2 : ℕ) ≤ Real.sin u ^ (2 : ℕ) := by
  have h1 := abs_sin_ge_of_abs_le h
  have h2 : (0 : ℝ) ≤ 2 / Real.pi * |u| := by positivity
  nlinarith [h1, h2, sq_abs u, sq_abs (Real.sin u)]

/-- The mean value theorem in the form used by the phase estimate. -/
theorem exists_mvt_between {φ φ' : ℝ → ℝ} (hderiv : ∀ t, HasDerivAt φ (φ' t) t) {x y : ℝ}
    (hne : y ≠ x) :
    ∃ ξ : ℝ, |ξ - x| ≤ |y - x| ∧ φ x - φ y = φ' ξ * (x - y) := by
  have hdiff : Differentiable ℝ φ := fun t => (hderiv t).differentiableAt
  have hcont : Continuous φ := hdiff.continuous
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨ξ, hξ, hval⟩ := exists_hasDerivAt_eq_slope φ φ' hlt hcont.continuousOn
      (fun t _ => hderiv t)
    refine ⟨ξ, ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hξ
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · rw [hval]
      field_simp
  · obtain ⟨ξ, hξ, hval⟩ := exists_hasDerivAt_eq_slope φ φ' hgt hcont.continuousOn
      (fun t _ => hderiv t)
    refine ⟨ξ, ?_, ?_⟩
    · obtain ⟨h1, h2⟩ := hξ
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · rw [hval]
      field_simp
      ring

/-- **Equation (13).**  The normalized coherence of a de Branges kernel through its phase. -/
def phaseCoherence (φ φ' : ℝ → ℝ) (x y : ℝ) : ℝ :=
  Real.sin (φ x - φ y) ^ (2 : ℕ) / ((x - y) ^ (2 : ℕ) * φ' x * φ' y)

/-- **Equation (15).**  Local phase regularity gives a uniform coherence floor on the radius
`1 / (2 M φ'(x))`. -/
theorem phaseCoherence_ge {φ φ' : ℝ → ℝ} (hderiv : ∀ t, HasDerivAt φ (φ' t) t)
    {M : ℝ} (hM : 1 ≤ M) {x : ℝ} (hx : 0 < φ' x)
    (hreg : ∀ t : ℝ, |t - x| ≤ 1 / (2 * M * φ' x) → φ' x / M ≤ φ' t ∧ φ' t ≤ M * φ' x)
    {y : ℝ} (hy : |y - x| ≤ 1 / (2 * M * φ' x)) (hne : y ≠ x) :
    4 / (Real.pi ^ (2 : ℕ) * M ^ (3 : ℕ)) ≤ phaseCoherence φ φ' x y := by
  have hpi := Real.pi_pos
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  obtain ⟨ξ, hξx, hval⟩ := exists_mvt_between hderiv hne
  obtain ⟨hξl, hξu⟩ := hreg ξ (le_trans hξx hy)
  obtain ⟨hyl, hyu⟩ := hreg y hy
  have hξpos : 0 < φ' ξ := lt_of_lt_of_le (by positivity) hξl
  have hypos : 0 < φ' y := lt_of_lt_of_le (by positivity) hyl
  have hxy : x - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hxy2 : (0 : ℝ) < (x - y) ^ (2 : ℕ) := by positivity
  have habs : |φ x - φ y| ≤ 1 / 2 := by
    have h1 : |x - y| ≤ 1 / (2 * M * φ' x) := by rwa [abs_sub_comm]
    have hcalc : φ' ξ * |x - y| ≤ M * φ' x * (1 / (2 * M * φ' x)) :=
      mul_le_mul hξu h1 (abs_nonneg _) (by positivity)
    have hval2 : M * φ' x * (1 / (2 * M * φ' x)) = 1 / 2 := by field_simp
    rw [hval, abs_mul, abs_of_pos hξpos]
    linarith [hcalc, hval2]
  have hpiub : |φ x - φ y| ≤ Real.pi / 2 := by
    have := Real.pi_gt_three
    linarith [habs]
  have hsin := sq_sin_ge_of_abs_le hpiub
  have hnum : (φ' x / M) ^ (2 : ℕ) * (x - y) ^ (2 : ℕ) ≤ (φ x - φ y) ^ (2 : ℕ) := by
    rw [hval, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hξl 2) (le_of_lt hxy2)
  have hden : (x - y) ^ (2 : ℕ) * φ' x * φ' y ≤ (x - y) ^ (2 : ℕ) * φ' x * (M * φ' x) :=
    mul_le_mul_of_nonneg_left hyu (by positivity)
  have hden0 : (0 : ℝ) < (x - y) ^ (2 : ℕ) * φ' x * φ' y := by positivity
  rw [phaseCoherence, le_div_iff₀ hden0]
  calc 4 / (Real.pi ^ (2 : ℕ) * M ^ (3 : ℕ)) * ((x - y) ^ (2 : ℕ) * φ' x * φ' y)
      ≤ 4 / (Real.pi ^ (2 : ℕ) * M ^ (3 : ℕ)) * ((x - y) ^ (2 : ℕ) * φ' x * (M * φ' x)) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
    _ = (2 / Real.pi) ^ (2 : ℕ) * ((φ' x / M) ^ (2 : ℕ) * (x - y) ^ (2 : ℕ)) := by
        field_simp
        ring
    _ ≤ (2 / Real.pi) ^ (2 : ℕ) * (φ x - φ y) ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
    _ ≤ Real.sin (φ x - φ y) ^ (2 : ℕ) := hsin

/-- The off-diagonal real-axis de Branges kernel of `E = A - i B`, i.e.
`K(x,y) = (B y * A x - A y * B x) / (π (y - x))`. -/
def deBrangesKernelOffDiag (A B : ℝ → ℝ) (x y : ℝ) : ℝ :=
  (B y * A x - A y * B x) / (Real.pi * (y - x))

/-- In polar form `E = m e^{-iφ}`, i.e. `A = m cos φ` and `B = m sin φ`, the off-diagonal kernel
is `m x * m y * sin (φ y - φ x) / (π (y - x))`. -/
theorem deBrangesKernelOffDiag_polar (m φ : ℝ → ℝ) (x y : ℝ) :
    deBrangesKernelOffDiag (fun t => m t * Real.cos (φ t)) (fun t => m t * Real.sin (φ t)) x y
      = m x * m y * Real.sin (φ y - φ x) / (Real.pi * (y - x)) := by
  rw [deBrangesKernelOffDiag, Real.sin_sub]
  ring

/-- The real-axis de Branges kernel of a structure function with modulus `m`, phase `φ` and phase
derivative `φ'`.  The diagonal value `m² φ' / π` is the limit of the off-diagonal formula. -/
def deBrangesRealKernel (m φ φ' : ℝ → ℝ) (x y : ℝ) : ℂ :=
  if x = y then ((m x ^ (2 : ℕ) * φ' x / Real.pi : ℝ) : ℂ)
  else ((deBrangesKernelOffDiag (fun t => m t * Real.cos (φ t))
    (fun t => m t * Real.sin (φ t)) x y : ℝ) : ℂ)

/-- **Equation (13).**  The normalized coherence of a de Branges kernel is the phase expression
`sin (φ x - φ y)² / ((x - y)² φ'(x) φ'(y))`.  Both the modulus `m` and the constant `π` drop out. -/
theorem kernelCoherence_deBranges {m φ φ' : ℝ → ℝ} (hm : ∀ t, 0 < m t) (hφ : ∀ t, 0 < φ' t)
    {x y : ℝ} (hne : x ≠ y) :
    kernelCoherence (deBrangesRealKernel m φ φ') x y = phaseCoherence φ φ' x y := by
  have hpi := Real.pi_pos
  have hxy : y - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hoff : deBrangesRealKernel m φ φ' x y
      = ((m x * m y * Real.sin (φ y - φ x) / (Real.pi * (y - x)) : ℝ) : ℂ) := by
    rw [deBrangesRealKernel, if_neg hne, deBrangesKernelOffDiag_polar]
  have hdiag : ∀ t : ℝ, ‖deBrangesRealKernel m φ φ' t t‖ = m t ^ (2 : ℕ) * φ' t / Real.pi := by
    intro t
    have hnn : (0 : ℝ) ≤ m t ^ (2 : ℕ) * φ' t / Real.pi :=
      div_nonneg (mul_nonneg (sq_nonneg _) (hφ t).le) hpi.le
    rw [deBrangesRealKernel, if_pos rfl, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hnn]
  have hN : ‖deBrangesRealKernel m φ φ' x y‖ ^ (2 : ℕ)
      = (m x * m y * Real.sin (φ y - φ x)) ^ (2 : ℕ) / (Real.pi * (y - x)) ^ (2 : ℕ) := by
    rw [hoff, Complex.norm_real, Real.norm_eq_abs, sq_abs, div_pow]
  have hsin : Real.sin (φ x - φ y) ^ (2 : ℕ) = Real.sin (φ y - φ x) ^ (2 : ℕ) := by
    rw [show φ x - φ y = -(φ y - φ x) by ring, Real.sin_neg]
    ring
  have hsq : (x - y) ^ (2 : ℕ) = (y - x) ^ (2 : ℕ) := by ring
  have h1 : m x ≠ 0 := ne_of_gt (hm x)
  have h2 : m y ≠ 0 := ne_of_gt (hm y)
  have h3 : φ' x ≠ 0 := ne_of_gt (hφ x)
  have h4 : φ' y ≠ 0 := ne_of_gt (hφ y)
  have h5 : Real.pi ≠ 0 := ne_of_gt hpi
  rw [kernelCoherence, hN, hdiag, hdiag, phaseCoherence, hsin, hsq]
  field_simp

/-- **Equation (16).**  A locally regular de Branges carrier which admits bounded normalized
critical-prime sampling has at least linear phase speed. -/
theorem phase_speed_ge {e : ℝ → H} {B : ℝ} {φ φ' : ℝ → ℝ} {M : ℝ}
    (hunit : ∀ y, ‖e y‖ = 1) (hB : PrimeSamplingBessel e B)
    (hM : 1 ≤ M) (hderiv : ∀ t, HasDerivAt φ (φ' t) t) (hpos : ∀ t, 0 < φ' t)
    (hreg : ∀ x t : ℝ, |t - x| ≤ 1 / (2 * M * φ' x) → φ' x / M ≤ φ' t ∧ φ' t ≤ M * φ' x)
    (hcoh : ∀ x y : ℝ, y ≠ x → unitCoherence e x y = phaseCoherence φ φ' x y)
    {D : ℝ} (hD : Real.pi ^ (2 : ℕ) * M ^ (3 : ℕ) * B ^ (2 : ℕ) / 8 < D) :
    ∀ᶠ x : ℝ in atTop, 1 / (2 * M * D) ≤ φ' x / x := by
  have hpi := Real.pi_pos
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  have hD0 : (0 : ℝ) < D := lt_of_le_of_lt (by positivity) hD
  set c : ℝ := 4 / (Real.pi ^ (2 : ℕ) * M ^ (3 : ℕ)) with hcdef
  have hc : (0 : ℝ) < c := by rw [hcdef]; positivity
  have hcle : c ≤ 1 := by
    rw [hcdef, div_le_one (by positivity)]
    have h3 := Real.pi_gt_three
    nlinarith [one_le_pow₀ hM (n := 3), hM0, h3]
  set r : ℝ → ℝ := fun x => min 1 (1 / (2 * M * φ' x)) with hrdef
  have hr0 : ∀ x, 0 < r x := fun x => lt_min zero_lt_one (by have := hpos x; positivity)
  have hr1 : ∀ x, r x ≤ 1 := fun x => min_le_left _ _
  have hrle : ∀ x, r x ≤ 1 / (2 * M * φ' x) := fun x => min_le_right _ _
  have hcohfloor : ∀ x y : ℝ, |y - x| ≤ r x → c ≤ unitCoherence e x y := by
    intro x y hyx
    by_cases hne : y = x
    · rw [hne, unitCoherence_self hunit]
      exact hcle
    · rw [hcoh x y hne]
      exact phaseCoherence_ge hderiv hM (hpos x) (fun t ht => hreg x t ht)
        (le_trans hyx (hrle x)) hne
  set ε : ℝ := D - Real.pi ^ (2 : ℕ) * M ^ (3 : ℕ) * B ^ (2 : ℕ) / 8 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hsum : B ^ (2 : ℕ) / (2 * c) + ε = D := by
    rw [hcdef, hεdef]
    field_simp
    ring
  have hmain := prime_coherence_radius_bound hunit hB hc hr0 hr1 hcohfloor hε
  rw [hsum] at hmain
  filter_upwards [hmain, eventually_gt_atTop D, eventually_gt_atTop (0 : ℝ)] with x hx hxD hx0
  have hφ := hpos x
  have hnotone : r x ≠ 1 := by
    intro h
    rw [h, mul_one] at hx
    linarith
  have hrx : r x = 1 / (2 * M * φ' x) := by
    rcases min_cases 1 (1 / (2 * M * φ' x)) with ⟨h, _⟩ | ⟨h, _⟩
    · exact absurd (by rw [hrdef]; exact h) hnotone
    · rw [hrdef]; exact h
  rw [hrx] at hx
  have hpos2 : (0 : ℝ) < 2 * M * φ' x := by positivity
  have hkey : x ≤ 2 * M * D * φ' x := by
    rw [mul_one_div, div_le_iff₀ hpos2] at hx
    linarith [hx]
  rw [div_le_div_iff₀ (by positivity) hx0]
  linarith [hkey]

/-- **Equation (16)**, limit form: the phase speed is asymptotically at least
`4 / (π² M⁴ B²)` times the prime-log coordinate. -/
theorem phase_speed_liminf {e : ℝ → H} {B : ℝ} {φ φ' : ℝ → ℝ} {M : ℝ}
    (hunit : ∀ y, ‖e y‖ = 1) (hB : PrimeSamplingBessel e B) (hB0 : 0 < B)
    (hM : 1 ≤ M) (hderiv : ∀ t, HasDerivAt φ (φ' t) t) (hpos : ∀ t, 0 < φ' t)
    (hreg : ∀ x t : ℝ, |t - x| ≤ 1 / (2 * M * φ' x) → φ' x / M ≤ φ' t ∧ φ' t ≤ M * φ' x)
    (hcoh : ∀ x y : ℝ, y ≠ x → unitCoherence e x y = phaseCoherence φ φ' x y)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, 4 / (Real.pi ^ (2 : ℕ) * M ^ (4 : ℕ) * B ^ (2 : ℕ)) - ε ≤ φ' x / x := by
  have hpi := Real.pi_pos
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le zero_lt_one hM
  set D₀ : ℝ := Real.pi ^ (2 : ℕ) * M ^ (3 : ℕ) * B ^ (2 : ℕ) / 8 with hD₀def
  have hD₀ : (0 : ℝ) < D₀ := by rw [hD₀def]; positivity
  set δ : ℝ := min D₀ (2 * M * D₀ ^ (2 : ℕ) * ε) with hδdef
  have hδ : 0 < δ := lt_min hD₀ (by positivity)
  have hδle : δ ≤ 2 * M * D₀ ^ (2 : ℕ) * ε := min_le_right _ _
  set D : ℝ := D₀ + δ with hDdef
  have hDgt : D₀ < D := by rw [hDdef]; linarith
  have hD0 : (0 : ℝ) < D := by linarith
  have hbase : 4 / (Real.pi ^ (2 : ℕ) * M ^ (4 : ℕ) * B ^ (2 : ℕ)) = 1 / (2 * M * D₀) := by
    rw [hD₀def]
    field_simp
    ring
  have hgap : 1 / (2 * M * D₀) - 1 / (2 * M * D) ≤ ε := by
    have hnum : 1 / (2 * M * D₀) - 1 / (2 * M * D) = δ / (2 * M * D₀ * D) := by
      rw [hDdef]
      field_simp
      ring
    rw [hnum, div_le_iff₀ (by positivity)]
    nlinarith [hδle, hDgt, hD₀, hε, hM0]
  have hmain := phase_speed_ge hunit hB hM hderiv hpos hreg hcoh (D := D) hDgt
  filter_upwards [hmain] with x hx
  rw [hbase]
  linarith [hgap, hx]

end

end RHTower
