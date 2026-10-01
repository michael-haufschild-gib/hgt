import GaloisForLFunctions.RHTower.WeilFibreBochnerLaw
import GaloisForLFunctions.RHTower.WeilDeviationLocalMass

/-!
# The multiples-of-a-prime law of the Weil cone

**Theorem** (`not_tendsto_atTop_multiplesSum`, `not_tendsto_atBot_multiplesSum`). Let `lam` be
full-cone Weil-positive with `|lam(n) − Λ(n)| ≤ C (1 + Λ(n))` for all `n ≥ 2`, and let `p` be prime.
Then the harmonic sums `G_p(k) = Σ_{n≤k, p∣n} (lam(n) − Λ(n))/n` tend neither to `+∞` nor to `−∞`.

**Corollary** (`summable_multiples_of_nonneg`). If moreover `lam ≥ 0` on the multiples of `p` other
than `p`, then `Σ_{p∣n, n>p} lam(n)/n < ∞`. A Weil-positive weight system of size `O(1 + Λ)` puts
finite harmonic mass on the multiples of every fixed prime, as `Λ` does.

**Corollary** (`not_weilPositiveFull_of_semiprime_floor`). No such `lam` has a floor
`lam(pq) ≥ c > 0` on the semiprimes with a fixed prime factor `p`.

**The nonnegative cone** (`summable_multiples_of_weilPositiveFull_of_nonneg`,
`not_weilPositiveFull_of_nonneg_semiprime_floor`). The size condition is only used through the local
harmonic mass of `lam − Λ`, which is bounded for every nonnegative Weil-positive `lam`
(`exists_localMassBounded_of_nonneg`). So every full-cone Weil-positive `lam ≥ 0` has
`Σ_{p∣n, n>p} lam(n)/n < ∞` for every prime `p`, and no nonnegative semiprime floor is Weil-positive.

**Proof.**
* **Fibre law at a fixed level** (`exists_twistFibre_level_bound`). For a twist polynomial
  `q = |Σ c_a e^{itλ(a)}|²` the refined notch costs `C + η K log L` when `d = lam − Λ` is
  notch-bounded at level `η`, while a `q`-fibre level `Y` gives the main term `κ₁ Y log L`. Hence
  `Y ≤ (K/κ₁) η`. Deviations of size `C(1 + Λ)` are notch-bounded at level `2C`.
* **Pinning** (`exists_abs_sum_coneDeviation_div_le`). The harmonic windows of `d` are `O(L^{−2})`
  and its local mass is `O(C)`, so the partial sums `Σ_{n<N} d(n)/n` are bounded.
* **The twist `|1 + ε p^{it}|²`.** Its main weight is `(1 + ε² + 2ε/√p) n^{−½}` off the multiples
  of `p` and `(1 + ε² + ε(√p + 1/√p)) n^{−½}` on them, so the `q`-fibre sum is
  `(1 + ε² + 2ε/√p) Σ_{n≤k} d(n)/n + ε(√p − 1/√p) G_p(k)`. If `G_p → ±∞`, the choice `ε = ±1`
  makes it exceed every level.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.WeilAbscissa

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport RHTower.WeilLogSummable
open RHTower.PrimeSmallDeviation

variable {P : Finset ℕ}

/-! ## The fibre law at a fixed level -/

/-- **The fibre law at a fixed level, deviation form.** For a twist polynomial
`q = |Σ_{a∈A} c_a e^{itλ(a)}|²` there is `Y₀ ≥ 0` such that: if `−ψ_v` is positive definite,
`d(n) = √n v(n)` is notch-bounded at level `η`, and the partial sums of `v(n) W_q(n)` stay above `Y`,
then `Y ≤ Y₀ η`. -/
theorem exists_twistFibre_level_bound_of (hP : ∀ p ∈ P, p.Prime) (A : Finset (P → ℤ))
    (c : (P → ℤ) → ℝ) {β : P → ℕ} (hβ : ∀ a ∈ A, ∀ p, |a p| ≤ β p) :
    ∃ Y₀ : ℝ, 0 ≤ Y₀ ∧ ∀ {v : ℕ → ℝ}, v 0 = 0 → ∀ {Av : ℝ}, 0 ≤ Av →
      (∀ n, |v n| ≤ 2 * Real.log n + Av) →
      PositiveDefiniteOnReal (fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) →
      ∀ {η : ℝ}, 0 < η → NotchBounded (sqrtScaled v) η → ∀ {Y : ℝ} {T : ℕ},
      (∀ k, T ≤ k → Y ≤ rampPartial (fun n => v n * twistMainWeight P A c n) k) →
      Y ≤ Y₀ * η := by
  obtain ⟨Dr, hDr0, hDr⟩ :=
    exists_sum_re_weightedMoment_ge_ramp_twist hP A c hβ (K := 7) (by norm_num)
  obtain ⟨CQ, hCQ0, hQb1, hqb⟩ := exists_abs_twistNotchWeight_le A c
  obtain ⟨κ₁, Kc, hκ₁, hKc, h⟩ := exists_ramp_scale_bound_bounded_of
    (differentiable_twistNotchWeightC A c) hQb1 (twistNotchWeightC_ofReal A c)
    (twistNotchWeight_nonneg A c) (continuous_twistNotchWeight A c) hqb one_pos
    (one_le_coordBound hP _) hDr0 (fun {v} hv0 N {u} hu => by rw [one_mul]; exact hDr hv0 N hu)
  refine ⟨Kc / κ₁, div_nonneg hKc hκ₁.le, fun {v} hv0 {Av} hA ha hPD {η} hη hd {Y T} hc => ?_⟩
  rcases le_or_gt Y 0 with hY | hY
  · exact hY.trans (mul_nonneg (div_nonneg hKc hκ₁.le) hη.le)
  set a : ℕ → ℝ := fun n => v n * twistMainWeight P A c n with hadef
  set T' := max T 1 with hT'
  set B : ℝ := ∑ k ∈ Finset.range T', |rampPartial a k| with hB
  have hlow : ∀ k, -B ≤ rampPartial a k := by
    intro k
    rcases lt_or_ge k T' with hk | hk
    · have := Finset.single_le_sum (f := fun k => |rampPartial a k|) (fun k _ => abs_nonneg _)
        (Finset.mem_range.mpr hk)
      linarith [neg_abs_le (rampPartial a k)]
    · have h1 := hc k ((le_max_left T 1).trans hk)
      have hB0 : 0 ≤ B := Finset.sum_nonneg fun k _ => abs_nonneg _
      linarith
  obtain ⟨Cη, L₀, hL⟩ := h hv0 hA ha hPD hη hd hY (le_max_right T 1) hlow
    fun k hk => hc k ((le_max_left T 1).trans hk)
  have hle := le_of_log_scale_bound hL
  rw [div_mul_eq_mul_div, le_div_iff₀ hκ₁]
  linarith

/-- **The fibre law of the Weil cone at a fixed level.** For a twist polynomial `q` there is
`Y₀ ≥ 0` such that: if `lam` is full-cone Weil-positive, `d = lam − Λ` is notch-bounded at level
`η`, and the `q`-fibre partial sums `Σ_{n≤k} d(n) n^{−½} W_q(n)` stay above `Y`, then `Y ≤ Y₀ η`. -/
theorem exists_twistFibre_level_bound (hP : ∀ p ∈ P, p.Prime) (A : Finset (P → ℤ))
    (c : (P → ℤ) → ℝ) {β : P → ℕ} (hβ : ∀ a ∈ A, ∀ p, |a p| ≤ β p) :
    ∃ Y₀ : ℝ, 0 ≤ Y₀ ∧ ∀ {lam : ℕ → ℝ}, RHTower.WeilPositiveFull lam → ∀ {η : ℝ}, 0 < η →
      NotchBounded (WeilOneSided.coneDeviation lam) η → ∀ {Y : ℝ} {T : ℕ},
      (∀ k, T ≤ k → Y ≤ ∑ n ∈ Finset.range (k + 1),
        WeilOneSided.coneDeviation lam n * (Real.sqrt n)⁻¹ * twistMainWeight P A c n) →
      Y ≤ Y₀ * η := by
  obtain ⟨Y₀, hY₀, h⟩ := exists_twistFibre_level_bound_of hP A c hβ
  refine ⟨Y₀, hY₀, fun {lam} hW {η} hη hd {Y T} hc => ?_⟩
  set v := RHTower.WeilExcess.weilDeviation lam with hv
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_abs_weilDeviation_le hW
  have hv0 : v 0 = 0 := by simp [hv, RHTower.WeilExcess.weilDeviation]
  have hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ) :=
    RHTower.WeilExcess.positiveDefiniteOnReal_neg_deviationPotential hW
  have hsc : ∀ n, sqrtScaled v n = WeilOneSided.coneDeviation lam n := by
    intro n
    simp only [sqrtScaled, hv, RHTower.WeilExcess.weilDeviation, WeilOneSided.coneDeviation]
    split_ifs with h2
    · have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
      field_simp
    · simp
  have hdv : NotchBounded (sqrtScaled v) η := by
    have e : sqrtScaled v = WeilOneSided.coneDeviation lam := funext hsc
    rw [e]; exact hd
  have hterm : ∀ n, v n = WeilOneSided.coneDeviation lam n * (Real.sqrt n)⁻¹ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hv0, WeilOneSided.coneDeviation]
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    rw [← hsc, sqrtScaled]
    field_simp
  refine h hv0 hC0 hC hPD hη hdv (T := T) fun k hk => ?_
  refine (hc k hk).trans (le_of_eq (Finset.sum_congr rfl fun n _ => ?_))
  show _ = v n * twistMainWeight P A c n
  rw [hterm]

/-! ## Bounded harmonic sums -/

/-- **Bounded harmonic sums.** If `lam` is full-cone Weil-positive and `d = lam − Λ` has bounded
local mass, then the partial sums `Σ_{n<N} d(n)/n` are bounded. The harmonic windows of `d` are
`O(L^{−2})`, and the two edges of a block cost at most twice the local mass. -/
theorem exists_abs_sum_coneDeviation_div_le {lam : ℕ → ℝ} (hW : RHTower.WeilPositiveFull lam)
    {M : ℝ} (hM0 : 0 ≤ M) (hloc : LocalMassBounded (WeilOneSided.coneDeviation lam) M) :
    ∃ B : ℝ, ∀ N : ℕ, |∑ n ∈ Finset.range N, WeilOneSided.coneDeviation lam n / n| ≤ B := by
  obtain ⟨φ, Cw, L₁, hφc, hφ0, hφs, hI, hL₁, hCw0, hwin⟩ :=
    WeilOneSided.exists_profile_window_le_inv_sq
  set I := WeilOneSided.profilePrimitive φ 1 with hIdef
  set d := WeilOneSided.coneDeviation lam with hddef
  have hd0 : d 0 = 0 := by simp [hddef, WeilOneSided.coneDeviation]
  set s : ℕ → ℝ := fun N => ∑ n ∈ Finset.range N, d n / n with hs
  set X₀ : ℝ := max L₁ 1 with hX₀
  have hX₀1 : 1 ≤ X₀ := le_max_right _ _
  have hX₀ne : X₀ ≠ 0 := by positivity
  have hIne : I ≠ 0 := hI.ne'
  set N : ℕ := ⌈Real.exp X₀⌉₊ with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by
    rw [hNdef]; exact (Nat.ceil_pos.mpr (Real.exp_pos _)).ne')
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  set X := Real.log N with hX
  have hXX₀ : X₀ ≤ X := by
    rw [hX, Real.le_log_iff_exp_le hN0]; exact Nat.le_ceil _
  have hX0 : 0 < X := by linarith
  have habs : ∀ N' : ℕ, |s N'| ≤ ∑ n ∈ Finset.range N', |d n| / n := fun N' =>
    (Finset.abs_sum_le_sum_abs _ _).trans
      (le_of_eq (Finset.sum_congr rfl fun n _ => by rw [abs_div, Nat.abs_cast]))
  set H : ℝ := ∑ n ∈ Finset.range N, |d n| / n with hH
  have hCI : 0 ≤ Cw / (I * X₀) := div_nonneg hCw0 (by positivity)
  refine ⟨H + Cw / (I * X₀) + 2 * M, fun N' => ?_⟩
  rcases lt_or_ge N' N with hN' | hN'
  · have h2 : ∑ n ∈ Finset.range N', |d n| / n ≤ H :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN'.le) fun n _ _ => by positivity
    linarith [habs N']
  have hN'0 : (0 : ℝ) < N' := by exact_mod_cast (show 1 ≤ N' by omega)
  set X' := Real.log N' with hX'
  have hXX' : X ≤ X' := Real.log_le_log hN0 (by exact_mod_cast hN')
  have hL₁X : L₁ ≤ X := (le_max_left _ _).trans hXX₀
  set N₁ := ⌈Real.exp (X' + 1)⌉₊ with hN₁
  have hN'N₁ : N' ≤ N₁ := by
    have : (N' : ℝ) ≤ Real.exp (X' + 1) := by
      rw [Real.exp_add, hX', Real.exp_log hN'0]
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    exact_mod_cast this.trans (Nat.le_ceil _)
  have hblock : I * (s N' - s N) =
      (∑ n ∈ Finset.range N₁, d n / n * (WeilOneSided.profilePrimitive φ (Real.log n - X) -
          WeilOneSided.profilePrimitive φ (Real.log n - X'))) +
        ∑ n ∈ Finset.range N₁, d n / n * WeilOneSided.profileEdge φ (Real.log n - X) -
          ∑ n ∈ Finset.range N₁, d n / n * WeilOneSided.profileEdge φ (Real.log n - X') := by
    have hsN : s N' - s N = ∑ n ∈ Finset.range N₁, d n / n * (if N ≤ n ∧ n < N' then 1 else 0) := by
      rw [hs]
      simp only
      rw [← Finset.sum_Ico_eq_sub _ hN']
      simp only [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext n
      simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩
      · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    rw [hsN, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hd0]; simp
    rw [mul_left_comm, WeilOneSided.indicator_block_eq hN1 hN' hn]
    ring
  have hint : |∑ n ∈ Finset.range N₁, d n / n * (WeilOneSided.profilePrimitive φ (Real.log n - X) -
      WeilOneSided.profilePrimitive φ (Real.log n - X'))| ≤ Cw / X := by
    rw [← WeilOneSided.integral_windowSum_eq hφc d N₁ X X']
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hXX'
      (g := fun L => Cw * (L ^ 2)⁻¹) (Eventually.of_forall fun L hL => by
        rw [Real.norm_eq_abs]
        refine hwin lam hW L (hL₁X.trans hL.1.le) N₁ ?_
        refine le_trans (Real.exp_le_exp.mpr (by linarith [hL.2])) (Nat.le_ceil _))
      (ContinuousOn.intervalIntegrable (continuousOn_const.mul (ContinuousOn.inv₀
        (continuousOn_pow 2) fun L hL => by
          rw [Set.uIcc_of_le hXX'] at hL
          exact pow_ne_zero 2 (by linarith [hL.1]))))
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (WeilOneSided.integral_const_div_sq_le hCw0 hX0 hXX')
  have hedge : ∀ Z, 1 ≤ Z →
      |∑ n ∈ Finset.range N₁, d n / n * WeilOneSided.profileEdge φ (Real.log n - Z)| ≤ I * M := by
    intro Z hZ
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ Finset.range N₁, |d n / n * WeilOneSided.profileEdge φ (Real.log n - Z)|
        ≤ ∑ n ∈ Finset.range N₁,
            I * (|d n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0)) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [abs_mul, abs_div, Nat.abs_cast]
          have h := WeilOneSided.abs_profileEdge_le hφc hφ0 hφs (Real.log n - Z)
          calc |d n| / n * |WeilOneSided.profileEdge φ (Real.log n - Z)|
              ≤ |d n| / n * (I * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0)) :=
                mul_le_mul_of_nonneg_left h (by positivity)
            _ = _ := by ring
      _ = I * ∑ n ∈ Finset.range N₁, |d n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) := by
          rw [Finset.mul_sum]
      _ ≤ I * M := mul_le_mul_of_nonneg_left (hloc Z hZ N₁) hI.le
  have he1 := hedge X (by linarith)
  have he2 := hedge X' (by linarith)
  have htot : I * |s N' - s N| ≤ Cw / X + I * M + I * M := by
    rw [← abs_of_pos hI, ← abs_mul, abs_of_pos hI, hblock]
    have := abs_add_three (∑ n ∈ Finset.range N₁, d n / n *
      (WeilOneSided.profilePrimitive φ (Real.log n - X) -
        WeilOneSided.profilePrimitive φ (Real.log n - X')))
      (∑ n ∈ Finset.range N₁, d n / n * WeilOneSided.profileEdge φ (Real.log n - X))
      (-∑ n ∈ Finset.range N₁, d n / n * WeilOneSided.profileEdge φ (Real.log n - X'))
    rw [abs_neg, ← sub_eq_add_neg] at this
    linarith
  have hCX : Cw / X ≤ I * (Cw / (I * X₀)) := by
    have e : I * (Cw / (I * X₀)) = Cw / X₀ := by field_simp
    rw [e]
    exact div_le_div_of_nonneg_left hCw0 (by linarith) hXX₀
  have hdiff : |s N' - s N| ≤ Cw / (I * X₀) + 2 * M := by
    have : I * |s N' - s N| ≤ I * (Cw / (I * X₀) + 2 * M) := by rw [mul_add]; linarith
    exact le_of_mul_le_mul_left this hI
  have h3 := abs_sub_abs_le_abs_sub (s N') (s N)
  have h4 : |s N| ≤ H := habs N
  linarith

/-! ## The twist `|1 + ε p^{it}|²` -/

/-- The singleton prime set `{p}`. -/
def primeSingleton (p : ℕ) : Finset ℕ := {p}

theorem prime_of_mem_primeSingleton {p : ℕ} (hp : p.Prime) : ∀ q ∈ primeSingleton p, q.Prime := by
  intro q hq
  rw [primeSingleton, Finset.mem_singleton] at hq
  exact hq ▸ hp

/-- The point `p` of `primeSingleton p`. -/
def primePt (p : ℕ) : primeSingleton p := ⟨p, Finset.mem_singleton_self p⟩

theorem eq_primePt {p : ℕ} (x : primeSingleton p) : x = primePt p :=
  Subtype.ext (Finset.mem_singleton.mp x.2)

theorem prod_primeSingleton {p : ℕ} {M : Type*} [CommMonoid M] (f : primeSingleton p → M) :
    ∏ x, f x = f (primePt p) :=
  Fintype.prod_eq_single (primePt p) fun x hx => absurd (eq_primePt x) hx

/-- The unit exponent vector of `primeSingleton p`. -/
def primeUnit (p : ℕ) : primeSingleton p → ℤ := fun _ => 1

theorem primeUnit_ne_zero (p : ℕ) : (0 : primeSingleton p → ℤ) ≠ primeUnit p := by
  intro h
  have := congrFun h (primePt p)
  simp [primeUnit] at this

theorem twistNorm_primeSingleton {p n : ℕ} (g : primeSingleton p → ℤ) :
    twistNorm (primeSingleton p) n g = (p : ℝ) ^ (((n.factorization p : ℕ) : ℤ) - g (primePt p)).natAbs *
      roughPart (primeSingleton p) n := by
  unfold twistNorm vecNum vecDen vecOf
  rw [prod_primeSingleton, prod_primeSingleton]
  have hp : ((primePt p : primeSingleton p) : ℕ) = p := rfl
  simp only [Pi.sub_apply, hp]
  push_cast
  rw [mul_comm ((p : ℝ) ^ _ * _) _, ← mul_assoc, ← pow_add, add_comm,
    Int.toNat_add_toNat_neg_eq_natAbs, mul_comm]

theorem smoothPart_primeSingleton (p n : ℕ) : smoothPart (primeSingleton p) n = p ^ n.factorization p := by
  unfold smoothPart
  rw [prod_primeSingleton]
  rfl

/-- The coefficients `c_0 = 1`, `c_u = ε` of the twist `|1 + ε p^{it}|²`. -/
def primePairCoeff (p : ℕ) (ε : ℝ) : (primeSingleton p → ℤ) → ℝ := fun a => if a = 0 then 1 else ε

/-- The main weight of `|1 + ε p^{it}|²`, times `√n`: `1 + ε² + 2ε/√p`, plus `ε(√p − 1/√p)` on the
multiples of `p`. -/
def primeTwistWeight (p : ℕ) (ε : ℝ) (n : ℕ) : ℝ :=
  1 + ε ^ 2 + 2 * ε * (Real.sqrt p)⁻¹ +
    (if p ∣ n then ε * (Real.sqrt p - (Real.sqrt p)⁻¹) else 0)

theorem twistMainWeight_primeSingleton {p : ℕ} (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) (ε : ℝ) :
    twistMainWeight (primeSingleton p) {0, primeUnit p} (primePairCoeff p ε) n =
      primeTwistWeight p ε n * (Real.sqrt n)⁻¹ := by
  unfold twistMainWeight
  rw [Finset.sum_pair (primeUnit_ne_zero p), Finset.sum_pair (primeUnit_ne_zero p),
    Finset.sum_pair (primeUnit_ne_zero p)]
  have hc0 : primePairCoeff p ε 0 = 1 := if_pos rfl
  have hcu : primePairCoeff p ε (primeUnit p) = ε := if_neg (primeUnit_ne_zero p).symm
  rw [hc0, hcu]
  simp only [mul_one, one_mul, sub_self, zero_sub, sub_zero]
  have hnr' := smoothPart_mul_roughPart (P := primeSingleton p) n hn
  rw [smoothPart_primeSingleton] at hnr'
  have hnr : (n : ℝ) = (p : ℝ) ^ n.factorization p * (roughPart (primeSingleton p) n : ℝ) := by
    exact_mod_cast hnr'.symm
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have t0 : twistNorm (primeSingleton p) n 0 = n := by
    rw [twistNorm_primeSingleton, hnr]
    simp
  have tm : twistNorm (primeSingleton p) n (-primeUnit p) = p * n := by
    rw [twistNorm_primeSingleton, hnr]
    simp only [Pi.neg_apply, primeUnit, sub_neg_eq_add]
    rw [show (((n.factorization p : ℕ) : ℤ) + 1).natAbs = n.factorization p + 1 by omega,
      pow_succ]
    ring
  have e0 : (Real.sqrt (twistNorm (primeSingleton p) n 0))⁻¹ = (Real.sqrt n)⁻¹ := by rw [t0]
  have em : (Real.sqrt (twistNorm (primeSingleton p) n (-primeUnit p)))⁻¹ =
      (Real.sqrt p)⁻¹ * (Real.sqrt n)⁻¹ := by
    rw [tm, Real.sqrt_mul hp0.le, mul_inv]
  unfold primeTwistWeight
  by_cases hpn : p ∣ n
  · have hv1 : 1 ≤ n.factorization p := (hp.dvd_iff_one_le_factorization hn).mp hpn
    have tp : twistNorm (primeSingleton p) n (primeUnit p) = n / p := by
      rw [twistNorm_primeSingleton, hnr]
      simp only [primeUnit]
      rw [show (((n.factorization p : ℕ) : ℤ) - 1).natAbs = n.factorization p - 1 by omega]
      have : (p : ℝ) ^ n.factorization p = (p : ℝ) ^ (n.factorization p - 1) * p := by
        rw [← pow_succ, Nat.sub_add_cancel hv1]
      rw [this]
      field_simp
    have ep : (Real.sqrt (twistNorm (primeSingleton p) n (primeUnit p)))⁻¹ =
        Real.sqrt p * (Real.sqrt n)⁻¹ := by
      rw [tp, Real.sqrt_div' _ hp0.le, inv_div, div_eq_mul_inv]
    rw [if_pos hpn, e0, em, ep]
    ring
  · have hv0 : n.factorization p = 0 :=
      (Nat.factorization_eq_zero_iff n p).mpr (Or.inr (Or.inl hpn))
    have tp : twistNorm (primeSingleton p) n (primeUnit p) = p * n := by
      rw [twistNorm_primeSingleton, hnr, hv0]
      simp [primeUnit]
    have ep : (Real.sqrt (twistNorm (primeSingleton p) n (primeUnit p)))⁻¹ =
        (Real.sqrt p)⁻¹ * (Real.sqrt n)⁻¹ := by
      rw [tp, Real.sqrt_mul hp0.le, mul_inv]
    rw [if_neg hpn, e0, em, ep]
    ring

/-! ## The multiples-of-a-prime law -/

/-- `G_p(k) = Σ_{n≤k, p∣n} d(n)/n`. -/
def multiplesSum (p : ℕ) (d : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (k + 1), if p ∣ n then d n / n else 0

/-- **The `|1 + ε p^{it}|²`-fibre sum** is
`(1 + ε² + 2ε/√p) Σ_{n≤k} d(n)/n + ε(√p − 1/√p) G_p(k)`. -/
theorem sum_primeTwist_eq {p : ℕ} (hp : p.Prime) {d : ℕ → ℝ} (hd0 : d 0 = 0) (ε : ℝ) (k : ℕ) :
    ∑ n ∈ Finset.range (k + 1), d n * (Real.sqrt n)⁻¹ *
        twistMainWeight (primeSingleton p) {0, primeUnit p} (primePairCoeff p ε) n =
      (1 + ε ^ 2 + 2 * ε * (Real.sqrt p)⁻¹) * ∑ n ∈ Finset.range (k + 1), d n / n +
        ε * (Real.sqrt p - (Real.sqrt p)⁻¹) * multiplesSum p d k := by
  unfold multiplesSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hd0]
  rw [twistMainWeight_primeSingleton hp hn.ne' ε, primeTwistWeight]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsq : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = (n : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hn0.le]
  split_ifs with h
  · rw [div_eq_mul_inv, ← hsq]; ring
  · rw [div_eq_mul_inv, ← hsq]; ring

/-- If `ε G_p(k) → +∞` for `ε = ±1`, the `|1 + ε p^{it}|²`-fibre sums exceed every level. -/
theorem false_of_tendsto_mul_multiplesSum {lam : ℕ → ℝ} (hW : RHTower.WeilPositiveFull lam)
    {M : ℝ} (hM0 : 0 ≤ M) (hloc : LocalMassBounded (WeilOneSided.coneDeviation lam) M)
    {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hG : Tendsto (fun k => ε * multiplesSum p (WeilOneSided.coneDeviation lam) k) atTop atTop) :
    False := by
  set d := WeilOneSided.coneDeviation lam with hddef
  have hd0 : d 0 = 0 := by simp [hddef, WeilOneSided.coneDeviation]
  have hβ : ∀ a ∈ ({0, primeUnit p} : Finset (primeSingleton p → ℤ)), ∀ x,
      |a x| ≤ (fun _ => 1 : primeSingleton p → ℕ) x := by
    intro a ha x
    rcases Finset.mem_insert.mp ha with rfl | ha
    · simp
    · rw [Finset.mem_singleton.mp ha]; simp [primeUnit]
  obtain ⟨Y₀, hY₀, hlev⟩ :=
    exists_twistFibre_level_bound (prime_of_mem_primeSingleton hp) {0, primeUnit p} (primePairCoeff p ε) hβ
  obtain ⟨B, hB⟩ := exists_abs_sum_coneDeviation_div_le hW hM0 hloc
  have hnb : NotchBounded d (5 * M + 1) := (notchBounded_of_localMassBounded hd0
    (by simp [hddef, WeilOneSided.coneDeviation]) hM0 hloc).mono_level (by linarith)
  have hp1 : (1 : ℝ) < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by exact_mod_cast hp.one_lt)
  have hinv : (Real.sqrt p)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hinv0 : 0 < (Real.sqrt p)⁻¹ := inv_pos.mpr (by linarith)
  set Q₀ : ℝ := 1 + ε ^ 2 + 2 * ε * (Real.sqrt p)⁻¹ with hQ₀
  have hQ₀0 : 0 < Q₀ := by
    rcases hε with rfl | rfl
    · rw [hQ₀]; nlinarith
    · rw [hQ₀]; nlinarith
  set D : ℝ := Real.sqrt p - (Real.sqrt p)⁻¹ with hD
  have hD0 : 0 < D := by rw [hD]; linarith
  have hDne : D ≠ 0 := hD0.ne'
  set η : ℝ := 5 * M + 1 with hη
  set Y : ℝ := Y₀ * η + 1 with hY
  obtain ⟨T, hT⟩ := eventually_atTop.mp (hG.eventually_ge_atTop ((Y + Q₀ * B) / D))
  have hc : ∀ k, T ≤ k → Y ≤ ∑ n ∈ Finset.range (k + 1),
      d n * (Real.sqrt n)⁻¹ * twistMainWeight (primeSingleton p) {0, primeUnit p} (primePairCoeff p ε) n := by
    intro k hk
    rw [sum_primeTwist_eq hp hd0 ε k, ← hQ₀, ← hD]
    have h1 := hT k hk
    have h2 := abs_le.mp (hB (k + 1))
    have h3 : D * ((Y + Q₀ * B) / D) = Y + Q₀ * B := by field_simp
    have h4 : D * ((Y + Q₀ * B) / D) ≤ D * (ε * multiplesSum p d k) :=
      mul_le_mul_of_nonneg_left h1 hD0.le
    have h5 : Q₀ * (-B) ≤ Q₀ * ∑ n ∈ Finset.range (k + 1), d n / n :=
      mul_le_mul_of_nonneg_left h2.1 hQ₀0.le
    linarith
  have := hlev hW (η := η) (by rw [hη]; linarith) hnb hc
  linarith

/-- **The multiples-of-a-prime law, upper side, local-mass form.** If `lam` is full-cone
Weil-positive and `d = lam − Λ` has bounded local mass, then `Σ_{n≤k, p∣n} d(n)/n` does not tend
to `+∞`. -/
theorem not_tendsto_atTop_multiplesSum_of_localMass {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam) {M : ℝ} (hM0 : 0 ≤ M)
    (hloc : LocalMassBounded (WeilOneSided.coneDeviation lam) M) {p : ℕ} (hp : p.Prime) :
    ¬ Tendsto (multiplesSum p (WeilOneSided.coneDeviation lam)) atTop atTop := fun hG =>
  false_of_tendsto_mul_multiplesSum hW hM0 hloc hp (Or.inl rfl)
    (hG.congr fun _ => (one_mul _).symm)

/-- **The multiples-of-a-prime law, lower side, local-mass form.** -/
theorem not_tendsto_atBot_multiplesSum_of_localMass {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam) {M : ℝ} (hM0 : 0 ≤ M)
    (hloc : LocalMassBounded (WeilOneSided.coneDeviation lam) M) {p : ℕ} (hp : p.Prime) :
    ¬ Tendsto (multiplesSum p (WeilOneSided.coneDeviation lam)) atTop atBot := fun hG =>
  false_of_tendsto_mul_multiplesSum hW hM0 hloc hp (Or.inr rfl)
    ((tendsto_neg_atBot_atTop.comp hG).congr fun _ => (neg_one_mul _).symm)

theorem localMassBounded_coneDeviation_of_abs_le {lam : ℕ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ n, |WeilOneSided.coneDeviation lam n| ≤ C * (1 + ArithmeticFunction.vonMangoldt n)) :
    0 ≤ C * ((2 * Real.log 4 + 18) * Real.exp (1 / 2)) ∧
      LocalMassBounded (WeilOneSided.coneDeviation lam)
        (C * ((2 * Real.log 4 + 18) * Real.exp (1 / 2))) :=
  ⟨by have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num); positivity,
    localMassBounded_of_abs_le hC hd⟩

/-- **The multiples-of-a-prime law, upper side.** If `lam` is full-cone Weil-positive with
`|lam − Λ| ≤ C (1 + Λ)`, then `Σ_{n≤k, p∣n} (lam(n) − Λ(n))/n` does not tend to `+∞`. -/
theorem not_tendsto_atTop_multiplesSum {lam : ℕ → ℝ} (hW : RHTower.WeilPositiveFull lam)
    {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ n, |WeilOneSided.coneDeviation lam n| ≤ C * (1 + ArithmeticFunction.vonMangoldt n))
    {p : ℕ} (hp : p.Prime) :
    ¬ Tendsto (multiplesSum p (WeilOneSided.coneDeviation lam)) atTop atTop :=
  not_tendsto_atTop_multiplesSum_of_localMass hW (localMassBounded_coneDeviation_of_abs_le hC hd).1
    (localMassBounded_coneDeviation_of_abs_le hC hd).2 hp

/-- **The multiples-of-a-prime law, lower side.** If `lam` is full-cone Weil-positive with
`|lam − Λ| ≤ C (1 + Λ)`, then `Σ_{n≤k, p∣n} (lam(n) − Λ(n))/n` does not tend to `−∞`. -/
theorem not_tendsto_atBot_multiplesSum {lam : ℕ → ℝ} (hW : RHTower.WeilPositiveFull lam)
    {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ n, |WeilOneSided.coneDeviation lam n| ≤ C * (1 + ArithmeticFunction.vonMangoldt n))
    {p : ℕ} (hp : p.Prime) :
    ¬ Tendsto (multiplesSum p (WeilOneSided.coneDeviation lam)) atTop atBot :=
  not_tendsto_atBot_multiplesSum_of_localMass hW (localMassBounded_coneDeviation_of_abs_le hC hd).1
    (localMassBounded_coneDeviation_of_abs_le hC hd).2 hp

/-! ## Finite harmonic mass on the multiples of a prime -/

/-- `Σ_{n≤k, p∣n} Λ(n)/n ≤ log p`: only the powers of `p` contribute. -/
theorem sum_multiples_vonMangoldt_div_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ∑ n ∈ Finset.range (k + 1),
        (if p ∣ n then (ArithmeticFunction.vonMangoldt n : ℝ) / n else 0) ≤ Real.log p := by
  classical
  have hp2 : 2 ≤ p := hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set S := (Finset.range (k + 1)).filter (fun n => p ∣ n ∧ IsPrimePow n) with hS
  have hsplit : ∑ n ∈ Finset.range (k + 1),
      (if p ∣ n then (ArithmeticFunction.vonMangoldt n : ℝ) / n else 0) =
        ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases h1 : p ∣ n
    · by_cases h2 : IsPrimePow n
      · rw [if_pos h1, if_pos ⟨h1, h2⟩]
      · rw [if_pos h1, if_neg (fun h => h2 h.2), ArithmeticFunction.vonMangoldt_apply,
          if_neg h2]; simp
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
  have himg : S ⊆ (Finset.range (k + 1)).image (fun j => p ^ (j + 1)) := by
    intro n hn
    rw [hS, Finset.mem_filter] at hn
    obtain ⟨hnk, hpn, hpp⟩ := hn
    obtain ⟨q, j, hq, hj, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    have hpq : p = q := (Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hpn)
    subst hpq
    refine Finset.mem_image.mpr ⟨j - 1, Finset.mem_range.mpr ?_, ?_⟩
    swap
    · show _ ^ (j - 1 + 1) = _ ^ j
      rw [Nat.sub_add_cancel hj]
    have hjlt : j < p ^ j := Nat.lt_pow_self hp.one_lt
    have := Finset.mem_range.mp hnk
    omega
  have hterm : ∀ j : ℕ, (ArithmeticFunction.vonMangoldt (p ^ (j + 1)) : ℝ) / (p ^ (j + 1) : ℕ) =
      Real.log p * (1 / (p : ℝ)) ^ (j + 1) := by
    intro j
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp]
    push_cast
    rw [one_div, inv_pow, div_eq_mul_inv]
  have hinj : Set.InjOn (fun j => p ^ (j + 1)) (Finset.range (k + 1) : Set ℕ) := fun a _ b _ h =>
    by
      have := Nat.pow_right_injective hp2 h
      omega
  rw [hsplit]
  calc ∑ n ∈ S, (ArithmeticFunction.vonMangoldt n : ℝ) / n
      ≤ ∑ n ∈ (Finset.range (k + 1)).image (fun j => p ^ (j + 1)),
          (ArithmeticFunction.vonMangoldt n : ℝ) / n :=
        Finset.sum_le_sum_of_subset_of_nonneg himg fun n _ _ => by
          have := ArithmeticFunction.vonMangoldt_nonneg (n := n); positivity
    _ = ∑ j ∈ Finset.range (k + 1), Real.log p * (1 / (p : ℝ)) ^ (j + 1) := by
        rw [Finset.sum_image hinj]
        exact Finset.sum_congr rfl fun j _ => hterm j
    _ ≤ ∑ j ∈ Finset.range (k + 1), Real.log p * ((1 / (2 : ℝ)) ^ j * (1 / 2)) := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (Real.log_nonneg
          (by exact_mod_cast hp.one_lt.le))
        rw [← pow_succ]
        exact pow_le_pow_left₀ (by positivity)
          (one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp2)) _
    _ = Real.log p * ((∑ j ∈ Finset.range (k + 1), (1 / (2 : ℝ)) ^ j) * (1 / 2)) := by
        rw [Finset.sum_mul, Finset.mul_sum]
    _ ≤ Real.log p * (2 * (1 / 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
        exact mul_le_mul_of_nonneg_right (sum_geometric_two_le _) (by norm_num)
    _ = Real.log p := by ring

theorem multiples_term_nonneg {lam : ℕ → ℝ} {p : ℕ} (hnn : ∀ n, p ∣ n → p < n → 0 ≤ lam n)
    (n : ℕ) : 0 ≤ (if p ∣ n ∧ n ≠ p then lam n / n else 0) := by
  split_ifs with h
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact div_nonneg (hnn n h.1 (lt_of_le_of_ne (Nat.le_of_dvd hn h.1) (Ne.symm h.2)))
        (Nat.cast_nonneg n)
  · exact le_rfl

/-- **Finite harmonic mass on the multiples of a prime, local-mass form.** If `lam` is full-cone
Weil-positive, `d = lam − Λ` has bounded local mass and `lam ≥ 0` on the multiples of a prime `p`
other than `p`, then `Σ_{p∣n, n≠p} lam(n)/n < ∞`. -/
theorem summable_multiples_of_localMass {lam : ℕ → ℝ} (hW : RHTower.WeilPositiveFull lam)
    {M : ℝ} (hM0 : 0 ≤ M) (hloc : LocalMassBounded (WeilOneSided.coneDeviation lam) M)
    {p : ℕ} (hp : p.Prime) (hnn : ∀ n, p ∣ n → p < n → 0 ≤ lam n) :
    Summable fun n : ℕ => if p ∣ n ∧ n ≠ p then lam n / n else 0 := by
  classical
  set f : ℕ → ℝ := fun n => if p ∣ n ∧ n ≠ p then lam n / n else 0 with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => multiples_term_nonneg hnn n
  set d := WeilOneSided.coneDeviation lam with hddef
  have hLpb : ∀ k, ∑ n ∈ Finset.range (k + 1),
      (if p ∣ n then (ArithmeticFunction.vonMangoldt n : ℝ) / n else 0) ≤ Real.log p :=
    sum_multiples_vonMangoldt_div_le hp
  have hdp : -(|d p| / p) ≤ d p / p := by
    have h3 := neg_abs_le (d p / p); rwa [abs_div, Nat.abs_cast] at h3
  have hΛp : 0 ≤ (ArithmeticFunction.vonMangoldt p : ℝ) / p := by
    have := ArithmeticFunction.vonMangoldt_nonneg (n := p); positivity
  have hdp0 : 0 ≤ |d p| / p := by positivity
  -- `G_p(k) ≥ Σ_{n≤k} f(n) − log p − |d(p)|/p`
  have hG : ∀ k, ∑ n ∈ Finset.range (k + 1), f n - Real.log p - |d p| / p ≤
      multiplesSum p d k := by
    intro k
    have hterm : ∀ n, f n - (if p ∣ n then (ArithmeticFunction.vonMangoldt n : ℝ) / n else 0) -
        (if n = p then |d p| / p else 0) ≤ (if p ∣ n then d n / n else 0) := by
      intro n
      have hdn : p ∣ n → d n / n = lam n / n - (ArithmeticFunction.vonMangoldt n : ℝ) / n := by
        intro h1
        have hn1 : n ≠ 1 := fun h => hp.one_lt.ne' (Nat.dvd_one.mp (h ▸ h1))
        rcases Nat.lt_or_ge n 2 with h2 | h2
        · interval_cases n
          · simp [hddef, WeilOneSided.coneDeviation]
          · exact absurd rfl hn1
        · simp only [hddef, WeilOneSided.coneDeviation, if_pos h2]; ring
      simp only [hf]
      split_ifs <;> first
        | linarith
        | (exfalso; tauto)
        | (rw [‹n = p›]; linarith)
        | (have := hdn ‹p ∣ n›; linarith)
    have hsum := Finset.sum_le_sum fun n (_ : n ∈ Finset.range (k + 1)) => hterm n
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hsum
    have hpk : ∑ n ∈ Finset.range (k + 1), (if n = p then |d p| / p else 0) ≤ |d p| / p := by
      rw [Finset.sum_ite_eq']
      split_ifs
      · exact le_rfl
      · exact hdp0
    unfold multiplesSum
    have := hLpb k
    linarith
  -- bounded partial sums
  by_contra hns
  have hunb : ∀ c : ℝ, ∃ m, c < ∑ n ∈ Finset.range m, f n := by
    intro c
    by_contra h
    push Not at h
    exact hns (summable_of_sum_range_le hf0 h)
  refine not_tendsto_atTop_multiplesSum_of_localMass hW hM0 hloc hp
    (tendsto_atTop.mpr fun c => ?_)
  obtain ⟨m, hm⟩ := hunb (c + Real.log p + |d p| / p)
  refine eventually_atTop.mpr ⟨m, fun k hk => ?_⟩
  have hmono : ∑ n ∈ Finset.range m, f n ≤ ∑ n ∈ Finset.range (k + 1), f n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega)) fun n _ _ => hf0 n
  have := hG k
  linarith

/-- A semiprime floor `lam(pq) ≥ c > 0` has divergent harmonic mass on `pℕ`. -/
theorem not_summable_multiples_of_semiprime_floor {lam : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    {p : ℕ} (hp : p.Prime) (hnn : ∀ n, p ∣ n → p < n → 0 ≤ lam n)
    (hfloor : ∀ q, q.Prime → q ≠ p → c ≤ lam (p * q)) :
    ¬ Summable fun n : ℕ => if p ∣ n ∧ n ≠ p then lam n / n else 0 := by
  intro hs
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs2 := hs.comp_injective (mul_right_injective₀ hp.ne_zero)
  have hcmp : ∀ q : ℕ, ({q : ℕ | q.Prime}.indicator (fun n : ℕ => (1 : ℝ) / n)) q ≤
      p / c * (if p ∣ p * q ∧ p * q ≠ p then lam (p * q) / ((p * q : ℕ) : ℝ) else 0) +
        (if q = p then 1 / (p : ℝ) else 0) := by
    intro q
    by_cases hq : q.Prime
    · rw [Set.indicator_of_mem (show q ∈ {q : ℕ | q.Prime} from hq)]
      show (1 : ℝ) / q ≤ _
      have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
      have hpq1 : p * q ≠ p := fun h => hq.one_lt.ne' (by
        have := Nat.eq_of_mul_eq_mul_left hp.pos (h.trans (mul_one p).symm); exact this)
      rw [if_pos ⟨dvd_mul_right p q, hpq1⟩]
      have hfirst : 0 ≤ p / c * (lam (p * q) / ((p * q : ℕ) : ℝ)) :=
        mul_nonneg (by positivity) (div_nonneg
          (hnn _ (dvd_mul_right p q) (lt_mul_of_one_lt_right hp.pos hq.one_lt)) (Nat.cast_nonneg _))
      by_cases hqp : q = p
      · rw [if_pos hqp]
        have e : (1 : ℝ) / q = 1 / p := by rw [hqp]
        linarith
      · rw [if_neg hqp, add_zero]
        have hfl := hfloor q hq hqp
        have hpne : (p : ℝ) ≠ 0 := hp0.ne'
        have hqne : (q : ℝ) ≠ 0 := hq0.ne'
        have hcne : c ≠ 0 := hc.ne'
        have e : (1 : ℝ) / q = p / c * (c / ((p * q : ℕ) : ℝ)) := by
          push_cast; field_simp
        rw [e]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact div_le_div_of_nonneg_right hfl (Nat.cast_nonneg _)
    · rw [Set.indicator_of_notMem (show q ∉ {q : ℕ | q.Prime} from hq)]
      have h1 : 0 ≤ (if p ∣ p * q ∧ p * q ≠ p then lam (p * q) / ((p * q : ℕ) : ℝ) else 0) :=
        multiples_term_nonneg hnn (p * q)
      have h2 : 0 ≤ (if q = p then 1 / (p : ℝ) else 0) := by split_ifs <;> positivity
      have := mul_nonneg (by positivity : (0 : ℝ) ≤ p / c) h1
      linarith
  have hsum : Summable ({q : ℕ | q.Prime}.indicator (fun n : ℕ => (1 : ℝ) / n)) :=
    Summable.of_nonneg_of_le (fun q => Set.indicator_nonneg (fun n _ => by positivity) q) hcmp
      ((hs2.mul_left (p / c)).add (hasSum_ite_eq p (1 / (p : ℝ))).summable)
  exact not_summable_one_div_on_primes hsum

/-- **Finite harmonic mass on the multiples of a prime.** If `lam` is full-cone Weil-positive with
`|lam − Λ| ≤ C (1 + Λ)` and `lam ≥ 0` on the multiples of a prime `p` other than `p`, then
`Σ_{p∣n, n≠p} lam(n)/n < ∞`. -/
theorem summable_multiples_of_nonneg {lam : ℕ → ℝ} (hW : RHTower.WeilPositiveFull lam)
    {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ n, |WeilOneSided.coneDeviation lam n| ≤ C * (1 + ArithmeticFunction.vonMangoldt n))
    {p : ℕ} (hp : p.Prime) (hnn : ∀ n, p ∣ n → p < n → 0 ≤ lam n) :
    Summable fun n : ℕ => if p ∣ n ∧ n ≠ p then lam n / n else 0 :=
  summable_multiples_of_localMass hW (localMassBounded_coneDeviation_of_abs_le hC hd).1
    (localMassBounded_coneDeviation_of_abs_le hC hd).2 hp hnn

/-- **Semiprime floors are not Weil-positive.** No full-cone Weil-positive `lam` with
`|lam − Λ| ≤ C (1 + Λ)`, `lam ≥ 0` on the multiples of `p` other than `p`, has a floor
`lam(pq) ≥ c > 0` on the semiprimes `pq`, `q ≠ p` prime. -/
theorem not_weilPositiveFull_of_semiprime_floor {lam : ℕ → ℝ} {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hd : ∀ n, |WeilOneSided.coneDeviation lam n| ≤ C * (1 + ArithmeticFunction.vonMangoldt n))
    {p : ℕ} (hp : p.Prime) (hnn : ∀ n, p ∣ n → p < n → 0 ≤ lam n)
    (hfloor : ∀ q, q.Prime → q ≠ p → c ≤ lam (p * q)) : ¬ RHTower.WeilPositiveFull lam :=
  fun hW => not_summable_multiples_of_semiprime_floor hc hp hnn hfloor
    (summable_multiples_of_nonneg hW hC hd hp hnn)

/-! ## The nonnegative Weil cone -/

/-- **The multiples-of-a-prime law of the nonnegative Weil cone.** If `lam ≥ 0` is full-cone
Weil-positive, then for every prime `p` the sums `Σ_{n≤k, p∣n} (lam(n) − Λ(n))/n` tend neither to
`+∞` nor to `−∞`. No size condition is placed on `lam`. -/
theorem not_tendsto_multiplesSum_of_nonneg {lam : ℕ → ℝ} (hW : RHTower.WeilPositiveFull lam)
    (hnn : ∀ n, 2 ≤ n → 0 ≤ lam n) {p : ℕ} (hp : p.Prime) :
    ¬ Tendsto (multiplesSum p (WeilOneSided.coneDeviation lam)) atTop atTop ∧
      ¬ Tendsto (multiplesSum p (WeilOneSided.coneDeviation lam)) atTop atBot := by
  obtain ⟨M, hM0, hloc⟩ := exists_localMassBounded_of_nonneg hW hnn
  exact ⟨not_tendsto_atTop_multiplesSum_of_localMass hW hM0 hloc hp,
    not_tendsto_atBot_multiplesSum_of_localMass hW hM0 hloc hp⟩

/-- **Nonnegative Weil-positive weights have finite harmonic mass on every `pℕ`.** If `lam ≥ 0` is
full-cone Weil-positive, then `Σ_{p∣n, n≠p} lam(n)/n < ∞` for every prime `p`. -/
theorem summable_multiples_of_weilPositiveFull_of_nonneg {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam) (hnn : ∀ n, 2 ≤ n → 0 ≤ lam n) {p : ℕ} (hp : p.Prime) :
    Summable fun n : ℕ => if p ∣ n ∧ n ≠ p then lam n / n else 0 := by
  obtain ⟨M, hM0, hloc⟩ := exists_localMassBounded_of_nonneg hW hnn
  exact summable_multiples_of_localMass hW hM0 hloc hp fun n _ hpn =>
    hnn n (by have := hp.two_le; omega)

/-- **No nonnegative Weil-positive weight system has a semiprime floor.** If `lam ≥ 0` and
`lam(pq) ≥ c > 0` for a prime `p` and all primes `q ≠ p`, then `lam` is not Weil-positive. -/
theorem not_weilPositiveFull_of_nonneg_semiprime_floor {lam : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hnn : ∀ n, 2 ≤ n → 0 ≤ lam n) {p : ℕ} (hp : p.Prime)
    (hfloor : ∀ q, q.Prime → q ≠ p → c ≤ lam (p * q)) : ¬ RHTower.WeilPositiveFull lam := by
  intro hW
  have hnn' : ∀ n, p ∣ n → p < n → 0 ≤ lam n := fun n _ hpn =>
    hnn n (by have := hp.two_le; omega)
  exact not_summable_multiples_of_semiprime_floor hc hp hnn' hfloor
    (summable_multiples_of_weilPositiveFull_of_nonneg hW hnn hp)

end RHTower.WeilAbscissa
