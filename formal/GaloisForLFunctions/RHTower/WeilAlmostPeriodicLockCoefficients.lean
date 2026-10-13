import GaloisForLFunctions.RHTower.WeilBoundedDenominatorLockPeriodicity
import GaloisForLFunctions.RHTower.LimitPeriodicExpSingleCharacter
import GaloisForLFunctions.HTGeometry.HurwitzZetaEulerMaclaurinBridge

/-!
# Almost-periodic locks force almost-periodic Dirichlet coefficients

**Theorem** (`apLock_coefficients`). Let `G` be a Herglotz producer for the weights `lam`, with
Dirichlet coefficients `a = exp⋆(lam/log)` and lower-line lock

`G(1 − s) = V(s) G(s)`,   `V(s) = Σ_j c_j u_j^{−(s−½)}`,

with `u_j > 0` and `Σ_j |c_j| max(1, u_j^{−1}) < ∞`.

The frequencies `u_j` are arbitrary positive reals. Then for every `n ≥ 1`

`a(n) = Σ_{(m,j) : 0 < m u_j ≤ 1} a(m) c_j √u_j e(n m u_j)`,   `e(x) = e^{2πix}`.

So `a` is an absolutely convergent almost-periodic sequence whose frequencies are the points
`m u_j ≤ 1`. For bounded denominators this is the periodicity of
`bounded_denominator_lock_periodic`.

**Proof.**
* *Period law* (`lockPer_add_one`). The twisted radial limit at height `x` is
  `𝒫(x) = Σ_{n u_j = x} a(n) c_j √u_j` (`sqrt_mul_tsum_ratSpec_eq`), and `𝒫(x + 1) = 𝒫(x)`
  (`tendsto_far_real_height`, `tendsto_far_translation`).
* *Hurwitz rearrangement* (`tsum_lockWeight_cpow_eq_hurwitz`). On `1 < Re s ≤ 3/2`,
  `F(s)V(s) = Σ_{(n,j)} a(n)c_j√u_j (n u_j)^{−s}` (`LSeries_mul_apLock_eq`). Grouping by the value
  `y` and moving `y` to `(0, 1]` with the period law gives `Σ_{0 < y_p ≤ 1} w(p) ζ(s, y_p)`.
  Both sides have the same fibre sums `𝒫(y) y^{−s}` (`HasSum.tsum_fiberwise`).
* *Continuation* (`differentiableAt_lockHurwitz`). With `ζ(s, y) = y^{−s} + ζ_EM(s, y + 1)` and the
  uniform bound for `ζ_EM`, the Hurwitz side `H` is holomorphic on `−½ < Re s < 3/2`, `s ≠ 1`.
  The domination is `|a(n)| n^{−3/2} |c_j| max(1, u_j^{−1})`.
* *Dual identity* (`apLock_upper_identity`). `G V = s(s − 1)Γ_ℝ H` on the lower half-strip and
  line. The lock gives `G(w) = w(w − 1)Γ_ℝ(1 − w) H(1 − w)` on the upper line, and on the upper
  strip by uniqueness from a half-line (`eq_zero_of_vertical_halfLine_strip`).
* *Functional equation* (`lockHurwitz_one_sub`). Termwise `hurwitzZeta_one_sub` gives, on
  `1 < Re w < 3/2`, `H(1 − w) = (2π)^{−w}Γ(w)(e^{−πiw/2} L(w, b_+) + e^{πiw/2} L(w, b_−))`, where
  `b_±(n) = Σ_{0 < y_p ≤ 1} w(p) e(±n y_p)` (`tsum_lockWeight_expZeta`).
* *Decay.* As in the bounded case, `(F − L(b_+))(1 + e^{−πiw}) = L(b_−) − L(b_+)`, so `F − L(b_+)`
  decays vertically on `1 < Re w < 3/2`. Being almost periodic, it vanishes there, hence on
  `Re w > 1`, and `a = b_+`.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

namespace AbelianTwist

open GaloisForLFunctions GaloisForLFunctions.HTGeometry IntegerMassRigidity FractionalMassRigidity
  PhaseLockRigidity HamburgerStability TruncatedRadial RightEdgeKernel FractionalMassTailRigidity
  HamburgerTwisted WeilSpectral

noncomputable section

/-! ## Lock points and weights -/

/-- The point `n u_j` of the pair `(n, j)`. -/
def lockPoint (u : ℕ → ℝ) (p : ℕ × ℕ) : ℝ := (p.1 : ℝ) * u p.2

/-- The weight `a(n) c_j √u_j` of the pair `(n, j)`. -/
def lockWeight (a c : ℕ → ℂ) (u : ℕ → ℝ) (p : ℕ × ℕ) : ℂ :=
  a p.1 * c p.2 * ((Real.sqrt (u p.2) : ℝ) : ℂ)

/-- The domination `|a(n)| n^{−3/2} |c_j| max(1, u_j^{−1})`. -/
def lockDom (a c : ℕ → ℂ) (u : ℕ → ℝ) (p : ℕ × ℕ) : ℝ :=
  ‖a p.1‖ * (p.1 : ℝ) ^ (-(3 / 2 : ℝ)) * (‖c p.2‖ * max 1 (u p.2)⁻¹)

theorem lockDom_nonneg (a c : ℕ → ℂ) (u : ℕ → ℝ) (p : ℕ × ℕ) : 0 ≤ lockDom a c u p :=
  mul_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))

theorem summable_lockDom {a c : ℕ → ℂ} {u : ℕ → ℝ}
    (ha : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)))
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹) : Summable (lockDom a c u) :=
  Summable.mul_of_nonneg ha hc
    (fun n => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (fun _ => mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))

theorem lockPoint_pos {u : ℕ → ℝ} (hu : ∀ j, 0 < u j) {p : ℕ × ℕ} (hp : p.1 ≠ 0) :
    0 < lockPoint u p :=
  mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp)) (hu p.2)

theorem lockPoint_nonneg {u : ℕ → ℝ} (hu : ∀ j, 0 < u j) (p : ℕ × ℕ) : 0 ≤ lockPoint u p :=
  mul_nonneg (Nat.cast_nonneg _) (hu p.2).le

/-- `√u_j (n u_j)^{−3/2} = n^{−3/2} u_j^{−1}`. -/
theorem sqrt_mul_lockPoint_rpow {u : ℕ → ℝ} (hu : ∀ j, 0 < u j) {p : ℕ × ℕ} (hp : p.1 ≠ 0) :
    Real.sqrt (u p.2) * lockPoint u p ^ (-(3 / 2 : ℝ)) =
      (p.1 : ℝ) ^ (-(3 / 2 : ℝ)) * (u p.2)⁻¹ := by
  have hn : (0 : ℝ) < p.1 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hp)
  have huj := hu p.2
  unfold lockPoint
  rw [Real.mul_rpow hn.le huj.le, Real.sqrt_eq_rpow,
    show (u p.2) ^ (1 / 2 : ℝ) * ((p.1 : ℝ) ^ (-(3 / 2 : ℝ)) * (u p.2) ^ (-(3 / 2 : ℝ))) =
      (p.1 : ℝ) ^ (-(3 / 2 : ℝ)) * ((u p.2) ^ (1 / 2 : ℝ) * (u p.2) ^ (-(3 / 2 : ℝ))) by ring,
    ← Real.rpow_add huj, show (1 / 2 : ℝ) + -(3 / 2) = -1 by norm_num, Real.rpow_neg_one]

/-- Below height one, `|w(p)| y_p^{−σ} ≤ D(p)` for every `σ ≤ 3/2`. -/
theorem norm_lockWeight_mul_rpow_le {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    {p : ℕ × ℕ} (hp0 : p.1 ≠ 0) (hp1 : lockPoint u p ≤ 1) {σ : ℝ} (hσ : σ ≤ 3 / 2) :
    ‖lockWeight a c u p‖ * lockPoint u p ^ (-σ) ≤ lockDom a c u p := by
  have hy := lockPoint_pos hu hp0
  have h1 : lockPoint u p ^ (-σ) ≤ lockPoint u p ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hy hp1 (by linarith)
  unfold lockWeight lockDom
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  calc ‖a p.1‖ * ‖c p.2‖ * Real.sqrt (u p.2) * lockPoint u p ^ (-σ)
      ≤ ‖a p.1‖ * ‖c p.2‖ * Real.sqrt (u p.2) * lockPoint u p ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ‖a p.1‖ * (p.1 : ℝ) ^ (-(3 / 2 : ℝ)) * (‖c p.2‖ * (u p.2)⁻¹) := by
        rw [mul_assoc _ (Real.sqrt _), sqrt_mul_lockPoint_rpow hu hp0]; ring
    _ ≤ ‖a p.1‖ * (p.1 : ℝ) ^ (-(3 / 2 : ℝ)) * (‖c p.2‖ * max 1 (u p.2)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _))
          (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- At height `x`, `|w(p)| ≤ x^{3/2} D(p)`. -/
theorem norm_lockWeight_le_of_lockPoint_eq {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    {p : ℕ × ℕ} (hp0 : p.1 ≠ 0) {x : ℝ} (hpx : lockPoint u p = x) :
    ‖lockWeight a c u p‖ ≤ x ^ (3 / 2 : ℝ) * lockDom a c u p := by
  have hy := lockPoint_pos hu hp0
  rw [hpx] at hy
  have hD := norm_lockWeight_mul_rpow_le (a := a) (c := c) hu hp0 (p := p)
  have heq : ‖lockWeight a c u p‖ = ‖lockWeight a c u p‖ * x ^ (-(3 / 2 : ℝ)) *
      x ^ (3 / 2 : ℝ) := by
    rw [mul_assoc, ← Real.rpow_add hy]; norm_num
  have hb : ‖lockWeight a c u p‖ * x ^ (-(3 / 2 : ℝ)) ≤ lockDom a c u p := by
    have h1 : (‖a p.1‖ * ‖c p.2‖ * Real.sqrt (u p.2)) * x ^ (-(3 / 2 : ℝ)) =
        ‖a p.1‖ * ‖c p.2‖ * (Real.sqrt (u p.2) * lockPoint u p ^ (-(3 / 2 : ℝ))) := by
      rw [hpx]; ring
    unfold lockWeight
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), h1,
      sqrt_mul_lockPoint_rpow hu hp0]
    unfold lockDom
    calc ‖a p.1‖ * ‖c p.2‖ * ((p.1 : ℝ) ^ (-(3 / 2 : ℝ)) * (u p.2)⁻¹)
        = ‖a p.1‖ * (p.1 : ℝ) ^ (-(3 / 2 : ℝ)) * (‖c p.2‖ * (u p.2)⁻¹) := by ring
      _ ≤ ‖a p.1‖ * (p.1 : ℝ) ^ (-(3 / 2 : ℝ)) * (‖c p.2‖ * max 1 (u p.2)⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _))
            (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  calc ‖lockWeight a c u p‖ = ‖lockWeight a c u p‖ * x ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) := heq
    _ ≤ lockDom a c u p * x ^ (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hy.le _)
    _ = x ^ (3 / 2 : ℝ) * lockDom a c u p := mul_comm _ _

/-! ## The period function -/

/-- The period function `𝒫(x) = Σ_{n u_j = x} a(n) c_j √u_j`. -/
def lockPer (a c : ℕ → ℂ) (u : ℕ → ℝ) (x : ℝ) : ℂ :=
  ∑' p : lockPoint u ⁻¹' {x}, lockWeight a c u p

theorem lockPer_eq_tsum_ite (a c : ℕ → ℂ) (u : ℕ → ℝ) (x : ℝ) :
    lockPer a c u x = ∑' p : ℕ × ℕ, if lockPoint u p = x then lockWeight a c u p else 0 := by
  classical
  unfold lockPer
  rw [tsum_subtype]
  refine tsum_congr fun p => ?_
  simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]

/-- **The radial limit is the period function.** -/
theorem sqrt_mul_tsum_ratSpec_eq {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (ha0 : a 0 = 0) (ha : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)))
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹) {x : ℝ} (hx : 0 < x) :
    ((Real.sqrt x : ℝ) : ℂ) * ∑' n, LSeries.term a (((3 / 2 : ℝ) : ℂ)) n * ratSpec 0 c u x n =
      lockPer a c u x := by
  classical
  have hrat : ∀ n : ℕ, ratSpec 0 c u x n =
      ∑' j, if (n : ℝ) * (u j / x) = ((1 : ℕ) : ℝ) then (n : ℂ) * c j else 0 := by
    intro n
    unfold ratSpec
    simp only [Pi.zero_apply, mul_zero, ite_self, tsum_zero, zero_add]
  have hiff : ∀ (n j : ℕ), (n : ℝ) * (u j / x) = ((1 : ℕ) : ℝ) ↔ lockPoint u (n, j) = x := by
    intro n j
    unfold lockPoint
    rw [Nat.cast_one, mul_div_assoc', div_eq_one_iff_eq hx.ne']
  have hterm : ∀ (n j : ℕ), ((Real.sqrt x : ℝ) : ℂ) * (LSeries.term a (((3 / 2 : ℝ) : ℂ)) n *
      (if (n : ℝ) * (u j / x) = ((1 : ℕ) : ℝ) then (n : ℂ) * c j else 0)) =
      if lockPoint u (n, j) = x then lockWeight a c u (n, j) else 0 := by
    intro n j
    rw [← if_congr (hiff n j) rfl rfl]
    split_ifs with h
    · rcases eq_or_ne n 0 with rfl | hn
      · simp [ha0, lockWeight]
      · have hxn : x = (n : ℝ) * u j := by
          have := (hiff n j).mp h; unfold lockPoint at this; exact this.symm
        have e : ((Real.sqrt x : ℝ) : ℂ) * (LSeries.term a (((3 / 2 : ℝ) : ℂ)) n *
            ((n : ℂ) * c j)) =
            ((Real.sqrt x : ℝ) : ℂ) * (LSeries.term a (((3 / 2 : ℝ) : ℂ)) n * n) * c j := by ring
        rw [e, term_three_halves_mul a hn, halfCoeff, natCast_cpow_half_eq_sqrt, hxn,
          Real.sqrt_mul (Nat.cast_nonneg n)]
        have hsn : ((Real.sqrt n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
          (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))).ne'
        unfold lockWeight
        push_cast
        field_simp
    · simp
  have hsum : Summable fun p : ℕ × ℕ =>
      if lockPoint u p = x then lockWeight a c u p else 0 := by
    refine Summable.of_norm_bounded ((summable_lockDom ha hc).mul_left (x ^ (3 / 2 : ℝ)))
      fun p => ?_
    split_ifs with h
    · rcases eq_or_ne p.1 0 with h0 | h0
      · have : lockWeight a c u p = 0 := by unfold lockWeight; rw [h0, ha0]; ring
        rw [this, norm_zero]
        exact mul_nonneg (Real.rpow_nonneg hx.le _) (lockDom_nonneg a c u p)
      · exact norm_lockWeight_le_of_lockPoint_eq hu h0 h
    · rw [norm_zero]; exact mul_nonneg (Real.rpow_nonneg hx.le _) (lockDom_nonneg a c u p)
  rw [lockPer_eq_tsum_ite, hsum.tsum_prod]
  simp only [hrat, ← tsum_mul_left]
  refine tsum_congr fun n => tsum_congr fun j => ?_
  rw [← hterm n j]

/-! ## The period law -/

/-- `Σ |a(n)| n^{−σ} < ∞` for the producer coefficients and every `σ > 1`. -/
theorem summable_norm_mul_rpow_dirichletExp {lam : ℕ → ℝ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {σ : ℝ}
    (hσ : 1 < σ) :
    Summable fun n : ℕ => ‖dirichletExp (lamLog lam) n‖ * (n : ℝ) ^ (-σ) := by
  have h := (LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
    (lseriesSummable_of_le (norm_lamLog_le lam) hsl (s := (σ : ℂ)) (by simpa using hσ))).1
  have h' := summable_norm_iff.mpr h
  simpa only [CharacterZeroPlanting.norm_term_ofReal _ (by linarith : (0 : ℝ) < σ)] using h'

/-- **The period law at every real height.** For a producer with lock `G(1 − s) = V(s)G(s)`,
`𝒫(x + 1) = 𝒫(x)` for every `x > 0`. -/
theorem lockPer_add_one {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = apLock c u (lineS τ) * G (lineS τ))
    {x : ℝ} (hx : 0 < x) :
    lockPer (dirichletExp (lamLog lam)) c u (x + 1) =
      lockPer (dirichletExp (lamLog lam)) c u x := by
  set a := dirichletExp (lamLog lam) with ha
  have hP0 : Summable fun k => ‖(0 : ℕ → ℂ) k‖ := by simp
  have hlockV : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) =
      (dirLock 0 (lineS τ) + apLock c u (lineS τ)) * G (lineS τ) := by
    intro τ hτ
    rw [hlock τ hτ, dirLock, LSeries_zero]
    simp
  have h1 := tendsto_far_real_height hsl hΦre hid hGc hGd hG2 hP0 hu hc hlockV
    (x := x + 1) (by linarith)
  have h0 := tendsto_far_real_height hsl hΦre hid hGc hGd hG2 hP0 hu hc hlockV hx
  have ht := tendsto_far_translation hsl hΦre hid hGc hGd hG2 hx
  have hper : ((Real.sqrt (x + 1) : ℝ) : ℂ) * ∑' n, LSeries.term a (((3 / 2 : ℝ) : ℂ)) n *
        ratSpec 0 c u (x + 1) n =
      ((Real.sqrt x : ℝ) : ℂ) * ∑' n, LSeries.term a (((3 / 2 : ℝ) : ℂ)) n *
        ratSpec 0 c u x n := by
    refine sub_eq_zero.mp (tendsto_nhds_unique (h1.sub h0) (ht.congr fun ε => ?_))
    rw [mul_sub]
  have ha0 : a 0 = 0 := dirichletExp_zero
  have haS := summable_norm_mul_rpow_dirichletExp hsl (σ := 3 / 2) (by norm_num)
  rw [← sqrt_mul_tsum_ratSpec_eq hu ha0 haS hc hx,
    ← sqrt_mul_tsum_ratSpec_eq hu ha0 haS hc (by linarith)]
  exact hper

theorem lockPer_add_nat {a c : ℕ → ℂ} {u : ℕ → ℝ}
    (hper : ∀ x : ℝ, 0 < x → lockPer a c u (x + 1) = lockPer a c u x) {x : ℝ} (hx : 0 < x) :
    ∀ m : ℕ, lockPer a c u (x + m) = lockPer a c u x := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.cast_succ, ← add_assoc, hper _ (by positivity), ih]

theorem lockPer_of_nonpos {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j) (ha0 : a 0 = 0)
    {t : ℝ} (ht : t ≤ 0) : lockPer a c u t = 0 := by
  rw [lockPer_eq_tsum_ite]
  refine (tsum_congr fun p => ?_).trans tsum_zero
  split_ifs with h
  · have hp0 : p.1 = 0 := by
      by_contra h0
      have := lockPoint_pos hu h0
      linarith
    unfold lockWeight; rw [hp0, ha0]; ring
  · rfl

/-! ## The rearrangement into Hurwitz zeta functions -/

/-- `u^{½ − σ} ≤ max(1, u^{−1})` for `½ ≤ σ ≤ 3/2`. -/
theorem rpow_half_sub_le_max {v σ : ℝ} (hv : 0 < v) (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 3 / 2) :
    v ^ (1 / 2 - σ) ≤ max 1 v⁻¹ := by
  rcases le_or_gt 1 v with h | h
  · exact (Real.rpow_le_one_of_one_le_of_nonpos h (by linarith)).trans (le_max_left _ _)
  · calc v ^ (1 / 2 - σ) ≤ v ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hv h.le (by linarith)
      _ = v⁻¹ := Real.rpow_neg_one v
      _ ≤ max 1 v⁻¹ := le_max_right _ _

/-- The terms of `Σ_p w(p) y_p^{−s}` are at most `|a(n)| n^{−σ} |c_j| max(1, u_j^{−1})`. -/
theorem norm_lockWeight_mul_cpow_le {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (ha0 : a 0 = 0) (p : ℕ × ℕ) {s : ℂ} (hs1 : 1 / 2 ≤ s.re) (hs2 : s.re ≤ 3 / 2) :
    ‖lockWeight a c u p * ((lockPoint u p : ℝ) : ℂ) ^ (-s)‖ ≤
      ‖a p.1‖ * (p.1 : ℝ) ^ (-s.re) * (‖c p.2‖ * max 1 (u p.2)⁻¹) := by
  rcases eq_or_ne p.1 0 with h0 | h0
  · have : lockWeight a c u p = 0 := by unfold lockWeight; rw [h0, ha0]; ring
    rw [this, zero_mul, norm_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _)))
  have hn : (0 : ℝ) < p.1 := Nat.cast_pos.mpr (Nat.pos_of_ne_zero h0)
  have huj := hu p.2
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lockPoint_pos hu h0), Complex.neg_re]
  unfold lockWeight lockPoint
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.mul_rpow hn.le huj.le]
  have hsq : Real.sqrt (u p.2) * (u p.2) ^ (-s.re) = (u p.2) ^ (1 / 2 - s.re) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add huj]; ring_nf
  calc ‖a p.1‖ * ‖c p.2‖ * Real.sqrt (u p.2) * ((p.1 : ℝ) ^ (-s.re) * u p.2 ^ (-s.re))
      = ‖a p.1‖ * (p.1 : ℝ) ^ (-s.re) * (‖c p.2‖ * (Real.sqrt (u p.2) * u p.2 ^ (-s.re))) := by
        ring
    _ = ‖a p.1‖ * (p.1 : ℝ) ^ (-s.re) * (‖c p.2‖ * (u p.2) ^ (1 / 2 - s.re)) := by rw [hsq]
    _ ≤ ‖a p.1‖ * (p.1 : ℝ) ^ (-s.re) * (‖c p.2‖ * max 1 (u p.2)⁻¹) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (rpow_half_sub_le_max huj hs1 hs2) (norm_nonneg _))
          (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- `‖w(p)‖ ≤ D(p)` below height one. -/
theorem norm_lockWeight_le_lockDom {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (ha0 : a 0 = 0) {p : ℕ × ℕ} (hp1 : lockPoint u p ≤ 1) :
    ‖lockWeight a c u p‖ ≤ lockDom a c u p := by
  rcases eq_or_ne p.1 0 with h0 | h0
  · have : lockWeight a c u p = 0 := by unfold lockWeight; rw [h0, ha0]; ring
    rw [this, norm_zero]; exact lockDom_nonneg a c u p
  have h := norm_lockWeight_mul_rpow_le (a := a) (c := c) hu h0 hp1 (σ := 0) (by norm_num)
  rwa [neg_zero, Real.rpow_zero, mul_one] at h

/-- **Fibre sums of the Dirichlet side.** -/
theorem tsum_fiber_lockWeight_cpow (a c : ℕ → ℂ) (u : ℕ → ℝ) (s : ℂ) (t : ℝ) :
    ∑' p : lockPoint u ⁻¹' {t}, lockWeight a c u p * ((lockPoint u p : ℝ) : ℂ) ^ (-s) =
      lockPer a c u t * ((t : ℝ) : ℂ) ^ (-s) := by
  have h : ∀ p : lockPoint u ⁻¹' {t},
      lockWeight a c u p * ((lockPoint u p : ℝ) : ℂ) ^ (-s) =
        lockWeight a c u p * ((t : ℝ) : ℂ) ^ (-s) := fun p => by
    have hp := p.2
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hp
    rw [hp]
  rw [tsum_congr h, tsum_mul_right]
  rfl

/-- The Hurwitz point `k + y_p`. -/
def hurwitzPoint (u : ℕ → ℝ) (q : (ℕ × ℕ) × ℕ) : ℝ := (q.2 : ℝ) + lockPoint u q.1

/-- The Hurwitz-side summand `[0 < y_p ≤ 1] w(p) (k + y_p)^{−s}`. -/
def hurwitzLockTerm (a c : ℕ → ℂ) (u : ℕ → ℝ) (s : ℂ) (q : (ℕ × ℕ) × ℕ) : ℂ :=
  if 0 < lockPoint u q.1 ∧ lockPoint u q.1 ≤ 1 then
    lockWeight a c u q.1 * (1 / ((q.2 : ℂ) + ((lockPoint u q.1 : ℝ) : ℂ)) ^ s) else 0

theorem natCast_add_ofReal (k : ℕ) (y : ℝ) : (k : ℂ) + ((y : ℝ) : ℂ) = (((k : ℝ) + y : ℝ) : ℂ) := by
  push_cast; ring

theorem norm_one_div_natCast_add_cpow {k : ℕ} {y : ℝ} (hy : 0 < y) (s : ℂ) :
    ‖1 / ((k : ℂ) + ((y : ℝ) : ℂ)) ^ s‖ = 1 / |(k : ℝ) + y| ^ s.re := by
  have hky : 0 < (k : ℝ) + y := by positivity
  rw [natCast_add_ofReal, norm_div, norm_one, Complex.norm_cpow_eq_rpow_re_of_pos hky,
    abs_of_pos hky]

/-- `Σ_k |k + y|^{−σ} ≤ y^{−σ} + Σ_k (k + 1)^{−σ}`. -/
theorem tsum_one_div_natCast_add_rpow_le {y σ : ℝ} (hy : 0 < y) (hσ : 1 < σ) :
    ∑' k : ℕ, 1 / |(k : ℝ) + y| ^ σ ≤ y ^ (-σ) + ∑' k : ℕ, 1 / |(k : ℝ) + 1| ^ σ := by
  have hs := (Real.summable_one_div_nat_add_rpow y σ).mpr hσ
  have hs1 := (Real.summable_one_div_nat_add_rpow 1 σ).mpr hσ
  rw [hs.tsum_eq_zero_add]
  have h0 : 1 / |((0 : ℕ) : ℝ) + y| ^ σ = y ^ (-σ) := by
    rw [Nat.cast_zero, zero_add, abs_of_pos hy, Real.rpow_neg hy.le, one_div]
  rw [h0]
  refine add_le_add le_rfl (Summable.tsum_le_tsum (fun k => ?_) ?_ hs1)
  · have h1 : 0 < (k : ℝ) + 1 := by positivity
    have h2 : (k : ℝ) + 1 ≤ ((k + 1 : ℕ) : ℝ) + y := by push_cast; linarith
    rw [abs_of_pos h1, abs_of_pos (by positivity : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + y)]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos h1 _)
      (Real.rpow_le_rpow h1.le h2 (by linarith))
  · exact (summable_nat_add_iff 1).mpr hs

/-- The domination of the Hurwitz-side summands. -/
theorem summable_hurwitzLockTerm {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (ha0 : a 0 = 0) (ha : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)))
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹) {s : ℂ} (hs1 : 1 < s.re)
    (hs2 : s.re ≤ 3 / 2) : Summable (hurwitzLockTerm a c u s) := by
  classical
  set Zc : ℝ := ∑' k : ℕ, 1 / |(k : ℝ) + 1| ^ s.re with hZc
  have hZc0 : 0 ≤ Zc := tsum_nonneg fun k => by positivity
  set b : (ℕ × ℕ) × ℕ → ℝ := fun q =>
    if 0 < lockPoint u q.1 ∧ lockPoint u q.1 ≤ 1 then
      ‖lockWeight a c u q.1‖ * (1 / |(q.2 : ℝ) + lockPoint u q.1| ^ s.re) else 0 with hb
  have hb0 : 0 ≤ b := fun q => by
    simp only [hb]; split_ifs
    · exact mul_nonneg (norm_nonneg _) (by positivity)
    · exact le_rfl
  have hbs : Summable b := by
    refine (summable_prod_of_nonneg hb0).mpr ⟨fun p => ?_, ?_⟩
    · simp only [hb]
      split_ifs with h
      · exact ((Real.summable_one_div_nat_add_rpow _ _).mpr hs1).mul_left _
      · exact summable_zero
    · refine Summable.of_nonneg_of_le (fun p => tsum_nonneg fun k => hb0 (p, k))
        (fun p => ?_) ((summable_lockDom ha hc).mul_left (1 + Zc))
      simp only [hb]
      split_ifs with h
      · rw [tsum_mul_left]
        have hy := h.1
        have h1 := tsum_one_div_natCast_add_rpow_le hy hs1
        have hp0 : p.1 ≠ 0 := fun h0 => by
          have hy' := h.1
          unfold lockPoint at hy'
          rw [h0, Nat.cast_zero, zero_mul] at hy'
          exact lt_irrefl 0 hy'
        have hD1 := norm_lockWeight_mul_rpow_le (a := a) (c := c) hu hp0 h.2 hs2
        have hD0 := norm_lockWeight_le_lockDom (a := a) (c := c) hu ha0 h.2
        calc ‖lockWeight a c u p‖ * ∑' k : ℕ, 1 / |(k : ℝ) + lockPoint u p| ^ s.re
            ≤ ‖lockWeight a c u p‖ * (lockPoint u p ^ (-s.re) + Zc) :=
              mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
          _ = ‖lockWeight a c u p‖ * lockPoint u p ^ (-s.re) + ‖lockWeight a c u p‖ * Zc := by
              ring
          _ ≤ lockDom a c u p + lockDom a c u p * Zc :=
              add_le_add hD1 (mul_le_mul_of_nonneg_right hD0 hZc0)
          _ = (1 + Zc) * lockDom a c u p := by ring
      · rw [tsum_zero]; exact mul_nonneg (by linarith) (lockDom_nonneg a c u p)
  refine Summable.of_norm_bounded hbs fun q => ?_
  unfold hurwitzLockTerm
  simp only [hb]
  split_ifs with h
  · rw [norm_mul, norm_one_div_natCast_add_cpow h.1]
  · rw [norm_zero]

/-- The Hurwitz side sums to `Σ_p [0 < y_p ≤ 1] w(p) ζ(s, y_p)`. -/
theorem tsum_hurwitzLockTerm {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (ha0 : a 0 = 0) (ha : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)))
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹) {s : ℂ} (hs1 : 1 < s.re)
    (hs2 : s.re ≤ 3 / 2) :
    ∑' q, hurwitzLockTerm a c u s q = ∑' p : ℕ × ℕ,
      if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
        lockWeight a c u p * HurwitzZeta.hurwitzZeta (lockPoint u p) s else 0 := by
  rw [(summable_hurwitzLockTerm hu ha0 ha hc hs1 hs2).tsum_prod]
  refine tsum_congr fun p => ?_
  unfold hurwitzLockTerm
  dsimp only
  split_ifs with h
  · rw [tsum_mul_left, (HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
      ⟨h.1.le, h.2⟩ hs1).tsum_eq]
  · exact tsum_zero

/-- `t − (⌈t⌉ − 1) ∈ (0, 1]` for `t > 0`. -/
theorem sub_ceil_sub_one_mem {t : ℝ} (ht : 0 < t) :
    0 < t - ((⌈t⌉₊ - 1 : ℕ) : ℝ) ∧ t - ((⌈t⌉₊ - 1 : ℕ) : ℝ) ≤ 1 := by
  have hc : 1 ≤ ⌈t⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr ht).ne'
  have h1 : ((⌈t⌉₊ - 1 : ℕ) : ℝ) < t := Nat.lt_ceil.mp (by omega)
  have h2 : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
  have h3 : ((⌈t⌉₊ - 1 : ℕ) : ℝ) = (⌈t⌉₊ : ℝ) - 1 := by rw [Nat.cast_sub hc]; simp
  constructor <;> linarith

theorem eq_ceil_sub_one {t y : ℝ} {k : ℕ} (hy0 : 0 < y) (hy1 : y ≤ 1) (h : (k : ℝ) + y = t) :
    k = ⌈t⌉₊ - 1 := by
  have : ⌈t⌉₊ = k + 1 := by
    rw [Nat.ceil_eq_iff (Nat.succ_ne_zero k)]
    constructor
    · rw [Nat.succ_sub_one]; linarith
    · push_cast; linarith
  omega

/-- **Fibre sums of the Hurwitz side.** By the period law, the Hurwitz points over `t` carry the
period function at `t − (⌈t⌉ − 1) ∈ (0, 1]`, which equals `𝒫(t)`. -/
theorem tsum_fiber_hurwitzLockTerm {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (ha0 : a 0 = 0) (ha : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)))
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹)
    (hper : ∀ x : ℝ, 0 < x → lockPer a c u (x + 1) = lockPer a c u x) (s : ℂ) (t : ℝ) :
    ∑' q : hurwitzPoint u ⁻¹' {t}, hurwitzLockTerm a c u s q =
      lockPer a c u t * ((t : ℝ) : ℂ) ^ (-s) := by
  classical
  set F : (ℕ × ℕ) × ℕ → ℂ := fun q =>
    if 0 < lockPoint u q.1 ∧ lockPoint u q.1 ≤ 1 then lockWeight a c u q.1 else 0 with hFdef
  have hfib : ∀ q : hurwitzPoint u ⁻¹' {t}, hurwitzLockTerm a c u s q =
      F q * (1 / ((t : ℝ) : ℂ) ^ s) := by
    intro q
    have hq := q.2
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hurwitzPoint] at hq
    unfold hurwitzLockTerm
    rw [natCast_add_ofReal, hq, hFdef]
    dsimp only
    split_ifs
    · rfl
    · rw [zero_mul]
  rw [tsum_congr hfib, tsum_mul_right]
  have hS' : ∑' q : hurwitzPoint u ⁻¹' {t}, F q = ∑' q : (ℕ × ℕ) × ℕ,
      if hurwitzPoint u q = t then F q else 0 := by
    rw [tsum_subtype (hurwitzPoint u ⁻¹' {t}) F]
    refine tsum_congr fun q => ?_
    simp only [Set.indicator, Set.mem_preimage, Set.mem_singleton_iff]
  rw [hS']
  rcases le_or_gt t 0 with ht | ht
  · have h0 : ∑' q : (ℕ × ℕ) × ℕ, (if hurwitzPoint u q = t then F q else 0) = 0 := by
      refine (tsum_congr fun q => ?_).trans tsum_zero
      simp only [hFdef]
      split_ifs with h1 h2
      · exfalso
        have := h2.1
        simp only [hurwitzPoint] at h1
        have hk : (0 : ℝ) ≤ q.2 := Nat.cast_nonneg _
        linarith
      · rfl
      · rfl
    rw [h0, lockPer_of_nonpos hu ha0 ht, zero_mul, zero_mul]
  · set k₀ : ℕ := ⌈t⌉₊ - 1 with hk₀
    obtain ⟨hm0, hm1⟩ := sub_ceil_sub_one_mem ht
    set G : ℕ × ℕ → ℂ := fun p =>
      if lockPoint u p = t - (k₀ : ℝ) then lockWeight a c u p else 0 with hG
    have hF : ∀ q : (ℕ × ℕ) × ℕ,
        (if hurwitzPoint u q = t then F q else 0) = if q.2 = k₀ then G q.1 else 0 := by
      intro q
      simp only [hG, hurwitzPoint, hFdef]
      by_cases hk : q.2 = k₀
      · rw [if_pos hk, hk]
        by_cases hy : lockPoint u q.1 = t - (k₀ : ℝ)
        · rw [if_pos (by rw [hy]; ring), if_pos ⟨by rw [hy]; exact hm0, by rw [hy]; exact hm1⟩,
            if_pos hy]
        · rw [if_neg hy]
          split_ifs with h1 h2
          · exact absurd (by linarith) hy
          · rfl
          · rfl
      · rw [if_neg hk]
        split_ifs with h1 h2
        · exact absurd (eq_ceil_sub_one h2.1 h2.2 h1) hk
        · rfl
        · rfl
    have hGb : ∀ p, ‖G p‖ ≤ lockDom a c u p := by
      intro p
      simp only [hG]
      split_ifs with h
      · exact norm_lockWeight_le_lockDom hu ha0 (by rw [h]; exact hm1)
      · rw [norm_zero]; exact lockDom_nonneg a c u p
    have hsum : Summable fun q : (ℕ × ℕ) × ℕ => if q.2 = k₀ then G q.1 else 0 := by
      set b : (ℕ × ℕ) × ℕ → ℝ := fun q => if q.2 = k₀ then lockDom a c u q.1 else 0 with hb
      have hb0 : 0 ≤ b := fun q => by
        simp only [hb]; split_ifs
        · exact lockDom_nonneg a c u q.1
        · exact le_rfl
      have hbs : Summable b := by
        refine (summable_prod_of_nonneg hb0).mpr ⟨fun p => ?_, ?_⟩
        · exact (hasSum_ite_eq k₀ (lockDom a c u p)).summable
        · simp only [hb]
          refine (summable_lockDom ha hc).congr fun p => ?_
          exact (tsum_ite_eq k₀ (fun _ => lockDom a c u p)).symm
      refine Summable.of_norm_bounded hbs fun q => ?_
      simp only [hb]
      split_ifs
      · exact hGb q.1
      · rw [norm_zero]
    have hSG : ∑' q : (ℕ × ℕ) × ℕ, (if hurwitzPoint u q = t then F q else 0) = ∑' p, G p := by
      rw [tsum_congr hF, hsum.tsum_prod]
      exact tsum_congr fun p => tsum_ite_eq k₀ (fun _ => G p)
    have hper' := lockPer_add_nat hper hm0 k₀
    rw [sub_add_cancel] at hper'
    rw [hSG, hG, ← lockPer_eq_tsum_ite, ← hper', one_div, ← Complex.cpow_neg]

/-- **The Hurwitz rearrangement.** For `1 < Re s ≤ 3/2`,
`Σ_{(n,j)} w(n,j)(n u_j)^{−s} = Σ_{n u_j ≤ 1} w(n,j) ζ(s, n u_j)`. -/
theorem tsum_lockWeight_cpow_eq_hurwitz {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (ha0 : a 0 = 0) (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-σ))
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹)
    (hper : ∀ x : ℝ, 0 < x → lockPer a c u (x + 1) = lockPer a c u x) {s : ℂ}
    (hs1 : 1 < s.re) (hs2 : s.re ≤ 3 / 2) :
    ∑' p : ℕ × ℕ, lockWeight a c u p * ((lockPoint u p : ℝ) : ℂ) ^ (-s) =
      ∑' p : ℕ × ℕ, if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
        lockWeight a c u p * HurwitzZeta.hurwitzZeta (lockPoint u p) s else 0 := by
  have ha32 := ha (3 / 2) (by norm_num)
  have hf : Summable fun p : ℕ × ℕ => lockWeight a c u p * ((lockPoint u p : ℝ) : ℂ) ^ (-s) :=
    Summable.of_norm_bounded (Summable.mul_of_nonneg (ha s.re hs1) hc
      (fun n => mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      (fun j => mul_nonneg (norm_nonneg _) (le_trans zero_le_one (le_max_left _ _))))
      fun p => norm_lockWeight_mul_cpow_le hu ha0 p (by linarith) hs2
  have h1 := hf.hasSum.tsum_fiberwise (lockPoint u)
  have e1 : (fun t : ℝ => ∑' p : lockPoint u ⁻¹' {t},
      lockWeight a c u p * ((lockPoint u p : ℝ) : ℂ) ^ (-s)) =
      fun t : ℝ => lockPer a c u t * ((t : ℝ) : ℂ) ^ (-s) :=
    funext fun t => tsum_fiber_lockWeight_cpow a c u s t
  rw [e1] at h1
  have h2 := (summable_hurwitzLockTerm hu ha0 ha32 hc hs1 hs2).hasSum.tsum_fiberwise
    (hurwitzPoint u)
  have e2 : (fun t : ℝ => ∑' q : hurwitzPoint u ⁻¹' {t}, hurwitzLockTerm a c u s q) =
      fun t : ℝ => lockPer a c u t * ((t : ℝ) : ℂ) ^ (-s) :=
    funext fun t => tsum_fiber_hurwitzLockTerm hu ha0 ha32 hc hper s t
  rw [e2] at h2
  rw [h1.unique h2, tsum_hurwitzLockTerm hu ha0 ha32 hc hs1 hs2]

/-- The product of a Dirichlet term and a lock term is the weighted power at the lock point. -/
theorem term_mul_lockTerm_eq (a c : ℕ → ℂ) {u : ℕ → ℝ} (hu : ∀ j, 0 < u j) {p : ℕ × ℕ}
    (h0 : p.1 ≠ 0) (s : ℂ) :
    LSeries.term a s p.1 * (c p.2 * ((u p.2 : ℝ) : ℂ) ^ (-(s - 1 / 2))) =
      lockWeight a c u p * ((lockPoint u p : ℝ) : ℂ) ^ (-s) := by
  have huj := hu p.2
  have hu0 : ((u p.2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr huj.ne'
  rw [LSeries.term_of_ne_zero h0]
  unfold lockWeight lockPoint
  have e1 : ((((p.1 : ℝ) * u p.2 : ℝ)) : ℂ) ^ (-s) =
      (p.1 : ℂ) ^ (-s) * ((u p.2 : ℝ) : ℂ) ^ (-s) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg _) huj.le,
      Complex.ofReal_natCast]
  have e3 : ((u p.2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt (u p.2) : ℝ) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow huj.le]
    norm_num
  have e2 : ((u p.2 : ℝ) : ℂ) ^ (-(s - 1 / 2)) =
      ((u p.2 : ℝ) : ℂ) ^ (-s) * ((Real.sqrt (u p.2) : ℝ) : ℂ) := by
    rw [show -(s - 1 / 2) = -s + 1 / 2 by ring, Complex.cpow_add _ _ hu0, e3]
  rw [e1, e2, div_eq_mul_inv, ← Complex.cpow_neg]
  ring

/-- **The lock times the Dirichlet series.** For `1 < Re s ≤ 3/2`,
`F(s) V(s) = Σ_{(n,j)} a(n) c_j √u_j (n u_j)^{−s}`. -/
theorem LSeries_mul_apLock_eq {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j) (ha0 : a 0 = 0)
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹) {s : ℂ} (hs1 : 1 < s.re)
    (hs2 : s.re ≤ 3 / 2) (haS : LSeriesSummable a s) :
    LSeries a s * apLock c u s =
      ∑' p : ℕ × ℕ, lockWeight a c u p * ((lockPoint u p : ℝ) : ℂ) ^ (-s) := by
  have hcs : Summable fun j => ‖c j * ((u j : ℝ) : ℂ) ^ (-(s - 1 / 2))‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_) hc
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hu j)]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have : (-(s - 1 / 2)).re = 1 / 2 - s.re := by simp
    rw [this]
    exact rpow_half_sub_le_max (hu j) (by linarith) hs2
  have hV : apLock c u s = ∑' j, c j * ((u j : ℝ) : ℂ) ^ (-(s - 1 / 2)) :=
    apLock_of_mem c u (by linarith) hs2
  have haN : Summable fun n => ‖LSeries.term a s n‖ :=
    (summable_norm_iff (f := fun n => LSeries.term a s n)).mpr haS
  have hprod := tsum_mul_tsum_of_summable_norm (f := fun n => LSeries.term a s n)
    (g := fun j => c j * ((u j : ℝ) : ℂ) ^ (-(s - 1 / 2))) haN hcs
  have hL : LSeries a s * apLock c u s = (∑' n, LSeries.term a s n) *
      ∑' j, c j * ((u j : ℝ) : ℂ) ^ (-(s - 1 / 2)) := by
    rw [hV]; rfl
  rw [hL, hprod]
  refine tsum_congr fun p => ?_
  rcases eq_or_ne p.1 0 with h0 | h0
  · have hw : lockWeight a c u p = 0 := by unfold lockWeight; rw [h0, ha0]; ring
    rw [hw, zero_mul, h0, LSeries.term_zero, zero_mul]
  · exact term_mul_lockTerm_eq a c hu h0 s

/-! ## The continued Hurwitz side -/

/-- The continued Hurwitz side `Σ_{0 < y_p ≤ 1} w(p) (y_p^{−s} + ζ_EM(s, y_p + 1))`. -/
def lockHurwitz (a c : ℕ → ℂ) (u : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
    lockWeight a c u p * (((lockPoint u p : ℝ) : ℂ) ^ (-s) +
      hurwitzZetaEM (lockPoint u p + 1) s) else 0

/-- The continued side is the Hurwitz sum on `Re s > −½`, `s ≠ 1`. -/
theorem lockHurwitz_eq (a c : ℕ → ℂ) (u : ℕ → ℝ) {s : ℂ} (hs : -(1 / 2 : ℝ) < s.re)
    (hs1 : s ≠ 1) : lockHurwitz a c u s = ∑' p : ℕ × ℕ,
      if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
        lockWeight a c u p * HurwitzZeta.hurwitzZeta (lockPoint u p) s else 0 := by
  unfold lockHurwitz
  refine tsum_congr fun p => ?_
  split_ifs with h
  · rw [hurwitzZeta_eq_rpow_add_hurwitzZetaEM h.1 h.2 hs hs1]
  · rfl

/-- **Holomorphy of the continued side** on `−½ < Re s < 3/2`, `s ≠ 1`. -/
theorem differentiableAt_lockHurwitz {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (ha0 : a 0 = 0) (ha : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)))
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹) {s₀ : ℂ} (h1 : -(1 / 2 : ℝ) < s₀.re)
    (h2 : s₀.re < 3 / 2) (hs₀ : s₀ ≠ 1) : DifferentiableAt ℂ (lockHurwitz a c u) s₀ := by
  have hd1 : 0 < ‖s₀ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hs₀)
  set r : ℝ := min (min ((s₀.re + 1 / 2) / 2) ((3 / 2 - s₀.re) / 2)) (min (‖s₀ - 1‖ / 2) 1)
    with hr
  have hr0 : 0 < r := by
    rw [hr]
    refine lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) one_pos)
  set M : ℝ := 2 ^ (3 / 2 : ℝ) / (‖s₀ - 1‖ / 2) + 2 + (‖s₀‖ + 1) * (‖s₀‖ + 2) / 4 with hM
  have hM0 : 0 ≤ M := by positivity
  have hball : ∀ s ∈ Metric.ball s₀ r, -(1 / 2 : ℝ) < s.re ∧ s.re < 3 / 2 ∧
      ‖s₀ - 1‖ / 2 ≤ ‖s - 1‖ ∧ ‖s‖ ≤ ‖s₀‖ + 1 := by
    intro s hs
    have hd : ‖s - s₀‖ < r := mem_ball_iff_norm.mp hs
    have hre : |s.re - s₀.re| ≤ ‖s - s₀‖ := by
      rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
    have hr1 : r ≤ (s₀.re + 1 / 2) / 2 := (min_le_left _ _).trans (min_le_left _ _)
    have hr2 : r ≤ (3 / 2 - s₀.re) / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hr3 : r ≤ ‖s₀ - 1‖ / 2 := (min_le_right _ _).trans (min_le_left _ _)
    have hr4 : r ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
    have habs := abs_lt.mp (hre.trans_lt hd)
    refine ⟨by linarith, by linarith, ?_, ?_⟩
    · have := norm_sub_norm_le (s₀ - 1) (s - 1)
      rw [show s₀ - 1 - (s - 1) = -(s - s₀) by ring, norm_neg] at this
      linarith
    · have := norm_sub_norm_le s s₀
      linarith
  have hU : DifferentiableOn ℂ (lockHurwitz a c u) (Metric.ball s₀ r) := by
    refine Complex.differentiableOn_tsum_of_summable_norm
      ((summable_lockDom ha hc).mul_left (1 + M)) (fun p s hs => ?_) Metric.isOpen_ball
      (fun p s hs => ?_)
    · obtain ⟨hs1, hs2, hs3, -⟩ := hball s hs
      have hsne : s ≠ 1 := fun h => by
        rw [h, sub_self, norm_zero] at hs3; linarith
      split_ifs with h
      · have hy0 : ((lockPoint u p : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h.1.ne'
        exact ((differentiableAt_const _).mul ((differentiableAt_id.neg.const_cpow
          (Or.inl hy0)).add (differentiableAt_hurwitzZetaEM (by linarith [h.1]) hs1 hsne)))
          |>.differentiableWithinAt
      · exact (differentiableAt_const _).differentiableWithinAt
    · obtain ⟨hs1, hs2, hs3, hs4⟩ := hball s hs
      split_ifs with h
      · have hp0 : p.1 ≠ 0 := fun h0 => by
          have hy' := h.1
          unfold lockPoint at hy'
          rw [h0, Nat.cast_zero, zero_mul] at hy'
          exact lt_irrefl 0 hy'
        have hEM := norm_hurwitzZetaEM_le (b := lockPoint u p + 1) (by linarith [h.1])
          (by linarith [h.2]) (s := s) hs1.le
        have hEM' : ‖hurwitzZetaEM (lockPoint u p + 1) s‖ ≤ M := by
          refine hEM.trans ?_
          rw [hM]
          have hq : 2 ^ (3 / 2 : ℝ) / ‖s - 1‖ ≤ 2 ^ (3 / 2 : ℝ) / (‖s₀ - 1‖ / 2) :=
            div_le_div_of_nonneg_left (by positivity) (by linarith) hs3
          have hn1 : ‖s + 1‖ ≤ ‖s₀‖ + 2 := by
            have := norm_add_le s 1; rw [norm_one] at this; linarith
          have hq2 : ‖s‖ * ‖s + 1‖ / 4 ≤ (‖s₀‖ + 1) * (‖s₀‖ + 2) / 4 := by
            have := mul_le_mul hs4 hn1 (norm_nonneg _) (by positivity)
            linarith
          linarith
        have hy := h.1
        have hcp : ‖((lockPoint u p : ℝ) : ℂ) ^ (-s)‖ = lockPoint u p ^ (-s.re) := by
          rw [Complex.norm_cpow_eq_rpow_re_of_pos hy, Complex.neg_re]
        have hD32 := norm_lockWeight_mul_rpow_le (a := a) (c := c) hu hp0 h.2 hs2.le
        have hD0 := norm_lockWeight_le_lockDom (a := a) (c := c) hu ha0 h.2
        rw [norm_mul]
        calc ‖lockWeight a c u p‖ * ‖((lockPoint u p : ℝ) : ℂ) ^ (-s) +
              hurwitzZetaEM (lockPoint u p + 1) s‖
            ≤ ‖lockWeight a c u p‖ * (lockPoint u p ^ (-s.re) + M) := by
              refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans ?_) (norm_nonneg _)
              rw [hcp]; linarith
          _ = ‖lockWeight a c u p‖ * lockPoint u p ^ (-s.re) + ‖lockWeight a c u p‖ * M := by
              ring
          _ ≤ lockDom a c u p + lockDom a c u p * M :=
              add_le_add hD32 (mul_le_mul_of_nonneg_right hD0 hM0)
          _ = (1 + M) * lockDom a c u p := by ring
      · rw [norm_zero]; exact mul_nonneg (by linarith) (lockDom_nonneg a c u p)
  exact hU.differentiableAt (Metric.ball_mem_nhds s₀ hr0)

/-! ## Uniqueness on a vertical strip -/

/-- **Uniqueness from a vertical boundary half-line, on a strip.** A function holomorphic on
`{a < Re w < b, Im w > 0}`, continuous at the half-line `{Re w = a, Im w > 0}` and vanishing there,
vanishes on the strip. -/
theorem eq_zero_of_vertical_halfLine_strip {E : ℂ → ℂ} {a b : ℝ}
    (hd : ∀ w : ℂ, a < w.re → w.re < b → 0 < w.im → DifferentiableAt ℂ E w)
    (hc : ∀ w : ℂ, w.re = a → 0 < w.im → ContinuousAt E w)
    (h0 : ∀ w : ℂ, w.re = a → 0 < w.im → E w = 0)
    {w : ℂ} (hw : a < w.re) (hwb : w.re < b) (hwi : 0 < w.im) : E w = 0 := by
  classical
  set U : Set ℂ := {z | 0 < z.im ∧ z.re < b} with hU
  have hUo : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  set F : ℂ → ℂ := fun z => if a ≤ z.re then E z else 0 with hF
  have hright : ∀ z : ℂ, a < z.re → F =ᶠ[𝓝 z] E := by
    intro z hz
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz] with ζ hζ
    simp only [hF, if_pos (le_of_lt (show a < ζ.re from hζ))]
  have hleft : ∀ z : ℂ, z.re < a → F =ᶠ[𝓝 z] fun _ => 0 := by
    intro z hz
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hz] with ζ hζ
    simp only [hF, if_neg (not_le.mpr (show ζ.re < a from hζ))]
  have hcont : ContinuousOn F U := by
    intro z hz
    apply ContinuousAt.continuousWithinAt
    rcases lt_trichotomy z.re a with hlt | heq | hgt
    · exact continuousAt_const.congr (hleft z hlt).symm
    · have hEz : E z = 0 := h0 z heq hz.1
      have hFz : F z = 0 := by simp only [hF, if_pos heq.ge, hEz]
      have hE : Tendsto (fun ζ => ‖E ζ‖) (𝓝 z) (𝓝 0) := by
        have h' : Tendsto (fun ζ => ‖E ζ‖) (𝓝 z) (𝓝 ‖E z‖) := (hc z heq hz.1).norm
        rwa [hEz, norm_zero] at h'
      rw [ContinuousAt, hFz]
      refine squeeze_zero_norm (fun ζ => ?_) hE
      simp only [hF]
      split_ifs <;> simp
    · exact (hd z hgt hz.2 hz.1).continuousAt.congr (hright z hgt).symm
  have hdiff : DifferentiableOn ℂ F (U ∩ {z : ℂ | (I * z + 0).im ≠ a}) := by
    intro z hz
    have hre : z.re ≠ a := by simpa using hz.2
    rcases lt_or_gt_of_ne hre with hlt | hgt
    · exact ((differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq
        (hleft z hlt)).differentiableWithinAt
    · exact ((hd z hgt hz.1.2 hz.1.1).congr_of_eventuallyEq (hright z hgt)).differentiableWithinAt
  have hFd : DifferentiableOn ℂ F U :=
    Bottcher.differentiableOn_of_off_line (c := I) (d := 0) (a := a) I_ne_zero hUo hcont hdiff
  have hab : a < b := hw.trans hwb
  have hz₀ : ((a - 1 : ℝ) : ℂ) + I ∈ U := by
    simp only [hU, Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.I_im,
      Complex.add_re, Complex.ofReal_re, Complex.I_re]
    constructor <;> linarith
  have hUc : Convex ℝ U := (convex_halfSpace_im_gt 0).inter (convex_halfSpace_re_lt b)
  have hzero : Set.EqOn F 0 U :=
    (hFd.analyticOnNhd hUo).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hUc.isPreconnected hz₀ (hleft _ (by simp))
  have := hzero (show w ∈ U from ⟨hwi, hwb⟩)
  simpa [hF, if_pos hw.le] using this

/-! ## The functional equation of the Hurwitz side -/

/-- The exponential coefficients `b_ε(n) = Σ_{0 < y_p ≤ 1} w(p) e(ε n y_p)`. -/
def lockExpCoeff (a c : ℕ → ℂ) (u : ℕ → ℝ) (ε : ℝ) (n : ℕ) : ℂ :=
  ∑' p : ℕ × ℕ, if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
    lockWeight a c u p * cexp (2 * Real.pi * I * ((ε * lockPoint u p : ℝ) : ℂ) * n) else 0

theorem norm_cexp_two_pi_I_mul (x : ℝ) (n : ℕ) :
    ‖cexp (2 * Real.pi * I * (x : ℂ) * n)‖ = 1 := by
  rw [show 2 * (Real.pi : ℂ) * I * (x : ℂ) * n = ((2 * Real.pi * x * n : ℝ) : ℂ) * I by
    push_cast; ring, Complex.norm_exp_ofReal_mul_I]

/-- `Σ_p [0 < y_p ≤ 1] |w(p)| < ∞`. -/
theorem summable_norm_lockWeight_le_one {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (ha0 : a 0 = 0) (ha : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)))
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹) :
    Summable fun p : ℕ × ℕ => if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
      ‖lockWeight a c u p‖ else 0 :=
  Summable.of_nonneg_of_le (fun p => by split_ifs; exacts [norm_nonneg _, le_rfl])
    (fun p => by
      split_ifs with h
      · exact norm_lockWeight_le_lockDom hu ha0 h.2
      · exact lockDom_nonneg a c u p) (summable_lockDom ha hc)

/-- The exponential coefficients are bounded by `W₀ = Σ_{y_p ≤ 1} |w(p)|`. -/
theorem norm_lockExpCoeff_le {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (ha0 : a 0 = 0) (ha : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)))
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹) (ε : ℝ) (n : ℕ) :
    ‖lockExpCoeff a c u ε n‖ ≤ ∑' p : ℕ × ℕ,
      if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then ‖lockWeight a c u p‖ else 0 := by
  have hs := summable_norm_lockWeight_le_one hu ha0 ha hc
  have hb : ∀ p : ℕ × ℕ, ‖(if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
      lockWeight a c u p * cexp (2 * Real.pi * I * ((ε * lockPoint u p : ℝ) : ℂ) * n) else 0)‖ ≤
      if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then ‖lockWeight a c u p‖ else 0 := by
    intro p
    split_ifs
    · rw [norm_mul, norm_cexp_two_pi_I_mul, mul_one]
    · rw [norm_zero]
  exact (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs)).trans
    ((Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hs).tsum_le_tsum hb hs)

/-- **The exponential sums as Dirichlet series.** For `Re w > 1`,
`Σ_p [0 < y_p ≤ 1] w(p) F(ε y_p, w) = Σ_n b_ε(n) n^{−w}`, with `F` the periodic zeta function. -/
theorem tsum_lockWeight_expZeta {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (ha0 : a 0 = 0) (ha : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)))
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹) (ε : ℝ) {w : ℂ} (hw : 1 < w.re) :
    ∑' p : ℕ × ℕ, (if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
      lockWeight a c u p * HurwitzZeta.expZeta ((ε * lockPoint u p : ℝ)) w else 0) =
      LSeries (lockExpCoeff a c u ε) w := by
  set T : ℕ × ℕ → ℕ → ℂ := fun p n => if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
    lockWeight a c u p * (cexp (2 * Real.pi * I * ((ε * lockPoint u p : ℝ) : ℂ) * n) /
      (n : ℂ) ^ w) else 0 with hT
  have hr : Summable fun n : ℕ => (n : ℝ) ^ (-w.re) := Real.summable_nat_rpow.mpr (by linarith)
  have hW := summable_norm_lockWeight_le_one hu ha0 ha hc
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw; linarith
  have hTb : ∀ p n, ‖T p n‖ ≤ (if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
      ‖lockWeight a c u p‖ else 0) * (n : ℝ) ^ (-w.re) := by
    intro p n
    simp only [hT]
    split_ifs
    · rw [norm_mul, norm_div, norm_cexp_two_pi_I_mul, one_div]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rcases eq_or_ne n 0 with rfl | hn
      · simp [Complex.zero_cpow hw0, Real.zero_rpow (by intro h; linarith : -w.re ≠ 0)]
      · rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
          Real.rpow_neg (Nat.cast_nonneg _)]
    · rw [norm_zero, zero_mul]
  have hsum : Summable (Function.uncurry T) :=
    Summable.of_norm_bounded (Summable.mul_of_nonneg hW hr
      (fun p => by split_ifs; exacts [norm_nonneg _, le_rfl])
      (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)) fun x => hTb x.1 x.2
  have hleft : ∀ p : ℕ × ℕ, (if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
      lockWeight a c u p * HurwitzZeta.expZeta ((ε * lockPoint u p : ℝ)) w else 0) =
      ∑' n, T p n := by
    intro p
    simp only [hT]
    split_ifs
    · rw [tsum_mul_left, (HurwitzZeta.hasSum_expZeta_of_one_lt_re _ hw).tsum_eq]
    · exact tsum_zero.symm
  have hright : ∀ n : ℕ, LSeries.term (lockExpCoeff a c u ε) w n = ∑' p, T p n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero]
      refine (tsum_congr fun p => ?_).trans tsum_zero |>.symm
      simp only [hT, Nat.cast_zero, Complex.zero_cpow hw0, div_zero, mul_zero, ite_self]
    · rw [LSeries.term_of_ne_zero hn, lockExpCoeff, ← tsum_div_const]
      refine tsum_congr fun p => ?_
      simp only [hT]
      split_ifs
      · ring
      · rw [zero_div]
  rw [tsum_congr hleft, LSeries, tsum_congr hright, hsum.tsum_comm]

theorem norm_expZeta_le (x : ℝ) {w : ℂ} (hw : 1 < w.re) :
    ‖HurwitzZeta.expZeta x w‖ ≤ ∑' n : ℕ, (n : ℝ) ^ (-w.re) := by
  have hr : Summable fun n : ℕ => (n : ℝ) ^ (-w.re) := Real.summable_nat_rpow.mpr (by linarith)
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw; linarith
  have hH := HurwitzZeta.hasSum_expZeta_of_one_lt_re x hw
  have hb : ∀ n : ℕ, ‖cexp (2 * Real.pi * I * (x : ℂ) * n) / (n : ℂ) ^ w‖ ≤
      (n : ℝ) ^ (-w.re) := by
    intro n
    rw [norm_div, norm_cexp_two_pi_I_mul]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [Complex.zero_cpow hw0, Real.zero_rpow (by intro h; linarith : -w.re ≠ 0)]
    · rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn),
        Real.rpow_neg (Nat.cast_nonneg _), one_div]
  have hs := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb hr
  rw [← hH.tsum_eq]
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb hr)

/-- **The functional equation of the Hurwitz side.** For `1 < Re w < 3/2`,
`H(1 − w) = (2π)^{−w} Γ(w) (e^{−πiw/2} L(w, b_+) + e^{πiw/2} L(w, b_−))`. -/
theorem lockHurwitz_one_sub {a c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (ha0 : a 0 = 0) (ha : Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-(3 / 2 : ℝ)))
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹) {w : ℂ} (hw1 : 1 < w.re) (hw2 : w.re < 3 / 2) :
    lockHurwitz a c u (1 - w) = (2 * (Real.pi : ℂ)) ^ (-w) * Gamma w *
      (cexp (-(Real.pi : ℂ) * I * w / 2) * LSeries (lockExpCoeff a c u 1) w +
        cexp ((Real.pi : ℂ) * I * w / 2) * LSeries (lockExpCoeff a c u (-1)) w) := by
  have hw0 : w ≠ 0 := fun h => by rw [h, Complex.zero_re] at hw1; linarith
  have hw1' : w ≠ 1 := fun h => by rw [h, Complex.one_re] at hw1; linarith
  have hre : -(1 / 2 : ℝ) < (1 - w).re := by rw [Complex.sub_re, Complex.one_re]; linarith
  have hs1 : 1 - w ≠ 1 := fun h => hw0 (by linear_combination -h)
  have hnn : ∀ n : ℕ, w ≠ -(n : ℂ) := fun n h => by
    have := congrArg Complex.re h
    rw [Complex.neg_re, Complex.natCast_re] at this
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  set C : ℂ := (2 * (Real.pi : ℂ)) ^ (-w) * Gamma w with hC
  set Em : ℂ := cexp (-(Real.pi : ℂ) * I * w / 2) with hEm
  set Ep : ℂ := cexp ((Real.pi : ℂ) * I * w / 2) with hEp
  set X : ℕ × ℕ → ℂ := fun p => if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
    lockWeight a c u p * HurwitzZeta.expZeta (((1 : ℝ) * lockPoint u p : ℝ)) w else 0 with hX
  set Y : ℕ × ℕ → ℂ := fun p => if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
    lockWeight a c u p * HurwitzZeta.expZeta (((-1 : ℝ) * lockPoint u p : ℝ)) w else 0 with hY
  have hW := summable_norm_lockWeight_le_one hu ha0 ha hc
  have hXs : Summable X := Summable.of_norm_bounded (hW.mul_right (∑' n : ℕ, (n : ℝ) ^ (-w.re)))
    fun p => by
      simp only [hX]; split_ifs
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_expZeta_le _ hw1) (norm_nonneg _)
      · rw [norm_zero, zero_mul]
  have hYs : Summable Y := Summable.of_norm_bounded (hW.mul_right (∑' n : ℕ, (n : ℝ) ^ (-w.re)))
    fun p => by
      simp only [hY]; split_ifs
      · rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_expZeta_le _ hw1) (norm_nonneg _)
      · rw [norm_zero, zero_mul]
  have hterm : ∀ p : ℕ × ℕ, (if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
      lockWeight a c u p * HurwitzZeta.hurwitzZeta (lockPoint u p) (1 - w) else 0) =
      C * Em * X p + C * Ep * Y p := by
    intro p
    simp only [hX, hY]
    split_ifs
    · rw [HurwitzZeta.hurwitzZeta_one_sub _ hnn (Or.inr hw1'), one_mul, ← AddCircle.coe_neg,
        show (-1 : ℝ) * lockPoint u p = -lockPoint u p by ring]
      ring
    · ring
  rw [lockHurwitz_eq a c u hre hs1, tsum_congr hterm, (hXs.mul_left _).tsum_add (hYs.mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_lockWeight_expZeta hu ha0 ha hc 1 hw1,
    tsum_lockWeight_expZeta hu ha0 ha hc (-1) hw1]
  ring

/-! ## The lock identity on the upper strip -/

/-- **The dual identity.** For a producer with lock `G(1 − s) = V(s)G(s)` on the lower line,
`G(w) = w(w − 1)Γ_ℝ(1 − w) H(1 − w)` on `½ < Re w < 3/2`, `Im w > 0`, where `H` is the continued
Hurwitz side. -/
theorem apLock_upper_identity {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = apLock c u (lineS τ) * G (lineS τ))
    {w : ℂ} (hw1 : 1 / 2 < w.re) (hw2 : w.re < 3 / 2) (hwi : 0 < w.im) :
    G w = w * (w - 1) * Gammaℝ (1 - w) *
      lockHurwitz (dirichletExp (lamLog lam)) c u (1 - w) := by
  set a := dirichletExp (lamLog lam) with ha
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have ha0 : a 0 = 0 := dirichletExp_zero
  have haσ : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-σ) :=
    fun σ hσ => summable_norm_mul_rpow_dirichletExp hsl hσ
  have ha32 := haσ (3 / 2) (by norm_num)
  have hper : ∀ x : ℝ, 0 < x → lockPer a c u (x + 1) = lockPer a c u x := fun x hx =>
    lockPer_add_one hsl hΦre hid hGc hGd hG2 hu hc hlock hx
  /- `F V = H` on `1 < Re s ≤ 3/2`. -/
  have hFV : ∀ s : ℂ, 1 < s.re → s.re ≤ 3 / 2 →
      LSeries a s * apLock c u s = lockHurwitz a c u s := by
    intro s hs1 hs2
    have hs1' : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs1; linarith
    rw [LSeries_mul_apLock_eq hu ha0 hc hs1 hs2 (hLa s hs1).1,
      tsum_lockWeight_cpow_eq_hurwitz hu ha0 haσ hc hper hs1 hs2,
      lockHurwitz_eq a c u (by linarith) hs1']
  /- The identity on the lower half-strip, and on the lower line. -/
  set R : ℂ → ℂ := fun z => z * (z - 1) * Gammaℝ z * lockHurwitz a c u z with hR
  set L : ℂ → ℂ := fun z => G z * apLock c u z with hL
  set Ω : Set ℂ := {z | 1 / 2 < z.re ∧ z.re < 3 / 2 ∧ z.im < 0} with hΩ
  have hΩo : IsOpen Ω :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      ((isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt Complex.continuous_im continuous_const))
  have hΩc : Convex ℝ Ω :=
    (convex_halfSpace_re_gt _).inter ((convex_halfSpace_re_lt _).inter (convex_halfSpace_im_lt _))
  have hRat : ∀ z : ℂ, -(1 / 2 : ℝ) < z.re → 0 < z.re → z.re < 3 / 2 → z ≠ 1 →
      DifferentiableAt ℂ R z := fun z h0 hre h3 hz1 =>
    ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul
      (RHTower.TruncatedRadial.differentiableAt_Gammaℝ_of_re_pos hre)).mul
      (differentiableAt_lockHurwitz hu ha0 ha32 hc h0 h3 hz1)
  have hLd : DifferentiableOn ℂ L Ω := fun z hz =>
    ((hGd z hz.1).differentiableAt.mul
      (differentiableAt_apLock hu hc hz.1 hz.2.1)).differentiableWithinAt
  have hRd : DifferentiableOn ℂ R Ω := fun z hz =>
    (hRat z (by linarith [hz.1]) (by linarith [hz.1]) hz.2.1 (fun h1 => by
      have h3 := hz.2.2
      rw [h1] at h3
      simp at h3)).differentiableWithinAt
  have hbase : ∀ z : ℂ, 1 < z.re → z.re < 3 / 2 → L z = R z := by
    intro z h1 h2
    simp only [hL, hR]
    rw [G_eq_bigG hsl hid hGd hG2 h1, bigG, ← (hLa z h1).2, ← hFV z h1 h2.le]
    ring
  set z₀ : ℂ := ((5 / 4 : ℝ) : ℂ) - I with hz₀
  have hz₀Ω : z₀ ∈ Ω := by simp only [hΩ, hz₀, mem_setOf_eq]; norm_num
  have hEq : Set.EqOn L R Ω := by
    refine (hLd.analyticOnNhd hΩo).eqOn_of_preconnected_of_eventuallyEq (hRd.analyticOnNhd hΩo)
      hΩc.isPreconnected hz₀Ω ?_
    have hopen : IsOpen {z : ℂ | 1 < z.re ∧ z.re < 3 / 2} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    filter_upwards [hopen.mem_nhds (show z₀ ∈ {z : ℂ | 1 < z.re ∧ z.re < 3 / 2} by
      simp only [hz₀, mem_setOf_eq]; norm_num)] with z hz
    exact hbase z hz.1 hz.2
  have hline : ∀ τ : ℝ, τ < 0 → L (lineS τ) = R (lineS τ) := by
    intro τ hτ
    set s₀ := lineS τ with hs₀
    have hs₀re : s₀.re = 1 / 2 := lineS_re τ
    have hs₀im : s₀.im = 2 * τ := by rw [hs₀, lineS_eq]; simp
    have hs₀1 : s₀ ≠ 1 := fun h1 => by
      have := congrArg Complex.im h1
      rw [hs₀im] at this
      simp at this
      linarith
    have hcL : ContinuousAt L s₀ :=
      (hGc s₀ hs₀re.symm.le).mul (continuous_apLock hu hc).continuousAt
    have hcR : ContinuousAt R s₀ :=
      (hRat s₀ (by rw [hs₀re]; norm_num) (by rw [hs₀re]; norm_num) (by rw [hs₀re]; norm_num)
        hs₀1).continuousAt
    have hpath : Tendsto (fun ε : ℝ => s₀ + (ε : ℂ)) (𝓝[>] 0) (𝓝 s₀) := by
      have hc' : Continuous (fun ε : ℝ => s₀ + (ε : ℂ)) :=
        continuous_const.add Complex.continuous_ofReal
      simpa using (hc'.tendsto 0).mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ ε : ℝ in 𝓝[>] 0, s₀ + (ε : ℂ) ∈ Ω := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
      simp only [hΩ, mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.add_im,
        Complex.ofReal_im, add_zero, hs₀re, hs₀im]
      refine ⟨by linarith [hε.1], by linarith [hε.2], by linarith⟩
    have h1 : Tendsto (fun ε : ℝ => L (s₀ + (ε : ℂ)) - R (s₀ + (ε : ℂ))) (𝓝[>] 0)
        (𝓝 (L s₀ - R s₀)) :=
      (hcL.sub hcR).tendsto.comp hpath
    have h2 : Tendsto (fun ε : ℝ => L (s₀ + (ε : ℂ)) - R (s₀ + (ε : ℂ))) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [hev] with ε hε
        rw [hEq hε, sub_self])
    exact sub_eq_zero.mp (tendsto_nhds_unique h1 h2)
  /- The identity on the upper line. -/
  set K : ℂ → ℂ := fun z => z * (z - 1) * Gammaℝ (1 - z) * lockHurwitz a c u (1 - z) with hK
  have hupper : ∀ z : ℂ, z.re = 1 / 2 → 0 < z.im → G z = K z := by
    intro z hzre hzim
    set τ : ℝ := -(z.im / 2) with hτdef
    have hτ : τ < 0 := by rw [hτdef]; linarith
    have hz : z = 1 - lineS τ := by
      rw [one_sub_lineS, lineS_eq]
      apply Complex.ext
      · simp [hzre]
      · simp [hτdef]; ring
    have hLR := hline τ hτ
    simp only [hL, hR] at hLR
    rw [hz, hlock τ hτ, mul_comm, hLR]
    simp only [hK, sub_sub_cancel]
    ring
  /- The identity on the upper strip. -/
  have hKd : ∀ z : ℂ, 0 < z.im → -(1 / 2 : ℝ) < (1 - z).re → (1 - z).re < 3 / 2 →
      DifferentiableAt ℂ K z := by
    intro z hzi h1 h2
    have hz1 : 1 - z ≠ 1 := fun h => by
      have := congrArg Complex.im h
      simp at this
      linarith
    have hGa : DifferentiableAt ℂ (fun z : ℂ => Gammaℝ (1 - z)) z :=
      (differentiableAt_Gammaℝ_of_im_ne (by simp; linarith)).comp z
        ((differentiableAt_const _).sub differentiableAt_id)
    have hHa : DifferentiableAt ℂ (fun z : ℂ => lockHurwitz a c u (1 - z)) z :=
      (differentiableAt_lockHurwitz hu ha0 ha32 hc h1 h2 hz1).comp z
        ((differentiableAt_const _).sub differentiableAt_id)
    exact ((differentiableAt_id.mul (differentiableAt_id.sub_const 1)).mul hGa).mul hHa
  have h0 := eq_zero_of_vertical_halfLine_strip (E := fun z => G z - K z) (a := 1 / 2) (b := 3 / 2)
    (fun z hz1 hz2 hzi => (hGd z hz1).differentiableAt.sub
      (hKd z hzi (by rw [Complex.sub_re, Complex.one_re]; linarith)
        (by rw [Complex.sub_re, Complex.one_re]; linarith)))
    (fun z hz hzi => (hGc z hz.symm.le).sub (hKd z hzi
      (by rw [Complex.sub_re, Complex.one_re, hz]; norm_num)
      (by rw [Complex.sub_re, Complex.one_re, hz]; norm_num)).continuousAt)
    (fun z hz hzi => sub_eq_zero.mpr (hupper z hz hzi)) hw1 hw2 hwi
  exact sub_eq_zero.mp h0

/-! ## The coefficients -/

/-- **An almost-periodic lock forces almost-periodic coefficients.** Let `G` be a Herglotz producer
for the weights `lam` with lower-line lock `G(1 − s) = V(s) G(s)`, `V(s) = Σ_j c_j u_j^{−(s−½)}`,
`u_j > 0`, `Σ_j |c_j| max(1, u_j^{−1}) < ∞`. Then the Dirichlet coefficients `a = exp⋆(lam/log)`
satisfy, for every `n ≥ 1`,

`a(n) = Σ_{(m,j) : 0 < m u_j ≤ 1} a(m) c_j √u_j e(n m u_j)`. -/
theorem apLock_coefficients {lam : ℕ → ℝ} {Φ G : ℂ → ℂ}
    (hsl : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ)
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hid : ∀ s : ℂ, 1 < s.re →
      Φ s = zetaArchimedeanDatum s + 1 / (s - 1) - LSeries (lamTwo lam) s)
    (hGc : ∀ s : ℂ, 1 / 2 ≤ s.re → ContinuousAt G s)
    (hGd : ∀ s : ℂ, 1 / 2 < s.re → HasDerivAt G (Φ s * G s) s) (hG2 : G 2 = bigG lam 2)
    {c : ℕ → ℂ} {u : ℕ → ℝ} (hu : ∀ j, 0 < u j)
    (hc : Summable fun j => ‖c j‖ * max 1 (u j)⁻¹)
    (hlock : ∀ τ : ℝ, τ < 0 → G (1 - lineS τ) = apLock c u (lineS τ) * G (lineS τ)) :
    ∀ n : ℕ, n ≠ 0 → dirichletExp (lamLog lam) n =
      lockExpCoeff (dirichletExp (lamLog lam)) c u 1 n := by
  set a := dirichletExp (lamLog lam) with ha
  have hLa : ∀ s : ℂ, 1 < s.re → LSeriesSummable a s ∧ LSeries a s = zetaOf lam s :=
    fun s hs => LSeries_dirichletExp (lamLog_zero lam) (lamLog_one lam)
      (lseriesSummable_of_le (norm_lamLog_le lam) hsl hs)
  have ha0 : a 0 = 0 := dirichletExp_zero
  have ha32 := summable_norm_mul_rpow_dirichletExp hsl (σ := 3 / 2) (by norm_num)
  set b := lockExpCoeff a c u 1 with hb
  set bA := lockExpCoeff a c u (-1) with hbA
  set W₀ : ℝ := ∑' p : ℕ × ℕ, if 0 < lockPoint u p ∧ lockPoint u p ≤ 1 then
    ‖lockWeight a c u p‖ else 0 with hW₀
  have hbS : ∀ s : ℂ, 1 < s.re → LSeriesSummable b s := fun s hs =>
    LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨W₀, fun n _ => by
      rw [sub_self, Real.rpow_zero, mul_one]; exact norm_lockExpCoeff_le hu ha0 ha32 hc 1 n⟩
  have hbAS : ∀ s : ℂ, 1 < s.re → LSeriesSummable bA s := fun s hs =>
    LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨W₀, fun n _ => by
      rw [sub_self, Real.rpow_zero, mul_one]; exact norm_lockExpCoeff_le hu ha0 ha32 hc (-1) n⟩
  /- The key identity on `1 < Re w < 3/2`, `Im w > 0`. -/
  have hkey : ∀ w : ℂ, 1 < w.re → w.re < 3 / 2 → 0 < w.im →
      (LSeries a w - LSeries b w) * (1 + cexp (-(Real.pi : ℂ) * I * w)) =
        LSeries bA w - LSeries b w := by
    intro w hw hw2 hwi
    have hq := apLock_upper_identity hsl hΦre hid hGc hGd hG2 hu hc hlock (by linarith) hw2 hwi
    have hw0 : w ≠ 0 := fun h0 => by rw [h0] at hw; simp at hw; linarith
    have hw1 : w - 1 ≠ 0 := fun h0 => by
      rw [sub_eq_zero] at h0; rw [h0] at hw; simp at hw
    have hΓw : Gammaℝ w ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by linarith)
    have hcos := cos_pi_mul_div_two_ne_zero hwi.ne'
    rw [G_eq_bigG hsl hid hGd hG2 hw, bigG, ← (hLa w hw).2,
      lockHurwitz_one_sub hu ha0 ha32 hc hw hw2] at hq
    rw [show w * (w - 1) * Gammaℝ (1 - w) * ((2 * (Real.pi : ℂ)) ^ (-w) * Gamma w *
        (cexp (-(Real.pi : ℂ) * I * w / 2) * LSeries b w +
          cexp ((Real.pi : ℂ) * I * w / 2) * LSeries bA w)) =
      w * (w - 1) * (Gammaℝ (1 - w) * ((2 * (Real.pi : ℂ)) ^ (-w) * Gamma w)) *
        (cexp (-(Real.pi : ℂ) * I * w / 2) * LSeries b w +
          cexp ((Real.pi : ℂ) * I * w / 2) * LSeries bA w) by ring,
      gammaR_one_sub_mul_Gamma hcos] at hq
    have h2cos : 2 * cos ((Real.pi : ℂ) * w / 2) =
        cexp ((Real.pi : ℂ) * I * w / 2) + cexp (-(Real.pi : ℂ) * I * w / 2) := by
      rw [two_cos]; congr 1 <;> congr 1 <;> ring
    have hexp : cexp (-(Real.pi : ℂ) * I * w) =
        cexp (-(Real.pi : ℂ) * I * w / 2) * (cexp ((Real.pi : ℂ) * I * w / 2))⁻¹ := by
      rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; ring
    have he1 : cexp ((Real.pi : ℂ) * I * w / 2) ≠ 0 := Complex.exp_ne_zero _
    have hsum : cexp ((Real.pi : ℂ) * I * w / 2) + cexp (-(Real.pi : ℂ) * I * w / 2) ≠ 0 := by
      rw [← h2cos]; exact mul_ne_zero two_ne_zero hcos
    rw [h2cos] at hq
    set Ep := cexp ((Real.pi : ℂ) * I * w / 2) with hEp
    set Em := cexp (-(Real.pi : ℂ) * I * w / 2) with hEm
    set A := LSeries bA w with hA
    set B := LSeries b w with hB
    have hne : w * (w - 1) * Gammaℝ w ≠ 0 := mul_ne_zero (mul_ne_zero hw0 hw1) hΓw
    have hS := inv_mul_cancel₀ hsum
    have hmain : LSeries a w * (Ep + Em) = Ep * A + Em * B := by
      apply mul_left_cancel₀ hne
      linear_combination (Ep + Em) * hq + (w * (w - 1) * Gammaℝ w * (Em * B + Ep * A)) * hS
    rw [hexp]
    field_simp
    linear_combination hmain
  /- Decay in the vertical direction on `1 < σ < 3/2`. -/
  have hcoef : ∀ σ : ℝ, 1 < σ → σ < 3 / 2 → LSeries a σ = LSeries b σ := by
    intro σ hσ hσ2
    have hσ' : 1 < (σ : ℂ).re := by simpa using hσ
    have hvre : ∀ y : ℝ, 1 < ((σ : ℂ) + (y : ℂ) * I).re := fun y => by simpa using hσ
    have hvre2 : ∀ y : ℝ, ((σ : ℂ) + (y : ℂ) * I).re < 3 / 2 := fun y => by simpa using hσ2
    set g : ℕ → ℂ := a - b with hg
    have hgS : LSeriesSummable g (σ : ℂ) := (hLa _ hσ').1.sub (hbS _ hσ')
    have hgv : ∀ y : ℝ, LSeries g ((σ : ℂ) + (y : ℂ) * I) =
        LSeries a ((σ : ℂ) + (y : ℂ) * I) - LSeries b ((σ : ℂ) + (y : ℂ) * I) := by
      intro y
      rw [hg, LSeries_sub (hLa _ (hvre y)).1 (hbS _ (hvre y))]
    set M : ℝ := (∑' n, ‖LSeries.term bA (σ : ℂ) n‖) + ∑' n, ‖LSeries.term b (σ : ℂ) n‖ with hM
    have hbound : ∀ y : ℝ, 1 ≤ y →
        ‖LSeries g ((σ : ℂ) + (y : ℂ) * I)‖ ≤ M / (Real.exp (Real.pi * y) - 1) := by
      intro y hy
      set w : ℂ := (σ : ℂ) + (y : ℂ) * I with hwdef
      have hwim : 0 < w.im := by simp [hwdef]; linarith
      have hk := hkey w (hvre y) (hvre2 y) hwim
      have hnorm_e : ‖cexp (-(Real.pi : ℂ) * I * w)‖ = Real.exp (Real.pi * y) := by
        rw [Complex.norm_exp]; congr 1; simp [hwdef]
      have hexp1 : 1 < Real.exp (Real.pi * y) :=
        Real.one_lt_exp_iff.mpr (mul_pos Real.pi_pos (by linarith))
      have hden : Real.exp (Real.pi * y) - 1 ≤ ‖1 + cexp (-(Real.pi : ℂ) * I * w)‖ := by
        have := norm_sub_le (1 + cexp (-(Real.pi : ℂ) * I * w)) 1
        rw [add_sub_cancel_left, norm_one, hnorm_e] at this
        linarith
      have hAB : ‖LSeries bA w - LSeries b w‖ ≤ M := by
        rw [hM]
        refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
        · exact norm_LSeries_vertical_le (hbAS _ hσ') y
        · exact norm_LSeries_vertical_le (hbS _ hσ') y
      rw [hgv y, le_div_iff₀ (by linarith)]
      calc ‖LSeries a w - LSeries b w‖ * (Real.exp (Real.pi * y) - 1)
          ≤ ‖LSeries a w - LSeries b w‖ * ‖1 + cexp (-(Real.pi : ℂ) * I * w)‖ :=
            mul_le_mul_of_nonneg_left hden (norm_nonneg _)
        _ = ‖LSeries bA w - LSeries b w‖ := by rw [← norm_mul, hk]
        _ ≤ M := hAB
    have hdiv : Tendsto (fun y : ℝ => Real.exp (Real.pi * y) - 1) atTop atTop := by
      have h1 := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop Real.pi_pos)
      simpa [sub_eq_add_neg] using Filter.tendsto_atTop_add_const_right atTop (-1) h1
    have hlim : Tendsto (fun y : ℝ => M / (Real.exp (Real.pi * y) - 1)) atTop (𝓝 0) :=
      (tendsto_const_nhds (x := M)).div_atTop hdiv
    have htend : Tendsto (fun y : ℝ => LSeries g ((σ : ℂ) + (y : ℂ) * I)) atTop (𝓝 0) :=
      squeeze_zero_norm' (by
        filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
        exact hbound y hy) hlim
    have h0 := HTGeometry.eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero
      (isBohrAlmostPeriodic_LSeries_vertical hgS) htend 0
    rw [hgv 0] at h0
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at h0
    exact sub_eq_zero.mp h0
  /- The identity theorem on `Re s > 1`. -/
  have habs_a : LSeries.abscissaOfAbsConv a ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      (hLa y (by simpa using hy)).1
  have habs_b : LSeries.abscissaOfAbsConv b ≤ (1 : ℝ) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      hbS y (by simpa using hy)
  set U : Set ℂ := {s : ℂ | 1 < s.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hanal : ∀ f : ℕ → ℂ, LSeries.abscissaOfAbsConv f ≤ (1 : ℝ) →
      AnalyticOnNhd ℂ (LSeries f) U := by
    intro f hf
    refine DifferentiableOn.analyticOnNhd (fun s hs => ?_) hUo
    have hopen : IsOpen {z : ℂ | LSeries.abscissaOfAbsConv f < z.re} :=
      isOpen_lt continuous_const (EReal.continuous_coe_iff.mpr Complex.continuous_re)
    exact ((LSeries_differentiableOn f).differentiableAt (hopen.mem_nhds
      (hf.trans_lt (by exact_mod_cast (show (1 : ℝ) < s.re from hs))))).differentiableWithinAt
  have hfreq : ∃ᶠ z in 𝓝[≠] (((5 / 4 : ℝ)) : ℂ), LSeries a z = LSeries b z := by
    have hreal : ∀ᶠ t : ℝ in 𝓝[≠] (5 / 4 : ℝ), LSeries a t = LSeries b t := by
      have hI : Ioo (1 : ℝ) (3 / 2) ∈ 𝓝 (5 / 4 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
      filter_upwards [nhdsWithin_le_nhds hI] with t ht
      exact hcoef t ht.1 ht.2
    have hmap : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝[≠] (5 / 4 : ℝ)) (𝓝[≠] (((5 / 4 : ℝ)) : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · exact (Complex.continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 5 / 4)
        exact fun h => ht (Complex.ofReal_injective h)
    exact hmap.frequently hreal.frequently
  have hEq : Set.EqOn (LSeries a) (LSeries b) U :=
    (hanal a habs_a).eqOn_of_preconnected_of_frequently_eq (hanal b habs_b)
      (convex_halfSpace_re_gt 1).isPreconnected (show (1 : ℝ) < (((5 / 4 : ℝ)) : ℂ).re by
        simp; norm_num) hfreq
  intro n hn
  have habs_a' : LSeries.abscissaOfAbsConv a < ⊤ :=
    habs_a.trans_lt (EReal.coe_lt_top _)
  have habs_b' : LSeries.abscissaOfAbsConv b < ⊤ :=
    habs_b.trans_lt (EReal.coe_lt_top _)
  have hev : (fun x : ℝ => LSeries a x) =ᶠ[atTop] fun x : ℝ => LSeries b x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact hEq (show (1 : ℝ) < ((x : ℂ)).re by simpa using hx)
  exact LSeries.eq_of_LSeries_eventually_eq habs_a' habs_b' hev hn

end

end AbelianTwist

end RHTower
