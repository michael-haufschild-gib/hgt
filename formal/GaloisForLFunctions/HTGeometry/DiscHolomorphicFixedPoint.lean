import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# A holomorphic map of a disc into a smaller concentric disc has a unique attracting fixed point

Let `ψ` be holomorphic on the disc `D(c, R)` with `ψ(D(c, R)) ⊆ D̄(c, θR)`, `0 ≤ θ < 1`.

**Theorem** (`exists_unique_fixedPoint`).  `ψ` has a fixed point `p` with `|p − c| ≤ θR`, it is the
only fixed point in `D(c, R)`, and `|ψ′(p)| ≤ κ(θ) < 1` with `κ(θ) = 2θ'/(1 + θ'²)`, `θ' = (1 + θ)/2`.

**Proof.**  Normalise to the unit disc.  The Möbius maps `mob a u = (u − a)/(1 − āu)` are
automorphisms of the disc (`norm_mob_lt_one`, `mob_neg_mob`), so the Schwarz lemma gives the
two-point Schwarz–Pick inequality `ρ(χx, χy) ≤ ρ(x, y)` for every holomorphic self-map `χ` of the disc,
`ρ(x, y) = |mob x y|` (`norm_mob_le_of_mapsTo`).  Multiplication by `θ' < 1` contracts `ρ` by the
factor `2θ'/(1 + θ'²)` (`norm_mob_smul_le`, from `(1 + t²)|1 − w| ≤ 2|1 − t²w|` for `|w| ≤ 1`).  Writing
`ψ = θ'·(ψ/θ')` makes `ψ` a `κ`-contraction for `ρ` (`norm_mob_le_contraction`).  Since
`|x − y| ≤ 2ρ(x, y)`, the iterates `ψⁿ(0)` form a Cauchy sequence, whose limit is a fixed point; two
fixed points have `ρ = 0`; and `|ψ′(p)| ≤ κ` is the limit of the contraction inequality at `p`.
-/

open Complex Metric Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry.DiscFixedPoint

/-! ## Möbius automorphisms of the unit disc -/

/-- The disc automorphism `u ↦ (u − a)/(1 − āu)`. -/
def mob (a u : ℂ) : ℂ := (u - a) / (1 - conj a * u)

theorem norm_conj_mul_lt_one {a u : ℂ} (ha : ‖a‖ < 1) (hu : ‖u‖ ≤ 1) : ‖conj a * u‖ < 1 := by
  rw [norm_mul, Complex.norm_conj]
  calc ‖a‖ * ‖u‖ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hu (norm_nonneg _)
    _ < 1 := by rw [mul_one]; exact ha

theorem one_sub_conj_mul_ne_zero {a u : ℂ} (ha : ‖a‖ < 1) (hu : ‖u‖ ≤ 1) :
    1 - conj a * u ≠ 0 := by
  intro h
  have h2 := norm_conj_mul_lt_one ha hu
  rw [show conj a * u = 1 by linear_combination -h, norm_one] at h2
  exact lt_irrefl _ h2

/-- `|1 − āu|² − |u − a|² = (1 − |a|²)(1 − |u|²)`. -/
theorem normSq_one_sub_sub_normSq (a u : ℂ) :
    normSq (1 - conj a * u) - normSq (u - a) = (1 - normSq a) * (1 - normSq u) := by
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

theorem norm_mob_lt_one {a u : ℂ} (ha : ‖a‖ < 1) (hu : ‖u‖ < 1) : ‖mob a u‖ < 1 := by
  have hne := one_sub_conj_mul_ne_zero ha hu.le
  unfold mob
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hne)]
  have h := normSq_one_sub_sub_normSq a u
  have ha2 : normSq a < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hu2 : normSq u < 1 := by rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg u]
  have hlt : normSq (u - a) < normSq (1 - conj a * u) := by nlinarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hlt
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt

theorem mob_self (a : ℂ) : mob a a = 0 := by simp [mob]

theorem mob_neg_zero (a : ℂ) : mob (-a) 0 = a := by simp [mob]

theorem mob_neg_mob {a u : ℂ} (ha : ‖a‖ < 1) (hu : ‖u‖ ≤ 1) : mob (-a) (mob a u) = u := by
  have hne := one_sub_conj_mul_ne_zero ha hu
  have ha2 : (1 : ℂ) - conj a * a ≠ 0 := by
    rw [mul_comm, Complex.mul_conj]
    intro h
    have : normSq a = 1 := by exact_mod_cast (sub_eq_zero.mp h).symm
    rw [Complex.normSq_eq_norm_sq] at this
    nlinarith [norm_nonneg a]
  have hne' : 1 - u * conj a ≠ 0 := by rwa [mul_comm]
  unfold mob
  rw [map_neg]
  have hden : (1 : ℂ) - -conj a * ((u - a) / (1 - conj a * u)) =
      (1 - conj a * a) / (1 - conj a * u) := by
    rw [eq_div_iff hne]; field_simp; ring
  have hnum : (u - a) / (1 - conj a * u) - -a = u * (1 - conj a * a) / (1 - conj a * u) := by
    rw [eq_div_iff hne]; field_simp; ring
  rw [hden, hnum, div_div_div_cancel_right₀ hne, mul_div_assoc, div_self ha2, mul_one]

theorem differentiableAt_mob {a u : ℂ} (ha : ‖a‖ < 1) (hu : ‖u‖ ≤ 1) :
    DifferentiableAt ℂ (mob a) u := by
  unfold mob
  exact (differentiableAt_id.sub_const a).div
    ((differentiableAt_const _).sub (differentiableAt_id.const_mul _))
    (one_sub_conj_mul_ne_zero ha hu)

/-! ## Schwarz–Pick -/

/-- **Two-point Schwarz–Pick**: a holomorphic self-map of the unit disc does not increase the
pseudo-hyperbolic distance. -/
theorem norm_mob_le_of_mapsTo {χ : ℂ → ℂ} (hd : DifferentiableOn ℂ χ (ball 0 1))
    (hm : MapsTo χ (ball 0 1) (ball 0 1)) {x y : ℂ} (hx : x ∈ ball 0 1) (hy : y ∈ ball 0 1) :
    ‖mob (χ x) (χ y)‖ ≤ ‖mob x y‖ := by
  have hx' : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  have hy' : ‖y‖ < 1 := mem_ball_zero_iff.mp hy
  have hχx : ‖χ x‖ < 1 := mem_ball_zero_iff.mp (hm hx)
  have hxn : ‖-x‖ < 1 := by rwa [norm_neg]
  have hinv : MapsTo (mob (-x)) (ball 0 1) (ball 0 1) := fun u hu =>
    mem_ball_zero_iff.mpr (norm_mob_lt_one hxn (mem_ball_zero_iff.mp hu))
  set g : ℂ → ℂ := fun u => mob (χ x) (χ (mob (-x) u)) with hg
  have hgd : DifferentiableOn ℂ g (ball 0 1) := by
    intro u hu
    have h1 : DifferentiableAt ℂ (mob (-x)) u :=
      differentiableAt_mob hxn (mem_ball_zero_iff.mp hu).le
    have h2 : DifferentiableAt ℂ χ (mob (-x) u) :=
      hd.differentiableAt (isOpen_ball.mem_nhds (hinv hu))
    have h3 : DifferentiableAt ℂ (mob (χ x)) (χ (mob (-x) u)) :=
      differentiableAt_mob hχx (mem_ball_zero_iff.mp (hm (hinv hu))).le
    exact (h3.comp u (h2.comp u h1)).differentiableWithinAt
  have hgm : MapsTo g (ball 0 1) (closedBall 0 1) := fun u hu =>
    mem_closedBall_zero_iff.mpr (norm_mob_lt_one hχx (mem_ball_zero_iff.mp (hm (hinv hu)))).le
  have hg0 : g 0 = 0 := by simp only [hg, mob_neg_zero, mob_self]
  have h := Complex.norm_le_norm_of_mapsTo_ball hgd hgm hg0 (norm_mob_lt_one hx' hy')
  simp only [hg, mob_neg_mob hx' hy'.le] at h
  exact h

/-- `(1 + t²)|1 − w| ≤ 2|1 − t²w|` for `|w| ≤ 1`, `0 ≤ t ≤ 1`. -/
theorem one_add_sq_mul_norm_le {w : ℂ} (hw : ‖w‖ ≤ 1) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 + t ^ 2) * ‖1 - w‖ ≤ 2 * ‖1 - ((t ^ 2 : ℝ) : ℂ) * w‖ := by
  have hw2 : w.re ^ 2 + w.im ^ 2 ≤ 1 := by
    have h := Complex.sq_norm w
    rw [Complex.normSq_apply] at h
    nlinarith [norm_nonneg w]
  have hre : -1 ≤ w.re := by nlinarith [sq_nonneg w.im, sq_nonneg (w.re + 1)]
  have h1 : ‖1 - w‖ ^ 2 = (1 - w.re) ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  have h2 : ‖1 - ((t ^ 2 : ℝ) : ℂ) * w‖ ^ 2 = (1 - t ^ 2 * w.re) ^ 2 + (t ^ 2 * w.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.one_re, Complex.one_im]
    ring
  have ht2 : 0 ≤ 1 - t ^ 2 := by nlinarith
  have hg : 2 * (1 - t ^ 2) * (1 + w.re) ≤
      (3 + t ^ 2) + 2 * w.re * (1 - t ^ 2) - (w.re ^ 2 + w.im ^ 2) * (1 + 3 * t ^ 2) := by
    have e : (3 + t ^ 2) + 2 * w.re * (1 - t ^ 2) - (w.re ^ 2 + w.im ^ 2) * (1 + 3 * t ^ 2) -
        2 * (1 - t ^ 2) * (1 + w.re) = (1 + 3 * t ^ 2) * (1 - (w.re ^ 2 + w.im ^ 2)) := by ring
    have : 0 ≤ (1 + 3 * t ^ 2) * (1 - (w.re ^ 2 + w.im ^ 2)) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hw2)
    linarith
  have hsq : ((1 + t ^ 2) * ‖1 - w‖) ^ 2 ≤ (2 * ‖1 - ((t ^ 2 : ℝ) : ℂ) * w‖) ^ 2 := by
    rw [mul_pow, mul_pow, h1, h2]
    have e : 2 ^ 2 * ((1 - t ^ 2 * w.re) ^ 2 + (t ^ 2 * w.im) ^ 2) -
        (1 + t ^ 2) ^ 2 * ((1 - w.re) ^ 2 + w.im ^ 2) = (1 - t ^ 2) *
          ((3 + t ^ 2) + 2 * w.re * (1 - t ^ 2) - (w.re ^ 2 + w.im ^ 2) * (1 + 3 * t ^ 2)) := by
      ring
    have h0 : 0 ≤ 2 * (1 - t ^ 2) * (1 + w.re) :=
      mul_nonneg (mul_nonneg (by norm_num) ht2) (by linarith)
    have h3 := mul_nonneg ht2 (le_trans h0 hg)
    linarith
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq

/-- **Scaling contracts the pseudo-hyperbolic distance**: `ρ(ta, tb) ≤ 2t/(1 + t²) ρ(a, b)`. -/
theorem norm_mob_smul_le {a b : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    ‖mob ((t : ℂ) * a) ((t : ℂ) * b)‖ ≤ 2 * t / (1 + t ^ 2) * ‖mob a b‖ := by
  have hne := one_sub_conj_mul_ne_zero ha hb.le
  have hw : ‖conj a * b‖ ≤ 1 := (norm_conj_mul_lt_one ha hb.le).le
  have hkey := one_add_sq_mul_norm_le hw ht0 ht1
  have hden : (1 : ℂ) - conj ((t : ℂ) * a) * ((t : ℂ) * b) = 1 - ((t ^ 2 : ℝ) : ℂ) * (conj a * b) := by
    rw [map_mul, Complex.conj_ofReal]; push_cast; ring
  have hpos : 0 < ‖1 - conj a * b‖ := norm_pos_iff.mpr hne
  unfold mob
  rw [hden, norm_div, norm_div, show (t : ℂ) * b - (t : ℂ) * a = (t : ℂ) * (b - a) by ring,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h]; simp
  have hpos2 : 0 < ‖1 - ((t ^ 2 : ℝ) : ℂ) * (conj a * b)‖ := by
    have : 0 < (1 + t ^ 2) * ‖1 - conj a * b‖ := by positivity
    linarith
  rw [div_le_iff₀ hpos2]
  calc t * ‖b - a‖ = t * ‖b - a‖ / ((1 + t ^ 2) * ‖1 - conj a * b‖) *
        ((1 + t ^ 2) * ‖1 - conj a * b‖) :=
        (div_mul_cancel₀ _ (mul_pos (by positivity) hpos).ne').symm
    _ ≤ t * ‖b - a‖ / ((1 + t ^ 2) * ‖1 - conj a * b‖) *
        (2 * ‖1 - ((t ^ 2 : ℝ) : ℂ) * (conj a * b)‖) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 2 * t / (1 + t ^ 2) * (‖b - a‖ / ‖1 - conj a * b‖) *
        ‖1 - ((t ^ 2 : ℝ) : ℂ) * (conj a * b)‖ := by simp only [div_eq_mul_inv, mul_inv]; ring

/-! ## The contraction and its fixed point -/

/-- The contraction factor `κ(θ) = 2θ'/(1 + θ'²)` with `θ' = (1 + θ)/2`. -/
def contractionFactor (θ : ℝ) : ℝ := 2 * ((1 + θ) / 2) / (1 + ((1 + θ) / 2) ^ 2)

theorem contractionFactor_nonneg {θ : ℝ} (hθ : 0 ≤ θ) : 0 ≤ contractionFactor θ := by
  unfold contractionFactor; positivity

theorem contractionFactor_lt_one {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) : contractionFactor θ < 1 := by
  unfold contractionFactor
  rw [div_lt_one (by positivity)]
  nlinarith

/-- **A map of the disc into `D̄(0, θ)` is a `κ(θ)`-contraction for the pseudo-hyperbolic
distance.** -/
theorem norm_mob_le_contraction {ψ : ℂ → ℂ} {θ : ℝ} (hd : DifferentiableOn ℂ ψ (ball 0 1))
    (hm : MapsTo ψ (ball 0 1) (closedBall 0 θ)) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {x y : ℂ}
    (hx : x ∈ ball 0 1) (hy : y ∈ ball 0 1) :
    ‖mob (ψ x) (ψ y)‖ ≤ contractionFactor θ * ‖mob x y‖ := by
  set θ' : ℝ := (1 + θ) / 2 with hθ'
  have hθ'0 : 0 < θ' := by rw [hθ']; linarith
  have hθ'1 : θ' ≤ 1 := by rw [hθ']; linarith
  have hθθ' : θ < θ' := by rw [hθ']; linarith
  set χ : ℂ → ℂ := fun u => ψ u / (θ' : ℂ) with hχ
  have hχd : DifferentiableOn ℂ χ (ball 0 1) := hd.div_const _
  have hχm : MapsTo χ (ball 0 1) (ball 0 1) := fun u hu => by
    have h := mem_closedBall_zero_iff.mp (hm hu)
    rw [mem_ball_zero_iff, hχ, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hθ'0, div_lt_one hθ'0]
    linarith
  have hθ'C : (θ' : ℂ) ≠ 0 := ofReal_ne_zero.mpr hθ'0.ne'
  have hψ : ∀ u, ψ u = (θ' : ℂ) * χ u := fun u => by
    simp only [hχ]; field_simp
  have hSP := norm_mob_le_of_mapsTo hχd hχm hx hy
  rw [hψ x, hψ y]
  calc ‖mob ((θ' : ℂ) * χ x) ((θ' : ℂ) * χ y)‖ ≤ 2 * θ' / (1 + θ' ^ 2) * ‖mob (χ x) (χ y)‖ :=
        norm_mob_smul_le (mem_ball_zero_iff.mp (hχm hx)) (mem_ball_zero_iff.mp (hχm hy))
          hθ'0.le hθ'1
    _ ≤ 2 * θ' / (1 + θ' ^ 2) * ‖mob x y‖ := mul_le_mul_of_nonneg_left hSP (by positivity)
    _ = contractionFactor θ * ‖mob x y‖ := rfl

/-- `|x − y| ≤ 2ρ(x, y)` on the disc. -/
theorem norm_sub_le_two_mul_norm_mob {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) :
    ‖y - x‖ ≤ 2 * ‖mob x y‖ := by
  have hne := one_sub_conj_mul_ne_zero hx hy.le
  have hle : ‖1 - conj x * y‖ ≤ 2 := by
    calc ‖1 - conj x * y‖ ≤ ‖(1 : ℂ)‖ + ‖conj x * y‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by rw [norm_one]; linarith [norm_conj_mul_lt_one hx hy.le]
      _ = 2 := by norm_num
  unfold mob
  rw [norm_div, mul_div_assoc', le_div_iff₀ (norm_pos_iff.mpr hne)]
  nlinarith [norm_nonneg (y - x)]

theorem eq_of_norm_mob_eq_zero {x y : ℂ} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) (h : ‖mob x y‖ = 0) :
    x = y := by
  have := norm_sub_le_two_mul_norm_mob hx hy
  rw [h, mul_zero] at this
  exact (sub_eq_zero.mp (norm_le_zero_iff.mp this)).symm

/-- **The unit-disc fixed point theorem.** -/
theorem exists_fixedPoint_unit {ψ : ℂ → ℂ} {θ : ℝ} (hd : DifferentiableOn ℂ ψ (ball 0 1))
    (hm : MapsTo ψ (ball 0 1) (closedBall 0 θ)) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ p, ‖p‖ ≤ θ ∧ ψ p = p := by
  set κ := contractionFactor θ with hκ
  have hκ0 := contractionFactor_nonneg hθ0
  have hκ1 := contractionFactor_lt_one hθ0 hθ1
  have hsub : closedBall (0 : ℂ) θ ⊆ ball 0 1 := closedBall_subset_ball hθ1
  set u : ℕ → ℂ := fun n => ψ^[n] 0 with hu
  have hsucc : ∀ n, u (n + 1) = ψ (u n) := fun n => by
    simp only [hu]; rw [Function.iterate_succ_apply']
  have hball : ∀ n, u n ∈ ball 0 1 := by
    intro n
    induction n with
    | zero => simp [hu]
    | succ n ih => rw [hsucc]; exact hsub (hm ih)
  have hθball : ∀ n, u (n + 1) ∈ closedBall 0 θ := fun n => by rw [hsucc]; exact hm (hball n)
  have hstep : ∀ n, ‖mob (u n) (u (n + 1))‖ ≤ κ ^ n * ‖mob (u 0) (u 1)‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h := norm_mob_le_contraction hd hm hθ0 hθ1 (hball n) (hball (n + 1))
      rw [← hsucc, ← hsucc] at h
      calc ‖mob (u (n + 1)) (u (n + 1 + 1))‖ ≤ κ * ‖mob (u n) (u (n + 1))‖ := h
        _ ≤ κ * (κ ^ n * ‖mob (u 0) (u 1)‖) := mul_le_mul_of_nonneg_left ih hκ0
        _ = κ ^ (n + 1) * ‖mob (u 0) (u 1)‖ := by ring
  have hdist : ∀ n, dist (u n) (u (n + 1)) ≤ 2 * ‖mob (u 0) (u 1)‖ * κ ^ n := by
    intro n
    rw [dist_comm, dist_eq_norm]
    refine (norm_sub_le_two_mul_norm_mob (mem_ball_zero_iff.mp (hball n))
      (mem_ball_zero_iff.mp (hball (n + 1)))).trans ?_
    nlinarith [hstep n]
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_le_geometric κ _ hκ1 hdist)
  have hp1 : Tendsto (fun n => u (n + 1)) atTop (𝓝 p) := hp.comp (tendsto_add_atTop_nat 1)
  have hpθ : p ∈ closedBall (0 : ℂ) θ :=
    isClosed_closedBall.mem_of_tendsto hp1 (Eventually.of_forall hθball)
  have hcont : ContinuousAt ψ p :=
    (hd.differentiableAt (isOpen_ball.mem_nhds (hsub hpθ))).continuousAt
  have h1 : Tendsto (fun n => ψ (u n)) atTop (𝓝 (ψ p)) := hcont.tendsto.comp hp
  have h2 : (fun n => ψ (u n)) = fun n => u (n + 1) := funext fun n => (hsucc n).symm
  rw [h2] at h1
  exact ⟨p, mem_closedBall_zero_iff.mp hpθ, tendsto_nhds_unique h1 hp1⟩

/-- **Uniqueness of the fixed point.** -/
theorem fixedPoint_unique_unit {ψ : ℂ → ℂ} {θ : ℝ} (hd : DifferentiableOn ℂ ψ (ball 0 1))
    (hm : MapsTo ψ (ball 0 1) (closedBall 0 θ)) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {p q : ℂ}
    (hp : p ∈ ball 0 1) (hq : q ∈ ball 0 1) (hψp : ψ p = p) (hψq : ψ q = q) : p = q := by
  have h := norm_mob_le_contraction hd hm hθ0 hθ1 hp hq
  rw [hψp, hψq] at h
  have hκ1 := contractionFactor_lt_one hθ0 hθ1
  have h0 : ‖mob p q‖ = 0 := by nlinarith [norm_nonneg (mob p q)]
  exact eq_of_norm_mob_eq_zero (mem_ball_zero_iff.mp hp) (mem_ball_zero_iff.mp hq) h0

/-- **The fixed point is attracting**: `|ψ′(p)| ≤ κ(θ)`. -/
theorem norm_deriv_le_unit {ψ : ℂ → ℂ} {θ : ℝ} (hd : DifferentiableOn ℂ ψ (ball 0 1))
    (hm : MapsTo ψ (ball 0 1) (closedBall 0 θ)) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) {p : ℂ}
    (hp : p ∈ ball 0 1) (hψp : ψ p = p) : ‖deriv ψ p‖ ≤ contractionFactor θ := by
  have hp1 : ‖p‖ < 1 := mem_ball_zero_iff.mp hp
  have hdiff : DifferentiableAt ℂ ψ p := hd.differentiableAt (isOpen_ball.mem_nhds hp)
  have hslope := (hasDerivAt_iff_tendsto_slope.mp hdiff.hasDerivAt).norm
  set q : ℂ → ℝ := fun z => ‖1 - conj p * ψ z‖ / ‖1 - conj p * z‖ with hq
  have hpp : (1 : ℂ) - conj p * p ≠ 0 := one_sub_conj_mul_ne_zero hp1 hp1.le
  have hqc : ContinuousAt q p := by
    refine ContinuousAt.div (continuous_norm.continuousAt.comp ?_)
      (continuous_norm.continuousAt.comp (by fun_prop)) (by rwa [norm_ne_zero_iff])
    exact continuousAt_const.sub (continuousAt_const.mul hdiff.continuousAt)
  have hq1 : q p = 1 := by
    simp only [hq, hψp]; exact div_self (norm_ne_zero_iff.mpr hpp)
  have hqlim : Tendsto q (𝓝[≠] p) (𝓝 1) := by
    rw [← hq1]; exact hqc.tendsto.mono_left nhdsWithin_le_nhds
  have hbound : ∀ᶠ z in 𝓝[≠] p, ‖slope ψ p z‖ ≤ contractionFactor θ * q z := by
    have hball : ∀ᶠ z in 𝓝[≠] p, z ∈ ball (0 : ℂ) 1 :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds hp)
    filter_upwards [hball, self_mem_nhdsWithin] with z hz hzp
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    have hψz : ‖ψ z‖ < 1 :=
      lt_of_le_of_lt (mem_closedBall_zero_iff.mp (hm hz)) hθ1
    have hc := norm_mob_le_contraction hd hm hθ0 hθ1 hp hz
    rw [hψp] at hc
    have hzne : z - p ≠ 0 := sub_ne_zero.mpr hzp
    have hd1 := one_sub_conj_mul_ne_zero hp1 hψz.le
    have hd2 := one_sub_conj_mul_ne_zero hp1 hz1.le
    unfold mob at hc
    rw [norm_div, norm_div, div_le_iff₀ (norm_pos_iff.mpr hd1)] at hc
    rw [slope_def_field, hψp, norm_div, div_le_iff₀ (norm_pos_iff.mpr hzne), hq]
    calc ‖ψ z - p‖ ≤ contractionFactor θ * (‖z - p‖ / ‖1 - conj p * z‖) *
          ‖1 - conj p * ψ z‖ := hc
      _ = contractionFactor θ * (‖1 - conj p * ψ z‖ / ‖1 - conj p * z‖) * ‖z - p‖ := by ring
  have hlim := hqlim.const_mul (contractionFactor θ)
  rw [mul_one] at hlim
  exact le_of_tendsto_of_tendsto hslope hlim hbound

/-! ## The rescaled statement -/

/-- **The disc fixed point theorem.**  A holomorphic map of `D(c, R)` into `D̄(c, θR)`, `θ < 1`, has a
unique fixed point in `D(c, R)`; it lies in `D̄(c, θR)` and `|ψ′(p)| ≤ κ(θ) < 1`. -/
theorem exists_unique_fixedPoint {ψ : ℂ → ℂ} {c : ℂ} {R θ : ℝ} (hR : 0 < R) (hθ0 : 0 ≤ θ)
    (hθ1 : θ < 1) (hd : DifferentiableOn ℂ ψ (ball c R))
    (hm : MapsTo ψ (ball c R) (closedBall c (θ * R))) :
    ∃ p, p ∈ closedBall c (θ * R) ∧ ψ p = p ∧ (∀ q ∈ ball c R, ψ q = q → q = p) ∧
      ‖deriv ψ p‖ ≤ contractionFactor θ := by
  have hR' : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR.ne'
  set A : ℂ → ℂ := fun u => c + (R : ℂ) * u with hA
  set B : ℂ → ℂ := fun z => (z - c) / (R : ℂ) with hB
  have hBA : ∀ u, B (A u) = u := fun u => by simp only [hA, hB]; field_simp; ring
  have hAB : ∀ z, A (B z) = z := fun z => by simp only [hA, hB]; field_simp; ring
  have hAball : ∀ u, u ∈ ball (0 : ℂ) 1 ↔ A u ∈ ball c R := fun u => by
    simp only [mem_ball, dist_eq_norm, sub_zero, hA, add_sub_cancel_left, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    rw [mul_lt_iff_lt_one_right hR]
  have hBnorm : ∀ z, ‖B z‖ = ‖z - c‖ / R := fun z => by
    simp only [hB, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  set ψ' : ℂ → ℂ := fun u => B (ψ (A u)) with hψ'
  have hAd : ∀ u, HasDerivAt A (R : ℂ) u := fun u => by
    have h := ((hasDerivAt_id u).const_mul (R : ℂ)).const_add c
    rw [mul_one] at h
    exact h
  have hd' : DifferentiableOn ℂ ψ' (ball 0 1) := by
    intro u hu
    have h1 : DifferentiableAt ℂ ψ (A u) :=
      hd.differentiableAt (isOpen_ball.mem_nhds ((hAball u).mp hu))
    have h2 : DifferentiableAt ℂ (fun u => ψ (A u)) u := h1.comp u (hAd u).differentiableAt
    exact ((h2.sub_const c).div_const _).differentiableWithinAt
  have hm' : MapsTo ψ' (ball 0 1) (closedBall 0 θ) := fun u hu => by
    have h := hm ((hAball u).mp hu)
    rw [mem_closedBall, dist_eq_norm] at h
    rw [mem_closedBall_zero_iff, hψ', hBnorm, div_le_iff₀ hR]
    exact h
  obtain ⟨p', hp'θ, hp'⟩ := exists_fixedPoint_unit hd' hm' hθ0 hθ1
  have hp'ball : p' ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (lt_of_le_of_lt hp'θ hθ1)
  have hfix : ψ (A p') = A p' := by
    have h := congrArg A hp'
    simp only [hψ', hAB] at h
    exact h
  refine ⟨A p', ?_, hfix, fun q hq hψq => ?_, ?_⟩
  · rw [mem_closedBall, dist_eq_norm]
    simp only [hA, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR]
    nlinarith
  · have hqball : B q ∈ ball (0 : ℂ) 1 := by rw [hAball, hAB]; exact hq
    have hψ'q : ψ' (B q) = B q := by simp only [hψ', hAB, hψq]
    have := fixedPoint_unique_unit hd' hm' hθ0 hθ1 hqball hp'ball hψ'q hp'
    rw [← hAB q, this]
  · have hder := norm_deriv_le_unit hd' hm' hθ0 hθ1 hp'ball hp'
    have h1 : HasDerivAt ψ (deriv ψ (A p')) (A p') :=
      (hd.differentiableAt (isOpen_ball.mem_nhds ((hAball p').mp hp'ball))).hasDerivAt
    have h2 : HasDerivAt ψ' (deriv ψ (A p') * R / R) p' := by
      have := ((h1.comp p' (hAd p')).sub_const c).div_const (R : ℂ)
      simpa [hψ', hB] using this
    rw [h2.deriv, mul_div_assoc, div_self hR', mul_one] at hder
    exact hder

end GaloisForLFunctions.HTGeometry.DiscFixedPoint

end
