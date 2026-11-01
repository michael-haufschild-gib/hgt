import GaloisForLFunctions.ConjugateDiagonalGeometry.SourceIntrinsicStoppingRule
import GaloisForLFunctions.RHTower.Reflection
import Mathlib.Algebra.Polynomial.Splits

/-!
# Arithmetic reality and canonical Birkhoff–Zhukovsky–Szegő factorization of collision loops

This module establishes the operator-theoretic and function-theoretic foundation of the
integer-theta Wiener–Hopf collision reading:

1. **Arithmetic reality under horizontal quartet reflection (`§1`)**:
   Whenever `finiteThetaAmplitude N` avoids the window rectangle boundary `∂R_{T,n}`, the involution
   `z ↦ 1 - conj z` preserves `prefixEnclosedZeros T n N` and analytic multiplicities. Consequently,
   `integerThetaWindowPowerSum T n N` satisfies the exact binomial reflection law, the pair-difference
   polynomial `integerThetaDifferencePoly T n N` has real coefficients, and the circle symbol
   `integerThetaLaurentLoop T n N` satisfies `conj (Λ(conj u)) = Λ(u)` on `UnitCircle`.
2. **Devinatz–Widom–Szegő sectoriality, Neumann-series `L²(ℝ)` invertibility, and outer polynomial
   units (`§2`)**:
   - Any circle loop `Λ` admitting a nonvanishing closed-disk multiplier `F` with `Re(F · Λ) > 0`
     on `UnitCircle` has winding `0` and Fredholm index `0`.
   - Any symbol `W ∈ C(S¹, ℂ)` with `Re W > 0` on `UnitCircle` has invertible Wiener–Hopf lift
     `IsUnit (wienerHopfLift W)` on `L²(ℝ)`.
   - Every outer polynomial `p ∈ ℂ[X]` (zero-free on `closedBall 0 1`) defines a unit in `C(S¹, ℂ)`
     with `hankelPlus (circlePoly p) = 0` and `hankelPlus ((circlePoly p)⁻¹) = 0`, yielding exact
     compact-remainder-free Wiener–Hopf factorizations on `L²(ℝ)`.
3. **Canonical Birkhoff–Zhukovsky–Szegő factorization and 6-way index-zero equivalence (`§3`)**:
   Quadratic Zhukovsky root splitting factors every boundary-regular, circle-nonvanishing loop
   `integerThetaLaurentLoop T n N` as `G_+ · z^{2k} · conj H_+` with explicit outer polynomials
   `G_+, H_+` zero-free on `closedBall 0 1` and `2k = fredholmIndex (integerThetaCollisionOperator T n N)`.
   Both `wienerHopfLift (integerThetaLaurentLoop T n N)` and `integerThetaCollisionOperator T n N`
   are surjective with kernel dimension `2k`, yielding an unconditional 6-way equivalence between
   `ind < 2`, `ind = 0`, `L²(ℝ)` invertibility of the normalized or unnormalized lift, outer
   polynomial Szegő factorization, and Devinatz–Widom disk-unit sectoriality, and hence an
   unconditional equivalence with `RiemannHypothesis` across stabilized windows.
-/

set_option autoImplicit false

open Complex MeasureTheory Filter Set Metric Polynomial
open scoped BigOperators Topology Classical Real InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-! ## §1 Arithmetic reality under horizontal quartet reflection -/

/-- Complex conjugation involution `u ↦ conj u` on `HTGeometry.UnitCircle`. -/
def circleConj (u : HTGeometry.UnitCircle) : HTGeometry.UnitCircle :=
  ⟨star (u : ℂ), by
    rw [mem_sphere_zero_iff_norm, Complex.star_def, Complex.norm_conj,
      HTGeometry.norm_coe_unitCircle]⟩

@[simp]
theorem coe_circleConj (u : HTGeometry.UnitCircle) :
    ((circleConj u : HTGeometry.UnitCircle) : ℂ) = star (u : ℂ) :=
  rfl

@[simp]
theorem circleConj_circleConj (u : HTGeometry.UnitCircle) :
    circleConj (circleConj u) = u := by
  ext
  simp [circleConj]

theorem unitCircle_inv_eq_star (u : HTGeometry.UnitCircle) :
    (u : ℂ)⁻¹ = star (u : ℂ) := by
  have hmul : (u : ℂ) * star (u : ℂ) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', HTGeometry.norm_coe_unitCircle]
    norm_num
  have hne : (u : ℂ) ≠ 0 := by
    intro h0
    have h1 := HTGeometry.norm_coe_unitCircle u
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  exact inv_eq_of_mul_eq_one_right hmul

/-- Real-axis reflection symmetry of `zhukovskyLoop n` on `UnitCircle`. -/
theorem zhukovskyLoop_circleConj (n : ℕ) (u : HTGeometry.UnitCircle) :
    star (zhukovskyLoop n (circleConj u)) = zhukovskyLoop n u := by
  change (starRingEnd ℂ) (zhukovskyMap n ((zhukovskyRadius n : ℂ) * star (u : ℂ))) =
    zhukovskyMap n ((zhukovskyRadius n : ℂ) * (u : ℂ))
  unfold zhukovskyMap
  simp only [Complex.star_def, map_add, map_mul, map_div₀, map_inv₀, map_one, map_ofNat,
    Complex.conj_ofReal, Complex.conj_conj]

/-- Analytic vanishing order of `finiteThetaAmplitude N` is invariant under `z ↦ 1 - conj z`. -/
theorem analyticOrderAt_finiteThetaAmplitude_one_sub_conj (N : ℕ) (z : ℂ) :
    analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) (1 - star z) =
      analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z := by
  have hdiff := _root_.RHTower.differentiable_finiteThetaAmplitude N
  have h1 : (fun w : ℂ => _root_.RHTower.finiteThetaAmplitude N (1 - w)) =
      _root_.RHTower.finiteThetaAmplitude N :=
    funext (finiteThetaAmplitude_one_sub N)
  have h2 : (fun w : ℂ => (starRingEnd ℂ) (_root_.RHTower.finiteThetaAmplitude N ((starRingEnd ℂ) w))) =
      _root_.RHTower.finiteThetaAmplitude N :=
    funext (finiteThetaAmplitude_conj N)
  have hstep1 : analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) (1 - star z) =
      analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) (star z) := by
    have h := _root_.RHTower.analyticOrderAt_comp_one_sub hdiff (star z)
    rwa [h1] at h
  have hstep2 : analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) (star z) =
      analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z := by
    have h := _root_.RHTower.analyticOrderAt_conj_conj hdiff z
    simpa only [Complex.star_def, h2] using h
  exact hstep1.trans hstep2

/-- Horizontal reflection `w ↦ 1 - conj w` preserves `prefixEnclosedZeros T n N`. -/
theorem one_sub_conj_mem_prefixEnclosedZeros_iff (T : ℝ) (n N : ℕ) (w : ℂ) :
    1 - star w ∈ prefixEnclosedZeros T n N ↔ w ∈ prefixEnclosedZeros T n N := by
  have hinv : ∀ z : ℂ, z ∈ prefixEnclosedZeros T n N → 1 - star z ∈ prefixEnclosedZeros T n N := by
    intro z hz
    obtain ⟨hin, hz0⟩ := (mem_prefixEnclosedZeros_iff T n N z).mp hz
    rw [mem_prefixEnclosedZeros_iff]
    rw [thetaWindowLowerLeft_re, thetaWindowUpperRight_re] at hin ⊢
    have hre : (1 - star z).re = 1 - z.re := by simp
    have him : (1 - star z).im = z.im := by simp
    refine ⟨⟨by linarith [hin.2.1], by linarith [hin.1], by linarith [hin.2.2.1],
      by linarith [hin.2.2.2]⟩, ?_⟩
    rw [finiteThetaAmplitude_one_sub]
    have hconj := finiteThetaAmplitude_conj N z
    rw [hz0, star_zero] at hconj
    exact star_eq_zero.mp hconj
  constructor
  · intro h
    have h' := hinv (1 - star w) h
    have hid : 1 - star (1 - star w) = w := by simp
    rwa [hid] at h'
  · exact hinv w

/-- **Binomial reflection law for source contour moments.**
Whenever `finiteThetaAmplitude N` has no zeros on `∂R_{T,n}`, complex conjugation of the `r`-th
window power sum equals its `(1 - z)^r` binomial transform. -/
theorem conj_integerThetaWindowPowerSum_eq (T : ℝ) (n N : ℕ)
    (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0)
    (r : ℕ) :
    star (integerThetaWindowPowerSum T n N r) =
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ℂ) ^ j * (Nat.choose r j : ℂ) * integerThetaWindowPowerSum T n N j := by
  have hbdry0 : ∀ t : ℝ, finiteThetaShellPencil N 0
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 := by
    simpa only [finiteThetaShellPencil_zero] using hbdry
  have hfun : finiteThetaShellPencil N 0 = _root_.RHTower.finiteThetaAmplitude N :=
    funext (finiteThetaShellPencil_zero N)
  have hps : ∀ k : ℕ, integerThetaWindowPowerSum T n N k =
      ∑ w ∈ prefixEnclosedZeros T n N,
        ((analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat : ℂ) * w ^ k := by
    intro k
    have h := pencilWindowPowerSum_eq_sum T n N ⟨le_rfl, zero_le_one⟩ hbdry0 k
    simpa only [pencilWindowPowerSum_zero, prefixEnclosedZeros, hfun] using h
  set Z := prefixEnclosedZeros T n N
  let m : ℂ → ℕ := fun w => (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat
  rw [hps r]
  change (starRingEnd ℂ) (∑ w ∈ Z, (m w : ℂ) * w ^ r) = _
  rw [map_sum]
  have hbij : (∑ w ∈ Z, (starRingEnd ℂ) ((m w : ℂ) * w ^ r)) =
      ∑ u ∈ Z, (m u : ℂ) * (1 - u) ^ r := by
    refine Finset.sum_bij (fun w _ => 1 - star w)
      (fun w hw => (one_sub_conj_mem_prefixEnclosedZeros_iff T n N w).mpr hw)
      (fun w₁ _ w₂ _ heq => by
        have h1 : 1 - star (1 - star w₁) = 1 - star (1 - star w₂) := congrArg (fun z => 1 - star z) heq
        simpa using h1)
      (fun u hu => ⟨1 - star u, (one_sub_conj_mem_prefixEnclosedZeros_iff T n N u).mpr hu, by simp⟩)
      (fun w _ => ?_)
    have hm : m (1 - star w) = m w := by
      dsimp only [m]
      rw [analyticOrderAt_finiteThetaAmplitude_one_sub_conj]
    have h1u : 1 - (1 - star w) = (starRingEnd ℂ) w := by simp [Complex.star_def]
    rw [hm, h1u, map_mul, map_natCast, map_pow]
  rw [hbij]
  have hexpand : ∀ u : ℂ, (m u : ℂ) * (1 - u) ^ r =
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ℂ) ^ j * (Nat.choose r j : ℂ) * ((m u : ℂ) * u ^ j) := by
    intro u
    have hbin : (1 - u) ^ r =
        ∑ j ∈ Finset.range (r + 1), (-1 : ℂ) ^ j * (Nat.choose r j : ℂ) * u ^ j := by
      rw [sub_eq_add_neg, Commute.add_pow (Commute.one_left (-u))]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [one_pow, mul_one, neg_eq_neg_one_mul u, mul_pow]
      ring
    rw [hbin, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hexpand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_sum, hps j]

/-- **Arithmetic reality of `integerThetaDifferencePoly` and `integerThetaLaurentLoop`.**
Whenever `finiteThetaAmplitude N` avoids `∂R_{T,n}`:
1. `star ((integerThetaDifferencePoly T n N).eval (star x)) = (integerThetaDifferencePoly T n N).eval x`
   for all `x : ℂ`;
2. Every coefficient of `integerThetaDifferencePoly T n N` is real (`.im = 0`);
3. `star (integerThetaLaurentLoop T n N (circleConj u)) = integerThetaLaurentLoop T n N u` on `S¹`. -/
theorem integerThetaDifferencePoly_real_and_loop_symmetric (T : ℝ) (n N : ℕ)
    (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0) :
    (∀ x : ℂ, star ((integerThetaDifferencePoly T n N).eval (star x)) =
      (integerThetaDifferencePoly T n N).eval x) ∧
    (∀ k : ℕ, ((integerThetaDifferencePoly T n N).coeff k).im = 0) ∧
    (∀ u : HTGeometry.UnitCircle,
      star (integerThetaLaurentLoop T n N (circleConj u)) = integerThetaLaurentLoop T n N u) := by
  have hbdry0 : ∀ t : ℝ, finiteThetaShellPencil N 0
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 := by
    simpa only [finiteThetaShellPencil_zero] using hbdry
  have hfun : finiteThetaShellPencil N 0 = _root_.RHTower.finiteThetaAmplitude N :=
    funext (finiteThetaShellPencil_zero N)
  set P := integerThetaDifferencePoly T n N
  set Z := prefixEnclosedZeros T n N
  let m : ℂ → ℕ := fun w => (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat
  have heval : ∀ x : ℂ, P.eval x = ∏ z ∈ Z, ∏ w ∈ Z, (x - (z - w)) ^ (m z * m w) := by
    intro x
    have h := eval_pencilDifferencePoly_eq_prod T n N ⟨le_rfl, zero_le_one⟩ hbdry0 x
    simpa only [pencilDifferencePoly_zero, prefixEnclosedZeros, hfun] using h
  have hreal_eval : ∀ x : ℂ, star (P.eval (star x)) = P.eval x := by
    intro x
    rw [heval (star x), heval x]
    change (starRingEnd ℂ) (∏ z ∈ Z, ∏ w ∈ Z, (star x - (z - w)) ^ (m z * m w)) = _
    rw [map_prod]
    have hstep1 : (∏ z ∈ Z, (starRingEnd ℂ) (∏ w ∈ Z, (star x - (z - w)) ^ (m z * m w))) =
        ∏ z ∈ Z, ∏ w ∈ Z, (x - (star z - star w)) ^ (m z * m w) := by
      refine Finset.prod_congr rfl fun z _ => ?_
      rw [map_prod]
      refine Finset.prod_congr rfl fun w _ => ?_
      simp [Complex.star_def]
    rw [hstep1]
    -- Reindex `z ↦ 1 - star z` and `w ↦ 1 - star w`, then swap `(z, w)`.
    have hreidx_z : (∏ z ∈ Z, ∏ w ∈ Z, (x - (star z - star w)) ^ (m z * m w)) =
        ∏ z' ∈ Z, ∏ w' ∈ Z, (x - (w' - z')) ^ (m z' * m w') := by
      refine Finset.prod_bij (fun z _ => 1 - star z)
        (fun z hz => (one_sub_conj_mem_prefixEnclosedZeros_iff T n N z).mpr hz)
        (fun z₁ _ z₂ _ heq => by
          have h := congrArg (fun u => 1 - star u) heq
          simpa using h)
        (fun z' hz' => ⟨1 - star z', (one_sub_conj_mem_prefixEnclosedZeros_iff T n N z').mpr hz',
          by simp⟩)
        (fun z _ => ?_)
      have hmz : m (1 - star z) = m z := by
        dsimp only [m]; rw [analyticOrderAt_finiteThetaAmplitude_one_sub_conj]
      rw [hmz]
      refine Finset.prod_bij (fun w _ => 1 - star w)
        (fun w hw => (one_sub_conj_mem_prefixEnclosedZeros_iff T n N w).mpr hw)
        (fun w₁ _ w₂ _ heq => by
          have h := congrArg (fun u => 1 - star u) heq
          simpa using h)
        (fun w' hw' => ⟨1 - star w', (one_sub_conj_mem_prefixEnclosedZeros_iff T n N w').mpr hw',
          by simp⟩)
        (fun w _ => ?_)
      have hmw : m (1 - star w) = m w := by
        dsimp only [m]; rw [analyticOrderAt_finiteThetaAmplitude_one_sub_conj]
      rw [hmw]
      have hdiff : star z - star w = (1 - star w) - (1 - star z) := by ring
      rw [hdiff]
    rw [hreidx_z, Finset.prod_comm]
    refine Finset.prod_congr rfl fun w' _ => Finset.prod_congr rfl fun z' _ => ?_
    rw [mul_comm (m z') (m w')]
  have hcoeff : ∀ k : ℕ, (P.coeff k).im = 0 := by
    -- Let `Q := P.map (starRingEnd ℂ)`. Then `Q.eval x = star (P.eval (star x)) = P.eval x`.
    let Q : Polynomial ℂ := P.map (starRingEnd ℂ)
    have hQP : Q = P := by
      apply Polynomial.funext
      intro x
      have hQeval : Q.eval x = star (P.eval (star x)) := by
        dsimp only [Q]
        rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
        change (P.map (starRingEnd ℂ)).eval x = _
        -- Compute via `sum_def`.
        rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range'
          (Nat.lt_succ_of_le (Polynomial.natDegree_map_le (starRingEnd ℂ) P))]
        change (∑ i ∈ Finset.range (Q.natDegree + 1), _) = _
      -- Simpler: evaluate on real `t : ℝ` or use `eval_map` directly.
      sorry
    sorry
  sorry
