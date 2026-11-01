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
    rw [hz0] at hconj
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
        have h1 := congrArg (fun z => 1 - star z) heq
        simpa using h1)
      (fun u hu => ⟨1 - star u, (one_sub_conj_mem_prefixEnclosedZeros_iff T n N u).mpr hu, by simp⟩)
      (fun w _ => ?_)
    have hm : m (1 - star w) = m w := by
      dsimp only [m]
      rw [analyticOrderAt_finiteThetaAmplitude_one_sub_conj]
    have h1u : 1 - (1 - star w) = (starRingEnd ℂ) w := by simp
    rw [hm, h1u, map_mul, map_natCast, map_pow]
  rw [hbij]
  have hexpand : ∀ u : ℂ, (m u : ℂ) * (1 - u) ^ r =
      ∑ j ∈ Finset.range (r + 1),
        (-1 : ℂ) ^ j * (Nat.choose r j : ℂ) * ((m u : ℂ) * u ^ j) := by
    intro u
    have hbin : (1 - u) ^ r =
        ∑ j ∈ Finset.range (r + 1), (-1 : ℂ) ^ j * (Nat.choose r j : ℂ) * u ^ j := by
      rw [show (1 : ℂ) - u = -u + 1 by ring, Commute.add_pow (Commute.one_right (-u))]
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
    dsimp only [P, Z, m, prefixEnclosedZeros]
    have h := eval_pencilDifferencePoly_eq_prod T n N ⟨le_rfl, zero_le_one⟩ hbdry0 x
    simpa only [pencilDifferencePoly_zero, hfun] using h
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
      simp
    rw [hstep1]
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
    let Q : Polynomial ℂ := P.map (starRingEnd ℂ)
    have hQP : Q = P := by
      haveI : Infinite ℂ := Infinite.of_injective (fun j : ℕ => (j : ℂ)) Nat.cast_injective
      apply Polynomial.funext
      intro x
      set D := max Q.natDegree P.natDegree + 1
      have hQsum := Polynomial.eval_eq_sum_range' (p := Q) (n := D)
        (Nat.lt_succ_of_le (le_max_left _ _)) x
      have hPsum := Polynomial.eval_eq_sum_range' (p := P) (n := D)
        (Nat.lt_succ_of_le (le_max_right _ _)) (star x)
      have hQeval : Q.eval x = star (P.eval (star x)) := by
        rw [hQsum, hPsum]
        change _ = (starRingEnd ℂ) (∑ i ∈ Finset.range D, P.coeff i * (star x) ^ i)
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        dsimp only [Q]
        rw [Polynomial.coeff_map, map_mul, map_pow]
        simp
      rw [hQeval, hreal_eval]
    intro k
    have hk : (starRingEnd ℂ) (P.coeff k) = P.coeff k := by
      rw [← Polynomial.coeff_map (starRingEnd ℂ) k, show P.map (starRingEnd ℂ) = P from hQP]
    exact Complex.conj_eq_iff_im.mp hk
  have hloop : ∀ u : HTGeometry.UnitCircle,
      star (integerThetaLaurentLoop T n N (circleConj u)) = integerThetaLaurentLoop T n N u := by
    intro u
    rw [integerThetaLaurentLoop_apply, integerThetaLaurentLoop_apply, star_pow]
    congr 1
    have hzhuk : zhukovskyLoop n (circleConj u) = star (zhukovskyLoop n u) := by
      have h := congrArg star (zhukovskyLoop_circleConj n u)
      simpa using h
    rw [hzhuk, hreal_eval]
  exact ⟨hreal_eval, hcoeff, hloop⟩

/-! ## §2 Devinatz–Widom–Szegő sectoriality, Neumann-series invertibility, and outer polynomials -/

/-- A closed-disk unit `F` is continuous and nonvanishing on `closedBall 0 1`. -/
def IsDiskUnit (F : ℂ → ℂ) : Prop :=
  ContinuousOn F (Metric.closedBall (0 : ℂ) 1) ∧
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, F z ≠ 0

/-- An outer polynomial `p ∈ ℂ[X]` is everywhere nonvanishing on the closed unit disk. -/
def IsOuterPolynomial (p : Polynomial ℂ) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ 1 → p.eval z ≠ 0

/-- Restriction of a polynomial `p ∈ ℂ[X]` to `UnitCircle`. -/
def circlePoly (p : Polynomial ℂ) : C(HTGeometry.UnitCircle, ℂ) where
  toFun u := p.eval (u : ℂ)
  continuous_toFun := p.continuous.comp continuous_subtype_val

@[simp]
theorem circlePoly_apply (p : Polynomial ℂ) (u : HTGeometry.UnitCircle) :
    circlePoly p u = p.eval (u : ℂ) :=
  rfl

@[simp]
theorem circlePoly_one : circlePoly 1 = 1 := by
  ext u
  simp [circlePoly]

@[simp]
theorem circlePoly_mul (p q : Polynomial ℂ) :
    circlePoly (p * q) = circlePoly p * circlePoly q := by
  ext u
  simp [circlePoly]

@[simp]
theorem circlePoly_pow (p : Polynomial ℂ) (m : ℕ) :
    circlePoly (p ^ m) = circlePoly p ^ m := by
  ext u
  simp [circlePoly]

theorem isOuterPolynomial_one : IsOuterPolynomial 1 := by
  intro _ _
  simp

theorem isOuterPolynomial_mul {p q : Polynomial ℂ}
    (hp : IsOuterPolynomial p) (hq : IsOuterPolynomial q) :
    IsOuterPolynomial (p * q) := by
  intro z hz
  rw [Polynomial.eval_mul]
  exact mul_ne_zero (hp z hz) (hq z hz)

theorem isOuterPolynomial_pow {p : Polynomial ℂ} (hp : IsOuterPolynomial p) (m : ℕ) :
    IsOuterPolynomial (p ^ m) := by
  intro z hz
  rw [Polynomial.eval_pow]
  exact pow_ne_zero m (hp z hz)

private lemma windingNumber_eq_zero_of_re_pos {γ : ℝ → ℂ} {a b : ℝ}
    (hγc : Continuous γ) (hclosed : γ a = γ b) (hre : ∀ t : ℝ, 0 < (γ t).re) :
    _root_.RHTower.windingNumber γ a b = 0 := by
  have hslit : ∀ t, γ t ∈ Complex.slitPlane :=
    fun t => Complex.mem_slitPlane_iff.mpr (Or.inl (hre t))
  have hnz : ∀ t, γ t ≠ 0 := fun t => Complex.slitPlane_ne_zero (hslit t)
  have hL : _root_.RHTower.IsLoop γ a b := ⟨hγc, hnz, hclosed⟩
  have hlogc : Continuous (fun t => Complex.log (γ t)) := hγc.clog hslit
  have hloge : ∀ t, Complex.exp (Complex.log (γ t)) = γ t := fun t => Complex.exp_log (hnz t)
  rw [_root_.RHTower.windingNumber_eq_zero_iff hL hlogc hloge, hclosed]

private lemma windingNumber_diskUnit_eq_zero {F : ℂ → ℂ} (hF : IsDiskUnit F) :
    _root_.RHTower.windingNumber
      (fun θ => F (HTGeometry.circleExp θ : ℂ)) 0 (2 * Real.pi) = 0 := by
  let c01 : ℝ → ℝ := fun σ => max 0 (min 1 σ)
  have hc01_cont : Continuous c01 := continuous_const.max (continuous_const.min continuous_id)
  let g : ℝ × ℝ → ℂ := fun p => ((c01 p.1 : ℝ) : ℂ) * (HTGeometry.circleExp p.2 : ℂ)
  have hg_cont : Continuous g :=
    (Complex.continuous_ofReal.comp (hc01_cont.comp continuous_fst)).mul
      (continuous_subtype_val.comp (HTGeometry.continuous_circleExp.comp continuous_snd))
  have hg_mem : ∀ p : ℝ × ℝ, g p ∈ Metric.closedBall (0 : ℂ) 1 := by
    intro p
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp only [g]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      HTGeometry.norm_coe_unitCircle, mul_one,
      abs_of_nonneg (le_max_left 0 _)]
    exact max_le zero_le_one (min_le_left 1 p.1)
  let H : ℝ → ℝ → ℂ := fun σ θ => F (g (σ, θ))
  have hHc : Continuous (fun p : ℝ × ℝ => H p.1 p.2) :=
    hF.1.comp_continuous hg_cont hg_mem
  have hH0 : ∀ σ θ, H σ θ ≠ 0 := fun σ θ => hF.2 _ (hg_mem (σ, θ))
  have hHloop : ∀ σ, H σ 0 = H σ (2 * Real.pi) := by
    intro σ
    dsimp only [H, g]
    rw [← HTGeometry.circleExp_add_two_pi 0, zero_add]
  have h0 : ∀ θ, H 0 θ = F 0 := by
    intro θ
    dsimp only [H, g, c01]
    simp
  have h1 : ∀ θ, H 1 θ = F (HTGeometry.circleExp θ : ℂ) := by
    intro θ
    dsimp only [H, g, c01]
    simp
  rw [← _root_.RHTower.windingNumber_of_homotopic H hHc hH0 hHloop h0 h1]
  exact _root_.RHTower.windingNumber_const
    (hF.2 0 (Metric.mem_closedBall_self zero_le_one)) 0 (2 * Real.pi)

/-- **Universal Devinatz–Widom–Szegő index-zero theorem.**
If `F` is continuous and nonvanishing on `closedBall 0 1` (`IsDiskUnit F`) and `Re(F · Λ) > 0`
everywhere on `UnitCircle`, then `Λ` is nonvanishing on `UnitCircle` and its unit-normalized
Wiener–Hopf operator has Fredholm index `0` (`< 2`). -/
theorem fredholmIndex_eq_zero_of_diskUnit_re_pos (Λ : C(HTGeometry.UnitCircle, ℂ))
    {F : ℂ → ℂ} (hF : IsDiskUnit F)
    (hpos : ∀ u : HTGeometry.UnitCircle, 0 < (F (u : ℂ) * Λ u).re) :
    (∀ u : HTGeometry.UnitCircle, Λ u ≠ 0) ∧
      HTGeometry.fredholmIndex (HTGeometry.wienerHopfLift (unitNormalizeSymbol Λ)) = 0 := by
  have hΛ_nz : ∀ u : HTGeometry.UnitCircle, Λ u ≠ 0 := by
    intro u h0
    have h := hpos u
    rw [h0, mul_zero, Complex.zero_re] at h
    exact lt_irrefl 0 h
  refine ⟨hΛ_nz, ?_⟩
  rw [fredholmIndex_wienerHopfLift_unitNormalizeSymbol,
    circleWinding_unitNormalizeSymbol_of_ne_zero hΛ_nz]
  have hFu_cont : Continuous (fun u : HTGeometry.UnitCircle => F (u : ℂ)) :=
    hF.1.comp_continuous continuous_subtype_val fun u => by
      rw [Metric.mem_closedBall, dist_zero_right, HTGeometry.norm_coe_unitCircle]
  have hF_loop : _root_.RHTower.IsLoop
      (fun θ => F (HTGeometry.circleExp θ : ℂ)) 0 (2 * Real.pi) :=
    ⟨hFu_cont.comp HTGeometry.continuous_circleExp,
      fun θ => hF.2 _ (by
        rw [Metric.mem_closedBall, dist_zero_right, HTGeometry.norm_coe_unitCircle]),
      by rw [← HTGeometry.circleExp_add_two_pi 0, zero_add]⟩
  have hΛ_loop : _root_.RHTower.IsLoop
      (fun θ => Λ (HTGeometry.circleExp θ)) 0 (2 * Real.pi) :=
    HTGeometry.isLoop_circleSymbol hΛ_nz
  have hprod_zero : _root_.RHTower.windingNumber
      (fun θ => F (HTGeometry.circleExp θ : ℂ) * Λ (HTGeometry.circleExp θ)) 0 (2 * Real.pi) = 0 :=
    windingNumber_eq_zero_of_re_pos
      (hF_loop.continuous.mul hΛ_loop.continuous)
      (by simp only [hF_loop.closed, hΛ_loop.closed])
      (fun θ => hpos (HTGeometry.circleExp θ))
  have hmul := _root_.RHTower.windingNumber_mul hF_loop hΛ_loop
  rw [hprod_zero, windingNumber_diskUnit_eq_zero hF, zero_add] at hmul
  exact hmul.symm

/-- **Universal Neumann-series `L²(ℝ)` invertibility of strictly sectorial Wiener–Hopf lifts.**
If `W ∈ C(UnitCircle, ℂ)` satisfies `0 < (W u).re` for all `u : UnitCircle`, then
`wienerHopfLift W` is an invertible bounded linear operator (`IsUnit`) on `L²(ℝ)`. -/
theorem isUnit_wienerHopfLift_of_re_pos (W : C(HTGeometry.UnitCircle, ℂ))
    (hW : ∀ u : HTGeometry.UnitCircle, 0 < (W u).re) :
    IsUnit (HTGeometry.wienerHopfLift W) := by
  have hU_ne : (Set.univ : Set HTGeometry.UnitCircle).Nonempty :=
    ⟨HTGeometry.circleExp 0, Set.mem_univ _⟩
  have hre_cont : Continuous (fun u : HTGeometry.UnitCircle => (W u).re) :=
    Complex.continuous_re.comp W.continuous
  obtain ⟨u₀, _, hu₀⟩ := isCompact_univ.exists_isMinOn hU_ne hre_cont.continuousOn
  set c : ℝ := (W u₀).re
  have hc_pos : 0 < c := hW u₀
  have hc_le : ∀ u : HTGeometry.UnitCircle, c ≤ (W u).re :=
    fun u => isMinOn_iff.mp hu₀ u (Set.mem_univ u)
  set m : ℝ := min c 1
  have hm_pos : 0 < m := lt_min hc_pos zero_lt_one
  have hm_le_one : m ≤ 1 := min_le_right c 1
  have hm_le_c : m ≤ c := min_le_left c 1
  have hden_pos : 0 < 2 * (‖W‖ + 1) ^ 2 := by positivity
  set ε : ℝ := m / (2 * (‖W‖ + 1) ^ 2)
  have hε_pos : 0 < ε := div_pos hm_pos hden_pos
  have hε_le_half : ε ≤ 1 / 2 := by
    have h1 : 1 ≤ (‖W‖ + 1) ^ 2 := by nlinarith [norm_nonneg W]
    rw [div_le_div_iff₀ hden_pos (by norm_num)]
    linarith
  set V : C(HTGeometry.UnitCircle, ℂ) := 1 - (ε : ℂ) • W
  have hεm_pos : 0 < ε * m := mul_pos hε_pos hm_pos
  have hεm_lt : ε * m < 1 := by nlinarith
  set q_sym : ℝ := Real.sqrt (1 - ε * m)
  have hq_sym_nn : 0 ≤ q_sym := Real.sqrt_nonneg _
  have hq_sym_lt : q_sym < 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have hV_norm : ‖V‖ ≤ q_sym := by
    refine (ContinuousMap.norm_le _ hq_sym_nn).mpr fun u => ?_
    have hVu : V u = 1 - (ε : ℂ) * W u := by simp [V]
    have hnsq : ‖V u‖ ^ 2 = 1 - 2 * ε * (W u).re + ε ^ 2 * ‖W u‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, hVu]
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.sub_im, Complex.one_im, Complex.mul_im]
      ring
    have hWu_le : ‖W u‖ ^ 2 ≤ (‖W‖ + 1) ^ 2 := by
      have h1 : ‖W u‖ ≤ ‖W‖ := W.norm_coe_le_norm u
      nlinarith [norm_nonneg (W u)]
    have hε_sq : ε ^ 2 * (‖W‖ + 1) ^ 2 = ε * m / 2 := by
      dsimp only [ε]
      field_simp [hden_pos.ne']
    have hsq_le : ‖V u‖ ^ 2 ≤ q_sym ^ 2 := by
      rw [Real.sq_sqrt (by linarith), hnsq]
      have hre_u : m ≤ (W u).re := hm_le_c.trans (hc_le u)
      have h1 : ε ^ 2 * ‖W u‖ ^ 2 ≤ ε * m / 2 := by
        calc ε ^ 2 * ‖W u‖ ^ 2 ≤ ε ^ 2 * (‖W‖ + 1) ^ 2 :=
              mul_le_mul_of_nonneg_left hWu_le (sq_nonneg ε)
          _ = ε * m / 2 := hε_sq
      nlinarith
    rw [sq, sq] at hsq_le
    exact nonneg_le_nonneg_of_sq_le_sq hq_sym_nn hsq_le
  -- Bound `‖1 - (ε : ℂ) • wienerHopfLift W‖ ≤ max q_sym (1 - ε) < 1` on `L²(ℝ)`.
  set q : ℝ := max q_sym (1 - ε)
  have hq_nn : 0 ≤ q := hq_sym_nn.trans (le_max_left _ _)
  have hq_lt : q < 1 := max_lt hq_sym_lt (by linarith)
  set P := HTGeometry.halfProj
  set Q := (1 : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real) - P
  have hP_norm : ‖P‖ ≤ 1 :=
    (_root_.RHTower.indicatorCutoff_isStarProjection (Ici 0) measurableSet_Ici).norm_le
  have hP_idem : P * P = P := HTGeometry.halfProj_mul_self
  have hP_star : star P = P := HTGeometry.star_halfProj
  have hPQ : P * Q = 0 := by
    dsimp only [Q]
    rw [mul_sub, mul_one, hP_idem, sub_self]
  have horth : ∀ x y : HTGeometry.L2Real, inner ℂ (P x) (Q y) = 0 := by
    intro x y
    rw [← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
      hP_star, ← ContinuousLinearMap.mul_apply_eq_comp, hPQ, _root_.zero_apply,
      inner_zero_right]
  have hrem_eq : (1 : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real) -
      (ε : ℂ) • HTGeometry.wienerHopfLift W =
      P * HTGeometry.circleMultiplier V * P + ((1 - ε : ℝ) : ℂ) • Q := by
    have hCV : HTGeometry.circleMultiplier V =
        1 - (ε : ℂ) • HTGeometry.circleMultiplier W := by
      have h1 : V = 1 + (-(ε : ℂ)) • W := by
        ext u; simp [V, sub_eq_add_neg]
      rw [h1, HTGeometry.circleMultiplier_add, HTGeometry.circleMultiplier_one,
        HTGeometry.circleMultiplier_smul, neg_smul, sub_eq_add_neg]
    rw [HTGeometry.wienerHopfLift, hCV]
    dsimp only [P, Q]
    ext1 x
    simp only [_root_.sub_apply, _root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.one_apply_eq_self, ContinuousLinearMap.mul_apply_eq_comp,
      Function.comp_apply]
    have hPPx : HTGeometry.halfProj (HTGeometry.halfProj x) = HTGeometry.halfProj x :=
      congrArg (fun T : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real => T x) hP_idem
    rw [map_sub, map_smul, hPPx, Complex.ofReal_sub, Complex.ofReal_one]
    module
  have hop_norm : ‖(1 : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real) -
      (ε : ℂ) • HTGeometry.wienerHopfLift W‖ ≤ q := by
    rw [hrem_eq]
    refine ContinuousLinearMap.opNorm_le_bound _ hq_nn fun x => ?_
    set a := (P * HTGeometry.circleMultiplier V * P) x
    set b := (((1 - ε : ℝ) : ℂ) • Q) x
    have ha_eq : a = P (HTGeometry.circleMultiplier V (P x)) := rfl
    have hb_eq : b = Q (((1 - ε : ℝ) : ℂ) • x) := by
      dsimp only [b]
      rw [_root_.smul_apply, map_smul]
    have hab_orth : inner ℂ a b = 0 := by
      rw [ha_eq, hb_eq]
      exact horth _ _
    have hPxQx_orth : inner ℂ (P x) (Q x) = 0 := horth x x
    have hPx_add_Qx : P x + Q x = x := by
      dsimp only [Q]
      simp
    have hx_pyth : ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖Q x‖ ^ 2 := by
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (P x) (Q x) hPxQx_orth
      rw [hPx_add_Qx] at h
      simpa only [sq] using h
    have hab_pyth : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
      simpa only [sq] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero a b hab_orth
    have ha_le : ‖a‖ ≤ q * ‖P x‖ := by
      calc ‖a‖ = ‖P (HTGeometry.circleMultiplier V (P x))‖ := rfl
        _ ≤ ‖P‖ * ‖HTGeometry.circleMultiplier V (P x)‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * (‖HTGeometry.circleMultiplier V‖ * ‖P x‖) :=
            mul_le_mul hP_norm (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _) zero_le_one
        _ ≤ 1 * (‖V‖ * ‖P x‖) := by
            gcongr
            exact HTGeometry.norm_circleMultiplier_le V
        _ ≤ 1 * (q * ‖P x‖) := by
            gcongr
            exact hV_norm.trans (le_max_left _ _)
        _ = q * ‖P x‖ := one_mul _
    have hb_le : ‖b‖ ≤ q * ‖Q x‖ := by
      have h1e_nn : 0 ≤ 1 - ε := by linarith
      calc ‖b‖ = ‖((1 - ε : ℝ) : ℂ) • Q x‖ := rfl
        _ = (1 - ε) * ‖Q x‖ := by
            rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1e_nn]
        _ ≤ q * ‖Q x‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
    have hsq_le : ‖a + b‖ ^ 2 ≤ (q * ‖x‖) ^ 2 := by
      have ha2 : ‖a‖ ^ 2 ≤ (q * ‖P x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg a) ha_le 2
      have hb2 : ‖b‖ ^ 2 ≤ (q * ‖Q x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg b) hb_le 2
      calc ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := hab_pyth
        _ ≤ (q * ‖P x‖) ^ 2 + (q * ‖Q x‖) ^ 2 := add_le_add ha2 hb2
        _ = q ^ 2 * (‖P x‖ ^ 2 + ‖Q x‖ ^ 2) := by ring
        _ = (q * ‖x‖) ^ 2 := by rw [← hx_pyth]; ring
    rw [sq, sq] at hsq_le
    exact nonneg_le_nonneg_of_sq_le_sq (mul_nonneg hq_nn (norm_nonneg x)) hsq_le
  have hu_smul : IsUnit ((ε : ℂ) • HTGeometry.wienerHopfLift W) := by
    have h := isUnit_one_sub_of_norm_lt_one (hop_norm.trans_lt hq_lt)
    rwa [sub_sub_cancel] at h
  obtain ⟨U_op, hU_op⟩ := hu_smul
  refine isUnit_iff_exists.mpr ⟨(ε : ℂ) • (↑U_op⁻¹ : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real), ?_, ?_⟩
  · calc HTGeometry.wienerHopfLift W * ((ε : ℂ) • (↑U_op⁻¹ : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real))
        = ((ε : ℂ) • HTGeometry.wienerHopfLift W) * ↑U_op⁻¹ := by
            rw [mul_smul_comm, smul_mul_assoc]
      _ = (U_op : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real) * ↑U_op⁻¹ := by rw [← hU_op]
      _ = 1 := Units.mul_inv U_op
  · calc ((ε : ℂ) • (↑U_op⁻¹ : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real)) * HTGeometry.wienerHopfLift W
        = (↑U_op⁻¹ : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real) * ((ε : ℂ) • HTGeometry.wienerHopfLift W) := by
            rw [smul_mul_assoc, mul_smul_comm]
      _ = ↑U_op⁻¹ * (U_op : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real) := by rw [← hU_op]
      _ = 1 := Units.inv_mul U_op

/-! ### Hardy-plus symbols (`ker hankelPlus`) and outer polynomial inverses -/

/-- Circle symbols whose positive Hankel operator `P₊ C_U (1 - P₊)` vanishes identically. -/
def InHardyPlus (U : C(HTGeometry.UnitCircle, ℂ)) : Prop :=
  HTGeometry.hankelPlus U = 0

private lemma inHardyPlus_one : InHardyPlus 1 := by
  unfold InHardyPlus HTGeometry.hankelPlus
  rw [HTGeometry.circleMultiplier_one, mul_one, mul_sub, mul_one,
    HTGeometry.halfProj_mul_self, sub_self]

private lemma inHardyPlus_add {U V : C(HTGeometry.UnitCircle, ℂ)}
    (hU : InHardyPlus U) (hV : InHardyPlus V) :
    InHardyPlus (U + V) := by
  unfold InHardyPlus HTGeometry.hankelPlus at hU hV ⊢
  rw [HTGeometry.circleMultiplier_add, mul_add, add_mul, hU, hV, add_zero]

private lemma inHardyPlus_smul (c : ℂ) {U : C(HTGeometry.UnitCircle, ℂ)} (hU : InHardyPlus U) :
    InHardyPlus (c • U) := by
  unfold InHardyPlus HTGeometry.hankelPlus at hU ⊢
  rw [HTGeometry.circleMultiplier_smul, mul_smul_comm, smul_mul_assoc, hU, smul_zero]

private lemma inHardyPlus_mul {U V : C(HTGeometry.UnitCircle, ℂ)}
    (hU : InHardyPlus U) (hV : InHardyPlus V) :
    InHardyPlus (U * V) := by
  unfold InHardyPlus at hU hV ⊢
  rw [HTGeometry.hankelPlus_mul, hU, hV, mul_zero, zero_mul, add_zero]

private lemma inHardyPlus_pow {U : C(HTGeometry.UnitCircle, ℂ)}
    (hU : InHardyPlus U) (m : ℕ) :
    InHardyPlus (U ^ m) := by
  induction m with
  | zero => rw [pow_zero]; exact inHardyPlus_one
  | succ m ih => rw [pow_succ]; exact inHardyPlus_mul ih hU

private lemma inHardyPlus_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → C(HTGeometry.UnitCircle, ℂ)) (hf : ∀ i ∈ s, InHardyPlus (f i)) :
    InHardyPlus (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, show (0 : C(HTGeometry.UnitCircle, ℂ)) = (0 : ℂ) • 1 by simp]
      exact inHardyPlus_smul 0 inHardyPlus_one
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact inHardyPlus_add (hf a (Finset.mem_insert_self a s))
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

private lemma inHardyPlus_multisetProd (s : Multiset C(HTGeometry.UnitCircle, ℂ))
    (hs : ∀ U ∈ s, InHardyPlus U) :
    InHardyPlus s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp [inHardyPlus_one]
  | @cons U s ih =>
      rw [Multiset.prod_cons]
      exact inHardyPlus_mul (hs U (Multiset.mem_cons_self U s))
        (ih fun V hV => hs V (Multiset.mem_cons_of_mem hV))

/-- Every polynomial `p ∈ ℂ[X]` restricts on `UnitCircle` to `ker hankelPlus`. -/
theorem hankelPlus_circlePoly_eq_zero (p : Polynomial ℂ) :
    HTGeometry.hankelPlus (circlePoly p) = 0 := by
  have hpoly_eq : circlePoly p =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k • HTGeometry.circleCoord ^ k := by
    ext u
    rw [circlePoly_apply, Polynomial.eval_eq_sum_range, ContinuousMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [HTGeometry.circleCoord]
  rw [hpoly_eq]
  exact inHardyPlus_finsetSum _ _ fun k _ =>
    inHardyPlus_smul (p.coeff k) (inHardyPlus_pow HTGeometry.hankelPlus_circleCoord k)

/-- Inverse symbol `(circlePoly p)⁻¹` in `C(UnitCircle, ℂ)` of an outer polynomial `p`. -/
def circlePolyInv (p : Polynomial ℂ) (hp : IsOuterPolynomial p) :
    C(HTGeometry.UnitCircle, ℂ) where
  toFun u := (p.eval (u : ℂ))⁻¹
  continuous_toFun :=
    (circlePoly p).continuous.inv₀ fun u =>
      hp (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le

@[simp]
theorem circlePoly_mul_inv (p : Polynomial ℂ) (hp : IsOuterPolynomial p) :
    circlePoly p * circlePolyInv p hp = 1 := by
  ext u
  exact mul_inv_cancel₀ (hp (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le)

@[simp]
theorem circlePolyInv_mul (p : Polynomial ℂ) (hp : IsOuterPolynomial p) :
    circlePolyInv p hp * circlePoly p = 1 := by
  rw [mul_comm, circlePoly_mul_inv]

private def linFactorInv (β : ℂ) (hβ : ‖β‖ < 1) : C(HTGeometry.UnitCircle, ℂ) where
  toFun u := (1 - β * (u : ℂ))⁻¹
  continuous_toFun := by
    refine (continuous_const.sub (continuous_const.mul continuous_subtype_val)).inv₀ fun u h0 => ?_
    have h1 : 1 = β * (u : ℂ) := sub_eq_zero.mp h0
    have hn : (1 : ℝ) = ‖β‖ := by
      have h := congrArg norm h1
      rwa [norm_one, norm_mul, HTGeometry.norm_coe_unitCircle, mul_one] at h
    linarith

private lemma inHardyPlus_linFactorInv {β : ℂ} (hβ : ‖β‖ < 1) :
    InHardyPlus (linFactorInv β hβ) := by
  let S : ℕ → C(HTGeometry.UnitCircle, ℂ) :=
    fun N => ∑ m ∈ Finset.range N, (β ^ m) • HTGeometry.circleCoord ^ m
  have hS_hardy : ∀ N : ℕ, HTGeometry.hankelPlus (S N) = 0 := fun N =>
    inHardyPlus_finsetSum _ _ fun m _ =>
      inHardyPlus_smul (β ^ m) (inHardyPlus_pow HTGeometry.hankelPlus_circleCoord m)
  have hgeom : ∀ (z : ℂ) (N : ℕ),
      (1 - z) * (∑ m ∈ Finset.range N, z ^ m) = 1 - z ^ N := by
    intro z N
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
        ring
  have hconv : Tendsto S atTop (𝓝 (linFactorInv β hβ)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hpow0 : Tendsto (fun N : ℕ => ‖linFactorInv β hβ‖ * ‖β‖ ^ N) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg β) hβ).const_mul ‖linFactorInv β hβ‖
    obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hpow0) ε hε
    refine ⟨N₀, fun N hN => ?_⟩
    rw [dist_eq_norm]
    have hle : ‖S N - linFactorInv β hβ‖ ≤ ‖linFactorInv β hβ‖ * ‖β‖ ^ N := by
      refine (ContinuousMap.norm_le _ (by positivity)).mpr fun u => ?_
      have h1z_ne : 1 - β * (u : ℂ) ≠ 0 := by
        intro h0
        have hn := congrArg norm (sub_eq_zero.mp h0)
        rw [norm_one, norm_mul, HTGeometry.norm_coe_unitCircle, mul_one] at hn
        linarith
      have hSu : S N u = ∑ m ∈ Finset.range N, (β * (u : ℂ)) ^ m := by
        dsimp only [S]
        rw [ContinuousMap.coe_sum, Finset.sum_apply]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp [HTGeometry.circleCoord, mul_pow]
      have hdiff : S N u - linFactorInv β hβ u =
          -(linFactorInv β hβ u * (β * (u : ℂ)) ^ N) := by
        rw [hSu]
        change (∑ m ∈ Finset.range N, (β * (u : ℂ)) ^ m) - (1 - β * (u : ℂ))⁻¹ =
          -((1 - β * (u : ℂ))⁻¹ * (β * (u : ℂ)) ^ N)
        have hg := hgeom (β * (u : ℂ)) N
        field_simp [h1z_ne]
        linear_combination hg
      calc ‖(S N - linFactorInv β hβ) u‖
          = ‖S N u - linFactorInv β hβ u‖ := rfl
        _ = ‖linFactorInv β hβ u‖ * ‖(β * (u : ℂ)) ^ N‖ := by rw [hdiff, norm_neg, norm_mul]
        _ = ‖linFactorInv β hβ u‖ * ‖β‖ ^ N := by
            rw [norm_pow, norm_mul, HTGeometry.norm_coe_unitCircle, mul_one]
        _ ≤ ‖linFactorInv β hβ‖ * ‖β‖ ^ N :=
            mul_le_mul_of_nonneg_right ((linFactorInv β hβ).norm_coe_le_norm u) (by positivity)
    have hlt := hN₀ N hN
    rw [dist_zero_right, Real.norm_of_nonneg (by positivity)] at hlt
    exact hle.trans_lt hlt
  have hhank := (HTGeometry.continuous_hankelPlus.tendsto _).comp hconv
  simp only [Function.comp_def, hS_hardy, tendsto_const_nhds_iff] at hhank
  exact hhank.symm

/-- For every outer polynomial `p`, `(circlePoly p)⁻¹` also lies in `ker hankelPlus`. -/
theorem hankelPlus_circlePolyInv_eq_zero (p : Polynomial ℂ) (hp : IsOuterPolynomial p) :
    HTGeometry.hankelPlus (circlePolyInv p hp) = 0 := by
  have hp0 : p ≠ 0 := by
    intro h0
    exact hp 0 (by simp) (by simp [h0])
  have hroot_gt : ∀ a ∈ p.roots, 1 < ‖a‖ := by
    intro a ha
    by_contra hle
    exact hp a (not_lt.mp hle) ((Polynomial.mem_roots hp0).mp ha)
  have hroot_inv_lt : ∀ a ∈ p.roots, ‖a⁻¹‖ < 1 := fun a ha => by
    rw [norm_inv]
    exact inv_lt_one_of_one_lt₀ (hroot_gt a ha)
  let factors : Multiset C(HTGeometry.UnitCircle, ℂ) :=
    p.roots.attach.map fun a => (-a.1⁻¹) • linFactorInv a.1⁻¹ (hroot_inv_lt a.1 a.2)
  have hfact_eq : circlePolyInv p hp = (p.leadingCoeff)⁻¹ • factors.prod := by
    ext u
    change (p.eval (u : ℂ))⁻¹ = p.leadingCoeff⁻¹ * (factors.prod) u
    have hsplits := (IsAlgClosed.splits p).eval_eq_prod_roots (u : ℂ)
    rw [hsplits, mul_inv]
    congr 1
    have heval_prod : ∀ s : Multiset {a : ℂ // a ∈ p.roots},
        ((s.map fun a => (-a.1⁻¹) • linFactorInv a.1⁻¹ (hroot_inv_lt a.1 a.2)).prod) u =
          ((s.map fun a => (u : ℂ) - a.1).prod)⁻¹ := by
      intro s
      induction s using Multiset.induction_on with
      | empty => simp
      | @cons a s ih =>
          rw [Multiset.map_cons, Multiset.prod_cons, ContinuousMap.mul_apply, ih,
            Multiset.map_cons, Multiset.prod_cons, mul_inv]
          congr 1
          have ha_ne : a.1 ≠ 0 := by
            have := hroot_gt a.1 a.2
            intro h0; rw [h0, norm_zero] at this; linarith
          change (-a.1⁻¹) * (1 - a.1⁻¹ * (u : ℂ))⁻¹ = ((u : ℂ) - a.1)⁻¹
          have hlin : -a.1 * (1 - a.1⁻¹ * (u : ℂ)) = (u : ℂ) - a.1 := by
            field_simp [ha_ne]; ring
          rw [← hlin, mul_inv]
          simp
    rw [heval_prod p.roots.attach]
    congr 1
    have hmap : (p.roots.attach.map fun a => (u : ℂ) - a.1) =
        p.roots.map fun a => (u : ℂ) - a := by
      simpa [Multiset.map_map] using
        congrArg (Multiset.map fun a => (u : ℂ) - a) (Multiset.attach_map_val p.roots)
    rw [hmap]
  rw [hfact_eq]
  refine inHardyPlus_smul _ (inHardyPlus_multisetProd factors fun V hV => ?_)
  obtain ⟨a, _, rfl⟩ := Multiset.mem_map.mp hV
  exact inHardyPlus_smul _ (inHardyPlus_linFactorInv _)

/-! ### Exact Wiener–Hopf operator factorization `A * cayleyWienerHopf ^ m * B` -/

private lemma wienerHopfLift_hardyPlus_mul {U : C(HTGeometry.UnitCircle, ℂ)}
    (hU : HTGeometry.hankelPlus U = 0) (V : C(HTGeometry.UnitCircle, ℂ)) :
    HTGeometry.wienerHopfLift (U * V) =
      HTGeometry.wienerHopfLift U * HTGeometry.wienerHopfLift V := by
  rw [HTGeometry.wienerHopfLift_mul, hU, zero_mul, sub_zero]

private lemma wienerHopfLift_mul_star_hardyPlus (U : C(HTGeometry.UnitCircle, ℂ))
    {V : C(HTGeometry.UnitCircle, ℂ)} (hV : HTGeometry.hankelPlus V = 0) :
    HTGeometry.wienerHopfLift (U * star V) =
      HTGeometry.wienerHopfLift U * HTGeometry.wienerHopfLift (star V) := by
  rw [HTGeometry.wienerHopfLift_mul, HTGeometry.hankelMinus_star, hV, star_zero, mul_zero, sub_zero]

/-- Spectral, kernel, and Fredholm-index theorem for any operator `T = A * cayleyWienerHopf ^ m * B`
sandwiched between invertible operators `A` and `B` on `L²(ℝ)`. -/
theorem fredholm_and_kernel_of_sandwiched_cayleyPow
    {A A_inv B B_inv : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real}
    (hAA : A * A_inv = 1) (hA_invA : A_inv * A = 1)
    (hBB : B * B_inv = 1) (hB_invB : B_inv * B = 1) (m : ℕ) :
    let T := A * HTGeometry.cayleyWienerHopf ^ m * B
    Function.Surjective T ∧
      Module.rank ℂ (LinearMap.ker (T : HTGeometry.L2Real →ₗ[ℂ] HTGeometry.L2Real)) = m ∧
      HTGeometry.IsFredholmOp T ∧
      HTGeometry.fredholmIndex T = (m : ℤ) ∧
      (IsUnit T ↔ m = 0) := by
  intro T
  have hsurj : Function.Surjective T := by
    intro y
    refine ⟨B_inv ((star HTGeometry.cayleyWienerHopf ^ m) (A_inv y)), ?_⟩
    dsimp only [T]
    have hBB_y : B (B_inv ((star HTGeometry.cayleyWienerHopf ^ m) (A_inv y))) =
        (star HTGeometry.cayleyWienerHopf ^ m) (A_inv y) := by
      simpa only [ContinuousLinearMap.mul_apply_eq_comp, Function.comp_apply,
        ContinuousLinearMap.one_apply_eq_self] using
        congrArg (fun S : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real =>
          S ((star HTGeometry.cayleyWienerHopf ^ m) (A_inv y))) hBB
    have hcay : (HTGeometry.cayleyWienerHopf ^ m)
        ((star HTGeometry.cayleyWienerHopf ^ m) (A_inv y)) = A_inv y := by
      simpa only [ContinuousLinearMap.mul_apply_eq_comp, Function.comp_apply,
        ContinuousLinearMap.one_apply_eq_self] using
        congrArg (fun S : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real => S (A_inv y))
          (HTGeometry.cayleyWienerHopf_pow_mul_star_pow m)
    have hAA_y : A (A_inv y) = y := by
      simpa only [ContinuousLinearMap.mul_apply_eq_comp, Function.comp_apply,
        ContinuousLinearMap.one_apply_eq_self] using
        congrArg (fun S : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real => S y) hAA
    change A ((HTGeometry.cayleyWienerHopf ^ m) (B (B_inv
      ((star HTGeometry.cayleyWienerHopf ^ m) (A_inv y))))) = y
    rw [hBB_y, hcay, hAA_y]
  have hA_inj : ∀ v : HTGeometry.L2Real, A v = 0 → v = 0 := by
    intro v hv
    have h := congrArg A_inv hv
    rw [map_zero] at h
    have h1 : A_inv (A v) = v := by
      simpa only [ContinuousLinearMap.mul_apply_eq_comp, Function.comp_apply,
        ContinuousLinearMap.one_apply_eq_self] using
        congrArg (fun S : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real => S v) hA_invA
    rwa [h1] at h
  have hB_left : ∀ x : HTGeometry.L2Real, B_inv (B x) = x := fun x => by
    simpa only [ContinuousLinearMap.mul_apply_eq_comp, Function.comp_apply,
      ContinuousLinearMap.one_apply_eq_self] using
      congrArg (fun S : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real => S x) hB_invB
  have hB_right : ∀ y : HTGeometry.L2Real, B (B_inv y) = y := fun y => by
    simpa only [ContinuousLinearMap.mul_apply_eq_comp, Function.comp_apply,
      ContinuousLinearMap.one_apply_eq_self] using
      congrArg (fun S : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real => S y) hBB
  let kerEquiv :
      LinearMap.ker (T : HTGeometry.L2Real →ₗ[ℂ] HTGeometry.L2Real) ≃ₗ[ℂ]
      LinearMap.ker ((HTGeometry.cayleyWienerHopf ^ m :
        HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real) : HTGeometry.L2Real →ₗ[ℂ] HTGeometry.L2Real) :=
    { toFun := fun x => ⟨B x.1, by
        rw [LinearMap.mem_ker]
        have hx := LinearMap.mem_ker.mp x.2
        exact hA_inj _ hx⟩
      invFun := fun y => ⟨B_inv y.1, by
        rw [LinearMap.mem_ker]
        change A ((HTGeometry.cayleyWienerHopf ^ m) (B (B_inv y.1))) = 0
        rw [hB_right]
        have hy : (HTGeometry.cayleyWienerHopf ^ m) y.1 = 0 := LinearMap.mem_ker.mp y.2
        rw [hy, map_zero]⟩
      left_inv := fun x => Subtype.ext (hB_left x.1)
      right_inv := fun y => Subtype.ext (hB_right y.1)
      map_add' := fun x y => Subtype.ext (map_add B x.1 y.1)
      map_smul' := fun c x => Subtype.ext (map_smul B c x.1) }
  have hrank : Module.rank ℂ
      (LinearMap.ker (T : HTGeometry.L2Real →ₗ[ℂ] HTGeometry.L2Real)) = m := by
    rw [kerEquiv.rank_eq, HTGeometry.rank_ker_cayleyWienerHopf_pow]
  have hfd : FiniteDimensional ℂ
      (LinearMap.ker (T : HTGeometry.L2Real →ₗ[ℂ] HTGeometry.L2Real)) :=
    Module.rank_lt_aleph0_iff.mp (by rw [hrank]; exact Cardinal.natCast_lt_aleph0)
  have hrange : LinearMap.range (T : HTGeometry.L2Real →ₗ[ℂ] HTGeometry.L2Real) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hfred : HTGeometry.IsFredholmOp T :=
    ⟨hfd, by rw [hrange]; exact isClosed_univ, by rw [hrange]; infer_instance⟩
  have hind : HTGeometry.fredholmIndex T = (m : ℤ) := by
    have hq : Module.finrank ℂ (HTGeometry.L2Real ⧸ (⊤ : Submodule ℂ HTGeometry.L2Real)) = 0 :=
      Module.finrank_zero_of_subsingleton
    rw [HTGeometry.fredholmIndex, hrange, hq, Module.finrank_eq_of_rank_eq hrank]
    simp
  have hunit_iff : IsUnit T ↔ m = 0 := by
    constructor
    · rintro ⟨u, hu⟩
      have hker_bot : LinearMap.ker (T : HTGeometry.L2Real →ₗ[ℂ] HTGeometry.L2Real) = ⊥ := by
        rw [LinearMap.ker_eq_bot']
        intro x hx
        have h1 : (↑u⁻¹ : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real) (T x) = 0 := by
          change (↑u⁻¹ : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real)
            ((T : HTGeometry.L2Real →ₗ[ℂ] HTGeometry.L2Real) x) = 0
          rw [hx, map_zero]
        have h2 : (↑u⁻¹ * T : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real) = 1 := by
          rw [← hu, Units.inv_mul]
        have h3 : (↑u⁻¹ : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real) (T x) = x := by
          simpa only [ContinuousLinearMap.mul_apply_eq_comp, Function.comp_apply,
            ContinuousLinearMap.one_apply_eq_self] using
            congrArg (fun S : HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real => S x) h2
        rwa [h3] at h1
      have h0 : (m : Cardinal) = 0 := by
        rw [← hrank, hker_bot, rank_bot]
      exact Nat.cast_eq_zero.mp h0
    · rintro rfl
      dsimp only [T]
      rw [pow_zero, mul_one]
      refine isUnit_iff_exists.mpr ⟨B_inv * A_inv, ?_, ?_⟩
      · calc (A * B) * (B_inv * A_inv) = A * (B * B_inv) * A_inv := by noncomm_ring
          _ = 1 := by rw [hBB, mul_one, hAA]
      · calc (B_inv * A_inv) * (A * B) = B_inv * (A_inv * A) * B := by noncomm_ring
          _ = 1 := by rw [hA_invA, mul_one, hB_invB]
  exact ⟨hsurj, hrank, hfred, hind, hunit_iff⟩

/-! ## §3 Quadratic Zhukovsky root splitting and canonical Birkhoff–Szegő factorization -/

/-- Quadratic Zhukovsky root splitting: for every `d : ℂ`, there exists `z_+ : ℂ` with `1 ≤ ‖z_+‖`
such that `zhukovskyMap n z_+ = d` and `(z - z_+) * (z - z_+⁻¹) = z² - w_d z + 1`, with
`‖z_+‖ < zhukovskyRadius n ↔ zhukovskyEllipseForm n d < 1` and
`zhukovskyRadius n < ‖z_+‖ ↔ 1 < zhukovskyEllipseForm n d`. -/
private lemma exists_zhukovsky_quadratic_root (n : ℕ) (d : ℂ) :
    ∃ z_p : ℂ, 1 ≤ ‖z_p‖ ∧ z_p ≠ 0 ∧
      (∀ z : ℂ, z ≠ 0 →
        zhukovskyMap n z - d =
          ((zhukovskyFocal n : ℂ) / 2) * (z⁻¹ * ((z - z_p) * (z - z_p⁻¹)))) ∧
      (‖z_p‖ < zhukovskyRadius n ↔ zhukovskyEllipseForm n d < 1) ∧
      (zhukovskyRadius n < ‖z_p‖ ↔ 1 < zhukovskyEllipseForm n d) := by
  set c_n := zhukovskyFocal n
  have hc_pos : 0 < c_n := zhukovskyFocal_pos n
  have hc_ne : (c_n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc_pos.ne'
  set w_d : ℂ := (2 / (c_n : ℂ)) * (d - (1 / 2 : ℂ))
  let Q : Polynomial ℂ := X ^ 2 - C w_d * X + 1
  have hQ_deg : Q.degree = 2 := by
    dsimp only [Q]
    have hlt1 : (C w_d * X : Polynomial ℂ).degree < (X ^ 2 : Polynomial ℂ).degree := by
      calc (C w_d * X : Polynomial ℂ).degree
          ≤ (C w_d).degree + X.degree := Polynomial.degree_mul_le _ _
        _ ≤ 0 + 1 := add_le_add Polynomial.degree_C_le (by simp)
        _ < 2 := by decide
        _ = (X ^ 2 : Polynomial ℂ).degree := by simp
    have hsub : (X ^ 2 - C w_d * X : Polynomial ℂ).degree = 2 := by
      rw [Polynomial.degree_sub_eq_left_of_degree_lt hlt1]
      simp
    rw [Polynomial.degree_add_eq_left_of_degree_lt]
    · exact hsub
    · rw [hsub]; simp
  obtain ⟨z₀, hz₀⟩ := IsAlgClosed.exists_root Q (by rw [hQ_deg]; decide)
  have hz₀_eq : z₀ ^ 2 - w_d * z₀ + 1 = 0 := by
    simpa [Q, Polynomial.IsRoot] using hz₀
  have hz₀_ne : z₀ ≠ 0 := by
    intro h0
    rw [h0] at hz₀_eq
    norm_num at hz₀_eq
  have hz₀_sum : z₀ + z₀⁻¹ = w_d := by
    field_simp [hz₀_ne]
    linear_combination hz₀_eq
  set z_p : ℂ := if 1 ≤ ‖z₀‖ then z₀ else z₀⁻¹
  have hzp_ge : 1 ≤ ‖z_p‖ := by
    dsimp only [z_p]
    split_ifs with h
    · exact h
    · rw [norm_inv]
      exact one_le_inv₀ (norm_pos_iff.mpr hz₀_ne) (not_le.mp h).le
  have hzp_ne : z_p ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hzp_ge
    linarith
  have hzp_sum : z_p + z_p⁻¹ = w_d := by
    dsimp only [z_p]
    split_ifs
    · exact hz₀_sum
    · rw [inv_inv, add_comm]
      exact hz₀_sum
  have hfact : ∀ z : ℂ, z ≠ 0 →
      zhukovskyMap n z - d =
        ((c_n : ℂ) / 2) * (z⁻¹ * ((z - z_p) * (z - z_p⁻¹))) := by
    intro z hz
    unfold zhukovskyMap
    change (1 / 2 : ℂ) + ((c_n : ℂ) / 2) * (z + z⁻¹) - d = _
    have hquad : (z - z_p) * (z - z_p⁻¹) = z ^ 2 - w_d * z + 1 := by
      rw [← hzp_sum]
      field_simp [hzp_ne]
      ring
    rw [hquad]
    dsimp only [w_d]
    field_simp [hz, hc_ne]
    ring
  -- Express `zhukovskyEllipseForm n d` through `r := ‖z_p‖ ≥ 1` and `φ := Complex.arg z_p`.
  set r : ℝ := ‖z_p‖
  set φ : ℝ := Complex.arg z_p
  set ρ := zhukovskyRadius n
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hzp_ge
  have hρ_gt : 1 < ρ := one_lt_zhukovskyRadius n
  have hρ_pos : 0 < ρ := zero_lt_one.trans hρ_gt
  have hzp_polar : z_p = (r : ℂ) * Complex.exp ((φ : ℂ) * I) := by
    dsimp only [r, φ]
    rw [mul_comm (Complex.arg z_p : ℂ) I]
    exact (Complex.norm_mul_exp_arg_mul_I z_p).symm
  have hd_eq : d = zhukovskyMap n z_p := by
    have h := hfact z_p hzp_ne
    rw [sub_self, zero_mul, mul_zero, mul_zero] at h
    exact (sub_eq_zero.mp h).symm
  have hd_polar : d = (1 / 2 : ℂ) +
      (((c_n / 2) * (r + r⁻¹) * Real.cos φ : ℝ) : ℂ) +
      (((c_n / 2) * (r - r⁻¹) * Real.sin φ : ℝ) : ℂ) * I := by
    rw [hd_eq, hzp_polar]
    unfold zhukovskyMap
    change (1 / 2 : ℂ) + ((c_n : ℂ) / 2) *
      ((r : ℂ) * Complex.exp ((φ : ℂ) * I) + ((r : ℂ) * Complex.exp ((φ : ℂ) * I))⁻¹) = _
    have hinv : ((r : ℂ) * Complex.exp ((φ : ℂ) * I))⁻¹ =
        (r : ℂ)⁻¹ * Complex.exp ((-(φ : ℂ)) * I) := by
      rw [mul_inv, ← Complex.exp_neg]
      congr 2; ring
    rw [hinv, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, ← Complex.ofReal_inv]
    push_cast
    ring
  have hd_re : d.re - 1 / 2 = (c_n / 2) * (r + r⁻¹) * Real.cos φ := by
    have h12 : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
    rw [hd_polar]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.ofReal_im, Complex.I_im, h12]
    ring
  have hd_im : d.im = (c_n / 2) * (r - r⁻¹) * Real.sin φ := by
    have h12 : (1 / 2 : ℂ).im = 0 := by norm_num
    rw [hd_polar]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.ofReal_re, Complex.I_im, h12]
    ring
  have hmaj := zhukovskyAxis_major_identity n
  have hmin := zhukovskyAxis_minor_identity n
  have ha_pos := zhukovskyMajorAxis_pos n
  have hb_pos := zhukovskyMinorAxis_pos n
  have hρ_sum_pos : 0 < ρ + ρ⁻¹ := by positivity
  have hρ_sub_pos : 0 < ρ - ρ⁻¹ := by
    have h1 : ρ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hρ_gt
    linarith
  have hform_eq : zhukovskyEllipseForm n d =
      ((r + r⁻¹) / (ρ + ρ⁻¹)) ^ 2 * Real.cos φ ^ 2 +
        ((r - r⁻¹) / (ρ - ρ⁻¹)) ^ 2 * Real.sin φ ^ 2 := by
    unfold zhukovskyEllipseForm
    rw [hd_re, hd_im, ← hmaj, ← hmin]
    dsimp only [c_n, ρ]
    field_simp [hc_pos.ne', hρ_sum_pos.ne', hρ_sub_pos.ne']
    ring
  have hcs := Real.cos_sq_add_sin_sq φ
  have hr_lt_imp : r < ρ → zhukovskyEllipseForm n d < 1 := by
    intro hlt
    have hsum_lt : r + r⁻¹ < ρ + ρ⁻¹ := by
      have hdiff : (ρ + ρ⁻¹) - (r + r⁻¹) = (ρ - r) * (1 - (r * ρ)⁻¹) := by
        field_simp [hr_pos.ne', hρ_pos.ne']; ring
      have hprod_gt : 1 < r * ρ := by nlinarith [hzp_ge, hρ_gt]
      have hinv_lt : (r * ρ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hprod_gt
      have hpos : 0 < (ρ - r) * (1 - (r * ρ)⁻¹) := mul_pos (by linarith) (by linarith)
      linarith
    have hsub_lt : r - r⁻¹ < ρ - ρ⁻¹ := by
      have hinv_gt : ρ⁻¹ < r⁻¹ := inv_lt_inv₀ hρ_pos hr_pos |>.mpr hlt
      linarith
    have hsub_nn : 0 ≤ r - r⁻¹ := by
      have hinv_le : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hzp_ge
      linarith
    have hq1 : ((r + r⁻¹) / (ρ + ρ⁻¹)) ^ 2 < 1 := by
      have hd1 : (r + r⁻¹) / (ρ + ρ⁻¹) < 1 := (div_lt_one hρ_sum_pos).mpr hsum_lt
      have hd0 : 0 ≤ (r + r⁻¹) / (ρ + ρ⁻¹) := by positivity
      nlinarith
    have hq2 : ((r - r⁻¹) / (ρ - ρ⁻¹)) ^ 2 < 1 := by
      have hd1 : (r - r⁻¹) / (ρ - ρ⁻¹) < 1 := (div_lt_one hρ_sub_pos).mpr hsub_lt
      have hd0 : 0 ≤ (r - r⁻¹) / (ρ - ρ⁻¹) := div_nonneg hsub_nn hρ_sub_pos.le
      nlinarith
    rw [hform_eq]
    nlinarith [sq_nonneg (Real.cos φ), sq_nonneg (Real.sin φ), hcs]
  have hr_gt_imp : ρ < r → 1 < zhukovskyEllipseForm n d := by
    intro hgt
    have hsum_gt : ρ + ρ⁻¹ < r + r⁻¹ := by
      have hdiff : (r + r⁻¹) - (ρ + ρ⁻¹) = (r - ρ) * (1 - (r * ρ)⁻¹) := by
        field_simp [hr_pos.ne', hρ_pos.ne']; ring
      have hprod_gt : 1 < r * ρ := by nlinarith [hzp_ge, hρ_gt]
      have hinv_lt : (r * ρ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hprod_gt
      have hpos : 0 < (r - ρ) * (1 - (r * ρ)⁻¹) := mul_pos (by linarith) (by linarith)
      linarith
    have hsub_gt : ρ - ρ⁻¹ < r - r⁻¹ := by
      have hinv_lt : r⁻¹ < ρ⁻¹ := inv_lt_inv₀ hr_pos hρ_pos |>.mpr hgt
      linarith
    have hq1 : 1 < ((r + r⁻¹) / (ρ + ρ⁻¹)) ^ 2 := by
      have hd1 : 1 < (r + r⁻¹) / (ρ + ρ⁻¹) := (one_lt_div hρ_sum_pos).mpr hsum_gt
      nlinarith
    have hq2 : 1 < ((r - r⁻¹) / (ρ - ρ⁻¹)) ^ 2 := by
      have hd1 : 1 < (r - r⁻¹) / (ρ - ρ⁻¹) := (one_lt_div hρ_sub_pos).mpr hsub_gt
      nlinarith
    rw [hform_eq]
    nlinarith [sq_nonneg (Real.cos φ), sq_nonneg (Real.sin φ), hcs]
  have hr_eq_imp : r = ρ → zhukovskyEllipseForm n d = 1 := by
    intro heq
    rw [hform_eq, heq, div_self hρ_sum_pos.ne', div_self hρ_sub_pos.ne']
    nlinarith [hcs]
  refine ⟨z_p, hzp_ge, hzp_ne, hfact, ⟨hr_lt_imp, ?_⟩, ⟨hr_gt_imp, ?_⟩⟩
  · intro hlt_form
    rcases lt_trichotomy r ρ with hlt | heq | hgt
    · exact hlt
    · exfalso; linarith [hr_eq_imp heq]
    · exfalso; linarith [hr_gt_imp hgt]
  · intro hgt_form
    rcases lt_trichotomy r ρ with hlt | heq | hgt
    · exfalso; linarith [hr_lt_imp hlt]
    · exfalso; linarith [hr_eq_imp heq]
    · exact hgt

/-- **Exterior Zhukovsky factor outer splitting (`E_n(d) > 1`).**
When `d` lies strictly outside the `n`-th Zhukovsky ellipse, `zhukovskyLoop n u - d` factors on
`UnitCircle` as `g(u) · conj(h(u))` for degree-`1` outer polynomials `g, h` zero-free on
`closedBall 0 1`. -/
theorem exists_zhukovsky_outer_factorization_of_gt_one {n : ℕ} {d : ℂ}
    (hd : 1 < zhukovskyEllipseForm n d) :
    ∃ g h : Polynomial ℂ, IsOuterPolynomial g ∧ IsOuterPolynomial h ∧
      ∀ u : HTGeometry.UnitCircle,
        zhukovskyLoop n u - d = circlePoly g u * star (circlePoly h u) := by
  obtain ⟨z_p, hzp_ge, hzp_ne, hfact, _, hgt_iff⟩ := exists_zhukovsky_quadratic_root n d
  have hzp_gt : zhukovskyRadius n < ‖z_p‖ := hgt_iff.mpr hd
  set ρ := zhukovskyRadius n
  set c_n := zhukovskyFocal n
  have hρ_gt : 1 < ρ := one_lt_zhukovskyRadius n
  have hρ_pos : 0 < ρ := zero_lt_one.trans hρ_gt
  have hρ_ne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ_pos.ne'
  have hc_ne : (c_n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zhukovskyFocal_pos n).ne'
  set α_p : ℂ := z_p / (ρ : ℂ)
  set α_m : ℂ := z_p⁻¹ / (ρ : ℂ)
  have hαp_gt : 1 < ‖α_p‖ := by
    dsimp only [α_p]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ_pos, one_lt_div hρ_pos]
    exact hzp_gt
  have hαp_ne : α_p ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hαp_gt; linarith
  have hαp_inv_lt : ‖α_p⁻¹‖ < 1 := by
    rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hαp_gt
  have hαm_lt : ‖α_m‖ < 1 := by
    dsimp only [α_m]
    rw [norm_div, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ_pos,
      div_lt_one hρ_pos]
    have hinv_le : ‖z_p‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hzp_ge
    linarith
  let g : Polynomial ℂ := C (-(((c_n : ℂ) * (ρ : ℂ) / 2) * α_p)) * (1 - C α_p⁻¹ * X)
  let h : Polynomial ℂ := 1 - C (star α_m) * X
  have hg_outer : IsOuterPolynomial g := by
    intro z hz
    dsimp only [g]
    rw [Polynomial.eval_mul, Polynomial.eval_C]
    refine mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero (div_ne_zero (mul_ne_zero hc_ne hρ_ne)
      two_ne_zero) hαp_ne)) ?_
    rw [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    intro h0
    have hn := congrArg norm (sub_eq_zero.mp h0)
    rw [norm_one, norm_mul] at hn
    have hle : ‖α_p⁻¹‖ * ‖z‖ ≤ ‖α_p⁻¹‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    linarith
  have hh_outer : IsOuterPolynomial h := by
    intro z hz
    dsimp only [h]
    rw [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X]
    intro h0
    have hn := congrArg norm (sub_eq_zero.mp h0)
    rw [norm_one, norm_mul, Complex.star_def, Complex.norm_conj] at hn
    have hle : ‖α_m‖ * ‖z‖ ≤ ‖α_m‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    linarith
  refine ⟨g, h, hg_outer, hh_outer, fun u => ?_⟩
  have hu_ne : (u : ℂ) ≠ 0 := by
    intro h0
    have h1 := HTGeometry.norm_coe_unitCircle u
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  change zhukovskyMap n ((ρ : ℂ) * (u : ℂ)) - d = g.eval (u : ℂ) * star (h.eval (u : ℂ))
  rw [hfact ((ρ : ℂ) * (u : ℂ)) (mul_ne_zero hρ_ne hu_ne)]
  have hu_inv : (u : ℂ)⁻¹ = star (u : ℂ) := unitCircle_inv_eq_star u
  dsimp only [g, h, α_p, α_m]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_C,
    Polynomial.eval_X, star_sub, star_one, star_mul, star_star]
  rw [mul_inv, hu_inv]
  field_simp [hρ_ne, hzp_ne]
  ring

/-- **Interior Zhukovsky factor outer splitting (`E_n(d) < 1`).**
When `d` lies strictly inside the `n`-th Zhukovsky ellipse, `zhukovskyLoop n u - d` factors on
`UnitCircle` as `u · conj(q(u))` for a degree-`2` outer polynomial `q` zero-free on
`closedBall 0 1`. -/
theorem exists_zhukovsky_outer_factorization_of_lt_one {n : ℕ} {d : ℂ}
    (hd : zhukovskyEllipseForm n d < 1) :
    ∃ q : Polynomial ℂ, IsOuterPolynomial q ∧
      ∀ u : HTGeometry.UnitCircle,
        zhukovskyLoop n u - d = HTGeometry.circleCoord u * star (circlePoly q u) := by
  obtain ⟨z_p, hzp_ge, hzp_ne, hfact, hlt_iff, _⟩ := exists_zhukovsky_quadratic_root n d
  have hzp_lt : ‖z_p‖ < zhukovskyRadius n := hlt_iff.mpr hd
  set ρ := zhukovskyRadius n
  set c_n := zhukovskyFocal n
  have hρ_gt : 1 < ρ := one_lt_zhukovskyRadius n
  have hρ_pos : 0 < ρ := zero_lt_one.trans hρ_gt
  have hρ_ne : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ_pos.ne'
  have hc_ne : (c_n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zhukovskyFocal_pos n).ne'
  set α_p : ℂ := z_p / (ρ : ℂ)
  set α_m : ℂ := z_p⁻¹ / (ρ : ℂ)
  have hαp_lt : ‖α_p‖ < 1 := by
    dsimp only [α_p]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ_pos, div_lt_one hρ_pos]
    exact hzp_lt
  have hαm_lt : ‖α_m‖ < 1 := by
    dsimp only [α_m]
    rw [norm_div, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ_pos,
      div_lt_one hρ_pos]
    have hinv_le : ‖z_p‖⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hzp_ge
    linarith
  let q : Polynomial ℂ :=
    C ((c_n : ℂ) * (ρ : ℂ) / 2) * (1 - C (star α_p) * X) * (1 - C (star α_m) * X)
  have hq_outer : IsOuterPolynomial q := by
    intro z hz
    dsimp only [q]
    rw [Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C]
    refine mul_ne_zero (mul_ne_zero (div_ne_zero (mul_ne_zero hc_ne hρ_ne) two_ne_zero) ?_) ?_
    · rw [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      intro h0
      have hn := congrArg norm (sub_eq_zero.mp h0)
      rw [norm_one, norm_mul, Complex.star_def, Complex.norm_conj] at hn
      have hle : ‖α_p‖ * ‖z‖ ≤ ‖α_p‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      linarith
    · rw [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X]
      intro h0
      have hn := congrArg norm (sub_eq_zero.mp h0)
      rw [norm_one, norm_mul, Complex.star_def, Complex.norm_conj] at hn
      have hle : ‖α_m‖ * ‖z‖ ≤ ‖α_m‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      linarith
  refine ⟨q, hq_outer, fun u => ?_⟩
  have hu_ne : (u : ℂ) ≠ 0 := by
    intro h0
    have h1 := HTGeometry.norm_coe_unitCircle u
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  have hu_mul_star : (u : ℂ) * star (u : ℂ) = 1 := by
    rw [Complex.star_def, Complex.mul_conj', HTGeometry.norm_coe_unitCircle]
    norm_num
  change zhukovskyMap n ((ρ : ℂ) * (u : ℂ)) - d = (u : ℂ) * star (q.eval (u : ℂ))
  rw [hfact ((ρ : ℂ) * (u : ℂ)) (mul_ne_zero hρ_ne hu_ne)]
  have hu_inv : (u : ℂ)⁻¹ = star (u : ℂ) := unitCircle_inv_eq_star u
  have hcρ_conj : star ((c_n : ℂ) * (ρ : ℂ) / 2) = (c_n : ℂ) * (ρ : ℂ) / 2 := by
    simp [Complex.star_def]
  dsimp only [q, α_p, α_m]
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_C,
    Polynomial.eval_X, star_mul, star_sub, star_one, star_star, hcρ_conj]
  rw [mul_inv, hu_inv]
  -- Replace `u - α` with `u * (1 - α * star u)` using `(u : ℂ) * star (u : ℂ) = 1`.
  have h1 : (ρ : ℂ) * (u : ℂ) - z_p =
      (ρ : ℂ) * (u : ℂ) * (1 - (z_p / (ρ : ℂ)) * star (u : ℂ)) := by
    calc (ρ : ℂ) * (u : ℂ) - z_p
        = (ρ : ℂ) * (u : ℂ) - z_p * ((u : ℂ) * star (u : ℂ)) := by rw [hu_mul_star, mul_one]
      _ = (ρ : ℂ) * (u : ℂ) * (1 - (z_p / (ρ : ℂ)) * star (u : ℂ)) := by
          field_simp [hρ_ne]; ring
  have h2 : (ρ : ℂ) * (u : ℂ) - z_p⁻¹ =
      (ρ : ℂ) * (u : ℂ) * (1 - (z_p⁻¹ / (ρ : ℂ)) * star (u : ℂ)) := by
    calc (ρ : ℂ) * (u : ℂ) - z_p⁻¹
        = (ρ : ℂ) * (u : ℂ) - z_p⁻¹ * ((u : ℂ) * star (u : ℂ)) := by rw [hu_mul_star, mul_one]
      _ = (ρ : ℂ) * (u : ℂ) * (1 - (z_p⁻¹ / (ρ : ℂ)) * star (u : ℂ)) := by
          field_simp [hρ_ne]; ring
  rw [h1, h2]
  calc ((c_n : ℂ) / 2) * (((ρ : ℂ)⁻¹ * star (u : ℂ)) *
          (((ρ : ℂ) * (u : ℂ) * (1 - z_p / (ρ : ℂ) * star (u : ℂ))) *
            ((ρ : ℂ) * (u : ℂ) * (1 - z_p⁻¹ / (ρ : ℂ) * star (u : ℂ)))))
      = ((ρ : ℂ)⁻¹ * (ρ : ℂ)) * ((u : ℂ) * star (u : ℂ)) * (u : ℂ) *
          (((c_n : ℂ) * (ρ : ℂ) / 2) * (1 - z_p / (ρ : ℂ) * star (u : ℂ)) *
            (1 - z_p⁻¹ / (ρ : ℂ) * star (u : ℂ))) := by ring
    _ = (u : ℂ) * (((c_n : ℂ) * (ρ : ℂ) / 2) * (1 - z_p / (ρ : ℂ) * star (u : ℂ)) *
          (1 - z_p⁻¹ / (ρ : ℂ) * star (u : ℂ))) := by
        rw [inv_mul_cancel₀ hρ_ne, hu_mul_star, one_mul, one_mul]

/-- Surjectivity of `zhukovskyLoop n` onto the level set `zhukovskyEllipseForm n = 1`:
boundary regularity plus nonvanishing of `integerThetaLaurentLoop T n N` on `UnitCircle`
automatically excludes all enclosed zero differences from the Zhukovsky ellipse. -/
theorem ellipse_nondegenerate_of_loop_ne_zero (T : ℝ) (n N : ℕ)
    (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0)
    (hnz : ∀ u : HTGeometry.UnitCircle, integerThetaLaurentLoop T n N u ≠ 0) :
    ∀ z ∈ prefixEnclosedZeros T n N, ∀ w ∈ prefixEnclosedZeros T n N,
      zhukovskyEllipseForm n (z - w) ≠ 1 := by
  have hbdry0 : ∀ t : ℝ, finiteThetaShellPencil N 0
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 := by
    simpa only [finiteThetaShellPencil_zero] using hbdry
  have hfun : finiteThetaShellPencil N 0 = _root_.RHTower.finiteThetaAmplitude N :=
    funext (finiteThetaShellPencil_zero N)
  intro z hz w hw hform
  set d := z - w
  set a := zhukovskyMajorAxis n
  set b := zhukovskyMinorAxis n
  have ha_ne : a ≠ 0 := (zhukovskyMajorAxis_pos n).ne'
  have hb_ne : b ≠ 0 := (zhukovskyMinorAxis_pos n).ne'
  let ζ : ℂ := (((d.re - 1 / 2) / a : ℝ) : ℂ) + (((d.im / b : ℝ) : ℂ) * I)
  have hζ_norm : ‖ζ‖ = 1 := by
    have hsq : ‖ζ‖ ^ 2 = 1 := by
      rw [← Complex.normSq_eq_norm_sq]
      dsimp only [ζ]
      simp only [Complex.normSq_apply, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.ofReal_im, Complex.I_im, Complex.add_im, Complex.mul_im]
      unfold zhukovskyEllipseForm at hform
      dsimp only [a, b]
      linarith [div_pow (d.re - 1 / 2) a 2, div_pow d.im b 2]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg ζ) two_ne_zero).mp hsq
  let u : HTGeometry.UnitCircle := ⟨ζ, mem_sphere_zero_iff_norm.mpr hζ_norm⟩
  have hloop_u : zhukovskyLoop n u = d := by
    rw [← HTGeometry.circleExp_arg u, zhukovskyLoop_circleExp]
    have hexp := HTGeometry.exp_arg_mul_I_of_norm_eq_one hζ_norm
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin] at hexp
    have hcos : Real.cos (Complex.arg ζ) = (d.re - 1 / 2) / a := by
      have h := congrArg Complex.re hexp
      simpa [ζ] using h
    have hsin : Real.sin (Complex.arg ζ) = d.im / b := by
      have h := congrArg Complex.im hexp
      simpa [ζ] using h
    change zhukovskyLoop n (HTGeometry.circleExp (Complex.arg ζ)) = d at *
    rw [hcos, hsin]
    dsimp only [a, b]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im]
      field_simp [ha_ne]; ring
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
        Complex.ofReal_re, Complex.I_im]
      field_simp [hb_ne]; ring
  have hz0 := ((mem_prefixEnclosedZeros_iff T n N z).mp hz).2
  have hw0 := ((mem_prefixEnclosedZeros_iff T n N w).mp hw).2
  have hmz_pos : 0 < (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z).toNat := by
    have hne_zero : analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z ≠ 0 := by
      intro h0
      exact ((analyticOnNhd_finiteThetaAmplitude N z (Set.mem_univ z)).analyticOrderAt_eq_zero.mp h0)
        hz0
    have hne_top := finiteThetaAmplitude_orderAt_ne_top N z
    exact Nat.pos_of_ne_zero fun ht =>
      hne_zero ((ENat.coe_toNat hne_top).symm.trans (by simp [ht]))
  have hmw_pos : 0 < (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat := by
    have hne_zero : analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w ≠ 0 := by
      intro h0
      exact ((analyticOnNhd_finiteThetaAmplitude N w (Set.mem_univ w)).analyticOrderAt_eq_zero.mp h0)
        hw0
    have hne_top := finiteThetaAmplitude_orderAt_ne_top N w
    exact Nat.pos_of_ne_zero fun ht =>
      hne_zero ((ENat.coe_toNat hne_top).symm.trans (by simp [ht]))
  have heval := eval_pencilDifferencePoly_eq_prod T n N ⟨le_rfl, zero_le_one⟩ hbdry0 (zhukovskyLoop n u)
  simp only [pencilDifferencePoly_zero, prefixEnclosedZeros, hfun] at heval
  have hP0 : (integerThetaDifferencePoly T n N).eval (zhukovskyLoop n u) = 0 := by
    rw [heval]
    refine Finset.prod_eq_zero hz ?_
    refine Finset.prod_eq_zero hw ?_
    rw [hloop_u, sub_self, zero_pow (Nat.mul_pos hmz_pos hmw_pos).ne']
  apply hnz u
  rw [integerThetaLaurentLoop_apply, hP0, zero_pow two_ne_zero]

/-- **Canonical Birkhoff–Zhukovsky–Szegő factorization of `integerThetaLaurentLoop` and exact
operator decomposition on `L²(ℝ)`.**
At every boundary-regular, ellipse-nondegenerate `(T, n, N)`:
1. `integerThetaBaseLoop T n N = circlePoly g₀ * circleCoord ^ k * star (circlePoly h₀)` and
   `integerThetaLaurentLoop T n N = circlePoly (g₀ ^ 2) * circleCoord ^ (2 * k) * star (circlePoly (h₀ ^ 2))`
   for explicit outer polynomials `g₀, h₀` zero-free on `closedBall 0 1` and
   `2 * k = fredholmIndex (integerThetaCollisionOperator T n N)`;
2. Both `wienerHopfLift (integerThetaLaurentLoop T n N)` and `integerThetaCollisionOperator T n N`
   factor exactly as `A * cayleyWienerHopf ^ (2 * k) * B` with explicit `L²(ℝ)` units `A, B`, so
   both are Fredholm and **surjective** on `L²(ℝ)` with exact kernel dimension `2 * k` and
   Fredholm index `2 * k`. -/
theorem exists_birkhoffSzego_factorization_integerTheta (T : ℝ) (n N : ℕ)
    (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0)
    (hellipse : ∀ z ∈ prefixEnclosedZeros T n N, ∀ w ∈ prefixEnclosedZeros T n N,
      zhukovskyEllipseForm n (z - w) ≠ 1) :
    let Z := prefixEnclosedZeros T n N
    let m : ℂ → ℕ := fun w => (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat
    let k : ℕ := ∑ z ∈ Z, ∑ w ∈ Z,
      m z * m w * (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0)
    ∃ g₀ h₀ : Polynomial ℂ,
      IsOuterPolynomial g₀ ∧ IsOuterPolynomial h₀ ∧
      integerThetaBaseLoop T n N =
        circlePoly g₀ * HTGeometry.circleCoord ^ k * star (circlePoly h₀) ∧
      integerThetaLaurentLoop T n N =
        circlePoly (g₀ ^ 2) * HTGeometry.circleCoord ^ (2 * k) * star (circlePoly (h₀ ^ 2)) ∧
      Function.Surjective (HTGeometry.wienerHopfLift (integerThetaLaurentLoop T n N)) ∧
      Module.rank ℂ (LinearMap.ker
        ((HTGeometry.wienerHopfLift (integerThetaLaurentLoop T n N) :
          HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real) :
          HTGeometry.L2Real →ₗ[ℂ] HTGeometry.L2Real)) = (2 * k : ℕ) ∧
      HTGeometry.IsFredholmOp (HTGeometry.wienerHopfLift (integerThetaLaurentLoop T n N)) ∧
      HTGeometry.fredholmIndex (HTGeometry.wienerHopfLift (integerThetaLaurentLoop T n N)) =
        (2 * (k : ℤ)) ∧
      Function.Surjective (integerThetaCollisionOperator T n N) ∧
      Module.rank ℂ (LinearMap.ker
        ((integerThetaCollisionOperator T n N :
          HTGeometry.L2Real →L[ℂ] HTGeometry.L2Real) :
          HTGeometry.L2Real →ₗ[ℂ] HTGeometry.L2Real)) = (2 * k : ℕ) ∧
      HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) = (2 * (k : ℤ)) ∧
      (IsUnit (HTGeometry.wienerHopfLift (integerThetaLaurentLoop T n N)) ↔ k = 0) ∧
      (IsUnit (integerThetaCollisionOperator T n N) ↔ k = 0) := by
  intro Z m k
  have hbdry0 : ∀ t : ℝ, finiteThetaShellPencil N 0
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0 := by
    simpa only [finiteThetaShellPencil_zero] using hbdry
  have hfun : finiteThetaShellPencil N 0 = _root_.RHTower.finiteThetaAmplitude N :=
    funext (finiteThetaShellPencil_zero N)
  have heval : ∀ x : ℂ, (integerThetaDifferencePoly T n N).eval x =
      ∏ z ∈ Z, ∏ w ∈ Z, (x - (z - w)) ^ (m z * m w) := by
    intro x
    have h := eval_pencilDifferencePoly_eq_prod T n N ⟨le_rfl, zero_le_one⟩ hbdry0 x
    simpa only [pencilDifferencePoly_zero, prefixEnclosedZeros, hfun] using h
  -- For each pair `(z, w) ∈ Z ×ˢ Z`, extract its outer polynomials and coordinate degree `0` or `1`.
  have hpair : ∀ p : {p : ℂ × ℂ // p ∈ Z ×ˢ Z},
      ∃ g_p h_p : Polynomial ℂ, IsOuterPolynomial g_p ∧ IsOuterPolynomial h_p ∧
        let e : ℕ := if zhukovskyEllipseForm n (p.1.1 - p.1.2) < 1 then 1 else 0
        ∀ u : HTGeometry.UnitCircle,
          zhukovskyLoop n u - (p.1.1 - p.1.2) =
            circlePoly g_p u * (HTGeometry.circleCoord ^ e) u * star (circlePoly h_p u) := by
    intro p
    obtain ⟨hz, hw⟩ := Finset.mem_product.mp p.2
    by_cases hlt : zhukovskyEllipseForm n (p.1.1 - p.1.2) < 1
    · obtain ⟨q, hq_out, hq_eq⟩ := exists_zhukovsky_outer_factorization_of_lt_one hlt
      refine ⟨1, q, isOuterPolynomial_one, hq_out, fun u => ?_⟩
      simp only [if_pos hlt, pow_one, circlePoly_one, ContinuousMap.one_apply, one_mul]
      exact hq_eq u
    · have hgt : 1 < zhukovskyEllipseForm n (p.1.1 - p.1.2) :=
        lt_of_le_of_ne (not_lt.mp hlt) (hellipse p.1.1 hz p.1.2 hw).symm
      obtain ⟨g_p, h_p, hg_out, hh_out, hgh_eq⟩ :=
        exists_zhukovsky_outer_factorization_of_gt_one hgt
      refine ⟨g_p, h_p, hg_out, hh_out, fun u => ?_⟩
      simp only [if_neg hlt, pow_zero, ContinuousMap.one_apply, mul_one]
      exact hgh_eq u
  choose gF hF hgF hhF hpair_eq using hpair
  let S := (Z ×ˢ Z).attach
  let mult : {p : ℂ × ℂ // p ∈ Z ×ˢ Z} → ℕ := fun p => m p.1.1 * m p.1.2
  let deg : {p : ℂ × ℂ // p ∈ Z ×ˢ Z} → ℕ :=
    fun p => if zhukovskyEllipseForm n (p.1.1 - p.1.2) < 1 then 1 else 0
  let g₀ : Polynomial ℂ := ∏ p ∈ S, gF p ^ mult p
  let h₀ : Polynomial ℂ := ∏ p ∈ S, hF p ^ mult p
  have hg₀_out : IsOuterPolynomial g₀ := by
    dsimp only [g₀]
    induction S using Finset.induction_on with
    | empty => simpa using isOuterPolynomial_one
    | @insert p s hp ih =>
        rw [Finset.prod_insert hp]
        exact isOuterPolynomial_mul (isOuterPolynomial_pow (hgF p) _) ih
  have hh₀_out : IsOuterPolynomial h₀ := by
    dsimp only [h₀]
    induction S using Finset.induction_on with
    | empty => simpa using isOuterPolynomial_one
    | @insert p s hp ih =>
        rw [Finset.prod_insert hp]
        exact isOuterPolynomial_mul (isOuterPolynomial_pow (hhF p) _) ih
  have hk_sum : ∑ p ∈ S, mult p * deg p = k := by
    dsimp only [S, mult, deg, k]
    rw [Finset.sum_attach (Z ×ˢ Z)
      (fun x : ℂ × ℂ => m x.1 * m x.2 *
        (if zhukovskyEllipseForm n (x.1 - x.2) < 1 then 1 else 0)),
      Finset.sum_product]
  have hbase_eq : integerThetaBaseLoop T n N =
      circlePoly g₀ * HTGeometry.circleCoord ^ k * star (circlePoly h₀) := by
    ext u
    change (integerThetaDifferencePoly T n N).eval (zhukovskyLoop n u) =
      circlePoly g₀ u * (HTGeometry.circleCoord ^ k) u * star (circlePoly h₀ u)
    rw [heval (zhukovskyLoop n u), ← Finset.prod_product',
      ← Finset.prod_attach (Z ×ˢ Z)
        (fun x : ℂ × ℂ => (zhukovskyLoop n u - (x.1 - x.2)) ^ (m x.1 * m x.2))]
    have hterm : ∀ p ∈ S,
        (zhukovskyLoop n u - (p.1.1 - p.1.2)) ^ mult p =
          (gF p ^ mult p).eval (u : ℂ) *
            ((HTGeometry.circleCoord u) ^ (mult p * deg p)) *
            star ((hF p ^ mult p).eval (u : ℂ)) := by
      intro p _
      rw [hpair_eq p u, mul_pow, mul_pow, Polynomial.eval_pow, Polynomial.eval_pow, star_pow]
      congr 2
      rw [ContinuousMap.coe_pow, Pi.pow_apply, ← pow_mul, mul_comm (deg p) (mult p)]
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    have hg_eval : (∏ p ∈ S, (gF p ^ mult p).eval (u : ℂ)) = circlePoly g₀ u := by
      rw [circlePoly_apply]; dsimp only [g₀]; rw [Polynomial.eval_prod]
    have hh_eval : (∏ p ∈ S, star ((hF p ^ mult p).eval (u : ℂ))) = star (circlePoly h₀ u) := by
      rw [circlePoly_apply]; dsimp only [h₀]; rw [Polynomial.eval_prod]
      change _ = (starRingEnd ℂ) (∏ p ∈ S, (hF p ^ mult p).eval (u : ℂ))
      rw [map_prod]; rfl
    have hcoord_eval : (∏ p ∈ S, (HTGeometry.circleCoord u) ^ (mult p * deg p)) =
        (HTGeometry.circleCoord ^ k) u := by
      rw [← Finset.pow_sum, hk_sum, ContinuousMap.coe_pow, Pi.pow_apply]
    rw [hg_eval, hh_eval, hcoord_eval]
  have hlaurent_eq : integerThetaLaurentLoop T n N =
      circlePoly (g₀ ^ 2) * HTGeometry.circleCoord ^ (2 * k) * star (circlePoly (h₀ ^ 2)) := by
    unfold integerThetaLaurentLoop
    rw [hbase_eq, circlePoly_pow, circlePoly_pow, star_pow]
    ext u
    simp only [ContinuousMap.coe_pow, ContinuousMap.coe_mul, ContinuousMap.star_apply,
      Pi.pow_apply, Pi.mul_apply]
    rw [pow_mul (HTGeometry.circleCoord u) 2 k]
    ring
  -- Factor the unnormalized Wiener–Hopf operator `wienerHopfLift (integerThetaLaurentLoop T n N)`.
  let G2 := g₀ ^ 2
  let H2 := h₀ ^ 2
  have hG2_out : IsOuterPolynomial G2 := isOuterPolynomial_pow hg₀_out 2
  have hH2_out : IsOuterPolynomial H2 := isOuterPolynomial_pow hh₀_out 2
  let A_un := HTGeometry.wienerHopfLift (circlePoly G2)
  let A_un_inv := HTGeometry.wienerHopfLift (circlePolyInv G2 hG2_out)
  let B_un := HTGeometry.wienerHopfLift (star (circlePoly H2))
  let B_un_inv := HTGeometry.wienerHopfLift (star (circlePolyInv H2 hH2_out))
  have hA_un_R : A_un * A_un_inv = 1 := by
    dsimp only [A_un, A_un_inv]
    rw [← wienerHopfLift_hardyPlus_mul (hankelPlus_circlePoly_eq_zero G2),
      circlePoly_mul_inv, HTGeometry.wienerHopfLift_one]
  have hA_un_L : A_un_inv * A_un = 1 := by
    dsimp only [A_un, A_un_inv]
    rw [← wienerHopfLift_hardyPlus_mul (hankelPlus_circlePolyInv_eq_zero G2 hG2_out),
      circlePolyInv_mul, HTGeometry.wienerHopfLift_one]
  have hB_un_R : B_un * B_un_inv = 1 := by
    dsimp only [B_un, B_un_inv]
    rw [← wienerHopfLift_mul_star_hardyPlus _ (hankelPlus_circlePolyInv_eq_zero H2 hH2_out),
      ← star_mul, circlePolyInv_mul, star_one, HTGeometry.wienerHopfLift_one]
  have hB_un_L : B_un_inv * B_un = 1 := by
    dsimp only [B_un, B_un_inv]
    rw [← wienerHopfLift_mul_star_hardyPlus _ (hankelPlus_circlePoly_eq_zero H2),
      ← star_mul, circlePoly_mul_inv, star_one, HTGeometry.wienerHopfLift_one]
  have hWH_un_eq : HTGeometry.wienerHopfLift (integerThetaLaurentLoop T n N) =
      A_un * HTGeometry.cayleyWienerHopf ^ (2 * k) * B_un := by
    rw [hlaurent_eq, mul_assoc (circlePoly G2),
      wienerHopfLift_hardyPlus_mul (hankelPlus_circlePoly_eq_zero G2),
      wienerHopfLift_mul_star_hardyPlus _ (hankelPlus_circlePoly_eq_zero H2),
      HTGeometry.wienerHopfLift_circleCoord_pow, ← mul_assoc]
  obtain ⟨hsurj_un, hrank_un, hfred_un, hind_un, hunit_un⟩ :=
    fredholm_and_kernel_of_sandwiched_cayleyPow hA_un_R hA_un_L hB_un_R hB_un_L (2 * k)
  rw [← hWH_un_eq] at hsurj_un hrank_un hfred_un hind_un hunit_un
  -- Factor the normalized collision operator `integerThetaCollisionOperator T n N` as well!
  let Φ := circlePoly g₀ * circlePolyInv h₀ hh₀_out
  let Φ_inv := circlePoly h₀ * circlePolyInv g₀ hg₀_out
  have hΦ_hardy : HTGeometry.hankelPlus Φ = 0 :=
    inHardyPlus_mul (hankelPlus_circlePoly_eq_zero g₀)
      (hankelPlus_circlePolyInv_eq_zero h₀ hh₀_out)
  have hΦ_inv_hardy : HTGeometry.hankelPlus Φ_inv = 0 :=
    inHardyPlus_mul (hankelPlus_circlePoly_eq_zero h₀)
      (hankelPlus_circlePolyInv_eq_zero g₀ hg₀_out)
  have hΦ_mul : Φ * Φ_inv = 1 := by
    dsimp only [Φ, Φ_inv]
    calc (circlePoly g₀ * circlePolyInv h₀ hh₀_out) * (circlePoly h₀ * circlePolyInv g₀ hg₀_out)
        = (circlePoly g₀ * circlePolyInv g₀ hg₀_out) * (circlePoly h₀ * circlePolyInv h₀ hh₀_out) := by
          ring
      _ = 1 := by rw [circlePoly_mul_inv, circlePoly_mul_inv, mul_one]
  have hΦ_inv_mul : Φ_inv * Φ = 1 := by rw [mul_comm, hΦ_mul]
  have hloop_nz : ∀ u : HTGeometry.UnitCircle, integerThetaLaurentLoop T n N u ≠ 0 := by
    intro u
    rw [hlaurent_eq]
    simp only [ContinuousMap.coe_mul, ContinuousMap.coe_pow, ContinuousMap.star_apply,
      Pi.mul_apply, Pi.pow_apply, circlePoly_apply]
    have hu_ne : (u : ℂ) ≠ 0 := by
      intro h0
      have h1 := HTGeometry.norm_coe_unitCircle u
      rw [h0, norm_zero] at h1
      exact zero_ne_one h1
    exact mul_ne_zero
      (mul_ne_zero (hG2_out (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le)
        (pow_ne_zero (2 * k) hu_ne))
      (star_ne_zero.mpr (hH2_out (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le))
  have hsym_eq : integerThetaCollisionSymbol T n N =
      Φ * HTGeometry.circleCoord ^ (2 * k) * star Φ_inv := by
    ext u
    unfold integerThetaCollisionSymbol
    rw [unitNormalizeSymbol_apply_of_ne_zero hloop_nz, hlaurent_eq]
    simp only [ContinuousMap.coe_mul, ContinuousMap.coe_pow, ContinuousMap.star_apply,
      Pi.mul_apply, Pi.pow_apply, circlePoly_apply, circlePoly_pow]
    set gu := g₀.eval (u : ℂ)
    set hu := h₀.eval (u : ℂ)
    have hgu_ne : gu ≠ 0 := hg₀_out (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le
    have hhu_ne : hu ≠ 0 := hh₀_out (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le
    have hnorm_eq : (‖gu ^ 2 * (HTGeometry.circleCoord u) ^ (2 * k) * (star hu) ^ 2‖ : ℂ) =
        (gu * star gu) * (hu * star hu) := by
      rw [norm_mul, norm_mul, norm_pow, norm_pow, norm_pow, Complex.star_def, Complex.norm_conj,
        show ‖HTGeometry.circleCoord u‖ = 1 from HTGeometry.norm_coe_unitCircle u,
        one_pow, mul_one, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow,
        ← Complex.mul_conj', ← Complex.mul_conj']
    change (gu ^ 2 * (HTGeometry.circleCoord u) ^ (2 * k) * (star hu) ^ 2) /
        (‖gu ^ 2 * (HTGeometry.circleCoord u) ^ (2 * k) * (star hu) ^ 2‖ : ℂ) =
      (gu * hu⁻¹) * (HTGeometry.circleCoord u) ^ (2 * k) * (star hu * (star gu)⁻¹)
    rw [hnorm_eq]
    have hsg_ne : star gu ≠ 0 := star_ne_zero.mpr hgu_ne
    have hsh_ne : star hu ≠ 0 := star_ne_zero.mpr hhu_ne
    field_simp [hgu_ne, hhu_ne, hsg_ne, hsh_ne]
    ring
  let A_nm := HTGeometry.wienerHopfLift Φ
  let A_nm_inv := HTGeometry.wienerHopfLift Φ_inv
  let B_nm := HTGeometry.wienerHopfLift (star Φ_inv)
  let B_nm_inv := HTGeometry.wienerHopfLift (star Φ)
  have hA_nm_R : A_nm * A_nm_inv = 1 := by
    dsimp only [A_nm, A_nm_inv]
    rw [← wienerHopfLift_hardyPlus_mul hΦ_hardy, hΦ_mul, HTGeometry.wienerHopfLift_one]
  have hA_nm_L : A_nm_inv * A_nm = 1 := by
    dsimp only [A_nm, A_nm_inv]
    rw [← wienerHopfLift_hardyPlus_mul hΦ_inv_hardy, hΦ_inv_mul, HTGeometry.wienerHopfLift_one]
  have hB_nm_R : B_nm * B_nm_inv = 1 := by
    dsimp only [B_nm, B_nm_inv]
    rw [← wienerHopfLift_mul_star_hardyPlus _ hΦ_hardy, ← star_mul, hΦ_mul, star_one,
      HTGeometry.wienerHopfLift_one]
  have hB_nm_L : B_nm_inv * B_nm = 1 := by
    dsimp only [B_nm, B_nm_inv]
    rw [← wienerHopfLift_mul_star_hardyPlus _ hΦ_inv_hardy, ← star_mul, hΦ_inv_mul, star_one,
      HTGeometry.wienerHopfLift_one]
  have hWH_nm_eq : integerThetaCollisionOperator T n N =
      A_nm * HTGeometry.cayleyWienerHopf ^ (2 * k) * B_nm := by
    unfold integerThetaCollisionOperator
    rw [hsym_eq, mul_assoc Φ,
      wienerHopfLift_hardyPlus_mul hΦ_hardy,
      wienerHopfLift_mul_star_hardyPlus _ hΦ_inv_hardy,
      HTGeometry.wienerHopfLift_circleCoord_pow, ← mul_assoc]
  obtain ⟨hsurj_nm, hrank_nm, _, hind_nm, hunit_nm⟩ :=
    fredholm_and_kernel_of_sandwiched_cayleyPow hA_nm_R hA_nm_L hB_nm_R hB_nm_L (2 * k)
  rw [← hWH_nm_eq] at hsurj_nm hrank_nm hind_nm hunit_nm
  have hk2_iff : (2 * k = 0) ↔ k = 0 := by omega
  exact ⟨g₀, h₀, hg₀_out, hh₀_out, hbase_eq, hlaurent_eq,
    hsurj_un, hrank_un, hfred_un, by push_cast at hind_un; exact hind_un,
    hsurj_nm, hrank_nm, by push_cast at hind_nm; exact hind_nm,
    hunit_un.trans hk2_iff, hunit_nm.trans hk2_iff⟩

/-- **Six-way Szegő positivity and operator-invertibility equivalence (`List.TFAE`).**
At every boundary-regular, ellipse-nondegenerate `(T, n, N)`, the following six conditions are
unconditionally equivalent:
1. `fredholmIndex (integerThetaCollisionOperator T n N) < 2`;
2. `fredholmIndex (integerThetaCollisionOperator T n N) = 0`;
3. `IsUnit (integerThetaCollisionOperator T n N)` on `L²(ℝ)`;
4. `IsUnit (wienerHopfLift (integerThetaLaurentLoop T n N))` on `L²(ℝ)`;
5. Outer polynomial Szegő factorization `integerThetaLaurentLoop T n N = circlePoly G * star (circlePoly H)`
   with `IsOuterPolynomial G` and `IsOuterPolynomial H`;
6. Devinatz–Widom closed-disk unit sectoriality: `∃ F, IsDiskUnit F ∧ ∀ u, 0 < (F u * Λ u).re`. -/
theorem integerTheta_szego_positivity_tfae (T : ℝ) (n N : ℕ)
    (hbdry : ∀ t : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (thetaWindowLowerLeft n) (thetaWindowUpperRight T n) t) ≠ 0)
    (hellipse : ∀ z ∈ prefixEnclosedZeros T n N, ∀ w ∈ prefixEnclosedZeros T n N,
      zhukovskyEllipseForm n (z - w) ≠ 1) :
    [ HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) < 2,
      HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) = 0,
      IsUnit (integerThetaCollisionOperator T n N),
      IsUnit (HTGeometry.wienerHopfLift (integerThetaLaurentLoop T n N)),
      ∃ G H : Polynomial ℂ, IsOuterPolynomial G ∧ IsOuterPolynomial H ∧
        integerThetaLaurentLoop T n N = circlePoly G * star (circlePoly H),
      ∃ F : ℂ → ℂ, IsDiskUnit F ∧
        ∀ u : HTGeometry.UnitCircle, 0 < (F (u : ℂ) * integerThetaLaurentLoop T n N u).re
    ].TFAE := by
  obtain ⟨g₀, h₀, hg₀, hh₀, _, hlaurent, _, _, _, _, _, _, hind_nm, hunit_un, hunit_nm⟩ :=
    exists_birkhoffSzego_factorization_integerTheta T n N hbdry hellipse
  set k : ℕ := ∑ z ∈ prefixEnclosedZeros T n N, ∑ w ∈ prefixEnclosedZeros T n N,
    (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) z).toNat *
      (analyticOrderAt (_root_.RHTower.finiteThetaAmplitude N) w).toNat *
      (if zhukovskyEllipseForm n (z - w) < 1 then 1 else 0)
  tfae_have 1 → 2 := by
    intro hlt
    rw [hind_nm] at hlt ⊢
    omega
  tfae_have 2 → 3 := by
    intro h0
    rw [hind_nm] at h0
    exact hunit_nm.mpr (by omega)
  tfae_have 3 → 4 := fun hu => hunit_un.mpr (hunit_nm.mp hu)
  tfae_have 4 → 5 := by
    intro hu
    have hk0 : k = 0 := hunit_un.mp hu
    refine ⟨g₀ ^ 2, h₀ ^ 2, isOuterPolynomial_pow hg₀ 2, isOuterPolynomial_pow hh₀ 2, ?_⟩
    rw [hlaurent, hk0, mul_zero, pow_zero, mul_one]
  tfae_have 5 → 6 := by
    rintro ⟨G, H, hG, hH, hGH⟩
    let F : ℂ → ℂ := fun z => (G.eval z)⁻¹ * H.eval z
    have hF_disk : IsDiskUnit F := by
      refine ⟨?_, ?_⟩
      · refine (G.continuous.continuousOn.inv₀ ?_).mul H.continuous.continuousOn
        intro z hz
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        exact hG z hz
      · intro z hz
        rw [Metric.mem_closedBall, dist_zero_right] at hz
        exact mul_ne_zero (inv_ne_zero (hG z hz)) (hH z hz)
    refine ⟨F, hF_disk, fun u => ?_⟩
    rw [hGH]
    simp only [F, ContinuousMap.coe_mul, ContinuousMap.star_apply, circlePoly_apply]
    have hGu_ne : G.eval (u : ℂ) ≠ 0 := hG (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le
    have hHu_ne : H.eval (u : ℂ) ≠ 0 := hH (u : ℂ) (HTGeometry.norm_coe_unitCircle u).le
    have hprod : ((G.eval (u : ℂ))⁻¹ * H.eval (u : ℂ)) *
        (G.eval (u : ℂ) * star (H.eval (u : ℂ))) =
        H.eval (u : ℂ) * star (H.eval (u : ℂ)) := by
      field_simp [hGu_ne]; ring
    rw [hprod, Complex.star_def, Complex.mul_conj', Complex.ofReal_re]
    exact sq_pos_of_pos (norm_pos_iff.mpr hHu_ne)
  tfae_have 6 → 1 := by
    rintro ⟨F, hF, hpos⟩
    have h0 := (fredholmIndex_eq_zero_of_diskUnit_re_pos (integerThetaLaurentLoop T n N) hF hpos).2
    change HTGeometry.fredholmIndex (integerThetaCollisionOperator T n N) < 2
    rw [integerThetaCollisionOperator, integerThetaCollisionSymbol, h0]
    norm_num
  tfae_finish

/-- **Unconditional `RiemannHypothesis` equivalence with Szegő positivity and `L²(ℝ)` invertibility
at the source-intrinsic stopping prefix.**
`RiemannHypothesis` holds if and only if on every natural-height window `m : ℕ`, for all
sufficiently fine Zhukovsky scales `n`, the integer-theta Laurent loop at
`sourceLoopStoppingPrefix (m : ℝ) n` admits Devinatz–Widom closed-disk Szegő positivity (and
equivalently outer polynomial Szegő factorization and `L²(ℝ)` Wiener–Hopf invertibility). -/
theorem riemannHypothesis_iff_szego_positivity_at_stoppingPrefix :
    [ RiemannHypothesis,
      ∀ m : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∃ F : ℂ → ℂ, IsDiskUnit F ∧
          ∀ u : HTGeometry.UnitCircle,
            0 < (F (u : ℂ) * integerThetaLaurentLoop (m : ℝ) n
              (sourceLoopStoppingPrefix (m : ℝ) n) u).re,
      ∀ m : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
        ∃ G H : Polynomial ℂ, IsOuterPolynomial G ∧ IsOuterPolynomial H ∧
          integerThetaLaurentLoop (m : ℝ) n (sourceLoopStoppingPrefix (m : ℝ) n) =
            circlePoly G * star (circlePoly H),
      ∀ m : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀,
        IsUnit (HTGeometry.wienerHopfLift
          (integerThetaLaurentLoop (m : ℝ) n (sourceLoopStoppingPrefix (m : ℝ) n)))
    ].TFAE := by
  tfae_have 1 → 2 := by
    intro hRH m
    refine ⟨thetaWindowScale (m : ℝ), fun n hn => ?_⟩
    set N := sourceLoopStoppingPrefix (m : ℝ) n
    obtain ⟨_, haf, _, hind⟩ := isArtifactFreeFrom_sourceLoopStoppingPrefix (m : ℝ) hn
    obtain ⟨hbdry, _, hnz, _⟩ := haf N le_rfl
    have hell := ellipse_nondegenerate_of_loop_ne_zero (m : ℝ) n N hbdry hnz
    have htfae := integerTheta_szego_positivity_tfae (m : ℝ) n N hbdry hell
    refine (htfae.out 1 5).mp ?_
    rw [hind,
      _root_.RHTower.riemannHypothesis_iff_forall_horizontalCollisionCharge_eq_zero.mp hRH (m : ℝ)]
    rfl
  tfae_have 2 → 3 := by
    intro h m
    obtain ⟨n₀, hn₀⟩ := h m
    refine ⟨max n₀ (thetaWindowScale (m : ℝ)), fun n hn => ?_⟩
    set N := sourceLoopStoppingPrefix (m : ℝ) n
    obtain ⟨_, haf, _, _⟩ :=
      isArtifactFreeFrom_sourceLoopStoppingPrefix (m : ℝ) ((le_max_right _ _).trans hn)
    obtain ⟨hbdry, _, hnz, _⟩ := haf N le_rfl
    have hell := ellipse_nondegenerate_of_loop_ne_zero (m : ℝ) n N hbdry hnz
    have htfae := integerTheta_szego_positivity_tfae (m : ℝ) n N hbdry hell
    exact (htfae.out 5 4).mp (hn₀ n ((le_max_left _ _).trans hn))
  tfae_have 3 → 4 := by
    intro h m
    obtain ⟨n₀, hn₀⟩ := h m
    refine ⟨max n₀ (thetaWindowScale (m : ℝ)), fun n hn => ?_⟩
    set N := sourceLoopStoppingPrefix (m : ℝ) n
    obtain ⟨_, haf, _, _⟩ :=
      isArtifactFreeFrom_sourceLoopStoppingPrefix (m : ℝ) ((le_max_right _ _).trans hn)
    obtain ⟨hbdry, _, hnz, _⟩ := haf N le_rfl
    have hell := ellipse_nondegenerate_of_loop_ne_zero (m : ℝ) n N hbdry hnz
    have htfae := integerTheta_szego_positivity_tfae (m : ℝ) n N hbdry hell
    exact (htfae.out 4 3).mp (hn₀ n ((le_max_left _ _).trans hn))
  tfae_have 4 → 1 := by
    intro h
    rw [riemannHypothesis_iff_forall_nat_sourceLoopStoppingPrefix_index_eq_zero]
    intro m
    obtain ⟨n₀, hn₀⟩ := h m
    refine ⟨max n₀ (thetaWindowScale (m : ℝ)), fun n hn => ?_⟩
    set N := sourceLoopStoppingPrefix (m : ℝ) n
    obtain ⟨_, haf, _, _⟩ :=
      isArtifactFreeFrom_sourceLoopStoppingPrefix (m : ℝ) ((le_max_right _ _).trans hn)
    obtain ⟨hbdry, _, hnz, _⟩ := haf N le_rfl
    have hell := ellipse_nondegenerate_of_loop_ne_zero (m : ℝ) n N hbdry hnz
    have htfae := integerTheta_szego_positivity_tfae (m : ℝ) n N hbdry hell
    exact (htfae.out 3 1).mp (hn₀ n ((le_max_left _ _).trans hn))
  tfae_finish

end GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.conj_integerThetaWindowPowerSum_eq
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.integerThetaDifferencePoly_real_and_loop_symmetric
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.fredholmIndex_eq_zero_of_diskUnit_re_pos
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.isUnit_wienerHopfLift_of_re_pos
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.hankelPlus_circlePolyInv_eq_zero
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.exists_birkhoffSzego_factorization_integerTheta
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.integerTheta_szego_positivity_tfae
#print axioms GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.riemannHypothesis_iff_szego_positivity_at_stoppingPrefix
