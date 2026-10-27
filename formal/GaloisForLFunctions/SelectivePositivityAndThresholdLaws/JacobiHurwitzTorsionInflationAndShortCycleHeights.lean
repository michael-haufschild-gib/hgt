import GaloisForLFunctions.ArithmeticEffectivityTheory.TheEffectivityCalculus
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheThetaSurface
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheBaseDoesNotExtend
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheStripLivesOnShortCycles
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SourceDeterminantalSectionsAndArithmeticRiemannRoch

/-!
# Jacobi–Hurwitz Torsion Inflation and Subquadratic Heights on Short Cycles

This module resolves the biarithmetic subquadratic naive-height problem and its converse
large-sieve torsion-inflation obstruction:

1. **Exact Tate-limit decomposition of torsion-weighted Jacobi–Hurwitz heights
   (`abs_jacobiHurwitzHeight_sub_quad_le`, `neg_errorBound_le_jacobiHurwitzHeight`):**
   Every finite packet `P` of shifted Jacobi–Hurwitz theta log-heights
   `h_P(x) = ∑_i w_i log ϑ(b_i; J_i(x), t_i)` (`w_i > 0`, `t_i > 0`) decomposes as
   `h_P(x) = q_P(x) + O_P(1)` where `q_P(x) = ∑_i w_i π J_i(x)² / t_i ≥ 0` is homogeneous quadratic
   and `h_P(x) ≥ -B_P` holds unconditionally without any `ℕ`-valuedness or vector-space structure.

2. **Generalized Weil argument for asymptotic Riemann inequalities
   (`hodgeIndex_of_asymptoticRiemannInequality`):**
   Replacing the exact Riemann inequality by the `-o(n²)` asymptotic Riemann inequality along rays,
   combined with subquadratic degree-zero growth, still unconditionally forces `S.HodgeIndex`.

3. **Sharp dichotomy for torsion-weighted Jacobi–Hurwitz functionals (`jacobiHurwitzHeight_dichotomy`):**
   Either `q_P` vanishes identically on `ker(· A)` — in which case every linear functional `J_i`
   factors through the degree, `h_P` is bounded by `±B_P` on the entire degree-zero hyperplane
   (blind to every degree-zero short cycle) and fails the asymptotic Riemann inequality on any
   surface violating `HodgeIndex` (such as `goldenDatum`) — or there is a degree-zero cycle `z`
   along which `h_P(n z) ≥ α n² - B_P` inflates quadratically with `α = q_P(z) > 0`.

4. **Converse large-sieve inflation law (`jacobiHurwitz_largeSieve_inflation_ge_half_abs`):**
   Whenever torsion-character averaging / Cauchy–Schwarz produces an unsigned Riemann-inequality
   majorant (`UnsignedLargeSieveMajorant`), every degree-zero cycle `z` suffers quadratic inflation
   with rate `α(z) = q_P(z) ≥ (1 / 2) |z · z|`. Moreover, on every abundant degree-zero class
   (such as on `goldenDatum`), even the signed asymptotic Riemann inequality forces
   `q_P(z) ≥ (1 / 4) |z · z| > 0`.

5. **Unconditional existence on proved short-cycle windows vs global equivalence to RH
   (`shortCycle_subquadratic_height_exists_primeTwo`,
   `riemannHypothesis_iff_exists_asymptotic_subquadratic_height`):**
   On the primitive short-cycle subsurface `scalingSubsurface (primitiveSmoothRealTestsAt r)` for
   `r ≤ (log 2 + 1/50)/2` (including `r = 3/10`), an explicit nonnegative functional satisfying the
   Riemann inequality and vanishing identically in degree zero exists unconditionally; globally on
   `scalingSurface` (and equivalently on all dyadic short-cycle differences `g - T_{2^m} g` over
   `[-3/10, 3/10]`), existence of a bounded-below asymptotic subquadratic height is unconditionally
   equivalent to `RiemannHypothesis`.
-/

open Filter Real HurwitzZeta Finset MeasureTheory Set Zeta23
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.ArithmeticEffectivityTheory
open scoped BigOperators Topology

noncomputable section

namespace GaloisForLFunctions.SelectivePositivityAndThresholdLaws

set_option autoImplicit false

/-! ### 1. Torsion-Weighted Jacobi–Hurwitz Theta Packets and Tate-Limit Decomposition -/

/-- A finite torsion-weighted Jacobi–Hurwitz theta packet on a real module `E`: finitely many
channels `i : Fin m` with positive weights `w i > 0`, lattice/torsion shifts `b i : ℝ` (modeling
rational torsion characteristics `a ∈ ℚ` under dilation transformations), positive modular scales
`t i > 0`, and additive linear functionals `J i : E →ₗ[ℝ] ℝ`. -/
structure JacobiHurwitzTorsionPacket (E : Type*) [AddCommGroup E] [Module ℝ E] (m : ℕ) where
  w : Fin m → ℝ
  hw : ∀ i, 0 < w i
  b : Fin m → ℝ
  t : Fin m → ℝ
  ht : ∀ i, 0 < t i
  J : Fin m → (E →ₗ[ℝ] ℝ)

section Packet

variable {E : Type*} [AddCommGroup E] [Module ℝ E] {m : ℕ}

/-- The `i`-th shifted Jacobi–Hurwitz theta series
`∑_{n ∈ ℤ} exp(-π (n + b_i)² t_i + 2π (n + b_i) J_i(x))`. -/
def jacobiHurwitzChannelTheta (P : JacobiHurwitzTorsionPacket E m) (i : Fin m) (x : E) : ℝ :=
  ∑' n : ℤ, Real.exp (-Real.pi * ((n : ℝ) + P.b i) ^ 2 * P.t i +
    2 * Real.pi * ((n : ℝ) + P.b i) * P.J i x)

theorem jacobiHurwitzChannelTheta_eq (P : JacobiHurwitzTorsionPacket E m) (i : Fin m) (x : E) :
    jacobiHurwitzChannelTheta P i x =
      Real.exp (Real.pi * (P.J i x) ^ 2 / P.t i) *
        evenKernel ((P.b i - P.J i x / P.t i : ℝ) : UnitAddCircle) (P.t i) :=
  (hasSum_shifted_thetaChar (P.b i) (P.J i x) (P.ht i)).tsum_eq

theorem jacobiHurwitzChannelTheta_pos (P : JacobiHurwitzTorsionPacket E m) (i : Fin m) (x : E) :
    0 < jacobiHurwitzChannelTheta P i x := by
  rw [jacobiHurwitzChannelTheta_eq]
  exact mul_pos (Real.exp_pos _)
    (evenKernel_pos (P.b i - P.J i x / P.t i) (P.ht i))

/-- The torsion-weighted Jacobi–Hurwitz log-height `h_P(x) = ∑_i w_i log ϑ_i(x)`. -/
def jacobiHurwitzHeight (P : JacobiHurwitzTorsionPacket E m) (x : E) : ℝ :=
  ∑ i : Fin m, P.w i * Real.log (jacobiHurwitzChannelTheta P i x)

/-- The exact Tate-limit quadratic form `q_P(x) = ∑_i w_i π J_i(x)² / t_i` of `P`. -/
def jacobiHurwitzQuad (P : JacobiHurwitzTorsionPacket E m) (x : E) : ℝ :=
  ∑ i : Fin m, P.w i * (Real.pi * (P.J i x) ^ 2 / P.t i)

/-- Uniform bounded-distance constant `B_P ≥ 0` between `jacobiHurwitzHeight P` and
`jacobiHurwitzQuad P`. -/
def jacobiHurwitzErrorBound (P : JacobiHurwitzTorsionPacket E m) : ℝ :=
  ∑ i : Fin m, P.w i * max (Real.pi * P.t i / 4) (Real.log (evenKernel 0 (P.t i)))

theorem jacobiHurwitzQuad_nonneg (P : JacobiHurwitzTorsionPacket E m) (x : E) :
    0 ≤ jacobiHurwitzQuad P x :=
  sum_nonneg fun i _ => mul_nonneg (P.hw i).le
    (div_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) (P.ht i).le)

theorem jacobiHurwitzQuad_smul (P : JacobiHurwitzTorsionPacket E m) (c : ℝ) (x : E) :
    jacobiHurwitzQuad P (c • x) = c ^ 2 * jacobiHurwitzQuad P x := by
  simp only [jacobiHurwitzQuad, map_smul, smul_eq_mul, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  ring

theorem jacobiHurwitzQuad_neg (P : JacobiHurwitzTorsionPacket E m) (x : E) :
    jacobiHurwitzQuad P (-x) = jacobiHurwitzQuad P x := by
  simpa using jacobiHurwitzQuad_smul P (-1) x

theorem jacobiHurwitzErrorBound_nonneg (P : JacobiHurwitzTorsionPacket E m) :
    0 ≤ jacobiHurwitzErrorBound P :=
  sum_nonneg fun i _ => mul_nonneg (P.hw i).le
    (le_trans (by have := P.ht i; positivity) (le_max_left _ _))

/-- **Exact Tate-Limit Bounded-Distance Law for Shifted Torsion Theta Heights:**
For every `x : E`, `|h_P(x) - q_P(x)| ≤ B_P`. -/
theorem abs_jacobiHurwitzHeight_sub_quad_le (P : JacobiHurwitzTorsionPacket E m) (x : E) :
    |jacobiHurwitzHeight P x - jacobiHurwitzQuad P x| ≤ jacobiHurwitzErrorBound P := by
  unfold jacobiHurwitzHeight jacobiHurwitzQuad jacobiHurwitzErrorBound
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  have hk_pos : 0 < evenKernel ((P.b i - P.J i x / P.t i : ℝ) : UnitAddCircle) (P.t i) :=
    evenKernel_pos (P.b i - P.J i x / P.t i) (P.ht i)
  have hlog : Real.log (jacobiHurwitzChannelTheta P i x) - Real.pi * (P.J i x) ^ 2 / P.t i =
      Real.log (evenKernel ((P.b i - P.J i x / P.t i : ℝ) : UnitAddCircle) (P.t i)) := by
    rw [jacobiHurwitzChannelTheta_eq, Real.log_mul (Real.exp_pos _).ne' hk_pos.ne', Real.log_exp]
    ring
  rw [← mul_sub, hlog, abs_mul, abs_of_pos (P.hw i)]
  refine mul_le_mul_of_nonneg_left (abs_le.mpr ⟨?_, ?_⟩) (P.hw i).le
  · have hlo : -(Real.pi * P.t i / 4) ≤
        Real.log (evenKernel ((P.b i - P.J i x / P.t i : ℝ) : UnitAddCircle) (P.t i)) := by
      have h := Real.log_le_log (Real.exp_pos _)
        (exp_neg_le_evenKernel (P.b i - P.J i x / P.t i) (P.ht i))
      rw [Real.log_exp] at h
      linarith
    linarith [le_max_left (Real.pi * P.t i / 4) (Real.log (evenKernel 0 (P.t i)))]
  · have hhi : Real.log (evenKernel ((P.b i - P.J i x / P.t i : ℝ) : UnitAddCircle) (P.t i)) ≤
        Real.log (evenKernel 0 (P.t i)) :=
      Real.log_le_log hk_pos (evenKernel_le_evenKernel_zero (P.b i - P.J i x / P.t i) (P.ht i))
    linarith [le_max_right (Real.pi * P.t i / 4) (Real.log (evenKernel 0 (P.t i)))]

/-- Every torsion-weighted Jacobi–Hurwitz functional satisfies the uniform lower bound
`-B_P ≤ h_P(x)` unconditionally on all of `E`. -/
theorem neg_errorBound_le_jacobiHurwitzHeight (P : JacobiHurwitzTorsionPacket E m) (x : E) :
    -jacobiHurwitzErrorBound P ≤ jacobiHurwitzHeight P x := by
  have habs := (abs_le.mp (abs_jacobiHurwitzHeight_sub_quad_le P x)).1
  have hq := jacobiHurwitzQuad_nonneg P x
  linarith

/-! ### 2. Asymptotic Riemann Inequality and Generalized Weil Argument -/

/-- Uniform lower boundedness `h(x) ≥ -C` on `E` (requiring no `ℕ`-valuedness or vector space). -/
def BoundedBelowFunctional (h : E → ℝ) : Prop :=
  ∃ C : ℝ, ∀ x : E, -C ≤ h x

/-- Asymptotic Riemann inequality along rays: for every class `x : E` and `ε > 0`, eventually
`h(n x) + h(κ - n x) ≥ χ₀ + ½ (n x · (n x - κ)) - ε n²`. -/
def AsymptoticRiemannInequality (S : PolarSurface E) (κ : E) (χ₀ : ℝ) (h : E → ℝ) : Prop :=
  ∀ (x : E) (ε : ℝ), 0 < ε → ∀ᶠ n : ℕ in atTop,
    eulerChar S κ χ₀ ((n : ℝ) • x) - ε * (n : ℝ) ^ 2 ≤ h ((n : ℝ) • x) + h (κ - (n : ℝ) • x)

/-- Single-ray subquadratic growth on degree-zero classes:
`limsup_{n → ∞} n^{-2} h(n z) ≤ 0` whenever `z · A = 0`. -/
def SingleRayDegreeZeroSubquadratic (S : PolarSurface E) (h : E → ℝ) : Prop :=
  ∀ z : E, S.pair z S.ample = 0 → ∀ c : ℝ, 0 < c →
    ∀ᶠ n : ℕ in atTop, h ((n : ℝ) • z) ≤ c * (n : ℝ) ^ 2

theorem asymptoticRiemannInequality_of_riemannInequality (S : PolarSurface E)
    {κ : E} {χ₀ : ℝ} {h : E → ℝ} (hRI : RiemannInequality S κ χ₀ h) :
    AsymptoticRiemannInequality S κ χ₀ h := by
  intro x ε hε
  filter_upwards with n
  have h1 := hRI ((n : ℝ) • x)
  have h2 : 0 ≤ ε * (n : ℝ) ^ 2 := mul_nonneg hε.le (sq_nonneg _)
  linarith

theorem degreeZeroSubquadratic_zero_of_singleRay (S : PolarSurface E) {h : E → ℝ}
    (hsub : SingleRayDegreeZeroSubquadratic S h) :
    DegreeZeroSubquadratic S 0 h := by
  intro z hz c hc
  have hz_neg : S.pair (-z) S.ample = 0 := by rw [map_neg, LinearMap.neg_apply, hz, neg_zero]
  refine Eventually.frequently ?_
  filter_upwards [hsub z hz (c / 3) (by positivity),
    hsub (-z) hz_neg (c / 3) (by positivity), eventually_gt_atTop 0] with n h1 h2 hn0
  have hneg : (0 : E) - (n : ℝ) • z = (n : ℝ) • (-z) := by simp [smul_neg]
  rw [hneg]
  have hn_pos : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hn0) 2
  nlinarith

/-- **Generalized Weil Argument (`-o(n²)` Asymptotic Riemann Inequality):**
Any functional `h : E → ℝ` satisfying `AsymptoticRiemannInequality S κ χ₀ h` and
`DegreeZeroSubquadratic S κ h` unconditionally forces `S.HodgeIndex`. -/
theorem hodgeIndex_of_asymptoticRiemannInequality (S : PolarSurface E)
    {κ : E} {χ₀ : ℝ} {h : E → ℝ}
    (hARI : AsymptoticRiemannInequality S κ χ₀ h)
    (hsub : DegreeZeroSubquadratic S κ h) :
    S.HodgeIndex := by
  suffices hAmple : S.AmpleHodgeIndex from
    S.hodgeIndex_iff_castelnuovoSeveri.mpr (S.ampleHodgeIndex_iff_castelnuovoSeveri.mp hAmple)
  intro x hx
  by_contra hpos
  push Not at hpos
  have hquarter : 0 < S.pair x x / 8 := by linarith
  have hev_lo : ∀ᶠ n : ℕ in atTop,
      (S.pair x x / 4) * (n : ℝ) ^ 2 ≤ h ((n : ℝ) • x) + h (κ - (n : ℝ) • x) := by
    filter_upwards [hARI x (S.pair x x / 8) hquarter,
      eventually_affine_lt_quadratic hquarter (S.pair x κ / 2) (-χ₀)] with n h1 h2
    rw [eulerChar_smul] at h1
    nlinarith
  obtain ⟨n, hn_hi, hn_lo⟩ := ((hsub x hx (S.pair x x / 8) hquarter).and_eventually hev_lo).exists
  nlinarith [sq_nonneg (n : ℝ)]

/-! ### 3. Sharp Dichotomy & Converse Large-Sieve Inflation for Jacobi–Hurwitz Heights -/

/-- Exact characterization of degree-zero subquadraticity for `jacobiHurwitzHeight P`:
`h_P` has subquadratic degree-zero growth if and only if `q_P` vanishes identically on `ker(· A)`. -/
theorem jacobiHurwitzHeight_singleRaySubquadratic_iff (S : PolarSurface E)
    (P : JacobiHurwitzTorsionPacket E m) :
    SingleRayDegreeZeroSubquadratic S (jacobiHurwitzHeight P) ↔
      ∀ z : E, S.pair z S.ample = 0 → jacobiHurwitzQuad P z = 0 := by
  constructor
  · intro hsub z hz
    apply le_antisymm _ (jacobiHurwitzQuad_nonneg P z)
    by_contra hpos
    push Not at hpos
    obtain ⟨n, hn_hi, hn_err, hn0⟩ :=
      ((hsub z hz (jacobiHurwitzQuad P z / 2) (half_pos hpos)).and
        ((eventually_affine_lt_quadratic (by linarith : 0 < jacobiHurwitzQuad P z / 4) 0
          (jacobiHurwitzErrorBound P)).and (eventually_gt_atTop 0))).exists
    have habs := (abs_le.mp (abs_jacobiHurwitzHeight_sub_quad_le P ((n : ℝ) • z))).1
    rw [jacobiHurwitzQuad_smul] at habs
    have hn_sq : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hn0) 2
    nlinarith
  · intro hzero z hz c hc
    filter_upwards [eventually_affine_lt_quadratic hc 0 (jacobiHurwitzErrorBound P)] with n hn
    have habs := (abs_le.mp (abs_jacobiHurwitzHeight_sub_quad_le P ((n : ℝ) • z))).2
    rw [jacobiHurwitzQuad_smul, hzero z hz, mul_zero] at habs
    linarith

/-- **Sharp Dichotomy Theorem for Torsion-Weighted Jacobi–Hurwitz Heights:**
For every polar surface `S` and every packet `P : JacobiHurwitzTorsionPacket E m`, either:
1. *(Degree-zero collapse / blindness):* `SingleRayDegreeZeroSubquadratic S (jacobiHurwitzHeight P)`
   holds, every channel functional `P.J i` vanishes on `ker(· A)`, `|h_P(z)| ≤ B_P` is uniformly
   bounded across the entire degree-zero hyperplane, and `h_P` cannot satisfy
   `AsymptoticRiemannInequality S κ χ₀` unless `S.HodgeIndex` holds; or
2. *(Quadratic degree-zero inflation):* there exists `z` with `z · A = 0` and `α = q_P(z) > 0`
   such that `h_P(n z) ≥ α n² - B_P` for every `n : ℝ`. -/
theorem jacobiHurwitzHeight_dichotomy (S : PolarSurface E) (κ : E) (χ₀ : ℝ)
    (P : JacobiHurwitzTorsionPacket E m) :
    ((SingleRayDegreeZeroSubquadratic S (jacobiHurwitzHeight P) ∧
      (∀ z : E, S.pair z S.ample = 0 → ∀ i : Fin m, P.J i z = 0) ∧
      (∀ z : E, S.pair z S.ample = 0 → |jacobiHurwitzHeight P z| ≤ jacobiHurwitzErrorBound P) ∧
      (AsymptoticRiemannInequality S κ χ₀ (jacobiHurwitzHeight P) → S.HodgeIndex)) ∨
    (∃ z : E, S.pair z S.ample = 0 ∧ 0 < jacobiHurwitzQuad P z ∧
      ∀ n : ℝ, jacobiHurwitzQuad P z * n ^ 2 - jacobiHurwitzErrorBound P ≤
        jacobiHurwitzHeight P (n • z))) := by
  by_cases hvan : ∀ z : E, S.pair z S.ample = 0 → jacobiHurwitzQuad P z = 0
  · left
    have hsub : SingleRayDegreeZeroSubquadratic S (jacobiHurwitzHeight P) :=
      (jacobiHurwitzHeight_singleRaySubquadratic_iff S P).mpr hvan
    have hJ0 : ∀ z : E, S.pair z S.ample = 0 → ∀ i : Fin m, P.J i z = 0 := by
      intro z hz i
      have hq0 := hvan z hz
      unfold jacobiHurwitzQuad at hq0
      have hterm0 : P.w i * (Real.pi * (P.J i z) ^ 2 / P.t i) = 0 := by
        have hall := (sum_eq_zero_iff_of_nonneg fun j _ =>
          mul_nonneg (P.hw j).le
            (div_nonneg (mul_nonneg Real.pi_pos.le (sq_nonneg _)) (P.ht j).le)).mp hq0
        exact hall i (mem_univ i)
      have hdiv0 : Real.pi * (P.J i z) ^ 2 / P.t i = 0 :=
        (mul_eq_zero.mp hterm0).resolve_left (P.hw i).ne'
      have hmul0 : Real.pi * (P.J i z) ^ 2 = 0 :=
        (div_eq_zero_iff.mp hdiv0).resolve_right (P.ht i).ne'
      exact sq_eq_zero_iff.mp ((mul_eq_zero.mp hmul0).resolve_left Real.pi_ne_zero)
    have hbd0 : ∀ z : E, S.pair z S.ample = 0 →
        |jacobiHurwitzHeight P z| ≤ jacobiHurwitzErrorBound P := by
      intro z hz
      have h := abs_jacobiHurwitzHeight_sub_quad_le P z
      rwa [hvan z hz, sub_zero] at h
    refine ⟨hsub, hJ0, hbd0, fun hARI => ?_⟩
    refine hodgeIndex_of_asymptoticRiemannInequality S hARI ?_
    intro z hz c hc
    have hJ_κ : ∀ n : ℕ, jacobiHurwitzQuad P (κ - (n : ℝ) • z) = jacobiHurwitzQuad P κ := by
      intro n
      unfold jacobiHurwitzQuad
      refine sum_congr rfl fun i _ => ?_
      rw [map_sub, map_smul, smul_eq_mul, hJ0 z hz i, mul_zero, sub_zero]
    refine Eventually.frequently ?_
    filter_upwards [eventually_affine_lt_quadratic hc 0
      (jacobiHurwitzQuad P κ + 2 * jacobiHurwitzErrorBound P)] with n hn
    have h1 := (abs_le.mp (abs_jacobiHurwitzHeight_sub_quad_le P ((n : ℝ) • z))).2
    have h2 := (abs_le.mp (abs_jacobiHurwitzHeight_sub_quad_le P (κ - (n : ℝ) • z))).2
    rw [jacobiHurwitzQuad_smul, hvan z hz, mul_zero] at h1
    rw [hJ_κ n] at h2
    linarith
  · right
    push Not at hvan
    obtain ⟨z, hz, hne⟩ := hvan
    have hpos : 0 < jacobiHurwitzQuad P z :=
      lt_of_le_of_ne (jacobiHurwitzQuad_nonneg P z) (Ne.symm hne)
    refine ⟨z, hz, hpos, fun n => ?_⟩
    have habs := (abs_le.mp (abs_jacobiHurwitzHeight_sub_quad_le P (n • z))).1
    rw [jacobiHurwitzQuad_smul] at habs
    linarith

/-- Unsigned large-sieve Riemann-inequality envelope: torsion-character / Cauchy–Schwarz averaging
replaces the signed pairing `x · (x - κ)` by its unsigned modulus `|x · (x - κ)|`. -/
def UnsignedLargeSieveMajorant (S : PolarSurface E) (κ : E) (χ₀ : ℝ) (h : E → ℝ) : Prop :=
  ∀ (x : E) (ε : ℝ), 0 < ε → ∀ᶠ n : ℕ in atTop,
    χ₀ + |S.pair ((n : ℝ) • x) ((n : ℝ) • x - κ)| / 2 - ε * (n : ℝ) ^ 2 ≤ h ((n : ℝ) • x)

/-- **Affirmative Converse Large-Sieve Inflation Theorem (`α(z) ≥ ½ |z · z|`):**
Every torsion-weighted Jacobi–Hurwitz height `h_P` satisfying `UnsignedLargeSieveMajorant S κ χ₀`
suffers quadratic inflation along every degree-zero class `z` (`z · A = 0`) with exact leading
coefficient `q_P(z) ≥ (1 / 2) |z · z|`. -/
theorem jacobiHurwitz_largeSieve_inflation_ge_half_abs (S : PolarSurface E) (κ : E) (χ₀ : ℝ)
    (P : JacobiHurwitzTorsionPacket E m)
    (hLS : UnsignedLargeSieveMajorant S κ χ₀ (jacobiHurwitzHeight P))
    {z : E} (_hz : S.pair z S.ample = 0) :
    (1 / 2 : ℝ) * |S.pair z z| ≤ jacobiHurwitzQuad P z ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ((1 / 2 : ℝ) * |S.pair z z| - ε) * (n : ℝ) ^ 2 ≤
          jacobiHurwitzHeight P ((n : ℝ) • z) := by
  have hrate : (1 / 2 : ℝ) * |S.pair z z| ≤ jacobiHurwitzQuad P z := by
    by_contra hlt
    push Not at hlt
    set δ : ℝ := ((1 / 2 : ℝ) * |S.pair z z| - jacobiHurwitzQuad P z) / 3
    have hδ : 0 < δ := by dsimp [δ]; linarith
    obtain ⟨n, h1, h2, hn0⟩ :=
      ((hLS z δ hδ).and
        ((eventually_affine_lt_quadratic hδ (|S.pair z κ| / 2)
          (|χ₀| + jacobiHurwitzErrorBound P)).and (eventually_gt_atTop 0))).exists
    have habs_P := (abs_le.mp (abs_jacobiHurwitzHeight_sub_quad_le P ((n : ℝ) • z))).2
    rw [jacobiHurwitzQuad_smul] at habs_P
    have hpair_eq : S.pair ((n : ℝ) • z) ((n : ℝ) • z - κ) =
        (n : ℝ) ^ 2 * S.pair z z - (n : ℝ) * S.pair z κ := by
      simp only [map_sub, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    have habs_pair : (n : ℝ) ^ 2 * |S.pair z z| - (n : ℝ) * |S.pair z κ| ≤
        |S.pair ((n : ℝ) • z) ((n : ℝ) • z - κ)| := by
      rw [hpair_eq]
      have htri := abs_sub_abs_le_abs_sub ((n : ℝ) ^ 2 * S.pair z z) ((n : ℝ) * S.pair z κ)
      rwa [abs_mul, abs_mul, abs_of_nonneg (a := (n : ℝ) ^ 2) (sq_nonneg (n : ℝ)),
        abs_of_nonneg (a := (n : ℝ)) (Nat.cast_nonneg n)] at htri
    have hχ : -|χ₀| ≤ χ₀ := neg_abs_le χ₀
    have hn_sq : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hn0) 2
    have hcomb : jacobiHurwitzQuad P z * (n : ℝ) ^ 2 + jacobiHurwitzErrorBound P <
        ((1 / 2 : ℝ) * |S.pair z z| - δ) * (n : ℝ) ^ 2 -
          ((|S.pair z κ| / 2) * (n : ℝ) + |χ₀|) := by
      have h3δ : 3 * δ = (1 / 2 : ℝ) * |S.pair z z| - jacobiHurwitzQuad P z := by
        dsimp [δ]; ring
      nlinarith
    linarith
  refine ⟨hrate, fun ε hε => ?_⟩
  filter_upwards [eventually_affine_lt_quadratic hε 0 (jacobiHurwitzErrorBound P)] with n hn
  have habs_lo := (abs_le.mp (abs_jacobiHurwitzHeight_sub_quad_le P ((n : ℝ) • z))).1
  rw [jacobiHurwitzQuad_smul] at habs_lo
  have hmul := mul_le_mul_of_nonneg_left hrate (sq_nonneg (n : ℝ))
  nlinarith

/-- On any abundant class (`z · A = 0` and `z · z > 0`, e.g. on `goldenDatum`), even the signed
`AsymptoticRiemannInequality` forces `jacobiHurwitzQuad P z ≥ (1 / 4) |z · z| > 0`. -/
theorem jacobiHurwitzQuad_ge_quarter_of_abundant (S : PolarSurface E) (κ : E) (χ₀ : ℝ)
    (P : JacobiHurwitzTorsionPacket E m)
    (hARI : AsymptoticRiemannInequality S κ χ₀ (jacobiHurwitzHeight P))
    {z : E} (hab : Abundant S κ χ₀ z) :
    (1 / 4 : ℝ) * |S.pair z z| ≤ jacobiHurwitzQuad P z ∧ 0 < jacobiHurwitzQuad P z := by
  obtain ⟨hz0, hz_pos⟩ := (abundant_iff S κ χ₀ z).mp hab
  have habs_eq : |S.pair z z| = S.pair z z := abs_of_pos hz_pos
  have hge : (1 / 4 : ℝ) * S.pair z z ≤ jacobiHurwitzQuad P z := by
    by_contra hlt
    push Not at hlt
    set δ : ℝ := (S.pair z z / 2 - 2 * jacobiHurwitzQuad P z) / 4
    have hδ : 0 < δ := by dsimp [δ]; linarith
    -- Bound `jacobiHurwitzQuad P (κ - n • z) ≤ 2 n² q_P(z) + ...`? Even cleaner:
    -- `P.J i (κ - n • z) = P.J i κ - n * P.J i z`, so `(a - n b)² = n² b² - 2 n a b + a²`!
    have hquad_shift : ∀ n : ℕ, jacobiHurwitzQuad P (κ - (n : ℝ) • z) ≤
        jacobiHurwitzQuad P z * (n : ℝ) ^ 2 +
          (∑ i : Fin m, P.w i * (2 * Real.pi * |P.J i κ| * |P.J i z| / P.t i)) * (n : ℝ) +
          jacobiHurwitzQuad P κ := by
      intro n
      unfold jacobiHurwitzQuad
      rw [mul_comm _ ((n : ℝ) ^ 2), mul_sum, sum_mul, ← sum_add_distrib, ← sum_add_distrib]
      refine sum_le_sum fun i _ => ?_
      rw [map_sub, map_smul, smul_eq_mul]
      have hlin : -(2 * P.J i κ * P.J i z * (n : ℝ)) ≤
          2 * |P.J i κ| * |P.J i z| * (n : ℝ) := by
        have h1 : -(P.J i κ * P.J i z) ≤ |P.J i κ * P.J i z| := neg_le_abs _
        rw [abs_mul] at h1
        have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith
      have hexp : Real.pi * (P.J i κ - (n : ℝ) * P.J i z) ^ 2 / P.t i ≤
          (n : ℝ) ^ 2 * (Real.pi * (P.J i z) ^ 2 / P.t i) +
            (2 * Real.pi * |P.J i κ| * |P.J i z| / P.t i) * (n : ℝ) +
            Real.pi * (P.J i κ) ^ 2 / P.t i := by
        have ht_pos := P.ht i
        have hpi := Real.pi_pos
        have hnum : Real.pi * (P.J i κ - (n : ℝ) * P.J i z) ^ 2 ≤
            (n : ℝ) ^ 2 * (Real.pi * (P.J i z) ^ 2) +
              (2 * Real.pi * |P.J i κ| * |P.J i z|) * (n : ℝ) +
              Real.pi * (P.J i κ) ^ 2 := by nlinarith
        calc Real.pi * (P.J i κ - (n : ℝ) * P.J i z) ^ 2 / P.t i
            ≤ ((n : ℝ) ^ 2 * (Real.pi * (P.J i z) ^ 2) +
                (2 * Real.pi * |P.J i κ| * |P.J i z|) * (n : ℝ) +
                Real.pi * (P.J i κ) ^ 2) / P.t i :=
              div_le_div_of_nonneg_right hnum ht_pos.le
          _ = (n : ℝ) ^ 2 * (Real.pi * (P.J i z) ^ 2 / P.t i) +
                (2 * Real.pi * |P.J i κ| * |P.J i z| / P.t i) * (n : ℝ) +
                Real.pi * (P.J i κ) ^ 2 / P.t i := by ring
      have hw_pos := P.hw i
      calc P.w i * (Real.pi * (P.J i κ - (n : ℝ) * P.J i z) ^ 2 / P.t i)
          ≤ P.w i * ((n : ℝ) ^ 2 * (Real.pi * (P.J i z) ^ 2 / P.t i) +
              (2 * Real.pi * |P.J i κ| * |P.J i z| / P.t i) * (n : ℝ) +
              Real.pi * (P.J i κ) ^ 2 / P.t i) := mul_le_mul_of_nonneg_left hexp hw_pos.le
        _ = (n : ℝ) ^ 2 * (P.w i * (Real.pi * (P.J i z) ^ 2 / P.t i)) +
              P.w i * (2 * Real.pi * |P.J i κ| * |P.J i z| / P.t i) * (n : ℝ) +
              P.w i * (Real.pi * (P.J i κ) ^ 2 / P.t i) := by ring
    set S_sum : ℝ := ∑ i : Fin m, P.w i * (2 * Real.pi * |P.J i κ| * |P.J i z| / P.t i)
    set L_lin : ℝ := |S.pair z κ| / 2 + S_sum
    set L_const : ℝ := |χ₀| + jacobiHurwitzQuad P κ + 2 * jacobiHurwitzErrorBound P
    obtain ⟨n, h1, h2, hn0⟩ :=
      ((hARI z δ hδ).and
        ((eventually_affine_lt_quadratic hδ L_lin L_const).and (eventually_gt_atTop 0))).exists
    have hb1 := (abs_le.mp (abs_jacobiHurwitzHeight_sub_quad_le P ((n : ℝ) • z))).2
    have hb2 := (abs_le.mp (abs_jacobiHurwitzHeight_sub_quad_le P (κ - (n : ℝ) • z))).2
    rw [jacobiHurwitzQuad_smul] at hb1
    have hqs : jacobiHurwitzQuad P (κ - (n : ℝ) • z) ≤
        jacobiHurwitzQuad P z * (n : ℝ) ^ 2 + S_sum * (n : ℝ) + jacobiHurwitzQuad P κ :=
      hquad_shift n
    rw [eulerChar_smul] at h1
    have h1_exp : ((n : ℝ) ^ 2 * S.pair z z - (n : ℝ) * S.pair z κ) / 2 =
        (S.pair z z * (n : ℝ) ^ 2) / 2 - ((n : ℝ) * S.pair z κ) / 2 := by ring
    have hkx : (n : ℝ) * S.pair z κ ≤ |S.pair z κ| * (n : ℝ) := by
      have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      nlinarith [le_abs_self (S.pair z κ)]
    have hχ : -|χ₀| ≤ χ₀ := neg_abs_le χ₀
    have hn_sq : (0 : ℝ) < (n : ℝ) ^ 2 := pow_pos (by exact_mod_cast hn0) 2
    have hδn_pos : 0 < δ * (n : ℝ) ^ 2 := mul_pos hδ hn_sq
    have h4δ : 4 * (δ * (n : ℝ) ^ 2) =
        (S.pair z z * (n : ℝ) ^ 2) / 2 - 2 * (jacobiHurwitzQuad P z * (n : ℝ) ^ 2) := by
      dsimp [δ]; ring
    have hL_lin_eq : L_lin * (n : ℝ) = (|S.pair z κ| / 2) * (n : ℝ) + S_sum * (n : ℝ) := by
      dsimp [L_lin]; ring
    have hL_const_eq : L_const = |χ₀| + jacobiHurwitzQuad P κ + 2 * jacobiHurwitzErrorBound P := rfl
    have hmul_z : (n : ℝ) ^ 2 * jacobiHurwitzQuad P z = jacobiHurwitzQuad P z * (n : ℝ) ^ 2 :=
      mul_comm _ _
    linarith
  rw [habs_eq]
  exact ⟨hge, by linarith⟩

end Packet

/-! ### 4. Calibration on `goldenDatum`, Proved Short-Cycle Windows, and Global RH Equivalence -/

/-- **Unconditional Impossibility on `goldenDatum`:**
On `goldenDatum`, there is a finite Frobenius window `W` on which **no** functional `h : SpanCycle → ℝ`
whatsoever can satisfy `AsymptoticRiemannInequality` and `DegreeZeroSubquadratic` (and in
particular no torsion-weighted Jacobi–Hurwitz height can satisfy both). -/
theorem goldenDatum_no_asymptotic_subquadratic_height (κ : SpanCycle) (χ₀ : ℝ) :
    ∃ W : Finset ℕ, ¬ ∃ h : SpanCycle → ℝ,
      AsymptoticRiemannInequality (goldenDatum.windowSurface W) κ χ₀ h ∧
        DegreeZeroSubquadratic (goldenDatum.windowSurface W) κ h := by
  obtain ⟨W, x, hab⟩ := goldenDatum_exists_abundant κ χ₀
  refine ⟨W, ?_⟩
  rintro ⟨h, hARI, hsub⟩
  have hH := hodgeIndex_of_asymptoticRiemannInequality (goldenDatum.windowSurface W) hARI hsub
  have hnot_ab := (ampleHodgeIndex_iff_not_abundant (goldenDatum.windowSurface W) κ χ₀).mp
    ((goldenDatum.windowSurface W).ampleHodgeIndex_iff_castelnuovoSeveri.mpr
      ((goldenDatum.windowSurface W).hodgeIndex_iff_castelnuovoSeveri.mp hH)) x
  exact hnot_ab hab

/-- **Unconditional Existence on Proved Short-Cycle Subsurfaces (`r ≤ ½(log 2 + 1/50)`, including `3/10`):**
On `S_r := scalingSubsurface (primitiveSmoothRealTestsAt r)` for every `r ≤ (log 2 + 1/50)/2`,
there exists an explicit arithmetic functional `h` satisfying:
1. Uniform lower bound `0 ≤ h(x)` (`BoundedBelowFunctional h`),
2. Both exact `RiemannInequality S_r 0 0 h` and `AsymptoticRiemannInequality S_r 0 0 h`, and
3. Exact vanishing `h(n z) = 0` on every degree-zero class (`SingleRayDegreeZeroSubquadratic S_r h`
   and `DegreeZeroSubquadratic S_r 0 h`). -/
theorem shortCycle_subquadratic_height_exists_primeTwo {r : ℝ}
    (hr : r ≤ (Real.log 2 + 1 / 50) / 2) :
    let S := scalingSubsurface (primitiveSmoothRealTestsAt r)
    ∃ h : ℝ × ℝ × primitiveSmoothRealTestsAt r → ℝ,
      (∀ x, 0 ≤ h x) ∧
      BoundedBelowFunctional h ∧
      RiemannInequality S 0 0 h ∧
      AsymptoticRiemannInequality S 0 0 h ∧
      (∀ z, S.pair z S.ample = 0 → ∀ n : ℕ, h ((n : ℝ) • z) = 0) ∧
      SingleRayDegreeZeroSubquadratic S h ∧
      DegreeZeroSubquadratic S 0 h := by
  intro S
  have hH : S.HodgeIndex := primitiveSmooth_scalingSubsurface_hodgeIndex_primeTwo hr
  refine ⟨optimalEffectivity S 0 0,
    fun x => div_nonneg (le_max_left 0 _) (by norm_num),
    ⟨0, fun x => by
      rw [neg_zero]
      exact div_nonneg (le_max_left 0 _) (by norm_num)⟩,
    riemannInequality_optimalEffectivity S 0 0,
    asymptoticRiemannInequality_of_riemannInequality S (riemannInequality_optimalEffectivity S 0 0),
    ?_, ?_, ?_⟩
  · intro z hz n
    have hdeg : S.pair ((n : ℝ) • z) S.ample = 0 := by
      rw [pair_smul_ample, hz, mul_zero]
    have hle0 : eulerChar S 0 0 ((n : ℝ) • z) ≤ 0 := by
      have h := eulerChar_le_levelBound S hH 0 0 0 hdeg
      simpa [levelBound] using h
    simp [optimalEffectivity, max_eq_left hle0]
  · intro z hz c hc
    filter_upwards with n
    have hdeg : S.pair ((n : ℝ) • z) S.ample = 0 := by
      rw [pair_smul_ample, hz, mul_zero]
    have hle0 : eulerChar S 0 0 ((n : ℝ) • z) ≤ 0 := by
      have h := eulerChar_le_levelBound S hH 0 0 0 hdeg
      simpa [levelBound] using h
    have h0 : optimalEffectivity S 0 0 ((n : ℝ) • z) = 0 := by
      simp [optimalEffectivity, max_eq_left hle0]
    rw [h0]
    exact mul_nonneg hc.le (sq_nonneg _)
  · refine degreeZeroSubquadratic_zero_of_singleRay S (fun z hz c hc => ?_)
    filter_upwards with n
    have hdeg : S.pair ((n : ℝ) • z) S.ample = 0 := by
      rw [pair_smul_ample, hz, mul_zero]
    have hle0 : eulerChar S 0 0 ((n : ℝ) • z) ≤ 0 := by
      have h := eulerChar_le_levelBound S hH 0 0 0 hdeg
      simpa [levelBound] using h
    have h0 : optimalEffectivity S 0 0 ((n : ℝ) • z) = 0 := by
      simp [optimalEffectivity, max_eq_left hle0]
    rw [h0]
    exact mul_nonneg hc.le (sq_nonneg _)

/-- **Global Short-Cycle & Scaling-Surface Equivalence to `RiemannHypothesis`:**
The following are unconditionally equivalent:
1. `RiemannHypothesis`;
2. Existence of a functional `h : ScalingCycle → ℝ` satisfying
   `BoundedBelowFunctional h`, `AsymptoticRiemannInequality scalingSurface 0 χ₀ h`, and
   `SingleRayDegreeZeroSubquadratic scalingSurface h`;
3. Nonnegativity of `Re W_ζ` on every dyadic short-cycle correspondence difference
   `g - translate (m * log 2) g` with `g ∈ C²_c([-3/10, 3/10])`. -/
theorem riemannHypothesis_iff_exists_asymptotic_subquadratic_height (χ₀ : ℝ) :
    List.TFAE [RiemannHypothesis,
      ∃ h : ScalingCycle → ℝ,
        BoundedBelowFunctional h ∧
        AsymptoticRiemannInequality scalingSurface 0 χ₀ h ∧
        SingleRayDegreeZeroSubquadratic scalingSurface h,
      ∀ g : ℝ → ℂ, ContDiff ℝ 2 g → tsupport g ⊆ Icc (-(3 / 10)) (3 / 10) → ∀ m : ℕ,
        0 ≤ (zetaZeroConfig.W (g - ArithmeticCastelnuovoSeveri.translate (m * Real.log 2) g)
          (g - ArithmeticCastelnuovoSeveri.translate (m * Real.log 2) g)).re] := by
  tfae_have 1 → 2 := by
    intro hRH
    have hH : scalingSurface.HodgeIndex := scalingSurface_hodgeIndex_iff.mpr hRH
    obtain ⟨h, hnonneg, hRI, hdb⟩ := exists_effectivity_of_hodgeIndex scalingSurface hH 0 0 χ₀
    have hκ0 : (0 : ℝ) • scalingSurface.H + (0 : ℝ) • scalingSurface.V = 0 := by simp
    rw [hκ0] at hRI
    refine ⟨h, ⟨0, fun x => by linarith [hnonneg x]⟩,
      asymptoticRiemannInequality_of_riemannInequality scalingSurface hRI, ?_⟩
    obtain ⟨M₀, hM₀⟩ := hdb 0
    intro z hz c hc
    filter_upwards [eventually_affine_lt_quadratic hc 0 M₀] with n hn
    have h0 : h ((n : ℝ) • z) ≤ M₀ :=
      hM₀ _ (by rw [pair_smul_ample, hz, mul_zero])
    linarith
  tfae_have 2 → 1 := by
    rintro ⟨h, _, hARI, hsub⟩
    have hH := hodgeIndex_of_asymptoticRiemannInequality scalingSurface hARI
      (degreeZeroSubquadratic_zero_of_singleRay scalingSurface hsub)
    exact scalingSurface_hodgeIndex_iff.mp hH
  tfae_have 1 ↔ 3 :=
    zeta_riemannHypothesis_iff_twoWindows Nat.prime_two (by norm_num : (0 : ℝ) < 3 / 10)
  tfae_finish

end GaloisForLFunctions.SelectivePositivityAndThresholdLaws
