import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Fejér–Riesz factorization

A trigonometric polynomial `T(θ) = Σ_{|k| ≤ n} a_k e^{ikθ}` that is real and nonnegative for every
real `θ` is the squared modulus `|Q(e^{iθ})|²` of a polynomial `Q` of degree `≤ n` (`fejerRiesz`).

We write `T(θ) = e^{−inθ} P(e^{iθ})` with `P` a polynomial of degree `≤ 2n` (`circleTrig n P`).
Realness on the circle makes `P` self-reciprocal, `P(z) = z^{2n} conj P(1/z̄)`
(`eq_mirrorConj_of_real`), so a zero `w` off the circle comes with the zero `1/w̄`; a zero on the
circle is a minimum of `T`, hence a double zero of `P` (`isRoot_derivative_of_circle_zero`). On the
circle `(z − w)(z − 1/w̄) = −(z/w̄)|z − w|²` (`circle_pair_factor`), so dividing out one pair
lowers `n` by one.
-/

open Polynomial Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The trigonometric polynomial `e^{−inθ} P(e^{iθ})`. -/
def circleTrig (n : ℕ) (P : ℂ[X]) (θ : ℝ) : ℂ :=
  Complex.exp (-((n : ℂ) * θ * I)) * P.eval (Complex.exp (θ * I))

theorem normSq_exp_mul_I (θ : ℝ) : Complex.normSq (Complex.exp (θ * I)) = 1 := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]

theorem conj_exp_mul_I (θ : ℝ) : conj (Complex.exp (θ * I)) = (Complex.exp (θ * I))⁻¹ := by
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  simp

/-- Two points of the circle at angular distance `< 2π` coincide only if the angles do. -/
theorem eq_of_exp_mul_I_eq {a b : ℝ} (h : Complex.exp (a * I) = Complex.exp (b * I))
    (hab : |a - b| < 2 * Real.pi) : a = b := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have h0 : ((a - b - m * (2 * Real.pi) : ℝ) : ℂ) * I = 0 := by
    push_cast; linear_combination hm
  have hd : a - b = m * (2 * Real.pi) := by
    have := Complex.ofReal_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right Complex.I_ne_zero)
    linarith
  rw [hd, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hab
  have hm1 : |(m : ℝ)| < 1 := by
    have := Real.pi_pos
    nlinarith [abs_nonneg (m : ℝ)]
  have hm0 : m = 0 := by
    rw [← Int.cast_abs] at hm1
    have : |m| < 1 := by exact_mod_cast hm1
    exact Int.abs_lt_one_iff.mp this
  rw [hm0] at hd
  simp at hd
  linarith

/-- The reciprocal-conjugate polynomial `Σ_{j ≤ N} conj(p_j) X^{N−j}`. -/
def mirrorConj (N : ℕ) (P : ℂ[X]) : ℂ[X] :=
  ∑ j ∈ Finset.range (N + 1), C (conj (P.coeff j)) * X ^ (N - j)

theorem eval_mirrorConj {N : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ N) {z : ℂ} (hz : z ≠ 0) :
    (mirrorConj N P).eval z = z ^ N * conj (P.eval (conj z)⁻¹) := by
  rw [mirrorConj, eval_finsetSum, eval_eq_sum_range' (Nat.lt_succ_of_le hP), map_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [eval_mul, eval_C, eval_pow, eval_X, map_mul, map_pow, map_inv₀, Complex.conj_conj,
    pow_sub₀ _ hz hjN, inv_pow]
  ring

theorem coeff_mirrorConj_top (N : ℕ) (P : ℂ[X]) :
    (mirrorConj N P).coeff N = conj (P.coeff 0) := by
  rw [mirrorConj, finsetSum_coeff, Finset.sum_eq_single 0]
  · simp
  · intro j hj hj0
    rw [coeff_C_mul, coeff_X_pow]
    have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [if_neg (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) h

/-- Realness on the circle: `P(z) = z^{2n} conj P(z)` for `|z| = 1`. -/
theorem eval_eq_pow_mul_conj {n : ℕ} {P : ℂ[X]} {θ : ℝ} (hθ : (circleTrig n P θ).im = 0) :
    P.eval (Complex.exp (θ * I)) =
      Complex.exp (θ * I) ^ (2 * n) * conj (P.eval (Complex.exp (θ * I))) := by
  set z := Complex.exp (θ * I)
  set p := P.eval z
  have hT : conj (circleTrig n P θ) = circleTrig n P θ := Complex.conj_eq_iff_im.mpr hθ
  have hzn : Complex.exp ((n : ℂ) * θ * I) = z ^ n := by
    rw [← Complex.exp_nat_mul]; congr 1; ring
  have hconj : conj (Complex.exp (-((n : ℂ) * θ * I))) = z ^ n := by
    rw [← Complex.exp_conj, ← hzn]; congr 1; simp
  rw [circleTrig, map_mul, hconj] at hT
  have hinv : Complex.exp (-((n : ℂ) * θ * I)) * z ^ n = 1 := by
    rw [← hzn, ← Complex.exp_add]; simp
  calc p = (Complex.exp (-((n : ℂ) * θ * I)) * z ^ n) * p := by rw [hinv, one_mul]
    _ = z ^ n * (Complex.exp (-((n : ℂ) * θ * I)) * p) := by ring
    _ = z ^ n * (z ^ n * conj p) := by rw [← hT]
    _ = z ^ (2 * n) * conj p := by ring

/-- **Self-reciprocity.** A polynomial real on the circle after the phase `e^{−inθ}` equals its
reciprocal conjugate of order `2n`. -/
theorem eq_mirrorConj_of_real {n : ℕ} {P : ℂ[X]} (hP : P.natDegree ≤ 2 * n)
    (hreal : ∀ θ : ℝ, (circleTrig n P θ).im = 0) : P = mirrorConj (2 * n) P := by
  apply Polynomial.eq_of_infinite_eval_eq
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => Complex.exp (((1 / ((k : ℝ) + 1) : ℝ) : ℂ) * I)) ?_ ?_
  · intro k l hkl
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hl : (0 : ℝ) < 1 / ((l : ℝ) + 1) := by positivity
    have hk1 : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) k]
    have hl1 : 1 / ((l : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) l]
    have h := eq_of_exp_mul_I_eq hkl (by
      rw [abs_lt]; constructor <;> linarith [Real.two_le_pi])
    have : (k : ℝ) + 1 = (l : ℝ) + 1 := by
      field_simp at h; linarith
    exact_mod_cast (by linarith : (k : ℝ) = l)
  · intro k
    set θ : ℝ := 1 / ((k : ℝ) + 1)
    show P.eval (Complex.exp (θ * I)) = (mirrorConj (2 * n) P).eval (Complex.exp (θ * I))
    rw [eval_mirrorConj hP (Complex.exp_ne_zero _), conj_exp_mul_I, inv_inv]
    exact eval_eq_pow_mul_conj (hreal θ)

/-- On the circle, one reciprocal pair of linear factors is a positive multiple of `|z − w|²`. -/
theorem circle_pair_factor (θ : ℝ) {w : ℂ} (hw : w ≠ 0) :
    (Complex.exp (θ * I) - w) * (Complex.exp (θ * I) - (conj w)⁻¹) =
      -(Complex.exp (θ * I) * (conj w)⁻¹) *
        (Complex.normSq (Complex.exp (θ * I) - w) : ℂ) := by
  set z := Complex.exp (θ * I)
  have hz : z ≠ 0 := Complex.exp_ne_zero _
  have hcw : conj w ≠ 0 := (_root_.map_ne_zero (starRingEnd ℂ)).mpr hw
  rw [← Complex.mul_conj, map_sub, conj_exp_mul_I]
  field_simp
  ring

theorem continuous_circleTrig (n : ℕ) (P : ℂ[X]) : Continuous (circleTrig n P) := by
  unfold circleTrig
  have h1 : Continuous fun θ : ℝ => Complex.exp (θ * I) :=
    Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  exact (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).mul
    continuous_const).neg).mul (P.continuous.comp h1)

/-- **A zero on the circle is double.** At a zero of `P` on the circle, the nonnegative real
function `T` has a minimum, so its derivative `e^{−inθ} P′(z) iz` vanishes. -/
theorem isRoot_derivative_of_circle_zero {n : ℕ} {P : ℂ[X]}
    (hnn : ∀ θ : ℝ, (circleTrig n P θ).im = 0 ∧ 0 ≤ (circleTrig n P θ).re) {θ₀ : ℝ}
    (h0 : P.IsRoot (Complex.exp (θ₀ * I))) :
    (derivative P).IsRoot (Complex.exp (θ₀ * I)) := by
  set z₀ := Complex.exp (θ₀ * I)
  -- derivatives of the two factors
  have hz : HasDerivAt (fun θ : ℝ => Complex.exp (θ * I)) (Complex.exp (θ₀ * I) * I) θ₀ := by
    have := ((hasDerivAt_id' θ₀).ofReal_comp.mul_const I).cexp
    simpa using this
  have hp : HasDerivAt (fun θ : ℝ => P.eval (Complex.exp (θ * I)))
      ((derivative P).eval z₀ * (z₀ * I)) θ₀ := by
    have hP' : HasDerivAt (fun x : ℂ => P.eval x) ((derivative P).eval z₀) z₀ :=
      Polynomial.hasDerivAt P z₀
    exact hP'.comp θ₀ hz
  obtain ⟨e', he⟩ : ∃ e', HasDerivAt (fun θ : ℝ => Complex.exp (-((n : ℂ) * θ * I))) e' θ₀ :=
    ⟨_, ((((hasDerivAt_id' θ₀).ofReal_comp.const_mul (n : ℂ)).mul_const I).neg).cexp⟩
  have hT : HasDerivAt (circleTrig n P)
      (Complex.exp (-((n : ℂ) * θ₀ * I)) * ((derivative P).eval z₀ * (z₀ * I))) θ₀ := by
    have := he.mul hp
    rw [show P.eval (Complex.exp (θ₀ * I)) = 0 from h0, mul_zero, zero_add] at this
    exact this
  set T' := Complex.exp (-((n : ℂ) * θ₀ * I)) * ((derivative P).eval z₀ * (z₀ * I))
  -- the real part has a minimum at `θ₀`, the imaginary part is constant
  have hre : T'.re = 0 := by
    have hmin : IsLocalMin (fun θ => (circleTrig n P θ).re) θ₀ := by
      refine Filter.Eventually.of_forall fun θ => ?_
      have : circleTrig n P θ₀ = 0 := by
        rw [circleTrig, show P.eval (Complex.exp (θ₀ * I)) = 0 from h0, mul_zero]
      simp only [this, Complex.zero_re]
      exact (hnn θ).2
    exact hmin.hasDerivAt_eq_zero (Complex.reCLM.hasFDerivAt.comp_hasDerivAt θ₀ hT)
  have him : T'.im = 0 := by
    have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt θ₀ hT
    have h2 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 θ₀ := hasDerivAt_const _ _
    have hfun : (⇑Complex.imCLM ∘ circleTrig n P) = fun _ : ℝ => (0 : ℝ) := by
      funext θ; exact (hnn θ).1
    rw [hfun] at h1
    exact h1.unique h2
  have hT0 : T' = 0 := Complex.ext hre him
  have hne : Complex.exp (-((n : ℂ) * θ₀ * I)) * (z₀ * I) ≠ 0 :=
    mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero)
  have : (derivative P).eval z₀ * (Complex.exp (-((n : ℂ) * θ₀ * I)) * (z₀ * I)) = 0 := by
    rw [← hT0]; simp only [T']; ring
  exact (mul_eq_zero.mp this).resolve_right hne

/-- The nonnegative half-line of `ℂ` is closed. -/
theorem isClosed_nonneg_real : IsClosed {x : ℂ | x.im = 0 ∧ 0 ≤ x.re} :=
  (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)

/-- A continuous function that lies in a closed set at all angles near `θ` lies there at `θ`. -/
theorem mem_of_punctured {f : ℝ → ℂ} (hf : Continuous f) {s : Set ℂ} (hs : IsClosed s) {θ : ℝ}
    (h : ∀ θ', θ' ≠ θ → |θ' - θ| < 2 * Real.pi → f θ' ∈ s) : f θ ∈ s := by
  refine hs.mem_of_tendsto ((hf.tendsto θ).mono_left (nhdsWithin_le_nhds (s := {θ}ᶜ))) ?_
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Metric.ball_mem_nhds θ (by positivity : (0 : ℝ) < 2 * Real.pi)] with θ' hθ' hne
  rw [Metric.mem_ball, Real.dist_eq] at hθ'
  exact h θ' hne hθ'

/-- **Fejér–Riesz.** A trigonometric polynomial of degree `n` that is real and nonnegative on the
line is `|Q(e^{iθ})|²` for a polynomial `Q` of degree `≤ n`. -/
theorem fejerRiesz (n : ℕ) (P : ℂ[X]) (hP : P.natDegree ≤ 2 * n)
    (hnn : ∀ θ : ℝ, (circleTrig n P θ).im = 0 ∧ 0 ≤ (circleTrig n P θ).re) :
    ∃ Q : ℂ[X], Q.natDegree ≤ n ∧
      ∀ θ : ℝ, circleTrig n P θ = (Complex.normSq (Q.eval (Complex.exp (θ * I))) : ℂ) := by
  induction n generalizing P with
  | zero =>
    have hP0 : P = C (P.coeff 0) := eq_C_of_natDegree_le_zero (by simpa using hP)
    have hT : ∀ θ : ℝ, circleTrig 0 P θ = P.coeff 0 := by
      intro θ; rw [circleTrig, hP0]; simp
    have hc := hnn 0
    rw [hT] at hc
    refine ⟨C (Real.sqrt (P.coeff 0).re : ℂ), by simp, fun θ => ?_⟩
    rw [hT, eval_C, Complex.normSq_ofReal, Real.mul_self_sqrt hc.2]
    exact Complex.ext (by simp) (by simp [hc.1])
  | succ n ih =>
    have hmir := eq_mirrorConj_of_real hP (fun θ => (hnn θ).1)
    have htop : P.coeff (2 * (n + 1)) = conj (P.coeff 0) := by
      conv_lhs => rw [hmir]
      exact coeff_mirrorConj_top _ _
    by_cases h0 : P.coeff 0 = 0
    · -- a zero at the origin: divide by `X`
      have hX : P = X * divX P := by
        have := X_mul_divX_add P
        rw [h0, C_0, add_zero] at this
        exact this.symm
      have hdeg : (divX P).natDegree ≤ 2 * n := by
        rw [natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rw [coeff_divX]
        rcases Nat.lt_or_ge (2 * (n + 1)) (N + 1) with hlt | hge
        · exact coeff_eq_zero_of_natDegree_lt (hP.trans_lt hlt)
        · have hN' : N + 1 = 2 * (n + 1) := by
            have : 2 * n < N := by exact_mod_cast hN
            omega
          rw [hN', htop, h0, map_zero]
      have hT : ∀ θ : ℝ, circleTrig n (divX P) θ = circleTrig (n + 1) P θ := by
        intro θ
        conv_rhs => rw [hX]
        rw [circleTrig, circleTrig, eval_mul, eval_X]
        have : Complex.exp (-(((n + 1 : ℕ) : ℂ) * θ * I)) * Complex.exp (θ * I) =
            Complex.exp (-((n : ℂ) * θ * I)) := by
          rw [← Complex.exp_add]; congr 1; push_cast; ring
        rw [← this]; ring
      obtain ⟨Q, hQ, hQT⟩ := ih (divX P) hdeg (fun θ => by rw [hT]; exact hnn θ)
      exact ⟨Q, hQ.trans (Nat.le_succ n), fun θ => by rw [← hT]; exact hQT θ⟩
    · -- a zero `w ≠ 0` and its reflection `1/w̄`
      have hP0 : P ≠ 0 := fun h => h0 (by rw [h, coeff_zero])
      have hdeg : 0 < P.degree := by
        have hne : P.coeff (2 * (n + 1)) ≠ 0 := by
          rw [htop]; exact (_root_.map_ne_zero (starRingEnd ℂ)).mpr h0
        have := le_natDegree_of_ne_zero hne
        exact natDegree_pos_iff_degree_pos.mp (by omega)
      obtain ⟨w, hw⟩ := Complex.exists_root hdeg
      have hw0 : w ≠ 0 := by
        rintro rfl
        exact h0 (by rw [coeff_zero_eq_eval_zero]; exact hw)
      set w' := (conj w)⁻¹ with hw'def
      have hw'0 : w' ≠ 0 := inv_ne_zero ((_root_.map_ne_zero (starRingEnd ℂ)).mpr hw0)
      -- the factorization `P = (X − w)(X − w')P₁`
      obtain ⟨P₁, hfac⟩ : ∃ P₁ : ℂ[X], P = (X - C w) * (X - C w') * P₁ := by
        by_cases hww : w' = w
        · -- `w` is on the circle, hence a double zero
          have hnorm : ‖w‖ = 1 := by
            have h1 : conj w * w = 1 := by
              calc conj w * w = conj w * (conj w)⁻¹ := by rw [← hw'def, hww]
                _ = 1 := mul_inv_cancel₀ ((_root_.map_ne_zero (starRingEnd ℂ)).mpr hw0)
            rw [mul_comm, Complex.mul_conj] at h1
            have h2 : Complex.normSq w = 1 := by exact_mod_cast h1
            rw [Complex.normSq_eq_norm_sq] at h2
            nlinarith [norm_nonneg w]
          have hθ : Complex.exp ((Complex.arg w : ℂ) * I) = w := by
            have := Complex.norm_mul_exp_arg_mul_I w
            rw [hnorm, Complex.ofReal_one, one_mul] at this
            exact this
          have hd := isRoot_derivative_of_circle_zero hnn (θ₀ := Complex.arg w)
            (by rw [hθ]; exact hw)
          rw [hθ] at hd
          have hmult : 2 ≤ P.rootMultiplicity w :=
            (one_lt_rootMultiplicity_iff_isRoot hP0).mpr ⟨hw, hd⟩
          obtain ⟨P₁, hP₁⟩ := (le_rootMultiplicity_iff hP0).mp hmult
          exact ⟨P₁, by rw [hP₁, hww, sq]⟩
        · -- `w' ≠ w` is a second zero
          have hw' : P.IsRoot w' := by
            have h := congrArg (eval w') hmir
            rw [eval_mirrorConj hP hw'0] at h
            have hcc : (conj w')⁻¹ = w := by
              rw [hw'def, map_inv₀, Complex.conj_conj, inv_inv]
            rw [hcc, show P.eval w = 0 from hw, map_zero, mul_zero] at h
            exact h
          set P₃ := P /ₘ (X - C w)
          have hP₃ : (X - C w) * P₃ = P := mul_divByMonic_eq_iff_isRoot.mpr hw
          have hr : P₃.IsRoot w' := by
            have h := congrArg (eval w') hP₃
            rw [eval_mul, eval_sub, eval_X, eval_C, show P.eval w' = 0 from hw'] at h
            exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hww)
          refine ⟨P₃ /ₘ (X - C w'), ?_⟩
          rw [mul_assoc, mul_divByMonic_eq_iff_isRoot.mpr hr, hP₃]
      have hP₁0 : P₁ ≠ 0 := by rintro rfl; exact hP0 (by rw [hfac, mul_zero])
      have hdeg₁ : P₁.natDegree ≤ 2 * n := by
        have hpair : ((X - C w) * (X - C w')).natDegree = 2 := by
          rw [natDegree_mul (X_sub_C_ne_zero w) (X_sub_C_ne_zero w'), natDegree_X_sub_C,
            natDegree_X_sub_C]
        have := congrArg natDegree hfac
        rw [natDegree_mul (mul_ne_zero (X_sub_C_ne_zero w) (X_sub_C_ne_zero w')) hP₁0,
          hpair] at this
        omega
      set P₁' := C (-w') * P₁
      have hdeg₁' : P₁'.natDegree ≤ 2 * n := (natDegree_C_mul_le _ _).trans hdeg₁
      -- `T = |z − w|² T₁` on the circle
      have hid : ∀ θ : ℝ, circleTrig (n + 1) P θ =
          (Complex.normSq (Complex.exp (θ * I) - w) : ℂ) * circleTrig n P₁' θ := by
        intro θ
        rw [circleTrig, circleTrig, hfac]
        simp only [P₁', eval_mul, eval_sub, eval_X, eval_C]
        rw [hw'def, circle_pair_factor θ hw0]
        have hsplit : Complex.exp (-(((n + 1 : ℕ) : ℂ) * θ * I)) =
            Complex.exp (-((n : ℂ) * θ * I)) * (Complex.exp (θ * I))⁻¹ := by
          rw [← Complex.exp_neg, ← Complex.exp_add]; congr 1; push_cast; ring
        rw [hsplit]
        field_simp
      have hT₁ : ∀ θ : ℝ, (circleTrig n P₁' θ).im = 0 ∧ 0 ≤ (circleTrig n P₁' θ).re := by
        have hgood : ∀ θ : ℝ, Complex.exp (θ * I) ≠ w →
            circleTrig n P₁' θ ∈ {x : ℂ | x.im = 0 ∧ 0 ≤ x.re} := by
          intro θ hne
          have hpos : 0 < Complex.normSq (Complex.exp (θ * I) - w) :=
            Complex.normSq_pos.mpr (sub_ne_zero.mpr hne)
          have hdiv : circleTrig n P₁' θ =
              circleTrig (n + 1) P θ / (Complex.normSq (Complex.exp (θ * I) - w) : ℂ) := by
            rw [hid θ, mul_div_cancel_left₀ _ (by exact_mod_cast hpos.ne')]
          rw [Set.mem_setOf_eq, hdiv, Complex.div_ofReal_im, Complex.div_ofReal_re, (hnn θ).1,
            zero_div]
          exact ⟨rfl, div_nonneg (hnn θ).2 hpos.le⟩
        intro θ
        by_cases hθ : Complex.exp (θ * I) = w
        · refine mem_of_punctured (continuous_circleTrig n P₁') isClosed_nonneg_real
            fun θ' hne hlt => hgood θ' fun h => hne (eq_of_exp_mul_I_eq (h.trans hθ.symm) hlt)
        · exact hgood θ hθ
      obtain ⟨Q₁, hQ₁, hQ₁T⟩ := ih P₁' hdeg₁' hT₁
      refine ⟨(X - C w) * Q₁, ?_, fun θ => ?_⟩
      · calc ((X - C w) * Q₁).natDegree ≤ (X - C w).natDegree + Q₁.natDegree :=
            natDegree_mul_le
          _ ≤ 1 + n := by rw [natDegree_X_sub_C]; omega
          _ = n + 1 := by ring
      · rw [hid θ, hQ₁T θ, eval_mul, eval_sub, eval_X, eval_C, Complex.normSq_mul]
        push_cast
        ring

end GaloisForLFunctions.HTGeometry
