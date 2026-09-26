import GaloisForLFunctions.RHTower.ZetaTwistedFirstMomentContour
import GaloisForLFunctions.RHTower.VonMangoldtMollifierPolynomialMeanSquare
import GaloisForLFunctions.RHTower.MertensFirst
import GaloisForLFunctions.HTGeometry.StripSquareMeanConvexity

/-!
# Unmollified primes put a floor under every short mollified mean square

Let `Ψ(s) = Σ_{d ≤ y} b_d d^{-s}` with `b_1 = 1`, `|b_d| ≤ 1`, and put
`c_n = Σ_{d ≤ y, d ∣ n} b_d`, the coefficients of `ζΨ`. Every prime `p > y` has `c_p = b_1 = 1`:
it is never mollified. Testing `ζΨ` against `Q(s) = Σ_{n ≤ M} c_n n^{-s}` on the line `Re s = σ`
gives, by the twisted first moment of `ζ` and Cauchy–Schwarz,

`∫_T^{2T} |ζΨ(σ+it)|² dt ≥ T · Σ_{n ≤ M} |c_n|² n^{-2σ} · (1 − o(1))`,

and the primes in `(y, M]` alone contribute `M^{1−2σ} (log(M/y) − O(1))/log M` to the sum.

On `Re s = 1/2 + a/log T`, with `y ≤ T^{1/100}` and `M = ⌊T^{1/20}⌋`, this gives for every `a > 0`
and all large `T`, uniformly over all such mollifiers,

`∫_T^{2T} |ζΨ(1/2 + a/log T + it)|² dt ≥ (1 + (3/10) e^{-a/10}) T`
(`exists_eventually_integral_normSq_zetaMollified_rightShift_ge`).

A mollified mean square `≤ T(1 + o(1))` at a fixed displacement `a` is therefore impossible for
mollifiers of length `≤ T^{1/100}`.
-/

noncomputable section

open Complex MeasureTheory Set Filter

namespace RHTower

/-- The Dirichlet coefficients `c_n = Σ_{d ≤ y, d ∣ n} b_d` of `ζΨ`. -/
def mollifiedZetaCoeff (b : ℕ → ℂ) (y n : ℕ) : ℂ :=
  ∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ∣ n), b d

theorem norm_mollifiedZetaCoeff_le {b : ℕ → ℂ} {y : ℕ} (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1)
    (n : ℕ) : ‖mollifiedZetaCoeff b y n‖ ≤ y := by
  unfold mollifiedZetaCoeff
  calc ‖∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ∣ n), b d‖
      ≤ ∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ∣ n), ‖b d‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ (Finset.Icc 1 y).filter (fun d => d ∣ n), (1 : ℝ) :=
        Finset.sum_le_sum fun d hd => hb d (Finset.mem_filter.mp hd).1
    _ ≤ ∑ _d ∈ Finset.Icc 1 y, (1 : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => zero_le_one)
    _ = y := by simp

theorem mollifiedZetaCoeff_one {b : ℕ → ℂ} {y : ℕ} (hy : 1 ≤ y) :
    mollifiedZetaCoeff b y 1 = b 1 := by
  unfold mollifiedZetaCoeff
  have : (Finset.Icc 1 y).filter (fun d => d ∣ 1) = {1} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.dvd_one, Finset.mem_singleton]
    constructor
    · rintro ⟨-, h⟩; exact h
    · rintro rfl; exact ⟨⟨le_rfl, hy⟩, rfl⟩
  rw [this, Finset.sum_singleton]

theorem mollifiedZetaCoeff_prime {b : ℕ → ℂ} {y p : ℕ} (hy : 1 ≤ y) (hp : p.Prime) (hyp : y < p) :
    mollifiedZetaCoeff b y p = b 1 := by
  unfold mollifiedZetaCoeff
  have : (Finset.Icc 1 y).filter (fun d => d ∣ p) = {1} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, hd⟩
      rcases (Nat.dvd_prime hp).mp hd with h | h
      · exact h
      · omega
    · rintro rfl; exact ⟨⟨le_rfl, hy⟩, one_dvd p⟩
  rw [this, Finset.sum_singleton]

/-- The mollified product tested against its own coefficient polynomial. -/
theorem zeta_mul_edPoly_mul_conj_eq_sum {σ t : ℝ} (b c : ℕ → ℂ) (y M : ℕ) :
    riemannZeta ((σ : ℂ) + (t : ℂ) * I) * edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) *
        (starRingEnd ℂ) (edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)) =
      ∑ d ∈ Finset.Icc 1 y, ∑ n ∈ Finset.Icc 1 M,
        b d * (starRingEnd ℂ) (c n) * twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I) := by
  set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
  have hconj : ∀ n : ℕ, (starRingEnd ℂ) (((n : ℝ) : ℂ) ^ (-s)) =
      ((n : ℝ) : ℂ) ^ (s - 2 * (σ : ℂ)) := by
    intro n
    have harg : ((n : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
      exact Real.pi_ne_zero.symm
    have h := Complex.cpow_conj ((n : ℝ) : ℂ) (-s) harg
    rw [Complex.conj_ofReal] at h
    rw [← h]
    congr 1
    rw [hs]
    apply Complex.ext <;> simp
    ring
  have hB : (starRingEnd ℂ) (edPoly c (Finset.Icc 1 M) s) =
      ∑ n ∈ Finset.Icc 1 M, (starRingEnd ℂ) (c n) * ((n : ℝ) : ℂ) ^ (s - 2 * (σ : ℂ)) := by
    unfold edPoly
    rw [map_sum]
    simp only [map_mul, hconj]
  rw [hB]
  unfold edPoly twistedZeta
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- **Core inequality at one height.** With `D = Σ_{n ≤ M} |c_n|² n^{-2σ}` and
`E = y² M (27√T M + 8M²)`, `T·D − E ≤ √((T + 8M(1+log M)) D · ∫_T^{2T} |ζΨ|²)`. -/
theorem mollified_meanSquare_floor_core {σ T : ℝ} (hσ : 1 / 2 ≤ σ) (hσ1 : σ < 1) (hT : 4 ≤ T)
    {y M : ℕ} (hy : 1 ≤ y) (hM : 1 ≤ M) {b : ℕ → ℂ} (hb : ∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1)
    (hD : 0 < ∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) :
    T * (∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) -
        (y : ℝ) ^ 2 * M * (27 * Real.sqrt T * M + 8 * (M : ℝ) ^ 2) ≤
      Real.sqrt ((T + 8 * M * (1 + Real.log M)) *
        (∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) *
        ∫ t in T..(2 * T), ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) := by
  classical
  set c : ℕ → ℂ := mollifiedZetaCoeff b y with hc
  set D : ℝ := ∑ n ∈ Finset.Icc 1 M, ‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) with hDdef
  have hs : ∀ n ∈ Finset.Icc 1 M, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hsy : ∀ n ∈ Finset.Icc 1 y, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hT0 : 0 < T := by linarith
  have hline : ∀ t : ℝ, ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro t h
    have := congrArg Complex.re h
    simp at this
    linarith
  -- continuity along the line
  have hZc : Continuous fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    exact (ContinuousAt.comp (g := riemannZeta) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
      (differentiableAt_riemannZeta (hline t)).continuousAt (by fun_prop)).mul
      (((differentiable_edPoly b hsy).continuous.comp (by fun_prop)).continuousAt)
  have hQc : Continuous fun t : ℝ => edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I) :=
    (differentiable_edPoly c hs).continuous.comp (by fun_prop)
  -- the test polynomial's mean square
  have hQ : ∫ t in T..(2 * T), ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      (T + 8 * M * (1 + Real.log M)) * D := by
    have h := integral_normSq_edPoly_displaced_le (1 / 2 - σ) c M T (2 * T)
    have hpt : ∀ t : ℝ, displacedLinePt (1 / 2 - σ) t = (σ : ℂ) + (t : ℂ) * I := by
      intro t; unfold displacedLinePt; congr 2; ring
    simp only [hpt] at h
    have hexp : ∀ n : ℕ, (n : ℝ) ^ (2 * (1 / 2 - σ) - 1) = (n : ℝ) ^ (-2 * σ) := by
      intro n; congr 1; ring
    simp only [hexp] at h
    rw [show 2 * T - T = T by ring] at h
    exact h
  -- the correlation and its diagonal
  have hcont : ∀ d ∈ Finset.Icc 1 y, ∀ n ∈ Finset.Icc 1 M,
      Continuous (fun t : ℝ => b d * (starRingEnd ℂ) (c n) *
        twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I)) := by
    intro d hd n hn
    refine continuous_const.mul (continuous_iff_continuousAt.mpr fun t => ?_)
    exact ContinuousAt.comp (g := twistedZeta σ d n) (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I)
      (differentiableAt_twistedZeta σ (hsy d hd) (hs n hn) (hline t)).continuousAt (by fun_prop)
  have hcorr : (∫ t in T..(2 * T), riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
      edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) *
        (starRingEnd ℂ) (edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I))) =
      ∑ d ∈ Finset.Icc 1 y, ∑ n ∈ Finset.Icc 1 M, b d * (starRingEnd ℂ) (c n) *
        ∫ t in T..(2 * T), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I) := by
    simp only [zeta_mul_edPoly_mul_conj_eq_sum]
    rw [intervalIntegral.integral_finsetSum (f := fun d t => ∑ n ∈ Finset.Icc 1 M,
      b d * (starRingEnd ℂ) (c n) * twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I))
      fun d hd => (continuous_finsetSum _ fun n hn => hcont d hd n hn).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [intervalIntegral.integral_finsetSum (f := fun n t =>
      b d * (starRingEnd ℂ) (c n) * twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I))
      fun n hn => (hcont d hd n hn).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun n _ => ?_
    exact intervalIntegral.integral_const_mul _ _
  set diag : ℕ → ℕ → ℂ := fun d n =>
    if d ∣ n then (((n : ℝ) ^ (-2 * σ) * T : ℝ) : ℂ) else 0 with hdiagdef
  have hmain : ∑ d ∈ Finset.Icc 1 y, ∑ n ∈ Finset.Icc 1 M,
      b d * (starRingEnd ℂ) (c n) * diag d n = ((T * D : ℝ) : ℂ) := by
    rw [Finset.sum_comm]
    have hn : ∀ n ∈ Finset.Icc 1 M, ∑ d ∈ Finset.Icc 1 y, b d * (starRingEnd ℂ) (c n) * diag d n =
        (((‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)) * T : ℝ) : ℂ) := by
      intro n _
      have h1 : ∑ d ∈ Finset.Icc 1 y, b d * (starRingEnd ℂ) (c n) * diag d n =
          (starRingEnd ℂ) (c n) * (((n : ℝ) ^ (-2 * σ) * T : ℝ) : ℂ) *
            ∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ∣ n), b d := by
        rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun d _ => ?_
        simp only [hdiagdef]
        split_ifs <;> ring
      rw [h1]
      have h2 : ∑ d ∈ (Finset.Icc 1 y).filter (fun d => d ∣ n), b d = c n := rfl
      rw [h2, mul_comm ((starRingEnd ℂ) (c n)), mul_assoc, ← Complex.normSq_eq_conj_mul_self,
        Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [Finset.sum_congr rfl hn, ← Complex.ofReal_sum, hDdef, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  have herr : ‖(∑ d ∈ Finset.Icc 1 y, ∑ n ∈ Finset.Icc 1 M, b d * (starRingEnd ℂ) (c n) *
        ∫ t in T..(2 * T), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I)) - ((T * D : ℝ) : ℂ)‖ ≤
      (y : ℝ) ^ 2 * M * (27 * Real.sqrt T * M + 8 * (M : ℝ) ^ 2) := by
    rw [← hmain, ← Finset.sum_sub_distrib]
    have hbound : ∀ d ∈ Finset.Icc 1 y, ‖(∑ n ∈ Finset.Icc 1 M,
        b d * (starRingEnd ℂ) (c n) *
          (∫ t in T..(2 * T), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I))) -
          ∑ n ∈ Finset.Icc 1 M, b d * (starRingEnd ℂ) (c n) * diag d n‖ ≤
        M * (y * (27 * Real.sqrt T * M + 8 * (M : ℝ) ^ 2)) := by
      intro d hd
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ n ∈ Finset.Icc 1 M, ‖b d * (starRingEnd ℂ) (c n) *
          (∫ t in T..(2 * T), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I)) -
            b d * (starRingEnd ℂ) (c n) * diag d n‖ ≤
          y * (27 * Real.sqrt T * M + 8 * (M : ℝ) ^ 2) := by
        intro n hn
        rw [← mul_sub, norm_mul, norm_mul, Complex.norm_conj]
        have h1 := norm_integral_twistedZeta_sub_diag_le hσ (by linarith) (hsy d hd) (hs n hn) hT
        have hnM : (n : ℝ) ≤ M := by exact_mod_cast (Finset.mem_Icc.mp hn).2
        have h2 : 27 * Real.sqrt T * n + 8 * (n : ℝ) ^ 2 ≤
            27 * Real.sqrt T * M + 8 * (M : ℝ) ^ 2 := by
          have : (n : ℝ) ^ 2 ≤ (M : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg n) hnM 2
          have hsq : 0 ≤ Real.sqrt T := Real.sqrt_nonneg T
          nlinarith
        calc ‖b d‖ * ‖c n‖ * ‖(∫ t in T..(2 * T), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I)) -
              diag d n‖ ≤ 1 * y * (27 * Real.sqrt T * M + 8 * (M : ℝ) ^ 2) := by
              gcongr
              · exact hb d hd
              · exact norm_mollifiedZetaCoeff_le hb n
              · exact h1.trans h2
          _ = y * (27 * Real.sqrt T * M + 8 * (M : ℝ) ^ 2) := by ring
      calc ∑ n ∈ Finset.Icc 1 M, ‖b d * (starRingEnd ℂ) (c n) *
            (∫ t in T..(2 * T), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I)) -
              b d * (starRingEnd ℂ) (c n) * diag d n‖
          ≤ ∑ _n ∈ Finset.Icc 1 M, (y : ℝ) * (27 * Real.sqrt T * M + 8 * (M : ℝ) ^ 2) :=
            Finset.sum_le_sum hterm
        _ = M * (y * (27 * Real.sqrt T * M + 8 * (M : ℝ) ^ 2)) := by simp
    refine (norm_sum_le _ _).trans ?_
    calc ∑ d ∈ Finset.Icc 1 y, ‖(∑ n ∈ Finset.Icc 1 M,
          b d * (starRingEnd ℂ) (c n) *
            (∫ t in T..(2 * T), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I))) -
            ∑ n ∈ Finset.Icc 1 M, b d * (starRingEnd ℂ) (c n) * diag d n‖
        ≤ ∑ _d ∈ Finset.Icc 1 y, (M : ℝ) * (y * (27 * Real.sqrt T * M + 8 * (M : ℝ) ^ 2)) :=
          Finset.sum_le_sum hbound
      _ = (y : ℝ) ^ 2 * M * (27 * Real.sqrt T * M + 8 * (M : ℝ) ^ 2) := by simp; ring
  -- Cauchy–Schwarz
  have hYpos : 0 < (T + 8 * M * (1 + Real.log M)) * D := by
    have : 0 ≤ Real.log (M : ℝ) := Real.log_nonneg (by exact_mod_cast hM)
    positivity
  have hcs := GaloisForLFunctions.HTGeometry.integral_norm_mul_le_sqrt_of_bound
    (A := T) (B := 2 * T) (by linarith) hQc hZc hYpos hQ
  have hlow : T * D - (y : ℝ) ^ 2 * M * (27 * Real.sqrt T * M + 8 * (M : ℝ) ^ 2) ≤
      ∫ t in T..(2 * T), ‖edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I)‖ *
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I) * edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I)‖ := by
    have h1 : ‖((T * D : ℝ) : ℂ)‖ - (y : ℝ) ^ 2 * M * (27 * Real.sqrt T * M + 8 * (M : ℝ) ^ 2) ≤
        ‖∫ t in T..(2 * T), riemannZeta ((σ : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 y) ((σ : ℂ) + (t : ℂ) * I) *
            (starRingEnd ℂ) (edPoly c (Finset.Icc 1 M) ((σ : ℂ) + (t : ℂ) * I))‖ := by
      rw [hcorr]
      have := norm_sub_norm_le ((T * D : ℝ) : ℂ) (∑ d ∈ Finset.Icc 1 y, ∑ n ∈ Finset.Icc 1 M,
        b d * (starRingEnd ℂ) (c n) * ∫ t in T..(2 * T), twistedZeta σ d n ((σ : ℂ) + (t : ℂ) * I))
      rw [norm_sub_rev] at this
      linarith
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    refine h1.trans ?_
    refine (intervalIntegral.norm_integral_le_integral_norm (by linarith)).trans (le_of_eq ?_)
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [norm_mul, Complex.norm_conj]
    ring
  refine hlow.trans (hcs.trans (le_of_eq ?_))
  ring_nf

/-- The Mertens constant of `mertens_first_prime`. -/
def mertensPrimeConst : ℝ := (Real.log 4 + 4) + (8 + Mertens.mertensTail)

/-- The primes in `(y, M]` carry `log(M/y) − 2K` of Mertens mass. -/
theorem sum_prime_log_div_Ioc_ge {y M : ℕ} (hy : 1 ≤ y) (hyM : y ≤ M) :
    Real.log M - Real.log y - 2 * mertensPrimeConst ≤
      ∑ p ∈ (Finset.Icc 1 M).filter (fun p => p.Prime ∧ y < p), Real.log p / (p : ℝ) := by
  classical
  have hM := Mertens.mertens_first_prime M (by omega)
  have hY := Mertens.mertens_first_prime y hy
  have hsplit : ∑ n ∈ (Finset.Icc 1 M).filter Nat.Prime, Real.log n / (n : ℝ) =
      ∑ p ∈ (Finset.Icc 1 M).filter (fun p => p.Prime ∧ y < p), Real.log p / (p : ℝ) +
        ∑ n ∈ (Finset.Icc 1 y).filter Nat.Prime, Real.log n / (n : ℝ) := by
    rw [← Finset.sum_filter_add_sum_filter_not ((Finset.Icc 1 M).filter Nat.Prime) (fun n => y < n)]
    congr 1
    · congr 1; ext n; simp [Finset.mem_filter, and_assoc]
    · congr 1; ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, not_lt]
      constructor
      · rintro ⟨⟨⟨h1, _⟩, hp⟩, hn⟩; exact ⟨⟨h1, hn⟩, hp⟩
      · rintro ⟨⟨h1, hn⟩, hp⟩; exact ⟨⟨⟨h1, by omega⟩, hp⟩, hn⟩
  have hMa := (abs_le.mp hM).1
  have hYa := (abs_le.mp hY).2
  unfold mertensPrimeConst
  linarith

/-- **Unmollified primes.** `D ≥ 1 + M^{1−2σ} (log(M/y) − 2K)/log M`. -/
theorem sum_normSq_mollifiedZetaCoeff_ge {b : ℕ → ℂ} {y M : ℕ} (hy : 1 ≤ y) (hyM : y ≤ M)
    (hM2 : 2 ≤ M) (hb1 : b 1 = 1) {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    1 + (M : ℝ) ^ (1 - 2 * σ) *
        ((Real.log M - Real.log y - 2 * mertensPrimeConst) / Real.log M) ≤
      ∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) := by
  classical
  set P := (Finset.Icc 1 M).filter (fun p => p.Prime ∧ y < p) with hP
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hlogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < M))
  have h1P : 1 ∉ P := by
    intro h
    exact Nat.not_prime_one (Finset.mem_filter.mp h).2.1
  have hsub : insert 1 P ⊆ Finset.Icc 1 M := by
    intro n hn
    rcases Finset.mem_insert.mp hn with rfl | hn
    · exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
    · exact (Finset.mem_filter.mp hn).1
  have hnonneg : ∀ n ∈ Finset.Icc 1 M, n ∉ insert 1 P →
      0 ≤ ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * σ) :=
    fun n _ _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hge := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
  rw [Finset.sum_insert h1P, mollifiedZetaCoeff_one hy, hb1] at hge
  simp only [norm_one, one_pow, Nat.cast_one, Real.one_rpow, mul_one] at hge
  have hprime : ∀ p ∈ P, (M : ℝ) ^ (1 - 2 * σ) * (Real.log p / (p : ℝ) / Real.log M) ≤
      ‖mollifiedZetaCoeff b y p‖ ^ 2 * (p : ℝ) ^ (-2 * σ) := by
    intro p hp
    obtain ⟨hpM, hpp, hyp⟩ := by simpa [hP, Finset.mem_filter] using hp
    rw [mollifiedZetaCoeff_prime hy hpp hyp, hb1, norm_one, one_pow, one_mul]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_lt.le
    have hpMr : (p : ℝ) ≤ M := by exact_mod_cast hpM.2
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
    have hlogpM : Real.log (p : ℝ) ≤ Real.log M := Real.log_le_log hp0 hpMr
    have hsplit : (p : ℝ) ^ (-2 * σ) = (p : ℝ) ^ (1 - 2 * σ) * (1 / (p : ℝ)) := by
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hp0]; congr 1; ring
    have hpow : (M : ℝ) ^ (1 - 2 * σ) ≤ (p : ℝ) ^ (1 - 2 * σ) :=
      Real.rpow_le_rpow_of_nonpos hp0 hpMr (by linarith)
    have hfrac : Real.log p / (p : ℝ) / Real.log M ≤ 1 / (p : ℝ) := by
      rw [div_div, div_le_div_iff₀ (by positivity) hp0]
      nlinarith
    rw [hsplit]
    exact mul_le_mul hpow hfrac (by positivity) (Real.rpow_nonneg hp0.le _)
  have hsumP := Finset.sum_le_sum hprime
  rw [← Finset.mul_sum, ← Finset.sum_div] at hsumP
  have hmert := sum_prime_log_div_Ioc_ge hy hyM
  have hMpow : 0 ≤ (M : ℝ) ^ (1 - 2 * σ) := Real.rpow_nonneg hMpos.le _
  have hstep : (M : ℝ) ^ (1 - 2 * σ) *
      ((Real.log M - Real.log y - 2 * mertensPrimeConst) / Real.log M) ≤
      (M : ℝ) ^ (1 - 2 * σ) * ((∑ p ∈ P, Real.log p / (p : ℝ)) / Real.log M) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hmert hlogM.le) hMpow
  linarith

/-- The closing algebra: from `A(1−η) ≤ √((1+η)A·X)`, `A ≥ T(1+c)`, `η = c/10`, `c ≤ 3/5`, get
`X ≥ T(1 + c/2)`. -/
theorem floor_closing_algebra {A X T c η : ℝ} (hT : 0 < T) (hc : 0 < c) (hc35 : c ≤ 3 / 5)
    (hη : η = c / 10) (hA : T * (1 + c) ≤ A) (hX : 0 ≤ X)
    (h : A * (1 - η) ≤ Real.sqrt ((1 + η) * A * X)) :
    T * (1 + c / 2) ≤ X := by
  have hA0 : 0 < A := lt_of_lt_of_le (by positivity) hA
  have hη0 : 0 < η := by rw [hη]; positivity
  have hη1 : η < 1 := by rw [hη]; linarith
  have hsq : (A * (1 - η)) ^ 2 ≤ (1 + η) * A * X :=
    (Real.le_sqrt (by nlinarith) (by positivity)).mp h
  have h1 : A * (1 - η) ^ 2 ≤ (1 + η) * X := by
    have : A * ((1 - η) ^ 2 * A) ≤ A * ((1 + η) * X) := by nlinarith
    have := le_of_mul_le_mul_left this hA0
    nlinarith
  have h2 : (1 - 3 * η) * (1 + η) ≤ (1 - η) ^ 2 := by nlinarith
  have h3 : A * (1 - 3 * η) ≤ X := by
    have : A * ((1 - 3 * η) * (1 + η)) ≤ (1 + η) * X := le_trans (by nlinarith) h1
    nlinarith
  have h4 : T * (1 + c) * (1 - 3 * η) ≤ A * (1 - 3 * η) :=
    mul_le_mul_of_nonneg_right hA (by rw [hη]; linarith)
  have h5 : T * (1 + c / 2) ≤ T * (1 + c) * (1 - 3 * η) := by
    rw [hη]
    have : (1 + c / 2) ≤ (1 + c) * (1 - 3 * (c / 10)) := by nlinarith
    nlinarith
  linarith

theorem floor_hundred_le_exp_five : (100 : ℝ) ≤ Real.exp 5 := by
  have h : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_gt_d9
  rw [h]
  calc (100 : ℝ) ≤ 2.7 ^ 5 := by norm_num
    _ ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5

/-- Size facts at `T = e^L` with `M = ⌊e^{L/20}⌋` and `y ≤ e^{L/100}`. -/
theorem floor_scale_facts {L : ℝ} (hL : 500 ≤ L) {M y : ℕ}
    (hMle : (M : ℝ) ≤ Real.exp (L / 20)) (hMgt : Real.exp (L / 20) - 1 < M)
    (hy : 1 ≤ y) (hyle : (y : ℝ) ≤ Real.exp (L / 100)) :
    2 ≤ M ∧ y ≤ M ∧ Real.log M ≤ L / 20 ∧ L / 20 - Real.log 2 ≤ Real.log M ∧
      Real.log y ≤ L / 100 := by
  have h5 : (100 : ℝ) ≤ Real.exp 5 := floor_hundred_le_exp_five
  have hE : Real.exp 5 ≤ Real.exp (L / 20) := Real.exp_le_exp.mpr (by linarith)
  have hM2 : 2 ≤ M := by
    have : (2 : ℝ) < M := by linarith
    exact_mod_cast this.le
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hypos : (0 : ℝ) < y := by exact_mod_cast (by omega : 0 < y)
  have hyM : y ≤ M := by
    have h1 : Real.exp (L / 100) * 2 ≤ Real.exp (L / 20) := by
      have : Real.exp (L / 20) = Real.exp (L / 100) * Real.exp (L / 25) := by
        rw [← Real.exp_add]; ring_nf
      rw [this]
      have h2 : (2 : ℝ) ≤ Real.exp (L / 25) := by
        have := Real.add_one_le_exp (L / 25); linarith
      nlinarith [Real.exp_pos (L / 100)]
    have : (y : ℝ) ≤ M := by linarith [Real.exp_pos (L / 100)]
    exact_mod_cast this
  refine ⟨hM2, hyM, ?_, ?_, ?_⟩
  · have := Real.log_le_log hMpos hMle
    rwa [Real.log_exp] at this
  · have h1 : Real.exp (L / 20) / 2 ≤ M := by linarith
    have := Real.log_le_log (by positivity) h1
    rwa [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp] at this
  · have := Real.log_le_log hypos hyle
    rwa [Real.log_exp] at this

/-- The twisted-moment error is `≤ η T` at `T = e^L`. -/
theorem floor_error_le {L η : ℝ} (hL0 : 0 ≤ L) (hη : 0 < η)
    (hL35 : Real.log (35 / η) / (19 / 50) ≤ L)
    {M y : ℕ} (hMle : (M : ℝ) ≤ Real.exp (L / 20)) (hyle : (y : ℝ) ≤ Real.exp (L / 100)) :
    (y : ℝ) ^ 2 * M * (27 * Real.sqrt (Real.exp L) * M + 8 * (M : ℝ) ^ 2) ≤
      η * Real.exp L := by
  have hsq : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
    rw [Real.sqrt_eq_iff_mul_self_eq (Real.exp_pos _).le (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  rw [hsq]
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have hy2 : (y : ℝ) ^ 2 ≤ Real.exp (L / 50) := by
    calc (y : ℝ) ^ 2 ≤ Real.exp (L / 100) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg y) hyle 2
      _ = Real.exp (L / 50) := by rw [← Real.exp_nat_mul]; ring_nf
  have hM2' : (M : ℝ) ^ 2 ≤ Real.exp (L / 10) := by
    calc (M : ℝ) ^ 2 ≤ Real.exp (L / 20) ^ 2 := pow_le_pow_left₀ hM0 hMle 2
      _ = Real.exp (L / 10) := by rw [← Real.exp_nat_mul]; ring_nf
  have hinner : 27 * Real.exp (L / 2) * M + 8 * (M : ℝ) ^ 2 ≤ 35 * Real.exp (11 / 20 * L) := by
    have h1 : Real.exp (L / 2) * M ≤ Real.exp (11 / 20 * L) := by
      calc Real.exp (L / 2) * M ≤ Real.exp (L / 2) * Real.exp (L / 20) :=
            mul_le_mul_of_nonneg_left hMle (Real.exp_pos _).le
        _ = Real.exp (11 / 20 * L) := by rw [← Real.exp_add]; ring_nf
    have h2 : Real.exp (L / 10) ≤ Real.exp (11 / 20 * L) := Real.exp_le_exp.mpr (by linarith)
    linarith
  have hprod : Real.exp (L / 50) * Real.exp (L / 20) * Real.exp (11 / 20 * L) =
      Real.exp (31 / 50 * L) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have htot : (y : ℝ) ^ 2 * M * (27 * Real.exp (L / 2) * M + 8 * (M : ℝ) ^ 2) ≤
      35 * Real.exp (31 / 50 * L) := by
    calc (y : ℝ) ^ 2 * M * (27 * Real.exp (L / 2) * M + 8 * (M : ℝ) ^ 2)
        ≤ Real.exp (L / 50) * Real.exp (L / 20) * (35 * Real.exp (11 / 20 * L)) := by
          gcongr
      _ = 35 * (Real.exp (L / 50) * Real.exp (L / 20) * Real.exp (11 / 20 * L)) := by ring
      _ = 35 * Real.exp (31 / 50 * L) := by rw [hprod]
  refine htot.trans ?_
  have hbig : 35 / η ≤ Real.exp (19 / 50 * L) := by
    have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 19 / 50)).mp hL35
    calc 35 / η = Real.exp (Real.log (35 / η)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (19 / 50 * L) := Real.exp_le_exp.mpr (by linarith)
  have hsplit : Real.exp L = Real.exp (31 / 50 * L) * Real.exp (19 / 50 * L) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  have := (div_le_iff₀ hη).mp hbig
  nlinarith [Real.exp_pos (31 / 50 * L)]

/-- The mean-value error `8M(1 + log M)` is `≤ η T` at `T = e^L`. -/
theorem floor_mvt_le {L η : ℝ} (hη : 0 < η) (hL8 : Real.log (8 / η) / (9 / 10) ≤ L) {M : ℕ}
    (hM1 : 1 ≤ M) (hMle : (M : ℝ) ≤ Real.exp (L / 20)) :
    8 * M * (1 + Real.log M) ≤ η * Real.exp L := by
  have h1 : 8 * (M : ℝ) * (1 + Real.log M) ≤ 8 * Real.exp (L / 10) := by
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hlog : Real.log (M : ℝ) ≤ L / 20 := by
      have := Real.log_le_log hMpos hMle; rwa [Real.log_exp] at this
    have h1' : 1 + Real.log (M : ℝ) ≤ Real.exp (L / 20) := by
      have := Real.add_one_le_exp (L / 20); linarith
    have hlog0 : 0 ≤ 1 + Real.log (M : ℝ) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ M by exact_mod_cast hM1); linarith
    calc 8 * (M : ℝ) * (1 + Real.log M) ≤ 8 * Real.exp (L / 20) * Real.exp (L / 20) := by
          gcongr
      _ = 8 * Real.exp (L / 10) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
  refine h1.trans ?_
  have hbig : 8 / η ≤ Real.exp (9 / 10 * L) := by
    have := (div_le_iff₀ (by norm_num : (0 : ℝ) < 9 / 10)).mp hL8
    calc 8 / η = Real.exp (Real.log (8 / η)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (9 / 10 * L) := Real.exp_le_exp.mpr (by linarith)
  have hsplit : Real.exp L = Real.exp (L / 10) * Real.exp (9 / 10 * L) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  have := (div_le_iff₀ hη).mp hbig
  nlinarith [Real.exp_pos (L / 10)]

/-- The unmollified primes give `D ≥ 1 + (3/5) e^{-a/10}` at `T = e^L`, `σ = 1/2 + a/L`. -/
theorem floor_D_ge {b : ℕ → ℂ} {y M : ℕ} {L a : ℝ} (hL500 : 500 ≤ L) (ha : 0 < a) (hLK : 100 * (2 * mertensPrimeConst + Real.log 2) + 1 ≤ L)
    (hy : 1 ≤ y) (hb1 : b 1 = 1) (hMle : (M : ℝ) ≤ Real.exp (L / 20))
    (hMgt : Real.exp (L / 20) - 1 < M) (hyle : (y : ℝ) ≤ Real.exp (L / 100)) :
    1 + 3 / 5 * Real.exp (-(a / 10)) ≤
      ∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ ^ 2 * (n : ℝ) ^ (-2 * (1 / 2 + a / L)) := by
  obtain ⟨hM2, hyM, _, hlogMge, hlogy⟩ := floor_scale_facts hL500 hMle hMgt hy hyle
  have hL0 : 0 < L := by linarith
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hσ12 : 1 / 2 ≤ 1 / 2 + a / L := by have := div_pos ha hL0; linarith
  have hDge := sum_normSq_mollifiedZetaCoeff_ge (b := b) hy hyM hM2 hb1 hσ12
  have hpowM : Real.exp (-(a / 10)) ≤ (M : ℝ) ^ (1 - 2 * (1 / 2 + a / L)) := by
    have h1 : Real.exp (L / 20) ^ (1 - 2 * (1 / 2 + a / L)) ≤
        (M : ℝ) ^ (1 - 2 * (1 / 2 + a / L)) :=
      Real.rpow_le_rpow_of_nonpos hMpos hMle (by have := div_pos ha hL0; linarith)
    have h2 : Real.exp (L / 20) ^ (1 - 2 * (1 / 2 + a / L)) = Real.exp (-(a / 10)) := by
      rw [← Real.exp_mul]; congr 1; field_simp; ring
    linarith
  have hratio : 3 / 5 ≤ (Real.log M - Real.log y - 2 * mertensPrimeConst) / Real.log M := by
    have h2 := Real.log_two_lt_d9
    have hlogM0 : 0 < Real.log (M : ℝ) := by linarith
    rw [le_div_iff₀ hlogM0]
    linarith
  have h := mul_le_mul hpowM hratio (by norm_num) (Real.rpow_nonneg hMpos.le _)
  linarith

/-- **The floor under every short mollified mean square right of the line.** For every `a > 0`, for
all large `T`, every mollifier `Ψ = Σ_{d ≤ y} b_d d^{-s}` with `y ≤ T^{1/100}`, `b_1 = 1`,
`|b_d| ≤ 1` satisfies `∫_T^{2T} |ζΨ(1/2 + a/log T + it)|² dt ≥ (1 + (3/10) e^{-a/10}) T`. -/
theorem exists_eventually_integral_normSq_zetaMollified_rightShift_ge {a : ℝ} (ha : 0 < a) :
    ∀ᶠ T in atTop, ∀ y : ℕ, 1 ≤ y → (y : ℝ) ≤ T ^ ((1 : ℝ) / 100) → ∀ b : ℕ → ℂ, b 1 = 1 →
      (∀ d ∈ Finset.Icc 1 y, ‖b d‖ ≤ 1) →
      (1 + 3 / 10 * Real.exp (-(a / 10))) * T ≤
        ∫ t in T..(2 * T), ‖riemannZeta (((1 / 2 + a / Real.log T : ℝ) : ℂ) + (t : ℂ) * I) *
          edPoly b (Finset.Icc 1 y) (((1 / 2 + a / Real.log T : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  set c : ℝ := 3 / 5 * Real.exp (-(a / 10)) with hcdef
  have hc0 : 0 < c := by positivity
  have hc35 : c ≤ 3 / 5 := by
    have : Real.exp (-(a / 10)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    rw [hcdef]; linarith
  have hη0 : 0 < c / 10 := by positivity
  filter_upwards [eventually_ge_atTop (Real.exp (max (max 500 (2 * a + 2))
    (max (100 * (2 * mertensPrimeConst + Real.log 2) + 1)
      (max (Real.log (35 / (c / 10)) / (19 / 50)) (Real.log (8 / (c / 10)) / (9 / 10))))))]
    with T hTL₀
  intro y hy hyle b hb1 hb
  have hT0 : 0 < T := lt_of_lt_of_le (Real.exp_pos _) hTL₀
  have hLL₀ := Real.log_le_log (Real.exp_pos _) hTL₀
  rw [Real.log_exp] at hLL₀
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log T := ⟨_, rfl⟩
  have hTexp : T = Real.exp L := by rw [hLdef, Real.exp_log hT0]
  rw [← hLdef] at hLL₀
  subst hTexp
  simp only [Real.log_exp] at hyle ⊢
  have hL500 : 500 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLL₀
  have hLa : 2 * a + 2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLL₀
  have hLK : 100 * (2 * mertensPrimeConst + Real.log 2) + 1 ≤ L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLL₀
  have hL35 : Real.log (35 / (c / 10)) / (19 / 50) ≤ L :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)) hLL₀
  have hL8 : Real.log (8 / (c / 10)) / (9 / 10) ≤ L :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)) hLL₀
  have hL0 : 0 < L := by linarith
  have hyle' : (y : ℝ) ≤ Real.exp (L / 100) := by
    rw [← Real.exp_mul] at hyle; rwa [show L * (1 / 100) = L / 100 by ring] at hyle
  obtain ⟨M, hMdef⟩ : ∃ M : ℕ, M = ⌊Real.exp (L / 20)⌋₊ := ⟨_, rfl⟩
  have hMle : (M : ℝ) ≤ Real.exp (L / 20) := by rw [hMdef]; exact Nat.floor_le (by positivity)
  have hMgt : Real.exp (L / 20) - 1 < M := by
    rw [hMdef]; have := Nat.lt_floor_add_one (Real.exp (L / 20)); linarith
  obtain ⟨hM2, -, -, -, -⟩ := floor_scale_facts hL500 hMle hMgt hy hyle'
  have hσ12 : 1 / 2 ≤ 1 / 2 + a / L := by have := div_pos ha hL0; linarith
  have hσ1 : 1 / 2 + a / L < 1 := by
    have : a / L < 1 / 2 := by rw [div_lt_iff₀ hL0]; linarith
    linarith
  have hD1c := floor_D_ge (b := b) hL500 ha hLK hy hb1 hMle hMgt hyle'
  rw [← hcdef] at hD1c
  set D : ℝ := ∑ n ∈ Finset.Icc 1 M, ‖mollifiedZetaCoeff b y n‖ ^ 2 *
    (n : ℝ) ^ (-2 * (1 / 2 + a / L)) with hD
  have hD0 : 0 < D := by linarith
  have hE := floor_error_le hL0.le hη0 hL35 (M := M) hMle hyle'
  have hMVT := floor_mvt_le hη0 hL8 (by omega : 1 ≤ M) hMle
  have hT4 : 4 ≤ Real.exp L := by have := Real.add_one_le_exp L; linarith
  have hcore := mollified_meanSquare_floor_core hσ12 hσ1 hT4 hy (by omega : 1 ≤ M) hb hD0
  rw [← hD] at hcore
  set X : ℝ := ∫ t in Real.exp L..(2 * Real.exp L), ‖riemannZeta (((1 / 2 + a / L : ℝ) : ℂ) +
    (t : ℂ) * I) * edPoly b (Finset.Icc 1 y) (((1 / 2 + a / L : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2 with hX
  have hX0 : 0 ≤ X := intervalIntegral.integral_nonneg (by linarith) fun t _ => by positivity
  have hY : (Real.exp L + 8 * M * (1 + Real.log M)) * D * X ≤
      (1 + c / 10) * (Real.exp L * D) * X := by
    have : (Real.exp L + 8 * M * (1 + Real.log M)) * D ≤ (1 + c / 10) * (Real.exp L * D) := by
      nlinarith
    exact mul_le_mul_of_nonneg_right this hX0
  have hlow : Real.exp L * D * (1 - c / 10) ≤
      Real.sqrt ((1 + c / 10) * (Real.exp L * D) * X) := by
    have h1 : Real.exp L * D * (1 - c / 10) ≤ Real.exp L * D -
        (y : ℝ) ^ 2 * M * (27 * Real.sqrt (Real.exp L) * M + 8 * (M : ℝ) ^ 2) := by
      have : c / 10 * Real.exp L ≤ c / 10 * (Real.exp L * D) := by
        have := mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ D) (Real.exp_pos L).le
        nlinarith
      nlinarith
    exact h1.trans (hcore.trans (Real.sqrt_le_sqrt hY))
  have hA : Real.exp L * (1 + c) ≤ Real.exp L * D :=
    mul_le_mul_of_nonneg_left hD1c (Real.exp_pos L).le
  have hfin := floor_closing_algebra (Real.exp_pos L) hc0 hc35 rfl hA hX0 hlow
  calc (1 + 3 / 10 * Real.exp (-(a / 10))) * Real.exp L = Real.exp L * (1 + c / 2) := by
        rw [hcdef]; ring
    _ ≤ X := hfin

end RHTower
