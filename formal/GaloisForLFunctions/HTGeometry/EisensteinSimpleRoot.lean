import GaloisForLFunctions.HTGeometry.CoeffDenominatorBound

/-!
# Eisenstein's theorem at a simple root

If `y` is a root of a polynomial `F` whose coefficients are power series over a subring `A`, and the
derivative `F′(y)` has a *nonzero constant term*, then the coefficients of `y` have geometrically
bounded denominators: `q ^ (2N) · y_N ∈ q · A` for every `N`, where `q` is any element of `A`
divisible by that constant term and clearing the first three coefficients of `y`.

This is the substance of Eisenstein's theorem on algebraic power series in the unramified case.
The proof is the recursion `(F′(y))_0 · y_n = − (F(y_{<n}))_n` together with the split

`F(w) = F₀ + F₁ · w + w² · Q(w)`,   `Q = F.divX.divX`,

into three parts, each of which pays for the single factor of `(F′(y))_0` lost at that step in a
different way:

* `F₀` contributes an element of `A` in degree `n`, and `q ^ (2n)` is a large power for `n ≥ 3`;
* `F₁ · w` is *linear* in `w`, and pays through the strict drop of the index: `w` is the truncation
  below degree `n`, so every surviving coefficient of `w` sits at index at most `n − 1`, which is one
  factor `q ^ (2 : ℕ)` better than the normalisation at `n`;
* `w² · Q(w)` is *quadratic* in `w`, and pays through the gain: two bounded factors gain `q ^ (2 : ℕ)`.

The exponent `2` is exactly what makes the first two mechanisms overlap: the index drop is worth
`q ^ (2 : ℕ)` and the loss is `q ^ (1 : ℕ)`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

variable {K : Type*} [Field K]

/-- The split of a polynomial into constant, linear, and quadratic-and-higher parts. -/
theorem eval_split_eisensteinSimpleRoot (F : Polynomial (PowerSeries K)) (w : PowerSeries K) :
    F.eval w = F.coeff 0 + F.coeff 1 * w + w ^ (2 : ℕ) * (F.divX.divX).eval w := by
  have h1 : F.eval w = (F.divX).eval w * w + F.coeff 0 := by
    conv_lhs => rw [← Polynomial.divX_mul_X_add F]
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  have h2 : (F.divX).eval w = (F.divX.divX).eval w * w + F.coeff 1 := by
    conv_lhs => rw [← Polynomial.divX_mul_X_add F.divX]
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.coeff_divX]
  rw [h1, h2]
  ring

/-- **Eisenstein's theorem at a simple root.** -/
theorem coeffBnd_of_isRoot_of_constantCoeff_ne_zero {A : Subring K} {q : K} (hq : q ∈ A)
    (hq0 : q ≠ 0) {F : Polynomial (PowerSeries K)}
    (hF : ∀ i N, PowerSeries.coeff N (F.coeff i) ∈ A)
    {y : PowerSeries K} (hroot : F.eval y = 0)
    {a : K} (ha : a ∈ A)
    (hqa : q = PowerSeries.coeff 0 ((Polynomial.derivative F).eval y) * a)
    (hbase : ∀ j, j ≤ 2 → IsPowMul A q 1 (q ^ (2 * j) * PowerSeries.coeff j y)) :
    CoeffBnd A q 2 1 y := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with hn | hn
    · exact hbase n (by omega)
    -- the truncation below degree `n` is bounded, by the induction hypothesis
    have hwbnd : CoeffBnd A q 2 1 (truncPS n y) := by
      intro j
      rw [coeff_truncPS]
      by_cases hj : j < n
      · rw [if_pos hj]
        exact ih j hj
      · rw [if_neg hj, mul_zero]
        exact isPowMul_zero
    -- the linear part pays through the strict drop of the index
    have hA1 : IsPowMul A q 1
        (q ^ (2 * (n - 1)) * PowerSeries.coeff n (F.coeff 1 * truncPS n y)) := by
      rw [PowerSeries.coeff_mul, Finset.mul_sum]
      refine IsPowMul.sum _ _ fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_cases hp2 : p.2 < n
      · have hexp : q ^ (2 * (n - 1)) = q ^ (2 * (n - 1 - p.2)) * q ^ (2 * p.2) := by
          rw [← pow_add]
          congr 1
          omega
        have hrw : q ^ (2 * (n - 1 - p.2)) * q ^ (2 * p.2) *
            (PowerSeries.coeff p.1 (F.coeff 1) * PowerSeries.coeff p.2 (truncPS n y))
            = PowerSeries.coeff p.1 (F.coeff 1) *
              (q ^ (2 * (n - 1 - p.2)) *
                (q ^ (2 * p.2) * PowerSeries.coeff p.2 (truncPS n y))) := by ring
        rw [hexp, hrw]
        exact IsPowMul.mul_left (hF 1 p.1)
          (IsPowMul.mul_left (A.pow_mem hq _) (hwbnd p.2))
      · have hzero : PowerSeries.coeff p.2 (truncPS n y) = 0 := by
          rw [coeff_truncPS, if_neg hp2]
        rw [hzero, mul_zero, mul_zero]
        exact isPowMul_zero
    -- the quadratic part pays through the gain
    have hQmem : ∀ i N, PowerSeries.coeff N ((F.divX.divX).coeff i) ∈ A := by
      intro i N
      rw [Polynomial.coeff_divX, Polynomial.coeff_divX]
      exact hF (i + 1 + 1) N
    have hA2 : CoeffBnd A q 2 2 ((truncPS n y) ^ (2 : ℕ) * (F.divX.divX).eval (truncPS n y)) := by
      have hsq : CoeffBnd A q 2 (1 + 1) ((truncPS n y) ^ (2 : ℕ)) := by
        have := hwbnd.mul hwbnd
        rwa [← sq] at this
      have hev : CoeffBnd A q 2 0 ((F.divX.divX).eval (truncPS n y)) :=
        CoeffBnd.eval hq (fun i => coeffBnd_of_coeff_mem hq 2 (hQmem i)) hwbnd
      have := hsq.mul hev
      rwa [Nat.add_zero] at this
    -- the three parts together
    have htotal : IsPowMul A q 2 (q ^ (2 * n) * PowerSeries.coeff n (F.eval (truncPS n y))) := by
      rw [eval_split_eisensteinSimpleRoot, map_add, map_add, mul_add, mul_add]
      refine IsPowMul.add (IsPowMul.add ?_ ?_) (hA2 n)
      · refine ⟨q ^ (2 * n - 2) * PowerSeries.coeff n (F.coeff 0),
          A.mul_mem (A.pow_mem hq _) (hF 0 n), ?_⟩
        rw [← mul_assoc, ← pow_add]
        congr 2
        omega
      · obtain ⟨c, hc, hce⟩ := hA1
        refine ⟨q * c, A.mul_mem hq hc, ?_⟩
        have hexp : q ^ (2 * n) = q ^ (2 : ℕ) * q ^ (2 * (n - 1)) := by
          rw [← pow_add]
          congr 1
          omega
        rw [hexp, mul_assoc, hce]
        ring
    -- the recursion turns that into the bound at `n`
    have hrec := coeff_deriv_mul_coeff_eq (r := 0) (n := n) hroot (by omega)
      (fun j hj => absurd hj (Nat.not_lt_zero j))
    rw [Nat.add_zero] at hrec
    obtain ⟨c, hc, hce⟩ := htotal
    have hkey : q * (q ^ (2 * n) * PowerSeries.coeff n y) = q * (q * (-(a * c))) := by
      have hqy : q * PowerSeries.coeff n y
          = -(a * PowerSeries.coeff n (F.eval (truncPS n y))) := by
        rw [hqa]
        calc PowerSeries.coeff 0 ((Polynomial.derivative F).eval y) * a * PowerSeries.coeff n y
            = a * (PowerSeries.coeff 0 ((Polynomial.derivative F).eval y)
                * PowerSeries.coeff n y) := by ring
          _ = a * -(PowerSeries.coeff n (F.eval (truncPS n y))) := by rw [hrec]
          _ = -(a * PowerSeries.coeff n (F.eval (truncPS n y))) := by ring
      calc q * (q ^ (2 * n) * PowerSeries.coeff n y)
          = q ^ (2 * n) * (q * PowerSeries.coeff n y) := by ring
        _ = q ^ (2 * n) * -(a * PowerSeries.coeff n (F.eval (truncPS n y))) := by rw [hqy]
        _ = -(a * (q ^ (2 * n) * PowerSeries.coeff n (F.eval (truncPS n y)))) := by ring
        _ = -(a * (q ^ (2 : ℕ) * c)) := by rw [hce]
        _ = q * (q * (-(a * c))) := by ring
    refine ⟨-(a * c), A.neg_mem (A.mul_mem ha hc), ?_⟩
    have := mul_left_cancel₀ hq0 hkey
    rw [this, pow_one]

/-- **Eisenstein at a simple root, existence form.**  If the fraction field of `A` is `K`, the
scaling element can be constructed: it is the constant term of `F′(y)` times enough of `A` to clear
the denominators of that constant term and of the first two coefficients of `y`. -/
theorem exists_coeffBnd_of_isRoot {A : Subring K}
    (hfrac : ∀ x : K, ∃ d ∈ A, d ≠ 0 ∧ d * x ∈ A)
    {F : Polynomial (PowerSeries K)} (hF : ∀ i N, PowerSeries.coeff N (F.coeff i) ∈ A)
    {y : PowerSeries K} (hroot : F.eval y = 0)
    (hu : PowerSeries.coeff 0 ((Polynomial.derivative F).eval y) ≠ 0)
    (hy0 : PowerSeries.coeff 0 y = 0) :
    ∃ q ∈ A, q ≠ 0 ∧ CoeffBnd A q 2 1 y := by
  classical
  obtain ⟨e, he, he0, heu⟩ := hfrac (PowerSeries.coeff 0 ((Polynomial.derivative F).eval y))
  obtain ⟨d₁, hd₁, hd₁0, hd₁y⟩ := hfrac (PowerSeries.coeff 1 y)
  obtain ⟨d₂, hd₂, hd₂0, hd₂y⟩ := hfrac (PowerSeries.coeff 2 y)
  have hqmem : PowerSeries.coeff 0 ((Polynomial.derivative F).eval y) * (e * d₁ * d₂) ∈ A := by
    have hrw : PowerSeries.coeff 0 ((Polynomial.derivative F).eval y) * (e * d₁ * d₂)
        = e * PowerSeries.coeff 0 ((Polynomial.derivative F).eval y) * d₁ * d₂ := by ring
    rw [hrw]
    exact A.mul_mem (A.mul_mem heu hd₁) hd₂
  refine ⟨PowerSeries.coeff 0 ((Polynomial.derivative F).eval y) * (e * d₁ * d₂), hqmem,
    mul_ne_zero hu (mul_ne_zero (mul_ne_zero he0 hd₁0) hd₂0), ?_⟩
  refine coeffBnd_of_isRoot_of_constantCoeff_ne_zero hqmem
    (mul_ne_zero hu (mul_ne_zero (mul_ne_zero he0 hd₁0) hd₂0)) hF hroot
    (A.mul_mem (A.mul_mem he hd₁) hd₂) rfl ?_
  intro j hj
  interval_cases j
  · rw [Nat.mul_zero, pow_zero, one_mul, hy0]
    exact isPowMul_zero
  · refine ⟨PowerSeries.coeff 0 ((Polynomial.derivative F).eval y) * (e * d₁ * d₂)
      * PowerSeries.coeff 1 y, ?_, by norm_num; ring⟩
    have hrw : PowerSeries.coeff 0 ((Polynomial.derivative F).eval y) * (e * d₁ * d₂)
        * PowerSeries.coeff 1 y
        = e * PowerSeries.coeff 0 ((Polynomial.derivative F).eval y) * d₂
          * (d₁ * PowerSeries.coeff 1 y) := by ring
    rw [hrw]
    exact A.mul_mem (A.mul_mem heu hd₂) hd₁y
  · refine ⟨(PowerSeries.coeff 0 ((Polynomial.derivative F).eval y) * (e * d₁ * d₂)) ^ (3 : ℕ)
      * PowerSeries.coeff 2 y, ?_, by norm_num; ring⟩
    have hrw : (PowerSeries.coeff 0 ((Polynomial.derivative F).eval y) * (e * d₁ * d₂)) ^ (3 : ℕ)
        * PowerSeries.coeff 2 y
        = (e * PowerSeries.coeff 0 ((Polynomial.derivative F).eval y)) ^ (3 : ℕ) * d₁ ^ (3 : ℕ) * d₂ ^ (2 : ℕ)
          * (d₂ * PowerSeries.coeff 2 y) := by ring
    rw [hrw]
    exact A.mul_mem (A.mul_mem (A.mul_mem (A.pow_mem heu 3) (A.pow_mem hd₁ 3))
      (A.pow_mem hd₂ 2)) hd₂y

end GaloisForLFunctions.HTGeometry
