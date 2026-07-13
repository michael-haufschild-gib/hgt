import Mathlib

/-!
# Geometric log-ratio resonance forces an algebraic limit

If the successive log-magnitude ratios `b(n+1)/b n` converge to a finite limit `λ`, then for
every fixed shift the ratio scales by a power (`ratio_tendsto_pow`): `b(n+r)/b n → λ^r`.

Consequently a **sublinear integer shift resonance** — a nonzero integer (Laurent) polynomial
`Q` and a subsequence `qₖ → ∞` along which `(∑_r Q_r · b(qₖ+r))/b(qₖ) → 0` — forces `Q(λ) = 0`
(`logRatio_resonance_aeval_eq_zero`), because the resonance ratio converges to `Q(λ)` along the
whole sequence.  Hence such a `λ` is algebraic (`logRatio_isAlgebraic_of_resonance`).  This is
the resonance-to-algebraicity half of the DA log-ratio law, independent of the differential
input that produces the resonance.
-/

open Filter Topology Polynomial

namespace GaloisForLFunctions

/-- **Shift-power ratio limit.**  If `b(n+1)/b n → λ`, then `b(n+r)/b n → λ^r` for every fixed
shift `r`, by telescoping the ratio. -/
theorem ratio_tendsto_pow {b : ℕ → ℝ} {lam : ℝ} (hb : ∀ᶠ n in atTop, b n ≠ 0)
    (hlam : Tendsto (fun n => b (n + 1) / b n) atTop (𝓝 lam)) (r : ℕ) :
    Tendsto (fun n => b (n + r) / b n) atTop (𝓝 (lam ^ r)) := by
  induction r with
  | zero =>
    simp only [Nat.add_zero, pow_zero]
    refine (tendsto_const_nhds (x := (1 : ℝ))).congr' ?_
    filter_upwards [hb] with n hn
    rw [div_self hn]
  | succ r ih =>
    have hshift : Tendsto (fun n => b (n + r + 1) / b (n + r)) atTop (𝓝 lam) :=
      hlam.comp (tendsto_add_atTop_nat r)
    have hbshift : ∀ᶠ n in atTop, b (n + r) ≠ 0 := (tendsto_add_atTop_nat r).eventually hb
    have hprod : Tendsto (fun n => (b (n + r + 1) / b (n + r)) * (b (n + r) / b n)) atTop
        (𝓝 (lam * lam ^ r)) := hshift.mul ih
    rw [pow_succ']
    refine Tendsto.congr' ?_ hprod
    filter_upwards [hbshift] with n hn
    rw [show n + (r + 1) = n + r + 1 from by ring]
    field_simp

/-- **Resonance forces a root.**  A sublinear integer shift resonance along a subsequence
forces the limit ratio to be a root of the resonance polynomial: `Q(λ) = 0`. -/
theorem logRatio_resonance_aeval_eq_zero {b : ℕ → ℝ} {lam : ℝ}
    (hb : ∀ᶠ n in atTop, b n ≠ 0)
    (hlam : Tendsto (fun n => b (n + 1) / b n) atTop (𝓝 lam))
    (Q : Polynomial ℤ) {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hres : Tendsto (fun k => (∑ r ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff r : ℝ) * b (q k + r)) / b (q k)) atTop (𝓝 0)) :
    (aeval lam) Q = 0 := by
  set R : ℕ → ℝ := fun n => ∑ r ∈ Finset.range (Q.natDegree + 1),
      (Q.coeff r : ℝ) * (b (n + r) / b n) with hR
  have hae : (aeval lam) Q
      = ∑ r ∈ Finset.range (Q.natDegree + 1), (Q.coeff r : ℝ) * lam ^ r := by
    rw [aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Algebra.smul_def]; simp
  have hRfull : Tendsto R atTop (𝓝 ((aeval lam) Q)) := by
    rw [hae]
    refine tendsto_finsetSum _ fun r _ => ?_
    exact tendsto_const_nhds.mul (ratio_tendsto_pow hb hlam r)
  have hcomp : Tendsto (fun k => R (q k)) atTop (𝓝 ((aeval lam) Q)) := hRfull.comp hq
  have hEq : (fun k => R (q k)) = fun k => (∑ r ∈ Finset.range (Q.natDegree + 1),
      (Q.coeff r : ℝ) * b (q k + r)) / b (q k) := by
    funext k
    rw [hR, Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_div_assoc]
  rw [hEq] at hcomp
  exact tendsto_nhds_unique hcomp hres

/-- **Algebraicity of the log-ratio limit.**  A limit ratio admitting a nonzero integer
shift-resonance polynomial is algebraic. -/
theorem logRatio_isAlgebraic_of_resonance {b : ℕ → ℝ} {lam : ℝ}
    (hb : ∀ᶠ n in atTop, b n ≠ 0)
    (hlam : Tendsto (fun n => b (n + 1) / b n) atTop (𝓝 lam))
    (Q : Polynomial ℤ) (hQ : Q ≠ 0) {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hres : Tendsto (fun k => (∑ r ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff r : ℝ) * b (q k + r)) / b (q k)) atTop (𝓝 0)) :
    IsAlgebraic ℤ lam :=
  ⟨Q, hQ, logRatio_resonance_aeval_eq_zero hb hlam Q hq hres⟩

/-- The transcendence obstruction: a transcendental limit ratio admits no nonzero integer
shift-resonance, so any such resonance rules out transcendence. -/
theorem not_transcendental_of_logRatio_resonance {b : ℕ → ℝ} {lam : ℝ}
    (hb : ∀ᶠ n in atTop, b n ≠ 0)
    (hlam : Tendsto (fun n => b (n + 1) / b n) atTop (𝓝 lam))
    (Q : Polynomial ℤ) (hQ : Q ≠ 0) {q : ℕ → ℕ} (hq : Tendsto q atTop atTop)
    (hres : Tendsto (fun k => (∑ r ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff r : ℝ) * b (q k + r)) / b (q k)) atTop (𝓝 0)) :
    ¬ Transcendental ℚ lam := by
  have hz : IsAlgebraic ℤ lam := logRatio_isAlgebraic_of_resonance hb hlam Q hQ hq hres
  obtain ⟨p, hp0, hpe⟩ := hz
  have : IsAlgebraic ℚ lam := by
    refine ⟨p.map (algebraMap ℤ ℚ), ?_, ?_⟩
    · exact fun hc => hp0 ((Polynomial.map_eq_zero_iff
        (algebraMap ℤ ℚ).injective_int).mp hc)
    · rw [aeval_map_algebraMap]; exact hpe
  exact fun h => h this

end GaloisForLFunctions
