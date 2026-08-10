import GaloisForLFunctions.HTGeometry.AbelianZetaGas.DefectLadder
import GaloisForLFunctions.HTGeometry.EulerQGammaGenusOne

/-!
# The modulus budget and the counterterm that pays it

The modulus of a product of characteristic functions twisted by *any* unimodular gauge is exactly
`exp(−Δ)`, where `Δ` is the total realization defect: a phase can never change a modulus.  The
genus-one counterterm of the Euler `q`-Gamma process, by contrast, has modulus `exp(q(1 − cos θ))`
at each prime — exactly the leading term of the defect.  Phase cannot pay a modulus debt; the
counterterm pays it at the exact rate.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex

/-- The realization defect of one prime at imaginary argument `t`. -/
noncomputable def primeDefect (q : RealEulerNome) (t : ℝ) : ℝ :=
  -Real.log ‖qGammaOn q (1 + (t : ℂ) * Complex.I)‖

theorem norm_qGammaOn_pos (q : RealEulerNome) (t : ℝ) :
    0 < ‖qGammaOn q (1 + (t : ℂ) * Complex.I)‖ := by
  have hbase : (0 : ℝ) < 1 - q.val := by have := q.lt_one; linarith
  have hQpos : 0 < realQFactorialInf q := realQFactorialInf_pos q
  have hDne : defectProduct q (phaseAngle q t) ≠ 0 := defectProduct_ne_zero q _
  have hnormcpow : ‖((1 - q.val : ℝ) : ℂ) ^ (1 - (1 + (t : ℂ) * Complex.I))‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hbase]
    have hre : (1 - (1 + (t : ℂ) * Complex.I)).re = 0 := by simp
    rw [hre, Real.rpow_zero]
  have hnorm : ‖qGammaOn q (1 + (t : ℂ) * Complex.I)‖
      = realQFactorialInf q / ‖defectProduct q (phaseAngle q t)‖ := by
    rw [qGammaOn, norm_mul, hnormcpow, one_mul, norm_div,
      qDenomProduct_eq_defectProduct, Complex.norm_real, Real.norm_of_nonneg hQpos.le]
  rw [hnorm]
  exact div_pos hQpos (norm_pos_iff.mpr hDne)

/-! ## A unimodular gauge cannot change the modulus -/

/-- **Theorem 2.2, item 1 (the identity behind it).**  Twisting each factor by an arbitrary
unimodular function leaves the modulus of the product equal to `exp(−Δ)`, where `Δ` is the total
realization defect. -/
theorem norm_prod_gauge (q : Nat.Primes → RealEulerNome) (t : ℝ) (u : Nat.Primes → ℂ)
    (hu : ∀ p, ‖u p‖ = 1) (s : Finset Nat.Primes) :
    ‖∏ p ∈ s, (qGammaOn (q p) (1 + (t : ℂ) * Complex.I) * u p)‖
      = Real.exp (-∑ p ∈ s, primeDefect (q p) t) := by
  rw [norm_prod]
  have hterm : ∀ p ∈ s, ‖qGammaOn (q p) (1 + (t : ℂ) * Complex.I) * u p‖
      = ‖qGammaOn (q p) (1 + (t : ℂ) * Complex.I)‖ := by
    intro p _
    rw [norm_mul, hu p, mul_one]
  rw [Finset.prod_congr rfl hterm]
  have hexp : -∑ p ∈ s, primeDefect (q p) t
      = ∑ p ∈ s, Real.log ‖qGammaOn (q p) (1 + (t : ℂ) * Complex.I)‖ := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [primeDefect, neg_neg]
  rw [hexp, Real.exp_sum]
  refine Finset.prod_congr rfl fun p _ => ?_
  exact (Real.exp_log (norm_qGammaOn_pos (q p) t)).symm

/-! ## The genus-one counterterm pays the leading budget -/

/-- **Theorem 2.2, item 3.**  The genus-one counterterm of the Euler `q`-Gamma process has modulus
`exp(q(1 − cos θ))` — exactly the leading term of the realization defect. -/
theorem norm_exp_neg_eqgActivation (q : RealEulerNome) (t : ℝ) :
    ‖Complex.exp (-(eqgActivation q ((t : ℂ) * Complex.I)))‖
      = Real.exp (q.val * (1 - Real.cos (phaseAngle q t))) := by
  rw [Complex.norm_exp]
  congr 1
  have hcpow : (q.val : ℂ) ^ (1 + (t : ℂ) * Complex.I)
      = (q.val : ℂ) * modePhase (phaseAngle q t) := by
    rw [Complex.cpow_add _ _ q.complex_ne_zero, Complex.cpow_one, qcpow_mul_I]
  rw [eqgActivation, hcpow]
  have hre1 : ((q.val : ℂ) * ((t : ℂ) * Complex.I - 1)).re = -q.val := by
    simp [Complex.mul_re]
  have hre2 : ((q.val : ℂ) * modePhase (phaseAngle q t)).re
      = q.val * Real.cos (phaseAngle q t) := by
    rw [modePhase, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.ofReal_re,
      Complex.ofReal_im, Real.cos_neg]
    ring
  rw [Complex.neg_re, Complex.add_re, hre1, hre2]
  ring

/-! ## The counterterm stabilizes the modulus -/

/-- **Theorem 2.2, items 2–3 in operative form.**  The modulus of the counterterm-renormalized
product is `exp` of the difference between the leading budget and the true defect. -/
theorem norm_prod_renorm {σ : ℝ} (hσ : 0 < σ) (t : ℝ) (s : Finset Nat.Primes) :
    ‖∏ p ∈ s, (qGammaOn (primeNome hσ p) (1 + (t : ℂ) * Complex.I)
        * Complex.exp (-(eqgActivation (primeNome hσ p) ((t : ℂ) * Complex.I))))‖
      = Real.exp (∑ p ∈ s,
          ((primeNome hσ p).val * (1 - Real.cos (phaseAngle (primeNome hσ p) t))
            - primeDefect (primeNome hσ p) t)) := by
  rw [norm_prod, Real.exp_sum]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [norm_mul, norm_exp_neg_eqgActivation, Real.exp_sub,
    ← Real.exp_log (norm_qGammaOn_pos (primeNome hσ p) t)]
  have hdef : Real.log ‖qGammaOn (primeNome hσ p) (1 + (t : ℂ) * Complex.I)‖
      = -primeDefect (primeNome hσ p) t := by
    rw [primeDefect, neg_neg]
  rw [hdef, Real.exp_neg]
  field_simp

/-- **The renormalized modulus exponent converges absolutely.**  Throughout the condensed chamber
the genus-one counterterm pays the modulus budget up to an absolutely summable correction, so the
renormalized product keeps a finite nonzero modulus. -/
theorem summable_renorm_exponent {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ) (t : ℝ) :
    Summable (fun p : Nat.Primes =>
      (primeNome hσ p).val * (1 - Real.cos (phaseAngle (primeNome hσ p) t))
        - primeDefect (primeNome hσ p) t) := by
  have h := (summable_defect_sub_leading hσ hhalf t).neg
  refine h.congr fun p => ?_
  rw [primeDefect]
  ring

end GaloisForLFunctions.HTGeometry
