import GaloisForLFunctions.HTGeometry.DyadicFisherDecomposition
import GaloisForLFunctions.RHTower.SquarefreeCriticalNormalCone

/-!
# The critical Hellinger curvatures

`prime-valuation-dyadic-fermion-normal-cone-law`, equations `(18)` and `(19)`.

Both the geometric affinity and each of its binary digits have their radial logarithm of the shape

`Λ_{a,μ}(c) = log(1 + a e^{μ c}) - ½ log(1 + a) - ½ log(1 + a e^{2 μ c})`,

whose first derivative vanishes at the critical source and whose second derivative there is
`-μ² a/(1+a)²`.  Reading it at `a = q^{2^j}`, `μ = 2^j log p` gives the digit curvature `(19)`; reading
the reflected instance `a = -q`, `μ = log p` gives the geometric curvature `(18)`.  The exact
identity `(20)` says the second is the sum of the first over `j`.
-/

open Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The universal radial log-affinity kernel. -/
def logAffinityKernel (a μ c : ℝ) : ℝ :=
  Real.log (1 + a * Real.exp (μ * c)) - Real.log (1 + a) / 2
    - Real.log (1 + a * Real.exp (2 * μ * c)) / 2

/-- Its first derivative. -/
def logAffinityKernelDeriv (a μ c : ℝ) : ℝ :=
  a * μ * Real.exp (μ * c) / (1 + a * Real.exp (μ * c))
    - a * μ * Real.exp (2 * μ * c) / (1 + a * Real.exp (2 * μ * c))

theorem hasDerivAt_logAffinityKernel {a μ c : ℝ}
    (h1 : 1 + a * Real.exp (μ * c) ≠ 0) (h2 : 1 + a * Real.exp (2 * μ * c) ≠ 0) :
    HasDerivAt (logAffinityKernel a μ) (logAffinityKernelDeriv a μ c) c := by
  have he1 : HasDerivAt (fun x : ℝ => Real.exp (μ * x)) (Real.exp (μ * c) * μ) c := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (μ * c)).comp c (by simpa using (hasDerivAt_id c).const_mul μ)
  have he2 : HasDerivAt (fun x : ℝ => Real.exp (2 * μ * x)) (Real.exp (2 * μ * c) * (2 * μ)) c := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (2 * μ * c)).comp c (by simpa using (hasDerivAt_id c).const_mul (2 * μ))
  have hE1 : HasDerivAt (fun x : ℝ => 1 + a * Real.exp (μ * x))
      (a * μ * Real.exp (μ * c)) c := by
    exact ((he1.const_mul a).const_add 1).congr_deriv (by ring)
  have hE2 : HasDerivAt (fun x : ℝ => 1 + a * Real.exp (2 * μ * x))
      (a * (2 * μ) * Real.exp (2 * μ * c)) c := by
    exact ((he2.const_mul a).const_add 1).congr_deriv (by ring)
  have hL1 := (Real.hasDerivAt_log h1).comp c hE1
  have hL2 := (Real.hasDerivAt_log h2).comp c hE2
  have hres := (hL1.sub_const (Real.log (1 + a) / 2)).sub (hL2.div_const 2)
  refine hres.congr_deriv ?_
  simp only [logAffinityKernelDeriv]
  field_simp

/-- **The critical source is a stationary point.** -/
theorem logAffinityKernelDeriv_zero (a μ : ℝ) :
    logAffinityKernelDeriv a μ 0 = 0 := by
  simp only [logAffinityKernelDeriv, mul_zero, Real.exp_zero, mul_one]
  ring

/-- **`(18)`, `(19)`: the curvature at the critical source.** -/
theorem hasDerivAt_logAffinityKernelDeriv {a μ : ℝ} (ha : 1 + a ≠ 0) :
    HasDerivAt (logAffinityKernelDeriv a μ) (-(μ ^ 2 * a / (1 + a) ^ 2)) 0 := by
  have hE1 : HasDerivAt (fun x : ℝ => Real.exp (μ * x)) μ 0 := by
    have h := ((Real.hasDerivAt_exp (μ * 0)).comp 0 ((hasDerivAt_id (0:ℝ)).const_mul μ))
    simpa [Function.comp_def] using h
  have hE2 : HasDerivAt (fun x : ℝ => Real.exp (2 * μ * x)) (2 * μ) 0 := by
    have h := ((Real.hasDerivAt_exp (2 * μ * 0)).comp 0 ((hasDerivAt_id (0:ℝ)).const_mul (2 * μ)))
    simpa [Function.comp_def] using h
  have hD1 : HasDerivAt (fun x : ℝ => 1 + a * Real.exp (μ * x)) (a * μ) 0 := by
    have := (hE1.const_mul a).const_add 1
    simpa using this
  have hD2 : HasDerivAt (fun x : ℝ => 1 + a * Real.exp (2 * μ * x)) (a * (2 * μ)) 0 := by
    have := (hE2.const_mul a).const_add 1
    simpa using this
  have hn1 : HasDerivAt (fun x : ℝ => a * μ * Real.exp (μ * x)) (a * μ * μ) 0 := by
    have := hE1.const_mul (a * μ)
    simpa using this
  have hn2 : HasDerivAt (fun x : ℝ => a * μ * Real.exp (2 * μ * x)) (a * μ * (2 * μ)) 0 := by
    have := hE2.const_mul (a * μ)
    simpa using this
  have hval1 : (fun x : ℝ => 1 + a * Real.exp (μ * x)) 0 = 1 + a := by simp
  have hval2 : (fun x : ℝ => 1 + a * Real.exp (2 * μ * x)) 0 = 1 + a := by simp
  have hq1 := hn1.div hD1 (by simpa using ha)
  have hq2 := hn2.div hD2 (by simpa using ha)
  have hres := hq1.sub hq2
  have hfun : logAffinityKernelDeriv a μ
      = ((fun x : ℝ => a * μ * Real.exp (μ * x)) / fun x : ℝ => 1 + a * Real.exp (μ * x))
        - ((fun x : ℝ => a * μ * Real.exp (2 * μ * x))
            / fun x : ℝ => 1 + a * Real.exp (2 * μ * x)) := by
    funext x
    simp [logAffinityKernelDeriv]
  have hval : (a * μ * μ * (1 + a * Real.exp (μ * 0)) - a * μ * Real.exp (μ * 0) * (a * μ))
        / (1 + a * Real.exp (μ * 0)) ^ 2
      - (a * μ * (2 * μ) * (1 + a * Real.exp (2 * μ * 0))
          - a * μ * Real.exp (2 * μ * 0) * (a * (2 * μ))) / (1 + a * Real.exp (2 * μ * 0)) ^ 2
      = -(μ ^ 2 * a / (1 + a) ^ 2) := by
    simp only [mul_zero, Real.exp_zero, mul_one]
    field_simp
    ring
  rw [hfun, ← hval]
  exact hres

/-! ## The two prime instances -/

theorem radialNome_pow {c : ℝ} {n : ℕ} (hn : 2 ≤ n) (k : ℕ) :
    radialNome c n ^ k = Real.exp (-(k : ℝ) * (1 - 2 * c) * Real.log n) := by
  rw [radialNome_eq_exp hn, ← Real.exp_nat_mul]
  congr 1
  ring

theorem sqrt_radialNome_mul {c : ℝ} {n : ℕ} (hn : 2 ≤ n) :
    Real.sqrt (radialNome 0 n * radialNome c n) = Real.exp (-(1 - c) * Real.log n) := by
  rw [radialNome_eq_exp hn, radialNome_eq_exp hn, ← Real.exp_add, sqrt_exp]
  congr 1
  ring

/-- **`(19)`: the digit log-affinity is the universal kernel.** -/
theorem log_bitHellingerAffinity_radial {n : ℕ} (hn : 2 ≤ n) (j : ℕ) (c : ℝ) :
    Real.log (bitHellingerAffinity (radialNome 0 n) (radialNome c n) j)
      = logAffinityKernel (Real.exp (-((2 : ℝ) ^ j) * Real.log n))
        ((2 : ℝ) ^ j * Real.log n) c := by
  set r : ℝ := Real.exp (-((2 : ℝ) ^ j) * Real.log n) with hr
  set μ : ℝ := (2 : ℝ) ^ j * Real.log n with hμ
  have hnum : Real.sqrt (radialNome 0 n * radialNome c n) ^ 2 ^ j = r * Real.exp (μ * c) := by
    rw [sqrt_radialNome_mul hn, ← Real.exp_nat_mul, hr, hμ, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have h0 : radialNome 0 n ^ 2 ^ j = r := by
    rw [radialNome_pow hn, hr]
    congr 1
    push_cast
    ring
  have hc2 : radialNome c n ^ 2 ^ j = r * Real.exp (2 * μ * c) := by
    rw [radialNome_pow hn, hr, hμ, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hrpos : 0 < r := Real.exp_pos _
  have hp1 : 0 < 1 + r * Real.exp (μ * c) := by positivity
  have hp2 : 0 < 1 + r * Real.exp (2 * μ * c) := by positivity
  have hp0 : 0 < 1 + r := by positivity
  rw [bitHellingerAffinity, hnum, h0, hc2, logAffinityKernel]
  rw [Real.log_div (ne_of_gt hp1) (by positivity), Real.log_sqrt (by positivity),
    Real.log_mul (ne_of_gt hp0) (ne_of_gt hp2)]
  ring

/-- **`(18)`: the geometric log-affinity is the reflected universal kernel.** -/
theorem log_geometricHellingerAffinity_radial {n : ℕ} (hn : 2 ≤ n) {c : ℝ}
    (hc : |c| ≤ 1 / 8) :
    Real.log (geometricHellingerAffinity (radialNome 0 n) (radialNome c n))
      = -logAffinityKernel (-Real.exp (-Real.log n)) (Real.log n) c := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hq : radialNome 0 n = Real.exp (-Real.log n) := by
    rw [radialNome_eq_exp hn]
    congr 1
    ring
  have h0le : radialNome 0 n ≤ 3 / 4 := radialNome_le hn (by norm_num)
  have hcle : radialNome c n ≤ 3 / 4 := radialNome_le hn hc
  have h0pos : 0 < radialNome 0 n := radialNome_pos hn
  have hcpos : 0 < radialNome c n := radialNome_pos hn
  have hsq : Real.sqrt (radialNome 0 n * radialNome c n) = Real.exp (-(1 - c) * Real.log n) :=
    sqrt_radialNome_mul hn
  have hsqle : Real.sqrt (radialNome 0 n * radialNome c n) ≤ 3 / 4 := by
    have hmul : radialNome 0 n * radialNome c n ≤ (3 / 4 : ℝ) ^ 2 := by nlinarith
    nlinarith [Real.sq_sqrt (le_of_lt (mul_pos h0pos hcpos)), Real.sqrt_nonneg
      (radialNome 0 n * radialNome c n)]
  have hA : (0 : ℝ) < 1 - radialNome 0 n := by linarith
  have hB : (0 : ℝ) < 1 - radialNome c n := by linarith
  have hS : (0 : ℝ) < 1 - Real.sqrt (radialNome 0 n * radialNome c n) := by linarith
  rw [geometricHellingerAffinity, Real.log_div (by positivity) (ne_of_gt hS),
    Real.log_sqrt (by positivity), Real.log_mul (ne_of_gt hA) (ne_of_gt hB)]
  rw [logAffinityKernel]
  have e1 : 1 + -Real.exp (-Real.log n) * Real.exp (Real.log n * c)
      = 1 - Real.sqrt (radialNome 0 n * radialNome c n) := by
    rw [hsq, neg_mul, ← Real.exp_add, ← sub_eq_add_neg]
    congr 2
    ring
  have e2 : 1 + -Real.exp (-Real.log n) = 1 - radialNome 0 n := by rw [hq]; ring
  have e3 : 1 + -Real.exp (-Real.log n) * Real.exp (2 * Real.log n * c)
      = 1 - radialNome c n := by
    rw [radialNome_eq_exp hn, neg_mul, ← Real.exp_add, ← sub_eq_add_neg]
    congr 2
    ring
  rw [e1, e2, e3]
  ring

/-- **`(19)`: the digit curvature at the critical source is `4^j (log p)² q^{2^j}/(1+q^{2^j})²`.** -/
theorem hasDerivAt_bitCurvature (n : ℕ) (j : ℕ) :
    HasDerivAt (logAffinityKernelDeriv (Real.exp (-((2 : ℝ) ^ j) * Real.log n))
        ((2 : ℝ) ^ j * Real.log n))
      (-((4 : ℝ) ^ j * Real.log n ^ 2 * Real.exp (-((2 : ℝ) ^ j) * Real.log n)
        / (1 + Real.exp (-((2 : ℝ) ^ j) * Real.log n)) ^ 2)) 0 := by
  have hpos : (0 : ℝ) < Real.exp (-((2 : ℝ) ^ j) * Real.log n) := Real.exp_pos _
  have h := hasDerivAt_logAffinityKernelDeriv
    (a := Real.exp (-((2 : ℝ) ^ j) * Real.log n)) (μ := (2 : ℝ) ^ j * Real.log n)
    (by positivity)
  refine h.congr_deriv ?_
  congr 2
  rw [mul_pow, ← pow_mul]
  congr 1
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  congr 1
  ring

/-- **`(18)`: the geometric curvature at the critical source is `(log p)² q/(1-q)²`.** -/
theorem hasDerivAt_geometricCurvature {n : ℕ} (hn : 2 ≤ n) :
    HasDerivAt (logAffinityKernelDeriv (-Real.exp (-Real.log n)) (Real.log n))
      (Real.log n ^ 2 * Real.exp (-Real.log n) / (1 - Real.exp (-Real.log n)) ^ 2) 0 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlt : Real.exp (-Real.log n) < 1 := by
    refine Real.exp_lt_one_iff.mpr ?_
    have : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    linarith
  have h := hasDerivAt_logAffinityKernelDeriv
    (a := -Real.exp (-Real.log n)) (μ := Real.log n) (by linarith)
  refine h.congr_deriv ?_
  rw [show (1 : ℝ) + -Real.exp (-Real.log n) = 1 - Real.exp (-Real.log n) by ring]
  ring

end

end RHTower
