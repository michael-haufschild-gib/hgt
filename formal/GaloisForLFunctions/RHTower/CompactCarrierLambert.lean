import GaloisForLFunctions.RHTower.CompactCarrierFourierBorel
import GaloisForLFunctions.RHTower.LambertRayRecovery
import GaloisForLFunctions.RHTower.EulerUnitTangent

/-!
# Lambert transforms on compact analytic-functional carriers

This file connects the Banach-valued exponential test to the actual
degree-one Euler-unit tangent.  The geometric-derivative series is summed in
the continuous-function Banach algebra and only then passed through the
continuous functional, so no pointwise/uniform interchange is assumed.
-/

noncomputable section

namespace RHTower

open Complex Set

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- The Banach-algebra sum of the geometric derivative attached to a compact
exponential test. -/
def compactLambertKernel (s : C(K, ℂ)) (z : ℂ) : C(K, ℂ) :=
  let q := compactExponentialTest s z
  q * (Ring.inverse (1 - q)) ^ 2

/-- The scalar Lambert transform produced by a compactly carried functional. -/
def compactCarrierLambertTransform
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) (z : ℂ) : ℂ :=
  L (compactLambertKernel s z)

/-- A uniform positive lower bound for `Re (z s)` forces the compact
exponential test strictly inside the unit ball. -/
theorem norm_compactExponentialTest_lt_one_of_re_pos
    (s : C(K, ℂ)) (z : ℂ) (d : ℝ) (hd : 0 < d)
    (hre : ∀ k, d ≤ (z * s k).re) :
    ‖compactExponentialTest s z‖ < 1 := by
  have hnorm : ‖compactExponentialTest s z‖ ≤ Real.exp (-d) := by
    apply (ContinuousMap.norm_le (compactExponentialTest s z) (Real.exp_nonneg _)).2
    intro k
    rw [compactExponentialTest_apply, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hk := hre k
    simp only [neg_mul, Complex.neg_re]
    linarith
  exact hnorm.trans_lt (Real.exp_lt_one_iff.mpr (by linarith))

/-- The compact Lambert kernel is the norm-convergent sum
`Σ n q^n`, weighted by `n`. -/
theorem compactLambertKernel_hasSum
    (s : C(K, ℂ)) (z : ℂ)
    (hq : ‖compactExponentialTest s z‖ < 1) :
    HasSum (fun n : ℕ => n * (compactExponentialTest s z) ^ n)
      (compactLambertKernel s z) := by
  simpa [compactLambertKernel] using
    (hasSum_coe_mul_geometric_of_norm_lt_one'
      (R := C(K, ℂ)) hq)

/-- The compact Lambert kernel is analytic at every point where its
exponential test has norm strictly below one. -/
theorem compactLambertKernel_analyticAt
    (s : C(K, ℂ)) (z : ℂ)
    (hq : ‖compactExponentialTest s z‖ < 1) :
    AnalyticAt ℂ (compactLambertKernel s) z := by
  have hqAn : AnalyticAt ℂ (compactExponentialTest s) z :=
    compactExponentialTest_analyticOnNhd s z (Set.mem_univ z)
  have hsub : AnalyticAt ℂ (fun w => 1 - compactExponentialTest s w) z :=
    analyticAt_const.sub hqAn
  let u : C(K, ℂ)ˣ := (isUnit_one_sub_of_norm_lt_one hq).unit
  have hu : (u : C(K, ℂ)) = 1 - compactExponentialTest s z :=
    (isUnit_one_sub_of_norm_lt_one hq).unit_spec
  have hinv0 : AnalyticAt ℂ (Ring.inverse : C(K, ℂ) → C(K, ℂ))
      (1 - compactExponentialTest s z) := by
    convert analyticAt_inverse (𝕜 := ℂ) u using 1
    exact hu
  have hinv : AnalyticAt ℂ
      (fun w => Ring.inverse (1 - compactExponentialTest s w)) z := by
    simpa [Function.comp_def] using hinv0.comp hsub
  unfold compactLambertKernel
  exact hqAn.mul (hinv.pow 2)

/-- The scalar compact-carrier Lambert transform is analytic wherever the
compact exponential test is uniformly contractive. -/
theorem compactCarrierLambertTransform_analyticAt
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) (z : ℂ)
    (hq : ‖compactExponentialTest s z‖ < 1) :
    AnalyticAt ℂ (compactCarrierLambertTransform L s) z := by
  simpa [compactCarrierLambertTransform, Function.comp_def] using
    (L.analyticAt _).comp (compactLambertKernel_analyticAt s z hq)

/-- Powers of the compact exponential test multiply its scalar parameter. -/
theorem compactExponentialTest_pow
    (s : C(K, ℂ)) (z : ℂ) (n : ℕ) :
    (compactExponentialTest s z) ^ n =
      compactExponentialTest s ((n : ℂ) * z) := by
  ext k
  simp only [ContinuousMap.pow_apply, compactExponentialTest_apply]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Pointwise, the Banach-algebra Lambert kernel is the usual geometric
derivative. -/
theorem compactLambertKernel_apply
    (s : C(K, ℂ)) (z : ℂ) (k : K)
    (hq : ‖compactExponentialTest s z‖ < 1) :
    compactLambertKernel s z k =
      Complex.exp (-z * s k) / (1 - Complex.exp (-z * s k)) ^ 2 := by
  have hban := (ContinuousMap.evalCLM ℂ k).hasSum
    (compactLambertKernel_hasSum s z hq)
  have hscalar := hasSum_coe_mul_geometric_of_norm_lt_one
    (show ‖Complex.exp (-z * s k)‖ < 1 by
      rw [← compactExponentialTest_apply s z k]
      exact (ContinuousMap.norm_coe_le_norm _ _).trans_lt hq)
  apply HasSum.unique hban
  convert hscalar using 1
  ext n
  change ((n : C(K, ℂ)) * (compactExponentialTest s z) ^ n) k =
    (n : ℂ) * Complex.exp (-z * s k) ^ n
  simp [compactExponentialTest_apply]

/-- Applying a compactly carried functional to the Lambert kernel gives the
positive Lambert derivative of its Fourier--Borel transform. -/
theorem positiveLambertDerivative_compactFourierBorel
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) (z : ℂ)
    (hq : ‖compactExponentialTest s z‖ < 1) :
    positiveLambertDerivative (compactFourierBorel L s) z =
      L (compactLambertKernel s z) := by
  have hsum := compactLambertKernel_hasSum s z hq
  have hmapped := L.hasSum hsum
  have hsummable := hsum.summable
  rw [← hmapped.tsum_eq]
  unfold positiveLambertDerivative compactFourierBorel
  let g : ℕ → ℂ := fun n => L (n * (compactExponentialTest s z) ^ n)
  have hg : Summable g := hmapped.summable
  have htail : (∑' n : ℕ, g (n + 1)) = ∑' n : ℕ, g n := by
    have hsplit := hg.sum_add_tsum_nat_add 1
    simpa [g] using hsplit
  calc
    (∑' m : ℕ+, (m : ℂ) * L (compactExponentialTest s ((m : ℂ) * z))) =
        ∑' n : ℕ, ((Nat.succPNat n : ℕ) : ℂ) *
          L (compactExponentialTest s (((Nat.succPNat n : ℕ) : ℂ) * z)) := by
            symm
            exact Equiv.tsum_eq Equiv.pnatEquivNat.symm
              (fun m : ℕ+ => (m : ℂ) *
                L (compactExponentialTest s ((m : ℂ) * z)))
    _ = ∑' n : ℕ, g (n + 1) := by
      apply tsum_congr
      intro n
      rw [Nat.succPNat_coe]
      dsimp [g]
      rw [← compactExponentialTest_pow]
      let q : C(K, ℂ) := (compactExponentialTest s z) ^ (n + 1)
      have hmap : ((n + 1 : ℕ) : ℂ) * L q = L ((n + 1 : C(K, ℂ)) * q) := by
        calc
        ((n + 1 : ℕ) : ℂ) * L q = L (((n + 1 : ℕ) : ℂ) • q) := by
          simpa [smul_eq_mul] using (L.map_smul (((n + 1 : ℕ) : ℂ)) q).symm
        _ = L ((n + 1 : C(K, ℂ)) * q) := by
          congr 1
          ext k
          simp
      simpa [q] using hmap
    _ = ∑' n : ℕ, g n := htail

/-- At a prime-log argument the compact Lambert kernel is exactly the actual
Euler-unit tangent divided by `log p`. -/
theorem compactLambertKernel_primeLog_apply
    (s : C(K, ℂ)) {p : ℕ} (hp : 2 ≤ p) (k : K)
    (hs : 0 < (s k).re)
    (hq : ‖compactExponentialTest s (Real.log p)‖ < 1) :
    compactLambertKernel s (Real.log p) k =
      primeEulerUnitTangent p (s k) / (Real.log p : ℂ) := by
  rw [compactLambertKernel_apply s _ k hq]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hexp : Complex.exp (-(Real.log p : ℂ) * s k) = (p : ℂ) ^ (-(s k)) := by
    rw [Complex.cpow_def_of_ne_zero hp0]
    have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) :=
      (Complex.ofReal_log (show (0 : ℝ) ≤ p by positivity)).symm
    rw [hlog]
    congr 1
    ring
  rw [hexp]
  unfold primeEulerUnitTangent
  have hlog : (Real.log p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_ne_zero_of_pos_of_ne_one (by positivity : (0 : ℝ) < p)
      (by exact_mod_cast (show p ≠ 1 by omega)))
  field_simp [hlog]

/-- The actual prime Euler-unit tangent as a continuous function on a compact
carrier. -/
def compactPrimeEulerUnitTangent (s : C(K, ℂ)) (p : ℕ) : C(K, ℂ) :=
  (Real.log p : ℂ) • compactLambertKernel s (Real.log p)

@[simp]
theorem compactPrimeEulerUnitTangent_apply
    (s : C(K, ℂ)) {p : ℕ} (hp : 2 ≤ p) (k : K)
    (hs : 0 < (s k).re)
    (hq : ‖compactExponentialTest s (Real.log p)‖ < 1) :
    compactPrimeEulerUnitTangent s p k = primeEulerUnitTangent p (s k) := by
  rw [compactPrimeEulerUnitTangent, ContinuousMap.smul_apply,
    compactLambertKernel_primeLog_apply s hp k hs hq]
  have hlog : (Real.log p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_ne_zero_of_pos_of_ne_one (by positivity : (0 : ℝ) < p)
      (by exact_mod_cast (show p ≠ 1 by omega)))
  change (Real.log p : ℂ) *
      (primeEulerUnitTangent p (s k) / (Real.log p : ℂ)) = _
  field_simp

/-- Annihilating the actual compact prime tangent makes the corresponding
prime-log value of the Fourier--Borel Lambert transform vanish. -/
theorem positiveLambertDerivative_primeLog_eq_zero_of_annihilates
    (L : C(K, ℂ) →L[ℂ] ℂ) (s : C(K, ℂ)) {p : ℕ} (hp : 2 ≤ p)
    (hq : ‖compactExponentialTest s (Real.log p)‖ < 1)
    (hann : L (compactPrimeEulerUnitTangent s p) = 0) :
    positiveLambertDerivative (compactFourierBorel L s) (Real.log p) = 0 := by
  rw [positiveLambertDerivative_compactFourierBorel L s _ hq]
  have hlog : (Real.log p : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_ne_zero_of_pos_of_ne_one (by positivity : (0 : ℝ) < p)
      (by exact_mod_cast (show p ≠ 1 by omega)))
  have hscaled : (Real.log p : ℂ) * L (compactLambertKernel s (Real.log p)) = 0 := by
    simpa [compactPrimeEulerUnitTangent] using hann
  exact (mul_eq_zero.mp hscaled).resolve_left hlog

end RHTower
