import GaloisForLFunctions.SelbergClass.DegreeOne.PeriodicCoefficients
import GaloisForLFunctions.SelbergClass.DegreeOne.CoefficientCharacter
import GaloisForLFunctions.SelbergClass.DegreeOne.DirichletElement
import GaloisForLFunctions.SelbergClass.FinitePrimeRigidity
import GaloisForLFunctions.SelbergClass.GammaIndependentEulerRigidity
import Mathlib.NumberTheory.LSeries.Deriv

/-!
# The classification of the Selberg class in degree one

**Theorem** (`degreeOne_classification`).  Let `F` be in the Selberg class with degree one.  Then the
conductor `q` of `F` is a positive integer, and there is a primitive character `χ` modulo `q` with

`F(s) = L(s + iθ, χ)`,   `θ` the internal shift of `F`,

and `θ = 0` if `q = 1`, so that `F = ζ` in that case.  Conversely every such function is in the
class (`exists_selberg_dirichlet`).

**Proof.**  The boundary law makes `a(n) n^{iθ}` periodic modulo `q ∈ ℕ`.  Multiplicativity gives a
character on the reduced residues, with primitive inducer `χ`, so that `F` and `L(s + iθ, χ)` have the
same Euler logarithm at every prime `p ∤ q`.  The condition `|b(n)| ≪ n^ϑ`, `ϑ < 1/2`, makes the
remaining finite discrepancy converge left of the critical line, which is excluded by Euler rigidity.
If `χ` is trivial, the same discrepancy shows that `F` has a pole at `1 − iθ`, so `θ = 0`.
-/

noncomputable section

set_option autoImplicit false

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace GaloisForLFunctions.SelbergClass.DegreeOne

/-! ### Geometric coefficients determine the Euler logarithm -/

theorem log_natCast_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    Complex.log ((p ^ j : ℕ) : ℂ) = (j : ℂ) * Complex.log (p : ℂ) := by
  rw [← Complex.natCast_log, ← Complex.natCast_log]
  push_cast
  rw [Real.log_pow]
  push_cast
  rfl

/-- If `a(p^k) = x^k` for all `k`, then the Euler logarithm at `p^k` is `x^k/k`. -/
theorem eulerLogCoeff_prime_pow_of_geometric (F : RHTower.SelbergClass) {p : ℕ} (hp : p.Prime)
    {x : ℂ} (hx : ∀ k, F.coeff (p ^ k) = x ^ k) (k : ℕ) :
    F.eulerLogCoeff (p ^ (k + 1)) = x ^ (k + 1) / ((k + 1 : ℕ) : ℂ) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    have hL : Complex.log (p : ℂ) ≠ 0 := by
      rw [← Complex.natCast_log]
      exact Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    have hsum := logMul_coeff_eq_sum_divisors F (p ^ (k + 1))
    rw [Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ, Finset.sum_range_succ'] at hsum
    have hlow : ∀ i ∈ Finset.range k, F.coeff (p ^ (k + 1) / p ^ (i + 1)) *
        LSeries.logMul F.eulerLogCoeff (p ^ (i + 1)) = Complex.log (p : ℂ) * x ^ (k + 1) := by
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      have hdiv : p ^ (k + 1) / p ^ (i + 1) = p ^ (k + 1 - (i + 1)) :=
        Nat.pow_div (by omega) hp.pos
      rw [hdiv, hx, LSeries.logMul, ih i hik, log_natCast_prime_pow hp]
      have hne : ((i + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero i
      have hpow : x ^ (k + 1 - (i + 1)) * x ^ (i + 1) = x ^ (k + 1) := by
        rw [← pow_add]
        congr 1
        omega
      field_simp
      linear_combination (Complex.log (p : ℂ)) * hpow
    rw [Finset.sum_congr rfl hlow, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have htop : p ^ (k + 1) / p ^ (k + 1) = 1 := Nat.div_self (pow_pos hp.pos _)
    have hzero : LSeries.logMul F.eulerLogCoeff (p ^ 0) = 0 := by
      simp [LSeries.logMul]
    rw [htop, F.coeff_one, hzero, mul_zero, add_zero, one_mul, LSeries.logMul, LSeries.logMul,
      hx, log_natCast_prime_pow hp] at hsum
    have hne : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    rw [eq_div_iff hne]
    have hcast : ((k + 1 : ℕ) : ℂ) = (k : ℂ) + 1 := by push_cast; rfl
    refine mul_left_cancel₀ hL ?_
    rw [hcast] at hsum ⊢
    linear_combination -hsum

/-! ### The prime powers of a twisted character -/

theorem natCast_pow_cpow {p : ℕ} (hp : p ≠ 0) (k : ℕ) (w : ℂ) :
    ((p ^ k : ℕ) : ℂ) ^ w = ((p : ℂ) ^ w) ^ k := by
  have h1 : ((p ^ k : ℕ) : ℂ) = (p : ℂ) ^ k := by push_cast; rfl
  rw [h1, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

theorem dirichletCoeff_prime_pow {N : ℕ} (χ : DirichletCharacter ℂ N) (θ : ℝ) {p : ℕ} (hp : p ≠ 0)
    (k : ℕ) : dirichletCoeff χ θ (p ^ k) = (χ p * (p : ℂ) ^ (-(I * (θ : ℂ)))) ^ k := by
  rw [dirichletCoeff_of_ne_zero χ θ (pow_ne_zero _ hp), natCast_pow_cpow hp, mul_pow]
  congr 1
  push_cast
  exact map_pow χ _ _

theorem dirichletLogCoeff_prime_pow {N : ℕ} (χ : DirichletCharacter ℂ N) (θ : ℝ) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    dirichletLogCoeff χ θ (p ^ (k + 1)) =
      (χ p * (p : ℂ) ^ (-(I * (θ : ℂ)))) ^ (k + 1) / ((k + 1 : ℕ) : ℂ) := by
  rw [dirichletLogCoeff_apply, dirichletCoeff_prime_pow χ θ hp.ne_zero,
    eulerLogDirichletCoeff_prime_pow_succ p k hp]
  push_cast
  ring

/-! ### The trivial character forces the internal shift to vanish -/

/-- If `F` agrees with `ζ(s + iθ)` at all but finitely many primes, then the discrepancy is holomorphic
past `Re s = 1/2`, so `F` inherits the pole of `ζ(s + iθ)` at `1 − iθ`.  Since `F` has its only pole at
`s = 1`, this forces `θ = 0`. -/
theorem shift_eq_zero_of_zeta_agreement (F : RHTower.SelbergClass) {q : ℕ} (hq : q ≠ 0) {θ : ℝ}
    (h : ∀ p : ℕ, p.Prime → ¬ p ∣ q → ∀ k, F.coeff (p ^ k) = ((p : ℂ) ^ (-(I * (θ : ℂ)))) ^ k) :
    θ = 0 := by
  classical
  obtain ⟨χ₁, hχ₁⟩ : ∃ χ₁ : DirichletCharacter ℂ 1, χ₁ = 1 := ⟨_, rfl⟩
  have hχp : ∀ p : ℕ, χ₁ (p : ZMod 1) = 1 := by
    intro p
    have : (p : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [this, map_one]
  let c := dirichletLogCoeff χ₁ θ
  let disc : ℕ → ℂ := fun n => F.eulerLogCoeff n - c n
  have hP : ∀ p ∈ q.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hagree : ∀ p : ℕ, p.Prime → p ∉ q.primeFactors → ∀ k : ℕ, 0 < k →
      F.eulerLogCoeff (p ^ k) = c (p ^ k) := by
    intro p hp hpq k hk
    have hnd : ¬ p ∣ q := fun hd => hpq (Nat.mem_primeFactors.mpr ⟨hp, hd, hq⟩)
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    rw [eulerLogCoeff_prime_pow_of_geometric F hp (h p hp hnd) j]
    simp only [c]
    rw [dirichletLogCoeff_prime_pow χ₁ θ hp j, hχp, one_mul]
  obtain ⟨CF, hCF, hF⟩ := F.eulerLogBound
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = max F.eulerTheta 0 := ⟨_, rfl⟩
  have hτlt : τ < 1 / 2 := by
    rw [hτ]
    exact max_lt F.eulerTheta_lt_half (by norm_num)
  obtain ⟨σ, hτσ, hσ⟩ := exists_between hτlt
  have hsumm : LSeriesSummable disc σ := by
    refine lSeriesSummable_of_finite_prime_support q.primeFactors hP (C := CF + 1) (θ := τ)
      ?_ ?_ hτσ
    · intro n hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have h1 : ‖c n‖ ≤ (n : ℝ) ^ τ := by
        refine (norm_dirichletLogCoeff_le χ₁ θ n).trans ?_
        refine Real.one_le_rpow hn1 ?_
        rw [hτ]
        exact le_max_right _ _
      have h2 : CF * (n : ℝ) ^ F.eulerTheta ≤ CF * (n : ℝ) ^ τ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1
          (by rw [hτ]; exact le_max_left _ _)) hCF.le
      calc ‖disc n‖ ≤ ‖F.eulerLogCoeff n‖ + ‖c n‖ := norm_sub_le _ _
        _ ≤ CF * (n : ℝ) ^ τ + (n : ℝ) ^ τ := add_le_add ((hF n hn).trans h2) h1
        _ = (CF + 1) * (n : ℝ) ^ τ := by ring
    · intro n hn
      have hex : ∃ p k : ℕ, p.Prime ∧ 0 < k ∧ n = p ^ k := by
        by_cases hfn : F.eulerLogCoeff n = 0
        · have hcn : c n ≠ 0 := fun h0 => hn (by simp only [disc, hfn, h0, sub_self])
          obtain ⟨p, k, hp, hk, rfl⟩ :=
            (isPrimePow_nat_iff n).mp (isPrimePow_of_dirichletLogCoeff_ne_zero χ₁ θ hcn)
          exact ⟨p, k, hp, hk, rfl⟩
        · exact F.eulerLogCoeff_primePower hfn
      obtain ⟨p, k, hp, hk, rfl⟩ := hex
      have hpP : p ∈ q.primeFactors := by
        by_contra hpP
        exact hn (sub_eq_zero.mpr (hagree p hp hpP k hk))
      exact ⟨p, hpP, k, rfl⟩
  -- the holomorphic discrepancy
  have habs : LSeries.abscissaOfAbsConv disc ≤ (σ : ℝ) := by
    simpa only [Complex.ofReal_re] using hsumm.abscissaOfAbsConv_le
  let U : Set ℂ := {s | σ < s.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUconv : Convex ℝ U := convex_halfSpace_re_gt σ
  have hDan : AnalyticOnNhd ℂ (fun s => cexp (LSeries disc s)) U := by
    intro s hs
    refine AnalyticAt.cexp (LSeries_analyticOnNhd disc s ?_)
    exact habs.trans_lt (by exact_mod_cast hs)
  have hZan : AnalyticOnNhd ℂ (fun s : ℂ => RHTower.zetaPoleUnit (s + I * (θ : ℂ))) U :=
    fun s _ => (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (RHTower.differentiable_zetaPoleUnit.comp (by fun_prop :
        Differentiable ℂ fun s : ℂ => s + I * (θ : ℂ)))) s (mem_univ _)
  have hRan : AnalyticOnNhd ℂ (fun s : ℂ => F.continuation.regularized s * (s + I * (θ : ℂ) - 1)) U :=
    fun s _ => (F.continuation.regularized.analytic s (mem_univ _)).mul (by fun_prop)
  have hLan : AnalyticOnNhd ℂ (fun s : ℂ => (s - 1) ^ F.continuation.poleOrder *
      (RHTower.zetaPoleUnit (s + I * (θ : ℂ)) * cexp (LSeries disc s))) U :=
    fun s hs => (by fun_prop : AnalyticAt ℂ (fun s : ℂ => (s - 1) ^ F.continuation.poleOrder) s).mul
      ((hZan s hs).mul (hDan s hs))
  -- identity on `Re s > 1`
  have hright : ∀ s : ℂ, 1 < s.re → F.continuation.regularized s * (s + I * (θ : ℂ) - 1) =
      (s - 1) ^ F.continuation.poleOrder *
        (RHTower.zetaPoleUnit (s + I * (θ : ℂ)) * cexp (LSeries disc s)) := by
    intro s hs
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1] at hs
      simp at hs
    have hsθ : s + I * (θ : ℂ) ≠ 1 := by
      intro h1
      have := congrArg Complex.re h1
      simp at this
      linarith
    have hpow : (s - 1) ^ F.continuation.poleOrder ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hs1)
    have hsplit : LSeries F.eulerLogCoeff s = LSeries c s + LSeries disc s := by
      have hb := F.eulerLogSummable s hs
      have hc : LSeriesSummable c s := lSeriesSummable_dirichletLogCoeff χ₁ θ hs
      have e : LSeries disc s = LSeries F.eulerLogCoeff s - LSeries c s := LSeries_sub hb hc
      rw [e]
      ring
    have hval : F.continuation.value s =
        DirichletCharacter.LFunction χ₁ (s + I * (θ : ℂ)) * cexp (LSeries disc s) := by
      rw [← F.eulerProduct s hs, hsplit, Complex.exp_add, exp_lSeries_dirichletLogCoeff χ₁ θ hs]
    have hreg : F.continuation.regularized s =
        (s - 1) ^ F.continuation.poleOrder * F.continuation.value s := by
      simp only [SelbergAnalyticContinuation.value]
      field_simp
    have hzeta : DirichletCharacter.LFunction χ₁ (s + I * (θ : ℂ)) = riemannZeta (s + I * (θ : ℂ)) := by
      rw [DirichletCharacter.LFunction_modOne_eq]
    rw [hreg, hval, hzeta, RHTower.zetaPoleUnit_of_ne hsθ]
    ring
  have htwo : (2 : ℂ) ∈ U := by
    change σ < (2 : ℂ).re
    simp only [Complex.re_ofNat]
    linarith
  have hev : (fun s : ℂ => F.continuation.regularized s * (s + I * (θ : ℂ) - 1)) =ᶠ[𝓝 (2 : ℂ)]
      fun s : ℂ => (s - 1) ^ F.continuation.poleOrder *
        (RHTower.zetaPoleUnit (s + I * (θ : ℂ)) * cexp (LSeries disc s)) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with s hs
    exact hright s hs
  have hEq := hRan.eqOn_of_preconnected_of_eventuallyEq hLan hUconv.isPreconnected htwo hev
  -- evaluate at the pole of the shifted zeta
  have hs₁ : (1 - I * (θ : ℂ)) ∈ U := by
    change σ < (1 - I * (θ : ℂ)).re
    simp
    linarith
  have hval := hEq hs₁
  simp only [sub_add_cancel, sub_self, mul_zero, RHTower.zetaPoleUnit_one, one_mul] at hval
  have hexp := Complex.exp_ne_zero (LSeries disc (1 - I * (θ : ℂ)))
  by_contra hθ
  have hne : (1 - I * (θ : ℂ) - 1) ≠ 0 := by
    have : (1 - I * (θ : ℂ) - 1) = -(I * (θ : ℂ)) := by ring
    rw [this]
    exact neg_ne_zero.mpr (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hθ))
  exact (mul_ne_zero (pow_ne_zero _ hne) hexp) hval.symm

end GaloisForLFunctions.SelbergClass.DegreeOne
