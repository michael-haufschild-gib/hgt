import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheLedgerIsBlindToTheLiouvilleTwin
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMultiplicityEstimateOnTheGaugeTorus
import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.WhereTheFactorOfTwoGoes
import GaloisForLFunctions.RHTower.DirichletSummatorySwap
import GaloisForLFunctions.RHTower.PrimeShiftResidueClosability
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# The ledger ladder sees a zero

The linear ledger `Σ_d Λ(d) g(⌊n/d⌋)` has generating function `(−ζ′/ζ) D_c ζ = −ζ′ D_c`, which is regular at
every zero of `ζ`: it is blind. The **ledger of degree `j`** uses the convolution power `Λ^{∗j}`. Its
generating function is `(−ζ′/ζ)^j D_c ζ`.

* **The order law.** At a zero of order `n` this function has a pole of exact order `j − n` when `j > n`, with
  leading coefficient `(−n)^j a D_c(ρ)`, and it is regular when `j ≤ n`. So the degree one ledger is blind to
  every zero, the quadratic ledger of Selberg sees exactly the simple ones, and every zero is seen at degree
  `n + 1`, for every stencil with `D_c(ρ) ≠ 0`.
* **The order law is not arithmetic.** It holds for every analytic function. It says that a nonlinear ledger
  reads a zero, not that a zero is forbidden: an off-line zero of order one contributes one mode to the
  quadratic ledger and is consistent with every meromorphic world.
* **The twin.** `Λ` and `−λΛ` give linear ledgers within `2 w ψ(√n)`. Their quadratic ledgers differ by
  `Σ_d (V ∗ W)(d) g(⌊n/d⌋)`, with `W = Λ + λΛ ≥ 0` on even prime powers and `V = Λ − λΛ ≥ 0` on odd ones, and
  this is at least `4 m log 2 Σ log p` over primes with `4p ≤ n < 4pB`. So the quadratic ledger separates
  the twin at the size of the main term. It does so through the prime squares, which are known, so this
  separation carries no information about the primes themselves.
-/

open Finset Filter Topology
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

local notation "vM" => ArithmeticFunction.vonMangoldt

/-- **The order law: a pole above the order.** If `f = (z − ρ)ⁿ g` near `ρ` and `j > n`, then
`(f′/f)^j f` has a pole of order `j − n` with leading coefficient `n^j g(ρ)`. -/
theorem tendsto_ladder_of_lt {f g : ℂ → ℂ} {ρ : ℂ} {n j : ℕ} (hg : AnalyticAt ℂ g ρ) (hg0 : g ρ ≠ 0)
    (hfac : f =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ n • g z) (hnj : n < j) :
    Tendsto (fun s => (s - ρ) ^ (j - n) * ((logDeriv f s) ^ j * f s)) (𝓝[≠] ρ)
      (𝓝 ((n : ℂ) ^ j * g ρ)) := by
  have hl := RHTower.logDeriv_residue_of_factorization hg hg0 hfac
  have hmain := (hl.pow j).mul (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  refine hmain.congr' ?_
  filter_upwards [nhdsWithin_le_nhds hfac] with s hs
  rw [hs, smul_eq_mul, mul_pow]
  have hsplit : (s - ρ) ^ j = (s - ρ) ^ (j - n) * (s - ρ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hnj.le]
  rw [hsplit]
  ring

/-- **The order law: regular up to the order.** If `f = (z − ρ)ⁿ g` near `ρ` and `j ≤ n`, then `(f′/f)^j f`
is bounded near `ρ`, with limit `n^j 0^{n−j} g(ρ)`. -/
theorem tendsto_ladder_of_le {f g : ℂ → ℂ} {ρ : ℂ} {n j : ℕ} (hg : AnalyticAt ℂ g ρ) (hg0 : g ρ ≠ 0)
    (hfac : f =ᶠ[𝓝 ρ] fun z => (z - ρ) ^ n • g z) (hjn : j ≤ n) :
    Tendsto (fun s => (logDeriv f s) ^ j * f s) (𝓝[≠] ρ)
      (𝓝 ((n : ℂ) ^ j * 0 ^ (n - j) * g ρ)) := by
  have hl := RHTower.logDeriv_residue_of_factorization hg hg0 hfac
  have hzero : Tendsto (fun s : ℂ => (s - ρ) ^ (n - j)) (𝓝[≠] ρ) (𝓝 (0 ^ (n - j))) := by
    have ha : Tendsto (fun s : ℂ => s - ρ) (𝓝[≠] ρ) (𝓝 0) :=
      ((continuous_id.sub continuous_const).tendsto' ρ 0 (by simp)).mono_left nhdsWithin_le_nhds
    exact ha.pow _
  have hmain := ((hl.pow j).mul hzero).mul (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  refine hmain.congr' ?_
  filter_upwards [nhdsWithin_le_nhds hfac] with s hs
  rw [hs, smul_eq_mul, mul_pow]
  have hsplit : (s - ρ) ^ n = (s - ρ) ^ j * (s - ρ) ^ (n - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hjn]
  rw [hsplit]
  ring

/-- **The ladder at a zero of `ζ`.** At a zero `ρ ≠ 1` of order `n ≥ 1`, for every stencil,
`(−ζ′/ζ)^j D_c ζ` has a pole of order `j − n` with leading coefficient `(−n)^j a D_c(ρ)` for `j > n`, and it is
regular for `j ≤ n`. -/
theorem exists_ladder_at_zero {ρ : ℂ} (hρ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ a : ℂ, a ≠ 0 ∧ ∀ c : ℕ →₀ ℤ, c 0 = 0 → ∀ j : ℕ,
      (n < j → Tendsto (fun s => (s - ρ) ^ (j - n) *
          ((-deriv riemannZeta s / riemannZeta s) ^ j * (dirichletPoly c s * riemannZeta s)))
        (𝓝[≠] ρ) (𝓝 ((-(n : ℂ)) ^ j * a * dirichletPoly c ρ))) ∧
      (j ≤ n → Tendsto (fun s =>
          (-deriv riemannZeta s / riemannZeta s) ^ j * (dirichletPoly c s * riemannZeta s))
        (𝓝[≠] ρ) (𝓝 ((-(n : ℂ)) ^ j * 0 ^ (n - j) * a * dirichletPoly c ρ))) := by
  have hana : AnalyticAt ℂ riemannZeta ρ :=
    DifferentiableOn.analyticAt (s := {1}ᶜ)
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
      (isOpen_compl_singleton.mem_nhds hρ1)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (RHTower.analyticOrderAt_riemannZeta_ne_top hρ1)
  obtain ⟨g, hg, hg0, hfac⟩ := hana.analyticOrderAt_eq_natCast.mp hn.symm
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    subst hn0
    have := hfac.self_of_nhds
    simp only [pow_zero, one_smul, hρ] at this
    exact hg0 this.symm
  refine ⟨n, hn1, g ρ, hg0, fun c hc0 j => ?_⟩
  have hD : Tendsto (dirichletPoly c) (𝓝[≠] ρ) (𝓝 (dirichletPoly c ρ)) := by
    have hdiff : Differentiable ℂ (dirichletPoly c) := by
      rw [← gaugeTwist_one, gaugeTwist_eq_logMoment]
      exact differentiable_logMoment hc0 _ 0
    exact (hdiff ρ).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hrew : ∀ s, (-deriv riemannZeta s / riemannZeta s) ^ j =
      (-1) ^ j * (logDeriv riemannZeta s) ^ j := by
    intro s
    rw [neg_div, neg_pow, logDeriv_apply]
  constructor
  · intro hnj
    have h := ((tendsto_ladder_of_lt hg hg0 hfac hnj).const_mul ((-1 : ℂ) ^ j)).mul hD
    have hval : (-1 : ℂ) ^ j * ((n : ℂ) ^ j * g ρ) * dirichletPoly c ρ =
        (-(n : ℂ)) ^ j * g ρ * dirichletPoly c ρ := by
      rw [neg_pow (n : ℂ)]
      ring
    rw [hval] at h
    refine h.congr fun s => ?_
    rw [hrew]
    ring
  · intro hjn
    have h := ((tendsto_ladder_of_le hg hg0 hfac hjn).const_mul ((-1 : ℂ) ^ j)).mul hD
    have hval : (-1 : ℂ) ^ j * ((n : ℂ) ^ j * 0 ^ (n - j) * g ρ) * dirichletPoly c ρ =
        (-(n : ℂ)) ^ j * 0 ^ (n - j) * g ρ * dirichletPoly c ρ := by
      rw [neg_pow (n : ℂ)]
      ring
    rw [hval] at h
    refine h.congr fun s => ?_
    rw [hrew]
    ring

/-- The increment of a stencil as an arithmetic function. -/
def incrementFn (c : ℕ →₀ ℤ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (increment c n : ℝ), by simp⟩

theorem sum_Icc_incrementFn (c : ℕ →₀ ℤ) (x : ℕ) :
    ∑ n ∈ Icc 1 x, incrementFn c n = (stepWeight c x : ℝ) := by
  rw [← sum_Icc_increment, Int.cast_sum]
  refine sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  simp [incrementFn, hn0]

/-- **The ledger is a partial sum.** `Σ_{n ≤ N} (a ∗ h)(n) = Σ_{d ≤ N} a(d) g(⌊N/d⌋)`. -/
theorem sum_Icc_mul_incrementFn (a : ArithmeticFunction ℝ) (c : ℕ →₀ ℤ) (N : ℕ) :
    ∑ n ∈ Icc 1 N, (a * incrementFn c) n = ledger c a N := by
  have hset : Ioc 0 N = Icc 1 N := by
    ext x
    simp only [mem_Ioc, mem_Icc]
    omega
  rw [RHTower.sum_Icc_mul_apply, ledger, hset]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_Icc_incrementFn]

private def toC (F : ArithmeticFunction ℝ) : ArithmeticFunction ℂ := ⟨fun n => (F n : ℂ), by simp⟩

private lemma toC_mul (F G : ArithmeticFunction ℝ) : toC (F * G) = toC F * toC G := by
  ext n
  simp [toC, ArithmeticFunction.mul_apply]

private lemma lseries_mul_real {F G : ArithmeticFunction ℝ} {s : ℂ}
    (hF : LSeriesSummable (fun n => (F n : ℂ)) s) (hG : LSeriesSummable (fun n => (G n : ℂ)) s) :
    LSeriesSummable (fun n => ((F * G) n : ℂ)) s ∧
      LSeries (fun n => ((F * G) n : ℂ)) s =
        LSeries (fun n => (F n : ℂ)) s * LSeries (fun n => (G n : ℂ)) s := by
  have hcast : (fun n => ((F * G) n : ℂ)) = fun n => (toC F * toC G) n := by
    funext n
    rw [← toC_mul]
    rfl
  rw [hcast]
  exact ⟨ArithmeticFunction.LSeriesSummable_mul (f := toC F) (g := toC G) hF hG,
    ArithmeticFunction.LSeries_mul' (f := toC F) (g := toC G) hF hG⟩

private def stencilFn (c : ℕ →₀ ℤ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else (c n : ℂ), by simp⟩

private lemma stencilFn_summable (c : ℕ →₀ ℤ) (s : ℂ) : LSeriesSummable (fun n => stencilFn c n) s := by
  refine summable_of_ne_finset_zero (s := c.support) fun n hn => ?_
  have h0 : c n = 0 := Finsupp.notMem_support_iff.mp hn
  rw [LSeries.term_def]
  simp [stencilFn, h0]

private lemma stencilFn_lseries {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) (s : ℂ) :
    LSeries (fun n => stencilFn c n) s = dirichletPoly c s := by
  rw [LSeries, tsum_eq_sum (s := c.support) (fun n hn => by
    have h0 : c n = 0 := Finsupp.notMem_support_iff.mp hn
    rw [LSeries.term_def]
    simp [stencilFn, h0]), dirichletPoly]
  refine sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hc0
  rw [LSeries.term_of_ne_zero hk0, Complex.cpow_neg, Complex.ofReal_natCast, div_eq_mul_inv]
  simp [stencilFn, hk0]

private lemma incrementFn_eq (c : ℕ →₀ ℤ) :
    (fun n => (incrementFn c n : ℂ)) =
      fun n => (stencilFn c * (ArithmeticFunction.zeta : ArithmeticFunction ℂ)) n := by
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hpos : 0 < n := Nat.pos_of_ne_zero hn
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  have hinc := increment_eq_sum_divisors (c := c) hpos
  have hval : incrementFn c n = (increment c n : ℝ) := by simp [incrementFn, hn]
  rw [hval, hinc]
  push_cast
  refine sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  simp [stencilFn, hd0]

/-- **The generating function of the increment.** On `Re s > 1` the increment has Dirichlet series
`D_c ζ`. -/
theorem lseries_incrementFn {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (incrementFn c n : ℂ)) s ∧
      LSeries (fun n => (incrementFn c n : ℂ)) s = dirichletPoly c s * riemannZeta s := by
  rw [incrementFn_eq]
  have hζ : LSeriesSummable
      (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s :=
    (ArithmeticFunction.LSeriesSummable_zeta_iff (s := s)).mpr hs
  have hζv : LSeries (fun n => (ArithmeticFunction.zeta : ArithmeticFunction ℂ) n) s =
      riemannZeta s := ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs
  refine ⟨ArithmeticFunction.LSeriesSummable_mul (f := stencilFn c) (stencilFn_summable c s) hζ, ?_⟩
  rw [ArithmeticFunction.LSeries_mul' (f := stencilFn c) (stencilFn_summable c s) hζ,
    stencilFn_lseries hc0, hζv]

/-- **The generating function of the ledger of degree `j`.** On `Re s > 1` the increments of
`Σ_d Λ^{∗j}(d) g(⌊n/d⌋)` have Dirichlet series `(−ζ′/ζ)^j D_c ζ`. -/
theorem lseries_ladder {c : ℕ →₀ ℤ} (hc0 : c 0 = 0) {s : ℂ} (hs : 1 < s.re) (j : ℕ) :
    LSeriesSummable (fun n => (((vM ^ j) * incrementFn c) n : ℂ)) s ∧
      LSeries (fun n => (((vM ^ j) * incrementFn c) n : ℂ)) s =
        (-deriv riemannZeta s / riemannZeta s) ^ j * (dirichletPoly c s * riemannZeta s) := by
  induction j with
  | zero =>
    simp only [pow_zero, one_mul]
    exact lseries_incrementFn hc0 hs
  | succ j ih =>
    have hΛ : LSeriesSummable (fun n => ((vM n : ℝ) : ℂ)) s :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt hs
    have hΛv : LSeries (fun n => ((vM n : ℝ) : ℂ)) s = -deriv riemannZeta s / riemannZeta s :=
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
    have hassoc : vM ^ (j + 1) * incrementFn c = vM * ((vM ^ j) * incrementFn c) := by
      rw [pow_succ', mul_assoc]
    rw [hassoc]
    obtain ⟨h1, h2⟩ := lseries_mul_real hΛ ih.1
    refine ⟨h1, ?_⟩
    rw [h2, hΛv, ih.2, pow_succ']
    ring

/-- The Liouville twin `−λΛ` as an arithmetic function. -/
def twinFn : ArithmeticFunction ℝ :=
  ⟨fun n => -ArithmeticOfSquareRootPrecision.liouvilleWeight n, by
    simp [ArithmeticOfSquareRootPrecision.liouvilleWeight]⟩

private lemma twin_apply (n : ℕ) :
    twinFn n = -ArithmeticOfSquareRootPrecision.liouvilleWeight n := rfl

private lemma af_sub_apply (a b : ArithmeticFunction ℝ) (n : ℕ) : (a - b) n = a n - b n := by
  rw [sub_eq_add_neg, ArithmeticFunction.add_apply, sub_eq_add_neg]
  rfl

private lemma sub_nonneg_twin (n : ℕ) : 0 ≤ (vM - twinFn) n := by
  have h := (ArithmeticOfSquareRootPrecision.liouvilleWeight_add_vonMangoldt_le n).1
  rw [af_sub_apply, twin_apply]
  linarith

private lemma add_nonneg_twin (n : ℕ) : 0 ≤ (vM + twinFn) n := by
  have hΛ : 0 ≤ vM n := ArithmeticFunction.vonMangoldt_nonneg
  rw [ArithmeticFunction.add_apply, twin_apply, ArithmeticOfSquareRootPrecision.liouvilleWeight]
  rcases neg_one_pow_eq_or ℝ (ArithmeticFunction.cardFactors n) with h | h <;> rw [h] <;> linarith

private lemma add_twin_prime {p : ℕ} (hp : p.Prime) : (vM + twinFn) p = 2 * Real.log p := by
  rw [ArithmeticFunction.add_apply, twin_apply, ArithmeticOfSquareRootPrecision.liouvilleWeight,
    ArithmeticFunction.cardFactors_apply_prime hp, ArithmeticFunction.vonMangoldt_apply_prime hp]
  ring

private lemma sub_twin_four : (vM - twinFn) 4 = 2 * Real.log 2 := by
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  have hΛ : vM 4 = Real.log 2 := by
    rw [h4, ArithmeticFunction.vonMangoldt_apply_pow (by norm_num),
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  have hΩ : ArithmeticFunction.cardFactors 4 = 2 := by
    rw [h4, ArithmeticFunction.cardFactors_apply_prime_pow Nat.prime_two]
  rw [af_sub_apply, twin_apply, ArithmeticOfSquareRootPrecision.liouvilleWeight, hΩ, hΛ]
  ring

/-- **The quadratic ledger separates the twin.** Over the primes with `4p ≤ N < 4pB`, the quadratic ledgers
of `Λ` and of `−λΛ` differ by at least `4 m log 2 Σ log p`. The linear ledgers differ by at most
`2 w ψ(√N)`. -/
theorem IsProducer.ledger_twin_gap {c : ℕ →₀ ℤ} {m B : ℕ} (hP : IsProducer c m B) (N : ℕ) :
    4 * Real.log 2 * (m : ℝ) *
        ∑ p ∈ (Ioc 0 N).filter (fun p => p.Prime ∧ 4 * p ≤ N ∧ N < 4 * p * B), Real.log p ≤
      ledger c ⇑(vM * vM) N - ledger c ⇑(twinFn * twinFn) N := by
  classical
  set S := (Ioc 0 N).filter (fun p => p.Prime ∧ 4 * p ≤ N ∧ N < 4 * p * B) with hS
  have hdiff : ledger c ⇑(vM * vM) N - ledger c ⇑(twinFn * twinFn) N =
      ∑ d ∈ Ioc 0 N, ((vM + twinFn) * (vM - twinFn)) d * (stepWeight c (N / d) : ℝ) := by
    rw [ledger, ledger, ← sum_sub_distrib]
    refine sum_congr rfl fun d _ => ?_
    rw [← sub_mul, ← af_sub_apply, ← mul_self_sub_mul_self]
  rw [hdiff]
  have hg0 : ∀ r, (0 : ℝ) ≤ (stepWeight c r : ℝ) := fun r => by exact_mod_cast hP.nonneg r
  have hconv0 : ∀ d, 0 ≤ ((vM + twinFn) * (vM - twinFn)) d := by
    intro d
    rw [ArithmeticFunction.mul_apply]
    exact sum_nonneg fun x _ => mul_nonneg (add_nonneg_twin _) (sub_nonneg_twin _)
  have hinj : Set.InjOn (fun p : ℕ => 4 * p) S := fun a _ b _ h => by
    simpa using h
  have hsub : S.image (fun p => 4 * p) ⊆ Ioc 0 N := by
    intro d hd
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hd
    have hp' := mem_filter.mp hp
    exact mem_Ioc.mpr ⟨by have := hp'.2.1.pos; omega, hp'.2.2.1⟩
  have hsum := sum_le_sum_of_subset_of_nonneg hsub
    (f := fun d => ((vM + twinFn) * (vM - twinFn)) d * (stepWeight c (N / d) : ℝ))
    (fun d _ _ => mul_nonneg (hconv0 d) (hg0 _))
  rw [sum_image hinj] at hsum
  refine le_trans ?_ hsum
  rw [mul_sum]
  refine sum_le_sum fun p hp => ?_
  obtain ⟨_, hpr, hle, hlt⟩ := mem_filter.mp hp
  have hmem : (p, 4) ∈ (4 * p).divisorsAntidiagonal := by
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨by ring, by have := hpr.pos; omega⟩
  have hconv : (2 * Real.log p) * (2 * Real.log 2) ≤ ((vM + twinFn) * (vM - twinFn)) (4 * p) := by
    rw [ArithmeticFunction.mul_apply, ← add_twin_prime hpr, ← sub_twin_four]
    exact single_le_sum (f := fun x : ℕ × ℕ => (vM + twinFn) x.1 * (vM - twinFn) x.2)
      (fun x _ => mul_nonneg (add_nonneg_twin _) (sub_nonneg_twin _)) hmem
  have hwin : (m : ℝ) ≤ (stepWeight c (N / (4 * p)) : ℝ) := by
    have hr : N / (4 * p) ∈ Ico 1 B := by
      refine mem_Ico.mpr ⟨Nat.div_pos hle (by have := hpr.pos; omega), ?_⟩
      exact Nat.div_lt_of_lt_mul hlt
    have := hP.window _ hr
    exact_mod_cast this
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  calc 4 * Real.log 2 * (m : ℝ) * Real.log p
      = (2 * Real.log p) * (2 * Real.log 2) * (m : ℝ) := by ring
    _ ≤ ((vM + twinFn) * (vM - twinFn)) (4 * p) * (stepWeight c (N / (4 * p)) : ℝ) :=
        mul_le_mul hconv hwin hm (hconv0 _)

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
