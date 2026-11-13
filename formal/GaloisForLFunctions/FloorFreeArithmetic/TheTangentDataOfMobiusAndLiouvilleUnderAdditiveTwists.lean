import GaloisForLFunctions.FloorFreeArithmetic.TheTangentDataOfMobiusAndLiouvilleInWorldOne
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheFourierCoefficientsOfTheTorsionMeasure
import GaloisForLFunctions.RHTower.HalfWeightCoefficientContinuation
import GaloisForLFunctions.RHTower.LiouvilleSummatoryPolyaBoundary

/-!
# The tangent data of Möbius and Liouville under additive twists

The additive twists of `μ` at the primitive `q`-th roots of unity sum to the Ramanujan twist
`μ(n) c_q(n)`, `c_q(n) = Σ_{ζ primitive} ζ^n = Σ_{de = q, e | n} μ(d) e`
(`ArithmeticEffectivityTheory.ramanujanSum`).  It keeps the exact structure of `1/ζ`:

* **Dirichlet series** (`LSeries_moebius_mul_ramanujanSum`, `LSeries_liouville_mul_ramanujanSum`).
  On `Re s > 1`,
  `Σ μ(n) c_q(n) n^{−s} = R_q(s)/ζ(s)`, `R_q(s) = Σ_{de=q} μ(d) e μ(e) e^{−s} Π_{p|e} (1 − p^{−s})⁻¹`,
  `Σ λ(n) c_q(n) n^{−s} = R^λ_q(s) ζ(2s)/ζ(s)`, `R^λ_q(s) = Σ_{de=q} μ(d) e λ(e) e^{−s}`.
  The multiples of `e` carry `μ(e) e^{−s} Σ_{(m,e)=1} μ(m) m^{−s} = μ(e) e^{−s}/L(s, 1_e)`, and
  `L(s, 1_e) = ζ(s) Π_{p|e}(1 − p^{−s})`; for `λ` complete multiplicativity gives `λ(e) e^{−s}`.
* **Window sums** (`signal_eq_tsum_of_LSeries`, `signal_ramanujanKernel_eq_tsum`,
  `signal_liouvilleRamanujanKernel_eq_tsum`).  With `A_q = (s − 1) R_q` and
  `A^λ_q = (s − 1) ζ(2s) R^λ_q`, the signals of the world kernels
  `e^{(s−c)²} A(s)/((s − 1)ζ(s))` are the Gaussian window sums of `μ c_q` and `λ c_q`.
* **The tangent data** (`tangentDatum_ramanujanTwist`, `tangentDatum_liouvilleRamanujanTwist`).  In
  world I (`Θ∞ < Θ`) the normalized twisted signals are asymptotic to the sums of their residues at
  the top zeros of `ζ`.  The residue numerators are those of `μ` multiplied by `R_q`, resp. by
  `R^λ_q(s) ζ(2s)` (`ramanujanNumerator_div_eq`, `liouvilleRamanujanNumerator_div_eq`): the top
  layer of `ζ` reappears in every Ramanujan twist with amplitude `R_q(ρ)`, with the same support
  and degrees wherever `R_q(ρ) ≠ 0`.
-/

noncomputable section

open Complex MeasureTheory Filter Topology Set
open scoped ArithmeticFunction.Moebius LSeries.notation

namespace GaloisForLFunctions.FloorFreeArithmetic

open HTGeometry FamilyContinuationTheory _root_.RHTower
open GaloisForLFunctions.ArithmeticEffectivityTheory (ramanujanSum ramanujanSum_eq_sum_moebius)

/-! ## The Dirichlet series of a Ramanujan twist -/

/-- `Π_{p | e} (1 − p^{−s})⁻¹`. -/
def eulerInv (e : ℕ) (s : ℂ) : ℂ := (∏ p ∈ e.primeFactors, (1 - (p : ℂ) ^ (-s)))⁻¹

/-- The Ramanujan factor `R_q(s) = Σ_{de=q} μ(d) e μ(e) e^{−s} Π_{p|e} (1 − p^{−s})⁻¹`. -/
def ramanujanFactor (q : ℕ) (s : ℂ) : ℂ :=
  ∑ x ∈ q.divisorsAntidiagonal,
    (μ x.1 : ℂ) * x.2 * ((μ x.2 : ℂ) * (x.2 : ℂ) ^ (-s) * eulerInv x.2 s)

/-- The Liouville–Ramanujan factor `R^λ_q(s) = Σ_{de=q} μ(d) e λ(e) e^{−s}`. -/
def liouvilleRamanujanFactor (q : ℕ) (s : ℂ) : ℂ :=
  ∑ x ∈ q.divisorsAntidiagonal,
    (μ x.1 : ℂ) * x.2 * (liouvilleC x.2 * (x.2 : ℂ) ^ (-s))

theorem snd_pos_of_mem {q : ℕ} {x : ℕ × ℕ} (hx : x ∈ q.divisorsAntidiagonal) : 0 < x.2 := by
  obtain ⟨h1, h2⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  exact Nat.pos_of_ne_zero fun h => h2 (by rw [← h1, h, mul_zero])

/-- `μ(em) = μ(e) · 1_e(m) μ(m)` with `1_e` the trivial character modulo `e`. -/
theorem moebius_mul_eq {e : ℕ} [NeZero e] (m : ℕ) :
    (μ (e * m) : ℂ) = (μ e : ℂ) * ((1 : DirichletCharacter ℂ e) m * (μ m : ℂ)) := by
  by_cases hcop : Nat.Coprime e m
  · rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop]
    have hu : IsUnit (m : ZMod e) := (ZMod.isUnit_iff_coprime m e).mpr hcop.symm
    rw [MulChar.one_apply hu]
    push_cast
    ring
  · have hsq : ¬ Squarefree (e * m) := fun h => hcop (Nat.squarefree_mul_iff.mp h).1
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    have hu : ¬ IsUnit (m : ZMod e) := fun h => hcop ((ZMod.isUnit_iff_coprime m e).mp h).symm
    rw [MulChar.map_nonunit _ hu]
    simp

/-- Reindexing an L-series supported on the multiples of `e`. -/
theorem LSeries_dvd_eq {e : ℕ} (he : 0 < e) {f g : ℕ → ℂ} (hf : ∀ n, ¬ e ∣ n → f n = 0) (k : ℂ)
    (hfg : ∀ m, f (e * m) = k * g m) (s : ℂ) :
    LSeries f s = k * (e : ℂ) ^ (-s) * LSeries g s := by
  have hsupp : Function.support (LSeries.term f s) ⊆ Set.range (e * ·) := by
    intro n hn
    by_contra hnr
    apply hn
    have hne : ¬ e ∣ n := fun ⟨m, hm⟩ => hnr ⟨m, hm.symm⟩
    simp [LSeries.term, hf n hne]
  have hterm : ∀ m, LSeries.term f s (e * m) = k * (e : ℂ) ^ (-s) * LSeries.term g s m := by
    intro m
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    · have hem : e * m ≠ 0 := mul_ne_zero he.ne' hm
      have he0 : (e : ℂ) ^ s ≠ 0 := by
        rw [Complex.cpow_ne_zero_iff]; left; exact_mod_cast he.ne'
      rw [LSeries.term_of_ne_zero hem, LSeries.term_of_ne_zero hm, hfg, Nat.cast_mul,
        Complex.natCast_mul_natCast_cpow, Complex.cpow_neg]
      ring
  unfold LSeries
  rw [← (mul_right_injective₀ he.ne').tsum_eq hsupp]
  simp only [hterm]
  rw [tsum_mul_left]

/-- **The multiples of `e` in the Möbius series**: `Σ_{e|n} μ(n) n^{−s} = μ(e) e^{−s}
Π_{p|e} (1 − p^{−s})⁻¹/ζ(s)` on `Re s > 1`. -/
theorem LSeries_moebius_dvd {e : ℕ} (he : 0 < e) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => if e ∣ n then (μ n : ℂ) else 0) s =
      (μ e : ℂ) * (e : ℂ) ^ (-s) * eulerInv e s / riemannZeta s := by
  haveI : NeZero e := ⟨he.ne'⟩
  have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
  have hχ : LSeries (↗(1 : DirichletCharacter ℂ e) * ↗μ) s = eulerInv e s / riemannZeta s := by
    have h := DirichletCharacter.LSeries.mul_mu_eq_one (1 : DirichletCharacter ℂ e) hs
    rw [← DirichletCharacter.LFunction_eq_LSeries _ hs,
      GaloisForLFunctions.RHTower.HalfWeight.LFunction_one_eq e hs1] at h
    rw [eq_inv_of_mul_eq_one_right h, mul_inv, eulerInv, div_eq_mul_inv, mul_comm]
  rw [LSeries_dvd_eq he (g := ↗(1 : DirichletCharacter ℂ e) * ↗μ)
    (fun n hn => by simp [hn]) (μ e : ℂ) (fun m => by
      simp only [dvd_mul_right, if_true, Pi.mul_apply]
      exact moebius_mul_eq m) s, hχ]
  ring

/-- **The multiples of `e` in the Liouville series**: `Σ_{e|n} λ(n) n^{−s} =
λ(e) e^{−s} ζ(2s)/ζ(s)` on `Re s > 1`. -/
theorem LSeries_liouville_dvd {e : ℕ} (he : 0 < e) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => if e ∣ n then liouvilleC n else 0) s =
      liouvilleC e * (e : ℂ) ^ (-s) * (riemannZeta (2 * s) / riemannZeta s) := by
  rw [LSeries_dvd_eq he (g := ↗liouvilleC) (fun n hn => by simp [hn]) (liouvilleC e)
    (fun m => by simp only [dvd_mul_right, if_true]; exact liouvilleC_mul e m) s,
    LSeries_liouvilleC_eq_div hs]

/-- `c_q(n) = Σ_{de = q} μ(d) e 1_{e | n}`, so a Ramanujan twist is a combination of the
restrictions to multiples. -/
theorem mul_ramanujanSum_eq {q : ℕ} (hq : 0 < q) (a : ℕ → ℂ) :
    (fun n => a n * ramanujanSum q n) =
      ∑ x ∈ q.divisorsAntidiagonal, fun n => ((μ x.1 : ℂ) * x.2) * (if x.2 ∣ n then a n else 0) := by
  funext n
  rw [Finset.sum_apply, ramanujanSum_eq_sum_moebius hq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

theorem lseriesSummable_of_bounded {a : ℕ → ℂ} {B : ℝ} (hB : ∀ n, ‖a n‖ ≤ B) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable a s :=
  LSeriesSummable_of_le_const_mul_rpow (x := 1) hs ⟨B, fun n _ => by
    rw [sub_self, Real.rpow_zero, mul_one]; exact hB n⟩

theorem norm_moebius_le_one (n : ℕ) : ‖(μ n : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one

theorem norm_liouvilleC_le_one (n : ℕ) : ‖liouvilleC n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [liouvilleC_apply, ArithmeticFunction.liouville_apply hn]
    push_cast
    rw [norm_pow, norm_neg, norm_one, one_pow]

/-- **The Ramanujan twist of `μ`**: `Σ μ(n) c_q(n) n^{−s} = R_q(s)/ζ(s)` on `Re s > 1`. -/
theorem LSeries_moebius_mul_ramanujanSum {q : ℕ} (hq : 0 < q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (μ n : ℂ) * ramanujanSum q n) s = ramanujanFactor q s / riemannZeta s := by
  have hx2 : ∀ x ∈ q.divisorsAntidiagonal, 0 < x.2 := fun x hx =>
    snd_pos_of_mem hx
  have hsumm : ∀ x ∈ q.divisorsAntidiagonal, LSeriesSummable
      (fun n => ((μ x.1 : ℂ) * x.2) * (if x.2 ∣ n then (μ n : ℂ) else 0)) s := fun x _ =>
    lseriesSummable_of_bounded (B := ‖(μ x.1 : ℂ) * x.2‖) (fun n => by
      rw [norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      split_ifs
      · exact norm_moebius_le_one n
      · simp) hs
  rw [mul_ramanujanSum_eq hq (fun n => (μ n : ℂ)), LSeries_sum hsumm]
  have hterm : ∀ x ∈ q.divisorsAntidiagonal,
      LSeries (fun n => ((μ x.1 : ℂ) * x.2) * (if x.2 ∣ n then (μ n : ℂ) else 0)) s =
        (μ x.1 : ℂ) * x.2 * ((μ x.2 : ℂ) * (x.2 : ℂ) ^ (-s) * eulerInv x.2 s) / riemannZeta s := by
    intro x hx
    have hsm : (fun n => ((μ x.1 : ℂ) * x.2) * (if x.2 ∣ n then (μ n : ℂ) else 0)) =
        ((μ x.1 : ℂ) * x.2) • fun n => if x.2 ∣ n then (μ n : ℂ) else 0 := by
      funext n; simp
    rw [hsm, LSeries_smul, LSeries_moebius_dvd (hx2 x hx) hs]
    ring
  rw [Finset.sum_congr rfl hterm, ramanujanFactor, Finset.sum_div]

/-- **The Ramanujan twist of `λ`**: `Σ λ(n) c_q(n) n^{−s} = R^λ_q(s) ζ(2s)/ζ(s)` on `Re s > 1`. -/
theorem LSeries_liouville_mul_ramanujanSum {q : ℕ} (hq : 0 < q) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => liouvilleC n * ramanujanSum q n) s =
      liouvilleRamanujanFactor q s * (riemannZeta (2 * s) / riemannZeta s) := by
  have hx2 : ∀ x ∈ q.divisorsAntidiagonal, 0 < x.2 := fun x hx =>
    snd_pos_of_mem hx
  have hsumm : ∀ x ∈ q.divisorsAntidiagonal, LSeriesSummable
      (fun n => ((μ x.1 : ℂ) * x.2) * (if x.2 ∣ n then liouvilleC n else 0)) s := fun x _ =>
    lseriesSummable_of_bounded (B := ‖(μ x.1 : ℂ) * x.2‖) (fun n => by
      rw [norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_
      split_ifs
      · exact norm_liouvilleC_le_one n
      · simp) hs
  rw [mul_ramanujanSum_eq hq (fun n => liouvilleC n), LSeries_sum hsumm]
  have hterm : ∀ x ∈ q.divisorsAntidiagonal,
      LSeries (fun n => ((μ x.1 : ℂ) * x.2) * (if x.2 ∣ n then liouvilleC n else 0)) s =
        (μ x.1 : ℂ) * x.2 * (liouvilleC x.2 * (x.2 : ℂ) ^ (-s)) *
          (riemannZeta (2 * s) / riemannZeta s) := by
    intro x hx
    have hsm : (fun n => ((μ x.1 : ℂ) * x.2) * (if x.2 ∣ n then liouvilleC n else 0)) =
        ((μ x.1 : ℂ) * x.2) • fun n => if x.2 ∣ n then liouvilleC n else 0 := by
      funext n; simp
    rw [hsm, LSeries_smul, LSeries_liouville_dvd (hx2 x hx) hs]
    ring
  rw [Finset.sum_congr rfl hterm, liouvilleRamanujanFactor, Finset.sum_mul]

/-! ## Analyticity and size of the factors -/

theorem norm_natCast_cpow_neg_lt_one {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    ‖(p : ℂ) ^ (-s)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (by omega : 1 < p)) (by linarith)

theorem one_sub_cpow_ne_zero {p : ℕ} (hp : 2 ≤ p) {s : ℂ} (hs : 0 < s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have := norm_natCast_cpow_neg_lt_one hp hs
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

theorem differentiableAt_eulerInv (e : ℕ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (eulerInv e) s := by
  unfold eulerInv
  refine DifferentiableAt.inv ?_ (Finset.prod_ne_zero_iff.mpr fun p hp =>
    one_sub_cpow_ne_zero (Nat.prime_of_mem_primeFactors hp).two_le hs)
  refine DifferentiableAt.fun_finsetProd fun p hp => ?_
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  exact (differentiableAt_id.neg.const_cpow (Or.inl hp0)).const_sub 1

theorem differentiableAt_ramanujanFactor (q : ℕ) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (ramanujanFactor q) s := by
  unfold ramanujanFactor
  refine DifferentiableAt.fun_sum fun x hx => ?_
  have hx0 : (x.2 : ℂ) ≠ 0 := by exact_mod_cast (snd_pos_of_mem hx).ne'
  exact (((differentiableAt_id.neg.const_cpow (Or.inl hx0)).const_mul _).mul
    (differentiableAt_eulerInv x.2 hs)).const_mul _

theorem differentiable_liouvilleRamanujanFactor (q : ℕ) :
    Differentiable ℂ (liouvilleRamanujanFactor q) := by
  intro s
  unfold liouvilleRamanujanFactor
  refine DifferentiableAt.fun_sum fun x hx => ?_
  have hx0 : (x.2 : ℂ) ≠ 0 := by exact_mod_cast (snd_pos_of_mem hx).ne'
  exact ((differentiableAt_id.neg.const_cpow (Or.inl hx0)).const_mul _).const_mul _

/-- `|Π_{p|e} (1 − p^{−s})⁻¹| ≤ (1 − 2^{−1/2})^{−ω(e)}` on `Re s ≥ 1/2`. -/
theorem norm_eulerInv_le (e : ℕ) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖eulerInv e s‖ ≤ ((1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) ^ e.primeFactors.card := by
  have hc1 : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hc0 : 0 < 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by linarith
  unfold eulerInv
  rw [norm_inv, norm_prod, ← Finset.prod_inv_distrib, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun p _ => inv_nonneg.mpr (norm_nonneg _)) fun p hp => ?_
  have hp2 := (Nat.prime_of_mem_primeFactors hp).two_le
  have hz : ‖(p : ℂ) ^ (-s)‖ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    calc (p : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp2) (by linarith)
      _ ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  have hlow : 1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
    have := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
    rw [norm_one] at this
    linarith
  exact inv_anti₀ hc0 hlow

/-- `R_q` is bounded on `Re s ≥ 1/2`. -/
theorem exists_norm_ramanujanFactor_le (q : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, 1 / 2 ≤ s.re → ‖ramanujanFactor q s‖ ≤ M := by
  refine ⟨∑ x ∈ q.divisorsAntidiagonal,
    (x.2 : ℝ) * ((1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) ^ x.2.primeFactors.card, ?_, fun s hs => ?_⟩
  · have hc0 : 0 ≤ (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ := inv_nonneg.mpr (by
      have : (2 : ℝ) ^ (-(1 / 2 : ℝ)) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
      linarith)
    exact Finset.sum_nonneg fun x _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc0 _)
  unfold ramanujanFactor
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  have hx1 : 1 ≤ x.2 := snd_pos_of_mem hx
  have hcpow : ‖(x.2 : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hx1) (by linarith)
  simp only [norm_mul, Complex.norm_natCast]
  have h1 := norm_moebius_le_one x.1
  have h2 := norm_moebius_le_one x.2
  have h3 := norm_eulerInv_le x.2 hs
  calc ‖(μ x.1 : ℂ)‖ * (x.2 : ℝ) * (‖(μ x.2 : ℂ)‖ * ‖(x.2 : ℂ) ^ (-s)‖ * ‖eulerInv x.2 s‖)
      ≤ 1 * (x.2 : ℝ) * (1 * 1 * ((1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹) ^ x.2.primeFactors.card) := by
        gcongr
    _ = _ := by ring

/-- `R^λ_q` is bounded on `Re s ≥ 0`. -/
theorem norm_liouvilleRamanujanFactor_le (q : ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖liouvilleRamanujanFactor q s‖ ≤ ∑ x ∈ q.divisorsAntidiagonal, (x.2 : ℝ) := by
  unfold liouvilleRamanujanFactor
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  have hx1 : 1 ≤ x.2 := snd_pos_of_mem hx
  have hcpow : ‖(x.2 : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hx1) (by linarith)
  simp only [norm_mul, Complex.norm_natCast]
  have h1 := norm_moebius_le_one x.1
  have h2 := norm_liouvilleC_le_one x.2
  calc ‖(μ x.1 : ℂ)‖ * (x.2 : ℝ) * (‖liouvilleC x.2‖ * ‖(x.2 : ℂ) ^ (-s)‖)
      ≤ 1 * (x.2 : ℝ) * (1 * 1) := by gcongr
    _ = _ := by ring

/-! ## The window sums -/

/-- **The window sum of a kernel with bounded Dirichlet coefficients.**  If on `Re s = 2` the world
kernel is `e^{(s−c)²} L(a, s)` with `|a(n)| ≤ B`, its signal at `Z` is the Gaussian window sum
`Σ_n a(n) e^{c(log Z − log n) − (log Z − log n)²/4}/(2√π)`. -/
theorem signal_eq_tsum_of_LSeries (c : ℝ) {A : ℂ → ℂ} {a : ℕ → ℂ} {B : ℝ} (ha0 : a 0 = 0)
    (hB : ∀ n, ‖a n‖ ≤ B)
    (hA : ∀ s : ℂ, s.re = 2 → worldKernel c A s = cexp ((s - c) ^ 2) * LSeries a s)
    {Z : ℝ} (hZ : 0 < Z) :
    signal (worldKernel c A) 2 Z =
      ∑' n : ℕ, a n * ((Real.exp (c * (Real.log Z - Real.log n) -
        (Real.log Z - Real.log n) ^ 2 / 4) / (2 * Real.sqrt Real.pi) : ℝ) : ℂ) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  rw [signal_eq_integral _ 2 hZ]
  set s : ℝ → ℂ := fun t => ((2 : ℝ) : ℂ) + t * I with hsdef
  have hsre : ∀ t, (s t).re = 2 := fun t => by simp [s]
  have hsim : ∀ t, (s t).im = t := fun t => by simp [s]
  set F : ℕ → ℝ → ℂ := fun n t => cexp ((Real.log Z : ℂ) * s t) * cexp ((s t - c) ^ 2) *
    LSeries.term a (s t) n with hFdef
  have hsum : ∀ t, cexp ((Real.log Z : ℂ) * s t) * worldKernel c A (s t) = ∑' n, F n t := by
    intro t
    rw [hA (s t) (hsre t), LSeries, ← tsum_mul_left, ← tsum_mul_left]
    exact tsum_congr fun n => by simp only [hFdef]; ring
  -- the bound `‖F n t‖ ≤ Z² e^{(|c|+2)²} B e^{−t²}/n²`
  set K : ℝ := Z ^ (2 : ℝ) * Real.exp ((|c| + 2) ^ 2) * B
  have hnorm : ∀ n t, ‖F n t‖ ≤ K * Real.exp (-1 * t ^ 2) * (1 / (n : ℝ) ^ 2) := by
    intro n t
    simp only [F]
    rw [norm_mul, norm_mul, norm_cexp_log_mul hZ, hsre]
    have hE := norm_cexp_sq_le c (s := s t) (by rw [hsre]; norm_num) (by rw [hsre])
    rw [hsim] at hE
    have hT : ‖LSeries.term a (s t) n‖ ≤ B * (1 / (n : ℝ) ^ 2) := by
      rw [LSeries.norm_term_eq, hsre]
      split_ifs with hn
      · simp [hn]
      · have hpos : (0 : ℝ) < (n : ℝ) ^ (2 : ℝ) := by
          have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
          positivity
        rw [Real.rpow_two] at hpos ⊢
        rw [mul_one_div]
        exact div_le_div_of_nonneg_right (hB n) hpos.le
    calc Z ^ (2 : ℝ) * ‖cexp ((s t - c) ^ 2)‖ * ‖LSeries.term a (s t) n‖
        ≤ Z ^ (2 : ℝ) * (Real.exp ((|c| + 2) ^ 2) * Real.exp (-t ^ 2)) * (B * (1 / (n : ℝ) ^ 2)) := by
          gcongr
      _ = K * Real.exp (-1 * t ^ 2) * (1 / (n : ℝ) ^ 2) := by
          simp only [K, neg_one_mul]
          ring
  have hgauss : Integrable fun t : ℝ => Real.exp (-1 * t ^ 2) := integrable_exp_neg_mul_sq one_pos
  have hcontF : ∀ n, Continuous (F n) := by
    intro n
    simp only [F]
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [LSeries.term_zero, mul_zero]
      exact continuous_const
    · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      have hF : (fun t => cexp ((Real.log Z : ℂ) * s t) * cexp ((s t - c) ^ 2) *
          LSeries.term a (s t) n) = fun t => cexp ((Real.log Z : ℂ) * s t) *
          cexp ((s t - c) ^ 2) * (a n / (n : ℂ) ^ s t) := by
        funext t
        rw [LSeries.term_of_ne_zero hn]
      rw [hF]
      have hcpow : Continuous fun t : ℝ => (n : ℂ) ^ s t :=
        continuous_const.cpow (by fun_prop) fun _ => Or.inl (by
          simpa using Nat.pos_of_ne_zero hn)
      have hne : ∀ t : ℝ, (n : ℂ) ^ s t ≠ 0 := fun t => by
        rw [Complex.cpow_def_of_ne_zero hn0]
        exact Complex.exp_ne_zero _
      exact (by fun_prop : Continuous fun t : ℝ => cexp ((Real.log Z : ℂ) * s t) *
        cexp ((s t - c) ^ 2)).mul (continuous_const.div hcpow hne)
  have hint : ∀ n, Integrable (F n) := fun n =>
    Integrable.mono' ((hgauss.const_mul K).mul_const (1 / (n : ℝ) ^ 2))
      (hcontF n).aestronglyMeasurable (Eventually.of_forall fun t => hnorm n t)
  have hsummable : Summable fun n => ∫ t, ‖F n t‖ := by
    have hb : ∀ n, ∫ t, ‖F n t‖ ≤ (K * ∫ t : ℝ, Real.exp (-1 * t ^ 2)) * (1 / (n : ℝ) ^ 2) := by
      intro n
      calc ∫ t, ‖F n t‖ ≤ ∫ t, K * Real.exp (-1 * t ^ 2) * (1 / (n : ℝ) ^ 2) :=
            integral_mono (hint n).norm ((hgauss.const_mul K).mul_const _) (hnorm n)
        _ = (K * ∫ t : ℝ, Real.exp (-1 * t ^ 2)) * (1 / (n : ℝ) ^ 2) := by
            rw [integral_mul_const, integral_const_mul]
    exact Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hb
      ((Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left _)
  have hswap := integral_tsum_of_summable_integral_norm hint hsummable
  rw [integral_congr_ae (Eventually.of_forall hsum), ← hswap, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [F, ha0]
  · have hFn : (F n) = fun t : ℝ => a n * (cexp (((Real.log Z - Real.log n : ℝ) : ℂ) *
        (((2 : ℝ) : ℂ) + (t : ℂ) * I)) * cexp ((((2 : ℝ) : ℂ) + (t : ℂ) * I - c) ^ 2)) := by
      funext t
      simp only [F]
      rw [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero (by exact_mod_cast hn),
        ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n), div_eq_mul_inv,
        ← Complex.exp_neg]
      simp only [s]
      rw [show cexp ((Real.log Z : ℂ) * (((2 : ℝ) : ℂ) + t * I)) *
          cexp ((((2 : ℝ) : ℂ) + t * I - c) ^ 2) * (a n *
          cexp (-((Real.log n : ℂ) * (((2 : ℝ) : ℂ) + t * I)))) =
          a n * (cexp ((Real.log Z : ℂ) * (((2 : ℝ) : ℂ) + t * I) +
          -((Real.log n : ℂ) * (((2 : ℝ) : ℂ) + t * I))) *
          cexp ((((2 : ℝ) : ℂ) + t * I - c) ^ 2)) by rw [Complex.exp_add]; ring]
      congr 3
      push_cast
      ring
    rw [hFn, integral_const_mul, integral_gaussian_line]
    have hπ : (0 : ℝ) < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have key : ∀ E : ℝ, 1 / (2 * Real.pi) * (Real.sqrt Real.pi * E) =
        E / (2 * Real.sqrt Real.pi) := by
      intro E
      rw [show 2 * Real.pi = 2 * (Real.sqrt Real.pi * Real.sqrt Real.pi) by
        rw [Real.mul_self_sqrt Real.pi_pos.le]]
      field_simp
    rw [← key]
    push_cast
    ring

/-- The numerator `A_q(s) = (s − 1) R_q(s)` of the Ramanujan twist of `μ`. -/
def ramanujanNumerator (q : ℕ) (s : ℂ) : ℂ := (s - 1) * ramanujanFactor q s

/-- The numerator `A^λ_q(s) = (s − 1) ζ(2s) R^λ_q(s)` of the Ramanujan twist of `λ`. -/
def liouvilleRamanujanNumerator (q : ℕ) (s : ℂ) : ℂ :=
  liouvilleNumerator s * liouvilleRamanujanFactor q s

theorem norm_ramanujanSum_le {q : ℕ} (hq : 0 < q) (n : ℕ) :
    ‖ramanujanSum q n‖ ≤ ∑ x ∈ q.divisorsAntidiagonal, (x.2 : ℝ) := by
  rw [ramanujanSum_eq_sum_moebius hq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [norm_mul]
  have h1 := norm_moebius_le_one x.1
  have h2 : ‖(if x.2 ∣ n then (x.2 : ℂ) else 0)‖ ≤ x.2 := by
    split_ifs <;> simp
  calc ‖(μ x.1 : ℂ)‖ * ‖(if x.2 ∣ n then (x.2 : ℂ) else 0)‖ ≤ 1 * x.2 :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = x.2 := one_mul _

/-- **The Ramanujan-twisted Möbius window sum** is the signal of the world kernel of `A_q`. -/
theorem signal_ramanujanKernel_eq_tsum (c : ℝ) {q : ℕ} (hq : 0 < q) {Z : ℝ} (hZ : 0 < Z) :
    signal (worldKernel c (ramanujanNumerator q)) 2 Z =
      ∑' n : ℕ, (μ n : ℂ) * ramanujanSum q n * ((Real.exp (c * (Real.log Z - Real.log n) -
        (Real.log Z - Real.log n) ^ 2 / 4) / (2 * Real.sqrt Real.pi) : ℝ) : ℂ) := by
  refine signal_eq_tsum_of_LSeries c (B := ∑ x ∈ q.divisorsAntidiagonal, (x.2 : ℝ))
    (by simp) (fun n => ?_) (fun s hs => ?_) hZ
  · rw [norm_mul]
    calc ‖(μ n : ℂ)‖ * ‖ramanujanSum q n‖ ≤ 1 * ∑ x ∈ q.divisorsAntidiagonal, (x.2 : ℝ) :=
          mul_le_mul (norm_moebius_le_one n) (norm_ramanujanSum_le hq n) (norm_nonneg _)
            zero_le_one
      _ = _ := one_mul _
  · have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
    have hζ := riemannZeta_ne_zero_of_one_lt_re (show 1 < s.re by rw [hs]; norm_num)
    have hs10 := sub_ne_zero.mpr hs1
    rw [LSeries_moebius_mul_ramanujanSum hq (by rw [hs]; norm_num), worldKernel,
      ramanujanNumerator, zetaEntire_eq hs1]
    field_simp

/-- **The Ramanujan-twisted Liouville window sum** is the signal of the world kernel of
`A^λ_q`. -/
theorem signal_liouvilleRamanujanKernel_eq_tsum (c : ℝ) {q : ℕ} (hq : 0 < q) {Z : ℝ}
    (hZ : 0 < Z) :
    signal (worldKernel c (liouvilleRamanujanNumerator q)) 2 Z =
      ∑' n : ℕ, liouvilleC n * ramanujanSum q n * ((Real.exp (c * (Real.log Z - Real.log n) -
        (Real.log Z - Real.log n) ^ 2 / 4) / (2 * Real.sqrt Real.pi) : ℝ) : ℂ) := by
  refine signal_eq_tsum_of_LSeries c (B := ∑ x ∈ q.divisorsAntidiagonal, (x.2 : ℝ))
    (by simp) (fun n => ?_) (fun s hs => ?_) hZ
  · rw [norm_mul]
    calc ‖liouvilleC n‖ * ‖ramanujanSum q n‖ ≤ 1 * ∑ x ∈ q.divisorsAntidiagonal, (x.2 : ℝ) :=
          mul_le_mul (norm_liouvilleC_le_one n) (norm_ramanujanSum_le hq n) (norm_nonneg _)
            zero_le_one
      _ = _ := one_mul _
  · have hs1 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
    have hζ := riemannZeta_ne_zero_of_one_lt_re (show 1 < s.re by rw [hs]; norm_num)
    have hs10 := sub_ne_zero.mpr hs1
    rw [LSeries_liouville_mul_ramanujanSum hq (by rw [hs]; norm_num), worldKernel,
      liouvilleRamanujanNumerator, liouvilleNumerator, zetaEntire_eq hs1]
    field_simp

/-! ## The tangent data -/

theorem analyticAt_ramanujanNumerator (q : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ (ramanujanNumerator q) s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (ramanujanNumerator q) {z : ℂ | 0 < z.re} := fun z hz =>
    ((differentiableAt_id.sub_const 1).mul
      (differentiableAt_ramanujanFactor q hz)).differentiableWithinAt
  exact hd.analyticAt (hU.mem_nhds (show 0 < s.re by linarith))

theorem analyticAt_liouvilleRamanujanNumerator (q : ℕ) {s : ℂ} (hs : 1 / 2 < s.re) :
    AnalyticAt ℂ (liouvilleRamanujanNumerator q) s :=
  (analyticAt_liouvilleNumerator hs).mul
    ((differentiable_liouvilleRamanujanFactor q).analyticAt s)

/-- **The tangent datum of the Ramanujan twist of `μ` in world I.**  The twisted Gaussian window
sum at `e^u`, normalized by `e^{−Θu}`, is asymptotic to the sum of its residues at the top zeros
of `ζ`. -/
theorem tangentDatum_ramanujanTwist
    (hI : ZeroConfigurationGeometry.zetaAsymptoticAbscissa < zetaZeroAbscissa) (c : ℝ) (q : ℕ) :
    ∃ T : Finset ℂ, (∀ p : ℂ, p ∈ T ↔ riemannZeta p = 0 ∧ p.re = zetaZeroAbscissa) ∧
      Tendsto (fun u : ℝ => (Real.exp (-zetaZeroAbscissa * u) : ℂ) *
        (signal (worldKernel c (ramanujanNumerator q)) 2 (Real.exp u) -
          ∑ p ∈ T, laurentCoeff
            (fun s => cexp ((u : ℂ) * s) * worldKernel c (ramanujanNumerator q) s) p (-1)))
        atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_ramanujanFactor_le q
  refine tendsto_normalized_signal_sub_top hI c (fun s hs => analyticAt_ramanujanNumerator q hs)
    fun σ hσ => ⟨M, fun s hs h2 => ?_⟩
  unfold ramanujanNumerator
  rw [norm_mul]
  have h1 := norm_mobiusNumerator_le (s := s) (by linarith) h2
  unfold mobiusNumerator at h1
  calc ‖s - 1‖ * ‖ramanujanFactor q s‖ ≤ (1 * (2 + |s.im|)) * M :=
        mul_le_mul h1 (hM s (by linarith)) (norm_nonneg _) (by positivity)
    _ = M * (2 + |s.im|) := by ring

/-- **The tangent datum of the Ramanujan twist of `λ` in world I.** -/
theorem tangentDatum_liouvilleRamanujanTwist
    (hI : ZeroConfigurationGeometry.zetaAsymptoticAbscissa < zetaZeroAbscissa) (c : ℝ) (q : ℕ) :
    ∃ T : Finset ℂ, (∀ p : ℂ, p ∈ T ↔ riemannZeta p = 0 ∧ p.re = zetaZeroAbscissa) ∧
      Tendsto (fun u : ℝ => (Real.exp (-zetaZeroAbscissa * u) : ℂ) *
        (signal (worldKernel c (liouvilleRamanujanNumerator q)) 2 (Real.exp u) -
          ∑ p ∈ T, laurentCoeff
            (fun s => cexp ((u : ℂ) * s) * worldKernel c (liouvilleRamanujanNumerator q) s) p (-1)))
        atTop (𝓝 0) := by
  refine tendsto_normalized_signal_sub_top hI c
    (fun s hs => analyticAt_liouvilleRamanujanNumerator q hs) fun σ hσ =>
      ⟨(1 + 1 / (2 * σ - 1)) * ∑ x ∈ q.divisorsAntidiagonal, (x.2 : ℝ), fun s hs h2 => ?_⟩
  have hR := norm_liouvilleRamanujanFactor_le q (s := s) (by linarith)
  have hL := norm_liouvilleNumerator_le hσ hs h2
  unfold liouvilleRamanujanNumerator
  rw [norm_mul]
  calc ‖liouvilleNumerator s‖ * ‖liouvilleRamanujanFactor q s‖
      ≤ ((1 + 1 / (2 * σ - 1)) * (2 + |s.im|)) * ∑ x ∈ q.divisorsAntidiagonal, (x.2 : ℝ) :=
        mul_le_mul hL hR (norm_nonneg _)
          (mul_nonneg (add_nonneg zero_le_one (one_div_nonneg.mpr (by linarith))) (by positivity))
    _ = _ := by ring

/-- **The residue numerators of the Ramanujan twists.**  With `(s − 1)ζ(s) = (s − ρ)^m g(s)` at a
zero, the numerator `H = e^{(s−c)²} A/g` of the residue polynomial of the twist of `μ` is `R_q` times
that of `μ`, and the one of the twist of `λ` is `R^λ_q(s) ζ(2s)` times that of `μ`. -/
theorem ramanujanNumerator_div_eq (c : ℝ) (q : ℕ) (g : ℂ → ℂ) :
    (fun s => cexp ((s - c) ^ 2) * ramanujanNumerator q s / g s) =
        (fun s => ramanujanFactor q s * (cexp ((s - c) ^ 2) * mobiusNumerator s / g s)) ∧
      (fun s => cexp ((s - c) ^ 2) * liouvilleRamanujanNumerator q s / g s) =
        (fun s => liouvilleRamanujanFactor q s * riemannZeta (2 * s) *
          (cexp ((s - c) ^ 2) * mobiusNumerator s / g s)) := by
  refine ⟨funext fun s => ?_, funext fun s => ?_⟩
  · unfold ramanujanNumerator mobiusNumerator; ring
  · unfold liouvilleRamanujanNumerator liouvilleNumerator mobiusNumerator; ring

#print axioms tangentDatum_ramanujanTwist
#print axioms tangentDatum_liouvilleRamanujanTwist
#print axioms signal_liouvilleRamanujanKernel_eq_tsum
#print axioms signal_ramanujanKernel_eq_tsum

end GaloisForLFunctions.FloorFreeArithmetic
