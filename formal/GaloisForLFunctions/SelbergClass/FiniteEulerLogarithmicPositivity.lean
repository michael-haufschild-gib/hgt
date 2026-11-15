import GaloisForLFunctions.SelbergClass.PositiveFiniteEulerBound
import GaloisForLFunctions.ZeroConfigurationGeometry.OneSidedPowerSumsDetectEveryExteriorRoot

/-!
# Logarithmic positivity detects finite Euler roots

A polynomial Euler multiplier contributes the negative power sums of its local
roots. The canonical logarithm is unique on every right half-plane on which it
converges absolutely. Eventual nonnegativity of its repeated-prime coefficients
therefore excludes every root outside the unit disk.
-/

noncomputable section
open Complex Filter Topology

namespace GaloisForLFunctions.SelbergClass.FiniteEuler

open PositiveFiniteEuler
open GaloisForLFunctions.ZeroConfigurationGeometry

/-- The polynomial multiplier with local roots counted with multiplicity. -/
def multiplier (W : Multiset ℂ) (x : ℂ) : ℂ :=
  (W.map fun a => 1 - a * x).prod

/-- The logarithmic correction supported on powers of one prime. -/
def rootLogCoeff (p : ℕ) (W : Multiset ℂ) (n : ℕ) : ℂ :=
  (W.map fun a => powerLogCoeff p a n).sum

/-- The zeta logarithm after multiplication by a finite local polynomial. -/
def logCoeff (p : ℕ) (W : Multiset ℂ) (n : ℕ) : ℂ :=
  RHTower.eulerLogDirichletCoeff n + rootLogCoeff p W n

private theorem rootLog_hasSum {p : ℕ} (hp : 1 < p) (W : Multiset ℂ) (s : ℂ)
    (hsmall : ∀ a ∈ W, ‖a * (p : ℂ) ^ (-s)‖ < 1) :
    LSeriesHasSum (rootLogCoeff p W) s
      (W.map fun a => Complex.log (1 - a * (p : ℂ) ^ (-s))).sum := by
  induction W using Multiset.induction_on with
  | empty =>
    simpa only [rootLogCoeff, Multiset.map_zero, Multiset.sum_zero,
      LSeriesHasSum, LSeries.term, zero_div, ite_self] using
      (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)
  | cons a W ih =>
    simpa only [rootLogCoeff, Multiset.map_cons, Multiset.sum_cons] using
      (hasSum_powerLogCoeff hp a (hsmall a (Multiset.mem_cons_self _ _))).add
        (ih fun b hb => hsmall b (Multiset.mem_cons_of_mem hb))

private theorem exp_sum_log {p : ℕ} (W : Multiset ℂ) (s : ℂ)
    (hsmall : ∀ a ∈ W, ‖a * (p : ℂ) ^ (-s)‖ < 1) :
    Complex.exp (W.map fun a => Complex.log (1 - a * (p : ℂ) ^ (-s))).sum =
      multiplier W ((p : ℂ) ^ (-s)) := by
  induction W using Multiset.induction_on with
  | empty => simp only [multiplier, Multiset.map_zero, Multiset.sum_zero,
      Multiset.prod_zero, Complex.exp_zero]
  | cons a W ih =>
    have hne : 1 - a * (p : ℂ) ^ (-s) ≠ 0 := by
      intro h
      have hn := hsmall a (Multiset.mem_cons_self _ _)
      rw [← sub_eq_zero.mp h, norm_one] at hn
      exact lt_irrefl _ hn
    simp only [Multiset.map_cons, Multiset.sum_cons, Complex.exp_add,
      Complex.exp_log hne, multiplier, Multiset.prod_cons]
    rw [ih fun b hb => hsmall b (Multiset.mem_cons_of_mem hb)]

/-- The finite local Taylor logarithms give an absolutely convergent Euler identity. -/
theorem logCoeff_summable_exp {p : ℕ} (hp : p.Prime) (W : Multiset ℂ) {s : ℂ}
    (hs : 1 < s.re) (hsmall : ∀ a ∈ W, ‖a * (p : ℂ) ^ (-s)‖ < 1) :
    LSeriesSummable (logCoeff p W) s ∧
      Complex.exp (LSeries (logCoeff p W) s) =
        riemannZeta s * multiplier W ((p : ℂ) ^ (-s)) := by
  have hsum := (RHTower.canonicalEulerLogZeta_summable hs).LSeriesHasSum.add
    (rootLog_hasSum hp.one_lt W s hsmall)
  refine ⟨hsum.LSeriesSummable, ?_⟩
  rw [show LSeries (logCoeff p W) s = RHTower.canonicalEulerLogZeta s +
      (W.map fun a => Complex.log (1 - a * (p : ℂ) ^ (-s))).sum from hsum.LSeries_eq,
    Complex.exp_add, RHTower.exp_canonicalEulerLogZeta_eq_riemannZeta hs,
    exp_sum_log W s hsmall]

private theorem exists_root_log_halfplane {p : ℕ} (hp : 1 < p) (a : ℂ) :
    ∃ B : ℝ, ∀ s : ℂ, B < s.re → ‖a * (p : ℂ) ^ (-s)‖ < 1 := by
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hl : 0 < Real.log p := Real.log_pos hpR
  have hbase : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have ht : Tendsto (fun x : ℝ => ‖a‖ * Real.exp (-(Real.log p * x))) atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply, id_eq] using
      (hbase.comp (Filter.Tendsto.const_mul_atTop hl tendsto_id)).const_mul ‖a‖
  obtain ⟨B, hB⟩ := eventually_atTop.mp (ht.eventually_lt_const (by norm_num : (0 : ℝ) < 1))
  refine ⟨B, fun s hs => ?_⟩
  have heq : ‖a * (p : ℂ) ^ (-s)‖ = ‖a‖ * Real.exp (-(Real.log p * s.re)) := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re,
      Real.rpow_def_of_pos (by positivity)]
    congr 2
    ring
  rw [heq]
  exact hB s.re hs.le

/-- Every finite Euler polynomial has its canonical logarithm on some right half-plane. -/
theorem exists_log_halfplane {p : ℕ} (hp : 1 < p) (W : Multiset ℂ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ s : ℂ, B < s.re →
      ∀ a ∈ W, ‖a * (p : ℂ) ^ (-s)‖ < 1 := by
  induction W using Multiset.induction_on with
  | empty => exact ⟨1, le_rfl, fun _ _ a ha => by simp only [Multiset.notMem_zero] at ha⟩
  | cons a W ih =>
    obtain ⟨B, hB, hW⟩ := ih
    obtain ⟨C, hC⟩ := exists_root_log_halfplane hp a
    refine ⟨max B C, hB.trans (le_max_left _ _), fun s hs b hb => ?_⟩
    rcases Multiset.mem_cons.mp hb with rfl | hb
    · exact hC s ((le_max_right _ _).trans_lt hs)
    · exact hW s ((le_max_left _ _).trans_lt hs) b hb

private theorem rootLogCoeff_pow {p : ℕ} (hp : 1 < p) (W : Multiset ℂ) (k : ℕ) :
    rootLogCoeff p W (p ^ k) = -(W.map fun a => a ^ k).sum / (k : ℂ) := by
  induction W using Multiset.induction_on with
  | empty => simp only [rootLogCoeff, Multiset.map_zero, Multiset.sum_zero, neg_zero, zero_div]
  | cons a W ih =>
    simp only [rootLogCoeff, Multiset.map_cons, Multiset.sum_cons] at ih ⊢
    rw [powerLogCoeff_pow hp, ih]
    ring

/-- These are the actual repeated-prime logarithmic coefficients. -/
theorem logCoeff_prime_pow {p : ℕ} (hp : p.Prime) (W : Multiset ℂ)
    {k : ℕ} (hk : k ≠ 0) :
    logCoeff p W (p ^ k) = (1 - (W.map fun a => a ^ k).sum) / (k : ℂ) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [logCoeff, rootLogCoeff_pow hp.one_lt,
    RHTower.eulerLogDirichletCoeff_prime_pow_succ _ _ hp]
  ring

/-- Every exterior root forces negative logarithmic coefficients beyond every cutoff. -/
theorem exists_negative_logCoeff {p : ℕ} (hp : p.Prime) (W : Multiset ℂ)
    {a : ℂ} (ha : a ∈ W) (hlarge : 1 < ‖a‖) (m₀ : ℕ) :
    ∃ k, m₀ ≤ k ∧ 0 < k ∧ (logCoeff p W (p ^ k)).re < 0 := by
  obtain ⟨k, hk, hk0, hsum⟩ := exists_re_powerSum_gt W ha hlarge 1 m₀
  refine ⟨k, hk, hk0, ?_⟩
  rw [logCoeff_prime_pow hp W hk0.ne']
  have hre : ((1 - (W.map fun a => a ^ k).sum) / (k : ℂ)).re =
      (1 - (W.map fun a => a ^ k).sum.re) / (k : ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, Complex.sub_re, Complex.one_re]
  rw [hre]
  exact div_neg_of_neg_of_pos (sub_neg.mpr hsum) (by exact_mod_cast hk0)

/-- Eventual nonnegativity of the prime-power logarithm forces all local roots into the unit disk. -/
theorem norm_le_one_of_eventually_logCoeff_nonneg {p : ℕ} (hp : p.Prime) (W : Multiset ℂ)
    (hpos : ∀ᶠ k : ℕ in atTop, 0 ≤ (logCoeff p W (p ^ k)).re) :
    ∀ a ∈ W, ‖a‖ ≤ 1 := by
  intro a ha
  by_contra h
  obtain ⟨N, hN⟩ := eventually_atTop.mp hpos
  obtain ⟨k, hk, _, hneg⟩ := exists_negative_logCoeff hp W ha (not_le.mp h) N
  exact (hN k hk).not_gt hneg

/-- Any absolutely convergent logarithmic representation has these coefficients at prime powers. -/
theorem coeff_prime_pow_eq {p : ℕ} (hp : p.Prime) (W : Multiset ℂ)
    {b : ℕ → ℂ} {B : ℝ}
    (hb : ∀ s : ℂ, B < s.re → LSeriesSummable b s ∧
      Complex.exp (LSeries b s) = riemannZeta s * multiplier W ((p : ℂ) ^ (-s)))
    {k : ℕ} (hk : k ≠ 0) : b (p ^ k) = logCoeff p W (p ^ k) := by
  obtain ⟨C, hC, hsmall⟩ := exists_log_halfplane hp.one_lt W
  apply DirichletSeries.coeff_eq_of_exp_lSeries_eq (B := max B C)
  · exact fun s hs => (hb s ((le_max_left _ _).trans_lt hs)).1
  · intro s hs
    have hCs := (le_max_right B C).trans_lt hs
    exact (logCoeff_summable_exp hp W (hC.trans_lt hCs) (hsmall s hCs)).1
  · intro s hs
    have hCs := (le_max_right B C).trans_lt hs
    exact (hb s ((le_max_left _ _).trans_lt hs)).2.trans
      (logCoeff_summable_exp hp W (hC.trans_lt hCs) (hsmall s hCs)).2.symm
  · exact one_lt_pow₀ hp.one_lt hk

/-- Nonnegative logarithmic coefficients on any right half-plane exclude every exterior root. -/
theorem norm_le_one_of_nonnegative_logarithm {p : ℕ} (hp : p.Prime) (W : Multiset ℂ)
    {b : ℕ → ℂ} (hpos : ∀ n : ℕ, 0 ≤ (b n).re) {B : ℝ}
    (hb : ∀ s : ℂ, B < s.re → LSeriesSummable b s ∧
      Complex.exp (LSeries b s) = riemannZeta s * multiplier W ((p : ℂ) ^ (-s))) :
    ∀ a ∈ W, ‖a‖ ≤ 1 := by
  apply norm_le_one_of_eventually_logCoeff_nonneg hp W
  filter_upwards [eventually_ge_atTop 1] with k hk
  rw [← coeff_prime_pow_eq hp W hb (by omega : k ≠ 0)]
  exact hpos _

end GaloisForLFunctions.SelbergClass.FiniteEuler
