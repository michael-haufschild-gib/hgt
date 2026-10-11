import GaloisForLFunctions.RHTower.JointAncestryArithmeticCapstone

/-!
# JAS positivity is Weil positivity on Euler vectors

For a finite prime set `P`, a unimodular point `w ∈ T^P` and `σ = ½ + c` with `c > 0`, let
`e_w(m) = Π_{p ∈ P} w_p^{v_p(m)}` on the `P`-smooth positive integers.  The twisted zero-sum density
of the JAS aggregate is the Weil lag form evaluated on the *Euler vector* `m ↦ e_w(m) m^{−σ}`
(`jasZeroSumDensity_eq_weilEulerForm`):

`jasZeroSumDensity c P w = Π_{p ∈ P} (1 − p^{−2σ}) · Σ_{m, n} e_w(m) e_w(n)‾ (mn)^{−σ} Φ(log n − log m)`,

the double sum running over pairs of `P`-smooth positive integers and converging absolutely.
Consequently (`riemannHypothesis_iff_weilEuler_and_halfPlane`)

`RH ⟺ (Weil's lag form is nonnegative on every harmonic Euler vector m ↦ e_w(m)/m) ∧ quasi-RH`.

**Proof.**  Each local factor is `(1 − p^{−2σ}) / ((1 − w_p p^{−(ρ+c)})(1 − w̄_p p^{−(1−ρ+c)}))`; the two
geometric factors are Euler products of the completely multiplicative functions
`m ↦ e_w(m) m^{−(ρ+c)}` and `n ↦ e_w(n)‾ n^{−(1−ρ+c)}` over the `P`-smooth integers, and
`Σ_ρ m^{−(ρ+c)} n^{−(1−ρ+c)}/(ρ(1−ρ)) = (mn)^{−σ} Φ(log n − log m)`.  Absolute convergence
(`|m^{−(ρ+c)} n^{−(1−ρ+c)}| ≤ (mn)^{−c}`) allows the exchange of the sums.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-- The primes of `P` as natural numbers. -/
def jasPrimeNats (P : Finset Nat.Primes) : Finset ℕ :=
  P.map ⟨Subtype.val, Subtype.val_injective⟩

/-- The unimodular Euler coefficient `e_w(m) = Π_{p ∈ P} w_p^{v_p(m)}`. -/
def jasEulerCoeff (P : Finset Nat.Primes) (w : ↥P → ℂ) (m : ℕ) : ℂ :=
  ∏ i : ↥P, w i ^ (m.factorization ((i : Nat.Primes) : ℕ))

/-- The twisted Euler character `m ↦ e_w(m) m^{−z}`, `0 ↦ 0`. -/
def jasEulerHom (P : Finset Nat.Primes) (w : ↥P → ℂ) (z : ℂ) : ℕ →* ℂ where
  toFun m := if m = 0 then 0 else jasEulerCoeff P w m * (m : ℂ) ^ (-z)
  map_one' := by simp [jasEulerCoeff]
  map_mul' m n := by
    by_cases hm : m = 0
    · simp [hm]
    by_cases hn : n = 0
    · simp [hn]
    rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn]
    unfold jasEulerCoeff
    rw [Nat.factorization_mul hm hn]
    simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring

theorem jasEulerHom_apply {P : Finset Nat.Primes} (w : ↥P → ℂ) (z : ℂ) {m : ℕ} (hm : m ≠ 0) :
    jasEulerHom P w z m = jasEulerCoeff P w m * (m : ℂ) ^ (-z) := by
  simp [jasEulerHom, hm]

theorem norm_jasEulerCoeff_le {P : Finset Nat.Primes} {w : ↥P → ℂ} (hw : ∀ i, ‖w i‖ = 1) (m : ℕ) :
    ‖jasEulerCoeff P w m‖ = 1 := by
  unfold jasEulerCoeff
  rw [norm_prod]
  exact Finset.prod_eq_one fun i _ => by rw [norm_pow, hw i, one_pow]

theorem jasEulerCoeff_prime {P : Finset Nat.Primes} (w : ↥P → ℂ) (i : ↥P) :
    jasEulerCoeff P w ((i : Nat.Primes) : ℕ) = w i := by
  classical
  unfold jasEulerCoeff
  rw [Nat.Prime.factorization (i : Nat.Primes).2]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    have hne : ((j : Nat.Primes) : ℕ) ≠ ((i : Nat.Primes) : ℕ) := fun h =>
      hj (Subtype.ext (Subtype.ext h))
    rw [Finsupp.single_apply, if_neg (Ne.symm hne), pow_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem norm_jasEulerHom_prime_lt {P : Finset Nat.Primes} {w : ↥P → ℂ} (hw : ∀ i, ‖w i‖ = 1)
    {z : ℂ} (hz : 0 < z.re) {p : ℕ} (hp : p.Prime) : ‖jasEulerHom P w z p‖ < 1 := by
  rw [jasEulerHom_apply w z hp.ne_zero, norm_mul, norm_jasEulerCoeff_le hw, one_mul,
    Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)

/-- **Euler product over `P`-smooth integers.** -/
theorem hasSum_jasEulerHom {P : Finset Nat.Primes} {w : ↥P → ℂ} (hw : ∀ i, ‖w i‖ = 1) {z : ℂ}
    (hz : 0 < z.re) :
    (Summable fun m : Nat.factoredNumbers (jasPrimeNats P) => ‖jasEulerHom P w z m‖) ∧
      HasSum (fun m : Nat.factoredNumbers (jasPrimeNats P) => jasEulerHom P w z m)
        (∏ i : ↥P, (1 - w i * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-z))⁻¹) := by
  classical
  obtain ⟨h1, h2⟩ := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (f := jasEulerHom P w z) (fun hp => norm_jasEulerHom_prime_lt hw hz hp) (jasPrimeNats P)
  refine ⟨h1, ?_⟩
  have hfilter : (jasPrimeNats P).filter Nat.Prime = jasPrimeNats P :=
    Finset.filter_true_of_mem fun p hp => by
      obtain ⟨q, _, rfl⟩ := Finset.mem_map.mp hp
      exact q.2
  have heq : ∏ p ∈ (jasPrimeNats P).filter Nat.Prime, (1 - jasEulerHom P w z p)⁻¹ =
      ∏ i : ↥P, (1 - w i * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-z))⁻¹ := by
    rw [hfilter, jasPrimeNats, Finset.prod_map, ← Finset.prod_attach, Finset.univ_eq_attach]
    refine Finset.prod_congr rfl fun i _ => ?_
    show (1 - jasEulerHom P w z ((i.1 : Nat.Primes) : ℕ))⁻¹ = _
    rw [jasEulerHom_apply w z i.1.2.ne_zero, jasEulerCoeff_prime]
  rw [heq] at h2
  exact h2

theorem jasHoloA_eq_cpow (s : ℂ) (p : Nat.Primes) :
    jasHoloA s p = ((p : ℕ) : ℂ) ^ (-s) := by
  rw [jasHoloA, natCast_cpow_neg_eq_cexp p.2.pos]

theorem jasHoloB_eq_cpow (s : ℂ) (p : Nat.Primes) :
    jasHoloB s p = ((p : ℕ) : ℂ) ^ (-(1 - s)) := by
  rw [jasHoloB, natCast_cpow_neg_eq_cexp p.2.pos]

/-- The local factor as a product of two geometric factors:
`(1 − ab)/((1 − aw)(1 − b w̄))` on the unit circle. -/
theorem jasHoloLocal_eq_mul {a b w : ℂ} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) (hw : ‖w‖ = 1) :
    jasHoloLocal a b w = (1 - a * b) * ((1 - w * a)⁻¹ * (1 - conj w * b)⁻¹) := by
  have h1 : 1 - a * w ≠ 0 := fun h => by
    have : ‖a * w‖ = 1 := by rw [(sub_eq_zero.mp h).symm, norm_one]
    rw [norm_mul, hw, mul_one] at this; linarith
  have h2 : 1 - b * conj w ≠ 0 := fun h => by
    have : ‖b * conj w‖ = 1 := by rw [(sub_eq_zero.mp h).symm, norm_one]
    rw [norm_mul, Complex.norm_conj, hw, mul_one] at this; linarith
  rw [jasHoloLocal, inv_one_sub_add_inv_one_sub_sub_one h1 h2]
  have hww : w * conj w = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hw]; norm_num
  rw [show a * w * (b * conj w) = a * b * (w * conj w) by ring, hww, mul_one, div_eq_mul_inv,
    mul_inv, mul_comm w a, mul_comm (conj w) b]

/-- The local factors at a zero as a constant times two Euler products. -/
theorem prod_jasHoloLocal_eq_tsum_mul {c : ℝ} (hc : 0 < c) (P : Finset Nat.Primes)
    {w : ↥P → ℂ} (hw : ∀ i, ‖w i‖ = 1) (q : XiZeroCopy) :
    ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i) (w i) =
      (∏ i : ↥P, (1 - jasHoloA ((q.1 : ℂ) + c) i * jasHoloB ((q.1 : ℂ) - c) i)) *
        ((∑' m : Nat.factoredNumbers (jasPrimeNats P), jasEulerHom P w ((q.1 : ℂ) + c) m) *
          ∑' n : Nat.factoredNumbers (jasPrimeNats P),
            jasEulerHom P (fun i => conj (w i)) (1 - (q.1 : ℂ) + c) n) := by
  have hre := xiZeroCopy_re_mem_open_unit q
  have hz1 : 0 < ((q.1 : ℂ) + c).re := by simp; linarith
  have hz2 : 0 < (1 - (q.1 : ℂ) + c).re := by simp; linarith
  have hwc : ∀ i, ‖conj (w i)‖ = 1 := fun i => by rw [Complex.norm_conj, hw i]
  rw [(hasSum_jasEulerHom hw hz1).2.tsum_eq, (hasSum_jasEulerHom hwc hz2).2.tsum_eq,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hA : ‖jasHoloA ((q.1 : ℂ) + c) i‖ < 1 := by
    rw [jasHoloA_eq_cpow]; exact norm_natCast_cpow_neg_lt_one i.1.2.two_le hz1
  have hB : ‖jasHoloB ((q.1 : ℂ) - c) i‖ < 1 := by
    rw [jasHoloB_eq_cpow, show 1 - ((q.1 : ℂ) - (c : ℂ)) = 1 - (q.1 : ℂ) + c by ring]
    exact norm_natCast_cpow_neg_lt_one i.1.2.two_le hz2
  rw [jasHoloLocal_eq_mul hA hB (hw i), jasHoloA_eq_cpow, jasHoloB_eq_cpow,
    show 1 - ((q.1 : ℂ) - (c : ℂ)) = 1 - (q.1 : ℂ) + c by ring]

/-- **Weil's lag form on the Euler vector** `m ↦ e_w(m) m^{−σ}` over `P`-smooth integers. -/
def weilEulerForm (P : Finset Nat.Primes) (w : ↥P → ℂ) (σ : ℝ) : ℂ :=
  ∑' x : Nat.factoredNumbers (jasPrimeNats P) × Nat.factoredNumbers (jasPrimeNats P),
    jasEulerCoeff P w x.1 * conj (jasEulerCoeff P w x.2) *
      (Real.exp (-σ * (Real.log (x.1 : ℕ) + Real.log (x.2 : ℕ))) : ℂ) *
        weilLagFunction (Real.log (x.2 : ℕ) - Real.log (x.1 : ℕ))

theorem jasEulerCoeff_conj (P : Finset Nat.Primes) (w : ↥P → ℂ) (m : ℕ) :
    jasEulerCoeff P (fun i => conj (w i)) m = conj (jasEulerCoeff P w m) := by
  unfold jasEulerCoeff
  rw [map_prod]
  exact Finset.prod_congr rfl fun i _ => by rw [map_pow]

theorem ne_zero_of_mem_factoredNumbers {s : Finset ℕ} (m : Nat.factoredNumbers s) :
    (m : ℕ) ≠ 0 := (Nat.mem_factoredNumbers.mp m.2).1

/-- `‖e_w(m) m^{−z}‖ = m^{−Re z}` on `P`-smooth integers. -/
theorem norm_jasEulerHom_factored {P : Finset Nat.Primes} {w : ↥P → ℂ} (hw : ∀ i, ‖w i‖ = 1)
    (z : ℂ) (m : Nat.factoredNumbers (jasPrimeNats P)) :
    ‖jasEulerHom P w z m‖ = ((m : ℕ) : ℝ) ^ (-z.re) := by
  rw [jasEulerHom_apply w z (ne_zero_of_mem_factoredNumbers m), norm_mul,
    norm_jasEulerCoeff_le hw, one_mul,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (ne_zero_of_mem_factoredNumbers m)),
    Complex.neg_re]

/-- Summation over a zero of the product of the two Euler terms. -/
theorem tsum_lagWeight_mul_jasEulerHom (c : ℝ) {P : Finset Nat.Primes} (w : ↥P → ℂ)
    (m n : Nat.factoredNumbers (jasPrimeNats P)) :
    ∑' q : XiZeroCopy, 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
        (jasEulerHom P w ((q.1 : ℂ) + c) m *
          jasEulerHom P (fun i => conj (w i)) (1 - (q.1 : ℂ) + c) n) =
      jasEulerCoeff P w m * conj (jasEulerCoeff P w n) *
        (Real.exp (-(1 / 2 + c) * (Real.log (m : ℕ) + Real.log (n : ℕ))) : ℂ) *
          weilLagFunction (Real.log (n : ℕ) - Real.log (m : ℕ)) := by
  have hm := ne_zero_of_mem_factoredNumbers m
  have hn := ne_zero_of_mem_factoredNumbers n
  rw [weilLagFunction, ← tsum_mul_left]
  refine tsum_congr fun q => ?_
  rw [jasEulerHom_apply w _ hm, jasEulerHom_apply _ _ hn, jasEulerCoeff_conj,
    natCast_cpow_neg_eq_cexp (Nat.pos_of_ne_zero hm),
    natCast_cpow_neg_eq_cexp (Nat.pos_of_ne_zero hn)]
  have hexp : cexp (-((q.1 : ℂ) + c) * (Real.log (m : ℕ) : ℂ)) *
      cexp (-(1 - (q.1 : ℂ) + c) * (Real.log (n : ℕ) : ℂ)) =
      (Real.exp (-(1 / 2 + c) * (Real.log (m : ℕ) + Real.log (n : ℕ))) : ℂ) *
        cexp (((Real.log (n : ℕ) - Real.log (m : ℕ) : ℝ) : ℂ) * ((q.1 : ℂ) - 1 / 2)) := by
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
        (jasEulerCoeff P w m * cexp (-((q.1 : ℂ) + c) * (Real.log (m : ℕ) : ℂ)) *
          (conj (jasEulerCoeff P w n) * cexp (-(1 - (q.1 : ℂ) + c) * (Real.log (n : ℕ) : ℂ))))
      = jasEulerCoeff P w m * conj (jasEulerCoeff P w n) *
          (cexp (-((q.1 : ℂ) + c) * (Real.log (m : ℕ) : ℂ)) *
            cexp (-(1 - (q.1 : ℂ) + c) * (Real.log (n : ℕ) : ℂ))) *
          (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by ring
    _ = _ := by rw [hexp]; ring

/-- The summand of the exchanged triple sum. -/
def jasEulerTerm (c : ℝ) (P : Finset Nat.Primes) (w : ↥P → ℂ) (q : XiZeroCopy)
    (x : Nat.factoredNumbers (jasPrimeNats P) × Nat.factoredNumbers (jasPrimeNats P)) : ℂ :=
  1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
    (jasEulerHom P w ((q.1 : ℂ) + c) x.1 *
      jasEulerHom P (fun i => conj (w i)) (1 - (q.1 : ℂ) + c) x.2)

theorem summable_rpow_neg_factored {c : ℝ} (hc : 0 < c) (P : Finset Nat.Primes) :
    Summable fun m : Nat.factoredNumbers (jasPrimeNats P) => ((m : ℕ) : ℝ) ^ (-c) := by
  have hv := (hasSum_jasEulerHom (P := P) (w := fun _ => (1 : ℂ)) (fun _ => norm_one)
    (z := (c : ℂ)) (by simpa using hc)).1
  refine hv.congr fun m => ?_
  rw [norm_jasEulerHom_factored (fun _ => norm_one)]
  simp

theorem norm_jasEulerTerm_le {c : ℝ} (P : Finset Nat.Primes) {w : ↥P → ℂ}
    (hw : ∀ i, ‖w i‖ = 1) (q : XiZeroCopy)
    (x : Nat.factoredNumbers (jasPrimeNats P) × Nat.factoredNumbers (jasPrimeNats P)) :
    ‖jasEulerTerm c P w q x‖ ≤ ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ *
      (((x.1 : ℕ) : ℝ) ^ (-c) * ((x.2 : ℕ) : ℝ) ^ (-c)) := by
  have hwc : ∀ i, ‖conj (w i)‖ = 1 := fun i => by rw [Complex.norm_conj, hw i]
  have hre := xiZeroCopy_re_mem_open_unit q
  rw [jasEulerTerm, norm_mul, norm_mul, norm_jasEulerHom_factored hw,
    norm_jasEulerHom_factored hwc]
  have h1 : (1 : ℝ) ≤ ((x.1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (ne_zero_of_mem_factoredNumbers x.1)
  have h2 : (1 : ℝ) ≤ ((x.2 : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (ne_zero_of_mem_factoredNumbers x.2)
  have e1 : ((x.1 : ℕ) : ℝ) ^ (-((q.1 : ℂ) + c).re) ≤ ((x.1 : ℕ) : ℝ) ^ (-c) :=
    Real.rpow_le_rpow_of_exponent_le h1 (by simp; linarith)
  have e2 : ((x.2 : ℕ) : ℝ) ^ (-(1 - (q.1 : ℂ) + c).re) ≤ ((x.2 : ℕ) : ℝ) ^ (-c) :=
    Real.rpow_le_rpow_of_exponent_le h2 (by simp; linarith)
  exact mul_le_mul_of_nonneg_left (mul_le_mul e1 e2 (by positivity) (by positivity))
    (norm_nonneg _)

theorem summable_uncurry_jasEulerTerm {c : ℝ} (hc : 0 < c) (P : Finset Nat.Primes)
    {w : ↥P → ℂ} (hw : ∀ i, ‖w i‖ = 1) : Summable (Function.uncurry (jasEulerTerm c P w)) := by
  have hv' := summable_rpow_neg_factored hc P
  have hn : ∀ m : Nat.factoredNumbers (jasPrimeNats P),
      ‖((m : ℕ) : ℝ) ^ (-c)‖ = ((m : ℕ) : ℝ) ^ (-c) := fun m =>
    Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hvv := summable_mul_of_summable_norm (hv'.congr fun m => (hn m).symm)
    (hv'.congr fun m => (hn m).symm)
  have hbig := summable_mul_of_summable_norm
    (summable_inv_mul_one_sub.norm.congr fun q => (norm_norm _).symm)
    (hvv.congr fun x => (Real.norm_of_nonneg (by positivity)).symm)
  exact Summable.of_norm_bounded hbig fun y => norm_jasEulerTerm_le P hw y.1 y.2

/-- Each zero: weight times local factors = constant times the inner double sum. -/
theorem lagWeight_mul_prod_jasHoloLocal_eq {c : ℝ} (hc : 0 < c) (P : Finset Nat.Primes)
    {w : ↥P → ℂ} (hw : ∀ i, ‖w i‖ = 1) (q : XiZeroCopy) :
    1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) *
      ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i) (jasHoloB ((q.1 : ℂ) - c) i) (w i) =
      (∏ i : ↥P, ((1 - Real.exp (-(1 + 2 * c) * Real.log (i : Nat.Primes)) : ℝ) : ℂ)) *
        ∑' x, jasEulerTerm c P w q x := by
  have hwc : ∀ i, ‖conj (w i)‖ = 1 := fun i => by rw [Complex.norm_conj, hw i]
  have hre := xiZeroCopy_re_mem_open_unit q
  have hz1 : 0 < ((q.1 : ℂ) + c).re := by simp; linarith
  have hz2 : 0 < (1 - (q.1 : ℂ) + c).re := by simp; linarith
  have hAB : ∀ i : ↥P, 1 - jasHoloA ((q.1 : ℂ) + c) i * jasHoloB ((q.1 : ℂ) - c) i =
      ((1 - Real.exp (-(1 + 2 * c) * Real.log (i : Nat.Primes)) : ℝ) : ℂ) := by
    intro i
    rw [jasHoloA, jasHoloB, ← Complex.exp_add]
    push_cast
    congr 2
    ring
  rw [prod_jasHoloLocal_eq_tsum_mul hc P hw q, Finset.prod_congr rfl fun i _ => hAB i,
    tsum_mul_tsum_of_summable_norm (hasSum_jasEulerHom hw hz1).1 (hasSum_jasEulerHom hwc hz2).1]
  unfold jasEulerTerm
  rw [tsum_mul_left]
  ring

/-- **JAS density = Weil form on Euler vectors.**  For `c > 0` and a unimodular `w ∈ T^P`,
the twisted zero-sum density equals `Π_{p ∈ P} (1 − p^{−(1+2c)})` times Weil's lag form on the
Euler vector `m ↦ e_w(m) m^{−(½+c)}`. -/
theorem jasZeroSumDensity_eq_weilEulerForm {c : ℝ} (hc : 0 < c) (P : Finset Nat.Primes)
    {w : ↥P → ℂ} (hw : ∀ i, ‖w i‖ = 1) :
    jasZeroSumDensity c P w =
      (∏ i : ↥P, ((1 - Real.exp (-(1 + 2 * c) * Real.log (i : Nat.Primes)) : ℝ) : ℂ)) *
        weilEulerForm P w (1 / 2 + c) := by
  have hsumg := summable_uncurry_jasEulerTerm hc P hw
  rw [jasZeroSumDensity, tsum_congr (lagWeight_mul_prod_jasHoloLocal_eq hc P hw), tsum_mul_left,
    weilEulerForm, ← Summable.tsum_comm' hsumg (fun q => hsumg.prod_factor q)
      (fun x => hsumg.prod_symm.prod_factor x)]
  congr 1
  exact tsum_congr fun x => tsum_lagWeight_mul_jasEulerHom c w x.1 x.2

/-- The constant factor `Π_{p ∈ P} (1 − p^{−(1+2c)})` is positive. -/
theorem prod_one_sub_exp_pos {c : ℝ} (hc : 0 < c) (P : Finset Nat.Primes) :
    0 < ∏ i : ↥P, (1 - Real.exp (-(1 + 2 * c) * Real.log (i : Nat.Primes))) := by
  refine Finset.prod_pos fun i _ => ?_
  have hl := log_prime_pos (i : Nat.Primes)
  have : Real.exp (-(1 + 2 * c) * Real.log (i : Nat.Primes)) < 1 :=
    Real.exp_lt_one_iff.mpr (by nlinarith)
  linarith

/-- **JAS positivity is Weil positivity on Euler vectors.**  For `σ > ½`, the dressed JAS
aggregate is positive semidefinite at `σ` iff Weil's lag form is nonnegative on every Euler vector
`m ↦ e_w(m) m^{−σ}` (`P` finite, `w ∈ T^P`). -/
theorem jasDressedPSD_iff_weilEulerForm_nonneg {σ : ℝ} (hσ : 1 / 2 < σ) :
    JasDressedPSD σ ↔ ∀ (P : Finset Nat.Primes) (w : ↥P → ℂ), (∀ i, ‖w i‖ = 1) →
      0 ≤ (weilEulerForm P w σ).re := by
  obtain ⟨c, rfl⟩ : ∃ c, σ = 1 / 2 + c := ⟨σ - 1 / 2, by ring⟩
  have hc : 0 < c := by linarith
  rw [jasDressedPSD_iff_pointwise hc]
  refine forall_congr' fun P => forall_congr' fun w => forall_congr' fun hw => ?_
  have h := jasZeroSumDensity_eq_weilEulerForm hc P hw
  unfold jasZeroSumDensity at h
  rw [h, ← Complex.ofReal_prod, Complex.re_ofReal_mul]
  have hK := prod_one_sub_exp_pos hc P
  constructor
  · intro h0; exact nonneg_of_mul_nonneg_right h0 hK
  · intro h0; exact mul_nonneg hK.le h0

/-- **A Weil-type capstone.**  RH holds iff Weil's lag form is nonnegative on every harmonic Euler
vector `m ↦ e_w(m)/m` over `P`-smooth integers and some half-plane bound `α < ½` holds. -/
theorem riemannHypothesis_iff_weilEuler_and_halfPlane :
    RiemannHypothesis ↔ (∀ (P : Finset Nat.Primes) (w : ↥P → ℂ), (∀ i, ‖w i‖ = 1) →
      0 ≤ (weilEulerForm P w 1).re) ∧
        ∃ alpha : ℝ, 0 ≤ alpha ∧ alpha < 1 / 2 ∧ XiZeroHalfPlaneBound alpha := by
  rw [riemannHypothesis_iff_jasDressedPSD_one_and_quasi,
    jasDressedPSD_iff_weilEulerForm_nonneg (by norm_num)]

end

end RHTower
