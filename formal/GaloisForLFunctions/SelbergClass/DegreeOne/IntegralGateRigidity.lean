import GaloisForLFunctions.SelbergClass.DegreeOne.Classification
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.EulerProduct.ExpLog

/-!
# Unconditional Rigidity of Degree-One Integral Prime Gates in the Extended Selberg Class

Let `F : ExtendedSelbergClass` have `F.gammaData.degree = 1`, `F.coeff 1 = 1`, coprime
multiplicativity, and degree-one integral prime-power coefficients `F.coeff (p ^ k) = (a p : ℂ) ^ k`
for `a : ℕ → ℤ` (assuming neither Ramanujan bounds, nor `ϑ < 1/2`, nor `internalShift = 0`).

1. **Automatic Sign-Alphabet Collapse (`integral_prime_gate_mem_signs`)**: Boundary periodicity in
   `ExtendedSelbergClass` forces `|a p| ≤ 1`, hence `a p ∈ {-1, 0, 1}` for every prime `p`.
2. **Automatic Full-Class Lift (`exists_full_selberg_of_integral_prime_gates`)**: With `|a p| ≤ 1`,
   `‖F.coeff n‖ ≤ 1`, the canonical Euler logarithm satisfies `ϑ = 0 < 1/2`, and `F` lifts
   unconditionally to `RHTower.SelbergClass`.
3. **Vanishing Shift and Quadratic Character Classification (`degreeOne_integral_gate_classification`)**:
   Unique factorization on two primes above the conductor forces `F.gammaData.internalShift = 0`
   for every conductor `q ≥ 1`, and `F` is the untwisted Dirichlet `L`-function `L(s, χ)` of a
   primitive real (quadratic) character `χ` modulo `q` (`χ u ∈ {-1, 0, 1}` for all `u : ZMod q`).
4. **Unique Zeta Pinning (`degreeOne_integral_gate_eq_zeta_iff`)**: Conductor `q = 1` is equivalent
   to having a pole at `s = 1` (`meromorphicOrderAt F 1 < 0`), and either condition uniquely pins
   `a p = 1` at every prime `p` and `F(s) = ζ(s)` for all `s ≠ 1`.
-/

noncomputable section

set_option autoImplicit false

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace GaloisForLFunctions.SelbergClass.DegreeOne

/-! ### Completely multiplicative extension of prime-indexed integer parameters -/

/-- Completely multiplicative monoid-with-zero homomorphism `ℕ →*₀ ℂ` sending each prime `p`
to `(a p : ℂ)`. -/
def primeIntMultHom (a : ℕ → ℤ) : ℕ →*₀ ℂ where
  toFun n := if n = 0 then 0 else (n.primeFactorsList.map fun p => ((a p : ℤ) : ℂ)).prod
  map_zero' := rfl
  map_one' := by simp
  map_mul' m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    simp only [mul_eq_zero.not.mpr ⟨hm, hn⟩, hm, hn, ↓reduceIte]
    rw [((Nat.perm_primeFactorsList_mul hm hn).map fun p => ((a p : ℤ) : ℂ)).prod_eq,
      List.map_append, List.prod_append]

theorem primeIntMultHom_prime (a : ℕ → ℤ) {p : ℕ} (hp : p.Prime) :
    primeIntMultHom a p = ((a p : ℤ) : ℂ) := by
  simp [primeIntMultHom, hp.ne_zero, Nat.primeFactorsList_prime hp]

theorem primeIntMultHom_prime_pow (a : ℕ → ℤ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primeIntMultHom a (p ^ k) = ((a p : ℤ) : ℂ) ^ k := by
  rw [map_pow, primeIntMultHom_prime a hp]

/-- Any coprime-multiplicative arithmetic function with `f 1 = 1` and `f (p ^ k) = (a p) ^ k`
equals `primeIntMultHom a` on all of `ℕ`, hence is completely multiplicative. -/
theorem coeff_eq_primeIntMultHom {f : ArithmeticFunction ℂ} {a : ℕ → ℤ}
    (h1 : f 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → f (m * n) = f m * f n)
    (hpow : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, f (p ^ k) = ((a p : ℤ) : ℂ) ^ k) :
    ∀ n : ℕ, f n = primeIntMultHom a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [primeIntMultHom]
    rcases eq_or_ne n 1 with rfl | hn1
    · simpa [primeIntMultHom] using h1
    have hn2 : 2 ≤ n := by omega
    set p : ℕ := n.minFac
    have hp : p.Prime := Nat.minFac_prime hn1
    have hdvd : p ∣ n := Nat.minFac_dvd n
    set k : ℕ := n.factorization p
    set m : ℕ := ordCompl[p] n
    have hk_pos : 0 < k := hp.factorization_pos_of_dvd hn0 hdvd
    have hpk_gt1 : 1 < p ^ k := Nat.one_lt_pow hk_pos.ne' hp.one_lt
    have hdecomp : p ^ k * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
    have hm0 : m ≠ 0 := fun h => hn0 (by rw [← hdecomp, h, mul_zero])
    have hm_lt : m < n := by
      calc m = 1 * m := (one_mul m).symm
        _ < p ^ k * m := Nat.mul_lt_mul_of_pos_right hpk_gt1 (Nat.pos_of_ne_zero hm0)
        _ = n := hdecomp
    have hcop : (p ^ k).Coprime m :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_ordCompl hp hn0))
    rw [← hdecomp, hmul (pow_ne_zero k hp.ne_zero) hm0 hcop, hpow hp k, ih m hm_lt,
      map_mul, primeIntMultHom_prime_pow a hp k]

theorem norm_primeIntMultHom_le_one {a : ℕ → ℤ}
    (ha : ∀ {p : ℕ}, p.Prime → |a p| ≤ 1) (n : ℕ) :
    ‖primeIntMultHom a n‖ ≤ 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [primeIntMultHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg hn]
  have hmem : ∀ z ∈ n.primeFactorsList.map (fun p => ((a p : ℤ) : ℂ)), ‖z‖ ≤ 1 := by
    intro z hz
    obtain ⟨p, hpL, rfl⟩ := List.mem_map.mp hz
    have hp : p.Prime := Nat.prime_of_mem_primeFactorsList hpL
    rw [Complex.norm_intCast]
    exact_mod_cast ha hp
  clear hn
  induction n.primeFactorsList with
  | nil => simp
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons, norm_mul]
    exact mul_le_one₀ (hmem _ (List.mem_cons_self)) (norm_nonneg _)
      (ih fun z hz => hmem z (List.mem_cons_of_mem _ hz))

theorem primeIntMultHom_mem_signs {a : ℕ → ℤ}
    (ha : ∀ {p : ℕ}, p.Prime → a p = -1 ∨ a p = 0 ∨ a p = 1) {n : ℕ} (hn : n ≠ 0) :
    primeIntMultHom a n = -1 ∨ primeIntMultHom a n = 0 ∨ primeIntMultHom a n = 1 := by
  simp only [primeIntMultHom, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, if_neg hn]
  have hmem : ∀ z ∈ n.primeFactorsList.map (fun p => ((a p : ℤ) : ℂ)),
      z = -1 ∨ z = 0 ∨ z = 1 := by
    intro z hz
    obtain ⟨p, hpL, rfl⟩ := List.mem_map.mp hz
    rcases ha (Nat.prime_of_mem_primeFactorsList hpL) with h | h | h <;> simp [h]
  clear hn
  induction n.primeFactorsList with
  | nil => exact Or.inr (Or.inr (by simp))
  | cons p ps ih =>
    simp only [List.map_cons, List.prod_cons]
    have hp_s := hmem _ List.mem_cons_self
    have hps_s := ih fun z hz => hmem z (List.mem_cons_of_mem _ hz)
    rcases hp_s with h1 | h1 | h1 <;> rcases hps_s with h2 | h2 | h2 <;> simp [h1, h2]

/-! ### Step 1: Boundary periodicity forces `a p ∈ {-1, 0, 1}` without Ramanujan -/

/-- **Automatic Sign-Alphabet Collapse.** In `ExtendedSelbergClass` at degree `1`, integral
prime-power coefficients `F.coeff (p ^ k) = (a p : ℂ) ^ k` automatically satisfy `|a p| ≤ 1`
(hence `a p ∈ {-1, 0, 1}`) at every prime `p`, without assuming Ramanujan or `ϑ < 1/2`. -/
theorem integral_prime_gate_mem_signs (F : ExtendedSelbergClass) (hd : F.gammaData.degree = 1)
    {a : ℕ → ℤ}
    (hpow : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, F.coeff (p ^ k) = ((a p : ℤ) : ℂ) ^ k)
    {p : ℕ} (hp : p.Prime) :
    |a p| ≤ 1 ∧ (a p = -1 ∨ a p = 0 ∨ a p = 1) := by
  obtain ⟨q, hq0, hq⟩ := exists_conductor_eq_nat F hd
  have hq_pos : 0 < q := Nat.pos_of_ne_zero hq0
  have hnorm_tw : ∀ m : ℕ, m ≠ 0 → ‖twistedCoeff F m‖ = ‖F.coeff m‖ := by
    intro m hm
    rw [twistedCoeff, norm_mul, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hm)]
    simp
  have hper_norm : ∀ m : ℕ, m ≠ 0 → ‖F.coeff (m + q)‖ = ‖F.coeff m‖ := by
    intro m hm
    rw [← hnorm_tw (m + q) (by omega), ← hnorm_tw m hm, twistedCoeff_add_conductor F hd hq hm]
  have hkper : ∀ j m : ℕ, m ≠ 0 → ‖F.coeff (m + j * q)‖ = ‖F.coeff m‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      intro m hm
      rw [show m + (j + 1) * q = m + j * q + q by ring, hper_norm _ (by omega), ih m hm]
  set S : Finset ℕ := Finset.Icc 1 q
  have hS_ne : S.Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hq_pos⟩⟩
  set M : ℝ := S.sup' hS_ne fun r => ‖F.coeff r‖
  have hbound : ∀ m : ℕ, m ≠ 0 → ‖F.coeff m‖ ≤ M := by
    intro m hm
    set r0 : ℕ := m % q
    rcases eq_or_ne r0 0 with hr0 | hr0
    · obtain ⟨j, hj⟩ := Nat.dvd_of_mod_eq_zero hr0
      have hj0 : j ≠ 0 := fun h => hm (by rw [hj, h, mul_zero])
      obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      have heq : m = q + j' * q := by rw [hj]; ring
      rw [heq, hkper j' q hq0]
      exact Finset.le_sup' (fun r => ‖F.coeff r‖) (Finset.mem_Icc.mpr ⟨hq_pos, le_rfl⟩)
    · have hdiv := (Nat.div_add_mod m q).symm
      have heq : m = r0 + (m / q) * q := by rw [mul_comm]; omega
      rw [heq, hkper (m / q) r0 hr0]
      exact Finset.le_sup' (fun r => ‖F.coeff r‖)
        (Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hr0, (Nat.mod_lt m hq_pos).le⟩)
  have habs_le : |a p| ≤ 1 := by
    by_contra hgt
    push Not at hgt
    have h2 : (2 : ℝ) ≤ |(a p : ℝ)| := by
      have hi : 2 ≤ |a p| := by omega
      exact_mod_cast hi
    obtain ⟨k, hk⟩ := exists_pow_gt (by norm_num : (1 : ℝ) < 2) M
    have hpk := hbound (p ^ k) (pow_ne_zero k hp.ne_zero)
    rw [hpow hp k, norm_pow, Complex.norm_intCast] at hpk
    have hpow_le : (2 : ℝ) ^ k ≤ |(a p : ℝ)| ^ k := pow_le_pow_left₀ (by norm_num) h2 k
    linarith
  refine ⟨habs_le, ?_⟩
  omega

/-! ### Step 2: Automatic Euler-product lift to the full Selberg class -/

/-- Canonical Euler logarithm attached to `primeIntMultHom a`. -/
def primeIntEulerLog (a : ℕ → ℤ) : ArithmeticFunction ℂ :=
  ⟨fun n => primeIntMultHom a n * eulerLogDirichletCoeff n, by simp⟩

private theorem norm_primeIntEulerLog_le_one {a : ℕ → ℤ}
    (ha : ∀ {p : ℕ}, p.Prime → |a p| ≤ 1) (n : ℕ) :
    ‖primeIntEulerLog a n‖ ≤ 1 := by
  show ‖primeIntMultHom a n * eulerLogDirichletCoeff n‖ ≤ 1
  rw [norm_mul]
  exact mul_le_one₀ (norm_primeIntMultHom_le_one ha n) (norm_nonneg _)
    (norm_eulerLogDirichletCoeff_le_one n)

private theorem lSeriesSummable_primeIntEulerLog {a : ℕ → ℤ}
    (ha : ∀ {p : ℕ}, p.Prime → |a p| ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (primeIntEulerLog a) s := by
  have h1n : Summable fun n => ‖LSeries.term (1 : ℕ → ℂ) s n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_one_iff.mpr hs)
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) h1n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div]
    simp only [Pi.one_apply, norm_one, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (norm_primeIntEulerLog_le_one ha n)
      (inv_nonneg.mpr (norm_nonneg ((n : ℂ) ^ s)))

private theorem exp_lSeries_primeIntEulerLog {a : ℕ → ℤ}
    (ha : ∀ {p : ℕ}, p.Prime → |a p| ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (LSeries (primeIntEulerLog a) s) = LSeries (primeIntMultHom a) s := by
  have h1n : Summable fun n => ‖LSeries.term (1 : ℕ → ℂ) s n‖ :=
    summable_norm_iff.mpr (LSeriesSummable_one_iff.mpr hs)
  let fs : ℕ →*₀ ℂ :=
    { toFun := fun n => LSeries.term (primeIntMultHom a) s n
      map_zero' := by simp
      map_one' := by simp [LSeries.term_of_ne_zero one_ne_zero]
      map_mul' := fun m n => by
        rcases eq_or_ne m 0 with rfl | hm
        · simp
        rcases eq_or_ne n 0 with rfl | hn
        · simp
        rw [LSeries.term_of_ne_zero (mul_ne_zero hm hn), LSeries.term_of_ne_zero hm,
          LSeries.term_of_ne_zero hn, map_mul, Nat.cast_mul,
          show ((m : ℂ) * (n : ℂ)) ^ s = (m : ℂ) ^ s * (n : ℂ) ^ s from by
            simpa using Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n) s]
        ring }
  have hfs_sum : Summable fun n => ‖fs n‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) h1n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [fs]
    · show ‖LSeries.term (primeIntMultHom a) s n‖ ≤ ‖LSeries.term (1 : ℕ → ℂ) s n‖
      rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, norm_div, norm_div]
      simp only [Pi.one_apply, norm_one, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (norm_primeIntMultHom_le_one ha n)
        (inv_nonneg.mpr (norm_nonneg ((n : ℂ) ^ s)))
  have hlog_eq : LSeries (primeIntEulerLog a) s =
      ∑' p : Nat.Primes, -Complex.log (1 - fs p) := by
    rw [LSeries, tsum_eq_tsum_primes_of_support_subset_prime_powers
      (lSeriesSummable_primeIntEulerLog ha hs)]
    · refine tsum_congr fun p => ?_
      have hp : (p : ℕ).Prime := p.prop
      have hnorm_lt : ‖fs p‖ < 1 := by
        show ‖LSeries.term (primeIntMultHom a) s p‖ < 1
        rw [LSeries.term_of_ne_zero hp.ne_zero, norm_div,
          Complex.norm_natCast_cpow_of_pos hp.pos]
        have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
        have hgt1 : 1 < (p : ℝ) ^ s.re := Real.one_lt_rpow hp1 (by linarith)
        exact (div_lt_one (zero_lt_one.trans hgt1)).mpr
          ((norm_primeIntMultHom_le_one ha p).trans_lt hgt1)
      have hseries := Complex.hasSum_taylorSeries_neg_log hnorm_lt
      rw [← hseries.tsum_eq, hseries.summable.tsum_eq_zero_add]
      simp only [Nat.cast_zero, div_zero, zero_add]
      refine tsum_congr fun k => ?_
      have hne : (p : ℕ) ^ (k + 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
      show LSeries.term (primeIntEulerLog a) s ((p : ℕ) ^ (k + 1)) =
        fs p ^ (k + 1) / ((k + 1 : ℕ) : ℂ)
      have hfs_pow : fs p ^ (k + 1) = LSeries.term (primeIntMultHom a) s ((p : ℕ) ^ (k + 1)) := by
        rw [← map_pow fs p (k + 1)]; rfl
      rw [hfs_pow, LSeries.term_of_ne_zero hne, LSeries.term_of_ne_zero hne]
      show (primeIntMultHom a ((p : ℕ) ^ (k + 1)) * eulerLogDirichletCoeff ((p : ℕ) ^ (k + 1))) /
          (((p : ℕ) ^ (k + 1) : ℕ) : ℂ) ^ s = _
      rw [eulerLogDirichletCoeff_prime_pow_succ p k hp]
      ring
    · intro n hn
      by_contra hpp
      apply hn
      rcases eq_or_ne n 0 with rfl | hn0
      · simp [LSeries.term_zero]
      · rw [LSeries.term_of_ne_zero hn0]
        show (primeIntMultHom a n * eulerLogDirichletCoeff n) / (n : ℂ) ^ s = 0
        rw [eulerLogDirichletCoeff_eq_zero_of_not_primePower hpp, mul_zero, zero_div]
  rw [hlog_eq, EulerProduct.exp_tsum_primes_log_eq_tsum hfs_sum, LSeries]
  rfl

/-- **Automatic Upgrade to `RHTower.SelbergClass`.** Any degree-one `ExtendedSelbergClass` element
with `F.coeff 1 = 1`, coprime multiplicativity, and `F.coeff (p ^ k) = (a p : ℂ) ^ k` (`a p ∈ ℤ`)
automatically belongs to the full `RHTower.SelbergClass`. -/
theorem exists_full_selberg_of_integral_prime_gates (F : ExtendedSelbergClass)
    (hd : F.gammaData.degree = 1) {a : ℕ → ℤ}
    (h1 : F.coeff 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → F.coeff (m * n) = F.coeff m * F.coeff n)
    (hpow : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, F.coeff (p ^ k) = ((a p : ℤ) : ℂ) ^ k) :
    ∃ G : RHTower.SelbergClass, G.toExtendedSelbergClass = F := by
  have ha : ∀ {p : ℕ}, p.Prime → |a p| ≤ 1 := fun hp =>
    (integral_prime_gate_mem_signs F hd hpow hp).1
  have hcoeff : ∀ n : ℕ, F.coeff n = primeIntMultHom a n :=
    coeff_eq_primeIntMultHom h1 hmul hpow
  have hL_eq : ∀ s : ℂ, LSeries F.coeff s = LSeries (primeIntMultHom a) s := fun s => by
    rw [LSeries, LSeries]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [LSeries.term_of_ne_zero hn, hcoeff n]
  refine ⟨{ toExtendedSelbergClass := F
            coeff_one := h1
            ramanujan := fun ε hε => ⟨1, one_pos, fun n hn => by
              rw [one_mul, hcoeff n]
              have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
              exact (norm_primeIntMultHom_le_one ha n).trans (Real.one_le_rpow hn1 hε.le)⟩
            eulerLogCoeff := primeIntEulerLog a
            eulerLogCoeff_primePower := fun {n} hn => by
              have hpp : IsPrimePow n := by
                by_contra hnot
                apply hn
                show primeIntMultHom a n * eulerLogDirichletCoeff n = 0
                rw [eulerLogDirichletCoeff_eq_zero_of_not_primePower hnot, mul_zero]
              obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hpp
              exact ⟨p, k, hp, hk, rfl⟩
            eulerTheta := 0
            eulerTheta_lt_half := by norm_num
            eulerLogBound := ⟨1, one_pos, fun n _ => by
              simpa using norm_primeIntEulerLog_le_one ha n⟩
            eulerLogSummable := fun _ hs => lSeriesSummable_primeIntEulerLog ha hs
            eulerProduct := fun s hs => by
              rw [exp_lSeries_primeIntEulerLog ha hs, ← hL_eq s, F.lSeries_eq_value s hs] }, rfl⟩

/-! ### Step 3: Vanishing internal shift, quadratic character collapse, and zeta pinning -/

private theorem internalShift_eq_zero_of_integral_primes {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} {θ : ℝ} {a : ℕ → ℤ}
    (ha_prime : ∀ {p : ℕ}, p.Prime → ((a p : ℤ) : ℂ) = χ p * (p : ℂ) ^ (-(I * (θ : ℂ)))) :
    θ = 0 := by
  by_contra hθ
  obtain ⟨p₁, hp₁_ge, hp₁⟩ := Nat.exists_infinite_primes (q + 1)
  obtain ⟨p₂, hp₂_ge, hp₂⟩ := Nat.exists_infinite_primes (p₁ + 1)
  have hp₁_gt : q < p₁ := by omega
  have hp₂_gt : q < p₂ := by omega
  have hp₁₂_ne : p₁ ≠ p₂ := by omega
  set M : ℕ := Fintype.card (ZMod q)ˣ
  have hM_pos : 0 < M := Fintype.card_pos
  have hunit_pow : ∀ {p : ℕ}, p.Prime → q < p →
      ∃ k : ℤ, -((2 * M : ℝ) * θ * Real.log p) = (k : ℝ) * (2 * Real.pi) := by
    intro p hp hgt
    have hndvd : ¬ (p ∣ q) := Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero (NeZero.ne q)) hgt
    have hcop : p.Coprime q := (Nat.Prime.coprime_iff_not_dvd hp).mpr hndvd
    set u : (ZMod q)ˣ := ZMod.unitOfCoprime p hcop
    have hu_coe : (u : ZMod q) = (p : ZMod q) := ZMod.coe_unitOfCoprime p hcop
    have hχ_pow : (χ p) ^ (2 * M) = 1 := by
      rw [← hu_coe, show 2 * M = M * 2 by ring, pow_mul, ← map_pow,
        show (u : ZMod q) ^ M = (((u ^ M : (ZMod q)ˣ) : ZMod q)) from (Units.val_pow_eq_pow_val u M).symm,
        pow_card_eq_one, Units.val_one, map_one, one_pow]
    have hχ_norm : ‖χ p‖ = 1 := by
      rw [← hu_coe]
      exact MulChar.norm_apply_of_isUnit χ u.isUnit
    have ha_eq := ha_prime hp
    have ha_norm : ‖((a p : ℤ) : ℂ)‖ = 1 := by
      rw [ha_eq, norm_mul, hχ_norm, one_mul, Complex.norm_natCast_cpow_of_pos hp.pos]
      simp
    have ha_sq : (a p) ^ 2 = 1 := by
      rw [Complex.norm_intCast] at ha_norm
      have habs : |a p| = 1 := by exact_mod_cast ha_norm
      rcases abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.mp habs with h | h <;> simp [h]
    have ha_pow : (((a p : ℤ) : ℂ)) ^ (2 * M) = 1 := by
      rw [show 2 * M = 2 * M from rfl, pow_mul]
      have hsqC : (((a p : ℤ) : ℂ)) ^ 2 = 1 := by exact_mod_cast ha_sq
      rw [hsqC, one_pow]
    have hexp_eq : ((p : ℂ) ^ (-(I * (θ : ℂ)))) ^ (2 * M) =
        Complex.exp (((-((2 * M : ℝ) * θ * Real.log p) : ℝ) : ℂ) * I) := by
      rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne_zero), ← Complex.natCast_log,
        ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h1 : Complex.exp (((-((2 * M : ℝ) * θ * Real.log p) : ℝ) : ℂ) * I) = 1 := by
      have hp_pow := congrArg (fun z : ℂ => z ^ (2 * M)) ha_eq
      rw [ha_pow, mul_pow, hχ_pow, one_mul, hexp_eq] at hp_pow
      exact hp_pow.symm
    obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h1
    refine ⟨k, ?_⟩
    have him := congrArg Complex.im hk
    simpa [mul_assoc, mul_comm, mul_left_comm] using him
  obtain ⟨k₁, hk₁⟩ := hunit_pow hp₁ hp₁_gt
  obtain ⟨k₂, hk₂⟩ := hunit_pow hp₂ hp₂_gt
  have hlog₁ : 0 < Real.log p₁ := Real.log_pos (by exact_mod_cast hp₁.one_lt)
  have hlog₂ : 0 < Real.log p₂ := Real.log_pos (by exact_mod_cast hp₂.one_lt)
  have hM_R : (0 : ℝ) < 2 * M := by positivity
  have hk₁_ne : k₁ ≠ 0 := by
    intro h0; rw [h0] at hk₁; simp at hk₁
    rcases hk₁ with h | h | h
    · linarith
    · exact hθ h
    · linarith
  have hk₂_ne : k₂ ≠ 0 := by
    intro h0; rw [h0] at hk₂; simp at hk₂
    rcases hk₂ with h | h | h
    · linarith
    · exact hθ h
    · linarith
  set n₁ : ℕ := k₁.natAbs
  set n₂ : ℕ := k₂.natAbs
  have hn₁_pos : 0 < n₁ := Int.natAbs_pos.mpr hk₁_ne
  have hn₂_pos : 0 < n₂ := Int.natAbs_pos.mpr hk₂_ne
  have habs₁ : (2 * M : ℝ) * |θ| * Real.log p₁ = (n₁ : ℝ) * (2 * Real.pi) := by
    have h := congrArg abs hk₁
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos hM_R, abs_of_pos hlog₁,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h
    have hk_abs : |(k₁ : ℝ)| = (n₁ : ℝ) := by
      dsimp only [n₁]
      rw [← Int.cast_abs, ← Int.cast_natCast, Int.natCast_natAbs]
    rwa [hk_abs] at h
  have habs₂ : (2 * M : ℝ) * |θ| * Real.log p₂ = (n₂ : ℝ) * (2 * Real.pi) := by
    have h := congrArg abs hk₂
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos hM_R, abs_of_pos hlog₂,
      abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at h
    have hk_abs : |(k₂ : ℝ)| = (n₂ : ℝ) := by
      dsimp only [n₂]
      rw [← Int.cast_abs, ← Int.cast_natCast, Int.natCast_natAbs]
    rwa [hk_abs] at h
  have hc_pos : 0 < (2 * M : ℝ) * |θ| := mul_pos hM_R (abs_pos.mpr hθ)
  have hlog_cross : (n₂ : ℝ) * Real.log p₁ = (n₁ : ℝ) * Real.log p₂ := by
    have hprod : ((2 * M : ℝ) * |θ|) * ((n₂ : ℝ) * Real.log p₁) =
        ((2 * M : ℝ) * |θ|) * ((n₁ : ℝ) * Real.log p₂) := by
      calc ((2 * M : ℝ) * |θ|) * ((n₂ : ℝ) * Real.log p₁)
          = (n₂ : ℝ) * ((2 * M : ℝ) * |θ| * Real.log p₁) := by ring
        _ = (n₂ : ℝ) * ((n₁ : ℝ) * (2 * Real.pi)) := by rw [habs₁]
        _ = (n₁ : ℝ) * ((n₂ : ℝ) * (2 * Real.pi)) := by ring
        _ = (n₁ : ℝ) * ((2 * M : ℝ) * |θ| * Real.log p₂) := by rw [← habs₂]
        _ = ((2 * M : ℝ) * |θ|) * ((n₁ : ℝ) * Real.log p₂) := by ring
    exact mul_left_cancel₀ hc_pos.ne' hprod
  have hpow_eq_R : ((p₁ ^ n₂ : ℕ) : ℝ) = ((p₂ ^ n₁ : ℕ) : ℝ) := by
    have h1_pos : (0 : ℝ) < ((p₁ ^ n₂ : ℕ) : ℝ) := by exact_mod_cast pow_pos hp₁.pos n₂
    have h2_pos : (0 : ℝ) < ((p₂ ^ n₁ : ℕ) : ℝ) := by exact_mod_cast pow_pos hp₂.pos n₁
    rw [← Real.exp_log h1_pos, ← Real.exp_log h2_pos]
    congr 1
    push_cast
    rw [Real.log_pow, Real.log_pow, hlog_cross]
  have hpow_eq : p₁ ^ n₂ = p₂ ^ n₁ := by exact_mod_cast hpow_eq_R
  have hdvd₁₂ : p₁ ∣ p₂ := by
    have hdvd_pow : p₁ ∣ p₂ ^ n₁ := by
      rw [← hpow_eq]
      exact dvd_pow_self p₁ hn₂_pos.ne'
    exact hp₁.dvd_of_dvd_pow hdvd_pow
  rcases hp₂.eq_one_or_self_of_dvd p₁ hdvd₁₂ with h1' | heq
  · exact hp₁.ne_one h1'
  · exact hp₁₂_ne heq

/-- **Complete Classification of Degree-One Integral Prime-Gate Elements.**
Every `F : ExtendedSelbergClass` of degree `1` with `F.coeff 1 = 1`, coprime multiplicativity,
and `F.coeff (p ^ k) = (a p : ℂ) ^ k` (`a p ∈ ℤ`) satisfies:
1. `a p ∈ {-1, 0, 1}` for every prime `p`;
2. `F.gammaData.internalShift = 0`;
3. `F.gammaData.conductor = q` for a positive integer `q`, and there is a primitive quadratic
   Dirichlet character `χ` modulo `q` (`χ u ∈ {-1, 0, 1}` for all `u : ZMod q`, `χ⁻¹ = χ`) such
   that `F.coeff n = χ n` for all `n ≠ 0` and `F s = L(s, χ)` for all `s ≠ 1`. -/
theorem degreeOne_integral_gate_classification (F : ExtendedSelbergClass)
    (hd : F.gammaData.degree = 1) {a : ℕ → ℤ}
    (h1 : F.coeff 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → F.coeff (m * n) = F.coeff m * F.coeff n)
    (hpow : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, F.coeff (p ^ k) = ((a p : ℤ) : ℂ) ^ k) :
    (∀ {p : ℕ}, p.Prime → a p = -1 ∨ a p = 0 ∨ a p = 1) ∧
    F.gammaData.internalShift = 0 ∧
    ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive ∧
      F.gammaData.conductor = q ∧
      (∀ u : ZMod q, χ u = -1 ∨ χ u = 0 ∨ χ u = 1) ∧
      χ⁻¹ = χ ∧
      (∀ n : ℕ, n ≠ 0 → F.coeff n = χ n) ∧
      (∀ s : ℂ, s ≠ 1 → F s = DirichletCharacter.LFunction χ s) := by
  have ha_signs : ∀ {p : ℕ}, p.Prime → a p = -1 ∨ a p = 0 ∨ a p = 1 :=
    fun hp => (integral_prime_gate_mem_signs F hd hpow hp).2
  have hcoeff_hom : ∀ n : ℕ, F.coeff n = primeIntMultHom a n :=
    coeff_eq_primeIntMultHom h1 hmul hpow
  obtain ⟨G, hGF⟩ := exists_full_selberg_of_integral_prime_gates F hd h1 hmul hpow
  have hGd : G.gammaData.degree = 1 := by rw [← hGF] at hd; exact hd
  obtain ⟨q, hq_ne, χ, hprim, hcond, _, hGcoeff, hGval⟩ := degreeOne_classification G hGd
  haveI : NeZero q := hq_ne
  have hθ0 : F.gammaData.internalShift = 0 := by
    have hθG : G.gammaData.internalShift = F.gammaData.internalShift := by rw [hGF]
    rw [← hθG]
    refine internalShift_eq_zero_of_integral_primes (q := q) (χ := χ) (a := a) ?_
    intro p hp
    have hp1 := hpow hp 1
    rw [pow_one, pow_one, ← hGF] at hp1
    exact hp1.symm.trans (hGcoeff p hp.ne_zero)
  have hFcoeff : ∀ n : ℕ, n ≠ 0 → F.coeff n = χ n := by
    intro n hn
    have hG := hGcoeff n hn
    rw [hGF, hθ0] at hG
    simpa using hG
  have hχ_signs : ∀ u : ZMod q, χ u = -1 ∨ χ u = 0 ∨ χ u = 1 := by
    intro u
    set n : ℕ := u.val + q
    have hn0 : n ≠ 0 := by
      have := Nat.pos_of_ne_zero (NeZero.ne q)
      omega
    have hcast : (n : ZMod q) = u := by
      dsimp only [n]
      push_cast
      simp
    rw [← hcast, ← hFcoeff n hn0, hcoeff_hom n]
    exact primeIntMultHom_mem_signs ha_signs hn0
  have hχ_inv : χ⁻¹ = χ := by
    ext u
    by_cases hu : IsUnit u
    · rw [MulChar.inv_apply_eq_inv]
      rcases hχ_signs u with h | h | h <;> simp [h]
    · rw [MulChar.map_nonunit _ hu, MulChar.map_nonunit _ hu]
  refine ⟨ha_signs, hθ0, q, hq_ne, χ, hprim, ?_, hχ_signs, hχ_inv, hFcoeff, ?_⟩
  · rw [← hGF]; exact hcond
  · intro s hs
    have hv := hGval s hs
    have hGs : G s = F s := by
      change G.toExtendedSelbergClass.continuation.value s = F.continuation.value s
      rw [hGF]
    rw [hGs, hθ0] at hv
    simpa using hv

/-- **Unique Pinning to the Riemann Zeta Function.**
For a degree-one `ExtendedSelbergClass` element with `F.coeff 1 = 1`, coprime multiplicativity,
and integral prime-power coefficients `F.coeff (p ^ k) = (a p : ℂ) ^ k` (`a p ∈ ℤ`), the
following are equivalent:
1. `F.gammaData.conductor = 1`;
2. `F` has a pole at `s = 1` (`meromorphicOrderAt F 1 < 0`);
3. `a p = 1` for every prime `p` (equivalently `F s = riemannZeta s` for all `s ≠ 1`). -/
theorem degreeOne_integral_gate_eq_zeta_iff (F : ExtendedSelbergClass)
    (hd : F.gammaData.degree = 1) {a : ℕ → ℤ}
    (h1 : F.coeff 1 = 1)
    (hmul : ∀ {m n : ℕ}, m ≠ 0 → n ≠ 0 → m.Coprime n → F.coeff (m * n) = F.coeff m * F.coeff n)
    (hpow : ∀ {p : ℕ}, p.Prime → ∀ k : ℕ, F.coeff (p ^ k) = ((a p : ℤ) : ℂ) ^ k) :
    (F.gammaData.conductor = 1 ↔ meromorphicOrderAt F 1 < 0) ∧
    (F.gammaData.conductor = 1 →
      meromorphicOrderAt F 1 = ((-1 : ℤ) : WithTop ℤ) ∧
      (∀ {p : ℕ}, p.Prime → a p = 1) ∧ ∀ s : ℂ, s ≠ 1 → F s = riemannZeta s) := by
  obtain ⟨_, _, q, hq_ne, χ, hprim, hcond, _, _, hFcoeff, hFval⟩ :=
    degreeOne_integral_gate_classification F hd h1 hmul hpow
  haveI : NeZero q := hq_ne
  have hq_one_imp : F.gammaData.conductor = 1 →
      meromorphicOrderAt F 1 = ((-1 : ℤ) : WithTop ℤ) ∧
        (∀ {p : ℕ}, p.Prime → a p = 1) ∧
        ∀ s : ℂ, s ≠ 1 → F s = riemannZeta s := by
    intro hcond1
    have hq1 : q = 1 := by
      have : (q : ℝ) = 1 := hcond.symm.trans hcond1
      exact_mod_cast this
    subst hq1
    have hχ1 : χ = 1 := Subsingleton.elim _ _
    have hzeta : ∀ s : ℂ, s ≠ 1 → F s = riemannZeta s := by
      intro s hs
      rw [hFval s hs, hχ1, DirichletCharacter.LFunction_modOne_eq]
    have hpole : meromorphicOrderAt F 1 = ((-1 : ℤ) : WithTop ℤ) := by
      have hev : (F : ℂ → ℂ) =ᶠ[𝓝[≠] (1 : ℂ)]
          fun s : ℂ => RHTower.zetaPoleUnit s * (s - 1)⁻¹ := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
        rw [hzeta s hs, RHTower.zetaPoleUnit_of_ne hs]
        field_simp [hs1]
      rw [meromorphicOrderAt_congr hev,
        meromorphicOrderAt_mul_of_ne_zero (RHTower.differentiable_zetaPoleUnit.analyticAt 1)
          (by rw [RHTower.zetaPoleUnit_one]; exact one_ne_zero),
        meromorphicOrderAt_inv]
      have hlin : meromorphicOrderAt (fun s : ℂ => s - 1) 1 = ((1 : ℤ) : WithTop ℤ) := by
        have han : AnalyticAt ℂ (fun s : ℂ => s - 1) 1 := by fun_prop
        rw [han.meromorphicOrderAt_eq]
        have hd : HasDerivAt (fun s : ℂ => s - 1) 1 1 := (hasDerivAt_id 1).sub_const 1
        have hord1 : analyticOrderAt (fun s : ℂ => s - 1) 1 = 1 := by
          rw [han.analyticOrderAt_eq_one_iff]
          exact ⟨by simp, by rw [hd.deriv]; exact one_ne_zero⟩
        simp [hord1]
      rw [hlin]
      rfl
    refine ⟨hpole, ?_, hzeta⟩
    intro p hp
    have hp1 := (hpow hp 1).symm.trans (hFcoeff p hp.ne_zero)
    rw [pow_one, pow_one, hχ1] at hp1
    have hone_mod : (p : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [hone_mod, map_one] at hp1
    exact_mod_cast hp1.symm
  refine ⟨⟨fun hc => by rw [(hq_one_imp hc).1]; decide, fun hpole => ?_⟩, hq_one_imp⟩
  by_contra hne1
  have hq_ne1 : q ≠ 1 := fun h => hne1 (by rw [hcond, h]; norm_num)
  have hχ_ne1 : χ ≠ 1 := by
    intro h
    apply hq_ne1
    have hc := (DirichletCharacter.isPrimitive_def χ).mp hprim
    rw [h, DirichletCharacter.conductor_one] at hc
    exact hc.symm
  have han : AnalyticAt ℂ (DirichletCharacter.LFunction χ) 1 :=
    (DirichletCharacter.differentiable_LFunction hχ_ne1).analyticAt 1
  have hev : (F : ℂ → ℂ) =ᶠ[𝓝[≠] (1 : ℂ)] DirichletCharacter.LFunction χ := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact hFval s hs
  have hord_eq : meromorphicOrderAt F 1 = meromorphicOrderAt (DirichletCharacter.LFunction χ) 1 :=
    meromorphicOrderAt_congr hev
  rw [hord_eq] at hpole
  exact not_lt_of_ge han.meromorphicOrderAt_nonneg hpole

#print axioms integral_prime_gate_mem_signs
#print axioms exists_full_selberg_of_integral_prime_gates
#print axioms degreeOne_integral_gate_classification
#print axioms degreeOne_integral_gate_eq_zeta_iff

end GaloisForLFunctions.SelbergClass.DegreeOne
