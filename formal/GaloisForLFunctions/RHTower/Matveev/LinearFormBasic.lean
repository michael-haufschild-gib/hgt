import GaloisForLFunctions.HTGeometry.WeldRateLattice

/-!
# Linear forms in prime logarithms: the statement and the elementary bound

A linear form `Λ(ν) = Σ νᵢ log pᵢ` with integer coefficients in the logarithms of distinct primes is
the logarithm of a ratio of `S`-units,

`Λ(ν) = log N − log M`,   `N = ∏_{νᵢ>0} pᵢ^{νᵢ}`,  `M = ∏_{νᵢ<0} pᵢ^{−νᵢ}`.

Unique factorization makes `Λ(ν) = 0` only for `ν = 0`, hence `N ≠ M` whenever `ν ≠ 0`, and the
elementary inequality `log t ≥ 1 − t⁻¹` then gives

`|Λ(ν)| ≥ max(N,M)⁻¹ ≥ Q^{−|ν|₁}`,   `Q = max(2, max pᵢ)`.

That is the Liouville-type baseline: exponential in the height.  The effective Baker–Matveev bound
asserts the far stronger *polynomial* estimate `|Λ(ν)| ≥ c(2+|ν|₁)^{−C}`; this file records its
statement together with the reduction that only large heights need be treated, small heights being
covered by the baseline with no finiteness argument.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset

variable {d : ℕ}

/-! ## The form, its height, and the prime bound -/

/-- The linear form in prime logarithms with integer coefficients. -/
def primeLogForm (p : Fin d → ℕ) (ν : Fin d → ℤ) : ℝ := ∑ i, (ν i : ℝ) * Real.log (p i)

/-- The `ℓ¹` height of an integer coefficient vector. -/
def coeffHeight (ν : Fin d → ℤ) : ℕ := ∑ i, (ν i).natAbs

/-- A bound for the primes of the family, at least two. -/
def primeBound (p : Fin d → ℕ) : ℕ := max 2 (Finset.univ.sup p)

theorem two_le_primeBound (p : Fin d → ℕ) : 2 ≤ primeBound p := le_max_left _ _

theorem le_primeBound (p : Fin d → ℕ) (i : Fin d) : p i ≤ primeBound p :=
  le_trans (Finset.le_sup (Finset.mem_univ i)) (le_max_right _ _)

/-! ## Nonvanishing from unique factorization -/

set_option maxHeartbeats 1000000 in
/-- Prime logarithms of an injective prime family are `ℤ`-linearly independent. -/
theorem primeLog_linearIndependent_fin (p : Fin d → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) :
    LinearIndependent ℤ (fun i : Fin d => Real.log (p i)) := by
  have hP : Function.Injective (fun i : Fin d => (⟨p i, hprime i⟩ : Nat.Primes)) := by
    intro i j hij
    exact hp (congrArg Subtype.val hij)
  have hfun : (fun q : Nat.Primes => Real.log ((q : ℕ) : ℝ)) ∘
      (fun i : Fin d => (⟨p i, hprime i⟩ : Nat.Primes))
      = fun i : Fin d => Real.log ((p i : ℕ) : ℝ) := rfl
  rw [← hfun]
  exact _root_.GaloisForLFunctions.RHTower.primeLog_linearIndependent.comp
    (fun i : Fin d => (⟨p i, hprime i⟩ : Nat.Primes)) hP

/-- **Unique factorization.**  The form vanishes only at the zero coefficient vector. -/
theorem primeLogForm_eq_zero_iff (p : Fin d → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) (ν : Fin d → ℤ) :
    primeLogForm p ν = 0 ↔ ν = 0 := by
  constructor
  · intro h
    have hli := primeLog_linearIndependent_fin p hp hprime
    rw [Fintype.linearIndependent_iff] at hli
    have hsum : ∑ i, ν i • Real.log (p i) = 0 := by
      simpa [zsmul_eq_mul, primeLogForm] using h
    funext i
    exact hli ν hsum i
  · intro h
    subst h
    simp [primeLogForm]

/-! ## The `S`-unit decomposition -/

/-- The numerator `S`-unit of the form. -/
def numerPart (p : Fin d → ℕ) (ν : Fin d → ℤ) : ℕ :=
  ∏ i ∈ Finset.univ.filter (fun i => 0 < ν i), p i ^ (ν i).toNat

/-- The denominator `S`-unit of the form. -/
def denomPart (p : Fin d → ℕ) (ν : Fin d → ℤ) : ℕ :=
  ∏ i ∈ Finset.univ.filter (fun i => ν i < 0), p i ^ (-(ν i)).toNat

theorem numerPart_pos (p : Fin d → ℕ) (hprime : ∀ i, (p i).Prime) (ν : Fin d → ℤ) :
    0 < numerPart p ν :=
  Finset.prod_pos fun i _ => pow_pos (hprime i).pos _

theorem denomPart_pos (p : Fin d → ℕ) (hprime : ∀ i, (p i).Prime) (ν : Fin d → ℤ) :
    0 < denomPart p ν :=
  Finset.prod_pos fun i _ => pow_pos (hprime i).pos _

/-- The logarithm of a product of prime powers is the corresponding sum. -/
theorem log_prod_pow (p : Fin d → ℕ) (hprime : ∀ i, (p i).Prime) (s : Finset (Fin d))
    (e : Fin d → ℕ) :
    Real.log ((∏ i ∈ s, p i ^ e i : ℕ) : ℝ) = ∑ i ∈ s, (e i : ℝ) * Real.log (p i) := by
  push_cast
  rw [Real.log_prod]
  · exact Finset.sum_congr rfl fun i _ => by rw [Real.log_pow]
  · intro i _
    have hpos : (0 : ℝ) < (p i : ℝ) ^ e i := by
      have := (hprime i).pos
      positivity
    exact hpos.ne'

/-- **The `S`-unit decomposition of the form.** -/
theorem primeLogForm_eq_log_sub (p : Fin d → ℕ) (hprime : ∀ i, (p i).Prime) (ν : Fin d → ℤ) :
    primeLogForm p ν
      = Real.log (numerPart p ν) - Real.log (denomPart p ν) := by
  classical
  set spos : Finset (Fin d) := Finset.univ.filter (fun i => 0 < ν i) with hspos
  set sneg : Finset (Fin d) := Finset.univ.filter (fun i => ν i < 0) with hsneg
  have hdisj : Disjoint spos sneg := by
    refine Finset.disjoint_left.mpr fun i hi hj => ?_
    rw [hspos, Finset.mem_filter] at hi
    rw [hsneg, Finset.mem_filter] at hj
    omega
  have hsplit : ∑ i ∈ spos ∪ sneg, (ν i : ℝ) * Real.log (p i)
      = ∑ i, (ν i : ℝ) * Real.log (p i) := by
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
    have hzero : ν i = 0 := by
      by_contra hne
      apply hi
      rcases lt_or_gt_of_ne hne with h | h
      · refine Finset.mem_union_right _ ?_
        rw [hsneg, Finset.mem_filter]
        exact ⟨Finset.mem_univ i, h⟩
      · refine Finset.mem_union_left _ ?_
        rw [hspos, Finset.mem_filter]
        exact ⟨Finset.mem_univ i, h⟩
    rw [hzero]
    simp
  have hunion : ∑ i ∈ spos ∪ sneg, (ν i : ℝ) * Real.log (p i)
      = (∑ i ∈ spos, (ν i : ℝ) * Real.log (p i)) + ∑ i ∈ sneg, (ν i : ℝ) * Real.log (p i) :=
    Finset.sum_union hdisj
  have hnum : Real.log (numerPart p ν) = ∑ i ∈ spos, (ν i : ℝ) * Real.log (p i) := by
    rw [numerPart, ← hspos, log_prod_pow p hprime spos (fun i => (ν i).toNat)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hspos, Finset.mem_filter] at hi
    have hcast : (((ν i).toNat : ℕ) : ℝ) = ((ν i : ℤ) : ℝ) := by
      have := Int.toNat_of_nonneg hi.2.le
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    rw [hcast]
  have hden : Real.log (denomPart p ν)
      = ∑ i ∈ sneg, (-(ν i) : ℝ) * Real.log (p i) := by
    rw [denomPart, ← hsneg, log_prod_pow p hprime sneg (fun i => (-(ν i)).toNat)]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hsneg, Finset.mem_filter] at hi
    have hnn : (0 : ℤ) ≤ -(ν i) := by omega
    have hcast : ((((-(ν i)).toNat : ℕ)) : ℝ) = ((-(ν i) : ℤ) : ℝ) := by
      have := Int.toNat_of_nonneg hnn
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) this
    rw [hcast]
    push_cast
    ring
  have hnegsum : (∑ i ∈ sneg, (-(ν i) : ℝ) * Real.log (p i))
      + (∑ i ∈ sneg, (ν i : ℝ) * Real.log (p i)) = 0 := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun i _ => by ring
  rw [primeLogForm, ← hsplit, hunion, hnum, hden]
  linarith

/-! ## The Liouville baseline -/

/-- `log t ≥ 1 − t⁻¹` for `t > 0`. -/
theorem one_sub_inv_le_log {t : ℝ} (ht : 0 < t) : 1 - t⁻¹ ≤ Real.log t := by
  have h := Real.add_one_le_exp (-Real.log t)
  rw [Real.exp_neg, Real.exp_log ht] at h
  linarith

/-- A ratio bound feeding the Liouville estimate: for positive integers `a > b` one has
`log a − log b ≥ a⁻¹`. -/
theorem inv_le_log_sub_log {a b : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : b + 1 ≤ a) :
    a⁻¹ ≤ Real.log a - Real.log b := by
  have hapos : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have hbpos : (0 : ℝ) < b := lt_of_lt_of_le one_pos hb
  have h1 := one_sub_inv_le_log (t := a / b) (by positivity)
  rw [Real.log_div hapos.ne' hbpos.ne'] at h1
  have h2 : (a / b)⁻¹ ≤ 1 - a⁻¹ := by
    rw [inv_div, div_le_iff₀ hapos]
    have hcancel : a⁻¹ * a = 1 := inv_mul_cancel₀ hapos.ne'
    nlinarith [hab, hcancel]
  linarith

/-- **The Liouville baseline.**  A nonzero form is at least the reciprocal of the larger of its two
`S`-units. -/
theorem inv_max_le_abs_primeLogForm (p : Fin d → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) (ν : Fin d → ℤ) (hν : ν ≠ 0) :
    ((max (numerPart p ν) (denomPart p ν) : ℕ) : ℝ)⁻¹ ≤ |primeLogForm p ν| := by
  have hN : 0 < numerPart p ν := numerPart_pos p hprime ν
  have hM : 0 < denomPart p ν := denomPart_pos p hprime ν
  have hNR : (1 : ℝ) ≤ (numerPart p ν : ℝ) := by exact_mod_cast hN
  have hMR : (1 : ℝ) ≤ (denomPart p ν : ℝ) := by exact_mod_cast hM
  have hdec := primeLogForm_eq_log_sub p hprime ν
  have hne : primeLogForm p ν ≠ 0 := fun h => hν ((primeLogForm_eq_zero_iff p hp hprime ν).mp h)
  rcases lt_trichotomy (numerPart p ν) (denomPart p ν) with hlt | heq | hgt
  · have hmax : max (numerPart p ν) (denomPart p ν) = denomPart p ν := max_eq_right hlt.le
    have hstep : (numerPart p ν : ℝ) + 1 ≤ (denomPart p ν : ℝ) := by exact_mod_cast hlt
    have hkey := inv_le_log_sub_log hMR hNR hstep
    have hinvnn : (0 : ℝ) ≤ ((denomPart p ν : ℕ) : ℝ)⁻¹ := by positivity
    have hnonpos : primeLogForm p ν ≤ 0 := by rw [hdec]; linarith
    rw [hmax, abs_of_nonpos hnonpos, hdec]
    linarith
  · exact absurd (by rw [hdec, heq]; ring) hne
  · have hmax : max (numerPart p ν) (denomPart p ν) = numerPart p ν := max_eq_left hgt.le
    have hstep : (denomPart p ν : ℝ) + 1 ≤ (numerPart p ν : ℝ) := by exact_mod_cast hgt
    have hkey := inv_le_log_sub_log hNR hMR hstep
    have hinvnn : (0 : ℝ) ≤ ((numerPart p ν : ℕ) : ℝ)⁻¹ := by positivity
    have hnonneg : 0 ≤ primeLogForm p ν := by rw [hdec]; linarith
    rw [hmax, abs_of_nonneg hnonneg, hdec]
    linarith

/-! ## Size of the `S`-units -/

theorem numerPart_le_pow (p : Fin d → ℕ) (ν : Fin d → ℤ) :
    numerPart p ν ≤ primeBound p ^ coeffHeight ν := by
  classical
  have h1 : numerPart p ν
      ≤ ∏ i ∈ Finset.univ.filter (fun i => 0 < ν i), primeBound p ^ (ν i).toNat :=
    Finset.prod_le_prod' fun i _ => Nat.pow_le_pow_left (le_primeBound p i) _
  have h2 : ∏ i ∈ Finset.univ.filter (fun i => 0 < ν i), primeBound p ^ (ν i).toNat
      = primeBound p ^ ∑ i ∈ Finset.univ.filter (fun i => 0 < ν i), (ν i).toNat :=
    Finset.prod_pow_eq_pow_sum _ _ _
  have h3 : ∑ i ∈ Finset.univ.filter (fun i => 0 < ν i), (ν i).toNat ≤ coeffHeight ν := by
    rw [coeffHeight]
    calc ∑ i ∈ Finset.univ.filter (fun i => 0 < ν i), (ν i).toNat
        ≤ ∑ i ∈ Finset.univ.filter (fun i => 0 < ν i), (ν i).natAbs :=
          Finset.sum_le_sum fun i _ => by omega
      _ ≤ ∑ i, (ν i).natAbs :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [h2] at h1
  refine h1.trans (Nat.pow_le_pow_right ?_ h3)
  have := two_le_primeBound p
  omega

theorem denomPart_le_pow (p : Fin d → ℕ) (ν : Fin d → ℤ) :
    denomPart p ν ≤ primeBound p ^ coeffHeight ν := by
  classical
  have h1 : denomPart p ν
      ≤ ∏ i ∈ Finset.univ.filter (fun i => ν i < 0), primeBound p ^ (-(ν i)).toNat :=
    Finset.prod_le_prod' fun i _ => Nat.pow_le_pow_left (le_primeBound p i) _
  have h2 : ∏ i ∈ Finset.univ.filter (fun i => ν i < 0), primeBound p ^ (-(ν i)).toNat
      = primeBound p ^ ∑ i ∈ Finset.univ.filter (fun i => ν i < 0), (-(ν i)).toNat :=
    Finset.prod_pow_eq_pow_sum _ _ _
  have h3 : ∑ i ∈ Finset.univ.filter (fun i => ν i < 0), (-(ν i)).toNat ≤ coeffHeight ν := by
    rw [coeffHeight]
    calc ∑ i ∈ Finset.univ.filter (fun i => ν i < 0), (-(ν i)).toNat
        ≤ ∑ i ∈ Finset.univ.filter (fun i => ν i < 0), (ν i).natAbs :=
          Finset.sum_le_sum fun i _ => by omega
      _ ≤ ∑ i, (ν i).natAbs :=
          Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [h2] at h1
  refine h1.trans (Nat.pow_le_pow_right ?_ h3)
  have := two_le_primeBound p
  omega

/-- **The Liouville baseline in the height.**  The elementary lower bound is exponential in the
`ℓ¹` height. -/
theorem inv_pow_le_abs_primeLogForm (p : Fin d → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) (ν : Fin d → ℤ) (hν : ν ≠ 0) :
    ((primeBound p : ℝ) ^ coeffHeight ν)⁻¹ ≤ |primeLogForm p ν| := by
  refine le_trans ?_ (inv_max_le_abs_primeLogForm p hp hprime ν hν)
  have hmaxle : max (numerPart p ν) (denomPart p ν) ≤ primeBound p ^ coeffHeight ν :=
    max_le (numerPart_le_pow p ν) (denomPart_le_pow p ν)
  have hmaxR : ((max (numerPart p ν) (denomPart p ν) : ℕ) : ℝ)
      ≤ ((primeBound p ^ coeffHeight ν : ℕ) : ℝ) := by exact_mod_cast hmaxle
  have hposmax : (0 : ℝ) < ((max (numerPart p ν) (denomPart p ν) : ℕ) : ℝ) := by
    have : 0 < max (numerPart p ν) (denomPart p ν) :=
      lt_of_lt_of_le (numerPart_pos p hprime ν) (le_max_left _ _)
    exact_mod_cast this
  have hcast : ((primeBound p ^ coeffHeight ν : ℕ) : ℝ)
      = (primeBound p : ℝ) ^ coeffHeight ν := by push_cast; ring
  have hgoal := one_div_le_one_div_of_le hposmax hmaxR
  rw [one_div, one_div] at hgoal
  rw [← hcast]
  exact hgoal

/-! ## The effective statement and the large-height reduction -/

/-- **The effective Baker–Matveev bound** for a fixed prime family: a *polynomial*, rather than
exponential, lower bound in the `ℓ¹` height. -/
def EffectiveBakerBound (p : Fin d → ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ν : Fin d → ℤ, ν ≠ 0 →
    c * (2 + (coeffHeight ν : ℝ)) ^ (-C) ≤ |primeLogForm p ν|

/-- **Only large heights matter.**  Below any fixed height the Liouville baseline already gives a
uniform positive constant, and shrinking `c` absorbs it; so the effective bound follows from its
restriction to heights at least `B₀`. -/
theorem effectiveBakerBound_of_large (p : Fin d → ℕ) (hp : Function.Injective p)
    (hprime : ∀ i, (p i).Prime) (B₀ : ℕ) {c₀ C : ℝ} (hc₀ : 0 < c₀) (hC : 0 < C)
    (h : ∀ ν : Fin d → ℤ, ν ≠ 0 → B₀ ≤ coeffHeight ν →
      c₀ * (2 + (coeffHeight ν : ℝ)) ^ (-C) ≤ |primeLogForm p ν|) :
    EffectiveBakerBound p := by
  have hQ : (2 : ℝ) ≤ (primeBound p : ℝ) := by exact_mod_cast two_le_primeBound p
  have hQpos : (0 : ℝ) < (primeBound p : ℝ) := by linarith
  set c₁ : ℝ := ((primeBound p : ℝ) ^ B₀)⁻¹ * (2 : ℝ) ^ C with hc₁def
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    have h2C : (0 : ℝ) < (2 : ℝ) ^ C := Real.rpow_pos_of_pos (by norm_num) C
    have : (0 : ℝ) < ((primeBound p : ℝ) ^ B₀)⁻¹ := by positivity
    positivity
  refine ⟨min c₀ c₁, C, lt_min hc₀ hc₁, hC, fun ν hν => ?_⟩
  have hheight : (0 : ℝ) ≤ (coeffHeight ν : ℝ) := Nat.cast_nonneg _
  have hbase : (2 : ℝ) ≤ 2 + (coeffHeight ν : ℝ) := by linarith
  have hbasepos : (0 : ℝ) < 2 + (coeffHeight ν : ℝ) := by linarith
  have hrpownn : (0 : ℝ) < (2 + (coeffHeight ν : ℝ)) ^ (-C) :=
    Real.rpow_pos_of_pos hbasepos _
  rcases le_or_gt B₀ (coeffHeight ν) with hbig | hsmall
  · refine le_trans ?_ (h ν hν hbig)
    exact mul_le_mul_of_nonneg_right (min_le_left _ _) hrpownn.le
  · -- below the threshold the Liouville baseline suffices
    have hpowle : (2 : ℝ) ^ C ≤ (2 + (coeffHeight ν : ℝ)) ^ C :=
      Real.rpow_le_rpow (by norm_num) hbase hC.le
    have hneg : (2 + (coeffHeight ν : ℝ)) ^ (-C) = ((2 + (coeffHeight ν : ℝ)) ^ C)⁻¹ :=
      Real.rpow_neg hbasepos.le C
    have h2Cpos : (0 : ℝ) < (2 : ℝ) ^ C := Real.rpow_pos_of_pos (by norm_num) C
    have hprod : (2 : ℝ) ^ C * (2 + (coeffHeight ν : ℝ)) ^ (-C) ≤ 1 := by
      rw [hneg]
      rw [mul_inv_le_iff₀ (Real.rpow_pos_of_pos hbasepos C), one_mul]
      exact hpowle
    have hQle : ((primeBound p : ℝ) ^ coeffHeight ν)⁻¹ ≤ |primeLogForm p ν| :=
      inv_pow_le_abs_primeLogForm p hp hprime ν hν
    have hpowmono : (primeBound p : ℝ) ^ coeffHeight ν ≤ (primeBound p : ℝ) ^ B₀ :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have hinvmono : ((primeBound p : ℝ) ^ B₀)⁻¹ ≤ ((primeBound p : ℝ) ^ coeffHeight ν)⁻¹ := by
      have hmono := one_div_le_one_div_of_le
        (show (0 : ℝ) < (primeBound p : ℝ) ^ coeffHeight ν by positivity) hpowmono
      rw [one_div, one_div] at hmono
      exact hmono
    have hfinal : min c₀ c₁ * (2 + (coeffHeight ν : ℝ)) ^ (-C)
        ≤ ((primeBound p : ℝ) ^ B₀)⁻¹ := by
      have hstep : min c₀ c₁ * (2 + (coeffHeight ν : ℝ)) ^ (-C)
          ≤ c₁ * (2 + (coeffHeight ν : ℝ)) ^ (-C) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hrpownn.le
      refine hstep.trans ?_
      rw [hc₁def, mul_assoc]
      have hnn : (0 : ℝ) ≤ ((primeBound p : ℝ) ^ B₀)⁻¹ := by positivity
      calc ((primeBound p : ℝ) ^ B₀)⁻¹ * ((2 : ℝ) ^ C * (2 + (coeffHeight ν : ℝ)) ^ (-C))
          ≤ ((primeBound p : ℝ) ^ B₀)⁻¹ * 1 := mul_le_mul_of_nonneg_left hprod hnn
        _ = ((primeBound p : ℝ) ^ B₀)⁻¹ := by ring
    exact hfinal.trans (hinvmono.trans hQle)

end GaloisForLFunctions.RHTower.Matveev
