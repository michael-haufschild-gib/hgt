import GaloisForLFunctions.WorldsOfTheZeroConfiguration.ThinAdditionsKeepTheCountRate
import GaloisForLFunctions.RHTower.BeurlingDeletionEulerProduct

/-!
# Two-sided edits of the rational primes

An **edit** is a sign function `e : ℕ → {−1, 0, 1}` supported on the primes (`IsEdit`).  Its
system (`editSystem`) is the rational primes with the primes of `e = −1` deleted and the primes of
`e = +1` doubled: a second generator of the same norm.

* **Euler product** (`editSystem_zetaSeriesC`).  On `Re s > 1`,
  `ζ_B(s) = ζ(s) exp(E(s) + Q(s))` with `E(s) = Σ_p e(p) p^{−s}` and
  `Q(s) = Σ_p e(p) (−log(1 − p^{−s}) − p^{−s})`; `Q` is holomorphic on `Re s > 1/2`
  (`differentiableOn_editRem`).
* **Count** (`editSystem_count`).  If `Σ_p |e(p)| p^{−β} < ∞`, `0 < β < 1`, then
  `N_B(x) = A x + O(x^β)`: Rankin's bound for the deletions, and the doubled primes are a thin
  addition.
* **Not the primes** (`notNormEquivPrimes_editSystem`).  An edit with one edited prime is not
  norm-equivalent to the rational primes.
-/

open Complex Finset Filter Topology
open RHTower RHTower.BeurlingDeletion RHTower.BeurlingDeletion.DeletionData
open GaloisForLFunctions.RigidArithmeticOfCuts
open GaloisForLFunctions.SumProductArithmeticOfTheLogarithm

noncomputable section

namespace GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits

open ThinAdditions

/-- A two-sided edit of the primes: signs in `{−1, 0, 1}` supported on the primes. -/
structure IsEdit (e : ℕ → ℤ) : Prop where
  prime : ∀ k, ¬ k.Prime → e k = 0
  range : ∀ k, e k = 1 ∨ e k = -1 ∨ e k = 0

/-- The doubled primes. -/
def plusSet (e : ℕ → ℤ) : Set ℕ := {k | e k = 1}

/-- The deleted primes. -/
def minusSet (e : ℕ → ℤ) : Set ℕ := {k | e k = -1}

/-- The system of an edit: the primes of `minusSet` deleted, the primes of `plusSet` doubled. -/
def editSystem (e : ℕ → ℤ) : BeurlingSystem :=
  sumSystem (keptPrimeSystem (minusSet e)) (keptPrimeSystem (plusSet e)ᶜ)

theorem IsEdit.abs_le_one {e : ℕ → ℤ} (he : IsEdit e) (k : ℕ) : |(e k : ℝ)| ≤ 1 := by
  rcases he.range k with h | h | h <;> rw [h] <;> simp

theorem IsEdit.norm_le_one {e : ℕ → ℤ} (he : IsEdit e) (k : ℕ) : ‖(e k : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_intCast]
  exact he.abs_le_one k

theorem hasIntegerNorms_editSystem (e : ℕ → ℤ) : HasIntegerNorms (editSystem e) :=
  hasIntegerNorms_sumSystem (hasIntegerNorms_keptPrimeSystem _) (hasIntegerNorms_keptPrimeSystem _)

theorem isDiscrete_editSystem (e : ℕ → ℤ) : (editSystem e).IsDiscrete :=
  isDiscrete_sumSystem (isDiscrete_keptPrimeSystem _) (isDiscrete_keptPrimeSystem _)

/-- An edit with an edited prime is not norm-equivalent to the rational primes: a doubled prime
is the norm of two generators, a deleted prime of none. -/
theorem notNormEquivPrimes_editSystem {e : ℕ → ℤ} (he : IsEdit e) {p : ℕ} (hp : e p ≠ 0) :
    NotNormEquivPrimes (editSystem e) := by
  have hpp : p.Prime := by
    by_contra h
    exact hp (he.prime p h)
  rintro ⟨⟨φ, hφ⟩⟩
  rcases he.range p with h | h | h
  · -- a doubled prime
    have hm : p ∉ minusSet e := fun hm => by
      have hm' : e p = -1 := hm
      rw [h] at hm'
      norm_num at hm'
    have hpl : p ∉ (plusSet e)ᶜ := fun hc => hc h
    set l₁ : (editSystem e).Label := Sum.inl ⟨p, hpp, hm⟩ with hl₁
    set l₂ : (editSystem e).Label := Sum.inr ⟨p, hpp, hpl⟩ with hl₂
    have h1 : ((φ l₁ : ℕ) : ℝ) = p := (hφ l₁).symm
    have h2 : ((φ l₂ : ℕ) : ℝ) = p := (hφ l₂).symm
    have h12 : φ l₁ = φ l₂ := Subtype.ext (by exact_mod_cast h1.trans h2.symm)
    have hl : l₁ = l₂ := φ.injective h12
    rw [hl₁, hl₂] at hl
    exact Sum.inl_ne_inr hl
  · -- a deleted prime
    set l : (editSystem e).Label := φ.symm ⟨p, hpp⟩ with hl
    have hnorm : (editSystem e).labelNorm l = p := by
      rw [hφ l, hl, φ.apply_symm_apply]
    rcases l with ⟨q, hq, hqm⟩ | ⟨q, hq, hqp⟩
    · have hqp' : (q : ℝ) = p := hnorm
      have hqe : q = p := by exact_mod_cast hqp'
      exact hqm (hqe ▸ h)
    · have hqp' : (q : ℝ) = p := hnorm
      have hqe : q = p := by exact_mod_cast hqp'
      have hmem : p ∈ plusSet e := by
        by_contra hc
        exact hqp (hqe ▸ hc)
      have hmem' : e p = 1 := hmem
      rw [h] at hmem'
      norm_num at hmem'
  · exact hp h

/-! ## The Euler product of the kept primes -/

/-- The completely multiplicative summand `1_{S-free}(n) n^{−s}`. -/
def keptHom (S : Set ℕ) (s : ℂ) : ℕ →*₀ ℂ where
  toFun n := (sFreeR S n : ℂ) * (n : ℂ) ^ (-s)
  map_zero' := by simp [sFreeR_zero]
  map_one' := by simp [sFreeR_one]
  map_mul' m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp [sFreeR_zero]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [sFreeR_zero]
    rw [sFreeR_mul _ hm hn, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    push_cast
    ring

theorem keptHom_apply (S : Set ℕ) (s : ℂ) (n : ℕ) :
    keptHom S s n = (sFreeR S n : ℂ) * (n : ℂ) ^ (-s) := rfl

theorem summable_norm_keptHom (S : Set ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun n => ‖keptHom S s n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    (Real.summable_nat_rpow.mpr (show -s.re < -1 by linarith))
  rw [keptHom_apply, norm_mul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [sFreeR_zero, Real.zero_rpow (show -s.re ≠ 0 by linarith)]
  · rw [norm_natCast_cpow_neg n hn, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) (abs_sFreeR_le S n)

/-- **Euler product of the kept primes.**  `Σ_{n S-free} n^{−s} = exp(Σ_{p ∉ S} −log(1 − p^{−s}))`
on `Re s > 1`. -/
theorem LSeries_sFreeR_eq_exp (S : Set ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (sFreeR S n : ℂ)) s =
      Complex.exp (∑' p : Nat.Primes, (1 - S.indicator (fun _ => (1 : ℂ)) (p : ℕ)) *
        -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))) := by
  classical
  have h1 : LSeries (fun n => (sFreeR S n : ℂ)) s = ∑' n, keptHom S s n := by
    unfold LSeries
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn.ne', keptHom_apply, div_eq_mul_inv, Complex.cpow_neg]
  rw [h1, ← EulerProduct.exp_tsum_primes_log_eq_tsum (summable_norm_keptHom S hs)]
  congr 1
  refine tsum_congr fun p => ?_
  rw [keptHom_apply, sFreeR_prime S p.2, Set.indicator_apply]
  by_cases h : (p : ℕ) ∈ S
  · simp [h]
  · simp [h]

/-! ## The Euler product of an edit -/

/-- The prime-power remainder `Q(s) = Σ_p e(p) (−log(1 − p^{−s}) − p^{−s})` of an edit. -/
def editRem (e : ℕ → ℤ) (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (e p : ℂ) * logRem (((p : ℕ) : ℂ) ^ (-s))

theorem norm_edit_mul_logRem_le {e : ℕ → ℤ} (he : IsEdit e) (p : Nat.Primes) {a : ℝ}
    (ha : 1 / 2 ≤ a) {s : ℂ} (hs : a ≤ s.re) :
    ‖(e p : ℂ) * logRem (((p : ℕ) : ℂ) ^ (-s))‖ ≤
      ((p : ℕ) : ℝ) ^ (-(2 * a)) * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ / 2 := by
  have h := norm_logRem_cpow_le (n := (p : ℕ)) p.2.two_le (c := 0) (s := s) (a := 1 / 2) (σ := a)
    (by norm_num) ha (by rw [add_zero]; exact hs)
  rw [add_zero] at h
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (he.norm_le_one p)).trans h

theorem summable_editMaj {a : ℝ} (ha : 1 / 2 < a) :
    Summable fun p : Nat.Primes =>
      ((p : ℕ) : ℝ) ^ (-(2 * a)) * (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ)))⁻¹ / 2 :=
  ((summable_prime_rpow (σ := 2 * a) (by linarith)).mul_right _).div_const _

/-- The prime-power remainder of an edit is holomorphic on `Re s > 1/2`. -/
theorem differentiableOn_editRem {e : ℕ → ℤ} (he : IsEdit e) :
    DifferentiableOn ℂ (editRem e) {s : ℂ | 1 / 2 < s.re} := by
  intro s hs
  have hs' : 1 / 2 < s.re := hs
  set a : ℝ := (1 / 2 + s.re) / 2 with ha
  have ha1 : 1 / 2 < a := by rw [ha]; linarith
  set U : Set ℂ := {w : ℂ | a < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ (editRem e) U := by
    refine differentiableOn_tsum_of_summable_norm (summable_editMaj ha1) (fun p => ?_) hUo
      (fun p w hw => norm_edit_mul_logRem_le he p ha1.le (le_of_lt hw))
    intro w hw
    have hw' : a < w.re := hw
    have hlt : ‖((p : ℕ) : ℂ) ^ (-(w + 0))‖ < 1 := by
      rw [norm_natCast_cpow_neg (p : ℕ) p.2.pos (w + 0)]
      exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt)
        (by simp only [add_zero]; linarith)
    have h := differentiableAt_logRem_cpow (n := (p : ℕ)) p.2.pos (c := 0) (s := w) hlt
    simp only [add_zero] at h
    exact (h.const_mul _).differentiableWithinAt
  exact (hd.differentiableAt (hUo.mem_nhds (by show a < s.re; rw [ha]; linarith))).differentiableWithinAt

/-- The indicators of an edit: `[p not deleted] + [p doubled] = 1 + e(p)`. -/
theorem indicator_add_indicator {e : ℕ → ℤ} (he : IsEdit e) (k : ℕ) :
    (1 - (minusSet e).indicator (fun _ => (1 : ℂ)) k) +
      (1 - (plusSet e)ᶜ.indicator (fun _ => (1 : ℂ)) k) = 1 + (e k : ℂ) := by
  classical
  rcases he.range k with h | h | h
  · have h1 : k ∉ minusSet e := fun hm => by
      have hm' : e k = -1 := hm
      rw [h] at hm'
      norm_num at hm'
    have h2 : k ∉ (plusSet e)ᶜ := fun hc => hc h
    rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2, h]
    push_cast
    ring
  · have h1 : k ∈ minusSet e := h
    have h2 : k ∈ (plusSet e)ᶜ := fun hc => by
      have hc' : e k = 1 := hc
      rw [h] at hc'
      norm_num at hc'
    rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2, h]
    push_cast
    ring
  · have h1 : k ∉ minusSet e := fun hm => by
      have hm' : e k = -1 := hm
      rw [h] at hm'
      norm_num at hm'
    have h2 : k ∈ (plusSet e)ᶜ := fun hc => by
      have hc' : e k = 1 := hc
      rw [h] at hc'
      norm_num at hc'
    rw [Set.indicator_of_notMem h1, Set.indicator_of_mem h2, h]
    push_cast
    ring

/-- **The Euler product of an edit.**  `ζ_B(s) = ζ(s) exp(Σ_p e(p) p^{−s} + Q(s))` on
`Re s > 1`. -/
theorem editSystem_zetaSeriesC {e : ℕ → ℤ} (he : IsEdit e) {s : ℂ} (hs : 1 < s.re) :
    (editSystem e).zetaSeriesC s =
      riemannZeta s * Complex.exp (LSeries (fun k => (e k : ℂ)) s + editRem e s) := by
  classical
  have hk : ∀ S : Set ℕ, Summable fun g : (keptPrimeSystem S).Integer =>
      ((keptPrimeSystem S).intNorm g) ^ (-s.re) := fun S =>
    (keptPrimeSystem S).summable_intNorm_rpow (isDiscrete_keptPrimeSystem S)
      (hasLinearCounting_keptPrimeSystem S) hs
  set L : Nat.Primes → ℂ := fun p => -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s)) with hLdef
  have hL : Summable L := (summable_neg_log s hs).of_norm
  have hbd : ∀ c : Nat.Primes → ℂ, (∀ p, ‖c p‖ ≤ 1) → Summable fun p => c p * L p :=
    fun c hc => Summable.of_norm_bounded (summable_neg_log s hs) fun p => by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hc p)
  have hind : ∀ (S : Set ℕ) (p : Nat.Primes),
      ‖1 - S.indicator (fun _ => (1 : ℂ)) (p : ℕ)‖ ≤ 1 := fun S p => by
    rw [Set.indicator_apply]
    split_ifs <;> simp
  have hs₁ : Summable fun p : Nat.Primes =>
      (1 - (minusSet e).indicator (fun _ => (1 : ℂ)) (p : ℕ)) * L p := hbd _ (hind _)
  have hs₂ : Summable fun p : Nat.Primes =>
      (1 - (plusSet e)ᶜ.indicator (fun _ => (1 : ℂ)) (p : ℕ)) * L p := hbd _ (hind _)
  have hs₃ : Summable fun p : Nat.Primes => (e p : ℂ) * L p :=
    hbd _ fun p => he.norm_le_one p
  -- the two Euler products together
  have h1 : (∑' p : Nat.Primes, (1 - (minusSet e).indicator (fun _ => (1 : ℂ)) (p : ℕ)) * L p) +
      (∑' p : Nat.Primes, (1 - (plusSet e)ᶜ.indicator (fun _ => (1 : ℂ)) (p : ℕ)) * L p) =
      (∑' p : Nat.Primes, L p) + ∑' p : Nat.Primes, (e p : ℂ) * L p := by
    rw [← hs₁.tsum_add hs₂, ← hL.tsum_add hs₃]
    refine tsum_congr fun p => ?_
    rw [← add_mul, indicator_add_indicator he]
    ring
  -- the linear part and the prime-power remainder
  have hA : Summable fun p : Nat.Primes => (e p : ℂ) * ((p : ℕ) : ℂ) ^ (-s) :=
    Summable.of_norm_bounded (summable_prime_rpow hs) fun p => by
      rw [norm_mul, norm_natCast_cpow_neg _ p.2.pos]
      exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg _) _) (he.norm_le_one p)
  have hB : Summable fun p : Nat.Primes => (e p : ℂ) * logRem (((p : ℕ) : ℂ) ^ (-s)) :=
    Summable.of_norm_bounded (summable_editMaj (a := 1) (by norm_num)) fun p =>
      norm_edit_mul_logRem_le he p (by norm_num) hs.le
  have hE : ∑' p : Nat.Primes, (e p : ℂ) * ((p : ℕ) : ℂ) ^ (-s) =
      LSeries (fun k => (e k : ℂ)) s :=
    tsum_primes_eq_LSeries (fun k => (e k : ℂ)) (fun n hn => by simp [he.prime n hn]) s
  have h2 : ∑' p : Nat.Primes, (e p : ℂ) * L p =
      LSeries (fun k => (e k : ℂ)) s + editRem e s := by
    rw [← hE, editRem, ← hA.tsum_add hB]
    refine tsum_congr fun p => ?_
    simp only [hLdef, logRem]
    ring
  rw [editSystem, zetaSeriesC_sumSystem (hk _) (hk _), zetaSeriesC_keptPrimeSystem _ hs,
    zetaSeriesC_keptPrimeSystem _ hs, LSeries_sFreeR_eq_exp _ hs, LSeries_sFreeR_eq_exp _ hs,
    ← Complex.exp_add, h1, h2, Complex.exp_add, riemannZeta_eulerProduct_exp_log hs]

/-! ## The count of an edit -/

/-- **The count of an edit.**  If the edited primes are summable at the exponent `β`, the system
of the edit has `N(x) = A x + O(x^β)`. -/
theorem editSystem_count {e : ℕ → ℤ} {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hS : Summable fun k : ℕ => |(e k : ℝ)| * (k : ℝ) ^ (-β)) :
    ∃ A C : ℝ, 0 ≤ A ∧ ∀ x : ℝ, 1 ≤ x →
      |((editSystem e).countBall x : ℝ) - A * x| ≤ C * x ^ β := by
  classical
  have hpow : ∀ k : ℕ, 0 ≤ (k : ℝ) ^ (-β) := fun k => Real.rpow_nonneg (Nat.cast_nonneg k) _
  have hminus : Summable fun p : ℕ => (minusSet e).indicator (fun n => (n : ℝ) ^ (-β)) p := by
    refine Summable.of_nonneg_of_le (fun p => Set.indicator_nonneg (fun n _ => hpow n) p)
      (fun p => ?_) hS
    by_cases h : p ∈ minusSet e
    · have h' : e p = -1 := h
      rw [Set.indicator_of_mem h, h']
      simp
    · rw [Set.indicator_of_notMem h]
      exact mul_nonneg (abs_nonneg _) (hpow p)
  have hplus : Summable fun p : ℕ => (plusSet e).indicator (fun n => (n : ℝ) ^ (-β)) p := by
    refine Summable.of_nonneg_of_le (fun p => Set.indicator_nonneg (fun n _ => hpow n) p)
      (fun p => ?_) hS
    by_cases h : p ∈ plusSet e
    · have h' : e p = 1 := h
      rw [Set.indicator_of_mem h, h']
      simp
    · rw [Set.indicator_of_notMem h]
      exact mul_nonneg (abs_nonneg _) (hpow p)
  obtain ⟨A₁, hA₁, h₁⟩ := keptPrimeSystem_count_sub_le_of_summable hβ0.le hβ1 hminus
  -- the integers supported on the doubled primes
  have hD := summable_sFreeR_compl_rpow hβ0 hplus
  have hLS : LSeriesSummable (fun n => (intCount (keptPrimeSystem (plusSet e)ᶜ)
      (hasIntegerNorms_keptPrimeSystem _) n : ℂ)) (β : ℂ) := by
    refine Summable.of_norm (hD.congr fun n => ?_)
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_zero, norm_zero, sFreeR_zero, zero_mul]
    · rw [LSeries.term_of_ne_zero hn, norm_div, Complex.norm_natCast,
        Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn), Complex.ofReal_re,
        intCount_keptPrimeSystem, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
  have hZ := summable_intNorm_rpow_of_lseriesSummable (hasIntegerNorms_keptPrimeSystem _)
    (isDiscrete_keptPrimeSystem (plusSet e)ᶜ) (σ := β) hLS
  refine ⟨A₁ * ∑' v : (keptPrimeSystem (plusSet e)ᶜ).Integer,
      ((keptPrimeSystem (plusSet e)ᶜ).intNorm v) ^ (-(1 : ℝ)),
    (2 * Real.exp (∑' p : ℕ, (minusSet e).indicator (fun n => (n : ℝ) ^ (-β)) p) + A₁) *
      ∑' v : (keptPrimeSystem (plusSet e)ᶜ).Integer,
        ((keptPrimeSystem (plusSet e)ᶜ).intNorm v) ^ (-β),
    mul_nonneg hA₁ (tsum_nonneg fun v =>
      Real.rpow_nonneg ((keptPrimeSystem (plusSet e)ᶜ).intNorm_pos v).le _), fun x hx => ?_⟩
  exact sumSystem_count_sub_le (isDiscrete_keptPrimeSystem _) (isDiscrete_keptPrimeSystem _) hA₁
    (by positivity) hβ1.le h₁ hZ hx

end GaloisForLFunctions.WorldsOfTheZeroConfiguration.TwoSidedEdits
