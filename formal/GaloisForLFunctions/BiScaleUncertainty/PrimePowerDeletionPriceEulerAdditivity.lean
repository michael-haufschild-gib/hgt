import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowCeilings

/-!
# Deletion prices are additive over primes: the blind cone reads the Euler product

Let `P` be a finite set of primes and `e(p) ≥ 1`, and delete the nodes `m_p = p^{e(p)}`, `p ∈ P`,
from the prime-power blind cone.

**Theorem** (`isLeast_eulerDeviations`, `isGreatest_eulerDeviations`). On the combinations blind at
every prime power except the `m_p`, the exact range of `(A − W)/‖c‖²` is

`[−Σ_{p∈P} Λ(m_p)/√m_p, Σ_{p∈P} Λ(m_p)/√m_p]`:

every deleted node costs its own atom, whatever the other primes do.

**Mechanism.**
* Upper bound: `A − W = Σ_p Λ(m_p) L_{m_p}`, and the tower Fejér bound applies to each node: the
  powers `m_p^k`, `k ≥ 2`, are prime powers outside the deleted set.
* Attainment: the iterated pair `b ∗ Π_{p∈P}(δ₀ + σ_p δ_{log m_p})` is a train over the subsets
  `A ⊆ P` at the positions `log m_A`, `m_A = Π_{p∈A} m_p`. Its lags are `log(m_A/m_B)`. The lag
  equals the logarithm of a prime power `n` exactly when `n m_B = m_A`, and unique factorization
  (`eq_insert_of_isPrimePow_mul_subProd`) forces `n = m_r` and `A = B ∪ {r}`: every other lag is the
  logarithm of a composite integer or of a non-integer, where the cone asks for nothing.
  Each deleted node is then charged with the extremal `L_{m_p}/‖·‖² = σ_p/√m_p` simultaneously.

This is the multiplicativity of the Euler product read by positivity: prime powers of different
primes never interact, and the composite nodes (`6`, `10`, `12`, …) only receive the cross lags.
-/

open MeasureTheory Set Complex Finsupp
open Zeta23
open RHTower RHTower.WeilOneSided
open scoped ComplexConjugate

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-! ### 1. Unique factorization of the subset products -/

/-- The product `m_A = Π_{p ∈ A} p^{e(p)}`. -/
def subProd (e : ℕ → ℕ) (A : Finset ℕ) : ℕ := ∏ p ∈ A, p ^ e p

theorem subProd_pos {e : ℕ → ℕ} {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) : 0 < subProd e A :=
  Finset.prod_pos fun p hp => pow_pos (hA p hp).pos _

theorem factorization_subProd {e : ℕ → ℕ} {A : Finset ℕ} (hA : ∀ p ∈ A, p.Prime) (q : ℕ) :
    (subProd e A).factorization q = if q ∈ A then e q else 0 := by
  classical
  rw [subProd, Nat.factorization_prod fun p hp => (pow_pos (hA p hp).pos _).ne',
    Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl fun p hp => by rw [(hA p hp).factorization_pow, Finsupp.single_apply]]
  exact Finset.sum_ite_eq' A q e

/-- **Unique factorization of the lags.** If a prime power `n` satisfies `n m_B = m_A` for subsets
`A, B` of a set of primes with positive exponents, then `n = m_r` and `A = B ∪ {r}` with `r ∉ B`. -/
theorem eq_insert_of_isPrimePow_mul_subProd {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ}
    (he : ∀ p ∈ P, 1 ≤ e p) {A B : Finset ℕ} (hA : A ⊆ P) (hB : B ⊆ P) {n : ℕ}
    (hn : IsPrimePow n) (h : n * subProd e B = subProd e A) :
    ∃ r ∈ A, r ∉ B ∧ n = r ^ e r ∧ A = insert r B := by
  classical
  obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff n).mp hn
  have hAp : ∀ p ∈ A, p.Prime := fun p hp => hP p (hA hp)
  have hBp : ∀ p ∈ B, p.Prime := fun p hp => hP p (hB hp)
  have hfac : ∀ x, (if x = q then k else 0) + (if x ∈ B then e x else 0) = if x ∈ A then e x else 0 := by
    intro x
    have := congrArg (fun m => m.factorization x) h
    rw [Nat.factorization_mul (pow_pos hq.pos k).ne' (subProd_pos hBp).ne', Finsupp.add_apply,
      hq.factorization_pow, Finsupp.single_apply, factorization_subProd hBp,
      factorization_subProd hAp] at this
    simpa [eq_comm] using this
  have hqA : q ∈ A := by
    by_contra hqA
    have := hfac q
    simp only [if_true, hqA, if_false] at this
    omega
  have hqB : q ∉ B := by
    intro hqB
    have := hfac q
    simp only [if_true, hqA, hqB] at this
    omega
  have hkq : k = e q := by
    have := hfac q
    simp only [if_true, hqA, hqB, if_false] at this
    omega
  refine ⟨q, hqA, hqB, by rw [hkq], ?_⟩
  ext x
  rw [Finset.mem_insert]
  by_cases hxq : x = q
  · subst hxq; simp [hqA]
  · have h1 := hfac x
    rw [if_neg hxq, zero_add] at h1
    constructor
    · intro hxA
      right
      by_contra hxB
      rw [if_neg hxB, if_pos hxA] at h1
      have := he x (hA hxA)
      omega
    · rintro (h' | hxB)
      · exact absurd h' hxq
      · by_contra hxA
        rw [if_pos hxB, if_neg hxA] at h1
        have := he x (hB hxB)
        omega

/-- The subset products separate subsets. -/
theorem eq_of_subProd_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ}
    (he : ∀ p ∈ P, 1 ≤ e p) {A B : Finset ℕ} (hA : A ⊆ P) (hB : B ⊆ P)
    (h : subProd e B = subProd e A) : A = B := by
  classical
  have hAp : ∀ p ∈ A, p.Prime := fun p hp => hP p (hA hp)
  have hBp : ∀ p ∈ B, p.Prime := fun p hp => hP p (hB hp)
  ext x
  have h1 := congrArg (fun m => m.factorization x) h
  simp only [factorization_subProd hAp, factorization_subProd hBp] at h1
  constructor
  · intro hxA
    by_contra hxB
    rw [if_neg hxB, if_pos hxA] at h1
    have := he x (hA hxA)
    omega
  · intro hxB
    by_contra hxA
    rw [if_pos hxB, if_neg hxA] at h1
    have := he x (hB hxB)
    omega

/-! ### 2. Finite trains of the narrow bump -/

/-- The autocorrelation of a finite combination of translates, over any finite index set. -/
theorem weilTest_finset_translates {ι : Type*} (S : Finset ι) (c : ι → ℂ) (x : ι → ℝ)
    {h : ℝ → ℂ} (hc : Continuous h) (hcs : HasCompactSupport h) (y : ℝ) :
    EF.weilTest (fun u => ∑ i ∈ S, c i * h (u - x i)) (fun u => ∑ i ∈ S, c i * h (u - x i)) y =
      ∑ i ∈ S, ∑ i' ∈ S, c i * conj (c i') * EF.weilTest h h (y - x i + x i') := by
  rw [WeilSpectral.weilTest_apply]
  have hpt : ∀ t : ℝ, (∑ i ∈ S, c i * h (t - x i)) * conj (∑ i ∈ S, c i * h (t - y - x i)) =
      ∑ i ∈ S, ∑ i' ∈ S, c i * conj (c i') * (h (t - x i) * conj (h (t - y - x i'))) := by
    intro t
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    rw [map_mul]; ring
  have hint : ∀ i i' : ι, Integrable fun t : ℝ => h (t - x i) * conj (h (t - y - x i')) := by
    intro i i'
    have h1 : Continuous fun t : ℝ => h (t - x i) := hc.comp (continuous_id.sub continuous_const)
    have h2 : Continuous fun t : ℝ => conj (h (t - y - x i')) :=
      continuous_conj.comp (hc.comp ((continuous_id.sub continuous_const).sub continuous_const))
    exact (h1.mul h2).integrable_of_hasCompactSupport
      ((hcs.comp_homeomorph (Homeomorph.subRight (x i))).mul_right)
  simp_rw [sub_sub] at hpt hint ⊢
  have hpt' : ∀ t : ℝ, (∑ i ∈ S, c i * h (t - x i)) * conj (∑ i ∈ S, c i * h (t - (y + x i))) =
      ∑ i ∈ S, ∑ i' ∈ S, c i * conj (c i') * (h (t - x i) * conj (h (t - (y + x i')))) := hpt
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt'),
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun i' _ => (hint i i').const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun i' _ => (hint i i').const_mul _]
  refine Finset.sum_congr rfl fun i' _ => ?_
  rw [integral_const_mul]
  congr 1
  rw [WeilSpectral.weilTest_apply]
  have := integral_add_right_eq_self (μ := volume)
    (fun t : ℝ => h (t - x i) * conj (h (t - (y + x i')))) (x i)
  rw [← this]
  congr 1; funext s
  congr 3 <;> ring

/-- **Lag selection for a train.** If every lag either equals `y` or misses it by more than the
correlation radius, the correlation at `y` is the selected coefficient mass times `∫ h²`. -/
theorem weilTest_train_select {ι : Type*} (S : Finset ι) (c x : ι → ℝ) (j : ℕ) (y : ℝ)
    (hsep : ∀ a ∈ S, ∀ b ∈ S, x a - x b ≠ y → 1 / (2 * ((j : ℝ) + 1)) < |y - x a + x b|) :
    EF.weilTest (fun u => ∑ a ∈ S, ((c a : ℝ) : ℂ) * narrowBumpC j (u - x a))
        (fun u => ∑ a ∈ S, ((c a : ℝ) : ℂ) * narrowBumpC j (u - x a)) y =
      ((∑ a ∈ S, ∑ b ∈ S, if x a - x b = y then c a * c b else 0 : ℝ) : ℂ) *
        ((∫ t, (narrowBump j t) ^ 2 : ℝ) : ℂ) := by
  classical
  rw [weilTest_finset_translates S (fun a => ((c a : ℝ) : ℂ)) x (contDiff_narrowBumpC j).continuous
    (hasCompactSupport_narrowBumpC j), ← weilTest_narrowBumpC_zero, Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [Complex.conj_ofReal]
  by_cases h : x a - x b = y
  · rw [if_pos h, show y - x a + x b = 0 by linarith]; push_cast; ring
  · rw [if_neg h, weilTest_narrowBumpC_eq_zero j (hsep a ha b hb h)]; simp

/-! ### 3. The iterated pair -/

/-- The sign `σ_A = Π_{p ∈ A} σ_p` of a subset. -/
def subSign (σ : ℕ → ℝ) (A : Finset ℕ) : ℝ := ∏ p ∈ A, σ p

/-- The position `log m_A`. -/
def subLog (e : ℕ → ℕ) (A : Finset ℕ) : ℝ := Real.log (subProd e A)

/-- The iterated pair `b ∗ Π_{p ∈ P}(δ₀ + σ_p δ_{log m_p})`, with the narrow bump of index `m_P`. -/
def iteratedPair (P : Finset ℕ) (e : ℕ → ℕ) (σ : ℕ → ℝ) (u : ℝ) : ℂ :=
  ∑ A ∈ P.powerset, ((subSign σ A : ℝ) : ℂ) * narrowBumpC (subProd e P) (u - subLog e A)

section IteratedPair

variable {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ} (he : ∀ p ∈ P, 1 ≤ e p)

include hP in
theorem subProd_le {A : Finset ℕ} (hA : A ⊆ P) : subProd e A ≤ subProd e P :=
  Nat.le_of_dvd (subProd_pos hP) (Finset.prod_dvd_prod_of_subset A P _ hA)

include hP in
/-- A lag `log m_A − log m_B` equals `log n` exactly when `m_A = n m_B`. -/
theorem subLog_sub_eq_log_iff {A B : Finset ℕ} (hA : A ⊆ P) (hB : B ⊆ P) {n : ℕ} (hn : 1 ≤ n) :
    subLog e A - subLog e B = Real.log n ↔ subProd e A = n * subProd e B := by
  have hAp := subProd_pos (e := e) fun p hp => hP p (hA hp)
  have hBp := subProd_pos (e := e) fun p hp => hP p (hB hp)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold subLog
  rw [sub_eq_iff_eq_add, ← Real.log_mul hn'.ne' (by positivity)]
  constructor
  · intro h
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < subProd e A))
      (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < n * subProd e B)) h
    exact_mod_cast this
  · intro h; rw [h]; push_cast; ring_nf

include hP in
/-- **Separation of the lags** at `±log n`. -/
theorem iteratedPair_sep {n : ℕ} (hn : 1 ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ∀ A ∈ P.powerset, ∀ B ∈ P.powerset, subLog e A - subLog e B ≠ s * Real.log n →
      1 / (2 * (((subProd e P : ℕ) : ℝ) + 1)) < |s * Real.log n - subLog e A + subLog e B| := by
  intro A hA B hB hne
  rw [Finset.mem_powerset] at hA hB
  have hAp := subProd_pos (e := e) fun p hp => hP p (hA hp)
  have hBp := subProd_pos (e := e) fun p hp => hP p (hB hp)
  have hMA : (subProd e A : ℝ) ≤ subProd e P := by exact_mod_cast subProd_le hP hA
  have hMB : (subProd e B : ℝ) ≤ subProd e P := by exact_mod_cast subProd_le hP hB
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key : ∀ X Y : ℕ, 1 ≤ X → 1 ≤ Y → X ≠ Y → (Y : ℝ) ≤ subProd e P →
      1 / (2 * (((subProd e P : ℕ) : ℝ) + 1)) < |Real.log X - Real.log Y| := by
    intro X Y hX hY hXY hYM
    refine lt_of_lt_of_le ?_ (WeilExcess.inv_succ_le_abs_log_sub hX hY hXY)
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) ≤ subProd e P := by positivity
    linarith
  rcases hs with rfl | rfl
  · rw [one_mul] at hne ⊢
    have hne' : n * subProd e B ≠ subProd e A := fun h =>
      hne ((subLog_sub_eq_log_iff hP hA hB hn).mpr h.symm)
    have := key (n * subProd e B) (subProd e A) (by nlinarith) hAp hne' hMA
    rw [Nat.cast_mul, Real.log_mul hn'.ne' (by positivity)] at this
    unfold subLog
    rwa [show Real.log n - Real.log (subProd e A) + Real.log (subProd e B) =
      Real.log n + Real.log (subProd e B) - Real.log (subProd e A) by ring]
  · rw [neg_one_mul] at hne ⊢
    have hne' : n * subProd e A ≠ subProd e B := fun h => by
      apply hne
      have := (subLog_sub_eq_log_iff hP hB hA hn).mpr h.symm
      linarith
    have := key (n * subProd e A) (subProd e B) (by nlinarith) hBp hne' hMB
    rw [Nat.cast_mul, Real.log_mul hn'.ne' (by positivity)] at this
    unfold subLog
    rw [abs_sub_comm] at this
    rwa [show -Real.log n - Real.log (subProd e A) + Real.log (subProd e B) =
      -(Real.log n + Real.log (subProd e A) - Real.log (subProd e B)) by ring, abs_neg,
      abs_sub_comm]

end IteratedPair

/-! ### 4. The coefficients of the train -/

/-- The coefficient of the lag `y` in the autocorrelation of the iterated pair. -/
def trainCoeff (P : Finset ℕ) (e : ℕ → ℕ) (σ : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ A ∈ P.powerset, ∑ B ∈ P.powerset,
    if subLog e A - subLog e B = y then subSign σ A * subSign σ B else 0

theorem hasCompactSupport_finsetSum {ι : Type*} (S : Finset ι) {f : ι → ℝ → ℂ}
    (hf : ∀ i ∈ S, HasCompactSupport (f i)) : HasCompactSupport fun u => ∑ i ∈ S, f i u := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact HasCompactSupport.zero
  | insert a S ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem contDiff_iteratedPair (P : Finset ℕ) (e : ℕ → ℕ) (σ : ℕ → ℝ) :
    ContDiff ℝ 2 (iteratedPair P e σ) :=
  ContDiff.sum fun _ _ => contDiff_const.mul
    (((contDiff_narrowBumpC _).of_le (by norm_cast)).comp (contDiff_id.sub contDiff_const))

theorem hasCompactSupport_iteratedPair (P : Finset ℕ) (e : ℕ → ℕ) (σ : ℕ → ℝ) :
    HasCompactSupport (iteratedPair P e σ) :=
  hasCompactSupport_finsetSum _ fun _ _ =>
    ((hasCompactSupport_narrowBumpC _).comp_homeomorph (Homeomorph.subRight _)).mul_left

/-- The iterated pair as a Weil test. -/
def iteratedPairTestFn (P : Finset ℕ) (e : ℕ → ℕ) (σ : ℕ → ℝ) : WeilTestFn :=
  ⟨iteratedPair P e σ, contDiff_iteratedPair P e σ, hasCompactSupport_iteratedPair P e σ⟩

section TrainCoefficients

variable {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ} (he : ∀ p ∈ P, 1 ≤ e p)
  {σ : ℕ → ℝ}

include hP in
/-- The autocorrelation of the iterated pair at `±log n` is a coefficient times `∫ h²`. -/
theorem weilTest_iteratedPair {n : ℕ} (hn : 1 ≤ n) (s : ℝ) (hs : s = 1 ∨ s = -1) :
    EF.weilTest (iteratedPair P e σ) (iteratedPair P e σ) (s * Real.log n) =
      (trainCoeff P e σ (s * Real.log n) : ℂ) *
        ((∫ t, (narrowBump (subProd e P) t) ^ 2 : ℝ) : ℂ) :=
  weilTest_train_select _ (subSign σ) (subLog e) _ _ (iteratedPair_sep hP hn s hs)

/-- Reversing the lag reverses the pair `(A, B)`. -/
theorem trainCoeff_neg (y : ℝ) : trainCoeff P e σ (-y) = trainCoeff P e σ y := by
  unfold trainCoeff
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
  by_cases h : subLog e A - subLog e B = y
  · rw [if_pos h, if_pos (by linarith), mul_comm]
  · rw [if_neg h, if_neg fun h' => h (by linarith)]

include hP in
/-- On the lag `log n` the coefficient counts the factorizations `m_A = n m_B`. -/
theorem trainCoeff_log_eq {n : ℕ} (hn : 1 ≤ n) :
    trainCoeff P e σ (Real.log n) = ∑ A ∈ P.powerset, ∑ B ∈ P.powerset,
      if subProd e A = n * subProd e B then subSign σ A * subSign σ B else 0 := by
  unfold trainCoeff
  refine Finset.sum_congr rfl fun A hA => Finset.sum_congr rfl fun B hB => ?_
  rw [Finset.mem_powerset] at hA hB
  exact if_congr (subLog_sub_eq_log_iff hP hA hB hn) rfl rfl

theorem subSign_sq (hσ : ∀ p ∈ P, σ p ^ 2 = 1) {A : Finset ℕ} (hA : A ⊆ P) :
    subSign σ A ^ 2 = 1 := by
  rw [subSign, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun p hp => hσ p (hA hp)

include hP he in
/-- The diagonal coefficient is the number of subsets. -/
theorem trainCoeff_zero (hσ : ∀ p ∈ P, σ p ^ 2 = 1) :
    trainCoeff P e σ (Real.log (1 : ℕ)) = (P.powerset.card : ℝ) := by
  classical
  rw [trainCoeff_log_eq hP le_rfl]
  have : ∀ A ∈ P.powerset, (∑ B ∈ P.powerset,
      if subProd e A = 1 * subProd e B then subSign σ A * subSign σ B else 0) = 1 := by
    intro A hA
    rw [Finset.sum_congr rfl fun B hB => if_congr (show subProd e A = 1 * subProd e B ↔ B = A from
      ⟨fun h => eq_of_subProd_eq hP he (Finset.mem_powerset.mp hB) (Finset.mem_powerset.mp hA)
        (by rw [h, one_mul]), fun h => by rw [h, one_mul]⟩) rfl rfl, Finset.sum_ite_eq' P.powerset A,
      if_pos hA, ← sq, subSign_sq hσ (Finset.mem_powerset.mp hA)]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]

include hP he in
/-- **Blindness of the train.** At a prime power outside the deleted set the coefficient is zero:
no two subset products differ by that prime power. -/
theorem trainCoeff_log_eq_zero {n : ℕ} (hn : IsPrimePow n) (hnot : ∀ p ∈ P, p ^ e p ≠ n) :
    trainCoeff P e σ (Real.log n) = 0 := by
  rw [trainCoeff_log_eq hP hn.one_lt.le]
  refine Finset.sum_eq_zero fun A hA => Finset.sum_eq_zero fun B hB => if_neg fun h => ?_
  obtain ⟨r, hrA, -, hr, -⟩ := eq_insert_of_isPrimePow_mul_subProd hP he
    (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB) hn h.symm
  exact hnot r (Finset.mem_powerset.mp hA hrA) hr.symm

/-- Prime powers with positive exponent determine their prime. -/
theorem eq_of_prime_pow_eq {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (ha : 1 ≤ a)
    (h : p ^ a = q ^ b) : p = q ∧ a = b := by
  have h1 := congrArg (fun m => m.factorization p) h
  simp only [hp.factorization_pow, hq.factorization_pow, Finsupp.single_apply, if_true] at h1
  by_cases hqp : q = p
  · rw [if_pos hqp] at h1; exact ⟨hqp.symm, h1⟩
  · rw [if_neg hqp] at h1; omega

include hP he in
/-- **The charged coefficient.** At a deleted node `m_r` the coefficient is `σ_r` times the number
of subsets avoiding `r`: the pairs are `(B ∪ {r}, B)`. -/
theorem trainCoeff_log_deleted (hσ : ∀ p ∈ P, σ p ^ 2 = 1) {r : ℕ} (hr : r ∈ P) :
    trainCoeff P e σ (Real.log (r ^ e r : ℕ)) = σ r * ((P.erase r).powerset.card : ℝ) := by
  classical
  have hrp := hP r hr
  have hn : IsPrimePow (r ^ e r) := hrp.isPrimePow.pow (by have := he r hr; omega)
  rw [trainCoeff_log_eq hP hn.one_lt.le, Finset.sum_comm]
  have key : ∀ B ∈ P.powerset, (∑ A ∈ P.powerset,
      if subProd e A = r ^ e r * subProd e B then subSign σ A * subSign σ B else 0) =
        if r ∉ B then σ r else 0 := by
    intro B hB
    have hBP := Finset.mem_powerset.mp hB
    rw [Finset.sum_congr rfl fun A hA => if_congr (show subProd e A = r ^ e r * subProd e B ↔
        r ∉ B ∧ A = insert r B from ?_) rfl rfl]
    · by_cases hrB : r ∈ B
      · simp only [hrB, not_true_eq_false, false_and, if_false, Finset.sum_const_zero]
      · simp only [hrB, not_false_eq_true, true_and, if_true]
        rw [Finset.sum_ite_eq' P.powerset (insert r B),
          if_pos (Finset.mem_powerset.mpr (Finset.insert_subset hr hBP)), subSign,
          Finset.prod_insert hrB, mul_assoc, ← subSign, ← sq, subSign_sq hσ hBP, mul_one]
    · constructor
      · intro h
        obtain ⟨r', hr'A, hr'B, hr', hAeq⟩ := eq_insert_of_isPrimePow_mul_subProd hP he
          (Finset.mem_powerset.mp hA) hBP hn h.symm
        obtain ⟨rfl, -⟩ := eq_of_prime_pow_eq hrp (hP r' (Finset.mem_powerset.mp hA hr'A))
          (he r hr) hr'
        exact ⟨hr'B, hAeq⟩
      · rintro ⟨hrB, rfl⟩
        simp only [subProd, Finset.prod_insert hrB]
  have hfilt : P.powerset.filter (fun B => r ∉ B) = (P.erase r).powerset := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hBP, hrB⟩ x hx
      exact Finset.mem_erase.mpr ⟨fun h => hrB (h ▸ hx), hBP hx⟩
    · intro hB
      exact ⟨fun x hx => (Finset.mem_erase.mp (hB hx)).2,
        fun hrB => (Finset.mem_erase.mp (hB hrB)).1 rfl⟩
  rw [Finset.sum_congr rfl key, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm, hfilt]

omit hP he in
theorem card_powerset_eq_two_mul {r : ℕ} (hr : r ∈ P) :
    (P.powerset.card : ℝ) = 2 * ((P.erase r).powerset.card : ℝ) := by
  classical
  rw [Finset.card_powerset, Finset.card_powerset, Finset.card_erase_of_mem hr]
  have : 1 ≤ P.card := Finset.card_pos.mpr ⟨r, hr⟩
  rw [show P.card = P.card - 1 + 1 by omega, pow_succ]
  push_cast
  ring_nf

end TrainCoefficients

/-! ### 5. The deletion identity and the additive bound -/

/-- The node value at `n`, zero below `2`. -/
def nodeAt (c : WeilTestFn →₀ ℝ) (n : ℕ) : ℝ := if h : 2 ≤ n then nodeVector c ⟨n, h⟩ else 0

/-- **The finite deletion identity.** On the cone blind at every prime power outside a finite set
`D`: `A(c) = W(c) + Σ_{n∈D} Λ(n) L_n(c)`. -/
theorem nodeArchEnergy_eq_weilEnergy_add_finset {c : WeilTestFn →₀ ℝ} (D : Finset ℕ)
    (hb : BlindOn (primePowerNodes \ ↑D) c) :
    nodeArchEnergy c = weilEnergy c +
      ∑ n ∈ D, (ArithmeticFunction.vonMangoldt n : ℝ) * nodeAt c n := by
  classical
  set g : LogIndex → ℝ := fun j => nodeVector c j • (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ)
  have hg : ∀ j : LogIndex, (j : ℕ) ∉ D → g j = 0 := by
    intro j hj
    by_cases hp : IsPrimePow (j : ℕ)
    · simp only [g, hb j ⟨hp, hj⟩, zero_smul]
    · simp only [g, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp, smul_zero]
  rw [nodeArchEnergy_eq_weilEnergy_add, linearCombination_apply, Finsupp.sum]
  congr 1
  change ∑ j ∈ (nodeVector c).support, g j = _
  have hs1 : ∑ j ∈ (nodeVector c).support, g j =
      ∑ j ∈ (nodeVector c).support ∪ D.subtype (fun n => 2 ≤ n), g j :=
    Finset.sum_subset Finset.subset_union_left fun j _ hj => by
      simp only [g, Finsupp.notMem_support_iff.mp hj, zero_smul]
  have hs2 : ∑ j ∈ D.subtype (fun n => 2 ≤ n), g j =
      ∑ j ∈ (nodeVector c).support ∪ D.subtype (fun n => 2 ≤ n), g j :=
    Finset.sum_subset Finset.subset_union_right fun j _ hj =>
      hg j fun h => hj (Finset.mem_subtype.mpr h)
  have hgf : ∀ j : LogIndex, g j =
      (ArithmeticFunction.vonMangoldt (j : ℕ) : ℝ) * nodeAt c (j : ℕ) := by
    intro j
    simp only [g, nodeAt, dif_pos j.2, smul_eq_mul, mul_comm]
  rw [hs1, ← hs2, Finset.sum_congr rfl fun j _ => hgf j,
    Finset.sum_subtype_eq_sum_filter (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ) * nodeAt c n),
    Finset.sum_filter_of_ne]
  intro n _ hn
  by_contra h2
  simp only [nodeAt, dif_neg h2, mul_zero, ne_eq, not_true_eq_false] at hn

/-- The deleted nodes `m_p = p^{e(p)}`, `p ∈ P`. -/
def eulerNodes (P : Finset ℕ) (e : ℕ → ℕ) : Finset ℕ := P.image fun p => p ^ e p

/-- The Euler price `Σ_{p∈P} Λ(m_p)/√m_p`. -/
def eulerPrice (P : Finset ℕ) (e : ℕ → ℕ) : ℝ :=
  ∑ p ∈ P, (ArithmeticFunction.vonMangoldt (p ^ e p) : ℝ) / Real.sqrt ((p ^ e p : ℕ) : ℝ)

section EulerBound

variable {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ} (he : ∀ p ∈ P, 1 ≤ e p)

include hP he in
theorem injOn_eulerNodes : Set.InjOn (fun p => p ^ e p) ↑P := fun p hp q hq h =>
  (eq_of_prime_pow_eq (hP p hp) (hP q hq) (he p hp) h).1

include hP he in
theorem two_le_pow {p : ℕ} (hp : p ∈ P) : 2 ≤ p ^ e p :=
  ((hP p hp).isPrimePow.pow (by have := he p hp; omega)).two_le

include hP he in
/-- The powers `m_p^k`, `k ≥ 2`, are prime powers outside the deleted set. -/
theorem pow_mem_primePowerNodes_diff_eulerNodes {p : ℕ} (hp : p ∈ P) {k : ℕ} (hk : 2 ≤ k) :
    (p ^ e p) ^ k ∈ primePowerNodes \ ↑(eulerNodes P e) := by
  have hpe := he p hp
  refine ⟨?_, fun h => ?_⟩
  · show IsPrimePow ((p ^ e p) ^ k)
    rw [← pow_mul]
    exact (hP p hp).isPrimePow.pow (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨q, hq, hqe⟩ := Finset.mem_image.mp (Finset.mem_coe.mp h)
  rw [← pow_mul] at hqe
  obtain ⟨rfl, h2⟩ := eq_of_prime_pow_eq (hP q hq) (hP p hp) (he q hq) hqe
  nlinarith

include hP he in
/-- **Additive upper bound.** On the cone blind at every prime power outside `{m_p : p ∈ P}`,
`|A − W| ≤ (Σ_{p∈P} Λ(m_p)/√m_p) ‖c‖²`. -/
theorem abs_nodeArchEnergy_sub_weilEnergy_le_euler {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f)
    (hb : BlindOn (primePowerNodes \ ↑(eulerNodes P e)) c) :
    |nodeArchEnergy c - weilEnergy c| ≤ eulerPrice P e * massOf c := by
  classical
  rw [nodeArchEnergy_eq_weilEnergy_add_finset _ hb, add_sub_cancel_left, eulerNodes,
    Finset.sum_image (injOn_eulerNodes hP he), eulerPrice, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p hp => ?_)
  have h2 := two_le_pow hP he hp
  have hΛ : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt (p ^ e p) :=
    ArithmeticFunction.vonMangoldt_nonneg
  have hF := abs_nodeVector_le_massOf_div_sqrt hc h2 fun j ⟨k, hk, hj⟩ =>
    hb j (hj ▸ pow_mem_primePowerNodes_diff_eulerNodes hP he hp hk)
  rw [nodeAt, dif_pos h2, abs_mul, abs_of_nonneg hΛ, div_mul_eq_mul_div, mul_div_assoc]
  exact mul_le_mul_of_nonneg_left hF hΛ

end EulerBound

/-! ### 6. Sharpness -/

section EulerSharp

variable {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ} (he : ∀ p ∈ P, 1 ≤ e p)
  {σ : ℕ → ℝ} (hσ : ∀ p ∈ P, σ p ^ 2 = 1)

include hP he hσ in
/-- The mass of the train is `2^{|P|} ∫ h²`. -/
theorem massOf_single_iteratedPairTestFn :
    massOf (Finsupp.single (iteratedPairTestFn P e σ) 1) =
      (P.powerset.card : ℝ) * ∫ t, (narrowBump (subProd e P) t) ^ 2 := by
  have hk := weilTest_iteratedPair hP (σ := σ) (e := e) le_rfl 1 (Or.inl rfl)
  rw [one_mul, trainCoeff_zero hP he hσ, Nat.cast_one, Real.log_one,
    RHTower.weilTest_zero_eq_integral_norm_sq] at hk
  have hm : ∫ u, ‖iteratedPair P e σ u‖ ^ 2 =
      (P.powerset.card : ℝ) * ∫ t, (narrowBump (subProd e P) t) ^ 2 := by exact_mod_cast hk
  rw [WeilOneSided.massOf, Finsupp.sum_single_index (by simp), one_mul]
  exact hm

include hP he in
/-- The train is blind at every prime power outside the deleted set. -/
theorem blindOn_single_iteratedPairTestFn :
    BlindOn (primePowerNodes \ ↑(eulerNodes P e)) (Finsupp.single (iteratedPairTestFn P e σ) 1) := by
  intro j ⟨hpp, hj⟩
  have hnot : ∀ p ∈ P, p ^ e p ≠ (j : ℕ) := fun p hp h =>
    hj (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨p, hp, h⟩))
  have h0 := trainCoeff_log_eq_zero hP he (σ := σ) hpp hnot
  have e1 := weilTest_iteratedPair hP (σ := σ) (e := e) hpp.one_lt.le 1 (Or.inl rfl)
  have e2 := weilTest_iteratedPair hP (σ := σ) (e := e) hpp.one_lt.le (-1) (Or.inr rfl)
  rw [one_mul] at e1
  rw [neg_one_mul, trainCoeff_neg] at e2
  rw [nodeVector_single_test, logVector_apply]
  change logValue (iteratedPair P e σ) j = 0
  rw [logValue, e1, e2, h0]
  simp

include hP he hσ in
/-- At a deleted node the train carries the tower Fejér extreme `L_{m_r} = σ_r ‖·‖²/√m_r`. -/
theorem nodeAt_single_iteratedPairTestFn {r : ℕ} (hr : r ∈ P) :
    nodeAt (Finsupp.single (iteratedPairTestFn P e σ) 1) (r ^ e r) =
      σ r * massOf (Finsupp.single (iteratedPairTestFn P e σ) 1) / Real.sqrt ((r ^ e r : ℕ) : ℝ) := by
  have h2 := two_le_pow hP he hr
  have hc := trainCoeff_log_deleted hP he hσ (σ := σ) hr
  have e1 := weilTest_iteratedPair hP (σ := σ) (e := e) (n := r ^ e r) (by omega) 1 (Or.inl rfl)
  have e2 := weilTest_iteratedPair hP (σ := σ) (e := e) (n := r ^ e r) (by omega) (-1) (Or.inr rfl)
  rw [one_mul] at e1
  rw [neg_one_mul, trainCoeff_neg] at e2
  rw [nodeAt, dif_pos h2, nodeVector_single_test, logVector_apply,
    massOf_single_iteratedPairTestFn hP he hσ, card_powerset_eq_two_mul hr]
  change logValue (iteratedPair P e σ) (r ^ e r) = _
  rw [logValue, e1, e2, hc, ← add_mul, ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

end EulerSharp

/-- The normalized deviations `(A − W)/‖·‖²` on the cone blind at every prime power outside
`{p^{e(p)} : p ∈ P}`. -/
def eulerDeviations (P : Finset ℕ) (e : ℕ → ℕ) : Set ℝ :=
  {x | ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧ BlindOn (primePowerNodes \ ↑(eulerNodes P e)) c ∧
    0 < massOf c ∧ x = (nodeArchEnergy c - weilEnergy c) / massOf c}

theorem deviation_single_iteratedPairTestFn {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ}
    (he : ∀ p ∈ P, 1 ≤ e p) {s : ℝ} (hs : s ^ 2 = 1) :
    s * eulerPrice P e ∈ eulerDeviations P e := by
  classical
  have hσ : ∀ p ∈ P, (fun _ : ℕ => s) p ^ 2 = 1 := fun _ _ => hs
  have hmass := massOf_single_iteratedPairTestFn hP he hσ
  have hpos : 0 < massOf (Finsupp.single (iteratedPairTestFn P e fun _ => s) 1) := by
    rw [hmass]
    have : (0 : ℝ) < P.powerset.card := by exact_mod_cast Finset.card_pos.mpr ⟨∅, by simp⟩
    exact mul_pos this (integral_narrowBump_sq_pos _)
  have hb := blindOn_single_iteratedPairTestFn hP he (σ := fun _ => s)
  refine ⟨_, fun f => ?_, hb, hpos, ?_⟩
  · rw [Finsupp.single_apply]; split_ifs <;> norm_num
  · rw [nodeArchEnergy_eq_weilEnergy_add_finset _ hb, add_sub_cancel_left, eulerNodes,
      Finset.sum_image (injOn_eulerNodes hP he), eulerPrice, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [nodeAt_single_iteratedPairTestFn hP he hσ hp]
    field_simp

/-- **Deletion prices add over primes: the least deviation is `−Σ_{p∈P} Λ(m_p)/√m_p`.** -/
theorem isLeast_eulerDeviations {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ}
    (he : ∀ p ∈ P, 1 ≤ e p) : IsLeast (eulerDeviations P e) (-eulerPrice P e) := by
  refine ⟨by simpa using deviation_single_iteratedPairTestFn hP he (s := -1) (by norm_num), ?_⟩
  rintro x ⟨c, hc, hb, hpos, rfl⟩
  have h := abs_nodeArchEnergy_sub_weilEnergy_le_euler hP he hc hb
  rw [le_div_iff₀ hpos]
  linarith [neg_abs_le (nodeArchEnergy c - weilEnergy c)]

/-- **Deletion prices add over primes: the greatest deviation is `Σ_{p∈P} Λ(m_p)/√m_p`.** -/
theorem isGreatest_eulerDeviations {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ}
    (he : ∀ p ∈ P, 1 ≤ e p) : IsGreatest (eulerDeviations P e) (eulerPrice P e) := by
  refine ⟨by simpa using deviation_single_iteratedPairTestFn hP he (s := 1) (by norm_num), ?_⟩
  rintro x ⟨c, hc, hb, hpos, rfl⟩
  have h := abs_nodeArchEnergy_sub_weilEnergy_le_euler hP he hc hb
  rw [div_le_iff₀ hpos]
  linarith [le_abs_self (nodeArchEnergy c - weilEnergy c)]

/-- The Euler price is `Σ_{p∈P} log p / p^{e(p)/2}`. -/
theorem eulerPrice_eq {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {e : ℕ → ℕ} (he : ∀ p ∈ P, 1 ≤ e p) :
    eulerPrice P e = ∑ p ∈ P, Real.log p / Real.sqrt ((p ^ e p : ℕ) : ℝ) := by
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by have := he p hp; omega),
    ArithmeticFunction.vonMangoldt_apply_prime (hP p hp)]

/-- **Deleting every prime up to `x`** (keeping all higher prime powers) has exact price
`Σ_{p ≤ x} log p/√p`. -/
theorem isLeast_eulerDeviations_primes_le (x : ℕ) :
    IsLeast (eulerDeviations ((Finset.range (x + 1)).filter Nat.Prime) fun _ => 1)
      (-∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime, Real.log p / Real.sqrt p) := by
  have hP : ∀ p ∈ (Finset.range (x + 1)).filter Nat.Prime, p.Prime := fun p hp =>
    (Finset.mem_filter.mp hp).2
  have h := isLeast_eulerDeviations hP (e := fun _ => 1) fun _ _ => le_rfl
  rwa [eulerPrice_eq hP fun _ _ => le_rfl, Finset.sum_congr rfl fun p _ => by rw [pow_one]] at h

end

end GaloisForLFunctions.BiScaleUncertainty
