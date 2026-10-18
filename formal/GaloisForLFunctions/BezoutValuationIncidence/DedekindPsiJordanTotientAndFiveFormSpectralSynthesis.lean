import GaloisForLFunctions.BezoutValuationIncidence.JordanUpperBoundAndGcdOrbitPrimitiveEnergy
import GaloisForLFunctions.BezoutValuationIncidence.SharpSuccessorPhaseLossAndClosureClassification
import GaloisForLFunctions.BezoutValuationIncidence.UniversalSawtoothInteriorMartingaleAndPostStepCalculus

/-!
# Pillar XXXII: Dedekind's Psi Ratio, Sharp Prime Lower Bounds on `J₂`, Wall 11 Five-Weight Separation & Master Five-Form Spectral Synthesis

In earlier pillars of **Bézout–Valuation Incidence Mechanics**, five fundamental quadratic forms on
finite divisor-sieve space were constructed and diagonalized in the common Selberg multiples basis
$Y_{N,c}(q) = \operatorname{selbergMultiplesCoord}\,N\,c\,q$:
1. **Selberg Variance (`sieveVariance`)**: modal weight $\varphi(q)$,
2. **Bézout Successor Covariance (`sieveSuccessorCovariance`)**: modal weight $\mu(q)$,
3. **Bézout Successor Reserve (`sieveSuccessorReserve`)**: modal weight $\varphi(q) - \mu(q)$,
4. **Irreducible One-Step Phase Loss (`successorPhaseLoss`)**: modal weight
   $\varphi(q) - \mu(q)^2 / \varphi(q)$,
5. **Sawtooth Primitive Energy (`12 * sievePrimitiveEnergy`)**: modal weight $J_2(q)$
   (`jordanTotient2 q`).

In this thirty-second pillar of **Bézout–Valuation Incidence Mechanics**, we establish the exact
multiplicative and spectral bridge uniting all five modal weights and their associated quadratic
forms:

1. **The Dedekind Psi Ratio $\psi(n) = J_2(n) / \varphi(n)$, Exact Prime Identity, & Wall 11
   Five-Weight Separation (`dedekindPsiReal`,
   `jordanTotient2_eq_dedekindPsiReal_mul_totient`,
   `dedekindPsiReal_prime_pow_succ`,
   `dedekindPsiReal_prime_eq_totient_sub_two_moebius`,
   `jordanTotient2_prime_eq_totient_moebius`,
   `wall11_five_modal_weights_separation`)**:
   - Defining $\operatorname{dedekindPsiReal}\,n := \operatorname{jordanTotient2}\,n / \varphi(n)$,
     we prove $J_2(n) = \psi(n)\,\varphi(n)$ for all $n \in \mathbb{N}$ and
     $\psi(p^{k+1}) = p^k(p + 1)$ for every prime power $p^{k+1}$.
   - At every prime $p$, the Dedekind psi ratio and Jordan totient are expressed **purely in terms
     of the Selberg–Bézout pair $(\varphi(p), \mu(p))$**:
     $$\psi(p) = p + 1 = \varphi(p) - 2\mu(p), \qquad
       J_2(p) = \varphi(p)\bigl(\varphi(p) - 2\mu(p)\bigr) = \bigl(\varphi(p) - \mu(p)\bigr)^2 - 1.$$
   - At the Wall 11 pair $(4, 6)$ where $\varphi(4) = \varphi(6) = 2$, all four non-Selberg modal
     weights break the totient degeneracy simultaneously:
     - $\mu(4) = 0 \ne 1 = \mu(6)$,
     - $\varphi(4) - \mu(4) = 2 \ne 1 = \varphi(6) - \mu(6)$,
     - $\varphi(4) - \mu(4)^2/\varphi(4) = 2 \ne 3/2 = \varphi(6) - \mu(6)^2/\varphi(6)$,
     - $J_2(4) = 12 \ne 24 = J_2(6) = 2\,J_2(4)$ (and $\psi(4) = 6 \ne 12 = \psi(6)$).

2. **Sharp Prime-Attained Lower Bound $(q + 1)\,\varphi(q) \le J_2(q)$ & Parity-Split Primitive
   Energy Inequality (`add_one_mul_totient_le_jordanTotient2`,
   `three_mul_sieveVariance_add_above_parity_le_twelve_mul_sievePrimitiveEnergy`,
   `three_mul_sieveVariance_add_phaseLoss_le_twelve_mul_sievePrimitiveEnergy`)**:
   - Strengthening `jordanTotient2_ge_mul_totient` ($q\,\varphi(q) \le J_2(q)$), we prove that for
     **every** $q \ge 2$:
     $$(q + 1)\,\varphi(q) \le J_2(q) \quad \text{and} \quad q + 1 \le \psi(q),$$
     with **exact equality at every prime $q = p$** (where $(p + 1)(p - 1) = p^2 - 1 = J_2(p)$).
   - Summing over $q \in [2, N]$ yields the sharp parity-split lower bound on `sievePrimitiveEnergy`:
     $$3\,\operatorname{sieveVariance}\,N\,c + \operatorname{sieveVarianceAboveParity}\,N\,c \le
       12\,\operatorname{sievePrimitiveEnergy}\,N\,c,$$
     with **exact equality at $N = 3$ for every weight $c$** (since $2 + 1 = 3$ at $q = 2$ and
     $3 + 1 = 4$ at $q = 3$), and hence:
     $$3\,\operatorname{sieveVariance}\,N\,c + \operatorname{successorPhaseLoss}\,N\,c \le
       12\,\operatorname{sievePrimitiveEnergy}\,N\,c.$$

3. **Gcd-Orbit Projection of `successorPhaseLoss` & Master Five-Form Spectral Synthesis
   (`successorPhaseLoss_gcdProjection_and_pythagoras`,
   `bezoutValuationIncidence_master_five_form_synthesis`)**:
   - Extending `sieveGcdProjection_observables_diagonal` and
     `sieveGcdProjection_simultaneous_pythagoras` to the 4th quadratic form `successorPhaseLoss`,
     we unite all five canonical quadratic forms of `BezoutValuationIncidence` into a single
     simultaneous diagonalization, gcd-orbit projection, and universal inequality theorem.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The Dedekind Psi Ratio $\psi(n) = J_2(n) / \varphi(n)$, Prime Bridge, & Wall 11 Five-Weight Separation -/

/-- **Real Dedekind Psi Function (`dedekindPsiReal`):**
The ratio `ψ(n) = J₂(n) / φ(n)` between the second Jordan totient `jordanTotient2 n` (governing the
discrete sawtooth primitive energy) and Euler's totient `φ(n)` (governing the Selberg variance). -/
def dedekindPsiReal (n : ℕ) : ℝ :=
  jordanTotient2 n / (Nat.totient n : ℝ)

/-- **Exact Factorization `J₂(n) = ψ(n) * φ(n)` (`jordanTotient2_eq_dedekindPsiReal_mul_totient`):**
For every `n : ℕ` (including `n = 0`), `jordanTotient2 n = dedekindPsiReal n * (Nat.totient n : ℝ)`. -/
theorem jordanTotient2_eq_dedekindPsiReal_mul_totient (n : ℕ) :
    jordanTotient2 n = dedekindPsiReal n * (Nat.totient n : ℝ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [dedekindPsiReal, jordanTotient2]
  · unfold dedekindPsiReal
    have hphi : (Nat.totient n : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)).ne'
    exact (div_mul_cancel₀ _ hphi).symm

/-- **Coprime Multiplicativity of `dedekindPsiReal` (`dedekindPsiReal_mul_of_coprime`):**
For every coprime pair `a, b : ℕ`, `dedekindPsiReal (a * b) = dedekindPsiReal a * dedekindPsiReal b`. -/
theorem dedekindPsiReal_mul_of_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    dedekindPsiReal (a * b) = dedekindPsiReal a * dedekindPsiReal b := by
  unfold dedekindPsiReal
  rw [jordanTotient2_mul_of_coprime hab, Nat.totient_mul hab, Nat.cast_mul, div_mul_div_comm]

/-- **Prime-Power Evaluation of `dedekindPsiReal` (`dedekindPsiReal_prime_pow_succ`):**
For every prime `p` and `k : ℕ`, `dedekindPsiReal (p ^ (k + 1)) = p ^ k * (p + 1)`. -/
theorem dedekindPsiReal_prime_pow_succ {p : ℕ} (hp : Nat.Prime p) (k : ℕ) :
    dedekindPsiReal (p ^ (k + 1)) = (p : ℝ) ^ k * ((p : ℝ) + 1) := by
  unfold dedekindPsiReal
  rw [jordanTotient2_prime_pow_succ hp k, Nat.totient_prime_pow_succ hp]
  push_cast [Nat.cast_sub hp.one_le]
  rw [pow_succ (p : ℝ) k]
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  have hpk : (p : ℝ) ^ k ≠ 0 := pow_ne_zero k (Nat.cast_ne_zero.mpr hp.ne_zero)
  have hfac :
      ((p : ℝ) ^ k * (p : ℝ)) ^ (2 : ℕ) - ((p : ℝ) ^ k) ^ (2 : ℕ) =
        ((p : ℝ) ^ k * ((p : ℝ) + 1)) * ((p : ℝ) ^ k * ((p : ℝ) - 1)) := by
    ring
  rw [hfac, mul_div_cancel_right₀ _ (mul_ne_zero hpk hp1)]

/-- **Prime Evaluation of `dedekindPsiReal` via Selberg–Bézout Weights
(`dedekindPsiReal_prime_eq_totient_sub_two_moebius`):**
For every prime `p`:
`dedekindPsiReal p = p + 1` and `dedekindPsiReal p = φ(p) - 2 * μ(p)`. -/
theorem dedekindPsiReal_prime_eq_totient_sub_two_moebius {p : ℕ} (hp : Nat.Prime p) :
    dedekindPsiReal p = (p : ℝ) + 1 ∧
      dedekindPsiReal p = (Nat.totient p : ℝ) - 2 * moebiusReal p := by
  have hpsi : dedekindPsiReal p = (p : ℝ) + 1 := by
    have h := dedekindPsiReal_prime_pow_succ hp 0
    simpa using h
  refine ⟨hpsi, ?_⟩
  rw [hpsi, Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  have hmu : moebiusReal p = -1 := by
    unfold moebiusReal
    rw [ArithmeticFunction.moebius_apply_prime hp]
    norm_num
  rw [hmu]
  ring

/-- **Exact Prime Algebraic Bridge Between `jordanTotient2`, `φ`, and `μ`
(`jordanTotient2_prime_eq_totient_moebius`):**
For every prime `p`, the primitive energy weight `J₂(p)` is determined algebraically by the Selberg
variance weight `φ(p)` and the Bézout covariance weight `μ(p)`:
`J₂(p) = φ(p) * (φ(p) - 2 * μ(p)) = (φ(p) - μ(p))² - 1`. -/
theorem jordanTotient2_prime_eq_totient_moebius {p : ℕ} (hp : Nat.Prime p) :
    jordanTotient2 p =
      (Nat.totient p : ℝ) * ((Nat.totient p : ℝ) - 2 * moebiusReal p) ∧
    jordanTotient2 p =
      ((Nat.totient p : ℝ) - moebiusReal p) ^ (2 : ℕ) - 1 := by
  rw [jordanTotient2_eq_dedekindPsiReal_mul_totient p,
    (dedekindPsiReal_prime_eq_totient_sub_two_moebius hp).2]
  have hmu_sq : moebiusReal p ^ (2 : ℕ) = 1 := by
    unfold moebiusReal
    rw [ArithmeticFunction.moebius_apply_prime hp]
    norm_num
  refine ⟨ by ring, ?_ ⟩
  linarith [show ((Nat.totient p : ℝ) - moebiusReal p) ^ (2 : ℕ) =
    (Nat.totient p : ℝ) * ((Nat.totient p : ℝ) - 2 * moebiusReal p) + moebiusReal p ^ (2 : ℕ)
    by ring]

/-- **Wall 11 Separation Across All Five Canonical Modal Weights (`wall11_five_modal_weights_separation`):**
At the Wall 11 pair `(4, 6)` (`4 = 2²` vs. `6 = 2 · 3`):
1. **Selberg totient degeneracy**: `φ(4) = 2 = φ(6)`,
2. **Bézout Möbius separation**: `μ(4) = 0 ≠ 1 = μ(6)`,
3. **Bézout successor reserve separation**: `φ(4) - μ(4) = 2 ≠ 1 = φ(6) - μ(6)`,
4. **Irreducible phase-loss separation**: `φ(4) - μ(4)² / φ(4) = 2 ≠ 3 / 2 = φ(6) - μ(6)² / φ(6)`,
5. **Jordan primitive & Dedekind psi separation**: `J₂(4) = 12`, `J₂(6) = 24 = 2 * J₂(4)`,
   `ψ(4) = 6`, and `ψ(6) = 12 = 2 * ψ(4)`. -/
theorem wall11_five_modal_weights_separation :
    (Nat.totient 4 = 2 ∧ Nat.totient 6 = 2) ∧
    (moebiusReal 4 = 0 ∧ moebiusReal 6 = 1) ∧
    ((Nat.totient 4 : ℝ) - moebiusReal 4 = 2 ∧
      (Nat.totient 6 : ℝ) - moebiusReal 6 = 1) ∧
    ((Nat.totient 4 : ℝ) - moebiusReal 4 ^ (2 : ℕ) / (Nat.totient 4 : ℝ) = 2 ∧
      (Nat.totient 6 : ℝ) - moebiusReal 6 ^ (2 : ℕ) / (Nat.totient 6 : ℝ) = 3 / 2) ∧
    (jordanTotient2 4 = 12 ∧ jordanTotient2 6 = 24 ∧
      dedekindPsiReal 4 = 6 ∧ dedekindPsiReal 6 = 12) := by
  obtain ⟨ht4, ht6, hm4, hm6⟩ := wall11_totient_degeneracy_broken_by_bezout
  rw [ht4] at hm4
  rw [ht6] at hm6
  norm_num at hm4 hm6
  have hmu4 : moebiusReal 4 = 0 := by linarith
  have hmu6 : moebiusReal 6 = 1 := by linarith
  have hj4 : jordanTotient2 4 = 12 := by
    have h := jordanTotient2_prime_pow_succ Nat.prime_two 1
    norm_num at h
    exact h
  have hj2 : jordanTotient2 2 = 3 := by
    have h := jordanTotient2_prime_pow_succ Nat.prime_two 0
    norm_num at h
    exact h
  have hj3 : jordanTotient2 3 = 8 := by
    have h := jordanTotient2_prime_pow_succ Nat.prime_three 0
    norm_num at h
    exact h
  have hj6 : jordanTotient2 6 = 24 := by
    have h := jordanTotient2_mul_of_coprime (show Nat.Coprime 2 3 by decide)
    rw [hj2, hj3] at h
    norm_num at h ⊢
    exact h
  have hpsi4 : dedekindPsiReal 4 = 6 := by
    unfold dedekindPsiReal
    rw [hj4, ht4]
    norm_num
  have hpsi6 : dedekindPsiReal 6 = 12 := by
    unfold dedekindPsiReal
    rw [hj6, ht6]
    norm_num
  refine ⟨⟨ht4, ht6⟩, ⟨hmu4, hmu6⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨hj4, hj6, hpsi4, hpsi6⟩⟩ <;>
    · rw [ht4, ht6, hmu4, hmu6] at *
      norm_num

/-! ## §2. Sharp Prime-Attained Lower Bound `(q + 1) * φ(q) ≤ J₂(q)` & Parity-Split Primitive Energy Inequality -/

private theorem jordanTotient2_lower_aux (n : ℕ) :
    (n : ℝ) * (Nat.totient n : ℝ) ≤ jordanTotient2 n ∧
      (2 ≤ n → ((n : ℝ) + 1) * (Nat.totient n : ℝ) ≤ jordanTotient2 n) := by
  induction n using Nat.recOnPrimeCoprime with
  | zero =>
    simp [jordanTotient2]
  | prime_pow p k hp =>
    rcases k with _ | k
    · simp
    · rw [jordanTotient2_prime_pow_succ hp, Nat.totient_prime_pow_succ hp]
      push_cast [Nat.cast_sub hp.one_le]
      rw [pow_succ (p : ℝ) k]
      set A : ℝ := (p : ℝ) ^ k
      set P : ℝ := (p : ℝ)
      have hP2 : 2 ≤ P := show (2 : ℝ) ≤ (p : ℝ) by exact_mod_cast hp.two_le
      have hA1 : 1 ≤ A := one_le_pow₀ (by linarith)
      have hid : ((A * P) ^ (2 : ℕ) - A ^ (2 : ℕ)) - (A * P + 1) * (A * (P - 1)) =
          A * (P - 1) * (A - 1) := by
        ring
      have hnonneg : 0 ≤ A * (P - 1) * (A - 1) :=
        mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
      have hsharp : (A * P + 1) * (A * (P - 1)) ≤ (A * P) ^ (2 : ℕ) - A ^ (2 : ℕ) := by
        linarith
      have hphi0 : 0 ≤ A * (P - 1) := mul_nonneg (by linarith) (by linarith)
      exact ⟨by linarith, fun _ => hsharp⟩
  | coprime a b ha1 hb1 hab ha hb =>
    refine ⟨jordanTotient2_ge_mul_totient (a * b), fun hab2 => ?_⟩
    rcases eq_or_ne a 0 with rfl | ha0
    · simp [jordanTotient2]
    rcases eq_or_ne b 0 with rfl | hb0
    · simp [jordanTotient2]
    by_cases ha2 : 2 ≤ a
    · by_cases hb2 : 2 ≤ b
      · rw [jordanTotient2_mul_of_coprime hab, Nat.totient_mul hab, Nat.cast_mul, Nat.cast_mul]
        have ha_ge := ha.2 ha2
        have hb_ge := hb.2 hb2
        have ha_pos : 0 ≤ ((a : ℝ) + 1) * (Nat.totient a : ℝ) := by positivity
        have hb_pos : 0 ≤ ((b : ℝ) + 1) * (Nat.totient b : ℝ) := by positivity
        have hmul : (((a : ℝ) + 1) * (Nat.totient a : ℝ)) *
            (((b : ℝ) + 1) * (Nat.totient b : ℝ)) ≤
            jordanTotient2 a * jordanTotient2 b :=
          mul_le_mul ha_ge hb_ge hb_pos (ha_pos.trans ha_ge)
        have hphi_nonneg : 0 ≤ (Nat.totient a : ℝ) * (Nat.totient b : ℝ) := by positivity
        have haR : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
        have hbR : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
        have hexp :
            ((a : ℝ) * (b : ℝ) + 1) * ((Nat.totient a : ℝ) * (Nat.totient b : ℝ)) ≤
              (((a : ℝ) + 1) * (Nat.totient a : ℝ)) *
                (((b : ℝ) + 1) * (Nat.totient b : ℝ)) := by
          nlinarith
        exact hexp.trans hmul
      · have hb_eq : b = 1 := by omega
        subst hb_eq
        simpa using ha.2 ha2
    · have ha_eq : a = 1 := by omega
      subst ha_eq
      simpa using hb.2 (by simpa using hab2)

/-- **Sharp Prime-Attained Lower Bound on `jordanTotient2` (`add_one_mul_totient_le_jordanTotient2`):**
For every `q ≥ 2`, `(q + 1) * φ(q) ≤ J₂(q)`, with exact equality at every prime `q = p`
(where `(p + 1) * (p - 1) = p² - 1 = J₂(p)`). -/
theorem add_one_mul_totient_le_jordanTotient2 {q : ℕ} (hq : 2 ≤ q) :
    ((q : ℝ) + 1) * (Nat.totient q : ℝ) ≤ jordanTotient2 q :=
  (jordanTotient2_lower_aux q).2 hq

/-- **Sharp Lower Bound on `dedekindPsiReal` (`add_one_le_dedekindPsiReal`):**
For every `q ≥ 2`, `q + 1 ≤ dedekindPsiReal q`, with exact equality at every prime `q = p`. -/
theorem add_one_le_dedekindPsiReal {q : ℕ} (hq : 2 ≤ q) :
    (q : ℝ) + 1 ≤ dedekindPsiReal q := by
  unfold dedekindPsiReal
  have hphi : (0 : ℝ) < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  exact (le_div_iff₀ hphi).mpr (add_one_mul_totient_le_jordanTotient2 hq)

/-- **Sharp Parity-Split Lower Bound on `sievePrimitiveEnergy`
(`three_mul_sieveVariance_add_above_parity_le_twelve_mul_sievePrimitiveEnergy`):**
For every cutoff `N : ℕ` and every weight `c : ℕ → ℝ`:
`3 * sieveVariance N c + sieveVarianceAboveParity N c ≤ 12 * sievePrimitiveEnergy N c`,
and at `N = 3` equality holds identically for every weight `c`. -/
theorem three_mul_sieveVariance_add_above_parity_le_twelve_mul_sievePrimitiveEnergy
    (N : ℕ) (c : ℕ → ℝ) :
    3 * sieveVariance N c + sieveVarianceAboveParity N c ≤
      12 * sievePrimitiveEnergy N c ∧
    3 * sieveVariance 3 c + sieveVarianceAboveParity 3 c =
      12 * sievePrimitiveEnergy 3 c := by
  refine ⟨?_, ?_⟩
  · rcases le_or_gt 2 N with hN2 | hN2
    · have hsplit : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
        ext q; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have hnot : (2 : ℕ) ∉ Finset.Icc 3 N := by
        simp only [Finset.mem_Icc]; omega
      rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]
      unfold sieveVariance sieveVarianceAboveParity
      rw [hsplit, Finset.sum_insert hnot, Finset.sum_insert hnot]
      have hj2 : jordanTotient2 2 = 3 * (Nat.totient 2 : ℝ) := by
        have h := jordanTotient2_prime_pow_succ Nat.prime_two 0
        norm_num [Nat.totient_two] at h ⊢
        exact h
      have hsum :
          4 * (∑ q ∈ Finset.Icc 3 N,
            (Nat.totient q : ℝ) * (selbergMultiplesCoord N c q) ^ (2 : ℕ)) ≤
          ∑ q ∈ Finset.Icc 3 N,
            jordanTotient2 q * (selbergMultiplesCoord N c q) ^ (2 : ℕ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun q hq => ?_
        obtain ⟨hq3, _⟩ := Finset.mem_Icc.mp hq
        have hqR : (4 : ℝ) ≤ (q : ℝ) + 1 := by
          have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq3
          linarith
        have h4 : 4 * (Nat.totient q : ℝ) ≤ jordanTotient2 q := by
          calc
            4 * (Nat.totient q : ℝ)
              ≤ ((q : ℝ) + 1) * (Nat.totient q : ℝ) :=
                mul_le_mul_of_nonneg_right hqR (Nat.cast_nonneg _)
            _ ≤ jordanTotient2 q := add_one_mul_totient_le_jordanTotient2 (by omega)
        have hmul := mul_le_mul_of_nonneg_right h4 (sq_nonneg (selbergMultiplesCoord N c q))
        linarith
      rw [hj2]
      linarith
    · have hI2 : Finset.Icc 2 N = ∅ := Finset.Icc_eq_empty (by omega)
      have hI3 : Finset.Icc 3 N = ∅ := Finset.Icc_eq_empty (by omega)
      rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]
      unfold sieveVariance sieveVarianceAboveParity
      simp [hI2, hI3]
  · rw [twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal]
    unfold sieveVariance sieveVarianceAboveParity
    have hsplit : Finset.Icc 2 3 = insert 2 (Finset.Icc 3 3) := by
      ext q; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : (2 : ℕ) ∉ Finset.Icc 3 3 := by simp
    rw [hsplit, Finset.sum_insert hnot, Finset.sum_insert hnot, Finset.Icc_self,
      Finset.sum_singleton, Finset.sum_singleton]
    have hj2 : jordanTotient2 2 = 3 := by
      have h := jordanTotient2_prime_pow_succ Nat.prime_two 0
      norm_num at h
      exact h
    have hj3 : jordanTotient2 3 = 8 := by
      have h := jordanTotient2_prime_pow_succ Nat.prime_three 0
      norm_num at h
      exact h
    rw [hj2, hj3, Nat.totient_two, Nat.totient_prime Nat.prime_three]
    norm_num
    ring

/-- **Direct Lower Bound on `12 * sievePrimitiveEnergy` via `sieveVariance` and `successorPhaseLoss`
(`three_mul_sieveVariance_add_phaseLoss_le_twelve_mul_sievePrimitiveEnergy`):**
For every cutoff `N : ℕ` and every weight `c : ℕ → ℝ`:
`3 * sieveVariance N c + successorPhaseLoss N c ≤ 12 * sievePrimitiveEnergy N c`. -/
theorem three_mul_sieveVariance_add_phaseLoss_le_twelve_mul_sievePrimitiveEnergy
    (N : ℕ) (c : ℕ → ℝ) :
    3 * sieveVariance N c + successorPhaseLoss N c ≤
      12 * sievePrimitiveEnergy N c := by
  have h1 := (three_mul_sieveVariance_add_above_parity_le_twelve_mul_sievePrimitiveEnergy N c).1
  have h2 := (successorPhaseLoss_bounds N c).2
  linarith

/-! ## §3. Gcd-Orbit Projection of `successorPhaseLoss` & Master Five-Form Spectral Synthesis -/

/-- **Gcd-Orbit Projection & Simultaneous Pythagoras for `successorPhaseLoss`
(`successorPhaseLoss_gcdProjection_and_pythagoras`):**
For every cutoff `N : ℕ`, stride `h : ℕ`, and weight `c : ℕ → ℝ`, the gcd-orbit projection
`Γ_h c = sieveGcdProjection N h c` restricts the Selberg diagonal of `successorPhaseLoss` to
resonant modes `q ∈ [2, N]` with `q ∣ h`, decomposes `successorPhaseLoss N c` additively into its
resonant (`q ∣ h`) and non-resonant (`¬ q ∣ h`) parts, and contracts `successorPhaseLoss`. -/
theorem successorPhaseLoss_gcdProjection_and_pythagoras (N h : ℕ) (c : ℕ → ℝ) :
    successorPhaseLoss N (sieveGcdProjection N h c) =
      (∑ q ∈ (Finset.Icc 2 N).filter (fun q => q ∣ h),
        ((Nat.totient q : ℝ) - moebiusReal q ^ (2 : ℕ) / (Nat.totient q : ℝ)) *
          (selbergMultiplesCoord N c q) ^ (2 : ℕ)) ∧
    successorPhaseLoss N c =
      successorPhaseLoss N (sieveGcdProjection N h c) +
        successorPhaseLoss N (fun d => c d - sieveGcdProjection N h c d) ∧
    successorPhaseLoss N (sieveGcdProjection N h c) ≤ successorPhaseLoss N c := by
  have hIcc2 : ∀ b : ℕ → ℝ,
      successorPhaseLoss N b =
        ∑ q ∈ Finset.Icc 2 N,
          ((Nat.totient q : ℝ) - moebiusReal q ^ (2 : ℕ) / (Nat.totient q : ℝ)) *
            (selbergMultiplesCoord N b q) ^ (2 : ℕ) := by
    intro b
    unfold successorPhaseLoss
    symm
    apply Finset.sum_subset
    · intro q hq
      exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hq).1; omega,
        (Finset.mem_Icc.mp hq).2⟩
    · intro q hq hn
      have hq1 : q = 1 := by simp only [Finset.mem_Icc] at hq hn; omega
      subst hq1
      norm_num [moebiusReal]
  have hdiag :
      successorPhaseLoss N (sieveGcdProjection N h c) =
        ∑ q ∈ (Finset.Icc 2 N).filter (fun q => q ∣ h),
          ((Nat.totient q : ℝ) - moebiusReal q ^ (2 : ℕ) / (Nat.totient q : ℝ)) *
            (selbergMultiplesCoord N c q) ^ (2 : ℕ) := by
    rw [hIcc2]
    exact sum_selbergMultiplesCoord_gcdProjection_sq N h
      (fun q => (Nat.totient q : ℝ) - moebiusReal q ^ (2 : ℕ) / (Nat.totient q : ℝ)) c
  have hcomp :
      successorPhaseLoss N (fun d => c d - sieveGcdProjection N h c d) =
        ∑ q ∈ (Finset.Icc 2 N).filter (fun q => ¬ q ∣ h),
          ((Nat.totient q : ℝ) - moebiusReal q ^ (2 : ℕ) / (Nat.totient q : ℝ)) *
            (selbergMultiplesCoord N c q) ^ (2 : ℕ) := by
    rw [hIcc2]
    exact sum_selbergMultiplesCoord_sub_gcdProjection_sq N h
      (fun q => (Nat.totient q : ℝ) - moebiusReal q ^ (2 : ℕ) / (Nat.totient q : ℝ)) c
  have hpyth :
      successorPhaseLoss N c =
        successorPhaseLoss N (sieveGcdProjection N h c) +
          successorPhaseLoss N (fun d => c d - sieveGcdProjection N h c d) := by
    rw [hIcc2 c, hdiag, hcomp]
    exact (Finset.sum_filter_add_sum_filter_not (Finset.Icc 2 N) (fun q => q ∣ h)
      (fun q => ((Nat.totient q : ℝ) - moebiusReal q ^ (2 : ℕ) / (Nat.totient q : ℝ)) *
        (selbergMultiplesCoord N c q) ^ (2 : ℕ))).symm
  have hnonneg :
      0 ≤ successorPhaseLoss N (fun d => c d - sieveGcdProjection N h c d) := by
    have habove :
        0 ≤ sieveVarianceAboveParity N (fun d => c d - sieveGcdProjection N h c d) :=
      Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
    linarith [(successorPhaseLoss_bounds N (fun d => c d - sieveGcdProjection N h c d)).1]
  exact ⟨hdiag, hpyth, by linarith⟩

/-- **Master Five-Form Spectral & Valuation Synthesis of `BezoutValuationIncidence`
(`bezoutValuationIncidence_master_five_form_synthesis`):**
For every cutoff `N ≥ 1`, weight `c : ℕ → ℝ`, and stride `h : ℕ`, the five fundamental quadratic
forms of **Bézout–Valuation Incidence Mechanics**:
1. `sieveVariance N c` (modal weight `φ(q)`),
2. `sieveSuccessorCovariance N c` (modal weight `μ(q)`),
3. `sieveSuccessorReserve N c` (modal weight `φ(q) - μ(q)`),
4. `successorPhaseLoss N c` (modal weight `φ(q) - μ(q)² / φ(q)`),
5. `12 * sievePrimitiveEnergy N c` (modal weight `J₂(q) = ψ(q) * φ(q)`),
are simultaneously diagonalized in the Selberg multiples basis `selbergMultiplesCoord N c`,
simultaneously split orthogonally by the gcd-orbit projection `sieveGcdProjection N h c`, and linked
by the universal inequality chain:
- `(3 / 4) * sieveVarianceAboveParity N c ≤ successorPhaseLoss N c ≤ sieveVarianceAboveParity N c`,
- `(1 / 2) * sieveVariance N c ≤ sieveSuccessorReserve N c ≤ 2 * sieveVariance N c`,
- `3 * sieveVariance N c + successorPhaseLoss N c ≤ 3 * sieveVariance N c + sieveVarianceAboveParity N c ≤ 12 * sievePrimitiveEnergy N c`,
- `16 * sievePrimitiveEnergy N c ≤ N² * sieveVariance N c`. -/
theorem bezoutValuationIncidence_master_five_form_synthesis
    {N : ℕ} (hN : 1 ≤ N) (h : ℕ) (c : ℕ → ℝ) :
    (sieveVariance N c =
        (∑ q ∈ Finset.Icc 2 N,
          (Nat.totient q : ℝ) * (selbergMultiplesCoord N c q) ^ (2 : ℕ)) ∧
      sieveSuccessorCovariance N c =
        (∑ q ∈ Finset.Icc 2 N,
          moebiusReal q * (selbergMultiplesCoord N c q) ^ (2 : ℕ)) ∧
      sieveSuccessorReserve N c =
        (∑ q ∈ Finset.Icc 2 N,
          ((Nat.totient q : ℝ) - moebiusReal q) * (selbergMultiplesCoord N c q) ^ (2 : ℕ)) ∧
      successorPhaseLoss N c =
        (∑ q ∈ Finset.Icc 3 N,
          ((Nat.totient q : ℝ) - moebiusReal q ^ (2 : ℕ) / (Nat.totient q : ℝ)) *
            (selbergMultiplesCoord N c q) ^ (2 : ℕ)) ∧
      12 * sievePrimitiveEnergy N c =
        (∑ q ∈ Finset.Icc 2 N,
          jordanTotient2 q * (selbergMultiplesCoord N c q) ^ (2 : ℕ))) ∧
    (sieveVariance N c =
        sieveVariance N (sieveGcdProjection N h c) +
          sieveVariance N (fun d => c d - sieveGcdProjection N h c d) ∧
      sieveSuccessorReserve N c =
        sieveSuccessorReserve N (sieveGcdProjection N h c) +
          sieveSuccessorReserve N (fun d => c d - sieveGcdProjection N h c d) ∧
      successorPhaseLoss N c =
        successorPhaseLoss N (sieveGcdProjection N h c) +
          successorPhaseLoss N (fun d => c d - sieveGcdProjection N h c d) ∧
      sievePrimitiveEnergy N c =
        sievePrimitiveEnergy N (sieveGcdProjection N h c) +
          sievePrimitiveEnergy N (fun d => c d - sieveGcdProjection N h c d)) ∧
    ((3 / 4 : ℝ) * sieveVarianceAboveParity N c ≤ successorPhaseLoss N c ∧
      successorPhaseLoss N c ≤ sieveVarianceAboveParity N c ∧
      (1 / 2 : ℝ) * sieveVariance N c ≤ sieveSuccessorReserve N c ∧
      sieveSuccessorReserve N c ≤ 2 * sieveVariance N c ∧
      3 * sieveVariance N c + successorPhaseLoss N c ≤
        3 * sieveVariance N c + sieveVarianceAboveParity N c ∧
      3 * sieveVariance N c + sieveVarianceAboveParity N c ≤
        12 * sievePrimitiveEnergy N c ∧
      16 * sievePrimitiveEnergy N c ≤ (N : ℝ) ^ (2 : ℕ) * sieveVariance N c) := by
  have hpyth := sieveGcdProjection_simultaneous_pythagoras N h c
  have hloss_pyth := (successorPhaseLoss_gcdProjection_and_pythagoras N h c).2.1
  have hloss_bds := successorPhaseLoss_bounds N c
  have hres_diag :
      sieveSuccessorReserve N c =
        ∑ q ∈ Finset.Icc 2 N,
          ((Nat.totient q : ℝ) - moebiusReal q) * (selbergMultiplesCoord N c q) ^ (2 : ℕ) := by
    unfold sieveSuccessorReserve
    exact selbergSubBezoutQuadraticForm_eq_Icc_two hN c
  have hres_bds := successor_energy_variance_bounds N c
  have hres_low : (1 / 2 : ℝ) * sieveVariance N c ≤ sieveSuccessorReserve N c := by
    unfold sieveSuccessorReserve
    linarith [hres_bds.1]
  have hres_high : sieveSuccessorReserve N c ≤ 2 * sieveVariance N c := by
    unfold sieveSuccessorReserve
    linarith [hres_bds.2]
  refine ⟨⟨rfl, sieveSuccessorCovariance_eq_diagonal N c, hres_diag,
      successorPhaseLoss_eq_above_parity N c,
      twelve_mul_sievePrimitiveEnergy_eq_jordan_diagonal N c⟩,
    ⟨hpyth.1, hpyth.2.1, hloss_pyth, hpyth.2.2.1⟩,
    ⟨hloss_bds.1, hloss_bds.2, hres_low, hres_high, by linarith [hloss_bds.2],
      (three_mul_sieveVariance_add_above_parity_le_twelve_mul_sievePrimitiveEnergy N c).1,
      (sixteen_mul_sievePrimitiveEnergy_le_sq_mul_sieveVariance N c).1⟩⟩

end
end GaloisForLFunctions.BezoutValuationIncidence
