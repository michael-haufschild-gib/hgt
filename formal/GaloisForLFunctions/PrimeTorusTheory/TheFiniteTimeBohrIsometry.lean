import GaloisForLFunctions.PrimeTorusTheory.TheOrbitOfAPhaseSystem
import GaloisForLFunctions.HTGeometry.LogFrequencySeparation
import GaloisForLFunctions.HTGeometry.TrigonometricSumWindowMean

/-!
# The finite-time Bohr isometry

For a Dirichlet series the supremum over the orbit is the supremum over the torus, and at finite time
this has a price. Here is the price, with no input from linear forms in logarithms.

**Theorem** (`exists_column_ge`). Let `P ⊆ Q` be finite sets of primes, `Y ≥ max Q`, `m ≥ 1`,
`D = Π_{p∈P} p^m`, `τ = (m+1)^{|P|}` the number of divisors of `D`, and `0 < η ≤ 1`. For every target
direction `θ` and every window `[T, T + L]` with `2(Y + 1) τ D < η L` there is a time `t` in the window with

`Σ_{r∈Q} a_r cos(t log r − θ_r) ≥ (m/(m+1)) Σ_{p∈P} a_p − η Σ_{r∈Q} a_r`.

**Mechanism.** The Fejér product `Π_{p∈P} |Σ_{j≤m} e^{ij(t log p − θ_p)}|²` is `|R(t)|²` for the
Dirichlet polynomial `R = Σ_{n∣D} c(n) n^{it}` with unimodular completely multiplicative coefficients. So
it is nonnegative, and its window integrals have an exact main term and an off-diagonal error
bounded with `|log a − log b| ≥ 1/max(a,b)`, the integrality of the frequencies. Only the pairs `nr = n'`
survive, and there are `(m/(m+1)) τ` of them for `r ∈ P`, none for `r ∉ P`.

Taking `P` the primes up to `y`, `D ≤ 4^{my}` and `τ ≤ (m+1)^y` (`exists_column_ge_of_primesLE`): every window of
length `exp(c_m y)` meets every half-space of the torus on the primes up to `y` at level `m/(m+1)`. This
is the **Kronecker scale** `y ≍ log T`. Its constant is linear in `y`, whereas a bound through linear forms
in logarithms is exponential in `y`.
-/

open Complex Finset

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The phase `n^{it}`. -/
def nPhase (n : ℕ) (t : ℝ) : ℂ := cexp (I * ((Real.log n : ℝ) * (t : ℝ)))

theorem continuous_nPhase (n : ℕ) : Continuous (nPhase n) := by
  unfold nPhase
  fun_prop

theorem norm_nPhase (n : ℕ) (t : ℝ) : ‖nPhase n t‖ = 1 := by
  unfold nPhase
  rw [show I * (((Real.log n : ℝ) : ℂ) * (t : ℂ)) = ((Real.log n * t : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem conj_nPhase (n : ℕ) (t : ℝ) :
    (starRingEnd ℂ) (nPhase n t) = cexp (I * ((-(Real.log n) : ℝ) * (t : ℝ))) := by
  unfold nPhase
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- The resonator `R(t) = Σ_{n∈A} c(n) n^{it}`. -/
def resonator (A : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℂ := ∑ n ∈ A, c n * nPhase n t

/-- The kernel `|R(t)|² ≥ 0`. -/
def resonatorKernel (A : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℝ := ‖resonator A c t‖ ^ 2

theorem continuous_resonator (A : Finset ℕ) (c : ℕ → ℂ) : Continuous (resonator A c) := by
  unfold resonator
  exact continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_nPhase n)

theorem continuous_resonatorKernel (A : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (resonatorKernel A c) := by
  unfold resonatorKernel
  exact (continuous_norm.comp (continuous_resonator A c)).pow 2

theorem resonatorKernel_nonneg (A : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    0 ≤ resonatorKernel A c t := by
  unfold resonatorKernel
  positivity

/-- The kernel times a phase is a double sum of pure exponentials. -/
theorem resonatorKernel_mul_nPhase {A : Finset ℕ} (hA : ∀ n ∈ A, 0 < n) (c : ℕ → ℂ) {q : ℕ}
    (hq : 0 < q) (t : ℝ) :
    (resonatorKernel A c t : ℂ) * nPhase q t =
      ∑ n ∈ A, ∑ n' ∈ A, c n * (starRingEnd ℂ) (c n') *
        cexp (I * (((Real.log (n * q : ℕ) - Real.log n' : ℝ) : ℂ) * (t : ℂ))) := by
  have hK : (resonatorKernel A c t : ℂ) =
      resonator A c t * (starRingEnd ℂ) (resonator A c t) := by
    rw [resonatorKernel, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hK]
  unfold resonator
  rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun n' _ => ?_
  rw [map_mul, conj_nPhase]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (hA n hn).ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hlog : Real.log (n * q : ℕ) = Real.log n + Real.log q := by
    push_cast
    exact Real.log_mul hn0 hq0
  have e : cexp (I * (((Real.log (n * q : ℕ) - Real.log n' : ℝ) : ℂ) * (t : ℂ))) =
      nPhase n t * cexp (I * ((-(Real.log n') : ℝ) * (t : ℝ))) * nPhase q t := by
    unfold nPhase
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [hlog]
    push_cast
    ring
  rw [e]
  ring

/-- **The window integral of the kernel against a phase**: an exact main term from `nq = n'`, and an
error bounded by the integrality of the frequencies. -/
theorem norm_integral_resonatorKernel_sub_le {A : Finset ℕ} (hA : ∀ n ∈ A, 0 < n) {c : ℕ → ℂ}
    (hc : ∀ n ∈ A, ‖c n‖ ≤ 1) {q M : ℕ} (hq : 0 < q) (hM : ∀ n ∈ A, n ≤ M) (T L : ℝ) :
    ‖(∫ t in T..T + L, (resonatorKernel A c t : ℂ) * nPhase q t) -
        (L : ℂ) * ∑ n ∈ A, ∑ n' ∈ A, if n * q = n' then c n * (starRingEnd ℂ) (c n') else 0‖ ≤
      (A.card : ℝ) ^ 2 * (2 * ((q * M : ℕ) : ℝ)) := by
  have hexp : ∀ n n' : ℕ, Continuous fun t : ℝ =>
      c n * (starRingEnd ℂ) (c n') *
        cexp (I * (((Real.log (n * q : ℕ) - Real.log n' : ℝ) : ℂ) * (t : ℂ))) := by
    intro n n'
    fun_prop
  have hint : (∫ t in T..T + L, (resonatorKernel A c t : ℂ) * nPhase q t) =
      ∑ n ∈ A, ∑ n' ∈ A, c n * (starRingEnd ℂ) (c n') *
        ∫ t in T..T + L, cexp (I * (((Real.log (n * q : ℕ) - Real.log n' : ℝ) : ℂ) * (t : ℂ))) := by
    simp_rw [resonatorKernel_mul_nPhase hA c hq]
    rw [intervalIntegral.integral_finsetSum fun n _ =>
      (continuous_finsetSum _ fun n' _ => hexp n n').intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_finsetSum fun n' _ => (hexp n n').intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun n' _ => ?_
    rw [intervalIntegral.integral_const_mul]
  rw [hint, Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hterm : ∀ n ∈ A, ∀ n' ∈ A,
      ‖c n * (starRingEnd ℂ) (c n') *
          (∫ t in T..T + L, cexp (I * (((Real.log (n * q : ℕ) - Real.log n' : ℝ) : ℂ) * (t : ℂ)))) -
        (L : ℂ) * if n * q = n' then c n * (starRingEnd ℂ) (c n') else 0‖ ≤
        2 * ((q * M : ℕ) : ℝ) := by
    intro n hn n' hn'
    have hbound : (0 : ℝ) ≤ 2 * ((q * M : ℕ) : ℝ) := by positivity
    by_cases he : n * q = n'
    · subst he
      simp only [if_true, sub_self, Complex.ofReal_zero, zero_mul, mul_zero, Complex.exp_zero]
      simp only [intervalIntegral.integral_const, add_sub_cancel_left, Complex.real_smul,
        mul_one]
      rw [mul_comm, sub_self, norm_zero]
      exact hbound
    · rw [if_neg he, mul_zero, sub_zero, norm_mul, norm_mul, Complex.norm_conj]
      have hnq : 0 < n * q := Nat.mul_pos (hA n hn) hq
      have hgap := HTGeometry.inv_max_le_abs_log_sub_log hnq (hA n' hn') he
      have hmaxpos : (0 : ℝ) < ((max (n * q) n' : ℕ) : ℝ) := by
        have : 0 < max (n * q) n' := lt_max_of_lt_left hnq
        exact_mod_cast this
      have hγ : Real.log (n * q : ℕ) - Real.log n' ≠ 0 := by
        intro h0
        rw [h0, abs_zero] at hgap
        exact absurd hgap (not_le.mpr (by positivity))
      have hI := TrigSum.norm_integral_exp_I_mul_le _ hγ T L
      have hmax : ((max (n * q) n' : ℕ) : ℝ) ≤ ((q * M : ℕ) : ℝ) := by
        have h1 : n * q ≤ q * M := by
          rw [mul_comm]
          exact Nat.mul_le_mul_left q (hM n hn)
        have h2 : n' ≤ q * M := (hM n' hn').trans (Nat.le_mul_of_pos_left M hq)
        exact_mod_cast max_le h1 h2
      have h2g : 2 / |Real.log (n * q : ℕ) - Real.log n'| ≤ 2 * ((q * M : ℕ) : ℝ) := by
        have hpos : 0 < |Real.log (n * q : ℕ) - Real.log n'| := abs_pos.mpr hγ
        rw [div_le_iff₀ hpos]
        have h3 : (1 : ℝ) ≤ ((max (n * q) n' : ℕ) : ℝ) * |Real.log (n * q : ℕ) - Real.log n'| := by
          have := mul_le_mul_of_nonneg_left hgap hmaxpos.le
          rwa [mul_inv_cancel₀ hmaxpos.ne'] at this
        nlinarith [abs_nonneg (Real.log (n * q : ℕ) - Real.log n')]
      have hcc : ‖c n‖ * ‖c n'‖ ≤ 1 := by
        have h1 := hc n hn
        have h2 := hc n' hn'
        have h3 := norm_nonneg (c n)
        have h4 := norm_nonneg (c n')
        nlinarith
      calc
        ‖c n‖ * ‖c n'‖ * ‖∫ t in T..T + L,
            cexp (I * (((Real.log (n * q : ℕ) - Real.log n' : ℝ) : ℂ) * (t : ℂ)))‖
            ≤ 1 * (2 * ((q * M : ℕ) : ℝ)) :=
              mul_le_mul hcc (hI.trans h2g) (norm_nonneg _) zero_le_one
        _ = 2 * ((q * M : ℕ) : ℝ) := one_mul _
  calc
    ‖∑ n ∈ A, ((∑ n' ∈ A, c n * (starRingEnd ℂ) (c n') *
          ∫ t in T..T + L, cexp (I * (((Real.log (n * q : ℕ) - Real.log n' : ℝ) : ℂ) * (t : ℂ)))) -
        (L : ℂ) * ∑ n' ∈ A, if n * q = n' then c n * (starRingEnd ℂ) (c n') else 0)‖
        ≤ ∑ n ∈ A, ‖(∑ n' ∈ A, c n * (starRingEnd ℂ) (c n') *
          ∫ t in T..T + L, cexp (I * (((Real.log (n * q : ℕ) - Real.log n' : ℝ) : ℂ) * (t : ℂ)))) -
        (L : ℂ) * ∑ n' ∈ A, if n * q = n' then c n * (starRingEnd ℂ) (c n') else 0‖ :=
          norm_sum_le _ _
    _ ≤ ∑ _n ∈ A, (A.card : ℝ) * (2 * ((q * M : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine (norm_sum_le _ _).trans ?_
        have := Finset.sum_le_card_nsmul A _ _ (hterm n hn)
        rwa [nsmul_eq_mul] at this
    _ = (A.card : ℝ) ^ 2 * (2 * ((q * M : ℕ) : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring

/-! ### The divisor resonator of a target direction -/

/-- The modulus `D = Π_{p∈P} p^m`. -/
def boxModulus (P : Finset ℕ) (m : ℕ) : ℕ := ∏ p ∈ P, p ^ m

theorem boxModulus_pos {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (m : ℕ) : 0 < boxModulus P m :=
  Finset.prod_pos fun p hp => pow_pos (hP p hp).pos m

theorem coprime_pow_boxModulus_erase {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {q : ℕ} (hq : q ∈ P)
    (i m : ℕ) : (q ^ i).Coprime (boxModulus (P.erase q) m) := by
  unfold boxModulus
  refine Nat.Coprime.prod_right fun p hp => ?_
  refine Nat.Coprime.pow _ _ ?_
  exact (Nat.coprime_primes (hP q hq) (hP p (Finset.mem_of_mem_erase hp))).mpr
    (Finset.ne_of_mem_erase hp).symm

theorem boxModulus_eq_pow_mul {P : Finset ℕ} {q : ℕ} (hq : q ∈ P) (m : ℕ) :
    boxModulus P m = q ^ m * boxModulus (P.erase q) m := by
  unfold boxModulus
  exact (Finset.mul_prod_erase P (fun p => p ^ m) hq).symm

/-- `D` has `(m + 1)^{|P|}` divisors. -/
theorem card_divisors_boxModulus {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (m : ℕ) :
    (boxModulus P m).divisors.card = (m + 1) ^ P.card := by
  classical
  induction P using Finset.induction_on with
  | empty => simp [boxModulus]
  | insert a s ha ih =>
    have hP' : ∀ p ∈ s, p.Prime := fun p hp => hP p (Finset.mem_insert_of_mem hp)
    have hmem : a ∈ insert a s := Finset.mem_insert_self a s
    have he : (insert a s).erase a = s := Finset.erase_insert ha
    have hcop := coprime_pow_boxModulus_erase hP hmem m m
    rw [he] at hcop
    rw [boxModulus_eq_pow_mul hmem, he, Nat.Coprime.card_divisors_mul hcop,
      Nat.divisors_prime_pow (hP a hmem), ih hP', Finset.card_map, Finset.card_range,
      Finset.card_insert_of_notMem ha, pow_succ]
    ring

open Classical in
/-- The divisors `n` of `D` with `qn ∣ D`: there are `m (m + 1)^{|P|−1}` of them for `q ∈ P`. -/
theorem card_filter_mul_mem_divisors {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {q : ℕ} (hq : q ∈ P)
    {m : ℕ} (hm : 1 ≤ m) :
    (((boxModulus P m).divisors.filter fun n => n * q ∈ (boxModulus P m).divisors).card) * (m + 1) =
      m * (boxModulus P m).divisors.card := by
  have hq' : q.Prime := hP q hq
  have hq0 : 0 < q := hq'.pos
  have hPe : ∀ p ∈ P.erase q, p.Prime := fun p hp => hP p (Finset.mem_of_mem_erase hp)
  obtain ⟨l, rfl⟩ : ∃ l, m = l + 1 := ⟨m - 1, by omega⟩
  set E := boxModulus (P.erase q) (l + 1) with hE
  have hE0 : E ≠ 0 := (boxModulus_pos hPe _).ne'
  have hD : boxModulus P (l + 1) = q ^ (l + 1) * E := boxModulus_eq_pow_mul hq _
  have hset : ((boxModulus P (l + 1)).divisors.filter
      fun n => n * q ∈ (boxModulus P (l + 1)).divisors) = (q ^ l * E).divisors := by
    ext n
    have hD0 : q ^ (l + 1) * E ≠ 0 := mul_ne_zero (pow_pos hq0 _).ne' hE0
    have hl0 : q ^ l * E ≠ 0 := mul_ne_zero (pow_pos hq0 _).ne' hE0
    simp only [Finset.mem_filter, Nat.mem_divisors, hD]
    constructor
    · rintro ⟨-, h, -⟩
      refine ⟨?_, hl0⟩
      have e : q ^ (l + 1) * E = q ^ l * E * q := by ring
      rw [e] at h
      exact Nat.dvd_of_mul_dvd_mul_right hq0 h
    · rintro ⟨h, -⟩
      have e : q ^ (l + 1) * E = q ^ l * E * q := by ring
      refine ⟨⟨h.trans ?_, hD0⟩, ?_, hD0⟩
      · rw [e]
        exact Dvd.intro _ rfl
      · rw [e]
        exact Nat.mul_dvd_mul_right h q
  have hcop := coprime_pow_boxModulus_erase hP hq l (l + 1)
  have hcop2 := coprime_pow_boxModulus_erase hP hq (l + 1) (l + 1)
  rw [hset, hD, Nat.Coprime.card_divisors_mul hcop, Nat.Coprime.card_divisors_mul hcop2,
    Nat.divisors_prime_pow hq', Nat.divisors_prime_pow hq', Finset.card_map, Finset.card_map,
    Finset.card_range, Finset.card_range]
  ring

/-- A prime outside `P` does not divide `D`. -/
theorem not_dvd_boxModulus {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {r : ℕ} (hr : r.Prime)
    (hrP : r ∉ P) (m : ℕ) : ¬ r ∣ boxModulus P m := by
  unfold boxModulus
  rw [hr.prime.dvd_finsetProd_iff]
  rintro ⟨p, hp, hd⟩
  have := (Nat.prime_dvd_prime_iff_eq hr (hP p hp)).mp (hr.dvd_of_dvd_pow hd)
  exact hrP (this ▸ hp)

/-- The target coefficient `c(n) = exp(−i Σ_{p∈P} v_p(n) θ_p)`, completely multiplicative and unimodular. -/
def targetCoeff (P : Finset ℕ) (θ : ℕ → ℝ) (n : ℕ) : ℂ :=
  cexp (((-(∑ p ∈ P, (n.factorization p : ℝ) * θ p) : ℝ) : ℂ) * I)

/-- The unit `e^{−iθ}`. -/
def unitPhase (θ : ℝ) : ℂ := cexp (((-θ : ℝ) : ℂ) * I)

theorem norm_targetCoeff (P : Finset ℕ) (θ : ℕ → ℝ) (n : ℕ) : ‖targetCoeff P θ n‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem norm_unitPhase (θ : ℝ) : ‖unitPhase θ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

/-- Multiplying by a prime of `P` multiplies the target coefficient by the target phase of that prime. -/
theorem targetCoeff_mul_prime {P : Finset ℕ} (θ : ℕ → ℝ) {n q : ℕ} (hn : n ≠ 0) (hq : q.Prime)
    (hqP : q ∈ P) : targetCoeff P θ (n * q) = targetCoeff P θ n * unitPhase (θ q) := by
  unfold targetCoeff unitPhase
  rw [← Complex.exp_add]
  congr 1
  have e : ∑ p ∈ P, ((n * q).factorization p : ℝ) * θ p =
      ∑ p ∈ P, (n.factorization p : ℝ) * θ p + θ q := by
    have h1 : ∀ p, ((n * q).factorization p : ℝ) =
        (n.factorization p : ℝ) + if p = q then 1 else 0 := by
      intro p
      rw [Nat.factorization_mul hn hq.ne_zero, hq.factorization]
      simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_apply]
      by_cases h : p = q
      · simp [h]
      · simp [h, Ne.symm h]
    simp_rw [h1, add_mul, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' P q, if_pos hqP]
  rw [e]
  push_cast
  ring

/-- `cexp(−iθ)` times `e^{i x}` read in real part. -/
theorem re_unitPhase_mul_nPhase (θ : ℝ) (q : ℕ) (t : ℝ) :
    (unitPhase θ * nPhase q t).re = Real.cos (t * Real.log q - θ) := by
  unfold unitPhase nPhase
  rw [← Complex.exp_add]
  have e : ((-θ : ℝ) : ℂ) * I + I * (((Real.log q : ℝ) : ℂ) * (t : ℂ)) =
      ((t * Real.log q - θ : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [e, Complex.exp_ofReal_mul_I_re]

/-- The real window integral of the kernel against a cosine is read from the complex one. -/
theorem integral_kernel_mul_cos (A : Finset ℕ) (c : ℕ → ℂ) (q : ℕ) (θ T L : ℝ) :
    ∫ t in T..T + L, resonatorKernel A c t * Real.cos (t * Real.log q - θ) =
      (unitPhase θ * ∫ t in T..T + L, (resonatorKernel A c t : ℂ) * nPhase q t).re := by
  have hcont : Continuous fun t : ℝ => unitPhase θ * ((resonatorKernel A c t : ℂ) * nPhase q t) :=
    continuous_const.mul
      ((Complex.continuous_ofReal.comp (continuous_resonatorKernel A c)).mul (continuous_nPhase q))
  have hre : (unitPhase θ * ∫ t in T..T + L, (resonatorKernel A c t : ℂ) * nPhase q t).re =
      ∫ t in T..T + L, (unitPhase θ * ((resonatorKernel A c t : ℂ) * nPhase q t)).re := by
    rw [← intervalIntegral.integral_const_mul]
    exact (Complex.reCLM.intervalIntegral_comp_comm (hcont.intervalIntegrable _ _)).symm
  rw [hre]
  refine intervalIntegral.integral_congr fun t _ => ?_
  have e : unitPhase θ * ((resonatorKernel A c t : ℂ) * nPhase q t) =
      (resonatorKernel A c t : ℂ) * (unitPhase θ * nPhase q t) := by ring
  rw [e, Complex.re_ofReal_mul, re_unitPhase_mul_nPhase]

open Classical in
/-- The main term at a prime of `P`: the pairs `nq = n'` count `#{n ∣ D : nq ∣ D}`. -/
theorem unitPhase_mul_main_of_mem {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (θ : ℕ → ℝ) {q : ℕ}
    (hq : q ∈ P) (A : Finset ℕ) (hA : ∀ n ∈ A, 0 < n) :
    unitPhase (θ q) * ∑ n ∈ A, ∑ n' ∈ A,
        (if n * q = n' then targetCoeff P θ n * (starRingEnd ℂ) (targetCoeff P θ n') else 0) =
      ((A.filter fun n => n * q ∈ A).card : ℂ) := by
  have hq' := hP q hq
  have hinner : ∀ n ∈ A, ∑ n' ∈ A,
      (if n * q = n' then targetCoeff P θ n * (starRingEnd ℂ) (targetCoeff P θ n') else 0) =
      if n * q ∈ A then (starRingEnd ℂ) (unitPhase (θ q)) else 0 := by
    intro n hn
    rw [Finset.sum_ite_eq]
    by_cases hmem : n * q ∈ A
    · rw [if_pos hmem, if_pos hmem, targetCoeff_mul_prime θ (hA n hn).ne' hq' hq, map_mul,
        ← mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_targetCoeff]
      simp
    · rw [if_neg hmem, if_neg hmem]
  rw [Finset.sum_congr rfl hinner, Finset.mul_sum]
  have hu : ∀ n ∈ A, unitPhase (θ q) *
      (if n * q ∈ A then (starRingEnd ℂ) (unitPhase (θ q)) else 0) =
      if n * q ∈ A then (1 : ℂ) else 0 := by
    intro n _
    by_cases hmem : n * q ∈ A
    · rw [if_pos hmem, if_pos hmem, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_unitPhase]
      simp
    · rw [if_neg hmem, if_neg hmem, mul_zero]
  rw [Finset.sum_congr rfl hu, Finset.sum_boole]

/-- The main term at `q = 1`: the number of terms. -/
theorem main_of_one (P : Finset ℕ) (θ : ℕ → ℝ) (A : Finset ℕ) :
    ∑ n ∈ A, ∑ n' ∈ A,
        (if n * 1 = n' then targetCoeff P θ n * (starRingEnd ℂ) (targetCoeff P θ n') else 0) =
      (A.card : ℂ) := by
  have hinner : ∀ n ∈ A, ∑ n' ∈ A,
      (if n * 1 = n' then targetCoeff P θ n * (starRingEnd ℂ) (targetCoeff P θ n') else 0) = 1 := by
    intro n hn
    simp only [mul_one]
    rw [Finset.sum_ite_eq, if_pos hn, Complex.mul_conj, Complex.normSq_eq_norm_sq,
      norm_targetCoeff]
    simp
  rw [Finset.sum_congr rfl hinner]
  simp

/-- `n^{i t}` at `n = 1`. -/
theorem nPhase_one (t : ℝ) : nPhase 1 t = 1 := by
  simp [nPhase]

/-- The total mass of the kernel on a window. -/
theorem abs_integral_kernel_sub_le {A : Finset ℕ} (hA : ∀ n ∈ A, 0 < n) (P : Finset ℕ)
    (θ : ℕ → ℝ) {M : ℕ} (hM : ∀ n ∈ A, n ≤ M) (T L : ℝ) :
    |(∫ t in T..T + L, resonatorKernel A (targetCoeff P θ) t) - L * A.card| ≤
      (A.card : ℝ) ^ 2 * (2 * (M : ℝ)) := by
  have h := norm_integral_resonatorKernel_sub_le hA (c := targetCoeff P θ)
    (fun n _ => (norm_targetCoeff P θ n).le) (q := 1) (M := M) Nat.one_pos hM T L
  rw [main_of_one] at h
  simp only [nPhase_one, mul_one, one_mul] at h
  have hc : (∫ t in T..T + L, (resonatorKernel A (targetCoeff P θ) t : ℂ)) =
      ((∫ t in T..T + L, resonatorKernel A (targetCoeff P θ) t : ℝ) : ℂ) :=
    intervalIntegral.integral_ofReal
  rw [hc, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- The kernel of the target direction `θ` on the divisors of the box modulus. -/
def boxKernel (P : Finset ℕ) (m : ℕ) (θ : ℕ → ℝ) (t : ℝ) : ℝ :=
  resonatorKernel (boxModulus P m).divisors (targetCoeff P θ) t

open Classical in
/-- The number of divisors `n` with `nr` also a divisor. -/
def pairCount (P : Finset ℕ) (m r : ℕ) : ℕ :=
  ((boxModulus P m).divisors.filter fun n => n * r ∈ (boxModulus P m).divisors).card

open Classical in
/-- Each prime contributes its main term up to the integrality error. -/
theorem kernel_cos_lower {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (m : ℕ) (θ : ℕ → ℝ) {r : ℕ}
    (hr : r.Prime) (T L : ℝ) :
    L * (pairCount P m r : ℝ) -
        (((boxModulus P m).divisors.card : ℝ) ^ 2 * (2 * ((r * boxModulus P m : ℕ) : ℝ))) ≤
      ∫ t in T..T + L, boxKernel P m θ t * Real.cos (t * Real.log r - θ r) := by
  set A := (boxModulus P m).divisors with hA
  have hApos : ∀ n ∈ A, 0 < n := fun n hn => Nat.pos_of_mem_divisors hn
  have hM : ∀ n ∈ A, n ≤ boxModulus P m := fun n hn => Nat.divisor_le hn
  have hnorm := norm_integral_resonatorKernel_sub_le hApos (c := targetCoeff P θ)
    (fun n _ => (norm_targetCoeff P θ n).le) hr.pos hM T L
  set J := ∫ t in T..T + L, (resonatorKernel A (targetCoeff P θ) t : ℂ) * nPhase r t with hJ
  set Mn := ∑ n ∈ A, ∑ n' ∈ A,
    (if n * r = n' then targetCoeff P θ n * (starRingEnd ℂ) (targetCoeff P θ n') else 0) with hMn
  have hmain : unitPhase (θ r) * Mn = ((A.filter fun n => n * r ∈ A).card : ℂ) := by
    by_cases hrP : r ∈ P
    · exact unitPhase_mul_main_of_mem hP θ hrP A hApos
    · have hzero : ∀ n ∈ A, n * r ∉ A := by
        intro n _ hmem
        exact not_dvd_boxModulus hP hr hrP m
          ((Dvd.intro_left n rfl).trans (Nat.dvd_of_mem_divisors hmem))
      have hMn0 : Mn = 0 := by
        rw [hMn]
        refine Finset.sum_eq_zero fun n hn => ?_
        rw [Finset.sum_ite_eq, if_neg (hzero n hn)]
      have hf0 : (A.filter fun n => n * r ∈ A) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun n hn => hzero n hn
      rw [hMn0, hf0]
      simp
  have hint : ∫ t in T..T + L, boxKernel P m θ t * Real.cos (t * Real.log r - θ r) =
      (unitPhase (θ r) * J).re := integral_kernel_mul_cos A _ r (θ r) T L
  rw [hint]
  have hsplit : unitPhase (θ r) * J =
      (L : ℂ) * ((A.filter fun n => n * r ∈ A).card : ℂ) +
        unitPhase (θ r) * (J - (L : ℂ) * Mn) := by
    rw [← hmain]
    ring
  rw [hsplit, Complex.add_re, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hre := Complex.abs_re_le_norm (unitPhase (θ r) * (J - (L : ℂ) * Mn))
  rw [norm_mul, norm_unitPhase, one_mul] at hre
  have := neg_le_of_abs_le (hre.trans hnorm)
  have hcount : (pairCount P m r : ℝ) = ((A.filter fun n => n * r ∈ A).card : ℝ) := by
    unfold pairCount
    rfl
  rw [hcount]
  linarith

/-- The pair count at a prime of `P`, in proportion to the number of divisors. -/
theorem pairCount_of_mem {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p ∈ P) {m : ℕ}
    (hm : 1 ≤ m) :
    (pairCount P m p : ℝ) = (m : ℝ) / (m + 1) * ((boxModulus P m).divisors.card : ℝ) := by
  have h := card_filter_mul_mem_divisors hP hp hm
  have h' : (pairCount P m p : ℝ) * ((m : ℝ) + 1) =
      (m : ℝ) * ((boxModulus P m).divisors.card : ℝ) := by
    have := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at this
    exact this
  have hm0 : (m : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  linarith

/-- The real inequality closing the Bohr isometry. -/
theorem bohr_algebra {κ η SP SQ L τ D Y I J : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) (hη0 : 0 < η)
    (hη1 : η ≤ 1) (hSP0 : 0 ≤ SP) (hSPQ : SP ≤ SQ) (hSQ : 0 < SQ) (hτ : 1 ≤ τ)
    (hlow : L * (κ * τ) * SP - SQ * (τ ^ 2 * (2 * (Y * D))) ≤ J)
    (hup : J ≤ (κ * SP - η * SQ) * I) (hI : |I - L * τ| ≤ τ ^ 2 * (2 * D)) :
    η * L ≤ 2 * (Y + 1) * τ * D := by
  set B := κ * SP - η * SQ with hB
  have hBabs : |B| ≤ SQ := by
    rw [abs_le]
    constructor
    · rw [hB]
      nlinarith [mul_nonneg hκ0 hSP0, mul_le_mul_of_nonneg_right hη1 hSQ.le]
    · rw [hB]
      nlinarith [mul_le_mul_of_nonneg_left hκ1 hSP0, mul_nonneg hη0.le hSQ.le]
  have hprod : B * I ≤ B * (L * τ) + SQ * (τ ^ 2 * (2 * D)) := by
    have e : B * I = B * (L * τ) + B * (I - L * τ) := by ring
    rw [e]
    have h1 : B * (I - L * τ) ≤ |B| * |I - L * τ| := by
      rw [← abs_mul]
      exact le_abs_self _
    have h2 : |B| * |I - L * τ| ≤ SQ * (τ ^ 2 * (2 * D)) :=
      mul_le_mul hBabs hI (abs_nonneg _) hSQ.le
    linarith
  have h4 := (hlow.trans hup).trans hprod
  have e : B * (L * τ) = κ * SP * (L * τ) - η * SQ * (L * τ) := by
    rw [hB]
    ring
  rw [e] at h4
  have h5 : SQ * τ * (η * L) ≤ SQ * τ * (2 * (Y + 1) * τ * D) := by nlinarith
  exact le_of_mul_le_mul_left h5 (by positivity)

/-- The column integrated against the kernel of the target direction. -/
theorem integral_kernel_mul_column (Q : Finset ℕ) (a : ℕ → ℝ) (P : Finset ℕ) (m : ℕ)
    (θ : ℕ → ℝ) (T L : ℝ) :
    ∫ t in T..T + L, boxKernel P m θ t * ∑ r ∈ Q, a r * Real.cos (t * Real.log r - θ r) =
      ∑ r ∈ Q, a r * ∫ t in T..T + L, boxKernel P m θ t * Real.cos (t * Real.log r - θ r) := by
  have hKc : Continuous (boxKernel P m θ) := continuous_resonatorKernel _ _
  simp only [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  · intro r _
    have : Continuous fun t : ℝ => boxKernel P m θ t * (a r * Real.cos (t * Real.log r - θ r)) :=
      hKc.mul (continuous_const.mul (by fun_prop))
    exact this.intervalIntegrable _ _

/-- **The finite-time Bohr isometry.** See the module docstring. -/
theorem exists_column_ge {P Q : Finset ℕ} (hQ : ∀ r ∈ Q, r.Prime) (hPQ : P ⊆ Q) {m : ℕ}
    (hm : 1 ≤ m) {a : ℕ → ℝ} (ha : ∀ r ∈ Q, 0 ≤ a r) (θ : ℕ → ℝ) {Y : ℕ} (hY : ∀ r ∈ Q, r ≤ Y)
    {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (T : ℝ) {L : ℝ}
    (hL : 2 * ((Y : ℝ) + 1) * ((m + 1 : ℕ) : ℝ) ^ P.card * (boxModulus P m : ℝ) < η * L) :
    ∃ t ∈ Set.Icc T (T + L),
      (m : ℝ) / (m + 1) * ∑ p ∈ P, a p - η * ∑ r ∈ Q, a r ≤
        ∑ r ∈ Q, a r * Real.cos (t * Real.log r - θ r) := by
  classical
  have hP : ∀ p ∈ P, p.Prime := fun p hp => hQ p (hPQ hp)
  have hD0 : 0 < boxModulus P m := boxModulus_pos hP m
  have hDr : (0 : ℝ) < (boxModulus P m : ℝ) := by exact_mod_cast hD0
  have hτeq : ((boxModulus P m).divisors.card : ℝ) = ((m + 1 : ℕ) : ℝ) ^ P.card := by
    rw [card_divisors_boxModulus hP]
    push_cast
    ring
  have hLpos : 0 < L := by
    have h0 : 0 ≤ 2 * ((Y : ℝ) + 1) * ((m + 1 : ℕ) : ℝ) ^ P.card * (boxModulus P m : ℝ) := by
      positivity
    have : 0 < η * L := lt_of_le_of_lt h0 hL
    exact (pos_iff_pos_of_mul_pos this).mp hη
  have hSQ0 : 0 ≤ ∑ r ∈ Q, a r := Finset.sum_nonneg ha
  have hSP0 : 0 ≤ ∑ p ∈ P, a p := Finset.sum_nonneg fun p hp => ha p (hPQ hp)
  have hSPQ : ∑ p ∈ P, a p ≤ ∑ r ∈ Q, a r :=
    Finset.sum_le_sum_of_subset_of_nonneg hPQ fun r hr _ => ha r hr
  have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hκ0 : 0 ≤ (m : ℝ) / (m + 1) := by positivity
  have hκ1 : (m : ℝ) / (m + 1) ≤ 1 := by
    rw [div_le_one hm0]
    linarith
  by_contra hcon
  have hlt : ∀ t ∈ Set.Icc T (T + L), ∑ r ∈ Q, a r * Real.cos (t * Real.log r - θ r) <
      (m : ℝ) / (m + 1) * ∑ p ∈ P, a p - η * ∑ r ∈ Q, a r := by
    intro t ht
    by_contra hge
    exact hcon ⟨t, ht, not_lt.mp hge⟩
  have hTmem : T ∈ Set.Icc T (T + L) := ⟨le_rfl, by linarith⟩
  have hfT : -∑ r ∈ Q, a r ≤ ∑ r ∈ Q, a r * Real.cos (T * Real.log r - θ r) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun r hr => ?_
    nlinarith [ha r hr, Real.neg_one_le_cos (T * Real.log r - θ r)]
  have hSQpos : 0 < ∑ r ∈ Q, a r := by
    rcases hSQ0.lt_or_eq with h | h
    · exact h
    · exfalso
      have hP0 : ∑ p ∈ P, a p = 0 := le_antisymm (h ▸ hSPQ) hSP0
      have h1 := hlt T hTmem
      rw [hP0, ← h] at h1
      rw [← h] at hfT
      simp only [mul_zero, sub_zero] at h1
      linarith
  have hKc : Continuous (boxKernel P m θ) := continuous_resonatorKernel _ _
  have hfc : Continuous fun t : ℝ => ∑ r ∈ Q, a r * Real.cos (t * Real.log r - θ r) := by
    refine continuous_finsetSum _ fun r _ => continuous_const.mul ?_
    fun_prop
  have hupper : ∫ t in T..T + L, boxKernel P m θ t *
        ∑ r ∈ Q, a r * Real.cos (t * Real.log r - θ r) ≤
      ((m : ℝ) / (m + 1) * ∑ p ∈ P, a p - η * ∑ r ∈ Q, a r) *
        ∫ t in T..T + L, boxKernel P m θ t := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith)
      ((hKc.mul hfc).intervalIntegrable _ _) ((continuous_const.mul hKc).intervalIntegrable _ _) ?_
    intro t ht
    rw [mul_comm _ (boxKernel P m θ t)]
    exact mul_le_mul_of_nonneg_left (hlt t ht).le (resonatorKernel_nonneg _ _ _)
  have hτ1 : (1 : ℝ) ≤ ((boxModulus P m).divisors.card : ℝ) := by
    rw [hτeq]
    exact one_le_pow₀ (by push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  set τ : ℝ := ((boxModulus P m).divisors.card : ℝ) with hτdef
  have hstep : ∑ r ∈ Q, a r * (L * (pairCount P m r : ℝ) -
      (τ ^ 2 * (2 * ((r * boxModulus P m : ℕ) : ℝ)))) ≤
      ∑ r ∈ Q, a r * ∫ t in T..T + L, boxKernel P m θ t * Real.cos (t * Real.log r - θ r) :=
    Finset.sum_le_sum fun r hr =>
      mul_le_mul_of_nonneg_left (kernel_cos_lower hP m θ (hQ r hr) T L) (ha r hr)
  have hsumlow : L * ((m : ℝ) / (m + 1) * τ) * ∑ p ∈ P, a p ≤
      ∑ r ∈ Q, a r * (L * (pairCount P m r : ℝ)) := by
    calc
      L * ((m : ℝ) / (m + 1) * τ) * ∑ p ∈ P, a p =
          ∑ p ∈ P, a p * (L * (pairCount P m p : ℝ)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [pairCount_of_mem hP hp hm]
        ring
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hPQ fun r hr _ =>
        mul_nonneg (ha r hr) (mul_nonneg hLpos.le (Nat.cast_nonneg _))
  have herr : ∑ r ∈ Q, a r * (τ ^ 2 * (2 * ((r * boxModulus P m : ℕ) : ℝ))) ≤
      (∑ r ∈ Q, a r) * (τ ^ 2 * (2 * ((Y : ℝ) * (boxModulus P m : ℝ)))) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun r hr => mul_le_mul_of_nonneg_left ?_ (ha r hr)
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have hrY : ((r * boxModulus P m : ℕ) : ℝ) ≤ (Y : ℝ) * (boxModulus P m : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hY r hr) hDr.le
    linarith
  have hlower : L * ((m : ℝ) / (m + 1) * τ) * (∑ p ∈ P, a p) -
      (∑ r ∈ Q, a r) * (τ ^ 2 * (2 * ((Y : ℝ) * (boxModulus P m : ℝ)))) ≤
      ∫ t in T..T + L, boxKernel P m θ t * ∑ r ∈ Q, a r * Real.cos (t * Real.log r - θ r) := by
    rw [integral_kernel_mul_column]
    simp only [mul_sub] at hstep
    rw [Finset.sum_sub_distrib] at hstep
    linarith
  have hmass : |(∫ t in T..T + L, boxKernel P m θ t) - L * τ| ≤ τ ^ 2 * (2 * (boxModulus P m : ℝ)) :=
    abs_integral_kernel_sub_le (fun n hn => Nat.pos_of_mem_divisors hn) P θ
      (fun n hn => Nat.divisor_le hn) T L
  have hcancel := bohr_algebra hκ0 hκ1 hη hη1 hSP0 hSPQ hSQpos hτ1 hlower hupper hmass
  rw [hτeq] at hcancel
  linarith

/-! ### The Kronecker scale -/

/-- The primes up to `y`. -/
def primesUpTo (y : ℕ) : Finset ℕ := (Finset.range (y + 1)).filter Nat.Prime

theorem prime_of_mem_primesUpTo {y p : ℕ} (hp : p ∈ primesUpTo y) : p.Prime :=
  (Finset.mem_filter.mp hp).2

theorem le_of_mem_primesUpTo {y p : ℕ} (hp : p ∈ primesUpTo y) : p ≤ y := by
  have := (Finset.mem_filter.mp hp).1
  rw [Finset.mem_range] at this
  omega

theorem primesUpTo_mono {y N : ℕ} (h : y ≤ N) : primesUpTo y ⊆ primesUpTo N := by
  intro p hp
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
  rw [Finset.mem_range] at h1
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h2⟩

theorem card_primesUpTo_le (y : ℕ) : (primesUpTo y).card ≤ y := by
  have hsub : primesUpTo y ⊆ Finset.Icc 1 y := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(prime_of_mem_primesUpTo hp).pos, le_of_mem_primesUpTo hp⟩
  simpa using Finset.card_le_card hsub

theorem boxModulus_primesUpTo_le (y m : ℕ) : boxModulus (primesUpTo y) m ≤ 4 ^ (m * y) := by
  unfold boxModulus
  rw [Finset.prod_pow, pow_mul']
  exact Nat.pow_le_pow_left (primorial_le_four_pow y) m

/-- **The Kronecker scale.** In a window of length `L > 2(N + 1)(m+1)^y 4^{my}/η`, the column sum on the
primes up to `N` enters every half-space at level `m/(m+1)` of the size of its primes up to `y`. -/
theorem exists_column_ge_of_primesUpTo {y N m : ℕ} (hyN : y ≤ N) (hm : 1 ≤ m) {a : ℕ → ℝ}
    (ha : ∀ r ∈ primesUpTo N, 0 ≤ a r) (θ : ℕ → ℝ) {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (T : ℝ)
    {L : ℝ} (hL : 2 * ((N : ℝ) + 1) * ((m + 1 : ℕ) : ℝ) ^ y * (4 : ℝ) ^ (m * y) < η * L) :
    ∃ t ∈ Set.Icc T (T + L),
      (m : ℝ) / (m + 1) * ∑ p ∈ primesUpTo y, a p - η * ∑ r ∈ primesUpTo N, a r ≤
        ∑ r ∈ primesUpTo N, a r * Real.cos (t * Real.log r - θ r) := by
  refine exists_column_ge (fun r hr => prime_of_mem_primesUpTo hr) (primesUpTo_mono hyN) hm ha θ
    (fun r hr => le_of_mem_primesUpTo hr) hη hη1 T (lt_of_le_of_lt ?_ hL)
  have h1 : ((m + 1 : ℕ) : ℝ) ^ (primesUpTo y).card ≤ ((m + 1 : ℕ) : ℝ) ^ y :=
    pow_le_pow_right₀ (by push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
      (card_primesUpTo_le y)
  have h2 : (boxModulus (primesUpTo y) m : ℝ) ≤ (4 : ℝ) ^ (m * y) := by
    exact_mod_cast boxModulus_primesUpTo_le y m
  have h0 : (0 : ℝ) ≤ 2 * ((N : ℝ) + 1) := by positivity
  calc
    2 * ((N : ℝ) + 1) * ((m + 1 : ℕ) : ℝ) ^ (primesUpTo y).card * (boxModulus (primesUpTo y) m : ℝ)
        ≤ 2 * ((N : ℝ) + 1) * ((m + 1 : ℕ) : ℝ) ^ y * (4 : ℝ) ^ (m * y) := by
          gcongr

end

end GaloisForLFunctions.PrimeTorusTheory
