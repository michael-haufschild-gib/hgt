import GaloisForLFunctions.EffectiveArithmeticHodgeTheory.ApproximateVanishingIsAlmostDivisibility

/-!
# Small integer auxiliaries are divisible

An auxiliary of the group ring `ℤ[Γ]` is an integer Dirichlet polynomial `D(s) = Σ_{n≤N} a_n n^{−s}`.
Its `p`-tower sums `C_w = Σ_{ω_p(n) = w} a_n` are integers. Approximate Bézout bounds
`Σ_w |C_w|² ≤ 2ε²` when `|D| ≤ ε` on `N²p log p` consecutive points of the progression of `p`; for
`ε < 1/√2` every `C_w` is an integer of modulus below one, hence zero. So for integer auxiliaries
**approximate vanishing is exact vanishing** (`dirDeriv_frobPoint_eq_zero_of_small`), and `D` is
divisible by `1 − p^{−s}` in `ℤ[Γ]`.

Multiplicity is read by derivatives. If `a = (1 − p^{−s})^k F` then on the progression the first
`k` derivatives of `D` vanish and the `k`-th is `k!(log p)^k F(s_j)`
(`dirDeriv_frobPoint_chain`). Peeling one Euler factor at a time:

* **Rigidity** (`vanishesAlong_of_small`). If `|D^{(i)}| ≤ i!(log p)^i ε` for `i < m` on `N²p log p`
  consecutive points, with `2ε² < 1`, then `D` vanishes to order `m` on the whole progression.
* **The zero estimate for integer auxiliaries** (`prod_pow_le_of_small`). A nonzero integer auxiliary
  of length `N` that is small in this sense along the progressions of the primes `p ∈ S` to orders
  `m_p` has `∏ p^{m_p} ≤ N`.

The threshold is of the right size: the auxiliary `1` has `|D| = 1` everywhere and is not divisible
(`dirDeriv_single_one`), so `ε < 1` is necessary. Integrality is used once per Euler factor, and no
transcendence input enters.
-/

open Complex Finset Filter
open scoped Real

noncomputable section

namespace GaloisForLFunctions.EffectiveArithmeticHodgeTheory

/-- Integer coefficients: the auxiliaries of `ℤ[Γ]`. -/
def IntegerCoeffs (a : ℕ → ℂ) : Prop := ∀ n, ∃ z : ℤ, a n = z

theorem integerCoeffs_towerQuot {a : ℕ → ℂ} (ha : IntegerCoeffs a) (p : ℕ) :
    IntegerCoeffs (towerQuot a p) := by
  choose b hb using ha
  exact fun m => ⟨∑ l ∈ range (m.factorization p + 1), b (m / p ^ l), by
    simp only [towerQuot, hb, Int.cast_sum]⟩

/-- An integer of modulus below one vanishes. -/
theorem eq_zero_of_int_of_norm_lt_one {z : ℂ} {k : ℤ} (hz : z = k) (h : ‖z‖ < 1) : z = 0 := by
  subst hz
  rw [Complex.norm_intCast] at h
  have h' : |k| < 1 := by exact_mod_cast (show ((|k| : ℤ) : ℝ) < 1 by rwa [Int.cast_abs])
  simp [Int.abs_lt_one_iff.mp h']

/-! ### Order one -/

/-- **Integrality makes approximate vanishing exact.** An integer auxiliary of length `N` with
`|D| ≤ ε < 1/√2` on `N²p log p` consecutive points of the progression of `p` vanishes on the whole
progression. -/
theorem dirDeriv_frobPoint_eq_zero_of_small {p : ℕ} (hp : p.Prime) {a : ℕ → ℂ}
    (ha : IntegerCoeffs a) {N : ℕ} {ε : ℝ} (hε : 2 * ε ^ 2 < 1) (J₀ : ℤ) {J : ℕ}
    (hJ : (N : ℝ) ^ 2 * p * Real.log p ≤ J)
    (hD : ∀ j ∈ range J, ‖dirDeriv a N 0 (frobPoint p (J₀ + j))‖ ≤ ε) (j : ℤ) :
    dirDeriv a N 0 (frobPoint p j) = 0 := by
  classical
  have hsum := sum_normSq_towerSums_le hp a J₀ hJ hD
  choose b hb using ha
  rw [dirDeriv_zero_frobPoint_eq]
  refine Finset.sum_eq_zero fun w hw => ?_
  set C := ∑ n ∈ Icc 1 N with frobRoot p n = w, a n
  have hC : C = ((∑ n ∈ Icc 1 N with frobRoot p n = w, b n : ℤ) : ℂ) := by
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl fun n _ => hb n
  have hle : ‖C‖ ^ 2 ≤ 2 * ε ^ 2 :=
    (Finset.single_le_sum (f := fun w => ‖∑ n ∈ Icc 1 N with frobRoot p n = w, a n‖ ^ 2)
      (fun _ _ => sq_nonneg _) hw).trans hsum
  have hlt : ‖C‖ < 1 := by nlinarith [norm_nonneg C]
  rw [eq_zero_of_int_of_norm_lt_one hC hlt, zero_mul]

/-! ### Multiplicity -/

/-- One Euler factor on the progression: if `b = (1 − p^{−s}) c`, then
`D_b^{(i)}(s_j) = −Σ_{l<i} C(i, l)(−log p)^{i−l} D_c^{(l)}(s_j)`. -/
theorem dirDeriv_frobPoint_of_eulerMul {p : ℕ} (hp : p.Prime) {b c : ℕ → ℂ} {M : ℕ}
    (hbc : ∀ m, m ≠ 0 → b m = c m - if p ∣ m then c (m / p) else 0)
    (hc0 : ∀ m, M / p < m → c m = 0) (i : ℕ) (j : ℤ) :
    dirDeriv b M i (frobPoint p j) = -∑ l ∈ range i, (i.choose l : ℂ) *
      (-(Real.log p : ℂ)) ^ (i - l) * dirDeriv c (M / p) l (frobPoint p j) := by
  rw [dirDeriv_quot hp hbc hc0, cpow_neg_frobPoint_self hp, one_mul, Finset.sum_range_succ]
  simp only [Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, one_mul]
  ring

/-- **The Taylor coefficient of a power of the Euler factor.** For a chain
`b₀ = (1 − p^{−s}) b₁ = ⋯ = (1 − p^{−s})^k b_k`, with `b_r` of length `M/p^r`, the first `k`
derivatives of `D_{b₀}` vanish on the progression and the `k`-th is `k!(log p)^k D_{b_k}`. -/
theorem dirDeriv_frobPoint_chain {p : ℕ} (hp : p.Prime) :
    ∀ (k : ℕ) (b : ℕ → ℕ → ℂ) (M : ℕ),
      (∀ r < k, ∀ m, m ≠ 0 → b r m = b (r + 1) m - if p ∣ m then b (r + 1) (m / p) else 0) →
      (∀ r < k, ∀ m, M / p ^ (r + 1) < m → b (r + 1) m = 0) → ∀ j : ℤ,
      (∀ i < k, dirDeriv (b 0) M i (frobPoint p j) = 0) ∧
        dirDeriv (b 0) M k (frobPoint p j) = (k.factorial : ℂ) * (Real.log p : ℂ) ^ k *
          dirDeriv (b k) (M / p ^ k) 0 (frobPoint p j) := by
  intro k
  induction k with
  | zero =>
    intro b M _ _ j
    exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), by simp⟩
  | succ k ih =>
    intro b M hrel hsupp j
    have hdiv : ∀ r, M / p / p ^ r = M / p ^ (r + 1) := fun r => by
      rw [Nat.div_div_eq_div_mul, pow_succ']
    obtain ⟨h0, hk⟩ := ih (fun r => b (r + 1)) (M / p) (fun r hr => hrel (r + 1) (by omega))
      (fun r hr m hm => hsupp (r + 1) (by omega) m (by rwa [hdiv] at hm)) j
    have hstep := dirDeriv_frobPoint_of_eulerMul hp (hrel 0 (by omega))
      (fun m hm => hsupp 0 (by omega) m (by simpa using hm))
    have hz : ∀ i, ∀ L ≤ k, ∑ l ∈ range L, (i.choose l : ℂ) * (-(Real.log p : ℂ)) ^ (i - l) *
        dirDeriv (b (0 + 1)) (M / p) l (frobPoint p j) = 0 := fun i L hL =>
      Finset.sum_eq_zero fun l hl => by
        rw [h0 l (lt_of_lt_of_le (mem_range.mp hl) hL), mul_zero]
    refine ⟨fun i hi => by rw [hstep, hz i i (by omega), neg_zero], ?_⟩
    rw [hstep, Finset.sum_range_succ, hz (k + 1) k le_rfl, zero_add, hk, hdiv k,
      Nat.choose_succ_self_right, Nat.add_sub_cancel_left, Nat.factorial_succ]
    push_cast
    ring

/-- **Rigidity of integer auxiliaries.** If `|D^{(i)}| ≤ i!(log p)^i ε` for `i < m` on
`N²p log p` consecutive points of the progression of `p`, with `2ε² < 1`, then `D` vanishes to
order `m` on the whole progression. -/
theorem vanishesAlong_of_small {p : ℕ} (hp : p.Prime) {a : ℕ → ℂ} (ha : IntegerCoeffs a) {N : ℕ}
    (ha0 : ∀ n, N < n → a n = 0) {m : ℕ} {ε : ℝ} (hε : 2 * ε ^ 2 < 1) (J₀ : ℤ) {J : ℕ}
    (hJ : (N : ℝ) ^ 2 * p * Real.log p ≤ J)
    (hD : ∀ i < m, ∀ j ∈ range J,
      ‖dirDeriv a N i (frobPoint p (J₀ + j))‖ ≤ i.factorial * Real.log p ^ i * ε) :
    ∀ i < m, ∀ j : ℤ, dirDeriv a N i (frobPoint p j) = 0 := by
  have hL : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  -- the chain of tower quotients `b_r = a/(1 − p^{−s})^r`
  obtain ⟨b, hb0, hbs⟩ : ∃ b : ℕ → ℕ → ℂ, b 0 = a ∧ ∀ r, b (r + 1) = towerQuot (b r) p :=
    ⟨fun r => (fun c => towerQuot c p)^[r] a, rfl,
      fun r => Function.iterate_succ_apply' (fun c => towerQuot c p) r a⟩
  have hrel : ∀ r m, m ≠ 0 → b r m = b (r + 1) m - if p ∣ m then b (r + 1) (m / p) else 0 :=
    fun r m hm => by rw [hbs]; exact towerQuot_sub (b r) hp hm
  have hint : ∀ r, IntegerCoeffs (b r) := fun r => by
    induction r with
    | zero => rw [hb0]; exact ha
    | succ r ih => rw [hbs]; exact integerCoeffs_towerQuot ih p
  -- each quotient up to order `m` exists in `ℤ[Γ]` and has length `N/p^r`
  have hsupp : ∀ r ≤ m, ∀ t ≤ r, ∀ n, N / p ^ t < n → b t n = 0 := by
    intro r
    induction r with
    | zero =>
      intro _ t ht n hn
      obtain rfl : t = 0 := by omega
      rw [hb0]
      exact ha0 n (by simpa using hn)
    | succ r ih =>
      intro hr t ht n hn
      rcases Nat.lt_or_ge t (r + 1) with htr | htr
      · exact ih (by omega) t (by omega) n hn
      obtain rfl : t = r + 1 := by omega
      have hval := dirDeriv_frobPoint_chain hp r b N (fun t _ => hrel t)
        (fun t _ => ih (by omega) (t + 1) (by omega))
      -- the `r`-th derivative of `a` is `r!(log p)^r` times the quotient `b_r`
      have hsmall : ∀ j ∈ range J,
          ‖dirDeriv (b r) (N / p ^ r) 0 (frobPoint p (J₀ + j))‖ ≤ ε := fun j hj => by
        have h := hD r (by omega) j hj
        rw [← hb0, (hval (J₀ + j)).2, norm_mul, norm_mul, norm_pow, Complex.norm_natCast,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL] at h
        exact le_of_mul_le_mul_left h (by positivity)
      have hJr : ((N / p ^ r : ℕ) : ℝ) ^ 2 * p * Real.log p ≤ J := by
        refine le_trans ?_ hJ
        have : ((N / p ^ r : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.div_le_self _ _
        gcongr
      have hzero := dirDeriv_frobPoint_eq_zero_of_small hp (hint r) hε J₀ hJr hsmall
      have hn' : N / p ^ r / p < n := by rwa [Nat.div_div_eq_div_mul, ← pow_succ]
      rw [hbs]
      exact towerQuot_eq_zero hp (ih (by omega) r le_rfl) (Eventually.of_forall hzero)
        (lt_of_le_of_lt (Nat.zero_le _) hn').ne' (by rw [mul_comm]; exact (Nat.div_lt_iff_lt_mul hp.pos).mp hn')
  intro i hi j
  rw [← hb0]
  exact (dirDeriv_frobPoint_chain hp m b N (fun t _ => hrel t)
    (fun t _ => hsupp m le_rfl (t + 1) (by omega)) j).1 i hi

/-- **The zero estimate for integer auxiliaries.** A nonzero integer auxiliary of length `N` whose
first `m_p` derivatives are at most `i!(log p)^i ε`, `2ε² < 1`, on `N²p log p` consecutive points of
the progression of each `p ∈ S` has `∏_{p∈S} p^{m_p} ≤ N`. -/
theorem prod_pow_le_of_small {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (mult : ℕ → ℕ) {a : ℕ → ℂ}
    (ha : IntegerCoeffs a) {N : ℕ} (ha0 : ∀ n, N < n → a n = 0) (hne : ∃ n ∈ Icc 1 N, a n ≠ 0)
    {ε : ℝ} (hε : 2 * ε ^ 2 < 1) (J₀ : ℕ → ℤ) {J : ℕ}
    (hJ : ∀ p ∈ S, (N : ℝ) ^ 2 * p * Real.log p ≤ J)
    (hD : ∀ p ∈ S, ∀ i < mult p, ∀ j ∈ range J,
      ‖dirDeriv a N i (frobPoint p (J₀ p + j))‖ ≤ i.factorial * Real.log p ^ i * ε) :
    ∏ p ∈ S, p ^ mult p ≤ N :=
  prod_pow_le_of_vanishesAlong hS _ mult a N le_rfl ha0 hne fun p hp i hi =>
    Eventually.of_forall fun j =>
      vanishesAlong_of_small (hS p hp) ha ha0 hε (J₀ p) (hJ p hp) (hD p hp) i hi j

/-- The auxiliary `1` has `|D| = 1` everywhere: the threshold `ε < 1` cannot be relaxed. -/
theorem dirDeriv_single_one {N : ℕ} (hN : 1 ≤ N) (s : ℂ) :
    dirDeriv (Pi.single 1 1 : ℕ → ℂ) N 0 s = 1 := by
  rw [dirDeriv, Finset.sum_eq_single 1 (fun n _ hn => by simp [hn])
    (fun h => absurd (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩) h)]
  simp

end GaloisForLFunctions.EffectiveArithmeticHodgeTheory
