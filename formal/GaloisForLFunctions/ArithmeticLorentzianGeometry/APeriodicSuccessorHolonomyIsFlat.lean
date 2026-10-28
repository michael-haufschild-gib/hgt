import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheSuccessorConnectionIsTheArchimedeanGaugeField

/-!
# A periodic successor holonomy is flat

The successor connection `A_ω(n) = conj χ_ω(n) χ_ω(n + 1)` of a point `ω` of the prime gauge torus
measures how the completely multiplicative character `χ_ω` turns along the additive successor.
Its flat locus is the Euler point (`succConn_flat_iff_primes_eq_one`). Periodicity already forces
flatness.

* **Ratio rigidity** (`eq_one_of_ratio_periodic`): a completely multiplicative `f` without zeros
  on `n ≥ 1` whose successor ratio `f(n + 1)/f(n)` is `q`-periodic is `≡ 1`. Periodicity of the
  ratio makes `f(n + q) = c f(n)`. At `n = mq` multiplicativity turns this into `f(m + 1) = c f(m)`,
  so `f(m) = c^{m−1}`, and `f(4) = f(2)²` forces `c = 1`.
* **On the torus** (`succConn_periodic_iff_euler`): the successor connection of `ω` is periodic iff
  `ω` is the Euler point. Every other torus point — the archimedean characters `n^{iτ}`, `τ ≠ 0`,
  included — has aperiodic holonomy.
* **Off the torus** (`exists_eq_zero_of_periodic`): a periodic completely multiplicative function
  other than `1`, such as a nontrivial Dirichlet character, vanishes at some `n ≥ 1`. Its successor
  ratio is periodic wherever it is defined.

Holonomy therefore separates the Dirichlet characters, whose holonomy is periodic but which leave
the torus, from the non-periodic torus points, whose holonomy is aperiodic. The Euler point is the
only point with both properties.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open BiarithmeticGaugeGeometry

/-- **Ratio rigidity.** A completely multiplicative function without zeros on `n ≥ 1` whose
successor ratio is `q`-periodic, `f(n + q + 1) f(n) = f(n + 1) f(n + q)`, is identically `1` on
`n ≥ 1`. -/
theorem eq_one_of_ratio_periodic {f : ℕ → ℂ} (hmul : ∀ m n, f (m * n) = f m * f n)
    (h1 : f 1 = 1) (hne : ∀ n, 1 ≤ n → f n ≠ 0) {q : ℕ} (hq : 1 ≤ q)
    (hper : ∀ n, 1 ≤ n → f (n + q + 1) * f n = f (n + 1) * f (n + q)) :
    ∀ n, 1 ≤ n → f n = 1 := by
  -- `f(n + q) = c f(n)` with `c = f(1 + q)`
  have hshift : ∀ n, 1 ≤ n → f (n + q) = f (1 + q) * f n := by
    intro n hn
    induction n with
    | zero => omega
    | succ k ih =>
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [zero_add, h1, mul_one]
      · have h := hper k hk
        rw [ih hk] at h
        rw [show k + 1 + q = k + q + 1 by ring]
        exact mul_right_cancel₀ (hne k hk) (by rw [h]; ring)
  -- `f(m + 1) = c f(m)`, from `n = mq`
  have hstep : ∀ m, 1 ≤ m → f (m + 1) = f (1 + q) * f m := by
    intro m hm
    have h := hshift (m * q) (Nat.one_le_iff_ne_zero.mpr (by positivity))
    rw [show m * q + q = (m + 1) * q by ring, hmul, hmul] at h
    exact mul_right_cancel₀ (hne q hq) (by rw [h]; ring)
  have hpow : ∀ m, f (m + 1) = f (1 + q) ^ m := by
    intro m
    induction m with
    | zero => simpa using h1
    | succ k ih => rw [hstep (k + 1) (by omega), ih, pow_succ, mul_comm]
  -- `f(4) = f(2)²` forces `c = 1`
  have hc0 : f (1 + q) ≠ 0 := hne (1 + q) (by omega)
  have hc : f (1 + q) = 1 := by
    have h4 : f (2 * 2) = f 2 * f 2 := hmul 2 2
    rw [show (2 * 2 : ℕ) = 3 + 1 from rfl, show (2 : ℕ) = 1 + 1 from rfl, hpow, hpow] at h4
    have : f (1 + q) ^ 2 * (f (1 + q) - 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) hc0
    · exact sub_eq_zero.mp h
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
  rw [hpow, hc, one_pow]

/-- **On the torus a periodic successor holonomy is flat**: the successor connection of `ω` is
periodic iff `ω` is the Euler point. -/
theorem succConn_periodic_iff_euler (ω : PrimeGauge) :
    (∃ q, 1 ≤ q ∧ ∀ n, 1 ≤ n → succConn ω (n + q) = succConn ω n) ↔
      ∀ p : ℕ, p.Prime → ω.val p = 1 := by
  constructor
  · rintro ⟨q, hq, hper⟩ p hp
    have hu : ∀ k, k ≠ 0 → ω.gaugeChar k * starRingEnd ℂ (ω.gaugeChar k) = 1 := fun k hk => by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ω.norm_gaugeChar hk]; simp
    have hne : ∀ n, 1 ≤ n → ω.gaugeChar n ≠ 0 := fun n hn h => by
      have := ω.norm_gaugeChar (by omega : n ≠ 0)
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have hratio : ∀ n, 1 ≤ n → ω.gaugeChar (n + q + 1) * ω.gaugeChar n =
        ω.gaugeChar (n + 1) * ω.gaugeChar (n + q) := fun n hn => by
      have h := hper n hn
      unfold succConn at h
      have h1 := hu (n + q) (by omega)
      have h2 := hu n (by omega)
      linear_combination (ω.gaugeChar (n + q) * ω.gaugeChar n) * h -
        (ω.gaugeChar (n + q + 1) * ω.gaugeChar n) * h1 +
        (ω.gaugeChar (n + 1) * ω.gaugeChar (n + q)) * h2
    have := eq_one_of_ratio_periodic ω.gaugeChar_mul ω.gaugeChar_one hne hq hratio p hp.one_lt.le
    rwa [ω.gaugeChar_prime hp] at this
  · intro h
    have hflat : ∀ n, 1 ≤ n → succConn ω n = 1 := fun n hn =>
      (succConn_flat_iff_primes_eq_one ω n).mpr (fun p _ hp => h p hp) n
        (Finset.mem_Icc.mpr ⟨hn, le_rfl⟩)
    exact ⟨1, le_rfl, fun n hn => by rw [hflat n hn, hflat (n + 1) (by omega)]⟩

/-- **Off the torus.** A `q`-periodic completely multiplicative function that is not `≡ 1` on
`n ≥ 1` vanishes at some `n ≥ 1`. -/
theorem exists_eq_zero_of_periodic {f : ℕ → ℂ} (hmul : ∀ m n, f (m * n) = f m * f n)
    (h1 : f 1 = 1) {q : ℕ} (hq : 1 ≤ q) (hper : ∀ n, 1 ≤ n → f (n + q) = f n)
    (hne1 : ∃ n, 1 ≤ n ∧ f n ≠ 1) : ∃ n, 1 ≤ n ∧ f n = 0 := by
  by_contra h
  push Not at h
  obtain ⟨n, hn, hfn⟩ := hne1
  refine hfn (eq_one_of_ratio_periodic hmul h1 h hq (fun k hk => ?_) n hn)
  rw [show k + q + 1 = k + 1 + q by ring, hper (k + 1) (by omega), hper k hk]

end GaloisForLFunctions.ArithmeticLorentzianGeometry
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms eq_one_of_ratio_periodic
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms succConn_periodic_iff_euler
open GaloisForLFunctions.ArithmeticLorentzianGeometry in
#print axioms exists_eq_zero_of_periodic
