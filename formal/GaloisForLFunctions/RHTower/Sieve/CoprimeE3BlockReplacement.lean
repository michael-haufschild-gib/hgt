import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenForbiddenSupport
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.SocleCondensedCentralLimit
import GaloisForLFunctions.RHTower.RouteECofactorParityBalance

/-!
# Coprime `E₃` replacement of squarefree blocks

A consequence of the forbidden-support all-interval `E₃` theorem: any fixed number of squarefree
blocks `N^δ ≤ u_i ≤ N^K` can be replaced simultaneously by squarefree `Q_i` of opposite Möbius sign,
pairwise coprime and coprime to every original support, each at distance
`≤ √(u_i ℓ_i) (log u_i)^{31/20}` above `u_i` with `ℓ_i ≪ log N`.  The blocks are processed in turn:
when `μ(u_i) = 1` an `E₃` token coprime to the accumulated support replaces `u_i`; when
`μ(u_i) = -1` a fresh prime `ℓ_i ∤` (accumulated support), `ℓ_i ≤ (3K + 3) log N` (Chebyshev's
`θ(y) ≥ y/2`), multiplies an `E₃` token at `u_i/ℓ_i`.  Every prime factor of `Q_i` is at most
`max(C log N, √u_i)`, so for `u_i ≤ z²` all replacement primes stay below `z` once `C log N ≤ z`.
-/

namespace RHTower.Sieve

open Filter

noncomputable section

/-- A prime at most `y` not dividing `M ≥ 1`, as soon as `θ(y) > log M`: otherwise the primorial of
`y` divides `M`. -/
theorem exists_prime_le_not_dvd {M : ℕ} (hM : M ≠ 0) {y : ℝ}
    (hy : Real.log M < Chebyshev.theta y) : ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ∧ ¬ p ∣ M := by
  by_contra h
  push Not at h
  have hle : ∀ p ∈ Nat.primesLE ⌊y⌋₊, p ∣ M := by
    intro p hp
    obtain ⟨hpy, hpp⟩ := Nat.mem_primesLE.1 hp
    have hy0 : 0 ≤ y := by
      by_contra hy0; push Not at hy0
      have : ⌊y⌋₊ = 0 := Nat.floor_eq_zero.2 (by linarith)
      have := hpp.two_le; omega
    exact h p hpp ((Nat.cast_le.2 hpy).trans (Nat.floor_le hy0))
  have hdvd : ∏ p ∈ Nat.primesLE ⌊y⌋₊, p ∣ M :=
    Finset.prod_primes_dvd M (fun p hp => (Nat.mem_primesLE.1 hp).2.prime) hle
  have hprod : ((∏ p ∈ Nat.primesLE ⌊y⌋₊, p : ℕ) : ℝ) ≤ M :=
    Nat.cast_le.2 (Nat.le_of_dvd (Nat.pos_of_ne_zero hM) hdvd)
  have hpos : (0 : ℝ) < ((∏ p ∈ Nat.primesLE ⌊y⌋₊, p : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos fun p hp => (Nat.mem_primesLE.1 hp).2.pos
  have hlog := Real.log_le_log hpos hprod
  rw [Chebyshev.theta_eq_sum_primesLE] at hy
  push_cast at hlog
  rw [Real.log_prod fun p hp => by
    have := (Nat.mem_primesLE.1 hp).2.pos; positivity] at hlog
  linarith

/-- A product of three distinct primes has Möbius value `-1`. -/
theorem moebius_mul_three_distinct_primes {p₁ p₂ p₃ : ℕ} (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h₃ : p₃.Prime)
    (h12 : p₁ ≠ p₂) (h13 : p₁ ≠ p₃) (h23 : p₂ ≠ p₃) :
    ArithmeticFunction.moebius (p₁ * p₂ * p₃) = -1 := by
  have hm := ArithmeticFunction.isMultiplicative_moebius
  rw [hm.map_mul_of_coprime (Nat.Coprime.mul_left ((Nat.coprime_primes h₁ h₃).2 h13)
      ((Nat.coprime_primes h₂ h₃).2 h23)).gcd_eq_one,
    hm.map_mul_of_coprime ((Nat.coprime_primes h₁ h₂).2 h12).gcd_eq_one,
    ArithmeticFunction.moebius_apply_prime h₁, ArithmeticFunction.moebius_apply_prime h₂,
    ArithmeticFunction.moebius_apply_prime h₃]
  norm_num

/-- The amplified window: `ℓ h(u/ℓ) ≤ √(uℓ) (log u)^{31/20}` for `h(y) = √(y (log y)^{11/10}) log y`,
`1 ≤ ℓ ≤ u`. -/
theorem amplified_window_le {u ℓ : ℝ} (hℓ : 1 ≤ ℓ) (hu : ℓ ≤ u) :
    ℓ * (Real.sqrt (u / ℓ * Real.log (u / ℓ) ^ (11 / 10 : ℝ)) * Real.log (u / ℓ)) ≤
      Real.sqrt (u * ℓ) * Real.log u ^ (31 / 20 : ℝ) := by
  have hℓ0 : 0 < ℓ := by linarith
  have hu0 : 0 < u := by linarith
  have hy1 : 1 ≤ u / ℓ := by rw [le_div_iff₀ hℓ0]; linarith
  have hly : 0 ≤ Real.log (u / ℓ) := Real.log_nonneg hy1
  have hlyu : Real.log (u / ℓ) ≤ Real.log u :=
    Real.log_le_log (by positivity) (div_le_self hu0.le hℓ)
  have hlu : 0 ≤ Real.log u := hly.trans hlyu
  -- `√((u/ℓ) λ^{11/10}) = √(u/ℓ) λ^{11/20}`
  have hs : Real.sqrt (u / ℓ * Real.log (u / ℓ) ^ (11 / 10 : ℝ)) =
      Real.sqrt (u / ℓ) * Real.log (u / ℓ) ^ (11 / 20 : ℝ) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (Real.log (u / ℓ) ^ (11 / 10 : ℝ)),
      ← Real.rpow_mul hly]
    norm_num
  have hsℓ : ℓ * Real.sqrt (u / ℓ) = Real.sqrt (u * ℓ) := by
    rw [Real.sqrt_div' u hℓ0.le, Real.sqrt_mul hu0.le]
    have h1 : Real.sqrt ℓ * Real.sqrt ℓ = ℓ := Real.mul_self_sqrt hℓ0.le
    have h2 : 0 < Real.sqrt ℓ := Real.sqrt_pos.2 hℓ0
    field_simp
    nlinarith
  have hpow : Real.log (u / ℓ) ^ (11 / 20 : ℝ) * Real.log (u / ℓ) ≤ Real.log u ^ (31 / 20 : ℝ) := by
    have e : Real.log (u / ℓ) ^ (11 / 20 : ℝ) * Real.log (u / ℓ) =
        Real.log (u / ℓ) ^ (31 / 20 : ℝ) := by
      rcases hly.lt_or_eq with hpos | hz
      · rw [show (31 / 20 : ℝ) = 11 / 20 + 1 by norm_num, Real.rpow_add hpos, Real.rpow_one]
      · rw [← hz]; simp
    rw [e]; exact Real.rpow_le_rpow hly hlyu (by norm_num)
  rw [hs]
  calc ℓ * (Real.sqrt (u / ℓ) * Real.log (u / ℓ) ^ (11 / 20 : ℝ) * Real.log (u / ℓ))
      = (ℓ * Real.sqrt (u / ℓ)) * (Real.log (u / ℓ) ^ (11 / 20 : ℝ) * Real.log (u / ℓ)) := by ring
    _ ≤ Real.sqrt (u * ℓ) * Real.log u ^ (31 / 20 : ℝ) := by
        rw [hsℓ]; exact mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg _)

/-- The prime factors of a product of three primes are those primes. -/
theorem mem_primeFactors_three {p₁ p₂ p₃ p : ℕ} (h₁ : p₁.Prime) (h₂ : p₂.Prime) (h₃ : p₃.Prime)
    (hp : p ∈ (p₁ * p₂ * p₃).primeFactors) : p = p₁ ∨ p = p₂ ∨ p = p₃ := by
  obtain ⟨hpp, hdvd, -⟩ := Nat.mem_primeFactors.1 hp
  rcases (Nat.Prime.dvd_mul hpp).1 hdvd with h12 | h3
  · rcases (Nat.Prime.dvd_mul hpp).1 h12 with h1 | h2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hpp h₁).1 h1)
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hpp h₂).1 h2))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hpp h₃).1 h3))

/-- The three primes of the all-interval `E₃` token at scale `y` lie below `√y`, once
`2P ≤ √y` and `P ≥ 9`. -/
theorem threePrime_le_sqrt {y P : ℝ} (h2P : 2 * P ≤ Real.sqrt y) (h9 : 9 ≤ P) {p₁ p₂ p₃ : ℕ} (hp₁ : (p₁ : ℝ) ≤ 2 * P)
    (hp₂ : (p₂ : ℝ) ≤ 2 * (Real.sqrt (y / P) / 2)) (hp₃ : (p₃ : ℝ) ≤ 6 * (Real.sqrt (y / P) / 2)) :
    (p₁ : ℝ) ≤ Real.sqrt y ∧ (p₂ : ℝ) ≤ Real.sqrt y ∧ (p₃ : ℝ) ≤ Real.sqrt y := by
  have hP0 : 0 < P := by linarith
  have hs : Real.sqrt (y / P) = Real.sqrt y / Real.sqrt P := Real.sqrt_div' y hP0.le
  have hsP : 3 ≤ Real.sqrt P := by
    rw [Real.le_sqrt (by norm_num) hP0.le]; linarith
  have hsy : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  have h3 : 3 * Real.sqrt (y / P) ≤ Real.sqrt y := by
    rw [hs, ← mul_div_assoc, div_le_iff₀ (by linarith)]; nlinarith
  refine ⟨hp₁.trans h2P, ?_, ?_⟩
  · have : Real.sqrt (y / P) ≤ Real.sqrt y := by linarith [Real.sqrt_nonneg (y / P)]
    linarith
  · linarith

/-- **One block with `μ(u) = 1`.**  An `E₃` token at `u` coprime to `M` is itself the replacement:
`μ = -1`, displacement `≤ √u (log u)^{31/20}`, prime factors `≤ √u`. -/
theorem block_step_of_token {u M p₁ p₂ p₃ : ℕ} {Λ : ℝ} (hu : (1 : ℝ) ≤ u) (hΛ : 1 ≤ Λ)
    (hμ : ArithmeticFunction.moebius u = 1)
    (hs1 : 2 * Real.log u ^ (11 / 10 : ℝ) ≤ Real.sqrt u) (hs9 : 9 ≤ Real.log u ^ (11 / 10 : ℝ))
    (htok : IsCoprimeE3Token (u : ℝ) M p₁ p₂ p₃) :
    ∃ Q ℓ : ℕ, Squarefree Q ∧ ArithmeticFunction.moebius Q = -ArithmeticFunction.moebius u ∧
      Nat.Coprime Q M ∧ 1 ≤ ℓ ∧ (ℓ : ℝ) ≤ Λ ∧ u < Q ∧
      (Q : ℝ) ≤ u + Real.sqrt (u * ℓ) * Real.log u ^ (31 / 20 : ℝ) ∧
      ∀ p ∈ Q.primeFactors, (p : ℝ) ≤ max Λ (Real.sqrt u) := by
  obtain ⟨h₁, h₂, h₃, h12, h13, h23, -, hp₁u, -, hp₂u, -, hp₃u, hsq, hcop, hlo, hhi⟩ := htok
  obtain ⟨hq1, hq2, hq3⟩ := threePrime_le_sqrt hs1 hs9 hp₁u hp₂u hp₃u
  refine ⟨p₁ * p₂ * p₃, 1, hsq, ?_, hcop, le_rfl, by simpa using hΛ, ?_, ?_, ?_⟩
  · rw [moebius_mul_three_distinct_primes h₁ h₂ h₃ h12 h13 h23, hμ]
  · exact_mod_cast hlo
  · have hw := amplified_window_le (u := (u : ℝ)) (ℓ := 1) le_rfl hu
    simp only [div_one, one_mul, mul_one] at hw
    rw [Nat.cast_one, mul_one]
    linarith
  · intro p hp
    rcases mem_primeFactors_three h₁ h₂ h₃ hp with rfl | rfl | rfl
    · exact hq1.trans (le_max_right _ _)
    · exact hq2.trans (le_max_right _ _)
    · exact hq3.trans (le_max_right _ _)

/-- **One block with `μ(u) = -1`.**  For a prime `ℓ ∤ M` and an `E₃` token at `u/ℓ` coprime to
`Mℓ`, `Q = ℓ E₃(u/ℓ)` has `μ(Q) = 1`, displacement `≤ √(uℓ)(log u)^{31/20}`, prime factors
`≤ max(ℓ, √u)`. -/
theorem block_step_of_prime_token {u M ℓ p₁ p₂ p₃ : ℕ} {Λ : ℝ} (hℓp : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    (hℓΛ : (ℓ : ℝ) ≤ Λ) (hℓu : (ℓ : ℝ) ≤ u) (hμ : ArithmeticFunction.moebius u = -1)
    (hs1 : 2 * Real.log ((u : ℝ) / ℓ) ^ (11 / 10 : ℝ) ≤ Real.sqrt ((u : ℝ) / ℓ))
    (hs9 : 9 ≤ Real.log ((u : ℝ) / ℓ) ^ (11 / 10 : ℝ))
    (htok : IsCoprimeE3Token ((u : ℝ) / ℓ) (M * ℓ) p₁ p₂ p₃) :
    ∃ Q ℓ' : ℕ, Squarefree Q ∧ ArithmeticFunction.moebius Q = -ArithmeticFunction.moebius u ∧
      Nat.Coprime Q M ∧ 1 ≤ ℓ' ∧ (ℓ' : ℝ) ≤ Λ ∧ u < Q ∧
      (Q : ℝ) ≤ u + Real.sqrt (u * ℓ') * Real.log u ^ (31 / 20 : ℝ) ∧
      ∀ p ∈ Q.primeFactors, (p : ℝ) ≤ max Λ (Real.sqrt u) := by
  obtain ⟨h₁, h₂, h₃, h12, h13, h23, -, hp₁u, -, hp₂u, -, hp₃u, hsq, hcop, hlo, hhi⟩ := htok
  obtain ⟨hq1, hq2, hq3⟩ := threePrime_le_sqrt hs1 hs9 hp₁u hp₂u hp₃u
  have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓp.one_lt.le
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hu0 : (0 : ℝ) < u := by linarith
  have hcopM : Nat.Coprime (p₁ * p₂ * p₃) M :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_right M ℓ) hcop
  have hcopℓ : Nat.Coprime (p₁ * p₂ * p₃) ℓ :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_left ℓ M) hcop
  have hℓMcop : Nat.Coprime ℓ M := (Nat.Prime.coprime_iff_not_dvd hℓp).2 hℓM
  have hsqrt : Real.sqrt ((u : ℝ) / ℓ) ≤ Real.sqrt u :=
    Real.sqrt_le_sqrt (div_le_self hu0.le hℓ1)
  refine ⟨ℓ * (p₁ * p₂ * p₃), ℓ, ?_, ?_, Nat.Coprime.mul_left hℓMcop hcopM, hℓp.one_lt.le, hℓΛ,
    ?_, ?_, ?_⟩
  · rw [Nat.squarefree_mul_iff]
    exact ⟨hcopℓ.symm, hℓp.squarefree, hsq⟩
  · rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcopℓ.symm.gcd_eq_one,
      moebius_mul_three_distinct_primes h₁ h₂ h₃ h12 h13 h23, ArithmeticFunction.moebius_apply_prime hℓp, hμ]
    norm_num
  · have : (u : ℝ) < ℓ * ((p₁ * p₂ * p₃ : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hℓ0] at hlo; linarith
    exact_mod_cast this
  · have hw := amplified_window_le (u := (u : ℝ)) hℓ1 hℓu
    have h1 := mul_le_mul_of_nonneg_left hhi hℓ0.le
    have e : (ℓ : ℝ) * ((u : ℝ) / ℓ) = u := by field_simp
    rw [mul_add, e] at h1
    push_cast at h1 ⊢
    linarith
  · intro p hp
    rw [Nat.primeFactors_mul hℓp.ne_zero
      (Nat.mul_ne_zero (Nat.mul_ne_zero h₁.ne_zero h₂.ne_zero) h₃.ne_zero), hℓp.primeFactors,
      Finset.mem_union, Finset.mem_singleton] at hp
    rcases hp with rfl | hp
    · exact hℓΛ.trans (le_max_left _ _)
    · rcases mem_primeFactors_three h₁ h₂ h₃ hp with rfl | rfl | rfl
      · exact (hq1.trans hsqrt).trans (le_max_right _ _)
      · exact (hq2.trans hsqrt).trans (le_max_right _ _)
      · exact (hq3.trans hsqrt).trans (le_max_right _ _)

/-- `2(log y)^{11/10} ≤ √y` and `9 ≤ (log y)^{11/10}` for large `y`. -/
theorem eventually_smallPrimeScale_le_sqrt :
    ∀ᶠ y : ℝ in atTop, 2 * Real.log y ^ (11 / 10 : ℝ) ≤ Real.sqrt y ∧
      9 ≤ Real.log y ^ (11 / 10 : ℝ) := by
  filter_upwards [eventually_polylog_le_rpow 2 (C := 2) (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2),
    Real.tendsto_log_atTop.eventually_ge_atTop 9, eventually_gt_atTop (0 : ℝ)] with y h1 h9 hy0
  have hl1 : 1 ≤ Real.log y := by linarith
  have hP : Real.log y ≤ Real.log y ^ (11 / 10 : ℝ) := by
    have := Real.rpow_le_rpow_of_exponent_le hl1 (by norm_num : (1 : ℝ) ≤ 11 / 10)
    rwa [Real.rpow_one] at this
  have hP2 : Real.log y ^ (11 / 10 : ℝ) ≤ Real.log y ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_le hl1 (by norm_num : (11 / 10 : ℝ) ≤ 2)
    rwa [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have hle : Real.log y ≤ 1 + Real.log (24 * y) := by
    rw [Real.log_mul (by norm_num) hy0.ne']
    have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
    linarith
  have h2 : 2 * Real.log y ^ 2 ≤ 2 * (1 + Real.log (24 * y)) ^ 2 := by gcongr
  rw [← Real.sqrt_eq_rpow] at h1
  exact ⟨by linarith, by linarith⟩
/-- The displacement is at most `u` once `ℓ (log u)^4 ≤ u` and `log u ≥ 1`. -/
theorem sqrt_mul_log_rpow_le_self {u ℓ : ℝ} (hu : 0 < u) (hℓ : 0 ≤ ℓ) (hlu : 1 ≤ Real.log u)
    (h : ℓ * Real.log u ^ 4 ≤ u) : Real.sqrt (u * ℓ) * Real.log u ^ (31 / 20 : ℝ) ≤ u := by
  have hl0 : 0 < Real.log u := by linarith
  have hpow : (Real.log u ^ (31 / 20 : ℝ)) ^ 2 ≤ Real.log u ^ 4 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le, ← Real.rpow_natCast (Real.log u) 4]
    exact Real.rpow_le_rpow_of_exponent_le hlu (by norm_num)
  have hsq : (Real.sqrt (u * ℓ) * Real.log u ^ (31 / 20 : ℝ)) ^ 2 ≤ u ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    calc u * ℓ * (Real.log u ^ (31 / 20 : ℝ)) ^ 2 ≤ u * ℓ * Real.log u ^ 4 :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = u * (ℓ * Real.log u ^ 4) := by ring
      _ ≤ u * u := mul_le_mul_of_nonneg_left h hu.le
      _ = u ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (by positivity) hu.le two_ne_zero).1 hsq

/-- **Admission of one block.**  Assume `(E1)` and `(E2)`.  For all large `N`, every squarefree `u`
with `N^δ ≤ u ≤ N^K` and every support `1 ≤ M ≤ N^K` admit a squarefree `Q` with
`μ(Q) = -μ(u)`, `(Q, M) = 1`, `u < Q ≤ min(2u, u + √(uℓ) (log u)^{31/20})` for some
`1 ≤ ℓ ≤ C log N`, and every prime factor of `Q` at most `max(C log N, √u)`. -/
theorem exists_block_step (hDI : MTDeshouillersIwaniecBound) (hW : MTWattBound) {δ K : ℝ}
    (hδ : 0 < δ) (hK : 0 < K) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℝ in atTop, ∀ u M : ℕ, N ^ δ ≤ u → (u : ℝ) ≤ N ^ K → 1 ≤ M →
      (M : ℝ) ≤ N ^ K → ArithmeticFunction.moebius u ≠ 0 →
      ∃ Q ℓ : ℕ, Squarefree Q ∧ ArithmeticFunction.moebius Q = -ArithmeticFunction.moebius u ∧
        Nat.Coprime Q M ∧ 1 ≤ ℓ ∧ (ℓ : ℝ) ≤ C * Real.log N ∧ u < Q ∧
        (Q : ℝ) ≤ u + Real.sqrt (u * ℓ) * Real.log u ^ (31 / 20 : ℝ) ∧ (Q : ℝ) ≤ 2 * u ∧
        ∀ p ∈ Q.primeFactors, (p : ℝ) ≤ max (C * Real.log N) (Real.sqrt u) := by
  have hB : 0 < 4 * K / δ := by positivity
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (eventually_exists_coprime_threePrime hDI hW hB)
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.1 GaloisForLFunctions.HTGeometry.eventually_theta_ge_half
  obtain ⟨x₁, hx₁⟩ := eventually_atTop.1 eventually_smallPrimeScale_le_sqrt
  set C : ℝ := 3 * K + 3 with hCdef
  have hC1 : 1 ≤ C := by rw [hCdef]; linarith
  refine ⟨C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (3 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (max 1 y₀),
    (tendsto_rpow_atTop (by positivity : (0 : ℝ) < δ / 2)).eventually_ge_atTop (max (max x₀ x₁) 1),
    eventually_polylog_le_rpow 1 (C := C) (by positivity) (by positivity : (0 : ℝ) < δ / 2),
    eventually_polylog_le_rpow 1 (C := C) (by positivity) hK,
    eventually_polylog_le_rpow 5 (C := C * (K + 1) ^ 4) (by positivity) hδ,
    Real.tendsto_log_atTop.eventually_ge_atTop (1 / δ)]
    with N hN3 hlogN hNδ hCδ hCK hC5 hlogδ
  intro u M hu1 hu2 hM1 hM2 hμ
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := le_trans (le_max_left _ _) hlogN
  have hlogle : Real.log N ≤ 1 + Real.log (24 * N) := by
    rw [Real.log_mul (by norm_num) hN0.ne']
    have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
    linarith
  have hCδ' : C * Real.log N ≤ N ^ (δ / 2) := by
    have := mul_le_mul_of_nonneg_left hlogle (by positivity : (0 : ℝ) ≤ C)
    simp only [pow_one] at hCδ; linarith
  have hCK' : C * Real.log N ≤ N ^ K := by
    have := mul_le_mul_of_nonneg_left hlogle (by positivity : (0 : ℝ) ≤ C)
    simp only [pow_one] at hCK; linarith
  have hNδ2 : N ^ δ = N ^ (δ / 2) * N ^ (δ / 2) := by
    rw [← Real.rpow_add hN0]; ring_nf
  have hNδ1 : 1 ≤ N ^ (δ / 2) := le_trans (le_max_right _ _) hNδ
  have hNδN : max (max x₀ x₁) 1 ≤ N ^ δ := by nlinarith
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le (by positivity) hu1
  have hM0 : M ≠ 0 := by omega
  have hΛ1 : 1 ≤ C * Real.log N := by nlinarith
  -- `log u ≥ 1` and `C log N (log u)^4 ≤ u`
  have hlogu : 1 ≤ Real.log u := by
    have h1 := Real.log_le_log (by positivity) hu1
    rw [Real.log_rpow hN0] at h1
    have := mul_le_mul_of_nonneg_left hlogδ hδ.le
    rw [mul_one_div_cancel hδ.ne'] at this
    linarith
  have hloguK : Real.log u ≤ K * Real.log N := by
    have := Real.log_le_log hu0 hu2
    rwa [Real.log_rpow hN0] at this
  have hdisp : ∀ ℓ : ℝ, 0 ≤ ℓ → ℓ ≤ C * Real.log N →
      Real.sqrt (u * ℓ) * Real.log u ^ (31 / 20 : ℝ) ≤ u := by
    intro ℓ hℓ0 hℓ
    refine sqrt_mul_log_rpow_le_self hu0 hℓ0 hlogu ?_
    have h1 : Real.log u ^ 4 ≤ ((K + 1) * Real.log N) ^ 4 :=
      pow_le_pow_left₀ (by linarith) (by nlinarith) 4
    have h2 : ℓ * Real.log u ^ 4 ≤ C * Real.log N * ((K + 1) * Real.log N) ^ 4 :=
      mul_le_mul hℓ h1 (by positivity) (by positivity)
    have h3 : C * Real.log N * ((K + 1) * Real.log N) ^ 4 ≤ C * (K + 1) ^ 4 *
        (1 + Real.log (24 * N)) ^ 5 := by
      have : Real.log N ^ 5 ≤ (1 + Real.log (24 * N)) ^ 5 := pow_le_pow_left₀ (by linarith) hlogle 5
      have e : C * Real.log N * ((K + 1) * Real.log N) ^ 4 = C * (K + 1) ^ 4 * Real.log N ^ 5 := by
        ring
      rw [e]; gcongr
    linarith
  have hfin : ∀ Q ℓ : ℕ, Squarefree Q ∧ ArithmeticFunction.moebius Q = -ArithmeticFunction.moebius u ∧
      Nat.Coprime Q M ∧ 1 ≤ ℓ ∧ (ℓ : ℝ) ≤ C * Real.log N ∧ u < Q ∧
      (Q : ℝ) ≤ u + Real.sqrt (u * ℓ) * Real.log u ^ (31 / 20 : ℝ) ∧
      (∀ p ∈ Q.primeFactors, (p : ℝ) ≤ max (C * Real.log N) (Real.sqrt u)) →
      ∃ Q ℓ : ℕ, Squarefree Q ∧ ArithmeticFunction.moebius Q = -ArithmeticFunction.moebius u ∧
        Nat.Coprime Q M ∧ 1 ≤ ℓ ∧ (ℓ : ℝ) ≤ C * Real.log N ∧ u < Q ∧
        (Q : ℝ) ≤ u + Real.sqrt (u * ℓ) * Real.log u ^ (31 / 20 : ℝ) ∧ (Q : ℝ) ≤ 2 * u ∧
        ∀ p ∈ Q.primeFactors, (p : ℝ) ≤ max (C * Real.log N) (Real.sqrt u) := by
    rintro Q ℓ ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩
    refine ⟨Q, ℓ, a1, a2, a3, a4, a5, a6, a7, ?_, a8⟩
    have := hdisp ℓ (Nat.cast_nonneg _) a5
    linarith
  rcases CofactorParity.moebius_eq_one_or_neg_one
    (ArithmeticFunction.moebius_ne_zero_iff_squarefree.1 hμ) with hμ1 | hμ1
  · have hux : max (max x₀ x₁) 1 ≤ (u : ℝ) := hNδN.trans hu1
    have hMu : (M : ℝ) ≤ (u : ℝ) ^ (4 * K / δ) := by
      refine hM2.trans ?_
      have h1 : N ^ K ≤ (N ^ δ) ^ (4 * K / δ) := by
        rw [← Real.rpow_mul hN0.le, show δ * (4 * K / δ) = 4 * K by field_simp]
        exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      exact h1.trans (Real.rpow_le_rpow (by positivity) hu1 hB.le)
    have hx0u : x₀ ≤ (u : ℝ) := by
      have := le_max_left x₀ x₁; have := le_max_left (max x₀ x₁) 1; linarith
    have hx1u : x₁ ≤ (u : ℝ) := by
      have := le_max_right x₀ x₁; have := le_max_left (max x₀ x₁) 1; linarith
    obtain ⟨p₁, p₂, p₃, htok⟩ := hx₀ (u : ℝ) hx0u M hM1 hMu
    obtain ⟨hs1, hs9⟩ := hx₁ (u : ℝ) hx1u
    obtain ⟨Q, ℓ, h⟩ := block_step_of_token ((le_max_right _ _).trans hux) hΛ1 hμ1 hs1 hs9 htok
    exact hfin Q ℓ h
  · have hθ : Real.log M < Chebyshev.theta (C * Real.log N) := by
      have h1 : y₀ ≤ C * Real.log N := by
        have := le_max_right 1 y₀
        nlinarith
      have h2 := hy₀ _ h1
      have h3 : Real.log M ≤ K * Real.log N := by
        have := Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) hM2
        rwa [Real.log_rpow hN0] at this
      have h4 : K * Real.log N < C * Real.log N / 2 := by
        rw [hCdef]; nlinarith
      linarith
    obtain ⟨ℓ, hℓp, hℓle, hℓM⟩ := exists_prime_le_not_dvd hM0 hθ
    have hℓ1 : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓp.one_lt.le
    have hℓ0 : (0 : ℝ) < ℓ := by linarith
    have huℓ : N ^ (δ / 2) ≤ (u : ℝ) / ℓ := by
      rw [le_div_iff₀ hℓ0]
      calc N ^ (δ / 2) * ℓ ≤ N ^ (δ / 2) * N ^ (δ / 2) :=
            mul_le_mul_of_nonneg_left (hℓle.trans hCδ') (by positivity)
        _ = N ^ δ := hNδ2.symm
        _ ≤ u := hu1
    have hux : max (max x₀ x₁) 1 ≤ (u : ℝ) / ℓ := hNδ.trans huℓ
    have hMℓ : ((M * ℓ : ℕ) : ℝ) ≤ ((u : ℝ) / ℓ) ^ (4 * K / δ) := by
      push_cast
      have h1 : (M : ℝ) * ℓ ≤ N ^ K * N ^ K :=
        mul_le_mul hM2 (hℓle.trans hCK') hℓ0.le (by positivity)
      have h2 : N ^ K * N ^ K = (N ^ (δ / 2)) ^ (4 * K / δ) := by
        rw [← Real.rpow_add hN0, ← Real.rpow_mul hN0.le]; congr 1; field_simp; ring
      rw [h2] at h1
      exact h1.trans (Real.rpow_le_rpow (by positivity) huℓ hB.le)
    have hx0u : x₀ ≤ (u : ℝ) / ℓ := by
      have := le_max_left x₀ x₁; have := le_max_left (max x₀ x₁) 1; linarith
    have hx1u : x₁ ≤ (u : ℝ) / ℓ := by
      have := le_max_right x₀ x₁; have := le_max_left (max x₀ x₁) 1; linarith
    obtain ⟨p₁, p₂, p₃, htok⟩ := hx₀ _ hx0u (M * ℓ)
      (Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hM0 hℓp.ne_zero)) hMℓ
    obtain ⟨hs1, hs9⟩ := hx₁ _ hx1u
    have hℓu : (ℓ : ℝ) ≤ u := by
      have h1 : (ℓ : ℝ) ≤ N ^ (δ / 2) := hℓle.trans hCδ'
      have h2 : N ^ (δ / 2) ≤ N ^ δ := by
        rw [hNδ2]; exact le_mul_of_one_le_left (by positivity) hNδ1
      linarith only [h1, h2, hu1]
    obtain ⟨Q, ℓ', h⟩ := block_step_of_prime_token hℓp hℓM hℓle hℓu hμ1 hs1 hs9 htok
    exact hfin Q ℓ' h

/-- The accumulated support of the first `k ≤ r` stages: `A₀ ∏ u_j ∏_{i<k} Q_i ≤ N^{(3r+1)K}` when
`A₀, u_j ≤ N^K` and `Q_i ≤ N^{2K}`. -/
theorem accumulated_support_le {r k A₀ : ℕ} {u : Fin r → ℕ} {Q : ℕ → ℕ} {N K : ℝ} (hN : 1 ≤ N)
    (hK : 0 ≤ K) (hk : k ≤ r) (hA : (A₀ : ℝ) ≤ N ^ K) (hu : ∀ j, (u j : ℝ) ≤ N ^ K)
    (hQ : ∀ i < k, (Q i : ℝ) ≤ N ^ (2 * K)) :
    (((A₀ * ∏ j, u j) * ∏ i ∈ Finset.range k, Q i : ℕ) : ℝ) ≤ N ^ ((3 * r + 1) * K) := by
  have hN0 : 0 < N := by linarith
  have hNK : 1 ≤ N ^ K := Real.one_le_rpow hN hK
  have hN2K : 1 ≤ N ^ (2 * K) := Real.one_le_rpow hN (by linarith)
  push_cast
  have h1 : (∏ j, (u j : ℝ)) ≤ (N ^ K) ^ r := by
    calc (∏ j, (u j : ℝ)) ≤ ∏ _j : Fin r, N ^ K :=
          Finset.prod_le_prod (fun j _ => Nat.cast_nonneg _) fun j _ => hu j
      _ = (N ^ K) ^ r := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h2 : (∏ i ∈ Finset.range k, (Q i : ℝ)) ≤ (N ^ (2 * K)) ^ r := by
    calc (∏ i ∈ Finset.range k, (Q i : ℝ)) ≤ ∏ _i ∈ Finset.range k, N ^ (2 * K) :=
          Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _)
            fun i hi => hQ i (Finset.mem_range.1 hi)
      _ = (N ^ (2 * K)) ^ k := by rw [Finset.prod_const, Finset.card_range]
      _ ≤ (N ^ (2 * K)) ^ r := pow_le_pow_right₀ hN2K hk
  have e : N ^ ((3 * r + 1) * K) = N ^ K * (N ^ K) ^ r * (N ^ (2 * K)) ^ r := by
    rw [← Real.rpow_mul_natCast hN0.le, ← Real.rpow_mul_natCast hN0.le, ← Real.rpow_add hN0,
      ← Real.rpow_add hN0]
    congr 1; ring
  rw [e]
  have hp1 : 0 ≤ ∏ j, (u j : ℝ) := Finset.prod_nonneg fun j _ => Nat.cast_nonneg _
  have hp2 : 0 ≤ ∏ i ∈ Finset.range k, (Q i : ℝ) := Finset.prod_nonneg fun i _ => Nat.cast_nonneg _
  gcongr

/-- **Simultaneous block admission (FS14).**  Assume `(E1)` and `(E2)`.  Fix `δ, K > 0` and `r`.
For all large `N`, any `r` squarefree blocks `N^δ ≤ u_i ≤ N^K` and any support `1 ≤ A₀ ≤ N^K`
admit squarefree replacements `Q_i` with `μ(Q_i) = -μ(u_i)`, pairwise coprime and coprime to
`A₀ ∏ u_j`, with `u_i < Q_i ≤ u_i + √(u_i ℓ_i) (log u_i)^{31/20}` for some `1 ≤ ℓ_i ≤ C log N`
and every prime factor of `Q_i` at most `max(C log N, √u_i)`.  The blocks are processed in turn,
each against the accumulated support. -/
theorem eventually_block_admission (hDI : MTDeshouillersIwaniecBound) (hW : MTWattBound)
    {δ K : ℝ} (hδ : 0 < δ) (hK : 0 < K) (r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℝ in atTop, ∀ (u : Fin r → ℕ) (A₀ : ℕ), 1 ≤ A₀ →
      (A₀ : ℝ) ≤ N ^ K → (∀ i, N ^ δ ≤ u i) → (∀ i, (u i : ℝ) ≤ N ^ K) →
      (∀ i, ArithmeticFunction.moebius (u i) ≠ 0) →
      ∃ Q ℓ : Fin r → ℕ, (∀ i, Squarefree (Q i)) ∧
        (∀ i, ArithmeticFunction.moebius (Q i) = -ArithmeticFunction.moebius (u i)) ∧
        (∀ i j, i ≠ j → Nat.Coprime (Q i) (Q j)) ∧ (∀ i, Nat.Coprime (Q i) (A₀ * ∏ j, u j)) ∧
        (∀ i, 1 ≤ ℓ i ∧ (ℓ i : ℝ) ≤ C * Real.log N) ∧
        (∀ i, u i < Q i ∧
          (Q i : ℝ) ≤ u i + Real.sqrt (u i * ℓ i) * Real.log (u i) ^ (31 / 20 : ℝ)) ∧
        (∀ i, ∀ p ∈ (Q i).primeFactors, (p : ℝ) ≤ max (C * Real.log N) (Real.sqrt (u i))) := by
  classical
  have hK' : 0 < (3 * r + 1) * K := by positivity
  obtain ⟨C, hC, hstep⟩ := exists_block_step hDI hW hδ hK'
  refine ⟨C, hC, ?_⟩
  filter_upwards [hstep, eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hK).eventually_ge_atTop 2] with N hN hN1 hNK2
  intro u A₀ hA1 hA2 hu1 hu2 hμ
  have hN0 : 0 < N := by linarith
  have hKle : N ^ K ≤ N ^ ((3 * r + 1) * K) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by nlinarith)
  have hN2K : 2 * N ^ K ≤ N ^ (2 * K) := by
    rw [show 2 * K = K + K by ring, Real.rpow_add hN0]
    exact mul_le_mul_of_nonneg_right hNK2 (by positivity)
  -- the stages
  let uN : ℕ → ℕ := fun i => if h : i < r then u ⟨i, h⟩ else 1
  have huN : ∀ i (h : i < r), uN i = u ⟨i, h⟩ := fun i h => by simp [uN, h]
  have key : ∀ k ≤ r, ∃ Q ℓ : ℕ → ℕ,
      (∀ i (hi : i < k), Squarefree (Q i) ∧
        ArithmeticFunction.moebius (Q i) = -ArithmeticFunction.moebius (uN i) ∧
        1 ≤ ℓ i ∧ (ℓ i : ℝ) ≤ C * Real.log N ∧ uN i < Q i ∧
        (Q i : ℝ) ≤ uN i + Real.sqrt (uN i * ℓ i) * Real.log (uN i) ^ (31 / 20 : ℝ) ∧
        (Q i : ℝ) ≤ 2 * uN i ∧
        ∀ p ∈ (Q i).primeFactors, (p : ℝ) ≤ max (C * Real.log N) (Real.sqrt (uN i))) ∧
      (∀ i j, i < k → j < k → i ≠ j → Nat.Coprime (Q i) (Q j)) ∧
      (∀ i < k, Nat.Coprime (Q i) (A₀ * ∏ j, u j)) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨fun _ => 1, fun _ => 1, fun i hi => absurd hi (Nat.not_lt_zero _),
        fun i j hi => absurd hi (Nat.not_lt_zero _), fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ k ih =>
      intro hk
      obtain ⟨Q, ℓ, hQ, hcop, hcopA⟩ := ih (by omega)
      have hkr : k < r := by omega
      set M := (A₀ * ∏ j, u j) * ∏ i ∈ Finset.range k, Q i with hMdef
      have hQ2 : ∀ i < k, (Q i : ℝ) ≤ N ^ (2 * K) := by
        intro i hi
        have h1 := (hQ i hi).2.2.2.2.2.2.1
        have hi' : i < r := by omega
        rw [huN i hi'] at h1
        linarith [hu2 ⟨i, hi'⟩]
      have hM1 : 1 ≤ M := by
        have hup : ∀ j, 0 < u j := fun j => by
          have := hu1 j
          exact_mod_cast (show (0 : ℝ) < u j from lt_of_lt_of_le (by positivity) this)
        have hQp : ∀ i ∈ Finset.range k, 0 < Q i := fun i hi => by
          have := (hQ i (Finset.mem_range.1 hi)).2.2.2.2.1
          omega
        exact Nat.one_le_iff_ne_zero.2 (Nat.pos_iff_ne_zero.1 (Nat.mul_pos (Nat.mul_pos (by omega)
          (Finset.prod_pos fun j _ => hup j)) (Finset.prod_pos hQp)))
      have hMle : (M : ℝ) ≤ N ^ ((3 * r + 1) * K) :=
        accumulated_support_le hN1 hK.le (by omega) hA2 hu2 hQ2
      obtain ⟨Q', ℓ', a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := hN (u ⟨k, hkr⟩) M (hu1 _)
        ((hu2 _).trans hKle) hM1 hMle (hμ _)
      refine ⟨Function.update Q k Q', Function.update ℓ k ℓ', ?_, ?_, ?_⟩
      · intro i hi
        by_cases hik : i = k
        · subst hik
          simp only [Function.update_self, huN i hkr]
          exact ⟨a1, a2, a4, a5, a6, a7, a8, a9⟩
        · have hi' : i < k := by omega
          simp only [Function.update_of_ne hik]
          exact hQ i hi'
      · intro i j hi hj hij
        have hdvd : ∀ i < k, Q i ∣ M := fun i hi =>
          Dvd.dvd.mul_left (Finset.dvd_prod_of_mem Q (Finset.mem_range.2 hi)) _
        by_cases hik : i = k
        · subst hik
          have hjk : j ≠ i := fun h => hij h.symm
          simp only [Function.update_self, Function.update_of_ne hjk]
          exact Nat.Coprime.coprime_dvd_right (hdvd j (by omega)) a3
        · by_cases hjk : j = k
          · subst hjk
            simp only [Function.update_self, Function.update_of_ne hik]
            exact (Nat.Coprime.coprime_dvd_right (hdvd i (by omega)) a3).symm
          · simp only [Function.update_of_ne hik, Function.update_of_ne hjk]
            exact hcop i j (by omega) (by omega) hij
      · intro i hi
        by_cases hik : i = k
        · subst hik
          simp only [Function.update_self]
          exact Nat.Coprime.coprime_dvd_right (dvd_mul_right _ _) a3
        · simp only [Function.update_of_ne hik]
          exact hcopA i (by omega)
  obtain ⟨Q, ℓ, hQ, hcop, hcopA⟩ := key r le_rfl
  refine ⟨fun i => Q i, fun i => ℓ i, fun i => (hQ i i.2).1, fun i => ?_, fun i j hij => ?_,
    fun i => hcopA i i.2, fun i => ⟨(hQ i i.2).2.2.1, (hQ i i.2).2.2.2.1⟩, fun i => ?_, fun i => ?_⟩
  · have := (hQ i i.2).2.1
    rwa [huN i i.2] at this
  · exact hcop i j i.2 j.2 (fun h => hij (Fin.ext h))
  · obtain ⟨-, -, -, -, h5, h6, -, -⟩ := hQ i i.2
    rw [huN i i.2] at h5 h6
    exact ⟨h5, h6⟩
  · have := (hQ i i.2).2.2.2.2.2.2.2
    rwa [huN i i.2] at this

end

end RHTower.Sieve
