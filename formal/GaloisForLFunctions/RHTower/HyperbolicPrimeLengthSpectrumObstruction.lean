import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.LinearCombination
import Mathlib.NumberTheory.Real.Irrational

/-!
# The primes are not a hyperbolic length spectrum

A hyperbolic element of `SL₂(ℝ)` with translation length `l` has trace `±2 cosh(l/2)`.  A closed
geodesic of length `k log r` therefore has trace `±(√r^k + √r^{−k})`.  Call `t` a *prime-length trace*
(`IsPrimeLengthTrace`) if `t = ±2` or `t = ±(√r^k + (√r^k)⁻¹)` for a prime `r` and `k ≥ 1`.

**Theorem** (`false_of_mem_of_primeLengthTraces`).  Let `G ≤ SL₂(ℝ)` be a subgroup all of whose traces are
prime-length traces.  Then `G` cannot contain elements `A`, `B` with traces `±(√p + 1/√p)` and
`±(√q + 1/√q)` for distinct primes `p ≠ q`.

So no Fuchsian group without elliptic elements, of finite or infinite covolume, has all its closed
geodesic lengths in `{k log r : r prime}` with two different primes occurring.  The primes are not the
length spectrum of any hyperbolic surface.  The proof is elementary.

**Proof.**  Fricke's identity `tr(AB) + tr(AB⁻¹) = tr A · tr B`
(`trace_mul_add_trace_mul_adjugate`, using `B⁻¹ = adj B` in `SL₂`) gives
`tr(AB) + tr(AB⁻¹) = ±(p+1)(q+1)/(pq) · √(pq)`.  Every prime-length trace is rational or a rational
multiple of `√r` for a prime `r` (`rat_or_rat_mul_sqrt_of_isPrimeLengthTrace`).  The products `pq` and
`pqr` are never squares, so `√(pq)`, `√r` and `√(pqr)` are irrational.  Two-term independence of square
roots (`eq_zero_of_mul_sqrt_add_mul_sqrt_eq_rat`), applied after one squaring, then forces the
coefficient of `√(pq)` to vanish, which is impossible.
-/

open Matrix

noncomputable section

namespace RHTower.HyperbolicPrimeLengthSpectrum

/-! ### Fricke's trace identity -/

/-- `tr(AB) + tr(A · adj B) = tr A · tr B` for `2 × 2` matrices. -/
theorem trace_mul_add_trace_mul_adjugate (A B : Matrix (Fin 2) (Fin 2) ℝ) :
    trace (A * B) + trace (A * adjugate B) = trace A * trace B := by
  simp [trace_fin_two, adjugate_fin_two, mul_apply, Fin.sum_univ_two]
  ring

/-! ### Prime-length traces -/

/-- `t = ±2`, or `t = ±(√r^k + (√r^k)⁻¹)` with `r` prime and `k ≥ 1`: the trace of the identity, of a
parabolic element, or of a hyperbolic element whose translation length is `k log r`. -/
def IsPrimeLengthTrace (t : ℝ) : Prop :=
  t = 2 ∨ t = -2 ∨ ∃ r k : ℕ, r.Prime ∧ 1 ≤ k ∧
    (t = √(r : ℝ) ^ k + (√(r : ℝ) ^ k)⁻¹ ∨ t = -(√(r : ℝ) ^ k + (√(r : ℝ) ^ k)⁻¹))

/-- A prime-length trace is rational or a rational multiple of `√r` for a prime `r`. -/
theorem rat_or_rat_mul_sqrt_of_isPrimeLengthTrace {t : ℝ} (ht : IsPrimeLengthTrace t) :
    (∃ a : ℚ, t = a) ∨ ∃ r : ℕ, r.Prime ∧ ∃ a : ℚ, t = a * √(r : ℝ) := by
  rcases ht with rfl | rfl | ⟨r, k, hr, -, hk⟩
  · exact Or.inl ⟨2, by norm_num⟩
  · exact Or.inl ⟨-2, by norm_num⟩
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr.pos
  have hs : √(r : ℝ) ^ 2 = r := Real.sq_sqrt hr0.le
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · left
    have he : √(r : ℝ) ^ (2 * j) = (r : ℝ) ^ j := by rw [pow_mul, hs]
    rcases hk with rfl | rfl
    · exact ⟨(r : ℚ) ^ j + ((r : ℚ) ^ j)⁻¹, by rw [he]; push_cast; ring⟩
    · exact ⟨-((r : ℚ) ^ j + ((r : ℚ) ^ j)⁻¹), by rw [he]; push_cast; ring⟩
  · right
    refine ⟨r, hr, ?_⟩
    have ho : √(r : ℝ) ^ (2 * j + 1) = (r : ℝ) ^ j * √(r : ℝ) := by rw [pow_succ, pow_mul, hs]
    have hmul : ((r : ℝ) ^ j * √(r : ℝ)) * (((r : ℝ) ^ (j + 1))⁻¹ * √(r : ℝ)) = 1 := by
      have hpow : (r : ℝ) ^ (j + 1) ≠ 0 := pow_ne_zero _ hr0.ne'
      calc ((r : ℝ) ^ j * √(r : ℝ)) * (((r : ℝ) ^ (j + 1))⁻¹ * √(r : ℝ))
          = ((r : ℝ) ^ j * √(r : ℝ) ^ 2) * ((r : ℝ) ^ (j + 1))⁻¹ := by ring
        _ = (r : ℝ) ^ (j + 1) * ((r : ℝ) ^ (j + 1))⁻¹ := by rw [hs, pow_succ]
        _ = 1 := mul_inv_cancel₀ hpow
    have hinv := inv_eq_of_mul_eq_one_right hmul
    rcases hk with rfl | rfl
    · exact ⟨(r : ℚ) ^ j + ((r : ℚ) ^ (j + 1))⁻¹, by rw [ho, hinv]; push_cast; ring⟩
    · exact ⟨-((r : ℚ) ^ j + ((r : ℚ) ^ (j + 1))⁻¹), by rw [ho, hinv]; push_cast; ring⟩

/-! ### Independence of two square roots -/

/-- If `x√m + y√n = w` with `x, y, w` rational and `√m`, `√n`, `√(mn)` irrational, then
`x = y = 0`. -/
theorem eq_zero_of_mul_sqrt_add_mul_sqrt_eq_rat {m n : ℚ} (hm0 : 0 ≤ m) (hn0 : 0 ≤ n)
    (hm : Irrational √(m : ℝ)) (hn : Irrational √(n : ℝ)) (hmn : Irrational √((m : ℝ) * n))
    {x y w : ℚ} (h : (x : ℝ) * √(m : ℝ) + (y : ℝ) * √(n : ℝ) = w) : x = 0 ∧ y = 0 := by
  have hm0' : (0 : ℝ) ≤ m := by exact_mod_cast hm0
  have hn0' : (0 : ℝ) ≤ n := by exact_mod_cast hn0
  have hm2 : √(m : ℝ) ^ 2 = m := Real.sq_sqrt hm0'
  have hn2 : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hn0'
  have hmn2 : √((m : ℝ) * n) = √(m : ℝ) * √(n : ℝ) := Real.sqrt_mul hm0' _
  have hm0 : √(m : ℝ) ≠ 0 := fun h0 => hm.ne_rat 0 (by simpa using h0)
  have hwy : w * y = 0 := by
    by_contra hne
    have hlin : (2 * (w : ℝ) * y) * √(n : ℝ) =
        (w : ℝ) ^ 2 + (y : ℝ) ^ 2 * n - (x : ℝ) ^ 2 * m := by
      have hxm : (x : ℝ) * √(m : ℝ) = w - y * √(n : ℝ) := by linarith
      have hsq : ((x : ℝ) * √(m : ℝ)) ^ 2 = ((w : ℝ) - y * √(n : ℝ)) ^ 2 := by rw [hxm]
      rw [mul_pow, hm2, sub_sq, mul_pow, hn2] at hsq
      linear_combination hsq
    have hc : (2 * (w : ℝ) * y) ≠ 0 := by
      have h1 : (2 * w * y : ℚ) ≠ 0 := by
        rw [mul_assoc]; exact mul_ne_zero two_ne_zero hne
      exact_mod_cast h1
    apply hn.ne_rat (((w ^ 2 + y ^ 2 * n - x ^ 2 * m) / (2 * w * y) : ℚ))
    push_cast
    rw [eq_div_iff hc]
    linear_combination hlin
  rcases mul_eq_zero.mp hwy with hw | hy
  · subst hw
    have h' : (x : ℝ) * √(m : ℝ) + (y : ℝ) * √(n : ℝ) = 0 := by simpa using h
    have hy : y = 0 := by
      by_contra hy
      have hy' : (y : ℝ) ≠ 0 := by exact_mod_cast hy
      apply hmn.ne_rat ((-(x * m) / y : ℚ))
      push_cast
      rw [eq_div_iff hy', hmn2]
      have h3 : ((x : ℝ) * √(m : ℝ) + y * √(n : ℝ)) * √(m : ℝ) = 0 := by rw [h']; ring
      linear_combination h3 - (x : ℝ) * hm2
    subst hy
    refine ⟨?_, rfl⟩
    have h4 : (x : ℝ) * √(m : ℝ) = 0 := by simpa using h'
    rcases mul_eq_zero.mp h4 with h1 | h1
    · exact_mod_cast h1
    · exact absurd h1 hm0
  · subst hy
    refine ⟨?_, rfl⟩
    have h' : (x : ℝ) * √(m : ℝ) = w := by simpa using h
    by_contra hx
    have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx
    apply hm.ne_rat (w / x)
    push_cast
    rw [eq_div_iff hx']
    linear_combination h'

/-! ### Squares of prime products -/

theorem not_isSquare_mul_of_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ¬IsSquare (p * q) := by
  rintro ⟨m, hm⟩
  have hpm : p ∣ m := by
    have : p ∣ m * m := hm ▸ dvd_mul_right p q
    rcases (Nat.Prime.dvd_mul hp).mp this with h | h <;> exact h
  obtain ⟨k, rfl⟩ := hpm
  have hq' : q = p * (k * k) := by
    have h2 : p * q = p * (p * (k * k)) := by rw [hm]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos h2
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp ⟨k * k, hq'⟩)

theorem not_isSquare_mul_mul_of_prime {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) : ¬IsSquare (p * q * r) := by
  rintro ⟨m, hm⟩
  by_cases hrp : r = p
  · subst hrp
    have hqm : q ∣ m := by
      have : q ∣ m * m := hm ▸ ⟨r * r, by ring⟩
      rcases (Nat.Prime.dvd_mul hq).mp this with h | h <;> exact h
    obtain ⟨k, rfl⟩ := hqm
    have h2 : r * r = q * (k * k) := by
      have h3 : q * (r * r) = q * (q * (k * k)) := by
        calc q * (r * r) = r * q * r := by ring
          _ = q * k * (q * k) := hm
          _ = q * (q * (k * k)) := by ring
      exact Nat.eq_of_mul_eq_mul_left hq.pos h3
    have hqr : q ∣ r * r := ⟨k * k, h2⟩
    rcases (Nat.Prime.dvd_mul hq).mp hqr with h | h <;>
      exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp h).symm
  · have hpm : p ∣ m := by
      have : p ∣ m * m := hm ▸ ⟨q * r, by ring⟩
      rcases (Nat.Prime.dvd_mul hp).mp this with h | h <;> exact h
    obtain ⟨k, rfl⟩ := hpm
    have h2 : q * r = p * (k * k) := by
      have h3 : p * (q * r) = p * (p * (k * k)) := by
        calc p * (q * r) = p * q * r := by ring
          _ = p * k * (p * k) := hm
          _ = p * (p * (k * k)) := by ring
      exact Nat.eq_of_mul_eq_mul_left hp.pos h3
    have hpqr : p ∣ q * r := ⟨k * k, h2⟩
    rcases (Nat.Prime.dvd_mul hp).mp hpqr with h | h
    · exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
    · exact hrp ((Nat.prime_dvd_prime_iff_eq hp hr).mp h).symm

/-! ### The arithmetic obstruction -/

theorem irrational_sqrt_mul {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Irrational √((p : ℝ) * q) := by
  have := irrational_sqrt_natCast_iff.mpr (not_isSquare_mul_of_prime hp hq hpq)
  simpa using this

theorem irrational_sqrt_mul_mul {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) : Irrational √((p : ℝ) * q * r) := by
  have := irrational_sqrt_natCast_iff.mpr (not_isSquare_mul_mul_of_prime hp hq hr hpq)
  simpa using this

/-- `(√p + 1/√p)(√q + 1/√q) = (p+1)(q+1)/(pq) · √(pq)`. -/
theorem prime_trace_mul_eq {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    (√(p : ℝ) + (√(p : ℝ))⁻¹) * (√(q : ℝ) + (√(q : ℝ))⁻¹) =
      (((p + 1) * (q + 1) / (p * q) : ℚ) : ℝ) * √((p : ℝ) * q) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hsp : √(p : ℝ) ^ 2 = p := Real.sq_sqrt hp0.le
  have hsq : √(q : ℝ) ^ 2 = q := Real.sq_sqrt hq0.le
  have hp1 : √(p : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hp0).ne'
  have hq1 : √(q : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hq0).ne'
  rw [Real.sqrt_mul hp0.le]
  push_cast
  field_simp
  rw [hsp, hsq]
  ring

/-- **Arithmetic core.**  For distinct primes `p ≠ q` and a sign `s`, the number
`s (√p + 1/√p)(√q + 1/√q)` is never a sum of two prime-length traces. -/
theorem ne_add_of_isPrimeLengthTrace {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {s : ℚ} (hs : s = 1 ∨ s = -1) {u v : ℝ} (hu : IsPrimeLengthTrace u)
    (hv : IsPrimeLengthTrace v) :
    (s : ℝ) * ((√(p : ℝ) + (√(p : ℝ))⁻¹) * (√(q : ℝ) + (√(q : ℝ))⁻¹)) ≠ u + v := by
  intro h
  set c : ℚ := s * ((p + 1) * (q + 1) / (p * q)) with hcdef
  have hc : c ≠ 0 := by
    have hp0 : (0 : ℚ) < p := by exact_mod_cast hp.pos
    have hq0 : (0 : ℚ) < q := by exact_mod_cast hq.pos
    have hpos : (0 : ℚ) < (p + 1) * (q + 1) / (p * q) := by positivity
    rcases hs with rfl | rfl <;> simp [hcdef, hpos.ne']
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hcm : (c : ℝ) * √((p : ℝ) * q) = u + v := by
    rw [← h, prime_trace_mul_eq hp hq, hcdef]; push_cast; ring
  have hirr : Irrational √((p : ℝ) * q) := irrational_sqrt_mul hp hq hpq
  have hpqr : ∀ {r : ℕ}, r.Prime → Irrational √((p : ℝ) * q * r) := fun hr =>
    irrational_sqrt_mul_mul hp hq hr hpq
  have key : ∀ {r : ℕ}, r.Prime → ∀ {x y w : ℚ},
      (x : ℝ) * √((p : ℝ) * q) + (y : ℝ) * √(r : ℝ) = w → x = 0 := by
    intro r hr x y w hxyw
    exact (eq_zero_of_mul_sqrt_add_mul_sqrt_eq_rat (m := (p : ℚ) * q) (n := (r : ℚ))
      (by positivity) (by positivity) (by push_cast; exact hirr)
      (by push_cast; exact hr.irrational_sqrt) (by push_cast; exact hpqr hr)
      (by push_cast; exact hxyw)).1
  rcases rat_or_rat_mul_sqrt_of_isPrimeLengthTrace hu with ⟨a, rfl⟩ | ⟨r₁, hr₁, a, rfl⟩ <;>
    rcases rat_or_rat_mul_sqrt_of_isPrimeLengthTrace hv with ⟨b, rfl⟩ | ⟨r₂, hr₂, b, rfl⟩
  · -- both rational
    apply hirr.ne_rat ((a + b) / c)
    push_cast
    rw [eq_div_iff hc']
    linear_combination hcm
  · -- `u` rational, `v = b√r₂`
    exact hc (key hr₂ (y := -b) (w := a) (by push_cast; linear_combination hcm))
  · -- `u = a√r₁`, `v` rational
    exact hc (key hr₁ (y := -a) (w := b) (by push_cast; linear_combination hcm))
  · -- `u = a√r₁`, `v = b√r₂`: square once to remove `√r₂`
    have hn1 : (0 : ℝ) ≤ (p : ℝ) * q := by positivity
    have hs1 : √((p : ℝ) * q) ^ 2 = (p : ℝ) * q := Real.sq_sqrt hn1
    have hs2 : √(r₁ : ℝ) ^ 2 = r₁ := Real.sq_sqrt (Nat.cast_nonneg _)
    have hs3 : √(r₂ : ℝ) ^ 2 = r₂ := Real.sq_sqrt (Nat.cast_nonneg _)
    have hprod : √((p : ℝ) * q * r₁) = √((p : ℝ) * q) * √(r₁ : ℝ) := Real.sqrt_mul hn1 _
    have hsq : ((c : ℝ) * √((p : ℝ) * q) - a * √(r₁ : ℝ)) ^ 2 = ((b : ℝ) * √(r₂ : ℝ)) ^ 2 := by
      have : (c : ℝ) * √((p : ℝ) * q) - a * √(r₁ : ℝ) = b * √(r₂ : ℝ) := by
        linear_combination hcm
      rw [this]
    have hlin : (2 * (c : ℝ) * a) * √((p : ℝ) * q * r₁) =
        (c : ℝ) ^ 2 * ((p : ℝ) * q) + (a : ℝ) ^ 2 * r₁ - (b : ℝ) ^ 2 * r₂ := by
      rw [sub_sq, mul_pow, mul_pow, mul_pow, hs1, hs2, hs3] at hsq
      rw [hprod]
      linear_combination -hsq
    have ha : a = 0 := by
      by_contra ha
      have hca : (2 * (c : ℝ) * a) ≠ 0 := by
        have : (2 * c * a : ℚ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero hc) ha
        exact_mod_cast this
      apply (hpqr hr₁).ne_rat
        ((c ^ 2 * ((p : ℚ) * q) + a ^ 2 * r₁ - b ^ 2 * r₂) / (2 * c * a))
      push_cast
      rw [eq_div_iff hca]
      linear_combination hlin
    subst ha
    exact hc (key hr₂ (y := -b) (w := 0) (by push_cast; linear_combination hcm))

/-! ### The obstruction in `SL₂(ℝ)` -/

/-- **No two prime lengths.**  If `A, B ∈ SL₂(ℝ)` have traces `±(√p + 1/√p)` and `±(√q + 1/√q)` for
distinct primes `p ≠ q`, then `AB` and `AB⁻¹` cannot both have prime-length traces. -/
theorem not_isPrimeLengthTrace_mul_and_mul_inv (A B : SpecialLinearGroup (Fin 2) ℝ) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hA : trace (A : Matrix (Fin 2) (Fin 2) ℝ) = √(p : ℝ) + (√(p : ℝ))⁻¹ ∨
      trace (A : Matrix (Fin 2) (Fin 2) ℝ) = -(√(p : ℝ) + (√(p : ℝ))⁻¹))
    (hB : trace (B : Matrix (Fin 2) (Fin 2) ℝ) = √(q : ℝ) + (√(q : ℝ))⁻¹ ∨
      trace (B : Matrix (Fin 2) (Fin 2) ℝ) = -(√(q : ℝ) + (√(q : ℝ))⁻¹))
    (h₁ : IsPrimeLengthTrace (trace ((A * B : SpecialLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ)))
    (h₂ : IsPrimeLengthTrace (trace ((A * B⁻¹ : SpecialLinearGroup (Fin 2) ℝ) :
      Matrix (Fin 2) (Fin 2) ℝ))) : False := by
  have hfricke := trace_mul_add_trace_mul_adjugate (A : Matrix (Fin 2) (Fin 2) ℝ) B
  rw [SpecialLinearGroup.coe_mul] at h₁
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_inv] at h₂
  obtain ⟨s, hs, hst⟩ : ∃ s : ℚ, (s = 1 ∨ s = -1) ∧
      trace (A : Matrix (Fin 2) (Fin 2) ℝ) * trace (B : Matrix (Fin 2) (Fin 2) ℝ) =
        (s : ℝ) * ((√(p : ℝ) + (√(p : ℝ))⁻¹) * (√(q : ℝ) + (√(q : ℝ))⁻¹)) := by
    rcases hA with hA | hA <;> rcases hB with hB | hB
    · exact ⟨1, Or.inl rfl, by rw [hA, hB]; push_cast; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [hA, hB]; push_cast; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [hA, hB]; push_cast; ring⟩
    · exact ⟨1, Or.inl rfl, by rw [hA, hB]; push_cast; ring⟩
  exact ne_add_of_isPrimeLengthTrace hp hq hpq hs h₁ h₂ (by rw [← hst, ← hfricke])

/-- **The primes are not a hyperbolic length spectrum.**  A subgroup of `SL₂(ℝ)` all of whose traces
are prime-length traces contains no two elements with traces `±(√p + 1/√p)`, `±(√q + 1/√q)` for distinct
primes `p ≠ q`. -/
theorem false_of_mem_of_primeLengthTraces (G : Subgroup (SpecialLinearGroup (Fin 2) ℝ))
    (hG : ∀ g ∈ G, IsPrimeLengthTrace (trace (g : Matrix (Fin 2) (Fin 2) ℝ)))
    {A B : SpecialLinearGroup (Fin 2) ℝ} (hAG : A ∈ G) (hBG : B ∈ G) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hA : trace (A : Matrix (Fin 2) (Fin 2) ℝ) = √(p : ℝ) + (√(p : ℝ))⁻¹ ∨
      trace (A : Matrix (Fin 2) (Fin 2) ℝ) = -(√(p : ℝ) + (√(p : ℝ))⁻¹))
    (hB : trace (B : Matrix (Fin 2) (Fin 2) ℝ) = √(q : ℝ) + (√(q : ℝ))⁻¹ ∨
      trace (B : Matrix (Fin 2) (Fin 2) ℝ) = -(√(q : ℝ) + (√(q : ℝ))⁻¹)) : False :=
  not_isPrimeLengthTrace_mul_and_mul_inv A B hp hq hpq hA hB
    (hG _ (G.mul_mem hAG hBG)) (hG _ (G.mul_mem hAG (G.inv_mem hBG)))

end RHTower.HyperbolicPrimeLengthSpectrum
