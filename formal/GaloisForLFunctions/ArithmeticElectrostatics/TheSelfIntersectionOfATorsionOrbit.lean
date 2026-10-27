import GaloisForLFunctions.ArithmeticEffectivityTheory.TheWeilPrimeKernelIsARenormalizedTorsionEnergy

/-!
# The self-intersection of a torsion orbit

On the characteristic circle the torsion orbit `O_n` (the primitive `n`-th roots of unity) is a
cycle of `φ(n)` unit charges. Its interaction with another orbit is the archimedean intersection
`I(m, n) = Σ log |ζ − η|`, and the Hecke law `I(m, mt) = φ(m)Λ(t)` makes the prime side of the
explicit formula an intersection theory (`ArithmeticEffectivityTheory`). The **self-intersection**
`I(n, n) = log |disc Φ_n|` is the renormalized diagonal: the self-energy of each point is removed.
This file computes it and finds an adjunction law.

* **The self-intersection** (`orbitIntersection_self_eq`): `I(n, n) = φ(n) log n − (φ ⋆ Λ)(n)`. The
  degree term `φ(n) log n` is corrected by the **local correction** `(φ ⋆ Λ)(n)`
  (`localCorrection`), which at a prime power is `p^{a−1} log p`
  (`localCorrection_prime_pow`): per point, `I(p^a, p^a)/φ(p^a) = a log p − log p/(p − 1)`.
* **Additivity** (`localCorrection_mul_of_coprime`, `orbitIntersection_self_mul_of_coprime`): the
  local correction obeys the Leibniz rule `D(ab) = φ(a)D(b) + φ(b)D(a)` on coprime orders, so the
  self-intersection per point `ℓ_n = I(n, n)/φ(n)` is additive: `ℓ_{ab} = ℓ_a + ℓ_b`, the orbit of a
  coprime product being the product of the orbits.
* **Adjunction along the tower of `p`** (`orbitIntersection_self_prime_pow_succ`): for `a ≥ 1`,
  `I(p^{a+1}, p^{a+1}) = p · I(p^a, p^a) + φ(p^a) · p log p`: the orbit `O_{p^{a+1}}` is the `p`-fold
  cover of `O_{p^a}` under `z ↦ z^p`, its self-energy is `p` times that of the base plus `p log p`
  per base point for the fibres. Per point the self-intersection grows by exactly the degree `log p`.
* **Conjugation is algebraic on the circle** (`conj_mem_primitiveRoots`, `sum_sum_conj_eq`,
  `torsionEnergy_eq_bilinear`): complex conjugation maps every torsion orbit onto itself (it is the
  power map of degree `−1`), so the Hermitian Abel energy `Σ −log |1 − r ζ η̄|` equals the bilinear
  one `Σ −log |1 − r ζ η|`. On torsion cycles the collided and the reflection pairing coincide; the
  positivity of the Abel energies (`r < 1`) and the Hecke law (`r = 1`) are properties of one form,
  separated only by the self-energy of the diagonal.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius ArithmeticFunction.vonMangoldt ComplexConjugate

namespace GaloisForLFunctions.ArithmeticElectrostatics

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory

/-! ### The totient and the local correction -/

/-- Euler's totient as a real arithmetic function. -/
def totientR : ArithmeticFunction ℝ := ⟨fun n => (Nat.totient n : ℝ), by simp⟩

@[simp] theorem totientR_apply (n : ℕ) : totientR n = Nat.totient n := rfl

theorem isMultiplicative_totientR : IsMultiplicative totientR := by
  refine ⟨by simp, fun {m n} hmn => ?_⟩
  simp only [totientR_apply, Nat.totient_mul hmn, Nat.cast_mul]

/-- The **local correction** `D = φ ⋆ Λ`, `D(n) = Σ_{d ∣ n} φ(d) Λ(n/d)`. -/
def localCorrection : ArithmeticFunction ℝ := totientR * vonMangoldt

theorem localCorrection_nonneg (n : ℕ) : 0 ≤ localCorrection n := by
  rw [localCorrection, mul_apply]
  exact sum_nonneg fun x _ => mul_nonneg (Nat.cast_nonneg _) vonMangoldt_nonneg

/-- `Σ_{d ∣ k} (φ(d) log d + D(d)) = k log k`. -/
theorem sum_divisors_totient_log_add_localCorrection {k : ℕ} (hk : 0 < k) :
    ∑ i ∈ k.divisors, ((Nat.totient i : ℝ) * Real.log i + localCorrection i) =
      (k : ℝ) * Real.log k := by
  have hD : ∑ i ∈ k.divisors, localCorrection i = (totientR * ArithmeticFunction.log) k := by
    rw [← coe_mul_zeta_apply, localCorrection, mul_assoc, vonMangoldt_mul_zeta]
  rw [sum_add_distrib, hD, mul_apply,
    ← Nat.sum_divisorsAntidiagonal (fun a _ => (Nat.totient a : ℝ) * Real.log a), ← sum_add_distrib]
  have hpt : ∀ x ∈ k.divisorsAntidiagonal,
      (Nat.totient x.1 : ℝ) * Real.log x.1 + totientR x.1 * ArithmeticFunction.log x.2 =
        (Nat.totient x.1 : ℝ) * Real.log k := by
    intro x hx
    obtain ⟨hmul, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have h1 : (x.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_right (hmul ▸ hk)).ne' |>.symm.symm
    have h2 : (x.2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_left (hmul ▸ hk)).ne'
    rw [totientR_apply, log_apply, ← mul_add, ← Real.log_mul h1 h2, ← Nat.cast_mul, hmul]
  rw [sum_congr rfl hpt, ← sum_mul,
    Nat.sum_divisorsAntidiagonal (fun a _ => (Nat.totient a : ℝ)), ← Nat.cast_sum, Nat.sum_totient]

/-- **`kLogKernel n = φ(n) log n + D(n)`.** -/
theorem kLogKernel_eq {n : ℕ} (hn : 0 < n) :
    kLogKernel n = (Nat.totient n : ℝ) * Real.log n + localCorrection n := by
  have h := (sum_eq_iff_sum_mul_moebius_eq
    (f := fun i => (Nat.totient i : ℝ) * Real.log i + localCorrection i)
    (g := fun k => (k : ℝ) * Real.log k)).mp
    (fun k hk => sum_divisors_totient_log_add_localCorrection hk) n hn
  rw [← h, kLogKernel, ← Nat.sum_divisorsAntidiagonal' (fun a b =>
    (μ a : ℝ) * ((b : ℝ) * Real.log b))]

/-- **The self-intersection of a torsion orbit**: `I(n, n) = φ(n) log n − (φ ⋆ Λ)(n)`. -/
theorem orbitIntersection_self_eq {n : ℕ} (hn : 0 < n) :
    orbitIntersection n n = (Nat.totient n : ℝ) * Real.log n - localCorrection n := by
  rw [orbitIntersection_self hn, kLogKernel_eq hn]
  ring

/-- The self-intersection never exceeds the degree term. -/
theorem orbitIntersection_self_le {n : ℕ} (hn : 0 < n) :
    orbitIntersection n n ≤ (Nat.totient n : ℝ) * Real.log n := by
  rw [orbitIntersection_self_eq hn]
  linarith [localCorrection_nonneg n]

/-! ### Prime powers and the tower of `p` -/

/-- `Σ_{j < a} φ(p^j) = p^{a−1}`. -/
theorem sum_range_totient_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    ∑ j ∈ range (a + 1), (Nat.totient (p ^ j) : ℝ) = (p : ℝ) ^ a := by
  have h := Nat.sum_totient (p ^ a)
  rw [Nat.sum_divisors_prime_pow hp] at h
  exact_mod_cast h

/-- **The local correction at a prime power**: `D(p^a) = p^{a−1} log p`. -/
theorem localCorrection_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    localCorrection (p ^ (a + 1)) = (p : ℝ) ^ a * Real.log p := by
  rw [localCorrection, mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => totientR x * vonMangoldt y),
    Nat.sum_divisors_prime_pow hp, Finset.sum_range_succ, Nat.div_self (pow_pos hp.pos _),
    vonMangoldt_apply_one, mul_zero, add_zero, ← sum_range_totient_prime_pow hp a, sum_mul]
  refine sum_congr rfl fun j hj => ?_
  have hja : j < a + 1 := mem_range.mp hj
  rw [totientR_apply, Nat.pow_div hja.le hp.pos,
    vonMangoldt_apply_pow (by omega), vonMangoldt_apply_prime hp]

/-- The self-intersection of a prime-power orbit: `I(p^a, p^a) = φ(p^a) a log p − p^{a−1} log p`. -/
theorem orbitIntersection_self_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    orbitIntersection (p ^ (a + 1)) (p ^ (a + 1)) =
      (Nat.totient (p ^ (a + 1)) : ℝ) * ((a + 1) * Real.log p) - (p : ℝ) ^ a * Real.log p := by
  rw [orbitIntersection_self_eq (pow_pos hp.pos _), localCorrection_prime_pow hp, Nat.cast_pow,
    Real.log_pow]
  push_cast
  ring

/-- **Adjunction along the tower of `p`**: the `p`-fold cover `O_{p^{a+1}} → O_{p^a}`, `z ↦ z^p`,
has self-intersection `p` times the base plus `p log p` per base point. -/
theorem orbitIntersection_self_prime_pow_succ {p : ℕ} (hp : p.Prime) (a : ℕ) :
    orbitIntersection (p ^ (a + 2)) (p ^ (a + 2)) =
      p * orbitIntersection (p ^ (a + 1)) (p ^ (a + 1)) +
        (Nat.totient (p ^ (a + 1)) : ℝ) * (p * Real.log p) := by
  rw [orbitIntersection_self_prime_pow hp (a + 1), orbitIntersection_self_prime_pow hp a,
    Nat.totient_prime_pow_succ hp, Nat.totient_prime_pow_succ hp]
  push_cast
  ring

/-- Per point the self-intersection grows by exactly the degree `log p` along the tower. -/
theorem selfIntersection_per_point_prime_pow_succ {p : ℕ} (hp : p.Prime) (a : ℕ) :
    orbitIntersection (p ^ (a + 2)) (p ^ (a + 2)) / Nat.totient (p ^ (a + 2)) =
      orbitIntersection (p ^ (a + 1)) (p ^ (a + 1)) / Nat.totient (p ^ (a + 1)) + Real.log p := by
  have hφ : (Nat.totient (p ^ (a + 1)) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (pow_pos hp.pos _)).ne'
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hφ2 : (Nat.totient (p ^ (a + 2)) : ℝ) = p * Nat.totient (p ^ (a + 1)) := by
    rw [show a + 2 = (a + 1) + 1 by ring, Nat.totient_prime_pow_succ hp,
      Nat.totient_prime_pow_succ hp]
    push_cast; ring
  rw [orbitIntersection_self_prime_pow_succ hp a, hφ2]
  field_simp

/-! ### Additivity over coprime orders -/

/-- Divisor sums over a coprime product factor. -/
theorem sum_divisors_mul_of_coprime {M : Type*} [AddCommMonoid M] {a b : ℕ} (hab : a.Coprime b)
    (F : ℕ → M) :
    ∑ d ∈ (a * b).divisors, F d = ∑ d₁ ∈ a.divisors, ∑ d₂ ∈ b.divisors, F (d₁ * d₂) := by
  rw [Nat.divisors_mul, Finset.mul_def, sum_image hab.mul_injOn_divisors, sum_product]

/-- `D = (φ ⋆ μ) ⋆ log`. -/
theorem localCorrection_eq_mul_log :
    localCorrection = (totientR * (μ : ArithmeticFunction ℝ)) * ArithmeticFunction.log := by
  rw [localCorrection, ← log_mul_moebius_eq_vonMangoldt, mul_assoc,
    mul_comm ArithmeticFunction.log]

/-- **The Leibniz rule**: on coprime orders `D(ab) = φ(a) D(b) + φ(b) D(a)`. -/
theorem localCorrection_mul_of_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) :
    localCorrection (a * b) =
      (Nat.totient a : ℝ) * localCorrection b + (Nat.totient b : ℝ) * localCorrection a := by
  set g : ArithmeticFunction ℝ := totientR * (μ : ArithmeticFunction ℝ)
  have hg : IsMultiplicative g := isMultiplicative_totientR.mul isMultiplicative_moebius.intCast
  -- `Σ_{d ∣ n} g(d) = φ(n)`
  have hgz : ∀ n, ∑ d ∈ n.divisors, g d = Nat.totient n := by
    intro n
    rw [← coe_mul_zeta_apply, mul_assoc, coe_moebius_mul_coe_zeta, mul_one, totientR_apply]
  -- `D(n) = Σ_{d ∣ n} g(d) log(n/d)`
  have hD : ∀ n, localCorrection n = ∑ d ∈ n.divisors, g d * Real.log ((n / d : ℕ) : ℝ) := by
    intro n
    rw [localCorrection_eq_mul_log, mul_apply,
      Nat.sum_divisorsAntidiagonal (fun x y => g x * ArithmeticFunction.log y)]
    simp only [log_apply]
  rw [hD, hD, hD, sum_divisors_mul_of_coprime hab]
  have hpt : ∀ d₁ ∈ a.divisors, ∀ d₂ ∈ b.divisors,
      g (d₁ * d₂) * Real.log (((a * b) / (d₁ * d₂) : ℕ) : ℝ) =
        g d₂ * (g d₁ * Real.log ((a / d₁ : ℕ) : ℝ)) +
          g d₁ * (g d₂ * Real.log ((b / d₂ : ℕ) : ℝ)) := by
    intro d₁ hd₁ d₂ hd₂
    have h1 := Nat.dvd_of_mem_divisors hd₁
    have h2 := Nat.dvd_of_mem_divisors hd₂
    have hcop : Nat.Coprime d₁ d₂ := (hab.coprime_dvd_left h1).coprime_dvd_right h2
    have hq1 : 0 < a / d₁ := Nat.div_pos (Nat.le_of_dvd ha h1) (Nat.pos_of_mem_divisors hd₁)
    have hq2 : 0 < b / d₂ := Nat.div_pos (Nat.le_of_dvd hb h2) (Nat.pos_of_mem_divisors hd₂)
    rw [hg.map_mul_of_coprime hcop, ← Nat.div_mul_div_comm h1 h2, Nat.cast_mul,
      Real.log_mul (by exact_mod_cast hq1.ne') (by exact_mod_cast hq2.ne')]
    ring
  rw [sum_congr rfl fun d₁ hd₁ => sum_congr rfl (hpt d₁ hd₁)]
  simp only [sum_add_distrib, ← mul_sum, ← sum_mul]
  rw [hgz, hgz]
  ring_nf

/-- **Additivity of the self-intersection**: on coprime orders
`I(ab, ab) = φ(b) I(a, a) + φ(a) I(b, b)`, i.e. `ℓ_{ab} = ℓ_a + ℓ_b` per point. -/
theorem orbitIntersection_self_mul_of_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) :
    orbitIntersection (a * b) (a * b) =
      (Nat.totient b : ℝ) * orbitIntersection a a + (Nat.totient a : ℝ) * orbitIntersection b b := by
  rw [orbitIntersection_self_eq (Nat.mul_pos ha hb), orbitIntersection_self_eq ha,
    orbitIntersection_self_eq hb, localCorrection_mul_of_coprime ha hb hab, Nat.totient_mul hab,
    Nat.cast_mul, Nat.cast_mul,
    Real.log_mul (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne')]
  ring

/-! ### Conjugation on torsion cycles -/

/-- Conjugation maps a torsion orbit onto itself. -/
theorem conj_mem_primitiveRoots {n : ℕ} {η : ℂ} (h : η ∈ primitiveRoots n ℂ) :
    conj η ∈ primitiveRoots n ℂ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at h
  · rw [mem_primitiveRoots hn] at h ⊢
    exact h.map_of_injective (starRingEnd ℂ).injective

/-- Summing over a torsion orbit is invariant under conjugation. -/
theorem sum_primitiveRoots_conj {M : Type*} [AddCommMonoid M] (n : ℕ) (F : ℂ → M) :
    ∑ η ∈ primitiveRoots n ℂ, F (conj η) = ∑ η ∈ primitiveRoots n ℂ, F η :=
  sum_nbij' (starRingEnd ℂ) (starRingEnd ℂ) (fun _ h => conj_mem_primitiveRoots h)
    (fun _ h => conj_mem_primitiveRoots h) (fun _ _ => Complex.conj_conj _)
    (fun _ _ => Complex.conj_conj _)
    (fun _ _ => rfl)

/-- **The collided and reflection pairings agree on torsion cycles.** -/
theorem sum_sum_conj_eq {M : Type*} [AddCommMonoid M] (m n : ℕ) (F : ℂ → M) :
    ∑ ζ ∈ primitiveRoots m ℂ, ∑ η ∈ primitiveRoots n ℂ, F (ζ * conj η) =
      ∑ ζ ∈ primitiveRoots m ℂ, ∑ η ∈ primitiveRoots n ℂ, F (ζ * η) :=
  sum_congr rfl fun ζ _ => sum_primitiveRoots_conj n fun η => F (ζ * η)

/-- The Hermitian Abel energy of two orbits is their bilinear Abel energy. -/
theorem torsionEnergy_eq_bilinear (r : ℝ) (m n : ℕ) :
    torsionEnergy r m n =
      ∑ ζ ∈ primitiveRoots m ℂ, ∑ η ∈ primitiveRoots n ℂ, -Real.log ‖1 - (r : ℂ) * (ζ * η)‖ :=
  sum_sum_conj_eq m n fun w => -Real.log ‖1 - (r : ℂ) * w‖

/-- On a torsion orbit conjugation is the power map of degree `−1`: `η̄ = η^{n−1}`. -/
theorem conj_eq_pow_of_mem_primitiveRoots {n : ℕ} {η : ℂ} (h : η ∈ primitiveRoots n ℂ) :
    conj η = η ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp at h
  have hη := (mem_primitiveRoots hn).mp h
  have hnorm : ‖η‖ = 1 := norm_of_mem_primitiveRoots h
  have hne : η ≠ 0 := by intro h0; rw [h0, norm_zero] at hnorm; exact zero_ne_one hnorm
  have hinv : conj η = η⁻¹ := (Complex.inv_eq_conj hnorm).symm
  rw [hinv, eq_comm, ← mul_eq_one_iff_eq_inv₀ hne, ← pow_succ, Nat.sub_add_cancel hn,
    hη.pow_eq_one]

end GaloisForLFunctions.ArithmeticElectrostatics
