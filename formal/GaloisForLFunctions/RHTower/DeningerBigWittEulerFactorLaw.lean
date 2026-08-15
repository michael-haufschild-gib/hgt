import GaloisForLFunctions.RHTower.DeningerBigWittRing

/-!
# Exact Euler-factor law for canonical big-Witt multiplication

The completed gcd--lcm construction already defines multiplication over every
commutative ring.  This module exposes its defining single-factor identity as
an unconditional theorem:

`(1-aT^m) ⊙ (1-bT^n)
  = gcd(m,n) ·_W (1-a^(l/m)b^(l/n)T^l)`,

where `l = lcm(m,n)` and `·_W` denotes repeated Witt addition, hence ordinary
power-series multiplication.  The proof first uses ghost injectivity over a
free integer polynomial ring and then evaluates into the arbitrary target.
No reducedness, torsion-freeness, field, or target ghost-injectivity hypothesis
is present; nilpotent coefficients are retained.
-/

namespace RHTower

noncomputable section

open PowerSeries

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Literal positive-degree Euler factor as a big-Witt additive carrier. -/
def deningerBigWittEulerFactorCarrier (a : A) (m : ℕ) (hm : 0 < m) :
    DeningerBigWittAdditive A :=
  deningerBigWittOfSeries (deningerBigWittFactor a m)
    (deningerBigWittFactor_constantCoeff a m hm.ne')

@[simp] theorem deningerBigWittSeries_eulerFactorCarrier
    (a : A) (m : ℕ) (hm : 0 < m) :
    deningerBigWittSeries (deningerBigWittEulerFactorCarrier a m hm) =
      deningerBigWittFactor a m := by
  rfl

@[simp] theorem deningerBigWittEulerFactorCarrier_natural
    (f : A →+* B) (a : A) (m : ℕ) (hm : 0 < m) :
    deningerBigWittMap f (deningerBigWittEulerFactorCarrier a m hm) =
      deningerBigWittEulerFactorCarrier (f a) m hm := by
  apply Subtype.ext
  apply Units.ext
  change PowerSeries.map f (deningerBigWittFactor a m) =
    deningerBigWittFactor (f a) m
  exact deningerBigWittFactor_map f a m

/-- Ghost coordinate of one positive-degree Euler factor. -/
theorem deningerBigWittGhostCoeff_eulerFactorCarrier
    (a : A) {m k : ℕ} (hm : 0 < m) (hk : 0 < k) :
    deningerBigWittGhostCoeff (deningerBigWittEulerFactorCarrier a m hm) k =
      if m ∣ k then (m : A) * a ^ (k / m) else 0 := by
  exact deningerBigWittLogGhost_factor_coeff a hm hk

/-- Ordinary carrier powers are repeated Witt sums, so ghosts scale by the
power.  This identity itself is integral and valid over every target ring. -/
theorem deningerBigWittGhostCoeff_pow
    (u : DeningerBigWittAdditive A) (d k : ℕ) :
    deningerBigWittGhostCoeff (u ^ d) k =
      d • deningerBigWittGhostCoeff u k := by
  induction d with
  | zero => simp [deningerBigWittGhostCoeff]
  | succ d ih =>
      rw [pow_succ, deningerBigWittGhostCoeff_add, ih, succ_nsmul]

/-- Gcd--lcm factor law over a torsion-free coefficient ring.  This is only
the universal proof stage; the public theorem below removes this hypothesis. -/
theorem deningerBigWittMul_eulerFactorCarrier_of_torsionFree
    [IsAddTorsionFree A] (a b : A) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    deningerBigWittMul
        (deningerBigWittEulerFactorCarrier a m hm)
        (deningerBigWittEulerFactorCarrier b n hn) =
      (deningerBigWittEulerFactorCarrier
        (a ^ (m.lcm n / m) * b ^ (m.lcm n / n))
        (m.lcm n) (Nat.lcm_pos hm hn)) ^ (m.gcd n) := by
  apply deningerBigWittGhostSeries_injective
  apply PowerSeries.ext
  intro k
  cases k with
  | zero => simp [deningerBigWittGhostSeries]
  | succ k =>
      have hk : 0 < k + 1 := Nat.succ_pos k
      change deningerBigWittGhostCoeff
          (deningerBigWittMul
            (deningerBigWittEulerFactorCarrier a m hm)
            (deningerBigWittEulerFactorCarrier b n hn)) (k + 1) =
        deningerBigWittGhostCoeff
          ((deningerBigWittEulerFactorCarrier
            (a ^ (m.lcm n / m) * b ^ (m.lcm n / n))
            (m.lcm n) (Nat.lcm_pos hm hn)) ^ (m.gcd n)) (k + 1)
      rw [deningerBigWittGhostCoeff_mul _ _ hk,
        deningerBigWittGhostCoeff_eulerFactorCarrier a hm hk,
        deningerBigWittGhostCoeff_eulerFactorCarrier b hn hk,
        deningerBigWittGhostCoeff_pow,
        deningerBigWittGhostCoeff_eulerFactorCarrier _ (Nat.lcm_pos hm hn) hk]
      simpa only [smul_ite, smul_zero] using
        (deningerBigWittPairGhostTerm_eq_mul a b hm hn (k := k + 1)).symm

/-- Exact gcd--lcm Euler-factor product over every commutative ring, including
rings with additive torsion, zero divisors, and nonzero nilpotents. -/
theorem deningerBigWittMul_eulerFactorCarrier
    (a b : A) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    deningerBigWittMul
        (deningerBigWittEulerFactorCarrier a m hm)
        (deningerBigWittEulerFactorCarrier b n hn) =
      (deningerBigWittEulerFactorCarrier
        (a ^ (m.lcm n / m) * b ^ (m.lcm n / n))
        (m.lcm n) (Nat.lcm_pos hm hn)) ^ (m.gcd n) := by
  let ev : MvPolynomial (Fin 2) ℤ →+* A :=
    MvPolynomial.eval₂Hom (Int.castRingHom A) ![a, b]
  have h := deningerBigWittMul_eulerFactorCarrier_of_torsionFree
    (A := MvPolynomial (Fin 2) ℤ)
    (MvPolynomial.X (0 : Fin 2)) (MvPolynomial.X (1 : Fin 2))
    m n hm hn
  have he := congrArg (deningerBigWittMap ev) h
  rw [deningerBigWittMul_natural] at he
  simp only [deningerBigWittEulerFactorCarrier_natural, map_pow] at he
  have hzero : ev (MvPolynomial.X (0 : Fin 2)) = a := by
    simp [ev]
  have hone : ev (MvPolynomial.X (1 : Fin 2)) = b := by
    simp [ev]
  simpa only [map_mul, map_pow, hzero, hone] using he

/-- Positive-degree Euler factor as an element of the canonical big-Witt ring. -/
def deningerBigWittRingEulerFactor (a : A) (m : ℕ) (hm : 0 < m) :
    DeningerBigWittRing A :=
  ⟨Additive.ofMul (deningerBigWittEulerFactorCarrier a m hm)⟩

/-- Repeated Witt addition of a wrapped carrier is ordinary carrier power. -/
theorem deningerBigWittRing_nsmul_mk_ofMul
    (u : DeningerBigWittAdditive A) (d : ℕ) :
    d • (⟨Additive.ofMul u⟩ : DeningerBigWittRing A) =
      ⟨Additive.ofMul (u ^ d)⟩ := by
  induction d with
  | zero =>
      apply DeningerBigWittRing.ext
      rfl
  | succ d ih =>
      rw [succ_nsmul, ih, pow_succ]
      apply DeningerBigWittRing.ext
      rfl

/-- Constructor-level canonical Euler-factor multiplication law. -/
theorem deningerBigWittRingEulerFactor_mul
    (a b : A) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    deningerBigWittRingEulerFactor a m hm *
        deningerBigWittRingEulerFactor b n hn =
      ⟨Additive.ofMul
        ((deningerBigWittEulerFactorCarrier
          (a ^ (m.lcm n / m) * b ^ (m.lcm n / n))
          (m.lcm n) (Nat.lcm_pos hm hn)) ^ (m.gcd n))⟩ := by
  apply DeningerBigWittRing.ext
  change Additive.ofMul
      (deningerBigWittMul
        (deningerBigWittEulerFactorCarrier a m hm)
        (deningerBigWittEulerFactorCarrier b n hn)) = _
  rw [deningerBigWittMul_eulerFactorCarrier]

/-- Canonical gcd--lcm law in ring notation: the exponent is Witt addition. -/
theorem deningerBigWittRingEulerFactor_mul_eq_nsmul
    (a b : A) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    deningerBigWittRingEulerFactor a m hm *
        deningerBigWittRingEulerFactor b n hn =
      (m.gcd n) • deningerBigWittRingEulerFactor
        (a ^ (m.lcm n / m) * b ^ (m.lcm n / n))
        (m.lcm n) (Nat.lcm_pos hm hn) := by
  rw [deningerBigWittRingEulerFactor_mul,
    show (m.gcd n) • deningerBigWittRingEulerFactor
        (a ^ (m.lcm n / m) * b ^ (m.lcm n / n))
        (m.lcm n) (Nat.lcm_pos hm hn) =
      ⟨Additive.ofMul
        ((deningerBigWittEulerFactorCarrier
          (a ^ (m.lcm n / m) * b ^ (m.lcm n / n))
          (m.lcm n) (Nat.lcm_pos hm hn)) ^ (m.gcd n))⟩ by
      exact deningerBigWittRing_nsmul_mk_ofMul _ _]

end

end RHTower
