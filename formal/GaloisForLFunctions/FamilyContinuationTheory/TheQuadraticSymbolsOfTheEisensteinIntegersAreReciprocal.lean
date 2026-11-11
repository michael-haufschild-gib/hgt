import GaloisForLFunctions.FamilyContinuationTheory.TheGaussSumOfAPrimePowerLivesOnOneLayer
import GaloisForLFunctions.MetaplecticMobiusDescent.TheQuadraticGaussPhaseLivesModuloFour

/-!
# The quadratic symbols of the Eisenstein integers are reciprocal

For `c ∈ O = ℤ[ω]`, `c ≠ 0`, let `Γ(c) = |c|⁻¹ Σ_{x mod c} ψ_c(x²)` with the trace character
`ψ_c(x) = exp(2πi Tr(x/(cλ)))`; it is `(1 + i^{−b} + i^a + i^{b−a})/2` for `c = a + bω` and depends
only on `c mod 4` (`normalizedQuadraticTraceGauss_formula`). For two odd primes `p, q` of `O` with
quadratic residue characters `η_p, η_q`:

* `sum_traceChar_mul_sq`: `Σ_{x mod p} ψ_p(ux²) = η_p(u) G(η_p)` for `p ∤ u` (square roots are
  counted by `1 + η_p`);
* `quadraticTraceGauss_mul`: for coprime `c, d`, the sum over `x mod cd` splits along
  `x = dx₁ + cx₂` into `Σ_{x₁} ψ_c(dx₁²) · Σ_{x₂} ψ_d(cx₂²)`, because the cross term `2x₁x₂` is
  integral and the trace character is trivial on integers (`traceChar_integral`);
* `quadratic_reciprocity`: `η_p(q) η_q(p) Γ(p) Γ(q) = Γ(pq)`.

So `η_p(q) η_q(p)` is a function of `p, q mod 4`: the quadratic part of sextic reciprocity, which
turns the cross phases of the cubic-theta probe into a fixed ray bicharacter.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent.Eisenstein

/-- The trace character is trivial on integers: `exp(2πi Tr(z/λ)) = 1` for `z ∈ O`. -/
theorem traceChar_integral (z : O) :
    Complex.exp ((Algebra.trace ℚ K
      ((algebraMap O K z) / (algebraMap O K traceLambda * algebraMap O K 1)) : ℂ) *
        (2 * Real.pi * Complex.I)) = 1 := by
  rw [← principalTraceChar_apply 1 one_ne_zero z]
  have h : Ideal.Quotient.mk (Ideal.span {(1 : O)}) z = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_one]
    trivial
  rw [h, AddChar.map_zero_eq_one]

/-- **The CRT phase.** For `x = dx₁ + cx₂`, `ψ_{cd}(x²) = ψ_c(dx₁²) ψ_d(cx₂²)`. -/
theorem traceChar_crt_sq (c d : O) [NeZero c] [NeZero d] (x y : O) :
    principalTraceChar (c * d) (mul_ne_zero (NeZero.ne c) (NeZero.ne d))
        (Ideal.Quotient.mk _ ((d * x + c * y) ^ 2)) =
      principalTraceChar c (NeZero.ne c) (Ideal.Quotient.mk _ (d * x ^ 2)) *
        principalTraceChar d (NeZero.ne d) (Ideal.Quotient.mk _ (c * y ^ 2)) := by
  rw [principalTraceChar_apply, principalTraceChar_apply, principalTraceChar_apply,
    ← Complex.exp_add]
  have hinj := FaithfulSMul.algebraMap_injective O K
  have hc : algebraMap O K c ≠ 0 := fun h => NeZero.ne c (hinj (by rw [h, map_zero]))
  have hd : algebraMap O K d ≠ 0 := fun h => NeZero.ne d (hinj (by rw [h, map_zero]))
  have hl : algebraMap O K traceLambda ≠ 0 := fun h => traceLambda_ne_zero
    (hinj (by rw [h, map_zero]))
  have hsplit : (algebraMap O K ((d * x + c * y) ^ 2)) /
      (algebraMap O K traceLambda * algebraMap O K (c * d)) =
      (algebraMap O K (d * x ^ 2)) / (algebraMap O K traceLambda * algebraMap O K c) +
        (algebraMap O K (c * y ^ 2)) / (algebraMap O K traceLambda * algebraMap O K d) +
          (algebraMap O K (2 * x * y)) / (algebraMap O K traceLambda * algebraMap O K 1) := by
    simp only [map_mul, map_pow, map_add, map_one, map_ofNat]
    field_simp
    ring
  have h1 := traceChar_integral (2 * x * y)
  rw [hsplit, map_add, map_add, Rat.cast_add, Rat.cast_add, add_mul, add_mul, Complex.exp_add, h1,
    mul_one]

/-- A representative of a residue class. -/
def qrep {I : Ideal O} (x : O ⧸ I) : O := Classical.choose (Ideal.Quotient.mk_surjective x)

theorem mk_qrep {I : Ideal O} (x : O ⧸ I) : Ideal.Quotient.mk I (qrep x) = x :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective x)

/-- The CRT parametrization `(x₁, x₂) ↦ dx₁ + cx₂` of `O/(cd)`. -/
def crtParam (c d : O) (p : (O ⧸ Ideal.span {c}) × (O ⧸ Ideal.span {d})) :
    O ⧸ Ideal.span {c * d} :=
  Ideal.Quotient.mk _ (d * qrep p.1 + c * qrep p.2)

theorem crtParam_bijective (c d : O) [NeZero c] [NeZero d] (hcd : IsCoprime c d) :
    Function.Bijective (crtParam c d) := by
  haveI : NeZero (c * d) := ⟨mul_ne_zero (NeZero.ne c) (NeZero.ne d)⟩
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
    simp only [crtParam, Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
    have e : d * qrep x₁ + c * qrep x₂ - (d * qrep y₁ + c * qrep y₂) =
        d * (qrep x₁ - qrep y₁) + c * (qrep x₂ - qrep y₂) := by ring
    rw [e] at h
    have hc : c ∣ d * (qrep x₁ - qrep y₁) :=
      (dvd_add_left (dvd_mul_right c _)).mp ((dvd_mul_right c d).trans h)
    have hd : d ∣ c * (qrep x₂ - qrep y₂) :=
      (dvd_add_right (dvd_mul_right d _)).mp ((dvd_mul_left d c).trans h)
    have h1 : x₁ = y₁ := by
      rw [← mk_qrep x₁, ← mk_qrep y₁, Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact hcd.dvd_of_dvd_mul_left hc
    have h2 : x₂ = y₂ := by
      rw [← mk_qrep x₂, ← mk_qrep y₂, Ideal.Quotient.eq, Ideal.mem_span_singleton]
      exact hcd.symm.dvd_of_dvd_mul_left hd
    rw [h1, h2]
  · have hcard : ∀ (e : O) [NeZero e], Fintype.card (O ⧸ Ideal.span {e}) =
        Ideal.absNorm (Ideal.span {e}) := fun e _ => by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    rw [Fintype.card_prod, hcard, hcard, hcard, ← Ideal.span_singleton_mul_span_singleton,
      map_mul]

/-- The quadratic trace sum, written with the instance of this file. -/
theorem quadraticTraceGauss_eq_sum (c : O) [NeZero c] :
    quadraticTraceGauss c (NeZero.ne c) =
      ∑ x : O ⧸ Ideal.span {c}, principalTraceChar c (NeZero.ne c) (x ^ 2) := rfl

/-- **The CRT splitting.** For coprime `c, d`,
`Σ_{x mod cd} ψ_{cd}(x²) = Σ_{x₁ mod c} ψ_c(dx₁²) · Σ_{x₂ mod d} ψ_d(cx₂²)`. -/
theorem quadraticTraceGauss_mul (c d : O) [NeZero c] [NeZero d] (hcd : IsCoprime c d) :
    quadraticTraceGauss (c * d) (mul_ne_zero (NeZero.ne c) (NeZero.ne d)) =
      (∑ x : O ⧸ Ideal.span {c}, principalTraceChar c (NeZero.ne c)
          (Ideal.Quotient.mk _ d * x ^ 2)) *
        ∑ y : O ⧸ Ideal.span {d}, principalTraceChar d (NeZero.ne d)
          (Ideal.Quotient.mk _ c * y ^ 2) := by
  haveI : NeZero (c * d) := ⟨mul_ne_zero (NeZero.ne c) (NeZero.ne d)⟩
  rw [quadraticTraceGauss_eq_sum, ← (Fintype.sum_bijective _ (crtParam_bijective c d hcd)
    (fun p => principalTraceChar (c * d) _ (crtParam c d p ^ 2)) _ fun _ => rfl),
    Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hx : Ideal.Quotient.mk (Ideal.span {c}) (d * qrep x ^ 2) =
      Ideal.Quotient.mk _ d * x ^ 2 := by rw [map_mul, map_pow, mk_qrep]
  have hy : Ideal.Quotient.mk (Ideal.span {d}) (c * qrep y ^ 2) =
      Ideal.Quotient.mk _ c * y ^ 2 := by rw [map_mul, map_pow, mk_qrep]
  show principalTraceChar (c * d) _ (Ideal.Quotient.mk _ (d * qrep x + c * qrep y) ^ 2) = _
  rw [← map_pow, traceChar_crt_sq, hx, hy]

/-! ### Odd primes -/

section Prime

variable (p : O) [NeZero p] [hP : (Ideal.span {p}).IsMaximal]

omit [NeZero p] hP in
/-- At an odd prime the residue ring has characteristic different from two. -/
theorem ringChar_ne_two (h2 : (2 : O) ∉ Ideal.span {p}) : ringChar (O ⧸ Ideal.span {p}) ≠ 2 := by
  intro h
  apply h2
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
  have := ringChar.spec (O ⧸ Ideal.span {p}) 2
  exact_mod_cast this.mpr (by rw [h])

/-- **Squares are counted by `1 + η`.** `Σ_{x mod p} ψ_p(ux²) = η_p(u) G(η_p)` for `p ∤ u`. -/
theorem sum_traceChar_mul_sq (h2 : (2 : O) ∉ Ideal.span {p}) {u : O ⧸ Ideal.span {p}}
    (hu : u ≠ 0) :
    ∑ x : O ⧸ Ideal.span {p}, principalTraceChar p (NeZero.ne p) (u * x ^ 2) =
      complexQuadraticChar (Ideal.span {p}) u *
        gaussSum (complexQuadraticChar (Ideal.span {p})) (principalTraceChar p (NeZero.ne p)) := by
  letI : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  set ψ := principalTraceChar p (NeZero.ne p)
  set η := complexQuadraticChar (Ideal.span {p})
  have hchar := ringChar_ne_two p h2
  -- group the `x` by their square
  have hfib : ∑ x : O ⧸ Ideal.span {p}, ψ (u * x ^ 2) =
      ∑ y : O ⧸ Ideal.span {p}, ((Finset.univ.filter fun x => x ^ 2 = y).card : ℂ) * ψ (u * y) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun x => x ^ 2) (fun x => ψ (u * x ^ 2))]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_congr rfl fun x hx => by rw [(Finset.mem_filter.mp hx).2], Finset.sum_const,
      nsmul_eq_mul]
  have hcount : ∀ y : O ⧸ Ideal.span {p},
      ((Finset.univ.filter fun x => x ^ 2 = y).card : ℂ) = η y + 1 := by
    intro y
    have h := quadraticChar_card_sqrts hchar y
    rw [Set.toFinset_setOf] at h
    simp only [η, complexQuadraticChar, MulChar.ringHomComp_apply, eq_intCast]
    exact_mod_cast h
  rw [hfib]
  simp only [hcount, add_mul, one_mul, Finset.sum_add_distrib]
  have hzero : ∑ y : O ⧸ Ideal.span {p}, ψ (u * y) = 0 := by
    have := AddChar.sum_mulShift u (principalTraceChar_primitive p (NeZero.ne p))
    rw [if_neg hu, Nat.cast_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun y _ => by rw [mul_comm]
  rw [hzero, add_zero]
  -- the Gauss sum at the unit multiplier `u`
  have hunit : IsUnit u := isUnit_iff_ne_zero.mpr hu
  have hg := gaussSum_mulShift η ψ hunit.unit
  rw [IsUnit.unit_spec] at hg
  have hsq : η u * η u = 1 := by
    simp only [η, complexQuadraticChar, MulChar.ringHomComp_apply, eq_intCast]
    rw [← Int.cast_mul, ← sq, quadraticChar_sq_one hu, Int.cast_one]
  calc ∑ y, η y * ψ (u * y) = gaussSum η (AddChar.mulShift ψ u) := rfl
    _ = η u * (η u * gaussSum η (AddChar.mulShift ψ u)) := by
        rw [← mul_assoc, hsq, one_mul]
    _ = η u * gaussSum η ψ := by rw [hg]

end Prime

/-- **Quadratic reciprocity over `ℤ[ω]`.** For coprime odd primes `p, q`,
`η_p(q) η_q(p) Γ(p) Γ(q) = Γ(pq)`, where `Γ(c) = |c|⁻¹ Σ_{x mod c} ψ_c(x²)` depends only on
`c mod 4`. -/
theorem quadratic_reciprocity (p q : O) [NeZero p] [NeZero q] [(Ideal.span {p}).IsMaximal]
    [(Ideal.span {q}).IsMaximal] (hp2 : (2 : O) ∉ Ideal.span {p}) (hq2 : (2 : O) ∉ Ideal.span {q})
    (hpq : IsCoprime p q) :
    complexQuadraticChar (Ideal.span {p}) (Ideal.Quotient.mk _ q) *
        complexQuadraticChar (Ideal.span {q}) (Ideal.Quotient.mk _ p) *
          normalizedQuadraticTraceGauss p (NeZero.ne p) *
            normalizedQuadraticTraceGauss q (NeZero.ne q) =
      normalizedQuadraticTraceGauss (p * q) (mul_ne_zero (NeZero.ne p) (NeZero.ne q)) := by
  -- neither prime divides the other
  have hnd : ∀ (a b : O) [(Ideal.span {a}).IsMaximal], IsCoprime a b →
      Ideal.Quotient.mk (Ideal.span {a}) b ≠ 0 := by
    intro a b ha hab h
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h
    exact ha.ne_top (Ideal.span_singleton_eq_top.mpr (hab.isUnit_of_dvd' (dvd_refl a) h))
  have hqp := hnd p q hpq
  have hpq' := hnd q p hpq.symm
  -- the three quadratic trace sums
  have hone : ∀ (a : O) [NeZero a] [(Ideal.span {a}).IsMaximal], (2 : O) ∉ Ideal.span {a} →
      quadraticTraceGauss a (NeZero.ne a) =
        gaussSum (complexQuadraticChar (Ideal.span {a})) (principalTraceChar a (NeZero.ne a)) := by
    intro a _ _ ha2
    have h := sum_traceChar_mul_sq a ha2 (u := 1) one_ne_zero
    simp only [one_mul, MulChar.map_one] at h
    rw [quadraticTraceGauss_eq_sum, h]
  have hprod := quadraticTraceGauss_mul p q hpq
  rw [sum_traceChar_mul_sq p hp2 hqp, sum_traceChar_mul_sq q hq2 hpq'] at hprod
  unfold normalizedQuadraticTraceGauss
  rw [hprod, hone p hp2, hone q hq2, map_mul, norm_mul, Complex.ofReal_mul]
  have hpn : (‖ringComplex p‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr fun h => NeZero.ne p (ringComplex_injective
      (by rw [h, map_zero]))
  have hqn : (‖ringComplex q‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr fun h => NeZero.ne q (ringComplex_injective
      (by rw [h, map_zero]))
  field_simp

end GaloisForLFunctions.FamilyContinuationTheory
