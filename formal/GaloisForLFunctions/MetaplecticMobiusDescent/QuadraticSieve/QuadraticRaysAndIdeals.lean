/-
Quadratic rays and admissible ideals adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.FiniteSieveOperators
import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.AbelGaussianLimits

/-!
# Quadratic rays and admissible ideals

The quadratic ray ring `QuadraticRayRing`, quadratic ideals and the canonical quadratic rows.
The complex-plane and number-field traces define the same character; quadratic reflection has
an explicit phase depending on the conductor modulo four. The sieve exponent
`HasSieveExponent` and the high-kernel square-part bounds.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter

namespace SchwartzPlanePoisson
open Eisenstein Eisenstein.Coordinates QuadraticPhase.Eisenstein

/-- The complex-plane trace and the intrinsic number-field trace define the same character. -/
lemma principalTraceChar_eq_paperE (c : O) (hc : c ≠ 0) (x : O) :
    principalTraceChar c hc (Ideal.Quotient.mk (Ideal.span {c}) x) =
      paperE (ringComplex x / ringComplex c) := by
  obtain ⟨a, b, ha⟩ := exists_coordinates c
  obtain ⟨u, v, hx⟩ := exists_coordinates x
  change c = eval a b at ha
  change x = eval u v at hx
  subst c
  subst x
  rw [principalTraceChar_eval]
  have hcC := ringComplex_ne_zero hc
  have hlC := ringComplex_ne_zero traceLambda_ne_zero
  have hconj : starRingEnd ℂ (ringComplex (eval a b)) =
      (((a : ℝ) - b : ℝ) : ℂ) + ((-(b : ℝ) : ℝ) : ℂ) * ringComplex omega := by
    simp only [ringComplex_eval, map_add, map_mul, map_intCast, complex_omega_conjugate]
    push_cast
    ring
  have harg : ringComplex (eval u v) / ringComplex (eval a b) / ringComplex traceLambda =
      (ringComplex (eval u v) * starRingEnd ℂ (ringComplex (eval a b)) /
        ringComplex traceLambda) / (‖ringComplex (eval a b)‖ ^ 2 : ℝ) := by
    rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
    have hs : starRingEnd ℂ (ringComplex (eval a b)) ≠ 0 := by
      intro h
      apply hcC
      simpa only [map_zero, starRingEnd_self_apply] using congrArg (starRingEnd ℂ) h
    field_simp
  have hnum :
      (ringComplex (eval u v) * starRingEnd ℂ (ringComplex (eval a b)) / ringComplex traceLambda) +
        starRingEnd ℂ (ringComplex (eval u v) * starRingEnd ℂ (ringComplex (eval a b)) /
          ringComplex traceLambda) = (((a * v - b * u : ℤ) : ℝ) : ℂ) := by
    rw [hconj, ringComplex_eval]
    convert complexTrace_real_basis_product u v ((a : ℝ) - b) (-(b : ℝ)) using 1 <;>
      push_cast <;> ring
  change _ = Complex.exp (2 * Real.pi * Complex.I * (_ + starRingEnd ℂ _))
  rw [harg, map_div₀, Complex.conj_ofReal, ← add_div, hnum, complex_norm_eval_sq]
  congr 1
  push_cast
  ring

lemma residueTraceQuotientChar_eq_principal (c : O) (hc : c ≠ 0) :
    residueTraceQuotientChar 1 c hc = principalTraceChar c hc := by
  ext x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [residueTraceQuotientChar_phase, principalTraceChar_eq_paperE, one_mul]
  change tracePhase _ = tracePhase _
  congr 1
  ring

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MulChar AddChar QuadraticPhase.Eisenstein
open scoped SchwartzMap

lemma complexQuadraticChar_inv (P : Ideal O) [P.IsMaximal] :
    (complexQuadraticChar P)⁻¹ = complexQuadraticChar P := by
  ext x
  rw [← MulChar.star_apply']
  change starRingEnd ℂ ((quadraticChar (O ⧸ P) x : ℤ) : ℂ) =
    ((quadraticChar (O ⧸ P) x : ℤ) : ℂ)
  exact map_intCast (starRingEnd ℂ) _

/-- Quadratic reflection has an explicit phase depending only on the conductor modulo four. -/
theorem prime_quadratic_radial_poisson {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, primeCuspRowCharacter p (fun i => complexQuadraticChar (Ideal.span {p i})) z *
      W (‖ringComplex z‖ ^ 2 / Y)) =
      ((Y : ℂ) * fixedDualAverage (∏ i, p i) / (‖ringComplex (∏ i, p i)‖ : ℂ)) *
        ∑' h : O, primeCuspRowCharacter p (fun i => complexQuadraticChar (Ideal.span {p i})) h *
          paperRadialFourier W (Y * ‖ringComplex h‖ ^ 2 / ‖ringComplex (∏ i, p i)‖ ^ 2) := by
  classical
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have hspan : Ideal.span {c} = ∏ i, P i := span_finset_prime_product p Finset.univ
  let e : (O ⧸ Ideal.span {c}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq hspan).trans (Eisenstein.primeCRT P hinj)
  have he (z : O) (i : ι) :
      e (Ideal.Quotient.mk (Ideal.span {c}) z) i = Ideal.Quotient.mk (P i) z := by
    simp only [e, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, Eisenstein.primeCRT]
    rfl
  let χ : ∀ i, MulChar (O ⧸ P i) ℂ := fun i => complexQuadraticChar (P i)
  have hχ (i : ι) : χ i ≠ 1 := complexQuadraticChar_ne_one (P i) (hodd i)
  let ψ := residueTraceQuotientChar 1 c hc
  let A : O ⧸ Ideal.span {c} → ℂ := fun x => ∏ i, χ i (e x i)
  let G := ∑ x : O ⧸ Ideal.span {c}, A x * ψ x
  have hG : G = quadraticTraceGauss c hc := by
    change (∑ x : O ⧸ Ideal.span {c},
      (∏ i, ((quadraticChar (O ⧸ P i)).ringHomComp (Int.castRingHom ℂ)) (e x i)) * ψ x) = _
    rw [QuadraticPhase.ProductGauss.quadratic_factorization_equiv (fun i => O ⧸ P i) e ψ
      (residueTraceQuotientChar_primitive c hc) hodd]
    simp only [ψ, residueTraceQuotientChar_eq_principal, quadraticTraceGauss]
  have hphase : G / (‖ringComplex c‖ : ℂ) = fixedDualAverage c := by
    rw [hG]
    exact normalizedQuadraticTraceGauss_eq_fixedDualAverage c hc
  have hPoisson :
      (∑' z : O, A (Ideal.Quotient.mk (Ideal.span {c}) z) * W (‖ringComplex z‖ ^ 2 / Y)) =
      (Y / ‖ringComplex c‖ ^ 2 : ℝ) • (G * ∑' h : O,
        (∏ i, (χ i)⁻¹ (e (Ideal.Quotient.mk (Ideal.span {c}) h) i)) *
          paperRadialFourier W (Y * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2)) := by
    rw [actual_radial_poisson_trace W Y hY c hc A]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro h
    rw [finite_crt_gauss_transform (fun i => O ⧸ P i) e χ hχ ψ]
    ring
  have hA (z : O) : A (Ideal.Quotient.mk (Ideal.span {c}) z) =
      primeCuspRowCharacter p (fun i => complexQuadraticChar (P i)) z := by
    change (∏ i, χ i (e (Ideal.Quotient.mk (Ideal.span {c}) z) i)) = _
    simp only [he]
    rfl
  simp only [hA, χ, complexQuadraticChar_inv, he] at hPoisson
  rw [hPoisson]
  change ((Y / ‖ringComplex c‖ ^ 2 : ℝ) : ℂ) *
      (G * ∑' h : O, (∏ i, complexQuadraticChar (P i) (Ideal.Quotient.mk (P i) h)) *
        paperRadialFourier W (Y * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2)) =
    ((Y : ℂ) * fixedDualAverage c / (‖ringComplex c‖ : ℂ)) *
      ∑' h : O, (∏ i, complexQuadraticChar (P i) (Ideal.Quotient.mk (P i) h)) *
        paperRadialFourier W (Y * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2)
  rw [← hphase]
  push_cast
  ring

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein QuadraticPhase.Eisenstein

local instance quotientFinite (c : O) [NeZero c] : Finite (O ⧸ Ideal.span {c}) :=
  finite_quotient_span (NeZero.ne c)

local instance quotientFintype (c : O) [NeZero c] : Fintype (O ⧸ Ideal.span {c}) :=
  Fintype.ofFinite _

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


end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MulChar AddChar

lemma primitive_unit_shift {R : Type*} [CommRing R] (ψ : AddChar R ℂ)
    (hψ : ψ.IsPrimitive) (u : R) (hu : IsUnit u) : (ψ.mulShift u).IsPrimitive := by
  obtain ⟨v, rfl⟩ := hu
  intro a ha
  rw [AddChar.mulShift_mulShift]
  apply hψ
  intro h
  apply ha
  have hh := congrArg (fun b : R => (↑v⁻¹ : R) * b) h
  simpa only [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul, mul_zero] using hh

lemma finite_quadratic_character_inv {F : Type*} [Field F] [Fintype F] :
    (((quadraticChar F).ringHomComp (Int.castRingHom ℂ)) : MulChar F ℂ)⁻¹ =
      (quadraticChar F).ringHomComp (Int.castRingHom ℂ) := by
  ext x
  rw [← MulChar.star_apply']
  change starRingEnd ℂ ((quadraticChar F x : ℤ) : ℂ) = ((quadraticChar F x : ℤ) : ℂ)
  exact map_intCast (starRingEnd ℂ) _

/-- A unit multiplier of a quadratic square sum contributes exactly its quadratic character. -/
theorem finite_crt_quadratic_square_twist {ι R : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    [CommRing R] [Fintype R] (e : R ≃+* ∀ i, F i)
    (hodd : ∀ i, ringChar (F i) ≠ 2) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive)
    (u : R) (hu : IsUnit u) :
    (∑ x : R, ψ (u * x ^ 2)) =
      (∏ i, (quadraticChar (F i) (e u i) : ℂ)) * ∑ x : R, ψ (x ^ 2) := by
  let χ : ∀ i, MulChar (F i) ℂ := fun i =>
    (quadraticChar (F i)).ringHomComp (Int.castRingHom ℂ)
  have hχ (i : ι) : χ i ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := ℂ))).mpr
      (quadraticChar_ne_one (hodd i))
  have ht := QuadraticPhase.ProductGauss.quadratic_factorization_equiv F e
    (ψ.mulShift u) (primitive_unit_shift ψ hψ u hu) hodd
  have h0 := QuadraticPhase.ProductGauss.quadratic_factorization_equiv F e ψ hψ hodd
  change (∑ x : R, (∏ i, χ i (e x i)) * ψ (u * x)) = ∑ x : R, ψ (u * x ^ 2) at ht
  rw [← ht, finite_crt_gauss_transform F e χ hχ ψ]
  change (∏ i, (χ i)⁻¹ (e u i)) * (∑ x : R, (∏ i, χ i (e x i)) * ψ x) = _
  rw [h0]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  dsimp only [χ]
  rw [finite_quadratic_character_inv]
  rfl

/-- Primitive quadratic square sums on products of odd fields have square-root mass. -/
theorem finite_crt_quadratic_square_norm_sq {ι R : Type*} [Fintype ι] [DecidableEq ι]
    (F : ι → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]
    [CommRing R] [Fintype R] (e : R ≃+* ∀ i, F i)
    (hodd : ∀ i, ringChar (F i) ≠ 2) (ψ : AddChar R ℂ) (hψ : ψ.IsPrimitive) :
    ‖∑ x : R, ψ (x ^ 2)‖ ^ 2 = (Fintype.card R : ℝ) := by
  let χ : ∀ i, MulChar (F i) ℂ := fun i =>
    (quadraticChar (F i)).ringHomComp (Int.castRingHom ℂ)
  have hχ (i : ι) : χ i ≠ 1 :=
    (MulChar.ringHomComp_ne_one_iff (Int.cast_injective (α := ℂ))).mpr
      (quadraticChar_ne_one (hodd i))
  rw [← QuadraticPhase.ProductGauss.quadratic_factorization_equiv F e ψ hψ hodd]
  exact finite_crt_gauss_norm_sq F e χ hχ ψ hψ

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein QuadraticPhase.Eisenstein

/-- CRT on the principal ideal generated by a product of distinct prime generators. -/
def primeProductCRT {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i})) :
    (O ⧸ Ideal.span {∏ i, p i}) ≃+* ∀ i, O ⧸ Ideal.span {p i} :=
  (Ideal.quotEquivOfEq (span_finset_prime_product p Finset.univ)).trans
    (Eisenstein.primeCRT (fun i => Ideal.span {p i}) hinj)

lemma primeProductCRT_mk {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (z : O) (i : ι) :
    primeProductCRT p hinj (Ideal.Quotient.mk (Ideal.span {∏ i, p i}) z) i =
      Ideal.Quotient.mk (Ideal.span {p i}) z := by
  simp only [primeProductCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, Eisenstein.primeCRT]
  rfl

lemma prime_quadratic_trace_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    ‖quadraticTraceGauss (∏ i, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))‖ ^ 2 =
      ‖ringComplex (∏ i, p i)‖ ^ 2 := by
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  change ‖∑ x : O ⧸ Ideal.span {c}, principalTraceChar c hc (x ^ 2)‖ ^ 2 = _
  rw [finite_crt_quadratic_square_norm_sq (fun i => O ⧸ Ideal.span {p i})
    (primeProductCRT p hinj) hodd (principalTraceChar c hc) (principalTraceChar_primitive c hc)]
  simpa only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    using (ringComplex_norm_sq_eq_absNorm_span c).symm

lemma prime_quadratic_phase_norm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    ‖fixedDualAverage (∏ i, p i)‖ = 1 := by
  have hc : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hn := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    (prime_quadratic_trace_mass p hp hinj hodd)
  rw [← normalizedQuadraticTraceGauss_eq_fixedDualAverage _ hc,
    normalizedQuadraticTraceGauss, norm_div, hn, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr (ringComplex_ne_zero hc))]

/-- The quadratic trace square sum with an integral multiplier. -/
def quadraticTraceTwist (c : O) (hc : c ≠ 0) (u : O) : ℂ :=
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  ∑ x : O ⧸ Ideal.span {c}, principalTraceChar c hc
    (Ideal.Quotient.mk (Ideal.span {c}) u * x ^ 2)

lemma prime_quadratic_trace_twist {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (u : O) (hu : IsCoprime (∏ i, p i) u) :
    quadraticTraceTwist (∏ i, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) u =
      primeCuspRowCharacter p (fun i => complexQuadraticChar (Ideal.span {p i})) u *
        quadraticTraceGauss (∏ i, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) := by
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {c}) u) := by
    change IsCoprime c u at hu
    obtain ⟨a, b, hab⟩ := hu
    have hm := congrArg (Ideal.Quotient.mk (Ideal.span {c})) hab
    have hz : Ideal.Quotient.mk (Ideal.span {c}) c = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self c)
    simp only [map_add, map_mul, map_one, hz, mul_zero, zero_add] at hm
    exact IsUnit.of_mul_eq_one_right _ hm
  have ht := finite_crt_quadratic_square_twist (fun i => O ⧸ Ideal.span {p i})
    (primeProductCRT p hinj) hodd (principalTraceChar c hc) (principalTraceChar_primitive c hc)
    (Ideal.Quotient.mk (Ideal.span {c}) u) hunit
  change (∑ x : O ⧸ Ideal.span {c}, principalTraceChar c hc
      (Ideal.Quotient.mk (Ideal.span {c}) u * x ^ 2)) =
    (∏ i, (quadraticChar (O ⧸ Ideal.span {p i}) (Ideal.Quotient.mk (Ideal.span {p i}) u) : ℂ)) *
      ∑ x : O ⧸ Ideal.span {c}, principalTraceChar c hc (x ^ 2)
  simpa only [c, primeProductCRT_mk] using ht

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein QuadraticPhase.Eisenstein

lemma primeCuspRowCharacter_restrict {ι : Type*} (p : ι → O)
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S : Finset ι) (z : O) :
    primeCuspRowCharacter (fun i : S => p i.val) (fun i => χ i.val) z =
      primeSubsetRow p χ S z := by
  classical
  change (∏ i : S, χ i.val (Ideal.Quotient.mk (Ideal.span {p i.val}) z)) =
    ∏ i ∈ S, χ i (Ideal.Quotient.mk (Ideal.span {p i}) z)
  exact Finset.prod_coe_sort (s := S)
    (f := fun i : ι => χ i (Ideal.Quotient.mk (Ideal.span {p i}) z))

/-- Quadratic residue symbol between squarefree products in a common prime family. -/
def quadraticSubsetSymbol {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (S T : Finset ι) : ℂ :=
  primeSubsetRow p (fun i => complexQuadraticChar (Ideal.span {p i})) S (∏ i ∈ T, p i)

lemma prime_subsets_coprime {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (S T : Finset ι) (hd : Disjoint S T) : IsCoprime (∏ i ∈ S, p i) (∏ i ∈ T, p i) := by
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.prod_right
  intro j hj
  have hij : i ≠ j := by
    intro h
    subst j
    exact Finset.disjoint_left.mp hd hi hj
  exact (Ideal.isCoprime_span_singleton_iff _ _).mp
    (Ideal.isCoprime_of_isMaximal (hinj.ne hij))

lemma quadraticSubsetSymbol_zero_of_overlap {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (S T : Finset ι) (hd : ¬ Disjoint S T) : quadraticSubsetSymbol p S T = 0 := by
  obtain ⟨i, hi, hj⟩ := Finset.not_disjoint_iff.mp hd
  unfold quadraticSubsetSymbol primeSubsetRow
  apply Finset.prod_eq_zero hi
  have hz : Ideal.Quotient.mk (Ideal.span {p i}) (∏ j ∈ T, p j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem p hj))
  rw [hz, MulChar.map_zero]

lemma quadraticSubsetRow_sq {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (S : Finset ι) (z : O)
    (hz : IsCoprime (∏ i ∈ S, p i) z) :
    primeSubsetRow p (fun i => complexQuadraticChar (Ideal.span {p i})) S z ^ 2 = 1 := by
  rw [primeSubsetRow, ← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i hi
  have hn : Ideal.Quotient.mk (Ideal.span {p i}) z ≠ 0 := by
    intro h
    have hd : p i ∣ z := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp h)
    have hu := hz.isUnit_of_dvd' (Finset.dvd_prod_of_mem p hi) hd
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top (Ideal.span_singleton_eq_top.mpr hu)
  change (quadraticChar (O ⧸ Ideal.span {p i}) (Ideal.Quotient.mk (Ideal.span {p i}) z) : ℂ) ^ 2 = 1
  exact_mod_cast quadraticChar_sq_one hn

/-- Composite quadratic reciprocity has only the fixed modulo-four Gauss phase. -/
theorem quadraticSubsetSymbol_reciprocity {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (S T : Finset ι) :
    quadraticSubsetSymbol p S T =
      (fixedDualAverage ((∏ i ∈ S, p i) * (∏ i ∈ T, p i)) /
        (fixedDualAverage (∏ i ∈ S, p i) * fixedDualAverage (∏ i ∈ T, p i))) *
          quadraticSubsetSymbol p T S := by
  classical
  by_cases hd : Disjoint S T
  · let c := ∏ i ∈ S, p i
    let d := ∏ i ∈ T, p i
    have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
    have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
    letI : NeZero c := ⟨hc⟩
    letI : NeZero d := ⟨hd0⟩
    have hcd : IsCoprime c d := prime_subsets_coprime p hinj S T hd
    have hs : quadraticTraceTwist c hc d =
        quadraticSubsetSymbol p S T * quadraticTraceGauss c hc := by
      have h := prime_quadratic_trace_twist (fun i : S => p i.val) (fun i => hp i.val)
        (hinj.comp Subtype.val_injective) (fun i => hodd i.val) d
        (by simpa only [Finset.prod_coe_sort] using hcd)
      rw [primeCuspRowCharacter_restrict p (fun i => complexQuadraticChar (Ideal.span {p i})) S d] at h
      simpa only [Finset.prod_coe_sort, quadraticSubsetSymbol, c, d] using h
    have ht : quadraticTraceTwist d hd0 c =
        quadraticSubsetSymbol p T S * quadraticTraceGauss d hd0 := by
      have h := prime_quadratic_trace_twist (fun i : T => p i.val) (fun i => hp i.val)
        (hinj.comp Subtype.val_injective) (fun i => hodd i.val) c
        (by simpa only [Finset.prod_coe_sort] using hcd.symm)
      rw [primeCuspRowCharacter_restrict p (fun i => complexQuadraticChar (Ideal.span {p i})) T c] at h
      simpa only [Finset.prod_coe_sort, quadraticSubsetSymbol, c, d] using h
    have hcrt := quadraticTraceGauss_mul c d hcd
    change quadraticTraceGauss (c * d) (mul_ne_zero hc hd0) =
      quadraticTraceTwist c hc d * quadraticTraceTwist d hd0 c at hcrt
    rw [hs, ht] at hcrt
    have hphase : fixedDualAverage (c * d) =
        (quadraticSubsetSymbol p S T * quadraticSubsetSymbol p T S) *
          (fixedDualAverage c * fixedDualAverage d) := by
      rw [← normalizedQuadraticTraceGauss_eq_fixedDualAverage _ (mul_ne_zero hc hd0),
        ← normalizedQuadraticTraceGauss_eq_fixedDualAverage c hc,
        ← normalizedQuadraticTraceGauss_eq_fixedDualAverage d hd0]
      unfold normalizedQuadraticTraceGauss
      rw [hcrt, map_mul, norm_mul, Complex.ofReal_mul]
      ring
    have hcn : ‖fixedDualAverage c‖ = 1 := by
      simpa only [c, Finset.prod_coe_sort] using prime_quadratic_phase_norm
        (fun i : S => p i.val) (fun i => hp i.val)
        (hinj.comp Subtype.val_injective) (fun i => hodd i.val)
    have hdn : ‖fixedDualAverage d‖ = 1 := by
      simpa only [d, Finset.prod_coe_sort] using prime_quadratic_phase_norm
        (fun i : T => p i.val) (fun i => hp i.val)
        (hinj.comp Subtype.val_injective) (fun i => hodd i.val)
    have hcphase : fixedDualAverage c ≠ 0 := norm_ne_zero_iff.mp (by rw [hcn]; exact one_ne_zero)
    have hdphase : fixedDualAverage d ≠ 0 := norm_ne_zero_iff.mp (by rw [hdn]; exact one_ne_zero)
    have hprod : quadraticSubsetSymbol p S T * quadraticSubsetSymbol p T S =
        fixedDualAverage (c * d) / (fixedDualAverage c * fixedDualAverage d) := by
      apply (eq_div_iff (mul_ne_zero hcphase hdphase)).mpr
      exact hphase.symm
    have hsq : quadraticSubsetSymbol p T S ^ 2 = 1 := quadraticSubsetRow_sq p T c hcd.symm
    calc
      _ = quadraticSubsetSymbol p S T * quadraticSubsetSymbol p T S ^ 2 := by rw [hsq, mul_one]
      _ = _ := by rw [pow_two, ← mul_assoc, hprod]
  · rw [quadraticSubsetSymbol_zero_of_overlap p S T hd,
      quadraticSubsetSymbol_zero_of_overlap p T S (fun h => hd h.symm), mul_zero]

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein Eisenstein.Coordinates QuadraticPhase.Eisenstein

/-- The four-term Gauss average is bounded by two, and every nonzero value has modulus at least one. -/
lemma fixedDualAverage_bounds (c : O) :
    ‖fixedDualAverage c‖ ≤ 2 ∧ ‖(fixedDualAverage c)⁻¹‖ ≤ 1 := by
  obtain ⟨⟨a, b⟩, hab⟩ := (rationalCoordEquiv 4 (by decide)).surjective
    (Ideal.Quotient.mk (Ideal.span {(4 : O)}) c)
  change Ideal.Quotient.mk (Ideal.span {(4 : O)})
    (eval (ZMod.cast a) (ZMod.cast b)) = Ideal.Quotient.mk (Ideal.span {(4 : O)}) c at hab
  rw [fixedDualAverage_eq_of_mod_four c _ hab.symm, fixedDualAverage_formula]
  fin_cases a <;> fin_cases b <;>
    norm_num [ZMod.cast, ZMod.val, zpow_neg, zpow_ofNat, Complex.I_sq, Complex.I_pow_three, Complex.inv_I] <;>
    ring_nf <;> norm_num [zpow_ofNat, Complex.I_sq, Complex.I_pow_three, Complex.inv_I]

abbrev QuadraticRayRing := O ⧸ Ideal.span {(4 : O)}

noncomputable instance quadraticRayRingFintype : Fintype QuadraticRayRing := by
  letI : Finite QuadraticRayRing := finite_quotient_span (by norm_num : (4 : O) ≠ 0)
  exact Fintype.ofFinite _

lemma quadraticRayRing_card : Fintype.card QuadraticRayRing = 16 := by
  have h := rational_modulus_card 4
  simpa only [Nat.card_eq_fintype_card, Nat.cast_ofNat, show (4 : ℕ) ^ 2 = 16 by decide] using h

def rayQuadraticPhase (r : QuadraticRayRing) : ℂ :=
  fixedDualAverage (QuadraticPhase.Eisenstein.GaussianShiftedPartition.representative 4 r)

lemma rayQuadraticPhase_mk (c : O) :
    rayQuadraticPhase (Ideal.Quotient.mk (Ideal.span {(4 : O)}) c) = fixedDualAverage c := by
  apply fixedDualAverage_eq_of_mod_four
  exact QuadraticPhase.Eisenstein.GaussianShiftedPartition.representative_spec _ _

def rayQuadraticPair (r s : QuadraticRayRing) : ℂ :=
  rayQuadraticPhase (r * s) / (rayQuadraticPhase r * rayQuadraticPhase s)

lemma rayQuadraticPair_mk (c d : O) :
    rayQuadraticPair (Ideal.Quotient.mk (Ideal.span {(4 : O)}) c)
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) d) =
      fixedDualAverage (c * d) / (fixedDualAverage c * fixedDualAverage d) := by
  simp only [rayQuadraticPair, ← map_mul, rayQuadraticPhase_mk]

lemma rayQuadraticPair_norm (r s : QuadraticRayRing) : ‖rayQuadraticPair r s‖ ≤ 2 := by
  rw [rayQuadraticPair, div_eq_mul_inv, mul_inv_rev, norm_mul, norm_mul]
  have hr := (fixedDualAverage_bounds (QuadraticPhase.Eisenstein.GaussianShiftedPartition.representative 4 r)).2
  have hs := (fixedDualAverage_bounds (QuadraticPhase.Eisenstein.GaussianShiftedPartition.representative 4 s)).2
  have hprod := (fixedDualAverage_bounds (QuadraticPhase.Eisenstein.GaussianShiftedPartition.representative 4 (r * s))).1
  exact (mul_le_mul hprod
    ((mul_le_mul hs hr (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)).trans_eq (mul_one 2)

lemma rayQuadraticPair_sum_norm :
    (∑ r : QuadraticRayRing, ∑ s : QuadraticRayRing, ‖rayQuadraticPair r s‖) ≤ 512 := by
  calc
    _ ≤ ∑ _r : QuadraticRayRing, ∑ _s : QuadraticRayRing, (2 : ℝ) :=
      Finset.sum_le_sum (fun r _ => Finset.sum_le_sum (fun s _ => rayQuadraticPair_norm r s))
    _ = 512 := by simp only [Finset.sum_const, Finset.card_univ, quadraticRayRing_card, nsmul_eq_mul]; norm_num

/-- Reduction modulo four separates reciprocity into a fixed finite sum of row and column masks. -/
lemma rayQuadraticPair_separation (c d : O) :
    rayQuadraticPair (Ideal.Quotient.mk (Ideal.span {(4 : O)}) c)
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) d) =
      ∑ r : QuadraticRayRing, ∑ s : QuadraticRayRing, rayQuadraticPair r s *
        (if Ideal.Quotient.mk (Ideal.span {(4 : O)}) c = r then 1 else 0) *
        (if Ideal.Quotient.mk (Ideal.span {(4 : O)}) d = s then 1 else 0) := by
  classical
  simp [mul_ite]

lemma quadraticSubsetSymbol_star {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (S T : Finset ι) :
    star (quadraticSubsetSymbol p S T) = quadraticSubsetSymbol p S T := by
  simp only [quadraticSubsetSymbol, primeSubsetRow, star_prod, MulChar.star_apply', complexQuadraticChar_inv]

/-- Finite quadratic sieve matrices admit uniform row-column duality. -/
theorem quadratic_subset_matrix_reverse {ι m n : Type*} [DecidableEq ι]
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (rows : m → Finset ι) (cols : n → Finset ι) :
    ‖FiniteSieveOperator.operator (fun i j => quadraticSubsetSymbol p (cols j) (rows i))‖ ≤
      512 * ‖FiniteSieveOperator.operator (fun j i => quadraticSubsetSymbol p (rows i) (cols j))‖ := by
  classical
  let A : Matrix m n ℂ := fun i j => quadraticSubsetSymbol p (cols j) (rows i)
  let B := Matrix.conjTranspose (fun j i => quadraticSubsetSymbol p (rows i) (cols j) : Matrix n m ℂ)
  let C : QuadraticRayRing × QuadraticRayRing → ℂ := fun k => rayQuadraticPair k.1 k.2
  let l : QuadraticRayRing × QuadraticRayRing → m → ℂ := fun k i =>
    if Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ s ∈ rows i, p s) = k.2 then 1 else 0
  let r : QuadraticRayRing × QuadraticRayRing → n → ℂ := fun k j =>
    if Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ s ∈ cols j, p s) = k.1 then 1 else 0
  have hB (i : m) (j : n) : B i j = quadraticSubsetSymbol p (rows i) (cols j) :=
    quadraticSubsetSymbol_star p _ _
  have hl (k : QuadraticRayRing × QuadraticRayRing) (i : m) : ‖l k i‖ ≤ 1 := by
    dsimp only [l]
    split_ifs <;> norm_num
  have hr (k : QuadraticRayRing × QuadraticRayRing) (j : n) : ‖r k j‖ ≤ 1 := by
    dsimp only [r]
    split_ifs <;> norm_num
  have hA (i : m) (j : n) : A i j = ∑ k, C k * (l k i * B i j * r k j) := by
    change quadraticSubsetSymbol p (cols j) (rows i) = _
    rw [quadraticSubsetSymbol_reciprocity p hp hinj hodd,
      ← rayQuadraticPair_mk, rayQuadraticPair_separation, Fintype.sum_prod_type]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    rw [hB]
    dsimp only [C, l, r]
    ring
  have hmass : (∑ k, ‖C k‖) ≤ 512 := by
    simpa only [C, Fintype.sum_prod_type] using rayQuadraticPair_sum_norm
  calc
    _ ≤ (∑ k, ‖C k‖) * ‖FiniteSieveOperator.operator B‖ :=
      FiniteSieveOperator.separated_phase_norm_le A B C l r hl hr hA
    _ ≤ 512 * ‖FiniteSieveOperator.operator B‖ := mul_le_mul_of_nonneg_right hmass (norm_nonneg _)
    _ = _ := by
      change 512 * ‖FiniteSieveOperator.operator
        (Matrix.conjTranspose (fun j i => quadraticSubsetSymbol p (rows i) (cols j) : Matrix n m ℂ))‖ = _
      rw [FiniteSieveOperator.operator_conjTranspose_norm]

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory QuadraticPhase.Eisenstein
open scoped SchwartzMap

/-- Masks preserve the same Gauss phase; selected divisors only rescale the dual radial variable. -/
theorem quadratic_row_masked_radial_poisson {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    ∀ {κ : Type*} (q : κ → O) (hq : ∀ i, q i ≠ 0)
      (hcop : Pairwise (Function.onFun IsCoprime q)) (S : Finset κ)
      (W : 𝓢(ℝ, ℂ)) (Y : ℝ), 0 < Y →
      (∑' z : O, primeCoprimeMask q S z * primeCuspRowCharacter p (fun i => complexQuadraticChar (Ideal.span {p i})) z *
        W (‖ringComplex z‖ ^ 2 / Y)) =
        ((Y : ℂ) * fixedDualAverage (∏ i, p i) / (‖ringComplex (∏ i, p i)‖ : ℂ)) *
          ∑ E ∈ S.powerset,
            ((-1 : ℂ) ^ E.card * primeCuspRowCharacter p (fun i => complexQuadraticChar (Ideal.span {p i})) (∏ i ∈ E, q i) /
              (‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 : ℝ)) *
              ∑' h : O, primeCuspRowCharacter p (fun i => complexQuadraticChar (Ideal.span {p i})) h *
                paperRadialFourier W
                  (Y * ‖ringComplex h‖ ^ 2 /
                    (‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 * ‖ringComplex (∏ i, p i)‖ ^ 2)) := by
  classical
  intro κ q hq hcop S W Y hY
  rw [prime_row_masked_dilations p (fun i => complexQuadraticChar (Ideal.span {p i})) q hq hcop S W Y hY, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  have hd : (∏ i ∈ E, q i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hq i)
  have hn : 0 < ‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hd))
  rw [prime_quadratic_radial_poisson p hp hinj hodd W _ (div_pos hY hn)]
  have harg (h : O) :
      Y / ‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 * ‖ringComplex h‖ ^ 2 /
          ‖ringComplex (∏ i, p i)‖ ^ 2 =
        Y * ‖ringComplex h‖ ^ 2 /
          (‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 * ‖ringComplex (∏ i, p i)‖ ^ 2) := by ring
  simp_rw [harg]
  push_cast
  ring


end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein UniqueFactorizationMonoid

/-- Odd unramified prime ideals, with their fixed primary generators. -/
abbrev QuadraticPrime := {P : Ideal O // P.IsMaximal ∧ lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2}

instance quadraticPrimeMaximal (P : QuadraticPrime) : P.val.IsMaximal := P.property.1

def quadraticPrimeGenerator (P : QuadraticPrime) : O := primaryIdealPrime P.val

lemma quadraticPrimeGenerator_ne_zero (P : QuadraticPrime) : quadraticPrimeGenerator P ≠ 0 :=
  primaryIdealPrime_ne_zero P.val P.property.2.1

lemma quadraticPrimeGenerator_span (P : QuadraticPrime) :
    Ideal.span {quadraticPrimeGenerator P} = P.val :=
  (primaryIdealPrime_spec P.val (quadraticPrimeGenerator_ne_zero P)).2.2.1

instance quadraticPrimeGeneratorMaximal (P : QuadraticPrime) :
    (Ideal.span {quadraticPrimeGenerator P}).IsMaximal := by
  rw [quadraticPrimeGenerator_span]
  infer_instance

lemma quadraticPrimeGenerator_span_injective :
    Function.Injective (fun P : QuadraticPrime => Ideal.span {quadraticPrimeGenerator P}) := by
  intro P Q h
  exact Subtype.ext (by simpa only [quadraticPrimeGenerator_span] using h)

lemma quadraticPrimeGenerator_odd (P : QuadraticPrime) :
    ringChar (O ⧸ Ideal.span {quadraticPrimeGenerator P}) ≠ 2 := by
  rw [quadraticPrimeGenerator_span]
  exact P.property.2.2

/-- Squarefree ideals coprime to the primes above two and three. -/
def quadraticIdealAdmissible (I : Ideal O) : Prop :=
  primaryIdealGenerator I ≠ 0 ∧ Squarefree I ∧ ∀ P ∈ primeSupport I, ringChar (O ⧸ P) ≠ 2

abbrev QuadraticIdeal := {I : Ideal O // quadraticIdealAdmissible I}

def quadraticIdealPrimeIndex (I : QuadraticIdeal) (P : primeSupport I.val) : QuadraticPrime :=
  ⟨P.val, (primaryIdealPrime_spec P.val
    (primaryIdealPrime_factor_ne_zero I.val P.val I.property.1 (Multiset.mem_toFinset.mp P.property))).1,
    (primaryIdealPrime_spec P.val
    (primaryIdealPrime_factor_ne_zero I.val P.val I.property.1 (Multiset.mem_toFinset.mp P.property))).2.1,
    I.property.2.2 P.val P.property⟩

def quadraticIdealSupport (I : QuadraticIdeal) : Finset QuadraticPrime :=
  (primeSupport I.val).attach.map
    ⟨quadraticIdealPrimeIndex I, fun _ _ h => Subtype.ext (congrArg (fun P : QuadraticPrime => P.val) h)⟩

lemma quadraticIdealSupport_product (I : QuadraticIdeal) :
    (∏ P ∈ quadraticIdealSupport I, quadraticPrimeGenerator P) = primaryIdealGenerator I.val := by
  rw [quadraticIdealSupport, Finset.prod_map]
  change (∏ P ∈ (primeSupport I.val).attach, primaryIdealPrime P.val) = _
  rw [Finset.prod_attach]
  exact (primaryIdealGenerator_squarefree_support I.val I.property.1 I.property.2.1).symm

lemma quadraticIdealGenerator_injective :
    Function.Injective (fun I : QuadraticIdeal => primaryIdealGenerator I.val) := by
  intro I J h
  change primaryIdealGenerator I.val = primaryIdealGenerator J.val at h
  apply Subtype.ext
  rw [← (primaryIdealGenerator_spec I.val I.property.1).1,
    ← (primaryIdealGenerator_spec J.val J.property.1).1, h]

lemma quadraticIdealSupport_injective : Function.Injective quadraticIdealSupport := by
  intro I J h
  apply quadraticIdealGenerator_injective
  change primaryIdealGenerator I.val = primaryIdealGenerator J.val
  rw [← quadraticIdealSupport_product I, ← quadraticIdealSupport_product J, h]

lemma quadraticIdealSupport_norm (I : QuadraticIdeal) :
    primeSubsetNorm quadraticPrimeGenerator (quadraticIdealSupport I) = (Ideal.absNorm I.val : ℝ) := by
  rw [primeSubsetNorm, quadraticIdealSupport_product, primaryIdealGenerator_norm_sq I.val I.property.1]

def canonicalQuadraticRow (I : QuadraticIdeal) (z : O) : ℂ :=
  primeSubsetRow quadraticPrimeGenerator
    (fun P => complexQuadraticChar (Ideal.span {quadraticPrimeGenerator P})) (quadraticIdealSupport I) z

lemma canonicalQuadraticRow_eq_symbol (I J : QuadraticIdeal) :
    canonicalQuadraticRow I (primaryIdealGenerator J.val) =
      quadraticSubsetSymbol quadraticPrimeGenerator (quadraticIdealSupport I) (quadraticIdealSupport J) := by
  rw [quadraticSubsetSymbol, quadraticIdealSupport_product]
  rfl

abbrev QuadraticIdealRange (N : ℝ) := {I : QuadraticIdeal // (Ideal.absNorm I.val : ℝ) ≤ N}

noncomputable instance quadraticIdealRangeFintype (N : ℝ) : Fintype (QuadraticIdealRange N) := by
  classical
  let S := {I : Ideal O | Ideal.absNorm I ≤ ⌈N⌉₊}
  letI : Finite S := (Ideal.finite_setOf_absNorm_le (S := O) ⌈N⌉₊).to_subtype
  let f : QuadraticIdealRange N → S := fun I => ⟨I.val.val, by
    have h : (Ideal.absNorm I.val.val : ℝ) ≤ (⌈N⌉₊ : ℝ) := I.property.trans (Nat.le_ceil N)
    exact_mod_cast h⟩
  have hf : Function.Injective f := fun I J h => Subtype.ext (Subtype.ext (congrArg (fun J : S => J.val) h))
  letI : Finite (QuadraticIdealRange N) := Finite.of_injective f hf
  exact Fintype.ofFinite _

namespace CanonicalQuadraticSieve

def matrix (M N : ℝ) : Matrix (QuadraticIdealRange M) (QuadraticIdealRange N) ℂ :=
  fun I J => canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val)

def sieveNorm (M N : ℝ) : ℝ := ‖FiniteSieveOperator.operator (matrix M N)‖ ^ 2

lemma sieveNorm_nonneg (M N : ℝ) : 0 ≤ sieveNorm M N := sq_nonneg _

/-- The initial exponent is two; its constant is independent of both norm balls. -/
theorem sieveNorm_initial : ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    sieveNorm M N ≤ C * (M + N ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := primeSubsetRow_initial_operator_bound
  refine ⟨C, hC, ?_⟩
  intro M N hM hN
  classical
  exact hbound quadraticPrimeGenerator quadraticPrimeGenerator_ne_zero
    quadraticPrimeGenerator_span_injective
    (fun P => complexQuadraticChar (Ideal.span {quadraticPrimeGenerator P}))
    (fun P => complexQuadraticChar_ne_one _ (quadraticPrimeGenerator_odd P))
    (fun I : QuadraticIdealRange M => primaryIdealGenerator I.val.val)
    (quadraticIdealGenerator_injective.comp Subtype.val_injective)
    (fun J : QuadraticIdealRange N => quadraticIdealSupport J.val)
    (quadraticIdealSupport_injective.comp Subtype.val_injective) M N hM hN
    (fun I => by rw [primaryIdealGenerator_norm_sq I.val.val I.val.property.1]; exact I.property)
    (fun J => by rw [quadraticIdealSupport_norm]; exact J.property)

/-- Reciprocity costs only a fixed ray-class constant. -/
theorem sieveNorm_reverse (M N : ℝ) : sieveNorm M N ≤ 262144 * sieveNorm N M := by
  classical
  have h := quadratic_subset_matrix_reverse quadraticPrimeGenerator quadraticPrimeGenerator_ne_zero
    quadraticPrimeGenerator_span_injective quadraticPrimeGenerator_odd
    (fun I : QuadraticIdealRange M => quadraticIdealSupport I.val)
    (fun J : QuadraticIdealRange N => quadraticIdealSupport J.val)
  simp only [← canonicalQuadraticRow_eq_symbol] at h
  have hsq := pow_le_pow_left₀ (norm_nonneg _) h 2
  change ‖FiniteSieveOperator.operator
    (fun I : QuadraticIdealRange M => fun J : QuadraticIdealRange N =>
      canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val))‖ ^ 2 ≤
    262144 * ‖FiniteSieveOperator.operator
      (fun J : QuadraticIdealRange N => fun I : QuadraticIdealRange M =>
        canonicalQuadraticRow I.val (primaryIdealGenerator J.val.val))‖ ^ 2
  simpa only [mul_pow, show (512 : ℝ) ^ 2 = 262144 by norm_num] using hsq

/-- Uniform power bounds for the actual quadratic residue matrix. -/
def HasSieveExponent (α : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N : ℝ, 1 ≤ M → 1 ≤ N →
    sieveNorm M N ≤ C * (M * N) ^ ε * (M + N ^ α)

lemma hasSieveExponent_two : HasSieveExponent 2 := by
  obtain ⟨C, hC, hb⟩ := sieveNorm_initial
  intro ε hε
  refine ⟨C, hC, ?_⟩
  intro M N hM hN
  have hMN : 1 ≤ M * N := one_le_mul_of_one_le_of_one_le hM hN
  have hr := Real.one_le_rpow hMN hε.le
  calc
    _ ≤ C * (M + N ^ 2) := hb M N hM hN
    _ ≤ C * (M * N) ^ ε * (M + N ^ (2 : ℝ)) := by
      rw [Real.rpow_two]
      exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC.le hr) (by positivity)

end CanonicalQuadraticSieve
end SchwartzPlanePoisson

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein

/-- Inclusion of norm balls preserves the underlying ideal. -/
def rangeInclusion {X Y : ℝ} (h : X ≤ Y) (I : QuadraticIdealRange X) : QuadraticIdealRange Y :=
  ⟨I.val, I.property.trans h⟩

lemma rangeInclusion_injective {X Y : ℝ} (h : X ≤ Y) : Function.Injective (rangeInclusion h) := by
  intro I J he
  exact Subtype.ext (congrArg (fun J : QuadraticIdealRange Y => J.val) he)

lemma sieveNorm_mono {M N M' N' : ℝ} (hM : M ≤ M') (hN : N ≤ N') :
    sieveNorm M N ≤ sieveNorm M' N' := by
  classical
  have h := FiniteSieveRestriction.submatrix_norm_le
    (rangeInclusion hM) (rangeInclusion_injective hM)
    (rangeInclusion hN) (rangeInclusion_injective hN) (matrix M' N')
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

lemma family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal)
    (hrows : Function.Injective rows) (hcols : Function.Injective cols)
    (M N : ℝ) (hM : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M)
    (hN : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator
      (fun i j => canonicalQuadraticRow (cols j) (primaryIdealGenerator (rows i).val))‖ ^ 2 ≤
      sieveNorm M N := by
  let r : m → QuadraticIdealRange M := fun i => ⟨rows i, hM i⟩
  let c : n → QuadraticIdealRange N := fun j => ⟨cols j, hN j⟩
  have hr : Function.Injective r := fun i j h => hrows (congrArg (fun J : QuadraticIdealRange M => J.val) h)
  have hc : Function.Injective c := fun i j h => hcols (congrArg (fun J : QuadraticIdealRange N => J.val) h)
  classical
  exact pow_le_pow_left₀ (norm_nonneg _)
    (FiniteSieveRestriction.submatrix_norm_le r hr c hc (matrix M N)) 2

lemma energy_bound (M N : ℝ) (a : QuadraticIdealRange N → ℂ) :
    (∑ I : QuadraticIdealRange M,
      ‖∑ J, canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val) * a J‖ ^ 2) ≤
      sieveNorm M N * ∑ J, ‖a J‖ ^ 2 := by
  classical
  exact FiniteSieveOperator.energy_bound (matrix M N) a

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson
open Eisenstein MeasureTheory QuadraticPhase.Eisenstein
open scoped SchwartzMap

/-- Exact second reflection of a Gram entry, retaining the signed common-prime divisor sum. -/
theorem quadraticSubsetRow_gram_poisson {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S T : Finset ι) :
    let p' : ↥((S \ T) ∪ (T \ S)) → O := fun i => p i.val
    let χ' := fun i : ↥((S \ T) ∪ (T \ S)) => complexQuadraticChar (Ideal.span {p i.val})
    ∀ (W : 𝓢(ℝ, ℂ)) (Y : ℝ), 0 < Y →
      (∑' z : O, (star (primeSubsetRow p (fun i => complexQuadraticChar (Ideal.span {p i})) S z) * primeSubsetRow p (fun i => complexQuadraticChar (Ideal.span {p i})) T z) *
        W (‖ringComplex z‖ ^ 2 / Y)) =
        ((Y : ℂ) * fixedDualAverage (∏ i, p' i) / (‖ringComplex (∏ i, p' i)‖ : ℂ)) *
          ∑ E ∈ (S ∩ T).powerset,
            ((-1 : ℂ) ^ E.card * primeCuspRowCharacter p' χ' (∏ i ∈ E, p i) /
              (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ)) *
              ∑' h : O, primeCuspRowCharacter p' χ' h *
                paperRadialFourier W
                  (Y * ‖ringComplex h‖ ^ 2 /
                    (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 * ‖ringComplex (∏ i, p' i)‖ ^ 2)) := by
  classical
  dsimp only
  intro W Y hY
  have hcop : Pairwise (Function.onFun IsCoprime p) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp
      (Ideal.isCoprime_of_isMaximal (hinj.ne hij))
  have hactive : activePrimeRowCharacter p
      (fun i => complexQuadraticChar (Ideal.span {p i})) S T =
      (fun i : ↥((S \ T) ∪ (T \ S)) => complexQuadraticChar (Ideal.span {p i.val})) := by
    funext i
    simp only [activePrimeRowCharacter, complexQuadraticChar_inv, ite_self]
  simp_rw [primeSubsetRow_pair_active, hactive]
  exact quadratic_row_masked_radial_poisson
    (fun i : ↥((S \ T) ∪ (T \ S)) => p i.val) (fun i => hp i.val)
    (hinj.comp Subtype.val_injective) (fun i => hodd i.val) p hp hcop (S ∩ T) W Y hY

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein UniqueFactorizationMonoid

/-- The odd-valuation part of an ideal. -/
def quadraticSquarefreePart (I : Ideal O) : Ideal O :=
  ∏ P ∈ (primeSupport I).filter (fun P => (normalizedFactors I).count P % 2 = 1), P

/-- The square root of the maximal square ideal factor. -/
def quadraticSquarePart (I : Ideal O) : Ideal O :=
  ∏ P ∈ primeSupport I, P ^ ((normalizedFactors I).count P / 2)

lemma quadraticSquarefreePart_squarefree (I : Ideal O) : Squarefree (quadraticSquarefreePart I) :=
  squarefree_support_product (Finset.filter_subset _ _)

lemma quadraticParts_mul_square (I : Ideal O) (hI : I ≠ 0) :
    quadraticSquarefreePart I * quadraticSquarePart I ^ 2 = I := by
  rw [quadraticSquarefreePart, Finset.prod_filter, quadraticSquarePart,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  calc
    _ = ∏ P ∈ primeSupport I, P ^ ((normalizedFactors I).count P) := by
      apply Finset.prod_congr rfl
      intro P hP
      have hm : (normalizedFactors I).count P % 2 = 0 ∨ (normalizedFactors I).count P % 2 = 1 := by omega
      rcases hm with hm | hm
      · rw [if_neg (by omega), one_mul, ← pow_mul]
        congr 1
        omega
      · rw [if_pos hm, ← pow_mul, ← pow_succ']
        congr 1
        omega
    _ = (normalizedFactors I).prod := (Finset.prod_multiset_count (normalizedFactors I)).symm
    _ = I := Ideal.prod_normalizedFactors_eq_self hI

/-- Prime valuations recover both square factors uniquely. -/
theorem squarefree_square_decomposition_unique {A B C D : Ideal O}
    (hB : B ≠ 0) (hD : D ≠ 0) (hA : Squarefree A) (hC : Squarefree C)
    (he : A * B ^ 2 = C * D ^ 2) : A = C ∧ B = D := by
  have hf := congrArg normalizedFactors he
  rw [normalizedFactors_mul hA.ne_zero (pow_ne_zero _ hB),
    normalizedFactors_mul hC.ne_zero (pow_ne_zero _ hD),
    normalizedFactors_pow, normalizedFactors_pow] at hf
  have ha := (squarefree_iff_nodup_normalizedFactors hA.ne_zero).mp hA
  have hc := (squarefree_iff_nodup_normalizedFactors hC.ne_zero).mp hC
  have hcount (P : Ideal O) :
      (normalizedFactors A).count P = (normalizedFactors C).count P ∧
      (normalizedFactors B).count P = (normalizedFactors D).count P := by
    have hp := congrArg (Multiset.count P) hf
    simp only [Multiset.count_add, Multiset.count_nsmul] at hp
    have ha1 := Multiset.nodup_iff_count_le_one.mp ha P
    have hc1 := Multiset.nodup_iff_count_le_one.mp hc P
    omega
  constructor
  · calc
      A = (normalizedFactors A).prod := (Ideal.prod_normalizedFactors_eq_self hA.ne_zero).symm
      _ = (normalizedFactors C).prod := congrArg Multiset.prod (Multiset.ext.mpr (fun P => (hcount P).1))
      _ = C := Ideal.prod_normalizedFactors_eq_self hC.ne_zero
  · calc
      B = (normalizedFactors B).prod := (Ideal.prod_normalizedFactors_eq_self hB).symm
      _ = (normalizedFactors D).prod := congrArg Multiset.prod (Multiset.ext.mpr (fun P => (hcount P).2))
      _ = D := Ideal.prod_normalizedFactors_eq_self hD

lemma quadraticSquarePart_ne_zero (I : Ideal O) : quadraticSquarePart I ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun P hP => pow_ne_zero _ (support_prime hP).ne_zero)

lemma quadraticParts_of_squarefree (A B : Ideal O) (hA : Squarefree A) (hB : B ≠ 0) :
    quadraticSquarefreePart (A * B ^ 2) = A ∧ quadraticSquarePart (A * B ^ 2) = B :=
  squarefree_square_decomposition_unique (quadraticSquarePart_ne_zero _) hB
    (quadraticSquarefreePart_squarefree _) hA
    (quadraticParts_mul_square _ (mul_ne_zero hA.ne_zero (pow_ne_zero _ hB)))

/-- Ideals supported away from two and three, with arbitrary prime multiplicities. -/
def quadraticSupported (I : Ideal O) : Prop :=
  primaryIdealGenerator I ≠ 0 ∧ ∀ P ∈ primeSupport I, ringChar (O ⧸ P) ≠ 2

lemma quadraticSupported_mul (A B : Ideal O) :
    quadraticSupported (A * B) ↔ quadraticSupported A ∧ quadraticSupported B := by
  constructor
  · intro h
    have hg : primaryIdealGenerator A * primaryIdealGenerator B ≠ 0 := by
      simpa only [primaryIdealGenerator_mul] using h.1
    have hA := left_ne_zero_of_mul hg
    have hB := right_ne_zero_of_mul hg
    have hAn := primaryIdealGenerator_ne_zero_ideal A hA
    have hBn := primaryIdealGenerator_ne_zero_ideal B hB
    refine ⟨⟨hA, ?_⟩, ⟨hB, ?_⟩⟩
    · intro P hP
      apply h.2 P
      simpa only [primeSupport, normalizedFactors_mul hAn hBn, Multiset.toFinset_add,
        Finset.mem_union] using Or.inl hP
    · intro P hP
      apply h.2 P
      simpa only [primeSupport, normalizedFactors_mul hAn hBn, Multiset.toFinset_add,
        Finset.mem_union] using Or.inr hP
  · rintro ⟨hA, hB⟩
    refine ⟨by rw [primaryIdealGenerator_mul]; exact mul_ne_zero hA.1 hB.1, ?_⟩
    intro P hP
    have hAn := primaryIdealGenerator_ne_zero_ideal A hA.1
    have hBn := primaryIdealGenerator_ne_zero_ideal B hB.1
    simp only [primeSupport, normalizedFactors_mul hAn hBn, Multiset.toFinset_add,
      Finset.mem_union] at hP
    exact hP.elim (hA.2 P) (hB.2 P)

lemma quadraticSupported_sq (A : Ideal O) : quadraticSupported (A ^ 2) ↔ quadraticSupported A := by
  rw [pow_two, quadraticSupported_mul, and_self]

lemma quadraticSupported_parts (I : Ideal O) (hI : I ≠ 0) :
    quadraticSupported I ↔ quadraticIdealAdmissible (quadraticSquarefreePart I) ∧
      quadraticSupported (quadraticSquarePart I) := by
  have he := quadraticSupported_mul (quadraticSquarefreePart I) (quadraticSquarePart I ^ 2)
  rw [quadraticParts_mul_square I hI, quadraticSupported_sq] at he
  constructor
  · intro h
    obtain ⟨hA, hB⟩ := he.mp h
    exact ⟨⟨hA.1, quadraticSquarefreePart_squarefree I, hA.2⟩, hB⟩
  · rintro ⟨hA, hB⟩
    exact he.mpr ⟨⟨hA.1, hA.2.2⟩, hB⟩

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein

lemma canonicalQuadraticRow_mul (I : QuadraticIdeal) (a b : O) :
    canonicalQuadraticRow I (a * b) = canonicalQuadraticRow I a * canonicalQuadraticRow I b := by
  simp only [canonicalQuadraticRow, primeSubsetRow, map_mul, Finset.prod_mul_distrib]

lemma canonicalQuadraticRow_star (I : QuadraticIdeal) (z : O) :
    star (canonicalQuadraticRow I z) = canonicalQuadraticRow I z := by
  simp only [canonicalQuadraticRow, primeSubsetRow, star_prod, MulChar.star_apply', complexQuadraticChar_inv]

def quadraticIdealMask (I : QuadraticIdeal) (z : O) : ℂ :=
  primeCoprimeMask quadraticPrimeGenerator (quadraticIdealSupport I) z

lemma canonicalQuadraticRow_square (I : QuadraticIdeal) (z : O) :
    canonicalQuadraticRow I (z ^ 2) = quadraticIdealMask I z := by
  rw [pow_two, canonicalQuadraticRow_mul]
  nth_rw 1 [← canonicalQuadraticRow_star I z]
  exact primeSubsetRow_diagonal quadraticPrimeGenerator
    (fun P => complexQuadraticChar (Ideal.span {quadraticPrimeGenerator P})) (quadraticIdealSupport I) z

/-- Square arguments leave only the coprimality density in a quadratic row. -/
lemma canonicalQuadraticRow_squarefree_argument (I : QuadraticIdeal) (A B : Ideal O) :
    canonicalQuadraticRow I (primaryIdealGenerator (A * B ^ 2)) =
      canonicalQuadraticRow I (primaryIdealGenerator A) * quadraticIdealMask I (primaryIdealGenerator B) := by
  have hp : primaryIdealGenerator (B ^ 2) = primaryIdealGenerator B ^ 2 :=
    map_pow primaryIdealGeneratorHom B 2
  rw [primaryIdealGenerator_mul, hp, canonicalQuadraticRow_mul, canonicalQuadraticRow_square]

abbrev QuadraticSupportedIdeal := {I : Ideal O // quadraticSupported I}

/-- Unique squarefree-square decomposition with the arithmetic support retained. -/
def quadraticSupportedPartsEquiv : QuadraticSupportedIdeal ≃ QuadraticIdeal × QuadraticSupportedIdeal where
  toFun I :=
    let h := (quadraticSupported_parts I.val (primaryIdealGenerator_ne_zero_ideal I.val I.property.1)).mp I.property
    (⟨quadraticSquarefreePart I.val, h.1⟩, ⟨quadraticSquarePart I.val, h.2⟩)
  invFun p := ⟨p.1.val * p.2.val ^ 2,
    quadraticSupported_mul _ _ |>.mpr ⟨⟨p.1.property.1, p.1.property.2.2⟩,
      (quadraticSupported_sq _).mpr p.2.property⟩⟩
  left_inv I := Subtype.ext (quadraticParts_mul_square I.val
    (primaryIdealGenerator_ne_zero_ideal I.val I.property.1))
  right_inv p := by
    have h := quadraticParts_of_squarefree p.1.val p.2.val p.1.property.2.1
      (primaryIdealGenerator_ne_zero_ideal p.2.val p.2.property.1)
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)

lemma quadraticSupported_tsum_parts (f : Ideal O → ℂ) :
    (∑' I : QuadraticSupportedIdeal, f I.val) =
      ∑' p : QuadraticIdeal × QuadraticSupportedIdeal, f (p.1.val * p.2.val ^ 2) :=
  (quadraticSupportedPartsEquiv.symm.tsum_eq (fun I => f I.val)).symm

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein

lemma canonicalQuadraticRow_norm_le_one (I : QuadraticIdeal) (z : O) :
    ‖canonicalQuadraticRow I z‖ ≤ 1 := by
  rw [canonicalQuadraticRow, ← primeCuspRowCharacter_restrict]
  exact primeCuspRowCharacter_norm_le_one _ _ z

abbrev QuadraticSupportedRange (M : ℝ) :=
  {I : QuadraticSupportedIdeal // (Ideal.absNorm I.val : ℝ) ≤ M}

noncomputable instance quadraticSupportedRangeFintype (M : ℝ) : Fintype (QuadraticSupportedRange M) := by
  classical
  let S := {I : Ideal O | Ideal.absNorm I ≤ ⌈M⌉₊}
  letI : Finite S := (Ideal.finite_setOf_absNorm_le (S := O) ⌈M⌉₊).to_subtype
  let f : QuadraticSupportedRange M → S := fun I => ⟨I.val.val, by
    have h : (Ideal.absNorm I.val.val : ℝ) ≤ (⌈M⌉₊ : ℝ) := I.property.trans (Nat.le_ceil M)
    exact_mod_cast h⟩
  have hf : Function.Injective f := fun I J h => Subtype.ext (Subtype.ext (congrArg (fun J : S => J.val) h))
  letI : Finite (QuadraticSupportedRange M) := Finite.of_injective f hf
  exact Fintype.ofFinite _

namespace CanonicalQuadraticSieve

/-- The high squarefree-part kernel over the full ideal norm ball. -/
def highMatrix (M N K : ℝ) : Matrix (QuadraticSupportedRange M) (QuadraticIdealRange N) ℂ :=
  fun I J => if K < (Ideal.absNorm (quadraticSquarefreePart I.val.val) : ℝ) then
    canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val) else 0

def highKernelNorm (M N K : ℝ) : ℝ := ‖FiniteSieveOperator.operator (highMatrix M N K)‖ ^ 2

lemma highKernelNorm_nonneg (M N K : ℝ) : 0 ≤ highKernelNorm M N K := sq_nonneg _

lemma highKernel_energy_bound (M N K : ℝ) (a : QuadraticIdealRange N → ℂ) :
    (∑ I, ‖∑ J, highMatrix M N K I J * a J‖ ^ 2) ≤
      highKernelNorm M N K * ∑ J, ‖a J‖ ^ 2 := by
  classical
  exact FiniteSieveOperator.energy_bound _ _

end CanonicalQuadraticSieve
end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein UniqueFactorizationMonoid

lemma quadraticIdealAdmissible_of_dvd {I J : Ideal O}
    (hI : quadraticIdealAdmissible I) (hJI : J ∣ I) : quadraticIdealAdmissible J := by
  obtain ⟨K, rfl⟩ := hJI
  have hJ := ((quadraticSupported_mul J K).mp ⟨hI.1, hI.2.2⟩).1
  exact ⟨hJ.1, hI.2.1.of_mul_left, hJ.2⟩

/-- Exact ideal quotient, used only on divisor columns. -/
def quadraticIdealQuotient (D I : Ideal O) : Ideal O :=
  if h : D ∣ I then h.choose else 0

lemma quadraticIdeal_mul_quotient {D I : Ideal O} (h : D ∣ I) :
    D * quadraticIdealQuotient D I = I := by
  rw [quadraticIdealQuotient, dif_pos h]
  exact h.choose_spec.symm

lemma quadraticIdealQuotient_dvd {D I : Ideal O} (h : D ∣ I) :
    quadraticIdealQuotient D I ∣ I :=
  ⟨D, by rw [mul_comm, quadraticIdeal_mul_quotient h]⟩

lemma quadraticIdealQuotient_admissible {D I : Ideal O}
    (hI : quadraticIdealAdmissible I) (h : D ∣ I) :
    quadraticIdealAdmissible (quadraticIdealQuotient D I) :=
  quadraticIdealAdmissible_of_dvd hI (quadraticIdealQuotient_dvd h)

lemma quadraticIdealQuotient_injective (D : Ideal O) :
    Set.InjOn (quadraticIdealQuotient D) {I : Ideal O | D ∣ I} := by
  intro I hI J hJ h
  rw [← quadraticIdeal_mul_quotient hI, ← quadraticIdeal_mul_quotient hJ, h]

lemma quadraticIdealQuotient_norm {D I : Ideal O} (hD : D ≠ 0) (h : D ∣ I) :
    (Ideal.absNorm (quadraticIdealQuotient D I) : ℝ) = (Ideal.absNorm I : ℝ) / Ideal.absNorm D := by
  have hDnorm : (Ideal.absNorm D : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  apply (eq_div_iff hDnorm).mpr
  have hn := congrArg (fun J : Ideal O => (Ideal.absNorm J : ℝ)) (quadraticIdeal_mul_quotient h)
  simpa only [map_mul, Nat.cast_mul, mul_comm] using hn

lemma quadraticIdealGenerator_factor {D I : Ideal O} (h : D ∣ I) :
    primaryIdealGenerator I = primaryIdealGenerator D * primaryIdealGenerator (quadraticIdealQuotient D I) := by
  rw [← primaryIdealGenerator_mul, quadraticIdeal_mul_quotient h]

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein UniqueFactorizationMonoid

lemma mem_quadraticIdealSupport (I : QuadraticIdeal) (P : QuadraticPrime) :
    P ∈ quadraticIdealSupport I ↔ P.val ∈ primeSupport I.val := by
  constructor
  · intro h
    obtain ⟨Q, _, he⟩ := Finset.mem_map.mp h
    have hval : Q.val = P.val := congrArg (fun R : QuadraticPrime => R.val) he
    simpa only [← hval] using Q.property
  · intro h
    exact Finset.mem_map.mpr ⟨⟨P.val, h⟩, Finset.mem_attach _ _, Subtype.ext rfl⟩

lemma quadraticIdealSupport_mul (I J : Ideal O) (h : quadraticIdealAdmissible (I * J)) :
    quadraticIdealSupport ⟨I * J, h⟩ =
      quadraticIdealSupport ⟨I, quadraticIdealAdmissible_of_dvd h (dvd_mul_right I J)⟩ ∪
      quadraticIdealSupport ⟨J, quadraticIdealAdmissible_of_dvd h (dvd_mul_left J I)⟩ := by
  have hI := quadraticIdealAdmissible_of_dvd h (dvd_mul_right I J)
  have hJ := quadraticIdealAdmissible_of_dvd h (dvd_mul_left J I)
  ext P
  simp only [Finset.mem_union, mem_quadraticIdealSupport, primeSupport,
    normalizedFactors_mul (primaryIdealGenerator_ne_zero_ideal I hI.1)
      (primaryIdealGenerator_ne_zero_ideal J hJ.1), Multiset.toFinset_add]

lemma quadraticIdealSupport_disjoint (I J : Ideal O) (h : quadraticIdealAdmissible (I * J)) :
    Disjoint
      (quadraticIdealSupport ⟨I, quadraticIdealAdmissible_of_dvd h (dvd_mul_right I J)⟩)
      (quadraticIdealSupport ⟨J, quadraticIdealAdmissible_of_dvd h (dvd_mul_left J I)⟩) := by
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  have hpI := Multiset.mem_toFinset.mp ((mem_quadraticIdealSupport _ P).mp hP)
  have hpJ := Multiset.mem_toFinset.mp ((mem_quadraticIdealSupport _ P).mp hQ)
  have hp := prime_of_normalized_factor P.val hpI
  exact hp.2.1 ((IsRelPrime.of_squarefree_mul h.2.1)
    (dvd_of_mem_normalizedFactors hpI) (dvd_of_mem_normalizedFactors hpJ))

/-- Squarefree products split into independent quadratic characters. -/
lemma canonicalQuadraticRow_conductor_mul (I J : Ideal O)
    (h : quadraticIdealAdmissible (I * J)) (z : O) :
    canonicalQuadraticRow ⟨I * J, h⟩ z =
      canonicalQuadraticRow ⟨I, quadraticIdealAdmissible_of_dvd h (dvd_mul_right I J)⟩ z *
      canonicalQuadraticRow ⟨J, quadraticIdealAdmissible_of_dvd h (dvd_mul_left J I)⟩ z := by
  simp only [canonicalQuadraticRow]
  rw [quadraticIdealSupport_mul I J h,
    primeSubsetRow_union _ _ _ _ (quadraticIdealSupport_disjoint I J h)]

lemma canonicalQuadraticRow_divisor_factor (I : QuadraticIdeal) (D : Ideal O)
    (h : D ∣ I.val) (z : O) :
    canonicalQuadraticRow I z =
      canonicalQuadraticRow ⟨D, quadraticIdealAdmissible_of_dvd I.property h⟩ z *
      canonicalQuadraticRow ⟨quadraticIdealQuotient D I.val,
        quadraticIdealQuotient_admissible I.property h⟩ z := by
  have hprod : quadraticIdealAdmissible (D * quadraticIdealQuotient D I.val) := by
    rw [quadraticIdeal_mul_quotient h]
    exact I.property
  have he := canonicalQuadraticRow_conductor_mul D (quadraticIdealQuotient D I.val) hprod z
  simpa only [quadraticIdeal_mul_quotient h] using he

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein

/-- Columns divisible by a fixed ideal, with that common factor removed. -/
def quotientMatrix {m n : Type*} (D : Ideal O)
    (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal) : Matrix m n ℂ :=
  fun i j => if h : D ∣ (cols j).val then
    canonicalQuadraticRow ⟨quadraticIdealQuotient D (cols j).val,
      quadraticIdealQuotient_admissible (cols j).property h⟩ (primaryIdealGenerator (rows i).val)
    else 0

lemma quotientMatrix_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (D : Ideal O) (hD : D ≠ 0)
    (rows : m → QuadraticIdeal) (cols : n → QuadraticIdeal)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N : ℝ) (hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M)
    (hcols : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N) :
    ‖FiniteSieveOperator.operator (quotientMatrix D rows cols)‖ ^ 2 ≤
      sieveNorm M (N / Ideal.absNorm D) := by
  classical
  let S : Finset n := Finset.univ.filter (fun j => D ∣ (cols j).val)
  have hS (j : S) : D ∣ (cols j.val).val := (Finset.mem_filter.mp j.property).2
  let q : S → QuadraticIdeal := fun j => ⟨quadraticIdealQuotient D (cols j.val).val,
    quadraticIdealQuotient_admissible (cols j.val).property (hS j)⟩
  have hq : Function.Injective q := by
    intro i j he
    apply Subtype.ext
    apply hc
    apply Subtype.ext
    apply quadraticIdealQuotient_injective D (hS i) (hS j)
    exact congrArg (fun I : QuadraticIdeal => I.val) he
  have hqn (j : S) : (Ideal.absNorm (q j).val : ℝ) ≤ N / Ideal.absNorm D := by
    change (Ideal.absNorm (quadraticIdealQuotient D (cols j.val).val) : ℝ) ≤ _
    rw [quadraticIdealQuotient_norm hD (hS j)]
    exact div_le_div_of_nonneg_right (hcols j.val) (Nat.cast_nonneg _)
  have hb := family_squared_norm_le rows q hr hq M (N / Ideal.absNorm D) hrows hqn
  apply FiniteSieveOperator.squared_norm_le_of_energy _ _ (sieveNorm_nonneg _ _)
  intro a
  have hsum (i : m) : (∑ j, quotientMatrix D rows cols i j * a j) =
      ∑ j : S, canonicalQuadraticRow (q j) (primaryIdealGenerator (rows i).val) * a j.val := by
    calc
      _ = ∑ j ∈ S, quotientMatrix D rows cols i j * a j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro j _ hj
        have hd : ¬ D ∣ (cols j).val := by
          simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hj
        simp only [quotientMatrix, dif_neg hd, zero_mul]
      _ = ∑ j : S, quotientMatrix D rows cols i j.val * a j.val :=
        (Finset.sum_coe_sort (s := S) (f := fun j => quotientMatrix D rows cols i j * a j)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [quotientMatrix, dif_pos (hS j)]
        rfl
  simp_rw [hsum]
  have he := FiniteSieveOperator.energy_bound
    (fun i j => canonicalQuadraticRow (q j) (primaryIdealGenerator (rows i).val)) (fun j : S => a j.val)
  have hE : (∑ j : S, ‖a j.val‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 := by
    rw [Finset.sum_coe_sort (s := S) (f := fun j : n => ‖a j‖ ^ 2)]
    exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖a j‖)
  exact he.trans ((mul_le_mul_of_nonneg_right hb (by positivity)).trans
    (mul_le_mul_of_nonneg_left hE (sieveNorm_nonneg _ _)))

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein

/-- Any injective high-kernel row family is a restriction of the canonical norm ball. -/
lemma highKernel_family_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → QuadraticSupportedIdeal) (cols : n → QuadraticIdeal)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hM : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M)
    (hN : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N)
    (hK : ∀ i, K < (Ideal.absNorm (quadraticSquarefreePart (rows i).val) : ℝ)) :
    ‖FiniteSieveOperator.operator
      (fun i j => canonicalQuadraticRow (cols j) (primaryIdealGenerator (rows i).val))‖ ^ 2 ≤
      highKernelNorm M N K := by
  let r : m → QuadraticSupportedRange M := fun i => ⟨rows i, hM i⟩
  let c : n → QuadraticIdealRange N := fun j => ⟨cols j, hN j⟩
  have hr' : Function.Injective r := fun i j h => hr (congrArg (fun J : QuadraticSupportedRange M => J.val) h)
  have hc' : Function.Injective c := fun i j h => hc (congrArg (fun J : QuadraticIdealRange N => J.val) h)
  classical
  have hb := FiniteSieveRestriction.submatrix_norm_le r hr' c hc' (highMatrix M N K)
  have he : (fun i j => highMatrix M N K (r i) (c j)) =
      fun i j => canonicalQuadraticRow (cols j) (primaryIdealGenerator (rows i).val) := by
    funext i j
    exact if_pos (hK i)
  rw [he] at hb
  exact pow_le_pow_left₀ (norm_nonneg _) hb 2

/-- Enlarging either norm ball or lowering the squarefree threshold enlarges the kernel bound. -/
lemma highKernelNorm_mono {M N K M' N' K' : ℝ}
    (hM : M ≤ M') (hN : N ≤ N') (hK : K' ≤ K) :
    highKernelNorm M N K ≤ highKernelNorm M' N' K' := by
  classical
  let r : QuadraticSupportedRange M → QuadraticSupportedRange M' :=
    fun I => ⟨I.val, I.property.trans hM⟩
  let c := rangeInclusion hN
  have hr : Function.Injective r := fun I J h =>
    Subtype.ext (congrArg (fun J : QuadraticSupportedRange M' => J.val) h)
  let B : Matrix (QuadraticSupportedRange M) (QuadraticIdealRange N) ℂ :=
    fun I J => highMatrix M' N' K' (r I) (c J)
  let w : QuadraticSupportedRange M → ℂ := fun I =>
    if K < (Ideal.absNorm (quadraticSquarefreePart I.val.val) : ℝ) then 1 else 0
  have hw (I : QuadraticSupportedRange M) : ‖w I‖ ≤ 1 := by
    dsimp only [w]
    split_ifs <;> norm_num
  have he : highMatrix M N K = fun I J => w I * B I J * 1 := by
    funext I J
    change (if K < (Ideal.absNorm (quadraticSquarefreePart I.val.val) : ℝ) then _ else 0) = _
    by_cases h : K < (Ideal.absNorm (quadraticSquarefreePart I.val.val) : ℝ)
    · have h' := hK.trans_lt h
      simp only [highMatrix, w, B, r, c, rangeInclusion, if_pos h, if_pos h', one_mul, mul_one]
    · simp only [highMatrix, w, if_neg h, zero_mul]
  have hb := FiniteSieveRestriction.submatrix_norm_le r hr c (rangeInclusion_injective hN)
    (highMatrix M' N' K')
  have ht := FiniteSieveOperator.diagonal_twist_norm_le B w (fun _ => 1) hw
    (fun _ => by norm_num)
  rw [← he] at ht
  exact pow_le_pow_left₀ (norm_nonneg _) (ht.trans hb) 2

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein

/-- Divisor columns in the high kernel keep the squarefree-part threshold unchanged. -/
def highQuotientMatrix {m n : Type*} (D : Ideal O)
    (rows : m → QuadraticSupportedIdeal) (cols : n → QuadraticIdeal) : Matrix m n ℂ :=
  fun i j => if h : D ∣ (cols j).val then
    canonicalQuadraticRow ⟨quadraticIdealQuotient D (cols j).val,
      quadraticIdealQuotient_admissible (cols j).property h⟩ (primaryIdealGenerator (rows i).val)
    else 0

lemma highQuotientMatrix_squared_norm_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (D : Ideal O) (hD : D ≠ 0)
    (rows : m → QuadraticSupportedIdeal) (cols : n → QuadraticIdeal)
    (hr : Function.Injective rows) (hc : Function.Injective cols)
    (M N K : ℝ) (hrows : ∀ i, (Ideal.absNorm (rows i).val : ℝ) ≤ M)
    (hcols : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ N)
    (hK : ∀ i, K < (Ideal.absNorm (quadraticSquarefreePart (rows i).val) : ℝ)) :
    ‖FiniteSieveOperator.operator (highQuotientMatrix D rows cols)‖ ^ 2 ≤
      highKernelNorm M (N / Ideal.absNorm D) K := by
  classical
  let S : Finset n := Finset.univ.filter (fun j => D ∣ (cols j).val)
  have hS (j : S) : D ∣ (cols j.val).val := (Finset.mem_filter.mp j.property).2
  let q : S → QuadraticIdeal := fun j => ⟨quadraticIdealQuotient D (cols j.val).val,
    quadraticIdealQuotient_admissible (cols j.val).property (hS j)⟩
  have hq : Function.Injective q := by
    intro i j he
    apply Subtype.ext
    apply hc
    apply Subtype.ext
    apply quadraticIdealQuotient_injective D (hS i) (hS j)
    exact congrArg (fun I : QuadraticIdeal => I.val) he
  have hqn (j : S) : (Ideal.absNorm (q j).val : ℝ) ≤ N / Ideal.absNorm D := by
    change (Ideal.absNorm (quadraticIdealQuotient D (cols j.val).val) : ℝ) ≤ _
    rw [quadraticIdealQuotient_norm hD (hS j)]
    exact div_le_div_of_nonneg_right (hcols j.val) (Nat.cast_nonneg _)
  have hb := highKernel_family_squared_norm_le rows q hr hq M (N / Ideal.absNorm D) K hrows hqn hK
  apply FiniteSieveOperator.squared_norm_le_of_energy _ _ (highKernelNorm_nonneg _ _ _)
  intro a
  have hsum (i : m) : (∑ j, highQuotientMatrix D rows cols i j * a j) =
      ∑ j : S, canonicalQuadraticRow (q j) (primaryIdealGenerator (rows i).val) * a j.val := by
    calc
      _ = ∑ j ∈ S, highQuotientMatrix D rows cols i j * a j := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro j _ hj
        have hd : ¬ D ∣ (cols j).val := by
          simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and] using hj
        simp only [highQuotientMatrix, dif_neg hd, zero_mul]
      _ = ∑ j : S, highQuotientMatrix D rows cols i j.val * a j.val :=
        (Finset.sum_coe_sort (s := S) (f := fun j => highQuotientMatrix D rows cols i j * a j)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        simp only [highQuotientMatrix, dif_pos (hS j)]
        rfl
  simp_rw [hsum]
  have he := FiniteSieveOperator.energy_bound
    (fun i j => canonicalQuadraticRow (q j) (primaryIdealGenerator (rows i).val)) (fun j : S => a j.val)
  have hE : (∑ j : S, ‖a j.val‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 := by
    rw [Finset.sum_coe_sort (s := S) (f := fun j : n => ‖a j‖ ^ 2)]
    exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖a j‖)
  exact he.trans ((mul_le_mul_of_nonneg_right hb (by positivity)).trans
    (mul_le_mul_of_nonneg_left hE (highKernelNorm_nonneg _ _ _)))

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson
open Eisenstein

/-- Dividing by the exact common ideal makes the remaining conductors coprime. -/
lemma quadraticIdealQuotient_coprime_iff (D I J : Ideal O) (hD : D ≠ 0)
    (hI : D ∣ I) (hJ : D ∣ J) :
    quadraticIdealQuotient D I ⊔ quadraticIdealQuotient D J = ⊤ ↔ I ⊔ J = D := by
  have he : D * (quadraticIdealQuotient D I ⊔ quadraticIdealQuotient D J) = I ⊔ J := by
    rw [← Ideal.add_eq_sup, mul_add, quadraticIdeal_mul_quotient hI,
      quadraticIdeal_mul_quotient hJ, Ideal.add_eq_sup]
  constructor
  · intro h
    rw [h, ← Ideal.one_eq_top, mul_one] at he
    exact he.symm
  · intro h
    apply mul_left_cancel₀ hD
    rw [he, h, ← Ideal.one_eq_top, mul_one]

namespace CanonicalQuadraticSieve

/-- Common ideals partition all pairs of conductor columns. -/
def commonFactorPool {n : Type*} [Fintype n] (cols : n → QuadraticIdeal) : Finset (Ideal O) :=
  Finset.univ.image (fun p : n × n => (cols p.1).val ⊔ (cols p.2).val)

lemma mem_commonFactorPool {n : Type*} [Fintype n] (cols : n → QuadraticIdeal) (j k : n) :
    (cols j).val ⊔ (cols k).val ∈ commonFactorPool cols :=
  Finset.mem_image.mpr ⟨(j, k), Finset.mem_univ _, rfl⟩

lemma commonFactorPool_admissible {n : Type*} [Fintype n]
    (cols : n → QuadraticIdeal) (D : Ideal O) (hD : D ∈ commonFactorPool cols) :
    quadraticIdealAdmissible D := by
  obtain ⟨⟨j, k⟩, _, rfl⟩ := Finset.mem_image.mp hD
  exact quadraticIdealAdmissible_of_dvd (cols j).property (Ideal.dvd_iff_le.mpr le_sup_left)

/-- Gram entries with a prescribed common conductor ideal. -/
def commonFactorBlock {m n : Type*} [Fintype m] [Fintype n]
    (D : Ideal O) (rows : m → O) (cols : n → QuadraticIdeal) (a : n → ℂ) : ℂ :=
  ∑ i, ∑ j, ∑ k, if (cols j).val ⊔ (cols k).val = D then
    star (canonicalQuadraticRow (cols j) (rows i) * a j) *
      (canonicalQuadraticRow (cols k) (rows i) * a k) else 0

end CanonicalQuadraticSieve
end SchwartzPlanePoisson

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein

lemma energy_eq_commonFactorBlocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → O) (cols : n → QuadraticIdeal) (a : n → ℂ) :
    ((∑ i, ‖∑ j, canonicalQuadraticRow (cols j) (rows i) * a j‖ ^ 2 : ℝ) : ℂ) =
      ∑ D ∈ commonFactorPool cols, commonFactorBlock D rows cols a := by
  classical
  have hp (i : m) (j k : n) :
      (∑ D ∈ commonFactorPool cols, if (cols j).val ⊔ (cols k).val = D then
        star (canonicalQuadraticRow (cols j) (rows i) * a j) *
          (canonicalQuadraticRow (cols k) (rows i) * a k) else 0) =
        star (canonicalQuadraticRow (cols j) (rows i) * a j) *
          (canonicalQuadraticRow (cols k) (rows i) * a k) := by
    rw [Finset.sum_eq_single ((cols j).val ⊔ (cols k).val)]
    · exact if_pos rfl
    · intro D _ hD
      exact if_neg (Ne.symm hD)
    · exact fun h => (h (mem_commonFactorPool cols j k)).elim
  have hi (i : m) :
      (∑ D ∈ commonFactorPool cols, ∑ j, ∑ k, if (cols j).val ⊔ (cols k).val = D then
        star (canonicalQuadraticRow (cols j) (rows i) * a j) *
          (canonicalQuadraticRow (cols k) (rows i) * a k) else 0) =
      ∑ j, ∑ k, star (canonicalQuadraticRow (cols j) (rows i) * a j) *
        (canonicalQuadraticRow (cols k) (rows i) * a k) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun k _ => hp i j k)
  simp only [commonFactorBlock]
  rw [Finset.sum_comm]
  simp_rw [hi]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_mul_sum, ← star_sum]
  simpa only [Complex.star_def, Complex.ofReal_pow] using
    (Complex.conj_mul' (∑ j, canonicalQuadraticRow (cols j) (rows i) * a j)).symm

lemma energy_le_commonFactorBlocks {m n : Type*} [Fintype m] [Fintype n]
    (rows : m → O) (cols : n → QuadraticIdeal) (a : n → ℂ) :
    (∑ i, ‖∑ j, canonicalQuadraticRow (cols j) (rows i) * a j‖ ^ 2) ≤
      ∑ D ∈ commonFactorPool cols, ‖commonFactorBlock D rows cols a‖ := by
  have he := congrArg norm (energy_eq_commonFactorBlocks rows cols a)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at he
  rw [he]
  exact norm_sum_le _ _

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein

/-- Square factors occurring among rows above the squarefree-part threshold. -/
def highSquareParts (M K : ℝ) : Finset (Ideal O) :=
  (Finset.univ.filter (fun I : QuadraticSupportedRange M =>
    K < (Ideal.absNorm (quadraticSquarefreePart I.val.val) : ℝ))).image
      (fun I => quadraticSquarePart I.val.val)

lemma mem_highSquareParts {M K : ℝ} (I : QuadraticSupportedRange M)
    (hI : K < (Ideal.absNorm (quadraticSquarefreePart I.val.val) : ℝ)) :
    quadraticSquarePart I.val.val ∈ highSquareParts M K :=
  Finset.mem_image.mpr ⟨I, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI⟩, rfl⟩

/-- A high squarefree factor forces its complementary square factor below the reciprocal scale. -/
lemma highSquareParts_bounds (M K : ℝ) (hK : 0 < K) (B : Ideal O)
    (hB : B ∈ highSquareParts M K) :
    quadraticSupported B ∧ (1 : ℝ) ≤ Ideal.absNorm B ∧
      (Ideal.absNorm B : ℝ) ≤ Real.sqrt (M / K) ∧
      1 ≤ M / (Ideal.absNorm B : ℝ) ^ 2 := by
  obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hB
  have hiK := (Finset.mem_filter.mp hI).2
  have hI0 := primaryIdealGenerator_ne_zero_ideal I.val.val I.val.property.1
  have hp := (quadraticSupported_parts I.val.val hI0).mp I.val.property
  have hA0 := primaryIdealGenerator_ne_zero_ideal _ hp.1.1
  have hB0 := primaryIdealGenerator_ne_zero_ideal _ hp.2.1
  have hA : (1 : ℝ) ≤ Ideal.absNorm (quadraticSquarefreePart I.val.val) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hA0)
  have hB : (1 : ℝ) ≤ Ideal.absNorm (quadraticSquarePart I.val.val) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hB0)
  have hn := congrArg (fun J : Ideal O => (Ideal.absNorm J : ℝ))
    (quadraticParts_mul_square I.val.val hI0)
  simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow] at hn
  have hM0 : 0 ≤ M := (Nat.cast_nonneg _).trans I.property
  have hBsq : 0 < (Ideal.absNorm (quadraticSquarePart I.val.val) : ℝ) ^ 2 := by positivity
  refine ⟨hp.2, hB, ?_, ?_⟩
  · apply (sq_le_sq₀ (Nat.cast_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (div_nonneg hM0 hK.le)]
    apply (le_div_iff₀ hK).mpr
    have hmul := mul_le_mul_of_nonneg_right hiK.le hBsq.le
    nlinarith only [hmul, hn, I.property]
  · apply (le_div_iff₀ hBsq).mpr
    have hmul := mul_le_mul_of_nonneg_right hA hBsq.le
    nlinarith only [hmul, hn, I.property]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein

/-- Squarefree-square decomposition reduces the high kernel to ordinary quadratic sieve norms. -/
theorem highKernelNorm_le_squarePart_sum (M N K : ℝ) :
    highKernelNorm M N K ≤
      ∑ B ∈ highSquareParts M K, sieveNorm (M / (Ideal.absNorm B : ℝ) ^ 2) N := by
  classical
  apply FiniteSieveOperator.squared_norm_le_of_energy _ _
    (Finset.sum_nonneg (fun _ _ => sieveNorm_nonneg _ _))
  intro a
  let R (B : Ideal O) : Finset (QuadraticSupportedRange M) := Finset.univ.filter
    (fun I => K < (Ideal.absNorm (quadraticSquarefreePart I.val.val) : ℝ) ∧
      quadraticSquarePart I.val.val = B)
  let E (I : QuadraticSupportedRange M) : ℝ := ‖∑ J, highMatrix M N K I J * a J‖ ^ 2
  have hR (B : Ideal O) (I : R B) :
      K < (Ideal.absNorm (quadraticSquarefreePart I.val.val.val) : ℝ) ∧
      quadraticSquarePart I.val.val.val = B := (Finset.mem_filter.mp I.property).2
  have hpartition (I : QuadraticSupportedRange M) :
      E I = ∑ B ∈ highSquareParts M K, if I ∈ R B then E I else 0 := by
    by_cases hI : K < (Ideal.absNorm (quadraticSquarefreePart I.val.val) : ℝ)
    · rw [Finset.sum_eq_single (quadraticSquarePart I.val.val)]
      · rw [if_pos (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hI, rfl⟩)]
      · intro B _ hB
        exact if_neg (fun h => hB ((Finset.mem_filter.mp h).2.2).symm)
      · exact fun h => (h (mem_highSquareParts I hI)).elim
    · have hz : E I = 0 := by simp only [E, highMatrix, if_neg hI, zero_mul,
          Finset.sum_const_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
      simp only [hz, ite_self, Finset.sum_const_zero]
  have hsum : (∑ I, E I) = ∑ B ∈ highSquareParts M K, ∑ I ∈ R B, E I := by
    calc
      _ = ∑ I, ∑ B ∈ highSquareParts M K, if I ∈ R B then E I else 0 :=
        Finset.sum_congr rfl (fun I _ => hpartition I)
      _ = ∑ B ∈ highSquareParts M K, ∑ I, if I ∈ R B then E I else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro B _
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and, Finset.sum_filter]
  have hblock (B : Ideal O) (_hB : B ∈ highSquareParts M K) :
      (∑ I ∈ R B, E I) ≤ sieveNorm (M / (Ideal.absNorm B : ℝ) ^ 2) N * ∑ J, ‖a J‖ ^ 2 := by
    let r : R B → QuadraticIdeal := fun I => ⟨quadraticSquarefreePart I.val.val.val,
      ((quadraticSupported_parts I.val.val.val
        (primaryIdealGenerator_ne_zero_ideal _ I.val.val.property.1)).mp I.val.val.property).1⟩
    have hr : Function.Injective r := by
      intro I J he
      have hf := congrArg (fun A : QuadraticIdeal => A.val) he
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      rw [← quadraticParts_mul_square I.val.val.val
        (primaryIdealGenerator_ne_zero_ideal _ I.val.val.property.1),
        ← quadraticParts_mul_square J.val.val.val
        (primaryIdealGenerator_ne_zero_ideal _ J.val.val.property.1),
        (hR B I).2, (hR B J).2]
      exact congrArg (fun A : Ideal O => A * B ^ 2) hf
    have hrn (I : R B) : (Ideal.absNorm (r I).val : ℝ) ≤ M / (Ideal.absNorm B : ℝ) ^ 2 := by
      have hI0 := primaryIdealGenerator_ne_zero_ideal _ I.val.val.property.1
      have hp := (quadraticSupported_parts I.val.val.val hI0).mp I.val.val.property
      have hB0 : B ≠ 0 := (hR B I).2 ▸ primaryIdealGenerator_ne_zero_ideal _ hp.2.1
      have hb : 0 < (Ideal.absNorm B : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hB0)
      apply (le_div_iff₀ (sq_pos_of_pos hb)).mpr
      have hn := congrArg (fun A : Ideal O => (Ideal.absNorm A : ℝ))
        (quadraticParts_mul_square I.val.val.val hI0)
      simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow, (hR B I).2] at hn
      exact hn.trans_le I.val.property
    let b : QuadraticIdealRange N → ℂ := fun J => a J * quadraticIdealMask J.val (primaryIdealGenerator B)
    have hb (J : QuadraticIdealRange N) : ‖b J‖ ≤ ‖a J‖ := by
      have hm := canonicalQuadraticRow_norm_le_one J.val ((primaryIdealGenerator B) ^ 2)
      rw [canonicalQuadraticRow_square] at hm
      exact (norm_mul _ _).le.trans (mul_le_of_le_one_right (norm_nonneg _) hm)
    have he (I : R B) : (∑ J, highMatrix M N K I.val J * a J) =
        ∑ J, canonicalQuadraticRow J.val (primaryIdealGenerator (r I).val) * b J := by
      apply Finset.sum_congr rfl
      intro J _
      rw [highMatrix, if_pos (hR B I).1,
        ← quadraticParts_mul_square I.val.val.val
          (primaryIdealGenerator_ne_zero_ideal _ I.val.val.property.1), (hR B I).2,
        canonicalQuadraticRow_squarefree_argument]
      change (canonicalQuadraticRow J.val (primaryIdealGenerator (r I).val) *
        quadraticIdealMask J.val (primaryIdealGenerator B)) * a J = _
      dsimp only [b]
      ring
    have hop := family_squared_norm_le r (fun J : QuadraticIdealRange N => J.val)
      hr Subtype.val_injective (M / (Ideal.absNorm B : ℝ) ^ 2) N hrn (fun J => J.property)
    have hen := FiniteSieveOperator.energy_bound
      (fun I J => canonicalQuadraticRow J.val (primaryIdealGenerator (r I).val)) b
    rw [← Finset.sum_coe_sort (s := R B) (f := E)]
    change (∑ I : R B, ‖∑ J, highMatrix M N K I.val J * a J‖ ^ 2) ≤ _
    simp_rw [he]
    exact hen.trans ((mul_le_mul_of_nonneg_right hop (by positivity)).trans
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun J _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hb J) 2)) (sieveNorm_nonneg _ _)))
  change (∑ I, E I) ≤ _
  rw [hsum, Finset.sum_mul]
  exact Finset.sum_le_sum hblock

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein

lemma highSquareParts_card_bound (M K : ℝ) (hK : 0 < K) :
    ((highSquareParts M K).card : ℝ) ≤ diagonalControl sieveCutoff * Real.sqrt (M / K) := by
  have hD := diagonalControl_nonneg sieveCutoff
  by_cases he : highSquareParts M K = ∅
  · simp only [he, Finset.card_empty, Nat.cast_zero]
    positivity
  · obtain ⟨B, hB⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hb := highSquareParts_bounds M K hK B hB
    exact finite_ideal_card_bound _ _ (hb.2.1.trans hb.2.2.1)
      (fun A hA => (highSquareParts_bounds M K hK A hA).2.2.1)

/-- A sieve power bound controls the full high kernel with only the square-factor counting cost. -/
theorem HasSieveExponent.high_kernel {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℝ,
      1 ≤ M → 1 ≤ N → 1 ≤ K →
      highKernelNorm M N K ≤ C * (M * N) ^ ε * (M + Real.sqrt (M / K) * N ^ α) := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := h ε hε
  obtain ⟨A, hA, hsum⟩ := finite_inverse_norm_square_bound
  let D := diagonalControl sieveCutoff
  have hD : 0 ≤ D := diagonalControl_nonneg sieveCutoff
  refine ⟨(A + D + 1) * C, by positivity, ?_⟩
  intro M N K hM hN hK
  have hM0 := zero_le_one.trans hM
  have hN0 := zero_le_one.trans hN
  have hK0 := zero_lt_one.trans_le hK
  have hrow (B : Ideal O) (hB : B ∈ highSquareParts M K) :
      sieveNorm (M / (Ideal.absNorm B : ℝ) ^ 2) N ≤
        C * (M * N) ^ ε * (M / (Ideal.absNorm B : ℝ) ^ 2 + N ^ α) := by
    have hb := highSquareParts_bounds M K hK0 B hB
    have hquot : M / (Ideal.absNorm B : ℝ) ^ 2 ≤ M := div_le_self hM0 (one_le_pow₀ hb.2.1)
    apply (hbound _ N hb.2.2.2 hN).trans
    have hpow := Real.rpow_le_rpow
      (mul_nonneg (div_nonneg hM0 (sq_nonneg _)) hN0)
      (mul_le_mul_of_nonneg_right hquot hN0) hε.le
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le)
      (add_nonneg (div_nonneg hM0 (sq_nonneg _)) (Real.rpow_nonneg hN0 _))
  have hcard := highSquareParts_card_bound M K hK0
  have hcoeff : 0 ≤ C * (M * N) ^ ε := by positivity
  have hr : 0 ≤ Real.sqrt (M / K) * N ^ α :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hN0 _)
  calc
    _ ≤ ∑ B ∈ highSquareParts M K, sieveNorm (M / (Ideal.absNorm B : ℝ) ^ 2) N :=
      highKernelNorm_le_squarePart_sum M N K
    _ ≤ ∑ B ∈ highSquareParts M K,
        C * (M * N) ^ ε * (M / (Ideal.absNorm B : ℝ) ^ 2 + N ^ α) := Finset.sum_le_sum hrow
    _ = C * (M * N) ^ ε *
        (M * (∑ B ∈ highSquareParts M K, 1 / (Ideal.absNorm B : ℝ) ^ 2) +
          ((highSquareParts M K).card : ℝ) * N ^ α) := by
      simp only [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    _ ≤ C * (M * N) ^ ε * (M * A + (D * Real.sqrt (M / K)) * N ^ α) := by
      gcongr
      exact hsum _
    _ ≤ C * (M * N) ^ ε * ((A + D + 1) * (M + Real.sqrt (M / K) * N ^ α)) := by
      apply mul_le_mul_of_nonneg_left _ hcoeff
      calc
        M * A + (D * Real.sqrt (M / K)) * N ^ α = A * M + D * (Real.sqrt (M / K) * N ^ α) := by ring
        _ ≤ (A + D + 1) * M + (A + D + 1) * (Real.sqrt (M / K) * N ^ α) :=
          add_le_add (mul_le_mul_of_nonneg_right (by linarith) hM0)
            (mul_le_mul_of_nonneg_right (by linarith) hr)
        _ = _ := by ring
    _ = ((A + D + 1) * C) * (M * N) ^ ε * (M + Real.sqrt (M / K) * N ^ α) := by ring

end SchwartzPlanePoisson.CanonicalQuadraticSieve

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
