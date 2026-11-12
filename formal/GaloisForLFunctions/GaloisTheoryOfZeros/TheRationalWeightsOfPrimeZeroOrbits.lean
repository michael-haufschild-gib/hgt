import GaloisForLFunctions.GaloisTheoryOfZeros.ThePrimeReflectionKernelOfTheZeros

/-!
# Rational weights and arithmetic zero orbits

The Galois group of the complete prime trace extension acts faithfully on
all integral zero relations and fixes their rational weights. Rational prime
weights therefore descend to the trace ground field.

Every rational-real-part zero has exactly its complex-conjugate pair as
arithmetic orbit. Conjugating complex conjugation doubles any horizontal
orbit displacement, whereas the full orbit lies in the critical strip.
Consequently critical-line membership is arithmetic invariant. Reflection
pair fields and their Kummer discriminants give the corresponding field
and square-relation obstructions away from the line.
-/

noncomputable section
set_option autoImplicit false
open Complex Set RHTower
open scoped BigOperators
namespace GaloisForLFunctions.GaloisTheoryOfZeros

local notation "B" => primeTraceField
local notation "E" => primeTraceExtension
local notation "G" => (E ≃ₐ[B] E)
local notation "Δ" => rawZeroRelationGroup
local instance : IsGalois B E := ⟨⟩

/-- An actual zero in the integral zero relation group, independent of multiplicity. -/
def primeTraceSupportRoot (ρ : XiDivisorSupport) : Δ := rawZeroRelationRoot (primeTraceSupportCopy ρ)

/-- Every integral exponent has its actual prime value inside the spectral extension. -/
def primeTraceExponentValue (p : Nat.Primes) (z : Δ) : E :=
  ⟨zeroPrimeEigenvalue p z,primeEigenvalue_mem_spectralField p p.2 z⟩

theorem primeTraceExponentValue_coe (p : Nat.Primes) (z : Δ) :
    (primeTraceExponentValue p z : ℂ) = Complex.exp ((Real.log (p : ℕ) : ℂ)*(z : ℂ)) := rfl

theorem primeTraceExponentValue_root (p : Nat.Primes) (ρ : XiDivisorSupport) :
    primeTraceExponentValue p (primeTraceSupportRoot ρ) = primeResidueValue p ρ := by
  apply Subtype.ext
  exact (primeResidueValue_coe p ρ).symm

private theorem exponent_value_zero (p : Nat.Primes) : primeTraceExponentValue p 0 = 1 := by
  apply Subtype.ext
  change Complex.exp ((Real.log (p : ℕ) : ℂ)*0) = 1
  rw [mul_zero,Complex.exp_zero]

private theorem exponent_value_add (p : Nat.Primes) (z w : Δ) :
    primeTraceExponentValue p (z+w) = primeTraceExponentValue p z * primeTraceExponentValue p w := by
  apply Subtype.ext
  change Complex.exp ((Real.log (p : ℕ) : ℂ)*((z : ℂ)+(w : ℂ))) = _
  rw [mul_add,Complex.exp_add]
  rfl

private theorem exponent_value_neg (p : Nat.Primes) (z : Δ) :
    primeTraceExponentValue p (-z) = (primeTraceExponentValue p z)⁻¹ := by
  apply Subtype.ext
  change Complex.exp ((Real.log (p : ℕ) : ℂ)*(-(z : ℂ))) = _
  rw [mul_neg,Complex.exp_neg]
  rfl

private theorem exponent_values_ext {z w : Δ}
    (h : ∀ p : Nat.Primes, primeTraceExponentValue p z = primeTraceExponentValue p w) : z=w := by
  apply Subtype.ext
  apply two_prime_exponential_injective Nat.prime_two Nat.prime_three (by decide)
  exact Prod.ext
    (congrArg (fun x : E => (x : ℂ)) (h ⟨2,Nat.prime_two⟩))
    (congrArg (fun x : E => (x : ℂ)) (h ⟨3,Nat.prime_three⟩))

/-- Applying an arithmetic automorphism preserves the complete prime spectrum on the integral span. -/
theorem primeTraceExponent_image (σ : G) (z : Δ) :
    ∃ w : Δ, ∀ p : Nat.Primes, primeTraceExponentValue p w = σ (primeTraceExponentValue p z) := by
  have hh : ∀ x : ℂ, ∀ hx : x ∈ Δ,
      ∃ w : Δ, ∀ p : Nat.Primes, primeTraceExponentValue p w = σ (primeTraceExponentValue p ⟨x,hx⟩) := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨q,rfl⟩ := hx
      refine ⟨primeTraceSupportRoot (primeTraceZeroMap σ q.1),?_⟩
      intro p
      change primeTraceExponentValue p (primeTraceSupportRoot (primeTraceZeroMap σ q.1)) =
        σ (primeTraceExponentValue p (primeTraceSupportRoot q.1))
      rw [primeTraceExponentValue_root,primeTraceExponentValue_root,primeResidueValue_map]
    | zero =>
      refine ⟨0,?_⟩
      intro p
      change primeTraceExponentValue p 0 = σ (primeTraceExponentValue p 0)
      rw [exponent_value_zero,map_one]
    | add x y hx hy ihx ihy =>
      obtain ⟨a,ha⟩ := ihx
      obtain ⟨b,hb⟩ := ihy
      refine ⟨a+b,?_⟩
      intro p
      change primeTraceExponentValue p (a+b) =
        σ (primeTraceExponentValue p (⟨x,hx⟩+⟨y,hy⟩))
      rw [exponent_value_add,exponent_value_add,map_mul,ha p,hb p]
    | neg x hx ih =>
      obtain ⟨a,ha⟩ := ih
      refine ⟨-a,?_⟩
      intro p
      change primeTraceExponentValue p (-a) = σ (primeTraceExponentValue p (-⟨x,hx⟩))
      rw [exponent_value_neg,exponent_value_neg,map_inv₀,ha p]
  exact hh z z.property

private def exponentImage (σ : G) (z : Δ) : Δ := Classical.choose (primeTraceExponent_image σ z)

private theorem exponentImage_value (σ : G) (z : Δ) (p : Nat.Primes) :
    primeTraceExponentValue p (exponentImage σ z) = σ (primeTraceExponentValue p z) :=
  Classical.choose_spec (primeTraceExponent_image σ z) p

/-- The actual Galois action extends to every integral zero relation. -/
def primeTraceExponentHom (σ : G) : Δ →+ Δ where
  toFun := exponentImage σ
  map_zero' := by
    apply exponent_values_ext
    intro p
    rw [exponentImage_value,exponent_value_zero,map_one]
  map_add' z w := by
    apply exponent_values_ext
    intro p
    rw [exponentImage_value,exponent_value_add,exponent_value_add,
      exponentImage_value,exponentImage_value,map_mul]

theorem primeTraceExponentHom_value (σ : G) (p : Nat.Primes) (z : Δ) :
    primeTraceExponentValue p (primeTraceExponentHom σ z) = σ (primeTraceExponentValue p z) :=
  exponentImage_value σ z p

theorem primeTraceExponentHom_root (σ : G) (ρ : XiDivisorSupport) :
    primeTraceExponentHom σ (primeTraceSupportRoot ρ) = primeTraceSupportRoot (primeTraceZeroMap σ ρ) := by
  apply exponent_values_ext
  intro p
  rw [primeTraceExponentHom_value,primeTraceExponentValue_root,
    primeTraceExponentValue_root,primeResidueValue_map]

theorem primeTraceExponentHom_id (z : Δ) : primeTraceExponentHom 1 z = z := by
  apply exponent_values_ext
  intro p
  rw [primeTraceExponentHom_value]
  rfl

theorem primeTraceExponentHom_mul (σ τ : G) (z : Δ) :
    primeTraceExponentHom (σ*τ) z = primeTraceExponentHom σ (primeTraceExponentHom τ z) := by
  apply exponent_values_ext
  intro p
  rw [primeTraceExponentHom_value,primeTraceExponentHom_value,primeTraceExponentHom_value]
  rfl

/-- Arithmetic automorphisms act by additive automorphisms of the complete relation group. -/
def primeTraceExponentEquiv (σ : G) : Δ ≃+ Δ where
  __ := primeTraceExponentHom σ
  invFun := primeTraceExponentHom σ⁻¹
  left_inv z := by
    change primeTraceExponentHom σ⁻¹ (primeTraceExponentHom σ z) = z
    rw [← primeTraceExponentHom_mul,inv_mul_cancel,primeTraceExponentHom_id]
  right_inv z := by
    change primeTraceExponentHom σ (primeTraceExponentHom σ⁻¹ z) = z
    rw [← primeTraceExponentHom_mul,mul_inv_cancel,primeTraceExponentHom_id]

/-- The integral character group of the zero motive carries a faithful arithmetic representation. -/
def primeTraceExponentRepresentation : G →* Multiplicative (AddAut Δ) where
  toFun σ := Multiplicative.ofAdd (primeTraceExponentEquiv σ)
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    intro z
    exact primeTraceExponentHom_id z
  map_mul' σ τ := by
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    intro z
    exact primeTraceExponentHom_mul σ τ z

theorem primeTraceExponentRepresentation_injective : Function.Injective primeTraceExponentRepresentation := by
  intro σ τ h
  apply primeTraceGaloisAction_injective
  apply Equiv.ext
  intro ρ
  have he := congrArg (fun a : Multiplicative (AddAut Δ) => a.toAdd (primeTraceSupportRoot ρ)) h
  change primeTraceExponentHom σ (primeTraceSupportRoot ρ) = primeTraceExponentHom τ (primeTraceSupportRoot ρ) at he
  rw [primeTraceExponentHom_root,primeTraceExponentHom_root] at he
  exact Subtype.ext (congrArg (fun z : Δ => (z : ℂ)) he)

private theorem exponent_value_unit (p : Nat.Primes) :
    primeTraceExponentValue p (rationalZeroOne : Δ) = (p : ℕ) := by
  apply Subtype.ext
  change Complex.exp ((Real.log (p : ℕ) : ℂ)*1) = (p : ℕ)
  rw [mul_one,GaloisForLFunctions.RHTower.SixExponentials.exp_log_nat p.2.pos]

/-- The central unit weight is fixed by every arithmetic automorphism. -/
theorem primeTraceExponentHom_one (σ : G) :
    primeTraceExponentHom σ (rationalZeroOne : Δ) = rationalZeroOne := by
  apply exponent_values_ext
  intro p
  rw [primeTraceExponentHom_value,exponent_value_unit,map_natCast]

/-- Every rational weight in the integral zero span is fixed, including its denominators. -/
theorem primeTraceExponentHom_rational (σ : G) (z : rationalZeroSubgroup) :
    primeTraceExponentHom σ (z : Δ) = z := by
  obtain ⟨n,hn,m,he⟩ := rationalZero_denominator z
  have hrel : n • (z : Δ) = m • (rationalZeroOne : Δ) :=
    congrArg (fun x : rationalZeroSubgroup => (x : Δ)) he
  have ht : n • primeTraceExponentHom σ (z : Δ) = n • (z : Δ) := by
    calc
      n • primeTraceExponentHom σ (z : Δ) = primeTraceExponentHom σ (n • (z : Δ)) := (map_nsmul _ n _).symm
      _ = primeTraceExponentHom σ (m • (rationalZeroOne : Δ)) := by rw [hrel]
      _ = m • (rationalZeroOne : Δ) := by rw [map_zsmul,primeTraceExponentHom_one]
      _ = n • (z : Δ) := hrel.symm
  apply Subtype.ext
  have hc := congrArg (fun w : Δ => (w : ℂ)) ht
  change n • ((primeTraceExponentHom σ (z : Δ)) : ℂ) = n • ((z : Δ) : ℂ) at hc
  simp only [nsmul_eq_mul] at hc
  exact mul_left_cancel₀ (by exact_mod_cast Nat.ne_of_gt hn) hc

/-- Prime values of all rational zero weights already belong to the complete trace ground field. -/
theorem rationalPrimeSpectralField_le_traceField : rationalPrimeSpectralField ≤ B := by
  apply Subfield.closure_le.mpr
  rintro x ⟨⟨p,z⟩,rfl⟩
  have hf : ∀ σ : G, σ (primeTraceExponentValue p (z : Δ)) = primeTraceExponentValue p (z : Δ) := by
    intro σ
    rw [← primeTraceExponentHom_value,primeTraceExponentHom_rational]
  obtain ⟨b,hb⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (primeTraceExponentValue p (z : Δ))).mpr hf
  have he : (b : ℂ) = zeroPrimeEigenvalue p (z : Δ) := congrArg (fun v : E => (v : ℂ)) hb
  change zeroPrimeEigenvalue p (z : Δ) ∈ B
  rw [← he]
  exact b.property

/-- Functional reflection adds the central unit and negates the zero generator. -/
theorem primeTraceSupportRoot_reflection (ρ : XiDivisorSupport) :
    primeTraceSupportRoot (xiZeroReflectEquiv ρ) = (rationalZeroOne : Δ) - primeTraceSupportRoot ρ := by
  apply Subtype.ext
  rfl

/-- Ordinary conjugation gives the usual conjugation action on every integral zero relation. -/
theorem primeTraceExponentHom_conjugation (z : Δ) :
    primeTraceExponentHom primeTraceConjugation z = rawZeroConjugation z := by
  apply exponent_values_ext
  intro p
  rw [primeTraceExponentHom_value]
  apply Subtype.ext
  change starRingEnd ℂ (Complex.exp ((Real.log (p : ℕ) : ℂ)*(z : ℂ))) =
    Complex.exp ((Real.log (p : ℕ) : ℂ)*(starRingEnd ℂ (z : ℂ)))
  rw [← Complex.exp_conj,map_mul,Complex.conj_ofReal]

/-- The complete arithmetic action preserves the absolute ordinate. -/
theorem primeTraceZeroMap_height (σ : G) (ρ : XiDivisorSupport) :
    |(primeTraceZeroMap σ ρ : ℂ).im| = |(ρ : ℂ).im| :=
  primeTraceEmbeddingZero_height ((IntermediateField.val E).comp σ.toAlgHom) ρ

private theorem rational_pair_weight (ρ : XiDivisorSupport)
    (hr : ∃ r : ℚ, (ρ : ℂ).re=(r : ℝ)) :
    primeTraceSupportRoot ρ + primeTraceSupportRoot (xiZeroConjEquiv ρ) ∈ rationalZeroSubgroup := by
  obtain ⟨r,hr⟩ := hr
  apply (mem_rationalZeroSubgroup _).mpr
  refine ⟨2*r,?_⟩
  change (ρ : ℂ)+starRingEnd ℂ (ρ : ℂ) = ((2*r : ℚ) : ℂ)
  apply Complex.ext
  · simp only [Complex.add_re,Complex.conj_re,Complex.ratCast_re]
    push_cast
    rw [hr]
    ring
  · simp only [Complex.add_im,Complex.conj_im,Complex.ratCast_im,add_neg_cancel]

private theorem bounded_doubling_zero (S : Set ℝ) (hS : S.Nonempty) (hB : BddAbove S)
    (hd : ∀ x ∈ S, 2*x ∈ S) (hn : ∀ x ∈ S, 0≤x) : ∀ x ∈ S, x=0 := by
  have hu : sSup S ≤ sSup S / 2 := by
    apply csSup_le hS
    intro x hx
    have he := le_csSup hB (hd x hx)
    linarith only [he]
  intro x hx
  have hx' := le_csSup hB hx
  exact le_antisymm (by linarith only [hu,hx']) (hn x hx)

/-- Rational real parts are preserved throughout every arithmetic orbit. -/
theorem primeTraceZeroMap_rational_real_part (ρ : XiDivisorSupport)
    (hr : ∃ r : ℚ, (ρ : ℂ).re=(r : ℝ)) (σ : G) :
    (primeTraceZeroMap σ ρ : ℂ).re = (ρ : ℂ).re := by
  let q : Δ := primeTraceSupportRoot ρ + primeTraceSupportRoot (xiZeroConjEquiv ρ)
  have hqfix (τ : G) : primeTraceExponentHom τ q = q :=
    primeTraceExponentHom_rational τ ⟨q,rational_pair_weight ρ hr⟩
  let S : Set ℝ := Set.range (fun τ : G => |(primeTraceZeroMap τ ρ : ℂ).re-(ρ : ℂ).re|)
  have hS : S.Nonempty := ⟨_,1,rfl⟩
  have hB : BddAbove S := by
    refine ⟨1,?_⟩
    rintro x ⟨τ,rfl⟩
    have ha := xi_divisor_support_re_mem_open_unit (primeTraceZeroMap τ ρ)
    have hb := xi_divisor_support_re_mem_open_unit ρ
    apply le_of_lt
    apply abs_lt.mpr
    constructor <;> linarith only [ha.1,ha.2,hb.1,hb.2]
  -- Conjugating complex conjugation doubles each horizontal displacement.
  have hd : ∀ x ∈ S, 2*x ∈ S := by
    rintro x ⟨τ,rfl⟩
    let ζ := primeTraceZeroMap τ⁻¹ ρ
    have hinv : primeTraceZeroMap τ ζ = ρ := by
      dsimp only [ζ]
      rw [← primeTraceZeroMap_mul,mul_inv_cancel,primeTraceZeroMap_one]
    have he : primeTraceSupportRoot (primeTraceZeroMap (τ*primeTraceConjugation*τ⁻¹) ρ) =
        primeTraceExponentHom τ (primeTraceSupportRoot (xiZeroConjEquiv ζ)) := by
      rw [primeTraceExponentHom_root]
      congr 1
      rw [primeTraceZeroMap_mul,primeTraceZeroMap_mul,primeTraceZeroMap_conjugation]
    refine ⟨τ*primeTraceConjugation*τ⁻¹,?_⟩
    change |(primeTraceZeroMap (τ*primeTraceConjugation*τ⁻¹) ρ : ℂ).re-(ρ : ℂ).re| =
      2*|(primeTraceZeroMap τ ρ : ℂ).re-(ρ : ℂ).re|
    rcases abs_eq_abs.mp (primeTraceZeroMap_height τ⁻¹ ρ) with hi | hi
    · have hc : primeTraceSupportRoot (xiZeroConjEquiv ζ) =
          primeTraceSupportRoot ζ-(2 • primeTraceSupportRoot ρ-q) := by
        apply Subtype.ext
        change starRingEnd ℂ (ζ : ℂ) =
          (ζ : ℂ)-(2 • (ρ : ℂ)-((ρ : ℂ)+starRingEnd ℂ (ρ : ℂ)))
        apply Complex.ext
        · simp only [two_nsmul,Complex.sub_re,Complex.add_re,Complex.conj_re]
          ring
        · change (ζ : ℂ).im=(ρ : ℂ).im at hi
          simp only [two_nsmul,Complex.sub_im,Complex.add_im,Complex.conj_im]
          linarith only [hi]
      rw [hc,map_sub,map_sub,map_nsmul,primeTraceExponentHom_root,
        primeTraceExponentHom_root,hqfix,hinv] at he
      have hre := congrArg (fun z : Δ => (z : ℂ).re) he
      change (primeTraceZeroMap (τ*primeTraceConjugation*τ⁻¹) ρ : ℂ).re =
        ((ρ : ℂ)-(2 • (primeTraceZeroMap τ ρ : ℂ)-((ρ : ℂ)+starRingEnd ℂ (ρ : ℂ)))).re at hre
      simp only [two_nsmul,Complex.sub_re,Complex.add_re,Complex.conj_re] at hre
      have hd' : (primeTraceZeroMap (τ*primeTraceConjugation*τ⁻¹) ρ : ℂ).re-(ρ : ℂ).re =
          -(2*((primeTraceZeroMap τ ρ : ℂ).re-(ρ : ℂ).re)) := by linarith only [hre]
      rw [hd',abs_neg,abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    · have hc : primeTraceSupportRoot (xiZeroConjEquiv ζ) =
          primeTraceSupportRoot ζ+(2 • primeTraceSupportRoot ρ-q) := by
        apply Subtype.ext
        change starRingEnd ℂ (ζ : ℂ) =
          (ζ : ℂ)+(2 • (ρ : ℂ)-((ρ : ℂ)+starRingEnd ℂ (ρ : ℂ)))
        apply Complex.ext
        · simp only [two_nsmul,Complex.sub_re,Complex.add_re,Complex.conj_re]
          ring
        · change (ζ : ℂ).im= -(ρ : ℂ).im at hi
          simp only [two_nsmul,Complex.sub_im,Complex.add_im,Complex.conj_im]
          linarith only [hi]
      rw [hc,map_add,map_sub,map_nsmul,primeTraceExponentHom_root,
        primeTraceExponentHom_root,hqfix,hinv] at he
      have hre := congrArg (fun z : Δ => (z : ℂ).re) he
      change (primeTraceZeroMap (τ*primeTraceConjugation*τ⁻¹) ρ : ℂ).re =
        ((ρ : ℂ)+(2 • (primeTraceZeroMap τ ρ : ℂ)-((ρ : ℂ)+starRingEnd ℂ (ρ : ℂ)))).re at hre
      simp only [two_nsmul,Complex.sub_re,Complex.add_re,Complex.conj_re] at hre
      have hd' : (primeTraceZeroMap (τ*primeTraceConjugation*τ⁻¹) ρ : ℂ).re-(ρ : ℂ).re =
          2*((primeTraceZeroMap τ ρ : ℂ).re-(ρ : ℂ).re) := by linarith only [hre]
      rw [hd',abs_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  have hn : ∀ x ∈ S, 0≤x := by
    rintro x ⟨τ,rfl⟩
    exact abs_nonneg _
  exact sub_eq_zero.mp (abs_eq_zero.mp (bounded_doubling_zero S hS hB hd hn _ ⟨σ,rfl⟩))

/-- The complete orbit of a rational-real-part zero consists only of it and its complex conjugate. -/
theorem primeTraceZeroMap_rational_orbit (ρ : XiDivisorSupport)
    (hr : ∃ r : ℚ, (ρ : ℂ).re=(r : ℝ)) (σ : G) :
    primeTraceZeroMap σ ρ = ρ ∨ primeTraceZeroMap σ ρ = xiZeroConjEquiv ρ := by
  have hre := primeTraceZeroMap_rational_real_part ρ hr σ
  rcases abs_eq_abs.mp (primeTraceZeroMap_height σ ρ) with hi | hi
  · exact Or.inl (Subtype.ext (Complex.ext hre hi))
  · exact Or.inr (Subtype.ext (Complex.ext hre hi))

/-- Critical-line membership is invariant under every arithmetic automorphism. -/
theorem primeTraceZeroMap_critical_iff (σ : G) (ρ : XiDivisorSupport) :
    (primeTraceZeroMap σ ρ : ℂ).re=1/2 ↔ (ρ : ℂ).re=1/2 := by
  constructor
  · intro h
    have he := primeTraceZeroMap_rational_real_part (primeTraceZeroMap σ ρ)
      ⟨1/2,by simpa using h⟩ σ⁻¹
    rw [← primeTraceZeroMap_mul,inv_mul_cancel,primeTraceZeroMap_one] at he
    exact he.trans h
  · intro h
    exact (primeTraceZeroMap_rational_real_part ρ ⟨1/2,by simpa using h⟩ σ).trans h

private theorem conjugation_reflects_critical (ρ : XiDivisorSupport) (h : (ρ : ℂ).re=1/2) :
    primeTraceZeroMap primeTraceConjugation ρ = xiZeroReflectEquiv ρ := by
  rw [primeTraceZeroMap_conjugation]
  apply Subtype.ext
  apply Complex.ext
  · change (starRingEnd ℂ (ρ : ℂ)).re = (1-(ρ : ℂ)).re
    simp only [Complex.conj_re,Complex.sub_re,Complex.one_re]
    linarith only [h]
  · change (starRingEnd ℂ (ρ : ℂ)).im = (1-(ρ : ℂ)).im
    simp only [Complex.conj_im,Complex.sub_im,Complex.one_im,zero_sub]

/-- A rational-real-part zero is arithmetically conjugate to its functional reflection exactly on the line. -/
theorem primeReflectionOrbit_rational_iff (ρ : XiDivisorSupport) :
    ((∃ σ : G, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ) ∧
      ∃ r : ℚ, (ρ : ℂ).re=(r : ℝ)) ↔ (ρ : ℂ).re=1/2 := by
  constructor
  · rintro ⟨⟨σ,hσ⟩,r,hr⟩
    have he := primeTraceZeroMap_rational_real_part ρ ⟨r,hr⟩ σ
    rw [hσ] at he
    change (1-(ρ : ℂ)).re=(ρ : ℂ).re at he
    simp only [Complex.sub_re,Complex.one_re] at he
    linarith only [he]
  · intro h
    exact ⟨⟨primeTraceConjugation,conjugation_reflects_critical ρ h⟩,1/2,by simpa using h⟩

/-- Among rational real parts, the reflection-pair extension is quadratic precisely on the line. -/
theorem primeResidueOverPair_rational_degree_iff (ρ : XiDivisorSupport) :
    (Module.finrank (primePairField ρ) (primeResidueOverPair ρ) = 2 ∧
      ∃ r : ℚ, (ρ : ℂ).re=(r : ℝ)) ↔ (ρ : ℂ).re=1/2 := by
  rw [primeResidueOverPair_degree_two_iff,primeReflectionOrbit_rational_iff]

/-- A rational-real-part zero off the line has no nontrivial reflection-pair quadratic step. -/
theorem primePairField_eq_residue_of_rational_offline (ρ : XiDivisorSupport)
    (hr : ∃ r : ℚ, (ρ : ℂ).re=(r : ℝ)) (hoff : (ρ : ℂ).re ≠ 1/2) :
    primePairField ρ = primeResidueField ρ := by
  apply (primePairField_eq_residue_iff ρ).mpr
  intro h
  exact hoff ((primeReflectionOrbit_rational_iff ρ).mp ⟨h,hr⟩)

/-- A nontrivial reflection orbit off the line forces an irrational real part. -/
theorem primeReflectionOrbit_irrational_offline (ρ : XiDivisorSupport)
    (horbit : ∃ σ : G, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ)
    (hoff : (ρ : ℂ).re ≠ 1/2) : ¬ ∃ r : ℚ, (ρ : ℂ).re=(r : ℝ) :=
  fun hr => hoff ((primeReflectionOrbit_rational_iff ρ).mp ⟨horbit,hr⟩)

/-- A global arithmetic reflection lift would force every off-line real part to be irrational. -/
theorem primeFunctionalReflection_irrational_offline (σ : G)
    (hσ : ∀ ρ : XiDivisorSupport, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ)
    (ρ : XiDivisorSupport) (hoff : (ρ : ℂ).re ≠ 1/2) :
    ¬ ∃ r : ℚ, (ρ : ℂ).re=(r : ℝ) :=
  primeReflectionOrbit_irrational_offline ρ ⟨σ,hσ ρ⟩ hoff

/-- Off the line, reflection-orbit membership excludes two independent algebraic prime relations. -/
theorem primeReflectionOrbit_relations_dependent (ρ : XiDivisorSupport)
    (horbit : ∃ σ : G, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ)
    (hoff : (ρ : ℂ).re ≠ 1/2) (m n : Nat.Primes →₀ ℤ)
    (hm : m ∈ algebraicPrimeRelations (ρ : ℂ))
    (hn : n ∈ algebraicPrimeRelations (ρ : ℂ)) : ¬ PrimeRelationsIndependent m n :=
  algebraicPrimeRelations_two_dependent (ρ : ℂ) (xi_divisor_support_im_ne_zero ρ)
    (primeReflectionOrbit_irrational_offline ρ horbit hoff) m n hm hn

/-- At an off-line reflection orbit, one relation support contains every algebraic prime monomial. -/
theorem primeReflectionOrbit_relations_single_support (ρ : XiDivisorSupport)
    (horbit : ∃ σ : G, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ)
    (hoff : (ρ : ℂ).re ≠ 1/2) :
    ∃ m ∈ algebraicPrimeRelations (ρ : ℂ),
      ∀ n ∈ algebraicPrimeRelations (ρ : ℂ), n.support ⊆ m.support :=
  algebraicPrimeRelations_irrational_finite_support (ρ : ℂ) (xi_divisor_support_im_ne_zero ρ)
    (primeReflectionOrbit_irrational_offline ρ horbit hoff)

/-- Two algebraic prime values force a reflection-conjugate zero onto the critical line. -/
theorem primeReflectionOrbit_two_algebraic_values_critical (ρ : XiDivisorSupport)
    (horbit : ∃ σ : G, primeTraceZeroMap σ ρ = xiZeroReflectEquiv ρ)
    (p q : Nat.Primes) (hpq : p ≠ q)
    (hp : IsAlgebraic ℚ (primeResidueValue p ρ : ℂ))
    (hq : IsAlgebraic ℚ (primeResidueValue q ρ : ℂ)) : (ρ : ℂ).re=1/2 := by
  apply (primeReflectionOrbit_rational_iff ρ).mp
  refine ⟨horbit,zero_two_algebraic_prime_values_real_rational (primeTraceSupportCopy ρ) p q hpq ?_ ?_⟩
  · change IsAlgebraic ℚ (Complex.exp ((ρ : ℂ)*(Real.log (p : ℕ) : ℂ)))
    simpa only [primeResidueValue_coe,mul_comm] using hp
  · change IsAlgebraic ℚ (Complex.exp ((ρ : ℂ)*(Real.log (q : ℕ) : ℂ)))
    simpa only [primeResidueValue_coe,mul_comm] using hq

/-- At a rational real part off the line, each reflection difference already lies in the pair field. -/
theorem primeReflectionDifference_mem_pair_of_rational_offline (p : Nat.Primes)
    (ρ : XiDivisorSupport) (hr : ∃ r : ℚ, (ρ : ℂ).re=(r : ℝ))
    (hoff : (ρ : ℂ).re ≠ 1/2) : primeReflectionDifference p ρ ∈ primePairField ρ := by
  rw [primePairField_eq_residue_of_rational_offline ρ hr hoff]
  apply (primeResidueField ρ).sub_mem (primeResidueValue_mem p ρ)
  rw [← primeResidueField_reflection ρ]
  exact primeResidueValue_mem p (xiZeroReflectEquiv ρ)

/-- A rational off-line zero makes its reflection discriminant a square in the global pair field. -/
theorem primeReflectionRadicand_square_of_rational_offline (i : NonzeroPrimeReflection)
    (hr : ∃ r : ℚ, (i.val.2 : ℂ).re=(r : ℝ)) (hoff : (i.val.2 : ℂ).re ≠ 1/2) :
    IsSquare (primeReflectionRadicand i) := by
  have hm : primeReflectionRadical i ∈ primeReflectionField :=
    primePairField_le_reflectionField i.val.2
      (primeReflectionDifference_mem_pair_of_rational_offline i.val.1 i.val.2 hr hoff)
  refine ⟨⟨primeReflectionRadical i,hm⟩,?_⟩
  apply Subtype.ext
  change primeReflectionRadical i ^ 2 = primeReflectionRadical i * primeReflectionRadical i
  exact pow_two _

/-- Every prime reflection difference is nonzero at an off-line zero. -/
theorem primeReflectionDifference_ne_zero_of_offline (p : Nat.Primes)
    (ρ : XiDivisorSupport) (hoff : (ρ : ℂ).re ≠ 1/2) : primeReflectionDifference p ρ ≠ 0 := by
  intro he
  have hv := congrArg (fun x : E => (x : ℂ)) (sub_eq_zero.mp he)
  simp only [primeResidueValue_coe] at hv
  have hn := congrArg norm hv
  rw [Complex.norm_exp,Complex.norm_exp] at hn
  have hre := Real.exp_injective hn
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hre
  have h := mul_left_cancel₀ (Real.log_pos (by exact_mod_cast p.2.one_lt)).ne' hre
  change (ρ : ℂ).re = (1-(ρ : ℂ)).re at h
  simp only [Complex.sub_re,Complex.one_re] at h
  apply hoff
  linarith only [h]

/-- A rational off-line zero supplies a singleton odd square relation, obstructing uniform reflection. -/
theorem primeReflection_rational_offline_odd_square_relation (ρ : XiDivisorSupport)
    (hr : ∃ r : ℚ, (ρ : ℂ).re=(r : ℝ)) (hoff : (ρ : ℂ).re ≠ 1/2) :
    ∃ S : Finset NonzeroPrimeReflection,
      IsSquare (∏ i ∈ S, primeReflectionRadicand i) ∧ ¬ Even S.card := by
  classical
  let i : NonzeroPrimeReflection :=
    ⟨(⟨2,Nat.prime_two⟩,ρ),primeReflectionDifference_ne_zero_of_offline _ ρ hoff⟩
  refine ⟨{i},?_,?_⟩
  · simpa only [Finset.prod_singleton] using
      primeReflectionRadicand_square_of_rational_offline i hr hoff
  · simp

/-- The reflection-pair field is the trace ground field exactly at critical zeros. -/
theorem primePairField_eq_bot_iff_critical (ρ : XiDivisorSupport) :
    primePairField ρ = ⊥ ↔ (ρ : ℂ).re=1/2 := by
  constructor
  · intro h
    apply (primePairField_real_iff ρ).mp
    intro x hx
    rw [h,IntermediateField.mem_bot] at hx
    obtain ⟨b,rfl⟩ := hx
    exact primeTraceField_real b b.property
  · intro h
    apply le_antisymm _ bot_le
    intro x hx
    rw [IntermediateField.mem_bot]
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr
    intro σ
    apply (IntermediateField.mem_fixingSubgroup_iff _ _).mp
      ((primePairField_fixing σ ρ).mpr ?_) x hx
    rcases primeTraceZeroMap_rational_orbit ρ ⟨1/2,by simpa using h⟩ σ with hs | hs
    · exact Or.inl hs
    · right
      have hc := conjugation_reflects_critical ρ h
      rw [primeTraceZeroMap_conjugation] at hc
      exact hs.trans hc

/-- Critical zeros form complete arithmetic orbits; any orbit meeting the line lies on it. -/
theorem primeTraceOrbit_meets_critical_iff (ρ : XiDivisorSupport) :
    (∃ σ : G, (primeTraceZeroMap σ ρ : ℂ).re=1/2) ↔ (ρ : ℂ).re=1/2 := by
  constructor
  · rintro ⟨σ,h⟩
    exact (primeTraceZeroMap_critical_iff σ ρ).mp h
  · intro h
    exact ⟨1,by rwa [primeTraceZeroMap_one]⟩

/-- Both conjugate zeros occur, and they exhaust every rational-real-part arithmetic orbit. -/
theorem primeTraceZeroMap_rational_orbit_iff (ρ ζ : XiDivisorSupport)
    (hr : ∃ r : ℚ, (ρ : ℂ).re=(r : ℝ)) :
    (∃ σ : G, primeTraceZeroMap σ ρ = ζ) ↔ ζ=ρ ∨ ζ=xiZeroConjEquiv ρ := by
  constructor
  · rintro ⟨σ,rfl⟩
    exact primeTraceZeroMap_rational_orbit ρ hr σ
  · intro h
    rcases h with h | h
    · exact ⟨1,(primeTraceZeroMap_one ρ).trans h.symm⟩
    · exact ⟨primeTraceConjugation,(primeTraceZeroMap_conjugation ρ).trans h.symm⟩

/-- The global reflection-pair field collapses to the trace field precisely when all zeros are critical. -/
theorem primeReflectionField_eq_bot_iff_critical :
    primeReflectionField = ⊥ ↔ ∀ ρ : XiDivisorSupport, (ρ : ℂ).re=1/2 := by
  constructor
  · intro h ρ
    apply (primePairField_eq_bot_iff_critical ρ).mp
    apply le_antisymm _ bot_le
    calc
      primePairField ρ ≤ primeReflectionField := primePairField_le_reflectionField ρ
      _ = ⊥ := h
  · intro h
    apply le_antisymm _ bot_le
    rw [primeReflectionField_eq_iSup]
    exact iSup_le (fun ρ => le_of_eq ((primePairField_eq_bot_iff_critical ρ).mpr (h ρ)))

end GaloisForLFunctions.GaloisTheoryOfZeros

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTraceExponent_image
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTraceExponentHom_value
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTraceExponentHom_root
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTraceExponentEquiv
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTraceExponentRepresentation_injective
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTraceExponentHom_one
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTraceExponentHom_rational
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.rationalPrimeSpectralField_le_traceField
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTraceExponentHom_conjugation
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTraceZeroMap_rational_real_part
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTraceZeroMap_rational_orbit
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTraceZeroMap_critical_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionOrbit_rational_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeResidueOverPair_rational_degree_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primePairField_eq_residue_of_rational_offline
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionOrbit_irrational_offline
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeFunctionalReflection_irrational_offline
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionOrbit_relations_dependent
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionOrbit_relations_single_support
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionOrbit_two_algebraic_values_critical
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionDifference_mem_pair_of_rational_offline
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionRadicand_square_of_rational_offline
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionDifference_ne_zero_of_offline
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflection_rational_offline_odd_square_relation
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primePairField_eq_bot_iff_critical
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTraceOrbit_meets_critical_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeTraceZeroMap_rational_orbit_iff
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.primeReflectionField_eq_bot_iff_critical
