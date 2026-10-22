import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeResidueSheaf

/-!
# The characteristic sheaf of the divisorial log structure

The valuations along `P` are a morphism of sheaves from the divisorial log structure to the direct
sum of the skyscrapers `i_{p,*} ℕ` over `p ∈ P`.  Over every open set it is onto, its kernel is the
sheaf of units, and its fibres are the orbits of the units.  So the characteristic sheaf of the
divisorial log structure is that direct sum of skyscrapers.

* `deningerResidueSectionHom` : the characteristic map on sections.
* `deningerLogResidueMap` : the morphism of sheaves.
* `deningerResidueSectionHom_surjective`, `deningerResidueSection_eq_one_iff`,
  `deningerResidueSection_orbit` : onto, kernel, and fibres.
-/

namespace RHTower

open TopologicalSpace CategoryTheory Opposite TopCat

variable {P : Finset Nat.Primes} {U : Opens deningerArithBase}

/-- The valuation of a section of the divisorial log structure along the primes of `P`. -/
def deningerResidueSectionFun (s : (deningerLogMulCond P).sub U) :
    deningerLogIdx P U → Multiplicative ℕ :=
  fun i => Multiplicative.ofAdd
    (padicValRat (((i : Nat.Primes) : ℕ))
      ((deningerLogSectionVal s ⟨deningerClosedPt ((i : Nat.Primes)), i.2.2⟩ : ℚˣ) : ℚ)).toNat

theorem deningerResidueSectionFun_eq (s : (deningerLogMulCond P).sub U) (x : ↥U)
    (i : deningerLogIdx P U) :
    deningerResidueSectionFun s i = Multiplicative.ofAdd
      (deningerLogOrdFun P U
        ⟨deningerLogSectionVal s x, deningerLogSection_mem s x⟩ i) := by
  refine congrArg Multiplicative.ofAdd ?_
  show (padicValRat _ _).toNat = (padicValRat _ _).toNat
  rw [deningerLogSectionVal_const s ⟨deningerClosedPt ((i : Nat.Primes)), i.2.2⟩ x]

theorem deningerResidueSectionFun_one :
    deningerResidueSectionFun (1 : (deningerLogMulCond P).sub U) = 1 := by
  funext i
  haveI : Fact (((i : Nat.Primes) : ℕ)).Prime := ⟨(i : Nat.Primes).2⟩
  show (padicValRat (((i : Nat.Primes) : ℕ)) ((1 : ℚˣ) : ℚ)).toNat = 0
  rw [Units.val_one, padicValRat.one]
  rfl

theorem deningerResidueSectionFun_mul (a b : (deningerLogMulCond P).sub U) :
    deningerResidueSectionFun (a * b) =
      deningerResidueSectionFun a * deningerResidueSectionFun b := by
  funext i
  haveI : Fact (((i : Nat.Primes) : ℕ)).Prime := ⟨(i : Nat.Primes).2⟩
  set x : ↥U := ⟨deningerClosedPt ((i : Nat.Primes)), i.2.2⟩ with hx
  set va : ℤ := padicValRat (((i : Nat.Primes) : ℕ))
    ((deningerLogSectionVal a x : ℚˣ) : ℚ) with hva
  set vb : ℤ := padicValRat (((i : Nat.Primes) : ℕ))
    ((deningerLogSectionVal b x : ℚˣ) : ℚ) with hvb
  have hna : 0 ≤ va := (deningerLogSection_mem a x (i : Nat.Primes) i.2.2).1
  have hnb : 0 ≤ vb := (deningerLogSection_mem b x (i : Nat.Primes) i.2.2).1
  have hmul : padicValRat (((i : Nat.Primes) : ℕ))
      ((deningerLogSectionVal (a * b) x : ℚˣ) : ℚ) = va + vb := by
    rw [hva, hvb,
      show ((deningerLogSectionVal (a * b) x : ℚˣ) : ℚ) =
        ((deningerLogSectionVal a x : ℚˣ) : ℚ) * ((deningerLogSectionVal b x : ℚˣ) : ℚ) from rfl,
      padicValRat.mul (Units.ne_zero _) (Units.ne_zero _)]
  show (padicValRat (((i : Nat.Primes) : ℕ))
      ((deningerLogSectionVal (a * b) x : ℚˣ) : ℚ)).toNat = va.toNat + vb.toNat
  rw [hmul, Int.toNat_add hna hnb]

/-- The valuations along `P`, as a monoid homomorphism on sections. -/
def deningerResidueSectionHom (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    (deningerLogMulCond P).sub U →* (deningerLogIdx P U → Multiplicative ℕ) where
  toFun := deningerResidueSectionFun
  map_one' := deningerResidueSectionFun_one
  map_mul' := deningerResidueSectionFun_mul

@[simp]
theorem deningerResidueSectionHom_apply (s : (deningerLogMulCond P).sub U) :
    deningerResidueSectionHom P U s = deningerResidueSectionFun s := rfl

/-- Sections of the sheaf of units are sections of the divisorial log structure. -/
theorem deningerUnitSub_le_logSub (P : Finset Nat.Primes) (U : Opens deningerArithBase) :
    deningerUnitMulCond.sub U ≤ (deningerLogMulCond P).sub U := by
  rintro f ⟨hconst, hcond⟩
  refine ⟨hconst, fun x p hxp => ?_⟩
  rw [hcond x p hxp]
  exact ⟨le_rfl, fun _ => rfl⟩

/-- **The characteristic map is onto**: every exponent vector along `P` is realized. -/
theorem deningerResidueSectionHom_surjective (P : Finset Nat.Primes)
    (U : Opens deningerArithBase) : Function.Surjective (deningerResidueSectionHom P U) := by
  intro n
  obtain ⟨q, hq⟩ := deningerLogOrd_surjective P U
    (Multiplicative.ofAdd (fun i => Multiplicative.toAdd (n i)))
  refine ⟨deningerLogConstSection q, ?_⟩
  funext i
  have hfun : deningerLogOrdFun P U q = fun i => Multiplicative.toAdd (n i) :=
    congrArg Multiplicative.toAdd hq
  show deningerResidueSectionFun (deningerLogConstSection q) i = n i
  rw [deningerResidueSectionFun_eq _ ⟨deningerClosedPt ((i : Nat.Primes)), i.2.2⟩ i]
  have hval : (⟨deningerLogSectionVal (deningerLogConstSection q)
      ⟨deningerClosedPt ((i : Nat.Primes)), i.2.2⟩,
      deningerLogSection_mem (deningerLogConstSection q) _⟩ :
        deningerLogSub P U) = q := Subtype.ext rfl
  rw [hval, hfun]
  rfl

/-- **The kernel of the characteristic map is the sheaf of units.** -/
theorem deningerResidueSection_eq_one_iff (s : (deningerLogMulCond P).sub U) :
    deningerResidueSectionHom P U s = 1 ↔
      ((s : ↥U → ℚˣ)) ∈ deningerUnitMulCond.sub U := by
  constructor
  · intro h
    refine ⟨s.2.1, fun x p hxp => ?_⟩
    have hp : deningerClosedPt p ∈ U := hxp ▸ x.2
    have hconst : (s : ↥U → ℚˣ) x = deningerLogSectionVal s ⟨deningerClosedPt p, hp⟩ :=
      s.2.1 x ⟨deningerClosedPt p, hp⟩
    rw [hconst]
    by_cases hP : p ∈ P
    · have hi : deningerResidueSectionFun s ⟨p, hP, hp⟩ = 1 := congrFun h ⟨p, hP, hp⟩
      have h0 : (padicValRat ((p : ℕ))
          ((deningerLogSectionVal s ⟨deningerClosedPt p, hp⟩ : ℚˣ) : ℚ)).toNat = 0 :=
        congrArg Multiplicative.toAdd hi
      have hnn : 0 ≤ padicValRat ((p : ℕ))
          ((deningerLogSectionVal s ⟨deningerClosedPt p, hp⟩ : ℚˣ) : ℚ) :=
        (deningerLogSection_mem s ⟨deningerClosedPt p, hp⟩ p hp).1
      omega
    · exact (deningerLogSection_mem s ⟨deningerClosedPt p, hp⟩ p hp).2 hP
  · intro h
    funext i
    have hp : deningerClosedPt ((i : Nat.Primes)) ∈ U := i.2.2
    have h0 := h.2 ⟨deningerClosedPt ((i : Nat.Primes)), hp⟩ (i : Nat.Primes) rfl
    show Multiplicative.ofAdd (padicValRat _ _).toNat = 1
    rw [show ((deningerLogSectionVal s ⟨deningerClosedPt ((i : Nat.Primes)), hp⟩ : ℚˣ) : ℚ) =
      (((s : ↥U → ℚˣ) ⟨deningerClosedPt ((i : Nat.Primes)), hp⟩ : ℚˣ) : ℚ) from rfl, h0]
    rfl

/-- **The fibres of the characteristic map are the orbits of the units**: two sections with the same
valuations differ by a unit. -/
theorem deningerResidueSection_orbit (s t : (deningerLogMulCond P).sub U)
    (h : deningerResidueSectionHom P U s = deningerResidueSectionHom P U t) :
    ∃ w : ↥U → ℚˣ, w ∈ deningerUnitMulCond.sub U ∧
      ((s : ↥U → ℚˣ)) = ((t : ↥U → ℚˣ)) * w := by
  refine ⟨fun x => ((t : ↥U → ℚˣ) x)⁻¹ * ((s : ↥U → ℚˣ) x), ⟨?_, ?_⟩, ?_⟩
  · intro x y
    show ((t : ↥U → ℚˣ) x)⁻¹ * ((s : ↥U → ℚˣ) x) =
      ((t : ↥U → ℚˣ) y)⁻¹ * ((s : ↥U → ℚˣ) y)
    rw [s.2.1 x y, t.2.1 x y]
  · intro x p hxp
    haveI : Fact ((p : ℕ)).Prime := ⟨p.2⟩
    have hp : deningerClosedPt p ∈ U := hxp ▸ x.2
    have hval : padicValRat ((p : ℕ)) (((s : ↥U → ℚˣ) x : ℚˣ) : ℚ) =
        padicValRat ((p : ℕ)) (((t : ↥U → ℚˣ) x : ℚˣ) : ℚ) := by
      have hsx : (s : ↥U → ℚˣ) x = deningerLogSectionVal s ⟨deningerClosedPt p, hp⟩ :=
        s.2.1 x ⟨deningerClosedPt p, hp⟩
      have htx : (t : ↥U → ℚˣ) x = deningerLogSectionVal t ⟨deningerClosedPt p, hp⟩ :=
        t.2.1 x ⟨deningerClosedPt p, hp⟩
      rw [hsx, htx]
      by_cases hP : p ∈ P
      · have hi : deningerResidueSectionFun s ⟨p, hP, hp⟩ =
            deningerResidueSectionFun t ⟨p, hP, hp⟩ := congrFun h ⟨p, hP, hp⟩
        have h0 : (padicValRat ((p : ℕ))
            ((deningerLogSectionVal s ⟨deningerClosedPt p, hp⟩ : ℚˣ) : ℚ)).toNat =
            (padicValRat ((p : ℕ))
            ((deningerLogSectionVal t ⟨deningerClosedPt p, hp⟩ : ℚˣ) : ℚ)).toNat :=
          congrArg Multiplicative.toAdd hi
        have h1 : 0 ≤ padicValRat ((p : ℕ))
            ((deningerLogSectionVal s ⟨deningerClosedPt p, hp⟩ : ℚˣ) : ℚ) :=
          (deningerLogSection_mem s ⟨deningerClosedPt p, hp⟩ p hp).1
        have h2 : 0 ≤ padicValRat ((p : ℕ))
            ((deningerLogSectionVal t ⟨deningerClosedPt p, hp⟩ : ℚˣ) : ℚ) :=
          (deningerLogSection_mem t ⟨deningerClosedPt p, hp⟩ p hp).1
        omega
      · rw [(deningerLogSection_mem s ⟨deningerClosedPt p, hp⟩ p hp).2 hP,
          (deningerLogSection_mem t ⟨deningerClosedPt p, hp⟩ p hp).2 hP]
    show padicValRat ((p : ℕ)) (((((t : ↥U → ℚˣ) x)⁻¹ * ((s : ↥U → ℚˣ) x) : ℚˣ)) : ℚ) = 0
    rw [Units.val_mul, padicValRat.mul (Units.ne_zero _) (Units.ne_zero _),
      Units.val_inv_eq_inv_val, padicValRat.inv, hval, neg_add_cancel]
  · funext x
    show (s : ↥U → ℚˣ) x = (t : ↥U → ℚˣ) x * (((t : ↥U → ℚˣ) x)⁻¹ * ((s : ↥U → ℚˣ) x))
    rw [← mul_assoc, mul_inv_cancel, one_mul]

/-- **The characteristic map is a morphism of sheaves** from the divisorial log structure to the
direct sum of the skyscrapers `i_{p,*} ℕ` over `p ∈ P`. -/
def deningerLogResidueMap (P : Finset Nat.Primes) :
    (deningerLogMulCond P).presheaf ⟶ deningerResidueMulPresheaf P (Multiplicative ℕ) where
  app U := CommMonCat.ofHom (deningerResidueSectionHom P U.unop)
  naturality U V h := by
    refine CommMonCat.hom_ext ?_
    refine MonoidHom.ext fun s => ?_
    funext i
    show deningerResidueSectionFun
      ((deningerLogMulCond P).resHom (leOfHom h.unop) s) i =
        deningerResidueRes (leOfHom h.unop) (deningerResidueSectionFun s) i
    show Multiplicative.ofAdd (padicValRat _ _).toNat =
      Multiplicative.ofAdd (padicValRat _ _).toNat
    refine congrArg Multiplicative.ofAdd (congrArg Int.toNat (congrArg _ ?_))
    exact congrArg (fun z : ℚˣ => (z : ℚ)) (s.2.1 _ _)

end RHTower
