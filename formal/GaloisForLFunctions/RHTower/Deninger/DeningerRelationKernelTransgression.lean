import GaloisForLFunctions.RHTower.Deninger.DeningerBaumslagH2
import GaloisForLFunctions.RHTower.Deninger.DeningerBaumslagDegreeOne
import GaloisForLFunctions.RHTower.Deninger.DeningerCalderonWittDerivedCupSource

/-!
# Relation-kernel transgression

A normalized degree-two cocycle may become exact after pullback to a free rational source without
being exact on the arithmetic quotient.  The primitive retains the missing information on the
relation kernel.  This file proves that the restriction is a homomorphism, is independent of the
primitive when degree-one comparison is onto, and vanishes exactly when the cocycle descends as a
coboundary.

For an abelian quotient and an alternating cocycle, a coboundary is symmetric.  Over rational
coefficients the kernel transgression therefore vanishes exactly when the alternating cocycle
itself vanishes.  This is the coefficient-faithful form needed by the Calderon--Witt source: the
free cover does not erase its degree-two orientation; it moves it to a canonical degree-one
relation character.
-/

namespace RHTower

universe v

namespace DeningerNormalizedCocycle

variable {G A : Type} {M : Type v}
  [Group G] [Group A] [AddCommGroup M]

/-- Pullback of a normalized cocycle along a group homomorphism. -/
def pullback (c : DeningerNormalizedCocycle A M) (pi : G →* A) :
    DeningerNormalizedCocycle G M where
  f p := c.f (pi p.1, pi p.2)
  cocycle g h j := by
    simpa using c.cocycle (pi g) (pi h) (pi j)
  one_fst g := by simpa using c.one_fst (pi g)
  one_snd g := by simpa using c.one_snd (pi g)

/-- A cochain trivializes a normalized cocycle when its coboundary is the cocycle. -/
def IsPrimitive (c : DeningerNormalizedCocycle G M) (b : G → M) : Prop :=
  ∀ g h, c.f (g, h) = b (g * h) - b g - b h

/-- A normalized cocycle is a coboundary when it has a global primitive. -/
def IsCoboundary (c : DeningerNormalizedCocycle G M) : Prop :=
  ∃ b : G → M, c.IsPrimitive b

/-- Every primitive of a normalized cocycle vanishes at the identity. -/
theorem primitive_one {c : DeningerNormalizedCocycle G M} {b : G → M}
    (hb : c.IsPrimitive b) : b 1 = 0 := by
  have h := hb 1 1
  rw [c.one_fst] at h
  simp only [one_mul] at h
  have hneg : -b 1 = 0 := by
    calc
      -b 1 = b 1 - b 1 - b 1 := by abel
      _ = 0 := h.symm
  exact neg_eq_zero.mp hneg

/-- On the kernel of a quotient map, a primitive of the pulled-back cocycle is additive. -/
theorem primitive_mul_of_mem_ker
    (c : DeningerNormalizedCocycle A M) (pi : G →* A) {b : G → M}
    (hb : (c.pullback pi).IsPrimitive b)
    {g h : G} (hg : g ∈ pi.ker) (hh : h ∈ pi.ker) :
    b (g * h) = b g + b h := by
  have hgh := hb g h
  have hpg : pi g = 1 := MonoidHom.mem_ker.mp hg
  have hph : pi h = 1 := MonoidHom.mem_ker.mp hh
  change c.f (pi g, pi h) = b (g * h) - b g - b h at hgh
  rw [hpg, hph, c.one_fst] at hgh
  calc
    b (g * h) = (b (g * h) - b g - b h) + b g + b h := by abel
    _ = 0 + b g + b h := by rw [hgh.symm]
    _ = b g + b h := by simp

/-- The canonical relation-kernel character carried by a chosen cocycle primitive. -/
def kernelTransgression
    (c : DeningerNormalizedCocycle A M) (pi : G →* A) (b : G → M)
    (hb : (c.pullback pi).IsPrimitive b) : pi.ker →* Multiplicative M where
  toFun k := Multiplicative.ofAdd (b k)
  map_one' := by
    change b 1 = 0
    exact primitive_one hb
  map_mul' g h := by
    change b ((g * h : pi.ker) : G) = b (g : G) + b (h : G)
    exact primitive_mul_of_mem_ker c pi hb g.property h.property

/-- The difference of two primitives of the same cocycle is a degree-one character. -/
def primitiveDifference
    (c : DeningerNormalizedCocycle G M) (b d : G → M)
    (hb : c.IsPrimitive b) (hd : c.IsPrimitive d) : G →* Multiplicative M where
  toFun g := Multiplicative.ofAdd (b g - d g)
  map_one' := by
    change b 1 - d 1 = 0
    rw [primitive_one hb, primitive_one hd, sub_self]
  map_mul' g h := by
    change b (g * h) - d (g * h) = (b g - d g) + (b h - d h)
    have hbc : b (g * h) = c.f (g, h) + b g + b h := by
      have h := hb g h
      rw [h]
      abel
    have hdc : d (g * h) = c.f (g, h) + d g + d h := by
      have h := hd g h
      rw [h]
      abel
    rw [hbc, hdc]
    abel

/-- If every degree-one character descends through the quotient, kernel transgression is
independent of the chosen degree-two primitive. -/
theorem kernelTransgression_apply_eq_of_degreeOneDescent
    (c : DeningerNormalizedCocycle A M) (pi : G →* A)
    (hH1 : ∀ psi : G →* Multiplicative M, ∀ k ∈ pi.ker, psi k = 1)
    {b d : G → M}
    (hb : (c.pullback pi).IsPrimitive b)
    (hd : (c.pullback pi).IsPrimitive d)
    (k : pi.ker) :
    kernelTransgression c pi b hb k = kernelTransgression c pi d hd k := by
  have hk := hH1
    (primitiveDifference (c.pullback pi) b d hb hd) k k.property
  have hk' := congrArg Multiplicative.toAdd hk
  change b k - d k = 0 at hk'
  exact congrArg Multiplicative.ofAdd (sub_eq_zero.mp hk')

/-- A primitive with zero relation-kernel character descends to a primitive on the quotient. -/
theorem isCoboundary_of_kernelTransgression_eq_one
    (c : DeningerNormalizedCocycle A M) (pi : G →* A)
    (hpi : Function.Surjective pi) {b : G → M}
    (hb : (c.pullback pi).IsPrimitive b)
    (hker : ∀ k : pi.ker, b k = 0) :
    c.IsCoboundary := by
  let lift : A → G := Function.surjInv hpi
  have hlift : ∀ a : A, pi (lift a) = a := Function.rightInverse_surjInv hpi
  refine ⟨fun a => b (lift a), ?_⟩
  intro a d
  let k : pi.ker :=
    ⟨(lift (a * d))⁻¹ * (lift a * lift d), by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hlift, map_mul, hlift, hlift,
        inv_mul_cancel]⟩
  have hk : b (k : G) = 0 := by
    exact hker k
  have hcompare : b (lift a * lift d) = b (lift (a * d)) := by
    have hprim := hb (lift (a * d)) k
    have hpk : pi (k : G) = 1 := MonoidHom.mem_ker.mp k.property
    change c.f (pi (lift (a * d)), pi (k : G)) =
      b (lift (a * d) * (k : G)) - b (lift (a * d)) - b (k : G) at hprim
    rw [hlift, hpk, c.one_snd, hk, sub_zero] at hprim
    have hprod : lift (a * d) * (k : G) = lift a * lift d := by
      simp [k]
    rw [hprod] at hprim
    exact sub_eq_zero.mp hprim.symm
  have hab := hb (lift a) (lift d)
  change c.f (pi (lift a), pi (lift d)) =
    b (lift a * lift d) - b (lift a) - b (lift d) at hab
  rw [hlift, hlift, hcompare] at hab
  exact hab

/-- A downstairs primitive pulls back with identically zero relation-kernel character. -/
theorem exists_primitive_kernelTransgression_eq_one_of_isCoboundary
    (c : DeningerNormalizedCocycle A M) (pi : G →* A)
    (hc : c.IsCoboundary) :
    ∃ b : G → M, (c.pullback pi).IsPrimitive b ∧
      ∀ k : pi.ker, b k = 0 := by
  obtain ⟨d, hd⟩ := hc
  let b : G → M := fun g => d (pi g)
  have hb : (c.pullback pi).IsPrimitive b := by
    intro g h
    simpa [pullback, b] using hd (pi g) (pi h)
  refine ⟨b, hb, ?_⟩
  intro k
  change d (pi (k : G)) = 0
  rw [MonoidHom.mem_ker.mp k.property]
  exact primitive_one hd

/-- Under degree-one descent, the relation-kernel character of any primitive vanishes exactly
when the original quotient cocycle is a coboundary. -/
theorem kernelTransgression_eq_one_iff_isCoboundary
    (c : DeningerNormalizedCocycle A M) (pi : G →* A)
    (hpi : Function.Surjective pi)
    (hH1 : ∀ psi : G →* Multiplicative M, ∀ k ∈ pi.ker, psi k = 1)
    {b : G → M} (hb : (c.pullback pi).IsPrimitive b) :
    (∀ k : pi.ker, b k = 0) ↔ c.IsCoboundary := by
  constructor
  · exact isCoboundary_of_kernelTransgression_eq_one c pi hpi hb
  · intro hc
    obtain ⟨d, hd, hdk⟩ :=
      exists_primitive_kernelTransgression_eq_one_of_isCoboundary c pi hc
    intro k
    have heq := kernelTransgression_apply_eq_of_degreeOneDescent c pi hH1 hb hd k
    have heq' := congrArg Multiplicative.toAdd heq
    change b k = d k at heq'
    rw [heq', hdk k]

end DeningerNormalizedCocycle

/-! ## Baumslag free-rational specialization -/

section BaumslagRelationKernel

variable {ι A M : Type}
  [AddCommGroup A] [Module ℚ A] [AddCommGroup M] [Module ℚ M]

/-- **Free-rational relation-kernel transgression law.**  Every normalized cocycle on a rational
vector group becomes exact on its Baumslag free-rational cover.  The resulting relation-kernel
character is canonical and vanishes exactly when the original cocycle is already a coboundary. -/
theorem deningerBauFree_exists_canonical_kernelTransgression
    (basis : Module.Basis ι ℚ A)
    (c : DeningerNormalizedCocycle (Multiplicative A) M) :
    ∃ b : DeningerBau (FreeGroup ι) → M,
      ((c.pullback (deningerBauFreeMap (⇑basis))).IsPrimitive b) ∧
      ((∀ k : (deningerBauFreeMap (⇑basis)).ker,
          b k = 0) ↔
        c.IsCoboundary) := by
  let pi := deningerBauFreeMap (⇑basis)
  obtain ⟨b, hb⟩ := deningerBauFree_cocycle_trivial (c.pullback pi)
  change (c.pullback pi).IsPrimitive b at hb
  refine ⟨b, ?_, ?_⟩
  · simpa [pi] using hb
  · have hpi : Function.Surjective pi :=
      deningerBauFree_surjective (⇑basis) basis.span_eq
    have hH1 : ∀ psi : DeningerBau (FreeGroup ι) →* Multiplicative M,
        ∀ k ∈ pi.ker, psi k = 1 := by
      intro psi k hk
      exact deningerBauFreeKer_killed basis psi hk
    have hcriterion :=
      DeningerNormalizedCocycle.kernelTransgression_eq_one_iff_isCoboundary
        c pi hpi hH1 hb
    simpa [pi] using hcriterion

end BaumslagRelationKernel

/-! ## Alternating quotient cocycles -/

namespace DeningerNormalizedCocycle

variable {A : Type} {M : Type v}
  [CommGroup A] [AddCommGroup M] [Module ℚ M]

/-- Alternation of a normalized cocycle. -/
def IsAlternating (c : DeningerNormalizedCocycle A M) : Prop :=
  ∀ a d, c.f (a, d) = -c.f (d, a)

/-- On an abelian quotient, an alternating rational cocycle is a coboundary exactly when it is
zero. -/
theorem isCoboundary_iff_eq_zero_of_alternating
    (c : DeningerNormalizedCocycle A M) (halt : c.IsAlternating) :
    c.IsCoboundary ↔ ∀ a d, c.f (a, d) = 0 := by
  constructor
  · rintro ⟨b, hb⟩ a d
    have hsymm : c.f (a, d) = c.f (d, a) := by
      rw [hb a d, hb d a, mul_comm]
      abel
    have hneg : c.f (a, d) = -c.f (a, d) := hsymm.trans (halt d a)
    have hsum : c.f (a, d) + c.f (a, d) = 0 :=
      (congrArg (fun z => z + c.f (a, d)) hneg).trans
        (neg_add_cancel (c.f (a, d)))
    have htwo : (2 : ℚ) • c.f (a, d) = 0 := by
      simpa [two_smul] using hsum
    calc
      c.f (a, d) = (1 / 2 : ℚ) • ((2 : ℚ) • c.f (a, d)) := by
        rw [smul_smul]
        norm_num
      _ = 0 := by rw [htwo, smul_zero]
  · intro hzero
    refine ⟨fun _ => 0, ?_⟩
    intro a d
    simp [hzero a d]

/-- **Alternating free-rational transgression law.**  For an alternating cocycle on a rational
vector group, the canonical relation-kernel character vanishes exactly when the full degree-two
cocycle vanishes. -/
theorem deningerBauFree_exists_alternating_kernelTransgression
    {ι V N : Type} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup N] [Module ℚ N]
    (basis : Module.Basis ι ℚ V)
    (c : DeningerNormalizedCocycle (Multiplicative V) N)
    (halt : c.IsAlternating) :
    ∃ b : DeningerBau (FreeGroup ι) → N,
      ((c.pullback (deningerBauFreeMap (⇑basis))).IsPrimitive b) ∧
      ((∀ k : (deningerBauFreeMap (⇑basis)).ker, b k = 0) ↔
        ∀ a d, c.f (a, d) = 0) := by
  obtain ⟨b, hb, htrans⟩ :=
    deningerBauFree_exists_canonical_kernelTransgression basis c
  exact ⟨b, hb, htrans.trans (isCoboundary_iff_eq_zero_of_alternating c halt)⟩

end DeningerNormalizedCocycle

/-! ## Actual Calderon--Witt source calibrator -/

noncomputable section

/-- The local Calderon--Witt cup, regarded as a normalized group two-cocycle on its additive
degree-one source. -/
def deningerCalderonWittCupCocycle (p : Nat.Primes) :
    DeningerNormalizedCocycle
      (Multiplicative (DeningerCalderonWittDegreeOne p))
      (DeningerCalderonWittDegreeTwo p) where
  f x := deningerCalderonWittCup p x.1.toAdd x.2.toAdd
  cocycle g h j := by
    change
      deningerCalderonWittCup p (g.toAdd + h.toAdd) j.toAdd +
          deningerCalderonWittCup p g.toAdd h.toAdd =
        deningerCalderonWittCup p h.toAdd j.toAdd +
          deningerCalderonWittCup p g.toAdd (h.toAdd + j.toAdd)
    simp only [map_add, LinearMap.add_apply]
    abel
  one_fst g := by
    change deningerCalderonWittCup p 0 g.toAdd = 0
    simp
  one_snd g := by
    change deningerCalderonWittCup p g.toAdd 0 = 0
    simp

/-- The Calderon--Witt cocycle is alternating before every scalar trace or completion. -/
theorem deningerCalderonWittCupCocycle_alternating (p : Nat.Primes) :
    (deningerCalderonWittCupCocycle p).IsAlternating := by
  intro x y
  change deningerCalderonWittCup p x.toAdd y.toAdd =
    -deningerCalderonWittCup p y.toAdd x.toAdd
  exact deningerCalderonWittCup_skew p x.toAdd y.toAdd

/-- The actual Calderon--Witt cocycle is not the zero degree-two class. -/
theorem deningerCalderonWittCupCocycle_ne_zero (p : Nat.Primes) :
    ¬ ∀ x y, (deningerCalderonWittCupCocycle p).f (x, y) = 0 := by
  intro hzero
  let x : DeningerCalderonWittDegreeOne p :=
    (0, deningerCalderonWittUnitPacket p)
  have hx : x ≠ 0 := by
    intro hx0
    apply deningerCalderonWittUnitPacket_ne_zero p
    exact congrArg Prod.snd hx0
  apply hx
  apply deningerCalderonWittCup_leftRadical_eq_zero p x
  intro y
  simpa [deningerCalderonWittCupCocycle] using
    hzero (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)

/-- **Actual source calibrator.**  On the Baumslag free-rational cover of the local
Calderon--Witt degree-one source, the pulled-back cup has a primitive whose restriction to the
relation kernel is nonzero.  Its kernel restriction is canonical by the degree-one comparison
theorem. -/
theorem exists_deningerCalderonWitt_nonzero_relationKernelTransgression
    (p : Nat.Primes) :
    let basis := Module.Free.chooseBasis ℚ (DeningerCalderonWittDegreeOne p)
    let pi := deningerBauFreeMap (⇑basis)
    ∃ b : DeningerBau (FreeGroup (Module.Free.ChooseBasisIndex ℚ
        (DeningerCalderonWittDegreeOne p))) → DeningerCalderonWittDegreeTwo p,
      (((deningerCalderonWittCupCocycle p).pullback pi).IsPrimitive b) ∧
      ¬ ∀ k : pi.ker, b k = 0 := by
  dsimp only
  let basis := Module.Free.chooseBasis ℚ (DeningerCalderonWittDegreeOne p)
  obtain ⟨b, hb, hvanish⟩ :=
    DeningerNormalizedCocycle.deningerBauFree_exists_alternating_kernelTransgression
      basis (deningerCalderonWittCupCocycle p)
      (deningerCalderonWittCupCocycle_alternating p)
  refine ⟨b, ?_, ?_⟩
  · simpa [basis] using hb
  · intro hzero
    exact deningerCalderonWittCupCocycle_ne_zero p (hvanish.mp hzero)

end

end RHTower
