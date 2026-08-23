import GaloisForLFunctions.RHTower.DeningerDynSysClosureFractionField
import GaloisForLFunctions.RHTower.DeningerDynSysValuedTriples
import GaloisForLFunctions.HTGeometry.PerfectionMonoidWithZero
import GaloisForLFunctions.HTGeometry.GroupWithZeroMultiplicativeExtension
import GaloisForLFunctions.HTGeometry.AdicCompletionTopology
import GaloisForLFunctions.RHTower.DeningerDynSysPerfectionDense

/-!
# The completed `𝒪`-valued points

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Definition 14.9
(`t42n`) and Proposition 14.11 (`t1213nn`).

Deninger's completed points of `W_rat (X)` are triples `(x , y , P^×)` where `P^×` is a character
of the units of `lim_{()^p} κ (x)` whose extension by zero fits into a diagram involving the
`p`-adic completion `Ô_{closure {x} , y}` and a continuous pointed multiplicative map `P̂_y` on its
perfection.  Proposition 14.11 says the triple is determined by `P̂_y`, and characterises the
`P̂_y` that occur by two conditions: `P̂_y` is nonzero off `0` on `lim_{()^p} 𝒪_{closure {x} , y}`,
and its residue depends only on the value at `y`.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory HTGeometry Perfection

noncomputable section

universe u

variable {X : Scheme.{u}} {x y : X} {p : ℕ} [NeZero p]

/-- The `p`-adic completion of the local ring of the closure of `x` at `y`. -/
def DeningerClosureHat (h : x ⤳ y) (p : ℕ) : Type u :=
  AdicCompletion (Ideal.span {(p : DeningerClosureLocalRing h)}) (DeningerClosureLocalRing h)

namespace DeningerClosureHat

variable (h : x ⤳ y) (p)

instance : CommRing (DeningerClosureHat h p) :=
  inferInstanceAs (CommRing (AdicCompletion _ _))

instance : Algebra (DeningerClosureLocalRing h) (DeningerClosureHat h p) :=
  inferInstanceAs (Algebra _ (AdicCompletion _ _))

instance : TopologicalSpace (DeningerClosureHat h p) :=
  inferInstanceAs (TopologicalSpace (AdicCompletion _ _))

instance : ContinuousMul (DeningerClosureHat h p) :=
  inferInstanceAs (ContinuousMul (AdicCompletion _ _))

end DeningerClosureHat

/-- The comparison `lim_{()^p} 𝒪_{closure {x},y} → lim_{()^p} Ô_{closure {x},y}`. -/
def deningerPerfIota (h : x ⤳ y) (p : ℕ) [NeZero p] :
    Perfection (DeningerClosureLocalRing h) p →*₀ Perfection (DeningerClosureHat h p) p :=
  perfectionMapWithZero
    (algebraMap (DeningerClosureLocalRing h) (DeningerClosureHat h p)).toMonoidWithZeroHom

/-- The evaluation `lim_{()^p} 𝒪_{closure {x},y} → lim_{()^p} κ (x)`. -/
def deningerPerfEvalGen (h : x ⤳ y) (p : ℕ) [NeZero p] :
    Perfection (DeningerClosureLocalRing h) p →*₀ Perfection (X.residueField x) p :=
  perfectionMapWithZero (deningerClosureToResidue h).toMonoidWithZeroHom

/-- The evaluation `lim_{()^p} 𝒪_{closure {x},y} → lim_{()^p} κ (y)`. -/
def deningerPerfEvalSpec (h : x ⤳ y) (p : ℕ) [NeZero p] :
    Perfection (DeningerClosureLocalRing h) p →*₀ Perfection (X.residueField y) p :=
  perfectionMapWithZero (deningerClosureResidue h).toMonoidWithZeroHom

theorem deningerPerfEvalGen_injective (h : x ⤳ y) :
    Function.Injective (deningerPerfEvalGen (p := p) h) :=
  perfectionMapWithZero_injective (deningerClosureToResidue_injective h)

/-- **Deninger, Definition 14.9 (`t42n`).**  A completed `𝒪`-valued point: a specialisation
`y ∈ closure {x}`, a character of the units of `lim_{()^p} κ (x)`, a continuous pointed
multiplicative map on `lim_{()^p} Ô_{closure {x},y}`, and a pointed multiplicative map on
`lim_{()^p} κ (y)`, making Deninger's two squares commute. -/
structure DeningerCompletedCharTriple (X : Scheme.{u}) (O : Type u) [CommRing O] [IsDomain O]
    [IsLocalRing O] [TopologicalSpace O] (p : ℕ) [NeZero p] where
  /-- The generic point. -/
  gen : X
  /-- The specialisation. -/
  spec : X
  /-- `spec` lies in the closure of `gen`. -/
  specializes : gen ⤳ spec
  /-- Deninger's `P^×`. -/
  chr : (Perfection (X.residueField gen) p)ˣ →* (FractionRing O)ˣ
  /-- Deninger's `P̂_y`. -/
  hatMap : Perfection (DeningerClosureHat specializes p) p →*₀ O
  /-- `P̂_y` is continuous. -/
  hatMap_continuous : Continuous hatMap
  /-- Deninger's `P̃_y`. -/
  residueMap : Perfection (X.residueField spec) p →*₀ IsLocalRing.ResidueField O
  /-- The lower square of (177). -/
  comm_gen : ∀ f : Perfection (DeningerClosureLocalRing specializes) p,
    algebraMap O (FractionRing O) (hatMap (deningerPerfIota specializes p f))
      = gwzExtendByZero chr (deningerPerfEvalGen specializes p f)
  /-- The upper square of (177). -/
  comm_spec : ∀ f : Perfection (DeningerClosureLocalRing specializes) p,
    IsLocalRing.residue O (hatMap (deningerPerfIota specializes p f))
      = residueMap (deningerPerfEvalSpec specializes p f)

/-- **Deninger, Proposition 14.11 (`t1213nn`).**  The description of a completed `𝒪`-valued point
by `P̂_y` alone, with Deninger's conditions 1) and 2). -/
structure DeningerCompletedHatTriple (X : Scheme.{u}) (O : Type u) [CommRing O] [IsDomain O]
    [IsLocalRing O] [TopologicalSpace O] (p : ℕ) [NeZero p] where
  /-- The generic point. -/
  gen : X
  /-- The specialisation. -/
  spec : X
  /-- `spec` lies in the closure of `gen`. -/
  specializes : gen ⤳ spec
  /-- Deninger's `P̂_y`. -/
  hatMap : Perfection (DeningerClosureHat specializes p) p →*₀ O
  /-- `P̂_y` is continuous. -/
  hatMap_continuous : Continuous hatMap
  /-- Condition 1): `P̂_y` is nonzero off `0`. -/
  hat_ne_zero : ∀ f : Perfection (DeningerClosureLocalRing specializes) p, f ≠ 0 →
    hatMap (deningerPerfIota specializes p f) ≠ 0
  /-- Condition 2): the residue depends only on the value at `spec`. -/
  hat_residue : ∀ f g : Perfection (DeningerClosureLocalRing specializes) p,
    deningerPerfEvalSpec specializes p f = deningerPerfEvalSpec specializes p g →
    hatMap (deningerPerfIota specializes p f) - hatMap (deningerPerfIota specializes p g)
      ∈ IsLocalRing.maximalIdeal O

variable {O : Type u} [CommRing O] [IsDomain O] [IsLocalRing O] [TopologicalSpace O]

/-- **Deninger, Proposition 14.11 (`t1213nn`).**  A completed character triple gives a point in the
`P̂_y` description. -/
@[reducible] def DeningerCompletedCharTriple.toHatTriple (T : DeningerCompletedCharTriple X O p) :
    DeningerCompletedHatTriple X O p where
  gen := T.gen
  spec := T.spec
  specializes := T.specializes
  hatMap := T.hatMap
  hatMap_continuous := T.hatMap_continuous
  hat_ne_zero := by
    intro f hf hc
    have h := T.comm_gen f
    rw [hc, map_zero] at h
    have hne : deningerPerfEvalGen T.specializes p f ≠ 0 := fun hz =>
      hf (deningerPerfEvalGen_injective T.specializes (by rw [hz, map_zero]))
    rw [gwzExtendByZero_apply_ne_zero _ hne] at h
    exact (Units.ne_zero _) h.symm
  hat_residue := by
    intro f g hfg
    have h1 := T.comm_spec f
    have h2 := T.comm_spec g
    have h3 : IsLocalRing.residue O (T.hatMap (deningerPerfIota T.specializes p f))
        = IsLocalRing.residue O (T.hatMap (deningerPerfIota T.specializes p g)) := by
      rw [h1, h2, hfg]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).1 h3

namespace DeningerCompletedHatTriple

variable (T : DeningerCompletedHatTriple X O p)

/-- The restriction of `P̂_y` to `lim_{()^p} 𝒪_{closure {x},y}`, with values in `C`. -/
def baseMap : Perfection (DeningerClosureLocalRing T.specializes) p →*₀ FractionRing O :=
  ((algebraMap O (FractionRing O)).toMonoidWithZeroHom).comp
    (T.hatMap.comp (deningerPerfIota T.specializes p))

@[simp] theorem baseMap_apply (f : Perfection (DeningerClosureLocalRing T.specializes) p) :
    T.baseMap f = algebraMap O (FractionRing O) (T.hatMap (deningerPerfIota T.specializes p f)) :=
  rfl

theorem baseMap_ne_zero (f : Perfection (DeningerClosureLocalRing T.specializes) p) (hf : f ≠ 0) :
    T.baseMap f ≠ 0 := by
  rw [baseMap_apply]
  intro hc
  exact T.hat_ne_zero f hf
    ((injective_iff_map_eq_zero (algebraMap O (FractionRing O))).1
      (IsFractionRing.injective O (FractionRing O)) _ hc)

variable
  (hratio : ∀ t : Perfection (X.residueField T.gen) p,
    ∃ fs : Perfection (DeningerClosureLocalRing T.specializes) p ×
        Perfection (DeningerClosureLocalRing T.specializes) p,
      fs.2 ≠ 0 ∧ t * deningerPerfEvalGen T.specializes p fs.2
        = deningerPerfEvalGen T.specializes p fs.1)

/-- The pointed multiplicative map on `lim_{()^p} κ (x)` recovered from `P̂_y`. -/
def genMap : Perfection (X.residueField T.gen) p →*₀ FractionRing O :=
  gwzRatioExtend (deningerPerfEvalGen T.specializes p)
    (deningerPerfEvalGen_injective T.specializes) hratio T.baseMap T.baseMap_ne_zero

theorem genMap_comp (f : Perfection (DeningerClosureLocalRing T.specializes) p) :
    T.genMap hratio (deningerPerfEvalGen T.specializes p f) = T.baseMap f :=
  gwzRatioExtend_comp _ _ _ _ _ f

/-- Deninger's `P^×` recovered from `P̂_y`. -/
def chrOf : (Perfection (X.residueField T.gen) p)ˣ →* (FractionRing O)ˣ :=
  gwzPointedEquivChar (T.genMap hratio)

theorem gwzExtendByZero_chrOf : gwzExtendByZero (T.chrOf hratio) = T.genMap hratio :=
  gwzPointedEquivChar.left_inv _

variable (hlam : Function.Surjective (deningerPerfEvalSpec T.specializes p))

/-- The map on `lim_{()^p} κ (y)` recovered from `P̂_y`. -/
noncomputable def residueFun (t : Perfection (X.residueField T.spec) p) :
    IsLocalRing.ResidueField O :=
  IsLocalRing.residue O (T.hatMap (deningerPerfIota T.specializes p (hlam t).choose))

theorem residueFun_apply (f : Perfection (DeningerClosureLocalRing T.specializes) p) :
    T.residueFun hlam (deningerPerfEvalSpec T.specializes p f)
      = IsLocalRing.residue O (T.hatMap (deningerPerfIota T.specializes p f)) := by
  have hs := (hlam (deningerPerfEvalSpec T.specializes p f)).choose_spec
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).2 (T.hat_residue _ _ hs)

/-- Deninger's `P̃_y` recovered from `P̂_y`. -/
noncomputable def residueMapOf :
    Perfection (X.residueField T.spec) p →*₀ IsLocalRing.ResidueField O where
  toFun := T.residueFun hlam
  map_zero' := by
    have h : (0 : Perfection (X.residueField T.spec) p)
        = deningerPerfEvalSpec T.specializes p 0 := (map_zero _).symm
    rw [h, T.residueFun_apply hlam, map_zero, map_zero, map_zero]
  map_one' := by
    have h : (1 : Perfection (X.residueField T.spec) p)
        = deningerPerfEvalSpec T.specializes p 1 := (map_one _).symm
    rw [h, T.residueFun_apply hlam, map_one, map_one, map_one]
  map_mul' s t := by
    obtain ⟨f, rfl⟩ := hlam s
    obtain ⟨g, rfl⟩ := hlam t
    rw [← map_mul, T.residueFun_apply hlam, T.residueFun_apply hlam, T.residueFun_apply hlam,
      map_mul, map_mul, map_mul]

/-- **Deninger, Proposition 14.11 (`t1213nn`).**  The completed character triple recovered from
`P̂_y`. -/
def toCharTriple : DeningerCompletedCharTriple X O p where
  gen := T.gen
  spec := T.spec
  specializes := T.specializes
  chr := T.chrOf hratio
  hatMap := T.hatMap
  hatMap_continuous := T.hatMap_continuous
  residueMap := T.residueMapOf hlam
  comm_gen := by
    intro f
    rw [T.gwzExtendByZero_chrOf hratio, T.genMap_comp hratio f, baseMap_apply]
  comm_spec := by
    intro f
    exact (T.residueFun_apply hlam f).symm

end DeningerCompletedHatTriple

theorem DeningerCompletedCharTriple.ext' {T U : DeningerCompletedCharTriple X O p}
    (hg : T.gen = U.gen) (hs : T.spec = U.spec) (hc : HEq T.chr U.chr)
    (hh : HEq T.hatMap U.hatMap) (hr : HEq T.residueMap U.residueMap) : T = U := by
  obtain ⟨g, s, hsp, c, hm, hcont, r, c1, c2⟩ := T
  obtain ⟨g', s', hsp', c', hm', hcont', r', c1', c2'⟩ := U
  cases hg
  cases hs
  cases hc
  cases hh
  cases hr
  rfl

theorem DeningerCompletedHatTriple.ext' {T U : DeningerCompletedHatTriple X O p}
    (hg : T.gen = U.gen) (hs : T.spec = U.spec) (hh : HEq T.hatMap U.hatMap) : T = U := by
  obtain ⟨g, s, hsp, hm, hcont, p1, p2⟩ := T
  obtain ⟨g', s', hsp', hm', hcont', p1', p2'⟩ := U
  cases hg
  cases hs
  cases hh
  rfl

variable
  (hratioAll : ∀ (a b : X) (h : a ⤳ b) (t : Perfection (X.residueField a) p),
    ∃ fs : Perfection (DeningerClosureLocalRing h) p × Perfection (DeningerClosureLocalRing h) p,
      fs.2 ≠ 0 ∧ t * deningerPerfEvalGen h p fs.2 = deningerPerfEvalGen h p fs.1)
  (hlamAll : ∀ (a b : X) (h : a ⤳ b), Function.Surjective (deningerPerfEvalSpec h p))

/-- **Deninger, Proposition 14.11 (`t1213nn`).**  If every element of `lim_{()^p} κ (x)` is a ratio
of elements of `lim_{()^p} 𝒪_{closure {x},y}` and evaluation at `y` is surjective on perfections,
then a completed `𝒪`-valued point is the same thing as a continuous pointed multiplicative map
`P̂_y` satisfying Deninger's conditions 1) and 2). -/
def deningerCompletedTripleEquiv :
    DeningerCompletedCharTriple X O p ≃ DeningerCompletedHatTriple X O p where
  toFun T := T.toHatTriple
  invFun T := T.toCharTriple (hratioAll T.gen T.spec T.specializes)
    (hlamAll T.gen T.spec T.specializes)
  left_inv T := by
    refine DeningerCompletedCharTriple.ext' rfl rfl (heq_of_eq ?_) (heq_of_eq rfl)
      (heq_of_eq ?_)
    · have hunique : gwzExtendByZero T.chr
          = T.toHatTriple.genMap (hratioAll T.gen T.spec T.specializes) := by
        refine gwzRatioExtend_unique _ _ _ _ _ _ fun f => ?_
        exact (T.comm_gen f).symm
      show gwzPointedEquivChar (T.toHatTriple.genMap
        (hratioAll T.gen T.spec T.specializes)) = T.chr
      rw [← hunique]
      exact gwzPointedEquivChar.right_inv T.chr
    · refine MonoidWithZeroHom.ext fun t => ?_
      obtain ⟨f, rfl⟩ := hlamAll T.gen T.spec T.specializes t
      exact (T.toHatTriple.residueFun_apply (hlamAll T.gen T.spec T.specializes) f).trans
        (T.comm_spec f)
  right_inv T := DeningerCompletedHatTriple.ext' rfl rfl (heq_of_eq rfl)

end

end RHTower