import GaloisForLFunctions.RHTower.DeningerFiniteFrobeniusOrbitEvaluationSpan
import Mathlib.RingTheory.ZMod.UnitsCyclic

/-!
# Directed finite Frobenius-evaluation system

Fix an integer `p`.  Finite prime-to-`p` cyclotomic stages are ordered by divisibility of their
moduli.  Reduction along `n ∣ m` sends `p mod m` to `p mod n`, hence descends to a surjection

`(ZMod m)ˣ / ⟨p⟩ → (ZMod n)ˣ / ⟨p⟩`.

Pullback therefore embeds the entire function space at the smaller stage into the function space
at the larger stage.  These embeddings compose exactly.  The system is directed: the product of
two stage moduli is a common upper stage.

The final compatibility theorem identifies the root index under a transition.  If `n ∣ m`, the
evaluation indexed by `j mod n` pulls back to the evaluation indexed by `(m / n)j mod m`.  Thus
the categorical transition maps are the actual transition maps of cyclotomic root evaluations,
not an abstract finite-dimensional replacement.

This module constructs the exact filtered finite source system.  Identifying its limit with the
full literal packet quotient is a separate profinite cofinality theorem.
-/

namespace RHTower

open scoped BigOperators

noncomputable section

/-- A nonzero cyclotomic modulus prime to `p`. -/
structure DeningerFiniteFrobeniusStage (p : ℕ) where
  modulus : ℕ
  modulus_ne_zero : modulus ≠ 0
  coprime : p.Coprime modulus

instance (p : ℕ) (s : DeningerFiniteFrobeniusStage p) :
    NeZero s.modulus :=
  ⟨s.modulus_ne_zero⟩

/-- Divisibility order on prime-to-`p` cyclotomic stages. -/
instance (p : ℕ) : PartialOrder (DeningerFiniteFrobeniusStage p) where
  le s t := s.modulus ∣ t.modulus
  le_refl s := dvd_refl s.modulus
  le_trans _ _ _ := dvd_trans
  le_antisymm s t hst hts := by
    cases s with
    | mk sn sn0 sp =>
      cases t with
      | mk tn tn0 tp =>
        simp only at hst hts
        have hnt : sn = tn := Nat.dvd_antisymm hst hts
        subst tn
        rfl

/-- Products give common upper stages, so the cyclotomic stage order is directed. -/
instance (p : ℕ) : IsDirectedOrder (DeningerFiniteFrobeniusStage p) := by
  constructor
  intro s t
  let u : DeningerFiniteFrobeniusStage p :=
    ⟨s.modulus * t.modulus,
      mul_ne_zero s.modulus_ne_zero t.modulus_ne_zero,
      s.coprime.mul_right t.coprime⟩
  exact
    ⟨u, dvd_mul_right s.modulus t.modulus,
      dvd_mul_left t.modulus s.modulus⟩

/-- Finite Frobenius packet at one prime-to-`p` cyclotomic stage. -/
abbrev DeningerFiniteFrobeniusStageQuotient
    (p : ℕ) (s : DeningerFiniteFrobeniusStage p) :=
  (ZMod s.modulus)ˣ ⧸
    deningerFiniteFrobeniusSubgroup p s.modulus s.coprime

noncomputable instance
    (p : ℕ) (s : DeningerFiniteFrobeniusStage p) :
    Fintype (DeningerFiniteFrobeniusStageQuotient p s) :=
  deningerFiniteFrobeniusQuotientFintype
    p s.modulus s.coprime

/-- Reduction of unit groups along a divisibility transition. -/
def deningerFiniteFrobeniusStageReduction
    {p : ℕ} {s t : DeningerFiniteFrobeniusStage p} (h : s ≤ t) :
    (ZMod t.modulus)ˣ →* (ZMod s.modulus)ˣ :=
  ZMod.unitsMap h

/-- Unit reduction at every stage transition is surjective. -/
theorem deningerFiniteFrobeniusStageReduction_surjective
    {p : ℕ} {s t : DeningerFiniteFrobeniusStage p} (h : s ≤ t) :
    Function.Surjective (deningerFiniteFrobeniusStageReduction h) :=
  ZMod.unitsMap_surjective h

/-- Reduction sends the larger-stage arithmetic Frobenius to the smaller-stage Frobenius. -/
theorem deningerFiniteFrobeniusStageReduction_frobenius
    {p : ℕ} {s t : DeningerFiniteFrobeniusStage p} (h : s ≤ t) :
    deningerFiniteFrobeniusStageReduction h
        (ZMod.unitOfCoprime p t.coprime) =
      ZMod.unitOfCoprime p s.coprime := by
  apply Units.ext
  simp [deningerFiniteFrobeniusStageReduction,
    ZMod.unitsMap, ZMod.unitOfCoprime]

/-- Unit reductions compose exactly. -/
theorem deningerFiniteFrobeniusStageReduction_comp
    {p : ℕ} {r s t : DeningerFiniteFrobeniusStage p}
    (hrs : r ≤ s) (hst : s ≤ t) :
    (deningerFiniteFrobeniusStageReduction hrs).comp
        (deningerFiniteFrobeniusStageReduction hst) =
      deningerFiniteFrobeniusStageReduction (hrs.trans hst) :=
  ZMod.unitsMap_comp hrs hst

/-- Frobenius subgroups map into Frobenius subgroups under stage reduction. -/
theorem deningerFiniteFrobeniusSubgroup_le_stageReduction_comap
    {p : ℕ} {s t : DeningerFiniteFrobeniusStage p} (h : s ≤ t) :
    deningerFiniteFrobeniusSubgroup p t.modulus t.coprime ≤
      Subgroup.comap (deningerFiniteFrobeniusStageReduction h)
        (deningerFiniteFrobeniusSubgroup p s.modulus s.coprime) := by
  change Subgroup.zpowers (ZMod.unitOfCoprime p t.coprime) ≤
    Subgroup.comap (deningerFiniteFrobeniusStageReduction h)
      (Subgroup.zpowers (ZMod.unitOfCoprime p s.coprime))
  rw [Subgroup.zpowers_le]
  change deningerFiniteFrobeniusStageReduction h
      (ZMod.unitOfCoprime p t.coprime) ∈
    Subgroup.zpowers (ZMod.unitOfCoprime p s.coprime)
  rw [deningerFiniteFrobeniusStageReduction_frobenius]
  exact Subgroup.mem_zpowers _

/-- Surjective transition map between finite Frobenius packet quotients. -/
noncomputable def deningerFiniteFrobeniusStageQuotientMap
    {p : ℕ} {s t : DeningerFiniteFrobeniusStage p} (h : s ≤ t) :
    DeningerFiniteFrobeniusStageQuotient p t →*
      DeningerFiniteFrobeniusStageQuotient p s :=
  QuotientGroup.map
    (deningerFiniteFrobeniusSubgroup p t.modulus t.coprime)
    (deningerFiniteFrobeniusSubgroup p s.modulus s.coprime)
    (deningerFiniteFrobeniusStageReduction h)
    (deningerFiniteFrobeniusSubgroup_le_stageReduction_comap h)

/-- Every finite quotient transition is surjective. -/
theorem deningerFiniteFrobeniusStageQuotientMap_surjective
    {p : ℕ} {s t : DeningerFiniteFrobeniusStage p} (h : s ≤ t) :
    Function.Surjective (deningerFiniteFrobeniusStageQuotientMap h) := by
  intro q
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨u, hu⟩ :=
    deningerFiniteFrobeniusStageReduction_surjective h v
  refine
    ⟨(QuotientGroup.mk u :
        DeningerFiniteFrobeniusStageQuotient p t), ?_⟩
  rw [deningerFiniteFrobeniusStageQuotientMap,
    QuotientGroup.map_mk, hu]

/-- Finite quotient transitions compose exactly. -/
theorem deningerFiniteFrobeniusStageQuotientMap_comp
    {p : ℕ} {r s t : DeningerFiniteFrobeniusStage p}
    (hrs : r ≤ s) (hst : s ≤ t) :
    (deningerFiniteFrobeniusStageQuotientMap hrs).comp
        (deningerFiniteFrobeniusStageQuotientMap hst) =
      deningerFiniteFrobeniusStageQuotientMap (hrs.trans hst) := by
  apply QuotientGroup.monoidHom_ext
  ext u
  simp only [MonoidHom.coe_comp, Function.comp_apply,
    deningerFiniteFrobeniusStageQuotientMap,
    QuotientGroup.map_mk']
  rw [QuotientGroup.map_mk]
  exact congrArg QuotientGroup.mk
    (DFunLike.congr_fun
      (deningerFiniteFrobeniusStageReduction_comp hrs hst) u)

/-- Pullback embeds functions contravariantly along a quotient transition. -/
noncomputable def deningerFiniteFrobeniusStageFunctionPullback
    {p : ℕ} {s t : DeningerFiniteFrobeniusStage p} (h : s ≤ t) :
    (DeningerFiniteFrobeniusStageQuotient p s → ℂ) →ₗ[ℂ]
      (DeningerFiniteFrobeniusStageQuotient p t → ℂ) where
  toFun F := F ∘ deningerFiniteFrobeniusStageQuotientMap h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Pullback is injective because the underlying finite quotient transition is surjective. -/
theorem deningerFiniteFrobeniusStageFunctionPullback_injective
    {p : ℕ} {s t : DeningerFiniteFrobeniusStage p} (h : s ≤ t) :
    Function.Injective
      (deningerFiniteFrobeniusStageFunctionPullback h) := by
  intro F G hFG
  funext q
  obtain ⟨r, hr⟩ :=
    deningerFiniteFrobeniusStageQuotientMap_surjective h q
  have hpoint := congrFun hFG r
  simpa [deningerFiniteFrobeniusStageFunctionPullback, hr] using hpoint

/-- Function pullbacks compose exactly in the covariant stage order. -/
theorem deningerFiniteFrobeniusStageFunctionPullback_comp
    {p : ℕ} {r s t : DeningerFiniteFrobeniusStage p}
    (hrs : r ≤ s) (hst : s ≤ t) :
    (deningerFiniteFrobeniusStageFunctionPullback hst).comp
        (deningerFiniteFrobeniusStageFunctionPullback hrs) =
      deningerFiniteFrobeniusStageFunctionPullback (hrs.trans hst) := by
  ext F q
  change F (deningerFiniteFrobeniusStageQuotientMap hrs
      (deningerFiniteFrobeniusStageQuotientMap hst q)) =
    F (deningerFiniteFrobeniusStageQuotientMap (hrs.trans hst) q)
  rw [← MonoidHom.comp_apply,
    deningerFiniteFrobeniusStageQuotientMap_comp hrs hst]

/-- Inflation of an additive root index from modulus `n` to a divisible modulus `m`. -/
def deningerFiniteFrobeniusStageIndexInflation
    {p : ℕ} {s t : DeningerFiniteFrobeniusStage p} (_h : s ≤ t)
    (j : ZMod s.modulus) : ZMod t.modulus :=
  ((t.modulus / s.modulus) * j.val : ℕ)

/-- **Exact root-evaluation transition law.**  Pulling an evaluation from modulus `n` back to
modulus `m` is the evaluation at the inflated index `(m / n)j`. -/
theorem deningerFiniteUnitEvaluation_stageReduction
    {p : ℕ} {s t : DeningerFiniteFrobeniusStage p} (h : s ≤ t)
    (j : ZMod s.modulus) (u : (ZMod t.modulus)ˣ) :
    deningerFiniteUnitEvaluation s.modulus j
        (deningerFiniteFrobeniusStageReduction h u) =
      deningerFiniteUnitEvaluation t.modulus
        (deningerFiniteFrobeniusStageIndexInflation h j) u := by
  have hlow :
      j * ((deningerFiniteFrobeniusStageReduction h u :
          (ZMod s.modulus)ˣ) : ZMod s.modulus) =
        ((j.val * (u : ZMod t.modulus).val : ℕ) :
          ZMod s.modulus) := by
    calc
      j * ((deningerFiniteFrobeniusStageReduction h u :
          (ZMod s.modulus)ˣ) : ZMod s.modulus) =
          (j.val : ZMod s.modulus) *
            ZMod.cast (u : ZMod t.modulus) := by
        congr 1
        exact (ZMod.natCast_zmod_val j).symm
      _ = (j.val : ZMod s.modulus) *
          ((u : ZMod t.modulus).val : ZMod s.modulus) := by
        congr 1
        rw [← ZMod.natCast_zmod_val (u : ZMod t.modulus)]
        simp
      _ = ((j.val * (u : ZMod t.modulus).val : ℕ) :
          ZMod s.modulus) := by
        rw [Nat.cast_mul]
  have hhigh :
      deningerFiniteFrobeniusStageIndexInflation h j *
          (u : ZMod t.modulus) =
        (((t.modulus / s.modulus) * j.val *
            (u : ZMod t.modulus).val : ℕ) :
          ZMod t.modulus) := by
    rw [← ZMod.natCast_zmod_val (u : ZMod t.modulus)]
    simp [deningerFiniteFrobeniusStageIndexInflation]
  rw [deningerFiniteUnitEvaluation, deningerFiniteUnitEvaluation,
    hlow, hhigh]
  have stdAddChar_nat (N a : ℕ) [NeZero N] :
      ZMod.stdAddChar (a : ZMod N) =
        Complex.exp (2 * Real.pi * Complex.I * a / N) := by
    change ↑(ZMod.toCircle (a : ZMod N)) =
      Complex.exp (2 * Real.pi * Complex.I * a / N)
    rw [ZMod.toCircle_natCast]
  rw [stdAddChar_nat, stdAddChar_nat]
  have hfactor :
      s.modulus * (t.modulus / s.modulus) = t.modulus :=
    Nat.mul_div_cancel' h
  have hs : (s.modulus : ℂ) ≠ 0 := by
    exact_mod_cast s.modulus_ne_zero
  have ht : (t.modulus : ℂ) ≠ 0 := by
    exact_mod_cast t.modulus_ne_zero
  congr 1
  push_cast
  field_simp
  have hfactorC :
      (s.modulus : ℂ) * (t.modulus / s.modulus : ℕ) =
        (t.modulus : ℂ) := by
    exact_mod_cast hfactor
  rw [← hfactorC]
  ring

/-- Every function pulled from a smaller finite packet is again an exact finite linear
combination of orbit root evaluations at the larger stage. -/
theorem deningerFiniteFrobeniusStageFunctionPullback_orbitEvaluation_span
    {p : ℕ} {s t : DeningerFiniteFrobeniusStage p} (h : s ≤ t)
    (F : DeningerFiniteFrobeniusStageQuotient p s → ℂ) :
    ∃ c : ZMod t.modulus → ℂ,
      ∀ q : DeningerFiniteFrobeniusStageQuotient p t,
        deningerFiniteFrobeniusStageFunctionPullback h F q =
          ∑ j : ZMod t.modulus,
            c j * deningerFiniteFrobeniusOrbitEvaluation
              p t.modulus t.coprime j q :=
  deningerFiniteFrobeniusOrbitEvaluation_span
    p t.modulus t.coprime
    (deningerFiniteFrobeniusStageFunctionPullback h F)

end

end RHTower
