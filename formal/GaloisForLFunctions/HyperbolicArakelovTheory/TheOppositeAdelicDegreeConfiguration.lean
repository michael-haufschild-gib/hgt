import GaloisForLFunctions.HyperbolicArakelovTheory.CarriersWithAClosedDegreeGeodesic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# Finite Weyl conjugation retains the degree configuration

The rational diagonal group embeds discretely in
`SL₂(ℂ) × ∏'_p SL₂(ℚ_p)`. Finite vertices are actual cosets of `SL₂(ℤ_p)`,
with finite support away from the standard vertex. On this quotient, writing
`g_q = diag(q,q⁻¹)`, the split degree configuration has the exact normal form

  `[(z_{(ab)²}, (g_{a/b}K_p)_p)] = [(z_{b⁴}, (K_p)_p)]`.

Two such classes coincide exactly when their opposite factors `b` coincide.
Thus principal orientation collapses all square degrees, whereas opposite
finite orientation separates them. Conjugating the arithmetic group by the
finite integral Weyl element transfers this separation to the original degree
points themselves. Both arithmetic embeddings and their discreteness are proved.

The construction uses the determinant-one local vertex spaces and establishes
orbit geometry on square degrees. It asserts no Green function or Robin identity.
-/

set_option autoImplicit false
noncomputable section
open Matrix Set
namespace GaloisForLFunctions.HyperbolicArakelovTheory.OppositeAdelic
open SurfaceOfSpecZ

abbrev RationalGroup := SpecialLinearGroup (Fin 2) ℚ
local instance (p : {p : ℕ // p.Prime}) : Fact p.1.Prime := ⟨p.2⟩
abbrev LocalGroup (p : {p : ℕ // p.Prime}) := SpecialLinearGroup (Fin 2) ℚ_[p.1]

def archMap : RationalGroup →* SL2C :=
  SpecialLinearGroup.map (Rat.castHom ℂ)

def localMap (p : {p : ℕ // p.Prime}) : RationalGroup →* LocalGroup p :=
  SpecialLinearGroup.map (Rat.castHom ℚ_[p.1])

/-- Stabilizer of the standard determinant-one lattice at a finite place. -/
def integralLocalGroup (p : {p : ℕ // p.Prime}) : Subgroup (LocalGroup p) where
  carrier := {g | ∀ i j, g i j ∈ PadicInt.subring p.1}
  one_mem' := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  mul_mem' := by
    intro g h hg hh i j
    change (g.1 * h.1) i j ∈ PadicInt.subring p.1
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    exact (PadicInt.subring p.1).add_mem
      ((PadicInt.subring p.1).mul_mem (hg i 0) (hh 0 j))
      ((PadicInt.subring p.1).mul_mem (hg i 1) (hh 1 j))
  inv_mem' := by
    intro g hg i j
    change g.1.adjugate i j ∈ PadicInt.subring p.1
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · exact hg 1 1
    · exact (PadicInt.subring p.1).neg_mem (hg 0 1)
    · exact (PadicInt.subring p.1).neg_mem (hg 1 0)
    · exact hg 0 0

abbrev LocalVertex (p : {p : ℕ // p.Prime}) := LocalGroup p ⧸ integralLocalGroup p
def baseVertex (p : {p : ℕ // p.Prime}) : LocalVertex p := QuotientGroup.mk 1
def principalVertex (g : RationalGroup) (p : {p : ℕ // p.Prime}) : LocalVertex p :=
  QuotientGroup.mk (localMap p g)

theorem padicNorm_le_one_of_den_not_dvd (q : ℚ) (p : {p : ℕ // p.Prime})
    (hp : ¬p.1 ∣ q.den) : padicNorm p.1 q ≤ 1 := by
  conv_lhs => rw [← Rat.num_div_den q]
  rw [padicNorm.div, (padicNorm.nat_eq_one_iff (p := p.1) q.den).mpr hp, div_one]
  exact padicNorm.of_int q.num

/-- A rational number integral at every finite place is an integer. -/
theorem integer_of_all_local_norm_le_one (q : ℚ)
    (hq : ∀ p : {p : ℕ // p.Prime}, ‖(q : ℚ_[p.1])‖ ≤ 1) : ∃ z : ℤ, q = z := by
  have hd : q.den = 1 := by
    by_contra hden
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hden
    let pp : {p : ℕ // p.Prime} := ⟨p, hp⟩
    letI : Fact p.Prime := ⟨hp⟩
    have hpn : ¬(p : ℤ) ∣ q.num := by
      intro h
      have hn : p ∣ q.num.natAbs := Int.natCast_dvd.mp h
      have hg := Nat.dvd_gcd hn hpd
      rw [q.reduced.gcd_eq_one] at hg
      exact hp.not_dvd_one hg
    have hn : padicNorm p (q.num : ℚ) = 1 := (padicNorm.int_eq_one_iff q.num).mpr hpn
    have hdlt : padicNorm p (q.den : ℚ) < 1 := (padicNorm.nat_lt_one_iff q.den).mpr hpd
    have hle : padicNorm p q ≤ 1 := by
      have h := hq pp
      rw [Padic.eq_padicNorm] at h
      exact_mod_cast h
    have hm : q * (q.den : ℚ) = q.num := by
      calc
        q * (q.den : ℚ) = (q.num : ℚ) / q.den * q.den :=
          congrArg (fun x : ℚ => x * (q.den : ℚ)) (Rat.num_div_den q).symm
        _ = q.num := div_mul_cancel₀ _ (show (q.den : ℚ) ≠ 0 by exact_mod_cast q.den_ne_zero)
    have he := congrArg (padicNorm p) hm
    rw [padicNorm.mul, hn] at he
    have hprod := mul_le_mul_of_nonneg_right hle (padicNorm.nonneg (p := p) (q.den : ℚ))
    rw [he, one_mul] at hprod
    exact (not_lt_of_ge hprod) hdlt
  refine ⟨q.num, ?_⟩
  conv_lhs => rw [← Rat.num_div_den q]
  simp only [hd, Nat.cast_one, div_one]

/-- Only denominator primes can move the standard integral lattice. -/
theorem finite_bad_places (q : ℚ) :
    {p : {p : ℕ // p.Prime} | ¬‖(q : ℚ_[p.1])‖ ≤ 1}.Finite := by
  have hb : {p : {p : ℕ // p.Prime} | p.1 ≤ q.den}.Finite :=
    (Set.finite_Iic q.den).preimage Subtype.val_injective.injOn
  apply hb.subset
  intro p hp
  have hpd : p.1 ∣ q.den := by
    by_contra h
    apply hp
    rw [Padic.eq_padicNorm]
    exact_mod_cast padicNorm_le_one_of_den_not_dvd q p h
  exact Nat.le_of_dvd q.den_pos hpd

theorem principalVertex_finite_support (g : RationalGroup) :
    {p | principalVertex g p ≠ baseVertex p}.Finite := by
  have hf : (⋃ i : Fin 2, ⋃ j : Fin 2,
      {p : {p : ℕ // p.Prime} | ¬‖((g i j : ℚ) : ℚ_[p.1])‖ ≤ 1}).Finite :=
    Set.finite_iUnion fun i => Set.finite_iUnion fun j => finite_bad_places (g i j)
  apply hf.subset
  intro p hp
  by_contra h
  apply hp
  have hg : localMap p g ∈ integralLocalGroup p := by
    intro i j
    change ‖((g i j : ℚ) : ℚ_[p.1])‖ ≤ 1
    by_contra hij
    exact h (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨j, hij⟩⟩)
  apply QuotientGroup.eq.mpr
  simpa only [mul_one] using (integralLocalGroup p).inv_mem hg

/-- Finite-support vertices in the product of the even local buildings. -/
def FiniteVertices := {v : ∀ p : {p : ℕ // p.Prime}, LocalVertex p //
  {p | v p ≠ baseVertex p}.Finite}

/-- The restricted product of vertex sets with singleton base sets has discrete topology. -/
instance : TopologicalSpace FiniteVertices := ⊥
instance : DiscreteTopology FiniteVertices := ⟨rfl⟩

def finiteBase : FiniteVertices := ⟨baseVertex, by simp⟩
def finitePoint (g : RationalGroup) : FiniteVertices :=
  ⟨principalVertex g, principalVertex_finite_support g⟩

theorem local_smul_base (g : RationalGroup) (p : {p : ℕ // p.Prime}) :
    localMap p g • baseVertex p = principalVertex g p := by
  simp [baseVertex, principalVertex]

instance : MulAction RationalGroup FiniteVertices where
  smul g v := ⟨fun p => localMap p g • v.1 p, by
    apply (v.2.union (principalVertex_finite_support g)).subset
    intro p hp
    by_contra h
    have hh : v.1 p = baseVertex p ∧ principalVertex g p = baseVertex p := by
      simpa only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] using h
    apply hp
    change localMap p g • v.1 p = baseVertex p
    rw [hh.1, local_smul_base, hh.2]⟩
  one_smul v := by
    apply Subtype.ext
    funext p
    change localMap p 1 • v.1 p = v.1 p
    rw [map_one, one_smul]
  mul_smul g h v := by
    apply Subtype.ext
    funext p
    change localMap p (g * h) • v.1 p = localMap p g • (localMap p h • v.1 p)
    rw [map_mul, mul_smul]

instance : MulAction RationalGroup H3 := MulAction.compHom H3 archMap
instance : ContinuousConstSMul RationalGroup H3 := ⟨fun g => continuous_h3Act (archMap g)⟩
instance : ContinuousConstSMul RationalGroup FiniteVertices :=
  ⟨fun _ => continuous_of_discreteTopology⟩

abbrev GlobalSpace := H3 × FiniteVertices
abbrev Carrier := Quotient (MulAction.orbitRel RationalGroup GlobalSpace)

theorem finite_smul_base (g : RationalGroup) : g • finiteBase = finitePoint g := by
  apply Subtype.ext
  funext p
  exact local_smul_base g p

theorem finitePoint_one : finitePoint 1 = finiteBase := by
  apply Subtype.ext
  funext p
  simp [finitePoint, principalVertex, finiteBase, baseVertex]

theorem finite_smul_point (g h : RationalGroup) :
    g • finitePoint h = finitePoint (g * h) := by
  rw [← finite_smul_base, ← mul_smul, finite_smul_base]

theorem fixes_finiteBase_iff (g : RationalGroup) :
    g • finiteBase = finiteBase ↔ ∀ p, localMap p g ∈ integralLocalGroup p := by
  constructor
  · intro h p
    have hp := congrArg (fun v : FiniteVertices => v.1 p) h
    change localMap p g • baseVertex p = baseVertex p at hp
    rw [local_smul_base] at hp
    have hi : (localMap p g)⁻¹ ∈ integralLocalGroup p := by
      simpa only [mul_one] using QuotientGroup.eq.mp hp
    exact (integralLocalGroup p).inv_mem_iff.mp hi
  · intro h
    rw [finite_smul_base]
    apply Subtype.ext
    funext p
    apply QuotientGroup.eq.mpr
    simpa only [mul_one] using (integralLocalGroup p).inv_mem (h p)

private theorem intCast_norm_sq_ge_one (z : ℤ) (hz : z ≠ 0) :
    1 ≤ ‖(z : ℂ)‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.intCast_re, Complex.intCast_im,
    mul_zero, add_zero]
  have h : (1 : ℤ) ≤ z ^ 2 :=
    (one_le_sq_iff_one_le_abs z).mpr (Int.one_le_abs hz)
  exact_mod_cast (by simpa only [pow_two] using h : (1 : ℤ) ≤ z * z)

/-- Integral rational matrices do not increase the height of the degree ray above one. -/
theorem integral_height_le (g : RationalGroup)
    (hg : ∀ p, localMap p g ∈ integralLocalGroup p)
    (t : ℝ) (ht : 0 < t) (ht1 : 1 ≤ t) :
    (h3Act (archMap g) (degPoint t ht)).t ≤ t := by
  obtain ⟨c, hc⟩ := integer_of_all_local_norm_le_one (g 1 0)
    (fun p => hg p 1 0)
  obtain ⟨d, hd⟩ := integer_of_all_local_norm_le_one (g 1 1)
    (fun p => hg p 1 1)
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h
    push Not at h
    have he := g.prop
    rw [Matrix.det_fin_two, hc, hd, h.1, h.2, Int.cast_zero,
      mul_zero, mul_zero, sub_zero] at he
    exact zero_ne_one he
  have hcC : (archMap g).1 1 0 = (c : ℂ) := by
    change ((g 1 0 : ℚ) : ℂ) = _
    rw [hc, Rat.cast_intCast]
  have hdC : (archMap g).1 1 1 = (d : ℂ) := by
    change ((g 1 1 : ℚ) : ℂ) = _
    rw [hd, Rat.cast_intCast]
  have hD : 1 ≤ h3Denom (archMap g) (degPoint t ht) := by
    simp only [h3Denom, degPoint, mul_zero, zero_add, hcC, hdC]
    rcases hcd with hc0 | hd0
    · have hs := one_le_mul_of_one_le_of_one_le
        (intCast_norm_sq_ge_one c hc0) (one_le_pow₀ ht1 : 1 ≤ t ^ 2)
      linarith only [hs, sq_nonneg ‖(d : ℂ)‖]
    · have hs := intCast_norm_sq_ge_one d hd0
      have hn : 0 ≤ ‖(c : ℂ)‖ ^ 2 * t ^ 2 := by positivity
      linarith only [hs, hn]
  rw [h3Act_t]
  exact div_le_self ht.le hD

/-- Distinct heights at least one remain distinct modulo the global finite stabilizer. -/
theorem integral_degree_height_rigid (g : RationalGroup)
    (hg : ∀ p, localMap p g ∈ integralLocalGroup p)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (ht1 : 1 ≤ t) (hu1 : 1 ≤ u)
    (he : h3Act (archMap g) (degPoint t ht) = degPoint u hu) : t = u := by
  have hle := integral_height_le g hg t ht ht1
  rw [he] at hle
  have hgi : ∀ p, localMap p g⁻¹ ∈ integralLocalGroup p := by
    intro p
    rw [map_inv]
    exact (integralLocalGroup p).inv_mem (hg p)
  have hei : h3Act (archMap g⁻¹) (degPoint u hu) = degPoint t ht := by
    rw [← he, map_inv, ← h3Act_mul, inv_mul_cancel, h3Act_one]
  have hge := integral_height_le g⁻¹ hgi u hu hu1
  rw [hei] at hge
  exact le_antisymm hge hle

def classOf (z : H3) (g : RationalGroup) : Carrier :=
  Quotient.mk _ (z, finitePoint g)

/-- Normalization of the rational finite fibre is an actual diagonal-group orbit identity. -/
theorem classOf_normal_form (z : H3) (g : RationalGroup) :
    classOf z g = classOf (h3Act (archMap g⁻¹) z) 1 := by
  apply Quotient.sound
  refine ⟨g, ?_⟩
  apply Prod.ext
  · change h3Act (archMap g) (h3Act (archMap g⁻¹) z) = z
    rw [map_inv, ← h3Act_mul, mul_inv_cancel, h3Act_one]
  · change g • finitePoint 1 = finitePoint g
    rw [finite_smul_point, mul_one]

theorem base_degree_classes_eq_iff {t u : ℝ} (ht : 0 < t) (hu : 0 < u)
    (ht1 : 1 ≤ t) (hu1 : 1 ≤ u) :
    classOf (degPoint t ht) 1 = classOf (degPoint u hu) 1 ↔ t = u := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Quotient.exact h
    have hfin : g • finiteBase = finiteBase := by
      have hf := congrArg Prod.snd hg
      simpa only [Prod.smul_snd, finitePoint_one] using hf
    have harch : h3Act (archMap g) (degPoint u hu) = degPoint t ht :=
      congrArg Prod.fst hg
    exact (integral_degree_height_rigid g ((fixes_finiteBase_iff g).mp hfin)
      hu ht hu1 ht1 harch).symm
  · intro h
    subst u
    rfl


open scoped RestrictedProduct

theorem principalVertex_eq_base_iff (g : RationalGroup) (p : {p : ℕ // p.Prime}) :
    principalVertex g p = baseVertex p ↔ localMap p g ∈ integralLocalGroup p := by
  change (QuotientGroup.mk (localMap p g) : LocalVertex p) = QuotientGroup.mk 1 ↔ _
  rw [QuotientGroup.eq, mul_one, Subgroup.inv_mem_iff]

/-- The rational diagonal belongs to the genuine restricted product at all finite places. -/
abbrev FiniteAdelicGroup := Πʳ p : {p : ℕ // p.Prime}, [LocalGroup p, integralLocalGroup p]
abbrev AdelicGroup := SL2C × FiniteAdelicGroup

def arithmeticEmbedding : RationalGroup →* AdelicGroup where
  toFun g := (archMap g, ⟨fun p => localMap p g, by
    rw [Filter.eventually_cofinite]
    change {p | localMap p g ∉ integralLocalGroup p}.Finite
    simpa only [ne_eq, principalVertex_eq_base_iff] using principalVertex_finite_support g⟩)
  map_one' := by
    apply Prod.ext
    · exact map_one archMap
    · apply RestrictedProduct.ext
      intro p
      exact map_one (localMap p)
  map_mul' g h := by
    apply Prod.ext
    · exact map_mul archMap g h
    · apply RestrictedProduct.ext
      intro p
      exact map_mul (localMap p) g h

theorem arithmeticEmbedding_injective : Function.Injective arithmeticEmbedding := by
  intro g h he
  apply Subtype.ext
  ext i j
  apply Rat.cast_injective (α := ℂ)
  exact congrArg (fun a : AdelicGroup => a.1.1 i j) he

def arithmeticGroup : Subgroup AdelicGroup := arithmeticEmbedding.range

theorem integralLocalGroup_isOpen (p : {p : ℕ // p.Prime}) :
    IsOpen (integralLocalGroup p : Set (LocalGroup p)) := by
  have hs : IsOpen (PadicInt.subring p.1 : Set ℚ_[p.1]) := by
    change IsOpen {y : ℚ_[p.1] | ‖y‖ ≤ 1}
    simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
      IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p.1]) one_ne_zero
  change IsOpen {g : LocalGroup p | ∀ i j, g i j ∈ PadicInt.subring p.1}
  simp only [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro j
  exact hs.preimage ((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val))

private theorem int_eq_zero_of_complex_norm_lt_one (z : ℤ) (hz : ‖(z : ℂ)‖ < 1) : z = 0 := by
  by_contra hne
  have hs := intCast_norm_sq_ge_one z hne
  nlinarith only [hs, hz, norm_nonneg (z : ℂ)]

/-- Integrality at all finite places and an archimedean unit neighbourhood isolate the identity. -/
theorem integral_near_identity_eq_one (g : RationalGroup)
    (hg : ∀ p, localMap p g ∈ integralLocalGroup p)
    (hnear : ∀ i j, ‖(archMap g).1 i j - (1 : SL2C).1 i j‖ < 1) : g = 1 := by
  apply Subtype.ext
  ext i j
  obtain ⟨z, hz⟩ := integer_of_all_local_norm_le_one (g i j) (fun p => hg p i j)
  have hn := hnear i j
  change ‖((g i j : ℚ) : ℂ) - (1 : Matrix (Fin 2) (Fin 2) ℂ) i j‖ < 1 at hn
  rw [hz, Rat.cast_intCast, Matrix.one_apply] at hn
  change g i j = (1 : Matrix (Fin 2) (Fin 2) ℚ) i j
  rw [hz, Matrix.one_apply]
  by_cases hij : i = j
  · simp only [if_pos hij] at hn ⊢
    have he : z - 1 = 0 := int_eq_zero_of_complex_norm_lt_one (z - 1)
      (by simpa only [Int.cast_sub, Int.cast_one] using hn)
    have hz1 : z = 1 := sub_eq_zero.mp he
    simp only [hz1, Int.cast_one]
  · simp only [if_neg hij, sub_zero] at hn ⊢
    rw [int_eq_zero_of_complex_norm_lt_one z hn, Int.cast_zero]

local instance : Fact (∀ p, IsOpen (integralLocalGroup p : Set (LocalGroup p))) :=
  ⟨integralLocalGroup_isOpen⟩

/-- The diagonal rational group is discrete in the actual archimedean--finite restricted product. -/
instance arithmeticGroup_discrete : DiscreteTopology arithmeticGroup := by
  apply discreteTopology_of_isOpen_singleton_one
  let U : Set AdelicGroup := {a | (∀ i j, ‖a.1.1 i j - (1 : SL2C).1 i j‖ < 1) ∧
    ∀ p, a.2 p ∈ integralLocalGroup p}
  have hc (i j : Fin 2) : Continuous (fun a : AdelicGroup => a.1.1 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp
      (continuous_subtype_val.comp continuous_fst))
  have hU : IsOpen U := by
    apply IsOpen.inter
    · have ho (i j : Fin 2) :
          IsOpen {a : AdelicGroup | ‖a.1.1 i j - (1 : SL2C).1 i j‖ < (1 : ℝ)} :=
        isOpen_lt ((hc i j).sub continuous_const).norm continuous_const
      have hh := isOpen_iInter_of_finite fun i : Fin 2 =>
        isOpen_iInter_of_finite fun j : Fin 2 => ho i j
      convert hh using 1
      ext a
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      rfl
    · exact (RestrictedProduct.isOpen_forall_mem integralLocalGroup_isOpen).preimage continuous_snd
  have he : (Subtype.val : arithmeticGroup → AdelicGroup) ⁻¹' U = {1} := by
    ext x
    constructor
    · intro hx
      obtain ⟨g, hg⟩ := x.property
      have hn : (∀ i j, ‖(archMap g).1 i j - (1 : SL2C).1 i j‖ < 1) ∧
          ∀ p, localMap p g ∈ integralLocalGroup p := by
        change (x : AdelicGroup) ∈ U at hx
        rw [← hg] at hx
        exact hx
      have hgone := integral_near_identity_eq_one g hn.2 hn.1
      apply Subtype.ext
      exact hg.symm.trans (by rw [hgone, map_one]; rfl)
    · intro hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨by intro i j; simp, fun p => (integralLocalGroup p).one_mem⟩
  rw [← he]
  exact hU.preimage continuous_subtype_val



/-- A rational diagonal element acts on the hyperbolic height by its squared norm. -/
def diagonal (q : ℚ) (hq : q ≠ 0) : RationalGroup :=
  ⟨!![q, 0; 0, q⁻¹], by simp [Matrix.det_fin_two, hq]⟩

theorem archMap_diagonal (q : ℚ) (hq : q ≠ 0) :
    archMap (diagonal q hq) = diagSL2 (q : ℂ) (by exact_mod_cast hq) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [archMap, diagonal, diagSL2,
    SpecialLinearGroup.map_apply_coe]

/-- Positive and opposite finite factors in the same squared degree. -/
def splitDegree (a b : ℕ+) : Carrier :=
  classOf
    (degPoint ((((a : ℕ) : ℝ) * (b : ℕ)) ^ 2)
      (sq_pos_of_pos (mul_pos (by exact_mod_cast a.pos) (by exact_mod_cast b.pos))))
    (diagonal (((a : ℕ) : ℚ) / (b : ℕ))
      (div_ne_zero (by exact_mod_cast a.ne_zero) (by exact_mod_cast b.ne_zero)))

/-- The finite factor with positive orientation cancels globally; the opposite factor
survives as fourth-power height in the integral fibre. -/
theorem splitDegree_normal_form (a b : ℕ+) :
    splitDegree a b = classOf
      (degPoint (((b : ℕ) : ℝ) ^ 4) (pow_pos (by exact_mod_cast b.pos) 4)) 1 := by
  unfold splitDegree
  rw [classOf_normal_form, map_inv, archMap_diagonal]
  have hq : (((a : ℕ) : ℚ) / (b : ℕ) : ℚ) ≠ 0 :=
    div_ne_zero (by exact_mod_cast a.ne_zero) (by exact_mod_cast b.ne_zero)
  have hqC : ((((a : ℕ) : ℚ) / (b : ℕ) : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hq
  have h := h3Act_inv_diag_pow hqC
    (t := (((a : ℕ) : ℝ) * (b : ℕ)) ^ 2)
    (sq_pos_of_pos (mul_pos (by exact_mod_cast a.pos) (by exact_mod_cast b.pos))) 1
  simp only [pow_one] at h
  rw [h]
  congr 1
  apply degPoint_eq
  simp only [Rat.cast_div, Rat.cast_natCast, norm_div, Complex.norm_natCast]
  have ha : ((a : ℕ) : ℝ) ≠ 0 := by exact_mod_cast a.ne_zero
  have hb : ((b : ℕ) : ℝ) ≠ 0 := by exact_mod_cast b.ne_zero
  field_simp [ha, hb]

/-- Exact orbit classification of all split-orientation square-degree configurations. -/
theorem splitDegree_eq_iff (a b c d : ℕ+) :
    splitDegree a b = splitDegree c d ↔ b = d := by
  rw [splitDegree_normal_form, splitDegree_normal_form,
    base_degree_classes_eq_iff]
  · constructor
    · intro h
      have he : ((b : ℕ) : ℝ) = ((d : ℕ) : ℝ) :=
        (pow_left_inj₀ (by positivity) (by positivity) (by decide : (4 : ℕ) ≠ 0)).mp h
      exact_mod_cast he
    · rintro rfl
      rfl
  · exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ (b : ℕ) from b.pos))
  · exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ (d : ℕ) from d.pos))

/-- All square degrees in the principal orientation have the same global orbit. -/
theorem forward_degree_collapses (n : ℕ+) : splitDegree n 1 = splitDegree 1 1 :=
  (splitDegree_eq_iff n 1 1 1).mpr rfl

/-- Opposite finite orientation separates every positive square degree in the adelic quotient. -/
theorem opposite_degree_injective : Function.Injective (splitDegree 1) := by
  intro m n h
  exact (splitDegree_eq_iff 1 m 1 n).mp h



/-- Integral Weyl element reversing every finite apartment. -/
def weyl : RationalGroup := ⟨!![0, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

theorem weyl_integral (p : {p : ℕ // p.Prime}) : localMap p weyl ∈ integralLocalGroup p := by
  intro i j
  change ‖((weyl i j : ℚ) : ℚ_[p.1])‖ ≤ 1
  fin_cases i <;> fin_cases j <;> simp [weyl]

theorem weyl_fixes_base : weyl • finiteBase = finiteBase :=
  (fixes_finiteBase_iff weyl).mpr weyl_integral

theorem finitePoint_mul_weyl (g : RationalGroup) : finitePoint (g * weyl) = finitePoint g := by
  rw [← finite_smul_base, mul_smul, weyl_fixes_base, finite_smul_base]

theorem weyl_diagonal (q : ℚ) (hq : q ≠ 0) :
    weyl * diagonal q hq = diagonal q⁻¹ (inv_ne_zero hq) * weyl := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [weyl, diagonal, Matrix.mul_apply, Fin.sum_univ_two]

/-- The adelic conjugator is integral at every finite place and trivial at infinity. -/
def finiteWeyl : AdelicGroup := (1, (arithmeticEmbedding weyl).2)

def conjugateArithmeticGroup : Subgroup AdelicGroup :=
  arithmeticGroup.map (MulAut.conj finiteWeyl⁻¹).toMonoidHom

def conjugateEmbedding : RationalGroup →* AdelicGroup :=
  (MulAut.conj finiteWeyl⁻¹).toMonoidHom.comp arithmeticEmbedding

theorem conjugateEmbedding_injective : Function.Injective conjugateEmbedding :=
  (MulAut.conj finiteWeyl⁻¹).injective.comp arithmeticEmbedding_injective

theorem conjugateArithmeticGroup_eq_range :
    conjugateArithmeticGroup = conjugateEmbedding.range := by
  ext x
  constructor
  · rintro ⟨y, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨arithmeticEmbedding g, ⟨g, rfl⟩, rfl⟩

theorem conjugateEmbedding_arch (g : RationalGroup) : (conjugateEmbedding g).1 = archMap g := by
  change 1⁻¹ * archMap g * (1⁻¹)⁻¹ = archMap g
  simp

theorem conjugateEmbedding_finite (g : RationalGroup) (p : {p : ℕ // p.Prime}) :
    (conjugateEmbedding g).2 p = localMap p (weyl⁻¹ * g * weyl) := by
  change (localMap p weyl)⁻¹ * localMap p g * ((localMap p weyl)⁻¹)⁻¹ = _
  rw [inv_inv, map_mul, map_mul, map_inv]

private def undoConjugation (x : conjugateArithmeticGroup) : arithmeticGroup :=
  ⟨finiteWeyl * x.1 * finiteWeyl⁻¹, by
    obtain ⟨g, hg, he⟩ := x.property
    have heq : finiteWeyl * x.1 * finiteWeyl⁻¹ = g := by
      rw [← he]
      simp [mul_assoc]
    rw [heq]
    exact hg⟩

private theorem undoConjugation_continuous : Continuous undoConjugation := by
  apply Continuous.subtype_mk
  exact (continuous_const.mul continuous_subtype_val).mul continuous_const

private theorem undoConjugation_eq_one_iff (x : conjugateArithmeticGroup) :
    undoConjugation x = 1 ↔ x = 1 := by
  constructor
  · intro h
    apply Subtype.ext
    have he := congrArg Subtype.val h
    change finiteWeyl * x.1 * finiteWeyl⁻¹ = 1 at he
    have hh := congrArg (fun y : AdelicGroup => finiteWeyl⁻¹ * y * finiteWeyl) he
    change (x : AdelicGroup) = 1
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, mul_inv_cancel,
      one_mul] using hh
  · rintro rfl
    apply Subtype.ext
    simp [undoConjugation]

/-- The finite Weyl conjugate is a discrete arithmetic subgroup of the same adelic group. -/
instance conjugateArithmeticGroup_discrete : DiscreteTopology conjugateArithmeticGroup := by
  apply discreteTopology_of_isOpen_singleton_one
  have h := (isOpen_discrete ({1} : Set arithmeticGroup)).preimage undoConjugation_continuous
  have he : undoConjugation ⁻¹' ({1} : Set arithmeticGroup) = {1} := by
    ext x
    exact undoConjugation_eq_one_iff x
  rwa [he] at h

def finiteFlip : GlobalSpace ≃ₜ GlobalSpace where
  toFun x := (x.1, weyl • x.2)
  invFun x := (x.1, weyl⁻¹ • x.2)
  left_inv x := by
    apply Prod.ext
    · rfl
    · exact inv_smul_smul weyl x.2
  right_inv x := by
    apply Prod.ext
    · rfl
    · exact smul_inv_smul weyl x.2
  continuous_toFun := continuous_fst.prodMk ((continuous_const_smul weyl).comp continuous_snd)
  continuous_invFun := continuous_fst.prodMk ((continuous_const_smul weyl⁻¹).comp continuous_snd)

/-- The same adelic space with the finite-conjugate arithmetic action. -/
@[ext] structure ConjugateSpace where
  point : GlobalSpace

instance : TopologicalSpace ConjugateSpace := TopologicalSpace.induced ConjugateSpace.point inferInstance

instance : MulAction RationalGroup ConjugateSpace where
  smul g x := ⟨finiteFlip.symm (g • finiteFlip x.point)⟩
  one_smul x := by
    apply ConjugateSpace.ext
    change finiteFlip.symm (1 • finiteFlip x.point) = x.point
    rw [one_smul, finiteFlip.symm_apply_apply]
  mul_smul g h x := by
    apply ConjugateSpace.ext
    change finiteFlip.symm ((g * h) • finiteFlip x.point) =
      finiteFlip.symm (g • finiteFlip (finiteFlip.symm (h • finiteFlip x.point)))
    rw [finiteFlip.apply_symm_apply, mul_smul]

theorem conjugate_smul_point (g : RationalGroup) (x : ConjugateSpace) :
    (g • x).point = (h3Act (archMap g) x.point.1, (weyl⁻¹ * g * weyl) • x.point.2) := by
  change (h3Act (archMap g) x.point.1, weyl⁻¹ • (g • (weyl • x.point.2))) = _
  rw [mul_smul, mul_smul]

abbrev ConjugateCarrier := Quotient (MulAction.orbitRel RationalGroup ConjugateSpace)

def toStandardCarrier : ConjugateCarrier → Carrier :=
  Quotient.map (fun x : ConjugateSpace => finiteFlip x.point) (by
    intro x y h
    obtain ⟨g, hg⟩ := h
    refine ⟨g, ?_⟩
    have he := congrArg (fun z : ConjugateSpace => finiteFlip z.point) hg
    change finiteFlip (finiteFlip.symm (g • finiteFlip y.point)) = finiteFlip x.point at he
    simpa only [finiteFlip.apply_symm_apply] using he)

/-- The original, equally oriented degree configuration, at square degrees. -/
def originalDegreePoint (n : ℕ+) : GlobalSpace :=
  (degPoint (((n : ℕ) : ℝ) ^ 2) (sq_pos_of_pos (by exact_mod_cast n.pos)),
    finitePoint (diagonal ((n : ℕ) : ℚ) (by exact_mod_cast n.ne_zero)))

def originalDegreeClass (n : ℕ+) : ConjugateCarrier := Quotient.mk _ ⟨originalDegreePoint n⟩

theorem originalDegreeClass_normal_form (n : ℕ+) :
    toStandardCarrier (originalDegreeClass n) = splitDegree 1 n := by
  change (Quotient.mk _
    (degPoint (((n : ℕ) : ℝ) ^ 2) _,
      weyl • finitePoint (diagonal ((n : ℕ) : ℚ) _)) : Carrier) = _
  rw [finite_smul_point, weyl_diagonal, finitePoint_mul_weyl]
  simp [splitDegree, classOf]

/-- Conjugating the arithmetic group retains every original square degree, without
changing the original degree configuration. -/
theorem original_degree_injective_on_conjugate_carrier : Function.Injective originalDegreeClass := by
  intro m n h
  have he := congrArg toStandardCarrier h
  rw [originalDegreeClass_normal_form, originalDegreeClass_normal_form] at he
  exact opposite_degree_injective he


#print axioms arithmeticEmbedding_injective
#print axioms arithmeticGroup_discrete
#print axioms splitDegree_eq_iff
#print axioms forward_degree_collapses
#print axioms conjugateEmbedding_injective
#print axioms conjugateArithmeticGroup_eq_range
#print axioms conjugateArithmeticGroup_discrete
#print axioms conjugateEmbedding_finite
#print axioms conjugate_smul_point
#print axioms originalDegreeClass_normal_form
#print axioms original_degree_injective_on_conjugate_carrier

end GaloisForLFunctions.HyperbolicArakelovTheory.OppositeAdelic
