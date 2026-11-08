import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeTruncatedBlocks

/-!
# Homology of truncated arithmetic two-prime blocks

The lower class is a born scalar modulo the ideal `0`, `2R` or `R`,
according to height. Upper cycles have coefficient `a+b`; it vanishes
before `2m` and is annihilated by two before `3m`. Their boundaries are
exactly the coefficients born at `6m`. Both quotient equivalences send
the original categorical homology class to its stated coefficient coset.
-/

noncomputable section
open CategoryTheory
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- Upper cycle coefficients vanish before twice the core height and are
annihilated by two until three times the core height. -/
def twoPrimeUpperCoefficients (m N : ℕ) : Submodule R R where
  carrier := {c | (N < 2*m → c=0) ∧ (N < 3*m → 2*c=0)}
  zero_mem' := ⟨fun _ => rfl,fun _ => mul_zero _⟩
  add_mem' hx hy := ⟨fun h => by rw [hx.1 h,hy.1 h,add_zero],
    fun h => by rw [mul_add,hx.2 h,hy.2 h,add_zero]⟩
  smul_mem' a x hx := ⟨fun h => by rw [hx.1 h,smul_zero],fun h => by
    change 2*(a*x)=0
    calc
      _ = a*(2*x) := by ring
      _ = 0 := by rw [hx.2 h,mul_zero]⟩

/-- The full row parametrization restricts to every truncated block. -/
def twoPrimeUpperCycleEquiv (m N : ℕ) :
    (twoPrimeUpperBlock R m N).g.hom.ker ≃ₗ[R] twoPrimeUpperCoefficients R m N where
  toFun x := ⟨x.val.val.1+x.val.val.2,by
    have hx : 2*x.val.val.1+3*x.val.val.2=0 := congrArg Subtype.val x.property
    constructor
    · intro h
      rw [x.val.property.1 h,x.val.property.2 (by omega),add_zero]
    · intro h
      have hb := x.val.property.2 h
      rw [hb,mul_zero,add_zero] at hx
      rw [hb,add_zero]
      exact hx⟩
  invFun c := ⟨⟨(3*c.val,-2*c.val),by
    constructor
    · intro h
      change 3*c.val=0
      rw [c.property.1 h,mul_zero]
    · intro h
      change -2*c.val=0
      rw [neg_mul,c.property.2 h,neg_zero]⟩,by
    apply Subtype.ext
    change 2*(3*c.val)+3*(-2*c.val)=0
    ring⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have hx : 2*x.val.val.1+3*x.val.val.2=0 := congrArg Subtype.val x.property
    apply Prod.ext
    · change 3*(x.val.val.1+x.val.val.2)=x.val.val.1
      linear_combination hx
    · change -2*(x.val.val.1+x.val.val.2)=x.val.val.2
      linear_combination -hx
  right_inv c := by apply Subtype.ext; change 3*c.val + -2*c.val=c.val; ring
  map_add' x y := by
    apply Subtype.ext
    change (x.val.val.1+y.val.val.1)+(x.val.val.2+y.val.val.2)=
      (x.val.val.1+x.val.val.2)+(y.val.val.1+y.val.val.2)
    ring
  map_smul' a x := by
    apply Subtype.ext
    change a*x.val.val.1+a*x.val.val.2=a*(x.val.val.1+x.val.val.2)
    ring

/-- Lower cycles are all bottom coefficients, since the next differential is zero. -/
def twoPrimeLowerCycleEquiv (m N : ℕ) :
    (twoPrimeLowerBlock R m N).g.hom.ker ≃ₗ[R] twoPrimeBlockScalar R m N where
  toFun x := x.val
  invFun c := ⟨c,rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Upper coefficients are functorial in arithmetic height. -/
theorem twoPrimeUpperCoefficients_mono (m : ℕ) {N M : ℕ} (h : N ≤ M) :
    twoPrimeUpperCoefficients R m N ≤ twoPrimeUpperCoefficients R m M := by
  intro c hc
  exact ⟨fun hm => hc.1 (h.trans_lt hm),fun hm => hc.2 (h.trans_lt hm)⟩

/-- Upper boundaries consist exactly of coefficients whose top face has appeared. -/
def twoPrimeUpperRelations (m N : ℕ) : Submodule R (twoPrimeUpperCoefficients R m N) :=
  (twoPrimeBlockScalar R (6*m) N).comap (twoPrimeUpperCoefficients R m N).subtype

theorem twoPrimeUpperCycleEquiv_boundary (m N : ℕ)
    (x : (twoPrimeUpperBlock R m N).g.hom.ker) :
    twoPrimeUpperCycleEquiv R m N x ∈ twoPrimeUpperRelations R m N ↔
      x ∈ (twoPrimeUpperBlock R m N).moduleCatToCycles.range := by
  constructor
  · intro hx
    refine ⟨⟨-(x.val.val.1+x.val.val.2),?_⟩,?_⟩
    · intro h
      change -(x.val.val.1+x.val.val.2)=0
      have hz : x.val.val.1+x.val.val.2=0 := hx h
      rw [hz,neg_zero]
    · apply Subtype.ext
      apply Subtype.ext
      have hc := congrArg (fun z => z.val.val) ((twoPrimeUpperCycleEquiv R m N).left_inv x)
      change (3*(x.val.val.1+x.val.val.2),-2*(x.val.val.1+x.val.val.2))=x.val.val at hc
      change (-3*-(x.val.val.1+x.val.val.2),2*-(x.val.val.1+x.val.val.2))=x.val.val
      calc
        _ = (3*(x.val.val.1+x.val.val.2),-2*(x.val.val.1+x.val.val.2)) := by ext <;> ring
        _ = x.val.val := hc
  · rintro ⟨b,rfl⟩ h
    change -3*b.val+2*b.val=0
    rw [b.property h,mul_zero,mul_zero,add_zero]

/-- Exact upper homology coefficients, including the top-face relation. -/
abbrev TwoPrimeUpperHomology (m N : ℕ) :=
  twoPrimeUpperCoefficients R m N ⧸ twoPrimeUpperRelations R m N

/-- Send an actual upper cycle to its coefficient modulo the top boundary. -/
def twoPrimeUpperProjection (m N : ℕ) :
    (twoPrimeUpperBlock R m N).g.hom.ker →ₗ[R] TwoPrimeUpperHomology R m N :=
  (twoPrimeUpperRelations R m N).mkQ.comp (twoPrimeUpperCycleEquiv R m N).toLinearMap

theorem twoPrimeUpperProjection_surjective (m N : ℕ) :
    Function.Surjective (twoPrimeUpperProjection R m N) :=
  (Submodule.mkQ_surjective _).comp (twoPrimeUpperCycleEquiv R m N).surjective

theorem twoPrimeUpperProjection_ker (m N : ℕ) :
    (twoPrimeUpperProjection R m N).ker = (twoPrimeUpperBlock R m N).moduleCatToCycles.range := by
  ext x
  change (Submodule.Quotient.mk (twoPrimeUpperCycleEquiv R m N x) :
    TwoPrimeUpperHomology R m N) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero,twoPrimeUpperCycleEquiv_boundary]

def twoPrimeUpperCycleQuotientEquiv (m N : ℕ) :=
  LinearMap.quotKerEquivOfSurjective (twoPrimeUpperProjection R m N)
    (twoPrimeUpperProjection_surjective R m N)

def twoPrimeUpperBoundaryQuotientEquiv (m N : ℕ) :=
  Submodule.quotEquivOfEq (twoPrimeUpperBlock R m N).moduleCatToCycles.range
    (twoPrimeUpperProjection R m N).ker (twoPrimeUpperProjection_ker R m N).symm

/-- Original categorical upper homology equals the explicit coefficient quotient. -/
def twoPrimeUpperHomologyEquiv (m N : ℕ) :
    (twoPrimeUpperBlock R m N).homology ≃ₗ[R] TwoPrimeUpperHomology R m N :=
  (twoPrimeUpperBlock R m N).moduleCatHomologyIso.toLinearEquiv.trans
    ((twoPrimeUpperBoundaryQuotientEquiv R m N).trans (twoPrimeUpperCycleQuotientEquiv R m N))

theorem twoPrimeUpperHomologyEquiv_class (m N : ℕ)
    (x : (twoPrimeUpperBlock R m N).g.hom.ker) :
    twoPrimeUpperHomologyEquiv R m N
      (DifferentialGeometry.Topology.moduleHomologyClass (twoPrimeUpperBlock R m N) x) =
      twoPrimeUpperProjection R m N x := by
  unfold twoPrimeUpperHomologyEquiv
  simp only [LinearEquiv.trans_apply]
  change twoPrimeUpperCycleQuotientEquiv R m N (twoPrimeUpperBoundaryQuotientEquiv R m N
    ((twoPrimeUpperBlock R m N).moduleCatHomologyIso.hom
      (DifferentialGeometry.Topology.moduleHomologyClass (twoPrimeUpperBlock R m N) x))) = _
  rw [DifferentialGeometry.Topology.moduleHomologyClass_quotient]
  rfl

/-- The lower relation ideal is zero, twice the ring, then the whole ring. -/
def twoPrimeLowerIdeal (m N : ℕ) : Submodule R R :=
  if 3*m ≤ N then ⊤ else if 2*m ≤ N then
    ((2 : R) • (LinearMap.id : R →ₗ[R] R)).range else ⊥

/-- Arithmetic births determine the entire image of the row differential. -/
theorem twoPrimeLowerIdeal_mem_iff (m N : ℕ) (c : R) :
    c ∈ twoPrimeLowerIdeal R m N ↔
      ∃ x : twoPrimeBlockMiddle R m N, twoPrimeBlockRow R x.val = c := by
  by_cases h3 : 3*m ≤ N
  · rw [twoPrimeLowerIdeal,if_pos h3]
    constructor
    · intro _
      refine ⟨⟨(-c,c),⟨fun h => False.elim (by omega),fun h => False.elim (by omega)⟩⟩,?_⟩
      change 2*(-c)+3*c=c
      ring
    · intro _
      trivial
  · by_cases h2 : 2*m ≤ N
    · rw [twoPrimeLowerIdeal,if_neg h3,if_pos h2]
      constructor
      · rintro ⟨a,ha⟩
        refine ⟨⟨(a,0),⟨fun h => False.elim (by omega),fun _ => rfl⟩⟩,?_⟩
        change 2*a+3*0=c
        change 2*a=c at ha
        rw [mul_zero,add_zero,ha]
      · rintro ⟨x,hx⟩
        refine ⟨x.val.1,?_⟩
        change 2*x.val.1=c
        change 2*x.val.1+3*x.val.2=c at hx
        rw [x.property.2 (by omega),mul_zero,add_zero] at hx
        exact hx
    · rw [twoPrimeLowerIdeal,if_neg h3,if_neg h2]
      constructor
      · intro hc
        refine ⟨0,?_⟩
        change c=0 at hc
        rw [hc]
        exact map_zero _
      · rintro ⟨x,hx⟩
        change c=0
        change 2*x.val.1+3*x.val.2=c at hx
        rw [x.property.1 (by omega),x.property.2 (by omega),mul_zero,mul_zero,add_zero] at hx
        exact hx.symm

/-- Lower boundaries are the lower relation ideal inside the born scalar generator. -/
def twoPrimeLowerRelations (m N : ℕ) : Submodule R (twoPrimeBlockScalar R m N) :=
  (twoPrimeLowerIdeal R m N).comap (twoPrimeBlockScalar R m N).subtype

abbrev TwoPrimeLowerHomology (m N : ℕ) :=
  twoPrimeBlockScalar R m N ⧸ twoPrimeLowerRelations R m N

/-- The lower class is the bottom coefficient modulo its arithmetic relation ideal. -/
def twoPrimeLowerProjection (m N : ℕ) :
    (twoPrimeLowerBlock R m N).g.hom.ker →ₗ[R] TwoPrimeLowerHomology R m N :=
  (twoPrimeLowerRelations R m N).mkQ.comp (twoPrimeLowerCycleEquiv R m N).toLinearMap

theorem twoPrimeLowerProjection_surjective (m N : ℕ) :
    Function.Surjective (twoPrimeLowerProjection R m N) :=
  (Submodule.mkQ_surjective _).comp (twoPrimeLowerCycleEquiv R m N).surjective

theorem twoPrimeLowerProjection_ker (m N : ℕ) :
    (twoPrimeLowerProjection R m N).ker = (twoPrimeLowerBlock R m N).moduleCatToCycles.range := by
  ext x
  change (Submodule.Quotient.mk (twoPrimeLowerCycleEquiv R m N x) :
    TwoPrimeLowerHomology R m N) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  change x.val.val ∈ twoPrimeLowerIdeal R m N ↔ _
  rw [twoPrimeLowerIdeal_mem_iff]
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨a,Subtype.ext (Subtype.ext ha)⟩
  · rintro ⟨a,rfl⟩
    exact ⟨a,rfl⟩

def twoPrimeLowerCycleQuotientEquiv (m N : ℕ) :=
  LinearMap.quotKerEquivOfSurjective (twoPrimeLowerProjection R m N)
    (twoPrimeLowerProjection_surjective R m N)

def twoPrimeLowerBoundaryQuotientEquiv (m N : ℕ) :=
  Submodule.quotEquivOfEq (twoPrimeLowerBlock R m N).moduleCatToCycles.range
    (twoPrimeLowerProjection R m N).ker (twoPrimeLowerProjection_ker R m N).symm

/-- Original categorical lower homology equals the explicit coefficient quotient. -/
def twoPrimeLowerHomologyEquiv (m N : ℕ) :
    (twoPrimeLowerBlock R m N).homology ≃ₗ[R] TwoPrimeLowerHomology R m N :=
  (twoPrimeLowerBlock R m N).moduleCatHomologyIso.toLinearEquiv.trans
    ((twoPrimeLowerBoundaryQuotientEquiv R m N).trans (twoPrimeLowerCycleQuotientEquiv R m N))

theorem twoPrimeLowerHomologyEquiv_class (m N : ℕ)
    (x : (twoPrimeLowerBlock R m N).g.hom.ker) :
    twoPrimeLowerHomologyEquiv R m N
      (DifferentialGeometry.Topology.moduleHomologyClass (twoPrimeLowerBlock R m N) x) =
      twoPrimeLowerProjection R m N x := by
  unfold twoPrimeLowerHomologyEquiv
  simp only [LinearEquiv.trans_apply]
  change twoPrimeLowerCycleQuotientEquiv R m N (twoPrimeLowerBoundaryQuotientEquiv R m N
    ((twoPrimeLowerBlock R m N).moduleCatHomologyIso.hom
      (DifferentialGeometry.Topology.moduleHomologyClass (twoPrimeLowerBlock R m N) x))) = _
  rw [DifferentialGeometry.Topology.moduleHomologyClass_quotient]
  rfl

#print axioms twoPrimeUpperHomologyEquiv
#print axioms twoPrimeUpperHomologyEquiv_class
#print axioms twoPrimeLowerHomologyEquiv
#print axioms twoPrimeLowerHomologyEquiv_class
#print axioms twoPrimeUpperCycleEquiv_boundary
#print axioms twoPrimeLowerIdeal_mem_iff
end GaloisForLFunctions.EffectiveScalingGeometry
