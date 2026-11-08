import GaloisForLFunctions.EffectiveScalingGeometry.PrimeTwoPrimeNormalForm

/-!
# The two-prime block algebra over an arbitrary ring

The row `(2,3)` is surjective, and its kernel is freely parametrized by
`c ↦ (3c,−2c)`, with inverse `(a,b) ↦ a+b`. The top column `(-3,2)`
injectively fills precisely this kernel. Before the three-vertex appears,
the two-vertex cycles are the annihilator of two; their inclusion into the
later free kernel keeps their coefficient. These algebraic identities supply
the cycle and boundary calculation for the truncated arithmetic blocks.
-/

noncomputable section
namespace GaloisForLFunctions.EffectiveScalingGeometry
variable (R : Type*) [CommRing R]

/-- The row differential once both small-prime vertices have appeared. -/
def twoPrimeBlockRow : (R × R) →ₗ[R] R where
  toFun x := 2*x.1 + 3*x.2
  map_add' x y := by simp only [Prod.fst_add,Prod.snd_add]; ring
  map_smul' c x := by simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,RingHom.id_apply]; ring

/-- The top face has the signed two-prime Koszul boundary. -/
def twoPrimeBlockTop : R →ₗ[R] (R × R) where
  toFun c := (-3*c,2*c)
  map_add' c d := by ext <;> simp only [Prod.fst_add,Prod.snd_add] <;> ring
  map_smul' c d := by ext <;> simp only [Prod.smul_fst,Prod.smul_snd,smul_eq_mul,RingHom.id_apply] <;> ring

/-- The Bézout relation makes the two-prime row surjective over every ring. -/
theorem twoPrimeBlockRow_surjective : Function.Surjective (twoPrimeBlockRow R) := by
  intro c
  refine ⟨(-c,c),?_⟩
  change 2*(-c)+3*c=c
  ring

/-- Every row cycle is uniquely `(3c,−2c)`, with coefficient `c=a+b`. -/
def twoPrimeBlockCycleEquiv : (twoPrimeBlockRow R).ker ≃ₗ[R] R where
  toFun x := x.val.1+x.val.2
  invFun c := ⟨(3*c,-2*c),by change 2*(3*c)+3*(-2*c)=0; ring⟩
  left_inv x := by
    apply Subtype.ext
    have hx : 2*x.val.1+3*x.val.2=0 := x.property
    apply Prod.ext
    · change 3*(x.val.1+x.val.2)=x.val.1
      linear_combination hx
    · change -2*(x.val.1+x.val.2)=x.val.2
      linear_combination -hx
  right_inv c := by change 3*c + -2*c=c; ring
  map_add' x y := by change (x.val.1+y.val.1)+(x.val.2+y.val.2)=(x.val.1+x.val.2)+(y.val.1+y.val.2); ring
  map_smul' c x := by change c*x.val.1+c*x.val.2=c*(x.val.1+x.val.2); ring

/-- Once the top face appears, its boundary fills every row cycle. -/
theorem twoPrimeBlockTop_range :
    (twoPrimeBlockTop R).range = (twoPrimeBlockRow R).ker := by
  apply le_antisymm
  · rintro x ⟨c,rfl⟩
    change 2*(-3*c)+3*(2*c)=0
    ring
  · intro x hx
    refine ⟨-(x.1+x.2),?_⟩
    have he := congrArg Subtype.val ((twoPrimeBlockCycleEquiv R).left_inv ⟨x,hx⟩)
    change (3*(x.1+x.2),-2*(x.1+x.2))=x at he
    change (-3*-(x.1+x.2),2*-(x.1+x.2))=x
    calc
      _ = (3*(x.1+x.2),-2*(x.1+x.2)) := by ext <;> ring
      _ = x := he

/-- The top differential is injective even when the coefficient ring has torsion. -/
theorem twoPrimeBlockTop_injective : Function.Injective (twoPrimeBlockTop R) := by
  intro c d h
  have he := congrArg (fun x : R × R => x.1+x.2) h
  change -3*c+2*c = -3*d+2*d at he
  linear_combination -he

/-- Before prime three appears, middle cycles are exactly the annihilator of two. -/
def twoPrimeAnnihilator : Submodule R R := ((2 : R) • (LinearMap.id : R →ₗ[R] R)).ker

/-- Inserting a two-torsion cycle into the full row preserves its coefficient. -/
def twoPrimeAnnihilatorToCycle : twoPrimeAnnihilator R →ₗ[R] (twoPrimeBlockRow R).ker where
  toFun a := ⟨(a.val,0),by
    have ha : 2*a.val=0 := a.property
    change 2*a.val+3*0=0
    rw [ha,mul_zero,add_zero]⟩
  map_add' a b := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (0 : R) = 0+0
      rw [add_zero]
  map_smul' c a := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change (0 : R) = c • (0 : R)
      rw [smul_zero]

theorem twoPrimeAnnihilator_transition (a : twoPrimeAnnihilator R) :
    twoPrimeBlockCycleEquiv R (twoPrimeAnnihilatorToCycle R a) = a.val := by
  change a.val+0=a.val
  exact add_zero _

#print axioms twoPrimeBlockRow_surjective
#print axioms twoPrimeBlockCycleEquiv
#print axioms twoPrimeBlockTop_range
#print axioms twoPrimeBlockTop_injective
#print axioms twoPrimeAnnihilator_transition
end GaloisForLFunctions.EffectiveScalingGeometry
