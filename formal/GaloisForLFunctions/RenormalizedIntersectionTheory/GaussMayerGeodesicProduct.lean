import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerGeodesicReversal
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerUnorientedProduct

/-! The actual Mayer determinant is the Euler product over genuine periodic
modular geodesics. Forgetting geometric orientation retains the exact cardinality
of each reversal fiber, including self-reversing closed orbits. -/

open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerClosedGeodesics MayerGeodesicReversal MayerInverseCycles
open MayerOrbitWords MayerOrbitProduct MayerFredholm
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerGeodesicProduct

local instance : DecidableEq ClosedGeodesic := Classical.decEq _

/-- The geometric transverse-mode weight, defined from actual least return time. -/
def weight (s : ℂ) (g : ClosedGeodesic) (m : ℕ) : ℂ :=
  Complex.exp (-(s+(m : ℂ))*(MayerClosedGeodesics.length g : ℂ))

def factor (s : ℂ) (g : ClosedGeodesic) (m : ℕ) : ℂ := 1-weight s g m

/-- The geometric Selberg Euler product; convergence is certified in `Re s>1`. -/
def selbergZeta (s : ℂ) : ℂ := ∏' g : ClosedGeodesic, ∏' m : ℕ, factor s g m

private theorem weight_ofCycle (w : ℂ) (c : Orbit) (m : ℕ) :
    weight (w/2) (ofCycle c) m=orbitWeight w 1 c m := by
  rw [weight,length_ofCycle,orbitWeight_eq_translationLength,one_pow,one_mul]

/-- Absolute convergence is preserved by the genuine geometric cycle bijection. -/
theorem summable_geodesic_weights {w : ℂ} (hw : 2 < w.re) :
    Summable (fun p : ClosedGeodesic × ℕ => ‖weight (w/2) p.1 p.2‖) := by
  have h := signed_determinant_eulerProduct_on_closed_unit (z := 1) hw
    (by simpa only [norm_one] using (le_refl (1 : ℝ)))
  have hn : Summable (fun p : Orbit × ℕ => ‖weight (w/2) (ofCycle p.1) p.2‖) := by
    simpa only [weight_ofCycle] using h.1
  exact (cycleEquiv.prodCongr (Equiv.refl ℕ)).summable_iff.mp hn

/-- The joint geometric Euler product is the actual signed Mayer determinant product. -/
theorem hasProd_geodesic {w : ℂ} (hw : 2 < w.re) :
    HasProd (fun p : ClosedGeodesic × ℕ => factor (w/2) p.1 p.2)
      (determinant w (show 0 < w.re by linarith only [hw]) 1 *
        determinant w (show 0 < w.re by linarith only [hw]) (-1)) := by
  have h := signed_determinant_eulerProduct_on_closed_unit (z := 1) hw
    (by simpa only [norm_one] using (le_refl (1 : ℝ)))
  have hp : HasProd (fun p : Orbit × ℕ => factor (w/2) (ofCycle p.1) p.2)
      (determinant w (show 0 < w.re by linarith only [hw]) 1 *
        determinant w (show 0 < w.re by linarith only [hw]) (-1)) := by
    simpa only [factor,weight_ofCycle] using h.2.1
  exact (cycleEquiv.prodCongr (Equiv.refl ℕ)).hasProd_iff.mp hp

/-- The geometric length normalization is exactly `s=w/2`. -/
theorem signed_determinant_eq_selbergZeta {w : ℂ} (hw : 2 < w.re) :
    determinant w (show 0 < w.re by linarith only [hw]) 1 *
      determinant w (show 0 < w.re by linarith only [hw]) (-1)=selbergZeta (w/2) := by
  have h := signed_determinant_eulerProduct_on_closed_unit (z := 1) hw
    (by simpa only [norm_one] using (le_refl (1 : ℝ)))
  rw [selbergZeta,← cycleEquiv.tprod_eq (fun g => ∏' m : ℕ, factor (w/2) g m)]
  change _ = ∏' c : Orbit, ∏' m : ℕ, factor (w/2) (ofCycle c) m
  simpa only [factor,weight_ofCycle] using h.2.2

/-- Forgetting the actual geometric orientation. -/
def reversalSetoid : Setoid ClosedGeodesic where
  r g h := g=h ∨ reverse g=h
  iseqv := by
    refine ⟨fun _ => Or.inl rfl,?_,?_⟩
    · intro g h he
      rcases he with he | he
      · exact Or.inl he.symm
      · exact Or.inr ((congrArg reverse he).symm.trans (reverse_involutive g))
    · intro g h k hgh hhk
      rcases hgh with rfl | hgh
      · exact hhk
      rcases hhk with hhk | hhk
      · exact Or.inr (hgh.trans hhk)
      · exact Or.inl ((reverse_involutive g).symm.trans ((congrArg reverse hgh).trans hhk))

def UnorientedGeodesic := Quotient reversalSetoid

def unorientedGeodesic (g : ClosedGeodesic) : UnorientedGeodesic := Quotient.mk reversalSetoid g

theorem unorientedGeodesic_eq_iff (g h : ClosedGeodesic) :
    unorientedGeodesic g=unorientedGeodesic h ↔ g=h ∨ reverse g=h := by
  exact Quotient.eq_iff_equiv

/-- The existing inverse-class quotient agrees with forgetting actual geometric orientation. -/
def unorientedCycleEquiv : UnorientedOrbit ≃ UnorientedGeodesic where
  toFun := Quotient.map ofCycle (by
    intro c d h
    rcases h with h | h
    · exact Or.inl (congrArg ofCycle h)
    · exact Or.inr ((reverse_ofCycle c).trans (congrArg ofCycle h)))
  invFun := Quotient.map cycleEquiv.symm (by
    intro g h he
    rcases he with he | he
    · exact Or.inl (congrArg cycleEquiv.symm he)
    · right
      apply ofCycle_injective
      rw [← reverse_ofCycle]
      change reverse (cycleEquiv (cycleEquiv.symm g))=cycleEquiv (cycleEquiv.symm h)
      rw [cycleEquiv.apply_symm_apply,cycleEquiv.apply_symm_apply]
      exact he)
  left_inv u := by
    refine Quotient.inductionOn u (fun c => ?_)
    apply Quotient.sound
    exact Or.inl (cycleEquiv.symm_apply_apply c)
  right_inv u := by
    refine Quotient.inductionOn u (fun g => ?_)
    apply Quotient.sound
    exact Or.inl (cycleEquiv.apply_symm_apply g)

theorem unorientedCycleEquiv_mk (c : Orbit) :
    unorientedCycleEquiv (unoriented c)=unorientedGeodesic (ofCycle c) := rfl

/-- Intrinsic length descends through geometric time reversal. -/
def unorientedLength : UnorientedGeodesic → ℝ :=
  Quotient.lift MayerClosedGeodesics.length (fun g h he => by
    rcases he with he | he
    · exact congrArg MayerClosedGeodesics.length he
    · exact (length_reverse g).symm.trans (congrArg MayerClosedGeodesics.length he))

/-- The geometric orientation count, independent of symbolic coding. -/
def orientationMultiplicity : UnorientedGeodesic → ℕ :=
  Quotient.lift (fun g : ClosedGeodesic => if reverse g=g then 1 else 2) (by
    intro g h he
    rcases he with rfl | rfl
    · rfl
    · rw [reverse_involutive]
      by_cases hg : reverse g=g
      · simp only [hg]
      · simp only [if_neg hg,if_neg (Ne.symm hg)])

/-- Every geometric orientation fiber consists exactly of a geodesic and its reverse. -/
theorem mem_orientation_fiber (g h : ClosedGeodesic) :
    unorientedGeodesic h=unorientedGeodesic g ↔ h ∈ ({g,reverse g} : Finset ClosedGeodesic) := by
  rw [unorientedGeodesic_eq_iff,Finset.mem_insert,Finset.mem_singleton]
  have hr : reverse h=g ↔ h=reverse g :=
    ⟨fun he => (reverse_involutive h).symm.trans (congrArg reverse he),
      fun he => (congrArg reverse he).trans (reverse_involutive g)⟩
  rw [hr]

/-- The product exponent is the actual cardinality of the geometric orientation fiber. -/
theorem orientationMultiplicity_card (g : ClosedGeodesic) :
    orientationMultiplicity (unorientedGeodesic g)=({g,reverse g} : Finset ClosedGeodesic).card := by
  change (if reverse g=g then 1 else 2)= _
  by_cases h : reverse g=g
  · simp [h]
  · simp [h,Ne.symm h]

theorem orientationMultiplicity_one_or_two (u : UnorientedGeodesic) :
    orientationMultiplicity u=1 ∨ orientationMultiplicity u=2 := by
  refine Quotient.inductionOn u (fun g => ?_)
  change (if reverse g=g then 1 else 2)=1 ∨ (if reverse g=g then 1 else 2)=2
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem unorientedLength_equiv (u : UnorientedOrbit) :
    unorientedLength (unorientedCycleEquiv u)=unorientedTranslationLength u := by
  refine Quotient.inductionOn u (fun c => ?_)
  exact length_ofCycle c

private theorem orientationMultiplicity_equiv (u : UnorientedOrbit) :
    orientationMultiplicity (unorientedCycleEquiv u)=multiplicity u := by
  refine Quotient.inductionOn u (fun c => ?_)
  change (if reverse (ofCycle c)=ofCycle c then 1 else 2)=multiplicity (unoriented c)
  rw [multiplicity_unoriented]
  by_cases h : inverseCycle c=c
  · rw [if_pos ((reverse_ofCycle_eq_iff c).mpr h),if_pos h]
  · have hr : reverse (ofCycle c) ≠ ofCycle c :=
      fun he => h ((reverse_ofCycle_eq_iff c).mp he)
    rw [if_neg hr,if_neg h]

def unorientedFactor (s : ℂ) (u : UnorientedGeodesic) (m : ℕ) : ℂ :=
  1-Complex.exp (-(s+(m : ℂ))*(unorientedLength u : ℂ))

private theorem unorientedFactor_equiv (w : ℂ) (u : UnorientedOrbit) (m : ℕ) :
    unorientedFactor (w/2) (unorientedCycleEquiv u) m=MayerUnorientedProduct.factor w 1 u m := by
  rw [unorientedFactor,unorientedLength_equiv,MayerUnorientedProduct.factor,one_pow,one_mul]

/-- Joint and nested geometric products retain one or two orientations exactly. -/
theorem signed_determinant_unoriented_geodesics {w : ℂ} (hw : 2 < w.re) :
    HasProd (fun p : UnorientedGeodesic × ℕ =>
      unorientedFactor (w/2) p.1 p.2 ^ orientationMultiplicity p.1)
      (determinant w (show 0 < w.re by linarith only [hw]) 1 *
        determinant w (show 0 < w.re by linarith only [hw]) (-1)) ∧
    (∀ u : UnorientedGeodesic, Multipliable (fun m : ℕ =>
      unorientedFactor (w/2) u m ^ orientationMultiplicity u)) ∧
    determinant w (show 0 < w.re by linarith only [hw]) 1 *
      determinant w (show 0 < w.re by linarith only [hw]) (-1)=
      ∏' u : UnorientedGeodesic, ∏' m : ℕ,
        unorientedFactor (w/2) u m ^ orientationMultiplicity u := by
  have h := MayerUnorientedProduct.signed_determinant_unorientedProduct_on_closed_unit
    (z := 1) hw (by simpa only [norm_one] using (le_refl (1 : ℝ)))
  refine ⟨?_,?_,?_⟩
  · have hp : HasProd (fun p : UnorientedOrbit × ℕ =>
        unorientedFactor (w/2) (unorientedCycleEquiv p.1) p.2 ^
          orientationMultiplicity (unorientedCycleEquiv p.1))
        (determinant w (show 0 < w.re by linarith only [hw]) 1 *
          determinant w (show 0 < w.re by linarith only [hw]) (-1)) := by
      simpa only [unorientedFactor_equiv,orientationMultiplicity_equiv] using h.1
    exact (unorientedCycleEquiv.prodCongr (Equiv.refl ℕ)).hasProd_iff.mp hp
  · intro u
    obtain ⟨v,rfl⟩ := unorientedCycleEquiv.surjective u
    simpa only [unorientedFactor_equiv,orientationMultiplicity_equiv] using h.2.1 v
  · rw [← unorientedCycleEquiv.tprod_eq (fun u => ∏' m : ℕ,
      unorientedFactor (w/2) u m ^ orientationMultiplicity u)]
    simpa only [unorientedFactor_equiv,orientationMultiplicity_equiv] using h.2.2

/-- The geometric Selberg Euler product with its exact unoriented multiplicities. -/
theorem selbergZeta_eq_unoriented_geodesics {w : ℂ} (hw : 2 < w.re) :
    selbergZeta (w/2)=∏' u : UnorientedGeodesic, ∏' m : ℕ,
      unorientedFactor (w/2) u m ^ orientationMultiplicity u :=
  (signed_determinant_eq_selbergZeta hw).symm.trans (signed_determinant_unoriented_geodesics hw).2.2

#print axioms summable_geodesic_weights
#print axioms hasProd_geodesic
#print axioms signed_determinant_eq_selbergZeta
#print axioms unorientedCycleEquiv
#print axioms mem_orientation_fiber
#print axioms orientationMultiplicity_card
#print axioms orientationMultiplicity_one_or_two
#print axioms signed_determinant_unoriented_geodesics
#print axioms selbergZeta_eq_unoriented_geodesics

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerGeodesicProduct
