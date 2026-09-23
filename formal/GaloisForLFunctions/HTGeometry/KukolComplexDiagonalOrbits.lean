import Mathlib

/-!
# Complete invariants of simultaneous complex unipotent orbits

Kukol, arXiv:2609.10214, Section 5 uses minus coordinates, Lorentz
quadratics and anchored transverse minors. On the nonzero-minus chart,
these invariants classify simultaneous orbits completely, with a unique
transport parameter. The action is the genuine complex bilinear Lorentz
shear in every finite transverse dimension and for arbitrary indexed families.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open scoped BigOperators

/-- The complete nonzero-minus coordinate chart of the complex light-cone space. -/
@[ext] structure KukolRegularPoint (κ : Type*) where
  minus : ℂˣ
  plus : ℂ
  transverse : κ → ℂ

variable {κ : Type*} [Fintype κ]

/-- The complex bilinear Lorentz quadratic; no complex conjugation occurs here. -/
def kukolRegularQuadratic (x : KukolRegularPoint κ) : ℂ :=
  (x.minus : ℂ)*x.plus-∑ k,x.transverse k^(2 : ℕ)

/-- Kukol's complex unipotent action in arbitrary transverse dimension. -/
def kukolRegularAction (u : κ → ℂ) (x : KukolRegularPoint κ) : KukolRegularPoint κ where
  minus := x.minus
  plus := x.plus+2*(∑ k,x.transverse k*u k)+(x.minus : ℂ)*(∑ k,u k^(2 : ℕ))
  transverse k := x.transverse k+(x.minus : ℂ)*u k

/-- The quadratic and transverse coordinates recover the omitted plus coordinate exactly. -/
def kukolRegularChart : KukolRegularPoint κ ≃ ℂˣ × ℂ × (κ → ℂ) where
  toFun x := (x.minus,kukolRegularQuadratic x,x.transverse)
  invFun a := ⟨a.1,(a.2.1+∑ k,a.2.2 k^(2 : ℕ))/(a.1 : ℂ),a.2.2⟩
  left_inv x := by
    apply KukolRegularPoint.ext
    · rfl
    · dsimp [kukolRegularQuadratic]
      field_simp
      ring
    · rfl
  right_inv a := by
    rcases a with ⟨m,q,z⟩
    dsimp only
    refine Prod.ext rfl ?_
    apply Prod.ext
    · dsimp [kukolRegularQuadratic]
      field_simp
      ring
    · rfl

/-- Equality is tested by the genuine Lorentz invariant and the remaining coordinates. -/
theorem kukolRegularPoint_eq_iff (x y : KukolRegularPoint κ) :
    x=y ↔ x.minus=y.minus ∧ kukolRegularQuadratic x=kukolRegularQuadratic y ∧
      x.transverse=y.transverse := by
  rw [← kukolRegularChart.injective.eq_iff]
  change (x.minus,kukolRegularQuadratic x,x.transverse) =
    (y.minus,kukolRegularQuadratic y,y.transverse) ↔ _
  simp only [Prod.mk.injEq]

/-- The actual complex shear preserves the Lorentz quadratic. -/
theorem kukolRegularQuadratic_action (u : κ → ℂ) (x : KukolRegularPoint κ) :
    kukolRegularQuadratic (kukolRegularAction u x)=kukolRegularQuadratic x := by
  have hs : (∑ k,(x.transverse k+(x.minus : ℂ)*u k)^(2 : ℕ)) =
      (∑ k,x.transverse k^(2 : ℕ))+2*(x.minus : ℂ)*(∑ k,x.transverse k*u k)+
        (x.minus : ℂ)^(2 : ℕ)*(∑ k,u k^(2 : ℕ)) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  dsimp [kukolRegularQuadratic,kukolRegularAction]
  rw [hs]
  ring

/-- Zero parameter is the identity on the entire regular coordinate chart. -/
theorem kukolRegularAction_zero (x : KukolRegularPoint κ) : kukolRegularAction 0 x=x := by
  ext <;> simp [kukolRegularAction]

/-- The parameter addition law holds in arbitrary transverse dimension. -/
theorem kukolRegularAction_add (u v : κ → ℂ) (x : KukolRegularPoint κ) :
    kukolRegularAction (u+v) x=kukolRegularAction u (kukolRegularAction v x) := by
  apply (kukolRegularPoint_eq_iff _ _).mpr
  refine ⟨rfl,?_,?_⟩
  · simp only [kukolRegularQuadratic_action]
  · funext k
    simp only [kukolRegularAction,Pi.add_apply]
    ring

/-- The nonzero-minus chart is a free complex unipotent space. -/
theorem kukolRegularAction_injective (x : KukolRegularPoint κ) :
    Function.Injective (fun u => kukolRegularAction u x) := by
  intro u v h
  funext k
  have he := congrArg (fun z : KukolRegularPoint κ => z.transverse k) h
  dsimp [kukolRegularAction] at he
  exact (mul_left_cancel₀ x.minus.ne_zero) (add_left_cancel he)

/-- Transverse two-column minors are invariants of the simultaneous action. -/
def kukolRegularPair (x y : KukolRegularPoint κ) (k : κ) : ℂ :=
  (x.minus : ℂ)*y.transverse k-(y.minus : ℂ)*x.transverse k

theorem kukolRegularPair_action (u : κ → ℂ) (x y : KukolRegularPoint κ) :
    kukolRegularPair (kukolRegularAction u x) (kukolRegularAction u y)=kukolRegularPair x y := by
  funext k
  dsimp [kukolRegularPair,kukolRegularAction]
  ring

variable {ι : Type*}

/-- The paper's complete invariant candidates for a simultaneous regular tuple, relative to one anchor. -/
def kukolDiagonalInvariants (anchor : ι) (x : ι → KukolRegularPoint κ) :
    (ι → ℂˣ) × (ι → ℂ) × (ι → κ → ℂ) :=
  (fun j => (x j).minus,fun j => kukolRegularQuadratic (x j),
    fun j => kukolRegularPair (x anchor) (x j))

/-- All proposed invariants are constant on simultaneous complex orbits. -/
theorem kukolDiagonalInvariants_action (anchor : ι) (u : κ → ℂ)
    (x : ι → KukolRegularPoint κ) :
    kukolDiagonalInvariants anchor (fun j => kukolRegularAction u (x j)) =
      kukolDiagonalInvariants anchor x := by
  unfold kukolDiagonalInvariants
  refine Prod.ext rfl ?_
  apply Prod.ext
  · funext j
    exact kukolRegularQuadratic_action u (x j)
  · funext j
    exact kukolRegularPair_action u (x anchor) (x j)

/-- The anchored transverse ratio is the global group coordinate. -/
def kukolDiagonalGauge (anchor : ι) (x : ι → KukolRegularPoint κ) (k : κ) : ℂ :=
  (x anchor).transverse k/((x anchor).minus : ℂ)

/-- The global coordinate changes by exactly the group parameter. -/
theorem kukolDiagonalGauge_action (anchor : ι) (u : κ → ℂ)
    (x : ι → KukolRegularPoint κ) :
    kukolDiagonalGauge anchor (fun j => kukolRegularAction u (x j)) =
      kukolDiagonalGauge anchor x+u := by
  funext k
  dsimp [kukolDiagonalGauge,kukolRegularAction]
  field_simp

/-- Complete simultaneous-orbit classification: the proposed invariants lose no orbit information. -/
theorem kukolDiagonal_orbit_iff (anchor : ι) (x y : ι → KukolRegularPoint κ) :
    (∃ u : κ → ℂ,∀ j,kukolRegularAction u (x j)=y j) ↔
      kukolDiagonalInvariants anchor x=kukolDiagonalInvariants anchor y := by
  constructor
  · rintro ⟨u,hu⟩
    have h := kukolDiagonalInvariants_action anchor u x
    simpa only [funext hu] using h.symm
  · intro h
    have hm (j : ι) : (x j).minus=(y j).minus := congrArg (fun t => t.1 j) h
    have hq (j : ι) : kukolRegularQuadratic (x j)=kukolRegularQuadratic (y j) :=
      congrArg (fun t => t.2.1 j) h
    have hw (j : ι) (k : κ) : kukolRegularPair (x anchor) (x j) k=
        kukolRegularPair (y anchor) (y j) k := congrArg (fun t => t.2.2 j k) h
    refine ⟨fun k => ((y anchor).transverse k-(x anchor).transverse k)/((x anchor).minus : ℂ),fun j => ?_⟩
    apply (kukolRegularPoint_eq_iff _ _).mpr
    refine ⟨hm j,?_,?_⟩
    · rw [kukolRegularQuadratic_action,hq]
    · funext k
      have he := hw j k
      dsimp [kukolRegularPair] at he
      rw [← hm anchor,← hm j] at he
      dsimp [kukolRegularAction]
      apply mul_left_cancel₀ (x anchor).minus.ne_zero
      field_simp
      linear_combination he

/-- Equal invariants determine a unique simultaneous unipotent transport. -/
theorem kukolDiagonal_unique_transport_iff (anchor : ι) (x y : ι → KukolRegularPoint κ) :
    (∃! u : κ → ℂ,∀ j,kukolRegularAction u (x j)=y j) ↔
      kukolDiagonalInvariants anchor x=kukolDiagonalInvariants anchor y := by
  constructor
  · intro h
    exact (kukolDiagonal_orbit_iff anchor x y).mp h.exists
  · intro h
    obtain ⟨u,hu⟩ := (kukolDiagonal_orbit_iff anchor x y).mpr h
    refine ⟨u,hu,fun v hv => ?_⟩
    exact kukolRegularAction_injective (x anchor) ((hv anchor).trans (hu anchor).symm)

end GaloisForLFunctions.HTGeometry
