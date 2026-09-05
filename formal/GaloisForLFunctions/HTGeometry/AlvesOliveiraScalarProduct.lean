import GaloisForLFunctions.HTGeometry.ExactnessFlagGreenReduction
import GaloisForLFunctions.HTGeometry.NativeObserverUniversalDescentInertiaLaw

/-!
# Alves-Oliveira scalar-product core

Linear-algebraic core of generalized semi-Riemannian submersions: horizontal space, radical,
radical-shift invariance, horizontal-lift ambiguity, and nondegenerate complements. Final theorems
apply this package to existing Green quotients, Stokes forms, and the hyperbolic-plane model.
-/

open LinearMap (BilinForm)

noncomputable section

namespace GaloisForLFunctions.HTGeometry

universe u

variable {K : Type*} [Field K]
variable {V : Type u} [AddCommGroup V] [Module K V]

def semiRiemannianHorizontal (g : BilinForm K V) (vertical : Submodule K V) :
    Submodule K V :=
  g.orthogonal vertical

def semiRiemannianRadical (g : BilinForm K V) (vertical : Submodule K V) :
    Submodule K V :=
  vertical ⊓ semiRiemannianHorizontal g vertical

def semiRiemannianTotal (g : BilinForm K V) (vertical : Submodule K V) :
    Submodule K V :=
  vertical ⊔ semiRiemannianHorizontal g vertical

theorem mem_semiRiemannianRadical_iff_pairing_zero_on_total
    [FiniteDimensional K V]
    {g : BilinForm K V} (hnd : g.Nondegenerate) (hrefl : g.IsRefl)
    {vertical : Submodule K V} {v : V} :
    v ∈ semiRiemannianRadical g vertical ↔
      ∀ u ∈ semiRiemannianTotal g vertical, g v u = 0 := by
  constructor
  · rintro ⟨hvV, hvH⟩ u hu
    have hu' : u ∈ vertical ⊔ semiRiemannianHorizontal g vertical := by
      simpa [semiRiemannianTotal] using hu
    rcases Submodule.mem_sup.mp hu' with ⟨a, ha, b, hb, rfl⟩
    have hva : g v a = 0 :=
      hrefl a v ((LinearMap.BilinForm.mem_orthogonal_iff.mp hvH) a ha)
    have hvb : g v b = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hb) v hvV
    simp [hva, hvb]
  · intro hall
    constructor
    · have hvHH : v ∈ g.orthogonal (g.orthogonal vertical) := by
        rw [LinearMap.BilinForm.mem_orthogonal_iff]
        intro h hh
        exact hrefl v h (hall h (show h ∈ semiRiemannianTotal g vertical from
          Submodule.mem_sup_right hh))
      rw [LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl] at hvHH
      exact hvHH
    · exact LinearMap.BilinForm.mem_orthogonal_iff.mpr (by
        intro a ha
        exact hrefl v a (hall a (show a ∈ semiRiemannianTotal g vertical from
          Submodule.mem_sup_left ha)))

theorem semiRiemannianRadical_pairing_zero
    {g : BilinForm K V} (hrefl : g.IsRefl)
    {vertical : Submodule K V} {v u : V}
    (hv : v ∈ semiRiemannianRadical g vertical)
    (hu : u ∈ semiRiemannianTotal g vertical) :
    g v u = 0 := by
  have hu' : u ∈ vertical ⊔ semiRiemannianHorizontal g vertical := by
    simpa [semiRiemannianTotal] using hu
  rcases Submodule.mem_sup.mp hu' with ⟨a, ha, b, hb, rfl⟩
  have hva : g v a = 0 :=
    hrefl a v ((LinearMap.BilinForm.mem_orthogonal_iff.mp hv.2) a ha)
  have hvb : g v b = 0 :=
    (LinearMap.BilinForm.mem_orthogonal_iff.mp hb) v hv.1
  simp [hva, hvb]

theorem semiRiemannianTotal_pairing_radical_zero
    {g : BilinForm K V} (hrefl : g.IsRefl)
    {vertical : Submodule K V} {u v : V}
    (hu : u ∈ semiRiemannianTotal g vertical)
    (hv : v ∈ semiRiemannianRadical g vertical) :
    g u v = 0 :=
  hrefl v u (semiRiemannianRadical_pairing_zero hrefl hv hu)

theorem semiRiemannian_pairing_add_radical
    {g : BilinForm K V} (hrefl : g.IsRefl)
    {vertical : Submodule K V} {u₁ u₂ v₁ v₂ : V}
    (hu₁ : u₁ ∈ semiRiemannianTotal g vertical)
    (hu₂ : u₂ ∈ semiRiemannianTotal g vertical)
    (hv₁ : v₁ ∈ semiRiemannianRadical g vertical)
    (hv₂ : v₂ ∈ semiRiemannianRadical g vertical) :
    g (u₁ + v₁) (u₂ + v₂) = g u₁ u₂ := by
  simp only [map_add, LinearMap.add_apply]
  rw [semiRiemannianTotal_pairing_radical_zero hrefl hu₁ hv₂,
    semiRiemannianRadical_pairing_zero hrefl hv₁ hu₂]
  have hv₂Total : v₂ ∈ semiRiemannianTotal g vertical := by
    exact Submodule.mem_sup_left hv₂.1
  rw [semiRiemannianRadical_pairing_zero hrefl hv₁ hv₂Total]
  simp

theorem semiRiemannian_eq_add_radical_of_pairing_eq
    [FiniteDimensional K V]
    {g : BilinForm K V} (hnd : g.Nondegenerate) (hrefl : g.IsRefl)
    {vertical : Submodule K V} {u₁ u₂ : V}
    (hpair : ∀ w ∈ semiRiemannianTotal g vertical, g u₁ w = g u₂ w) :
    ∃ v ∈ semiRiemannianRadical g vertical, u₁ = u₂ + v := by
  have hrad : u₁ - u₂ ∈ semiRiemannianRadical g vertical :=
    (mem_semiRiemannianRadical_iff_pairing_zero_on_total hnd hrefl).mpr (by
      intro w hw
      simpa only [map_sub, LinearMap.sub_apply, sub_eq_zero] using hpair w hw)
  exact ⟨u₁ - u₂, hrad, by abel⟩

variable {W : Type*} [AddCommGroup W] [Module K W]

theorem horizontal_lifts_sub_mem_radical
    {g : BilinForm K V} {vertical : Submodule K V} (q : V →ₗ[K] W)
    (hker : q.ker = vertical) {x y : V}
    (hx : x ∈ semiRiemannianHorizontal g vertical)
    (hy : y ∈ semiRiemannianHorizontal g vertical)
    (hxy : q x = q y) :
    x - y ∈ semiRiemannianRadical g vertical := by
  constructor
  · rw [← hker]
    exact LinearMap.mem_ker.mpr (by simp [hxy])
  · exact sub_mem hx hy

theorem horizontal_lift_pairing_independent
    {g : BilinForm K V} (hrefl : g.IsRefl)
    {vertical : Submodule K V} (q : V →ₗ[K] W) (hker : q.ker = vertical)
    {x₁ x₂ y₁ y₂ : V}
    (hx₁ : x₁ ∈ semiRiemannianHorizontal g vertical)
    (hx₂ : x₂ ∈ semiRiemannianHorizontal g vertical)
    (hy₁ : y₁ ∈ semiRiemannianHorizontal g vertical)
    (hy₂ : y₂ ∈ semiRiemannianHorizontal g vertical)
    (hx : q x₁ = q x₂) (hy : q y₁ = q y₂) :
    g x₁ y₁ = g x₂ y₂ := by
  have hxrad := horizontal_lifts_sub_mem_radical q hker hx₁ hx₂ hx
  have hyrad := horizontal_lifts_sub_mem_radical q hker hy₁ hy₂ hy
  have hx₂Total : x₂ ∈ semiRiemannianTotal g vertical :=
    Submodule.mem_sup_right hx₂
  have hy₂Total : y₂ ∈ semiRiemannianTotal g vertical :=
    Submodule.mem_sup_right hy₂
  calc
    g x₁ y₁ = g (x₂ + (x₁ - x₂)) (y₂ + (y₁ - y₂)) := by
      congr 1 <;> abel_nf
    _ = g x₂ y₂ :=
      semiRiemannian_pairing_add_radical hrefl hx₂Total hy₂Total hxrad hyrad

theorem horizontal_lift_unique_iff_radical_eq_bot
    {g : BilinForm K V} {vertical : Submodule K V} (q : V →ₗ[K] W)
    (hker : q.ker = vertical) :
    Function.Injective (q.domRestrict (semiRiemannianHorizontal g vertical)) ↔
      semiRiemannianRadical g vertical = ⊥ := by
  constructor
  · intro hinj
    apply le_antisymm
    · intro v hv
      rw [Submodule.mem_bot]
      have heq : (q.domRestrict (semiRiemannianHorizontal g vertical))
          ⟨v, hv.2⟩ = (q.domRestrict (semiRiemannianHorizontal g vertical)) 0 := by
        simpa using (show q v = 0 by
          rw [← LinearMap.mem_ker, hker]
          exact hv.1)
      exact Subtype.ext_iff.mp (hinj heq)
    · exact bot_le
  · intro hrad x y hxy
    apply Subtype.ext
    have hsub : (x : V) - y ∈ semiRiemannianRadical g vertical :=
      horizontal_lifts_sub_mem_radical q hker x.property y.property hxy
    rw [hrad, Submodule.mem_bot] at hsub
    exact sub_eq_zero.mp hsub

theorem nondegenerate_restrict_of_horizontal_radical_complement
    [FiniteDimensional K V]
    {g : BilinForm K V} (hnd : g.Nondegenerate) (hrefl : g.IsRefl)
    {vertical D : Submodule K V}
    (hD : D ≤ semiRiemannianHorizontal g vertical)
    (hsup : D ⊔ semiRiemannianRadical g vertical =
      semiRiemannianHorizontal g vertical)
    (hdisj : Disjoint D (semiRiemannianRadical g vertical)) :
    (g.restrict D).Nondegenerate := by
  apply g.nondegenerate_restrict_of_disjoint_orthogonal hrefl
  rw [Submodule.disjoint_def]
  intro x hxD hxDorth
  have hxH : x ∈ semiRiemannianHorizontal g vertical := hD hxD
  have hxHH : x ∈ g.orthogonal (g.orthogonal vertical) := by
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro u hu
    have hu' : u ∈ D ⊔ semiRiemannianRadical g vertical := by
      rw [hsup]
      exact hu
    rcases Submodule.mem_sup.mp hu' with ⟨d, hd, r, hr, rfl⟩
    have hdx : g d x = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hxDorth) d hd
    have hxTotal : x ∈ semiRiemannianTotal g vertical :=
      Submodule.mem_sup_right hxH
    have hrx : g r x = 0 :=
      semiRiemannianRadical_pairing_zero hrefl hr hxTotal
    simp [hdx, hrx]
  rw [g.orthogonal_orthogonal hnd hrefl vertical] at hxHH
  exact (Submodule.disjoint_def.mp hdisj) x hxD ⟨hxHH, hxH⟩

theorem nondegenerate_restrict_of_vertical_radical_complement
    {g : BilinForm K V} (hrefl : g.IsRefl)
    {vertical D : Submodule K V}
    (hD : D ≤ vertical)
    (hsup : D ⊔ semiRiemannianRadical g vertical = vertical)
    (hdisj : Disjoint D (semiRiemannianRadical g vertical)) :
    (g.restrict D).Nondegenerate := by
  apply g.nondegenerate_restrict_of_disjoint_orthogonal hrefl
  rw [Submodule.disjoint_def]
  intro x hxD hxDorth
  have hxV : x ∈ vertical := hD hxD
  have hxH : x ∈ semiRiemannianHorizontal g vertical := by
    apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
    intro u hu
    have hu' : u ∈ D ⊔ semiRiemannianRadical g vertical := by
      rw [hsup]
      exact hu
    rcases Submodule.mem_sup.mp hu' with ⟨d, hd, r, hr, rfl⟩
    have hdx : g d x = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hxDorth) d hd
    have hxTotal : x ∈ semiRiemannianTotal g vertical :=
      Submodule.mem_sup_left hxV
    have hrx : g r x = 0 :=
      semiRiemannianRadical_pairing_zero hrefl hr hxTotal
    simp [hdx, hrx]
  exact (Submodule.disjoint_def.mp hdisj) x hxD ⟨hxV, hxH⟩

namespace AlvesOliveiraApplications

open ExFlag

theorem hyperbolicForm_isRefl : hyperbolicForm.IsRefl := by
  intro x y h
  simpa [hyperbolicForm_apply, mul_comm, add_comm] using h

theorem hyperbolicForm_nondegenerate : hyperbolicForm.Nondegenerate := by
  constructor
  · intro x hx
    apply Prod.ext
    · simpa using hx ((0 : ℝ), (1 : ℝ))
    · simpa using hx ((1 : ℝ), (0 : ℝ))
  · intro y hy
    apply Prod.ext
    · simpa using hy ((0 : ℝ), (1 : ℝ))
    · simpa using hy ((1 : ℝ), (0 : ℝ))

theorem hyperbolicLine_radical :
    semiRiemannianRadical hyperbolicForm hyperbolicLine = hyperbolicLine := by
  simp [semiRiemannianRadical, semiRiemannianHorizontal,
    hyperbolicForm_orthogonal_line]

theorem hyperbolicLine_total :
    semiRiemannianTotal hyperbolicForm hyperbolicLine = hyperbolicLine := by
  simp [semiRiemannianTotal, semiRiemannianHorizontal,
    hyperbolicForm_orthogonal_line]

noncomputable def hyperbolicQuotientMap : (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  LinearMap.snd ℝ ℝ ℝ

theorem hyperbolicQuotientMap_ker :
    hyperbolicQuotientMap.ker = hyperbolicLine := by
  ext v
  simp [hyperbolicQuotientMap, mem_hyperbolicLine_iff]

theorem hyperbolic_horizontal_lift_not_unique :
    ¬ Function.Injective
      (hyperbolicQuotientMap.domRestrict
        (semiRiemannianHorizontal hyperbolicForm hyperbolicLine)) := by
  rw [horizontal_lift_unique_iff_radical_eq_bot hyperbolicQuotientMap
    hyperbolicQuotientMap_ker, hyperbolicLine_radical]
  intro h
  have hmem : ((1 : ℝ), (0 : ℝ)) ∈ hyperbolicLine :=
    mem_hyperbolicLine_iff.mpr rfl
  rw [h, Submodule.mem_bot] at hmem
  norm_num at hmem

theorem hyperbolic_horizontal_pairing_is_lift_independent
    {x₁ x₂ y₁ y₂ : ℝ × ℝ}
    (hx₁ : x₁ ∈ semiRiemannianHorizontal hyperbolicForm hyperbolicLine)
    (hx₂ : x₂ ∈ semiRiemannianHorizontal hyperbolicForm hyperbolicLine)
    (hy₁ : y₁ ∈ semiRiemannianHorizontal hyperbolicForm hyperbolicLine)
    (hy₂ : y₂ ∈ semiRiemannianHorizontal hyperbolicForm hyperbolicLine)
    (hx : hyperbolicQuotientMap x₁ = hyperbolicQuotientMap x₂)
    (hy : hyperbolicQuotientMap y₁ = hyperbolicQuotientMap y₂) :
    hyperbolicForm x₁ y₁ = hyperbolicForm x₂ y₂ :=
  horizontal_lift_pairing_independent hyperbolicForm_isRefl
    hyperbolicQuotientMap hyperbolicQuotientMap_ker
    hx₁ hx₂ hy₁ hy₂ hx hy

/-- In a Green self-dual flag, the horizontal space of the cycle space is exactly the boundary
space. This identifies the paper's vertical-horizontal intersection with existing homological
boundaries. -/
theorem green_horizontal_eq_boundary
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {g : BilinForm K V}
    (hnd : g.Nondegenerate) (hrefl : g.IsRefl)
    (p : ExFlag K V) (hgreen : IsGreenSelfDual g p) :
    semiRiemannianHorizontal g p.cycle = p.boundary := by
  simp only [semiRiemannianHorizontal]
  rw [hgreen, g.orthogonal_orthogonal hnd hrefl]

/-- The radical attached to a Green cycle space is precisely its boundary space. -/
theorem green_cycle_radical_eq_boundary
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {g : BilinForm K V}
    (hnd : g.Nondegenerate) (hrefl : g.IsRefl)
    (p : ExFlag K V) (hgreen : IsGreenSelfDual g p) :
    semiRiemannianRadical g p.cycle = p.boundary := by
  rw [semiRiemannianRadical,
    green_horizontal_eq_boundary hnd hrefl p hgreen]
  exact inf_eq_right.mpr p.boundary_le_cycle

/-- The vertical-plus-horizontal total space of a Green cycle is again the cycle space. -/
theorem green_cycle_total_eq_cycle
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {g : BilinForm K V}
    (hnd : g.Nondegenerate) (hrefl : g.IsRefl)
    (p : ExFlag K V) (hgreen : IsGreenSelfDual g p) :
    semiRiemannianTotal g p.cycle = p.cycle := by
  rw [semiRiemannianTotal,
    green_horizontal_eq_boundary hnd hrefl p hgreen]
  exact sup_eq_left.mpr p.boundary_le_cycle

theorem green_pairing_add_boundaries
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {g : BilinForm K V}
    (hnd : g.Nondegenerate) (hrefl : g.IsRefl)
    (p : ExFlag K V) (hgreen : IsGreenSelfDual g p)
    {v w b c : V} (hv : v ∈ p.cycle) (hw : w ∈ p.cycle)
    (hb : b ∈ p.boundary) (hc : c ∈ p.boundary) :
    g (v + b) (w + c) = g v w := by
  have horth : g.orthogonal p.cycle = p.boundary := by
    rw [hgreen, g.orthogonal_orthogonal hnd hrefl]
  have hbRad : b ∈ semiRiemannianRadical g p.cycle := by
    refine ⟨p.boundary_le_cycle hb, ?_⟩
    simpa [semiRiemannianHorizontal, horth] using hb
  have hcRad : c ∈ semiRiemannianRadical g p.cycle := by
    refine ⟨p.boundary_le_cycle hc, ?_⟩
    simpa [semiRiemannianHorizontal, horth] using hc
  exact semiRiemannian_pairing_add_radical hrefl
    (Submodule.mem_sup_left hv) (Submodule.mem_sup_left hw) hbRad hcRad

theorem stokes_form_add_radical
    {V : Type*} [AddCommGroup V] [Module ℝ V] {r : ℕ}
    (D : StokesPortData V r) {u₁ u₂ v₁ v₂ : V}
    (hv₁ : v₁ ∈ bilinearRadical D.form)
    (hv₂ : v₂ ∈ bilinearRadical D.form) :
    D.form (u₁ + v₁) (u₂ + v₂) = D.form u₁ u₂ := by
  have hv₁zero : D.form v₁ = 0 := hv₁
  have hv₂zero : D.form v₂ = 0 := hv₂
  have hu₁v₂ : D.form u₁ v₂ = 0 := by
    rw [D.symmetric u₁ v₂, hv₂zero]
    rfl
  simp only [map_add, LinearMap.add_apply, hv₁zero, hu₁v₂]
  simp

theorem stokes_quadratic_add_radical
    {V : Type*} [AddCommGroup V] [Module ℝ V] {r : ℕ}
    (D : StokesPortData V r) {u v : V}
    (hv : v ∈ bilinearRadical D.form) :
    D.form (u + v) (u + v) = D.form u u :=
  stokes_form_add_radical D hv hv

end AlvesOliveiraApplications

end GaloisForLFunctions.HTGeometry
