import GaloisForLFunctions.Hypertranscendence

/-!
# Exponential-gauge selection for hypertranscendence

The class of elements differentially algebraic over a base differential field is itself a
differential field and is relatively closed under solutions of algebraic differential equations.
For a static exponential gauge `u c = exp(c h)`, multiplication does not alter divisor data.  This
file isolates the algebraic selection rule behind the resulting constraint geometry:

* in several parameters, a nonempty exceptional set is exactly one affine coset of the linear
  subspace of directions whose logarithmic derivatives lie in the distinguished field;
* if the gauge direction has derivative outside the distinguished differential field, a
  multiplicative translate of the gauge meets that field in at most one parameter;
* if the distinguished field is closed under logarithmic primitives, the exceptional parameter
  set is empty, a singleton, or the whole parameter field.

The development is abstract.  In the meromorphic specialization, `A` is the field of functions
differentially algebraic over the chosen base, `D` is differentiation, `dh = h'`, and
`u c = exp(c h)`.  No flow or limiting process is involved: the parameter indexes a family of
static representatives inside one zero-free multiplicative gauge fiber.
-/

namespace GaloisForLFunctions

variable {C F : Type*} [Field C] [Field F] [Algebra C F]

/-- A static differential exponential gauge: its members are nonzero, pairwise quotients subtract
parameters, and their logarithmic derivatives are scalar multiples of one fixed direction. -/
def IsDifferentialExponentialGauge (D : Derivation C F F) (dh : F) (u : C → F) : Prop :=
  (∀ c, u c ≠ 0) ∧
  (∀ c d, u c / u d = u (c - d)) ∧
  (∀ c, D (u c) / u c = algebraMap C F c * dh)

/-- Relative closure under nonzero solutions of first-order logarithmic-derivative equations.
The field of elements differentially algebraic over a base field has this property by transitivity
of differential algebraicity. -/
def ClosedUnderLogarithmicPrimitives
    (A : IntermediateField C F) (D : Derivation C F F) : Prop :=
  ∀ {a y : F}, a ∈ A → y ≠ 0 → D y / y = a → y ∈ A

section Multidimensional

variable {V : Type*} [AddCommGroup V] [Module C V]

/-- A multi-parameter static exponential gauge.  In the analytic model,
`u v = exp(∑ᵢ vᵢ hᵢ)` and `direction v = ∑ᵢ vᵢ hᵢ'`. -/
def IsDifferentialExponentialFamily (D : Derivation C F F)
    (direction : V →ₗ[C] F) (u : V → F) : Prop :=
  (∀ v, u v ≠ 0) ∧
  (∀ v w, u (v + w) = u v * u w) ∧
  (∀ v, D (u v) / u v = direction v)

/-- Parameter directions whose logarithmic derivatives lie in the distinguished differential
field.  This is the native linear constraint space of a multi-parameter exponential gauge. -/
def differentialRelationSubmodule (A : IntermediateField C F)
    (direction : V →ₗ[C] F) : Submodule C V where
  carrier := {v | direction v ∈ A}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw
    simpa using A.add_mem hv hw
  smul_mem' := by
    intro c v hv
    have := A.mul_mem (A.algebraMap_mem c) hv
    simpa using this

/-- **Affine-coset classification.**  Once a multi-parameter exponential gauge has one member in
the distinguished differential field, every other such member is obtained by translating the
base parameter by a direction whose logarithmic derivative belongs to that field.  Thus the full
exceptional set is exactly one affine coset of `differentialRelationSubmodule`. -/
theorem exceptionalParameters_eq_relationCoset
    (A : IntermediateField C F) (D : Derivation C F F)
    (hD : ∀ {x : F}, x ∈ A → D x ∈ A)
    (hclosed : ClosedUnderLogarithmicPrimitives A D)
    {direction : V →ₗ[C] F} {g : F} {u : V → F}
    (hg : g ≠ 0) (hgauge : IsDifferentialExponentialFamily D direction u)
    {c0 : V} (hc0 : g * u c0 ∈ A) :
    {c : V | g * u c ∈ A} =
      {c : V | c - c0 ∈ differentialRelationSubmodule A direction} := by
  ext c
  constructor
  · intro hc
    have hratio : (g * u c) / (g * u c0) ∈ A := A.div_mem hc hc0
    have hucd : u c / u c0 ∈ A := by
      rwa [mul_div_mul_left _ _ hg] at hratio
    have hufactor : u c / u c0 = u (c - c0) := by
      have hadd := hgauge.2.1 (c - c0) c0
      rw [sub_add_cancel] at hadd
      rw [hadd, mul_div_cancel_right₀ _ (hgauge.1 c0)]
    have hudiff : u (c - c0) ∈ A := by
      rwa [hufactor] at hucd
    have hld : D (u (c - c0)) / u (c - c0) ∈ A :=
      A.div_mem (hD hudiff) hudiff
    change direction (c - c0) ∈ A
    rwa [← hgauge.2.2 (c - c0)]
  · intro hc
    change direction (c - c0) ∈ A at hc
    have hudiff : u (c - c0) ∈ A := by
      apply hclosed hc (hgauge.1 (c - c0))
      exact hgauge.2.2 (c - c0)
    have hproduct : (g * u c0) * u (c - c0) ∈ A := A.mul_mem hc0 hudiff
    have hadd := hgauge.2.1 c0 (c - c0)
    rw [add_sub_cancel] at hadd
    change g * u c ∈ A
    rw [hadd]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hproduct

end Multidimensional

/-- **One-exception selection rule.**  If the gauge direction lies outside a differential subfield,
then any nonzero multiplicative translate of the gauge meets that subfield in at most one
parameter.  Two exceptional parameters would put the quotient gauge in the field; taking its
logarithmic derivative would put the forbidden direction there as well. -/
theorem exceptionalParameters_subsingleton
    (A : IntermediateField C F) (D : Derivation C F F)
    (hD : ∀ {x : F}, x ∈ A → D x ∈ A)
    {dh g : F} {u : C → F}
    (hg : g ≠ 0) (hgauge : IsDifferentialExponentialGauge D dh u)
    (hdh : dh ∉ A) :
    {c : C | g * u c ∈ A}.Subsingleton := by
  rintro c hc d hd
  by_contra hcd
  rcases hgauge with ⟨_, hquot, hlog⟩
  have hratio : (g * u c) / (g * u d) ∈ A := A.div_mem hc hd
  have hucd : u c / u d ∈ A := by
    rwa [mul_div_mul_left _ _ hg] at hratio
  have husub : u (c - d) ∈ A := by
    rw [← hquot c d]
    exact hucd
  have hld : D (u (c - d)) / u (c - d) ∈ A :=
    A.div_mem (hD husub) husub
  have hscaled : algebraMap C F (c - d) * dh ∈ A := by
    rw [← hlog (c - d)]
    exact hld
  have ha : algebraMap C F (c - d) ≠ 0 := by
    rw [map_ne_zero]
    exact sub_ne_zero.mpr hcd
  have hinv : (algebraMap C F (c - d))⁻¹ ∈ A :=
    A.inv_mem (A.algebraMap_mem (c - d))
  have hmem : (algebraMap C F (c - d))⁻¹ *
      (algebraMap C F (c - d) * dh) ∈ A := A.mul_mem hinv hscaled
  apply hdh
  have ha' : algebraMap C F c - algebraMap C F d ≠ 0 := by
    simpa using ha
  simpa [map_sub, ha', mul_assoc] using hmem

/-- When the gauge direction belongs to a logarithmically closed differential field, every gauge
member belongs to that field. -/
theorem gauge_mem_of_direction_mem
    (A : IntermediateField C F) (D : Derivation C F F)
    (hclosed : ClosedUnderLogarithmicPrimitives A D)
    {dh : F} {u : C → F}
    (hgauge : IsDifferentialExponentialGauge D dh u)
    (hdh : dh ∈ A) (c : C) : u c ∈ A := by
  rcases hgauge with ⟨hu0, _, hlog⟩
  apply hclosed (A.mul_mem (A.algebraMap_mem c) hdh) (hu0 c)
  exact hlog c

/-- **Zero-one-all law, compressed form.**  On a differential exponential-gauge pencil, the
distinguished differential field occurs at at most one parameter or at every parameter. -/
theorem exceptionalParameters_subsingleton_or_eq_univ
    (A : IntermediateField C F) (D : Derivation C F F)
    (hD : ∀ {x : F}, x ∈ A → D x ∈ A)
    (hclosed : ClosedUnderLogarithmicPrimitives A D)
    {dh g : F} {u : C → F}
    (hg : g ≠ 0) (hgauge : IsDifferentialExponentialGauge D dh u) :
    {c : C | g * u c ∈ A}.Subsingleton ∨ {c : C | g * u c ∈ A} = Set.univ := by
  by_cases hdh : dh ∈ A
  · by_cases hex : ∃ c : C, g * u c ∈ A
    · right
      obtain ⟨c0, hc0⟩ := hex
      have hu0mem := gauge_mem_of_direction_mem A D hclosed hgauge hdh c0
      have hu0ne : u c0 ≠ 0 := hgauge.1 c0
      have hgmem : g ∈ A := by
        have := A.div_mem hc0 hu0mem
        simpa [mul_div_cancel_right₀ g hu0ne] using this
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact A.mul_mem hgmem (gauge_mem_of_direction_mem A D hclosed hgauge hdh c)
    · left
      intro c hc
      exact False.elim (hex ⟨c, hc⟩)
  · left
    exact exceptionalParameters_subsingleton A D hD hg hgauge hdh

/-- **Zero-one-all law, explicit form.**  The exceptional parameter set is empty, a singleton, or
the whole parameter field; no exponential-gauge pencil has exactly two (or any larger finite proper
number of) differentially algebraic members. -/
theorem exceptionalParameters_eq_empty_or_singleton_or_univ
    (A : IntermediateField C F) (D : Derivation C F F)
    (hD : ∀ {x : F}, x ∈ A → D x ∈ A)
    (hclosed : ClosedUnderLogarithmicPrimitives A D)
    {dh g : F} {u : C → F}
    (hg : g ≠ 0) (hgauge : IsDifferentialExponentialGauge D dh u) :
    {c : C | g * u c ∈ A} = ∅ ∨
      (∃ c : C, {x : C | g * u x ∈ A} = {c}) ∨
      {c : C | g * u c ∈ A} = Set.univ := by
  rcases exceptionalParameters_subsingleton_or_eq_univ A D hD hclosed hg hgauge with hsub | hall
  · by_cases hempty : {c : C | g * u c ∈ A} = ∅
    · exact Or.inl hempty
    · right
      left
      have hnonempty : {c : C | g * u c ∈ A}.Nonempty := Set.nonempty_iff_ne_empty.mpr hempty
      obtain ⟨c, hc⟩ := hnonempty
      refine ⟨c, Set.Subset.antisymm ?_ ?_⟩
      · intro x hx
        simpa only [Set.mem_singleton_iff] using hsub hx hc
      · intro x hx
        simpa only [Set.mem_singleton_iff] at hx
        simpa [hx] using hc
  · exact Or.inr (Or.inr hall)

end GaloisForLFunctions
