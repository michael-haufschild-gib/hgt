import GaloisForLFunctions.RHTower.RelativeStripDivisorReflection

/-!
# Non-archimedean stability of the Euler-to-divisor map

Two exponents are attached to a pair of completed Euler products: the absolute-convergence abscissa
`σ_E` of their logarithmic Euler discrepancy, and the outer horizontal exponent `σ_D` of their
nontrivial divisor difference.  Both obey the *max*-triangle law, so after exponentiation they are
extended ultrapseudometrics, and the relative-strip inequality makes the Euler-to-divisor map
non-expanding.

Consequently the critical value `1/2` is a topological threshold: a class with `σ_E ≤ 1/2` has a
fixed off-critical divisor, a class with `σ_E < 1/2` has a fixed nontrivial divisor, and — since
every ultrametric space is totally disconnected — no divisor motion can happen along a continuous
family.

## Main results

* `abscissa_le_max` — the max-triangle law for absolute-convergence abscissae;
* `divisorExponent_le_max` — the max-triangle law for the outer divisor exponent;
* `divisorExponent_le_of_forall`, `divisorExponent_le_of_reflection` — non-expansion;
* `re_eq_half_of_divisorExponent_le`, `eq_empty_of_divisorExponent_lt` — the two threshold classes;
* `strong_triangle_of_monotone_max` — exponentiation gives an ultrapseudometric;
* `constant_of_connected_of_ultrametric` — continuous families cannot move the divisor.
-/

noncomputable section

namespace RHTower

open scoped ENNReal

/-! ### The absolute-convergence abscissa -/

/-- The set of exponents to the right of which a weighted coefficient family is absolutely
summable. -/
def convSet {ι : Type*} (c : ι → ℝ) (w : ι → ℝ → ℝ) : Set EReal :=
  {u : EReal | ∀ v : ℝ, u < (v : EReal) → Summable (fun i => |c i| * w i v)}

/-- The absolute-convergence abscissa of a weighted coefficient family. -/
def abscissa {ι : Type*} (c : ι → ℝ) (w : ι → ℝ → ℝ) : EReal := sInf (convSet c w)

theorem summable_of_abscissa_lt {ι : Type*} {c : ι → ℝ} {w : ι → ℝ → ℝ} {v : ℝ}
    (hv : abscissa c w < (v : EReal)) : Summable (fun i => |c i| * w i v) := by
  obtain ⟨u, hu, huv⟩ := (sInf_lt_iff).mp hv
  exact hu v huv

/-- **The max-triangle law for abscissae.**  A coefficient family that splits as a sum has abscissa
at most the maximum of the two summands' abscissae. -/
theorem abscissa_le_max {ι : Type*} {c₁ c₂ c₃ : ι → ℝ} {w : ι → ℝ → ℝ}
    (hw : ∀ i v, 0 ≤ w i v) (hsplit : ∀ i, c₃ i = c₁ i + c₂ i) :
    abscissa c₃ w ≤ max (abscissa c₁ w) (abscissa c₂ w) := by
  refine sInf_le ?_
  intro v hv
  have h₁ : abscissa c₁ w < (v : EReal) := lt_of_le_of_lt (le_max_left _ _) hv
  have h₂ : abscissa c₂ w < (v : EReal) := lt_of_le_of_lt (le_max_right _ _) hv
  refine Summable.of_nonneg_of_le (fun i => mul_nonneg (abs_nonneg _) (hw i v)) (fun i => ?_)
    ((summable_of_abscissa_lt h₁).add (summable_of_abscissa_lt h₂))
  rw [hsplit i]
  calc |c₁ i + c₂ i| * w i v ≤ (|c₁ i| + |c₂ i|) * w i v := by
        exact mul_le_mul_of_nonneg_right (abs_add_le _ _) (hw i v)
    _ = |c₁ i| * w i v + |c₂ i| * w i v := by ring

/-! ### The outer divisor exponent -/

/-- The outer horizontal exponent of a divisor support. -/
def divisorExponent (S : Set ℂ) : EReal := ⨆ ρ ∈ S, ((max ρ.re (1 - ρ.re) : ℝ) : EReal)

theorem le_divisorExponent {S : Set ℂ} {ρ : ℂ} (hρ : ρ ∈ S) :
    ((max ρ.re (1 - ρ.re) : ℝ) : EReal) ≤ divisorExponent S :=
  le_iSup₂ (f := fun ρ (_ : ρ ∈ S) => ((max ρ.re (1 - ρ.re) : ℝ) : EReal)) ρ hρ

theorem divisorExponent_empty : divisorExponent ∅ = ⊥ := by
  simp [divisorExponent]

theorem divisorExponent_mono {S T : Set ℂ} (h : S ⊆ T) :
    divisorExponent S ≤ divisorExponent T := by
  refine iSup₂_le (fun ρ hρ => le_divisorExponent (h hρ))

/-- **The max-triangle law for divisor exponents.**  Cancellation can remove support but never
creates a point outside the union. -/
theorem divisorExponent_le_max {S₁ S₂ S₃ : Set ℂ} (h : S₃ ⊆ S₁ ∪ S₂) :
    divisorExponent S₃ ≤ max (divisorExponent S₁) (divisorExponent S₂) := by
  refine iSup₂_le (fun ρ hρ => ?_)
  rcases h hρ with h1 | h2
  · exact le_trans (le_divisorExponent h1) (le_max_left _ _)
  · exact le_trans (le_divisorExponent h2) (le_max_right _ _)

/-- **Non-expansion.**  The relative-strip inequality bounds the divisor exponent by the Euler
exponent. -/
theorem divisorExponent_le_of_forall {S : Set ℂ} {σ : EReal}
    (h : ∀ ρ ∈ S, ((max ρ.re (1 - ρ.re) : ℝ) : EReal) ≤ σ) :
    divisorExponent S ≤ σ :=
  iSup₂_le h

/-- **Non-expansion from the reflection band.**  A divisor support avoiding `Re s > A` and stable
under `s ↦ 1 - s` has outer exponent at most `A`.  Composed with the relative-strip theorem this is
the non-expansion inequality `σ_D ≤ σ_E`. -/
theorem divisorExponent_le_of_reflection {S : Set ℂ} {A : ℝ}
    (hright : ∀ ρ ∈ S, ρ.re ≤ A) (hrefl : ∀ ρ ∈ S, (1 - ρ) ∈ S) :
    divisorExponent S ≤ ((A : ℝ) : EReal) := by
  refine divisorExponent_le_of_forall (fun ρ hρ => ?_)
  exact_mod_cast max_re_le_of_reflection hright hrefl hρ

/-! ### The threshold classes -/

theorem half_le_max_re (ρ : ℂ) : (1 / 2 : ℝ) ≤ max ρ.re (1 - ρ.re) := by
  rcases le_total ρ.re (1 / 2 : ℝ) with h | h
  · exact le_trans (by linarith) (le_max_right _ _)
  · exact le_trans h (le_max_left _ _)

/-- **The critical ball has constant off-line divisor.** -/
theorem re_eq_half_of_divisorExponent_le {S : Set ℂ}
    (h : divisorExponent S ≤ ((1 / 2 : ℝ) : EReal)) {ρ : ℂ} (hρ : ρ ∈ S) : ρ.re = 1 / 2 := by
  have hle : ((max ρ.re (1 - ρ.re) : ℝ) : EReal) ≤ ((1 / 2 : ℝ) : EReal) :=
    le_trans (le_divisorExponent hρ) h
  have hreal : max ρ.re (1 - ρ.re) ≤ 1 / 2 := by exact_mod_cast hle
  have h1 : ρ.re ≤ 1 / 2 := le_trans (le_max_left _ _) hreal
  have h2 : 1 - ρ.re ≤ 1 / 2 := le_trans (le_max_right _ _) hreal
  linarith

/-- **Below the critical ball the whole nontrivial divisor is constant.** -/
theorem eq_empty_of_divisorExponent_lt {S : Set ℂ}
    (h : divisorExponent S < ((1 / 2 : ℝ) : EReal)) : S = ∅ := by
  by_contra hne
  obtain ⟨ρ, hρ⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hle : ((max ρ.re (1 - ρ.re) : ℝ) : EReal) ≤ divisorExponent S := le_divisorExponent hρ
  have hlt : ((max ρ.re (1 - ρ.re) : ℝ) : EReal) < ((1 / 2 : ℝ) : EReal) := lt_of_le_of_lt hle h
  have hreal : max ρ.re (1 - ρ.re) < 1 / 2 := by exact_mod_cast hlt
  linarith [half_le_max_re ρ]

/-! ### Exponentiation -/

/-- **Exponentiation preserves the strong triangle law.**  Any monotone, `max`-preserving transfer
turns the exponent form into an ultrapseudometric. -/
theorem strong_triangle_of_monotone_max {X : Type*} {σ : X → X → EReal} {φ : EReal → ℝ}
    (hmax : ∀ a b : EReal, φ (max a b) = max (φ a) (φ b))
    (hmono : Monotone φ) {x y z : X}
    (htri : σ x z ≤ max (σ x y) (σ y z)) :
    φ (σ x z) ≤ max (φ (σ x y)) (φ (σ y z)) := by
  calc φ (σ x z) ≤ φ (max (σ x y) (σ y z)) := hmono htri
    _ = max (φ (σ x y)) (φ (σ y z)) := hmax _ _

/-! ### Ultrametric path rigidity -/

/-- **No divisor motion along a continuous family.**  Every continuous map from a connected space
into an ultrametric space is constant, because an ultrametric space is totally disconnected. -/
theorem constant_of_connected_of_ultrametric {X Y : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [MetricSpace Y] [IsUltrametricDist Y] (f : X → Y)
    (hf : Continuous f) (x y : X) : f x = f y := by
  have hconn : IsPreconnected (Set.range f) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image f hf.continuousOn
  have hsub : (Set.range f).Subsingleton := hconn.subsingleton
  exact hsub ⟨x, rfl⟩ ⟨y, rfl⟩

end RHTower
