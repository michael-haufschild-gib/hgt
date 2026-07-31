import GaloisForLFunctions.HTGeometry.IsometricRecurrence
import GaloisForLFunctions.HTGeometry.GammaFinitePhaseCapstone
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# The vertical-strip Bohr hull and its local-uniform return

The finite-phase theorem needs a holomorphic function on a vertical strip whose *vertical* translates
return to it locally uniformly along times tending to `+∞`.  Almost periodicity is stated in the Bohr
topology: on each closed substrip strictly inside the strip, the translation orbit is relatively
compact for the supremum distance over that (vertically unbounded) substrip.

This file builds that hull and extracts the return sequence.

* `bcfVerticalAction` makes vertical translation an isometric additive `ℝ`-action on `S →ᵇ ℂ` for a
  vertically invariant `S`;
* `IsVerticalBohrAP` is Bochner's criterion for that action, and
  `hasVerticalUniformReturn_of_isVerticalBohrAP` turns it into arbitrarily late uniform return times
  through the abstract recurrence theorem;
* `exists_return_seq_tendstoLocallyUniformlyOn_openVerticalStrip` performs the diagonal choice over an
  exhausting family of closed substrips and produces a single sequence `T l → +∞` along which the
  vertical translates converge to `f` locally uniformly on the whole open strip;
* `verticalStrip_recurrence_collapse` feeds that sequence to the finite-phase capstone, so the
  local-uniform translate return is no longer a hypothesis of the collapse: only the coefficient
  projective boundary is.
-/

open Filter Topology
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

noncomputable section

/-- Vertical translation of the complex plane by a real time. -/
def verticalTranslate (t : ℝ) (z : ℂ) : ℂ := z + (t : ℂ) * Complex.I

@[simp] theorem verticalTranslate_apply (t : ℝ) (z : ℂ) :
    verticalTranslate t z = z + (t : ℂ) * Complex.I := rfl

@[simp] theorem verticalTranslate_re (t : ℝ) (z : ℂ) :
    (verticalTranslate t z).re = z.re := by
  simp [verticalTranslate]

theorem verticalTranslate_verticalTranslate (s t : ℝ) (z : ℂ) :
    verticalTranslate s (verticalTranslate t z) = verticalTranslate (s + t) z := by
  simp only [verticalTranslate, Complex.ofReal_add]
  ring

theorem verticalTranslate_neg_verticalTranslate (t : ℝ) (z : ℂ) :
    verticalTranslate t (verticalTranslate (-t) z) = z := by
  rw [verticalTranslate_verticalTranslate]
  simp [verticalTranslate]

/-- A set of complex numbers is vertically invariant when every real vertical translation maps it
into itself. -/
def IsVerticallyInvariant (S : Set ℂ) : Prop :=
  ∀ t : ℝ, ∀ z ∈ S, verticalTranslate t z ∈ S

/-- The closed vertical strip of half-width `η` about the abscissa `σ`. -/
def closedVerticalStrip (σ η : ℝ) : Set ℂ := {z : ℂ | |z.re - σ| ≤ η}

/-- The open vertical strip of half-width `η` about the abscissa `σ`. -/
def openVerticalStrip (σ η : ℝ) : Set ℂ := {z : ℂ | |z.re - σ| < η}

theorem mem_closedVerticalStrip {σ η : ℝ} {z : ℂ} :
    z ∈ closedVerticalStrip σ η ↔ |z.re - σ| ≤ η := Iff.rfl

theorem mem_openVerticalStrip {σ η : ℝ} {z : ℂ} :
    z ∈ openVerticalStrip σ η ↔ |z.re - σ| < η := Iff.rfl

theorem openVerticalStrip_subset_closedVerticalStrip (σ η : ℝ) :
    openVerticalStrip σ η ⊆ closedVerticalStrip σ η := fun _ hz =>
  mem_closedVerticalStrip.mpr (le_of_lt (mem_openVerticalStrip.mp hz))

theorem closedVerticalStrip_mono {σ η η' : ℝ} (h : η ≤ η') :
    closedVerticalStrip σ η ⊆ closedVerticalStrip σ η' := fun _ hz =>
  mem_closedVerticalStrip.mpr ((mem_closedVerticalStrip.mp hz).trans h)

theorem isOpen_openVerticalStrip (σ η : ℝ) : IsOpen (openVerticalStrip σ η) :=
  isOpen_lt ((Complex.continuous_re.sub continuous_const).abs) continuous_const

theorem isVerticallyInvariant_closedVerticalStrip (σ η : ℝ) :
    IsVerticallyInvariant (closedVerticalStrip σ η) := by
  intro t z hz
  simpa [closedVerticalStrip] using hz

theorem isVerticallyInvariant_openVerticalStrip (σ η : ℝ) :
    IsVerticallyInvariant (openVerticalStrip σ η) := by
  intro t z hz
  simpa [openVerticalStrip] using hz

section Action

variable {S : Set ℂ}

/-- Vertical translation as a self-map of a vertically invariant set. -/
def verticalTranslateSelf (hS : IsVerticallyInvariant S) (t : ℝ) : C(S, S) :=
  ⟨fun z => ⟨verticalTranslate t (z : ℂ), hS t (z : ℂ) z.2⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.add continuous_const⟩

@[simp] theorem verticalTranslateSelf_coe (hS : IsVerticallyInvariant S) (t : ℝ) (z : S) :
    ((verticalTranslateSelf hS t z : S) : ℂ) = verticalTranslate t (z : ℂ) := rfl

/-- Vertical translation of a bounded continuous function on a vertically invariant set. -/
def bcfVerticalTranslate (hS : IsVerticallyInvariant S) (t : ℝ) (g : S →ᵇ ℂ) : S →ᵇ ℂ :=
  g.compContinuous (verticalTranslateSelf hS t)

@[simp] theorem bcfVerticalTranslate_apply (hS : IsVerticallyInvariant S) (t : ℝ)
    (g : S →ᵇ ℂ) (z : S) :
    bcfVerticalTranslate hS t g z = g (verticalTranslateSelf hS t z) :=
  BoundedContinuousFunction.compContinuous_apply g (verticalTranslateSelf hS t) z

/-- Vertical translation is an additive action on bounded continuous functions. -/
theorem bcfVerticalTranslate_add (hS : IsVerticallyInvariant S) (s t : ℝ) (g : S →ᵇ ℂ) :
    bcfVerticalTranslate hS s (bcfVerticalTranslate hS t g) =
      bcfVerticalTranslate hS (s + t) g := by
  ext z
  simp only [bcfVerticalTranslate_apply]
  congr 1
  apply Subtype.ext
  simp only [verticalTranslateSelf_coe]
  rw [verticalTranslate_verticalTranslate, add_comm t s]

/-- Vertical translation preserves the supremum distance: it is an isometry of `S →ᵇ ℂ`. -/
theorem dist_bcfVerticalTranslate (hS : IsVerticallyInvariant S) (t : ℝ) (g h : S →ᵇ ℂ) :
    dist (bcfVerticalTranslate hS t g) (bcfVerticalTranslate hS t h) = dist g h := by
  refine le_antisymm ?_ ?_
  · refine (BoundedContinuousFunction.dist_le dist_nonneg).2 (fun z => ?_)
    simpa using
      BoundedContinuousFunction.dist_coe_le_dist (f := g) (g := h) (verticalTranslateSelf hS t z)
  · refine (BoundedContinuousFunction.dist_le dist_nonneg).2 (fun z => ?_)
    have hz : verticalTranslate (-t) (z : ℂ) ∈ S := hS (-t) (z : ℂ) z.2
    have hshift : verticalTranslateSelf hS t (⟨verticalTranslate (-t) (z : ℂ), hz⟩ : S) = z := by
      apply Subtype.ext
      simp only [verticalTranslateSelf_coe]
      exact verticalTranslate_neg_verticalTranslate t (z : ℂ)
    have hle := BoundedContinuousFunction.dist_coe_le_dist
      (f := bcfVerticalTranslate hS t g) (g := bcfVerticalTranslate hS t h)
      (⟨verticalTranslate (-t) (z : ℂ), hz⟩ : S)
    rwa [bcfVerticalTranslate_apply, bcfVerticalTranslate_apply, hshift] at hle

/-- Vertical translation as an isometric additive `ℝ`-action on the bounded continuous functions of
a vertically invariant set. -/
def bcfVerticalAction (hS : IsVerticallyInvariant S) : IsometricRAction (S →ᵇ ℂ) where
  act := bcfVerticalTranslate hS
  map_add := bcfVerticalTranslate_add hS
  isometry := fun t => Isometry.of_dist_eq (dist_bcfVerticalTranslate hS t)

/-- **Bohr almost periodicity on a vertically invariant set** (Bochner's criterion): the vertical
translation orbit is relatively compact for the supremum distance. -/
def IsVerticalBohrAP (hS : IsVerticallyInvariant S) (g : S →ᵇ ℂ) : Prop :=
  IsCompact (closure (Set.range fun t : ℝ => bcfVerticalTranslate hS t g))

end Action

/-- **Uniform vertical return.**  Arbitrarily late real times move `f` uniformly on `S` by at most
any prescribed amount.  This is the return property consumed by the recurrence collapse. -/
def HasVerticalUniformReturn (S : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ ε > 0, ∀ N : ℝ, ∃ t : ℝ, N ≤ t ∧ ∀ z ∈ S, ‖f (verticalTranslate t z) - f z‖ ≤ ε

/-- **Bochner's criterion supplies uniform return.**  A relatively compact vertical translation
orbit of a bounded continuous function on `S` gives arbitrarily late times at which the underlying
function returns to itself uniformly on `S`. -/
theorem hasVerticalUniformReturn_of_isVerticalBohrAP {S : Set ℂ}
    (hS : IsVerticallyInvariant S) {f : ℂ → ℂ} {g : S →ᵇ ℂ}
    (hg : IsVerticalBohrAP hS g) (hfg : ∀ z : S, g z = f (z : ℂ)) :
    HasVerticalUniformReturn S f := by
  intro ε hε N
  obtain ⟨t, htN, hdist⟩ :=
    isometricAction_recurrence (bcfVerticalAction hS) (x := g) hg hε N
  refine ⟨t, htN, fun z hz => ?_⟩
  have hpt := BoundedContinuousFunction.dist_coe_le_dist
    (f := bcfVerticalTranslate hS t g) (g := g) (⟨z, hz⟩ : S)
  have hlt : dist (bcfVerticalTranslate hS t g (⟨z, hz⟩ : S)) (g (⟨z, hz⟩ : S)) < ε :=
    lt_of_le_of_lt hpt hdist
  rw [bcfVerticalTranslate_apply, hfg, hfg, verticalTranslateSelf_coe, dist_eq_norm] at hlt
  exact hlt.le

/-- A vertical translate of a function holomorphic on a vertically invariant open set is again
holomorphic there. -/
theorem differentiableOn_comp_verticalTranslate {U : Set ℂ} (hU : IsVerticallyInvariant U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (t : ℝ) :
    DifferentiableOn ℂ (fun z => f (verticalTranslate t z)) U := by
  intro z hz
  have hgt : DifferentiableWithinAt ℂ f U (verticalTranslate t z) := hf _ (hU t z hz)
  have hft : DifferentiableWithinAt ℂ (fun w : ℂ => verticalTranslate t w) U z :=
    (differentiableAt_id.add_const ((t : ℂ) * Complex.I)).differentiableWithinAt
  exact hgt.comp z hft (fun w hw => hU t w hw)

private theorem eventually_div_add_two_lt (a : ℝ) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ l : ℕ in atTop, a / ((l : ℝ) + 2) < c := by
  obtain ⟨n, hn⟩ := exists_nat_gt (a / c)
  rw [Filter.eventually_atTop]
  refine ⟨n, fun l hl => ?_⟩
  have hden : (0 : ℝ) < (l : ℝ) + 2 := by positivity
  have hcast : (n : ℝ) ≤ (l : ℝ) := Nat.cast_le.mpr hl
  have hln : a / c < (l : ℝ) + 2 := by linarith
  rw [div_lt_iff₀ hc] at hln
  rw [div_lt_iff₀ hden]
  linarith

/-- **Diagonal return sequence on an open vertical strip.**  Suppose `f` has the uniform vertical
return property on every closed substrip strictly inside the open strip of half-width `η`.  Then a
single sequence of times `T l → +∞` makes the vertical translates of `f` converge to `f` locally
uniformly on the whole open strip.  The diagonal is over an exhausting family of substrips of
half-widths `η - η / (l + 2) ↑ η` with tolerances `1 / (l + 2) ↓ 0`. -/
theorem exists_return_seq_tendstoLocallyUniformlyOn_openVerticalStrip
    {σ η : ℝ} (hη : 0 < η) {f : ℂ → ℂ}
    (hap : ∀ η' : ℝ, 0 < η' → η' < η → HasVerticalUniformReturn (closedVerticalStrip σ η') f) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
      TendstoLocallyUniformlyOn (fun l z => f (verticalTranslate (T l) z)) f atTop
        (openVerticalStrip σ η) := by
  have hkey : ∀ l : ℕ, ∃ t : ℝ, (l : ℝ) ≤ t ∧
      ∀ z ∈ closedVerticalStrip σ (η - η / ((l : ℝ) + 2)),
        ‖f (verticalTranslate t z) - f z‖ ≤ 1 / ((l : ℝ) + 2) := by
    intro l
    have hden : (0 : ℝ) < (l : ℝ) + 2 := by positivity
    have hsmall : η / ((l : ℝ) + 2) < η := by
      refine div_lt_self hη ?_
      have : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
      linarith
    have hpos : 0 < η - η / ((l : ℝ) + 2) := sub_pos.mpr hsmall
    have hlt : η - η / ((l : ℝ) + 2) < η := by
      have : 0 < η / ((l : ℝ) + 2) := by positivity
      linarith
    exact hap _ hpos hlt (1 / ((l : ℝ) + 2)) (by positivity) (l : ℝ)
  choose T hT1 hT2 using hkey
  refine ⟨T, tendsto_atTop_mono hT1 tendsto_natCast_atTop_atTop, ?_⟩
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  set η' : ℝ := (|x.re - σ| + η) / 2 with hη'
  have hxlt : |x.re - σ| < η := hx
  have hη'lt : η' < η := by rw [hη']; linarith
  have hxη' : |x.re - σ| < η' := by rw [hη']; linarith
  have hη'pos : 0 < η' := lt_of_le_of_lt (abs_nonneg _) hxη'
  refine ⟨openVerticalStrip σ η', ?_, ?_⟩
  · exact mem_nhdsWithin_of_mem_nhds ((isOpen_openVerticalStrip σ η').mem_nhds hxη')
  · have h1 : ∀ᶠ l : ℕ in atTop, η / ((l : ℝ) + 2) < η - η' :=
      eventually_div_add_two_lt η (by linarith)
    have h2 : ∀ᶠ l : ℕ in atTop, 1 / ((l : ℝ) + 2) < ε :=
      eventually_div_add_two_lt 1 hε
    filter_upwards [h1, h2] with l hl1 hl2 y hy
    have hywidth : |y.re - σ| ≤ η - η / ((l : ℝ) + 2) := by
      have : |y.re - σ| < η' := hy
      linarith
    have hbound := hT2 l y hywidth
    rw [dist_eq_norm, norm_sub_rev]
    exact lt_of_le_of_lt hbound hl2

/-- **Vertical-strip finite-phase collapse (§5, eq. 8).**  Let `f` be holomorphic on the open
vertical strip of half-width `η` about `σ` and Bohr almost periodic there in the sense that it has
the uniform vertical return property on every closed substrip.  Then there is a single sequence of
return times `T l → +∞` such that, whenever the Gamma-field coefficients of a finite differential
relation satisfied by `f` have the one-point projective boundary along those times, the relation
collapses to a nontrivial autonomous algebraic differential relation at every point of the strip.

The local-uniform translate return, previously a hypothesis of `holomorphic_recurrence_collapse`, is
now produced from almost periodicity alone; the surviving input is exactly the coefficient
projective boundary. -/
theorem verticalStrip_recurrence_collapse {ι : Type*} (E : Finset ι)
    {σ η : ℝ} (hη : 0 < η) (f : ℂ → ℂ) (exps : ι → (ℕ →₀ ℕ)) (F : ι → ℂ → ℂ) (β : ι) (hβ : β ∈ E)
    (hf : DifferentiableOn ℂ f (openVerticalStrip σ η))
    (hap : ∀ η' : ℝ, 0 < η' → η' < η → HasVerticalUniformReturn (closedVerticalStrip σ η') f)
    (hrel : ∀ s : ℂ, ∑ α ∈ E, F α s * diffMonomial f (exps α) s = 0) :
    ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧
      ∀ z₀ ∈ openVerticalStrip σ η, ∀ d : ι → ℂ,
        (∀ᶠ l in atTop, F β (z₀ + (T l : ℂ) * Complex.I) ≠ 0) →
        (∀ α ∈ E, Tendsto
          (fun l => F α (z₀ + (T l : ℂ) * Complex.I) / F β (z₀ + (T l : ℂ) * Complex.I))
          atTop (nhds (d α))) →
        (∑ α ∈ E, d α * diffMonomial f (exps α) z₀ = 0) ∧ d β = 1 := by
  obtain ⟨T, hT, hconv⟩ :=
    exists_return_seq_tendstoLocallyUniformlyOn_openVerticalStrip (σ := σ) hη hap
  refine ⟨T, hT, fun z₀ hz₀ d hFβ hcoeff => ?_⟩
  refine holomorphic_recurrence_collapse_eventually E (isOpen_openVerticalStrip σ η) f exps F β hβ
    hz₀ T d ?_ ?_ hrel hFβ hcoeff
  · exact Filter.Eventually.of_forall fun l =>
      differentiableOn_comp_verticalTranslate (isVerticallyInvariant_openVerticalStrip σ η) hf (T l)
  · exact hconv

end

end GaloisForLFunctions
