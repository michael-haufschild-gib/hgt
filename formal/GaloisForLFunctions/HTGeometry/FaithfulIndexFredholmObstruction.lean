import Mathlib

/-!
# The continuous-Fredholm obstruction for a faithful negative index

`faithful-krein-index-escape-stratification`, the continuous-Fredholm obstruction.

A bounded self-adjoint operator `A` on a Hilbert space is *Fredholm at zero with finite-dimensional
negative spectral subspace* exactly when it is uniformly positive off a subspace of finite
dimension: `∃ ε > 0` and `V, U` with `V ⊔ U = ⊤`, `dim U ≤ d` and `ε‖x‖² ≤ Re⟪x, A x⟫` on `V`.
(The spectral subspace of `(-∞, ε)` is then contained in a `d`-dimensional space; equivalently the
negative and near-zero spectral subspaces are finite-dimensional and `0` is not in the essential
spectrum.)  This module takes that gap property as the hypothesis and proves the two facts the
card's obstruction argument uses:

* `negIndexAtMost_of_coerciveComplement` — the negative Morse index is *stable*: every operator
  within distance `ε` of `A` has negative index at most `d`;
* `no_faithful_continuous_index_of_unbounded_witness` — hence no assignment that is continuous into
  the operator norm can carry a negative Morse index which exceeds `d` along a convergent net.

Nothing here is specific to Herglotz carriers, `ξ`, or RH.
-/

open Submodule Filter

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The negative Morse index of `A` is at most `m`: every finite-dimensional subspace on which the
quadratic form of `A` is strictly negative has dimension at most `m`. -/
def NegIndexAtMost (A : H →L[ℂ] H) (m : ℕ) : Prop :=
  ∀ W : Submodule ℂ H, FiniteDimensional ℂ W →
    (∀ x ∈ W, x ≠ 0 → (inner ℂ x (A x) : ℂ).re < 0) → Module.finrank ℂ W ≤ m

/-- `A` is uniformly positive off a subspace of dimension at most `d`.  This is the gap form of
"self-adjoint Fredholm at `0` with finite-dimensional negative spectral subspace". -/
def HasCoerciveComplement (A : H →L[ℂ] H) (ε : ℝ) (d : ℕ) : Prop :=
  0 < ε ∧ ∃ V U : Submodule ℂ H,
    FiniteDimensional ℂ U ∧ Module.finrank ℂ U ≤ d ∧ V ⊔ U = ⊤ ∧
      ∀ x ∈ V, ε * ‖x‖ ^ (2 : ℕ) ≤ (inner ℂ x (A x) : ℂ).re

/-! ## A dimension bound across a finite-codimension subspace -/

theorem finrank_le_of_trivial_meet_of_sup_eq_top
    {V U W : Submodule ℂ H} (hU : FiniteDimensional ℂ U)
    (hsup : V ⊔ U = ⊤)
    (hdisj : ∀ x ∈ W, x ∈ V → x = 0) :
    Module.finrank ℂ W ≤ Module.finrank ℂ U := by
  classical
  have hsurj : Function.Surjective ((V.mkQ).comp U.subtype) := by
    intro y
    obtain ⟨x, rfl⟩ := V.mkQ_surjective y
    have hx : x ∈ V ⊔ U := by rw [hsup]; trivial
    obtain ⟨v, hv, u, hu, rfl⟩ := Submodule.mem_sup.mp hx
    refine ⟨⟨u, hu⟩, ?_⟩
    have hv0 : V.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero V).mpr hv
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, map_add, hv0, zero_add]
  have hrange : LinearMap.range ((V.mkQ).comp U.subtype) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hfinQ : FiniteDimensional ℂ (H ⧸ V) := Module.Finite.of_surjective _ hsurj
  have hle1 : Module.finrank ℂ (H ⧸ V) ≤ Module.finrank ℂ U := by
    have h := LinearMap.finrank_range_le ((V.mkQ).comp U.subtype)
    rw [hrange, finrank_top] at h
    exact h
  have hinj : Function.Injective ((V.mkQ).comp W.subtype) := by
    intro a b hab
    have hsub : ((a : H) - (b : H)) ∈ V := by
      have h0 : V.mkQ ((a : H) - (b : H)) = 0 := by
        rw [map_sub]
        simpa only [LinearMap.comp_apply, Submodule.subtype_apply] using sub_eq_zero.mpr hab
      exact (Submodule.Quotient.mk_eq_zero V).mp h0
    have := hdisj ((a : H) - (b : H)) (sub_mem a.2 b.2) hsub
    exact Subtype.ext (sub_eq_zero.mp this)
  have hle2 : Module.finrank ℂ W ≤ Module.finrank ℂ (H ⧸ V) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  omega

/-! ## Stability of the negative Morse index -/

theorem abs_re_inner_sub_le {A B : H →L[ℂ] H} (x : H) :
    |(inner ℂ x (B x) : ℂ).re - (inner ℂ x (A x) : ℂ).re| ≤ ‖B - A‖ * ‖x‖ ^ (2 : ℕ) := by
  have hval : (inner ℂ x (B x) : ℂ) - (inner ℂ x (A x) : ℂ) = inner ℂ x ((B - A) x) := by
    rw [sub_apply, inner_sub_right]
  have h1 : |(inner ℂ x ((B - A) x) : ℂ).re| ≤ ‖(inner ℂ x ((B - A) x) : ℂ)‖ :=
    Complex.abs_re_le_norm _
  have h2 : ‖(inner ℂ x ((B - A) x) : ℂ)‖ ≤ ‖x‖ * ‖(B - A) x‖ := norm_inner_le_norm _ _
  have h3 : ‖(B - A) x‖ ≤ ‖B - A‖ * ‖x‖ := ContinuousLinearMap.le_opNorm _ _
  have hx : (0 : ℝ) ≤ ‖x‖ := norm_nonneg _
  have hre : (inner ℂ x (B x) : ℂ).re - (inner ℂ x (A x) : ℂ).re
      = (inner ℂ x ((B - A) x) : ℂ).re := by
    rw [← Complex.sub_re, hval]
  rw [hre]
  calc |(inner ℂ x ((B - A) x) : ℂ).re| ≤ ‖x‖ * ‖(B - A) x‖ := le_trans h1 h2
    _ ≤ ‖x‖ * (‖B - A‖ * ‖x‖) := by
        exact mul_le_mul_of_nonneg_left h3 hx
    _ = ‖B - A‖ * ‖x‖ ^ (2 : ℕ) := by ring

/-- **Index stability.**  If `A` is uniformly positive off a `d`-dimensional subspace with gap `ε`,
then every operator within norm distance `ε` of `A` has negative Morse index at most `d`. -/
theorem negIndexAtMost_of_coerciveComplement
    {A B : H →L[ℂ] H} {ε : ℝ} {d : ℕ}
    (hA : HasCoerciveComplement A ε d) (hAB : ‖B - A‖ < ε) :
    NegIndexAtMost B d := by
  obtain ⟨hε, V, U, hUfin, hUd, hsup, hcoer⟩ := hA
  intro W _ hWneg
  have hdisj : ∀ x ∈ W, x ∈ V → x = 0 := by
    intro x hxW hxV
    by_contra hx0
    have h1 := hWneg x hxW hx0
    have h2 := hcoer x hxV
    have h3 := abs_re_inner_sub_le (A := A) (B := B) x
    have h4 : -(‖B - A‖ * ‖x‖ ^ (2 : ℕ))
        ≤ (inner ℂ x (B x) : ℂ).re - (inner ℂ x (A x) : ℂ).re := neg_le_of_abs_le h3
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hxsq : 0 < ‖x‖ ^ (2 : ℕ) := by positivity
    nlinarith [h1, h2, h4, hxsq, hAB]
  exact le_trans (finrank_le_of_trivial_meet_of_sup_eq_top hUfin hsup hdisj) hUd

/-! ## The obstruction -/

/-- **The continuous-Fredholm obstruction.**  A net of operators converging in norm to an operator
with a finite-dimensional negative and near-zero spectral part cannot eventually carry negative
Morse index exceeding that finite dimension.  Consequently a faithful index realization which is
norm-continuous in the carrier topology cannot exist on a class where the index jumps by an
arbitrary prescribed finite amount inside every compact-open neighbourhood. -/
theorem no_faithful_continuous_index_of_unbounded_witness
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {Aseq : ι → (H →L[ℂ] H)} {A₀ : H →L[ℂ] H} {ε : ℝ} {d : ℕ}
    (hA₀ : HasCoerciveComplement A₀ ε d)
    (hconv : Tendsto Aseq l (nhds A₀))
    (hwit : ∀ᶠ i in l, ∃ W : Submodule ℂ H, FiniteDimensional ℂ W ∧ d < Module.finrank ℂ W ∧
      ∀ x ∈ W, x ≠ 0 → (inner ℂ x (Aseq i x) : ℂ).re < 0) :
    False := by
  have hballmem : Metric.ball A₀ ε ∈ nhds A₀ := Metric.ball_mem_nhds _ hA₀.1
  have hnear : ∀ᶠ i in l, ‖Aseq i - A₀‖ < ε := by
    filter_upwards [hconv hballmem] with i hi
    simpa [dist_eq_norm] using hi
  obtain ⟨i, hi₁, hi₂⟩ := (hnear.and hwit).exists
  obtain ⟨W, hWfin, hWd, hWneg⟩ := hi₂
  have := negIndexAtMost_of_coerciveComplement hA₀ hi₁ W hWfin hWneg
  omega

end GaloisForLFunctions.HTGeometry
