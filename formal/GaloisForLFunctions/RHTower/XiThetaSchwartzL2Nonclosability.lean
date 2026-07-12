import GaloisForLFunctions.RHTower.CyclicNullFormNonclosability
import GaloisForLFunctions.RHTower.XiThetaSchwartzL2ExtensionObstruction

/-!
# The Hedenmalm theta metric is nonclosable in ordinary `L²`

The actual normalized theta source is cyclic for ordinary real translations
in `L²(R)`.  Momentum symmetry and theta nullity put its complete Schwartz
translation orbit in the radical of every candidate nonnegative form.  The
abstract cyclic-null theorem then constructs an `L²`-null sequence with fixed
positive form energy, proving forced nonclosability.
-/

open Complex Function Filter Set MeasureTheory
open scoped Topology SchwartzMap

namespace RHTower

noncomputable section

/-- The complex-linear inclusion of Schwartz space into ordinary `L²(R)`. -/
def xiThetaSchwartzToL2 : 𝓢(ℝ, ℂ) →ₗ[ℂ] XiThetaL2 :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure ℝ)).toLinearMap

/-- The actual normalized theta source translated inside Schwartz space. -/
def xiThetaSchwartzTranslationOrbit (a : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.translateCLM ℂ a xiThetaSchwartzSource

/-- The Schwartz orbit maps exactly to the already constructed ordinary-`L²` orbit. -/
theorem xiThetaSchwartzToL2_translationOrbit (a : ℝ) :
    xiThetaSchwartzToL2 (xiThetaSchwartzTranslationOrbit a) =
      xiThetaTranslationOrbit a := by
  rw [xiThetaSchwartzTranslationOrbit, xiThetaTranslationOrbit,
    xiThetaSourceL2, MellinL2.additiveTranslation_toLp,
    mellinL2_schwartzTranslate_eq_translateCLM]
  rfl

/-- The actual translated theta source remains in the left radical of every
momentum-symmetric theta-null Schwartz form. -/
theorem xiThetaSchwartzTranslationOrbit_mem_leftRadical
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hMomentum : Q.MomentumSymmetric)
    (hThetaNull : ∀ w : 𝓢(ℝ, ℂ), Q xiThetaSchwartzSource w = 0)
    (a : ℝ) :
    xiThetaSchwartzTranslationOrbit a ∈ Q.leftRadical := by
  rw [Q.mem_leftRadical_iff]
  intro w
  let w₀ : 𝓢(ℝ, ℂ) := SchwartzMap.translateCLM ℂ (-a) w
  have hw : SchwartzMap.translateCLM ℂ a w₀ = w := by
    simp [w₀]
  rw [← hw, xiThetaSchwartzTranslationOrbit,
    Q.translate_pair_invariant hMomentum]
  exact hThetaNull w₀

/-- The ordinary-`L²` image of the Schwartz radical. -/
def xiThetaL2RadicalImage
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm) :
    Submodule ℂ XiThetaL2 :=
  Submodule.map xiThetaSchwartzToL2 Q.leftRadical

/-- Momentum symmetry and theta nullity force the ordinary-`L²` radical image to be dense. -/
theorem dense_xiThetaL2RadicalImage
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hMomentum : Q.MomentumSymmetric)
    (hThetaNull : ∀ w : 𝓢(ℝ, ℂ), Q xiThetaSchwartzSource w = 0) :
    Dense (xiThetaL2RadicalImage Q : Set XiThetaL2) := by
  have hcyclic : IsCyclicFamily (𝕜 := ℂ)
      (fun a ↦ xiThetaSchwartzToL2 (xiThetaSchwartzTranslationOrbit a)) := by
    simpa only [xiThetaSchwartzToL2_translationOrbit] using
      isCyclicFamily_xiThetaTranslationOrbit
  have horbit (a : ℝ) :
      xiThetaSchwartzToL2 (xiThetaSchwartzTranslationOrbit a) ∈
        xiThetaL2RadicalImage Q := by
    exact ⟨xiThetaSchwartzTranslationOrbit a,
      xiThetaSchwartzTranslationOrbit_mem_leftRadical
        Q hMomentum hThetaNull a, rfl⟩
  have hspan : Submodule.span ℂ
      (Set.range fun a ↦ xiThetaSchwartzToL2 (xiThetaSchwartzTranslationOrbit a)) ≤
        xiThetaL2RadicalImage Q := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact horbit a
  exact hcyclic.mono hspan

/-- Every Schwartz vector is arbitrarily close in ordinary `L²` to the radical of a
momentum-symmetric theta-null form.  Equivalently, the quotient seminorm induced by ordinary
`L²` vanishes on every source coset. -/
theorem exists_leftRadical_l2_approx
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hMomentum : Q.MomentumSymmetric)
    (hThetaNull : ∀ w : SchwartzMap ℝ ℂ, Q xiThetaSchwartzSource w = 0)
    (u : SchwartzMap ℝ ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : SchwartzMap ℝ ℂ, r ∈ Q.leftRadical ∧
      ‖xiThetaSchwartzToL2 (u - r)‖ < ε := by
  have hmem : xiThetaSchwartzToL2 u ∈
      closure (xiThetaL2RadicalImage Q : Set XiThetaL2) := by
    rw [(dense_xiThetaL2RadicalImage Q hMomentum hThetaNull).closure_eq]
    exact Set.mem_univ _
  obtain ⟨b, hb, hub⟩ := (Metric.mem_closure_iff.mp hmem) ε hε
  obtain ⟨r, hr, rfl⟩ := hb
  refine ⟨r, hr, ?_⟩
  rw [map_sub, ← dist_eq_norm]
  exact hub

/-- A nonzero form has a proper ordinary-`L²` radical image. -/
theorem xiThetaL2RadicalImage_ne_top
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hNonzero : ∃ u v : 𝓢(ℝ, ℂ), Q u v ≠ 0) :
    xiThetaL2RadicalImage Q ≠ ⊤ := by
  intro htop
  obtain ⟨u, v, huv⟩ := hNonzero
  have hju : xiThetaSchwartzToL2 u ∈ xiThetaL2RadicalImage Q := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨r, hr, hjr⟩ := hju
  have hur : u = r := by
    apply SchwartzMap.injective_toLp (F := ℂ) 2 (volume : Measure ℝ)
    change u.toLp 2 volume = r.toLp 2 volume
    exact hjr.symm
  exact huv (by rw [hur]; exact hr v)

/-- The ordinary-`L²` radical image of every nonzero momentum-symmetric theta-null form is dense,
proper, and therefore nonclosed. -/
theorem not_isClosed_xiThetaL2RadicalImage
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hMomentum : Q.MomentumSymmetric)
    (hThetaNull : ∀ w : 𝓢(ℝ, ℂ), Q xiThetaSchwartzSource w = 0)
    (hNonzero : ∃ u v : 𝓢(ℝ, ℂ), Q u v ≠ 0) :
    ¬ IsClosed (xiThetaL2RadicalImage Q : Set XiThetaL2) := by
  intro hclosed
  have hdense := dense_xiThetaL2RadicalImage Q hMomentum hThetaNull
  have hset : (xiThetaL2RadicalImage Q : Set XiThetaL2) = Set.univ := by
    rw [← hclosed.closure_eq]
    exact hdense.closure_eq
  have htop : xiThetaL2RadicalImage Q = ⊤ := by
    ext x
    change x ∈ (xiThetaL2RadicalImage Q : Set XiThetaL2) ↔ True
    rw [hset]
    simp
  exact xiThetaL2RadicalImage_ne_top Q hNonzero htop

/-- **Hedenmalm singular sequence.** Around every Schwartz vector, a nonnegative
momentum-symmetric theta-null form has an ordinary-`L²` null sequence with
constant form energy and pairwise zero difference energy. -/
theorem exists_xiThetaL2Null_constantEnergy_sequence
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hNonnegative : Q.IsNonnegative)
    (hMomentum : Q.MomentumSymmetric)
    (hThetaNull : ∀ w : 𝓢(ℝ, ℂ), Q xiThetaSchwartzSource w = 0)
    (u : 𝓢(ℝ, ℂ)) :
    ∃ z : ℕ → 𝓢(ℝ, ℂ),
      Tendsto (fun n ↦ xiThetaSchwartzToL2 (z n)) atTop (nhds 0) ∧
      (∀ m n, Q (z m - z n) (z m - z n) = 0) ∧
      (∀ n, Q (z n) (z n) = Q u u) := by
  have hcyclic : IsCyclicFamily (𝕜 := ℂ)
      (fun a ↦ xiThetaSchwartzToL2 (xiThetaSchwartzTranslationOrbit a)) := by
    simpa only [xiThetaSchwartzToL2_translationOrbit] using
      isCyclicFamily_xiThetaTranslationOrbit
  have hHermitian : Q.IsHermitian := Q.isHermitian_of_isNonnegative hNonnegative
  have hnullOrbit : ∀ a w, Q (xiThetaSchwartzTranslationOrbit a) w = 0 := by
    intro a w
    exact (xiThetaSchwartzTranslationOrbit_mem_leftRadical
      Q hMomentum hThetaNull a) w
  exact Q.exists_ambientNull_constantEnergy_sequence_of_cyclic_null
    xiThetaSchwartzToL2 xiThetaSchwartzTranslationOrbit
    hcyclic hHermitian hnullOrbit u

/-- **Forced nonclosability for the actual Hedenmalm theta source.** Every
nonnegative momentum-symmetric theta-null Schwartz form with a nonzero diagonal
fails sequential closability through ordinary `L²(R)`. -/
theorem not_xiThetaSchwartzForm_sequentiallyL2Closable
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hNonnegative : Q.IsNonnegative)
    (hMomentum : Q.MomentumSymmetric)
    (hThetaNull : ∀ w : 𝓢(ℝ, ℂ), Q xiThetaSchwartzSource w = 0)
    {u : 𝓢(ℝ, ℂ)} (hu : Q u u ≠ 0) :
    ¬ Q.IsSequentiallyClosableThrough xiThetaSchwartzToL2 := by
  have hcyclic : IsCyclicFamily (𝕜 := ℂ)
      (fun a ↦ xiThetaSchwartzToL2 (xiThetaSchwartzTranslationOrbit a)) := by
    simpa only [xiThetaSchwartzToL2_translationOrbit] using
      isCyclicFamily_xiThetaTranslationOrbit
  have hHermitian : Q.IsHermitian := Q.isHermitian_of_isNonnegative hNonnegative
  have hnullOrbit : ∀ a w, Q (xiThetaSchwartzTranslationOrbit a) w = 0 := by
    intro a w
    exact (xiThetaSchwartzTranslationOrbit_mem_leftRadical
      Q hMomentum hThetaNull a) w
  exact Q.not_isSequentiallyClosableThrough_of_cyclic_null
    xiThetaSchwartzToL2 xiThetaSchwartzTranslationOrbit
    hcyclic hHermitian hnullOrbit hu

/-- There is no nonzero nonnegative Hedenmalm source form which is sequentially
closable through ordinary `L²(R)`. -/
theorem not_exists_nonzero_nonnegative_xiThetaSchwartzForm_sequentiallyL2Closable :
    ¬ ∃ Q : SchwartzMap.ContinuousSchwartzSesquilinearForm,
      Q.IsNonnegative ∧
      Q.MomentumSymmetric ∧
      (∀ w : 𝓢(ℝ, ℂ), Q xiThetaSchwartzSource w = 0) ∧
      Q.IsSequentiallyClosableThrough xiThetaSchwartzToL2 ∧
      ∃ u v : 𝓢(ℝ, ℂ), Q u v ≠ 0 := by
  rintro ⟨Q, hNonnegative, hMomentum, hThetaNull, hClosable, hNonzero⟩
  obtain ⟨u, hu⟩ := Q.exists_diagonal_ne_zero_of_exists_apply_ne_zero hNonzero
  exact (not_xiThetaSchwartzForm_sequentiallyL2Closable
    Q hNonnegative hMomentum hThetaNull hu) hClosable

/-- **Exact ordinary-`L²` closure classification.** Inside the nonnegative,
momentum-symmetric, theta-null cone, sequential closability through ordinary
`L²(R)` is equivalent to the form vanishing identically. -/
theorem xiThetaSchwartzForm_sequentiallyL2Closable_iff_zero
    (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm)
    (hNonnegative : Q.IsNonnegative)
    (hMomentum : Q.MomentumSymmetric)
    (hThetaNull : ∀ w : SchwartzMap ℝ ℂ, Q xiThetaSchwartzSource w = 0) :
    Q.IsSequentiallyClosableThrough xiThetaSchwartzToL2 ↔
      ∀ u v : SchwartzMap ℝ ℂ, Q u v = 0 := by
  constructor
  · intro hClosable u v
    by_contra huv
    obtain ⟨w, hw⟩ := Q.exists_diagonal_ne_zero_of_exists_apply_ne_zero
      ⟨u, v, huv⟩
    exact (not_xiThetaSchwartzForm_sequentiallyL2Closable
      Q hNonnegative hMomentum hThetaNull hw) hClosable
  · intro hZero u _hu0 _huCauchy
    have hdiag : (fun n ↦ Q (u n) (u n)) = fun _n : ℕ ↦ 0 := by
      funext n
      exact hZero (u n) (u n)
    rw [hdiag]
    exact tendsto_const_nhds

end

end RHTower
