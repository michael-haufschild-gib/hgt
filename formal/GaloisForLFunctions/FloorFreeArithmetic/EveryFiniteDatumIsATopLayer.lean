import GaloisForLFunctions.FloorFreeArithmetic.NonAttainmentIsALawOfConfigurations
import GaloisForLFunctions.FloorFreeArithmetic.TheFloorOfAMechanism

/-!
# Every finite datum is a top layer

A tangent datum is a depth `0 < b ≤ ½`, a finite set `Γ` of positive ordinates and a
multiplicity for each ordinate. The four-fold orbit `½ ± b ± iγ`, `γ ∈ Γ`, with these
multiplicities is a zero configuration: it is finite, hence tempered, symmetric under the
reflection `ρ ↦ 1 − ρ̄` and under conjugation, and has no real zero. Its top layer at the depth
`b` is exactly the datum.

* `layerConfig`: the configuration of a datum.
* `mem_positiveTopSupport_layerConfig`: its positive top support is `{b + iγ : γ ∈ Γ}`.
* `exists_config_with_top_layer`: the realization theorem.
* `hasModelAt_of_forall_tempered_symmetric`: a mechanism that holds on every tempered
  configuration symmetric under conjugation and without real zeros has a model at every depth
  of the strip.

So what holds for every such configuration — every identity of the explicit formula — imposes no
condition on the tangent datum: none on the depth, on the number of ordinates, on their
positions or on the multiplicities.
-/

open Complex Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.FloorFreeArithmetic

open SquareRootThreshold Zeta23 SurfaceOfSpecZ SurfaceOfSpecZ.ScaleLocality
open ZeroConfigurationGeometry ZeroConfigurationGeometry.ConfigAbscissa

/-- The carrier of a datum: the points `½ ± b ± iγ`, `γ ∈ Γ`. -/
def layerCarrier (b : ℝ) (Γ : Finset ℝ) : Set ℂ := {ρ | |ρ.re - 1 / 2| = b ∧ |ρ.im| ∈ Γ}

theorem finite_layerCarrier (b : ℝ) (Γ : Finset ℝ) : (layerCarrier b Γ).Finite := by
  classical
  refine ((({1 / 2 + b, 1 / 2 - b} : Finset ℝ) ×ˢ (Γ ∪ Γ.image fun γ => -γ)).finite_toSet.image
    fun p : ℝ × ℝ => (⟨p.1, p.2⟩ : ℂ)).subset ?_
  rintro ρ ⟨hre, him⟩
  refine ⟨(ρ.re, ρ.im), ?_, Complex.eta ρ⟩
  rw [Finset.mem_coe, Finset.mem_product]
  constructor
  · rcases eq_or_eq_neg_of_abs_eq hre with h | h
    · exact Finset.mem_insert.mpr (Or.inl (by linarith only [h]))
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (by linarith only [h])))
  · rcases abs_choice ρ.im with h | h
    · rw [h] at him
      exact Finset.mem_union_left _ him
    · rw [h] at him
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨-ρ.im, him, neg_neg _⟩)

/-- The configuration of a datum: the points `½ ± b ± iγ`, `γ ∈ Γ`, with the multiplicity
`m γ` at the ordinates `±γ`. -/
def layerConfig {b : ℝ} (hb' : b ≤ 1 / 2) (Γ : Finset ℝ) (m : ℝ → ℕ) (hm : ∀ γ, 1 ≤ m γ) :
    ZeroConfig where
  carrier := layerCarrier b Γ
  mult := fun ρ => m |ρ.im|
  one_le_mult := fun _ _ => hm _
  strip := by
    rintro ρ ⟨hre, -⟩
    have h := abs_le.mp (hre.le.trans hb')
    constructor <;> linarith only [h.1, h.2]
  reflect_mem := by
    rintro ρ ⟨hre, him⟩
    have h1 : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
    have h2 : (reflect ρ).im = ρ.im := by simp [reflect]
    refine ⟨?_, by rw [h2]; exact him⟩
    rw [h1, ← hre, ← abs_neg (ρ.re - 1 / 2)]
    congr 1
    ring
  mult_reflect := by
    intro ρ _
    have h2 : (reflect ρ).im = ρ.im := by simp [reflect]
    show m |(reflect ρ).im| = m |ρ.im|
    rw [h2]
  finite_window := fun _ _ => (finite_layerCarrier b Γ).subset fun _ h => h.1

section Layer

variable {b : ℝ} (hb' : b ≤ 1 / 2) (Γ : Finset ℝ) (m : ℝ → ℕ) (hm : ∀ γ, 1 ≤ m γ)

theorem temperedConfig_layerConfig : TemperedConfig (layerConfig hb' Γ m hm) := by
  haveI : Finite (layerConfig hb' Γ m hm).carrier := (finite_layerCarrier b Γ).to_subtype
  unfold TemperedConfig
  exact Summable.of_finite

theorem conj_mem_layerConfig :
    ∀ ρ ∈ (layerConfig hb' Γ m hm).carrier, conj ρ ∈ (layerConfig hb' Γ m hm).carrier := by
  rintro ρ ⟨hre, him⟩
  refine ⟨?_, ?_⟩
  · rw [Complex.conj_re]
    exact hre
  · rw [Complex.conj_im, abs_neg]
    exact him

theorem im_ne_zero_of_mem_layerConfig (hΓ : ∀ γ ∈ Γ, 0 < γ) :
    ∀ ρ ∈ (layerConfig hb' Γ m hm).carrier, ρ.im ≠ 0 := by
  rintro ρ ⟨-, him⟩ h0
  have hpos := hΓ _ him
  rw [h0, abs_zero] at hpos
  exact lt_irrefl _ hpos

/-- The points of the datum belong to its configuration. -/
theorem mk_mem_layerConfig (hb : 0 < b) (hΓ : ∀ γ ∈ Γ, 0 < γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    (⟨1 / 2 + b, γ⟩ : ℂ) ∈ (layerConfig hb' Γ m hm).carrier := by
  refine ⟨?_, ?_⟩
  · show |1 / 2 + b - 1 / 2| = b
    rw [add_sub_cancel_left, abs_of_pos hb]
  · show |γ| ∈ Γ
    rw [abs_of_pos (hΓ γ hγ)]
    exact hγ

/-- The multiplicities of the datum are those of its configuration. -/
theorem mult_layerConfig (hΓ : ∀ γ ∈ Γ, 0 < γ) {γ : ℝ} (hγ : γ ∈ Γ) :
    (layerConfig hb' Γ m hm).mult ⟨1 / 2 + b, γ⟩ = m γ := by
  show m |γ| = m γ
  rw [abs_of_pos (hΓ γ hγ)]

/-- No exponent of the configuration lies beyond the depth of the datum. -/
theorem topDepth_layerConfig : TopDepth (layerConfig hb' Γ m hm) b := by
  intro z hz
  obtain ⟨hre, -⟩ := add_half_mem_of_evenCoeff_ne_zero (conj_mem_layerConfig hb' Γ m hm) hz
  have he : ((1 / 2 : ℂ) + z).re = 1 / 2 + z.re := by norm_num
  rw [he] at hre
  have h := le_abs_self (1 / 2 + z.re - 1 / 2)
  linarith only [h, hre]

/-- **The top layer of the configuration is the datum.** -/
theorem mem_positiveTopSupport_layerConfig (hb : 0 < b) (hΓ : ∀ γ ∈ Γ, 0 < γ) (z : ℂ) :
    z ∈ positiveTopSupport (layerConfig hb' Γ m hm) b ↔ ∃ γ ∈ Γ, z = ⟨b, γ⟩ := by
  constructor
  · rintro ⟨hre, him, hz⟩
    obtain ⟨-, hmem⟩ := add_half_mem_of_evenCoeff_ne_zero (conj_mem_layerConfig hb' Γ m hm) hz
    have he : ((1 / 2 : ℂ) + z).im = z.im := by norm_num
    rw [he, abs_of_pos him] at hmem
    exact ⟨z.im, hmem, Complex.ext hre rfl⟩
  · rintro ⟨γ, hγ, rfl⟩
    have hsee := evenCoeff_spline_sees_config (mk_mem_layerConfig hb' Γ m hm hb hΓ hγ)
      (show (1 : ℝ) / 2 < 1 / 2 + b by linarith only [hb])
    have hz : (⟨1 / 2 + b, γ⟩ : ℂ) - 1 / 2 = ⟨b, γ⟩ := by apply Complex.ext <;> simp
    rw [hz] at hsee
    exact ⟨rfl, hΓ γ hγ, hsee⟩

/-- A nonempty datum violates the abscissa law. -/
theorem not_abscissaLaw_layerConfig (hb : 0 < b) (hΓ : ∀ γ ∈ Γ, 0 < γ) (hne : Γ.Nonempty) :
    ¬ AbscissaLaw (layerConfig hb' Γ m hm) := by
  intro hlaw
  obtain ⟨γ, hγ⟩ := hne
  have hle := hlaw 0 le_rfl ((finite_layerCarrier b Γ).subset fun _ h => h.1) _
    (mk_mem_layerConfig hb' Γ m hm hb hΓ hγ)
  have hre : (⟨1 / 2 + b, γ⟩ : ℂ).re = 1 / 2 + b := rfl
  rw [hre] at hle
  linarith only [hle, hb]

end Layer

/-- **Every finite datum is a top layer.** For a depth `0 < b ≤ ½`, a finite set `Γ` of positive
ordinates and multiplicities `m`, there is a finite zero configuration, symmetric under
conjugation and without real zeros, whose exponents have depth at most `b`, whose positive top
support is `{b + iγ : γ ∈ Γ}`, and whose multiplicities at these points are `m γ`. -/
theorem exists_config_with_top_layer {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) (Γ : Finset ℝ)
    (hΓ : ∀ γ ∈ Γ, 0 < γ) (m : ℝ → ℕ) (hm : ∀ γ, 1 ≤ m γ) :
    ∃ Z : ZeroConfig, TemperedConfig Z ∧ Z.carrier.Finite ∧
      (∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier) ∧ (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) ∧ TopDepth Z b ∧
      (∀ z, z ∈ positiveTopSupport Z b ↔ ∃ γ ∈ Γ, z = ⟨b, γ⟩) ∧
      ∀ γ ∈ Γ, Z.mult ⟨1 / 2 + b, γ⟩ = m γ :=
  ⟨layerConfig hb' Γ m hm, temperedConfig_layerConfig hb' Γ m hm, finite_layerCarrier b Γ,
    conj_mem_layerConfig hb' Γ m hm, im_ne_zero_of_mem_layerConfig hb' Γ m hm hΓ,
    topDepth_layerConfig hb' Γ m hm, mem_positiveTopSupport_layerConfig hb' Γ m hm hb hΓ,
    fun _ hγ => mult_layerConfig hb' Γ m hm hΓ hγ⟩

/-- **Identities of the explicit formula have models at every depth.** A mechanism that holds
on every tempered configuration symmetric under conjugation and without real zeros has a model
at every depth `0 < b ≤ ½`, and it does not give the abscissa law. -/
theorem hasModelAt_of_forall_tempered_symmetric {M : Mechanism}
    (hM : ∀ Z : ZeroConfig, TemperedConfig Z → (∀ ρ ∈ Z.carrier, conj ρ ∈ Z.carrier) →
      (∀ ρ ∈ Z.carrier, ρ.im ≠ 0) → M Z) {b : ℝ} (hb : 0 < b) (hb' : b ≤ 1 / 2) :
    HasModelAt M b ∧ ¬ ∀ Z, M Z → AbscissaLaw Z := by
  have hΓ : ∀ γ ∈ ({1} : Finset ℝ), 0 < γ := fun γ hγ => by
    rw [Finset.mem_singleton.mp hγ]
    exact one_pos
  have hm : ∀ γ : ℝ, 1 ≤ (fun _ : ℝ => 1) γ := fun _ => le_rfl
  have hMZ : M (layerConfig hb' {1} (fun _ => 1) hm) :=
    hM _ (temperedConfig_layerConfig hb' _ _ hm) (conj_mem_layerConfig hb' _ _ hm)
      (im_ne_zero_of_mem_layerConfig hb' _ _ hm hΓ)
  refine ⟨⟨_, hMZ, _, mk_mem_layerConfig hb' _ _ hm hb hΓ (Finset.mem_singleton_self 1), rfl⟩,
    fun hall => ?_⟩
  exact not_abscissaLaw_layerConfig hb' _ _ hm hb hΓ (Finset.singleton_nonempty 1) (hall _ hMZ)

end GaloisForLFunctions.FloorFreeArithmetic
