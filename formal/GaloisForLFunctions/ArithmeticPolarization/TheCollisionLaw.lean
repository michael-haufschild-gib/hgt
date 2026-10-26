import GaloisForLFunctions.RHTower.CHMDArchimedeanBoundarySingularity
import GaloisForLFunctions.ArithmeticPolarization.TwistedSectorsCollideQuartets

/-!
# The collision law

Over `𝔽_q` the exterior square `Λ²H¹` has the eigenvalues `α_i α_j`; a conjugate pair `α, ᾱ`
collides into the real eigenvalue `|α|²`, and kernel counts on `Λ²H¹` see it (ACP
`unitary_of_exteriorDetDeg_nonneg`). Over `ℤ` the exterior divisor of a zero configuration is
`{ρ + ρ′ − ½}`.

* **Conjugate collision** (`extPoint_conj`, `extPoint_conj_re`): the conjugate pair `{ρ, ρ̄}`
  collides at the real point `2 Re ρ − ½`, of depth `2(Re ρ − ½)`: collision doubles depth and
  forgets the ordinate. The exterior divisor is reflection-equivariant (`extPoint_rosatiRefl`).
  RH is the statement that every collided point is `½` (`extPoint_conj_eq_half_iff`).
* **Ordinate-local collision is a twist** (`shift_collides_at_ordinate`): the archimedean twist at
  `γ` collides the conjugate quartet at ordinate `γ` onto the real axis without touching the depth;
  every other ordinate stays complex.
* **No analytic carrier for the global collision** (`eqOn_zero_of_vanishes_on_collision`,
  `zeta_global_collision_not_analytic`). All collided points of a zero configuration lie in the
  compact interval `[−½, 3/2]`; for a configuration with infinitely many points they either
  accumulate or pile up with unbounded multiplicity. So a function analytic on a connected
  neighbourhood of that interval which vanishes at every collided point, to at least the number of
  points colliding there, is identically zero. For `ζ` this holds unconditionally: the global
  collision of conjugate zeros has no meromorphic carrier, and a counting device for it must be
  non-meromorphic (two-variable, or a measure such as the depth distribution of the zeros).
-/

open Complex Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticPolarization

/-! ### 1. The exterior divisor and conjugate collision -/

/-- The **exterior point** `ρ + ρ′ − ½` of two spectral points: the logarithm of `α α′/√q^2`. -/
def extPoint (ρ ρ' : ℂ) : ℂ := ρ + ρ' - 1 / 2

/-- **Conjugate collision**: `ρ + ρ̄ − ½ = 2 Re ρ − ½` is real. -/
theorem extPoint_conj (ρ : ℂ) : extPoint ρ (conj ρ) = ((2 * ρ.re - 1 / 2 : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [extPoint]; ring

/-- Collision doubles depth: the collided point has depth `2(Re ρ − ½)`. -/
theorem extPoint_conj_re (ρ : ℂ) : (extPoint ρ (conj ρ)).re - 1 / 2 = 2 * (ρ.re - 1 / 2) := by
  rw [extPoint_conj, Complex.ofReal_re]; ring

/-- The exterior divisor is reflection-equivariant. -/
theorem extPoint_rosatiRefl (ρ ρ' : ℂ) :
    rosatiRefl (extPoint ρ ρ') = extPoint (rosatiRefl ρ) (rosatiRefl ρ') := by
  apply Complex.ext <;> simp [rosatiRefl, extPoint] <;> ring

/-- **RH as collision.** The collided point of `ρ` is `½` iff `ρ` is critical. -/
theorem extPoint_conj_eq_half_iff (ρ : ℂ) : extPoint ρ (conj ρ) = 1 / 2 ↔ ρ.re = 1 / 2 := by
  rw [extPoint_conj]
  constructor
  · intro h
    have := congrArg Complex.re h
    simp at this; linarith
  · intro h; rw [h]; push_cast; norm_num

/-- Collided points of the strip lie in `[−½, 3/2]`. -/
theorem collided_mem_Icc {ρ : ℂ} (h0 : 0 ≤ ρ.re) (h1 : ρ.re ≤ 1) :
    2 * ρ.re - 1 / 2 ∈ Icc (-(1 / 2) : ℝ) (3 / 2) :=
  ⟨by linarith, by linarith⟩

/-! ### 2. Ordinate-local collision is a twist -/

/-- **The twist collides one ordinate.** A point of `Z` at ordinate `γ` becomes real in `Z − iγ`
with the same depth, and a point at another ordinate stays non-real. -/
theorem shift_collides_at_ordinate (Z : Zeta23.ZeroConfig) {γ : ℝ} {ρ : ℂ} (hρ : ρ ∈ Z.carrier) :
    ρ - γ * I ∈ (shiftConfig Z γ).carrier ∧ (ρ - γ * I).re = ρ.re ∧
      ((ρ - γ * I).im = 0 ↔ ρ.im = γ) := by
  refine ⟨mem_shiftConfig Z hρ, by simp, ?_⟩
  simp [sub_eq_zero]

/-! ### 3. No analytic carrier for the global collision -/

/-- **The global collision has no analytic carrier.** Let `Z` have infinitely many points and let
`F` be analytic on a preconnected open set containing `[−½, 3/2]`. If `F` vanishes at every
collided point `c = 2 Re ρ − ½` to order at least the number of points of `Z` colliding at `c`,
then `F = 0` on `U`. -/
theorem eqOn_zero_of_vanishes_on_collision {Z : Zeta23.ZeroConfig} (hZ : Z.carrier.Infinite)
    {F : ℂ → ℂ} {U : Set ℂ} (hF : AnalyticOnNhd ℂ F U) (hU : IsPreconnected U)
    (hI : ∀ x : ℝ, x ∈ Icc (-(1 / 2) : ℝ) (3 / 2) → (x : ℂ) ∈ U)
    (hvan : ∀ (c : ℝ) (T : Finset ℂ), (∀ ρ ∈ T, ρ ∈ Z.carrier ∧ 2 * ρ.re - 1 / 2 = c) →
      (T.card : ℕ∞) ≤ analyticOrderAt F c) :
    EqOn F 0 U := by
  classical
  -- the collision map on the carrier
  set col : ℂ → ℝ := fun ρ => 2 * ρ.re - 1 / 2
  have hcolI : ∀ ρ ∈ Z.carrier, col ρ ∈ Icc (-(1 / 2) : ℝ) (3 / 2) := fun ρ hρ =>
    collided_mem_Icc (Z.strip ρ hρ).1 (Z.strip ρ hρ).2
  -- every collided point is a zero of `F`
  have hzero : ∀ ρ ∈ Z.carrier, F (col ρ) = 0 := by
    intro ρ hρ
    have h1 := hvan (col ρ) {ρ} (by intro x hx; rw [Finset.mem_singleton.mp hx]; exact ⟨hρ, rfl⟩)
    have hne : analyticOrderAt F (col ρ) ≠ 0 := by
      intro h0; rw [h0] at h1; simp at h1
    by_contra hF0
    exact hne ((hF _ (hI _ (hcolI ρ hρ))).analyticOrderAt_eq_zero.mpr hF0)
  by_cases hfin : (col '' Z.carrier).Finite
  · -- a fibre of the collision map is infinite: unbounded order at one point
    haveI : Infinite Z.carrier := hZ.to_subtype
    haveI : Finite (col '' Z.carrier) := hfin.to_subtype
    obtain ⟨⟨c, hc⟩, hfib⟩ := Finite.exists_infinite_fiber
      (fun ρ : Z.carrier => (⟨col ρ, ρ, ρ.2, rfl⟩ : col '' Z.carrier))
    have hfibset : {ρ : ℂ | ρ ∈ Z.carrier ∧ col ρ = c}.Infinite := by
      have hinf := Set.infinite_coe_iff.mp hfib
      have hsub : Subtype.val '' ((fun ρ : Z.carrier => (⟨col ρ, ρ, ρ.2, rfl⟩ :
          col '' Z.carrier)) ⁻¹' {⟨c, hc⟩}) ⊆ {ρ : ℂ | ρ ∈ Z.carrier ∧ col ρ = c} := by
        rintro _ ⟨ρ, hρ, rfl⟩
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.mk.injEq] at hρ
        exact ⟨ρ.2, hρ⟩
      exact (hinf.image Subtype.val_injective.injOn).mono hsub
    have htop : analyticOrderAt F (c : ℂ) = ⊤ := by
      refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
      obtain ⟨T, hT, hTc⟩ := hfibset.exists_subset_card_eq n
      have := hvan c T fun ρ hρ => hT hρ
      rw [hTc] at this
      exact this
    obtain ⟨ρ₀, hρ₀, rfl⟩ := hc
    exact hF.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU (hI _ (hcolI ρ₀ hρ₀))
      (analyticOrderAt_eq_top.mp htop)
  · -- infinitely many collided points accumulate in the compact interval
    have hinf : ((fun x : ℝ => (x : ℂ)) '' (col '' Z.carrier)).Infinite :=
      (Set.not_finite.mp hfin).image Complex.ofReal_injective.injOn
    have hK : IsCompact ((fun x : ℝ => (x : ℂ)) '' Icc (-(1 / 2) : ℝ) (3 / 2)) :=
      isCompact_Icc.image Complex.continuous_ofReal
    have hsub : (fun x : ℝ => (x : ℂ)) '' (col '' Z.carrier) ⊆
        (fun x : ℝ => (x : ℂ)) '' Icc (-(1 / 2) : ℝ) (3 / 2) := by
      rintro _ ⟨_, ⟨ρ, hρ, rfl⟩, rfl⟩
      exact ⟨col ρ, hcolI ρ hρ, rfl⟩
    obtain ⟨x, ⟨x', hx', rfl⟩, hacc⟩ := hinf.exists_accPt_of_subset_isCompact hK hsub
    refine hF.eqOn_zero_of_preconnected_of_frequently_eq_zero hU (hI x' hx') ?_
    rw [accPt_iff_frequently_nhdsNE] at hacc
    refine hacc.mono fun z hz => ?_
    obtain ⟨_, ⟨ρ, hρ, rfl⟩, rfl⟩ := hz
    exact hzero ρ hρ

/-- **For `ζ` the global collision of conjugate zeros has no analytic carrier** on any connected
neighbourhood of `[−½, 3/2]`: `ζ` has infinitely many nontrivial zeros. -/
theorem zeta_global_collision_not_analytic {F : ℂ → ℂ} {U : Set ℂ} (hF : AnalyticOnNhd ℂ F U)
    (hU : IsPreconnected U) (hI : ∀ x : ℝ, x ∈ Icc (-(1 / 2) : ℝ) (3 / 2) → (x : ℂ) ∈ U)
    (hvan : ∀ (c : ℝ) (T : Finset ℂ),
      (∀ ρ ∈ T, ρ ∈ Zeta23.zetaZeroConfig.carrier ∧ 2 * ρ.re - 1 / 2 = c) →
      (T.card : ℕ∞) ≤ analyticOrderAt F c) :
    EqOn F 0 U :=
  eqOn_zero_of_vanishes_on_collision RHTower.CHMDLightCone.zetaZeroConfig_carrier_infinite hF hU
    hI hvan

end GaloisForLFunctions.ArithmeticPolarization
