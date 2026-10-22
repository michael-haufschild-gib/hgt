import GaloisForLFunctions.RHTower.Deninger.DeningerProLogCuspHodge
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Analysis.Normed.Module.Basic

/-!
# The affine/prime overlap of oriented conformal leaves

Characters of a finite group take values in the roots of unity, so on the residue-character locus
every tangential coordinate has modulus one and its logarithm vanishes.  A net of generic points
approaching such a character therefore has logarithmic modulus vector with normal part tending to
infinity and tangential part tending to zero, and its normalized modulus direction converges to the
positive normal direction.

The tautological affine plane spanned by a modulus vector and its phase depends only on the
positive projective class of that vector, and its normalized oriented frame varies continuously, so
the affine planes converge to the normal complex line.  Along the normal ray the affine metric and
the cusp metric differ by a positive conformal factor, and the degree-one Hodge star of a conformal
metric in real dimension two is conformal-factor free, so the two stars agree on the overlap.

* `deningerFiniteCharacter_norm_eq_one` : tangential unitarity.
* `deningerModulusDirection_tendsto` : the normalized direction converges to the normal `(4)`.
* `deningerAffinePlane_smul_pos`, `deningerAffineFrame_tendsto` : the planes converge `(5)`--`(7)`.
* `deningerAffineCusp_conformal`, `deningerAffineCusp_star_agree` : the metrics `(8)`--`(9)` are
  conformal and the stars agree.
-/

namespace RHTower

open Filter Topology

section TangentialUnitarity

/-- **Tangential unitarity.**  Every value of a character of a finite group is a root of unity, so
it has modulus one; the residue-character locus has unitary tangential coordinates. -/
theorem deningerFiniteCharacter_norm_eq_one {G : Type*} [Group G] [Fintype G] (chi : G →* ℂˣ)
    (g : G) : ‖((chi g : ℂˣ) : ℂ)‖ = 1 := by
  have hcard : 0 < Fintype.card G := Fintype.card_pos
  have hg : g ^ Fintype.card G = 1 := pow_card_eq_one
  have hchi : ((chi g : ℂˣ) : ℂ) ^ Fintype.card G = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hg, map_one, Units.val_one]
  have hnorm : ‖((chi g : ℂˣ) : ℂ)‖ ^ Fintype.card G = 1 := by
    rw [← norm_pow, hchi, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hcard.ne').mp hnorm

/-- The logarithm of a unitary tangential coordinate vanishes. -/
theorem deningerFiniteCharacter_log_eq_zero {G : Type*} [Group G] [Fintype G] (chi : G →* ℂˣ)
    (g : G) : Real.log ‖((chi g : ℂˣ) : ℂ)‖ = 0 := by
  rw [deningerFiniteCharacter_norm_eq_one, Real.log_one]

end TangentialUnitarity

section ModulusDirection

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **`(4)`: the normalized logarithmic modulus direction converges to the normal direction.**  On
a net approaching the residue-character locus the normal coordinate diverges and the tangential
coordinates vanish, so the normalized modulus vector tends to the positive normal generator. -/
theorem deningerModulusDirection_tendsto {L : ℕ → ℝ} {t : ℕ → F}
    (hL : Tendsto L atTop atTop) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun k => (‖((L k, t k) : ℝ × F)‖)⁻¹ • ((L k, t k) : ℝ × F)) atTop
      (𝓝 ((1 : ℝ), (0 : F))) := by
  have hL1 : ∀ᶠ k in atTop, 1 ≤ L k := hL.eventually_ge_atTop 1
  have htnorm : Tendsto (fun k => ‖t k‖) atTop (𝓝 0) := by
    simpa using ht.norm
  have htle : ∀ᶠ k in atTop, ‖t k‖ ≤ 1 := by
    filter_upwards [htnorm.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k hk
    exact le_of_lt hk
  have hnorm : ∀ᶠ k in atTop, ‖((L k, t k) : ℝ × F)‖ = L k := by
    filter_upwards [hL1, htle] with k hk hkt
    rw [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    exact max_eq_left (by linarith)
  have hsub : Tendsto (fun k => (L k)⁻¹ • t k) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ htnorm
    filter_upwards [hL1] with k hk
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    have hLpos : 0 < L k := by linarith
    have : (L k)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      exact Or.inr hk
    calc (L k)⁻¹ * ‖t k‖ ≤ 1 * ‖t k‖ := by
          exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = ‖t k‖ := one_mul _
  refine Tendsto.congr' (f₁ := fun k => ((1 : ℝ), (L k)⁻¹ • t k)) ?_ ?_
  · filter_upwards [hL1, hnorm] with k hk hkn
    have hLne : L k ≠ 0 := by
      intro hcon
      rw [hcon] at hk
      linarith
    rw [hkn]
    refine Prod.ext ?_ rfl
    show (1 : ℝ) = (L k)⁻¹ * L k
    exact (inv_mul_cancel₀ hLne).symm
  · exact Filter.Tendsto.prodMk_nhds tendsto_const_nhds hsub

end ModulusDirection

section AffinePlane

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The tautological affine plane `(5)` of a logarithmic modulus vector: the real span of the
modulus direction and its matching phase direction. -/
def deningerAffinePlane (m : F) : Submodule ℝ (F × F) :=
  Submodule.span ℝ {((m, 0) : F × F), ((0, m) : F × F)}

/-- **The plane depends only on the positive projective class.**  In particular the positive
rational power maps, which scale the whole modulus vector, do not move it. -/
theorem deningerAffinePlane_smul_pos {c : ℝ} (hc : c ≠ 0) (m : F) :
    deningerAffinePlane (c • m) = deningerAffinePlane m := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro x (rfl | rfl)
    · have : ((c • m, 0) : F × F) = c • ((m, 0) : F × F) := by
        refine Prod.ext rfl ?_
        show (0 : F) = c • (0 : F)
        rw [smul_zero]
      rw [this]
      exact Submodule.smul_mem _ c (Submodule.subset_span (by left; rfl))
    · have : ((0, c • m) : F × F) = c • ((0, m) : F × F) := by
        refine Prod.ext ?_ rfl
        show (0 : F) = c • (0 : F)
        rw [smul_zero]
      rw [this]
      exact Submodule.smul_mem _ c (Submodule.subset_span (by right; rfl))
  · refine Submodule.span_le.mpr ?_
    rintro x (rfl | rfl)
    · have : ((m, 0) : F × F) = c⁻¹ • ((c • m, 0) : F × F) := by
        refine Prod.ext ?_ ?_
        · show m = c⁻¹ • (c • m)
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        · show (0 : F) = c⁻¹ • (0 : F)
          rw [smul_zero]
      rw [this]
      exact Submodule.smul_mem _ c⁻¹ (Submodule.subset_span (by left; rfl))
    · have : ((0, m) : F × F) = c⁻¹ • ((0, c • m) : F × F) := by
        refine Prod.ext ?_ ?_
        · show (0 : F) = c⁻¹ • (0 : F)
          rw [smul_zero]
        · show m = c⁻¹ • (c • m)
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [this]
      exact Submodule.smul_mem _ c⁻¹ (Submodule.subset_span (by right; rfl))

end AffinePlane

section AffineComplexStructure

variable {F : Type*} [AddCommGroup F]

/-- The complex structure `(6)` of the affine plane: the quarter turn exchanging modulus and
phase. -/
def deningerAffineJ (x : F × F) : F × F := (-x.2, x.1)

theorem deningerAffineJ_modulus (m : F) : deningerAffineJ ((m, 0) : F × F) = (0, m) := by
  refine Prod.ext ?_ rfl
  show -(0 : F) = 0
  rw [neg_zero]

theorem deningerAffineJ_phase (m : F) : deningerAffineJ ((0, m) : F × F) = (-m, 0) := rfl

/-- **The affine complex structure squares to `-1`.** -/
theorem deningerAffineJ_sq (x : F × F) : deningerAffineJ (deningerAffineJ x) = -x := by
  refine Prod.ext ?_ ?_
  · show -x.1 = -x.1
    rfl
  · show -x.2 = -x.2
    rfl

end AffineComplexStructure

section AffineFrame

variable {F : Type*} [NormedAddCommGroup F]

/-- **`(7)`: the oriented frames converge.**  The normalized frame of the affine plane is
continuous in the modulus direction, so along a net approaching the residue-character locus the
affine planes converge to the normal complex line. -/
theorem deningerAffineFrame_tendsto {n : ℕ → F} {e : F} (hn : Tendsto n atTop (𝓝 e)) :
    Tendsto (fun k => (((n k, 0) : F × F), ((0, n k) : F × F))) atTop
      (𝓝 (((e, 0) : F × F), ((0, e) : F × F))) := by
  refine Filter.Tendsto.prodMk_nhds ?_ ?_
  · exact Filter.Tendsto.prodMk_nhds hn tendsto_const_nhds
  · exact Filter.Tendsto.prodMk_nhds tendsto_const_nhds hn

end AffineFrame

section ConformalOverlap

/-- **`(8)`--`(9)`: the affine and cusp metrics are conformal.**  Along the normal ray the affine
radial coordinate is a positive multiple of the log-radius and the phase coordinate is the same
multiple of the angle, so the two metrics differ by that positive factor. -/
theorem deningerAffineCusp_conformal {c u L : ℝ} (hc : 0 < c) (hL : 0 < L) (v w : ℝ × ℝ) :
    deningerCuspMetric u (c * L) (c • v) (c • w) = c * deningerCuspMetric u L v w := by
  have hc' : c ≠ 0 := ne_of_gt hc
  have hL' : L ≠ 0 := ne_of_gt hL
  show u / (c * L) * ((c * v.1) * (c * w.1) + (c * v.2) * (c * w.2))
      = c * (u / L * (v.1 * w.1 + v.2 * w.2))
  field_simp

/-- **The stars agree on the overlap.**  The degree-one Hodge star of a conformal metric in real
dimension two is conformal-factor free, so the star of the affine metric and the star of the cusp
metric are the same quarter turn. -/
theorem deningerAffineCusp_star_agree {lam mu : ℝ} (hlam : lam ≠ 0) (hmu : mu ≠ 0)
    (α β : ℝ × ℝ) :
    deningerConformalInner lam α β * deningerConformalVolume lam
      = deningerConformalInner mu α β * deningerConformalVolume mu := by
  rw [← deningerConformalStar_char hlam, deningerConformalStar_char hmu]

end ConformalOverlap

end RHTower
