import GaloisForLFunctions.HTGeometry.LpShift

/-!
# The punctured space is contractible

The straight-line families used to contract the unit sphere never vanish on any nonzero vector, not
only on the unit vectors: the line from the identity to the isometry can only vanish at the
parameter `1/2` and would then force `S x = -x`, and the line from the isometry to a unit vector
orthogonal to its range is detected by pairing with that vector.  So the same two homotopies
contract the punctured space `H ∖ {0}` itself, with no renormalisation.

Adjoining the origin therefore forms a cone on a contractible base: the punctured space, the sphere
and the whole space are all contractible, so the radial coordinate carries no topology and the polar
decomposition loses nothing at the apex.

* `puncturedIsometryMap` : a linear isometry as a self-map of the punctured space.
* `contractibleSpace_punctured_of_isometry` : **the punctured space is contractible.**
* `contractibleSpace_punctured_lp` : the punctured `ℓ²(ℕ, ℝ)` is contractible.
-/

open scoped InnerProductSpace unitInterval

noncomputable section

namespace GaloisForLFunctions

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (S : H →ₗᵢ[ℝ] H)

/-! ## The isometry as a map of the punctured space -/

theorem isometry_ne_zero {x : H} (hx : x ≠ 0) : S x ≠ 0 := by
  rw [← norm_ne_zero_iff, S.norm_map]
  exact norm_ne_zero_iff.mpr hx

/-- A linear isometry as a self-map of the punctured space. -/
def puncturedIsometryMap : C({x : H // x ≠ 0}, {x : H // x ≠ 0}) where
  toFun x := ⟨S (x : H), isometry_ne_zero S x.2⟩
  continuous_toFun := Continuous.subtype_mk (S.continuous.comp continuous_subtype_val) _

/-! ## The two straight-line families are nonvanishing off the origin -/

theorem puncturedLineToIsometry_ne_zero (hfix : ∀ x : H, S x = -x → x = 0) (t : I)
    (x : {x : H // x ≠ 0}) :
    (1 - (t : ℝ)) • (x : H) + (t : ℝ) • S (x : H) ≠ 0 := by
  intro hzero
  have hx : ‖(x : H)‖ ≠ 0 := norm_ne_zero_iff.mpr x.2
  have hxpos : 0 < ‖(x : H)‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hx)
  have hSx : ‖S (x : H)‖ = ‖(x : H)‖ := S.norm_map _
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (t : ℝ) ≤ 1 := t.2.2
  have heq : (1 - (t : ℝ)) • (x : H) = -((t : ℝ) • S (x : H)) := by
    rw [← sub_eq_zero, sub_neg_eq_add]
    exact hzero
  have hnorm : (1 - (t : ℝ)) * ‖(x : H)‖ = (t : ℝ) * ‖S (x : H)‖ := by
    have h1 : ‖(1 - (t : ℝ)) • (x : H)‖ = ‖-((t : ℝ) • S (x : H))‖ := by rw [heq]
    rw [norm_smul, norm_neg, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - (t : ℝ)), abs_of_nonneg ht0] at h1
    exact h1
  rw [hSx] at hnorm
  have hthalf : (t : ℝ) = 1 / 2 := by
    have := mul_right_cancel₀ hx hnorm
    linarith
  have hhalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [hthalf, hhalf] at hzero
  have h2 : (1 / 2 : ℝ) • ((x : H) + S (x : H)) = 0 := by
    rw [smul_add]
    exact hzero
  have h4 : (x : H) + S (x : H) = 0 := by
    rcases smul_eq_zero.mp h2 with h | h
    · exact absurd h (by norm_num)
    · exact h
  have hxS : S (x : H) = -(x : H) := by
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact h4
  exact x.2 (hfix (x : H) hxS)

theorem puncturedLineToPoint_ne_zero {e : H} (he : ‖e‖ = 1) (hperp : ∀ x : H, ⟪S x, e⟫_ℝ = 0)
    (t : I) (x : {x : H // x ≠ 0}) :
    (1 - (t : ℝ)) • S (x : H) + (t : ℝ) • e ≠ 0 := by
  intro hzero
  have hinner : ⟪(1 - (t : ℝ)) • S (x : H) + (t : ℝ) • e, e⟫_ℝ = (t : ℝ) := by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hperp (x : H),
      real_inner_self_eq_norm_sq, he]
    ring
  rw [hzero, inner_zero_left] at hinner
  have ht : (t : ℝ) = 0 := hinner.symm
  rw [ht] at hzero
  simp only [sub_zero, one_smul, zero_smul, add_zero] at hzero
  exact isometry_ne_zero S x.2 hzero

/-! ## The contraction -/

/-- The straight line from the identity to the isometry, on the punctured space. -/
def puncturedHomotopyToIsometry (hfix : ∀ x : H, S x = -x → x = 0) :
    (ContinuousMap.id {x : H // x ≠ 0}).Homotopy (puncturedIsometryMap S) where
  toFun p := ⟨(1 - (p.1 : ℝ)) • (p.2 : H) + (p.1 : ℝ) • S (p.2 : H),
    puncturedLineToIsometry_ne_zero S hfix p.1 p.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  map_zero_left x := by
    refine Subtype.ext ?_
    show (1 - ((0 : I) : ℝ)) • (x : H) + ((0 : I) : ℝ) • S (x : H) = (x : H)
    norm_num
  map_one_left x := by
    refine Subtype.ext ?_
    show (1 - ((1 : I) : ℝ)) • (x : H) + ((1 : I) : ℝ) • S (x : H) = S (x : H)
    norm_num

/-- The straight line from the isometry to the base point, on the punctured space. -/
def puncturedHomotopyToPoint {e : H} (he : ‖e‖ = 1) (hperp : ∀ x : H, ⟪S x, e⟫_ℝ = 0) :
    (puncturedIsometryMap S).Homotopy
      (ContinuousMap.const {x : H // x ≠ 0}
        (⟨e, by rw [← norm_ne_zero_iff, he]; norm_num⟩ : {x : H // x ≠ 0})) where
  toFun p := ⟨(1 - (p.1 : ℝ)) • S (p.2 : H) + (p.1 : ℝ) • e,
    puncturedLineToPoint_ne_zero S he hperp p.1 p.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  map_zero_left x := by
    refine Subtype.ext ?_
    show (1 - ((0 : I) : ℝ)) • S (x : H) + ((0 : I) : ℝ) • e = S (x : H)
    norm_num
  map_one_left x := by
    refine Subtype.ext ?_
    show (1 - ((1 : I) : ℝ)) • S (x : H) + ((1 : I) : ℝ) • e = e
    norm_num

/-- **The punctured space is contractible** when it carries a linear isometry whose range misses a
unit vector orthogonally and which fixes no antipode.  Adjoining the origin is then a cone on a
contractible base. -/
theorem contractibleSpace_punctured_of_isometry {e : H} (he : ‖e‖ = 1)
    (hperp : ∀ x : H, ⟪S x, e⟫_ℝ = 0) (hfix : ∀ x : H, S x = -x → x = 0) :
    ContractibleSpace {x : H // x ≠ 0} := by
  rw [contractible_iff_id_nullhomotopic]
  refine ⟨⟨e, by rw [← norm_ne_zero_iff, he]; norm_num⟩, ?_⟩
  exact ⟨(puncturedHomotopyToIsometry S hfix).trans (puncturedHomotopyToPoint S he hperp)⟩

/-- **The punctured `ℓ²(ℕ, ℝ)` is contractible**: the radial coordinate of the polar decomposition
carries no topology, and no class is created at the apex. -/
theorem contractibleSpace_punctured_lp : ContractibleSpace {x : LpTwo // x ≠ 0} :=
  contractibleSpace_punctured_of_isometry lpShift norm_lpBasisZero
    inner_lpShift_lpBasisZero lpShift_eq_neg_imp_zero

end GaloisForLFunctions

end
