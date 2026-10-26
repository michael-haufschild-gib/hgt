import GaloisForLFunctions.ArithmeticPositiveDuality.TheIntegerSuccessorForcesTheHeckeWeight

/-!
# The pre-Hilbert space of a positive-definite function

For a positive-definite `φ` on a group `G`, finitely supported vectors `x : G →₀ ℂ` carry the
semi-inner product `⟪x, y⟫ = Σ_{g,h} conj(x_g) y_h φ(g⁻¹h)`; `G` acts isometrically by left
translation and `⟪δ_g, δ_h⟫ = φ(g⁻¹h)`. Every Gram-form argument about `φ` is an argument in this
space: Cauchy–Schwarz, null vectors, Bessel's inequality.
-/

open Complex Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

variable {G : Type*} [Group G]

/-- A positive-definite function, bundled. -/
structure PosDefFn (G : Type*) [Group G] where
  /-- The function. -/
  toFun : G → ℂ
  posDef : IsPosDefOnGroup toFun

/-- The pre-Hilbert space of a positive-definite function: finitely supported vectors on `G`. -/
def PreGNS (_Φ : PosDefFn G) : Type _ := G →₀ ℂ

variable (Φ : PosDefFn G)

instance : AddCommGroup (PreGNS Φ) := inferInstanceAs (AddCommGroup (G →₀ ℂ))
instance : Module ℂ (PreGNS Φ) := inferInstanceAs (Module ℂ (G →₀ ℂ))

/-- The underlying finitely supported function. -/
def toF (x : PreGNS Φ) : G →₀ ℂ := x

theorem toF_add (x y : PreGNS Φ) : toF Φ (x + y) = toF Φ x + toF Φ y := rfl
theorem toF_smul (r : ℂ) (x : PreGNS Φ) : toF Φ (r • x) = r • toF Φ x := rfl

/-- The vector `δ_g`. -/
def gnsVec (g : G) : PreGNS Φ := Finsupp.single g 1

/-- The φ-inner product `⟪x, y⟫ = Σ conj(x_g) y_h φ(g⁻¹h)`. -/
def gnsInner (x y : PreGNS Φ) : ℂ :=
  (toF Φ x).sum fun g a => (toF Φ y).sum fun h b => star a * Φ.toFun (g⁻¹ * h) * b

theorem gnsInner_add_left (x y z : PreGNS Φ) :
    gnsInner Φ (x + y) z = gnsInner Φ x z + gnsInner Φ y z := by
  unfold gnsInner
  rw [toF_add, Finsupp.sum_add_index']
  · intro g; simp
  · intro g a b
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [star_add]; ring

theorem gnsInner_smul_left (x y : PreGNS Φ) (r : ℂ) :
    gnsInner Φ (r • x) y = star r * gnsInner Φ x y := by
  unfold gnsInner
  rw [toF_smul, Finsupp.sum_smul_index']
  · rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun g _ => ?_
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [smul_eq_mul, star_mul]; ring
  · intro g; simp

theorem gnsInner_add_right (x y z : PreGNS Φ) :
    gnsInner Φ x (y + z) = gnsInner Φ x y + gnsInner Φ x z := by
  unfold gnsInner
  rw [← Finsupp.sum_add]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [toF_add, Finsupp.sum_add_index']
  · intro h; simp
  · intro h a b; ring

theorem gnsInner_smul_right (x y : PreGNS Φ) (r : ℂ) :
    gnsInner Φ x (r • y) = r * gnsInner Φ x y := by
  unfold gnsInner
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [toF_smul, Finsupp.sum_smul_index', Finsupp.mul_sum]
  · refine Finsupp.sum_congr fun h _ => ?_
    rw [smul_eq_mul]; ring
  · intro h; simp

theorem gnsInner_gnsVec (g h : G) : gnsInner Φ (gnsVec Φ g) (gnsVec Φ h) = Φ.toFun (g⁻¹ * h) := by
  show (Finsupp.single g (1 : ℂ)).sum (fun g a => (Finsupp.single h (1 : ℂ)).sum
    fun h b => star a * Φ.toFun (g⁻¹ * h) * b) = _
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  simp

/-- The self-pairing is a Gram form. -/
theorem gnsInner_self_eq (x : PreGNS Φ) :
    ∃ r : ℝ, 0 ≤ r ∧ gnsInner Φ x x = r := by
  obtain ⟨r, hr, h⟩ := Φ.posDef.form (fun i : (toF Φ x).support => (i : G))
    (fun i => toF Φ x i)
  refine ⟨r, hr, ?_⟩
  rw [← h]
  unfold gnsInner
  rw [Finsupp.sum, ← Finset.sum_coe_sort]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finsupp.sum, ← Finset.sum_coe_sort]

theorem gnsInner_conj_symm (x y : PreGNS Φ) : star (gnsInner Φ y x) = gnsInner Φ x y := by
  unfold gnsInner
  simp only [Finsupp.sum, star_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun h _ => ?_
  rw [star_mul, star_mul, star_star, ← Φ.posDef.map_inv, mul_inv_rev, inv_inv]
  ring

/-- The pre-inner-product core. -/
instance preGNSCore : PreInnerProductSpace.Core ℂ (PreGNS Φ) where
  inner x y := gnsInner Φ x y
  conj_inner_symm x y := gnsInner_conj_symm Φ x y
  re_inner_nonneg x := by
    obtain ⟨r, hr, h⟩ := gnsInner_self_eq Φ x
    show 0 ≤ (gnsInner Φ x x).re
    rw [h, Complex.ofReal_re]; exact hr
  add_left x y z := gnsInner_add_left Φ x y z
  smul_left x y r := gnsInner_smul_left Φ x y r

instance instSeminormedAddCommGroupPreGNS : SeminormedAddCommGroup (PreGNS Φ) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (PreGNS Φ) := InnerProductSpace.ofCore (preGNSCore Φ)

theorem inner_eq_gnsInner (x y : PreGNS Φ) : inner ℂ x y = gnsInner Φ x y := rfl

theorem inner_gnsVec (g h : G) : inner ℂ (gnsVec Φ g) (gnsVec Φ h) = Φ.toFun (g⁻¹ * h) :=
  gnsInner_gnsVec Φ g h

/-! ### Translations -/

/-- Left translation by `a`: `δ_g ↦ δ_{ag}`. -/
def gnsTranslate (a : G) : PreGNS Φ →ₗ[ℂ] PreGNS Φ :=
  Finsupp.lmapDomain ℂ ℂ (a * ·)

theorem toF_gnsTranslate (a : G) (x : PreGNS Φ) :
    toF Φ (gnsTranslate Φ a x) = Finsupp.mapDomain (a * ·) (toF Φ x) := rfl

theorem gnsTranslate_gnsVec (a g : G) : gnsTranslate Φ a (gnsVec Φ g) = gnsVec Φ (a * g) := by
  show Finsupp.mapDomain (a * ·) (Finsupp.single g (1 : ℂ)) = Finsupp.single (a * g) 1
  exact Finsupp.mapDomain_single

/-- Translations are isometric. -/
theorem inner_gnsTranslate (a : G) (x y : PreGNS Φ) :
    inner ℂ (gnsTranslate Φ a x) (gnsTranslate Φ a y) = inner ℂ x y := by
  rw [inner_eq_gnsInner, inner_eq_gnsInner]
  unfold gnsInner
  rw [toF_gnsTranslate, toF_gnsTranslate]
  have hadd : ∀ (g : G) (u v : ℂ), (Finsupp.mapDomain (a * ·) (toF Φ y)).sum
      (fun h b => star (u + v) * Φ.toFun (g⁻¹ * h) * b) =
      (Finsupp.mapDomain (a * ·) (toF Φ y)).sum (fun h b => star u * Φ.toFun (g⁻¹ * h) * b) +
      (Finsupp.mapDomain (a * ·) (toF Φ y)).sum (fun h b => star v * Φ.toFun (g⁻¹ * h) * b) := by
    intro g u v
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [star_add]; ring
  rw [Finsupp.sum_mapDomain_index (by simp) hadd]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.sum_mapDomain_index (by simp) (by intro h u v; ring)]
  refine Finsupp.sum_congr fun h _ => ?_
  rw [mul_inv_rev, show g⁻¹ * a⁻¹ * (a * h) = g⁻¹ * h by group]

theorem gnsTranslate_mul (a b : G) (x : PreGNS Φ) :
    gnsTranslate Φ (a * b) x = gnsTranslate Φ a (gnsTranslate Φ b x) := by
  show Finsupp.mapDomain ((a * b) * ·) (toF Φ x) =
    Finsupp.mapDomain (a * ·) (Finsupp.mapDomain (b * ·) (toF Φ x))
  rw [← Finsupp.mapDomain_comp]
  congr 1
  funext g
  simp [mul_assoc]

theorem gnsTranslate_one (x : PreGNS Φ) : gnsTranslate Φ 1 x = x := by
  show Finsupp.mapDomain (fun g => 1 * g) (toF Φ x) = x
  simp only [one_mul]
  exact Finsupp.mapDomain_id

theorem inner_gnsTranslate_left (a : G) (x y : PreGNS Φ) :
    inner ℂ (gnsTranslate Φ a x) y = inner ℂ x (gnsTranslate Φ a⁻¹ y) := by
  rw [← inner_gnsTranslate Φ a⁻¹, ← gnsTranslate_mul, inv_mul_cancel, gnsTranslate_one]

end GaloisForLFunctions.ArithmeticPositiveDuality
