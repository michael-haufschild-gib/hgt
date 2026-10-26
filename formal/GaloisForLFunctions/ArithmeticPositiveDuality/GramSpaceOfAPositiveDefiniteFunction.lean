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

/-- The vector `δ_g`. -/
def gnsVec (g : G) : PreGNS Φ := Finsupp.single g 1

/-- The φ-inner product `⟪x, y⟫ = Σ conj(x_g) y_h φ(g⁻¹h)`. -/
def gnsInner (x y : PreGNS Φ) : ℂ :=
  Finsupp.sum (M := ℂ) x fun g a => Finsupp.sum (M := ℂ) y fun h b => star a * Φ.toFun (g⁻¹ * h) * b

theorem gnsInner_add_left (x y z : PreGNS Φ) :
    gnsInner Φ (x + y) z = gnsInner Φ x z + gnsInner Φ y z := by
  unfold gnsInner
  rw [Finsupp.sum_add_index']
  · intro g; simp
  · intro g a b
    rw [← Finsupp.sum_add]
    refine Finsupp.sum_congr fun h _ => ?_
    rw [star_add]; ring

theorem gnsInner_smul_left (x y : PreGNS Φ) (r : ℂ) :
    gnsInner Φ (r • x) y = star r * gnsInner Φ x y := by
  unfold gnsInner
  rw [Finsupp.sum_smul_index']
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
  rw [Finsupp.sum_add_index']
  · intro h; simp
  · intro h a b; ring

theorem gnsInner_smul_right (x y : PreGNS Φ) (r : ℂ) :
    gnsInner Φ x (r • y) = r * gnsInner Φ x y := by
  unfold gnsInner
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.sum_smul_index', Finsupp.mul_sum]
  · refine Finsupp.sum_congr fun h _ => ?_
    rw [smul_eq_mul]; ring
  · intro h; simp

theorem gnsInner_single_single (g h : G) (a b : ℂ) :
    gnsInner Φ (Finsupp.single g a) (Finsupp.single h b) = star a * Φ.toFun (g⁻¹ * h) * b := by
  unfold gnsInner
  rw [Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]

theorem gnsInner_gnsVec (g h : G) : gnsInner Φ (gnsVec Φ g) (gnsVec Φ h) = Φ.toFun (g⁻¹ * h) := by
  rw [gnsVec, gnsVec, gnsInner_single_single]; simp

/-- The self-pairing is a Gram form. -/
theorem gnsInner_self_eq (x : PreGNS Φ) :
    ∃ r : ℝ, 0 ≤ r ∧ gnsInner Φ x x = r := by
  obtain ⟨r, hr, h⟩ := Φ.posDef.form (fun i : (x : G →₀ ℂ).support => (i : G))
    (fun i => (x : G →₀ ℂ) i)
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

instance : SeminormedAddCommGroup (PreGNS Φ) :=
  (preGNSCore Φ).toSeminormedAddCommGroup

instance : InnerProductSpace ℂ (PreGNS Φ) := InnerProductSpace.ofCore (preGNSCore Φ)

theorem inner_eq_gnsInner (x y : PreGNS Φ) : inner ℂ x y = gnsInner Φ x y := rfl

theorem inner_gnsVec (g h : G) : inner ℂ (gnsVec Φ g) (gnsVec Φ h) = Φ.toFun (g⁻¹ * h) :=
  gnsInner_gnsVec Φ g h

/-! ### Translations -/

/-- Left translation by `a`: `δ_g ↦ δ_{ag}`. -/
def gnsTranslate (a : G) : PreGNS Φ →ₗ[ℂ] PreGNS Φ :=
  Finsupp.lmapDomain ℂ ℂ (a * ·)

theorem gnsTranslate_gnsVec (a g : G) : gnsTranslate Φ a (gnsVec Φ g) = gnsVec Φ (a * g) := by
  simp [gnsTranslate, gnsVec]

/-- Translations are isometric. -/
theorem inner_gnsTranslate (a : G) (x y : PreGNS Φ) :
    inner ℂ (gnsTranslate Φ a x) (gnsTranslate Φ a y) = inner ℂ x y := by
  rw [inner_eq_gnsInner, inner_eq_gnsInner]
  unfold gnsInner gnsTranslate
  simp only [Finsupp.lmapDomain_apply]
  rw [Finsupp.sum_mapDomain_index (by simp) (by intro g a b; rw [← Finsupp.sum_add]; refine
    Finsupp.sum_congr fun h _ => ?_; rw [star_add]; ring)]
  refine Finsupp.sum_congr fun g _ => ?_
  rw [Finsupp.sum_mapDomain_index (by simp) (by intro h a b; ring)]
  refine Finsupp.sum_congr fun h _ => ?_
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left]

theorem gnsTranslate_mul (a b : G) (x : PreGNS Φ) :
    gnsTranslate Φ (a * b) x = gnsTranslate Φ a (gnsTranslate Φ b x) := by
  simp only [gnsTranslate, Finsupp.lmapDomain_apply, ← Finsupp.mapDomain_comp]
  congr 1
  funext g
  simp [mul_assoc]

theorem gnsTranslate_one (x : PreGNS Φ) : gnsTranslate Φ 1 x = x := by
  show Finsupp.mapDomain (fun g => 1 * g) (x : G →₀ ℂ) = x
  simp only [one_mul]
  exact Finsupp.mapDomain_id

theorem inner_gnsTranslate_left (a : G) (x y : PreGNS Φ) :
    inner ℂ (gnsTranslate Φ a x) y = inner ℂ x (gnsTranslate Φ a⁻¹ y) := by
  rw [← inner_gnsTranslate Φ a⁻¹, ← gnsTranslate_mul, inv_mul_cancel, gnsTranslate_one]

end GaloisForLFunctions.ArithmeticPositiveDuality
