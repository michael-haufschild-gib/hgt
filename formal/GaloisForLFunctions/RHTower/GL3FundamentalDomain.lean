import GaloisForLFunctions.RHTower.GL3SiegelDomain
import GaloisForLFunctions.HTGeometry.RealPolynomialZeroMeasure


/-!
# A fundamental domain of finite volume for `SL₃(ℤ)` on `h³`

**Faithfulness.** If `g ∈ GL₃(ℝ)` fixes every point then `g gᵀ = c·1` and `g` multiplies each Gram
matrix into a positive multiple of itself; comparing determinants shows the multiple is `1`, so `g`
commutes with `diag(4,1,1)`, `diag(1/4,1/4,1)` and `[[2,1,0],[1,2,1],[0,1,1]]`, hence is scalar
(`eq_smul_one_of_forall_smul_eq`). An integral scalar of determinant one is `1`, so every `γ ≠ 1` in
`SL₃(ℤ)` moves a point (`exists_smul_ne`).

**Null fixed-point sets.** `γ • z = z` iff `γ G γᵀ = (γ G γᵀ)₂₂ G` for `G = gram z`, the vanishing of
the polynomial `fixPoly` in the coordinates. It is nonzero at a moved point, so its zero set is
Lebesgue-null and the fixed-point set has measure zero (`volume_fixedPoints`).

**The domain.** `fundDomain` is the set of points of the Siegel set that are lexicographically minimal
in coordinates among the points of their orbit in the Siegel set. Each orbit meets the Siegel set in
a finite nonempty set (Siegel covering and finiteness), so it meets `fundDomain` in exactly one point.
Distinct translates can overlap only on fixed-point sets, so `fundDomain` is a measurable
fundamental domain (`isFundamentalDomain_fundDomain`) contained in the Siegel set, of finite volume
(`volume_fundDomain_lt_top`).
-/

open Matrix MeasureTheory MvPolynomial
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower.GL3
namespace H3

/-! ### Elements acting trivially are scalar -/

/-- `g • z = z` exactly when `g · gram z · gᵀ` is proportional to `gram z`. -/
theorem smul_eq_self_iff (g : GL (Fin 3) ℝ) (z : H3) :
    g • z = z ↔ (g : Matrix (Fin 3) (Fin 3) ℝ) * z.gram * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ =
      ((g : Matrix (Fin 3) (Fin 3) ℝ) * z.gram * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ) 2 2 • z.gram := by
  set M := (g : Matrix (Fin 3) (Fin 3) ℝ) * z.gram * (g : Matrix (Fin 3) (Fin 3) ℝ)ᵀ
  have hM : M.PosDef := posDef_conj g z
  have hc := hM.diag_pos (i := 2)
  constructor
  · intro h
    have hg := congrArg gram h
    rw [smul_def, gram_ofMat_of_posDef hM] at hg
    rw [← hg, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  · intro h
    rw [smul_def]
    change ofMat M = z
    rw [h, ofMat_smul z.posDef_gram hc, ofMat_gram]

/-- A matrix `A` with `AAᵀ = c₁·1` that multiplies an invertible `G` into a positive multiple of
itself by congruence commutes with `G`. -/
theorem comm_of_conj_eq_smul {A G : Matrix (Fin 3) (Fin 3) ℝ} {c₁ c : ℝ} (hc₁ : 0 < c₁) (hc : 0 < c)
    (hA : A * Aᵀ = c₁ • 1) (hG : A * G * Aᵀ = c • G) (hA0 : A.det ≠ 0) (hG0 : G.det ≠ 0) :
    A * G = G * A := by
  have hAA : Aᵀ * A = c₁ • 1 := by
    have h1 : A * (c₁⁻¹ • Aᵀ) = 1 := by
      rw [Matrix.mul_smul, hA, smul_smul, inv_mul_cancel₀ hc₁.ne', one_smul]
    have h2 := mul_eq_one_comm.1 h1
    rw [Matrix.smul_mul] at h2
    rw [← one_smul ℝ (Aᵀ * A), ← mul_inv_cancel₀ hc₁.ne', mul_smul, h2]
  have key : c₁ • (A * G) = c • (G * A) := by
    calc c₁ • (A * G) = A * G * (Aᵀ * A) := by
          rw [hAA, Matrix.mul_smul, Matrix.mul_one]
      _ = (A * G * Aᵀ) * A := by simp only [Matrix.mul_assoc]
      _ = c • (G * A) := by rw [hG, Matrix.smul_mul]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_smul, Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Fintype.card_fin,
    mul_comm (G.det)] at hdet
  have hcube : c₁ ^ 3 = c ^ 3 := mul_right_cancel₀ (mul_ne_zero hA0 hG0) hdet
  have hcc : c₁ = c := (pow_left_inj₀ hc₁.le hc.le (by norm_num)).1 hcube
  rw [hcc] at key
  exact smul_right_injective _ hc.ne' key

/-- A point with Gram matrix `diag(4, 1, 1)`. -/
def pt2 : H3 := ⟨0, 0, 0, 1, 2, one_pos, two_pos⟩
/-- A point with Gram matrix `diag(1/4, 1/4, 1)`. -/
noncomputable def pt3 : H3 := ⟨0, 0, 0, 1 / 2, 1, by norm_num, one_pos⟩
/-- A point with Gram matrix `[[2,1,0],[1,2,1],[0,1,1]]`. -/
def pt4 : H3 := ⟨1, 1, 0, 1, 1, one_pos, one_pos⟩

/-- **Only scalars act trivially on `h³`.** -/
theorem eq_smul_one_of_forall_smul_eq (g : GL (Fin 3) ℝ) (h : ∀ z : H3, g • z = z) :
    ∃ r : ℝ, (g : Matrix (Fin 3) (Fin 3) ℝ) = r • 1 := by
  set A := (g : Matrix (Fin 3) (Fin 3) ℝ)
  have hA0 : A.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det _ |>.1 (Units.isUnit g)).ne_zero
  have hfix : ∀ z : H3, A * z.gram * Aᵀ = (A * z.gram * Aᵀ) 2 2 • z.gram :=
    fun z => (smul_eq_self_iff g z).1 (h z)
  have hpos : ∀ z : H3, 0 < (A * z.gram * Aᵀ) 2 2 := fun z => (posDef_conj g z).diag_pos
  have hdetg : ∀ z : H3, z.gram.det ≠ 0 := fun z => z.posDef_gram.det_pos.ne'
  have hg1 : (1 : H3).gram = 1 := by simp [gram, mat_one]
  have h1 : A * Aᵀ = (A * (1 : H3).gram * Aᵀ) 2 2 • 1 := by
    have := hfix 1
    rw [hg1, Matrix.mul_one] at this ⊢
    exact this
  have hcomm : ∀ z : H3, A * z.gram = z.gram * A := fun z =>
    comm_of_conj_eq_smul (hpos 1) (hpos z) h1 (hfix z) hA0 (hdetg z)
  have c2 := hcomm pt2
  have c3 := hcomm pt3
  have c4 := hcomm pt4
  rw [gram_apply] at c2 c3 c4
  have e : ∀ (M N : Matrix (Fin 3) (Fin 3) ℝ), M = N → ∀ i j, M i j = N i j := fun M N h i j => by
    rw [h]
  have h01 := e _ _ c2 0 1; have h02 := e _ _ c2 0 2; have h10 := e _ _ c2 1 0
  have h20 := e _ _ c2 2 0; have h12 := e _ _ c3 1 2; have h21 := e _ _ c3 2 1
  have k01 := e _ _ c4 0 1; have k12 := e _ _ c4 1 2
  simp [pt2, pt3, pt4, Matrix.mul_apply, Fin.sum_univ_three] at h01 h02 h10 h20 h12 h21 k01 k12
  refine ⟨A 0 0, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- **`SL₃(ℤ)` acts faithfully on `h³`**: every `γ ≠ 1` moves some point. -/
theorem exists_smul_ne (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (hγ : γ ≠ 1) :
    ∃ z : H3, γ • z ≠ z := by
  by_contra h
  push Not at h
  obtain ⟨r, hr⟩ := eq_smul_one_of_forall_smul_eq (slToGL γ) fun z => by rw [← sl_smul_def]; exact h z
  rw [coe_slToGL] at hr
  have hdet : r ^ 3 = 1 := by
    have hd : ((γ : Matrix (Fin 3) (Fin 3) ℤ).map (Int.castRingHom ℝ)).det = 1 := by
      have := RingHom.map_det (Int.castRingHom ℝ) (γ : Matrix (Fin 3) (Fin 3) ℤ)
      rw [γ.2, map_one] at this
      exact this.symm
    rw [hr, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one] at hd
    exact hd
  have hr1 : r = 1 := by nlinarith [sq_nonneg (r + 1 / 2), sq_nonneg (r - 1)]
  apply hγ
  ext i j
  have := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℝ => M i j) hr
  simp only [hr1, one_smul, Matrix.map_apply, Int.coe_castRingHom] at this
  rw [Matrix.SpecialLinearGroup.coe_one]
  by_cases hij : i = j
  · subst hij; simp only [Matrix.one_apply_eq] at this ⊢; exact_mod_cast this
  · simp only [Matrix.one_apply_ne hij] at this ⊢; exact_mod_cast this

/-! ### Fixed-point sets are null -/

/-- The Gram matrix as a matrix of polynomials in the coordinates `(x₁, x₂, x₃, y₁, y₂)`. -/
noncomputable def Xg : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 5) ℝ) :=
  !![X 3 ^ 2 * X 4 ^ 2 + X 3 ^ 2 * X 1 ^ 2 + X 2 ^ 2, X 3 ^ 2 * X 1 + X 2 * X 0, X 2;
    X 3 ^ 2 * X 1 + X 2 * X 0, X 3 ^ 2 + X 0 ^ 2, X 0; X 2, X 0, 1]

theorem map_eval_Xg (z : H3) : Xg.map (eval (coords z)) = z.gram := by
  rw [gram_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xg, coords]
  ring

/-- The polynomial matrix `A · G · Aᵀ`. -/
noncomputable def conjPoly (A : Matrix (Fin 3) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 5) ℝ) :=
  A.map C * Xg * (A.map C)ᵀ

/-- The polynomial `Σᵢⱼ (Mᵢⱼ − M₂₂ Gᵢⱼ)²`, `M = A G Aᵀ`, vanishing exactly where `A` fixes the point. -/
noncomputable def fixPoly (A : Matrix (Fin 3) (Fin 3) ℝ) : MvPolynomial (Fin 5) ℝ :=
  ∑ i, ∑ j, (conjPoly A i j - conjPoly A 2 2 * Xg i j) ^ 2

theorem eval_fixPoly (A : Matrix (Fin 3) (Fin 3) ℝ) (z : H3) :
    eval (coords z) (fixPoly A) =
      ∑ i, ∑ j, ((A * z.gram * Aᵀ) i j - (A * z.gram * Aᵀ) 2 2 * z.gram i j) ^ 2 := by
  have hA : (A.map C).map (eval (coords z)) = A := by
    rw [Matrix.map_map]; ext i j; simp
  have hmap : (conjPoly A).map (eval (coords z)) = A * z.gram * Aᵀ := by
    rw [conjPoly, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hA, map_eval_Xg]
  simp only [fixPoly, map_sum, map_pow, map_sub, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hmap, ← map_eval_Xg z]
  rfl

theorem fixPoly_eval_eq_zero_iff (A : Matrix (Fin 3) (Fin 3) ℝ) (z : H3) :
    eval (coords z) (fixPoly A) = 0 ↔ A * z.gram * Aᵀ = (A * z.gram * Aᵀ) 2 2 • z.gram := by
  rw [eval_fixPoly]
  constructor
  · intro h
    ext i j
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg _).1 h i (Finset.mem_univ _)
    have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).1 hi j (Finset.mem_univ _)
    rw [Matrix.smul_apply, smul_eq_mul]
    linarith [pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hj]
  · intro h
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    have := congrFun (congrFun h i) j
    rw [Matrix.smul_apply, smul_eq_mul] at this
    rw [this]; ring

/-- **The fixed-point set of every `γ ≠ 1` in `SL₃(ℤ)` is null.** It lies in the zero set of the
nonzero polynomial `fixPoly`. -/
theorem volume_fixedPoints (γ : Matrix.SpecialLinearGroup (Fin 3) ℤ) (hγ : γ ≠ 1) :
    volume {z : H3 | γ • z = z} = 0 := by
  obtain ⟨z0, hz0⟩ := exists_smul_ne γ hγ
  set A := ((slToGL γ : GL (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ)
  have hP : fixPoly A ≠ 0 := by
    intro h0
    apply hz0
    rw [sl_smul_def, smul_eq_self_iff, ← fixPoly_eval_eq_zero_iff, h0, map_zero]
  have hnull := realMvPolynomial_zero_set_volume_fin 5 (fixPoly A) hP
  rw [volume_eq_lintegral]
  refine setLIntegral_measure_zero _ _ (measure_mono_null ?_ hnull)
  rintro _ ⟨z, hz, rfl⟩
  show eval (coords z) (fixPoly A) = 0
  rw [fixPoly_eval_eq_zero_iff, ← smul_eq_self_iff, ← sl_smul_def]
  exact hz

/-! ### A fundamental domain of finite volume -/

/-- Lexicographic order on the Iwasawa coordinates. -/
def lexC (z : H3) : Lex (Fin 5 → ℝ) := toLex (coords z)

theorem lexC_injective : Function.Injective lexC := fun _ _ h =>
  coords_injective (toLex.injective h)

/-- **The fundamental domain**: the points of the Siegel set that are lexicographically minimal
among the points of their orbit lying in the Siegel set. -/
def fundDomain : Set H3 :=
  {z | z ∈ siegelSet ∧ ∀ γ : Matrix.SpecialLinearGroup (Fin 3) ℤ, γ • z ∈ siegelSet →
    lexC z ≤ lexC (γ • z)}

theorem finite_orbit_siegel (z : H3) :
    {γ : Matrix.SpecialLinearGroup (Fin 3) ℤ | γ • z ∈ siegelSet}.Finite := by
  obtain ⟨γ₀, h₀⟩ := exists_smul_mem_siegelSet z
  refine ((finite_siegelTransitions.image fun δ => δ * γ₀)).subset ?_
  intro γ hγ
  refine ⟨γ * γ₀⁻¹, ⟨γ₀ • z, h₀, ?_⟩, by simp⟩
  rw [← mul_smul, inv_mul_cancel_right]
  exact hγ

/-- Every orbit meets the fundamental domain. -/
theorem exists_smul_mem_fundDomain (z : H3) :
    ∃ γ : Matrix.SpecialLinearGroup (Fin 3) ℤ, γ • z ∈ fundDomain := by
  obtain ⟨γ₀, h₀⟩ := exists_smul_mem_siegelSet z
  obtain ⟨γ, hγ, hmin⟩ := Set.exists_min_image _ (fun δ => lexC (δ • z)) (finite_orbit_siegel z)
    ⟨γ₀, h₀⟩
  refine ⟨γ, hγ, fun δ hδ => ?_⟩
  rw [← mul_smul] at hδ ⊢
  exact hmin _ hδ

/-- Each orbit meets the fundamental domain in exactly one point. -/
theorem eq_of_mem_fundDomain {z : H3} {γ : Matrix.SpecialLinearGroup (Fin 3) ℤ}
    (hz : z ∈ fundDomain) (hγz : γ • z ∈ fundDomain) : γ • z = z := by
  have h1 := hz.2 γ hγz.1
  have h2 := hγz.2 γ⁻¹ (by rw [inv_smul_smul]; exact hz.1)
  rw [inv_smul_smul] at h2
  exact lexC_injective (le_antisymm h2 h1)

theorem isClosed_siegelSet : IsClosed siegelSet := by
  have e : siegelSet = {z : H3 | 1 ≤ 2 * z.y1 ^ 2} ∩ {z | 1 ≤ 2 * z.y2 ^ 2} ∩ {z | |z.x1| ≤ 1} ∩
      {z | |z.x2| ≤ 1} ∩ {z | |z.x3| ≤ 1} := by
    ext z; simp [siegelSet, and_assoc]
  rw [e]
  exact ((((isClosed_le continuous_const (by fun_prop)).inter
    (isClosed_le continuous_const (by fun_prop))).inter
    (isClosed_le (by fun_prop) continuous_const)).inter
    (isClosed_le (by fun_prop) continuous_const)).inter
    (isClosed_le (by fun_prop) continuous_const)

theorem measurableSet_siegelSet : MeasurableSet siegelSet := isClosed_siegelSet.measurableSet

instance : Countable (Matrix.SpecialLinearGroup (Fin 3) ℤ) := by
  haveI : Countable (Matrix (Fin 3) (Fin 3) ℤ) := inferInstanceAs (Countable (Fin 3 → Fin 3 → ℤ))
  exact Subtype.countable

theorem measurable_coords_apply (i : Fin 5) : Measurable fun z : H3 => coords z i :=
  ((continuous_apply i).comp continuous_coords).measurable

theorem measurableSet_lexC_le {f g : H3 → H3} (hf : Measurable f) (hg : Measurable g) :
    MeasurableSet {z | lexC (f z) ≤ lexC (g z)} := by
  have e : {z | lexC (f z) ≤ lexC (g z)} =
      {z | coords (f z) = coords (g z)} ∪
        ⋃ i : Fin 5, ({z | ∀ j, j < i → coords (f z) j = coords (g z) j} ∩
          {z | coords (f z) i < coords (g z) i}) := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff, lexC,
      le_iff_eq_or_lt, EmbeddingLike.apply_eq_iff_eq]
    rfl
  rw [e]
  have hfi : ∀ i, Measurable fun z => coords (f z) i := fun i => (measurable_coords_apply i).comp hf
  have hgi : ∀ i, Measurable fun z => coords (g z) i := fun i => (measurable_coords_apply i).comp hg
  refine MeasurableSet.union ?_ (MeasurableSet.iUnion fun i => ?_)
  · have : {z | coords (f z) = coords (g z)} = ⋂ i, {z | coords (f z) i = coords (g z) i} := by
      ext z; simp [funext_iff]
    rw [this]
    exact MeasurableSet.iInter fun i => measurableSet_eq_fun (hfi i) (hgi i)
  · refine MeasurableSet.inter ?_ (measurableSet_lt (hfi i) (hgi i))
    have : {z | ∀ j, j < i → coords (f z) j = coords (g z) j} =
        ⋂ j, ⋂ (_ : j < i), {z | coords (f z) j = coords (g z) j} := by
      ext z; simp
    rw [this]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      measurableSet_eq_fun (hfi j) (hgi j)

theorem measurableSet_fundDomain : MeasurableSet fundDomain := by
  have e : fundDomain = siegelSet ∩ ⋂ γ : Matrix.SpecialLinearGroup (Fin 3) ℤ,
      ((fun z => γ • z) ⁻¹' siegelSet)ᶜ ∪ {z | lexC z ≤ lexC (γ • z)} := by
    ext z
    simp only [fundDomain, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_union,
      Set.mem_compl_iff, Set.mem_preimage, imp_iff_not_or]
  rw [e]
  refine measurableSet_siegelSet.inter (MeasurableSet.iInter fun γ => ?_)
  have hγ : Measurable fun z : H3 => γ • z := (continuous_const_smul (slToGL γ)).measurable
  exact (measurableSet_siegelSet.preimage hγ).compl.union (measurableSet_lexC_le measurable_id hγ)

/-- **A fundamental domain for `SL₃(ℤ)` on `h³`.** -/
theorem isFundamentalDomain_fundDomain :
    IsFundamentalDomain (Matrix.SpecialLinearGroup (Fin 3) ℤ) fundDomain volume where
  nullMeasurableSet := measurableSet_fundDomain.nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall exists_smul_mem_fundDomain
  aedisjoint := by
    intro γ₁ γ₂ hne
    have hδ : γ₂⁻¹ * γ₁ ≠ 1 := fun h => hne (inv_mul_eq_one.1 h).symm
    refine measure_mono_null ?_ ((measure_smul_null (volume_fixedPoints _ hδ)) γ₁)
    rintro z ⟨⟨w₁, hw₁, rfl⟩, ⟨w₂, hw₂, hw⟩⟩
    refine ⟨w₁, ?_, rfl⟩
    simp only at hw
    have hw₂' : w₂ = (γ₂⁻¹ * γ₁) • w₁ := by
      rw [mul_smul, ← hw, inv_smul_smul]
    rw [hw₂'] at hw₂
    show (γ₂⁻¹ * γ₁) • w₁ = w₁
    exact eq_of_mem_fundDomain hw₁ hw₂

/-- **`SL₃(ℤ)\h³` has finite volume.** -/
theorem volume_fundDomain_lt_top : volume fundDomain < ⊤ :=
  lt_of_le_of_lt (measure_mono fun _ hz => hz.1) volume_siegelSet_lt_top

end H3
end GaloisForLFunctions.RHTower.GL3
