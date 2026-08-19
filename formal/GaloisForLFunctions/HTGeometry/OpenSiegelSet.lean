import GaloisForLFunctions.HTGeometry.JacobiSignFlip

/-!
# The open Siegel set and finite presentability of `SL(n, ℤ)`

Replacing the Siegel bounds by strict inequalities turns the Siegel set into an **open** subset of
the cone, because the Jacobi coordinates are continuous.  It is connected, being the continuous image
of the convex region of admissible Jacobi parameters; its translates still cover the cone, because
the closed Siegel set of the covering theorem sits inside it; and its overlap set is finite by
Siegel's finiteness property.

These are exactly the hypotheses of Macbeath's criterion on a convex domain, so the arithmetic group
is finitely presented.

* `openSiegelSet` : the Siegel set with strict bounds.
* `isOpen_openSiegelSet`, `openSiegelSet_nonempty`, `isPreconnected_openSiegelSet` : its topology.
* `openSiegelSet_cover` : **its translates cover the cone.**
* `meetSet_openSiegelSet_finite` : **its overlap set is finite.**
* `isFinitelyPresented_specialLinearGroup` : **`SL(n, ℤ)` is finitely presented.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix Pointwise

variable {n : ℕ}

theorem jacOf_d_of_form {A : posDefCone n} {J : JacobiData n} (h : J.form = coneMat A) :
    (jacOf A).d = J.d :=
  JacobiData.d_unique (by rw [jacOf_form, h])

theorem jacOf_U_of_form {A : posDefCone n} {J : JacobiData n} (h : J.form = coneMat A) :
    (jacOf A).U = J.U :=
  JacobiData.U_unique (by rw [jacOf_form, h])

/-- The Siegel set with strict bounds. -/
def openSiegelSet (n : ℕ) (t u : ℝ) : Set (posDefCone n) :=
  {A | (∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → (jacOf A).d i < t * (jacOf A).d j)
      ∧ (∀ i j : Fin n, |(jacOf A).U i j| < u)}

theorem isSiegel_of_mem_openSiegelSet {t u : ℝ} {A : posDefCone n}
    (hA : A ∈ openSiegelSet n t u) : (jacOf A).IsSiegel t u :=
  ⟨fun i j hij => (hA.1 i j hij).le, fun i j => (hA.2 i j).le⟩

/-- **The open Siegel set is open.** -/
theorem isOpen_openSiegelSet (n : ℕ) (t u : ℝ) : IsOpen (openSiegelSet n t u) := by
  classical
  have heq : openSiegelSet n t u
      = (⋂ i : Fin n, ⋂ j : Fin n,
          {A : posDefCone n | (i : ℕ) + 1 = (j : ℕ) → (jacOf A).d i < t * (jacOf A).d j})
        ∩ (⋂ i : Fin n, ⋂ j : Fin n, {A : posDefCone n | |(jacOf A).U i j| < u}) := by
    ext A
    simp only [openSiegelSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [heq]
  refine IsOpen.inter ?_ ?_
  · refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    by_cases hij : (i : ℕ) + 1 = (j : ℕ)
    · simpa [hij] using
        isOpen_lt (continuous_jacOf_d i) (continuous_const.mul (continuous_jacOf_d j))
    · simp [hij]
  · refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => ?_
    exact isOpen_lt (continuous_jacOf_U i j).abs continuous_const

/-- The identity form, as a point of the cone. -/
def coneOne (n : ℕ) : posDefCone n := ⟨⟨1, Matrix.transpose_one⟩, Matrix.PosDef.one⟩

theorem coneMat_coneOne (n : ℕ) : coneMat (coneOne n) = 1 := rfl

/-- The Jacobi datum of the identity form. -/
def jacobiOne (n : ℕ) : JacobiData n where
  U := 1
  d := fun _ => 1
  pos := fun _ => zero_lt_one
  upper := fun _ _ hji => Matrix.one_apply_ne (fun h => absurd (h ▸ hji) (lt_irrefl _))
  unit := fun i => Matrix.one_apply_eq i

theorem jacobiOne_form (n : ℕ) : (jacobiOne n).form = 1 := by
  show (1 : Matrix (Fin n) (Fin n) ℝ)ᵀ * Matrix.diagonal (fun _ => (1 : ℝ)) * 1 = 1
  rw [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.diagonal_one]

/-- **The open Siegel set is nonempty.** -/
theorem openSiegelSet_nonempty {t u : ℝ} (ht : 1 < t) (hu : 1 < u) :
    (openSiegelSet n t u).Nonempty := by
  classical
  refine ⟨coneOne n, ?_, ?_⟩
  · intro i j _
    rw [jacOf_d_of_form (A := coneOne n) (J := jacobiOne n) (by rw [jacobiOne_form]; rfl)]
    show (1 : ℝ) < t * 1
    linarith
  · intro i j
    rw [jacOf_U_of_form (A := coneOne n) (J := jacobiOne n) (by rw [jacobiOne_form]; rfl)]
    show |(1 : Matrix (Fin n) (Fin n) ℝ) i j| < u
    by_cases hij : i = j
    · rw [hij, Matrix.one_apply_eq, abs_one]
      exact hu
    · rw [Matrix.one_apply_ne hij, abs_zero]
      linarith

/-- The Jacobi parameters satisfying the strict Siegel bounds. -/
def siegelParam (n : ℕ) (t u : ℝ) : Set (Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) :=
  {p | (∀ i j : Fin n, j < i → p.1 i j = 0) ∧ (∀ i, p.1 i i = 1)
      ∧ (∀ i j, |p.1 i j| < u) ∧ (∀ i, 0 < p.2 i)
      ∧ (∀ i j : Fin n, (i : ℕ) + 1 = (j : ℕ) → p.2 i < t * p.2 j)}

/-- **The parameter region is convex**: all its conditions are linear. -/
theorem convex_siegelParam (n : ℕ) (t u : ℝ) : Convex ℝ (siegelParam n t u) := by
  intro p hp q hq a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hq
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hp
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := hp
  obtain ⟨hq1, hq2, hq3, hq4, hq5⟩ := hq
  refine ⟨fun i j hji => ?_, fun i => ?_, fun i j => ?_, fun i => ?_, fun i j hij => ?_⟩
  · show a * p.1 i j + b * q.1 i j = 0
    rw [hp1 i j hji, hq1 i j hji]
    ring
  · show a * p.1 i i + b * q.1 i i = 1
    rw [hp2 i, hq2 i]
    linarith
  · show |a * p.1 i j + b * q.1 i j| < u
    have h1 : |a * p.1 i j| < a * u := by
      rw [abs_mul, abs_of_pos hapos]
      exact mul_lt_mul_of_pos_left (hp3 i j) hapos
    have h2 : |b * q.1 i j| < b * u := by
      rw [abs_mul, abs_of_pos hbpos]
      exact mul_lt_mul_of_pos_left (hq3 i j) hbpos
    calc |a * p.1 i j + b * q.1 i j| ≤ |a * p.1 i j| + |b * q.1 i j| := abs_add_le _ _
      _ < a * u + b * u := by linarith
      _ = u := by rw [← add_mul, hab, one_mul]
  · show 0 < a * p.2 i + b * q.2 i
    have := hp4 i
    have := hq4 i
    nlinarith
  · show a * p.2 i + b * q.2 i < t * (a * p.2 j + b * q.2 j)
    have h1 : p.2 i < t * p.2 j := hp5 i j hij
    have h2 : q.2 i < t * q.2 j := hq5 i j hij
    nlinarith

/-- The form attached to Jacobi parameters. -/
def psiParam (p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  p.1ᵀ * Matrix.diagonal p.2 * p.1

theorem continuous_psiParam : Continuous (psiParam (n := n)) := by
  classical
  have hdiag : Continuous
      (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) => Matrix.diagonal p.2) := by
    refine continuous_matrix fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.diagonal_apply_eq]
      exact (continuous_apply i).comp continuous_snd
    · simpa [Matrix.diagonal_apply_ne _ hij] using continuous_const
  exact ((continuous_fst.matrix_transpose).matrix_mul hdiag).matrix_mul continuous_fst

/-- The Jacobi datum attached to admissible parameters. -/
def jacobiOfParam {t u : ℝ} {p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)}
    (hp : p ∈ siegelParam n t u) : JacobiData n :=
  ⟨p.1, p.2, hp.2.2.2.1, hp.1, hp.2.1⟩

theorem jacobiOfParam_form {t u : ℝ} {p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ)}
    (hp : p ∈ siegelParam n t u) : (jacobiOfParam hp).form = psiParam p := rfl

theorem coneMat_image_openSiegelSet (n : ℕ) (t u : ℝ) :
    coneMat '' (openSiegelSet n t u) = psiParam '' (siegelParam n t u) := by
  ext X
  constructor
  · rintro ⟨A, hA, rfl⟩
    refine ⟨((jacOf A).U, (jacOf A).d), ⟨(jacOf A).upper, (jacOf A).unit, hA.2,
      (jacOf A).pos, hA.1⟩, ?_⟩
    show ((jacOf A).U)ᵀ * Matrix.diagonal (jacOf A).d * (jacOf A).U = coneMat A
    exact jacOf_form A
  · rintro ⟨p, hp, rfl⟩
    have hform : (jacobiOfParam hp).form = psiParam p := jacobiOfParam_form hp
    have hsymm : (psiParam p)ᵀ = psiParam p := by
      rw [← hform]
      have : ((jacobiOfParam hp).form)ᵀ = (jacobiOfParam hp).form := by
        show (((jacobiOfParam hp).U)ᵀ * Matrix.diagonal (jacobiOfParam hp).d
          * (jacobiOfParam hp).U)ᵀ = _
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
          Matrix.diagonal_transpose, ← Matrix.mul_assoc]
        rfl
      exact this
    have hpd : (psiParam p).PosDef := by
      rw [← hform]
      exact (jacobiOfParam hp).posDef
    refine ⟨⟨⟨psiParam p, hsymm⟩, hpd⟩, ?_, rfl⟩
    have hcm : coneMat (⟨⟨psiParam p, hsymm⟩, hpd⟩ : posDefCone n) = psiParam p := rfl
    constructor
    · intro i j hij
      rw [jacOf_d_of_form (J := jacobiOfParam hp) (by rw [hform, hcm])]
      exact hp.2.2.2.2 i j hij
    · intro i j
      rw [jacOf_U_of_form (J := jacobiOfParam hp) (by rw [hform, hcm])]
      exact hp.2.2.1 i j

/-- **The open Siegel set is connected**: it is the continuous image of a convex parameter region. -/
theorem isPreconnected_openSiegelSet (n : ℕ) (t u : ℝ) :
    IsPreconnected (openSiegelSet n t u) := by
  have hind : Topology.IsInducing (coneMat (n := n)) :=
    Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  rw [← hind.isPreconnected_image, coneMat_image_openSiegelSet]
  exact ((convex_siegelParam n t u).isPreconnected).image _ continuous_psiParam.continuousOn

theorem slReal_injective : Function.Injective (slReal (n := n)) := by
  intro g h hgh
  refine Subtype.ext ?_
  ext a b
  have hab : ((g : Matrix (Fin n) (Fin n) ℤ) a b : ℝ) = ((h : Matrix (Fin n) (Fin n) ℤ) a b : ℝ) :=
    congrFun (congrFun hgh a) b
  exact_mod_cast hab

theorem coneMat_smul (g : Matrix.SpecialLinearGroup (Fin n) ℤ) (A : posDefCone n) :
    coneMat (g • A) = slReal g * coneMat A * (slReal g)ᵀ := rfl

/-- **The translates of the open Siegel set cover the cone.** -/
theorem openSiegelSet_cover (n : ℕ) :
    (⋃ g : Matrix.SpecialLinearGroup (Fin n) ℤ, g • openSiegelSet n 3 2)
      = (Set.univ : Set (posDefCone n)) := by
  refine Set.eq_univ_of_forall fun A => ?_
  obtain ⟨g₀, J, hdet, hJ, hS⟩ := exists_siegel_inOrbit_det_one (coneMat_posDef A)
  set g : Matrix.SpecialLinearGroup (Fin n) ℤ :=
    ⟨g₀ᵀ, by rw [Matrix.det_transpose]; exact hdet⟩ with hgdef
  have hslReal : slReal g = (g₀.map (fun z : ℤ => (z : ℝ)))ᵀ := rfl
  have hact : coneMat (g • A) = J.form := by
    rw [coneMat_smul, hslReal, Matrix.transpose_transpose, hJ]
  have hmem : g • A ∈ openSiegelSet n 3 2 := by
    constructor
    · intro i j hij
      rw [jacOf_d_of_form (J := J) (by rw [hact])]
      have h1 := hS.1 i j hij
      have h2 := J.pos j
      linarith
    · intro i j
      rw [jacOf_U_of_form (J := J) (by rw [hact])]
      have h1 := hS.2 i j
      linarith
  refine Set.mem_iUnion.2 ⟨g⁻¹, ?_⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
  exact hmem

/-- **The overlap set of the open Siegel set is finite.** -/
theorem meetSet_openSiegelSet_finite (n : ℕ) (t u : ℝ) (ht : 1 ≤ t) :
    (meetSet (G := Matrix.SpecialLinearGroup (Fin n) ℤ) (openSiegelSet n t u)).Finite := by
  classical
  have hSfin := siegel_finiteness n t u ht
  have hinj : Function.Injective
      (fun g : Matrix.SpecialLinearGroup (Fin n) ℤ => (slReal g)ᵀ) := by
    intro g h hgh
    exact slReal_injective (Matrix.transpose_injective hgh)
  refine Set.Finite.subset (Set.Finite.preimage (fun g _ h _ hgh => hinj hgh) hSfin) ?_
  rintro g ⟨B, hB1, hB2⟩
  have hA : g⁻¹ • B ∈ openSiegelSet n t u := Set.mem_smul_set_iff_inv_smul_mem.1 hB1
  set A : posDefCone n := g⁻¹ • B with hAdef
  have hBA : B = g • A := by rw [hAdef, smul_inv_smul]
  refine ⟨⟨(g : Matrix (Fin n) (Fin n) ℤ)ᵀ, ?_, fun a b => rfl⟩,
    jacOf A, jacOf B, isSiegel_of_mem_openSiegelSet hA, isSiegel_of_mem_openSiegelSet hB2, ?_⟩
  · refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
    rw [Matrix.det_transpose, Matrix.SpecialLinearGroup.det_coe]
    exact isUnit_one
  · rw [jacOf_form A, jacOf_form B, hBA, coneMat_smul, Matrix.transpose_transpose]

/-- **`SL(n, ℤ)` is finitely presented.**  Reduction theory supplies the open connected fundamental
set with finitely many overlaps that Macbeath's criterion consumes. -/
theorem isFinitelyPresented_specialLinearGroup (n : ℕ) :
    IsFinitelyPresented (Matrix.SpecialLinearGroup (Fin n) ℤ) :=
  isFinitelyPresented_specialLinearGroup_of_siegel
    (isOpen_openSiegelSet n 3 2)
    (openSiegelSet_nonempty (by norm_num) (by norm_num))
    (isPreconnected_openSiegelSet n 3 2)
    (openSiegelSet_cover n)
    (meetSet_openSiegelSet_finite n 3 2 (by norm_num))

end GaloisForLFunctions.HTGeometry
