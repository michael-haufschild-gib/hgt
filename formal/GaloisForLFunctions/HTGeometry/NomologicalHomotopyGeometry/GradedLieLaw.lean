import Mathlib

/-!
# Graded Lie algebras and the three-storey law

A `ℤ`-graded Lie algebra over `ℝ` with zero differential is an internal direct sum of components
`L_i` with a bilinear bracket `[L_i, L_j] ⊆ L_{i+j}` which is graded antisymmetric,
`[u, v] = −(−1)^{ij} [v, u]`, and satisfies the graded Jacobi identity on homogeneous elements
(`GradedLieAlgebra`); strict morphisms preserve degrees and brackets (`GradedLieHom`).  The lower
central series is `F¹ = L`, `F^{k+1} = [L, F^k]`.

The **three-storey law** has homogeneous generators `x ∈ L₋₁`, `y ∈ L₋₂`, `w ∈ L₋₃` with the single
bracket `[x, y] = w`, all other generator brackets zero (`threeStoreyLaw`).  Every nested bracket
contains `w` after its inner bracket and so vanishes, which gives the Jacobi identity; the lower
central series is `F¹ = L`, `F² = ℝw`, `F³ = 0`, so the law is finite, complete and nilpotent.
-/

namespace GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry

/-- The Koszul sign `(−1)^{ij}`. -/
noncomputable def koszulSign (i j : ℤ) : ℝ := (-1 : ℝ) ^ (i * j)

theorem koszulSign_comm (i j : ℤ) : koszulSign i j = koszulSign j i := by
  rw [koszulSign, koszulSign, mul_comm]

theorem koszulSign_mul_self (i j : ℤ) : koszulSign i j * koszulSign i j = 1 := by
  rw [koszulSign, ← mul_zpow]
  norm_num

/-- A `ℤ`-graded Lie algebra over `ℝ` with zero differential: an internal direct sum of
components with a bilinear bracket of degree zero which is graded antisymmetric and satisfies
the graded Jacobi identity on homogeneous elements. -/
structure GradedLieAlgebra (V : Type*) [AddCommGroup V] [Module ℝ V] where
  comp : ℤ → Submodule ℝ V
  isInternal : DirectSum.IsInternal comp
  bracket : V →ₗ[ℝ] V →ₗ[ℝ] V
  bracket_mem : ∀ {i j : ℤ} {u v : V}, u ∈ comp i → v ∈ comp j → bracket u v ∈ comp (i + j)
  antisymm : ∀ {i j : ℤ} {u v : V}, u ∈ comp i → v ∈ comp j →
    bracket u v = -(koszulSign i j • bracket v u)
  jacobi : ∀ {i j k : ℤ} {u v w : V}, u ∈ comp i → v ∈ comp j → w ∈ comp k →
    koszulSign i k • bracket u (bracket v w) + koszulSign j i • bracket v (bracket w u) +
      koszulSign k j • bracket w (bracket u v) = 0

namespace GradedLieAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (G : GradedLieAlgebra V)

/-- The lower central series `F¹ = V`, `F^{k+1} = [V, F^k]`. -/
def lowerCentral : ℕ → Submodule ℝ V
  | 0 => ⊤
  | k + 1 => Submodule.span ℝ {z | ∃ u v, v ∈ lowerCentral k ∧ z = G.bracket u v}

/-- Nilpotence: some term of the lower central series vanishes. -/
def IsNilpotent : Prop := ∃ k, G.lowerCentral k = ⊥

end GradedLieAlgebra

/-- A strict morphism of graded Lie algebras: a degree-preserving linear map preserving brackets
(both differentials being zero). -/
structure GradedLieHom {V V' : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup V']
    [Module ℝ V'] (G : GradedLieAlgebra V) (G' : GradedLieAlgebra V') where
  toLinearMap : V →ₗ[ℝ] V'
  map_comp : ∀ {i : ℤ} {u : V}, u ∈ G.comp i → toLinearMap u ∈ G'.comp i
  map_bracket : ∀ u v : V, toLinearMap (G.bracket u v) = G'.bracket (toLinearMap u) (toLinearMap v)

/-! ## The three-storey law -/

/-- Coordinates `(a, b, c) ↔ a x + b y + c w`. -/
abbrev ThreeStorey := ℝ × ℝ × ℝ

def gx : ThreeStorey := (1, 0, 0)
def gy : ThreeStorey := (0, 1, 0)
def gw : ThreeStorey := (0, 0, 1)

/-- The bracket `[u, v] = (u_x v_y − u_y v_x) w`. -/
def threeStoreyBracket : ThreeStorey →ₗ[ℝ] ThreeStorey →ₗ[ℝ] ThreeStorey :=
  LinearMap.mk₂ ℝ (fun u v => (0, 0, u.1 * v.2.1 - u.2.1 * v.1))
    (fun u u' v => by ext <;> simp; ring)
    (fun c u v => by ext <;> simp; ring)
    (fun u v v' => by ext <;> simp; ring)
    (fun c u v => by ext <;> simp; ring)

@[simp] theorem threeStoreyBracket_apply (u v : ThreeStorey) :
    threeStoreyBracket u v = (0, 0, u.1 * v.2.1 - u.2.1 * v.1) := rfl

theorem threeStoreyBracket_x_y : threeStoreyBracket gx gy = gw := by
  simp [gx, gy, gw]


/-- The components: `L₋₁ = ℝx`, `L₋₂ = ℝy`, `L₋₃ = ℝw`, all others zero. -/
def threeStoreyComp (i : ℤ) : Submodule ℝ ThreeStorey :=
  if i = -1 then ℝ ∙ gx else if i = -2 then ℝ ∙ gy else if i = -3 then ℝ ∙ gw else ⊥

theorem mem_span_gx {u : ThreeStorey} : u ∈ ℝ ∙ gx ↔ u.2.1 = 0 ∧ u.2.2 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    simp [gx]
  · rintro ⟨h1, h2⟩
    exact ⟨u.1, by ext <;> simp [gx, h1, h2]⟩

theorem mem_span_gy {u : ThreeStorey} : u ∈ ℝ ∙ gy ↔ u.1 = 0 ∧ u.2.2 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    simp [gy]
  · rintro ⟨h1, h2⟩
    exact ⟨u.2.1, by ext <;> simp [gy, h1, h2]⟩

theorem mem_span_gw {u : ThreeStorey} : u ∈ ℝ ∙ gw ↔ u.1 = 0 ∧ u.2.1 = 0 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    simp [gw]
  · rintro ⟨h1, h2⟩
    exact ⟨u.2.2, by ext <;> simp [gw, h1, h2]⟩

theorem threeStoreyComp_neg_one : threeStoreyComp (-1) = ℝ ∙ gx := by simp [threeStoreyComp]
theorem threeStoreyComp_neg_two : threeStoreyComp (-2) = ℝ ∙ gy := by simp [threeStoreyComp]
theorem threeStoreyComp_neg_three : threeStoreyComp (-3) = ℝ ∙ gw := by simp [threeStoreyComp]

theorem threeStoreyComp_of_ne {i : ℤ} (h1 : i ≠ -1) (h2 : i ≠ -2) (h3 : i ≠ -3) :
    threeStoreyComp i = ⊥ := by
  simp [threeStoreyComp, h1, h2, h3]

/-- Membership in a component, by cases on the degree. -/
theorem mem_threeStoreyComp {i : ℤ} {u : ThreeStorey} :
    u ∈ threeStoreyComp i ↔
      (i = -1 ∧ u.2.1 = 0 ∧ u.2.2 = 0) ∨ (i = -2 ∧ u.1 = 0 ∧ u.2.2 = 0) ∨
        (i = -3 ∧ u.1 = 0 ∧ u.2.1 = 0) ∨ u = 0 := by
  by_cases h1 : i = -1
  · subst h1
    rw [threeStoreyComp_neg_one, mem_span_gx]
    constructor
    · intro h; exact Or.inl ⟨rfl, h⟩
    · rintro (⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | rfl)
      · exact h
      · norm_num at h
      · norm_num at h
      · simp
  by_cases h2 : i = -2
  · subst h2
    rw [threeStoreyComp_neg_two, mem_span_gy]
    constructor
    · intro h; exact Or.inr (Or.inl ⟨rfl, h⟩)
    · rintro (⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -⟩ | rfl)
      · norm_num at h
      · exact h
      · norm_num at h
      · simp
  by_cases h3 : i = -3
  · subst h3
    rw [threeStoreyComp_neg_three, mem_span_gw]
    constructor
    · intro h; exact Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))
    · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩ | rfl)
      · norm_num at h
      · norm_num at h
      · exact h
      · simp
  rw [threeStoreyComp_of_ne h1 h2 h3, Submodule.mem_bot]
  constructor
  · intro h; exact Or.inr (Or.inr (Or.inr h))
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h)
    · exact absurd h h1
    · exact absurd h h2
    · exact absurd h h3
    · exact h


theorem threeStorey_iSup_eq_top : iSup threeStoreyComp = ⊤ := by
  rw [eq_top_iff]
  intro u _
  have hu : u = u.1 • gx + u.2.1 • gy + u.2.2 • gw := by ext <;> simp [gx, gy, gw]
  rw [hu]
  refine add_mem (add_mem ?_ ?_) ?_
  · exact Submodule.mem_iSup_of_mem (-1) (by
      rw [threeStoreyComp_neg_one]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · exact Submodule.mem_iSup_of_mem (-2) (by
      rw [threeStoreyComp_neg_two]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  · exact Submodule.mem_iSup_of_mem (-3) (by
      rw [threeStoreyComp_neg_three]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

theorem threeStorey_iSupIndep : iSupIndep threeStoreyComp := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro u hu hsup
  rcases mem_threeStoreyComp.mp hu with ⟨rfl, h2, h3⟩ | ⟨rfl, h1, h3⟩ | ⟨rfl, h1, h2⟩ | h
  · have hle : (⨆ j, ⨆ (_ : j ≠ -1), threeStoreyComp j) ≤
        LinearMap.ker (LinearMap.fst ℝ ℝ (ℝ × ℝ)) := by
      refine iSup₂_le fun j hj v hv => ?_
      rcases mem_threeStoreyComp.mp hv with ⟨rfl, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | rfl
      · exact absurd rfl hj
      · simp [h]
      · simp [h]
      · simp
    have h1 : u.1 = 0 := by simpa using hle hsup
    ext <;> simp [h1, h2, h3]
  · have hle : (⨆ j, ⨆ (_ : j ≠ -2), threeStoreyComp j) ≤
        LinearMap.ker ((LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))) := by
      refine iSup₂_le fun j hj v hv => ?_
      rcases mem_threeStoreyComp.mp hv with ⟨-, h, -⟩ | ⟨rfl, -⟩ | ⟨-, -, h⟩ | rfl
      · simp [h]
      · exact absurd rfl hj
      · simp [h]
      · simp
    have h2 : u.2.1 = 0 := by simpa using hle hsup
    ext <;> simp [h1, h2, h3]
  · have hle : (⨆ j, ⨆ (_ : j ≠ -3), threeStoreyComp j) ≤
        LinearMap.ker ((LinearMap.snd ℝ ℝ ℝ).comp (LinearMap.snd ℝ ℝ (ℝ × ℝ))) := by
      refine iSup₂_le fun j hj v hv => ?_
      rcases mem_threeStoreyComp.mp hv with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨rfl, -⟩ | rfl
      · simp [h]
      · simp [h]
      · exact absurd rfl hj
      · simp
    have h3 : u.2.2 = 0 := by simpa using hle hsup
    ext <;> simp [h1, h2, h3]
  · exact h

theorem threeStoreyBracket_mem_neg_three (u v : ThreeStorey) :
    threeStoreyBracket u v ∈ threeStoreyComp (-3) := by
  rw [threeStoreyComp_neg_three, mem_span_gw]
  simp

/-- The bracket vanishes unless its arguments have degrees `−1, −2` in some order. -/
theorem threeStoreyBracket_eq_zero_of_degrees {i j : ℤ} {u v : ThreeStorey}
    (hu : u ∈ threeStoreyComp i) (hv : v ∈ threeStoreyComp j) (h : i + j ≠ -3) :
    threeStoreyBracket u v = 0 := by
  rw [threeStoreyBracket_apply]
  rcases mem_threeStoreyComp.mp hu with
      ⟨rfl, hu2, hu3⟩ | ⟨rfl, hu1, hu3⟩ | ⟨rfl, hu1, hu2⟩ | rfl <;>
    rcases mem_threeStoreyComp.mp hv with
      ⟨rfl, hv2, hv3⟩ | ⟨rfl, hv1, hv3⟩ | ⟨rfl, hv1, hv2⟩ | rfl <;>
    simp_all

theorem threeStoreyBracket_comm_of_ne_zero {i j : ℤ} {u v : ThreeStorey}
    (hu : u ∈ threeStoreyComp i) (hv : v ∈ threeStoreyComp j) (h : threeStoreyBracket u v ≠ 0) :
    koszulSign i j = 1 := by
  rcases mem_threeStoreyComp.mp hu with
      ⟨rfl, hu2, hu3⟩ | ⟨rfl, hu1, hu3⟩ | ⟨rfl, hu1, hu2⟩ | rfl <;>
    rcases mem_threeStoreyComp.mp hv with
      ⟨rfl, hv2, hv3⟩ | ⟨rfl, hv1, hv3⟩ | ⟨rfl, hv1, hv2⟩ | rfl <;>
    simp_all [koszulSign] <;> norm_num

/-- **The three-storey law** `x ∈ L₋₁, y ∈ L₋₂, w ∈ L₋₃, [x, y] = w`, all other generator brackets
zero, as a graded Lie algebra. -/
noncomputable def threeStoreyLaw : GradedLieAlgebra ThreeStorey where
  comp := threeStoreyComp
  isInternal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top threeStorey_iSupIndep
    threeStorey_iSup_eq_top
  bracket := threeStoreyBracket
  bracket_mem := by
    intro i j u v hu hv
    by_cases h : i + j = -3
    · rw [h]; exact threeStoreyBracket_mem_neg_three u v
    · rw [threeStoreyBracket_eq_zero_of_degrees hu hv h]; exact Submodule.zero_mem _
  antisymm := by
    intro i j u v hu hv
    by_cases h : threeStoreyBracket v u = 0
    · have h' : threeStoreyBracket u v = 0 := by
        rw [threeStoreyBracket_apply] at h ⊢
        simp only [Prod.mk_eq_zero, true_and] at h ⊢
        linarith
      rw [h, h', smul_zero, neg_zero]
    · rw [koszulSign_comm, threeStoreyBracket_comm_of_ne_zero hv hu h, one_smul,
        threeStoreyBracket_apply, threeStoreyBracket_apply]
      refine Prod.ext (by simp) (Prod.ext (by simp) ?_)
      simp only [Prod.snd_neg]
      ring
  jacobi := by
    intro i j k u v w _ _ _
    simp

theorem threeStoreyLaw_bracket : threeStoreyLaw.bracket = threeStoreyBracket := rfl
theorem threeStoreyLaw_comp : threeStoreyLaw.comp = threeStoreyComp := rfl

/-- The lower central series of the three-storey law: `F² = ℝw`. -/
theorem threeStoreyLaw_lowerCentral_one : threeStoreyLaw.lowerCentral 1 = ℝ ∙ gw := by
  apply le_antisymm
  · rw [GradedLieAlgebra.lowerCentral, Submodule.span_le]
    rintro _ ⟨u, v, -, rfl⟩
    exact (threeStoreyComp_neg_three ▸ threeStoreyBracket_mem_neg_three u v :)
  · rw [Submodule.span_singleton_le_iff_mem, GradedLieAlgebra.lowerCentral]
    exact Submodule.subset_span ⟨gx, gy, Submodule.mem_top, (threeStoreyBracket_x_y).symm⟩

/-- `F³ = 0`: the three-storey law is nilpotent. -/
theorem threeStoreyLaw_lowerCentral_two : threeStoreyLaw.lowerCentral 2 = ⊥ := by
  rw [GradedLieAlgebra.lowerCentral, threeStoreyLaw_lowerCentral_one, Submodule.span_eq_bot]
  rintro _ ⟨u, v, hv, rfl⟩
  rw [mem_span_gw] at hv
  simp [threeStoreyLaw_bracket, hv.1, hv.2]

theorem threeStoreyLaw_isNilpotent : threeStoreyLaw.IsNilpotent :=
  ⟨2, threeStoreyLaw_lowerCentral_two⟩

end GaloisForLFunctions.HTGeometry.NomologicalHomotopyGeometry
