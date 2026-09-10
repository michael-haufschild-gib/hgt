import GaloisForLFunctions.HTGeometry.PointedLorentzSpinFactor

/-!
# Unipotent Lorentz actions and convex imaginary orbit domains

Kukol, arXiv:2609.10214, Lemma 3.1, Proposition 3.2 and Lemma 5.1 supply
three mechanisms: negative generator squares, convex tube slices and free actions
on the nonzero light-coordinate locus. These mechanisms hold for every real
inner-product space. The exact stabilizer also describes all degenerate loci.

The action preserves the Lorentz quadratic and the pairwise transverse minors.
Positive exponential coordinates construct strict future states; every transverse
coordinate on a fixed such mass shell belongs to one orbit. The convexity result
applies to arbitrary simultaneous families of tube constraints. This establishes
the coordinate geometry used in the paper, without asserting its Stein theorem.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev KukolLightCone (E : Type*) := ℝ × ℝ × E

def kukolQuadratic (x : KukolLightCone E) : ℝ :=
  x.1 * x.2.1 - inner ℝ x.2.2 x.2.2

def kukolAction (u : E) (x : KukolLightCone E) : KukolLightCone E :=
  (x.1, x.2.1 + 2 * inner ℝ x.2.2 u + x.1 * inner ℝ u u, x.2.2 + x.1 • u)

def kukolGenerator (u : E) (x : KukolLightCone E) : KukolLightCone E :=
  (0, 2 * inner ℝ x.2.2 u, x.1 • u)

def kukolFuture : Set (KukolLightCone E) := {x | 0 < x.1 ∧ 0 < kukolQuadratic x}

theorem kukolAction_zero (x : KukolLightCone E) : kukolAction 0 x = x := by
  simp [kukolAction]

theorem kukolAction_add (u v : E) (x : KukolLightCone E) :
    kukolAction (u + v) x = kukolAction u (kukolAction v x) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · simp only [kukolAction, inner_add_left, inner_add_right, inner_smul_left,
      RCLike.conj_to_real, real_inner_comm v u]
    ring
  · simp only [kukolAction, smul_add]
    abel

theorem kukolQuadratic_action (u : E) (x : KukolLightCone E) :
    kukolQuadratic (kukolAction u x) = kukolQuadratic x := by
  simp only [kukolQuadratic, kukolAction, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real, real_inner_comm u x.2.2]
  ring

theorem kukolAction_future_iff (u : E) (x : KukolLightCone E) :
    kukolAction u x ∈ kukolFuture ↔ x ∈ kukolFuture := by
  simp only [kukolFuture, Set.mem_setOf_eq, kukolQuadratic_action]
  rfl

theorem kukolQuadratic_generator (u : E) (x : KukolLightCone E) :
    kukolQuadratic (kukolGenerator u x) = -(x.1 ^ 2 * ‖u‖ ^ 2) := by
  simp only [kukolQuadratic, kukolGenerator, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, real_inner_self_eq_norm_sq]
  ring

theorem kukolQuadratic_generator_nonpos (u : E) (x : KukolLightCone E) :
    kukolQuadratic (kukolGenerator u x) ≤ 0 := by
  rw [kukolQuadratic_generator]
  exact neg_nonpos.mpr (mul_nonneg (sq_nonneg _) (sq_nonneg _))

theorem kukolQuadratic_generator_neg_iff (u : E) (x : KukolLightCone E) :
    kukolQuadratic (kukolGenerator u x) < 0 ↔ x.1 ≠ 0 ∧ u ≠ 0 := by
  rw [kukolQuadratic_generator, neg_neg_iff_pos]
  constructor
  · intro h
    constructor
    · intro hx
      simp [hx] at h
    · intro hu
      simp [hu] at h
  · rintro ⟨hx, hu⟩
    exact mul_pos (sq_pos_of_ne_zero hx) (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hu))

theorem kukolGenerator_cube (u : E) (x : KukolLightCone E) :
    kukolGenerator u (kukolGenerator u (kukolGenerator u x)) = 0 := by
  simp [kukolGenerator]

def kukolPairInvariant (x y : KukolLightCone E) : E := x.1 • y.2.2 - y.1 • x.2.2

theorem kukolPairInvariant_action (u : E) (x y : KukolLightCone E) :
    kukolPairInvariant (kukolAction u x) (kukolAction u y) = kukolPairInvariant x y := by
  simp only [kukolPairInvariant, kukolAction, smul_add, smul_smul]
  rw [mul_comm y.1 x.1]
  abel

theorem kukolAction_stabilizer_iff (u : E) (x : KukolLightCone E) :
    kukolAction u x = x ↔ (u = 0 ∨ x.1 = 0 ∧ inner ℝ x.2.2 u = 0) := by
  constructor
  · intro h
    have hv : x.1 • u = 0 := by
      have := congrArg (fun z : KukolLightCone E => z.2.2) h
      simpa [kukolAction] using this
    rcases smul_eq_zero.mp hv with ha | hu
    · right
      refine ⟨ha, ?_⟩
      have := congrArg (fun z : KukolLightCone E => z.2.1) h
      simp only [kukolAction, ha, zero_mul, add_zero] at this
      linarith
    · exact Or.inl hu
  · rintro (rfl | ⟨ha, hb⟩)
    · exact kukolAction_zero x
    · rcases x with ⟨a,b,z⟩
      simp_all [kukolAction]

/-- Every positive-mass light-cone state is constructed without an admissibility premise. -/
def kukolStrictState (r s : ℝ) (z : E) : KukolLightCone E :=
  (Real.exp r, (inner ℝ z z + Real.exp s) / Real.exp r, z)

theorem kukolQuadratic_strictState (r s : ℝ) (z : E) :
    kukolQuadratic (kukolStrictState r s z) = Real.exp s := by
  unfold kukolQuadratic kukolStrictState
  dsimp
  field_simp
  ring

theorem kukolStrictState_mem_future (r s : ℝ) (z : E) :
    kukolStrictState r s z ∈ kukolFuture := by
  exact ⟨Real.exp_pos r, by rw [kukolQuadratic_strictState]; exact Real.exp_pos s⟩

theorem kukolAction_strictState_free (u : E) (r s : ℝ) (z : E) :
    kukolAction u (kukolStrictState r s z) = kukolStrictState r s z ↔ u = 0 := by
  rw [kukolAction_stabilizer_iff]
  simp [kukolStrictState, Real.exp_ne_zero]

theorem kukolAction_strictState (u : E) (r s : ℝ) (z : E) :
    kukolAction u (kukolStrictState r s z) = kukolStrictState r s (z + Real.exp r • u) := by
  apply Prod.ext
  · rfl
  apply Prod.ext
  · simp only [kukolAction, kukolStrictState, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, RCLike.conj_to_real, real_inner_comm u z]
    field_simp
    ring
  · rfl

theorem kukolStrictState_transitive (r s : ℝ) (z w : E) :
    kukolAction ((Real.exp r)⁻¹ • (w - z)) (kukolStrictState r s z) =
      kukolStrictState r s w := by
  rw [kukolAction_strictState]
  congr 1
  rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero r), one_smul]
  abel

/-- Imaginary part of the complexified unipotent action on `v + i w`. -/
def kukolImaginaryAction (u : E) (v w : KukolLightCone E) : KukolLightCone E :=
  (w.1, w.2.1 + 2 * inner ℝ v.2.2 u - w.1 * inner ℝ u u,
    w.2.2 + v.1 • u)

/-- The tube margin is a concave quadratic in the imaginary group parameter. -/
theorem kukolQuadratic_imaginaryAction (u : E) (v w : KukolLightCone E) :
    kukolQuadratic (kukolImaginaryAction u v w) = kukolQuadratic w +
      2 * (w.1 * inner ℝ v.2.2 u - v.1 * inner ℝ w.2.2 u) -
      (w.1 ^ 2 + v.1 ^ 2) * ‖u‖ ^ 2 := by
  simp only [kukolQuadratic, kukolImaginaryAction, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    real_inner_comm u w.2.2, real_inner_self_eq_norm_sq]
  ring

/-- Exact positive defect underlying convexity of every imaginary orbit slice. -/
theorem kukolImaginaryAction_convex_defect (u z : E) (v w : KukolLightCone E) (t : ℝ) :
    kukolQuadratic (kukolImaginaryAction (t • u + (1-t) • z) v w) =
      t * kukolQuadratic (kukolImaginaryAction u v w) +
      (1-t) * kukolQuadratic (kukolImaginaryAction z v w) +
      t * (1-t) * (w.1 ^ 2 + v.1 ^ 2) * ‖u-z‖ ^ 2 := by
  simp only [kukolQuadratic, kukolImaginaryAction, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    ← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right]
  rw [real_inner_comm z u, real_inner_comm u w.2.2, real_inner_comm z w.2.2]
  ring

/-- Tube admissibility along imaginary unipotent parameters is convex. -/
theorem kukolImaginaryAction_convex (v w : KukolLightCone E) :
    Convex ℝ {u : E | kukolImaginaryAction u v w ∈ kukolFuture} := by
  intro u hu z hz a b ha hb hab
  refine ⟨hu.1, ?_⟩
  have hb' : b = 1-a := by linarith
  change 0 < kukolQuadratic (kukolImaginaryAction (a • u + b • z) v w)
  rw [hb', kukolImaginaryAction_convex_defect, ← hb']
  have hmix : 0 < a * kukolQuadratic (kukolImaginaryAction u v w) +
      b * kukolQuadratic (kukolImaginaryAction z v w) := by
    rcases eq_or_lt_of_le ha with hzero | hpos
    · have : 0 < b := by linarith
      exact add_pos_of_nonneg_of_pos (mul_nonneg ha hu.2.le) (mul_pos this hz.2)
    · exact add_pos_of_pos_of_nonneg (mul_pos hpos hu.2) (mul_nonneg hb hz.2.le)
  exact add_pos_of_pos_of_nonneg hmix
    (mul_nonneg (mul_nonneg (mul_nonneg ha hb) (add_nonneg (sq_nonneg _) (sq_nonneg _)))
      (sq_nonneg _))

/-- Arbitrary simultaneous tube constraints still have a convex parameter domain. -/
theorem kukolImaginaryAction_family_convex {ι : Type*} (v w : ι → KukolLightCone E) :
    Convex ℝ {u : E | ∀ i, kukolImaginaryAction u (v i) (w i) ∈ kukolFuture} := by
  intro u hu z hz a b ha hb hab i
  exact kukolImaginaryAction_convex (v i) (w i) (hu i) (hz i) ha hb hab

/-- The domain controlling simultaneous complexified orbits is connected when nonempty. -/
theorem kukolImaginaryAction_family_preconnected {ι : Type*} (v w : ι → KukolLightCone E) :
    IsPreconnected {u : E | ∀ i, kukolImaginaryAction u (v i) (w i) ∈ kukolFuture} :=
  (kukolImaginaryAction_family_convex v w).isPreconnected

end GaloisForLFunctions.HTGeometry
