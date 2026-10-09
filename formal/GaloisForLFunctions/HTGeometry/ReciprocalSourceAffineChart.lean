import GaloisForLFunctions.HTGeometry.ReciprocalSourceGeometry
import GaloisForLFunctions.HTGeometry.HankelSliceBirational
import GaloisForLFunctions.HTGeometry.HankelAffineChartDimension

/-!
# The source caustics at depth `s = 0`: the affine chart `h_0 = 1`

At depth `s = 0` the Hankel window is `h_0, …, h_{2m-2}` and `h_0 = 1` is the constant coefficient
of `Z²`.  So the caustic of corank `≥ k` in the unit-jet chart `z_1, …, z_{2m-2}` is the pull-back,
along the squaring automorphism `(12)`, of the affine chart `x_0 = 1` of the Hankel secant variety
`V(I_r)` (`r = m - k`).  Its coordinate ring is `K[x] / (I_r + (x_0 - 1))`, which has rational
singularities (`hankelChartRing_hasRationalSingularities`).  The Zariski tangent space of the chart at
a point `x` is `T_x V(I_r) ∩ {dx_0 = 0}`; the Euler vector `x` is tangent to the cone and has
`dx_0(x) = x_0 = 1`, so the chart is smooth of dimension `2r - 1` exactly off the next caustic, and
every direction is tangent on the next caustic.  For `k = m` the caustic is empty (`h_0 = 1`).

* `HTGeometry.unitWindow` : `x_0 ↦ 1`, `x_n ↦ X_{n-1}`; `HTGeometry.ker_unitWindow`.
* `HTGeometry.sourceIdeal0`, `HTGeometry.zeroLocus_sourceIdeal0`, `HTGeometry.sourceCaustic_zero_top`.
* `HTGeometry.sourceRing0Equiv`, `HTGeometry.sourceCaustic0_hasRationalSingularities`.
* `HTGeometry.ringKrullDim_sourceRing0` : dimension `2(m - k) - 1`, codimension `2k - 1`.
* `HTGeometry.sourceCaustic0_smooth_iff`.
-/

namespace HTGeometry

open MvPolynomial GaloisForLFunctions.HTGeometry

variable {K : Type} [Field K] {m : ℕ}

/-! ## The normalization `x_0 = 1` -/

variable (K m) in
/-- `x_0 ↦ 1`, `x_n ↦ X_{n-1}` (`n ≥ 1`). -/
noncomputable def unitWindow : MvPolynomial (Fin (2 * m - 1)) K →ₐ[K] MvPolynomial (Fin (2 * m - 2)) K :=
  aeval fun n => if h : (n : ℕ) = 0 then 1 else X ⟨n - 1, by omega⟩

/-- The point `(1, p)`. -/
def unitWindowPoint (p : Fin (2 * m - 2) → K) : Fin (2 * m - 1) → K :=
  fun n => if h : (n : ℕ) = 0 then 1 else p ⟨n - 1, by omega⟩

variable (K m) in
/-- The direction `(0, v)`. -/
def unitWindowDir : (Fin (2 * m - 2) → K) →ₗ[K] (Fin (2 * m - 1) → K) where
  toFun v n := if h : (n : ℕ) = 0 then 0 else v ⟨n - 1, by omega⟩
  map_add' v w := by
    funext n
    by_cases h : (n : ℕ) = 0 <;> simp [h]
  map_smul' c v := by
    funext n
    by_cases h : (n : ℕ) = 0 <;> simp [h]

/-- **The chain rule for `x_0 ↦ 1`.** -/
theorem unitWindow_chain (p v : Fin (2 * m - 2) → K) (g : MvPolynomial (Fin (2 * m - 1)) K) :
    eval p (unitWindow K m g) = eval (unitWindowPoint p) g ∧
      tangentDeriv p v (unitWindow K m g) = tangentDeriv (unitWindowPoint p) (unitWindowDir K m v) g := by
  have hcomp : (aeval (dualNumberPoint p v)).comp (unitWindow K m)
      = aeval (dualNumberPoint (unitWindowPoint p) (unitWindowDir K m v)) := by
    refine MvPolynomial.algHom_ext fun n => ?_
    rw [AlgHom.comp_apply, unitWindow, aeval_X, aeval_X]
    by_cases h : (n : ℕ) = 0
    · simp [h, dualNumberPoint, unitWindowPoint, unitWindowDir]
    · simp [h, dualNumberPoint, unitWindowPoint, unitWindowDir]
  have h := congrArg (fun φ : MvPolynomial (Fin (2 * m - 1)) K →ₐ[K] TrivSqZeroExt K K => φ g) hcomp
  simp only [AlgHom.comp_apply, aeval_dualNumberPoint] at h
  exact ⟨by simpa using congrArg TrivSqZeroExt.fst h, by simpa using congrArg TrivSqZeroExt.snd h⟩

variable (K m) in
/-- `X_q ↦ x_{q+1}`, a section of `unitWindow`. -/
noncomputable def unitWindowLift : MvPolynomial (Fin (2 * m - 2)) K →ₐ[K] MvPolynomial (Fin (2 * m - 1)) K :=
  rename fun q => ⟨q + 1, by omega⟩

theorem unitWindow_unitWindowLift (p : MvPolynomial (Fin (2 * m - 2)) K) :
    unitWindow K m (unitWindowLift K m p) = p := by
  have h : (unitWindow K m).comp (unitWindowLift K m) = AlgHom.id K _ := algHom_ext fun q => by
    rw [AlgHom.comp_apply, unitWindowLift, rename_X, unitWindow, aeval_X, dif_neg (by simp),
      AlgHom.id_apply]
    congr 1
  exact DFunLike.congr_fun h p

theorem unitWindow_surjective : Function.Surjective (unitWindow K m) :=
  fun p => ⟨unitWindowLift K m p, unitWindow_unitWindowLift p⟩

theorem firstMoment_eq_X (hm : 0 < m) : firstMoment K (2 * m - 1) = X ⟨0, by omega⟩ := by
  rw [firstMoment, dif_pos (by omega)]

theorem sub_unitWindowLift_mem (hm : 0 < m) (p : MvPolynomial (Fin (2 * m - 1)) K) :
    p - unitWindowLift K m (unitWindow K m p) ∈ Ideal.span {firstMoment K (2 * m - 1) - 1} := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    rw [← algebraMap_eq, AlgHom.commutes, AlgHom.commutes, sub_self]
    exact zero_mem _
  | add p q hp hq =>
    rw [map_add, map_add, add_sub_add_comm]
    exact Ideal.add_mem _ hp hq
  | mul_X p n hp =>
    have hn : X n - unitWindowLift K m (unitWindow K m (X n)) ∈ Ideal.span {firstMoment K (2 * m - 1) - 1} := by
      rw [unitWindow, aeval_X]
      by_cases h : (n : ℕ) = 0
      · rw [dif_pos h, map_one, firstMoment_eq_X hm, show n = ⟨0, by omega⟩ from Fin.ext h]
        exact Ideal.subset_span rfl
      · rw [dif_neg h, unitWindowLift, rename_X,
          show (⟨(⟨(n : ℕ) - 1, by omega⟩ : Fin (2 * m - 2)) + 1, by omega⟩ : Fin (2 * m - 1)) = n from
            Fin.ext (by simp; omega), sub_self]
        exact zero_mem _
    have e : p * X n - unitWindowLift K m (unitWindow K m (p * X n))
        = (p - unitWindowLift K m (unitWindow K m p)) * X n
          + unitWindowLift K m (unitWindow K m p) * (X n - unitWindowLift K m (unitWindow K m (X n))) := by
      rw [map_mul, map_mul]
      ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hp) (Ideal.mul_mem_left _ _ hn)

theorem unitWindow_firstMoment (hm : 0 < m) : unitWindow K m (firstMoment K (2 * m - 1) - 1) = 0 := by
  rw [firstMoment_eq_X hm, map_sub, map_one, unitWindow, aeval_X, dif_pos rfl, sub_self]

/-- **The kernel of `x_0 ↦ 1` is `(x_0 - 1)`.** -/
theorem ker_unitWindow (hm : 0 < m) :
    RingHom.ker (unitWindow K m) = Ideal.span {firstMoment K (2 * m - 1) - 1} := by
  refine le_antisymm (fun p hp => ?_) ((Ideal.span_singleton_le_iff_mem _).mpr
    (unitWindow_firstMoment hm))
  have h := sub_unitWindowLift_mem hm p
  rwa [RingHom.mem_ker.mp hp, map_zero, sub_zero] at h

variable (K m) in
/-- **`K[x] / (I + (x_0 - 1)) ≅ K[X] / I|_{x_0 = 1}`.** -/
noncomputable def unitQuotEquiv (hm : 0 < m) (I : Ideal (MvPolynomial (Fin (2 * m - 1)) K)) :
    (MvPolynomial (Fin (2 * m - 1)) K ⧸ (I ⊔ Ideal.span {firstMoment K (2 * m - 1) - 1}))
      ≃ₐ[K] MvPolynomial (Fin (2 * m - 2)) K ⧸ I.map (unitWindow K m) :=
  AlgEquiv.ofAlgHom
    (Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ K _).comp (unitWindow K m)) (fun a ha => by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp ha
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      rw [map_add, map_mul, unitWindow_firstMoment hm, mul_zero, add_zero]
      exact Ideal.mem_map_of_mem _ hb))
    (Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ K _).comp (unitWindowLift K m)) (fun a ha => by
      rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
      obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ unitWindow_surjective).mp ha
      have h := sub_unitWindowLift_mem hm b
      have e : unitWindowLift K m (unitWindow K m b) = b - (b - unitWindowLift K m (unitWindow K m b)) := by ring
      rw [e]
      exact Ideal.sub_mem _ (Ideal.mem_sup_left hb) (Ideal.mem_sup_right h)))
    (Ideal.Quotient.algHom_ext K (AlgHom.ext fun p => by
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.liftₐ_apply,
        Ideal.Quotient.lift_mk, AlgHom.coe_toRingHom, unitWindow_unitWindowLift, AlgHom.id_apply]))
    (Ideal.Quotient.algHom_ext K (AlgHom.ext fun p => by
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.liftₐ_apply,
        Ideal.Quotient.lift_mk, AlgHom.coe_toRingHom, AlgHom.id_apply]
      rw [Ideal.Quotient.eq]
      have h := sub_unitWindowLift_mem hm p
      rw [← neg_mem_iff, neg_sub] at h
      exact Ideal.mem_sup_right h))

/-! ## The source ideal at depth `0` -/

theorem coeff_zero_sq_unitJetAt {M : ℕ} (z : Fin M → K) : (unitJetAt z * unitJetAt z).coeff 0 = 1 := by
  rw [Polynomial.mul_coeff_zero, unitJetAt, Polynomial.coeff_map, coeff_unitJet, if_pos rfl, map_one,
    one_mul]

section Source

variable [CharZero K]

variable (K m) in
/-- **The caustic ideal in the source chart at depth `s = 0`** (rank `≤ r`): the secant ideal of the
window `h_0, …, h_{2m-2}` restricted to `h_0 = 1`, pulled back along the squaring automorphism `(12)`. -/
noncomputable def sourceIdeal0 (r : ℕ) : Ideal (MvPolynomial (Fin (2 * m - 2)) K) :=
  ((RHTower.finiteHankelSecantIdeal K (2 * m - 1) r).map (unitWindow K m)).map (jetSqEquiv K (2 * m - 2))

/-- The window point `(1, h_1, …, h_{2m-2})` of `z`. -/
noncomputable def windowPoint0 (z : Fin (2 * m - 2) → K) : Fin (2 * m - 1) → K :=
  unitWindowPoint (mapPoint (jetSqEquiv K (2 * m - 2)).toAlgHom z)

theorem windowPoint0_eq (z : Fin (2 * m - 2) → K) :
    windowPoint0 z = fun n : Fin (2 * m - 1) => (unitJetAt z * unitJetAt z).coeff n := by
  funext n
  rw [windowPoint0, unitWindowPoint]
  split_ifs with h
  · rw [h, coeff_zero_sq_unitJetAt]
  · change eval z (jetSqEquiv K (2 * m - 2) (X _)) = _
    rw [jetSqEquiv_X, ← coeff_sq_unitJetAt]
    congr 1
    simp only
    omega

theorem windowPoint0_zero (hm : 0 < m) (z : Fin (2 * m - 2) → K) : windowPoint0 z ⟨0, by omega⟩ = 1 := by
  rw [windowPoint0, unitWindowPoint, dif_pos rfl]

theorem eval_source0Gen (z : Fin (2 * m - 2) → K) (g : MvPolynomial (Fin (2 * m - 1)) K) :
    eval z (jetSqEquiv K (2 * m - 2) (unitWindow K m g)) = eval (windowPoint0 z) g := by
  have h := (tangentDeriv_map (jetSqEquiv K (2 * m - 2)).toAlgHom z 0 (unitWindow K m g)).1
  simp only [AlgEquiv.coe_toAlgHom] at h
  rw [h]
  exact (unitWindow_chain _ 0 g).1

theorem tangentDeriv_source0Gen (z v : Fin (2 * m - 2) → K) (g : MvPolynomial (Fin (2 * m - 1)) K) :
    tangentDeriv z v (jetSqEquiv K (2 * m - 2) (unitWindow K m g))
      = tangentDeriv (windowPoint0 z) (unitWindowDir K m (tangentEquiv (jetSqEquiv K (2 * m - 2)) z v)) g := by
  have h := (tangentDeriv_map (jetSqEquiv K (2 * m - 2)).toAlgHom z v (unitWindow K m g)).2
  simp only [AlgEquiv.coe_toAlgHom] at h
  rw [h]
  exact (unitWindow_chain _ _ g).2

theorem zero_sourceIdeal0_iff {r : ℕ} (z : Fin (2 * m - 2) → K) :
    (∀ g ∈ sourceIdeal0 K m r, eval z g = 0)
      ↔ ∀ g ∈ RHTower.finiteHankelSecantIdeal K (2 * m - 1) r, eval (windowPoint0 z) g = 0 := by
  constructor
  · intro h g hg
    rw [← eval_source0Gen]
    exact h _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hg))
  · intro h g hg
    have h1 : (RHTower.finiteHankelSecantIdeal K (2 * m - 1) r).map (unitWindow K m)
        ≤ (RingHom.ker (eval z)).comap (jetSqEquiv K (2 * m - 2)) :=
      Ideal.map_le_iff_le_comap.mpr fun x hx => by
        rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, eval_source0Gen]
        exact h x hx
    exact (Ideal.map_le_iff_le_comap.mpr h1) hg

/-- **The zero locus of the depth-`0` source ideal is the horizon caustic** (`1 ≤ k ≤ m`,
rank `r = m - k`). -/
theorem zeroLocus_sourceIdeal0 {k : ℕ} (hk : 1 ≤ k) (hkm : k ≤ m) (z : Fin (2 * m - 2) → K) :
    (∀ g ∈ sourceIdeal0 K m (m - k), eval z g = 0) ↔ z ∈ sourceCaustic 0 m k (2 * m - 2) := by
  rw [mem_sourceCaustic_iff (by omega) hkm, zero_sourceIdeal0_iff, windowPoint0_eq]
  have hsq := GaloisForLFunctions.HTGeometry.squareCatalecticant_iff (K := K) (m := m) (r := m - k)
    (by omega) (fun n : Fin (2 * m - 1) => (unitJetAt z * unitJetAt z).coeff n)
  have hmat : (Matrix.of fun i j : Fin m => (unitJetAt z * unitJetAt z).coeff (0 + i + j))
      = Matrix.of fun i j : Fin m => (fun n : Fin (2 * m - 1) => (unitJetAt z * unitJetAt z).coeff n)
          ⟨i + j, by have := i.isLt; have := j.isLt; omega⟩ := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, zero_add]
  rw [hmat, hsq.1, hsq.2]

/-- **At depth `0` the top caustic is empty**: the window contains `h_0 = 1`. -/
theorem sourceCaustic_zero_top (hm : 0 < m) : sourceCaustic (K := K) 0 m m (2 * m - 2) = ∅ := by
  ext z
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hz
  rw [mem_sourceCaustic_iff hm le_rfl, Nat.sub_self, Nat.le_zero, Matrix.rank,
    Submodule.finrank_eq_zero] at hz
  set A := Matrix.of fun i j : Fin m => (unitJetAt z * unitJetAt z).coeff (0 + i + j)
  have h1 : A.mulVecLin (Pi.single ⟨0, hm⟩ 1) ∈ LinearMap.range A.mulVecLin := ⟨_, rfl⟩
  rw [hz, Submodule.mem_bot, Matrix.mulVecLin_apply, Matrix.mulVec_single_one] at h1
  have h2 := congrFun h1 ⟨0, hm⟩
  simp only [A, Matrix.col_apply, Matrix.of_apply, add_zero, coeff_zero_sq_unitJetAt,
    Pi.zero_apply] at h2
  exact one_ne_zero h2

variable (K m) in
/-- **The coordinate ring of the depth-`0` source caustic** is the affine chart `x_0 = 1` of the
Hankel secant ring of the window. -/
noncomputable def sourceRing0Equiv (hm : 0 < m) (r : ℕ) :
    (MvPolynomial (Fin (2 * m - 2)) K ⧸ sourceIdeal0 K m r)
      ≃ₐ[K] (MvPolynomial (Fin (2 * m - 1)) K ⧸
        (RHTower.finiteHankelSecantIdeal K (2 * m - 1) r ⊔ Ideal.span {firstMoment K (2 * m - 1) - 1})) :=
  (Ideal.quotientEquivAlg _ _ (jetSqEquiv K (2 * m - 2)).symm (by
    rw [sourceIdeal0]
    exact (Ideal.map_of_equiv (jetSqEquiv K (2 * m - 2)).toRingEquiv).symm)).trans
  (unitQuotEquiv K m hm _).symm

/-- **The source caustics at depth `0` have rational singularities** (`1 ≤ k < m`). -/
theorem sourceCaustic0_hasRationalSingularities {k : ℕ} (hk : 1 ≤ k) (hkm : k + 1 ≤ m) :
    HasRationalSingularities K (MvPolynomial (Fin (2 * m - 2)) K ⧸ sourceIdeal0 K m (m - k)) :=
  (hankelChartRing_hasRationalSingularities K (N := 2 * m - 1) (r := m - k) (by omega)
    (by omega)).of_algEquiv (sourceRing0Equiv K m (by omega) (m - k)).symm

/-- **Codimension at depth `0`**: the caustic of corank `≥ k` (`1 ≤ k < m`) has dimension
`2(m - k) - 1` in the `(2m - 2)`-dimensional unit-jet chart, i.e. codimension `2k - 1`. -/
theorem ringKrullDim_sourceRing0 {k : ℕ} (hk : 1 ≤ k) (hkm : k + 1 ≤ m) :
    ringKrullDim (MvPolynomial (Fin (2 * m - 2)) K ⧸ sourceIdeal0 K m (m - k))
      = ((2 * (m - k) - 1 : ℕ) : WithBot ℕ∞) := by
  rw [ringKrullDim_eq_of_ringEquiv (sourceRing0Equiv K m (by omega) (m - k)).toRingEquiv,
    ringKrullDim_hankelAffineChart K (by omega) (by omega)]

end Source

/-! ## Singular loci at depth `0` -/

section Sing

/-- **Euler's relation for a determinant of variables**: at a zero `w`, the radial direction `w`
is tangent (over the dual numbers, `det((1 + ε) M(w)) = (1 + ε)^n det M(w) = 0`). -/
theorem tangentDeriv_det_X_self {N n : ℕ} (idx : Fin n → Fin n → Fin N) (w : Fin N → K)
    (hw : eval w (Matrix.det fun i j => (X (idx i j) : MvPolynomial (Fin N) K)) = 0) :
    tangentDeriv w w (Matrix.det fun i j => (X (idx i j) : MvPolynomial (Fin N) K)) = 0 := by
  set e : TrivSqZeroExt K K := TrivSqZeroExt.inl 1 + TrivSqZeroExt.inr 1
  have hM : (aeval (dualNumberPoint w w)).mapMatrix (fun i j => (X (idx i j) : MvPolynomial (Fin N) K))
      = e • (TrivSqZeroExt.inlHom K K).mapMatrix ((eval w).mapMatrix
          (fun i j => (X (idx i j) : MvPolynomial (Fin N) K))) := by
    refine Matrix.ext fun i j => ?_
    simp only [AlgHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.map_apply, aeval_X, eval_X,
      Matrix.smul_apply, smul_eq_mul, dualNumberPoint, e, TrivSqZeroExt.inlHom_apply]
    ext <;> simp
  have h0 : aeval (dualNumberPoint w w) (Matrix.det fun i j => (X (idx i j) : MvPolynomial (Fin N) K)) = 0 := by
    rw [AlgHom.map_det, hM, Matrix.det_smul, ← RingHom.map_det, ← RingHom.map_det, hw, map_zero,
      mul_zero]
  rw [aeval_dualNumberPoint, hw] at h0
  simpa using congrArg TrivSqZeroExt.snd h0

/-- **The radial direction is tangent to the secant cone.** -/
theorem self_mem_zariskiTangent_secant {N r : ℕ} (w : Fin N → K)
    (hw : ∀ g ∈ RHTower.finiteHankelSecantIdeal K N r, eval w g = 0) :
    w ∈ zariskiTangent (RHTower.finiteHankelSecantIdeal K N r) w := by
  rw [mem_zariskiTangent]
  intro g hg
  have hg' := hg
  rw [RHTower.finiteHankelSecantIdeal] at hg'
  induction hg' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hb, -, rfl⟩ := hx
    rw [RHTower.finiteHankelMaximalMinorOver] at hg ⊢
    exact tangentDeriv_det_X_self _ w (hw _ hg)
  | zero => exact tangentDeriv_zero' w w
  | add x y hx hy ihx ihy =>
    rw [tangentDeriv_add', ihx (by rw [RHTower.finiteHankelSecantIdeal]; exact hx),
      ihy (by rw [RHTower.finiteHankelSecantIdeal]; exact hy), add_zero]
  | smul a x hx ihx =>
    have hx' : x ∈ RHTower.finiteHankelSecantIdeal K N r := by
      rw [RHTower.finiteHankelSecantIdeal]; exact hx
    rw [smul_eq_mul, tangentDeriv_mul', ihx hx', hw x hx', mul_zero, zero_mul, add_zero]

theorem unitWindowDir_injective : Function.Injective (unitWindowDir K m) := by
  intro v v' h
  funext q
  have h1 := congrFun h ⟨q + 1, by omega⟩
  simp only [unitWindowDir, LinearMap.coe_mk, AddHom.coe_mk, Nat.add_one_ne_zero, ↓reduceDIte,
    Nat.add_sub_cancel] at h1
  exact h1

theorem unitWindowDir_zero (hm : 0 < m) (v : Fin (2 * m - 2) → K) : unitWindowDir K m v ⟨0, by omega⟩ = 0 := by
  simp [unitWindowDir]

/-- **Cutting by the hyperplane `{u_0 = 0}`** lowers the dimension of a subspace containing a vector
with `u_0 ≠ 0` by one. -/
theorem finrank_comap_unitWindowDir (hm : 0 < m) (U : Submodule K (Fin (2 * m - 1) → K))
    {w : Fin (2 * m - 1) → K} (hwU : w ∈ U) (hw0 : w ⟨0, by omega⟩ ≠ 0) :
    Module.finrank K (U.comap (unitWindowDir K m)) + 1 = Module.finrank K U := by
  set H := LinearMap.range (unitWindowDir K m)
  have h1 : Module.finrank K (U.comap (unitWindowDir K m)) = Module.finrank K (U ⊓ H : Submodule K _) := by
    rw [(Submodule.equivMapOfInjective _ unitWindowDir_injective (U.comap (unitWindowDir K m))).finrank_eq,
      Submodule.map_comap_eq, inf_comm]
  have h2 : Module.finrank K H = 2 * m - 2 := by
    rw [LinearMap.finrank_range_of_inj unitWindowDir_injective, Module.finrank_fin_fun]
  have hwH : w ∉ H := by
    rintro ⟨v, rfl⟩
    exact hw0 (unitWindowDir_zero hm v)
  have hlt : H < U ⊔ H := lt_of_le_of_ne le_sup_right fun h => hwH (h ▸ Submodule.mem_sup_left hwU)
  have h3 := Submodule.finrank_lt_finrank_of_lt hlt
  have h4 : Module.finrank K (U ⊔ H : Submodule K _) ≤ 2 * m - 1 := by
    have := Submodule.finrank_le (U ⊔ H)
    rwa [Module.finrank_fin_fun] at this
  have h5 := Submodule.finrank_sup_add_finrank_inf_eq U H
  omega

variable [CharZero K]

/-- **The tangent spaces of the depth-`0` source caustic**: the window tangent space at
`(1, h_1, …, h_{2m-2})`, cut by `dx_0 = 0` and pulled back along `(12)`. -/
theorem zariskiTangent_sourceIdeal0 {r : ℕ} (z : Fin (2 * m - 2) → K)
    (hz : ∀ g ∈ sourceIdeal0 K m r, eval z g = 0) :
    zariskiTangent (sourceIdeal0 K m r) z
      = (zariskiTangent (RHTower.finiteHankelSecantIdeal K (2 * m - 1) r) (windowPoint0 z)).comap
          ((unitWindowDir K m).comp (tangentEquiv (jetSqEquiv K (2 * m - 2)) z).toLinearMap) := by
  have hzw := (zero_sourceIdeal0_iff z).mp hz
  ext v
  rw [Submodule.mem_comap, sourceIdeal0, mem_zariskiTangent_map_iff _ _ hz]
  change _ ↔ ∀ g ∈ RHTower.finiteHankelSecantIdeal K (2 * m - 1) r, tangentDeriv (windowPoint0 z) _ g = 0
  constructor
  · intro h g hg
    have := h _ (Ideal.mem_map_of_mem (unitWindow K m) hg)
    rw [tangentDeriv_source0Gen] at this
    exact this
  · intro h g hg
    have hy : ∀ x ∈ (RHTower.finiteHankelSecantIdeal K (2 * m - 1) r).map (unitWindow K m),
        eval (mapPoint (jetSqEquiv K (2 * m - 2)).toAlgHom z) x = 0 := by
      intro x hx
      have h1 : (RHTower.finiteHankelSecantIdeal K (2 * m - 1) r).map (unitWindow K m)
          ≤ RingHom.ker (eval (mapPoint (jetSqEquiv K (2 * m - 2)).toAlgHom z)) :=
        Ideal.map_le_iff_le_comap.mpr fun x hx => by
          rw [Ideal.mem_comap, RingHom.mem_ker, (unitWindow_chain _ 0 x).1]
          exact hzw x hx
      exact h1 hx
    have hmem := (mem_zariskiTangent_map_iff (unitWindow K m)
      (RHTower.finiteHankelSecantIdeal K (2 * m - 1) r) hy
      (v := tangentEquiv (jetSqEquiv K (2 * m - 2)) z v)).mpr (fun g' hg' => by
        rw [(unitWindow_chain _ _ g').2]
        exact h g' hg')
    have h2 := (tangentDeriv_map (jetSqEquiv K (2 * m - 2)).toAlgHom z v g).2
    simp only [AlgEquiv.coe_toAlgHom] at h2
    rw [h2]
    exact hmem g hg

theorem finrank_zariskiTangent_sourceIdeal0 {r : ℕ} (hm : 0 < m) (z : Fin (2 * m - 2) → K)
    (hz : ∀ g ∈ sourceIdeal0 K m r, eval z g = 0) :
    Module.finrank K (zariskiTangent (sourceIdeal0 K m r) z) + 1
      = Module.finrank K (zariskiTangent (RHTower.finiteHankelSecantIdeal K (2 * m - 1) r)
          (windowPoint0 z)) := by
  rw [zariskiTangent_sourceIdeal0 z hz, Submodule.comap_comp,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  exact finrank_comap_unitWindowDir hm _ (self_mem_zariskiTangent_secant _ ((zero_sourceIdeal0_iff z).mp hz))
    (by rw [windowPoint0_zero hm]; exact one_ne_zero)

theorem sourceCaustic0_smooth_iff_aux {t : ℕ} (htm : 2 * (t + 1) < 2 * m - 1)
    (z : Fin (2 * m - 2) → K) (hz : ∀ g ∈ sourceIdeal0 K m (t + 1), eval z g = 0) :
    (Module.finrank K (zariskiTangent (sourceIdeal0 K m (t + 1)) z) = 2 * (t + 1) - 1
        ↔ ∃ g ∈ sourceIdeal0 K m t, eval z g ≠ 0) ∧
      ((∀ g ∈ sourceIdeal0 K m t, eval z g = 0) →
        zariskiTangent (sourceIdeal0 K m (t + 1)) z = ⊤) := by
  have hm : 0 < m := by omega
  have hw := (zero_sourceIdeal0_iff z).mp hz
  have hsm := GaloisForLFunctions.HTGeometry.hankel_smooth_iff K (N := 2 * m - 1) (s := t)
    htm (windowPoint0 z) hw
  have hdim := finrank_zariskiTangent_sourceIdeal0 hm z hz
  refine ⟨?_, fun hnext => ?_⟩
  · have e : Module.finrank K (zariskiTangent (sourceIdeal0 K m (t + 1)) z) = 2 * (t + 1) - 1
        ↔ Module.finrank K (zariskiTangent (RHTower.finiteHankelSecantIdeal K (2 * m - 1) (t + 1))
          (windowPoint0 z)) = 2 * (t + 1) := by omega
    rw [e, hsm.1]
    constructor
    · rintro ⟨g, hg, hne⟩
      by_contra hall
      push Not at hall
      exact hne (((zero_sourceIdeal0_iff z).mp hall) g hg)
    · rintro ⟨g, hg, hne⟩
      by_contra hall
      push Not at hall
      exact hne (((zero_sourceIdeal0_iff z).mpr hall) g hg)
  · rw [zariskiTangent_sourceIdeal0 z hz, hsm.2.1 ((zero_sourceIdeal0_iff z).mp hnext),
      Submodule.comap_top]

/-- **`Sing(C_k) = C_{k+1}` in the source chart at depth `0`** (`1 ≤ k < m`): a point of the caustic
has a tangent space of dimension `2(m - k) - 1` exactly when it lies off the next caustic; on the
next caustic every direction is tangent. -/
theorem sourceCaustic0_smooth_iff {k : ℕ} (hk : 1 ≤ k) (hkm : k + 1 ≤ m)
    (z : Fin (2 * m - 2) → K) (hz : ∀ g ∈ sourceIdeal0 K m (m - k), eval z g = 0) :
    (Module.finrank K (zariskiTangent (sourceIdeal0 K m (m - k)) z) = 2 * (m - k) - 1
        ↔ ∃ g ∈ sourceIdeal0 K m (m - k - 1), eval z g ≠ 0) ∧
      ((∀ g ∈ sourceIdeal0 K m (m - k - 1), eval z g = 0) →
        zariskiTangent (sourceIdeal0 K m (m - k)) z = ⊤) := by
  have h1 : m - k - 1 + 1 = m - k := by omega
  have h2 := sourceCaustic0_smooth_iff_aux (m := m) (t := m - k - 1) (by omega) z (by rwa [h1])
  rwa [h1] at h2

end Sing

end HTGeometry
