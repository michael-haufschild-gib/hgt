import GaloisForLFunctions.HTGeometry.HankelIncidenceCech
import GaloisForLFunctions.HTGeometry.HankelIncidenceChartRing
import GaloisForLFunctions.HTGeometry.TwistedCechSlice

/-!
# The slice `v_0 = 1` of the Hankel incidence variety

The affine chart `x_0 = 1` of the projective secant variety is resolved by the slice
`Y_1 = Proj(B_j / (v_0 - 1))` of the incidence variety.  The element `v_0 - 1` has degree zero,
and it is regular on every chart of `B_j`: on the chart `z_0 ≠ 0` the quotient of `K[z][z_0⁻¹][v]`
by the triangular equations is a domain (the iterated substitution embeds it), and `v_0 - 1` survives
there because the substitutions have no constant terms; the moment shift `σ_t` fixes `v_0` and
carries the chart `z_0 ≠ 0` to `G(t) ≠ 0`.  Hence the twisted Čech complexes of the slice are exact
(`twCech_slice_exactAt`).

* `HTGeometry.constantCoeff_triangularElim`.
* `HTGeometry.SliceReg`, `HTGeometry.sliceReg_chartForm`.
* `HTGeometry.sliceIdeal`, `HTGeometry.sliceGrading`, `HTGeometry.sliceCech_exactAt`.
-/

namespace HTGeometry

open MvPolynomial

/-! ## Constant terms survive triangular substitution -/

section Const

variable {R : Type*} [CommRing R] {m : ℕ} {φ : Fin m → MvPolynomial (Fin m) R}

theorem constantCoeff_substOneVar {i : Fin m} {ψ : MvPolynomial (Fin m) R}
    (hψ : constantCoeff ψ = 0) (g : MvPolynomial (Fin m) R) :
    constantCoeff (substOneVar i ψ g) = constantCoeff g := by
  induction g using MvPolynomial.induction_on with
  | C c => simp [substOneVar]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p l hp =>
    rw [map_mul, map_mul, hp, map_mul, substOneVar, aeval_X, constantCoeff_X]
    split_ifs
    · rw [hψ]
    · rw [constantCoeff_X]

/-- **Triangular substitutions without constant terms preserve constant terms.** -/
theorem constantCoeff_triangularElim (hφ : ∀ i, constantCoeff (φ i) = 0) (j : ℕ)
    (g : MvPolynomial (Fin m) R) : constantCoeff (triangularElim φ j g) = constantCoeff g := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [triangularElim]
    split_ifs with h
    · rw [AlgHom.comp_apply, constantCoeff_substOneVar (hφ _), ih]
    · exact ih

end Const

variable {K : Type*} [Field K] {r N : ℕ}

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-! ## The slice element is regular on the charts -/

variable (K r N) in
/-- The slice element `v_0 - 1`. -/
noncomputable def sliceElem : IncRing K r N := vAt K r N 0 - 1

variable (K r N) in
/-- **Regularity of the slice element on the chart `f ≠ 0` of `B_j`.** -/
def SliceReg (f : IncRing K r N) (j : ℕ) : Prop :=
  ∀ x : IncRing K r N, (∃ a : ℕ, f ^ a * (sliceElem K r N * x) ∈ hankelIdeal K r N j) →
    ∃ b : ℕ, f ^ b * x ∈ hankelIdeal K r N j

theorem SliceReg.mul {f : IncRing K r N} {j : ℕ} (hf : SliceReg K r N f j) (c : IncRing K r N) :
    SliceReg K r N (f * c) j := by
  rintro x ⟨a, ha⟩
  obtain ⟨b, hb⟩ := hf (c ^ a * x) ⟨a, by
    have : f ^ a * (sliceElem K r N * (c ^ a * x)) = (f * c) ^ a * (sliceElem K r N * x) := by ring
    rw [this]
    exact ha⟩
  refine ⟨a + b, ?_⟩
  have : (f * c) ^ (a + b) * x = f ^ a * c ^ b * (f ^ b * (c ^ a * x)) := by ring
  rw [this]
  exact Ideal.mul_mem_left _ _ hb

theorem chartTail_constantCoeff (l : Fin N) : constantCoeff (chartTail K r N l) = 0 := by
  rw [chartTail]
  split_ifs
  · simp [map_neg, map_sum]
  · exact map_zero _

theorem vAt_zero_of_pos (hN : 0 < N) : vAt K r N 0 = vv K r N ⟨0, hN⟩ := by
  rw [vAt, dif_pos hN]

/-- **On the chart `z_0 ≠ 0`, the slice element is regular modulo the Hankel equations.** -/
theorem sliceReg_zero {j : ℕ} (hj : j + r ≤ N) : SliceReg K r N (zv K r N 0) j := by
  rintro x ⟨a, ha⟩
  rcases Nat.eq_zero_or_pos N with hN | hN
  · refine ⟨a, ?_⟩
    have h0 : sliceElem K r N = -1 := by
      rw [sliceElem, vAt, dif_neg (by omega), zero_sub]
    rw [h0, neg_one_mul, mul_neg] at ha
    exact neg_mem_iff.mp ha
  have h1 := chartMap_mem_triangularIdeal hj ha
  have hz : chartMap K r N (zv K r N 0) = chartUnit K r N := chartMap_zv 0
  have hs : chartMap K r N (sliceElem K r N) = MvPolynomial.X ⟨0, hN⟩ - 1 := by
    rw [sliceElem, map_sub, map_one, chartMap_vAt, dif_pos hN]
  rw [map_mul, map_pow, map_mul, hz, hs] at h1
  have h2 := (Ideal.unit_mul_mem_iff_mem _ ((isUnit_chartUnit (K := K) (r := r) (N := N)).pow a)).mp h1
  -- the quotient by the triangular equations is a domain
  haveI : IsDomain (MvPolynomial (Fin N) (ChartBase K r) ⧸ triangularIdeal (chartTail K r N) j) := by
    have hinj : Function.Injective (Ideal.Quotient.lift (triangularIdeal (chartTail K r N) j)
        (triangularElim (chartTail K r N) j).toRingHom (fun g hg => by
          rw [← ker_triangularElim chartTail_isTriangular] at hg; exact hg)) := by
      rw [injective_iff_map_eq_zero]
      intro y hy
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Ideal.Quotient.lift_mk] at hy
      rw [Ideal.Quotient.eq_zero_iff_mem, ← ker_triangularElim chartTail_isTriangular]
      exact hy
    exact hinj.isDomain
  have hne : Ideal.Quotient.mk (triangularIdeal (chartTail K r N) j) (MvPolynomial.X ⟨0, hN⟩ - 1) ≠ 0 := by
    intro h0
    rw [Ideal.Quotient.eq_zero_iff_mem, ← ker_triangularElim chartTail_isTriangular,
      RingHom.mem_ker] at h0
    have h3 := congrArg MvPolynomial.constantCoeff h0
    rw [constantCoeff_triangularElim (fun l => chartTail_constantCoeff l), map_sub, constantCoeff_X,
      map_one, map_zero, zero_sub] at h3
    exact one_ne_zero (neg_eq_zero.mp h3)
  have h3 : chartMap K r N x ∈ triangularIdeal (chartTail K r N) j := by
    have hprod : Ideal.Quotient.mk (triangularIdeal (chartTail K r N) j) (MvPolynomial.X ⟨0, hN⟩ - 1)
        * Ideal.Quotient.mk (triangularIdeal (chartTail K r N) j) (chartMap K r N x) = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact h2
    exact Ideal.Quotient.eq_zero_iff_mem.mp ((mul_eq_zero.mp hprod).resolve_left hne)
  have h4 := triangularIdeal_le_map hj h3
  rw [chartMap, ← Ideal.map_map] at h4
  haveI hloc : IsLocalization
      ((Submonoid.powers (MvPolynomial.X (0 : Fin (r + 1)) : MvPolynomial (Fin (r + 1)) K)).map
        (MvPolynomial.C (σ := Fin N))) (MvPolynomial (Fin N) (ChartBase K r)) :=
    MvPolynomial.isLocalization _ _
  obtain ⟨m, hm, hmem⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    ((Submonoid.powers (MvPolynomial.X (0 : Fin (r + 1)) : MvPolynomial (Fin (r + 1)) K)).map
      (MvPolynomial.C (σ := Fin N))) (MvPolynomial (Fin N) (ChartBase K r)) _ _).mp h4
  obtain ⟨_, ⟨b, rfl⟩, rfl⟩ := Submonoid.mem_map.mp hm
  refine ⟨b, ?_⟩
  obtain ⟨y, hy, hyx⟩ :=
    (Ideal.mem_map_iff_of_surjective (incEquiv K r N).toRingHom (incEquiv K r N).surjective).mp hmem
  have hyx2 : incEquiv K r N y
      = MvPolynomial.C (MvPolynomial.X 0 ^ b) * incEquiv K r N x := hyx
  have hyx' : y = zv K r N 0 ^ b * x := by
    apply (incEquiv K r N).injective
    rw [hyx2]
    simp only [map_mul, map_pow, incEquiv_zv]
  rwa [← hyx']

theorem momentShift_sliceElem (t : K) : momentShift K r N t (sliceElem K r N) = sliceElem K r N := by
  rw [sliceElem, map_sub, map_one]
  congr 1
  rw [vAt]
  split_ifs with hN
  · rw [momentShift_vv, pow_zero, ← pow_zero (Polynomial.X : Polynomial (IncRing K r N)), momentPair_X_pow',
      vAt, dif_pos hN]
  · exact map_zero _

/-- **Regularity of the slice element on every evaluation chart.** -/
theorem sliceReg_chartForm (t : K) {j : ℕ} (hj : j + r ≤ N) :
    SliceReg K r N (chartForm K r N t) j := by
  rintro x ⟨a, ha⟩
  have h1 := momentShift_mem_hankelIdeal (-t) hj ha
  rw [map_mul, map_pow, map_mul, momentShift_sliceElem, ← momentShift_zv_zero t,
    momentShift_inv] at h1
  obtain ⟨b, hb⟩ := sliceReg_zero hj _ ⟨a, h1⟩
  refine ⟨b, ?_⟩
  have h3 := momentShift_mem_hankelIdeal t hj hb
  rwa [map_mul, map_pow, momentShift_zv_zero, momentShift_inv'] at h3

theorem sliceReg_wProd {j : ℕ} (hj : j + r ≤ N) {s : Finset (Fin (r + 1))} (hs : s.Nonempty) :
    SliceReg K r N (wProd (fun k => chartForm K r N (node K k)) s) j := by
  classical
  obtain ⟨k, hk⟩ := hs
  rw [wProd, ← Finset.mul_prod_erase s _ hk]
  exact (sliceReg_chartForm (node K k) hj).mul _

/-! ## The slice ring -/

open GaloisForLFunctions.HTGeometry.StableCoordinate.HomogeneousQuotient

attribute [local instance] MvPolynomial.weightedGradedAlgebra

local notation "𝒵" => projGrading K (Fin (r + 1)) (Fin N)

theorem sliceElem_mem : sliceElem K r N ∈ 𝒵 0 :=
  Submodule.sub_mem _ (vAt_mem 0) (by simpa using algebraMap_mem (r := r) (N := N) (1 : K))

variable (K r N) in
/-- **The slice ideal** `(ℓ_0, …, ℓ_{j-1}, v_0 - 1)`. -/
noncomputable def sliceIdeal (j : ℕ) : Ideal (IncRing K r N) :=
  hankelIdeal K r N j ⊔ Ideal.span {sliceElem K r N}

theorem sliceIdeal_isHomogeneous (j : ℕ) : (sliceIdeal K r N j).IsHomogeneous 𝒵 :=
  (hankelIdeal_isHomogeneous j).sup (Ideal.homogeneous_span _ _ (by
    rintro _ rfl
    exact ⟨0, sliceElem_mem⟩))

variable (K r N) in
/-- The slice ring `B_j / (v_0 - 1)`. -/
abbrev SliceQuot (j : ℕ) := IncRing K r N ⧸ sliceIdeal K r N j

variable (K r N) in
/-- The grading of the slice ring. -/
noncomputable abbrev sliceGrading (j : ℕ) : ℕ → Submodule K (SliceQuot K r N j) :=
  piece 𝒵 (sliceIdeal K r N j)

noncomputable instance sliceGradedAlgebra (j : ℕ) : GradedAlgebra (sliceGrading K r N j) :=
  gradedAlgebra 𝒵 _ (sliceIdeal_isHomogeneous j)

section SliceMaps

variable (j : ℕ)

variable (K r N) in
/-- `B_j → B_j / (v_0 - 1)`. -/
noncomputable def sliceMap : HankelQuot K r N j →+* SliceQuot K r N j :=
  Ideal.Quotient.factor le_sup_left

theorem sliceMap_mk (x : IncRing K r N) :
    sliceMap K r N j (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl

variable (K r N) in
/-- The evaluation charts of the slice. -/
noncomputable def sChart (k : Fin (r + 1)) : SliceQuot K r N j :=
  Ideal.Quotient.mk _ (chartForm K r N (node K k))

theorem sChart_mem (k : Fin (r + 1)) : sChart K r N j k ∈ sliceGrading K r N j 1 :=
  mk_mem_piece 𝒵 _ (chartForm_mem _)

theorem sliceMap_qChart (k : Fin (r + 1)) : sliceMap K r N j (qChart K r N j k) = sChart K r N j k :=
  rfl

theorem sliceMap_mem {i : ℕ} {x : HankelQuot K r N j} (hx : x ∈ quotGrading K r N j i) :
    sliceMap K r N j x ∈ sliceGrading K r N j i := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact mk_mem_piece 𝒵 _ ha

theorem sliceMap_lift {i : ℕ} {x' : SliceQuot K r N j} (hx' : x' ∈ sliceGrading K r N j i) :
    ∃ x ∈ quotGrading K r N j i, sliceMap K r N j x = x' := by
  obtain ⟨a, ha, rfl⟩ := hx'
  exact ⟨Ideal.Quotient.mk _ a, mk_mem_piece 𝒵 _ ha, rfl⟩

variable (K r N) in
/-- The slice element in `B_j`. -/
noncomputable def qSlice : HankelQuot K r N j := Ideal.Quotient.mk _ (sliceElem K r N)

theorem qSlice_mem : qSlice K r N j ∈ quotGrading K r N j 0 := mk_mem_piece 𝒵 _ sliceElem_mem

theorem sliceMap_qSlice : sliceMap K r N j (qSlice K r N j) = 0 := by
  rw [qSlice, sliceMap_mk, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sup_right (Ideal.subset_span rfl)

/-- **The kernel of `B_j → B_j/(v_0 - 1)` is generated by `v_0 - 1`.** -/
theorem sliceMap_ker (x : HankelQuot K r N j) (hx : sliceMap K r N j x = 0) :
    ∃ z, x = qSlice K r N j * z := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [sliceMap_mk, Ideal.Quotient.eq_zero_iff_mem, sliceIdeal] at hx
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
  refine ⟨Ideal.Quotient.mk _ d, ?_⟩
  rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hb, zero_add, map_mul, qSlice, mul_comm]

/-- **The slice element is a nonzerodivisor on the chart localizations.** -/
theorem algebraMap_qSlice_mem_nonZeroDivisors {f : IncRing K r N} (hf : SliceReg K r N f j)
    {f' : HankelQuot K r N j} (hf' : f' = Ideal.Quotient.mk _ f) :
    algebraMap (HankelQuot K r N j) (Localization.Away f') (qSlice K r N j) ∈ nonZeroDivisors _ := by
  subst hf'
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  obtain ⟨⟨x', ⟨_, m, rfl⟩⟩, hxy⟩ := IsLocalization.surj
    (Submonoid.powers (Ideal.Quotient.mk (hankelIdeal K r N j) f)) y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x'
  simp only at hxy
  have h1 : algebraMap (HankelQuot K r N j) (Localization.Away (Ideal.Quotient.mk (hankelIdeal K r N j) f))
      (Ideal.Quotient.mk _ (x * sliceElem K r N)) = 0 := by
    rw [map_mul, map_mul, ← hxy, mul_right_comm,
      show Ideal.Quotient.mk (hankelIdeal K r N j) (sliceElem K r N) = qSlice K r N j from rfl, hy,
      zero_mul]
  obtain ⟨⟨_, a, rfl⟩, ha⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (Ideal.Quotient.mk (hankelIdeal K r N j) f)) _ _).mp h1
  simp only [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at ha
  obtain ⟨b, hb⟩ := hf x ⟨a, by rwa [mul_comm (sliceElem K r N)]⟩
  have h2 : algebraMap (HankelQuot K r N j) (Localization.Away (Ideal.Quotient.mk (hankelIdeal K r N j) f))
      (Ideal.Quotient.mk _ x) = 0 := by
    refine (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Ideal.Quotient.mk (hankelIdeal K r N j) f)) _ _).mpr
        ⟨⟨_, b, rfl⟩, ?_⟩
    simp only [← map_pow, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact hb
  have hu : IsUnit (algebraMap (HankelQuot K r N j)
      (Localization.Away (Ideal.Quotient.mk (hankelIdeal K r N j) f))
      (Ideal.Quotient.mk (hankelIdeal K r N j) f ^ m)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit _).pow m
  rw [h2] at hxy
  exact (hu.mul_left_eq_zero).mp hxy

end SliceMaps

variable (K r N) in
/-- The twisted Čech datum of `𝒪(-e)` on the slice `Proj(B_j/(v_0 - 1))`. -/
noncomputable abbrev sliceCech (j e : ℕ) : FinsetCechDatum (Fin (r + 1)) :=
  twCech (sliceGrading K r N j) (sChart K r N j) (sChart_mem j) e

/-- **The slice is Čech-exact**: for `j + r ≤ N` and `e ≤ p`, the augmented Čech complex of
`𝒪(-e)` on `Proj(B_j/(v_0 - 1))` is exact in degree `p`. -/
theorem sliceCech_exactAt [CharZero K] {j : ℕ} (hj : j + r ≤ N) {e p : ℕ} (hep : e ≤ p) :
    (sliceCech K r N j e).ExactAt p :=
  twCech_slice_exactAt (𝒜 := quotGrading K r N j) (𝒜' := sliceGrading K r N j) (w := qChart K r N j)
    (w' := sChart K r N j) (sliceMap K r N j) (sliceMap_qChart j) (fun _ _ hx => sliceMap_mem j hx)
    (qChart_mem j) (sChart_mem j) (qSlice_mem j) (sliceMap_qSlice j) (sliceMap_ker j)
    (fun _ _ hx' => sliceMap_lift j hx')
    (fun s hs => algebraMap_qSlice_mem_nonZeroDivisors j (sliceReg_wProd hj hs) (wProd_qChart j s))
    e p (hankelCech_exactAt (K := K) j hj e (p + 1) (by omega)) (hankelCech_exactAt (K := K) j hj e p hep)

end HTGeometry
