import GaloisForLFunctions.HTGeometry.FreeFamilyJetShift
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchwarzianJetDerivatives
import GaloisForLFunctions.HTGeometry.JacobianDomainCriterion
import GaloisForLFunctions.HTGeometry.FreeCoordinateBasisEquiv

/-!
# The Schwarzian coordinate system of a family of free differential indeterminates

For every member `Y_a` of a free differential family the Schwarzian `𝔖_a = S(Y_a)` involves only the
jets `Y_a', Y_a'', Y_a'''`, and its `k`-th jet involves only the `a`-packet jets of order between
one and `k+3`, with leading coefficient `1/Y_a'`.  The system consisting, for each `a`, of the first
three jets of `Y_a` followed by all jets of `𝔖_a` is therefore algebraically independent, and it
generates the whole field because the Schwarzian solves for the third jet.

So a free differential family and its Schwarzian family present the same field, in coordinates in
which the projective gauge moves only the first three jets of each packet.  The base is an
arbitrary differential field: the ambient derivation differentiates the coefficients as well as
shifting the jets.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {C ι : Type*} [Field C] [CharZero C] [Differential C]

/-! ## The ambient derivation lowers a coordinate derivation -/

/-- **The fresh-jet commutator.**  Differentiating in the jet `(b, m+1)` after the ambient
derivation equals ambient differentiation after that coordinate derivation, plus the coordinate
derivation in the jet `(b, m)`. -/
theorem freeCoordinateDerivation_deriv (b : ι) (m : ℕ) (f : FreeFamilyJetField C ι) :
    freeCoordinateDerivation C (ι × ℕ) (b, m + 1) (f′) =
      (freeCoordinateDerivation C (ι × ℕ) (b, m + 1) f)′ +
        freeCoordinateDerivation C (ι × ℕ) (b, m) f := by
  set W : FreeFamilyJetField C ι → FreeFamilyJetField C ι := fun g =>
    freeCoordinateDerivation C (ι × ℕ) (b, m + 1) (g′) -
      ((freeCoordinateDerivation C (ι × ℕ) (b, m + 1) g)′ +
        freeCoordinateDerivation C (ι × ℕ) (b, m) g) with hW
  have hadd : ∀ x y, W (x + y) = W x + W y := by
    intro x y
    simp only [hW, map_add]
    ring
  have hleib : ∀ x y, W (x * y) = (RingHom.id (FreeFamilyJetField C ι)) x * W y +
      (RingHom.id (FreeFamilyJetField C ι)) y * W x := by
    intro x y
    simp only [hW, RingHom.id_apply, Derivation.leibniz, smul_eq_mul, map_add]
    ring
  have hbase : ∀ c : C, W (algebraMap C (FreeFamilyJetField C ι) c) = 0 := by
    intro c
    simp only [hW, freeFamilyJetField_deriv_base, Derivation.map_algebraMap, map_zero,
      add_zero, sub_self]
  have hcoord : ∀ p : ι × ℕ, W (freeCoordinate C (ι × ℕ) p) = 0 := by
    rintro ⟨a, k⟩
    have hmid : (freeCoordinateDerivation C (ι × ℕ) (b, m + 1)
        (freeCoordinate C (ι × ℕ) (a, k)))′ = 0 := by
      by_cases h : ((a, k) : ι × ℕ) = (b, m + 1)
      · rw [h, freeCoordinateDerivation_freeCoordinate_self, freeFamilyJetField_deriv_one]
      · rw [freeCoordinateDerivation_freeCoordinate_of_ne h, map_zero]
    simp only [hW, freeCoordinate_deriv, hmid]
    by_cases hp : ((a, k) : ι × ℕ) = (b, m)
    · obtain ⟨rfl, rfl⟩ : a = b ∧ k = m := ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
      rw [freeCoordinateDerivation_freeCoordinate_self,
        freeCoordinateDerivation_freeCoordinate_self]
      ring
    · rw [freeCoordinateDerivation_freeCoordinate_of_ne (by
          intro hcon
          refine hp ?_
          have h1 : a = b := congrArg Prod.fst hcon
          have h2 : k + 1 = m + 1 := congrArg Prod.snd hcon
          exact Prod.ext h1 (by omega)),
        freeCoordinateDerivation_freeCoordinate_of_ne hp]
      ring
  have := eq_zero_of_twistedLeibniz W (RingHom.id _) hadd hleib hbase hcoord f
  rw [hW] at this
  simp only [sub_eq_zero] at this
  exact this

/-! ## The Schwarzian of a family member -/

/-- The Schwarzian of the `a`-th free family generator. -/
def familySchwarzian (C : Type*) {ι : Type*} [Field C] [Differential C] (a : ι) :
    FreeFamilyJetField C ι :=
  schwarzian (familyJet C a 0)

omit [CharZero C] in
theorem familyJet_deriv3 (a : ι) :
    (familyJet C a 0)′′′ = familyJet C a 3 := by
  rw [show ((familyJet C a 0)′′′ : FreeFamilyJetField C ι) = (((familyJet C a 0)′)′)′ from rfl,
    familyJet_deriv, familyJet_deriv, familyJet_deriv]

omit [CharZero C] in
theorem familyJet_deriv2 (a : ι) :
    (familyJet C a 0)′′ = familyJet C a 2 := by
  rw [show ((familyJet C a 0)′′ : FreeFamilyJetField C ι) = ((familyJet C a 0)′)′ from rfl,
    familyJet_deriv, familyJet_deriv]

omit [CharZero C] in
theorem familyJet_deriv1 (a : ι) :
    (familyJet C a 0)′ = familyJet C a 1 := familyJet_deriv a 0

/-- The Schwarzian solves for the third jet of its packet. -/
theorem familyJet_three_eq (a : ι) :
    familyJet C a 3 =
      familyJet C a 1 * familySchwarzian C a +
        (3 / 2 : FreeFamilyJetField C ι) * familyJet C a 2 ^ (2 : ℕ) / familyJet C a 1 := by
  have h1 : familyJet C a 1 ≠ (0 : FreeFamilyJetField C ι) := familyJet_ne_zero a 1
  rw [familySchwarzian, schwarzian, familyJet_deriv3, familyJet_deriv2, familyJet_deriv1]
  field_simp
  ring

/-! ## Packet support of the Schwarzian jets -/

/-- The coordinate set carrying the `k`-th Schwarzian jet of the `a`-packet. -/
def schwarzianSupport {ι : Type*} (a : ι) (k : ℕ) : Set (ι × ℕ) :=
  {p | p.1 = a ∧ 1 ≤ p.2 ∧ p.2 ≤ k + 3}

theorem schwarzianSupport_mono {a : ι} {k : ℕ} :
    schwarzianSupport a k ⊆ schwarzianSupport a (k + 1) := by
  rintro p ⟨h1, h2, h3⟩
  exact ⟨h1, h2, by omega⟩

omit [CharZero C] in
theorem familySchwarzian_mem (a : ι) :
    familySchwarzian C a ∈ freeCoordinateField C (ι × ℕ) (schwarzianSupport a 0) := by
  have h1 : familyJet C a 1 ∈ freeCoordinateField C (ι × ℕ) (schwarzianSupport a 0) :=
    IntermediateField.subset_adjoin _ _ ⟨(a, 1), ⟨rfl, by omega, by omega⟩, rfl⟩
  have h2 : familyJet C a 2 ∈ freeCoordinateField C (ι × ℕ) (schwarzianSupport a 0) :=
    IntermediateField.subset_adjoin _ _ ⟨(a, 2), ⟨rfl, by omega, by omega⟩, rfl⟩
  have h3 : familyJet C a 3 ∈ freeCoordinateField C (ι × ℕ) (schwarzianSupport a 0) :=
    IntermediateField.subset_adjoin _ _ ⟨(a, 3), ⟨rfl, by omega, by omega⟩, rfl⟩
  rw [familySchwarzian, schwarzian, familyJet_deriv3, familyJet_deriv2, familyJet_deriv1]
  exact sub_mem (div_mem h3 h1)
    (mul_mem (div_mem (by simp) (by simp)) (pow_mem (div_mem h2 h1) 2))

omit [CharZero C] in
theorem differentialJet_familySchwarzian_mem (a : ι) (k : ℕ) :
    differentialJet k (familySchwarzian C a) ∈
      freeCoordinateField C (ι × ℕ) (schwarzianSupport a k) := by
  induction k with
  | zero => simpa using familySchwarzian_mem a
  | succ k ih =>
      rw [differentialJet_succ]
      refine deriv_mem_freeCoordinateField ?_ schwarzianSupport_mono ih
      rintro p ⟨h1, h2, h3⟩
      exact ⟨h1, by omega, by omega⟩

omit [CharZero C] in
/-- Outside its packet support a Schwarzian jet is annihilated by the coordinate derivation. -/
theorem freeCoordinateDerivation_differentialJet_familySchwarzian_of_notMem
    (a : ι) (k : ℕ) {p : ι × ℕ} (hp : p ∉ schwarzianSupport a k) :
    freeCoordinateDerivation C (ι × ℕ) p (differentialJet k (familySchwarzian C a)) = 0 :=
  freeCoordinateField_le_commonKernel _ (differentialJet_familySchwarzian_mem a k) p hp

/-- **The leading jet derivative of a Schwarzian jet.** -/
theorem freeCoordinateDerivation_differentialJet_familySchwarzian_top (a : ι) :
    ∀ k : ℕ, freeCoordinateDerivation C (ι × ℕ) (a, k + 3)
        (differentialJet k (familySchwarzian C a)) = (familyJet C a 1)⁻¹ := by
  intro k
  induction k with
  | zero =>
      rw [differentialJet_zero]
      have h1 : freeCoordinateDerivation C (ι × ℕ) (a, 3) (familyJet C a 1) = 0 :=
        freeCoordinateDerivation_freeCoordinate_of_ne (by simp)
      have h2 : freeCoordinateDerivation C (ι × ℕ) (a, 3) (familyJet C a 2) = 0 :=
        freeCoordinateDerivation_freeCoordinate_of_ne (by simp)
      have h3 : freeCoordinateDerivation C (ι × ℕ) (a, 3) (familyJet C a 3) = 1 :=
        freeCoordinateDerivation_freeCoordinate_self (a, 3)
      have hne : familyJet C a 1 ≠ (0 : FreeFamilyJetField C ι) := familyJet_ne_zero a 1
      have hc : freeCoordinateDerivation C (ι × ℕ) (a, 3)
          (3 / 2 : FreeFamilyJetField C ι) = 0 := by
        have hnum : (3 / 2 : FreeFamilyJetField C ι) =
            algebraMap C (FreeFamilyJetField C ι) ((3 : C) / 2) := by
          rw [map_div₀]
          norm_num [map_ofNat]
        rw [hnum]
        exact Derivation.map_algebraMap _ _
      rw [familySchwarzian, schwarzian, familyJet_deriv3, familyJet_deriv2, familyJet_deriv1,
        map_sub, Derivation.leibniz_div, h1, h3, Derivation.leibniz, Derivation.leibniz_pow,
        Derivation.leibniz_div, h1, h2, hc]
      simp only [smul_eq_mul, smul_zero, mul_zero, sub_zero, mul_one]
      field_simp
      ring
  | succ k ih =>
      rw [show k + 1 + 3 = (k + 3) + 1 from by omega, differentialJet_succ,
        freeCoordinateDerivation_deriv,
        freeCoordinateDerivation_differentialJet_familySchwarzian_of_notMem a k
          (p := (a, k + 3 + 1)) (by
            rintro ⟨-, -, h⟩
            omega),
        map_zero, zero_add, ih]

/-! ## The family Schwarzian coordinate system -/

/-- The Schwarzian coordinate system of the family: for each packet the first three jets of the
generator followed by every jet of its Schwarzian. -/
def familySchwarzianSystem (C : Type*) {ι : Type*} [Field C] [Differential C] :
    ι × ℕ → FreeFamilyJetField C ι := fun p =>
  if p.2 < 3 then familyJet C p.1 p.2 else differentialJet (p.2 - 3) (familySchwarzian C p.1)

omit [CharZero C] in
theorem familySchwarzianSystem_of_lt {p : ι × ℕ} (hp : p.2 < 3) :
    familySchwarzianSystem C p = familyJet C p.1 p.2 := if_pos hp

omit [CharZero C] in
theorem familySchwarzianSystem_of_ge {p : ι × ℕ} (hp : 3 ≤ p.2) :
    familySchwarzianSystem C p = differentialJet (p.2 - 3) (familySchwarzian C p.1) :=
  if_neg (by omega)

omit [CharZero C] in
/-- Coordinate derivations of one packet annihilate the Schwarzian system of another. -/
theorem freeCoordinateDerivation_familySchwarzianSystem_of_ne_fst {q p : ι × ℕ}
    (h : q.1 ≠ p.1) :
    freeCoordinateDerivation C (ι × ℕ) q (familySchwarzianSystem C p) = 0 := by
  by_cases hp : p.2 < 3
  · rw [familySchwarzianSystem_of_lt hp, familyJet]
    exact freeCoordinateDerivation_freeCoordinate_of_ne (by
      intro hcon
      exact h (congrArg Prod.fst hcon).symm)
  · rw [familySchwarzianSystem_of_ge (by omega)]
    refine freeCoordinateDerivation_differentialJet_familySchwarzian_of_notMem _ _ ?_
    rintro ⟨h1, -, -⟩
    exact h h1

omit [CharZero C] in
/-- Within a packet the Schwarzian system is upper triangular. -/
theorem freeCoordinateDerivation_familySchwarzianSystem_of_gt {a : ι} {i j : ℕ} (hij : j < i) :
    freeCoordinateDerivation C (ι × ℕ) (a, i) (familySchwarzianSystem C (a, j)) = 0 := by
  by_cases hj : j < 3
  · rw [familySchwarzianSystem_of_lt (by exact hj), familyJet]
    exact freeCoordinateDerivation_freeCoordinate_of_ne (by
      intro hcon
      have := congrArg Prod.snd hcon
      simp at this
      omega)
  · rw [familySchwarzianSystem_of_ge (by omega)]
    refine freeCoordinateDerivation_differentialJet_familySchwarzian_of_notMem _ _ ?_
    rintro ⟨-, -, h3⟩
    simp only at h3
    omega

/-- The diagonal of the packet Jacobian. -/
theorem freeCoordinateDerivation_familySchwarzianSystem_diag (a : ι) (j : ℕ) :
    freeCoordinateDerivation C (ι × ℕ) (a, j) (familySchwarzianSystem C (a, j)) =
      if j < 3 then 1 else (familyJet C a 1)⁻¹ := by
  by_cases hj : j < 3
  · rw [familySchwarzianSystem_of_lt (by exact hj), if_pos hj, familyJet]
    exact freeCoordinateDerivation_freeCoordinate_self (a, j)
  · rw [familySchwarzianSystem_of_ge (by omega), if_neg hj]
    have h := freeCoordinateDerivation_differentialJet_familySchwarzian_top (C := C) a (j - 3)
    rwa [show j - 3 + 3 = j from by omega] at h

/-! ## Algebraic independence -/

/-- The Jacobian of one packet's initial block. -/
def familySchwarzianJacobian (C : Type*) {ι : Type*} [Field C] [Differential C] (a : ι) (N : ℕ) :
    Matrix (Fin (3 + N)) (Fin (3 + N)) (FreeFamilyJetField C ι) :=
  Matrix.of fun i j =>
    freeCoordinateDerivation C (ι × ℕ) (a, (i : ℕ)) (familySchwarzianSystem C (a, (j : ℕ)))

theorem familySchwarzianJacobian_det_ne_zero (a : ι) (N : ℕ) :
    (familySchwarzianJacobian C a N).det ≠ 0 := by
  have htri : (familySchwarzianJacobian C a N).BlockTriangular id := by
    intro i j hji
    exact freeCoordinateDerivation_familySchwarzianSystem_of_gt hji
  rw [Matrix.det_of_upperTriangular htri]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rw [familySchwarzianJacobian, Matrix.of_apply,
    freeCoordinateDerivation_familySchwarzianSystem_diag]
  by_cases hi : (i : ℕ) < 3
  · rw [if_pos hi]; exact one_ne_zero
  · rw [if_neg hi]; exact inv_ne_zero (familyJet_ne_zero a 1)

theorem algebraicIndependent_familySchwarzianBlock [DecidableEq ι] (J : Finset ι) (N : ℕ) :
    AlgebraicIndependent C
      (fun p : Fin (3 + N) × J => familySchwarzianSystem C ((p.2 : ι), (p.1 : ℕ))) := by
  classical
  refine algebraicIndependent_of_domain_jacobian
    (K := C) (R := FreeFamilyJetField C ι)
    (fun p : Fin (3 + N) × J => familySchwarzianSystem C ((p.2 : ι), (p.1 : ℕ)))
    (fun p f => freeCoordinateDerivation C (ι × ℕ) ((p.2 : ι), (p.1 : ℕ)) f)
    (fun p a b => map_add _ a b)
    (fun p a b => by
      rw [Derivation.leibniz]
      simp only [smul_eq_mul])
    (fun p c => Derivation.map_algebraMap _ c)
    (Matrix.blockDiagonal fun a : J => familySchwarzianJacobian C (a : ι) N) ?_ ?_
  · rw [Matrix.det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun a _ => familySchwarzianJacobian_det_ne_zero _ N
  · rintro ⟨i, a⟩ ⟨j, b⟩
    rw [Matrix.blockDiagonal_apply]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, familySchwarzianJacobian, Matrix.of_apply]
    · rw [if_neg hab]
      refine (freeCoordinateDerivation_familySchwarzianSystem_of_ne_fst (C := C)
        (q := ((a : ι), (i : ℕ))) (p := ((b : ι), (j : ℕ))) ?_)
      intro hcon
      exact hab (Subtype.ext hcon)

/-- **The family Schwarzian coordinate system is algebraically independent.** -/
theorem algebraicIndependent_familySchwarzianSystem :
    AlgebraicIndependent C (familySchwarzianSystem C (ι := ι)) := by
  classical
  refine algebraicIndependent_of_finite_type fun t ht => ?_
  obtain ⟨b, hb⟩ := (ht.image Prod.snd).bddAbove
  set N := b + 1 with hN
  set J : Finset ι := ht.toFinset.image Prod.fst with hJ
  have hlt : ∀ p : t, ((p : ι × ℕ).2) < 3 + N := by
    intro p
    have := hb ⟨(p : ι × ℕ), p.2, rfl⟩
    omega
  have hmemJ : ∀ p : t, ((p : ι × ℕ).1) ∈ J := by
    intro p
    rw [hJ]
    exact Finset.mem_image.2 ⟨(p : ι × ℕ), by simp [ht.mem_toFinset], rfl⟩
  have hinj : Function.Injective
      (fun p : t => ((⟨(p : ι × ℕ).2, hlt p⟩ : Fin (3 + N)),
        (⟨(p : ι × ℕ).1, hmemJ p⟩ : J))) := by
    intro p q hpq
    have h1 := congrArg Prod.fst hpq
    have h2 := congrArg Prod.snd hpq
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact congrArg Subtype.val h2
    · exact congrArg Fin.val h1
  have h := (algebraicIndependent_familySchwarzianBlock (C := C) J N).comp _ hinj
  exact h

/-! ## Generation -/

/-- **The family Schwarzian coordinate system generates the free family jet field.** -/
theorem familySchwarzianSystem_adjoin_eq_top :
    IntermediateField.adjoin C (Set.range (familySchwarzianSystem C (ι := ι))) = ⊤ := by
  classical
  set L := IntermediateField.adjoin C (Set.range (familySchwarzianSystem C (ι := ι))) with hL
  have hmem : ∀ p : ι × ℕ, familySchwarzianSystem C p ∈ L := fun p =>
    IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩
  have hjetmem : ∀ (a : ι) (m : ℕ), m < 3 → familyJet C a m ∈ L := by
    intro a m hm
    have h := hmem (a, m)
    rwa [familySchwarzianSystem_of_lt (by exact hm)] at h
  have hschwmem : ∀ (a : ι) (k : ℕ), differentialJet k (familySchwarzian C a) ∈ L := by
    intro a k
    have h := hmem (a, k + 3)
    rwa [familySchwarzianSystem_of_ge (by simp), show (a, k + 3).2 - 3 = k from by simp] at h
  have hclosed : ∀ y ∈ L, y′ ∈ L := by
    have hle := adjoin_le_derivStableField (C := C)
      (S := Set.range (familySchwarzianSystem C (ι := ι))) (L := L)
      (hbase := deriv_algebraMap_mem L) ?_
    · exact fun y hy => (hle hy).2
    rintro _ ⟨⟨a, m⟩, rfl⟩
    refine ⟨hmem (a, m), ?_⟩
    by_cases hm : m < 3
    · interval_cases m
      · rw [familySchwarzianSystem_of_lt (by norm_num), familyJet_deriv]
        exact hjetmem a 1 (by norm_num)
      · rw [familySchwarzianSystem_of_lt (by norm_num), familyJet_deriv]
        exact hjetmem a 2 (by norm_num)
      · rw [familySchwarzianSystem_of_lt (by norm_num), familyJet_deriv]
        have h3 : familyJet C a 3 ∈ L := by
          rw [familyJet_three_eq]
          refine add_mem (mul_mem (hjetmem a 1 (by norm_num)) ?_) ?_
          · simpa using hschwmem a 0
          · exact div_mem (mul_mem (div_mem (by simp) (by simp))
              (pow_mem (hjetmem a 2 (by norm_num)) 2)) (hjetmem a 1 (by norm_num))
        exact h3
    · rw [familySchwarzianSystem_of_ge (by simp; omega)]
      rw [show (differentialJet (((a, m) : ι × ℕ).2 - 3) (familySchwarzian C a))′
          = differentialJet (m - 3 + 1) (familySchwarzian C a) from by
        rw [differentialJet_succ]]
      exact hschwmem a (m - 3 + 1)
  have hjet : ∀ (a : ι) (m : ℕ), familyJet C a m ∈ L := by
    intro a m
    induction m with
    | zero => exact hjetmem a 0 (by norm_num)
    | succ m ih =>
        have h := hclosed _ ih
        rwa [familyJet_deriv] at h
  refine le_antisymm le_top ?_
  rw [← freeCoordinateField_univ (C := C) (σ := ι × ℕ), freeCoordinateField,
    IntermediateField.adjoin_le_iff]
  rintro _ ⟨⟨a, m⟩, -, rfl⟩
  exact hjet a m

/-- **The family Schwarzian change of coordinates.** -/
def familySchwarzianBasisEquiv (C ι : Type*) [Field C] [CharZero C] [Differential C] :
    FreeCoordinateRationalField C (ι × ℕ) ≃ₐ[C] FreeFamilyJetField C ι :=
  freeCoordinateBasisEquiv algebraicIndependent_familySchwarzianSystem
    familySchwarzianSystem_adjoin_eq_top

@[simp]
theorem familySchwarzianBasisEquiv_freeCoordinate (p : ι × ℕ) :
    familySchwarzianBasisEquiv C ι (freeCoordinate C (ι × ℕ) p) =
      familySchwarzianSystem C p :=
  freeCoordinateBasisEquiv_freeCoordinate _ _ p

end

end GaloisForLFunctions.HTGeometry
