import GaloisForLFunctions.HTGeometry.CDGABarLeibniz

/-!
# The total differential of the bar construction

The bar differential lowers the number of factors by one and the internal differential keeps it, so
the square of the total differential splits into three independent components: the internal
differential squared, the bar differential squared, and the cross term in which each is applied
once.  The first two vanish already; the cross term is the statement that the two differentials
anticommute, and it follows stage by stage from four cancellations — the Leibniz rule on the merged
slot, the commutation of a multiplication with a differential acting further to the right, the
anticommutation of a degree-one map on the left factor with one on the right, and the inductive
hypothesis one stage down.

* `HTGeometry.barD_comm_d` : the bar and internal differentials anticommute.
* `HTGeometry.barTotalD_sq` : the total differential squares to zero.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))

section StageSplit

/-- The internal differential of a bar stage, as a degree-one map on the outer shifted factor plus
one on everything after it. -/
theorem barPower_succ_d_split (k n : ℕ)
    (G : TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier n) :
    (barPower ε (k + 1)).d n G
      = barStageDL ε (barPower ε k).carrier n G
        + tensorRightDegOne (M := barShiftFamily ε) (N := (barPower ε k).carrier)
          (N' := (barPower ε k).carrier) (fun b => (barPower ε k).d b) n G := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases a <;> cases b <;> rfl

/-- The same one stage up, with the coefficient family unfolded and the inner differential already
split, so that the three halves the cancellations use appear separately. -/
theorem barPower_succ_succ_d_split (k n : ℕ)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b) n) :
    (barPower ε (k + 2)).d n F
      = barStageDL ε
          (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b) n F
        + tensorRightDegOne (M := barShiftFamily ε)
          (N := fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b)
          (N' := fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b)
          (fun b => barStageDL ε (barPower ε k).carrier b
            + tensorRightDegOneₗ (M := barShiftFamily ε) (N := (barPower ε k).carrier)
              (N' := (barPower ε k).carrier) (fun c => (barPower ε k).d c) b) n F := by
  funext p
  obtain ⟨⟨a, b⟩, h⟩ := p
  cases a <;> cases b <;> rfl

/-- The regrouping of the eight terms of the cross term into the four pairs and triples that
cancel. -/
theorem barTotal_regroup {β : Type*} [AddCommGroup β] (u₁ u₂ u₃ v₁ v₂ w₁ w₂ z₁ z₂ : β) :
    u₁ + (u₂ + u₃) + (v₁ + v₂) + (w₁ + w₂ + (z₁ + z₂))
      = w₁ + u₁ + u₂ + (u₃ + z₁) + (w₂ + v₁) + (v₂ + z₂) := by
  abel

end StageSplit

set_option maxHeartbeats 1000000 in
/-- **The bar differential and the internal differential anticommute.**  Written recursively, the
head of the bar differential against the internal one is the Leibniz rule of the shifted product
plus the commutation of a multiplication with a differential further to the right, and the tail
against the internal one is the anticommutation of the two half-differentials of a tensor product
plus the inductive hypothesis. -/
theorem barD_comm_d : ∀ (k n : ℕ) (F : (barPower ε (k + 1)).carrier n),
    barD ε k (n + 1) ((barPower ε (k + 1)).d n F)
      + (barPower ε k).d (n + 1) (barD ε k n F) = 0
  | 0, n, F => by
      rw [barD_zero, barD_zero]
      simp only [LinearMap.zero_apply, map_zero, add_zero]
  | (k + 1), n, F => by
    have hIH : ∀ b : ℕ,
        (barD ε k (b + 1)).comp ((barPower ε (k + 1)).d b)
          + ((barPower ε k).d (b + 1)).comp (barD ε k b) = 0 :=
      fun b => LinearMap.ext fun G => barD_comm_d k b G
    have hbar : ∀ (m : ℕ) (V : TensorCarrier (R := R) (barShiftFamily ε)
          (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b) m),
        barD ε (k + 1) m V = barH ε k m V + barT ε k m V := fun m V => by
      rw [barD_succ]
      rfl
    have hsrc : (barPower ε (k + 2)).d n F
        = barStageDL ε
            (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b) n F
          + (tensorRightDegOne (M := barShiftFamily ε)
              (fun b => barStageDL ε (barPower ε k).carrier b) n F
            + tensorRightDegOne (M := barShiftFamily ε)
              (fun b => tensorRightDegOneₗ (M := barShiftFamily ε)
                (N := (barPower ε k).carrier) (N' := (barPower ε k).carrier)
                (fun c => (barPower ε k).d c) b) n F) := by
      rw [barPower_succ_succ_d_split]
      exact congrArg (fun z => barStageDL ε
        (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b) n F + z)
        (tensorRightDegOne_add_map (M := barShiftFamily ε) _ _ n F)
    have hexp : barD ε (k + 1) (n + 1) ((barPower ε (k + 2)).d n F)
          + (barPower ε (k + 1)).d (n + 1) (barD ε (k + 1) n F)
        = barStageDL ε (barPower ε k).carrier (n + 1) (barH ε k n F)
            + barH ε k (n + 1) (barStageDL ε
              (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b) n F)
            + barH ε k (n + 1) (tensorRightDegOne (M := barShiftFamily ε)
              (fun b => barStageDL ε (barPower ε k).carrier b) n F)
          + (barH ε k (n + 1) (tensorRightDegOne (M := barShiftFamily ε)
                (fun b => tensorRightDegOneₗ (M := barShiftFamily ε)
                  (N := (barPower ε k).carrier) (N' := (barPower ε k).carrier)
                  (fun c => (barPower ε k).d c) b) n F)
            + tensorRightDegOne (M := barShiftFamily ε) (N := (barPower ε k).carrier)
              (N' := (barPower ε k).carrier) (fun b => (barPower ε k).d b) (n + 1)
              (barH ε k n F))
          + (barStageDL ε (barPower ε k).carrier (n + 1) (barT ε k n F)
            + barT ε k (n + 1) (barStageDL ε
              (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b) n F))
          + (barT ε k (n + 1) (tensorRightDegOne (M := barShiftFamily ε)
                (fun b => barStageDL ε (barPower ε k).carrier b) n F
              + tensorRightDegOne (M := barShiftFamily ε)
                (fun b => tensorRightDegOneₗ (M := barShiftFamily ε)
                  (N := (barPower ε k).carrier) (N' := (barPower ε k).carrier)
                  (fun c => (barPower ε k).d c) b) n F)
            + tensorRightDegOne (M := barShiftFamily ε) (N := (barPower ε k).carrier)
              (N' := (barPower ε k).carrier) (fun b => (barPower ε k).d b) (n + 1)
              (barT ε k n F)) := by
      rw [hsrc, hbar, hbar, barPower_succ_d_split, (barH ε k (n + 1)).map_add,
        (barH ε k (n + 1)).map_add, (barT ε k (n + 1)).map_add,
        (barStageDL ε (barPower ε k).carrier (n + 1)).map_add, tensorRightDegOne_add]
      exact barTotal_regroup _ _ _ _ _ _ _ _ _
    have h3 : barStageDL ε (barPower ε k).carrier (n + 1) (barT ε k n F)
          + barT ε k (n + 1) (barStageDL ε
            (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b) n F)
        = 0 :=
      tensorLeftDegOne_tensorRightDegOne_add (M := barShiftFamily ε) (M' := barShiftFamily ε)
        (N := fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b)
        (N' := (barPower ε k).carrier) (augIdealShiftD ε) (fun b => barD ε k b) n F
    have h4 : barT ε k (n + 1) (tensorRightDegOne (M := barShiftFamily ε)
            (fun b => barStageDL ε (barPower ε k).carrier b) n F
          + tensorRightDegOne (M := barShiftFamily ε)
            (fun b => tensorRightDegOneₗ (M := barShiftFamily ε)
              (N := (barPower ε k).carrier) (N' := (barPower ε k).carrier)
              (fun c => (barPower ε k).d c) b) n F)
        + tensorRightDegOne (M := barShiftFamily ε) (N := (barPower ε k).carrier)
          (N' := (barPower ε k).carrier) (fun b => (barPower ε k).d b) (n + 1)
          (barT ε k n F) = 0 := by
      have hsum : tensorRightDegOne (M := barShiftFamily ε)
              (fun b => barStageDL ε (barPower ε k).carrier b) n F
            + tensorRightDegOne (M := barShiftFamily ε)
              (fun b => tensorRightDegOneₗ (M := barShiftFamily ε)
                (N := (barPower ε k).carrier) (N' := (barPower ε k).carrier)
                (fun c => (barPower ε k).d c) b) n F
          = tensorRightDegOne (M := barShiftFamily ε)
            (fun b => barStageDL ε (barPower ε k).carrier b
              + tensorRightDegOneₗ (M := barShiftFamily ε) (N := (barPower ε k).carrier)
                (N' := (barPower ε k).carrier) (fun c => (barPower ε k).d c) b) n F :=
        (tensorRightDegOne_add_map (M := barShiftFamily ε) _ _ n F).symm
      rw [hsum]
      exact tensorRightDegOne_comp_add (M := barShiftFamily ε)
        (N := fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b)
        (N'' := (barPower ε k).carrier)
        (fun b => barStageDL ε (barPower ε k).carrier b
          + tensorRightDegOneₗ (M := barShiftFamily ε) (N := (barPower ε k).carrier)
            (N' := (barPower ε k).carrier) (fun c => (barPower ε k).d c) b)
        (fun b => barD ε k b) (fun b => barD ε k b) (fun b => (barPower ε k).d b) hIH n F
    rw [hexp]
    funext p
    obtain ⟨⟨c, e⟩, hp⟩ := p
    have h1 := barHead_leibniz_apply (ε := ε) (Z := (barPower ε k).carrier) n c e hp F
    have h2 := barHead_comm_tail_apply (ε := ε) (N := (barPower ε k).carrier)
      (N' := (barPower ε k).carrier) n c e hp (fun b => (barPower ε k).d b) F
    have h3p : (barStageDL ε (barPower ε k).carrier (n + 1) (barT ε k n F)
          + barT ε k (n + 1) (barStageDL ε
            (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b) n F))
        ⟨(c, e), hp⟩ = 0 := by rw [h3]; rfl
    have h4p : (barT ε k (n + 1) (tensorRightDegOne (M := barShiftFamily ε)
            (fun b => barStageDL ε (barPower ε k).carrier b) n F
          + tensorRightDegOne (M := barShiftFamily ε)
            (fun b => tensorRightDegOneₗ (M := barShiftFamily ε)
              (N := (barPower ε k).carrier) (N' := (barPower ε k).carrier)
              (fun c => (barPower ε k).d c) b) n F)
        + tensorRightDegOne (M := barShiftFamily ε) (N := (barPower ε k).carrier)
          (N' := (barPower ε k).carrier) (fun b => (barPower ε k).d b) (n + 1)
          (barT ε k n F)) ⟨(c, e), hp⟩ = 0 := by rw [h4]; rfl
    show (barStageDL ε (barPower ε k).carrier (n + 1) (barH ε k n F) ⟨(c, e), hp⟩
          + barH ε k (n + 1) (barStageDL ε
              (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b) n F)
            ⟨(c, e), hp⟩
          + barH ε k (n + 1) (tensorRightDegOne (M := barShiftFamily ε)
              (fun b => barStageDL ε (barPower ε k).carrier b) n F) ⟨(c, e), hp⟩)
        + (barH ε k (n + 1) (tensorRightDegOneₗ (M := barShiftFamily ε)
              (fun b => tensorRightDegOneₗ (M := barShiftFamily ε)
                (N := (barPower ε k).carrier) (N' := (barPower ε k).carrier)
                (fun c => (barPower ε k).d c) b) n F) ⟨(c, e), hp⟩
          + tensorRightDegOneₗ (M := barShiftFamily ε) (N := (barPower ε k).carrier)
              (N' := (barPower ε k).carrier) (fun b => (barPower ε k).d b) (n + 1)
              (barH ε k n F) ⟨(c, e), hp⟩)
        + (barStageDL ε (barPower ε k).carrier (n + 1) (barT ε k n F)
            + barT ε k (n + 1) (barStageDL ε
              (fun b => TensorCarrier (R := R) (barShiftFamily ε) (barPower ε k).carrier b) n F))
            ⟨(c, e), hp⟩
        + (barT ε k (n + 1) (tensorRightDegOne (M := barShiftFamily ε)
                (fun b => barStageDL ε (barPower ε k).carrier b) n F
              + tensorRightDegOne (M := barShiftFamily ε)
                (fun b => tensorRightDegOneₗ (M := barShiftFamily ε)
                  (N := (barPower ε k).carrier) (N' := (barPower ε k).carrier)
                  (fun c => (barPower ε k).d c) b) n F)
            + tensorRightDegOne (M := barShiftFamily ε) (N := (barPower ε k).carrier)
              (N' := (barPower ε k).carrier) (fun b => (barPower ε k).d b) (n + 1)
              (barT ε k n F)) ⟨(c, e), hp⟩ = 0
    rw [h1, h2, h3p, h4p, add_zero, add_zero, add_zero]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open DirectSum

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))

theorem barTotalComponent_zero (n : ℕ) (x : (barPower ε 0).carrier n) :
    barTotalComponent ε 0 n x
      = DirectSum.lof R ℕ (fun j => (barPower ε j).carrier (n + 1)) 0
        ((barPower ε 0).d n x) := rfl

theorem barTotalComponent_succ (k n : ℕ) (x : (barPower ε (k + 1)).carrier n) :
    barTotalComponent ε (k + 1) n x
      = DirectSum.lof R ℕ (fun j => (barPower ε j).carrier (n + 1)) (k + 1)
          ((barPower ε (k + 1)).d n x)
        + DirectSum.lof R ℕ (fun j => (barPower ε j).carrier (n + 1)) k (barD ε k n x) := rfl

/-- **The total differential squares to zero on one tensor power.**  The component with the same
number of factors is the internal differential squared, the one with two fewer is the bar
differential squared, and the one in between is the cross term. -/
theorem barTotalD_of_sq (k n : ℕ) (x : (barPower ε k).carrier n) :
    barTotalD ε (n + 1)
        (barTotalD ε n (DirectSum.lof R ℕ (fun j => (barPower ε j).carrier n) k x)) = 0 := by
  rw [barTotalD_of]
  cases k with
  | zero =>
      rw [barTotalComponent_zero, barTotalD_of, barTotalComponent_zero, (barPower ε 0).d_d,
        map_zero]
  | succ k' =>
      rw [barTotalComponent_succ, map_add, barTotalD_of, barTotalD_of, barTotalComponent_succ,
        (barPower ε (k' + 1)).d_d, map_zero, zero_add]
      cases k' with
      | zero =>
          rw [barTotalComponent_zero, ← map_add, barD_comm_d, map_zero]
      | succ k'' =>
          rw [barTotalComponent_succ, barD_sq, map_zero, add_zero, ← map_add, barD_comm_d,
            map_zero]

/-- **The total differential of the bar construction squares to zero.** -/
theorem barTotalD_sq (n : ℕ) (x : BarCarrier ε n) :
    barTotalD ε (n + 1) (barTotalD ε n x) = 0 := by
  refine DirectSum.induction_on x ?_ ?_ ?_
  · rw [map_zero, map_zero]
  · intro k y
    exact barTotalD_of_sq ε k n y
  · intro y z hy hz
    rw [map_add, map_add, hy, hz, add_zero]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))

/-- **The bar construction of an augmented commutative differential graded algebra**, as a cochain
complex: in each degree the direct sum over the number of factors of the tensor powers of the
shifted augmentation ideal, with the internal differential plus the multiplication of one adjacent
pair. -/
noncomputable def barComplex : Cochain R where
  carrier n := BarCarrier ε n
  group _ := inferInstance
  smul _ := inferInstance
  d n := barTotalD ε n
  d_d n x := barTotalD_sq ε n x

@[simp] theorem barComplex_d (n : ℕ) : (barComplex ε).d n = barTotalD ε n := rfl

end GaloisForLFunctions.HTGeometry
