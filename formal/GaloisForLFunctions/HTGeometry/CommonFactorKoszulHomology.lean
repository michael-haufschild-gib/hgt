import GaloisForLFunctions.HTGeometry.PrincipalConormal

/-!
# Koszul homology of two unit presentations of one regular factor

For a regular element `z` and units `a,b`, this file computes the actual homology quotients of
the three-term Koszul complex on `(z*a,z*b)`.  Degree zero and degree one are both `R/(z)`, degree
two vanishes, and the degree-one generator is the syzygy `(b,-a)`.  Composing degree one with the
principal cotangent equivalence identifies it with `(z)/(z)^(2 : ℕ)`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R]

/-- Degree-one differential of the Koszul complex on `(z*a,z*b)`. -/
def commonFactorKoszulD1 (z : R) (a b : Rˣ) : R × R →ₗ[R] R where
  toFun p := p.1 * (z * (a : R)) + p.2 * (z * (b : R))
  map_add' x y := by simp; ring
  map_smul' r x := by simp [smul_eq_mul]; ring

/-- Degree-two differential of the Koszul complex on `(z*a,z*b)`. -/
def commonFactorKoszulD2 (z : R) (a b : Rˣ) : R →ₗ[R] R × R where
  toFun t := (-t * (z * (b : R)), t * (z * (a : R)))
  map_add' x y := by ext <;> simp <;> ring
  map_smul' r x := by ext <;> simp [smul_eq_mul] <;> ring

@[simp] theorem commonFactorKoszulD1_apply (z : R) (a b : Rˣ) (p : R × R) :
    commonFactorKoszulD1 z a b p = p.1 * (z * (a : R)) + p.2 * (z * (b : R)) := rfl

@[simp] theorem commonFactorKoszulD2_apply (z : R) (a b : Rˣ) (t : R) :
    commonFactorKoszulD2 z a b t = (-t * (z * (b : R)), t * (z * (a : R))) := rfl

/-- The two Koszul differentials compose to zero. -/
theorem commonFactorKoszulD1_comp_D2 (z : R) (a b : Rˣ) :
    commonFactorKoszulD1 z a b ∘ₗ commonFactorKoszulD2 z a b = 0 := by
  apply LinearMap.ext
  intro t
  simp
  ring

/-- Degree-zero homology, defined as the actual cokernel of `d₁`. -/
abbrev commonFactorKoszulH0 (z : R) (a b : Rˣ) : Type _ :=
  R ⧸ LinearMap.range (commonFactorKoszulD1 z a b)

/-- Degree-one cycles of the actual Koszul complex. -/
abbrev commonFactorKoszulCycles (z : R) (a b : Rˣ) : Submodule R (R × R) :=
  LinearMap.ker (commonFactorKoszulD1 z a b)

/-- Degree-one boundaries, as a submodule of degree-one cycles. -/
def commonFactorKoszulBoundaries (z : R) (a b : Rˣ) :
    Submodule R (commonFactorKoszulCycles z a b) :=
  (LinearMap.range (commonFactorKoszulD2 z a b)).comap
    (commonFactorKoszulCycles z a b).subtype

/-- Degree-one homology, defined as cycles modulo boundaries. -/
abbrev commonFactorKoszulH1 (z : R) (a b : Rˣ) : Type _ :=
  commonFactorKoszulCycles z a b ⧸ commonFactorKoszulBoundaries z a b

/-- Degree-two homology, the kernel of `d₂`. -/
abbrev commonFactorKoszulH2 (z : R) (a b : Rˣ) : Submodule R R :=
  LinearMap.ker (commonFactorKoszulD2 z a b)

/-- The image ideal of `(z*a,z*b)` is exactly the principal ideal `(z)`. -/
theorem range_commonFactorKoszulD1 (z : R) (a b : Rˣ) :
    LinearMap.range (commonFactorKoszulD1 z a b) =
      (Ideal.span ({z} : Set R) : Submodule R R) := by
  ext r
  constructor
  · rintro ⟨p, rfl⟩
    rw [Ideal.mem_span_singleton]
    refine ⟨p.1 * (a : R) + p.2 * (b : R), ?_⟩
    simp
    ring
  · intro hr
    rw [Ideal.mem_span_singleton] at hr
    obtain ⟨c, rfl⟩ := hr
    refine ⟨(c * (↑(a⁻¹) : R), 0), ?_⟩
    simp only [commonFactorKoszulD1_apply, zero_mul, add_zero]
    calc
      c * (↑(a⁻¹) : R) * (z * (a : R)) = c * z * ((↑(a⁻¹) : R) * (a : R)) := by ring
      _ = z * c := by simp [mul_comm]

/-- Degree-zero Koszul homology is the Cartier divisor ring `R/(z)`. -/
def commonFactorKoszulH0Equiv (z : R) (a b : Rˣ) :
    commonFactorKoszulH0 z a b ≃ₗ[R] R ⧸ (Ideal.span ({z} : Set R) : Submodule R R) :=
  Submodule.quotEquivOfEq _ _ (range_commonFactorKoszulD1 z a b)

/-- The shell-presentation syzygy `t ↦ t(b,-a)`. -/
def commonFactorSyzygyMap (a b : Rˣ) : R →ₗ[R] R × R where
  toFun t := (t * (b : R), -(t * (a : R)))
  map_add' x y := by ext <;> simp <;> ring
  map_smul' r x := by ext <;> simp [smul_eq_mul] <;> ring

/-- Every multiple of `(b,-a)` is a degree-one cycle. -/
def commonFactorSyzygyToCycles (z : R) (a b : Rˣ) :
    R →ₗ[R] commonFactorKoszulCycles z a b :=
  (commonFactorSyzygyMap a b).codRestrict _ fun t => by
    rw [LinearMap.mem_ker]
    simp [commonFactorSyzygyMap]
    ring

theorem commonFactorSyzygyToCycles_injective (z : R) (a b : Rˣ) :
    Function.Injective (commonFactorSyzygyToCycles z a b) := by
  intro x y h
  have hfst := congrArg (fun p : commonFactorKoszulCycles z a b => p.1.1) h
  apply_fun (fun r : R => r * (↑(b⁻¹) : R)) at hfst
  simpa [commonFactorSyzygyToCycles, commonFactorSyzygyMap, mul_assoc] using hfst

/-- Regularity hypothesis in the exact form used by the homology computation. -/
def IsKoszulRegular (z : R) : Prop := ∀ r : R, z * r = 0 → r = 0

/-- Every degree-one cycle is a unique multiple of `(b,-a)`. -/
theorem commonFactorSyzygyToCycles_surjective {z : R} (a b : Rˣ)
    (hz : IsKoszulRegular z) :
    Function.Surjective (commonFactorSyzygyToCycles z a b) := by
  intro p
  have hp := p.2
  rw [LinearMap.mem_ker] at hp
  rw [commonFactorKoszulD1_apply] at hp
  have hlin : p.1.1 * (a : R) + p.1.2 * (b : R) = 0 := by
    apply hz
    calc
      z * (p.1.1 * (a : R) + p.1.2 * (b : R)) =
          p.1.1 * (z * (a : R)) + p.1.2 * (z * (b : R)) := by ring
      _ = 0 := hp
  refine ⟨p.1.1 * (↑(b⁻¹) : R), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · simp [commonFactorSyzygyToCycles, commonFactorSyzygyMap, mul_assoc]
  · have hmul := congrArg (fun r : R => r * (↑(b⁻¹) : R)) hlin
    simp [add_mul, mul_assoc] at hmul
    change -(p.1.1 * (↑(b⁻¹) : R) * (a : R)) = p.1.2
    linear_combination -hmul

/-- The syzygy line is exactly the degree-one cycle module. -/
def commonFactorSyzygyEquiv {z : R} (a b : Rˣ) (hz : IsKoszulRegular z) :
    R ≃ₗ[R] commonFactorKoszulCycles z a b :=
  LinearEquiv.ofBijective (commonFactorSyzygyToCycles z a b)
    ⟨commonFactorSyzygyToCycles_injective z a b,
      commonFactorSyzygyToCycles_surjective a b hz⟩

/-- Under the syzygy trivialization, boundaries are exactly `z` times the syzygy line. -/
theorem map_span_commonFactorSyzygyEquiv_eq_boundaries {z : R} (a b : Rˣ)
    (hz : IsKoszulRegular z) :
    Submodule.map (commonFactorSyzygyEquiv a b hz).toLinearMap
        (Ideal.span ({z} : Set R) : Submodule R R) =
      commonFactorKoszulBoundaries z a b := by
  ext p
  constructor
  · rintro ⟨r, hr, rfl⟩
    change r ∈ Ideal.span ({z} : Set R) at hr
    rw [Ideal.mem_span_singleton] at hr
    obtain ⟨c, rfl⟩ := hr
    change (commonFactorSyzygyEquiv a b hz (z * c)).1 ∈
      LinearMap.range (commonFactorKoszulD2 z a b)
    refine ⟨-c, ?_⟩
    apply Prod.ext <;>
      simp [commonFactorSyzygyEquiv, commonFactorSyzygyToCycles,
        commonFactorSyzygyMap] <;> ring
  · intro hp
    change p.1 ∈ LinearMap.range (commonFactorKoszulD2 z a b) at hp
    obtain ⟨t, ht⟩ := hp
    refine ⟨-t * z, ?_, ?_⟩
    · change -t * z ∈ Ideal.span ({z} : Set R)
      rw [Ideal.mem_span_singleton]
      exact ⟨-t, by ring⟩
    · apply Subtype.ext
      rw [← ht]
      apply Prod.ext <;>
        simp [commonFactorSyzygyEquiv, commonFactorSyzygyToCycles,
          commonFactorSyzygyMap] <;> ring

/-- Degree-one Koszul homology is `R/(z)`, with `t mod z` represented by `t(b,-a)`. -/
def commonFactorKoszulH1Equiv {z : R} (a b : Rˣ) (hz : IsKoszulRegular z) :
    commonFactorKoszulH1 z a b ≃ₗ[R]
      R ⧸ (Ideal.span ({z} : Set R) : Submodule R R) :=
  (Submodule.Quotient.equiv
    (Ideal.span ({z} : Set R) : Submodule R R)
    (commonFactorKoszulBoundaries z a b)
    (commonFactorSyzygyEquiv a b hz)
    (map_span_commonFactorSyzygyEquiv_eq_boundaries a b hz)).symm

/-- Degree two vanishes for a regular common factor. -/
theorem commonFactorKoszulH2_eq_bot {z : R} (a b : Rˣ) (hz : IsKoszulRegular z) :
    commonFactorKoszulH2 z a b = ⊥ := by
  ext t
  constructor
  · intro ht
    rw [LinearMap.mem_ker] at ht
    have hfst := congrArg Prod.fst ht
    have hzero : z * t = 0 := by
      apply_fun (fun r : R => r * (↑(b⁻¹) : R)) at hfst
      simpa [mul_assoc, mul_comm, mul_left_comm] using hfst
    exact (hz t hzero : t = 0)
  · rintro rfl
    simp

/-- The excess degree-one class is the principal Cartier conormal `(z)/(z)^(2 : ℕ)`. -/
def commonFactorKoszulH1CotangentEquiv {z : R} (a b : Rˣ) (hz : IsKoszulRegular z) :
    commonFactorKoszulH1 z a b ≃ₗ[R] (Ideal.span ({z} : Set R)).Cotangent :=
  (commonFactorKoszulH1Equiv a b hz).trans
    (principalCotangentEquiv fun x y h => by
      apply sub_eq_zero.mp
      apply hz
      simpa [mul_sub] using sub_eq_zero.mpr h)

/-! ## Arbitrary split families and the full normalized Koszul complex -/

section SplitFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Unit-weighted augmentation `h((xᵢ)) = ∑ uᵢ xᵢ`. -/
def unitWeightedAugmentation (u : ι → Rˣ) : (ι → R) →ₗ[R] R where
  toFun x := ∑ i, (u i : R) * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- A section of the augmentation obtained from one chosen unit coordinate. -/
def unitWeightedSection (u : ι → Rˣ) (i₀ : ι) : R →ₗ[R] (ι → R) where
  toFun r i := if i = i₀ then (↑((u i₀)⁻¹) : R) * r else 0
  map_add' x y := by
    ext i
    by_cases hi : i = i₀ <;> simp [hi, mul_add]
  map_smul' r x := by
    ext i
    by_cases hi : i = i₀ <;> simp [hi, smul_eq_mul]
    ring

@[simp] theorem unitWeightedAugmentation_section (u : ι → Rˣ) (i₀ : ι) (r : R) :
    unitWeightedAugmentation u (unitWeightedSection u i₀ r) = r := by
  classical
  simp [unitWeightedAugmentation, unitWeightedSection]

/-- Kernel of the unit-weighted augmentation: the shell-presentation relation module. -/
abbrev unitWeightedRelations (u : ι → Rˣ) : Submodule R (ι → R) :=
  LinearMap.ker (unitWeightedAugmentation u)

/-- Exact split decomposition `R^ι = R·v ⊕ ker h`. -/
def unitWeightedSplitEquiv (u : ι → Rˣ) (i₀ : ι) :
    (ι → R) ≃ₗ[R] R × unitWeightedRelations u := by
  let s := unitWeightedSection u i₀
  let h := unitWeightedAugmentation u
  let f : (ι → R) →ₗ[R] R × unitWeightedRelations u :=
    { toFun := fun x => (h x, ⟨x - s (h x), by
          rw [LinearMap.mem_ker, map_sub, unitWeightedAugmentation_section, sub_self]⟩)
      map_add' := fun x y => by
        apply Prod.ext
        · simp
        · apply Subtype.ext
          dsimp
          rw [map_add, map_add]
          abel
      map_smul' := fun r x => by
        apply Prod.ext
        · simp
        · apply Subtype.ext
          dsimp
          rw [map_smul, map_smul, smul_sub] }
  let g : R × unitWeightedRelations u →ₗ[R] (ι → R) :=
    { toFun := fun p => s p.1 + p.2.1
      map_add' := fun x y => by
        ext i
        simp
        abel
      map_smul' := fun r x => by
        simp only [map_smul, Prod.smul_fst, Submodule.coe_smul, Prod.smul_snd,
          smul_add, RingHom.id_apply] }
  exact LinearEquiv.ofLinear f g
    (by
      apply LinearMap.ext
      rintro ⟨r, e⟩
      apply Prod.ext
      · simp [f, g, s, h]
      · apply Subtype.ext
        ext i
        simp [f, g, s, h])
    (by
      apply LinearMap.ext
      intro x
      ext i
      simp [f, g, s, h])

/-- Coordinates away from the chosen splitting index. -/
abbrev unitWeightedAway (i₀ : ι) := ↥((Finset.univ : Finset ι).erase i₀)

private theorem sum_eq_pivot_add_away (i₀ : ι) (f : ι → R) :
    ∑ i, f i = f i₀ + ∑ j : unitWeightedAway i₀, f j.1 := by
  have hattach : (∑ j : unitWeightedAway i₀, f j.1) =
      ∑ i ∈ (Finset.univ : Finset ι).erase i₀, f i := by
    simpa using Finset.sum_attach ((Finset.univ : Finset ι).erase i₀) f
  rw [hattach, add_comm]
  exact (Finset.sum_erase_add Finset.univ f (Finset.mem_univ i₀)).symm

/-- Explicit basis-coordinate isomorphism
`ker(∑uᵢ·) ≃ R^{ι\{i₀}}`. -/
def unitWeightedAwayEquivRelations (u : ι → Rˣ) (i₀ : ι) :
    (unitWeightedAway i₀ → R) ≃ₗ[R] unitWeightedRelations u := by
  let A : (unitWeightedAway i₀ → R) →ₗ[R] R :=
    { toFun := fun y => ∑ j, (u j.1 : R) * y j
      map_add' := fun x y => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring }
  let f : (unitWeightedAway i₀ → R) →ₗ[R] unitWeightedRelations u :=
    { toFun := fun y => ⟨fun i => if hi : i = i₀
          then -(↑((u i₀)⁻¹) : R) * A y
          else y ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩⟩, by
          rw [LinearMap.mem_ker]
          change (∑ i, (u i : R) * (if hi : i = i₀
            then -(↑((u i₀)⁻¹) : R) * A y
            else y ⟨i, Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩⟩)) = 0
          rw [sum_eq_pivot_add_away i₀]
          simp only [dif_pos]
          have haway : (∑ j : unitWeightedAway i₀,
              (u j.1 : R) * (if h : j.1 = i₀ then
                -(↑((u i₀)⁻¹) : R) * A y else y j)) = A y := by
            change (∑ j : unitWeightedAway i₀,
              (u j.1 : R) * (if h : j.1 = i₀ then
                -(↑((u i₀)⁻¹) : R) * A y else y j)) =
              ∑ j, (u j.1 : R) * y j
            apply Fintype.sum_congr
            intro j
            rw [dif_neg (Finset.mem_erase.mp j.2).1]
          rw [haway]
          calc
            (u i₀ : R) * (-(↑((u i₀)⁻¹) : R) * A y) + A y =
              -((u i₀ : R) * (↑((u i₀)⁻¹) : R)) *
                  A y + A y := by ring
            _ = 0 := by simp⟩
      map_add' := fun x y => by
        apply Subtype.ext
        ext i
        by_cases hi : i = i₀
        · simp [hi, A, Finset.sum_add_distrib, mul_add]
        · simp [hi, A]
      map_smul' := fun r x => by
        apply Subtype.ext
        ext i
        by_cases hi : i = i₀
        · simp [hi, A, Finset.mul_sum, smul_eq_mul]
          ring
        · simp [hi, smul_eq_mul] }
  let g : unitWeightedRelations u →ₗ[R] (unitWeightedAway i₀ → R) :=
    { toFun := fun x j => x.1 j.1
      map_add' := fun x y => rfl
      map_smul' := fun r x => rfl }
  exact LinearEquiv.ofLinear f g
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      ext i
      by_cases hi : i = i₀
      · subst i
        have hx := x.2
        rw [LinearMap.mem_ker] at hx
        change (∑ i, (u i : R) * x.1 i) = 0 at hx
        rw [sum_eq_pivot_add_away i₀] at hx
        have hsum : ∑ j : unitWeightedAway i₀, (u j.1 : R) * x.1 j.1 =
            -(u i₀ : R) * x.1 i₀ := by
          linear_combination hx
        dsimp [f, g]
        rw [if_pos rfl]
        change -(↑((u i₀)⁻¹) : R) * A (fun j => x.1 j.1) = x.1 i₀
        rw [show A (fun j => x.1 j.1) =
          ∑ j : unitWeightedAway i₀, (u j.1 : R) * x.1 j.1 by rfl]
        rw [hsum]
        calc
          -(↑((u i₀)⁻¹) : R) * (-(u i₀ : R) * x.1 i₀) =
              ((↑((u i₀)⁻¹) : R) * (u i₀ : R)) * x.1 i₀ := by ring
          _ = x.1 i₀ := by simp
      · simp [f, g, hi])
    (by
      apply LinearMap.ext
      intro y
      ext j
      simp [f, g, (Finset.mem_erase.mp j.2).1])

/-- Explicit free basis of the relation module, indexed by all non-pivot coordinates. -/
noncomputable def unitWeightedRelationsBasis [LinearOrder ι] (u : ι → Rˣ) (i₀ : ι) :
    Module.Basis (unitWeightedAway i₀) R (unitWeightedRelations u) :=
  (Pi.basisFun R (unitWeightedAway i₀)).map (unitWeightedAwayEquivRelations u i₀)

theorem card_unitWeightedAway [LinearOrder ι] (i₀ : ι) :
    Fintype.card (unitWeightedAway i₀) = Fintype.card ι - 1 := by
  simp [unitWeightedAway]

end SplitFamily

/-! ## Finitely supported arbitrary families -/

section FinsuppSplitFamily

variable {ι : Type*} [DecidableEq ι]

/-- Unit-weighted augmentation on the algebraic direct sum:
`h((xᵢ)) = ∑ uᵢ xᵢ`.  Every sum is finite by the `Finsupp` carrier. -/
def unitWeightedFinsuppAugmentation (u : ι → Rˣ) : (ι →₀ R) →ₗ[R] R :=
  Finsupp.lsum R fun i => LinearMap.toSpanSingleton R R (u i : R)

omit [DecidableEq ι] in
@[simp] theorem unitWeightedFinsuppAugmentation_single
    (u : ι → Rˣ) (i : ι) (r : R) :
    unitWeightedFinsuppAugmentation u (Finsupp.single i r) = (u i : R) * r := by
  simp [unitWeightedFinsuppAugmentation, Finsupp.lsum_apply,
    LinearMap.toSpanSingleton, mul_comm]

/-- A one-coordinate section of the finitely supported augmentation. -/
def unitWeightedFinsuppSection (u : ι → Rˣ) (i₀ : ι) : R →ₗ[R] (ι →₀ R) where
  toFun r := Finsupp.single i₀ ((↑((u i₀)⁻¹) : R) * r)
  map_add' x y := by rw [mul_add, Finsupp.single_add]
  map_smul' r x := by
    ext i
    by_cases hi : i = i₀ <;> simp [hi, smul_eq_mul]
    ring

@[simp] theorem unitWeightedFinsuppAugmentation_section
    (u : ι → Rˣ) (i₀ : ι) (r : R) :
    unitWeightedFinsuppAugmentation u (unitWeightedFinsuppSection u i₀ r) = r := by
  change unitWeightedFinsuppAugmentation u
    (Finsupp.single i₀ ((↑((u i₀)⁻¹) : R) * r)) = r
  rw [unitWeightedFinsuppAugmentation_single]
  calc
    (u i₀ : R) * ((↑((u i₀)⁻¹) : R) * r) =
        ((u i₀ : R) * (↑((u i₀)⁻¹) : R)) * r := by ring
    _ = r := by simp

/-- Relation module in an arbitrary algebraic direct sum. -/
abbrev unitWeightedFinsuppRelations (u : ι → Rˣ) : Submodule R (ι →₀ R) :=
  LinearMap.ker (unitWeightedFinsuppAugmentation u)

/-- Exact splitting of the algebraic direct sum into one pivot line and all relations. -/
def unitWeightedFinsuppSplitEquiv (u : ι → Rˣ) (i₀ : ι) :
    (ι →₀ R) ≃ₗ[R] R × unitWeightedFinsuppRelations u := by
  let s := unitWeightedFinsuppSection u i₀
  let h := unitWeightedFinsuppAugmentation u
  let f : (ι →₀ R) →ₗ[R] R × unitWeightedFinsuppRelations u :=
    { toFun := fun x => (h x, ⟨x - s (h x), by
          rw [LinearMap.mem_ker, map_sub,
            unitWeightedFinsuppAugmentation_section, sub_self]⟩)
      map_add' := fun x y => by
        apply Prod.ext
        · simp
        · apply Subtype.ext
          dsimp
          rw [map_add, map_add]
          abel
      map_smul' := fun r x => by
        apply Prod.ext
        · simp
        · apply Subtype.ext
          dsimp
          rw [map_smul, map_smul, smul_sub] }
  let g : R × unitWeightedFinsuppRelations u →ₗ[R] (ι →₀ R) :=
    { toFun := fun p => s p.1 + p.2.1
      map_add' := fun x y => by
        simp
        abel
      map_smul' := fun r x => by
        simp only [map_smul, Prod.smul_fst, Submodule.coe_smul, Prod.smul_snd,
          smul_add, RingHom.id_apply] }
  exact LinearEquiv.ofLinear f g
    (by
      apply LinearMap.ext
      rintro ⟨r, e⟩
      apply Prod.ext
      · simp [f, g, s, h]
      · apply Subtype.ext
        simp [f, g, s, h])
    (by
      apply LinearMap.ext
      intro x
      simp [f, g, s, h])

/-- Non-pivot indices in an arbitrary family. -/
abbrev unitWeightedFinsuppAway (i₀ : ι) := {i : ι // i ≠ i₀}

/-- The explicit relation vector `eⱼ-uⱼuᵢ₀⁻¹eᵢ₀`. -/
def unitWeightedFinsuppRelationVector (u : ι → Rˣ) (i₀ : ι)
    (j : unitWeightedFinsuppAway i₀) : ι →₀ R :=
  Finsupp.single j.1 1 -
    Finsupp.single i₀ ((u j.1 : R) * (↑((u i₀)⁻¹) : R))

omit [DecidableEq ι] in
theorem unitWeightedFinsuppRelationVector_mem (u : ι → Rˣ) (i₀ : ι)
    (j : unitWeightedFinsuppAway i₀) :
    unitWeightedFinsuppRelationVector u i₀ j ∈ unitWeightedFinsuppRelations u := by
  rw [LinearMap.mem_ker, unitWeightedFinsuppRelationVector, map_sub,
    unitWeightedFinsuppAugmentation_single, unitWeightedFinsuppAugmentation_single]
  calc
    (u j.1 : R) * 1 - (u i₀ : R) *
        ((u j.1 : R) * (↑((u i₀)⁻¹) : R)) =
      (u j.1 : R) - (u j.1 : R) *
        ((u i₀ : R) * (↑((u i₀)⁻¹) : R)) := by ring
    _ = 0 := by simp

/-- Weighted sum on all non-pivot coordinates. -/
def unitWeightedFinsuppAwayAugmentation (u : ι → Rˣ) (i₀ : ι) :
    (unitWeightedFinsuppAway i₀ →₀ R) →ₗ[R] R :=
  Finsupp.lsum R fun j => LinearMap.toSpanSingleton R R (u j.1 : R)

omit [DecidableEq ι] in
theorem unitWeightedFinsuppAugmentation_mapDomain
    (u : ι → Rˣ) (i₀ : ι) (y : unitWeightedFinsuppAway i₀ →₀ R) :
    unitWeightedFinsuppAugmentation u (Finsupp.mapDomain Subtype.val y) =
      unitWeightedFinsuppAwayAugmentation u i₀ y := by
  rw [unitWeightedFinsuppAugmentation, unitWeightedFinsuppAwayAugmentation,
    Finsupp.lsum_apply, Finsupp.lsum_apply,
    Finsupp.sum_mapDomain_index_inj Subtype.val_injective]

private def unitWeightedFinsuppToRelationsRaw (u : ι → Rˣ) (i₀ : ι) :
    (unitWeightedFinsuppAway i₀ →₀ R) →ₗ[R] (ι →₀ R) where
  toFun y := Finsupp.mapDomain Subtype.val y -
    Finsupp.single i₀ ((↑((u i₀)⁻¹) : R) *
      unitWeightedFinsuppAwayAugmentation u i₀ y)
  map_add' x y := by
    rw [Finsupp.mapDomain_add, map_add, mul_add, Finsupp.single_add]
    abel
  map_smul' r x := by
    rw [Finsupp.mapDomain_smul, map_smul]
    ext i
    by_cases hi : i = i₀ <;> simp [hi, smul_eq_mul]
    ring

/-- Build a relation from arbitrary finitely supported non-pivot coordinates. -/
def unitWeightedFinsuppToRelations (u : ι → Rˣ) (i₀ : ι) :
    (unitWeightedFinsuppAway i₀ →₀ R) →ₗ[R] unitWeightedFinsuppRelations u :=
  (unitWeightedFinsuppToRelationsRaw u i₀).codRestrict _ fun y => by
    rw [LinearMap.mem_ker]
    simp only [unitWeightedFinsuppToRelationsRaw]
    change unitWeightedFinsuppAugmentation u
      (Finsupp.mapDomain Subtype.val y -
        Finsupp.single i₀ ((↑((u i₀)⁻¹) : R) *
          unitWeightedFinsuppAwayAugmentation u i₀ y)) = 0
    rw [map_sub, unitWeightedFinsuppAugmentation_mapDomain,
      unitWeightedFinsuppAugmentation_single]
    calc
      unitWeightedFinsuppAwayAugmentation u i₀ y - (u i₀ : R) *
          ((↑((u i₀)⁻¹) : R) * unitWeightedFinsuppAwayAugmentation u i₀ y) =
        unitWeightedFinsuppAwayAugmentation u i₀ y -
          ((u i₀ : R) * (↑((u i₀)⁻¹) : R)) *
            unitWeightedFinsuppAwayAugmentation u i₀ y := by ring
      _ = 0 := by simp

/-- Read all non-pivot coordinates of a relation. -/
def unitWeightedFinsuppFromRelations (u : ι → Rˣ) (i₀ : ι) :
    unitWeightedFinsuppRelations u →ₗ[R] (unitWeightedFinsuppAway i₀ →₀ R) where
  toFun x := x.1.comapDomain Subtype.val Subtype.val_injective.injOn
  map_add' x y := by ext j; simp [Finsupp.comapDomain_apply]
  map_smul' r x := by ext j; simp [Finsupp.comapDomain_apply]

theorem unitWeightedFinsuppFromRelations_toRelations
    (u : ι → Rˣ) (i₀ : ι) (y : unitWeightedFinsuppAway i₀ →₀ R) :
    unitWeightedFinsuppFromRelations u i₀
      (unitWeightedFinsuppToRelations u i₀ y) = y := by
  ext j
  simp only [unitWeightedFinsuppFromRelations, unitWeightedFinsuppToRelations,
    unitWeightedFinsuppToRelationsRaw]
  change (Finsupp.mapDomain Subtype.val y -
    Finsupp.single i₀ ((↑((u i₀)⁻¹) : R) *
      unitWeightedFinsuppAwayAugmentation u i₀ y)) j.1 = y j
  rw [Finsupp.sub_apply, Finsupp.mapDomain_apply Subtype.val_injective,
    Finsupp.single_apply, if_neg j.2.symm, sub_zero]

private theorem unitWeightedFinsuppRelations_ext
    (u : ι → Rˣ) (i₀ : ι) (x y : unitWeightedFinsuppRelations u)
    (h : ∀ j : unitWeightedFinsuppAway i₀, x.1 j.1 = y.1 j.1) : x = y := by
  apply Subtype.ext
  have hdiff : x.1 - y.1 = Finsupp.single i₀ (x.1 i₀ - y.1 i₀) := by
    ext i
    by_cases hi : i = i₀
    · subst i
      simp
    · simp [hi, h ⟨i, hi⟩]
  have hker : unitWeightedFinsuppAugmentation u (x.1 - y.1) = 0 := by
    rw [map_sub]
    simp [LinearMap.mem_ker.mp x.2, LinearMap.mem_ker.mp y.2]
  rw [hdiff, unitWeightedFinsuppAugmentation_single] at hker
  have hzero : x.1 i₀ - y.1 i₀ = 0 := by
    calc
      x.1 i₀ - y.1 i₀ =
          (↑((u i₀)⁻¹) : R) * ((u i₀ : R) * (x.1 i₀ - y.1 i₀)) := by simp
      _ = 0 := by rw [hker, mul_zero]
  ext i
  by_cases hi : i = i₀
  · subst i
    exact sub_eq_zero.mp hzero
  · exact h ⟨i, hi⟩

theorem unitWeightedFinsuppToRelations_fromRelations
    (u : ι → Rˣ) (i₀ : ι) (x : unitWeightedFinsuppRelations u) :
    unitWeightedFinsuppToRelations u i₀
      (unitWeightedFinsuppFromRelations u i₀ x) = x := by
  apply unitWeightedFinsuppRelations_ext u i₀
  intro j
  simp only [unitWeightedFinsuppFromRelations, unitWeightedFinsuppToRelations,
    unitWeightedFinsuppToRelationsRaw]
  change (Finsupp.mapDomain Subtype.val
    (Finsupp.comapDomain Subtype.val x.1 Subtype.val_injective.injOn) -
      Finsupp.single i₀ ((↑((u i₀)⁻¹) : R) *
        unitWeightedFinsuppAwayAugmentation u i₀
          (Finsupp.comapDomain Subtype.val x.1
            Subtype.val_injective.injOn))) j.1 = x.1 j.1
  rw [Finsupp.sub_apply, Finsupp.mapDomain_apply Subtype.val_injective,
    Finsupp.comapDomain_apply, Finsupp.single_apply, if_neg j.2.symm, sub_zero]

/-- Explicit coordinates on all relations in an arbitrary algebraic direct sum. -/
def unitWeightedFinsuppAwayEquivRelations (u : ι → Rˣ) (i₀ : ι) :
    (unitWeightedFinsuppAway i₀ →₀ R) ≃ₗ[R] unitWeightedFinsuppRelations u :=
  LinearEquiv.ofBijective (unitWeightedFinsuppToRelations u i₀) ⟨
    fun x y h => by
      apply_fun unitWeightedFinsuppFromRelations u i₀ at h
      simpa only [unitWeightedFinsuppFromRelations_toRelations] using h,
    fun x => ⟨unitWeightedFinsuppFromRelations u i₀ x,
      unitWeightedFinsuppToRelations_fromRelations u i₀ x⟩⟩

/-- The explicit free basis of all finitely supported relations. -/
noncomputable def unitWeightedFinsuppRelationsBasis (u : ι → Rˣ) (i₀ : ι) :
    Module.Basis (unitWeightedFinsuppAway i₀) R (unitWeightedFinsuppRelations u) :=
  Finsupp.basisSingleOne.map (unitWeightedFinsuppAwayEquivRelations u i₀)

/-- Each relation-basis vector is exactly `eⱼ-uⱼuᵢ₀⁻¹eᵢ₀`. -/
theorem unitWeightedFinsuppRelationsBasis_apply (u : ι → Rˣ) (i₀ : ι)
    (j : unitWeightedFinsuppAway i₀) :
    (unitWeightedFinsuppRelationsBasis u i₀ j).1 =
      unitWeightedFinsuppRelationVector u i₀ j := by
  rw [unitWeightedFinsuppRelationsBasis, Module.Basis.map_apply]
  change (unitWeightedFinsuppToRelations u i₀ (Finsupp.basisSingleOne j)).1 =
    unitWeightedFinsuppRelationVector u i₀ j
  have hsingle : Finsupp.basisSingleOne j = Finsupp.single j (1 : R) := by
    apply (Finsupp.basisSingleOne.repr).injective
    rw [Module.Basis.repr_self, Finsupp.basisSingleOne_repr]
    rfl
  rw [hsingle]
  change unitWeightedFinsuppToRelationsRaw u i₀ (Finsupp.single j (1 : R)) =
    unitWeightedFinsuppRelationVector u i₀ j
  simp only [unitWeightedFinsuppToRelationsRaw]
  ext i
  change (Finsupp.mapDomain Subtype.val (Finsupp.single j (1 : R)) -
      Finsupp.single i₀ ((↑((u i₀)⁻¹) : R) *
        unitWeightedFinsuppAwayAugmentation u i₀ (Finsupp.single j (1 : R)))) i =
    ((Finsupp.single j.1 1 -
      Finsupp.single i₀ ((u j.1 : R) * (↑((u i₀)⁻¹) : R))) : ι →₀ R) i
  simp only [Finsupp.sub_apply]
  rw [Finsupp.mapDomain_single]
  simp [unitWeightedFinsuppAwayAugmentation, Finsupp.single_apply, mul_comm]

end FinsuppSplitFamily

/-- Scalar multiplication by the common factor, as a linear endomorphism. -/
def commonFactorScalarMap (z : R) {M : Type*} [AddCommGroup M] [Module R M] : M →ₗ[R] M where
  toFun x := z • x
  map_add' x y := smul_add z x y
  map_smul' r x := by simp [smul_smul, mul_comm]

/-- Degree `p+1` chain group in split Koszul coordinates:
`Λ^(p+1) E ⊕ v∧Λ^p E`. -/
abbrev splitCommonFactorKoszulChain (E : Type*) [AddCommGroup E] [Module R E] (p : ℕ) :=
  (⋀[R]^(p + 1) E) × (⋀[R]^p E)

/-- Differential test on degree `p+1`: `(u,v) ↦ z v`.  Its zero set is the cycle module. -/
def splitCommonFactorKoszulCycleMap (z : R) (E : Type*) [AddCommGroup E] [Module R E]
    (p : ℕ) : splitCommonFactorKoszulChain (R := R) E p →ₗ[R] (⋀[R]^p E) where
  toFun x := z • x.2
  map_add' x y := by simp [smul_add]
  map_smul' r x := by simp [smul_smul, mul_comm]

/-- Boundary map from degree `p+2` after forgetting its irrelevant first summand:
`w ↦ (z w,0)`.  This has exactly the full differential range. -/
def splitCommonFactorKoszulBoundaryMap (z : R) (E : Type*) [AddCommGroup E] [Module R E]
    (p : ℕ) : (⋀[R]^(p + 1) E) →ₗ[R] splitCommonFactorKoszulChain (R := R) E p where
  toFun w := (z • w, 0)
  map_add' x y := by simp [smul_add]
  map_smul' r x := by ext <;> simp [smul_smul, mul_comm]

abbrev splitCommonFactorKoszulCycles (z : R) (E : Type*) [AddCommGroup E] [Module R E]
    (p : ℕ) : Submodule R (splitCommonFactorKoszulChain (R := R) E p) :=
  LinearMap.ker (splitCommonFactorKoszulCycleMap z E p)

def splitCommonFactorKoszulBoundaries (z : R) (E : Type*) [AddCommGroup E] [Module R E]
    (p : ℕ) : Submodule R (splitCommonFactorKoszulCycles z E p) :=
  (LinearMap.range (splitCommonFactorKoszulBoundaryMap z E p)).comap
    (splitCommonFactorKoszulCycles z E p).subtype

theorem splitCommonFactorKoszulBoundary_mem_cycles (z : R) (E : Type*) [AddCommGroup E]
    [Module R E] (p : ℕ) (w : ⋀[R]^(p + 1) E) :
    splitCommonFactorKoszulBoundaryMap z E p w ∈ splitCommonFactorKoszulCycles z E p := by
  rw [LinearMap.mem_ker]
  simp [splitCommonFactorKoszulBoundaryMap, splitCommonFactorKoszulCycleMap]

/-- Inclusion of the relation exterior power as all cycles in split coordinates. -/
def splitCommonFactorCyclesMap (z : R) (E : Type*) [AddCommGroup E] [Module R E]
    (p : ℕ) : (⋀[R]^(p + 1) E) →ₗ[R] splitCommonFactorKoszulCycles z E p :=
  { toFun := fun u => ⟨(u, 0), by
        rw [LinearMap.mem_ker]
        simp [splitCommonFactorKoszulCycleMap]⟩
    map_add' := fun x y => by ext <;> simp
    map_smul' := fun r x => by ext <;> simp }

theorem splitCommonFactorCyclesMap_bijective {z : R} (hz : z ≠ 0)
    (E : Type*) [AddCommGroup E] [Module R E] (p : ℕ)
    [NoZeroSMulDivisors R (⋀[R]^p E)] :
    Function.Bijective (splitCommonFactorCyclesMap z E p) := by
  constructor
  · intro x y h
    have := congrArg (fun q : splitCommonFactorKoszulCycles z E p => q.1.1) h
    simpa [splitCommonFactorCyclesMap] using this
  · intro x
    have hx := x.2
    rw [LinearMap.mem_ker] at hx
    have hzero : x.1.2 = 0 := by
      exact (eq_zero_or_eq_zero_of_smul_eq_zero hx).resolve_left hz
    refine ⟨x.1.1, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl hzero.symm

/-- All cycles are canonically the exterior power `Λ^(p+1) E`. -/
def splitCommonFactorCyclesEquiv {z : R} (hz : z ≠ 0)
    (E : Type*) [AddCommGroup E] [Module R E] (p : ℕ)
    [NoZeroSMulDivisors R (⋀[R]^p E)] :
    (⋀[R]^(p + 1) E) ≃ₗ[R] splitCommonFactorKoszulCycles z E p :=
  LinearEquiv.ofBijective (splitCommonFactorCyclesMap z E p)
    (splitCommonFactorCyclesMap_bijective hz E p)

/-- Under cycle coordinates, boundaries are precisely the `z`-multiple submodule. -/
theorem map_scalarRange_splitCommonFactorCyclesEquiv_eq_boundaries {z : R} (hz : z ≠ 0)
    (E : Type*) [AddCommGroup E] [Module R E] (p : ℕ)
    [NoZeroSMulDivisors R (⋀[R]^p E)] :
    Submodule.map (splitCommonFactorCyclesEquiv hz E p).toLinearMap
        (LinearMap.range (commonFactorScalarMap z :
          (⋀[R]^(p + 1) E) →ₗ[R] (⋀[R]^(p + 1) E))) =
      splitCommonFactorKoszulBoundaries z E p := by
  ext x
  constructor
  · rintro ⟨u, ⟨w, rfl⟩, rfl⟩
    change ((splitCommonFactorCyclesEquiv hz E p (z • w)).1) ∈
      LinearMap.range (splitCommonFactorKoszulBoundaryMap z E p)
    refine ⟨w, ?_⟩
    rfl
  · intro hx
    change x.1 ∈ LinearMap.range (splitCommonFactorKoszulBoundaryMap z E p) at hx
    obtain ⟨w, hw⟩ := hx
    refine ⟨z • w, ⟨w, rfl⟩, ?_⟩
    change splitCommonFactorCyclesMap z E p (z • w) = x
    apply Subtype.ext
    exact hw

end

end GaloisForLFunctions.HTGeometry
