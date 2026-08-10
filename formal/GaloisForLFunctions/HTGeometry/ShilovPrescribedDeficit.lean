import GaloisForLFunctions.HTGeometry.ShilovStableImage

/-!
# Prescribed link deficits with global derived vanishing

A countable tower can carry an arbitrary prescribed cokernel at every link and still have
vanishing `lim¹`.  The witness is the tower of tails of a product: `supportedAbove D n` is the set
of sections of `D` vanishing below `n`, and the bonds are the inclusions.  Then

* the cokernel of the `n`-th bond is exactly `D n`, by evaluation at `n`;
* the Roos difference is onto, because the correction sum `∑_{j ∈ [n, k]} (b j) k` is finite in
  every coordinate.

This is the linear core of the card's cancellation phenomenon: linkwise deficits may be arbitrary
while the global derived obstruction vanishes.

It also shows the Mittag-Leffler criterion of `ShilovStableImage.lean` is strictly sufficient.  The
reaches of this tower are the tails themselves, so they never stabilise once infinitely many `D k`
are nonzero, yet `lim¹` vanishes.
-/

namespace GaloisForLFunctions.HTGeometry

namespace BoundaryMigration

universe u v

variable {𝕜 : Type u} [Field 𝕜]
variable {D : ℕ → Type v} [∀ n, AddCommGroup (D n)] [∀ n, Module 𝕜 (D n)]

/-- The sections of `D` vanishing below `n`. -/
def supportedAbove (𝕜 : Type u) [Field 𝕜] (D : ℕ → Type v) [∀ n, AddCommGroup (D n)]
    [∀ n, Module 𝕜 (D n)] (n : ℕ) : Submodule 𝕜 (∀ k, D k) where
  carrier := {x | ∀ k, k < n → x k = 0}
  add_mem' {x y} hx hy := fun k hk => by
    simp only [Pi.add_apply, hx k hk, hy k hk, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' c x hx := fun k hk => by
    simp only [Pi.smul_apply, hx k hk, smul_zero]

theorem mem_supportedAbove {n : ℕ} {x : ∀ k, D k} :
    x ∈ supportedAbove 𝕜 D n ↔ ∀ k, k < n → x k = 0 := Iff.rfl

theorem supportedAbove_succ_le (n : ℕ) :
    supportedAbove 𝕜 D (n + 1) ≤ supportedAbove 𝕜 D n :=
  fun _ hx k hk => hx k (by omega)

/-- The bonds of the prescribed-deficit tower are the tail inclusions. -/
def prescribedBond (n : ℕ) :
    ↥(supportedAbove 𝕜 D (n + 1)) →ₗ[𝕜] ↥(supportedAbove 𝕜 D n) :=
  Submodule.inclusion (supportedAbove_succ_le n)

@[simp]
theorem prescribedBond_coe (n : ℕ) (x : ↥(supportedAbove 𝕜 D (n + 1))) :
    ((prescribedBond n x : ↥(supportedAbove 𝕜 D n)) : ∀ k, D k) = (x : ∀ k, D k) := rfl

/-! ## The prescribed cokernel -/

/-- Evaluation of a tail section at its first coordinate. -/
def tailEval (n : ℕ) : ↥(supportedAbove 𝕜 D n) →ₗ[𝕜] D n where
  toFun x := (x : ∀ k, D k) n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem tailEval_surjective (n : ℕ) : Function.Surjective (tailEval (𝕜 := 𝕜) (D := D) n) := by
  classical
  intro d
  refine ⟨⟨Pi.single n d, fun k hk => ?_⟩, ?_⟩
  · exact Pi.single_eq_of_ne (by omega) d
  · exact Pi.single_eq_same n d

theorem ker_tailEval (n : ℕ) :
    LinearMap.ker (tailEval (𝕜 := 𝕜) (D := D) n)
      = LinearMap.range (prescribedBond (𝕜 := 𝕜) (D := D) n) := by
  ext x
  constructor
  · intro hx
    have hxn : (x : ∀ k, D k) n = 0 := hx
    refine ⟨⟨(x : ∀ k, D k), fun k hk => ?_⟩, Subtype.ext rfl⟩
    rcases Nat.lt_or_ge k n with h | h
    · exact x.2 k h
    · have : k = n := by omega
      rw [this]
      exact hxn
  · rintro ⟨y, rfl⟩
    show ((y : ∀ k, D k)) n = 0
    exact y.2 n (by omega)

/-- **The link cokernel is the prescribed module.** -/
noncomputable def prescribedCokernelEquiv (n : ℕ) :
    (↥(supportedAbove 𝕜 D n) ⧸ LinearMap.range (prescribedBond (𝕜 := 𝕜) (D := D) n)) ≃ₗ[𝕜] D n :=
  (Submodule.quotEquivOfEq _ _ (ker_tailEval n).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (tailEval_surjective n))

/-! ## Global derived vanishing -/

/-- The correction section: in each coordinate only finitely many terms contribute. -/
def tailCorrection (b : ∀ n, ↥(supportedAbove 𝕜 D n)) (n : ℕ) : ∀ k, D k :=
  fun k => ∑ j ∈ Finset.Ico n (k + 1), (b j : ∀ k, D k) k

theorem tailCorrection_mem (b : ∀ n, ↥(supportedAbove 𝕜 D n)) (n : ℕ) :
    tailCorrection b n ∈ supportedAbove 𝕜 D n := by
  intro k hk
  have : Finset.Ico n (k + 1) = ∅ := Finset.Ico_eq_empty (by omega)
  rw [tailCorrection, this, Finset.sum_empty]

/-- **The Roos difference of the prescribed-deficit tower is onto.** -/
theorem inverseDifference_surjective_prescribed :
    Function.Surjective (inverseDifference (fun n => ↥(supportedAbove 𝕜 D n))
      (prescribedBond (𝕜 := 𝕜) (D := D))) := by
  intro b
  refine ⟨fun n => ⟨tailCorrection b n, tailCorrection_mem b n⟩, ?_⟩
  funext n
  refine Subtype.ext ?_
  funext k
  show tailCorrection b n k - (tailCorrection b (n + 1)) k = (b n : ∀ k, D k) k
  rcases Nat.lt_or_ge k n with hk | hk
  · have h1 : Finset.Ico n (k + 1) = ∅ := Finset.Ico_eq_empty (by omega)
    have h2 : Finset.Ico (n + 1) (k + 1) = ∅ := Finset.Ico_eq_empty (by omega)
    rw [tailCorrection, tailCorrection, h1, h2]
    simp [(b n).2 k hk]
  · have hlt : n < k + 1 := by omega
    have hbot := Finset.sum_eq_sum_Ico_succ_bot hlt fun j => (b j : ∀ k, D k) k
    rw [tailCorrection, tailCorrection, hbot]
    abel

/-- **Prescribed deficits with vanishing `lim¹`.**  Every link cokernel is the prescribed module,
and the derived limit still vanishes. -/
theorem prescribed_deficit_and_derived_vanishing :
    (∀ n, Nonempty ((↥(supportedAbove 𝕜 D n)
        ⧸ LinearMap.range (prescribedBond (𝕜 := 𝕜) (D := D) n)) ≃ₗ[𝕜] D n)) ∧
      Subsingleton (DerivedLimitOne (fun n => ↥(supportedAbove 𝕜 D n))
        (prescribedBond (𝕜 := 𝕜) (D := D))) := by
  refine ⟨fun n => ⟨prescribedCokernelEquiv n⟩, ?_⟩
  change Subsingleton ((∀ n, ↥(supportedAbove 𝕜 D n))
    ⧸ LinearMap.range (inverseDifference (fun n => ↥(supportedAbove 𝕜 D n))
      (prescribedBond (𝕜 := 𝕜) (D := D))))
  rw [Submodule.Quotient.subsingleton_iff]
  exact LinearMap.range_eq_top.mpr inverseDifference_surjective_prescribed

end BoundaryMigration

end GaloisForLFunctions.HTGeometry
