import GaloisForLFunctions.HTGeometry.GammaIrreversibleClockHorizon
import Mathlib.Data.Set.Finite.Basic

open Function Set
namespace GaloisForLFunctions
noncomputable section

/-- One step of the Gamma horizon clock forgets exactly the first natural-number label. -/
def bgv_gammaClockFiberEquiv (eta : ℕ → ℕ) :
    {omega : ℕ → ℕ // gammaHorizonClock omega = gammaHorizonClock eta} ≃ ℕ where
  toFun omega := omega.val 0
  invFun n := ⟨Function.update eta 0 n, by
    funext k
    simp [gammaHorizonClock]⟩
  left_inv omega := by
    apply Subtype.ext
    funext k
    cases k with
    | zero => simp
    | succ k =>
      have h := congrFun omega.property k
      simpa [gammaHorizonClock] using (Nat.add_right_cancel h).symm
  right_inv n := by simp

/-- Every nonempty clock fibre is infinite; branching alone does not force stabilization. -/
theorem bgv_gammaClock_fiber_infinite (eta : ℕ → ℕ) :
    {omega : ℕ → ℕ | gammaHorizonClock omega = gammaHorizonClock eta}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => (bgv_gammaClockFiberEquiv eta).symm n |>.val)
  · intro m n h
    have hsub : (bgv_gammaClockFiberEquiv eta).symm m =
        (bgv_gammaClockFiberEquiv eta).symm n := Subtype.ext h
    exact (bgv_gammaClockFiberEquiv eta).symm.injective hsub
  · intro n
    exact ((bgv_gammaClockFiberEquiv eta).symm n).property

/-- Every present clock image has a predecessor in the initial gap. -/
theorem bgv_gammaClock_image_gap :
    gammaHorizonClock '' (Set.range gammaHorizonClock)ᶜ = Set.range gammaHorizonClock := by
  apply Set.Subset.antisymm (Set.image_subset_range _ _)
  rintro z ⟨eta, rfl⟩
  refine ⟨Function.update eta 0 0, ?_, ?_⟩
  · rintro ⟨omega, h⟩
    have h0 := congrFun h 0
    simp [gammaHorizonClock] at h0
  · funext k
    simp [gammaHorizonClock]

/-- The initial gap is infinite: an unrestricted tail remains after the first zero label. -/
theorem bgv_gammaClock_gap_infinite : (Set.range gammaHorizonClock)ᶜ.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => Function.update (fun _ => n) 0 0)
  · intro m n h
    have h1 := congrFun h 1
    simpa using h1
  · intro n
    rintro ⟨omega, h⟩
    have h0 := congrFun h 0
    simp [gammaHorizonClock] at h0

/-- The age-`d` loss layer is exactly the histories whose minimum label is `d`. -/
theorem bgv_gammaClock_loss_layer (eta : ℕ → ℕ) (d : ℕ) :
    eta ∈ Set.range gammaHorizonClock^[d] \ Set.range gammaHorizonClock^[d + 1] ↔
      (∀ k, d ≤ eta k) ∧ ∃ k, eta k = d := by
  simp only [Set.mem_sdiff, mem_range_gammaHorizonClock_iterate_iff]
  constructor
  · rintro ⟨h, hn⟩
    refine ⟨h, ?_⟩
    push Not at hn
    obtain ⟨k, hk⟩ := hn
    exact ⟨k, Nat.le_antisymm (Nat.le_of_lt_succ hk) (h k)⟩
  · rintro ⟨h, k, hk⟩
    refine ⟨h, ?_⟩
    intro hn
    have hh := hn k
    rw [hk] at hh
    exact Nat.not_succ_le_self d hh

/-- The actual restricted Gamma map has exactly the same countably infinite fibres. -/
def bgv_actualGammaHorizonFiberEquiv (eta : ℕ → ℕ) :
    {z : gammaConstrainedHorizon // gammaConstrainedHorizonMap z =
      gammaConstrainedHorizonMap (gammaConstrainedHorizonHomeomorph eta)} ≃ ℕ := by
  let e := gammaConstrainedHorizonHomeomorph.toEquiv
  have h (omega : ℕ → ℕ) :
      gammaHorizonClock omega = gammaHorizonClock eta ↔
        gammaConstrainedHorizonMap (e omega) = gammaConstrainedHorizonMap (e eta) := by
    change _ ↔ gammaConstrainedHorizonMap (gammaConstrainedHorizonHomeomorph omega) =
      gammaConstrainedHorizonMap (gammaConstrainedHorizonHomeomorph eta)
    rw [← gammaConstrainedHorizonHomeomorph_intertwines,
      ← gammaConstrainedHorizonHomeomorph_intertwines]
    exact gammaConstrainedHorizonHomeomorph.injective.eq_iff.symm
  exact (Equiv.subtypeEquiv e h).symm.trans (bgv_gammaClockFiberEquiv eta)

/-- An actual Gamma fibre on the constrained horizon is infinite. -/
theorem bgv_actualGammaHorizon_fiber_infinite (eta : ℕ → ℕ) :
    {z : gammaConstrainedHorizon | gammaConstrainedHorizonMap z =
      gammaConstrainedHorizonMap (gammaConstrainedHorizonHomeomorph eta)}.Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => (bgv_actualGammaHorizonFiberEquiv eta).symm n |>.val)
  · intro m n h
    exact (bgv_actualGammaHorizonFiberEquiv eta).symm.injective (Subtype.ext h)
  · intro n
    exact ((bgv_actualGammaHorizonFiberEquiv eta).symm n).property

end
end GaloisForLFunctions
