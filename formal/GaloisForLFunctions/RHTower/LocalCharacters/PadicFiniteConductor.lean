import GaloisForLFunctions.HTGeometry.Topology.ProfiniteCircleCharacters
import GaloisForLFunctions.RHTower.FieldOnePadicValuationUnitDecomposition
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Finite conductor of continuous p-adic unit characters

Every continuous circle character of `ℤ_pˣ` factors uniquely through the
units of `ℤ / p^n ℤ` for some `n`. The character kernel is open because the
circle has no small subgroups. Compactness then places one congruence kernel
inside it: these closed kernels decrease to the identity. This is the
finite-conductor step of Lemma 3.3 of arXiv:2610.23742 for the actual p-adic
unit group used by the local Tate integrals.
-/

noncomputable section
namespace GaloisForLFunctions.RHTower.LocalCharacters
open GaloisForLFunctions.HTGeometry

variable (p : ℕ) [Fact p.Prime]

local instance padicUnitTotallyDisconnected : TotallyDisconnectedSpace ℤ_[p]ˣ :=
  ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn
    (fun _ _ h => Units.ext h) (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩

/-- Deeper congruence kernels are contained in shallower ones. -/
theorem reduction_ker_antitone : Antitone (fun n => (fieldOnePadicUnitReduction p n).ker) := by
  intro m n hmn u hu
  have h : PadicInt.toZModPow n (u : ℤ_[p]) = 1 := congrArg Units.val hu
  apply Units.ext
  change PadicInt.toZModPow m (u : ℤ_[p]) = 1
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hmn]
  change (ZMod.castHom (pow_dvd_pow p hmn) (ZMod (p ^ m)))
    (PadicInt.toZModPow n (u : ℤ_[p])) = 1
  rw [h, map_one]

/-- Reduction at every depth separates the identity in the actual unit group. -/
theorem eq_one_of_reductions (u : ℤ_[p]ˣ)
    (h : ∀ n, fieldOnePadicUnitReduction p n u = 1) : u = 1 := by
  apply Units.ext
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  have hu : PadicInt.toZModPow n (u : ℤ_[p]) = 1 := congrArg Units.val (h n)
  simpa only [map_one, Units.val_one] using hu

/-- Every continuous unit character kills a congruence kernel of finite depth. -/
theorem exists_reduction_ker_le (χ : ℤ_[p]ˣ →ₜ* Circle) :
    ∃ n : ℕ, (fieldOnePadicUnitReduction p n).ker ≤ χ.toMonoidHom.ker := by
  let K : ℕ → Set ℤ_[p]ˣ := fun n => (fieldOnePadicUnitReduction p n).ker
  have hc (n : ℕ) : IsClosed (K n) :=
    isClosed_singleton.preimage (fieldOnePadicUnitReduction_continuous p n)
  have hm : Antitone K := reduction_ker_antitone p
  have hi : (χ.toMonoidHom.ker : Set ℤ_[p]ˣ)ᶜ ∩ ⋂ n, K n = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro u ⟨hu, huK⟩
    have hu1 : u = 1 := eq_one_of_reductions p u (fun n => Set.mem_iInter.mp huK n)
    apply hu
    rw [hu1]
    exact χ.toMonoidHom.ker.one_mem
  obtain ⟨n, hn⟩ := (ProfiniteCircleCharacters.isOpen_ker χ).isClosed_compl.isCompact
    |>.elim_directed_family_closed K hc hi hm.directed_ge
  refine ⟨n, fun u hu => ?_⟩
  by_contra hχ
  have hmem : u ∈ (χ.toMonoidHom.ker : Set ℤ_[p]ˣ)ᶜ ∩ K n := ⟨hχ, hu⟩
  rw [hn] at hmem
  exact hmem

/-- A continuous unit character is exactly a character of one finite residue-unit group. -/
theorem exists_unique_finite_character (χ : ℤ_[p]ˣ →ₜ* Circle) :
    ∃ n : ℕ, ∃! θ : (ZMod (p ^ n))ˣ →* Circle,
      ∀ u : ℤ_[p]ˣ, θ (fieldOnePadicUnitReduction p n u) = χ u := by
  obtain ⟨n, hn⟩ := exists_reduction_ker_le p χ
  let θ := (fieldOnePadicUnitReduction p n).liftOfSurjective
    (fieldOnePadicUnitReduction_surjective p n) ⟨χ.toMonoidHom, hn⟩
  have hθ (u : ℤ_[p]ˣ) : θ (fieldOnePadicUnitReduction p n u) = χ u := by
    simp [θ]
  refine ⟨n, θ, hθ, ?_⟩
  intro ψ hψ
  apply MonoidHom.ext
  intro v
  obtain ⟨u, rfl⟩ := fieldOnePadicUnitReduction_surjective p n v
  exact (hψ u).trans (hθ u).symm

#print axioms exists_reduction_ker_le
#print axioms exists_unique_finite_character

end GaloisForLFunctions.RHTower.LocalCharacters
