import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.IsingStressCalibration
import Mathlib.Analysis.Convex.Combination

/-!
# Joint expectations of diagonal stress observables

One basis law governs all diagonal observables. At prescribed ground
energy, its nonzero weights are confined to the ground configurations.
This identifies the full set of attainable vector stresses.
-/

open Set
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace FiniteStrain

variable {ι V W : Type*} [Fintype ι]
variable [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Simultaneous expectation of a vector of diagonal observables. -/
def diagonalVectorMean (p : ι → ℝ) (b : ι → V) : V := ∑ i, p i • b i

/-- Simultaneous readout in a normalized pure state. -/
def pureDiagonalVectorMean (ψ : EuclideanSpace ℂ ι) (b : ι → V) : V :=
  diagonalVectorMean (pureBasisLaw ψ) b

theorem diagonalVectorMean_point (b : ι → V) (i : ι) :
    diagonalVectorMean (pointBasisLaw i) b = b i := by
  classical
  simp [diagonalVectorMean, pointBasisLaw, ite_smul]

theorem diagonalVectorMean_mix (p q : ι → ℝ) (b : ι → V) (t : ℝ) :
    diagonalVectorMean (mixBasisLaw p q t) b =
      (1 - t) • diagonalVectorMean p b + t • diagonalVectorMean q b := by
  simp only [diagonalVectorMean, mixBasisLaw, add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum]

theorem diagonalVectorMean_map (L : V →ₗ[ℝ] W) (p : ι → ℝ) (b : ι → V) :
    L (diagonalVectorMean p b) = diagonalVectorMean p (fun i => L (b i)) := by
  simp only [diagonalVectorMean, map_sum, map_smul]

theorem diagonalVectorMean_real (p b : ι → ℝ) :
    diagonalVectorMean p b = diagonalMean p b := rfl

/-- With support confined to a finite set, attainable means are exactly
the convex hull of its readouts. -/
theorem diagonalVectorMeanRange_eq_convexHull (S : Finset ι) (b : ι → V) :
    {v | ∃ p, IsBasisLaw p ∧ (∀ i, p i ≠ 0 → i ∈ S) ∧ diagonalVectorMean p b = v} =
      convexHull ℝ (b '' (S : Set ι)) := by
  classical
  let C : Set V := {v | ∃ p, IsBasisLaw p ∧ (∀ i, p i ≠ 0 → i ∈ S) ∧ diagonalVectorMean p b = v}
  change C = _
  apply le_antisymm
  · rintro _ ⟨p, hp, hsupport, rfl⟩
    have hz (i : ι) (_ : i ∈ Finset.univ) (hi : i ∉ S) : p i = 0 :=
      Classical.byContradiction fun h => hi (hsupport i h)
    have hsum : ∑ i ∈ S, p i = 1 :=
      (Finset.sum_subset (Finset.subset_univ S) hz).trans hp.2
    have hmean : (∑ i ∈ S, p i • b i) = diagonalVectorMean p b :=
      Finset.sum_subset (Finset.subset_univ S) fun i hi hn => by rw [hz i hi hn, zero_smul]
    rw [← hmean]
    exact (convex_convexHull ℝ (b '' (S : Set ι))).sum_mem (fun i _ => hp.1 i) hsum
      (fun i hi => subset_convexHull ℝ _ ⟨i, hi, rfl⟩)
  · apply convexHull_min
    · rintro _ ⟨i, hi, rfl⟩
      refine ⟨pointBasisLaw i, isBasisLaw_point i, ?_, diagonalVectorMean_point b i⟩
      intro j hj
      by_cases he : j = i
      · rwa [he]
      · exact (hj (by simp [pointBasisLaw, he])).elim
    · intro x hx y hy r t hr ht hrt
      obtain ⟨p, hp, hps, rfl⟩ := hx
      obtain ⟨q, hq, hqs, rfl⟩ := hy
      have ht₁ : t ≤ 1 := by linarith only [hr, hrt]
      have he : 1 - t = r := by linarith only [hrt]
      refine ⟨mixBasisLaw p q t, isBasisLaw_mix hp hq ht ht₁, ?_, ?_⟩
      · intro i hi
        by_contra hn
        have hpz : p i = 0 := Classical.byContradiction fun h => hn (hps i h)
        have hqz : q i = 0 := Classical.byContradiction fun h => hn (hqs i h)
        exact hi (by simp [mixBasisLaw, hpz, hqz])
      · rw [diagonalVectorMean_mix, he]

variable [Nonempty ι]

/-- Pure ground states realize every convex combination of ground
configuration stress vectors. -/
theorem pureGroundVectorStressRange_eq_convexHull (a : ι → ℝ) (b : ι → V) :
    {v | ∃ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 ∧ pureDiagonalMean ψ a = groundEnergy a ∧
      pureDiagonalVectorMean ψ b = v} =
      convexHull ℝ (b '' (groundConfigurations a : Set ι)) := by
  rw [← diagonalVectorMeanRange_eq_convexHull]
  ext v
  constructor
  · rintro ⟨ψ, hψ, he, hv⟩
    have h := isBasisLaw_pure ψ hψ
    exact ⟨pureBasisLaw ψ, h, (diagonalMean_eq_groundEnergy_iff a h).mp he, hv⟩
  · rintro ⟨p, hp, hs, hv⟩
    obtain ⟨ψ, hψ, hprob⟩ := exists_pureBasisLaw hp
    refine ⟨ψ, hψ, ?_, ?_⟩
    · rw [pureDiagonalMean, hprob]
      exact (diagonalMean_eq_groundEnergy_iff a hp).mpr hs
    · rwa [pureDiagonalVectorMean, hprob]

omit [Nonempty ι] in
/-- For diagonal observables, the joint energy–stress diagram is the
convex hull of the basis energy–stress pairs. -/
theorem pureEnergyStressRange_eq_convexHull (a : ι → ℝ) (b : ι → V) :
    {z : ℝ × V | ∃ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 ∧
      (pureDiagonalMean ψ a, pureDiagonalVectorMean ψ b) = z} =
      convexHull ℝ (range (fun i => (a i, b i))) := by
  classical
  have hpair (p : ι → ℝ) : diagonalVectorMean p (fun i => (a i, b i)) =
      (diagonalMean p a, diagonalVectorMean p b) := by
    exact Prod.ext
      (by simp only [diagonalVectorMean, diagonalMean, Prod.fst_sum, Prod.smul_fst, smul_eq_mul])
      (by simp only [diagonalVectorMean, Prod.snd_sum, Prod.smul_snd])
  have hset : range (fun i => (a i, b i)) = (fun i => (a i, b i)) '' ((Finset.univ : Finset ι) : Set ι) := by
    rw [Finset.coe_univ, image_univ]
  rw [hset, ← diagonalVectorMeanRange_eq_convexHull]
  ext z
  constructor
  · rintro ⟨ψ, hψ, h⟩
    exact ⟨pureBasisLaw ψ, isBasisLaw_pure ψ hψ, fun i _ => Finset.mem_univ i, (hpair _).trans h⟩
  · rintro ⟨p, hp, _, h⟩
    obtain ⟨ψ, hψ, hprob⟩ := exists_pureBasisLaw hp
    refine ⟨ψ, hψ, ?_⟩
    rwa [pureDiagonalMean, pureDiagonalVectorMean, hprob, ← hpair]

/-- Every linear component of the joint ground stress fills its complete
scalar interval. Its endpoints give the two energy slopes in that direction. -/
theorem groundStressHull_linearImage (a : ι → ℝ) (b : ι → V) (L : V →ₗ[ℝ] ℝ) :
    L '' convexHull ℝ (b '' (groundConfigurations a : Set ι)) =
      Icc (groundStressMin a (fun i => L (b i))) (groundStressMax a (fun i => L (b i))) := by
  rw [← pureGroundVectorStressRange_eq_convexHull, ← pureGroundStressRange_eq_Icc]
  have hm (ψ : EuclideanSpace ℂ ι) :
      L (pureDiagonalVectorMean ψ b) = pureDiagonalMean ψ (fun i => L (b i)) := by
    rw [pureDiagonalVectorMean, diagonalVectorMean_map, diagonalVectorMean_real]
    rfl
  ext s
  constructor
  · rintro ⟨v, ⟨ψ, hψ, ha, rfl⟩, rfl⟩
    exact ⟨ψ, hψ, ha, (hm ψ).symm⟩
  · rintro ⟨ψ, hψ, ha, hs⟩
    exact ⟨pureDiagonalVectorMean ψ b, ⟨ψ, hψ, ha, rfl⟩, (hm ψ).trans hs⟩

omit [Nonempty ι] in
/-- A budget cuts the energy–stress hull by a half-space before taking
its stress projection. -/
theorem pureStressBudgetRange_eq_projection (a : ι → ℝ) (b : ι → V) (B : ℝ) :
    {v | ∃ ψ : EuclideanSpace ℂ ι, ‖ψ‖ = 1 ∧ pureDiagonalMean ψ a ≤ B ∧
      pureDiagonalVectorMean ψ b = v} =
      Prod.snd '' (convexHull ℝ (range (fun i => (a i, b i))) ∩ {z : ℝ × V | z.1 ≤ B}) := by
  rw [← pureEnergyStressRange_eq_convexHull]
  ext v
  constructor
  · rintro ⟨ψ, hψ, ha, rfl⟩
    exact ⟨(pureDiagonalMean ψ a, pureDiagonalVectorMean ψ b), ⟨⟨ψ, hψ, rfl⟩, ha⟩, rfl⟩
  · rintro ⟨z, ⟨⟨ψ, hψ, rfl⟩, ha⟩, rfl⟩
    exact ⟨ψ, hψ, ha, rfl⟩

end FiniteStrain

/-- Changing several onsite strain components gives a joint ground
stress polytope. Its vertices come from unstrained ground configurations. -/
theorem isingStrain_jointGroundStress_eq_convexHull {n : ℕ} {κ : Type*}
    (h : Fin (n + 2) → ℝ) (d : κ → Fin (n + 2) → ℝ) (J : Fin (n + 1) → ℝ) :
    let a := pathDiagEnergy (strainPath h (fun _ => 0) J 0)
    let b := fun x j => onsiteResponse (d j) x
    {v : κ → ℝ | ∃ ψ : EuclideanSpace ℂ (FiniteQubitConfiguration (Fin (n + 2))),
      ‖ψ‖ = 1 ∧ FiniteStrain.pureDiagonalMean ψ a = FiniteStrain.groundEnergy a ∧
        FiniteStrain.pureDiagonalVectorMean ψ b = v} =
      convexHull ℝ (b '' (FiniteStrain.groundConfigurations a : Set _)) :=
  FiniteStrain.pureGroundVectorStressRange_eq_convexHull _ _

#print axioms FiniteStrain.diagonalVectorMeanRange_eq_convexHull
#print axioms FiniteStrain.pureGroundVectorStressRange_eq_convexHull
#print axioms FiniteStrain.pureEnergyStressRange_eq_convexHull
#print axioms FiniteStrain.groundStressHull_linearImage
#print axioms FiniteStrain.pureStressBudgetRange_eq_projection
#print axioms isingStrain_jointGroundStress_eq_convexHull

end

end GaloisForLFunctions.HTGeometry
