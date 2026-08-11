import GaloisForLFunctions.HTGeometry.TripticNormalForm
import GaloisForLFunctions.HTGeometry.TripticJetCombinationHypertranscendence

/-!
# The kernel of the triptic orbit-residue divisor

A finite set of base points can be replaced by a transversal of its classes, with the class of
`-(τ/2+1/2)` always represented by that point itself.  The correction built on such a transversal is
a jet combination with distinct classes, so it is hypertranscendental as soon as one of its weights
is nonzero — and its weights are the divisor values of the source.

The source itself need not be a quotient of entire functions: the kernel theorem presents the
corrected function, off a countable set, as an explicitly realized differentially algebraic
function, and the correction is realized too, so the sum realizes the source.  Differential
algebraicity of the source therefore forces it on the correction, and the divisor must vanish.

* `exists_classTransversal`;
* `additiveOrbitalDivisorAt_eq_zero_of_differentiallyAlgebraic` — the kernel inclusion;
* `differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero` — the kernel of `R_trip`.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero

attribute [local instance] meromorphicEllipticCompositumComplexAlgebraMero

/-- **A finite set of points has a transversal of its classes**, avoiding a prescribed class, which
is represented by the prescribed point. -/
theorem exists_classTransversal (τ σ : ℂ) (P : Finset ℂ) (b : ℂ) :
    ∃ P₀ : Finset ℂ,
      (∀ q ∈ P₀, ∀ q' ∈ P₀, q ≠ q' → ¬ SameClass τ σ q q') ∧
      (∀ q ∈ P₀, ¬ SameClass τ σ q b) ∧
      (∀ q ∈ P, ∃ r ∈ insert b P₀, SameClass τ σ q r) := by
  classical
  induction P using Finset.induction with
  | empty => exact ⟨∅, by simp, by simp, by simp⟩
  | insert a P ha ih =>
      obtain ⟨P₀, hdist, hb, hrep⟩ := ih
      by_cases hcase : ∃ r ∈ insert b P₀, SameClass τ σ a r
      · refine ⟨P₀, hdist, hb, fun q hq ↦ ?_⟩
        rcases Finset.mem_insert.mp hq with rfl | hq'
        · exact hcase
        · exact hrep q hq'
      · push Not at hcase
        refine ⟨insert a P₀, ?_, ?_, ?_⟩
        · intro q hq q' hq' hne
          rcases Finset.mem_insert.mp hq with rfl | hq2
          · rcases Finset.mem_insert.mp hq' with rfl | hq2'
            · exact absurd rfl hne
            · exact hcase q' (Finset.mem_insert_of_mem hq2')
          · rcases Finset.mem_insert.mp hq' with rfl | hq2'
            · exact fun hcl ↦ hcase q (Finset.mem_insert_of_mem hq2) (sameClass_symm hcl)
            · exact hdist q hq2 q' hq2' hne
        · intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq2
          · exact hcase b (Finset.mem_insert_self b P₀)
          · exact hb q hq2
        · intro q hq
          rcases Finset.mem_insert.mp hq with rfl | hq2
          · exact ⟨q, Finset.mem_insert_of_mem (Finset.mem_insert_self q P₀), sameClass_refl τ σ q⟩
          · obtain ⟨r, hr, hcl⟩ := hrep q hq2
            rcases Finset.mem_insert.mp hr with rfl | hr2
            · exact ⟨r, Finset.mem_insert_self r _, hcl⟩
            · exact ⟨r, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr2), hcl⟩

theorem thetaTranslationNonresonant_of_not_sameClass {τ σ q q' : ℂ}
    (h : ¬ SameClass τ σ q q') : ThetaTranslationNonresonant σ τ (q - q') := by
  intro hcon
  obtain ⟨a, b, n, hab⟩ := hcon
  exact h ⟨a, n, b, by linear_combination hab⟩

theorem thetaTranslationNonresonant_of_not_sameClass_neg {τ σ q b : ℂ}
    (h : ¬ SameClass τ σ q b) : ThetaTranslationNonresonant σ τ (b - q) := by
  intro hcon
  obtain ⟨a, c, n, hac⟩ := hcon
  exact h ⟨-a, -n, -c, by push_cast; linear_combination -hac⟩

section

variable {F : ℂ → ℂ} {τ σ : ℂ} (hF : MeromorphicOn F (Set.univ : Set ℂ))
  (hper : PeriodicOneGerm F) {Cst : ℂ} (hmixed : MixedConstGerm F τ σ Cst)
  (hτ : 0 < τ.im) (hσ : 0 < σ.im) (hindep : IndepPeriods τ σ)
  (hindepτ : LinearIndependent ℝ ![(1 : ℂ), τ]) (hindepσ : LinearIndependent ℝ ![(1 : ℂ), σ])

include hF in
/-- Off every represented class the source has no divisor. -/
theorem additiveOrbitalDivisorAt_eq_zero_of_no_representative (P : Finset ℂ)
    (hP : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ F (w + σ) - F w) z < 0 →
      ∃ q ∈ P, SameClass τ σ q z)
    {p : ℂ} (hp : ¬ ∃ q ∈ P, SameClass τ σ q p) {ℓ : ℤ} (hℓ : ℓ < 0) :
    additiveOrbitalDivisorAt F σ p ℓ = 0 := by
  have hUmero : MeromorphicOn (fun w ↦ F (w + σ) - F w) (Set.univ : Set ℂ) := fun y _ ↦
    (meromorphicAt_comp_add.mpr (hF (y + σ) (Set.mem_univ _))).sub (hF y (Set.mem_univ y))
  refine additiveOrbitalDivisorAt_eq_zero_of_terms F σ p _ fun m ↦ ?_
  by_contra hne
  have hpole : meromorphicOrderAt (fun w ↦ F (w + σ) - F w) (p + (m : ℂ) * σ) < 0 :=
    meromorphicOrderAt_neg_of_laurentCoeff_ne_zero (hUmero _ (Set.mem_univ _)) hℓ hne
  obtain ⟨q, hqP, hq⟩ := hP _ hpole
  obtain ⟨u, v, k, huvk⟩ := hq
  exact hp ⟨q, hqP, ⟨u, v, k + m, by push_cast; linear_combination huvk⟩⟩

include hF hper hmixed hτ hσ hindep hindepτ hindepσ in
/-- **The kernel inclusion.**  A differentially algebraic member of the triptic class has vanishing
orbital divisor. -/
theorem additiveOrbitalDivisorAt_eq_zero_of_differentiallyAlgebraic
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods τ σ))
    (hDA : DifferentiallyAlgebraic (toMeromorphicNFOn F (Set.univ : Set ℂ)))
    (p : ℂ) (ℓ : ℤ) (hℓ : ℓ < 0) : additiveOrbitalDivisorAt F σ p ℓ = 0 := by
  classical
  by_contra hne
  obtain ⟨i, rfl⟩ : ∃ i : ℕ, ℓ = -((i : ℤ) + 1) := ⟨(-ℓ - 1).toNat, by omega⟩
  obtain ⟨P, hPcl⟩ := exists_finset_boundaryPoleClasses hF hper hmixed hindepτ
  obtain ⟨L, hL⟩ := exists_orderBound_boundary hF hper hmixed hindepτ
  obtain ⟨P₀, hdist, hbase, hrep⟩ :=
    exists_classTransversal τ σ P (-(gammaPresentationShift σ))
  set P' : Finset ℂ := insert (-(gammaPresentationShift σ)) P₀ with hP'
  set J : ℕ := max ((-L).toNat) (i + 1) with hJdef
  -- every pole class is represented in the transversal
  have hP : ∀ z : ℂ, meromorphicOrderAt (fun w ↦ F (w + σ) - F w) z < 0 →
      ∃ q ∈ P', SameClass τ σ q z := by
    intro z hz
    obtain ⟨u, v, hmem⟩ := hPcl z hz
    obtain ⟨r, hr, hcl⟩ := hrep _ hmem
    refine ⟨r, hr, sameClass_trans (sameClass_symm hcl) ?_⟩
    refine ⟨-u, -v, 0, ?_⟩
    simp only [zsmul_eq_mul]
    push_cast
    ring
  have hJ : ∀ (z : ℂ) (ℓ' : ℤ), ℓ' < -(J : ℤ) →
      laurentCoeff (fun w ↦ F (w + σ) - F w) z ℓ' = 0 := by
    intro z ℓ' hℓ'
    refine hL _ _ ?_
    have hbnd : (-L) ≤ (((-L).toNat : ℕ) : ℤ) := Int.self_le_toNat _
    have hle : ((-L).toNat : ℤ) ≤ (J : ℤ) := by
      exact_mod_cast Nat.le_max_left _ _
    omega
  -- the class of `p` is represented, and carries the nonzero weight
  have hpcls : ∃ q ∈ P', SameClass τ σ q p := by
    by_contra hcon
    exact hne (additiveOrbitalDivisorAt_eq_zero_of_no_representative hF P' hP hcon (by omega))
  obtain ⟨q₀, hq₀P, hq₀⟩ := hpcls
  have hneg : (-((i : ℤ) + 1)) < 0 := by omega
  have hq₀ne : additiveOrbitalDivisorAt F σ q₀ (-((i : ℤ) + 1)) ≠ 0 := by
    rw [additiveOrbitalDivisorAt_congr_sameClass hF hper hmixed hq₀ hneg]
    exact hne
  have hcoeff : gammaCorrectionCoeff τ σ F P' q₀ i ≠ 0 := by
    refine div_ne_zero hq₀ne (mul_ne_zero (mul_ne_zero (pow_ne_zero i (by norm_num)) ?_) ?_)
    · exact_mod_cast i.factorial_ne_zero
    · exact classCount_ne_zero_of_exists ⟨q₀, hq₀P, sameClass_refl τ σ q₀⟩
  -- the corrected function has vanishing divisor, hence is realized and differentially algebraic
  have hvan := gammaCorrection_vanishing_divisor_of_represents hF hper hmixed hτ hσ hindep P' J
    hP hJ
  have hGmero : MeromorphicOn (fun z ↦ F z - gammaCorrection τ σ F P' J z)
      (Set.univ : Set ℂ) := fun z _ ↦
    (hF z (Set.mem_univ z)).sub
      (meromorphicOn_jetCombination hτ hσ (gammaCorrectionCoeff τ σ F P') P' J z (Set.mem_univ z))
  have hGper : PeriodicOneGerm (fun z ↦ F z - gammaCorrection τ σ F P' J z) :=
    periodicOneGerm_sub hper (periodicOneGerm_jetCombination τ σ (gammaCorrectionCoeff τ σ F P')
      P' J)
  have hGmixed : MixedConstGerm (fun z ↦ F z - gammaCorrection τ σ F P' J z) τ σ
      (Cst - gammaCorrectionConst τ σ F P' J) :=
    mixedConstGerm_sub hmixed
      (mixedConstGerm_jetCombination hτ hσ (gammaCorrectionCoeff τ σ F P') P' J)
  obtain ⟨-, x, g, S, hx, hxmem, hScount, hGS⟩ :=
    exists_realizesMero_of_vanishing_orbital_divisor hGmero hGper hGmixed hτ hσ
      (indepTriple_of_indepPeriods hindep) hindepτ hindepσ (fun p' ℓ' hℓ' ↦ hvan p' ℓ' hℓ')
  -- the correction is realized and hypertranscendental
  obtain ⟨X, hX, hHT⟩ := exists_realizesMero_jetCombination_option hτ hσ hperiods P₀ J
    (gammaCorrectionCoeff τ σ F P')
    (fun q hq ↦ thetaTranslationNonresonant_of_not_sameClass_neg (hbase q hq))
    (fun q hq q' hq' hqq' ↦ thetaTranslationNonresonant_of_not_sameClass (hdist q hq q' hq' hqq'))
    hq₀P (by omega : i < J) hcoeff
  -- the source is realized by the sum
  have hsum : RealizesMero (x + X) (g + gammaCorrection τ σ F P' J) := realizesMero_add hx hX
  have hoff : ∀ z ∉ S, F z = (g + gammaCorrection τ σ F P' J) z := by
    intro z hz
    have hz' := hGS z hz
    simp only [Pi.add_apply]
    linear_combination hz'
  have hNF : toMeromorphicNFOn F (Set.univ : Set ℂ)
      = toMeromorphicNFOn (g + gammaCorrection τ σ F P' J) (Set.univ : Set ℂ) :=
    toMeromorphicNFOn_eq_of_eq_off_countable hF (meromorphicOn_of_realizesMero hsum) hScount hoff
  rw [hNF] at hDA
  have hxX : x + X ∈ daOverRatFuncField :=
    (mem_daOverRatFuncField_iff _).mpr (differentialAlgebraicOver_of_realizesMero hsum hDA)
  have hXmem : X ∈ daOverRatFuncField := by
    have hsub := sub_mem hxX hxmem
    simpa using hsub
  exact hHT (differentialAlgebraicOver_complex_of_ratFunc
    ((mem_daOverRatFuncField_iff X).mp hXmem))

include hF hper hmixed hτ hσ hindep hindepτ hindepσ in
/-- **The kernel of the triptic orbit-residue divisor** is the differentially algebraic part of the
class: a member of the class is differentially algebraic exactly when its orbital divisor vanishes
identically. -/
theorem differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero
    (hperiods : LinearIndependent ℚ (ellipticGammaSourcePeriods τ σ)) :
    DifferentiallyAlgebraic (toMeromorphicNFOn F (Set.univ : Set ℂ))
      ↔ ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 → additiveOrbitalDivisorAt F σ p ℓ = 0 := by
  constructor
  · intro hDA
    exact additiveOrbitalDivisorAt_eq_zero_of_differentiallyAlgebraic hF hper hmixed hτ hσ hindep
      hindepτ hindepσ hperiods hDA
  · intro hzero
    exact (differentiallyAlgebraic_toMeromorphicNFOn_of_vanishing_orbital_divisor hF hper hmixed
      hτ hσ (indepTriple_of_indepPeriods hindep) hindepτ hindepσ
      (fun p ℓ hℓ ↦ hzero p ℓ hℓ)).2

end

end

end GaloisForLFunctions.HTGeometry
