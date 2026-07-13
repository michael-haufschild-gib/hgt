import GaloisForLFunctions.HTGeometry.FiniteKMSWightman

/-!
# Finite positive atomic moments as thermal/KMS value systems

Every finite positive atomic Stieltjes moment sequence is an even Liouvillian gap-moment
sequence.  One distinguished zero-energy state and one excited state per atom suffice: the
squared energy gap is the atomic node and the transition intensity is the atomic mass.

The same realization is canonical KMS/Wightman data at inverse temperature zero.  Scaling the
transition amplitude by the finite partition function makes its Wightman intensity exactly the
prescribed atomic mass.  Thus finite thermal systems are universal for finite positive atomic
moment values; no Hamiltonian flow or dynamical hypothesis is involved.
-/

open scoped BigOperators

namespace HTGeometry

noncomputable section

/-- A zero-energy base state together with one energy `sqrt (node i)` per atom. -/
def finiteAtomicThermalEnergy {d : ℕ} (node : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cases 0 (fun i => Real.sqrt (node i))

/-- The directed base-to-atom transition intensity carrying each atomic mass. -/
def finiteAtomicThermalIntensity {d : ℕ} (mass : Fin d → ℝ) :
    Fin (d + 1) → Fin (d + 1) → ℝ :=
  Fin.cases (fun _ => 0) (fun i b => if b = 0 then mass i else 0)

/-- Nonnegative atomic masses give a nonnegative finite transition spectrum. -/
theorem finiteAtomicThermalIntensity_nonneg {d : ℕ} (mass : Fin d → ℝ)
    (hmass : ∀ i, 0 ≤ mass i) (a b : Fin (d + 1)) :
    0 ≤ finiteAtomicThermalIntensity mass a b := by
  refine Fin.cases ?_ (fun i => ?_) a
  · simp [finiteAtomicThermalIntensity]
  · simp only [finiteAtomicThermalIntensity, Fin.cases_succ]
    split_ifs
    · exact hmass i
    · exact le_rfl

/-- **Finite atomic thermal realization.**  The even gap moments are exactly the prescribed
finite positive atomic moment values. -/
theorem thermalEvenGapMoment_finiteAtomic {d : ℕ}
    (mass node : Fin d → ℝ) (hnode : ∀ i, 0 ≤ node i) (n : ℕ) :
    thermalEvenGapMoment
        (finiteAtomicThermalIntensity mass) (finiteAtomicThermalEnergy node) n =
      ∑ i, mass i * node i ^ n := by
  rw [thermalEvenGapMoment_eq]
  rw [Fin.sum_univ_succ]
  simp only [finiteAtomicThermalIntensity, Fin.cases_zero, zero_mul, Finset.sum_const_zero,
    zero_add, Fin.cases_succ]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_succ]
  simp only [ite_true, finiteAtomicThermalEnergy, Fin.cases_succ, Fin.cases_zero, sub_zero]
  rw [Real.sq_sqrt (hnode i)]
  simp

/-- At inverse temperature zero, scale the transition amplitude so its canonical Wightman
intensity is the requested atomic mass. -/
def finiteAtomicKMSAmplitude {d : ℕ} (mass : Fin d → ℝ) :
    Fin (d + 1) → Fin (d + 1) → ℂ :=
  Fin.cases (fun _ => 0) (fun i b =>
    if b = 0 then (Real.sqrt ((d + 1 : ℝ) * mass i) : ℂ) else 0)

/-- The canonical zero-temperature-parameter Wightman intensity of the atomic amplitude is the
directed atomic transition intensity itself. -/
theorem finiteKMSWightmanTransitionIntensity_finiteAtomic {d : ℕ}
    (mass node : Fin d → ℝ) (hmass : ∀ i, 0 ≤ mass i)
    (a b : Fin (d + 1)) :
    finiteKMSWightmanTransitionIntensity 0 (finiteAtomicThermalEnergy node)
        (finiteAtomicKMSAmplitude mass) a b =
      finiteAtomicThermalIntensity mass a b := by
  refine Fin.cases ?_ (fun i => ?_) a
  · simp [finiteKMSWightmanTransitionIntensity, wightmanTransitionIntensity,
      finiteAtomicKMSAmplitude, finiteAtomicThermalIntensity]
  · simp only [finiteAtomicThermalIntensity, Fin.cases_succ]
    by_cases hb : b = 0
    · subst b
      simp only [ite_true, finiteKMSWightmanTransitionIntensity,
        wightmanTransitionIntensity]
      rw [show finiteAtomicKMSAmplitude mass (Fin.succ i) 0 =
          (Real.sqrt ((d + 1 : ℝ) * mass i) : ℂ) by
        simp [finiteAtomicKMSAmplitude]]
      rw [show finiteKMSWightmanWeight 0 (finiteAtomicThermalEnergy node) (Fin.succ i) 0 =
          1 / (d + 1 : ℝ) by
        simp [finiteKMSWightmanWeight, finiteGibbsPartition]]
      rw [Complex.normSq_ofReal, ← pow_two]
      have hrad : 0 ≤ ((d : ℝ) + 1) * mass i :=
        mul_nonneg (by positivity) (hmass i)
      rw [Real.sq_sqrt hrad]
      have hd : (d + 1 : ℝ) ≠ 0 := by positivity
      field_simp
    · simp [hb, finiteKMSWightmanTransitionIntensity, wightmanTransitionIntensity,
        finiteAtomicKMSAmplitude]

/-- **Finite atomic KMS realization.**  Canonical finite Wightman data already realize every
finite positive atomic Stieltjes moment sequence. -/
theorem thermalEvenGapMoment_finiteAtomicKMS {d : ℕ}
    (mass node : Fin d → ℝ) (hmass : ∀ i, 0 ≤ mass i)
    (hnode : ∀ i, 0 ≤ node i) (n : ℕ) :
    thermalEvenGapMoment
        (finiteKMSWightmanTransitionIntensity 0 (finiteAtomicThermalEnergy node)
          (finiteAtomicKMSAmplitude mass))
        (finiteAtomicThermalEnergy node) n =
      ∑ i, mass i * node i ^ n := by
  rw [show finiteKMSWightmanTransitionIntensity 0 (finiteAtomicThermalEnergy node)
        (finiteAtomicKMSAmplitude mass) = finiteAtomicThermalIntensity mass by
    funext a b
    exact finiteKMSWightmanTransitionIntensity_finiteAtomic mass node hmass a b]
  exact thermalEvenGapMoment_finiteAtomic mass node hnode n

end

end HTGeometry
