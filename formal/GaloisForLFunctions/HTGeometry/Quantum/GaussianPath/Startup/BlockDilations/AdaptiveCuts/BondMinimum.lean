import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.BoxMass

/-! # Lower-tail scale of the weakest Gaussian bond in one buffer -/

open MeasureTheory ProbabilityTheory Real Set Finset
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section

private abbrev γ := gaussianReal 0 1
/-- One nearest-neighbour bond has nine independent Pauli coefficients. -/
abbrev bondLaw := Measure.pi fun _ : Fin 9 => γ

def weakBond (δ : ℝ) : Set (Fin 9→ℝ) := Set.univ.pi fun _ => Icc (-δ) δ

theorem weakBond_measurable (δ : ℝ) : MeasurableSet (weakBond δ) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

theorem weakBond_mass (δ : ℝ) : bondLaw.real (weakBond δ)=(γ.real (Icc (-δ) δ))^9 := by
  unfold Measure.real bondLaw weakBond
  rw [Measure.pi_pi,ENNReal.toReal_prod]
  simp

/-- For N independent candidate bonds, the exact probability of missing
a δ-weak bond is the Nth power of its one-bond miss probability. -/
theorem buffer_miss_mass (N : ℕ) (δ : ℝ) :
    (Measure.pi fun _ : Fin N => bondLaw).real (Set.univ.pi fun _ => (weakBond δ)ᶜ)=
      (1-(γ.real (Icc (-δ) δ))^9)^N := by
  change ((Measure.pi fun _ : Fin N => bondLaw) _).toReal=_
  rw [Measure.pi_pi,ENNReal.toReal_prod]
  simp only [prod_const,card_univ,Fintype.card_fin]
  rw [←measureReal_def,measureReal_compl (weakBond_measurable δ),probReal_univ,weakBond_mass]

/-- The crossover in a buffer of N candidates is at N^(-1/9). -/
theorem buffer_miss_bound (N : ℕ) {δ : ℝ} (hδ : 0≤δ) (h₁ : δ≤1) :
    (Measure.pi fun _ : Fin N => bondLaw).real (Set.univ.pi fun _ => (weakBond δ)ᶜ) ≤
      exp (-(N:ℝ)*((2*gaussianDensityFloor)*δ)^9) := by
  let p := γ.real (Icc (-δ) δ)
  let c := 2*gaussianDensityFloor*δ
  have hc : 0≤c := mul_nonneg (mul_nonneg zero_le_two gaussianDensityFloor_pos.le) hδ
  have h := ENNReal.toReal_mono (measure_ne_top _ _) (gaussianReal_Icc_lower h₁)
  rw [ENNReal.toReal_ofReal (mul_nonneg gaussianDensityFloor_pos.le (mul_nonneg zero_le_two hδ))] at h
  have hp : c≤p := (show c=gaussianDensityFloor*(2*δ) by dsimp only [c]; ring).le.trans h
  have hp₁ : p^9≤1 := pow_le_one₀ measureReal_nonneg (measureReal_le_one)
  have hex : 1-p^9≤exp (-c^9) := by
    linarith only [pow_le_pow_left₀ hc hp 9,Real.add_one_le_exp (-c^9)]
  rw [buffer_miss_mass]
  exact (pow_le_pow_left₀ (sub_nonneg.mpr hp₁) hex N).trans_eq (by rw [←exp_nat_mul]; congr 1; ring)

#print axioms buffer_miss_mass
#print axioms buffer_miss_bound
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
