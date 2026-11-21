import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.SortedResponse
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Slicing.WordSublevel

/-! # A finite union of witnessed spectral near-resonances -/

open Matrix MvPolynomial MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section

/-- The order-zero mode is the physical energy combination on every spectrum. -/
theorem sortedMode_nil {n D : ℕ} {P : Fin n → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (p : MvPolynomial (Option (Fin n)) ℂ)
    (m : Fin D → ℝ) (θ : Fin n → ℝ) :
    sortedMode hP p m [] θ = ∑ j, m j*sortedEnsembleSpectrum hP θ j := by
  simp [sortedMode,numerator,sortedEval]

/-- The total price of all candidate modes, derivative rows and their suffixes. -/
def modeStripPrice (D L count : ℕ) := 16*count*D*L*jetLineIntervals D L

/-- A near-zero mode with a derivative above a, on one of the chosen rows. -/
def finiteWitnesses (N L : ℕ) (S : Finset (Fin (2^N) → ℤ))
    (rows : Fin (2^N) → Option (List (Coordinates N))) (a r : ℝ) : Set (Coordinates N → ℝ) :=
  let hP := chainPauliFin_isHermitian N
  let p := pathCharacteristic N
  ⋃ m ∈ S, ⋃ i ∈ (Finset.univ : Finset (Fin (2^N))),
    {θ | θ ∈ simpleEnsembleLocus hP ∧ |sortedMode hP p (fun j => (m j:ℝ)) [] θ| < a*r^L ∧
      a ≤ |sortedMode hP p (fun j => (m j:ℝ)) ((rows i).getD []) θ|}

theorem gaussian_finite_witnesses (N L : ℕ) (S : Finset (Fin (2^N) → ℤ))
    (rows : Fin (2^N) → Option (List (Coordinates N))) (hw : ∀ i w, w ∈ rows i → w.length ≤ L)
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (hr' : r ≤ 1) :
    (Measure.pi (fun _ : Coordinates N => gaussianReal 0 1)) (finiteWitnesses N L S rows a r) ≤
      ENNReal.ofReal ((modeStripPrice (2^N) L S.card:ℝ)*r) := by
  classical
  let D := 2^N
  let K : ℝ≥0∞ := (jetLineIntervals D L : ℝ≥0∞)*ENNReal.ofReal (16*r)
  have hh (i : Fin D) : ((rows i).getD []).length ≤ L := by
    cases he : rows i with
    | none => simp
    | some w => exact hw i w he
  unfold finiteWitnesses
  apply (measure_biUnion_finset_le _ _).trans
  have hinner (m : Fin D → ℤ) := fun i : Fin D =>
    gaussian_jet_word_sublevel (integralGenerators N) GaussianInt.toComplex (chainPauliFin N)
      (funext (generators_map N)) (chainPauliFin_isHermitian N) (fun j => (m j:ℝ)) ((rows i).getD [])
      (hh i) ha hr hr'
  calc
    _ ≤ ∑ _m ∈ S, ∑ _i : Fin D, (L:ℝ≥0∞)*K := by
      apply Finset.sum_le_sum
      intro m _
      apply (measure_biUnion_finset_le _ _).trans
      exact Finset.sum_le_sum (fun i _ => (hinner m i).trans
        (mul_le_mul_left (by exact_mod_cast hh i) K))
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,K]
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16)]
      simp only [modeStripPrice,Nat.cast_mul,ENNReal.ofReal_ofNat,Nat.cast_ofNat,D]
      ring

/-- A squared response bound gives a linear response threshold when the
detector lower bound lies between zero and one. -/
theorem response_amplitude_le {a c x : ℝ} (ha : a ≤ 1) (h : a ≤ (c * |x|)^2) :
    a/(1+|c|) ≤ |x| := by
  have hh : a ≤ |c| * |x| := by
    by_contra! he
    have hx : (|c| * |x|)^2 ≤ |c| * |x| := by
      simpa only [pow_two,mul_one] using mul_le_mul_of_nonneg_left (he.le.trans ha)
        (mul_nonneg (abs_nonneg c) (abs_nonneg x))
    have h' : a ≤ (|c| * |x|)^2 := by simpa only [mul_pow,sq_abs] using h
    exact (he.not_ge (h'.trans hx))
  apply (div_le_iff₀ (by positivity)).mpr
  rw [mul_add,mul_one,mul_comm |x| |c|]
  linarith only [hh,abs_nonneg x]

#print axioms gaussian_finite_witnesses
end
end GaloisForLFunctions.HTGeometry.SpectralJets
