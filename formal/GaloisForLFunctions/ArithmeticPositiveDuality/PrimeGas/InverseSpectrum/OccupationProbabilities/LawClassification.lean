import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.BornLaw

/-! # Physical rank-one spectra are parametrized by probability laws with infinite mean label -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

/-- Probability laws on positive occupations whose expected integer label is infinite.
The reciprocal weight at slot `k` is its label `k+1`. -/
def ExteriorLaw := {μ : ℕ+ → ℝ // (∀ n, 0 ≤ μ n) ∧ HasSum (fun k => μ (number k)) 1 ∧
  ¬ Summable (fun k => μ (number k)/occupationWeight k)}

def exteriorLaw (v : MissingWave) : ExteriorLaw := by
  refine ⟨occupationProbability v,fun n => div_nonneg (sq_nonneg _) (sq_nonneg _),occupationProbability_sum v,?_⟩
  intro h
  apply v.property
  apply (heat_range_iff_summable v.val).mpr
  apply (h.mul_right (‖v.val‖^2)).congr
  intro k
  unfold occupationProbability
  field_simp [norm_ne_zero_iff.mpr (missingWave_ne_zero v),(occupationWeight_pos k).ne']

private theorem sqrt_mass_sq (μ : ExteriorLaw) (n : ℕ+) : ‖(Real.sqrt (μ.val n):ℂ)‖^2 = μ.val n := by
  rw [Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (μ.property.1 n)]

/-- The canonical representative has real, nonnegative occupation amplitudes. -/
def lawVector (μ : ExteriorLaw) : Gas := gasOfCoords (fun k => (Real.sqrt (μ.val (number k)):ℂ))
  (μ.property.2.1.summable.congr (fun k => (sqrt_mass_sq μ (number k)).symm))

theorem lawVector_apply (μ : ExteriorLaw) (n : ℕ+) : lawVector μ n = (Real.sqrt (μ.val n):ℂ) := by
  obtain ⟨k,rfl⟩ := number_surjective n
  rfl

theorem lawVector_norm_sq (μ : ExteriorLaw) : ‖lawVector μ‖^2 = 1 := by
  rw [gas_norm_sq]
  simpa only [lawVector_apply,sqrt_mass_sq] using μ.property.2.1.tsum_eq

def lawOmission (μ : ExteriorLaw) : MissingWave := ⟨lawVector μ,fun h =>
  μ.property.2.2 (by simpa only [lawVector_apply,sqrt_mass_sq] using (heat_range_iff_summable _).mp h)⟩

theorem lawOmission_probability (μ : ExteriorLaw) : occupationProbability (lawOmission μ) = μ.val := by
  funext n
  change ‖lawVector μ n‖^2/‖lawVector μ‖^2 = _
  rw [lawVector_norm_sq,lawVector_apply,sqrt_mass_sq,div_one]

/-- Assign a physical ordered spectrum to each infinite-mean law. -/
def spectrumFromLaw (μ : ExteriorLaw) : ↥(physicalSpectra 1) :=
  ⟨missingSpectrum (lawOmission μ),missingSpectrum_physical _⟩

theorem spectrumFromLaw_bijective : Function.Bijective spectrumFromLaw := by
  constructor
  · intro μ ν h
    have he := congrArg Subtype.val h
    change missingSpectrum (lawOmission μ) = missingSpectrum (lawOmission ν) at he
    exact Subtype.ext (by simpa only [lawOmission_probability] using (missingSpectrum_eq_iff_probability _ _).mp he)
  · rintro ⟨b,P,hd,hc,he⟩
    obtain ⟨w,hw,rfl⟩ := (missingDimension_one_iff _).mp hd
    let v : MissingWave := ⟨w,(nonzero_line_conserves_iff _).mp ⟨hw,hc⟩⟩
    refine ⟨exteriorLaw v,Subtype.ext (Eq.trans ?_ he)⟩
    change missingSpectrum (lawOmission (exteriorLaw v)) = missingSpectrum v
    apply (missingSpectrum_eq_iff_probability _ _).mpr
    exact lawOmission_probability _

def exteriorLawEquivPhysicalSpectrum : ExteriorLaw ≃ ↥(physicalSpectra 1) :=
  Equiv.ofBijective spectrumFromLaw spectrumFromLaw_bijective

#print axioms lawVector_apply
#print axioms lawVector_norm_sq
#print axioms lawOmission_probability
#print axioms spectrumFromLaw_bijective
#print axioms exteriorLawEquivPhysicalSpectrum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
