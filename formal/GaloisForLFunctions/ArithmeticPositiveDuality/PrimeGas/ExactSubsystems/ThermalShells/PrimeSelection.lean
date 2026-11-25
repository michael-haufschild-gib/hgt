import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Rigidity
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells.Resolution
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.GapSpectrum.BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints.Geometry
import GaloisForLFunctions.HTGeometry.ArchimedeanCorank

/-! # Temperature tests on selected squarefree prime configurations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells

open Set Filter Topology _root_.RHTower
open BinaryOrientation.LargestPrime.Bands BinaryOrientation.LargestPrime.Bands.Marks.FixedCount
open BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization
open BinaryOrientation.LargestPrime.Bands.Marks.FixedCount.Localization.Endpoints

/-- Born weight of a configuration on the selected occupation-count sector. -/
def born {S : Finset Nat.Primes} {k : ℕ} (β : ℝ) (R : BreadthSubset k ↥S) :=
  finiteSquarefreeBornWeight S β ((squarefreeOccupationEquiv S).symm R.val)

theorem born_share {S : Finset Nat.Primes} {k : ℕ} (β : ℝ) (U A : Finset (BreadthSubset k ↥S)) :
    share (born β) U A = share (weight β energyOf) U A := by
  have he (R : BreadthSubset k ↥S) : born β R = weight β energyOf R/finiteSquarefreePartition S β := by
    rw [born,finiteSquarefreeBornWeight_eq,energyOf_eq,weight]
  simp only [share,mass,he,← Finset.sum_div,div_div_div_cancel_right₀ (finiteSquarefreePartition_pos S β).ne']

theorem born_variation {S : Finset Nat.Primes} {k : ℕ} (β γ : ℝ) (U : Finset (BreadthSubset k ↥S)) :
    variation (born β) (born γ) U = variation (weight β energyOf) (weight γ energyOf) U := by
  unfold variation
  simp only [born_share]

/-- Born probability of a spectral event after selecting a family of configurations. -/
def spectralRead {S : Finset Nat.Primes} {k : ℕ} (h : Ioi (0:ℝ)) (U : Finset (BreadthSubset k ↥S))
    (β : ℝ) (F : Set (Fin k → ℝ)) : ℝ := by
  classical
  exact share (born β) U (U.filter fun R => spectrum h R ∈ F)

/-- Selecting the entire nonempty count sector reproduces its original normalized spectral law. -/
theorem spectralRead_univ (c d β : ℝ) (h : Ioi (0:ℝ)) (k : ℕ)
    (hU : (Finset.univ : Finset (BreadthSubset k ↥(added c d h))).Nonempty)
    {F : Set (Fin k → ℝ)} (hF : MeasurableSet F) :
    spectralRead h (Finset.univ : Finset (BreadthSubset k ↥(added c d h))) β F = (thermalLaw c d h β k F : ℝ) := by
  classical
  let S := added c d h
  have hp : 0 < coefficient S β k := by
    rw [coefficient_exp_sum S β h k]
    exact Finset.sum_pos (fun _ _ => Real.exp_pos _) hU
  calc _ = eventWeight S β h k F/coefficient S β k := by
         rw [spectralRead,born_share,share,eventWeight,coefficient_exp_sum S β h k]
         simp only [mass,Finset.sum_filter,weight]
         rfl
       _ = _ := (thermalLaw_event h k hF hp).symm

/-- Rational independence of the prime logarithms distinguishes all squarefree occupation energies. -/
theorem energyOf_injective (S : Finset Nat.Primes) (k : ℕ) :
    Function.Injective (energyOf (S := S) (k := k)) := by
  classical
  let a (T : Finset ↥S) (p : ↥S) := if p ∈ T then (1:ℚ) else 0
  let e (p : ↥S) := Real.log (p.val:ℝ)
  have hs (T : Finset ↥S) : (∑ p : ↥S, a T p • e p) = ∑ p ∈ T, squarefreePrimeEnergy p.val := by
    simp [a,e,ite_smul,squarefreePrimeEnergy]
    rw [Finset.inter_eq_right.mpr (show T ⊆ S.attach from fun p _ => Finset.mem_attach S p)]
  intro R T he
  have hz : (∑ p : ↥S, (a R.val p-a T.val p) • e p) = 0 := by
    simp only [sub_smul,Finset.sum_sub_distrib,hs]
    exact sub_eq_zero.mpr he
  have H := Fintype.linearIndependent_iff.mp (primeLogFiniteSlice_linearIndependent S) _ hz
  apply Subtype.ext
  ext p
  have h := sub_eq_zero.mp (H p)
  constructor
  · intro hr
    by_contra ht
    simp [a,hr,ht] at h
  · intro ht
    by_contra hr
    simp [a,hr,ht] at h

/-- Every configuration event in a selected count sector can be read by a finite set of
total-energy values, simultaneously at every temperature. -/
theorem read_from_total_energy {S : Finset Nat.Primes} {k : ℕ} (h : Ioi (0:ℝ))
    {U A : Finset (BreadthSubset k ↥S)} (ha : A ⊆ U) :
    ∃ B : Finset ℝ, ∀ β, spectralRead h U β {v | (∑ i, v i) ∈ B} = share (born β) U A := by
  classical
  let f (R : BreadthSubset k ↥S) := h.val*energyOf R
  have hinj : Function.Injective f := fun _ _ he =>
    energyOf_injective S k (mul_left_cancel₀ (show 0 < h.val from h.property).ne' he)
  refine ⟨A.image f,fun β => ?_⟩
  unfold spectralRead
  congr 1
  ext R
  simp only [Finset.mem_filter,Set.mem_setOf_eq,sum_spectrum,Finset.mem_image]
  constructor
  · rintro ⟨_,T,hT,he⟩
    exact hinj he ▸ hT
  · intro hR
    exact ⟨ha hR,R,hR,rfl⟩

/-- A single yes/no test of total energy attains the full temperature contrast. -/
theorem total_energy_attains_variation {S : Finset Nat.Primes} {k : ℕ} (h : Ioi (0:ℝ))
    (U : Finset (BreadthSubset k ↥S)) (β γ : ℝ) :
    ∃ B : Finset ℝ, |spectralRead h U β {v | (∑ i, v i) ∈ B}-spectralRead h U γ {v | (∑ i, v i) ∈ B}| =
      variation (born β) (born γ) U := by
  obtain ⟨A,hA,he⟩ := Finset.exists_mem_eq_sup' U.powerset_nonempty (fun A => |share (born β) U A-share (born γ) U A|)
  obtain ⟨B,hB⟩ := read_from_total_energy h (Finset.mem_powerset.mp hA)
  exact ⟨B,by rw [hB,hB]; exact he.symm⟩

private theorem unscaled_span {S : Finset Nat.Primes} {k : ℕ} (h : Ioi (0:ℝ)) {U : Finset (BreadthSubset k ↥S)}
    {δ : ℝ} (hw : ∀ R ∈ U, ∀ T ∈ U, |(∑ i, spectrum h R i)-(∑ i, spectrum h T i)| ≤ δ) :
    ∀ R ∈ U, ∀ T ∈ U, |energyOf R-energyOf T| ≤ δ/h.val := by
  intro R hR T hT
  have H := hw R hR T hT
  rw [sum_spectrum,sum_spectrum,← mul_sub,abs_mul,abs_of_pos (show 0 < h.val from h.property)] at H
  exact (le_div_iff₀ (show 0 < h.val from h.property)).mpr ((mul_comm _ _).le.trans H)

/-- Sharp total-variation bound in terms of the scaled Hamiltonian read from the spectrum. -/
theorem shell_bound {S : Finset Nat.Primes} {k : ℕ} (h : Ioi (0:ℝ)) {U : Finset (BreadthSubset k ↥S)}
    (hU : U.Nonempty) (β γ δ : ℝ)
    (hδ : ∀ R ∈ U, ∀ T ∈ U, |(∑ i, spectrum h R i)-(∑ i, spectrum h T i)| ≤ δ) :
    variation (born β) (born γ) U ≤ Real.tanh (|β-γ| * (δ/h.val)/4) := by
  rw [born_variation]
  exact thermal_variation energyOf hU β γ _ (unscaled_span h hδ)

/-- The same resolution bound applies to any measurement of the ordered modes. -/
theorem spectral_event_bound {S : Finset Nat.Primes} {k : ℕ} (h : Ioi (0:ℝ)) {U : Finset (BreadthSubset k ↥S)}
    (hU : U.Nonempty) (β γ δ : ℝ) (F : Set (Fin k → ℝ))
    (hδ : ∀ R ∈ U, ∀ T ∈ U, |(∑ i, spectrum h R i)-(∑ i, spectrum h T i)| ≤ δ) :
    |spectralRead h U β F-spectralRead h U γ F| ≤ Real.tanh (|β-γ| * (δ/h.val)/4) := by
  classical
  exact (event_le_variation (born β) (born γ) (Finset.filter_subset (fun R => spectrum h R ∈ F) U)).trans
    (shell_bound h hU β γ δ hδ)

/-- For simple prime energies, a nonzero maximal contrast is attained only by two configurations
at opposite temperatures, and every such pair attaining the full width is sharp. -/
theorem prime_sharp_iff {S : Finset Nat.Primes} {k : ℕ} {U : Finset (BreadthSubset k ↥S)} (hU : U.Nonempty)
    (β γ D : ℝ) (hD : ∀ x ∈ U, ∀ y ∈ U, |energyOf x-energyOf y| ≤ D) (hη : 0 < |β-γ| * D) :
    variation (born β) (born γ) U = Real.tanh (|β-γ| * D/4) ↔
      β+γ=0 ∧ ∃ x y, x ≠ y ∧ U = {x,y} ∧ |energyOf x-energyOf y| = D := by
  rw [born_variation]
  exact sharp_iff_pair energyOf hU (energyOf_injective S k).injOn β γ D hD hη

/-- Every selection containing two distinct configurations detects isometric splitting exactly
by comparison with the unit-temperature law. -/
theorem split_isometric_iff_selected_laws {S : Finset Nat.Primes} {k : ℕ}
    {U : Finset (BreadthSubset k ↥S)} {x y : BreadthSubset k ↥S} (hx : x ∈ U) (hy : y ∈ U) (hxy : x ≠ y) (s : ℂ) :
    (∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f n, T f n = split s f n) ↔ variation (born (2*s.re)) (born 1) U = 0 := by
  rw [split_isometric_iff,born_variation,variation_zero_iff energyOf ⟨x,hx⟩]
  constructor
  · intro h
    exact Or.inl (by rw [h]; ring)
  · rintro (ht | ht)
    · linarith only [ht]
    · exact False.elim (hxy (energyOf_injective S k (ht x hx y hy)))

/-- A moving selected shell of scaled width o(h) loses all fixed thermal contrast. -/
theorem thin_shell {k : ℕ} (S : Ioi (0:ℝ) → Finset Nat.Primes) (U : ∀ h, Finset (BreadthSubset k ↥(S h)))
    (δ : Ioi (0:ℝ) → ℝ) (β γ : ℝ) (hU : ∀ᶠ h in criticalApproach, (U h).Nonempty)
    (hw : ∀ᶠ h in criticalApproach, ∀ R ∈ U h, ∀ T ∈ U h, |(∑ i, spectrum h R i)-(∑ i, spectrum h T i)| ≤ δ h)
    (hδ : Tendsto (fun h => δ h/h.val) criticalApproach (𝓝 0)) :
    Tendsto (fun h => variation (born β) (born γ) (U h)) criticalApproach (𝓝 0) := by
  have hd : ∀ᶠ h in criticalApproach, ∀ R ∈ U h, ∀ T ∈ U h, |energyOf R-energyOf T| ≤ δ h/h.val :=
    hw.mono fun h hwidth => unscaled_span h hwidth
  have hη := hδ.const_mul |β-γ|
  rw [mul_zero] at hη
  exact (variation_tendsto_zero (fun _ => energyOf) U (fun _ => β) (fun _ => γ) _ hU hd hη).congr
    fun h => (born_variation β γ (U h)).symm

#print axioms spectralRead_univ
#print axioms spectral_event_bound
#print axioms energyOf_injective
#print axioms total_energy_attains_variation
#print axioms shell_bound
#print axioms prime_sharp_iff
#print axioms split_isometric_iff_selected_laws
#print axioms thin_shell

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.ThermalShells
