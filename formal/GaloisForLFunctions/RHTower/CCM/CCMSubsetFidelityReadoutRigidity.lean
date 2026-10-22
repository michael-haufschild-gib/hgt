import GaloisForLFunctions.RHProofLab.EulerProductArithmetic
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Subset fidelity and coefficient-one readout are rigid

The higher-subset CCM/Fock lift expands one multiplicative Euler block into Boolean subset
channels.  A tempting cofinal regularization is to average those channels with positive weights.
This file records the exact obstruction.

On a Boolean input `S ⊆ V`, the monomial indexed by `T` has value `1` precisely when `T ⊆ S`.
Thus a positive mixture has response `∑ T ∈ S.powerset, weight T`.  If that response agrees with
the full product monomial -- zero on every proper face and one on the top face -- positivity forces
the mixture to be the Dirac mass at `V`.  No diagonal positive redistribution among lower subset
grades preserves the exact multiplicative source.

The remaining theorems are normalization-independent companions.  If feature and readout scalings
multiply to one in every retained coordinate, Cauchy--Schwarz forces the product of their squared
norms to be at least the square of the channel count.  More generally, this remains true for an
arbitrary non-diagonal Hilbert encoding: if one reader evaluates to one on every encoded channel,
its norm times the norm of the summed channel state is at least the number of channels.  Hence
Walsh rotations and all other bounded linear changes of coordinates cannot repair the cofinal
coefficient-one readout.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Boolean-face response of a subset-channel mixture. -/
def positiveSubsetMixtureResponse {α : Type*}
    (weight : Finset α → ℝ) (S : Finset α) : ℝ :=
  ∑ T ∈ S.powerset, weight T

/-- Boolean point whose active coordinates are exactly `S`. -/
def booleanSubsetPoint {α : Type*} [DecidableEq α] (S : Finset α) : α → ℝ :=
  fun i => if i ∈ S then 1 else 0

theorem squarefreeMonomial_booleanSubsetPoint {α : Type*} [DecidableEq α]
    (S T : Finset α) :
    GaloisForLFunctions.RHProofLab.squarefreeMonomial (booleanSubsetPoint S) T =
      if T ⊆ S then 1 else 0 := by
  by_cases hTS : T ⊆ S
  · rw [if_pos hTS]
    apply Finset.prod_eq_one
    intro i hi
    simp [booleanSubsetPoint, hTS hi]
  · rw [if_neg hTS]
    obtain ⟨i, hiT, hiS⟩ := Set.not_subset.mp hTS
    have hiS' : i ∉ S := by simpa using hiS
    apply Finset.prod_eq_zero hiT
    simp [booleanSubsetPoint, hiS']

/-- Squarefree subset mixture evaluated on a Boolean point. -/
def positiveSquarefreeSubsetMixture {α : Type*} [DecidableEq α]
    (V : Finset α) (weight : Finset α → ℝ) (S : Finset α) : ℝ :=
  ∑ T ∈ V.powerset, weight T *
    GaloisForLFunctions.RHProofLab.squarefreeMonomial (booleanSubsetPoint S) T

theorem positiveSquarefreeSubsetMixture_boolean_eq_response
    {α : Type*} [DecidableEq α] (V : Finset α) (weight : Finset α → ℝ)
    {S : Finset α} (hSV : S ⊆ V) :
    positiveSquarefreeSubsetMixture V weight S =
      positiveSubsetMixtureResponse weight S := by
  rw [positiveSquarefreeSubsetMixture, positiveSubsetMixtureResponse]
  simp_rw [squarefreeMonomial_booleanSubsetPoint]
  symm
  calc
    (∑ T ∈ S.powerset, weight T) =
        ∑ T ∈ S.powerset, weight T * (if T ⊆ S then 1 else 0) := by
          apply Finset.sum_congr rfl
          intro T hT
          simp [(Finset.mem_powerset.mp hT)]
    _ = ∑ T ∈ V.powerset, weight T * (if T ⊆ S then 1 else 0) := by
      apply Finset.sum_subset
      · intro T hT
        exact Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hT).trans hSV)
      · intro T hTV hTS
        have hnsub : ¬T ⊆ S := by
          intro h
          exact hTS (Finset.mem_powerset.mpr h)
        simp [hnsub]

/-- **Positive full-product fidelity rigidity.**  A nonnegative subset mixture which vanishes on
every proper Boolean face and has value one on the full face is uniquely the full-subset atom. -/
theorem positiveSubsetMixture_eq_fullAtom_of_fullProductFidelity
    {α : Type*} [DecidableEq α] (V : Finset α) (weight : Finset α → ℝ)
    (hweight : ∀ T, T ⊆ V → 0 ≤ weight T)
    (hfidelity : ∀ S, S ⊆ V →
      positiveSubsetMixtureResponse weight S = if S = V then 1 else 0) :
    ∀ S, S ⊆ V → weight S = if S = V then 1 else 0 := by
  have hproper : ∀ S, S ⊆ V → S ≠ V → weight S = 0 := by
    intro S hSV hS
    have hnonneg : ∀ T ∈ S.powerset, 0 ≤ weight T := by
      intro T hT
      exact hweight T ((Finset.mem_powerset.mp hT).trans hSV)
    have hsingle :
        weight S ≤ positiveSubsetMixtureResponse weight S := by
      rw [positiveSubsetMixtureResponse]
      exact Finset.single_le_sum hnonneg (Finset.mem_powerset.mpr (by rfl))
    have hzero : positiveSubsetMixtureResponse weight S = 0 := by
      simpa [hS] using hfidelity S hSV
    exact le_antisymm (by simpa [hzero] using hsingle) (hweight S hSV)
  intro S hSV
  by_cases hS : S = V
  · subst S
    have hsum : positiveSubsetMixtureResponse weight V = 1 := by
      simpa using hfidelity V (by rfl)
    have hcollapse : positiveSubsetMixtureResponse weight V = weight V := by
      rw [positiveSubsetMixtureResponse]
      apply Finset.sum_eq_single V
      · intro T hT hTV
        exact hproper T (Finset.mem_powerset.mp hT) hTV
      · simp
    rw [hcollapse] at hsum
    simpa using hsum
  · simpa [hS] using hproper S hSV hS

/-- **Euler/Fock connector.**  If a nonnegative squarefree-channel mixture agrees with the top
squarefree monomial on every Boolean point, it is forced to be the top channel itself. -/
theorem positiveSquarefreeSubsetMixture_eq_fullAtom_of_topMonomialFidelity
    {α : Type*} [DecidableEq α] (V : Finset α) (weight : Finset α → ℝ)
    (hweight : ∀ T, T ⊆ V → 0 ≤ weight T)
    (hfidelity : ∀ S, S ⊆ V →
      positiveSquarefreeSubsetMixture V weight S =
        GaloisForLFunctions.RHProofLab.squarefreeMonomial (booleanSubsetPoint S) V) :
    ∀ S, S ⊆ V → weight S = if S = V then 1 else 0 := by
  apply positiveSubsetMixture_eq_fullAtom_of_fullProductFidelity V weight hweight
  intro S hSV
  rw [← positiveSquarefreeSubsetMixture_boolean_eq_response V weight hSV,
    hfidelity S hSV, squarefreeMonomial_booleanSubsetPoint]
  by_cases hS : S = V
  · subst S
    simp
  · have hnot : ¬V ⊆ S := by
      intro hVS
      exact hS (Finset.Subset.antisymm hSV hVS)
    simp [hS, hnot]

/-- **Diagonal feature/readout uncertainty law.**  Exact coefficient-one reconstruction in every
coordinate forces the product of feature and readout energies to dominate the squared channel
count. -/
theorem diagonalCoefficientOne_energy_product_ge_card_sq
    {ι : Type*} (s : Finset ι) (feature readout : ι → ℝ)
    (hfaithful : ∀ i ∈ s, feature i * readout i = 1) :
    ((s.card : ℝ) ^ (2 : ℕ)) ≤
      (∑ i ∈ s, feature i ^ (2 : ℕ)) * (∑ i ∈ s, readout i ^ (2 : ℕ)) := by
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (r := fun _ : ι => (1 : ℝ))
    (f := fun i => feature i ^ (2 : ℕ))
    (g := fun i => readout i ^ (2 : ℕ))
    (fun i _ => sq_nonneg (feature i))
    (fun i _ => sq_nonneg (readout i))
    (fun i hi => by
      rw [← mul_pow, hfaithful i hi])
  simpa using hcs

/-- **Basis-free coefficient-one readout uncertainty law.**  For any finite family in any complex
Hilbert space, a single reader which returns coefficient one on every channel must pay the full
channel count against the norm of the summed encoded state.  No orthogonality, diagonal weighting,
or choice of basis is assumed. -/
theorem coefficientOneHilbertReadout_energy_product_ge_card_sq
    {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (s : Finset ι) (reader : E) (channel : ι → E)
    (hread : ∀ i ∈ s, inner ℂ reader (channel i) = 1) :
    ((s.card : ℝ) ^ (2 : ℕ)) ≤
      ‖reader‖ ^ (2 : ℕ) * ‖∑ i ∈ s, channel i‖ ^ (2 : ℕ) := by
  have hinner :
      inner ℂ reader (∑ i ∈ s, channel i) = (s.card : ℂ) := by
    rw [inner_sum]
    calc
      (∑ i ∈ s, inner ℂ reader (channel i)) =
          ∑ i ∈ s, (1 : ℂ) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hread i hi
      _ = (s.card : ℂ) := by simp
  have hbound :=
    norm_inner_le_norm (𝕜 := ℂ) reader (∑ i ∈ s, channel i)
  rw [hinner] at hbound
  have hcast : ‖(s.card : ℂ)‖ = (s.card : ℝ) := by simp
  rw [hcast] at hbound
  calc
    ((s.card : ℝ) ^ (2 : ℕ)) ≤
        (‖reader‖ * ‖∑ i ∈ s, channel i‖) ^ (2 : ℕ) :=
      (sq_le_sq₀ (by positivity) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).2 hbound
    _ = ‖reader‖ ^ (2 : ℕ) * ‖∑ i ∈ s, channel i‖ ^ (2 : ℕ) := by ring

/-- Subset coordinates carrying the actual CCM multiplicative covariance anomaly. -/
def ccmHigherSubsetChannels {α : Type*} [DecidableEq α] (V : Finset α) :
    Finset (Finset α) :=
  V.powerset.filter fun T => 2 ≤ T.card

/-- **CCM covariance specialization.**  Every bounded linear encoding of the exact
coefficient-one higher-subset anomaly pays the complete size of the retained covariance grade.
This includes non-diagonal and Walsh-rotated encodings. -/
theorem ccmHigherSubsetCoefficientOneReadout_energy_product_ge_card_sq
    {α E : Type*} [DecidableEq α]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (V : Finset α) (reader : E) (channel : Finset α → E)
    (hread : ∀ T ∈ ccmHigherSubsetChannels V,
      inner ℂ reader (channel T) = 1) :
    (((ccmHigherSubsetChannels V).card : ℝ) ^ (2 : ℕ)) ≤
      ‖reader‖ ^ (2 : ℕ) *
        ‖∑ T ∈ ccmHigherSubsetChannels V, channel T‖ ^ (2 : ℕ) :=
  coefficientOneHilbertReadout_energy_product_ge_card_sq
    (ccmHigherSubsetChannels V) reader channel hread

end

end RHTower
