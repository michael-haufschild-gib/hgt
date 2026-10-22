import GaloisForLFunctions.RHTower.Deninger.DeningerNuclearOperator

/-!
# Nuclear maps with a bound on the total mass

Nuclearity is an existential statement about a rank-one representation; for infinite sums of
nuclear maps the mass of the representation has to be tracked, since only summable masses may be
concatenated.  A nuclear map of mass at most `M` is one admitting a representation whose norms sum
to at most `M`; composing on either side multiplies the mass by the norm of the factor, and a family
of nuclear maps whose masses are summable and which converges pointwise has a nuclear sum, obtained
by concatenating the representations over the disjoint union of their index sets.

* `DeningerIsNuclearLe` : nuclearity with a bound on the mass.
* `DeningerIsNuclearLe.compL`, `.compR` : the quantitative ideal property.
* `DeningerIsNuclearLe.tsum` : **a pointwise convergent family of nuclear maps with summable masses
  has a nuclear sum.**
-/

namespace RHTower

open scoped Topology

section Definition

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]

/-- **A nuclear map of mass at most `M`**: it admits a rank-one representation whose norms sum to
at most `M`. -/
def DeningerIsNuclearLe (T : X →L[𝕜] Y) (M : ℝ) : Prop :=
  ∃ (ι : Type) (φ : ι → (X →L[𝕜] 𝕜)) (y : ι → Y),
    (Summable fun i => ‖φ i‖ * ‖y i‖) ∧ (∑' i, ‖φ i‖ * ‖y i‖ ≤ M) ∧
      ∀ x, HasSum (fun i => φ i x • y i) (T x)

theorem DeningerIsNuclearLe.isNuclear {T : X →L[𝕜] Y} {M : ℝ} (h : DeningerIsNuclearLe T M) :
    DeningerIsNuclear T := by
  obtain ⟨ι, φ, y, hsum, _, happ⟩ := h
  exact ⟨ι, φ, y, hsum, happ⟩

theorem DeningerIsNuclearLe.mono {T : X →L[𝕜] Y} {M M' : ℝ} (h : DeningerIsNuclearLe T M)
    (hle : M ≤ M') : DeningerIsNuclearLe T M' := by
  obtain ⟨ι, φ, y, hsum, hmass, happ⟩ := h
  exact ⟨ι, φ, y, hsum, hmass.trans hle, happ⟩

/-- Every nuclear map has some finite mass. -/
theorem DeningerIsNuclear.exists_nuclearLe {T : X →L[𝕜] Y} (h : DeningerIsNuclear T) :
    ∃ M : ℝ, 0 ≤ M ∧ DeningerIsNuclearLe T M := by
  obtain ⟨ι, φ, y, hsum, happ⟩ := h
  refine ⟨∑' i, ‖φ i‖ * ‖y i‖, tsum_nonneg fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _), ?_⟩
  exact ⟨ι, φ, y, hsum, le_rfl, happ⟩

end Definition

section Ideal

variable {𝕜 X Y Z W : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [SeminormedAddCommGroup Z] [NormedSpace 𝕜 Z]
variable [SeminormedAddCommGroup W] [NormedSpace 𝕜 W]

/-- Precomposition multiplies the mass by the norm of the factor. -/
theorem DeningerIsNuclearLe.compR {T : X →L[𝕜] Y} {M : ℝ} (h : DeningerIsNuclearLe T M)
    (A : W →L[𝕜] X) : DeningerIsNuclearLe (T.comp A) (‖A‖ * M) := by
  obtain ⟨ι, φ, y, hsum, hmass, happ⟩ := h
  have hnonneg : ∀ i, 0 ≤ ‖φ i‖ * ‖y i‖ := fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hbound : ∀ i, ‖(φ i).comp A‖ * ‖y i‖ ≤ ‖A‖ * (‖φ i‖ * ‖y i‖) := by
    intro i
    have h1 : ‖(φ i).comp A‖ ≤ ‖φ i‖ * ‖A‖ := ContinuousLinearMap.opNorm_comp_le _ _
    calc ‖(φ i).comp A‖ * ‖y i‖ ≤ (‖φ i‖ * ‖A‖) * ‖y i‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖A‖ * (‖φ i‖ * ‖y i‖) := by ring
  have hsum' : Summable fun i => ‖(φ i).comp A‖ * ‖y i‖ :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hbound
      (hsum.mul_left ‖A‖)
  refine ⟨ι, fun i => (φ i).comp A, y, hsum', ?_, ?_⟩
  · calc ∑' i, ‖(φ i).comp A‖ * ‖y i‖ ≤ ∑' i, ‖A‖ * (‖φ i‖ * ‖y i‖) :=
        hsum'.tsum_le_tsum hbound (hsum.mul_left ‖A‖)
      _ = ‖A‖ * ∑' i, ‖φ i‖ * ‖y i‖ := tsum_mul_left
      _ ≤ ‖A‖ * M := mul_le_mul_of_nonneg_left hmass (norm_nonneg _)
  · intro x
    exact happ (A x)

/-- Postcomposition multiplies the mass by the norm of the factor. -/
theorem DeningerIsNuclearLe.compL {T : X →L[𝕜] Y} {M : ℝ} (h : DeningerIsNuclearLe T M)
    (B : Y →L[𝕜] Z) : DeningerIsNuclearLe (B.comp T) (‖B‖ * M) := by
  obtain ⟨ι, φ, y, hsum, hmass, happ⟩ := h
  have hbound : ∀ i, ‖φ i‖ * ‖B (y i)‖ ≤ ‖B‖ * (‖φ i‖ * ‖y i‖) := by
    intro i
    have h1 : ‖B (y i)‖ ≤ ‖B‖ * ‖y i‖ := B.le_opNorm _
    calc ‖φ i‖ * ‖B (y i)‖ ≤ ‖φ i‖ * (‖B‖ * ‖y i‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖B‖ * (‖φ i‖ * ‖y i‖) := by ring
  have hsum' : Summable fun i => ‖φ i‖ * ‖B (y i)‖ :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hbound
      (hsum.mul_left ‖B‖)
  refine ⟨ι, φ, fun i => B (y i), hsum', ?_, ?_⟩
  · calc ∑' i, ‖φ i‖ * ‖B (y i)‖ ≤ ∑' i, ‖B‖ * (‖φ i‖ * ‖y i‖) :=
        hsum'.tsum_le_tsum hbound (hsum.mul_left ‖B‖)
      _ = ‖B‖ * ∑' i, ‖φ i‖ * ‖y i‖ := tsum_mul_left
      _ ≤ ‖B‖ * M := mul_le_mul_of_nonneg_left hmass (norm_nonneg _)
  · intro x
    have h2 := B.hasSum (happ x)
    simp only [map_smul] at h2
    exact h2

end Ideal

section Tsum

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [CompleteSpace Y]

omit [CompleteSpace Y] in
/-- The operator norm of a nuclear map is at most its mass. -/
theorem DeningerIsNuclearLe.norm_le {T : X →L[𝕜] Y} {M : ℝ} (h : DeningerIsNuclearLe T M) :
    ‖T‖ ≤ M := by
  obtain ⟨ι, φ, y, hsum, hmass, happ⟩ := h
  have hMnn : 0 ≤ M :=
    le_trans (tsum_nonneg fun i => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hmass
  refine ContinuousLinearMap.opNorm_le_bound _ hMnn fun x => ?_
  have hb : ∀ i, ‖φ i x • y i‖ ≤ ‖x‖ * (‖φ i‖ * ‖y i‖) := by
    intro i
    rw [norm_smul]
    have h1 : ‖φ i x‖ ≤ ‖φ i‖ * ‖x‖ := (φ i).le_opNorm x
    calc ‖φ i x‖ * ‖y i‖ ≤ (‖φ i‖ * ‖x‖) * ‖y i‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖x‖ * (‖φ i‖ * ‖y i‖) := by ring
  have hns : Summable fun i => ‖φ i x • y i‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hb (hsum.mul_left ‖x‖)
  have h1 : ‖T x‖ ≤ ∑' i, ‖φ i x • y i‖ := by
    rw [← (happ x).tsum_eq]
    exact norm_tsum_le_tsum_norm hns
  have h2 : ∑' i, ‖φ i x • y i‖ ≤ ‖x‖ * ∑' i, ‖φ i‖ * ‖y i‖ := by
    rw [← tsum_mul_left]
    exact hns.tsum_le_tsum hb (hsum.mul_left ‖x‖)
  calc ‖T x‖ ≤ ‖x‖ * ∑' i, ‖φ i‖ * ‖y i‖ := h1.trans h2
    _ ≤ ‖x‖ * M := mul_le_mul_of_nonneg_left hmass (norm_nonneg _)
    _ = M * ‖x‖ := mul_comm _ _

/-- **A pointwise convergent family of nuclear maps with summable masses has a nuclear sum**, of
mass at most the sum of the masses: concatenate the representations over the disjoint union of their
index sets. -/
theorem DeningerIsNuclearLe.tsum {κ : Type} {T : κ → (X →L[𝕜] Y)} {M : κ → ℝ}
    (hT : ∀ n, DeningerIsNuclearLe (T n) (M n)) (hM : Summable M)
    {S : X →L[𝕜] Y} (hS : ∀ x, HasSum (fun n => T n x) (S x)) :
    DeningerIsNuclearLe S (∑' n, M n) := by
  choose ι φ y hsum hmass happ using hT
  set F : (Σ n : κ, ι n) → ℝ := fun p => ‖φ p.1 p.2‖ * ‖y p.1 p.2‖ with hF
  have hFnonneg : ∀ p, 0 ≤ F p := fun p => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hblock : ∀ n, Summable fun i => F ⟨n, i⟩ := hsum
  have hblocksum : Summable fun n => ∑' i, F ⟨n, i⟩ :=
    Summable.of_nonneg_of_le (fun n => tsum_nonneg fun i => hFnonneg ⟨n, i⟩) hmass hM
  have hFsum : Summable F :=
    (summable_sigma_of_nonneg hFnonneg).mpr ⟨hblock, hblocksum⟩
  have hmasstotal : ∑' p, F p ≤ ∑' n, M n := by
    rw [hFsum.tsum_sigma]
    exact hblocksum.tsum_le_tsum hmass hM
  refine ⟨Σ n : κ, ι n, fun p => φ p.1 p.2, fun p => y p.1 p.2, hFsum, hmasstotal, ?_⟩
  intro x
  have hnormle : ∀ p : Σ n : κ, ι n, ‖φ p.1 p.2 x • y p.1 p.2‖ ≤ ‖x‖ * F p := by
    intro p
    rw [norm_smul, hF]
    have h1 : ‖φ p.1 p.2 x‖ ≤ ‖φ p.1 p.2‖ * ‖x‖ := (φ p.1 p.2).le_opNorm x
    calc ‖φ p.1 p.2 x‖ * ‖y p.1 p.2‖ ≤ (‖φ p.1 p.2‖ * ‖x‖) * ‖y p.1 p.2‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = ‖x‖ * (‖φ p.1 p.2‖ * ‖y p.1 p.2‖) := by ring
  have hvecsum : Summable fun p : Σ n : κ, ι n => φ p.1 p.2 x • y p.1 p.2 :=
    Summable.of_norm_bounded (hFsum.mul_left ‖x‖) hnormle
  have hbase : HasSum (fun n => ∑' i, φ n i x • y n i)
      (∑' p : Σ n : κ, ι n, φ p.1 p.2 x • y p.1 p.2) :=
    hvecsum.hasSum.sigma fun n => (happ n x).summable.hasSum
  have heq : ∀ n, ∑' i, φ n i x • y n i = T n x := fun n => (happ n x).tsum_eq
  simp only [heq] at hbase
  have := (hS x).unique hbase
  rw [this]
  exact hvecsum.hasSum

end Tsum

end RHTower
