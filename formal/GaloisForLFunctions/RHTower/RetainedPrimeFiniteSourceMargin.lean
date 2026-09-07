import GaloisForLFunctions.RHTower.RetainedPrimeLandauSeparation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Lattice

/-!
# Finite clipping-stable source margins on every retained prime field

Unconditional Landau separation supplies an actual source cutoff for every
nonzero retained direction. Compactness of the finite coordinate unit sphere
extracts finitely many cutoffs with one positive homogeneous margin. Finite
source-mass bounds preserve that margin under independent sufficiently small
adjacent-cutoff clipping. The pairing is exactly the coordinate pairing with
the complete source vector grouped by retained prime-intersection labels.
These witnesses depend on the retained field; cofinal energy propagation is
not asserted.
-/

noncomputable section
open Complex Set Metric
namespace RHTower

/-- All subsets of the finite retained prime field, including the empty label. -/
abbrev retainedPrimeFieldIndex (Q : Finset Nat.Primes) :=
  ↥((Q.image (fun p : Nat.Primes => (p : ℕ))).powerset)

/-- Real coordinates of a functional on the complete finite retained field. -/
abbrev retainedPrimeFieldCoordinates (Q : Finset Nat.Primes) := retainedPrimeFieldIndex Q → ℝ

private def retainedFieldExtension (Q : Finset Nat.Primes)
    (z : retainedPrimeFieldCoordinates Q) (R : Finset ℕ) : ℝ :=
  if h : R ∈ (Q.image (fun p : Nat.Primes => (p : ℕ))).powerset then z ⟨R, h⟩ else 0

/-- Pairing with the complete actual retained field at one source cutoff. -/
def retainedPrimeFieldPairing (Q : Finset Nat.Primes)
    (z : retainedPrimeFieldCoordinates Q) (M : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 M,
    z ⟨d.primeFactors ∩ Q.image (fun p : Nat.Primes => (p : ℕ)),
      Finset.mem_powerset.mpr Finset.inter_subset_right⟩ * mobiusDivisorDilationChannel M d

private lemma fieldPairing_eq_sourceMean (Q : Finset Nat.Primes)
    (z : retainedPrimeFieldCoordinates Q) (M : ℕ) :
    retainedPrimeFieldPairing Q z M =
      (retainedPrimeSourceMean (Q.image (fun p : Nat.Primes => (p : ℕ)))
        (fun R => (retainedFieldExtension Q z R : ℂ)) M).re := by
  simp [retainedPrimeFieldPairing, retainedPrimeSourceMean, retainedFieldExtension,
    Finset.mem_powerset.mpr Finset.inter_subset_right]

lemma continuous_retainedPrimeFieldPairing (Q : Finset Nat.Primes) (M : ℕ) :
    Continuous (fun z : retainedPrimeFieldCoordinates Q => retainedPrimeFieldPairing Q z M) := by
  unfold retainedPrimeFieldPairing
  fun_prop

lemma retainedPrimeFieldPairing_smul (Q : Finset Nat.Primes)
    (z : retainedPrimeFieldCoordinates Q) (c : ℝ) (M : ℕ) :
    retainedPrimeFieldPairing Q (c • z) M = c * retainedPrimeFieldPairing Q z M := by
  simp [retainedPrimeFieldPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Every nonzero direction in the complete retained field is strictly detected
by an actual source cutoff. -/
lemma exists_positive_retainedPrimeFieldPairing (Q : Finset Nat.Primes)
    (z : retainedPrimeFieldCoordinates Q) (hz : z ≠ 0) :
    ∃ M : ℕ, 0 < retainedPrimeFieldPairing Q z M := by
  have hcoord : ∃ R : retainedPrimeFieldIndex Q, z R ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hz
    funext R
    exact hn R
  obtain ⟨R, hR⟩ := hcoord
  have hy : ∃ S : Finset ℕ, S ⊆ Q.image (fun p : Nat.Primes => (p : ℕ)) ∧
      retainedFieldExtension Q z S ≠ 0 := by
    refine ⟨R.1, Finset.mem_powerset.mp R.2, ?_⟩
    simpa only [retainedFieldExtension, dif_pos R.2] using hR
  obtain ⟨M, hM⟩ := exists_positive_retainedPrimeSourceMean Q (retainedFieldExtension Q z) hy
  exact ⟨M, by rwa [fieldPairing_eq_sourceMean]⟩

/-- Each finite retained field has a finite family of actual source cutoffs and
one uniform positive directional margin. The cutoffs depend on the retained field. -/
theorem exists_retainedPrimeField_finite_uniform_margin (Q : Finset Nat.Primes) :
    ∃ K : Finset ℕ, K.Nonempty ∧ ∃ c : ℝ, 0 < c ∧
      ∀ z : retainedPrimeFieldCoordinates Q, ∃ M ∈ K,
        c * ‖z‖ ≤ retainedPrimeFieldPairing Q z M := by
  letI : Nonempty (retainedPrimeFieldIndex Q) := ⟨⟨∅, by simp⟩⟩
  let S := sphere (0 : retainedPrimeFieldCoordinates Q) 1
  have hS : IsCompact S := isCompact_sphere _ _
  have hSne : S.Nonempty := by
    refine ⟨1, ?_⟩
    simp [S]
  let U : ℕ → Set (retainedPrimeFieldCoordinates Q) := fun M =>
    {z | 0 < retainedPrimeFieldPairing Q z M}
  have hU : ∀ M, IsOpen (U M) := fun M =>
    isOpen_lt continuous_const (continuous_retainedPrimeFieldPairing Q M)
  have hcover : S ⊆ ⋃ M, U M := by
    intro z hz
    have hn : ‖z‖ = 1 := by simpa only [S, mem_sphere, dist_zero_right] using hz
    have hz0 : z ≠ 0 := by intro he; simp [he] at hn
    obtain ⟨M, hM⟩ := exists_positive_retainedPrimeFieldPairing Q z hz0
    exact mem_iUnion.mpr ⟨M, hM⟩
  obtain ⟨K, hKcover⟩ := hS.elim_finite_subcover U hU hcover
  have hK : K.Nonempty := by
    obtain ⟨z, hz⟩ := hSne
    obtain ⟨M, hM, _⟩ := mem_iUnion₂.mp (hKcover hz)
    exact ⟨M, hM⟩
  let F : retainedPrimeFieldCoordinates Q → ℝ := fun z =>
    K.sup' hK (fun M => retainedPrimeFieldPairing Q z M)
  have hF : Continuous F := Continuous.finset_sup'_apply hK
    (fun M _ => continuous_retainedPrimeFieldPairing Q M)
  have hFpos : ∀ z ∈ S, 0 < F z := by
    intro z hz
    obtain ⟨M, hM, hzM⟩ := mem_iUnion₂.mp (hKcover hz)
    exact lt_of_lt_of_le hzM (Finset.le_sup' (fun M => retainedPrimeFieldPairing Q z M) hM)
  obtain ⟨z₀, hz₀, hmin⟩ := hS.exists_isMinOn hSne hF.continuousOn
  refine ⟨K, hK, F z₀, hFpos z₀ hz₀, ?_⟩
  intro z
  by_cases hz : z = 0
  · obtain ⟨M, hM⟩ := hK
    refine ⟨M, hM, ?_⟩
    simp [hz, retainedPrimeFieldPairing]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  let u : retainedPrimeFieldCoordinates Q := ‖z‖⁻¹ • z
  have hu : u ∈ S := by
    simp [u, S, norm_smul, hn.ne']
  obtain ⟨M, hM, hmax⟩ := Finset.exists_mem_eq_sup' hK
    (fun M => retainedPrimeFieldPairing Q u M)
  have hbound : F z₀ ≤ retainedPrimeFieldPairing Q u M := by
    rw [← hmax]
    exact hmin hu
  change F z₀ ≤ retainedPrimeFieldPairing Q (‖z‖⁻¹ • z) M at hbound
  rw [retainedPrimeFieldPairing_smul] at hbound
  refine ⟨M, hM, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hbound hn.le
  have he : ‖z‖ * (‖z‖⁻¹ * retainedPrimeFieldPairing Q z M) =
      retainedPrimeFieldPairing Q z M := by rw [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  rw [he] at hm
  simpa only [mul_comm] using hm

end RHTower

namespace RHTower

/-- A finite source-mass bound on the retained pairing, in the coordinate sup norm. -/
lemma abs_retainedPrimeFieldPairing_le (Q : Finset Nat.Primes)
    (z : retainedPrimeFieldCoordinates Q) (M : ℕ) :
    |retainedPrimeFieldPairing Q z M| ≤
      ‖z‖ * ∑ d ∈ Finset.Icc 1 M, |mobiusDivisorDilationChannel M d| := by
  unfold retainedPrimeFieldPairing
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 M,
      |z ⟨d.primeFactors ∩ Q.image (fun p : Nat.Primes => (p : ℕ)),
        Finset.mem_powerset.mpr Finset.inter_subset_right⟩ * mobiusDivisorDilationChannel M d| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 M, ‖z‖ * |mobiusDivisorDilationChannel M d| := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm z ⟨d.primeFactors ∩ Q.image (fun p : Nat.Primes => (p : ℕ)),
          Finset.mem_powerset.mpr Finset.inter_subset_right⟩)) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- The finite actual source witnesses retain one positive margin under
independent sufficiently small adjacent-cutoff clipping. -/
theorem exists_retainedPrimeField_finite_clip_margin (Q : Finset Nat.Primes) :
    ∃ K : Finset ℕ, K.Nonempty ∧ ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ δ ≤ 1 ∧
      ∀ clip : ℕ → ℝ, (∀ M ∈ K, 0 ≤ clip M ∧ clip M ≤ δ) →
      ∀ z : retainedPrimeFieldCoordinates Q, ∃ M ∈ K,
        c * ‖z‖ ≤ (1 - clip M) * retainedPrimeFieldPairing Q z M +
          clip M * retainedPrimeFieldPairing Q z (M + 1) := by
  obtain ⟨K, hK, c, hc, hmargin⟩ := exists_retainedPrimeField_finite_uniform_margin Q
  let A : ℕ → ℝ := fun M => ∑ d ∈ Finset.Icc 1 M, |mobiusDivisorDilationChannel M d|
  have hA : ∀ M, 0 ≤ A M := fun M => Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  let L : ℝ := 1 + ∑ M ∈ K, (A (M + 1) + A M)
  have hL : 0 < L := by
    have hs := Finset.sum_nonneg (s := K) (fun M _ => add_nonneg (hA (M + 1)) (hA M))
    dsimp [L]
    linarith
  have hLM (M : ℕ) (hM : M ∈ K) : A (M + 1) + A M ≤ L := by
    have hb := Finset.single_le_sum (fun M _ => add_nonneg (hA (M + 1)) (hA M)) hM
    dsimp [L]
    linarith
  let δ : ℝ := min 1 (c / (2 * L))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hc (by positivity))
  refine ⟨K, hK, c / 2, δ, by positivity, hδ, min_le_left _ _, ?_⟩
  intro clip hclip z
  obtain ⟨M, hM, hbound⟩ := hmargin z
  have hclip0 := (hclip M hM).1
  have hclipc : clip M ≤ c / (2 * L) := (hclip M hM).2.trans (min_le_right _ _)
  have hclipL : clip M * L ≤ c / 2 := by
    have h := (le_div_iff₀ (show 0 < 2 * L by positivity)).mp hclipc
    nlinarith
  have hdiff : |retainedPrimeFieldPairing Q z (M + 1) - retainedPrimeFieldPairing Q z M| ≤
      ‖z‖ * L := by
    calc
      _ ≤ |retainedPrimeFieldPairing Q z (M + 1)| + |retainedPrimeFieldPairing Q z M| := abs_sub _ _
      _ ≤ ‖z‖ * A (M + 1) + ‖z‖ * A M :=
        add_le_add (abs_retainedPrimeFieldPairing_le Q z (M + 1))
          (abs_retainedPrimeFieldPairing_le Q z M)
      _ = ‖z‖ * (A (M + 1) + A M) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hLM M hM) (norm_nonneg _)
  have herror : |clip M * (retainedPrimeFieldPairing Q z (M + 1) - retainedPrimeFieldPairing Q z M)| ≤
      (c / 2) * ‖z‖ := by
    rw [abs_mul, abs_of_nonneg hclip0]
    calc
      _ ≤ clip M * (‖z‖ * L) := mul_le_mul_of_nonneg_left hdiff hclip0
      _ = ‖z‖ * (clip M * L) := by ring
      _ ≤ ‖z‖ * (c / 2) := mul_le_mul_of_nonneg_left hclipL (norm_nonneg _)
      _ = _ := by ring
  refine ⟨M, hM, ?_⟩
  have hlower := (abs_le.mp herror).1
  nlinarith

end RHTower

namespace RHTower

/-- Complete retained source vector, grouped by its actual prime-intersection label. -/
def retainedPrimeFieldProfile (Q : Finset Nat.Primes) (M : ℕ) : retainedPrimeFieldCoordinates Q :=
  fun R => ∑ d ∈ Finset.Icc 1 M,
    if (⟨d.primeFactors ∩ Q.image (fun p : Nat.Primes => (p : ℕ)),
      Finset.mem_powerset.mpr Finset.inter_subset_right⟩ : retainedPrimeFieldIndex Q) = R
    then mobiusDivisorDilationChannel M d else 0

/-- The directional functional is exactly the coordinate pairing with the
complete actual source profile. -/
lemma retainedPrimeFieldPairing_eq_sum_profile (Q : Finset Nat.Primes)
    (z : retainedPrimeFieldCoordinates Q) (M : ℕ) :
    retainedPrimeFieldPairing Q z M = ∑ R : retainedPrimeFieldIndex Q,
      z R * retainedPrimeFieldProfile Q M R := by
  unfold retainedPrimeFieldPairing retainedPrimeFieldProfile
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  simp

end RHTower
